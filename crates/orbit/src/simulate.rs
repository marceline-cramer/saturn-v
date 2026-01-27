// Copyright (C) 2025-2026 Marceline Cramer
// SPDX-License-Identifier: AGPL-3.0-or-later
//
// Saturn V is free software: you can redistribute it and/or modify it under
// the terms of the GNU Affero General Public License as published by the Free
// Software Foundation, either version 3 of the License, or (at your option) any
// later version.
//
// Saturn V is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
// FOR A PARTICULAR PURPOSE. See the GNU Affero General Public License for
// more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with Saturn V. If not, see <https://www.gnu.org/licenses/>.

use glam::*;
use rayon::iter::{ParallelBridge, ParallelIterator};
use rustfft::{num_complex::Complex64, FftPlanner};
use serde::{Deserialize, Serialize};
use tracing::{debug, info_span};

use crate::{BakedBody, BakedOrbit, FrequencyComponent};

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct Config {
    pub orbit: Vec<OrbitConfig>,
    pub simulation: SimulationConfig,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct SimulationConfig {
    pub frames: usize,
    pub subframes: usize,
}

/// The configuration for a single orbit.
///
/// This is distinct from [Orbit], which is ready to be simulated.
/// This structure exists to make it easy to copy-paste three-body
/// solutions from existing work.
///
/// TODO: cite orbit solution sources
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct OrbitConfig {
    pub name: String,
    pub period: f64,
    pub energy: f64,
    pub masses: Vec<f64>,
    pub positions: Vec<DVec2>,
    pub velocities: Vec<DVec2>,
}

impl OrbitConfig {
    pub fn to_orbit(&self) -> Orbit {
        let bodies = self
            .masses
            .iter()
            .zip(self.positions.iter())
            .zip(self.velocities.iter())
            .map(|((mass, position), velocity)| Body {
                mass: *mass,
                position: *position,
                velocity: *velocity,
            })
            .collect();

        Orbit {
            name: self.name.clone(),
            initial_conds: bodies,
            period: self.period,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Orbit {
    pub name: String,
    pub initial_conds: Vec<Body>,
    pub period: f64,
}

pub fn bake(sim_config: &SimulationConfig, orbit_config: &OrbitConfig) -> BakedOrbit {
    let span = info_span!("bake", orbit = orbit_config.name);
    let _enter = span.enter();

    let orbit = orbit_config.to_orbit();

    let mut simulated = Simulation::simulate_closed(sim_config, &orbit);

    simulated.fit();

    let mut baked_bodies = simulated.analyze();

    baked_bodies
        .iter_mut()
        .for_each(|body| body.optimize(0.001));

    let by_body = transpose(&simulated.positions, Clone::clone);

    let total_frames = simulated.positions.len();
    let mut compressed = Vec::new();
    for (body, baseline) in baked_bodies.iter().zip(by_body.iter()) {
        let positions = inverse_analyze(total_frames, body);
        debug!("optimization error: {}", rms_error(&positions, baseline));
        compressed.push(positions);
    }

    BakedOrbit {
        name: orbit_config.name.clone(),
        period: orbit_config.period,
        energy: orbit_config.energy,
        bodies: baked_bodies.clone(),
    }
}

pub fn fft_to_freq(idx: usize, fft: Complex64, frame_num: usize) -> FrequencyComponent {
    let half = frame_num / 2;

    let freq = if idx == 0 {
        0.0
    } else if idx < half {
        -(idx as f64)
    } else {
        (frame_num as f64) - (idx as f64)
    };

    FrequencyComponent {
        freq,
        amplitude: (fft.im * fft.im + fft.re * fft.re).sqrt() / frame_num as f64,
        phase: (-fft.im).atan2(fft.re),
    }
}

pub fn inverse_analyze(frames: usize, body: &BakedBody) -> Vec<DVec2> {
    (0..frames)
        .map(|idx| {
            let sample = (idx as f64) / (frames as f64);
            body.position.iter().map(|freq| freq.sample(sample)).sum()
        })
        .collect()
}

#[derive(Clone)]
pub struct Simulation {
    /// The positions of each body in the orbit, body-major.
    pub positions: Vec<Vec<DVec2>>,

    /// The minimum body position.
    pub min_position: DVec2,

    /// The maximum body position.
    pub max_position: DVec2,
}

impl Simulation {
    pub fn from_positions(positions: Vec<Vec<DVec2>>) -> Self {
        let min_position = positions
            .iter()
            .flatten()
            .copied()
            .reduce(|p1, p2| p1.min(p2))
            .unwrap_or_default();

        let max_position = positions
            .iter()
            .flatten()
            .copied()
            .reduce(|p1, p2| p1.max(p2))
            .unwrap_or_default();

        Self {
            positions,
            min_position,
            max_position,
        }
    }

    pub fn fit(&mut self) {
        let max_bound = [self.min_position, self.max_position]
            .into_iter()
            .map(|vec| vec.abs())
            .flat_map(|vec| [vec.x, vec.y])
            .reduce(|v1, v2| v1.max(v2))
            .unwrap();

        let scale = 1.0 / max_bound;

        self.min_position *= scale;
        self.max_position *= scale;

        self.positions
            .iter_mut()
            .flat_map(|body| body.iter_mut())
            .for_each(|position| *position *= scale);
    }

    pub fn simulate_closed(config: &SimulationConfig, orbit: &Orbit) -> Self {
        let mut reversed = orbit.clone();

        for body in reversed.initial_conds.iter_mut() {
            body.velocity = -body.velocity;
        }

        let forward_span = info_span!("forward sim");
        let reverse_span = info_span!("reverse sim");

        let (mut forwards, mut backwards) = rayon::join(
            || {
                let _enter = forward_span.enter();
                Self::simulate(config, orbit)
            },
            || {
                let _enter = reverse_span.enter();
                Self::simulate(config, &reversed)
            },
        );

        backwards.reverse();

        // simulations should end where they started
        // remove the last element to even out the period
        forwards.pop();
        backwards.pop();

        let forwards_error = transpose(&forwards, Clone::clone);
        let backwards_error = transpose(&backwards, Clone::clone);

        for (forwards, backwards) in forwards_error.iter().zip(backwards_error.iter()) {
            let error = rms_error(forwards, backwards);
            debug!("closed simulation RMS error: {error}",);
            assert!(error < 0.001);
        }

        let frame_num = forwards.len();
        for (idx, (forwards, backwards)) in forwards.iter_mut().zip(backwards.iter()).enumerate() {
            let position = (idx as f64) / (frame_num as f64);
            let blend = position;

            for (forward, backward) in forwards.iter_mut().zip(backwards.iter()) {
                *forward = forward.lerp(*backward, blend);
            }
        }

        Self::from_positions(forwards)
    }

    pub fn simulate(config: &SimulationConfig, orbit: &Orbit) -> Vec<Vec<DVec2>> {
        let subframe_num = config.frames * config.subframes;
        let timestep = orbit.period / subframe_num as f64;
        let mut bodies = orbit.initial_conds.clone();
        let mut history = Vec::with_capacity(subframe_num);

        let first: Vec<_> = bodies.iter().map(|body| body.position).collect();
        history.push(first.clone());

        let mut last = vec![];
        for frame_idx in 0..config.frames {
            for _ in 0..config.subframes {
                step(timestep, &mut bodies);
            }

            last = bodies.iter().map(|body| body.position).collect();
            history.push(last.clone());

            if frame_idx % (config.frames / 10) == 0 {
                debug!("simulating frame #{frame_idx}");
            }
        }

        debug!("start-end simulation drift: {}", rms_error(&first, &last));

        history
    }

    pub fn analyze(&self) -> Vec<BakedBody> {
        let mut planner = FftPlanner::new();
        let frame_num = self.positions.len();
        let fft = planner.plan_fft_forward(frame_num);

        let average_speeds = self.positions.iter().map(|body| {
            let loop_dist = body.first().unwrap() - body.last().unwrap();

            let total_dist: f64 = body
                .windows(2)
                .map(|pair| pair[1] - pair[0])
                .chain(std::iter::once(loop_dist))
                .map(|v| v.length())
                .sum();

            total_dist / body.len() as f64
        });

        let mut freqs = transpose(&self.positions, |pos| Complex64 {
            re: pos.x,
            im: pos.y,
        });

        freqs
            .iter_mut()
            .par_bridge()
            .for_each(|body| fft.process(body));

        freqs
            .into_iter()
            .map(|frames| {
                frames
                    .into_iter()
                    .enumerate()
                    .map(|(idx, freq)| fft_to_freq(idx, freq, frame_num))
                    .collect()
            })
            .zip(average_speeds)
            .map(|(position, average_speed)| BakedBody {
                position,
                average_speed,
            })
            .collect()
    }
}

pub fn rms_error(lhs: &[DVec2], rhs: &[DVec2]) -> f64 {
    lhs.iter()
        .zip(rhs.iter())
        .map(|(lhs_pos, rhs_pos)| lhs_pos.distance_squared(*rhs_pos) / lhs.len() as f64)
        .sum()
}

pub fn transpose<T, O: Clone>(positions: &[Vec<T>], map: impl Fn(&T) -> O) -> Vec<Vec<O>> {
    let mut by_body = vec![Vec::new(); positions[0].len()];

    for frame in positions.iter() {
        for (by_body, position) in by_body.iter_mut().zip(frame.iter()) {
            by_body.push(map(position));
        }
    }

    by_body
}

pub fn step(dt: f64, bodies: &mut [Body]) {
    apply_forces(dt, bodies);
    update(dt, bodies);
}

pub fn apply_forces(dt: f64, bodies: &mut [Body]) {
    for body in 0..bodies.len() {
        for other in (body + 1)..bodies.len() {
            let [body, other] = bodies.get_disjoint_mut([body, other]).unwrap();

            let delta = body.position - other.position;

            let mass = body.mass * other.mass;
            let r2 = delta.length_squared();
            let force = mass / r2;

            let delta = delta.normalize();
            body.velocity -= dt * force * delta;
            other.velocity += dt * force * delta;
        }
    }
}

pub fn update(dt: f64, bodies: &mut [Body]) {
    for body in bodies.iter_mut() {
        body.position += body.velocity * dt;
    }
}

#[derive(Clone, Debug)]
pub struct Body {
    pub mass: f64,
    pub position: DVec2,
    pub velocity: DVec2,
}
