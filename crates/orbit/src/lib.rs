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

use std::sync::LazyLock;

use glam::*;
use serde::{Deserialize, Serialize};

pub mod canvas;

#[cfg(feature = "leptos")]
pub mod leptos;

#[cfg(feature = "simulate")]
pub mod simulate;

/// A compressed orbit: random-access reconstruction at any timestep.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct BakedOrbit {
    /// The name of the orbit.
    pub name: String,

    /// The duration of this orbit's period.
    pub period: f64,

    /// The total momentum energy of the orbit.
    ///
    /// TODO: what are the units here?
    pub energy: f64,

    /// Each [CompressedBody] in this orbit.
    pub bodies: Vec<BakedBody>,
}

/// A baked body: compressed representation of its motion.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct BakedBody {
    /// Every frequency component in this body's position.
    pub position: Vec<FrequencyComponent>,

    /// This body's average speed over its orbit.
    pub average_speed: f64,
}

impl BakedBody {
    /// Discards all frequency components with amplitudes below the cutoff.
    #[cfg(feature = "simulate")]
    pub fn optimize(&mut self, cutoff: f64) {
        let original_length = self.position.len();
        self.position.retain(|freq| freq.amplitude > cutoff);
        let new_length = self.position.len();
        tracing::debug!("optimized #freqs from {original_length} to {new_length}");
    }

    /// Calculates the position of this body at a given time.
    pub fn position_at(&self, time: f64) -> DVec2 {
        self.position.iter().map(|freq| freq.sample(time)).sum()
    }
}

/// A single frequency component.
#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct FrequencyComponent {
    /// The frequency of this frequency component.
    ///
    /// This is in units of the domain's period, which is specified elsewhere.
    pub freq: f64,

    /// The amplitude of this frequency component.
    pub amplitude: f64,

    /// The phase of this frequency component.
    pub phase: f64,
}

impl FrequencyComponent {
    /// A zeroed frequency component.
    pub const ZERO: Self = Self {
        freq: 0.0,
        amplitude: 0.0,
        phase: 0.0,
    };

    /// Samples the value of this frequency component at some timestep (unit is periods).
    pub fn sample(&self, at: f64) -> DVec2 {
        let theta = std::f64::consts::TAU * at * self.freq + self.phase;
        DVec2::from_angle(-theta) * self.amplitude
    }
}

/// Gets the set of built-in baked orbits.
pub fn get_default_orbits() -> Vec<BakedOrbit> {
    static ORBITS: LazyLock<Vec<BakedOrbit>> =
        LazyLock::new(|| serde_json::from_str(include_str!("../baked.json")).unwrap());

    ORBITS.to_owned()
}
