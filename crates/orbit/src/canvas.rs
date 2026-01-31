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

use std::f64::consts::TAU;

use web_sys::{wasm_bindgen::JsValue, CanvasRenderingContext2d};

use crate::BakedOrbit;

pub struct OrbitRenderer {
    /// The baked orbit to render.
    pub orbit: BakedOrbit,

    /// The radius of each body.
    pub body_radius: f64,

    /// The fill style of each body.
    pub body_fill: String,

    /// The stroke style of each body.
    pub body_stroke: String,

    /// The width of each body's stroke.
    pub body_stroke_width: f64,

    /// The number of motion blur frames to render.
    pub motion_blur: u16,

    /// The number of segments in the trail.
    pub trail_segments: u16,

    /// The orbit duration of the trail.
    pub trail_duration: f64,

    /// The stroke style of the trail.
    pub trail_stroke: String,

    /// The width of the trail stroke.
    pub trail_width: f64,

    /// Speed scaling factor, in units per second per second.
    ///
    /// Used to normalize by the average speed of the orbit's body.
    pub speed: f64,
}

impl OrbitRenderer {
    /// Creates a new orbit renderer with the default properties and the given orbit.
    pub fn new(orbit: BakedOrbit) -> Self {
        Self {
            orbit,
            body_radius: 0.1,
            body_fill: "white".to_string(),
            body_stroke: "black".to_string(),
            body_stroke_width: 0.05,
            motion_blur: 10,
            trail_segments: 20,
            trail_duration: 0.1,
            trail_stroke: "black".to_string(),
            trail_width: 0.025,
            speed: 0.5,
        }
    }

    /// Draws this orbit to a canvas.
    pub fn draw(
        &self,
        canvas: &CanvasRenderingContext2d,
        time: f64,
        delta_time: f64,
    ) -> Result<(), JsValue> {
        let average_speed = self
            .orbit
            .bodies
            .iter()
            .map(|body| body.average_speed)
            .reduce(|a, b| a.max(b))
            .unwrap();

        let speed_factor = self.speed / average_speed;

        let time = time * speed_factor;
        let delta_time = delta_time * speed_factor;

        canvas.set_line_width(self.trail_width);
        canvas.set_stroke_style_str(&self.trail_stroke);

        let trail_dt = self.trail_duration / self.trail_segments as f64;

        for body in self.orbit.bodies.iter() {
            canvas.begin_path();

            for trail_idx in 0..self.trail_segments {
                let time = time - trail_dt * trail_idx as f64;
                let position = body.position_at(time);
                canvas.line_to(position.x, position.y);
            }

            canvas.stroke();
        }

        canvas.set_line_width(self.body_stroke_width);
        canvas.set_fill_style_str(&self.body_fill);
        canvas.set_stroke_style_str(&self.body_stroke);

        let blur_dt = delta_time / (self.motion_blur + 1) as f64;

        canvas.set_global_composite_operation("lighter")?;
        canvas.set_global_alpha(1.0 / (self.motion_blur + 1) as f64);

        for blur_offset in (0..=self.motion_blur).rev() {
            let time = time - blur_offset as f64 * blur_dt;

            for body in self.orbit.bodies.iter() {
                let position = body.position_at(time);
                canvas.begin_path();
                canvas.arc(position.x, position.y, self.body_radius, 0.0, TAU)?;
                canvas.fill();
                canvas.stroke();
            }
        }

        Ok(())
    }
}
