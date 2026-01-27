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

//! Leptos integration to the orbital sim.

use leptos::{html::Canvas, prelude::*};
use web_sys::{wasm_bindgen::JsCast, CanvasRenderingContext2d};

use crate::{canvas::OrbitRenderer, get_default_orbits};

#[component]
pub fn Orbit(#[prop(optional)] name: Option<String>) -> impl IntoView {
    let canvas_ref = NodeRef::<Canvas>::new();
    let (time, set_time) = signal(0.0f64);

    let orbit = get_default_orbits()
        .iter()
        .find(|orbit| Some(&orbit.name) == name.as_ref())
        .cloned()
        .unwrap_or_else(|| get_default_orbits().first().unwrap().clone());

    let renderer = OrbitRenderer::new(orbit);

    let performance = window()
        .performance()
        .expect("performance is not available");

    let start = performance.now();
    let mut last_frame = start;

    Effect::new(move || {
        let Some(canvas) = canvas_ref.get() else {
            return;
        };

        let performance = performance.clone();
        request_animation_frame(move || {
            let elapsed_ms = performance.now() - start;
            set_time.set(elapsed_ms / 1000.0);
        });

        let width = canvas.offset_width() as f64;
        let height = canvas.offset_height() as f64;

        let ctx = canvas
            .get_context("2d")
            .unwrap()
            .unwrap()
            .dyn_into::<CanvasRenderingContext2d>()
            .unwrap();

        let time = time.get();
        let dt = time - last_frame;
        last_frame = time;

        ctx.reset();
        ctx.clear_rect(0.0, 0.0, width, height);

        let margin = renderer.body_radius + renderer.body_stroke_width;
        let margin_offset = margin + 1.0;
        ctx.scale(width / margin_offset / 2.0, height / margin_offset / 2.0)
            .unwrap();
        ctx.translate(margin_offset, margin_offset).unwrap();
        renderer.draw(&ctx, time, dt).unwrap();
    });

    view! {
      <canvas node_ref=canvas_ref width="300px" height="300px" />
    }
}
