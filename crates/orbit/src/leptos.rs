// Copyright (C) 2025 Marceline Cramer
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

#[component]
pub fn Orbit() -> impl IntoView {
    let canvas_ref = NodeRef::<Canvas>::new();
    let (time, set_time) = signal(0.0f64);

    let performance = window()
        .performance()
        .expect("performance is not available");

    let start = performance.now();

    Effect::new(move || {
        let Some(canvas) = canvas_ref.get() else {
            return;
        };

        let performance = performance.clone();
        request_animation_frame(move || {
            let elapsed_ms = performance.now() - start;
            set_time.set(elapsed_ms / 1000.0);
        });

        let width = canvas.offset_width();
        let height = canvas.offset_height();

        let ctx = canvas
            .get_context("2d")
            .unwrap()
            .unwrap()
            .dyn_into::<CanvasRenderingContext2d>()
            .unwrap();

        let time = time.get();
        let x = 40.0 + (time * 4.0).sin() * 30.0;

        ctx.clear_rect(0.0, 0.0, width as f64, height as f64);
        ctx.set_fill_style_str("red");
        ctx.fill_rect(x, 20.0, 30.0, 30.0);
    });

    view! {
      <canvas node_ref=canvas_ref width="200px" height="200px" />
    }
}
