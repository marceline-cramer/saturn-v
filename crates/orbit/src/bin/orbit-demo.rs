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

use leptos::prelude::*;
use saturn_v_orbit::{get_default_orbits, leptos::Orbit};
use web_sys::wasm_bindgen::JsCast;

#[component]
fn App() -> impl IntoView {
    let all_orbits: Vec<_> = get_default_orbits()
        .iter()
        .map(|orbit| orbit.name.clone())
        .collect();

    let (name, set_name) = signal(all_orbits[0].clone());

    let options = all_orbits
        .into_iter()
        .map(|name| view! { <option value={name.clone()}>{name.clone()}</option> })
        .collect::<Vec<_>>();

    let on_change = move |ev| {
        set_name.set(event_target_value(&ev));
    };

    view! {
        <div style="width:100%;height:100%;display:flex;align-items:center;justify-content:center;flex-direction:column">
            <div style="border:1px solid black;padding:10px;margin:10px">
                {move || view!{ <Orbit name=name.get()/> } }
            </div>
            <select on:change=on_change style="font-size:14pt">
                {options}
            </select>
        </div>
    }
}

fn main() {
    console_error_panic_hook::set_once();

    if let Some(el) = document().get_element_by_id("orbit-demo") {
        mount_to(el.dyn_into().unwrap(), App).forget();
    }
}
