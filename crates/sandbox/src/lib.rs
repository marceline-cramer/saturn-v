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

use leptos::prelude::*;
use wasm_bindgen::prelude::*;
use web_sys::Element;

#[component]
fn App() -> impl IntoView {
    view! {
        <p>"The sandbox will go here."</p>
    }
}

#[wasm_bindgen]
pub fn mount(el: Element) {
    mount_to(el.dyn_into().unwrap(), App).forget();
}
