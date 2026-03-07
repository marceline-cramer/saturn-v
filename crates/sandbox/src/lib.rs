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

use leptos::{html::Div, prelude::*};
use wasm_bindgen::prelude::*;
use web_sys::{
    js_sys::{self, Reflect},
    Element,
};

#[wasm_bindgen]
pub fn mount(el: Element) {
    console_error_panic_hook::set_once();
    mount_to(el.dyn_into().unwrap(), App).forget();
}

#[component]
pub fn App() -> impl IntoView {
    view! {
        <p>"The sandbox will go here."</p>
        <Editor/>
    }
}

#[component]
fn Editor() -> impl IntoView {
    let node = NodeRef::<Div>::new();

    node.on_load(|node| {
        let config = js_sys::Object::new();
        Reflect::set(&config, &"doc".into(), &"test contents\n".into()).unwrap();
        Reflect::set(&config, &"parent".into(), node.dyn_ref().unwrap()).unwrap();
        Reflect::set(&config, &"extensions".into(), &basicSetup).unwrap();
        EditorView::new(config);
    });

    view! { <div node_ref=node /> }
}

#[wasm_bindgen(module = "/codemirror.js")]
extern "C" {
    pub type EditorView;

    #[wasm_bindgen(constructor)]
    pub fn new(args: js_sys::Object) -> EditorView;

    static basicSetup: JsValue;
}
