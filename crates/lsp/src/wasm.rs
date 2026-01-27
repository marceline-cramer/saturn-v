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

use futures_util::{AsyncWriteExt, SinkExt};
use sluice::pipe::*;
use tokio_util::compat::*;
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::js_sys::Uint8Array;
use wasm_streams::{ReadableStream, WritableStream};

use crate::*;

/** The Kerolox language server, interacted with via JS streams. */
#[wasm_bindgen]
pub struct LanguageServer {
    /// A stream to send requests to the language server.
    #[wasm_bindgen(getter_with_clone)]
    pub requests: wasm_streams::writable::sys::WritableStream,

    /// A stream for receiving responses from the language server.
    #[wasm_bindgen(getter_with_clone)]
    pub responses: wasm_streams::readable::sys::ReadableStream,
}

#[wasm_bindgen]
impl LanguageServer {
    /// Creates a Kerolox language server.
    #[wasm_bindgen(constructor)]
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        // create pipes to do internal async IO
        let (request_rx, request_tx) = pipe();
        let (response_rx, response_tx) = pipe();

        // create service
        let (service, socket) = LspService::new(LspBackend::new);

        // initialize language server
        let server =
            Server::new(request_rx.compat(), response_tx.compat_write(), socket).serve(service);

        // spawn thread to run language server
        wasm_bindgen_futures::spawn_local(server);

        // adapt reader into a sink of byte arrays
        let requests_sink = request_tx
            .into_sink()
            .sink_map_err(|err| JsError::new(&format!("IO error: {err:?}")))
            .with(|js: JsValue| async {
                if js.is_instance_of::<Uint8Array>() {
                    Ok(Uint8Array::from(js).to_vec())
                } else {
                    Err(JsError::new("expected a Uint8Array").into())
                }
            });

        // convert channels into JS streams
        let requests = WritableStream::from_sink(requests_sink);
        let responses = ReadableStream::from_async_read(response_rx, 512);

        // return complete language server interface
        Self {
            requests: requests.into_raw(),
            responses: responses.into_raw(),
        }
    }
}
