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

use std::{collections::BTreeSet, future::Future, sync::Arc};

use leptos::prelude::*;
use leptos_use::use_interval_fn;
use saturn_v_client::*;
use saturn_v_protocol::*;

pub fn use_input<T>(client: &Client, name: &str) -> ReadSignal<BTreeSet<T>>
where
    T: FromValue + Ord + Send + Sync + 'static,
{
    let client = client.clone();
    let name = name.to_string();
    use_query(move || {
        let client = client.clone();
        let name = name.to_string();
        async move { client.get_input(&name).await.unwrap() }
    })
}

pub fn use_output<T>(client: &Client, name: &str) -> ReadSignal<BTreeSet<T>>
where
    T: FromValue + Ord + Send + Sync + 'static,
{
    let client = client.clone();
    let name = name.to_string();
    use_query(move || {
        let client = client.clone();
        let name = name.to_string();
        async move { client.get_output(&name).await.unwrap() }
    })
}

pub fn use_query<T, Q, F>(get_query: impl Fn() -> F + Send + 'static) -> ReadSignal<BTreeSet<T>>
where
    T: FromValue + Ord + Send + Sync + 'static,
    F: Future<Output = Q>,
    Q: QueryRelation,
{
    // create signal to modify the updated values
    let (values, set_values) = signal(BTreeSet::new());
    let get_query = Arc::new(get_query);

    // update values on an interval
    // TODO: work around the browser limiting SSE subscriptions
    use_interval_fn(
        move || {
            let get_query = get_query.clone();
            leptos::task::spawn_local(async move {
                let query = get_query().await;
                let current = query.get_all().await.unwrap();
                set_values.set(BTreeSet::from_iter(current));
            });
        },
        1000,
    );

    // return the getter for the current values
    values
}
