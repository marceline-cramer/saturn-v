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

use std::path::PathBuf;

use rayon::iter::{ParallelBridge, ParallelIterator};
use saturn_v_orbit::simulate::{bake, Config};

fn main() {
    let config_path: PathBuf = std::env::args()
        .nth(1)
        .unwrap_or("orbits.toml".to_string())
        .into();

    let baked_path: PathBuf = std::env::args()
        .nth(2)
        .unwrap_or("baked.json".to_string())
        .into();

    let config_src =
        std::fs::read_to_string(&config_path).expect("failed to read orbit configuration");

    let config: Config = toml::from_str(&config_src).expect("failed to parse orbit configuration");

    let mut baked_orbits: Vec<_> = config
        .orbit
        .iter()
        .par_bridge()
        .map(|orbit| bake(&config.simulation, orbit))
        .collect();

    baked_orbits.sort_by_cached_key(|orbit| orbit.name.clone());

    let baked_json =
        serde_json::to_string_pretty(&baked_orbits).expect("failed to serialize orbits");

    if std::fs::exists(&baked_path).expect("failed to check for existing baked JSON") {
        let old_json =
            std::fs::read_to_string(&baked_path).expect("failed to read existing baked JSON");

        if old_json == baked_json {
            println!("baked orbits unchanged");
            return;
        }
    }

    std::fs::write(&baked_path, baked_json).expect("failed to write baked JSON");
}
