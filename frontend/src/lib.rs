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

use salsa::Database;
use toplevel::{File, Point, Span, Workspace};

pub mod diagnostic;
pub mod parse;
pub mod resolve;
pub mod toplevel;
pub mod types;

#[salsa::tracked]
pub fn check_all(db: &dyn Database, ws: Workspace) {
    for (_url, file) in ws.files(db).iter() {
        parse::file_relations(db, *file);
        parse::file_rules(db, *file);
    }
}

#[salsa::tracked]
pub fn hover(db: &dyn Database, file: File, at: Point) -> Option<(Span, String)> {
    let mut list = Vec::new();
    let mut span = Span::default();
    for node in toplevel::node_hierarchy_at(db, file, at) {
        list.push(node.symbol(db));
        span = node.span(db);
    }

    let mut msg = format!("node hierarchy symbols: {list:?}\n");
    for (name, def) in parse::file_relations(db, file) {
        let ty = def.ty(db);
        msg.push_str(&format!("{name}: {ty}\n"));
    }

    for (name, rules) in parse::file_rules(db, file) {
        for rule in rules.iter() {
            let pat = rule.head(db).clone();
            msg.push_str(&format!("{name}: {pat:?}\n"));
        }
    }

    Some((span, msg))
}
