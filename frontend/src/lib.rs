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

use std::collections::HashMap;

use diagnostic::DynDiagnostic;
use locate::{entity_info, locate_entity};
use salsa::Database;
use toplevel::{File, Point, Span, Workspace};

pub mod desugar;
pub mod diagnostic;
pub mod infer;
pub mod locate;
pub mod lower;
pub mod parse;
pub mod resolve;
pub mod toplevel;
pub mod types;

/// Returns the set of diagnostics returned by [check_all].
///
/// rust-analyzer doesn't like to type accumulated Salsa values, so this helps
/// diagnostics code be written with the help of LSP.
pub fn check_all_diagnostics(db: &dyn Database, ws: Workspace) -> Vec<&DynDiagnostic> {
    // read the dynamic diagnostics from workspace checking
    check_all::accumulated::<DynDiagnostic>(db, ws)
        .into_iter()
        .map(|d| (d.dyn_eq(), d))
        .collect::<HashMap<_, _>>()
        .into_values()
        .collect()
}

#[salsa::tracked]
pub fn check_all(db: &dyn Database, ws: Workspace) {
    for (_url, file) in ws.files(db).iter() {
        toplevel::file_syntax_errors(db, *file);
        parse::file_relations(db, *file);

        for (_name, rules) in parse::file_rules(db, *file) {
            for rule in rules {
                infer::typed_rule(db, rule);
            }
        }

        for constraint in parse::file_constraints(db, *file) {
            infer::typed_constraint(db, constraint);
        }
    }
}

#[salsa::tracked]
pub fn hover(db: &dyn Database, file: File, at: Point) -> Option<(Span, String)> {
    // locate the entity
    let e = locate_entity(db, file, at)?;

    // get the entity's info
    let info = entity_info(db, e);

    // format the info
    let mut msg = String::new();

    // add the name of the symbol
    if let Some(name) = info.name {
        msg.push_str(&format!("# {name}"));
    }

    // add the type:
    if let Some(ty) = info.ty {
        msg.push_str(&format!("` : {ty}`\n"));
    } else {
        msg.push('\n');
    }

    // add the kind of symbol
    msg.push_str(&format!("{}\n", info.kind));

    // add the symbol's docs
    if let Some(docs) = info.docs {
        msg.push_str(&format!("__{docs}__\n"));
    }

    // create the span
    let span = Span { start: at, end: at };

    // return the complete hover info
    Some((span, msg))
}

pub fn completion(
    db: &dyn Database,
    file: File,
    at: Point,
) -> Option<Vec<lsp_types::CompletionItem>> {
    // fetch the relation table for this file
    let relations = parse::file_relations(db, file);

    // convert each relation into items
    Some(
        relations
            .keys()
            .map(|name| lsp_types::CompletionItem {
                label: name.clone(),
                kind: Some(lsp_types::CompletionItemKind::EVENT),
                // TODO: documentation for the selection
                // TODO: use insert_text/_format to expand out the type of this relation
                ..Default::default()
            })
            .collect(),
    )
}
