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

use std::collections::HashMap;

use diagnostic::DynDiagnostic;
use infer::TypeKey;
use locate::{entity, entity_info};
use parse::{AbstractConstraint, AbstractRule};
use salsa::Database;
use toplevel::{AstNode, File, NamespaceItem, Point, Span, Workspace};

pub mod desugar;
pub mod diagnostic;
pub mod infer;
pub mod locate;
pub mod lookup;
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
        let interns = resolve::file_interns(db, *file);

        // compute relation stratums to surface non-monotonic diagnostics
        for (_name, item) in interns {
            match item.inner {
                NamespaceItem::Relation(rel) => {
                    // compute stratum which will walk body relations and emit warnings
                    lookup::relation_stratum(db, rel);
                }
                _ => {}
            }
        }

        for (_name, rules) in parse::file_rules(db, *file) {
            for rule in rules {
                infer::typed_rule(db, rule);
                lookup::rule_vars(db, rule);
            }
        }

        for constraint in parse::file_constraints(db, *file) {
            infer::typed_constraint(db, constraint);
            lookup::constraint_vars(db, constraint);
        }
    }
}

#[salsa::tracked]
pub fn hover(db: &dyn Database, file: File, at: Point) -> Option<(Span, String)> {
    // locate the entity
    let e = entity(db, file, at)?;

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

    // return the complete hover info
    Some((e.ast(db).span(db), msg))
}

pub fn completion(
    db: &dyn Database,
    file: File,
    _at: Point,
) -> Option<Vec<lsp_types::CompletionItem>> {
    Some(
        resolve::file_interns(db, file)
            .into_iter()
            .flat_map(|(name, item)| item_to_completion(db, name, item.inner))
            .collect(),
    )
}

pub fn item_to_completion(
    _db: &dyn Database,
    label: String,
    item: NamespaceItem,
) -> Option<lsp_types::CompletionItem> {
    // TODO: item documentation
    // TODO: use insert_text/_format to expand out completions
    use lsp_types::*;
    match item {
        NamespaceItem::File(_file) => Some(CompletionItem {
            label,
            kind: Some(CompletionItemKind::FILE),
            ..Default::default()
        }),
        NamespaceItem::Relation(_rel) => Some(CompletionItem {
            label,
            kind: Some(CompletionItemKind::EVENT),
            ..Default::default()
        }),
        NamespaceItem::TypeAlias(_alias) => Some(CompletionItem {
            label,
            kind: Some(CompletionItemKind::STRUCT),
            ..Default::default()
        }),
        _ => None,
    }
}

#[salsa::tracked]
pub fn file_inlay_hints(db: &dyn Database, file: File) -> Vec<(AstNode, String)> {
    // track the list of hints
    let mut hints = Vec::new();

    // add all rules
    for ast in parse::file_item_kind_ast(db, file, parse::ItemKind::Rule) {
        let rule = parse::parse_rule(db, ast);
        hints.extend(rule_inlay_hints(db, rule));
    }

    // add all constraints
    for ast in parse::file_item_kind_ast(db, file, parse::ItemKind::Constraint) {
        let constraint = parse::parse_constraint(db, ast);
        hints.extend(constraint_inlay_hints(db, constraint));
    }

    // return the list of hints
    hints
}
#[salsa::tracked]
pub fn constraint_inlay_hints<'db>(
    db: &'db dyn Database,
    constraint: AbstractConstraint<'db>,
) -> Vec<(AstNode, String)> {
    // track the list of hints
    let mut hints = Vec::new();

    // type the constraint
    let typed = infer::typed_constraint(db, constraint);

    // retrieve the variables in the constraint
    let vars = lookup::constraint_vars(db, constraint);

    // provide type inlay hints for each variable
    let mut typed = typed.body(db).table(db).clone();
    for (name, refs) in vars {
        let ty = typed.lookup(&TypeKey::Variable(name.clone()));
        let msg = format!(": {}", ty.to_naive());
        hints.push((*refs.first().unwrap(), msg));
    }

    // return the completed list
    hints
}

#[salsa::tracked]
pub fn rule_inlay_hints<'db>(
    db: &'db dyn Database,
    rule: AbstractRule<'db>,
) -> Vec<(AstNode, String)> {
    // track the list of hints
    let mut hints = Vec::new();

    // type the rule
    let Some(typed) = infer::typed_rule(db, rule) else {
        return hints;
    };

    // retrieve the variables in the rule
    let vars = lookup::rule_vars(db, rule);

    // first, provide inlay hints for each head
    let mut typed_head = typed.head_table(db).clone();
    for (name, refs) in vars.head.iter() {
        let ty = typed_head.lookup(&TypeKey::Variable(name.clone()));
        let msg = format!(": {}", ty.to_naive());
        hints.push((*refs.first().unwrap(), msg));
    }

    // provide inlay hints for each body
    for (body, typed) in vars.bodies.into_iter().zip(typed.bodies(db)) {
        let mut typed_body = typed.table(db).to_owned().clone();
        for (name, refs) in body {
            // do not label head variables twice
            if vars.head.contains_key(&name) {
                continue;
            }

            let ty = typed_body.lookup(&TypeKey::Variable(name.clone()));
            let msg = format!(": {}", ty.to_naive());
            hints.push((*refs.first().unwrap(), msg));
        }
    }

    // return the completed list
    hints
}
