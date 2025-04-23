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

use std::collections::{HashMap, HashSet};

use salsa::Database;

use crate::toplevel::{AstNode, File, Span};

/// A definition of a relation.
// TODO: add commment above definition AST node for documentation
#[salsa::interned]
pub struct RelationDefinition {
    /// The file this relation was defined in.
    pub file: File,

    /// The span within the file this relation was defined in.
    pub span: Span,

    /// The name of this relation.
    pub name: String,

    /// Whether this relation is a decision.
    pub is_decision: bool,

    /// Whether this relation is a output.
    pub is_output: bool,
}

/// Gets the full relation table of a file.
#[salsa::tracked]
pub fn file_relations(db: &dyn Database, file: File) -> HashMap<String, RelationDefinition<'_>> {
    // iterate over all definition items
    let mut relations = HashMap::new();
    for node in file_item_kind_ast(db, file, ItemKind::Definition) {
        let def = parse_relation_def(db, node);
        // TODO: emit error diagnostic when relation is already defined
        relations.insert(def.name(db).clone(), def);
    }

    // done!
    relations
}

/// Parses a relation from a relation definition AST node.
#[salsa::tracked]
pub fn parse_relation_def(db: &dyn Database, node: AstNode) -> RelationDefinition<'_> {
    // get file info
    let file = node.file(db);

    // get the name
    let relation = node.expect_field(db, "relation");
    let name = relation.contents(db).clone().unwrap();
    let span = relation.span(db);

    // relation attributes
    let is_decision = node.get_field(db, "decision").is_some();
    let is_output = node.get_field(db, "output").is_some();

    // create the full decision
    RelationDefinition::new(db, file, span, name, is_decision, is_output)
}

/// Gets all top-level AST nodes of a particular item kind from a file.
#[salsa::tracked]
pub fn file_item_kind_ast(db: &dyn Database, file: File, kind: ItemKind) -> HashSet<AstNode> {
    file_item_ast(db, file)
        .get(&kind)
        .cloned()
        .unwrap_or_default()
}

/// Gets the top-level item AST nodes from a file.
#[salsa::tracked]
pub fn file_item_ast(db: &dyn Database, file: File) -> HashMap<ItemKind, HashSet<AstNode>> {
    // get top-level information
    let ast = file.ast(db);
    let root = ast.get(&file.root(db)).unwrap();

    // iterate all children
    let mut items: HashMap<_, HashSet<_>> = HashMap::default();
    for child in root.children(db).iter() {
        let child = ast.get(child).unwrap();

        // select item kind based on symbol
        use ItemKind::*;
        let kind = match child.symbol(db) {
            "import" => Import,
            "definition" => Definition,
            "rule" => Rule,
            "constraint" => Constraint,
            // TODO: accumulate a diagnostic?
            _ => continue,
        };

        // add this AST to the items list
        items.entry(kind).or_default().insert(*child);
    }

    // all done :)
    items
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Import,
    Definition,
    Rule,
    Constraint,
}
