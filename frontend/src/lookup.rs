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

use std::collections::{BTreeMap, BTreeSet};

use salsa::{Database, Update};

use crate::{
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind},
    parse::*,
    toplevel::{AstNode, Workspace},
    types::WithAst,
};

/// Looks up the variable definitions within a constraint.
#[salsa::tracked]
pub fn constraint_vars<'db>(
    db: &'db dyn Database,
    constraint: AbstractConstraint<'db>,
) -> VariableMap {
    // load all of the body's variables
    let mut vars = rule_body_vars(db, constraint.body(db));

    // push variables with definitions from the head to the front of variable references
    // run in reverse so that duplicate variables are ordered left-first
    // technically an error but this code should do something about it
    for var in constraint.head(db).iter() {
        // look up the entry in the body for this variable
        let entry = vars.entry(var.inner.clone());

        // if this variable is not found within the body, throw an error
        use std::collections::btree_map::Entry;
        if let Entry::Vacant(_) = &entry {
            UnboundVariable {
                at: var.clone(),
                body: constraint.body(db).ast(db),
            }
            .accumulate(db);
        }

        // add the variable definition to the def maps
        entry.or_default().insert(0, var.ast);
    }

    // return the complete variables
    vars
}

/// Looks up the [VariableDefinitions] within a rule.
#[salsa::tracked]
pub fn rule_vars<'db>(db: &'db dyn Database, rule: AbstractRule<'db>) -> VariableDefinitions {
    // parse each variable occurrence within the head pattern
    let mut head: VariableMap = BTreeMap::new();
    let mut stack = vec![rule.head(db)];
    while let Some(pat) = stack.pop() {
        use Pattern::*;
        match pat.as_ref() {
            Tuple(els) => stack.extend(els.iter().rev()),
            Value(_) => {}
            Variable(name) => {
                head.entry(name.clone()).or_default().push(pat.ast);
            }
        }
    }

    // find variable definitions from each body
    let mut bodies: Vec<_> = rule
        .bodies(db)
        .iter()
        .map(|body| body.ast(db).with(rule_body_vars(db, *body)))
        .collect();

    // merge head variable definitions into each body's variables
    for body in bodies.iter_mut() {
        for (var, asts) in head.iter_mut() {
            // look up the entry in the body for this variable
            let entry = body.inner.entry(var.clone());

            // if this variable is not found within the body, throw an error
            use std::collections::btree_map::Entry;
            let is_unbound = matches!(entry, Entry::Vacant(_));

            // create the base head variable map
            let entry = entry.or_default();

            // add each head binding to this variable to the map
            for ast in asts.iter() {
                if is_unbound {
                    UnboundVariable {
                        at: ast.with(var.to_string()),
                        body: body.ast,
                    }
                    .accumulate(db);
                }

                // add the variable definition to the body's var map
                entry.insert(0, *ast);
            }

            // add all of the body's definitions to the head
            asts.extend(entry.iter().copied());
        }
    }

    // remove ASTs from bodies
    let bodies = bodies.into_iter().map(|body| body.inner).collect();

    // return the complete definitions
    VariableDefinitions { head, bodies }
}

/// Looks up the variable definitions within a rule body.
///
/// Notice that this tracks the first occurrence of each variable within a rule
/// body and does not care whether the variable is used in the rule's head.
#[salsa::tracked]
pub fn rule_body_vars<'db>(db: &'db dyn Database, body: AbstractRuleBody<'db>) -> VariableMap {
    // track the map of variables to nodes
    let mut vars: VariableMap = BTreeMap::new();

    // track each expression to look within, in last-to-first order
    let mut stack = body.clauses(db).clone();

    // flip clauses so that first clauses are popped first
    stack.reverse();

    // iterate through all expressions
    while let Some(expr) = stack.pop() {
        use ExprKind::*;
        match expr.kind(db) {
            Tuple(els) => stack.extend(els.iter().rev()),
            Value(_) => {}
            Variable(name) => {
                vars.entry(name).or_default().push(expr.ast(db));
            }
            BinaryOp { lhs, rhs, .. } => {
                // push rhs first because it is popped last
                stack.push(rhs);
                stack.push(lhs);
            }
            UnaryOp { term, .. } => {
                stack.push(term);
            }
            Atom { body, .. } => {
                stack.push(body);
            }
        }
    }

    // return the complete map
    vars
}

/// Tracks the locations of each variable within a rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Update)]
pub struct VariableDefinitions {
    /// Variable definitions within the head of the rule.
    pub head: VariableMap,

    /// Variable definitions within each body of the rule.
    pub bodies: Vec<VariableMap>,
}

/// Maps a variable's name to the location of each of its references.
pub type VariableMap = BTreeMap<String, Vec<AstNode>>;

/// Tracks if a relation is conditional or not.
#[salsa::tracked]
pub fn relation_is_conditional<'db>(db: &'db dyn Database, rel: RelationDefinition<'db>) -> bool {
    relation_indirect_deps(db, rel)
        .into_iter()
        .any(|dep| dep.is_decision(db))
}

/// Enumerates every indirect relation definition of a relation.
#[salsa::tracked]
pub fn relation_indirect_deps<'db>(
    db: &'db dyn Database,
    rel: RelationDefinition<'db>,
) -> BTreeSet<RelationDefinition<'db>> {
    // maintain the set of deps
    let mut deps = BTreeSet::new();

    // keep a stack of relations to search
    let mut stack = vec![rel];

    // repeatedly iterate until all relations are found
    while let Some(rel) = stack.pop() {
        // get all direct deps of this relation
        let direct = relation_direct_deps(db, rel);

        // further search all new direct deps
        // avoids cycles by tracking repeat insertion
        for dep in direct {
            if deps.insert(dep) {
                stack.push(dep);
            }
        }
    }

    // return the complete set of deps
    deps
}

/// Enumerates every direct relation definition of a relation.
#[salsa::tracked]
pub fn relation_direct_deps<'db>(
    db: &'db dyn Database,
    rel: RelationDefinition<'db>,
) -> BTreeSet<RelationDefinition<'db>> {
    relation_rules(db, rel)
        .into_iter()
        .flat_map(|rule| rule.bodies(db).clone())
        .flat_map(|body| rule_body_relations(db, body).into_keys())
        .collect()
}

/// Finds every rule implementing a particular relation.
#[salsa::tracked]
pub fn relation_rules<'db>(
    db: &'db dyn Database,
    rel: RelationDefinition<'db>,
) -> BTreeSet<AbstractRule<'db>> {
    relation_to_rules(db, rel.ast(db).file(db).workspace(db))
        .get(&rel)
        .cloned()
        .unwrap_or_default()
}

/// Enumerates the rules of every relation in the workspace.
///
/// You probably want to use [relation_rules] instead.
#[salsa::tracked]
pub fn relation_to_rules<'db>(
    db: &'db dyn Database,
    ws: Workspace,
) -> BTreeMap<RelationDefinition<'db>, BTreeSet<AbstractRule<'db>>> {
    // iterate every possible rule in the workspace
    let mut to_rules: BTreeMap<_, BTreeSet<_>> = BTreeMap::new();
    for file in ws.files(db).values() {
        for ast in file_item_kind_ast(db, *file, ItemKind::Rule) {
            let rule = parse_rule(db, ast);
            if let Some(rel) = file_relation(db, *file, rule.relation(db)) {
                to_rules.entry(rel).or_default().insert(rule);
            }
        }
    }

    // return the complete list of rules
    to_rules
}

/// Retrieves the set of relations used by a rule body.
#[salsa::tracked]
pub fn rule_body_relations<'db>(
    db: &'db dyn Database,
    body: AbstractRuleBody<'db>,
) -> BTreeSet<RelationDefinition<'db>> {
    // iterate over each expression
    let mut relations = BTreeSet::new();
    let mut stack = body.clauses(db).clone();
    while let Some(expr) = stack.pop() {
        use ExprKind::*;
        match expr.kind(db) {
            Tuple(els) => stack.extend(els),
            BinaryOp { lhs, rhs, .. } => stack.extend([lhs, rhs]),
            UnaryOp { term, .. } => stack.push(term),
            Atom { head, body } => {
                let file = head.ast.file(db);
                relations.extend(file_relation(db, file, head));
                stack.push(body);
            }
            _ => {}
        }
    }

    // return the complete set
    relations
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct UnboundVariable {
    pub at: WithAst<String>,
    pub body: AstNode,
}

impl BasicDiagnostic for UnboundVariable {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.at.ast..self.at.ast
    }

    fn message(&self) -> String {
        format!("variable {} is not bound by rule body", self.at)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![self.body.with("the rule body in question".to_string())]
    }
}
