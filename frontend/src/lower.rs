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
use saturn_v_ir::{self as ir, ConstraintWeight};

use crate::{
    desugar::desugar_rule_body,
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind},
    infer::{
        infer_resolved_relation_type, typed_constraint, typed_rule, NaiveType, TypedConstraint,
        TypedRule,
    },
    lookup::relation_is_conditional,
    parse::{file_constraints, file_rules, Pattern, RelationDefinition},
    resolve::resolve_relation_type,
    toplevel::{AstNode, File, Workspace},
    types::WithAst,
};

pub fn lower_workspace<'db>(
    db: &'db dyn Database,
    ws: Workspace,
) -> ir::Program<RelationDefinition<'db>> {
    // merge each file's programs
    ws.files(db)
        .values()
        .map(|file| lower_file(db, *file))
        .fold(ir::Program::default(), |ws, file| ws.merge(file))
}

pub fn lower_file<'db>(db: &'db dyn Database, file: File) -> ir::Program<RelationDefinition<'db>> {
    // add the lowered rules
    let mut relations: HashMap<_, ir::Relation<_>> = HashMap::new();
    for rule in file_rules(db, file).values().flatten() {
        // type a rule, if possible
        let Some(typed) = typed_rule(db, *rule) else {
            continue;
        };

        // resolve the relation type
        let ty = resolve_relation_type(db, typed.relation(db));

        // infer it
        let ty = infer_resolved_relation_type(db, ty).to_naive();

        // flatten the head type
        let Some(head) = ty.flatten() else {
            continue;
        };

        // format the output
        let formatting = format_tuple(rule.relation(db).as_ref(), &ty);

        // pick the kind of the relation
        let relation = typed.relation(db);
        let kind = if relation.is_decision(db) {
            ir::RelationKind::Decision
        } else if relation_is_conditional(db, relation) {
            ir::RelationKind::Conditional
        } else {
            ir::RelationKind::Basic
        };

        // initialize the lowered relation
        let relation = relations.entry(typed.relation(db)).or_insert(ir::Relation {
            store: typed.relation(db),
            facts: Vec::new(),
            rules: Vec::new(),
            is_output: typed.relation(db).is_output(db),
            ty: head.into_iter().map(Into::into).collect(),
            kind,
            formatting,
        });

        // lower the rule and then add it to the relation based on kind
        match lower_rule(db, typed) {
            BodiesOrFact::Bodies(rules) => relation.rules.extend(rules),
            BodiesOrFact::Fact(fact) => relation.facts.push(fact),
        }
    }

    // add the lowered constraints
    let mut constraints = Vec::new();
    for constraint in file_constraints(db, file) {
        // type the constraint
        let typed = typed_constraint(db, constraint);

        // lower it
        let lowered = lower_constraint(db, typed);

        // add it to the list of constraints
        constraints.push(lowered);
    }

    // return the completed program
    ir::Program {
        relations,
        constraints,
    }
}

/// Create formatting string segments out of a naive type.
pub fn format_tuple(name: &str, ty: &NaiveType) -> Vec<String> {
    // create the formatted string list
    let mut formatted = vec![name.to_string()];

    // format the inner string
    format_naive(ty, true, &mut formatted);

    // append the period to the formatted
    formatted.last_mut().unwrap().push('.');

    // return the completed formatting string
    formatted
}

/// Returns whether a token has been newly pushed.
pub fn format_naive(ty: &NaiveType, first: bool, formatted: &mut Vec<String>) {
    match ty {
        NaiveType::Tuple(els) => {
            formatted.last_mut().unwrap().push('(');

            for (idx, el) in els.iter().enumerate() {
                if idx != 0 {
                    formatted.last_mut().unwrap().push_str(", ");
                }

                format_naive(el, false, formatted);
            }

            formatted.last_mut().unwrap().push(')');
        }
        NaiveType::Primitive(_) => {
            if first {
                formatted.last_mut().unwrap().push(' ');
            }

            formatted.push("".to_string());
        }
        // flattening is performed before formatting
        // panic is alright
        NaiveType::Unknown => unreachable!(),
    }
}

pub fn lower_constraint<'db>(
    db: &'db dyn Database,
    constraint: TypedConstraint<'db>,
) -> ir::Constraint<RelationDefinition<'db>> {
    // desugar the rule body
    let mut desugarer = desugar_rule_body(db, constraint.body(db));

    // find the constraint weight
    let weight = match constraint.constraint(db).soft(db) {
        Some(weight) => ConstraintWeight::Soft(weight.inner),
        None => ConstraintWeight::Hard,
    };

    // allocate and track each variable in the head
    // all variables are confirmed to be bound at this point
    let head: Vec<_> = constraint
        .constraint(db)
        .head(db)
        .iter()
        .flat_map(|binding| desugarer.allocate_variable(db, binding.to_string()))
        .collect();

    // all head variables are needed
    let needed_variables = head.iter().copied().collect();

    // lower the body
    let body = saturn_v_lower::lower_rule_body(desugarer.to_rule_body(needed_variables));

    // create the final constraint
    ir::Constraint {
        weight,
        kind: constraint.constraint(db).kind(db).inner,
        head,
        body,
    }
}

pub fn lower_rule<'db>(db: &'db dyn Database, rule: TypedRule<'db>) -> BodiesOrFact<'db> {
    // how to lower depends on whether the rule has bodies
    if rule.bodies(db).is_empty() {
        // recursively create a list of values
        let mut stack = vec![rule.inner(db).head(db).clone()];
        let mut values = Vec::new();
        let mut failure = false;
        while let Some(pat) = stack.pop() {
            match pat.as_ref() {
                // TODO: implicit rules
                Pattern::Variable(name) => {
                    // emit error diagnostic
                    CannotAssignVariable {
                        variable: pat.with(name.to_string()),
                    }
                    .accumulate(db);

                    // make sure we track error to not push faulty facts
                    failure = true;
                }
                Pattern::Value(val) => values.push(val.clone()),
                Pattern::Tuple(els) => stack.extend(els.iter().rev().cloned()),
            }
        }

        if failure {
            // if failure, return empty bodies
            BodiesOrFact::Bodies(vec![])
        } else {
            // otherwise, create the complete fact from the values
            BodiesOrFact::Fact(values)
        }
    } else {
        // if the rule has bodies, turn each rule body into an IR rule
        let mut bodies = Vec::new();
        for body in rule.bodies(db) {
            // desugar the rule body
            let mut desugarer = desugar_rule_body(db, *body);

            // create a desugared head out of the rule's head pattern
            let mut head = Vec::new();
            let mut needed_variables = HashSet::new();
            desugarer.desugar_pattern(
                db,
                rule.inner(db).head(db),
                &mut head,
                &mut needed_variables,
            );

            // lower the rule body
            let body = saturn_v_lower::lower_rule_body(desugarer.to_rule_body(needed_variables));

            // add it to the list
            bodies.push(ir::Rule { body, head });
        }

        // return the total list of lowered bodies
        BodiesOrFact::Bodies(bodies)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BodiesOrFact<'db> {
    Bodies(Vec<ir::Rule<RelationDefinition<'db>>>),
    Fact(Vec<ir::Value>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CannotAssignVariable {
    pub variable: WithAst<String>,
}

impl BasicDiagnostic for CannotAssignVariable {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.variable.ast..self.variable.ast
    }

    fn message(&self) -> String {
        format!("cannot assign value to {:?}", self.variable)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}
