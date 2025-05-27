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

use std::collections::{BTreeMap, BTreeSet, HashSet};

use salsa::{Database, Update};

use crate::{
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind},
    infer::{infer_resolved_relation_type, typed_constraint, typed_rule, TypeKey},
    parse::*,
    resolve::{file_unresolved_types, resolve_relation_type, Unresolved},
    toplevel::{AstNode, File, Point},
    types::WithAst,
};

/// Gets the [EntityInfo] for an [Entity].
#[salsa::tracked]
pub fn entity_info<'db>(db: &'db dyn Database, e: Entity<'db>) -> EntityInfo {
    // get the kind of entity
    let kind = match e.kind(db) {
        EntityKind::Import(_) => "Import",
        EntityKind::File(_) => "File",
        EntityKind::Relation(_) => "Relation",
        EntityKind::Variable { .. } => "Variable",
    }
    .to_string();

    // get the name of the entity
    let name = match e.kind(db) {
        EntityKind::Relation(def) => Some(def.name(db).inner.to_owned()),
        EntityKind::Variable { name, .. } => Some(name.clone()),
        _ => None,
    };

    // TODO: add docs to various items
    let docs = None;

    // get the entity's type
    let ty = match e.kind(db) {
        EntityKind::Relation(def) => {
            let resolved = resolve_relation_type(db, *def);
            let ty = infer_resolved_relation_type(db, resolved);
            Some(ty.to_naive().to_string())
        }
        EntityKind::Variable { name, scope } => {
            let table = match scope {
                Scope::Constraint(constraint) => {
                    let typed = typed_constraint(db, *constraint);
                    Some(typed.body(db).table(db))
                }
                Scope::Rule { rule, body } => typed_rule(db, *rule).map(|rule| match body {
                    Some(idx) => rule.bodies(db)[*idx].table(db),
                    None => rule.head_table(db),
                }),
            };

            match table {
                Some(table) => {
                    let key = TypeKey::Variable(name.clone());
                    Some(table.clone().lookup(&key).to_naive().to_string())
                }
                None => None,
            }
        }
        _ => None,
    };

    // no type definition for now
    let ty_def = None;

    // get the location of the entity's definition
    let def = match e.kind(db) {
        EntityKind::Relation(def) => Some(def.ast(db)),
        EntityKind::Variable { name, scope } => match scope {
            Scope::Constraint(constraint) => constraint_vars(db, *constraint),
            Scope::Rule { rule, body } => {
                let vars = rule_vars(db, *rule);
                match *body {
                    Some(idx) => vars.bodies.get(idx).unwrap().clone(),
                    None => vars.head.clone(),
                }
            }
        }
        .get(name)
        .copied(),
        _ => None,
    };

    // no references for now
    let references = HashSet::new();

    // no implementations for now
    let implementations = HashSet::new();

    // initialize the final entity info
    EntityInfo {
        kind,
        name,
        docs,
        ty,
        ty_def,
        def,
        references,
        implementations,
    }
}

#[derive(Clone, PartialEq, Eq, Update)]
pub struct EntityInfo {
    /// A description of the kind of entity this is.
    pub kind: String,

    /// The name of this entity, if it has one.
    pub name: Option<String>,

    /// The documentation of this entity, if it has any.
    pub docs: Option<String>,

    /// The displayed type of this entity, if it has one.
    pub ty: Option<String>,

    /// The location of this entity's type definition, if it has one.
    pub ty_def: Option<AstNode>,

    /// The location of this entity's definition.
    pub def: Option<AstNode>,

    /// Every reference to this entity.
    pub references: HashSet<AstNode>,

    /// Every implementation of this entity.
    pub implementations: HashSet<AstNode>,
}

/// Locates an [Entity] at a given position in a source file.
#[salsa::tracked]
pub fn locate_entity(db: &dyn Database, file: File, at: Point) -> Option<Entity<'_>> {
    // scan all top-level items of the file
    for (kind, nodes) in file_item_ast(db, file) {
        for ast in nodes {
            if ast.span(db).contains(at) {
                return match kind {
                    ItemKind::Import => Some(Entity::new(db, ast, EntityKind::Import(ast))),
                    ItemKind::Definition => {
                        let def = parse_relation_def(db, ast);
                        locate_definition(db, def, at)
                    }
                    ItemKind::Rule => {
                        let def = parse_rule(db, ast);
                        locate_rule(db, def, at)
                    }
                    ItemKind::Constraint => {
                        let def = parse_constraint(db, ast);
                        locate_constraint(db, def, at)
                    }
                };
            }
        }
    }

    // if no item was found, the entity is the file itself
    Some(Entity::new(
        db,
        file.root(db).unwrap(),
        EntityKind::File(file),
    ))
}

/// Locates an entity within a relation definition.
#[salsa::tracked]
pub fn locate_definition<'db>(
    db: &'db dyn Database,
    def: RelationDefinition<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // if the name of the relation is hovered, that is the entity
    if def.name(db).ast.span(db).contains(at) {
        return Some(Entity::new(db, def.name(db).ast, EntityKind::Relation(def)));
    }

    // locate within the abstract type
    if def.ty(db).ast.span(db).contains(at) {
        return locate_resolved_type(db, def.ty(db), at);
    }

    // otherwise, no entity could be located
    None
}

/// Locates an entity within an abstract type.
pub fn locate_resolved_type<'db>(
    db: &'db dyn Database,
    ty: &WithAst<AbstractType>,
    at: Point,
) -> Option<Entity<'db>> {
    match ty.as_ref() {
        AbstractType::Tuple(els) => {
            for el in els.iter() {
                if el.ast.span(db).contains(at) {
                    return locate_resolved_type(db, el, at);
                }
            }

            None
        }
        AbstractType::Named(name) => match file_unresolved_types(db, ty.ast.file(db)).get(name) {
            Some(Unresolved::Relation(def)) => {
                Some(Entity::new(db, ty.ast, EntityKind::Relation(*def)))
            }
            _ => None,
        },
        AbstractType::Primitive(_) => None,
    }
}

/// Locates an entity within a rule.
#[salsa::tracked]
pub fn locate_rule<'db>(
    db: &'db dyn Database,
    def: AbstractRule<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // if the relation of the rule is hovered, find its definition entity
    let relation = def.relation(db);
    if relation.ast.span(db).contains(at) {
        return file_relation(db, relation.ast.file(db), relation.clone())
            .map(EntityKind::Relation)
            .map(|kind| Entity::new(db, relation.ast, kind));
    }

    // attempt to locate within the head
    if def.head(db).ast.span(db).contains(at) {
        return locate_pattern(db, def, def.head(db), at);
    }

    // attempt to locate within each rule body
    for (idx, body) in def.bodies(db).iter().enumerate() {
        if body.ast(db).span(db).contains(at) {
            let scope = Scope::Rule {
                rule: def,
                body: Some(idx),
            };

            return locate_rule_body(db, scope, *body, at);
        }
    }

    // otherwise, no entity could be located
    None
}

/// Locates an item within a pattern.
pub fn locate_pattern<'db>(
    db: &'db dyn Database,
    rule: AbstractRule<'db>,
    pat: &WithAst<Pattern>,
    at: Point,
) -> Option<Entity<'db>> {
    match pat.as_ref() {
        Pattern::Variable(name) => Some(Entity::new(
            db,
            pat.ast,
            EntityKind::Variable {
                name: name.clone(),
                scope: Scope::Rule { rule, body: None },
            },
        )),
        Pattern::Tuple(els) => {
            for el in els.iter() {
                if el.ast.span(db).contains(at) {
                    return locate_pattern(db, rule, el, at);
                }
            }

            None
        }
        Pattern::Value(_) => None,
    }
}

/// Locates an entity within a constraint.
#[salsa::tracked]
pub fn locate_constraint<'db>(
    db: &'db dyn Database,
    def: AbstractConstraint<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // try to locate within head bindings
    for binding in def.head(db).iter() {
        if binding.ast.span(db).contains(at) {
            return Some(Entity::new(
                db,
                binding.ast,
                EntityKind::Variable {
                    name: binding.inner.clone(),
                    scope: Scope::Constraint(def),
                },
            ));
        }
    }

    // locate within the rule body
    let scope = Scope::Constraint(def);
    locate_rule_body(db, scope, def.body(db), at)
}

/// Locates an entity within a rule body.
#[salsa::tracked]
pub fn locate_rule_body<'db>(
    db: &'db dyn Database,
    scope: Scope<'db>,
    def: AbstractRuleBody<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // simply iterate over each clause and locate within one that contains the cursor
    for clause in def.clauses(db).iter() {
        if clause.ast(db).span(db).contains(at) {
            return locate_expr(db, scope, *clause, at);
        }
    }

    // otherwise, no entity could be located
    None
}

/// Locates an entity within an expression.
#[salsa::tracked]
pub fn locate_expr<'db>(
    db: &'db dyn Database,
    scope: Scope<'db>,
    expr: Expr<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // if this expression's span does not contain the point, return no entity
    // this is the base case for recursive expressions
    if !expr.ast(db).span(db).contains(at) {
        return None;
    }

    // select based on instruction kind
    match expr.kind(db) {
        // find the first tuple element that locates an entity
        ExprKind::Tuple(els) => els
            .into_iter()
            .find_map(|el| locate_expr(db, scope, el, at)),
        // variables are base case entities
        ExprKind::Variable(name) => Some(Entity::new(
            db,
            expr.ast(db),
            EntityKind::Variable { scope, name },
        )),
        // recursively attempt to locate within each branch of a binary operator
        ExprKind::BinaryOp { lhs, rhs, .. } => {
            locate_expr(db, scope, lhs, at).or_else(|| locate_expr(db, scope, rhs, at))
        }
        // passthru unary operators
        ExprKind::UnaryOp { term, .. } => locate_expr(db, scope, term, at),
        // attempt to locate head first, then body otherwise
        ExprKind::Atom { head, body } => {
            if head.ast.span(db).contains(at) {
                let def = file_relation(db, head.ast.file(db), head.clone());
                def.map(EntityKind::Relation)
                    .map(|kind| Entity::new(db, head.ast, kind))
            } else {
                locate_expr(db, scope, body, at)
            }
        }
        // TODO: primitive entities?
        ExprKind::Value(_) => None,
    }
}

/// A singular semantic element in the language.
#[salsa::interned]
pub struct Entity<'db> {
    pub ast: AstNode,

    #[return_ref]
    pub kind: EntityKind<'db>,
}

/// A singular kind of semantic element in the language.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Update)]
pub enum EntityKind<'db> {
    /// An import item. Unimplemented so far.
    Import(AstNode),

    /// Refers to a single file.
    File(File),

    /// A relation definition.
    Relation(RelationDefinition<'db>),

    /// A variable within a rule body, rule, or constraint.
    Variable {
        /// The name of the variable.
        name: String,

        /// The scope of the variable's definition.
        scope: Scope<'db>,
    },
}

/// A variable scope.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Update)]
pub enum Scope<'db> {
    /// The variable is defined in a constraint.
    Constraint(AbstractConstraint<'db>),

    /// The variable is defined in a rule.
    Rule {
        /// The rule the variable is defined in.
        rule: AbstractRule<'db>,

        /// The *specific* index of the rule body this variable is defined in, if any.
        body: Option<usize>,
    },
}

/// Tracks the variable definitions within a constraint.
#[salsa::tracked]
pub fn constraint_vars<'db>(
    db: &'db dyn Database,
    constraint: AbstractConstraint<'db>,
) -> BTreeMap<String, AstNode> {
    // load all of the body's variables
    let mut vars = rule_body_vars(db, constraint.body(db));

    // overwrite variables with definitions from the head
    // run in reverse so that duplicate variables are ordered left-first
    // technically an error but this code should do something about it
    for var in constraint.head(db).iter().rev() {
        if vars.insert(var.inner.clone(), var.ast).is_none() {
            // if this variable is not found within the body, throw an error
            UnboundVariable {
                at: var.clone(),
                body: constraint.body(db).ast(db),
            }
            .accumulate(db);
        }
    }

    // return the complete variables
    vars
}

/// Tracks the [VariableDefinitions] within a rule.
#[salsa::tracked]
pub fn rule_vars<'db>(db: &'db dyn Database, rule: AbstractRule<'db>) -> VariableDefinitions {
    // parse each variable occurrence within the head pattern
    let mut head = BTreeMap::new();
    let mut stack = vec![rule.head(db)];
    while let Some(pat) = stack.pop() {
        use Pattern::*;
        match pat.as_ref() {
            Tuple(els) => stack.extend(els.iter().rev()),
            Value(_) => {}
            Variable(name) => {
                head.entry(name.clone()).or_insert(pat.ast);
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
        for (var, ast) in head.iter() {
            if body.inner.insert(var.clone(), *ast).is_none() {
                // if this variable is not found within the body, throw an error
                UnboundVariable {
                    at: ast.with(var.to_string()),
                    body: body.ast,
                }
                .accumulate(db);
            }
        }
    }

    // remove ASTs from bodies
    let bodies = bodies.into_iter().map(|body| body.inner).collect();

    // return the complete definitions
    VariableDefinitions { head, bodies }
}

/// Tracks the variable definitions within a rule body.
///
/// Notice that this tracks the first occurrence of each variable within a rule
/// body and does not care whether the variable is used in the rule's head.
#[salsa::tracked]
pub fn rule_body_vars<'db>(
    db: &'db dyn Database,
    body: AbstractRuleBody<'db>,
) -> BTreeMap<String, AstNode> {
    // track the map of variables to nodes
    let mut vars = BTreeMap::new();

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
                vars.entry(name).or_insert_with(|| expr.ast(db));
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
    pub head: BTreeMap<String, AstNode>,

    /// Variable definitions within each body of the rule.
    pub bodies: Vec<BTreeMap<String, AstNode>>,
}

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
        .flat_map(|body| rule_body_relations(db, body))
        .collect()
}

/// Finds every rule implementing a relation.
#[salsa::tracked]
pub fn relation_rules<'db>(
    db: &'db dyn Database,
    rel: RelationDefinition<'db>,
) -> BTreeSet<AbstractRule<'db>> {
    // iterate every possible rule in the workspace
    let mut rules = BTreeSet::new();
    for file in rel.ast(db).file(db).workspace(db).files(db).values() {
        for ast in file_item_kind_ast(db, *file, ItemKind::Rule) {
            let rule = parse_rule(db, ast);
            if Some(rel) == file_relation(db, *file, rule.relation(db)) {
                rules.insert(rule);
            }
        }
    }

    // return the complete list of rules
    rules
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
