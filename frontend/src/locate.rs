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

use std::collections::BTreeSet;

use salsa::{Database, Update};

use crate::{
    infer::{infer_resolved_relation_type, typed_constraint, typed_rule, TypeKey},
    lookup,
    parse::*,
    resolve::{file_relation, file_unresolved_types, resolve_relation_type, Unresolved},
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

    // get the location of the entity's references
    let references = match e.kind(db) {
        EntityKind::Relation(def) => vec![def.ast(db)],
        EntityKind::Variable { name, scope } => match scope {
            Scope::Constraint(constraint) => lookup::constraint_vars(db, *constraint),
            Scope::Rule { rule, body } => {
                let vars = lookup::rule_vars(db, *rule);
                match *body {
                    Some(idx) => vars.bodies.get(idx).unwrap().clone(),
                    None => vars.head.clone(),
                }
            }
        }
        .get(name)
        .cloned()
        .unwrap_or_default(),
        _ => vec![],
    };

    // the definition is the first reference, if available
    let def = references.first().cloned();

    // get the locations of the entity's implementations
    let implementations = match e.kind(db) {
        EntityKind::Relation(rel) => lookup::relation_rules(db, *rel)
            .into_iter()
            .map(|rule| rule.relation(db).ast)
            .collect(),
        _ => BTreeSet::new(),
    };

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

#[derive(Clone, PartialEq, Eq, Hash, Update)]
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
    pub references: Vec<AstNode>,

    /// Every implementation of this entity.
    pub implementations: BTreeSet<AstNode>,
}

/// Locates an [Entity] at a given position in a source file.
#[salsa::tracked]
pub fn entity(db: &dyn Database, file: File, at: Point) -> Option<Entity<'_>> {
    // scan all top-level items of the file
    for (kind, nodes) in file_item_ast(db, file) {
        for ast in nodes {
            if ast.span(db).contains(at) {
                return match kind {
                    ItemKind::Import => Some(Entity::new(db, ast, EntityKind::Import(ast))),
                    ItemKind::Definition => {
                        let def = abstract_relation(db, ast);
                        definition(db, def, at)
                    }
                    ItemKind::Rule => {
                        let def = parse_rule(db, ast);
                        rule(db, def, at)
                    }
                    ItemKind::Constraint => {
                        let def = parse_constraint(db, ast);
                        constraint(db, def, at)
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
pub fn definition<'db>(
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
        return resolved_type(db, def.ty(db), at);
    }

    // otherwise, no entity could be located
    None
}

/// Locates an entity within an abstract type.
pub fn resolved_type<'db>(
    db: &'db dyn Database,
    ty: &WithAst<AbstractType>,
    at: Point,
) -> Option<Entity<'db>> {
    match ty.as_ref() {
        AbstractType::Tuple(els) => {
            for el in els.iter() {
                if el.ast.span(db).contains(at) {
                    return resolved_type(db, el, at);
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
pub fn rule<'db>(db: &'db dyn Database, def: AbstractRule<'db>, at: Point) -> Option<Entity<'db>> {
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

            return rule_body(db, scope, *body, at);
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
pub fn constraint<'db>(
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
    rule_body(db, scope, def.body(db), at)
}

/// Locates an entity within a rule body.
#[salsa::tracked]
pub fn rule_body<'db>(
    db: &'db dyn Database,
    scope: Scope<'db>,
    def: AbstractRuleBody<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // simply iterate over each clause and locate within one that contains the cursor
    for clause in def.clauses(db).iter() {
        if clause.ast(db).span(db).contains(at) {
            return expr(db, scope, *clause, at);
        }
    }

    // otherwise, no entity could be located
    None
}

/// Locates an entity within an expression.
#[salsa::tracked]
pub fn expr<'db>(
    db: &'db dyn Database,
    scope: Scope<'db>,
    expr_data: Expr<'db>,
    at: Point,
) -> Option<Entity<'db>> {
    // if this expression's span does not contain the point, return no entity
    // this is the base case for recursive expressions
    if !expr_data.ast(db).span(db).contains(at) {
        return None;
    }

    // select based on instruction kind
    match expr_data.kind(db) {
        // find the first tuple element that locates an entity
        ExprKind::Tuple(els) => els.into_iter().find_map(|el| expr(db, scope, el, at)),
        // variables are base case entities
        ExprKind::Variable(name) => Some(Entity::new(
            db,
            expr_data.ast(db),
            EntityKind::Variable { scope, name },
        )),
        // recursively attempt to locate within each branch of a binary operator
        ExprKind::BinaryOp { lhs, rhs, .. } => {
            expr(db, scope, lhs, at).or_else(|| expr(db, scope, rhs, at))
        }
        // passthru unary operators
        ExprKind::UnaryOp { term, .. } => expr(db, scope, term, at),
        // attempt to locate head first, then body otherwise
        ExprKind::Atom { head, body } => {
            if head.ast.span(db).contains(at) {
                let def = file_relation(db, head.ast.file(db), head.clone());
                def.map(EntityKind::Relation)
                    .map(|kind| Entity::new(db, head.ast, kind))
            } else {
                expr(db, scope, body, at)
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
