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

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
};

use salsa::{Database, Update};
use saturn_v_ir::BinaryOpCategory;

use crate::{
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind},
    parse::*,
    resolve::{resolve_relation_type, ResolvedRelationType, ResolvedType, ResolvedTypeAlias},
    toplevel::AstNode,
    types::{PrimitiveType, WithAst},
};

#[salsa::tracked]
pub fn typed_constraint<'db>(
    db: &'db dyn Database,
    constraint: AbstractConstraint<'db>,
) -> TypedConstraint<'db> {
    // simply type the rule body
    let table = full_rule_body_type_table(db, constraint.body(db));

    // unifying the rule body with the constraint head would go here, but...
    // not sure exactly how to implement that quite yet
    let body = TypedRuleBody::new(db, table, constraint.body(db));

    // create the typed constraint
    TypedConstraint::new(db, constraint, body)
}

#[salsa::tracked]
pub struct TypedConstraint<'db> {
    /// The abstract constraint to be typed.
    pub constraint: AbstractConstraint<'db>,

    /// The typed rule body.
    pub body: TypedRuleBody<'db>,
}

#[salsa::tracked]
pub fn typed_rule<'db>(db: &'db dyn Database, rule: AbstractRule<'db>) -> Option<TypedRule<'db>> {
    // create the basic type tables for each rule
    // done first so that type errors inside bodies are caught even if their
    // heads are invalid
    let bodies = rule
        .bodies(db)
        .iter()
        .copied()
        .map(|body| (body, full_rule_body_type_table(db, body)));

    // resolve the relation definition, if available
    let def = file_relation(db, rule.relation(db).ast.file(db), rule.relation(db).inner)?;

    // turn the head pattern into a type
    let head = rule.head(db).clone().map(|head| head.into());

    // resolve the relation type
    let ty = resolve_relation_type(db, def);

    // infer it
    let ty = infer_resolved_relation_type(db, ty);

    // for each body, unify the relation's type with the head
    let bodies = bodies
        .map(|(body, mut table)| {
            // unify the head pattern's type with the relation
            table.unify(db, &ty, &head);

            // initialize the full, typed rule body
            TypedRuleBody::new(db, table, body)
        })
        .collect();

    // create the total rule
    Some(TypedRule::new(db, def, bodies))
}

#[salsa::tracked]
pub struct TypedRule<'db> {
    /// The relation that this rule targets.
    pub relation: RelationDefinition<'db>,

    /// The typed rule bodies.
    pub bodies: Vec<TypedRuleBody<'db>>,
}

#[salsa::tracked]
pub struct TypedRuleBody<'db> {
    /// The [TypeTable] providing type information for this rule body.
    pub table: TypeTable<'db>,

    /// The abstract rule body.
    pub inner: AbstractRuleBody<'db>,
}

#[salsa::tracked]
pub fn full_rule_body_type_table<'db>(
    db: &'db dyn Database,
    body: AbstractRuleBody<'db>,
) -> TypeTable<'db> {
    // begin with the base type table, only inferring clauses
    let mut table = base_rule_body_type_table(db, body);

    // iterate over each key in the table
    for (key, entry) in table.map.clone().iter() {
        // filter out only relations
        let TypeKey::Relation(relation) = key else {
            continue;
        };

        // resolve the relation definition
        let Some(def) = file_relations(db, body.ast(db).file(db))
            .get(relation)
            .copied()
        else {
            // TODO: log an error
            continue;
        };

        // resolve the relation type
        let ty = resolve_relation_type(db, def);

        // infer it
        let ty = infer_resolved_relation_type(db, ty);

        // unify the relation in the type table with the inferred type
        let rhs = entry.with(key.clone().into());
        table.unify(db, &ty, &rhs);
    }

    // return the inferred table
    table
}

#[salsa::tracked]
pub fn base_rule_body_type_table<'db>(
    db: &'db dyn Database,
    body: AbstractRuleBody<'db>,
) -> TypeTable<'db> {
    // simply merge each clause's type table
    body.clauses(db)
        .iter()
        .map(|clause| clause_type_table(db, *clause))
        .fold(TypeTable::default(), |acc, table| acc.merge(db, table))
}

#[salsa::tracked]
pub fn clause_type_table<'db>(db: &'db dyn Database, clause: Expr<'db>) -> TypeTable<'db> {
    // create a blank table
    let mut table = TypeTable::default();

    // infer this clause's expression
    let expr = table.infer_expr(db, clause).map(Into::into);

    // every clause should evaluate to a Boolean
    let ty = WithAst::new(clause.ast(db), PrimitiveType::Boolean.into());
    table.unify(db, &expr, &ty);

    // return the completed table
    table
}

#[salsa::tracked]
pub fn infer_resolved_relation_type<'db>(
    db: &'db dyn Database,
    ty: ResolvedRelationType<'db>,
) -> WithAst<TableType<'db>> {
    infer_resolved_type(db, ty.kind(db))
}

#[salsa::tracked]
pub fn infer_resolved_type_alias<'db>(
    db: &'db dyn Database,
    ty: ResolvedTypeAlias<'db>,
) -> WithAst<TableType<'db>> {
    infer_resolved_type(db, ty.kind(db))
}

pub fn infer_resolved_type<'db>(
    db: &'db dyn Database,
    ty: WithAst<ResolvedType<'db>>,
) -> WithAst<TableType<'db>> {
    let kind = match ty.as_ref() {
        ResolvedType::Primitive(prim) => TableType::Primitive(*prim),
        ResolvedType::Tuple(els) => TableType::Tuple(
            els.iter()
                .cloned()
                .map(|el| infer_resolved_type(db, el))
                .collect(),
        ),
        ResolvedType::Relation(relation) => return infer_resolved_relation_type(db, *relation),
        ResolvedType::Alias(alias) => return infer_resolved_type_alias(db, *alias),
        ResolvedType::Unknown => TableType::Unknown,
    };

    ty.with(kind)
}

#[derive(Clone, Default, PartialEq, Eq, Hash, Update)]
pub struct TypeTable<'db> {
    map: BTreeMap<TypeKey<'db>, WithAst<TableType<'db>>>,
    relations: BTreeSet<String>,
    sound: bool,
}

impl<'db> TypeTable<'db> {
    /// Type-infers an expression. Returns its key.
    pub fn infer_expr(&mut self, db: &'db dyn Database, expr: Expr<'db>) -> WithAst<TypeKey<'db>> {
        // determine what type this expression should be based on kind
        use ExprKind::*;
        let ty = match expr.kind(db) {
            Tuple(els) => TableType::Tuple(
                els.iter()
                    .map(|el| self.infer_expr(db, *el))
                    .map(|el| el.map(Into::into))
                    .collect(),
            ),
            Value(value) => TableType::Primitive(value.ty().into()),
            Variable(name) => TableType::Key(TypeKey::Variable(name.clone())),
            BinaryOp { op, lhs, rhs } => {
                // type-infer operands
                let lhs = self.infer_expr(db, lhs).map(Into::into);
                let rhs = self.infer_expr(db, rhs).map(Into::into);

                // pick the type of expression based on the operator
                use BinaryOpCategory::*;
                match op.category() {
                    // numerical arithmetic works on some types
                    Arithmetic => {
                        // TODO: constrain sum types of operands using operator
                        self.unify(db, &lhs, &rhs);
                        lhs.inner
                    }
                    // string operations work on strings only
                    String => {
                        let string = TableType::Primitive(PrimitiveType::String);
                        let ty = op.with(string.clone());
                        self.unify(db, &lhs, &ty);
                        self.unify(db, &rhs, &ty);
                        string
                    }
                    // logical operations work on booleans only
                    Logical => {
                        let boolean = TableType::Primitive(PrimitiveType::Boolean);
                        let ty = op.with(boolean.clone());
                        self.unify(db, &lhs, &ty);
                        self.unify(db, &rhs, &ty);
                        boolean
                    }
                    // comparison makes boolean with any same-typed terms
                    Comparison => {
                        self.unify(db, &lhs, &rhs);
                        PrimitiveType::Boolean.into()
                    }
                }
            }
            UnaryOp { op, term } => {
                // type-infer inner term
                let term = self.infer_expr(db, term).map(Into::into);

                // determine expected type based on operator
                match op.inner {
                    UnaryOpKind::Not => {
                        let boolean: TableType = PrimitiveType::Boolean.into();
                        let ty = op.with(boolean.clone());
                        self.unify(db, &term, &ty);
                        boolean
                    }
                    UnaryOpKind::Negate => {
                        // TODO constrain to either integer or real
                        term.inner
                    }
                }
            }
            Atom { head, body } => {
                // type-infer body
                let body = self.infer_expr(db, body).map(Into::into);

                // unify body with relation key type
                let relation = TypeKey::Relation(head.inner.clone()).into();
                let ty = head.with(relation);
                self.unify(db, &ty, &body);

                // expression evaluates to a boolean
                PrimitiveType::Boolean.into()
            }
        };

        // unify this expression with its type
        let key = WithAst::new(expr.ast(db), TypeKey::Expr(expr));
        let lhs = key.with(TableType::Key(key.inner.clone()));
        let rhs = key.with(ty);
        self.unify(db, &lhs, &rhs);

        // return the key to this expression
        key
    }

    /// Applies the current inference map to a given inference type.
    ///
    /// Mutates the inference map along the way to cache nested variable
    /// indirections.
    pub fn apply(&mut self, ty: &WithAst<TableType<'db>>) -> WithAst<TableType<'db>> {
        use TableType::*;
        match ty.as_ref() {
            Tuple(els) => ty.with(Tuple(els.iter().map(|ty| self.apply(ty)).collect())),
            Key(key) => match self.map.get(key).cloned() {
                None => ty.with(Key(key.clone())),
                Some(applied) => {
                    let applied = self.apply(&applied);
                    self.map.insert(key.clone(), applied.clone());
                    applied
                }
            },
            _ => ty.clone(),
        }
    }

    /// Gets the flattened type of a given type.
    ///
    /// Returns `None` if any unknown types were encountered.
    ///
    /// No AST is necessary because this is intended to be used by desugaring.
    pub fn flatten(&self, ty: &TableType<'db>) -> Option<Vec<PrimitiveType>> {
        use TableType::*;
        match ty {
            // recursively concatenate flattened tuple elements
            Tuple(els) => {
                let mut tys = Vec::with_capacity(els.len());

                for el in els.iter() {
                    let el_ty = self.flatten(el)?;
                    tys.extend(el_ty);
                }

                Some(tys)
            }
            // primitive base case
            Primitive(ty) => Some(vec![*ty]),
            // recursively dereference and flatten keys
            Key(key) => self.flatten(self.map.get(key)?),
            // unknown types are a failure
            Unknown => None,
        }
    }

    /// Unifies two types and rollbacks the inference map in the presence of errors.
    pub fn unify(
        &mut self,
        db: &'db dyn Database,
        lhs: &WithAst<TableType<'db>>,
        rhs: &WithAst<TableType<'db>>,
    ) {
        // make a backup
        let backup = self.map.clone();

        // try the unification and restore if necessary
        if !self.try_unify(db, lhs, rhs) {
            self.map = backup;
            self.sound = false;
        }
    }

    /// Fallibly unify two types in this table. Returns if successful. This may
    /// mutate the inference map, so keep a backup or use [Self::unify] if you
    /// want to rollback.
    pub fn try_unify(
        &mut self,
        db: &'db dyn Database,
        lhs: &WithAst<TableType<'db>>,
        rhs: &WithAst<TableType<'db>>,
    ) -> bool {
        // fully apply type substitutions of sides
        let lhs = self.apply(lhs);
        let rhs = self.apply(rhs);

        // recursively unify
        use TableType::*;
        match (lhs.as_ref(), rhs.as_ref()) {
            // unknown types unify with anything
            (Unknown, _) | (_, Unknown) => true,
            // tautological unification simply succeeds
            (Key(lhs), Key(rhs)) if lhs == rhs => true,
            // safely create substitutions in inference map
            (Key(key), _) => self.insert(db, key.clone(), rhs),
            (_, Key(key)) => self.insert(db, key.clone(), lhs),
            // recursively unify tuples
            (Tuple(lhs_els), Tuple(rhs_els)) => {
                // unify as many elements of both elements as possible
                let mut success = true;
                for (lhs, rhs) in lhs_els.iter().zip(rhs_els.iter()) {
                    success = success && self.try_unify(db, lhs, rhs);
                }

                // if the tuples are of mismatching size, log an error
                if lhs_els.len() != rhs_els.len() {
                    // report an error
                    TupleSizeMismatch {
                        lhs: lhs.with(lhs_els.len()),
                        rhs: rhs.with(rhs_els.len()),
                    }
                    .accumulate(db);

                    // always fail if the size is mismatched
                    success = false;
                }

                // return if successful
                success
            }
            // primitives can be unified if they're the same type
            (Primitive(lhs), Primitive(rhs)) if lhs == rhs => true,
            // otherwise, we've encountered an error
            _ => {
                // report diagnostic
                let lhs = self.apply(&lhs);
                let rhs = self.apply(&rhs);

                TypeMismatch {
                    lhs: lhs.with(lhs.to_naive()),
                    rhs: rhs.with(rhs.to_naive()),
                }
                .accumulate(db);

                // unsuccessful unification
                false
            }
        }
    }

    /// Attempts to insert a type into the type inference map, returning if successful.
    pub fn insert(
        &mut self,
        db: &'db dyn Database,
        key: TypeKey<'db>,
        ty: WithAst<TableType<'db>>,
    ) -> bool {
        // ignore the tautological case
        if TableType::Key(key.clone()) == ty.inner {
            return true;
        }

        // test if key occurs in type, meaning recursive type
        if ty.occurs(&key) {
            SelfReferencingType { ast: ty.ast }.accumulate(db);
            false
        } else {
            self.map.insert(key, ty);
            true
        }
    }

    /// Unifies another type table with this one.
    pub fn merge(mut self, db: &'db dyn Database, other: Self) -> Self {
        // unify each entry in the other inference map with ours
        for (key, ty) in other.map {
            match self.map.get(&key) {
                // unify an existing type with their type
                Some(ours) => {
                    // clone ours to mutably borrow self for unify()
                    let ours = ours.to_owned();
                    self.unify(db, &ours, &ty);
                }
                // no type conflict possible, so just apply and insert
                None => {
                    // drop entry to mutably borrow self for apply()
                    let ty = self.apply(&ty);
                    self.insert(db, key, ty);
                }
            }
        }

        // return modified self
        self
    }

    /// Performs final checks on a type table, emitting any errors or warnings
    /// encountered along the way.
    pub fn finalize(&mut self) {}

    /// Returns if the type table is sound, i.e. there are no type errors.
    pub fn is_sound(&self) -> bool {
        self.sound
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Update)]
pub enum TableType<'db> {
    Tuple(Vec<WithAst<TableType<'db>>>),
    Primitive(PrimitiveType),
    Key(TypeKey<'db>),
    Unknown,
}

impl<'db> From<TypeKey<'db>> for TableType<'db> {
    fn from(key: TypeKey<'db>) -> Self {
        TableType::Key(key)
    }
}

impl From<PrimitiveType> for TableType<'_> {
    fn from(prim: PrimitiveType) -> Self {
        TableType::Primitive(prim)
    }
}

impl From<Pattern> for TableType<'_> {
    fn from(pat: Pattern) -> Self {
        use Pattern::*;
        match pat {
            Variable(name) => TypeKey::Variable(name).into(),
            Value(value) => PrimitiveType::from(value.ty()).into(),
            Tuple(els) => TableType::Tuple(
                els.iter()
                    .map(|el| el.with(el.as_ref().clone().into()))
                    .collect(),
            ),
        }
    }
}

impl<'db> TableType<'db> {
    /// Tests if a key occurs in this type.
    pub fn occurs(&self, key: &TypeKey<'db>) -> bool {
        use TableType::*;
        match self {
            Tuple(els) => els.iter().any(|el| el.occurs(key)),
            Primitive(_) => false,
            Key(other) => other == key,
            Unknown => false,
        }
    }

    /// Converts this table type into a [NaiveType], assuming keys are unknown.
    pub fn to_naive(&self) -> NaiveType {
        use TableType::*;
        match self {
            Tuple(els) => NaiveType::Tuple(els.iter().map(|el| el.to_naive()).collect()),
            Primitive(prim) => NaiveType::Primitive(*prim),
            Key(_) | Unknown => NaiveType::Unknown,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Update)]
pub enum TypeKey<'db> {
    Variable(String),
    Relation(String),
    Expr(Expr<'db>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NaiveType {
    Tuple(Vec<NaiveType>),
    Primitive(PrimitiveType),
    Unknown,
}

impl Display for NaiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use NaiveType::*;
        match self {
            Tuple(els) => {
                let mut first = true;
                write!(f, "(")?;
                for el in els.iter() {
                    if !first {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", el)?;
                    first = false;
                }

                write!(f, ")")
            }
            Primitive(prim) => prim.fmt(f),
            Unknown => write!(f, "<unknown>"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeMismatch {
    pub lhs: WithAst<NaiveType>,
    pub rhs: WithAst<NaiveType>,
}

impl BasicDiagnostic for TypeMismatch {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.rhs.ast..self.rhs.ast
    }

    fn message(&self) -> String {
        format!("conflicting types: {} and {}", self.lhs, self.rhs)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![
            self.lhs.with(format!("this has type {}", self.lhs)),
            self.rhs.with(format!("this has type {}", self.rhs)),
        ]
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SelfReferencingType {
    pub ast: AstNode,
}

impl BasicDiagnostic for SelfReferencingType {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.ast..self.ast
    }

    fn message(&self) -> String {
        "Type is self-referencing".into()
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TupleSizeMismatch {
    pub lhs: WithAst<usize>,
    pub rhs: WithAst<usize>,
}

impl BasicDiagnostic for TupleSizeMismatch {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.rhs.ast..self.rhs.ast
    }

    fn message(&self) -> String {
        format!("tuple size mismatch: {} and {}", self.lhs, self.rhs)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn source(&self) -> Option<String> {
        Some("Type inference".to_string())
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![
            self.lhs.with(format!("this tuple has length {}", self.lhs)),
            self.rhs.with(format!("this tuple has length {}", self.rhs)),
        ]
    }

    fn is_fatal(&self) -> bool {
        true
    }
}
