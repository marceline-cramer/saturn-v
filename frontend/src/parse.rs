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
    collections::{HashMap, HashSet},
    fmt::Display,
    str::FromStr,
};

use salsa::Database;
use saturn_v_ir::{
    self as ir, BinaryOpCategory, CardinalityConstraintKind, ConstraintKind, ConstraintWeight,
    Value,
};

use crate::{
    diagnostic::{AccumulateDiagnostic, SimpleError},
    toplevel::{AstNode, File},
    types::{PrimitiveType, WithAst},
};

/// A definition of a relation.
// TODO: add commment above definition AST node for documentation
#[salsa::tracked]
#[derive(Debug)]
pub struct RelationDefinition<'db> {
    /// The AST node this relation corresponds to.
    pub ast: AstNode,

    /// The name of this relation.
    #[return_ref]
    pub name: String,

    /// Whether this relation is a decision.
    pub is_decision: bool,

    /// Whether this relation is a output.
    pub is_output: bool,

    /// This relation's abstract type (pure syntax).
    #[return_ref]
    pub ty: WithAst<AbstractType>,
}

/// A definition of a type alias.
#[salsa::tracked]
pub struct TypeAlias<'db> {
    /// The AST node this type alias corresponds to.
    pub ast: AstNode,

    /// The name of this type alias.
    pub name: String,

    /// The alias's abstract type (pure syntax).
    pub ty: WithAst<AbstractType>,
}

/// An abstract type definition of a type.
///
/// This just represents the literal, syntactic type representation, without
/// dereferencing any aliases or checking semantic validity.
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum AbstractType {
    Named(String),
    Primitive(PrimitiveType),
    Tuple(Vec<WithAst<AbstractType>>),
}

impl Display for AbstractType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbstractType::Named(name) => write!(f, "{name}"),
            AbstractType::Primitive(ty) => write!(f, "{ty}"),
            AbstractType::Tuple(els) => {
                let els = els
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({els})")
            }
        }
    }
}

/// Gets the full rule table of a file.
#[salsa::tracked]
pub fn file_rules(db: &dyn Database, file: File) -> HashMap<String, HashSet<AbstractRule<'_>>> {
    // iterate over all rule items
    let mut rules: HashMap<_, HashSet<_>> = HashMap::new();
    for node in file_item_kind_ast(db, file, ItemKind::Rule) {
        // parse the rule
        let rule = parse_rule(db, node);

        // add it into the set corresponding to each relation name
        rules
            .entry(rule.relation(db).clone().inner)
            .or_default()
            .insert(rule);
    }

    // done!
    rules
}

/// Parses all constraints in a file.
pub fn file_constraints(db: &dyn Database, file: File) -> HashSet<AbstractConstraint<'_>> {
    file_item_kind_ast(db, file, ItemKind::Constraint)
        .into_iter()
        .map(|item| parse_constraint(db, item))
        .collect()
}

/// Looks up a relation definition in a file by name.
#[salsa::tracked]
pub fn file_relation(
    db: &dyn Database,
    file: File,
    name: String,
) -> Option<RelationDefinition<'_>> {
    file_relations(db, file).get(&name).copied()
}

/// Gets the full relation table of a file.
#[salsa::tracked]
pub fn file_relations(db: &dyn Database, file: File) -> HashMap<String, RelationDefinition<'_>> {
    // iterate over all relation items
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
    // get the name
    let relation = node.expect_field(db, "relation");
    let name = relation.contents(db).clone().unwrap();

    // relation attributes
    let is_decision = node.get_field(db, "decision").is_some();
    let is_output = node.get_field(db, "output").is_some();

    // parse the type
    let ty = parse_abstract_type(db, node.expect_field(db, "type"));

    // create the full decision
    RelationDefinition::new(db, node, name, is_decision, is_output, ty)
}

/// Parses an [AbstractType] from an AST node.
#[salsa::tracked]
pub fn parse_abstract_type(db: &dyn Database, ast: AstNode) -> WithAst<AbstractType> {
    let ty = if let Some(named) = ast.get_field(db, "named") {
        let name = named.contents(db).as_ref().unwrap();
        match name.parse() {
            Ok(prim) => AbstractType::Primitive(prim),
            Err(_) => AbstractType::Named(name.to_string()),
        }
    } else {
        AbstractType::Tuple(
            ast.get_fields(db, "tuple")
                .map(|child| parse_abstract_type(db, child))
                .collect(),
        )
    };

    WithAst::new(ast, ty)
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
    // iterate all children
    let root = file.ast(db);
    let mut items: HashMap<_, HashSet<_>> = HashMap::default();
    for child in root.children(db).iter() {
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

/// Parses an abstract constraint from an AST.
#[salsa::tracked]
pub fn parse_constraint(db: &dyn Database, ast: AstNode) -> AbstractConstraint<'_> {
    // parse each capture into the head
    let head = ast
        .get_fields(db, "capture")
        .map(|node| WithAst::new(ast, node.contents(db).to_owned().unwrap()))
        .collect();

    // match the constraint kind
    let kind = {
        let cardinality = ast.expect_field(db, "kind").expect_field(db, "cardinality");

        let kind = match cardinality.expect_field(db, "kind").symbol(db) {
            "only" => CardinalityConstraintKind::Only,
            "at_most" => CardinalityConstraintKind::AtMost,
            "at_least" => CardinalityConstraintKind::AtLeast,
            other => panic!("unexpected cardinality kind node {other:?}"),
        };

        let threshold = cardinality
            .expect_field(db, "threshold")
            .contents(db)
            .as_ref()
            .unwrap()
            .parse()
            .unwrap();

        WithAst::new(cardinality, ConstraintKind::Cardinality { kind, threshold })
    };

    // parse the body
    let body = parse_rule_body(db, ast.expect_field(db, "body"));

    // initialize the constraint
    AbstractConstraint::new(db, head, kind, body)
}

/// An abstract constraint (syntax representation).
#[salsa::tracked]
pub struct AbstractConstraint<'db> {
    /// The constraint's head variables.
    pub head: Vec<WithAst<String>>,

    /// The kind of constraint.
    pub kind: WithAst<ConstraintKind>,

    /// The rule body of this constraint.
    pub body: AbstractRuleBody<'db>,
}

/// Parses an abstract rule from an AST.
#[salsa::tracked]
pub fn parse_rule(db: &dyn Database, ast: AstNode) -> AbstractRule<'_> {
    // get the name of the relation
    let relation_node = ast.expect_field(db, "relation");
    let relation = WithAst::new(ast, relation_node.contents(db).clone().unwrap());

    // parse the head
    let head = parse_pattern(db, ast.expect_field(db, "head"));

    // parse each rule body
    let bodies = ast
        .get_fields(db, "body")
        .map(|body| parse_rule_body(db, body))
        .collect();

    // init the full rule
    AbstractRule::new(db, relation, head, bodies)
}

/// An abstract rule, aka a syntactical representation of one.
#[salsa::tracked]
pub struct AbstractRule<'db> {
    /// The name of the relation this rule is for.
    pub relation: WithAst<String>,

    /// The pattern defining this rule's head.
    #[return_ref]
    pub head: WithAst<Pattern>,

    /// The set of rule bodies in this rule.
    #[return_ref]
    pub bodies: Vec<AbstractRuleBody<'db>>,
}

/// Parses an [AbstractRuleBody] from an AST.
#[salsa::tracked]
pub fn parse_rule_body(db: &dyn Database, ast: AstNode) -> AbstractRuleBody<'_> {
    // simply iterate over each clause in the AST and parse each one
    let clauses = ast
        .get_fields(db, "clause")
        .map(|clause| parse_expr(db, clause))
        .collect();

    AbstractRuleBody::new(db, ast, clauses)
}

#[salsa::tracked]
pub struct AbstractRuleBody<'db> {
    /// The AST node this rule body corresponds to.
    pub ast: AstNode,

    /// Each clause in the body is an expression.
    #[return_ref]
    pub clauses: Vec<Expr<'db>>,
}

/// Parses a pattern from an AST.
#[salsa::tracked]
pub fn parse_pattern(db: &dyn Database, ast: AstNode) -> WithAst<Pattern> {
    let inner = if let Some(val) = ast.get_field(db, "value") {
        Pattern::Value(parse_value(db, val))
    } else if let Some(variable) = ast.get_field(db, "variable") {
        Pattern::Variable(variable.contents(db).clone().unwrap())
    } else {
        Pattern::Tuple(
            ast.get_fields(db, "tuple")
                .map(|el| parse_pattern(db, el))
                .collect(),
        )
    };

    WithAst::new(ast, inner)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Pattern {
    Variable(String),
    Value(Value),
    Tuple(Vec<WithAst<Pattern>>),
}

/// Parses a value from an AST.
#[salsa::tracked]
pub fn parse_value(db: &dyn Database, ast: AstNode) -> Value {
    if ast.get_field(db, "true").is_some() {
        Value::Boolean(true)
    } else if ast.get_field(db, "false").is_some() {
        Value::Boolean(false)
    } else if let Some(sym) = ast.get_field(db, "symbol") {
        Value::Symbol(sym.contents(db).clone().unwrap())
    } else {
        let int = ast.expect_field(db, "integer");
        match int.contents(db).as_ref().unwrap().parse() {
            Ok(val) => Value::Integer(val),
            Err(_) => {
                SimpleError::new(int, "failed to parse integer literal").accumulate(db);
                Value::Integer(0)
            }
        }
    }
}

#[salsa::tracked]
pub fn parse_expr(db: &dyn Database, ast: AstNode) -> Expr<'_> {
    // parse the kind depending on which field is selected
    let kind = if let Some(tuple) = ast.get_field(db, "tuple") {
        let els = tuple
            .get_fields(db, "el")
            .map(|el| parse_expr(db, el))
            .collect();

        ExprKind::Tuple(els)
    } else if let Some(val) = ast.get_field(db, "value") {
        ExprKind::Value(parse_value(db, val))
    } else if let Some(var) = ast.get_field(db, "variable") {
        ExprKind::Variable(var.contents(db).to_owned().unwrap())
    } else if let Some(binary) = ast.get_field(db, "binary") {
        let op = parse_binary_op(db, binary.expect_field(db, "op"));
        let lhs = parse_expr(db, binary.expect_field(db, "lhs"));
        let rhs = parse_expr(db, binary.expect_field(db, "rhs"));
        ExprKind::BinaryOp { op, lhs, rhs }
    } else if let Some(unary) = ast.get_field(db, "unary") {
        let op = parse_unary_op(db, unary.expect_field(db, "op"));
        let term = parse_expr(db, unary.expect_field(db, "term"));
        ExprKind::UnaryOp { op, term }
    } else if let Some(atom) = ast.get_field(db, "atom") {
        let head = atom.expect_field(db, "head");
        let head = WithAst::new(head, head.contents(db).to_owned().unwrap());
        let body = parse_expr(db, atom.expect_field(db, "body"));
        ExprKind::Atom { head, body }
    } else {
        unreachable!("unrecognized expression node kind at {:?}", ast.symbol(db));
    };

    // create the expression
    Expr::new(db, ast, kind)
}

#[salsa::interned]
#[derive(Debug)]
pub struct Expr<'db> {
    pub ast: AstNode,
    pub kind: ExprKind<'db>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ExprKind<'db> {
    Tuple(Vec<Expr<'db>>),
    Value(Value),
    Variable(String),
    BinaryOp {
        op: WithAst<BinaryOpKind>,
        lhs: Expr<'db>,
        rhs: Expr<'db>,
    },
    UnaryOp {
        op: WithAst<UnaryOpKind>,
        term: Expr<'db>,
    },
    Atom {
        head: WithAst<String>,
        body: Expr<'db>,
    },
}

pub fn parse_binary_op(db: &dyn Database, ast: AstNode) -> WithAst<BinaryOpKind> {
    match ast.contents(db).as_ref().unwrap().parse() {
        Ok(op) => WithAst::new(ast, op),
        Err(_) => {
            SimpleError::new(ast, "failed to parse binary operator").accumulate(db);
            WithAst::new(ast, BinaryOpKind::Eq)
        }
    }
}

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash)]
pub enum BinaryOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Concat,
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl FromStr for BinaryOpKind {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use BinaryOpKind::*;
        Ok(match s {
            "+" => Add,
            "-" => Sub,
            "*" => Mul,
            "/" => Div,
            ".." => Concat,
            "&&" => And,
            "||" => Or,
            "=" => Eq,
            "!=" => Ne,
            "<" => Lt,
            "<=" => Le,
            ">=" => Gt,
            ">" => Ge,
            _ => return Err(()),
        })
    }
}

impl BinaryOpKind {
    pub fn category(&self) -> BinaryOpCategory {
        use BinaryOpCategory::*;
        use BinaryOpKind::*;
        match self {
            Add | Sub | Mul | Div => Arithmetic,
            Concat => String,
            And | Or => Logical,
            Eq | Ne | Lt | Le | Gt | Ge => Comparison,
        }
    }
}

pub fn parse_unary_op(db: &dyn Database, ast: AstNode) -> WithAst<UnaryOpKind> {
    match ast.contents(db).as_ref().unwrap().parse() {
        Ok(op) => WithAst::new(ast, op),
        Err(_) => {
            SimpleError::new(ast, "failed to parse unary operator").accumulate(db);
            WithAst::new(ast, UnaryOpKind::Negate)
        }
    }
}

#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOpKind {
    Not,
    Negate,
}

impl FromStr for UnaryOpKind {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use UnaryOpKind::*;
        Ok(match s {
            "!" => Not,
            "-" => Negate,
            _ => return Err(()),
        })
    }
}

impl From<UnaryOpKind> for ir::UnaryOpKind {
    fn from(op: UnaryOpKind) -> Self {
        use ir::UnaryOpKind::*;
        match op {
            UnaryOpKind::Not => Not,
            UnaryOpKind::Negate => Negate,
        }
    }
}
