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
    collections::{BTreeSet, HashMap, HashSet},
    fmt::Display,
    str::FromStr,
};

use salsa::Database;
use saturn_v_ir::{self as ir, BinaryOpCategory, CardinalityConstraintKind, ConstraintKind, Value};

use crate::{
    diagnostic::{AccumulateDiagnostic, BasicDiagnostic, DiagnosticKind, SimpleError},
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
    pub name: WithAst<String>,

    /// Whether this relation is a decision.
    pub is_decision: bool,

    /// The IO of this relation.
    pub io: ir::RelationIO,

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
    for item in file_item_kind_ast(db, file, ItemKind::Rule) {
        // parse the rule
        let rule = parse_rule(db, item);

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
    name: WithAst<String>,
) -> Option<RelationDefinition<'_>> {
    let rel = file_relations(db, file).get(name.as_ref()).copied();

    // emit a fatal error if this relation could not be found
    if rel.is_none() {
        RelationNotFound { name }.accumulate(db);
    }

    rel
}

/// Gets the full relation table of a file.
#[salsa::tracked]
pub fn file_relations(db: &dyn Database, file: File) -> HashMap<String, RelationDefinition<'_>> {
    // iterate over all relation items
    let mut relations: HashMap<String, RelationDefinition> = HashMap::new();
    for node in file_item_kind_ast(db, file, ItemKind::Definition) {
        let def = parse_relation_def(db, node);
        let name = def.name(db).clone().inner;
        use std::collections::hash_map::Entry;
        match relations.entry(name.clone()) {
            Entry::Occupied(entry) => {
                RelationDefinedAgain {
                    name,
                    original: entry.get().ast(db),
                    redefinition: def.ast(db),
                }
                .accumulate(db);
            }
            Entry::Vacant(entry) => {
                entry.insert(def);
            }
        }
    }

    // done!
    relations
}

/// Parses a relation from a relation definition AST node.
#[salsa::tracked]
pub fn parse_relation_def<'db>(db: &'db dyn Database, item: Item<'db>) -> RelationDefinition<'db> {
    // extract the item's AST
    let ast = item.ast(db);

    // get the name
    let relation = ast.expect_field(db, "relation");
    let name = relation.with(relation.contents(db).to_string());

    // relation attributes
    let is_decision = ast.get_field(db, "decision").is_some();

    // handle the relation IO
    let input = ast.get_field(db, "input");
    let output = ast.get_field(db, "output");
    let io = match (input, output) {
        (None, None) => ir::RelationIO::None,
        (Some(_), None) => ir::RelationIO::Input,
        (None, Some(_)) => ir::RelationIO::Output,
        // if the IO conflicts, report error and default to no IO
        (Some(input), Some(output)) => {
            ConflictingIO {
                name: name.inner.clone(),
                input,
                output,
            }
            .accumulate(db);

            ir::RelationIO::None
        }
    };

    // parse the type
    let ty = parse_abstract_type(db, ast.expect_field(db, "type"));

    // create the full decision
    RelationDefinition::new(db, ast, name, is_decision, io, ty)
}

/// Parses an [AbstractType] from an AST node.
#[salsa::tracked]
pub fn parse_abstract_type(db: &dyn Database, ast: AstNode) -> WithAst<AbstractType> {
    let ty = if let Some(named) = ast.get_field(db, "named") {
        let name = named.contents(db).to_string();
        match name.parse() {
            Ok(prim) => AbstractType::Primitive(prim),
            Err(_) => AbstractType::Named(name),
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
pub fn file_item_kind_ast<'db>(
    db: &'db dyn Database,
    file: File,
    kind: ItemKind,
) -> BTreeSet<Item<'db>> {
    file_items(db, file)
        .into_iter()
        .filter(|item| item.kind(db) == kind)
        .collect()
}

/// Gets the top-level items from a file in order of appearance.
#[salsa::tracked]
pub fn file_items<'db>(db: &'db dyn Database, file: File) -> Vec<Item<'db>> {
    // iterate all children
    let root = file.ast(db);
    let mut items = Vec::new();
    let mut docs = Vec::new();
    for child in root.children(db).iter() {
        // select item kind based on symbol
        use ItemKind::*;
        let kind = match child.symbol(db) {
            // accumulate top-level or doc comments
            "comment" => {
                docs.push(*child);
                continue;
            }
            // parse each main item kind
            "import" => Import,
            "definition" => Definition,
            "rule" => Rule,
            "constraint" => Constraint,
            "newline" => Comment,
            // TODO: accumulate a diagnostic?
            _ => continue,
        };

        // assemble the complete item
        let item = Item::new(db, std::mem::take(&mut docs), *child, kind);

        // push this item to the list
        items.push(item);
    }

    // all done :)
    items
}

#[salsa::tracked]
pub struct Item<'db> {
    /// The documentation comments before the item.
    ///
    /// For top-level comment items, contains the list of actual comments.
    #[return_ref]
    pub docs: Vec<AstNode>,

    /// The AST node of the item body.
    ///
    /// For consecutive top-level comments, this is the newline terminating them.
    pub ast: AstNode,

    /// The kind of this item.
    pub kind: ItemKind,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Import,
    Definition,
    Rule,
    Constraint,
    Comment,
}

/// Parses an abstract constraint from an AST.
#[salsa::tracked]
pub fn parse_constraint<'db>(db: &'db dyn Database, item: Item<'db>) -> AbstractConstraint<'db> {
    // extract the item's AST
    let ast = item.ast(db);

    // parse each capture into the head
    let head = ast
        .get_fields(db, "capture")
        .map(|node| node.with(node.contents(db).to_string()))
        .collect();

    // attempt to parse the soft constraint
    let soft =
        ast.get_field(db, "soft")
            .and_then(|ast| match ast.contents(db).to_string().parse() {
                Ok(weight) => Some(ast.with(weight)),
                Err(_) => {
                    SimpleError::new(ast, "failed to parse soft constraint weight").accumulate(db);
                    None
                }
            });

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
            .to_string()
            .parse()
            .unwrap();

        WithAst::new(cardinality, ConstraintKind::Cardinality { kind, threshold })
    };

    // parse the body
    let body = parse_rule_body(db, ast.expect_field(db, "body"));

    // initialize the constraint
    AbstractConstraint::new(db, head, soft, kind, body)
}

/// An abstract constraint (syntax representation).
#[salsa::tracked]
#[derive(Debug)]
pub struct AbstractConstraint<'db> {
    /// The constraint's head variables.
    #[return_ref]
    pub head: Vec<WithAst<String>>,

    /// The soft constraint cost, if any.
    pub soft: Option<WithAst<u32>>,

    /// The kind of constraint.
    pub kind: WithAst<ConstraintKind>,

    /// The rule body of this constraint.
    pub body: AbstractRuleBody<'db>,
}

/// Parses an abstract rule from an AST.
#[salsa::tracked]
pub fn parse_rule<'db>(db: &'db dyn Database, item: Item<'db>) -> AbstractRule<'db> {
    // extract the item's AST
    let ast = item.ast(db);

    // get the name of the relation
    let relation_node = ast.expect_field(db, "relation");
    let relation = relation_node.with(relation_node.contents(db).to_string());

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
#[derive(Debug)]
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
#[derive(Debug)]
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
        Pattern::Variable(variable.contents(db).to_string())
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
        Value::Symbol(sym.contents(db).to_string())
    } else {
        let int = ast.expect_field(db, "integer");
        match int.contents(db).to_string().parse() {
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
        ExprKind::Variable(var.contents(db).to_string())
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
        let head = WithAst::new(head, head.contents(db).to_string());
        let body = parse_expr(db, atom.expect_field(db, "body"));
        ExprKind::Atom { head, body }
    } else if let Some(parens) = ast.get_field(db, "parens") {
        return parse_expr(db, parens);
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
    match ast.contents(db).to_string().parse() {
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
    match ast.contents(db).to_string().parse() {
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RelationNotFound {
    pub name: WithAst<String>,
}

impl BasicDiagnostic for RelationNotFound {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.name.ast..self.name.ast
    }

    fn message(&self) -> String {
        format!("undefined relation {}", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RelationDefinedAgain {
    pub name: String,
    pub original: AstNode,
    pub redefinition: AstNode,
}

impl BasicDiagnostic for RelationDefinedAgain {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.redefinition..self.redefinition
    }

    fn message(&self) -> String {
        format!("relation {} defined again", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![self.original.with("originally defined here".to_string())]
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConflictingIO {
    pub name: String,
    pub input: AstNode,
    pub output: AstNode,
}

impl BasicDiagnostic for ConflictingIO {
    fn range(&self) -> std::ops::Range<AstNode> {
        self.input..self.output
    }

    fn message(&self) -> String {
        format!("relation {} cannot be both input and output", self.name)
    }

    fn kind(&self) -> DiagnosticKind {
        DiagnosticKind::Error
    }

    fn is_fatal(&self) -> bool {
        true
    }

    fn notes(&self) -> Vec<WithAst<String>> {
        vec![]
    }
}
