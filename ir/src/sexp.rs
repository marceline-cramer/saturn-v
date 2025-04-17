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

use std::{str::FromStr, sync::Arc};

use chumsky::prelude::*;

#[cfg(feature = "fuzz")]
use arbitrary::Arbitrary;

use crate::*;

pub type Doc = RcDoc<'static, ()>;

pub trait Sexp: Sized {
    fn to_doc(&self) -> Doc;
    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>>;
}

impl Sexp for HashSet<i64> {
    fn to_doc(&self) -> Doc {
        let vars = Doc::intersperse(self.iter().map(|idx| idx.to_string()), Doc::line());
        doc_list(Doc::text("set-of").append(Doc::line().append(vars).nest(4).group()))
    }

    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>> {
        parse_list("set-of", Token::integer().repeated()).map(Self::from_iter)
    }
}

impl Sexp for Instruction {
    fn to_doc(&self) -> Doc {
        use Instruction::*;
        match self {
            Noop => doc_list(Doc::text("Noop")),
            Sink(vars, rest) => doc_indent(doc_pair("Sink", vars.to_doc()), rest.to_doc()),
            Filter(expr, rest) => doc_indent_two(Doc::text("Filter"), expr.to_doc(), rest.to_doc()),
            FromQuery(relation, terms) => doc_indent(
                doc_pair("FromQuery", Doc::text(relation.to_string())),
                QueryTerm::to_doc(terms.iter()),
            ),
            Let(var, expr, rest) => doc_indent_two(
                doc_pair("Let", Doc::text(var.to_string())),
                expr.to_doc(),
                rest.to_doc(),
            ),
            Merge(lhs, rhs) => doc_indent_two(Doc::text("Merge"), lhs.to_doc(), rhs.to_doc()),
            Join(lhs, rhs) => doc_indent_two(Doc::text("Join"), lhs.to_doc(), rhs.to_doc()),
        }
    }

    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>> {
        use Instruction::*;
        recursive(|instr| {
            // recurse helper
            let instr = instr.map(Box::new);

            // noop
            let noop = parse_tag("Noop").to(Noop);

            // sink
            let sink = parse_list("Sink", HashSet::parser().then(instr.clone()))
                .map(|(vars, rest)| Sink(vars, rest));

            // filter
            let filter = parse_list("Filter", Expr::parser().then(instr.clone()))
                .map(|(expr, rest)| Filter(expr, rest));

            // from query
            let from_query = parse_list("FromQuery", Token::integer().then(QueryTerm::parser()))
                .map(|(r, q)| FromQuery(r, q));

            // let
            let let_ = parse_list(
                "Let",
                Token::integer().then(Expr::parser()).then(instr.clone()),
            )
            .map(|((var, expr), rest)| Let(var, expr, rest));

            // merge
            let merge = parse_list("Merge", instr.clone().then(instr.clone()))
                .map(|(lhs, rhs)| Merge(lhs, rhs));

            // join
            let join = parse_list("Join", instr.clone().then(instr.clone()))
                .map(|(lhs, rhs)| Join(lhs, rhs));

            noop.or(sink)
                .or(filter)
                .or(from_query)
                .or(let_)
                .or(merge)
                .or(join)
        })
    }
}

impl Sexp for Expr {
    fn to_doc(&self) -> Doc {
        use Expr::*;
        match self {
            Variable(idx) => doc_list(doc_pair("Variable", Doc::text(idx.to_string()))),
            Value(val) => doc_list(doc_pair("Value", val.to_doc())),
            Load { relation, query } => doc_indent(
                doc_pair("Load", Doc::text(relation.to_string())),
                QueryTerm::to_doc(query.iter()),
            ),
            UnaryOp { op, term } => doc_indent(doc_pair("UnaryOp", op.to_doc()), term.to_doc()),
            BinaryOp { op, lhs, rhs } => doc_indent_two(
                doc_pair("BinaryOp", op.to_doc()),
                lhs.to_doc(),
                rhs.to_doc(),
            ),
        }
    }

    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>> {
        recursive(|expr| {
            // recurse helper
            let expr = expr.map(Arc::new);

            // variable
            // TODO typecast hack?
            let variable =
                parse_list("Variable", Token::integer()).map(|var| Expr::Variable(var as _));

            // value
            let value = parse_list("Value", Value::parser()).map(Expr::Value);

            // load
            let load = parse_list("Load", Token::integer().then(QueryTerm::parser())).map(
                |(relation, query)| Expr::Load {
                    relation: relation as _, // TODO hack?
                    query,
                },
            );

            // unary op
            let unary_op = parse_list("UnaryOp", UnaryOpKind::parser().then(expr.clone()))
                .map(|(op, term)| Expr::UnaryOp { op, term });

            // binary op
            let binary_op = parse_list(
                "BinaryOp",
                BinaryOpKind::parser().then(expr.clone()).then(expr),
            )
            .map(|((op, lhs), rhs)| Expr::BinaryOp { op, lhs, rhs });

            variable.or(value).or(load).or(unary_op).or(binary_op)
        })
    }
}

impl Sexp for BinaryOpKind {
    fn to_doc(&self) -> Doc {
        use BinaryOpKind::*;
        let kind = match self {
            Add => "Add",
            Mul => "Mul",
            Div => "Div",
            Concat => "Concat",
            And => "And",
            Or => "Or",
            Eq => "Eq",
            Lt => "Lt",
            Le => "Le",
        };

        doc_list(Doc::text(kind))
    }

    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>> {
        parse_tag_variant()
    }
}

impl Sexp for UnaryOpKind {
    fn to_doc(&self) -> Doc {
        use UnaryOpKind::*;
        let kind = match self {
            Not => "Not",
            Negate => "Negate",
        };

        doc_list(Doc::text(kind))
    }

    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>> {
        parse_tag_variant()
    }
}

impl QueryTerm {
    pub fn to_doc<'a>(mut terms: impl Iterator<Item = &'a Self>) -> Doc {
        use QueryTerm::*;
        let (kind, val) = match terms.next() {
            Some(Variable(idx)) => ("QueryVariable", Doc::text(idx.to_string())),
            Some(Value(val)) => ("QueryValue", val.to_doc()),
            None => return Doc::text("(QueryNil)"),
        };

        doc_list(
            Doc::text(kind)
                .append(Doc::space())
                .append(val)
                .append(Doc::line())
                .append(Self::to_doc(terms)),
        )
    }

    pub fn parser() -> impl Parser<Token, Vec<Self>, Error = Simple<Token>> {
        recursive(|query| {
            let value = parse_list("QueryValue", Value::parser().then(query.clone())).map(
                |(val, mut rest): (Value, Vec<Self>)| {
                    rest.push(QueryTerm::Value(val));
                    rest
                },
            );

            let variable =
                parse_list("QueryVariable", Token::integer().then(query)).map(|(var, mut rest)| {
                    rest.push(QueryTerm::Variable(var as _)); // TODO: cast?
                    rest
                });

            let nil = parse_tag("QueryNil").to(vec![]);

            value.or(variable).or(nil)
        })
        // we push new terms into the back, so reverse
        .map(|mut terms| {
            terms.reverse();
            terms
        })
    }
}

impl Sexp for Value {
    fn to_doc(&self) -> Doc {
        use Value::*;
        let (kind, val) = match self {
            Boolean(val) => ("Boolean", val.to_string()),
            Integer(val) => ("Integer", val.to_string()),
            Real(val) => ("Real", val.to_string()),
            Symbol(val) => ("Symbol", format!("{val:?}")),
            String(val) => ("String", format!("{val:?}")),
        };

        doc_inline_list([kind, &val])
    }

    fn parser() -> impl Parser<Token, Self, Error = Simple<Token>> {
        let boolean =
            parse_list("Boolean", Token::item()).try_map(|item, span| match item.as_str() {
                "True" => Ok(Value::Boolean(true)),
                "False" => Ok(Value::Boolean(false)),
                _ => Err(Simple::custom(span, "expected `True` or `False`")),
            });

        let integer = parse_list("Integer", Token::integer()).map(Value::Integer);

        boolean.or(integer)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum Token {
    LParen,
    RParen,
    Item(String),
    Integer(i64),
    Real(OrderedFloat<f64>),
}

impl Token {
    pub fn lexer() -> impl Parser<char, Vec<Self>, Error = Simple<char>> {
        // punctuation
        let lparen = just("(").to(Token::LParen);
        let rparen = just(")").to(Token::RParen);

        // integer
        let int = just('-')
            .or_not()
            .then(one_of("0123456789").repeated().at_least(1).at_most(9))
            .map(|(negate, numerals)| {
                let mut string = String::new();
                string.extend(negate);
                string.extend(numerals);
                Token::Integer(string.parse().unwrap())
            });

        // alphanumeric item
        let item = filter(|c: &char| c.is_ascii_alphabetic())
            .then(filter(|c: &char| c.is_ascii_alphanumeric() || *c == '_' || *c == '-').repeated())
            .map(|(first, rest)| {
                let mut str = String::new();
                str.push(first);
                str.extend(rest);
                Token::Item(str.into())
            });

        // any of the above options (padded with whitespace)
        lparen
            .or(rparen)
            .or(int)
            .or(item)
            .recover_with(skip_then_retry_until([]))
            .padded()
            .repeated()
            .then_ignore(end())
    }

    /// Short-hand to expect a specific item.
    pub fn expect_item(name: impl ToString) -> impl Parser<Token, Token, Error = Simple<Token>> {
        just(Token::Item(name.to_string()))
    }

    /// Short-hand to parse an integer.
    pub fn integer() -> impl Parser<Token, i64, Error = Simple<Token>> {
        select! {
            Token::Integer(val) => val,
        }
    }

    /// Short-hand to parse the contents of any item.
    pub fn item() -> impl Parser<Token, String, Error = Simple<Token>> {
        select! {
            Token::Item(val) => val.to_string(),
        }
    }
}

/// Creates a paren-surrounded list with two children with smart indentation.
pub fn doc_indent_two(head: Doc, item1: Doc, item2: Doc) -> Doc {
    doc_list(
        head.append(
            Doc::line()
                .append(item1)
                .append(Doc::line())
                .append(item2)
                .nest(2)
                .group(),
        ),
    )
}

/// Creates a paren-surrounded list with a single child with smart indentation.
pub fn doc_indent(head: Doc, item: Doc) -> Doc {
    doc_list(head.append(Doc::line().append(item).nest(2).group()))
}

/// Helper to create a document representing "<text> <kind>".
pub fn doc_pair(text: &str, kind: Doc) -> Doc {
    Doc::text(text.to_string())
        .append(Doc::space())
        .append(kind)
}

/// Creates a list of documents separated by spaces and surrounded by parentheses.
pub fn doc_inline_list<T: ToString>(items: impl IntoIterator<Item = T>) -> Doc {
    doc_list(Doc::intersperse(
        items.into_iter().map(|item| Doc::text(item.to_string())),
        Doc::space(),
    ))
}

/// Wraps a document in parentheses.
pub fn doc_list(inner: Doc) -> Doc {
    Doc::text("(").append(inner).append(")")
}

/// Parse a paren-delimited list annotated with a given tag.
pub fn parse_list<T>(
    tag: &'static str,
    items: impl Parser<Token, T, Error = Simple<Token>>,
) -> impl Parser<Token, T, Error = Simple<Token>> {
    Token::expect_item(tag)
        .ignore_then(items)
        .delimited_by(just(Token::LParen), just(Token::RParen))
}

/// Parse a unit-length tagged list.
pub fn parse_tag(tag: &'static str) -> impl Parser<Token, (), Error = Simple<Token>> {
    Token::expect_item(tag)
        .ignored()
        .delimited_by(just(Token::LParen), just(Token::RParen))
}

/// Parse the tag in a unit-length tagged list.
pub fn parse_tag_variant<T: FromStr>() -> impl Parser<Token, T, Error = Simple<Token>> {
    Token::item()
        .try_map(|item, span| match item.parse() {
            Ok(op) => Ok(op),
            Err(_) => Err(Simple::custom(span, "unrecognized variant")),
        })
        .delimited_by(just(Token::LParen), just(Token::RParen))
}
