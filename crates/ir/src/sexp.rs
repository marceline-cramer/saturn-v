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

use std::{fmt::Debug, str::FromStr};

use chumsky::{input::ValueInput, prelude::*};
use either::Either;

use crate::*;

impl Sexp for Program<String> {
    fn to_doc(&self) -> Doc {
        let relations = self.relations.values().map(|rel| rel.to_doc());
        let constraints = self.constraints.iter().map(|cons| cons.to_doc());
        Doc::intersperse(relations.chain(constraints), Doc::hardline())
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        Relation::<String>::parser()
            .map(Either::Left)
            .or(Constraint::<String>::parser().map(Either::Right))
            .repeated()
            .fold(Program::default(), |mut program, el| match el {
                Either::Left(rel) => {
                    program.insert_relation(rel);
                    program
                }

                Either::Right(cons) => {
                    program.constraints.insert(cons);
                    program
                }
            })
    }
}

impl Sexp for Relation<String> {
    fn to_doc(&self) -> Doc {
        let store = Doc::text(self.store.clone());
        let ty = self.ty.to_doc();
        let kind = self.kind.to_doc();
        let io = self.io.to_doc();

        let facts = self.facts.iter().map(Vec::as_slice).map(doc_fact);
        let rules = self.rules.iter().map(Sexp::to_doc);

        doc_indent_many(
            Doc::text("relation"),
            [store, ty, kind, io].into_iter().chain(facts).chain(rules),
        )
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        let base = set((
            parse_property("name", Token::item()),
            parse_property("stratum", Token::unsigned()),
            parse_property("ty", StructuredType::parser()),
            parse_property("kind", RelationKind::parser()),
            parse_property("io", RelationIO::parser()),
        ))
        .map(|(store, stratum, ty, kind, io)| Relation {
            store,
            stratum,
            ty,
            kind,
            io,
            facts: vec![],
            rules: vec![],
        });

        let fact = parse_fact().map(Either::Left);
        let rule = Rule::<String>::parser().map(Either::Right);

        let fields = fact.or(rule).repeated().fold(
            (Vec::new(), Vec::new()),
            |(mut facts, mut rules), field| {
                match field {
                    Either::Left(fact) => facts.push(fact),
                    Either::Right(rule) => rules.push(rule),
                };

                (facts, rules)
            },
        );

        let body = base.then(fields).map(|(mut base, (facts, rules))| {
            base.facts = facts;
            base.rules = rules;
            base
        });

        parse_list("relation", body)
    }
}

impl Sexp for Constraint<String> {
    fn to_doc(&self) -> Doc {
        todo!()
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        let body = set((
            parse_property("weight", ConstraintWeight::parser()),
            parse_property("kind", ConstraintKind::parser()),
            parse_property("head", Vec::<u32>::parser()),
            parse_property("body", RuleBody::parser()),
        ))
        .map(|(weight, kind, head, body)| Constraint {
            weight,
            kind,
            head,
            body,
        });

        parse_list("constraint", body)
    }
}

impl Sexp for Rule<String> {
    fn to_doc(&self) -> Doc {
        doc_pair(
            "rule",
            QueryTerm::to_doc(self.head.iter())
                .append(Doc::space())
                .append(self.body.to_doc()),
        )
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        let body = QueryTerm::parser()
            .then(RuleBody::parser())
            .map(|(head, body)| Rule { head, body });

        parse_list("rule", body)
    }
}

impl Sexp for RuleBody<String> {
    fn to_doc(&self) -> Doc {
        todo!()
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        let loaded = parse_list("vec-of", Token::item().repeated().collect());

        let body = set((
            parse_property("vars", Vec::<Type>::parser()),
            parse_property("loaded", loaded),
        ))
        .then(Instruction::parser())
        .map(|((vars, loaded), instructions)| RuleBody {
            vars,
            loaded,
            instructions,
        });

        parse_list("rule-body", body)
    }
}

impl Sexp for ConstraintKind {
    fn to_doc(&self) -> Doc {
        todo!()
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        parse_list(
            "Cardinality",
            CardinalityConstraintKind::parser()
                .then(Token::unsigned())
                .map(|(kind, threshold)| ConstraintKind::Cardinality { kind, threshold }),
        )
    }
}

impl Sexp for ConstraintWeight {
    fn to_doc(&self) -> Doc {
        todo!()
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        parse_list("Hard", empty())
            .to(ConstraintWeight::Hard)
            .or(parse_list(
                "Soft",
                Token::unsigned().to(ConstraintWeight::Hard),
            ))
    }
}

impl Sexp for StructuredType {
    fn to_doc(&self) -> Doc {
        match self {
            StructuredType::Primitive(ty) => ty.to_doc(),
            StructuredType::Tuple(els) => {
                doc_indent_many(Doc::text("Tuple"), els.iter().map(Sexp::to_doc))
            }
        }
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        recursive(|structured_ty| {
            let tuple = Token::expect_item("Tuple")
                .ignore_then(structured_ty.repeated().collect())
                .map(StructuredType::Tuple)
                .delimited_by(just(Token::LParen), just(Token::RParen));

            Type::parser().map(StructuredType::Primitive).or(tuple)
        })
    }
}

impl Sexp for Instruction {
    fn to_doc(&self) -> Doc {
        use Instruction::*;
        match self {
            Noop => doc_list(Doc::text("Noop")),
            Sink { vars, rest } => doc_indent(doc_pair("Sink", vars.to_doc()), rest.to_doc()),
            Filter { test, rest } => {
                doc_indent_two(Doc::text("Filter"), test.to_doc(), rest.to_doc())
            }
            FromQuery { relation, terms } => doc_indent(
                doc_pair("FromQuery", Doc::text(relation.to_string())),
                QueryTerm::to_doc(terms.iter()),
            ),
            Let { var, expr, rest } => doc_indent_two(
                doc_pair("Let", Doc::text(var.to_string())),
                expr.to_doc(),
                rest.to_doc(),
            ),
            Merge { lhs, rhs } => doc_indent_two(Doc::text("Merge"), lhs.to_doc(), rhs.to_doc()),
            Join { lhs, rhs } => doc_indent_two(Doc::text("Join"), lhs.to_doc(), rhs.to_doc()),
            Antijoin {
                relation,
                terms,
                rest,
            } => doc_indent_many(
                Doc::text("Antijoin"),
                [
                    Doc::text(relation.to_string()),
                    QueryTerm::to_doc(terms.iter()),
                    rest.to_doc(),
                ],
            ),
        }
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        use Instruction::*;
        recursive(|instr| {
            // recurse helper
            let instr = instr.map(Box::new);

            // noop
            let noop = parse_tag("Noop").to(Noop);

            // sink
            let sink = parse_list("Sink", BTreeSet::parser().then(instr.clone()))
                .map(|(vars, rest)| Sink { vars, rest });

            // filter
            let filter = parse_list("Filter", Expr::parser().then(instr.clone()))
                .map(|(test, rest)| Filter { test, rest });

            // from query
            let from_query = parse_list("FromQuery", Token::unsigned().then(QueryTerm::parser()))
                .map(|(relation, terms)| FromQuery { relation, terms });

            // let
            let let_ = parse_list(
                "Let",
                Token::unsigned().then(Expr::parser()).then(instr.clone()),
            )
            .map(|((var, expr), rest)| Let { var, expr, rest });

            // merge
            let merge = parse_list("Merge", instr.clone().then(instr.clone()))
                .map(|(lhs, rhs)| Merge { lhs, rhs });

            // join
            let join = parse_list("Join", instr.clone().then(instr.clone()))
                .map(|(lhs, rhs)| Join { lhs, rhs });

            // antijoin
            let antijoin = parse_list(
                "Antijoin",
                Token::unsigned()
                    .then(QueryTerm::parser())
                    .then(instr.clone()),
            )
            .map(|((relation, terms), rest)| Antijoin {
                relation,
                terms,
                rest,
            });

            // combine all options
            choice((noop, sink, filter, from_query, let_, merge, join, antijoin))
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

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        recursive(|expr| {
            // recurse helper
            let expr = expr.map(Arc::new);

            // variable
            let variable = parse_list("Variable", Token::unsigned()).map(Expr::Variable);

            // value
            let value = parse_list("Value", Value::parser()).map(Expr::Value);

            // load
            let load = parse_list("Load", Token::unsigned().then(QueryTerm::parser()))
                .map(|(relation, query)| Expr::Load { relation, query });

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

    pub fn parser<I: TokenInput>() -> impl SexpParser<I, Vec<Self>> {
        recursive(|query| {
            let value = parse_list("QueryValue", Value::parser().then(query.clone())).map(
                |(val, mut rest): (Value, Vec<Self>)| {
                    rest.push(QueryTerm::Value(val));
                    rest
                },
            );

            let variable = parse_list("QueryVariable", Token::unsigned().then(query)).map(
                |(var, mut rest)| {
                    rest.push(QueryTerm::Variable(var));
                    rest
                },
            );

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

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        let boolean =
            parse_list("Boolean", Token::item()).try_map(|item, span| match item.as_str() {
                "True" => Ok(Value::Boolean(true)),
                "False" => Ok(Value::Boolean(false)),
                _ => Err(Rich::custom(span, "expected `True` or `False`")),
            });

        let integer = parse_list("Integer", Token::integer()).map(Value::Integer);

        let symbol = parse_list(
            "Symbol",
            Token::item().delimited_by(just(Token::Quote), just(Token::Quote)),
        )
        .map(Value::Symbol);

        boolean.or(integer).or(symbol)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "fuzz", derive(Arbitrary))]
pub enum Token {
    LParen,
    RParen,
    Quote,
    Item(String),
    Keyword(String),
    Integer(i64),
    Real(OrderedFloat<f64>),
}

impl Token {
    pub fn lexer<'a>() -> impl Parser<'a, &'a str, Vec<Self>, extra::Full<Rich<'a, char>, (), ()>> {
        // punctuation
        let lparen = just("(").to(Token::LParen);
        let rparen = just(")").to(Token::RParen);
        let quote = just("\"").to(Token::Quote);

        // integer
        let int = just('-')
            .or_not()
            .then(text::int(10))
            .try_map(|(negate, numerals), span| {
                let mut string = String::new();
                string.extend(negate);
                string.push_str(numerals);

                string
                    .parse()
                    .map(Token::Integer)
                    .map_err(|_| Rich::custom(span, "failed to parse integer literal"))
            });

        // alphanumeric item
        let item = text::ident().map(ToString::to_string).map(Token::Item);

        // Lisp-style keyword
        let kw = just(":")
            .ignore_then(text::ident())
            .map(ToString::to_string)
            .map(Token::Keyword);

        // any of the above options (padded with whitespace)
        choice((lparen, rparen, quote, int, item, kw))
            .padded()
            .repeated()
            .collect()
            .then_ignore(end())
    }

    /// Short-hand to expect a specific item.
    pub fn expect_item<I: TokenInput>(name: impl ToString) -> impl SexpParser<I, Token> {
        just(Token::Item(name.to_string()))
    }

    /// Short-hand to expect a specific keyword.
    pub fn expect_kw<I: TokenInput>(name: impl ToString) -> impl SexpParser<I, Token> {
        just(Token::Keyword(name.to_string()))
    }

    /// Short-hand to parse an integer.
    pub fn integer<I: TokenInput>() -> impl SexpParser<I, i64> {
        select! {
            Token::Integer(val) => val,
        }
    }

    /// Short-hand to parse an unsigned integer.
    pub fn unsigned<I: TokenInput>() -> impl SexpParser<I, u32> {
        Self::integer().try_map(|i, span| {
            i.try_into()
                .map_err(|_| Rich::custom(span, "expected unsigned 32-bit integer"))
        })
    }

    /// Short-hand to parse the contents of any item.
    pub fn item<I: TokenInput>() -> impl SexpParser<I, String> {
        select! {
            Token::Item(val) => val.to_string(),
        }
    }
}

/// Creates a fact document.
pub fn doc_fact(fact: &[Value]) -> Doc {
    doc_indent_many(Doc::text("fact"), fact.iter().map(|fact| fact.to_doc()))
}

/// Parses a fact.
pub fn parse_fact<I: TokenInput>() -> impl SexpParser<I, Vec<Value>> {
    Token::expect_item("fact")
        .ignore_then(Value::parser().repeated().collect())
        .delimited_by(just(Token::LParen), just(Token::RParen))
}

/// Creates a paren-surrounded list with two children with smart indentation.
pub fn doc_indent_two(head: Doc, item1: Doc, item2: Doc) -> Doc {
    doc_indent_many(head, [item1, item2])
}

/// Creates a paren-surrounded list with a single child with smart indentation.
pub fn doc_indent(head: Doc, item: Doc) -> Doc {
    doc_indent_many(head, [item])
}

/// Creates a paren-surrounded list with any number of children and smart indentation.
pub fn doc_indent_many(head: Doc, children: impl IntoIterator<Item = Doc>) -> Doc {
    doc_list(
        head.append(
            Doc::line()
                .append(Doc::intersperse(children, Doc::line()))
                .nest(2)
                .group(),
        ),
    )
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

/// Creates a keyword-indicated document property.
pub fn doc_property(name: &'static str, value: impl Into<Doc>) -> Doc {
    Doc::text(format!(":{name}"))
        .append(Doc::space())
        .append(value.into())
}

/// Parse a keyword-indicated property with the given parser.
pub fn parse_property<I: TokenInput, T>(
    kw: &'static str,
    items: impl SexpParser<I, T>,
) -> impl SexpParser<I, T> {
    Token::expect_kw(kw).ignore_then(items)
}

/// Parse a paren-delimited list annotated with a given tag.
pub fn parse_list<I: TokenInput, T>(
    tag: &'static str,
    items: impl SexpParser<I, T>,
) -> impl SexpParser<I, T> {
    Token::expect_item(tag)
        .ignore_then(items)
        .delimited_by(just(Token::LParen), just(Token::RParen))
}

/// Parse a unit-length tagged list.
pub fn parse_tag<I: TokenInput>(tag: &'static str) -> impl SexpParser<I, ()> {
    Token::expect_item(tag)
        .ignored()
        .delimited_by(just(Token::LParen), just(Token::RParen))
}

pub trait SexpVariant: FromStr + Debug + Sized {}

impl SexpVariant for RelationIO {}
impl SexpVariant for RelationKind {}
impl SexpVariant for BinaryOpKind {}
impl SexpVariant for UnaryOpKind {}
impl SexpVariant for CardinalityConstraintKind {}
impl SexpVariant for Type {}

impl<T: SexpVariant> Sexp for T {
    fn to_doc(&self) -> Doc {
        doc_list(Doc::text(format!("{self:?}")))
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        Token::item()
            .try_map(|item, span| match item.parse() {
                Ok(op) => Ok(op),
                Err(_) => Err(Rich::custom(span, "unrecognized variant")),
            })
            .delimited_by(just(Token::LParen), just(Token::RParen))
    }
}

pub type Doc = RcDoc<'static, ()>;

pub trait Sexp: Sized {
    fn to_doc(&self) -> Doc;
    fn parser<I: TokenInput>() -> impl SexpParser<I, Self>;
}

impl<T: Ord + Sexp> Sexp for BTreeSet<T> {
    fn to_doc(&self) -> Doc {
        let vars = Doc::intersperse(self.iter().map(|idx| idx.to_doc()), Doc::line());
        doc_list(Doc::text("set-of").append(Doc::line().append(vars).nest(4).group()))
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        parse_list("set-of", T::parser().repeated().collect())
    }
}

impl<T: Sexp> Sexp for Vec<T> {
    fn to_doc(&self) -> Doc {
        let vars = Doc::intersperse(self.iter().map(|idx| idx.to_doc()), Doc::line());
        doc_list(Doc::text("vec-of").append(Doc::line().append(vars).nest(4).group()))
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        parse_list("vec-of", T::parser().repeated().collect())
    }
}

impl Sexp for u32 {
    fn to_doc(&self) -> Doc {
        Doc::text(self.to_string())
    }

    fn parser<I: TokenInput>() -> impl SexpParser<I, Self> {
        Token::unsigned()
    }
}

/// A utility trait alias for valid sexp parsers.
pub trait SexpParser<I: TokenInput, T>: Parser<'static, I, T, ParserExtra> + Clone {}

impl<I: TokenInput, T, P> SexpParser<I, T> for P where P: Parser<'static, I, T, ParserExtra> + Clone {}

/// The type of parser extras to use throughout.
type ParserExtra = extra::Full<Rich<'static, Token>, (), ()>;

/// A trait alias for [ValueInput] for tokens.
pub trait TokenInput: ValueInput<'static, Span = SimpleSpan, Token = Token> {}

impl<I> TokenInput for I where I: ValueInput<'static, Span = SimpleSpan, Token = Token> {}
