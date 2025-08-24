/**
 * @file Kerolox grammar for tree-sitter
 * @license AGPL-3.0-or-later
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const list = el => seq(el, repeat(seq(",", el)))
const listComma = el => seq(el, choice(",", repeat1(seq(",", el))))
const parenList = (el) => seq("(", list(el), ")");
const parenListComma = (el) => seq("(", listComma(el), ")");

/// Shorthand to write a binary expression with left precedence of the given priority.
const expr_prec = (expr, precedence, op) => prec.left(precedence,
  seq(field("lhs", expr), field("op", op), field("rhs", expr)))

module.exports = grammar({
  name: "kerolox",

  extras: $ => [$._whitespace, $.comment],

  rules: {
    file: $ => repeat(choice(
      // explicitly parse newlines and comments separately
      // this helps determine which comments are doc comments
      $.newline, $.comment,
      // the actual items
      $.import, $.definition, $.rule, $.constraint
    )),

    comment: $ => seq(/;[ \t]*/, $.commentInner),
    commentInner: _ => token.immediate(/[^\n]*\n/),
    newline: _ => /[\n\r]/,
    _whitespace: _ => /[ \n\r\t]/,
    docs: _ => /(?:;.*\n)*/,

    variable: _ => /[a-z][a-zA-Z0-9_]*/,
    symbol: _ => /[A-Z][a-zA-Z0-9]*/,
    _ident: $ => choice($.variable, $.symbol),

    integer: _ => choice("0", /-?[1-9][0-9]*/),

    import: $ => seq(
      "import",
      field("path", $.symbol),
      repeat(seq(".", field("path", $.symbol))),
      ".",
      choice($.symbol, parenList(field("item", $.symbol))),
    ),

    definition: $ => seq(
      "define",
      field("input", optional("input")),
      field("output", optional("output")),
      field("decision", optional("decision")),
      field("relation", $.symbol),
      field("type", $.type),
      "."
    ),

    type: $ => choice(
      field("named", $.symbol),
      parenListComma(field("tuple", $.type)),
    ),

    rule: $ => seq(
      field("relation", $.symbol),
      field("head", $.pattern),
      repeat(seq(":-", field("body", $.rule_body))),
      "."
    ),

    pattern: $ => choice(
      field("value", $.value),
      field("variable", $.variable),
      parenListComma(field("tuple", $.pattern)),
    ),

    rule_body: $ => list(field("clause", $.expr)),

    constraint: $ => seq(
      "constrain",
      optional(seq("soft", "(", field("soft", $.integer), ")")),
      optional(parenList(field("capture", $.variable))),
      field("kind", $.constraint_kind),
      ":-",
      field("body", $.rule_body),
      "."
    ),

    constraint_kind: $ => choice(field("cardinality", $.cardinality)),

    cardinality: $ => seq(
      field("kind", choice($.only, $.at_most, $.at_least)),
      field("threshold", $.integer),
    ),

    only: _ => "=",
    at_most: _ => "<=",
    at_least: _ => ">=",

    expr: $ => choice(
      field("atom", $.atom),
      field("tuple", $.tuple),
      field("value", $.value),
      field("variable", $.variable),
      field("unary", $.unary_expr),
      field("binary", $.binary_expr),
      seq('(', field("parens", $.expr), ')'),
    ),

    atom: $ => prec.right(2, seq(field("head", $.symbol), field("body", $.expr))),

    tuple: $ => parenListComma(field("el", $.expr)),

    value: $ => choice(
      field("true", "True"),
      field("false", "False"),
      field("symbol", $.symbol),
      field("integer", $.integer),
    ),

    unary_expr: $ => prec.left(5, seq(
      field("op", $.unary_op),
      field("term", $.expr)
    )),

    unary_op: _ => choice("!", "-"),

    binary_expr: $ => choice(
      expr_prec($.expr, 4, choice("*", "/")),
      expr_prec($.expr, 3, choice("+", "-")),
      expr_prec($.expr, 2, ".."),
      expr_prec($.expr, 1, choice("=", "!=", ">=", "<=", "<", ">")),
      expr_prec($.expr, 0, choice("&&", "||")),
    ),
  }
});
