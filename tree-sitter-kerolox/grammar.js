/**
 * @file Kerolox grammar for tree-sitter
 * @license AGPL-3.0-or-later
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const list = el => seq(el, repeat(seq(",", el)))
const list1 = el => seq(el, choice(",", repeat(seq(",", el))))
const paren_list = (el) => seq("(", list(el), ")");
const paren_list1 = (el) => seq("(", list1(el), ")");

/// Shorthand to write a binary expression with left precedence of the given priority.
const expr_prec = (expr, precedence, op) => prec.left(precedence,
  seq(field("lhs", expr), field("op", op), field("rhs", expr)))

module.exports = grammar({
  name: "kerolox",

  extras: $ => [$._whitespace, $.comment],
  conflicts: $ => [[$.expr, $.tuple]],

  rules: {
    file: $ => repeat(choice($.import, $.definition, $.rule, $.constraint)),

    _whitespace: _ => /[ \n\r\t]/,
    comment: _ => /;.*\n/,

    variable: _ => /[a-z][a-zA-Z0-9_]*/,
    symbol: _ => /[A-Z][a-zA-Z0-9]*/,
    _ident: $ => choice($.variable, $.symbol),

    integer: _ => choice("0", /-?[1-9][0-9]*/),

    import: $ => seq(
      "import",
      field("path", $.symbol),
      repeat(seq(".", field("path", $.symbol))),
      ".",
      choice($.symbol, paren_list1(field("item", $.symbol))),
    ),

    definition: $ => seq(
      "define",
      field("output", optional("output")),
      field("decision", optional("decision")),
      field("relation", $.symbol),
      field("type", $.type),
      "."
    ),

    type: $ => choice(
      field("named", $.symbol),
      paren_list1(field("tuple", $.type)),
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
      paren_list1(field("tuple", $.pattern)),
    ),

    rule_body: $ => list1(field("clause", $.expr)),

    constraint: $ => seq(
      "constrain",
      optional(seq("soft", "(", field("soft", $.integer), ")")),
      optional(paren_list(field("capture", $.variable))),
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
      seq('(', choice($.expr), ')')
    ),

    atom: $ => prec.right(2, seq(field("head", $.symbol), field("body", $.expr))),

    tuple: $ => paren_list1(field("el", $.expr)),

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
