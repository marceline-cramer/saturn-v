(comment) @comment.line
(integer) @constant.numeric
(variable) @variable
(value (symbol) @constant)
(import (symbol) @module)
(type (symbol)) @type

(rule relation: (symbol) @constructor)
(definition relation: (symbol) @function)
(atom head: (symbol) @function)

[ ":-" "," "." ] @punctuation.delimiter
[ "(" ")" ] @punctuation.bracket

(binary_expr op: _ @operator)
(unary_expr op: _ @operator)

(cardinality kind: _ @operator)

[
  "constrain"
  "decision"
  "define"
  "import"
  "input"
  "output"
  "soft"
] @keyword

(constraint_kind) @keyword.control
