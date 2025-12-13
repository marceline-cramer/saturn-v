(comment) @comment.line
(integer) @constant.numeric
(variable) @variable
(value (symbol) @constant)
(import (symbol) @module)
(type (symbol)) @type
(type_alias name: _ @type)

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
  "type"
  "decision"
  "define"
  "import"
  "input"
  "output"
  "soft"
] @keyword

(constraint_kind) @keyword.control

; doc comments
((comment)+ @comment.docs . (definition))
((comment)+ @comment.docs . (rule))
((comment)+ @comment.docs . (constraint))
