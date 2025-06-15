# Saturn V

Saturn V is an implementation of a general-purpose decision engine (see [What's a decision engine?](https://marceline-cramer.github.io/saturn-v/blog/whats-a-decision-engine/)).

It is named after the [Saturn V](https://en.wikipedia.org/wiki/Saturn_V) rocket engine because it is my fifth iteration on a general-purpose decision engine design. The name can also be interpreted as an homage to Japan's [Fifth Generation Computer Systems](https://en.wikipedia.org/wiki/Fifth_Generation_Computer_Systems) project.

At the moment, Saturn V is incomplete, but its early code and documentation is available on this repository.

# Architecture

```
parse -> type-infer -> desugar -> lower -> check -> evaluate -> solve
```

- **parse**: Saturn V incrementally parses updates to Kerolox source files using [tree-sitter](https://tree-sitter.github.io/), then loads the resulting syntax trees into incremental [Salsa](https://salsa-rs.github.io/salsa/) data structures. This is the source of all the inputs to the incremental frontend.
- **type-infer**: Kerolox programs are type-inferred at a high level using explicit relation definitions and type constraint rules applied on the expression levels. This gives every variable and expression in a program a concrete type and reports error diagnostics when types are inconsistent or unknown.
- **desugar**: The typing information is used by Saturn V to desugar the Kerolox types and values into Saturn V's intermediate representation (IR). For example, tuple types are flattened into lists of primitive values. All Saturn V relations ultimately end up as flat relations with columns of only primitive types.
- **lower**: Although desugaring has transformed the logical representation of Kerolox of semantics into IR, the IR is still purely logical and does not instruct Saturn V how to operate on relations to meet those semantics. The program's IR is fed into [egglog](https://github.com/egraphs-good/egglog), a state-of-the-art [equality graph (e-graph)](https://en.wikipedia.org/wiki/E-graph) implementation, to extract an equivalent relational program that can be actually be executed. The relational program is represented as a forest of [bottom-up](https://en.wikipedia.org/wiki/Datalog) relational operations.
- **check**: Some undesirable or unexpected properties of programs such as infinite recursion or unused relations can be detected using [Z3](https://github.com/Z3Prover/z3)'s [fixed-point engine](https://microsoft.github.io/z3guide/docs/fixedpoints/intro). This can provide warning diagnostics to users as they write programs, but in the future, it may also be used to ensure the safety of untrusted Saturn V programs before running them. Z3's fixed-point features are designed to check program safety in procedural environments, but luckily, we're already in a Horn clause-based system! It's a match made in heaven.
- **evaluate**: Now that the IR describes concrete relational operations instead of pure logical relations, it is passed to a [Differential Dataflow](https://github.com/TimelyDataflow/differential-dataflow) engine that incrementally populates the contents of each relation. It also assembles a model of the logical relationships between each entry in the program's decision relations. These relationships are eventually gathered in the top-level constraint operations, which emit constraints on decision values in propositional logic.
- **solve**: The constraints, set of active decisions, and logical relations are passed to a decoupled solving engine, which uses a [SAT solver](https://en.wikipedia.org/wiki/SAT_solver) to select decisions which meet all of the constraints. Because the evaluation engine's output is incremental, the solving engine's SAT instance can be kept across updates and extended with minor changes to inputs, responding with low latency instead of solving the program from scratch.

The steps of the pipeline between "parse" and "check" can be considered the "frontend" of Saturn V, because they reason about Kerolox programs without evaluating them or making any decisions. The Saturn V "backend" is composed of the evaluation and solve steps, which run separately and can be asynchronously loaded with new, valid IR code. In other words, the Saturn V frontend is everything that runs in a language server or IDE, and the backend runs long-term on a dedicated server machine and is dynamically loaded with new code over time.
