# Changelog

## [0.2.0] - 2026-01-03

- Lowercases every `StructuredValue` tag and adds tuple/update helpers to align the client, protocol, and server APIs ([#31](https://github.com/marceline-cramer/saturn-v/pull/31)).
- Ships the first `saturn_v_py` package with asyncio-friendly program/input/output APIs and pytest coverage for server calls ([#40](https://github.com/marceline-cramer/saturn-v/pull/40)).
- Reworks lowering to use `IndexSet` relation tables and an updated `lower.egg` script for deterministic rewrites ([#42](https://github.com/marceline-cramer/saturn-v/pull/42)).
- Fixes the Kerolox tree-sitter grammar so newline-free semicolon comments no longer swallow doc comments ([#43](https://github.com/marceline-cramer/saturn-v/pull/43)).
- Publishes wasm-pack bundles for the client crate and adds packaging support to the repository ([#45](https://github.com/marceline-cramer/saturn-v/pull/45)).
- Computes negation strata, reports non-monotonic cycles, and prepares the evaluator for negation-as-failure programs ([#47](https://github.com/marceline-cramer/saturn-v/pull/47)).
- Embeds the Wasm language server in the Kerolox VS Code extension and bridges it to Node streams ([#50](https://github.com/marceline-cramer/saturn-v/pull/50)).
- Adds metadata APIs, SSE subscriptions, and wasm-bindgen shims to the Rust client library ([#53](https://github.com/marceline-cramer/saturn-v/pull/53)).
- Emits CLI version info via Clap ([#55](https://github.com/marceline-cramer/saturn-v/pull/55)).
- Introduces the `saturn-v-orbit` crate with baked trajectories, Leptos bindings, and simulation tools ([#62](https://github.com/marceline-cramer/saturn-v/pull/62)).
- Refreshes workspace dependencies to the latest compatible releases ([#73](https://github.com/marceline-cramer/saturn-v/pull/73)).
- Moves release automation into the `Justfile`, adds Zig/Cross targets, and wires Wasm/VScode workflows into release jobs ([#84](https://github.com/marceline-cramer/saturn-v/pull/84)).
- Optimizes the MaxSAT solver by switching from batsat to CaDiCaL, using linearSU instead of linearUS, and using DynamicPolynomialWatchdog instead of the generalized totalizer ([#86](https://github.com/marceline-cramer/saturn-v/pull/86)).
- Adds support for release artifacts using CaDiCaL ([#89](https://github.com/marceline-cramer/saturn-v/pull/89)).
