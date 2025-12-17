set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

crate := "client"
target := "bundler"

wasm crate target:
    wasm-pack build crates/{{crate}} --release --target {{target}} --out-name saturn-v-{{crate}}-{{target}}
    wasm-pack pack crates/{{crate}}
