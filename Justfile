set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

wasm crate target:
    wasm-pack build crates/{{crate}} --release --target {{target}}
    wasm-pack pack crates/{{crate}}
    mkdir -p pkg
    mv crates/{{crate}}/pkg/*.tgz pkg/{{crate}}-{{target}}.tgz
