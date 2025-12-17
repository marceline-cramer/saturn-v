set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

wasm crate target:
    RUSTFLAGS="-C opt-level=z -C codegen-units=1 -C panic=abort" wasm-pack build crates/{{crate}} --release --target {{target}}
    wasm-pack pack crates/{{crate}}
    mkdir -p pkg
    mv crates/{{crate}}/pkg/*.tgz pkg/{{crate}}-{{target}}.tgz
