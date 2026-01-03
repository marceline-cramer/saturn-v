set windows-shell := ["powershell.exe", "-NoLogo", "-Command"]

target := env('TARGET', `rustc --print host-tuple`)
cargo := env('CARGO', 'cargo')

default_package_tool := if replace(target, 'windows', '') == target {
    'tar'
} else {
    'zip'
}

package_tool := env('PACKAGE_TOOL', default_package_tool)
package_tool_name := file_stem(package_tool)

package_ext := if package_tool_name == 'tar' {
    'tar.gz'
} else if package_tool_name == 'zip' {
    'zip'
} else {
    error('unknown packaging tool')
}

package_args := if package_tool_name == 'tar' {
    '-czf'
} else if package_tool_name == 'zip' {
    '-j'
} else {
    error('unknown packaging tool')
}

binary_ext := if replace(target, 'windows', '') == target {
    ''
} else {
    '.exe'
}

github_ref_name := env('GITHUB_REF_NAME', 'HEAD')
src := 'target/' + target + '/release/saturn-v' + binary_ext
package_name := 'saturn-v-' + github_ref_name + '-' + target

wasm crate target:
    RUSTFLAGS="-C opt-level=z -C codegen-units=1 -C panic=abort" wasm-pack build crates/{{crate}} --release --target {{target}}
    wasm-pack pack crates/{{crate}}
    mkdir -p pkg
    mv crates/{{crate}}/pkg/*.tgz pkg/{{crate}}-{{target}}.tgz

release-cli:
    env
    mkdir -p artifacts
    {{cargo}} build --locked --keep-going --release --target {{target}}
    {{package_tool}} {{package_args}} artifacts/{{package_name}}.{{package_ext}} {{src}}
    echo artifact=artifacts/{{package_name}}.{{package_ext}} >> {{env('GITHUB_OUTPUT')}}
    echo artifact_name={{package_name}} >> {{env('GITHUB_OUTPUT')}}
