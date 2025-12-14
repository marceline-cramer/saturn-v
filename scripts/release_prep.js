#!/usr/bin/env node
const fs = require('fs');
const path = require('path');

if (process.argv.length !== 5) {
  console.error('Usage: node scripts/release_prep.js <pkg-node> <pkg-bundler> <out-dir>');
  process.exit(2);
}

const [pkgNodeDir, pkgBundlerDir, outDir] = process.argv.slice(2);

function findFirst(dir, re) {
  const files = fs.readdirSync(dir);
  for (const f of files) if (re.test(f)) return path.join(dir, f);
  return null;
}

// read Cargo.toml version (simple regex)
const cargo = fs.readFileSync('crates/client/Cargo.toml', 'utf8');
const m = cargo.match(/^version\s*=\s*"([^"]+)"/m);
if (!m) {
  console.error('Could not find version in crates/client/Cargo.toml');
  process.exit(2);
}
const version = m[1];

// read base package.json from node pkg
const basePkgPath = path.join(pkgNodeDir, 'package.json');
if (!fs.existsSync(basePkgPath)) {
  console.error('package.json not found in', pkgNodeDir);
  process.exit(2);
}
const basePkg = JSON.parse(fs.readFileSync(basePkgPath, 'utf8'));

// figure files
const wasmFile = findFirst(pkgNodeDir, /_bg\.wasm$/) || findFirst(pkgBundlerDir, /_bg\.wasm$/);
const nodeJs = findFirst(pkgNodeDir, /\.js$/);
const bundlerJs = findFirst(pkgBundlerDir, /\.js$/) || nodeJs;
const dts = findFirst(pkgBundlerDir, /\.d\.ts$/) || findFirst(pkgNodeDir, /\.d\.ts$/);

if (!wasmFile || !nodeJs || !bundlerJs) {
  console.error('Could not locate required artifacts:', { wasmFile, nodeJs, bundlerJs, dts });
  process.exit(2);
}

// prepare out dir
if (!fs.existsSync(outDir)) fs.mkdirSync(outDir, { recursive: true });

// basename for files
const baseName = path.basename(nodeJs, path.extname(nodeJs)).replace(/-/g, '_');
const wasmBase = path.basename(wasmFile);

// copy files
const nodeDest = path.join(outDir, `${baseName}.node.js`);
fs.copyFileSync(nodeJs, nodeDest);
const bundlerDest = path.join(outDir, `${baseName}.js`);
fs.copyFileSync(bundlerJs, bundlerDest);
const wasmDest = path.join(outDir, wasmBase);
fs.copyFileSync(wasmFile, wasmDest);

if (dts) {
  const dtsDest = path.join(outDir, 'index.d.ts');
  fs.copyFileSync(dts, dtsDest);
}

// create package.json for release package
const releasePkg = {
  name: basePkg.name || '@saturn-v/client',
  version: version,
  description: basePkg.description || 'Saturn V client (wasm)',
  main: `./${baseName}.node.js`,
  module: `./${baseName}.js`,
  types: dts ? './index.d.ts' : undefined,
  files: [
    `${baseName}.js`,
    `${baseName}.node.js`,
    wasmBase,
  ].concat(dts ? ['index.d.ts'] : []),
  exports: {
    '.': {
      node: `./${baseName}.node.js`,
      import: `./${baseName}.js`,
      default: `./${baseName}.js`
    }
  }
};

// write package.json
fs.writeFileSync(path.join(outDir, 'package.json'), JSON.stringify(releasePkg, null, 2));

console.log('Prepared release package in', outDir);
console.log('Files:', fs.readdirSync(outDir));
console.log('Version set to', version);
process.exit(0);
