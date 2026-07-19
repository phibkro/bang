#!/usr/bin/env node
// tool: role=gen couples=examples/json,examples/calc,examples/nqueens,examples/ndet-sim-kv-a,examples/ndet-sim-kv-b,web/docs/static/compiled-demos,tools/test-compiled-browser-demo.mjs runs-in=manual
// Rebuild the committed ◊5.75 browser-demo artifacts and their exact provenance manifest.
import { createHash } from 'node:crypto'
import { execFileSync } from 'node:child_process'
import {
  copyFileSync,
  existsSync,
  mkdtempSync,
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { basename, dirname, join, relative } from 'node:path'
import { fileURLToPath } from 'node:url'

const root = execFileSync('git', ['rev-parse', '--show-toplevel'], { encoding: 'utf8' }).trim()
const here = dirname(fileURLToPath(import.meta.url))
if (root !== dirname(here)) throw new Error('generator must live under the repository tools directory')
const bang = join(root, '.lake', 'build', 'bin', 'bang')
const outputDir = join(root, 'web', 'docs', 'static', 'compiled-demos')
const demos = [
  ['json', 'JSON parser', 'examples/json/main.bang', ['Json.bang', 'Parse.bang', 'Print.bang', 'main.bang']],
  ['calc', 'Calculator parser', 'examples/calc/main.bang', ['Ast.bang', 'Eval.bang', 'Lexer.bang', 'Parser.bang', 'Print.bang', 'main.bang']],
  ['nqueens', 'N-Queens (4 + 5 + 6)', 'examples/nqueens/main.bang', ['main.bang']],
  ['ndet-sim-kv-a', 'sim-KV · first realization', 'examples/ndet-sim-kv-a/main.bang', ['main.bang']],
  ['ndet-sim-kv-b', 'sim-KV · swapped realization', 'examples/ndet-sim-kv-b/main.bang', ['main.bang']],
]
const sourceInputs = demos.flatMap(([, , source, inputs]) => [
  ...inputs.map((name) => join(dirname(source), name)),
  join(dirname(source), 'expected.txt'),
])

function run(command, args, options = {}) {
  return execFileSync(command, args, { cwd: root, encoding: 'utf8', maxBuffer: 16 * 1024 * 1024, ...options })
}

function wasmTools(args, options = {}) {
  try {
    return run('wasm-tools', args, options)
  } catch (error) {
    if (error?.code !== 'ENOENT') throw error
    return run('nix', ['shell', 'nixpkgs#wasm-tools', '--command', 'wasm-tools', ...args], options)
  }
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex')
}

if (!existsSync(bang)) throw new Error('missing .lake/build/bin/bang; run `lake build bang` first')
const dirty = run('git', ['status', '--porcelain', '--', 'Bang', 'lakefile.toml', 'lean-toolchain', ...sourceInputs]).trim()
if (dirty) throw new Error(`refusing dirty compiler/example inputs:\n${dirty}`)

const commit = run('git', ['rev-parse', 'HEAD']).trim()
const bangVersion = run(bang, ['--version']).trim()
const wasmToolsVersion = wasmTools(['--version']).trim()
const compilerTree = run('git', ['rev-parse', 'HEAD:Bang']).trim()
const temporary = mkdtempSync(join(tmpdir(), 'bang-compiled-demos-'))
mkdirSync(outputDir, { recursive: true })

try {
  const entries = []
  for (const [id, title, source, inputs] of demos) {
    const wat = run(bang, ['emit', source])
    const watPath = join(temporary, `${id}.wat`)
    const wasmPath = join(temporary, `${id}.wasm`)
    writeFileSync(watPath, wat)
    wasmTools(['parse', watPath, '-o', wasmPath], { encoding: null })
    const destination = join(outputDir, `${id}.wasm`)
    copyFileSync(wasmPath, destination)

    const expectedPath = join(dirname(source), 'expected.txt')
    const expectedOutput = readFileSync(join(root, expectedPath), 'utf8')
    // N-Queens intentionally crosses the default 100k substitution-machine ceiling.
    // One explicit shared ceiling keeps the generator's live kernel comparison honest.
    const oracleOutput = run(bang, ['run', '--engine=oracle', '--fuel', '250000', source])
    if (oracleOutput !== expectedOutput) {
      throw new Error(`${id}: live oracle does not match ${expectedPath}`)
    }
    const sourceFiles = inputs.map((name) => join(root, dirname(source), name)).map((path) => ({
      path: relative(root, path),
      sha256: sha256(readFileSync(path)),
    }))
    entries.push({
      id,
      title,
      source,
      sourceUrl: `https://github.com/phibkro/bang/tree/${commit}/${dirname(source)}`,
      sourceFiles,
      artifact: basename(destination),
      artifactSha256: sha256(readFileSync(destination)),
      expectedOutput,
    })
  }

  const manifest = {
    schemaVersion: 1,
    packId: 'bang-compiled-browser-demo-v1',
    builtFrom: {
      repository: 'https://github.com/phibkro/bang',
      commit,
      compilerTree,
      bangVersion,
      wasmToolsVersion,
    },
    runtime: {
      format: 'WebAssembly 3.0 modules using WasmGC and exception handling',
      hostContract: 'wasi_snapshot_preview1.fd_write on stdout descriptor 1 only',
      refuses: [
        'arbitrary BANG source compilation',
        'ambient filesystem, network, clock, randomness, and process authority',
        'imports other than wasi_snapshot_preview1.fd_write',
        'claims of support beyond enrolled engines or universal compiler correctness',
      ],
    },
    demos: entries,
  }
  writeFileSync(join(outputDir, 'manifest.json'), `${JSON.stringify(manifest, null, 2)}\n`)
  console.log(`compiled-demo generator: wrote ${entries.length} artifacts from ${commit.slice(0, 12)}`)
} finally {
  rmSync(temporary, { recursive: true, force: true })
}
