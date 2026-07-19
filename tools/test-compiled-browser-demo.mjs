#!/usr/bin/env node
// tool: role=test couples=tools/test-compiled-browser-demo.sh,tools/build-compiled-browser-demo.mjs,web/docs/static/compiled-demos,examples/json,examples/calc,examples/nqueens,examples/ndet-sim-kv-a,examples/ndet-sim-kv-b runs-in=manual
// Check committed demo provenance, source/oracle/artifact agreement, and the narrow host refusals.
import { createHash } from 'node:crypto'
import { execFileSync } from 'node:child_process'
import { readFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { createStdoutWrite, runBangModule, validateDemoImports } from '../web/docs/static/compiled-demos/runtime.js'

const root = dirname(dirname(fileURLToPath(import.meta.url)))
const packDir = join(root, 'web', 'docs', 'static', 'compiled-demos')
const manifest = JSON.parse(readFileSync(join(packDir, 'manifest.json'), 'utf8'))
const bang = process.env.BANG_BIN || join(root, '.lake', 'build', 'bin', 'bang')
let passed = 0

function assert(condition, message) {
  if (!condition) throw new Error(message)
  passed += 1
}

function sha256(bytes) {
  return createHash('sha256').update(bytes).digest('hex')
}

assert(manifest.schemaVersion === 1, 'unexpected manifest schema')
assert(manifest.packId === 'bang-compiled-browser-demo-v1', 'unexpected pack identity')
assert(/^[0-9a-f]{40}$/.test(manifest.builtFrom.commit), 'invalid producer commit')
assert(manifest.demos.length === 5, 'the fixed demo corpus must contain five entries')
const currentCompilerTree = execFileSync('git', ['rev-parse', 'HEAD:Bang'], { cwd: root, encoding: 'utf8' }).trim()
assert(currentCompilerTree === manifest.builtFrom.compilerTree, 'compiler tree changed; regenerate the demo pack')
const producerCompilerTree = execFileSync(
  'git', ['rev-parse', `${manifest.builtFrom.commit}:Bang`], { cwd: root, encoding: 'utf8' },
).trim()
assert(producerCompilerTree === manifest.builtFrom.compilerTree, 'producer commit/compiler tree mismatch')
const currentBangVersion = execFileSync(bang, ['--version'], { cwd: root, encoding: 'utf8' }).trim()
assert(currentBangVersion === manifest.builtFrom.bangVersion, 'compiler version changed; regenerate the demo pack')

let firstArtifact
let firstObserved
for (const demo of manifest.demos) {
  const bytes = readFileSync(join(packDir, demo.artifact))
  firstArtifact ??= bytes
  assert(sha256(bytes) === demo.artifactSha256, `${demo.id}: artifact hash mismatch`)
  for (const sourceFile of demo.sourceFiles) {
    assert(
      sha256(readFileSync(join(root, sourceFile.path))) === sourceFile.sha256,
      `${demo.id}: source hash mismatch for ${sourceFile.path}`,
    )
  }
  const expected = readFileSync(join(root, dirname(demo.source), 'expected.txt'), 'utf8')
  assert(demo.expectedOutput === expected, `${demo.id}: manifest/expected.txt mismatch`)
  const oracle = execFileSync(bang, ['run', '--engine=oracle', '--fuel', '250000', demo.source], {
    cwd: root,
    encoding: 'utf8',
    maxBuffer: 16 * 1024 * 1024,
  })
  assert(oracle === expected, `${demo.id}: live kernel oracle mismatch`)
  const observed = await runBangModule(bytes)
  firstObserved ??= observed
  assert(observed === expected, `${demo.id}: committed Wasm output mismatch`)
  console.log(`✓ ${demo.id}: artifact = kernel oracle = ${JSON.stringify(expected)}`)
}

const tamperedArtifact = Buffer.from(firstArtifact)
tamperedArtifact[tamperedArtifact.length - 1] ^= 1
assert(
  sha256(tamperedArtifact) !== manifest.demos[0].artifactSha256,
  'in-memory artifact tamper pole must change the pinned digest',
)
assert(
  firstObserved !== `${manifest.demos[0].expectedOutput}tampered`,
  'in-memory expected-output tamper pole must remain distinguishable',
)

assert.throws = (callback, pattern, message) => {
  try {
    callback()
  } catch (error) {
    assert(pattern.test(String(error)), message)
    return
  }
  throw new Error(message)
}
assert.throws(
  () => validateDemoImports([{ module: 'host', name: 'readFile', kind: 'function' }]),
  /must import only/,
  'unexpected host imports must be refused',
)
assert.throws(
  () => createStdoutWrite(() => null, [])(2, 0, 0, 0),
  /stdout \(1\) only/,
  'non-stdout descriptors must be refused',
)

console.log(`compiled-browser-demo: PASS — ${passed} assertions across ${manifest.demos.length} demos`)
