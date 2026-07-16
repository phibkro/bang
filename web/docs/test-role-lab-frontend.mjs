import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { roleLabContent } from './role-lab-content.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const bang = resolve(repoRoot, process.env.BANG_BIN ?? '.lake/build/bin/bang')
const lab = roleLabContent.find((candidate) => candidate.key === 'frontend-language')
assert.ok(lab, 'frontend-language role-lab content exists')
const practice = lab.stages.find((stage) => stage.id === 'isolated-practice')
assert.ok(practice, 'isolated-practice stage exists')
assert.equal(
  roleLabContent.filter((candidate) => candidate.key === 'frontend-language').length,
  1,
  'frontend role-lab content is unique',
)

const workdir = mkdtempSync(join(tmpdir(), 'bang-role-lab-frontend-'))
const practicePath = join(workdir, practice.fixture.path)
let executed = 0

function run(command, { allowStderr = false } = {}) {
  const result = spawnSync('bash', ['-lc', command], {
    cwd: repoRoot,
    env: { ...process.env, bang, practice: practicePath },
    encoding: 'utf8',
  })
  assert.equal(
    result.status,
    0,
    `practice command failed: ${command}\nstdout:\n${result.stdout}\nstderr:\n${result.stderr}`,
  )
  if (!allowStderr) assert.equal(result.stderr, '', `practice command wrote unexpected stderr: ${command}`)
  executed += 1
  return result.stdout
}

function parseJson(output, command) {
  assert.doesNotThrow(() => JSON.parse(output), `${command} emits JSON`)
  return JSON.parse(output)
}

try {
  writeFileSync(practicePath, practice.fixture.source)
  assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)

  const outputs = []
  for (const [index, command] of practice.commands.entries()) {
    if (index === 11) assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)
    outputs.push(run(command, { allowStderr: index === 0 }))
    if (index === 11) {
      assert.equal(
        readFileSync(practicePath, 'utf8'),
        practice.fixture.source,
        'rewrite fmt diff mode leaves the fixture byte-identical',
      )
    }
  }
  assert.equal(executed, practice.commands.length, 'every displayed practice command executed')

  const canonical = outputs[1]
  assert.notEqual(canonical, practice.fixture.source, 'fixture starts intentionally noncanonical')

  const checkBefore = parseJson(outputs[2], practice.commands[2])
  const dumpBefore = parseJson(outputs[3], practice.commands[3])
  const symbols = parseJson(outputs[4], practice.commands[4])
  const type = parseJson(outputs[5], practice.commands[5])
  const effects = parseJson(outputs[6], practice.commands[6])
  const definition = parseJson(outputs[7], practice.commands[7])
  const refs = parseJson(outputs[8], practice.commands[8])
  const impactBefore = parseJson(outputs[9], practice.commands[9])
  const resultBefore = outputs[10].trimEnd()

  assert.deepEqual(checkBefore, { ok: true, diagnostics: [] })
  assert.deepEqual(dumpBefore.decls.map((decl) => decl.name), ['double', 'quad', 'main'])
  assert.deepEqual(dumpBefore.refs, [
    { from: 'quad', to: 'double' },
    { from: 'main', to: 'quad' },
  ])
  assert.deepEqual(symbols.symbols, dumpBefore.decls, 'symbols is the dump declaration projection')
  assert.deepEqual(type, { ok: true, type: dumpBefore.decls[0].type, row: dumpBefore.decls[0].row })
  assert.deepEqual(effects, { ok: true, row: dumpBefore.decls[0].row })
  assert.deepEqual(definition.symbol, dumpBefore.decls[0])
  assert.deepEqual(refs.refs.map((ref) => ref.name), ['quad'])
  assert.deepEqual(impactBefore.dependents.map((decl) => decl.name).sort(), ['main', 'quad'])
  assert.notEqual(resultBefore, '', 'the practice program produces an observable result')

  assert.match(outputs[11], /^-let rec double/m, 'rewrite fmt diff shows the original line')
  assert.match(outputs[11], /^\+let rec double/m, 'rewrite fmt diff shows the formatted line')
  assert.equal(
    readFileSync(practicePath, 'utf8'),
    canonical.trimEnd(),
    'write mode stores the dynamically computed formatter content without stdout framing',
  )
  assert.equal(outputs[13], '', 'displayed formatter-content comparison succeeds silently')

  const checkAfter = parseJson(outputs[14], practice.commands[14])
  const dumpAfter = parseJson(outputs[15], practice.commands[15])
  const impactAfter = parseJson(outputs[16], practice.commands[16])
  const resultAfter = outputs[17].trimEnd()
  assert.deepEqual(checkAfter, checkBefore)
  assert.deepEqual(dumpAfter, dumpBefore, 'formatting preserves parsed query facts')
  assert.deepEqual(impactAfter, impactBefore, 'formatting preserves impact')
  assert.equal(resultAfter, resultBefore, 'formatting preserves the observed result')

  const idempotent = run('"$bang" fmt "$practice"')
  assert.equal(idempotent, canonical, 'formatting is idempotent')
  assert.equal(readFileSync(practicePath, 'utf8'), canonical.trimEnd())

  console.log(
    `role-lab-frontend: PASS — ${executed}/${practice.commands.length + 1} required commands executed; ` +
      'fixture, projections, nonmutation, write, facts, impact, and result agree',
  )
} finally {
  rmSync(workdir, { recursive: true, force: true })
}
