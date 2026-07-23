import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join, resolve } from 'node:path'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { roleLabContent } from './role-lab-content.mjs'
import { acquireRoleLabLane } from './role-lab-lane.mjs'
import { compileSite, resolveRoleLabContent } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const frontend = roleLabContent.find((candidate) => candidate.key === 'frontend-language')
const site = compileSite({ manifestPath: join(siteDir, 'page-manifest.json'), repoRoot })
const lab = resolveRoleLabContent(site, roleLabContent).find(
  (candidate) => candidate.routeChoice.id === 'coding-agent',
)
assert.ok(lab, 'coding-agent role-lab content exists')
assert.equal(roleLabContent.filter((candidate) => candidate.key === 'coding-agent').length, 1)
assert.deepEqual(lab.stages.map((stage) => stage.id), [
  'retrieve-predict',
  'trace-seam',
  'isolated-practice',
  'inspect-select',
])

const practice = lab.stages[2]
assert.strictEqual(practice.fixture, frontend.stages[2].fixture, 'frontend fixture is reused by identity')
assert.equal(practice.commands[0], 'nix develop --command lake build bang', 'lane binary is built first')
assert.deepEqual(practice.commands.slice(-4), [
  'rm "$practice"',
  'test -z "$(git status --porcelain)"',
  'nix develop --command just fitness',
  'nix develop --command just verify',
])
assert.equal(
  practice.commands.slice(1, -4).length,
  frontend.stages[2].commands.length - 1,
  'the complete frontend observation/edit sequence is reused',
)
for (const command of practice.commands.slice(1, -4)) {
  assert.ok(command.includes('./.lake/build/bin/bang') || command.startsWith('test '), `lane binary provenance: ${command}`)
}

const issueSelection = lab.stages[3].issueSelection
assert.match(issueSelection, /gh issue list/)
assert.match(issueSelection, /gh issue view/)
assert.doesNotMatch(issueSelection, /gh issue (?:create|comment|edit|close|reopen|delete|develop|pin|lock)/)

function result(command, args, { cwd = repoRoot, env = process.env } = {}) {
  return spawnSync(command, args, { cwd, env, encoding: 'utf8' })
}

function run(command, args, options = {}) {
  const completed = result(command, args, options)
  const output = `${completed.stdout ?? ''}${completed.stderr ?? ''}`
  assert.equal(completed.status, 0, `command failed: ${command} ${args.join(' ')}\ncwd: ${options.cwd ?? repoRoot}\n${output}`)
  return output
}

function validateEvidence(record) {
  const required = ['base', 'head', 'protectedCheckout', 'lane', 'files', 'commands', 'results', 'gates', 'uncertainty']
  assert.deepEqual(Object.keys(record).sort(), [...required].sort(), 'evidence fields are exact and complete')
  assert.equal(record.base, record.head, 'evidence is bound to one exact source commit')
  assert.notEqual(resolve(record.protectedCheckout), resolve(record.lane), 'protected checkout and lane differ')
  assert.deepEqual(record.files, ['main.bang'], 'only the disposable fixture changed')
  assert.equal(record.results.length, record.commands.length, 'every command has one observation')
  for (const [index, observation] of record.results.entries()) {
    assert.equal(observation.command, record.commands[index], 'observation order is command-bound')
    assert.equal(observation.observed, true, 'command result was observed')
    assert.equal(observation.status, 0, 'observed command passed')
  }
  for (const gate of ['narrow', 'full']) {
    assert.equal(record.gates[gate].command, lab[`${gate}Gate`], `${gate} gate is command-bound`)
    assert.equal(record.gates[gate].observed, true, `${gate} gate was observed`)
    assert.equal(record.gates[gate].status, 0, `${gate} gate passed`)
  }
  assert.equal(typeof record.uncertainty, 'string')
  assert.notEqual(record.uncertainty.trim(), '', 'uncertainty is explicit')
}

const parent = mkdtempSync(join(tmpdir(), 'bang-role-lab-coding-agent-'))
const base = run('git', ['rev-parse', 'HEAD']).trim()
const protectedStatusBefore = run('git', ['status', '--porcelain'])
const commandResults = []
let diffObserved = false
let factsObserved = false
let cleanObserved = false

try {
  const { lane } = acquireRoleLabLane({ repoRoot, parent, base, labKey: 'coding-agent', run })
  const practicePath = join(lane, practice.fixture.path)
  writeFileSync(practicePath, practice.fixture.source)
  assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '?? main.bang\n')

  const outputs = []
  for (const [index, command] of practice.commands.entries()) {
    if (index === 11) assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)
    if (command === lab.narrowGate || command === lab.fullGate) {
      commandResults.push({
        command,
        observed: false,
        status: null,
        result: 'repository gate is exercised only by the enclosing just verify',
      })
      continue
    }
    const completed = result('bash', ['-o', 'pipefail', '-lc', command], {
      cwd: lane,
      env: { ...process.env, lane, practice: practicePath },
    })
    const output = `${completed.stdout ?? ''}${completed.stderr ?? ''}`
    assert.equal(completed.status, 0, `practice command failed: ${command}\n${output}`)
    outputs.push(completed.stdout ?? '')
    commandResults.push({ command, observed: true, status: completed.status, result: output.trimEnd() })

    if (index === 11) {
      assert.equal(command, './.lake/build/bin/bang rewrite fmt "$practice"')
      assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source, 'diff mode is nonmutating')
      assert.match(outputs[index], /^-let rec double/m)
      assert.match(outputs[index], /^\+let rec double/m)
      diffObserved = true
    }
    if (index === 17) {
      const before = JSON.parse(outputs[3])
      const after = JSON.parse(outputs[15])
      assert.deepEqual(after, before, 'formatting preserves query dump facts')
      assert.deepEqual(JSON.parse(outputs[16]), JSON.parse(outputs[9]), 'formatting preserves impact')
      assert.equal(outputs[17].trimEnd(), outputs[10].trimEnd(), 'formatting preserves result')
      factsObserved = true
    }
    if (index === 19) {
      assert.equal(command, 'test -z "$(git status --porcelain)"')
      assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'cleanup leaves lane clean')
      cleanObserved = true
    }
  }

  assert.ok(diffObserved && factsObserved && cleanObserved, 'diff, fact preservation, and cleanup were observed')
  assert.equal(run('git', ['rev-parse', 'HEAD'], { cwd: lane }).trim(), base, 'lane remains exact HEAD')
  assert.equal(run('git', ['rev-parse', 'HEAD']).trim(), base, 'protected checkout HEAD is unchanged')
  assert.equal(run('git', ['status', '--porcelain']), protectedStatusBefore, 'protected checkout status is unchanged')

  const evidence = {
    base,
    head: base,
    protectedCheckout: repoRoot,
    lane,
    files: [practice.fixture.path],
    commands: practice.commands,
    results: commandResults,
    gates: {
      narrow: commandResults.find((observation) => observation.command === lab.narrowGate),
      full: commandResults.find((observation) => observation.command === lab.fullGate),
    },
    uncertainty: 'narrow and full repository gates are enclosing gates and are not complete inside this harness',
  }
  assert.throws(() => validateEvidence(evidence), /command result was observed/, 'skipped repository gates cannot pass as evidence')

  // Pure validator fixture: the enclosing `just verify` supplies these final
  // observations for a real journey. Do not relabel the in-harness skips themselves.
  const completeEvidence = structuredClone(evidence)
  for (const gate of ['narrow', 'full']) {
    const gateResult = completeEvidence.results.find((observation) => observation.command === lab[`${gate}Gate`])
    Object.assign(gateResult, { observed: true, status: 0, result: `fixture: enclosing ${gate} gate completed` })
    completeEvidence.gates[gate] = gateResult
  }
  completeEvidence.uncertainty = 'none observed'
  validateEvidence(completeEvidence)

  for (const mutate of [
    (candidate) => { candidate.results[0].observed = false },
    (candidate) => { candidate.results.pop() },
    (candidate) => { candidate.gates.narrow.status = null; candidate.gates.narrow.observed = false },
    (candidate) => { candidate.gates.full.status = null; candidate.gates.full.observed = false },
  ]) {
    const falseGreen = structuredClone(completeEvidence)
    mutate(falseGreen)
    assert.throws(() => validateEvidence(falseGreen), /observed|one observation/, 'skipped-as-pass evidence is rejected')
  }

  console.log(
    `role-lab-coding-agent: PASS — exact-HEAD isolated lane; ${practice.commands.length - 2}/${practice.commands.length} ` +
      'displayed commands observed; two enclosing repository gates skipped honestly; frontend fixture reused; ' +
      'protected checkout unchanged; skipped evidence rejected',
  )
} finally {
  rmSync(parent, { recursive: true, force: true })
}
