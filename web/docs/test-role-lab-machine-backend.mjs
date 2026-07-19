import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { machineBackendReference, roleLabContent } from './role-lab-content.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const lab = roleLabContent.find((candidate) => candidate.key === 'machine-backend')
assert.ok(lab, 'machine-backend role-lab content exists')
assert.deepEqual(
  lab.stages.map((stage) => stage.id),
  ['retrieve-predict', 'trace-seam', 'isolated-practice', 'inspect-select'],
)
assert.equal(
  roleLabContent.filter((candidate) => candidate.key === 'machine-backend').length,
  1,
  'machine-backend role-lab content is unique',
)

const practice = lab.stages[2]
assert.equal(practice.fixture.path, 'main.bang')
assert.equal(practice.fixture.source, 'let main = 19 + 23\n')
assert.equal(
  practice.commands.filter((command) => command.includes('just test-role-lab-machine-backend')).length,
  1,
  'the displayed command list has one recursive self-invocation',
)
for (const engine of ['env', 'oracle', 'compiled']) {
  assert.equal(
    practice.commands.filter((command) => command.includes(`--engine=${engine}`)).length,
    1,
    `the displayed command list runs ${engine} exactly once`,
  )
}
assert.equal(
  practice.commands.filter((command) => command.includes(machineBackendReference.emitterHarness)).length,
  1,
  'the displayed command list runs the supported emitter harness exactly once',
)
assert.ok(
  practice.commands.some((command) => command.includes('just check Bang/Backend/AbstractMachine.lean')),
  'the displayed command list runs the Agree battery owner',
)
assert.equal(practice.commands.at(-1), 'test -z "$(git status --porcelain)"')
const expectedCommand = `printf '${machineBackendReference.expectedOutput.replaceAll('\n', '\\n')}' > "$expected"`
const compiledCommand = './.lake/build/bin/bang run --engine=compiled "$practice" > "$bundle/compiled.txt" && diff -u "$expected" "$bundle/compiled.txt"'
assert.equal(practice.commands[2], expectedCommand, 'expected-output post-condition stays anchored to its command')
assert.equal(practice.commands[5], compiledCommand, 'engine post-condition stays anchored to the compiled command')

function result(command, args, { cwd = repoRoot, env = process.env } = {}) {
  return spawnSync(command, args, { cwd, env, encoding: 'utf8' })
}

function run(command, args, options = {}) {
  const completed = result(command, args, options)
  const output = `${completed.stdout ?? ''}${completed.stderr ?? ''}`
  assert.equal(
    completed.status,
    0,
    `command failed: ${command} ${args.join(' ')}\ncwd: ${options.cwd ?? repoRoot}\n${output}`,
  )
  return output
}

function runPractice(command, lane, practicePath, expectedPath, bundle) {
  return run('bash', ['-o', 'pipefail', '-lc', command], {
    cwd: lane,
    env: {
      ...process.env,
      lane,
      practice: practicePath,
      expected: expectedPath,
      bundle,
    },
  })
}

const parent = mkdtempSync(join(tmpdir(), 'bang-role-lab-machine-backend-'))
const lane = join(parent, 'repo')
const bundle = join(parent, 'evidence')
const base = run('git', ['rev-parse', 'HEAD']).trim()
const branch = `practice/machine-backend-harness-${process.pid}-${Date.now()}`
const practicePath = join(lane, practice.fixture.path)
const expectedPath = join(lane, 'expected.txt')
let skipped = 0
let wrongExpectedRejected = false
let fixtureOnlyObserved = false

try {
  run(join(repoRoot, 'tools', 'new-worktree.sh'), [lane, branch, base])
  assert.equal(run('git', ['rev-parse', 'HEAD'], { cwd: lane }).trim(), base, 'lane is exact source HEAD')
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'exact-HEAD lane starts clean')
  run('mkdir', [bundle])

  writeFileSync(practicePath, practice.fixture.source)
  assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)

  for (const [index, command] of practice.commands.entries()) {
    if (command.includes('just test-role-lab-machine-backend')) {
      skipped += 1
      continue
    }

    runPractice(command, lane, practicePath, expectedPath, bundle)

    if (index === 2) {
      assert.equal(command, expectedCommand, 'expected-output observation follows its materialization command')
      assert.equal(
        readFileSync(expectedPath, 'utf8'),
        machineBackendReference.expectedOutput,
        'the displayed command materializes the committed expected output',
      )
      assert.deepEqual(
        run('git', ['status', '--porcelain'], { cwd: lane }).trim().split('\n').sort(),
        ['?? expected.txt', '?? main.bang'],
        'only the disposable source and expected fixture exist in the lane',
      )
      fixtureOnlyObserved = true
    }

    if (index === 5) {
      assert.equal(command, compiledCommand, 'engine observation follows the compiled command')
      for (const engine of ['env', 'oracle', 'compiled']) {
        const outputPath = join(bundle, `${engine}.txt`)
        assert.equal(
          readFileSync(outputPath, 'utf8'),
          machineBackendReference.expectedOutput,
          `${engine} matches the committed expected output`,
        )
      }
      writeFileSync(expectedPath, '41\n')
      for (const engine of ['env', 'oracle', 'compiled']) {
        const rejected = result('diff', ['-u', expectedPath, join(bundle, `${engine}.txt`)], { cwd: lane })
        assert.equal(rejected.status, 1, `wrong expected output rejects ${engine}`)
      }
      writeFileSync(expectedPath, machineBackendReference.expectedOutput)
      wrongExpectedRejected = true
    }

    if (command.includes('just check Bang/Backend/AbstractMachine.lean')) {
      const machineSource = readFileSync(join(lane, machineBackendReference.machineSource), 'utf8')
      assert.match(machineSource, /def Agree \(fuel : Nat\)/, 'compiled owner defines the Agree oracle')
      assert.match(machineSource, /example : Agree/, 'compiled owner contains executable Agree cases')
      assert.ok(readFileSync(join(bundle, 'agree.txt'), 'utf8').length > 0, 'Agree check evidence exists')
    }

    if (command.includes(machineBackendReference.emitterHarness)) {
      const emitter = readFileSync(join(bundle, 'emitter.txt'), 'utf8')
      assert.match(emitter, /emit exe reports: EMITTED=\d+\s+REFUSED=0/, 'emitter reports no refusal')
      assert.match(emitter, /^prog0\s+.*\s+OK$/m, 'supported integer-add anchor agrees')
      assert.match(emitter, /PASS — all \d+ emitted core-wasm modules ran on wasmtime with a value matching Source\.eval\./)
    }
  }

  assert.equal(skipped, 1, 'only the displayed recursive self-invocation is skipped')
  assert.ok(fixtureOnlyObserved, 'fixture-only lane state was observed')
  assert.ok(wrongExpectedRejected, 'known-wrong expected output rejected every engine')
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'displayed cleanup leaves lane clean')
  for (const artifact of [
    'env.txt',
    'oracle.txt',
    'compiled.txt',
    'agree.txt',
    'emitter.txt',
    'main.bang',
    'expected.txt',
  ]) {
    assert.ok(readFileSync(join(bundle, artifact), 'utf8').length > 0, `evidence artifact exists: ${artifact}`)
  }

  console.log(
    `role-lab-machine-backend: PASS — exact-HEAD lane; ${practice.commands.length - skipped}/${practice.commands.length} ` +
      'displayed commands executed; one recursive command skipped; env/oracle/compiled agree on 42; ' +
      'wrong-expected pole rejected; Agree battery checked; supported Wasm emission agrees with Source.eval',
  )
} finally {
  rmSync(parent, { recursive: true, force: true })
}
