import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { roleLabContent, toolingDocsExamplesReference } from './role-lab-content.mjs'
import { acquireRoleLabLane } from './role-lab-lane.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const lab = roleLabContent.find((candidate) => candidate.key === 'tooling-docs-examples')
assert.ok(lab, 'tooling-docs-examples role-lab content exists')
assert.equal(
  roleLabContent.filter((candidate) => candidate.key === 'tooling-docs-examples').length,
  1,
  'tooling-docs-examples role-lab content is unique',
)
assert.deepEqual(
  lab.stages.map((stage) => stage.id),
  ['retrieve-predict', 'trace-seam', 'isolated-practice', 'inspect-select'],
)

const practice = lab.stages[2]
assert.equal(practice.fixture.path, 'main.bang')
assert.match(practice.fixture.source, /^-- Role-lab practice:/)
assert.equal(practice.commands[0], 'nix develop --command lake build bang', 'lane binary is built first')
assert.equal(
  practice.commands.filter((command) => command.includes('just update-example logger-counting')).length,
  1,
  'the existing named update interface is used exactly once',
)
assert.equal(
  practice.commands.filter((command) => command === 'nix develop --command python3 tools/docfacts_logger.py').length,
  2,
  'the existing generator runs twice to prove idempotence',
)
assert.equal(
  practice.commands.filter((command) => command.includes('just test-role-lab-tooling-docs-examples')).length,
  1,
  'the displayed command list has one recursive self-invocation',
)
for (const engine of ['env', 'oracle', 'compiled']) {
  const commands = practice.commands.filter((command) => command.includes(`--engine=${engine}`))
  assert.equal(commands.length, 1, `the displayed command list runs ${engine} exactly once`)
  assert.match(commands[0], /^\.\/\.lake\/build\/bin\/bang /, `${engine} uses the lane-built binary`)
}
assert.equal(
  practice.commands.filter((command) => command.includes('> "$example/expected.txt"')).length,
  0,
  'no displayed command types or redirects accepted output',
)
assert.equal(practice.commands.at(-1), 'test -z "$(git status --porcelain)"')

// Positional post-conditions are deliberately anchored to command content. A
// seemingly harmless reorder must fail here instead of checking the wrong state.
const updateCommand = 'nix develop --command just update-example logger-counting 2>&1 | tee "$bundle/update.txt"'
const compiledCommand = './.lake/build/bin/bang run --engine=compiled "$example/main.bang" > "$bundle/compiled.txt" && diff -u "$example/expected.txt" "$bundle/compiled.txt"'
const stalePoleCommand = "if nix develop --command python3 tools/docfacts_logger.py --check > \"$bundle/stale-projection.txt\" 2>&1; then printf '%s\\n' 'STOP: stale example projection was accepted.' >&2; false; fi"
const firstGenerationCommand = 'nix develop --command python3 tools/docfacts_logger.py'
const diffCommand = 'git diff -- examples/logger-counting/main.bang examples/logger-counting/expected.txt examples/logger-silent/main.bang docfacts/examples/logger-counting.json docs/reference/examples/logger-counting.md > "$bundle/practice.diff" && test -s "$bundle/practice.diff"'
const idempotenceCommand = 'sha256sum --check "$bundle/projection.sha256"'
const docfactGateCommand = 'nix develop --command just test-docfacts-logger > "$bundle/docfacts-check.txt" 2>&1'
const docsGateCommand = 'nix develop --command just docs-check > "$bundle/docs-check.txt" 2>&1'
assert.equal(practice.commands[7], updateCommand, 'snapshot post-condition stays anchored to update')
assert.equal(practice.commands[10], compiledCommand, 'engine post-condition stays anchored to compiled')
assert.equal(practice.commands[13], stalePoleCommand, 'falsifier post-condition stays anchored to stale check')
assert.equal(practice.commands[14], firstGenerationCommand, 'projection post-condition stays anchored to generation')
assert.equal(practice.commands[16], diffCommand, 'diff post-condition stays anchored to diff capture')
assert.equal(practice.commands[20], idempotenceCommand, 'idempotence post-condition stays anchored to hash check')
assert.equal(practice.commands[21], docfactGateCommand, 'docfact post-condition stays anchored to its gate')
assert.equal(practice.commands[22], docsGateCommand, 'docs post-condition stays anchored to docs-check')

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

function runPractice(command, lane, practicePath, bundle, example, silent, fact, page) {
  return run('bash', ['-o', 'pipefail', '-lc', command], {
    cwd: lane,
    env: { ...process.env, lane, practice: practicePath, bundle, example, silent, fact, page },
  })
}

const parent = mkdtempSync(join(tmpdir(), 'bang-role-lab-tooling-docs-examples-'))
const bundle = join(parent, 'evidence')
const base = run('git', ['rev-parse', 'HEAD']).trim()
let skipped = 0
let snapshotObserved = false
let enginesObserved = false
let stalePoleObserved = false
let projectionObserved = false
let diffObserved = false
let idempotenceObserved = false

try {
  const { lane } = acquireRoleLabLane({ repoRoot, parent, base, labKey: 'tooling-docs-examples', run })
  const practicePath = join(lane, practice.fixture.path)
  const example = join(lane, 'examples', toolingDocsExamplesReference.exampleId)
  const silent = join(lane, 'examples', 'logger-silent')
  const expectedPath = join(lane, toolingDocsExamplesReference.expectedOutput)
  const fact = join(lane, toolingDocsExamplesReference.fact)
  const page = join(lane, toolingDocsExamplesReference.projection)
  run('mkdir', [bundle])

  const committedExpected = readFileSync(expectedPath, 'utf8')
  writeFileSync(practicePath, practice.fixture.source)
  assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)

  for (const [index, command] of practice.commands.entries()) {
    if (command.includes('just test-role-lab-tooling-docs-examples')) {
      skipped += 1
      continue
    }

    const output = runPractice(command, lane, practicePath, bundle, example, silent, fact, page)

    if (index === 7) {
      assert.equal(command, updateCommand, 'snapshot observation follows the named update command')
      assert.equal(readFileSync(expectedPath, 'utf8'), committedExpected, 'runner recreates accepted stdout')
      assert.match(readFileSync(join(bundle, 'update.txt'), 'utf8'), /wrote examples\/logger-counting\/expected\.txt/)
      snapshotObserved = true
    }

    if (index === 10) {
      assert.equal(command, compiledCommand, 'engine observation follows the compiled command')
      for (const engine of ['env', 'oracle', 'compiled']) {
        assert.equal(readFileSync(join(bundle, `${engine}.txt`), 'utf8'), committedExpected)
      }
      enginesObserved = true
    }

    if (index === 11) {
      assert.equal(JSON.parse(readFileSync(join(bundle, 'check.json'), 'utf8')).ok, true)
    }
    if (index === 12) {
      const query = JSON.parse(readFileSync(join(bundle, 'query.json'), 'utf8'))
      assert.equal(query.ok, true)
      assert.ok(query.decls.some((decl) => decl.name === 'Log' && decl.kind === 'effect'))
    }

    if (index === 13) {
      assert.equal(command, stalePoleCommand, 'falsifier observation follows the stale check')
      const stale = readFileSync(join(bundle, 'stale-projection.txt'), 'utf8')
      assert.match(stale, /stale or missing docfacts\/examples\/logger-counting\.json/)
      stalePoleObserved = true
    }

    if (index === 14) {
      assert.equal(command, firstGenerationCommand, 'projection observation follows generation')
      const generatedFact = JSON.parse(readFileSync(fact, 'utf8'))
      assert.equal(generatedFact.program.text, practice.fixture.source)
      assert.equal(generatedFact.expectedOutput.text, committedExpected)
      assert.deepEqual(generatedFact.supportedEngines, ['env', 'oracle', 'compiled'])
      assert.match(readFileSync(page, 'utf8'), /Role-lab practice: canonical source flows through checked projections/)
      projectionObserved = true
    }

    if (index === 16) {
      assert.equal(command, diffCommand, 'diff observation follows diff capture')
      const diff = readFileSync(join(bundle, 'practice.diff'), 'utf8')
      for (const path of [
        toolingDocsExamplesReference.program,
        'examples/logger-silent/main.bang',
        toolingDocsExamplesReference.fact,
        toolingDocsExamplesReference.projection,
      ]) assert.match(diff, new RegExp(path.replaceAll('/', '\\/')))
      diffObserved = true
    }

    if (index === 20) {
      assert.equal(command, idempotenceCommand, 'idempotence observation follows hash check')
      assert.match(output, /docfacts\/examples\/logger-counting\.json: OK/)
      assert.match(output, /docs\/reference\/examples\/logger-counting\.md: OK/)
      idempotenceObserved = true
    }

    if (index === 21) {
      assert.equal(command, docfactGateCommand, 'docfact evidence follows its focused gate')
      assert.match(readFileSync(join(bundle, 'docfacts-check.txt'), 'utf8'), /docfacts-logger: 11 passed, 0 failed/)
    }
    if (index === 22) {
      assert.equal(command, docsGateCommand, 'docs evidence follows docs-check')
      assert.match(readFileSync(join(bundle, 'docs-check.txt'), 'utf8'), /site-model: PASS/)
    }
  }

  assert.equal(skipped, 1, 'only the displayed recursive self-invocation is skipped')
  assert.ok(snapshotObserved, 'runner-owned snapshot recreation was observed')
  assert.ok(enginesObserved, 'all declared engines were observed')
  assert.ok(stalePoleObserved, 'stale projection falsifier was observed')
  assert.ok(projectionObserved, 'validated fact and generated page were observed')
  assert.ok(diffObserved, 'source/fact/page diff was observed')
  assert.ok(idempotenceObserved, 'idempotent regeneration was observed')
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'displayed cleanup leaves lane clean')
  for (const artifact of [
    'original-main.bang',
    'original-expected.txt',
    'original-silent-main.bang',
    'update.txt',
    'env.txt',
    'oracle.txt',
    'compiled.txt',
    'check.json',
    'query.json',
    'stale-projection.txt',
    'practice.diff',
    'logger-counting.json',
    'logger-counting.md',
    'projection.sha256',
    'docfacts-check.txt',
    'docs-check.txt',
  ]) assert.ok(readFileSync(join(bundle, artifact), 'utf8').length > 0, `evidence artifact exists: ${artifact}`)

  console.log(
    `role-lab-tooling-docs-examples: PASS — exact-HEAD lane; ${practice.commands.length - skipped}/${practice.commands.length} ` +
      'displayed commands executed; one recursive command skipped; lane-built env/oracle/compiled agree; ' +
      'runner-owned snapshot recreated; stale projection rejected; source/fact/page diff generated twice byte-identically',
  )
} finally {
  rmSync(parent, { recursive: true, force: true })
}
