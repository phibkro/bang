import assert from 'node:assert/strict'
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { spawnSync } from 'node:child_process'
import { fileURLToPath } from 'node:url'
import { kernelProofReference, roleLabContent } from './role-lab-content.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const lab = roleLabContent.find((candidate) => candidate.key === 'kernel-proof')
assert.ok(lab, 'kernel-proof role-lab content exists')
assert.deepEqual(
  lab.stages.map((stage) => stage.id),
  ['retrieve-predict', 'trace-seam', 'isolated-practice', 'inspect-select'],
)
assert.equal(
  roleLabContent.filter((candidate) => candidate.key === 'kernel-proof').length,
  1,
  'kernel-proof role-lab content is unique',
)
const practice = lab.stages[2]
assert.equal(practice.fixture.path, 'KernelProofLab.lean')
assert.equal(practice.commands[0], 'nix develop --command lake build Bang.Core.Soundness')
assert.equal(
  practice.commands.filter((command) => command.includes('just test-role-lab-kernel-proof')).length,
  1,
  'the displayed command list has one recursive self-invocation',
)
assert.ok(
  practice.commands.some((command) =>
    command.includes("STOP: replace exact? with Lean current suggestion before continuing."),
  ),
)
assert.ok(practice.commands.some((command) => command.includes('nix develop --command just axioms')))
assert.equal(practice.commands.at(-1), 'test -z "$(git status --porcelain)"')

function run(command, args, { cwd = repoRoot, env = process.env, input } = {}) {
  const result = spawnSync(command, args, {
    cwd,
    env,
    encoding: 'utf8',
    input,
  })
  const output = `${result.stdout ?? ''}${result.stderr ?? ''}`
  assert.equal(
    result.status,
    0,
    `command failed: ${command} ${args.join(' ')}\ncwd: ${cwd}\n${output}`,
  )
  return output
}

function runPractice(command, lane, practicePath, bundle, extraEnv = {}) {
  return run('bash', ['-lc', command], {
    cwd: lane,
    env: { ...process.env, practice: practicePath, bundle, ...extraEnv },
  })
}

function extractSuggestion(output) {
  const lines = output.split(/\r?\n/)
  const markers = lines.flatMap((line, index) => line.trim() === 'Try this:' ? [index] : [])
  assert.equal(markers.length, 1, 'direct Lean emits exactly one Try this block')
  const index = markers[0]
  assert.match(lines[index + 1] ?? '', /^\s+\S/, 'Try this has one indented suggestion line')
  assert.ok(!/^\s+\S/.test(lines[index + 2] ?? ''), 'Try this suggestion is one line')
  const suggestion = lines[index + 1].trim().replace(/^\[apply\]\s*/, '')
  assert.notEqual(suggestion, '', 'suggestion is nonempty')
  assert.doesNotMatch(suggestion, /\b(?:sorry|admit)\b/i, 'suggestion does not bypass proof')
  assert.doesNotMatch(suggestion, /\b[\w.]+\?/, 'suggestion does not contain another suggestion tactic')
  return suggestion
}

function parseAxiomOutput(output) {
  const adapter = `
import json
import sys
sys.path.insert(0, sys.argv[1])
from audit_facts import TRUSTED, parse_axiom_entries
print(json.dumps({"entries": parse_axiom_entries(sys.stdin.read()), "trusted": sorted(TRUSTED)}))
`
  return JSON.parse(run('python3', ['-c', adapter, join(repoRoot, 'tools')], { input: output }))
}

function requireSingleReport(output, theorem) {
  const parsed = parseAxiomOutput(output)
  assert.deepEqual(parsed.entries.map(([name]) => name), [theorem], `one report for ${theorem}`)
  return { axioms: parsed.entries[0][1], trusted: new Set(parsed.trusted) }
}

function requireCanonicalCensus(output) {
  const canonical = output.split(/\r?\n/).filter((line) =>
    /^[✓⚠]\s+Bang\.subst_value:/.test(line))
  const bare = output.split(/\r?\n/).filter((line) =>
    /^[✓⚠]\s+subst_value:/.test(line))
  assert.equal(bare.length, 0, 'authoritative census never reports bare subst_value')
  assert.equal(canonical.length, 1, 'authoritative census reports Bang.subst_value exactly once')
  assert.match(canonical[0], /^✓\s+Bang\.subst_value:/, 'Bang.subst_value is within the trusted baseline')
  assert.doesNotMatch(canonical[0], /sorryAx/, 'Bang.subst_value contains no sorryAx')
}

function replaceProofBody(source, proofLines) {
  const start = source.indexOf(':= by')
  const end = source.indexOf('\n\n#print axioms')
  assert.ok(start >= 0 && end > start, 'scratch theorem proof body is uniquely bounded')
  return `${source.slice(0, start)}:= by\n${proofLines.join('\n')}${source.slice(end)}`
}

assert.throws(() => extractSuggestion('Try this:\n  exact sorry'), /bypass proof/)
assert.throws(() => extractSuggestion('Try this:\n  exact ih\n  exact ih'), /one line/)
assert.throws(() => extractSuggestion('Try this:\n  exact?'), /suggestion tactic/)

const parent = mkdtempSync(join(tmpdir(), 'bang-role-lab-kernel-proof-'))
const lane = join(parent, 'repo')
const bundle = join(parent, 'evidence')
const base = run('git', ['rev-parse', 'HEAD']).trim()
const branch = `practice/kernel-proof-harness-${process.pid}-${Date.now()}`
const practicePath = join(lane, practice.fixture.path)
const theorem = 'Bang.GradeVec.zero_smul_scratch'
let skipped = 0
let negativesRun = false
let referenceProbeRun = false

try {
  run(join(repoRoot, 'tools', 'new-worktree.sh'), [lane, branch, base])
  assert.equal(run('git', ['rev-parse', 'HEAD'], { cwd: lane }).trim(), base, 'lane is exact source HEAD')
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'exact-HEAD lane starts clean')
  run('mkdir', [bundle])

  writeFileSync(practicePath, practice.fixture.source)
  assert.equal(readFileSync(practicePath, 'utf8'), practice.fixture.source)
  assert.equal(practice.fixture.source.split('exact?').length - 1, 1, 'fixture has one replacement marker')

  for (const [index, command] of practice.commands.entries()) {
    if (command.includes('just test-role-lab-kernel-proof')) {
      skipped += 1
      continue
    }

    const output = runPractice(command, lane, practicePath, bundle)
    if (index === 1) {
      const suggestion = extractSuggestion(output)
      assert.ok(!JSON.stringify(lab).includes(suggestion), 'content does not store Lean current proof answer')
      const completed = practice.fixture.source.replace('exact?', suggestion)
      assert.equal(completed.replace(suggestion, 'exact?'), practice.fixture.source, 'only exact? is replaced')
      writeFileSync(practicePath, completed)
    }

    if (command.includes('lake env lean "$practice"') && index > 1) {
      const positive = requireSingleReport(output, theorem)
      assert.deepEqual(positive.axioms, [], 'scratch theorem has an empty axiom set')

      const completed = readFileSync(practicePath, 'utf8')
      const sorryPath = join(lane, 'KernelProofLabSorry.lean')
      writeFileSync(sorryPath, replaceProofBody(completed, ['  sorry']))
      const sorryOutput = runPractice(
        'nix develop --command lake env lean "$mutant"',
        lane,
        practicePath,
        bundle,
        { mutant: sorryPath },
      )
      writeFileSync(join(bundle, 'scratch-sorry-axioms.txt'), sorryOutput)
      const sorryReport = requireSingleReport(sorryOutput, theorem)
      assert.ok(sorryReport.axioms.includes('sorryAx'), 'kernel evidence rejects the sorry mutant')

      const scratchAxiom = 'scratch_zero_smul'
      const axiomDeclaration = `axiom ${scratchAxiom} [MulZeroClass M] (γ : GradeVec M) :\n    GradeVec.smul 0 γ = GradeVec.zeros γ.length\n\n`
      const axiomPath = join(lane, 'KernelProofLabAxiom.lean')
      const withAxiom = completed.replace(
        'theorem zero_smul_scratch',
        `${axiomDeclaration}theorem zero_smul_scratch`,
      )
      writeFileSync(axiomPath, replaceProofBody(withAxiom, [`  exact ${scratchAxiom} γ`]))
      const axiomOutput = runPractice(
        'nix develop --command lake env lean "$mutant"',
        lane,
        practicePath,
        bundle,
        { mutant: axiomPath },
      )
      writeFileSync(join(bundle, 'scratch-declared-axiom.txt'), axiomOutput)
      const axiomReport = requireSingleReport(axiomOutput, theorem)
      assert.ok(
        axiomReport.axioms.includes(scratchAxiom) &&
          axiomReport.axioms.some((axiom) => !axiomReport.trusted.has(axiom)),
        `kernel evidence rejects the unexpected scratch axiom mutant: ${JSON.stringify(axiomReport.axioms)}`,
      )

      rmSync(sorryPath)
      rmSync(axiomPath)
      negativesRun = true
    }

    if (command.includes('nix develop --command just axioms')) {
      requireCanonicalCensus(output)
      const referencePath = join(lane, 'KernelProofReferenceCheck.lean')
      writeFileSync(referencePath, `import Bang.Spec\n#check ${kernelProofReference.statement}\n#check ${kernelProofReference.implementation}\n`)
      const referenceOutput = runPractice(
        'nix develop --command lake env lean "$mutant"',
        lane,
        practicePath,
        bundle,
        { mutant: referencePath },
      )
      assert.match(referenceOutput, /Bang\.subst_value/)
      assert.match(referenceOutput, /Bang\.subst_value_proof/)
      writeFileSync(join(bundle, 'reference-check.txt'), referenceOutput)
      rmSync(referencePath)
      referenceProbeRun = true
    }
  }

  assert.equal(skipped, 1, 'only the displayed recursive self-invocation is skipped')
  assert.ok(negativesRun, 'negative axiom poles ran')
  assert.ok(referenceProbeRun, 'statement and implementation declaration probe ran')
  assert.equal(run('git', ['status', '--porcelain'], { cwd: lane }), '', 'displayed cleanup leaves lane clean')
  assert.equal(readFileSync(join(bundle, practice.fixture.path), 'utf8').includes('exact?'), false)
  for (const artifact of [
    'scratch-suggestion.txt',
    'scratch-check.txt',
    'scratch-axioms.txt',
    'audit-axioms.txt',
    'KernelProofLab.lean',
    'scratch-sorry-axioms.txt',
    'scratch-declared-axiom.txt',
    'reference-check.txt',
  ]) {
    assert.ok(readFileSync(join(bundle, artifact), 'utf8').length > 0, `evidence artifact exists: ${artifact}`)
  }

  console.log(
    `role-lab-kernel-proof: PASS — exact-HEAD lane; ${practice.commands.length - skipped}/${practice.commands.length} ` +
      `displayed commands executed; one recursive command skipped; dynamic exact? completion; ` +
      `empty scratch axioms; negative poles rejected; ${kernelProofReference.statement} canonical census trusted`,
  )
} finally {
  rmSync(parent, { recursive: true, force: true })
}
