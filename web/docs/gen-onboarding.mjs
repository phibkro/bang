// Generate the P4.1 onboarding projections from existing authorities:
// page-manifest.json owns route choices/pages; canonical examples own outputs;
// resolved docfact status owns evidence labels, claims, sources, and commands.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { escapeProse } from './mdx-safe.mjs'
import { roleLabContent } from './role-lab-content.mjs'
import { compileSite, resolveRoleLabContent } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const pagesDir = join(siteDir, 'src', 'pages')
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot,
})

function repositoryLink(path) {
  return `${site.repository.url}/blob/${site.repository.branch}/${path}`
}

function writeRoute(route, text) {
  const emitted = site.routeToPage.get(route)
  if (!emitted) throw new Error(`gen-onboarding: route is not emitted by the site model: ${route}`)
  const destination = join(pagesDir, emitted.outputPath)
  mkdirSync(dirname(destination), { recursive: true })
  writeFileSync(destination, text)
}

function renderRoutes() {
  const lines = [
    '# Choose a contributor route',
    '',
    'Choose by the **first edit seam and smallest falsifying gate**, not by a reading list. ' +
      'The frontend route now has a complete role lab; the remaining routes start at their ' +
      'existing references.',
    '',
  ]
  const pagesById = new Map(site.pages.map((page) => [page.id, page]))
  for (const choice of site.routeChoices) {
    const targetKind = pagesById.get(choice.targetPage)?.target.kind
    const startLabel = targetKind === 'onboarding-page' ? 'role lab' : 'existing reference'
    lines.push(`## ${escapeProse(choice.title)}`, '')
    lines.push(escapeProse(choice.summary), '')
    lines.push(`**Start:** [${startLabel}](${choice.target})`, '')
    lines.push('**First seams:**', '')
    for (const seam of choice.seams) {
      lines.push(`- [\`${seam}\`](${repositoryLink(seam)})`)
    }
    lines.push('', `**First bounded change:** ${escapeProse(choice.firstChange)}`, '')
    lines.push('**Narrow gate:**', '', '```bash', choice.narrowGate, '```', '')
    lines.push('**Full gate:**', '', '```bash', choice.fullGate, '```', '')
  }
  return `${lines.join('\n')}\n`
}

function loadExpected(name) {
  return readFileSync(join(repoRoot, 'examples', name, 'expected.txt'), 'utf8').trimEnd()
}

function evidenceLabel(status) {
  if (status.kind !== 'evidence') {
    throw new Error('gen-onboarding: logger-counting page lacks an evidence-backed status')
  }
  return status.label[0].toUpperCase() + status.label.slice(1)
}

function renderEvidence() {
  const loggerPage = site.pages.find((page) => page.id === 'logger-counting-evidence')
  if (!loggerPage) throw new Error('gen-onboarding: logger-counting evidence page is missing')
  const status = loggerPage.status
  const journeyChoice = site.routeChoices.find((choice) => choice.id === 'tooling-docs-examples')
  if (!journeyChoice) throw new Error('gen-onboarding: tooling/docs/examples route choice is missing')

  const examples = [
    ['Thunk/force', 'thunk-force'],
    ['Effect arithmetic', 'effect-op-arith'],
    ['Counting handler', 'logger-counting'],
    ['Silent handler', 'logger-silent'],
  ]
  const lines = [
    '# Common journey evidence',
    '',
    'This page is generated. Program outputs come from each canonical `expected.txt`; ' +
      'the logger evidence label and claim come from the validated serialized docfact. ' +
      'The page does not contain a hand-copied terminal transcript.',
    '',
    '```text',
    'canonical source → check/query → env | oracle | compiled → expected output',
    '```',
    '',
    '| Moment | Canonical source | Expected on env/oracle/compiled |',
    '|---|---|---:|',
  ]
  for (const [title, name] of examples) {
    const source = `examples/${name}/main.bang`
    lines.push(`| ${title} | [\`${source}\`](${repositoryLink(source)}) | \`${escapeProse(loadExpected(name))}\` |`)
  }
  lines.push(
    '',
    'The executable journey additionally checks `1 + 2`, exact `check --json` output, ' +
      'the `query dump` schema, and that the two logger programs differ only in the handler clause.',
    '',
    '## Serialized logger evidence',
    '',
    `**${evidenceLabel(status)}** — ${escapeProse(status.claim)}`,
    '',
    '**Sources:**',
    '',
  )
  for (const source of status.sources) lines.push(`- [\`${source}\`](${repositoryLink(source)})`)
  lines.push('', '**Validating commands:**', '')
  for (const command of status.commands) lines.push('```bash', command, '```', '')
  lines.push(
    '## Complete common-journey gate',
    '',
    '```bash',
    journeyChoice.narrowGate,
    `${journeyChoice.narrowGate} --json --require-clean > /tmp/bang-onboarding-journey.json`,
    '```',
    '',
    'The machine artifact records the source SHA, binary hash, every required step result, ' +
      'and explicit pass/fail/skip counts. `--require-clean` refuses dirty provenance.',
    '',
  )
  return lines.join('\n')
}

function pageLink(page) {
  if (page.target.kind !== 'repository-link') return page.target.route
  return `${site.repository.url}/${page.target.view}/${site.repository.branch}/${page.target.path}`
}

function appendChecks(lines, checks) {
  for (const check of checks) lines.push(`- ${escapeProse(check)}`)
  lines.push('')
}

function renderRoleLab(lab) {
  const [retrieve, trace, practice, inspect] = lab.stages
  const lines = [
    `# ${escapeProse(lab.page.title)}`,
    '',
    'This role lab is generated from the shared four-stage contract. Page identity, ' +
      'prerequisites, seams, and gates remain manifest-owned.',
    '',
    '## Prerequisites',
    '',
  ]
  for (const prerequisite of lab.prerequisites) {
    lines.push(`- [${escapeProse(prerequisite.title)}](${pageLink(prerequisite)})`)
  }
  lines.push(
    '',
    '## 1. Retrieve and predict',
    '',
    escapeProse(retrieve.prose.trim()),
    '',
    '**Retrieve:**',
    '',
  )
  appendChecks(lines, retrieve.retrievalChecks)
  lines.push('**Predict before running:**', '')
  appendChecks(lines, retrieve.predictionChecks)
  lines.push('## 2. Trace the seam', '', escapeProse(trace.prose.trim()), '', '**Checks:**', '')
  appendChecks(lines, trace.checks)
  lines.push('**Tracked seams:**', '')
  for (const seam of lab.seams) lines.push(`- [\`${seam}\`](${repositoryLink(seam)})`)
  lines.push(
    '',
    '## 3. Practise in isolation',
    '',
    escapeProse(practice.prose.trim()),
    '',
    'Start from the clean, ready checkout used for the common journey. The project helper ' +
      'creates an independent full clone at its exact commit; all writes and gates below happen there.',
    '',
    '```bash',
    'set -euo pipefail',
    'root="$(git rev-parse --show-toplevel)"',
    'test -z "$(git -C "$root" status --porcelain)"',
    'base="$(git -C "$root" rev-parse HEAD)"',
    'parent="$(mktemp -d)"',
    'lane="$parent/repo"',
    `branch="practice/${lab.routeChoice.id}-$(date +%s)-$$"`,
    '"$root/tools/new-worktree.sh" "$lane" "$branch" "$base"',
    'cd "$lane"',
    `practice="$lane/${practice.fixture.path}"`,
    'bang="$root/.lake/build/bin/bang"',
    'cat > "$practice" <<\'BANG\'',
    practice.fixture.source.trimEnd(),
    'BANG',
    '```',
    '',
    '**Run every step in order:**',
    '',
    '```bash',
    ...practice.commands,
    '```',
    '',
  )
  lines.push(
    `**Bounded outcome:** ${escapeProse(practice.boundedOutcome)}`,
    '',
    '## 4. Inspect evidence and select live work',
    '',
    escapeProse(inspect.prose.trim()),
    '',
    '**Evidence checks:**',
    '',
  )
  appendChecks(lines, inspect.evidenceChecks)
  lines.push(
    '**Narrow gate:**',
    '',
    '```bash',
    lab.narrowGate,
    '```',
    '',
    '**Full gate:**',
    '',
    '```bash',
    lab.fullGate,
    '```',
    '',
    '**Read-only issue selection:**',
    '',
    escapeProse(inspect.issueSelection),
    '',
  )
  return lines.join('\n')
}

const onboardingPages = site.pages.filter((page) => page.target.kind === 'onboarding-page')
const roleLabs = resolveRoleLabContent(site, roleLabContent)
const renderers = new Map([
  ['contributor-routes', renderRoutes],
  ['common-journey-evidence', renderEvidence],
])
for (const lab of roleLabs) renderers.set(lab.page.target.contentKey, () => renderRoleLab(lab))
if (onboardingPages.length !== renderers.size) {
  throw new Error(
    `gen-onboarding: expected ${renderers.size} onboarding pages, found ${onboardingPages.length}`,
  )
}
for (const page of onboardingPages) {
  const render = renderers.get(page.target.contentKey)
  if (!render) throw new Error(`gen-onboarding: unknown content key ${page.target.contentKey}`)
  writeRoute(page.target.route, render())
  renderers.delete(page.target.contentKey)
}
if (renderers.size !== 0) {
  throw new Error(`gen-onboarding: missing manifest pages for ${[...renderers.keys()].join(', ')}`)
}

console.log(`gen-onboarding: ${onboardingPages.length} manifest-backed pages generated`)
