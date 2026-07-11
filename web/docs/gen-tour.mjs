// gen-tour.mjs — the interactive-tour v0 generator (door 4, no-exec floor;
// docs/notes/interactive-tour-design.md §4/§7 item 1-2).
//
// Reads web/docs/tour-manifest.mjs (the ONE hand-authored artifact: lesson
// order + prose) and, for each lesson, READS its code and expected output
// straight from examples/<name>/{main.bang,expected.txt} at generation time
// — never copied by hand, so a lesson's shown output cannot silently drift
// from what `bang run` actually produces (the SSoT move sync-docs.mjs
// already applies to root docs, extended to lesson content).
//
// Drift gate: a lesson whose seed example (or its expected.txt) is missing
// FAILS THE BUILD LOUDLY here — never silently skipped, never a stale
// example rendered from memory. Follows sync-docs.mjs's own convention
// (mkdirSync/writeFileSync straight to src/pages, gitignored build output,
// regenerated every run).
import { mkdirSync, rmSync, readFileSync, writeFileSync, existsSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { escapeProse } from './mdx-safe.mjs'
import { lessons } from './tour-manifest.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const examplesDir = join(repoRoot, 'examples')
const tourDir = join(siteDir, 'src', 'pages', 'tour')

const INSTALL_ONE_LINER =
  'curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh'

// Load one seed example's code + expected output. Throws (LOUD, not a
// console.warn-and-skip) if the example directory or expected.txt is
// missing — a renamed/deleted example breaks the site build, not the reader.
function loadSeed(name, lessonSlug) {
  const dir = join(examplesDir, name)
  const mainPath = join(dir, 'main.bang')
  const expectedPath = join(dir, 'expected.txt')
  if (!existsSync(mainPath)) {
    throw new Error(
      `gen-tour: lesson '${lessonSlug}' references examples/${name}/main.bang, ` +
      `which does not exist. Fix the seed in tour-manifest.mjs or restore the example.`,
    )
  }
  if (!existsSync(expectedPath)) {
    throw new Error(
      `gen-tour: lesson '${lessonSlug}' references examples/${name}/expected.txt, ` +
      `which does not exist. Every tour seed must be a gated example (main.bang + ` +
      `expected.txt) — an output-less example cannot back a lesson.`,
    )
  }
  return {
    name,
    code: readFileSync(mainPath, 'utf8').trimEnd(),
    expected: readFileSync(expectedPath, 'utf8').trimEnd(),
  }
}

function renderLesson(lesson, prevLesson, nextLesson) {
  const seeds = lesson.seeds.map((name) => loadSeed(name, lesson.slug))
  const lines = []
  lines.push(`# ${lesson.n}. ${lesson.title}`)
  lines.push('')
  lines.push(`*Teaches: ${escapeProse(lesson.teaches)}*`)
  lines.push('')
  // Prose is hand-authored Markdown in the manifest — still routed through
  // the same prose-escape as sync-docs.mjs applies to mirrored repo docs,
  // since it can contain bang syntax (`<`, `{`) outside of fences.
  for (const line of lesson.prose.trim().split('\n')) {
    lines.push(escapeProse(line))
  }
  lines.push('')
  for (const seed of seeds) {
    if (seeds.length > 1) {
      lines.push(`### \`examples/${seed.name}/\``)
      lines.push('')
    }
    lines.push('```bang')
    lines.push(seed.code)
    lines.push('```')
    lines.push('')
    lines.push('Expected output (`bang run` stdout):')
    lines.push('')
    lines.push('```text')
    lines.push(seed.expected)
    lines.push('```')
    lines.push('')
  }
  lines.push('---')
  lines.push('')
  lines.push('**Run it yourself:**')
  lines.push('')
  lines.push('```bash')
  lines.push(INSTALL_ONE_LINER)
  for (const seed of seeds) {
    lines.push(`bang run examples/${seed.name}/main.bang`)
  }
  lines.push('```')
  lines.push('')
  const nav = []
  if (prevLesson) nav.push(`[← ${prevLesson.n}. ${prevLesson.title}](/tour/${prevLesson.slug})`)
  if (nextLesson) nav.push(`[${nextLesson.n}. ${nextLesson.title} →](/tour/${nextLesson.slug})`)
  if (nav.length) {
    lines.push(nav.join(' · '))
    lines.push('')
  }
  return lines.join('\n')
}

function renderIndex() {
  const lines = []
  lines.push('# Tour')
  lines.push('')
  lines.push(
    'A guided walk through bang, one concept per page. Every code sample below ' +
    'is a real, gated example from the repo\'s `examples/` corpus — the shown ' +
    'output is read from its `expected.txt` at build time, so it cannot drift ' +
    'from what `bang run` actually produces.',
  )
  lines.push('')
  lines.push('This is the v0, no-exec tour: read the code, read the expected output, ' +
    'then run it yourself locally (each lesson has a copy-paste command). ' +
    'An in-browser "edit and run" door is future work, not v0.')
  lines.push('')
  for (const l of lessons) {
    lines.push(`${l.n}. [${l.title}](/tour/${l.slug}) — ${escapeProse(l.teaches)}`)
  }
  lines.push('')
  return lines.join('\n')
}

rmSync(tourDir, { recursive: true, force: true })
mkdirSync(tourDir, { recursive: true })

writeFileSync(join(tourDir, 'index.md'), renderIndex())
for (let i = 0; i < lessons.length; i++) {
  const lesson = lessons[i]
  const prev = lessons[i - 1]
  const next = lessons[i + 1]
  writeFileSync(join(tourDir, `${lesson.slug}.md`), renderLesson(lesson, prev, next))
}

console.log(`gen-tour: ${lessons.length} lessons generated under src/pages/tour`)
