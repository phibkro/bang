// Generate the interactive tour from two non-overlapping authorities:
// page-manifest.json owns page identity/order/routes; tour-content.mjs owns
// lesson prose and canonical example seeds. Every seed's code/output is read
// from examples/<name>/{main.bang,expected.txt}; missing inputs fail loudly.
import { existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { escapeProse } from './mdx-safe.mjs'
import { compileSite, resolveTourContent } from './site-model.mjs'
import { lessonContent } from './tour-content.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const examplesDir = join(repoRoot, 'examples')
const pagesDir = join(siteDir, 'src', 'pages')
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot,
})

const INSTALL_ONE_LINER =
  'curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh'

function loadSeed(name, lesson) {
  const dir = join(examplesDir, name)
  const mainPath = join(dir, 'main.bang')
  const expectedPath = join(dir, 'expected.txt')
  if (!existsSync(mainPath)) {
    throw new Error(
      `gen-tour: lesson '${lesson.id}' references examples/${name}/main.bang, ` +
      'which does not exist. Fix tour-content.mjs or restore the example.',
    )
  }
  if (!existsSync(expectedPath)) {
    throw new Error(
      `gen-tour: lesson '${lesson.id}' references examples/${name}/expected.txt, ` +
      'which does not exist. Every tour seed must be a gated example.',
    )
  }
  return {
    name,
    code: readFileSync(mainPath, 'utf8').trimEnd(),
    expected: readFileSync(expectedPath, 'utf8').trimEnd(),
  }
}

function renderLesson(lesson, prevLesson, nextLesson) {
  const seeds = lesson.seeds.map((name) => loadSeed(name, lesson))
  const lines = [`# ${lesson.number}. ${lesson.title}`, '', `*Teaches: ${escapeProse(lesson.teaches)}*`, '']
  for (const line of lesson.prose.trim().split('\n')) lines.push(escapeProse(line))
  lines.push('')
  for (const seed of seeds) {
    if (seeds.length > 1) lines.push(`### \`examples/${seed.name}/\``, '')
    lines.push('```bang', seed.code, '```', '')
    lines.push('Expected output (`bang run` stdout):', '', '```text', seed.expected, '```', '')
  }
  lines.push('---', '', '**Run it yourself:**', '', '```bash', INSTALL_ONE_LINER)
  for (const seed of seeds) lines.push(`bang run examples/${seed.name}/main.bang`)
  lines.push('```', '')
  const nav = []
  if (prevLesson) nav.push(`[← ${prevLesson.number}. ${prevLesson.title}](${prevLesson.target.route})`)
  if (nextLesson) nav.push(`[${nextLesson.number}. ${nextLesson.title} →](${nextLesson.target.route})`)
  if (nav.length) lines.push(nav.join(' · '), '')
  return lines.join('\n')
}

function renderIndex(lessons) {
  const lines = [
    '# Tour',
    '',
    'A guided walk through bang, one concept per page. Every code sample below ' +
      'is a real, gated example from the repo\'s `examples/` corpus — the shown ' +
      'output is read from its `expected.txt` at build time, so it cannot drift ' +
      'from what `bang run` actually produces.',
    '',
    'This is the v0, no-exec tour: read the code, read the expected output, ' +
      'then run it yourself locally (each lesson has a copy-paste command). ' +
      'An in-browser "edit and run" door is future work, not v0.',
    '',
  ]
  for (const lesson of lessons) {
    lines.push(
      `${lesson.number}. [${lesson.title}](${lesson.target.route}) — ${escapeProse(lesson.teaches)}`,
    )
  }
  lines.push('')
  return lines.join('\n')
}

const lessons = resolveTourContent(site, lessonContent)
const tourIndex = site.pages.find((page) => page.target.kind === 'tour-index')
if (!tourIndex) throw new Error('gen-tour: page manifest has no tour-index page')

const tourDir = join(pagesDir, 'tour')
rmSync(tourDir, { recursive: true, force: true })
mkdirSync(tourDir, { recursive: true })

function writeRoute(route, text) {
  const emitted = site.routeToPage.get(route)
  if (!emitted) throw new Error(`gen-tour: route is not emitted by the site model: ${route}`)
  const destination = join(pagesDir, emitted.outputPath)
  mkdirSync(dirname(destination), { recursive: true })
  writeFileSync(destination, text)
}

writeRoute(tourIndex.target.route, renderIndex(lessons))
for (let index = 0; index < lessons.length; index += 1) {
  writeRoute(
    lessons[index].target.route,
    renderLesson(lessons[index], lessons[index - 1], lessons[index + 1]),
  )
}

console.log(`gen-tour: ${lessons.length} manifest-ordered lessons generated under src/pages/tour`)
