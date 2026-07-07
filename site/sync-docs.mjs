// SSoT bridge (GENERATE rung): the repo's markdown is the single source of
// truth (ADR-0077/0078). Vocs compiles every page through the MDX-jsx pipeline,
// which rejects raw GitHub-flavored markdown (HTML comments `<!-- -->`, bare `<`
// and `{` in prose — pervasive in our Lean snippets / type sigs / generated-file
// banners). So we cannot symlink the raw files; instead we DERIVE MDX-safe copies
// on every build. These live under src/pages (gitignored build artifacts), are
// never hand-edited, and are regenerated from the root each run — so they cannot
// drift from the source (top rung of the SSoT ladder).
//
// Route map (Vocs file-based routing over src/pages):
//   README.md    -> index.md            => /
//   <NAME>.md    -> <name>.md  (root)   => /<name>
//   docs/<dir>/* -> <dir>/*             => /<dir>/<file>
import { mkdirSync, rmSync, readFileSync, writeFileSync, readdirSync, statSync } from 'node:fs'
import { dirname, join, extname } from 'node:path'
import { fileURLToPath } from 'node:url'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..')
const pagesDir = join(siteDir, 'src', 'pages')

const rootFiles = {
  'index.md': 'README.md',
  'ONBOARDING.md': 'ONBOARDING.md',
  'CONTRIBUTING.md': 'CONTRIBUTING.md',
  'CONTEXT.md': 'CONTEXT.md',
  'ROADMAP.md': 'ROADMAP.md',
  'CLAUDE.md': 'CLAUDE.md',
  'CHANGELOG.md': 'CHANGELOG.md',
  'PRD.md': 'docs/PRD.md',
}
const dirs = {
  reference: 'docs/reference',
  decisions: 'docs/decisions',
  notes: 'docs/notes',
  roadmap: 'docs/roadmap',
  architecture: 'docs/architecture',
  spec: 'docs/spec',
}

// --- MDX-safe transform -----------------------------------------------------
// Operate line-by-line, tracking fenced code blocks (``` / ~~~) where MDX does
// NOT parse JSX. Outside fences, protect inline-code spans (`...`) and escape the
// characters MDX treats as JSX/expression starts in the remaining prose.
function mdxSafe(src) {
  // Drop HTML comments everywhere (MDX has no `<!-- -->`); they're doc-internal.
  src = src.replace(/<!--[\s\S]*?-->/g, '')
  // Flatten [[wikilinks]] -> plain text (whole-text: they wrap across lines in our
  // prose). Ours point at auto-memory slugs, not site pages, so they'd be dead links.
  src = src.replace(/\[\[([^\]]+?)\]\]/g, '$1')
  const out = []
  let inFence = false
  let fenceTok = ''
  for (const line of src.split('\n')) {
    const fenceMatch = line.match(/^\s*(```+|~~~+)/)
    if (fenceMatch) {
      const tok = fenceMatch[1][0]
      if (!inFence) { inFence = true; fenceTok = tok }
      else if (tok === fenceTok) { inFence = false }
      out.push(line)
      continue
    }
    if (inFence) { out.push(line); continue }
    out.push(escapeProse(rewriteLinks(line)))
  }
  return out.join('\n')
}

// Rewrite for Vocs routing: relative `*.md` links -> extensionless (Vocs drops the
// `.md` from routes, so `[x](foo.md)` would 404 — `[x](foo)` resolves). Skip external
// (`http`) and pure-anchor (`#`) targets. ([[wikilinks]] are flattened globally in
// mdxSafe, since they wrap across lines.)
function rewriteLinks(line) {
  return line.replace(/\]\((?!https?:|#)([^)]+?)\.md(#[^)]*)?\)/g, ']($1$2)')
}

// Escape MDX's JSX/expression triggers (`<`, `{`). MDX does NOT parse JSX inside
// an inline-code span — EXCEPT a GFM table splits `code | with a pipe`, breaking
// the span and exposing a `<;>` (Lean combinator) to the parser. So: escape in
// prose always; inside a code span only when it holds a `|` (the break risk).
// Everywhere else the code span is left verbatim, so `Foo<Bar>` still displays.
const esc = (s) => s.replace(/</g, '&lt;').replace(/\{/g, '&#123;')
function escapeProse(line) {
  return line
    .split(/(`+[^`]*`+)/) // odd indices are inline-code spans
    .map((seg, i) =>
      i % 2 === 0 ? esc(seg) : seg.includes('|') ? esc(seg) : seg,
    )
    .join('')
}

// --- emit -------------------------------------------------------------------
function emit(srcAbs, destAbs) {
  const ext = extname(srcAbs)
  if (ext !== '.md' && ext !== '.mdx') return
  mkdirSync(dirname(destAbs), { recursive: true })
  writeFileSync(destAbs.replace(/\.mdx$/, '.md'), mdxSafe(readFileSync(srcAbs, 'utf8')))
}

function emitTree(srcDir, destDir) {
  for (const name of readdirSync(srcDir)) {
    const s = join(srcDir, name)
    const d = join(destDir, name)
    if (statSync(s).isDirectory()) emitTree(s, d)
    else emit(s, d)
  }
}

rmSync(pagesDir, { recursive: true, force: true })
mkdirSync(pagesDir, { recursive: true })
for (const [page, src] of Object.entries(rootFiles)) {
  try { emit(join(repoRoot, src), join(pagesDir, page)) }
  catch { console.warn(`skip missing ${src}`) }
}
for (const [seg, src] of Object.entries(dirs)) {
  try { emitTree(join(repoRoot, src), join(pagesDir, seg)) }
  catch { console.warn(`skip missing ${src}`) }
}
console.log('sync-docs: MDX-safe pages generated under src/pages')
