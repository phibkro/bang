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
import { mkdirSync, rmSync, readFileSync, writeFileSync, readdirSync, statSync, mkdtempSync } from 'node:fs'
import { dirname, join, extname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { tmpdir } from 'node:os'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..')
const pagesDir = join(siteDir, 'src', 'pages')
// Pre-rendered mermaid SVGs land here; vite copies site/public → the site root,
// served under basePath. vocs does NOT rewrite markdown-image src with basePath
// (it does for links/its own assets), so we prepend it ourselves — read from the
// vocs config (single source of truth, no second copy of the deploy path).
const mermaidDir = join(siteDir, 'public', 'mermaid')
const basePath = (readFileSync(join(siteDir, 'vocs.config.ts'), 'utf8')
  .match(/basePath:\s*['"]([^'"]*)['"]/)?.[1]) ?? ''

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
      if (!inFence) {
        inFence = true; fenceTok = tok
        // Shiki hard-errors on fence languages not in its bundle — and `bang` (our own
        // language, ~200 fences across the docs) has no grammar yet. Alias the known
        // non-bundled infostrings to plain `text` AT THE SYNC SEAM (the repo markdown
        // stays `bang`-tagged — GitHub renders it; only the derived site copy degrades).
        // A real bang tmLanguage grammar is the follow-up that deletes this map.
        out.push(line.replace(/^(\s*(?:```+|~~~+))(bang|wat)\s*$/, '$1text'))
        continue
      }
      else if (tok === fenceTok) { inFence = false }
      out.push(line)
      continue
    }
    if (inFence) { out.push(line); continue }
    out.push(escapeProse(rewriteLinks(line)))
  }
  // Vocs's CLIENT mermaid component's render effect loops on our pages
  // (colorScheme-keyed useEffect → infinite re-render, the "reload" bug). Instead
  // of shipping the component, PRE-RENDER each ```mermaid fence to a static SVG at
  // build time (mmdc) written to public/mermaid, and embed it with a core-markdown
  // image `![](/mermaid/<hash>.svg)`. The diagram is DRAWN into the static HTML (no
  // client component, no loop), and it's regenerated from the mermaid source each
  // build so it can't drift (SSoT). Markdown-image (not a raw `<img>`) is required:
  // vocs runs no rehype-raw, so a raw HTML `<img>` node is dropped — a markdown
  // image is first-class and always renders. Run LAST, so the emitted `![](…)` line
  // is not touched by the escapeProse pass.
  return out.join('\n').replace(/```mermaid[^\n]*\n([\s\S]*?)```/g, (_m, code) => {
    const rel = renderMermaid(code)
    if (!rel) {
      return '> 📊 _Mermaid diagram omitted on the docs site — view it rendered in the repository source._'
    }
    return `![diagram](${rel})`
  })
}

// Render a mermaid source to an SVG under public/mermaid/<hash>.svg (hash of the
// source → stable name + dedup) and return its site-root path for a markdown image.
// mmdc is the mermaid-cli (dev shell / a site devDep). One fixed theme — a static
// SVG can't follow the site's dark/light toggle — so `default` + a white background
// reads legibly under BOTH modes (dark text on a white card). Returns null on
// failure so the caller falls back to the pointer note for just THAT diagram
// (never breaks the build).
function renderMermaid(code) {
  const hash = createHash('sha256').update(code).digest('hex').slice(0, 16)
  const dest = join(mermaidDir, `${hash}.svg`)
  mkdirSync(mermaidDir, { recursive: true })
  const d = mkdtempSync(join(tmpdir(), 'mmd-'))
  const mmd = join(d, 'g.mmd')
  const cfg = join(d, 'pptr.json')
  writeFileSync(mmd, code)
  writeFileSync(cfg, '{"args":["--no-sandbox","--disable-gpu"]}') // headless chromium in CI/sandbox
  try {
    execFileSync('mmdc', ['-i', mmd, '-o', dest, '-p', cfg, '-t', 'default', '-b', 'white'],
      { stdio: 'pipe', timeout: 180000 })
    return `${basePath}/mermaid/${hash}.svg`
  } catch (e) {
    console.warn(`sync-docs: mermaid render failed, falling back to pointer note: ${String(e.stderr || e.message).slice(-300)}`)
    return null
  } finally {
    rmSync(d, { recursive: true, force: true })
  }
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
// Reset the pre-rendered mermaid SVGs too, so a removed/edited diagram leaves no orphan.
rmSync(mermaidDir, { recursive: true, force: true })
for (const [page, src] of Object.entries(rootFiles)) {
  try { emit(join(repoRoot, src), join(pagesDir, page)) }
  catch { console.warn(`skip missing ${src}`) }
}
for (const [seg, src] of Object.entries(dirs)) {
  try { emitTree(join(repoRoot, src), join(pagesDir, seg)) }
  catch { console.warn(`skip missing ${src}`) }
}
console.log('sync-docs: MDX-safe pages generated under src/pages')
