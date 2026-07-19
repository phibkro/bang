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
import { cpSync, mkdirSync, rmSync, readFileSync, writeFileSync, mkdtempSync } from 'node:fs'
import { dirname, join, extname } from 'node:path'
import { fileURLToPath } from 'node:url'
import { tmpdir } from 'node:os'
import { execFileSync } from 'node:child_process'
import { createHash } from 'node:crypto'
import { escapeProse } from './mdx-safe.mjs'
import { compileSite, rewriteMarkdownLinks } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const pagesDir = join(siteDir, 'src', 'pages')
const mermaidDir = join(siteDir, 'public', 'mermaid')
const compiledDemoSource = join(siteDir, 'static', 'compiled-demos')
const compiledDemoDestination = join(siteDir, 'public', 'demos', 'compiled')
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot,
})
const basePath = site.basePath
const strictMermaid = process.env.BANG_SITE_STRICT_MERMAID === '1'
  || process.argv.includes('--strict-mermaid')

// --- MDX-safe transform -----------------------------------------------------
// Operate line-by-line, tracking fenced code blocks (``` / ~~~) where MDX does
// NOT parse JSX. Outside fences, protect inline-code spans (`...`) and escape the
// characters MDX treats as JSX/expression starts in the remaining prose.
function mdxSafe(src, sourcePath) {
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
        // Shiki hard-errors on fence languages not in its bundle. `bang` now HAS a
        // grammar (site/bang.tmLanguage.json, registered via vocs.config's
        // codeHighlight.langs — plan 013 slice 1), so `bang` fences highlight and are
        // no longer aliased. `wat` stays aliased to `text`: it is not in Shiki's default
        // bundle and some un-bundled wat fences remain (docs/notes/emission-rung1-probe.md).
        out.push(line.replace(/^(\s*(?:```+|~~~+))(wat)\s*$/, '$1text'))
        continue
      }
      else if (tok === fenceTok) { inFence = false }
      out.push(line)
      continue
    }
    if (inFence) { out.push(line); continue }
    out.push(escapeProse(rewriteMarkdownLinks({ line, site, repoRoot, sourcePath })))
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
// reads legibly under BOTH modes (dark text on a white card). Authoring sync/dev may
// fall back per diagram; production `build` is strict and fails before publishing.
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
    const detail = String(e.stderr || e.message).slice(-300)
    if (strictMermaid) {
      throw new Error(`sync-docs: strict Mermaid render failed for ${hash}: ${detail}`, { cause: e })
    }
    console.warn(`sync-docs: mermaid render failed for ${hash}, falling back to pointer note: ${detail}`)
    return null
  } finally {
    rmSync(d, { recursive: true, force: true })
  }
}

// --- emit -------------------------------------------------------------------
function emit(sourcePath, outputPath) {
  const ext = extname(sourcePath)
  if (ext !== '.md' && ext !== '.mdx') return
  const destination = join(pagesDir, outputPath)
  mkdirSync(dirname(destination), { recursive: true })
  writeFileSync(destination, mdxSafe(readFileSync(join(repoRoot, sourcePath), 'utf8'), sourcePath))
}

rmSync(pagesDir, { recursive: true, force: true })
mkdirSync(pagesDir, { recursive: true })
rmSync(mermaidDir, { recursive: true, force: true })
rmSync(compiledDemoDestination, { recursive: true, force: true })
cpSync(compiledDemoSource, compiledDemoDestination, { recursive: true })
const publicationPages = site.emittedPages.filter((page) => !page.source.startsWith('@'))
for (const page of publicationPages) emit(page.source, page.outputPath)
console.log(
  `sync-docs: ${publicationPages.length} manifest-selected MDX-safe pages generated`,
)
