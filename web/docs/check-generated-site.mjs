import { readFileSync, readdirSync } from 'node:fs'
import { dirname, join, relative, sep } from 'node:path'
import { fileURLToPath } from 'node:url'
import { compileSite } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const pagesDir = join(siteDir, 'src', 'pages')
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot,
})

function generatedMarkdown(root) {
  const files = []
  function walk(directory) {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const path = join(directory, entry.name)
      if (entry.isDirectory()) walk(path)
      else if (entry.isFile() && entry.name.endsWith('.md')) {
        files.push(relative(root, path).split(sep).join('/'))
      }
    }
  }
  walk(root)
  return files.sort()
}

const expected = site.emittedPages.map((page) => page.outputPath).sort()
const actual = generatedMarkdown(pagesDir)
const missing = expected.filter((path) => !actual.includes(path))
const extra = actual.filter((path) => !expected.includes(path))
if (missing.length > 0 || extra.length > 0) {
  throw new Error(
    `generated page inventory differs from the site model\n` +
    `missing: ${missing.join(', ') || 'none'}\nextra: ${extra.join(', ') || 'none'}`,
  )
}

let linkCount = 0
for (const outputPath of actual) {
  const markdown = readFileSync(join(pagesDir, outputPath), 'utf8')
  for (const match of markdown.matchAll(/(!?)\[[^\]]*\]\((\/[^)\s#]+)(?:#[^)]*)?\)/g)) {
    if (match[1] === '!') continue
    const route = match[2]
    if (route === site.basePath || route.startsWith(`${site.basePath}/`)) {
      throw new Error(`generated page link contains deploy basePath: ${outputPath} -> ${route}`)
    }
    if (!site.routeToPage.has(route)) {
      throw new Error(`generated page links to a route outside the site model: ${outputPath} -> ${route}`)
    }
    linkCount += 1
  }
}

console.log(
  `generated-site: PASS — ${actual.length} pages exactly match the model · ` +
  `${linkCount} internal route links resolve`,
)
