// Vocs 2.3.3 emits each accessibility skip-link without basePath (for example
// `/#vocs-content` and `/reference/language#vocs-content`). Repair those
// generated attributes after build; site-smoke.mjs checks every emitted page.
import { readFileSync, readdirSync, writeFileSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { compileSite } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const repoRoot = join(siteDir, '..', '..')
const publicDir = join(siteDir, 'dist', 'public')
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot,
})

let replacementCount = 0
function walk(directory) {
  for (const entry of readdirSync(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name)
    if (entry.isDirectory()) walk(path)
    else if (entry.isFile() && entry.name.endsWith('.html')) {
      const before = readFileSync(path, 'utf8')
      const after = before.replace(
        /href\s*=\s*(["'])(\/[^"']*#vocs-content)\1/g,
        (match, quote, href) => {
          if (href === site.basePath || href.startsWith(`${site.basePath}/`)) return match
          replacementCount += 1
          return `href=${quote}${site.basePath}${href}${quote}`
        },
      )
      for (const match of after.matchAll(/href\s*=\s*(["'])(\/[^"']*#vocs-content)\1/g)) {
        const href = match[2]
        if (href !== site.basePath && !href.startsWith(`${site.basePath}/`)) {
          throw new Error(`fix-vocs-basepath: unrepaired skip-link escape in ${path}: ${href}`)
        }
      }
      if (after !== before) writeFileSync(path, after)
    }
  }
}
walk(publicDir)
console.log(`fix-vocs-basepath: ${replacementCount} skip-link escape(s) repaired`)
