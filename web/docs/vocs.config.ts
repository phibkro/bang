import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'
import { defineConfig } from 'vocs/config'
import bangGrammar from './bang.tmLanguage.json' with { type: 'json' }
import { compileSite } from './site-model.mjs'

const siteDir = dirname(fileURLToPath(import.meta.url))
const site = compileSite({
  manifestPath: join(siteDir, 'page-manifest.json'),
  repoRoot: join(siteDir, '..', '..'),
})

export default defineConfig({
  title: 'BANG',
  description:
    'A small language whose paradigm and runtime are values, not language features.',
  // The manifest is the single deploy-path and navigation authority (ADR-0109).
  basePath: site.basePath,
  renderStrategy: 'full-static',
  // The grammar is generated from reified parser tables by gen-tmgrammar.py.
  codeHighlight: {
    langs: [{ ...bangGrammar, name: 'bang' }],
  },
  // Vocs 2.3.3: true throws on dead links; 'warn' would produce a false green.
  checkDeadlinks: true,
  topNav: [{ text: 'Dashboard ↗', link: 'https://phibkro.github.io/bang/dashboard/' }],
  // Direct consumption makes a parallel hand-authored/generated sidebar impossible.
  sidebar: site.sidebar,
})
