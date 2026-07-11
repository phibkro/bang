import { defineConfig } from 'vocs/config'
import bangGrammar from './bang.tmLanguage.json' with { type: 'json' }

// Live subpath deploy target: https://phibkro.github.io/bang/
// basePath makes every asset URL resolve under /bang/ (Vocs URLs-and-Deployment).
export default defineConfig({
  title: 'BANG',
  description:
    'A small language whose paradigm and runtime are values, not language features.',
  basePath: '/bang',
  // GitHub Pages is a static-only host: emit plain HTML/JS/CSS (no server runtime).
  renderStrategy: 'full-static',
  // Register the GENERATED bang TextMate grammar with Shiki (vocs passes
  // codeHighlight.langs straight through to rehype-shiki — verified empirically,
  // vocs 2.3.3 `internal/config.js`). `name: 'bang'` is the fence-infostring id, so
  // ```bang blocks highlight instead of degrading to plain text. The grammar is
  // tools/gen-tmgrammar.py's committed output (derived from the reified parser
  // tables), so highlighting cannot drift from what the parser recognises.
  codeHighlight: {
    langs: [{ ...bangGrammar, name: 'bang' }],
  },
  // sync-docs.mjs rewrites relative `*.md` links to extensionless + flattens
  // [[wikilinks]], so most now resolve as Vocs routes. Kept at 'warn': some
  // cross-doc question links (e.g. the OPEN_QUESTIONS ties) route through
  // subdirs that don't fully resolve — not worth failing the build over.
  checkDeadlinks: 'warn',
  // Cross-link to the progress dashboard (a static page merged in by CI at
  // /bang/dashboard/ — outside Vocs's routes, so a full-URL external link).
  topNav: [{ text: 'Dashboard ↗', link: 'https://phibkro.github.io/bang/dashboard/' }],
  // Sidebar is hand-curated (mirrors CLAUDE.md reference index). Pages
  // themselves are symlinks to the repo's real markdown (see sync-docs.mjs).
  sidebar: [
    {
      text: 'Start here',
      items: [
        { text: 'What BANG is (README)', link: '/' },
        { text: 'Onboarding', link: '/ONBOARDING' },
        { text: 'Contributing', link: '/CONTRIBUTING' },
        { text: 'Current position (CONTEXT)', link: '/CONTEXT' },
        { text: 'Roadmap', link: '/ROADMAP' },
        { text: 'Agent guide (CLAUDE)', link: '/CLAUDE' },
      ],
    },
    {
      text: 'Reference',
      items: [
        { text: 'Language reference', link: '/reference/language' },
        { text: 'Product definition (PRD)', link: '/PRD' },
        { text: 'Changelog', link: '/CHANGELOG' },
      ],
    },
    {
      text: 'Architecture — ADRs',
      collapsed: true,
      items: [
        { text: 'ADR index', link: '/decisions/README' },
        { text: '0016 — Two-hop architecture', link: '/decisions/0016-two-hop-architecture-calcvm-and-wasmfx' },
      ],
    },
    {
      text: 'Design notes',
      collapsed: true,
      items: [
        { text: 'Notes index', link: '/notes/README' },
        { text: 'Open questions', link: '/notes/OPEN_QUESTIONS' },
        { text: 'Design-space map', link: '/notes/design-space-map' },
        { text: 'Stdlib map', link: '/notes/stdlib-map' },
      ],
    },
    {
      text: 'Long-range roadmap',
      collapsed: true,
      items: [
        { text: 'Project roadmap', link: '/roadmap/project-roadmap' },
        { text: 'Northstar roadmap', link: '/roadmap/bang-northstar-roadmap' },
      ],
    },
  ],
})
