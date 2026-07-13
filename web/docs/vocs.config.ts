import { defineConfig } from 'vocs/config'
import bangGrammar from './bang.tmLanguage.json' with { type: 'json' }
import { lessons } from './tour-manifest.mjs'

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
  // Stable public learning/contributor routes. Volatile CONTEXT/active-path state
  // stays repository-local by ADR-0108 (enforced by sync-docs.mjs's source map).
  sidebar: [
    {
      text: 'Start',
      items: [
        { text: 'What BANG is', link: '/' },
        { text: 'Contributor quickstart', link: '/ONBOARDING' },
      ],
    },
    {
      // Generated FROM tour-manifest.mjs (the SSoT for lesson order/titles) —
      // never hand-duplicated, so the sidebar cannot drift from gen-tour.mjs's
      // own page list.
      text: 'Learn',
      items: [
        { text: 'Guided tour', link: '/tour' },
        ...lessons.map((l) => ({ text: `${l.n}. ${l.title}`, link: `/tour/${l.slug}` })),
      ],
    },
    {
      text: 'Reference',
      items: [
        { text: 'Language and CLI', link: '/reference/language' },
        { text: 'Current architecture', link: '/architecture/core-overview' },
        { text: 'Product definition', link: '/PRD' },
        { text: 'Changelog', link: '/CHANGELOG' },
      ],
    },
    {
      text: 'Contribute',
      items: [
        { text: 'Contribution workflow', link: '/CONTRIBUTING' },
        { text: 'Agent guide', link: '/CLAUDE' },
        { text: 'Decision index', link: '/decisions/README' },
      ],
    },
    {
      text: 'Architecture decisions',
      collapsed: true,
      items: [
        { text: '0016 — Two-hop architecture', link: '/decisions/0016-two-hop-architecture-calcvm-and-wasmfx' },
        { text: '0035 — Equivalence vs simulation', link: '/decisions/0035-lr-for-equivalence-simulation-for-compilation' },
        { text: '0059 — Wasm 3.0 target', link: '/decisions/0059-wasm3-grade-directed-pluggable-backend' },
      ],
    },
    {
      text: 'Advanced design',
      collapsed: true,
      items: [
        { text: 'Notes index', link: '/notes/README' },
        { text: 'Design-space map', link: '/notes/design-space-map' },
        { text: 'Stdlib map', link: '/notes/stdlib-map' },
      ],
    },
    {
      text: 'Roadmap',
      collapsed: true,
      items: [
        { text: 'Checkpoint map', link: '/ROADMAP' },
        { text: 'Project roadmap', link: '/roadmap/project-roadmap' },
        { text: 'Northstar roadmap', link: '/roadmap/bang-northstar-roadmap' },
      ],
    },
  ],
})
