import { defineConfig } from 'vocs/config'

// Live subpath deploy target: https://phibkro.github.io/bang/
// basePath makes every asset URL resolve under /bang/ (Vocs URLs-and-Deployment).
export default defineConfig({
  title: 'BANG',
  description:
    'A small language whose paradigm and runtime are values, not language features.',
  basePath: '/bang',
  // GitHub Pages is a static-only host: emit plain HTML/JS/CSS (no server runtime).
  renderStrategy: 'full-static',
  // Our repo markdown uses GitHub-style relative `*.md` links; Vocs routes drop
  // the `.md`, so its dead-link check flags them. Warn (don't fail) — a rewrite
  // pass in sync-docs.mjs could make them extensionless later.
  checkDeadlinks: 'warn',
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
