# web/landing — the marketing/landing page (stub)

**Status: not built.** This directory is a reserved slot in the `web/` bundle
(operator decision, 2026-07-11: every web-facing project lives under `web/`).
Building the landing page itself is a FUTURE lane — this README only fixes the
directory contract so the slot exists and its shape is agreed.

## What goes here

The public landing page for BANG — the top-of-funnel marketing surface a
stranger hits before the docs. It is a SEPARATE app from `web/docs/`:

| | `web/docs/` | `web/landing/` (this slot) |
|---|---|---|
| what | the vocs + waku documentation site | the marketing landing page |
| source of truth | the repo's markdown (synced by `sync-docs.mjs`) | its own hand-authored content |
| deploy target | GitHub Pages `/bang/` | TBD (own lane) |
| status | shipped | not started |

## Contract for whoever builds it

- **Own workspace, not a shared monorepo.** `web/docs/` is a self-contained bun
  app (its own `package.json` + `bun.lock`, no root workspace file). Follow the
  same pattern: `web/landing/` gets its OWN lockfile and node config. The two
  apps are independent — do not couple them into one workspace unless a concrete
  shared-dependency need appears (it does not today).
- **Its own CI workflow.** Mirror `.github/workflows/site.yml` (a build-only
  PR-validation job scoped to `web/landing/**`); do not fold it into the docs
  workflow.
- **Deploy target is an open question** — GitHub Pages already serves the docs
  at `/bang/`; the landing page's URL/host is for the building lane to decide.
