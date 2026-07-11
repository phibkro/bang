# web/ — the web-facing projects bundle

Every web-facing BANG project lives under `web/` (operator decision,
2026-07-11). Each subdirectory is an **independent app**, not a shared
monorepo workspace.

| dir | what | status |
|---|---|---|
| [`docs/`](docs/) | the vocs + waku documentation site → GitHub Pages `/bang/` | shipped |
| [`landing/`](landing/) | the marketing landing page | stub — future lane |

## Why two independent apps, not one workspace

`web/docs/` is a self-contained bun app: one `package.json`, one tracked
`bun.lock`, no root workspace file — it was built and shipped that way. Bundling
it and `web/landing/` into a single bun/npm workspace would buy shared hoisting,
but the two share no dependencies today and have different sources of truth (docs
is generated from the repo's markdown; landing is hand-authored) and different
deploy targets. A workspace is the wrong construct until a concrete shared-dep
need appears. So: **each app owns its lockfile and CI; `web/` is just the
namespace.** (One construct per problem — don't add a workspace layer no app
needs yet.)
