# web/landing — the bang marketing landing page

The public landing page for BANG — the top-of-funnel surface a stranger hits
before the docs. A SEPARATE app from [`../docs/`](../docs/) (the `web/` bundle
contract, [`../README.md`](../README.md)): its own directory, its own scripts, no
shared workspace.

**Status:** a reviewable draft (not deployed). One self-contained static page.

## Run it

```bash
cd web/landing
npm run serve      # python3 -m http.server 4321  → open http://localhost:4321
npm run build      # validate + stage assets to dist/ (CI-checkable)
```

No install step, no dependencies — the page is plain HTML/CSS/JS. `npm run build`
runs [`build.mjs`](build.mjs), which asserts the three assets exist and stages
them to `dist/` (exits non-zero on a missing asset, so CI catches a broken page).

## Stack choice — static single page, zero framework

The sibling [`../docs/`](../docs/) uses vocs + waku because it *generates many
pages* from the repo's markdown. This page is *one hand-authored page*; that
machinery is the wrong construct here (one construct per problem). The lightest
thing that fits the design values — fast, no bloat, accessible, dark-mode aware —
is a single `index.html` with one stylesheet and one small script:

| | why |
|---|---|
| **no framework / no bundler** | one page has nothing to bundle; a framework would add build time + JS weight for zero benefit (design value: "no framework bloat for one page") |
| **hand-tinted syntax** (spans in the HTML) | the alternative — a build-time highlighter fed [`../docs/bang.tmLanguage.json`](../docs/bang.tmLanguage.json) — reintroduces exactly the build dependency this page avoids, to color ~14 lines. Hand tinting is cheaper and ships zero JS. |
| **JS only for the copy button** | the page is fully usable with JS off (the install command is selectable text); the script only adds the one-click copy affordance |

The page owns its `package.json` (its own scripts, no lockfile needed since it has
no deps) per the `web/` independent-app contract.

## The page (top to bottom)

1. **Hero** — the tagline, the three subclaims, two CTAs (Install one-liner in a
   copy-block; "Take the tour" → `./tour/`, a sibling lane that may 404 until both
   deploy).
2. **The code moment** — the `logger-silent` / `logger-counting` pair side by
   side: the *identical* program, the one differing handler clause highlighted,
   outputs `0` vs `3`.
3. **The honesty strip** — the verified-core / tested-superset seam as a two-band
   diagram, plus the required "v0.x — not production-ready" line.
4. **Footer** — docs · tour · GitHub · the install line again.

## Every copy claim traces to the copy kit

The content is not invented here — it is *form given to* the ruled copy. Sources:

| on the page | source |
|---|---|
| tagline "The docs can't lie…" | [`../../docs/notes/copy-kit.md`](../../docs/notes/copy-kit.md) §1, candidate A (the ruled winner) |
| subhead + the three subclaims | [`../../docs/notes/copy-kit.md`](../../docs/notes/copy-kit.md) §2 |
| "the runtime is a value you install" caption | [`../../docs/notes/explainer-series.md`](../../docs/notes/explainer-series.md) E3 |
| the logger pair (same program, `=> 0` vs `=> 1`, `0` vs `3`) | [`../../examples/logger-silent/`](../../examples/logger-silent/) + [`../../examples/logger-counting/`](../../examples/logger-counting/) |
| the verified / tested band contents | [`../../docs/notes/copy-kit.md`](../../docs/notes/copy-kit.md) §4 Q4 |
| the "v0.x — not production-ready" line | [`../../docs/notes/copy-kit.md`](../../docs/notes/copy-kit.md) §5 (required by the anti-hype rules) |
| the install one-liner | [`../../README.md`](../../README.md) §Install |

### Anti-hype compliance (copy-kit §5 — a hard gate)

The page ships **none** of the forbidden claims: no browser-playground claim, no
"proof-by-construction today", no "production-ready / stable / 1.0", no closed
contextual-equivalence (LR) claim, no "deterministic concurrency today". The
deterministic-replay tagline (candidate C) is deliberately **omitted** — it is
gated behind post-v1 concurrency, so it does not appear.
