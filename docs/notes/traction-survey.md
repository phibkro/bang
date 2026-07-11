<!-- note-status: active -->
# Traction survey — how new-age languages got adopted, mapped to a bang plan

> Research survey (operator-posed 2026-07-11): how Zig/Rust/Gleam/Elixir + peers actually
> got traction, and the ordered content/community backlog it implies for bang. Traction claims
> are web-sourced (citations §6); bang-state claims are repo-cited. Docs-only.

## 1. The census

Each language: **wedge** (the concrete thing that made people care) · **first external
artifact + its maturity** · **content mechanics** (who made the numbers-moving content — team or
community) · **one transferable lesson**.

| lang | the wedge | first external artifact @ maturity | content mechanics | one lesson |
|---|---|---|---|---|
| **Zig** | "better C" (comptime, no hidden control flow, C interop) — *then* Bun as the proof-of-capability | Andrew Kelley's talks + the pre-1.0 compiler devs kept trying despite "the compiler broke all the time"; the *breakout* was **Bun (2021)**, written in Zig, at pre-1.0 Zig | Bun's own launch (a benchmark video, ~10× claims) pulled Zig along; a streamer/creator ecosystem, not a single team channel. Still pre-1.0 in 2026 yet hit TIOBE top-10 | A **killer OSS app in your language** (Bun) beats any first-party marketing — but you can't schedule it; you make the language good enough that someone builds it |
| **Rust** | **memory safety without GC** (the borrow checker), proven by **Servo** (a real parallel browser engine Mozilla funded 2012–2020) | Servo as the flagship testbed; the RFC process + a code-of-conduct culture pre-1.0; **1.0 only in May 2015**, ~9 yrs after Graydon started, ~6 yrs after Mozilla | Community-made: **No Boilerplate** (Tris Oaten, compile-checked-markdown Rust videos), **Fireship** "Rust in 100s", **This Week in Rust** (volunteer, since 2014). Team ran the RFC + blog cadence; community ran the hype | **Stability before the crowd.** Rust let janky demos leak for years but gated *1.0* hard; the friendly-community + RFC culture was as load-bearing as the tech |
| **Gleam** | **static types on the BEAM** + a surface "learnable in an afternoon"; friendly mascot/DX | created 2016 as a **conference-talk hobby project**; slow burn to **v1.0 (Mar 2024)**; hit **#1 trending on GitHub** at the v1.0 moment | Louis Pilfold's **personal presence** (talks, Changelog #588, Serokell interview) + **Gleam Weekly** (community newsletter) + an active Discord. Solo-author-led, community-amplified | **The author IS the early channel.** A solo/tiny-team language grows on the founder's visible, consistent presence — not a media team. Survey showed adopters came from *outside* Erlang/Elixir |
| **Elixir** | **Ruby-grade DX on Erlang's concurrency**, then **Phoenix + LiveView** as the app-shaped reason | José Valim (Rails core alum) → instant credibility with the **Rails diaspora**; Phoenix Channels/LiveView were the "first to fully use the platform" hook | Valim's standing + Dashbit's blog cadence; a framework (Phoenix) as the content magnet, conf talks | **Borrow an existing diaspora.** Elixir didn't build an audience cold — it captured disillusioned Rubyists with a familiar author and syntax |
| **Roc** | fast+friendly functional; **platforms/effects-as-data** design novelty | Richard Feldman (author of *Elm in Action*) — audience carried from Elm; ~2018 dev start, **still pre-1.0** in 2026; a Roc Foundation (nonprofit) ~2022 | Feldman's talks are the engine ("Outperforming Imperative with Pure Functional") — design-deep-dive content, not release notes | **Design-deep-dive talks travel** even pre-1.0 — if the design is genuinely novel, the *idea* is the content |
| **Odin** | pragmatic "joy of C without the footguns"; *no* killer feature by design | gingerBill's blog + steady releases; game-dev niche (used in shipped tools) | Author's "hot takes" as **accidental marketing**; deliberately anti-hype | **Slow-and-loyal can be the strategy.** Odin explicitly rejects hype: "steady, stable, slow growth" + users who stay. Non-evangelists aren't a bug |
| **Crystal** | Ruby syntax, native speed | Manas (Ruby consultancy) internal, 2011; a **2017 TIOBE spike (60→32)** from creator marketing + Ruby interest — **that spike didn't last** | Creator-driven marketing burst | **A hype spike without the ecosystem underneath decays.** Crystal's jump reverted; a package manager + real apps are what a must-have wide adoption needs |

**Cross-cutting infrastructure timeline pattern** (what every survivor eventually had): (a) online
playground → (b) a docs site → (c) a **package manager/registry** (repeatedly named the *must-have*
for wide adoption) → (d) a chat home (Discord/Zulip) + CoC → (e) a "This Week in X" newsletter
(often community-run) → (f) conf talks → own conf → (g) a foundation/sponsorship model (late) → (h)
the killer OSS app (Bun/Servo/Phoenix — the un-schedulable one).

## 2. The Diataxis mapping for bang (what EXISTS vs gaps)

Diataxis = four quadrants: **tutorials** (learning-oriented) · **how-to** (task-oriented) ·
**explanation** (understanding-oriented) · **reference** (information-oriented).

| quadrant | bang state today | verdict |
|---|---|---|
| **Reference** | `docs/reference/language.md` (1083 lines, **generated** from parser tables — cannot drift), the ADR ledger (`docs/decisions/README.md`, generated), the glossary in CLAUDE.md, the generated bang TextMate grammar. | **STRONGEST.** This is the moat quadrant: "docs that cannot lie" (build-gated, SSoT-derived). Lead with it. |
| **Explanation** | Extremely deep, but **agent-facing not human-facing**: the R-series surveys (`refinement-types-survey`, `lambda-cube-ascent-survey`, `kernel-substrate-survey`, `memory-management-survey`, `os-inspiration-survey`, …), ADRs, `PRD.md`, `categorical-architecture.md`. | **RICH RAW MATERIAL, WRONG ALTITUDE.** These are internal design notes, not public explainers. The gap is *translation*, not authoring-from-scratch. |
| **How-to** | Thin: `ONBOARDING.md`, `CONTRIBUTING.md`, 36 `examples/` (caesar, json, tokenizer, nqueens, stm, parser-combinators…). Examples show *what runs*, not "how do I do X". | **GAP.** The stranger tests (8.5/7/7) already probe this loop; task-shaped guides ("write a State handler", "add a verified law") are missing. |
| **Tutorials** | Essentially absent as a guided learning path. Examples ≠ tutorials (no narrative scaffolding). | **BIGGEST GAP.** No "clone → first program → you get it" path. The stranger-test journey (clone→cipher in 8 min) is the *seed* of the first tutorial. |

The generated-reference strength is unusual and defensible; the two weak quadrants (tutorials,
how-to) are exactly what the **weakest feedback loop — organic outside users** (`loop-audit.md`:
◑ OPEN, stranger-test plateau at 7/10, named 2 consecutive ◊) needs fed. Content that grows those
quadrants IS the outer-loop instrument.

## 3. The prioritized traction backlog (ordered)

Ordered by (feeds-the-weak-loop × cheap × unblocked). Each: effort · loop it feeds · depends-on.

1. **Ship the site as it stands, on the first public tag.** `site/` (vocs+waku, `phibkro.github.io/bang/`) already renders the generated reference + curated sidebar; v0.1.0 is tagged (`bbca771`). *Effort: S (exists, needs deploy verify). Feeds: outside-user loop opens. Depends: nothing — unblock now.*
2. **One real tutorial: the stranger journey, written down.** "Clone → Caesar cipher in 8 min", the exact path stranger-tests already validate. *Effort: S. Feeds: tutorial quadrant (biggest gap) + stranger loop. Depends: #1.*
3. **The announcement post + one asciinema/gif.** The honest hook is unique (§4): zero-training-data, agent-built, build-gated docs. Issue #70 already scopes this. *Effort: S. Feeds: first HN/lobsters surface. Depends: #1, #2.*
4. **3 design-deep-dive explainer posts from the R-series** (translate, don't author): the strongest three as-is are **(a)** "docs that cannot lie" (generated-reference + axiom gate), **(b)** deterministic-replay-by-default (ADR-0101 — the seeded sim-scheduler is the default runtime; nondeterminism is opt-in handler-swap), **(c)** "paradigms are values" (State one-effect/two-handlers, the moat §2). *Effort: M each. Feeds: explanation quadrant + HN design-deep-dive pattern (what worked for Roc/Rust, NOT release notes). Depends: #1.*
5. **A browser playground — but only rung-1 honestly.** Rungs 1 emits pure ⊥-row arithmetic to `.wat` running on wasmtime (`emit-rung1-diff.sh`, `emission-rung1-probe.md`); rungs 2-3 are demonstrated in the Lean harness, **not yet browser-runnable**. A playground that runs only the pure fragment is honest and still a strong "try it now"; do NOT claim full-language. *Effort: M–L. Feeds: try-it loop (Rust/Zig playgrounds were early wins). Depends: emission arc maturity — assess before promising.*
6. **Chat home (Discord or Zulip) + a code-of-conduct.** Rust's friendly-community culture was load-bearing. Zulip suits a proof-heavy audience (threaded). *Effort: S to stand up, ongoing to moderate. Feeds: community loop. Depends: #3 (need arrivals first).*
7. **Founder-presence cadence: one post/thread per ◊ tag.** Gleam's #1 lesson — the author is the channel. The PUBLIC-EARLY policy (every ◊ ships v0.x) already generates the cadence hooks. *Effort: S recurring. Feeds: all outer loops. Depends: #1.*
8. **How-to guides for the top 3 stranger-test asks** (wildcard arms #101, multi-op effects #86, module shapes). Task-shaped, fed by real friction. *Effort: M. Feeds: how-to quadrant + retention. Depends: the fixes landing.*
9. **Package-registry design sketch (not build).** Named the *must-have* for wide adoption across the census, but **v1 non-goal** (PRD §10). Sketch the shape so the surface doesn't foreclose it; defer the build. *Effort: S (design only). Feeds: nothing yet — insurance. Depends: post-v1.*
10. **A "This Week in bang" / changelog-digest — only once there's a community to write it.** Rust's TWiR was volunteer-run and *followed* the crowd. Don't front-run it. *Effort: S. Feeds: community loop. Depends: #6 producing contributors.*

**Media-team timing verdict:** **NOT YET — and the census says don't.** For a solo-operator
project, Gleam/Odin/Roc all grew on **founder presence + community-amplified content**, never a
first-party media team pre-1.0. A media team is item ~15, post-v1, after the killer-app or a
sustained inbound. Premature media-team spend is the Crystal-spike failure mode: hype without the
ecosystem underneath decays. The operator IS the media team until the loop pulls.

## 4. The wedge recommendation — lead with ONE differentiator

**Lead with "docs that cannot lie" — the verified-kernel + build-gated-generated-reference story.**

Why this one over the alternatives:
- It is bang's **strongest quadrant already shipped** (§2), not a promise. Rust/Gleam/Elixir all
  led with a wedge that was *real at first contact* (Servo ran; types-on-BEAM compiled). bang's
  proof-by-construction moat (PRD §2) is the *north star but least-built* — leading with it is
  the Crystal trap (claim > substance). The generated-reference + axiom gate is **demonstrable today**.
- It compounds with the genuinely novel positioning: **"a language safe to generate into"** (PRD §3)
  — built BY agent teams, zero-training-data, the stranger-test as proof. Nobody else has that story
  (issue #70 names it). The verified substrate is what makes "safe to generate into" true rather than
  asserted.
- Deterministic-replay-by-default (ADR-0101) is the **strong second beat**, not the lead — it's a
  runtime property, most compelling *after* the reader accepts the verified-substrate frame.

One-line pitch to test: *"bang is a verified language whose docs are generated from the proof — so
they can't drift — and it's designed to be safe for an AI to write."*

## 5. Anti-pattern warnings, applied to bang

- **Don't lead with the moat you haven't built.** Proof-by-construction is the north star (PRD §2)
  but "least-built" — leading marketing on it repeats Crystal's substance-gap spike. Lead with the
  shipped generated-reference; let the moat be the roadmap.
- **Don't stand up a media team / sponsor a conf pre-1.0.** Census-wide anti-pattern (Odin's whole
  thesis). Founder presence first; media team is a lagging indicator of traction, not a leading one.
- **Don't over-claim the playground.** Only rung-1 (pure arithmetic) is browser-runnable honestly.
  A "try the full language" playground that stubs the hard part is the green-stub lie in marketing
  form — and this audience (proof people) will catch it.
- **Don't front-run the newsletter/registry.** TWiR followed the crowd; registries are the must-have
  *at scale*, a v1 non-goal now. Building them before there's demand is docs-before-stability effort.
- **Don't post release notes to HN.** The pattern that moved numbers (Roc, Rust) was **design
  deep-dives**, not changelogs. bang's R-series is a deep-dive goldmine — translate those.
- **Stability gates the crowd (Rust's lesson).** Public-early (every ◊ = v0.x tag) is right for
  *exposure*, but the loud push (HN launch) should ride a tag you'd stand behind — don't invite the
  crowd onto a compiler that "breaks all the time" without saying so.

## 6. Citations

Traction claims (web, verified 2026-07-11): Zig/Bun — [Wikipedia: Zig](https://en.wikipedia.org/wiki/Zig_(programming_language)), [Bun: lessons from disrupting (Pragmatic Engineer)](https://blog.pragmaticengineer.com/bun-lessons-from-disrupting/), [Wikipedia: Bun](https://en.wikipedia.org/wiki/Bun_(software)). Rust — [Wikipedia: Rust](https://en.wikipedia.org/wiki/Rust_(programming_language)), [MIT Tech Review: how Rust went from side project](https://www.technologyreview.com/2023/02/14/1067869/rust-worlds-fastest-growing-programming-language/), [10 Years of Stable Rust (Rust Foundation)](https://rustfoundation.org/media/10-years-of-stable-rust-an-infrastructure-story/), [This Week in Rust](https://this-week-in-rust.org/), [No Boilerplate](https://www.youtube.com/@NoBoilerplate). Gleam — [Wikipedia: Gleam](https://en.wikipedia.org/wiki/Gleam_(programming_language)), [Gleam 2024 Developer Survey](https://gleam.run/news/developer-survey-2024-results/), [Serokell interview with Louis Pilfold](https://serokell.io/blog/interview-with-louis-pilfold), [Changelog #588](https://changelog.com/podcast/588), [Gleam Weekly](https://gleamweekly.com/). Elixir — [Ten years-ish of Elixir (Dashbit)](https://dashbit.co/blog/ten-years-ish-of-elixir). Roc — [roc-lang.org](https://www.roc-lang.org/), [roc GitHub](https://github.com/roc-lang/roc). Odin — [Marketing the Odin Language is Weird (gingerBill)](https://www.gingerbill.org/article/2024/09/08/odin-weird-to-market/). Crystal — [HN: A look at Crystal](https://news.ycombinator.com/item?id=35811879), [Crystal 2026 overview](https://www.programming-helper.com/tech/crystal-programming-language-2026).

bang-state claims (repo, this branch @ e21777fe): `docs/PRD.md` §2–§3 (moat, agent-first), `docs/notes/loop-audit.md` (weakest loop = organic outside user), `docs/decisions/0101-concurrency-model-scheduler-as-handler.md` (deterministic-replay default), `docs/reference/language.md` (1083-line generated reference), `docs/notes/emission-rung1-probe.md` (rung-1 wasm on wasmtime), `site/vocs.config.ts` (existing docs site), `examples/` (36 projects), issue #70 (website+media backlog).
