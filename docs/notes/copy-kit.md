<!-- note-status: active -->
# Copy kit — pitching bang accurately and hook-worthily

> The marketing-copy deliverable (operator-posed 2026-07-11): taglines · hero · pitches · skeptic
> FAQ · anti-hype rules, all grounded on the ruled wedge. **Every claim here is TRUE and cited** —
> `traction-survey.md` §4 ruled the wedge ("docs that cannot lie"); this file turns it into copy.
> Sibling: `explainer-series.md` (the multi-sensory series). Docs-only.
>
> Grounding: `traction-survey.md` §4 (wedge) · `PRD.md` §2–§3 (moat, agent-first) ·
> `docs/reference/language.md` (what's REAL) · ADR-0101 (deterministic replay) ·
> `stranger-test-{1,2,3}.md` (the HONEST current experience — copy must not pitch past it).

## 1 · The one-liner — 5 candidates, ranked

Each: the **claim** it makes · the **citation** that makes it true · the **hook mechanic**.
The rule (from the reference class): **specificity beats superlatives** — a checkable concrete
claim out-pulls "fast/safe/simple". Rust's early "fast, safe, concurrent — pick three" won by
naming the three, not by claiming greatness.

| # | tagline | claim | citation | hook mechanic |
|---|---|---|---|---|
| **A** ★ | **"The docs can't lie. They're generated from the proof."** | every reference example is build-gated; the reference is derived from the verified source, so it cannot drift | `docs/reference/language.md` header ("GENERATED … every example is a `#guard` gated by `lake build`"); ~90 gated examples (stranger-3 "what worked") | **specificity + mild taboo** ("lie" is a word no language site uses about its own docs) — provokes "wait, how?" |
| B | **"A language whose runtime is a value you swap."** | paradigm = the effect row, runtime = an installed handler; swap the handler, swap the behavior | `PRD.md` §2, invariant #3; `state` = one effect / two handlers (event-store vs in-place), `PRD.md` §6 | **concreteness of a familiar word made strange** ("runtime" as a value) — but abstract at first contact |
| C | **"Your concurrent program replays byte-for-byte — unless you opt out."** | the seeded sim-scheduler is the default concurrency runtime; nondeterminism is an explicit handler-swap | ADR-0101 G6 ("same seed ⇒ same interleaving ⇒ byte-identical output"; production nondeterminism is the opt-in) | **inverts the default everyone expects** (concurrency = nondeterministic) — strong, but concurrency is post-v1 (see §5) |
| D | **"A language that's safe to generate into."** | illegal states are unrepresentable structurally, not linted; the verified kernel enforces what the author (human or agent) might not | `PRD.md` §3; the moat §2; stranger-tests as agent-authored proof | **2026-native positioning** (AI codegen target) — the meta-hook, but a promise more than a demo today |
| E | **"One kernel. Every paradigm is a library."** | thunks + effects + handlers + STM; imperative/reactive/actor/transactional are ordinary library code | CLAUDE.md invariant #5, `PRD.md` §1 | **the classic "small core" flex** — true but crowded (many langs claim minimal cores) |

**Strongest: A — "The docs can't lie. They're generated from the proof."**

Why A over the rest:
- It leads with **the shipped, demonstrable strength** (stranger-3: ~90 gated examples pass; the
  reference is generated). Rust/Gleam/Elixir all led with a wedge *real at first contact*
  (`traction-survey.md` §4). B/C/D are truer to the *moat* but less-built — leading on them is the
  Crystal trap (claim > substance, `traction-survey.md` §5).
- **"Lie" is the hook.** Every other language's docs *can* drift and everyone who has been burned
  by stale docs knows it. Naming the universal pain and claiming structural immunity is specific,
  falsifiable, and slightly transgressive — the three ingredients of a hook that travels.
- It **compounds into D** (the agent-first meta-story): docs-that-can't-lie is *why* it's safe to
  generate into. Lead A, follow with D as the "and here's why that matters in 2026" beat.

Ranking: **A ≫ C ≈ B > D > E**. (C ranks high on hook mechanics but is gated behind post-v1
concurrency — hold it for when the sim-scheduler is browser-runnable.)

## 2 · The 30-second pitch (landing-page hero)

> **Headline:** The docs can't lie. They're generated from the proof.
>
> **Subhead:** bang is a programming language with a formally-verified core, compiled to
> WebAssembly. Its reference isn't written — it's *generated* from the same verified source the
> compiler runs, and every example in it is machine-checked on every build. The documentation
> literally cannot drift from the language.
>
> **Three subclaims:**
> - **Verified core, honest edges.** A small kernel (thunks · effects · handlers · STM) is proven
>   correct in Lean; the rest is a tested superset, and the seam between them is marked, never
>   hidden. *(the stratification principle, CLAUDE.md)*
> - **Paradigms are values.** Imperative, transactional, reactive — each is a library over one
>   kernel, installed as a handler you can swap. *(PRD.md §2)*
> - **Built to be generated into.** Illegal states are unrepresentable, not linted — which is what
>   makes it a safe target for an AI to write. bang itself is built by agent teams. *(PRD.md §3)*
>
> **CTA:** `git clone` → your first program in 8 minutes. *(stranger-test-1: clone→working cipher
> in ~8 min)* → **Read the reference that can't lie ›**

Honesty guardrail on the hero: the CTA promises the *stranger-test-1 journey* (a real cipher from
the reference + examples), **not** a browser playground for the full language — only rung-1 pure
arithmetic is browser-runnable (`traction-survey.md` §5; §5 below).

## 3 · The 2-minute pitch (HN-comment length)

> Most languages document themselves twice: once in the compiler, once in prose — and the prose
> rots. bang closes that gap by construction. Its kernel (a small graded call-by-push-value core:
> thunks, effect rows, handlers, and STM) is formally verified in Lean, and the language reference
> is *generated* from that same source — the surface grammar from the reified parser tables, every
> code example as a build-gated assertion. If an example would break, the build goes red. The docs
> can't drift because they're derived, not maintained.
>
> The design bet underneath: **paradigms and runtimes are values, not language features.** A
> program is a *description* until you force it; a function's paradigm is just which effects are in
> its type row; a runtime is a handler you install at the use site. Want state with an audit trail?
> Install the event-store handler. Want it fast and destructive? Swap to the in-place handler —
> same program, different runtime. Concurrency (post-v1) is the same move: the default scheduler is
> a *seeded, deterministic* one, so concurrent programs replay byte-for-byte; production
> nondeterminism is an explicit opt-in, not the default you're stuck with.
>
> It's early — v0.1, a real surface that runs rungs 0–4 through the verified kernel, honest about
> what's tested vs proven. But the honesty *is* the pitch: this is a language designed to be safe
> to generate into (its illegal states are unrepresentable, not linted), and it's being built by
> agent teams as the proof. If you've ever wanted a language where "the docs are wrong" is
> structurally impossible, this is that experiment.

## 4 · The skeptic's FAQ (the 6 questions an HN thread WILL ask)

**Q1. Is it production-ready?**
No — and we'll tell you exactly how not. bang is v0.1. The surface runs rungs 0–4 (state, STM,
reactivity, user types) through the verified kernel from real `.bang` source, but the compiler is
young, the multi-op user-effect surface is broken today (issue #86), and the full compile-to-wasm
pipeline is landing incrementally. Stranger tests score current ship-ability at **7/10** and say so
publicly (`stranger-test-3.md`). Public-early is deliberate: every checkpoint ships a v0.x tag. Use
it to explore the ideas, not to run your payroll.

**Q2. Why Lean?**
Because the claim is "verified," and verified means machine-checked by a kernel you can audit, not
"we tested it a lot." Lean 4 gives a small trusted axiom base; bang's headline theorems reduce to
`{propext, Classical.choice, Quot.sound}` and the build gates that (CLAUDE.md "how to verify"). The
payoff a user *sees*: the generated reference and its gated examples are a direct consequence of the
same source the proofs run against — that's what makes "docs can't lie" a structural fact, not a
slogan.

**Q3. Why not just use Koka / Effekt / OCaml 5 effects?**
Those are excellent effect languages and bang borrows from them (row-polymorphic forwarding is
Koka's; tunneling/lexically-scoped handlers are Zhang–Myers — `effect-algebra-survey.md`). bang is
**not** "another effect-typed language" (`PRD.md` §2). The differentiator is the *verified
substrate*: the effect system is proven sound in Lean, the compilation is verified two-hop to wasm,
and the docs are generated from that. The moat is (paradigm-and-stage flexibility) *turned into
guarantees* rather than conventions — an effect language you can prove things *about*, aimed
squarely at being a codegen target for AI. If you want effects today in production, use Koka. If you
want a verified substrate to build correctness-critical systems (the north star is a verified OS,
`PRD.md` §3), that's the bet bang is making.

**Q4. What's actually verified vs just tested?**
This is the best question and the honest answer is our differentiator. bang is built on an explicit
**verified core + tested superset** seam (CLAUDE.md, the stratification principle):
- **Verified (Lean-proven, axiom-clean):** the kernel semantics, the effect-row algebra, the
  CalcVM derivation, type/effect/resource safety of the total fragment.
- **Tested (differential-tested against the verified reference, not proven):** the surface parser
  and elaborator, the runtime, and the Turing-complete `Div` fragment (fuel-bounded).
- **The seam is type-visible and marked** — descent from verified to tested is never silent.
We publish this split rather than blur it. A language that tells you precisely where the proof stops
is more trustworthy than one that says "verified" and means "we have some tests."

**Q5. What about performance?**
Second-class, on purpose, and we own it (invariant #7: "a slow correct path beats a fast unverified
one"). v1 optimizes only where it touches the user; the default State handler is the *verifiable*
event-store one, with a fast in-place handler as an explicit opt-in. bang is not competing with Rust
on throughput — it's competing on *correctness you get structurally*. If your bottleneck is proving
your allocator never double-frees, not shaving nanoseconds, that's the trade bang makes.

**Q6. Who is it for?**
Two audiences, one substrate. **Humans** building correctness-critical systems (the north-star
validation is a verified xv6-class OS kernel, in the seL4/CertiKOS lineage — `PRD.md` §3). And
**agents**: a verified, illegal-states-unrepresentable language is uniquely valuable as a *target
for AI code generation* — the language enforces what the author might not. bang is built by agent
teams as the existence proof. It is not for CRUD apps; you don't need proof-by-construction for
those.

## 5 · Anti-hype rules — what we must NOT claim

Enforced against every piece of copy (from `traction-survey.md` §5, the Crystal-spike lesson —
hype without substrate decays; this audience of proof people *will* catch a green-stub claim):

- **NO "try the full language in your browser."** Only rung-1 (pure ⊥-row arithmetic → `.wat` on
  wasmtime) is browser-runnable honestly (`emission-rung1-probe.md`). A playground that stubs the
  hard part is the green-stub lie in marketing form. Say "try the pure fragment" or don't ship the
  playground claim.
- **NO "proof-by-construction, today, for your data structures."** The full user-facing law-language
  is post-v1 (`PRD.md` §2, §6: "this is the north star; it is the least-built thing"). v1 ships the
  *kernel's* guarantees + one minimal verified-data-structure demo. Lead with docs-that-can't-lie
  (shipped), let the moat be the roadmap.
- **NO "production-ready" / "stable" / "1.0".** It's v0.1, 7/10 stranger-test. Public-early ≠ done.
- **NO closed contextual-equivalence claim.** The binary LR (◊4 contextual equivalence) is parked;
  don't claim it. The forward-simulation (compile correctness) is the live theorem — cite that.
- **NO "deterministic concurrency, today."** Concurrency is post-v1 (ADR-0101 records *direction*;
  nothing in v1 changes). The replay claim (candidate C) is real but gated — hold it until the
  sim-scheduler is a runnable demo, then it's a headline.
- **NO first-party media team / sponsored conf.** Census-wide anti-pattern pre-1.0
  (`traction-survey.md` §5). Founder presence + design-deep-dives, not release-note marketing.

## 6 · Tone — the reference class we emulate

| language | tone signature | what bang borrows | cite |
|---|---|---|---|
| **Gleam** | *"a friendly language for building type-safe systems that scale"* — warm, approachable, DX-forward | the friendliness and the *concrete* type-safety claim (not "powerful"); solo-author-as-channel voice | [gleam.run](https://gleam.run/) |
| **Zig** | blunt, engineer-to-engineer, anti-marketing ("no hidden control flow", "no hidden allocations") | the **bluntness** and the *negative* specificity (name what it *doesn't* do — "the docs can't lie / drift") | `traction-survey.md` §1 |
| **Rust (early)** | *"fast, safe, concurrent — pick three"* — names the three concrete properties, no superlatives | **specificity beats superlatives**; the honest-about-tradeoffs voice; "stability gates the crowd" | `traction-survey.md` §1, §5 |
| **Odin** | deliberately anti-hype, "steady, stable, slow growth"; author's hot-takes as accidental marketing | the **honesty-as-differentiator** posture — publish the 7/10, publish the tested-vs-proven seam | `traction-survey.md` §1 |

**Composite voice for bang:** Zig's bluntness + Rust's specificity + Odin's radical honesty, warmed
by Gleam's friendliness. The through-line: **we tell you exactly what's true, including what isn't
done** — because for a *verification* language, honesty isn't just tone, it's the product claim.

Sources for the tone research: [Gleam homepage](https://gleam.run/) · [gleam-lang/gleam
README](https://github.com/gleam-lang/gleam); Zig/Rust/Odin voice per `traction-survey.md` §1
citations (Wikipedia:Zig, gingerBill "Marketing Odin is Weird", the Rust MIT-Tech-Review piece).
