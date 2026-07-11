<!-- note-status: active -->
# bang v0.2 — a language whose docs are generated from the proof

<!--
POST METADATA (for the operator, strip before posting):
  target: Hacker News (Show HN) + lobste.rs · ~750 words
  title options (HN):
    A) "Show HN: Bang – a verified language whose docs are generated from the proof"
    B) "Show HN: Bang – the docs can't drift because they're generated from the verified source"
  first comment: docs/outreach/hn-first-comment.md (post immediately, author convention)
  every load-bearing claim traces — see the table in docs/outreach/README.md
-->

Most languages document themselves twice: once in the compiler, once in prose. The
prose rots. You've hit it — the example in the docs that no longer compiles, the flag
that was renamed three releases ago, the "returns a list" that now returns an iterator.
Everyone who has been burned by stale docs knows the docs *can* lie.

**bang's can't.** Its language reference isn't written — it's generated from the same
verified source the compiler runs against, and every code example in it is a build-gated
assertion. Here's what that looks like in the source:

```lean
#guard runYieldsInt 30 "let x = 3 in let y = 4 in x * x + y * y" 25
```

That `#guard` runs the program through the kernel semantics at build time. If the
language ever stopped evaluating that expression to `25`, `lake build` goes red — and
the reference row derived from it never ships. There are 96 such examples in the
1165-line generated reference, and over a thousand `#guard`s across the source. The
documentation cannot drift from the language because it is *derived* from it, not
maintained alongside it.

## What it actually is (the honest part)

bang is v0.2. It is a small, formally-verified kernel with a larger tested surface on
top, and the seam between them is marked, not hidden. The kernel — thunks, effect rows,
handlers, and STM — is proven correct in Lean 4, with the headline theorems reducing to
a three-axiom trusted base the build gates on every commit. Everything else (the parser,
the elaborator, the Turing-complete fragment) is *differential-tested* against that
verified kernel, never assumed. When we say "verified" we mean a specific, auditable set
of theorems; when we say "tested" we say that too. A language that tells you exactly
where the proof stops is more trustworthy than one that says "verified" and means "we
have a lot of tests."

It is not production-ready and we will tell you exactly how not: the compiler is young,
the multi-operation user-effect surface is still rough, and the outsider usability score
from our "stranger tests" (a fresh person, cold, with a stopwatch) sits at 8/10, published.
Use it to explore the ideas, not to run your payroll.

## Three things that work today

**Paradigms are values you swap.** A program is a description until you force it; a
function's paradigm is just which effects are in its type row; a runtime is a handler you
install at the use site. One shared `logic` function, `net.fetch(1) + net.fetch(2)`, run
under two different handlers:

```
$ bang run examples/stage-swap/main.bang
30005     # test handler: fetch(n) => n*10 gives 30000; prod: fetch(n) => n+1 gives 5
```

Same code. Two runtimes. Two answers. Nothing about `logic` changed — the behavior lives
in the handler, which is an ordinary value.

**Laws you declare get checked.** A trait law is a first-class object, not a comment.
Declare one and `bang test` sample-checks it and reports a counterexample when it breaks:

```
$ bang test transitivity.bang
✓ IntOrd.trans — PASS (30 samples)
$ bang test bogus.bang
✗ IntOrd.bogus — FAIL — counterexample [(0 - 10), 0]
```

`deriving (Eq, Ord)` for a recursive type generates the impl *and* its laws, so the
same check covers derived instances too.

**Whole programs compile to WebAssembly.** This is the v0.2 milestone. An n-queens solver —
closures, algebraic data types, recursion — lowers to a WasmGC module and runs on stock
`wasmtime`, returning the exact value the verified kernel computes:

```
$ lake exe rung4-shape examples/nqueens/main.bang nqueens.wat
oracle: Source.eval = 21004
$ wasmtime run -W gc=y,function-references=y,exceptions=y --invoke main nqueens.wat
21004
```

One command reproduces the whole rung against a real engine: `bash tools/emit-rung4-diff.sh`
runs ten complete programs through WasmGC on wasmtime and diffs every result against the
kernel oracle. That agreement — stock Wasm engine equals verified reference — is the point.

## Why we built it this way

bang is designed to be *safe to generate into*. Its illegal states are structurally
unrepresentable, not caught by a linter — which is exactly what you want in a language an
AI is going to write. bang itself is built by agent teams, against the verified kernel, as
the existence proof. The docs-can't-lie property isn't a slogan; it's the thing that makes
generating into the language trustworthy, because the reference an author (human or agent)
reads is provably the language that runs.

## Try it

```
curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh
```

Prebuilt for x86_64-linux, aarch64-linux, and Apple Silicon; build from source with Nix
for anything else.

**The reference that can't lie ›** https://phibkro.github.io/bang/

It's early, it's honest about where the proof stops, and the docs are generated from that
proof. If you've ever wanted a language where "the docs are wrong" is structurally
impossible, this is that experiment.
