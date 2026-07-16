<!-- note-status: active -->
# Stranger test — round 4

A developer with a strong general-PL background, never having seen bang, clones
the repo, learns it from the docs, and builds something real. The naivety is the
instrument: every time I had to read compiler source to answer a question, the
docs failed; every friction point in the first 15 minutes is where a real
stranger bounces.

**Method** (round-3 protocol): rebuild first (time it, note friction) → learn
from docs ONLY (`docs/reference/language.md`, README, `examples/`) → build up
hello-world → exercise the new surface, probing one step past each example →
build one real ~90-line program → score. Round-3's report was read ONLY at the
very end, after the score below was locked.

---

## Overall score: **8 / 10**

**Rubric** (what each point measures, stranger's-eye):

| Band | Meaning |
|---|---|
| 9–10 | I could learn it and ship without reading compiler source; errors teach; docs never lied. |
| 7–8  | I shipped a real program from the docs; a handful of sharp corners cost me 20–40 min each, mostly recoverable from error text + examples. |
| 5–6  | I shipped, but only by reading source or examples the reference should have taught; ≥1 error actively misled me. |
| ≤4   | I bounced — couldn't get a non-trivial program running from the docs alone. |

**Why 8, not higher**: the build was fast and clean, the reference is genuinely
excellent (generated-from-source, every example build-gated — it never lied to me
on syntax), and I shipped a 90-line RPN calculator with a custom effect. What
held it back from 9: two of the corners cost real time and one had an error
message whose *own suggested fix does not work* (F1), plus the whole
"top-level `let f = fun …` must be thunked" rule and the custom-effect cap
idioms are undocumented in the reference — I recovered them only by reading
`examples/caesar` and the reference's #90 example line, not from any prose that
teaches the rule.

**Why 8, not lower**: nothing forced me into the compiler *source*. Every gap was
recoverable from an example or an error string. The delight column is real.

---

## Journey log

| # | What I did | Result | Time-to-recover |
|---|---|---|---|
| 1 | `nix develop -c lake exe cache get && … lake build bang` (README path) | clean, ~4.5 min cold (Mathlib oleans already in nix store; add minutes if not) | — |
| 2 | `bang eval "1 + 2"`, run `examples/state` | `3`, `5` — worked first try | — |
| 3 | Probed all basics (let/if/lambda/thunk/raise/handle/state/match/do) | all correct | — |
| 4 | Prelude fns `($fst)`, `($abs)`, `($min)`, `($concat)` | all correct | — |
| 5 | `fst (3, 4)` (natural, no force) | `app: callee is not a function ('fst')` | instant — the docs DO say force-convention |
| 6 | Custom effect `handle … with Net as net { fetch(n) => n*10 }` | `30` — worked from the reference example verbatim | — |
| 7 | `deriving (Eq)` on a recursive `data Tree` | `1` — worked | — |
| 8 | `deriving (Eq)` on a generic `data Box a` | `generic type 'Box' needs type argument(s)` — even with `(Mk(3) : Box Int)` | gave up; generic deriving is simply absent |
| 9 | `bang test` on a trait law using `==` | `✓ PASS (30 samples)` — works! | — (but reference says it's broken — F5) |
| 10 | `let double = fun x => x + x` (top-level, natural) | `value is not a returner — force it ($double)` — **the suggested fix is wrong** | ~15 min: tried `$double`, `$fun…` (parse errors), finally found `{…}` in caesar |
| 11 | RPN: `match c { Char(n) -> … }` inside a curried 2-arg `let rec` | `match scrutinee is #3000002, not Str` | ~10 min: fix is ascribe the OUTER scrutinee `(s : Str)` |
| 12 | RPN: thread a cap `err` through a helper fn | `receiver is not a capability value (Cap ℓ)`; `(e : Cap Err)` → `constructor 'Err' expects 1 argument(s)` | ~15 min: annotate whole thunk `: Thunk (Cap Fail -> …)`, and rename effect off `Err` (prelude-constructor clash) |
| 13 | RPN calculator (90 lines) checks + runs | `35` for `"3 4 + 5 *"`; div/underflow branches all behave | shipped |
| 14 | `bang fmt` my annotated file | round-trips + still runs, but **strips every comment** (8-line header gone) | documented, but jarring |

**The program shipped**: `scratch-stranger4/rpn/main.bang` — an RPN calculator
(space-separated tokens, `+ - * /`, multi-digit ints) using a `data Stack`, a
custom `Fail` effect threaded as a typed capability through helpers, curried
structural recursion, and the injected `isDigit`. `"3 4 + 5 *"` ⟹ 35,
`"2 3 4 * +"` ⟹ 14, `"100 50 - 3 *"` ⟹ 150.

---

## TOP findings (ranked)

### F1 — the top-level `let f = fun …` error message suggests a fix that DOESN'T PARSE (the strongest finding)

**Repro**:
```
$ echo 'let double = fun x => x + x
let main = ($double) 21' | bang check
error at 1:5: let-binding 'double': value is not a returner — force it ($double) or bind a value
```
Following the suggestion literally is a **parse error**:
```
$ echo 'let double = $fun x => x + x ...' | bang run
error: parse error: unexpected 'fun' where an atom was expected
```
The actual fix — nowhere in the message — is to **thunk the RHS**:
`let double = {fun x => x + x}` (as `examples/caesar` does for `encode`/`decode`).

**Why it bites a stranger hard**: `let f = fun x => …` is the single most natural
thing a functional programmer writes. bang's CBPV core makes a bare `fun` a
*computation* (returner), and a top-level `let` binds a *value*, so it must be
suspended. That's a fine design — but the error tells me to `$`-force at a
position where `$` can't go, sending me chasing parse errors for 15 minutes.

**What a fix looks like**: change the message to name the real fix —
`wrap the function in a thunk: let double = {fun x => …}` — and add a "Top-level
bindings" subsection to the reference's *Modules* or a new *Definitions* section
that states the rule (a top-level `let` binds a value; suspend a function with
`{…}`; call it forced, `($f) x`). Ideally a `B0xx` diagnostic code for it.

**Which docs failed me**: `docs/reference/language.md` — the words "returner",
"top-level let", and the thunk-a-function idiom appear **nowhere**. The examples
use `{fun …}` everywhere but never say why.

---

### F2 — `deriving (Eq, Ord)` is entirely absent from the language reference

**Repro**: `grep -i deriving docs/reference/language.md` → zero hits about the
feature. Yet `examples/derive-eq-ord/main.bang` uses `data Point = Pt(Int, Int)
deriving (Eq, Ord)` and it works (`==`/`<` dispatch through generated impls).

A stranger learning from the reference would **never discover `deriving`
exists**. It's a headline ergonomic (the alternative is ~15 lines of hand-written
trait+impl per type), and it's example-only.

**Also**: `deriving` on a **generic** type is unusable —
`data Box a = Mk(a) deriving (Eq)` fails at the *decl* site with
`generic type 'Box' needs type argument(s)`, and no annotation at the use site
rescues it. Non-generic (`data BoxI = MkI(Int) deriving (Eq)`) and recursive
(`data Tree = Leaf | Node(Tree, Tree) deriving (Eq)`) both work.

**What a fix looks like**: a *Deriving* section in the reference — the syntax, the
supported classes (Eq, Ord), the recursive-OK / generic-NOT-OK boundary stated as
a known limitation with a forward pointer, and one build-gated example. The
generated reference already harvests `#guard`s; the `derive-eq-ord` example just
needs to be pulled into the corpus that renders.

---

### F3 — threading a capability through a helper needs a heavy, undocumented annotation

**Repro** — the natural spelling fails two ways:
```
let apply = {fun f => fun op => fun st => … f.fail(1) …}
  ⟹ error: cap op 'fail': receiver is not a capability value (Cap ℓ)

let useIt = {fun e => (e : Cap Err).fail(9)}
  ⟹ error: constructor 'Err' expects 1 argument(s)   -- inline (e : Cap Err) doesn't parse as a cap type
```
The working idiom (recovered from the reference's #90 example, line 579): annotate
the **whole thunk** with the full arrow-and-row type, cap-position included:
```
let apply = ( {fun f => fun op => fun st => …} : Thunk (Cap Fail -> Int -> Stack -> Stack ! {Fail}) )
```
Plus: an effect named `Err` (or an op `Ok`) silently **clashes with the prelude's
Result constructors** — `(… : Cap Err)` gets read as the constructor `Err`. I had
to rename my effect `Err` → `Fail`.

**Why it bites**: every custom-effect example in `examples/` and the reference
inlines the handler right where the cap is bound (`handle … with Net as net {…}`),
so `net` is always in scope locally. The moment you factor logic into a helper
that *receives* the cap — the obvious move for any non-toy program — you're on
your own. The annotation is correct-by-construction (it's CBPV surfacing), but
it's undiscoverable: no example passes a cap as a parameter, and the reference's
`Cap Foo` type only ever appears inside those big whole-thunk annotations without
saying "this is how you thread a cap".

**What a fix looks like**: a *"Passing a capability to a helper"* subsection under
User-defined effects, with the `Thunk (Cap E -> … ! {E})` idiom spelled out and
one worked example (an effect used across two functions). And a B0xx note that an
effect/op name colliding with a prelude constructor (`Err`/`Ok`/`Some`/`None`/…)
is a hazard — ideally a loud diagnostic rather than the cryptic
`constructor 'Err' expects 1 argument(s)`.

---

### F4 — `match scrutinee is #NNNN, not Str` in a curried multi-arg `let rec`; the fix (ascribe the scrutinee) isn't in the message

**Repro**:
```
let rec numOf : Int -> Str -> Int ! {Div} = fun acc => fun s => match s {
  SNil -> acc, SCons(c, t) -> match c { Char(n) -> ($numOf) (acc*10 + (n-48)) t }
}                        ⟹ error: match scrutinee is #3000002, not Str
```
The single-arg version (matching the `examples/tokenizer` shape) works fine. The
fix in the curried case is to **ascribe the outer scrutinee** `match (s : Str) {…}`
— the second curried parameter's type isn't propagated to the match site.

**Why it bites**: the `#3000002` is an internal type-hole placeholder leaking into
a user-facing error (the reference's issue #100 notes the same leak in
`type`/`hover`). A stranger reads "not Str" and stares at code that clearly *is*
matching a Str. The `examples/` corpus that does multi-arg recursion (e.g. caesar's
`shiftCode : Int -> Int -> Int`) never matches a *sum* scrutinee on the later
param, so the idiom-by-example doesn't surface it.

**What a fix looks like**: propagate the declared param types into match-scrutinee
inference for curried `let rec` (the real fix), or — cheaper — a diagnostic that
says "scrutinee type is undetermined here; ascribe it: `match (x : T) {…}`"
instead of leaking `#NNNN`. A one-line reference note ("in a curried `let rec`,
ascribe a sum/data scrutinee that comes from a later parameter") would have saved
the 10 minutes.

---

### F5 — the reference is STALE on `bang test` law execution (a POSITIVE drift)

The reference (Traits & Laws section, the #74 note) still says: *"a law's
INVOCATION of its trait op … currently errors (`app: callee is not a function`)
… end-to-end law EXECUTION through the CLI is not yet wired."*

**Reality**: it works.
```
$ bang test scratch-stranger4/law2.bang      -- law refl(a): a == a
✓ Eq2.refl — PASS (30 samples)
laws: 1/1 passed
```
And a law that calls its op *by name* now gets a **clear, specific** diagnostic
(not the old `app: callee is not a function`): *"law 'Add.comm' calls trait op
'add' directly — trait ops are invoked ONLY through their overloaded operator in
v1 (ADR-0068); write the law using '==' …"*. The feature grew past its docs.

**What a fix looks like**: update the #74 note to reflect that operator-bodied
laws execute and sample-check, and that by-name op calls give the new B0xx-class
diagnostic. Right now the docs *undersell* a working feature — a marketing loss.

---

### F6 (minor) — `bang fmt` silently deletes all comments

Documented (Lexical notes: comments stripped pre-parse, not preserved by fmt), so
not a hidden bug — but running the *canonical formatter* on my own 90-line
annotated file erased an 8-line header doc and every inline comment. For a
stranger this is a "wait, where did my documentation go?" moment. A stronger doc
warning at the `bang fmt` description (not only buried in Lexical notes), or a
`--check`/refuse-if-comments-present guard, would soften it.

### F7 (minor) — the default-fuel exhaustion error is a wall of internals

```
error: the env engine (the default, ADR-0094) produced no first-order value — it
collapses out-of-fuel / escaped-capability / raise / function-terminal / stuck
into one outcome; re-run with --engine=oracle …
```
A stranger who just wrote a deep recursion isn't told the *likely* cause (out of
fuel) or the *cheap* fix (`--fuel N`, which the README documents). `--engine=oracle`
gives the precise diagnosis, but the first thing to suggest for a plain deep
recursion is raising the fuel. Adding "…or raise the step ceiling with `--fuel N`"
to this message would close the loop.

---

## What DELIGHTED me (the honest positives — these matter for the pitch)

1. **The generated reference is the best I've seen in a research language.** Every
   syntax example is a `#guard` gated by `lake build`, so *it cannot lie about what
   the language does*. When I typed something from the reference verbatim, it ran.
   That's a real trust dividend — I stopped double-checking after the third example.

2. **`bang query`/`holes`/`impact` — an "LSP for agents" as plain CLI subcommands.**
   `bang query type f`, `bang holes` (shows `Thunk #1000002 -> #1000002` for an
   un-pinned `id`), `bang impact` (reverse dependents) — all JSON, all stateless,
   one process per call. As an agent I'd lean on these constantly. No server, no
   protocol. This is a genuinely novel and *right* bet.

3. **`bang explain B004`** gives a summary + teaching text + a minimal triggering
   example. rustc-class diagnostic codes in a research language is above
   expectation, and the ones that exist are good.

4. **Custom effects are as clean as the pitch claims** — `effect Net { fetch : … }`
   then `handle … with Net as net { fetch(n) => n*10 }` ran first try from the
   reference. The "runtime is a handler installed at the use site" story is real
   and *legible* at the surface.

5. **`deriving (Eq, Ord)`** (once I found it in examples) just works on recursive
   types — `Node(Leaf,Leaf) == Node(Leaf,Leaf)` is `true` with a one-word annotation.

6. **`bang new`** scaffolds a runnable starter whose `expected.txt` is *produced by
   running it*, not hand-written — the SSoT discipline visible in the tooling itself.

7. **No undefined behavior, and it's a documented design pillar.** Every failure is
   a named terminal (`outOfFuel`/`escapedCap`/`wrong`/`stuck`-unreachable-when-typed).
   Coming from C-family languages this is a breath of air, and the reference states
   it as a *guarantee* against the C trichotomy.

8. **Learning the one-shot-resume effect model by building.** My div-by-zero branch
   returned the wrong sentinel — because a custom-effect `fail` *resumes* (tail,
   one-shot), it doesn't abort. That's not a bug, it's the semantics teaching me:
   to abort you reach for `raise`, and the B005 ret-shape wall then stops you from
   raising *inside* a clause. The model is coherent once you feel it.

---

## Diff vs round 3 (read only after the score above was locked)

Round 3 scored **7/10**. Its top findings and their round-4 status:

| Round-3 finding | Round-4 status |
|---|---|
| **#86 multi-op custom effects broken** (`two.a`/`two.b` in one handler) | **FIXED** — the reference's clause-shape matrix (30+ build-gated `#guard`s) exercises 2- and 3-op effects exhaustively; my own custom effect worked. |
| **#87 param-carrying handler inert** (`param` unusable) | **FIXED** — reference shows `fetch(x) => x + param` ⟹ 105 as gated examples; `param` is documented + reserved. |
| **#88 user-effects undocumented** | **FIXED** — there's now a full *User-defined effects (ADR-0095)* section in the reference with the effect/handle/perform grammar, the `param` rule, and the B005 ret-shape wall spelled out. This was round-3's headline gap; it's closed. |
| laws + check-json (already fixed by r3 vs r2) | **still good** — and law *execution* now works too (F5), which the docs haven't caught up to. |

**Round-3 findings I did NOT re-test** (out of round-4's language-authoring scope,
flagged for honesty): #89 (`just verify` red-exits on a fresh clone's
`check-git-hygiene` pre-`setup`) — I built with the README's `lake build bang`
path, never ran `just verify`, so I can't claim it fixed or standing. #73 (`pub`
visibility unenforced) — still carried in the reference's Modules section as a
documented "known v1 limitation", not re-probed. The round-3 S4 cosmetics (`query`
verb key drift; `rename -w` trailing-newline) I also didn't re-check.

**New in round 4** (not in round 3's list): F1 (misleading returner error — likely
the single highest-value fix), F2 (`deriving` undocumented), F3 (cap-threading
idiom undocumented), F4 (curried-rec scrutinee ascription). These are the *next
layer* of stranger-stumbles — the ones you hit when you go past single-expression
examples into a real multi-helper program. Round 3's findings were about the
custom-effect surface being *broken*; round 4's are about the surface being
*correct but undocumented* once you factor code into helpers. That's progress: the
gaps moved from "the feature doesn't work" to "the feature works but the docs don't
teach the idiom for using it at scale."

**Standing theme across rounds**: the reference is superb at the
*single-expression* altitude (every form, build-gated) but thin at the
*program-authoring* altitude — top-level definition rules (F1), threading effects
through helpers (F3), and multi-arg recursion typing (F4) are exactly the things a
stranger needs the moment they write more than one `let`, and they live only in
example osmosis, not in teaching prose.
