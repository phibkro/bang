<!-- note-status: active -->
# Stranger test — round 5 (pre-v0.2)

A competent programmer new to bang meets it at `main @ 0fbececd`, right before the
public v0.2 tag. Read only what a newcomer may read (README, ONBOARDING, `docs/reference/
language.md`, `examples/**`, `bang --help`/`explain`, and the tool's own error text);
never the Lean sources, notes, decisions, or prior stranger notes. Rebuilt `bang` first
(`lake build bang`, green). Every repro lives in `scratch/stranger5/`.

## Overall score: **7 / 10**

The *tooling* is a genuine standout — `bang new`, `bang test`, `bang explain`, `bang fmt`,
`bang query` are the best onboarding surface I've seen in a young language, and the
reference is comprehensive and build-gated so most of what it teaches is true by
construction. What holds it to a 7 is that the **very first file a newcomer writes**
lands on a silent misparse (F1), the **reference's own `deriving` example doesn't run**
because the prelude now owns `Nil`/`Cons` (F2), the **most natural effect-op names**
(`get`/`set`/`put`) fail with an opaque parse error that never shows the `B002` the docs
promise (F3), and the **reference flatly contradicts a shipped feature** (mutual `let rec`,
F5). None of these are deep bugs; they are the exact rough edges that make a newcomer
think "I must be holding it wrong" on their first hour. What a newcomer needs above all
is a *learning path* — and there isn't one: ONBOARDING is entirely "verify the proofs,"
so the only teaching surface is the reference (dense, changelog-flavoured, issue-numbered)
plus `examples/`.

Measured against "what a newcomer needs": the language *works* (every feature I reached
for runs once spelled correctly), the tools are delightful, but the on-ramp has four
tripwires in the first three programs and no guide to route around them.

---

## Findings

Severity is for a **newcomer** (would this stop them / make them doubt the language),
not for the maintainer.

### F1 — The most natural multi-statement file silently misparses. **[high]**

The first thing a functional programmer writes is a few top-level bindings then a result:

```bang
let x = 3
let y = 4
x + y
```

`scratch/stranger5/trap.bang`:
```
$ bang run scratch/stranger5/trap.bang
error: app: callee is not a function
$ bang check scratch/stranger5/trap.bang
error: app: callee is not a function       # no span, no code, no hint
```

**What happened:** a top-level `let x = 3` with no `in` absorbs the *next* line's
expression as its RHS via juxtaposition-application — `3` applied to the trailing
expression — so `x + 1` becomes part of `x`'s body and "callee `3` is not a function."
Minimal repro (`g1.bang`):
```
let x = 3
x + 1
```
→ `error: app: callee is not a function`, and `bang query symbols` shows `x` with
`"typeError":"app: callee is not a function"`.

Interpose a `data` decl and it works (`g3.bang` = `let x = 3` / `data Marker = M` /
`x + 1` ⟹ `4`), because the decl terminates the RHS. That is exactly the
"literal-adjacency trap" the reference's own examples work around (`let x = 3 data
Marker = M x + 1`), but a newcomer has no reason to insert a marker `data` decl.

**What I expected:** either (a) a top-level `let` without `in` treats the following
line as the next decl / trailing expression (what every ML-family programmer expects),
or (b) a *located* parse/type error that says "the trailing expression was absorbed into
`x`'s binding — did you mean `let x = 3 in …`, or a `let main = …` decl?".

**The safe idioms** (which the reference's runnable examples all use, but never state as
a rule up front): end the file in `let last = e in <expr>`, or define `let main = <expr>`,
or a *single* bare trailing expression after decls. Two-plus decls + a bare trailing
expression is the trap. The `bang new` scaffold (F7) dodges it by ending in `let main`,
which is good but accidental teaching.

Repro: `scratch/stranger5/{trap,g1,g3}.bang`.

### F2 — The reference's own `deriving` example does not run (prelude owns `Nil`/`Cons`). **[high]**

The Deriving section (reference §Deriving, the `IntList` paragraph) presents:
```bang
data IntList = Nil | Cons(Int, IntList) deriving (Eq)
```
as a supported self-recursive example. Run it verbatim:
```
$ bang eval 'data IntList = Nil | Cons(Int, IntList) deriving (Eq) match (Cons(1, Nil)) { Nil -> 0, Cons(h, t) -> h }'
error at 1:16: ambiguous constructor 'Nil' — candidates: IntList (as 'IntList_Nil'), List (as 'List_Nil')
```

The prelude now unconditionally injects `data List a = Nil | Cons(a, List a)`
(ADR-0103 Amendment ①), so **any** user type reusing `Nil`/`Cons` collides (`B012`).
Worse, `deriving` on such a type is **impossible even with fully type-qualified
references**, because the generated impl body references the bare ctor names internally:

`scratch/stranger5/il2.bang` (qualified refs, paren scrutinee, still fails):
```bang
data IntList = Nil | Cons(Int, IntList) deriving (Eq)
let a = IntList_Cons(1, IntList_Nil) in
let b = IntList_Cons(1, IntList_Nil) in
if a == b then 1 else 0
```
→ `error: ambiguous constructor 'Nil' — candidates: IntList …, List …`

The identical shape with **non-colliding** names works perfectly (`il3.bang`,
`data Lst = Empty | Node(Int, Lst) deriving (Eq, Ord)` ⟹ `1`, both `==` and `<`
correct). So the fix a newcomer needs is "never name a ctor `Nil`/`Cons`" — which the
Deriving section does not warn about while *actively demonstrating* `Nil | Cons`.

`bang explain B012` is excellent (explains `(dataName, ctorName)` identity, gives the
`Type_Ctor` fix) — but it doesn't help the deriving case, where qualification isn't
enough. The `trait-recursive-eq` example *was* updated to `IntList_Nil`/`IntList_Cons`
with a comment about the collision; the **reference's Deriving section was not**.

**What I expected:** the Deriving section to either use non-colliding names, or lead with
"the prelude owns `Nil`/`Cons`/`Some`/`None`/`Ok`/`Err` — don't reuse them," and for
`deriving` on a colliding type to fail *at the decl site with B012* rather than mid-run.

Repro: `scratch/stranger5/{il2,il3}.bang`.

### F3 — Natural effect-op names (`get`/`set`/`put`) fail with a raw parse error, never the promised `B002`. **[high]**

A key-value effect is the canonical user-effect demo. The most natural op names:
```bang
effect KV { get : Int -> Int, set : Int -> Int }
```
```
$ bang run scratch/stranger5/p3e.bang
error: parse error: expected an identifier, got keyword 'get'
```
and with `put`:
```
$ bang check scratch/stranger5/b002.bang     # effect KV { put : Int -> Int }
error at 2:34: expected an identifier, got keyword 'put'
```

The reference *documents* this collision (effect-op names may not reuse
`get`/`put`/`new`/`read`/`write`/`raise`/`handle`) and registers a teaching code:
`bang explain B002` even gives the triggering example `effect E { get : Int -> Int }`.
But the reserved-word check fires in the **lexer/parser** at the *perform site*
(`kv.put(7)`, col 34), so the user gets a raw `parse error: … keyword 'put'` and the
`error[B002]` the docs advertise **never appears**. Renaming to non-reserved names works
(`kv2.bang`, `lookup`/`store` ⟹ `107`).

**What I expected:** the collision to surface as `error[B002]` at the *op declaration*
(`effect KV { get : … }`), with the "rename the op" teaching — not an opaque parse error
at a downstream call. Right now the one place the docs promise a friendly code is the one
place a newcomer will most naturally hit, and the code doesn't fire.

Repro: `scratch/stranger5/{p3e,b002,kv2}.bang`.

### F4 — Unparenthesized ctor-application match scrutinee ⇒ opaque parse error. **[medium]**

```
$ bang eval 'data Qux = Zed | Wam(Int) match Wam(3) { Qux_Zed -> 0, Qux_Wam(x) -> x }'
# (in a file) error: parse error: expected '{', got '('
```
`match Wam(3) { … }` is rejected; `match (Wam(3)) { … }` runs (⟹ `3`). The parser reads
`match Wam` then hits `(` and reports `expected '{', got '('` — it never says
"parenthesize the scrutinee." Every reference example parenthesizes ctor-app scrutinees
(`match (Cons(7, Nil)) { … }`), so the rule is *observable* but never *stated*, and the
diagnostic doesn't teach it. A nullary scrutinee (`match Zed { … }`) is fine unparenthesized,
which makes the inconsistency more confusing.

**What I expected:** either accept `match Wam(3) { … }`, or a diagnostic naming the fix.

Repro: `scratch/stranger5/{n5,n6}.bang`.

### F5 — The reference contradicts a shipped feature: mutual `let rec` (`and`). **[medium]**

Reference §Grammar (the `let` paragraph) states plainly:
> `let rec` is the only recursion marker, and it has no multi-binding form

This is **false**. `let rec f = … and g = … in …` works and is example-backed:
```
$ bang run examples/mutual-parity/main.bang
1101
```
My own `scratch/stranger5/mutual2.bang` (isEven/isOdd via `and`) ⟹ `1`. The `and`
mutual-rec form is taught *only* in `examples/mutual-parity`, never in the reference —
and the reference's prose actively says it doesn't exist. This is doc-vs-reality drift in
a hand-written prose paragraph inside an otherwise-generated reference.

Note the rough edge is honest and well-signposted: mutual siblings need an explicit
`! {Div}` row (neither certifies structurally), and the error when you omit it is
*helpful* — `thunk body performs {Div}, exceeding its declared bound {}` points right at
the fix. That part is a delight; only the reference's denial of the feature is the bug.

Repro: `scratch/stranger5/{mutual,mutual2}.bang`; `examples/mutual-parity/`.

### F6 — Type ascription on a `let` binder: allowed at top-level, rejected in `let … in`. **[medium]**

```
$ bang eval 'let x : Int = 3 data Marker = M x + 1'      ⟹ 4       # top-level decl: OK
$ bang eval 'let x : Int = 3 in x + 1'
error at 1:7: expected '=', got ':'                                 # expression form: rejected
```
The reference (Examples) shows `let x : Int = 3 …` working as a *top-level decl*, and a
newcomer reasonably generalizes it to the `let … in` expression form — where it's a parse
error. Relatedly, an *unparenthesized* ascription in a `let` RHS also fails:
```
$ bang eval 'let x = 3 : Int in x'
error at 1:11: unexpected ':' where an atom was expected
```
You must parenthesize: `let x = (3 : Int) in x` ⟹ `3`. Both are consistent with the
reference's always-parenthesize-ascriptions habit, but neither the asymmetry
(top-level binder ascription yes, `let…in` binder ascription no) nor the
parenthesization requirement is stated, and both diagnostics are low-level.

Repro: `scratch/stranger5/p-ann.bang` and inline evals above.

### F7 — `bang new`'s scaffold advertises a command that doesn't exist. **[low]**

`bang new myfirst` produces a clean, working starter (`hello from bang!`) — a real
delight (see below). But the generated `main.bang`'s own header comment says:
> Edit `main`, then re-run — `bang test --update <NAME>` re-bakes expected.txt.

There is no `--update` flag: `bang test` is only the trait-law runner, and
`bang test --update examples/myfirst/main.bang` just dumps the usage text. So the very
first file a newcomer opens instructs them to run a non-existent command. Also minor:
`bang new <NAME>` hardcodes an `examples/<NAME>/` prefix relative to cwd, so a newcomer
scaffolding outside the repo gets a surprise `examples/` directory.

Repro: `scratch/stranger5/examples/myfirst/` (created by `bang new`).

### F8 — Higher-order functions: the arrow type hides the thunk-and-force requirement. **[low]**

Writing `map` (the canonical second program):
```bang
let rec map : (Int -> Int) -> List Int -> List Int =
  fun f => fun xs => match (xs : List Int) {
    Nil -> (Nil : List Int),
    Cons(h, t) -> Cons(f h, (($map) f t))     -- f h  ⟹  error: app: callee is not a function ('f')
  }
```
The declared param type is `(Int -> Int)`, but the value you must pass is a *thunk*
(`{fun x => x*2}`) and the param must be *forced* to call it: `($f) h`. With `($f) h`
the program runs (`p1-map.bang` ⟹ `12`). The reference teaches the force convention for
`let rec` names (`$sum`) and for `let f = {fun…}` bindings, but not for the
*function-as-argument* case — and the arrow type `(Int -> Int)` gives no visible hint
that the argument is a thunk. This is the CBPV seam leaking into the newcomer's first
HOF; a one-line note ("a function passed as an argument is a thunk — force it: `($f) x`")
would close it.

Repro: `scratch/stranger5/p1-map.bang`.

### F9 — `10 / 0` returns `0` silently, against the "no undefined behavior / fail-loud" claim. **[low]**

```
$ bang eval '10 / 0'                    ⟹ 0    (env engine)
$ bang eval --engine=oracle '10 / 0'    ⟹ 0    (oracle too)
```
The reference's "Errors & terminals" section makes a strong promise: *"there is no
undefined behavior… every reachable failure is a defined, fail-loud outcome."* Division
by zero returning `0` is *defined and deterministic*, so it's arguably conformant — but
it is **silent**, not fail-loud, which is exactly the surprise the section's framing tells
a newcomer not to expect. Either it deserves a mention ("`/ 0` is defined to yield `0`")
or it should be a fail-loud terminal. As-is it reads as the one crack in an otherwise
airtight no-UB story.

---

## What genuinely delighted

- **`bang new`** — scaffolds a runnable `main.bang` + README + `expected.txt` *produced by
  running the starter*, and the generated file's comments teach the `$`/force convention
  inline. `hello from bang!` works on first run. Best first-five-minutes I've had in a young
  language. (Only F7 mars it.)
- **`bang test`** — pointing it at `data Point = Pt(Int,Int) deriving (Eq, Ord)` discovers
  `Eq.refl` and `Ord.irrefl` and sample-checks them (30 samples, PASS) with zero extra
  wiring. Derived instances being *law-checked* out of the box is a real "oh, nice."
- **`bang explain <CODE>`** — B012 and B002 both give a crisp summary + the fix + a minimal
  triggering example. When the codes actually fire (F3 is where one doesn't), this is
  rustc-grade.
- **The B005 RET-shape diagnostic** — `handle: clause 'test' body must be a 'ret'-shape
  value in v1 (no effects before resuming) …` names the wall *and* the reason. A documented
  limitation surfaced as a teaching error, not a crash.
- **The `{Div}` error on mutual rec** — `thunk body performs {Div}, exceeding its declared
  bound {}` points straight at "add `! {Div}`." Effect-row enforcement that *teaches*.
- **`bang fmt`** — canonicalizes and *simplifies* (`($sum) t` → `$sum t`), idempotent.
- **The reference is generated and build-gated** — every `⟹` example is a `#guard`, so the
  huge Examples section can be trusted. Most of the reference cannot lie; the drift I found
  (F2, F5) is concentrated in the *hand-written prose* paragraphs, exactly where the
  generate-don't-maintain discipline hasn't reached yet.
- **`bang query dump` / `symbols`** — clean JSON fact base; `symbols` on a broken file even
  carries the `typeError` per decl, which is how I confirmed F1's misparse.

## Docs-vs-reality gaps

**Taught but doesn't work as taught:**
- Deriving section shows `data IntList = Nil | Cons(…) deriving (Eq)` — collides with the
  prelude `List`, fails to run (F2).
- Grammar section says `let rec` "has no multi-binding form" — mutual `let rec … and …`
  exists and ships (F5).
- Docs promise `error[B002]` for reserved effect-op names — a raw parse error fires instead
  (F3).
- The `bang new` starter comment tells you to run `bang test --update` — no such flag (F7).

**Works but is untaught (newcomer would never find it):**
- **Host IO** (`import Io`, `Io_Console`, `con.print`/`readLine`, `--env=sim/real`) — real
  and runnable (`examples/hostio-echo` ⟹ `ih`), but *entirely absent* from README and the
  reference; `--env` isn't even in `bang --help`. Only discoverable by browsing `examples/`.
- **Mutual `let rec` (`and`)** — only in `examples/mutual-parity`, and contradicted by the
  reference (F5).
- **The safe file-entry shapes** (`… let x = e in <expr>` / `let main = …` / single trailing
  expr) — every example obeys them, but the rule is never stated, so the *unsafe* shape (F1)
  is what a newcomer writes first.
- **Passing/forcing a function argument** (`($f) x`) — the force convention is taught for
  names and thunk-bindings but not for HOF parameters (F8).

**The structural gap under all of this:** there is no *learner's guide*. ONBOARDING.md is
"verify the proofs" (contributor-facing); README pivots to architecture/packaging after a
short run-a-program section; the reference is a dense, issue-numbered, changelog-flavoured
generated document. A newcomer's path is README → `examples/` → reverse-engineer the idioms.
The single highest-leverage doc for v0.2 adoption would be a short "write your first bang
program" guide that states the four idioms F1/F3/F5/F8 leave implicit. The tools are already
excellent; the on-ramp is what's missing.

## Method note (for round 6)

The "probe one step past every example" method (round 3's addendum) paid off again: F1, F3,
F5, F8 all live exactly one natural step past a working example — the example runs, the
obvious next program doesn't. F2 was the exception: it's the *example itself* drifting under
a prelude change (the reference is generated for `⟹` blocks but its *prose* paragraphs
aren't gated, so a prelude change silently invalidated a hand-written code sample). Round 6
should specifically diff the reference's **prose code samples** against the running compiler —
they're the un-gated soft spot in an otherwise drift-proof document.
