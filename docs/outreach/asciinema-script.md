<!-- note-status: active -->
# Asciinema script — the v0.2 90-second demo

> The exact terminal sequence for the launch recording. **Every command was run
> against the repo binary and the outputs below are the REAL captured frames**
> (built `2026-07-11` off `draft-announcement @ 0425b925`, `wasmtime 45.0.0`) —
> a recording whose outputs are fictional is the green-stub lie in demo form.
> Re-run before recording; if a frame drifts, the demo is wrong, not the doc.
>
> Grounding: outputs captured from `lake exe bang` / `lake exe rung4-shape` +
> `wasmtime run` in the dev shell. Claims trace table: `README.md`.

## The through-line (why these five beats, in this order)

The wedge is **"the docs can't lie"** (`copy-kit.md` §1, candidate A). The demo can't
show a generated doc drifting in 90 seconds — so it shows the *runtime* facts the
docs are generated from, ending on the milestone that proves the pipeline is real:
a whole program compiled to WebAssembly and run on a stock engine, byte-matching the
verified kernel.

```
install → eval (it's alive) → handler-swap (paradigms are values)
        → hover (the tooling is real) → nqueens→wasm (the milestone)
```

Estimated runtime: **~85–95 seconds** at a readable typing pace (see per-beat budget below).

---

## Setup (before recording — NOT on camera)

```bash
nix develop                       # enter the dev shell (lake on PATH)
lake build bang rung4-shape       # warm the binaries so no build scrolls on camera
export PATH="$(pwd)/$(dirname "$(find .lake/build/bin -name bang)"):$PATH"
```

On camera, `bang` is the installed binary. For the recording we alias the freshly
built exe to `bang`; the install beat (§1) shows the command a *viewer* would run.

---

## Beat 1 — install (≈12s)

The one-liner a viewer runs. **Do not actually pipe-to-sh on camera** (it pulls a
release asset and mutates `~/.local/bin`); type it, let it sit, then cut. The command
is real (`tools/install.sh`, `README.md:52`); the frame is the command, not its effect.

```console
$ curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh
```

> Caption overlay: *"prebuilt for x86_64-linux · aarch64-linux · aarch64-darwin"*
> (the three release triples — `tools/install.sh` platform table).

---

## Beat 2 — eval: it's alive (≈12s)

A one-liner that forces a thunk. Charming + shows the `$`-force surface in one line.

```console
$ bang eval "let double = {fun x => x + x} in ($double) 21"
42
```

> Caption: *"a bare `fun` is a description; `{…}` suspends it, `$` forces it"*
> (ADR-0007 — the force discipline, one line).

---

## Beat 3 — the handler-swap: paradigms are values (≈22s)

THE conceptual beat. One shared effectful `logic` function; two handler installers
(`test` maps `fetch(n) => n*10`, `prod` maps `fetch(n) => n+1`); same code, two
runtimes, two answers, combined so both are legible: `30*1000 + 5 = 30005`.

Show the source, then run it.

```console
$ cat examples/stage-swap/main.bang
effect Net { fetch : Int -> Int }
let logic = ( {fun net => (net.fetch(1)) + (net.fetch(2))} : Thunk (Cap Net -> Int ! {Net}) ) in
let test = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n * 10 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in
let prod = ( {fun body => handle (($body)(net)) with Net as net { fetch(n) => n + 1 }} : Thunk (Thunk (Cap Net -> Int ! {Net}) -> Int) ) in
(($test) logic) * 1000 + (($prod) logic)

$ bang run examples/stage-swap/main.bang
30005
```

> Caption: *"one `logic`, two handlers — the runtime is a value you install"*
> (`copy-kit.md` §1 candidate B; `examples/stage-swap/README.md`).

---

### Optional beat 3b — checked laws (≈14s, if the runtime budget allows)

A trait law is a first-class object that the tooling samples. `bang test` reads a
DECLS-ONLY file (a trailing expression is refused — the runner supplies its own body).
Show a true law passing and a false one caught with a counterexample.

```console
$ bang test transitivity.bang
✓ IntOrd.trans — PASS (30 samples)
──────────────────────────────
laws: 1/1 passed

$ bang test bogus.bang
✗ IntOrd.bogus — FAIL — counterexample [(0 - 10), 0]
──────────────────────────────
laws: 0/1 passed
```

The two fixture files (from `tools/test-law.sh`):
- `transitivity.bang`: `trait IntOrd { fn lt(a, b) -> (Unit + Unit) law trans(a, b, c): a < b => b < c => a < c }` + an `impl IntOrd for (Int * Int)`.
- `bogus.bang`: the same, but the law is `bogus(a, b): a < b => b < a` (false).

> Caption: *"declare a law, and it gets sample-checked — with a counterexample when it
> breaks"* (issue #60; `tools/test-law.sh`). Cut this beat first if you're over budget.

---

## Beat 4 — hover: the tooling is real (≈14s)

`bang query hover` is an LSP-class op as a stateless CLI subcommand — JSON on stdout,
built for agents. Hover into the body of `safeAt` in nqueens; it resolves the whole
decl with its checked type and effect row `{Div}`.

```console
$ bang query hover examples/nqueens/main.bang 12 9
{"ok":true,"decl":{"name":"safeAt","kind":"letRec","type":"Thunk!{Div} Int -> Int -> List Int -> Int","row":"{Div}","typeError":null,"span":{"line":12,"col":9,"endLine":12,"endCol":15}}}
```

> Caption: *"`{Div}` = this function may not terminate — partiality is in the type"*
> (the stratification seam: the total fragment is ⊥-row, `Div` is descent).
> Optional: pipe `| jq .decl.type` for a clean frame if the raw JSON reads dense.

---

## Beat 5 — nqueens → WebAssembly: the milestone (≈25s)

The rung-4 payoff. A whole program — closures + algebraic data types + recursion —
lowers to a WasmGC module and runs on **stock wasmtime**, returning the exact value
the verified kernel computes. `21004` encodes 4-, 5-, 6-queens counts (2·10000 +
10·100 + 4).

```console
$ lake exe rung4-shape examples/nqueens/main.bang nqueens.wat
oracle: Source.eval = 21004
wat written: nqueens.wat

$ wasmtime run -W gc=y,function-references=y,exceptions=y --invoke main nqueens.wat
warning: using `--invoke` with a function that returns values is experimental and may break in the future
21004
```

Then the one-command repro (the differential harness — the whole rung-4 corpus, real
engine vs kernel oracle):

```console
$ bash tools/emit-rung4-diff.sh
── differential: wasmtime (WasmGC, real engine)  vs  Source.eval (kernel oracle) ──
example                      wasmtime         oracle   verdict
nqueens                         21004          21004   OK
list-basics                       302            302   OK
mutual-parity                    1101           1101   OK
parser-combinators                 35             35   OK
wildcard-match                      2              2   OK
tokenizer                           3              3   OK
string-stdlib                       1              1   OK
derive-eq-ord                       1              1   OK
trait-recursive-eq                  1              1   OK
trait-recursive-ord                 1              1   OK
PASS — all 10 programs ran on wasmtime with a value matching Source.eval (nqueens = 21004).
```

> Caption: *"same answer from a stock Wasm engine and the verified kernel — that
> agreement is the whole point"* (`emission-rung4-design.md`; invariant #1, proof
> rides the reference).

---

## Closing frame (≈3s, static)

```
bang — a verified language whose docs are generated from the proof.
  curl -fsSL https://raw.githubusercontent.com/phibkro/bang/main/tools/install.sh | sh
  the reference that can't lie ›  https://phibkro.github.io/bang/
```

---

## Per-beat time budget

| beat | content | ~seconds |
|---|---|---|
| 1 | install one-liner (typed, not run) | 12 |
| 2 | `bang eval` → 42 | 12 |
| 3 | `cat` stage-swap + `bang run` → 30005 | 22 |
| 4 | `bang query hover` → the `{Div}` row | 14 |
| 5 | `rung4-shape` + `wasmtime` → 21004, then the diff harness | 25 |
| — | closing static frame | 3 |
| | **total** | **~88s** |

## Recording notes

- Use `asciinema rec` with an idle-time cap (`--idle-time-limit=2`) so pauses don't
  bloat the runtime; keep the typing pace readable, not rushed.
- The `--invoke` experimental warning is REAL wasmtime output — leave it in, it's
  honest (we're using a bleeding-edge Wasm 3.0 feature). Don't edit it out.
- Frame 5's harness output is trimmed here to the verdict table; the full run also
  prints a build line and the corpus footer — let those scroll or cut with the
  `--idle-time-limit`.
- If recording for a GIF instead, drop beat 4 (the JSON reads dense in a loop) and
  keep 1-2-3-5; that lands at ~65s.
