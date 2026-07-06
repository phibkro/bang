/-
  Main.lean — the `bang` runner CLI (Tier-1 keystone).
  ─────────────────────────────────────────────────────────────────────────
  Turns "run a bang program" from "write a #guard + lake build" into

      lake exe bang run  <file.bang>     -- read a file, run it
      lake exe bang eval "<surface expr>" -- run a string argument

  This is a LEAF: it imports `Bang.Frontend.Surface` and is imported by
  nothing in `Bang/`, so the verified library + the Audit gate are untouched.

  WHY a compiled exe (not #eval): `Source.eval`'s fuel recursion does not
  reduce reliably under `#eval`/`lake env lean` (repo lesson
  `lean-eval-reliable-only-compiled`). A `lake exe` is COMPILED, so it runs
  the kernel semantics correctly at runtime. That is the whole reason this
  tool exists as a binary.

  It WRAPS existing machinery — `Bang.Surface.parse` / `.lower` and the
  kernel `Bang.Source.eval` — surfacing each failure outcome loudly with a
  distinct nonzero exit code. (We run the pipeline stage-by-stage instead of
  the one-shot `Surface.runFrom` so a parse/lower error is reported as such,
  not collapsed into `stuck`.)

  TWO ENGINES (issue #6). The default engine is the kernel oracle
  `Bang.Source.eval`. `--compiled` instead runs `exec ∘ compile` — the
  CALCULATED abstract machine (`Bang.CalcVM`, the verified compiler output of
  the two-hop architecture, ADR-0016), making the verified spine's payoff
  user-visible: the SAME program, the interpreted oracle vs the compiled
  machine, the SAME value. That agreement is not hoped-for — it is the proven
  `compile_correct` / `evalD_agrees_source` pair, cross-checked by the
  differential `#guard`s in `Bang/Examples.lean` (§C).
-/

import Bang.Frontend.Surface
import Bang.Frontend.TypeCheck
import Bang.Backend.AbstractMachine

open Bang
open Bang.Surface

/-- Default fuel for `Source.eval`. The kernel has no primitive arithmetic, so
programs are small; the in-repo `#guard` demos top out around 200. 100000 is a
generous ceiling that still terminates a genuinely-looping program as `oom`. -/
def defaultFuel : Nat := 100000

/-- Fuel for the compiled engine `exec`. `exec` counts MACHINE-INSTRUCTION steps
(a small constant multiple of `Source.eval`'s recursion depth — each source form
lowers to a few `Instr`s), so it is a FINER unit than `defaultFuel`. We hand it a
10× larger ceiling to stay generous under the different unit; both functions are
monotone in fuel (`exec_mono`; a terminated `Source.eval` stays `done`), so an
over-supply never changes a value — a genuinely-looping program still terminates
as the fail-loud non-value below. This maps fuel across the two engines; it does
NOT redefine either. -/
def compiledFuel : Nat := 1000000

/-- A `Str` value (ADR-0074, #49) — `SNil = fold (inl ())`, `SCons(Char cp, …) = fold (inr (fold cp,
…))` — rendered to its glyphs (code points → chars). `none` if the value is not a char-list. Only a
NON-EMPTY result is treated as a string by `valPretty` (an EMPTY char-list `fold (inl ())` is
structurally identical to any nullary constructor like `Nil`, so it stays structural — no misrender). -/
def asString : Val → Option String
  | .fold (.inl .vunit) => some ""
  | .fold (.inr (.pair (.fold (.vint cp)) rest)) =>
      (asString rest).map (fun s => String.singleton (Char.ofNat cp.toNat) ++ s)
  | _ => none

/-- A readable, structural rendering of a kernel `Val`. Reused nowhere in the
spine (kernel `Val` derives only `Inhabited`), so a small printer lives here.
`vthunk` holds a `Comp`, not a `Val`, so it prints opaquely — the rest is a
plain structural fold. A NON-EMPTY `Str` value prints as its glyphs (ADR-0074). -/
def valPretty : Val → String
  | .vunit      => "()"
  | .vint n     => toString n
  | .vvar i     => s!"#{i}"
  | .vcap n l   => s!"<cap {n}@{l}>"
  | .vthunk _   => "<thunk>"
  | .inl v      => s!"inl {valPretty v}"
  | .inr v      => s!"inr {valPretty v}"
  | .pair a b   => s!"({valPretty a}, {valPretty b})"
  | .fold v     => match asString (.fold v) with
                   | some s => if s.isEmpty then s!"fold {valPretty v}" else s
                   | none   => s!"fold {valPretty v}"

/-- Run a lowered `Comp` on the COMPILED engine: `exec ∘ compile`, the calculated
abstract machine (`Bang.CalcVM`). Success is the terminal `some [ret v]` (the value
on an otherwise-empty stack — the exact shape `compile_correct` and the `Agree`
battery pin); `exec` COLLAPSES every non-success (out of fuel, escaped cap, stuck)
into `none`, so unlike the interpreter this engine cannot sub-classify a failure —
it reports one honest fail-loud non-value (exit 5). A successful value prints
identically to the interpreted path (same `valPretty`). -/
def runCompiled (c : Comp) : IO UInt32 := do
  match Bang.CalcVM.exec compiledFuel 0 (Bang.CalcVM.compile c []) [] [] with
  | some [.ret v] => IO.println (valPretty v); pure 0
  | _ =>
    IO.eprintln "compiled machine produced no value (out of fuel, escaped cap, or stuck)"
    pure 5

/-- Run a lowered `Comp` on the selected engine (§ issue #6): the kernel oracle `Source.eval`
(default) or the calculated machine `exec ∘ compile` (`--compiled`). `done` → stdout + 0; every
failure outcome → a clear stderr line + a distinct nonzero code (fail-loud, ADR-0063). -/
def runComp (compiled : Bool) (c : Comp) : IO UInt32 := do
  if compiled then runCompiled c
  else
  match Bang.Source.eval defaultFuel c with
  | .done v      => IO.println (valPretty v); pure 0
  | .oom         => IO.eprintln "out of fuel"; pure 2
  | .escapedCap  => IO.eprintln "capability escaped its handler"; pure 3
  | .stuck       => IO.eprintln "stuck (ill-formed program)"; pure 4

/-- Run one source string through the whole pipeline, printing the outcome and returning the process
exit code. `typecheck` selects the pipeline (ADR-0076 #51):

  * DEFAULT — parse (located) → **TYPE-CHECK (reject on error)** → lower → run (`checkAndLower`).
    An ill-typed program is caught as a TYPE ERROR before it runs, so the run path and the `#guard`
    gate share ONE type gate (SSoT) and `type_safety` (well-typed ⟹ never stuck) is real for users.
    A parse error is LOCATED (`error at line:col: …`); a type/elab error prints the checker's message.
  * `--no-typecheck` — the raw erase-and-run path (`elaborateToComp`): parse → elaborate → lower →
    run, NO type gate. Kept for oracle/differential testing (running an ill-typed program to observe
    the defined runtime `stuck`/`escapedCap`, ADR-0063).

`compiled` selects only the execution ENGINE and is orthogonal to `typecheck`. -/
def runSource (typecheck compiled : Bool) (src : String) : IO UInt32 := do
  if typecheck then
    match Bang.TypeCheck.checkAndLower src with
    | .error (m, some sp) => IO.eprintln s!"error at {sp.loc}: {m}"; pure 1
    | .error (m, none)    => IO.eprintln s!"error: {m}"; pure 1
    | .ok c               => runComp compiled c
  else
    match Bang.TypeCheck.elaborateToComp src with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp compiled c

def usage : String :=
  "bang — the lang-bang runner\n\n" ++
  "USAGE:\n" ++
  "  bang run  [FLAGS] <file.bang>      run a bang program from a file\n" ++
  "  bang eval [FLAGS] \"<surface expr>\"  run a surface expression directly\n\n" ++
  "PIPELINE (default: type-check first):\n" ++
  "  (default)        parse → TYPE-CHECK → lower → run; an ill-typed program is a TYPE ERROR\n" ++
  "  --no-typecheck   raw erase-and-run (no type gate) — for oracle/differential testing\n\n" ++
  "ENGINE:\n" ++
  "  (default)    kernel oracle Source.eval\n" ++
  "  --compiled   the calculated machine exec∘compile (verified compiler output, ADR-0016)\n" ++
  "               — same program, same value; failures collapse to exit 5\n\n" ++
  "EXIT CODES:\n" ++
  "  0  done — value printed to stdout\n" ++
  "  1  usage / parse / elaboration / TYPE error\n" ++
  "  2  out of fuel (oom)              [oracle engine]\n" ++
  "  3  capability escaped its handler [oracle engine]\n" ++
  "  4  stuck (ill-formed program)     [oracle engine, --no-typecheck]\n" ++
  "  5  compiled machine produced no value (oom / escaped cap / stuck) [--compiled]"

def main (args : List String) : IO UInt32 := do
  match args with
  | cmd :: rest =>
    if cmd == "run" || cmd == "eval" then
      -- FLAGS (`--…`) may appear in any order before the single positional; anything else is usage.
      let compiled   := rest.contains "--compiled"
      let typecheck  := !rest.contains "--no-typecheck"
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [arg] =>
        let src ← if cmd == "run" then IO.FS.readFile ⟨arg⟩ else pure arg
        runSource typecheck compiled src
      | _ => IO.eprintln usage; pure 1
    else
      IO.eprintln usage; pure 1
  | _ => IO.eprintln usage; pure 1
