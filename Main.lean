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
-/

import Bang.Frontend.Surface

open Bang
open Bang.Surface

/-- Default fuel for `Source.eval`. The kernel has no primitive arithmetic, so
programs are small; the in-repo `#guard` demos top out around 200. 100000 is a
generous ceiling that still terminates a genuinely-looping program as `oom`. -/
def defaultFuel : Nat := 100000

/-- A readable, structural rendering of a kernel `Val`. Reused nowhere in the
spine (kernel `Val` derives only `Inhabited`), so a small printer lives here.
`vthunk` holds a `Comp`, not a `Val`, so it prints opaquely — the rest is a
plain structural fold. -/
def valPretty : Val → String
  | .vunit      => "()"
  | .vint n     => toString n
  | .vvar i     => s!"#{i}"
  | .vcap n l   => s!"<cap {n}@{l}>"
  | .vthunk _   => "<thunk>"
  | .inl v      => s!"inl {valPretty v}"
  | .inr v      => s!"inr {valPretty v}"
  | .pair a b   => s!"({valPretty a}, {valPretty b})"
  | .fold v     => s!"fold {valPretty v}"

/-- Run one source string through the whole pipeline, printing the outcome and
returning the process exit code. `done` → stdout + 0; every failure outcome →
a clear stderr line + a distinct nonzero code (fail-loud, ADR-0063). -/
def runSource (src : String) : IO UInt32 := do
  match Bang.Surface.parse src with
  | .error e => IO.eprintln s!"parse error: {e}"; pure 1
  | .ok surf =>
    match Bang.Surface.lower surf with
    | .error e => IO.eprintln s!"lower error: {e}"; pure 1
    | .ok c =>
      match Bang.Source.eval defaultFuel c with
      | .done v      => IO.println (valPretty v); pure 0
      | .oom         => IO.eprintln "out of fuel"; pure 2
      | .escapedCap  => IO.eprintln "capability escaped its handler"; pure 3
      | .stuck       => IO.eprintln "stuck (ill-formed program)"; pure 4

def usage : String :=
  "bang — the lang-bang runner\n\n" ++
  "USAGE:\n" ++
  "  bang run  <file.bang>      run a bang program from a file\n" ++
  "  bang eval \"<surface expr>\"  run a surface expression directly\n\n" ++
  "EXIT CODES:\n" ++
  "  0  done — value printed to stdout\n" ++
  "  1  usage / parse / lower error\n" ++
  "  2  out of fuel (oom)\n" ++
  "  3  capability escaped its handler\n" ++
  "  4  stuck (ill-formed program)"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", file] =>
    let src ← IO.FS.readFile ⟨file⟩
    runSource src
  | ["eval", expr] =>
    runSource expr
  | _ =>
    IO.eprintln usage
    pure 1
