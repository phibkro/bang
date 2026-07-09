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
import Bang.Frontend.Format
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

/-- Run `bang fmt`: format a whole program (decls + body, `Bang.Format.fmtProg`) and print the
canonical form to stdout. `.error` → stderr + exit 1, the SAME convention `runSource`'s parse-error
arm uses (a fmt failure IS a parse failure — `fmtProg` round-trips through the ordinary parser,
ADR-0046: never a silent guess on unparsable input). No `-w` (in-place write) this slice — print
only; in-place writing is a separate decision the team lead is holding. -/
def runFmt (src : String) : IO UInt32 := do
  match Bang.Format.fmtProg src with
  | .error e  => IO.eprintln s!"error: {e}"; pure 1
  | .ok out   => IO.println out; pure 0

def usage : String :=
  "bang — the lang-bang runner\n\n" ++
  "USAGE:\n" ++
  "  bang run  [FLAGS] <file.bang>      run a bang program from a file\n" ++
  "  bang eval [FLAGS] \"<surface expr>\"  run a surface expression directly\n" ++
  "  bang repl [FLAGS]                  interactive read-eval-print loop (issue #7)\n" ++
  "  bang fmt  [<file.bang>]            print the canonical form (issue #58); reads stdin if no file\n\n" ++
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

/-! ## The REPL (issue #7)

A read-eval-print loop over the SAME production pipeline `runSource` wraps (parse → type-check →
lower → run) — no bespoke evaluation path, so the REPL can never disagree with `bang run`/`bang
eval` on a given program. Two things a loop needs that a one-shot runner doesn't:

  1. **multi-line input** (issue #52 span errors, `--compiled`, etc. all reuse `runSource` as-is).
  2. **definition persistence across turns** — the one piece of state a REPL adds.

### Persistence is textual, by design

`Prog.body` (`Bang/Frontend/Surface.lean`) is ONE expression — a bang program has no top-level
"define and stop" form, only `let x = e1 in e2`. Nothing exposed to this LEAF lets us extend a
type/elaboration CONTEXT incrementally (`checkAndLower`/`elaborateToComp` are the only `public`
entries in `Bang.Frontend.TypeCheck`, and both take a whole source string). So a persisted
definition is `:let x = <expr>` — a REPL-only command, deliberately NOT bare `let x = <expr>`
(the surface's `let` always demands `in <body>`, so a body-less `let` would be a grammar change,
which this lane does not own) — and persistence itself is accomplished by re-wrapping every
subsequent turn's source in the accumulated bindings before handing the WHOLE string to
`runSource`, oldest-first so later definitions may shadow earlier ones:

    :let x = 3        →  binding "x" "3" recorded, nothing printed
    :let y = x + 1     →  binding "y" "x + 1" recorded (sees "x" via the wrap)
    y * 2              →  runs "let x = 3 in let y = x + 1 in y * 2" through runSource → 8

This is a real re-elaboration each turn (not a cache), so it is exactly as sound as the one-shot
CLI: any `#guard`/example in the build that pins `checkAndLower`/`runSource` behavior pins this too. -/

/-- One persisted REPL definition: `:let x = e` records `("x", "e")` (unparsed source text — the
wrap re-parses it fresh each turn, so a later `:let` shadowing an earlier name, or referencing one,
behaves exactly like nested `let`, textually). -/
abbrev ReplBinding := String × String

/-- Wrap a tail expression in all persisted bindings, OLDEST first, so `:let` order = nesting order
(a later binding can see an earlier one; `let b1 in let b2 in … in tail`). Pure string composition —
no parser/typechecker touched, so this needs no hook beyond `runSource`. -/
def wrapBindings (binds : List ReplBinding) (tail : String) : String :=
  binds.foldr (fun (x, e) acc => s!"let {x} = ({e}) in {acc}") tail

/-- `:let x = e` splits on the FIRST top-level `=`. We don't have the tokenizer (not `public` from
this leaf — see the missing-hook note in the REPL header comment), so this is a conservative
character split over `List Char` (sidesteps `String.Pos`/`String.Slice` entirely): the first `=`
that is not part of `==`/`<=`/`>=`/`!=` — those are the only multi-char operators containing `=` in
the surface grammar (`Bang/Frontend/Surface.lean` `BinOp`/tokenizer). Good enough for `:let name =
expr` (name is a bare identifier, never itself containing `=`); a false split inside a MORE deeply
nested comparison on the RHS is theoretically possible but `:let` bodies in practice are the same
shape as ordinary `let` right-hand sides. -/
def splitLetCmd (s : String) : Option (String × String) := Id.run do
  let chars := s.toList
  let n := chars.length
  for i in [0:n] do
    if chars[i]! == '=' then
      let prevOk := i == 0 || (chars[i-1]! != '<' && chars[i-1]! != '>' && chars[i-1]! != '=' && chars[i-1]! != '!')
      let nextOk := i + 1 >= n || chars[i+1]! != '='
      if prevOk && nextOk then
        let name := (String.ofList (chars.take i)).trimAscii.toString
        let rhs  := (String.ofList (chars.drop (i+1))).trimAscii.toString
        if name.length > 0 && rhs.length > 0 then
          return some (name, rhs)
  return none

/-- REPL help text for `:help`/`:?`. -/
def replHelp : String :=
  "commands:\n" ++
  "  :t <expr>, :type <expr>   show the checked type ! effect row of <expr>\n" ++
  "  :let <name> = <expr>      persist a definition for the rest of the session\n" ++
  "  :load <file>              run a file's contents as one turn (not persisted)\n" ++
  "  :help, :?                 this text\n" ++
  "  :q, :quit                 exit (also Ctrl-D / EOF)\n" ++
  "  <expr>                    evaluate against all persisted definitions and print the result"

/-- `:t <expr>` / `:type <expr>` — strip the recognized prefix, returning the tail (may be empty,
which the caller reports as a usage error). `":t"`/`":type"` are matched as exact prefixes (not
`startsWith ":t"`, which would also swallow `:type` under the shorter alias) so each reports its
OWN leftover tail correctly. -/
def stripTPrefix (line : String) : Option String :=
  if line.startsWith ":type" then some ((line.drop 5).toString.trimAscii.toString)
  else if line.startsWith ":t" then some ((line.drop 2).toString.trimAscii.toString)
  else none

/-- Evaluate one line of REPL input against the accumulated bindings, returning the (possibly
updated) bindings and the exit code of whatever ran (`0` for a silent `:let`/`:help`/comment/blank
line, so a piped session's exit code reflects only the last REAL evaluation — see `runRepl`). -/
def replStep (typecheck compiled : Bool) (binds : List ReplBinding) (line : String) :
    IO (List ReplBinding × UInt32) := do
  let line := line.trimAscii.toString
  if line.isEmpty then
    return (binds, 0)
  else if line == ":q" || line == ":quit" then
    return (binds, 0)  -- caller checks for this via the sentinel below; see runRepl
  else if line == ":help" || line == ":?" then
    IO.println replHelp; return (binds, 0)
  else if let some tail := stripTPrefix line then
    if tail.isEmpty then
      IO.eprintln "error: `:t`/`:type` expects `:t <expr>`"; return (binds, 1)
    else match Bang.TypeCheck.typeStringOfProg (wrapBindings binds tail) with
    | .ok tyStr  => IO.println tyStr; return (binds, 0)
    | .error msg => IO.eprintln s!"error: {msg}"; return (binds, 1)
  else if line.startsWith ":load" then
    let path := (line.drop 5).toString.trimAscii.toString
    if path.isEmpty then
      IO.eprintln "error: `:load` expects `:load <file>`"; return (binds, 1)
    else match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
    | none     => IO.eprintln s!"error: could not read file '{path}'"; return (binds, 1)
    | some src =>
      let code ← runSource typecheck compiled (wrapBindings binds src)
      return (binds, code)
  else if line.startsWith ":let" then
    match splitLetCmd (line.drop 4).toString with
    | none => IO.eprintln "error: `:let` expects `:let <name> = <expr>`"; return (binds, 1)
    | some (name, rhs) => return (binds ++ [(name, rhs)], 0)
  else if line.startsWith ":" then
    IO.eprintln s!"error: unknown command '{line}' (:help for the list)"; return (binds, 1)
  else
    let code ← runSource typecheck compiled (wrapBindings binds line)
    return (binds, code)

/-- The interactive/piped loop: read a line, `replStep`, repeat until `:q`/`:quit`/EOF. Works
identically whether stdin is a terminal or a pipe (`echo 'expr' | bang repl` runs each line and
exits on EOF) — `IO.FS.Stream.getLine` doesn't care which; that is what makes the non-interactive
(agent-driven) use case work for free, per the operator's agent-first framing. Tracks the exit
code of the LAST line that actually ran (silent lines don't overwrite it), so a piped single-expr
session's exit code matches `bang eval`'s for the same program. -/
partial def runRepl (typecheck compiled : Bool) : IO UInt32 := do
  let stdin ← IO.getStdin
  let isTty ← stdin.isTty
  let rec loop (binds : List ReplBinding) (lastCode : UInt32) : IO UInt32 := do
    if isTty then IO.eprint "bang> " -- prompt to STDERR so piped stdout stays clean for scripting
    let line ← stdin.getLine
    if line.isEmpty then
      return lastCode -- EOF (Ctrl-D / end of piped input)
    else
      let trimmed := line.trimAscii.toString
      if trimmed == ":q" || trimmed == ":quit" then
        return lastCode
      else
        let (binds', code) ← replStep typecheck compiled binds line
        loop binds' code
  loop [] 0

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
    else if cmd == "repl" then
      let compiled  := rest.contains "--compiled"
      let typecheck := !rest.contains "--no-typecheck"
      runRepl typecheck compiled
    else if cmd == "fmt" then
      -- no `--` flags this slice (no `-w`, per the team lead's hold); any non-positional is usage.
      match rest with
      | []      => runFmt (← (← IO.getStdin).readToEnd)   -- `bang fmt` with no file: read stdin
      | [arg]   => runFmt (← IO.FS.readFile ⟨arg⟩)
      | _       => IO.eprintln usage; pure 1
    else
      IO.eprintln usage; pure 1
  | _ => IO.eprintln usage; pure 1
