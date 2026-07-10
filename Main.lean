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

  THREE ENGINES (issue #6 · ADR-0094). The default engine is the PROVEN
  environment machine (`Bang.EnvMachine.evalE` + readback — v0.1.0's flip,
  dissolving #61). `--engine=oracle` runs the kernel oracle
  `Bang.Source.eval` (the reference + arbiter). `--compiled` runs `exec ∘ compile` — the
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
import Bang.Frontend.Diagnostics
import Bang.Frontend.Query
import Bang.Backend.AbstractMachine
import Bang.Backend.EnvMachine
import Bang.Witness.LawTest

open Bang
open Bang.Surface

/-- The `bang` CLI's SINGLE SOURCE OF TRUTH for its version string (issue #67/#69): every
version-facing surface (`--version`, and the v0.1.0 release-checklist's "self-identifying
binary" requirement) reads THIS constant — never a second hand-copied literal. Pre-tag: no
`git tag` has been cut yet (issue #69's checklist is still open), so this is the honest
pre-release marker; bump it here, in ONE place, at tag time. -/
def bangVersion : String := "0.1.0"

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

/-- The execution ENGINE (issue #6, ADR-0094). Three engines: `env` (the DEFAULT since v0.1.0 —
the environment machine `evalE`/`readback`, PROVEN ≡ the oracle at empty stores via
`Bang.EnvMachine.evalE_agrees_evalD` and differentially gated; the #61 fix), `oracle` (the kernel
`Source.eval` — the verified reference and the arbiter; sub-classifies failures), and `compiled`
(`exec ∘ compile`, the calculated machine, ADR-0016). -/
inductive Engine where
  | oracle
  | compiled
  | env
  deriving DecidableEq

/-- Parse the engine selector from the flag list: `--engine=env` / `--engine=compiled` / `--engine=oracle`,
with `--compiled` kept as a back-compat alias for `--engine=compiled` (issue #6's original spelling).
THE DEFAULT IS `env` (ADR-0094 A1's final step, operator-ruled at v0.1.0): the environment machine,
PROVEN ≡ the oracle (`evalE_agrees_evalD`, trusted-three) and differentially gated (9/9 corpus,
tools/check-examples-env.sh) — dissolving #61's per-step substitution cost (~300× on the json
dogfood). The substitution oracle stays one flag away (`--engine=oracle`) and remains the arbiter
in every differential gate. Unknown `--engine=<x>` falls to the default. -/
def parseEngine (flags : List String) : Engine :=
  if flags.contains "--engine=oracle" then .oracle
  else if flags.contains "--engine=compiled" || flags.contains "--compiled" then .compiled
  else .env

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
identically to the interpreted path (same `valPretty`).

The MESSAGE (issue #67) names what collapsed even though `exec` itself can't
distinguish the three — the oracle engine (`runComp`'s `.oom`/`.escapedCap`/`.stuck`
arms below) already sub-classifies the SAME program, so the message directs the
reader there for the specific cause rather than pretending `--compiled` can say more
than its own return type allows. -/
def runCompiled (c : Comp) : IO UInt32 := do
  match Bang.CalcVM.exec compiledFuel 0 (Bang.CalcVM.compile c []) [] [] with
  | some [.ret v] => IO.println (valPretty v); pure 0
  | _ =>
    IO.eprintln <|
      "error: compiled machine produced no value — it does not sub-classify which " ++
      "terminal collapsed (out of fuel, an escaped capability, or stuck); re-run " ++
      "without --compiled to see which one, via the oracle engine's specific message"
    pure 5

/-- Run a lowered `Comp` on the EXPERIMENTAL environment machine (`--engine=env`, ADR-0094): `evalE`/
`readback` at empty stores — exactly the premise shape of the proven headline `evalE_agrees_evalD`
(elaborator output is `WF`/`WFClos`/`HandlerWF`/`ScopedC` by the CK contract). Returns the value on a
first-order returner; every other terminal (`raise`/function-terminal/oom/stuck) collapses to a single
fail-loud line — the experimental engine does NOT sub-classify (that is what the oracle is for). -/
def runEnv (c : Comp) : IO UInt32 := do
  match Bang.EnvMachine.runE defaultFuel c with
  | .done v => IO.println (valPretty v); pure 0
  | _ =>
    IO.eprintln <|
      "error: the env engine (the default, ADR-0094) produced no first-order value — it collapses " ++
      "out-of-fuel / escaped-capability / raise / function-terminal / stuck into one outcome; " ++
      "re-run with --engine=oracle (the verified reference) for the specific diagnosis"
    pure 5

/-- Run a lowered `Comp` on the selected engine (§ issue #6, ADR-0094): the kernel oracle `Source.eval`
(default), the calculated machine `exec ∘ compile` (`--engine=compiled`/`--compiled`), or the experimental
environment machine `evalE`/`readback` (`--engine=env`). `done` → stdout + 0; every failure outcome →
a clear stderr line + a distinct nonzero code (fail-loud, ADR-0063).

MESSAGES (issue #67, operator ruling 2026-07-09): the exit code stays the machine contract;
each non-zero outcome ALSO gets a one-line stderr explanation naming the outcome, the likely
cause, and the next step, matching `check --json`'s plain-English tone. `stuck` is reachable
ONLY via `--no-typecheck` (`type_safety`: a well-typed ⊥-row program never gets there), so its
message can unconditionally point at the type gate being off — not a flag-dependent guess. -/
def runComp (engine : Engine) (c : Comp) : IO UInt32 := do
  match engine with
  | .compiled => runCompiled c
  | .env      => runEnv c
  | .oracle   =>
  match Bang.Source.eval defaultFuel c with
  | .done v      => IO.println (valPretty v); pure 0
  | .oom         =>
    IO.eprintln <|
      s!"error: out of fuel (ceiling {defaultFuel} steps) — the program may diverge, or hit " ++
      "the recursion-cost cliff (issue #61); a well-typed program that should terminate is " ++
      "likely paying substitution cost per step rather than genuinely looping"
    pure 2
  | .escapedCap  =>
    IO.eprintln <|
      "error: a capability escaped its handler — it was forced (`$`/`!`) after the `with`/" ++
      "`atomically`/`state` block that installed it had already returned; this is a defined " ++
      "fail-loud terminal (ADR-0063), not corruption — move the force inside the handler's " ++
      "scope, or restructure so the capability doesn't outlive it"
    pure 3
  | .stuck       =>
    IO.eprintln <|
      "error: stuck (ill-formed program) — this is only reachable with --no-typecheck; the " ++
      "type gate was off, so an ill-typed term ran anyway (type_safety guarantees a well-typed " ++
      "program never reaches this outcome) — drop --no-typecheck to catch it as a type error instead"
    pure 4

/-! ## Module resolution (ADR-0093 D1) — file = module, `import`/`use` at the top of a file.

Reading ANOTHER file is inherently IO, so this lives here (not `Bang.Frontend`, which is a pure
leaf) — the pure half (`mergeModules`, `Bang.TypeCheck`) already exists and takes an ALREADY-
RESOLVED `List (String × Prog)`; this section's only job is to WALK the import graph and produce
that list, loudly erroring on a missing file or a cycle before `mergeModules` ever runs. -/

/-- Resolve `import name`/`use name` module NAME to a file path: try `<dir of the importing
file>/name.bang` first, then `<root>/name.bang` (D1's fixed, documented order). `none` on a miss in
BOTH — the caller names both probed paths in its error (a miss must be loud AND specific, ADR-0046:
"the fix is obvious from the message" is the bar, not just "file not found"). -/
def resolveModulePath (root : System.FilePath) (importingDir : System.FilePath) (modName : String) :
    IO (Option System.FilePath) := do
  let sameDir := importingDir / s!"{modName}.bang"
  if ← sameDir.pathExists then return some sameDir
  let atRoot := root / s!"{modName}.bang"
  if ← atRoot.pathExists then return some atRoot
  return none

/-- The accumulated state of one resolution walk: `resolved` maps a module name to its PARSED
(unqualified) `Prog`, built bottom-up (a module is added only after everything IT imports is
already resolved) so `resolved`'s LIST ORDER is already the dependency-first topological order
`mergeModules` needs. `visiting` is the current DFS path (module names, root-to-here) — a name
reappearing in `visiting` is the cycle (ADR-0076's acyclic-DAG pin, enforced here since the
resolver is where the actual file graph is walked). -/
structure ResolveState where
  resolved : List (String × Prog) := []
  visiting : List String := []

/-- Recursively resolve `modName`'s transitive imports/uses, then `modName` itself, into `st`.
Fuel-bounded (not structural — the import graph's depth isn't visible to Lean's termination
checker without threading a well-founded proof no v1 program needs; a real cycle is caught by
`visiting` LONG before fuel would ever matter at realistic project sizes, matching the file's own
`bigFuel`-idiom precedent elsewhere in the codebase). -/
partial def resolveModule (root : System.FilePath) (modName : String) (path : System.FilePath)
    (st : ResolveState) : IO (Except String ResolveState) := do
  if (st.resolved.map Prod.fst).contains modName then return .ok st   -- already resolved (diamond import)
  if st.visiting.contains modName then
    return .error s!"import cycle: {String.intercalate " → " (st.visiting ++ [modName])}"
  let some src ← (do let s ← IO.FS.readFile path; pure (some s)) <|> pure none
    | return .error s!"could not read module '{modName}' at '{path}'"
  match Bang.Surface.parseProg src with
  | .error m => return .error s!"module '{modName}' ({path}): parse error: {m}"
  | .ok prog =>
      let dir := path.parent.getD root
      let mut st' := { st with visiting := st.visiting ++ [modName] }
      for imp in prog.imports do
        match ← resolveModule root imp.modName (Id.run <| dir / s!"{imp.modName}.bang") st' with
        | .error e  => return .error e
        | .ok stNew => st' := stNew
      for u in prog.uses do
        match ← resolveModule root u.modName (Id.run <| dir / s!"{u.modName}.bang") st' with
        | .error e  => return .error e
        | .ok stNew => st' := stNew
      return .ok { st' with resolved := st'.resolved ++ [(modName, prog)], visiting := st.visiting }

/-- ADR-0093 D5's entry rule, applied to the FULLY MERGED entry `Prog` (so it sees the right-most
picture: every imported decl is already folded in by the time this runs, but a `main` decl only
D5 cares about must be the ENTRY FILE's OWN — an imported module cannot silently become the
program via a same-named `main` it happens to export, matching "the runtime, not an importer,
invokes it"). Four cases: `main` present + library mode (no trailing expr) ⟹ PROGRAM mode — the
body becomes a bare reference to `main` (CBPV: `Surf.lett`-bound names are directly available, no
`$`-force needed, matching how every OTHER `let`-decl reference in the corpus already reads); `main`
absent + script mode (a real trailing expr) ⟹ unchanged (today's whole corpus); BOTH present ⟹ a
loud error (ADR-0046, no silent precedence); NEITHER ⟹ a pure library file — running it directly is
a loud error naming that fact, not a silent "prints 0". -/
def applyEntryRule (p : Prog) : Except String Prog :=
  let hasMain := p.decls.any (fun d => match d with
    | .letD n _ _ | .letRecD n _ _ => n == "main"
    | _ => false)
  match hasMain, p.isLibrary with
  | true,  true  => .ok { p with body := Surf.var "main", isLibrary := false }   -- program mode
  | false, false => .ok p                                                        -- script mode, unchanged
  | true,  false => .error "both a `main` decl and a trailing expression are present — ADR-0093 D5 forbids silent precedence (remove one)"
  | false, true  => .error "this file is a library (no `main` decl, no trailing expression) — nothing to run; import it from an entry file instead"

/-- The full D1 resolution + D2/D3/D4 merge, from an entry FILE: parse it, resolve every
`import`/`use` it names (transitively, same-dir-then-root, cycle-checked), then `mergeModules` the
result into ONE flat `Prog` ready for `checkAndLowerProg`. A resolved import's OWN path is
re-probed via `resolveModulePath` (not the naive `dir/name.bang` `resolveModule` builds directly)
ONLY at the top level, matching D1's exact documented search order; nested imports resolve relative
to THEIR OWN file's directory (the natural reading of "same directory as the importing file" — a
transitively-imported module's imports are relative to IT, not the original entry file). The D5
entry rule (`applyEntryRule`) is applied LAST, to the fully-merged result. -/
def resolveEntryFile (path : String) : IO (Except String Prog) := do
  let entryPath : System.FilePath := ⟨path⟩
  let root ← IO.currentDir
  let some entrySrc ← (do let s ← IO.FS.readFile entryPath; pure (some s)) <|> pure none
    | return .error s!"could not read file '{path}'"
  match Bang.Surface.parseProg entrySrc with
  | .error m => return .error s!"parse error: {m}"
  | .ok entryProg =>
      if entryProg.imports.isEmpty && entryProg.uses.isEmpty then return applyEntryRule entryProg
      let dir := entryPath.parent.getD root
      let mut st : ResolveState := {}
      for imp in entryProg.imports do
        match ← resolveModulePath root dir imp.modName with
        | none =>
            let probed1 := dir / s!"{imp.modName}.bang"
            let probed2 := root / s!"{imp.modName}.bang"
            return .error s!"cannot find module '{imp.modName}' — probed '{probed1}' and '{probed2}'"
        | some found =>
            match ← resolveModule root imp.modName found st with
            | .error e  => return .error e
            | .ok stNew => st := stNew
      for u in entryProg.uses do
        match ← resolveModulePath root dir u.modName with
        | none =>
            let probed1 := dir / s!"{u.modName}.bang"
            let probed2 := root / s!"{u.modName}.bang"
            return .error s!"cannot find module '{u.modName}' — probed '{probed1}' and '{probed2}'"
        | some found =>
            match ← resolveModule root u.modName found st with
            | .error e  => return .error e
            | .ok stNew => st := stNew
      match Bang.TypeCheck.mergeModules st.resolved entryProg with
      | .error e     => return .error e
      | .ok merged   => return applyEntryRule merged

/-- Run one source string through the whole pipeline, printing the outcome and returning the process
exit code. `typecheck` selects the pipeline (ADR-0076 #51):

  * DEFAULT — parse (located) → **TYPE-CHECK (reject on error)** → lower → run (`checkAndLower`).
    An ill-typed program is caught as a TYPE ERROR before it runs, so the run path and the `#guard`
    gate share ONE type gate (SSoT) and `type_safety` (well-typed ⟹ never stuck) is real for users.
    A parse error is LOCATED (`error at line:col: …`); a type/elab error prints the checker's message.
  * `--no-typecheck` — the raw erase-and-run path (`elaborateToComp`): parse → elaborate → lower →
    run, NO type gate. Kept for oracle/differential testing (running an ill-typed program to observe
    the defined runtime `stuck`/`escapedCap`, ADR-0063).

`engine` selects only the execution ENGINE and is orthogonal to `typecheck`. -/
def runSource (typecheck : Bool) (engine : Engine) (src : String) : IO UInt32 := do
  if typecheck then
    match Bang.TypeCheck.checkAndLower src with
    | .error (m, some sp) => IO.eprintln s!"error at {sp.loc}: {m}"; pure 1
    | .error (m, none)    => IO.eprintln s!"error: {m}"; pure 1
    | .ok c               => runComp engine c
  else
    match Bang.TypeCheck.elaborateToComp src with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp engine c

/-- Run an already-RESOLVED-and-merged `Prog` (ADR-0093 D1-D4 — `resolveEntryFile`'s output) through
the SAME two pipelines `runSource` offers for a single file: DEFAULT type-checked
(`checkAndLowerProg`) or `--no-typecheck` raw erase-and-run (`elaborateToCompProg`), then `runComp`.
No located errors either way (see `checkAndLowerProg`'s doc comment) — a resolution/parse failure
is already located by `resolveEntryFile` itself, before this runs. -/
def runResolvedProg (typecheck : Bool) (engine : Engine) (prog : Prog) : IO UInt32 := do
  if typecheck then
    match Bang.TypeCheck.checkAndLowerProg prog with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp engine c
  else
    match Bang.TypeCheck.elaborateToCompProg prog with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp engine c

/-- Run `bang fmt`: format a whole program (decls + body, `Bang.Format.fmtProg`) and print the
canonical form to stdout. `.error` → stderr + exit 1, the SAME convention `runSource`'s parse-error
arm uses (a fmt failure IS a parse failure — `fmtProg` round-trips through the ordinary parser,
ADR-0046: never a silent guess on unparsable input). No `-w` (in-place write) this slice — print
only; in-place writing is a separate decision the team lead is holding. -/
def runFmt (src : String) : IO UInt32 := do
  match Bang.Format.fmtProg src with
  | .error e  => IO.eprintln s!"error: {e}"; pure 1
  | .ok out   => IO.println out; pure 0

/-- Run `bang check --json`: `Bang.Diagnostics.checkJson` printed as exactly ONE JSON object on
stdout, newline-terminated (via `IO.println`), nothing else on stdout — agent-facing (#59). Exit
code is `ok:true → 0`, `ok:false → 1` (diagnostics present). Cheap re-parse of `ok` from the
rendered string (`"ok":true` is a fixed prefix `checkJson` always emits first, ADR-46: the schema
IS the contract) rather than exposing a second entry point from `Diagnostics` — keeps `checkJson`'s
public surface at ONE function. -/
def runCheckJson (src : String) : IO UInt32 := do
  let out := Bang.Diagnostics.checkJson src
  IO.println out
  pure (if out.startsWith "{\"ok\":true" then 0 else 1)

/-- Run `bang check` (human-readable, no `--json`): the SAME typed pipeline (`checkAndLower`) the
default `bang run`/`eval` use, reporting only PASS/FAIL — no value is produced (unlike `run`,
`check` never evaluates). Mirrors `runSource`'s DEFAULT arm's error rendering (`error at L:C: …` /
`error: …`) so a human reading `bang check`'s failure sees the identical message `bang run` would
have failed with. -/
def runCheckHuman (src : String) : IO UInt32 := do
  match Bang.TypeCheck.checkAndLower src with
  | .error (m, some sp) => IO.eprintln s!"error at {sp.loc}: {m}"; pure 1
  | .error (m, none)    => IO.eprintln s!"error: {m}"; pure 1
  | .ok _               => IO.println "ok"; pure 0

/-- One `ok:false` diagnostic JSON object for the `Prog`-taking check path (`code` always `"type"`,
`span` always `null` — see `runCheck`'s doc comment for why: no stage split, no source text to
locate into). Built with `++` (not `s!"..."`), matching `Diagnostics.spanJson`/`Diagnostic.toJson`'s
own convention — Lean's string interpolation escapes a literal `{` as `\{`, not `{{`, which makes a
hand-written JSON-brace literal read backwards; plain concatenation sidesteps the ambiguity entirely
(the SAME reason those two functions avoid `s!`). -/
def checkFailJson (msg : String) : String :=
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"type\",\"msg\":" ++
    Bang.Diagnostics.jsonStr msg ++ ",\"span\":null}]}"

/-- `bang check [FLAGS] [<file.bang>]` (issue #59): type-check ONLY (no run), human-readable by
default or `--json` for the agent-facing structured schema (`Bang.Diagnostics`). Reads a file if
given, else stdin (mirrors `fmt`'s file-or-stdin convention).

RESOLVER-AWARE (ADR-0093 follow-up ruling, 2026-07-09) — for a GENUINE multi-file program only
(#75 fix, 2026-07-10): a FILE argument with a nonempty `import`/`use` header goes through the SAME
`resolveEntryFile` (import/use resolution + D5 entry-rule) `bang run` uses — the agent-first
rationale is direct: `check --json` is the tool an agent actually calls to lint a program, so if it
can't see imports, an agent cannot lint a multi-file project at all. The resolved `Prog` is checked
DIRECTLY via `TypeCheck.checkAndLowerProg` (the SAME `Prog`-taking pipeline `run` uses) — NOT
re-stringified through `Bang.Format.showProg` and re-parsed by the string-taking `checkJson`. This
print-then-reparse route was tried first and found UNSOUND: `resolveEntryFile` already applies D5's
entry rule (`applyEntryRule`, rewriting `body := Surf.var "main"` when a `main` decl exists), so the
rendered text carries BOTH the `let main = …` decl AND a separate trailing `main` reference — a
shape no hand-authored file has, and one the grammar cannot always tell apart from an application
(`let main = 0` then a lone `main` line re-tokenizes as `0 main`, silently parsed as one expression,
per the SAME literal-adjacency class `Prog.isLibrary` already guards elsewhere — `#guard`ed below as
a regression). Calling `checkAndLowerProg` on the in-memory `Prog` sidesteps the round-trip
entirely — exactly the trade `checkAndLowerProg`'s own doc comment already recommends over
print-then-reparse. The cost: no `Diagnostics`-schema `Diagnostic`/`span` structure for this path (a
merged multi-file `Prog` has no contiguous source `checkAndLowerProg` could span into either — see
its doc comment), so the JSON here is hand-assembled to the SAME schema `checkJson` emits (`code`
always `"type"`, `span` always `null` — `checkAndLowerProg` gives no stage/location split), reusing
`Bang.Diagnostics.jsonStr` for the one string that needs JSON-escaping (the error message) rather
than a second hand-rolled escaper. `Bang.Frontend.Diagnostics` needed no NEW entry point — `jsonStr`
was already there, just previously private; see its doc comment for why marking it `public` was the
minimal correct move over a second implementation. STDIN input is NOT resolver-aware (no file path
to resolve relative to, matching `eval`'s same limitation on `bang run`) and stays on the ORIGINAL
string-based `checkJson`/`checkAndLower` path (full span support, unaffected by any of the above).

SINGLE-FILE FAST PATH (#75 fix, 2026-07-10 — the span regression this closes): a file with NO
`import`/`use` header never needs `resolveEntryFile`/`checkAndLowerProg` at all — it stays on the
exact string-based `checkJson`/`checkAndLower` pipeline stdin already uses, which is where FULL
`Diagnostics`-schema spans (parse AND type/elaboration) come from. Round-1 of the stranger test
praised these exact spans; routing every FILE argument through the resolver (even an import-free
one) silently traded them for `span:null` on every file-input diagnostic — a real regression, not
the documented v1 limitation (that limitation is about content pulled in via `import`/`use`, which
genuinely has no single contiguous source a `Span` can index into; a lone file has exactly one). The
test is `Bang.Surface.parseProgLocated src`'s own header fields: a PARSE failure is reported
directly from THIS located call (full span, `code:"parse"` — fixing #75's mislabel, since the
resolver's own internal parse used the un-located `parseProg`); a successful parse with an empty
`imports`/`uses` header stays on the string pipeline (`checkJson`/`checkAndLower`, full span for
type errors too); only a header that NAMES an import/use falls through to `resolveEntryFile` below
— the genuine multi-file case the documented limitation covers.

KNOWN v1 LIMITATION (documented here + the usage text, follow-up tracked under this ADR's own
issue): a resolved multi-file program's diagnostic never carries a `span` (`null` always) — no
line/col at all, not even a merged-source coordinate, since the `Prog`-taking pipeline has no source
text to index into. File-aware span mapping (spans that name which file, with per-file coordinates)
is a named follow-up, not solved by this ruling. This grant covers ONLY programs that actually pull
in `import`/`use` content — see the single-file fast path above for why a lone file doesn't need it.

EXIT CODES (the `--json` contract; the human path reuses 0/1 and never emits 2 — a human already
sees the read failure as the SAME uncaught-IO-exception report every other subcommand gives): `0`
ok, `1` diagnostics present OR a resolution failure (missing import, cycle, private access — the
SAME exit `bang run` gives a resolution error, ADR-0093 D1-D5), `2` TOOL error (the ENTRY file
itself could not be read) — caught HERE via `<|>` (the `:load` idiom, §REPL) so it lands on stderr
with NOTHING written to stdout, never folded into the JSON (a tool error is not a diagnostic — the
pipeline never even ran). -/
def runCheck (json : Bool) (file : Option String) : IO UInt32 := do
  match file with
  | none      =>
    let src ← (← IO.getStdin).readToEnd
    if json then runCheckJson src else runCheckHuman src
  | some path =>
    match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
    | none     => IO.eprintln s!"error: could not read file '{path}'"; pure 2
    | some src =>
        match Bang.Surface.parseProgLocated src with
        -- header itself doesn't parse: located, full span, code "parse" (#75) — no resolver needed,
        -- parsing precedes import resolution regardless of what `resolveEntryFile` would have done.
        | .error (m, sp) =>
            if json then IO.println (Bang.Diagnostics.parseFailJson m sp)
            else match sp with
              | some s => IO.eprintln s!"error at {s.loc}: {m}"
              | none   => IO.eprintln s!"error: {m}"
            pure 1
        | .ok headerProg =>
          -- single-file fast path (#75): no import/use header ⟹ the full-span string pipeline
          -- (`checkJson`/`checkAndLower`, the SAME one stdin uses), not the resolver.
          if headerProg.imports.isEmpty && headerProg.uses.isEmpty then
            if json then runCheckJson src else runCheckHuman src
          else
            -- genuine multi-file program: resolver + `Prog`-taking pipeline, `span:null` grant intact.
            match ← resolveEntryFile path with
            | .error e   =>
                if json then IO.println (checkFailJson e) else IO.eprintln s!"error: {e}"
                pure 1
            | .ok merged =>
                match Bang.TypeCheck.checkAndLowerProg merged with
                | .error e =>
                    if json then IO.println (checkFailJson e) else IO.eprintln s!"error: {e}"
                    pure 1
                | .ok _ =>
                    if json then IO.println "{\"ok\":true,\"diagnostics\":[]}" else IO.println "ok"
                    pure 0

/-! ## `bang query <op>` (#80) — the agent LSP as stateless CLI subcommands.

Every op is `--json`-only in v1 (`Bang.Query`'s own module header: agents are the audience, a
human rendering may piggyback later). RESOLVER-AWARE for the SAME reason `check --json` is (#75's
ruling, applied here at first landing rather than retrofitted): `symbols`/`type`/`effects`/`def`/
`refs` all take a FILE, and an agent querying a multi-file project needs its imports visible —
mirrors `runCheck`'s exact single-file-fast-path/resolver split (`Bang.Query`'s `*JsonP` siblings
beside its `src`-taking entries are the `checkAndLowerProg`-beside-`checkAndLower` split applied to
this module). `laws` stays STRING-only (no `Prog`-taking sibling exists — `lawInstancesOf` itself
has none, matching `runTest`'s own documented non-resolver-aware precedent: "no multi-file
law-discovery need has arisen yet"). -/

/-- Read `file`'s source (or stdin if `none`), returning `(src, headerProg)` — `headerProg` is the
LOCATED parse used by every op below to decide fast-path vs resolver (mirrors `runCheck`'s own
`parseProgLocated` peek). TOOL error (unreadable file — `none` never hits this arm, `readToEnd`
doesn't fail the way a missing path does) reports on STDERR with NOTHING on stdout, exit `2` —
mirrors `check --json`'s own convention exactly ("a tool error is not a diagnostic — the pipeline
never even ran"). A PARSE error, by contrast, IS an op-level answer: `errorJsonOk` on stdout,
exit `1`. -/
def readQuerySrc (file : Option String) : IO (Except UInt32 (String × Bang.Surface.Prog)) := do
  let srcRes ← match file with
    | none      => some <$> (← IO.getStdin).readToEnd
    | some path => (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none
  match srcRes with
  | none     =>
      match file with
      | some path => IO.eprintln s!"error: could not read file '{path}'"
      | none      => pure ()
      pure (.error 2)
  | some src =>
      match Bang.Surface.parseProgLocated src with
      | .error (m, _) => IO.println (Bang.Query.errorJsonOk m); pure (.error 1)
      | .ok headerProg => pure (.ok (src, headerProg))

/-- Resolve `(src, headerProg, file)` to the `Prog` a resolver-aware query op should run against:
the single-file fast path (no `import`/`use` header ⟹ just re-parse `src` directly, matching
`Bang.Query`'s own `src`-taking entries) or the genuine multi-file resolver (`resolveEntryFile`,
the SAME D1-D5 machinery `bang run`/`check --json` use) when a `file` path is available to resolve
relative to (STDIN has none — the SAME limitation `bang run`'s own `eval` has, `runCheck`'s doc
comment). On the resolver path, `.error` is a resolution/merge failure (missing import, cycle,
private access) — printed as `errorJsonOk` and mapped to exit `1`, matching `check --json`'s SAME
failure's exit code (ADR-0093 D1-D5). -/
def resolveQueryProg (src : String) (headerProg : Bang.Surface.Prog) (file : Option String) :
    IO (Except UInt32 Bang.Surface.Prog) := do
  if headerProg.imports.isEmpty && headerProg.uses.isEmpty then
    match Bang.Surface.parseProgLocated src with
    | .ok p         => pure (.ok p)
    | .error (m, _) => IO.println (Bang.Query.errorJsonOk m); pure (.error 1)
  else
    match file with
    | none      => pure (.ok headerProg)   -- stdin, no path to resolve relative to (same as `eval`'s limitation)
    | some path =>
        match ← resolveEntryFile path with
        | .error e   => IO.println (Bang.Query.errorJsonOk e); pure (.error 1)
        | .ok merged => pure (.ok merged)

/-- Print `json` and return `0` — the uniform success tail every `runQuery*` arm shares (an op's
OWN `errorJsonOk`/`ok:false` embeds its failure in the JSON body already; exit is still `0` at
THIS layer since the tool ran and produced a well-formed answer — matching how `symbols`'s
per-decl `typeError` doesn't fail the whole call. An op that fails structurally, like `def`'s "no
such decl", is `{"ok":false,...}` on stdout but STILL exit 0 here — the CALLER inspects `ok`, the
same convention a `grep`-style tool uses; only a genuine tool/resolution/parse failure, caught
upstream in `readQuerySrc`/`resolveQueryProg`, uses a nonzero exit). -/
def printQueryOk (json : String) : IO UInt32 := IO.println json *> pure 0

/-- `bang query dump <file>` / stdin — THE key operation (#80's operator refinement): the COMPLETE
fact base in one export, so a caller composes ARBITRARY queries over it (a `jq`/`python`/Lean
script) rather than waiting on a new fixed verb. SINGLE-FILE/STDIN fast path uses `Query.dumpJson`
directly (full law facts — real source text `lawInstancesOf` can re-derive from); the MULTI-FILE
resolver path uses `Query.dumpJsonP` on the merged `Prog` (empty `"laws"` array — the SAME
documented v1 grant `check --json`'s own multi-file path carries, since a merged `Prog` has no
single contiguous source `lawInstancesOf` could re-derive law bodies from). Written directly
(not via `resolveQueryProg`, which always RE-PARSES from `src` and would silently drop the
fast-path's law-fact advantage) so the single-file route keeps `src` all the way to `dumpJson`. -/
def runQueryDump (file : Option String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      if headerProg.imports.isEmpty && headerProg.uses.isEmpty then
        printQueryOk (Bang.Query.dumpJson src)
      else
        match file with
        | none      => printQueryOk (Bang.Query.dumpJsonP headerProg)   -- stdin, no resolver path
        | some path =>
            match ← resolveEntryFile path with
            | .error e   => IO.println (Bang.Query.errorJsonOk e); pure 1
            | .ok merged =>
                -- `mergeModules` clears `imports`/`uses` on its OWN merged output (D1-D4's flat
                -- decl-list convention) — splice the ENTRY file's own header back on so `dump`'s
                -- `"imports"`/`"uses"` fields report what the program's source ACTUALLY declares,
                -- not an artifact of the merge (a real fidelity gap `dumpJsonP` alone can't see,
                -- since it only ever receives the merged `Prog`).
                printQueryOk (Bang.Query.dumpJsonP { merged with imports := headerProg.imports, uses := headerProg.uses })

/-- `bang query symbols <file>` / stdin — every top-level decl's outline. -/
def runQuerySymbols (file : Option String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg file with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.symbolsJsonP p)

/-- `bang query type <file> <name>` — type + row of one binding. -/
def runQueryType (file : Option String) (name : String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg file with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.typeJsonP p name)

/-- `bang query effects <name> [file]` — the row of one binding. -/
def runQueryEffects (file : Option String) (name : String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg file with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.effectsJsonP p name)

/-- `bang query laws <file>` — string-only (no resolver; see this section's header). -/
def runQueryLaws (file : Option String) : IO UInt32 := do
  let src ← match file with
    | none      => (← IO.getStdin).readToEnd
    | some path =>
      match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
      | none   => IO.eprintln s!"error: could not read file '{path}'"; return 2
      | some s => pure s
  printQueryOk (Bang.Query.lawsJson src)

/-- `bang query def <name> <file>` — the decl defining `name`. -/
def runQueryDef (file : Option String) (name : String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg file with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.defJsonP p name)

/-- `bang query refs <name> <file>` — every decl referencing `name`. -/
def runQueryRefs (file : Option String) (name : String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg file with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.refsJsonP p name)

/-- Default sample count and RNG seed for `bang test` — fixed (not randomized per-run) so a CI
run is byte-reproducible (`Bang.LawTest.genIntSamples`'s own documented requirement: "the SAME
seed reproduces the SAME samples"). 30 samples is a generous default for the Int-tuple shrinking
`Bang.LawTest` already does per-law; a future `--samples N`/`--seed N` flag is the natural
follow-up if a law needs more, not added speculatively here. -/
def testSamples : Nat := 30
def testSeed : Nat := 7

/-- Render one `NamedOutcome` as a human-readable report line + whether it counts as a PASS for
the exit-code tally. `PASS`/`FAIL`/`ERROR` mirror `check --json`'s plain-English severity
naming; a counterexample/eval-stuck witness prints via `renderWitness` WITHOUT parameter names
(`NamedOutcome` doesn't carry `params` — only `LawInstance` does, and `runLawsFromSource`
doesn't surface it back to the caller — a positional witness list is still actionable and this
avoids widening `NamedOutcome`'s public shape for a cosmetic label). -/
def renderOutcome (o : Bang.LawTest.NamedOutcome) : String × Bool :=
  let name := s!"{o.traitName}.{o.lawName}"
  match o.outcome with
  | .holds n           => (s!"✓ {name} — PASS ({n} samples)", true)
  | .counterexample ws => (s!"✗ {name} — FAIL — counterexample {ws}", false)
  | .untypeable m       => (s!"✗ {name} — ERROR — {m}", false)
  | .evalStuck ws       => (s!"✗ {name} — STUCK — witness {ws} did not evaluate to a Bool", false)

/-- `bang test [<file.bang>]` (#60's CLI wiring): discover EVERY trait-law instance in a program
(`Bang.LawTest.runLawsFromSource`, the landed #60 discovery seam) and sample-check each one,
reporting per-law PASS/FAIL/ERROR/STUCK. Reads a file if given, else stdin (mirrors `fmt`/`check`'s
file-or-stdin convention). NOT resolver-aware (like `eval`/stdin `check`, not `run`'s file path) —
`Bang.LawTest.runLawsFromSource` operates on a raw decls-string, and no multi-file law-discovery
need has arisen yet; a resolver-aware upgrade is the natural follow-up if one does.

DECLS-ONLY INPUT, ENFORCED (a real footgun found while writing this slice's own manual test):
`runLawsFromSource` appends ITS OWN throwaway `0` body for discovery, and its per-sample test
programs splice `progPrelude` (== the WHOLE input string) directly against a SEPARATE generated
readback body. A file that ALREADY ends in a trailing expression (an ordinary bang program's
usual shape — even a bare `0`) glues onto that spliced body as a second, adjacent expression —
the SAME literal-adjacency trap `runCheck`'s own doc comment warns about elsewhere — and every
law silently reports STUCK (`0 (let a = ... in ...)`, applying a literal to a computation) with
NO indication the input shape, not the law, is the problem. Pre-checked here via `parseProg` +
`Prog.isLibrary` (true ⟺ no trailing body) BEFORE ever calling `runLawsFromSource`, so the error
names the actual cause instead of a confusing blanket STUCK on every discovered law.

EXIT CODES: `0` every discovered law holds (including the vacuous "no laws found" case — #60's own
`runLawsFromSource "" ...` guard: zero laws is not a failure); `1` at least one law
FAILED/ERRORED/STUCK, the input has a trailing body (the decls-only check above), OR the source
didn't even elaborate for discovery (`lawInstancesOf`'s own error, e.g. malformed decls) — the
SAME "usage/parse/elaboration error" code every other subcommand uses for a source-level failure;
`2` the file could not be read (the `check`/`:load` convention: a tool error is not a diagnostic). -/
def runTest (file : Option String) : IO UInt32 := do
  let src ← match file with
    | none      => (← IO.getStdin).readToEnd
    | some path =>
      match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
      | none   => IO.eprintln s!"error: could not read file '{path}'"; return 2
      | some s => pure s
  match Bang.Surface.parseProg src with
  | .error e => IO.eprintln s!"error: parse error: {e}"; return 1
  | .ok p    =>
    if !p.isLibrary then
      IO.eprintln <|
        "error: `bang test` expects a DECLS-ONLY file (trait/impl declarations, no trailing " ++
        "expression) — the runner supplies its own throwaway body internally; a trailing " ++
        "expression here silently corrupts every discovered law's test program. Remove the " ++
        "trailing expression (the file should end after the last decl's closing brace)."
      return 1
    match Bang.LawTest.runLawsFromSource src testSamples testSeed with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok []   => IO.println "no trait laws found (0 discovered)"; pure 0
    | .ok outcomes =>
      let rendered := outcomes.map renderOutcome
      for (line, _) in rendered do IO.println line
      let allHold := rendered.all Prod.snd
      let n := outcomes.length
      let passed := (rendered.filter Prod.snd).length
      IO.println s!"──────────────────────────────"
      IO.println s!"laws: {passed}/{n} passed"
      pure (if allHold then 0 else 1)

def usage : String :=
  "bang — the lang-bang runner\n\n" ++
  "USAGE:\n" ++
  "  bang run  [FLAGS] <file.bang>      run a bang program from a file\n" ++
  "  bang eval [FLAGS] \"<surface expr>\"  run a surface expression directly\n" ++
  "  bang repl [FLAGS]                  interactive read-eval-print loop (issue #7)\n" ++
  "  bang fmt  [<file.bang>]            print the canonical form (issue #58); reads stdin if no file\n\n" ++
  "  bang check [FLAGS] [<file.bang>]   type-check only, no run (issue #59); reads stdin if no file\n" ++
  "             --json                  emit agent-facing structured JSON diagnostics on stdout\n\n" ++
  "  bang test [<file.bang>]            discover + sample-check every trait law (issue #60);\n" ++
  "                                     reads stdin if no file; reports per-law PASS/FAIL/ERROR/STUCK.\n" ++
  "                                     INPUT MUST BE DECLS-ONLY (no trailing expression) — the\n" ++
  "                                     runner supplies its own body internally.\n\n" ++
  "  bang query <op> ...                LSP-class operations as stateless CLI subcommands (issue #80);\n" ++
  "                                     ALWAYS JSON on stdout (agents are the audience — no --json flag).\n" ++
  "                                     THE KEY OP is `dump` — the complete fact base in one export, so\n" ++
  "                                     you compose ARBITRARY queries in jq/python/etc rather than\n" ++
  "                                     waiting on a new fixed verb; every verb below is a THIN\n" ++
  "                                     PROJECTION of the same facts `dump` exports (schema in\n" ++
  "                                     docs/reference/language.md's `bang query` section).\n" ++
  "    bang query dump [<file.bang>]           THE complete fact base: every decl (name/kind/type/\n" ++
  "                                             row/visibility), every name-ref edge, every law\n" ++
  "                                             instance, the import/use header — one JSON object\n" ++
  "    bang query symbols [<file.bang>]        outline: every top-level decl, its kind, type ! row\n" ++
  "                                             (dump's own \"decls\" field, narrowed)\n" ++
  "    bang query type <file.bang> <name>      the checked type ! row of one top-level binding\n" ++
  "    bang query effects <name> [<file.bang>] the effect ROW alone of one top-level binding\n" ++
  "    bang query laws [<file.bang>]           every trait-law × impl instance (issue #60 seam)\n" ++
  "    bang query def <name> <file.bang>       the decl that defines <name>\n" ++
  "    bang query refs <name> <file.bang>      every decl whose body mentions <name>\n" ++
  "                                             (dump's own \"refs\" edge list, filtered to <name>)\n" ++
  "                                     `dump`/`symbols`/`type`/`effects`/`def`/`refs` read stdin if\n" ++
  "                                     no <file.bang> is given (except `type`/`def`/`refs`, which\n" ++
  "                                     always require a file — name-addressed multi-arg forms);\n" ++
  "                                     a <file.bang> WITH imports/uses is resolved the SAME way\n" ++
  "                                     `bang check` resolves it (imports visible to every op).\n" ++
  "                                     `def`/`refs` are DECL-granularity, not line/col — see #52.\n\n" ++
  "  bang --help, -h                    print this text and exit 0\n" ++
  "  bang --version, -v                 print the version and exit 0\n\n" ++
  "PIPELINE (default: type-check first):\n" ++
  "  (default)        parse → TYPE-CHECK → lower → run; an ill-typed program is a TYPE ERROR\n" ++
  "  --no-typecheck   raw erase-and-run (no type gate) — for oracle/differential testing\n\n" ++
  "ENGINE:\n" ++
  "  (default)          environment machine evalE/readback (ADR-0094) — PROVEN ≡ the oracle\n" ++
  "               (evalE_agrees_evalD, axiom-clean) + differentially gated; the FAST engine\n" ++
  "               (#61's substitution cost eliminated, ~300x on examples/json)\n" ++
  "  --engine=oracle    kernel oracle Source.eval — the verified reference; slower, but its\n" ++
  "               failures carry the SPECIFIC outcome (oom/escaped-cap/stuck); the arbiter\n" ++
  "  --engine=compiled  the calculated machine exec∘compile (verified compiler output, ADR-0016)\n" ++
  "  --compiled         alias for --engine=compiled\n" ++
  "               — env/compiled failures collapse to exit 5; re-run with --engine=oracle\n" ++
  "               for the specific diagnosis\n\n" ++
  "EXIT CODES:\n" ++
  "  0  done — value printed to stdout\n" ++
  "  1  usage / parse / elaboration / TYPE error\n" ++
  "  2  out of fuel (oom)              [oracle engine]\n" ++
  "  3  capability escaped its handler [oracle engine]\n" ++
  "  4  stuck (ill-formed program)     [oracle engine, --no-typecheck]\n" ++
  "  5  compiled machine produced no value (oom / escaped cap / stuck) [--compiled]\n\n" ++
  "EXIT CODES [bang check --json]:\n" ++
  "  0  ok:true  — the program type-checks\n" ++
  "  1  ok:false — diagnostics present (see the JSON on stdout)\n" ++
  "  2  tool error (e.g. unreadable file) — reported on stderr, never folded into the JSON\n\n" ++
  "  NOTE: a <file.bang> with imports/uses is resolved the SAME way `bang run` resolves it, before\n" ++
  "  type-checking, so a multi-file project's imports are visible to `check`. KNOWN v1 LIMITATION:\n" ++
  "  a diagnostic from a resolved multi-file program always has \"span\":null — no line/col — since\n" ++
  "  the resolved program has no single source text to locate into (follow-up: file-aware spans).\n\n" ++
  "EXIT CODES [bang query <op>]:\n" ++
  "  0  the op ran and produced a JSON answer on stdout — INCLUDING an op-level \"ok\":false\n" ++
  "     (e.g. `def` naming a decl that doesn't exist): the tool succeeded, the ANSWER is negative\n" ++
  "  1  {\"ok\":false,\"error\":...} on stdout — a parse failure or (multi-file) an\n" ++
  "     import-resolution failure: the op could not even run, but stdout still carries the answer\n" ++
  "  2  tool error (e.g. unreadable file) — reported on STDERR, NOTHING on stdout (never folded\n" ++
  "     into the JSON, mirrors `check --json`'s own TOOL-error convention exactly)."

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
def replStep (typecheck : Bool) (engine : Engine) (binds : List ReplBinding) (line : String) :
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
      let code ← runSource typecheck engine (wrapBindings binds src)
      return (binds, code)
  else if line.startsWith ":let" then
    match splitLetCmd (line.drop 4).toString with
    | none => IO.eprintln "error: `:let` expects `:let <name> = <expr>`"; return (binds, 1)
    | some (name, rhs) => return (binds ++ [(name, rhs)], 0)
  else if line.startsWith ":" then
    IO.eprintln s!"error: unknown command '{line}' (:help for the list)"; return (binds, 1)
  else
    let code ← runSource typecheck engine (wrapBindings binds line)
    return (binds, code)

/-- The interactive/piped loop: read a line, `replStep`, repeat until `:q`/`:quit`/EOF. Works
identically whether stdin is a terminal or a pipe (`echo 'expr' | bang repl` runs each line and
exits on EOF) — `IO.FS.Stream.getLine` doesn't care which; that is what makes the non-interactive
(agent-driven) use case work for free, per the operator's agent-first framing. Tracks the exit
code of the LAST line that actually ran (silent lines don't overwrite it), so a piped single-expr
session's exit code matches `bang eval`'s for the same program. -/
partial def runRepl (typecheck : Bool) (engine : Engine) : IO UInt32 := do
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
        let (binds', code) ← replStep typecheck engine binds line
        loop binds' code
  loop [] 0

def main (args : List String) : IO UInt32 := do
  match args with
  | cmd :: rest =>
    if cmd == "--help" || cmd == "-h" then
      -- A HELP REQUEST IS A SUCCESS (issue #66): stdout (not stderr — this is the ordinary
      -- `usage` case's convention, reversed on purpose, since a piped `bang --help | less`
      -- reader expects the text on stdout), exit 0.
      IO.println usage; pure 0
    else if cmd == "--version" || cmd == "-v" then
      IO.println s!"bang {bangVersion}"; pure 0
    else if cmd == "run" then
      -- FLAGS (`--…`) may appear in any order before the single positional; anything else is usage.
      -- `run` ALWAYS goes through the module resolver (ADR-0093 D1) — a decl-free/import-free file
      -- resolves to itself unchanged (`resolveEntryFile`'s short-circuit), so this is behavior-
      -- preserving for every program in today's corpus; only a file with an `import`/`use` header
      -- takes the actual resolve-and-merge path. `eval`'s inline string has no FILE to resolve
      -- relative to, so it stays on the single-string `runSource` path unconditionally (below) —
      -- an `import` in an `eval`-string program is out of v1 scope (no directory to search).
      let engine     := parseEngine rest
      let typecheck  := !rest.contains "--no-typecheck"
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [arg] =>
        match ← resolveEntryFile arg with
        | .error e   => IO.eprintln s!"error: {e}"; pure 1
        | .ok merged => runResolvedProg typecheck engine merged
      | _ => IO.eprintln usage; pure 1
    else if cmd == "eval" then
      let engine     := parseEngine rest
      let typecheck  := !rest.contains "--no-typecheck"
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [arg] => runSource typecheck engine arg
      | _ => IO.eprintln usage; pure 1
    else if cmd == "repl" then
      let engine    := parseEngine rest
      let typecheck := !rest.contains "--no-typecheck"
      runRepl typecheck engine
    else if cmd == "fmt" then
      -- no `--` flags this slice (no `-w`, per the team lead's hold); any non-positional is usage.
      match rest with
      | []      => runFmt (← (← IO.getStdin).readToEnd)   -- `bang fmt` with no file: read stdin
      | [arg]   => runFmt (← IO.FS.readFile ⟨arg⟩)
      | _       => IO.eprintln usage; pure 1
    else if cmd == "check" then
      -- `--json` may appear anywhere before the single optional positional; anything else is usage.
      let json := rest.contains "--json"
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | []      => runCheck json none        -- `bang check [--json]` with no file: read stdin
      | [arg]   => runCheck json (some arg)
      | _       => IO.eprintln usage; pure 1
    else if cmd == "test" then
      -- no flags this slice (no `--samples`/`--seed`, a natural follow-up, not added speculatively).
      match rest with
      | []      => runTest none        -- `bang test` with no file: read stdin
      | [arg]   => runTest (some arg)
      | _       => IO.eprintln usage; pure 1
    else if cmd == "query" then
      -- `bang query <op> ...` (#80). Per-op ARGUMENT ORDER matches the issue's own spec exactly
      -- (name-addressed ops put the NAME first when a bare-file positional would be ambiguous with
      -- it; `symbols`/`type`/`laws` are unambiguous — file only — so file stays first there too,
      -- matching `check`/`fmt`'s own convention). `--json` is NOT a flag here (`Bang.Query`'s
      -- module header: `--json` is the ONLY v1 output, not an opt-in) — a stray `--`-prefixed arg
      -- falls through to the usage error like every other subcommand's unknown-flag case.
      match rest with
      | ["dump", file]          => runQueryDump (some file)
      | ["dump"]                => runQueryDump none
      | ["symbols", file]       => runQuerySymbols (some file)
      | ["symbols"]             => runQuerySymbols none
      | ["type", file, name]    => runQueryType (some file) name
      | ["effects", name, file] => runQueryEffects (some file) name
      | ["effects", name]       => runQueryEffects none name
      | ["laws", file]          => runQueryLaws (some file)
      | ["laws"]                => runQueryLaws none
      | ["def", name, file]     => runQueryDef (some file) name
      | ["refs", name, file]    => runQueryRefs (some file) name
      | _                       => IO.eprintln usage; pure 1
    else
      IO.eprintln usage; pure 1
  | _ => IO.eprintln usage; pure 1
