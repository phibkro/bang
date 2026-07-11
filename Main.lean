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
import Bang.Frontend.Rewrite
import Bang.Frontend.Lint
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

/-- Parse `--fuel N` out of the raw flag list (issue #103(a)): a TWO-TOKEN flag (unlike every
other `--…` flag in this CLI, which is single-token), so it needs its own scan rather than a
`.contains` check. Returns `defaultFuel` when absent, when the value fails to parse as a `Nat`, or
when `--fuel` is the last token with no following value — never a silent 0/crash; an unparseable
value falls back to the safe default rather than becoming a surprising fuel-less run. -/
def parseFuel (flags : List String) : Nat :=
  let rec go : List String → Nat
    | "--fuel" :: v :: _ => v.toNat?.getD defaultFuel
    | _ :: rest          => go rest
    | []                 => defaultFuel
  go flags

/-- Strip `--fuel N` (BOTH tokens) out of a flag list, alongside the SAME `"--".isPrefixOf`
single-token filter every other subcommand already applies — so `--fuel`'s VALUE token (a bare
number, no `--` prefix) doesn't leak through as a stray positional. Composes with
`.filter (fun a => !("--".isPrefixOf a))`: apply THIS first, then that. -/
def stripFuelFlag : List String → List String
  | "--fuel" :: _ :: rest => stripFuelFlag rest
  | a :: rest             => a :: stripFuelFlag rest
  | []                    => []

/-! ### Host-IO flag parsing (ADR-0104) — `--env`, `--allow`, `--record`/`--replay`, `--max-host-requests`. -/

/-- The default host-request ceiling (ADR-0104 §4): the replay-prefix driver re-evaluates once per
host request (O(n²)), so this bounds the quadratic. Generous for the Console/Clock wedge (a handful
of ops); a program exceeding it fails LOUD naming `--max-host-requests`, not a silent slowdown. -/
def defaultMaxHostRequests : Nat := 1024

/-- `--env=real` present ⟹ the real host environment (do actual IO). Absent / `--env=sim` ⟹ the
pure sim (today's default engine path). `--replay <file>` also implies the host driver (pure, but the
answers come from the trace, not IO). -/
def wantsHostEnv (flags : List String) : Bool :=
  flags.contains "--env=real" || (flags.any (· == "--record")) ||
  (flags.any (fun a => a == "--replay" || "--replay=".isPrefixOf a)) ||
  flags.any (fun a => "--record=".isPrefixOf a)

/-- Parse a `--flag=value` (single-token, `=`-joined) out of the flag list; `none` if absent. -/
def parseEqFlag (key : String) (flags : List String) : Option String :=
  (flags.find? (fun a => (key ++ "=").isPrefixOf a)).map (fun a => (a.drop (key.length + 1)).toString)

/-- `--allow=A,B` or `--allow A,B` → `some ["A","B"]`; absent → `none` (grant ALL, ADR-0104 §2). -/
def parseAllow (flags : List String) : Option (List String) :=
  match parseEqFlag "--allow" flags <|> (do
      let rec go : List String → Option String
        | "--allow" :: v :: _ => some v
        | _ :: rest           => go rest
        | []                  => none
      go flags) with
  | some s => some ((s.splitOn ",").filterMap (fun t => let t := t.trim; if t.isEmpty then none else some t))
  | none   => none

/-- `--max-host-requests N` (two-token) or `--max-host-requests=N`; `defaultMaxHostRequests` otherwise. -/
def parseMaxHostRequests (flags : List String) : Nat :=
  match parseEqFlag "--max-host-requests" flags <|> (do
      let rec go : List String → Option String
        | "--max-host-requests" :: v :: _ => some v
        | _ :: rest                       => go rest
        | []                              => none
      go flags) with
  | some v => v.toNat?.getD defaultMaxHostRequests
  | none   => defaultMaxHostRequests

/-- `--record <file>` / `--record=<file>` → the trace output path (`none` if absent). -/
def parseRecord (flags : List String) : Option String :=
  parseEqFlag "--record" flags <|> (do
    let rec go : List String → Option String
      | "--record" :: v :: _ => if "--".isPrefixOf v then none else some v
      | _ :: rest            => go rest
      | []                   => none
    go flags)

/-- `--replay <file>` / `--replay=<file>` → the trace input path (`none` if absent). -/
def parseReplay (flags : List String) : Option String :=
  parseEqFlag "--replay" flags <|> (do
    let rec go : List String → Option String
      | "--replay" :: v :: _ => if "--".isPrefixOf v then none else some v
      | _ :: rest            => go rest
      | []                   => none
    go flags)

/-- Strip every host-IO TWO-TOKEN flag's value token (`--allow V`, `--max-host-requests V`,
`--record V`, `--replay V`) so a bare value doesn't leak as a stray positional (mirrors
`stripFuelFlag`). Single-token `=`-joined forms are removed by the ordinary `--`-prefix filter. -/
def stripHostFlags : List String → List String
  | "--allow" :: _ :: rest              => stripHostFlags rest
  | "--max-host-requests" :: _ :: rest  => stripHostFlags rest
  | "--record" :: v :: rest             => if "--".isPrefixOf v then "--record" :: stripHostFlags (v :: rest) else stripHostFlags rest
  | "--replay" :: v :: rest             => if "--".isPrefixOf v then "--replay" :: stripHostFlags (v :: rest) else stripHostFlags rest
  | a :: rest                           => a :: stripHostFlags rest
  | []                                  => []

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
than its own return type allows.

`srcFuel` is the USER-facing fuel (issue #103(a), `--fuel N`; `defaultFuel` when not
given) — scaled ×10 to stay in `exec`'s finer machine-instruction unit, exactly the
same ratio `compiledFuel := 10 * defaultFuel` already fixed for the no-flag case (see
`compiledFuel`'s own doc comment); this makes `--fuel` raise BOTH engines' ceilings by
the same proportional amount rather than only the oracle's. -/
def runCompiled (srcFuel : Nat) (c : Comp) : IO UInt32 := do
  match Bang.CalcVM.exec (10 * srcFuel) 0 (Bang.CalcVM.compile c []) [] [] with
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
fail-loud line — the experimental engine does NOT sub-classify (that is what the oracle is for).

`fuel` is the USER-facing fuel (issue #103(a), `--fuel N`; `defaultFuel` when not given) — `runE`
already takes fuel as a plain parameter, so no scaling is needed (unlike the compiled engine's finer
machine-instruction unit): this engine's step is the SAME unit `--fuel` names. -/
def runEnv (fuel : Nat) (c : Comp) : IO UInt32 := do
  match Bang.EnvMachine.runE fuel c with
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
message can unconditionally point at the type gate being off — not a flag-dependent guess.

`fuel` is the USER-facing ceiling (issue #103(a), `--fuel N`; `defaultFuel` when not given) —
plumbed to all three engines: the oracle directly (SAME unit `Source.eval` counts in), the env
engine directly (`runEnv`'s own doc comment — SAME unit), the compiled engine ×10-scaled
(`runCompiled`'s own doc comment — its finer machine-instruction unit). The out-of-fuel MESSAGE
below names `fuel`, not the frozen `defaultFuel` constant, so it stays accurate under `--fuel`. -/
def runComp (engine : Engine) (fuel : Nat) (c : Comp) : IO UInt32 := do
  match engine with
  | .compiled => runCompiled fuel c
  | .env      => runEnv fuel c
  | .oracle   =>
  match Bang.Source.eval fuel c with
  | .done v      => IO.println (valPretty v); pure 0
  | .oom         =>
    IO.eprintln <|
      s!"error: out of fuel (ceiling {fuel} steps) — the program may diverge, or hit " ++
      "the recursion-cost cliff (issue #61); a well-typed program that should terminate is " ++
      "likely paying substitution cost per step rather than genuinely looping — try a higher " ++
      "ceiling with --fuel N (issue #103)"
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

/-! ### Bundled `std/` modules (ADR-0104) — a SECOND search root, baked into the binary.

`import Io` resolves to `std/Io.bang` WITHOUT a filesystem probe: the source is `include_str`-baked
into the executable at compile time, exactly as `Prelude.bang` is (`TypeCheck.preludeSrc`). This is
the robust convention — a bundled stdlib module works for an installed `bang` binary regardless of
CWD (a `std/`-relative-to-CWD probe would only work from the repo root), and `test-modules.sh`'s
`bang check std/Io.bang` leg keeps the baked bytes ≡ the on-disk file. Unlike the prelude (auto-
injected into EVERY program), an `std/` module is served ONLY on an explicit `import`/`use` — the
least-authority discipline (host-io-design §1): a program must name `Io` to get IO into its row.

std modules resolve BEFORE the same-dir/root filesystem probe (`resolveModulePath` /
`resolveModule`), so a stray local `Io.bang` cannot silently shadow the bundled one. -/
def stdModules : List (String × String) :=
  [("Io", include_str "std/Io.bang")]

/-- The bundled source for std module `modName`, or `none` if it is not a bundled std module. -/
def stdModuleSrc (modName : String) : Option String :=
  (stdModules.find? (·.1 = modName)).map (·.2)

/-- Resolve `import name`/`use name` module NAME to a file path: try `<dir of the importing
file>/name.bang` first, then `<root>/name.bang` (D1's fixed, documented order). `none` on a miss in
BOTH — the caller names both probed paths in its error (a miss must be loud AND specific, ADR-0046:
"the fix is obvious from the message" is the bar, not just "file not found"). A bundled `std/` module
(`stdModuleSrc`) is served by `resolveModule` directly, ahead of this path probe, so it never reaches
here — callers check `stdModuleSrc` first. -/
def resolveModulePath (root : System.FilePath) (importingDir : System.FilePath) (modName : String) :
    IO (Option System.FilePath) := do
  let sameDir := importingDir / s!"{modName}.bang"
  if ← sameDir.pathExists then return some sameDir
  let atRoot := root / s!"{modName}.bang"
  if ← atRoot.pathExists then return some atRoot
  return none

/-- The two real (symlink-resolved) trees an import-derived module path is allowed to live in:
the ENTRY file's own directory subtree and the `root` (CWD) subtree — exactly the two probe
locations of D1's same-dir-then-root search order, so every legitimate resolution (absent
symlinks) already lands in one of them. Both fields are `IO.FS.realPath`-resolved ONCE, at
entry-resolution time (`resolveEntryFile`), never re-resolved per module. -/
structure AllowedRoots where
  entryDir : System.FilePath
  root     : System.FilePath

/-- Resolve `p` to its real (symlink-free) path and require it inside one of the two real
`allowed` trees. Import-derived paths only — the entry file is the USER's explicit choice and is
never contained. `.error pReal` = escape (the REAL path is returned so the caller's diagnostic can
name it alongside BOTH allowed trees — ADR-0046: the fix must be obvious from the message). `p`
must exist (callers sit behind a `pathExists` check — `IO.FS.realPath` throws on a missing path). -/
def containedRealPath (allowed : AllowedRoots) (p : System.FilePath) :
    IO (Except System.FilePath System.FilePath) := do
  let pReal ← IO.FS.realPath p
  -- separator-guarded prefix check: `/proj` must not admit `/project-evil`
  let inTree (r : System.FilePath) : Bool :=
    pReal == r || pReal.toString.startsWith (r.toString ++ "/")
  if inTree allowed.entryDir || inTree allowed.root then return .ok pReal
  return .error pReal

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
`bigFuel`-idiom precedent elsewhere in the codebase). Every module READ here is import-derived,
so it passes the `containedRealPath` guard first (the entry file is read by `resolveEntryFile`
itself, never here — the user's explicit choice of entry is never contained). -/
partial def resolveModule (root : System.FilePath) (allowed : AllowedRoots) (modName : String)
    (path : System.FilePath) (st : ResolveState) : IO (Except String ResolveState) := do
  if (st.resolved.map Prod.fst).contains modName then return .ok st   -- already resolved (diamond import)
  if st.visiting.contains modName then
    return .error s!"import cycle: {String.intercalate " → " (st.visiting ++ [modName])}"
  -- ADR-0104: a bundled `std/` module (e.g. `Io`) is served from `include_str`-baked source,
  -- BEFORE the filesystem probe — trusted, compiled-in, no containment check (it isn't a
  -- user path). Its OWN transitive imports still resolve normally (relative to `dir` = `root`).
  if let some src := stdModuleSrc modName then
    match Bang.Surface.parseProg src with
    | .error m => return .error s!"bundled std module '{modName}': parse error: {m}"
    | .ok prog =>
        let mut st' := { st with visiting := st.visiting ++ [modName] }
        for imp in prog.imports do
          match ← resolveModule root allowed imp.modName (Id.run <| root / s!"{imp.modName}.bang") st' with
          | .error e  => return .error e
          | .ok stNew => st' := stNew
        for u in prog.uses do
          match ← resolveModule root allowed u.modName (Id.run <| root / s!"{u.modName}.bang") st' with
          | .error e  => return .error e
          | .ok stNew => st' := stNew
        return .ok { st' with resolved := st'.resolved ++ [(modName, prog)], visiting := st.visiting }
  if ¬ (← path.pathExists) then
    return .error s!"could not read module '{modName}' at '{path}'"
  let pathReal ← match ← containedRealPath allowed path with
    | .error pReal => return .error s!"module '{modName}': resolved path escapes the project — '{pReal}' is outside both the entry tree '{allowed.entryDir}' and the root '{allowed.root}' (symlinked module sources must stay inside the project)"
    | .ok r => pure r
  let some src ← (do let s ← IO.FS.readFile pathReal; pure (some s)) <|> pure none
    | return .error s!"could not read module '{modName}' at '{path}'"
  match Bang.Surface.parseProg src with
  | .error m => return .error s!"module '{modName}' ({path}): parse error: {m}"
  | .ok prog =>
      let dir := path.parent.getD root
      let mut st' := { st with visiting := st.visiting ++ [modName] }
      for imp in prog.imports do
        match ← resolveModule root allowed imp.modName (Id.run <| dir / s!"{imp.modName}.bang") st' with
        | .error e  => return .error e
        | .ok stNew => st' := stNew
      for u in prog.uses do
        match ← resolveModule root allowed u.modName (Id.run <| dir / s!"{u.modName}.bang") st' with
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

/-- The D1 resolution + D2/D3/D4 merge, from an entry FILE, WITHOUT the D5 entry rule
(`applyEntryRule`) applied — parse it, resolve every `import`/`use` it names (transitively,
same-dir-then-root, cycle-checked), then `mergeModules` the result into ONE flat, UN-entry-ruled
`Prog`. Factored out of `resolveEntryFile` (#117's gap-2 fix) so a caller that does NOT want the
"must be runnable" D5 rule — `bang test`'s decls-only law discovery, which `applyEntryRule` would
otherwise reject outright ("this file is a library… nothing to run", the SAME message `bang run`
correctly gives for an unrunnable file but WRONG for `bang test`'s intentionally decls-only input)
— can reuse the resolve+merge machinery without also inheriting a runnability check meant for a
DIFFERENT subcommand. A resolved import's OWN path is re-probed via `resolveModulePath` (not the
naive `dir/name.bang` `resolveModule` builds directly) ONLY at the top level, matching D1's exact
documented search order; nested imports resolve relative to THEIR OWN file's directory (the
natural reading of "same directory as the importing file" — a transitively-imported module's
imports are relative to IT, not the original entry file). -/
def resolveEntryFileRaw (path : String) : IO (Except String Prog) := do
  let entryPath : System.FilePath := ⟨path⟩
  let root ← IO.currentDir
  let some entrySrc ← (do let s ← IO.FS.readFile entryPath; pure (some s)) <|> pure none
    | return .error s!"could not read file '{path}'"
  match Bang.Surface.parseProg entrySrc with
  | .error m => return .error s!"parse error: {m}"
  | .ok entryProg =>
      if entryProg.imports.isEmpty && entryProg.uses.isEmpty then return .ok entryProg
      let dir := entryPath.parent.getD root
      -- both containment trees realPath-resolved ONCE here (never per module). The entry dir
      -- exists (the entry file was just read from it); the `<|>` fallback to the root tree only
      -- covers a pathological dir string and can only SHRINK the allowed set, never widen it.
      let rootReal ← IO.FS.realPath root
      let entryDirReal ← IO.FS.realPath dir <|> pure rootReal
      let allowed : AllowedRoots := { entryDir := entryDirReal, root := rootReal }
      let mut st : ResolveState := {}
      for imp in entryProg.imports do
        -- ADR-0104: a bundled `std/` module resolves via `resolveModule`'s baked-source branch,
        -- ahead of the filesystem probe (`path` is unused for it — pass a placeholder).
        if (stdModuleSrc imp.modName).isSome then
          match ← resolveModule root allowed imp.modName root st with
          | .error e  => return .error e
          | .ok stNew => st := stNew
        else
        match ← resolveModulePath root dir imp.modName with
        | none =>
            let probed1 := dir / s!"{imp.modName}.bang"
            let probed2 := root / s!"{imp.modName}.bang"
            return .error s!"cannot find module '{imp.modName}' — probed '{probed1}' and '{probed2}'"
        | some found =>
            match ← resolveModule root allowed imp.modName found st with
            | .error e  => return .error e
            | .ok stNew => st := stNew
      for u in entryProg.uses do
        if (stdModuleSrc u.modName).isSome then
          match ← resolveModule root allowed u.modName root st with
          | .error e  => return .error e
          | .ok stNew => st := stNew
        else
        match ← resolveModulePath root dir u.modName with
        | none =>
            let probed1 := dir / s!"{u.modName}.bang"
            let probed2 := root / s!"{u.modName}.bang"
            return .error s!"cannot find module '{u.modName}' — probed '{probed1}' and '{probed2}'"
        | some found =>
            match ← resolveModule root allowed u.modName found st with
            | .error e  => return .error e
            | .ok stNew => st := stNew
      return Bang.TypeCheck.mergeModules st.resolved entryProg

/-- The full D1-D5 resolution + merge, from an entry FILE — `resolveEntryFileRaw` (the resolve+merge
half) followed by the D5 entry rule (`applyEntryRule`), applied LAST to the fully-merged result.
The `bang check`/`bang run` entry point; `bang test` uses `resolveEntryFileRaw` directly instead
(see that function's own doc comment for why). -/
def resolveEntryFile (path : String) : IO (Except String Prog) := do
  match ← resolveEntryFileRaw path with
  | .error e   => pure (.error e)
  | .ok merged => pure (applyEntryRule merged)

/-- Run one source string through the whole pipeline, printing the outcome and returning the process
exit code. `typecheck` selects the pipeline (ADR-0076 #51):

  * DEFAULT — parse (located) → **TYPE-CHECK (reject on error)** → lower → run (`checkAndLower`).
    An ill-typed program is caught as a TYPE ERROR before it runs, so the run path and the `#guard`
    gate share ONE type gate (SSoT) and `type_safety` (well-typed ⟹ never stuck) is real for users.
    A parse error is LOCATED (`error at line:col: …`); a type/elab error prints the checker's message.
  * `--no-typecheck` — the raw erase-and-run path (`elaborateToComp`): parse → elaborate → lower →
    run, NO type gate. Kept for oracle/differential testing (running an ill-typed program to observe
    the defined runtime `stuck`/`escapedCap`, ADR-0063).

`engine` selects only the execution ENGINE and is orthogonal to `typecheck`. `fuel` is the
USER-facing ceiling (issue #103(a), `--fuel N`; `defaultFuel` when not given), forwarded straight
to `runComp`. -/
def runSource (typecheck : Bool) (engine : Engine) (fuel : Nat) (src : String) : IO UInt32 := do
  if typecheck then
    match Bang.TypeCheck.checkAndLower src with
    | .error (m, some sp) => IO.eprintln s!"error at {sp.loc}: {m}"; pure 1
    | .error (m, none)    => IO.eprintln s!"error: {m}"; pure 1
    | .ok c               => runComp engine fuel c
  else
    match Bang.TypeCheck.elaborateToComp src with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp engine fuel c

/-- Run an already-RESOLVED-and-merged `Prog` (ADR-0093 D1-D4 — `resolveEntryFile`'s output) through
the SAME two pipelines `runSource` offers for a single file: DEFAULT type-checked
(`checkAndLowerProg`) or `--no-typecheck` raw erase-and-run (`elaborateToCompProg`), then `runComp`.
No located errors either way (see `checkAndLowerProg`'s doc comment) — a resolution/parse failure
is already located by `resolveEntryFile` itself, before this runs. `fuel` is the USER-facing ceiling
(issue #103(a), `--fuel N`; `defaultFuel` when not given), forwarded straight to `runComp`. -/
def runResolvedProg (typecheck : Bool) (engine : Engine) (fuel : Nat) (prog : Prog) : IO UInt32 := do
  if typecheck then
    match Bang.TypeCheck.checkAndLowerProg prog with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp engine fuel c
  else
    match Bang.TypeCheck.elaborateToCompProg prog with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok c    => runComp engine fuel c

/-! ## Host-IO driver (ADR-0104) — the replay-prefix seam's IO shell

The ONLY IO site. `evalEHost` (`Bang.EnvMachine`, pure) surfaces a host request; this driver does the
real IO, records a trace row, and RE-RUNS with the answer accumulated — the replay-prefix (ADR-0104
§4). Record and replay share ONE response-supply: `HostEnv.answer` is `real-IO + record` under
`--env=real`, and `read-the-next-trace-row` under `--replay` — the SAME driver loop, only the answer
source differs (condition 4). Both stay on the PURE `evalEHost`; the pure-oracle equality that makes
this invariant-#1-compliant is the replay leg reproducing the recorded run. -/

/-- Build a `Str` kernel `Val` from a Lean string (the inverse of `asString`): `SNil = fold (inl ())`,
`SCons(Char cp, rest) = fold (inr (pair (fold (vint cp)) rest))` (ADR-0074). Used by the host
`readLine` handler to lift a real input line into the value the program resumes with. -/
partial def strToVal (s : String) : Val :=
  match s.data with
  | []      => .fold (.inl .vunit)
  | c :: cs => .fold (.inr (.pair (.fold (.vint (Int.ofNat c.toNat))) (strToVal (String.mk cs))))

/-- A host request's op → the effect it belongs to, for the wedge (Console/Clock op names are
disjoint, ADR-0104 §2 — so op-name dispatch is unambiguous). Unknown op ⇒ `none` (fail-loud). -/
def hostServiceReal (op : Bang.OpId) (payload : Val) : IO (Option Val) := do
  match op with
  | "print"    => match asString payload with
                  | some s => IO.println s; pure (some .vunit)
                  | none   => pure none                       -- print of a non-Str ⇒ fail-loud
  | "readLine" => let line ← (← IO.getStdin).getLine
                  pure (some (strToVal (line.dropRightWhile (· == '\n'))))
  | "now"      => let ms ← IO.monoMsNow; pure (some (.vint (Int.ofNat ms)))
  | _          => pure none

/-- One recorded trace row (ADR-0104 §3): a satisfied host perform, ndJSON. All fields Sendable
(`op`/`payload`/`result` — `label`/`id` are `Nat`), so it serializes faithfully. Payload/result are
rendered via `valPretty` (the SAME rendering the run oracle uses) — for the wedge (Str/Int/Unit)
`valPretty` is injective enough to replay by POSITION (the row order IS the replay prefix). -/
def traceRow (req : Bang.EnvMachine.HostReq) (result : Val) : String :=
  "{\"label\":" ++ toString req.label ++ ",\"op\":\"" ++ req.op ++
  "\",\"payload\":\"" ++ valPretty req.payload ++ "\",\"result\":\"" ++ valPretty result ++ "\"}"

/-- The replay-prefix DRIVER (ADR-0104 §4). Runs `M` under `evalEHost` at the granted `hostLabels`
with the response prefix built SO FAR (`rsRev`, reversed for O(1) append); on a host request, calls
`answer` (the shared response-supply — real IO under record, trace-read under replay), optionally
records via `onRow`, appends the answer, and re-runs. `hdone` → print + 0; `hstuck` → fail-loud;
the O(n²) re-eval is bounded by `maxReq` (a LOUD ceiling naming `--max-host-requests`, ADR-0104 §4). -/
partial def runHostLoop (hostLabels : List Bang.EffectRow.Label) (fuel maxReq : Nat)
    (answer : Bang.EnvMachine.HostReq → IO (Option Val))
    (onRow : Bang.EnvMachine.HostReq → Val → IO Unit)
    (M : Comp) : IO UInt32 := do
  let rec loop (rsRev : List Bang.EnvMachine.MVal) (nReq : Nat) : IO UInt32 := do
    if nReq > maxReq then
      IO.eprintln s!"error: host-request ceiling exceeded ({maxReq}) — the program performed more \
        host operations than --max-host-requests allows. The v1 replay-prefix driver re-evaluates \
        once per host request (O(n²) total), so this ceiling is a fail-loud guard, not a hard limit; \
        raise it with --max-host-requests N. (A future suspendable engine, ADR-0101, removes the \
        re-eval and this ceiling.)"
      return 6
    match Bang.EnvMachine.stepHost hostLabels fuel rsRev.reverse M with
    | .hdone v  => IO.println (valPretty v); return 0
    | .hstuck   =>
        IO.eprintln "error: the host run produced no first-order value — an escaped capability on an \
          UNGRANTED host label (add it to --allow), a non-host raise, out of fuel, or a function \
          terminal. Re-run under --engine=oracle for the specific diagnosis."
        return 5
    | .hreq req =>
        match ← answer req with
        | none   =>
            IO.eprintln s!"error: no host handler for op '{req.op}' on label {req.label} — the v1 \
              wedge services Console (print/readLine) and Clock (now) only (ADR-0104)."
            return 7
        | some result =>
            onRow req result
            loop (Bang.EnvMachine.readbackIn result :: rsRev) (nReq + 1)
  loop [] 0

/-- Resolve `--allow=A,B` (or `--allow A,B`) NAMES to the labels the elaborator allocated, via the
program's effect map. An allow-name not in the map (not a declared effect) ⇒ a LOUD error naming it
(ADR-0104 §2 — an under/mis-granting flag is caught before the run). Empty/absent `--allow` under
`--env=real` grants ALL declared effect labels (the "grant everything" shorthand, ADR-0104 §2). -/
def resolveAllow (effMap : List (String × Bang.EffectRow.Label)) (allow : Option (List String)) :
    Except String (List Bang.EffectRow.Label) :=
  match allow with
  | none       => .ok (effMap.map (·.2))                 -- no --allow ⇒ all declared labels granted
  | some names =>
      -- A grant name matches an effect by its EXACT name OR its unqualified tail: a program that
      -- `import Io`s sees the effect as `Io_Console` (ADR-0093 module-qualification), but a user
      -- writes `--allow=Console` naturally — accept both (`Io_Console` ends in `_Console`).
      let nameMatches (nm en : String) : Bool := en == nm || en.endsWith ("_" ++ nm)
      names.foldlM (init := []) (fun acc nm =>
        match effMap.find? (fun p => nameMatches nm p.1) with
        | some (_, ℓ) => .ok (acc ++ [ℓ])
        | none        => .error s!"--allow names '{nm}', which is not a declared effect in this program \
                          (declared: {String.intercalate ", " (effMap.map (·.1))})")

/-- Parse a `--replay` trace's `result` fields, in order, into the response prefix the sim run
consumes (ADR-0104 §3). A trace row is `{…,"result":"<valPretty>"}`; for the wedge the results are
`()` (unit), an int, or a Str glyph-string, which `parseTraceResult` lifts back to a `Val`. The row
ORDER is the replay prefix (positional), matching how record appended them. -/
def parseTraceResult (s : String) : Option Val :=
  if s == "()" then some .vunit
  else match s.toInt? with
    | some n => some (.vint n)
    | none   => some (strToVal s)      -- a Str glyph-string (the only remaining Sendable wedge shape)

/-- Extract the ordered `result` values from an ndJSON trace file's rows (one row per line). A line
without a `"result":"…"` field is skipped (blank lines, trailing newline). ADR-0104 §3. -/
def loadTraceResults (contents : String) : List Val :=
  (contents.splitOn "\n").filterMap (fun line =>
    let marker := "\"result\":\""
    match (line.splitOn marker) with
    | _ :: rest :: _ => parseTraceResult (rest.takeWhile (· != '"')).toString
    | _              => none)

/-- The host-IO entry (ADR-0104): run a resolved `Prog` under the replay-prefix driver. Resolves
`--allow` names→labels via the program's effect map, then drives `evalEHost`. Record and REPLAY share
ONE loop (`runHostLoop`) — only the `answer` supply differs (real IO+record vs trace-read), condition
4. `--replay` runs on the PURE engine (no real IO), the invariant-#1 leg. -/
def runHostProg (fuel maxReq : Nat) (allow : Option (List String))
    (record : Option String) (replay : Option String) (prog : Prog) : IO UInt32 := do
  match Bang.TypeCheck.checkAndLowerProgWithEffects prog with
  | .error e => IO.eprintln s!"error: {e}"; pure 1
  | .ok (c, effMap) =>
    match resolveAllow effMap allow with
    | .error e => IO.eprintln s!"error: {e}"; pure 1
    | .ok hostLabels =>
      match replay with
      | some tracePath =>
        -- REPLAY: the answer supply is the pre-loaded trace, consumed in order. Pure (no IO).
        let contents ← IO.FS.readFile ⟨tracePath⟩
        let results := loadTraceResults contents
        let queue ← IO.mkRef results
        runHostLoop hostLabels fuel maxReq
          (answer := fun _ => do
            match ← queue.get with
            | []      => pure none                                   -- trace exhausted ⇒ fail-loud (divergence)
            | r :: rs => queue.set rs; pure (some r))
          (onRow := fun _ _ => pure ())
          c
      | none =>
        -- REAL (+ optional record): the answer supply is real IO; a row is appended per satisfied op.
        let recRef ← IO.mkRef (#[] : Array String)
        let code ← runHostLoop hostLabels fuel maxReq
          (answer := fun req => hostServiceReal req.op req.payload)
          (onRow := fun req result => do
            if record.isSome then recRef.modify (·.push (traceRow req result)))
          c
        match record with
        | some path => IO.FS.writeFile ⟨path⟩ (String.intercalate "\n" (← recRef.get).toList ++ "\n")
        | none      => pure ()
        pure code

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

/-- The `error`-prefix for a human diagnostic, carrying the STABLE code when the message belongs to a
coded family (the rustc `error[B004]:` shape) — `error[B004]` when `Bang.DiagCodes.codeForMsg` finds
one, plain `error` otherwise. A reader can then run `bang explain B004` for the teaching text. -/
def errWord (msg : String) : String :=
  match Bang.DiagCodes.codeForMsg msg with
  | some c => s!"error[{c}]"
  | none   => "error"

/-- Run `bang check` (human-readable, no `--json`): the SAME typed pipeline (`checkAndLower`) the
default `bang run`/`eval` use, reporting only PASS/FAIL — no value is produced (unlike `run`,
`check` never evaluates). Mirrors `runSource`'s DEFAULT arm's error rendering (`error at L:C: …` /
`error: …`) so a human reading `bang check`'s failure sees the identical message `bang run` would
have failed with, plus the STABLE code (`error[B004]` via `errWord`) when the diagnostic is coded. -/
def runCheckHuman (src : String) : IO UInt32 := do
  match Bang.TypeCheck.checkAndLower src with
  | .error (m, some sp) => IO.eprintln s!"{errWord m} at {sp.loc}: {m}"; pure 1
  | .error (m, none)    => IO.eprintln s!"{errWord m}: {m}"; pure 1
  | .ok _               => IO.println "ok"; pure 0

/-- `bang explain <CODE>` (plan 013 s5): print the registry teaching entry for a stable diagnostic
code — summary, explanation, and a minimal triggering example (the `example?` field, when the
diagnostic is a check-time one). An UNKNOWN code is a loud stderr error + exit 1 (never a silent
empty print), matching every other verb's fail-loud contract. The registry (`Bang.DiagCodes`) is the
SINGLE SOURCE OF TRUTH — the same table `check`'s codes and the generated reference read. -/
def runExplain (code : String) : IO UInt32 := do
  match Bang.DiagCodes.explain code with
  | none => IO.eprintln s!"error: unknown diagnostic code '{code}' — run `bang --help` and see the codes in docs/reference/language.md"; pure 1
  | some e =>
    IO.println s!"{e.code}: {e.summary}"
    IO.println ""
    IO.println e.teaching
    match e.example? with
    | some ex =>
      IO.println ""
      IO.println "Triggering example:"
      IO.println ex
    | none => pure ()
    pure 0

/-- One `ok:false` diagnostic JSON object for the `Prog`-taking check path (`code` always `"type"`,
`span` always `null` — see `runCheck`'s doc comment for why: no stage split, no source text to
locate into). Built with `++` (not `s!"..."`), matching `Diagnostics.spanJson`/`Diagnostic.toJson`'s
own convention — Lean's string interpolation escapes a literal `{` as `\{`, not `{{`, which makes a
hand-written JSON-brace literal read backwards; plain concatenation sidesteps the ambiguity entirely
(the SAME reason those two functions avoid `s!`). -/
def checkFailJson (msg : String) : String :=
  let explainStr := match Bang.DiagCodes.codeForMsg msg with
    | some c => Bang.Diagnostics.jsonStr c
    | none   => "null"
  "{\"ok\":false,\"diagnostics\":[{\"severity\":\"error\",\"code\":\"type\",\"explainCode\":" ++
    explainStr ++ ",\"msg\":" ++ Bang.Diagnostics.jsonStr msg ++ ",\"span\":null}]}"

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
failure's exit code (ADR-0093 D1-D5).

Expanded through `Bang.TypeCheck.expandDerives` (#109, ADR-0097 §7) on EVERY path before returning
— `symbols`/`type`/`effects`/`def`/`refs`/`hover` all fan out from here (`runQuerySymbols`'s own
`symbolsJsonP p` call site, and its siblings, never touch `Bang.Query.symbolsJson`'s own
already-expanded string entry, so this is the ONE place that needs the fix for the resolver-backed
verbs to see a `deriving`-generated `trait`/`impl`). A `expandDerives` failure falls back to the
un-expanded `Prog` (same isolation rule as `Query.lean`'s `dumpJson`/`symbolsJson`) rather than
failing the whole query. -/
def resolveQueryProg (src : String) (headerProg : Bang.Surface.Prog) (file : Option String) :
    IO (Except UInt32 Bang.Surface.Prog) := do
  let withDerives (p : Bang.Surface.Prog) : Bang.Surface.Prog :=
    (Bang.TypeCheck.expandDerives p).toOption.getD p
  if headerProg.imports.isEmpty && headerProg.uses.isEmpty then
    match Bang.Surface.parseProgLocated src with
    | .ok p         => pure (.ok (withDerives p))
    | .error (m, _) => IO.println (Bang.Query.errorJsonOk m); pure (.error 1)
  else
    match file with
    | none      => pure (.ok (withDerives headerProg))   -- stdin, no path to resolve relative to (same as `eval`'s limitation)
    | some path =>
        match ← resolveEntryFile path with
        | .error e   => IO.println (Bang.Query.errorJsonOk e); pure (.error 1)
        | .ok merged => pure (.ok (withDerives merged))

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
        printQueryOk (Bang.Query.dumpJson src bangVersion)
      else
        match file with
        | none      => printQueryOk (Bang.Query.dumpJsonP headerProg bangVersion)   -- stdin, no resolver path
        | some path =>
            match ← resolveEntryFile path with
            | .error e   => IO.println (Bang.Query.errorJsonOk e); pure 1
            | .ok merged =>
                -- `mergeModules` clears `imports`/`uses` on its OWN merged output (D1-D4's flat
                -- decl-list convention) — splice the ENTRY file's own header back on so `dump`'s
                -- `"imports"`/`"uses"` fields report what the program's source ACTUALLY declares,
                -- not an artifact of the merge (a real fidelity gap `dumpJsonP` alone can't see,
                -- since it only ever receives the merged `Prog`).
                printQueryOk (Bang.Query.dumpJsonP { merged with imports := headerProg.imports, uses := headerProg.uses } bangVersion)

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

/-- `bang query hover <file> <line> <col>` (#52 slice 5) — the decl at `line:col`, DECL granularity
(see `Bang.Query`'s hover section for the ceiling). 1-INDEXED line/col. Written directly (not via
`resolveQueryProg`, which discards `src` — hover needs the ORIGINAL source text alongside the
resolved `Prog` for its span lookup, the SAME reason `runQueryDump`'s single-file path keeps `src`)
so the resolver path still has `src` available for `hoverJsonP`'s span resolution. A miss
(`{"ok":false,"error":"no decl at L:C"}`) is STILL exit 0 (the tool ran; matches `def`'s "no such
decl" convention) — only a parse/resolution/unreadable-file failure is nonzero. -/
def runQueryHover (file : Option String) (line col : Nat) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      if headerProg.imports.isEmpty && headerProg.uses.isEmpty then
        printQueryOk (Bang.Query.hoverJson src line col)
      else
        match file with
        | none      => printQueryOk (Bang.Query.hoverJsonP src headerProg line col)   -- stdin, no resolver path
        | some path =>
            match ← resolveEntryFile path with
            | .error e   => IO.println (Bang.Query.errorJsonOk e); pure 1
            | .ok merged => printQueryOk (Bang.Query.hoverJsonP src merged line col)

/-- `bang holes [<file.bang>]` (#82 item 3) — every decl carrying a residual/underdetermined
position (a checker hole rendered `#N`, `N ≥ holeBase`; see `Bang.Query.holesOf`). ALWAYS JSON on
stdout — a machine-readable report like `check --json`/`query`'s shape (agents are the audience).
RESOLVER-AWARE (the SAME `readQuerySrc`/`resolveQueryProg` split every `query` op uses — an agent
querying a multi-file project needs its imports visible). Exit contract mirrors `query`: `2` on an
unreadable file (tool error, nothing on stdout), `1` on a parse/resolution failure (`ok:false` on
stdout), `0` when the tool ran and produced a well-formed answer (an EMPTY `holes` array — nothing
underdetermined — is still `ok:true`/exit 0; the caller inspects the array, `query`'s convention). -/
def runHoles (file : Option String) : IO UInt32 := do
  match ← readQuerySrc file with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg file with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.holesJsonP p)

/-- `bang impact <file.bang> <decl>` (#82 item 5) — the transitive DEPENDENTS of `decl` (the
pre-edit blast radius: what breaks if I change it). ALWAYS JSON (agents are the audience).
RESOLVER-AWARE (`readQuerySrc`/`resolveQueryProg`, like every `query` op). Same 0/1/2 exit contract
as `holes`/`query`: `2` unreadable file, `1` parse/resolution failure, `0` well-formed answer (an
`{"ok":false,...}` "no such decl" op-level miss is STILL exit 0 — the caller inspects `ok`). -/
def runImpact (file : String) (decl : String) : IO UInt32 := do
  match ← readQuerySrc (some file) with
  | .error code => pure code
  | .ok (src, headerProg) =>
      match ← resolveQueryProg src headerProg (some file) with
      | .error code => pure code
      | .ok p       => printQueryOk (Bang.Query.impactJsonP p decl)

/-- `bang semver-diff <old.bang> <new.bang>` (#82 item 6) — the public-surface diff of two programs
→ the required version bump (#72's enforcement engine, elm-package precedent). ALWAYS JSON. Both
files are read + parsed; an unreadable EITHER side is a tool error (exit 2, nothing on stdout); a
parse failure on either side is an op-level `{"ok":false,...}` (exit 1, naming which side). Reads
each file's raw source (NOT resolver-aware in v1 — the public surface is the file's OWN `pub` decls;
a multi-file public-surface upgrade is the natural follow-up, matching `test`/`lint`'s precedent). -/
def runSemverDiff (oldFile newFile : String) : IO UInt32 := do
  match ← (do let s ← IO.FS.readFile ⟨oldFile⟩; pure (some s)) <|> pure none with
  | none      => IO.eprintln s!"error: could not read file '{oldFile}'"; pure 2
  | some oldSrc =>
      match ← (do let s ← IO.FS.readFile ⟨newFile⟩; pure (some s)) <|> pure none with
      | none      => IO.eprintln s!"error: could not read file '{newFile}'"; pure 2
      | some newSrc =>
          let out := Bang.Query.semverDiffJson oldSrc newSrc
          IO.println out
          -- op-level parse failure ⟹ exit 1 (mirrors `query`'s errorJsonOk-on-stdout/exit-1 path);
          -- a well-formed diff ⟹ exit 0 (the caller reads `bump`).
          pure (if out.startsWith "{\"ok\":false" then 1 else 0)

/-! ## `bang rewrite <verb>` (#81) — the CQS COMMAND side over #80's query/read-model side.

OUTPUT CONTRACT (operator ruling, 2026-07-10, verbatim): **every rewrite verb emits the DIFF
between source and rewritten program BY DEFAULT; `-w` applies the change with an explicit write.**
Immutable by default, mutation opt-in — the language's own description-until-forced thesis
(`$`/force, ADR-0007) applied to tooling. `fmt` re-housed as rewrite #0 adopts the SAME contract
(a genuine behavior addition over the pre-existing `bang fmt`, which stays print-only — see
`runFmt`'s own doc comment; `bang rewrite fmt` is a NEW, additional CLI surface, not a replacement).

THE PRESERVATION GATE (the moat feature, #81 item 5): `rename` is gated on BEHAVIOR PRESERVATION
before it ever emits — re-elaborate BOTH the original and rewritten `Prog` through the SAME
`Bang.TypeCheck.checkAndLowerProg` the runner uses, then run BOTH under the kernel ORACLE
(`Bang.Source.eval`, `--engine=oracle`'s own reference) and require the outcomes agree. This code
lives HERE, not in `Bang.Frontend.Rewrite` — `Rewrite.lean` is a LEAF (fan-in 0, `tools/
arch-check.sh`) and cannot reach `checkAndLowerProg`'s eval half without inverting that invariant;
`Main.lean` is the unrestricted Apex-rank consumer `runComp`'s oracle arm already lives in, so the
gate reuses that SAME machinery rather than re-deriving a second eval path. A rewrite that FAILS
preservation aborts loudly (the failure shown) and never emits — falsified in `tools/
test-rewrite.sh` by a deliberately name-colliding/miscompiled rewrite the gate must catch. -/

/-- Unified-diff two strings, line-based, ZERO-context (every changed line shown, `-`/`+`
prefixed; unchanged lines shown bare, matching a minimal `diff -u0`-style rendering) — a small
hand-rolled renderer (the repo's own "small fixed shape beats a new dependency" convention,
`Diagnostics.jsonStr`'s precedent) since no diff library is in the Lean toolchain here. NOT a
byte-exact LCS diff (no minimal-edit-distance alignment) — a POSITIONAL line comparison: line `i`
of `a` vs line `i` of `b`, changed/added/removed by INDEX. This is the honest ceiling for a
rewrite whose changes are typically local (a rename touches few lines; `fmt` re-lays out the
whole file) — sufficient for a human/agent to see WHAT changed, not a general-purpose diff tool. -/
def unifiedDiff (a b : String) : String :=
  let linesA := a.splitOn "\n"
  let linesB := b.splitOn "\n"
  let n := max linesA.length linesB.length
  let rows := (List.range n).filterMap (fun i =>
    let la := linesA[i]?
    let lb := linesB[i]?
    match la, lb with
    | some x, some y => if x == y then some s!" {x}" else some s!"-{x}\n+{y}"
    | some x, none    => some s!"-{x}"
    | none,   some y  => some s!"+{y}"
    | none,   none    => none)
  String.intercalate "\n" rows

#guard unifiedDiff "a\nb\nc" "a\nb\nc" == " a\n b\n c"
#guard unifiedDiff "a\nb\nc" "a\nX\nc" == " a\n-b\n+X\n c"
#guard unifiedDiff "a\nb" "a\nb\nc" == " a\n b\n+c"

/-- Strip exactly ONE trailing `\n`, if present — `IO.FS.readFile`'s own convention (a well-formed
text file ends in a newline the shell/editor added, not a semantic part of the program) vs
`Bang.Format.showProg`'s output (no trailing newline; a total structural fold, nothing appends
one). Without this, EVERY `rewrite fmt`/`rewrite rename` diff on an ordinary (newline-terminated)
file would show a spurious final `-` line even when the program itself is byte-for-byte
unchanged — a presentation artifact of the file/printer convention mismatch, not a real edit. -/
def stripTrailingNewline (s : String) : String :=
  if s.endsWith "\n" then s.dropRight 1 else s

#guard stripTrailingNewline "a\nb\n" == "a\nb"
#guard stripTrailingNewline "a\nb" == "a\nb"

/-- Does `unifiedDiff a b` report NO changes (every line prefixed with a bare space)? The
`diff-vs--w` battery's own definition of "byte-identical" at the LINE-DIFF layer, reused so the
CLI's success message can say "no changes" honestly rather than always printing a diff header.
Compares AFTER `stripTrailingNewline` on `a` (the file-read side) — see that function's doc
comment for why. -/
def diffIsEmpty (a b : String) : Bool := stripTrailingNewline a == b

/-- Render `p` through the SAME canonical printer `bang fmt` uses (`Bang.Format.showProg`) — the
ONE rendering every rewrite verb diffs against, so `bang rewrite fmt`'s diff and `bang rewrite
rename`'s diff are visually consistent (both show canonical-form source, not a raw re-serialization
that might differ from `bang fmt`'s own output for unrelated reasons). -/
def renderProg (p : Bang.Surface.Prog) : String := Bang.Format.showProg p

/-- THE PRESERVATION GATE (see this section's header): re-elaborate `orig`/`rewritten` via
`checkAndLowerProg` and compare their kernel-oracle (`Bang.Source.eval`) outcomes. `.ok none` on
agreement; `.ok (some msg)` names the FIRST divergence found (elaboration failure on one side but
not the other, or a value/outcome mismatch) — never silently passes a divergent rewrite. Outcomes
are compared via `valPretty`/an outcome-tag string — the SAME rendering `runComp`'s oracle arm
already uses for `.done`, so "the same value" here means exactly what `bang run --engine=oracle`
would print for both programs. -/
def preservationCheck (orig rewritten : Bang.Surface.Prog) : IO (Option String) := do
  match Bang.TypeCheck.checkAndLowerProg orig, Bang.TypeCheck.checkAndLowerProg rewritten with
  | .error e, .ok _ => pure (some s!"preservation: original program failed to elaborate ({e}) — refusing to gate against a broken baseline")
  | .ok _, .error e => pure (some s!"preservation: rewritten program FAILED TO ELABORATE ({e}) — the rewrite is unsound, aborting")
  | .error e1, .error e2 =>
      if e1 == e2 then pure none   -- both sides fail identically (e.g. renaming inside an already ill-typed program) — not a NEW divergence
      else pure (some s!"preservation: both programs fail to elaborate, but with DIFFERENT errors (original: {e1}; rewritten: {e2})")
  | .ok c1, .ok c2 =>
      let outcomeTag (r : Result Val) : String := match r with
        | .done v     => s!"done:{valPretty v}"
        | .oom        => "oom"
        | .escapedCap => "escapedCap"
        | .stuck      => "stuck"
      let o1 := outcomeTag (Bang.Source.eval defaultFuel c1)
      let o2 := outcomeTag (Bang.Source.eval defaultFuel c2)
      if o1 == o2 then pure none
      else pure (some s!"preservation: the kernel oracle DISAGREES after rewriting — original evaluated to [{o1}], rewritten to [{o2}]")

/-- Shared tail every rewrite verb's happy path funnels through: given the ORIGINAL `Prog`, its
rendered source, and the REWRITTEN `Prog`, either print the diff (default) or WRITE the rewritten
form to `path` (`-w`). `gate` is `none` for a rewrite with no preservation obligation (`fmt` — a
no-op on the AST by construction, `Rewrite.fmt`'s own doc comment) or `some` the preservation
message when a GATED rewrite (`rename`) failed it — in which case this function ABORTS before
printing/writing anything, per #81 item 5 ("a rewrite that fails preservation aborts with the
failure shown, does NOT emit"). -/
def emitRewrite (write : Bool) (path : Option String) (origSrc : String) (rewritten : Bang.Surface.Prog)
    (gate : Option String) : IO UInt32 := do
  match gate with
  | some msg => IO.eprintln s!"error: {msg}"; pure 1
  | none =>
      let out := renderProg rewritten
      if write then
        match path with
        | none      => IO.eprintln "error: -w requires a <file.bang> path (cannot write stdin in place)"; pure 1
        | some p    => IO.FS.writeFile ⟨p⟩ out; IO.println s!"wrote {p}"; pure 0
      else
        if diffIsEmpty origSrc out then IO.println "(no changes)"; pure 0
        else IO.println (unifiedDiff (stripTrailingNewline origSrc) out); pure 0

/-- `bang rewrite fmt [<file.bang>] [-w]` — rewrite #0 (#81 item 2): the canonical formatter
re-housed as the first command. No preservation gate (`Rewrite.fmt` is `.ok p` — an AST no-op by
construction; the ONLY thing that can change is printed LAYOUT, which `Format.lean`'s own
idempotency/round-trip `#guard`s already cover at the Lean level). Reads a file if given, else
stdin — mirrors `bang fmt`'s own file-or-stdin convention. -/
def runRewriteFmt (write : Bool) (file : Option String) : IO UInt32 := do
  let src ← match file with
    | none      => (← IO.getStdin).readToEnd
    | some path =>
      match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
      | none   => IO.eprintln s!"error: could not read file '{path}'"; return 2
      | some s => pure s
  match Bang.Surface.parseProg src with
  | .error e => IO.eprintln s!"error: {e}"; pure 1
  | .ok p    =>
      match Bang.Rewrite.fmt p with
      | .error e     => IO.eprintln s!"error: {e}"; pure 1
      | .ok p'       => emitRewrite write file src p' none

/-- `bang rewrite rename <old> <new> <file.bang> [-w]` — the classic first refactoring (#81 item
3): rename a top-level decl + every reference to it, GATED on the preservation check (#81 item 5)
before ever emitting. Requires a FILE (unlike `fmt`, no stdin route — `-w` needs a real path to
write, and the diff-mode default stays consistent with that rather than branching on presence).
Three loud, distinct failures surface directly from `Bang.Rewrite.rename` (missing/ambiguous/
colliding name, ADR-0046) BEFORE the gate ever runs — a rename that can't even be COMPUTED never
reaches preservation-checking. -/
def runRewriteRename (write : Bool) (old new : String) (file : String) : IO UInt32 := do
  match ← (do let s ← IO.FS.readFile ⟨file⟩; pure (some s)) <|> pure none with
  | none     => IO.eprintln s!"error: could not read file '{file}'"; pure 2
  | some src =>
      match Bang.Surface.parseProg src with
      | .error e => IO.eprintln s!"error: {e}"; pure 1
      | .ok p    =>
          match Bang.Rewrite.rename old new p with
          | .error e => IO.eprintln s!"error: {e}"; pure 1
          | .ok p'   =>
              let gate ← preservationCheck p p'
              emitRewrite write (some file) src p' gate

/-- One `SkipReason` → its human-readable report line — `runRewriteAnnotate`'s stderr summary,
never stdout (stdout stays the pure diff/write contract every rewrite verb shares; the skip
report is DIAGNOSTIC context alongside it, mirroring how `checkAndLowerProg`'s errors print to
stderr beside `check`'s ok/fail stdout line). -/
def renderSkipReason : Bang.Rewrite.SkipReason → String
  | .alreadyAnnotated          => "already annotated"
  | .notValueTyped             => "no value-level type (trait/impl/data/effect)"
  | .typeCheckFailed msg       => s!"does not type-check standalone ({msg})"
  | .userLabelInRow row        => s!"row {row} names a USER effect — annotate cannot express it yet (a known gap: row annotations only name the four builtin effects throws/state/stm/Div today; see docs/reference/language.md's `bang rewrite annotate` section)"
  | .typeNotRoundTrippable ty  => s!"inferred type '{ty}' has no parseable surface ascription (a data-type/internal shape)"

/-- `bang rewrite annotate [<file.bang>] [-w]` (#82 item 1): infer types AND effect rows for every
top-level `letD` lacking an explicit ascription, splice them in. UNGATED (unlike `rename`) — see
`Bang.Rewrite.annotate`'s own module header for why an added ascription cannot silently change
program behavior — but this runner still defensively re-elaborates the rewritten `Prog` via
`checkAndLowerProg` before ever emitting (a sanity check, not a preservation gate: an ascription
that fails to re-elaborate is a BUG in `annotate`'s own round-trip claim, surfaced loudly rather
than emitted). Reads a file if given, else stdin (mirrors `fmt`'s convention; `-w` still requires
a real file path, same as every other verb). The per-decl skip/annotate SUMMARY prints to
STDERR (never stdout — the diff/write contract on stdout stays uniform across every rewrite verb),
so `effect creep becomes diff-visible` (#82's own framing) shows on a re-run: a decl whose row grew
a new label appears as a changed line in the NEXT diff. -/
def runRewriteAnnotate (write : Bool) (file : Option String) : IO UInt32 := do
  let src ← match file with
    | none      => (← IO.getStdin).readToEnd
    | some path =>
      match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
      | none   => IO.eprintln s!"error: could not read file '{path}'"; return 2
      | some s => pure s
  match Bang.Surface.parseProg src with
  | .error e => IO.eprintln s!"error: {e}"; pure 1
  | .ok p    =>
      let outcomes := Bang.Rewrite.annotateOutcomes p
      for (d, o) in outcomes do
        match o with
        | .annotated ty => IO.eprintln s!"  + {d.name} : {Bang.Format.showTy ty}"
        | .skipped why  => IO.eprintln s!"  · {d.name} — {renderSkipReason why}"
      match Bang.Rewrite.annotate p with
      | .error e => IO.eprintln s!"error: {e}"; pure 1
      | .ok p'   =>
          match Bang.TypeCheck.checkAndLowerProg p' with
          | .error e => IO.eprintln s!"error: annotate produced a program that fails to elaborate ({e}) — this is a bug in annotate's own round-trip claim, aborting"; pure 1
          | .ok _    => emitRewrite write file src p' none

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
avoids widening `NamedOutcome`'s public shape for a cosmetic label). `.skipped` (#113) counts as
PASS for the tally — not sampling an unreachable impl's law is not itself a failure (the
unreachable-impl `.untypeable` line already forces a non-zero exit); it renders `–` (a dash, not
`✓`/`✗`) so a reader can tell "not run" apart from "ran and held" at a glance. -/
def renderOutcome (o : Bang.LawTest.NamedOutcome) : String × Bool :=
  let name := s!"{o.traitName}.{o.lawName}"
  match o.outcome with
  | .holds n           => (s!"✓ {name} — PASS ({n} samples)", true)
  | .counterexample ws => (s!"✗ {name} — FAIL — counterexample {ws}", false)
  | .untypeable m       => (s!"✗ {name} — ERROR — {m}", false)
  | .evalStuck ws       => (s!"✗ {name} — STUCK — witness {ws} did not evaluate to a Bool", false)
  | .skipped m          => (s!"– {name} — SKIPPED — {m}", true)

/-- `bang test [<file.bang>]` (#60's CLI wiring): discover EVERY trait-law instance in a program
(`Bang.LawTest.runLawsFromSource`, the landed #60 discovery seam) and sample-check each one,
reporting per-law PASS/FAIL/ERROR/STUCK. Reads a file if given, else stdin (mirrors `fmt`/`check`'s
file-or-stdin convention). RESOLVER-AWARE for a FILE with an `import`/`use` header (#117's gap-2
fix — mirrors `runCheck`'s exact single-file-fast-path/resolver split): `resolveEntryFile` (the
SAME multi-file resolver `bang check`/`bang run` use) produces the merged `Prog`, then
`Bang.TypeCheck.lawTestSourceOfProg` runs `expandDerives`/`injectPrelude` on it and re-derives a
source STRING — closing the gap where a prelude-hosted `trait Eq`/`trait Ord` (ADR-0097's
migration) was invisible to law discovery, since `Bang.LawTest.runLawsFromSource` itself still
operates on a raw decls-string, unchanged. Stdin (no file path — no resolver context to resolve
relative imports against) and a file with NO `import`/`use` header stay on the exact prior
zero-resolver fast path (`Bang.Surface.parseProg` directly) — no behavior change for the common
single-file case.

DECLS-ONLY INPUT, ENFORCED (a real footgun found while writing this slice's own manual test):
`runLawsFromSource` appends ITS OWN throwaway `0` body for discovery, and its per-sample test
programs splice `progPrelude` (== the WHOLE input string) directly against a SEPARATE generated
readback body. A file that ALREADY ends in a trailing expression (an ordinary bang program's
usual shape — even a bare `0`) glues onto that spliced body as a second, adjacent expression —
the SAME literal-adjacency trap `runCheck`'s own doc comment warns about elsewhere — and every
law silently reports STUCK (`0 (let a = ... in ...)`, applying a literal to a computation) with
NO indication the input shape, not the law, is the problem. Pre-checked here via `parseProg` +
`Prog.isLibrary` (true ⟺ no trailing body) BEFORE ever calling `runLawsFromSource`, so the error
names the actual cause instead of a confusing blanket STUCK on every discovered law. The
resolver-aware path re-checks `isLibrary` on the MERGED `Prog` (not just the entry file's own
header) — an imported module's own trailing expression cannot corrupt the merge (`mergeModules`
never merges a non-entry module's body in), but this keeps the check symmetric with the fast path.

EXIT CODES: `0` every discovered law holds (including the vacuous "no laws found" case — #60's own
`runLawsFromSource "" ...` guard: zero laws is not a failure); `1` at least one law
FAILED/ERRORED/STUCK, the input has a trailing body (the decls-only check above), a resolution
failure (missing import, cycle, private access — the SAME exit `bang check`/`bang run` give), OR
the source didn't even elaborate for discovery (`lawInstancesOf`'s own error, e.g. malformed
decls) — the SAME "usage/parse/elaboration error" code every other subcommand uses for a
source-level failure; `2` the file could not be read (the `check`/`:load` convention: a tool error
is not a diagnostic). -/
def runTest (file : Option String) : IO UInt32 := do
  -- Determine the source string to feed `runLawsFromSource`: stdin or a headerless file take the
  -- exact prior zero-resolver path; a file WITH an `import`/`use` header routes through the SAME
  -- resolver `bang check`/`bang run` use, then `lawTestSourceOfProg` (#117's gap-2 fix).
  let src ← match file with
    | none      => (← IO.getStdin).readToEnd
    | some path =>
      match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
      | none   => IO.eprintln s!"error: could not read file '{path}'"; return 2
      | some s =>
        match Bang.Surface.parseProgLocated s with
        | .error (m, _) => IO.eprintln s!"error: parse error: {m}"; return 1
        | .ok headerProg =>
          if headerProg.imports.isEmpty && headerProg.uses.isEmpty then pure s
          else
            -- `resolveEntryFileRaw`, NOT `resolveEntryFile`: the D5 entry rule the latter applies
            -- would reject a decls-only file outright ("nothing to run"), but decls-only is
            -- EXACTLY `bang test`'s expected shape (the `!p.isLibrary` check below, unchanged).
            match ← resolveEntryFileRaw path with
            | .error e   => IO.eprintln s!"error: {e}"; return 1
            | .ok merged =>
              match Bang.TypeCheck.lawTestSourceOfProg merged with
              | .error e   => IO.eprintln s!"error: {e}"; return 1
              | .ok merged => pure merged
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

/-! ## `bang lint <file>` (#82 item 2) — the rule package over the query fact base. -/

/-- One `Finding` → its JSON object — `{"rule","severity","decl","message"}`, `decl` rendered
`null` for a whole-file finding (mirrors `Query.jsonOptStrField`'s "absence over a guessed
default" convention — this module cannot import `Bang.Query`'s private JSON helpers, an unrelated
LEAF, so the shape is hand-rolled here identically, `Main.lean`'s existing `checkFailJson`
precedent for a small fixed JSON shape). -/
def findingJson (f : Bang.Lint.Finding) : String :=
  let declField := match f.decl with
    | some n => Bang.Diagnostics.jsonStr n
    | none   => "null"
  "{\"rule\":" ++ Bang.Diagnostics.jsonStr f.rule ++
    ",\"severity\":\"" ++ f.severity.toString ++ "\"" ++
    ",\"decl\":" ++ declField ++
    ",\"message\":" ++ Bang.Diagnostics.jsonStr f.message ++ "}"

/-- The `--json` report: `{"ok":bool,"findings":[Finding,...]}` — `ok` is `true` only when NO
finding reaches `.warning` (mirrors `check --json`'s `ok:true ⟺ no diagnostics` convention,
narrowed to `.warning`-and-above since `.info` findings, by their own severity's definition, don't
constitute a failure — an `unused-pub` decl is not wrong, just worth knowing about). -/
def lintReportJson (findings : List Bang.Lint.Finding) : String :=
  let ok := !findings.any (·.severity == .warning)
  "{\"ok\":" ++ (if ok then "true" else "false") ++
    ",\"findings\":[" ++ String.intercalate "," (findings.map findingJson) ++ "]}"

/-- The human-table report: one line per finding, `[SEVERITY] rule decl — message` (`decl`
rendered `(file)` for a whole-file finding), then a `N warning(s), M info` tally. -/
def renderFindingHuman (f : Bang.Lint.Finding) : String :=
  let sev := match f.severity with | .warning => "WARN" | .info => "INFO"
  let declStr := f.decl.getD "(file)"
  s!"[{sev}] {f.rule} {declStr} — {f.message}"

/-- `bang lint [<file.bang>] [--json] [--quiet-clean]` (#82 item 2): run every rule
(`Bang.Lint.lintProg`) over the file, report human table (default) or `--json`. EXIT CONTRACT
(task #40): `0` when no finding reaches `.warning` (an `.info`-only or empty report still exits
0 — mirrors `check --json`'s "the caller inspects `ok`" convention); `1` when any `.warning`
finding is present; `2` the file could not be read (the `check`/`test` convention: a tool error is
not a diagnostic). `--quiet-clean` suppresses the "no findings" success line on a CLEAN human-table
report (a scripted caller wanting only nonzero-exit-on-real-findings, never printing on the happy
path) — has no effect on `--json` (the JSON body is always the complete, stable answer; there is
no "quiet" JSON). Reads a file if given, else stdin (mirrors `fmt`/`check`'s convention). NOT
resolver-aware in v1 (like `test`/stdin `check`) — `Bang.Lint`'s rules operate on ONE parsed
`Prog`; a resolver-aware multi-file upgrade is the natural follow-up if that need arises, matching
`bang test`'s own documented non-resolver precedent. -/
def runLint (json quietClean : Bool) (file : Option String) : IO UInt32 := do
  let src ← match file with
    | none      => (← IO.getStdin).readToEnd
    | some path =>
      match ← (do let s ← IO.FS.readFile ⟨path⟩; pure (some s)) <|> pure none with
      | none   => IO.eprintln s!"error: could not read file '{path}'"; return 2
      | some s => pure s
  match Bang.Surface.parseProg src with
  | .error e =>
      if json then IO.println (Bang.Query.errorJsonOk e) else IO.eprintln s!"error: {e}"
      pure 1
  | .ok p    =>
      let findings := Bang.Lint.lintProg src p
      let hasWarning := findings.any (·.severity == .warning)
      if json then
        IO.println (lintReportJson findings)
      else
        if findings.isEmpty then
          if !quietClean then IO.println "no findings"
        else
          for f in findings do IO.println (renderFindingHuman f)
          let warnCount := (findings.filter (·.severity == .warning)).length
          let infoCount := (findings.filter (·.severity == .info)).length
          IO.println s!"──────────────────────────────"
          IO.println s!"{warnCount} warning(s), {infoCount} info"
      pure (if hasWarning then 1 else 0)

/-! ## `bang new NAME` — scaffold a runnable example project (plan 013 slice 7).

Writes an `examples/<NAME>/` directory in the check-examples convention: a runnable starter
`main.bang`, a `README.md` stub, and an `expected.txt` PRODUCED BY ACTUALLY RUNNING the
starter (never hand-written — the oracle can't drift from a byte someone typed). `--module`
scaffolds the multi-file import shape: a sibling `Lib.bang` exporting one `pub` fn that
`main.bang` consumes via `use Lib (greet)`. The scaffolded sources deliberately avoid every
reserved binder word (`get put raise new read write resume param with`, Surface.lean `pIdent`)
so a scaffold always parses. -/

/-- The single-file starter's `main.bang`. -/
def newStarterMain : String :=
  "-- A starter bang program. `bang run main.bang` runs it; the value prints to stdout.\n" ++
  "-- Every value is a description until forced with `$` (ADR-0007); `bare` = description,\n" ++
  "-- `$name` = the forced value. Edit `main`, then re-run — `bang test --update " ++
  "<NAME>` re-bakes expected.txt.\n" ++
  "let greeting = \"hello from bang\"\n" ++
  "let main = $concat greeting \"!\"\n"

/-- The `--module` variant's library `Lib.bang` — one `pub` export consumed by main. -/
def newStarterLib : String :=
  "-- A library module. `pub` exports a decl; a bare (non-`pub`) decl stays module-private\n" ++
  "-- (ADR-0093 D3). This file is imported, not run directly.\n" ++
  "pub let greet = {fun who => $concat \"hello, \" who}\n"

/-- The `--module` variant's `main.bang` — consumes Lib's export. -/
def newStarterModuleMain : String :=
  "-- Multi-file starter: `use Lib (greet)` hoists Lib's `pub` fn into unqualified scope\n" ++
  "-- (same-directory import; `bang run main.bang` resolves + merges Lib.bang automatically).\n" ++
  "use Lib (greet)\n" ++
  "let main = $greet \"bang\"\n"

/-- The scaffolded README stub (`{name}` and the `--module` note interpolated). -/
def newReadme (name : String) (isModule : Bool) : String :=
  s!"# {name}\n\n" ++
  "Scaffolded by `bang new" ++ (if isModule then " --module " else " ") ++ s!"{name}`.\n\n" ++
  "- `main.bang` — the entry program (`bang run examples/" ++ name ++ "/main.bang`).\n" ++
  (if isModule then
    "- `Lib.bang` — a library module; its `pub greet` is consumed by `main.bang`.\n" else "") ++
  "- `expected.txt` — the run oracle (produced by `bang new`, re-baked by " ++
  s!"`bang test --update {name}`); `tools/check-examples.sh` diffs `main.bang`'s stdout against it.\n\n" ++
  "Replace this stub with what the example teaches.\n"

/-- Evaluate a fully-resolved `Prog` to its printed value STRING (the exact bytes `bang run`
would put on stdout), on the default env engine — so a scaffold's `expected.txt` is what
`bang run` and `check-examples` will actually observe, byte-for-byte. `.error` names the
failing outcome (a scaffold that doesn't run is a loud failure, never a silent empty file). -/
def evalProgToString (prog : Prog) : Except String String :=
  match Bang.TypeCheck.checkAndLowerProg prog with
  | .error e => .error e
  | .ok c    =>
    match Bang.EnvMachine.runE defaultFuel c with
    | .done v => .ok (valPretty v)
    | _       => .error "the starter produced no first-order value on the env engine"

/-- Run `bang new NAME [--module]`: scaffold `examples/NAME/` per the check-examples convention
(§ the doc block above). Refuses loudly if the target directory already exists (ADR-0046: never
silently overwrite). The `expected.txt` is COMPUTED by running the just-written `main.bang`, so
it can never disagree with the sources; a starter that fails to run aborts BEFORE any expected.txt
is written (a half-scaffolded dir with a stale/empty oracle is worse than a loud failure). -/
def runNew (name : String) (isModule : Bool) : IO UInt32 := do
  let root ← IO.currentDir
  let dir := root / "examples" / name
  if ← dir.pathExists then
    IO.eprintln s!"error: {dir} already exists — pick a new name or remove it first"
    return 1
  IO.FS.createDirAll dir
  let mainSrc := if isModule then newStarterModuleMain else newStarterMain
  IO.FS.writeFile (dir / "main.bang") mainSrc
  if isModule then IO.FS.writeFile (dir / "Lib.bang") newStarterLib
  IO.FS.writeFile (dir / "README.md") (newReadme name isModule)
  -- expected.txt is the RUN oracle: resolve + run the just-written main.bang, capture its value.
  match ← resolveEntryFile ((dir / "main.bang").toString) with
  | .error e =>
    IO.eprintln s!"error: scaffolded starter failed to resolve: {e}"
    return 1
  | .ok merged =>
    match evalProgToString merged with
    | .error e =>
      IO.eprintln s!"error: scaffolded starter failed to run: {e} — no expected.txt written"
      return 1
    | .ok out =>
      IO.FS.writeFile (dir / "expected.txt") (out ++ "\n")
      IO.println s!"created examples/{name}/"
      IO.println s!"  main.bang     ({mainSrc.length} bytes)"
      if isModule then IO.println s!"  Lib.bang      (pub greet, consumed by main)"
      IO.println s!"  README.md"
      IO.println s!"  expected.txt  → {out}"
      IO.println s!"run it:  bang run examples/{name}/main.bang"
      return 0

def usage : String :=
  "bang — the lang-bang runner\n\n" ++
  "USAGE:\n" ++
  "  bang run  [FLAGS] <file.bang>      run a bang program from a file\n" ++
  "  bang eval [FLAGS] \"<surface expr>\"  run a surface expression directly\n" ++
  "  bang repl [FLAGS]                  interactive read-eval-print loop (issue #7)\n" ++
  "             --engine=oracle|compiled|env   select the execution engine (ADR-0094; default env)\n" ++
  "             --no-typecheck                 skip the type gate (oracle/differential testing)\n" ++
  "             --fuel N                       raise the step ceiling above the default " ++
  s!"{defaultFuel}\n" ++
  "                                             (issue #103); applies to run/eval/repl on every " ++
  "engine\n" ++
  "                                             (the compiled engine scales it ×10 internally for " ++
  "its\n" ++
  "                                             finer machine-instruction unit — see `runCompiled`)\n" ++
  "  bang fmt  [<file.bang>]            print the canonical form (issue #58); reads stdin if no file\n\n" ++
  "  bang check [FLAGS] [<file.bang>]   type-check only, no run (issue #59); reads stdin if no file\n" ++
  "             --json                  emit agent-facing structured JSON diagnostics on stdout\n\n" ++
  "  bang explain <CODE>                print the teaching entry for a stable diagnostic code\n" ++
  "                                     (the rustc `error[B004]` pattern, plan 013 s5): summary,\n" ++
  "                                     explanation, and a minimal triggering example. Codes appear\n" ++
  "                                     in `check` output (`error[B004]:` / the `explainCode` JSON\n" ++
  "                                     field). An unknown code is a LOUD error on stderr, exit 1.\n\n" ++
  "  bang new <NAME> [--module]         scaffold examples/<NAME>/ — a runnable starter main.bang, a\n" ++
  "                                     README stub, and an expected.txt PRODUCED BY RUNNING the\n" ++
  "                                     starter (plan 013 s7, never hand-written). `--module` picks\n" ++
  "                                     the multi-file import shape (a sibling Lib.bang whose `pub`\n" ++
  "                                     fn main.bang consumes). Refuses if the dir already exists.\n\n" ++
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
  "    bang query hover [<file.bang>] <line> <col>\n" ++
  "                                             the decl at 1-INDEXED <line>:<col> (issue #52 slice 5),\n" ++
  "                                             DECL granularity — a cursor anywhere in a decl's body\n" ++
  "                                             resolves to that WHOLE decl, rendered like `dump`'s own\n" ++
  "                                             per-decl fact plus its name-token \"span\"; a miss\n" ++
  "                                             (cursor before any decl) is {\"ok\":false,...}, exit 0\n" ++
  "                                     `dump`/`symbols`/`type`/`effects`/`def`/`refs`/`hover` read\n" ++
  "                                     stdin if no <file.bang> is given (except `type`/`def`/`refs`,\n" ++
  "                                     which always require a file — name-addressed forms);\n" ++
  "                                     a <file.bang> WITH imports/uses is resolved the SAME way\n" ++
  "                                     `bang check` resolves it (imports visible to every op).\n" ++
  "                                     `def`/`refs` are DECL-granularity, not sub-decl — see #52.\n\n" ++
  "  bang rewrite <verb> ...             the CQS COMMAND side over `query`'s read model (issue #81);\n" ++
  "                                     every verb prints a DIFF (source → rewritten) by default —\n" ++
  "                                     IMMUTABLE unless `-w` (write) is given (description-until-\n" ++
  "                                     forced, applied to tooling).\n" ++
  "    bang rewrite fmt [<file.bang>] [-w]       rewrite #0: the canonical formatter (issue #58),\n" ++
  "                                               re-housed as a command; reads stdin if no file\n" ++
  "    bang rewrite rename <old> <new> <file.bang> [-w]\n" ++
  "                                               rename a top-level decl + every reference to it;\n" ++
  "                                               GATED on the differential PRESERVATION check (the\n" ++
  "                                               kernel oracle must agree on both programs) before\n" ++
  "                                               ever emitting — a failing gate aborts, no diff/write\n" ++
  "    bang rewrite annotate [<file.bang>] [-w]  infer types AND effect rows for every top-level\n" ++
  "                                               `let` lacking an ascription, splice them in — a\n" ++
  "                                               PR that adds an effect to a row shows as a diff on\n" ++
  "                                               re-run; row annotations name only the four builtin\n" ++
  "                                               effects today (throws/state/stm/Div) — a decl whose\n" ++
  "                                               row carries a USER effect is skipped with a note\n" ++
  "                                               (stderr); reads stdin if no file\n" ++
  "                                     `-w` applies the change to `<file.bang>` in place; the default\n" ++
  "                                     prints a unified diff to stdout and touches nothing on disk.\n\n" ++
  "  bang lint [<file.bang>] [--json] [--quiet-clean]\n" ++
  "                                     rule package over the query fact base (issue #82 item 2):\n" ++
  "                                     dead-private (an unreferenced non-pub decl, warning),\n" ++
  "                                     unused-pub (a pub decl nothing in-module references, info),\n" ++
  "                                     fmt-divergence (the file's layout ≠ its canonical form,\n" ++
  "                                     warning). Human table by default, `--json` for the agent\n" ++
  "                                     schema. Exit 0 unless a `warning`-severity finding is\n" ++
  "                                     present; `--quiet-clean` suppresses the \"no findings\" line\n" ++
  "                                     on a clean human-table report. Reads stdin if no file.\n\n" ++
  "  bang holes [<file.bang>]           list every decl carrying a residual/underdetermined\n" ++
  "                                     position (a checker hole the inference could not pin down,\n" ++
  "                                     rendered #N in the type/row; issue #82 item 3). ALWAYS JSON\n" ++
  "                                     on stdout (agents are the audience). Resolver-aware like\n" ++
  "                                     `query`; reads stdin if no file. Empty holes array + exit 0\n" ++
  "                                     when the program is fully pinned.\n\n" ++
  "  bang impact <file.bang> <decl>     the transitive DEPENDENTS of <decl> — the pre-edit blast\n" ++
  "                                     radius (what breaks if you change it), reverse closure over\n" ++
  "                                     the same ref-graph `query refs`/`dump` expose (issue #82\n" ++
  "                                     item 5). ALWAYS JSON. Resolver-aware; empty dependents +\n" ++
  "                                     exit 0 when nothing depends on it.\n\n" ++
  "  bang semver-diff <old.bang> <new.bang>\n" ++
  "                                     the public-surface diff of two programs → the required\n" ++
  "                                     version bump (added/removed/changed pub decls + a derived\n" ++
  "                                     major/minor/patch `bump`; issue #82 item 6, #72's engine).\n" ++
  "                                     ALWAYS JSON.\n\n" ++
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
def replStep (typecheck : Bool) (engine : Engine) (fuel : Nat) (binds : List ReplBinding) (line : String) :
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
      let code ← runSource typecheck engine fuel (wrapBindings binds src)
      return (binds, code)
  else if line.startsWith ":let" then
    match splitLetCmd (line.drop 4).toString with
    | none => IO.eprintln "error: `:let` expects `:let <name> = <expr>`"; return (binds, 1)
    | some (name, rhs) => return (binds ++ [(name, rhs)], 0)
  else if line.startsWith ":" then
    IO.eprintln s!"error: unknown command '{line}' (:help for the list)"; return (binds, 1)
  else
    let code ← runSource typecheck engine fuel (wrapBindings binds line)
    return (binds, code)

/-- The interactive/piped loop: read a line, `replStep`, repeat until `:q`/`:quit`/EOF. Works
identically whether stdin is a terminal or a pipe (`echo 'expr' | bang repl` runs each line and
exits on EOF) — `IO.FS.Stream.getLine` doesn't care which; that is what makes the non-interactive
(agent-driven) use case work for free, per the operator's agent-first framing. Tracks the exit
code of the LAST line that actually ran (silent lines don't overwrite it), so a piped single-expr
session's exit code matches `bang eval`'s for the same program. -/
partial def runRepl (typecheck : Bool) (engine : Engine) (fuel : Nat) : IO UInt32 := do
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
        let (binds', code) ← replStep typecheck engine fuel binds line
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
      let fuel       := parseFuel rest
      match stripHostFlags (stripFuelFlag rest) |>.filter (fun a => !("--".isPrefixOf a)) with
      | [arg] =>
        match ← resolveEntryFile arg with
        | .error e   => IO.eprintln s!"error: {e}"; pure 1
        | .ok merged =>
          -- ADR-0104: `--env=real` / `--record` / `--replay` route through the host-IO driver;
          -- otherwise the ordinary pure run (sim = the default engine).
          if wantsHostEnv rest then
            runHostProg fuel (parseMaxHostRequests rest) (parseAllow rest)
              (parseRecord rest) (parseReplay rest) merged
          else runResolvedProg typecheck engine fuel merged
      | _ => IO.eprintln usage; pure 1
    else if cmd == "eval" then
      let engine     := parseEngine rest
      let typecheck  := !rest.contains "--no-typecheck"
      let fuel       := parseFuel rest
      match stripFuelFlag rest |>.filter (fun a => !("--".isPrefixOf a)) with
      | [arg] => runSource typecheck engine fuel arg
      | _ => IO.eprintln usage; pure 1
    else if cmd == "repl" then
      let engine    := parseEngine rest
      let typecheck := !rest.contains "--no-typecheck"
      let fuel      := parseFuel rest
      runRepl typecheck engine fuel
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
    else if cmd == "explain" then
      -- `bang explain <CODE>` (plan 013 s5): exactly one positional code; anything else is usage.
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [code] => runExplain code
      | _      => IO.eprintln usage; pure 1
    else if cmd == "new" then
      -- `bang new <NAME> [--module]` (plan 013 s7): scaffold examples/<NAME>/. `--module` picks the
      -- multi-file import shape; any OTHER `--`-prefixed arg falls to usage (mirrors run/check).
      let isModule := rest.contains "--module"
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [name] => runNew name isModule
      | _      => IO.eprintln usage; pure 1
    else if cmd == "test" then
      -- `bang test [<file.bang>]` discovers + checks laws; `bang test --update <NAME>` (plan 013 s8)
      -- is handled at the HARNESS level (tools/check-examples.sh --update), NOT here — `test`'s CLI
      -- shape reads a single .bang FILE, whereas --update names an example DIRECTORY the run-oracle
      -- harness owns (see that script's header). No flags on this verb this slice.
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
      | ["hover", file, lineS, colS] =>
          match lineS.toNat?, colS.toNat? with
          | some line, some col => runQueryHover (some file) line col
          | _, _                 => IO.eprintln usage; pure 1
      | ["hover", lineS, colS] =>
          match lineS.toNat?, colS.toNat? with
          | some line, some col => runQueryHover none line col   -- stdin, no path to resolve imports
          | _, _                 => IO.eprintln usage; pure 1
      | _                       => IO.eprintln usage; pure 1
    else if cmd == "rewrite" then
      -- `bang rewrite <verb> ...` (#81). `-w` may appear anywhere; every OTHER `--`-prefixed arg
      -- is unrecognized (mirrors `query`'s own "unknown flag falls to usage" convention).
      let write := rest.contains "-w"
      let pos := rest.filter (fun a => a != "-w" && !("--".isPrefixOf a))
      match pos with
      | ["fmt", file] => runRewriteFmt write (some file)
      | ["fmt"]       => runRewriteFmt write none
      | ["rename", old, new, file] => runRewriteRename write old new file
      | ["annotate", file] => runRewriteAnnotate write (some file)
      | ["annotate"]       => runRewriteAnnotate write none
      | _             => IO.eprintln usage; pure 1
    else if cmd == "lint" then
      -- `bang lint [<file.bang>] [--json] [--quiet-clean]` (#82 item 2). `--json`/`--quiet-clean`
      -- may appear anywhere before the single optional positional (mirrors `check`'s own
      -- `--json`-anywhere convention); any OTHER `--`-prefixed arg falls to usage.
      let json := rest.contains "--json"
      let quietClean := rest.contains "--quiet-clean"
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | []      => runLint json quietClean none
      | [arg]   => runLint json quietClean (some arg)
      | _       => IO.eprintln usage; pure 1
    else if cmd == "holes" then
      -- `bang holes [<file.bang>]` (#82 item 3). ALWAYS JSON (agents are the audience — no `--json`
      -- flag, matching `query`'s own convention); any `--`-prefixed arg falls to usage.
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | []      => runHoles none        -- read stdin
      | [arg]   => runHoles (some arg)
      | _       => IO.eprintln usage; pure 1
    else if cmd == "impact" then
      -- `bang impact <file.bang> <decl>` (#82 item 5). ALWAYS JSON; file THEN decl (file-first,
      -- matching `query type`'s own file-first order — the file is unambiguous, the decl names
      -- what to blast-radius). A stray `--`-prefixed arg falls to usage.
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [file, decl] => runImpact file decl
      | _            => IO.eprintln usage; pure 1
    else if cmd == "semver-diff" then
      -- `bang semver-diff <old.bang> <new.bang>` (#82 item 6). ALWAYS JSON; OLD then NEW positional.
      match rest.filter (fun a => !("--".isPrefixOf a)) with
      | [oldF, newF] => runSemverDiff oldF newF
      | _            => IO.eprintln usage; pure 1
    else
      IO.eprintln usage; pure 1
  | _ => IO.eprintln usage; pure 1
