# Plan 005: Contain module resolution to the project tree — normalize and check import paths

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- Main.lean tools/test-modules.sh`
> If either file changed since this plan was written, compare the "Current
> state" excerpts against the live code before proceeding; on a mismatch,
> treat it as a STOP condition.

## Status

- **Priority**: P3
- **Effort**: M
- **Risk**: LOW (additive check; loud error on violation)
- **Depends on**: none (composes with plan 004: `tools/test-modules.sh` gains a case here, and 004 wires that script into `verify`)
- **Category**: security (defensive hardening — not an exploitable vulnerability today)
- **Planned at**: commit `f1cb2cf`, 2026-07-10; **REVISED (reviewer ruling, same day)** after the executor's correct STOP: the plan's premise "`root` = the project tree" was WRONG — `root` is `IO.currentDir`, only the *fallback probe* of the same-dir-then-root search order (ADR-0093 D1); entry files legitimately live outside it (all 33 test fixtures do). **Containment boundary re-ruled: a resolved module's real path must be under the ENTRY FILE's real directory subtree OR under the real `root` (CWD) subtree** — the tokenizer's no-`..` guarantee makes those two trees exactly the reachable-without-symlinks set, so all existing behavior is preserved and symlink escapes are still caught. `containedRealPath` takes both roots (or a list); the escape diagnostic names the resolved path AND both allowed trees.

## Why this matters

`bang`'s module resolver turns import names into file paths and reads them. The tokenizer already prevents `../` inside a module name (`.` and `/` are splitting punctuators, so `import ../x` cannot parse as one name — audited and confirmed). The residual vector is **symlinks**: a symlink inside the project tree pointing outside it lets a `.bang` file's import chain read arbitrary readable files as module source. Exploitation requires an attacker who controls both a `.bang` file you compile AND a symlink in the tree — a real but narrow scenario (e.g. compiling an untrusted repo). This is defense-in-depth for a compiler that will increasingly be run on third-party code (agent workflows, CI), plus a loud, specific diagnostic instead of a confusing parse error on binary garbage.

## Current state

- `Main.lean:208-214` — the documented probe order (same-dir then root); verbatim:

```lean
def resolveModulePath (root : System.FilePath) (importingDir : System.FilePath) (modName : String) :
    IO (Option System.FilePath) := do
  let sameDir := importingDir / s!"{modName}.bang"
  if ← sameDir.pathExists then return some sameDir
  let atRoot := root / s!"{modName}.bang"
  if ← atRoot.pathExists then return some atRoot
  return none
```

- `Main.lean:231-251` — the recursive walk; it constructs child paths directly (NOT via `resolveModulePath`) and reads them; the relevant lines:

```lean
partial def resolveModule (root : System.FilePath) (modName : String) (path : System.FilePath)
    (st : ResolveState) : IO (Except String ResolveState) := do
  ...
  let some src ← (do let s ← IO.FS.readFile path; pure (some s)) <|> pure none
    | return .error s!"could not read module '{modName}' at '{path}'"
  ...
      let dir := path.parent.getD root
      ...
        match ← resolveModule root imp.modName (Id.run <| dir / s!"{imp.modName}.bang") st' with
```

  (The same `dir / s!"{u.modName}.bang"` shape repeats for `use` at line 248.)

- Error-message convention that binds this plan (`Main.lean:206-207`, ADR-0046): *"the fix is obvious from the message" is the bar, not just "file not found"* — a containment rejection must name both the resolved real path and the root it escaped.
- `tools/test-modules.sh` — the modules gate (ADR-0093: `import`/`use`/`pub`); bash, `set -euo pipefail`, builds fixtures and runs the compiled binary. New cases go here.
- Toolchain: Lean 4 `v4.30.0` (`lean-toolchain`). `IO.FS.realPath : FilePath → IO FilePath` is the symlink-resolving primitive expected available; Step 1 confirms it against this pin before any design commitment.

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell | `nix develop` | banner |
| Fast check of Main.lean | `nix develop --command just check Main.lean` | `✓ no errors or warnings` |
| Build the binary | `nix develop --command lake build bang` | exit 0 |
| Modules gate | `nix develop --command just test-modules` | pass summary, exit 0 |
| Full gate | `nix develop --command just verify` | exit 0 |

## Scope

**In scope**:
- `Main.lean` — a new containment helper + calls at the read boundary of module resolution.
- `tools/test-modules.sh` — one new test case (symlink escape rejected).
- `plans/README.md` (status row).

**Out of scope** (do NOT touch):
- The tokenizer/parser (`Bang/Frontend/Surface.lean`) — module-name lexing is already safe; do not add string-level `..` filtering there (wrong layer).
- The pure merge half (`Bang.TypeCheck.mergeModules`) — containment is an IO-boundary concern; keep it in `Main.lean` where the reads happen.
- Any file under `Bang/Core/`, `Bang/Spec.lean`, `Bang/Meta/`, `Bang/Backend/`.
- The ENTRY file argument itself (`bang run /anywhere/x.bang` is the user naming a file explicitly — do not contain it; containment applies to paths *derived from import names*).

## Steps

### Step 1: Confirm the primitive

Check that `IO.FS.realPath` exists and resolves symlinks under the pinned toolchain: write a 5-line scratch program (in `/tmp`, not the repo) that `realPath`s a symlink you create in `/tmp`, and run it with `lake env lean --run` or as a `#eval` in a scratch file. If `realPath` is absent under `v4.30.0`, STOP.

**Verify**: scratch output shows the symlink's *target* path.

### Step 2: Add the containment helper

In `Main.lean`, next to `resolveModulePath` (~line 208), add:

```lean
/-- Resolve `p` to its real (symlink-free) path and require it inside the real `root` tree.
Import-derived paths only — the entry file is the USER's explicit choice and is never contained.
`none` = escape; the caller's error must name BOTH paths (ADR-0046: the fix must be obvious). -/
def containedRealPath (root : System.FilePath) (p : System.FilePath) : IO (Option System.FilePath) := do
  let rootReal ← IO.FS.realPath root
  let pReal ← IO.FS.realPath p
  -- separator-guarded prefix check: `/proj` must not admit `/project-evil`
  if pReal == rootReal || pReal.toString.startsWith (rootReal.toString ++ "/") then
    return some pReal
  return none
```

(Match the file's doc-comment voice — see the comment on `resolveModulePath` for the register. Call `realPath` only on paths that exist; both call sites below already sit behind existence checks or a read attempt.)

**Verify**: `nix develop --command just check Main.lean` → clean.

### Step 3: Enforce at both derivation sites

1. In `resolveModulePath`: after each `pathExists` success, pass the candidate through `containedRealPath root`; only a `some` returns. A contained-check failure should fall through to `return none`? **No** — an existing-but-escaping path must be a LOUD error, not a silent miss (a miss would fall back to the root probe and mask the event). Change the return type to carry the distinction, or simpler: keep the `Option` but log nothing and instead do the loud check at the single read boundary in step 3.2 — choose the design that keeps `resolveModulePath`'s callers' error messages intact, and record the choice in the commit message.
2. In `resolveModule` (the walk): before `IO.FS.readFile path` (line 236 pre-drift), guard import-derived paths:

```lean
  let some pathReal ← containedRealPath root path
    | return .error s!"module '{modName}': resolved path escapes the project root — '{path}' resolves outside '{root}' (symlinked module sources must stay inside the tree)"
  -- then read pathReal instead of path
```

Note the top-level caller passes the ENTRY file into the walk too — thread a flag or resolve the entry separately so the entry file itself is exempt (see Scope). The clean shape: the entry caller reads+parses the entry file itself and only the *recursive* import/use children go through the guarded read.

**Verify**: `nix develop --command lake build bang` → exit 0; `nix develop --command just test-modules` → all existing cases still pass (in-tree modules, including root-fallback resolution, must be unaffected — `realPath` on the root normalizes consistently).

### Step 4: Add the red test

In `tools/test-modules.sh`, following its existing case pattern (read the script first; keep its `set -euo pipefail` capture-guard discipline — no unguarded `$(a | b)`):

- Fixture: a temp project dir with `main.bang` containing `import outside`; a file `secret.bang` created OUTSIDE the project dir; a symlink `outside.bang` inside the project dir pointing at it.
- Assert: `bang check <proj>/main.bang` exits nonzero AND stderr/stdout contains `escapes the project root`.
- Also add the green control: a legitimate symlink pointing WITHIN the tree still resolves (pin current behavior; if you choose to reject all symlinks instead, record that as a deliberate tightening in the commit message and make this control expect rejection too).

**Verify**: `nix develop --command just test-modules` → passes including the new case(s), and its check-count assertion (if the script has one) is updated.

### Step 5: Full gate + commit

Commit style: `fix(cli): contain import-derived module paths to the project root (plan 005)`.

**Verify**: `nix develop --command just verify` → exit 0.

## Test plan

- Red: symlink inside tree → file outside tree → loud rejection naming both paths.
- Green control: in-tree resolution (same-dir AND root-fallback order per `resolveModulePath`'s doc) unchanged; within-tree symlink behavior pinned explicitly.
- Entry-file exemption: `bang run /tmp/somewhere/standalone.bang` (no imports) still works — add as a case if `test-modules.sh` doesn't already cover an out-of-tree entry file.

## Done criteria

- [ ] `containedRealPath` exists with the doc comment; both derivation sites guarded
- [ ] Entry file explicitly exempt (out-of-tree entry still runs)
- [ ] `just test-modules` includes the symlink-escape red case and passes
- [ ] Escape diagnostic names both the resolved path and the root
- [ ] `nix develop --command just verify` exits 0
- [ ] `plans/README.md` status row updated

## STOP conditions

Stop and report back (do not improvise) if:

- `IO.FS.realPath` is unavailable or behaves differently under `v4.30.0` (Step 1) — report; the fallback design (manual lexical normalization) has different security properties and needs an operator decision.
- Existing `test-modules` cases fail after Step 3 — the root the CLI passes may not be what this plan assumed (e.g. relative vs. absolute); report the actual `root` value at the failure.
- The entry-file exemption can't be implemented without restructuring `resolveModule`'s signature beyond adding one parameter — report the shape instead of refactoring the walk.

## Maintenance notes

- If a future workspace feature (ADR-0089 is queued) introduces multi-root projects, `containedRealPath` needs the root-SET, not a single root — the helper's signature is the seam.
- Reviewer should scrutinize: the separator-guarded prefix check (the `/proj` vs `/project-evil` case), and that the rejection path is exercised by a test that actually runs (check the script's count assertion).
- Deferred: sandboxing the compiler's *entire* filesystem view (real capability confinement is an OS/runtime concern, tracked in the OS-inspiration survey `docs/notes/os-inspiration-survey.md` — pledge-as-a-type); this plan only closes the import-derivation vector.
