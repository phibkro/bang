# Plan 001: Add an end-to-end example proving innermost-identity dispatch with two active handlers of the same effect

> **Executor instructions**: Follow this plan step by step. Run every
> verification command and confirm the expected result before moving to the
> next step. If anything in the "STOP conditions" section occurs, stop and
> report — do not improvise. When done, update the status row for this plan
> in `plans/README.md` — unless a reviewer dispatched you and told you they
> maintain the index.
>
> **Drift check (run first)**: `git diff --stat f1cb2cf..HEAD -- examples/ tools/check-examples.sh`
> If any in-scope file changed since this plan was written, compare the
> "Current state" excerpts against the live code before proceeding; on a
> mismatch, treat it as a STOP condition.

## Status

- **Priority**: P1
- **Effort**: S
- **Risk**: LOW
- **Depends on**: none
- **Category**: tests
- **Planned at**: commit `f1cb2cf`, 2026-07-10

## Why this matters

The project's core dispatch principle (glossary in `CLAUDE.md`): **typing is by label, dispatch is by identity**. When two handlers of the *same* effect are simultaneously active, an operation performed on the outer handler's capability must dispatch to the *outer* handler — even though the inner handler (same label) is nearer on the stack. A "nearest-label" dispatcher would get this wrong; that exact bug class was rejected design (the stale `evalD`, ADR-0052).

The kernel has proof-level coverage of this, but the **surface end-to-end path** (parse → elaborate → type-check → lower → run) has zero coverage: an audit verified every example in `examples/` runs at most one handler *per effect* at a time (`stage-swap` selects handlers sequentially, never nested). A future elaborator regression that collapses capability identity to label would pass every existing example. This plan pins the discriminating case in the run-oracle gate.

## Current state

- `examples/` contains 19 example projects, each a directory with `main.bang` + `expected.txt`. None nests two handlers of the same effect.
- `tools/check-examples.sh` — the run-oracle gate. It loops over `examples/*/`, runs each `main.bang` with the compiled `bang` binary, and diffs stdout against `expected.txt`. **New example directories are picked up automatically — no registration step.** Excerpt (`tools/check-examples.sh:28-40`):

```bash
for dir in examples/*/; do
  main="$dir/main.bang"
  expected="$dir/expected.txt"
  name="$(basename "$dir")"
  [ -f "$main" ] || continue
  if [ ! -f "$expected" ]; then
    echo "✗ $name — no expected.txt"; fail=$((fail + 1)); continue
  fi
  got="$("$bang" run "$main" 2>/dev/null)" || true
```

- Existing single-handler example to model after — `examples/handle-custom-tracer/main.bang` (verbatim, complete):

```
effect Net { fetch : Int -> Int }
handle
  (net.fetch(1)) + (net.fetch(2))
with Net as net {
  fetch(n) => n * 10
}
```

  and its `expected.txt` is the single line `30`.

- Surface syntax rules that apply (ADR-0095, `docs/decisions/0095-stage7-handler-surface.md`): the handler binder is introduced by `as <name>`; clause bodies are **bare** (`fetch(n) => n * 10`, no braces); operations are performed as `<binder>.<op>(<args>)`.
- Language gotcha: `read`, `get`, `put`, `raise`, `new`, `write`, `resume`, `with` are reserved names — do not use them as effect op names or binders in the new example.

## Commands you will need

| Purpose | Command | Expected on success |
|---|---|---|
| Enter dev shell (required — bare `lake`/`just` are NOT on PATH) | `nix develop` | shell banner |
| Run one example directly | `nix develop --command bash -c 'lake build bang && .lake/build/bin/bang run examples/handle-custom-nested/main.bang'` | program's stdout |
| Run the full example gate | `nix develop --command just check-examples` | `✓` per example, 0 failures |
| Full gate (before commit) | `nix develop --command just verify` | exit 0 |

Note: the first `lake build` in a fresh clone pulls the Mathlib cache (minutes). Subsequent builds are incremental.

## Scope

**In scope** (the only files you may create/modify):
- `examples/handle-custom-nested/main.bang` (create)
- `examples/handle-custom-nested/expected.txt` (create)
- `examples/handle-custom-nested/README.md` (create, optional — a 3–5 line note naming what the example pins; model on `examples/json/README.md`'s tone)
- `plans/README.md` (status row)

**Out of scope** (do NOT touch):
- Any `.lean` file. This plan is example-corpus only. If the example fails to type-check or run, that is a STOP condition (a finding), not something to fix here.
- `tools/check-examples.sh` — the loop already picks up the new directory.
- Existing examples.

## Git workflow

- Branch: work directly on `main` is acceptable for this repo's flow, or `advisor/001-nested-handler-oracle` if you prefer isolation.
- Commit message style: conventional commits, matching e.g. `test(surface): pin the #94 boundary — …`. Suggested: `test(examples): nested same-effect handlers — pin innermost-identity dispatch (ADR-0055)`.
- The repo pre-commit hook will run `just fitness` + `just verify` automatically. Do not use skip variables.
- Do NOT push unless the operator instructed it.

## Steps

### Step 1: Create the example

Create `examples/handle-custom-nested/main.bang` with exactly:

```
effect Net { fetch : Int -> Int }
handle (
  handle
    (inner.fetch(1)) + (outer.fetch(2))
  with Net as inner {
    fetch(n) => n * 10
  }
) with Net as outer {
  fetch(n) => n * 100
}
```

Semantics this pins: `inner.fetch(1)` dispatches to the inner handler (`1 * 10 = 10`); `outer.fetch(2)` must dispatch to the **outer** handler by capability identity (`2 * 100 = 200`) even though the inner handler of the same effect `Net` is nearer. Expected program result: `210`.

A nearest-label (wrong) dispatcher would route `outer.fetch(2)` to the inner handler and print `30`. **That is the discriminating value — see STOP conditions.**

**Verify**: `nix develop --command bash -c 'lake build bang >&2 && .lake/build/bin/bang run examples/handle-custom-nested/main.bang'` → prints `210`

### Step 2: Pin the expectation

Write `examples/handle-custom-nested/expected.txt` containing the single line:

```
210
```

**Verify**: `nix develop --command just check-examples` → all examples `✓`, including `✓ handle-custom-nested → 210`, `0` failures.

### Step 3: Full gate + commit

Run the full gate, then commit the new directory by pathspec.

**Verify**: `nix develop --command just verify` → exit 0. Then `git status --porcelain` shows nothing unexpected staged/modified outside the in-scope list.

## Test plan

The example IS the test — it becomes a permanent leg of the run-oracle gate (`check-examples`, which runs inside `just verify` and the pre-commit hook). Cases covered: two simultaneously active handlers of one effect; outer-cap dispatch past a nearer same-label handler; inner-cap dispatch as control.

## Done criteria

- [ ] `examples/handle-custom-nested/{main.bang,expected.txt}` exist
- [ ] `nix develop --command just check-examples` exits 0 and lists `handle-custom-nested`
- [ ] `nix develop --command just verify` exits 0
- [ ] No files outside the in-scope list are modified (`git status --porcelain`)
- [ ] `plans/README.md` status row updated

## STOP conditions

Stop and report back (do not improvise) if:

- **The program prints `30`** — that means dispatch is by nearest label, not identity: a real correctness bug in the surface→kernel pipeline contradicting ADR-0052/ADR-0055. Report it verbatim with the output; do not adjust `expected.txt` to make the gate green.
- The program fails to parse or type-check. The nested form may be hitting an elaborator limitation (the ADR-0095 D4 ret-shape restriction or a scoping gap). Report the exact diagnostic; do not restructure the program beyond whitespace to work around it.
- The program prints anything other than `210` or `30` — report the value and diagnostic.
- `check-examples` fails on a *pre-existing* example (baseline was 19/19 green at `f1cb2cf`).

## Maintenance notes

- If the future explicit `resume(w)` form (ADR-0095 D5, issue #93) or multi-op effects change clause syntax, this example's syntax may need a mechanical update — its *semantics* (identity dispatch) must not change.
- Reviewer should scrutinize: that `expected.txt` says `210` (the identity-dispatch value), not a value that happens to come out of the runner.
- Deferred: a same-effect nesting case where the outer cap is passed *through a function* into the inner scope (composes this plan with the #84 caps-through-functions pattern). Add it as a second example if/when plan 002's matrix work is done.
