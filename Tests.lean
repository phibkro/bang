/-! `lake test` driver — the Lean-ecosystem-standard test entry point.

Delegates to `tools/run-batteries.sh` (the same battery set `just verify` runs, minus its
build/audit legs). `just` remains the SSoT for orchestration (recipes, dependency chain,
gate composition — see `justfile`); this exe exists ONLY so a Lean developer's reflexive
`lake test` works without reading the justfile. Wired via `testDriver` in `lakefile.toml`. -/
def main (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd := "bash", args := #["tools/run-batteries.sh"] ++ args.toArray }
  child.wait
