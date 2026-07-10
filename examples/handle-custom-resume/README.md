# handle-custom-resume

A **parameter-carrying** custom handler (the `(Name init) as h` form), ported from the Stage-2
kernel's `customResume` `#guard` (`Bang/Core/Semantics/Eval.lean`) to SOURCE TEXT — the same
dispatch + one-shot resume the kernel-level test proves, now reached through the surface parser
+ elaborator + typer. The clause body writes the literal `100` directly (`fetch(x) => x + 100`):
v1 has NO surface binder for the carried param — the `(Reader 100)` init is threaded internally
but is not yet nameable from a clause (the named next slice, ADR-0095 D1b). `net.fetch(5)`
resumes with `105`, and the `letC` continuation (`r + 1`) runs AFTER — the one-shot resume,
verified end to end.

```
lake exe bang run examples/handle-custom-resume/main.bang    # (5+100)+1 -> 106
```
