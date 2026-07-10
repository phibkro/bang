# handle-custom-resume

A **parameter-carrying** custom handler (the `(Name init) as h` form), ported from the Stage-2
kernel's `customResume` `#guard` (`Bang/Core/Semantics/Eval.lean`) to SOURCE TEXT — the same
dispatch + one-shot resume the kernel-level test proves, now reached through the surface parser
+ elaborator + typer. `fetch(x)` resumes with `x + param` (`param` names the carried `100`);
`net.fetch(5)` resumes with `105`, and the `letC` continuation (`r + 1`) runs AFTER — the
one-shot resume, verified end to end.

```
lake exe bang run examples/handle-custom-resume/main.bang    # (5+100)+1 -> 106
```
