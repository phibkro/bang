# handle-custom-resume

A **parameter-carrying** custom handler (the `(Name init) as h` form), ported from the Stage-2
kernel's `customResume` `#guard` (`Bang/Core/Semantics/Eval.lean`) to SOURCE TEXT — the same
dispatch + one-shot resume the kernel-level test proves, now reached through the surface parser
+ elaborator + typer. The clause body reads the carried param via the reserved identifier
`param` (`fetch(x) => x + param`, ADR-0095 D1's own worked example, landed #87): the `(Reader
100)` init is threaded internally AND nameable from a clause. `net.fetch(5)` resumes with `105`
(`5 + param` where `param = 100`), and the `letC` continuation (`r + 1`) runs AFTER — the
one-shot resume, verified end to end.

```
lake exe bang run examples/handle-custom-resume/main.bang    # (5+100)+1 -> 106
```
