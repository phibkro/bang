# hostio-fs

**ADR-0104, the Fs widening (host-io-widen lane).** A program that imports the
bundled `std/Io.bang` module and performs `Fs` operations (`writeFile`, `exists`,
`readFile`) — the first bang program whose effect touches the real **filesystem**.

```
import Io
let main =
  let path = SCons(Char(103), SCons(Char(46), SCons(Char(116), SNil))) in   -- "g.t"
  let body = SCons(Char(104), SCons(Char(105), SNil)) in                    -- "hi"
  let u1 = Io.writeFile((path, body)) in
  let ex = Io.exists(path) in                                               -- 1 (present)
  let back = Io.readFile(path) in
  back
```

```
# inside a scratch dir (the file lands next to cwd):
bang run --env=real --allow=Fs examples/hostio-fs/ambient.bang    # hi
```

## Why the ambient spelling (no `with`)

Unlike `hostio-echo/main.bang` (which installs its own `with Io_Console`), this file
uses the module-qualified AMBIENT spelling `Io.writeFile`/`Io.readFile`/`Io.exists`
with no enclosing handler — so it reaches ONLY the driver's outermost grant surface
(`--env=real --allow=Fs`), exactly like `hostio-echo/ambient.bang`. Under the default
engine (no `--env`) the surface does not exist, so the first `Io.*` perform hits the
DEFINED `escapedCap` terminal (ADR-0063, exit 5). That is the shipped contract: an
ambient host perform needs a grant to resolve. This keeps the file out of the sim
corpus by construction (its name is `ambient.bang`, not `main.bang`, so
`check-examples.sh`'s `examples/*/main.bang` loop skips it) — it is exercised instead
by `tools/test-hostio-seam.sh` §7 against a fresh `mktemp` jail.

## The `writeFile((path, body))` double-paren

`writeFile : Str * Str -> Unit` takes ONE argument of PAIR type. v1 effect ops are
single-arg (ADR-0095 D3), so the checker refuses a two-arg `writeFile(path, body)`;
the argument is the pair value `(path, body)`, with the outer parens being the call.
The driver's `hostServiceReal` splits the pair back into `(path, body)` — this is the
first multi-component host payload, riding the `hostPerformS` reach (ADR-0104 §4).

## Record / replay — the conformance gate over a REAL filesystem

The heart of this slice (ADR-0104 §3, invariant #1). A real run RECORDS a Sendable
trace of each `(label, op, payload, result)`; REPLAY re-runs the SAME program on the
pure oracle, feeding the recorded results back — **with the file no longer present**:

```
bang run --env=real --allow=Fs --record trace.ndjson ambient.bang   # hi  (writes g.t)
rm g.t
bang run --replay trace.ndjson ambient.bang                          # hi  (NO real IO; g.t stays absent)
```

Byte-identical output without the file on disk ⇒ the tested-stratum host handler
conforms to the pure model. The trace's `result` fields are JSON-escaped, so a file
body containing a `"` or a newline round-trips faithfully (the un-escaped loader would
have truncated it — a silent record/replay divergence). See
`docs/decisions/0104-host-io-environment.md` §Addendum (Fs) and
`docs/notes/host-io-design.md` §1 for the full design.

## Sim mode

Under `--env=sim` there is no per-op Fs sim MAP in v1 (a stateful in-memory filesystem
wants carried-param update, ADR-0092 D5, open). The v1 determinism source for Fs is the
`--record`/`--replay` trace, not a sim map — so the ambient program above is a
`--env=real` + record/replay demonstrator, not a sim-corpus entry. A program that wants
a sim Fs installs its OWN `with Io_Fs as fs { … }` fixed-source clauses (documented in
`std/Io.bang`), exactly as `hostio-echo/main.bang` does for Console.
