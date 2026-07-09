# caesar — encode/decode/round-trip cipher

Originally written by the round-1 **stranger-test** agent (docs/notes/stranger-test-1.md)
from the public docs alone — the first bang program authored by an outsider. The AUTHORED
LOGIC is preserved verbatim (`shiftCode`/`caesar`/`encode`/`decode`/`roundtrips`/`bitStr` and
`main`'s computation are unchanged); the file's SHAPE was rewritten flat (top-level `let`/
`let rec` decls, ADR-0093 D5) once the module system landed, replacing the original single
`let ... in` nesting pyramid — same program, same `expected.txt`, easier to read top-to-bottom.
Line comments (issue #62) now carry this attribution inline in `main.bang` itself, closing the
dogfood finding that used to justify keeping it only here.

Exercises: `Str`/`Char` matching, nested `Char(n)` match, single- and multi-arg recursion,
thunks, `Left`/`Right` sums, arithmetic modular wrap, `concat`. Shifts assume `k ∈ 0..25`
(the author's own shipping note).
