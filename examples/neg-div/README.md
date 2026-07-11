# neg-div — Euclidean division regression (issue #132)

The kernel's `/` is `Int.ediv` (Euclidean: the remainder is always non-negative), so
`(0 - 7) / 2 = -4`. wasm's raw `i64.div_s` is truncated-toward-zero and would give `-3`.

Before the B0 fix (`docs/notes/emission-bignum-design.md` Finding A) the compiled/WasmGC path
emitted a bare `div_s` and returned `-3` — compiled ≠ oracle, a latent soundness gap that never
fired because no other corpus program divides with a negative operand. This example gates that the
emitted division sequence is Euclidean on both the inline and the GC path.

`expected.txt` is `bang run`'s stdout (`-4`).
