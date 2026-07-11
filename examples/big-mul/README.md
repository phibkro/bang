# big-mul — bignum multiply, i64-overflow from in-range operands (issue #132, bignum lane B3)

`(4*10^9) * (4*10^9) = 16000000000000000000` overflows i64 from two operands that each fit. `$mulVal`
computes `p = a*b` (wrapping), detects overflow via `p/a != b` (wasm has no `mul_high`), and spills to
a `$bigval` schoolbook multiply. This is the COMPUTED-overflow case, distinct from a big literal:
omitting the check would silently wrap here. `expected.txt` is `bang run`'s stdout.
