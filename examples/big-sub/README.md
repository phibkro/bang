# big-sub — bignum subtraction crossing back to i64 range (issue #132, bignum lane B2)

`100000000000000000000 - 99999999999999999998 = 2`. Exercises sign-magnitude `subMag` on `$bigval`
operands, then `$normBig` demotes the small result back to a plain `$ival` — the value round-trips as
`2`. `expected.txt` is `bang run`'s stdout.
