# thunk-force

The smallest description/observation example used by the contributor quickstart.
The braced expression creates a deferred computation; `$c` forces it. Parentheses
only group—they do not force. The expected result lives in the checked
[`expected.txt`](expected.txt), not in this prose.

```bash
lake exe bang run examples/thunk-force/main.bang
cat examples/thunk-force/expected.txt
```
