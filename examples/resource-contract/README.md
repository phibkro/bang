# Resource contract

This example is the first vertical slice of BANG as a language of semantic descriptions.
`Permit` declares an operation and a law; `Identity` and `Negate` are alternative realizations.
The entry program then declares two local resource obligations:

- `use [1] permit` requires the installed capability to be consumed exactly once.
- `use [0] ghost` proves the value is unused. The assertion erases before lowering, and the Wasm
  backend evaluates the binding expression but omits its dead environment cell.

```sh
.lake/build/bin/bang check examples/resource-contract/main.bang
.lake/build/bin/bang run examples/resource-contract/main.bang
.lake/build/bin/bang test examples/resource-contract/Permit.bang
.lake/build/bin/bang query contract examples/resource-contract/main.bang
.lake/build/bin/bang emit examples/resource-contract/main.bang -o /tmp/resource-contract.wat
```

Run these from the repository root after the normal `nix develop` and build/bootstrap step. Using
the already-built binary keeps repeated example runs focused on their result instead of replaying
Lake's repository-wide warning backlog.

The program prints `7`; both handler realizations satisfy `preserves_zero`. The contract query
returns contracts, realizations, quantities, laws, and compiler evidence in one JSON document.
Its `ok` field reports query execution; consumers use `subjectValid` for program validity and the
`id` fields for stable joins across realization selection.
The refusal fixtures in `scratch/resource-contract/` pin duplicate and forgotten permit errors.
