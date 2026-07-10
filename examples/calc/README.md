# calc

An **arithmetic calculator written in bang, split across SIX files**
(`Ast.bang` / `Lexer.bang` / `Parser.bang` / `Eval.bang` / `Print.bang` /
`main.bang`) — the LARGEST bang program in the corpus (~300 lines, 6 modules),
dogfooding the full lexer → parser → evaluator pipeline plus a user effect used
structurally. Written for the N5 dogfood lane; friction log in
`docs/notes/dogfood-calc-findings.md`.

## What it computes

A fixed battery of arithmetic expressions, evaluated deterministically and
combined into one pinned integer (`expected.txt` = `11021193`). The grammar is
real, not a toy:

```
expr   = term (('+' | '-') term)*        left-assoc, lowest precedence
term   = factor (('*' | '/') factor)*    left-assoc, higher precedence
factor = '-' factor | number | ident | '(' expr ')'
```

- **precedence + associativity**: `2 + 3 * 4` = 14, `(2 + 3) * 4` = 20.
- **parentheses** (re-entrant into the outer `parseExpr` knot).
- **unary minus**: `0 - 7 + 10`, `-` as a prefix in `factor`.
- **integer division** (guarded: `/0` yields 0, not a crash).
- **variables** via an environment: `x * y + 1` with `x=10, y=3` → 31.

## The split

- **`Ast.bang`** — `pub data Tok` (the token type), `pub data TokList` (the
  token stream, a `data`-threaded linked list — bang strings are `List Char`
  but tokens are not chars), `pub data Expr` (the AST, one self-recursive
  `data`), and `pub data Env` (the variable environment, `EnvCons(Str, (Int *
  Env))` — a 2-arg ctor whose second slot is a *product*, because v1 caps
  constructor arity at ≤ 2).
- **`Lexer.bang`** — `import Ast`; `pub let rec lex : Str -> Ast_TokList !
  {Div}`, chars → tokens. Digit-runs and identifier-runs are scanned by nested
  `let rec`s (`scanNum`/`scanId`) closing over the outer `lex` knot.
- **`Parser.bang`** — `import Ast`; `pub let rec parseExpr`, recursive descent.
  The four grammar levels (`parseFactor` / `termLoop` / `parseTerm` /
  `exprLoop`) are SIBLING nested `let rec`s inside `parseExpr`'s body (bang has
  no mutual `let rec`), ordered so each references only earlier siblings + the
  outer `parseExpr` knot.
- **`Eval.bang`** — `import Ast`; declares `pub effect Trace { log : Int ->
  Int }` and `pub let rec eval : Cap Eval_Trace -> Ast_Env -> Ast_Expr -> Int !
  {Div, Eval_Trace}`. A SECOND traversal, `countSteps`, sums `tr.log(1)` per
  node — the SAME tree, two handlers: `log(x) => 0` (silent, pure value) vs
  `log(x) => 1` (counting, node total). This is the structural per-stage story:
  the effect is woven into the traversal, and the handler at `main` decides
  whether it fires.
- **`Print.bang`** — `import Ast`; `pub let rec show : Ast_Expr -> Str !
  {Div}`, the AST → fully-parenthesized canonical string (the second, independent
  consumer of `Ast` — the "one type, two consumers" module shape). `main`'s
  `roundTrips` check confirms `eval(parse(src)) == eval(parse(show(parse(src))))`.
- **`main.bang`** — `import`s all five; a `let main = …` that runs the battery
  through `$(Parser.parseAll)`/`$(Eval.eval)`/`$(Print.show)` (the `$(Mod.op)
  arg` calling convention — `$Mod.op arg` does NOT parse the way you'd expect,
  since `$` forces only an ATOM).

## Known walls (see the findings note)

- **`bang run --compiled` (the CalcVM engine) HANGS** on the parser's re-entrant
  outer-knot calls (`+`/`-`/parens), while `bang run` (env engine, the gate) and
  `--engine=ck` both return `11021193`. `check-examples` uses the env engine, so
  the gate is green; the compiled-engine divergence is a finding, not a fix.
- **`bang fmt` is NOT semantics-preserving** on `$(Mod.op) arg`: it rewrites to
  `$Mod.op arg`, which re-parses as `($Mod).op arg` and breaks; and it oscillates
  on `$Mod.op (arg)` spacing, so `fmt(fmt) != fmt` (the `test-fmt` gate). Worked
  around by flattening every cross-module call to take a BARE-identifier argument
  (`let toks = $(Lexer.lex) src in let ast = $(Parser.parseAll) toks`), which is
  fmt-idempotent while the correct `$(Mod.op)` source is what `check-examples`
  runs. Also: `use Mod (f)` won't hoist a `pub let rec`, so it was not an
  alternative for the recursive module functions.
