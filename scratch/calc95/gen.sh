#!/usr/bin/env bash
# gen.sh <INPUT-STRING> — emit a minimal calc entry that runs $calc on ONE input.
set -euo pipefail
INPUT="$1"
cat <<BANG
import Ast
import Lexer
import Parser
import Eval
let baseEnv = {Ast.EnvCons("x", (10, Ast.EnvCons("y", (3, Ast.EnvNil))))}
let calc = {fun src =>
    let toks = \$(Lexer.lex) src
      in
    let ast = \$(Parser.parseAll) toks
      in
    handle ((\$(Eval.eval)) tr \$baseEnv ast) with Eval_Trace as tr { log(x) => 0 }}
let main = \$calc "${INPUT}"
BANG
