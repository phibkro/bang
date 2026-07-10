#!/usr/bin/env bash
# runc.sh <input> <timeout-secs> — run one input on --compiled, report resolve/hang + wall secs
BANG=.lake/build/bin/bang
inp="$1"; to="${2:-60}"
scratch/calc95/gen.sh "$inp" > scratch/calc95/probe.bang
t0=$SECONDS
out=$(timeout "$to" $BANG run --compiled scratch/calc95/probe.bang 2>&1); rc=$?
dt=$((SECONDS - t0))
if [ $rc -eq 124 ]; then echo "input=[$inp] HANG (>${to}s)"; else echo "input=[$inp] resolves=[$out] rc=$rc wall=${dt}s"; fi
