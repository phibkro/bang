// oracle-client.ts -- one long-lived oracle process, line in / line out.
//
// Do NOT spawn per query; that dominates runtime at thousands of cases. We
// keep a single process and a FIFO of pending resolvers.

import { spawn, ChildProcessWithoutNullStreams } from "node:child_process";
import { createInterface, Interface } from "node:readline";
import { decodeUnifyResp, type Row, type UnifyResp } from "./wire.js";
import type { Expr, RunResult } from "./ast.js";

// Outcome of the effect fragment (CalcEff): a value or a propagating effect.
export type Outcome =
  | { ok: true; outcome: "ret"; n: number }
  | { ok: true; outcome: "exc"; label: number; payload: number }
  | { ok: false; reason: string; msg?: string };

// Result of the State fragment (CalcSt): a value plus the final state.
export type StOut =
  | { ok: true; value: number; state: number }
  | { ok: false; reason: string; msg?: string };

export class Oracle {
  private proc: ChildProcessWithoutNullStreams;
  private rl: Interface;
  private pending: ((line: string) => void)[] = [];

  constructor(exePath: string) {
    this.proc = spawn(exePath, [], { stdio: ["pipe", "pipe", "inherit"] });
    this.rl = createInterface({ input: this.proc.stdout });
    this.rl.on("line", (line) => {
      const resolve = this.pending.shift();
      if (resolve) resolve(line);
    });
  }

  private send<T>(req: unknown, parse: (line: string) => T): Promise<T> {
    return new Promise<T>((resolve, reject) => {
      this.pending.push((line) => {
        try { resolve(parse(line)); } catch (e) { reject(e); }
      });
      this.proc.stdin.write(JSON.stringify(req) + "\n");
    });
  }

  unify(fresh: number, r1: Row, r2: Row): Promise<UnifyResp> {
    return this.send({ op: "unify", fresh, r1, r2 }, (line) =>
      decodeUnifyResp(JSON.parse(line)),
    );
  }

  // Drive the definitional interpreter `eval` (ADR-0008). The reply is already
  // in the RunResult shape (see Bang/EvalJson.lean); parse-don't-validate at
  // the edge so a malformed reply fails here rather than skewing a comparison.
  evalProg(fuel: number, expr: Expr): Promise<RunResult> {
    return this.send({ op: "eval", fuel, expr }, (line) => JSON.parse(line) as RunResult);
  }

  // Run the CALCULATED stack machine (compile + exec, ADR-0009) on a program.
  // Defined for arithmetic + let/var so far.
  execProg(expr: Expr): Promise<RunResult> {
    return this.send({ op: "exec", expr }, (line) => JSON.parse(line) as RunResult);
  }

  // Run the CALCULATED higher-order machine (closures, CBV, ADR-0010) on a
  // program. Adds lam/app to the above; fuel-bounded.
  execHOProg(fuel: number, expr: Expr): Promise<RunResult> {
    return this.send({ op: "execho", fuel, expr }, (line) => JSON.parse(line) as RunResult);
  }

  // Run the CALCULATED call-by-name machine (thunk/force; matches Bang.Eval).
  execCBNProg(fuel: number, expr: Expr): Promise<RunResult> {
    return this.send({ op: "execcbn", fuel, expr }, (line) => JSON.parse(line) as RunResult);
  }

  // Effect fragment (CalcEff.Src wire format): the total reference `eval` and the
  // calculated handler machine `exec`, both returning an Outcome (ret/exc).
  evalEff(expr: unknown): Promise<Outcome> {
    return this.send({ op: "evaleff", expr }, (line) => JSON.parse(line) as Outcome);
  }
  execEff(fuel: number, expr: unknown): Promise<Outcome> {
    return this.send({ op: "execeff", fuel, expr }, (line) => JSON.parse(line) as Outcome);
  }

  // State fragment (CalcSt.Src): the total reference `eval` and the calculated
  // state-register machine, both returning { value, state }.
  evalSt(expr: unknown): Promise<StOut> {
    return this.send({ op: "evalst", expr }, (line) => JSON.parse(line) as StOut);
  }
  execSt(expr: unknown): Promise<StOut> {
    return this.send({ op: "execst", expr }, (line) => JSON.parse(line) as StOut);
  }

  close(): void {
    this.rl.close();
    this.proc.stdin.end();
    this.proc.kill();
  }
}
