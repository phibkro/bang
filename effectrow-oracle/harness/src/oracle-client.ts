// oracle-client.ts -- one long-lived oracle process, line in / line out.
//
// Do NOT spawn per query; that dominates runtime at thousands of cases. We
// keep a single process and a FIFO of pending resolvers.

import { spawn, ChildProcessWithoutNullStreams } from "node:child_process";
import { createInterface, Interface } from "node:readline";
import { decodeUnifyResp, type Row, type UnifyResp } from "./wire.js";
import type { Expr, RunResult } from "./ast.js";

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

  close(): void {
    this.rl.close();
    this.proc.stdin.end();
    this.proc.kill();
  }
}
