// wire.ts -- Effect Schema definitions for the oracle protocol.
//
// Both sides serialise identically. Labels are interned to ints at this
// boundary (matching the F* `nat`). Keeping the wire types in Schema means
// parse-don't-validate at the process edge: a malformed oracle reply fails
// loudly here rather than corrupting a comparison.

import { Schema as S } from "effect";

export const Row = S.Struct({
  labels: S.Array(S.Number),
  tail: S.NullOr(S.Number),
});
export type Row = S.Schema.Type<typeof Row>;

export const Binding = S.Tuple(S.Number, Row);
export const Subst = S.Array(Binding);

export const UnifyResp = S.Union(
  S.Struct({ ok: S.Literal(true), subst: Subst }),
  S.Struct({ ok: S.Literal(false) }),
);
export type UnifyResp = S.Schema.Type<typeof UnifyResp>;

export const decodeUnifyResp = S.decodeUnknownSync(UnifyResp);
