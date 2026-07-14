// Tour lesson CONTENT only. Page identity, title, route, order, prerequisites,
// and navigation live in page-manifest.json; this module owns prose, teaching
// metadata, and canonical example seeds. gen-tour.mjs requires a bijection
// between these content keys and the manifest's tour-lesson pages.
export const lessonContent = [
  {
    key: 'values-and-force',
    teaches: 'description-vs-value, `$` (ADR-0007)',
    seeds: ['effect-op-arith'],
    prose: `
Every value in bang is a **thunk** — a description of a computation, not the
computation run. Writing \`a\` never runs anything; only \`$a\` (**force**) runs
it to a value.

This program allocates a TVar, writes \`read a - 30\` into it, then reads it
back — inside an \`atomically\` block so the read/write pair is one
transaction. Notice \`read a - 30\` parses as \`(read a) - 30\`: effect
operations parse at application precedence, so they compose with arithmetic
the way you'd expect from reading it left to right.
`,
  },
  {
    key: 'functions-and-recursion',
    teaches: 'a generic `let rec` over your own data, no trait bound',
    seeds: ['list-basics'],
    prose: `
Functions are ordinary thunks bound with \`let\`; recursive functions use
\`let rec\`. This program declares its own \`List a\` and a recursive
\`length\`, then calls the prelude's \`take\`/\`drop\` — both are generic over
the element type with **no trait bound at all**: the compiler discovers each
call site's concrete instantiation from its type annotation and monomorphizes
it, so nothing polymorphic ever reaches the kernel.
`,
  },
  {
    key: 'your-own-data',
    teaches: '`data`, constructors, pattern match, `deriving`',
    seeds: ['derive-eq-ord'],
    prose: `
Declare your own algebraic data type with \`data\`, and get structural
equality/ordering for free with \`deriving (Eq, Ord)\` — no hand-written
\`trait\`/\`impl\` pair needed. \`==\` and \`<\` on a derived type dispatch through
the generated implementation exactly like a hand-written one, usable
directly inside an ordinary \`match\`.
`,
  },
  {
    key: 'match-and-mutual-recursion',
    teaches: 'the `_` wildcard arm, `let rec … and …` mutual recursion',
    seeds: ['wildcard-match', 'mutual-parity'],
    prose: `
A \`match\` normally needs one arm per constructor. The \`_\` wildcard arm
names ONE shared body for every constructor you didn't spell out — the
elaborator expands it into the missing arms before the kernel ever sees it,
so it's sugar, not a new primitive.

Functions can also recurse **mutually**: \`let rec f = … and g = …\` lets two
(or more) functions call each other with neither needing to be defined
first. Below, \`even\`/\`odd\` hand off to each other, and a three-way group
(\`cycleA\`/\`cycleB\`/\`cycleC\`) confirms the same construct scales past a pair.
`,
  },
  {
    key: 'state-as-a-library',
    teaches: 'State is a handler, not a keyword',
    seeds: ['state'],
    prose: `
There is no mutable-variable keyword in bang. \`state 0 in …\` installs a
**handler** that interprets \`get\`/\`put\` as reads/writes against a seeded
value — mutability is ordinary library code over the same effect-and-handler
mechanism every other effect in this tour uses (kernel invariant: the only
privileged primitive is STM, and even that ships as a handler in v1).
`,
  },
  {
    key: 'handling-an-effect',
    teaches: '`with`, catching `raise`',
    seeds: ['handle'],
    prose: `
\`raise\` performs bang's built-in error effect; \`handle\` catches it and
returns the raised value directly, short-circuiting whatever computation
came after the \`raise\`. This is the same \`handle\`/\`with\` shape you'll use
for effects you declare yourself, next.
`,
  },
  {
    key: 'declare-your-own-effect',
    teaches: '`effect` decl, `perform`, handle end-to-end',
    seeds: ['handle-custom-tracer'],
    prose: `
Effects aren't limited to the built-ins. \`effect Net { fetch : Int -> Int }\`
declares a new effect with one operation; \`with Net as net { fetch(n) => … }\`
installs a handler for it, naming a **capability** (\`net\`) that the program
uses to perform \`fetch\` calls. This is the moat feature: user-defined
effects, not just user-defined data.
`,
  },
  {
    key: 'swap-the-handler',
    teaches: 'the same program under two different handlers',
    seeds: ['logger-silent', 'logger-counting'],
    prose: `
Because a handler is just a value installed at a \`with\` site, the **same
program** runs differently depending only on which handler you swap in.
Both programs below perform the identical three \`log\` calls; only the
handler's \`log\` clause differs — one discards, one counts. This is the
cartridge-swap moment: a runtime is a value you choose, not a fixed part of
the language.
`,
  },
  {
    key: 'identity-dispatch',
    teaches: 'why nesting the same effect twice does NOT pick the nearest handler',
    seeds: ['handle-custom-nested'],
    prose: `
Nest two handlers for the same effect, and give the program capabilities
named after each (\`inner\`, \`outer\`). A capability dispatches to the handler
it was **lexically bound to**, not to whichever handler is nearest at
runtime — \`inner.fetch\` always reaches the inner handler even from inside
the outer one's scope. This is identity-keyed dispatch: the capability
carries which specific handler instance it names, not just an effect label.
`,
  },
  {
    key: 'generation-as-an-effect',
    teaches: 'seeded, replayable nondeterminism — the DST warm-up',
    seeds: ['gen-seed-a', 'gen-seed-b'],
    prose: `
Nondeterminism is an effect too — \`Choice\` performs a \`pick\`, and the
handler decides what "random" means. Give it a constant-returning handler
and reruns are byte-identical; that determinism-by-construction is what
makes seeded simulation testing possible: swap the handler for a scheduler
policy, replay the same driver, and every run is reproducible. (The full
picture — a driver replayed under different delivery-order policies —
lives in \`examples/dst-rounds-const/\`, the tour's parting pointer past v0.)
`,
  },
]
