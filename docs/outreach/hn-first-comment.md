<!-- note-status: active -->
# HN first-comment (author convention)

> Post this as the author's own first reply, immediately after submitting — the HN
> convention that pre-empts the predictable skeptic thread. ~150 words. Preempts the
> top three skeptic-FAQ questions: production-ready? · verified-vs-tested? · why not
> Koka/Effekt/OCaml effects?
>
> Grounding: `copy-kit.md` §4 (Q1, Q4, Q3). Claims trace: `README.md`.

---

Author here. Three things I'd rather say up front than have you find out.

**"Verified" means a specific set of theorems, not a vibe.** The kernel — thunks,
effect rows, handlers, STM — is proven in Lean 4, and the headline theorems reduce to
a three-axiom trusted base the build checks on every commit. The parser, elaborator,
and the Turing-complete fragment are *tested* against that kernel, not proven. The seam
is marked in the type system. I'll tell you exactly where the proof stops, because for
a verification language that honesty is the product.

**It's v0.2, not production.** The compiler is young, multi-op user effects are still
rough, and a cold outsider scored it 8/10 with a stopwatch. Explore the ideas; don't
run payroll on it.

**Why not Koka/Effekt?** Those are excellent — use them for effects in production today.
bang isn't "another effect language"; the bet is a *verified* substrate you can prove
things about, aimed at being a target an AI can safely generate into. Happy to dig into
any of it.
