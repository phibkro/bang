---
type: design-question
title: "Surface concrete-syntax discipline: canonical (formatter-normalized) vs lenient"
description: "whitespace-insensitive grammar + a canonical formatter (the Go/Rust model)"
status: open
area: surface
ties: ["ADR-0066"]
see-also: ["#30", "#111"]
---
**Question**: should the surface have ONE canonical textual form (a formatter normalizes to it, gofmt/rustfmt
style) or a lenient grammar that tolerates whitespace/style variation? And — the orthogonal axis — should
the grammar be whitespace-*insensitive*?

**Why it matters**: it sets the human↔agent ergonomics trade. Inference + loose input is nice for humans;
a single canonical, explicit form is nice for agents, diffs, and CI (less ambiguity, stable blame). The
two concerns (type-annotation optionality, text-format canonicality) are SEPARATE axes and shouldn't be
conflated — bidirectional typing already answers the first (optional, mandatory exactly where synthesis is
stuck; ADR-0066).

**Detail**: the current surface is the worst quadrant on the format axis — whitespace-*sensitive* (operators
are space-delimited: `a + b` parses, `a+b` does not — `Bang/Frontend/Surface.lean` tokenizer) AND non-canonical.
The modern answer (Go, Rust, Elm) is **both**: a whitespace-insensitive grammar PLUS a canonical formatter.
Humans write loose; the formatter normalizes to one true form; agents/diffs/CI see only canonical text. This
is the same single-source-of-truth move as everywhere else (the formatter GENERATES the canonical form).

**Options**: (1) **whitespace-insensitive grammar + canonical formatter** (recommended — Go/Rust model; serves
human, agent, machine at once); (2) lenient/whitespace-tolerant but no canonical form (compiles despite style
drift — but diffs/agents see noise); (3) status quo (whitespace-sensitive operators — the trap; fix via #30).

**Recommended**: (1). Precondition is the Pratt parser (#30) which removes the space-delimited-operator hack →
whitespace-insensitive; a `bang fmt` canonical formatter is then pure gravy (and pairs with the tree-sitter
grammar, #111).

**Blocked on**: nothing hard; sequencing — do the Pratt parser (#30) first, then the formatter. Liquid until
the surface stabilizes past the toy parser.

**Revisit signal**: building the Pratt parser (#30), or the first `bang fmt` / formatter; or agent-ergonomics
friction from non-canonical diffs.
