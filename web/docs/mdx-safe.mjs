// Shared MDX-prose-escaping helper — the same rule sync-docs.mjs applies to
// mirrored repo markdown, reused by gen-tour.mjs for hand-authored lesson
// prose so there is exactly one place that knows what MDX's JSX/expression
// parser chokes on (never a second copy that could drift).
//
// Escape MDX's JSX/expression triggers (`<`, `{`). MDX does NOT parse JSX inside
// an inline-code span — EXCEPT a GFM table splits `code | with a pipe`, breaking
// the span and exposing a `<;>` (Lean combinator) to the parser. So: escape in
// prose always; inside a code span only when it holds a `|` (the break risk).
// Everywhere else the code span is left verbatim, so `Foo<Bar>` still displays.
const esc = (s) => s.replace(/</g, '&lt;').replace(/\{/g, '&#123;')
export function escapeProse(line) {
  return line
    .split(/(`+[^`]*`+)/) // odd indices are inline-code spans
    .map((seg, i) =>
      i % 2 === 0 ? esc(seg) : seg.includes('|') ? esc(seg) : seg,
    )
    .join('')
}
