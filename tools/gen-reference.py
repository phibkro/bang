#!/usr/bin/env python3
"""Generate docs/reference/language.md — a DERIVATION of the code, never hand-maintained.

Sources of truth (the generate rung of the derivation ladder):
  • Bang/Frontend/Surface.lean — the `Surf` and `Ty` inductives. Each constructor's trailing
    `-- comment` IS the surface form, so they generate the SYNTAX + TYPES reference.
  • Bang/Examples.lean + Bang/Frontend/TypeCheck.lean — the `#guard` corpus. `runYieldsInt "src" N`
    (program ⟹ value) and `display "src" == "type"` (program : type) generate the EXAMPLES reference.
    Every example is gated by `lake build`, so a doc derived from them CANNOT drift.

Usage:  gen-reference.py            regenerate docs/reference/language.md
        gen-reference.py --check    exit 1 if the committed doc != the regenerated one (fitness leg)
"""
import re
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
SURFACE = ROOT / "Bang/Frontend/Surface.lean"
IR = ROOT / "Bang/Core/IR.lean"
EVAL = ROOT / "Bang/Core/Semantics/Eval.lean"
SOURCES = [ROOT / "Bang/Examples.lean", ROOT / "Bang/Frontend/TypeCheck.lean"]
OUT = ROOT / "docs/reference/language.md"

STR = r'"((?:[^"\\]|\\.)*)"'  # a Lean string literal (with escapes)


def first_sentence(s):
    s = re.sub(r"\s+", " ", s).strip()
    m = re.match(r"(.*?\.)(?:\s|$)", s)
    return (m.group(1) if m else s).strip()


def extract_labels(text):
    """(name, value, summary) for each `/-- … -/ def <name>Label : Label := <n>`."""
    rows = []
    for m in re.finditer(r"/--(.*?)-/\s*def\s+(\w+Label)\s*:\s*Label\s*:=\s*(\d+)", text, re.S):
        rows.append((m.group(2), m.group(3), first_sentence(m.group(1))))
    return rows


def extract_constructors(text, name):
    """(ctor, signature, comment) for `inductive <name>` (line-based; stops at the inductive's end)."""
    rows, capturing = [], False
    for line in text.splitlines():
        s = line.strip()
        if re.match(rf"inductive {name}\b", s):
            capturing = True
            continue
        if not capturing:
            continue
        if s.startswith("|"):
            cm = re.match(r"\|\s*(\w+)\s*:\s*([^-]*?)\s*(?:--\s*(.*))?$", s)
            if cm:
                rows.append((cm.group(1), cm.group(2).strip(), (cm.group(3) or "").strip()))
        elif s.startswith(("deriving", "inductive", "end", "def", "@", "abbrev")):
            break
    return rows


def extract_inductive(text, name):
    """`| ctor : sig  -- comment` rows of `inductive <name> where … deriving`."""
    m = re.search(rf"inductive {name} where\n(.*?)\n\s*deriving", text, re.S)
    if not m:
        return []
    rows = []
    for line in m.group(1).splitlines():
        cm = re.match(r"\s*\|\s*(\w+)\s*:.*?--\s*(.*)", line)
        if cm:
            # the comment is `<form>   <note>` (2+ spaces separate the form from any description)
            parts = re.split(r"\s{2,}", cm.group(2).strip(), maxsplit=1)
            form = parts[0]
            note = parts[1].strip() if len(parts) > 1 else ""
            rows.append((cm.group(1), form, note))
    return rows


def extract_op_table(text):
    """(op, leftBP, rightBP) for each `| "op" => some (lbp, rbp, …)` in `def opInfo` (ADR-0071 ①).

    The precedence table is a pure function of this reified operator table — the same table the
    Pratt loop (`pOp`) consults — so the doc cannot claim a precedence the parser doesn't have."""
    m = re.search(r"def opInfo.*?\n(.*?)\n\s*\|\s*_\s*=>\s*none", text, re.S)
    if not m:
        sys.exit("gen-reference: could not locate `def opInfo` — the precedence table is keyed off it.")
    rows = []
    for line in m.group(1).splitlines():
        cm = re.match(rf'\s*\|\s*{STR}\s*=>\s*some\s*\(\s*(\d+)\s*,\s*(\d+)\s*,', line)
        if cm:
            rows.append((cm.group(1), int(cm.group(2)), int(cm.group(3))))
    return rows


def extract_keyword_rules(text):
    """(keyword, form) for each reified `Rule` in `def keywordRule` (ADR-0071 ②).

    Renders the surface shape by walking the rule's `choices`: `.kw "x"`→`x`, `.refE`→`<expr>`,
    `.refA`→`<atom>`, `.refI`→`<ident>`, `.optAs`→`[as <ident>]` (the optional named-cap binder,
    ADR-0072). The same rules `pRuleDrive` interprets, so the grammar tracks the parser."""
    m = re.search(r"def keywordRule.*?\n(.*?)\n\s*\|\s*_\s*=>\s*none", text, re.S)
    if not m:
        sys.exit("gen-reference: could not locate `def keywordRule` — the keyword grammar is keyed off it.")
    slot = {"refE": "<expr>", "refA": "<atom>", "refI": "<ident>", "optAs": "[as <ident>]"}
    rows = []
    for cm in re.finditer(r'\|\s*"([^"]+)"\s*=>\s*some\s*⟨\[(.*?)\]\s*,', m.group(1)):
        parts = []
        for c in re.finditer(r'\.kw\s*"([^"]*)"|\.(refE|refA|refI|optAs)', cm.group(2)):
            parts.append(c.group(1) if c.group(1) is not None else slot[c.group(2)])
        rows.append((cm.group(1), " ".join(parts)))
    return rows


def extract_result_ctors(text):
    """Constructor names of `inductive Result` (the reference's observable-outcome type).

    Line-based, like extract_constructors, but Result's escapedCap carries a LEADING `--`
    block comment (not trailing), so we only need the ctor names here — the observation /
    error prose is keyed off them, and a name change in source breaks generation (fail-loud)."""
    names, capturing = [], False
    for line in text.splitlines():
        s = line.strip()
        if re.match(r"inductive Result\b", s):
            capturing = True
            continue
        if not capturing:
            continue
        if s.startswith("|"):
            cm = re.match(r"\|\s*(\w+)\s*:", s)
            if cm:
                names.append(cm.group(1))
        elif s.startswith(("deriving", "inductive", "end", "def", "@", "abbrev", "/-")):
            break
    return names


def parse_examples(path):
    """(section, comment, kind, src, result) for each runYieldsInt / display #guard."""
    lines = path.read_text().splitlines()
    section, comment, out, i = None, None, [], 0
    while i < len(lines):
        s = lines[i].strip()
        hm = re.match(r"/-!\s*#+\s*(.*)", s)
        if hm:
            section = re.sub(r"\s*-/\s*$", "", hm.group(1)).strip()
            comment = None
            i += 1
            continue
        if s.startswith("--"):
            comment = s.lstrip("-").strip()
            i += 1
            continue
        if s.startswith("#guard"):
            stmt, j = s, i + 1
            while j < len(lines):  # join continuation lines (multi-line #guards)
                nxt = lines[j].strip()
                if nxt == "" or nxt.startswith(("#guard", "/-!", "--")):
                    break
                stmt += " " + nxt
                j += 1
            mv = re.search(rf"runYieldsInt\s+\d+\s+{STR}\s+(-?\d+)", stmt)
            if mv:
                out.append((section, comment, "value", mv.group(1), mv.group(2)))
            mt = re.search(rf"display\s+{STR}\s*==\s*{STR}", stmt)
            if mt:
                out.append((section, comment, "type", mt.group(1), mt.group(2)))
            comment = None
            i = j
            continue
        if s == "":
            comment = None
        i += 1
    return out


def render():
    surf = SURFACE.read_text()
    L = []
    L.append("# BANG — language reference")
    L.append("")
    L.append("<!-- GENERATED by tools/gen-reference.py from the verified source — do not hand-edit. -->")
    L.append("<!-- Run `just reference` to regenerate; `gen-reference.py --check` gates it. -->")
    L.append("")
    L.append("Derived from the code: the surface forms are the `Surf`/`Ty` constructor comments in")
    L.append("`Bang/Frontend/Surface.lean`; every example is a `#guard` gated by `lake build`, so")
    L.append("nothing here can drift from what the language actually does.")
    L.append("")

    L.append("## Surface syntax")
    L.append("")
    L.append("| Form | Notes |")
    L.append("|---|---|")
    for _name, form, note in extract_inductive(surf, "Surf"):
        L.append(f"| `{form}` | {note} |")
    L.append("")

    L.append("## Types")
    L.append("")
    L.append("| Type | Notes |")
    L.append("|---|---|")
    for _name, form, note in extract_inductive(surf, "Ty"):
        L.append(f"| `{form}` | {note} |")
    L.append("")

    L.append("## Grammar")
    L.append("")
    L.append("GENERATED from the reified parser tables in `Bang/Frontend/Surface.lean` (ADR-0071):")
    L.append("operator precedence from `opInfo`, keyword-led constructs from `keywordRule`. The parser")
    L.append("consults these same tables, so this grammar cannot drift from what BANG actually parses.")
    L.append("")
    L.append("### Operator precedence")
    L.append("")
    L.append("Binding powers from `opInfo`, loosest first (higher BP binds tighter). Associativity is")
    L.append("read off the powers: left-assoc ⟺ leftBP < rightBP, right-assoc ⟺ leftBP > rightBP.")
    L.append("Application (juxtaposition) binds tighter than every operator below; `.`-method-perform")
    L.append("tighter still.")
    L.append("")
    L.append("| Operator | leftBP | rightBP | Associativity |")
    L.append("|---|---|---|---|")
    for op, lbp, rbp in extract_op_table(surf):
        assoc = "left" if lbp < rbp else "right" if lbp > rbp else "non"
        L.append(f"| `{op}` | {lbp} | {rbp} | {assoc} |")
    L.append("")
    L.append("### Keyword-led constructs")
    L.append("")
    L.append("Each is a reified `Rule` (`keywordRule`): a linear sequence of keyword literals and")
    L.append("sub-parses — `<expr>` a full expression, `<atom>` an atom, `<ident>` a bound name.")
    L.append("Surface constructs not (yet) reified as rules are parsed by bespoke arms; the complete")
    L.append("construct list is the Surface syntax table above.")
    L.append("")
    L.append("| Keyword | Form |")
    L.append("|---|---|")
    for kw, form in extract_keyword_rules(surf):
        L.append(f"| `{kw}` | `{form}` |")
    L.append("")

    L.append("## Effect channels")
    L.append("")
    L.append("The surface's effect labels (the frozen v1 set). A handler on a label discharges its row;")
    L.append("an undischarged label surfaces in the inferred effect (see Examples → type display).")
    L.append("")
    L.append("| Label | Value | Channel |")
    L.append("|---|---|---|")
    for name, val, summ in extract_labels(surf):
        L.append(f"| `{name}` | {val} | {summ} |")
    L.append("")

    L.append("## Kernel primitives (the IR the surface lowers to)")
    L.append("")
    L.append("The graded-CBPV kernel — `Val` (values), `Comp` (computations), `Handler` (effect handlers).")
    L.append("The surface is sugar over these; `Source.eval` (Bang/Core/IR.lean) is the reference semantics.")
    L.append("")
    ir = IR.read_text()
    for ind, heading in [("Val", "Values"), ("Comp", "Computations"), ("Handler", "Handlers")]:
        L.append(f"### {heading} (`{ind}`)")
        L.append("")
        L.append("| Primitive | Signature | Notes |")
        L.append("|---|---|---|")
        for ctor, sig, note in extract_constructors(ir, ind):
            L.append(f"| `{ctor}` | `{sig}` | {note} |")
        L.append("")

    L.append("## Examples")
    L.append("")
    L.append("Every example below is a build-verified `#guard`. `⟹` is evaluation; `:` is the inferred type.")
    L.append("")
    rows = [r for p in SOURCES for r in parse_examples(p)]
    cur = None
    for section, comment, kind, src, result in rows:
        if section != cur:
            cur = section
            L.append(f"### {section}")
            L.append("")
        arrow = "⟹" if kind == "value" else ":"
        note = f"  — {comment}" if comment else ""
        L.append(f"- `{src}` {arrow} `{result}`{note}")
    L.append("")

    # ── Spec shell (#35): programs & observation ──
    # The load-bearing derived fact is the SET of observable outcomes — the `Result`
    # constructors. The observation prose is keyed off them; a rename/add in source
    # breaks generation (fail-loud), forcing the section to be reviewed.
    result_ctors = set(extract_result_ctors(EVAL.read_text()))
    expected_result = {"done", "oom", "escapedCap", "stuck"}
    if result_ctors != expected_result:
        sys.exit(
            f"gen-reference: Result constructors {sorted(result_ctors)} != "
            f"{sorted(expected_result)} — the observation section (#35) is keyed off "
            "these; update tools/gen-reference.py to match the source."
        )

    L.append("## Programs & observation")
    L.append("")
    L.append("A **program** is a closed term of ground type — a `Comp` with no free variables whose")
    L.append("value type is a base type (`Int`/`Unit`, or a sum/product of them). The CLI entry")
    L.append("convention (`bang run` / `eval`, the `runYieldsInt` harness) accepts exactly these and")
    L.append("reports the outcome of `Source.eval` (`Bang/Core/Semantics/Eval.lean`), the reference")
    L.append("semantics.")
    L.append("")
    L.append("**Observable outcomes** are the constructors of the reference's `Result` type — nothing")
    L.append("else about a run is observable:")
    L.append("")
    L.append("| Outcome | Meaning |")
    L.append("|---|---|")
    L.append("| `done v` | terminated with value `v` — at ground type, the observed answer |")
    L.append("| `oom` | fuel exhausted — the v1 stand-in for divergence (the fuel-bounded `Div` fragment) |")
    L.append("| `escapedCap` | a capability escaped its handler — a defined fail-loud terminal (ADR-0063) |")
    L.append("| `stuck` | genuine stuck — a well-typed `⊥`-row program NEVER reaches it (`type_safety`) |")
    L.append("")
    L.append("This is the **same observation** the ◊4 contextual-equivalence work quantifies over:")
    L.append("`lr_sound` holds two programs equivalent when they agree on this outcome (convergence at")
    L.append("ground type) in every closing context. One definition, two consumers — the reference")
    L.append("runner and the equivalence LR.")
    L.append("")

    L.append("## Conformance")
    L.append("")
    L.append("A **conforming implementation** of BANG agrees with the reference semantics `Source.eval`")
    L.append("(`Bang/Core/Semantics/Eval.lean`) on the observation defined above, for every program in")
    L.append("the **normative corpus**, and diverges only where the reference diverges.")
    L.append("")
    L.append("The normative corpus is the executable conformance suite:")
    L.append("")
    L.append("- **`Bang/Examples.lean`** — the curated worked-examples corpus; every `#guard` runs the")
    L.append("  compiled kernel, so a false assertion fails `lake build`.")
    L.append("- the **verified examples rendered in this reference** (the *Examples* section above) —")
    L.append("  each a `lake build`-gated `#guard`.")
    L.append("")
    L.append("Because the oracle is mechanized and every example is build-gated, drift is a *failing")
    L.append("diff*, not a judgement call — the top rung of the single-source-of-truth ladder")
    L.append("(generate / test) applied to implementations. A third-party or AI-paved implementation is")
    L.append("checkable by running the corpus against it: invariant #1 (\"proof rides the reference;")
    L.append("anything that runs is differential-tested against `Source.eval`\") stated as a spec clause.")
    L.append("")

    L.append("## Errors & terminals")
    L.append("")
    L.append("BANG makes the choice most languages never do: **there is no undefined behavior.** Every")
    L.append("reachable failure is a *defined, fail-loud* outcome. Against the C-standard trichotomy:")
    L.append("")
    L.append("| Class | In BANG |")
    L.append("|---|---|")
    L.append("| undefined behavior | **∅** — every reachable failure is a defined terminal |")
    L.append("| unspecified behavior | **∅** — the reference semantics is deterministic |")
    L.append("| implementation-defined | the **fuel bound** only (when `oom` is reported); integer width is *not* one — `Int` is unbounded ℤ, overflow never UB (ADR-0067) |")
    L.append("")
    L.append("**Static errors** reject a term before it is a program: parse errors, type errors, and")
    L.append("effect-signature violations (an `! {ρ}` annotation that under-declares the inferred row).")
    L.append("A rejected term never runs.")
    L.append("")
    L.append("**Runtime terminals** are the fail-loud outcomes of a run — the `Result` failure")
    L.append("constructors (`Bang/Core/Semantics/Eval.lean`) plus the IR's explicit fail-loud marker")
    L.append("(`Comp.wrong`, `Bang/Core/IR.lean`):")
    L.append("")
    L.append("| Terminal | When it arises | Corpus example / definition |")
    L.append("|---|---|---|")
    L.append("| `oom` | fuel exhausted before the program returned — the v1 divergence proxy | `Config.run` fuel-0 arm (`Bang/Core/Semantics/Eval.lean`) |")
    L.append("| `escapedCap` | a first-class capability is forced after its handler has popped; dispatch finds no frame (ADR-0063) | `capEscape` `#guard` (`Bang/Examples.lean`) |")
    L.append("| `wrong s` | an explicit IR abort — e.g. `wrong \"elab-failed\"` when elaboration fails (`Bang/Frontend/NamedCore.lean`) | `Comp.wrong` (`Bang/Core/IR.lean`) |")
    L.append("")
    L.append("The fourth `Result` outcome, `stuck` (genuine stuck), is **unreachable** for a well-typed")
    L.append("`⊥`-row program — that is exactly what `type_safety` proves, and what \"no undefined")
    L.append("behavior\" means: there is no reachable failure the semantics does not name.")
    L.append("")
    L.append("`escapedCap` is *defined* for v1, not silent corruption: the kernel's global-fresh")
    L.append("capability minting guarantees an escaped cap resolves to no handler and fails loud")
    L.append("(OCaml-effects' `Effect.Unhandled`). Post-v1 it becomes **untypeable** — scoped/region")
    L.append("capability types (#21) make the escape unrepresentable rather than merely detected.")
    L.append("")

    return "\n".join(L) + "\n"


def main():
    content = render()
    if "--check" in sys.argv:
        current = OUT.read_text() if OUT.exists() else ""
        if current != content:
            print("reference: STALE — docs/reference/language.md != regenerated. Run `just reference`.")
            sys.exit(1)
        print("reference: OK — language.md ≡ the verified source.")
        return
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(content)
    n = content.count("\n- `")
    print(f"reference: wrote {OUT.relative_to(ROOT)} ({n} verified examples).")


if __name__ == "__main__":
    main()
