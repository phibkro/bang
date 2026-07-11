#!/usr/bin/env python3
# tool: role=gen couples=Bang/Frontend/Surface.lean,docs/reference/language.md runs-in=fitness
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
DIAGCODES = ROOT / "Bang/Frontend/DiagCodes.lean"
IR = ROOT / "Bang/Core/IR.lean"
EVAL = ROOT / "Bang/Core/Semantics/Eval.lean"
TYPECHECK = ROOT / "Bang/Frontend/TypeCheck.lean"
PRELUDE = ROOT / "Prelude.bang"
SOURCES = [ROOT / "Bang/Examples.lean", TYPECHECK]
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


def extract_diag_codes(text):
    """(code, summary, has_example) for each `DiagEntry` in `def registry` (DiagCodes.lean, plan 013 s5).

    The registry is the SINGLE SOURCE OF TRUTH for diagnostic codes; this derives the reference's
    codes section from it (drift unrepresentable). Each entry is a `{ code := "B0xx" … summary := "…"
    … example? := (some "…"|none) }` record. `summary` is a single string literal; `example?` presence
    is `some` vs `none`."""
    m = re.search(r"def registry\s*:\s*List DiagEntry\s*:=\s*\[(.*?)\n\]", text, re.S)
    if not m:
        sys.exit("gen-reference: could not locate `def registry` — the diagnostic-codes section is keyed off it.")
    body = m.group(1)
    rows = []
    # split on the record openers; each entry starts `{ code := "…"`.
    for em in re.finditer(r"\{\s*code\s*:=\s*" + STR, body):
        start = em.start()
        # the entry spans from this `{` to the matching top-level `}` — find it by brace-matching,
        # ignoring braces inside string literals.
        depth, i, in_str, esc = 0, start, False, False
        while i < len(body):
            c = body[i]
            if in_str:
                if esc:
                    esc = False
                elif c == "\\":
                    esc = True
                elif c == '"':
                    in_str = False
            else:
                if c == '"':
                    in_str = True
                elif c == "{":
                    depth += 1
                elif c == "}":
                    depth -= 1
                    if depth == 0:
                        break
            i += 1
        entry = body[start:i + 1]
        code = em.group(1)
        sm = re.search(r"summary\s*:=\s*" + STR, entry)
        summary = sm.group(1) if sm else ""
        has_example = re.search(r"example\?\s*:=\s*some", entry) is not None
        rows.append((code, summary, has_example))
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


# The 3 STRING-STDLIB names (concat/reverse/eq) vs the GENERIC-PRELUDE remainder -- Prelude.bang
# carries NO section markers (it is comment-free, matching the examples/*.bang convention: `bang
# fmt` strips `--` comments, so a commented module permanently fails `bang lint`'s
# `fmt-divergence` check), so the split is this fixed NAME set instead of a text boundary.
STDLIB_NAMES = {"concat", "reverse", "eq"}


def extract_prelude_decl_names(prelude_text):
    """Every `pub let[ rec] NAME` decl name in `Prelude.bang`, in SOURCE ORDER -- the name/order
    SSoT (ADR-0097: the module itself, not a Lean string bucket)."""
    names = re.findall(r"^pub let(?: rec)? (\w+)", prelude_text, re.M)
    if not names:
        sys.exit("gen-reference: no `pub let` entries found in Prelude.bang.")
    return names


def extract_prelude_sigs(typecheck_text):
    """(name -> sig) from `TypeCheck.lean`'s `preludeSigs` table -- the DESCRIPTIVE signature SSoT
    (ADR-0097 sec preludeSigs): bang's surface has no generic function-type ascription (`pub let
    mapOption : (a -> b) -> ... = ...` rejects -- generics elaborate to MONO, ADR-0075/0079), so a
    generic entry's signature cannot live as checked syntax IN `Prelude.bang` the way `concat :
    Str -> Str -> Str` does; `preludeSigs` is the one hand-maintained escape hatch, kept honest by
    the corpus `#guard`s that exercise every entry against these exact shapes."""
    m = re.search(r"def preludeSigs\b.*?:=\s*\n\s*\[(.*?)\]\s*\n", typecheck_text, re.S)
    if not m:
        sys.exit("gen-reference: could not locate `def preludeSigs` -- the stdlib/generic-prelude sections are keyed off it.")
    sigs = {}
    for nm, sig in re.findall(r'\(\s*"(\w+)"\s*,\s*"([^"]*)"\s*\)', m.group(1)):
        sigs[nm] = sig
    if not sigs:
        sys.exit("gen-reference: `preludeSigs` parsed to no entries -- the head-literal shape changed.")
    return sigs


def extract_stdlib(prelude_text, sigs):
    """(name, sig) for the 3 STRING STDLIB entries (concat/reverse/eq), in `Prelude.bang`'s OWN
    declared order -- `reverse` has no signature (an accumulator fold; true in the retired string
    bucket too, not new here)."""
    return [(n, sigs.get(n)) for n in extract_prelude_decl_names(prelude_text) if n in STDLIB_NAMES]


def extract_generic_prelude(prelude_text, sigs):
    """(name, sig) for every OTHER `Prelude.bang` entry (mapOption, the isos, the #105 first
    slice, the char kit), in `Prelude.bang`'s OWN declared order."""
    return [(n, sigs.get(n)) for n in extract_prelude_decl_names(prelude_text) if n not in STDLIB_NAMES]


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
            # `runYieldsInt` (untyped `parse >>= lower` pipeline) and `runTypedYieldsInt` (the
            # TypeCheck.lean pipeline, string-prelude-injected — needed for any Str/Char example)
            # are the SAME (fuel, src, expected) shape over two different pipelines; either is a
            # "value" example.
            mv = re.search(rf"run(?:Typed)?YieldsInt\s+\d+\s+{STR}\s+(-?\d+)", stmt)
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
    diagcodes = DIAGCODES.read_text()
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

    if "def pLetBindings" not in surf:
        sys.exit(
            "gen-reference: `pLetBindings` not found in Surface.lean — the `let` note below is "
            "keyed off it (issue #68)."
        )
    L.append("`let` is NOT in the table above (issue #68): its multi-binding sugar needs a")
    L.append("repeated-group grammar the fixed linear `Rule`/`Choice` shape can't express, so —")
    L.append("like `let (a,b) = …`, `let rec`, `match`, `do` — it is a bespoke `pExpr` arm instead.")
    L.append("`let x = e1; y = e2; … in body` binds SEQUENTIALLY (a later binding sees every")
    L.append("earlier one; an earlier binding can never see a later one). **Contrast with Haskell's")
    L.append("`let`-block**, which is mutually recursive: bang's plain `let` stays non-recursive by")
    L.append("convention (`let rec` is the only recursion marker, and it has no multi-binding form),")
    L.append("so sequential-not-recursive is the reading consistent with the rest of the surface.")
    L.append("Semantically it ELABORATES to the IDENTICAL nested chain a hand-written")
    L.append("`let x = e1 in let y = e2 in … in body` already produces (a thin `.lettMulti` SUGAR")
    L.append("MARKER, erased before typing/lowering ever run — zero new semantics).")
    L.append("")
    L.append("**`bang fmt`'s CANONICAL FORM is a single multi-binding block** (issue #71, operator")
    L.append("ruling 2026-07-10): every MAXIMAL RUN of sequential `let`-bindings prints as ONE")
    L.append("`let x = e1; y = e2; … in body` — a hand-written nested chain COLLAPSES into this")
    L.append("form exactly like a sugar-parsed one does (a single binding still prints plain")
    L.append("`let x = e in body`, no trailing `;`). The collapse is exactly semantics-preserving,")
    L.append("including when a later binding SHADOWS an earlier one's name (`let x = 1 in let x =")
    L.append("x + 1 in x` collapses to `let x = 1; x = x + 1 in x` — verified, not assumed: the")
    L.append("grammar imposes no duplicate-name restriction, and sequential scoping through the")
    L.append("`;`-chain matches the nested chain's binder-shadowing exactly).")
    L.append("")

    if '"-\' :: \'-\' :: rest' not in surf and "'-' :: '-' :: rest" not in surf:
        sys.exit(
            "gen-reference: `tokenize`'s `--` line-comment arm not found in Surface.lean — "
            "the Lexical notes section below is keyed off it (issue #62)."
        )
    L.append("### Lexical notes")
    L.append("")
    L.append("**Line comments**: `--` runs to end-of-line (or end-of-input) and is dropped by the")
    L.append("lexer — no token, no source span (issue #62). `--` wins maximal munch over the")
    L.append("single-char `-` and the `->` arrow, so a comment can follow either without escaping.")
    L.append("Comments are **stripped before parsing**, so they carry no meaning to check/run and are")
    L.append("**not preserved by `bang fmt`** — a formatted file drops any comments in its input. There")
    L.append("is no block-comment form.")
    L.append("")

    if 'f + 1, "-" :: ts => do' not in surf:
        sys.exit(
            "gen-reference: the unary-minus `pAtom` arm not found in Surface.lean — the "
            "Lexical notes section below is keyed off it (issue #64)."
        )
    L.append("**Unary minus**: `-e` desugars to `0 - e` (the same binary-`-` AST node — no new")
    L.append("surface constructor), binding to ONE atom — tighter than every binary operator, so")
    L.append("`-x + 1` reads as `(-x) + 1` and `-x * y` as `(-x) * y`, matching mainstream convention.")
    L.append("A bare (unparenthesized) application argument goes to the BINARY reading instead: `f -1`")
    L.append("parses as `f - 1`, not `f` applied to `-1` — parenthesize for the unary reading (`f (-1)`)")
    L.append("the same disambiguation every language with juxtaposition-application + infix `-` makes.")
    L.append("**Interacts with line comments**: `--` wins maximal munch over two `-` tokens, so `3--10`")
    L.append("is `3` followed by a DROPPED line comment (`--10`), not `3 - (-10)` — write `3 - -10` or")
    L.append("`3-(-10)` (a space or parens before the second `-`) to get subtraction of a negative.")
    L.append("")

    if "def pHeader" not in surf or "def pUse" not in surf:
        sys.exit(
            "gen-reference: `pHeader`/`pUse` not found in Surface.lean — the Modules section "
            "below is keyed off them (issue #76)."
        )
    L.append("## Modules (ADR-0093)")
    L.append("")
    L.append("A **module is a file** — `import Foo` resolves `Foo.bang` (same directory, then the")
    L.append("project root; a miss is a loud error naming both probed paths). No module header, no")
    L.append("`module { … }` block — the module's name IS its filename stem.")
    L.append("")
    L.append("**The header comes first.** `import`/`use` lines form the file's HEADER and must appear")
    L.append("before any `let`/`data`/`trait`/`fn` decl — a `use`/`import` after the first decl is a")
    L.append("parse error (`unexpected 'use'/'import' where an atom was expected`). Any number of")
    L.append("`import`/`use` lines compose, in any order, within the header.")
    L.append("")
    L.append("| Form | Effect |")
    L.append("|---|---|")
    L.append("| `import Foo` | brings `Foo` into scope as a QUALIFIER prefix only — `Foo.name` — no name is hoisted unqualified |")
    L.append("| `use Foo (a, b, C)` | hoists exactly the NAMED decls of `Foo` into unqualified scope — `a`/`b`/`C` are then written bare, like any local `let`. The parens + comma-separated list are REQUIRED (`use Foo a` — no parens — is a parse error) |")
    L.append("| `pub let x = …` / `pub data T = …` / `pub fn …` / `pub trait …` | exports the decl; a bare (non-`pub`) decl is module-PRIVATE by convention (ADR-0093 D3) — only a `pub` decl is nameable via qualified access or `use` |")
    L.append("")
    L.append("**Qualified access — the `$(mod.op) arg` convention.** A qualified reference to an")
    L.append("imported (not `use`d) function must be FORCED as a PARENTHESIZED group, not a bare dotted")
    L.append("atom: `$(Foo.op) arg`, never `$Foo.op arg` — `$` forces exactly one ATOM, and `Foo.op` is")
    L.append("not itself an atom, so `$Foo.op arg` parses as `($Foo).op` (forcing `Foo` alone, then")
    L.append("projecting `.op` off the result) — almost never what's intended. The same rule applies to")
    L.append("any qualified call, including inside `let`/`match`; a `use`-hoisted name needs no such")
    L.append("wrapping (`use Foo (op)` then a bare `$op arg`, exactly like a local binding).")
    L.append("")
    L.append("**The `Mod_Type` hand-qualification convention.** A qualified TYPE name has no dot syntax")
    L.append("(`pTy` parses no `Foo.T`) — an imported `data` type must be spelled by hand as")
    L.append("`Foo_T` (the module resolver's own qualification scheme, `Mod` `_` `Name`) wherever a bare")
    L.append("type name is needed, e.g. a `match (v : Foo_T) { … }` ascription or a function's declared")
    L.append("parameter type. `use Foo (T)` avoids this — it hoists `T` (and its constructors) fully")
    L.append("unqualified, so the plain name `T` is written and matched on directly.")
    L.append("")
    L.append("**Known v1 limitation (visibility enforcement, tracked as issue #73):** `pub`/private-by-")
    L.append("default is the DESIGNED semantics above (ADR-0093 D3), but enforcement is not yet wired —")
    L.append("today a non-`pub` decl is still importable. Treat `pub` as the interface you are")
    L.append("declaring, not (yet) a gate the checker enforces.")
    L.append("")
    L.append("See `examples/json/` for a worked four-file module program (`Json.bang`/`Parse.bang`/")
    L.append("`Print.bang`/`main.bang`) exercising `import`, qualified access, and `Mod_Type` ascriptions")
    L.append("end-to-end, gated by `check-examples`.")
    L.append("")

    if "def pTraitMembers" not in surf or "def pImplMembers" not in surf:
        sys.exit(
            "gen-reference: `pTraitMembers`/`pImplMembers` not found in Surface.lean — the "
            "Traits & Laws section below is keyed off them (issue #76)."
        )
    L.append("## Traits & Laws (ADR-0040 §5, ADR-0068)")
    L.append("")
    L.append("A **trait** declares a Self-typed interface: zero or more operation SIGNATURES (`fn`) and")
    L.append("zero or more LAWS (`law`) the implementations are expected to satisfy. An **impl**")
    L.append("provides the operation bodies for one STRUCTURAL target type. Member separators (`;` or")
    L.append("`,`) are optional — the leading keyword (`fn`/`law`/`}`) alone delimits each member.")
    L.append("")
    L.append("```")
    L.append("trait Add { fn add(a, b) -> Int ; law comm(a, b): add a b == add b a }")
    L.append("impl Add for (Int * Int) { fn add(p, q) = p }")
    L.append("```")
    L.append("")
    L.append("| Form | Meaning |")
    L.append("|---|---|")
    L.append("| `trait Name { fn op(a, b) -> T }` | declares operation `op`, arity 2, every param typed `Self` (bite-2: v1 traits are Self-only — `[]` HK params) |")
    L.append("| `trait Name { law lawName(a, b): expr }` | declares a LAW: `expr` is a Bool-valued equation over the params + trait ops (e.g. `add a b == add b a`), universally quantified over `a, b` |")
    L.append("| `impl Name for Ty { fn op(a, b) = expr }` | supplies `op`'s body for the STRUCTURAL type `Ty` (a `pTy`, e.g. `Int`, `(Int * Int)`) |")
    L.append("")
    L.append("**A law body calls a trait op in PAREN-CALL form** (`add a b == add b a`, note the")
    L.append("`add a b`, ordinary curried application) — this is consistent with the rest of the")
    L.append("surface's curried convention (`f x y`, not `f(x, y)`). An `impl`'s operation DEFINITION,")
    L.append("however, uses a TUPLE-STYLE parameter list at both the trait declaration site")
    L.append("(`fn add(a, b) -> Int`) and the impl site (`fn add(p, q) = p`) — the parenthesized,")
    L.append("comma-separated form, not curried `fn add a b`. This is a deliberate but visible")
    L.append("asymmetry: trait/impl SIGNATURES use the paren-list form, law BODIES and ordinary")
    L.append("function calls elsewhere use curried application.")
    L.append("")
    L.append("`bang test [<file.bang>]` (issue #60) discovers every trait-law instance in a decls-only")
    L.append("program and sample-checks it (30 Int-tuple samples, a fixed seed for CI-reproducible")
    L.append("runs), reporting PASS/FAIL/ERROR/STUCK per law. **Known v1 limitation (tracked as issue")
    L.append("#74):** a law's INVOCATION of its trait op through `bang test`'s discovery/dispatch path")
    L.append("currently errors (`app: callee is not a function`) rather than reaching PASS/FAIL — the")
    L.append("grammar above is stable and build-gated (every form is a `lake build`-verified `#guard` in")
    L.append("`Bang/Frontend/Surface.lean`), but end-to-end law EXECUTION through the CLI is not yet")
    L.append("wired. `impl Add for (Int * Int) { fn add(p, q) = p }` — an impl with no laws to")
    L.append("discharge — type-checks and runs today; it is specifically the discovered-LAW dispatch")
    L.append("path that is still open.")
    L.append("")

    if "handleCustomS" not in surf or "def pDecl" not in surf:
        sys.exit(
            "gen-reference: `handleCustomS`/`pDecl` not found in Surface.lean — the "
            "User-defined effects section below is keyed off them (issue #88)."
        )
    L.append("## User-defined effects (ADR-0095, issue #44 Stage 7)")
    L.append("")
    L.append("A user declares a NAMED effect interface (`effect Name { op : ArgTy -> ResTy, … }`),")
    L.append("installs a HANDLER for it at a use site (`handle e with Name as h { … }`), and PERFORMS")
    L.append("through the handler's own capability value (`h.op(arg)`) — the SAME \"runtime is a")
    L.append("handler installed at the use site\" thesis the built-in effects (`state`/`atomically`)")
    L.append("already use, now user-spellable. The kernel is untouched: this surface lowers to the")
    L.append("already-landed `Handler.custom` constructor (ADR-0085) — a fourth handler shape, not a")
    L.append("sixth primitive.")
    L.append("")
    L.append("```")
    L.append("effect Net { fetch : Int -> Int }             -- the interface: one op, Int -> Int")
    L.append("")
    L.append("handle")
    L.append("  (net.fetch(1)) + (net.fetch(2))              -- performs through the `as`-bound `net`")
    L.append("with Net as net {")
    L.append("  fetch(n) => n * 10                           -- bare body = the resume value (implicit tail-resume)")
    L.append("}")
    L.append("-- ⟹ 30   (examples/handle-custom-tracer)")
    L.append("```")
    L.append("")
    L.append("| Form | Meaning |")
    L.append("|---|---|")
    L.append("| `effect Name { op : ArgTy -> ResTy, … }` | declares a named interface; the elaborator allocates a label (`4 + declIndex`, deterministic by decl order) and builds a program-derived op-signature table — the surface analogue of the kernel's `EffSig`. v1 ops are single-argument (`ArgTy -> ResTy`) or nullary (`op : ResTy`, no arrow) |")
    L.append("| `handle e with Name as h { op(x) => body, … }` | installs a handler for `Name` around `e`, binding the capability as `h` — the `as h` binder is MANDATORY (no implicit default: two nested handlers of the same effect would otherwise silently collide) and scopes over `e`, not the clause bodies |")
    L.append("| `handle e with (Name init) as h { … }` | the PARAMETER-CARRYING form — `init` is threaded internally at install time AND clause-nameable via the reserved identifier `param` (see below) |")
    L.append("| `h.op(arg)` | performs `op` on the named capability `h` — the SAME `$h.op` bare-call convention the built-in named-cap surface uses (`state … as h`); NOT `$h.op arg` (`h` is already a value, not a thunk) |")
    L.append("")
    L.append("**Clause bodies are CURRIED, matching the perform site** (`op(x, y) => body` desugars to a")
    L.append("curried clause, mirroring `h.op(x)(y)`'s own curried call shape) — a deliberate divergence")
    L.append("from today's trait-op convention (trait ops stay tuple-style, `fn add(a, b)`; effects are a")
    L.append("new construct born curried rather than inheriting the trait-op inconsistency).")
    L.append("")
    L.append("**A bare clause body IS the resume value — v1 has no `resume` keyword.** `op(x) => x * 10`")
    L.append("resumes the captured continuation with `x * 10` directly (one-shot, tail-resumptive); there")
    L.append("is no explicit `resume(…)` form to write in v1 (a future multi-shot upgrade grows the")
    L.append("surface additively, it does not change this form).")
    L.append("")
    L.append("**The carried param is CLAUSE-NAMEABLE via the reserved identifier `param`** (issue #87,")
    L.append("ADR-0095 D1's own worked example). A `(Name init) as h` clause body reads the `init` value")
    L.append("through the bare word `param` — READ-ONLY in v1 (no param-UPDATE surface, ADR-0092 D5")
    L.append("deferred):")
    L.append("")
    L.append("```")
    L.append("effect Reader { fetch : Int -> Int }")
    L.append("handle net.fetch(5) with (Reader 100) as net { fetch(x) => x + param }")
    L.append("-- net.fetch(5) resumes with 5 + 100 = 105")
    L.append("```")
    L.append("")
    L.append("`param` is RESERVED at every BINDER position (a clause-arg name, the `as h` capability")
    L.append("binder, a `let`/`fun` name, …) — the same discipline `with`/`resume` already use — so no")
    L.append("user binding can ever shadow it; it stays freely usable as an ordinary expression")
    L.append("(`param`, `param + x`, …) everywhere else, exactly like `get`. A param-less `Name` (no")
    L.append("`(Name init)`) still elaborates fine; its clauses simply have no reason to reference `param`.")
    L.append("")
    L.append("**The v1 RET-SHAPE restriction — a clause body may not itself perform an effect before")
    L.append("resuming.** A clause whose body computes-then-effects (e.g. performs another op, or")
    L.append("`raise`s) is rejected with a named diagnostic, not a bare type error:")
    L.append("")
    L.append("```")
    L.append("error: handle: clause 'fetch' body must be a `ret`-shape value in v1 (no effects")
    L.append("       before resuming) — a compute-then-return body needs binop typing (ADR-0065)")
    L.append("       + resumption-grade surfacing (Q27), tracked as the general-body entry gate")
    L.append("       (ADR-0095 D4)")
    L.append("```")
    L.append("")
    L.append("A clause body that only computes arithmetically over its argument and returns (no nested")
    L.append("effect performed) is fine (`fetch(n) => n * 10`, `fetch(n) => n + 1`); a clause performing")
    L.append("`raise`/another op/etc. before its final value hits this wall.")
    L.append("")
    L.append("**Effect op names may not collide with a built-in effect's own operations** (`get`/`put`/")
    L.append("`new`/`read`/`write`/`raise`/`handle` are reserved at the op-name position) — a collision is")
    L.append("a loud parse/elaboration error naming the conflict, not a silent shadow.")
    L.append("")
    L.append("See `examples/handle-custom-tracer/`, `examples/handle-custom-resume/` (now reading its")
    L.append("carried param through `param` for real, issue #87), and")
    L.append("`examples/handle-custom-abort-coexist/` (a `raise` inside a nested `handle` still aborts")
    L.append("PAST a custom handler that is still installed — the two effect systems coexist) for worked,")
    L.append("`check-examples`-gated single-op programs.")
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

    L.append("## Standard library")
    L.append("")
    L.append("Library functions available FREE in every program that mentions them — `Prelude.bang` (repo")
    L.append("root), auto-`use`d (ADR-0097): no `import`/`use` line needed. They are `let rec` bindings,")
    L.append("so call them with the **force convention**: `($concat) \"ab\" \"cd\"`, not bare `concat …`. A user")
    L.append("binding of the same name shadows the injected one (lexical scope, per-name — not an")
    L.append("all-or-nothing bucket); this also covers a project that names its OWN module `Prelude.bang` —")
    L.append("an explicit `use Prelude (name)`/`import Prelude` resolves to the USER's file (the ordinary")
    L.append("same-dir-then-root search, ADR-0093 D1) and its own binding of `name` wins, exactly like any")
    L.append("other user-vs-prelude shadow; with no explicit `use`/`import` naming `Prelude`, a same-named")
    L.append("file just sits there unreferenced (no silent pickup).")
    L.append("")
    L.append("| Function | Signature |")
    L.append("|---|---|")
    prelude_text = PRELUDE.read_text()
    prelude_sigs = extract_prelude_sigs(TYPECHECK.read_text())
    for name, sig in extract_stdlib(prelude_text, prelude_sigs):
        cell = f"`{sig}`" if sig else "— (no top-level annotation — see `Prelude.bang`)"
        L.append(f"| `{name}` | {cell} |")
    L.append("")
    L.append("Curried (multi-arg) `let rec`s type `… ! {Div}` — the #47 multi-arg gap (ADR-0073), a sound")
    L.append("over-approximation: they terminate but the certifier can't prove it, so they run correctly.")
    L.append("")

    L.append("### Generic prelude functions")
    L.append("")
    L.append("Also FREE in every program that mentions them — `Prelude.bang`'s remaining entries: the ⊥-row")
    L.append("(non-recursive) companions to the tagged-sum types (`Option`/`Result`/the built-in sum")
    L.append("`Either`) plus the type-agnostic first-slice prelude (issue #105). Auto-`use`d ONLY for the")
    L.append("names a program actually mentions (a syntactic scan, ADR-0097 — this is a FUEL discipline, not")
    L.append("just a scope-pollution one: `Prelude.bang` is a real module merged in via `mergeModules`, and")
    L.append("an unconditional merge would tax every program one evaluation step per unused entry). A user")
    L.append("binding of the same name shadows the injected one.")
    L.append("")
    L.append("| Function | Signature |")
    L.append("|---|---|")
    for name, sig in extract_generic_prelude(prelude_text, prelude_sigs):
        cell = f"`{sig}`" if sig else "— (see `Prelude.bang`)"
        L.append(f"| `{name}` | {cell} |")
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

    L.append("## `bang query` — the agent LSP as stateless CLI subcommands (issue #80)")
    L.append("")
    L.append("`bang query <op>` exposes the compiler's own facts (parse/elaborate/check results) as")
    L.append("JSON — the cheapest \"LSP for agents\": no server, no protocol, one process per call.")
    L.append("Every op's Lean-side implementation is `Bang/Frontend/Query.lean`, a **public library")
    L.append("API** (every fact-producing function is `public`, documented as reusable outside the")
    L.append("CLI — a Lean script can call `declFactsOf`/`nameRefEdgesOf`/`lawInstancesOf` directly).")
    L.append("")
    L.append("**`bang query dump [<file.bang>]` is the key operation**: the COMPLETE fact base in one")
    L.append("export, so you compose *arbitrary* queries (`jq`, `python`, a Lean script) instead of")
    L.append("waiting on a new fixed verb. Every curated verb below (`symbols`/`type`/`effects`/`def`/")
    L.append("`refs`) is a **thin projection** of the SAME fact list `dump` exports — one construct,")
    L.append("not six independent implementations.")
    L.append("")
    L.append("### `dump`'s schema — a VERSIONED public contract")
    L.append("")
    L.append("```json")
    L.append("{")
    L.append('  "ok": true,')
    L.append('  "schemaVersion": 1,')
    L.append('  "bangVersion": "0.1.0",')
    L.append('  "decls": [ { "name": "..", "kind": "let|letRec|fn|trait|impl|data|effect",')
    L.append('               "type": "T"|null, "row": "{..}"|null, "typeError": "msg"|null,')
    L.append('               "shape": {..}|null, "pub": true|false, "module": "Mod"|null } ],')
    L.append('  "refs": [ { "from": "declName", "to": "referencedName" } ],')
    L.append('  "laws": [ { "trait": "..", "law": "..", "params": [".."], "body": "source text" } ],')
    L.append('  "imports": [ { "module": ".." } ],')
    L.append('  "uses":    [ { "module": "..", "names": [".."] } ]')
    L.append("}")
    L.append("```")
    L.append("")
    L.append("`decls`/`refs`/`laws`/`imports`/`uses` are **FLAT top-level arrays of flat records** —")
    L.append("a relational fact base (Glean's \"predicates = tables, facts = rows\" framing), never a")
    L.append("nested tree. The concrete test: `dump`'s output loads into DuckDB with ONE `read_json`")
    L.append("call, no unnesting gymnastics —")
    L.append("")
    L.append("```sh")
    L.append("bang query dump myfile.bang | duckdb -c \"SELECT unnest(decls) FROM read_json('/dev/stdin')\"")
    L.append("```")
    L.append("")
    L.append("Every `DeclFact` key is **always present** — `null` means absent, never a missing key —")
    L.append("so a `jq '.decls[].type'`-style consumer never branches on key existence, only on")
    L.append("nullness. `type`/`row` are `some` only for a VALUE-typed decl (`let`/`letRec`/`fn`) that")
    L.append("type-checks; `typeError` carries the checker's message when it doesn't; `shape` carries")
    L.append("a structural summary (ops/ctors/params) for `trait`/`impl`/`data`/`effect`, which have no")
    L.append("value-level type. `refs` is DECL-granularity (which decl's body mentions which name).")
    L.append("")
    L.append("**Position-addressing (line/col → decl) landed at DECL granularity** (issue #52 slice 5,")
    L.append("`bang query hover`, below) — a cursor resolves to the NEAREST-ENCLOSING top-level decl,")
    L.append("not an exact sub-expression. EXACT sub-decl spans remain OUT of v1: `Surf` carries no")
    L.append("per-node span (the Spanned-Surf tier, `docs/notes/spanned-surf-design.md`'s Q1 — deferred")
    L.append("until a concrete consumer needs finer-than-decl precision).")
    L.append("")
    L.append("**`schemaVersion`/`bangVersion` are TWO DISJOINT fields, first-class from v1** (bang's")
    L.append("docs/notes/compiler-as-dbms-survey.md, the ONE piece of DBMS discipline adopted *eagerly*,")
    L.append("not post-1.0): bang's 0.x \"breaking changes allowed\" policy collides with \"agents write")
    L.append("durable scripts against `dump`'s JSON\" — every unversioned BREAKING change silently")
    L.append("invalidates every saved query. The two fields split the concern:")
    L.append("")
    L.append("- **`schemaVersion`** — a plain monotonic **integer**, THE CONTRACT. Bumps ONLY on a")
    L.append("  BREAKING shape change (a field/table rename, removal, or meaning-change) — never for")
    L.append("  additive growth. A durable consumer keys ITS compatibility check on this field alone.")
    L.append("- **`bangVersion`** — PROVENANCE metadata (which compiler binary emitted this dump), NOT")
    L.append("  a compatibility signal — never gate a script's behavior on it.")
    L.append("")
    L.append("**The other half of the contract binds the CONSUMER**: implementations **MUST IGNORE")
    L.append("UNKNOWN FIELDS** (the protobuf/Kubernetes-API discipline). This is what makes \"additive")
    L.append("⟹ non-breaking\" true by construction — a script asserting `schemaVersion == 1` must")
    L.append("survive twenty compiler releases that only ADD facts; a script that hard-fails on an")
    L.append("unrecognized key breaks that guarantee itself, regardless of what bang promises.")
    L.append("")
    L.append("`tools/golden-dump-caesar.json` is a pinned snapshot gated by `tools/test-query.sh`'s")
    L.append("`golden-dump-schema-pinned` check — ANY shape change (breaking or additive) must re-pin")
    L.append("this file in the same commit, so drift is always VISIBLE in the diff, never silent; a")
    L.append("BREAKING change additionally requires the `schemaVersion` bump.")
    L.append("")
    L.append("`decls`/`refs`/`laws`/`imports` are the **extensional** fact base (extracted, not")
    L.append("computed from other facts); the curated verbs below are **intensional** — derived")
    L.append("predicates (views) over this extensional base, kept few and stable per the Kythe/Glean")
    L.append("small-core lesson (push richness into derived views, not the base schema).")
    L.append("")
    L.append("**KNOWN v1 LIMITATIONS** (both match `check --json`'s own documented multi-file grants,")
    L.append("not new gaps): on a MULTI-FILE (resolver-aware) `dump`, `\"laws\"` is always `[]` — the")
    L.append("merged program has no single contiguous source `lawInstancesOf` could re-derive law")
    L.append("bodies from; and a decl's `\"module\"` is `null` unless the CLI layer's own resolution")
    L.append("walk supplies provenance (`Query.lean`'s `declFactsOf` alone never computes it — a flat")
    L.append("merged `Prog` carries no per-decl module field). An imported (not `use`d) decl's own")
    L.append("`\"name\"` is QUALIFIED by the merge (`Parse.bang`'s `dropWs` becomes `Parse_dropWs`,")
    L.append("`TypeCheck.mergeModules`'s convention) — `def`/`refs`/`type`/`effects` on a multi-file")
    L.append("program address the qualified name, discoverable via `dump`/`symbols`'s own `\"name\"`")
    L.append("field.")
    L.append("")
    L.append("### The curated verbs (thin projections of `dump`)")
    L.append("")
    L.append("| Verb | Args | Answers |")
    L.append("|---|---|---|")
    L.append("| `symbols` | `[<file.bang>]` | `dump`'s own `\"decls\"` array, unfiltered |")
    L.append("| `type` | `<file.bang> <name>` | one `DeclFact`'s `type`+`row`, looked up by name |")
    L.append("| `effects` | `<name> [<file.bang>]` | one `DeclFact`'s `row` alone |")
    L.append("| `laws` | `[<file.bang>]` | every discovered trait-law × impl instance (issue #60 seam) |")
    L.append("| `def` | `<name> <file.bang>` | the one decl DEFINING `name`, as a `DeclFact` |")
    L.append("| `refs` | `<name> <file.bang>` | `dump`'s own `\"refs\"` edges, filtered to `<name>` |")
    L.append("| `hover` | `[<file.bang>] <line> <col>` | the decl at 1-indexed `<line>:<col>` — nearest-enclosing, DECL granularity (issue #52 slice 5) |")
    L.append("")
    L.append("All are `--json`-only (agents are the audience — no human-rendering flag in v1). Every")
    L.append("op reads stdin when no `<file.bang>` is given, except `type`/`def`/`refs` (name-addressed")
    L.append("multi-arg forms that always require a file). A `<file.bang>` with `import`/`use` is")
    L.append("resolved the SAME way `bang check`/`bang run` resolve it — imports are visible to every")
    L.append("op. Exit codes: `0` the op ran (including an op-level `\"ok\":false` answer, e.g. `def`")
    L.append("naming a decl that doesn't exist — the tool succeeded, the ANSWER is negative); `1` the")
    L.append("op could not run at all (a parse or import-resolution failure, still `\"ok\":false` on")
    L.append("stdout); `2` a tool error (e.g. unreadable file) — reported on stderr, nothing on stdout,")
    L.append("never folded into the JSON (mirrors `check --json`'s own tool-error convention exactly).")
    L.append("")
    L.append("### `hover` — decl-granularity position query (issue #52 slice 5)")
    L.append("")
    L.append("`bang query hover [<file.bang>] <line> <col>` answers \"what decl is at this cursor, and")
    L.append("what is its type\" — the ONE position-addressed verb, resolving `<line>:<col>` (1-indexed,")
    L.append("matching every other located-error convention in bang) to the NEAREST-ENCLOSING top-level")
    L.append("decl (the LAST decl, in source order, whose name starts at-or-before the cursor). A cursor")
    L.append("anywhere in a decl's body — not just on its name — resolves to that WHOLE decl; this is")
    L.append("coarser than an LSP's exact sub-expression hover (see the position-addressing note above).")
    L.append("")
    L.append("```json")
    L.append("{\"ok\":true,\"decl\":{\"name\":\"main\",\"kind\":\"let\",\"type\":\"Int\",\"row\":\"{}\",")
    L.append(" \"typeError\":null,\"span\":{\"line\":2,\"col\":5,\"endLine\":2,\"endCol\":9}}}")
    L.append("```")
    L.append("")
    L.append("`decl` carries the SAME fields as one `dump`/`symbols` entry (`name`/`kind`/`type`/`row`/")
    L.append("`typeError`), plus `span` — the decl's NAME-TOKEN location, rendered with the same")
    L.append("`{\"line\",\"col\",\"endLine\",\"endCol\"}` shape `bang check --json`'s diagnostics use (one")
    L.append("`Span`-rendering convention, reused, not reinvented). A cursor before every decl's name")
    L.append("(e.g. inside the `import`/`use` header) is an honest miss:")
    L.append("")
    L.append("```json")
    L.append("{\"ok\":false,\"error\":\"no decl at 1:1\"}")
    L.append("```")
    L.append("")
    L.append("still exit `0` — the tool ran and produced a well-formed negative answer, the SAME")
    L.append("convention `def`'s \"no such decl\" miss uses. `hover` is resolver-aware like every other")
    L.append("op (imports visible); on a multi-file program the cursor addresses the ENTRY file's own")
    L.append("source text (the file passed on the command line), not an imported module's.")
    L.append("")
    L.append("**Known interaction (issue #100, open, not fixed by this verb):** a decl whose checker-")
    L.append("rendered `type` mentions a user `data` type can leak an internal μ-encoding placeholder")
    L.append("(e.g. `#1000070`) in the `type` string — the SAME rendering `dump`/`symbols`/`type` already")
    L.append("produce for such a decl. `hover` does not introduce this; it re-renders the existing fact.")
    L.append("")
    L.append("**Composing an arbitrary query over `dump`** — the whole point: no fixed verb answers")
    L.append("\"every exported decl whose type carries a divergence taint\", but `dump` + `jq` does:")
    L.append("")
    L.append("```sh")
    L.append('bang query dump myfile.bang | jq -c \'')
    L.append('  [.decls[] | select(.pub and ((.type // "") | contains("Div"))) | .name]\'')
    L.append("```")
    L.append("")

    L.append("## `bang rewrite` — the CQS command side over the query fact base (issue #81)")
    L.append("")
    L.append("`bang query` INSPECTS a program (the read model); `bang rewrite <verb>` REWRITES one —")
    L.append("a pure `Prog → Prog` transform, implemented in `Bang/Frontend/Rewrite.lean` as a")
    L.append("**public library API** (every rewrite is `public`, reusable outside the CLI, mirroring")
    L.append("`Bang.Query`'s own tier-1 convention) and consuming the QUERY side's own public facts")
    L.append("(`declFactsOf`) rather than re-deriving a second decl inventory.")
    L.append("")
    L.append("**Output contract — immutable by default, mutation opt-in** (the language's own")
    L.append("description-until-forced thesis, `$`/force, applied to tooling): every verb prints a")
    L.append("**unified diff** (source → rewritten) on stdout and touches NOTHING on disk, unless")
    L.append("`-w` is given, which APPLIES the change to the file in place. There is no partial or")
    L.append("silent mutation — a rewrite either emits a diff, or (with `-w`) writes the whole")
    L.append("rewritten file, or aborts loudly with nothing written.")
    L.append("")
    L.append("| Verb | Args | Does |")
    L.append("|---|---|---|")
    L.append("| `fmt` | `[<file.bang>] [-w]` | rewrite #0 — the canonical formatter (issue #58),")
    L.append("re-housed as a command; reads stdin if no file |")
    L.append("| `rename` | `<old> <new> <file.bang> [-w]` | rename a top-level declaration and every")
    L.append("reference to it |")
    L.append("| `annotate` | `[<file.bang>] [-w]` | infer types AND effect rows for every top-level")
    L.append("`let` lacking an ascription, splice them in; reads stdin if no file |")
    L.append("")
    L.append("**`fmt` as rewrite #0**: `bang fmt` (the pre-existing, print-only CLI surface) is")
    L.append("UNCHANGED — `bang rewrite fmt` is an ADDITIONAL surface sharing the SAME canonical")
    L.append("printer (`Bang.Format.showProg`), so the two never disagree on what \"canonical\" means.")
    L.append("`Bang.Rewrite.fmt` is a no-op on the parsed AST by construction (formatting changes")
    L.append("printed LAYOUT only — `Format.lean`'s own idempotency/round-trip laws already cover")
    L.append("that at the Lean level); the diff a user sees is entirely `showProg`'s re-layout.")
    L.append("")
    L.append("**`rename`'s three loud diagnostics** (ADR-0046 — never a silent guess): naming a")
    L.append("`<old>` that doesn't exist, a `<new>` that COLLIDES with an existing top-level name, or")
    L.append("an `<old>` that is ambiguous (more than one top-level decl sharing it — a malformed-")
    L.append("program defensive case). The rewrite itself is a shadowing-aware, capture-safe AST walk")
    L.append("(mirrors `Bang.TypeCheck`'s own module-qualification pass, ADR-0093): a binder that")
    L.append("shadows `<old>` stops the rename at that subtree, so a local variable of the same name")
    L.append("is never touched.")
    L.append("")
    L.append("### The preservation gate — the moat feature")
    L.append("")
    L.append("`rename`'s static collision check only sees TOP-LEVEL names — it cannot see that the")
    L.append("new name might collide with a LOCAL binding somewhere in the program (shadowing a")
    L.append("call site rather than another declaration). The **differential preservation gate**")
    L.append("catches this class of hazard: before emitting, `bang rewrite rename` re-elaborates")
    L.append("BOTH the original and rewritten program (`Bang.TypeCheck.checkAndLowerProg`) and runs")
    L.append("BOTH under the kernel ORACLE (`Bang.Source.eval`, the SAME reference `--engine=oracle`")
    L.append("uses) — if the two outcomes disagree (a value that differs, one side elaborating and")
    L.append("the other not, or elaboration failing with a genuinely different error), the rewrite")
    L.append("ABORTS: no diff, no write, a loud message naming the divergence, nonzero exit.")
    L.append("")
    L.append("This is a RUNG-1 (differential) preservation check, not a proof — `docs/notes/")
    L.append("proof-export-survey.md`'s rung-2 (the binary LR's contextual-equivalence certificate)")
    L.append("is the post-LR upgrade path for a machine-checked guarantee rather than a run-time")
    L.append("differential gate.")
    L.append("")
    L.append("### `annotate` — types AND effect rows become explicit, diff-visible ascriptions")
    L.append("")
    L.append("`bang rewrite annotate` infers the type AND effect row of every top-level `let`")
    L.append("lacking an explicit ascription and splices it in — the SAME diff-by-default/`-w`")
    L.append("contract every rewrite verb shares. It adds NO new checking: every fact it emits is")
    L.append("a re-rendering of what `bang query type`/`effects` already compute")
    L.append("(`Bang.Query.typeStringOfDecl`), reused directly.")
    L.append("")
    L.append("**The triple win**: checking is cheaper than inference (the checker already computed")
    L.append("every decl's type + row; annotate only renders it back into source), explicit context")
    L.append("for an agent reading the file (a decl's paradigm — which effects it may perform — is")
    L.append("visible without running the checker), and **effect creep becomes diff-visible**: a PR")
    L.append("that adds `Div`/`throws` to a previously-unconstrained decl shows as a one-line change")
    L.append("on `annotate`'s own re-run, the same way any other diff does.")
    L.append("")
    L.append("**Never overwrites an existing ascription.** `annotate` only fills in a MISSING")
    L.append("ascription — `let rec`/bounded `fn` decls already carry a mandatory one (ADR-0073/")
    L.append("bite-2's own grammar), so they are always a no-op; a `let` that already has")
    L.append("`: T` is left untouched even if the checker would infer something different-looking.")
    L.append("A human-written ascription is authoritative.")
    L.append("")
    L.append("**Row annotations name only the four BUILTIN effects today** (`throws`/`state`/`stm`/")
    L.append("`Div`) — a known gap, not a bug: naming a USER-declared `effect`'s label in a `! {ρ}`")
    L.append("ascription requires a checker-side extension (`TypeCheck.effNames`) that has not yet")
    L.append("landed. A decl whose row carries a user effect label is SKIPPED with a note (on")
    L.append("stderr) rather than emitting an ascription that would silently fail to constrain the")
    L.append("row it claims to — a forward pointer, not a silent gap.")
    L.append("")
    L.append("**Self-verified, per decl.** Before ever returning a candidate ascription, `annotate`")
    L.append("re-derives the checker's type string FROM the candidate and requires it to agree with")
    L.append("what was originally inferred (`roundTripsClean`) — a decl whose checker rendering is")
    L.append("ambiguous or otherwise fails this check is skipped, never emitted wrong. A failure")
    L.append("here skips only THAT decl, never the whole file.")
    L.append("")
    L.append("## `bang lint` — a rule package over the query fact base (issue #82)")
    L.append("")
    L.append("`bang lint [<file.bang>] [--json] [--quiet-clean]` runs a small package of rules")
    L.append("over `Bang.Query`'s own fact base (`declFactsOf`/`nameRefEdgesOf`) — RULES ARE")
    L.append("QUERIES, no new analysis machinery. Human table by default, `--json` for the agent")
    L.append("schema. It mirrors `tools/DeadCode.lean`'s own Lean-side dead-code discipline (root")
    L.append("set → transitive closure → \"genuine orphan vs. intentional park\" reading) at the")
    L.append("SURFACE-program level.")
    L.append("")
    L.append("| Rule | Severity | Fires when |")
    L.append("|---|---|---|")
    L.append("| `dead-private` | warning | a non-`pub` top-level decl is unreachable from the")
    L.append("program's public surface, its own trailing body, or (when declared) `main` — the")
    L.append("SAME root convention `bang run` itself uses (ADR-0093 D5) |")
    L.append("| `unused-pub` | info | a `pub` decl is referenced by NOTHING in the module (an")
    L.append("external importer may still use it — a much weaker signal than `dead-private`) |")
    L.append("| `fmt-divergence` | warning | the file's own layout ≠ its canonical form")
    L.append("(`bang rewrite fmt -w` is the fix) |")
    L.append("")
    L.append("**Exit contract**: `0` unless a `warning`-severity finding is present (an `info`-only")
    L.append("or empty report still exits `0` — the caller inspects `ok`/the finding list, the SAME")
    L.append("convention `bang check --json` uses); `1` when any `warning` finding fires; `2` the")
    L.append("file could not be read. `--quiet-clean` suppresses the \"no findings\" success line on")
    L.append("a clean human-table report (for a scripted caller wanting only")
    L.append("nonzero-exit-on-real-findings) — it has no effect on `--json` output, which is always")
    L.append("the complete, stable answer.")
    L.append("")
    L.append("**`dead-private`'s own advisory honesty** (mirroring `tools/DeadCode.lean`'s own")
    L.append("documented caveat): a decl reachable ONLY through a syntactic path this rule's SYNTACTIC")
    L.append("closure (`Query.nameRefEdgesOf` + `Query.surfUsesVar`) cannot see is a false positive")
    L.append("this rule does not itself distinguish from a genuine orphan — the finding names the")
    L.append("decl, the human/agent judges deletability.")
    L.append("")

    L.append("## `bang holes` — residual/underdetermined positions (issue #82 item 3)")
    L.append("")
    L.append("`bang holes [<file.bang>]` lists every top-level decl whose checked type or effect row")
    L.append("carries a RESIDUAL hole — a position the inference could not pin down. bang has no")
    L.append("user-facing `_` hole syntax yet, but the checker still reports underdetermined")
    L.append("positions: a bare `id = {fun x => x}` reports `Thunk #1000003 -> #1000003`, two")
    L.append("positions (arg and result) the checker left polymorphic. Those `#N` markers (with")
    L.append("`N ≥ holeBase`, `Bang.TypeCheck.holeBase`) ARE the holes — `holes` extracts and names")
    L.append("them. ALWAYS JSON (agents are the audience), resolver-aware like `query`.")
    L.append("")
    L.append("```")
    L.append("bang holes myfile.bang")
    L.append('{"ok":true,"holes":[{"name":"id","kind":"let","type":"Thunk #1000003 -> #1000003","row":"{}","holes":["#1000003"]}]}')
    L.append("```")
    L.append("")
    L.append("A fully-pinned program reports `{\"ok\":true,\"holes\":[]}`. **Exit contract** (the")
    L.append("`query` convention): `2` unreadable file (nothing on stdout), `1` parse/resolution")
    L.append("failure (`ok:false` on stdout), `0` a well-formed answer (an empty `holes` array is")
    L.append("still exit `0` — the caller inspects the array). This is a THIN PROJECTION of the SAME")
    L.append("`DeclFact` list `symbols`/`dump` expose — no new checking logic.")
    L.append("")
    L.append("## `bang impact` — the pre-edit blast radius (issue #82 item 5)")
    L.append("")
    L.append("`bang impact <file.bang> <decl>` reports the TRANSITIVE DEPENDENTS of `decl` — every")
    L.append("top-level decl that reaches it directly or through a chain, so you know what breaks")
    L.append("before you change it. This is the REVERSE of the reference graph `bang query refs`/")
    L.append("`dump` already expose (a forward edge `src → tgt` read backwards is \"`src` depends on")
    L.append("`tgt`\"), computed as a reverse closure over that SAME edge set — no new graph walk.")
    L.append("")
    L.append("```")
    L.append("bang impact myfile.bang double")
    L.append('{"ok":true,"decl":"double","dependents":[{"name":"main","kind":"let"},{"name":"quad","kind":"let"}]}')
    L.append("```")
    L.append("")
    L.append("An empty `dependents` array is the honest \"nothing depends on it, safe to change in")
    L.append("isolation\" answer. A nonexistent `decl` is a LOUD op-level miss")
    L.append("(`{\"ok\":false,\"error\":\"no top-level decl named '…'\"}`, exit `0` — the tool ran).")
    L.append("Same `2`/`1`/`0` exit contract as `holes`/`query`. ALWAYS JSON, resolver-aware. DECL")
    L.append("granularity (#52).")
    L.append("")
    L.append("## `bang semver-diff` — the public-surface diff (issue #82 item 6)")
    L.append("")
    L.append("`bang semver-diff <old.bang> <new.bang>` diffs the PUBLIC (`pub`) decl surface of two")
    L.append("programs and reports the required version bump — #72's enforcement engine (elm-package")
    L.append("precedent) falling out of the fact base. Non-`pub` decls are INVISIBLE (a private")
    L.append("decl's churn never bumps a version).")
    L.append("")
    L.append("```")
    L.append("bang semver-diff v1.bang v2.bang")
    L.append('{"ok":true,"bump":"major","added":["mul"],"removed":["sub"],"changed":[]}')
    L.append("```")
    L.append("")
    L.append("| Change to the `pub` surface | `bump` |")
    L.append("|---|---|")
    L.append("| a pub decl REMOVED, or its `(type, row)` CHANGED | `major` (breaking) |")
    L.append("| a pub decl ADDED (nothing removed/changed) | `minor` (feature) |")
    L.append("| no pub change | `patch` |")
    L.append("")
    L.append("The `bump` field is DERIVED from added/removed/changed so a caller (a release gate)")
    L.append("keys its policy on ONE field. **Exit contract**: `2` if EITHER file is unreadable")
    L.append("(tool error, nothing on stdout), `1` if EITHER side fails to parse (`ok:false` naming")
    L.append("the side), `0` a well-formed diff. ALWAYS JSON. **Known v1 gap** (a forward pointer,")
    L.append("not a silent miss): only VALUE-typed decls' `type`/`row` are compared — a `trait`/")
    L.append("`data`/`effect`'s structural `shape` change is not yet a `changed` finding.")
    L.append("")

    L.append("## Diagnostic codes (`bang explain`)")
    L.append("")
    L.append("GENERATED from the registry in `Bang/Frontend/DiagCodes.lean` (plan 013 s5) — the SINGLE")
    L.append("SOURCE OF TRUTH. Each diagnostic carries a STABLE code (the rustc `error[B004]` pattern):")
    L.append("it appears in `bang check` output (`error[B004]: …`) and in the `explainCode` field of")
    L.append("`bang check --json`. `bang explain <CODE>` prints the code's summary, teaching text, and a")
    L.append("minimal triggering example. A code stays stable across message-wording changes, so tools")
    L.append("and docs can reference it durably.")
    L.append("")
    L.append("| Code | Summary | `explain` example |")
    L.append("|---|---|---|")
    for code, summary, has_example in extract_diag_codes(diagcodes):
        ex = "yes" if has_example else "—"
        L.append(f"| `{code}` | {summary} | {ex} |")
    L.append("")

    return "\n".join(L) + "\n"


def main():
    try: __import__("subprocess").run(["bash", __import__("os").path.join(__import__("os").path.dirname(__file__), "tool-log.sh"), __import__("os").path.basename(__file__)], check=False)  # tool-log (plan 012)
    except Exception: pass
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
