#!/usr/bin/env python3
# tool: role=gen couples=Bang/**/*.lean,leanlex.py runs-in=manual
"""Generate source-syntax symbol indexes for the Lean source tree.

The default index is unchanged: declarations by keyword, not elaborator-derived exports.
`--public` is a narrower source projection of declarations explicitly made public by a
`public` modifier or an enclosing `public section`.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from collections.abc import Iterable
from pathlib import Path

from leanlex import strip_comments

ROOT = Path(__file__).resolve().parent.parent
KINDS = "def|theorem|lemma|inductive|structure|class|instance|abbrev|axiom|opaque"
LEGACY_MODIFIERS = "private|protected|noncomputable|partial|unsafe|scoped|local"
MODIFIERS = LEGACY_MODIFIERS + "|public"
LEGACY_DECL = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:{LEGACY_MODIFIERS})\s+)*)"
    rf"(?P<kind>{KINDS})\s+(?P<name>[^\s({{:\[]+)(?P<rest>.*)$"
)
DECL = re.compile(
    rf"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:{MODIFIERS})\s+)*)"
    rf"(?P<kind>{KINDS})\s+(?P<name>[^\s({{:\[]+)(?P<rest>.*)$"
)
SCOPE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?P<visibility>public|private|noncomputable)\s+)?"
    r"(?P<kind>namespace|section|mutual)(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$"
)
END = re.compile(r"^end(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$")


class SymbolFactsError(ValueError):
    """Lean source scopes are malformed for the source-syntax projection."""


def lean_files(root: Path = ROOT) -> list[Path]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "Bang/*.lean", "Bang/**/*.lean"],
        check=True,
        capture_output=True,
        text=True,
    )
    return [root / path for path in sorted(set(result.stdout.splitlines()))]


def module_name(path: Path, root: Path) -> str:
    return ".".join(path.relative_to(root).with_suffix("").parts)


def declaration(line: str, include_public: bool = False):
    match = (DECL if include_public else LEGACY_DECL).match(line)
    if not match:
        return None
    modifiers = match.group("mods").split()
    rest = match.group("rest").strip()
    signature = rest.split(":=", 1)[0].strip()
    signature = (signature[:90] + "…") if len(signature) > 90 else signature
    return match.group("kind"), match.group("name"), signature, modifiers


def collect_symbols(root: Path = ROOT) -> list[dict]:
    symbols = []
    for path in lean_files(root):
        relative = path.relative_to(root).as_posix()
        for line_number, line in enumerate(
            path.read_text(errors="replace").splitlines(), 1
        ):
            parsed = declaration(line)
            if parsed is None:
                continue
            kind, name, signature, _ = parsed
            symbols.append(
                {
                    "name": name,
                    "kind": kind,
                    "file": relative,
                    "line": line_number,
                    "sig": signature,
                }
            )
    return symbols


def public_symbols_from_text(text: str, path: str, module: str) -> list[dict]:
    scopes: list[tuple[str, str | None, bool]] = []
    symbols: list[dict] = []
    for line_number, line in enumerate(strip_comments(text).splitlines(), 1):
        line = line.rstrip()
        if not line.strip():
            continue
        scope = SCOPE.match(line)
        if scope:
            kind = scope.group("kind")
            visibility = scope.group("visibility")
            if visibility == "public" and kind != "section":
                raise SymbolFactsError(
                    f"{path}:{line_number}: public {kind} is not a visibility scope"
                )
            inherited_public = any(entry[2] for entry in scopes)
            scopes.append(
                (kind, scope.group("name"), inherited_public or visibility == "public")
            )
            continue
        closing = END.match(line)
        if closing:
            if not scopes:
                raise SymbolFactsError(f"{path}:{line_number}: unmatched end")
            closing_name = closing.group("name")
            if closing_name is None:
                scopes.pop()
                continue
            matching = next(
                (
                    index
                    for index in range(len(scopes) - 1, -1, -1)
                    if scopes[index][1] == closing_name
                ),
                None,
            )
            if matching is None:
                raise SymbolFactsError(
                    f"{path}:{line_number}: unmatched end {closing_name}"
                )
            del scopes[matching:]
            continue

        parsed = declaration(line, include_public=True)
        if parsed is None:
            continue
        kind, name, _, modifiers = parsed
        if "private" in modifiers:
            continue
        in_public_section = any(scope[2] for scope in scopes)
        if "public" in modifiers:
            basis = "public-modifier"
        elif in_public_section:
            basis = "public-section"
        else:
            continue
        symbols.append(
            {
                "module": module,
                "path": path,
                "name": name,
                "kind": kind,
                "line": line_number,
                "visibilityBasis": basis,
            }
        )

    malformed = [scope for scope in scopes if scope[0] == "mutual"]
    if malformed:
        open_scopes = ", ".join(
            f"{kind} {name}" if name else kind for kind, name, _ in malformed
        )
        raise SymbolFactsError(f"{path}: unclosed mutual scope(s): {open_scopes}")
    return symbols


def collect_public_symbols(
    root: Path = ROOT, source_paths: Iterable[Path] | None = None
) -> list[dict]:
    symbols = []
    for source_path in source_paths if source_paths is not None else lean_files(root):
        relative = source_path.relative_to(root).as_posix()
        text = source_path.read_text(encoding="utf-8")
        projected = public_symbols_from_text(
            text,
            relative,
            module_name(source_path, root),
        )
        syntax = strip_comments(text)
        declares_public = re.search(r"^\s*public\s+section\b", syntax, re.MULTILINE)
        declares_public = declares_public or re.search(
            rf"^\s*(?:@\[[^\]]*\]\s*)*public\s+(?:{KINDS})\b",
            syntax,
            re.MULTILINE,
        )
        if declares_public and not projected:
            raise SymbolFactsError(
                f"{relative}: public syntax produced no declaration inventory"
            )
        symbols.extend(projected)
    return symbols


def self_test() -> None:
    probe = """namespace Bang
@[expose] public section
public abbrev Explicit := Nat
inductive SectionVisible where
  | mk
private def Hidden := 0
namespace Nested
mutual
def First := 1
def Second := First
end
end Nested
end
-- public def CommentLine := 2
/- public inductive CommentBlock where | mk -/
def AfterPublic := 3
public instance namedInstance : Inhabited Nat := inferInstance
end Bang
"""
    symbols = public_symbols_from_text(probe, "Bang/Probe.lean", "Bang.Probe")
    by_name = {symbol["name"]: symbol for symbol in symbols}
    assert by_name["Explicit"]["visibilityBasis"] == "public-modifier"
    assert by_name["SectionVisible"]["visibilityBasis"] == "public-section"
    assert by_name["First"]["visibilityBasis"] == "public-section"
    assert by_name["Second"]["visibilityBasis"] == "public-section"
    assert by_name["namedInstance"]["kind"] == "instance"
    assert "Hidden" not in by_name
    assert "CommentLine" not in by_name and "CommentBlock" not in by_name
    assert "AfterPublic" not in by_name
    try:
        public_symbols_from_text("mutual\npublic def Leaked := 1\n", "bad.lean", "Bad")
    except SymbolFactsError:
        pass
    else:
        raise AssertionError("unclosed mutual did not fail")

    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        source = root / "Bang/Untracked.lean"
        source.parent.mkdir()
        source.write_text("public def Visible := 1\n", encoding="utf-8")
        projected = collect_public_symbols(root, [source])
        assert [symbol["name"] for symbol in projected] == ["Visible"]
        source.write_text("public section\nend\n", encoding="utf-8")
        try:
            collect_public_symbols(root, [source])
        except SymbolFactsError:
            pass
        else:
            raise AssertionError("empty public syntax inventory did not fail")


def render_text(
    symbols: list[dict], by_file: bool, pattern: str | None, public: bool
) -> None:
    path_key = "path" if public else "file"
    if by_file:
        current = None
        for symbol in sorted(symbols, key=lambda item: (item[path_key], item["line"])):
            if symbol[path_key] != current:
                current = symbol[path_key]
                print(f"\n── {current} ──")
            print(f"  {symbol['line']:>5}  {symbol['kind']:<9} {symbol['name']}")
    else:
        for symbol in sorted(symbols, key=lambda item: item["name"].lower()):
            location = f"{symbol[path_key]}:{symbol['line']}"
            print(f"{symbol['name']:<42} {symbol['kind']:<9} {location}")
    print(
        f"\n{len(symbols)} declaration(s)"
        + (f" matching '{pattern}'" if pattern else "")
        + f" across {len({symbol[path_key] for symbol in symbols})} module(s).",
        file=sys.stderr,
    )


def main(argv: list[str] | None = None) -> int:
    try:
        subprocess.run(
            ["bash", str(Path(__file__).with_name("tool-log.sh")), Path(__file__).name],
            check=False,
        )
    except Exception:
        pass
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pattern", nargs="?")
    parser.add_argument("--by-file", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--public", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)

    try:
        if args.self_test:
            self_test()
            current = collect_public_symbols(ROOT)
            if not current:
                raise SymbolFactsError("current public declaration inventory is empty")
            print(
                f"symbols: PASS — public syntax poles hold; {len(current)} current public declarations."
            )
            return 0
        symbols = collect_public_symbols(ROOT) if args.public else collect_symbols(ROOT)
    except (AssertionError, SymbolFactsError, subprocess.CalledProcessError) as error:
        print(f"symbols: FAIL — {error}", file=sys.stderr)
        return 1

    if args.pattern:
        needle = args.pattern.lower()
        symbols = [symbol for symbol in symbols if needle in symbol["name"].lower()]
    if args.json:
        print(json.dumps(symbols, indent=2))
    else:
        render_text(symbols, args.by_file, args.pattern, args.public)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
