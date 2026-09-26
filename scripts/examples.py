#!/usr/bin/env python3
"""Adds the `examples` facet to a dataset: the `example`s of the library that name each declaration.

  python3 scripts/examples.py --dataset DIR --source DIR [--repo OWNER/NAME]

An `example` is elaborated and then discarded: the compiled library does not keep it, so the
extractor cannot see it. It is still a unit test of the declarations its statement names, checked by
Lean at every build. This analyzer reads the library's sources (the paths of `modules.jsonl`, under
`--source`, a checkout at the dataset's commit), finds every `example`, and resolves the identifiers
of its statement as Lean would: through the namespaces around it, then the namespaces opened, then as
written, against the dataset's project nodes (an example of the library tests the library, not what
it builds on). Names bound in the statement itself are local.

It writes `facets/examples.jsonl` (schema `examples/1`): one row per declaration some example names,
`{decl, examples: [{path, line, end, statement, sorry}]}`, where `sorry` says whether the example's
text uses `sorry`; and adds the facet to `meta.json`. Reading source text is a heuristic: an example
whose statement names a declaration through notation only is not found.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

EXAMPLE = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|noncomputable|public)\s+)*example\b")
NAMESPACE = re.compile(r"^namespace\s+(\S+)")
SECTION = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|private)\s+)*section\b")
END = re.compile(r"^end\b")
OPEN = re.compile(r"^open\s+(.*?)\s*$")
SORRY = re.compile(r"\bsorry\b")
IDENT = re.compile(r"(?<![\w'.])(?:[^\W\d]|_)[\w'!?]*(?:\.(?:[^\W\d]|_)[\w'!?]*)*")
BINDER = re.compile(r"[(\[{⦃]\s*((?:[^\W\d][\w'!?]*\s+)*[^\W\d][\w'!?]*)\s*:(?!=)")
QUANTIFIED = re.compile(r"(?:∀|∃!?|fun|λ|Σ|Π)\s*[(\[{⦃]?\s*((?:[^\W\d][\w'!?]*\s*)+)")


def comment_end(lines: list[str], i: int) -> int:
    """The line after the block comment that starts on line i. Lean's block comments nest."""
    depth = 0
    for j in range(i, len(lines)):
        line, k = lines[j], 0
        while k < len(line):
            if line.startswith("/-", k):
                depth, k = depth + 1, k + 2
            elif line.startswith("-/", k):
                depth, k = depth - 1, k + 2
                if depth == 0:
                    return j + 1
            else:
                k += 1
    return len(lines)


def statement(text: str) -> str:
    """An example up to its proof: up to the first `:=` outside brackets."""
    depth = 0
    for k, char in enumerate(text):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth = max(depth - 1, 0)
        elif depth == 0 and text.startswith(":=", k):
            return text[:k].rstrip()
    return text.rstrip()


def signature(text: str) -> str:
    """An example's binders: its statement up to the colon that starts its type."""
    depth = 0
    for k, char in enumerate(text):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth = max(depth - 1, 0)
        elif depth == 0 and char == ":" and not text.startswith(":=", k):
            return text[:k]
    return text


def open_names(text: str) -> list[str]:
    """The namespaces an `open` line opens."""
    text = re.sub(r"\([^)]*\)", " ", text)
    text = re.split(r"\s(?:hiding|renaming)\s", " " + text + " ")[0]
    return [word for word in text.split() if word not in ("scoped", "in")]


def scan(source: str, path: str) -> list[dict]:
    """The examples of a module, with the namespaces around each and those opened."""
    lines = source.splitlines()
    scopes: list[list[str]] = []
    opened: list[list[str]] = [[]]
    once: list[str] = []
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("/-"):
            i = comment_end(lines, i)
            continue
        if NAMESPACE.match(line):
            scopes.append(NAMESPACE.match(line).group(1).split("."))
            opened.append([])
        elif SECTION.match(line) or line.startswith("mutual"):
            scopes.append([])
            opened.append([])
        elif END.match(line) and scopes:
            scopes.pop()
            opened.pop()
        elif OPEN.match(line):
            names = open_names(OPEN.match(line).group(1))
            if line.rstrip().endswith(" in"):
                once += names
            else:
                opened[-1] += names
            i += 1
            continue
        if EXAMPLE.match(line):
            start = i
            i += 1
            while i < len(lines) and (not lines[i] or lines[i][0].isspace()):
                i += 1
            end = start + len("\n".join(lines[start:i]).rstrip().splitlines())
            text = "\n".join(lines[start:end])
            out.append({"path": path, "line": start + 1, "end": end, "statement": statement(text),
                        "sorry": bool(SORRY.search(text)),
                        "scope": [part for scope in scopes for part in scope],
                        "opens": [name for scope in opened for name in scope] + once})
            once = []
            continue
        if line and not line[0].isspace() and not line.startswith(("--", "@[")):
            once = []
        i += 1
    return out


def named(example: dict, names: set[str]) -> set[str]:
    """The declarations an example's statement names, resolved as Lean would."""
    text = example["statement"]
    local = {name for group in BINDER.findall(signature(text)) + QUANTIFIED.findall(text) for name in group.split()}
    scope = example["scope"]
    found = set()
    for token in IDENT.findall(text):
        if token == "example" or token.split(".")[0] in local:
            continue
        if token.startswith("_root_."):
            candidates = [token[len("_root_."):]]
        else:
            candidates = [".".join(scope[:k] + [token]) for k in range(len(scope), -1, -1)] + \
                [f"{name}.{token}" for name in example["opens"]]
        hit = next((name for name in candidates if name in names), None)
        if hit:
            found.add(hit)
    return found


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--dataset", type=Path, required=True)
    p.add_argument("--source", type=Path, required=True, help="a checkout of the library at the dataset's commit")
    args = p.parse_args()
    meta = json.loads((args.dataset / "meta.json").read_text(encoding="utf-8"))
    # The library's own declarations: an example in it tests the library, not what it builds on.
    decls = [json.loads(l) for l in (args.dataset / "decls.jsonl").read_text(encoding="utf-8").splitlines() if l.strip()]
    names = {d["name"] for d in decls if d.get("scope") == "project"}
    modules = [json.loads(l) for l in (args.dataset / "modules.jsonl").read_text(encoding="utf-8").splitlines() if l.strip()]
    by_decl: dict[str, list[dict]] = {}
    count = 0
    for m in modules:
        path = m.get("path") or ""
        f = args.source / path
        if not path or not f.exists():
            continue
        for ex in scan(f.read_text(encoding="utf-8", errors="replace"), path):
            count += 1
            row = {k: ex[k] for k in ("path", "line", "end", "statement", "sorry")}
            for d in sorted(named(ex, names)):
                by_decl.setdefault(d, []).append(row)
    rows = [{"decl": d, "examples": by_decl[d]} for d in sorted(by_decl)]
    (args.dataset / "facets").mkdir(exist_ok=True)
    with (args.dataset / "facets" / "examples.jsonl").open("w", encoding="utf-8") as out:
        for r in rows:
            out.write(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n")
    facets = [f for f in meta.get("facets", []) if f.get("name") != "examples"]
    facets.append({"name": "examples", "file": "facets/examples.jsonl", "schema": "examples/1", "count": len(rows),
                   "description": "the `example`s of the library whose statement names the declaration, found in "
                                  "the sources by scripts/examples.py (they are not in the compiled library): path, "
                                  "lines, statement, and whether it uses `sorry`"})
    meta["facets"] = facets
    (args.dataset / "meta.json").write_text(json.dumps(meta, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"examples: {count} examples, naming {len(rows)} declarations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
