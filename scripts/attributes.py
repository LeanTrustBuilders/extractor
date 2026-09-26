#!/usr/bin/env python3
"""Adds the `attributes` facet to a dataset: the attributes each declaration is written with.

  python3 scripts/attributes.py --dataset DIR --source DIR

A library says things about its declarations in attributes that the compiled library keeps in
extensions only it can read: Mathlib's `@[stacks 09GA "comment"]`, `@[kerodon 0001]` and
`@[wikidata Q616608]` link a declaration to the Stacks project, Kerodon and Wikidata; `@[deprecated]`
marks one as kept only for compatibility; `@[simp]`, `@[to_additive]` say how it is used. This
reads them from the sources, as written: the `@[…]` blocks between a declaration's doc comment and
its keyword, over the range the `source` facet gives (under `--source`, a checkout at the dataset's
commit).

It writes `facets/attributes.jsonl` (schema `attributes/1`): one row per declaration written with
attributes, `{decl, attributes: [{name, args}]}`, `args` the text after the name (`09GA "comment"`),
and adds the facet to `meta.json`. Reading the text is a heuristic: attributes added later with an
`attribute [...] name` command are not seen, and a declaration generated from another (an
`@[to_additive]` twin) shares its range, so its attributes.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def utf16_to_index(line: str, col: int) -> int:
    units = 0
    for i, ch in enumerate(line):
        if units >= col:
            return i
        units += 2 if ord(ch) > 0xFFFF else 1
    return len(line)


def skip_space_and_comments(text: str, i: int) -> int:
    """Past blank space, line comments and block comments (doc comments included), which nest."""
    n = len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif text.startswith("/-", i):
            depth = 0
            while i < n:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                    if depth == 0:
                        break
                else:
                    i += 1
        else:
            break
    return i


def split_top(text: str) -> list[str]:
    """``text`` split at the commas outside brackets and strings."""
    parts, depth, start, i = [], 0, 0, 0
    while i < len(text):
        c = text[i]
        if c == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
            continue
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif c == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
        i += 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def attribute_blocks(text: str) -> list[dict]:
    """The attributes of the `@[…]` blocks that open a declaration's text."""
    out = []
    i = skip_space_and_comments(text, 0)
    while text.startswith("@[", i):
        depth, j = 0, i + 1
        while j < len(text):
            c = text[j]
            if c == '"':
                k = j + 1
                while k < len(text) and text[k] != '"':
                    k += 2 if text[k] == "\\" else 1
                j = k + 1
                continue
            if c == "[":
                depth += 1
            elif c == "]":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        for attr in split_top(text[i + 2:j]):
            # `scoped simp`, `local instance`: the scope is not the attribute.
            words = attr.split(None, 1)
            if words and words[0] in ("scoped", "local") and len(words) > 1:
                attr = words[1]
            name, _, args = attr.partition(" ")
            out.append({"name": name.strip(), "args": " ".join(args.split())})
        i = skip_space_and_comments(text, j + 1)
    return out


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--dataset", type=Path, required=True)
    p.add_argument("--source", type=Path, required=True, help="a checkout of the library at the dataset's commit")
    args = p.parse_args()
    meta = json.loads((args.dataset / "meta.json").read_text(encoding="utf-8"))
    source = next((f for f in meta.get("facets", []) if f["name"] == "source"), None)
    if source is None:
        print("the dataset has no source facet", file=sys.stderr)
        return 1
    files: dict[str, list[str] | None] = {}
    rows = []
    with (args.dataset / source["file"]).open(encoding="utf-8") as f:
        for line in f:
            if not line.strip():
                continue
            row = json.loads(line)
            path = row["path"]
            if path not in files:
                file = args.source / path
                files[path] = file.read_text(encoding="utf-8", errors="replace").splitlines() if file.exists() else None
            lines = files[path]
            (l0, c0), (l1, _) = row["start"], row["end"]
            if lines is None or l0 < 1 or l1 > len(lines):
                continue
            chunk = lines[l0 - 1:l1]
            chunk[0] = chunk[0][utf16_to_index(chunk[0], c0):]
            attrs = attribute_blocks("\n".join(chunk))
            if attrs:
                rows.append({"decl": row["decl"], "attributes": attrs})
    (args.dataset / "facets").mkdir(exist_ok=True)
    with (args.dataset / "facets" / "attributes.jsonl").open("w", encoding="utf-8") as out:
        for r in rows:
            out.write(json.dumps(r, ensure_ascii=False, separators=(",", ":")) + "\n")
    facets = [f for f in meta.get("facets", []) if f.get("name") != "attributes"]
    facets.append({"name": "attributes", "file": "facets/attributes.jsonl", "schema": "attributes/1", "count": len(rows),
                   "description": "the attributes each declaration is written with (`@[…]` before its keyword), read "
                                  "from the sources by scripts/attributes.py: name and the text of its arguments"})
    meta["facets"] = facets
    (args.dataset / "meta.json").write_text(json.dumps(meta, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"attributes: {len(rows)} declarations written with attributes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
