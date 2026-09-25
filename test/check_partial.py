#!/usr/bin/env python3
"""Checks a dataset extracted with `--skip-module Fixture.Uses` against the full one: the skipped
module and the root, which imports it, are listed as unavailable and have no nodes, and every
other project node is unchanged.

  python3 test/check_partial.py FULL PARTIAL
"""
import json
import sys
from pathlib import Path

UNAVAILABLE = ["Fixture", "Fixture.Uses"]


def project(ds: Path) -> dict:
    rows = [json.loads(line) for line in (ds / "decls.jsonl").read_text().splitlines()]
    return {r["name"]: (r["module"], r["hashes"]) for r in rows if r["scope"] == "project"}


def main() -> int:
    full, partial = Path(sys.argv[1]), Path(sys.argv[2])
    errors = []
    listed = json.loads((partial / "meta.json").read_text())["library"].get("unavailable")
    if listed != UNAVAILABLE:
        errors.append(f"library.unavailable is {listed}, expected {UNAVAILABLE}")
    a, b = project(full), project(partial)
    if any(module in UNAVAILABLE for module, _ in b.values()):
        errors.append("nodes of unavailable modules were extracted")
    if b != {n: v for n, v in a.items() if v[0] not in UNAVAILABLE}:
        errors.append("skipping a module changed the other modules' nodes")
    for e in errors:
        print(f"FAIL: {e}")
    if not errors:
        print("ok: a module that does not build is skipped with its importers, and nothing else changes")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
