#!/usr/bin/env python3
"""Checks a dataset extracted with `--upstream-closure term` against the same commit without it.

    python3 test/check_closure.py <dataset> <dataset with the closure>

The project's part must be the same; past it, every upstream declaration the closure reached is a
node with edges of its own, and nothing else is.
"""
from __future__ import annotations

import sys
from pathlib import Path

from check import check, failures, load

F = "Fixture."


def main() -> int:
    plain, full = load(Path(sys.argv[1])), load(Path(sys.argv[2]))
    m = full["meta"]
    check(m.get("upstreamClosure") == {"follow": "term", "display": "declared"}, "meta: upstreamClosure")
    check("upstreamClosure" not in plain["meta"], "meta: no upstreamClosure without the option")
    check({e["name"] for e in m["edges"]} == {"statement", "meaning", "term", "source", "upstream-statement",
                                             "upstream-meaning", "upstream-term"}, "meta: edge notions")

    # The project's part is what it was.
    project = lambda ds: {d["name"]: d for d in ds["decls"] if d["scope"] == "project"}
    check(project(plain) == {n: {**d, "id": project(plain)[n]["id"]} for n, d in project(full).items()},
          "the project's nodes are the same")
    for notion in ("statement", "meaning"):
        check(plain["edges"][notion] == full["edges"][notion], f"{notion} edges are the same")
    up_plain = {d["name"] for d in plain["decls"] if d["scope"] == "upstream"}
    up_full = {d["name"] for d in full["decls"] if d["scope"] == "upstream"}
    # `term` edges keep the targets that are nodes, and the closure adds nodes.
    pt, ft = plain["edges"]["term"], full["edges"]["term"]
    check(set(pt) == set(ft) and all(pt[n] <= ft[n] and ft[n] - pt[n] <= up_full - up_plain for n in pt),
          "term edges are the same, but for targets the closure added")
    check(up_plain < up_full, f"the closure adds upstream nodes ({len(up_plain)} → {len(up_full)})")

    # Upstream edges, and what they stop at.
    ust, ume, ute = (full["edges"][f"upstream-{n}"] for n in ("statement", "meaning", "term"))
    check("HAdd.hAdd" not in full["by_name"] and "HAdd" in up_full,
          "a projection is not a node: it is looked through, to its structure")
    check("Nat.one_pos" not in full["by_name"], "a lemma called only by a project proof is not reached")
    proofs = {d["name"] for d in full["decls"] if d["scope"] == "upstream" and d["isProp"]}
    check(proofs, "the closure reaches upstream proofs, through definitions' values")
    check(all(not ute.get(p) for p in proofs), "an upstream proof has no term edges: its proof is not walked")
    check(all(ume.get(p, set()) == ust.get(p, set()) for p in proofs), "an upstream proof means its statement")

    # Nothing stray: every upstream node is reached from the project along the closure's rule.
    is_prop = {d["name"]: d["isProp"] for d in full["decls"]}
    step = lambda n: (full["edges"]["statement"].get(n, set()) | ust.get(n, set()) |
                      (set() if is_prop[n] else full["edges"]["term"].get(n, set()) | ute.get(n, set())))
    seen = set(project(full))
    todo = list(seen)
    while todo:
        for t in step(todo.pop()):
            if t not in seen:
                seen.add(t)
                todo.append(t)
    check(up_full <= seen, f"every upstream node is reached ({len(up_full - seen)} are not)")

    # Facets past the project.
    stmts = {r["decl"]: r for r in full["facets"]["statement"]}
    check("value" in stmts.get("Nat.add", {}), "the statement facet covers an upstream definition, with its value")
    check(not any(p in stmts for p in proofs), "and not upstream proofs")
    sigs = {r["decl"]: r for r in full["facets"]["signature"]}
    check(all(n in sigs for n in up_full), "every upstream node has a signature")
    refs = {r[2] for r in sigs[F + "double_zero"].get("refs", [])}
    check(F + "double" in refs and F + "double_zero" not in refs,
          f"signature refs name the constants, not the declaration itself ({sorted(refs)})")

    if failures:
        for f in failures:
            print(f"FAIL: {f}")
        return 1
    print(f"ok: the closure adds {len(up_full - up_plain)} upstream nodes; all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
