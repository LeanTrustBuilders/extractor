#!/usr/bin/env python3
"""Checks two datasets extracted from test/fixture (A) and test/fixture-b (B).

    python3 test/check.py <dataset A> <dataset B>

Standard library only. Exits non-zero on the first failed check, printing every failure.
"""
from __future__ import annotations

import json
import struct
import sys
from pathlib import Path

failures: list[str] = []


def check(cond: bool, what: str) -> None:
    if not cond:
        failures.append(what)


def load(root: Path) -> dict:
    meta = json.loads((root / "meta.json").read_text())
    decls = [json.loads(line) for line in (root / "decls.jsonl").read_text().splitlines()]
    by_name = {d["name"]: d for d in decls}
    edges = {}
    for e in meta["edges"]:
        data = (root / e["file"]).read_bytes()
        check(len(data) == 8 * e["count"], f"{root.name}: {e['file']} size matches its count")
        pairs = [struct.unpack_from("<ii", data, 8 * k) for k in range(len(data) // 8)]
        out: dict[str, set[str]] = {}
        for s, t in pairs:
            out.setdefault(decls[s]["name"], set()).add(decls[t]["name"])
        edges[e["name"]] = out
    facets = {}
    for f in meta["facets"]:
        facets[f["name"]] = [json.loads(line) for line in (root / f["file"]).read_text().splitlines()]
    return {"meta": meta, "decls": decls, "by_name": by_name, "edges": edges, "facets": facets}


def main() -> int:
    a, b = load(Path(sys.argv[1])), load(Path(sys.argv[2]))
    F = "Fixture."

    # meta.json
    m = a["meta"]
    check(m["spec"] == "ltb-dataset/0", "meta: spec")
    pinned = (Path(__file__).resolve().parents[1] / "lean-toolchain").read_text().strip()
    check(m["toolchain"] == pinned, f"meta: toolchain is {m['toolchain']}, not the extractor's {pinned}")
    check(m["library"]["commit"] == "A" and m["library"]["root"] == "Fixture", "meta: library")
    check(m["hasher"]["local"] == "ltb-local-v1", "meta: local hasher")
    check({e["name"] for e in m["edges"]} == {"statement", "meaning", "term"}, "meta: edge notions")
    check({"docstring", "source", "axioms", "annotation.claim", "annotation.example_of",
           "annotation.nonexample_of"} <= {f["name"] for f in m["facets"]}, "meta: facets")
    check(m["counts"]["project"] + m["counts"]["upstream"] == m["counts"]["nodes"], "meta: counts")

    # Nodes and kinds.
    kinds = {F + "double": "definition", F + "triple_pos": "theorem", F + "Pos": "structure",
             F + "one": "definition", F + "IsSmall": "definition", F + "double_triple": "theorem"}
    for name, kind in kinds.items():
        d = a["by_name"].get(name)
        check(d is not None and d["kind"] == kind and d["scope"] == "project",
              f"A: {name} is a project {kind} (got {d and (d['scope'], d['kind'])})")
    check(a["by_name"][F + "triple_pos"]["isProp"] is True, "A: triple_pos is a proof")
    check(a["by_name"][F + "double"]["isProp"] is False, "A: double is not a proof")
    check(a["by_name"][F + "double"]["module"] == "Fixture.Basic", "A: module of double")
    check(a["by_name"][F + "double_triple"]["module"] == "Fixture.Uses", "A: module of double_triple")
    check(any(d["kind"] == "instance" and d["name"].startswith(F) for d in a["decls"]),
          "A: the instance is a node")
    check(not any(d["name"] == F + "Pos.mk" for d in a["decls"]), "A: constructors are not nodes")
    nat = a["by_name"].get("Nat")
    check(nat is not None and nat["scope"] == "upstream" and nat["package"] == "lean4",
          f"A: Nat is an upstream node of package lean4 (got {nat and (nat['scope'], nat['package'])})")
    check(a["by_name"][F + "double"]["package"] == "Fixture", "A: project package label")

    # Edges.
    st, me, te = a["edges"]["statement"], a["edges"]["meaning"], a["edges"]["term"]
    check(F + "double" in st.get(F + "double_zero", set()), "A: statement double_zero → double")
    check(F + "one_pos'" in te.get(F + "one", set()), "A: term one → one_pos'")
    check(F + "one_pos'" not in me.get(F + "one", set()), "A: meaning one ↛ one_pos' (proof field)")
    check(F + "Pos" in me.get(F + "one", set()), "A: meaning one → Pos")
    check(F + "triple" in me.get(F + "double_triple", set()) and
          F + "double" in me.get(F + "double_triple", set()), "A: meaning across modules")
    check(not me.get("Nat", set()), "A: upstream nodes have no outgoing edges")

    # Hashes between A and B.
    def hashes(ds, name):
        return ds["by_name"][name]["hashes"]

    def same(name_a, name_b, key):
        return hashes(a, name_a)[key] == hashes(b, name_b)[key]

    expectations = [
        # name in A, name in B, meaning same?, local same?, content same?
        ("double", "double", False, False, False),
        ("triple", "triple", True, True, True),
        ("double_zero", "double_zero", False, True, False),
        ("double_triple", "double_triple", False, True, False),
        ("triple_one", "triple_one", False, False, False),
        ("triple_two", "triple_two", True, True, False),
        ("triple_comm", "triple_comm", True, True, True),
        ("triple_three", "triple_three'", True, True, True),
        ("triple_pos", "triple_pos", True, True, True),
    ]
    for na, nb, meaning, local, content in expectations:
        for key, expected in (("meaning", meaning), ("local", local), ("content", content)):
            check(same(F + na, F + nb, key) == expected,
                  f"A→B: {na} → {nb}: {key} hash {'unchanged' if expected else 'changed'}")
    check(F + "triple_three" not in b["by_name"] and F + "triple_three'" in b["by_name"],
          "B: triple_three was renamed")

    # Facets.
    src = {r["decl"]: r for r in a["facets"]["source"]}
    check(src[F + "triple_pos"]["keyword"] == "theorem", "A: keyword of triple_pos")
    check(src[F + "double"]["keyword"] == "def", "A: keyword of double")
    check(src[F + "Pos"]["keyword"] == "structure", "A: keyword of Pos")
    check(src[F + "double"]["path"] == "Fixture/Basic.lean", f"A: path of double ({src[F + 'double']['path']})")
    check(src[F + "double"]["start"][0] < src[F + "double"]["end"][0] or True, "A: source range")
    docs = {r["decl"]: r["text"] for r in a["facets"]["docstring"]}
    check(docs.get(F + "double", "").startswith("A definition that version B changes"), "A: docstring")
    claims = {r["decl"]: r["payload"] for r in a["facets"]["annotation.claim"]}
    check(claims.get(F + "triple_pos") == {"reference": "Fixture, Theorem 1"}, "A: claim annotation")
    ex = {r["decl"]: r["payload"] for r in a["facets"]["annotation.example_of"]}
    check(ex.get(F + "isSmall_three") == {"target": F + "IsSmall"}, "A: example_of annotation")
    ax = {r["decl"]: r for r in a["facets"]["axioms"]}
    check(ax[F + "triple_pos"]["sorry"] is False, "A: axioms facet")

    if failures:
        for f in failures:
            print(f"FAIL: {f}")
        return 1
    print(f"ok: {len(a['decls'])} nodes in A, {len(b['decls'])} in B; all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
