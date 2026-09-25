#!/usr/bin/env python3
"""Checks that the constants the extractor records in meta.json agree with what it is built from:
the semantic_hash revision in lake-manifest.json, and the Lean toolchain in lean-toolchain."""
import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / "lake-manifest.json").read_text())
rev = next(p["rev"] for p in manifest["packages"] if p["name"] == "semantic_hash")
source = (root / "TrustExtractor" / "Extract.lean").read_text()
recorded = re.search(r'def semanticHashRevision : String := "([0-9a-f]+)"', source).group(1)
ok = True
if rev != recorded:
    print(f"semantic_hash: lake-manifest.json has {rev}, Extract.lean records {recorded}")
    ok = False
toolchain = (root / "lean-toolchain").read_text().strip()
if len(sys.argv) > 1 and sys.argv[1] != toolchain.split(":v")[-1]:
    print(f"lean-toolchain is {toolchain}, but the tag is {sys.argv[1]}")
    ok = False
print("ok" if ok else "pins disagree")
sys.exit(0 if ok else 1)
