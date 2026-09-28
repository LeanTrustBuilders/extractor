#!/usr/bin/env python3
"""Checks that the Lean toolchain in lean-toolchain is the one a release tag names."""
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
ok = True
toolchain = (root / "lean-toolchain").read_text().strip()
if len(sys.argv) > 1 and sys.argv[1] != toolchain.split(":v")[-1]:
    print(f"lean-toolchain is {toolchain}, but the tag is {sys.argv[1]}")
    ok = False
print("ok" if ok else "pins disagree")
sys.exit(0 if ok else 1)
