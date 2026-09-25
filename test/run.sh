#!/usr/bin/env bash
# End-to-end test of the extractor on a two-version fixture.
#
# Builds test/fixture (version A), extracts it twice (the dataset must be identical both times),
# overlays test/fixture-b (version B), extracts again, and runs test/check.py on the two datasets:
# it checks the nodes, kinds, edges, facets, and how each hash of the declaration key moves
# between A and B.
#
# Usage: test/run.sh [KEEP_DIR]   (after `lake build` of the extractor)
#   With KEEP_DIR, the two datasets are copied to KEEP_DIR/fixture-a and KEEP_DIR/fixture-b.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
bin="$root/.lake/build/bin/trust-extract"
[ -x "$bin" ] || { echo "build the extractor first: lake build" >&2; exit 1; }

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

cp -r "$here/fixture" "$work/a"
(cd "$work/a" && lake build -q >/dev/null)
(cd "$work/a" && lake env "$bin" extract --root Fixture --out "$work/out-a" --commit A --repo test/fixture)
(cd "$work/a" && lake env "$bin" extract --root Fixture --out "$work/out-a2" --commit A --repo test/fixture)
if ! diff -r "$work/out-a" "$work/out-a2" >/dev/null; then
  echo "FAIL: two extractions of the same commit differ" >&2
  diff -r "$work/out-a" "$work/out-a2" | head -20 >&2
  exit 1
fi
echo "ok: extraction is deterministic"

cp -r "$work/a" "$work/b"
cp -r "$here/fixture-b/." "$work/b/"
(cd "$work/b" && lake build -q >/dev/null)
(cd "$work/b" && lake env "$bin" extract --root Fixture --out "$work/out-b" --commit B --repo test/fixture)

python3 "$here/check.py" "$work/out-a" "$work/out-b"

if [ $# -ge 1 ]; then
  mkdir -p "$1"
  rm -rf "$1/fixture-a" "$1/fixture-b"
  cp -r "$work/out-a" "$1/fixture-a"
  cp -r "$work/out-b" "$1/fixture-b"
  echo "kept the datasets in $1"
fi
