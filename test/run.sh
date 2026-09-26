#!/usr/bin/env bash
# End-to-end test of the extractor on a two-version fixture.
#
# Builds test/fixture (version A), extracts it twice (the dataset must be identical both times),
# overlays test/fixture-b (version B), extracts again, and runs test/check.py on the two datasets:
# it checks the nodes, kinds, edges, facets, and how each hash of the declaration key moves
# between A and B. Last, extracts B again as if `Fixture.Uses` did not build: that module and the
# root, which imports it, must be listed as unavailable, and nothing else may change.
#
# Usage: test/run.sh [KEEP_DIR]   (after `lake build` of the extractor)
#   With KEEP_DIR, the datasets are copied to KEEP_DIR/fixture-a, KEEP_DIR/fixture-b,
#   KEEP_DIR/fixture-b-partial and KEEP_DIR/fixture-b-closure.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
bin="$root/.lake/build/bin/trust-extract"
[ -x "$bin" ] || { echo "build the extractor first: lake build" >&2; exit 1; }

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

cp -r "$here/fixture" "$work/a"
# The fixture is built with the extractor's toolchain and its revision of the annotations package,
# whatever its own files say: the extractor can only read what its own Lean wrote.
cp "$root/lean-toolchain" "$work/a/lean-toolchain"
rev=$(python3 -c "import json, sys; print(next(p['rev'] for p in json.load(open(sys.argv[1]))['packages'] if p['name'] == 'TrustAnnotations'))" "$root/lake-manifest.json")
sed -i "s/^rev = .*/rev = \"$rev\"/" "$work/a/lakefile.toml"
(cd "$work/a" && lake build -q >/dev/null)
(cd "$work/a" && lake env "$bin" extract --root Fixture --out "$work/out-a" --commit A --repo test/fixture)
(cd "$work/a" && lake env "$bin" extract --root Fixture --out "$work/out-a2" --commit A --repo test/fixture)
if ! diff -r "$work/out-a" "$work/out-a2" >/dev/null; then
  echo "FAIL: two extractions of the same commit differ" >&2
  diff -r "$work/out-a" "$work/out-a2" | head -20 >&2
  exit 1
fi
echo "ok: extraction is deterministic"
(cd "$work/a" && lake env "$bin" extract --root Fixture --out "$work/out-a3" --commit A --repo test/fixture --parts 3 --jobs 2)
# meta.json records the number of parts run (--parts 3 on four modules runs two); nothing else may
# differ.
cp -r "$work/out-a" "$work/cmp-1"
cp -r "$work/out-a3" "$work/cmp-3"
python3 - "$work/cmp-1/meta.json" "$work/cmp-3/meta.json" <<'EOF'
import json, sys
one, several = (json.load(open(p)) for p in sys.argv[1:])
assert one["producer"].pop("parts") == 1 and several["producer"].pop("parts") > 1, "producer.parts"
for p, m in zip(sys.argv[1:], (one, several)):
    json.dump(m, open(p, "w"), indent=1)
EOF
if ! diff -r "$work/cmp-1" "$work/cmp-3" >/dev/null; then
  echo "FAIL: extracting in 3 parts gives a different dataset" >&2
  diff -r "$work/cmp-1" "$work/cmp-3" | head -20 >&2
  exit 1
fi
echo "ok: extracting in parts, in parallel, gives the same dataset"

cp -r "$work/a" "$work/b"
cp -r "$here/fixture-b/." "$work/b/"
(cd "$work/b" && lake build -q >/dev/null)
(cd "$work/b" && lake env "$bin" extract --root Fixture --out "$work/out-b" --commit B --repo test/fixture)

python3 "$here/check.py" "$work/out-a" "$work/out-b"

# Check 2: the kernel checks every closure, along both notions, and catches a dropped edge.
(cd "$work/b" && lake env "$bin" check --root Fixture --dataset "$work/out-b" --no-write --strict >/dev/null 2>&1) || {
  echo "FAIL: the kernel check fails on version B" >&2
  (cd "$work/b" && lake env "$bin" check --root Fixture --dataset "$work/out-b" --no-write) >&2; exit 1; }
(cd "$work/b" && lake env "$bin" check --root Fixture --dataset "$work/out-b" --notion term --no-write --strict >/dev/null 2>&1) || {
  echo "FAIL: the kernel check along term fails on version B" >&2; exit 1; }
if (cd "$work/b" && lake env "$bin" check --root Fixture --dataset "$work/out-b" --strict \
      --drop-edge Fixture.double_zero Fixture.double >/dev/null 2>&1); then
  echo "FAIL: the kernel check did not catch a dropped edge" >&2; exit 1
fi
if (cd "$work/b" && lake env "$bin" check --root Fixture --dataset "$work/out-b" --notion term --strict \
      --drop-edge Fixture.one "Fixture.one_pos'" >/dev/null 2>&1); then
  echo "FAIL: the kernel check along term did not catch a dropped proof edge" >&2; exit 1
fi
echo "ok: the kernel checks every closure, and catches a dropped edge"

(cd "$work/b" && lake env "$bin" extract --root Fixture --out "$work/out-b-partial" --commit B --repo test/fixture --skip-module Fixture.Uses)
python3 "$here/check_partial.py" "$work/out-b" "$work/out-b-partial"

# Past the project: the closure along `term`, in one part and in three.
(cd "$work/b" && lake env "$bin" extract --root Fixture --out "$work/out-b-closure" --commit B --repo test/fixture --upstream-closure term)
(cd "$work/b" && lake env "$bin" extract --root Fixture --out "$work/out-b-closure3" --commit B --repo test/fixture --upstream-closure term --parts 3 --jobs 2)
python3 "$here/check_closure.py" "$work/out-b" "$work/out-b-closure"
python3 - "$work/out-b-closure/meta.json" "$work/out-b-closure3/meta.json" <<'EOF2'
import json, sys
for p in sys.argv[1:]:
    m = json.load(open(p)); m["producer"].pop("parts"); json.dump(m, open(p, "w"), indent=1)
EOF2
if ! diff -r "$work/out-b-closure" "$work/out-b-closure3" >/dev/null; then
  echo "FAIL: the closure extracted in 3 parts differs" >&2
  diff -r "$work/out-b-closure" "$work/out-b-closure3" | head -20 >&2
  exit 1
fi
echo "ok: the closure does not depend on the parts"

if [ $# -ge 1 ]; then
  mkdir -p "$1"
  rm -rf "$1/fixture-a" "$1/fixture-b" "$1/fixture-b-partial" "$1/fixture-b-closure"
  cp -r "$work/out-a" "$1/fixture-a"
  cp -r "$work/out-b" "$1/fixture-b"
  cp -r "$work/out-b-partial" "$1/fixture-b-partial"
  cp -r "$work/out-b-closure" "$1/fixture-b-closure"
  echo "kept the datasets in $1"
fi
