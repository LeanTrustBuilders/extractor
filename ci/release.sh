#!/usr/bin/env bash
# The extractor's releases, as the actions and other workflows use them. A release is tagged
# v<extractor version>-lean-v<toolchain> (the first ones were tagged v<toolchain>), and carries
# trust-extract-linux-x86_64.tar.gz: trust-extract, and scripts/examples.py.
#
#   release.sh toolchains              the Lean versions some release supports, one per line
#   release.sh tag VERSION             the newest release for Lean VERSION (4.34.0, 4.35.0-rc2)
#   release.sh install VERSION DIR     unpacks that release into DIR/trust-extract; prints its tag
#
# VERSION may also be a lean-toolchain file. Needs gh, authenticated (GH_TOKEN).
set -euo pipefail
REPO=${TRUST_EXTRACT_REPO:-LeanTrustBuilders/extractor}

version_of() {
  if [ -f "$1" ]; then sed 's/.*:v//' "$1" | tr -d '[:space:]'; else echo "${1#v}"; fi
}

tags() {
  gh release list -R "$REPO" --limit 200 --json tagName,createdAt \
    --jq 'sort_by(.createdAt) | .[].tagName'
}

case "${1:-}" in
  toolchains)
    tags | sed -E 's/^v[0-9.]+-lean-//; s/^v//' | sort -u ;;
  tag)
    v=$(version_of "$2")
    tags | grep -E "^(v[0-9.]+-lean-)?v${v//./\\.}$" | tail -1 || true ;;
  install)
    v=$(version_of "$2")
    tag=$("$0" tag "$v")
    [ -n "$tag" ] || { echo "::error::LeanTrustBuilders/extractor has no release for Lean v$v" >&2; exit 1; }
    mkdir -p "$3"
    gh release download "$tag" -R "$REPO" -p trust-extract-linux-x86_64.tar.gz -D "$3" --clobber
    tar -xzf "$3/trust-extract-linux-x86_64.tar.gz" -C "$3"
    rm "$3/trust-extract-linux-x86_64.tar.gz"
    echo "$tag" ;;
  *)
    sed -n '2,11p' "$0" >&2; exit 2 ;;
esac
