#!/usr/bin/env bash
# Moves a LeanTrustBuilders Lean repository to the Lean toolchain Mathlib's master is on, and
# releases it. Run from a checkout of main with its history, by the follow-toolchain action.
#
# When Mathlib is on another toolchain than main, and the repositories this one requires (DEPS)
# have moved already:
#   1. the branch lean-v<old toolchain> keeps main's code for the old toolchain, its requirements
#      pinned to their own lean-v<old toolchain> branches;
#   2. main moves to the new toolchain, is built and tested, and pushed;
#   3. the release: a tag v<toolchain> with a GitHub release (RELEASE=tag), or for the extractor a tag
#      v<version>-lean-v<toolchain> and its Release workflow (RELEASE=extractor).
# A build that fails opens the issue "Lean <toolchain>: the build fails" and nothing is pushed; while
# that issue is open, later runs wait.
#
# Environment: DEPS (repository names, space-separated), BUILD (lake targets), TEST (a command run
# after the build), RELEASE (tag | extractor), GH_TOKEN; DRY_RUN=1 changes nothing outside the
# checkout and says what it would push.
set -euo pipefail
ORG=LeanTrustBuilders
MATHLIB=https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain

act() { if [ -n "${DRY_RUN:-}" ]; then echo "would run: $*"; else "$@"; fi; }

target_tc=$(curl -sSf "$MATHLIB" | tr -d '[:space:]')
current_tc=$(tr -d '[:space:]' < lean-toolchain)
target=${target_tc#*:v} current=${current_tc#*:v}
if [ "$target_tc" = "$current_tc" ]; then
  echo "main is on $current_tc, as Mathlib's master is"; exit 0
fi
case "$target_tc" in
  leanprover/lean4:v4.*) ;;
  *) echo "::warning::Mathlib's master is on $target_tc, which is not a Lean release: not followed"; exit 0 ;;
esac
echo "Mathlib's master is on $target_tc; main is on $current_tc"
old_branch="lean-v$current"
title="Lean $target: the build fails"

if [ "$(gh issue list --state open --search "\"$title\" in:title" --json title --jq ".[] | select(.title == \"$title\") | .title")" ]; then
  echo "waiting: the issue \"$title\" is open"; exit 0
fi
for dep in ${DEPS:-}; do
  dep_tc=$(curl -sSf "https://raw.githubusercontent.com/$ORG/$dep/main/lean-toolchain" | tr -d '[:space:]')
  if [ "$dep_tc" != "$target_tc" ] ||
      ! git ls-remote --exit-code --heads "https://github.com/$ORG/$dep" "$old_branch" > /dev/null; then
    echo "waiting for $ORG/$dep to move first (its main is on $dep_tc)"; exit 0
  fi
done

if ! command -v lake > /dev/null; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi
git config user.name "github-actions[bot]"
git config user.email "41898282+github-actions[bot]@users.noreply.github.com"

# Requirements among our repositories, pinned to a branch of theirs (`rev`), in lakefile.toml.
pin() {
  python3 - "$1" <<'EOF'
import re, sys
text = open("lakefile.toml").read()
blocks = re.split(r"(?m)^(?=\[\[)", text)
def pinned(block):
    if "github.com/LeanTrustBuilders/" not in block:
        return block
    return re.sub(r'(?m)^rev\s*=\s*".*"$', f'rev = "{sys.argv[1]}"', block)
open("lakefile.toml", "w").write("".join(pinned(b) for b in blocks))
EOF
}

# The build and the tests, the log kept for the issue.
check() {
  { lake build ${BUILD:-} && { [ -z "${TEST:-}" ] || bash -c "$TEST"; }; } > "$RUNNER_TEMP_DIR/build.log" 2>&1
}
RUNNER_TEMP_DIR=${RUNNER_TEMP:-$(mktemp -d)}

# 1. The old toolchain's branch.
if git ls-remote --exit-code --heads origin "$old_branch" > /dev/null; then
  echo "$old_branch exists"
else
  git switch -q -c "$old_branch"
  if [ -n "${DEPS:-}" ]; then
    pin "$old_branch"
    lake update
    echo "$current_tc" > lean-toolchain   # lake update may have set a requirement's
    if ! check; then
      tail -40 "$RUNNER_TEMP_DIR/build.log"
      echo "::error::$old_branch does not build with its requirements' $old_branch branches"; exit 1
    fi
    git commit -q -am "$old_branch: main's code for Lean $current, requirements on their $old_branch"
  fi
  act git push -q origin "HEAD:refs/heads/$old_branch"
  echo "kept Lean $current on $old_branch"
  git switch -q main
fi

# 2. main on the new toolchain.
echo "$target_tc" > lean-toolchain
if [ -n "${DEPS:-}" ]; then
  lake update
  echo "$target_tc" > lean-toolchain
fi
if ! check; then
  tail -60 "$RUNNER_TEMP_DIR/build.log"
  body=$(printf 'Mathlib has moved to `%s`. On it, `lake build %s`%s fails (from the [run](%s)):\n\n```text\n%s\n```\n\nFix main, then close this issue: the next run moves main to Lean %s and releases it. Or move main by hand.' \
    "$target_tc" "${BUILD:-}" "${TEST:+ followed by \`$TEST\`}" \
    "${GITHUB_SERVER_URL:-https://github.com}/${GITHUB_REPOSITORY:-}/actions/runs/${GITHUB_RUN_ID:-}" \
    "$(tail -60 "$RUNNER_TEMP_DIR/build.log")" "$target")
  act gh label create toolchain --color fbca04 --description "Following Lean toolchains" --force
  act gh issue create --title "$title" --label toolchain --body "$body"
  echo "::error::$title"; exit 1
fi
git commit -q -am "Lean $target, as Mathlib's master"
act git push -q origin HEAD:main
echo "main is on Lean $target"

# 3. The release.
if [ "${RELEASE:-tag}" = extractor ]; then
  version=$(sed -n 's/^def extractorVersion : String := "\(.*\)"$/\1/p' TrustExtractor/Extract.lean)
  tag="v$version-lean-v$target"
else
  tag="v$target"
fi
if git ls-remote --exit-code --tags origin "refs/tags/$tag" > /dev/null; then
  echo "$tag exists: no new release"; exit 0
fi
act git tag "$tag"
act git push -q origin "refs/tags/$tag"
if [ "${RELEASE:-tag}" = extractor ]; then
  # A tag pushed with the workflow's token starts no workflow: start the release by hand.
  act gh workflow run release.yml --ref "$tag"
else
  act gh release create "$tag" --title "Lean $target" --notes "${GITHUB_REPOSITORY:-$(basename "$(pwd)")} for Lean $target, as Mathlib's master."
fi
echo "released $tag"
