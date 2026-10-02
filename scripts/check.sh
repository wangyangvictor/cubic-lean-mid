#!/bin/sh
set -eu
repo_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'Lake is not on PATH. Install Lean through elan: https://lean-lang.org/install/' >&2
  exit 1
fi
cd "$repo_dir/formalization/CubicTenVariables"
# This limits Lean's internal worker pool; the Lake script separately limits
# concurrent module compilations (default two, CUBIC_BUILD_JOBS=1..3)
# and reuses one build session.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
lake run boundedCheck
# Rehash independently after the bounded build. Missing or stale artifacts fail
# this check instead of triggering a second, unrestricted compilation pass.
lake --rehash --no-build build CubicTenVariables HessianTheorem11 TranslatedDepthSeven
lake env lean PublicationAudit.lean
