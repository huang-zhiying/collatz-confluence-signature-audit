#!/usr/bin/env bash
# Guarded `lake build`.
#
# `.lake/packages` is a junction to a sibling project's package directory, so the
# Mathlib sources and build artefacts under it are shared mutable state.  `lake
# build` trusts lake-manifest.json and will happily check out whatever rev the
# manifest pins — silently compiling against a different Mathlib if the shared
# directory moved.  This wrapper makes that a loud failure instead.
#
# Usage: ./lake-verify.sh [lake build args...]
#   GUESS_MANIFEST=path   check a different manifest (test only)
set -e
cd "$(dirname "$0")"
MANIFEST="${GUESS_MANIFEST:-lake-manifest.json}"
LAKE="${LAKE:-/d/tools/elan/toolchains/stable/bin/lake.exe}"

PIN=$(grep -A4 'leanprover-community/mathlib4' "$MANIFEST" | grep -o '[0-9a-f]\{40\}' | head -1)
[ -n "$PIN" ] || { echo "lake-verify: no mathlib rev in $MANIFEST" >&2; exit 1; }

HAVE=$( cd .lake/packages/mathlib && git rev-parse HEAD 2>/dev/null || echo unknown )
if [ "$PIN" != "$HAVE" ]; then
  echo "lake-verify: mathlib drift — shared checkout is $HAVE, manifest pins $PIN" >&2
  echo "             refusing to build. Re-sync .lake/packages or update the manifest." >&2
  exit 1
fi

exec "$LAKE" build "$@"
