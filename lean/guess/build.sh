#!/usr/bin/env bash
# OFFLINE SHIM — not the canonical build.
#
# The canonical build is `lake exe cache get && lake build`, which needs network
# to fetch Mathlib's dependencies.  This script instead borrows a Mathlib clone
# that is already built on this machine and compiles Guess.lean against its
# oleans.  Because it bypasses Lake's dependency graph, the Mathlib revision is
# NOT checked by anything else — so the first thing it does is check it, against
# the rev recorded in lakefile.toml (single source of truth).
#
# Override MATHLIB_PACKAGES if the clone moves; EXPECT_MATHLIB_REV only for
# testing the guard.
set -e
cd "$(dirname "$0")"

ML="${MATHLIB_PACKAGES:-D:/projects/pvsnp-code/pvsnp-code/.lake/packages}"
MATHLIB_DIR="$ML/mathlib"
EXPECT_REV="${EXPECT_MATHLIB_REV:-$(sed -n 's/^rev = "\([0-9a-f]\{40\}\)".*/\1/p' lakefile.toml | head -1)}"
EXPECT_LEAN="${EXPECT_LEAN_VERSION:-4.32.2}"
LEAN="${LEAN:-D:/tools/elan/toolchains/stable/bin/lean.exe}"

[ -n "$EXPECT_REV" ] || { echo "build.sh: no rev pinned in lakefile.toml" >&2; exit 1; }

actual_rev=$( cd "$MATHLIB_DIR" && git rev-parse HEAD 2>/dev/null || echo unknown )
if [ "$actual_rev" != "$EXPECT_REV" ]; then
  echo "build.sh: mathlib rev drift — have $actual_rev" >&2
  echo "          lakefile.toml pins $EXPECT_REV" >&2
  echo "          refusing to build against an unrecorded Mathlib." >&2
  exit 1
fi

actual_lean=$("$LEAN" --version | sed -n 's/.*version \([0-9][0-9.]*\).*/\1/p')
if [ "$actual_lean" != "$EXPECT_LEAN" ]; then
  echo "build.sh: Lean version drift — have $actual_lean, lean-toolchain pins $EXPECT_LEAN" >&2
  exit 1
fi

export LEAN_PATH="$MATHLIB_DIR/.lake/build/lib/lean;$ML/batteries/.lake/build/lib/lean;$ML/aesop/.lake/build/lib/lean;$ML/Qq/.lake/build/lib/lean;$ML/proofwidgets/.lake/build/lib/lean;$ML/plausible/.lake/build/lib/lean;$ML/importGraph/.lake/build/lib/lean;$ML/LeanSearchClient/.lake/build/lib/lean"
exec "$LEAN" Guess.lean
