#!/usr/bin/env bash
# check_axioms.sh — fail if a main theorem depends on sorryAx or on any axiom
# outside Mathlib's standard set: propext, Classical.choice, Quot.sound.
#
# Usage: ./scripts/check_axioms.sh
# Requires: `lake build` to have run first (uses the built olean files).
set -euo pipefail

cd "$(dirname "$0")/.."

ALLOWED="propext Classical.choice Quot.sound"

THEOREMS="
Leancollusion.cournotNash_symmetric
Leancollusion.cournotNash_unique_symmetric
Leancollusion.monopoly_gap
Leancollusion.price_gap
Leancollusion.screen_nash_zero
Leancollusion.screen_monopoly_one
"

fail=0
for thm in $THEOREMS; do
  tmpfile="./.check_axioms_tmp.lean"
  printf 'import Leancollusion\n#print axioms %s\n' "$thm" > "$tmpfile"
  out=$(lake env lean "$tmpfile" 2>&1) || {
    echo "FAIL: could not run #print axioms on $thm"
    echo "$out"
    fail=1
    rm -f "$tmpfile"
    continue
  }
  rm -f "$tmpfile"
  echo "$out"
  if echo "$out" | grep -q "sorryAx"; then
    echo "FAIL: $thm depends on sorryAx"
    fail=1
    continue
  fi
  # Extract the axiom list between [ and ] on the "depends on axioms" line.
  axioms=$(echo "$out" | sed -n 's/.*depends on axioms: \[\(.*\)\].*/\1/p' | tr ',' '\n' | tr -d ' ' | grep -v '^$' || true)
  for ax in $axioms; do
    ok=0
    for a in $ALLOWED; do
      if [ "$ax" = "$a" ]; then ok=1; break; fi
    done
    if [ "$ok" = "0" ]; then
      echo "FAIL: $thm depends on unexpected axiom: $ax"
      fail=1
    fi
  done
done

# Belt and suspenders: no sorry/admit tokens in the library sources.
if grep -rn --include='*.lean' -E '\bsorry\b|\badmit\b' Leancollusion.lean Leancollusion/; then
  echo "FAIL: sorry/admit token found in sources"
  fail=1
fi

if [ "$fail" = "0" ]; then
  echo "OK: all theorems depend only on the standard axioms."
else
  exit 1
fi
