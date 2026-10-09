#!/usr/bin/env bash
# run_all.sh -- re-run every check of the counterexamples to WOWII Conjecture 66.
#
#   C, C++  build verification/c/wowii66.c and verification/cpp/wowii66.cpp into build/;
#           check G_10 and the chains H_c (c <= 300) with both programs; run both searches
#           on all connected graphs with 2..9 vertices (FULL=1: 2..10, about an hour on one
#           core), compare the two outputs line by line and with verification/data/.
#           The searches need nauty's geng on PATH (also as nauty-geng) or in $NAUTY.
#   Shell   verification/shell/check66.sh       (bash integer arithmetic only)
#   Python  verification/python/verify66.py
#   Julia   verification/julia/verify66.jl     (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean/C66.lean         (if lean is on PATH; the folder pins v4.34.1)
#           verification/lean/mathlib          (MATHLIB=1 only: lake fetches Mathlib's cache
#                                               and builds the proof for every c)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/wowii66" "$V/c/wowii66.c" || fail "compile wowii66.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/wowii66cpp" "$V/cpp/wowii66.cpp" || fail "compile wowii66.cpp"
"$BUILD/wowii66" g10 > "$BUILD/c_g10.txt" && ok "C: G_10" || fail "C: G_10 (see build/c_g10.txt)"
"$BUILD/wowii66" family 300 > "$BUILD/c_family.txt" && ok "C: H_c for c <= 300" \
  || fail "C: H_c (see build/c_family.txt)"
"$BUILD/wowii66cpp" family 300 > "$BUILD/cpp_family.txt" && ok "C++: H_c for c <= 300" \
  || fail "C++: H_c (see build/cpp_family.txt)"

if [ -n "${NAUTY:-}" ] && [ -x "$NAUTY/geng" ]; then GENG="$NAUTY/geng"
else GENG=$(command -v geng || command -v nauty-geng || true); fi
if [ -z "$GENG" ]; then
  echo "nauty's geng not found: skipping the searches; set NAUTY to its directory"
else
  if [ "${FULL:-0}" = 1 ]; then GMAX=10; else GMAX=9; fi
  graphs() { for n in $(seq 2 "$GMAX"); do "$GENG" -cq "$n"; done; }
  graphs | "$BUILD/wowii66" search > "$BUILD/c_search.txt" || fail "C search"
  graphs | "$BUILD/wowii66cpp" search > "$BUILD/cpp_search.txt" || fail "C++ search"
  if cmp -s "$BUILD/c_search.txt" "$BUILD/cpp_search.txt"; then
    ok "C and C++ searches, connected graphs 2..$GMAX: identical output"
  else fail "C and C++ searches differ (build/c_search.txt, build/cpp_search.txt)"; fi
  DATA="$V/data/connected_2_10.txt"
  got=$(grep '^n=' "$BUILD/c_search.txt")
  want=$(grep '^n=' "$DATA" | head -n $((GMAX - 1)))
  [ "$got" = "$want" ] && ok "per-order counts 2..$GMAX agree with verification/data" \
    || fail "per-order counts differ from verification/data"
  if [ "$GMAX" = 10 ]; then
    if diff -q <(grep '^X' "$BUILD/c_search.txt" | sort) <(grep '^X' "$DATA" | sort) > /dev/null; then
      ok "the 12 counterexample lines agree with verification/data"
    else fail "counterexample lines differ from verification/data"; fi
  fi
fi

echo "== Shell"
bash "$V/shell/check66.sh" > "$BUILD/sh66.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh66.txt" \
  && ok "check66.sh" || fail "check66.sh (see build/sh66.txt)"

echo "== Python"
python3 "$V/python/verify66.py" > "$BUILD/py66.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py66.txt" \
  && ok "verify66.py" || fail "verify66.py (see build/py66.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify66.jl" > "$BUILD/jl66.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl66.txt" \
    && ok "verify66.jl" || fail "verify66.jl (see build/jl66.txt)"
fi

echo "== Lean"
if ! command -v lean > /dev/null; then echo "lean not found: skipping (install elan)"; else
  out=$(cd "$V/lean" && lean C66.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean66.txt"
  if [ $st -eq 0 ] && ! grep -q "error" <<< "$out" \
       && grep -q "'conjecture66_false' depends on axioms: \[propext\]" <<< "$out"; then
    ok "C66.lean (kernel-checked, axioms: propext)"
  else fail "C66.lean (see build/lean66.txt)"; fi
  if [ "${MATHLIB:-0}" = 1 ]; then
    out=$(cd "$V/lean/mathlib" && lake exe cache get > /dev/null && lake build 2>&1); st=$?
    echo "$out" > "$BUILD/lean66_mathlib.txt"
    n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out")
    if [ $st -eq 0 ] && [ "$n" = 4 ] && ! grep -q "sorryAx\|error" <<< "$out"; then
      ok "mathlib/C66Family.lean (H_c for every c; standard axioms only)"
    else fail "mathlib/C66Family.lean (see build/lean66_mathlib.txt)"; fi
  else echo "Mathlib proof skipped (set MATHLIB=1)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
