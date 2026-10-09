#!/usr/bin/env bash
# check66.sh -- a fourth, shell-only check (bash integer arithmetic, no other programs):
#   1. G_10 from its edge list: degrees, complement degrees, both even modes, both right sides,
#      and f(G_10) = 7 by testing all 1024 vertex subsets with a union-find forest test;
#   2. H_c for c <= 40 from its edge list: edges, complement degrees, even modes and the
#      violation pattern (CEIL from c = 8, FLOOR from c = 14);
#   3. the arithmetic of Lemma 2.3 for c <= 20000.
# Prints ALL OK and exits 0 if every check passed.
set -u
FAILS=0
check() { if [ "$1" != "$2" ]; then echo "FAIL: $3 (got $1, want $2)"; FAILS=$((FAILS + 1)); fi; }

# even modes of a complement degree list (space separated) -> "R0 R2" (-1 if undefined)
modes() {
  local -a cnt=(); local d top=0 etop=0 r0=-1 r2=-1
  for d in $1; do cnt[d]=$(( ${cnt[d]:-0} + 1 )); done
  for d in "${!cnt[@]}"; do
    (( cnt[d] > top )) && top=${cnt[d]}
    (( d % 2 == 0 && cnt[d] > etop )) && etop=${cnt[d]}
  done
  for d in "${!cnt[@]}"; do            # indices come out in increasing order
    (( d % 2 == 0 && cnt[d] == etop && r0 < 0 )) && r0=$d
    (( d % 2 == 0 && cnt[d] == top && r2 < 0 )) && r2=$d
  done
  echo "$r0 $r2"
}
# 2*CEIL(x*n/(2m)) and 2*FLOOR(x*n/(2m))
rhs_ceil() { echo $(( 2 * (($1 * $2 + $3 - 1) / $3) )); }
rhs_floor() { echo $(( 2 * ($1 * $2 / $3) )); }

# 1. G_10 -----------------------------------------------------------------------------------
E="0-5 0-6 5-6 1-7 1-8 1-9 7-8 7-9 8-9 0-9 2-7 3-8 4-9"
n=10; deg=(0 0 0 0 0 0 0 0 0 0)
for e in $E; do a=${e%-*}; b=${e#*-}; deg[a]=$((deg[a] + 1)); deg[b]=$((deg[b] + 1)); done
twom=0; cd=""; for v in $(seq 0 9); do twom=$((twom + deg[v])); cd="$cd $((n - 1 - deg[v]))"; done
check "$twom" 26 "G_10: 2m"
check "$(echo $cd | tr ' ' '\n' | sort -n | tr '\n' ' ')" "4 5 5 6 6 7 7 8 8 8 " "G_10: complement degrees"
read -r r0 r2 <<< "$(modes "$cd")"
check "$r0 $r2" "8 8" "G_10: even modes"
check "$(rhs_ceil 8 $n $twom) $(rhs_floor 8 $n $twom)" "8 6" "G_10: right sides"
best=0
for mask in $(seq 0 1023); do
  k=0; for v in $(seq 0 9); do (( mask >> v & 1 )) && k=$((k + 1)); done
  (( k <= best )) && continue
  p=(0 1 2 3 4 5 6 7 8 9); acyclic=1
  for e in $E; do
    a=${e%-*}; b=${e#*-}
    (( (mask >> a & 1) && (mask >> b & 1) )) || continue
    while (( p[a] != a )); do a=${p[a]}; done
    while (( p[b] != b )); do b=${p[b]}; done
    if (( a == b )); then acyclic=0; break; fi
    p[a]=$b
  done
  (( acyclic )) && best=$k
done
check "$best" 7 "f(G_10) by all subsets"
echo "G_10: f = $best, 2m = $twom, even modes $r0 $r2, right sides $(rhs_ceil 8 $n $twom) (CEIL) $(rhs_floor 8 $n $twom) (FLOOR)"

# 2. H_c ------------------------------------------------------------------------------------
for c in $(seq 2 40); do
  n=$((4 * c)); declare -a dg=(); for v in $(seq 0 $((n - 1))); do dg[v]=0; done; m=0
  for i in $(seq 0 $((c - 1))); do
    for a in 0 1 2 3; do for b in 0 1 2 3; do
      (( a < b )) && { dg[4*i+a]=$((dg[4*i+a] + 1)); dg[4*i+b]=$((dg[4*i+b] + 1)); m=$((m + 1)); }
    done; done
    (( i + 1 < c )) && { dg[4*i+1]=$((dg[4*i+1] + 1)); dg[4*i+4]=$((dg[4*i+4] + 1)); m=$((m + 1)); }
  done
  check "$m" $((7 * c - 1)) "H_$c: edges"
  cd=""; for v in $(seq 0 $((n - 1))); do cd="$cd $((n - 1 - dg[v]))"; done
  read -r r0 r2 <<< "$(modes "$cd")"
  check "$r0 $r2" "$((4 * c - 4)) $((4 * c - 4))" "H_$c: even modes"
  rc=$(rhs_ceil "$r0" "$n" $((2 * m))); rf=$(rhs_floor "$r0" "$n" $((2 * m)))
  check "$(( rc > 2 * c ))" "$(( c >= 8 ))" "H_$c: CEIL violated iff c >= 8"
  check "$(( rf > 2 * c ))" "$(( c >= 14 ))" "H_$c: FLOOR violated iff c >= 14"
  unset dg
done
echo "H_c, c = 2..40: checked"

# 3. Lemma 2.3 ------------------------------------------------------------------------------
for ((c = 1; c <= 20000; c++)); do
  num=$((8 * c * (c - 1))); den=$((7 * c - 1))
  ce=$(( (num + den - 1) / den )); fl=$(( num / den ))
  (( (ce >= c + 1) == (c >= 8) )) || check "$ce" "?" "ceil pattern at c = $c"
  (( (fl >= c + 1) == (c >= 14) )) || check "$fl" "?" "floor pattern at c = $c"
  if (( c >= 7 )); then (( fl - c >= (c - 7) / 7 )) || check "$fl" "?" "gap at c = $c"; fi
done
echo "Lemma 2.3: c = 1..20000 checked"

if (( FAILS == 0 )); then echo "ALL OK"; else echo "$FAILS FAILURES"; exit 1; fi
