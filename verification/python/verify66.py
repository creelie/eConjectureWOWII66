#!/usr/bin/env python3
"""verify66.py -- independent checks, in exact arithmetic, of the claims of the paper on
Written on the Wall II Conjecture 66:

    G simple and connected  ==>  f(G) >= 2 * CEIL[ even_mode_min(Gbar) / deg_avg(G) ].

Checks
  1. G_10 (graph6 I?ACJ@PqW): every quantity, with f by testing all 1024 vertex subsets.
  2. The seven 10-vertex counterexamples listed in ../data/connected_2_10.txt: f by all
     subsets, the four readings, and pairwise non-isomorphism (colour refinement).
  3. Every labelled graph on 2..6 vertices (no nauty involved): no counterexample under any
     of the four readings.
  4. H_c for c <= 60: degrees, edges, both even modes and both right sides from the edge list;
     f(H_c) = 2c from the clique partition and an explicit forest, and by testing all
     subsets for c <= 4.
  5. The inequalities of Lemma 3.2 for c <= 100000.
Prints ALL OK at the end if every check passed.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
import math
import os
import sys

FAIL = []


def check(ok, what):
    if not ok:
        FAIL.append(what)
        print("FAIL:", what)


def graph6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> k) & 1 for k in range(5, -1, -1))
    adj = [set() for _ in range(n)]
    k = 0
    for j in range(1, n):
        for i in range(j):
            if bits[k]:
                adj[i].add(j)
                adj[j].add(i)
            k += 1
    return adj


def connected(adj):
    seen, stack = {0}, [0]
    while stack:
        u = stack.pop()
        for w in adj[u]:
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == len(adj)


def is_forest(adj, S):
    """S induces a forest iff (number of edges) = |S| - (number of components)."""
    S = set(S)
    edges = sum(1 for u in S for w in adj[u] if w in S) // 2
    comps, seen = 0, set()
    for s in S:
        if s in seen:
            continue
        comps += 1
        seen.add(s)
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if w in S and w not in seen:
                    seen.add(w)
                    stack.append(w)
    return edges == len(S) - comps


def forest_number(adj):
    n = len(adj)
    for k in range(n, 0, -1):
        if any(is_forest(adj, S) for S in combinations(range(n), k)):
            return k
    return 0


def even_modes(adj):
    """(R0, R2): R0 = most frequent even degree of the complement (smallest if tied);
    R2 = smallest even value among the most frequent complement degrees; None if undefined."""
    n = len(adj)
    cnt = Counter(n - 1 - len(a) for a in adj)
    ev = {d: k for d, k in cnt.items() if d % 2 == 0}
    r0 = min(d for d in ev if ev[d] == max(ev.values())) if ev else None
    top = max(cnt.values())
    r2s = [d for d in cnt if cnt[d] == top and d % 2 == 0]
    return r0, (min(r2s) if r2s else None)


def right_sides(adj):
    """dict reading -> right side, with deg_avg = 2m/n as an exact fraction"""
    n = len(adj)
    davg = Fraction(sum(len(a) for a in adj), n)
    out = {}
    for name, x in zip(("R0", "R2"), even_modes(adj)):
        if x is None or davg == 0:
            continue
        q = Fraction(x) / davg
        out["CEIL-" + name] = 2 * math.ceil(q)
        out["FLOOR-" + name] = 2 * math.floor(q)
    return out


def wl_hash(adj, rounds=6):
    col = [len(a) for a in adj]
    for _ in range(rounds):
        sig = [(col[v], tuple(sorted(col[w] for w in adj[v]))) for v in range(len(adj))]
        table = {s: i for i, s in enumerate(sorted(set(sig)))}
        col = [table[s] for s in sig]
    return tuple(sorted(Counter(sig).items()))


# 1. G_10 ------------------------------------------------------------------------------
E10 = [(0, 5), (0, 6), (5, 6), (1, 7), (1, 8), (1, 9), (7, 8), (7, 9), (8, 9), (0, 9), (2, 7), (3, 8), (4, 9)]
g10 = [set() for _ in range(10)]
for a, b in E10:
    g10[a].add(b)
    g10[b].add(a)
check(g10 == graph6("I?ACJ@PqW"), "G_10 edge list matches I?ACJ@PqW")
check(connected(g10), "G_10 connected")
f10 = forest_number(g10)
check(f10 == 7, "f(G_10) = 7")
check(not any(is_forest(g10, S) for S in combinations(range(10), 8)), "no induced forest on 8 vertices")
check(sorted(9 - len(a) for a in g10) == [4, 5, 5, 6, 6, 7, 7, 8, 8, 8], "complement degrees of G_10")
check(Fraction(sum(len(a) for a in g10), 10) == Fraction(13, 5), "deg_avg(G_10) = 13/5")
rs = right_sides(g10)
check(rs == {"CEIL-R0": 8, "FLOOR-R0": 6, "CEIL-R2": 8, "FLOOR-R2": 6}, "right sides of G_10: %s" % rs)
print("G_10: f = %d, right sides %s" % (f10, rs))

# 2. the 10-vertex counterexamples ---------------------------------------------------------
here = os.path.dirname(os.path.abspath(__file__))
data = os.path.join(here, "..", "data", "connected_2_10.txt")
listed = {}
with open(data) as fh:
    for line in fh:
        if line.startswith("X "):
            _, reading, g6, f, rhs = line.split()
            listed.setdefault(g6, set()).add(reading)
check(len(listed) == 7, "seven graphs listed")
for g6, readings in sorted(listed.items()):
    adj = graph6(g6)
    f = forest_number(adj)
    rs = right_sides(adj)
    viol = {r for r, v in rs.items() if f < v}
    check(len(adj) == 10 and connected(adj), g6 + " connected on 10 vertices")
    check(viol == readings, "%s violated readings %s, listed %s" % (g6, sorted(viol), sorted(readings)))
    print("%s  f = %d  m = %d  violated %s" % (g6, f, sum(len(a) for a in adj) // 2, " ".join(sorted(viol))))
check(sum("CEIL-R0" in r for r in listed.values()) == 7, "7 counterexamples for CEIL-R0")
check(sum("CEIL-R2" in r for r in listed.values()) == 5, "5 counterexamples for CEIL-R2")
check(not any(r & {"FLOOR-R0", "FLOOR-R2"} for r in listed.values()), "none for FLOOR")
hashes = [wl_hash(graph6(g)) for g in listed]
check(len(set(hashes)) == len(hashes), "the listed graphs are pairwise non-isomorphic")

# 3. every labelled graph on 2..6 vertices --------------------------------------------------
for n in range(2, 7):
    pairs = list(combinations(range(n), 2))
    count = bad = 0
    for mask in range(1 << len(pairs)):
        adj = [set() for _ in range(n)]
        for k, (a, b) in enumerate(pairs):
            if mask >> k & 1:
                adj[a].add(b)
                adj[b].add(a)
        if not connected(adj):
            continue
        count += 1
        rs = right_sides(adj)
        if rs and max(rs.values()) > 1 and forest_number(adj) < max(rs.values()):
            bad += 1
    check(bad == 0, "labelled graphs on %d vertices" % n)
    print("n = %d: %d connected labelled graphs, %d counterexamples" % (n, count, bad))


# 4. the chains H_c -------------------------------------------------------------------------
def chain(c):
    adj = [set() for _ in range(4 * c)]
    for i in range(c):
        for a, b in combinations(range(4), 2):
            adj[4 * i + a].add(4 * i + b)
            adj[4 * i + b].add(4 * i + a)
        if i + 1 < c:
            adj[4 * i + 1].add(4 * i + 4)
            adj[4 * i + 4].add(4 * i + 1)
    return adj


for c in range(1, 61):
    H = chain(c)
    n = 4 * c
    tag = "H_%d" % c
    check(connected(H), tag + " connected")
    check(sum(len(a) for a in H) == 14 * c - 2, tag + " has 7c-1 edges")
    degs = Counter(len(a) for a in H)
    check(degs == (Counter({3: 4}) if c == 1 else Counter({3: 2 * c + 2, 4: 2 * c - 2})), tag + " degrees")
    blocks = [range(4 * i, 4 * i + 4) for i in range(c)]
    check(all(b in H[a] for blk in blocks for a, b in combinations(blk, 2)), tag + " blocks are cliques")
    check(is_forest(H, [v for v in range(n) if v % 4 >= 2]), tag + " explicit forest of order 2c")
    if c <= 4:
        check(forest_number(H) == 2 * c, tag + " f = 2c by all subsets")
    r0, r2 = even_modes(H)
    check(r0 == r2 == 4 * c - 4, tag + " even modes")
    rs = right_sides(H)
    check((rs["CEIL-R0"] > 2 * c) == (c >= 8) and (rs["FLOOR-R0"] > 2 * c) == (c >= 14), tag + " violation pattern")
    check(rs["CEIL-R0"] == rs["CEIL-R2"] and rs["FLOOR-R0"] == rs["FLOOR-R2"], tag + " readings agree")
    q = Fraction(8 * c * (c - 1), 7 * c - 1)
    check(Fraction(4 * c - 4) / Fraction(14 * c - 2, 4 * c) == q, tag + " ratio 8c(c-1)/(7c-1)")
print("H_c, c = 1..60: checked")

# 5. Lemma 3.2 -----------------------------------------------------------------------------
for c in range(1, 100001):
    num, den = 8 * c * (c - 1), 7 * c - 1
    ceil_q, floor_q = -(-num // den), num // den
    check((ceil_q >= c + 1) == (c >= 8), "ceil pattern at c = %d" % c)
    check((floor_q >= c + 1) == (c >= 14), "floor pattern at c = %d" % c)
    if c >= 7:   # the gaps of Lemma 3.2: at least 2*floor((c-7)/7) and 2*ceil((c-7)/7)
        check(2 * floor_q - 2 * c >= 2 * ((c - 7) // 7), "floor gap at c = %d" % c)
        check(2 * ceil_q - 2 * c >= 2 * (-(-(c - 7) // 7)), "ceil gap at c = %d" % c)
print("Lemma 3.2: c = 1..100000 checked")

if FAIL:
    print("%d FAILURES" % len(FAIL))
    sys.exit(1)
print("ALL OK")
