/*
 * wowii66.c -- checks for Written on the Wall II Conjecture 66 (Graffiti.pc, 2004):
 *
 *     G simple and connected  ==>  f(G) >= 2 * CEIL[ even_mode_min(Gbar) / deg_avg(G) ]
 *
 * f(G)    order of a largest induced forest of G,
 * Gbar    the complement of G,
 * deg_avg the average degree 2m/n.
 *
 * Two readings of even_mode_min are tested (the list defines it as "the most frequently
 * occurring degree that is an even integer", smallest in case of ties):
 *   R0  among the even degrees of Gbar, the most frequent one (smallest if tied);
 *   R2  among the most frequent degrees of Gbar, the smallest even one (undefined if none).
 * Each is tested with CEIL (as printed) and with FLOOR (the definition the list links to the
 * statement).  All arithmetic is exact: x / (2m/n) = x*n / (2m).
 *
 * Usage
 *   wowii66 search  < graphs.g6     connected graphs in graph6 format (n <= 64); prints one
 *                                   summary line per order and every counterexample
 *   wowii66 family  CMAX            the chains H_c, c = 1..CMAX (c <= 300)
 *   wowii66 g10                     the 10-vertex example G_10 of the paper
 *
 * Exit status 0 if every check passed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t M64;
#define BIT(v) (1ULL << (v))
static int pc(M64 x) { return __builtin_popcountll(x); }
static int lo(M64 x) { return __builtin_ctzll(x); }

/* ---------- graph6 ---------- */
static int g6read(const char *s, int *n, M64 *adj)
{
    int N = s[0] - 63;
    if (N < 1 || N > 64) return 0;
    *n = N;
    memset(adj, 0, 64 * sizeof(M64));
    const char *p = s + 1;
    int bit = 5, val = *p - 63;
    for (int j = 1; j < N; j++)
        for (int i = 0; i < j; i++) {
            if (bit < 0) { p++; val = *p - 63; bit = 5; }
            if ((val >> bit) & 1) { adj[i] |= BIT(j); adj[j] |= BIT(i); }
            bit--;
        }
    return 1;
}

static int connected64(int n, const M64 *adj)
{
    M64 seen = 1, fr = 1;
    while (fr) {
        M64 nx = 0;
        for (M64 t = fr; t; t &= t - 1) nx |= adj[lo(t)];
        nx &= ~seen; seen |= nx; fr = nx;
    }
    return seen == (n == 64 ? ~0ULL : BIT(n) - 1);
}

/* ---------- largest induced forest (branch and bound, n <= 64) ---------- */
static int fbest, fn, ford[64];
static const M64 *fadj;

/* would adding v to the induced forest F close a cycle?  yes iff two neighbours of v in F
   lie in the same component of F */
static int closes_cycle(M64 F, int v)
{
    M64 nb = fadj[v] & F;
    if (pc(nb) <= 1) return 0;
    M64 done = 0;
    for (M64 t = nb; t; t &= t - 1) {
        int u = lo(t);
        if (done & BIT(u)) return 1;
        M64 comp = BIT(u), fr = comp;
        while (fr) {
            M64 nx = 0;
            for (M64 s = fr; s; s &= s - 1) nx |= fadj[lo(s)] & F;
            nx &= ~comp; comp |= nx; fr = nx;
        }
        if (pc(comp & nb) > 1) return 1;
        done |= comp;
    }
    return 0;
}

static void frec(int i, M64 F, int kept)
{
    if (kept + (fn - i) <= fbest) return;
    if (i == fn) { fbest = kept; return; }
    int v = ford[i];
    if (!closes_cycle(F, v)) frec(i + 1, F | BIT(v), kept + 1);
    frec(i + 1, F, kept);
}

static int forest_number(int n, const M64 *adj)
{
    fadj = adj; fn = n;
    for (int i = 0; i < n; i++) ford[i] = i;
    for (int i = 0; i < n; i++)          /* low degree first: good forests are found early */
        for (int j = i + 1; j < n; j++)
            if (pc(adj[ford[j]]) < pc(adj[ford[i]])) { int t = ford[i]; ford[i] = ford[j]; ford[j] = t; }
    fbest = 0;
    frec(0, 0, 0);
    return fbest;
}

/* ---------- the right side ---------- */
/* x for reading r (0 = R0, 1 = R2), or -1 if undefined; cdeg = complement degrees */
static int even_mode(const int *cdeg, int n, int r)
{
    static int cnt[4096];
    memset(cnt, 0, sizeof cnt);
    for (int v = 0; v < n; v++) cnt[cdeg[v]]++;
    int best = 0, x = -1;
    if (r == 0) {
        for (int d = 0; d < n; d += 2)
            if (cnt[d] > best) { best = cnt[d]; x = d; }
        return x;
    }
    for (int d = 0; d < n; d++) if (cnt[d] > best) best = cnt[d];
    for (int d = 0; d < n; d += 2) if (cnt[d] == best) return d;
    return -1;
}

/* 2*CEIL(x*n/(2m)) if up, else 2*FLOOR(x*n/(2m)) */
static long rhs_of(long x, long n, long twom, int up)
{
    long num = x * n;
    return 2 * (up ? (num + twom - 1) / twom : num / twom);
}

static const char *RNAME[4] = {"CEIL-R0", "CEIL-R2", "FLOOR-R0", "FLOOR-R2"};

/* ---------- search mode ---------- */
static int search(void)
{
    char line[1024];
    long graphs[65] = {0}, tested[65][4], viol[65][4];
    memset(tested, 0, sizeof tested); memset(viol, 0, sizeof viol);
    int nmax = 0, bad = 0;
    M64 adj[64];
    while (fgets(line, sizeof line, stdin)) {
        int n;
        if (line[0] == '>' || !g6read(line, &n, adj)) continue;
        if (n < 2) continue;
        if (!connected64(n, adj)) { bad = 1; fprintf(stderr, "disconnected input: %s", line); continue; }
        if (n > nmax) nmax = n;
        graphs[n]++;
        int cdeg[64]; long twom = 0;
        for (int v = 0; v < n; v++) { int d = pc(adj[v]); twom += d; cdeg[v] = n - 1 - d; }
        int f = -1;
        for (int r = 0; r < 4; r++) {
            int x = even_mode(cdeg, n, r & 1);
            if (x < 0) continue;
            tested[n][r]++;
            long rhs = rhs_of(x, n, twom, r < 2);
            if (rhs <= 1) continue;                 /* f >= 1 always */
            if (f < 0) f = forest_number(n, adj);
            if (f < rhs) {
                viol[n][r]++;
                line[strcspn(line, "\r\n")] = 0;
                printf("X %s %s f=%d rhs=%ld\n", RNAME[r], line, f, rhs);
            }
        }
    }
    for (int n = 2; n <= nmax; n++) {
        if (!graphs[n]) continue;
        printf("n=%d graphs %ld", n, graphs[n]);
        for (int r = 0; r < 4; r++) printf(" %s %ld/%ld", RNAME[r], viol[n][r], tested[n][r]);
        printf("\n");
    }
    return bad;
}

/* ---------- the chains H_c ---------- */
/* vertex 4i+a is vertex a of block Q_i; bridges join 4i+1 and 4(i+1) */
static int failures = 0;
#define CHECK(cond, ...) do { if (!(cond)) { failures++; printf("FAIL: "); printf(__VA_ARGS__); printf("\n"); } } while (0)

static int Hadj(int c, int u, int v)
{
    if (u == v) return 0;
    if (u / 4 == v / 4) return 1;
    if (u > v) { int t = u; u = v; v = t; }
    return u % 4 == 1 && v == u + 3 && v / 4 < c;     /* 4i+1 -- 4i+4 */
}

static int family(int cmax)
{
    printf("  c    n    m  f-cert  x(R0) x(R2)  rhs:CEIL FLOOR  violated\n");
    for (int c = 1; c <= cmax; c++) {
        int n = 4 * c;
        static int deg[4000], cdeg[4000], dsu[4000];
        long twom = 0;
        for (int u = 0; u < n; u++) {
            deg[u] = 0;
            for (int w = 0; w < n; w++) deg[u] += Hadj(c, u, w);
            twom += deg[u]; cdeg[u] = n - 1 - deg[u];
        }
        /* connectivity */
        for (int u = 0; u < n; u++) dsu[u] = u;
        for (int u = 0; u < n; u++) for (int w = u + 1; w < n; w++) if (Hadj(c, u, w)) {
            int a = u, b = w;
            while (dsu[a] != a) a = dsu[a];
            while (dsu[b] != b) b = dsu[b];
            dsu[a] = b;
        }
        int roots = 0;
        for (int u = 0; u < n; u++) if (dsu[u] == u) roots++;
        CHECK(roots == 1, "H_%d is not connected", c);
        /* closed forms of the paper */
        CHECK(twom == 14L * c - 2, "H_%d: 2m = %ld", c, twom);
        int n3 = 0, n4 = 0;
        for (int u = 0; u < n; u++) { if (deg[u] == 3) n3++; else if (deg[u] == 4) n4++; }
        CHECK(n3 == (c == 1 ? 4 : 2 * c + 2) && n4 == (c == 1 ? 0 : 2 * c - 2) && n3 + n4 == n,
              "H_%d: degree counts %d %d", c, n3, n4);
        /* certificate for f = 2c: the blocks are cliques partitioning V (so an induced forest
           meets each in at most 2 vertices), and {4i+2, 4i+3} induces a forest (a matching) */
        for (int i = 0; i < c; i++)
            for (int a = 0; a < 4; a++) for (int b = a + 1; b < 4; b++)
                CHECK(Hadj(c, 4 * i + a, 4 * i + b), "H_%d: block %d not a clique", c, i);
        int cycle = 0;
        for (int u = 0; u < n; u++) dsu[u] = u;
        for (int u = 0; u < n; u++) for (int w = u + 1; w < n; w++)
            if (u % 4 >= 2 && w % 4 >= 2 && Hadj(c, u, w)) {
                int a = u, b = w;
                while (dsu[a] != a) a = dsu[a];
                while (dsu[b] != b) b = dsu[b];
                if (a == b) cycle = 1; else dsu[a] = b;
            }
        CHECK(!cycle, "H_%d: the set {4i+2,4i+3} is not a forest", c);
        int f = 2 * c;
        if (n <= 24) {                               /* exact value by branch and bound */
            M64 adj[64] = {0};
            for (int u = 0; u < n; u++) for (int w = 0; w < n; w++) if (Hadj(c, u, w)) adj[u] |= BIT(w);
            int fx = forest_number(n, adj);
            CHECK(fx == f, "H_%d: forest number %d != 2c", c, fx);
        }
        int x0 = even_mode(cdeg, n, 0), x2 = even_mode(cdeg, n, 1);
        CHECK(x0 == 4 * c - 4 && x2 == 4 * c - 4, "H_%d: even modes %d %d", c, x0, x2);
        long rc = rhs_of(x0, n, twom, 1), rf = rhs_of(x0, n, twom, 0);
        int vc = f < rc, vf = f < rf;
        CHECK(vc == (c >= 8) && vf == (c >= 14), "H_%d: violation pattern %d %d", c, vc, vf);
        /* the bounds used in the proof: rhs >= 2c+2 for c >= 8 (CEIL) and c >= 14 (FLOOR) */
        if (c >= 8) CHECK(rc >= 2L * c + 2, "H_%d: CEIL bound", c);
        if (c >= 14) CHECK(rf >= 2L * c + 2, "H_%d: FLOOR bound", c);
        if (c <= 20 || c % 50 == 0)
            printf("%3d %4d %4ld %6d %6d %5d %9ld %5ld  %s%s\n", c, n, twom / 2, f, x0, x2, rc, rf,
                   vc ? "CEIL " : "", vf ? "FLOOR" : "");
    }
    printf("family: c = 1..%d, %s\n", cmax, failures ? "FAILED" : "all checks passed");
    return failures != 0;
}

/* ---------- the 10-vertex example ---------- */
static int g10(void)
{
    /* triangle {0,5,6}; K4 {1,7,8,9}; bridge 0-9; pendant vertices 2, 3, 4 at 7, 8, 9 */
    static const int E[][2] = {{0,5},{0,6},{5,6},{1,7},{1,8},{1,9},{7,8},{7,9},{8,9},{0,9},{2,7},{3,8},{4,9}};
    int n = 10; M64 adj[64] = {0};
    for (unsigned k = 0; k < sizeof E / sizeof E[0]; k++) { adj[E[k][0]] |= BIT(E[k][1]); adj[E[k][1]] |= BIT(E[k][0]); }
    char g6[32]; int pos = 1, bit = 5, val = 0;
    g6[0] = n + 63;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if ((adj[i] >> j) & 1) val |= 1 << bit;
        if (--bit < 0) { g6[pos++] = val + 63; val = 0; bit = 5; }
    }
    if (bit != 5) g6[pos++] = val + 63;
    g6[pos] = 0;
    int cdeg[64]; long twom = 0;
    for (int v = 0; v < n; v++) { int d = pc(adj[v]); twom += d; cdeg[v] = n - 1 - d; }
    int f = forest_number(n, adj);
    printf("G_10 = %s  connected %d  m = %ld  f = %d\n", g6, connected64(n, adj), twom / 2, f);
    printf("complement degrees:");
    for (int v = 0; v < n; v++) printf(" %d", cdeg[v]);
    printf("\n");
    CHECK(strcmp(g6, "I?ACJ@PqW") == 0, "G_10 graph6 %s", g6);
    CHECK(connected64(n, adj) && twom == 26 && f == 7, "G_10 basic values");
    for (int r = 0; r < 4; r++) {
        int x = even_mode(cdeg, n, r & 1);
        long rhs = rhs_of(x, n, twom, r < 2);
        printf("%-8s x = %d  rhs = %ld  %s\n", RNAME[r], x, rhs, f < rhs ? "violated" : "holds");
        CHECK(x == 8 && rhs == (r < 2 ? 8 : 6), "G_10 %s", RNAME[r]);
    }
    printf("g10: %s\n", failures ? "FAILED" : "all checks passed");
    return failures != 0;
}

int main(int argc, char **argv)
{
    if (argc >= 2 && !strcmp(argv[1], "search")) return search();
    if (argc >= 2 && !strcmp(argv[1], "family")) {
        int cmax = argc >= 3 ? atoi(argv[2]) : 200;
        if (cmax < 1 || cmax > 300) { fprintf(stderr, "CMAX must be in 1..300\n"); return 2; }
        return family(cmax);
    }
    if (argc >= 2 && !strcmp(argv[1], "g10")) return g10();
    fprintf(stderr, "usage: wowii66 search < graphs.g6 | wowii66 family CMAX | wowii66 g10\n");
    return 2;
}
