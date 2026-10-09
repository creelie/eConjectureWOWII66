// wowii66.cpp -- an independent re-implementation of the checks in ../c/wowii66.c for
// Written on the Wall II Conjecture 66:  f(G) >= 2*CEIL[even_mode_min(Gbar)/deg_avg(G)].
//
// It shares no code with the C program and computes the forest number differently: the right
// side is evaluated first; a greedy induced forest gives a lower bound for f, and only when
// that bound is below the right side is f computed exactly, by testing every vertex subset
// with a union-find acyclicity test.  The output of "search" is identical, line for line, to
// that of the C program, so the two can be compared with diff.
//
//   wowii66cpp search < graphs.g6
//   wowii66cpp family CMAX          (CMAX <= 300; exact f by all subsets for c <= 5)
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <string>
#include <vector>

using Graph = std::vector<std::vector<int>>;   // adjacency lists

static Graph parse_graph6(const std::string &s)
{
    int n = s.at(0) - 63;
    Graph g(n);
    std::size_t pos = 1;
    int bit = 5;
    for (int j = 1; j < n; ++j)
        for (int i = 0; i < j; ++i) {
            if (bit < 0) { ++pos; bit = 5; }
            if (((s.at(pos) - 63) >> bit) & 1) { g[i].push_back(j); g[j].push_back(i); }
            --bit;
        }
    return g;
}

struct DSU {
    std::vector<int> p;
    explicit DSU(int n) : p(n) { std::iota(p.begin(), p.end(), 0); }
    int find(int x) { while (p[x] != x) x = p[x] = p[p[x]]; return x; }
    bool unite(int a, int b) { a = find(a); b = find(b); if (a == b) return false; p[a] = b; return true; }
};

static bool is_connected(const Graph &g)
{
    DSU d(static_cast<int>(g.size()));
    for (std::size_t u = 0; u < g.size(); ++u) for (int w : g[u]) d.unite(static_cast<int>(u), w);
    for (std::size_t u = 0; u < g.size(); ++u) if (d.find(static_cast<int>(u)) != d.find(0)) return false;
    return true;
}

// does the vertex set `in` induce a forest?
static bool induces_forest(const Graph &g, const std::vector<char> &in)
{
    DSU d(static_cast<int>(g.size()));
    for (std::size_t u = 0; u < g.size(); ++u) if (in[u])
        for (int w : g[u]) if (static_cast<int>(u) < w && in[w])
            if (!d.unite(static_cast<int>(u), w)) return false;
    return true;
}

static int greedy_forest(const Graph &g)
{
    int n = static_cast<int>(g.size());
    std::vector<int> order(n);
    std::iota(order.begin(), order.end(), 0);
    std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return g[a].size() < g[b].size(); });
    std::vector<char> in(n, 0);
    int size = 0;
    for (int v : order) {
        in[v] = 1;
        if (induces_forest(g, in)) ++size; else in[v] = 0;
    }
    return size;
}

static int exact_forest(const Graph &g)          // all 2^n subsets (n <= 24)
{
    int n = static_cast<int>(g.size()), best = 0;
    std::vector<char> in(n);
    for (std::uint32_t mask = 0; mask < (1u << n); ++mask) {
        int k = __builtin_popcount(mask);
        if (k <= best) continue;
        for (int v = 0; v < n; ++v) in[v] = (mask >> v) & 1;
        if (induces_forest(g, in)) best = k;
    }
    return best;
}

// even mode of the complement degree sequence: reading 0 = most frequent even value,
// reading 1 = smallest even value among the most frequent values; -1 if undefined
static int even_mode(const std::vector<int> &cdeg, int reading)
{
    std::map<int, int> count;
    for (int d : cdeg) ++count[d];
    if (reading == 0) {
        int best = 0, x = -1;
        for (auto [d, k] : count) if (d % 2 == 0 && k > best) { best = k; x = d; }
        return x;
    }
    int top = 0;
    for (auto [d, k] : count) top = std::max(top, k);
    for (auto [d, k] : count) if (k == top && d % 2 == 0) return d;
    return -1;
}

// 2*CEIL or 2*FLOOR of x / (2m/n) = x*n / (2m)
static long long rhs_of(long long x, long long n, long long twom, bool ceil_reading)
{
    long long num = x * n;
    long long q = num / twom;
    if (ceil_reading && q * twom != num) ++q;
    return 2 * q;
}

static const char *NAME[4] = {"CEIL-R0", "CEIL-R2", "FLOOR-R0", "FLOOR-R2"};

static int search()
{
    std::map<int, long> graphs;
    std::map<int, std::vector<long>> tested, viol;
    std::string line;
    int status = 0;
    while (std::getline(std::cin, line)) {
        while (!line.empty() && (line.back() == '\r' || line.back() == '\n')) line.pop_back();
        if (line.empty() || line[0] == '>') continue;
        Graph g = parse_graph6(line);
        int n = static_cast<int>(g.size());
        if (n < 2) continue;
        if (!is_connected(g)) { std::cerr << "disconnected input: " << line << "\n"; status = 1; continue; }
        ++graphs[n];
        tested[n].resize(4); viol[n].resize(4);
        long long twom = 0;
        std::vector<int> cdeg(n);
        for (int v = 0; v < n; ++v) { twom += static_cast<long long>(g[v].size()); cdeg[v] = n - 1 - static_cast<int>(g[v].size()); }
        int f = -1, lower = -1;
        for (int r = 0; r < 4; ++r) {
            int x = even_mode(cdeg, r & 1);
            if (x < 0) continue;
            ++tested[n][r];
            long long rhs = rhs_of(x, n, twom, r < 2);
            if (rhs <= 1) continue;
            if (lower < 0) lower = greedy_forest(g);
            if (lower >= rhs) continue;
            if (f < 0) f = exact_forest(g);
            if (f < rhs) {
                ++viol[n][r];
                std::cout << "X " << NAME[r] << " " << line << " f=" << f << " rhs=" << rhs << "\n";
            }
        }
    }
    for (auto [n, k] : graphs) {
        std::cout << "n=" << n << " graphs " << k;
        for (int r = 0; r < 4; ++r) std::cout << " " << NAME[r] << " " << viol[n][r] << "/" << tested[n][r];
        std::cout << "\n";
    }
    return status;
}

// H_c: blocks {4i,...,4i+3} are copies of K4; the bridges are 4i+1 -- 4(i+1)
static Graph chain(int c)
{
    Graph g(4 * c);
    auto add = [&](int a, int b) { g[a].push_back(b); g[b].push_back(a); };
    for (int i = 0; i < c; ++i) {
        for (int a = 0; a < 4; ++a) for (int b = a + 1; b < 4; ++b) add(4 * i + a, 4 * i + b);
        if (i + 1 < c) add(4 * i + 1, 4 * (i + 1));
    }
    return g;
}

static int family(int cmax)
{
    int fails = 0;
    auto check = [&](bool ok, const std::string &what) { if (!ok) { ++fails; std::cout << "FAIL: " << what << "\n"; } };
    for (int c = 1; c <= cmax; ++c) {
        Graph g = chain(c);
        int n = 4 * c;
        long long twom = 0;
        std::vector<int> cdeg(n);
        for (int v = 0; v < n; ++v) { twom += static_cast<long long>(g[v].size()); cdeg[v] = n - 1 - static_cast<int>(g[v].size()); }
        std::string tag = "H_" + std::to_string(c);
        check(is_connected(g), tag + " connected");
        check(twom == 14LL * c - 2, tag + " edge count");
        // f <= 2c: each block is a clique (3 of its vertices would form a triangle);
        // f >= 2c: the vertices 4i+2, 4i+3 induce a matching
        std::vector<char> in(n, 0);
        for (int i = 0; i < c; ++i) {
            for (int a = 0; a < 4; ++a)
                for (int b = a + 1; b < 4; ++b) {
                    const auto &nb = g[4 * i + a];
                    check(std::find(nb.begin(), nb.end(), 4 * i + b) != nb.end(), tag + " block clique");
                }
            in[4 * i + 2] = in[4 * i + 3] = 1;
        }
        check(induces_forest(g, in), tag + " lower-bound forest");
        if (c <= 5) check(exact_forest(g) == 2 * c, tag + " exact forest number");
        int x0 = even_mode(cdeg, 0), x2 = even_mode(cdeg, 1);
        check(x0 == 4 * c - 4 && x2 == 4 * c - 4, tag + " even mode");
        long long rc = rhs_of(x0, n, twom, true), rf = rhs_of(x0, n, twom, false);
        check((2 * c < rc) == (c >= 8), tag + " CEIL violation pattern");
        check((2 * c < rf) == (c >= 14), tag + " FLOOR violation pattern");
    }
    std::cout << "family: c = 1.." << cmax << ", " << (fails ? "FAILED" : "all checks passed") << "\n";
    return fails != 0;
}

int main(int argc, char **argv)
{
    std::ios::sync_with_stdio(false);
    std::string mode = argc >= 2 ? argv[1] : "";
    if (mode == "search") return search();
    if (mode == "family") {
        int cmax = argc >= 3 ? std::stoi(argv[2]) : 200;
        if (cmax < 1 || cmax > 300) { std::cerr << "CMAX must be in 1..300\n"; return 2; }
        return family(cmax);
    }
    std::cerr << "usage: wowii66cpp search < graphs.g6 | wowii66cpp family CMAX\n";
    return 2;
}
