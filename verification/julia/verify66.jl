# verify66.jl -- checks, in exact (Rational) arithmetic, of the claims of the paper on
# Written on the Wall II Conjecture 66:  f(G) >= 2*CEIL[even_mode_min(Gbar)/deg_avg(G)].
#
#   1. G_10 and the seven 10-vertex counterexamples of ../data/connected_2_10.txt:
#      f by testing all vertex subsets, all four readings of the right side.
#   2. H_c for c <= 5: f(H_c) = 2c by testing all 2^(4c) vertex subsets.
#   3. H_c for c <= 300: degrees, edges, even modes and right sides from the adjacency
#      matrix; the clique-partition bound and an explicit forest of order 2c.
# Prints ALL OK at the end if every check passed.

const FAILS = String[]
check(ok, what) = ok || (push!(FAILS, what); println("FAIL: ", what))

function graph6(s::AbstractString)
    n = Int(s[1]) - 63
    bits = Int[]
    for ch in s[2:end], k in 5:-1:0
        push!(bits, ((Int(ch) - 63) >> k) & 1)
    end
    A = falses(n, n)
    k = 1
    for j in 2:n, i in 1:j-1
        if bits[k] == 1
            A[i, j] = A[j, i] = true
        end
        k += 1
    end
    return A
end

function connected(A)
    n = size(A, 1); seen = falses(n); seen[1] = true; stack = [1]
    while !isempty(stack)
        u = pop!(stack)
        for w in 1:n
            if A[u, w] && !seen[w]
                seen[w] = true; push!(stack, w)
            end
        end
    end
    return all(seen)
end

# does the vertex set encoded by `mask` (bit v-1 for vertex v) induce a forest?
function forest_mask(A, mask::Int)
    n = size(A, 1); parent = collect(1:n)
    root(x) = (while parent[x] != x; x = parent[x]; end; x)
    for u in 1:n, w in u+1:n
        if (mask >> (u - 1)) & 1 == 1 && (mask >> (w - 1)) & 1 == 1 && A[u, w]
            a, b = root(u), root(w)
            a == b && return false
            parent[a] = b
        end
    end
    return true
end

function forest_number(A)
    n = size(A, 1); best = 0
    for mask in 0:(1 << n) - 1
        k = count_ones(mask)
        k > best && forest_mask(A, mask) && (best = k)
    end
    return best
end

# (R0, R2) even modes of the complement; `nothing` if undefined
function even_modes(A)
    n = size(A, 1)
    cdeg = [n - 1 - count(A[v, :]) for v in 1:n]
    cnt = Dict{Int,Int}()
    for d in cdeg; cnt[d] = get(cnt, d, 0) + 1; end
    ev = [(d, k) for (d, k) in cnt if iseven(d)]
    r0 = isempty(ev) ? nothing : minimum(d for (d, k) in ev if k == maximum(last.(ev)))
    top = maximum(values(cnt))
    r2s = [d for (d, k) in cnt if k == top && iseven(d)]
    return r0, isempty(r2s) ? nothing : minimum(r2s)
end

function right_sides(A)
    n = size(A, 1); davg = count(A) // n          # count(A) = 2m
    out = Dict{String,Int}()
    for (name, x) in zip(("R0", "R2"), even_modes(A))
        x === nothing && continue
        q = x // davg
        out["CEIL-" * name] = 2 * ceil(Int, q)
        out["FLOOR-" * name] = 2 * floor(Int, q)
    end
    return out
end

# 1. G_10 and the listed counterexamples ------------------------------------------------
E10 = [(0,5),(0,6),(5,6),(1,7),(1,8),(1,9),(7,8),(7,9),(8,9),(0,9),(2,7),(3,8),(4,9)]
G10 = falses(10, 10)
for (a, b) in E10; G10[a+1, b+1] = G10[b+1, a+1] = true; end
check(G10 == graph6("I?ACJ@PqW"), "G_10 graph6")
check(connected(G10) && forest_number(G10) == 7, "f(G_10) = 7")
check(right_sides(G10) == Dict("CEIL-R0" => 8, "CEIL-R2" => 8, "FLOOR-R0" => 6, "FLOOR-R2" => 6), "G_10 right sides")
println("G_10: f = ", forest_number(G10), ", right sides ", right_sides(G10))

listed = Dict{String,Set{String}}()
for line in eachline(joinpath(@__DIR__, "..", "data", "connected_2_10.txt"))
    startswith(line, "X ") || continue
    _, reading, g6, _, _ = split(line)
    push!(get!(listed, String(g6), Set{String}()), String(reading))
end
check(length(listed) == 7, "seven listed graphs")
for g6 in sort(collect(keys(listed)))
    readings = listed[g6]
    A = graph6(g6); f = forest_number(A); rs = right_sides(A)
    viol = Set(r for (r, v) in rs if f < v)
    check(connected(A) && viol == readings, "$g6 readings")
    println(g6, "  f = ", f, "  violated ", join(sort(collect(viol)), " "))
end

# 2-3. the chains H_c ---------------------------------------------------------------------
function chain(c)
    n = 4c; A = falses(n, n)
    for i in 0:c-1
        for a in 0:3, b in a+1:3
            A[4i+a+1, 4i+b+1] = A[4i+b+1, 4i+a+1] = true
        end
        if i + 1 < c
            A[4i+2, 4i+5] = A[4i+5, 4i+2] = true      # vertex 4i+1 -- vertex 4(i+1), 0-based
        end
    end
    return A
end

for c in 1:300
    A = chain(c); n = 4c; tag = "H_$c"
    check(connected(A), tag * " connected")
    check(count(A) == 14c - 2, tag * " edges")
    check(all(A[4i+a+1, 4i+b+1] for i in 0:c-1 for a in 0:3 for b in 0:3 if a != b), tag * " cliques")
    if c <= 15
        mask = sum(1 << (v - 1) for v in 1:n if (v - 1) % 4 >= 2)
        check(forest_mask(A, mask), tag * " explicit forest")
    end
    c <= 5 && check(forest_number(A) == 2c, tag * " f = 2c by all subsets")
    r0, r2 = even_modes(A)
    check(r0 == r2 == 4c - 4, tag * " even modes")
    rs = right_sides(A)
    check((rs["CEIL-R0"] > 2c) == (c >= 8) && (rs["FLOOR-R0"] > 2c) == (c >= 14), tag * " pattern")
    check(rs["CEIL-R0"] == 2 * ceil(Int, 8c * (c - 1) // (7c - 1)), tag * " closed form")
end
println("H_c, c = 1..300: checked (exact f for c <= 5)")

if isempty(FAILS)
    println("ALL OK")
else
    println(length(FAILS), " FAILURES"); exit(1)
end
