# A counterexample to Graffiti.pc Conjecture 66

Deep Bhattacharjee

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23254096.svg)](https://doi.org/10.5281/zenodo.23254096)

*Written on the Wall II* (E. DeLaViña's list of the conjectures of Graffiti.pc) marks
Conjecture 66 as open:

> If G is a simple connected graph, then f(G) ≥ 2·⌈even_mode_min(Ḡ) / deg_avg(G)⌉,

where f(G) is the order of a largest induced forest, Ḡ the complement and deg_avg(G) = 2m/n.

It is false. Let H_c be c copies of K₄ joined in a path by c − 1 single edges. Then
f(H_c) = 2c, the only even degree of the complement is 4c − 4, and deg_avg(H_c) = (7c − 1)/(2c),
so the right side is 2·⌈8c(c − 1)/(7c − 1)⌉, which exceeds 2c for every c ≥ 8. The same family
also refutes the statement with ⌊·⌋ in place of ⌈·⌉ (the definition the list links to) for every
c ≥ 14, and the gap grows without bound. Both readings of even_mode_min are covered. As printed,
the smallest counterexamples have 10 vertices: 7 of the 11,716,571 connected graphs on 10
vertices, and none smaller.

## Paper

`preprintWOWIIConjecture66/` holds the paper, *A counterexample to a conjecture of Graffiti.pc on
the forest number* (LaTeX source and TikZ figures); `dist/` holds the PDF, a source zip with PNG
figures and an arXiv tarball, rebuilt by `scripts/build_paper.sh`. The same paper in the template of
Discrete Mathematics Letters is `preprintWOWIIConjecture66/dml/wowii66-dml.tex`; `scripts/build_dml.sh`
builds it into `build/submission-dml/`.

## Checks

```
verification/c/wowii66.c                 exhaustive search (graph6 from nauty's geng) and H_c, c <= 300
verification/cpp/wowii66.cpp             independent re-implementation; its output is identical to the C one
verification/shell/check66.sh            bash integer arithmetic only: G_10 (f by all subsets), H_c, Lemma 2.3
verification/python/verify66.py          exact arithmetic, all labelled graphs up to 6 vertices, H_c
verification/julia/verify66.jl           exact arithmetic, f by all subsets for H_c with c <= 5
verification/lean/C66.lean               Lean 4 kernel check of the 10-vertex counterexample (axiom: propext)
verification/lean/mathlib/C66Family.lean Lean 4 + Mathlib proof that H_c violates the conjecture for every
                                         c >= 8 (c >= 14 with the floor), under both readings
verification/data/                       output of the search over all connected graphs with 2 to 10 vertices
```

`scripts/run_all.sh` runs them all (`FULL=1` repeats the 10-vertex search, `MATHLIB=1` builds the
Mathlib proof); the `verify` workflow runs them on every pull request.

## Citation

Archived on Zenodo: concept DOI [10.5281/zenodo.23254096](https://doi.org/10.5281/zenodo.23254096)
(all versions); v1.0.0 is [10.5281/zenodo.23254097](https://doi.org/10.5281/zenodo.23254097).
See `CITATION.cff`.

## Licence

MIT, see `LICENSE`.
