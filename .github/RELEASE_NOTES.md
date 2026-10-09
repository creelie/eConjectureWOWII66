**A counterexample to a conjecture of Graffiti.pc on the forest number**, by Deep Bhattacharjee.

Conjecture 66 of Graffiti.pc, listed as open in Written on the Wall II, states that every connected graph G satisfies f(G) ≥ 2·⌈even_mode_min(Ḡ)/deg_avg(G)⌉, where f is the order of a largest induced forest. The paper shows that it is false under every reading of its definitions.

| Reading | Counterexamples |
|---|---|
| as printed (⌈·⌉), both readings of the even mode | the chain H_c of c copies of K₄ for every c ≥ 8; seven graphs with 10 vertices, none smaller |
| with ⌊·⌋, both readings of the even mode | H_c for every c ≥ 14 (56 vertices); a 37-vertex example for the first reading |

The gap between the two sides grows without bound along H_c. The proofs are by hand. Every finite claim is re-checked in C, C++, Bash, Python, Julia and Lean 4: a Lean proof with Mathlib covers H_c for every c using only the standard axioms, and a kernel check of the 10-vertex counterexample depends only on `propext`. The exhaustive search covers all 11,989,763 connected graphs with 2 to 10 vertices.

Files:
- `wowii66-forest-number.pdf`: the paper
- `wowii66-forest-number-tex.zip`: LaTeX source with the figures as PNG (and their TikZ sources)
- `wowii66-forest-number-arxiv.tar.gz`: LaTeX source with the figures as PDF, ready for arXiv

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
