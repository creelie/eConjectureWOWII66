/-
  Certificate that the 10-vertex graph G₁₀ refutes Written on the Wall II Conjecture 66 as printed.

  Conjecture 66 (Graffiti.pc, 2004).  If G is a simple connected graph, then
      f(G) ≥ 2 * CEIL[ even_mode_min(Ḡ) / deg_avg(G) ],
  where f(G) is the order of a largest induced forest, Ḡ is the complement of G, deg_avg(G) = 2m/n,
  and even_mode_min(Ḡ) is the most frequent even degree of Ḡ (the smallest one if several are
  equally frequent).  We also evaluate the other reading of even_mode_min (the smallest even value
  among the most frequent degrees of Ḡ) and the right side with FLOOR in place of CEIL.

  G₁₀: a K₄ on {1, 7, 8, 9}, a triangle on {0, 5, 6}, the bridge 0 - 9, and pendant vertices 2, 3, 4
  attached to 7, 8, 9 (graph6 `I?ACJ@PqW`).

  A vertex set is a bit mask below 2¹⁰.  A set induces a forest iff repeatedly deleting the
  vertices that have at most one neighbour in what is left deletes everything (a graph with a
  cycle keeps the cycle forever; a nonempty forest always has a vertex of degree ≤ 1).
  The file is self-contained (Lean 4 core, no Mathlib); every statement is checked by the kernel
  (`decide +kernel`).
-/

def N : Nat := 10

def E : List (Nat × Nat) :=
  [(0,5),(0,6),(5,6),(1,7),(1,8),(1,9),(7,8),(7,9),(8,9),(0,9),(2,7),(3,8),(4,9)]

def V : List Nat := List.range N

def adj (u v : Nat) : Bool :=
  E.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

def nbrs (v : Nat) : List Nat := V.filter (adj v)

def deg (v : Nat) : Nat := (nbrs v).length

def subsetOf (mask : Nat) : List Nat := V.filter fun v => mask.testBit v

/-- delete, `fuel` times, every vertex of `S` with at most one neighbour in `S` -/
def strip : Nat → List Nat → List Nat
  | 0, S => S
  | fuel + 1, S => strip fuel (S.filter fun v => decide (2 ≤ ((nbrs v).filter S.contains).length))

/-- `S` induces a forest -/
def isForest (S : List Nat) : Bool := (strip N S).isEmpty

/-- forest number: the largest size of a vertex subset inducing a forest -/
def fVal : Nat :=
  (List.range (2 ^ N)).foldl
    (fun acc m => if isForest (subsetOf m) then max acc (subsetOf m).length else acc) 0

/-- breadth-first reachability from 0 -/
def reach : Nat → List Nat → List Nat
  | 0, seen => seen
  | fuel + 1, seen => reach fuel (seen ++ (V.filter fun w => !seen.contains w && seen.any fun u => adj u w))

def connected : Bool := (reach N [0]).length == N

/-- twice the number of edges -/
def twoM : Nat := (V.map deg).foldl (· + ·) 0

/-- degree of v in the complement -/
def cdeg (v : Nat) : Nat := N - 1 - deg v

/-- multiplicity of d in the complement degree sequence -/
def mult (d : Nat) : Nat := (V.filter fun v => cdeg v == d).length

def evens : List Nat := (List.range N).filter fun d => d % 2 == 0

/-- reading R0: the most frequent even complement degree, the smallest if tied (0 if none) -/
def modeR0 : Nat :=
  let top := (evens.map mult).foldl max 0
  ((evens.filter fun d => mult d == top && top > 0).head?).getD 0

/-- reading R2: the smallest even value among the most frequent complement degrees (0 if none) -/
def modeR2 : Nat :=
  let top := ((List.range N).map mult).foldl max 0
  ((evens.filter fun d => mult d == top).head?).getD 0

/-- 2 * CEIL(x / (2m/n)) and 2 * FLOOR(x / (2m/n)), in integer arithmetic -/
def rhsCeil (x : Nat) : Nat := 2 * ((x * N + twoM - 1) / twoM)
def rhsFloor (x : Nat) : Nat := 2 * (x * N / twoM)

theorem connected_true : connected = true := by decide +kernel
theorem twoM_eq : twoM = 26 := by decide +kernel
theorem cdegs : V.map cdeg = [6, 6, 8, 8, 8, 7, 7, 5, 5, 4] := by decide +kernel
theorem modeR0_eq : modeR0 = 8 := by decide +kernel
theorem modeR2_eq : modeR2 = 8 := by decide +kernel
theorem rhs_ceil : rhsCeil 8 = 8 := by decide +kernel
theorem rhs_floor : rhsFloor 8 = 6 := by decide +kernel

/-- sanity checks of the forest test: the triangle {0, 5, 6} is not a forest -/
theorem triangle_not_forest : isForest [0, 5, 6] = false := by decide +kernel
/-- {2, 3, 4, 5, 6, 8, 9} induces a forest on 7 vertices (mask 4+8+16+32+64+256+512 = 892) -/
theorem forest7 : isForest (subsetOf 892) = true ∧ (subsetOf 892).length = 7 := by decide +kernel

/-- f(G₁₀) = 7, by testing all 1024 vertex subsets -/
theorem f_eq : fVal = 7 := by decide +kernel

/-- Conjecture 66 as printed fails for G₁₀ under both readings of even_mode_min:
    f(G₁₀) = 7 < 8 = 2 * CEIL[8 / (26/10)]. -/
theorem conjecture66_false :
    connected = true ∧ fVal < rhsCeil modeR0 ∧ fVal < rhsCeil modeR2 := by
  refine ⟨connected_true, ?_, ?_⟩ <;> rw [f_eq] <;> decide +kernel

/-- With FLOOR in place of CEIL the inequality holds for G₁₀ (6 ≤ 7); see the paper for the
    family that refutes that reading too. -/
theorem floor_reading_holds_here : rhsFloor modeR0 ≤ fVal := by rw [f_eq]; decide +kernel

#print axioms conjecture66_false
