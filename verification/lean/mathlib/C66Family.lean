/-
  Written on the Wall II, Conjecture 66, is false for the chains H_c of the paper:
  under both readings of the even mode, with CEIL for every c ≥ 8 and with FLOOR for every c ≥ 14.

  Conjecture 66 (Graffiti.pc, 2004).  If G is a simple connected graph, then
      f(G) ≥ 2 * CEIL[ even_mode_min(Ḡ) / deg_avg(G) ].

  Definitions used below (Mathlib's `SimpleGraph`):
  * `forestNumber G`: the largest card of a vertex set S such that the induced graph `G.induce S`
    is acyclic;
  * `avgDeg G`: the sum of the degrees divided by the number of vertices;
  * `evenMode1 H`: among the even values in the degree sequence of H, the most frequent one,
    the smallest of these if several are equally frequent (the list's definition);
  * `evenMode2 H`: the smallest even value among the most frequent degrees of H;
    both are 0 when undefined.

  H_c has vertex set Fin c × Fin 4: the vertices (i, 0..3) form a copy of K₄, and (i, 1) is
  joined to (i+1, 0).
-/
import Mathlib

open SimpleGraph Finset

namespace WOWII66

section Definitions

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- the forest number: the largest size of a vertex set inducing an acyclic subgraph -/
noncomputable def forestNumber (G : SimpleGraph V) : ℕ :=
  (univ.filter fun S : Finset V => (G.induce (S : Set V)).IsAcyclic).sup Finset.card

/-- the multiplicity of `d` in the degree sequence -/
def mult (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : ℕ :=
  (univ.filter fun v => G.degree v = d).card

/-- the list's even mode: the most frequent even degree, the smallest if tied; 0 if none -/
def evenMode1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let E := (univ.image fun v => G.degree v).filter Even
  if h : (E.filter fun d => mult G d = E.sup (mult G)).Nonempty then
    (E.filter fun d => mult G d = E.sup (mult G)).min' h else 0

/-- second reading: the smallest even value among the most frequent degrees; 0 if none -/
def evenMode2 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  let A := univ.image fun v => G.degree v
  if h : (A.filter fun d => mult G d = A.sup (mult G) ∧ Even d).Nonempty then
    (A.filter fun d => mult G d = A.sup (mult G) ∧ Even d).min' h else 0

/-- the average degree -/
def avgDeg (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (∑ v, (G.degree v : ℚ)) / Fintype.card V

end Definitions

/-! ## The chains H_c -/

/-- the relation generating H_c: same block, or (i,1) followed by (i+1,0) -/
def rel (c : ℕ) (u v : Fin c × Fin 4) : Prop :=
  u.1 = v.1 ∨ (u.2 = 1 ∧ v.2 = 0 ∧ v.1.val = u.1.val + 1)

instance (c : ℕ) : DecidableRel (rel c) := fun u v => by unfold rel; infer_instance

/-- the chain H_c of c copies of K₄ -/
def H (c : ℕ) : SimpleGraph (Fin c × Fin 4) := SimpleGraph.fromRel (rel c)

instance (c : ℕ) : DecidableRel (H c).Adj := fun u v => by
  unfold H; rw [fromRel_adj]; infer_instance

lemma H_adj_iff {c : ℕ} {u v : Fin c × Fin 4} :
    (H c).Adj u v ↔ u ≠ v ∧ (rel c u v ∨ rel c v u) := fromRel_adj _ _ _

lemma H_adj_block {c : ℕ} {u v : Fin c × Fin 4} (h : u.1 = v.1) (hne : u ≠ v) : (H c).Adj u v :=
  H_adj_iff.mpr ⟨hne, Or.inl (Or.inl h)⟩

/-! ### The forest number is at most 2c -/

/-- three distinct vertices of one block lie in no induced forest -/
lemma not_three_in_block {c : ℕ} (S : Finset (Fin c × Fin 4))
    (hS : ((H c).induce (S : Set (Fin c × Fin 4))).IsAcyclic) (i : Fin c) :
    (S.filter fun v => v.1 = i).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp hlt
  simp only [Finset.mem_filter] at ha hb hd
  have adj : ∀ {x y : Fin c × Fin 4}, x.1 = i → y.1 = i → x ≠ y → (H c).Adj x y :=
    fun hx hy hxy => H_adj_block (hx.trans hy.symm) hxy
  have hc := hS.cliqueFree (le_refl 3)
  apply hc {⟨a, ha.1⟩, ⟨b, hb.1⟩, ⟨d, hd.1⟩}
  rw [is3Clique_triple_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact adj ha.2 hb.2 hab
  · exact adj ha.2 hd.2 had
  · exact adj hb.2 hd.2 hbd

lemma forest_card_le {c : ℕ} (S : Finset (Fin c × Fin 4))
    (hS : ((H c).induce (S : Set (Fin c × Fin 4))).IsAcyclic) : S.card ≤ 2 * c := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  calc ∑ i ∈ (univ : Finset (Fin c)), (S.filter fun v => v.1 = i).card
      ≤ ∑ _i ∈ (univ : Finset (Fin c)), 2 := Finset.sum_le_sum fun i _ => not_three_in_block S hS i
    _ = 2 * c := by simp [mul_comm]

lemma forestNumber_le (c : ℕ) : forestNumber (H c) ≤ 2 * c := by
  classical
  unfold forestNumber
  apply Finset.sup_le
  intro S hS
  simp only [Finset.mem_filter] at hS
  convert forest_card_le S (by convert hS.2)

/-! ### Connectivity -/

lemma reach_block {c : ℕ} (i : Fin c) (a b : Fin 4) : (H c).Reachable (i, a) (i, b) := by
  by_cases h : a = b
  · subst h; rfl
  · exact (H_adj_block (u := (i, a)) (v := (i, b)) rfl fun e => h (Prod.ext_iff.mp e).2).reachable

lemma reach_zero {c : ℕ} (h0 : 0 < c) : ∀ k (hk : k < c), (H c).Reachable (⟨0, h0⟩, 0) (⟨k, hk⟩, 0)
  | 0, _ => Reachable.refl _
  | k + 1, hk => by
    have ih := reach_zero h0 k (by omega)
    have step : (H c).Adj (⟨k, by omega⟩, 1) (⟨k + 1, hk⟩, 0) :=
      H_adj_iff.mpr ⟨by simp, Or.inl (Or.inr ⟨rfl, rfl, rfl⟩)⟩
    exact ih.trans ((reach_block _ 0 1).trans step.reachable)

lemma H_connected {c : ℕ} (h0 : 0 < c) : (H c).Connected := by
  have : Nonempty (Fin c × Fin 4) := ⟨(⟨0, h0⟩, 0)⟩
  refine Connected.mk fun u v => ?_
  have hu := (reach_zero h0 u.1.val u.1.isLt).trans (reach_block u.1 0 u.2)
  have hv := (reach_zero h0 v.1.val v.1.isLt).trans (reach_block v.1 0 v.2)
  exact hu.symm.trans hv

/-! ### Degrees -/

/-- the number of joining edges at a vertex -/
def bridges (c : ℕ) (v : Fin c × Fin 4) : ℕ :=
  (if v.2 = 1 ∧ v.1.val + 1 < c then 1 else 0) + (if v.2 = 0 ∧ 0 < v.1.val then 1 else 0)

lemma card_self {c : ℕ} (i : Fin c) : #{x : Fin c | i = x ∨ x = i} = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => h.elim Eq.symm id, Or.inr⟩

lemma card_none {c : ℕ} (i : Fin c) : #{x : Fin c | ¬i = x ∧ (i = x ∨ x = i)} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ h
  exact h.1 (h.2.elim id Eq.symm)

lemma card_prev {c : ℕ} (i : Fin c) :
    #{x : Fin c | i = x ∨ x = i ∨ (i : ℕ) = x + 1} = 1 + if 0 < (i : ℕ) then 1 else 0 := by
  split_ifs with h
  · have hne : i ≠ ⟨i - 1, by omega⟩ := by intro e; rw [Fin.ext_iff] at e; simp at e; omega
    rw [show (univ.filter fun x : Fin c => i = x ∨ x = i ∨ (i : ℕ) = x + 1) = {i, ⟨i - 1, by omega⟩} by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      constructor <;> intro hx <;> omega]
    rw [Finset.card_pair hne]
  · rw [show (univ.filter fun x : Fin c => i = x ∨ x = i ∨ (i : ℕ) = x + 1) = {i} by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
      constructor <;> intro hx <;> omega]
    simp

lemma card_next {c : ℕ} (i : Fin c) :
    #{x : Fin c | (i = x ∨ (x : ℕ) = i + 1) ∨ x = i} = 1 + if (i : ℕ) + 1 < c then 1 else 0 := by
  split_ifs with h
  · have hne : i ≠ ⟨i + 1, h⟩ := by intro e; rw [Fin.ext_iff] at e; simp at e
    rw [show (univ.filter fun x : Fin c => (i = x ∨ (x : ℕ) = i + 1) ∨ x = i) = {i, ⟨i + 1, h⟩} by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff]
      constructor <;> intro hx <;> omega]
    rw [Finset.card_pair hne]
  · rw [show (univ.filter fun x : Fin c => (i = x ∨ (x : ℕ) = i + 1) ∨ x = i) = {i} by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
      constructor <;> intro hx <;> omega]
    simp

lemma degree_H (c : ℕ) (v : Fin c × Fin 4) : (H c).degree v = 3 + bridges c v := by
  classical
  obtain ⟨i, a⟩ := v
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter (H c), Finset.card_filter,
    Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, H_adj_iff, rel, bridges]
  fin_cases a <;> simp [Prod.ext_iff, Finset.sum_add_distrib, card_self, card_none, card_prev,
    card_next] <;> omega

lemma bridges_le (c : ℕ) (v : Fin c × Fin 4) : bridges c v ≤ 1 := by
  unfold bridges
  split_ifs with h1 h2 <;> simp_all

lemma sum_next (c : ℕ) : (∑ i : Fin c, if (i : ℕ) + 1 < c then 1 else 0) = c - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i + 1 < c then 1 else 0) c, ← Finset.card_filter]
  rw [show (range c).filter (fun i => i + 1 < c) = range (c - 1) by ext x; simp; omega]
  simp

lemma sum_prev (c : ℕ) : (∑ i : Fin c, if 0 < (i : ℕ) then 1 else 0) = c - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if 0 < i then 1 else 0) c, ← Finset.card_filter]
  rw [show (range c).filter (fun i => 0 < i) = Ico 1 c by ext x; simp; omega]
  simp

lemma sum_bridges (c : ℕ) (hc : 1 ≤ c) : (∑ v, bridges c v) = 2 * c - 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, bridges]
  simp only [Fin.isValue, Fin.reduceEq, false_and, ite_false, true_and, add_zero, zero_add,
    Finset.sum_add_distrib, sum_next, sum_prev]
  omega

lemma card_V (c : ℕ) : Fintype.card (Fin c × Fin 4) = 4 * c := by simp [mul_comm]

lemma sum_degree (c : ℕ) (hc : 1 ≤ c) : (∑ v, (H c).degree v) = 14 * c - 2 := by
  simp only [degree_H, Finset.sum_add_distrib, sum_bridges c hc]
  rw [Finset.sum_const, card_univ, card_V, smul_eq_mul]
  omega

/-- the number of vertices of degree 4 is 2c - 2 -/
lemma mult_four (c : ℕ) (hc : 1 ≤ c) : mult (H c) 4 = 2 * c - 2 := by
  unfold mult
  rw [← sum_bridges c hc, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro v _
  have := bridges_le c v
  rw [degree_H]
  split_ifs with h <;> omega

lemma mult_three (c : ℕ) (hc : 1 ≤ c) : mult (H c) 3 = 2 * c + 2 := by
  have h34 : mult (H c) 3 + mult (H c) 4 = 4 * c := by
    unfold mult
    rw [← Finset.card_union_of_disjoint]
    · rw [show (univ.filter fun v => (H c).degree v = 3) ∪ (univ.filter fun v => (H c).degree v = 4)
          = univ by
        ext v; have := bridges_le c v; simp [degree_H]; omega]
      simp [mul_comm]
    · rw [Finset.disjoint_filter]; intro v _ h; omega
  have := mult_four c hc
  omega

/-! ### The complement -/

lemma compl_degree (c : ℕ) (v : Fin c × Fin 4) :
    (H c)ᶜ.degree v = 4 * c - 1 - (3 + bridges c v) := by
  rw [degree_compl, card_V, degree_H]

lemma compl_mult (c : ℕ) (hc : 2 ≤ c) (d : ℕ) :
    mult (H c)ᶜ d = if d = 4 * c - 4 then 2 * c + 2 else if d = 4 * c - 5 then 2 * c - 2 else 0 := by
  have h3 := mult_three c (by omega)
  have h4 := mult_four c (by omega)
  unfold mult at *
  split_ifs with ha hb
  · rw [← h3]; congr 1; ext v; have := bridges_le c v; simp [compl_degree, degree_H]; omega
  · rw [← h4]; congr 1; ext v; have := bridges_le c v; simp [compl_degree, degree_H]; omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _; have := bridges_le c v; rw [compl_degree]; omega

lemma compl_image (c : ℕ) (hc : 2 ≤ c) :
    (univ.image fun v => (H c)ᶜ.degree v) = {4 * c - 4, 4 * c - 5} := by
  ext d
  simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨v, rfl⟩; have := bridges_le c v; rw [compl_degree]; omega
  · rintro (rfl | rfl)
    · refine ⟨(⟨0, by omega⟩, 2), ?_⟩
      have hb : bridges c (⟨0, by omega⟩, 2) = 0 := by simp [bridges]
      rw [compl_degree, hb]; omega
    · refine ⟨(⟨0, by omega⟩, 1), ?_⟩
      have hb : bridges c (⟨0, by omega⟩, 1) = 1 := by simp [bridges]; omega
      rw [compl_degree, hb]; omega

lemma evenMode1_eq (c : ℕ) (hc : 2 ≤ c) : evenMode1 (H c)ᶜ = 4 * c - 4 := by
  have hE : ((univ.image fun v => (H c)ᶜ.degree v).filter Even) = {4 * c - 4} := by
    rw [compl_image c hc]
    ext d
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, he⟩
      · rfl
      · exfalso; rcases he with ⟨k, hk⟩; omega
    · rintro rfl; exact ⟨Or.inl rfl, ⟨2 * c - 2, by omega⟩⟩
  have hF : (({4 * c - 4} : Finset ℕ).filter fun d =>
      mult (H c)ᶜ d = ({4 * c - 4} : Finset ℕ).sup (mult (H c)ᶜ)) = {4 * c - 4} := by
    rw [Finset.sup_singleton, Finset.filter_singleton, ite_eq_left rfl]
  unfold evenMode1
  simp only [hE]
  rw [dite_eq_left (by rw [hF]; exact Finset.singleton_nonempty _)]
  simp only [hF, Finset.min'_singleton]

lemma evenMode2_eq (c : ℕ) (hc : 2 ≤ c) : evenMode2 (H c)ᶜ = 4 * c - 4 := by
  have hne : 4 * c - 5 ≠ 4 * c - 4 := by omega
  have m4 : mult (H c)ᶜ (4 * c - 4) = 2 * c + 2 := by rw [compl_mult c hc, ite_eq_left rfl]
  have m5 : mult (H c)ᶜ (4 * c - 5) = 2 * c - 2 := by
    rw [compl_mult c hc, ite_eq_right hne, ite_eq_left rfl]
  have hsup : (({4 * c - 4, 4 * c - 5} : Finset ℕ)).sup (mult (H c)ᶜ) = 2 * c + 2 := by
    rw [Finset.sup_insert, Finset.sup_singleton, m4, m5]
    exact sup_eq_left.mpr (by omega)
  have hF : ((({4 * c - 4, 4 * c - 5} : Finset ℕ)).filter fun d =>
      mult (H c)ᶜ d = 2 * c + 2 ∧ Even d) = {4 * c - 4} := by
    ext d
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, h, -⟩
      · rfl
      · exfalso; rw [m5] at h; omega
    · rintro rfl; exact ⟨Or.inl rfl, m4, ⟨2 * c - 2, by omega⟩⟩
  unfold evenMode2
  simp only [compl_image c hc, hsup, hF]
  rw [dite_eq_left (Finset.singleton_nonempty _)]
  simp only [Finset.min'_singleton]

lemma avgDeg_eq (c : ℕ) (hc : 1 ≤ c) : avgDeg (H c) = (14 * c - 2 : ℚ) / (4 * c) := by
  unfold avgDeg
  rw [← Nat.cast_sum, sum_degree c hc, card_V]
  push_cast [show 2 ≤ 14 * c by omega]
  ring

/-! ### The right side -/

lemma ratio_eq (c : ℕ) (hc : 2 ≤ c) :
    ((4 * c - 4 : ℕ) : ℚ) / avgDeg (H c) = 8 * c * (c - 1) / (7 * c - 1) := by
  rw [avgDeg_eq c (by omega)]
  have hc' : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have h7 : (7 * c - 1 : ℚ) ≠ 0 := by linarith
  have h14 : (14 * c - 2 : ℚ) ≠ 0 := by linarith
  have h4 : (4 * c : ℚ) ≠ 0 := by positivity
  push_cast [show 4 ≤ 4 * c by omega]
  rw [div_div_eq_mul_div, div_eq_div_iff h14 h7]
  ring

lemma ceil_gt (c : ℕ) (hc : 8 ≤ c) : (c : ℤ) + 1 ≤ ⌈(8 * c * (c - 1) / (7 * c - 1) : ℚ)⌉ := by
  have hc' : (8 : ℚ) ≤ c := by exact_mod_cast hc
  have : (c : ℤ) < ⌈(8 * c * (c - 1) / (7 * c - 1) : ℚ)⌉ := by
    rw [Int.lt_ceil]
    push_cast
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  omega

lemma floor_ge (c : ℕ) (hc : 14 ≤ c) : (c : ℤ) + 1 ≤ ⌊(8 * c * (c - 1) / (7 * c - 1) : ℚ)⌋ := by
  have hc' : (14 : ℚ) ≤ c := by exact_mod_cast hc
  rw [Int.le_floor]
  push_cast
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ### The counterexamples -/

/-- For every c ≥ 8, H_c is connected and violates Conjecture 66 as printed (with CEIL),
    under both readings of the even mode. -/
theorem H_violates_ceil (c : ℕ) (hc : 8 ≤ c) :
    (H c).Connected ∧
    (forestNumber (H c) : ℤ) < 2 * ⌈(evenMode1 (H c)ᶜ : ℚ) / avgDeg (H c)⌉ ∧
    (forestNumber (H c) : ℤ) < 2 * ⌈(evenMode2 (H c)ᶜ : ℚ) / avgDeg (H c)⌉ := by
  have hf : (forestNumber (H c) : ℤ) ≤ 2 * c := by exact_mod_cast forestNumber_le c
  have key := ceil_gt c hc
  rw [← ratio_eq c (by omega)] at key
  refine ⟨H_connected (by omega), ?_, ?_⟩
  · rw [evenMode1_eq c (by omega)]; linarith
  · rw [evenMode2_eq c (by omega)]; linarith

/-- For every c ≥ 14, H_c violates Conjecture 66 also with FLOOR in place of CEIL,
    under both readings of the even mode. -/
theorem H_violates_floor (c : ℕ) (hc : 14 ≤ c) :
    (H c).Connected ∧
    (forestNumber (H c) : ℤ) < 2 * ⌊(evenMode1 (H c)ᶜ : ℚ) / avgDeg (H c)⌋ ∧
    (forestNumber (H c) : ℤ) < 2 * ⌊(evenMode2 (H c)ᶜ : ℚ) / avgDeg (H c)⌋ := by
  have hf : (forestNumber (H c) : ℤ) ≤ 2 * c := by exact_mod_cast forestNumber_le c
  have key := floor_ge c hc
  rw [← ratio_eq c (by omega)] at key
  refine ⟨H_connected (by omega), ?_, ?_⟩
  · rw [evenMode1_eq c (by omega)]; linarith
  · rw [evenMode2_eq c (by omega)]; linarith

/-- Conjecture 66 with FLOOR and the list's even mode: false. -/
theorem conjecture66_floor_false :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 * ⌊(evenMode1 Gᶜ : ℚ) / avgDeg G⌋ ≤ (forestNumber G : ℤ) := by
  intro h
  obtain ⟨hconn, hlt, -⟩ := H_violates_floor 14 le_rfl
  exact absurd (h _ (H 14) hconn) (not_le.mpr hlt)

/-- Conjecture 66 as printed (CEIL, the list's even mode): false. -/
theorem conjecture66_false :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 2 * ⌈(evenMode1 Gᶜ : ℚ) / avgDeg G⌉ ≤ (forestNumber G : ℤ) := by
  intro h
  obtain ⟨hconn, hlt, -⟩ := H_violates_ceil 8 le_rfl
  exact absurd (h _ (H 8) hconn) (not_le.mpr hlt)

end WOWII66

#print axioms WOWII66.H_violates_ceil
#print axioms WOWII66.H_violates_floor
#print axioms WOWII66.conjecture66_false
#print axioms WOWII66.conjecture66_floor_false
