/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# PPL 033 — Erdős Problem #86: `C_4`-Free Subgraphs of the Hypercube `Q_n`

**Open Problem Reference:** Erdős Problem #86 (`erdosproblems.com/86`, PPL 033, $100, VERIFIED OPEN):
> Let `Q_n` be the `n`-dimensional hypercube (`2^n` vertices, `n * 2^{n-1}` edges).
> Is `ex(Q_n, C_4) = (1/2 + o(1)) n 2^{n-1}`?

**Honest Scope Statement:** This file does **NOT** solve the open Erdős #86 conjecture
`lim_{n → ∞} ex(Q_n, C_4) / (n 2^{n-1}) = 1/2`. Instead, it formalizes from scratch in pure Mathlib
(0 custom or `private` definitions in any public theorem signature, 0 `sorry`, 0 custom axioms,
0 `native_decide`):

1. **Hypercube `Q_n` Foundations & Density Monotonicity:**
   - Exact edge count `|E(Q_n)| = n * 2^{n-1}` (`ppl033_hypercube_edge_count`).
   - Codimension-1 subcube averaging `n * ex(Q_{n+1}, C_4) ≤ 2 * (n + 1) * ex(Q_n, C_4)`
     (`ppl033_subcube_averaging_step`) and antitonicity of the Turán density
     `ex(Q_n, C_4) / |E(Q_n)|` (`ppl033_turan_density_antitone`).
   - Existence of the Turán density limit `L ∈ [1/2, 247/400]` (`ppl033_turan_density_limit_exists`).
2. **Explicit Lower Bounds (`1/2` Parity-Prefix & Brass–Harborth–Nienborg `1/2 + c/√n`):**
   - Parity-prefix construction with `(n + 1) * 2^{n-2}` edges (`ppl033_parity_prefix_lower`).
   - Recursive 2-coloring product on `Q_4` giving exact Brass–Harborth–Nienborg (1995)
     `(1/2) * (n + √n) * 2^{n-1}` for all `n = 4^r` (`ppl033_bhn_1995_power_of_four`),
     and unconditional `(1/2 + 1/(4√n)) * n * 2^{n-1}` for **all** `n ≥ 1` (`ppl033_bhn_1995_all_n`).
3. **Exact Small-Cube Extremal Numbers (0 `native_decide`):**
   - `ex(Q_1, C_4) = 1`, `ex(Q_2, C_4) = 3`, `ex(Q_3, C_4) = 9`, `ex(Q_4, C_4) = 24`,
     and universal `≤ 3/4` subcube-averaging bound for all `n ≥ 2`.
4. **Upper Bounds (`1/√2`, `2/3`, `(1/4)^{1/3}`, & Sub-`0.6175` Flag-Algebra Sum-of-Squares):**
   - Distance-2 path double counting `ex(Q_n, C_4) ≤ (1/√2 + 1/(2n)) n 2^{n-1}`.
   - `Q_2`-face 2-path bound `ex(Q_n, C_4) ≤ (2/3 + 1/(3n)) n 2^{n-1}`.
   - `Q_3` 3-star bound `∑ C(deg(v), 3) ≤ 2 * C(n, 3) * 2^{n-3}` (`≤ (1/4)^{1/3} ≈ 0.62996`).
   - Oriented `Q_1`-rooted `Q_2`-flag Sum-of-Squares theorem on `Q_3` proving
     `800 (n - 2) |E(G)| ≤ 247 n (n - 2) 2^n + 580 n 2^n` (`≤ (247/400 + 29/(20(n-2))) n 2^{n-1}`,
     asymptotic `0.6175`, strictly beating Chung 1992 `0.62284`, Thomason–Wagner 2009 `0.62256`,
     `0.623`, and `5/8 = 0.625`).
5. **Local Subcube-Averaging Barrier:**
   - Pure `Q_k`-subcube averaging cannot approach `1/2` for any fixed `k ≥ 1`, because
     `ex(Q_k, C_4) / |E(Q_k)| ≥ 1/2 + 1/(4√k) > 1/2`.
-/

namespace PPL033

open scoped BigOperators
open Filter

/-! ## Section 1: Hypercube `Q_n` Foundations & Density Monotonicity -/

section HypercubeFoundations

/-- Private shorthand for the `n`-dimensional hypercube `Q_n`.
NEVER exposed in any public theorem signature. -/
private def Q (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel
    (fun u v : Fin n → Bool => (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1)

/-- Private shorthand for `C_4`-freeness. NEVER exposed in any public theorem signature. -/
private def IsC4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

/-- Private shorthand for `ex(Q_n, C_4)`. NEVER exposed in any public theorem signature. -/
private noncomputable def exC4 (n : ℕ) : ℕ :=
  open Classical in
  sSup { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
    G ≤ Q n ∧ IsC4Free G ∧ G.edgeFinset.card = m }

/-- Flip coordinate `i` of a binary vector `u : Fin n → Bool`. -/
private def flip {n : ℕ} (u : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update u i (!u i)

private lemma flip_apply_self {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    flip u i i = !u i := by
  simp [flip]

private lemma flip_apply_ne {n : ℕ} (u : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    flip u i j = u j := by
  simp [flip, h]

private lemma flip_flip {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    flip (flip u i) i = u := by
  ext j
  by_cases h : j = i
  · subst h; simp [flip]
  · simp [flip, h]

private lemma flip_ne_self {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    flip u i ≠ u := by
  intro h
  have h1 := congrFun h i
  simp [flip] at h1

private lemma flip_comm {n : ℕ} (u : Fin n → Bool) (i j : Fin n) :
    flip (flip u i) j = flip (flip u j) i := by
  ext k
  by_cases h1 : k = i <;> by_cases h2 : k = j
  · subst h1; subst h2; simp [flip]
  · subst h1; simp [flip, h2]
  · subst h2; simp [flip, h1]
  · simp [flip, h1, h2]

private lemma flip_inj {n : ℕ} (u : Fin n → Bool) :
    Function.Injective (flip u) := by
  intro i j h
  by_contra hne
  have h1 := congrFun h i
  simp [flip, hne] at h1

private lemma filter_ne_flip {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    Finset.univ.filter (fun j : Fin n => u j ≠ flip u i j) = {i} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases h : j = i
  · subst h; simp [flip]
  · simp [flip, h]

private lemma Q_adj_iff {n : ℕ} {u v : Fin n → Bool} :
    (Q n).Adj u v ↔ (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1 := by
  unfold Q SimpleGraph.fromRel
  simp only
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · convert h using 2
      ext i
      simp [ne_comm]
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq
    subst heq
    simp at h

private lemma Q_adj_iff_exists_flip {n : ℕ} {u v : Fin n → Bool} :
    (Q n).Adj u v ↔ ∃ i : Fin n, v = flip u i := by
  rw [Q_adj_iff]
  constructor
  · intro h
    rw [Finset.card_eq_one] at h
    rcases h with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    ext j
    by_cases hj : j = i
    · subst hj
      have hm : j ∈ Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by rw [hi]; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [flip_apply_self]
      cases h1 : u j <;> cases h2 : v j <;> simp_all
    · have hm : j ∉ Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by rw [hi]; simp [hj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hm
      rw [flip_apply_ne u hj, hm]
  · rintro ⟨i, rfl⟩
    rw [filter_ne_flip, Finset.card_singleton]

private lemma Q_adj_flip {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    (Q n).Adj u (flip u i) :=
  Q_adj_iff_exists_flip.mpr ⟨i, rfl⟩

private lemma edgeFinset_card_congr {V : Type*} (G : SimpleGraph V)
    (inst1 inst2 : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G inst1).card = (@SimpleGraph.edgeFinset _ G inst2).card := by
  congr 1
  ext e
  simp [SimpleGraph.mem_edgeFinset]

private lemma Q_neighborFinset {n : ℕ} (u : Fin n → Bool) [DecidableRel (Q n).Adj] :
    (Q n).neighborFinset u = Finset.univ.image (flip u) := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Q_adj_iff_exists_flip, Finset.mem_image,
    Finset.mem_univ, true_and, eq_comm]

private lemma Q_degree {n : ℕ} (u : Fin n → Bool) [DecidableRel (Q n).Adj] :
    (Q n).degree u = n := by
  rw [SimpleGraph.degree, Q_neighborFinset, Finset.card_image_of_injective _ (flip_inj u),
    Finset.card_fin]

private lemma Q_edgeFinset_card (n : ℕ) [Fintype (Q n).edgeSet] :
    (Q n).edgeFinset.card = n * 2 ^ (n - 1) := by
  classical
  rw [edgeFinset_card_congr (Q n) _ (SimpleGraph.fintypeEdgeSet (Q n))]
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (Q n)
  have hdeg : ∑ u : Fin n → Bool, (Q n).degree u = n * 2 ^ n := by
    simp [Q_degree, Fintype.card_pi, mul_comm]
  rw [hdeg] at hsum
  cases n with
  | zero =>
    have h0 : 2 * (@SimpleGraph.edgeFinset _ (Q 0) (SimpleGraph.fintypeEdgeSet (Q 0))).card = 0 := by
      simpa using hsum.symm
    have hcard0 : (@SimpleGraph.edgeFinset _ (Q 0) (SimpleGraph.fintypeEdgeSet (Q 0))).card = 0 := by
      omega
    simpa using hcard0
  | succ k =>
    have hpow : (k + 1) * 2 ^ (k + 1) = 2 * ((k + 1) * 2 ^ k) := by ring
    rw [hpow] at hsum
    simp only [Nat.add_sub_cancel]
    exact (Nat.mul_left_cancel (by omega : 0 < 2) hsum).symm

/-- **Theorem 1.1 (`ppl033_hypercube_edge_count`):**
The `n`-dimensional hypercube `Q_n` has exactly `n * 2 ^ (n - 1)` edges (pure Mathlib signature). -/
theorem ppl033_hypercube_edge_count (n : ℕ) :
    open Classical in
    (SimpleGraph.fromRel
      (fun u v : Fin n → Bool =>
        (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1)).edgeFinset.card =
      n * 2 ^ (n - 1) := by
  classical
  trans (@SimpleGraph.edgeFinset (Fin n → Bool) (Q n) (SimpleGraph.fintypeEdgeSet (Q n))).card
  · exact edgeFinset_card_congr (Q n) _ _
  · exact Q_edgeFinset_card n

/-- Characterization of 4-cycles in `Q_n`: every `C_4` in `G ≤ Q_n` is a 2-face
`{a, flip a i, flip (flip a i) j, flip a j}` with `i ≠ j`. -/
private lemma c4_in_Q_is_face {n : ℕ} {G : SimpleGraph (Fin n → Bool)} (hG : G ≤ Q n)
    {a b c d : Fin n → Bool} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    ∃ i j : Fin n, i ≠ j ∧ b = flip a i ∧ d = flip a j ∧ c = flip (flip a i) j := by
  obtain ⟨i, rfl⟩ := Q_adj_iff_exists_flip.mp (hG hab)
  obtain ⟨j, rfl⟩ := Q_adj_iff_exists_flip.mp (hG hbc)
  obtain ⟨k, hdk⟩ := Q_adj_iff_exists_flip.mp (hG hda.symm)
  obtain ⟨l, hdl⟩ := Q_adj_iff_exists_flip.mp (hG hcd)
  have hij : i ≠ j := by
    rintro rfl
    exact hac (flip_flip a i).symm
  have hki : k ≠ i := by
    rintro rfl
    exact hbd hdk.symm
  have hkj : k = j := by
    by_contra hne
    have heq : flip a k = flip (flip (flip a i) j) l := hdk.symm.trans hdl
    have hlk : l = k := by
      by_contra hlk
      have hk_val := congrFun heq k
      rw [flip_apply_self, flip_apply_ne _ (Ne.symm hlk), flip_apply_ne _ hne,
          flip_apply_ne _ hki] at hk_val
      exact Bool.not_ne_self (a k) hk_val
    subst hlk
    have hi_val := congrFun heq i
    rw [flip_apply_ne _ (Ne.symm hki), flip_apply_ne _ (Ne.symm hki),
        flip_apply_ne _ hij, flip_apply_self] at hi_val
    exact Bool.not_ne_self (a i) hi_val.symm
  subst hkj
  exact ⟨i, k, hij, rfl, hdk, rfl⟩

/-- Equivalent characterization of `IsC4Free` for subgraphs `G ≤ Q_n` via 2-faces. -/
private lemma isC4Free_iff_no_face {n : ℕ} {G : SimpleGraph (Fin n → Bool)} (hG : G ≤ Q n) :
    IsC4Free G ↔
      ∀ (u : Fin n → Bool) (i j : Fin n), i ≠ j →
        ¬ (G.Adj u (flip u i) ∧ G.Adj (flip u i) (flip (flip u i) j) ∧
           G.Adj (flip (flip u i) j) (flip u j) ∧ G.Adj (flip u j) u) := by
  constructor
  · intro hfree u i j hij h
    apply hfree u (flip u i) (flip (flip u i) j) (flip u j)
    · intro heq
      have h1 := congrFun heq i
      rw [flip_apply_ne _ hij, flip_apply_self] at h1
      exact Bool.not_ne_self (u i) h1.symm
    · intro heq
      exact hij (flip_inj u heq)
    · exact h
  · intro hface a b c d hac hbd ⟨hab, hbc, hcd, hda⟩
    obtain ⟨i, j, hij, rfl, rfl, rfl⟩ := c4_in_Q_is_face hG hac hbd hab hbc hcd hda
    exact hface a i j hij ⟨hab, hbc, hcd, hda⟩

private lemma exC4_bddAbove (n : ℕ) :
    open Classical in
    BddAbove { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ Q n ∧ IsC4Free G ∧ G.edgeFinset.card = m } := by
  classical
  refine ⟨n * 2 ^ (n - 1), ?_⟩
  rintro m ⟨G, hG, _, rfl⟩
  calc G.edgeFinset.card
      ≤ (Q n).edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hG)
    _ = n * 2 ^ (n - 1) := Q_edgeFinset_card n

private lemma exC4_nonempty (n : ℕ) :
    open Classical in
    { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ Q n ∧ IsC4Free G ∧ G.edgeFinset.card = m }.Nonempty := by
  classical
  refine ⟨0, ⊥, bot_le, fun _ _ _ _ _ _ h => h.1, ?_⟩
  simp

private lemma card_le_exC4 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ Q n) (hfree : IsC4Free G) :
    G.edgeFinset.card ≤ exC4 n := by
  classical
  rw [edgeFinset_card_congr G _ _]
  exact le_csSup (exC4_bddAbove n) ⟨G, hG, hfree, rfl⟩

private lemma exists_exC4_witness (n : ℕ) :
    open Classical in
    ∃ G : SimpleGraph (Fin n → Bool), G ≤ Q n ∧ IsC4Free G ∧ G.edgeFinset.card = exC4 n := by
  classical
  exact Nat.sSup_mem (exC4_nonempty n) (exC4_bddAbove n)

private lemma exC4_le_Q (n : ℕ) : exC4 n ≤ n * 2 ^ (n - 1) := by
  classical
  obtain ⟨G, hG, _, hcard⟩ := exists_exC4_witness n
  rw [← hcard]
  calc G.edgeFinset.card
      ≤ (Q n).edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hG)
    _ = n * 2 ^ (n - 1) := Q_edgeFinset_card n

/-- Embed `Q_n` into `Q_{n+1}` as the codimension-1 subcube `{ u | u i = b }`. -/
private def subcubeEmbed {n : ℕ} (i : Fin (n + 1)) (b : Bool) :
    (Fin n → Bool) ↪ (Fin (n + 1) → Bool) where
  toFun u := i.insertNth b u
  inj' u v h := by
    ext j
    have h1 := congrFun h (i.succAbove j)
    simpa [Fin.insertNth_apply_succAbove] using h1

private lemma subcubeEmbed_apply {n : ℕ} (i : Fin (n + 1)) (b : Bool) (u : Fin n → Bool) :
    subcubeEmbed i b u = i.insertNth b u := rfl

private lemma subcubeEmbed_flip {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (u : Fin n → Bool) (j : Fin n) :
    subcubeEmbed i b (flip u j) = flip (subcubeEmbed i b u) (i.succAbove j) := by
  ext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [subcubeEmbed_apply, flip, (Fin.succAbove_ne i j).symm]
  · intro m
    by_cases hm : m = j
    · subst hm
      simp [subcubeEmbed_apply, flip]
    · have hne : i.succAbove m ≠ i.succAbove j := fun h => hm (Fin.succAbove_right_injective h)
      simp [subcubeEmbed_apply, flip, hm, hne]

private lemma comap_subcubeEmbed_le_Q {n : ℕ} {G : SimpleGraph (Fin (n + 1) → Bool)}
    (hG : G ≤ Q (n + 1)) (i : Fin (n + 1)) (b : Bool) :
    G.comap (subcubeEmbed i b) ≤ Q n := by
  intro u v huv
  have hq : (Q (n + 1)).Adj (subcubeEmbed i b u) (subcubeEmbed i b v) := hG huv
  obtain ⟨k, hk⟩ := Q_adj_iff_exists_flip.mp hq
  have hki : k ≠ i := by
    intro h
    have h1 := congrFun hk i
    rw [h] at h1
    simp [subcubeEmbed_apply, flip] at h1
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
  rw [Q_adj_iff_exists_flip]
  refine ⟨j, (subcubeEmbed i b).injective ?_⟩
  rw [subcubeEmbed_flip, hk]

private lemma comap_subcubeEmbed_isC4Free {n : ℕ} {G : SimpleGraph (Fin (n + 1) → Bool)}
    (hfree : IsC4Free G) (i : Fin (n + 1)) (b : Bool) :
    IsC4Free (G.comap (subcubeEmbed i b)) := by
  intro a x c d hac hxd ⟨h1, h2, h3, h4⟩
  exact hfree _ _ _ _ (fun h => hac ((subcubeEmbed i b).injective h))
    (fun h => hxd ((subcubeEmbed i b).injective h)) ⟨h1, h2, h3, h4⟩

/-- Helper: double counting oriented edges of `G ≤ Q_n` (polymorphic in `Fintype G.edgeSet`). -/
private lemma twice_card_edges_eq_sum_oriented {n : ℕ} (G : SimpleGraph (Fin n → Bool))
    [Fintype G.edgeSet] (hG : G ≤ Q n) :
    open Classical in
    2 * G.edgeFinset.card =
      ∑ u : Fin n → Bool, (Finset.univ.filter (fun j : Fin n => G.Adj u (flip u j))).card := by
  classical
  rw [edgeFinset_card_congr G _ (SimpleGraph.fintypeEdgeSet G)]
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [SimpleGraph.degree]
  symm
  refine Finset.card_bij (fun j _ => flip u j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simpa [SimpleGraph.mem_neighborFinset] using hj
  · intro j1 _ j2 _ h
    exact flip_inj u h
  · intro v hv
    simp only [SimpleGraph.mem_neighborFinset] at hv
    obtain ⟨j, rfl⟩ := Q_adj_iff_exists_flip.mp (hG hv)
    exact ⟨j, by simpa using hv, rfl⟩

/-- Subcube averaging step: `n * |E(G)| ≤ 2 * (n + 1) * ex(Q_n, C_4)` for `C_4`-free `G ≤ Q_{n+1}`. -/
private lemma subcube_averaging_graph {n : ℕ} (G : SimpleGraph (Fin (n + 1) → Bool))
    [Fintype G.edgeSet] (hG : G ≤ Q (n + 1)) (hfree : IsC4Free G) :
    n * G.edgeFinset.card ≤ 2 * (n + 1) * exC4 n := by
  classical
  have hway1 :
      ∑ i : Fin (n + 1), ∑ b : Bool,
        2 * (G.comap (subcubeEmbed i b)).edgeFinset.card =
      n * (2 * G.edgeFinset.card) := by
    have hsub : ∀ (i : Fin (n + 1)) (b : Bool),
        2 * (G.comap (subcubeEmbed i b)).edgeFinset.card =
        ∑ u : Fin n → Bool,
          (Finset.univ.filter (fun j : Fin n =>
            G.Adj (subcubeEmbed i b u) (flip (subcubeEmbed i b u) (i.succAbove j)))).card := by
      intro i b
      rw [twice_card_edges_eq_sum_oriented _ (comap_subcubeEmbed_le_Q hG i b)]
      refine Finset.sum_congr rfl fun u _ => ?_
      congr 1
      ext j
      simp [SimpleGraph.comap_adj, subcubeEmbed_flip]
    simp_rw [hsub]
    have hfib : ∀ i : Fin (n + 1),
        ∑ b : Bool, ∑ u : Fin n → Bool,
          (Finset.univ.filter (fun j : Fin n =>
            G.Adj (subcubeEmbed i b u) (flip (subcubeEmbed i b u) (i.succAbove j)))).card =
        ∑ v : Fin (n + 1) → Bool,
          (Finset.univ.filter (fun j : Fin n => G.Adj v (flip v (i.succAbove j)))).card := by
      intro i
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv
        { toFun := fun p => subcubeEmbed i p.1 p.2
          invFun := fun v => (v i, fun j => v (i.succAbove j))
          left_inv := fun ⟨b, u⟩ => by
            ext
            · simp [subcubeEmbed_apply]
            · simp [subcubeEmbed_apply]
          right_inv := fun v => by
            ext k
            refine Fin.succAboveCases i ?_ ?_ k
            · simp [subcubeEmbed_apply]
            · intro m; simp [subcubeEmbed_apply] } _ _ (fun _ => rfl)
    simp_rw [hfib]
    rw [Finset.sum_comm]
    rw [twice_card_edges_eq_sum_oriented G hG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hinner : ∀ i : Fin (n + 1),
        (Finset.univ.filter (fun j : Fin n => G.Adj v (flip v (i.succAbove j)))).card =
        (Finset.univ.filter (fun k : Fin (n + 1) => k ≠ i ∧ G.Adj v (flip v k))).card := by
      intro i
      refine Finset.card_bij (fun j _ => i.succAbove j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨Fin.succAbove_ne i j, hj⟩
      · intro j1 _ j2 _ h
        exact Fin.succAbove_right_injective h
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk.1
        exact ⟨j, by simpa using hk.2, rfl⟩
    simp_rw [hinner, Finset.card_filter]
    rw [Finset.sum_comm]
    have hpoint : ∀ k : Fin (n + 1),
        (∑ i : Fin (n + 1), if k ≠ i ∧ G.Adj v (flip v k) then 1 else 0) =
        n * (if G.Adj v (flip v k) then 1 else 0) := by
      intro k
      by_cases hadj : G.Adj v (flip v k)
      · simp only [hadj, and_true, ↓reduceIte, mul_one]
        rw [← Finset.card_filter]
        have : (Finset.univ.filter (fun i : Fin (n + 1) => k ≠ i)) = Finset.univ.erase k := by
          ext i; simp [ne_comm]
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_fin]
        omega
      · simp [hadj]
    simp_rw [hpoint, ← Finset.mul_sum]
  have hle :
      ∑ i : Fin (n + 1), ∑ b : Bool,
        2 * (G.comap (subcubeEmbed i b)).edgeFinset.card ≤
      ∑ _i : Fin (n + 1), ∑ _b : Bool, 2 * exC4 n := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
    exact Nat.mul_le_mul_left 2
      (card_le_exC4 _ (comap_subcubeEmbed_le_Q hG i b) (comap_subcubeEmbed_isC4Free hfree i b))
  rw [hway1] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin,
    smul_eq_mul] at hle
  linarith

/-- **Theorem 1.2 (`ppl033_subcube_averaging_step`):**
For every `n ≥ 1`, `n * ex(Q_{n+1}, C_4) ≤ 2 * (n + 1) * ex(Q_n, C_4)` (pure Mathlib signature). -/
theorem ppl033_subcube_averaging_step (n : ℕ) (_hn : 1 ≤ n) :
    open Classical in
    n * sSup { m : ℕ | ∃ G : SimpleGraph (Fin (n + 1) → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin (n + 1) → Bool =>
        (Finset.univ.filter (fun i : Fin (n + 1) => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = m } ≤
    2 * (n + 1) * sSup { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
        (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = m } := by
  classical
  change n * exC4 (n + 1) ≤ 2 * (n + 1) * exC4 n
  obtain ⟨G, hG, hfree, hcard⟩ := exists_exC4_witness (n + 1)
  rw [← hcard]
  exact subcube_averaging_graph G hG hfree

private lemma turan_density_step (n : ℕ) (hn : 1 ≤ n) :
    ((exC4 (n + 1) : ℝ) / (((n + 1) * 2 ^ n : ℕ) : ℝ)) ≤
      ((exC4 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ)) := by
  classical
  have hstep : n * exC4 (n + 1) ≤ 2 * (n + 1) * exC4 n := by
    obtain ⟨G, hG, hfree, hcard⟩ := exists_exC4_witness (n + 1)
    rw [← hcard]
    exact subcube_averaging_graph G hG hfree
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  have hpos1 : (0 : ℝ) < (((n + 1) * 2 ^ n : ℕ) : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hpos1 hpos2]
  have hcast : ((n * exC4 (n + 1) : ℕ) : ℝ) ≤ ((2 * (n + 1) * exC4 n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hstep
  push_cast at hcast ⊢
  rw [hpow]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := by positivity
  nlinarith

private lemma turan_density_antitone_aux {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((exC4 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ)) ≤
      ((exC4 m : ℝ) / ((m * 2 ^ (m - 1) : ℕ) : ℝ)) := by
  induction hmn with
  | refl => exact le_rfl
  | @step k hmk ih =>
    have hk : 1 ≤ k := le_trans hm hmk
    have h1 := turan_density_step k hk
    simpa [Nat.add_sub_cancel] using le_trans h1 ih

/-- **Theorem 1.3 (`ppl033_turan_density_antitone`):**
The Turán density `ex(Q_n, C_4) / |E(Q_n)|` is non-increasing for all `1 ≤ m ≤ n`
(pure Mathlib signature). -/
theorem ppl033_turan_density_antitone {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    open Classical in
    ((sSup { k : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
        G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
          (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
        (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
        G.edgeFinset.card = k } : ℕ) : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ) ≤
    ((sSup { k : ℕ | ∃ G : SimpleGraph (Fin m → Bool),
        G ≤ SimpleGraph.fromRel (fun u v : Fin m → Bool =>
          (Finset.univ.filter (fun i : Fin m => u i ≠ v i)).card = 1) ∧
        (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
        G.edgeFinset.card = k } : ℕ) : ℝ) / ((m * 2 ^ (m - 1) : ℕ) : ℝ) :=
  turan_density_antitone_aux hm hmn

end HypercubeFoundations

/-! ## Section 2: Explicit Lower Bounds (`1/2` Parity-Prefix & Brass–Harborth–Nienborg) -/

section ExplicitLowerBounds

/-- Prefix Hamming weight count before coordinate `i`. -/
private def prefixWeight {n : ℕ} (u : Fin n → Bool) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => j < i ∧ u j = true)).card

private lemma prefixWeight_flip_self {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    prefixWeight (flip u i) i = prefixWeight u i := by
  unfold prefixWeight
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨hji, hj⟩ <;> exact ⟨hji, by rwa [flip_apply_ne u (ne_of_lt hji)] at *⟩

private lemma prefixWeight_flip_lt_parity {n : ℕ} (u : Fin n → Bool) {i j : Fin n} (hji : j < i) :
    Even (prefixWeight (flip u j) i) ↔ ¬ Even (prefixWeight u i) := by
  unfold prefixWeight
  set S1 := Finset.univ.filter (fun k : Fin n => k < i ∧ u k = true)
  set S2 := Finset.univ.filter (fun k : Fin n => k < i ∧ flip u j k = true)
  cases huj : u j
  · have hj_not : j ∉ S1 := by simp [S1, huj]
    have hS2 : S2 = insert j S1 := by
      ext k
      simp only [S2, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hkj : k = j
      · subst hkj; simp [flip_apply_self, huj, hji]
      · simp [flip_apply_ne u hkj, hkj]
    rw [hS2, Finset.card_insert_of_notMem hj_not, Nat.even_add_one]
  · have hj_not : j ∉ S2 := by simp [S2, flip_apply_self, huj]
    have hS1 : S1 = insert j S2 := by
      ext k
      simp only [S2, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hkj : k = j
      · subst hkj; simp [huj, hji]
      · simp [flip_apply_ne u hkj, hkj]
    rw [hS1, Finset.card_insert_of_notMem hj_not, Nat.even_add_one, not_not]

private lemma card_even_prefixWeight {n : ℕ} (i : Fin n) (hi : 0 < i.1) :
    2 * (Finset.univ.filter (fun u : Fin n → Bool => Even (prefixWeight u i))).card = 2 ^ n := by
  let z : Fin n := ⟨0, lt_of_le_of_lt (Nat.zero_le _) i.2⟩
  have hzi : z < i := hi
  let S := Finset.univ.filter (fun u : Fin n → Bool => Even (prefixWeight u i))
  let T := Finset.univ.filter (fun u : Fin n → Bool => ¬ Even (prefixWeight u i))
  have hST : S.card = T.card := by
    refine Finset.card_bij (fun u _ => flip u z) ?_ ?_ ?_
    · intro u hu
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact (prefixWeight_flip_lt_parity u hzi).not.mpr (not_not.mpr hu)
    · intro u1 _ u2 _ h
      have := congrArg (fun v => flip v z) h
      simpa [flip_flip] using this
    · intro v hv
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨flip v z, ?_, flip_flip v z⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (prefixWeight_flip_lt_parity v hzi).mpr hv
  have hsum : S.card + T.card = 2 ^ n := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool)))
      (p := fun u => Even (prefixWeight u i))
    have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      simp [Fintype.card_pi]
    change S.card + T.card = _ at h1
    omega
  change 2 * S.card = 2 ^ n
  omega

/-- Parity-prefix `C_4`-free subgraph of `Q_n` with `(n + 1) * 2 ^ (n - 2)` edges for `n ≥ 2`. -/
private def parityPrefixGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := ∃ i : Fin n, v = flip u i ∧ Even (prefixWeight u i)
  symm := ⟨by
    rintro u v ⟨i, rfl, hev⟩
    refine ⟨i, (flip_flip u i).symm, ?_⟩
    rwa [prefixWeight_flip_self]⟩
  loopless := ⟨by
    rintro u ⟨i, h, _⟩
    exact flip_ne_self u i h.symm⟩

private lemma parityPrefixGraph_le_Q (n : ℕ) : parityPrefixGraph n ≤ Q n := by
  rintro u v ⟨i, rfl, _⟩
  exact Q_adj_flip u i

private lemma parityPrefixGraph_isC4Free (n : ℕ) : IsC4Free (parityPrefixGraph n) := by
  rw [isC4Free_iff_no_face (parityPrefixGraph_le_Q n)]
  intro u i j hij ⟨h1, h2, h3, h4⟩
  have h_ui : Even (prefixWeight u i) := by
    rcases h1 with ⟨k, hk, hev⟩
    have := flip_inj u hk
    subst this; exact hev
  have h_uj : Even (prefixWeight u j) := by
    rcases h4.symm with ⟨k, hk, hev⟩
    have := flip_inj u hk
    subst this; exact hev
  have h_uij : Even (prefixWeight (flip u i) j) := by
    rcases h2 with ⟨k, hk, hev⟩
    have := flip_inj (flip u i) hk
    subst this; exact hev
  have h_uji : Even (prefixWeight (flip u j) i) := by
    rcases h3.symm with ⟨k, hk, hev⟩
    rw [flip_comm] at hk
    have := flip_inj (flip u j) hk
    subst this; exact hev
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (prefixWeight_flip_lt_parity u hlt).mp h_uij h_uj
  · exact (prefixWeight_flip_lt_parity u hgt).mp h_uji h_ui

private lemma parityPrefixGraph_card_twice (n : ℕ) (hn : 1 ≤ n)
    [Fintype (parityPrefixGraph n).edgeSet] :
    2 * (parityPrefixGraph n).edgeFinset.card = (n + 1) * 2 ^ (n - 1) := by
  classical
  rw [twice_card_edges_eq_sum_oriented _ (parityPrefixGraph_le_Q n)]
  have hsimp : ∀ u : Fin n → Bool,
      (Finset.univ.filter (fun j : Fin n => (parityPrefixGraph n).Adj u (flip u j))).card =
      (Finset.univ.filter (fun j : Fin n => Even (prefixWeight u j))).card := by
    intro u; congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (∃ k : Fin n, flip u j = flip u k ∧ Even (prefixWeight u k)) ↔ Even (prefixWeight u j)
    constructor
    · rintro ⟨k, hk, hev⟩
      have := flip_inj u hk; subst this; exact hev
    · intro hev; exact ⟨j, rfl, hev⟩
  simp_rw [hsimp, Finset.card_filter]
  rw [Finset.sum_comm]
  have hterm : ∀ j : Fin n,
      (∑ u : Fin n → Bool, if Even (prefixWeight u j) then 1 else 0) =
      if j.1 = 0 then 2 ^ n else 2 ^ (n - 1) := by
    intro j
    rw [← Finset.card_filter]
    by_cases hj : j.1 = 0
    · simp only [hj, ↓reduceIte]
      have hall : ∀ u : Fin n → Bool, Even (prefixWeight u j) := by
        intro u
        have hemp : Finset.univ.filter (fun k : Fin n => k < j ∧ u k = true) = ∅ := by
          ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          intro hkj
          have : k.1 < j.1 := hkj
          omega
        simp [prefixWeight, hemp]
      simp [hall, Fintype.card_pi]
    · simp only [hj, ↓reduceIte]
      have hpos : 0 < j.1 := Nat.pos_of_ne_zero hj
      have h2 := card_even_prefixWeight j hpos
      have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        cases n with
        | zero => omega
        | succ k => simp [pow_succ, mul_comm]
      rw [hpow] at h2
      omega
  simp_rw [hterm]
  let z : Fin n := ⟨0, hn⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z)]
  have hz : (if z.1 = 0 then 2 ^ n else 2 ^ (n - 1)) = 2 ^ n := by simp [z]
  have hrest : ∑ x ∈ Finset.univ.erase z, (if x.1 = 0 then 2 ^ n else 2 ^ (n - 1)) =
      (n - 1) * 2 ^ (n - 1) := by
    have hcongr : ∀ x ∈ Finset.univ.erase z,
        (if x.1 = 0 then 2 ^ n else 2 ^ (n - 1)) = 2 ^ (n - 1) := by
      intro x hx
      have hne : x.1 ≠ 0 := by
        intro h0
        apply (Finset.mem_erase.mp hx).1
        exact Fin.ext h0
      simp [hne]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ z),
        Finset.card_fin, smul_eq_mul]
  rw [hz, hrest]
  cases n with
  | zero => omega
  | succ k =>
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    simp only [Nat.add_sub_cancel, hpow]
    ring

/-- **Theorem 2.1 (`ppl033_parity_prefix_lower`):**
For every `n ≥ 2`, there exists a `C_4`-free subgraph of `Q_n` with exactly `(n + 1) * 2 ^ (n - 2)`
edges (strictly beating `(1/2) * n * 2 ^ (n - 1)` by `2 ^ (n - 2)`). -/
theorem ppl033_parity_prefix_lower (n : ℕ) (hn : 2 ≤ n) :
    open Classical in
    ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
        (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = (n + 1) * 2 ^ (n - 2) := by
  classical
  refine ⟨parityPrefixGraph n, parityPrefixGraph_le_Q n, parityPrefixGraph_isC4Free n, ?_⟩
  have h2 := parityPrefixGraph_card_twice n (by omega)
  have hpow : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    have he : n - 1 = (n - 2) + 1 := by omega
    rw [he, pow_succ]; ring
  rw [hpow] at h2
  have h2' : 2 * (parityPrefixGraph n).edgeFinset.card = 2 * ((n + 1) * 2 ^ (n - 2)) := by
    linarith
  exact Nat.mul_left_cancel (by omega : 0 < 2) h2'

/-- Parity-prefix extension: extend any `C_4`-free `G_m ≤ Q_m` (`1 ≤ m ≤ n`) to a `C_4`-free
subgraph of `Q_n` with `2 * |E| = 2 ^ (n - m) * (2 * |E(G_m)|) + (n - m) * 2 ^ (n - 1)`. -/
private def extendByParity {m n : ℕ} (hmn : m ≤ n) (Gm : SimpleGraph (Fin m → Bool)) :
    SimpleGraph (Fin n → Bool) where
  Adj u v :=
    ∃ i : Fin n, v = flip u i ∧
      if hi : i.1 < m then
        Gm.Adj (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩)
               (flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨i.1, hi⟩)
      else
        Even (prefixWeight u i)
  symm := ⟨by
    rintro u v ⟨i, rfl, h⟩
    refine ⟨i, (flip_flip u i).symm, ?_⟩
    by_cases hi : i.1 < m
    · simp only [hi, ↓reduceDIte] at h ⊢
      have hres : (fun k : Fin m => flip u i ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) =
          flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨i.1, hi⟩ := by
        ext k
        by_cases hk : k.1 = i.1
        · have hke : (⟨k.1, lt_of_lt_of_le k.2 hmn⟩ : Fin n) = i := Fin.ext hk
          have hkm : k = ⟨i.1, hi⟩ := Fin.ext hk
          rw [hke, hkm, flip_apply_self, flip_apply_self]
        · have hke : (⟨k.1, lt_of_lt_of_le k.2 hmn⟩ : Fin n) ≠ i := fun he => hk (congrArg Fin.val he)
          have hkm : k ≠ ⟨i.1, hi⟩ := fun he => hk (congrArg Fin.val he)
          rw [flip_apply_ne u hke, flip_apply_ne _ hkm]
      rw [hres, flip_flip]
      exact h.symm
    · simp only [hi, ↓reduceDIte] at h ⊢
      rwa [prefixWeight_flip_self]⟩
  loopless := ⟨by
    rintro u ⟨i, h, _⟩
    exact flip_ne_self u i h.symm⟩

private lemma extendByParity_le_Q {m n : ℕ} (hmn : m ≤ n) (Gm : SimpleGraph (Fin m → Bool)) :
    extendByParity hmn Gm ≤ Q n := by
  rintro u v ⟨i, rfl, _⟩
  exact Q_adj_flip u i

private lemma extendByParity_isC4Free {m n : ℕ} (hmn : m ≤ n) {Gm : SimpleGraph (Fin m → Bool)}
    (hGm : Gm ≤ Q m) (hfree : IsC4Free Gm) :
    IsC4Free (extendByParity hmn Gm) := by
  rw [isC4Free_iff_no_face (extendByParity_le_Q hmn Gm)]
  intro u i j hij ⟨h1, h2, h3, h4⟩
  have hcond : ∀ (w : Fin n → Bool) (k : Fin n),
      (extendByParity hmn Gm).Adj w (flip w k) →
      if hk : k.1 < m then
        Gm.Adj (fun t : Fin m => w ⟨t.1, lt_of_lt_of_le t.2 hmn⟩)
               (flip (fun t : Fin m => w ⟨t.1, lt_of_lt_of_le t.2 hmn⟩) ⟨k.1, hk⟩)
      else
        Even (prefixWeight w k) := by
    intro w k ⟨l, hl, hc⟩
    have := flip_inj w hl
    subst this; exact hc
  have c1 := hcond u i h1
  have c2 := hcond (flip u i) j h2
  have c3 : (extendByParity hmn Gm).Adj (flip u j) (flip (flip u j) i) := by
    rw [flip_comm]; exact h3.symm
  have c3' := hcond (flip u j) i c3
  have c4 := hcond u j h4.symm
  by_cases hi : i.1 < m <;> by_cases hj : j.1 < m
  · simp only [hi, hj, ↓reduceDIte] at c1 c2 c3' c4
    let u0 : Fin m → Bool := fun t => u ⟨t.1, lt_of_lt_of_le t.2 hmn⟩
    let i0 : Fin m := ⟨i.1, hi⟩
    let j0 : Fin m := ⟨j.1, hj⟩
    have hij0 : i0 ≠ j0 := by
      intro h
      have hv : i0.1 = j0.1 := congrArg Fin.val h
      exact hij (Fin.ext hv)
    have hproj : ∀ (k : Fin n) (hk : k.1 < m),
        (fun t : Fin m => flip u k ⟨t.1, lt_of_lt_of_le t.2 hmn⟩) = flip u0 ⟨k.1, hk⟩ := by
      intro k hk; ext t
      by_cases ht : t.1 = k.1
      · have h1 : (⟨t.1, lt_of_lt_of_le t.2 hmn⟩ : Fin n) = k := Fin.ext ht
        have h2 : t = ⟨k.1, hk⟩ := Fin.ext ht
        rw [h1, h2, flip_apply_self, flip_apply_self]
      · have h1 : (⟨t.1, lt_of_lt_of_le t.2 hmn⟩ : Fin n) ≠ k := fun he => ht (congrArg Fin.val he)
        have h2 : t ≠ ⟨k.1, hk⟩ := fun he => ht (congrArg Fin.val he)
        rw [flip_apply_ne u h1, flip_apply_ne u0 h2]
    rw [hproj i hi] at c2
    rw [hproj j hj, flip_comm] at c3'
    exact (isC4Free_iff_no_face hGm).mp hfree u0 i0 j0 hij0 ⟨c1, c2, c3'.symm, c4.symm⟩
  · simp only [hj, ↓reduceDIte] at c2 c4
    have hlt : i < j := by show i.1 < j.1; omega
    exact (prefixWeight_flip_lt_parity u hlt).mp c2 c4
  · simp only [hi, ↓reduceDIte] at c1 c3'
    have hlt : j < i := by show j.1 < i.1; omega
    exact (prefixWeight_flip_lt_parity u hlt).mp c3' c1
  · simp only [hi, hj, ↓reduceDIte] at c1 c2 c3' c4
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact (prefixWeight_flip_lt_parity u hlt).mp c2 c4
    · exact (prefixWeight_flip_lt_parity u hgt).mp c3' c1

private lemma extendByParity_card_twice {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    {Gm : SimpleGraph (Fin m → Bool)} [Fintype Gm.edgeSet]
    [Fintype (extendByParity hmn Gm).edgeSet] (hGm : Gm ≤ Q m) :
    2 * (extendByParity hmn Gm).edgeFinset.card =
      2 ^ (n - m) * (2 * Gm.edgeFinset.card) + (n - m) * 2 ^ (n - 1) := by
  classical
  rw [twice_card_edges_eq_sum_oriented _ (extendByParity_le_Q hmn Gm)]
  have hsimp : ∀ u : Fin n → Bool,
      (Finset.univ.filter (fun j : Fin n => (extendByParity hmn Gm).Adj u (flip u j))).card =
      ∑ j : Fin n,
        if hj : j.1 < m then
          if Gm.Adj (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩)
                    (flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨j.1, hj⟩)
          then 1 else 0
        else
          if Even (prefixWeight u j) then 1 else 0 := by
    intro u
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hiff : (extendByParity hmn Gm).Adj u (flip u j) ↔
        if hj : j.1 < m then
          Gm.Adj (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩)
                 (flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨j.1, hj⟩)
        else
          Even (prefixWeight u j) := by
      constructor
      · rintro ⟨k, hk, hc⟩
        have := flip_inj u hk; subst this; exact hc
      · intro hc; exact ⟨j, rfl, hc⟩
    by_cases hj : j.1 < m <;> simp [hiff, hj]
  simp_rw [hsimp]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.1 < m)]
  congr 1
  · let splitEquiv : (Fin n → Bool) ≃ (Fin m → Bool) × (Fin (n - m) → Bool) :=
      { toFun := fun u =>
          (fun k => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩,
           fun k => u ⟨m + k.1, by omega⟩)
        invFun := fun p i =>
          if hi : i.1 < m then p.1 ⟨i.1, hi⟩ else p.2 ⟨i.1 - m, by omega⟩
        left_inv := fun u => by
          ext i
          by_cases hi : i.1 < m
          · simp [hi]
          · have hsub : m + (i.1 - m) = i.1 := by omega
            simp [hi, hsub]
        right_inv := fun ⟨a, b⟩ => by
          ext k
          · simp [k.2]
          · have hnot : ¬ (m + k.1 < m) := by omega
            have hsub : m + k.1 - m = k.1 := by omega
            simp [hnot, hsub] }
    have hlt_eq : ∀ j : Fin n, j ∈ Finset.univ.filter (fun j : Fin n => j.1 < m) →
        (∑ u : Fin n → Bool,
          if hj : j.1 < m then
            if Gm.Adj (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩)
                      (flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨j.1, hj⟩)
            then 1 else 0
          else if Even (prefixWeight u j) then 1 else 0) =
        2 ^ (n - m) * ∑ a : Fin m → Bool,
          if hj : j.1 < m then if Gm.Adj a (flip a ⟨j.1, hj⟩) then 1 else 0 else 0 := by
      intro j hjmem
      have hj : j.1 < m := (Finset.mem_filter.mp hjmem).2
      simp only [hj, ↓reduceDIte]
      have hsum_eq :
          (∑ u : Fin n → Bool,
            if Gm.Adj (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩)
                      (flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨j.1, hj⟩)
            then 1 else 0) =
          ∑ p : (Fin m → Bool) × (Fin (n - m) → Bool),
            if Gm.Adj p.1 (flip p.1 ⟨j.1, hj⟩) then 1 else 0 :=
        Fintype.sum_equiv splitEquiv _ _ (fun _ => rfl)
      rw [hsum_eq, Fintype.sum_prod_type, Finset.sum_comm]
      simp [Finset.sum_const, Fintype.card_pi]
    rw [Finset.sum_congr rfl hlt_eq, ← Finset.mul_sum]
    congr 1
    rw [twice_card_edges_eq_sum_oriented Gm hGm]
    simp_rw [Finset.card_filter]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_bij (fun (j : Fin n) (hj : j ∈ Finset.univ.filter (fun j : Fin n => j.1 < m)) =>
        (⟨j.1, (Finset.mem_filter.mp hj).2⟩ : Fin m)) ?_ ?_ ?_ ?_
    · intro j _; exact Finset.mem_univ _
    · intro j1 _ j2 _ h
      exact Fin.ext (congrArg (Fin.val : Fin m → ℕ) h)
    · intro k _
      exact ⟨⟨k.1, lt_of_lt_of_le k.2 hmn⟩, by simp [k.2], Fin.ext rfl⟩
    · intro j hj
      have hjlt : j.1 < m := (Finset.mem_filter.mp hj).2
      simp [hjlt]
  · have hge_eq : ∀ j : Fin n, j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j.1 < m)) →
        (∑ u : Fin n → Bool,
          if hj : j.1 < m then
            if Gm.Adj (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩)
                      (flip (fun k : Fin m => u ⟨k.1, lt_of_lt_of_le k.2 hmn⟩) ⟨j.1, hj⟩)
            then 1 else 0
          else if Even (prefixWeight u j) then 1 else 0) =
        2 ^ (n - 1) := by
      intro j hjmem
      have hj : ¬ (j.1 < m) := (Finset.mem_filter.mp hjmem).2
      simp only [hj, ↓reduceDIte, ← Finset.card_filter]
      have hpos : 0 < j.1 := by omega
      have h2 := card_even_prefixWeight j hpos
      have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
        cases n with
        | zero => omega
        | succ k => simp [pow_succ, mul_comm]
      rw [hpow] at h2
      omega
    rw [Finset.sum_congr rfl hge_eq, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← Fintype.card_fin (n - m), ← Finset.card_univ]
    refine Finset.card_bij (fun (j : Fin n) (hj : j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j.1 < m))) =>
        (⟨j.1 - m, by have := (Finset.mem_filter.mp hj).2; omega⟩ : Fin (n - m))) ?_ ?_ ?_
    · intro j _; exact Finset.mem_univ _
    · intro j1 hj1 j2 hj2 h
      have h1 : ¬ (j1.1 < m) := (Finset.mem_filter.mp hj1).2
      have h2 : ¬ (j2.1 < m) := (Finset.mem_filter.mp hj2).2
      have hv := congrArg Fin.val h
      dsimp at hv
      exact Fin.ext (by omega)
    · intro k _
      refine ⟨⟨m + k.1, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega

/-! ### Brass–Harborth–Nienborg (1995): Recursive `Q_4` 2-Coloring Product -/

/-- The 8 removed edges of `Q_4` (a perfect matching hitting every one of the 24 2-faces
of `Q_4` exactly once). Returns `true` iff the edge `{u, flip u i}` is KEPT in `H_4`. -/
private def keepEdge4 (u : Fin 4 → Bool) (i : Fin 4) : Bool :=
  match i with
  | ⟨0, _⟩ => !((u 1 == u 2) && (u 2 == u 3))
  | ⟨1, _⟩ => !((u 0 == u 2) && (u 2 != u 3))
  | ⟨2, _⟩ => !((u 0 != u 1) && (u 0 == u 3))
  | ⟨3, _⟩ => !((u 0 == u 1) && (u 1 != u 2))

private lemma keepEdge4_flip_self (u : Fin 4 → Bool) (i : Fin 4) :
    keepEdge4 (flip u i) i = keepEdge4 u i := by
  fin_cases i <;> simp [keepEdge4, flip]

/-- Every 2-face `(u, i, j)` (`i ≠ j`) of `Q_4` has EXACTLY 3 kept edges and 1 removed edge,
so at least one parallel pair has opposite `keepEdge4` truth values! -/
private lemma keepEdge4_face_not_mono (u : Fin 4 → Bool) (i j : Fin 4) (hij : i ≠ j) :
    (keepEdge4 u i ≠ keepEdge4 (flip u j) i) ∨ (keepEdge4 u j ≠ keepEdge4 (flip u i) j) := by
  have hall : ∀ (a b c d : Bool) (i j : Fin 4), i ≠ j →
      let u : Fin 4 → Bool := ![a, b, c, d]
      (keepEdge4 u i ≠ keepEdge4 (flip u j) i) ∨
      (keepEdge4 u j ≠ keepEdge4 (flip u i) j) := by
    decide
  have hu : u = ![u 0, u 1, u 2, u 3] := by
    ext k; fin_cases k <;> rfl
  rw [hu]
  exact hall (u 0) (u 1) (u 2) (u 3) i j hij

/-- Every 2-face `(u, i, j)` (`i ≠ j`) of `Q_4` has at least one removed edge (`H_4` is `C_4`-free). -/
private lemma keepEdge4_c4_free (u : Fin 4 → Bool) (i j : Fin 4) (hij : i ≠ j) :
    ¬ (keepEdge4 u i = true ∧ keepEdge4 (flip u i) j = true ∧
       keepEdge4 (flip u j) i = true ∧ keepEdge4 u j = true) := by
  rintro ⟨h1, h2, h3, h4⟩
  rcases keepEdge4_face_not_mono u i j hij with h | h
  · exact h (h1.trans h3.symm)
  · exact h (h4.trans h2.symm)

/-- In each direction `i : Fin 4`, exactly `12` of the `16` vertices `u : Fin 4 → Bool` satisfy
`keepEdge4 u i = true` (i.e., `6` of the `8` undirected edges in direction `i`). -/
private lemma keepEdge4_dir_count (i : Fin 4) :
    (Finset.univ.filter (fun u : Fin 4 → Bool => keepEdge4 u i = true)).card = 12 := by
  fin_cases i <;> decide

/-- Explicit `24`-edge `C_4`-free subgraph `H_4 ≤ Q_4`. -/
private def H4Graph : SimpleGraph (Fin 4 → Bool) where
  Adj u v := ∃ i : Fin 4, v = flip u i ∧ keepEdge4 u i = true
  symm := ⟨by
    rintro u v ⟨i, rfl, hk⟩
    exact ⟨i, (flip_flip u i).symm, by rwa [keepEdge4_flip_self]⟩⟩
  loopless := ⟨by
    rintro u ⟨i, h, _⟩
    exact flip_ne_self u i h.symm⟩

private lemma H4Graph_le_Q4 : H4Graph ≤ Q 4 := by
  rintro u v ⟨i, rfl, _⟩; exact Q_adj_flip u i

private lemma H4Graph_isC4Free : IsC4Free H4Graph := by
  rw [isC4Free_iff_no_face H4Graph_le_Q4]
  intro u i j hij ⟨h1, h2, h3, h4⟩
  have hk1 : keepEdge4 u i = true := by
    rcases h1 with ⟨l, hl, h⟩; have := flip_inj u hl; subst this; exact h
  have hk2 : keepEdge4 (flip u i) j = true := by
    rcases h2 with ⟨l, hl, h⟩; have := flip_inj (flip u i) hl; subst this; exact h
  have hk3 : keepEdge4 (flip u j) i = true := by
    rcases h3.symm with ⟨l, hl, h⟩; rw [flip_comm] at hl
    have := flip_inj (flip u j) hl; subst this; exact h
  have hk4 : keepEdge4 u j = true := by
    rcases h4.symm with ⟨l, hl, h⟩; have := flip_inj u hl; subst this; exact h
  exact keepEdge4_c4_free u i j hij ⟨hk1, hk2, hk3, hk4⟩

private lemma H4Graph_card [Fintype H4Graph.edgeSet] :
    H4Graph.edgeFinset.card = 24 := by
  classical
  have h2 := twice_card_edges_eq_sum_oriented H4Graph H4Graph_le_Q4
  have hsimp : ∀ u : Fin 4 → Bool,
      (Finset.univ.filter (fun j : Fin 4 => H4Graph.Adj u (flip u j))).card =
      (Finset.univ.filter (fun j : Fin 4 => keepEdge4 u j = true)).card := by
    intro u; congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (∃ l : Fin 4, flip u j = flip u l ∧ keepEdge4 u l = true) ↔ keepEdge4 u j = true
    constructor
    · rintro ⟨l, hl, hk⟩; have := flip_inj u hl; subst this; exact hk
    · intro hk; exact ⟨j, rfl, hk⟩
  simp_rw [hsimp, Finset.card_filter] at h2
  rw [Finset.sum_comm] at h2
  have hdir : ∀ j : Fin 4,
      (∑ u : Fin 4 → Bool, if keepEdge4 u j = true then 1 else 0) = 12 := by
    intro j
    rw [← Finset.card_filter]
    exact keepEdge4_dir_count j
  simp_rw [hdir] at h2
  simp at h2
  omega

/-- Parity of a binary vector `u : Fin k → Bool` (`Bool`: `true` iff odd Hamming weight). -/
private def vecParity {k : ℕ} (u : Fin k → Bool) : Bool :=
  (Finset.univ.filter (fun i : Fin k => u i = true)).card % 2 == 1

private lemma vecParity_flip {k : ℕ} (u : Fin k → Bool) (i : Fin k) :
    vecParity (flip u i) = !vecParity u := by
  unfold vecParity
  set S1 := Finset.univ.filter (fun j : Fin k => u j = true)
  set S2 := Finset.univ.filter (fun j : Fin k => flip u i j = true)
  cases hui : u i
  · have hi : i ∉ S1 := by simp [S1, hui]
    have hS2 : S2 = insert i S1 := by
      ext j; simp only [S2, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hji : j = i
      · subst hji; simp [flip_apply_self, hui]
      · simp [flip_apply_ne u hji, hji]
    rw [hS2, Finset.card_insert_of_notMem hi]
    cases Nat.mod_two_eq_zero_or_one S1.card with
    | inl h => simp [Nat.add_mod, h]
    | inr h => simp [Nat.add_mod, h]
  · have hi : i ∉ S2 := by simp [S2, flip_apply_self, hui]
    have hS1 : S1 = insert i S2 := by
      ext j; simp only [S2, S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hji : j = i
      · subst hji; simp [hui]
      · simp [flip_apply_ne u hji, hji]
    rw [hS1, Finset.card_insert_of_notMem hi]
    cases Nat.mod_two_eq_zero_or_one S2.card with
    | inl h => simp [Nat.add_mod, h]
    | inr h => simp [Nat.add_mod, h]

private lemma card_vecParity_eq {k : ℕ} (hk : 1 ≤ k) (b : Bool) :
    (Finset.univ.filter (fun u : Fin k → Bool => vecParity u = b)).card = 2 ^ (k - 1) := by
  let z : Fin k := ⟨0, hk⟩
  let S := Finset.univ.filter (fun u : Fin k → Bool => vecParity u = b)
  let T := Finset.univ.filter (fun u : Fin k → Bool => vecParity u = !b)
  have hST : S.card = T.card := by
    refine Finset.card_bij (fun u _ => flip u z) ?_ ?_ ?_
    · intro u hu
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [vecParity_flip, hu]
    · intro u1 _ u2 _ h
      have := congrArg (fun v => flip v z) h
      simpa [flip_flip] using this
    · intro v hv
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨flip v z, ?_, flip_flip v z⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [vecParity_flip, hv, Bool.not_not]
  have hsum : S.card + T.card = 2 ^ k := by
    rw [← Finset.card_union_of_disjoint]
    · have : S ∪ T = Finset.univ := by
        ext u; simp only [S, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          iff_true]
        cases vecParity u <;> cases b <;> simp
      rw [this, Finset.card_univ, Fintype.card_pi]; simp
    · rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
      rw [hu1] at hu2
      exact Bool.not_ne_self b hu2.symm
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    cases k with
    | zero => omega
    | succ m => simp [pow_succ, mul_comm]
  change S.card = 2 ^ (k - 1)
  omega

/-- Complement of `G ≤ Q_k` inside `Q_k`. -/
private def QComp {k : ℕ} (G : SimpleGraph (Fin k → Bool)) : SimpleGraph (Fin k → Bool) where
  Adj u v := (Q k).Adj u v ∧ ¬ G.Adj u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hg => h.2 hg.symm⟩⟩
  loopless := ⟨fun u h => (Q k).loopless.irrefl u h.1⟩

private lemma QComp_le_Q {k : ℕ} (G : SimpleGraph (Fin k → Bool)) : QComp G ≤ Q k :=
  fun _ _ h => h.1

/-- Equivalence between `Fin (4 * k) → Bool` and `Fin 4 → (Fin k → Bool)`. -/
private def cube4Equiv (k : ℕ) : (Fin (4 * k) → Bool) ≃ (Fin 4 → (Fin k → Bool)) where
  toFun u a b := u (finProdFinEquiv (a, b))
  invFun U i := U (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv u := by
    ext i
    change u (finProdFinEquiv (finProdFinEquiv.symm i)) = u i
    rw [finProdFinEquiv.apply_symm_apply]
  right_inv U := by
    ext a b
    change U (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1
             (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = U a b
    rw [finProdFinEquiv.symm_apply_apply]

private lemma cube4Equiv_flip {k : ℕ} (u : Fin (4 * k) → Bool) (a : Fin 4) (b : Fin k) :
    cube4Equiv k (flip u (finProdFinEquiv (a, b))) =
      Function.update (cube4Equiv k u) a (flip (cube4Equiv k u a) b) := by
  ext a' b'
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp [cube4Equiv, flip]
    · have hne : finProdFinEquiv (a', b') ≠ finProdFinEquiv (a', b) := by
        intro h; exact hb (congrArg Prod.snd (finProdFinEquiv.injective h))
      simp [cube4Equiv, flip, hb, hne]
  · have hne : finProdFinEquiv (a', b') ≠ finProdFinEquiv (a, b) := by
      intro h; exact ha (congrArg Prod.fst (finProdFinEquiv.injective h))
    simp [cube4Equiv, flip, ha, hne]

/-- Block-parity projection `Q_{4k} → Q_4`. -/
private def blockParities {k : ℕ} (u : Fin (4 * k) → Bool) : Fin 4 → Bool :=
  fun a => vecParity (cube4Equiv k u a)

private lemma blockParities_flip {k : ℕ} (u : Fin (4 * k) → Bool) (a : Fin 4) (b : Fin k) :
    blockParities (flip u (finProdFinEquiv (a, b))) = flip (blockParities u) a := by
  ext a'
  unfold blockParities
  rw [cube4Equiv_flip]
  by_cases ha : a' = a
  · subst ha
    simp only [Function.update_self, flip_apply_self]
    exact vecParity_flip (cube4Equiv k u a') b
  · simp [flip, ha]

/-- **Brass–Harborth–Nienborg (1995) Recursive `Q_4`-Product Graph `bhnStep G ≤ Q_{4k}`:**
Given `G ≤ Q_k`, an edge of `Q_{4k}` in block `a` flipping coordinate `b` is included iff
`(keepEdge4 (blockParities u) a = true) ↔ G.Adj (u_a) (flip u_a b)`. -/
private def bhnStep {k : ℕ} (G : SimpleGraph (Fin k → Bool)) :
    SimpleGraph (Fin (4 * k) → Bool) where
  Adj u v :=
    ∃ (a : Fin 4) (b : Fin k), v = flip u (finProdFinEquiv (a, b)) ∧
      ((keepEdge4 (blockParities u) a = true) ↔
        G.Adj (cube4Equiv k u a) (flip (cube4Equiv k u a) b))
  symm := ⟨by
    rintro u v ⟨a, b, rfl, hiff⟩
    refine ⟨a, b, (flip_flip u _).symm, ?_⟩
    rw [blockParities_flip, keepEdge4_flip_self, cube4Equiv_flip]
    simp only [Function.update_self, flip_flip]
    exact hiff.trans ⟨fun h => h.symm, fun h => h.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨a, b, h, _⟩
    exact flip_ne_self u _ h.symm⟩

private lemma bhnStep_le_Q {k : ℕ} (G : SimpleGraph (Fin k → Bool)) :
    bhnStep G ≤ Q (4 * k) := by
  rintro u v ⟨a, b, rfl, _⟩
  exact Q_adj_flip u _

private lemma bhnStep_adj_flip_iff {k : ℕ} (G : SimpleGraph (Fin k → Bool))
    (u : Fin (4 * k) → Bool) (a : Fin 4) (b : Fin k) :
    (bhnStep G).Adj u (flip u (finProdFinEquiv (a, b))) ↔
      ((keepEdge4 (blockParities u) a = true) ↔
        G.Adj (cube4Equiv k u a) (flip (cube4Equiv k u a) b)) := by
  constructor
  · rintro ⟨a', b', heq, hiff⟩
    have hp := finProdFinEquiv.injective (flip_inj u heq)
    cases hp
    exact hiff
  · intro hiff
    exact ⟨a, b, rfl, hiff⟩

/-- Both `bhnStep G` AND its complement `QComp (bhnStep G)` are `C_4`-free whenever
both `G` and `QComp G` are `C_4`-free! -/
private lemma bhnStep_double_c4_free {k : ℕ} {G : SimpleGraph (Fin k → Bool)}
    (hG : G ≤ Q k) (hfreeG : IsC4Free G) (hfreeC : IsC4Free (QComp G)) :
    IsC4Free (bhnStep G) ∧ IsC4Free (QComp (bhnStep G)) := by
  have hunified : ∀ (pol : Bool) (u : Fin (4 * k) → Bool) (i j : Fin (4 * k)), i ≠ j →
      ¬ (((bhnStep G).Adj u (flip u i) ↔ pol = true) ∧
         ((bhnStep G).Adj (flip u i) (flip (flip u i) j) ↔ pol = true) ∧
         ((bhnStep G).Adj (flip u j) (flip (flip u j) i) ↔ pol = true) ∧
         ((bhnStep G).Adj u (flip u j) ↔ pol = true)) := by
    intro pol u i j hij ⟨h1, h2, h3, h4⟩
    let p1 := finProdFinEquiv.symm i
    let p2 := finProdFinEquiv.symm j
    have hi : i = finProdFinEquiv (p1.1, p1.2) := (finProdFinEquiv.apply_symm_apply i).symm
    have hj : j = finProdFinEquiv (p2.1, p2.2) := (finProdFinEquiv.apply_symm_apply j).symm
    let a1 := p1.1; let b1 := p1.2; let a2 := p2.1; let b2 := p2.2
    rw [hi] at hij h1 h2 h3
    rw [hj] at hij h2 h3 h4
    rw [bhnStep_adj_flip_iff] at h1 h2 h3 h4
    rw [blockParities_flip, cube4Equiv_flip] at h2 h3
    by_cases ha : a1 = a2
    · have hb : b1 ≠ b2 := fun h => hij (by simp [a1, a2, b1, b2, ha, h])
      dsimp only [a1, a2, b1, b2] at ha hb
      rw [← ha] at h2 h3 h4
      simp only [keepEdge4_flip_self, Function.update_self] at h2 h3
      set x := cube4Equiv k u p1.1
      set flag := keepEdge4 (blockParities u) p1.1
      cases hfp : (flag == pol)
      · have hn1 : ¬ G.Adj x (flip x p1.2) := by cases flag <;> cases pol <;> simp_all
        have hn2 : ¬ G.Adj (flip x p1.2) (flip (flip x p1.2) p2.2) := by cases flag <;> cases pol <;> simp_all
        have hn3 : ¬ G.Adj (flip x p2.2) (flip (flip x p2.2) p1.2) := by cases flag <;> cases pol <;> simp_all
        have hn4 : ¬ G.Adj x (flip x p2.2) := by cases flag <;> cases pol <;> simp_all
        refine (isC4Free_iff_no_face (QComp_le_Q G)).mp hfreeC x p1.2 p2.2 hb ?_
        refine ⟨⟨Q_adj_flip _ _, hn1⟩, ⟨Q_adj_flip _ _, hn2⟩, ?_,
          ⟨(Q_adj_flip _ _).symm, fun h => hn4 h.symm⟩⟩
        rw [flip_comm]
        exact ⟨(Q_adj_flip _ _).symm, fun h => hn3 h.symm⟩
      · have hg1 : G.Adj x (flip x p1.2) := by cases flag <;> cases pol <;> simp_all
        have hg2 : G.Adj (flip x p1.2) (flip (flip x p1.2) p2.2) := by cases flag <;> cases pol <;> simp_all
        have hg3 : G.Adj (flip x p2.2) (flip (flip x p2.2) p1.2) := by cases flag <;> cases pol <;> simp_all
        have hg4 : G.Adj x (flip x p2.2) := by cases flag <;> cases pol <;> simp_all
        refine (isC4Free_iff_no_face hG).mp hfreeG x p1.2 p2.2 hb ?_
        refine ⟨hg1, hg2, ?_, hg4.symm⟩
        rw [flip_comm]
        exact hg3.symm
    · have ha12 : p1.1 ≠ p2.1 := ha
      have ha21 : p2.1 ≠ p1.1 := Ne.symm ha12
      simp only [Function.update_of_ne ha21, Function.update_of_ne ha12] at h2 h3
      rcases keepEdge4_face_not_mono (blockParities u) p1.1 p2.1 ha12 with hdiff | hdiff
      · cases pol <;>
        cases hka : keepEdge4 (blockParities u) p1.1 <;>
        cases hkb : keepEdge4 (flip (blockParities u) p2.1) p1.1 <;>
        (simp_all; try tauto)
      · cases pol <;>
        cases hka : keepEdge4 (blockParities u) p2.1 <;>
        cases hkb : keepEdge4 (flip (blockParities u) p1.1) p2.1 <;>
        (simp_all; try tauto)
  constructor
  · rw [isC4Free_iff_no_face (bhnStep_le_Q G)]
    intro u i j hij ⟨h1, h2, h3, h4⟩
    apply hunified true u i j hij
    refine ⟨by simp [h1], by simp [h2], ?_, by simp [h4.symm]⟩
    rw [flip_comm]; simp [h3.symm]
  · rw [isC4Free_iff_no_face (QComp_le_Q (bhnStep G))]
    intro u i j hij ⟨h1, h2, h3, h4⟩
    apply hunified false u i j hij
    have hn1 : ¬ (bhnStep G).Adj u (flip u i) := h1.2
    have hn2 : ¬ (bhnStep G).Adj (flip u i) (flip (flip u i) j) := h2.2
    have hn3 : ¬ (bhnStep G).Adj (flip u j) (flip (flip u j) i) := by
      intro h
      apply h3.2
      rw [flip_comm]
      exact h.symm
    have hn4 : ¬ (bhnStep G).Adj u (flip u j) := fun h => h4.2 h.symm
    exact ⟨by simp [hn1], by simp [hn2], by simp [hn3], by simp [hn4]⟩

/-- Exact edge count of `bhnStep G`:
`2 * |E(bhnStep G)| = 2 ^ (3 * k) * (2 * (2 * |E(G)|) + k * 2 ^ k)`. -/
private lemma bhnStep_card_twice {k : ℕ} (hk : 1 ≤ k) {G : SimpleGraph (Fin k → Bool)}
    [Fintype G.edgeSet] [Fintype (bhnStep G).edgeSet] (hG : G ≤ Q k) :
    2 * (bhnStep G).edgeFinset.card =
      2 ^ (3 * k) * (2 * (2 * G.edgeFinset.card) + k * 2 ^ k) := by
  classical
  rw [twice_card_edges_eq_sum_oriented _ (bhnStep_le_Q G)]
  have h1 :
      ∑ u : Fin (4 * k) → Bool,
        (Finset.univ.filter (fun j : Fin (4 * k) => (bhnStep G).Adj u (flip u j))).card =
      ∑ a : Fin 4, ∑ U : Fin 4 → (Fin k → Bool),
        (Finset.univ.filter (fun b : Fin k =>
          (keepEdge4 (fun d => vecParity (U d)) a = true) ↔ G.Adj (U a) (flip (U a) b))).card := by
    have hinner : ∀ u : Fin (4 * k) → Bool,
        (Finset.univ.filter (fun j : Fin (4 * k) => (bhnStep G).Adj u (flip u j))).card =
        ∑ a : Fin 4,
          (Finset.univ.filter (fun b : Fin k =>
            (keepEdge4 (blockParities u) a = true) ↔
              G.Adj (cube4Equiv k u a) (flip (cube4Equiv k u a) b))).card := by
      intro u
      simp_rw [Finset.card_filter]
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv finProdFinEquiv.symm _ _ fun j => ?_
      have hj : j = finProdFinEquiv (finProdFinEquiv.symm j) :=
        (finProdFinEquiv.apply_symm_apply j).symm
      conv_lhs => rw [hj]
      rw [bhnStep_adj_flip_iff]
      simp
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Fintype.sum_equiv (cube4Equiv k) _ _ (fun u => rfl)
  rw [h1]
  have hdir : ∀ a : Fin 4,
      ∑ U : Fin 4 → (Fin k → Bool),
        (Finset.univ.filter (fun b : Fin k =>
          (keepEdge4 (fun d => vecParity (U d)) a = true) ↔ G.Adj (U a) (flip (U a) b))).card =
      2 ^ (3 * k - 2) * (3 * (2 * G.edgeFinset.card) + (k * 2 ^ k - 2 * G.edgeFinset.card)) := by
    intro a
    let splitA : (Fin 4 → (Fin k → Bool)) ≃ (Fin k → Bool) × ({d : Fin 4 // d ≠ a} → (Fin k → Bool)) :=
      { toFun := fun U => (U a, fun d => U d.1)
        invFun := fun p d => if hd : d = a then p.1 else p.2 ⟨d, hd⟩
        left_inv := fun U => by ext d b; by_cases hd : d = a <;> simp [hd]
        right_inv := fun ⟨x, y⟩ => by
          ext
          · simp
          · rename_i d b; simp [d.2] }
    have hke_indep : ∀ (x : Fin k → Bool) (y : {d : Fin 4 // d ≠ a} → (Fin k → Bool)),
        keepEdge4 (fun d => vecParity (splitA.symm (x, y) d)) a =
        keepEdge4 (fun d => if hd : d = a then false else vecParity (y ⟨d, hd⟩)) a := by
      intro x y
      set p1 : Fin 4 → Bool := fun d => vecParity (splitA.symm (x, y) d)
      set p2 : Fin 4 → Bool := fun d => if hd : d = a then false else vecParity (y ⟨d, hd⟩)
      have hdiff : p1 = p2 ∨ p1 = flip p2 a := by
        cases hpa : p1 a
        · left; ext d; by_cases hd : d = a
          · subst hd; simp [p2, hpa]
          · simp [p1, p2, splitA, hd]
        · right; ext d; by_cases hd : d = a
          · subst hd; simp [p2, flip, hpa]
          · simp [p1, p2, splitA, flip, hd]
      rcases hdiff with h | h
      · rw [h]
      · rw [h, keepEdge4_flip_self]
    rw [Fintype.sum_equiv splitA _ (fun p =>
      (Finset.univ.filter (fun b : Fin k =>
        (keepEdge4 (fun d => if hd : d = a then false else vecParity (p.2 ⟨d, hd⟩)) a = true) ↔
          G.Adj p.1 (flip p.1 b))).card) (fun U => by
            have hinv : splitA.symm (splitA U) = U := splitA.symm_apply_apply U
            have hke := hke_indep (splitA U).1 (splitA U).2
            rw [hinv] at hke
            dsimp [splitA] at hke ⊢
            rw [hke])]
    rw [Fintype.sum_prod_type_right]
    have hsum_true :
        ∑ x : Fin k → Bool, (Finset.univ.filter (fun b : Fin k => G.Adj x (flip x b))).card =
        2 * G.edgeFinset.card :=
      (twice_card_edges_eq_sum_oriented G hG).symm
    have hsum_false :
        ∑ x : Fin k → Bool, (Finset.univ.filter (fun b : Fin k => ¬ G.Adj x (flip x b))).card =
        k * 2 ^ k - 2 * G.edgeFinset.card := by
      have htot :
          (∑ x : Fin k → Bool, (Finset.univ.filter (fun b : Fin k => G.Adj x (flip x b))).card) +
          (∑ x : Fin k → Bool, (Finset.univ.filter (fun b : Fin k => ¬ G.Adj x (flip x b))).card) =
          k * 2 ^ k := by
        rw [← Finset.sum_add_distrib]
        have hp : ∀ x : Fin k → Bool,
            (Finset.univ.filter (fun b : Fin k => G.Adj x (flip x b))).card +
            (Finset.univ.filter (fun b : Fin k => ¬ G.Adj x (flip x b))).card = k := by
          intro x
          rw [Finset.card_filter_add_card_filter_not, Finset.card_fin]
        simp_rw [hp]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, smul_eq_mul, mul_comm]
        simp
      omega
    let P (y : {d : Fin 4 // d ≠ a} → (Fin k → Bool)) : Bool :=
      keepEdge4 (fun d => if hd : d = a then false else vecParity (y ⟨d, hd⟩)) a
    have hinner_y : ∀ y : {d : Fin 4 // d ≠ a} → (Fin k → Bool),
        (∑ x : Fin k → Bool, (Finset.univ.filter (fun b : Fin k =>
          (P y = true) ↔ G.Adj x (flip x b))).card) =
        if P y = true then 2 * G.edgeFinset.card else k * 2 ^ k - 2 * G.edgeFinset.card := by
      intro y
      cases hpy : P y
      · simp only [Bool.false_eq_true, false_iff, ↓reduceIte]
        exact hsum_false
      · simp only [true_iff, ↓reduceIte]
        exact hsum_true
    change (∑ y : {d : Fin 4 // d ≠ a} → (Fin k → Bool),
        ∑ x : Fin k → Bool, (Finset.univ.filter (fun b : Fin k =>
          (P y = true) ↔ G.Adj x (flip x b))).card) = _
    simp_rw [hinner_y]
    let S_true := Finset.univ.filter (fun y : {d : Fin 4 // d ≠ a} → (Fin k → Bool) => P y = true)
    let S_false := Finset.univ.filter (fun y : {d : Fin 4 // d ≠ a} → (Fin k → Bool) => P y = false)
    have hsplit_y :
        (∑ y : {d : Fin 4 // d ≠ a} → (Fin k → Bool),
          if P y = true then 2 * G.edgeFinset.card else k * 2 ^ k - 2 * G.edgeFinset.card) =
        S_true.card * (2 * G.edgeFinset.card) +
        S_false.card * (k * 2 ^ k - 2 * G.edgeFinset.card) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => P y = true)]
      have hsf : Finset.univ.filter (fun y => ¬ (P y = true)) = S_false := by
        ext y; simp [S_false]
      rw [hsf]
      congr 1
      · rw [Finset.sum_congr rfl (fun y hy => if_pos (Finset.mem_filter.mp hy).2),
            Finset.sum_const, smul_eq_mul]
      · rw [Finset.sum_congr rfl (fun y hy => if_neg (by
              have hpy : P y = false := (Finset.mem_filter.mp hy).2
              simp [hpy])),
            Finset.sum_const, smul_eq_mul]
    rw [hsplit_y]
    have hfiber_card : ∀ (p : {d : Fin 4 // d ≠ a} → Bool),
        (Finset.univ.filter (fun y : {d : Fin 4 // d ≠ a} → (Fin k → Bool) =>
          (fun d => vecParity (y d)) = p)).card = 2 ^ (3 * (k - 1)) := by
      intro p
      have heq : Finset.univ.filter (fun y : {d : Fin 4 // d ≠ a} → (Fin k → Bool) =>
          (fun d => vecParity (y d)) = p) =
        Fintype.piFinset (fun d : {d : Fin 4 // d ≠ a} =>
          Finset.univ.filter (fun x : Fin k → Bool => vecParity x = p d)) := by
        ext y; simp [Fintype.mem_piFinset, funext_iff]
      rw [heq, Fintype.card_piFinset]
      simp_rw [card_vecParity_eq hk]
      rw [Finset.prod_const]
      have hcard_sub : (Finset.univ : Finset {d : Fin 4 // d ≠ a}).card = 3 := by
        fin_cases a <;> decide
      rw [hcard_sub, ← pow_mul, mul_comm]
    have hcount_p :
        (Finset.univ.filter (fun p : {d : Fin 4 // d ≠ a} → Bool =>
          keepEdge4 (fun d => if hd : d = a then false else p ⟨d, hd⟩) a = true)).card = 6 := by
      fin_cases a <;> decide
    have hS_true_card : S_true.card = 3 * 2 ^ (3 * k - 2) := by
      have hbi : S_true.card =
          ∑ p ∈ Finset.univ.filter (fun p : {d : Fin 4 // d ≠ a} → Bool =>
              keepEdge4 (fun d => if hd : d = a then false else p ⟨d, hd⟩) a = true),
            (Finset.univ.filter (fun y : {d : Fin 4 // d ≠ a} → (Fin k → Bool) =>
              (fun d => vecParity (y d)) = p)).card := by
        rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to
              (g := fun y d => vecParity (y d)) (t := Finset.univ.filter (fun p : {d : Fin 4 // d ≠ a} → Bool =>
                keepEdge4 (fun d => if hd : d = a then false else p ⟨d, hd⟩) a = true))]
        · refine Finset.sum_congr rfl fun p hp => ?_
          rw [← Finset.card_eq_sum_ones]
          congr 1; ext y
          simp only [S_true, P, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          constructor
          · intro h; exact h.2
          · intro h; refine ⟨?_, h⟩; rw [← h] at hp; exact hp
        · intro y hy
          simp only [S_true, P, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          exact hy
      rw [hbi]
      simp_rw [hfiber_card, Finset.sum_const, hcount_p, smul_eq_mul]
      have he : 3 * k - 2 = 3 * (k - 1) + 1 := by omega
      rw [he, pow_succ]; ring
    have hS_false_card : S_false.card = 2 ^ (3 * k - 2) := by
      have htot : S_true.card + S_false.card = 2 ^ (3 * k) := by
        rw [← Finset.card_union_of_disjoint]
        · have : S_true ∪ S_false = Finset.univ := by
            ext y; simp only [S_true, S_false, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
              true_and, iff_true]
            cases P y <;> simp
          rw [this, Finset.card_univ, Fintype.card_pi]
          have hcard_sub : (Finset.univ : Finset {d : Fin 4 // d ≠ a}).card = 3 := by
            fin_cases a <;> decide
          simp [Fintype.card_pi, hcard_sub, ← pow_mul, mul_comm]
        · rw [Finset.disjoint_left]
          intro y h1 h2
          simp only [S_true, S_false, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          rw [h1] at h2; exact Bool.false_ne_true h2.symm
      have hpow : 2 ^ (3 * k) = 4 * 2 ^ (3 * k - 2) := by
        have he : 3 * k = (3 * k - 2) + 2 := by omega
        conv_lhs => rw [he]
        rw [pow_add]; ring
      omega
    rw [hS_true_card, hS_false_card]
    ring
  simp_rw [hdir, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hleQ : 2 * G.edgeFinset.card ≤ k * 2 ^ k := by
    have h1 : G.edgeFinset.card ≤ k * 2 ^ (k - 1) := by
      calc G.edgeFinset.card
          ≤ (Q k).edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hG)
        _ = k * 2 ^ (k - 1) := Q_edgeFinset_card k
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
      cases k with
      | zero => omega
      | succ m => simp [pow_succ, mul_comm]
    rw [hpow]; linarith
  have hpow4 : 4 * 2 ^ (3 * k - 2) = 2 ^ (3 * k) := by
    have he : 3 * k = (3 * k - 2) + 2 := by omega
    conv_rhs => rw [he]
    rw [pow_add]; ring
  calc 4 * (2 ^ (3 * k - 2) * (3 * (2 * G.edgeFinset.card) + (k * 2 ^ k - 2 * G.edgeFinset.card)))
      = (4 * 2 ^ (3 * k - 2)) * (3 * (2 * G.edgeFinset.card) + (k * 2 ^ k - 2 * G.edgeFinset.card)) := by ring
    _ = 2 ^ (3 * k) * (2 * (2 * G.edgeFinset.card) + k * 2 ^ k) := by
        rw [hpow4]; congr 1; omega

/-- Inductive Brass–Harborth–Nienborg family on `Q_{4^r}`: both `G` and `QComp G` are `C_4`-free,
with exact edge count `2 * |E(G)| = (4^r + 2^r) * 2 ^ (4^r - 1)`. -/
private lemma bhn_family_exists (r : ℕ) :
    open Classical in
    ∃ G : SimpleGraph (Fin (4 ^ r) → Bool),
      G ≤ Q (4 ^ r) ∧ IsC4Free G ∧ IsC4Free (QComp G) ∧
      2 * G.edgeFinset.card = (4 ^ r + 2 ^ r) * 2 ^ (4 ^ r - 1) := by
  classical
  induction r with
  | zero =>
    refine ⟨Q 1, le_rfl, ?_, ?_, ?_⟩
    · rw [isC4Free_iff_no_face le_rfl]
      intro u i j hij
      exact absurd (Subsingleton.elim i j) hij
    · rw [isC4Free_iff_no_face (QComp_le_Q (Q 1))]
      intro u i j hij
      exact absurd (Subsingleton.elim i j) hij
    · simp [Q_edgeFinset_card]
  | succ r ih =>
    obtain ⟨G, hG, hfreeG, hfreeC, hcard⟩ := ih
    have hk : 1 ≤ 4 ^ r := Nat.one_le_pow r 4 (by omega)
    have h4pow : 4 ^ (r + 1) = 4 * 4 ^ r := by ring
    let eV : (Fin (4 ^ (r + 1)) → Bool) ≃ (Fin (4 * 4 ^ r) → Bool) :=
      Equiv.arrowCongr (finCongr h4pow) (Equiv.refl Bool)
    refine ⟨(bhnStep G).comap eV, ?_, ?_, ?_, ?_⟩
    · intro u v huv
      have hq : (Q (4 * 4 ^ r)).Adj (eV u) (eV v) := bhnStep_le_Q G huv
      rw [Q_adj_iff] at hq ⊢
      convert hq using 1
      refine Finset.card_bij (fun i _ => finCongr h4pow i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        simpa [eV, Equiv.arrowCongr] using hi
      · intro i1 _ i2 _ h; exact (finCongr h4pow).injective h
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        refine ⟨(finCongr h4pow).symm j, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [eV, Equiv.arrowCongr] using hj
    · intro a b c d hac hbd ⟨h1, h2, h3, h4⟩
      exact (bhnStep_double_c4_free hG hfreeG hfreeC).1 _ _ _ _
        (fun h => hac (eV.injective h)) (fun h => hbd (eV.injective h)) ⟨h1, h2, h3, h4⟩
    · intro a b c d hac hbd ⟨h1, h2, h3, h4⟩
      have hmap : ∀ {x y : Fin (4 ^ (r + 1)) → Bool},
          (QComp ((bhnStep G).comap eV)).Adj x y →
          (QComp (bhnStep G)).Adj (eV x) (eV y) := by
        intro x y ⟨hxq, hxng⟩
        refine ⟨?_, hxng⟩
        rw [Q_adj_iff] at hxq ⊢
        convert hxq using 1
        symm
        refine Finset.card_bij (fun i _ => finCongr h4pow i) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          simpa [eV, Equiv.arrowCongr] using hi
        · intro i1 _ i2 _ h; exact (finCongr h4pow).injective h
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          refine ⟨(finCongr h4pow).symm j, ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [eV, Equiv.arrowCongr] using hj
      exact (bhnStep_double_c4_free hG hfreeG hfreeC).2 _ _ _ _
        (fun h => hac (eV.injective h)) (fun h => hbd (eV.injective h))
        ⟨hmap h1, hmap h2, hmap h3, hmap h4⟩
    · have hiso : ((bhnStep G).comap eV).edgeFinset.card = (bhnStep G).edgeFinset.card := by
        refine Finset.card_bij (fun e _ => Sym2.map eV e) ?_ ?_ ?_
        · intro e he
          rw [SimpleGraph.mem_edgeFinset] at he ⊢
          induction e using Sym2.ind with
          | _ x y => exact he
        · intro e1 _ e2 _ h
          exact Sym2.map.injective eV.injective h
        · intro e he
          rw [SimpleGraph.mem_edgeFinset] at he
          refine ⟨Sym2.map eV.symm e, ?_, ?_⟩
          · rw [SimpleGraph.mem_edgeFinset]
            induction e using Sym2.ind with
            | _ x y => simpa [SimpleGraph.comap_adj] using he
          · rw [Sym2.map_map]
            have : (eV ∘ eV.symm) = id := funext (fun x => eV.apply_symm_apply x)
            rw [this, Sym2.map_id]
            rfl
      rw [edgeFinset_card_congr _ _ _, hiso, bhnStep_card_twice hk hG, hcard]
      have hpow1 : 2 ^ (4 ^ r) = 2 * 2 ^ (4 ^ r - 1) := by
        have he : 4 ^ r = (4 ^ r - 1) + 1 := by omega
        conv_lhs => rw [he]
        rw [pow_succ]; ring
      have hpow2 : 2 ^ (3 * 4 ^ r) * 2 ^ (4 ^ r - 1) = 2 ^ (4 ^ (r + 1) - 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc 2 ^ (3 * 4 ^ r) * (2 * ((4 ^ r + 2 ^ r) * 2 ^ (4 ^ r - 1)) + 4 ^ r * 2 ^ (4 ^ r))
          = 2 ^ (3 * 4 ^ r) * (2 * ((4 ^ r + 2 ^ r) * 2 ^ (4 ^ r - 1)) + 4 ^ r * (2 * 2 ^ (4 ^ r - 1))) := by
              rw [hpow1]
        _ = (4 * 4 ^ r + 2 * 2 ^ r) * (2 ^ (3 * 4 ^ r) * 2 ^ (4 ^ r - 1)) := by ring
        _ = (4 ^ (r + 1) + 2 ^ (r + 1)) * 2 ^ (4 ^ (r + 1) - 1) := by
              rw [hpow2]; ring

/-- **Theorem 2.2 (`ppl033_bhn_1995_power_of_four`):**
Exact Brass–Harborth–Nienborg (1995) lower bound on `Q_{4^r}`: for every `r : ℕ`, there exists
a `C_4`-free subgraph of `Q_{4^r}` with `2 * |E(G)| = (4^r + 2^r) * 2^(4^r - 1)`, i.e.,
`|E(G)| = (1/2) * (n + √n) * 2^(n - 1)` for `n = 4^r`. -/
theorem ppl033_bhn_1995_power_of_four (r : ℕ) :
    open Classical in
    ∃ G : SimpleGraph (Fin (4 ^ r) → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin (4 ^ r) → Bool =>
        (Finset.univ.filter (fun i : Fin (4 ^ r) => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      2 * G.edgeFinset.card = (4 ^ r + 2 ^ r) * 2 ^ (4 ^ r - 1) := by
  classical
  obtain ⟨G, hG, hfree, _, hcard⟩ := bhn_family_exists r
  exact ⟨G, hG, hfree, hcard⟩

/-- Every `n ≥ 1` admits `r : ℕ` with `4 ^ r ≤ n < 4 ^ (r + 1)`. -/
private lemma exists_pow_four_between (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ, 4 ^ r ≤ n ∧ n < 4 ^ (r + 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h4 : n < 4
    · exact ⟨0, by simpa using hn, by simpa using h4⟩
    · have hq : 1 ≤ n / 4 := by omega
      have hlt : n / 4 < n := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨r, hr1, hr2⟩ := ih (n / 4) hlt hq
      refine ⟨r + 1, ?_, ?_⟩
      · calc 4 ^ (r + 1) = 4 * 4 ^ r := by ring
          _ ≤ 4 * (n / 4) := Nat.mul_le_mul_left 4 hr1
          _ ≤ n := Nat.mul_div_le n 4
      · calc n < 4 * (n / 4 + 1) := by omega
          _ ≤ 4 * 4 ^ (r + 1) := Nat.mul_le_mul_left 4 hr2
          _ = 4 ^ (r + 2) := by ring

/-- **Theorem 2.3 (`ppl033_bhn_1995_all_n`):**
Unconditional Brass–Harborth–Nienborg (1995) lower bound for **every** `n ≥ 1`:
there exists a `C_4`-free subgraph of `Q_n` with at least
`(1/2 + 1 / (4 * √n)) * n * 2^(n - 1)` edges (pure Mathlib signature). -/
theorem ppl033_bhn_1995_all_n (n : ℕ) (hn : 1 ≤ n) :
    open Classical in
    ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
        (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      ((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * ((n * 2 ^ (n - 1) : ℕ) : ℝ) ≤
        (G.edgeFinset.card : ℝ) := by
  classical
  obtain ⟨r, hr_le, hr_lt⟩ := exists_pow_four_between n hn
  obtain ⟨Gm, hGm, hfreeGm, _, hcardGm⟩ := bhn_family_exists r
  have hm1 : 1 ≤ 4 ^ r := Nat.one_le_pow r 4 (by omega)
  let G := extendByParity hr_le Gm
  refine ⟨G, extendByParity_le_Q hr_le Gm, extendByParity_isC4Free hr_le hGm hfreeGm, ?_⟩
  have h2 := extendByParity_card_twice hm1 hr_le hGm
  rw [hcardGm] at h2
  have hpow : 2 ^ (n - 4 ^ r) * 2 ^ (4 ^ r - 1) = 2 ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  have h2_eq : 2 * G.edgeFinset.card = (n + 2 ^ r) * 2 ^ (n - 1) := by
    calc 2 * G.edgeFinset.card
        = (4 ^ r + 2 ^ r) * (2 ^ (n - 4 ^ r) * 2 ^ (4 ^ r - 1)) + (n - 4 ^ r) * 2 ^ (n - 1) := by
            rw [h2]; ring
      _ = (4 ^ r + 2 ^ r) * 2 ^ (n - 1) + (n - 4 ^ r) * 2 ^ (n - 1) := by rw [hpow]
      _ = (4 ^ r + 2 ^ r + (n - 4 ^ r)) * 2 ^ (n - 1) := by ring
      _ = (n + 2 ^ r) * 2 ^ (n - 1) := by congr 1; omega
  have h4nat : 4 ^ (r + 1) = (2 * 2 ^ r) ^ 2 := by
    calc 4 ^ (r + 1) = 4 * (2 ^ 2) ^ r := by ring
      _ = 4 * (2 ^ r) ^ 2 := by rw [← pow_mul, mul_comm 2 r, pow_mul]
      _ = (2 * 2 ^ r) ^ 2 := by ring
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ 2 * ((2 ^ r : ℕ) : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hlt' : (n : ℝ) ≤ ((4 ^ (r + 1) : ℕ) : ℝ) := Nat.cast_le.mpr (le_of_lt hr_lt)
    have h4eq : ((4 ^ (r + 1) : ℕ) : ℝ) = (2 * ((2 ^ r : ℕ) : ℝ)) ^ 2 := by
      rw [h4nat]; push_cast; ring
    linarith
  have hcast : (2 : ℝ) * (G.edgeFinset.card : ℝ) =
      ((n : ℝ) + ((2 ^ r : ℕ) : ℝ)) * (2 : ℝ) ^ (n - 1) := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h2_eq
    push_cast at this ⊢
    exact this
  have hsq_pos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hsq_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have hmain : ((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * (n : ℝ) ≤
      ((n : ℝ) + ((2 ^ r : ℕ) : ℝ)) / 2 := by
    have hdiv : (n : ℝ) / (4 * Real.sqrt (n : ℝ)) = Real.sqrt (n : ℝ) / 4 := by
      field_simp [hsq_pos.ne']
      nlinarith
    have h1 : ((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * (n : ℝ) =
        (n : ℝ) / 2 + Real.sqrt (n : ℝ) / 4 := by
      calc ((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * (n : ℝ)
          = (n : ℝ) / 2 + (n : ℝ) / (4 * Real.sqrt (n : ℝ)) := by ring
        _ = (n : ℝ) / 2 + Real.sqrt (n : ℝ) / 4 := by rw [hdiv]
    rw [h1]
    linarith
  push_cast
  calc ((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * ((n : ℝ) * (2 : ℝ) ^ (n - 1))
      = (((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * (n : ℝ)) * (2 : ℝ) ^ (n - 1) := by ring
    _ ≤ (((n : ℝ) + ((2 ^ r : ℕ) : ℝ)) / 2) * (2 : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
    _ = (G.edgeFinset.card : ℝ) := by
        have : (((n : ℝ) + ((2 ^ r : ℕ) : ℝ)) / 2) * (2 : ℝ) ^ (n - 1) =
            (((n : ℝ) + ((2 ^ r : ℕ) : ℝ)) * (2 : ℝ) ^ (n - 1)) / 2 := by ring
        rw [this, ← hcast]; ring

private lemma exC4_ge_half (n : ℕ) (hn : 1 ≤ n) :
    ((n * 2 ^ (n - 1) : ℕ) : ℝ) / 2 ≤ (exC4 n : ℝ) := by
  classical
  obtain ⟨G, hG, hfree, hcard⟩ := ppl033_bhn_1995_all_n n hn
  have hle : (G.edgeFinset.card : ℝ) ≤ (exC4 n : ℝ) :=
    Nat.cast_le.mpr (card_le_exC4 G hG hfree)
  have hpos : (0 : ℝ) ≤ 1 / (4 * Real.sqrt (n : ℝ)) := by positivity
  have hmul : (1 / 2 : ℝ) * ((n * 2 ^ (n - 1) : ℕ) : ℝ) ≤
      ((1 / 2 : ℝ) + 1 / (4 * Real.sqrt (n : ℝ))) * ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ ((n * 2 ^ (n - 1) : ℕ) : ℝ) by positivity]
  linarith

end ExplicitLowerBounds

/-! ## Section 3: Exact Small-Cube Extremal Numbers (`Q_1` through `Q_4`, `0` `native_decide`) -/

section SmallCubeExact

private lemma exC4_one : exC4 1 = 1 := by
  classical
  apply le_antisymm
  · simpa using exC4_le_Q 1
  · have hfree : IsC4Free (Q 1) := by
      rw [isC4Free_iff_no_face le_rfl]
      intro u i j hij
      exact absurd (Subsingleton.elim i j) hij
    have hle := card_le_exC4 (Q 1) le_rfl hfree
    simpa [Q_edgeFinset_card 1] using hle

private lemma exC4_two : exC4 2 = 3 := by
  classical
  apply le_antisymm
  · obtain ⟨G, hG, hfree, hcard⟩ := exists_exC4_witness 2
    rw [← hcard]
    have hleQ : G.edgeFinset.card ≤ 4 := by
      calc G.edgeFinset.card
          ≤ (Q 2).edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hG)
        _ = 4 := by simpa using Q_edgeFinset_card 2
    by_contra hgt
    have heq4 : G.edgeFinset.card = 4 := by omega
    have hsub : G.edgeFinset ⊆ (Q 2).edgeFinset := SimpleGraph.edgeFinset_mono hG
    have hQcard : (Q 2).edgeFinset.card = 4 := by simpa using Q_edgeFinset_card 2
    have heq_set : G.edgeFinset = (Q 2).edgeFinset :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hGQ : ∀ u v : Fin 2 → Bool, (Q 2).Adj u v → G.Adj u v := by
      intro u v huv
      have hmem : s(u, v) ∈ (Q 2).edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      rw [← heq_set, SimpleGraph.mem_edgeFinset] at hmem
      exact hmem
    let u0 : Fin 2 → Bool := fun _ => false
    exact (isC4Free_iff_no_face hG).mp hfree u0 0 1 (by decide)
      ⟨hGQ _ _ (Q_adj_flip _ _), hGQ _ _ (Q_adj_flip _ _),
       hGQ _ _ (by rw [flip_comm]; exact (Q_adj_flip _ _).symm),
       hGQ _ _ (Q_adj_flip _ _).symm⟩
  · have hle := card_le_exC4 (parityPrefixGraph 2) (parityPrefixGraph_le_Q 2)
      (parityPrefixGraph_isC4Free 2)
    have h2 := parityPrefixGraph_card_twice 2 (by omega)
    omega

/-- Explicit `9`-edge `C_4`-free subgraph of `Q_3`: remove the 3 face-disjoint edges
`(?, false, false)`, `(false, ?, true)`, `(true, true, ?)`. -/
private def keepEdge3 (u : Fin 3 → Bool) (i : Fin 3) : Bool :=
  match i with
  | ⟨0, _⟩ => !((u 1 == false) && (u 2 == false))
  | ⟨1, _⟩ => !((u 0 == false) && (u 2 == true))
  | ⟨2, _⟩ => !((u 0 == true) && (u 1 == true))

private lemma keepEdge3_flip_self (u : Fin 3 → Bool) (i : Fin 3) :
    keepEdge3 (flip u i) i = keepEdge3 u i := by
  fin_cases i <;> simp [keepEdge3, flip]

private lemma keepEdge3_c4_free (u : Fin 3 → Bool) (i j : Fin 3) (hij : i ≠ j) :
    ¬ (keepEdge3 u i = true ∧ keepEdge3 (flip u i) j = true ∧
       keepEdge3 (flip u j) i = true ∧ keepEdge3 u j = true) := by
  have hall : ∀ (a b c : Bool) (i j : Fin 3), i ≠ j →
      let u : Fin 3 → Bool := ![a, b, c]
      ¬ (keepEdge3 u i = true ∧ keepEdge3 (flip u i) j = true ∧
         keepEdge3 (flip u j) i = true ∧ keepEdge3 u j = true) := by
    decide
  have hu : u = ![u 0, u 1, u 2] := by ext k; fin_cases k <;> rfl
  rw [hu]
  exact hall (u 0) (u 1) (u 2) i j hij

private lemma keepEdge3_dir_count (i : Fin 3) :
    (Finset.univ.filter (fun u : Fin 3 → Bool => keepEdge3 u i = true)).card = 6 := by
  fin_cases i <;> decide

private def H3Graph : SimpleGraph (Fin 3 → Bool) where
  Adj u v := ∃ i : Fin 3, v = flip u i ∧ keepEdge3 u i = true
  symm := ⟨by
    rintro u v ⟨i, rfl, hk⟩
    exact ⟨i, (flip_flip u i).symm, by rwa [keepEdge3_flip_self]⟩⟩
  loopless := ⟨by
    rintro u ⟨i, h, _⟩
    exact flip_ne_self u i h.symm⟩

private lemma H3Graph_le_Q3 : H3Graph ≤ Q 3 := by
  rintro u v ⟨i, rfl, _⟩; exact Q_adj_flip u i

private lemma H3Graph_isC4Free : IsC4Free H3Graph := by
  rw [isC4Free_iff_no_face H3Graph_le_Q3]
  intro u i j hij ⟨h1, h2, h3, h4⟩
  have hk1 : keepEdge3 u i = true := by
    rcases h1 with ⟨l, hl, h⟩; have := flip_inj u hl; subst this; exact h
  have hk2 : keepEdge3 (flip u i) j = true := by
    rcases h2 with ⟨l, hl, h⟩; have := flip_inj (flip u i) hl; subst this; exact h
  have hk3 : keepEdge3 (flip u j) i = true := by
    rcases h3.symm with ⟨l, hl, h⟩; rw [flip_comm] at hl
    have := flip_inj (flip u j) hl; subst this; exact h
  have hk4 : keepEdge3 u j = true := by
    rcases h4.symm with ⟨l, hl, h⟩; have := flip_inj u hl; subst this; exact h
  exact keepEdge3_c4_free u i j hij ⟨hk1, hk2, hk3, hk4⟩

private lemma H3Graph_card [Fintype H3Graph.edgeSet] :
    H3Graph.edgeFinset.card = 9 := by
  classical
  have h2 := twice_card_edges_eq_sum_oriented H3Graph H3Graph_le_Q3
  have hsimp : ∀ u : Fin 3 → Bool,
      (Finset.univ.filter (fun j : Fin 3 => H3Graph.Adj u (flip u j))).card =
      (Finset.univ.filter (fun j : Fin 3 => keepEdge3 u j = true)).card := by
    intro u; congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (∃ l : Fin 3, flip u j = flip u l ∧ keepEdge3 u l = true) ↔ keepEdge3 u j = true
    constructor
    · rintro ⟨l, hl, hk⟩; have := flip_inj u hl; subst this; exact hk
    · intro hk; exact ⟨j, rfl, hk⟩
  simp_rw [hsimp, Finset.card_filter] at h2
  rw [Finset.sum_comm] at h2
  have hdir : ∀ j : Fin 3,
      (∑ u : Fin 3 → Bool, if keepEdge3 u j = true then 1 else 0) = 6 := by
    intro j; rw [← Finset.card_filter]; exact keepEdge3_dir_count j
  simp_rw [hdir] at h2
  simp at h2
  omega

private lemma exC4_three : exC4 3 = 9 := by
  classical
  apply le_antisymm
  · obtain ⟨G, hG, hfree, hcard⟩ := exists_exC4_witness 3
    have hstep := subcube_averaging_graph G hG hfree
    rw [hcard, exC4_two] at hstep
    omega
  · have hle := card_le_exC4 H3Graph H3Graph_le_Q3 H3Graph_isC4Free
    rw [H3Graph_card] at hle
    exact hle

private lemma exC4_four : exC4 4 = 24 := by
  classical
  apply le_antisymm
  · obtain ⟨G, hG, hfree, hcard⟩ := exists_exC4_witness 4
    have hstep := subcube_averaging_graph G hG hfree
    rw [hcard, exC4_three] at hstep
    omega
  · have hle := card_le_exC4 H4Graph H4Graph_le_Q4 H4Graph_isC4Free
    rw [H4Graph_card] at hle
    exact hle

/-- **Theorem 3.1 (`ppl033_ex_Q1`):** `ex(Q_1, C_4) = 1` (pure Mathlib signature). -/
theorem ppl033_ex_Q1 :
    open Classical in
    sSup { m : ℕ | ∃ G : SimpleGraph (Fin 1 → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin 1 → Bool =>
        (Finset.univ.filter (fun i : Fin 1 => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = m } = 1 := exC4_one

/-- **Theorem 3.2 (`ppl033_ex_Q2`):** `ex(Q_2, C_4) = 3` (pure Mathlib signature). -/
theorem ppl033_ex_Q2 :
    open Classical in
    sSup { m : ℕ | ∃ G : SimpleGraph (Fin 2 → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin 2 → Bool =>
        (Finset.univ.filter (fun i : Fin 2 => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = m } = 3 := exC4_two

/-- **Theorem 3.3 (`ppl033_ex_Q3`):** `ex(Q_3, C_4) = 9` (pure Mathlib signature). -/
theorem ppl033_ex_Q3 :
    open Classical in
    sSup { m : ℕ | ∃ G : SimpleGraph (Fin 3 → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin 3 → Bool =>
        (Finset.univ.filter (fun i : Fin 3 => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = m } = 9 := exC4_three

/-- **Theorem 3.4 (`ppl033_ex_Q4`):** `ex(Q_4, C_4) = 24` (pure Mathlib signature). -/
theorem ppl033_ex_Q4 :
    open Classical in
    sSup { m : ℕ | ∃ G : SimpleGraph (Fin 4 → Bool),
      G ≤ SimpleGraph.fromRel (fun u v : Fin 4 → Bool =>
        (Finset.univ.filter (fun i : Fin 4 => u i ≠ v i)).card = 1) ∧
      (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
      G.edgeFinset.card = m } = 24 := exC4_four

/-- **Theorem 3.5 (`ppl033_universal_three_fourths`):**
Universal `≤ 3/4` subcube-averaging upper bound: for every `n ≥ 2` and every `C_4`-free
subgraph `G ≤ Q_n`, `4 * |E(G)| ≤ 3 * (n * 2 ^ (n - 1))`. -/
theorem ppl033_universal_three_fourths (n : ℕ) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    4 * G.edgeFinset.card ≤ 3 * (n * 2 ^ (n - 1)) := by
  have hle : G.edgeFinset.card ≤ exC4 n := card_le_exC4 G hG hfree
  have hant := turan_density_antitone_aux (by omega : 1 ≤ 2) hn
  rw [exC4_two] at hant
  have hpos : (0 : ℝ) < ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by positivity
  have hreal : (exC4 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ) ≤ 3 / 4 := by
    convert hant using 1; norm_num
  have hmul : (exC4 n : ℝ) * 4 ≤ 3 * ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 4)] at hreal
    linarith
  have hnat : 4 * exC4 n ≤ 3 * (n * 2 ^ (n - 1)) := by
    exact_mod_cast (by linarith : (4 * (exC4 n : ℝ)) ≤ 3 * ((n * 2 ^ (n - 1) : ℕ) : ℝ))
  omega

end SmallCubeExact

/-! ## Section 4: `2`-Path (`1/√2`), `2/3` Face Bound, `Q_3` 3-Star, & Sub-`0.6175` Flag-SOS Upper Bounds -/

section UpperBounds

/-- Cauchy–Schwarz over `Fin n → Bool` in `ℕ` (`(∑ f)^2 ≤ 2^n * ∑ f^2`). -/
private lemma sq_sum_le_card_mul_sum_sq {α : Type*} [Fintype α] (f : α → ℝ) :
    (∑ x : α, f x) ^ 2 ≤ (Fintype.card α : ℝ) * ∑ x : α, (f x) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) (fun _ => (1 : ℝ)) f
  simpa using h

/-- Exact degree-pair sum for `G ≤ Q_n`: `∑ u, d(u) * (d(u) - 1)` equals the number of
triples `(u, i, j)` with `i ≠ j`, `G.Adj u (flip u i)`, and `G.Adj u (flip u j)`. -/
private lemma sum_deg_mul_deg_sub_one_eq {n : ℕ} (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] (hG : G ≤ Q n) :
    ∑ u : Fin n → Bool, G.degree u * (G.degree u - 1) =
      ∑ u : Fin n → Bool, ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
  refine Finset.sum_congr rfl fun u _ => ?_
  have hdeg : G.degree u = (Finset.univ.filter (fun i : Fin n => G.Adj u (flip u i))).card := by
    rw [SimpleGraph.degree]
    symm
    refine Finset.card_bij (fun i _ => flip u i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simpa [SimpleGraph.mem_neighborFinset] using hi
    · intro i1 _ i2 _ h; exact flip_inj u h
    · intro v hv
      simp only [SimpleGraph.mem_neighborFinset] at hv
      obtain ⟨i, rfl⟩ := Q_adj_iff_exists_flip.mp (hG hv)
      exact ⟨i, by simpa using hv, rfl⟩
  rw [hdeg]
  set S := Finset.univ.filter (fun i : Fin n => G.Adj u (flip u i))
  have hrhs :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) =
      ∑ i ∈ S, (S.erase i).card := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => G.Adj u (flip u i))]
    have hzero :
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => ¬ G.Adj u (flip u i)),
          ∑ j ∈ Finset.univ.erase i,
            if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ => ?_
      have hni : ¬ G.Adj u (flip u i) := (Finset.mem_filter.mp hi).2
      simp [hni]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hiG : G.Adj u (flip u i) := (Finset.mem_filter.mp hi).2
    have hfilt : (Finset.univ.erase i).filter (fun j : Fin n => G.Adj u (flip u i) ∧ G.Adj u (flip u j)) =
        S.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, S, hiG, true_and]
    rw [← Finset.card_filter, hfilt]
  rw [hrhs]
  have heach : ∀ i ∈ S, (S.erase i).card = S.card - 1 := fun i hi => Finset.card_erase_of_mem hi
  rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]

/-- Distance-2 path double counting: for `C_4`-free `G ≤ Q_n`,
`2 * ∑ u, d(u) * (d(u) - 1) ≤ n * (n - 1) * 2 ^ n`. -/
private lemma two_path_sum_le {n : ℕ} (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] (hG : G ≤ Q n) (hfree : IsC4Free G) :
    2 * (∑ u : Fin n → Bool, G.degree u * (G.degree u - 1)) ≤ n * (n - 1) * 2 ^ n := by
  rw [sum_deg_mul_deg_sub_one_eq G hG]
  -- Swap sums so (i, j) is outer and u is inner
  have hswap :
      (∑ u : Fin n → Bool, ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
        if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  have hinner : ∀ (i : Fin n) (j : Fin n), j ∈ Finset.univ.erase i →
      2 * (∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) ≤ 2 ^ n := by
    intro i j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hij : i ≠ j := Ne.symm hji
    -- Involution u ↦ flip (flip u i) j
    let inv : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun u => flip (flip u i) j
        invFun := fun u => flip (flip u i) j
        left_inv := fun u => by dsimp only; rw [flip_comm (flip u i) j i, flip_flip, flip_flip]
        right_inv := fun u => by dsimp only; rw [flip_comm (flip u i) j i, flip_flip, flip_flip] }
    have hsum_inv :
        (∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) =
        ∑ u : Fin n → Bool, if G.Adj (inv u) (flip (inv u) i) ∧ G.Adj (inv u) (flip (inv u) j) then 1 else 0 :=
      (Fintype.sum_equiv inv _ _ (fun _ => rfl)).symm
    have h2 :
        2 * (∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) =
        ∑ u : Fin n → Bool,
          ((if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) +
           (if G.Adj (inv u) (flip (inv u) i) ∧ G.Adj (inv u) (flip (inv u) j) then 1 else 0)) := by
      rw [two_mul, Finset.sum_add_distrib, ← hsum_inv]
    rw [h2]
    have hpt : ∀ u : Fin n → Bool,
        (if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) +
        (if G.Adj (inv u) (flip (inv u) i) ∧ G.Adj (inv u) (flip (inv u) j) then 1 else 0) ≤ 1 := by
      intro u
      by_cases h1 : G.Adj u (flip u i) ∧ G.Adj u (flip u j)
      · by_cases h2 : G.Adj (inv u) (flip (inv u) i) ∧ G.Adj (inv u) (flip (inv u) j)
        · exfalso
          have hf1 : flip (inv u) i = flip u j := by
            dsimp [inv]; rw [flip_comm, flip_flip]
          have hf2 : flip (inv u) j = flip u i := by
            dsimp [inv]; rw [flip_flip]
          rw [hf1, hf2] at h2
          exact (isC4Free_iff_no_face hG).mp hfree u i j hij
            ⟨h1.1, h2.2.symm, h2.1, h1.2.symm⟩
        · simp [h1, h2]
      · simp only [h1, ↓reduceIte, zero_add]
        split_ifs <;> omega
    calc ∑ u : Fin n → Bool,
            ((if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) +
             (if G.Adj (inv u) (flip (inv u) i) ∧ G.Adj (inv u) (flip (inv u) j) then 1 else 0))
        ≤ ∑ _u : Fin n → Bool, 1 := Finset.sum_le_sum fun u _ => hpt u
      _ = 2 ^ n := by simp [Fintype.card_pi]
  calc (∑ i : Fin n, 2 * ∑ j ∈ Finset.univ.erase i,
          ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0)
      = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          2 * ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
          refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 2 ^ n := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => hinner i j hj
    _ = n * (n - 1) * 2 ^ n := by
          simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring

/-- **Theorem 4.1 (`ppl033_two_path_upper_exact`):**
Exact distance-2 path double-counting bound: for every `n ≥ 1` and every `C_4`-free `G ≤ Q_n`,
`4 * |E(G)|^2 ≤ n * (n - 1) * 2 ^ (2 * n - 1) + 2 * |E(G)| * 2 ^ n` (pure Mathlib signature). -/
theorem ppl033_two_path_upper_exact (n : ℕ) (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    4 * G.edgeFinset.card ^ 2 ≤ n * (n - 1) * 2 ^ (2 * n - 1) + 2 * G.edgeFinset.card * 2 ^ n := by
  classical
  rw [edgeFinset_card_congr G _ (SimpleGraph.fintypeEdgeSet G)]
  clear ‹Fintype G.edgeSet›
  have h2p := two_path_sum_le G hG hfree
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hcs := sq_sum_le_card_mul_sum_sq (fun u : Fin n → Bool => (G.degree u : ℝ))
  have hcardV : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by simp [Fintype.card_pi]
  rw [hcardV] at hcs
  have hsumR : (∑ u : Fin n → Bool, (G.degree u : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum
  rw [hsumR] at hcs
  have hsq_eq : ∑ u : Fin n → Bool, (G.degree u : ℝ) ^ 2 =
      (∑ u : Fin n → Bool, ((G.degree u * (G.degree u - 1) : ℕ) : ℝ)) + 2 * (G.edgeFinset.card : ℝ) := by
    rw [← hsumR, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    cases hd : G.degree u with
    | zero => simp
    | succ k => push_cast; ring
  have h2pR : 2 * (∑ u : Fin n → Bool, ((G.degree u * (G.degree u - 1) : ℕ) : ℝ)) ≤
      ((n * (n - 1) : ℕ) : ℝ) * (2 : ℝ) ^ n := by
    have := Nat.cast_le (α := ℝ).mpr h2p
    push_cast at this ⊢
    linarith
  have hpow : (2 : ℝ) ^ n * (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (2 * n - 1) := by
    have he : 2 * n = (2 * n - 1) + 1 := by omega
    calc (2 : ℝ) ^ n * (2 : ℝ) ^ n = (2 : ℝ) ^ (n + n) := (pow_add 2 n n).symm
      _ = (2 : ℝ) ^ (2 * n) := by congr 1; omega
      _ = (2 : ℝ) ^ ((2 * n - 1) + 1) := by conv_lhs => rw [he]
      _ = 2 * (2 : ℝ) ^ (2 * n - 1) := by rw [pow_succ]; ring
  have hfinalR : 4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      ((n * (n - 1) : ℕ) : ℝ) * (2 : ℝ) ^ (2 * n - 1) + 2 * (G.edgeFinset.card : ℝ) * (2 : ℝ) ^ n := by
    have h1 : 8 * (G.edgeFinset.card : ℝ) ^ 2 ≤
        (2 : ℝ) ^ n * (2 * (∑ u : Fin n → Bool, ((G.degree u * (G.degree u - 1) : ℕ) : ℝ)) +
          4 * (G.edgeFinset.card : ℝ)) := by
      rw [hsq_eq] at hcs
      nlinarith
    have h2 : (2 : ℝ) ^ n * (2 * (∑ u : Fin n → Bool, ((G.degree u * (G.degree u - 1) : ℕ) : ℝ))) ≤
        ((n * (n - 1) : ℕ) : ℝ) * ((2 : ℝ) ^ n * (2 : ℝ) ^ n) := by
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
      nlinarith
    rw [hpow] at h2
    linarith
  exact_mod_cast hfinalR

/-- **Theorem 4.2 (`ppl033_two_path_inv_sqrt_two`):**
Distance-2 path asymptotic upper bound: for every `n ≥ 1` and every `C_4`-free `G ≤ Q_n`,
`|E(G)| ≤ (1 / √2 + 1 / (2 * n)) * (n * 2 ^ (n - 1))` (pure Mathlib signature). -/
theorem ppl033_two_path_inv_sqrt_two (n : ℕ) (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    (G.edgeFinset.card : ℝ) ≤
      (1 / Real.sqrt 2 + 1 / (2 * (n : ℝ))) * ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by
  have hex := ppl033_two_path_upper_exact n hn G hG hfree
  have hexR : 4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      (n : ℝ) * ((n : ℝ) - 1) * (2 : ℝ) ^ (2 * n - 1) + 2 * (G.edgeFinset.card : ℝ) * (2 : ℝ) ^ n := by
    have h1 := Nat.cast_le (α := ℝ).mpr hex
    push_cast [Nat.cast_sub hn] at h1 ⊢
    exact h1
  set E : ℝ := ((n * 2 ^ (n - 1) : ℕ) : ℝ)
  have hE_pos : 0 < E := by positivity
  set α : ℝ := (G.edgeFinset.card : ℝ) / E
  have hα_def : (G.edgeFinset.card : ℝ) = α * E := (div_mul_cancel₀ _ hE_pos.ne').symm
  have hE_eq : E = (n : ℝ) * (2 : ℝ) ^ (n - 1) := by dsimp [E]; push_cast; rfl
  have h2n : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]; ring
  have h22n : (2 : ℝ) ^ (2 * n - 1) = 2 * ((2 : ℝ) ^ (n - 1)) ^ 2 := by
    have he : 2 * n - 1 = (n - 1) + (n - 1) + 1 := by omega
    rw [he, pow_succ, pow_add]; ring
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hquad : α ^ 2 - α / (n : ℝ) ≤ 1 / 2 - 1 / (2 * (n : ℝ)) := by
    rw [hα_def, hE_eq, h2n, h22n] at hexR
    have hpos : (0 : ℝ) < 4 * ((n : ℝ) * (2 : ℝ) ^ (n - 1)) ^ 2 := by positivity
    have hrew : (α ^ 2 - α / (n : ℝ)) * (4 * ((n : ℝ) * (2 : ℝ) ^ (n - 1)) ^ 2) =
        4 * (α * ((n : ℝ) * (2 : ℝ) ^ (n - 1))) ^ 2 -
        2 * (α * ((n : ℝ) * (2 : ℝ) ^ (n - 1))) * (2 * (2 : ℝ) ^ (n - 1)) := by
      field_simp [hn_pos.ne']
      ring
    have hrhs : (1 / 2 - 1 / (2 * (n : ℝ))) * (4 * ((n : ℝ) * (2 : ℝ) ^ (n - 1)) ^ 2) =
        (n : ℝ) * ((n : ℝ) - 1) * (2 * ((2 : ℝ) ^ (n - 1)) ^ 2) := by
      field_simp [hn_pos.ne']
      ring
    nlinarith
  have hsq : (α - 1 / (2 * (n : ℝ))) ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h1 : 1 / (4 * (n : ℝ) ^ 2) ≤ 1 / (2 * (n : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
      nlinarith
    have hexp : (α - 1 / (2 * (n : ℝ))) ^ 2 = α ^ 2 - α / (n : ℝ) + 1 / (4 * (n : ℝ) ^ 2) := by
      field_simp [hn_pos.ne']
      ring
    linarith
  have hsub : α - 1 / (2 * (n : ℝ)) ≤ 1 / Real.sqrt 2 := by
    have hpos : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
    nlinarith [sq_nonneg (α - 1 / (2 * (n : ℝ)) - 1 / Real.sqrt 2)]
  have hα_le : α ≤ 1 / Real.sqrt 2 + 1 / (2 * (n : ℝ)) := by linarith
  rw [hα_def]
  exact mul_le_mul_of_nonneg_right hα_le hE_pos.le

/-- `Q_2`-face local inequality: on every `C_4`-free 2-face, `3 * (# 2-paths) ≤ 2 * (# edges)`. -/
private lemma q2_face_two_path_le_edges (a b c d : Bool) (hfree : ¬ (a = true ∧ b = true ∧ c = true ∧ d = true)) :
    3 * ((if a && d then 1 else 0) + (if a && b then 1 else 0) +
         (if b && c then 1 else 0) + (if c && d then 1 else 0)) ≤
    2 * ((if a then 1 else 0) + (if b then 1 else 0) +
         (if c then 1 else 0) + (if d then 1 else 0)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- **Theorem 4.3 (`ppl033_two_thirds_upper`):**
`Q_2`-face 2-path double-counting upper bound: for every `n ≥ 1` and every `C_4`-free `G ≤ Q_n`,
`3 * |E(G)| ≤ (2 * n + 1) * 2 ^ (n - 1)`, i.e., `|E(G)| ≤ (2/3 + 1/(3n)) * |E(Q_n)|`
(strictly beating `1/√2 ≈ 0.7071` and sharp with equality on `Q_4`: `72 = 72`). -/
theorem ppl033_two_thirds_upper (n : ℕ) (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    3 * G.edgeFinset.card ≤ (2 * n + 1) * 2 ^ (n - 1) := by
  classical
  rw [edgeFinset_card_congr G _ (SimpleGraph.fintypeEdgeSet G)]
  clear ‹Fintype G.edgeSet›
  -- Step 1: Prove 3 * ∑ u, d(u) * (d(u) - 1) ≤ 4 * (n - 1) * |E(G)|
  have hface_sum :
      3 * (∑ u : Fin n → Bool, G.degree u * (G.degree u - 1)) ≤ 4 * (n - 1) * G.edgeFinset.card := by
    rw [sum_deg_mul_deg_sub_one_eq G hG]
    -- For each (u, i, j) with i ≠ j, apply q2_face_two_path_le_edges to the 4 edges of the face!
    let eA (u : Fin n → Bool) (i _j : Fin n) : Bool := decide (G.Adj u (flip u i))
    let eB (u : Fin n → Bool) (i j : Fin n) : Bool := decide (G.Adj (flip u i) (flip (flip u i) j))
    let eC (u : Fin n → Bool) (i j : Fin n) : Bool := decide (G.Adj (flip (flip u i) j) (flip u j))
    let eD (u : Fin n → Bool) (_i j : Fin n) : Bool := decide (G.Adj (flip u j) u)
    have hpt : ∀ (u : Fin n → Bool) (i : Fin n) (j : Fin n), j ∈ Finset.univ.erase i →
        3 * ((if eA u i j && eD u i j then 1 else 0) + (if eA u i j && eB u i j then 1 else 0) +
             (if eB u i j && eC u i j then 1 else 0) + (if eC u i j && eD u i j then 1 else 0)) ≤
        2 * ((if eA u i j then 1 else 0) + (if eB u i j then 1 else 0) +
             (if eC u i j then 1 else 0) + (if eD u i j then 1 else 0)) := by
      intro u i j hj
      have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
      apply q2_face_two_path_le_edges
      rintro ⟨ha, hb, hc, hd⟩
      simp only [eA, eB, eC, eD, decide_eq_true_eq] at ha hb hc hd
      exact (isC4Free_iff_no_face hG).mp hfree u i j hij ⟨ha, hb, hc, hd⟩
    -- Sum over i, j ≠ i, u:
    have hsum_ineq :
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
          3 * ((if eA u i j && eD u i j then 1 else 0) + (if eA u i j && eB u i j then 1 else 0) +
               (if eB u i j && eC u i j then 1 else 0) + (if eC u i j && eD u i j then 1 else 0)) ≤
        ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
          2 * ((if eA u i j then 1 else 0) + (if eB u i j then 1 else 0) +
               (if eC u i j then 1 else 0) + (if eD u i j then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
        Finset.sum_le_sum fun u _ => hpt u i j hj
    -- Helper: for fixed i ≠ j, all 4 corner sums equal ∑ u, if G.Adj u (flip u i) ∧ G.Adj u (flip u j)
    let hbi_i : ∀ (i : Fin n), (Fin n → Bool) ≃ (Fin n → Bool) := fun i =>
      { toFun := fun u => flip u i, invFun := fun u => flip u i,
        left_inv := fun u => flip_flip u i, right_inv := fun u => flip_flip u i }
    let hbi_ij : ∀ (i j : Fin n), (Fin n → Bool) ≃ (Fin n → Bool) := fun i j =>
      { toFun := fun u => flip (flip u i) j, invFun := fun u => flip (flip u i) j,
        left_inv := fun u => by dsimp only; rw [flip_comm (flip u i) j i, flip_flip, flip_flip],
        right_inv := fun u => by dsimp only; rw [flip_comm (flip u i) j i, flip_flip, flip_flip] }
    have hlhs :
        (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
          3 * ((if eA u i j && eD u i j then 1 else 0) + (if eA u i j && eB u i j then 1 else 0) +
               (if eB u i j && eC u i j then 1 else 0) + (if eC u i j && eD u i j then 1 else 0))) =
        12 * (∑ u : Fin n → Bool, ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
          if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) := by
      have hinner : ∀ (i : Fin n) (j : Fin n), j ∈ Finset.univ.erase i →
          (∑ u : Fin n → Bool,
            ((if eA u i j && eD u i j then 1 else 0) + (if eA u i j && eB u i j then 1 else 0) +
             (if eB u i j && eC u i j then 1 else 0) + (if eC u i j && eD u i j then 1 else 0))) =
          4 * ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
        intro i j _
        simp only [Finset.sum_add_distrib]
        have h1 : (∑ u : Fin n → Bool, if eA u i j && eD u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          have : (eA u i j && eD u i j) = true ↔ G.Adj u (flip u i) ∧ G.Adj u (flip u j) := by
            simp [eA, eD, SimpleGraph.adj_comm]
          exact if_congr this rfl rfl
        have h2 : (∑ u : Fin n → Bool, if eA u i j && eB u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
          refine Fintype.sum_equiv (hbi_i i) _ _ fun u => ?_
          have : (eA u i j && eB u i j) = true ↔
              G.Adj (hbi_i i u) (flip (hbi_i i u) i) ∧ G.Adj (hbi_i i u) (flip (hbi_i i u) j) := by
            simp [eA, eB, hbi_i, flip_flip, SimpleGraph.adj_comm]
          exact if_congr this rfl rfl
        have h3 : (∑ u : Fin n → Bool, if eB u i j && eC u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
          refine Fintype.sum_equiv (hbi_ij i j) _ _ fun u => ?_
          have hf1 : flip (flip (flip u i) j) i = flip u j := by rw [flip_comm, flip_flip]
          have hf2 : flip (flip (flip u i) j) j = flip u i := by rw [flip_flip]
          have : (eB u i j && eC u i j) = true ↔
              G.Adj (hbi_ij i j u) (flip (hbi_ij i j u) i) ∧
              G.Adj (hbi_ij i j u) (flip (hbi_ij i j u) j) := by
            simp only [hbi_ij, Equiv.coe_fn_mk]
            rw [hf1, hf2]
            simp [eB, eC, SimpleGraph.adj_comm, and_comm]
          exact if_congr this rfl rfl
        have h4 : (∑ u : Fin n → Bool, if eC u i j && eD u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
          refine Fintype.sum_equiv (hbi_i j) _ _ fun u => ?_
          have : (eC u i j && eD u i j) = true ↔
              G.Adj (hbi_i j u) (flip (hbi_i j u) i) ∧ G.Adj (hbi_i j u) (flip (hbi_i j u) j) := by
            simp only [hbi_i, Equiv.coe_fn_mk]
            rw [flip_flip, flip_comm]
            simp [eC, eD, SimpleGraph.adj_comm]
          exact if_congr this rfl rfl
        rw [h1, h2, h3, h4]; ring
      have hstep1 :
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
            3 * ((if eA u i j && eD u i j then 1 else 0) + (if eA u i j && eB u i j then 1 else 0) +
                 (if eB u i j && eC u i j then 1 else 0) + (if eC u i j && eD u i j then 1 else 0))) =
          12 * ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
            if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.mul_sum, hinner i j hj]; ring
      rw [hstep1]
      congr 1
      have hcomm' : ∀ i : Fin n,
          (∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
            if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) =
          ∑ u : Fin n → Bool, ∑ j ∈ Finset.univ.erase i,
            if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0 := fun _ => Finset.sum_comm
      simp_rw [hcomm']
      exact Finset.sum_comm
    have hrhs :
        (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
          2 * ((if eA u i j then 1 else 0) + (if eB u i j then 1 else 0) +
               (if eC u i j then 1 else 0) + (if eD u i j then 1 else 0))) =
        16 * (n - 1) * G.edgeFinset.card := by
      -- For fixed i ≠ j, eA & eC sum to ∑ u, 1_{G(u, flip u i)}, and eB & eD sum to ∑ u, 1_{G(u, flip u j)}
      have hinner : ∀ (i : Fin n) (j : Fin n), j ∈ Finset.univ.erase i →
          (∑ u : Fin n → Bool,
            ((if eA u i j then 1 else 0) + (if eB u i j then 1 else 0) +
             (if eC u i j then 1 else 0) + (if eD u i j then 1 else 0))) =
          2 * (∑ u : Fin n → Bool, if G.Adj u (flip u i) then 1 else 0) +
          2 * (∑ u : Fin n → Bool, if G.Adj u (flip u j) then 1 else 0) := by
        intro i j _
        simp only [Finset.sum_add_distrib]
        have hA : (∑ u : Fin n → Bool, if eA u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u i) then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => by simp [eA]
        have hB : (∑ u : Fin n → Bool, if eB u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u j) then 1 else 0 := by
          refine Fintype.sum_equiv (hbi_i i) _ _ fun u => by simp [eB, hbi_i]
        have hC : (∑ u : Fin n → Bool, if eC u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u i) then 1 else 0 := by
          refine Fintype.sum_equiv (hbi_i j) _ _ fun u => by
            dsimp only [hbi_i]
            have : (eC u i j = true) ↔ G.Adj (flip u j) (flip (flip u j) i) := by
              rw [flip_comm]; simp [eC, SimpleGraph.adj_comm]
            exact if_congr this rfl rfl
        have hD : (∑ u : Fin n → Bool, if eD u i j then 1 else 0) =
            ∑ u : Fin n → Bool, if G.Adj u (flip u j) then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => by simp [eD, SimpleGraph.adj_comm]
        rw [hA, hB, hC, hD]; ring
      let f (i : Fin n) : ℕ := ∑ u : Fin n → Bool, if G.Adj u (flip u i) then 1 else 0
      have hfsum : ∑ i : Fin n, f i = 2 * G.edgeFinset.card := by
        rw [twice_card_edges_eq_sum_oriented G hG]
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      have hstep :
          (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ u : Fin n → Bool,
            2 * ((if eA u i j then 1 else 0) + (if eB u i j then 1 else 0) +
                 (if eC u i j then 1 else 0) + (if eD u i j then 1 else 0))) =
          4 * ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (f i + f j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [← Finset.mul_sum, hinner i j hj]; dsimp [f]; ring
      rw [hstep]
      have hpair : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (f i + f j) =
          2 * (n - 1) * ∑ i : Fin n, f i := by
        have hsplit : ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, (f i + f j) =
            (∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, f i) +
            (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, f j) := by
          simp_rw [Finset.sum_add_distrib]
        rw [hsplit]
        have hleft : (∑ i : Fin n, ∑ _j ∈ Finset.univ.erase i, f i) =
            (n - 1) * ∑ i : Fin n, f i := by
          simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
        have hright : (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, f j) =
            (n - 1) * ∑ j : Fin n, f j := by
          have : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, f j =
              ∑ j : Fin n, if j ≠ i then f j else 0 := by
            intro i
            rw [← Finset.sum_filter]
            congr 1; ext j; simp
          simp_rw [this]
          rw [Finset.sum_comm]
          have hpt : ∀ j : Fin n, (∑ i : Fin n, if j ≠ i then f j else 0) = (n - 1) * f j := by
            intro j
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
            congr 1
            have : Finset.univ.filter (fun i : Fin n => j ≠ i) = Finset.univ.erase j := by
              ext i; simp [ne_comm]
            rw [this, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
          simp_rw [hpt, ← Finset.mul_sum]
        rw [hleft, hright]; ring
      rw [hpair, hfsum]; ring
    rw [hlhs, hrhs] at hsum_ineq
    have h4 : 4 * (3 * ∑ u : Fin n → Bool, ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
        if G.Adj u (flip u i) ∧ G.Adj u (flip u j) then 1 else 0) ≤
        4 * (4 * (n - 1) * G.edgeFinset.card) := by
      linarith
    exact Nat.le_of_mul_le_mul_left h4 (by omega)
  -- Step 2: Combine with Cauchy–Schwarz: 3 * (4 m^2 - 2 * 2^n * m) ≤ 4 * (n - 1) * 2^n * m
  by_cases hm0 : G.edgeFinset.card = 0
  · rw [hm0]; simp
  · have hcs := sq_sum_le_card_mul_sum_sq (fun u : Fin n → Bool => (G.degree u : ℝ))
    have hcardV : (Fintype.card (Fin n → Bool) : ℝ) = (2 : ℝ) ^ n := by simp [Fintype.card_pi]
    rw [hcardV] at hcs
    have hsumR : (∑ u : Fin n → Bool, (G.degree u : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast SimpleGraph.sum_degrees_eq_twice_card_edges G
    rw [hsumR] at hcs
    have hsq_eq : ∑ u : Fin n → Bool, (G.degree u : ℝ) ^ 2 =
        (∑ u : Fin n → Bool, ((G.degree u * (G.degree u - 1) : ℕ) : ℝ)) + 2 * (G.edgeFinset.card : ℝ) := by
      rw [← hsumR, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      cases hd : G.degree u with
      | zero => simp
      | succ k => push_cast; ring
    have hfaceR : 3 * (∑ u : Fin n → Bool, ((G.degree u * (G.degree u - 1) : ℕ) : ℝ)) ≤
        4 * ((n : ℝ) - 1) * (G.edgeFinset.card : ℝ) := by
      have := Nat.cast_le (α := ℝ).mpr hface_sum
      push_cast [Nat.cast_sub hn] at this ⊢
      exact this
    have hm_pos : (0 : ℝ) < (G.edgeFinset.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
    have h2n : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
      have he : n = (n - 1) + 1 := by omega
      conv_lhs => rw [he]
      rw [pow_succ]; ring
    have hineqR : 3 * (G.edgeFinset.card : ℝ) ≤ (2 * (n : ℝ) + 1) * (2 : ℝ) ^ (n - 1) := by
      rw [hsq_eq] at hcs
      have h1 : 12 * (G.edgeFinset.card : ℝ) ^ 2 ≤
          (2 : ℝ) ^ n * (4 * ((n : ℝ) - 1) * (G.edgeFinset.card : ℝ) + 6 * (G.edgeFinset.card : ℝ)) := by
        have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
        nlinarith
      rw [h2n] at h1
      nlinarith
    exact_mod_cast hineqR

/-! ### Embedded `Q_3` Subcube Engine (For 3-Star Bound & Sub-`0.6175` Flag-SOS Upper Bound) -/

/-- Embedded `Q_3` map `φ_{u, a, b, c} : (Fin 3 → Bool) → (Fin n → Bool)` flipping coordinates
`a, b, c` according to `w 0, w 1, w 2`. -/
private def embedQ3 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) : Fin n → Bool :=
  let u1 := if w 0 then flip u a else u
  let u2 := if w 1 then flip u1 b else u1
  if w 2 then flip u2 c else u2

private lemma embedQ3_flip0 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) :
    embedQ3 u a b c (flip w 0) = flip (embedQ3 u a b c w) a := by
  have h1 : flip w 0 0 = !w 0 := by simp [flip]
  have h2 : flip w 0 1 = w 1 := by simp [flip]
  have h3 : flip w 0 2 = w 2 := by simp [flip]
  dsimp only [embedQ3]
  rw [h1, h2, h3]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip, flip_comm]

private lemma embedQ3_flip1 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) :
    embedQ3 u a b c (flip w 1) = flip (embedQ3 u a b c w) b := by
  have h1 : flip w 1 0 = w 0 := by simp [flip]
  have h2 : flip w 1 1 = !w 1 := by simp [flip]
  have h3 : flip w 1 2 = w 2 := by simp [flip]
  dsimp only [embedQ3]
  rw [h1, h2, h3]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip, flip_comm]

private lemma embedQ3_flip2 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) :
    embedQ3 u a b c (flip w 2) = flip (embedQ3 u a b c w) c := by
  have h1 : flip w 2 0 = w 0 := by simp [flip]
  have h2 : flip w 2 1 = w 1 := by simp [flip]
  have h3 : flip w 2 2 = !w 2 := by simp [flip]
  dsimp only [embedQ3]
  rw [h1, h2, h3]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip]

private lemma embedQ3_flip {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) (d : Fin 3) :
    embedQ3 u a b c (flip w d) = flip (embedQ3 u a b c w) (![a, b, c] d) := by
  fin_cases d
  · exact embedQ3_flip0 u a b c w
  · exact embedQ3_flip1 u a b c w
  · exact embedQ3_flip2 u a b c w

private lemma embedQ3_equiv_u {n : ℕ} (a b c : Fin n) (w : Fin 3 → Bool) :
    Function.Bijective (fun u : Fin n → Bool => embedQ3 u a b c w) := by
  -- embedQ3 · a b c w is an involution on Fin n → Bool!
  have hinv : ∀ u : Fin n → Bool, embedQ3 (embedQ3 u a b c w) a b c w = u := by
    intro u
    dsimp only [embedQ3]
    cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip, flip_comm]
  exact Function.Involutive.bijective hinv

private lemma embedQ3_inj_w {n : ℕ} (u : Fin n → Bool) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (embedQ3 u a b c) := by
  intro w1 w2 h
  ext d
  fin_cases d
  · have ha := congrFun h a
    dsimp only [embedQ3] at ha
    cases hw10 : w1 0 <;> cases hw11 : w1 1 <;> cases hw12 : w1 2 <;>
    cases hw20 : w2 0 <;> cases hw21 : w2 1 <;> cases hw22 : w2 2 <;>
    simp_all [flip_apply_self, flip_apply_ne]
  · have hb := congrFun h b
    dsimp only [embedQ3] at hb
    cases hw10 : w1 0 <;> cases hw11 : w1 1 <;> cases hw12 : w1 2 <;>
    cases hw20 : w2 0 <;> cases hw21 : w2 1 <;> cases hw22 : w2 2 <;>
    simp_all [flip_apply_self, flip_apply_ne, hab.symm]
  · have hc := congrFun h c
    dsimp only [embedQ3] at hc
    cases hw10 : w1 0 <;> cases hw11 : w1 1 <;> cases hw12 : w1 2 <;>
    cases hw20 : w2 0 <;> cases hw21 : w2 1 <;> cases hw22 : w2 2 <;>
    simp_all [flip_apply_self, flip_apply_ne, hac.symm, hbc.symm]

/-- Any `C_4`-free `H ≤ Q_3` has at most `2` vertices of degree `3` (at most 1 of even parity
and at most 1 of odd parity). -/
private lemma q3_deg3_le_two (H : SimpleGraph (Fin 3 → Bool)) [DecidableRel H.Adj]
    (hH : H ≤ Q 3) (hfree : IsC4Free H) :
    (Finset.univ.filter (fun w : Fin 3 → Bool => H.degree w = 3)).card ≤ 2 := by
  classical
  -- Any two distinct vertices of the same parity in Q_3 differ in exactly 2 coordinates!
  have hno_two_same_parity : ∀ u v : Fin 3 → Bool, u ≠ v → vecParity u = vecParity v →
      ¬ (H.degree u = 3 ∧ H.degree v = 3) := by
    intro u v huv hpar ⟨hu3, hv3⟩
    -- Every neighbor of u in Q_3 is adjacent to u in H (since degree u = 3 = Q_3 degree)
    have hall : ∀ (x : Fin 3 → Bool), H.degree x = 3 → ∀ d : Fin 3, H.Adj x (flip x d) := by
      intro x hx3 d
      have hsub : H.neighborFinset x ⊆ (Q 3).neighborFinset x := by
        intro y hy
        simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
        exact hH hy
      have hqdeg : ((Q 3).neighborFinset x).card = 3 := Q_degree x
      have heq : H.neighborFinset x = (Q 3).neighborFinset x :=
        Finset.eq_of_subset_of_card_le hsub (by rw [SimpleGraph.degree] at hx3; omega)
      have hmem : flip x d ∈ (Q 3).neighborFinset x := by
        simp only [SimpleGraph.mem_neighborFinset]; exact Q_adj_flip x d
      rw [← heq, SimpleGraph.mem_neighborFinset] at hmem
      exact hmem
    -- Find two distinct coordinates i, j where u and v differ (since u ≠ v and same parity!)
    have hdiff2 : ∃ i j : Fin 3, i ≠ j ∧ v = flip (flip u i) j := by
      have hall_bool : ∀ (a1 b1 c1 a2 b2 c2 : Bool),
          let u' : Fin 3 → Bool := ![a1, b1, c1]
          let v' : Fin 3 → Bool := ![a2, b2, c2]
          u' ≠ v' → vecParity u' = vecParity v' → ∃ i j : Fin 3, i ≠ j ∧ v' = flip (flip u' i) j := by
        decide
      have hu' : u = ![u 0, u 1, u 2] := by ext k; fin_cases k <;> rfl
      have hv' : v = ![v 0, v 1, v 2] := by ext k; fin_cases k <;> rfl
      rw [hu', hv'] at huv hpar ⊢
      exact hall_bool (u 0) (u 1) (u 2) (v 0) (v 1) (v 2) huv hpar
    obtain ⟨i, j, hij, rfl⟩ := hdiff2
    have h1 := hall u hu3 i
    have h2 : H.Adj (flip u i) (flip (flip u i) j) := by
      have := hall (flip (flip u i) j) hv3 j
      rw [flip_flip] at this; exact this.symm
    have h3 : H.Adj (flip (flip u i) j) (flip u j) := by
      have := hall (flip (flip u i) j) hv3 i
      have hfl : flip (flip (flip u i) j) i = flip u j := by rw [flip_comm (flip u i) j i, flip_flip]
      rwa [hfl] at this
    have h4 := (hall u hu3 j).symm
    exact (isC4Free_iff_no_face hH).mp hfree u i j hij ⟨h1, h2, h3, h4⟩
  set S := Finset.univ.filter (fun w : Fin 3 → Bool => H.degree w = 3)
  set S0 := S.filter (fun w => vecParity w = false)
  set S1 := S.filter (fun w => vecParity w = true)
  have hS0 : S0.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    by_contra hne
    exact hno_two_same_parity u v hne (hu.2.trans hv.2.symm) ⟨hu.1, hv.1⟩
  have hS1 : S1.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro u hu v hv
    simp only [S1, S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    by_contra hne
    exact hno_two_same_parity u v hne (hu.2.trans hv.2.symm) ⟨hu.1, hv.1⟩
  have hunion : S = S0 ∪ S1 := by
    ext w; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
    cases vecParity w <;> simp
  rw [hunion]
  calc (S0 ∪ S1).card ≤ S0.card + S1.card := Finset.card_union_le S0 S1
    _ ≤ 1 + 1 := Nat.add_le_add hS0 hS1
    _ = 2 := rfl

/-- **Theorem 4.4 (`ppl033_q3_three_star_upper`):**
`Q_3` 3-star double-counting bound: for every `n ≥ 3` and every `C_4`-free `G ≤ Q_n`,
`∑ v, Nat.choose (G.degree v) 3 ≤ 2 * Nat.choose n 3 * 2 ^ (n - 3)`
(asymptotically `α ≤ (1/4)^(1/3) ≈ 0.62996`, sharp with equality on `Q_4`: `16 = 16`). -/
theorem ppl033_q3_three_star_upper (n : ℕ) (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    ∑ v : Fin n → Bool, Nat.choose (G.degree v) 3 ≤ 2 * Nat.choose n 3 * 2 ^ (n - 3) := by
  classical
  -- Sum over all ordered distinct triples (a, b, c) and all u : Fin n → Bool:
  -- For each (u, a, b, c), the pullback H = G.comap (embedQ3 u a b c) is C_4-free in Q_3,
  -- hence has ≤ 2 vertices w : Fin 3 → Bool with all 3 incident edges in H!
  let deg3Ind (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) : ℕ :=
    if G.Adj (embedQ3 u a b c w) (flip (embedQ3 u a b c w) a) ∧
       G.Adj (embedQ3 u a b c w) (flip (embedQ3 u a b c w) b) ∧
       G.Adj (embedQ3 u a b c w) (flip (embedQ3 u a b c w) c) then 1 else 0
  have hQ3_le : ∀ (u : Fin n → Bool) (a : Fin n) (b : Fin n) (_hb : b ∈ Finset.univ.erase a)
      (c : Fin n) (_hc : c ∈ (Finset.univ.erase a).erase b),
      ∑ w : Fin 3 → Bool, deg3Ind u a b c w ≤ 2 := by
    intro u a b hb c hc
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
    have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
    have hab : a ≠ b := Ne.symm hba
    have hac : a ≠ c := Ne.symm hca
    have hbc : b ≠ c := Ne.symm hcb
    let H : SimpleGraph (Fin 3 → Bool) := G.comap (embedQ3 u a b c)
    have hH_le : H ≤ Q 3 := by
      intro w1 w2 hw
      have hq := hG hw
      obtain ⟨k, hk⟩ := Q_adj_iff_exists_flip.mp hq
      -- Since embedQ3 u a b c w1 and w2 differ only at coordinates in {a, b, c}, k ∈ {a, b, c}!
      by_cases hka : k = a
      · rw [hka] at hk
        rw [Q_adj_iff_exists_flip]
        refine ⟨0, embedQ3_inj_w u hab hac hbc ?_⟩
        rw [embedQ3_flip0 u a b c, hk]
      · by_cases hkb : k = b
        · rw [hkb] at hk
          rw [Q_adj_iff_exists_flip]
          refine ⟨1, embedQ3_inj_w u hab hac hbc ?_⟩
          rw [embedQ3_flip1 u a b c, hk]
        · by_cases hkc : k = c
          · rw [hkc] at hk
            rw [Q_adj_iff_exists_flip]
            refine ⟨2, embedQ3_inj_w u hab hac hbc ?_⟩
            rw [embedQ3_flip2 u a b c, hk]
          · exfalso
            have hval := congrFun hk k
            rw [flip_apply_self] at hval
            have heq : embedQ3 u a b c w2 k = embedQ3 u a b c w1 k := by
              dsimp only [embedQ3]
              cases w1 0 <;> cases w1 1 <;> cases w1 2 <;>
              cases w2 0 <;> cases w2 1 <;> cases w2 2 <;>
              simp [flip_apply_ne, hka, hkb, hkc]
            rw [heq] at hval
            exact Bool.not_ne_self _ hval.symm
    have hH_free : IsC4Free H := by
      intro w1 w2 w3 w4 h13 h24 ⟨e1, e2, e3, e4⟩
      exact hfree _ _ _ _ (fun h => h13 (embedQ3_inj_w u hab hac hbc h))
        (fun h => h24 (embedQ3_inj_w u hab hac hbc h)) ⟨e1, e2, e3, e4⟩
    have hdeg3 : ∀ w : Fin 3 → Bool, deg3Ind u a b c w = if H.degree w = 3 then 1 else 0 := by
      intro w
      have hiff : (G.Adj (embedQ3 u a b c w) (flip (embedQ3 u a b c w) a) ∧
                   G.Adj (embedQ3 u a b c w) (flip (embedQ3 u a b c w) b) ∧
                   G.Adj (embedQ3 u a b c w) (flip (embedQ3 u a b c w) c)) ↔ H.degree w = 3 := by
        have hcard : H.degree w = (Finset.univ.filter (fun d : Fin 3 => H.Adj w (flip w d))).card := by
          rw [SimpleGraph.degree]
          symm
          refine Finset.card_bij (fun d _ => flip w d) ?_ ?_ ?_
          · intro d hd; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
            simpa [SimpleGraph.mem_neighborFinset] using hd
          · intro d1 _ d2 _ h; exact flip_inj w h
          · intro y hy; simp only [SimpleGraph.mem_neighborFinset] at hy
            obtain ⟨d, rfl⟩ := Q_adj_iff_exists_flip.mp (hH_le hy)
            exact ⟨d, by simpa using hy, rfl⟩
        have h3 : (Finset.univ.filter (fun d : Fin 3 => H.Adj w (flip w d))).card = 3 ↔
            Finset.univ.filter (fun d : Fin 3 => H.Adj w (flip w d)) = Finset.univ :=
          Finset.card_eq_iff_eq_univ _
        rw [hcard, h3]
        simp only [Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        constructor
        · rintro ⟨ha', hb', hc'⟩ d
          fin_cases d
          · simpa [H, SimpleGraph.comap_adj, embedQ3_flip0 u a b c] using ha'
          · simpa [H, SimpleGraph.comap_adj, embedQ3_flip1 u a b c] using hb'
          · simpa [H, SimpleGraph.comap_adj, embedQ3_flip2 u a b c] using hc'
        · intro hall
          refine ⟨?_, ?_, ?_⟩
          · simpa [H, SimpleGraph.comap_adj, embedQ3_flip0 u a b c] using hall 0
          · simpa [H, SimpleGraph.comap_adj, embedQ3_flip1 u a b c] using hall 1
          · simpa [H, SimpleGraph.comap_adj, embedQ3_flip2 u a b c] using hall 2
      simp only [deg3Ind, hiff]
    simp_rw [hdeg3, ← Finset.card_filter]
    exact q3_deg3_le_two H hH_le hH_free
  -- Sum over all (a, b, c) pairwise distinct and all u : Fin n → Bool
  have hsum_ub :
      ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool, deg3Ind u a b c w ≤
      2 * (n * (n - 1) * (n - 2) * 2 ^ n) := by
    calc ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
            ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool, deg3Ind u a b c w
        ≤ ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ _c ∈ (Finset.univ.erase a).erase b,
            ∑ _u : Fin n → Bool, 2 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b hb =>
            Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun u _ => hQ3_le u a b hb c hc
      _ = 2 * (n * (n - 1) * (n - 2) * 2 ^ n) := by
          have hcard2 : ∀ (a : Fin n) (b : Fin n), b ∈ Finset.univ.erase a →
              ((Finset.univ.erase a).erase b).card = n - 2 := by
            intro a b hb
            rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
                Finset.card_univ, Fintype.card_fin]
            omega
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
            Finset.prod_const, Fintype.card_fin, smul_eq_mul]
          have h1 : ∀ a : Fin n,
              ∑ b ∈ Finset.univ.erase a, ((Finset.univ.erase a).erase b).card * (2 ^ n * 2) =
              (n - 1) * ((n - 2) * (2 ^ n * 2)) := by
            intro a
            rw [Finset.sum_congr rfl fun b hb => by rw [hcard2 a b hb],
                Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
                Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          simp_rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
  -- Self-contained identity: k * (k - 1) * (k - 2) = 6 * Nat.choose k 3
  have hchoose2 : ∀ k : ℕ, k * (k - 1) = 2 * Nat.choose k 2 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add]
      cases m with
      | zero => simp
      | succ m' =>
        simp only [Nat.add_sub_cancel] at ih ⊢
        linarith
  have hchoose3 : ∀ k : ℕ, k * (k - 1) * (k - 2) = 6 * Nat.choose k 3 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      rw [Nat.choose_succ_succ, mul_add]
      have h2 := hchoose2 m
      cases m with
      | zero => simp
      | succ m1 =>
        cases m1 with
        | zero => decide
        | succ m2 =>
          simp only [Nat.add_sub_cancel] at ih h2 ⊢
          have hm2 : m2 + 1 + 1 - 2 = m2 := by omega
          rw [hm2] at ih
          have hm3 : m2 + 1 + 1 + 1 - 2 = m2 + 1 := by omega
          rw [hm3]
          nlinarith
  -- Evaluate LHS: for each w : Fin 3 → Bool, reindex u ↦ embedQ3 u a b c w!
  have hlhs_eq :
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool, deg3Ind u a b c w) =
      48 * ∑ v : Fin n → Bool, Nat.choose (G.degree v) 3 := by
    have hinner_w : ∀ (a b c : Fin n),
        (∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool, deg3Ind u a b c w) =
        8 * ∑ v : Fin n → Bool,
          if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0 := by
      intro a b c
      rw [Finset.sum_comm]
      have hw : ∀ w : Fin 3 → Bool,
          (∑ u : Fin n → Bool, deg3Ind u a b c w) =
          ∑ v : Fin n → Bool,
            if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0 := by
        intro w
        exact Fintype.sum_bijective (fun u => embedQ3 u a b c w) (embedQ3_equiv_u a b c w) _ _
          (fun _ => rfl)
      simp_rw [hw]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
      simp [smul_eq_mul]
    simp_rw [hinner_w, ← Finset.mul_sum]
    -- Move ∑ v outside (a, b, c)
    have hswap3 :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool,
            if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
        ∑ v : Fin n → Bool, ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0 := by
      have s1 : ∀ a : Fin n,
          (∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
            ∑ v : Fin n → Bool,
              if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
          ∑ v : Fin n → Bool, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
            if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0 := by
        intro a
        have s2 : ∀ b ∈ Finset.univ.erase a,
            (∑ c ∈ (Finset.univ.erase a).erase b, ∑ v : Fin n → Bool,
              if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
            ∑ v : Fin n → Bool, ∑ c ∈ (Finset.univ.erase a).erase b,
              if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0 :=
          fun _ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl s2]
        exact Finset.sum_comm
      simp_rw [s1]
      exact Finset.sum_comm
    rw [hswap3]
    -- For each v, the triple sum equals 6 * Nat.choose (G.degree v) 3!
    have htri : ∀ v : Fin n → Bool,
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
        6 * Nat.choose (G.degree v) 3 := by
      intro v
      set S := Finset.univ.filter (fun i : Fin n => G.Adj v (flip v i))
      have hdegS : G.degree v = S.card := by
        rw [SimpleGraph.degree]; symm
        refine Finset.card_bij (fun i _ => flip v i) ?_ ?_ ?_
        · intro i hi; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simpa [SimpleGraph.mem_neighborFinset] using hi
        · intro i1 _ i2 _ h; exact flip_inj v h
        · intro y hy; simp only [SimpleGraph.mem_neighborFinset] at hy
          obtain ⟨i, rfl⟩ := Q_adj_iff_exists_flip.mp (hG hy)
          exact ⟨i, by simpa [S] using hy, rfl⟩
      rw [hdegS]
      -- Simplify triple sum to S.card * (S.card - 1) * (S.card - 2)
      have hprod :
          (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
            if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
          S.card * (S.card - 1) * (S.card - 2) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin n => G.Adj v (flip v a))]
        have hz1 : (∑ a ∈ Finset.univ.filter (fun a : Fin n => ¬ G.Adj v (flip v a)),
            ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
              if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) = 0 := by
          refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
          have := (Finset.mem_filter.mp ha).2; simp [this]
        rw [hz1, add_zero]
        have hstepa : ∀ a ∈ S,
            (∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
              if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
            (S.card - 1) * (S.card - 2) := by
          intro a ha
          have haG : G.Adj v (flip v a) := (Finset.mem_filter.mp ha).2
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase a) (fun b : Fin n => G.Adj v (flip v b))]
          have hz2 : (∑ b ∈ (Finset.univ.erase a).filter (fun b : Fin n => ¬ G.Adj v (flip v b)),
              ∑ c ∈ (Finset.univ.erase a).erase b,
                if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) = 0 := by
            refine Finset.sum_eq_zero fun b hb => Finset.sum_eq_zero fun c _ => ?_
            have := (Finset.mem_filter.mp hb).2; simp [this]
          rw [hz2, add_zero]
          have hfilt_b : (Finset.univ.erase a).filter (fun b : Fin n => G.Adj v (flip v b)) = S.erase a := by
            ext b; simp [S, Finset.mem_erase, Finset.mem_filter]
          rw [hfilt_b]
          have hstepb : ∀ b ∈ S.erase a,
              (∑ c ∈ (Finset.univ.erase a).erase b,
                if G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c) then 1 else 0) =
              S.card - 2 := by
            intro b hb
            have hbG : G.Adj v (flip v b) := (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).2
            rw [← Finset.card_filter]
            have hfilt_c : ((Finset.univ.erase a).erase b).filter
                (fun c : Fin n => G.Adj v (flip v a) ∧ G.Adj v (flip v b) ∧ G.Adj v (flip v c)) =
                (S.erase a).erase b := by
              ext c; simp [S, haG, hbG, Finset.mem_erase, Finset.mem_filter, and_assoc]
            rw [hfilt_c, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
            omega
          rw [Finset.sum_congr rfl hstepb, Finset.sum_const, Finset.card_erase_of_mem ha, smul_eq_mul]
        rw [Finset.sum_congr rfl hstepa, Finset.sum_const, smul_eq_mul]
        ring
      rw [hprod]
      exact hchoose3 S.card
    simp_rw [htri, ← Finset.mul_sum]
    ring
  rw [hlhs_eq] at hsum_ub
  have hchoose_n : n * (n - 1) * (n - 2) = 6 * Nat.choose n 3 := hchoose3 n
  have hpow3 : 2 ^ n = 8 * 2 ^ (n - 3) := by
    have he : n = (n - 3) + 3 := by omega
    conv_lhs => rw [he]
    rw [pow_add]; ring
  rw [hchoose_n, hpow3] at hsum_ub
  have hmul : 48 * ∑ v : Fin n → Bool, Nat.choose (G.degree v) 3 ≤
      48 * (2 * Nat.choose n 3 * 2 ^ (n - 3)) := by
    calc 48 * ∑ v : Fin n → Bool, Nat.choose (G.degree v) 3
        ≤ 2 * (6 * Nat.choose n 3 * (8 * 2 ^ (n - 3))) := hsum_ub
      _ = 48 * (2 * Nat.choose n 3 * 2 ^ (n - 3)) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-! ### Oriented `Q_1`-Rooted `Q_2`-Flag Sum-of-Squares Theorem (`≤ 247/400 + O(1/n) = 0.6175 + O(1/n)`) -/

/-- Exact integer weight vector `W_0` on the 7 oriented `Q_1`-rooted `Q_2`-flags for `e ∈ G`
(index `7` corresponds to a `C_4` and is set to `0`). -/
private def sosW0 (t : Fin 8) : ℤ :=
  match t with
  | ⟨0, _⟩ => -3 | ⟨1, _⟩ => 3 | ⟨2, _⟩ => 4 | ⟨3, _⟩ => -3
  | ⟨4, _⟩ => -5 | ⟨5, _⟩ => -1 | ⟨6, _⟩ => 4 | ⟨7, _⟩ => 0

/-- Exact integer weight vector `W_1` on oriented `Q_1`-rooted `Q_2`-flags for `e ∈ G`. -/
private def sosW1 (t : Fin 8) : ℤ :=
  match t with
  | ⟨0, _⟩ => -3 | ⟨1, _⟩ => 4 | ⟨2, _⟩ => 5 | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => -6 | ⟨5, _⟩ => -10 | ⟨6, _⟩ => 5 | ⟨7, _⟩ => 0

/-- Exact integer weight vector `U_0` on oriented `Q_1`-rooted `Q_2`-flags for `e ∈ G^c`. -/
private def sosU0 (t : Fin 8) : ℤ :=
  match t with
  | ⟨0, _⟩ => -2 | ⟨1, _⟩ => -6 | ⟨2, _⟩ => -12 | ⟨3, _⟩ => -10
  | ⟨4, _⟩ => -2 | ⟨5, _⟩ => 2 | ⟨6, _⟩ => -1 | ⟨7, _⟩ => 6

/-- Exact integer weight vector `U_1` on oriented `Q_1`-rooted `Q_2`-flags for `e ∈ G^c`. -/
private def sosU1 (t : Fin 8) : ℤ :=
  match t with
  | ⟨0, _⟩ => 7 | ⟨1, _⟩ => 4 | ⟨2, _⟩ => -1 | ⟨3, _⟩ => -4
  | ⟨4, _⟩ => -2 | ⟨5, _⟩ => 2 | ⟨6, _⟩ => 0 | ⟨7, _⟩ => -2

private lemma sosW_sq_le (t : Fin 8) : sosW0 t ^ 2 + sosW1 t ^ 2 ≤ 145 := by
  fin_cases t <;> decide

private lemma sosU_sq_le (t : Fin 8) : sosU0 t ^ 2 + sosU1 t ^ 2 ≤ 145 := by
  fin_cases t <;> decide

/-- Shifted non-negative `Nat` lookup table for `100 + sosW0 t1 * sosW0 t2 + sosW1 t1 * sosW1 t2 + 200`. -/
private def sosMGShift (t1 t2 : Fin 8) : ℕ :=
  (300 + sosW0 t1 * sosW0 t2 + sosW1 t1 * sosW1 t2).toNat

/-- Shifted non-negative `Nat` lookup table for `sosU0 t1 * sosU0 t2 + sosU1 t1 * sosU1 t2 + 200`. -/
private def sosMUShift (t1 t2 : Fin 8) : ℕ :=
  (200 + sosU0 t1 * sosU0 t2 + sosU1 t1 * sosU1 t2).toNat

private lemma sosMGShift_coe (t1 t2 : Fin 8) :
    (sosMGShift t1 t2 : ℤ) = 300 + sosW0 t1 * sosW0 t2 + sosW1 t1 * sosW1 t2 := by
  fin_cases t1 <;> fin_cases t2 <;> decide

private lemma sosMUShift_coe (t1 t2 : Fin 8) :
    (sosMUShift t1 t2 : ℤ) = 200 + sosU0 t1 * sosU0 t2 + sosU1 t1 * sosU1 t2 := by
  fin_cases t1 <;> fin_cases t2 <;> decide

/-- Flag code `4 * a + 2 * b + o : Fin 8` from 3 Booleans. -/
private def mkFlag (a b o : Bool) : Fin 8 :=
  ⟨(if a then 4 else 0) + (if b then 2 else 0) + (if o then 1 else 0), by
    cases a <;> cases b <;> cases o <;> simp⟩

/-- Contribution of one oriented edge `(e, a1, b1, o1, a2, b2, o2)` in `Q_3` (shifted by `+200`). -/
private def edgeContribShift (e a1 b1 o1 a2 b2 o2 : Bool) : ℕ :=
  if e then sosMGShift (mkFlag a1 b1 o1) (mkFlag a2 b2 o2)
  else sosMUShift (mkFlag a1 b1 o1) (mkFlag a2 b2 o2)

/-- Full shifted `Q_3` flag-SOS score on 12 edge Booleans:
- `x00, x01, x10, x11`: direction-0 edges at `(y, z) = (0,0), (0,1), (1,0), (1,1)`
- `y00, y01, y10, y11`: direction-1 edges at `(x, z) = (0,0), (0,1), (1,0), (1,1)`
- `z00, z01, z10, z11`: direction-2 edges at `(x, y) = (0,0), (0,1), (1,0), (1,1)`
Every `C_4`-free `Q_3` satisfies `q3ScoreShift ≤ 6282 (= 1482 + 24 * 200)`. -/
private def q3ScoreShift (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) : ℕ :=
  -- 8 oriented x-edges (dir 0; other dirs are 1 [y] and 2 [z]):
  -- (0,0,0) -> (1,0,0): e=x00; dir1: (y00, y10, x10); dir2: (z00, z10, x01)
  edgeContribShift x00 y00 y10 x10 z00 z10 x01 +
  -- (1,0,0) -> (0,0,0): e=x00; dir1: (y10, y00, x10); dir2: (z10, z00, x01)
  edgeContribShift x00 y10 y00 x10 z10 z00 x01 +
  -- (0,0,1) -> (1,0,1): e=x01; dir1: (y01, y11, x11); dir2: (z00, z10, x00)
  edgeContribShift x01 y01 y11 x11 z00 z10 x00 +
  -- (1,0,1) -> (0,0,1): e=x01; dir1: (y11, y01, x11); dir2: (z10, z00, x00)
  edgeContribShift x01 y11 y01 x11 z10 z00 x00 +
  -- (0,1,0) -> (1,1,0): e=x10; dir1: (y00, y10, x00); dir2: (z01, z11, x11)
  edgeContribShift x10 y00 y10 x00 z01 z11 x11 +
  -- (1,1,0) -> (0,1,0): e=x10; dir1: (y10, y00, x00); dir2: (z11, z01, x11)
  edgeContribShift x10 y10 y00 x00 z11 z01 x11 +
  -- (0,1,1) -> (1,1,1): e=x11; dir1: (y01, y11, x01); dir2: (z01, z11, x10)
  edgeContribShift x11 y01 y11 x01 z01 z11 x10 +
  -- (1,1,1) -> (0,1,1): e=x11; dir1: (y11, y01, x01); dir2: (z11, z01, x10)
  edgeContribShift x11 y11 y01 x01 z11 z01 x10 +
  -- 8 oriented y-edges (dir 1; other dirs are 0 [x] and 2 [z]):
  -- (0,0,0) -> (0,1,0): e=y00; dir0: (x00, x10, y10); dir2: (z00, z01, y01)
  edgeContribShift y00 x00 x10 y10 z00 z01 y01 +
  -- (0,1,0) -> (0,0,0): e=y00; dir0: (x10, x00, y10); dir2: (z01, z00, y01)
  edgeContribShift y00 x10 x00 y10 z01 z00 y01 +
  -- (0,0,1) -> (0,1,1): e=y01; dir0: (x01, x11, y11); dir2: (z00, z01, y00)
  edgeContribShift y01 x01 x11 y11 z00 z01 y00 +
  -- (0,1,1) -> (0,0,1): e=y01; dir0: (x11, x01, y11); dir2: (z01, z00, y00)
  edgeContribShift y01 x11 x01 y11 z01 z00 y00 +
  -- (1,0,0) -> (1,1,0): e=y10; dir0: (x00, x10, y00); dir2: (z10, z11, y11)
  edgeContribShift y10 x00 x10 y00 z10 z11 y11 +
  -- (1,1,0) -> (1,0,0): e=y10; dir0: (x10, x00, y00); dir2: (z11, z10, y11)
  edgeContribShift y10 x10 x00 y00 z11 z10 y11 +
  -- (1,0,1) -> (1,1,1): e=y11; dir0: (x01, x11, y01); dir2: (z10, z11, y10)
  edgeContribShift y11 x01 x11 y01 z10 z11 y10 +
  -- (1,1,1) -> (1,0,1): e=y11; dir0: (x11, x01, y01); dir2: (z11, z10, y10)
  edgeContribShift y11 x11 x01 y01 z11 z10 y10 +
  -- 8 oriented z-edges (dir 2; other dirs are 0 [x] and 1 [y]):
  -- (0,0,0) -> (0,0,1): e=z00; dir0: (x00, x01, z10); dir1: (y00, y01, z01)
  edgeContribShift z00 x00 x01 z10 y00 y01 z01 +
  -- (0,0,1) -> (0,0,0): e=z00; dir0: (x01, x00, z10); dir1: (y01, y00, z01)
  edgeContribShift z00 x01 x00 z10 y01 y00 z01 +
  -- (0,1,0) -> (0,1,1): e=z01; dir0: (x10, x11, z11); dir1: (y00, y01, z00)
  edgeContribShift z01 x10 x11 z11 y00 y01 z00 +
  -- (0,1,1) -> (0,1,0): e=z01; dir0: (x11, x10, z11); dir1: (y01, y00, z00)
  edgeContribShift z01 x11 x10 z11 y01 y00 z00 +
  -- (1,0,0) -> (1,0,1): e=z10; dir0: (x00, x01, z00); dir1: (y10, y11, z11)
  edgeContribShift z10 x00 x01 z00 y10 y11 z11 +
  -- (1,0,1) -> (1,0,0): e=z10; dir0: (x01, x00, z00); dir1: (y11, y10, z11)
  edgeContribShift z10 x01 x00 z00 y11 y10 z11 +
  -- (1,1,0) -> (1,1,1): e=z11; dir0: (x10, x11, z01); dir1: (y10, y11, z10)
  edgeContribShift z11 x10 x11 z01 y10 y11 z10 +
  -- (1,1,1) -> (1,1,0): e=z11; dir0: (x11, x10, z01); dir1: (y11, y10, z10)
  edgeContribShift z11 x11 x10 z01 y11 y10 z10

/-- `C_4`-freeness predicate on the 12 edge Booleans of `Q_3` (the 6 2-faces). -/
private def q3IsC4FreeBool (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool) : Bool :=
  !(y00 && y01 && z00 && z01) &&
  !(y10 && y11 && z10 && z11) &&
  !(x00 && x01 && z00 && z10) &&
  !(x10 && x11 && z01 && z11) &&
  !(x00 && x10 && y00 && y10) &&
  !(x01 && x11 && y01 && y11)

/-- Kernel-checked `decide` helper for fixed `(x00, x01, x10, x11)` (256 cases each, 0 `native_decide`). -/
private def checkQ3Slice (x00 x01 x10 x11 : Bool) : Bool :=
  [false, true].all fun y00 =>
  [false, true].all fun y01 =>
  [false, true].all fun y10 =>
  [false, true].all fun y11 =>
  [false, true].all fun z00 =>
  [false, true].all fun z01 =>
  [false, true].all fun z10 =>
  [false, true].all fun z11 =>
    !q3IsC4FreeBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ||
    decide (q3ScoreShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ≤ 6282)

private lemma checkQ3_0000 : checkQ3Slice false false false false = true := by decide
private lemma checkQ3_0001 : checkQ3Slice false false false true  = true := by decide
private lemma checkQ3_0010 : checkQ3Slice false false true  false = true := by decide
private lemma checkQ3_0011 : checkQ3Slice false false true  true  = true := by decide
private lemma checkQ3_0100 : checkQ3Slice false true  false false = true := by decide
private lemma checkQ3_0101 : checkQ3Slice false true  false true  = true := by decide
private lemma checkQ3_0110 : checkQ3Slice false true  true  false = true := by decide
private lemma checkQ3_0111 : checkQ3Slice false true  true  true  = true := by decide
private lemma checkQ3_1000 : checkQ3Slice true  false false false = true := by decide
private lemma checkQ3_1001 : checkQ3Slice true  false false true  = true := by decide
private lemma checkQ3_1010 : checkQ3Slice true  false true  false = true := by decide
private lemma checkQ3_1011 : checkQ3Slice true  false true  true  = true := by decide
private lemma checkQ3_1100 : checkQ3Slice true  true  false false = true := by decide
private lemma checkQ3_1101 : checkQ3Slice true  true  false true  = true := by decide
private lemma checkQ3_1110 : checkQ3Slice true  true  true  false = true := by decide
private lemma checkQ3_1111 : checkQ3Slice true  true  true  true  = true := by decide

private lemma checkQ3Slice_all (x00 x01 x10 x11 : Bool) :
    checkQ3Slice x00 x01 x10 x11 = true := by
  cases x00 <;> cases x01 <;> cases x10 <;> cases x11
  · exact checkQ3_0000
  · exact checkQ3_0001
  · exact checkQ3_0010
  · exact checkQ3_0011
  · exact checkQ3_0100
  · exact checkQ3_0101
  · exact checkQ3_0110
  · exact checkQ3_0111
  · exact checkQ3_1000
  · exact checkQ3_1001
  · exact checkQ3_1010
  · exact checkQ3_1011
  · exact checkQ3_1100
  · exact checkQ3_1101
  · exact checkQ3_1110
  · exact checkQ3_1111

private lemma list_all_bool {P : Bool → Bool} (h : [false, true].all P = true) (b : Bool) :
    P b = true := by
  cases b <;> simp_all

private lemma q3ScoreShift_le_6282 (x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : Bool)
    (hc4 : q3IsC4FreeBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 = true) :
    q3ScoreShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ≤ 6282 := by
  have h0 : [false, true].all (fun y00 =>
      [false, true].all fun y01 =>
      [false, true].all fun y10 =>
      [false, true].all fun y11 =>
      [false, true].all fun z00 =>
      [false, true].all fun z01 =>
      [false, true].all fun z10 =>
      [false, true].all fun z11 =>
        !q3IsC4FreeBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ||
        decide (q3ScoreShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 ≤ 6282)) = true :=
    checkQ3Slice_all x00 x01 x10 x11
  have h1 := list_all_bool h0 y00
  have h2 := list_all_bool h1 y01
  have h3 := list_all_bool h2 y10
  have h4 := list_all_bool h3 y11
  have h5 := list_all_bool h4 z00
  have h6 := list_all_bool h5 z01
  have h7 := list_all_bool h6 z10
  have h8 := list_all_bool h7 z11
  simp only [hc4, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h8
  exact h8

/-- Oriented `Q_1`-rooted `Q_2`-flag code for `(u, i, j)` in `G ≤ Q_n`. -/
private def edgeFlag {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j : Fin n) : Fin 8 :=
  mkFlag (decide (G.Adj u (flip u j)))
         (decide (G.Adj (flip u i) (flip (flip u i) j)))
         (decide (G.Adj (flip u j) (flip (flip u j) i)))

/-- Unshifted `ℤ` score of one oriented edge `(u, i)` with two other directions `(j1, j2)`. -/
private def orientedEdgeTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j1 j2 : Fin n) : ℤ :=
  let t1 := edgeFlag G u i j1
  let t2 := edgeFlag G u i j2
  if G.Adj u (flip u i) then
    100 + sosW0 t1 * sosW0 t2 + sosW1 t1 * sosW1 t2
  else
    sosU0 t1 * sosU0 t2 + sosU1 t1 * sosU1 t2

private lemma orientedEdgeTerm_eq_shift {n : ℕ} (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] (u : Fin n → Bool) (i j1 j2 : Fin n) :
    orientedEdgeTerm G u i j1 j2 + 200 =
      (edgeContribShift (decide (G.Adj u (flip u i)))
        (decide (G.Adj u (flip u j1)))
        (decide (G.Adj (flip u i) (flip (flip u i) j1)))
        (decide (G.Adj (flip u j1) (flip (flip u j1) i)))
        (decide (G.Adj u (flip u j2)))
        (decide (G.Adj (flip u i) (flip (flip u i) j2)))
        (decide (G.Adj (flip u j2) (flip (flip u j2) i))) : ℤ) := by
  unfold orientedEdgeTerm edgeContribShift edgeFlag
  by_cases h : G.Adj u (flip u i)
  · simp only [h, ↓reduceIte, decide_true, sosMGShift_coe]
    ring
  · simp only [h, ↓reduceIte, decide_false, Bool.false_eq_true, sosMUShift_coe]
    ring

private lemma flip3_0 (p q r : Bool) : flip ![p, q, r] 0 = ![!p, q, r] := by
  ext k; fin_cases k <;> simp [flip]

private lemma flip3_1 (p q r : Bool) : flip ![p, q, r] 1 = ![p, !q, r] := by
  ext k; fin_cases k <;> simp [flip]

private lemma flip3_2 (p q r : Bool) : flip ![p, q, r] 2 = ![p, q, !r] := by
  ext k; fin_cases k <;> simp [flip]

/-- The sum of `orientedEdgeTerm` over all 24 oriented edges of `embedQ3 u a b c` is `≤ 1482`! -/
private lemma q3_sos_local_bound {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : G ≤ Q n) (hfree : IsC4Free G)
    (u : Fin n → Bool) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let v (w : Fin 3 → Bool) := embedQ3 u a b c w
    (∑ w : Fin 3 → Bool,
      (orientedEdgeTerm G (v w) a b c +
       orientedEdgeTerm G (v w) b a c +
       orientedEdgeTerm G (v w) c a b)) ≤ 1482 := by
  intro v
  -- Helper equalities identifying flipped vertices with the 8 corners of `v`!
  have ha000 : flip (v ![false, false, false]) a = v ![true, false, false] := by
    have h := embedQ3_flip0 u a b c ![false, false, false]; rw [flip3_0] at h; exact h.symm
  have ha001 : flip (v ![false, false, true]) a = v ![true, false, true] := by
    have h := embedQ3_flip0 u a b c ![false, false, true]; rw [flip3_0] at h; exact h.symm
  have ha010 : flip (v ![false, true, false]) a = v ![true, true, false] := by
    have h := embedQ3_flip0 u a b c ![false, true, false]; rw [flip3_0] at h; exact h.symm
  have ha011 : flip (v ![false, true, true]) a = v ![true, true, true] := by
    have h := embedQ3_flip0 u a b c ![false, true, true]; rw [flip3_0] at h; exact h.symm
  have hb000 : flip (v ![false, false, false]) b = v ![false, true, false] := by
    have h := embedQ3_flip1 u a b c ![false, false, false]; rw [flip3_1] at h; exact h.symm
  have hb001 : flip (v ![false, false, true]) b = v ![false, true, true] := by
    have h := embedQ3_flip1 u a b c ![false, false, true]; rw [flip3_1] at h; exact h.symm
  have hb100 : flip (v ![true, false, false]) b = v ![true, true, false] := by
    have h := embedQ3_flip1 u a b c ![true, false, false]; rw [flip3_1] at h; exact h.symm
  have hb101 : flip (v ![true, false, true]) b = v ![true, true, true] := by
    have h := embedQ3_flip1 u a b c ![true, false, true]; rw [flip3_1] at h; exact h.symm
  have hc000 : flip (v ![false, false, false]) c = v ![false, false, true] := by
    have h := embedQ3_flip2 u a b c ![false, false, false]; rw [flip3_2] at h; exact h.symm
  have hc010 : flip (v ![false, true, false]) c = v ![false, true, true] := by
    have h := embedQ3_flip2 u a b c ![false, true, false]; rw [flip3_2] at h; exact h.symm
  have hc100 : flip (v ![true, false, false]) c = v ![true, false, true] := by
    have h := embedQ3_flip2 u a b c ![true, false, false]; rw [flip3_2] at h; exact h.symm
  have hc110 : flip (v ![true, true, false]) c = v ![true, true, true] := by
    have h := embedQ3_flip2 u a b c ![true, true, false]; rw [flip3_2] at h; exact h.symm
  -- Reverse flip equalities
  have ha100 : flip (v ![true, false, false]) a = v ![false, false, false] := by rw [← ha000, flip_flip]
  have ha101 : flip (v ![true, false, true]) a = v ![false, false, true] := by rw [← ha001, flip_flip]
  have ha110 : flip (v ![true, true, false]) a = v ![false, true, false] := by rw [← ha010, flip_flip]
  have ha111 : flip (v ![true, true, true]) a = v ![false, true, true] := by rw [← ha011, flip_flip]
  have hb010 : flip (v ![false, true, false]) b = v ![false, false, false] := by rw [← hb000, flip_flip]
  have hb011 : flip (v ![false, true, true]) b = v ![false, false, true] := by rw [← hb001, flip_flip]
  have hb110 : flip (v ![true, true, false]) b = v ![true, false, false] := by rw [← hb100, flip_flip]
  have hb111 : flip (v ![true, true, true]) b = v ![true, false, true] := by rw [← hb101, flip_flip]
  have hc001 : flip (v ![false, false, true]) c = v ![false, false, false] := by rw [← hc000, flip_flip]
  have hc011 : flip (v ![false, true, true]) c = v ![false, true, false] := by rw [← hc010, flip_flip]
  have hc101 : flip (v ![true, false, true]) c = v ![true, false, false] := by rw [← hc100, flip_flip]
  have hc111 : flip (v ![true, true, true]) c = v ![true, true, false] := by rw [← hc110, flip_flip]
  -- Define the 12 edge Booleans of `G` on the embedded `Q_3`
  let x00 : Bool := decide (G.Adj (v ![false, false, false]) (v ![true, false, false]))
  let x01 : Bool := decide (G.Adj (v ![false, false, true])  (v ![true, false, true]))
  let x10 : Bool := decide (G.Adj (v ![false, true, false])  (v ![true, true, false]))
  let x11 : Bool := decide (G.Adj (v ![false, true, true])   (v ![true, true, true]))
  let y00 : Bool := decide (G.Adj (v ![false, false, false]) (v ![false, true, false]))
  let y01 : Bool := decide (G.Adj (v ![false, false, true])  (v ![false, true, true]))
  let y10 : Bool := decide (G.Adj (v ![true, false, false])  (v ![true, true, false]))
  let y11 : Bool := decide (G.Adj (v ![true, false, true])   (v ![true, true, true]))
  let z00 : Bool := decide (G.Adj (v ![false, false, false]) (v ![false, false, true]))
  let z01 : Bool := decide (G.Adj (v ![false, true, false])  (v ![false, true, true]))
  let z10 : Bool := decide (G.Adj (v ![true, false, false])  (v ![true, false, true]))
  let z11 : Bool := decide (G.Adj (v ![true, true, false])   (v ![true, true, true]))
  -- Check C_4-freeness on the 6 faces
  have hnoface := (isC4Free_iff_no_face hG).mp hfree
  have hf_x0 : (!(y00 && y01 && z00 && z01)) = true := by
    cases h1 : y00 <;> cases h2 : y01 <;> cases h3 : z00 <;> cases h4 : z01 <;> try rfl
    exfalso; simp only [y00, y01, z00, z01, decide_eq_true_eq] at h1 h2 h3 h4
    rw [← hb000] at h1 h4; rw [← hc000] at h2 h3; rw [← hc010] at h4; rw [← hb001] at h2
    rw [← hb000] at h4; rw [← hc000] at h2
    exact hnoface (v ![false, false, false]) b c hbc ⟨h1, h4, by rw [flip_comm]; exact h2.symm, h3.symm⟩
  have hf_x1 : (!(y10 && y11 && z10 && z11)) = true := by
    cases h1 : y10 <;> cases h2 : y11 <;> cases h3 : z10 <;> cases h4 : z11 <;> try rfl
    exfalso; simp only [y10, y11, z10, z11, decide_eq_true_eq] at h1 h2 h3 h4
    rw [← hb100] at h1 h4; rw [← hc100] at h2 h3; rw [← hc110] at h4; rw [← hb101] at h2
    rw [← hb100] at h4; rw [← hc100] at h2
    exact hnoface (v ![true, false, false]) b c hbc ⟨h1, h4, by rw [flip_comm]; exact h2.symm, h3.symm⟩
  have hf_y0 : (!(x00 && x01 && z00 && z10)) = true := by
    cases h1 : x00 <;> cases h2 : x01 <;> cases h3 : z00 <;> cases h4 : z10 <;> try rfl
    exfalso; simp only [x00, x01, z00, z10, decide_eq_true_eq] at h1 h2 h3 h4
    rw [← ha000] at h1 h4; rw [← hc000] at h2 h3; rw [← hc100] at h4; rw [← ha001] at h2
    rw [← ha000] at h4; rw [← hc000] at h2
    exact hnoface (v ![false, false, false]) a c hac ⟨h1, h4, by rw [flip_comm]; exact h2.symm, h3.symm⟩
  have hf_y1 : (!(x10 && x11 && z01 && z11)) = true := by
    cases h1 : x10 <;> cases h2 : x11 <;> cases h3 : z01 <;> cases h4 : z11 <;> try rfl
    exfalso; simp only [x10, x11, z01, z11, decide_eq_true_eq] at h1 h2 h3 h4
    rw [← ha010] at h1 h4; rw [← hc010] at h2 h3; rw [← hc110] at h4; rw [← ha011] at h2
    rw [← ha010] at h4; rw [← hc010] at h2
    exact hnoface (v ![false, true, false]) a c hac ⟨h1, h4, by rw [flip_comm]; exact h2.symm, h3.symm⟩
  have hf_z0 : (!(x00 && x10 && y00 && y10)) = true := by
    cases h1 : x00 <;> cases h2 : x10 <;> cases h3 : y00 <;> cases h4 : y10 <;> try rfl
    exfalso; simp only [x00, x10, y00, y10, decide_eq_true_eq] at h1 h2 h3 h4
    rw [← ha000] at h1 h4; rw [← hb000] at h2 h3; rw [← hb100] at h4; rw [← ha010] at h2
    rw [← ha000] at h4; rw [← hb000] at h2
    exact hnoface (v ![false, false, false]) a b hab ⟨h1, h4, by rw [flip_comm]; exact h2.symm, h3.symm⟩
  have hf_z1 : (!(x01 && x11 && y01 && y11)) = true := by
    cases h1 : x01 <;> cases h2 : x11 <;> cases h3 : y01 <;> cases h4 : y11 <;> try rfl
    exfalso; simp only [x01, x11, y01, y11, decide_eq_true_eq] at h1 h2 h3 h4
    rw [← ha001] at h1 h4; rw [← hb001] at h2 h3; rw [← hb101] at h4; rw [← ha011] at h2
    rw [← ha001] at h4; rw [← hb001] at h2
    exact hnoface (v ![false, false, true]) a b hab ⟨h1, h4, by rw [flip_comm]; exact h2.symm, h3.symm⟩
  have hc4 : q3IsC4FreeBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 = true := by
    unfold q3IsC4FreeBool
    rw [hf_x0, hf_x1, hf_y0, hf_y1, hf_z0, hf_z1]; rfl
  have hbound : (q3ScoreShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : ℤ) ≤ 6282 :=
    Int.ofNat_le.mpr (q3ScoreShift_le_6282 _ _ _ _ _ _ _ _ _ _ _ _ hc4)
  -- Express the sum over w : Fin 3 → Bool explicitly over the 8 vertices of Q_3!
  have hsum8 :
      (∑ w : Fin 3 → Bool,
        (orientedEdgeTerm G (v w) a b c + orientedEdgeTerm G (v w) b a c + orientedEdgeTerm G (v w) c a b)) + 4800 =
      (q3ScoreShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : ℤ) := by
    let e3 : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
      { toFun := fun w => (w 0, w 1, w 2)
        invFun := fun p => ![p.1, p.2.1, p.2.2]
        left_inv := fun w => by ext k; fin_cases k <;> rfl
        right_inv := fun ⟨p1, p2, p3⟩ => rfl }
    rw [Fintype.sum_equiv e3 _ (fun p =>
      orientedEdgeTerm G (v ![p.1, p.2.1, p.2.2]) a b c +
      orientedEdgeTerm G (v ![p.1, p.2.1, p.2.2]) b a c +
      orientedEdgeTerm G (v ![p.1, p.2.1, p.2.2]) c a b) (fun w => by
        have hw : w = ![w 0, w 1, w 2] := by ext k; fin_cases k <;> rfl
        conv_lhs => rw [hw]
        rfl)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    have hshift_sub : ∀ (x : Fin n → Bool) (i j1 j2 : Fin n),
        orientedEdgeTerm G x i j1 j2 =
        (edgeContribShift (decide (G.Adj x (flip x i)))
          (decide (G.Adj x (flip x j1)))
          (decide (G.Adj (flip x i) (flip (flip x i) j1)))
          (decide (G.Adj (flip x j1) (flip (flip x j1) i)))
          (decide (G.Adj x (flip x j2)))
          (decide (G.Adj (flip x i) (flip (flip x i) j2)))
          (decide (G.Adj (flip x j2) (flip (flip x j2) i))) : ℤ) - 200 := by
      intro x i j1 j2
      have h := orientedEdgeTerm_eq_shift G x i j1 j2
      linarith
    simp_rw [hshift_sub]
    have hsym : ∀ p q : Fin n → Bool, decide (G.Adj q p) = decide (G.Adj p q) := fun p q => by
      simp [SimpleGraph.adj_comm]
    -- Forward and reverse edge equalities matching x00..z11 syntactically
    have hx00_f : decide (G.Adj (v ![false, false, false]) (v ![true, false, false])) = x00 := rfl
    have hx01_f : decide (G.Adj (v ![false, false, true])  (v ![true, false, true]))  = x01 := rfl
    have hx10_f : decide (G.Adj (v ![false, true, false])  (v ![true, true, false]))  = x10 := rfl
    have hx11_f : decide (G.Adj (v ![false, true, true])   (v ![true, true, true]))   = x11 := rfl
    have hy00_f : decide (G.Adj (v ![false, false, false]) (v ![false, true, false])) = y00 := rfl
    have hy01_f : decide (G.Adj (v ![false, false, true])  (v ![false, true, true]))  = y01 := rfl
    have hy10_f : decide (G.Adj (v ![true, false, false])  (v ![true, true, false]))  = y10 := rfl
    have hy11_f : decide (G.Adj (v ![true, false, true])   (v ![true, true, true]))   = y11 := rfl
    have hz00_f : decide (G.Adj (v ![false, false, false]) (v ![false, false, true])) = z00 := rfl
    have hz01_f : decide (G.Adj (v ![false, true, false])  (v ![false, true, true]))  = z01 := rfl
    have hz10_f : decide (G.Adj (v ![true, false, false])  (v ![true, false, true]))  = z10 := rfl
    have hz11_f : decide (G.Adj (v ![true, true, false])   (v ![true, true, true]))   = z11 := rfl
    have hx00_r : decide (G.Adj (v ![true, false, false]) (v ![false, false, false])) = x00 := hsym _ _
    have hx01_r : decide (G.Adj (v ![true, false, true])  (v ![false, false, true]))  = x01 := hsym _ _
    have hx10_r : decide (G.Adj (v ![true, true, false])  (v ![false, true, false]))  = x10 := hsym _ _
    have hx11_r : decide (G.Adj (v ![true, true, true])   (v ![false, true, true]))   = x11 := hsym _ _
    have hy00_r : decide (G.Adj (v ![false, true, false]) (v ![false, false, false])) = y00 := hsym _ _
    have hy01_r : decide (G.Adj (v ![false, true, true])  (v ![false, false, true]))  = y01 := hsym _ _
    have hy10_r : decide (G.Adj (v ![true, true, false])  (v ![true, false, false]))  = y10 := hsym _ _
    have hy11_r : decide (G.Adj (v ![true, true, true])   (v ![true, false, true]))   = y11 := hsym _ _
    have hz00_r : decide (G.Adj (v ![false, false, true]) (v ![false, false, false])) = z00 := hsym _ _
    have hz01_r : decide (G.Adj (v ![false, true, true])  (v ![false, true, false]))  = z01 := hsym _ _
    have hz10_r : decide (G.Adj (v ![true, false, true])  (v ![true, false, false]))  = z10 := hsym _ _
    have hz11_r : decide (G.Adj (v ![true, true, true])   (v ![true, true, false]))   = z11 := hsym _ _
    simp only [ha000, ha001, ha010, ha011, ha100, ha101, ha110, ha111,
               hb000, hb001, hb100, hb101, hb010, hb011, hb110, hb111,
               hc000, hc010, hc100, hc110, hc001, hc011, hc101, hc111,
               hx00_f, hx01_f, hx10_f, hx11_f,
               hy00_f, hy01_f, hy10_f, hy11_f,
               hz00_f, hz01_f, hz10_f, hz11_f,
               hx00_r, hx01_r, hx10_r, hx11_r,
               hy00_r, hy01_r, hy10_r, hy11_r,
               hz00_r, hz01_r, hz10_r, hz11_r]
    change _ = (q3ScoreShift x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 : ℤ)
    dsimp only [q3ScoreShift]
    push_cast
    ring
  linarith

/-- **Theorem 4.5 (`ppl033_flag_sos_upper_exact`):**
Oriented `Q_1`-rooted `Q_2`-flag Sum-of-Squares upper bound on `Q_3`:
for every `n ≥ 3` and every `C_4`-free subgraph `G ≤ Q_n`,
`800 * (n - 2) * |E(G)| ≤ 247 * n * (n - 2) * 2 ^ n + 580 * n * 2 ^ n`
(equivalently `|E(G)| ≤ (247 / 400 + 29 / (20 * (n - 2))) * (n * 2 ^ (n - 1))`,
giving asymptotic Turán density `≤ 247 / 400 = 0.6175`, strictly beating
Chung 1992 `(2 + √13)/9 ≈ 0.62284`, Thomason–Wagner 2009 `0.62256`, `0.623`, and `5/8 = 0.625`!). -/
theorem ppl033_flag_sos_upper_exact (n : ℕ) (hn : 3 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    800 * (n - 2) * G.edgeFinset.card ≤ 247 * n * (n - 2) * 2 ^ n + 580 * n * 2 ^ n := by
  classical
  rw [edgeFinset_card_congr G _ (SimpleGraph.fintypeEdgeSet G)]
  clear ‹Fintype G.edgeSet›
  -- Sum q3_sos_local_bound over all pairwise distinct (a, b, c) and u : Fin n → Bool!
  have hsum_ub :
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
          (orientedEdgeTerm G (embedQ3 u a b c w) a b c +
           orientedEdgeTerm G (embedQ3 u a b c w) b a c +
           orientedEdgeTerm G (embedQ3 u a b c w) c a b)) ≤
      1482 * ((n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 : ℤ) ^ n) := by
    have h1 :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
            (orientedEdgeTerm G (embedQ3 u a b c w) a b c +
             orientedEdgeTerm G (embedQ3 u a b c w) b a c +
             orientedEdgeTerm G (embedQ3 u a b c w) c a b)) ≤
        ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ _c ∈ (Finset.univ.erase a).erase b,
          ∑ _u : Fin n → Bool, (1482 : ℤ) := by
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b hb =>
        Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun u _ => ?_
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
      have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
      exact q3_sos_local_bound G hG hfree u hba.symm hca.symm hcb.symm
    refine le_trans h1 ?_
    have hcard2 : ∀ (a : Fin n) (b : Fin n), b ∈ Finset.univ.erase a →
        ((Finset.univ.erase a).erase b).card = n - 2 := by
      intro a b hb
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]; omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
      Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∀ a : Fin n,
        ∑ b ∈ Finset.univ.erase a, (((Finset.univ.erase a).erase b).card : ℤ) * ((2 : ℤ) ^ n * 1482) =
        (((n - 1 : ℕ) : ℤ) * (((n - 2 : ℕ) : ℤ) * ((2 : ℤ) ^ n * 1482))) := by
      intro a
      rw [Finset.sum_congr rfl fun b hb => by rw [hcard2 a b hb],
          Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2' : ∀ a : Fin n,
        ∑ b ∈ Finset.univ.erase a, (((Finset.univ.erase a).erase b).card : ℤ) * (((2 ^ n : ℕ) : ℤ) * 1482) =
        (((n - 1 : ℕ) : ℤ) * (((n - 2 : ℕ) : ℤ) * ((2 : ℤ) ^ n * 1482))) := by
      intro a; simpa using h2 a
    simp_rw [h2', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    rw [hn1, hn2]; ring_nf; exact le_rfl
  -- Evaluate LHS: all 3 terms (a,b,c), (b,a,c), (c,a,b) give the EXACT same sum over all distinct triples!
  -- And each of the 8 vertices w gives the exact same sum over u (by embedQ3_equiv_u)!
  let T : ℤ := ∑ i : Fin n, ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
      ∑ v : Fin n → Bool, orientedEdgeTerm G v i j1 j2
  have hlhs_eq :
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
          (orientedEdgeTerm G (embedQ3 u a b c w) a b c +
           orientedEdgeTerm G (embedQ3 u a b c w) b a c +
           orientedEdgeTerm G (embedQ3 u a b c w) c a b)) =
      24 * T := by
    have hinner : ∀ a b c : Fin n,
        (∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
          (orientedEdgeTerm G (embedQ3 u a b c w) a b c +
           orientedEdgeTerm G (embedQ3 u a b c w) b a c +
           orientedEdgeTerm G (embedQ3 u a b c w) c a b)) =
        8 * ((∑ v : Fin n → Bool, orientedEdgeTerm G v a b c) +
             (∑ v : Fin n → Bool, orientedEdgeTerm G v b a c) +
             (∑ v : Fin n → Bool, orientedEdgeTerm G v c a b)) := by
      intro a b c
      rw [Finset.sum_comm]
      have hw : ∀ w : Fin 3 → Bool,
          (∑ u : Fin n → Bool,
            (orientedEdgeTerm G (embedQ3 u a b c w) a b c +
             orientedEdgeTerm G (embedQ3 u a b c w) b a c +
             orientedEdgeTerm G (embedQ3 u a b c w) c a b)) =
          (∑ v : Fin n → Bool, orientedEdgeTerm G v a b c) +
          (∑ v : Fin n → Bool, orientedEdgeTerm G v b a c) +
          (∑ v : Fin n → Bool, orientedEdgeTerm G v c a b) := by
        intro w
        rw [Fintype.sum_bijective (fun u => embedQ3 u a b c w) (embedQ3_equiv_u a b c w) _
          (fun v => orientedEdgeTerm G v a b c + orientedEdgeTerm G v b a c + orientedEdgeTerm G v c a b)
          (fun _ => rfl)]
        simp only [Finset.sum_add_distrib]
      simp_rw [hw]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
      simp
    simp_rw [hinner, ← Finset.mul_sum]
    -- Split the sum of 3 terms over pairwise distinct (a, b, c)
    have hsplit3 :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ((∑ v : Fin n → Bool, orientedEdgeTerm G v a b c) +
           (∑ v : Fin n → Bool, orientedEdgeTerm G v b a c) +
           (∑ v : Fin n → Bool, orientedEdgeTerm G v c a b))) =
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool, orientedEdgeTerm G v a b c) +
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool, orientedEdgeTerm G v b a c) +
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool, orientedEdgeTerm G v c a b) := by
      simp only [Finset.sum_add_distrib]
    rw [hsplit3]
    -- Each of the 3 triple sums equals T by permuting (a, b, c)!
    let f3 (i j1 j2 : Fin n) : ℤ := ∑ v : Fin n → Bool, orientedEdgeTerm G v i j1 j2
    have hrew : ∀ g : Fin n → Fin n → Fin n → ℤ,
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, g a b c) =
        ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n × Fin n =>
            p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2), g p.1 p.2.1 p.2.2 := by
      intro g
      rw [Finset.sum_filter]
      have h1 : ∀ a : Fin n,
          (∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, g a b c) =
          ∑ b : Fin n, ∑ c : Fin n, if a ≠ b ∧ a ≠ c ∧ b ≠ c then g a b c else 0 := by
        intro a
        have h2 : ∀ b : Fin n,
            (∑ c ∈ (Finset.univ.erase a).erase b, g a b c) =
            ∑ c : Fin n, if c ≠ b ∧ c ≠ a then g a b c else 0 := by
          intro b; rw [← Finset.sum_filter]; congr 1; ext c; simp [Finset.mem_erase]
        simp_rw [h2]
        have h3 : (∑ b ∈ Finset.univ.erase a, ∑ c : Fin n, if c ≠ b ∧ c ≠ a then g a b c else 0) =
            ∑ b : Fin n, if b ≠ a then ∑ c : Fin n, if c ≠ b ∧ c ≠ a then g a b c else 0 else 0 := by
          rw [← Finset.sum_filter]; congr 1; ext b; simp [Finset.mem_erase]
        rw [h3]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hba : b = a
        · subst hba; simp
        · simp only [hba, ne_eq, not_false_eq_true, ↓reduceIte]
          refine Finset.sum_congr rfl fun c _ => ?_
          have hiff : (c ≠ b ∧ c ≠ a) ↔ (a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
            constructor
            · rintro ⟨hcb, hca⟩; exact ⟨Ne.symm hba, hca.symm, hcb.symm⟩
            · rintro ⟨_, hac, hbc⟩; exact ⟨hbc.symm, hac.symm⟩
          by_cases hc : c ≠ b ∧ c ≠ a
          · simp [hc, hiff.mp hc]
          · simp [hc, show ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c) from fun h => hc (hiff.mpr h)]
      simp_rw [h1]
      rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
      exact Fintype.sum_equiv (Equiv.prodAssoc (Fin n) (Fin n) (Fin n)) _ _ (fun _ => rfl)
    have hperm_ab :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 b a c) =
        ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 a b c := by
      rw [hrew (fun a b c => f3 b a c), hrew f3]
      refine Finset.sum_bij (fun p _ => (p.2.1, p.1, p.2.2)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact ⟨hp.1.symm, hp.2.2, hp.2.1⟩
      · intro p1 _ p2 _ h
        rcases p1 with ⟨a1, b1, c1⟩; rcases p2 with ⟨a2, b2, c2⟩; simp_all
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨(q.2.1, q.1, q.2.2), by simp [hq.1.symm, hq.2.1, hq.2.2], rfl⟩
      · intro _ _; rfl
    have hperm_ac :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 c a b) =
        ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 a b c := by
      rw [hrew (fun a b c => f3 c a b), hrew f3]
      refine Finset.sum_bij (fun p _ => (p.2.2, p.1, p.2.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact ⟨hp.2.1.symm, hp.2.2.symm, hp.1⟩
      · intro p1 _ p2 _ h
        rcases p1 with ⟨a1, b1, c1⟩; rcases p2 with ⟨a2, b2, c2⟩; simp_all
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨(q.2.1, q.2.2, q.1), by simp [hq.2.2, hq.1.symm, hq.2.1.symm], rfl⟩
      · intro _ _; rfl
    change 8 * (T + (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 b a c) +
                (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 c a b)) = 24 * T
    rw [hperm_ab, hperm_ac]
    change 8 * (T + T + T) = 24 * T
    ring
  -- Lower bound T via Sum-of-Squares:
  -- For every (v, i), ∑_{j1 ≠ i} ∑_{j2 ≠ i, j1} w(t1) * w(t2) = (∑ w(t))^2 - ∑ w(t)^2 ≥ - (n - 1) * max(w^2)!
  have hT_lb :
      200 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ) -
        145 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n ≤ T := by
    -- Move ∑ v outside (j1, j2)
    have hT_swap :
        T = ∑ v : Fin n → Bool, ∑ i : Fin n,
          ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
            orientedEdgeTerm G v i j1 j2 := by
      dsimp only [T]
      have s1 : ∀ i : Fin n,
          (∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
            ∑ v : Fin n → Bool, orientedEdgeTerm G v i j1 j2) =
          ∑ v : Fin n → Bool, ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
            orientedEdgeTerm G v i j1 j2 := by
        intro i
        have s2 : ∀ j1 ∈ Finset.univ.erase i,
            (∑ j2 ∈ (Finset.univ.erase i).erase j1, ∑ v : Fin n → Bool, orientedEdgeTerm G v i j1 j2) =
            ∑ v : Fin n → Bool, ∑ j2 ∈ (Finset.univ.erase i).erase j1, orientedEdgeTerm G v i j1 j2 :=
          fun _ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl s2]
        exact Finset.sum_comm
      simp_rw [s1]
      exact Finset.sum_comm
    rw [hT_swap]
    -- Elementary SOS identity for any function f : Fin n → ℤ:
    -- ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b = (∑ a ∈ S, f a)^2 - ∑ a ∈ S, (f a)^2 ≥ - ∑ a ∈ S, (f a)^2
    have hsos : ∀ (S : Finset (Fin n)) (f : Fin n → ℤ),
        - ∑ a ∈ S, (f a) ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b := by
      intro S f
      have hid : (∑ a ∈ S, f a) ^ 2 =
          (∑ a ∈ S, (f a) ^ 2) + ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b := by
        rw [sq, Finset.sum_mul]
        have h1 : ∀ a ∈ S, f a * ∑ b ∈ S, f b = (f a) ^ 2 + ∑ b ∈ S.erase a, f a * f b := by
          intro a ha
          rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ ha, sq]
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      have hsq_nonneg : (0 : ℤ) ≤ (∑ a ∈ S, f a) ^ 2 := sq_nonneg _
      linarith
    have hpt_vi : ∀ (v : Fin n → Bool) (i : Fin n),
        (if G.Adj v (flip v i) then 100 * ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) - 145 * ((n : ℤ) - 1) ≤
        ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
          orientedEdgeTerm G v i j1 j2 := by
      intro v i
      set S := Finset.univ.erase i
      have hScard : (S.card : ℤ) = (n : ℤ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
        omega
      by_cases hadj : G.Adj v (flip v i)
      · simp only [hadj, ↓reduceIte, orientedEdgeTerm]
        simp only [Finset.sum_add_distrib]
        have h100 :
            (∑ j1 ∈ S, ∑ _j2 ∈ S.erase j1, (100 : ℤ)) = 100 * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
          have hc : ∀ j1 ∈ S, ((S.erase j1).card : ℤ) = (n : ℤ) - 2 := by
            intro j1 hj1
            rw [Finset.card_erase_of_mem hj1, Finset.card_erase_of_mem (Finset.mem_univ i),
                Finset.card_univ, Fintype.card_fin]; omega
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.sum_congr rfl fun j1 hj1 => by rw [hc j1 hj1], Finset.sum_const, nsmul_eq_mul, hScard]
          ring
        have h0 := hsos S (fun j => sosW0 (edgeFlag G v i j))
        have h1 := hsos S (fun j => sosW1 (edgeFlag G v i j))
        have hdiag : ∑ j ∈ S, (sosW0 (edgeFlag G v i j) ^ 2 + sosW1 (edgeFlag G v i j) ^ 2) ≤
            145 * ((n : ℤ) - 1) := by
          calc ∑ j ∈ S, (sosW0 (edgeFlag G v i j) ^ 2 + sosW1 (edgeFlag G v i j) ^ 2)
              ≤ ∑ _j ∈ S, (145 : ℤ) := Finset.sum_le_sum fun j _ => sosW_sq_le _
            _ = 145 * ((n : ℤ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul, hScard]; ring
        rw [Finset.sum_add_distrib] at hdiag
        rw [h100]; linarith
      · simp only [hadj, ↓reduceIte, orientedEdgeTerm]
        simp only [Finset.sum_add_distrib]
        have h0 := hsos S (fun j => sosU0 (edgeFlag G v i j))
        have h1 := hsos S (fun j => sosU1 (edgeFlag G v i j))
        have hdiag : ∑ j ∈ S, (sosU0 (edgeFlag G v i j) ^ 2 + sosU1 (edgeFlag G v i j) ^ 2) ≤
            145 * ((n : ℤ) - 1) := by
          calc ∑ j ∈ S, (sosU0 (edgeFlag G v i j) ^ 2 + sosU1 (edgeFlag G v i j) ^ 2)
              ≤ ∑ _j ∈ S, (145 : ℤ) := Finset.sum_le_sum fun j _ => sosU_sq_le _
            _ = 145 * ((n : ℤ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul, hScard]; ring
        rw [Finset.sum_add_distrib] at hdiag
        linarith
    have hsum_vi := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
      Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt_vi v i
    refine le_trans ?_ hsum_vi
    simp only [Finset.sum_sub_distrib]
    have hconst :
        (∑ _v : Fin n → Bool, ∑ _i : Fin n, (145 : ℤ) * ((n : ℤ) - 1)) =
        145 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
        Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hedge :
        (∑ v : Fin n → Bool, ∑ i : Fin n,
          if G.Adj v (flip v i) then (100 : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) =
        200 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ) := by
      have hfac : ∀ v : Fin n → Bool,
          (∑ i : Fin n, if G.Adj v (flip v i) then (100 : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) =
          ((Finset.univ.filter (fun i : Fin n => G.Adj v (flip v i))).card : ℤ) *
            (100 * ((n : ℤ) - 1) * ((n : ℤ) - 2)) := by
        intro v
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simp_rw [hfac, ← Finset.sum_mul]
      have h2e := twice_card_edges_eq_sum_oriented G hG
      have h2eZ : (∑ v : Fin n → Bool, ((Finset.univ.filter (fun i : Fin n => G.Adj v (flip v i))).card : ℤ)) =
          2 * (G.edgeFinset.card : ℤ) := by
        exact_mod_cast h2e.symm
      rw [h2eZ]; ring
    rw [hconst, hedge]
  -- Combine `24 * T ≤ 1482 * n*(n-1)*(n-2)*2^n` and `hT_lb`:
  rw [hlhs_eq] at hsum_ub
  have hcomb :
      24 * (200 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ)) ≤
      1482 * ((n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 : ℤ) ^ n) +
        24 * (145 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n) := by
    linarith
  have hfac6 : (6 * ((n : ℤ) - 1)) * (800 * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ)) ≤
      (6 * ((n : ℤ) - 1)) * (247 * (n : ℤ) * ((n : ℤ) - 2) * (2 : ℤ) ^ n + 580 * (n : ℤ) * (2 : ℤ) ^ n) := by
    linarith
  have hpos6 : (0 : ℤ) < 6 * ((n : ℤ) - 1) := by omega
  have hZ : 800 * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ) ≤
      247 * (n : ℤ) * ((n : ℤ) - 2) * (2 : ℤ) ^ n + 580 * (n : ℤ) * (2 : ℤ) ^ n :=
    le_of_mul_le_mul_left hfac6 hpos6
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  rw [← hn2] at hZ
  exact_mod_cast hZ

/-- **Theorem 4.6 (`ppl033_chung_benchmark_lt_five_eighths`):**
Explicit `< 5/8 = 0.625` benchmark: for every `n ≥ 196` and every `C_4`-free `G ≤ Q_n`,
`8 * |E(G)| < 5 * (n * 2 ^ (n - 1))` (pure Mathlib signature). -/
theorem ppl033_chung_benchmark_lt_five_eighths (n : ℕ) (hn : 196 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    8 * G.edgeFinset.card < 5 * (n * 2 ^ (n - 1)) := by
  have hsos := ppl033_flag_sos_upper_exact n (by omega) G hG hfree
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]; ring
  rw [hpow] at hsos
  have hpos : 0 < n * 2 ^ (n - 1) := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
  -- 800*(n-2)*m ≤ (494*(n-2) + 1160) * (n * 2^(n-1)) < 500*(n-2) * (n * 2^(n-1)) since 6*(n-2) > 1160 for n ≥ 196!
  have hlt : 247 * n * (n - 2) * (2 * 2 ^ (n - 1)) + 580 * n * (2 * 2 ^ (n - 1)) <
      500 * (n - 2) * (n * 2 ^ (n - 1)) := by
    have hcoeff : 494 * (n - 2) + 1160 < 500 * (n - 2) := by omega
    calc 247 * n * (n - 2) * (2 * 2 ^ (n - 1)) + 580 * n * (2 * 2 ^ (n - 1))
        = (494 * (n - 2) + 1160) * (n * 2 ^ (n - 1)) := by ring
      _ < 500 * (n - 2) * (n * 2 ^ (n - 1)) := Nat.mul_lt_mul_of_pos_right hcoeff hpos
  have hstrict : 100 * (n - 2) * (8 * G.edgeFinset.card) < 100 * (n - 2) * (5 * (n * 2 ^ (n - 1))) := by
    calc 100 * (n - 2) * (8 * G.edgeFinset.card)
        = 800 * (n - 2) * G.edgeFinset.card := by ring
      _ < 500 * (n - 2) * (n * 2 ^ (n - 1)) := lt_of_le_of_lt hsos hlt
      _ = 100 * (n - 2) * (5 * (n * 2 ^ (n - 1))) := by ring
  exact Nat.lt_of_mul_lt_mul_left hstrict

/-- **Theorem 4.7 (`ppl033_chung_benchmark_le_623`):**
Explicit `≤ 0.623` benchmark (beating Chung 1992's `0.623` / `(2 + √13)/9 ≈ 0.62284`):
for every `n ≥ 266` and every `C_4`-free `G ≤ Q_n`,
`1000 * |E(G)| ≤ 623 * (n * 2 ^ (n - 1))` (pure Mathlib signature). -/
theorem ppl033_chung_benchmark_le_623 (n : ℕ) (hn : 266 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    1000 * G.edgeFinset.card ≤ 623 * (n * 2 ^ (n - 1)) := by
  have hsos := ppl033_flag_sos_upper_exact n (by omega) G hG hfree
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]; ring
  rw [hpow] at hsos
  -- Multiply by 5: 4000*(n-2)*m ≤ (2470*(n-2) + 5800)*(n*2^(n-1)) ≤ 2492*(n-2)*(n*2^(n-1)) since 22*(n-2) ≥ 5800 for n ≥ 266!
  have hcoeff : 2470 * (n - 2) + 5800 ≤ 2492 * (n - 2) := by omega
  have hle : 4 * (n - 2) * (1000 * G.edgeFinset.card) ≤ 4 * (n - 2) * (623 * (n * 2 ^ (n - 1))) := by
    calc 4 * (n - 2) * (1000 * G.edgeFinset.card)
        = 5 * (800 * (n - 2) * G.edgeFinset.card) := by ring
      _ ≤ 5 * (247 * n * (n - 2) * (2 * 2 ^ (n - 1)) + 580 * n * (2 * 2 ^ (n - 1))) :=
          Nat.mul_le_mul_left 5 hsos
      _ = (2470 * (n - 2) + 5800) * (n * 2 ^ (n - 1)) := by ring
      _ ≤ (2492 * (n - 2)) * (n * 2 ^ (n - 1)) := Nat.mul_le_mul_right _ hcoeff
      _ = 4 * (n - 2) * (623 * (n * 2 ^ (n - 1))) := by ring
  exact Nat.le_of_mul_le_mul_left hle (by omega : 0 < 4 * (n - 2))

end UpperBounds

/-! ## Section 5: Turán Density Limit Existence & Local Subcube-Averaging Barrier -/

section LimitAndBarrier

/-- **Theorem 5.1 (`ppl033_turan_density_limit_exists`):**
The hypercube `C_4` Turán density limit `L = lim_{n → ∞} ex(Q_n, C_4) / (n * 2 ^ (n - 1))`
exists and satisfies `1 / 2 ≤ L ≤ 247 / 400 (= 0.6175)` (pure Mathlib signature). -/
theorem ppl033_turan_density_limit_exists :
    open Classical in
    ∃ L : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          ((sSup { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
              G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
                (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
              (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
              G.edgeFinset.card = m } : ℕ) : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ))
        Filter.atTop (nhds L) ∧
      (1 / 2 : ℝ) ≤ L ∧ L ≤ 247 / 400 := by
  classical
  let d : ℕ → ℝ := fun n => (exC4 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ)
  let d1 : ℕ → ℝ := fun k => d (k + 1)
  have hanti : Antitone d1 := by
    intro a b hab
    exact turan_density_antitone_aux (by omega : 1 ≤ a + 1) (by omega : a + 1 ≤ b + 1)
  have hlb : ∀ k : ℕ, (1 / 2 : ℝ) ≤ d1 k := by
    intro k
    dsimp [d1, d]
    have hpos : (0 : ℝ) < (((k + 1) * 2 ^ k : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hpos]
    have hhalf := exC4_ge_half (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hhalf
    linarith
  have hbdd : BddBelow (Set.range d1) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hlb k
  have htend1 : Tendsto d1 atTop (nhds (⨅ k, d1 k)) :=
    tendsto_atTop_ciInf hanti hbdd
  have htend : Tendsto d atTop (nhds (⨅ k, d1 k)) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact htend1
  refine ⟨⨅ k, d1 k, htend, ?_, ?_⟩
  · exact le_ciInf hlb
  · -- Upper bound L ≤ 247/400 from Theorem 4.5 (ppl033_flag_sos_upper_exact)!
    -- Show ∀ ε > 0, L ≤ 247/400 + ε by evaluating d(n) for large n!
    by_contra hgt
    push Not at hgt
    set ε : ℝ := (⨅ k, d1 k) - 247 / 400
    have hε_eq : ε = (⨅ k, d1 k) - 247 / 400 := rfl
    have hε : 0 < ε := sub_pos.mpr hgt
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    let m : ℕ := N + 3
    have hm3 : 3 ≤ m := by omega
    have hL_le : ⨅ k, d1 k ≤ d m := by
      have : d m = d1 (N + 2) := rfl
      rw [this]
      exact ciInf_le hbdd (N + 2)
    obtain ⟨G, hG, hfree, hcard⟩ := exists_exC4_witness m
    have hsos := ppl033_flag_sos_upper_exact m hm3 G hG hfree
    rw [hcard] at hsos
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have he : m = (m - 1) + 1 := by omega
      conv_lhs => rw [he]
      rw [pow_succ]; ring
    rw [hpow] at hsos
    have hdm : d m ≤ 247 / 400 + 29 / (20 * ((m : ℝ) - 2)) := by
      dsimp [d]
      have hposE : (0 : ℝ) < ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by positivity
      have hm2_pos : (0 : ℝ) < (m : ℝ) - 2 := by
        have : (3 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm3
        linarith
      rw [div_le_iff₀ hposE]
      have hsosR : 800 * ((m : ℝ) - 2) * (exC4 m : ℝ) ≤
          (494 * ((m : ℝ) - 2) + 1160) * ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by
        have h1 := Nat.cast_le (α := ℝ).mpr hsos
        have hm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub (by omega)
        push_cast [hm2] at h1 ⊢
        linarith
      have hdiv : (247 / 400 + 29 / (20 * ((m : ℝ) - 2))) * (800 * ((m : ℝ) - 2)) =
          494 * ((m : ℝ) - 2) + 1160 := by
        field_simp [hm2_pos.ne']
        ring
      nlinarith
    have hm2_gt : 29 / (20 * ((m : ℝ) - 2)) < ε := by
      have hm_eq : (m : ℝ) - 2 = (N : ℝ) + 1 := by dsimp [m]; push_cast; ring
      rw [hm_eq]
      have hpos1 : (0 : ℝ) < 20 * ((N : ℝ) + 1) := by positivity
      rw [div_lt_iff₀ hpos1]
      have hNε : 2 < (N : ℝ) * ε := by
        rwa [div_lt_iff₀ hε] at hN
      nlinarith
    linarith

/-- **Theorem 5.2 (`ppl033_local_subcube_averaging_barrier`):**
Local subcube-averaging barrier: for every fixed subcube dimension `k ≥ 1`, pure `Q_k`-subcube
averaging yields at best the upper bound `ex(Q_k, C_4) / |E(Q_k)|`, which is strictly bounded
away from Erdős's conjectured `1/2` by at least `1 / (4 * √k) > 0` (pure Mathlib signature). -/
theorem ppl033_local_subcube_averaging_barrier (k : ℕ) (hk : 1 ≤ k) :
    open Classical in
    (1 / 2 : ℝ) + 1 / (4 * Real.sqrt (k : ℝ)) ≤
      ((sSup { m : ℕ | ∃ G : SimpleGraph (Fin k → Bool),
          G ≤ SimpleGraph.fromRel (fun u v : Fin k → Bool =>
            (Finset.univ.filter (fun i : Fin k => u i ≠ v i)).card = 1) ∧
          (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
          G.edgeFinset.card = m } : ℕ) : ℝ) / ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by
  classical
  change (1 / 2 : ℝ) + 1 / (4 * Real.sqrt (k : ℝ)) ≤ (exC4 k : ℝ) / ((k * 2 ^ (k - 1) : ℕ) : ℝ)
  obtain ⟨G, hG, hfree, hcard⟩ := ppl033_bhn_1995_all_n k hk
  have hle : (G.edgeFinset.card : ℝ) ≤ (exC4 k : ℝ) :=
    Nat.cast_le.mpr (card_le_exC4 G hG hfree)
  have hpos : (0 : ℝ) < ((k * 2 ^ (k - 1) : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hpos]
  linarith

end LimitAndBarrier

end PPL033
