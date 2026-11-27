/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Trees
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# PPL 033 — Unconditional World-Record Upper Bound on `ex(Q_n, C_6)` (Beating Baber 2012)

This file formalizes in pure Mathlib + verified branch-and-bound / flag-algebra Sum-of-Squares
certificates (`RHDirect.PPL033_C6Trees`, zero `sorry`, zero custom axioms, zero `native_decide`):

1. **Exact Finite-`n` Bound (`ppl033_c6_q4_upper_exact`):**
   For every `n ≥ 4` and every `C_6`-free subgraph `G ≤ Q_n`:
   `250000 * (n - 2) * (n - 3) * |E(G)| ≤`
     `(91225 * (n - 2) * (n - 3) + 730366429 * (n - 3) + 1768520 * (4 * n - 6) + 1457021 * (n - 2)) * (n * 2 ^ (n - 1))`.
   Note `91225 / 250000 = 3649 / 10000 = 0.3649`.

2. **Explicit Finite-`n` World Record (`ppl033_c6_beats_baber_2012_explicit`, `ppl033_c6_lt_365_explicit`):**
   - For all `n ≥ 3400000`: `|E(G)| / (n * 2^{n-1}) < 36577 / 100000` (beating Baber 2012's `0.36577`).
   - For all `n ≥ 29600000`: `|E(G)| / (n * 2^{n-1}) < 365 / 1000` (`< 0.365`).

3. **Turán Density Limit Existence & Bound (`ppl033_c6_turan_density_limit_beats_baber`):**
   The limit `L = lim_{n → ∞} ex(Q_n, C_6) / (n * 2^{n-1})` exists and satisfies
   `0 ≤ L ≤ 3649 / 10000 < 365 / 1000 < 36577 / 100000`.
-/

open Filter
open PPL033_C6Cert

/-! ## Section 1: Hypercube `Q_n` Foundations & `C_6` Density Monotonicity -/

section HypercubeFoundations

private def Q (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel
    (fun u v : Fin n → Bool => (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1)

private def IsC6Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ f : Fin 6 → V, Function.Injective f →
    ¬ (G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧
       G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 0))

private noncomputable def exC6 (n : ℕ) : ℕ :=
  open Classical in
  sSup { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
    G ≤ Q n ∧ IsC6Free G ∧ G.edgeFinset.card = m }

private def qFlip {n : ℕ} (u : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update u i (!u i)

private lemma qFlip_apply_self {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    qFlip u i i = !u i := by simp [qFlip]

private lemma qFlip_apply_ne {n : ℕ} (u : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    qFlip u i j = u j := by simp [qFlip, h]

private lemma qFlip_flip {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    qFlip (qFlip u i) i = u := by
  ext j; by_cases h : j = i
  · subst h; simp [qFlip]
  · simp [qFlip, h]

private lemma qFlip_ne_self {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    qFlip u i ≠ u := by
  intro h; have h1 := congrFun h i; simp [qFlip] at h1

private lemma qFlip_comm {n : ℕ} (u : Fin n → Bool) (i j : Fin n) :
    qFlip (qFlip u i) j = qFlip (qFlip u j) i := by
  ext k; by_cases h1 : k = j <;> by_cases h2 : k = i
  · subst h1; subst h2; simp [qFlip]
  · subst h1; simp [qFlip, h2]
  · subst h2; simp [qFlip, h1]
  · simp [qFlip, h1, h2]

private lemma qFlip_inj {n : ℕ} (u : Fin n → Bool) {i j : Fin n}
    (h : qFlip u i = qFlip u j) : i = j := by
  by_contra hne
  have h1 := congrFun h i
  rw [qFlip_apply_self, qFlip_apply_ne u (i := j) (j := i) hne] at h1
  exact Bool.not_ne_self (u i) h1

private lemma filter_ne_qFlip {n : ℕ} (u : Fin n → Bool) (i : Fin n) :
    Finset.univ.filter (fun k : Fin n => u k ≠ qFlip u i k) = {i} := by
  ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases hk : k = i
  · subst hk; simp [qFlip]
  · simp [qFlip, hk]

private lemma Q_adj_iff {n : ℕ} (u v : Fin n → Bool) :
    (Q n).Adj u v ↔ (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1 := by
  simp only [Q, SimpleGraph.fromRel_adj]
  constructor
  · intro ⟨hne, h⟩; rcases h with h | h
    · exact h
    · convert h using 2; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_comm]
  · intro h; refine ⟨?_, Or.inl h⟩; intro heq; subst heq; simp at h

private lemma Q_adj_iff_exists_qFlip {n : ℕ} {u v : Fin n → Bool} :
    (Q n).Adj u v ↔ ∃ i : Fin n, qFlip u i = v := by
  rw [Q_adj_iff]
  constructor
  · intro h; rw [Finset.card_eq_one] at h; rcases h with ⟨i, hi⟩; refine ⟨i, ?_⟩
    ext j; by_cases hj : j = i
    · subst hj
      have hm : j ∈ Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by rw [hi]; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [qFlip_apply_self]; cases h1 : u j <;> cases h2 : v j <;> simp_all
    · have hm : j ∉ Finset.univ.filter (fun k : Fin n => u k ≠ v k) := by rw [hi]; simp [hj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hm
      rw [qFlip_apply_ne u hj, hm]
  · rintro ⟨i, rfl⟩; rw [filter_ne_qFlip, Finset.card_singleton]

private lemma edgeFinset_card_congr {V : Type*} (G : SimpleGraph V)
    (inst1 inst2 : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G inst1).card = (@SimpleGraph.edgeFinset _ G inst2).card := by
  congr 1; ext e; simp [SimpleGraph.mem_edgeFinset]

private lemma Q_edgeFinset_card (n : ℕ) :
    open Classical in (Q n).edgeFinset.card = n * 2 ^ (n - 1) := by
  classical
  by_cases hn : n = 0
  · subst hn
    have he : (Q 0).edgeSet = ∅ := by
      ext e; induction e using Sym2.ind with | _ u v =>
      simp only [SimpleGraph.mem_edgeSet, Q_adj_iff, Finset.univ_eq_empty,
        Finset.filter_empty, Finset.card_empty, zero_ne_one, Set.mem_empty_iff_false]
    simp [SimpleGraph.edgeFinset, he]
  · have hdeg : ∀ u : Fin n → Bool, (Q n).degree u = n := by
      intro u; rw [SimpleGraph.degree]
      conv_rhs => rw [← Finset.card_fin n]
      refine Finset.card_bij (fun v hv => Classical.choose (Q_adj_iff_exists_qFlip.mp
        ((SimpleGraph.mem_neighborFinset _ _ _).mp hv))) ?_ ?_ ?_
      · intro _ _; simp
      · intro v1 hv1 v2 hv2 heq
        have h1 := Classical.choose_spec (Q_adj_iff_exists_qFlip.mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hv1))
        have h2 := Classical.choose_spec (Q_adj_iff_exists_qFlip.mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hv2))
        rw [← h1, ← h2, heq]
      · intro i _
        refine ⟨qFlip u i, (SimpleGraph.mem_neighborFinset _ _ _).mpr
          (Q_adj_iff_exists_qFlip.mpr ⟨i, rfl⟩), ?_⟩
        exact qFlip_inj u (Classical.choose_spec (Q_adj_iff_exists_qFlip.mp
          (Q_adj_iff_exists_qFlip.mpr ⟨i, rfl⟩)))
    have hsum := (Q n).sum_degrees_eq_twice_card_edges
    simp_rw [hdeg] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, smul_eq_mul] at hsum
    have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), pow_succ']
    rw [hpow] at hsum
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (by linarith)

private lemma exC6_bddAbove (n : ℕ) :
    open Classical in
    BddAbove { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ Q n ∧ IsC6Free G ∧ G.edgeFinset.card = m } := by
  classical
  refine ⟨n * 2 ^ (n - 1), ?_⟩
  rintro m ⟨G, hG, _, rfl⟩
  calc G.edgeFinset.card
      ≤ (Q n).edgeFinset.card := Finset.card_le_card (SimpleGraph.edgeFinset_mono hG)
    _ = n * 2 ^ (n - 1) := Q_edgeFinset_card n

private lemma exC6_nonempty (n : ℕ) :
    open Classical in
    { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
      G ≤ Q n ∧ IsC6Free G ∧ G.edgeFinset.card = m }.Nonempty := by
  classical
  refine ⟨0, ⊥, bot_le, fun _ _ h => h.1, ?_⟩
  simp

private lemma card_le_exC6 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ Q n) (hfree : IsC6Free G) :
    G.edgeFinset.card ≤ exC6 n := by
  classical
  rw [edgeFinset_card_congr G _ _]
  exact le_csSup (exC6_bddAbove n) ⟨G, hG, hfree, rfl⟩

private lemma exists_exC6_witness (n : ℕ) :
    open Classical in
    ∃ G : SimpleGraph (Fin n → Bool), G ≤ Q n ∧ IsC6Free G ∧ G.edgeFinset.card = exC6 n := by
  classical
  exact Nat.sSup_mem (exC6_nonempty n) (exC6_bddAbove n)

private lemma twice_card_edges_eq_sum_oriented {n : ℕ} (G : SimpleGraph (Fin n → Bool))
    [Fintype G.edgeSet] (hG : G ≤ Q n) :
    open Classical in
    2 * G.edgeFinset.card =
      ∑ u : Fin n → Bool, (Finset.univ.filter (fun j : Fin n => G.Adj u (qFlip u j))).card := by
  classical
  rw [edgeFinset_card_congr G _ (SimpleGraph.fintypeEdgeSet G)]
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [SimpleGraph.degree]
  symm
  refine Finset.card_bij (fun j _ => qFlip u j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simpa [SimpleGraph.mem_neighborFinset] using hj
  · intro j1 _ j2 _ h; exact qFlip_inj u h
  · intro v hv
    simp only [SimpleGraph.mem_neighborFinset] at hv
    obtain ⟨j, rfl⟩ := Q_adj_iff_exists_qFlip.mp (hG hv)
    exact ⟨j, by simpa using hv, rfl⟩

private def subcubeEmbed {n : ℕ} (i : Fin (n + 1)) (b : Bool) :
    (Fin n → Bool) ↪ (Fin (n + 1) → Bool) where
  toFun u := i.insertNth b u
  inj' u v h := by
    ext j
    have h1 := congrFun h (i.succAbove j)
    simpa [Fin.insertNth_apply_succAbove] using h1

private lemma subcubeEmbed_apply {n : ℕ} (i : Fin (n + 1)) (b : Bool) (u : Fin n → Bool) :
    subcubeEmbed i b u = i.insertNth b u := rfl

private lemma subcubeEmbed_qFlip {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (u : Fin n → Bool) (j : Fin n) :
    subcubeEmbed i b (qFlip u j) = qFlip (subcubeEmbed i b u) (i.succAbove j) := by
  ext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [subcubeEmbed_apply, qFlip, (Fin.succAbove_ne i j).symm]
  · intro m
    by_cases hm : m = j
    · subst hm; simp [subcubeEmbed_apply, qFlip]
    · have hne : i.succAbove m ≠ i.succAbove j := fun h => hm (Fin.succAbove_right_injective h)
      simp [subcubeEmbed_apply, qFlip, hm, hne]

private lemma comap_subcubeEmbed_le_Q {n : ℕ} {G : SimpleGraph (Fin (n + 1) → Bool)}
    (hG : G ≤ Q (n + 1)) (i : Fin (n + 1)) (b : Bool) :
    G.comap (subcubeEmbed i b) ≤ Q n := by
  intro u v huv
  have hq : (Q (n + 1)).Adj (subcubeEmbed i b u) (subcubeEmbed i b v) := hG huv
  obtain ⟨k, hk⟩ := Q_adj_iff_exists_qFlip.mp hq
  have hki : k ≠ i := by
    intro h
    have h1 := congrFun hk i
    rw [h] at h1
    simp [subcubeEmbed_apply, qFlip] at h1
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hki
  rw [Q_adj_iff_exists_qFlip]
  refine ⟨j, (subcubeEmbed i b).injective ?_⟩
  rw [subcubeEmbed_qFlip, hk]

private lemma comap_subcubeEmbed_isC6Free {n : ℕ} {G : SimpleGraph (Fin (n + 1) → Bool)}
    (hfree : IsC6Free G) (i : Fin (n + 1)) (b : Bool) :
    IsC6Free (G.comap (subcubeEmbed i b)) := by
  intro f hf ⟨h0, h1, h2, h3, h4, h5⟩
  exact hfree (subcubeEmbed i b ∘ f) ((subcubeEmbed i b).injective.comp hf)
    ⟨h0, h1, h2, h3, h4, h5⟩

private lemma subcube_averaging_graph {n : ℕ} (G : SimpleGraph (Fin (n + 1) → Bool))
    [Fintype G.edgeSet] (hG : G ≤ Q (n + 1)) (hfree : IsC6Free G) :
    n * G.edgeFinset.card ≤ 2 * (n + 1) * exC6 n := by
  classical
  have hway1 :
      ∑ i : Fin (n + 1), ∑ b : Bool,
        2 * (G.comap (subcubeEmbed i b)).edgeFinset.card =
      n * (2 * G.edgeFinset.card) := by
    have hsub : ∀ (i : Fin (n + 1)) (b : Bool),
        2 * (G.comap (subcubeEmbed i b)).edgeFinset.card =
        ∑ u : Fin n → Bool,
          (Finset.univ.filter (fun j : Fin n =>
            G.Adj (subcubeEmbed i b u) (qFlip (subcubeEmbed i b u) (i.succAbove j)))).card := by
      intro i b
      rw [twice_card_edges_eq_sum_oriented _ (comap_subcubeEmbed_le_Q hG i b)]
      refine Finset.sum_congr rfl fun u _ => ?_
      congr 1; ext j; simp [SimpleGraph.comap_adj, subcubeEmbed_qFlip]
    simp_rw [hsub]
    have hfib : ∀ i : Fin (n + 1),
        ∑ b : Bool, ∑ u : Fin n → Bool,
          (Finset.univ.filter (fun j : Fin n =>
            G.Adj (subcubeEmbed i b u) (qFlip (subcubeEmbed i b u) (i.succAbove j)))).card =
        ∑ v : Fin (n + 1) → Bool,
          (Finset.univ.filter (fun j : Fin n => G.Adj v (qFlip v (i.succAbove j)))).card := by
      intro i
      rw [← Fintype.sum_prod_type']
      refine Fintype.sum_equiv
        { toFun := fun p => subcubeEmbed i p.1 p.2
          invFun := fun v => (v i, fun j => v (i.succAbove j))
          left_inv := fun ⟨b, u⟩ => by ext <;> simp [subcubeEmbed_apply]
          right_inv := fun v => by
            ext k
            refine Fin.succAboveCases i ?_ ?_ k
            · simp [subcubeEmbed_apply]
            · intro m; simp [subcubeEmbed_apply] } _ _ (fun _ => rfl)
    simp_rw [hfib]
    rw [Finset.sum_comm, twice_card_edges_eq_sum_oriented G hG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hinner : ∀ i : Fin (n + 1),
        (Finset.univ.filter (fun j : Fin n => G.Adj v (qFlip v (i.succAbove j)))).card =
        (Finset.univ.filter (fun k : Fin (n + 1) => k ≠ i ∧ G.Adj v (qFlip v k))).card := by
      intro i
      refine Finset.card_bij (fun j _ => i.succAbove j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨Fin.succAbove_ne i j, hj⟩
      · intro j1 _ j2 _ h; exact Fin.succAbove_right_injective h
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk.1
        exact ⟨j, by simpa using hk.2, rfl⟩
    simp_rw [hinner, Finset.card_filter]
    rw [Finset.sum_comm]
    have hpoint : ∀ k : Fin (n + 1),
        (∑ i : Fin (n + 1), if k ≠ i ∧ G.Adj v (qFlip v k) then 1 else 0) =
        n * (if G.Adj v (qFlip v k) then 1 else 0) := by
      intro k
      by_cases hadj : G.Adj v (qFlip v k)
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
      ∑ _i : Fin (n + 1), ∑ _b : Bool, 2 * exC6 n := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => ?_
    exact Nat.mul_le_mul_left 2
      (card_le_exC6 _ (comap_subcubeEmbed_le_Q hG i b) (comap_subcubeEmbed_isC6Free hfree i b))
  rw [hway1] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin,
    smul_eq_mul] at hle
  linarith

private lemma turan_density_step (n : ℕ) (hn : 1 ≤ n) :
    ((exC6 (n + 1) : ℝ) / (((n + 1) * 2 ^ n : ℕ) : ℝ)) ≤
      ((exC6 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ)) := by
  classical
  have hstep : n * exC6 (n + 1) ≤ 2 * (n + 1) * exC6 n := by
    obtain ⟨G, hG, hfree, hcard⟩ := exists_exC6_witness (n + 1)
    rw [← hcard]
    exact subcube_averaging_graph G hG hfree
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ k => simp [pow_succ, mul_comm]
  have hpos1 : (0 : ℝ) < (((n + 1) * 2 ^ n : ℕ) : ℝ) := by positivity
  have hpos2 : (0 : ℝ) < ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hpos1 hpos2]
  have hcast : ((n * exC6 (n + 1) : ℕ) : ℝ) ≤ ((2 * (n + 1) * exC6 n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hstep
  push_cast at hcast ⊢
  rw [hpow]
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := by positivity
  nlinarith

private lemma turan_density_antitone_aux {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((exC6 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ)) ≤
      ((exC6 m : ℝ) / ((m * 2 ^ (m - 1) : ℕ) : ℝ)) := by
  induction hmn with
  | refl => exact le_rfl
  | @step k hmk ih =>
    have hk : 1 ≤ k := le_trans hm hmk
    have h1 := turan_density_step k hk
    simpa [Nat.add_sub_cancel] using le_trans h1 ih

end HypercubeFoundations

/-! ## Section 2: Compositional `Aut(Q_4)` Invariance & `q4_bound_all` -/

section AutQ4Invariance

-- Q4 edge endpoints
private def edgeEndpointsQ4 (e : Fin 32) : Fin 16 × Fin 16 :=
  match e.val with
  | 0 => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | 1 => (⟨0, by decide⟩, ⟨2, by decide⟩)
  | 2 => (⟨0, by decide⟩, ⟨4, by decide⟩)
  | 3 => (⟨0, by decide⟩, ⟨8, by decide⟩)
  | 4 => (⟨1, by decide⟩, ⟨3, by decide⟩)
  | 5 => (⟨1, by decide⟩, ⟨5, by decide⟩)
  | 6 => (⟨1, by decide⟩, ⟨9, by decide⟩)
  | 7 => (⟨2, by decide⟩, ⟨3, by decide⟩)
  | 8 => (⟨2, by decide⟩, ⟨6, by decide⟩)
  | 9 => (⟨2, by decide⟩, ⟨10, by decide⟩)
  | 10 => (⟨3, by decide⟩, ⟨7, by decide⟩)
  | 11 => (⟨3, by decide⟩, ⟨11, by decide⟩)
  | 12 => (⟨4, by decide⟩, ⟨5, by decide⟩)
  | 13 => (⟨4, by decide⟩, ⟨6, by decide⟩)
  | 14 => (⟨4, by decide⟩, ⟨12, by decide⟩)
  | 15 => (⟨5, by decide⟩, ⟨7, by decide⟩)
  | 16 => (⟨5, by decide⟩, ⟨13, by decide⟩)
  | 17 => (⟨6, by decide⟩, ⟨7, by decide⟩)
  | 18 => (⟨6, by decide⟩, ⟨14, by decide⟩)
  | 19 => (⟨7, by decide⟩, ⟨15, by decide⟩)
  | 20 => (⟨8, by decide⟩, ⟨9, by decide⟩)
  | 21 => (⟨8, by decide⟩, ⟨10, by decide⟩)
  | 22 => (⟨8, by decide⟩, ⟨12, by decide⟩)
  | 23 => (⟨9, by decide⟩, ⟨11, by decide⟩)
  | 24 => (⟨9, by decide⟩, ⟨13, by decide⟩)
  | 25 => (⟨10, by decide⟩, ⟨11, by decide⟩)
  | 26 => (⟨10, by decide⟩, ⟨14, by decide⟩)
  | 27 => (⟨11, by decide⟩, ⟨15, by decide⟩)
  | 28 => (⟨12, by decide⟩, ⟨13, by decide⟩)
  | 29 => (⟨12, by decide⟩, ⟨14, by decide⟩)
  | 30 => (⟨13, by decide⟩, ⟨15, by decide⟩)
  | _ => (⟨14, by decide⟩, ⟨15, by decide⟩)

-- C6 cycle vertices in Q4
private def c6CycleVertsQ4 (cid : Fin 128) (j : Fin 6) : Fin 16 :=
  match cid.val, j.val with
  | 0, 0 => ⟨0, by decide⟩ | 0, 1 => ⟨4, by decide⟩ | 0, 2 => ⟨5, by decide⟩ | 0, 3 => ⟨13, by decide⟩ | 0, 4 => ⟨12, by decide⟩ | 0, _ => ⟨8, by decide⟩
  | 1, 0 => ⟨0, by decide⟩ | 1, 1 => ⟨1, by decide⟩ | 1, 2 => ⟨3, by decide⟩ | 1, 3 => ⟨7, by decide⟩ | 1, 4 => ⟨6, by decide⟩ | 1, _ => ⟨2, by decide⟩
  | 2, 0 => ⟨2, by decide⟩ | 2, 1 => ⟨3, by decide⟩ | 2, 2 => ⟨7, by decide⟩ | 2, 3 => ⟨15, by decide⟩ | 2, 4 => ⟨14, by decide⟩ | 2, _ => ⟨10, by decide⟩
  | 3, 0 => ⟨8, by decide⟩ | 3, 1 => ⟨9, by decide⟩ | 3, 2 => ⟨13, by decide⟩ | 3, 3 => ⟨15, by decide⟩ | 3, 4 => ⟨11, by decide⟩ | 3, _ => ⟨10, by decide⟩
  | 4, 0 => ⟨5, by decide⟩ | 4, 1 => ⟨7, by decide⟩ | 4, 2 => ⟨15, by decide⟩ | 4, 3 => ⟨14, by decide⟩ | 4, 4 => ⟨12, by decide⟩ | 4, _ => ⟨13, by decide⟩
  | 5, 0 => ⟨5, by decide⟩ | 5, 1 => ⟨7, by decide⟩ | 5, 2 => ⟨6, by decide⟩ | 5, 3 => ⟨14, by decide⟩ | 5, 4 => ⟨15, by decide⟩ | 5, _ => ⟨13, by decide⟩
  | 6, 0 => ⟨8, by decide⟩ | 6, 1 => ⟨10, by decide⟩ | 6, 2 => ⟨11, by decide⟩ | 6, 3 => ⟨15, by decide⟩ | 6, 4 => ⟨13, by decide⟩ | 6, _ => ⟨12, by decide⟩
  | 7, 0 => ⟨0, by decide⟩ | 7, 1 => ⟨1, by decide⟩ | 7, 2 => ⟨3, by decide⟩ | 7, 3 => ⟨11, by decide⟩ | 7, 4 => ⟨10, by decide⟩ | 7, _ => ⟨8, by decide⟩
  | 8, 0 => ⟨1, by decide⟩ | 8, 1 => ⟨5, by decide⟩ | 8, 2 => ⟨7, by decide⟩ | 8, 3 => ⟨15, by decide⟩ | 8, 4 => ⟨11, by decide⟩ | 8, _ => ⟨9, by decide⟩
  | 9, 0 => ⟨0, by decide⟩ | 9, 1 => ⟨4, by decide⟩ | 9, 2 => ⟨6, by decide⟩ | 9, 3 => ⟨14, by decide⟩ | 9, 4 => ⟨12, by decide⟩ | 9, _ => ⟨8, by decide⟩
  | 10, 0 => ⟨8, by decide⟩ | 10, 1 => ⟨9, by decide⟩ | 10, 2 => ⟨11, by decide⟩ | 10, 3 => ⟨15, by decide⟩ | 10, 4 => ⟨14, by decide⟩ | 10, _ => ⟨12, by decide⟩
  | 11, 0 => ⟨0, by decide⟩ | 11, 1 => ⟨1, by decide⟩ | 11, 2 => ⟨9, by decide⟩ | 11, 3 => ⟨11, by decide⟩ | 11, 4 => ⟨10, by decide⟩ | 11, _ => ⟨2, by decide⟩
  | 12, 0 => ⟨0, by decide⟩ | 12, 1 => ⟨2, by decide⟩ | 12, 2 => ⟨3, by decide⟩ | 12, 3 => ⟨1, by decide⟩ | 12, 4 => ⟨9, by decide⟩ | 12, _ => ⟨8, by decide⟩
  | 13, 0 => ⟨1, by decide⟩ | 13, 1 => ⟨3, by decide⟩ | 13, 2 => ⟨11, by decide⟩ | 13, 3 => ⟨15, by decide⟩ | 13, 4 => ⟨7, by decide⟩ | 13, _ => ⟨5, by decide⟩
  | 14, 0 => ⟨9, by decide⟩ | 14, 1 => ⟨11, by decide⟩ | 14, 2 => ⟨15, by decide⟩ | 14, 3 => ⟨14, by decide⟩ | 14, 4 => ⟨12, by decide⟩ | 14, _ => ⟨13, by decide⟩
  | 15, 0 => ⟨1, by decide⟩ | 15, 1 => ⟨3, by decide⟩ | 15, 2 => ⟨7, by decide⟩ | 15, 3 => ⟨5, by decide⟩ | 15, 4 => ⟨13, by decide⟩ | 15, _ => ⟨9, by decide⟩
  | 16, 0 => ⟨0, by decide⟩ | 16, 1 => ⟨4, by decide⟩ | 16, 2 => ⟨12, by decide⟩ | 16, 3 => ⟨14, by decide⟩ | 16, 4 => ⟨10, by decide⟩ | 16, _ => ⟨8, by decide⟩
  | 17, 0 => ⟨1, by decide⟩ | 17, 1 => ⟨3, by decide⟩ | 17, 2 => ⟨11, by decide⟩ | 17, 3 => ⟨15, by decide⟩ | 17, 4 => ⟨13, by decide⟩ | 17, _ => ⟨9, by decide⟩
  | 18, 0 => ⟨4, by decide⟩ | 18, 1 => ⟨6, by decide⟩ | 18, 2 => ⟨7, by decide⟩ | 18, 3 => ⟨15, by decide⟩ | 18, 4 => ⟨14, by decide⟩ | 18, _ => ⟨12, by decide⟩
  | 19, 0 => ⟨0, by decide⟩ | 19, 1 => ⟨4, by decide⟩ | 19, 2 => ⟨6, by decide⟩ | 19, 3 => ⟨14, by decide⟩ | 19, 4 => ⟨10, by decide⟩ | 19, _ => ⟨8, by decide⟩
  | 20, 0 => ⟨2, by decide⟩ | 20, 1 => ⟨6, by decide⟩ | 20, 2 => ⟨7, by decide⟩ | 20, 3 => ⟨15, by decide⟩ | 20, 4 => ⟨11, by decide⟩ | 20, _ => ⟨10, by decide⟩
  | 21, 0 => ⟨8, by decide⟩ | 21, 1 => ⟨9, by decide⟩ | 21, 2 => ⟨11, by decide⟩ | 21, 3 => ⟨15, by decide⟩ | 21, 4 => ⟨14, by decide⟩ | 21, _ => ⟨10, by decide⟩
  | 22, 0 => ⟨2, by decide⟩ | 22, 1 => ⟨3, by decide⟩ | 22, 2 => ⟨11, by decide⟩ | 22, 3 => ⟨10, by decide⟩ | 22, 4 => ⟨14, by decide⟩ | 22, _ => ⟨6, by decide⟩
  | 23, 0 => ⟨6, by decide⟩ | 23, 1 => ⟨7, by decide⟩ | 23, 2 => ⟨15, by decide⟩ | 23, 3 => ⟨11, by decide⟩ | 23, 4 => ⟨10, by decide⟩ | 23, _ => ⟨14, by decide⟩
  | 24, 0 => ⟨10, by decide⟩ | 24, 1 => ⟨11, by decide⟩ | 24, 2 => ⟨15, by decide⟩ | 24, 3 => ⟨13, by decide⟩ | 24, 4 => ⟨12, by decide⟩ | 24, _ => ⟨14, by decide⟩
  | 25, 0 => ⟨1, by decide⟩ | 25, 1 => ⟨3, by decide⟩ | 25, 2 => ⟨11, by decide⟩ | 25, 3 => ⟨10, by decide⟩ | 25, 4 => ⟨8, by decide⟩ | 25, _ => ⟨9, by decide⟩
  | 26, 0 => ⟨4, by decide⟩ | 26, 1 => ⟨5, by decide⟩ | 26, 2 => ⟨13, by decide⟩ | 26, 3 => ⟨15, by decide⟩ | 26, 4 => ⟨14, by decide⟩ | 26, _ => ⟨6, by decide⟩
  | 27, 0 => ⟨0, by decide⟩ | 27, 1 => ⟨2, by decide⟩ | 27, 2 => ⟨6, by decide⟩ | 27, 3 => ⟨14, by decide⟩ | 27, 4 => ⟨12, by decide⟩ | 27, _ => ⟨4, by decide⟩
  | 28, 0 => ⟨0, by decide⟩ | 28, 1 => ⟨2, by decide⟩ | 28, 2 => ⟨6, by decide⟩ | 28, 3 => ⟨14, by decide⟩ | 28, 4 => ⟨12, by decide⟩ | 28, _ => ⟨8, by decide⟩
  | 29, 0 => ⟨2, by decide⟩ | 29, 1 => ⟨3, by decide⟩ | 29, 2 => ⟨11, by decide⟩ | 29, 3 => ⟨15, by decide⟩ | 29, 4 => ⟨14, by decide⟩ | 29, _ => ⟨6, by decide⟩
  | 30, 0 => ⟨8, by decide⟩ | 30, 1 => ⟨9, by decide⟩ | 30, 2 => ⟨11, by decide⟩ | 30, 3 => ⟨10, by decide⟩ | 30, 4 => ⟨14, by decide⟩ | 30, _ => ⟨12, by decide⟩
  | 31, 0 => ⟨0, by decide⟩ | 31, 1 => ⟨4, by decide⟩ | 31, 2 => ⟨5, by decide⟩ | 31, 3 => ⟨13, by decide⟩ | 31, 4 => ⟨9, by decide⟩ | 31, _ => ⟨8, by decide⟩
  | 32, 0 => ⟨9, by decide⟩ | 32, 1 => ⟨11, by decide⟩ | 32, 2 => ⟨10, by decide⟩ | 32, 3 => ⟨14, by decide⟩ | 32, 4 => ⟨12, by decide⟩ | 32, _ => ⟨13, by decide⟩
  | 33, 0 => ⟨4, by decide⟩ | 33, 1 => ⟨6, by decide⟩ | 33, 2 => ⟨7, by decide⟩ | 33, 3 => ⟨15, by decide⟩ | 33, 4 => ⟨13, by decide⟩ | 33, _ => ⟨12, by decide⟩
  | 34, 0 => ⟨8, by decide⟩ | 34, 1 => ⟨9, by decide⟩ | 34, 2 => ⟨13, by decide⟩ | 34, 3 => ⟨15, by decide⟩ | 34, 4 => ⟨14, by decide⟩ | 34, _ => ⟨10, by decide⟩
  | 35, 0 => ⟨2, by decide⟩ | 35, 1 => ⟨3, by decide⟩ | 35, 2 => ⟨7, by decide⟩ | 35, 3 => ⟨15, by decide⟩ | 35, 4 => ⟨11, by decide⟩ | 35, _ => ⟨10, by decide⟩
  | 36, 0 => ⟨1, by decide⟩ | 36, 1 => ⟨5, by decide⟩ | 36, 2 => ⟨4, by decide⟩ | 36, 3 => ⟨12, by decide⟩ | 36, 4 => ⟨8, by decide⟩ | 36, _ => ⟨9, by decide⟩
  | 37, 0 => ⟨3, by decide⟩ | 37, 1 => ⟨7, by decide⟩ | 37, 2 => ⟨6, by decide⟩ | 37, 3 => ⟨14, by decide⟩ | 37, 4 => ⟨10, by decide⟩ | 37, _ => ⟨11, by decide⟩
  | 38, 0 => ⟨2, by decide⟩ | 38, 1 => ⟨3, by decide⟩ | 38, 2 => ⟨7, by decide⟩ | 38, 3 => ⟨15, by decide⟩ | 38, 4 => ⟨14, by decide⟩ | 38, _ => ⟨6, by decide⟩
  | 39, 0 => ⟨4, by decide⟩ | 39, 1 => ⟨5, by decide⟩ | 39, 2 => ⟨7, by decide⟩ | 39, 3 => ⟨15, by decide⟩ | 39, 4 => ⟨14, by decide⟩ | 39, _ => ⟨6, by decide⟩
  | 40, 0 => ⟨8, by decide⟩ | 40, 1 => ⟨10, by decide⟩ | 40, 2 => ⟨14, by decide⟩ | 40, 3 => ⟨15, by decide⟩ | 40, 4 => ⟨13, by decide⟩ | 40, _ => ⟨12, by decide⟩
  | 41, 0 => ⟨2, by decide⟩ | 41, 1 => ⟨3, by decide⟩ | 41, 2 => ⟨11, by decide⟩ | 41, 3 => ⟨15, by decide⟩ | 41, 4 => ⟨14, by decide⟩ | 41, _ => ⟨10, by decide⟩
  | 42, 0 => ⟨4, by decide⟩ | 42, 1 => ⟨5, by decide⟩ | 42, 2 => ⟨7, by decide⟩ | 42, 3 => ⟨6, by decide⟩ | 42, 4 => ⟨14, by decide⟩ | 42, _ => ⟨12, by decide⟩
  | 43, 0 => ⟨1, by decide⟩ | 43, 1 => ⟨5, by decide⟩ | 43, 2 => ⟨7, by decide⟩ | 43, 3 => ⟨15, by decide⟩ | 43, 4 => ⟨13, by decide⟩ | 43, _ => ⟨9, by decide⟩
  | 44, 0 => ⟨9, by decide⟩ | 44, 1 => ⟨11, by decide⟩ | 44, 2 => ⟨10, by decide⟩ | 44, 3 => ⟨14, by decide⟩ | 44, 4 => ⟨15, by decide⟩ | 44, _ => ⟨13, by decide⟩
  | 45, 0 => ⟨0, by decide⟩ | 45, 1 => ⟨4, by decide⟩ | 45, 2 => ⟨6, by decide⟩ | 45, 3 => ⟨2, by decide⟩ | 45, 4 => ⟨10, by decide⟩ | 45, _ => ⟨8, by decide⟩
  | 46, 0 => ⟨2, by decide⟩ | 46, 1 => ⟨6, by decide⟩ | 46, 2 => ⟨14, by decide⟩ | 46, 3 => ⟨12, by decide⟩ | 46, 4 => ⟨8, by decide⟩ | 46, _ => ⟨10, by decide⟩
  | 47, 0 => ⟨2, by decide⟩ | 47, 1 => ⟨6, by decide⟩ | 47, 2 => ⟨7, by decide⟩ | 47, 3 => ⟨15, by decide⟩ | 47, 4 => ⟨14, by decide⟩ | 47, _ => ⟨10, by decide⟩
  | 48, 0 => ⟨0, by decide⟩ | 48, 1 => ⟨2, by decide⟩ | 48, 2 => ⟨10, by decide⟩ | 48, 3 => ⟨11, by decide⟩ | 48, 4 => ⟨9, by decide⟩ | 48, _ => ⟨8, by decide⟩
  | 49, 0 => ⟨4, by decide⟩ | 49, 1 => ⟨5, by decide⟩ | 49, 2 => ⟨13, by decide⟩ | 49, 3 => ⟨15, by decide⟩ | 49, 4 => ⟨14, by decide⟩ | 49, _ => ⟨12, by decide⟩
  | 50, 0 => ⟨1, by decide⟩ | 50, 1 => ⟨3, by decide⟩ | 50, 2 => ⟨11, by decide⟩ | 50, 3 => ⟨9, by decide⟩ | 50, 4 => ⟨13, by decide⟩ | 50, _ => ⟨5, by decide⟩
  | 51, 0 => ⟨2, by decide⟩ | 51, 1 => ⟨6, by decide⟩ | 51, 2 => ⟨4, by decide⟩ | 51, 3 => ⟨12, by decide⟩ | 51, 4 => ⟨14, by decide⟩ | 51, _ => ⟨10, by decide⟩
  | 52, 0 => ⟨0, by decide⟩ | 52, 1 => ⟨2, by decide⟩ | 52, 2 => ⟨3, by decide⟩ | 52, 3 => ⟨1, by decide⟩ | 52, 4 => ⟨5, by decide⟩ | 52, _ => ⟨4, by decide⟩
  | 53, 0 => ⟨0, by decide⟩ | 53, 1 => ⟨4, by decide⟩ | 53, 2 => ⟨12, by decide⟩ | 53, 3 => ⟨13, by decide⟩ | 53, 4 => ⟨9, by decide⟩ | 53, _ => ⟨8, by decide⟩
  | 54, 0 => ⟨1, by decide⟩ | 54, 1 => ⟨5, by decide⟩ | 54, 2 => ⟨4, by decide⟩ | 54, 3 => ⟨12, by decide⟩ | 54, 4 => ⟨13, by decide⟩ | 54, _ => ⟨9, by decide⟩
  | 55, 0 => ⟨0, by decide⟩ | 55, 1 => ⟨1, by decide⟩ | 55, 2 => ⟨5, by decide⟩ | 55, 3 => ⟨4, by decide⟩ | 55, 4 => ⟨6, by decide⟩ | 55, _ => ⟨2, by decide⟩
  | 56, 0 => ⟨0, by decide⟩ | 56, 1 => ⟨1, by decide⟩ | 56, 2 => ⟨5, by decide⟩ | 56, 3 => ⟨7, by decide⟩ | 56, 4 => ⟨3, by decide⟩ | 56, _ => ⟨2, by decide⟩
  | 57, 0 => ⟨0, by decide⟩ | 57, 1 => ⟨1, by decide⟩ | 57, 2 => ⟨5, by decide⟩ | 57, 3 => ⟨7, by decide⟩ | 57, 4 => ⟨6, by decide⟩ | 57, _ => ⟨2, by decide⟩
  | 58, 0 => ⟨8, by decide⟩ | 58, 1 => ⟨9, by decide⟩ | 58, 2 => ⟨13, by decide⟩ | 58, 3 => ⟨15, by decide⟩ | 58, 4 => ⟨14, by decide⟩ | 58, _ => ⟨12, by decide⟩
  | 59, 0 => ⟨4, by decide⟩ | 59, 1 => ⟨5, by decide⟩ | 59, 2 => ⟨7, by decide⟩ | 59, 3 => ⟨15, by decide⟩ | 59, 4 => ⟨13, by decide⟩ | 59, _ => ⟨12, by decide⟩
  | 60, 0 => ⟨3, by decide⟩ | 60, 1 => ⟨7, by decide⟩ | 60, 2 => ⟨15, by decide⟩ | 60, 3 => ⟨14, by decide⟩ | 60, 4 => ⟨10, by decide⟩ | 60, _ => ⟨11, by decide⟩
  | 61, 0 => ⟨0, by decide⟩ | 61, 1 => ⟨1, by decide⟩ | 61, 2 => ⟨3, by decide⟩ | 61, 3 => ⟨7, by decide⟩ | 61, 4 => ⟨6, by decide⟩ | 61, _ => ⟨4, by decide⟩
  | 62, 0 => ⟨0, by decide⟩ | 62, 1 => ⟨1, by decide⟩ | 62, 2 => ⟨9, by decide⟩ | 62, 3 => ⟨13, by decide⟩ | 62, 4 => ⟨5, by decide⟩ | 62, _ => ⟨4, by decide⟩
  | 63, 0 => ⟨8, by decide⟩ | 63, 1 => ⟨9, by decide⟩ | 63, 2 => ⟨13, by decide⟩ | 63, 3 => ⟨12, by decide⟩ | 63, 4 => ⟨14, by decide⟩ | 63, _ => ⟨10, by decide⟩
  | 64, 0 => ⟨0, by decide⟩ | 64, 1 => ⟨1, by decide⟩ | 64, 2 => ⟨9, by decide⟩ | 64, 3 => ⟨13, by decide⟩ | 64, 4 => ⟨12, by decide⟩ | 64, _ => ⟨4, by decide⟩
  | 65, 0 => ⟨0, by decide⟩ | 65, 1 => ⟨1, by decide⟩ | 65, 2 => ⟨9, by decide⟩ | 65, 3 => ⟨11, by decide⟩ | 65, 4 => ⟨3, by decide⟩ | 65, _ => ⟨2, by decide⟩
  | 66, 0 => ⟨0, by decide⟩ | 66, 1 => ⟨2, by decide⟩ | 66, 2 => ⟨3, by decide⟩ | 66, 3 => ⟨7, by decide⟩ | 66, 4 => ⟨5, by decide⟩ | 66, _ => ⟨4, by decide⟩
  | 67, 0 => ⟨8, by decide⟩ | 67, 1 => ⟨10, by decide⟩ | 67, 2 => ⟨11, by decide⟩ | 67, 3 => ⟨9, by decide⟩ | 67, 4 => ⟨13, by decide⟩ | 67, _ => ⟨12, by decide⟩
  | 68, 0 => ⟨0, by decide⟩ | 68, 1 => ⟨2, by decide⟩ | 68, 2 => ⟨6, by decide⟩ | 68, 3 => ⟨4, by decide⟩ | 68, 4 => ⟨12, by decide⟩ | 68, _ => ⟨8, by decide⟩
  | 69, 0 => ⟨0, by decide⟩ | 69, 1 => ⟨1, by decide⟩ | 69, 2 => ⟨9, by decide⟩ | 69, 3 => ⟨13, by decide⟩ | 69, 4 => ⟨12, by decide⟩ | 69, _ => ⟨8, by decide⟩
  | 70, 0 => ⟨0, by decide⟩ | 70, 1 => ⟨1, by decide⟩ | 70, 2 => ⟨3, by decide⟩ | 70, 3 => ⟨2, by decide⟩ | 70, 4 => ⟨10, by decide⟩ | 70, _ => ⟨8, by decide⟩
  | 71, 0 => ⟨0, by decide⟩ | 71, 1 => ⟨1, by decide⟩ | 71, 2 => ⟨9, by decide⟩ | 71, 3 => ⟨8, by decide⟩ | 71, 4 => ⟨12, by decide⟩ | 71, _ => ⟨4, by decide⟩
  | 72, 0 => ⟨1, by decide⟩ | 72, 1 => ⟨3, by decide⟩ | 72, 2 => ⟨2, by decide⟩ | 72, 3 => ⟨6, by decide⟩ | 72, 4 => ⟨7, by decide⟩ | 72, _ => ⟨5, by decide⟩
  | 73, 0 => ⟨0, by decide⟩ | 73, 1 => ⟨2, by decide⟩ | 73, 2 => ⟨6, by decide⟩ | 73, 3 => ⟨14, by decide⟩ | 73, 4 => ⟨10, by decide⟩ | 73, _ => ⟨8, by decide⟩
  | 74, 0 => ⟨1, by decide⟩ | 74, 1 => ⟨3, by decide⟩ | 74, 2 => ⟨7, by decide⟩ | 74, 3 => ⟨6, by decide⟩ | 74, 4 => ⟨4, by decide⟩ | 74, _ => ⟨5, by decide⟩
  | 75, 0 => ⟨3, by decide⟩ | 75, 1 => ⟨7, by decide⟩ | 75, 2 => ⟨15, by decide⟩ | 75, 3 => ⟨13, by decide⟩ | 75, 4 => ⟨9, by decide⟩ | 75, _ => ⟨11, by decide⟩
  | 76, 0 => ⟨2, by decide⟩ | 76, 1 => ⟨3, by decide⟩ | 76, 2 => ⟨11, by decide⟩ | 76, 3 => ⟨15, by decide⟩ | 76, 4 => ⟨7, by decide⟩ | 76, _ => ⟨6, by decide⟩
  | 77, 0 => ⟨2, by decide⟩ | 77, 1 => ⟨6, by decide⟩ | 77, 2 => ⟨7, by decide⟩ | 77, 3 => ⟨3, by decide⟩ | 77, 4 => ⟨11, by decide⟩ | 77, _ => ⟨10, by decide⟩
  | 78, 0 => ⟨4, by decide⟩ | 78, 1 => ⟨5, by decide⟩ | 78, 2 => ⟨13, by decide⟩ | 78, 3 => ⟨15, by decide⟩ | 78, 4 => ⟨7, by decide⟩ | 78, _ => ⟨6, by decide⟩
  | 79, 0 => ⟨4, by decide⟩ | 79, 1 => ⟨5, by decide⟩ | 79, 2 => ⟨13, by decide⟩ | 79, 3 => ⟨12, by decide⟩ | 79, 4 => ⟨14, by decide⟩ | 79, _ => ⟨6, by decide⟩
  | 80, 0 => ⟨1, by decide⟩ | 80, 1 => ⟨3, by decide⟩ | 80, 2 => ⟨7, by decide⟩ | 80, 3 => ⟨15, by decide⟩ | 80, 4 => ⟨13, by decide⟩ | 80, _ => ⟨9, by decide⟩
  | 81, 0 => ⟨4, by decide⟩ | 81, 1 => ⟨5, by decide⟩ | 81, 2 => ⟨13, by decide⟩ | 81, 3 => ⟨9, by decide⟩ | 81, 4 => ⟨8, by decide⟩ | 81, _ => ⟨12, by decide⟩
  | 82, 0 => ⟨3, by decide⟩ | 82, 1 => ⟨7, by decide⟩ | 82, 2 => ⟨5, by decide⟩ | 82, 3 => ⟨13, by decide⟩ | 82, 4 => ⟨15, by decide⟩ | 82, _ => ⟨11, by decide⟩
  | 83, 0 => ⟨0, by decide⟩ | 83, 1 => ⟨1, by decide⟩ | 83, 2 => ⟨3, by decide⟩ | 83, 3 => ⟨2, by decide⟩ | 83, 4 => ⟨6, by decide⟩ | 83, _ => ⟨4, by decide⟩
  | 84, 0 => ⟨0, by decide⟩ | 84, 1 => ⟨1, by decide⟩ | 84, 2 => ⟨3, by decide⟩ | 84, 3 => ⟨7, by decide⟩ | 84, 4 => ⟨5, by decide⟩ | 84, _ => ⟨4, by decide⟩
  | 85, 0 => ⟨0, by decide⟩ | 85, 1 => ⟨2, by decide⟩ | 85, 2 => ⟨3, by decide⟩ | 85, 3 => ⟨11, by decide⟩ | 85, 4 => ⟨9, by decide⟩ | 85, _ => ⟨8, by decide⟩
  | 86, 0 => ⟨2, by decide⟩ | 86, 1 => ⟨6, by decide⟩ | 86, 2 => ⟨14, by decide⟩ | 86, 3 => ⟨15, by decide⟩ | 86, 4 => ⟨11, by decide⟩ | 86, _ => ⟨10, by decide⟩
  | 87, 0 => ⟨2, by decide⟩ | 87, 1 => ⟨3, by decide⟩ | 87, 2 => ⟨7, by decide⟩ | 87, 3 => ⟨5, by decide⟩ | 87, 4 => ⟨4, by decide⟩ | 87, _ => ⟨6, by decide⟩
  | 88, 0 => ⟨6, by decide⟩ | 88, 1 => ⟨7, by decide⟩ | 88, 2 => ⟨15, by decide⟩ | 88, 3 => ⟨13, by decide⟩ | 88, 4 => ⟨12, by decide⟩ | 88, _ => ⟨14, by decide⟩
  | 89, 0 => ⟨0, by decide⟩ | 89, 1 => ⟨2, by decide⟩ | 89, 2 => ⟨10, by decide⟩ | 89, 3 => ⟨14, by decide⟩ | 89, 4 => ⟨12, by decide⟩ | 89, _ => ⟨8, by decide⟩
  | 90, 0 => ⟨4, by decide⟩ | 90, 1 => ⟨6, by decide⟩ | 90, 2 => ⟨14, by decide⟩ | 90, 3 => ⟨10, by decide⟩ | 90, 4 => ⟨8, by decide⟩ | 90, _ => ⟨12, by decide⟩
  | 91, 0 => ⟨0, by decide⟩ | 91, 1 => ⟨1, by decide⟩ | 91, 2 => ⟨3, by decide⟩ | 91, 3 => ⟨11, by decide⟩ | 91, 4 => ⟨9, by decide⟩ | 91, _ => ⟨8, by decide⟩
  | 92, 0 => ⟨0, by decide⟩ | 92, 1 => ⟨1, by decide⟩ | 92, 2 => ⟨5, by decide⟩ | 92, 3 => ⟨4, by decide⟩ | 92, 4 => ⟨12, by decide⟩ | 92, _ => ⟨8, by decide⟩
  | 93, 0 => ⟨2, by decide⟩ | 93, 1 => ⟨6, by decide⟩ | 93, 2 => ⟨4, by decide⟩ | 93, 3 => ⟨12, by decide⟩ | 93, 4 => ⟨8, by decide⟩ | 93, _ => ⟨10, by decide⟩
  | 94, 0 => ⟨8, by decide⟩ | 94, 1 => ⟨10, by decide⟩ | 94, 2 => ⟨11, by decide⟩ | 94, 3 => ⟨15, by decide⟩ | 94, 4 => ⟨14, by decide⟩ | 94, _ => ⟨12, by decide⟩
  | 95, 0 => ⟨1, by decide⟩ | 95, 1 => ⟨5, by decide⟩ | 95, 2 => ⟨7, by decide⟩ | 95, 3 => ⟨3, by decide⟩ | 95, 4 => ⟨11, by decide⟩ | 95, _ => ⟨9, by decide⟩
  | 96, 0 => ⟨5, by decide⟩ | 96, 1 => ⟨7, by decide⟩ | 96, 2 => ⟨6, by decide⟩ | 96, 3 => ⟨14, by decide⟩ | 96, 4 => ⟨12, by decide⟩ | 96, _ => ⟨13, by decide⟩
  | 97, 0 => ⟨1, by decide⟩ | 97, 1 => ⟨5, by decide⟩ | 97, 2 => ⟨13, by decide⟩ | 97, 3 => ⟨15, by decide⟩ | 97, 4 => ⟨11, by decide⟩ | 97, _ => ⟨9, by decide⟩
  | 98, 0 => ⟨2, by decide⟩ | 98, 1 => ⟨3, by decide⟩ | 98, 2 => ⟨7, by decide⟩ | 98, 3 => ⟨6, by decide⟩ | 98, 4 => ⟨14, by decide⟩ | 98, _ => ⟨10, by decide⟩
  | 99, 0 => ⟨3, by decide⟩ | 99, 1 => ⟨7, by decide⟩ | 99, 2 => ⟨6, by decide⟩ | 99, 3 => ⟨14, by decide⟩ | 99, 4 => ⟨15, by decide⟩ | 99, _ => ⟨11, by decide⟩
  | 100, 0 => ⟨1, by decide⟩ | 100, 1 => ⟨5, by decide⟩ | 100, 2 => ⟨13, by decide⟩ | 100, 3 => ⟨12, by decide⟩ | 100, 4 => ⟨8, by decide⟩ | 100, _ => ⟨9, by decide⟩
  | 101, 0 => ⟨5, by decide⟩ | 101, 1 => ⟨7, by decide⟩ | 101, 2 => ⟨15, by decide⟩ | 101, 3 => ⟨11, by decide⟩ | 101, 4 => ⟨9, by decide⟩ | 101, _ => ⟨13, by decide⟩
  | 102, 0 => ⟨0, by decide⟩ | 102, 1 => ⟨2, by decide⟩ | 102, 2 => ⟨3, by decide⟩ | 102, 3 => ⟨7, by decide⟩ | 102, 4 => ⟨6, by decide⟩ | 102, _ => ⟨4, by decide⟩
  | 103, 0 => ⟨0, by decide⟩ | 103, 1 => ⟨2, by decide⟩ | 103, 2 => ⟨6, by decide⟩ | 103, 3 => ⟨7, by decide⟩ | 103, 4 => ⟨5, by decide⟩ | 103, _ => ⟨4, by decide⟩
  | 104, 0 => ⟨0, by decide⟩ | 104, 1 => ⟨1, by decide⟩ | 104, 2 => ⟨5, by decide⟩ | 104, 3 => ⟨7, by decide⟩ | 104, 4 => ⟨6, by decide⟩ | 104, _ => ⟨4, by decide⟩
  | 105, 0 => ⟨0, by decide⟩ | 105, 1 => ⟨4, by decide⟩ | 105, 2 => ⟨5, by decide⟩ | 105, 3 => ⟨1, by decide⟩ | 105, 4 => ⟨9, by decide⟩ | 105, _ => ⟨8, by decide⟩
  | 106, 0 => ⟨4, by decide⟩ | 106, 1 => ⟨5, by decide⟩ | 106, 2 => ⟨7, by decide⟩ | 106, 3 => ⟨15, by decide⟩ | 106, 4 => ⟨14, by decide⟩ | 106, _ => ⟨12, by decide⟩
  | 107, 0 => ⟨2, by decide⟩ | 107, 1 => ⟨3, by decide⟩ | 107, 2 => ⟨11, by decide⟩ | 107, 3 => ⟨9, by decide⟩ | 107, 4 => ⟨8, by decide⟩ | 107, _ => ⟨10, by decide⟩
  | 108, 0 => ⟨0, by decide⟩ | 108, 1 => ⟨1, by decide⟩ | 108, 2 => ⟨3, by decide⟩ | 108, 3 => ⟨11, by decide⟩ | 108, 4 => ⟨10, by decide⟩ | 108, _ => ⟨2, by decide⟩
  | 109, 0 => ⟨1, by decide⟩ | 109, 1 => ⟨3, by decide⟩ | 109, 2 => ⟨7, by decide⟩ | 109, 3 => ⟨15, by decide⟩ | 109, 4 => ⟨13, by decide⟩ | 109, _ => ⟨5, by decide⟩
  | 110, 0 => ⟨0, by decide⟩ | 110, 1 => ⟨2, by decide⟩ | 110, 2 => ⟨10, by decide⟩ | 110, 3 => ⟨8, by decide⟩ | 110, 4 => ⟨12, by decide⟩ | 110, _ => ⟨4, by decide⟩
  | 111, 0 => ⟨0, by decide⟩ | 111, 1 => ⟨1, by decide⟩ | 111, 2 => ⟨9, by decide⟩ | 111, 3 => ⟨11, by decide⟩ | 111, 4 => ⟨10, by decide⟩ | 111, _ => ⟨8, by decide⟩
  | 112, 0 => ⟨1, by decide⟩ | 112, 1 => ⟨3, by decide⟩ | 112, 2 => ⟨2, by decide⟩ | 112, 3 => ⟨10, by decide⟩ | 112, 4 => ⟨8, by decide⟩ | 112, _ => ⟨9, by decide⟩
  | 113, 0 => ⟨0, by decide⟩ | 113, 1 => ⟨1, by decide⟩ | 113, 2 => ⟨5, by decide⟩ | 113, 3 => ⟨13, by decide⟩ | 113, 4 => ⟨9, by decide⟩ | 113, _ => ⟨8, by decide⟩
  | 114, 0 => ⟨0, by decide⟩ | 114, 1 => ⟨2, by decide⟩ | 114, 2 => ⟨10, by decide⟩ | 114, 3 => ⟨14, by decide⟩ | 114, 4 => ⟨12, by decide⟩ | 114, _ => ⟨4, by decide⟩
  | 115, 0 => ⟨4, by decide⟩ | 115, 1 => ⟨6, by decide⟩ | 115, 2 => ⟨14, by decide⟩ | 115, 3 => ⟨15, by decide⟩ | 115, 4 => ⟨13, by decide⟩ | 115, _ => ⟨12, by decide⟩
  | 116, 0 => ⟨0, by decide⟩ | 116, 1 => ⟨1, by decide⟩ | 116, 2 => ⟨5, by decide⟩ | 116, 3 => ⟨13, by decide⟩ | 116, 4 => ⟨12, by decide⟩ | 116, _ => ⟨4, by decide⟩
  | 117, 0 => ⟨3, by decide⟩ | 117, 1 => ⟨7, by decide⟩ | 117, 2 => ⟨5, by decide⟩ | 117, 3 => ⟨13, by decide⟩ | 117, 4 => ⟨9, by decide⟩ | 117, _ => ⟨11, by decide⟩
  | 118, 0 => ⟨0, by decide⟩ | 118, 1 => ⟨1, by decide⟩ | 118, 2 => ⟨5, by decide⟩ | 118, 3 => ⟨13, by decide⟩ | 118, 4 => ⟨12, by decide⟩ | 118, _ => ⟨8, by decide⟩
  | 119, 0 => ⟨8, by decide⟩ | 119, 1 => ⟨9, by decide⟩ | 119, 2 => ⟨11, by decide⟩ | 119, 3 => ⟨15, by decide⟩ | 119, 4 => ⟨13, by decide⟩ | 119, _ => ⟨12, by decide⟩
  | 120, 0 => ⟨0, by decide⟩ | 120, 1 => ⟨2, by decide⟩ | 120, 2 => ⟨10, by decide⟩ | 120, 3 => ⟨14, by decide⟩ | 120, 4 => ⟨6, by decide⟩ | 120, _ => ⟨4, by decide⟩
  | 121, 0 => ⟨1, by decide⟩ | 121, 1 => ⟨3, by decide⟩ | 121, 2 => ⟨11, by decide⟩ | 121, 3 => ⟨15, by decide⟩ | 121, 4 => ⟨13, by decide⟩ | 121, _ => ⟨5, by decide⟩
  | 122, 0 => ⟨1, by decide⟩ | 122, 1 => ⟨3, by decide⟩ | 122, 2 => ⟨7, by decide⟩ | 122, 3 => ⟨15, by decide⟩ | 122, 4 => ⟨11, by decide⟩ | 122, _ => ⟨9, by decide⟩
  | 123, 0 => ⟨0, by decide⟩ | 123, 1 => ⟨2, by decide⟩ | 123, 2 => ⟨3, by decide⟩ | 123, 3 => ⟨11, by decide⟩ | 123, 4 => ⟨10, by decide⟩ | 123, _ => ⟨8, by decide⟩
  | 124, 0 => ⟨1, by decide⟩ | 124, 1 => ⟨3, by decide⟩ | 124, 2 => ⟨2, by decide⟩ | 124, 3 => ⟨6, by decide⟩ | 124, 4 => ⟨4, by decide⟩ | 124, _ => ⟨5, by decide⟩
  | 125, 0 => ⟨0, by decide⟩ | 125, 1 => ⟨1, by decide⟩ | 125, 2 => ⟨9, by decide⟩ | 125, 3 => ⟨8, by decide⟩ | 125, 4 => ⟨10, by decide⟩ | 125, _ => ⟨2, by decide⟩
  | 126, 0 => ⟨4, by decide⟩ | 126, 1 => ⟨6, by decide⟩ | 126, 2 => ⟨7, by decide⟩ | 126, 3 => ⟨5, by decide⟩ | 126, 4 => ⟨13, by decide⟩ | 126, _ => ⟨12, by decide⟩
  | _, 0 => ⟨1, by decide⟩ | _, 1 => ⟨3, by decide⟩ | _, 2 => ⟨2, by decide⟩ | _, 3 => ⟨10, by decide⟩ | _, 4 => ⟨11, by decide⟩ | _, _ => ⟨9, by decide⟩

private def q4Flip0 (g : Q4Bits) : Q4Bits := { q00 := g.q00, q01 := g.q04, q02 := g.q05, q03 := g.q06, q04 := g.q01, q05 := g.q02, q06 := g.q03, q07 := g.q07, q08 := g.q10, q09 := g.q11, q10 := g.q08, q11 := g.q09, q12 := g.q12, q13 := g.q15, q14 := g.q16, q15 := g.q13, q16 := g.q14, q17 := g.q17, q18 := g.q19, q19 := g.q18, q20 := g.q20, q21 := g.q23, q22 := g.q24, q23 := g.q21, q24 := g.q22, q25 := g.q25, q26 := g.q27, q27 := g.q26, q28 := g.q28, q29 := g.q30, q30 := g.q29, q31 := g.q31 }
private def q4Swap01 (g : Q4Bits) : Q4Bits := { q00 := g.q01, q01 := g.q00, q02 := g.q02, q03 := g.q03, q04 := g.q07, q05 := g.q08, q06 := g.q09, q07 := g.q04, q08 := g.q05, q09 := g.q06, q10 := g.q10, q11 := g.q11, q12 := g.q13, q13 := g.q12, q14 := g.q14, q15 := g.q17, q16 := g.q18, q17 := g.q15, q18 := g.q16, q19 := g.q19, q20 := g.q21, q21 := g.q20, q22 := g.q22, q23 := g.q25, q24 := g.q26, q25 := g.q23, q26 := g.q24, q27 := g.q27, q28 := g.q29, q29 := g.q28, q30 := g.q31, q31 := g.q30 }
private def q4Swap12 (g : Q4Bits) : Q4Bits := { q00 := g.q00, q01 := g.q02, q02 := g.q01, q03 := g.q03, q04 := g.q05, q05 := g.q04, q06 := g.q06, q07 := g.q12, q08 := g.q13, q09 := g.q14, q10 := g.q15, q11 := g.q16, q12 := g.q07, q13 := g.q08, q14 := g.q09, q15 := g.q10, q16 := g.q11, q17 := g.q17, q18 := g.q18, q19 := g.q19, q20 := g.q20, q21 := g.q22, q22 := g.q21, q23 := g.q24, q24 := g.q23, q25 := g.q28, q26 := g.q29, q27 := g.q30, q28 := g.q25, q29 := g.q26, q30 := g.q27, q31 := g.q31 }
private def q4Swap23 (g : Q4Bits) : Q4Bits := { q00 := g.q00, q01 := g.q01, q02 := g.q03, q03 := g.q02, q04 := g.q04, q05 := g.q06, q06 := g.q05, q07 := g.q07, q08 := g.q09, q09 := g.q08, q10 := g.q11, q11 := g.q10, q12 := g.q20, q13 := g.q21, q14 := g.q22, q15 := g.q23, q16 := g.q24, q17 := g.q25, q18 := g.q26, q19 := g.q27, q20 := g.q12, q21 := g.q13, q22 := g.q14, q23 := g.q15, q24 := g.q16, q25 := g.q17, q26 := g.q18, q27 := g.q19, q28 := g.q28, q29 := g.q29, q30 := g.q30, q31 := g.q31 }

private def c6Perm_flip0 (cid : Fin 128) : Fin 128 :=
  match cid.val with
  | 0 => ⟨54, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨29, by decide⟩ | 3 => ⟨30, by decide⟩ | 4 => ⟨115, by decide⟩ | 5 => ⟨18, by decide⟩ | 6 => ⟨32, by decide⟩ | 7 => ⟨11, by decide⟩
  | 8 => ⟨19, by decide⟩ | 9 => ⟨43, by decide⟩ | 10 => ⟨34, by decide⟩ | 11 => ⟨7, by decide⟩ | 12 => ⟨12, by decide⟩ | 13 => ⟨120, by decide⟩ | 14 => ⟨40, by decide⟩ | 15 => ⟨68, by decide⟩
  | 16 => ⟨97, by decide⟩ | 17 => ⟨89, by decide⟩ | 18 => ⟨5, by decide⟩ | 19 => ⟨8, by decide⟩ | 20 => ⟨37, by decide⟩ | 21 => ⟨21, by decide⟩ | 22 => ⟨35, by decide⟩ | 23 => ⟨23, by decide⟩
  | 24 => ⟨24, by decide⟩ | 25 => ⟨48, by decide⟩ | 26 => ⟨106, by decide⟩ | 27 => ⟨109, by decide⟩ | 28 => ⟨80, by decide⟩ | 29 => ⟨2, by decide⟩ | 30 => ⟨3, by decide⟩ | 31 => ⟨36, by decide⟩
  | 32 => ⟨6, by decide⟩ | 33 => ⟨96, by decide⟩ | 34 => ⟨10, by decide⟩ | 35 => ⟨22, by decide⟩ | 36 => ⟨31, by decide⟩ | 37 => ⟨20, by decide⟩ | 38 => ⟨38, by decide⟩ | 39 => ⟨39, by decide⟩
  | 40 => ⟨14, by decide⟩ | 41 => ⟨41, by decide⟩ | 42 => ⟨78, by decide⟩ | 43 => ⟨9, by decide⟩ | 44 => ⟨94, by decide⟩ | 45 => ⟨95, by decide⟩ | 46 => ⟨75, by decide⟩ | 47 => ⟨99, by decide⟩
  | 48 => ⟨25, by decide⟩ | 49 => ⟨49, by decide⟩ | 50 => ⟨110, by decide⟩ | 51 => ⟨82, by decide⟩ | 52 => ⟨52, by decide⟩ | 53 => ⟨100, by decide⟩ | 54 => ⟨0, by decide⟩ | 55 => ⟨84, by decide⟩
  | 56 => ⟨83, by decide⟩ | 57 => ⟨61, by decide⟩ | 58 => ⟨58, by decide⟩ | 59 => ⟨79, by decide⟩ | 60 => ⟨86, by decide⟩ | 61 => ⟨57, by decide⟩ | 62 => ⟨92, by decide⟩ | 63 => ⟨119, by decide⟩
  | 64 => ⟨118, by decide⟩ | 65 => ⟨70, by decide⟩ | 66 => ⟨124, by decide⟩ | 67 => ⟨67, by decide⟩ | 68 => ⟨15, by decide⟩ | 69 => ⟨69, by decide⟩ | 70 => ⟨65, by decide⟩ | 71 => ⟨113, by decide⟩
  | 72 => ⟨102, by decide⟩ | 73 => ⟨122, by decide⟩ | 74 => ⟨103, by decide⟩ | 75 => ⟨46, by decide⟩ | 76 => ⟨98, by decide⟩ | 77 => ⟨77, by decide⟩ | 78 => ⟨42, by decide⟩ | 79 => ⟨59, by decide⟩
  | 80 => ⟨28, by decide⟩ | 81 => ⟨81, by decide⟩ | 82 => ⟨51, by decide⟩ | 83 => ⟨56, by decide⟩ | 84 => ⟨55, by decide⟩ | 85 => ⟨112, by decide⟩ | 86 => ⟨60, by decide⟩ | 87 => ⟨87, by decide⟩
  | 88 => ⟨88, by decide⟩ | 89 => ⟨17, by decide⟩ | 90 => ⟨101, by decide⟩ | 91 => ⟨125, by decide⟩ | 92 => ⟨62, by decide⟩ | 93 => ⟨117, by decide⟩ | 94 => ⟨44, by decide⟩ | 95 => ⟨45, by decide⟩
  | 96 => ⟨33, by decide⟩ | 97 => ⟨16, by decide⟩ | 98 => ⟨76, by decide⟩ | 99 => ⟨47, by decide⟩ | 100 => ⟨53, by decide⟩ | 101 => ⟨90, by decide⟩ | 102 => ⟨72, by decide⟩ | 103 => ⟨74, by decide⟩
  | 104 => ⟨104, by decide⟩ | 105 => ⟨105, by decide⟩ | 106 => ⟨26, by decide⟩ | 107 => ⟨107, by decide⟩ | 108 => ⟨108, by decide⟩ | 109 => ⟨27, by decide⟩ | 110 => ⟨50, by decide⟩ | 111 => ⟨111, by decide⟩
  | 112 => ⟨85, by decide⟩ | 113 => ⟨71, by decide⟩ | 114 => ⟨121, by decide⟩ | 115 => ⟨4, by decide⟩ | 116 => ⟨116, by decide⟩ | 117 => ⟨93, by decide⟩ | 118 => ⟨64, by decide⟩ | 119 => ⟨63, by decide⟩
  | 120 => ⟨13, by decide⟩ | 121 => ⟨114, by decide⟩ | 122 => ⟨73, by decide⟩ | 123 => ⟨127, by decide⟩ | 124 => ⟨66, by decide⟩ | 125 => ⟨91, by decide⟩ | 126 => ⟨126, by decide⟩ | _ => ⟨123, by decide⟩
private def c6Perm_swap01 (cid : Fin 128) : Fin 128 :=
  match cid.val with
  | 0 => ⟨9, by decide⟩ | 1 => ⟨56, by decide⟩ | 2 => ⟨80, by decide⟩ | 3 => ⟨21, by decide⟩ | 4 => ⟨88, by decide⟩ | 5 => ⟨5, by decide⟩ | 6 => ⟨10, by decide⟩ | 7 => ⟨85, by decide⟩
  | 8 => ⟨20, by decide⟩ | 9 => ⟨0, by decide⟩ | 10 => ⟨6, by decide⟩ | 11 => ⟨11, by decide⟩ | 12 => ⟨70, by decide⟩ | 13 => ⟨76, by decide⟩ | 14 => ⟨24, by decide⟩ | 15 => ⟨98, by decide⟩
  | 16 => ⟨53, by decide⟩ | 17 => ⟨41, by decide⟩ | 18 => ⟨59, by decide⟩ | 19 => ⟨31, by decide⟩ | 20 => ⟨8, by decide⟩ | 21 => ⟨3, by decide⟩ | 22 => ⟨50, by decide⟩ | 23 => ⟨101, by decide⟩
  | 24 => ⟨14, by decide⟩ | 25 => ⟨107, by decide⟩ | 26 => ⟨26, by decide⟩ | 27 => ⟨116, by decide⟩ | 28 => ⟨118, by decide⟩ | 29 => ⟨121, by decide⟩ | 30 => ⟨67, by decide⟩ | 31 => ⟨19, by decide⟩
  | 32 => ⟨32, by decide⟩ | 33 => ⟨106, by decide⟩ | 34 => ⟨34, by decide⟩ | 35 => ⟨122, by decide⟩ | 36 => ⟨93, by decide⟩ | 37 => ⟨117, by decide⟩ | 38 => ⟨109, by decide⟩ | 39 => ⟨78, by decide⟩
  | 40 => ⟨58, by decide⟩ | 41 => ⟨17, by decide⟩ | 42 => ⟨126, by decide⟩ | 43 => ⟨47, by decide⟩ | 44 => ⟨44, by decide⟩ | 45 => ⟨105, by decide⟩ | 46 => ⟨100, by decide⟩ | 47 => ⟨43, by decide⟩
  | 48 => ⟨111, by decide⟩ | 49 => ⟨115, by decide⟩ | 50 => ⟨22, by decide⟩ | 51 => ⟨54, by decide⟩ | 52 => ⟨83, by decide⟩ | 53 => ⟨16, by decide⟩ | 54 => ⟨51, by decide⟩ | 55 => ⟨55, by decide⟩
  | 56 => ⟨1, by decide⟩ | 57 => ⟨57, by decide⟩ | 58 => ⟨40, by decide⟩ | 59 => ⟨18, by decide⟩ | 60 => ⟨75, by decide⟩ | 61 => ⟨66, by decide⟩ | 62 => ⟨120, by decide⟩ | 63 => ⟨63, by decide⟩
  | 64 => ⟨114, by decide⟩ | 65 => ⟨108, by decide⟩ | 66 => ⟨61, by decide⟩ | 67 => ⟨30, by decide⟩ | 68 => ⟨92, by decide⟩ | 69 => ⟨89, by decide⟩ | 70 => ⟨12, by decide⟩ | 71 => ⟨110, by decide⟩
  | 72 => ⟨72, by decide⟩ | 73 => ⟨113, by decide⟩ | 74 => ⟨87, by decide⟩ | 75 => ⟨60, by decide⟩ | 76 => ⟨13, by decide⟩ | 77 => ⟨95, by decide⟩ | 78 => ⟨39, by decide⟩ | 79 => ⟨79, by decide⟩
  | 80 => ⟨2, by decide⟩ | 81 => ⟨90, by decide⟩ | 82 => ⟨99, by decide⟩ | 83 => ⟨52, by decide⟩ | 84 => ⟨102, by decide⟩ | 85 => ⟨7, by decide⟩ | 86 => ⟨97, by decide⟩ | 87 => ⟨74, by decide⟩
  | 88 => ⟨4, by decide⟩ | 89 => ⟨69, by decide⟩ | 90 => ⟨81, by decide⟩ | 91 => ⟨123, by decide⟩ | 92 => ⟨68, by decide⟩ | 93 => ⟨36, by decide⟩ | 94 => ⟨119, by decide⟩ | 95 => ⟨77, by decide⟩
  | 96 => ⟨96, by decide⟩ | 97 => ⟨86, by decide⟩ | 98 => ⟨15, by decide⟩ | 99 => ⟨82, by decide⟩ | 100 => ⟨46, by decide⟩ | 101 => ⟨23, by decide⟩ | 102 => ⟨84, by decide⟩ | 103 => ⟨104, by decide⟩
  | 104 => ⟨103, by decide⟩ | 105 => ⟨45, by decide⟩ | 106 => ⟨33, by decide⟩ | 107 => ⟨25, by decide⟩ | 108 => ⟨65, by decide⟩ | 109 => ⟨38, by decide⟩ | 110 => ⟨71, by decide⟩ | 111 => ⟨48, by decide⟩
  | 112 => ⟨112, by decide⟩ | 113 => ⟨73, by decide⟩ | 114 => ⟨64, by decide⟩ | 115 => ⟨49, by decide⟩ | 116 => ⟨27, by decide⟩ | 117 => ⟨37, by decide⟩ | 118 => ⟨28, by decide⟩ | 119 => ⟨94, by decide⟩
  | 120 => ⟨62, by decide⟩ | 121 => ⟨29, by decide⟩ | 122 => ⟨35, by decide⟩ | 123 => ⟨91, by decide⟩ | 124 => ⟨124, by decide⟩ | 125 => ⟨125, by decide⟩ | 126 => ⟨42, by decide⟩ | _ => ⟨127, by decide⟩
private def c6Perm_swap12 (cid : Fin 128) : Fin 128 :=
  match cid.val with
  | 0 => ⟨123, by decide⟩ | 1 => ⟨104, by decide⟩ | 2 => ⟨106, by decide⟩ | 3 => ⟨119, by decide⟩ | 4 => ⟨60, by decide⟩ | 5 => ⟨99, by decide⟩ | 6 => ⟨6, by decide⟩ | 7 => ⟨118, by decide⟩
  | 8 => ⟨80, by decide⟩ | 9 => ⟨73, by decide⟩ | 10 => ⟨34, by decide⟩ | 11 => ⟨64, by decide⟩ | 12 => ⟨105, by decide⟩ | 13 => ⟨109, by decide⟩ | 14 => ⟨44, by decide⟩ | 15 => ⟨95, by decide⟩
  | 16 => ⟨89, by decide⟩ | 17 => ⟨97, by decide⟩ | 18 => ⟨47, by decide⟩ | 19 => ⟨28, by decide⟩ | 20 => ⟨33, by decide⟩ | 21 => ⟨58, by decide⟩ | 22 => ⟨79, by decide⟩ | 23 => ⟨88, by decide⟩
  | 24 => ⟨24, by decide⟩ | 25 => ⟨100, by decide⟩ | 26 => ⟨29, by decide⟩ | 27 => ⟨120, by decide⟩ | 28 => ⟨19, by decide⟩ | 29 => ⟨26, by decide⟩ | 30 => ⟨63, by decide⟩ | 31 => ⟨85, by decide⟩
  | 32 => ⟨32, by decide⟩ | 33 => ⟨20, by decide⟩ | 34 => ⟨10, by decide⟩ | 35 => ⟨59, by decide⟩ | 36 => ⟨112, by decide⟩ | 37 => ⟨96, by decide⟩ | 38 => ⟨39, by decide⟩ | 39 => ⟨38, by decide⟩
  | 40 => ⟨94, by decide⟩ | 41 => ⟨49, by decide⟩ | 42 => ⟨98, by decide⟩ | 43 => ⟨122, by decide⟩ | 44 => ⟨14, by decide⟩ | 45 => ⟨68, by decide⟩ | 46 => ⟨90, by decide⟩ | 47 => ⟨18, by decide⟩
  | 48 => ⟨53, by decide⟩ | 49 => ⟨41, by decide⟩ | 50 => ⟨50, by decide⟩ | 51 => ⟨51, by decide⟩ | 52 => ⟨52, by decide⟩ | 53 => ⟨48, by decide⟩ | 54 => ⟨127, by decide⟩ | 55 => ⟨83, by decide⟩
  | 56 => ⟨84, by decide⟩ | 57 => ⟨61, by decide⟩ | 58 => ⟨21, by decide⟩ | 59 => ⟨35, by decide⟩ | 60 => ⟨4, by decide⟩ | 61 => ⟨57, by decide⟩ | 62 => ⟨65, by decide⟩ | 63 => ⟨30, by decide⟩
  | 64 => ⟨11, by decide⟩ | 65 => ⟨62, by decide⟩ | 66 => ⟨66, by decide⟩ | 67 => ⟨67, by decide⟩ | 68 => ⟨45, by decide⟩ | 69 => ⟨111, by decide⟩ | 70 => ⟨92, by decide⟩ | 71 => ⟨125, by decide⟩
  | 72 => ⟨74, by decide⟩ | 73 => ⟨9, by decide⟩ | 74 => ⟨72, by decide⟩ | 75 => ⟨101, by decide⟩ | 76 => ⟨78, by decide⟩ | 77 => ⟨126, by decide⟩ | 78 => ⟨76, by decide⟩ | 79 => ⟨22, by decide⟩
  | 80 => ⟨8, by decide⟩ | 81 => ⟨107, by decide⟩ | 82 => ⟨82, by decide⟩ | 83 => ⟨55, by decide⟩ | 84 => ⟨56, by decide⟩ | 85 => ⟨31, by decide⟩ | 86 => ⟨115, by decide⟩ | 87 => ⟨87, by decide⟩
  | 88 => ⟨23, by decide⟩ | 89 => ⟨16, by decide⟩ | 90 => ⟨46, by decide⟩ | 91 => ⟨113, by decide⟩ | 92 => ⟨70, by decide⟩ | 93 => ⟨93, by decide⟩ | 94 => ⟨40, by decide⟩ | 95 => ⟨15, by decide⟩
  | 96 => ⟨37, by decide⟩ | 97 => ⟨17, by decide⟩ | 98 => ⟨42, by decide⟩ | 99 => ⟨5, by decide⟩ | 100 => ⟨25, by decide⟩ | 101 => ⟨75, by decide⟩ | 102 => ⟨103, by decide⟩ | 103 => ⟨102, by decide⟩
  | 104 => ⟨1, by decide⟩ | 105 => ⟨12, by decide⟩ | 106 => ⟨2, by decide⟩ | 107 => ⟨81, by decide⟩ | 108 => ⟨116, by decide⟩ | 109 => ⟨13, by decide⟩ | 110 => ⟨110, by decide⟩ | 111 => ⟨69, by decide⟩
  | 112 => ⟨36, by decide⟩ | 113 => ⟨91, by decide⟩ | 114 => ⟨114, by decide⟩ | 115 => ⟨86, by decide⟩ | 116 => ⟨108, by decide⟩ | 117 => ⟨117, by decide⟩ | 118 => ⟨7, by decide⟩ | 119 => ⟨3, by decide⟩
  | 120 => ⟨27, by decide⟩ | 121 => ⟨121, by decide⟩ | 122 => ⟨43, by decide⟩ | 123 => ⟨0, by decide⟩ | 124 => ⟨124, by decide⟩ | 125 => ⟨71, by decide⟩ | 126 => ⟨77, by decide⟩ | _ => ⟨54, by decide⟩
private def c6Perm_swap23 (cid : Fin 128) : Fin 128 :=
  match cid.val with
  | 0 => ⟨53, by decide⟩ | 1 => ⟨108, by decide⟩ | 2 => ⟨29, by decide⟩ | 3 => ⟨78, by decide⟩ | 4 => ⟨14, by decide⟩ | 5 => ⟨44, by decide⟩ | 6 => ⟨33, by decide⟩ | 7 => ⟨61, by decide⟩
  | 8 => ⟨8, by decide⟩ | 9 => ⟨16, by decide⟩ | 10 => ⟨106, by decide⟩ | 11 => ⟨57, by decide⟩ | 12 => ⟨52, by decide⟩ | 13 => ⟨122, by decide⟩ | 14 => ⟨4, by decide⟩ | 15 => ⟨50, by decide⟩
  | 16 => ⟨9, by decide⟩ | 17 => ⟨109, by decide⟩ | 18 => ⟨94, by decide⟩ | 19 => ⟨19, by decide⟩ | 20 => ⟨20, by decide⟩ | 21 => ⟨39, by decide⟩ | 22 => ⟨98, by decide⟩ | 23 => ⟨23, by decide⟩
  | 24 => ⟨88, by decide⟩ | 25 => ⟨74, by decide⟩ | 26 => ⟨34, by decide⟩ | 27 => ⟨89, by decide⟩ | 28 => ⟨114, by decide⟩ | 29 => ⟨2, by decide⟩ | 30 => ⟨42, by decide⟩ | 31 => ⟨31, by decide⟩
  | 32 => ⟨96, by decide⟩ | 33 => ⟨6, by decide⟩ | 34 => ⟨26, by decide⟩ | 35 => ⟨76, by decide⟩ | 36 => ⟨36, by decide⟩ | 37 => ⟨37, by decide⟩ | 38 => ⟨41, by decide⟩ | 39 => ⟨21, by decide⟩
  | 40 => ⟨115, by decide⟩ | 41 => ⟨38, by decide⟩ | 42 => ⟨30, by decide⟩ | 43 => ⟨97, by decide⟩ | 44 => ⟨5, by decide⟩ | 45 => ⟨45, by decide⟩ | 46 => ⟨51, by decide⟩ | 47 => ⟨86, by decide⟩
  | 48 => ⟨103, by decide⟩ | 49 => ⟨58, by decide⟩ | 50 => ⟨15, by decide⟩ | 51 => ⟨46, by decide⟩ | 52 => ⟨12, by decide⟩ | 53 => ⟨0, by decide⟩ | 54 => ⟨100, by decide⟩ | 55 => ⟨125, by decide⟩
  | 56 => ⟨65, by decide⟩ | 57 => ⟨11, by decide⟩ | 58 => ⟨49, by decide⟩ | 59 => ⟨119, by decide⟩ | 60 => ⟨99, by decide⟩ | 61 => ⟨7, by decide⟩ | 62 => ⟨113, by decide⟩ | 63 => ⟨79, by decide⟩
  | 64 => ⟨118, by decide⟩ | 65 => ⟨56, by decide⟩ | 66 => ⟨85, by decide⟩ | 67 => ⟨126, by decide⟩ | 68 => ⟨110, by decide⟩ | 69 => ⟨116, by decide⟩ | 70 => ⟨83, by decide⟩ | 71 => ⟨92, by decide⟩
  | 72 => ⟨127, by decide⟩ | 73 => ⟨120, by decide⟩ | 74 => ⟨25, by decide⟩ | 75 => ⟨82, by decide⟩ | 76 => ⟨35, by decide⟩ | 77 => ⟨77, by decide⟩ | 78 => ⟨3, by decide⟩ | 79 => ⟨63, by decide⟩
  | 80 => ⟨121, by decide⟩ | 81 => ⟨81, by decide⟩ | 82 => ⟨75, by decide⟩ | 83 => ⟨70, by decide⟩ | 84 => ⟨91, by decide⟩ | 85 => ⟨66, by decide⟩ | 86 => ⟨47, by decide⟩ | 87 => ⟨107, by decide⟩
  | 88 => ⟨24, by decide⟩ | 89 => ⟨27, by decide⟩ | 90 => ⟨90, by decide⟩ | 91 => ⟨84, by decide⟩ | 92 => ⟨71, by decide⟩ | 93 => ⟨93, by decide⟩ | 94 => ⟨18, by decide⟩ | 95 => ⟨95, by decide⟩
  | 96 => ⟨32, by decide⟩ | 97 => ⟨43, by decide⟩ | 98 => ⟨22, by decide⟩ | 99 => ⟨60, by decide⟩ | 100 => ⟨54, by decide⟩ | 101 => ⟨101, by decide⟩ | 102 => ⟨123, by decide⟩ | 103 => ⟨48, by decide⟩
  | 104 => ⟨111, by decide⟩ | 105 => ⟨105, by decide⟩ | 106 => ⟨10, by decide⟩ | 107 => ⟨87, by decide⟩ | 108 => ⟨1, by decide⟩ | 109 => ⟨17, by decide⟩ | 110 => ⟨68, by decide⟩ | 111 => ⟨104, by decide⟩
  | 112 => ⟨124, by decide⟩ | 113 => ⟨62, by decide⟩ | 114 => ⟨28, by decide⟩ | 115 => ⟨40, by decide⟩ | 116 => ⟨69, by decide⟩ | 117 => ⟨117, by decide⟩ | 118 => ⟨64, by decide⟩ | 119 => ⟨59, by decide⟩
  | 120 => ⟨73, by decide⟩ | 121 => ⟨80, by decide⟩ | 122 => ⟨13, by decide⟩ | 123 => ⟨102, by decide⟩ | 124 => ⟨112, by decide⟩ | 125 => ⟨55, by decide⟩ | 126 => ⟨67, by decide⟩ | _ => ⟨72, by decide⟩

private def q3Flip0 (q : Q3Bits) : Q3Bits := { e01 := q.e01, e02 := q.e13, e04 := q.e15, e13 := q.e02, e15 := q.e04, e23 := q.e23, e26 := q.e37, e37 := q.e26, e45 := q.e45, e46 := q.e57, e57 := q.e46, e67 := q.e67 }
private def q3Swap01 (q : Q3Bits) : Q3Bits := { e01 := q.e02, e02 := q.e01, e04 := q.e04, e13 := q.e23, e15 := q.e26, e23 := q.e13, e26 := q.e15, e37 := q.e37, e45 := q.e46, e46 := q.e45, e57 := q.e67, e67 := q.e57 }
private def q3Swap12 (q : Q3Bits) : Q3Bits := { e01 := q.e01, e02 := q.e04, e04 := q.e02, e13 := q.e15, e15 := q.e13, e23 := q.e45, e26 := q.e46, e37 := q.e57, e45 := q.e23, e46 := q.e26, e57 := q.e37, e67 := q.e67 }
private def b2Swap01 (b : B2Bits) : B2Bits := { b01 := b.b02, b02 := b.b01, b04 := b.b04, b08 := b.b08, b13 := b.b23, b15 := b.b26, b19 := b.b2a, b23 := b.b13, b26 := b.b15, b2a := b.b19, b45 := b.b46, b46 := b.b45, b4c := b.b4c, b89 := b.b8a, b8a := b.b89, b8c := b.b8c }
private def b2Swap12 (b : B2Bits) : B2Bits := { b01 := b.b01, b02 := b.b04, b04 := b.b02, b08 := b.b08, b13 := b.b15, b15 := b.b13, b19 := b.b19, b23 := b.b45, b26 := b.b46, b2a := b.b4c, b45 := b.b23, b46 := b.b26, b4c := b.b2a, b89 := b.b89, b8a := b.b8c, b8c := b.b8a }
private def b2Swap23 (b : B2Bits) : B2Bits := { b01 := b.b01, b02 := b.b02, b04 := b.b08, b08 := b.b04, b13 := b.b13, b15 := b.b19, b19 := b.b15, b23 := b.b23, b26 := b.b2a, b2a := b.b26, b45 := b.b89, b46 := b.b8a, b4c := b.b8c, b89 := b.b45, b8a := b.b46, b8c := b.b4c }



private inductive Aut4Gen | f0 | s01 | s12 | s23 deriving DecidableEq
private def applyGen4 : Aut4Gen → Q4Bits → Q4Bits
  | .f0, g => q4Flip0 g | .s01, g => q4Swap01 g | .s12, g => q4Swap12 g | .s23, g => q4Swap23 g
private def applyWord4 (w : List Aut4Gen) (g : Q4Bits) : Q4Bits := w.foldr applyGen4 g

private def liftAut3Word (ai : Fin 48) : List Aut4Gen :=
  match ai.val with
  | 0 => []
  | 1 => [.f0]
  | 2 => [.s01, .f0, .s01]
  | 3 => [.s01, .f0, .s01, .f0]
  | 4 => [.s12, .s01, .f0, .s01, .s12]
  | 5 => [.s12, .s01, .f0, .s01, .s12, .f0]
  | 6 => [.s12, .s01, .f0, .s01, .s12, .s01, .f0, .s01]
  | 7 => [.s12, .s01, .f0, .s01, .s12, .s01, .f0, .s01, .f0]
  | 8 => [.s12]
  | 9 => [.s12, .f0]
  | 10 => [.s12, .s01, .f0, .s01]
  | 11 => [.s12, .s01, .f0, .s01, .f0]
  | 12 => [.s01, .f0, .s01, .s12]
  | 13 => [.s01, .f0, .s01, .s12, .f0]
  | 14 => [.s01, .f0, .s01, .s12, .s01, .f0, .s01]
  | 15 => [.s01, .f0, .s01, .s12, .s01, .f0, .s01, .f0]
  | 16 => [.s01]
  | 17 => [.s01, .f0]
  | 18 => [.f0, .s01]
  | 19 => [.f0, .s01, .f0]
  | 20 => [.s12, .s01, .f0, .s01, .s12, .s01]
  | 21 => [.s12, .s01, .f0, .s01, .s12, .s01, .f0]
  | 22 => [.s12, .s01, .f0, .s01, .s12, .f0, .s01]
  | 23 => [.s12, .s01, .f0, .s01, .s12, .f0, .s01, .f0]
  | 24 => [.s01, .s12]
  | 25 => [.s01, .s12, .f0]
  | 26 => [.s01, .s12, .s01, .f0, .s01]
  | 27 => [.s01, .s12, .s01, .f0, .s01, .f0]
  | 28 => [.f0, .s01, .s12]
  | 29 => [.f0, .s01, .s12, .f0]
  | 30 => [.f0, .s01, .s12, .s01, .f0, .s01]
  | 31 => [.f0, .s01, .s12, .s01, .f0, .s01, .f0]
  | 32 => [.s12, .s01]
  | 33 => [.s12, .s01, .f0]
  | 34 => [.s12, .f0, .s01]
  | 35 => [.s12, .f0, .s01, .f0]
  | 36 => [.s01, .f0, .s01, .s12, .s01]
  | 37 => [.s01, .f0, .s01, .s12, .s01, .f0]
  | 38 => [.s01, .f0, .s01, .s12, .f0, .s01]
  | 39 => [.s01, .f0, .s01, .s12, .f0, .s01, .f0]
  | 40 => [.s01, .s12, .s01]
  | 41 => [.s01, .s12, .s01, .f0]
  | 42 => [.s01, .s12, .f0, .s01]
  | 43 => [.s01, .s12, .f0, .s01, .f0]
  | 44 => [.f0, .s01, .s12, .s01]
  | 45 => [.f0, .s01, .s12, .s01, .f0]
  | 46 => [.f0, .s01, .s12, .f0, .s01]
  | _ => [.f0, .s01, .s12, .f0, .s01, .f0]
private def liftAut3 (ai : Fin 48) (g : Q4Bits) : Q4Bits := applyWord4 (liftAut3Word ai) g

private def moveFacetWord (fk : Fin 8) : List Aut4Gen :=
  match fk.val with
  | 0 => [.s23, .s12, .s01]
  | 1 => [.s23, .s12, .s01, .f0]
  | 2 => [.s23, .s12]
  | 3 => [.s23, .s12, .s01, .f0, .s01]
  | 4 => [.s23]
  | 5 => [.s23, .s12, .s01, .f0, .s01, .s12]
  | 6 => []
  | _ => [.s23, .s12, .s01, .f0, .s01, .s12, .s23]
private def moveFacetTo6 (fk : Fin 8) (g : Q4Bits) : Q4Bits := applyWord4 (moveFacetWord fk) g

private def q4EdgePerm_flip0 (e : Fin 32) : Fin 32 :=
  match e.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨4, by decide⟩ | 2 => ⟨5, by decide⟩ | 3 => ⟨6, by decide⟩ | 4 => ⟨1, by decide⟩ | 5 => ⟨2, by decide⟩ | 6 => ⟨3, by decide⟩ | 7 => ⟨7, by decide⟩ | 8 => ⟨10, by decide⟩ | 9 => ⟨11, by decide⟩ | 10 => ⟨8, by decide⟩ | 11 => ⟨9, by decide⟩ | 12 => ⟨12, by decide⟩ | 13 => ⟨15, by decide⟩ | 14 => ⟨16, by decide⟩ | 15 => ⟨13, by decide⟩ | 16 => ⟨14, by decide⟩ | 17 => ⟨17, by decide⟩ | 18 => ⟨19, by decide⟩ | 19 => ⟨18, by decide⟩ | 20 => ⟨20, by decide⟩ | 21 => ⟨23, by decide⟩ | 22 => ⟨24, by decide⟩ | 23 => ⟨21, by decide⟩ | 24 => ⟨22, by decide⟩ | 25 => ⟨25, by decide⟩ | 26 => ⟨27, by decide⟩ | 27 => ⟨26, by decide⟩ | 28 => ⟨28, by decide⟩ | 29 => ⟨30, by decide⟩ | 30 => ⟨29, by decide⟩ | _ => ⟨31, by decide⟩
private def q4EdgePerm_swap01 (e : Fin 32) : Fin 32 :=
  match e.val with
  | 0 => ⟨1, by decide⟩ | 1 => ⟨0, by decide⟩ | 2 => ⟨2, by decide⟩ | 3 => ⟨3, by decide⟩ | 4 => ⟨7, by decide⟩ | 5 => ⟨8, by decide⟩ | 6 => ⟨9, by decide⟩ | 7 => ⟨4, by decide⟩ | 8 => ⟨5, by decide⟩ | 9 => ⟨6, by decide⟩ | 10 => ⟨10, by decide⟩ | 11 => ⟨11, by decide⟩ | 12 => ⟨13, by decide⟩ | 13 => ⟨12, by decide⟩ | 14 => ⟨14, by decide⟩ | 15 => ⟨17, by decide⟩ | 16 => ⟨18, by decide⟩ | 17 => ⟨15, by decide⟩ | 18 => ⟨16, by decide⟩ | 19 => ⟨19, by decide⟩ | 20 => ⟨21, by decide⟩ | 21 => ⟨20, by decide⟩ | 22 => ⟨22, by decide⟩ | 23 => ⟨25, by decide⟩ | 24 => ⟨26, by decide⟩ | 25 => ⟨23, by decide⟩ | 26 => ⟨24, by decide⟩ | 27 => ⟨27, by decide⟩ | 28 => ⟨29, by decide⟩ | 29 => ⟨28, by decide⟩ | 30 => ⟨31, by decide⟩ | _ => ⟨30, by decide⟩
private def q4EdgePerm_swap12 (e : Fin 32) : Fin 32 :=
  match e.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨1, by decide⟩ | 3 => ⟨3, by decide⟩ | 4 => ⟨5, by decide⟩ | 5 => ⟨4, by decide⟩ | 6 => ⟨6, by decide⟩ | 7 => ⟨12, by decide⟩ | 8 => ⟨13, by decide⟩ | 9 => ⟨14, by decide⟩ | 10 => ⟨15, by decide⟩ | 11 => ⟨16, by decide⟩ | 12 => ⟨7, by decide⟩ | 13 => ⟨8, by decide⟩ | 14 => ⟨9, by decide⟩ | 15 => ⟨10, by decide⟩ | 16 => ⟨11, by decide⟩ | 17 => ⟨17, by decide⟩ | 18 => ⟨18, by decide⟩ | 19 => ⟨19, by decide⟩ | 20 => ⟨20, by decide⟩ | 21 => ⟨22, by decide⟩ | 22 => ⟨21, by decide⟩ | 23 => ⟨24, by decide⟩ | 24 => ⟨23, by decide⟩ | 25 => ⟨28, by decide⟩ | 26 => ⟨29, by decide⟩ | 27 => ⟨30, by decide⟩ | 28 => ⟨25, by decide⟩ | 29 => ⟨26, by decide⟩ | 30 => ⟨27, by decide⟩ | _ => ⟨31, by decide⟩
private def q4EdgePerm_swap23 (e : Fin 32) : Fin 32 :=
  match e.val with
  | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | 3 => ⟨2, by decide⟩ | 4 => ⟨4, by decide⟩ | 5 => ⟨6, by decide⟩ | 6 => ⟨5, by decide⟩ | 7 => ⟨7, by decide⟩ | 8 => ⟨9, by decide⟩ | 9 => ⟨8, by decide⟩ | 10 => ⟨11, by decide⟩ | 11 => ⟨10, by decide⟩ | 12 => ⟨20, by decide⟩ | 13 => ⟨21, by decide⟩ | 14 => ⟨22, by decide⟩ | 15 => ⟨23, by decide⟩ | 16 => ⟨24, by decide⟩ | 17 => ⟨25, by decide⟩ | 18 => ⟨26, by decide⟩ | 19 => ⟨27, by decide⟩ | 20 => ⟨12, by decide⟩ | 21 => ⟨13, by decide⟩ | 22 => ⟨14, by decide⟩ | 23 => ⟨15, by decide⟩ | 24 => ⟨16, by decide⟩ | 25 => ⟨17, by decide⟩ | 26 => ⟨18, by decide⟩ | 27 => ⟨19, by decide⟩ | 28 => ⟨28, by decide⟩ | 29 => ⟨29, by decide⟩ | 30 => ⟨30, by decide⟩ | _ => ⟨31, by decide⟩

private def c6CycleOrdEdge (cid : Fin 128) (j : Fin 6) : Fin 32 :=
  match cid.val, j.val with
  | 0, 0 => ⟨2, by decide⟩ | 0, 1 => ⟨12, by decide⟩ | 0, 2 => ⟨16, by decide⟩ | 0, 3 => ⟨28, by decide⟩ | 0, 4 => ⟨22, by decide⟩ | 0, _ => ⟨3, by decide⟩
  | 1, 0 => ⟨0, by decide⟩ | 1, 1 => ⟨4, by decide⟩ | 1, 2 => ⟨10, by decide⟩ | 1, 3 => ⟨17, by decide⟩ | 1, 4 => ⟨8, by decide⟩ | 1, _ => ⟨1, by decide⟩
  | 2, 0 => ⟨7, by decide⟩ | 2, 1 => ⟨10, by decide⟩ | 2, 2 => ⟨19, by decide⟩ | 2, 3 => ⟨31, by decide⟩ | 2, 4 => ⟨26, by decide⟩ | 2, _ => ⟨9, by decide⟩
  | 3, 0 => ⟨20, by decide⟩ | 3, 1 => ⟨24, by decide⟩ | 3, 2 => ⟨30, by decide⟩ | 3, 3 => ⟨27, by decide⟩ | 3, 4 => ⟨25, by decide⟩ | 3, _ => ⟨21, by decide⟩
  | 4, 0 => ⟨15, by decide⟩ | 4, 1 => ⟨19, by decide⟩ | 4, 2 => ⟨31, by decide⟩ | 4, 3 => ⟨29, by decide⟩ | 4, 4 => ⟨28, by decide⟩ | 4, _ => ⟨16, by decide⟩
  | 5, 0 => ⟨15, by decide⟩ | 5, 1 => ⟨17, by decide⟩ | 5, 2 => ⟨18, by decide⟩ | 5, 3 => ⟨31, by decide⟩ | 5, 4 => ⟨30, by decide⟩ | 5, _ => ⟨16, by decide⟩
  | 6, 0 => ⟨21, by decide⟩ | 6, 1 => ⟨25, by decide⟩ | 6, 2 => ⟨27, by decide⟩ | 6, 3 => ⟨30, by decide⟩ | 6, 4 => ⟨28, by decide⟩ | 6, _ => ⟨22, by decide⟩
  | 7, 0 => ⟨0, by decide⟩ | 7, 1 => ⟨4, by decide⟩ | 7, 2 => ⟨11, by decide⟩ | 7, 3 => ⟨25, by decide⟩ | 7, 4 => ⟨21, by decide⟩ | 7, _ => ⟨3, by decide⟩
  | 8, 0 => ⟨5, by decide⟩ | 8, 1 => ⟨15, by decide⟩ | 8, 2 => ⟨19, by decide⟩ | 8, 3 => ⟨27, by decide⟩ | 8, 4 => ⟨23, by decide⟩ | 8, _ => ⟨6, by decide⟩
  | 9, 0 => ⟨2, by decide⟩ | 9, 1 => ⟨13, by decide⟩ | 9, 2 => ⟨18, by decide⟩ | 9, 3 => ⟨29, by decide⟩ | 9, 4 => ⟨22, by decide⟩ | 9, _ => ⟨3, by decide⟩
  | 10, 0 => ⟨20, by decide⟩ | 10, 1 => ⟨23, by decide⟩ | 10, 2 => ⟨27, by decide⟩ | 10, 3 => ⟨31, by decide⟩ | 10, 4 => ⟨29, by decide⟩ | 10, _ => ⟨22, by decide⟩
  | 11, 0 => ⟨0, by decide⟩ | 11, 1 => ⟨6, by decide⟩ | 11, 2 => ⟨23, by decide⟩ | 11, 3 => ⟨25, by decide⟩ | 11, 4 => ⟨9, by decide⟩ | 11, _ => ⟨1, by decide⟩
  | 12, 0 => ⟨1, by decide⟩ | 12, 1 => ⟨7, by decide⟩ | 12, 2 => ⟨4, by decide⟩ | 12, 3 => ⟨6, by decide⟩ | 12, 4 => ⟨20, by decide⟩ | 12, _ => ⟨3, by decide⟩
  | 13, 0 => ⟨4, by decide⟩ | 13, 1 => ⟨11, by decide⟩ | 13, 2 => ⟨27, by decide⟩ | 13, 3 => ⟨19, by decide⟩ | 13, 4 => ⟨15, by decide⟩ | 13, _ => ⟨5, by decide⟩
  | 14, 0 => ⟨23, by decide⟩ | 14, 1 => ⟨27, by decide⟩ | 14, 2 => ⟨31, by decide⟩ | 14, 3 => ⟨29, by decide⟩ | 14, 4 => ⟨28, by decide⟩ | 14, _ => ⟨24, by decide⟩
  | 15, 0 => ⟨4, by decide⟩ | 15, 1 => ⟨10, by decide⟩ | 15, 2 => ⟨15, by decide⟩ | 15, 3 => ⟨16, by decide⟩ | 15, 4 => ⟨24, by decide⟩ | 15, _ => ⟨6, by decide⟩
  | 16, 0 => ⟨2, by decide⟩ | 16, 1 => ⟨14, by decide⟩ | 16, 2 => ⟨29, by decide⟩ | 16, 3 => ⟨26, by decide⟩ | 16, 4 => ⟨21, by decide⟩ | 16, _ => ⟨3, by decide⟩
  | 17, 0 => ⟨4, by decide⟩ | 17, 1 => ⟨11, by decide⟩ | 17, 2 => ⟨27, by decide⟩ | 17, 3 => ⟨30, by decide⟩ | 17, 4 => ⟨24, by decide⟩ | 17, _ => ⟨6, by decide⟩
  | 18, 0 => ⟨13, by decide⟩ | 18, 1 => ⟨17, by decide⟩ | 18, 2 => ⟨19, by decide⟩ | 18, 3 => ⟨31, by decide⟩ | 18, 4 => ⟨29, by decide⟩ | 18, _ => ⟨14, by decide⟩
  | 19, 0 => ⟨2, by decide⟩ | 19, 1 => ⟨13, by decide⟩ | 19, 2 => ⟨18, by decide⟩ | 19, 3 => ⟨26, by decide⟩ | 19, 4 => ⟨21, by decide⟩ | 19, _ => ⟨3, by decide⟩
  | 20, 0 => ⟨8, by decide⟩ | 20, 1 => ⟨17, by decide⟩ | 20, 2 => ⟨19, by decide⟩ | 20, 3 => ⟨27, by decide⟩ | 20, 4 => ⟨25, by decide⟩ | 20, _ => ⟨9, by decide⟩
  | 21, 0 => ⟨20, by decide⟩ | 21, 1 => ⟨23, by decide⟩ | 21, 2 => ⟨27, by decide⟩ | 21, 3 => ⟨31, by decide⟩ | 21, 4 => ⟨26, by decide⟩ | 21, _ => ⟨21, by decide⟩
  | 22, 0 => ⟨7, by decide⟩ | 22, 1 => ⟨11, by decide⟩ | 22, 2 => ⟨25, by decide⟩ | 22, 3 => ⟨26, by decide⟩ | 22, 4 => ⟨18, by decide⟩ | 22, _ => ⟨8, by decide⟩
  | 23, 0 => ⟨17, by decide⟩ | 23, 1 => ⟨19, by decide⟩ | 23, 2 => ⟨27, by decide⟩ | 23, 3 => ⟨25, by decide⟩ | 23, 4 => ⟨26, by decide⟩ | 23, _ => ⟨18, by decide⟩
  | 24, 0 => ⟨25, by decide⟩ | 24, 1 => ⟨27, by decide⟩ | 24, 2 => ⟨30, by decide⟩ | 24, 3 => ⟨28, by decide⟩ | 24, 4 => ⟨29, by decide⟩ | 24, _ => ⟨26, by decide⟩
  | 25, 0 => ⟨4, by decide⟩ | 25, 1 => ⟨11, by decide⟩ | 25, 2 => ⟨25, by decide⟩ | 25, 3 => ⟨21, by decide⟩ | 25, 4 => ⟨20, by decide⟩ | 25, _ => ⟨6, by decide⟩
  | 26, 0 => ⟨12, by decide⟩ | 26, 1 => ⟨16, by decide⟩ | 26, 2 => ⟨30, by decide⟩ | 26, 3 => ⟨31, by decide⟩ | 26, 4 => ⟨18, by decide⟩ | 26, _ => ⟨13, by decide⟩
  | 27, 0 => ⟨1, by decide⟩ | 27, 1 => ⟨8, by decide⟩ | 27, 2 => ⟨18, by decide⟩ | 27, 3 => ⟨29, by decide⟩ | 27, 4 => ⟨14, by decide⟩ | 27, _ => ⟨2, by decide⟩
  | 28, 0 => ⟨1, by decide⟩ | 28, 1 => ⟨8, by decide⟩ | 28, 2 => ⟨18, by decide⟩ | 28, 3 => ⟨29, by decide⟩ | 28, 4 => ⟨22, by decide⟩ | 28, _ => ⟨3, by decide⟩
  | 29, 0 => ⟨7, by decide⟩ | 29, 1 => ⟨11, by decide⟩ | 29, 2 => ⟨27, by decide⟩ | 29, 3 => ⟨31, by decide⟩ | 29, 4 => ⟨18, by decide⟩ | 29, _ => ⟨8, by decide⟩
  | 30, 0 => ⟨20, by decide⟩ | 30, 1 => ⟨23, by decide⟩ | 30, 2 => ⟨25, by decide⟩ | 30, 3 => ⟨26, by decide⟩ | 30, 4 => ⟨29, by decide⟩ | 30, _ => ⟨22, by decide⟩
  | 31, 0 => ⟨2, by decide⟩ | 31, 1 => ⟨12, by decide⟩ | 31, 2 => ⟨16, by decide⟩ | 31, 3 => ⟨24, by decide⟩ | 31, 4 => ⟨20, by decide⟩ | 31, _ => ⟨3, by decide⟩
  | 32, 0 => ⟨23, by decide⟩ | 32, 1 => ⟨25, by decide⟩ | 32, 2 => ⟨26, by decide⟩ | 32, 3 => ⟨29, by decide⟩ | 32, 4 => ⟨28, by decide⟩ | 32, _ => ⟨24, by decide⟩
  | 33, 0 => ⟨13, by decide⟩ | 33, 1 => ⟨17, by decide⟩ | 33, 2 => ⟨19, by decide⟩ | 33, 3 => ⟨30, by decide⟩ | 33, 4 => ⟨28, by decide⟩ | 33, _ => ⟨14, by decide⟩
  | 34, 0 => ⟨20, by decide⟩ | 34, 1 => ⟨24, by decide⟩ | 34, 2 => ⟨30, by decide⟩ | 34, 3 => ⟨31, by decide⟩ | 34, 4 => ⟨26, by decide⟩ | 34, _ => ⟨21, by decide⟩
  | 35, 0 => ⟨7, by decide⟩ | 35, 1 => ⟨10, by decide⟩ | 35, 2 => ⟨19, by decide⟩ | 35, 3 => ⟨27, by decide⟩ | 35, 4 => ⟨25, by decide⟩ | 35, _ => ⟨9, by decide⟩
  | 36, 0 => ⟨5, by decide⟩ | 36, 1 => ⟨12, by decide⟩ | 36, 2 => ⟨14, by decide⟩ | 36, 3 => ⟨22, by decide⟩ | 36, 4 => ⟨20, by decide⟩ | 36, _ => ⟨6, by decide⟩
  | 37, 0 => ⟨10, by decide⟩ | 37, 1 => ⟨17, by decide⟩ | 37, 2 => ⟨18, by decide⟩ | 37, 3 => ⟨26, by decide⟩ | 37, 4 => ⟨25, by decide⟩ | 37, _ => ⟨11, by decide⟩
  | 38, 0 => ⟨7, by decide⟩ | 38, 1 => ⟨10, by decide⟩ | 38, 2 => ⟨19, by decide⟩ | 38, 3 => ⟨31, by decide⟩ | 38, 4 => ⟨18, by decide⟩ | 38, _ => ⟨8, by decide⟩
  | 39, 0 => ⟨12, by decide⟩ | 39, 1 => ⟨15, by decide⟩ | 39, 2 => ⟨19, by decide⟩ | 39, 3 => ⟨31, by decide⟩ | 39, 4 => ⟨18, by decide⟩ | 39, _ => ⟨13, by decide⟩
  | 40, 0 => ⟨21, by decide⟩ | 40, 1 => ⟨26, by decide⟩ | 40, 2 => ⟨31, by decide⟩ | 40, 3 => ⟨30, by decide⟩ | 40, 4 => ⟨28, by decide⟩ | 40, _ => ⟨22, by decide⟩
  | 41, 0 => ⟨7, by decide⟩ | 41, 1 => ⟨11, by decide⟩ | 41, 2 => ⟨27, by decide⟩ | 41, 3 => ⟨31, by decide⟩ | 41, 4 => ⟨26, by decide⟩ | 41, _ => ⟨9, by decide⟩
  | 42, 0 => ⟨12, by decide⟩ | 42, 1 => ⟨15, by decide⟩ | 42, 2 => ⟨17, by decide⟩ | 42, 3 => ⟨18, by decide⟩ | 42, 4 => ⟨29, by decide⟩ | 42, _ => ⟨14, by decide⟩
  | 43, 0 => ⟨5, by decide⟩ | 43, 1 => ⟨15, by decide⟩ | 43, 2 => ⟨19, by decide⟩ | 43, 3 => ⟨30, by decide⟩ | 43, 4 => ⟨24, by decide⟩ | 43, _ => ⟨6, by decide⟩
  | 44, 0 => ⟨23, by decide⟩ | 44, 1 => ⟨25, by decide⟩ | 44, 2 => ⟨26, by decide⟩ | 44, 3 => ⟨31, by decide⟩ | 44, 4 => ⟨30, by decide⟩ | 44, _ => ⟨24, by decide⟩
  | 45, 0 => ⟨2, by decide⟩ | 45, 1 => ⟨13, by decide⟩ | 45, 2 => ⟨8, by decide⟩ | 45, 3 => ⟨9, by decide⟩ | 45, 4 => ⟨21, by decide⟩ | 45, _ => ⟨3, by decide⟩
  | 46, 0 => ⟨8, by decide⟩ | 46, 1 => ⟨18, by decide⟩ | 46, 2 => ⟨29, by decide⟩ | 46, 3 => ⟨22, by decide⟩ | 46, 4 => ⟨21, by decide⟩ | 46, _ => ⟨9, by decide⟩
  | 47, 0 => ⟨8, by decide⟩ | 47, 1 => ⟨17, by decide⟩ | 47, 2 => ⟨19, by decide⟩ | 47, 3 => ⟨31, by decide⟩ | 47, 4 => ⟨26, by decide⟩ | 47, _ => ⟨9, by decide⟩
  | 48, 0 => ⟨1, by decide⟩ | 48, 1 => ⟨9, by decide⟩ | 48, 2 => ⟨25, by decide⟩ | 48, 3 => ⟨23, by decide⟩ | 48, 4 => ⟨20, by decide⟩ | 48, _ => ⟨3, by decide⟩
  | 49, 0 => ⟨12, by decide⟩ | 49, 1 => ⟨16, by decide⟩ | 49, 2 => ⟨30, by decide⟩ | 49, 3 => ⟨31, by decide⟩ | 49, 4 => ⟨29, by decide⟩ | 49, _ => ⟨14, by decide⟩
  | 50, 0 => ⟨4, by decide⟩ | 50, 1 => ⟨11, by decide⟩ | 50, 2 => ⟨23, by decide⟩ | 50, 3 => ⟨24, by decide⟩ | 50, 4 => ⟨16, by decide⟩ | 50, _ => ⟨5, by decide⟩
  | 51, 0 => ⟨8, by decide⟩ | 51, 1 => ⟨13, by decide⟩ | 51, 2 => ⟨14, by decide⟩ | 51, 3 => ⟨29, by decide⟩ | 51, 4 => ⟨26, by decide⟩ | 51, _ => ⟨9, by decide⟩
  | 52, 0 => ⟨1, by decide⟩ | 52, 1 => ⟨7, by decide⟩ | 52, 2 => ⟨4, by decide⟩ | 52, 3 => ⟨5, by decide⟩ | 52, 4 => ⟨12, by decide⟩ | 52, _ => ⟨2, by decide⟩
  | 53, 0 => ⟨2, by decide⟩ | 53, 1 => ⟨14, by decide⟩ | 53, 2 => ⟨28, by decide⟩ | 53, 3 => ⟨24, by decide⟩ | 53, 4 => ⟨20, by decide⟩ | 53, _ => ⟨3, by decide⟩
  | 54, 0 => ⟨5, by decide⟩ | 54, 1 => ⟨12, by decide⟩ | 54, 2 => ⟨14, by decide⟩ | 54, 3 => ⟨28, by decide⟩ | 54, 4 => ⟨24, by decide⟩ | 54, _ => ⟨6, by decide⟩
  | 55, 0 => ⟨0, by decide⟩ | 55, 1 => ⟨5, by decide⟩ | 55, 2 => ⟨12, by decide⟩ | 55, 3 => ⟨13, by decide⟩ | 55, 4 => ⟨8, by decide⟩ | 55, _ => ⟨1, by decide⟩
  | 56, 0 => ⟨0, by decide⟩ | 56, 1 => ⟨5, by decide⟩ | 56, 2 => ⟨15, by decide⟩ | 56, 3 => ⟨10, by decide⟩ | 56, 4 => ⟨7, by decide⟩ | 56, _ => ⟨1, by decide⟩
  | 57, 0 => ⟨0, by decide⟩ | 57, 1 => ⟨5, by decide⟩ | 57, 2 => ⟨15, by decide⟩ | 57, 3 => ⟨17, by decide⟩ | 57, 4 => ⟨8, by decide⟩ | 57, _ => ⟨1, by decide⟩
  | 58, 0 => ⟨20, by decide⟩ | 58, 1 => ⟨24, by decide⟩ | 58, 2 => ⟨30, by decide⟩ | 58, 3 => ⟨31, by decide⟩ | 58, 4 => ⟨29, by decide⟩ | 58, _ => ⟨22, by decide⟩
  | 59, 0 => ⟨12, by decide⟩ | 59, 1 => ⟨15, by decide⟩ | 59, 2 => ⟨19, by decide⟩ | 59, 3 => ⟨30, by decide⟩ | 59, 4 => ⟨28, by decide⟩ | 59, _ => ⟨14, by decide⟩
  | 60, 0 => ⟨10, by decide⟩ | 60, 1 => ⟨19, by decide⟩ | 60, 2 => ⟨31, by decide⟩ | 60, 3 => ⟨26, by decide⟩ | 60, 4 => ⟨25, by decide⟩ | 60, _ => ⟨11, by decide⟩
  | 61, 0 => ⟨0, by decide⟩ | 61, 1 => ⟨4, by decide⟩ | 61, 2 => ⟨10, by decide⟩ | 61, 3 => ⟨17, by decide⟩ | 61, 4 => ⟨13, by decide⟩ | 61, _ => ⟨2, by decide⟩
  | 62, 0 => ⟨0, by decide⟩ | 62, 1 => ⟨6, by decide⟩ | 62, 2 => ⟨24, by decide⟩ | 62, 3 => ⟨16, by decide⟩ | 62, 4 => ⟨12, by decide⟩ | 62, _ => ⟨2, by decide⟩
  | 63, 0 => ⟨20, by decide⟩ | 63, 1 => ⟨24, by decide⟩ | 63, 2 => ⟨28, by decide⟩ | 63, 3 => ⟨29, by decide⟩ | 63, 4 => ⟨26, by decide⟩ | 63, _ => ⟨21, by decide⟩
  | 64, 0 => ⟨0, by decide⟩ | 64, 1 => ⟨6, by decide⟩ | 64, 2 => ⟨24, by decide⟩ | 64, 3 => ⟨28, by decide⟩ | 64, 4 => ⟨14, by decide⟩ | 64, _ => ⟨2, by decide⟩
  | 65, 0 => ⟨0, by decide⟩ | 65, 1 => ⟨6, by decide⟩ | 65, 2 => ⟨23, by decide⟩ | 65, 3 => ⟨11, by decide⟩ | 65, 4 => ⟨7, by decide⟩ | 65, _ => ⟨1, by decide⟩
  | 66, 0 => ⟨1, by decide⟩ | 66, 1 => ⟨7, by decide⟩ | 66, 2 => ⟨10, by decide⟩ | 66, 3 => ⟨15, by decide⟩ | 66, 4 => ⟨12, by decide⟩ | 66, _ => ⟨2, by decide⟩
  | 67, 0 => ⟨21, by decide⟩ | 67, 1 => ⟨25, by decide⟩ | 67, 2 => ⟨23, by decide⟩ | 67, 3 => ⟨24, by decide⟩ | 67, 4 => ⟨28, by decide⟩ | 67, _ => ⟨22, by decide⟩
  | 68, 0 => ⟨1, by decide⟩ | 68, 1 => ⟨8, by decide⟩ | 68, 2 => ⟨13, by decide⟩ | 68, 3 => ⟨14, by decide⟩ | 68, 4 => ⟨22, by decide⟩ | 68, _ => ⟨3, by decide⟩
  | 69, 0 => ⟨0, by decide⟩ | 69, 1 => ⟨6, by decide⟩ | 69, 2 => ⟨24, by decide⟩ | 69, 3 => ⟨28, by decide⟩ | 69, 4 => ⟨22, by decide⟩ | 69, _ => ⟨3, by decide⟩
  | 70, 0 => ⟨0, by decide⟩ | 70, 1 => ⟨4, by decide⟩ | 70, 2 => ⟨7, by decide⟩ | 70, 3 => ⟨9, by decide⟩ | 70, 4 => ⟨21, by decide⟩ | 70, _ => ⟨3, by decide⟩
  | 71, 0 => ⟨0, by decide⟩ | 71, 1 => ⟨6, by decide⟩ | 71, 2 => ⟨20, by decide⟩ | 71, 3 => ⟨22, by decide⟩ | 71, 4 => ⟨14, by decide⟩ | 71, _ => ⟨2, by decide⟩
  | 72, 0 => ⟨4, by decide⟩ | 72, 1 => ⟨7, by decide⟩ | 72, 2 => ⟨8, by decide⟩ | 72, 3 => ⟨17, by decide⟩ | 72, 4 => ⟨15, by decide⟩ | 72, _ => ⟨5, by decide⟩
  | 73, 0 => ⟨1, by decide⟩ | 73, 1 => ⟨8, by decide⟩ | 73, 2 => ⟨18, by decide⟩ | 73, 3 => ⟨26, by decide⟩ | 73, 4 => ⟨21, by decide⟩ | 73, _ => ⟨3, by decide⟩
  | 74, 0 => ⟨4, by decide⟩ | 74, 1 => ⟨10, by decide⟩ | 74, 2 => ⟨17, by decide⟩ | 74, 3 => ⟨13, by decide⟩ | 74, 4 => ⟨12, by decide⟩ | 74, _ => ⟨5, by decide⟩
  | 75, 0 => ⟨10, by decide⟩ | 75, 1 => ⟨19, by decide⟩ | 75, 2 => ⟨30, by decide⟩ | 75, 3 => ⟨24, by decide⟩ | 75, 4 => ⟨23, by decide⟩ | 75, _ => ⟨11, by decide⟩
  | 76, 0 => ⟨7, by decide⟩ | 76, 1 => ⟨11, by decide⟩ | 76, 2 => ⟨27, by decide⟩ | 76, 3 => ⟨19, by decide⟩ | 76, 4 => ⟨17, by decide⟩ | 76, _ => ⟨8, by decide⟩
  | 77, 0 => ⟨8, by decide⟩ | 77, 1 => ⟨17, by decide⟩ | 77, 2 => ⟨10, by decide⟩ | 77, 3 => ⟨11, by decide⟩ | 77, 4 => ⟨25, by decide⟩ | 77, _ => ⟨9, by decide⟩
  | 78, 0 => ⟨12, by decide⟩ | 78, 1 => ⟨16, by decide⟩ | 78, 2 => ⟨30, by decide⟩ | 78, 3 => ⟨19, by decide⟩ | 78, 4 => ⟨17, by decide⟩ | 78, _ => ⟨13, by decide⟩
  | 79, 0 => ⟨12, by decide⟩ | 79, 1 => ⟨16, by decide⟩ | 79, 2 => ⟨28, by decide⟩ | 79, 3 => ⟨29, by decide⟩ | 79, 4 => ⟨18, by decide⟩ | 79, _ => ⟨13, by decide⟩
  | 80, 0 => ⟨4, by decide⟩ | 80, 1 => ⟨10, by decide⟩ | 80, 2 => ⟨19, by decide⟩ | 80, 3 => ⟨30, by decide⟩ | 80, 4 => ⟨24, by decide⟩ | 80, _ => ⟨6, by decide⟩
  | 81, 0 => ⟨12, by decide⟩ | 81, 1 => ⟨16, by decide⟩ | 81, 2 => ⟨24, by decide⟩ | 81, 3 => ⟨20, by decide⟩ | 81, 4 => ⟨22, by decide⟩ | 81, _ => ⟨14, by decide⟩
  | 82, 0 => ⟨10, by decide⟩ | 82, 1 => ⟨15, by decide⟩ | 82, 2 => ⟨16, by decide⟩ | 82, 3 => ⟨30, by decide⟩ | 82, 4 => ⟨27, by decide⟩ | 82, _ => ⟨11, by decide⟩
  | 83, 0 => ⟨0, by decide⟩ | 83, 1 => ⟨4, by decide⟩ | 83, 2 => ⟨7, by decide⟩ | 83, 3 => ⟨8, by decide⟩ | 83, 4 => ⟨13, by decide⟩ | 83, _ => ⟨2, by decide⟩
  | 84, 0 => ⟨0, by decide⟩ | 84, 1 => ⟨4, by decide⟩ | 84, 2 => ⟨10, by decide⟩ | 84, 3 => ⟨15, by decide⟩ | 84, 4 => ⟨12, by decide⟩ | 84, _ => ⟨2, by decide⟩
  | 85, 0 => ⟨1, by decide⟩ | 85, 1 => ⟨7, by decide⟩ | 85, 2 => ⟨11, by decide⟩ | 85, 3 => ⟨23, by decide⟩ | 85, 4 => ⟨20, by decide⟩ | 85, _ => ⟨3, by decide⟩
  | 86, 0 => ⟨8, by decide⟩ | 86, 1 => ⟨18, by decide⟩ | 86, 2 => ⟨31, by decide⟩ | 86, 3 => ⟨27, by decide⟩ | 86, 4 => ⟨25, by decide⟩ | 86, _ => ⟨9, by decide⟩
  | 87, 0 => ⟨7, by decide⟩ | 87, 1 => ⟨10, by decide⟩ | 87, 2 => ⟨15, by decide⟩ | 87, 3 => ⟨12, by decide⟩ | 87, 4 => ⟨13, by decide⟩ | 87, _ => ⟨8, by decide⟩
  | 88, 0 => ⟨17, by decide⟩ | 88, 1 => ⟨19, by decide⟩ | 88, 2 => ⟨30, by decide⟩ | 88, 3 => ⟨28, by decide⟩ | 88, 4 => ⟨29, by decide⟩ | 88, _ => ⟨18, by decide⟩
  | 89, 0 => ⟨1, by decide⟩ | 89, 1 => ⟨9, by decide⟩ | 89, 2 => ⟨26, by decide⟩ | 89, 3 => ⟨29, by decide⟩ | 89, 4 => ⟨22, by decide⟩ | 89, _ => ⟨3, by decide⟩
  | 90, 0 => ⟨13, by decide⟩ | 90, 1 => ⟨18, by decide⟩ | 90, 2 => ⟨26, by decide⟩ | 90, 3 => ⟨21, by decide⟩ | 90, 4 => ⟨22, by decide⟩ | 90, _ => ⟨14, by decide⟩
  | 91, 0 => ⟨0, by decide⟩ | 91, 1 => ⟨4, by decide⟩ | 91, 2 => ⟨11, by decide⟩ | 91, 3 => ⟨23, by decide⟩ | 91, 4 => ⟨20, by decide⟩ | 91, _ => ⟨3, by decide⟩
  | 92, 0 => ⟨0, by decide⟩ | 92, 1 => ⟨5, by decide⟩ | 92, 2 => ⟨12, by decide⟩ | 92, 3 => ⟨14, by decide⟩ | 92, 4 => ⟨22, by decide⟩ | 92, _ => ⟨3, by decide⟩
  | 93, 0 => ⟨8, by decide⟩ | 93, 1 => ⟨13, by decide⟩ | 93, 2 => ⟨14, by decide⟩ | 93, 3 => ⟨22, by decide⟩ | 93, 4 => ⟨21, by decide⟩ | 93, _ => ⟨9, by decide⟩
  | 94, 0 => ⟨21, by decide⟩ | 94, 1 => ⟨25, by decide⟩ | 94, 2 => ⟨27, by decide⟩ | 94, 3 => ⟨31, by decide⟩ | 94, 4 => ⟨29, by decide⟩ | 94, _ => ⟨22, by decide⟩
  | 95, 0 => ⟨5, by decide⟩ | 95, 1 => ⟨15, by decide⟩ | 95, 2 => ⟨10, by decide⟩ | 95, 3 => ⟨11, by decide⟩ | 95, 4 => ⟨23, by decide⟩ | 95, _ => ⟨6, by decide⟩
  | 96, 0 => ⟨15, by decide⟩ | 96, 1 => ⟨17, by decide⟩ | 96, 2 => ⟨18, by decide⟩ | 96, 3 => ⟨29, by decide⟩ | 96, 4 => ⟨28, by decide⟩ | 96, _ => ⟨16, by decide⟩
  | 97, 0 => ⟨5, by decide⟩ | 97, 1 => ⟨16, by decide⟩ | 97, 2 => ⟨30, by decide⟩ | 97, 3 => ⟨27, by decide⟩ | 97, 4 => ⟨23, by decide⟩ | 97, _ => ⟨6, by decide⟩
  | 98, 0 => ⟨7, by decide⟩ | 98, 1 => ⟨10, by decide⟩ | 98, 2 => ⟨17, by decide⟩ | 98, 3 => ⟨18, by decide⟩ | 98, 4 => ⟨26, by decide⟩ | 98, _ => ⟨9, by decide⟩
  | 99, 0 => ⟨10, by decide⟩ | 99, 1 => ⟨17, by decide⟩ | 99, 2 => ⟨18, by decide⟩ | 99, 3 => ⟨31, by decide⟩ | 99, 4 => ⟨27, by decide⟩ | 99, _ => ⟨11, by decide⟩
  | 100, 0 => ⟨5, by decide⟩ | 100, 1 => ⟨16, by decide⟩ | 100, 2 => ⟨28, by decide⟩ | 100, 3 => ⟨22, by decide⟩ | 100, 4 => ⟨20, by decide⟩ | 100, _ => ⟨6, by decide⟩
  | 101, 0 => ⟨15, by decide⟩ | 101, 1 => ⟨19, by decide⟩ | 101, 2 => ⟨27, by decide⟩ | 101, 3 => ⟨23, by decide⟩ | 101, 4 => ⟨24, by decide⟩ | 101, _ => ⟨16, by decide⟩
  | 102, 0 => ⟨1, by decide⟩ | 102, 1 => ⟨7, by decide⟩ | 102, 2 => ⟨10, by decide⟩ | 102, 3 => ⟨17, by decide⟩ | 102, 4 => ⟨13, by decide⟩ | 102, _ => ⟨2, by decide⟩
  | 103, 0 => ⟨1, by decide⟩ | 103, 1 => ⟨8, by decide⟩ | 103, 2 => ⟨17, by decide⟩ | 103, 3 => ⟨15, by decide⟩ | 103, 4 => ⟨12, by decide⟩ | 103, _ => ⟨2, by decide⟩
  | 104, 0 => ⟨0, by decide⟩ | 104, 1 => ⟨5, by decide⟩ | 104, 2 => ⟨15, by decide⟩ | 104, 3 => ⟨17, by decide⟩ | 104, 4 => ⟨13, by decide⟩ | 104, _ => ⟨2, by decide⟩
  | 105, 0 => ⟨2, by decide⟩ | 105, 1 => ⟨12, by decide⟩ | 105, 2 => ⟨5, by decide⟩ | 105, 3 => ⟨6, by decide⟩ | 105, 4 => ⟨20, by decide⟩ | 105, _ => ⟨3, by decide⟩
  | 106, 0 => ⟨12, by decide⟩ | 106, 1 => ⟨15, by decide⟩ | 106, 2 => ⟨19, by decide⟩ | 106, 3 => ⟨31, by decide⟩ | 106, 4 => ⟨29, by decide⟩ | 106, _ => ⟨14, by decide⟩
  | 107, 0 => ⟨7, by decide⟩ | 107, 1 => ⟨11, by decide⟩ | 107, 2 => ⟨23, by decide⟩ | 107, 3 => ⟨20, by decide⟩ | 107, 4 => ⟨21, by decide⟩ | 107, _ => ⟨9, by decide⟩
  | 108, 0 => ⟨0, by decide⟩ | 108, 1 => ⟨4, by decide⟩ | 108, 2 => ⟨11, by decide⟩ | 108, 3 => ⟨25, by decide⟩ | 108, 4 => ⟨9, by decide⟩ | 108, _ => ⟨1, by decide⟩
  | 109, 0 => ⟨4, by decide⟩ | 109, 1 => ⟨10, by decide⟩ | 109, 2 => ⟨19, by decide⟩ | 109, 3 => ⟨30, by decide⟩ | 109, 4 => ⟨16, by decide⟩ | 109, _ => ⟨5, by decide⟩
  | 110, 0 => ⟨1, by decide⟩ | 110, 1 => ⟨9, by decide⟩ | 110, 2 => ⟨21, by decide⟩ | 110, 3 => ⟨22, by decide⟩ | 110, 4 => ⟨14, by decide⟩ | 110, _ => ⟨2, by decide⟩
  | 111, 0 => ⟨0, by decide⟩ | 111, 1 => ⟨6, by decide⟩ | 111, 2 => ⟨23, by decide⟩ | 111, 3 => ⟨25, by decide⟩ | 111, 4 => ⟨21, by decide⟩ | 111, _ => ⟨3, by decide⟩
  | 112, 0 => ⟨4, by decide⟩ | 112, 1 => ⟨7, by decide⟩ | 112, 2 => ⟨9, by decide⟩ | 112, 3 => ⟨21, by decide⟩ | 112, 4 => ⟨20, by decide⟩ | 112, _ => ⟨6, by decide⟩
  | 113, 0 => ⟨0, by decide⟩ | 113, 1 => ⟨5, by decide⟩ | 113, 2 => ⟨16, by decide⟩ | 113, 3 => ⟨24, by decide⟩ | 113, 4 => ⟨20, by decide⟩ | 113, _ => ⟨3, by decide⟩
  | 114, 0 => ⟨1, by decide⟩ | 114, 1 => ⟨9, by decide⟩ | 114, 2 => ⟨26, by decide⟩ | 114, 3 => ⟨29, by decide⟩ | 114, 4 => ⟨14, by decide⟩ | 114, _ => ⟨2, by decide⟩
  | 115, 0 => ⟨13, by decide⟩ | 115, 1 => ⟨18, by decide⟩ | 115, 2 => ⟨31, by decide⟩ | 115, 3 => ⟨30, by decide⟩ | 115, 4 => ⟨28, by decide⟩ | 115, _ => ⟨14, by decide⟩
  | 116, 0 => ⟨0, by decide⟩ | 116, 1 => ⟨5, by decide⟩ | 116, 2 => ⟨16, by decide⟩ | 116, 3 => ⟨28, by decide⟩ | 116, 4 => ⟨14, by decide⟩ | 116, _ => ⟨2, by decide⟩
  | 117, 0 => ⟨10, by decide⟩ | 117, 1 => ⟨15, by decide⟩ | 117, 2 => ⟨16, by decide⟩ | 117, 3 => ⟨24, by decide⟩ | 117, 4 => ⟨23, by decide⟩ | 117, _ => ⟨11, by decide⟩
  | 118, 0 => ⟨0, by decide⟩ | 118, 1 => ⟨5, by decide⟩ | 118, 2 => ⟨16, by decide⟩ | 118, 3 => ⟨28, by decide⟩ | 118, 4 => ⟨22, by decide⟩ | 118, _ => ⟨3, by decide⟩
  | 119, 0 => ⟨20, by decide⟩ | 119, 1 => ⟨23, by decide⟩ | 119, 2 => ⟨27, by decide⟩ | 119, 3 => ⟨30, by decide⟩ | 119, 4 => ⟨28, by decide⟩ | 119, _ => ⟨22, by decide⟩
  | 120, 0 => ⟨1, by decide⟩ | 120, 1 => ⟨9, by decide⟩ | 120, 2 => ⟨26, by decide⟩ | 120, 3 => ⟨18, by decide⟩ | 120, 4 => ⟨13, by decide⟩ | 120, _ => ⟨2, by decide⟩
  | 121, 0 => ⟨4, by decide⟩ | 121, 1 => ⟨11, by decide⟩ | 121, 2 => ⟨27, by decide⟩ | 121, 3 => ⟨30, by decide⟩ | 121, 4 => ⟨16, by decide⟩ | 121, _ => ⟨5, by decide⟩
  | 122, 0 => ⟨4, by decide⟩ | 122, 1 => ⟨10, by decide⟩ | 122, 2 => ⟨19, by decide⟩ | 122, 3 => ⟨27, by decide⟩ | 122, 4 => ⟨23, by decide⟩ | 122, _ => ⟨6, by decide⟩
  | 123, 0 => ⟨1, by decide⟩ | 123, 1 => ⟨7, by decide⟩ | 123, 2 => ⟨11, by decide⟩ | 123, 3 => ⟨25, by decide⟩ | 123, 4 => ⟨21, by decide⟩ | 123, _ => ⟨3, by decide⟩
  | 124, 0 => ⟨4, by decide⟩ | 124, 1 => ⟨7, by decide⟩ | 124, 2 => ⟨8, by decide⟩ | 124, 3 => ⟨13, by decide⟩ | 124, 4 => ⟨12, by decide⟩ | 124, _ => ⟨5, by decide⟩
  | 125, 0 => ⟨0, by decide⟩ | 125, 1 => ⟨6, by decide⟩ | 125, 2 => ⟨20, by decide⟩ | 125, 3 => ⟨21, by decide⟩ | 125, 4 => ⟨9, by decide⟩ | 125, _ => ⟨1, by decide⟩
  | 126, 0 => ⟨13, by decide⟩ | 126, 1 => ⟨17, by decide⟩ | 126, 2 => ⟨15, by decide⟩ | 126, 3 => ⟨16, by decide⟩ | 126, 4 => ⟨28, by decide⟩ | 126, _ => ⟨14, by decide⟩
  | _, 0 => ⟨4, by decide⟩ | _, 1 => ⟨7, by decide⟩ | _, 2 => ⟨9, by decide⟩ | _, 3 => ⟨25, by decide⟩ | _, 4 => ⟨23, by decide⟩ | _, _ => ⟨6, by decide⟩

private lemma isQ3C6Free_q3Flip0 (q : Q3Bits) : isQ3C6Free (q3Flip0 q) = isQ3C6Free q := by
  simp only [isQ3C6Free, q3IsC6FreeBool, q3Flip0]
  have h0 : (!(q.e01 && q.e13 && q.e02 && q.e37 && q.e26 && q.e67)) = (!(q.e01 && q.e02 && q.e13 && q.e26 && q.e37 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h2 : (!(q.e01 && q.e15 && q.e02 && q.e23 && q.e37 && q.e57)) = (!(q.e01 && q.e02 && q.e15 && q.e23 && q.e37 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h3 : (!(q.e01 && q.e15 && q.e02 && q.e26 && q.e57 && q.e67)) = (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h4 : (!(q.e01 && q.e13 && q.e04 && q.e37 && q.e45 && q.e57)) = (!(q.e01 && q.e04 && q.e13 && q.e37 && q.e45 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h7 : (!(q.e23 && q.e37 && q.e26 && q.e45 && q.e57 && q.e46)) = (!(q.e23 && q.e26 && q.e37 && q.e45 && q.e46 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h9 : (!(q.e01 && q.e13 && q.e04 && q.e37 && q.e46 && q.e67)) = (!(q.e01 && q.e04 && q.e13 && q.e37 && q.e46 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h11 : (!(q.e01 && q.e15 && q.e04 && q.e57 && q.e46 && q.e67)) = (!(q.e01 && q.e04 && q.e15 && q.e46 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h12 : (!(q.e13 && q.e15 && q.e02 && q.e04 && q.e23 && q.e45)) = (!(q.e02 && q.e04 && q.e13 && q.e15 && q.e23 && q.e45)) := congrArg Bool.not (by ac_rfl)
  have h13 : (!(q.e01 && q.e13 && q.e04 && q.e23 && q.e26 && q.e46)) = (!(q.e01 && q.e04 && q.e13 && q.e23 && q.e26 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h14 : (!(q.e01 && q.e15 && q.e02 && q.e26 && q.e45 && q.e46)) = (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e45 && q.e46)) := congrArg Bool.not (by ac_rfl)
  rw [h0, h2, h3, h4, h7, h9, h11, h12, h13, h14]
  ac_rfl
private lemma isQ3C6Free_q3Swap01 (q : Q3Bits) : isQ3C6Free (q3Swap01 q) = isQ3C6Free q := by
  simp only [isQ3C6Free, q3IsC6FreeBool, q3Swap01]
  have h0 : (!(q.e02 && q.e01 && q.e23 && q.e15 && q.e37 && q.e57)) = (!(q.e01 && q.e02 && q.e15 && q.e23 && q.e37 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h2 : (!(q.e02 && q.e04 && q.e23 && q.e13 && q.e15 && q.e45)) = (!(q.e02 && q.e04 && q.e13 && q.e15 && q.e23 && q.e45)) := congrArg Bool.not (by ac_rfl)
  have h4 : (!(q.e02 && q.e01 && q.e26 && q.e15 && q.e46 && q.e45)) = (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e45 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h5 : (!(q.e23 && q.e26 && q.e13 && q.e15 && q.e67 && q.e57)) = (!(q.e13 && q.e15 && q.e23 && q.e26 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h6 : (!(q.e23 && q.e26 && q.e13 && q.e15 && q.e46 && q.e45)) = (!(q.e13 && q.e15 && q.e23 && q.e26 && q.e45 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h7 : (!(q.e13 && q.e15 && q.e37 && q.e46 && q.e45 && q.e67)) = (!(q.e13 && q.e15 && q.e37 && q.e45 && q.e46 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h8 : (!(q.e01 && q.e04 && q.e15 && q.e46 && q.e67 && q.e57)) = (!(q.e01 && q.e04 && q.e15 && q.e46 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h9 : (!(q.e02 && q.e01 && q.e26 && q.e15 && q.e67 && q.e57)) = (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h11 : (!(q.e02 && q.e04 && q.e26 && q.e45 && q.e67 && q.e57)) = (!(q.e02 && q.e04 && q.e26 && q.e45 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h12 : (!(q.e01 && q.e04 && q.e23 && q.e26 && q.e13 && q.e46)) = (!(q.e01 && q.e04 && q.e13 && q.e23 && q.e26 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h13 : (!(q.e02 && q.e01 && q.e26 && q.e13 && q.e37 && q.e67)) = (!(q.e01 && q.e02 && q.e13 && q.e26 && q.e37 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h15 : (!(q.e23 && q.e26 && q.e37 && q.e46 && q.e45 && q.e57)) = (!(q.e23 && q.e26 && q.e37 && q.e45 && q.e46 && q.e57)) := congrArg Bool.not (by ac_rfl)
  rw [h0, h2, h4, h5, h6, h7, h8, h9, h11, h12, h13, h15]
  ac_rfl
private lemma isQ3C6Free_q3Swap12 (q : Q3Bits) : isQ3C6Free (q3Swap12 q) = isQ3C6Free q := by
  simp only [isQ3C6Free, q3IsC6FreeBool, q3Swap12]
  have h1 : (!(q.e04 && q.e02 && q.e45 && q.e57 && q.e23 && q.e37)) = (!(q.e02 && q.e04 && q.e23 && q.e37 && q.e45 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h2 : (!(q.e01 && q.e02 && q.e15 && q.e45 && q.e46 && q.e26)) = (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e45 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h3 : (!(q.e01 && q.e02 && q.e15 && q.e57 && q.e26 && q.e67)) = (!(q.e01 && q.e02 && q.e15 && q.e26 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h4 : (!(q.e01 && q.e04 && q.e13 && q.e46 && q.e23 && q.e26)) = (!(q.e01 && q.e04 && q.e13 && q.e23 && q.e26 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h5 : (!(q.e15 && q.e13 && q.e45 && q.e46 && q.e37 && q.e67)) = (!(q.e13 && q.e15 && q.e37 && q.e45 && q.e46 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h6 : (!(q.e15 && q.e13 && q.e45 && q.e46 && q.e23 && q.e26)) = (!(q.e13 && q.e15 && q.e23 && q.e26 && q.e45 && q.e46)) := congrArg Bool.not (by ac_rfl)
  have h7 : (!(q.e45 && q.e46 && q.e57 && q.e23 && q.e26 && q.e37)) = (!(q.e23 && q.e26 && q.e37 && q.e45 && q.e46 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h8 : (!(q.e04 && q.e02 && q.e46 && q.e23 && q.e37 && q.e67)) = (!(q.e02 && q.e04 && q.e23 && q.e37 && q.e46 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h9 : (!(q.e01 && q.e04 && q.e13 && q.e46 && q.e37 && q.e67)) = (!(q.e01 && q.e04 && q.e13 && q.e37 && q.e46 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h10 : (!(q.e04 && q.e02 && q.e45 && q.e57 && q.e26 && q.e67)) = (!(q.e02 && q.e04 && q.e26 && q.e45 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  have h12 : (!(q.e04 && q.e02 && q.e15 && q.e13 && q.e45 && q.e23)) = (!(q.e02 && q.e04 && q.e13 && q.e15 && q.e23 && q.e45)) := congrArg Bool.not (by ac_rfl)
  have h13 : (!(q.e01 && q.e04 && q.e13 && q.e45 && q.e57 && q.e37)) = (!(q.e01 && q.e04 && q.e13 && q.e37 && q.e45 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h14 : (!(q.e01 && q.e02 && q.e15 && q.e57 && q.e23 && q.e37)) = (!(q.e01 && q.e02 && q.e15 && q.e23 && q.e37 && q.e57)) := congrArg Bool.not (by ac_rfl)
  have h15 : (!(q.e15 && q.e13 && q.e57 && q.e23 && q.e26 && q.e67)) = (!(q.e13 && q.e15 && q.e23 && q.e26 && q.e57 && q.e67)) := congrArg Bool.not (by ac_rfl)
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h12, h13, h14, h15]
  ac_rfl
private lemma evalQ3G_q3Flip0 (q : Q3Bits) : evalQ3G (q3Flip0 q) = evalQ3G q := by
  unfold evalQ3G q3LocalBool q3UngaugedBool q3Flip0
  ring
private lemma evalQ3G_q3Swap01 (q : Q3Bits) : evalQ3G (q3Swap01 q) = evalQ3G q := by
  unfold evalQ3G q3LocalBool q3UngaugedBool q3Swap01
  rw [lam23_swap01 q.e02 q.e01 q.e04 q.e23 q.e13 q.e26 q.e46 q.e15 q.e45]
  rw [lam23_swap01 q.e02 q.e23 q.e26 q.e01 q.e13 q.e04 q.e46 q.e37 q.e67]
  rw [lam23_swap01 q.e13 q.e01 q.e15 q.e23 q.e02 q.e37 q.e57 q.e04 q.e45]
  rw [lam23_swap01 q.e13 q.e23 q.e37 q.e01 q.e02 q.e15 q.e57 q.e26 q.e67]
  rw [lam23_swap01 q.e46 q.e45 q.e04 q.e67 q.e57 q.e26 q.e02 q.e15 q.e01]
  rw [lam23_swap01 q.e46 q.e67 q.e26 q.e45 q.e57 q.e04 q.e02 q.e37 q.e23]
  rw [lam23_swap01 q.e57 q.e45 q.e15 q.e67 q.e46 q.e37 q.e13 q.e04 q.e01]
  rw [lam23_swap01 q.e57 q.e67 q.e37 q.e45 q.e46 q.e15 q.e13 q.e26 q.e23]
  ring
private lemma evalQ3G_q3Swap12 (q : Q3Bits) : evalQ3G (q3Swap12 q) = evalQ3G q := by
  unfold evalQ3G q3LocalBool q3UngaugedBool q3Swap12
  rw [lam23_swap12 q.e01 q.e04 q.e02 q.e15 q.e45 q.e13 q.e23 q.e46 q.e26]
  rw [lam23_swap12 q.e01 q.e15 q.e13 q.e04 q.e45 q.e02 q.e23 q.e57 q.e37]
  rw [lam23_swap12 q.e45 q.e04 q.e46 q.e15 q.e01 q.e57 q.e67 q.e02 q.e26]
  rw [lam23_swap12 q.e45 q.e15 q.e57 q.e04 q.e01 q.e46 q.e67 q.e13 q.e37]
  rw [lam23_swap12 q.e23 q.e26 q.e02 q.e37 q.e67 q.e13 q.e01 q.e46 q.e04]
  rw [lam23_swap12 q.e23 q.e37 q.e13 q.e26 q.e67 q.e02 q.e01 q.e57 q.e15]
  rw [lam23_swap12 q.e67 q.e26 q.e46 q.e37 q.e23 q.e57 q.e45 q.e02 q.e04]
  rw [lam23_swap12 q.e67 q.e37 q.e57 q.e26 q.e23 q.e46 q.e45 q.e13 q.e15]
  ring

private lemma evalQ3U_q3Flip0 (q : Q3Bits) : evalQ3U (q3Flip0 q) = evalQ3U q := by
  unfold evalQ3U q3UngaugedBool q3Flip0; ring
private lemma evalQ3U_q3Swap01 (q : Q3Bits) : evalQ3U (q3Swap01 q) = evalQ3U q := by
  unfold evalQ3U q3UngaugedBool q3Swap01; ring
private lemma evalQ3U_q3Swap12 (q : Q3Bits) : evalQ3U (q3Swap12 q) = evalQ3U q := by
  unfold evalQ3U q3UngaugedBool q3Swap12; ring

private lemma evalQ3Fast_q3Flip0 (q : Q3Bits) : evalQ3Fast (q3Flip0 q) = evalQ3Fast q := by
  have h := evalQ3Fast_eq (q3Flip0 q); have h' := evalQ3Fast_eq q
  rw [isQ3C6Free_q3Flip0, evalQ3G_q3Flip0] at h; omega
private lemma evalQ3Fast_q3Swap01 (q : Q3Bits) : evalQ3Fast (q3Swap01 q) = evalQ3Fast q := by
  have h := evalQ3Fast_eq (q3Swap01 q); have h' := evalQ3Fast_eq q
  rw [isQ3C6Free_q3Swap01, evalQ3G_q3Swap01] at h; omega
private lemma evalQ3Fast_q3Swap12 (q : Q3Bits) : evalQ3Fast (q3Swap12 q) = evalQ3Fast q := by
  have h := evalQ3Fast_eq (q3Swap12 q); have h' := evalQ3Fast_eq q
  rw [isQ3C6Free_q3Swap12, evalQ3G_q3Swap12] at h; omega

private lemma b4Pair_comm (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair c d cd dc a b ab ba := by unfold b4Pair; ring
private lemma b4Pair_swapL (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair b a ba ab c d cd dc := by simp only [b4Pair, rcIdx_swap a b ab ba]
private lemma b4Pair_swapR (a b ab ba c d cd dc : Bool) :
    b4Pair a b ab ba c d cd dc = b4Pair a b ab ba d c dc cd := by simp only [b4Pair, rcIdx_swap c d cd dc]
private lemma q2Term_swapCD (a b ab ba c0 ca cb ck cl d0 da db dk dl : Bool) :
    q2Term a b ab ba c0 ca cb ck cl d0 da db dk dl =
      q2Term a b ab ba d0 da db dk dl c0 ca cb ck cl := by
  unfold q2Term; dsimp only; split_ifs <;> ring

private lemma evalB2U_b2Swap01 (b : B2Bits) : evalB2U (b2Swap01 b) = evalB2U b := by
  unfold evalB2U b2UngaugedBool b2Swap01
  rw [b4Pair_swapL b.b02 b.b01 b.b23 b.b13 b.b04 b.b08 b.b4c b.b8c]
  rw [b4Pair_comm b.b02 b.b04 b.b26 b.b46 b.b01 b.b08 b.b19 b.b89]
  rw [b4Pair_comm b.b02 b.b08 b.b2a b.b8a b.b01 b.b04 b.b15 b.b45]
  rw [q2Term_swapCD b.b04 b.b08 b.b4c b.b8c b.b02 b.b46 b.b8a b.b26 b.b2a b.b01 b.b45 b.b89 b.b15 b.b19]
  rw [q2Term_swapCD b.b08 b.b04 b.b8c b.b4c b.b02 b.b8a b.b46 b.b2a b.b26 b.b01 b.b89 b.b45 b.b19 b.b15]
  ring
private lemma evalB2U_b2Swap12 (b : B2Bits) : evalB2U (b2Swap12 b) = evalB2U b := by
  unfold evalB2U b2UngaugedBool b2Swap12
  rw [b4Pair_swapR b.b01 b.b08 b.b19 b.b89 b.b04 b.b02 b.b46 b.b26]
  rw [q2Term_swapCD b.b01 b.b08 b.b19 b.b89 b.b04 b.b15 b.b8c b.b45 b.b4c b.b02 b.b13 b.b8a b.b23 b.b2a]
  rw [q2Term_swapCD b.b08 b.b01 b.b89 b.b19 b.b04 b.b8c b.b15 b.b4c b.b45 b.b02 b.b8a b.b13 b.b2a b.b23]
  ring
private lemma evalB2U_b2Swap23 (b : B2Bits) : evalB2U (b2Swap23 b) = evalB2U b := by
  unfold evalB2U b2UngaugedBool b2Swap23
  rw [b4Pair_swapR b.b01 b.b02 b.b13 b.b23 b.b08 b.b04 b.b8c b.b4c]
  rw [q2Term_swapCD b.b01 b.b02 b.b13 b.b23 b.b08 b.b19 b.b2a b.b89 b.b8a b.b04 b.b15 b.b26 b.b45 b.b46]
  rw [q2Term_swapCD b.b02 b.b01 b.b23 b.b13 b.b08 b.b2a b.b19 b.b8a b.b89 b.b04 b.b26 b.b15 b.b46 b.b45]
  ring


private def in6B (x a0 a1 a2 a3 a4 a5 : Fin 32) : Bool :=
  decide (x = a0) || decide (x = a1) || decide (x = a2) || decide (x = a3) || decide (x = a4) || decide (x = a5)

private lemma mem_of_in6B {g : Q4Bits} {x a0 a1 a2 a3 a4 a5 : Fin 32}
    (hin : in6B x a0 a1 a2 a3 a4 a5 = true)
    (h0 : getQ4E g a0 = true) (h1 : getQ4E g a1 = true) (h2 : getQ4E g a2 = true)
    (h3 : getQ4E g a3 = true) (h4 : getQ4E g a4 = true) (h5 : getQ4E g a5 = true) :
    getQ4E g x = true := by
  simp only [in6B, Bool.or_eq_true, decide_eq_true_eq] at hin
  rcases hin with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) <;> assumption

private def allFin128 (P : Fin 128 → Bool) : Bool :=
  (List.range 128).all fun i => if h : i < 128 then P ⟨i, h⟩ else true

private lemma allFin128_ok {P : Fin 128 → Bool} (h : allFin128 P = true) (x : Fin 128) :
    P x = true := by
  have hx : x.val ∈ List.range 128 := List.mem_range.mpr x.isLt
  simp only [allFin128, List.all_eq_true] at h
  have h1 := h x.val hx; simp [x.isLt] at h1; exact h1

private def checkQ4EdgeC6Perm (ePerm : Fin 32 → Fin 32) (cPerm : Fin 128 → Fin 128) : Bool :=
  allFin128 fun cid =>
    let (a0, a1, a2, a3, a4, a5) := c6CyclesQ4 cid
    let (b0, b1, b2, b3, b4, b5) := c6CyclesQ4 (cPerm cid)
    in6B b0 (ePerm a0) (ePerm a1) (ePerm a2) (ePerm a3) (ePerm a4) (ePerm a5) &&
    in6B b1 (ePerm a0) (ePerm a1) (ePerm a2) (ePerm a3) (ePerm a4) (ePerm a5) &&
    in6B b2 (ePerm a0) (ePerm a1) (ePerm a2) (ePerm a3) (ePerm a4) (ePerm a5) &&
    in6B b3 (ePerm a0) (ePerm a1) (ePerm a2) (ePerm a3) (ePerm a4) (ePerm a5) &&
    in6B b4 (ePerm a0) (ePerm a1) (ePerm a2) (ePerm a3) (ePerm a4) (ePerm a5) &&
    in6B b5 (ePerm a0) (ePerm a1) (ePerm a2) (ePerm a3) (ePerm a4) (ePerm a5)

private lemma isQ4C6Free_of_perm (τ : Q4Bits → Q4Bits) (ePerm : Fin 32 → Fin 32) (cPerm : Fin 128 → Fin 128)
    (he : ∀ g (e : Fin 32), getQ4E (τ g) e = getQ4E g (ePerm e))
    (hchk : checkQ4EdgeC6Perm ePerm cPerm = true)
    (g : Q4Bits) (hc : isQ4C6Free g) : isQ4C6Free (τ g) := by
  intro cid
  have hm := allFin128_ok hchk cid; dsimp only at hm
  rcases ha : c6CyclesQ4 cid with ⟨a0, a1, a2, a3, a4, a5⟩
  rcases hb : c6CyclesQ4 (cPerm cid) with ⟨b0, b1, b2, b3, b4, b5⟩
  rw [ha, hb] at hm; dsimp only at hm ⊢; simp only [Bool.and_eq_true] at hm
  rcases hm with ⟨⟨⟨⟨⟨m0, m1⟩, m2⟩, m3⟩, m4⟩, m5⟩
  rintro ⟨e0, e1, e2, e3, e4, e5⟩
  rw [he] at e0 e1 e2 e3 e4 e5
  have hbad := hc (cPerm cid); rw [hb] at hbad
  exact hbad ⟨mem_of_in6B m0 e0 e1 e2 e3 e4 e5, mem_of_in6B m1 e0 e1 e2 e3 e4 e5,
    mem_of_in6B m2 e0 e1 e2 e3 e4 e5, mem_of_in6B m3 e0 e1 e2 e3 e4 e5,
    mem_of_in6B m4 e0 e1 e2 e3 e4 e5, mem_of_in6B m5 e0 e1 e2 e3 e4 e5⟩

private lemma getQ4E_flip0 (g : Q4Bits) (e : Fin 32) : getQ4E (q4Flip0 g) e = getQ4E g (q4EdgePerm_flip0 e) := by fin_cases e <;> rfl
private lemma getQ4E_swap01 (g : Q4Bits) (e : Fin 32) : getQ4E (q4Swap01 g) e = getQ4E g (q4EdgePerm_swap01 e) := by fin_cases e <;> rfl
private lemma getQ4E_swap12 (g : Q4Bits) (e : Fin 32) : getQ4E (q4Swap12 g) e = getQ4E g (q4EdgePerm_swap12 e) := by fin_cases e <;> rfl
private lemma getQ4E_swap23 (g : Q4Bits) (e : Fin 32) : getQ4E (q4Swap23 g) e = getQ4E g (q4EdgePerm_swap23 e) := by fin_cases e <;> rfl

private lemma chkPerm_flip0 : checkQ4EdgeC6Perm q4EdgePerm_flip0 c6Perm_flip0 = true := by decide
private lemma chkPerm_swap01 : checkQ4EdgeC6Perm q4EdgePerm_swap01 c6Perm_swap01 = true := by decide
private lemma chkPerm_swap12 : checkQ4EdgeC6Perm q4EdgePerm_swap12 c6Perm_swap12 = true := by decide
private lemma chkPerm_swap23 : checkQ4EdgeC6Perm q4EdgePerm_swap23 c6Perm_swap23 = true := by decide

private lemma isQ4C6Free_flip0 {g : Q4Bits} (hc : isQ4C6Free g) : isQ4C6Free (q4Flip0 g) :=
  isQ4C6Free_of_perm q4Flip0 q4EdgePerm_flip0 c6Perm_flip0 getQ4E_flip0 chkPerm_flip0 g hc
private lemma isQ4C6Free_swap01 {g : Q4Bits} (hc : isQ4C6Free g) : isQ4C6Free (q4Swap01 g) :=
  isQ4C6Free_of_perm q4Swap01 q4EdgePerm_swap01 c6Perm_swap01 getQ4E_swap01 chkPerm_swap01 g hc
private lemma isQ4C6Free_swap12 {g : Q4Bits} (hc : isQ4C6Free g) : isQ4C6Free (q4Swap12 g) :=
  isQ4C6Free_of_perm q4Swap12 q4EdgePerm_swap12 c6Perm_swap12 getQ4E_swap12 chkPerm_swap12 g hc
private lemma isQ4C6Free_swap23 {g : Q4Bits} (hc : isQ4C6Free g) : isQ4C6Free (q4Swap23 g) :=
  isQ4C6Free_of_perm q4Swap23 q4EdgePerm_swap23 c6Perm_swap23 getQ4E_swap23 chkPerm_swap23 g hc

private lemma extractFacet_flip0 (g : Q4Bits) :
    extractFacetQ3 0 (q4Flip0 g) = extractFacetQ3 1 g ∧
    extractFacetQ3 1 (q4Flip0 g) = extractFacetQ3 0 g ∧
    extractFacetQ3 2 (q4Flip0 g) = q3Flip0 (extractFacetQ3 2 g) ∧
    extractFacetQ3 3 (q4Flip0 g) = q3Flip0 (extractFacetQ3 3 g) ∧
    extractFacetQ3 4 (q4Flip0 g) = q3Flip0 (extractFacetQ3 4 g) ∧
    extractFacetQ3 5 (q4Flip0 g) = q3Flip0 (extractFacetQ3 5 g) ∧
    extractFacetQ3 6 (q4Flip0 g) = q3Flip0 (extractFacetQ3 6 g) ∧
    extractFacetQ3 7 (q4Flip0 g) = q3Flip0 (extractFacetQ3 7 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractFacet_swap01 (g : Q4Bits) :
    extractFacetQ3 0 (q4Swap01 g) = extractFacetQ3 2 g ∧
    extractFacetQ3 1 (q4Swap01 g) = extractFacetQ3 3 g ∧
    extractFacetQ3 2 (q4Swap01 g) = extractFacetQ3 0 g ∧
    extractFacetQ3 3 (q4Swap01 g) = extractFacetQ3 1 g ∧
    extractFacetQ3 4 (q4Swap01 g) = q3Swap01 (extractFacetQ3 4 g) ∧
    extractFacetQ3 5 (q4Swap01 g) = q3Swap01 (extractFacetQ3 5 g) ∧
    extractFacetQ3 6 (q4Swap01 g) = q3Swap01 (extractFacetQ3 6 g) ∧
    extractFacetQ3 7 (q4Swap01 g) = q3Swap01 (extractFacetQ3 7 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractFacet_swap12 (g : Q4Bits) :
    extractFacetQ3 0 (q4Swap12 g) = q3Swap01 (extractFacetQ3 0 g) ∧
    extractFacetQ3 1 (q4Swap12 g) = q3Swap01 (extractFacetQ3 1 g) ∧
    extractFacetQ3 2 (q4Swap12 g) = extractFacetQ3 4 g ∧
    extractFacetQ3 3 (q4Swap12 g) = extractFacetQ3 5 g ∧
    extractFacetQ3 4 (q4Swap12 g) = extractFacetQ3 2 g ∧
    extractFacetQ3 5 (q4Swap12 g) = extractFacetQ3 3 g ∧
    extractFacetQ3 6 (q4Swap12 g) = q3Swap12 (extractFacetQ3 6 g) ∧
    extractFacetQ3 7 (q4Swap12 g) = q3Swap12 (extractFacetQ3 7 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractFacet_swap23 (g : Q4Bits) :
    extractFacetQ3 0 (q4Swap23 g) = q3Swap12 (extractFacetQ3 0 g) ∧
    extractFacetQ3 1 (q4Swap23 g) = q3Swap12 (extractFacetQ3 1 g) ∧
    extractFacetQ3 2 (q4Swap23 g) = q3Swap12 (extractFacetQ3 2 g) ∧
    extractFacetQ3 3 (q4Swap23 g) = q3Swap12 (extractFacetQ3 3 g) ∧
    extractFacetQ3 4 (q4Swap23 g) = extractFacetQ3 6 g ∧
    extractFacetQ3 5 (q4Swap23 g) = extractFacetQ3 7 g ∧
    extractFacetQ3 6 (q4Swap23 g) = extractFacetQ3 4 g ∧
    extractFacetQ3 7 (q4Swap23 g) = extractFacetQ3 5 g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractBall_flip0 (g : Q4Bits) :
    extractBallB2 0 (q4Flip0 g) = extractBallB2 1 g ∧
    extractBallB2 1 (q4Flip0 g) = extractBallB2 0 g ∧
    extractBallB2 2 (q4Flip0 g) = extractBallB2 3 g ∧
    extractBallB2 3 (q4Flip0 g) = extractBallB2 2 g ∧
    extractBallB2 4 (q4Flip0 g) = extractBallB2 5 g ∧
    extractBallB2 5 (q4Flip0 g) = extractBallB2 4 g ∧
    extractBallB2 6 (q4Flip0 g) = extractBallB2 7 g ∧
    extractBallB2 7 (q4Flip0 g) = extractBallB2 6 g ∧
    extractBallB2 8 (q4Flip0 g) = extractBallB2 9 g ∧
    extractBallB2 9 (q4Flip0 g) = extractBallB2 8 g ∧
    extractBallB2 10 (q4Flip0 g) = extractBallB2 11 g ∧
    extractBallB2 11 (q4Flip0 g) = extractBallB2 10 g ∧
    extractBallB2 12 (q4Flip0 g) = extractBallB2 13 g ∧
    extractBallB2 13 (q4Flip0 g) = extractBallB2 12 g ∧
    extractBallB2 14 (q4Flip0 g) = extractBallB2 15 g ∧
    extractBallB2 15 (q4Flip0 g) = extractBallB2 14 g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractBall_swap01 (g : Q4Bits) :
    extractBallB2 0 (q4Swap01 g) = b2Swap01 (extractBallB2 0 g) ∧
    extractBallB2 1 (q4Swap01 g) = b2Swap01 (extractBallB2 2 g) ∧
    extractBallB2 2 (q4Swap01 g) = b2Swap01 (extractBallB2 1 g) ∧
    extractBallB2 3 (q4Swap01 g) = b2Swap01 (extractBallB2 3 g) ∧
    extractBallB2 4 (q4Swap01 g) = b2Swap01 (extractBallB2 4 g) ∧
    extractBallB2 5 (q4Swap01 g) = b2Swap01 (extractBallB2 6 g) ∧
    extractBallB2 6 (q4Swap01 g) = b2Swap01 (extractBallB2 5 g) ∧
    extractBallB2 7 (q4Swap01 g) = b2Swap01 (extractBallB2 7 g) ∧
    extractBallB2 8 (q4Swap01 g) = b2Swap01 (extractBallB2 8 g) ∧
    extractBallB2 9 (q4Swap01 g) = b2Swap01 (extractBallB2 10 g) ∧
    extractBallB2 10 (q4Swap01 g) = b2Swap01 (extractBallB2 9 g) ∧
    extractBallB2 11 (q4Swap01 g) = b2Swap01 (extractBallB2 11 g) ∧
    extractBallB2 12 (q4Swap01 g) = b2Swap01 (extractBallB2 12 g) ∧
    extractBallB2 13 (q4Swap01 g) = b2Swap01 (extractBallB2 14 g) ∧
    extractBallB2 14 (q4Swap01 g) = b2Swap01 (extractBallB2 13 g) ∧
    extractBallB2 15 (q4Swap01 g) = b2Swap01 (extractBallB2 15 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractBall_swap12 (g : Q4Bits) :
    extractBallB2 0 (q4Swap12 g) = b2Swap12 (extractBallB2 0 g) ∧
    extractBallB2 1 (q4Swap12 g) = b2Swap12 (extractBallB2 1 g) ∧
    extractBallB2 2 (q4Swap12 g) = b2Swap12 (extractBallB2 4 g) ∧
    extractBallB2 3 (q4Swap12 g) = b2Swap12 (extractBallB2 5 g) ∧
    extractBallB2 4 (q4Swap12 g) = b2Swap12 (extractBallB2 2 g) ∧
    extractBallB2 5 (q4Swap12 g) = b2Swap12 (extractBallB2 3 g) ∧
    extractBallB2 6 (q4Swap12 g) = b2Swap12 (extractBallB2 6 g) ∧
    extractBallB2 7 (q4Swap12 g) = b2Swap12 (extractBallB2 7 g) ∧
    extractBallB2 8 (q4Swap12 g) = b2Swap12 (extractBallB2 8 g) ∧
    extractBallB2 9 (q4Swap12 g) = b2Swap12 (extractBallB2 9 g) ∧
    extractBallB2 10 (q4Swap12 g) = b2Swap12 (extractBallB2 12 g) ∧
    extractBallB2 11 (q4Swap12 g) = b2Swap12 (extractBallB2 13 g) ∧
    extractBallB2 12 (q4Swap12 g) = b2Swap12 (extractBallB2 10 g) ∧
    extractBallB2 13 (q4Swap12 g) = b2Swap12 (extractBallB2 11 g) ∧
    extractBallB2 14 (q4Swap12 g) = b2Swap12 (extractBallB2 14 g) ∧
    extractBallB2 15 (q4Swap12 g) = b2Swap12 (extractBallB2 15 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractBall_swap23 (g : Q4Bits) :
    extractBallB2 0 (q4Swap23 g) = b2Swap23 (extractBallB2 0 g) ∧
    extractBallB2 1 (q4Swap23 g) = b2Swap23 (extractBallB2 1 g) ∧
    extractBallB2 2 (q4Swap23 g) = b2Swap23 (extractBallB2 2 g) ∧
    extractBallB2 3 (q4Swap23 g) = b2Swap23 (extractBallB2 3 g) ∧
    extractBallB2 4 (q4Swap23 g) = b2Swap23 (extractBallB2 8 g) ∧
    extractBallB2 5 (q4Swap23 g) = b2Swap23 (extractBallB2 9 g) ∧
    extractBallB2 6 (q4Swap23 g) = b2Swap23 (extractBallB2 10 g) ∧
    extractBallB2 7 (q4Swap23 g) = b2Swap23 (extractBallB2 11 g) ∧
    extractBallB2 8 (q4Swap23 g) = b2Swap23 (extractBallB2 4 g) ∧
    extractBallB2 9 (q4Swap23 g) = b2Swap23 (extractBallB2 5 g) ∧
    extractBallB2 10 (q4Swap23 g) = b2Swap23 (extractBallB2 6 g) ∧
    extractBallB2 11 (q4Swap23 g) = b2Swap23 (extractBallB2 7 g) ∧
    extractBallB2 12 (q4Swap23 g) = b2Swap23 (extractBallB2 12 g) ∧
    extractBallB2 13 (q4Swap23 g) = b2Swap23 (extractBallB2 13 g) ∧
    extractBallB2 14 (q4Swap23 g) = b2Swap23 (extractBallB2 14 g) ∧
    extractBallB2 15 (q4Swap23 g) = b2Swap23 (extractBallB2 15 g) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma q4ScoreUngauged_flip0 (g : Q4Bits) :
    q4ScoreUngauged (q4Flip0 g) = q4ScoreUngauged g := by
  unfold q4ScoreUngauged
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, add_assoc]
  rcases extractFacet_flip0 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  rw [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]; simp only [evalQ3U_q3Flip0]
  rcases extractBall_flip0 g with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15]; ring

private lemma q4ScoreUngauged_swap01 (g : Q4Bits) :
    q4ScoreUngauged (q4Swap01 g) = q4ScoreUngauged g := by
  unfold q4ScoreUngauged
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, add_assoc]
  rcases extractFacet_swap01 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  rw [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]; simp only [evalQ3U_q3Swap01]
  rcases extractBall_swap01 g with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15]
  simp only [evalB2U_b2Swap01]; ring

private lemma q4ScoreUngauged_swap12 (g : Q4Bits) :
    q4ScoreUngauged (q4Swap12 g) = q4ScoreUngauged g := by
  unfold q4ScoreUngauged
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, add_assoc]
  rcases extractFacet_swap12 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  rw [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]; simp only [evalQ3U_q3Swap01, evalQ3U_q3Swap12]
  rcases extractBall_swap12 g with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15]
  simp only [evalB2U_b2Swap12]; ring

private lemma q4ScoreUngauged_swap23 (g : Q4Bits) :
    q4ScoreUngauged (q4Swap23 g) = q4ScoreUngauged g := by
  unfold q4ScoreUngauged
  rw [Fin.sum_univ_eight, Fin.sum_univ_eight]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, add_assoc]
  rcases extractFacet_swap23 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  rw [hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]; simp only [evalQ3U_q3Swap12]
  rcases extractBall_swap23 g with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15⟩
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15]
  simp only [evalB2U_b2Swap23]; ring

private lemma facet_perm_flip0 (fk : Fin 8) (g : Q4Bits) :
    ∃ fk' : Fin 8, evalQ3Fast (extractFacetQ3 fk (q4Flip0 g)) = evalQ3Fast (extractFacetQ3 fk' g) := by
  rcases extractFacet_flip0 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  fin_cases fk
  · exact ⟨1, congrArg evalQ3Fast hf0⟩
  · exact ⟨0, congrArg evalQ3Fast hf1⟩
  · exact ⟨2, (congrArg evalQ3Fast hf2).trans (evalQ3Fast_q3Flip0 _)⟩
  · exact ⟨3, (congrArg evalQ3Fast hf3).trans (evalQ3Fast_q3Flip0 _)⟩
  · exact ⟨4, (congrArg evalQ3Fast hf4).trans (evalQ3Fast_q3Flip0 _)⟩
  · exact ⟨5, (congrArg evalQ3Fast hf5).trans (evalQ3Fast_q3Flip0 _)⟩
  · exact ⟨6, (congrArg evalQ3Fast hf6).trans (evalQ3Fast_q3Flip0 _)⟩
  · exact ⟨7, (congrArg evalQ3Fast hf7).trans (evalQ3Fast_q3Flip0 _)⟩

private lemma facet_perm_swap01 (fk : Fin 8) (g : Q4Bits) :
    ∃ fk' : Fin 8, evalQ3Fast (extractFacetQ3 fk (q4Swap01 g)) = evalQ3Fast (extractFacetQ3 fk' g) := by
  rcases extractFacet_swap01 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  fin_cases fk
  · exact ⟨2, congrArg evalQ3Fast hf0⟩
  · exact ⟨3, congrArg evalQ3Fast hf1⟩
  · exact ⟨0, congrArg evalQ3Fast hf2⟩
  · exact ⟨1, congrArg evalQ3Fast hf3⟩
  · exact ⟨4, (congrArg evalQ3Fast hf4).trans (evalQ3Fast_q3Swap01 _)⟩
  · exact ⟨5, (congrArg evalQ3Fast hf5).trans (evalQ3Fast_q3Swap01 _)⟩
  · exact ⟨6, (congrArg evalQ3Fast hf6).trans (evalQ3Fast_q3Swap01 _)⟩
  · exact ⟨7, (congrArg evalQ3Fast hf7).trans (evalQ3Fast_q3Swap01 _)⟩

private lemma facet_perm_swap12 (fk : Fin 8) (g : Q4Bits) :
    ∃ fk' : Fin 8, evalQ3Fast (extractFacetQ3 fk (q4Swap12 g)) = evalQ3Fast (extractFacetQ3 fk' g) := by
  rcases extractFacet_swap12 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  fin_cases fk
  · exact ⟨0, (congrArg evalQ3Fast hf0).trans (evalQ3Fast_q3Swap01 _)⟩
  · exact ⟨1, (congrArg evalQ3Fast hf1).trans (evalQ3Fast_q3Swap01 _)⟩
  · exact ⟨4, congrArg evalQ3Fast hf2⟩
  · exact ⟨5, congrArg evalQ3Fast hf3⟩
  · exact ⟨2, congrArg evalQ3Fast hf4⟩
  · exact ⟨3, congrArg evalQ3Fast hf5⟩
  · exact ⟨6, (congrArg evalQ3Fast hf6).trans (evalQ3Fast_q3Swap12 _)⟩
  · exact ⟨7, (congrArg evalQ3Fast hf7).trans (evalQ3Fast_q3Swap12 _)⟩

private lemma facet_perm_swap23 (fk : Fin 8) (g : Q4Bits) :
    ∃ fk' : Fin 8, evalQ3Fast (extractFacetQ3 fk (q4Swap23 g)) = evalQ3Fast (extractFacetQ3 fk' g) := by
  rcases extractFacet_swap23 g with ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩
  fin_cases fk
  · exact ⟨0, (congrArg evalQ3Fast hf0).trans (evalQ3Fast_q3Swap12 _)⟩
  · exact ⟨1, (congrArg evalQ3Fast hf1).trans (evalQ3Fast_q3Swap12 _)⟩
  · exact ⟨2, (congrArg evalQ3Fast hf2).trans (evalQ3Fast_q3Swap12 _)⟩
  · exact ⟨3, (congrArg evalQ3Fast hf3).trans (evalQ3Fast_q3Swap12 _)⟩
  · exact ⟨6, congrArg evalQ3Fast hf4⟩
  · exact ⟨7, congrArg evalQ3Fast hf5⟩
  · exact ⟨4, congrArg evalQ3Fast hf6⟩
  · exact ⟨5, congrArg evalQ3Fast hf7⟩

private lemma isQ4C6Free_word4 (w : List Aut4Gen) {g : Q4Bits} (hc : isQ4C6Free g) :
    isQ4C6Free (applyWord4 w g) := by
  induction w with
  | nil => exact hc
  | cons op ws ih => cases op with
    | f0 => exact isQ4C6Free_flip0 ih
    | s01 => exact isQ4C6Free_swap01 ih
    | s12 => exact isQ4C6Free_swap12 ih
    | s23 => exact isQ4C6Free_swap23 ih

private lemma q4ScoreUngauged_word4 (w : List Aut4Gen) (g : Q4Bits) :
    q4ScoreUngauged (applyWord4 w g) = q4ScoreUngauged g := by
  induction w with
  | nil => rfl
  | cons op ws ih => cases op with
    | f0 => simpa [applyWord4, applyGen4, q4ScoreUngauged_flip0] using ih
    | s01 => simpa [applyWord4, applyGen4, q4ScoreUngauged_swap01] using ih
    | s12 => simpa [applyWord4, applyGen4, q4ScoreUngauged_swap12] using ih
    | s23 => simpa [applyWord4, applyGen4, q4ScoreUngauged_swap23] using ih

private lemma facet_perm_gen (op : Aut4Gen) (fk : Fin 8) (g : Q4Bits) :
    ∃ fk' : Fin 8, evalQ3Fast (extractFacetQ3 fk (applyGen4 op g)) = evalQ3Fast (extractFacetQ3 fk' g) := by
  cases op with
  | f0 => exact facet_perm_flip0 fk g
  | s01 => exact facet_perm_swap01 fk g
  | s12 => exact facet_perm_swap12 fk g
  | s23 => exact facet_perm_swap23 fk g

private lemma facet_perm_word4 (w : List Aut4Gen) (fk : Fin 8) (g : Q4Bits) :
    ∃ fk' : Fin 8, evalQ3Fast (extractFacetQ3 fk (applyWord4 w g)) = evalQ3Fast (extractFacetQ3 fk' g) := by
  induction w generalizing fk with
  | nil => exact ⟨fk, rfl⟩
  | cons op ws ih =>
    obtain ⟨k1, hk1⟩ := facet_perm_gen op fk (applyWord4 ws g)
    obtain ⟨k2, hk2⟩ := ih k1
    exact ⟨k2, hk1.trans hk2⟩

private lemma evalQ3Fast_facet6_word3 (w : List Aut4Gen) (hw : ∀ op ∈ w, op ≠ .s23) (g : Q4Bits) :
    evalQ3Fast (extractFacetQ3 6 (applyWord4 w g)) = evalQ3Fast (extractFacetQ3 6 g) := by
  induction w with
  | nil => rfl
  | cons op ws ih =>
    have hop := hw op (by simp)
    have hws := ih (fun x hx => hw x (by simp [hx]))
    cases op with
    | s23 => exact absurd rfl hop
    | f0 =>
      rcases extractFacet_flip0 (applyWord4 ws g) with ⟨_, _, _, _, _, _, hf6, _⟩
      change evalQ3Fast (extractFacetQ3 6 (q4Flip0 (applyWord4 ws g))) = _
      rw [hf6, evalQ3Fast_q3Flip0]; exact hws
    | s01 =>
      rcases extractFacet_swap01 (applyWord4 ws g) with ⟨_, _, _, _, _, _, hf6, _⟩
      change evalQ3Fast (extractFacetQ3 6 (q4Swap01 (applyWord4 ws g))) = _
      rw [hf6, evalQ3Fast_q3Swap01]; exact hws
    | s12 =>
      rcases extractFacet_swap12 (applyWord4 ws g) with ⟨_, _, _, _, _, _, hf6, _⟩
      change evalQ3Fast (extractFacetQ3 6 (q4Swap12 (applyWord4 ws g))) = _
      rw [hf6, evalQ3Fast_q3Swap12]; exact hws

private lemma extractFacet6_liftAut3 (ai : Fin 48) (g : Q4Bits) :
    extractFacetQ3 6 (liftAut3 ai g) = applyAut3 ai (extractFacetQ3 6 g) := by
  fin_cases ai <;> rfl

private lemma evalQ3Fast_facet6_moveFacetTo6 (fk0 : Fin 8) (g : Q4Bits) :
    evalQ3Fast (extractFacetQ3 6 (moveFacetTo6 fk0 g)) = evalQ3Fast (extractFacetQ3 fk0 g) := by
  fin_cases fk0 <;> simp only [moveFacetTo6, applyWord4, moveFacetWord, List.foldr_cons, List.foldr_nil, applyGen4]
  · -- 0
    rcases extractFacet_swap23 (q4Swap12 (q4Swap01 g)) with ⟨_, _, _, _, _, _, h6, _⟩
    rcases extractFacet_swap12 (q4Swap01 g) with ⟨_, _, _, _, h4, _, _, _⟩
    rcases extractFacet_swap01 g with ⟨_, _, h2, _, _, _, _, _⟩
    exact congrArg evalQ3Fast (h6.trans (h4.trans h2))
  · -- 1
    rcases extractFacet_swap23 (q4Swap12 (q4Swap01 (q4Flip0 g))) with ⟨_, _, _, _, _, _, h6, _⟩
    rcases extractFacet_swap12 (q4Swap01 (q4Flip0 g)) with ⟨_, _, _, _, h4, _, _, _⟩
    rcases extractFacet_swap01 (q4Flip0 g) with ⟨_, _, h2, _, _, _, _, _⟩
    rcases extractFacet_flip0 g with ⟨h0, _, _, _, _, _, _, _⟩
    exact congrArg evalQ3Fast (h6.trans (h4.trans (h2.trans h0)))
  · -- 2
    rcases extractFacet_swap23 (q4Swap12 g) with ⟨_, _, _, _, _, _, h6, _⟩
    rcases extractFacet_swap12 g with ⟨_, _, _, _, h4, _, _, _⟩
    exact congrArg evalQ3Fast (h6.trans h4)
  · -- 3
    rcases extractFacet_swap23 (q4Swap12 (q4Swap01 (q4Flip0 (q4Swap01 g)))) with ⟨_, _, _, _, _, _, h6, _⟩
    rcases extractFacet_swap12 (q4Swap01 (q4Flip0 (q4Swap01 g))) with ⟨_, _, _, _, h4, _, _, _⟩
    rcases extractFacet_swap01 (q4Flip0 (q4Swap01 g)) with ⟨_, _, h2, _, _, _, _, _⟩
    rcases extractFacet_flip0 (q4Swap01 g) with ⟨h0, _, _, _, _, _, _, _⟩
    rcases extractFacet_swap01 g with ⟨_, h1, _, _, _, _, _, _⟩
    exact congrArg evalQ3Fast (h6.trans (h4.trans (h2.trans (h0.trans h1))))
  · -- 4
    rcases extractFacet_swap23 g with ⟨_, _, _, _, _, _, h6, _⟩
    exact congrArg evalQ3Fast h6
  · -- 5
    rcases extractFacet_swap23 (q4Swap12 (q4Swap01 (q4Flip0 (q4Swap01 (q4Swap12 g))))) with ⟨_, _, _, _, _, _, h6, _⟩
    rcases extractFacet_swap12 (q4Swap01 (q4Flip0 (q4Swap01 (q4Swap12 g)))) with ⟨_, _, _, _, h4, _, _, _⟩
    rcases extractFacet_swap01 (q4Flip0 (q4Swap01 (q4Swap12 g))) with ⟨_, _, h2, _, _, _, _, _⟩
    rcases extractFacet_flip0 (q4Swap01 (q4Swap12 g)) with ⟨h0, _, _, _, _, _, _, _⟩
    rcases extractFacet_swap01 (q4Swap12 g) with ⟨_, h1, _, _, _, _, _, _⟩
    rcases extractFacet_swap12 g with ⟨_, _, _, h3, _, _, _, _⟩
    exact congrArg evalQ3Fast (h6.trans (h4.trans (h2.trans (h0.trans (h1.trans h3)))))
  · -- 6
    rfl
  · -- 7
    rcases extractFacet_swap23 (q4Swap12 (q4Swap01 (q4Flip0 (q4Swap01 (q4Swap12 (q4Swap23 g)))))) with ⟨_, _, _, _, _, _, h6, _⟩
    rcases extractFacet_swap12 (q4Swap01 (q4Flip0 (q4Swap01 (q4Swap12 (q4Swap23 g))))) with ⟨_, _, _, _, h4, _, _, _⟩
    rcases extractFacet_swap01 (q4Flip0 (q4Swap01 (q4Swap12 (q4Swap23 g)))) with ⟨_, _, h2, _, _, _, _, _⟩
    rcases extractFacet_flip0 (q4Swap01 (q4Swap12 (q4Swap23 g))) with ⟨h0, _, _, _, _, _, _, _⟩
    rcases extractFacet_swap01 (q4Swap12 (q4Swap23 g)) with ⟨_, h1, _, _, _, _, _, _⟩
    rcases extractFacet_swap12 (q4Swap23 g) with ⟨_, _, _, h3, _, _, _, _⟩
    rcases extractFacet_swap23 g with ⟨_, _, _, _, _, h5, _, _⟩
    exact congrArg evalQ3Fast (h6.trans (h4.trans (h2.trans (h0.trans (h1.trans (h3.trans h5))))))

private theorem q4_bound_all (g : Q4Bits) (hc : isQ4C6Free g) : q4ScoreUngauged g ≤ M_target := by
  obtain ⟨fk0, _, hmax0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 8))
    (fun fk => evalQ3Fast (extractFacetQ3 fk g)) ⟨0, Finset.mem_univ 0⟩
  let g1 := moveFacetTo6 fk0 g
  have hc1 : isQ4C6Free g1 := isQ4C6Free_word4 (moveFacetWord fk0) hc
  have hs1 : q4ScoreUngauged g1 = q4ScoreUngauged g := q4ScoreUngauged_word4 (moveFacetWord fk0) g
  have hmax1 : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g1) ≤ evalQ3Fast (extractFacetQ3 6 g1) := by
    intro fk
    obtain ⟨fk', hfk'⟩ := facet_perm_word4 (moveFacetWord fk0) fk g
    calc evalQ3Fast (extractFacetQ3 fk g1)
        = evalQ3Fast (extractFacetQ3 fk' g) := hfk'
      _ ≤ evalQ3Fast (extractFacetQ3 fk0 g) := hmax0 fk' (Finset.mem_univ fk')
      _ = evalQ3Fast (extractFacetQ3 6 g1) := (evalQ3Fast_facet6_moveFacetTo6 fk0 g).symm
  have hq1_c6 : isQ3C6Free (extractFacetQ3 6 g1) = true := isQ3C6Free_of_isQ4C6Free g1 hc1 6
  obtain ⟨ai, ri, hai⟩ := q3_exists_aut3_rep (extractFacetQ3 6 g1) hq1_c6
  let g2 := liftAut3 ai g1
  have hc2 : isQ4C6Free g2 := isQ4C6Free_word4 (liftAut3Word ai) hc1
  have hs2 : q4ScoreUngauged g2 = q4ScoreUngauged g1 := q4ScoreUngauged_word4 (liftAut3Word ai) g1
  have hrep2 : extractFacetQ3 6 g2 = q3RepBits ri := (extractFacet6_liftAut3 ai g1).trans hai
  have hw3 : ∀ op ∈ liftAut3Word ai, op ≠ .s23 := by fin_cases ai <;> decide
  have hmax2 : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g2) ≤ evalQ3Fast (extractFacetQ3 6 g2) := by
    intro fk
    obtain ⟨fk', hfk'⟩ := facet_perm_word4 (liftAut3Word ai) fk g1
    calc evalQ3Fast (extractFacetQ3 fk g2)
        = evalQ3Fast (extractFacetQ3 fk' g1) := hfk'
      _ ≤ evalQ3Fast (extractFacetQ3 6 g1) := hmax1 fk'
      _ = evalQ3Fast (extractFacetQ3 6 g2) := (evalQ3Fast_facet6_word3 (liftAut3Word ai) hw3 g1).symm
  have hbound := all_roots_bound ri g2 hc2 hrep2 hmax2
  rw [q4ScoreGauged_eq_ungauged, hs2, hs1] at hbound
  exact hbound

end AutQ4Invariance

/-! ## Section 3: `Q_4` Embedding & `extractQ4_isC6Free` -/

section Q4Embedding

private def P2 (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

private def P3 (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)

private def P4 (n : ℕ) : Finset (Fin n × Fin n × Fin n × Fin n) :=
  Finset.univ.filter (fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
    p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2)

private lemma sum_P2 {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    (∑ p ∈ P2 n, F p.1 p.2) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, F i j := by
  symm
  calc (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, F i j)
      = ∑ q ∈ (Finset.univ : Finset (Fin n)).sigma (fun i => Finset.univ.erase i), F q.1 q.2 :=
          (Finset.sum_sigma (Finset.univ : Finset (Fin n)) (fun i => Finset.univ.erase i)
            (fun q => F q.1 q.2)).symm
    _ = ∑ p ∈ P2 n, F p.1 p.2 := by
        refine Finset.sum_bij (fun (q : Σ _ : Fin n, Fin n) _ => (q.1, q.2)) ?_ ?_ ?_ ?_
        · intro ⟨a, b⟩ h
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, true_and] at h
          simp only [P2, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h.1.symm
        · intro ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h; cases h; rfl
        · intro ⟨a, b⟩ h
          simp only [P2, Finset.mem_filter, Finset.mem_univ, true_and] at h
          refine ⟨⟨a, b⟩, ?_, rfl⟩
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, true_and]
          exact ⟨h.symm, trivial⟩
        · intro _ _; rfl

private lemma P2_card (n : ℕ) : (P2 n).card = n * (n - 1) := by
  have h := sum_P2 (fun (_ _ : Fin n) => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have h1 : ∀ i : Fin n, (Finset.univ.erase i).card = n - 1 := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
  rw [h]
  simp only [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

private lemma sum_P3 {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → Fin n → M) :
    (∑ p ∈ P3 n, F p.1 p.2.1 p.2.2) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, F i j k := by
  symm
  have h_in : ∀ i : Fin n, (∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, F i j k) =
      ∑ jk ∈ (Finset.univ.erase i).sigma (fun j => (Finset.univ.erase i).erase j), F i jk.1 jk.2 :=
    fun i => (Finset.sum_sigma (Finset.univ.erase i) (fun j => (Finset.univ.erase i).erase j)
      (fun jk => F i jk.1 jk.2)).symm
  calc (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, F i j k)
      = ∑ i : Fin n, ∑ jk ∈ (Finset.univ.erase i).sigma (fun j => (Finset.univ.erase i).erase j), F i jk.1 jk.2 :=
          Finset.sum_congr rfl fun i _ => h_in i
    _ = ∑ q ∈ (Finset.univ : Finset (Fin n)).sigma (fun i =>
            (Finset.univ.erase i).sigma (fun j => (Finset.univ.erase i).erase j)), F q.1 q.2.1 q.2.2 :=
          (Finset.sum_sigma (Finset.univ : Finset (Fin n))
            (fun i => (Finset.univ.erase i).sigma (fun j => (Finset.univ.erase i).erase j))
            (fun q => F q.1 q.2.1 q.2.2)).symm
    _ = ∑ p ∈ P3 n, F p.1 p.2.1 p.2.2 := by
        refine Finset.sum_bij (fun (q : Σ _ : Fin n, Σ _ : Fin n, Fin n) _ => (q.1, q.2.1, q.2.2)) ?_ ?_ ?_ ?_
        · intro ⟨a, b, c⟩ h
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, true_and] at h
          simp only [P3, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨h.1.1.symm, h.2.2.1.symm, h.2.1.symm⟩
        · intro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h; cases h; rfl
        · intro ⟨a, b, c⟩ h
          simp only [P3, Finset.mem_filter, Finset.mem_univ, true_and] at h
          refine ⟨⟨a, ⟨b, c⟩⟩, ?_, rfl⟩
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, true_and]
          exact ⟨⟨h.1.symm, trivial⟩, h.2.2.symm, h.2.1.symm, trivial⟩
        · intro _ _; rfl

private lemma sum_P4 {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → Fin n → Fin n → M) :
    (∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2) =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
        ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, F i j k l := by
  symm
  have h_kl : ∀ i j : Fin n,
      (∑ k ∈ (Finset.univ.erase i).erase j, ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, F i j k l) =
      ∑ kl ∈ ((Finset.univ.erase i).erase j).sigma (fun k => ((Finset.univ.erase i).erase j).erase k),
        F i j kl.1 kl.2 :=
    fun i j => (Finset.sum_sigma ((Finset.univ.erase i).erase j)
      (fun k => ((Finset.univ.erase i).erase j).erase k) (fun kl => F i j kl.1 kl.2)).symm
  have h_jkl : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
        ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, F i j k l) =
      ∑ jkl ∈ (Finset.univ.erase i).sigma
        (fun j => ((Finset.univ.erase i).erase j).sigma (fun k => ((Finset.univ.erase i).erase j).erase k)),
          F i jkl.1 jkl.2.1 jkl.2.2 := by
    intro i
    calc (∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
            ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, F i j k l)
        = ∑ j ∈ Finset.univ.erase i, ∑ kl ∈ ((Finset.univ.erase i).erase j).sigma
            (fun k => ((Finset.univ.erase i).erase j).erase k), F i j kl.1 kl.2 :=
            Finset.sum_congr rfl fun j _ => h_kl i j
      _ = _ := (Finset.sum_sigma (Finset.univ.erase i)
            (fun j => ((Finset.univ.erase i).erase j).sigma (fun k => ((Finset.univ.erase i).erase j).erase k))
            (fun jkl => F i jkl.1 jkl.2.1 jkl.2.2)).symm
  calc (∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
          ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, F i j k l)
      = ∑ i : Fin n, ∑ jkl ∈ (Finset.univ.erase i).sigma
          (fun j => ((Finset.univ.erase i).erase j).sigma (fun k => ((Finset.univ.erase i).erase j).erase k)),
            F i jkl.1 jkl.2.1 jkl.2.2 := Finset.sum_congr rfl fun i _ => h_jkl i
    _ = ∑ q ∈ (Finset.univ : Finset (Fin n)).sigma (fun i => (Finset.univ.erase i).sigma
          (fun j => ((Finset.univ.erase i).erase j).sigma (fun k => ((Finset.univ.erase i).erase j).erase k))),
            F q.1 q.2.1 q.2.2.1 q.2.2.2 :=
          (Finset.sum_sigma (Finset.univ : Finset (Fin n))
            (fun i => (Finset.univ.erase i).sigma
              (fun j => ((Finset.univ.erase i).erase j).sigma (fun k => ((Finset.univ.erase i).erase j).erase k)))
            (fun q => F q.1 q.2.1 q.2.2.1 q.2.2.2)).symm
    _ = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
        refine Finset.sum_bij (fun (q : Σ _ : Fin n, Σ _ : Fin n, Σ _ : Fin n, Fin n) _ =>
            (q.1, q.2.1, q.2.2.1, q.2.2.2)) ?_ ?_ ?_ ?_
        · intro ⟨a, b, c, d⟩ h
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, true_and] at h
          rcases h with ⟨⟨hba, _⟩, ⟨hcb, hca, _⟩, ⟨hdc, hdb, hda, _⟩⟩
          simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hba.symm, hca.symm, hda.symm, hcb.symm, hdb.symm, hdc.symm⟩
        · intro ⟨a1, b1, c1, d1⟩ _ ⟨a2, b2, c2, d2⟩ _ h; cases h; rfl
        · intro ⟨a, b, c, d⟩ h
          simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h
          refine ⟨⟨a, ⟨b, ⟨c, d⟩⟩⟩, ?_, rfl⟩
          simp [Finset.mem_sigma, Finset.mem_erase,
            h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm]
        · intro _ _; rfl

private lemma P4_card (n : ℕ) : (P4 n).card = n * (n - 1) * (n - 2) * (n - 3) := by
  have h : (∑ p ∈ P4 n, (1 : ℕ)) = ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i,
      ∑ k ∈ (Finset.univ.erase i).erase j, ∑ _l ∈ ((Finset.univ.erase i).erase j).erase k, (1 : ℕ) :=
    sum_P4 (fun (_ _ _ _ : Fin n) => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have h3 : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i, ∀ k ∈ (Finset.univ.erase i).erase j,
      (((Finset.univ.erase i).erase j).erase k).card = n - 3 := by
    intro i j hj k hk
    rw [Finset.card_erase_of_mem hk, Finset.card_erase_of_mem hj,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]; omega
  have h2 : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
      ((Finset.univ.erase i).erase j).card = n - 2 := by
    intro i j hj
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]; omega
  have h1 : ∀ i : Fin n, (Finset.univ.erase i).card = n - 1 := fun i => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
  have hi : ∀ i : Fin n, (∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
      (((Finset.univ.erase i).erase j).erase k).card) = (n - 1) * (n - 2) * (n - 3) := by
    intro i
    have hs1 : ∀ j ∈ Finset.univ.erase i, (∑ k ∈ (Finset.univ.erase i).erase j,
        (((Finset.univ.erase i).erase j).erase k).card) = (n - 2) * (n - 3) := fun j hj => by
      rw [Finset.sum_congr rfl fun k hk => h3 i j hj k hk, Finset.sum_const, h2 i j hj, smul_eq_mul]
    rw [Finset.sum_congr rfl hs1, Finset.sum_const, h1 i, smul_eq_mul]; ring
  rw [h, Finset.sum_congr rfl fun i _ => hi i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring

private lemma sum_P4_dropL {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → Fin n → M) :
    (∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1) = (n - 3) • ∑ p ∈ P3 n, F p.1 p.2.1 p.2.2 := by
  have h4 := sum_P4 (fun i j k (_ : Fin n) => F i j k)
  have h3 := sum_P3 F
  rw [h4, h3, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hc : (((Finset.univ.erase i).erase j).erase k).card = n - 3 := by
    rw [Finset.card_erase_of_mem hk, Finset.card_erase_of_mem hj,
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]; omega
  rw [Finset.sum_const, hc]

private lemma sum_P4_dropKL {n : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    (∑ p ∈ P4 n, F p.1 p.2.1) = ((n - 2) * (n - 3)) • ∑ p ∈ P2 n, F p.1 p.2 := by
  have h1 := sum_P4_dropL (fun (i j _ : Fin n) => F i j)
  have h3 := sum_P3 (fun i j (_ : Fin n) => F i j)
  have h2 := sum_P2 F
  rw [h1, h3, h2, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hc : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]; omega
  rw [Finset.sum_const, hc, smul_smul, mul_comm (n - 2) (n - 3)]

private def embedQ4 {n : ℕ} (u : Fin n → Bool) (i j k l : Fin n) (v : Fin 16) : Fin n → Bool :=
  let u1 := if v.val % 2 = 1 then qFlip u i else u
  let u2 := if (v.val / 2) % 2 = 1 then qFlip u1 j else u1
  let u3 := if (v.val / 4) % 2 = 1 then qFlip u2 k else u2
  if (v.val / 8) % 2 = 1 then qFlip u3 l else u3

private lemma embedQ4_bit0 {n : ℕ} (u : Fin n → Bool) {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (v : Fin 16) :
    embedQ4 u i j k l v i = if v.val % 2 = 1 then !u i else u i := by
  dsimp only [embedQ4]; split_ifs <;>
    simp [qFlip, Function.update, hij, hik, hil]

private lemma embedQ4_bit1 {n : ℕ} (u : Fin n → Bool) {i j k l : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hjl : j ≠ l) (v : Fin 16) :
    embedQ4 u i j k l v j = if (v.val / 2) % 2 = 1 then !u j else u j := by
  dsimp only [embedQ4]; split_ifs <;>
    simp [qFlip, Function.update, hij.symm, hjk, hjl]

private lemma embedQ4_bit2 {n : ℕ} (u : Fin n → Bool) {i j k l : Fin n}
    (hik : i ≠ k) (hjk : j ≠ k) (hkl : k ≠ l) (v : Fin 16) :
    embedQ4 u i j k l v k = if (v.val / 4) % 2 = 1 then !u k else u k := by
  dsimp only [embedQ4]; split_ifs <;>
    simp [qFlip, Function.update, hik.symm, hjk.symm, hkl]

private lemma embedQ4_bit3 {n : ℕ} (u : Fin n → Bool) {i j k l : Fin n}
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l) (v : Fin 16) :
    embedQ4 u i j k l v l = if (v.val / 8) % 2 = 1 then !u l else u l := by
  dsimp only [embedQ4]; split_ifs <;>
    simp [qFlip, Function.update, hil.symm, hjl.symm, hkl.symm]

private lemma embedQ4_injective {n : ℕ} (u : Fin n → Bool) {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Function.Injective (embedQ4 u i j k l) := by
  intro v1 v2 h
  have b0 : (v1.val % 2 = 1) ↔ (v2.val % 2 = 1) := by
    have h0 := congrFun h i
    rw [embedQ4_bit0 u hij hik hil v1, embedQ4_bit0 u hij hik hil v2] at h0
    by_cases p1 : v1.val % 2 = 1 <;> by_cases p2 : v2.val % 2 = 1 <;> simp_all
  have b1 : ((v1.val / 2) % 2 = 1) ↔ ((v2.val / 2) % 2 = 1) := by
    have h1 := congrFun h j
    rw [embedQ4_bit1 u hij hjk hjl v1, embedQ4_bit1 u hij hjk hjl v2] at h1
    by_cases p1 : (v1.val / 2) % 2 = 1 <;> by_cases p2 : (v2.val / 2) % 2 = 1 <;> simp_all
  have b2 : ((v1.val / 4) % 2 = 1) ↔ ((v2.val / 4) % 2 = 1) := by
    have h2 := congrFun h k
    rw [embedQ4_bit2 u hik hjk hkl v1, embedQ4_bit2 u hik hjk hkl v2] at h2
    by_cases p1 : (v1.val / 4) % 2 = 1 <;> by_cases p2 : (v2.val / 4) % 2 = 1 <;> simp_all
  have b3 : ((v1.val / 8) % 2 = 1) ↔ ((v2.val / 8) % 2 = 1) := by
    have h3 := congrFun h l
    rw [embedQ4_bit3 u hil hjl hkl v1, embedQ4_bit3 u hil hjl hkl v2] at h3
    by_cases p1 : (v1.val / 8) % 2 = 1 <;> by_cases p2 : (v2.val / 8) % 2 = 1 <;> simp_all
  ext; omega

private lemma embedQ4_invol {n : ℕ} (v : Fin 16) (i j k l : Fin n) (u : Fin n → Bool) :
    embedQ4 (embedQ4 u i j k l v) i j k l v = u := by
  fin_cases v <;> dsimp only [embedQ4] <;> simp [qFlip_flip, qFlip_comm]

private lemma sum_u_embedQ4 {n : ℕ} (v : Fin 16) (i j k l : Fin n) (F : (Fin n → Bool) → ℤ) :
    (∑ u : Fin n → Bool, F (embedQ4 u i j k l v)) = ∑ u : Fin n → Bool, F u :=
  Fintype.sum_equiv
    { toFun := fun u => embedQ4 u i j k l v
      invFun := fun u => embedQ4 u i j k l v
      left_inv := embedQ4_invol v i j k l
      right_inv := embedQ4_invol v i j k l } _ _ (fun _ => rfl)


private def extractQ4 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j k l : Fin n) : Q4Bits :=
  { q00 := decide (G.Adj (embedQ4 u i j k l ⟨0, by decide⟩) (embedQ4 u i j k l ⟨1, by decide⟩)), q01 := decide (G.Adj (embedQ4 u i j k l ⟨0, by decide⟩) (embedQ4 u i j k l ⟨2, by decide⟩)), q02 := decide (G.Adj (embedQ4 u i j k l ⟨0, by decide⟩) (embedQ4 u i j k l ⟨4, by decide⟩)), q03 := decide (G.Adj (embedQ4 u i j k l ⟨0, by decide⟩) (embedQ4 u i j k l ⟨8, by decide⟩)), q04 := decide (G.Adj (embedQ4 u i j k l ⟨1, by decide⟩) (embedQ4 u i j k l ⟨3, by decide⟩)), q05 := decide (G.Adj (embedQ4 u i j k l ⟨1, by decide⟩) (embedQ4 u i j k l ⟨5, by decide⟩)), q06 := decide (G.Adj (embedQ4 u i j k l ⟨1, by decide⟩) (embedQ4 u i j k l ⟨9, by decide⟩)), q07 := decide (G.Adj (embedQ4 u i j k l ⟨2, by decide⟩) (embedQ4 u i j k l ⟨3, by decide⟩)), q08 := decide (G.Adj (embedQ4 u i j k l ⟨2, by decide⟩) (embedQ4 u i j k l ⟨6, by decide⟩)), q09 := decide (G.Adj (embedQ4 u i j k l ⟨2, by decide⟩) (embedQ4 u i j k l ⟨10, by decide⟩)), q10 := decide (G.Adj (embedQ4 u i j k l ⟨3, by decide⟩) (embedQ4 u i j k l ⟨7, by decide⟩)), q11 := decide (G.Adj (embedQ4 u i j k l ⟨3, by decide⟩) (embedQ4 u i j k l ⟨11, by decide⟩)), q12 := decide (G.Adj (embedQ4 u i j k l ⟨4, by decide⟩) (embedQ4 u i j k l ⟨5, by decide⟩)), q13 := decide (G.Adj (embedQ4 u i j k l ⟨4, by decide⟩) (embedQ4 u i j k l ⟨6, by decide⟩)), q14 := decide (G.Adj (embedQ4 u i j k l ⟨4, by decide⟩) (embedQ4 u i j k l ⟨12, by decide⟩)), q15 := decide (G.Adj (embedQ4 u i j k l ⟨5, by decide⟩) (embedQ4 u i j k l ⟨7, by decide⟩)), q16 := decide (G.Adj (embedQ4 u i j k l ⟨5, by decide⟩) (embedQ4 u i j k l ⟨13, by decide⟩)), q17 := decide (G.Adj (embedQ4 u i j k l ⟨6, by decide⟩) (embedQ4 u i j k l ⟨7, by decide⟩)), q18 := decide (G.Adj (embedQ4 u i j k l ⟨6, by decide⟩) (embedQ4 u i j k l ⟨14, by decide⟩)), q19 := decide (G.Adj (embedQ4 u i j k l ⟨7, by decide⟩) (embedQ4 u i j k l ⟨15, by decide⟩)), q20 := decide (G.Adj (embedQ4 u i j k l ⟨8, by decide⟩) (embedQ4 u i j k l ⟨9, by decide⟩)), q21 := decide (G.Adj (embedQ4 u i j k l ⟨8, by decide⟩) (embedQ4 u i j k l ⟨10, by decide⟩)), q22 := decide (G.Adj (embedQ4 u i j k l ⟨8, by decide⟩) (embedQ4 u i j k l ⟨12, by decide⟩)), q23 := decide (G.Adj (embedQ4 u i j k l ⟨9, by decide⟩) (embedQ4 u i j k l ⟨11, by decide⟩)), q24 := decide (G.Adj (embedQ4 u i j k l ⟨9, by decide⟩) (embedQ4 u i j k l ⟨13, by decide⟩)), q25 := decide (G.Adj (embedQ4 u i j k l ⟨10, by decide⟩) (embedQ4 u i j k l ⟨11, by decide⟩)), q26 := decide (G.Adj (embedQ4 u i j k l ⟨10, by decide⟩) (embedQ4 u i j k l ⟨14, by decide⟩)), q27 := decide (G.Adj (embedQ4 u i j k l ⟨11, by decide⟩) (embedQ4 u i j k l ⟨15, by decide⟩)), q28 := decide (G.Adj (embedQ4 u i j k l ⟨12, by decide⟩) (embedQ4 u i j k l ⟨13, by decide⟩)), q29 := decide (G.Adj (embedQ4 u i j k l ⟨12, by decide⟩) (embedQ4 u i j k l ⟨14, by decide⟩)), q30 := decide (G.Adj (embedQ4 u i j k l ⟨13, by decide⟩) (embedQ4 u i j k l ⟨15, by decide⟩)), q31 := decide (G.Adj (embedQ4 u i j k l ⟨14, by decide⟩) (embedQ4 u i j k l ⟨15, by decide⟩)) }

private lemma getQ4E_extractQ4 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j k l : Fin n) (e : Fin 32) :
    getQ4E (extractQ4 G u i j k l) e =
      decide (G.Adj (embedQ4 u i j k l (edgeEndpointsQ4 e).1) (embedQ4 u i j k l (edgeEndpointsQ4 e).2)) := by
  fin_cases e <;> rfl


private def allFin6 (P : Fin 6 → Bool) : Bool :=
  [0, 1, 2, 3, 4, 5].all fun i => if h : i < 6 then P ⟨i, h⟩ else true

private lemma allFin6_ok {P : Fin 6 → Bool} (h : allFin6 P = true) (x : Fin 6) : P x = true := by
  fin_cases x <;> simp_all [allFin6]

private def checkC6EmbedSpec : Bool :=
  allFin128 fun cid =>
    let (c0, c1, c2, c3, c4, c5) := c6CyclesQ4 cid
    (allFin6 fun m1 => allFin6 fun m2 =>
      decide (m1 = m2) || decide (c6CycleVertsQ4 cid m1 ≠ c6CycleVertsQ4 cid m2)) &&
    (allFin6 fun m =>
      let e := c6CycleOrdEdge cid m
      let ep := edgeEndpointsQ4 e
      let v1 := c6CycleVertsQ4 cid m
      let v2 := c6CycleVertsQ4 cid ⟨(m.val + 1) % 6, Nat.mod_lt _ (by decide)⟩
      in6B e c0 c1 c2 c3 c4 c5 &&
      (decide (ep = (v1, v2)) || decide (ep = (v2, v1))))

private lemma checkC6EmbedSpec_ok : checkC6EmbedSpec = true := by decide

private lemma adj_of_edgeEndpoints {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j k l : Fin n) (cid : Fin 128) (m : Fin 6)
    (he : getQ4E (extractQ4 G u i j k l) (c6CycleOrdEdge cid m) = true) :
    G.Adj (embedQ4 u i j k l (c6CycleVertsQ4 cid m))
      (embedQ4 u i j k l (c6CycleVertsQ4 cid ⟨(m.val + 1) % 6, Nat.mod_lt _ (by decide)⟩)) := by
  have hsp := allFin128_ok checkC6EmbedSpec_ok cid
  dsimp only [checkC6EmbedSpec] at hsp
  rcases hcid : c6CyclesQ4 cid with ⟨c0, c1, c2, c3, c4, c5⟩
  rw [hcid] at hsp
  simp only [Bool.and_eq_true] at hsp
  have hm := allFin6_ok hsp.2 m
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hm
  rw [getQ4E_extractQ4, decide_eq_true_eq] at he
  rcases hm.2 with hdir | hrev
  · rcases hdir with hdir; rw [hdir] at he; exact he
  · rw [hrev] at he; exact he.symm

private lemma extractQ4_isC6Free {n : ℕ} {G : SimpleGraph (Fin n → Bool)} [DecidableRel G.Adj]
    (hfree : IsC6Free G) (u : Fin n → Bool) {i j k l : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    isQ4C6Free (extractQ4 G u i j k l) := by
  intro cid
  rcases hcid : c6CyclesQ4 cid with ⟨c0, c1, c2, c3, c4, c5⟩
  rintro ⟨h0, h1, h2, h3, h4, h5⟩
  have hsp := allFin128_ok checkC6EmbedSpec_ok cid
  dsimp only [checkC6EmbedSpec] at hsp
  rw [hcid] at hsp
  simp only [Bool.and_eq_true] at hsp
  have hinjV : Function.Injective (c6CycleVertsQ4 cid) := by
    intro m1 m2 hmeq
    have hd := allFin6_ok (allFin6_ok hsp.1 m1) m2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hd
    rcases hd with rfl | hne
    · rfl
    · exact absurd hmeq hne
  have hinj : Function.Injective (fun m : Fin 6 => embedQ4 u i j k l (c6CycleVertsQ4 cid m)) :=
    (embedQ4_injective u hij hik hil hjk hjl hkl).comp hinjV
  have hmem : ∀ m : Fin 6, getQ4E (extractQ4 G u i j k l) (c6CycleOrdEdge cid m) = true := by
    intro m
    have hm := allFin6_ok hsp.2 m
    simp only [Bool.and_eq_true] at hm
    exact mem_of_in6B hm.1 h0 h1 h2 h3 h4 h5
  exact hfree _ hinj ⟨
    adj_of_edgeEndpoints G u i j k l cid 0 (hmem 0),
    adj_of_edgeEndpoints G u i j k l cid 1 (hmem 1),
    adj_of_edgeEndpoints G u i j k l cid 2 (hmem 2),
    adj_of_edgeEndpoints G u i j k l cid 3 (hmem 3),
    adj_of_edgeEndpoints G u i j k l cid 4 (hmem 4),
    adj_of_edgeEndpoints G u i j k l cid 5 (hmem 5)⟩

end Q4Embedding

/-! ## Section 4: Global Averaging & PSD Diagonal Bounds -/

section GlobalAveraging

private lemma decide_adj_comm {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    decide (G.Adj x y) = decide (G.Adj y x) :=
  decide_eq_decide.mpr (G.adj_comm x y)

private def embedQ3 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) : Fin n → Bool :=
  let u1 := if w 0 then qFlip u a else u
  let u2 := if w 1 then qFlip u1 b else u1
  if w 2 then qFlip u2 c else u2

private lemma embedQ3_invol {n : ℕ} (w : Fin 3 → Bool) (a b c : Fin n) (u : Fin n → Bool) :
    embedQ3 (embedQ3 u a b c w) a b c w = u := by
  dsimp only [embedQ3]; cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [qFlip_flip, qFlip_comm]

private lemma sum_u_embedQ3 {n : ℕ} (w : Fin 3 → Bool) (a b c : Fin n) (F : (Fin n → Bool) → ℤ) :
    (∑ u : Fin n → Bool, F (embedQ3 u a b c w)) = ∑ u : Fin n → Bool, F u :=
  Fintype.sum_equiv
    { toFun := fun u => embedQ3 u a b c w
      invFun := fun u => embedQ3 u a b c w
      left_inv := embedQ3_invol w a b c
      right_inv := embedQ3_invol w a b c } _ _ (fun _ => rfl)

private def edgeFlag {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (i j : Fin n) : Fin 8 :=
  mkFlag (decide (G.Adj v (qFlip v j)))
         (decide (G.Adj (qFlip v i) (qFlip (qFlip v i) j)))
         (decide (G.Adj (qFlip v j) (qFlip (qFlip v j) i)))

private def q3OrientedTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (i j1 j2 : Fin n) : ℤ :=
  q3EdgeTerm (decide (G.Adj v (qFlip v i)))
    (decide (G.Adj v (qFlip v j1)))
    (decide (G.Adj (qFlip v i) (qFlip (qFlip v i) j1)))
    (decide (G.Adj (qFlip v j1) (qFlip (qFlip v j1) i)))
    (decide (G.Adj v (qFlip v j2)))
    (decide (G.Adj (qFlip v i) (qFlip (qFlip v i) j2)))
    (decide (G.Adj (qFlip v j2) (qFlip (qFlip v j2) i)))

private def extractQ3 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (a b c : Fin n) : Q3Bits :=
  let v0 := u
  let v1 := qFlip u a
  let v2 := qFlip u b
  let v3 := qFlip (qFlip u a) b
  let v4 := qFlip u c
  let v5 := qFlip (qFlip u a) c
  let v6 := qFlip (qFlip u b) c
  let v7 := qFlip (qFlip (qFlip u a) b) c
  { e01 := decide (G.Adj v0 v1), e02 := decide (G.Adj v0 v2), e04 := decide (G.Adj v0 v4),
    e13 := decide (G.Adj v1 v3), e15 := decide (G.Adj v1 v5),
    e23 := decide (G.Adj v2 v3), e26 := decide (G.Adj v2 v6),
    e37 := decide (G.Adj v3 v7),
    e45 := decide (G.Adj v4 v5), e46 := decide (G.Adj v4 v6),
    e57 := decide (G.Adj v5 v7), e67 := decide (G.Adj v6 v7) }

private lemma qFlip_flip2 {n : ℕ} (u : Fin n → Bool) (a b : Fin n) :
    qFlip (qFlip (qFlip u a) b) a = qFlip u b := by
  rw [qFlip_comm (qFlip u a) b a, qFlip_flip]

private lemma qFlip_flip3 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) :
    qFlip (qFlip (qFlip (qFlip u a) b) c) a = qFlip (qFlip u b) c := by
  rw [qFlip_comm (qFlip (qFlip u a) b) c a, qFlip_flip2]

private lemma qFlip_flip3b {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) :
    qFlip (qFlip (qFlip (qFlip u a) b) c) b = qFlip (qFlip u a) c := by
  rw [qFlip_comm (qFlip (qFlip u a) b) c b, qFlip_flip]

private lemma vec3_eval {α : Type*} (x y z : α) :
    ![x, y, z] 0 = x ∧ ![x, y, z] 1 = y ∧ ![x, y, z] 2 = z := ⟨rfl, rfl, rfl⟩

private lemma evalQ3U_extractQ3 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (a b c : Fin n) :
    evalQ3U (extractQ3 G u a b c) =
      ∑ w : Fin 3 → Bool, (
        q3OrientedTerm G (embedQ3 u a b c w) a b c +
        q3OrientedTerm G (embedQ3 u a b c w) a c b +
        q3OrientedTerm G (embedQ3 u a b c w) b a c +
        q3OrientedTerm G (embedQ3 u a b c w) b c a +
        q3OrientedTerm G (embedQ3 u a b c w) c a b +
        q3OrientedTerm G (embedQ3 u a b c w) c b a) := by
  have hw : (∑ w : Fin 3 → Bool, (
      q3OrientedTerm G (embedQ3 u a b c w) a b c +
      q3OrientedTerm G (embedQ3 u a b c w) a c b +
      q3OrientedTerm G (embedQ3 u a b c w) b a c +
      q3OrientedTerm G (embedQ3 u a b c w) b c a +
      q3OrientedTerm G (embedQ3 u a b c w) c a b +
      q3OrientedTerm G (embedQ3 u a b c w) c b a)) =
      (fun g => g ![false,false,false] + g ![true,false,false] + g ![false,true,false] + g ![true,true,false] +
                g ![false,false,true] + g ![true,false,true] + g ![false,true,true] + g ![true,true,true])
        (fun w =>
          q3OrientedTerm G (embedQ3 u a b c w) a b c +
          q3OrientedTerm G (embedQ3 u a b c w) a c b +
          q3OrientedTerm G (embedQ3 u a b c w) b a c +
          q3OrientedTerm G (embedQ3 u a b c w) b c a +
          q3OrientedTerm G (embedQ3 u a b c w) c a b +
          q3OrientedTerm G (embedQ3 u a b c w) c b a) := by
    let e : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
      { toFun := fun w => (w 0, w 1, w 2)
        invFun := fun p => ![p.1, p.2.1, p.2.2]
        left_inv := fun w => by ext i; fin_cases i <;> rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    have heq : ∀ w : Fin 3 → Bool, ![w 0, w 1, w 2] = w := fun w => by ext i; fin_cases i <;> rfl
    rw [Fintype.sum_equiv e _ (fun p => (
      q3OrientedTerm G (embedQ3 u a b c ![p.1, p.2.1, p.2.2]) a b c +
      q3OrientedTerm G (embedQ3 u a b c ![p.1, p.2.1, p.2.2]) a c b +
      q3OrientedTerm G (embedQ3 u a b c ![p.1, p.2.1, p.2.2]) b a c +
      q3OrientedTerm G (embedQ3 u a b c ![p.1, p.2.1, p.2.2]) b c a +
      q3OrientedTerm G (embedQ3 u a b c ![p.1, p.2.1, p.2.2]) c a b +
      q3OrientedTerm G (embedQ3 u a b c ![p.1, p.2.1, p.2.2]) c b a)) (fun w => by
        dsimp only [e]; simp only [Equiv.coe_fn_mk]; rw [heq w])]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]; ring
  rw [hw]
  dsimp only [evalQ3U, q3UngaugedBool, extractQ3, q3OrientedTerm, embedQ3]
  simp only [vec3_eval, Bool.false_eq_true, eq_self, ↓reduceIte, qFlip_flip, qFlip_flip2, qFlip_flip3]
  have hf_ab : qFlip (qFlip u b) a = qFlip (qFlip u a) b := qFlip_comm u b a
  have hf_ac : qFlip (qFlip u c) a = qFlip (qFlip u a) c := qFlip_comm u c a
  have hf_bc : qFlip (qFlip u c) b = qFlip (qFlip u b) c := qFlip_comm u c b
  have hf_abc1 : qFlip (qFlip (qFlip u a) c) b = qFlip (qFlip (qFlip u a) b) c :=
    qFlip_comm (qFlip u a) c b
  have hf_abc2 : qFlip (qFlip (qFlip u b) c) a = qFlip (qFlip (qFlip u a) b) c := by
    rw [qFlip_comm (qFlip u b) c a, qFlip_comm u b a]
  simp only [hf_ab, hf_ac, hf_bc, hf_abc1, hf_abc2]
  -- Normalize edge direction for swapped endpoints inside decide (G.Adj ...)
  have hc01 : decide (G.Adj (qFlip u a) u) = decide (G.Adj u (qFlip u a)) := decide_adj_comm G _ _
  have hc02 : decide (G.Adj (qFlip u b) u) = decide (G.Adj u (qFlip u b)) := decide_adj_comm G _ _
  have hc04 : decide (G.Adj (qFlip u c) u) = decide (G.Adj u (qFlip u c)) := decide_adj_comm G _ _
  have hc13 : decide (G.Adj (qFlip (qFlip u a) b) (qFlip u a)) = decide (G.Adj (qFlip u a) (qFlip (qFlip u a) b)) := decide_adj_comm G _ _
  have hc15 : decide (G.Adj (qFlip (qFlip u a) c) (qFlip u a)) = decide (G.Adj (qFlip u a) (qFlip (qFlip u a) c)) := decide_adj_comm G _ _
  have hc23 : decide (G.Adj (qFlip (qFlip u a) b) (qFlip u b)) = decide (G.Adj (qFlip u b) (qFlip (qFlip u a) b)) := decide_adj_comm G _ _
  have hc26 : decide (G.Adj (qFlip (qFlip u b) c) (qFlip u b)) = decide (G.Adj (qFlip u b) (qFlip (qFlip u b) c)) := decide_adj_comm G _ _
  have hc37 : decide (G.Adj (qFlip (qFlip (qFlip u a) b) c) (qFlip (qFlip u a) b)) = decide (G.Adj (qFlip (qFlip u a) b) (qFlip (qFlip (qFlip u a) b) c)) := decide_adj_comm G _ _
  have hc45 : decide (G.Adj (qFlip (qFlip u a) c) (qFlip u c)) = decide (G.Adj (qFlip u c) (qFlip (qFlip u a) c)) := decide_adj_comm G _ _
  have hc46 : decide (G.Adj (qFlip (qFlip u b) c) (qFlip u c)) = decide (G.Adj (qFlip u c) (qFlip (qFlip u b) c)) := decide_adj_comm G _ _
  have hc57 : decide (G.Adj (qFlip (qFlip (qFlip u a) b) c) (qFlip (qFlip u a) c)) = decide (G.Adj (qFlip (qFlip u a) c) (qFlip (qFlip (qFlip u a) b) c)) := decide_adj_comm G _ _
  have hc67 : decide (G.Adj (qFlip (qFlip (qFlip u a) b) c) (qFlip (qFlip u b) c)) = decide (G.Adj (qFlip (qFlip u b) c) (qFlip (qFlip (qFlip u a) b) c)) := decide_adj_comm G _ _
  simp only [hc01, hc02, hc04, hc13, hc15, hc23, hc26, hc37, hc45, hc46, hc57, hc67]
  ring

private lemma embedQ4_vals {n : ℕ} (u : Fin n → Bool) (i j k l : Fin n) :
    embedQ4 u i j k l ⟨0, by decide⟩ = u ∧
    embedQ4 u i j k l ⟨1, by decide⟩ = qFlip u i ∧
    embedQ4 u i j k l ⟨2, by decide⟩ = qFlip u j ∧
    embedQ4 u i j k l ⟨3, by decide⟩ = qFlip (qFlip u i) j ∧
    embedQ4 u i j k l ⟨4, by decide⟩ = qFlip u k ∧
    embedQ4 u i j k l ⟨5, by decide⟩ = qFlip (qFlip u i) k ∧
    embedQ4 u i j k l ⟨6, by decide⟩ = qFlip (qFlip u j) k ∧
    embedQ4 u i j k l ⟨7, by decide⟩ = qFlip (qFlip (qFlip u i) j) k ∧
    embedQ4 u i j k l ⟨8, by decide⟩ = qFlip u l ∧
    embedQ4 u i j k l ⟨9, by decide⟩ = qFlip (qFlip u i) l ∧
    embedQ4 u i j k l ⟨10, by decide⟩ = qFlip (qFlip u j) l ∧
    embedQ4 u i j k l ⟨11, by decide⟩ = qFlip (qFlip (qFlip u i) j) l ∧
    embedQ4 u i j k l ⟨12, by decide⟩ = qFlip (qFlip u k) l ∧
    embedQ4 u i j k l ⟨13, by decide⟩ = qFlip (qFlip (qFlip u i) k) l ∧
    embedQ4 u i j k l ⟨14, by decide⟩ = qFlip (qFlip (qFlip u j) k) l ∧
    embedQ4 u i j k l ⟨15, by decide⟩ = qFlip (qFlip (qFlip (qFlip u i) j) k) l :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private lemma extractFacetQ3_extractQ4 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j k l : Fin n) :
    extractFacetQ3 0 (extractQ4 G u i j k l) = extractQ3 G u j k l ∧
    extractFacetQ3 1 (extractQ4 G u i j k l) = extractQ3 G (qFlip u i) j k l ∧
    extractFacetQ3 2 (extractQ4 G u i j k l) = extractQ3 G u i k l ∧
    extractFacetQ3 3 (extractQ4 G u i j k l) = extractQ3 G (qFlip u j) i k l ∧
    extractFacetQ3 4 (extractQ4 G u i j k l) = extractQ3 G u i j l ∧
    extractFacetQ3 5 (extractQ4 G u i j k l) = extractQ3 G (qFlip u k) i j l ∧
    extractFacetQ3 6 (extractQ4 G u i j k l) = extractQ3 G u i j k ∧
    extractFacetQ3 7 (extractQ4 G u i j k l) = extractQ3 G (qFlip u l) i j k := by
  rcases embedQ4_vals u i j k l with ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩
  have hij : qFlip (qFlip u i) j = qFlip (qFlip u j) i := qFlip_comm u i j
  have hik : qFlip (qFlip u i) k = qFlip (qFlip u k) i := qFlip_comm u i k
  have hjk : qFlip (qFlip u j) k = qFlip (qFlip u k) j := qFlip_comm u j k
  have hil : qFlip (qFlip u i) l = qFlip (qFlip u l) i := qFlip_comm u i l
  have hjl : qFlip (qFlip u j) l = qFlip (qFlip u l) j := qFlip_comm u j l
  have hkl : qFlip (qFlip u k) l = qFlip (qFlip u l) k := qFlip_comm u k l
  have hijk : qFlip (qFlip (qFlip u i) j) k = qFlip (qFlip (qFlip u k) i) j := by
    rw [qFlip_comm (qFlip u i) j k, qFlip_comm u i k]
  have hijl : qFlip (qFlip (qFlip u i) j) l = qFlip (qFlip (qFlip u l) i) j := by
    rw [qFlip_comm (qFlip u i) j l, qFlip_comm u i l]
  have hikl : qFlip (qFlip (qFlip u i) k) l = qFlip (qFlip (qFlip u l) i) k := by
    rw [qFlip_comm (qFlip u i) k l, qFlip_comm u i l]
  have hjkl : qFlip (qFlip (qFlip u j) k) l = qFlip (qFlip (qFlip u l) j) k := by
    rw [qFlip_comm (qFlip u j) k l, qFlip_comm u j l]
  have hijkl : qFlip (qFlip (qFlip (qFlip u i) j) k) l = qFlip (qFlip (qFlip (qFlip u l) i) j) k := by
    rw [qFlip_comm (qFlip (qFlip u i) j) k l, hijl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [extractFacetQ3]
    rw [show (0 : Fin 8).val = 0 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v0, v2, v4, v6, v8, v10, v12, v14]
  · dsimp only [extractFacetQ3]
    rw [show (1 : Fin 8).val = 1 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v1, v3, v5, v7, v9, v11, v13, v15]
  · dsimp only [extractFacetQ3]
    rw [show (2 : Fin 8).val = 2 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v0, v1, v4, v5, v8, v9, v12, v13]
  · dsimp only [extractFacetQ3]
    rw [show (3 : Fin 8).val = 3 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v2, v3, v6, v7, v10, v11, v14, v15]
    rw [hij]
  · dsimp only [extractFacetQ3]
    rw [show (4 : Fin 8).val = 4 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v0, v1, v2, v3, v8, v9, v10, v11]
  · dsimp only [extractFacetQ3]
    rw [show (5 : Fin 8).val = 5 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v4, v5, v6, v7, v12, v13, v14, v15]
    rw [hik, hjk, hijk]
  · dsimp only [extractFacetQ3]
    rw [show (6 : Fin 8).val = 6 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v0, v1, v2, v3, v4, v5, v6, v7]
  · dsimp only [extractFacetQ3]
    rw [show (7 : Fin 8).val = 7 from rfl]
    dsimp only [extractQ4, extractQ3, embedQ3]
    simp only [v8, v9, v10, v11, v12, v13, v14, v15]
    rw [hil, hjl, hijl, hkl, hikl, hjkl, hijkl]

private lemma sum_P4_inv {n : ℕ} (σ : Fin n × Fin n × Fin n × Fin n → Fin n × Fin n × Fin n × Fin n)
    (hinv : ∀ p, σ (σ p) = p) (hmem : ∀ p, p ∈ P4 n → σ p ∈ P4 n)
    (F : Fin n × Fin n × Fin n × Fin n → ℤ) :
    (∑ p ∈ P4 n, F (σ p)) = ∑ p ∈ P4 n, F p :=
  Finset.sum_bij (fun p _ => σ p) (fun p hp => hmem p hp)
    (fun p1 _ p2 _ h => by simpa [hinv] using congrArg σ h)
    (fun q hq => ⟨σ q, hmem q hq, hinv q⟩) (fun _ _ => rfl)

private lemma sum_extractQ3_base {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (fk : Fin 8) :
    (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 fk (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) =
      48 * ∑ u : Fin n → Bool, ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 := by
  have hfixed : ∀ (s : (Fin n × Fin n × Fin n × Fin n) → Fin n × Fin n × Fin n)
      (_hperm_u : (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractQ3 G u (s p).1 (s p).2.1 (s p).2.2)) =
        ∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1)),
      (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractQ3 G u (s p).1 (s p).2.1 (s p).2.2)) =
        48 * ∑ u : Fin n → Bool, ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 := by
    intro s hs; rw [hs]
    simp_rw [evalQ3U_extractQ3]
    have step1 : (∑ u : Fin n → Bool, ∑ p ∈ P4 n, ∑ w : Fin 3 → Bool, (
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.1 p.2.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.2.1 p.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.1 p.2.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.2.2.1 p.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.1 p.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.2.1 p.1)) =
      ∑ p ∈ P4 n, ∑ w : Fin 3 → Bool, ∑ u : Fin n → Bool, (
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.1 p.2.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.2.1 p.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.1 p.2.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.2.2.1 p.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.1 p.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.2.1 p.1) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
    rw [step1]
    have step2 : ∀ p ∈ P4 n, (∑ w : Fin 3 → Bool, ∑ u : Fin n → Bool, (
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.1 p.2.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.2.1 p.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.1 p.2.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.2.2.1 p.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.1 p.2.1 +
        q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.2.1 p.1)) =
      8 * ∑ u : Fin n → Bool, (
        q3OrientedTerm G u p.1 p.2.1 p.2.2.1 +
        q3OrientedTerm G u p.1 p.2.2.1 p.2.1 +
        q3OrientedTerm G u p.2.1 p.1 p.2.2.1 +
        q3OrientedTerm G u p.2.1 p.2.2.1 p.1 +
        q3OrientedTerm G u p.2.2.1 p.1 p.2.1 +
        q3OrientedTerm G u p.2.2.1 p.2.1 p.1) := by
      intro p _
      have hu : ∀ w : Fin 3 → Bool, (∑ u : Fin n → Bool, (
          q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.1 p.2.2.1 +
          q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.1 p.2.2.1 p.2.1 +
          q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.1 p.2.2.1 +
          q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.1 p.2.2.1 p.1 +
          q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.1 p.2.1 +
          q3OrientedTerm G (embedQ3 u p.1 p.2.1 p.2.2.1 w) p.2.2.1 p.2.1 p.1)) =
        ∑ u : Fin n → Bool, (
          q3OrientedTerm G u p.1 p.2.1 p.2.2.1 +
          q3OrientedTerm G u p.1 p.2.2.1 p.2.1 +
          q3OrientedTerm G u p.2.1 p.1 p.2.2.1 +
          q3OrientedTerm G u p.2.1 p.2.2.1 p.1 +
          q3OrientedTerm G u p.2.2.1 p.1 p.2.1 +
          q3OrientedTerm G u p.2.2.1 p.2.1 p.1) := fun w => sum_u_embedQ3 w p.1 p.2.1 p.2.2.1 (fun u =>
          q3OrientedTerm G u p.1 p.2.1 p.2.2.1 +
          q3OrientedTerm G u p.1 p.2.2.1 p.2.1 +
          q3OrientedTerm G u p.2.1 p.1 p.2.2.1 +
          q3OrientedTerm G u p.2.1 p.2.2.1 p.1 +
          q3OrientedTerm G u p.2.2.1 p.1 p.2.1 +
          q3OrientedTerm G u p.2.2.1 p.2.1 p.1)
      simp_rw [hu, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      push_cast; norm_num
    rw [Finset.sum_congr rfl step2, ← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_add_distrib]
    have p12 : ∀ u, (∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.2.1 p.2.1) = ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 :=
      fun u => sum_P4_inv (fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2))
        (fun ⟨a,b,c,d⟩ => rfl) (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; tauto)
        (fun p => q3OrientedTerm G u p.1 p.2.1 p.2.2.1)
    have p01 : ∀ u, (∑ p ∈ P4 n, q3OrientedTerm G u p.2.1 p.1 p.2.2.1) = ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 :=
      fun u => sum_P4_inv (fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2))
        (fun ⟨a,b,c,d⟩ => rfl) (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; refine ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.2⟩)
        (fun p => q3OrientedTerm G u p.1 p.2.1 p.2.2.1)
    have p02 : ∀ u, (∑ p ∈ P4 n, q3OrientedTerm G u p.2.2.1 p.2.1 p.1) = ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 :=
      fun u => sum_P4_inv (fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2))
        (fun ⟨a,b,c,d⟩ => rfl) (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; refine ⟨h.2.2.2.1.symm, h.2.1.symm, h.2.2.2.2.2, h.1.symm, h.2.2.2.2.1, h.2.2.1⟩)
        (fun p => q3OrientedTerm G u p.1 p.2.1 p.2.2.1)
    have p_bca : ∀ u, (∑ p ∈ P4 n, q3OrientedTerm G u p.2.1 p.2.2.1 p.1) = ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 :=
      fun u => Finset.sum_bij (fun p _ => (p.2.1, p.2.2.1, p.1, p.2.2.2))
        (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4,h1.symm,h5,h2.symm,h6,h3⟩)
        (fun ⟨_,_,_,_⟩ _ ⟨_,_,_,_⟩ _ h => by cases h; rfl)
        (fun ⟨a,b,c,d⟩ h => ⟨(c, a, b, d), by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2.symm,h4.symm,h6,h1,h3,h5⟩, rfl⟩)
        (fun _ _ => rfl)
    have p_cab : ∀ u, (∑ p ∈ P4 n, q3OrientedTerm G u p.2.2.1 p.1 p.2.1) = ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 :=
      fun u => Finset.sum_bij (fun p _ => (p.2.2.1, p.1, p.2.1, p.2.2.2))
        (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2.symm,h4.symm,h6,h1,h3,h5⟩)
        (fun ⟨_,_,_,_⟩ _ ⟨_,_,_,_⟩ _ h => by cases h; rfl)
        (fun ⟨a,b,c,d⟩ h => ⟨(b, c, a, d), by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4,h1.symm,h5,h2.symm,h6,h3⟩, rfl⟩)
        (fun _ _ => rfl)
    simp_rw [p12, p01, p02, p_bca, p_cab]
    ring
  have hf (u : Fin n → Bool) (p : Fin n × Fin n × Fin n × Fin n) :=
    extractFacetQ3_extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2
  have hflip : ∀ (sel : Fin n × Fin n × Fin n × Fin n → Fin n) (F : (Fin n → Bool) → Fin n × Fin n × Fin n × Fin n → ℤ),
      (∑ u : Fin n → Bool, ∑ p ∈ P4 n, F (qFlip u (sel p)) p) = ∑ u : Fin n → Bool, ∑ p ∈ P4 n, F u p := by
    intro sel F
    rw [Finset.sum_comm]
    have hh : ∀ p ∈ P4 n, (∑ u : Fin n → Bool, F (qFlip u (sel p)) p) = ∑ u : Fin n → Bool, F u p := fun p _ =>
      Fintype.sum_equiv
        { toFun := fun u => qFlip u (sel p)
          invFun := fun u => qFlip u (sel p)
          left_inv := fun u => qFlip_flip u (sel p)
          right_inv := fun u => qFlip_flip u (sel p) } _ _ (fun _ => rfl)
    rw [Finset.sum_congr rfl hh, Finset.sum_comm]
  have hp0 : ∀ u : Fin n → Bool, (∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.2.1 p.2.2.1 p.2.2.2)) =
      ∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1) := by
    intro u
    have hi1 := sum_P4_inv (fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2)) (fun ⟨a,b,c,d⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; refine ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.2⟩)
      (fun p => evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1))
    have hi2 := sum_P4_inv (fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2)) (fun ⟨a,b,c,d⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; refine ⟨h.2.2.2.1.symm, h.2.1.symm, h.2.2.2.2.2, h.1.symm, h.2.2.2.2.1, h.2.2.1⟩)
      (fun p => evalQ3U (extractQ3 G u p.2.1 p.1 p.2.2.1))
    have hi3 := sum_P4_inv (fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1)) (fun ⟨a,b,c,d⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h5.symm, h6.symm, h3.symm, h4, h1.symm, h2.symm⟩)
      (fun p => evalQ3U (extractQ3 G u p.2.1 p.2.2.1 p.1))
    rw [← hi1, ← hi2, ← hi3]
  have hp2 : ∀ u : Fin n → Bool, (∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.1 p.2.2.1 p.2.2.2)) =
      ∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1) := by
    intro u
    have hi1 := sum_P4_inv (fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2)) (fun ⟨a,b,c,d⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; tauto)
      (fun p => evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1))
    have hi2 := sum_P4_inv (fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1)) (fun ⟨a,b,c,d⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h3, h2, h1, h6.symm, h5.symm, h4.symm⟩)
      (fun p => evalQ3U (extractQ3 G u p.1 p.2.2.1 p.2.1))
    rw [← hi1, ← hi2]
  have hp4 : ∀ u : Fin n → Bool, (∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.2)) =
      ∑ p ∈ P4 n, evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1) := fun u =>
    sum_P4_inv (fun p => (p.1, p.2.1, p.2.2.2, p.2.2.1)) (fun ⟨a,b,c,d⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; refine ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.symm⟩)
      (fun p => evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1))
  fin_cases fk
  · -- 0: (j, k, l)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 0 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).1]
    refine hfixed (fun p => (p.2.1, p.2.2.1, p.2.2.2)) ?_
    exact Finset.sum_congr rfl fun u _ => hp0 u
  · -- 1: qFlip u i, (j, k, l)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 1 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.1]
    rw [hflip (fun p => p.1) (fun u p => evalQ3U (extractQ3 G u p.2.1 p.2.2.1 p.2.2.2))]
    refine hfixed (fun p => (p.2.1, p.2.2.1, p.2.2.2)) ?_
    exact Finset.sum_congr rfl fun u _ => hp0 u
  · -- 2: (i, k, l)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 2 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.2.1]
    refine hfixed (fun p => (p.1, p.2.2.1, p.2.2.2)) ?_
    exact Finset.sum_congr rfl fun u _ => hp2 u
  · -- 3: qFlip u j, (i, k, l)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 3 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.2.2.1]
    rw [hflip (fun p => p.2.1) (fun u p => evalQ3U (extractQ3 G u p.1 p.2.2.1 p.2.2.2))]
    refine hfixed (fun p => (p.1, p.2.2.1, p.2.2.2)) ?_
    exact Finset.sum_congr rfl fun u _ => hp2 u
  · -- 4: (i, j, l)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 4 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.2.2.2.1]
    refine hfixed (fun p => (p.1, p.2.1, p.2.2.2)) ?_
    exact Finset.sum_congr rfl fun u _ => hp4 u
  · -- 5: qFlip u k, (i, j, l)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 5 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.2.2.2.2.1]
    rw [hflip (fun p => p.2.2.1) (fun u p => evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.2))]
    refine hfixed (fun p => (p.1, p.2.1, p.2.2.2)) ?_
    exact Finset.sum_congr rfl fun u _ => hp4 u
  · -- 6: (i, j, k)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 6 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.2.2.2.2.2.1]
    exact hfixed (fun p => (p.1, p.2.1, p.2.2.1)) rfl
  · -- 7: qFlip u l, (i, j, k)
    change (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 7 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) = _
    simp_rw [(hf _ _).2.2.2.2.2.2.2]
    rw [hflip (fun p => p.2.2.2) (fun u p => evalQ3U (extractQ3 G u p.1 p.2.1 p.2.2.1))]
    exact hfixed (fun p => (p.1, p.2.1, p.2.2.1)) rfl

private lemma hsos {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℤ) :
    - ∑ a ∈ S, (f a) ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b := by
  have hid : (∑ a ∈ S, f a) ^ 2 =
      (∑ a ∈ S, (f a) ^ 2) + ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b := by
    rw [sq, Finset.sum_mul]
    have h1 : ∀ a ∈ S, f a * ∑ b ∈ S, f b = (f a) ^ 2 + ∑ b ∈ S.erase a, f a * f b := by
      intro a ha; rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ ha, sq]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hsq : (0 : ℤ) ≤ (∑ a ∈ S, f a) ^ 2 := sq_nonneg _
  linarith

private lemma hsosK {n m : ℕ} (S : Finset (Fin n)) (v : Fin n → Fin m → ℤ) :
    - ∑ a ∈ S, ∑ s : Fin m, (v a s) ^ 2 ≤
      ∑ a ∈ S, ∑ b ∈ S.erase a, ∑ s : Fin m, v a s * v b s := by
  have h1 : ∀ a ∈ S, (∑ b ∈ S.erase a, ∑ s : Fin m, v a s * v b s) =
      ∑ s : Fin m, ∑ b ∈ S.erase a, v a s * v b s := fun a _ => Finset.sum_comm
  conv_rhs => rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  calc - ∑ a ∈ S, ∑ s : Fin m, (v a s) ^ 2
      = ∑ s : Fin m, - ∑ a ∈ S, (v a s) ^ 2 := by rw [Finset.sum_neg_distrib, Finset.sum_comm]
    _ ≤ ∑ s : Fin m, ∑ a ∈ S, ∑ b ∈ S.erase a, v a s * v b s :=
        Finset.sum_le_sum fun s _ => hsos S (fun a => v a s)

private lemma sum_Q3_lower {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G ≤ Q n) (hn : 4 ≤ n) :
    384 * (D_edge * ((n - 1 : ℤ) * (n - 2) * (n - 3) * (2 * (G.edgeFinset.card : ℤ))) -
      K_Q3 * ((n : ℤ) * (n - 1) * (n - 3) * ((2 ^ n : ℕ) : ℤ))) ≤
      ∑ fk : Fin 8, ∑ u : Fin n → Bool, ∑ p ∈ P4 n,
        evalQ3U (extractFacetQ3 fk (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
  have h8 : ∀ fk : Fin 8, (∑ u : Fin n → Bool, ∑ p ∈ P4 n,
      evalQ3U (extractFacetQ3 fk (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) =
      48 * ∑ u : Fin n → Bool, ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 :=
    fun fk => sum_extractQ3_base G fk
  rw [Finset.sum_congr rfl fun fk _ => h8 fk, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hs_pull : (8 : ℤ) * (48 * ∑ u : Fin n → Bool, ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1) =
      384 * ∑ u : Fin n → Bool, ∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1 := by ring
  rw [hs_pull]
  refine Int.mul_le_mul_of_nonneg_left ?_ (by decide)
  have hdrop : ∀ u : Fin n → Bool,
      (∑ p ∈ P4 n, q3OrientedTerm G u p.1 p.2.1 p.2.2.1) =
        ((n - 3 : ℕ) : ℤ) * ∑ p ∈ P3 n, q3OrientedTerm G u p.1 p.2.1 p.2.2 := by
    intro u
    have h := sum_P4_dropL (fun i j k => q3OrientedTerm G u i j k)
    simpa [nsmul_eq_mul] using h
  simp_rw [hdrop, ← Finset.mul_sum]
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Int.ofNat_sub (by omega)
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Int.ofNat_sub (by omega)
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Int.ofNat_sub (by omega)
  have hinner : ∀ u : Fin n → Bool, ∀ i : Fin n,
      (if G.Adj u (qFlip u i) then ((n - 1 : ℤ) * (n - 2) * D_edge) else 0) - (n - 1 : ℤ) * K_Q3 ≤
        ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1, q3OrientedTerm G u i j1 j2 := by
    intro u i
    set S := Finset.univ.erase i
    have hScard : S.card = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    have hScardZ : (S.card : ℤ) = (n : ℤ) - 1 := by rw [hScard, hn1]
    by_cases hadj : G.Adj u (qFlip u i)
    · simp only [hadj, ↓reduceIte]
      have hterm : ∀ j1 j2, q3OrientedTerm G u i j1 j2 =
          D_edge + ∑ s : Fin 8, q3W0 s (edgeFlag G u i j1) * q3W0 s (edgeFlag G u i j2) := by
        intro j1 j2
        unfold q3OrientedTerm q3EdgeTerm edgeFlag
        simp only [hadj, decide_true, ↓reduceIte]
        rw [Fin.sum_univ_eight]
      simp_rw [hterm, Finset.sum_add_distrib]
      have hconst : (∑ j1 ∈ S, ∑ _j2 ∈ S.erase j1, D_edge) = (n - 1 : ℤ) * (n - 2) * D_edge := by
        have h1 : ∀ j1 ∈ S, (∑ _j2 ∈ S.erase j1, D_edge) = ((n - 2 : ℤ) * D_edge) := by
          intro j1 hj1
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj1, hScard, show n - 1 - 1 = n - 2 by omega, hn2]
        rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, hScardZ]; ring
      have hsosW := hsosK S (fun j s => q3W0 s (edgeFlag G u i j))
      have hbound : ∑ j ∈ S, ∑ s : Fin 8, q3W0 s (edgeFlag G u i j) ^ 2 ≤ (n - 1 : ℤ) * K_Q3 := by
        calc ∑ j ∈ S, ∑ s : Fin 8, q3W0 s (edgeFlag G u i j) ^ 2
            ≤ ∑ _j ∈ S, K_Q3 := Finset.sum_le_sum fun j _ => by
              rw [Fin.sum_univ_eight]; exact q3W0_sq_le _
          _ = (n - 1 : ℤ) * K_Q3 := by rw [Finset.sum_const, nsmul_eq_mul, hScardZ]
      linarith
    · simp only [hadj, ↓reduceIte]
      have hterm : ∀ j1 j2, q3OrientedTerm G u i j1 j2 =
          ∑ s : Fin 8, q3U1 s (edgeFlag G u i j1) * q3U1 s (edgeFlag G u i j2) := by
        intro j1 j2
        unfold q3OrientedTerm q3EdgeTerm edgeFlag
        simp only [hadj, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [Fin.sum_univ_eight]
      simp_rw [hterm]
      have hsosU := hsosK S (fun j s => q3U1 s (edgeFlag G u i j))
      have hbound : ∑ j ∈ S, ∑ s : Fin 8, q3U1 s (edgeFlag G u i j) ^ 2 ≤ (n - 1 : ℤ) * K_Q3 := by
        calc ∑ j ∈ S, ∑ s : Fin 8, q3U1 s (edgeFlag G u i j) ^ 2
            ≤ ∑ _j ∈ S, K_Q3 := Finset.sum_le_sum fun j _ => by
              rw [Fin.sum_univ_eight]; exact q3U1_sq_le _
          _ = (n - 1 : ℤ) * K_Q3 := by rw [Finset.sum_const, nsmul_eq_mul, hScardZ]
      linarith
  have hsum_all :
      D_edge * ((n - 1 : ℤ) * (n - 2) * (2 * (G.edgeFinset.card : ℤ))) -
        K_Q3 * ((n : ℤ) * (n - 1) * ((2 ^ n : ℕ) : ℤ)) ≤
      ∑ u : Fin n → Bool, ∑ p ∈ P3 n, q3OrientedTerm G u p.1 p.2.1 p.2.2 := by
    have hP3 : ∀ u, (∑ p ∈ P3 n, q3OrientedTerm G u p.1 p.2.1 p.2.2) =
        ∑ i : Fin n, ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
          q3OrientedTerm G u i j1 j2 := fun u => sum_P3 _
    simp_rw [hP3]
    have hle : (∑ u : Fin n → Bool, ∑ i : Fin n,
        ((if G.Adj u (qFlip u i) then ((n - 1 : ℤ) * (n - 2) * D_edge) else 0) - (n - 1 : ℤ) * K_Q3)) ≤
        ∑ u : Fin n → Bool, ∑ i : Fin n, ∑ j1 ∈ Finset.univ.erase i,
          ∑ j2 ∈ (Finset.univ.erase i).erase j1, q3OrientedTerm G u i j1 j2 :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun i _ => hinner u i
    have h2e : (2 * (G.edgeFinset.card : ℤ)) =
        ∑ u : Fin n → Bool, ∑ i : Fin n, (if G.Adj u (qFlip u i) then (1 : ℤ) else 0) := by
      have h := congrArg (Nat.cast (R := ℤ)) (twice_card_edges_eq_sum_oriented G hG)
      simp only [Finset.card_filter] at h
      push_cast at h
      refine h.trans (Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => ?_)
      split_ifs <;> rfl
    have hlhs : (∑ u : Fin n → Bool, ∑ i : Fin n,
        ((if G.Adj u (qFlip u i) then ((n - 1 : ℤ) * (n - 2) * D_edge) else 0) - (n - 1 : ℤ) * K_Q3)) =
        D_edge * ((n - 1 : ℤ) * (n - 2) * (2 * (G.edgeFinset.card : ℤ))) -
          K_Q3 * ((n : ℤ) * (n - 1) * ((2 ^ n : ℕ) : ℤ)) := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      have hite : ∀ u i, (if G.Adj u (qFlip u i) then ((n - 1 : ℤ) * (n - 2) * D_edge) else 0) =
          (if G.Adj u (qFlip u i) then (1 : ℤ) else 0) * ((n - 1 : ℤ) * (n - 2) * D_edge) := by
        intro u i; split_ifs <;> ring
      simp_rw [hite, ← Finset.sum_mul, h2e]; ring
    linarith
  have hm3 : (0 : ℤ) ≤ ((n - 3 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hm := Int.mul_le_mul_of_nonneg_left hsum_all hm3
  rw [hn3] at hm ⊢
  linarith

private lemma embedQ4_bit_split {n : ℕ} (u : Fin n → Bool) (i j k l : Fin n) (v : Fin 16) :
    embedQ4 u i j k l v =
      (let u1 := if decide (v.val % 2 = 1) then qFlip u i else u
       let u2 := if decide ((v.val / 2) % 2 = 1) then qFlip u1 j else u1
       let u3 := if decide ((v.val / 4) % 2 = 1) then qFlip u2 k else u2
       if decide ((v.val / 8) % 2 = 1) then qFlip u3 l else u3) := by
  simp only [embedQ4, decide_eq_true_eq]

private lemma flip_ite_comm {n : ℕ} (a b : Bool) (u : Fin n → Bool) (x y : Fin n) :
    (if a then qFlip (if b then qFlip u y else u) x else (if b then qFlip u y else u)) =
      (if b then qFlip (if a then qFlip u x else u) y else (if a then qFlip u x else u)) := by
  cases a <;> cases b <;> simp [qFlip_comm]

private lemma flip_ite_xor {n : ℕ} (a b : Bool) (u : Fin n → Bool) (x : Fin n) :
    (if a then qFlip (if b then qFlip u x else u) x else (if b then qFlip u x else u)) =
      (if (xor b a) then qFlip u x else u) := by
  cases a <;> cases b <;> simp [qFlip_flip]

private def xor16 (v w : Fin 16) : Fin 16 :=
  ⟨(v.val ^^^ w.val) % 16, Nat.mod_lt _ (by decide)⟩

private lemma embedQ4_xor {n : ℕ} (u : Fin n → Bool) (i j k l : Fin n) (v w : Fin 16) :
    embedQ4 (embedQ4 u i j k l v) i j k l w = embedQ4 u i j k l (xor16 v w) := by
  let f := fun (a b c d : Bool) (x : Fin n → Bool) =>
    let x1 := if a then qFlip x i else x
    let x2 := if b then qFlip x1 j else x1
    let x3 := if c then qFlip x2 k else x2
    if d then qFlip x3 l else x3
  have hf_comp : ∀ a0 a1 a2 a3 b0 b1 b2 b3 (x : Fin n → Bool),
      f b0 b1 b2 b3 (f a0 a1 a2 a3 x) = f (xor a0 b0) (xor a1 b1) (xor a2 b2) (xor a3 b3) x := by
    intro a0 a1 a2 a3 b0 b1 b2 b3 x
    dsimp only [f]
    -- commute b0 inward to a0, b1 to a1, b2 to a2, b3 stays outer
    have c1 : ∀ y, (if b0 then qFlip (if a3 then qFlip (if a2 then qFlip (if a1 then qFlip y j else y) k else (if a1 then qFlip y j else y)) l else (if a2 then qFlip (if a1 then qFlip y j else y) k else (if a1 then qFlip y j else y))) i
        else (if a3 then qFlip (if a2 then qFlip (if a1 then qFlip y j else y) k else (if a1 then qFlip y j else y)) l else (if a2 then qFlip (if a1 then qFlip y j else y) k else (if a1 then qFlip y j else y)))) =
        (if a3 then qFlip (if a2 then qFlip (if a1 then qFlip (if b0 then qFlip y i else y) j else (if b0 then qFlip y i else y)) k else (if a1 then qFlip (if b0 then qFlip y i else y) j else (if b0 then qFlip y i else y))) l else (if a2 then qFlip (if a1 then qFlip (if b0 then qFlip y i else y) j else (if b0 then qFlip y i else y)) k else (if a1 then qFlip (if b0 then qFlip y i else y) j else (if b0 then qFlip y i else y)))) := by
      intro y; rw [flip_ite_comm b0 a3, flip_ite_comm b0 a2, flip_ite_comm b0 a1]
    rw [c1, flip_ite_xor b0 a0]
    have c2 : ∀ y, (if b1 then qFlip (if a3 then qFlip (if a2 then qFlip y k else y) l else (if a2 then qFlip y k else y)) j
        else (if a3 then qFlip (if a2 then qFlip y k else y) l else (if a2 then qFlip y k else y))) =
        (if a3 then qFlip (if a2 then qFlip (if b1 then qFlip y j else y) k else (if b1 then qFlip y j else y)) l else (if a2 then qFlip (if b1 then qFlip y j else y) k else (if b1 then qFlip y j else y))) := by
      intro y; rw [flip_ite_comm b1 a3, flip_ite_comm b1 a2]
    rw [c2, flip_ite_xor b1 a1, flip_ite_comm b2 a3, flip_ite_xor b2 a2, flip_ite_xor b3 a3]
  have hbits : ∀ (v w : Fin 16),
      xor (decide (v.val % 2 = 1)) (decide (w.val % 2 = 1)) = decide ((xor16 v w).val % 2 = 1) ∧
      xor (decide ((v.val / 2) % 2 = 1)) (decide ((w.val / 2) % 2 = 1)) = decide (((xor16 v w).val / 2) % 2 = 1) ∧
      xor (decide ((v.val / 4) % 2 = 1)) (decide ((w.val / 4) % 2 = 1)) = decide (((xor16 v w).val / 4) % 2 = 1) ∧
      xor (decide ((v.val / 8) % 2 = 1)) (decide ((w.val / 8) % 2 = 1)) = decide (((xor16 v w).val / 8) % 2 = 1) := by
    decide
  rcases hbits v w with ⟨hb0, hb1, hb2, hb3⟩
  rw [embedQ4_bit_split, embedQ4_bit_split, embedQ4_bit_split]
  change f (decide (w.val % 2 = 1)) (decide ((w.val / 2) % 2 = 1)) (decide ((w.val / 4) % 2 = 1)) (decide ((w.val / 8) % 2 = 1))
    (f (decide (v.val % 2 = 1)) (decide ((v.val / 2) % 2 = 1)) (decide ((v.val / 4) % 2 = 1)) (decide ((v.val / 8) % 2 = 1)) u) =
    f (decide ((xor16 v w).val % 2 = 1)) (decide (((xor16 v w).val / 2) % 2 = 1)) (decide (((xor16 v w).val / 4) % 2 = 1)) (decide (((xor16 v w).val / 8) % 2 = 1)) u
  rw [hf_comp, hb0, hb1, hb2, hb3]

private def allFin16 (P : Fin 16 → Bool) : Bool :=
  (List.range 16).all fun i => if h : i < 16 then P ⟨i, h⟩ else true

private lemma allFin16_ok {P : Fin 16 → Bool} (h : allFin16 P = true) (x : Fin 16) : P x = true := by
  have hx : x.val ∈ List.range 16 := List.mem_range.mpr x.isLt
  simp only [allFin16, List.all_eq_true] at h
  have h1 := h x.val hx; simp [x.isLt] at h1; exact h1

private def checkBallEdgeXor : Bool :=
  allFin16 fun v => allFin16 fun k =>
    let epV := edgeEndpointsQ4 (ballEdge v k)
    let ep0 := edgeEndpointsQ4 (ballEdge 0 k)
    let a := xor16 v ep0.1
    let b := xor16 v ep0.2
    decide (epV = (a, b)) || decide (epV = (b, a))

private lemma checkBallEdgeXor_ok : checkBallEdgeXor = true := by decide

private lemma extractBallB2_extractQ4 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j k l : Fin n) (v : Fin 16) :
    extractBallB2 v (extractQ4 G u i j k l) =
      extractBallB2 0 (extractQ4 G (embedQ4 u i j k l v) i j k l) := by
  have he : ∀ m : Fin 16,
      getB2Edge (extractBallB2 v (extractQ4 G u i j k l)) m =
        getB2Edge (extractBallB2 0 (extractQ4 G (embedQ4 u i j k l v) i j k l)) m := by
    intro m
    rw [getB2Edge_extractBallB2, getB2Edge_extractBallB2, getQ4E_extractQ4, getQ4E_extractQ4]
    have hc := allFin16_ok (allFin16_ok checkBallEdgeXor_ok v) m
    dsimp only at hc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with hdir | hrev
    · rw [hdir, embedQ4_xor, embedQ4_xor]
    · rw [hrev, embedQ4_xor, embedQ4_xor, decide_adj_comm]
  have h0 := he 0; have h1 := he 1; have h2 := he 2; have h3 := he 3
  have h4 := he 4; have h5 := he 5; have h6 := he 6; have h7 := he 7
  have h8 := he 8; have h9 := he 9; have h10 := he 10; have h11 := he 11
  have h12 := he 12; have h13 := he 13; have h14 := he 14; have h15 := he 15
  dsimp only [getB2Edge, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  cases hb1 : extractBallB2 v (extractQ4 G u i j k l)
  cases hb2 : extractBallB2 0 (extractQ4 G (embedQ4 u i j k l v) i j k l)
  rw [hb1, hb2] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp only at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  congr

private def b4Raw {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (a b c d : Fin n) : ℤ :=
  b4Pair (decide (G.Adj u (qFlip u a))) (decide (G.Adj u (qFlip u b)))
    (decide (G.Adj (qFlip u a) (qFlip (qFlip u a) b))) (decide (G.Adj (qFlip u b) (qFlip (qFlip u b) a)))
    (decide (G.Adj u (qFlip u c))) (decide (G.Adj u (qFlip u d)))
    (decide (G.Adj (qFlip u c) (qFlip (qFlip u c) d))) (decide (G.Adj (qFlip u d) (qFlip (qFlip u d) c)))

private def q2Raw {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (a b c d : Fin n) : ℤ :=
  q2Term (decide (G.Adj u (qFlip u a))) (decide (G.Adj u (qFlip u b)))
    (decide (G.Adj (qFlip u a) (qFlip (qFlip u a) b))) (decide (G.Adj (qFlip u b) (qFlip (qFlip u b) a)))
    (decide (G.Adj u (qFlip u c))) (decide (G.Adj (qFlip u a) (qFlip (qFlip u a) c)))
    (decide (G.Adj (qFlip u b) (qFlip (qFlip u b) c))) (decide (G.Adj (qFlip u c) (qFlip (qFlip u c) a)))
    (decide (G.Adj (qFlip u c) (qFlip (qFlip u c) b)))
    (decide (G.Adj u (qFlip u d))) (decide (G.Adj (qFlip u a) (qFlip (qFlip u a) d)))
    (decide (G.Adj (qFlip u b) (qFlip (qFlip u b) d))) (decide (G.Adj (qFlip u d) (qFlip (qFlip u d) a)))
    (decide (G.Adj (qFlip u d) (qFlip (qFlip u d) b)))

private lemma evalB2U_extractBallB2_0 {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (i j k l : Fin n) :
    evalB2U (extractBallB2 0 (extractQ4 G u i j k l)) =
      (8 * b4Raw G u i j k l + 8 * b4Raw G u i k j l + 8 * b4Raw G u i l j k) +
      (2 * q2Raw G u i j k l + 2 * q2Raw G u i k j l + 2 * q2Raw G u i l j k + 2 * q2Raw G u j i k l +
       2 * q2Raw G u j k i l + 2 * q2Raw G u j l i k + 2 * q2Raw G u k i j l + 2 * q2Raw G u k j i l +
       2 * q2Raw G u k l i j + 2 * q2Raw G u l i j k + 2 * q2Raw G u l j i k + 2 * q2Raw G u l k i j) := by
  rcases embedQ4_vals u i j k l with ⟨v0, v1, v2, v3, v4, v5, v6, _, v8, v9, v10, _, v12, _, _, _⟩
  dsimp only [evalB2U, b2UngaugedBool, extractBallB2, extractQ4, b4Raw, q2Raw]
  simp only [Fin.val_zero, v0, v1, v2, v3, v4, v5, v6, v8, v9, v10, v12]
  have hf_ji : qFlip (qFlip u j) i = qFlip (qFlip u i) j := qFlip_comm u j i
  have hf_ki : qFlip (qFlip u k) i = qFlip (qFlip u i) k := qFlip_comm u k i
  have hf_li : qFlip (qFlip u l) i = qFlip (qFlip u i) l := qFlip_comm u l i
  have hf_kj : qFlip (qFlip u k) j = qFlip (qFlip u j) k := qFlip_comm u k j
  have hf_lj : qFlip (qFlip u l) j = qFlip (qFlip u j) l := qFlip_comm u l j
  have hf_lk : qFlip (qFlip u l) k = qFlip (qFlip u k) l := qFlip_comm u l k
  simp only [hf_ji, hf_ki, hf_li, hf_kj, hf_lj, hf_lk]

private lemma sum_P4_bij {n : ℕ}
    (σ τ : Fin n × Fin n × Fin n × Fin n → Fin n × Fin n × Fin n × Fin n)
    (hστ : ∀ p, σ (τ p) = p) (hτσ : ∀ p, τ (σ p) = p)
    (hσ : ∀ p, p ∈ P4 n → σ p ∈ P4 n) (hτ : ∀ p, p ∈ P4 n → τ p ∈ P4 n)
    (F : Fin n × Fin n × Fin n × Fin n → ℤ) :
    (∑ p ∈ P4 n, F (σ p)) = ∑ p ∈ P4 n, F p :=
  Finset.sum_bij (fun p _ => σ p) (fun p hp => hσ p hp)
    (fun p1 _ p2 _ h => by simpa [hτσ] using congrArg τ h)
    (fun q hq => ⟨τ q, hτ q hq, hστ q⟩) (fun _ _ => rfl)

private lemma sum_P4_perm_collapse {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℤ) :
    (∑ p ∈ P4 n, (
      (8 * F p.1 p.2.1 p.2.2.1 p.2.2.2 + 8 * F p.1 p.2.2.1 p.2.1 p.2.2.2 + 8 * F p.1 p.2.2.2 p.2.1 p.2.2.1))) =
      24 * ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : (∑ p ∈ P4 n, F p.1 p.2.2.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    sum_P4_bij (fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2)) (fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2,h1,h3,h4.symm,h6,h5⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2,h1,h3,h4.symm,h6,h5⟩)
      (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)
  have h2 : (∑ p ∈ P4 n, F p.1 p.2.2.2 p.2.1 p.2.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    sum_P4_bij (fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1)) (fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h3,h1,h2,h5.symm,h6.symm,h4⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2,h3,h1,h6,h4.symm,h5.symm⟩)
      (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)
  rw [h1, h2]; ring

private lemma sum_P4_perm12_collapse {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → ℤ) :
    (∑ p ∈ P4 n, (
      2 * F p.1 p.2.1 p.2.2.1 p.2.2.2 + 2 * F p.1 p.2.2.1 p.2.1 p.2.2.2 +
      2 * F p.1 p.2.2.2 p.2.1 p.2.2.1 + 2 * F p.2.1 p.1 p.2.2.1 p.2.2.2 +
      2 * F p.2.1 p.2.2.1 p.1 p.2.2.2 + 2 * F p.2.1 p.2.2.2 p.1 p.2.2.1 +
      2 * F p.2.2.1 p.1 p.2.1 p.2.2.2 + 2 * F p.2.2.1 p.2.1 p.1 p.2.2.2 +
      2 * F p.2.2.1 p.2.2.2 p.1 p.2.1 + 2 * F p.2.2.2 p.1 p.2.1 p.2.2.1 +
      2 * F p.2.2.2 p.2.1 p.1 p.2.2.1 + 2 * F p.2.2.2 p.2.2.1 p.1 p.2.1)) =
      24 * ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have mkBij : ∀ (σ τ : Fin n × Fin n × Fin n × Fin n → Fin n × Fin n × Fin n × Fin n),
      (∀ p, σ (τ p) = p) → (∀ p, τ (σ p) = p) →
      (∀ p, p ∈ P4 n → σ p ∈ P4 n) → (∀ p, p ∈ P4 n → τ p ∈ P4 n) →
      (∑ p ∈ P4 n, F (σ p).1 (σ p).2.1 (σ p).2.2.1 (σ p).2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    fun σ τ h1 h2 h3 h4 => sum_P4_bij σ τ h1 h2 h3 h4 (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)
  have p_ikjl : (∑ p ∈ P4 n, F p.1 p.2.2.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2)) (fun p => (p.1, p.2.2.1, p.2.1, p.2.2.2))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2,h1,h3,h4.symm,h6,h5⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2,h1,h3,h4.symm,h6,h5⟩)
  have p_iljk : (∑ p ∈ P4 n, F p.1 p.2.2.2 p.2.1 p.2.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.1, p.2.2.2, p.2.1, p.2.2.1)) (fun p => (p.1, p.2.2.1, p.2.2.2, p.2.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h3,h1,h2,h5.symm,h6.symm,h4⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2,h3,h1,h6,h4.symm,h5.symm⟩)
  have p_jikl : (∑ p ∈ P4 n, F p.2.1 p.1 p.2.2.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2)) (fun p => (p.2.1, p.1, p.2.2.1, p.2.2.2))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h1.symm,h4,h5,h2,h3,h6⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h1.symm,h4,h5,h2,h3,h6⟩)
  have p_jkil : (∑ p ∈ P4 n, F p.2.1 p.2.2.1 p.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2)) (fun p => (p.2.2.1, p.1, p.2.1, p.2.2.2))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4,h1.symm,h5,h2.symm,h6,h3⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2.symm,h4.symm,h6,h1,h3,h5⟩)
  have p_jlik : (∑ p ∈ P4 n, F p.2.1 p.2.2.2 p.1 p.2.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.1, p.2.2.2, p.1, p.2.2.1)) (fun p => (p.2.2.1, p.1, p.2.2.2, p.2.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h5,h1.symm,h4,h3.symm,h6.symm,h2⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2.symm,h6,h4.symm,h3,h1,h5.symm⟩)
  have p_kijl : (∑ p ∈ P4 n, F p.2.2.1 p.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.2.1, p.1, p.2.1, p.2.2.2)) (fun p => (p.2.1, p.2.2.1, p.1, p.2.2.2))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h2.symm,h4.symm,h6,h1,h3,h5⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4,h1.symm,h5,h2.symm,h6,h3⟩)
  have p_kjil : (∑ p ∈ P4 n, F p.2.2.1 p.2.1 p.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2)) (fun p => (p.2.2.1, p.2.1, p.1, p.2.2.2))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4.symm,h2.symm,h6,h1.symm,h5,h3⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4.symm,h2.symm,h6,h1.symm,h5,h3⟩)
  have p_klij : (∑ p ∈ P4 n, F p.2.2.1 p.2.2.2 p.1 p.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1)) (fun p => (p.2.2.1, p.2.2.2, p.1, p.2.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h6,h2.symm,h4.symm,h3.symm,h5.symm,h1⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h6,h2.symm,h4.symm,h3.symm,h5.symm,h1⟩)
  have p_lijk : (∑ p ∈ P4 n, F p.2.2.2 p.1 p.2.1 p.2.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.2.2, p.1, p.2.1, p.2.2.1)) (fun p => (p.2.1, p.2.2.1, p.2.2.2, p.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h3.symm,h5.symm,h6.symm,h1,h2,h4⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4,h5,h1.symm,h6,h2.symm,h3.symm⟩)
  have p_ljik : (∑ p ∈ P4 n, F p.2.2.2 p.2.1 p.1 p.2.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.2.2, p.2.1, p.1, p.2.2.1)) (fun p => (p.2.2.1, p.2.1, p.2.2.2, p.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h5.symm,h3.symm,h6.symm,h1.symm,h4,h2⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h4.symm,h6,h2.symm,h5,h1.symm,h3.symm⟩)
  have p_lkij : (∑ p ∈ P4 n, F p.2.2.2 p.2.2.1 p.1 p.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
    mkBij (fun p => (p.2.2.2, p.2.2.1, p.1, p.2.1)) (fun p => (p.2.2.1, p.2.2.2, p.2.1, p.1))
      (fun ⟨_,_,_,_⟩ => rfl) (fun ⟨_,_,_,_⟩ => rfl)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h6.symm,h3.symm,h5.symm,h2.symm,h4.symm,h1⟩)
      (fun ⟨a,b,c,d⟩ h => by simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢; rcases h with ⟨h1,h2,h3,h4,h5,h6⟩; exact ⟨h6,h4.symm,h2.symm,h5.symm,h3.symm,h1.symm⟩)
  rw [p_ikjl, p_iljk, p_jikl, p_jkil, p_jlik, p_kijl, p_kjil, p_klij, p_lijk, p_ljik, p_lkij]
  ring

private lemma b4Raw_ge_neg {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (u : Fin n → Bool) (a b c d : Fin n) :
    - K_B4 ≤ b4Raw G u a b c d := by
  unfold b4Raw b4Pair
  set c1 := rcIdx (decide (G.Adj u (qFlip u a))) (decide (G.Adj u (qFlip u b)))
    (decide (G.Adj (qFlip u a) (qFlip (qFlip u a) b))) (decide (G.Adj (qFlip u b) (qFlip (qFlip u b) a)))
  set c2 := rcIdx (decide (G.Adj u (qFlip u c))) (decide (G.Adj u (qFlip u d)))
    (decide (G.Adj (qFlip u c) (qFlip (qFlip u c) d))) (decide (G.Adj (qFlip u d) (qFlip (qFlip u d) c)))
  have h1 := b4V_sq_le c1
  have h2 := b4V_sq_le c2
  have hsq : ∀ s : Fin 10, (0 : ℤ) ≤ (b4V s c1 + b4V s c2) ^ 2 := fun s => sq_nonneg _
  have h0 := hsq 0; have hs1 := hsq 1; have hs2 := hsq 2; have hs3 := hsq 3; have hs4 := hsq 4
  have hs5 := hsq 5; have hs6 := hsq 6; have hs7 := hsq 7; have hs8 := hsq 8; have hs9 := hsq 9
  linarith

private lemma sum_B4_lower {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (hn : 4 ≤ n) :
    - K_B4 * ((n : ℤ) * (n - 1) * (4 * n - 6) * ((2 ^ n : ℕ) : ℤ)) ≤
      ∑ u : Fin n → Bool, ∑ p ∈ P4 n, b4Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hu : ∀ u : Fin n → Bool,
      - K_B4 * ((n : ℤ) * (n - 1) * (4 * n - 6)) ≤ ∑ p ∈ P4 n, b4Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    intro u
    let v : (Fin n × Fin n) → Fin 10 → ℤ := fun p s =>
      b4V s (rcIdx (decide (G.Adj u (qFlip u p.1))) (decide (G.Adj u (qFlip u p.2)))
        (decide (G.Adj (qFlip u p.1) (qFlip (qFlip u p.1) p.2))) (decide (G.Adj (qFlip u p.2) (qFlip (qFlip u p.2) p.1))))
    have hb4_dot : ∀ a b c d, b4Raw G u a b c d = ∑ s : Fin 10, v (a, b) s * v (c, d) s := by
      intro a b c d; unfold b4Raw b4Pair
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, v]; ring
    have hfull : (0 : ℤ) ≤ ∑ p1 ∈ P2 n, ∑ p2 ∈ P2 n, b4Raw G u p1.1 p1.2 p2.1 p2.2 := by
      have hsq : ∀ p1 p2, b4Raw G u p1.1 p1.2 p2.1 p2.2 = ∑ s : Fin 10, v p1 s * v p2 s :=
        fun p1 p2 => hb4_dot p1.1 p1.2 p2.1 p2.2
      simp_rw [hsq]
      have hcomm : (∑ p1 ∈ P2 n, ∑ p2 ∈ P2 n, ∑ s : Fin 10, v p1 s * v p2 s) =
          ∑ s : Fin 10, (∑ p ∈ P2 n, v p s) ^ 2 := by
        have h1 : ∀ p1 ∈ P2 n, (∑ p2 ∈ P2 n, ∑ s : Fin 10, v p1 s * v p2 s) =
            ∑ s : Fin 10, ∑ p2 ∈ P2 n, v p1 s * v p2 s := fun p1 _ => Finset.sum_comm
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p1 _ => ?_
        rw [Finset.mul_sum]
      rw [hcomm]
      exact Finset.sum_nonneg fun s _ => sq_nonneg _
    -- Map P4 n into P2 n ×ˢ P2 n cleanly via `Finset.filter`
    let QP := P2 n ×ˢ P2 n
    let Q4 := QP.filter (fun q : (Fin n × Fin n) × (Fin n × Fin n) =>
      q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧ q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2)
    have hQ4_eq : (∑ p ∈ P4 n, b4Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2) =
        ∑ q ∈ Q4, b4Raw G u q.1.1 q.1.2 q.2.1 q.2.2 := by
      refine Finset.sum_bij (fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) ?_ ?_ ?_ ?_
      · intro ⟨a, b, c, d⟩ hp
        simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Q4, QP, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        exact ⟨⟨hp.1, hp.2.2.2.2.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩
      · intro ⟨_,_,_,_⟩ _ ⟨_,_,_,_⟩ _ h; cases h; rfl
      · intro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
        simp only [Q4, QP, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq
        refine ⟨(a, b, c, d), ?_, rfl⟩
        simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq.1.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2, hq.1.2⟩
      · intro _ _; rfl
    have hQ4_card : Q4.card = (P4 n).card := by
      rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
      refine (Finset.sum_bij (fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) ?_ ?_ ?_ ?_).symm
      · intro ⟨a, b, c, d⟩ hp
        simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Q4, QP, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        exact ⟨⟨hp.1, hp.2.2.2.2.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩
      · intro ⟨_,_,_,_⟩ _ ⟨_,_,_,_⟩ _ h; cases h; rfl
      · intro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hq
        simp only [Q4, QP, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq
        refine ⟨(a, b, c, d), ?_, rfl⟩
        simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq.1.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2, hq.1.2⟩
      · intro _ _; rfl
    have hQ4_sub : Q4 ⊆ QP := Finset.filter_subset
      (fun q : (Fin n × Fin n) × (Fin n × Fin n) =>
        q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧ q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2) QP
    have hsdiff := Finset.sum_sdiff hQ4_sub (f := fun q : (Fin n × Fin n) × (Fin n × Fin n) => b4Raw G u q.1.1 q.1.2 q.2.1 q.2.2)
    have hQ_sum : (∑ q ∈ QP, b4Raw G u q.1.1 q.1.2 q.2.1 q.2.2) =
        ∑ p1 ∈ P2 n, ∑ p2 ∈ P2 n, b4Raw G u p1.1 p1.2 p2.1 p2.2 :=
      Finset.sum_product' (P2 n) (P2 n) (fun p1 p2 => b4Raw G u p1.1 p1.2 p2.1 p2.2)
    have hdiff_card : ((QP \ Q4).card : ℤ) = (n : ℤ) * (n - 1) * (4 * n - 6) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hQ4_sub]
      have hle : Q4.card ≤ QP.card := Finset.card_le_card hQ4_sub
      have hQcard : QP.card = (n * (n - 1)) * (n * (n - 1)) := by
        simp only [QP, Finset.card_product, P2_card]
      rw [Int.ofNat_sub hle, hQcard, hQ4_card, P4_card]
      have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Int.ofNat_sub (by omega)
      have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Int.ofNat_sub (by omega)
      have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Int.ofNat_sub (by omega)
      push_cast; rw [hn1, hn2, hn3]; ring
    rw [← hQ_sum] at hfull
    rw [hQ4_eq]
    have hle_pos : ∀ a b c d, b4Raw G u a b c d ≤ K_B4 := by
      intro a b c d
      unfold b4Raw b4Pair
      set c1 := rcIdx (decide (G.Adj u (qFlip u a))) (decide (G.Adj u (qFlip u b)))
        (decide (G.Adj (qFlip u a) (qFlip (qFlip u a) b))) (decide (G.Adj (qFlip u b) (qFlip (qFlip u b) a)))
      set c2 := rcIdx (decide (G.Adj u (qFlip u c))) (decide (G.Adj u (qFlip u d)))
        (decide (G.Adj (qFlip u c) (qFlip (qFlip u c) d))) (decide (G.Adj (qFlip u d) (qFlip (qFlip u d) c)))
      have h1 := b4V_sq_le c1
      have h2 := b4V_sq_le c2
      have hsq : ∀ s : Fin 10, (0 : ℤ) ≤ (b4V s c1 - b4V s c2) ^ 2 := fun s => sq_nonneg _
      have h0 := hsq 0; have hs1 := hsq 1; have hs2 := hsq 2; have hs3 := hsq 3; have hs4 := hsq 4
      have hs5 := hsq 5; have hs6 := hsq 6; have hs7 := hsq 7; have hs8 := hsq 8; have hs9 := hsq 9
      linarith
    have hrem_upper : ∑ q ∈ QP \ Q4, b4Raw G u q.1.1 q.1.2 q.2.1 q.2.2 ≤ ((QP \ Q4).card : ℤ) * K_B4 := by
      calc ∑ q ∈ QP \ Q4, b4Raw G u q.1.1 q.1.2 q.2.1 q.2.2
          ≤ ∑ _q ∈ QP \ Q4, K_B4 := Finset.sum_le_sum fun q _ => hle_pos _ _ _ _
        _ = ((QP \ Q4).card : ℤ) * K_B4 := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hdiff_card] at hrem_upper
    linarith
  calc - K_B4 * ((n : ℤ) * (n - 1) * (4 * n - 6) * ((2 ^ n : ℕ) : ℤ))
      = ∑ _u : Fin n → Bool, (- K_B4 * ((n : ℤ) * (n - 1) * (4 * n - 6))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ ∑ u : Fin n → Bool, ∑ p ∈ P4 n, b4Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 := Finset.sum_le_sum fun u _ => hu u

private lemma sum_Q2_lower {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (hn : 4 ≤ n) :
    - K_Q2 * ((n : ℤ) * (n - 1) * (n - 2) * ((2 ^ n : ℕ) : ℤ)) ≤
      ∑ u : Fin n → Bool, ∑ p ∈ P4 n, q2Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hu : ∀ u : Fin n → Bool,
      - K_Q2 * ((n : ℤ) * (n - 1) * (n - 2)) ≤ ∑ p ∈ P4 n, q2Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    intro u
    rw [sum_P4]
    have hij_bound : ∀ i : Fin n, ∀ j ∈ Finset.univ.erase i,
        - K_Q2 * ((n : ℤ) - 2) ≤ ∑ k ∈ (Finset.univ.erase i).erase j,
          ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, q2Raw G u i j k l := by
      intro i j hj
      set S := (Finset.univ.erase i).erase j
      have hScard : S.card = n - 2 := by
        rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]; omega
      have hScardZ : (S.card : ℤ) = (n : ℤ) - 2 := by
        rw [hScard]; simp only [Int.ofNat_sub (by omega : 2 ≤ n)]; push_cast; rfl
      set ca := decide (G.Adj u (qFlip u i))
      set cb := decide (G.Adj u (qFlip u j))
      set cab := decide (G.Adj (qFlip u i) (qFlip (qFlip u i) j))
      set cba := decide (G.Adj (qFlip u j) (qFlip (qFlip u j) i))
      by_cases hcr : isCanonRoot ca cb cab cba = true
      · set r := rcIdx ca cb cab cba
        let vec : Fin n → Fin 10 → ℤ := fun z x =>
          q2W r x (decide (G.Adj u (qFlip u z))) (decide (G.Adj (qFlip u i) (qFlip (qFlip u i) z)))
            (decide (G.Adj (qFlip u j) (qFlip (qFlip u j) z))) (decide (G.Adj (qFlip u z) (qFlip (qFlip u z) i)))
            (decide (G.Adj (qFlip u z) (qFlip (qFlip u z) j)))
        have hq2_eq : ∀ k l, q2Raw G u i j k l = ∑ x : Fin 10, vec k x * vec l x := by
          intro k l; unfold q2Raw q2Term
          simp only [ca, cb, cab, cba, hcr, ↓reduceIte, r, vec]
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc]; ring
        simp_rw [hq2_eq]
        have hsosQ := hsosK S vec
        have hb : ∑ k ∈ S, ∑ x : Fin 10, vec k x ^ 2 ≤ K_Q2 * ((n : ℤ) - 2) := by
          calc ∑ k ∈ S, ∑ x : Fin 10, vec k x ^ 2
              ≤ ∑ _k ∈ S, K_Q2 := Finset.sum_le_sum fun k _ => by
                simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.reduceSucc, vec]
                have hq := q2W_sq_le r (decide (G.Adj u (qFlip u k))) (decide (G.Adj (qFlip u i) (qFlip (qFlip u i) k)))
                  (decide (G.Adj (qFlip u j) (qFlip (qFlip u j) k))) (decide (G.Adj (qFlip u k) (qFlip (qFlip u k) i)))
                  (decide (G.Adj (qFlip u k) (qFlip (qFlip u k) j)))
                linarith
            _ = K_Q2 * ((n : ℤ) - 2) := by rw [Finset.sum_const, nsmul_eq_mul, hScardZ]; ring
        linarith
      · have hzero : ∀ k l, q2Raw G u i j k l = 0 := by
          intro k l; unfold q2Raw q2Term
          simp only [ca, cb, cab, cba, hcr, Bool.false_eq_true, ↓reduceIte]
        simp_rw [hzero, Finset.sum_const_zero]
        have hK : (0 : ℤ) ≤ K_Q2 := by unfold K_Q2; decide
        have hn2 : (0 : ℤ) ≤ (n : ℤ) - 2 := by omega
        nlinarith
    have hstep1 : ∀ i : Fin n,
        - K_Q2 * ((n - 1 : ℤ) * (n - 2)) ≤ ∑ j ∈ Finset.univ.erase i,
          ∑ k ∈ (Finset.univ.erase i).erase j, ∑ l ∈ ((Finset.univ.erase i).erase j).erase k, q2Raw G u i j k l := by
      intro i
      have hi_card : ((Finset.univ.erase i).card : ℤ) = (n : ℤ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
        simp only [Int.ofNat_sub (by omega : 1 ≤ n)]; push_cast; rfl
      calc - K_Q2 * ((n - 1 : ℤ) * (n - 2))
          = ∑ _j ∈ Finset.univ.erase i, (- K_Q2 * ((n : ℤ) - 2)) := by rw [Finset.sum_const, nsmul_eq_mul, hi_card]; ring
        _ ≤ _ := Finset.sum_le_sum fun j hj => hij_bound i j hj
    calc - K_Q2 * ((n : ℤ) * (n - 1) * (n - 2))
        = ∑ _i : Fin n, (- K_Q2 * ((n - 1 : ℤ) * (n - 2))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => hstep1 i
  calc - K_Q2 * ((n : ℤ) * (n - 1) * (n - 2) * ((2 ^ n : ℕ) : ℤ))
      = ∑ _u : Fin n → Bool, (- K_Q2 * ((n : ℤ) * (n - 1) * (n - 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ _ := Finset.sum_le_sum fun u _ => hu u

private lemma sum_B2_lower {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] (hn : 4 ≤ n) :
    - 384 * K_B4 * ((n : ℤ) * (n - 1) * (4 * n - 6) * ((2 ^ n : ℕ) : ℤ)) -
      384 * K_Q2 * ((n : ℤ) * (n - 1) * (n - 2) * ((2 ^ n : ℕ) : ℤ)) ≤
      ∑ v : Fin 16, ∑ u : Fin n → Bool, ∑ p ∈ P4 n,
        evalB2U (extractBallB2 v (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
  have hv_eq : ∀ v : Fin 16,
      (∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalB2U (extractBallB2 v (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) =
        ∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalB2U (extractBallB2 0 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
    intro v
    rw [Finset.sum_comm]
    have hp : ∀ p ∈ P4 n, (∑ u : Fin n → Bool, evalB2U (extractBallB2 v (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) =
        ∑ u : Fin n → Bool, evalB2U (extractBallB2 0 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)) := by
      intro p _
      rw [Finset.sum_congr rfl fun u _ => congrArg evalB2U (extractBallB2_extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2 v)]
      exact sum_u_embedQ4 v p.1 p.2.1 p.2.2.1 p.2.2.2
        (fun u => evalB2U (extractBallB2 0 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)))
    rw [Finset.sum_congr rfl hp, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun v _ => hv_eq v, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hsplit : ∀ u : Fin n → Bool, (∑ p ∈ P4 n, evalB2U (extractBallB2 0 (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) =
      24 * ∑ p ∈ P4 n, b4Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 +
      24 * ∑ p ∈ P4 n, q2Raw G u p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    intro u
    rw [Finset.sum_congr rfl fun p _ => evalB2U_extractBallB2_0 G u p.1 p.2.1 p.2.2.1 p.2.2.2,
      Finset.sum_add_distrib, sum_P4_perm_collapse (b4Raw G u), sum_P4_perm12_collapse (q2Raw G u)]
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hb4 := sum_B4_lower G hn
  have hq2 := sum_Q2_lower G hn
  linarith

private theorem c6_q4_bound_core {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] [Fintype G.edgeSet] (hG : G ≤ Q n) (hfree : IsC6Free G) :
    250000 * (n - 2) * (n - 3) * G.edgeFinset.card ≤
      (91225 * (n - 2) * (n - 3) + 730366429 * (n - 3) +
        1768520 * (4 * n - 6) + 1457021 * (n - 2)) * (n * 2 ^ (n - 1)) := by
  have hpoint : ∀ u : Fin n → Bool, ∀ p ∈ P4 n,
      q4ScoreUngauged (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2) ≤ M_target := by
    intro u p hp
    simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact q4_bound_all _ (extractQ4_isC6Free hfree u hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2)
  have hupper : (∑ u : Fin n → Bool, ∑ p ∈ P4 n, q4ScoreUngauged (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)) ≤
      ((2 ^ n : ℕ) : ℤ) * ((n : ℤ) * (n - 1) * (n - 2) * (n - 3)) * M_target := by
    calc (∑ u : Fin n → Bool, ∑ p ∈ P4 n, q4ScoreUngauged (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))
        ≤ ∑ _u : Fin n → Bool, ∑ _p ∈ P4 n, M_target :=
          Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun p hp => hpoint u p hp
      _ = ((2 ^ n : ℕ) : ℤ) * ((n : ℤ) * (n - 1) * (n - 2) * (n - 3)) * M_target := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, P4_card, nsmul_eq_mul]
        have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := Int.ofNat_sub (by omega)
        have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Int.ofNat_sub (by omega)
        have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Int.ofNat_sub (by omega)
        push_cast; rw [hn1, hn2, hn3]; ring
  have hdecomp : (∑ u : Fin n → Bool, ∑ p ∈ P4 n, q4ScoreUngauged (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)) =
      (∑ fk : Fin 8, ∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 fk (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) +
      (∑ v : Fin 16, ∑ u : Fin n → Bool, ∑ p ∈ P4 n, evalB2U (extractBallB2 v (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2))) := by
    unfold q4ScoreUngauged
    simp_rw [Finset.sum_add_distrib]
    congr 1
    · trans (∑ u : Fin n → Bool, ∑ fk : Fin 8, ∑ p ∈ P4 n, evalQ3U (extractFacetQ3 fk (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)))
      · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
      · exact Finset.sum_comm
    · trans (∑ u : Fin n → Bool, ∑ v : Fin 16, ∑ p ∈ P4 n, evalB2U (extractBallB2 v (extractQ4 G u p.1 p.2.1 p.2.2.1 p.2.2.2)))
      · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
      · exact Finset.sum_comm
  have hq3 := sum_Q3_lower G hG hn
  have hb2 := sum_B2_lower G hn
  have hcomb : 384 * (D_edge * ((n - 1 : ℤ) * (n - 2) * (n - 3) * (2 * (G.edgeFinset.card : ℤ))) -
        K_Q3 * ((n : ℤ) * (n - 1) * (n - 3) * ((2 ^ n : ℕ) : ℤ))) -
      384 * K_B4 * ((n : ℤ) * (n - 1) * (4 * n - 6) * ((2 ^ n : ℕ) : ℤ)) -
      384 * K_Q2 * ((n : ℤ) * (n - 1) * (n - 2) * ((2 ^ n : ℕ) : ℤ)) ≤
      ((2 ^ n : ℕ) : ℤ) * ((n : ℤ) * (n - 1) * (n - 2) * (n - 3)) * M_target := by
    linarith
  have hpow : (2 : ℤ) ^ n = 2 * (2 : ℤ) ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n), pow_succ']
  have hconsts : D_edge = 250000 ∧ M_target = 384 * 91225 ∧ K_Q3 = 730366429 ∧
      K_B4 = 1768520 ∧ K_Q2 = 1457021 := by
    unfold D_edge M_target K_Q3 K_B4 K_Q2; decide
  rcases hconsts with ⟨hD, hM, hKq3, hKb4, hKq2⟩
  rw [hD, hM, hKq3, hKb4, hKq2] at hcomb
  push_cast at hcomb
  rw [hpow] at hcomb
  have hfactor : 768 * (n - 1 : ℤ) * (
      250000 * (n - 2 : ℤ) * (n - 3 : ℤ) * (G.edgeFinset.card : ℤ)) ≤
      768 * (n - 1 : ℤ) * (
        (91225 * (n - 2 : ℤ) * (n - 3 : ℤ) + 730366429 * (n - 3 : ℤ) +
          1768520 * (4 * n - 6 : ℤ) + 1457021 * (n - 2 : ℤ)) * ((n : ℤ) * (2 : ℤ) ^ (n - 1))) := by
    linarith
  have hpos_fac : (0 : ℤ) < 768 * (n - 1 : ℤ) := by omega
  have hZ := Int.le_of_mul_le_mul_left hfactor hpos_fac
  have h2Z : ((2 ^ (n - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (n - 1) := by push_cast; rfl
  zify
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Int.ofNat_sub (by omega)
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Int.ofNat_sub (by omega)
  have hn46 : ((4 * n - 6 : ℕ) : ℤ) = 4 * (n : ℤ) - 6 := Int.ofNat_sub (by omega)
  push_cast [hn2, hn3, hn46]
  exact hZ

end GlobalAveraging

/-! ## Section 5: Pure-Mathlib Public Headline Theorems -/

section PublicTheorems

/-- **Theorem 1 (`ppl033_c6_q4_upper_exact`):**
Unconditional exact finite-`n` upper bound on any `C_6`-free subgraph `G ≤ Q_n` for all `n ≥ 4`. -/
theorem ppl033_c6_q4_upper_exact (n : ℕ) (hn : 4 ≤ n) (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ f : Fin 6 → (Fin n → Bool), Function.Injective f →
      ¬ (G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧
         G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 0))) :
    250000 * (n - 2) * (n - 3) * G.edgeFinset.card ≤
      (91225 * (n - 2) * (n - 3) + 730366429 * (n - 3) +
        1768520 * (4 * n - 6) + 1457021 * (n - 2)) * (n * 2 ^ (n - 1)) :=
  c6_q4_bound_core hn G hG hfree

private lemma density_lt_of_exact {n num den : ℕ} (hn : 4 ≤ n) (hden : 0 < den)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G ≤ Q n) (hfree : IsC6Free G)
    (hpoly : (91225 * (n - 2) * (n - 3) + 730366429 * (n - 3) +
        1768520 * (4 * n - 6) + 1457021 * (n - 2)) * den <
      250000 * (n - 2) * (n - 3) * num) :
    (G.edgeFinset.card : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ) < (num : ℝ) / (den : ℝ) := by
  have hex := c6_q4_bound_core hn G hG hfree
  have hposE : (0 : ℝ) < ((n * 2 ^ (n - 1) : ℕ) : ℝ) := by positivity
  have hposD : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  rw [div_lt_div_iff₀ hposE hposD]
  have hcoef_pos : (0 : ℝ) < ((250000 * (n - 2) * (n - 3) : ℕ) : ℝ) := by
    have h1 : 0 < n - 2 := by omega
    have h2 : 0 < n - 3 := by omega
    positivity
  have hexR : ((250000 * (n - 2) * (n - 3) : ℕ) : ℝ) * (G.edgeFinset.card : ℝ) ≤
      (((91225 * (n - 2) * (n - 3) + 730366429 * (n - 3) +
        1768520 * (4 * n - 6) + 1457021 * (n - 2) : ℕ) : ℝ) * ((n * 2 ^ (n - 1) : ℕ) : ℝ)) := by
    exact_mod_cast hex
  have hpolyR : ((91225 * (n - 2) * (n - 3) + 730366429 * (n - 3) +
        1768520 * (4 * n - 6) + 1457021 * (n - 2) : ℕ) : ℝ) * (den : ℝ) <
      ((250000 * (n - 2) * (n - 3) : ℕ) : ℝ) * (num : ℝ) := by
    exact_mod_cast hpoly
  nlinarith

/-- **Theorem 2 (`ppl033_c6_beats_baber_2012_explicit`):**
For every `n ≥ 3400000`, any `C_6`-free subgraph `G ≤ Q_n` has edge density strictly less than
`36577 / 100000` (`= 0.36577`), strictly beating Baber (2012). -/
theorem ppl033_c6_beats_baber_2012_explicit (n : ℕ) (hn : 3400000 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ f : Fin 6 → (Fin n → Bool), Function.Injective f →
      ¬ (G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧
         G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 0))) :
    (G.edgeFinset.card : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ) < 36577 / 100000 := by
  refine density_lt_of_exact (by omega : 4 ≤ n) (by decide : 0 < 100000) G hG hfree ?_
  zify
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Int.ofNat_sub (by omega)
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Int.ofNat_sub (by omega)
  have hn46 : ((4 * n - 6 : ℕ) : ℤ) = 4 * (n : ℤ) - 6 := Int.ofNat_sub (by omega)
  push_cast [hn2, hn3, hn46]
  nlinarith

/-- **Theorem 3 (`ppl033_c6_lt_365_explicit`):**
For every `n ≥ 29600000`, any `C_6`-free subgraph `G ≤ Q_n` has edge density strictly less than
`365 / 1000` (`= 0.365`). -/
theorem ppl033_c6_lt_365_explicit (n : ℕ) (hn : 29600000 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ f : Fin 6 → (Fin n → Bool), Function.Injective f →
      ¬ (G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧
         G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 0))) :
    (G.edgeFinset.card : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ) < 365 / 1000 := by
  refine density_lt_of_exact (by omega : 4 ≤ n) (by decide : 0 < 1000) G hG hfree ?_
  zify
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := Int.ofNat_sub (by omega)
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := Int.ofNat_sub (by omega)
  have hn46 : ((4 * n - 6 : ℕ) : ℤ) = 4 * (n : ℤ) - 6 := Int.ofNat_sub (by omega)
  push_cast [hn2, hn3, hn46]
  nlinarith

/-- **Theorem 4 (`ppl033_c6_turan_density_limit_beats_baber`):**
The hypercube `C_6` Turán density limit `L = lim_{n → ∞} ex(Q_n, C_6) / (n * 2 ^ (n - 1))`
exists and satisfies `0 ≤ L ≤ 3649 / 10000 < 365 / 1000 < 36577 / 100000`, strictly beating
Baber (2012)'s `0.36577`. -/
theorem ppl033_c6_turan_density_limit_beats_baber :
    open Classical in
    ∃ L : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          ((sSup { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
              G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
                (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
              (∀ f : Fin 6 → (Fin n → Bool), Function.Injective f →
                ¬ (G.Adj (f 0) (f 1) ∧ G.Adj (f 1) (f 2) ∧ G.Adj (f 2) (f 3) ∧
                   G.Adj (f 3) (f 4) ∧ G.Adj (f 4) (f 5) ∧ G.Adj (f 5) (f 0))) ∧
              G.edgeFinset.card = m } : ℕ) : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ))
        Filter.atTop (nhds L) ∧
      0 ≤ L ∧ L ≤ 3649 / 10000 ∧ L < 365 / 1000 ∧ L < 36577 / 100000 := by
  classical
  let d : ℕ → ℝ := fun n => (exC6 n : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ)
  let d1 : ℕ → ℝ := fun k => d (k + 1)
  have hanti : Antitone d1 := fun a b hab =>
    turan_density_antitone_aux (by omega : 1 ≤ a + 1) (by omega : a + 1 ≤ b + 1)
  have hlb : ∀ k : ℕ, (0 : ℝ) ≤ d1 k := fun k => by positivity
  have hbdd : BddBelow (Set.range d1) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hlb k⟩
  have htend1 : Tendsto d1 atTop (nhds (⨅ k, d1 k)) := tendsto_atTop_ciInf hanti hbdd
  have htend : Tendsto d atTop (nhds (⨅ k, d1 k)) := by
    rw [← tendsto_add_atTop_iff_nat 1]; exact htend1
  have hL_le_3649 : ⨅ k, d1 k ≤ 3649 / 10000 := by
    by_contra hgt
    push Not at hgt
    set ε : ℝ := (⨅ k, d1 k) - 3649 / 10000
    have hε : 0 < ε := sub_pos.mpr hgt
    obtain ⟨N, hN⟩ := exists_nat_gt (6000 / ε)
    let m : ℕ := N + 6
    have hm6 : 6 ≤ m := by omega
    have hL_le : ⨅ k, d1 k ≤ d m := by
      have : d m = d1 (N + 5) := rfl
      rw [this]; exact ciInf_le hbdd (N + 5)
    obtain ⟨G, hG, hfree, hcard⟩ := exists_exC6_witness m
    have hcore := c6_q4_bound_core (by omega : 4 ≤ m) G hG hfree
    rw [hcard] at hcore
    have hm2_pos : (0 : ℝ) < (m : ℝ) - 2 := by
      have : (6 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm6; linarith
    have hm3_pos : (0 : ℝ) < (m : ℝ) - 3 := by
      have : (6 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm6; linarith
    have hposE : (0 : ℝ) < ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by positivity
    have hcoreR : 250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) * (exC6 m : ℝ) ≤
        (91225 * ((m : ℝ) - 2) * ((m : ℝ) - 3) + 730366429 * ((m : ℝ) - 3) +
          1768520 * (4 * (m : ℝ) - 6) + 1457021 * ((m : ℝ) - 2)) * ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by
      have h1 := Nat.cast_le (α := ℝ).mpr hcore
      have hm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub (by omega)
      have hm3 : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := Nat.cast_sub (by omega)
      have hm46 : ((4 * m - 6 : ℕ) : ℝ) = 4 * (m : ℝ) - 6 := by
        rw [Nat.cast_sub (by omega : 6 ≤ 4 * m)]; push_cast; ring
      push_cast [hm2, hm3, hm46] at h1
      have hE : (m : ℝ) * (2 : ℝ) ^ (m - 1) = ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by push_cast; rfl
      rw [hE] at h1
      exact h1
    have hdm : d m ≤ 3649 / 10000 + 3000 / ((m : ℝ) - 3) := by
      dsimp [d]
      rw [div_le_iff₀ hposE]
      have hdiv : (3649 / 10000 + 3000 / ((m : ℝ) - 3)) * (250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3)) =
          91225 * ((m : ℝ) - 2) * ((m : ℝ) - 3) + 750000000 * ((m : ℝ) - 2) := by
        field_simp [hm3_pos.ne']
        ring
      have hnum : 91225 * ((m : ℝ) - 2) * ((m : ℝ) - 3) + 730366429 * ((m : ℝ) - 3) +
          1768520 * (4 * (m : ℝ) - 6) + 1457021 * ((m : ℝ) - 2) ≤
          91225 * ((m : ℝ) - 2) * ((m : ℝ) - 3) + 750000000 * ((m : ℝ) - 2) := by
        have hm_ge : (6 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm6
        linarith
      have hmul := mul_le_mul_of_nonneg_right hnum hposE.le
      have hfac : (0 : ℝ) < 250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) := by positivity
      have hle1 : 250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) * (exC6 m : ℝ) ≤
          250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
            ((3649 / 10000 + 3000 / ((m : ℝ) - 3)) * ((m * 2 ^ (m - 1) : ℕ) : ℝ)) := by
        have hmul2 : 250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
              ((3649 / 10000 + 3000 / ((m : ℝ) - 3)) * ((m * 2 ^ (m - 1) : ℕ) : ℝ)) =
            (91225 * ((m : ℝ) - 2) * ((m : ℝ) - 3) + 750000000 * ((m : ℝ) - 2)) * ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by
          calc 250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
                ((3649 / 10000 + 3000 / ((m : ℝ) - 3)) * ((m * 2 ^ (m - 1) : ℕ) : ℝ))
              = ((3649 / 10000 + 3000 / ((m : ℝ) - 3)) * (250000 * ((m : ℝ) - 2) * ((m : ℝ) - 3))) * ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by ring
            _ = (91225 * ((m : ℝ) - 2) * ((m : ℝ) - 3) + 750000000 * ((m : ℝ) - 2)) * ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by rw [hdiv]
        rw [hmul2]
        exact le_trans hcoreR hmul
      exact le_of_mul_le_mul_left hle1 hfac
    have h3000 : 3000 / ((m : ℝ) - 3) < ε := by
      have hmN : (N : ℝ) < (m : ℝ) - 3 := by
        have : m = N + 6 := rfl
        push_cast [this]; linarith
      rw [div_lt_iff₀ hm3_pos]
      have hNpos : 0 < (6000 / ε) := by positivity
      have h1 : 6000 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
      nlinarith
    dsimp only [ε] at h3000
    linarith
  refine ⟨⨅ k, d1 k, htend, le_ciInf hlb, hL_le_3649, by linarith, by linarith⟩

end PublicTheorems
