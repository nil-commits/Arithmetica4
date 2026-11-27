/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_B2Q4Cert
import RHDirect.PPL033_Main
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# PPL 033 — Erdős Problem #86: New World-Record Upper Bound (`< 0.6030 < 0.60318`)

**Open Problem Reference:** Erdős Problem #86 (`ex(Q_n, C_4) = (1/2 + o(1)) n 2^{n-1}`).
Previous best unconditional asymptotic upper bound: `0.60318` (Baber 2012, *Turán densities
of hypercubes*, arXiv:1201.3587), and `0.6175` in `RHDirect.PPL033_Main`.

## Summary of Verified Results (Pure Mathlib Signatures, Zero `sorry`, Zero Custom Axioms, Zero `native_decide`)

Using the kernel-checked (`decide`) coupled `Q_3 + B_2(Q_4)` flag-algebra Sum-of-Squares
certificate in `RHDirect.PPL033_B2Q4Cert`:

1. **`ppl033_b2q4_upper_exact`:** For every `n ≥ 4` and every `C_4`-free subgraph `G ≤ Q_n`:
   `48 * 100000000 * (n - 2) * (n - 3) * |E(G)| ≤ 1447121170 * n * (n - 2) * (n - 3) * 2 ^ n +`
   `  24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2)) * n * 2 ^ n`.
2. **`ppl033_beats_baber_2012_explicit`:** For every `n ≥ 22330` and every `C_4`-free `G ≤ Q_n`:
   `100000 * |E(G)| < 60318 * (n * 2 ^ (n - 1))` (strictly below Baber 2012's `0.60318`).
3. **`ppl033_lt_603_explicit`:** For every `n ≥ 144685` and every `C_4`-free `G ≤ Q_n`:
   `1000 * |E(G)| < 603 * (n * 2 ^ (n - 1))` (strictly below `0.6030`).
4. **`ppl033_turan_density_limit_beats_baber`:** The hypercube `C_4` Turán density limit
   `L = lim_{n → ∞} ex(Q_n, C_4) / (n * 2 ^ (n - 1))` exists and satisfies
   `1 / 2 ≤ L ≤ 1447121170 / 2400000000 ≈ 0.6029671542`, hence `L < 603 / 1000 < 60318 / 100000`.
-/

namespace PPL033_B2Q4

open scoped BigOperators
open Filter
open PPL033_B2Q4Cert

/-! ## Section 1: Hypercube Helpers & `C_4`-Freeness on `Q_n` -/

section HypercubeHelpers

private def Q (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel
    (fun u v : Fin n → Bool => (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1)

private def IsC4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

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
    · convert h using 2; ext i; simp [ne_comm]
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro heq; subst heq; simp at h

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

private lemma edgeFinset_card_congr {V : Type*} (G : SimpleGraph V)
    (inst1 inst2 : Fintype G.edgeSet) :
    (@SimpleGraph.edgeFinset _ G inst1).card = (@SimpleGraph.edgeFinset _ G inst2).card := by
  congr 1; ext e; simp [SimpleGraph.mem_edgeFinset]

private lemma twice_card_edges_eq_sum_oriented {n : ℕ} (G : SimpleGraph (Fin n → Bool))
    [DecidableRel G.Adj] [Fintype G.edgeSet] (hG : G ≤ Q n) :
    2 * G.edgeFinset.card =
      ∑ u : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => G.Adj u (flip u i))).card := by
  have hdeg : 2 * G.edgeFinset.card = ∑ v, G.degree v := by
    rw [edgeFinset_card_congr G _ _]
    exact (G.sum_degrees_eq_twice_card_edges).symm
  rw [hdeg]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [SimpleGraph.degree]
  refine Finset.card_bij (fun y hy => Classical.choose (Q_adj_iff_exists_flip.mp (hG
      ((G.mem_neighborFinset u y).mp hy)))) ?_ ?_ ?_
  · intro y hy
    have hGu : G.Adj u y := (G.mem_neighborFinset u y).mp hy
    have hsp := Classical.choose_spec (Q_adj_iff_exists_flip.mp (hG hGu))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← hsp]
  · intro y1 hy1 y2 hy2 heq
    have h1 := Classical.choose_spec (Q_adj_iff_exists_flip.mp (hG ((G.mem_neighborFinset u y1).mp hy1)))
    have h2 := Classical.choose_spec (Q_adj_iff_exists_flip.mp (hG ((G.mem_neighborFinset u y2).mp hy2)))
    rw [h1, h2, heq]
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨flip u i, (G.mem_neighborFinset u (flip u i)).mpr hi, ?_⟩
    have hsp := Classical.choose_spec (Q_adj_iff_exists_flip.mp (hG hi))
    exact flip_inj u hsp.symm

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

private lemma hsos {n : ℕ} (S : Finset (Fin n)) (f : Fin n → ℤ) :
    - ∑ a ∈ S, (f a) ^ 2 ≤ ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b := by
  have hid : (∑ a ∈ S, f a) ^ 2 =
      (∑ a ∈ S, (f a) ^ 2) + ∑ a ∈ S, ∑ b ∈ S.erase a, f a * f b := by
    rw [sq, Finset.sum_mul]
    have h1 : ∀ a ∈ S, f a * ∑ b ∈ S, f b = (f a) ^ 2 + ∑ b ∈ S.erase a, f a * f b := by
      intro a ha
      rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ ha, sq]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
  have hsq_nonneg : (0 : ℤ) ≤ (∑ a ∈ S, f a) ^ 2 := sq_nonneg _
  linarith

end HypercubeHelpers

/-! ## Section 2: `Q_3` Global Inequality with Coupling `-24 * L` -/

section Q3Global

private def embedQ3 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) : Fin n → Bool :=
  let u1 := if w 0 then flip u a else u
  let u2 := if w 1 then flip u1 b else u1
  if w 2 then flip u2 c else u2

private lemma embedQ3_flip0 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) :
    embedQ3 u a b c (flip w 0) = flip (embedQ3 u a b c w) a := by
  have h1 : flip w 0 0 = !w 0 := by simp [flip]
  have h2 : flip w 0 1 = w 1 := by simp [flip]
  have h3 : flip w 0 2 = w 2 := by simp [flip]
  dsimp only [embedQ3]; rw [h1, h2, h3]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip, flip_comm]

private lemma embedQ3_flip1 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) :
    embedQ3 u a b c (flip w 1) = flip (embedQ3 u a b c w) b := by
  have h1 : flip w 1 0 = w 0 := by simp [flip]
  have h2 : flip w 1 1 = !w 1 := by simp [flip]
  have h3 : flip w 1 2 = w 2 := by simp [flip]
  dsimp only [embedQ3]; rw [h1, h2, h3]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip, flip_comm]

private lemma embedQ3_flip2 {n : ℕ} (u : Fin n → Bool) (a b c : Fin n) (w : Fin 3 → Bool) :
    embedQ3 u a b c (flip w 2) = flip (embedQ3 u a b c w) c := by
  have h1 : flip w 2 0 = w 0 := by simp [flip]
  have h2 : flip w 2 1 = w 1 := by simp [flip]
  have h3 : flip w 2 2 = !w 2 := by simp [flip]
  dsimp only [embedQ3]; rw [h1, h2, h3]
  cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip]

private lemma flip3_0 (p q r : Bool) : flip ![p, q, r] 0 = ![!p, q, r] := by
  ext k; fin_cases k <;> simp [flip]

private lemma flip3_1 (p q r : Bool) : flip ![p, q, r] 1 = ![p, !q, r] := by
  ext k; fin_cases k <;> simp [flip]

private lemma flip3_2 (p q r : Bool) : flip ![p, q, r] 2 = ![p, q, !r] := by
  ext k; fin_cases k <;> simp [flip]

private lemma embedQ3_equiv_u {n : ℕ} (a b c : Fin n) (w : Fin 3 → Bool) :
    Function.Bijective (fun u : Fin n → Bool => embedQ3 u a b c w) := by
  have hinv : ∀ u : Fin n → Bool, embedQ3 (embedQ3 u a b c w) a b c w = u := by
    intro u; dsimp only [embedQ3]
    cases w 0 <;> cases w 1 <;> cases w 2 <;> simp [flip_flip, flip_comm]
  exact Function.Involutive.bijective hinv

private def edgeFlag {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (i j : Fin n) : Fin 8 :=
  mkFlag (decide (G.Adj v (flip v j)))
         (decide (G.Adj (flip v i) (flip (flip v i) j)))
         (decide (G.Adj (flip v j) (flip (flip v j) i)))

private def q3OrientedTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (i j1 j2 : Fin n) : ℤ :=
  let t1 := edgeFlag G v i j1
  let t2 := edgeFlag G v i j2
  if G.Adj v (flip v i) then
    D_edge + (q3W0 0 t1 * q3W0 0 t2 + q3W0 1 t1 * q3W0 1 t2 +
              q3W0 2 t1 * q3W0 2 t2 + q3W0 3 t1 * q3W0 3 t2)
  else
    q3U1 0 t1 * q3U1 0 t2 + q3U1 1 t1 * q3U1 1 t2 +
    q3U1 2 t1 * q3U1 2 t2 + q3U1 3 t1 * q3U1 3 t2 + q3U1 4 t1 * q3U1 4 t2

private lemma q3OrientedTerm_eq_bool {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (i j1 j2 : Fin n) :
    q3OrientedTerm G v i j1 j2 =
      q3EdgeTerm (decide (G.Adj v (flip v i)))
        (decide (G.Adj v (flip v j1)))
        (decide (G.Adj (flip v i) (flip (flip v i) j1)))
        (decide (G.Adj (flip v j1) (flip (flip v j1) i)))
        (decide (G.Adj v (flip v j2)))
        (decide (G.Adj (flip v i) (flip (flip v i) j2)))
        (decide (G.Adj (flip v j2) (flip (flip v j2) i))) := by
  unfold q3OrientedTerm q3EdgeTerm edgeFlag
  by_cases h : G.Adj v (flip v i)
  · simp only [h, ↓reduceIte, decide_true]
  · simp only [h, ↓reduceIte, decide_false, Bool.false_eq_true]

private def lamTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (a b c : Fin n) : ℤ :=
  lam23
    (decide (G.Adj v (flip v a)))
    (decide (G.Adj v (flip v b)))
    (decide (G.Adj v (flip v c)))
    (decide (G.Adj (flip v a) (flip (flip v a) b)))
    (decide (G.Adj (flip v b) (flip (flip v b) a)))
    (decide (G.Adj (flip v a) (flip (flip v a) c)))
    (decide (G.Adj (flip v c) (flip (flip v c) a)))
    (decide (G.Adj (flip v b) (flip (flip v b) c)))
    (decide (G.Adj (flip v c) (flip (flip v c) b)))

private lemma q3_local_bound {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : G ≤ Q n) (hfree : IsC4Free G)
    (u : Fin n → Bool) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let v (w : Fin 3 → Bool) := embedQ3 u a b c w
    (∑ w : Fin 3 → Bool,
      ((q3OrientedTerm G (v w) a b c +
        q3OrientedTerm G (v w) b a c +
        q3OrientedTerm G (v w) c a b) - 3 * lamTerm G (v w) a b c)) ≤ M3 := by
  intro v
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
  have hle := q3LocalBool_le_M3 x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 hc4
  have hsum_eq :
      (∑ w : Fin 3 → Bool,
        ((q3OrientedTerm G (v w) a b c + q3OrientedTerm G (v w) b a c + q3OrientedTerm G (v w) c a b) -
          3 * lamTerm G (v w) a b c)) =
      q3LocalBool x00 x01 x10 x11 y00 y01 y10 y11 z00 z01 z10 z11 := by
    let e3 : (Fin 3 → Bool) ≃ Bool × Bool × Bool :=
      { toFun := fun w => (w 0, w 1, w 2)
        invFun := fun p => ![p.1, p.2.1, p.2.2]
        left_inv := fun w => by ext k; fin_cases k <;> rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    rw [Fintype.sum_equiv e3 _ (fun p =>
      (q3OrientedTerm G (v ![p.1, p.2.1, p.2.2]) a b c +
       q3OrientedTerm G (v ![p.1, p.2.1, p.2.2]) b a c +
       q3OrientedTerm G (v ![p.1, p.2.1, p.2.2]) c a b) -
      3 * lamTerm G (v ![p.1, p.2.1, p.2.2]) a b c) (fun w => by
        have hw : w = ![w 0, w 1, w 2] := by ext k; fin_cases k <;> rfl
        conv_lhs => rw [hw]
        rfl)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, q3OrientedTerm_eq_bool, lamTerm]
    have hsym : ∀ p q : Fin n → Bool, decide (G.Adj q p) = decide (G.Adj p q) := fun p q => by
      simp [SimpleGraph.adj_comm]
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
    dsimp only [q3LocalBool]
    ring
  linarith

private lemma q3_global_bound {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hG : G ≤ Q n) (hfree : IsC4Free G) :
    let L : ℤ := ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
      ∑ v : Fin n → Bool, lamTerm G v a b c
    24 * (2 * D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ) -
          K_Q3 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n - L) ≤
      M3 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 : ℤ) ^ n := by
  intro L
  let T : ℤ := ∑ i : Fin n, ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
      ∑ v : Fin n → Bool, q3OrientedTerm G v i j1 j2
  have hsum_ub :
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
          ((q3OrientedTerm G (embedQ3 u a b c w) a b c +
            q3OrientedTerm G (embedQ3 u a b c w) b a c +
            q3OrientedTerm G (embedQ3 u a b c w) c a b) -
            3 * lamTerm G (embedQ3 u a b c w) a b c)) ≤
      M3 * ((n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 : ℤ) ^ n) := by
    have h1 :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
            ((q3OrientedTerm G (embedQ3 u a b c w) a b c +
              q3OrientedTerm G (embedQ3 u a b c w) b a c +
              q3OrientedTerm G (embedQ3 u a b c w) c a b) -
              3 * lamTerm G (embedQ3 u a b c w) a b c)) ≤
        ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ _c ∈ (Finset.univ.erase a).erase b,
          ∑ _u : Fin n → Bool, M3 := by
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b hb =>
        Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun u _ => ?_
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
      have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
      exact q3_local_bound G hG hfree u hba.symm hca.symm hcb.symm
    refine le_trans h1 ?_
    have hcard2 : ∀ (a b : Fin n), b ∈ Finset.univ.erase a →
        ((Finset.univ.erase a).erase b).card = n - 2 := by
      intro a b hb
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]; omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
      Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∀ a : Fin n,
        ∑ b ∈ Finset.univ.erase a, (((Finset.univ.erase a).erase b).card : ℤ) * ((2 : ℤ) ^ n * M3) =
        (((n - 1 : ℕ) : ℤ) * (((n - 2 : ℕ) : ℤ) * ((2 : ℤ) ^ n * M3))) := by
      intro a
      rw [Finset.sum_congr rfl fun b hb => by rw [hcard2 a b hb],
          Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2' : ∀ a : Fin n,
        ∑ b ∈ Finset.univ.erase a, (((Finset.univ.erase a).erase b).card : ℤ) * (((2 ^ n : ℕ) : ℤ) * M3) =
        (((n - 1 : ℕ) : ℤ) * (((n - 2 : ℕ) : ℤ) * ((2 : ℤ) ^ n * M3))) := fun a => by simpa using h2 a
    simp_rw [h2', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    rw [hn1, hn2]; ring_nf; exact le_rfl
  have hlhs_eq :
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
          ((q3OrientedTerm G (embedQ3 u a b c w) a b c +
            q3OrientedTerm G (embedQ3 u a b c w) b a c +
            q3OrientedTerm G (embedQ3 u a b c w) c a b) -
            3 * lamTerm G (embedQ3 u a b c w) a b c)) =
      24 * T - 24 * L := by
    have hinner : ∀ a b c : Fin n,
        (∑ u : Fin n → Bool, ∑ w : Fin 3 → Bool,
          ((q3OrientedTerm G (embedQ3 u a b c w) a b c +
            q3OrientedTerm G (embedQ3 u a b c w) b a c +
            q3OrientedTerm G (embedQ3 u a b c w) c a b) -
            3 * lamTerm G (embedQ3 u a b c w) a b c)) =
        8 * ((∑ v : Fin n → Bool, q3OrientedTerm G v a b c) +
             (∑ v : Fin n → Bool, q3OrientedTerm G v b a c) +
             (∑ v : Fin n → Bool, q3OrientedTerm G v c a b)) -
        24 * (∑ v : Fin n → Bool, lamTerm G v a b c) := by
      intro a b c
      rw [Finset.sum_comm]
      have hw : ∀ w : Fin 3 → Bool,
          (∑ u : Fin n → Bool,
            ((q3OrientedTerm G (embedQ3 u a b c w) a b c +
              q3OrientedTerm G (embedQ3 u a b c w) b a c +
              q3OrientedTerm G (embedQ3 u a b c w) c a b) -
              3 * lamTerm G (embedQ3 u a b c w) a b c)) =
          ((∑ v : Fin n → Bool, q3OrientedTerm G v a b c) +
           (∑ v : Fin n → Bool, q3OrientedTerm G v b a c) +
           (∑ v : Fin n → Bool, q3OrientedTerm G v c a b)) -
          3 * (∑ v : Fin n → Bool, lamTerm G v a b c) := by
        intro w
        rw [Fintype.sum_bijective (fun u => embedQ3 u a b c w) (embedQ3_equiv_u a b c w) _
          (fun v => (q3OrientedTerm G v a b c + q3OrientedTerm G v b a c + q3OrientedTerm G v c a b) -
            3 * lamTerm G v a b c) (fun _ => rfl)]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp_rw [hw, Finset.sum_const, Finset.card_univ, Fintype.card_pi]
      simp only [Fintype.card_bool, Finset.prod_const, nsmul_eq_mul]
      norm_num; ring
    simp_rw [hinner, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsplit3 :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ((∑ v : Fin n → Bool, q3OrientedTerm G v a b c) +
           (∑ v : Fin n → Bool, q3OrientedTerm G v b a c) +
           (∑ v : Fin n → Bool, q3OrientedTerm G v c a b))) =
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool, q3OrientedTerm G v a b c) +
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool, q3OrientedTerm G v b a c) +
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ v : Fin n → Bool, q3OrientedTerm G v c a b) := by
      simp only [Finset.sum_add_distrib]
    let f3 (i j1 j2 : Fin n) : ℤ := ∑ v : Fin n → Bool, q3OrientedTerm G v i j1 j2
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
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact ⟨hp.1.symm, hp.2.2, hp.2.1⟩
      · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1⟩; rcases p2 with ⟨a2, b2, c2⟩; simp_all
      · intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨(q.2.1, q.1, q.2.2), by simp [hq.1.symm, hq.2.1, hq.2.2], rfl⟩
      · intro _ _; rfl
    have hperm_ac :
        (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 c a b) =
        ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 a b c := by
      rw [hrew (fun a b c => f3 c a b), hrew f3]
      refine Finset.sum_bij (fun p _ => (p.2.2, p.1, p.2.1)) ?_ ?_ ?_ ?_
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact ⟨hp.2.1.symm, hp.2.2.symm, hp.1⟩
      · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1⟩; rcases p2 with ⟨a2, b2, c2⟩; simp_all
      · intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨(q.2.1, q.2.2, q.1), by simp [hq.2.2, hq.1.symm, hq.2.1.symm], rfl⟩
      · intro _ _; rfl
    rw [hsplit3]
    change 8 * (T + (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 b a c) +
                (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, f3 c a b)) -
           24 * L = 24 * T - 24 * L
    rw [hperm_ab, hperm_ac]
    change 8 * (T + T + T) - 24 * L = 24 * T - 24 * L
    ring
  have hT_lb :
      2 * D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ) -
        K_Q3 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n ≤ T := by
    have hT_swap :
        T = ∑ v : Fin n → Bool, ∑ i : Fin n,
          ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
            q3OrientedTerm G v i j1 j2 := by
      dsimp only [T]
      have s1 : ∀ i : Fin n,
          (∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
            ∑ v : Fin n → Bool, q3OrientedTerm G v i j1 j2) =
          ∑ v : Fin n → Bool, ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
            q3OrientedTerm G v i j1 j2 := fun i => by
        have s2 : ∀ j1 ∈ Finset.univ.erase i,
            (∑ j2 ∈ (Finset.univ.erase i).erase j1, ∑ v : Fin n → Bool, q3OrientedTerm G v i j1 j2) =
            ∑ v : Fin n → Bool, ∑ j2 ∈ (Finset.univ.erase i).erase j1, q3OrientedTerm G v i j1 j2 :=
          fun _ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl s2]; exact Finset.sum_comm
      simp_rw [s1]; exact Finset.sum_comm
    rw [hT_swap]
    have hpt_vi : ∀ (v : Fin n → Bool) (i : Fin n),
        (if G.Adj v (flip v i) then D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) -
          K_Q3 * ((n : ℤ) - 1) ≤
        ∑ j1 ∈ Finset.univ.erase i, ∑ j2 ∈ (Finset.univ.erase i).erase j1,
          q3OrientedTerm G v i j1 j2 := by
      intro v i
      set S := Finset.univ.erase i
      have hScard : (S.card : ℤ) = (n : ℤ) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]; omega
      by_cases hadj : G.Adj v (flip v i)
      · simp only [hadj, ↓reduceIte, q3OrientedTerm]
        simp only [Finset.sum_add_distrib]
        have hconst :
            (∑ j1 ∈ S, ∑ _j2 ∈ S.erase j1, D_edge) = D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
          have hc : ∀ j1 ∈ S, ((S.erase j1).card : ℤ) = (n : ℤ) - 2 := by
            intro j1 hj1
            rw [Finset.card_erase_of_mem hj1, Finset.card_erase_of_mem (Finset.mem_univ i),
                Finset.card_univ, Fintype.card_fin]; omega
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.sum_congr rfl fun j1 hj1 => by rw [hc j1 hj1], Finset.sum_const, nsmul_eq_mul, hScard]
          ring
        have h0 := hsos S (fun j => q3W0 0 (edgeFlag G v i j))
        have h1 := hsos S (fun j => q3W0 1 (edgeFlag G v i j))
        have h2 := hsos S (fun j => q3W0 2 (edgeFlag G v i j))
        have h3 := hsos S (fun j => q3W0 3 (edgeFlag G v i j))
        have hdiag : ∑ j ∈ S, (q3W0 0 (edgeFlag G v i j) ^ 2 + q3W0 1 (edgeFlag G v i j) ^ 2 +
            q3W0 2 (edgeFlag G v i j) ^ 2 + q3W0 3 (edgeFlag G v i j) ^ 2) ≤ K_Q3 * ((n : ℤ) - 1) := by
          calc ∑ j ∈ S, (q3W0 0 (edgeFlag G v i j) ^ 2 + q3W0 1 (edgeFlag G v i j) ^ 2 +
                q3W0 2 (edgeFlag G v i j) ^ 2 + q3W0 3 (edgeFlag G v i j) ^ 2)
              ≤ ∑ _j ∈ S, K_Q3 := Finset.sum_le_sum fun j _ => q3W0_sq_le _
            _ = K_Q3 * ((n : ℤ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul, hScard]; ring
        simp only [Finset.sum_add_distrib] at hdiag
        rw [hconst]; linarith
      · simp only [hadj, ↓reduceIte, q3OrientedTerm]
        simp only [Finset.sum_add_distrib]
        have h0 := hsos S (fun j => q3U1 0 (edgeFlag G v i j))
        have h1 := hsos S (fun j => q3U1 1 (edgeFlag G v i j))
        have h2 := hsos S (fun j => q3U1 2 (edgeFlag G v i j))
        have h3 := hsos S (fun j => q3U1 3 (edgeFlag G v i j))
        have h4 := hsos S (fun j => q3U1 4 (edgeFlag G v i j))
        have hdiag : ∑ j ∈ S, (q3U1 0 (edgeFlag G v i j) ^ 2 + q3U1 1 (edgeFlag G v i j) ^ 2 +
            q3U1 2 (edgeFlag G v i j) ^ 2 + q3U1 3 (edgeFlag G v i j) ^ 2 +
            q3U1 4 (edgeFlag G v i j) ^ 2) ≤ K_Q3 * ((n : ℤ) - 1) := by
          calc ∑ j ∈ S, (q3U1 0 (edgeFlag G v i j) ^ 2 + q3U1 1 (edgeFlag G v i j) ^ 2 +
                q3U1 2 (edgeFlag G v i j) ^ 2 + q3U1 3 (edgeFlag G v i j) ^ 2 +
                q3U1 4 (edgeFlag G v i j) ^ 2)
              ≤ ∑ _j ∈ S, K_Q3 := Finset.sum_le_sum fun j _ => q3U1_sq_le _
            _ = K_Q3 * ((n : ℤ) - 1) := by rw [Finset.sum_const, nsmul_eq_mul, hScard]; ring
        simp only [Finset.sum_add_distrib] at hdiag
        linarith
    have hsum_vi := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
      Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt_vi v i
    refine le_trans ?_ hsum_vi
    simp only [Finset.sum_sub_distrib]
    have hconst :
        (∑ _v : Fin n → Bool, ∑ _i : Fin n, K_Q3 * ((n : ℤ) - 1)) =
        K_Q3 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
        Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    have hedge :
        (∑ v : Fin n → Bool, ∑ i : Fin n,
          if G.Adj v (flip v i) then D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) =
        2 * D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (G.edgeFinset.card : ℤ) := by
      have hfac : ∀ v : Fin n → Bool,
          (∑ i : Fin n, if G.Adj v (flip v i) then D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2) else 0) =
          ((Finset.univ.filter (fun i : Fin n => G.Adj v (flip v i))).card : ℤ) *
            (D_edge * ((n : ℤ) - 1) * ((n : ℤ) - 2)) := fun v => by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simp_rw [hfac, ← Finset.sum_mul]
      have h2e := twice_card_edges_eq_sum_oriented G hG
      have h2eZ : (∑ v : Fin n → Bool, ((Finset.univ.filter (fun i : Fin n => G.Adj v (flip v i))).card : ℤ)) =
          2 * (G.edgeFinset.card : ℤ) := by exact_mod_cast h2e.symm
      rw [h2eZ]; ring
    rw [hconst, hedge]
  rw [hlhs_eq] at hsum_ub
  linarith

end Q3Global

/-! ## Section 3: `B_2(Q_4)` Global Inequality (`Coupling + Flip + B4s + Q2`) -/

section B2Q4Global

private def P4 (n : ℕ) : Finset (Fin n × Fin n × Fin n × Fin n) :=
  Finset.univ.filter (fun p =>
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
    p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2)

private lemma sum_P4_eq {n : ℕ} (g : Fin n → Fin n → Fin n → Fin n → ℤ) :
    (∑ p ∈ P4 n, g p.1 p.2.1 p.2.2.1 p.2.2.2) =
    ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
      ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, g a b c d := by
  symm
  unfold P4
  rw [Finset.sum_filter]
  have h1 : ∀ a : Fin n,
      (∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, g a b c d) =
      ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then g a b c d else 0 := by
    intro a
    have h4 : ∀ b c : Fin n,
        (∑ d ∈ ((Finset.univ.erase a).erase b).erase c, g a b c d) =
        ∑ d : Fin n, if d ≠ c ∧ d ≠ b ∧ d ≠ a then g a b c d else 0 := by
      intro b c; rw [← Finset.sum_filter]; congr 1; ext d; simp [Finset.mem_erase]
    simp_rw [h4]
    have h3 : ∀ b : Fin n,
        (∑ c ∈ (Finset.univ.erase a).erase b, ∑ d : Fin n, if d ≠ c ∧ d ≠ b ∧ d ≠ a then g a b c d else 0) =
        ∑ c : Fin n, if c ≠ b ∧ c ≠ a then ∑ d : Fin n, if d ≠ c ∧ d ≠ b ∧ d ≠ a then g a b c d else 0 else 0 := by
      intro b; rw [← Finset.sum_filter]; congr 1; ext c; simp [Finset.mem_erase]
    simp_rw [h3]
    have h2 : (∑ b ∈ Finset.univ.erase a, ∑ c : Fin n,
          if c ≠ b ∧ c ≠ a then ∑ d : Fin n, if d ≠ c ∧ d ≠ b ∧ d ≠ a then g a b c d else 0 else 0) =
        ∑ b : Fin n, if b ≠ a then ∑ c : Fin n,
          if c ≠ b ∧ c ≠ a then ∑ d : Fin n, if d ≠ c ∧ d ≠ b ∧ d ≠ a then g a b c d else 0 else 0 else 0 := by
      rw [← Finset.sum_filter]; congr 1; ext b; simp [Finset.mem_erase]
    rw [h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hba : b = a
    · subst hba; simp
    · simp only [hba, ne_eq, not_false_eq_true, ↓reduceIte]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hcb : c = b
      · subst hcb; simp [ne_comm]
      · by_cases hca : c = a
        · subst hca; simp [ne_comm]
        · simp only [hcb, hca, not_false_eq_true, and_self, ↓reduceIte]
          refine Finset.sum_congr rfl fun d _ => ?_
          have hiff : (d ≠ c ∧ d ≠ b ∧ d ≠ a) ↔ (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
            constructor
            · rintro ⟨hdc, hdb, hda⟩; exact ⟨Ne.symm hba, Ne.symm hca, hda.symm, Ne.symm hcb, hdb.symm, hdc.symm⟩
            · rintro ⟨_, _, had, _, hbd, hcd⟩; exact ⟨hcd.symm, hbd.symm, had.symm⟩
          by_cases hd : d ≠ c ∧ d ≠ b ∧ d ≠ a
          · simp [hd, hiff.mp hd]
          · simp [hd, show ¬ (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) from fun h => hd (hiff.mpr h)]
  simp_rw [h1]
  symm
  rw [Fintype.sum_prod_type]; dsimp only
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]; dsimp only
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Fintype.sum_prod_type _

private lemma sum_P4_swap01 {n : ℕ} (g : Fin n → Fin n → Fin n → Fin n → ℤ) :
    (∑ p ∈ P4 n, g p.2.1 p.1 p.2.2.1 p.2.2.2) = ∑ p ∈ P4 n, g p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  refine Finset.sum_bij (fun p _ => (p.2.1, p.1, p.2.2.1, p.2.2.2)) ?_ ?_ ?_ ?_
  · intro p hp; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1.symm, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.1, hp.2.2.1, hp.2.2.2.2.2⟩
  · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1, d1⟩; rcases p2 with ⟨a2, b2, c2, d2⟩; simp_all
  · intro q hq; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨(q.2.1, q.1, q.2.2.1, q.2.2.2), by
      simp [P4, hq.1.symm, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.1, hq.2.2.1, hq.2.2.2.2.2], rfl⟩
  · intro _ _; rfl

private lemma sum_P4_swap12 {n : ℕ} (g : Fin n → Fin n → Fin n → Fin n → ℤ) :
    (∑ p ∈ P4 n, g p.1 p.2.2.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, g p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  refine Finset.sum_bij (fun p _ => (p.1, p.2.2.1, p.2.1, p.2.2.2)) ?_ ?_ ?_ ?_
  · intro p hp; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.2.1, hp.1, hp.2.2.1, hp.2.2.2.1.symm, hp.2.2.2.2.2, hp.2.2.2.2.1⟩
  · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1, d1⟩; rcases p2 with ⟨a2, b2, c2, d2⟩; simp_all
  · intro q hq; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨(q.1, q.2.2.1, q.2.1, q.2.2.2), by
      simp [P4, hq.2.1, hq.1, hq.2.2.1, hq.2.2.2.1.symm, hq.2.2.2.2.2, hq.2.2.2.2.1], rfl⟩
  · intro _ _; rfl

private lemma sum_P4_swap23 {n : ℕ} (g : Fin n → Fin n → Fin n → Fin n → ℤ) :
    (∑ p ∈ P4 n, g p.1 p.2.1 p.2.2.2 p.2.2.1) = ∑ p ∈ P4 n, g p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  refine Finset.sum_bij (fun p _ => (p.1, p.2.1, p.2.2.2, p.2.2.1)) ?_ ?_ ?_ ?_
  · intro p hp; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hp.2.2.1, hp.2.1, hp.2.2.2.2.1, hp.2.2.2.1, hp.2.2.2.2.2.symm⟩
  · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1, d1⟩; rcases p2 with ⟨a2, b2, c2, d2⟩; simp_all
  · intro q hq; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨(q.1, q.2.1, q.2.2.2, q.2.2.1), by
      simp [P4, hq.1, hq.2.2.1, hq.2.1, hq.2.2.2.2.1, hq.2.2.2.1, hq.2.2.2.2.2.symm], rfl⟩
  · intro _ _; rfl

private lemma P4_card {n : ℕ} (hn : 4 ≤ n) :
    (P4 n).card = n * (n - 1) * (n - 2) * (n - 3) := by
  have hz : ((P4 n).card : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
    have hs := sum_P4_eq (n := n) (fun _ _ _ _ => (1 : ℤ))
    have hconst : (∑ _p ∈ P4 n, (1 : ℤ)) = ((P4 n).card : ℤ) := by simp
    rw [hconst] at hs
    rw [hs]
    have hd : ∀ a : Fin n, ∀ b ∈ Finset.univ.erase a, ∀ c ∈ (Finset.univ.erase a).erase b,
        (∑ _d ∈ ((Finset.univ.erase a).erase b).erase c, (1 : ℤ)) = (n : ℤ) - 3 := by
      intro a b hb c hc
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hc,
          Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]
      omega
    have hc : ∀ a : Fin n, ∀ b ∈ Finset.univ.erase a,
        (∑ c ∈ (Finset.univ.erase a).erase b, ∑ _d ∈ ((Finset.univ.erase a).erase b).erase c, (1 : ℤ)) =
        ((n : ℤ) - 2) * ((n : ℤ) - 3) := by
      intro a b hb
      rw [Finset.sum_congr rfl fun c hc' => hd a b hb c hc', Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]
      have : ((n - 1 - 1 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
      rw [this]
    have hb : ∀ a : Fin n,
        (∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ _d ∈ ((Finset.univ.erase a).erase b).erase c, (1 : ℤ)) =
        ((n : ℤ) - 1) * (((n : ℤ) - 2) * ((n : ℤ) - 3)) := by
      intro a
      rw [Finset.sum_congr rfl fun b hb' => hc a b hb', Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [this]
    simp_rw [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h1 : ((P4 n).card : ℤ) = ((n * (n - 1) * (n - 2) * (n - 3) : ℕ) : ℤ) := by
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    push_cast [hn1, hn2, hn3]; exact hz
  exact_mod_cast h1

private def phiTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (a b c d : Fin n) : ℤ :=
  phiFlip (decide (G.Adj v (flip v a))) (edgeFlag G v a b) (edgeFlag G v a c) (edgeFlag G v a d)

private def b4PairTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (a b c d : Fin n) : ℤ :=
  b4Pair (decide (G.Adj v (flip v a))) (decide (G.Adj v (flip v b)))
         (decide (G.Adj (flip v a) (flip (flip v a) b))) (decide (G.Adj (flip v b) (flip (flip v b) a)))
         (decide (G.Adj v (flip v c))) (decide (G.Adj v (flip v d)))
         (decide (G.Adj (flip v c) (flip (flip v c) d))) (decide (G.Adj (flip v d) (flip (flip v d) c)))

private def q2PairTerm {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (a b c d : Fin n) : ℤ :=
  q2Term (decide (G.Adj v (flip v a))) (decide (G.Adj v (flip v b)))
         (decide (G.Adj (flip v a) (flip (flip v a) b))) (decide (G.Adj (flip v b) (flip (flip v b) a)))
         (decide (G.Adj v (flip v c))) (decide (G.Adj (flip v a) (flip (flip v a) c)))
         (decide (G.Adj (flip v b) (flip (flip v b) c))) (decide (G.Adj (flip v c) (flip (flip v c) a)))
         (decide (G.Adj (flip v c) (flip (flip v c) b)))
         (decide (G.Adj v (flip v d))) (decide (G.Adj (flip v a) (flip (flip v a) d)))
         (decide (G.Adj (flip v b) (flip (flip v b) d))) (decide (G.Adj (flip v d) (flip (flip v d) a)))
         (decide (G.Adj (flip v d) (flip (flip v d) b)))

private def b24Term {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (v : Fin n → Bool) (a b c d : Fin n) : ℤ :=
  6 * (lamTerm G v a b c + lamTerm G v a b d + lamTerm G v a c d + lamTerm G v b c d) +
  6 * (phiTerm G v a b c d + phiTerm G v b a c d + phiTerm G v c a b d + phiTerm G v d a b c) +
  8 * (b4PairTerm G v a b c d + b4PairTerm G v a c b d + b4PairTerm G v a d b c) +
  2 * (q2PairTerm G v a b c d + q2PairTerm G v b a c d +
       q2PairTerm G v a c b d + q2PairTerm G v c a b d +
       q2PairTerm G v a d b c + q2PairTerm G v d a b c +
       q2PairTerm G v b c a d + q2PairTerm G v c b a d +
       q2PairTerm G v b d a c + q2PairTerm G v d b a c +
       q2PairTerm G v c d a b + q2PairTerm G v d c a b)

private lemma b24_local_bound {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : G ≤ Q n) (hfree : IsC4Free G)
    (v : Fin n → Bool) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    b24Term G v a b c d ≤ M4 := by
  have hnoface := (isC4Free_iff_no_face hG).mp hfree
  have hface_ok : ∀ i j : Fin n, i ≠ j →
      (!(decide (G.Adj v (flip v i)) && decide (G.Adj v (flip v j)) &&
         decide (G.Adj (flip v i) (flip (flip v i) j)) &&
         decide (G.Adj (flip v j) (flip (flip v j) i)))) = true := by
    intro i j hij
    cases h1 : decide (G.Adj v (flip v i)) <;>
    cases h2 : decide (G.Adj v (flip v j)) <;>
    cases h3 : decide (G.Adj (flip v i) (flip (flip v i) j)) <;>
    cases h4 : decide (G.Adj (flip v j) (flip (flip v j) i)) <;> try rfl
    exfalso
    simp only [decide_eq_true_eq] at h1 h2 h3 h4
    exact hnoface v i j hij ⟨h1, h3, by rw [flip_comm]; exact h4.symm, h2.symm⟩
  have hc4 : c4FreeB24
      (decide (G.Adj v (flip v a))) (decide (G.Adj v (flip v b)))
      (decide (G.Adj v (flip v c))) (decide (G.Adj v (flip v d)))
      (decide (G.Adj (flip v a) (flip (flip v a) b))) (decide (G.Adj (flip v b) (flip (flip v b) a)))
      (decide (G.Adj (flip v a) (flip (flip v a) c))) (decide (G.Adj (flip v c) (flip (flip v c) a)))
      (decide (G.Adj (flip v a) (flip (flip v a) d))) (decide (G.Adj (flip v d) (flip (flip v d) a)))
      (decide (G.Adj (flip v b) (flip (flip v b) c))) (decide (G.Adj (flip v c) (flip (flip v c) b)))
      (decide (G.Adj (flip v b) (flip (flip v b) d))) (decide (G.Adj (flip v d) (flip (flip v d) b)))
      (decide (G.Adj (flip v c) (flip (flip v c) d))) (decide (G.Adj (flip v d) (flip (flip v d) c))) = true := by
    unfold c4FreeB24
    rw [hface_ok a b hab, hface_ok a c hac, hface_ok a d had,
        hface_ok b c hbc, hface_ok b d hbd, hface_ok c d hcd]
    rfl
  exact b24LocalBool_le_M4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc4

private lemma sum_phiTerm_eq_zero {n : ℕ} (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (a b c d : Fin n) :
    (∑ v : Fin n → Bool, phiTerm G v a b c d) = 0 := by
  let invA : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun v => flip v a
      invFun := fun v => flip v a
      left_inv := fun v => flip_flip v a
      right_inv := fun v => flip_flip v a }
  have hswap : ∀ v : Fin n → Bool,
      phiTerm G (flip v a) a b c d =
      phiFlip (decide (G.Adj v (flip v a)))
        (flipF (edgeFlag G v a b)) (flipF (edgeFlag G v a c)) (flipF (edgeFlag G v a d)) := by
    intro v
    dsimp only [phiTerm]
    have he : decide (G.Adj (flip v a) (flip (flip v a) a)) = decide (G.Adj v (flip v a)) := by
      rw [flip_flip]; simp [SimpleGraph.adj_comm]
    have hfl : ∀ j : Fin n, edgeFlag G (flip v a) a j = flipF (edgeFlag G v a j) := by
      intro j
      dsimp only [edgeFlag]
      rw [flipF_mkFlag]
      have h2 : decide (G.Adj (flip (flip v a) a) (flip (flip (flip v a) a) j)) =
          decide (G.Adj v (flip v j)) := by rw [flip_flip]
      have h3 : decide (G.Adj (flip (flip v a) j) (flip (flip (flip v a) j) a)) =
          decide (G.Adj (flip v j) (flip (flip v j) a)) := by
        rw [flip_comm (flip v a) j a, flip_flip, flip_comm v a j]
        simp [SimpleGraph.adj_comm]
      rw [h2, h3]
    rw [he, hfl b, hfl c, hfl d]
  have h1 : (∑ v : Fin n → Bool, phiTerm G v a b c d) =
      ∑ v : Fin n → Bool, phiTerm G (flip v a) a b c d :=
    (Fintype.sum_equiv invA _ _ (fun _ => rfl)).symm
  have h2 : 2 * (∑ v : Fin n → Bool, phiTerm G v a b c d) = 0 := by
    calc 2 * (∑ v : Fin n → Bool, phiTerm G v a b c d)
        = (∑ v : Fin n → Bool, phiTerm G v a b c d) +
          (∑ v : Fin n → Bool, phiTerm G v a b c d) := by ring
      _ = (∑ v : Fin n → Bool, phiTerm G v a b c d) +
          (∑ v : Fin n → Bool, phiTerm G (flip v a) a b c d) := by rw [← h1]
      _ = ∑ v : Fin n → Bool, (phiTerm G v a b c d + phiTerm G (flip v a) a b c d) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ _v : Fin n → Bool, (0 : ℤ) := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [hswap v]; exact phiFlip_antisymm _ _ _ _
      _ = 0 := by simp
  omega

private lemma sum_lam23_b24 {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] :
    (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
      (lamTerm G v p.1 p.2.1 p.2.2.1 + lamTerm G v p.1 p.2.1 p.2.2.2 +
       lamTerm G v p.1 p.2.2.1 p.2.2.2 + lamTerm G v p.2.1 p.2.2.1 p.2.2.2)) =
    4 * ((n : ℤ) - 3) *
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ v : Fin n → Bool, lamTerm G v a b c) := by
  let S3 : ℤ := ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
      ∑ v : Fin n → Bool, lamTerm G v a b c
  have h012 : (∑ p ∈ P4 n, ∑ v : Fin n → Bool, lamTerm G v p.1 p.2.1 p.2.2.1) = ((n : ℤ) - 3) * S3 := by
    have hp := sum_P4_eq (n := n) (fun a b c _ => ∑ v : Fin n → Bool, lamTerm G v a b c)
    rw [hp]
    have hinner : ∀ a : Fin n, ∀ b ∈ Finset.univ.erase a, ∀ c ∈ (Finset.univ.erase a).erase b,
        (∑ _d ∈ ((Finset.univ.erase a).erase b).erase c, ∑ v : Fin n → Bool, lamTerm G v a b c) =
        ((n : ℤ) - 3) * ∑ v : Fin n → Bool, lamTerm G v a b c := by
      intro a b hb c hc
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hc,
          Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]
      have hn3 : ((n - 1 - 1 - 1 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
      rw [hn3]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun c hc => hinner a b hb c hc]
    simp only [← Finset.mul_sum]
    rfl
  have h013 : (∑ p ∈ P4 n, ∑ v : Fin n → Bool, lamTerm G v p.1 p.2.1 p.2.2.2) = ((n : ℤ) - 3) * S3 := by
    rw [sum_P4_swap23 (fun a b c _ => ∑ v : Fin n → Bool, lamTerm G v a b c)]
    exact h012
  have h023 : (∑ p ∈ P4 n, ∑ v : Fin n → Bool, lamTerm G v p.1 p.2.2.1 p.2.2.2) = ((n : ℤ) - 3) * S3 := by
    rw [sum_P4_swap12 (fun a b _ d => ∑ v : Fin n → Bool, lamTerm G v a b d)]
    exact h013
  have h123 : (∑ p ∈ P4 n, ∑ v : Fin n → Bool, lamTerm G v p.2.1 p.2.2.1 p.2.2.2) = ((n : ℤ) - 3) * S3 := by
    rw [sum_P4_swap01 (fun a _ c d => ∑ v : Fin n → Bool, lamTerm G v a c d)]
    exact h023
  simp only [Finset.sum_add_distrib]
  rw [h012, h013, h023, h123]
  ring

private lemma sum_q2Pair_lb {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] :
    - K_Q2 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 : ℤ) ^ n ≤
      ∑ p ∈ P4 n, ∑ v : Fin n → Bool, q2PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have hp := sum_P4_eq (n := n) (fun a b c d => ∑ v : Fin n → Bool, q2PairTerm G v a b c d)
  rw [hp]
  have hswap_v :
      (∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
        ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, ∑ v : Fin n → Bool, q2PairTerm G v a b c d) =
      ∑ v : Fin n → Bool, ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a,
        ∑ c ∈ (Finset.univ.erase a).erase b, ∑ d ∈ ((Finset.univ.erase a).erase b).erase c,
          q2PairTerm G v a b c d := by
    have s1 : ∀ a : Fin n,
        (∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, ∑ v : Fin n → Bool, q2PairTerm G v a b c d) =
        ∑ v : Fin n → Bool, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, q2PairTerm G v a b c d := fun a => by
      have s2 : ∀ b ∈ Finset.univ.erase a,
          (∑ c ∈ (Finset.univ.erase a).erase b,
            ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, ∑ v : Fin n → Bool, q2PairTerm G v a b c d) =
          ∑ v : Fin n → Bool, ∑ c ∈ (Finset.univ.erase a).erase b,
            ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, q2PairTerm G v a b c d := fun b _ => by
        have s3 : ∀ c ∈ (Finset.univ.erase a).erase b,
            (∑ d ∈ ((Finset.univ.erase a).erase b).erase c, ∑ v : Fin n → Bool, q2PairTerm G v a b c d) =
            ∑ v : Fin n → Bool, ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, q2PairTerm G v a b c d :=
          fun _ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl s3]; exact Finset.sum_comm
      rw [Finset.sum_congr rfl s2]; exact Finset.sum_comm
    simp_rw [s1]; exact Finset.sum_comm
  rw [hswap_v]
  have hpt : ∀ (v : Fin n → Bool) (a b : Fin n), b ∈ Finset.univ.erase a →
      - K_Q2 * ((n : ℤ) - 2) ≤
        ∑ c ∈ (Finset.univ.erase a).erase b, ∑ d ∈ ((Finset.univ.erase a).erase b).erase c,
          q2PairTerm G v a b c d := by
    intro v a b hb
    set S := (Finset.univ.erase a).erase b
    have hScard : (S.card : ℤ) = (n : ℤ) - 2 := by
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ, Fintype.card_fin]; omega
    by_cases hcan : isCanonRoot (decide (G.Adj v (flip v a))) (decide (G.Adj v (flip v b)))
        (decide (G.Adj (flip v a) (flip (flip v a) b))) (decide (G.Adj (flip v b) (flip (flip v b) a))) = true
    · set r := rcIdx (decide (G.Adj v (flip v a))) (decide (G.Adj v (flip v b)))
          (decide (G.Adj (flip v a) (flip (flip v a) b))) (decide (G.Adj (flip v b) (flip (flip v b) a)))
      let qf (s : Fin 8) (x : Fin n) : ℤ :=
        q2W r s (decide (G.Adj v (flip v x))) (decide (G.Adj (flip v a) (flip (flip v a) x)))
          (decide (G.Adj (flip v b) (flip (flip v b) x)))
          (decide (G.Adj (flip v x) (flip (flip v x) a))) (decide (G.Adj (flip v x) (flip (flip v x) b)))
      have hrew : ∀ c d : Fin n, q2PairTerm G v a b c d =
          qf 0 c * qf 0 d + qf 1 c * qf 1 d + qf 2 c * qf 2 d + qf 3 c * qf 3 d +
          qf 4 c * qf 4 d + qf 5 c * qf 5 d + qf 6 c * qf 6 d + qf 7 c * qf 7 d := fun c d => by
        dsimp only [q2PairTerm, q2Term, qf]; simp only [hcan, ↓reduceIte]; rfl
      simp_rw [hrew, Finset.sum_add_distrib]
      have h0 := hsos S (qf 0); have h1 := hsos S (qf 1); have h2 := hsos S (qf 2); have h3 := hsos S (qf 3)
      have h4 := hsos S (qf 4); have h5 := hsos S (qf 5); have h6 := hsos S (qf 6); have h7 := hsos S (qf 7)
      have hdiag : ∑ c ∈ S, (qf 0 c ^ 2 + qf 1 c ^ 2 + qf 2 c ^ 2 + qf 3 c ^ 2 +
          qf 4 c ^ 2 + qf 5 c ^ 2 + qf 6 c ^ 2 + qf 7 c ^ 2) ≤ K_Q2 * ((n : ℤ) - 2) := by
        calc ∑ c ∈ S, (qf 0 c ^ 2 + qf 1 c ^ 2 + qf 2 c ^ 2 + qf 3 c ^ 2 +
              qf 4 c ^ 2 + qf 5 c ^ 2 + qf 6 c ^ 2 + qf 7 c ^ 2)
            ≤ ∑ _c ∈ S, K_Q2 := Finset.sum_le_sum fun c _ => q2W_sq_le r _ _ _ _ _
          _ = K_Q2 * ((n : ℤ) - 2) := by rw [Finset.sum_const, nsmul_eq_mul, hScard]; ring
      simp only [Finset.sum_add_distrib] at hdiag
      linarith
    · have hzero : ∀ c d : Fin n, q2PairTerm G v a b c d = 0 := fun c d => by
        dsimp only [q2PairTerm, q2Term]; simp [hcan]
      simp_rw [hzero, Finset.sum_const_zero]
      have hK_nonneg : 0 ≤ K_Q2 := by decide
      have hn2 : (0 : ℤ) ≤ (n : ℤ) - 2 := by omega
      nlinarith
  have hsum_v :
      ∑ _v : Fin n → Bool, ∑ _a : Fin n, ∑ _b ∈ Finset.univ.erase _a, (- K_Q2 * ((n : ℤ) - 2)) ≤
      ∑ v : Fin n → Bool, ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a,
        ∑ c ∈ (Finset.univ.erase a).erase b, ∑ d ∈ ((Finset.univ.erase a).erase b).erase c,
          q2PairTerm G v a b c d :=
    Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun a _ =>
      Finset.sum_le_sum fun b hb => hpt v a b hb
  refine le_trans (le_of_eq ?_) hsum_v
  have hb_const : ∀ a : Fin n,
      (∑ _b ∈ Finset.univ.erase a, (- K_Q2 * ((n : ℤ) - 2))) = ((n : ℤ) - 1) * (- K_Q2 * ((n : ℤ) - 2)) := by
    intro a
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, Fintype.card_fin]
    have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hn1]
  simp_rw [hb_const, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring

private lemma sum_b4Pair_lb {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj] :
    - K_B4 * (n : ℤ) * ((n : ℤ) - 1) * (4 * (n : ℤ) - 6) * (2 : ℤ) ^ n ≤
      ∑ p ∈ P4 n, ∑ v : Fin n → Bool, b4PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let P2 : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  let Q4 : Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
    (P2 ×ˢ P2).filter (fun q => q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧ q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2)
  have hP2_card : P2.card = n * (n - 1) := by
    have heq : (∑ _p ∈ P2, (1 : ℕ)) = ∑ a : Fin n, ∑ _b ∈ Finset.univ.erase a, 1 := by
      dsimp only [P2]; rw [Finset.sum_filter]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_filter]; congr 1; ext b; simp [Finset.mem_erase, ne_comm]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] at heq
    rw [heq]
    have hs : ∀ a : Fin n, (Finset.univ.erase a).card = n - 1 := fun a => by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    simp_rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Nat.cast_id]
  have hQ4_sub : Q4 ⊆ P2 ×ˢ P2 := Finset.filter_subset _ _
  have hpt_v : ∀ v : Fin n → Bool,
      - K_B4 * (n : ℤ) * ((n : ℤ) - 1) * (4 * (n : ℤ) - 6) ≤
        ∑ p ∈ P4 n, b4PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    intro v
    have hbij : (∑ p ∈ P4 n, b4PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2) =
        ∑ q ∈ Q4, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2 := by
      refine Finset.sum_bij (fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) ?_ ?_ ?_ ?_
      · intro p hp; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Q4, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
        exact ⟨⟨hp.1, hp.2.2.2.2.2⟩, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩
      · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1, d1⟩; rcases p2 with ⟨a2, b2, c2, d2⟩; simp_all
      · intro q hq; simp only [Q4, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq
        exact ⟨(q.1.1, q.1.2, q.2.1, q.2.2), by
          simp [P4, hq.1.1, hq.1.2, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2], rfl⟩
      · intro _ _; rfl
    have hQ4_card : Q4.card = (P4 n).card := by
      refine Finset.card_bij (fun q _ => (q.1.1, q.1.2, q.2.1, q.2.2)) ?_ ?_ ?_
      · intro q hq; simp only [Q4, P2, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hq
        simp [P4, hq.1.1, hq.1.2, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2]
      · intro q1 _ q2 _ h; rcases q1 with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩; rcases q2 with ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩; simp_all
      · intro p hp; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact ⟨((p.1, p.2.1), (p.2.2.1, p.2.2.2)), by
          simp [Q4, P2, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2], rfl⟩
    have hdiff_card : (((P2 ×ˢ P2) \ Q4).card : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * (4 * (n : ℤ) - 6) := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hQ4_sub, Finset.card_product, hP2_card, hQ4_card, P4_card hn]
      have hge : n * (n - 1) * (n - 2) * (n - 3) ≤ (n * (n - 1)) * (n * (n - 1)) := by
        calc n * (n - 1) * (n - 2) * (n - 3)
            = (n * (n - 1)) * ((n - 2) * (n - 3)) := by ring
          _ ≤ (n * (n - 1)) * (n * (n - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      rw [Nat.cast_sub hge]
      have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
      have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
      push_cast [hn1, hn2, hn3]; ring
    let bf (s : Fin 5) (p : Fin n × Fin n) : ℤ :=
      b4V s (rcIdx (decide (G.Adj v (flip v p.1))) (decide (G.Adj v (flip v p.2)))
        (decide (G.Adj (flip v p.1) (flip (flip v p.1) p.2)))
        (decide (G.Adj (flip v p.2) (flip (flip v p.2) p.1))))
    have hfull_nonneg : (0 : ℤ) ≤ ∑ q ∈ P2 ×ˢ P2, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2 := by
      have hdec : ∀ q : (Fin n × Fin n) × (Fin n × Fin n),
          b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2 =
          bf 0 q.1 * bf 0 q.2 + bf 1 q.1 * bf 1 q.2 + bf 2 q.1 * bf 2 q.2 +
          bf 3 q.1 * bf 3 q.2 + bf 4 q.1 * bf 4 q.2 := fun _ => rfl
      simp_rw [hdec, Finset.sum_add_distrib]
      have hsq : ∀ s : Fin 5, (0 : ℤ) ≤ ∑ q ∈ P2 ×ˢ P2, bf s q.1 * bf s q.2 := fun s => by
        rw [Finset.sum_product, ← Finset.sum_mul_sum, ← sq]
        exact sq_nonneg _
      linarith [hsq 0, hsq 1, hsq 2, hsq 3, hsq 4]
    have hrem_ub : ∑ q ∈ (P2 ×ˢ P2) \ Q4, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2 ≤
        K_B4 * (((P2 ×ˢ P2) \ Q4).card : ℤ) := by
      have hpt_le : ∀ q : (Fin n × Fin n) × (Fin n × Fin n),
          b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2 ≤ K_B4 := fun q => by
        have h2 : 2 * b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2 ≤
            (bf 0 q.1 ^ 2 + bf 1 q.1 ^ 2 + bf 2 q.1 ^ 2 + bf 3 q.1 ^ 2 + bf 4 q.1 ^ 2) +
            (bf 0 q.2 ^ 2 + bf 1 q.2 ^ 2 + bf 2 q.2 ^ 2 + bf 3 q.2 ^ 2 + bf 4 q.2 ^ 2) := by
          dsimp only [b4PairTerm, b4Pair, bf]
          linarith [sq_nonneg (bf 0 q.1 - bf 0 q.2), sq_nonneg (bf 1 q.1 - bf 1 q.2),
            sq_nonneg (bf 2 q.1 - bf 2 q.2), sq_nonneg (bf 3 q.1 - bf 3 q.2), sq_nonneg (bf 4 q.1 - bf 4 q.2)]
        have hb1 := b4V_sq_le (rcIdx (decide (G.Adj v (flip v q.1.1))) (decide (G.Adj v (flip v q.1.2)))
          (decide (G.Adj (flip v q.1.1) (flip (flip v q.1.1) q.1.2)))
          (decide (G.Adj (flip v q.1.2) (flip (flip v q.1.2) q.1.1))))
        have hb2 := b4V_sq_le (rcIdx (decide (G.Adj v (flip v q.2.1))) (decide (G.Adj v (flip v q.2.2)))
          (decide (G.Adj (flip v q.2.1) (flip (flip v q.2.1) q.2.2)))
          (decide (G.Adj (flip v q.2.2) (flip (flip v q.2.2) q.2.1))))
        dsimp only [bf] at h2; omega
      calc ∑ q ∈ (P2 ×ˢ P2) \ Q4, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2
          ≤ ∑ _q ∈ (P2 ×ˢ P2) \ Q4, K_B4 := Finset.sum_le_sum fun q _ => hpt_le q
        _ = K_B4 * (((P2 ×ˢ P2) \ Q4).card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hsplit : (∑ q ∈ P2 ×ˢ P2, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2) =
        (∑ q ∈ Q4, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2) +
        (∑ q ∈ (P2 ×ˢ P2) \ Q4, b4PairTerm G v q.1.1 q.1.2 q.2.1 q.2.2) :=
      (Finset.sum_sdiff hQ4_sub).symm.trans (add_comm _ _)
    rw [hbij]; rw [hdiff_card] at hrem_ub; linarith
  rw [Finset.sum_comm]
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpt_v v
  refine le_trans ?_ hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
    Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring_nf; exact le_rfl

private lemma b24_global_bound {n : ℕ} (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [DecidableRel G.Adj]
    (hG : G ≤ Q n) (hfree : IsC4Free G) :
    let L : ℤ := ∑ a : Fin n, ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
      ∑ v : Fin n → Bool, lamTerm G v a b c
    24 * ((n : ℤ) - 3) * L -
      24 * (K_B4 * (n : ℤ) * ((n : ℤ) - 1) * (4 * (n : ℤ) - 6) +
            K_Q2 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2)) * (2 : ℤ) ^ n ≤
      M4 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (2 : ℤ) ^ n := by
  intro L
  have h_ub : (∑ p ∈ P4 n, ∑ v : Fin n → Bool, b24Term G v p.1 p.2.1 p.2.2.1 p.2.2.2) ≤
      M4 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (2 : ℤ) ^ n := by
    have hpt : ∀ p ∈ P4 n, ∀ v : Fin n → Bool, b24Term G v p.1 p.2.1 p.2.2.1 p.2.2.2 ≤ M4 := by
      intro p hp v
      simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact b24_local_bound G hG hfree v hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2
    calc (∑ p ∈ P4 n, ∑ v : Fin n → Bool, b24Term G v p.1 p.2.1 p.2.2.1 p.2.2.2)
        ≤ ∑ _p ∈ P4 n, ∑ _v : Fin n → Bool, M4 :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun v _ => hpt p hp v
      _ = M4 * (n : ℤ) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (2 : ℤ) ^ n := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
            Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, P4_card hn]
          have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
          have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
          have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
          push_cast [hn1, hn2, hn3]; ring
  have hsplit_b24 :
      (∑ p ∈ P4 n, ∑ v : Fin n → Bool, b24Term G v p.1 p.2.1 p.2.2.1 p.2.2.2) =
      6 * (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
            (lamTerm G v p.1 p.2.1 p.2.2.1 + lamTerm G v p.1 p.2.1 p.2.2.2 +
             lamTerm G v p.1 p.2.2.1 p.2.2.2 + lamTerm G v p.2.1 p.2.2.1 p.2.2.2)) +
      6 * (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
            (phiTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 + phiTerm G v p.2.1 p.1 p.2.2.1 p.2.2.2 +
             phiTerm G v p.2.2.1 p.1 p.2.1 p.2.2.2 + phiTerm G v p.2.2.2 p.1 p.2.1 p.2.2.1)) +
      8 * (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
            (b4PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 + b4PairTerm G v p.1 p.2.2.1 p.2.1 p.2.2.2 +
             b4PairTerm G v p.1 p.2.2.2 p.2.1 p.2.2.1)) +
      2 * (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
            (q2PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 + q2PairTerm G v p.2.1 p.1 p.2.2.1 p.2.2.2 +
             q2PairTerm G v p.1 p.2.2.1 p.2.1 p.2.2.2 + q2PairTerm G v p.2.2.1 p.1 p.2.1 p.2.2.2 +
             q2PairTerm G v p.1 p.2.2.2 p.2.1 p.2.2.1 + q2PairTerm G v p.2.2.2 p.1 p.2.1 p.2.2.1 +
             q2PairTerm G v p.2.1 p.2.2.1 p.1 p.2.2.2 + q2PairTerm G v p.2.2.1 p.2.1 p.1 p.2.2.2 +
             q2PairTerm G v p.2.1 p.2.2.2 p.1 p.2.2.1 + q2PairTerm G v p.2.2.2 p.2.1 p.1 p.2.2.1 +
             q2PairTerm G v p.2.2.1 p.2.2.2 p.1 p.2.1 + q2PairTerm G v p.2.2.2 p.2.2.1 p.1 p.2.1)) := by
    simp only [b24Term, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hflip0 :
      (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
        (phiTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 + phiTerm G v p.2.1 p.1 p.2.2.1 p.2.2.2 +
         phiTerm G v p.2.2.1 p.1 p.2.1 p.2.2.2 + phiTerm G v p.2.2.2 p.1 p.2.1 p.2.2.1)) = 0 := by
    refine Finset.sum_eq_zero fun p _ => ?_
    simp only [Finset.sum_add_distrib, sum_phiTerm_eq_zero]; norm_num
  have hb4_all :
      (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
        (b4PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 + b4PairTerm G v p.1 p.2.2.1 p.2.1 p.2.2.2 +
         b4PairTerm G v p.1 p.2.2.2 p.2.1 p.2.2.1)) =
      3 * ∑ p ∈ P4 n, ∑ v : Fin n → Bool, b4PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    let F (a b c d : Fin n) : ℤ := ∑ v : Fin n → Bool, b4PairTerm G v a b c d
    have h1 : (∑ p ∈ P4 n, F p.1 p.2.2.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      sum_P4_swap12 F
    have h2 : (∑ p ∈ P4 n, F p.1 p.2.2.2 p.2.1 p.2.2.1) = ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap23 (fun a b c d => F a d b c)).symm.trans h1
    simp_rw [Finset.sum_add_distrib]
    change (∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2) +
           (∑ p ∈ P4 n, F p.1 p.2.2.1 p.2.1 p.2.2.2) +
           (∑ p ∈ P4 n, F p.1 p.2.2.2 p.2.1 p.2.2.1) =
           3 * ∑ p ∈ P4 n, F p.1 p.2.1 p.2.2.1 p.2.2.2
    rw [h1, h2]; ring
  have hq2_all :
      (∑ p ∈ P4 n, ∑ v : Fin n → Bool,
        (q2PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 + q2PairTerm G v p.2.1 p.1 p.2.2.1 p.2.2.2 +
         q2PairTerm G v p.1 p.2.2.1 p.2.1 p.2.2.2 + q2PairTerm G v p.2.2.1 p.1 p.2.1 p.2.2.2 +
         q2PairTerm G v p.1 p.2.2.2 p.2.1 p.2.2.1 + q2PairTerm G v p.2.2.2 p.1 p.2.1 p.2.2.1 +
         q2PairTerm G v p.2.1 p.2.2.1 p.1 p.2.2.2 + q2PairTerm G v p.2.2.1 p.2.1 p.1 p.2.2.2 +
         q2PairTerm G v p.2.1 p.2.2.2 p.1 p.2.2.1 + q2PairTerm G v p.2.2.2 p.2.1 p.1 p.2.2.1 +
         q2PairTerm G v p.2.2.1 p.2.2.2 p.1 p.2.1 + q2PairTerm G v p.2.2.2 p.2.2.1 p.1 p.2.1)) =
      12 * ∑ p ∈ P4 n, ∑ v : Fin n → Bool, q2PairTerm G v p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    let H (a b c d : Fin n) : ℤ := ∑ v : Fin n → Bool, q2PairTerm G v a b c d
    have s_ba : (∑ p ∈ P4 n, H p.2.1 p.1 p.2.2.1 p.2.2.2) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      sum_P4_swap01 H
    have s_ac : (∑ p ∈ P4 n, H p.1 p.2.2.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      sum_P4_swap12 H
    have s_ca : (∑ p ∈ P4 n, H p.2.2.1 p.1 p.2.1 p.2.2.2) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap12 (fun a b c d => H b a c d)).trans s_ba
    have s_bc : (∑ p ∈ P4 n, H p.2.1 p.2.2.1 p.1 p.2.2.2) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap01 (fun a b c d => H a c b d)).trans s_ac
    have s_cb : (∑ p ∈ P4 n, H p.2.2.1 p.2.1 p.1 p.2.2.2) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap01 (fun a b c d => H c a b d)).trans s_ca
    have s_ad : (∑ p ∈ P4 n, H p.1 p.2.2.2 p.2.1 p.2.2.1) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap23 (fun a b c d => H a c b d)).trans s_ac
    have s_da : (∑ p ∈ P4 n, H p.2.2.2 p.1 p.2.1 p.2.2.1) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap23 (fun a b c d => H c a b d)).trans s_ca
    have s_bd : (∑ p ∈ P4 n, H p.2.1 p.2.2.2 p.1 p.2.2.1) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap23 (fun a b c d => H b c a d)).trans s_bc
    have s_db : (∑ p ∈ P4 n, H p.2.2.2 p.2.1 p.1 p.2.2.1) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap23 (fun a b c d => H c b a d)).trans s_cb
    have s_cd : (∑ p ∈ P4 n, H p.2.2.1 p.2.2.2 p.1 p.2.1) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 := by
      refine Finset.sum_bij (fun p _ => (p.2.2.1, p.2.2.2, p.1, p.2.1)) ?_ ?_ ?_ ?_
      · intro p hp; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact ⟨hp.2.2.2.2.2, hp.2.1.symm, hp.2.2.2.1.symm, hp.2.2.1.symm, hp.2.2.2.2.1.symm, hp.1⟩
      · intro p1 _ p2 _ h; rcases p1 with ⟨a1, b1, c1, d1⟩; rcases p2 with ⟨a2, b2, c2, d2⟩; simp_all
      · intro q hq; simp only [P4, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨(q.2.2.1, q.2.2.2, q.1, q.2.1), by
          simp [P4, hq.2.2.2.2.2, hq.2.1.symm, hq.2.2.2.1.symm, hq.2.2.1.symm, hq.2.2.2.2.1.symm, hq.1], rfl⟩
      · intro _ _; rfl
    have s_dc : (∑ p ∈ P4 n, H p.2.2.2 p.2.2.1 p.1 p.2.1) = ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2 :=
      (sum_P4_swap23 (fun a b c d => H c d a b)).trans s_cd
    simp_rw [Finset.sum_add_distrib]
    change (∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2) +
           (∑ p ∈ P4 n, H p.2.1 p.1 p.2.2.1 p.2.2.2) +
           (∑ p ∈ P4 n, H p.1 p.2.2.1 p.2.1 p.2.2.2) +
           (∑ p ∈ P4 n, H p.2.2.1 p.1 p.2.1 p.2.2.2) +
           (∑ p ∈ P4 n, H p.1 p.2.2.2 p.2.1 p.2.2.1) +
           (∑ p ∈ P4 n, H p.2.2.2 p.1 p.2.1 p.2.2.1) +
           (∑ p ∈ P4 n, H p.2.1 p.2.2.1 p.1 p.2.2.2) +
           (∑ p ∈ P4 n, H p.2.2.1 p.2.1 p.1 p.2.2.2) +
           (∑ p ∈ P4 n, H p.2.1 p.2.2.2 p.1 p.2.2.1) +
           (∑ p ∈ P4 n, H p.2.2.2 p.2.1 p.1 p.2.2.1) +
           (∑ p ∈ P4 n, H p.2.2.1 p.2.2.2 p.1 p.2.1) +
           (∑ p ∈ P4 n, H p.2.2.2 p.2.2.1 p.1 p.2.1) =
           12 * ∑ p ∈ P4 n, H p.1 p.2.1 p.2.2.1 p.2.2.2
    rw [s_ba, s_ac, s_ca, s_ad, s_da, s_bc, s_cb, s_bd, s_db, s_cd, s_dc]
    ring
  have hlam_all := sum_lam23_b24 hn G
  have hb4_lb := sum_b4Pair_lb hn G
  have hq2_lb := sum_q2Pair_lb hn G
  rw [hsplit_b24, hflip0, hb4_all, hq2_all] at h_ub
  linarith

end B2Q4Global

/-! ## Section 4: Headline Pure-Mathlib World-Record Theorems -/

section HeadlineTheorems

/-- **Theorem (`ppl033_b2q4_upper_exact`):**
Coupled `Q_3 + B_2(Q_4)` Flag-Algebra Sum-of-Squares upper bound:
for every `n ≥ 4` and every `C_4`-free subgraph `G ≤ Q_n`,
`48 * 100000000 * (n - 2) * (n - 3) * |E(G)| ≤ 1447121170 * n * (n - 2) * (n - 3) * 2 ^ n +`
`  24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2)) * n * 2 ^ n`
(pure Mathlib signature, zero custom/private symbols exposed). -/
theorem ppl033_b2q4_upper_exact (n : ℕ) (hn : 4 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    48 * 100000000 * (n - 2) * (n - 3) * G.edgeFinset.card ≤
      1447121170 * n * (n - 2) * (n - 3) * 2 ^ n +
      24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2)) * n * 2 ^ n := by
  classical
  rw [edgeFinset_card_congr G _ (SimpleGraph.fintypeEdgeSet G)]
  clear ‹Fintype G.edgeSet›
  have hq3 := q3_global_bound hn G hG hfree
  have hb24 := b24_global_bound hn G hG hfree
  have hn3_nonneg : (0 : ℤ) ≤ (n : ℤ) - 3 := by omega
  have hq3_mul := mul_le_mul_of_nonneg_left hq3 hn3_nonneg
  have hcomb :
      ((n : ℤ) - 1) * (48 * D_edge * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (G.edgeFinset.card : ℤ)) ≤
      ((n : ℤ) - 1) * ((M3 + M4) * (n : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (2 : ℤ) ^ n +
        24 * (K_Q3 * ((n : ℤ) - 3) + K_B4 * (4 * (n : ℤ) - 6) + K_Q2 * ((n : ℤ) - 2)) *
          (n : ℤ) * (2 : ℤ) ^ n) := by
    linarith
  have hpos1 : (0 : ℤ) < (n : ℤ) - 1 := by omega
  have hZ := le_of_mul_le_mul_left hcomb hpos1
  have hn2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
  have hn46 : ((4 * n - 6 : ℕ) : ℤ) = 4 * (n : ℤ) - 6 := by omega
  change ((48 : ℤ) * 100000000 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (G.edgeFinset.card : ℤ)) ≤
      ((897230798 + 549890372) * (n : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (2 : ℤ) ^ n +
        24 * (101444909 * ((n : ℤ) - 3) + 50128370 * (4 * (n : ℤ) - 6) +
          173258785 * ((n : ℤ) - 2)) * (n : ℤ) * (2 : ℤ) ^ n) at hZ
  rw [← hn2, ← hn3, ← hn46] at hZ
  have hZ' :
      (((48 * 100000000 * (n - 2) * (n - 3) * G.edgeFinset.card : ℕ) : ℤ)) ≤
      (((1447121170 * n * (n - 2) * (n - 3) * 2 ^ n +
         24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) +
           173258785 * (n - 2)) * n * 2 ^ n : ℕ) : ℤ)) := by
    push_cast; linarith
  exact_mod_cast hZ'

/-- **Theorem (`ppl033_beats_baber_2012_explicit`):**
Explicit improvement over Baber (2012) `0.60318`:
for every `n ≥ 22330` and every `C_4`-free `G ≤ Q_n`,
`100000 * |E(G)| < 60318 * (n * 2 ^ (n - 1))` (pure Mathlib signature). -/
theorem ppl033_beats_baber_2012_explicit (n : ℕ) (hn : 22330 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    100000 * G.edgeFinset.card < 60318 * (n * 2 ^ (n - 1)) := by
  have hsos := ppl033_b2q4_upper_exact n (by omega) G hG hfree
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]; ring
  rw [hpow] at hsos
  have hposE : 0 < n * 2 ^ (n - 1) := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
  have hk : (1447121170 * (n - 2) * (n - 3) +
      24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2))) * 2 * 100000 <
      60318 * 48 * 100000000 * (n - 2) * (n - 3) := by
    set k : ℕ := n - 3
    have hk_ge : 22327 ≤ k := by omega
    have hn2 : n - 2 = k + 1 := by omega
    have h46 : 4 * n - 6 = 4 * k + 6 := by omega
    rw [hn2, h46]
    nlinarith
  have hstrict :
      (48 * 100000000 * (n - 2) * (n - 3)) * (100000 * G.edgeFinset.card) <
      (48 * 100000000 * (n - 2) * (n - 3)) * (60318 * (n * 2 ^ (n - 1))) := by
    calc (48 * 100000000 * (n - 2) * (n - 3)) * (100000 * G.edgeFinset.card)
        = 100000 * (48 * 100000000 * (n - 2) * (n - 3) * G.edgeFinset.card) := by ring
      _ ≤ 100000 * (1447121170 * n * (n - 2) * (n - 3) * (2 * 2 ^ (n - 1)) +
            24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2)) *
              n * (2 * 2 ^ (n - 1))) := Nat.mul_le_mul_left 100000 hsos
      _ = ((1447121170 * (n - 2) * (n - 3) +
            24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2))) * 2 * 100000) *
            (n * 2 ^ (n - 1)) := by ring
      _ < (60318 * 48 * 100000000 * (n - 2) * (n - 3)) * (n * 2 ^ (n - 1)) :=
            Nat.mul_lt_mul_of_pos_right hk hposE
      _ = (48 * 100000000 * (n - 2) * (n - 3)) * (60318 * (n * 2 ^ (n - 1))) := by ring
  exact Nat.lt_of_mul_lt_mul_left hstrict

/-- **Theorem (`ppl033_lt_603_explicit`):**
Explicit sub-`0.6030` bound: for every `n ≥ 144685` and every `C_4`-free `G ≤ Q_n`,
`1000 * |E(G)| < 603 * (n * 2 ^ (n - 1))` (pure Mathlib signature). -/
theorem ppl033_lt_603_explicit (n : ℕ) (hn : 144685 ≤ n)
    (G : SimpleGraph (Fin n → Bool)) [Fintype G.edgeSet]
    (hG : G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
      (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1))
    (hfree : ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) :
    1000 * G.edgeFinset.card < 603 * (n * 2 ^ (n - 1)) := by
  have hsos := ppl033_b2q4_upper_exact n (by omega) G hG hfree
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]; ring
  rw [hpow] at hsos
  have hposE : 0 < n * 2 ^ (n - 1) := Nat.mul_pos (by omega) (Nat.pos_of_ne_zero (by positivity))
  have hk : (1447121170 * (n - 2) * (n - 3) +
      24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2))) * 2 * 1000 <
      603 * 48 * 100000000 * (n - 2) * (n - 3) := by
    set k : ℕ := n - 3
    have hk_ge : 144682 ≤ k := by omega
    have hn2 : n - 2 = k + 1 := by omega
    have h46 : 4 * n - 6 = 4 * k + 6 := by omega
    rw [hn2, h46]
    nlinarith
  have hstrict :
      (48 * 100000000 * (n - 2) * (n - 3)) * (1000 * G.edgeFinset.card) <
      (48 * 100000000 * (n - 2) * (n - 3)) * (603 * (n * 2 ^ (n - 1))) := by
    calc (48 * 100000000 * (n - 2) * (n - 3)) * (1000 * G.edgeFinset.card)
        = 1000 * (48 * 100000000 * (n - 2) * (n - 3) * G.edgeFinset.card) := by ring
      _ ≤ 1000 * (1447121170 * n * (n - 2) * (n - 3) * (2 * 2 ^ (n - 1)) +
            24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2)) *
              n * (2 * 2 ^ (n - 1))) := Nat.mul_le_mul_left 1000 hsos
      _ = ((1447121170 * (n - 2) * (n - 3) +
            24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2))) * 2 * 1000) *
            (n * 2 ^ (n - 1)) := by ring
      _ < (603 * 48 * 100000000 * (n - 2) * (n - 3)) * (n * 2 ^ (n - 1)) :=
            Nat.mul_lt_mul_of_pos_right hk hposE
      _ = (48 * 100000000 * (n - 2) * (n - 3)) * (603 * (n * 2 ^ (n - 1))) := by ring
  exact Nat.lt_of_mul_lt_mul_left hstrict

/-- **Theorem (`ppl033_turan_density_limit_beats_baber`):**
The hypercube `C_4` Turán density limit `L = lim_{n → ∞} ex(Q_n, C_4) / (n * 2 ^ (n - 1))`
exists and satisfies `1 / 2 ≤ L ≤ 1447121170 / 2400000000 < 603 / 1000 < 60318 / 100000`
(improving Baber 2012's `0.60318`, pure Mathlib signature). -/
theorem ppl033_turan_density_limit_beats_baber :
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
      (1 / 2 : ℝ) ≤ L ∧ L ≤ 1447121170 / 2400000000 ∧
      L < 603 / 1000 ∧ L < 60318 / 100000 := by
  classical
  obtain ⟨L, htend, hhalf, _⟩ := PPL033.ppl033_turan_density_limit_exists
  let S (n : ℕ) : Set ℕ :=
    { m : ℕ | ∃ G : SimpleGraph (Fin n → Bool),
        G ≤ SimpleGraph.fromRel (fun u v : Fin n → Bool =>
          (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1) ∧
        (∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) ∧
        G.edgeFinset.card = m }
  have hS_ne : ∀ n : ℕ, (S n).Nonempty := fun n =>
    ⟨0, ⊥, bot_le, fun _ _ _ _ _ _ h => h.1, by simp⟩
  have hsup_le : ∀ n : ℕ, 4 ≤ n →
      48 * 100000000 * (n - 2) * (n - 3) * (sSup (S n)) ≤
        1447121170 * n * (n - 2) * (n - 3) * 2 ^ n +
        24 * (101444909 * (n - 3) + 50128370 * (4 * n - 6) + 173258785 * (n - 2)) * n * 2 ^ n := by
    intro n hn
    have hbdd : BddAbove (S n) := by
      refine ⟨(SimpleGraph.fromRel (fun u v : Fin n → Bool =>
          (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1)).edgeFinset.card, ?_⟩
      rintro _ ⟨G, hG, _, rfl⟩
      exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hG)
    obtain ⟨G, hG, hfree, hcard⟩ := Nat.sSup_mem (hS_ne n) hbdd
    rw [← hcard]
    exact ppl033_b2q4_upper_exact n hn G hG hfree
  have hL_le : L ≤ 1447121170 / 2400000000 := by
    by_contra hgt
    push Not at hgt
    set ε : ℝ := (L - 1447121170 / 2400000000) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hev1 : ∀ᶠ n in Filter.atTop,
        1447121170 / 2400000000 + ε < ((sSup (S n) : ℕ) : ℝ) / ((n * 2 ^ (n - 1) : ℕ) : ℝ) :=
      htend.eventually (lt_mem_nhds (by dsimp [ε]; linarith))
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hev1
    obtain ⟨N2, hN2⟩ := exists_nat_gt (1000 / ε)
    let m : ℕ := max N1 (max N2 4) + 1
    have hm1 : N1 ≤ m := by omega
    have hm2 : N2 ≤ m := by omega
    have hm4 : 4 ≤ m := by omega
    have hlt := hN1 m hm1
    have hsupm := hsup_le m hm4
    have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
      have he : m = (m - 1) + 1 := by omega
      conv_lhs => rw [he]
      rw [pow_succ]; ring
    rw [hpow] at hsupm
    have hposE : (0 : ℝ) < ((m * 2 ^ (m - 1) : ℕ) : ℝ) := by positivity
    have hdm : ((sSup (S m) : ℕ) : ℝ) / ((m * 2 ^ (m - 1) : ℕ) : ℝ) ≤
        1447121170 / 2400000000 + ε := by
      rw [div_le_iff₀ hposE]
      have hsosR := Nat.cast_le (α := ℝ).mpr hsupm
      have hm2R : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := Nat.cast_sub (by omega)
      have hm3R : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := Nat.cast_sub (by omega)
      have h46R : ((4 * m - 6 : ℕ) : ℝ) = 4 * (m : ℝ) - 6 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [hm2R, hm3R, h46R] at hsosR ⊢
      have hm_gt : 1000 < (m : ℝ) * ε := by
        have hN2' : 1000 / ε < (m : ℝ) := lt_of_lt_of_le hN2 (Nat.cast_le.mpr hm2)
        rwa [div_lt_iff₀ hε] at hN2'
      have hm_ge4 : (4 : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm4
      have hc : (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) * ((sSup (S m) : ℕ) : ℝ) ≤
          (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
            ((1447121170 / 2400000000 + ε) * ((m : ℝ) * (2 : ℝ) ^ (m - 1))) := by
        have hcoeff :
            ((1447121170 : ℝ) * ((m : ℝ) - 2) * ((m : ℝ) - 3) +
             24 * (101444909 * ((m : ℝ) - 3) + 50128370 * (4 * (m : ℝ) - 6) +
               173258785 * ((m : ℝ) - 2))) * 2 ≤
            (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) * (1447121170 / 2400000000 + ε) := by
          have hlin : (24 : ℝ) * (101444909 * ((m : ℝ) - 3) + 50128370 * (4 * (m : ℝ) - 6) +
              173258785 * ((m : ℝ) - 2)) * 2 ≤
              (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) * ε := by
            have hm3_ge : (m : ℝ) ≤ 4 * ((m : ℝ) - 3) := by linarith
            have hm3_ε : (250 : ℝ) < ((m : ℝ) - 3) * ε := by nlinarith
            have hstep1 : (24 : ℝ) * (101444909 * ((m : ℝ) - 3) + 50128370 * (4 * (m : ℝ) - 6) +
                173258785 * ((m : ℝ) - 2)) * 2 ≤
                (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * 250 := by nlinarith
            have hstep2 : (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * 250 ≤
                (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * (((m : ℝ) - 3) * ε) :=
              mul_le_mul_of_nonneg_left hm3_ε.le (by nlinarith)
            linarith
          nlinarith
        have hE_nonneg : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (m - 1) := by positivity
        calc (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) * ((sSup (S m) : ℕ) : ℝ)
            ≤ (1447121170 : ℝ) * (m : ℝ) * ((m : ℝ) - 2) * ((m : ℝ) - 3) * (2 * (2 : ℝ) ^ (m - 1)) +
                24 * (101444909 * ((m : ℝ) - 3) + 50128370 * (4 * (m : ℝ) - 6) +
                  173258785 * ((m : ℝ) - 2)) * (m : ℝ) * (2 * (2 : ℝ) ^ (m - 1)) := by
                rw [show (48 : ℝ) * 100000000 = 4800000000 by norm_num]; exact hsosR
          _ = ((1447121170 : ℝ) * ((m : ℝ) - 2) * ((m : ℝ) - 3) +
                24 * (101444909 * ((m : ℝ) - 3) + 50128370 * (4 * (m : ℝ) - 6) +
                  173258785 * ((m : ℝ) - 2))) * 2 * ((m : ℝ) * (2 : ℝ) ^ (m - 1)) := by ring
          _ ≤ ((48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
                (1447121170 / 2400000000 + ε)) * ((m : ℝ) * (2 : ℝ) ^ (m - 1)) :=
                mul_le_mul_of_nonneg_right hcoeff hE_nonneg
          _ = (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
                ((1447121170 / 2400000000 + ε) * ((m : ℝ) * (2 : ℝ) ^ (m - 1))) := by ring
      have hposF : (0 : ℝ) < (48 : ℝ) * 100000000 * ((m : ℝ) - 2) * ((m : ℝ) - 3) := by nlinarith
      exact le_of_mul_le_mul_left hc hposF
    linarith
  exact ⟨L, htend, hhalf, hL_le, by linarith, by linarith⟩

end HeadlineTheorems

end PPL033_B2Q4
