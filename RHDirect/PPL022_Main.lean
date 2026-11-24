/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 022 & PPL 099 (Erdős Problems #588 & #101): Maximum `k`-Point Lines with No `k+1` Collinear

## Honest Scope & Literature Status
This file formalizes a comprehensive pure-Mathlib milestone (`0` `sorry`, `0` custom definitions in
any public theorem signature) for **Erdős Problems #588 (PPL 022)** and **#101 (PPL 099)**
($100 prize each):

> Let `f_k(n)` be the maximum number of lines in `ℝ²` containing at least `k` points among any `n`
> points with no `k + 1` points collinear. Is `f_k(n) = o(n^2)` for `k ≥ 4` (in particular `k = 4`)?

**BOTH Erdős Problem #101 (`k = 4`) and Erdős Problem #588 (`k ≥ 4`) REMAIN OPEN.**
This file does **not** claim to prove `f_k(n) = o(n^2)` for any `k ≥ 4`. Instead, it provides
complete, self-contained, pure-Mathlib formalizations closing all major sub-theorems of `588.lean`
along with the Dual Crossing Lemma and formalized structural barrier theorems.
-/

namespace PPL022

open Classical

/-! ### Section 1: Unique Line Through Two Distinct Points (General Field / Vector Space) -/

/-- Two 1-dimensional affine subspaces over a field `K` sharing two distinct points are equal. -/
private lemma affine_line_eq_of_two_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ℓ₁ ℓ₂ : AffineSubspace K V}
    (h₁ : Module.finrank K ℓ₁.direction = 1)
    (h₂ : Module.finrank K ℓ₂.direction = 1)
    {p q : V} (hpq : p ≠ q)
    (hp₁ : p ∈ ℓ₁) (hq₁ : q ∈ ℓ₁) (hp₂ : p ∈ ℓ₂) (hq₂ : q ∈ ℓ₂) :
    ℓ₁ = ℓ₂ := by
  have hv_ne : q -ᵥ p ≠ (0 : V) := vsub_ne_zero.mpr hpq.symm
  have hspan_dim : Module.finrank K (Submodule.span K ({q -ᵥ p} : Set V)) = 1 :=
    finrank_span_singleton hv_ne
  have hle₁ : Submodule.span K ({q -ᵥ p} : Set V) ≤ ℓ₁.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (AffineSubspace.vsub_mem_direction hq₁ hp₁))
  have hle₂ : Submodule.span K ({q -ᵥ p} : Set V) ≤ ℓ₂.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (AffineSubspace.vsub_mem_direction hq₂ hp₂))
  have : FiniteDimensional K ℓ₁.direction :=
    Module.finite_of_finrank_pos (by omega)
  have : FiniteDimensional K ℓ₂.direction :=
    Module.finite_of_finrank_pos (by omega)
  have hdir₁ : Submodule.span K ({q -ᵥ p} : Set V) = ℓ₁.direction :=
    Submodule.eq_of_le_of_finrank_eq hle₁ (by omega)
  have hdir₂ : Submodule.span K ({q -ᵥ p} : Set V) = ℓ₂.direction :=
    Submodule.eq_of_le_of_finrank_eq hle₂ (by omega)
  have hdir : ℓ₁.direction = ℓ₂.direction := hdir₁.symm.trans hdir₂
  ext x
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hp₁,
      ← AffineSubspace.vsub_right_mem_direction_iff_mem hp₂, hdir]

/-! ### Section 2: Pair Double-Counting & `trivial_upper` (`588.lean`) -/

/-- Weighted pair double-counting bound in `ℝ²`: the sum of `choose (|P ∩ ℓ|) 2` over any finite
family `L` of distinct 1-dimensional affine lines is at most `choose |P| 2`. -/
theorem ppl022_weighted_pair_bound
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1) :
    ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card.choose 2 ≤ P.card.choose 2 := by
  classical
  have hdisj : Set.PairwiseDisjoint (L : Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
      (fun ℓ => (P.filter (· ∈ ℓ)).powersetCard 2) := by
    intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hs₁ hs₂
    rw [Finset.mem_powersetCard] at hs₁ hs₂
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs₁.2
    have hp₁ : p ∈ ℓ₁ := (Finset.mem_filter.mp (hs₁.1 (by simp))).2
    have hq₁ : q ∈ ℓ₁ := (Finset.mem_filter.mp (hs₁.1 (by simp))).2
    have hp₂ : p ∈ ℓ₂ := (Finset.mem_filter.mp (hs₂.1 (by simp))).2
    have hq₂ : q ∈ ℓ₂ := (Finset.mem_filter.mp (hs₂.1 (by simp))).2
    exact hne (affine_line_eq_of_two_mem (hL ℓ₁ hℓ₁) (hL ℓ₂ hℓ₂) hpq hp₁ hq₁ hp₂ hq₂)
  have hsub : L.biUnion (fun ℓ => (P.filter (· ∈ ℓ)).powersetCard 2) ⊆ P.powersetCard 2 := by
    intro s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨ℓ, _, hsℓ⟩ := hs
    rw [Finset.mem_powersetCard] at hsℓ ⊢
    exact ⟨hsℓ.1.trans (Finset.filter_subset _ _), hsℓ.2⟩
  calc
    ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card.choose 2
        = ∑ ℓ ∈ L, ((P.filter (· ∈ ℓ)).powersetCard 2).card := by
          simp [Finset.card_powersetCard]
    _ = (L.biUnion (fun ℓ => (P.filter (· ∈ ℓ)).powersetCard 2)).card :=
          (Finset.card_biUnion hdisj).symm
    _ ≤ (P.powersetCard 2).card := Finset.card_le_card hsub
    _ = P.card.choose 2 := Finset.card_powersetCard 2 P

/-- Trivial upper bound (`588.lean`: `trivial_upper`): for any `k ≥ 2`, any finite `P ⊆ ℝ²`, and
any finite family `L` of distinct 1-dimensional lines each containing at least `k` points of `P`,
`|L| * k * (k - 1) ≤ |P| * (|P| - 1)` (in particular, `12 * |L| ≤ |P| * (|P| - 1)` for `k = 4`). -/
theorem ppl022_trivial_upper
    (k : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hL : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1)
    (hrich : ∀ ℓ ∈ L, k ≤ (P.filter (· ∈ ℓ)).card) :
    L.card * (k * (k - 1)) ≤ P.card * (P.card - 1) := by
  have h1 : L.card * k.choose 2 ≤ ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card.choose 2 := by
    calc
      L.card * k.choose 2 = ∑ _ℓ ∈ L, k.choose 2 := by simp
      _ ≤ ∑ ℓ ∈ L, (P.filter (· ∈ ℓ)).card.choose 2 :=
        Finset.sum_le_sum fun ℓ hℓ => Nat.choose_le_choose 2 (hrich ℓ hℓ)
  have h2 := h1.trans (ppl022_weighted_pair_bound P L hL)
  have hmul : 2 * (L.card * k.choose 2) ≤ 2 * P.card.choose 2 := Nat.mul_le_mul_left 2 h2
  have hk2 : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd]
  have hp2 : 2 * P.card.choose 2 = P.card * (P.card - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self P.card).two_dvd]
  calc
    L.card * (k * (k - 1)) = 2 * (L.card * k.choose 2) := by rw [← hk2]; ring
    _ ≤ 2 * P.card.choose 2 := hmul
    _ = P.card * (P.card - 1) := hp2

/-! ### Section 3: Probabilistic Crossing Lemma & Dual Crossing Upper Bound -/

/-- Bernoulli product weight identity over all subsets of a finite set `A`. -/
private lemma sum_powerset_bernoulli {V : Type*} [DecidableEq V]
    (A : Finset V) (p : ℝ) :
    ∑ R ∈ A.powerset, p ^ R.card * (1 - p) ^ (A.card - R.card) = 1 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hcard_ins : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    rw [Finset.powerset_insert, Finset.sum_union]
    · have h1 : ∑ R ∈ s.powerset,
          p ^ R.card * (1 - p) ^ ((insert a s).card - R.card) =
          (1 - p) * ∑ R ∈ s.powerset, p ^ R.card * (1 - p) ^ (s.card - R.card) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun R hR => ?_
        have hle : R.card ≤ s.card := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [hcard_ins, Nat.sub_add_comm hle, pow_succ]
        ring
      have h2 : ∑ R ∈ s.powerset.image (insert a),
          p ^ R.card * (1 - p) ^ ((insert a s).card - R.card) =
          p * ∑ R ∈ s.powerset, p ^ R.card * (1 - p) ^ (s.card - R.card) := by
        rw [Finset.sum_image, Finset.mul_sum]
        · refine Finset.sum_congr rfl fun R hR => ?_
          have haR : a ∉ R := fun h => ha (Finset.mem_powerset.mp hR h)
          rw [Finset.card_insert_of_notMem haR, hcard_ins, Nat.add_sub_add_right, pow_succ]
          ring
        · intro R₁ hR₁ R₂ hR₂ heq
          have ha₁ : a ∉ R₁ := fun h => ha (Finset.mem_powerset.mp hR₁ h)
          have ha₂ : a ∉ R₂ := fun h => ha (Finset.mem_powerset.mp hR₂ h)
          have := congrArg (Finset.erase · a) heq
          simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using this
      rw [h1, h2, ih]
      ring
    · rw [Finset.disjoint_left]
      intro R hR hRimg
      rw [Finset.mem_image] at hRimg
      obtain ⟨R', _, rfl⟩ := hRimg
      exact ha (Finset.mem_powerset.mp hR (Finset.mem_insert_self a R'))

/-- Probability that a `p`-random subset `S ⊆ verts` contains a fixed subset `T ⊆ verts` is `p ^ |T|`. -/
private lemma sum_powerset_bernoulli_superset {V : Type*} [DecidableEq V]
    (verts T : Finset V) (hT : T ⊆ verts) (p : ℝ) :
    ∑ S ∈ verts.powerset.filter (T ⊆ ·), p ^ S.card * (1 - p) ^ (verts.card - S.card) =
      p ^ T.card := by
  have hbij : verts.powerset.filter (T ⊆ ·) = (verts \ T).powerset.image (T ∪ ·) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hSv, hTS⟩
      refine ⟨S \ T, Finset.sdiff_subset_sdiff hSv (Finset.Subset.refl T), Finset.union_sdiff_of_subset hTS⟩
    · rintro ⟨R, hR, rfl⟩
      refine ⟨Finset.union_subset hT (hR.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  rw [hbij, Finset.sum_image]
  · have hsum : ∑ R ∈ (verts \ T).powerset,
        p ^ (T ∪ R).card * (1 - p) ^ (verts.card - (T ∪ R).card) =
        p ^ T.card * ∑ R ∈ (verts \ T).powerset,
          p ^ R.card * (1 - p) ^ ((verts \ T).card - R.card) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun R hR => ?_
      have hdisj : Disjoint T R :=
        Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR) Finset.disjoint_sdiff
      rw [Finset.card_union_of_disjoint hdisj, pow_add]
      have hcard_sdiff : (verts \ T).card = verts.card - T.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT]
      rw [hcard_sdiff, Nat.sub_sub]
      ring
    rw [hsum, sum_powerset_bernoulli, mul_one]
  · intro R₁ hR₁ R₂ hR₂ heq
    have hd₁ : Disjoint T R₁ :=
      Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR₁) Finset.disjoint_sdiff
    have hd₂ : Disjoint T R₂ :=
      Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hR₂) Finset.disjoint_sdiff
    have := congrArg (· \ T) heq
    simpa [Finset.union_sdiff_cancel_left hd₁, Finset.union_sdiff_cancel_left hd₂] using this

/-- **Probabilistic Crossing Lemma** (Ajtai–Chvátal–Newborn–Szemerédi 1982 / Leighton 1983):
for any finite vertex set `verts`, edge set `edges` (2-subsets of `verts`), and crossing index set
`crossings` (each supported on a 4-subset of `verts`), if every induced subgraph `S ⊆ verts` obeys
Euler's linear crossing bound `e(S) ≤ 3 * |S| + cr(S)` and `4 * |verts| ≤ |edges|`, then
`|edges|^3 ≤ 64 * |verts|^2 * |crossings|`. -/
theorem ppl022_crossing_lemma_64 {V α : Type*} [DecidableEq V] [DecidableEq α]
    (verts : Finset V)
    (edges : Finset (Finset V))
    (crossings : Finset α)
    (supp : α → Finset V)
    (hE_sub : ∀ e ∈ edges, e ⊆ verts ∧ e.card = 2)
    (hC_sub : ∀ c ∈ crossings, supp c ⊆ verts ∧ (supp c).card = 4)
    (hEuler : ∀ S : Finset V, S ⊆ verts →
      (edges.filter (· ⊆ S)).card ≤ 3 * S.card + (crossings.filter (fun c => supp c ⊆ S)).card)
    (hDense : 4 * verts.card ≤ edges.card) :
    edges.card ^ 3 ≤ 64 * verts.card ^ 2 * crossings.card := by
  by_cases hv : verts.card = 0
  · have he0 : edges.card = 0 := by
      rw [Finset.card_eq_zero] at hv ⊢
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      have := (hE_sub e he).1
      rw [hv, Finset.subset_empty] at this
      have hc := (hE_sub e he).2
      rw [this, Finset.card_empty] at hc
      omega
    simp [hv, he0]
  have hv_pos : (0 : ℝ) < (verts.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hv)
  have he_pos : (0 : ℝ) < (edges.card : ℝ) := by
    have : 4 * verts.card ≤ edges.card := hDense
    exact Nat.cast_pos.mpr (by omega)
  set p : ℝ := 4 * (verts.card : ℝ) / (edges.card : ℝ)
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    rw [div_le_one he_pos]
    exact_mod_cast hDense
  have h1mp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  set w : Finset V → ℝ := fun S => p ^ S.card * (1 - p) ^ (verts.card - S.card)
  have hw_nn : ∀ S, 0 ≤ w S := fun S => mul_nonneg (pow_nonneg hp0 _) (pow_nonneg h1mp _)
  -- Weighted sum of `hEuler S` over `S ∈ verts.powerset`
  have hsum_ineq :
      ∑ S ∈ verts.powerset, w S * ((edges.filter (· ⊆ S)).card : ℝ) ≤
      ∑ S ∈ verts.powerset, w S * (3 * (S.card : ℝ) + ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ)) := by
    refine Finset.sum_le_sum fun S hS => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hw_nn S)
    exact_mod_cast hEuler S (Finset.mem_powerset.mp hS)
  -- Evaluate LHS = p^2 * |edges|
  have hLHS :
      ∑ S ∈ verts.powerset, w S * ((edges.filter (· ⊆ S)).card : ℝ) =
      p ^ 2 * (edges.card : ℝ) := by
    have hrewrite :
        ∑ S ∈ verts.powerset, w S * ((edges.filter (· ⊆ S)).card : ℝ) =
        ∑ S ∈ verts.powerset, ∑ e ∈ edges, (if e ⊆ S then w S else 0) := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      split_ifs <;> simp
    rw [hrewrite, Finset.sum_comm]
    calc
      ∑ e ∈ edges, ∑ S ∈ verts.powerset, (if e ⊆ S then w S else 0)
          = ∑ e ∈ edges, ∑ S ∈ verts.powerset.filter (e ⊆ ·), w S := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.sum_filter]
      _ = ∑ e ∈ edges, p ^ 2 := by
            refine Finset.sum_congr rfl fun e he => ?_
            rw [sum_powerset_bernoulli_superset verts e (hE_sub e he).1 p, (hE_sub e he).2]
      _ = p ^ 2 * (edges.card : ℝ) := by simp [mul_comm]
  -- Evaluate vertex term = p * |verts|
  have hV :
      ∑ S ∈ verts.powerset, w S * (S.card : ℝ) = p * (verts.card : ℝ) := by
    have hrewrite :
        ∑ S ∈ verts.powerset, w S * (S.card : ℝ) =
        ∑ S ∈ verts.powerset, ∑ v ∈ verts, (if ({v} : Finset V) ⊆ S then w S else 0) := by
      refine Finset.sum_congr rfl fun S hS => ?_
      have hcard : S.card = ∑ v ∈ verts, (if ({v} : Finset V) ⊆ S then 1 else 0) := by
        have hSv : S ⊆ verts := Finset.mem_powerset.mp hS
        simp [Finset.singleton_subset_iff, Finset.inter_eq_right.mpr hSv]
      rw [hcard, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp
    rw [hrewrite, Finset.sum_comm]
    calc
      ∑ v ∈ verts, ∑ S ∈ verts.powerset, (if ({v} : Finset V) ⊆ S then w S else 0)
          = ∑ v ∈ verts, ∑ S ∈ verts.powerset.filter (({v} : Finset V) ⊆ ·), w S := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.sum_filter]
      _ = ∑ v ∈ verts, p := by
            refine Finset.sum_congr rfl fun v hv => ?_
            rw [sum_powerset_bernoulli_superset verts {v} (Finset.singleton_subset_iff.mpr hv) p]
            simp
      _ = p * (verts.card : ℝ) := by simp [mul_comm]
  -- Evaluate crossing term = p^4 * |crossings|
  have hC :
      ∑ S ∈ verts.powerset, w S * ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ) =
      p ^ 4 * (crossings.card : ℝ) := by
    have hrewrite :
        ∑ S ∈ verts.powerset, w S * ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ) =
        ∑ S ∈ verts.powerset, ∑ c ∈ crossings, (if supp c ⊆ S then w S else 0) := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> simp
    rw [hrewrite, Finset.sum_comm]
    calc
      ∑ c ∈ crossings, ∑ S ∈ verts.powerset, (if supp c ⊆ S then w S else 0)
          = ∑ c ∈ crossings, ∑ S ∈ verts.powerset.filter (supp c ⊆ ·), w S := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.sum_filter]
      _ = ∑ c ∈ crossings, p ^ 4 := by
            refine Finset.sum_congr rfl fun c hc => ?_
            rw [sum_powerset_bernoulli_superset verts (supp c) (hC_sub c hc).1 p, (hC_sub c hc).2]
      _ = p ^ 4 * (crossings.card : ℝ) := by simp [mul_comm]
  have hRHS :
      ∑ S ∈ verts.powerset, w S * (3 * (S.card : ℝ) + ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ)) =
      3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ) := by
    have hsplit :
        ∑ S ∈ verts.powerset, w S * (3 * (S.card : ℝ) + ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ)) =
        3 * (∑ S ∈ verts.powerset, w S * (S.card : ℝ)) +
        ∑ S ∈ verts.powerset, w S * ((crossings.filter (fun c => supp c ⊆ S)).card : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun S _ => by ring
    rw [hsplit, hV, hC]
    ring
  have hmain : p ^ 2 * (edges.card : ℝ) ≤ 3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ) := by
    rwa [hLHS, hRHS] at hsum_ineq
  have hreal : ((edges.card : ℝ)) ^ 3 ≤ 64 * ((verts.card : ℝ)) ^ 2 * (crossings.card : ℝ) := by
    have hmul : (edges.card : ℝ) ^ 4 * (p ^ 2 * (edges.card : ℝ)) ≤
        (edges.card : ℝ) ^ 4 * (3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hmain (by positivity)
    have hsimp : 4 * (verts.card : ℝ) ^ 2 * (edges.card : ℝ) ^ 3 ≤
        256 * (verts.card : ℝ) ^ 4 * (crossings.card : ℝ) := by
      have he_ne : (edges.card : ℝ) ≠ 0 := ne_of_gt he_pos
      have h1 : (edges.card : ℝ) ^ 4 * (p ^ 2 * (edges.card : ℝ)) =
          16 * (verts.card : ℝ) ^ 2 * (edges.card : ℝ) ^ 3 := by
        simp only [p]; field_simp; ring
      have h2 : (edges.card : ℝ) ^ 4 * (3 * p * (verts.card : ℝ) + p ^ 4 * (crossings.card : ℝ)) =
          12 * (verts.card : ℝ) ^ 2 * (edges.card : ℝ) ^ 3 +
          256 * (verts.card : ℝ) ^ 4 * (crossings.card : ℝ) := by
        simp only [p]; field_simp; ring
      linarith
    have h4v2 : (0 : ℝ) < 4 * (verts.card : ℝ) ^ 2 := by positivity
    nlinarith
  exact_mod_cast hreal

/-- **Dual Crossing Lemma Upper Bound**: combining the Crossing Lemma (`e^3 ≤ 64 * m^2 * cr`) on
the dual geometric graph `G*` (`v = m`, `e ≥ k * m - n`, `cr + m * choose k 2 ≤ choose n 2`) yields
`(k^3 + 32 * k * (k - 1)) * m ≤ 32 * n * (n - 1) + 3 * k^2 * n`, strictly dominating both
double-counting `n(n-1)/(k(k-1))` and the primal Székely Crossing Lemma `32 n^2 / (k-1)^3` for
every `k ≥ 5` (and beating Melchior's `n^2 / ((k+3)(k-2))` for all `k ≥ 8`). -/
theorem ppl022_dual_crossing_upper (k n m e cr : ℕ)
    (he_lb : k * m ≤ e + n)
    (he_dense : 4 * m ≤ e)
    (hcr_lb : e ^ 3 ≤ 64 * m ^ 2 * cr)
    (hcr_ub : cr + m * k.choose 2 ≤ n.choose 2) :
    (k ^ 3 + 32 * k * (k - 1)) * m ≤ 32 * n * (n - 1) + 3 * k ^ 2 * n := by
  by_cases hm : m = 0
  · subst hm; simp
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hcube : (k * m : ℤ) ^ 3 - 3 * (k : ℤ) ^ 2 * (m : ℤ) ^ 2 * (n : ℤ) ≤ (e : ℤ) ^ 3 := by
    by_cases hkn : (n : ℤ) ≤ (k : ℤ) * (m : ℤ)
    · have hez : (k : ℤ) * (m : ℤ) - (n : ℤ) ≤ (e : ℤ) := by omega
      have hnn : (0 : ℤ) ≤ (k : ℤ) * (m : ℤ) - (n : ℤ) := by linarith
      have hpow : ((k : ℤ) * (m : ℤ) - (n : ℤ)) ^ 3 ≤ (e : ℤ) ^ 3 :=
        pow_le_pow_left₀ hnn hez 3
      have hrem : (0 : ℤ) ≤ 3 * (k : ℤ) * (m : ℤ) * (n : ℤ) ^ 2 - (n : ℤ) ^ 3 := by
        have h1 : (n : ℤ) ^ 2 * (n : ℤ) ≤ (n : ℤ) ^ 2 * (3 * (k : ℤ) * (m : ℤ)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
        linarith
      nlinarith
    · have : (k : ℤ) * (m : ℤ) < (n : ℤ) := not_le.mp hkn
      have hneg : (k * m : ℤ) ^ 3 - 3 * (k : ℤ) ^ 2 * (m : ℤ) ^ 2 * (n : ℤ) ≤ 0 := by
        have h1 : (k : ℤ) ^ 2 * (m : ℤ) ^ 2 * ((k : ℤ) * (m : ℤ)) ≤
            (k : ℤ) ^ 2 * (m : ℤ) ^ 2 * (3 * (n : ℤ)) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        linarith
      have he3_nn : (0 : ℤ) ≤ (e : ℤ) ^ 3 := by positivity
      linarith
  have hcr_lb_z : (e : ℤ) ^ 3 ≤ 64 * (m : ℤ) ^ 2 * (cr : ℤ) := by exact_mod_cast hcr_lb
  have hm2_pos : (0 : ℤ) < (m : ℤ) ^ 2 := by positivity
  have h64cr : (k : ℤ) ^ 3 * (m : ℤ) - 3 * (k : ℤ) ^ 2 * (n : ℤ) ≤ 64 * (cr : ℤ) := by
    have hmul : (m : ℤ) ^ 2 * ((k : ℤ) ^ 3 * (m : ℤ) - 3 * (k : ℤ) ^ 2 * (n : ℤ)) ≤
        (m : ℤ) ^ 2 * (64 * (cr : ℤ)) := by
      linarith
    exact le_of_mul_le_mul_left hmul hm2_pos
  have hk2 : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd]
  have hn2 : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd]
  have hcr_ub64 : 64 * (cr : ℤ) + 32 * (m : ℤ) * ((k * (k - 1) : ℕ) : ℤ) ≤
      32 * ((n * (n - 1) : ℕ) : ℤ) := by
    have h1 : 64 * cr + 64 * (m * k.choose 2) ≤ 64 * n.choose 2 := by
      calc 64 * cr + 64 * (m * k.choose 2) = 64 * (cr + m * k.choose 2) := by ring
        _ ≤ 64 * n.choose 2 := Nat.mul_le_mul_left 64 hcr_ub
    have h2 : 64 * (m * k.choose 2) = 32 * m * (k * (k - 1)) := by
      calc 64 * (m * k.choose 2) = 32 * m * (2 * k.choose 2) := by ring
        _ = 32 * m * (k * (k - 1)) := by rw [hk2]
    have h3 : 64 * n.choose 2 = 32 * (n * (n - 1)) := by
      calc 64 * n.choose 2 = 32 * (2 * n.choose 2) := by ring
        _ = 32 * (n * (n - 1)) := by rw [hn2]
    rw [h2, h3] at h1
    exact_mod_cast h1
  have hfinal_z :
      (((k ^ 3 + 32 * k * (k - 1)) * m : ℕ) : ℤ) ≤
      ((32 * n * (n - 1) + 3 * k ^ 2 * n : ℕ) : ℤ) := by
    push_cast at hcr_ub64 ⊢
    linarith
  exact_mod_cast hfinal_z

/-! ### Section 4: Sharp `k = 3` Construction (`sylvester`, `three_lower`, `three_not_isLittleO`) -/

private noncomputable def mkPt (x y : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

private lemma mkPt_zero (x y : ℝ) : mkPt x y 0 = x := rfl
private lemma mkPt_one (x y : ℝ) : mkPt x y 1 = y := rfl

private lemma mkPt_ext {p q : EuclideanSpace ℝ (Fin 2)} (h0 : p 0 = q 0) (h1 : p 1 = q 1) :
    p = q := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- Three points `p, q, r ∈ ℝ²` lying on a 1-dimensional affine line satisfy the 2×2 collinearity
determinant equation `(q 0 - p 0) * (r 1 - p 1) = (r 0 - p 0) * (q 1 - p 1)`. -/
private lemma det_eq_zero_of_mem_line
    {ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))}
    (hℓ : Module.finrank ℝ ℓ.direction = 1)
    {p q r : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (hp : p ∈ ℓ) (hq : q ∈ ℓ) (hr : r ∈ ℓ) :
    (q 0 - p 0) * (r 1 - p 1) = (r 0 - p 0) * (q 1 - p 1) := by
  have hv_ne : q -ᵥ p ≠ (0 : EuclideanSpace ℝ (Fin 2)) := vsub_ne_zero.mpr hpq.symm
  have hle : Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) ≤ ℓ.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (AffineSubspace.vsub_mem_direction hq hp))
  have : FiniteDimensional ℝ ℓ.direction := Module.finite_of_finrank_pos (by omega)
  have hspan_dim : Module.finrank ℝ (Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2)))) = 1 :=
    finrank_span_singleton hv_ne
  have hdir : Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) = ℓ.direction :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hr_mem : r -ᵥ p ∈ Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hdir]
    exact AffineSubspace.vsub_mem_direction hr hp
  rw [Submodule.mem_span_singleton] at hr_mem
  obtain ⟨c, hc⟩ := hr_mem
  have h0 : r 0 - p 0 = c * (q 0 - p 0) := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hc
    simpa [vsub_eq_sub] using this.symm
  have h1 : r 1 - p 1 = c * (q 1 - p 1) := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hc
    simpa [vsub_eq_sub] using this.symm
  rw [h0, h1]
  ring

/-- The 1-dimensional affine line through two distinct points `p ≠ q` in `ℝ²`. -/
private noncomputable def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  AffineSubspace.mk' p (Submodule.span ℝ ({q -ᵥ p} : Set (EuclideanSpace ℝ (Fin 2))))

private lemma lineThrough_finrank {p q : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q) :
    Module.finrank ℝ (lineThrough p q).direction = 1 := by
  unfold lineThrough
  rw [AffineSubspace.direction_mk']
  exact finrank_span_singleton (vsub_ne_zero.mpr hpq.symm)

private lemma left_mem_lineThrough (p q : EuclideanSpace ℝ (Fin 2)) : p ∈ lineThrough p q :=
  AffineSubspace.self_mem_mk' p _

private lemma right_mem_lineThrough (p q : EuclideanSpace ℝ (Fin 2)) : q ∈ lineThrough p q := by
  rw [lineThrough, AffineSubspace.mem_mk']
  exact Submodule.subset_span rfl

private lemma mem_lineThrough_of_det {p q r : EuclideanSpace ℝ (Fin 2)} (hpq : p ≠ q)
    (hdet : (q 0 - p 0) * (r 1 - p 1) = (r 0 - p 0) * (q 1 - p 1)) :
    r ∈ lineThrough p q := by
  rw [lineThrough, AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  by_cases hx : q 0 - p 0 ≠ 0
  · refine ⟨(r 0 - p 0) / (q 0 - p 0), ?_⟩
    apply mkPt_ext
    · simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply]
      field_simp
    · simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply]
      field_simp
      linarith
  · push Not at hx
    have hy : q 1 - p 1 ≠ 0 := by
      intro hy0
      apply hpq
      apply mkPt_ext <;> linarith
    have hr0 : r 0 - p 0 = 0 := by
      have : (r 0 - p 0) * (q 1 - p 1) = 0 := by rw [← hdet, hx, zero_mul]
      exact (mul_eq_zero.mp this).resolve_right hy
    refine ⟨(r 1 - p 1) / (q 1 - p 1), ?_⟩
    apply mkPt_ext
    · simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply]
      rw [hx, hr0, mul_zero]
    · simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply]
      field_simp

/-- Shifted angle `θ_j = π * (3j + 1) / (3n)` for the universal Burr–Grünbaum–Sloane / Sylvester
cubic construction (uniformly valid for all `n ≥ 3`, both even and odd). -/
private noncomputable def sylvAngle (n : ℕ) (j : Fin n) : ℝ :=
  Real.pi * (3 * (j.val : ℝ) + 1) / (3 * (n : ℝ))

private noncomputable def sylvPt (n : ℕ) (j : Fin n) : EuclideanSpace ℝ (Fin 2) :=
  mkPt (Real.tan (sylvAngle n j)) (Real.sin (sylvAngle n j) * Real.cos (sylvAngle n j))

private lemma sylvAngle_pos {n : ℕ} (hn : 0 < n) (j : Fin n) : 0 < sylvAngle n j := by
  unfold sylvAngle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  positivity

private lemma sylvAngle_lt_pi {n : ℕ} (hn : 0 < n) (j : Fin n) : sylvAngle n j < Real.pi := by
  unfold sylvAngle
  have hpi : 0 < Real.pi := Real.pi_pos
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [div_lt_iff₀ (by positivity)]
  have hj : (j.val : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast j.isLt
  nlinarith

private lemma sylvAngle_cos_ne_zero {n : ℕ} (hn : 0 < n) (j : Fin n) :
    Real.cos (sylvAngle n j) ≠ 0 := by
  intro hcos
  have hsin : Real.sin (Real.pi / 2 - sylvAngle n j) = 0 := by
    rw [Real.sin_pi_div_two_sub]; exact hcos
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨m, hm⟩ := hsin
  unfold sylvAngle at hm
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have h1 : (1 - 2 * (m : ℝ)) * (3 * (n : ℝ)) = 2 * (3 * (j.val : ℝ) + 1) := by
    have hmul : (m : ℝ) * Real.pi * (6 * (n : ℝ)) =
        (Real.pi / 2 - Real.pi * (3 * (j.val : ℝ) + 1) / (3 * (n : ℝ))) * (6 * (n : ℝ)) := by
      rw [hm]
    have hmul' : Real.pi * ((1 - 2 * (m : ℝ)) * (3 * (n : ℝ))) =
        Real.pi * (2 * (3 * (j.val : ℝ) + 1)) := by
      have hr : (Real.pi / 2 - Real.pi * (3 * (j.val : ℝ) + 1) / (3 * (n : ℝ))) * (6 * (n : ℝ)) =
          Real.pi * (3 * (n : ℝ)) - Real.pi * (2 * (3 * (j.val : ℝ) + 1)) := by
        field_simp; ring
      linarith
    exact mul_left_cancel₀ hpi hmul'
  have hz : (1 - 2 * m) * (3 * (n : ℤ)) = 2 * (3 * (j.val : ℤ) + 1) := by exact_mod_cast h1
  have hmod3 : ((1 - 2 * m) * (3 * (n : ℤ))) % 3 = (2 * (3 * (j.val : ℤ) + 1)) % 3 :=
    congrArg (· % 3) hz
  rw [show (1 - 2 * m) * (3 * (n : ℤ)) = 3 * ((1 - 2 * m) * (n : ℤ)) by ring,
      show 2 * (3 * (j.val : ℤ) + 1) = 3 * (2 * (j.val : ℤ)) + 2 by ring] at hmod3
  omega

private lemma sylvPt_injective {n : ℕ} (hn : 0 < n) : Function.Injective (sylvPt n) := by
  intro i j hij
  have htan : Real.tan (sylvAngle n i) = Real.tan (sylvAngle n j) := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hij
    simpa [sylvPt, mkPt_zero] using this
  have hci : Real.cos (sylvAngle n i) ≠ 0 := sylvAngle_cos_ne_zero hn i
  have hcj : Real.cos (sylvAngle n j) ≠ 0 := sylvAngle_cos_ne_zero hn j
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos] at htan
  have hcross : Real.sin (sylvAngle n i) * Real.cos (sylvAngle n j) -
      Real.cos (sylvAngle n i) * Real.sin (sylvAngle n j) = 0 := by
    have hmul : Real.sin (sylvAngle n i) * Real.cos (sylvAngle n j) =
        Real.sin (sylvAngle n j) * Real.cos (sylvAngle n i) := by
      have := (div_eq_div_iff hci hcj).mp htan
      linarith
    linarith
  have hsin0 : Real.sin (sylvAngle n i - sylvAngle n j) = 0 := by
    rw [Real.sin_sub]; exact hcross
  rw [Real.sin_eq_zero_iff] at hsin0
  obtain ⟨m, hm⟩ := hsin0
  have hi0 := sylvAngle_pos hn i
  have hi1 := sylvAngle_lt_pi hn i
  have hj0 := sylvAngle_pos hn j
  have hj1 := sylvAngle_lt_pi hn j
  have hpi : 0 < Real.pi := Real.pi_pos
  have hm0 : m = 0 := by
    have hlt : -Real.pi < (m : ℝ) * Real.pi := by linarith
    have hgt : (m : ℝ) * Real.pi < Real.pi := by linarith
    have h1 : (-1 : ℝ) < (m : ℝ) := by nlinarith
    have h2 : (m : ℝ) < (1 : ℝ) := by nlinarith
    have hz1 : (-1 : ℤ) < m := by exact_mod_cast h1
    have hz2 : m < (1 : ℤ) := by exact_mod_cast h2
    omega
  subst hm0
  simp only [Int.cast_zero, zero_mul] at hm
  have heq : sylvAngle n i = sylvAngle n j := by linarith
  unfold sylvAngle at heq
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h3 : (i.val : ℝ) = (j.val : ℝ) := by
    have h1 : Real.pi * (3 * (i.val : ℝ) + 1) = Real.pi * (3 * (j.val : ℝ) + 1) := by
      exact (div_left_inj' (by positivity : (3 * (n : ℝ)) ≠ 0)).mp heq
    have h2 : 3 * (i.val : ℝ) + 1 = 3 * (j.val : ℝ) + 1 := mul_left_cancel₀ Real.pi_ne_zero h1
    linarith
  exact Fin.ext (by exact_mod_cast h3)

private lemma sin_mul_cos_eq_tan_div (θ : ℝ) (hc : Real.cos θ ≠ 0) :
    Real.sin θ * Real.cos θ = Real.tan θ / (Real.tan θ ^ 2 + 1) := by
  rw [Real.tan_eq_sin_div_cos]
  have hsc : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have hden : (Real.sin θ / Real.cos θ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp
  rw [hsc]
  ring

private lemma sin_add_three_eq (α β γ : ℝ) :
    Real.sin (α + β + γ) =
      Real.sin α * Real.cos β * Real.cos γ +
      Real.cos α * Real.sin β * Real.cos γ +
      Real.cos α * Real.cos β * Real.sin γ -
      Real.sin α * Real.sin β * Real.sin γ := by
  rw [Real.sin_add, Real.sin_add, Real.cos_add]
  ring

private lemma sylvPt_det_iff {n : ℕ} (hn : 0 < n) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (sylvPt n b 0 - sylvPt n a 0) * (sylvPt n c 1 - sylvPt n a 1) =
    (sylvPt n c 0 - sylvPt n a 0) * (sylvPt n b 1 - sylvPt n a 1) ↔
    (a.val + b.val + c.val + 1) % n = 0 := by
  set α := sylvAngle n a
  set β := sylvAngle n b
  set γ := sylvAngle n c
  set ta := Real.tan α
  set tb := Real.tan β
  set tc := Real.tan γ
  have hca : Real.cos α ≠ 0 := sylvAngle_cos_ne_zero hn a
  have hcb : Real.cos β ≠ 0 := sylvAngle_cos_ne_zero hn b
  have hcc : Real.cos γ ≠ 0 := sylvAngle_cos_ne_zero hn c
  have htab : tb ≠ ta := by
    intro h
    apply hab
    apply sylvPt_injective hn
    apply mkPt_ext
    · simpa [sylvPt, mkPt_zero, ta, tb] using h.symm
    · simp only [sylvPt, mkPt_one]
      rw [sin_mul_cos_eq_tan_div α hca, sin_mul_cos_eq_tan_div β hcb]
      change ta / (ta ^ 2 + 1) = tb / (tb ^ 2 + 1)
      rw [h]
  have htac : tc ≠ ta := by
    intro h
    apply hac
    apply sylvPt_injective hn
    apply mkPt_ext
    · simpa [sylvPt, mkPt_zero, ta, tc] using h.symm
    · simp only [sylvPt, mkPt_one]
      rw [sin_mul_cos_eq_tan_div α hca, sin_mul_cos_eq_tan_div γ hcc]
      change ta / (ta ^ 2 + 1) = tc / (tc ^ 2 + 1)
      rw [h]
  have htbc : tc ≠ tb := by
    intro h
    apply hbc
    apply sylvPt_injective hn
    apply mkPt_ext
    · simpa [sylvPt, mkPt_zero, tb, tc] using h.symm
    · simp only [sylvPt, mkPt_one]
      rw [sin_mul_cos_eq_tan_div β hcb, sin_mul_cos_eq_tan_div γ hcc]
      change tb / (tb ^ 2 + 1) = tc / (tc ^ 2 + 1)
      rw [h]
  have hya : sylvPt n a 1 = ta / (ta ^ 2 + 1) := by
    simpa [sylvPt, mkPt_one, ta] using sin_mul_cos_eq_tan_div α hca
  have hyb : sylvPt n b 1 = tb / (tb ^ 2 + 1) := by
    simpa [sylvPt, mkPt_one, tb] using sin_mul_cos_eq_tan_div β hcb
  have hyc : sylvPt n c 1 = tc / (tc ^ 2 + 1) := by
    simpa [sylvPt, mkPt_one, tc] using sin_mul_cos_eq_tan_div γ hcc
  have hdet_id :
      (tb - ta) * (tc / (tc ^ 2 + 1) - ta / (ta ^ 2 + 1)) -
      (tc - ta) * (tb / (tb ^ 2 + 1) - ta / (ta ^ 2 + 1)) =
      (tb - ta) * (tc - ta) * (tc - tb) * (ta * tb * tc - (ta + tb + tc)) /
      ((ta ^ 2 + 1) * (tb ^ 2 + 1) * (tc ^ 2 + 1)) := by
    have d1 : ta ^ 2 + 1 ≠ 0 := by positivity
    have d2 : tb ^ 2 + 1 ≠ 0 := by positivity
    have d3 : tc ^ 2 + 1 ≠ 0 := by positivity
    field_simp
    ring
  have htan_sin :
      ta + tb + tc - ta * tb * tc =
      Real.sin (α + β + γ) / (Real.cos α * Real.cos β * Real.cos γ) := by
    rw [sin_add_three_eq]
    simp only [ta, tb, tc, Real.tan_eq_sin_div_cos]
    field_simp
  have hiff1 :
      (sylvPt n b 0 - sylvPt n a 0) * (sylvPt n c 1 - sylvPt n a 1) =
      (sylvPt n c 0 - sylvPt n a 0) * (sylvPt n b 1 - sylvPt n a 1) ↔
      Real.sin (α + β + γ) = 0 := by
    rw [hya, hyb, hyc]
    simp only [sylvPt, mkPt_zero]
    change (tb - ta) * (tc / (tc ^ 2 + 1) - ta / (ta ^ 2 + 1)) =
      (tc - ta) * (tb / (tb ^ 2 + 1) - ta / (ta ^ 2 + 1)) ↔ Real.sin (α + β + γ) = 0
    rw [← sub_eq_zero, hdet_id]
    have hden : (ta ^ 2 + 1) * (tb ^ 2 + 1) * (tc ^ 2 + 1) ≠ 0 := by positivity
    rw [div_eq_zero_iff]
    simp only [hden, or_false]
    have hfac : (tb - ta) * (tc - ta) * (tc - tb) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr htab) (sub_ne_zero.mpr htac))
        (sub_ne_zero.mpr htbc)
    rw [mul_eq_zero]
    simp only [hfac, false_or]
    have hcos_prod : Real.cos α * Real.cos β * Real.cos γ ≠ 0 :=
      mul_ne_zero (mul_ne_zero hca hcb) hcc
    constructor
    · intro h
      have : ta + tb + tc - ta * tb * tc = 0 := by linarith
      rw [htan_sin, div_eq_zero_iff] at this
      exact this.resolve_right hcos_prod
    · intro h
      have : ta + tb + tc - ta * tb * tc = 0 := by rw [htan_sin, h, zero_div]
      linarith
  rw [hiff1, Real.sin_eq_zero_iff]
  have hsum_angle : α + β + γ = ((a.val + b.val + c.val + 1 : ℕ) : ℝ) / (n : ℝ) * Real.pi := by
    simp only [α, β, γ, sylvAngle]
    push_cast
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    field_simp
    ring
  rw [hsum_angle]
  constructor
  · rintro ⟨m, hm⟩
    have h1 : (m : ℝ) = ((a.val + b.val + c.val + 1 : ℕ) : ℝ) / (n : ℝ) :=
      mul_right_cancel₀ Real.pi_ne_zero hm
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have h2 : (m : ℝ) * (n : ℝ) = ((a.val + b.val + c.val + 1 : ℕ) : ℝ) := by
      rw [h1, div_mul_cancel₀ _ hn_ne]
    have h3 : m * (n : ℤ) = ((a.val + b.val + c.val + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    have hm_nn : 0 ≤ m := by
      by_contra hneg
      have : m * (n : ℤ) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) (by exact_mod_cast hn)
      omega
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hm_nn
    have hnat : q * n = a.val + b.val + c.val + 1 := by exact_mod_cast h3
    rw [← hnat, Nat.mul_mod_left]
  · intro hmod
    refine ⟨((a.val + b.val + c.val + 1) / n : ℕ), ?_⟩
    have hdiv : n * ((a.val + b.val + c.val + 1) / n) = a.val + b.val + c.val + 1 := by
      have := Nat.div_add_mod (a.val + b.val + c.val + 1) n
      omega
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hreal : (n : ℝ) * (((a.val + b.val + c.val + 1) / n : ℕ) : ℝ) =
        ((a.val + b.val + c.val + 1 : ℕ) : ℝ) := by exact_mod_cast hdiv
    simp only [Int.cast_natCast]
    field_simp
    linarith

private lemma eq_of_add_mod_zero {n z x y : ℕ} (hx : x < n) (hy : y < n)
    (h1 : (z + x) % n = 0) (h2 : (z + y) % n = 0) : x = y := by
  have hmod : z + x ≡ z + y [MOD n] := by rw [Nat.ModEq, h1, h2]
  have hxy : x ≡ y [MOD n] := Nat.ModEq.add_left_cancel' z hmod
  rw [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hxy
  exact hxy

/-- **Sharp `k = 3` Lower Bound (`588.lean`: `three_lower` / `sylvester`)**:
for every `n ≥ 3`, there exist a set `P` of `n` points in `ℝ²` with **no 4 collinear** and a
family `L` of distinct 1-dimensional lines each containing **exactly 3** points of `P` such that
`6 * |L| + 3 * n ≥ n^2` (asymptotically `|L| ≥ n^2 / 6 - n / 2`, matching Sylvester /
Burr–Grünbaum–Sloane / Füredi–Palásti's sharp constant `1/6`). -/
theorem ppl022_sylvester_three_lower (n : ℕ) (hn : 3 ≤ n) :
    ∃ (P : Finset (EuclideanSpace ℝ (Fin 2)))
      (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
      P.card = n ∧
      (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ 3) ∧
      (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = 3) ∧
      n * n ≤ 6 * L.card + 3 * n := by
  have hn_pos : 0 < n := by omega
  let P : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.image (sylvPt n)
  have hP_card : P.card = n := by
    rw [Finset.card_image_of_injective _ (sylvPt_injective hn_pos), Finset.card_univ, Fintype.card_fin]
  have hno4 : ∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ 3 := by
    intro ℓ hℓ
    by_contra hgt
    push Not at hgt
    have h4 : 4 ≤ (P.filter (· ∈ ℓ)).card := hgt
    obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h4
    -- Extract 4 distinct indices from S
    have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p₁, hp₁S⟩ := hS_ne
    have hS1_card : (S.erase p₁).card = 3 := by rw [Finset.card_erase_of_mem hp₁S, hS_card]
    obtain ⟨p₂, hp₂S⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase p₁).card)
    have hS2_card : ((S.erase p₁).erase p₂).card = 2 := by
      rw [Finset.card_erase_of_mem hp₂S, hS1_card]
    obtain ⟨p₃, hp₃S⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase p₁).erase p₂).card)
    have hS3_card : (((S.erase p₁).erase p₂).erase p₃).card = 1 := by
      rw [Finset.card_erase_of_mem hp₃S, hS2_card]
    obtain ⟨p₄, hp₄S⟩ := Finset.card_pos.mp (by omega : 0 < (((S.erase p₁).erase p₂).erase p₃).card)
    have hp₁ : p₁ ∈ P.filter (· ∈ ℓ) := hS_sub hp₁S
    have hp₂ : p₂ ∈ P.filter (· ∈ ℓ) := hS_sub (Finset.mem_of_mem_erase hp₂S)
    have hp₃ : p₃ ∈ P.filter (· ∈ ℓ) :=
      hS_sub (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp₃S))
    have hp₄ : p₄ ∈ P.filter (· ∈ ℓ) :=
      hS_sub (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp₄S)))
    have h12 : p₁ ≠ p₂ := (Finset.ne_of_mem_erase hp₂S).symm
    have h13 : p₁ ≠ p₃ := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp₃S)).symm
    have h23 : p₂ ≠ p₃ := (Finset.ne_of_mem_erase hp₃S).symm
    have h14 : p₁ ≠ p₄ :=
      (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp₄S))).symm
    have h24 : p₂ ≠ p₄ := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hp₄S)).symm
    have h34 : p₃ ≠ p₄ := (Finset.ne_of_mem_erase hp₄S).symm
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp₁).1
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp₂).1
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp₃).1
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hp₄).1
    have hab : a ≠ b := fun h => h12 (congrArg _ h)
    have hac : a ≠ c := fun h => h13 (congrArg _ h)
    have hbc : b ≠ c := fun h => h23 (congrArg _ h)
    have had : a ≠ d := fun h => h14 (congrArg _ h)
    have hbd : b ≠ d := fun h => h24 (congrArg _ h)
    have hcd : c ≠ d := fun h => h34 (congrArg _ h)
    have hdet_c := det_eq_zero_of_mem_line hℓ h12
      (Finset.mem_filter.mp hp₁).2 (Finset.mem_filter.mp hp₂).2 (Finset.mem_filter.mp hp₃).2
    have hdet_d := det_eq_zero_of_mem_line hℓ h12
      (Finset.mem_filter.mp hp₁).2 (Finset.mem_filter.mp hp₂).2 (Finset.mem_filter.mp hp₄).2
    have hmc : (a.val + b.val + c.val + 1) % n = 0 := (sylvPt_det_iff hn_pos hab hac hbc).mp hdet_c
    have hmd : (a.val + b.val + d.val + 1) % n = 0 := (sylvPt_det_iff hn_pos hab had hbd).mp hdet_d
    have hceqd : c.val = d.val :=
      eq_of_add_mod_zero c.isLt d.isLt
        (by rwa [show (a.val + b.val + 1) + c.val = a.val + b.val + c.val + 1 by omega])
        (by rwa [show (a.val + b.val + 1) + d.val = a.val + b.val + d.val + 1 by omega])
    exact hcd (Fin.ext hceqd)
  -- Build the finset `T` of valid 3-subsets of `Fin n` summing to `-1 mod n`
  let T : Finset (Finset (Fin n)) :=
    ((Finset.univ : Finset (Fin n)).powersetCard 3).filter
      (fun s => ((∑ i ∈ s, i.val) + 1) % n = 0)
  -- Map each 3-subset `s ∈ T` to its line `lineOf s`
  let lineOf : Finset (Fin n) → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := fun s =>
    if h : s.card = 3 then
      let p := s.min' (Finset.card_pos.mp (by omega))
      let q := (s.erase p).min' (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (Finset.min'_mem _ _), h]; omega))
      lineThrough (sylvPt n p) (sylvPt n q)
    else ⊥
  have hlineOf_props : ∀ s ∈ T,
      Module.finrank ℝ (lineOf s).direction = 1 ∧
      (∀ i ∈ s, sylvPt n i ∈ lineOf s) ∧
      (P.filter (· ∈ lineOf s)).card = 3 := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
    obtain ⟨⟨_, hscard⟩, hsmod⟩ := hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    let a := s.min' hne
    have ha : a ∈ s := Finset.min'_mem s hne
    have hne1 : (s.erase a).Nonempty :=
      Finset.card_pos.mp (by rw [Finset.card_erase_of_mem ha, hscard]; omega)
    let b := (s.erase a).min' hne1
    have hb_er : b ∈ s.erase a := Finset.min'_mem _ hne1
    have hb : b ∈ s := Finset.mem_of_mem_erase hb_er
    have hab : a ≠ b := (Finset.ne_of_mem_erase hb_er).symm
    have hcard2 : ((s.erase a).erase b).card = 1 := by
      rw [Finset.card_erase_of_mem hb_er, Finset.card_erase_of_mem ha, hscard]
    obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hcard2
    have hc_mem : c ∈ (s.erase a).erase b := by rw [hc_eq]; simp
    have hc : c ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc_mem)
    have hbc : b ≠ c := (Finset.ne_of_mem_erase hc_mem).symm
    have hac : a ≠ c := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc_mem)).symm
    have hs_eq : s = {a, b, c} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        by_cases hxa : x = a
        · exact Or.inl hxa
        · by_cases hxb : x = b
          · exact Or.inr (Or.inl hxb)
          · have : x ∈ (s.erase a).erase b :=
              Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩
            rw [hc_eq, Finset.mem_singleton] at this
            exact Or.inr (Or.inr this)
      · rintro (rfl | rfl | rfl) <;> assumption
    have hline_eq : lineOf s = lineThrough (sylvPt n a) (sylvPt n b) := by
      simp only [lineOf, dif_pos hscard]; rfl
    have hpab : sylvPt n a ≠ sylvPt n b := fun h => hab (sylvPt_injective hn_pos h)
    have hdim : Module.finrank ℝ (lineOf s).direction = 1 := by
      rw [hline_eq]; exact lineThrough_finrank hpab
    have hsum_s : ∑ i ∈ s, i.val = a.val + b.val + c.val := by
      rw [hs_eq, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      · ring
      · simp [hbc]
      · simp [hab, hac]
    have hmod_abc : (a.val + b.val + c.val + 1) % n = 0 := by rwa [← hsum_s]
    have hdet := (sylvPt_det_iff hn_pos hab hac hbc).mpr hmod_abc
    have hmem : ∀ i ∈ s, sylvPt n i ∈ lineOf s := by
      intro i hi
      rw [hs_eq] at hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [hline_eq]
      rcases hi with rfl | rfl | rfl
      · exact left_mem_lineThrough _ _
      · exact right_mem_lineThrough _ _
      · exact mem_lineThrough_of_det hpab hdet
    have hsub : s.image (sylvPt n) ⊆ P.filter (· ∈ lineOf s) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hmem i hi⟩
    have hge3 : 3 ≤ (P.filter (· ∈ lineOf s)).card := by
      calc 3 = s.card := hscard.symm
        _ = (s.image (sylvPt n)).card := (Finset.card_image_of_injective s (sylvPt_injective hn_pos)).symm
        _ ≤ (P.filter (· ∈ lineOf s)).card := Finset.card_le_card hsub
    have hle3 : (P.filter (· ∈ lineOf s)).card ≤ 3 := hno4 (lineOf s) hdim
    exact ⟨hdim, hmem, le_antisymm hle3 hge3⟩
  let L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := T.image lineOf
  have hlineOf_inj : Set.InjOn lineOf (T : Set (Finset (Fin n))) := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := hlineOf_props s₁ hs₁
    have h2 := hlineOf_props s₂ hs₂
    have hcard₁ : s₁.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs₁).1).2
    have hsub₁ : s₁.image (sylvPt n) ⊆ P.filter (· ∈ lineOf s₁) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, h1.2.1 i hi⟩
    have hsub₂ : s₂.image (sylvPt n) ⊆ P.filter (· ∈ lineOf s₁) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, heq ▸ h2.2.1 i hi⟩
    have himg₁ : s₁.image (sylvPt n) = P.filter (· ∈ lineOf s₁) :=
      Finset.eq_of_subset_of_card_le hsub₁ (by
        rw [Finset.card_image_of_injective _ (sylvPt_injective hn_pos), hcard₁, h1.2.2])
    have hcard₂ : s₂.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs₂).1).2
    have himg₂ : s₂.image (sylvPt n) = P.filter (· ∈ lineOf s₁) :=
      Finset.eq_of_subset_of_card_le hsub₂ (by
        rw [Finset.card_image_of_injective _ (sylvPt_injective hn_pos), hcard₂, h1.2.2])
    ext i
    constructor
    · intro hi
      have : sylvPt n i ∈ s₂.image (sylvPt n) := by
        rw [himg₂, ← himg₁]; exact Finset.mem_image_of_mem _ hi
      obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp this
      rwa [sylvPt_injective hn_pos hij] at hj
    · intro hi
      have : sylvPt n i ∈ s₁.image (sylvPt n) := by
        rw [himg₁, ← himg₂]; exact Finset.mem_image_of_mem _ hi
      obtain ⟨j, hj, hij⟩ := Finset.mem_image.mp this
      rwa [sylvPt_injective hn_pos hij] at hj
  have hL_card : L.card = T.card := Finset.card_image_of_injOn hlineOf_inj
  -- Lower bound `T.card`: count valid ordered pairs `(a, b) ∈ (Fin n)^2`
  let compC : Fin n → Fin n → Fin n := fun a b =>
    ⟨(n - (a.val + b.val + 1) % n) % n, Nat.mod_lt _ hn_pos⟩
  have hcompC_mod : ∀ a b : Fin n, (a.val + b.val + (compC a b).val + 1) % n = 0 := by
    intro a b
    dsimp [compC]
    set r := (a.val + b.val + 1) % n
    have hr : r < n := Nat.mod_lt _ hn_pos
    have h1 : a.val + b.val + (n - r) % n + 1 = (a.val + b.val + 1) + (n - r) % n := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod]
    by_cases hr0 : r = 0
    · simp [r, hr0]
    · have hlt : n - r < n := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have : r + (n - r) = n := by omega
      change (r + (n - r)) % n = 0
      rw [this, Nat.mod_self]
  let goodPairs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ compC p.1 p.2 ∧ p.2 ≠ compC p.1 p.2)
  let bad1 : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 = p.2)
  let bad2 : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 = compC p.1 p.2)
  let bad3 : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.2 = compC p.1 p.2)
  have hbad1 : bad1.card ≤ n := by
    have hsub : bad1 ⊆ (Finset.univ : Finset (Fin n)).image (fun a => (a, a)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_image.mpr ⟨p.1, Finset.mem_univ _, Prod.ext rfl hp.2⟩
    calc bad1.card ≤ ((Finset.univ : Finset (Fin n)).image (fun a => (a, a))).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have hbad2 : bad2.card ≤ n := by
    have hinj : ∀ p₁ ∈ bad2, ∀ p₂ ∈ bad2, p₁.1 = p₂.1 → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ heq1
      have hm1 := hcompC_mod p₁.1 p₁.2
      have hm2 := hcompC_mod p₂.1 p₂.2
      rw [← (Finset.mem_filter.mp hp₁).2] at hm1
      rw [← (Finset.mem_filter.mp hp₂).2] at hm2
      rw [heq1] at hm1
      have hb_eq : p₁.2.val = p₂.2.val :=
        eq_of_add_mod_zero p₁.2.isLt p₂.2.isLt
          (by rwa [show (p₂.1.val + p₂.1.val + 1) + p₁.2.val =
            p₂.1.val + p₁.2.val + p₂.1.val + 1 by omega])
          (by rwa [show (p₂.1.val + p₂.1.val + 1) + p₂.2.val =
            p₂.1.val + p₂.2.val + p₂.1.val + 1 by omega])
      exact Prod.ext heq1 (Fin.ext hb_eq)
    have hcard : (bad2.image Prod.fst).card = bad2.card :=
      Finset.card_image_of_injOn fun p₁ hp₁ p₂ hp₂ h => hinj p₁ hp₁ p₂ hp₂ h
    calc bad2.card = (bad2.image Prod.fst).card := hcard.symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hbad3 : bad3.card ≤ n := by
    have hinj : ∀ p₁ ∈ bad3, ∀ p₂ ∈ bad3, p₁.2 = p₂.2 → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ heq2
      have hm1 := hcompC_mod p₁.1 p₁.2
      have hm2 := hcompC_mod p₂.1 p₂.2
      rw [← (Finset.mem_filter.mp hp₁).2] at hm1
      rw [← (Finset.mem_filter.mp hp₂).2] at hm2
      rw [heq2] at hm1
      have ha_eq : p₁.1.val = p₂.1.val :=
        eq_of_add_mod_zero p₁.1.isLt p₂.1.isLt
          (by rwa [show (p₂.2.val + p₂.2.val + 1) + p₁.1.val =
            p₁.1.val + p₂.2.val + p₂.2.val + 1 by omega])
          (by rwa [show (p₂.2.val + p₂.2.val + 1) + p₂.1.val =
            p₂.1.val + p₂.2.val + p₂.2.val + 1 by omega])
      exact Prod.ext (Fin.ext ha_eq) heq2
    have hcard : (bad3.image Prod.snd).card = bad3.card :=
      Finset.card_image_of_injOn fun p₁ hp₁ p₂ hp₂ h => hinj p₁ hp₁ p₂ hp₂ h
    calc bad3.card = (bad3.image Prod.snd).card := hcard.symm
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have huniv_sub : (Finset.univ : Finset (Fin n × Fin n)) ⊆ goodPairs ∪ bad1 ∪ bad2 ∪ bad3 := by
    intro p _
    by_cases h1 : p.1 = p.2
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)))
    · by_cases h2 : p.1 = compC p.1 p.2
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
      · by_cases h3 : p.2 = compC p.1 p.2
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩)))
  have hgood_lb : n * n ≤ goodPairs.card + 3 * n := by
    have hu : n * n = (Finset.univ : Finset (Fin n × Fin n)).card := by simp
    have h1 := Finset.card_le_card huniv_sub
    have h2 : (goodPairs ∪ bad1 ∪ bad2 ∪ bad3).card ≤
        goodPairs.card + bad1.card + bad2.card + bad3.card := by
      have a := Finset.card_union_le (goodPairs ∪ bad1 ∪ bad2) bad3
      have b := Finset.card_union_le (goodPairs ∪ bad1) bad2
      have c := Finset.card_union_le goodPairs bad1
      omega
    omega
  -- Map each good pair `(a, b)` to `{a, b, compC a b} ∈ T` (at most 6-to-1)
  let mkTriple : Fin n × Fin n → Finset (Fin n) := fun p => {p.1, p.2, compC p.1 p.2}
  have hmaps : ∀ p ∈ goodPairs, mkTriple p ∈ T := by
    intro p hp
    obtain ⟨_, h12, h13, h23⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · dsimp [mkTriple]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h23]
      · simp [h12, h13]
    · dsimp [mkTriple]
      rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      · have := hcompC_mod p.1 p.2
        rwa [show p.1.val + (p.2.val + (compC p.1 p.2).val) + 1 =
          p.1.val + p.2.val + (compC p.1 p.2).val + 1 by omega]
      · simp [h23]
      · simp [h12, h13]
  have hfiber : ∀ s ∈ T, (goodPairs.filter (fun p => mkTriple p = s)).card ≤ 6 := by
    intro s hs
    have hscard : s.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
    have hsub : goodPairs.filter (fun p => mkTriple p = s) ⊆
        (s ×ˢ s).filter (fun p => p.1 ≠ p.2) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, (Finset.mem_filter.mp hp.1).2.1⟩
      · rw [← hp.2]; simp [mkTriple]
      · rw [← hp.2]; simp [mkTriple]
    have hoff : ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).card = 6 := by
      have hdiag : ((s ×ˢ s).filter (fun p => p.1 = p.2)).card = s.card := by
        have heq : (s ×ˢ s).filter (fun p => p.1 = p.2) = s.image (fun a => (a, a)) := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨hp1, _⟩, heq⟩; exact ⟨p.1, hp1, Prod.ext rfl heq⟩
          · rintro ⟨a, ha, rfl⟩; exact ⟨⟨ha, ha⟩, rfl⟩
        rw [heq, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
      have htot : ((s ×ˢ s).filter (fun p => p.1 = p.2)).card +
          ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).card = (s ×ˢ s).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1
          ext p
          simp only [Finset.mem_union, Finset.mem_filter, ne_eq]
          tauto
        · rw [Finset.disjoint_left]
          intro p hp1 hp2
          exact (Finset.mem_filter.mp hp2).2 (Finset.mem_filter.mp hp1).2
      rw [Finset.card_product, hdiag, hscard] at htot
      omega
    exact (Finset.card_le_card hsub).trans (le_of_eq hoff)
  have hgood_le_6T : goodPairs.card ≤ 6 * T.card := by
    calc goodPairs.card
        = ∑ s ∈ T, (goodPairs.filter (fun p => mkTriple p = s)).card := by
          rw [Finset.card_eq_sum_card_fiberwise hmaps]
      _ ≤ ∑ _s ∈ T, 6 := Finset.sum_le_sum hfiber
      _ = 6 * T.card := by simp [mul_comm]
  refine ⟨P, L, hP_card, hno4, ?_, ?_⟩
  · intro ℓ hℓ
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hℓ
    exact ⟨(hlineOf_props s hs).1, (hlineOf_props s hs).2.2⟩
  · rw [hL_card]; omega

/-- **`k = 3` Is Not `o(n^2)` (`588.lean`: `three_not_isLittleO`)**:
there exists no upper bound `f : ℕ → ℝ` with `f = o(n^2)` that dominates the number of 3-point
lines among `n` points with no 4 collinear. -/
theorem ppl022_three_not_isLittleO (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, 3 ≤ n →
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
        P.card = n →
        (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ 3) →
        (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = 3) →
        (L.card : ℝ) ≤ f n) :
    ¬ Asymptotics.IsLittleO Filter.atTop f (fun n : ℕ => (n : ℝ) ^ 2) := by
  intro ho
  have hsmall := ho.bound (show (0 : ℝ) < 1 / 12 by norm_num)
  rw [Filter.eventually_atTop] at hsmall
  obtain ⟨N, hN⟩ := hsmall
  let n : ℕ := max N 7
  have hn3 : 3 ≤ n := by omega
  have hn7 : 7 ≤ n := le_max_right N 7
  have hnN : N ≤ n := le_max_left N 7
  obtain ⟨P, L, hP, hno4, hL, hcount⟩ := ppl022_sylvester_three_lower n hn3
  have hfl : (L.card : ℝ) ≤ f n := hf n hn3 P L hP hno4 hL
  have hbound : ‖f n‖ ≤ (1 / 12 : ℝ) * ‖(n : ℝ) ^ 2‖ := hN n hnN
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))] at hbound
  have hf_le : f n ≤ (1 / 12 : ℝ) * (n : ℝ) ^ 2 := (le_abs_self (f n)).trans hbound
  have hcount_r : (n : ℝ) * (n : ℝ) ≤ 6 * (L.card : ℝ) + 3 * (n : ℝ) := by exact_mod_cast hcount
  have hn7_r : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn7
  nlinarith

/-! ### Section 5: Solymosi–Stojaković (2013), Grünbaum (1976), Kárteszi (1963) Lower Bounds -/

/-- A quadratic equation `A * t^2 + B * t + D = 0` with `A ≠ 0` has at most two distinct roots. -/
private lemma not_three_roots_quadratic {A B D t₁ t₂ t₃ : ℝ} (hA : A ≠ 0)
    (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (hr1 : A * t₁ ^ 2 + B * t₁ + D = 0)
    (hr2 : A * t₂ ^ 2 + B * t₂ + D = 0)
    (hr3 : A * t₃ ^ 2 + B * t₃ + D = 0) : False := by
  have hd12 : (t₁ - t₂) * (A * (t₁ + t₂) + B) = 0 := by linarith [hr1, hr2]
  have hd13 : (t₁ - t₃) * (A * (t₁ + t₃) + B) = 0 := by linarith [hr1, hr3]
  have hs12 : A * (t₁ + t₂) + B = 0 := (mul_eq_zero.mp hd12).resolve_left (sub_ne_zero.mpr h12)
  have hs13 : A * (t₁ + t₃) + B = 0 := (mul_eq_zero.mp hd13).resolve_left (sub_ne_zero.mpr h13)
  have h23' : A * (t₂ - t₃) = 0 := by linarith
  exact (mul_eq_zero.mp h23').elim hA (sub_ne_zero.mpr h23)

/-- Any line `t ↦ u + t • v` (`v ≠ 0`) in `ℝ^d` intersects a sphere `∑ i, (x i)^2 = R` in at most
two points. -/
private lemma sphere_line_le_two {d : ℕ} (R : ℝ) (u v : Fin d → ℝ) (hv : v ≠ 0)
    {t₁ t₂ t₃ : ℝ} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (h1 : ∑ i : Fin d, (u i + t₁ * v i) ^ 2 = R)
    (h2 : ∑ i : Fin d, (u i + t₂ * v i) ^ 2 = R)
    (h3 : ∑ i : Fin d, (u i + t₃ * v i) ^ 2 = R) : False := by
  set A : ℝ := ∑ i : Fin d, (v i) ^ 2
  set B : ℝ := 2 * ∑ i : Fin d, u i * v i
  set D : ℝ := (∑ i : Fin d, (u i) ^ 2) - R
  have hA : A ≠ 0 := by
    have hex : ∃ i₀ : Fin d, v i₀ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv (funext hall)
    obtain ⟨i₀, hi₀⟩ := hex
    have hpos : 0 < A := by
      have hterm : 0 < (v i₀) ^ 2 := sq_pos_of_ne_zero hi₀
      have hle : (v i₀) ^ 2 ≤ A :=
        Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_univ i₀)
      linarith
    exact ne_of_gt hpos
  have expand : ∀ t : ℝ, (∑ i : Fin d, (u i + t * v i) ^ 2) = R → A * t ^ 2 + B * t + D = 0 := by
    intro t ht
    have hexp : ∑ i : Fin d, (u i + t * v i) ^ 2 =
        (∑ i : Fin d, (u i) ^ 2) + 2 * t * (∑ i : Fin d, u i * v i) +
        t ^ 2 * (∑ i : Fin d, (v i) ^ 2) := by
      have hpoint : ∀ i : Fin d,
          (u i + t * v i) ^ 2 = (u i) ^ 2 + 2 * t * (u i * v i) + t ^ 2 * (v i) ^ 2 := fun i => by
        ring
      simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
    change (∑ i : Fin d, (v i) ^ 2) * t ^ 2 + (2 * ∑ i : Fin d, u i * v i) * t +
      ((∑ i : Fin d, (u i) ^ 2) - R) = 0
    linarith
  exact not_three_roots_quadratic hA h12 h13 h23 (expand t₁ h1) (expand t₂ h2) (expand t₃ h3)

/-- Base-`(m + 1)` univariate moment-curve linear projection `ℝ^m → ℝ²`. -/
private noncomputable def projPt (m : ℕ) (t : ℝ) (v : Fin m → ℝ) : EuclideanSpace ℝ (Fin 2) :=
  mkPt (∑ i : Fin m, v i * t ^ i.val) (∑ i : Fin m, v i * t ^ ((m + 1) * i.val))

private lemma projPt_zero (m : ℕ) (t : ℝ) (v : Fin m → ℝ) :
    projPt m t v 0 = ∑ i : Fin m, v i * t ^ i.val := rfl

private lemma projPt_one (m : ℕ) (t : ℝ) (v : Fin m → ℝ) :
    projPt m t v 1 = ∑ i : Fin m, v i * t ^ ((m + 1) * i.val) := rfl

private noncomputable def diffPoly {m : ℕ} (a : Fin m → ℝ) : Polynomial ℝ :=
  ∑ i : Fin m, Polynomial.C (a i) * Polynomial.X ^ i.val

private lemma eval_diffPoly {m : ℕ} (a : Fin m → ℝ) (t : ℝ) :
    (diffPoly a).eval t = ∑ i : Fin m, a i * t ^ i.val := by
  simp [diffPoly, Polynomial.eval_finsetSum]

private lemma diffPoly_ne_zero {m : ℕ} {a : Fin m → ℝ} (ha : a ≠ 0) : diffPoly a ≠ 0 := by
  have hex : ∃ i₀ : Fin m, a i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha (funext hall)
  obtain ⟨i₀, hi₀⟩ := hex
  intro h0
  have hcoeff : (diffPoly a).coeff i₀.val = 0 := by rw [h0]; simp
  rw [diffPoly, Polynomial.finsetSum_coeff] at hcoeff
  have hval : ∑ i : Fin m, (Polynomial.C (a i) * Polynomial.X ^ i.val).coeff i₀.val = a i₀ := by
    rw [Finset.sum_eq_single i₀]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro i _ hne
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hne' : i₀.val ≠ i.val := fun h => hne (Fin.ext h.symm)
      rw [if_neg hne', mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [hval] at hcoeff
  exact hi₀ hcoeff

private noncomputable def detPoly {m : ℕ} (a b : Fin m → ℝ) : Polynomial ℝ :=
  ∑ i : Fin m, ∑ j : Fin m,
    Polynomial.C (a i * b j - b i * a j) * Polynomial.X ^ (i.val + (m + 1) * j.val)

private lemma eval_detPoly {m : ℕ} (a b : Fin m → ℝ) (t : ℝ) :
    (detPoly a b).eval t =
      (∑ i : Fin m, a i * t ^ i.val) * (∑ j : Fin m, b j * t ^ ((m + 1) * j.val)) -
      (∑ i : Fin m, b i * t ^ i.val) * (∑ j : Fin m, a j * t ^ ((m + 1) * j.val)) := by
  simp only [detPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, pow_add]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma base_repr_inj {m : ℕ} {i₁ j₁ i₂ j₂ : Fin m}
    (heq : i₁.val + (m + 1) * j₁.val = i₂.val + (m + 1) * j₂.val) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hi₁ : i₁.val < m + 1 := Nat.lt_succ_of_lt i₁.isLt
  have hi₂ : i₂.val < m + 1 := Nat.lt_succ_of_lt i₂.isLt
  have hj : j₁.val = j₂.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : i₁.val + (m + 1) * j₁.val < (m + 1) * (j₁.val + 1) := by nlinarith
      have : (m + 1) * (j₁.val + 1) ≤ (m + 1) * j₂.val := Nat.mul_le_mul_left (m + 1) hlt
      omega
    · have : i₂.val + (m + 1) * j₂.val < (m + 1) * (j₂.val + 1) := by nlinarith
      have : (m + 1) * (j₂.val + 1) ≤ (m + 1) * j₁.val := Nat.mul_le_mul_left (m + 1) hgt
      omega
  have hi : i₁.val = i₂.val := by rw [hj] at heq; omega
  exact ⟨Fin.ext hi, Fin.ext hj⟩

private lemma detPoly_ne_zero {m : ℕ} {a b : Fin m → ℝ}
    (ha : a ≠ 0) (hind : ∀ c : ℝ, b ≠ c • a) : detPoly a b ≠ 0 := by
  have hex_i : ∃ i₀ : Fin m, a i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha (funext hall)
  obtain ⟨i₀, hi₀⟩ := hex_i
  set c : ℝ := b i₀ / a i₀
  have hne_c : b ≠ c • a := hind c
  have hex_j : ∃ j₀ : Fin m, b j₀ ≠ c * a j₀ := by
    by_contra hall
    push Not at hall
    exact hne_c (funext hall)
  obtain ⟨j₀, hj₀⟩ := hex_j
  have hdet_ne : a i₀ * b j₀ - b i₀ * a j₀ ≠ 0 := by
    intro h0
    apply hj₀
    simp only [c]
    field_simp [hi₀]
    linarith
  intro hzero
  have hcoeff : (detPoly a b).coeff (i₀.val + (m + 1) * j₀.val) = 0 := by rw [hzero]; simp
  rw [detPoly, Polynomial.finsetSum_coeff] at hcoeff
  have hval :
      ∑ i : Fin m, (∑ j : Fin m,
        Polynomial.C (a i * b j - b i * a j) * Polynomial.X ^ (i.val + (m + 1) * j.val)).coeff
        (i₀.val + (m + 1) * j₀.val) = a i₀ * b j₀ - b i₀ * a j₀ := by
    rw [Finset.sum_eq_single i₀]
    · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j₀]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro j _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hne' : i₀.val + (m + 1) * j₀.val ≠ i₀.val + (m + 1) * j.val := by
          intro heq
          exact hne (base_repr_inj heq).2.symm
        rw [if_neg hne', mul_zero]
      · intro h; exact absurd (Finset.mem_univ j₀) h
    · intro i _ hne
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hne' : i₀.val + (m + 1) * j₀.val ≠ i.val + (m + 1) * j.val := by
        intro heq
        exact hne (base_repr_inj heq).1.symm
      rw [if_neg hne', mul_zero]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [hval] at hcoeff
  exact hdet_ne hcoeff

/-- Existence of a generic moment-curve projection `ℝ^m → ℝ²` that is injective on any finite set
`Q ⊆ ℝ^m` and strictly preserves collinearity and non-collinearity of all triples in `Q`. -/
private lemma exists_generic_projection {m : ℕ} (Q : Finset (Fin m → ℝ)) :
    ∃ t₀ : ℝ,
      Set.InjOn (projPt m t₀) (Q : Set (Fin m → ℝ)) ∧
      (∀ p ∈ Q, ∀ q ∈ Q, ∀ s ∈ Q, p ≠ q →
        ((projPt m t₀ q 0 - projPt m t₀ p 0) * (projPt m t₀ s 1 - projPt m t₀ p 1) =
         (projPt m t₀ s 0 - projPt m t₀ p 0) * (projPt m t₀ q 1 - projPt m t₀ p 1) ↔
         ∃ c : ℝ, s - p = c • (q - p))) := by
  let polys1 : Finset (Polynomial ℝ) :=
    ((Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => diffPoly (pq.1 - pq.2))
  let polys2 : Finset (Polynomial ℝ) :=
    (((Q ×ˢ Q) ×ˢ Q).filter (fun t => t.1.1 ≠ t.1.2 ∧ ∀ c : ℝ, t.2 - t.1.1 ≠ c • (t.1.2 - t.1.1))).image
      (fun t => detPoly (t.1.2 - t.1.1) (t.2 - t.1.1))
  let badRoots : Finset ℝ := (polys1 ∪ polys2).biUnion (fun P => P.roots.toFinset)
  obtain ⟨t₀, ht₀⟩ := Infinite.exists_notMem_finset badRoots
  refine ⟨t₀, ?_, ?_⟩
  · intro p hp q hq heq
    by_contra hpq
    have hpoly_mem : diffPoly (p - q) ∈ polys1 :=
      Finset.mem_image.mpr ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hpq⟩, rfl⟩
    have hne0 : diffPoly (p - q) ≠ 0 := diffPoly_ne_zero (sub_ne_zero.mpr hpq)
    have hroot : (diffPoly (p - q)).eval t₀ = 0 := by
      rw [eval_diffPoly]
      have h0 : projPt m t₀ p 0 = projPt m t₀ q 0 := congrArg (fun v => v 0) heq
      rw [projPt_zero, projPt_zero] at h0
      have : ∑ i : Fin m, (p - q) i * t₀ ^ i.val =
          (∑ i : Fin m, p i * t₀ ^ i.val) - (∑ i : Fin m, q i * t₀ ^ i.val) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.sub_apply]
        ring
      linarith
    have hmem_bad : t₀ ∈ badRoots := by
      rw [Finset.mem_biUnion]
      refine ⟨diffPoly (p - q), Finset.mem_union_left _ hpoly_mem, ?_⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne0]
      exact hroot
    exact ht₀ hmem_bad
  · intro p hp q hq s hs hpq
    constructor
    · intro hdet
      by_contra hnotcol
      push Not at hnotcol
      have hpoly_mem : detPoly (q - p) (s - p) ∈ polys2 := by
        refine Finset.mem_image.mpr ⟨((p, q), s), Finset.mem_filter.mpr ?_, rfl⟩
        exact ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hs⟩, hpq, hnotcol⟩
      have hne0 : detPoly (q - p) (s - p) ≠ 0 :=
        detPoly_ne_zero (sub_ne_zero.mpr hpq.symm) hnotcol
      have hroot : (detPoly (q - p) (s - p)).eval t₀ = 0 := by
        rw [eval_detPoly]
        have hq0 : ∑ i : Fin m, (q - p) i * t₀ ^ i.val = projPt m t₀ q 0 - projPt m t₀ p 0 := by
          rw [projPt_zero, projPt_zero, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_; simp only [Pi.sub_apply]; ring
        have hs0 : ∑ i : Fin m, (s - p) i * t₀ ^ i.val = projPt m t₀ s 0 - projPt m t₀ p 0 := by
          rw [projPt_zero, projPt_zero, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_; simp only [Pi.sub_apply]; ring
        have hq1 : ∑ i : Fin m, (q - p) i * t₀ ^ ((m + 1) * i.val) =
            projPt m t₀ q 1 - projPt m t₀ p 1 := by
          rw [projPt_one, projPt_one, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_; simp only [Pi.sub_apply]; ring
        have hs1 : ∑ i : Fin m, (s - p) i * t₀ ^ ((m + 1) * i.val) =
            projPt m t₀ s 1 - projPt m t₀ p 1 := by
          rw [projPt_one, projPt_one, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_; simp only [Pi.sub_apply]; ring
        rw [hq0, hs0, hq1, hs1]
        linarith
      have hmem_bad : t₀ ∈ badRoots := by
        rw [Finset.mem_biUnion]
        refine ⟨detPoly (q - p) (s - p), Finset.mem_union_right _ hpoly_mem, ?_⟩
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne0]
        exact hroot
      exact ht₀ hmem_bad
    · rintro ⟨c, hc⟩
      have hs0 : projPt m t₀ s 0 - projPt m t₀ p 0 = c * (projPt m t₀ q 0 - projPt m t₀ p 0) := by
        rw [projPt_zero, projPt_zero, projPt_zero, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi : s i - p i = c * (q i - p i) := by
          have := congrFun hc i
          simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
        calc s i * t₀ ^ i.val - p i * t₀ ^ i.val = (s i - p i) * t₀ ^ i.val := by ring
          _ = (c * (q i - p i)) * t₀ ^ i.val := by rw [hi]
          _ = c * (q i * t₀ ^ i.val - p i * t₀ ^ i.val) := by ring
      have hs1 : projPt m t₀ s 1 - projPt m t₀ p 1 = c * (projPt m t₀ q 1 - projPt m t₀ p 1) := by
        rw [projPt_one, projPt_one, projPt_one, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi : s i - p i = c * (q i - p i) := by
          have := congrFun hc i
          simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
        calc s i * t₀ ^ ((m + 1) * i.val) - p i * t₀ ^ ((m + 1) * i.val)
            = (s i - p i) * t₀ ^ ((m + 1) * i.val) := by ring
          _ = (c * (q i - p i)) * t₀ ^ ((m + 1) * i.val) := by rw [hi]
          _ = c * (q i * t₀ ^ ((m + 1) * i.val) - p i * t₀ ^ ((m + 1) * i.val)) := by ring
      rw [hs0, hs1]
      ring

/-- Padding lemma: for any finite set `P ⊆ ℝ²`, there exists a point `q ∉ P` lying on no line
determined by any two distinct points of `P`. -/
private lemma exists_general_position_point (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    ∃ q : EuclideanSpace ℝ (Fin 2), q ∉ P ∧
      ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ → q ∉ lineThrough p₁ p₂ := by
  let badX : Finset ℝ := P.image (fun p => p 0)
  obtain ⟨x₀, hx₀⟩ := Infinite.exists_notMem_finset badX
  let badY : Finset ℝ :=
    ((P ×ˢ P).filter (fun pq => pq.1 0 ≠ pq.2 0)).image
      (fun pq => pq.1 1 + (x₀ - pq.1 0) * (pq.2 1 - pq.1 1) / (pq.2 0 - pq.1 0))
  obtain ⟨y₀, hy₀⟩ := Infinite.exists_notMem_finset badY
  refine ⟨mkPt x₀ y₀, ?_, ?_⟩
  · intro hmem
    exact hx₀ (Finset.mem_image.mpr ⟨mkPt x₀ y₀, hmem, rfl⟩)
  · intro p₁ hp₁ p₂ hp₂ hp12 hq_line
    have hdet := det_eq_zero_of_mem_line (lineThrough_finrank hp12) hp12
      (left_mem_lineThrough p₁ p₂) (right_mem_lineThrough p₁ p₂) hq_line
    rw [mkPt_zero, mkPt_one] at hdet
    by_cases hx : p₁ 0 = p₂ 0
    · have h0 : (x₀ - p₁ 0) * (p₂ 1 - p₁ 1) = 0 := by rw [← hdet, hx]; ring
      have hx0_ne : x₀ - p₁ 0 ≠ 0 := by
        intro h; apply hx₀; exact Finset.mem_image.mpr ⟨p₁, hp₁, by linarith⟩
      have hy_eq : p₂ 1 - p₁ 1 = 0 := (mul_eq_zero.mp h0).resolve_left hx0_ne
      exact hp12 (mkPt_ext hx (by linarith))
    · have hden : p₂ 0 - p₁ 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have hy_eq : y₀ = p₁ 1 + (x₀ - p₁ 0) * (p₂ 1 - p₁ 1) / (p₂ 0 - p₁ 0) := by
        field_simp [hden]
        linarith
      apply hy₀
      exact Finset.mem_image.mpr
        ⟨(p₁, p₂), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₁, hp₂⟩, hx⟩, hy_eq.symm⟩

/-- Pad a planar point set `P₀` of size `≤ n` (with no `k + 1` collinear, `k ≥ 2`) to exact size
`n` without creating any `(k + 1)`-collinear line or disturbing any existing `k`-point line. -/
private lemma pad_point_set {k n : ℕ} (hk : 2 ≤ k)
    (P₀ : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
    (hcard : P₀.card ≤ n)
    (hnok : ∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      Module.finrank ℝ ℓ.direction = 1 → (P₀.filter (· ∈ ℓ)).card ≤ k)
    (hL : ∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P₀.filter (· ∈ ℓ)).card = k) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧
      (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k) ∧
      (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hcard
  induction m with
  | zero => exact ⟨P₀, by simp, hnok, hL⟩
  | succ m ih =>
    obtain ⟨P, hP_card, hP_nok, hP_L⟩ := ih (by omega)
    obtain ⟨q, hq_not, hq_gen⟩ := exists_general_position_point P
    refine ⟨insert q P, by rw [Finset.card_insert_of_notMem hq_not, hP_card]; omega, ?_, ?_⟩
    · intro ℓ hℓ
      by_cases hqℓ : q ∈ ℓ
      · have hle1 : (P.filter (· ∈ ℓ)).card ≤ 1 := by
          by_contra hgt
          push Not at hgt
          obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.mp hgt
          rw [Finset.mem_filter] at hp₁ hp₂
          have hline_eq : ℓ = lineThrough p₁ p₂ :=
            affine_line_eq_of_two_mem hℓ (lineThrough_finrank hp12) hp12
              hp₁.2 hp₂.2 (left_mem_lineThrough _ _) (right_mem_lineThrough _ _)
          exact hq_gen p₁ hp₁.1 p₂ hp₂.1 hp12 (hline_eq ▸ hqℓ)
        have hfilt : (insert q P).filter (· ∈ ℓ) = insert q (P.filter (· ∈ ℓ)) := by
          rw [Finset.filter_insert, if_pos hqℓ]
        rw [hfilt, Finset.card_insert_of_notMem (fun h => hq_not (Finset.mem_filter.mp h).1)]
        omega
      · have hfilt : (insert q P).filter (· ∈ ℓ) = P.filter (· ∈ ℓ) := by
          rw [Finset.filter_insert, if_neg hqℓ]
        rw [hfilt]
        exact hP_nok ℓ hℓ
    · intro ℓ hℓ
      obtain ⟨hdim, hcardk⟩ := hP_L ℓ hℓ
      have hqℓ : q ∉ ℓ := by
        intro hmem
        have hgt : 1 < (P.filter (· ∈ ℓ)).card := by omega
        obtain ⟨p₁, hp₁, p₂, hp₂, hp12⟩ := Finset.one_lt_card.mp hgt
        rw [Finset.mem_filter] at hp₁ hp₂
        have hline_eq : ℓ = lineThrough p₁ p₂ :=
          affine_line_eq_of_two_mem hdim (lineThrough_finrank hp12) hp12
            hp₁.2 hp₂.2 (left_mem_lineThrough _ _) (right_mem_lineThrough _ _)
        exact hq_gen p₁ hp₁.1 p₂ hp₂.1 hp12 (hline_eq ▸ hmem)
      refine ⟨hdim, ?_⟩
      rw [Finset.filter_insert, if_neg hqℓ]
      exact hcardk

/-- Finite pigeonhole principle: if `f : A → B`, then some fiber has size `≥ |A| / |B|`. -/
private lemma exists_fiber_mul_ge {α β : Type*} [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → β) (hmaps : ∀ a ∈ A, f a ∈ B) (hB : B.Nonempty) :
    ∃ b ∈ B, A.card ≤ B.card * (A.filter (fun a => f a = b)).card := by
  by_contra hall
  push Not at hall
  have hsum : ∑ b ∈ B, B.card * (A.filter (fun a => f a = b)).card < ∑ _b ∈ B, A.card := by
    refine Finset.sum_lt_sum_of_nonempty hB fun b hb => ?_
    exact hall b hb
  rw [← Finset.mul_sum, ← Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_const, smul_eq_mul] at hsum
  omega

/-- Finite layered Behrend-sphere construction in `ℝ²` (for any `k ≥ 3`, `d ≥ 1`, `r ≥ 1`):
produces `P ⊆ ℝ²` with `|P| ≤ k * (2 * k * r)^d`, no `k + 1` collinear, and a family `L` of
distinct `k`-point lines satisfying
`(d * r^2) * (d * r^2 + 1)^2 * |L| ≥ r^d * (r^d - (d * r^2 + 1))` (in integer form). -/
private lemma layered_sphere_construction (k d r : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    ∃ (P : Finset (EuclideanSpace ℝ (Fin 2)))
      (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
      P.card ≤ k * (2 * k * r) ^ d ∧
      (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k) ∧
      (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = k) ∧
      ∃ S_card : ℕ,
        r ^ d ≤ (d * r ^ 2 + 1) * S_card ∧
        S_card * (S_card - 1) ≤ (d * r ^ 2) * L.card := by
  let sqNorm : (Fin d → ℤ) → ℤ := fun w => ∑ i : Fin d, (w i) ^ 2
  let B : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) (r : ℤ))
  have hB_card : B.card = r ^ d := by
    rw [Fintype.card_piFinset]
    simp [Int.card_Ico]
  let normRange : Finset ℤ := Finset.Icc (0 : ℤ) ((d * r ^ 2 : ℕ) : ℤ)
  have hnormRange_card : normRange.card = d * r ^ 2 + 1 := by
    simp only [normRange, Int.card_Icc, sub_zero]
    omega
  have hB_maps : ∀ w ∈ B, sqNorm w ∈ normRange := by
    intro w hw
    rw [Finset.mem_Icc]
    refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg (w i), ?_⟩
    have hle : ∀ i : Fin d, (w i) ^ 2 ≤ ((r : ℤ) ^ 2) := by
      intro i
      have hi : w i ∈ Finset.Ico (0 : ℤ) (r : ℤ) := (Fintype.mem_piFinset.mp hw) i
      rw [Finset.mem_Ico] at hi
      nlinarith
    calc ∑ i : Fin d, (w i) ^ 2 ≤ ∑ _i : Fin d, (r : ℤ) ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = ((d * r ^ 2 : ℕ) : ℤ) := by simp [Finset.sum_const]
  have hnorm_ne : normRange.Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨le_refl _, by positivity⟩⟩
  obtain ⟨R₀, _, hR₀⟩ := exists_fiber_mul_ge B normRange sqNorm hB_maps hnorm_ne
  rw [hB_card, hnormRange_card] at hR₀
  let S : Finset (Fin d → ℤ) := B.filter (fun w => sqNorm w = R₀)
  let U : Finset ((Fin d → ℤ) × (Fin d → ℤ)) := (S ×ˢ S).filter (fun p => p.1 ≠ p.2)
  have hU_card : U.card = S.card * (S.card - 1) := by
    have hdiag : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card = S.card := by
      have heq : (S ×ˢ S).filter (fun p => p.1 = p.2) = S.image (fun x => (x, x)) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
        constructor
        · rintro ⟨⟨hp1, _⟩, h⟩; exact ⟨p.1, hp1, Prod.ext rfl h⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨⟨hx, hx⟩, rfl⟩
      rw [heq, Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
    have htot : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card + U.card = (S ×ˢ S).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext p
        simp only [U, Finset.mem_union, Finset.mem_filter, ne_eq]
        tauto
      · rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact (Finset.mem_filter.mp hp2).2 (Finset.mem_filter.mp hp1).2
    rw [Finset.card_product, hdiag] at htot
    cases hS : S.card with
    | zero => rw [hS] at htot; omega
    | succ m =>
      rw [hS] at htot
      simp only [Nat.add_sub_cancel]
      have : (m + 1) * (m + 1) = (m + 1) + (m + 1) * m := by ring
      omega
  let distRange : Finset ℤ := Finset.Icc (1 : ℤ) ((d * r ^ 2 : ℕ) : ℤ)
  have hdr_pos : 1 ≤ d * r ^ 2 := by nlinarith
  have hdistRange_card : distRange.card = d * r ^ 2 := by
    simp only [distRange, Int.card_Icc]
    omega
  have hU_maps : ∀ p ∈ U, sqNorm (p.2 - p.1) ∈ distRange := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1, hp2⟩, hne⟩ := hp
    rw [Finset.mem_Icc]
    constructor
    · have hex : ∃ i₀ : Fin d, p.2 i₀ - p.1 i₀ ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne
        funext i
        have := hall i
        linarith
      obtain ⟨i₀, hi₀⟩ := hex
      have h1 : (1 : ℤ) ≤ (p.2 i₀ - p.1 i₀) ^ 2 := by
        rcases lt_or_gt_of_ne hi₀ with h | h <;> nlinarith
      have hle : (p.2 i₀ - p.1 i₀) ^ 2 ≤ sqNorm (p.2 - p.1) :=
        Finset.single_le_sum (f := fun i => ((p.2 - p.1) i) ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ i₀)
      linarith
    · have hle : ∀ i : Fin d, (p.2 i - p.1 i) ^ 2 ≤ (r : ℤ) ^ 2 := by
        intro i
        have h1 := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp1).1) i
        have h2 := (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp2).1) i
        rw [Finset.mem_Ico] at h1 h2
        nlinarith
      calc ∑ i : Fin d, (p.2 i - p.1 i) ^ 2 ≤ ∑ _i : Fin d, (r : ℤ) ^ 2 :=
            Finset.sum_le_sum fun i _ => hle i
        _ = ((d * r ^ 2 : ℕ) : ℤ) := by simp [Finset.sum_const]
  have hdist_ne : distRange.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_refl _, by exact_mod_cast hdr_pos⟩⟩
  obtain ⟨D, hD_mem, hD⟩ := exists_fiber_mul_ge U distRange (fun p => sqNorm (p.2 - p.1)) hU_maps hdist_ne
  rw [hU_card, hdistRange_card] at hD
  let ED : Finset ((Fin d → ℤ) × (Fin d → ℤ)) := U.filter (fun p => sqNorm (p.2 - p.1) = D)
  -- Layered sphere set in `ℝ^{d+1}`
  let BigB : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun _ : Fin d => Finset.Ico (-(k : ℤ) * (r : ℤ)) ((k : ℤ) * (r : ℤ)))
  have hBigB_card : BigB.card = (2 * k * r) ^ d := by
    rw [Fintype.card_piFinset]
    have hcard_ico : (Finset.Ico (-(k : ℤ) * (r : ℤ)) ((k : ℤ) * (r : ℤ))).card = 2 * k * r := by
      rw [Int.card_Ico]
      have h2 : (k : ℤ) * (r : ℤ) - -(k : ℤ) * (r : ℤ) = ((2 * k * r : ℕ) : ℤ) := by
        push_cast; ring
      rw [h2, Int.toNat_natCast]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard_ico]
  let Q_int : Finset ((Fin d → ℤ) × Fin k) :=
    (BigB ×ˢ (Finset.univ : Finset (Fin k))).filter
      (fun p => sqNorm p.1 = R₀ + (p.2.val : ℤ) * ((p.2.val : ℤ) - 1) * D)
  have hQ_int_card : Q_int.card ≤ k * (2 * k * r) ^ d := by
    calc Q_int.card ≤ (BigB ×ˢ (Finset.univ : Finset (Fin k))).card := Finset.card_filter_le _ _
      _ = BigB.card * k := by simp
      _ = k * (2 * k * r) ^ d := by rw [hBigB_card, mul_comm]
  let embedPt : (Fin d → ℤ) × Fin k → (Fin (d + 1) → ℝ) :=
    fun p => Fin.snoc (fun i : Fin d => (p.1 i : ℝ)) (p.2.val : ℝ)
  have hembed_inj : Function.Injective embedPt := by
    intro p₁ p₂ heq
    have hlast : (p₁.2.val : ℝ) = (p₂.2.val : ℝ) := by
      have := congrFun heq (Fin.last d)
      simpa [embedPt, Fin.snoc_last] using this
    have h2 : p₁.2 = p₂.2 := Fin.ext (by exact_mod_cast hlast)
    have h1 : p₁.1 = p₂.1 := by
      funext i
      have := congrFun heq (Fin.castSucc i)
      simp only [embedPt, Fin.snoc_castSucc] at this
      exact_mod_cast this
    exact Prod.ext h1 h2
  let Q : Finset (Fin (d + 1) → ℝ) := Q_int.image embedPt
  have hQ_card : Q.card ≤ k * (2 * k * r) ^ d := by
    rw [Finset.card_image_of_injective _ hembed_inj]
    exact hQ_int_card
  -- Obtain a generic linear projection `π : ℝ^{d+1} → ℝ²`
  obtain ⟨t₀, hπ_inj, hπ_col⟩ := exists_generic_projection Q
  let π : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 2) := projPt (d + 1) t₀
  let P : Finset (EuclideanSpace ℝ (Fin 2)) := Q.image π
  have hP_card : P.card ≤ k * (2 * k * r) ^ d := by
    rw [Finset.card_image_of_injOn hπ_inj]
    exact hQ_card
  -- Prove no `k + 1` points of `P` are collinear
  have hno_kp1 : ∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k := by
    intro ℓ hℓ
    by_contra hgt
    push Not at hgt
    let T_Q : Finset (Fin (d + 1) → ℝ) := Q.filter (fun v => π v ∈ ℓ)
    have hTQ_card : k < T_Q.card := by
      have himg : T_Q.image π = P.filter (· ∈ ℓ) := by
        ext x
        simp only [T_Q, P, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨v, ⟨hvQ, hvℓ⟩, rfl⟩; exact ⟨⟨v, hvQ, rfl⟩, hvℓ⟩
        · rintro ⟨⟨v, hvQ, rfl⟩, hvℓ⟩; exact ⟨v, ⟨hvQ, hvℓ⟩, rfl⟩
      have hcard_eq : T_Q.card = (P.filter (· ∈ ℓ)).card := by
        rw [← himg]
        exact (Finset.card_image_of_injOn (hπ_inj.mono (Finset.filter_subset _ _))).symm
      omega
    -- Pull back `T_Q` to `T_int ⊆ Q_int`
    let T_int : Finset ((Fin d → ℤ) × Fin k) := Q_int.filter (fun p => π (embedPt p) ∈ ℓ)
    have hTint_card : k < T_int.card := by
      have himg : T_int.image embedPt = T_Q := by
        ext v
        simp only [T_int, T_Q, Q, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨p, ⟨hpQ, hpℓ⟩, rfl⟩; exact ⟨⟨p, hpQ, rfl⟩, hpℓ⟩
        · rintro ⟨⟨p, hpQ, rfl⟩, hpℓ⟩; exact ⟨p, ⟨hpQ, hpℓ⟩, rfl⟩
      rw [← himg, Finset.card_image_of_injective _ hembed_inj] at hTQ_card
      exact hTQ_card
    -- By pigeonhole on `Prod.snd : T_int → Fin k`, two distinct points share a layer `j₀`
    have hnot_inj : ¬ Set.InjOn (Prod.snd : (Fin d → ℤ) × Fin k → Fin k) T_int := by
      intro hinj
      have hle : T_int.card ≤ k := by
        calc T_int.card = (T_int.image Prod.snd).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = k := by simp
      omega
    rw [Set.InjOn] at hnot_inj
    push Not at hnot_inj
    obtain ⟨a, haT, b, hbT, hab_layer, hab_ne⟩ := hnot_inj
    -- Pick a third distinct point `c ∈ T_int` (since `T_int.card ≥ k + 1 ≥ 4 ≥ 3`)
    have hcard_er : 0 < ((T_int.erase a).erase b).card := by
      have hb_er : b ∈ T_int.erase a := Finset.mem_erase.mpr ⟨hab_ne.symm, hbT⟩
      rw [Finset.card_erase_of_mem hb_er, Finset.card_erase_of_mem haT]
      omega
    obtain ⟨c, hc_er⟩ := Finset.card_pos.mp hcard_er
    have hcT : c ∈ T_int := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc_er)
    have hbc_ne : b ≠ c := (Finset.ne_of_mem_erase hc_er).symm
    have hac_ne : a ≠ c := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc_er)).symm
    -- All three points `embedPt a, embedPt b, embedPt c` are collinear in `ℝ^{d+1}`
    have haQ : embedPt a ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_filter.mp haT).1
    have hbQ : embedPt b ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_filter.mp hbT).1
    have hcQ : embedPt c ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_filter.mp hcT).1
    have hπab_ne : π (embedPt a) ≠ π (embedPt b) :=
      fun h => hab_ne (hembed_inj (hπ_inj haQ hbQ h))
    have hdet := det_eq_zero_of_mem_line hℓ hπab_ne
      (Finset.mem_filter.mp haT).2 (Finset.mem_filter.mp hbT).2 (Finset.mem_filter.mp hcT).2
    have heab_ne : embedPt a ≠ embedPt b := fun h => hab_ne (hembed_inj h)
    obtain ⟨tc, htc⟩ := (hπ_col (embedPt a) haQ (embedPt b) hbQ (embedPt c) hcQ heab_ne).mp hdet
    -- Since `a.2 = b.2`, `c.2 = a.2` as well!
    have hc_layer : c.2 = a.2 := by
      have hlast := congrFun htc (Fin.last d)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, embedPt, Fin.snoc_last, hab_layer] at hlast
      have hval : (c.2.val : ℝ) = (b.2.val : ℝ) := by linarith
      rw [hab_layer]
      exact Fin.ext (by exact_mod_cast hval)
    -- Therefore `a.1, b.1, c.1` are 3 distinct collinear points on the sphere of radius `R_{a.2}`!
    set u : Fin d → ℝ := fun i => (a.1 i : ℝ)
    set v : Fin d → ℝ := fun i => (b.1 i : ℝ) - (a.1 i : ℝ)
    have hv_ne : v ≠ 0 := by
      intro hv0
      apply hab_ne
      refine Prod.ext (funext fun i => ?_) hab_layer
      have := congrFun hv0 i
      simp only [v, Pi.zero_apply] at this
      have : (b.1 i : ℝ) = (a.1 i : ℝ) := by linarith
      exact_mod_cast this.symm
    have htc0 : tc ≠ 0 := by
      intro h0
      apply hac_ne
      apply hembed_inj
      rw [h0, zero_smul] at htc
      exact (sub_eq_zero.mp htc).symm
    have htc1 : tc ≠ 1 := by
      intro h1
      apply hbc_ne
      apply hembed_inj
      rw [h1, one_smul] at htc
      have : embedPt c = embedPt b := by
        funext i
        have := congrFun htc i
        simp only [Pi.sub_apply] at this
        linarith
      exact this.symm
    set R : ℝ := ((R₀ + (a.2.val : ℤ) * ((a.2.val : ℤ) - 1) * D : ℤ) : ℝ)
    have ha_norm : ∑ i : Fin d, (u i + 0 * v i) ^ 2 = R := by
      have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp haT).1).2
      simp only [zero_mul, add_zero, u, R]
      have hcast : ((sqNorm a.1 : ℤ) : ℝ) = ((R₀ + (a.2.val : ℤ) * ((a.2.val : ℤ) - 1) * D : ℤ) : ℝ) :=
        by exact_mod_cast hn
      simpa [sqNorm] using hcast
    have hb_norm : ∑ i : Fin d, (u i + 1 * v i) ^ 2 = R := by
      have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hbT).1).2
      rw [← hab_layer] at hn
      have hcast : ((sqNorm b.1 : ℤ) : ℝ) = R := congrArg Int.cast hn
      have heq_sum : ∑ i : Fin d, (u i + 1 * v i) ^ 2 = ∑ i : Fin d, (b.1 i : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_; simp only [u, v]; ring
      rw [heq_sum]
      simpa [sqNorm] using hcast
    have hc_norm : ∑ i : Fin d, (u i + tc * v i) ^ 2 = R := by
      have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hcT).1).2
      rw [hc_layer] at hn
      have hcast : ((sqNorm c.1 : ℤ) : ℝ) = R := congrArg Int.cast hn
      have heq_sum : ∑ i : Fin d, (u i + tc * v i) ^ 2 = ∑ i : Fin d, (c.1 i : ℝ) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hi := congrFun htc (Fin.castSucc i)
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, embedPt, Fin.snoc_castSucc] at hi
        have : u i + tc * v i = (c.1 i : ℝ) := by simp only [u, v]; linarith
        rw [this]
      rw [heq_sum]
      simpa [sqNorm] using hcast
    exact sphere_line_le_two R u v hv_ne (by norm_num) htc0.symm htc1.symm ha_norm hb_norm hc_norm
  -- Construct the `k`-point lines from `ED`
  let mkLine : (Fin d → ℤ) × (Fin d → ℤ) → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    fun p => lineThrough (π (embedPt (p.1, ⟨0, by omega⟩))) (π (embedPt (p.2, ⟨1, by omega⟩)))
  have hED_line : ∀ p ∈ ED,
      Module.finrank ℝ (mkLine p).direction = 1 ∧
      (∀ j : Fin k, embedPt (fun i => p.1 i + (j.val : ℤ) * (p.2 i - p.1 i), j) ∈ Q ∧
        π (embedPt (fun i => p.1 i + (j.val : ℤ) * (p.2 i - p.1 i), j)) ∈ mkLine p) ∧
      (P.filter (· ∈ mkLine p)).card = k := by
    intro p hp
    have hpU : p ∈ U := (Finset.mem_filter.mp hp).1
    have hpD : sqNorm (p.2 - p.1) = D := (Finset.mem_filter.mp hp).2
    have hp1S : p.1 ∈ S := (Finset.mem_product.mp (Finset.mem_filter.mp hpU).1).1
    have hp2S : p.2 ∈ S := (Finset.mem_product.mp (Finset.mem_filter.mp hpU).1).2
    have hp1B : p.1 ∈ B := (Finset.mem_filter.mp hp1S).1
    have hp2B : p.2 ∈ B := (Finset.mem_filter.mp hp2S).1
    have hnorm1 : sqNorm p.1 = R₀ := (Finset.mem_filter.mp hp1S).2
    have hnorm2 : sqNorm p.2 = R₀ := (Finset.mem_filter.mp hp2S).2
    have hcross : 2 * ∑ i : Fin d, p.1 i * (p.2 i - p.1 i) = -D := by
      have hpoint : ∀ i : Fin d,
          2 * (p.1 i * (p.2 i - p.1 i)) = (p.2 i) ^ 2 - (p.1 i) ^ 2 - (p.2 i - p.1 i) ^ 2 :=
        fun i => by ring
      rw [Finset.mul_sum]
      simp_rw [hpoint, Finset.sum_sub_distrib]
      change sqNorm p.2 - sqNorm p.1 - sqNorm (p.2 - p.1) = -D
      rw [hnorm1, hnorm2, hpD]
      ring
    have hpt_mem_Q : ∀ j : Fin k,
        embedPt (fun i => p.1 i + (j.val : ℤ) * (p.2 i - p.1 i), j) ∈ Q := by
      intro j
      refine Finset.mem_image.mpr ⟨(fun i => p.1 i + (j.val : ℤ) * (p.2 i - p.1 i), j), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Fintype.mem_piFinset.mpr fun i => ?_, Finset.mem_univ _⟩, ?_⟩
      · rw [Finset.mem_Ico]
        have h1 := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp hp1B) i)
        have h2 := Finset.mem_Ico.mp ((Fintype.mem_piFinset.mp hp2B) i)
        have hj0 : (0 : ℤ) ≤ (j.val : ℤ) := Nat.cast_nonneg _
        have hjk : (j.val : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast j.isLt
        constructor <;> nlinarith
      · dsimp [sqNorm]
        have hpoint : ∀ i : Fin d,
            (p.1 i + (j.val : ℤ) * (p.2 i - p.1 i)) ^ 2 =
            (p.1 i) ^ 2 + (j.val : ℤ) * (2 * (p.1 i * (p.2 i - p.1 i))) +
            (j.val : ℤ) ^ 2 * (p.2 i - p.1 i) ^ 2 := fun i => by ring
        simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]
        change sqNorm p.1 + (j.val : ℤ) * (2 * ∑ i : Fin d, p.1 i * (p.2 i - p.1 i)) +
          (j.val : ℤ) ^ 2 * sqNorm (p.2 - p.1) = R₀ + (j.val : ℤ) * ((j.val : ℤ) - 1) * D
        rw [hnorm1, hcross, hpD]
        ring
    have hp0_eq : (fun i => p.1 i + ((⟨0, by omega⟩ : Fin k).val : ℤ) * (p.2 i - p.1 i)) = p.1 := by
      funext i; simp
    have hp1_eq : (fun i => p.1 i + ((⟨1, by omega⟩ : Fin k).val : ℤ) * (p.2 i - p.1 i)) = p.2 := by
      funext i; simp
    have h0Q : embedPt (p.1, ⟨0, by omega⟩) ∈ Q := by simpa [hp0_eq] using hpt_mem_Q ⟨0, by omega⟩
    have h1Q : embedPt (p.2, ⟨1, by omega⟩) ∈ Q := by simpa [hp1_eq] using hpt_mem_Q ⟨1, by omega⟩
    have h01_ne : embedPt (p.1, ⟨0, by omega⟩) ≠ embedPt (p.2, ⟨1, by omega⟩) := by
      intro heq
      have := congrFun heq (Fin.last d)
      simp [embedPt, Fin.snoc_last] at this
    have hπ01_ne : π (embedPt (p.1, ⟨0, by omega⟩)) ≠ π (embedPt (p.2, ⟨1, by omega⟩)) :=
      fun h => h01_ne (hπ_inj h0Q h1Q h)
    have hdim : Module.finrank ℝ (mkLine p).direction = 1 := lineThrough_finrank hπ01_ne
    have hmem_line : ∀ j : Fin k,
        π (embedPt (fun i => p.1 i + (j.val : ℤ) * (p.2 i - p.1 i), j)) ∈ mkLine p := by
      intro j
      apply mem_lineThrough_of_det hπ01_ne
      apply (hπ_col _ h0Q _ h1Q _ (hpt_mem_Q j) h01_ne).mpr
      refine ⟨(j.val : ℝ), ?_⟩
      funext idx
      refine Fin.lastCases ?_ (fun i => ?_) idx
      · simp [embedPt, Fin.snoc_last]
      · simp [embedPt, Fin.snoc_castSucc]
    have hcard_ge : k ≤ (P.filter (· ∈ mkLine p)).card := by
      let f : Fin k → EuclideanSpace ℝ (Fin 2) :=
        fun j => π (embedPt (fun i => p.1 i + (j.val : ℤ) * (p.2 i - p.1 i), j))
      have hf_inj : Function.Injective f := by
        intro j₁ j₂ heq
        have h1 := hπ_inj (hpt_mem_Q j₁) (hpt_mem_Q j₂) heq
        have h2 := congrFun h1 (Fin.last d)
        simp only [embedPt, Fin.snoc_last] at h2
        exact Fin.ext (by exact_mod_cast h2)
      have hsub : (Finset.univ : Finset (Fin k)).image f ⊆ P.filter (· ∈ mkLine p) := by
        intro x hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (hpt_mem_Q j), hmem_line j⟩
      calc k = (Finset.univ : Finset (Fin k)).card := by simp
        _ = ((Finset.univ : Finset (Fin k)).image f).card := (Finset.card_image_of_injective _ hf_inj).symm
        _ ≤ (P.filter (· ∈ mkLine p)).card := Finset.card_le_card hsub
    exact ⟨hdim, fun j => ⟨hpt_mem_Q j, hmem_line j⟩, le_antisymm (hno_kp1 _ hdim) hcard_ge⟩
  -- Prove `mkLine` is injective on `ED`
  have hmkLine_inj : Set.InjOn mkLine (ED : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 := hED_line p₁ hp₁
    have h2 := hED_line p₂ hp₂
    have h01_eq : (fun i => p₁.1 i + ((⟨0, by omega⟩ : Fin k).val : ℤ) * (p₁.2 i - p₁.1 i)) = p₁.1 := by
      funext i; simp
    have h11_eq : (fun i => p₁.1 i + ((⟨1, by omega⟩ : Fin k).val : ℤ) * (p₁.2 i - p₁.1 i)) = p₁.2 := by
      funext i; simp
    have h02_eq : (fun i => p₂.1 i + ((⟨0, by omega⟩ : Fin k).val : ℤ) * (p₂.2 i - p₂.1 i)) = p₂.1 := by
      funext i; simp
    have h12_eq : (fun i => p₂.1 i + ((⟨1, by omega⟩ : Fin k).val : ℤ) * (p₂.2 i - p₂.1 i)) = p₂.2 := by
      funext i; simp
    have haQ : embedPt (p₁.1, ⟨0, by omega⟩) ∈ Q := by simpa [h01_eq] using (h1.2.1 ⟨0, by omega⟩).1
    have hbQ : embedPt (p₁.2, ⟨1, by omega⟩) ∈ Q := by simpa [h11_eq] using (h1.2.1 ⟨1, by omega⟩).1
    have hcQ : embedPt (p₂.1, ⟨0, by omega⟩) ∈ Q := by simpa [h02_eq] using (h2.2.1 ⟨0, by omega⟩).1
    have hdQ : embedPt (p₂.2, ⟨1, by omega⟩) ∈ Q := by simpa [h12_eq] using (h2.2.1 ⟨1, by omega⟩).1
    have hab_ne : embedPt (p₁.1, ⟨0, by omega⟩) ≠ embedPt (p₁.2, ⟨1, by omega⟩) := by
      intro h; have := congrFun h (Fin.last d); simp [embedPt, Fin.snoc_last] at this
    have hπab_ne : π (embedPt (p₁.1, ⟨0, by omega⟩)) ≠ π (embedPt (p₁.2, ⟨1, by omega⟩)) :=
      fun h => hab_ne (hπ_inj haQ hbQ h)
    -- `p₂.1` at layer 0 lies on `mkLine p₁`
    have hc_mem : π (embedPt (p₂.1, ⟨0, by omega⟩)) ∈ mkLine p₁ := by
      rw [heq]; exact left_mem_lineThrough _ _
    have hdet_c := det_eq_zero_of_mem_line h1.1 hπab_ne
      (left_mem_lineThrough _ _) (right_mem_lineThrough _ _) hc_mem
    obtain ⟨tc, htc⟩ := (hπ_col _ haQ _ hbQ _ hcQ hab_ne).mp hdet_c
    have htc0 : tc = 0 := by
      have := congrFun htc (Fin.last d)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, embedPt, Fin.snoc_last,
        Nat.cast_zero, Nat.cast_one] at this
      linarith
    have hp1_eq : p₁.1 = p₂.1 := by
      funext i
      have := congrFun htc (Fin.castSucc i)
      simp only [htc0, zero_smul, Pi.sub_apply, Pi.zero_apply, embedPt, Fin.snoc_castSucc] at this
      have : (p₂.1 i : ℝ) = (p₁.1 i : ℝ) := by linarith
      exact_mod_cast this.symm
    -- `p₂.2` at layer 1 lies on `mkLine p₁`
    have hd_mem : π (embedPt (p₂.2, ⟨1, by omega⟩)) ∈ mkLine p₁ := by
      rw [heq]; exact right_mem_lineThrough _ _
    have hdet_d := det_eq_zero_of_mem_line h1.1 hπab_ne
      (left_mem_lineThrough _ _) (right_mem_lineThrough _ _) hd_mem
    obtain ⟨td, htd⟩ := (hπ_col _ haQ _ hbQ _ hdQ hab_ne).mp hdet_d
    have htd1 : td = 1 := by
      have := congrFun htd (Fin.last d)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, embedPt, Fin.snoc_last,
        Nat.cast_zero, Nat.cast_one] at this
      linarith
    have hp2_eq : p₁.2 = p₂.2 := by
      funext i
      have := congrFun htd (Fin.castSucc i)
      simp only [htd1, one_smul, Pi.sub_apply, embedPt, Fin.snoc_castSucc] at this
      have : (p₂.2 i : ℝ) = (p₁.2 i : ℝ) := by linarith
      exact_mod_cast this.symm
    exact Prod.ext hp1_eq hp2_eq
  let L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := ED.image mkLine
  refine ⟨P, L, hP_card, hno_kp1, ?_, S.card, hR₀, ?_⟩
  · intro ℓ hℓ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hℓ
    exact ⟨(hED_line p hp).1, (hED_line p hp).2.2⟩
  · rw [Finset.card_image_of_injOn hmkLine_inj]
    exact hD

/-- Elementary bound `x^3 ≤ 6 * exp x` for `x ≥ 0`. -/
private lemma cube_le_six_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ 6 * Real.exp x := by
  have h4 := Real.sum_le_exp_of_nonneg hx 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero] at h4
  simp only [Nat.factorial] at h4
  have h0 : 0 ≤ 1 + x + x ^ 2 / 2 := by positivity
  nlinarith

set_option maxHeartbeats 800000 in
/-- **Solymosi–Stojaković (2013) Lower Bound (`588.lean`: `solymosi_stojakovic`)**:
for every `k ≥ 4`, there exist explicit constants `c > 0` and `C > 0` such that for all
sufficiently large `n`, there exist `n` points `P ⊆ ℝ²` with **no `k + 1` collinear** and a
family `L` of distinct 1-dimensional lines each containing **exactly `k`** points of `P` with
`c * n ^ (2 - C / √(log n)) ≤ |L|`. -/
theorem ppl022_solymosi_stojakovic (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ (P : Finset (EuclideanSpace ℝ (Fin 2)))
          (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
          P.card = n ∧
          (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
            Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k) ∧
          (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = k) ∧
          c * (n : ℝ) ^ (2 - C / Real.sqrt (Real.log (n : ℝ))) ≤ (L.card : ℝ) := by
  set c : ℝ := 1 / (48 * (k : ℝ) ^ 2)
  set C : ℝ := 13 + 2 * Real.log (4 * (k : ℝ))
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hc_pos : 0 < c := by positivity
  have hlog4k_pos : 0 < Real.log (4 * (k : ℝ)) := by
    apply Real.log_pos
    have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hC_pos : 0 < C := by linarith
  refine ⟨c, hc_pos, C, hC_pos, ?_⟩
  -- Pick a clean explicit threshold `L₀` on `√(log n)`
  set M : ℝ := max 4 (4 * Real.log (4 * (k : ℝ)) + 8)
  have hM_ge4 : 4 ≤ M := le_max_left _ _
  have hM_ge_log : 4 * Real.log (4 * (k : ℝ)) + 8 ≤ M := le_max_right _ _
  rw [Filter.eventually_atTop]
  refine ⟨Nat.ceil (Real.exp (M ^ 2)) + 2, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_ge_exp : Real.exp (M ^ 2) ≤ (n : ℝ) := by
    have h1 : (Nat.ceil (Real.exp (M ^ 2)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show Nat.ceil (Real.exp (M ^ 2)) ≤ n by omega)
    exact (Nat.le_ceil _).trans h1
  set L : ℝ := Real.log (n : ℝ)
  have hL_ge : M ^ 2 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hn_ge_exp
    rwa [Real.log_exp] at this
  have hsqrtL_ge : M ≤ Real.sqrt L := by
    have hM0 : 0 ≤ M := by linarith
    rw [← Real.sqrt_sq hM0]
    exact Real.sqrt_le_sqrt hL_ge
  have hsqrtL_pos : 0 < Real.sqrt L := by linarith
  have hL_pos : 0 < L := by nlinarith
  -- Choose `d = ⌊√L⌋` and `r = ⌊(n / k)^(1/d) / (2k)⌋`
  let d : ℕ := Nat.floor (Real.sqrt L)
  have hd_le : (d : ℝ) ≤ Real.sqrt L := Nat.floor_le (le_of_lt hsqrtL_pos)
  have hd_gt : Real.sqrt L - 1 < (d : ℝ) := by linarith [Nat.lt_floor_add_one (Real.sqrt L)]
  have hd_ge_half : Real.sqrt L / 2 ≤ (d : ℝ) := by linarith
  have hd_ge2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ (d : ℝ) := by linarith
    exact_mod_cast this
  have hd_pos_r : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  set x : ℝ := ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) / (2 * (k : ℝ))
  have hnk_pos : 0 < (n : ℝ) / (k : ℝ) := div_pos hn_pos hk_pos
  have hx_ge2 : 2 ≤ x := by
    have hlog_k_le : Real.log (k : ℝ) ≤ Real.log (4 * (k : ℝ)) :=
      Real.log_le_log hk_pos (by linarith)
    have hlog_ratio : Real.log ((n : ℝ) / (k : ℝ)) / (d : ℝ) ≥ Real.log (4 * (k : ℝ)) := by
      rw [ge_iff_le, le_div_iff₀ hd_pos_r, Real.log_div (ne_of_gt hn_pos) (ne_of_gt hk_pos)]
      have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL_pos)
      have h1 : Real.log (4 * (k : ℝ)) * Real.sqrt L + Real.log (k : ℝ) ≤
          (Real.log (4 * (k : ℝ)) + 1) * Real.sqrt L := by nlinarith
      have h2 : Real.log (4 * (k : ℝ)) + 1 ≤ Real.sqrt L := by linarith
      nlinarith
    have hexp_ge : 4 * (k : ℝ) ≤ ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) := by
      rw [Real.rpow_def_of_pos hnk_pos]
      have h1 : 4 * (k : ℝ) = Real.exp (Real.log (4 * (k : ℝ))) := (Real.exp_log (by positivity)).symm
      rw [h1]
      apply Real.exp_le_exp.mpr
      have : Real.log ((n : ℝ) / (k : ℝ)) * (1 / (d : ℝ)) = Real.log ((n : ℝ) / (k : ℝ)) / (d : ℝ) := by ring
      linarith
    simp only [x]
    rw [le_div_iff₀ (by positivity)]
    linarith
  let r : ℕ := Nat.floor x
  have hr_ge2 : 2 ≤ r := by
    have : (2 : ℝ) ≤ x := hx_ge2
    exact Nat.le_floor this
  have hr_le : (r : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hr_ge_half : x / 2 ≤ (r : ℝ) := by linarith [Nat.lt_floor_add_one x]
  have hr_pos_r : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Run the finite layered-sphere construction with `(k, d, r)`
  obtain ⟨P₀, L_lines, hP₀_le, hno_kp1, hL_lines, S_card, hS_lb, hED_lb⟩ :=
    layered_sphere_construction k d r (by omega) (by omega) (by omega)
  -- Check `P₀.card ≤ n`
  have hP₀_le_n : P₀.card ≤ n := by
    have h2kr : (2 * (k : ℝ) * (r : ℝ)) ^ d ≤ (n : ℝ) / (k : ℝ) := by
      have hbase : 2 * (k : ℝ) * (r : ℝ) ≤ ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hr_le (show (0 : ℝ) ≤ 2 * (k : ℝ) by positivity)
        simp only [x] at this
        rwa [mul_div_cancel₀ _ (by positivity)] at this
      calc (2 * (k : ℝ) * (r : ℝ)) ^ d
          ≤ (((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ))) ^ d :=
            pow_le_pow_left₀ (by positivity) hbase d
        _ = (((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ))) ^ (d : ℝ) := (Real.rpow_natCast _ d).symm
        _ = (n : ℝ) / (k : ℝ) := by
            rw [← Real.rpow_mul (le_of_lt hnk_pos), one_div_mul_cancel (ne_of_gt hd_pos_r), Real.rpow_one]
    have hreal : ((k * (2 * k * r) ^ d : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      have := mul_le_mul_of_nonneg_left h2kr (le_of_lt hk_pos)
      rwa [mul_div_cancel₀ _ (ne_of_gt hk_pos)] at this
    exact hP₀_le.trans (by exact_mod_cast hreal)
  -- Pad `P₀` to exact size `n`
  obtain ⟨P, hP_card, hP_nok, hP_L⟩ := pad_point_set (by omega) P₀ L_lines hP₀_le_n hno_kp1 hL_lines
  refine ⟨P, L_lines, hP_card, hP_nok, hP_L, ?_⟩
  -- Lower bound `r^d` and upper bound `r`
  have hrd_lb : (n : ℝ) / ((k : ℝ) * (4 * (k : ℝ)) ^ d) ≤ (r : ℝ) ^ d := by
    have hbase : ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) / (4 * (k : ℝ)) ≤ (r : ℝ) := by
      have : x / 2 = ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) / (4 * (k : ℝ)) := by simp only [x]; ring
      linarith
    have hpow_eq : (((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ))) ^ d = (n : ℝ) / (k : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnk_pos),
        one_div_mul_cancel (ne_of_gt hd_pos_r), Real.rpow_one]
    calc (n : ℝ) / ((k : ℝ) * (4 * (k : ℝ)) ^ d)
        = (((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) / (4 * (k : ℝ))) ^ d := by
          rw [div_pow, hpow_eq, div_div]
      _ ≤ (r : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hbase d
  have hr_ub : (r : ℝ) ≤ (n : ℝ) ^ (1 / (d : ℝ)) := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have h1 : (n : ℝ) / (k : ℝ) ≤ (n : ℝ) := div_le_self (le_of_lt hn_pos) hk1
    have h2 : ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) ≤ (n : ℝ) ^ (1 / (d : ℝ)) :=
      Real.rpow_le_rpow (le_of_lt hnk_pos) h1 (by positivity)
    have h3 : x ≤ ((n : ℝ) / (k : ℝ)) ^ (1 / (d : ℝ)) := by
      simp only [x]
      exact div_le_self (by positivity) (by linarith)
    linarith
  have hr_pow_exp : ∀ a : ℝ, 0 ≤ a → (r : ℝ) ^ a ≤ Real.exp (2 * a * Real.sqrt L) := by
    intro a ha
    calc (r : ℝ) ^ a ≤ ((n : ℝ) ^ (1 / (d : ℝ))) ^ a := Real.rpow_le_rpow (le_of_lt hr_pos_r) hr_ub ha
      _ = Real.exp (L * (a / (d : ℝ))) := by
          rw [← Real.rpow_mul (le_of_lt hn_pos), Real.rpow_def_of_pos hn_pos]
          congr 1; ring
      _ ≤ Real.exp (2 * a * Real.sqrt L) := by
          apply Real.exp_le_exp.mpr
          have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL_pos)
          have hdiv : L / (d : ℝ) ≤ 2 * Real.sqrt L := by
            rw [div_le_iff₀ hd_pos_r]
            nlinarith
          have : L * (a / (d : ℝ)) = a * (L / (d : ℝ)) := by ring
          nlinarith
  -- Show `S_card ≥ 2` so `S_card * (S_card - 1) ≥ S_card^2 / 2`
  have hS_ge2 : 2 ≤ S_card := by
    have hS_r : ((r : ℝ) ^ d) / ((d : ℝ) * (r : ℝ) ^ 2 + 1) ≤ (S_card : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have hcast : ((r ^ d : ℕ) : ℝ) ≤ (((d * r ^ 2 + 1) * S_card : ℕ) : ℝ) := by exact_mod_cast hS_lb
      push_cast at hcast
      linarith
    have hdenom_le : (d : ℝ) * (r : ℝ) ^ 2 + 1 ≤ 2 * Real.exp (5 * Real.sqrt L) := by
      have hd_exp : (d : ℝ) ≤ Real.exp (Real.sqrt L) :=
        hd_le.trans (by linarith [Real.add_one_le_exp (Real.sqrt L)])
      have hr2_exp : (r : ℝ) ^ 2 ≤ Real.exp (4 * Real.sqrt L) := by
        calc (r : ℝ) ^ 2 = (r : ℝ) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast (r : ℝ) 2).symm
          _ ≤ Real.exp (2 * 2 * Real.sqrt L) := hr_pow_exp 2 (by norm_num)
          _ = Real.exp (4 * Real.sqrt L) := by ring_nf
      have hmul : (d : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp (5 * Real.sqrt L) := by
        calc (d : ℝ) * (r : ℝ) ^ 2 ≤ Real.exp (Real.sqrt L) * Real.exp (4 * Real.sqrt L) :=
              mul_le_mul hd_exp hr2_exp (by positivity) (by positivity)
          _ = Real.exp (5 * Real.sqrt L) := by rw [← Real.exp_add]; ring_nf
      have hexp1 : 1 ≤ Real.exp (5 * Real.sqrt L) := Real.one_le_exp (by positivity)
      linarith
    have h4kd : (k : ℝ) * (4 * (k : ℝ)) ^ d ≤ Real.exp ((Real.log (4 * (k : ℝ)) + 1) * Real.sqrt L) := by
      have h1 : (4 * (k : ℝ)) ^ d = Real.exp ((d : ℝ) * Real.log (4 * (k : ℝ))) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]; ring_nf
      have h2 : (k : ℝ) ≤ Real.exp (Real.log (4 * (k : ℝ))) := by
        rw [Real.exp_log (by positivity)]; linarith
      calc (k : ℝ) * (4 * (k : ℝ)) ^ d
          ≤ Real.exp (Real.log (4 * (k : ℝ))) * Real.exp ((d : ℝ) * Real.log (4 * (k : ℝ))) :=
            mul_le_mul h2 (le_of_eq h1) (by positivity) (by positivity)
        _ = Real.exp (((d : ℝ) + 1) * Real.log (4 * (k : ℝ))) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp ((Real.log (4 * (k : ℝ)) + 1) * Real.sqrt L) := by
            apply Real.exp_le_exp.mpr
            have : Real.log (4 * (k : ℝ)) ≤ Real.sqrt L := by linarith
            nlinarith
    have h4_le_n : 4 * (Real.exp ((Real.log (4 * (k : ℝ)) + 1) * Real.sqrt L) *
        Real.exp (5 * Real.sqrt L)) ≤ (n : ℝ) := by
      have hn_eq : (n : ℝ) = Real.exp L := (Real.exp_log hn_pos).symm
      rw [hn_eq, ← Real.exp_add]
      have h4_exp : (4 : ℝ) ≤ Real.exp (2 * Real.sqrt L) := by
        have : 2 * Real.sqrt L ≥ 8 := by linarith
        linarith [Real.add_one_le_exp (2 * Real.sqrt L)]
      calc 4 * Real.exp ((Real.log (4 * (k : ℝ)) + 1) * Real.sqrt L + 5 * Real.sqrt L)
          ≤ Real.exp (2 * Real.sqrt L) *
              Real.exp ((Real.log (4 * (k : ℝ)) + 1) * Real.sqrt L + 5 * Real.sqrt L) :=
            mul_le_mul_of_nonneg_right h4_exp (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((Real.log (4 * (k : ℝ)) + 8) * Real.sqrt L) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp L := by
            apply Real.exp_le_exp.mpr
            have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL_pos)
            have : Real.log (4 * (k : ℝ)) + 8 ≤ Real.sqrt L := by linarith
            nlinarith
    have h2_le_S : (2 : ℝ) ≤ (S_card : ℝ) := by
      have hnum : 2 * ((d : ℝ) * (r : ℝ) ^ 2 + 1) ≤ (r : ℝ) ^ d := by
        have hstep : 2 * ((d : ℝ) * (r : ℝ) ^ 2 + 1) * ((k : ℝ) * (4 * (k : ℝ)) ^ d) ≤ (n : ℝ) := by
          have hmul := mul_le_mul hdenom_le h4kd (by positivity) (by positivity)
          nlinarith
        have hdiv : 2 * ((d : ℝ) * (r : ℝ) ^ 2 + 1) ≤ (n : ℝ) / ((k : ℝ) * (4 * (k : ℝ)) ^ d) :=
          (le_div_iff₀ (by positivity)).mpr hstep
        linarith
      have : 2 ≤ (r : ℝ) ^ d / ((d : ℝ) * (r : ℝ) ^ 2 + 1) :=
        (le_div_iff₀ (by positivity)).mpr hnum
      linarith
    exact_mod_cast h2_le_S
  -- Combine `hED_lb`, `hS_lb`, `hrd_lb`, and exponential upper bounds on denominator
  have hS_quad : (S_card : ℝ) ^ 2 ≤ 2 * ((S_card : ℝ) * ((S_card - 1 : ℕ) : ℝ)) := by
    have hnat : S_card * S_card ≤ 2 * (S_card * (S_card - 1)) := by
      cases hS : S_card with
      | zero => omega
      | succ m =>
        simp only [Nat.add_sub_cancel]
        have hm1 : 1 ≤ m := by omega
        nlinarith
    have hcast : ((S_card * S_card : ℕ) : ℝ) ≤ ((2 * (S_card * (S_card - 1)) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hED_r : (S_card : ℝ) ^ 2 ≤ 2 * ((d : ℝ) * (r : ℝ) ^ 2) * (L_lines.card : ℝ) := by
    have h1 : ((S_card * (S_card - 1) : ℕ) : ℝ) ≤ ((d * r ^ 2 * L_lines.card : ℕ) : ℝ) := by
      exact_mod_cast hED_lb
    push_cast at h1
    nlinarith
  have hS_sq : ((r : ℝ) ^ d) ^ 2 ≤ ((d : ℝ) * (r : ℝ) ^ 2 + 1) ^ 2 * (S_card : ℝ) ^ 2 := by
    have h1 : (r : ℝ) ^ d ≤ ((d : ℝ) * (r : ℝ) ^ 2 + 1) * (S_card : ℝ) := by
      have hc : ((r ^ d : ℕ) : ℝ) ≤ (((d * r ^ 2 + 1) * S_card : ℕ) : ℝ) := by exact_mod_cast hS_lb
      push_cast at hc; exact hc
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    linarith
  have hdr2_ge1 : (1 : ℝ) ≤ (d : ℝ) * (r : ℝ) ^ 2 := by
    have : 1 ≤ d * r ^ 2 := by nlinarith
    exact_mod_cast this
  have hdenom_comb :
      ((r : ℝ) ^ d) ^ 2 ≤ 8 * (d : ℝ) ^ 3 * (r : ℝ) ^ 6 * (L_lines.card : ℝ) := by
    have h1 : ((d : ℝ) * (r : ℝ) ^ 2 + 1) ^ 2 ≤ 4 * ((d : ℝ) * (r : ℝ) ^ 2) ^ 2 := by nlinarith
    have h2 : ((d : ℝ) * (r : ℝ) ^ 2 + 1) ^ 2 * (S_card : ℝ) ^ 2 ≤
        4 * ((d : ℝ) * (r : ℝ) ^ 2) ^ 2 * (2 * ((d : ℝ) * (r : ℝ) ^ 2) * (L_lines.card : ℝ)) :=
      mul_le_mul h1 hED_r (by positivity) (by positivity)
    linarith
  have hrd_sq : (n : ℝ) ^ 2 / ((k : ℝ) ^ 2 * (4 * (k : ℝ)) ^ (2 * d)) ≤ ((r : ℝ) ^ d) ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity) hrd_lb 2
    rw [div_pow, mul_pow, ← pow_mul] at hsq
    rwa [show d * 2 = 2 * d by ring] at hsq
  have hmain_div :
      (n : ℝ) ^ 2 ≤ 8 * (k : ℝ) ^ 2 * (d : ℝ) ^ 3 * (r : ℝ) ^ 6 * (4 * (k : ℝ)) ^ (2 * d) * (L_lines.card : ℝ) := by
    have h1 : (n : ℝ) ^ 2 / ((k : ℝ) ^ 2 * (4 * (k : ℝ)) ^ (2 * d)) ≤
        8 * (d : ℝ) ^ 3 * (r : ℝ) ^ 6 * (L_lines.card : ℝ) := hrd_sq.trans hdenom_comb
    have h2 := (div_le_iff₀ (by positivity)).mp h1
    linarith
  -- Bound the denominator factors by `48 * k^2 * exp (C * √L)`
  have hd3_bound : (d : ℝ) ^ 3 ≤ 6 * Real.exp (Real.sqrt L) :=
    (pow_le_pow_left₀ (by positivity) hd_le 3).trans (cube_le_six_mul_exp (le_of_lt hsqrtL_pos))
  have hr6_bound : (r : ℝ) ^ 6 ≤ Real.exp (12 * Real.sqrt L) := by
    calc (r : ℝ) ^ 6 = (r : ℝ) ^ ((6 : ℕ) : ℝ) := (Real.rpow_natCast (r : ℝ) 6).symm
      _ ≤ Real.exp (2 * 6 * Real.sqrt L) := hr_pow_exp 6 (by norm_num)
      _ = Real.exp (12 * Real.sqrt L) := by ring_nf
  have h4k_bound : (4 * (k : ℝ)) ^ (2 * d) ≤ Real.exp (2 * Real.log (4 * (k : ℝ)) * Real.sqrt L) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
    apply Real.exp_le_exp.mpr
    have hcast : ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) := by push_cast; ring
    rw [hcast]
    have hmul := mul_le_mul_of_nonneg_left hd_le (show (0 : ℝ) ≤ 2 * Real.log (4 * (k : ℝ)) by positivity)
    linarith
  have hfactor_bound :
      8 * (k : ℝ) ^ 2 * (d : ℝ) ^ 3 * (r : ℝ) ^ 6 * (4 * (k : ℝ)) ^ (2 * d) ≤
      48 * (k : ℝ) ^ 2 * Real.exp (C * Real.sqrt L) := by
    have hprod1 : (d : ℝ) ^ 3 * (r : ℝ) ^ 6 ≤ 6 * Real.exp (13 * Real.sqrt L) := by
      calc (d : ℝ) ^ 3 * (r : ℝ) ^ 6
          ≤ (6 * Real.exp (Real.sqrt L)) * Real.exp (12 * Real.sqrt L) :=
            mul_le_mul hd3_bound hr6_bound (by positivity) (by positivity)
        _ = 6 * Real.exp (13 * Real.sqrt L) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    have hprod2 : (d : ℝ) ^ 3 * (r : ℝ) ^ 6 * (4 * (k : ℝ)) ^ (2 * d) ≤
        6 * Real.exp (C * Real.sqrt L) := by
      calc (d : ℝ) ^ 3 * (r : ℝ) ^ 6 * (4 * (k : ℝ)) ^ (2 * d)
          ≤ (6 * Real.exp (13 * Real.sqrt L)) * Real.exp (2 * Real.log (4 * (k : ℝ)) * Real.sqrt L) :=
            mul_le_mul hprod1 h4k_bound (by positivity) (by positivity)
        _ = 6 * Real.exp (C * Real.sqrt L) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; simp only [C]; ring
    have hmul := mul_le_mul_of_nonneg_left hprod2 (show (0 : ℝ) ≤ 8 * (k : ℝ) ^ 2 by positivity)
    linarith
  -- Rewrite `n ^ (2 - C / √L) = n^2 / exp (C * √L)` and conclude
  have hrpow_eq : (n : ℝ) ^ (2 - C / Real.sqrt L) = (n : ℝ) ^ 2 / Real.exp (C * Real.sqrt L) := by
    rw [Real.rpow_def_of_pos hn_pos]
    have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL_pos)
    have hexp_eq : L * (2 - C / Real.sqrt L) = 2 * L - C * Real.sqrt L := by
      have h1 : L / Real.sqrt L = Real.sqrt L := by
        rw [div_eq_iff (ne_of_gt hsqrtL_pos)]; linarith
      calc L * (2 - C / Real.sqrt L) = 2 * L - C * (L / Real.sqrt L) := by ring
        _ = 2 * L - C * Real.sqrt L := by rw [h1]
    rw [hexp_eq, Real.exp_sub, show 2 * L = L * 2 by ring, Real.exp_mul, Real.exp_log hn_pos,
      Real.rpow_two]
  rw [hrpow_eq]
  simp only [c]
  have h1 : (n : ℝ) ^ 2 ≤ 48 * (k : ℝ) ^ 2 * Real.exp (C * Real.sqrt L) * (L_lines.card : ℝ) := by
    have := mul_le_mul_of_nonneg_right hfactor_bound (Nat.cast_nonneg L_lines.card)
    linarith
  have hden_pos : 0 < 48 * (k : ℝ) ^ 2 * Real.exp (C * Real.sqrt L) := by positivity
  have h2 : (n : ℝ) ^ 2 / (48 * (k : ℝ) ^ 2 * Real.exp (C * Real.sqrt L)) ≤ (L_lines.card : ℝ) :=
    (div_le_iff₀ hden_pos).mpr (by linarith)
  have h3 : 1 / (48 * (k : ℝ) ^ 2) * ((n : ℝ) ^ 2 / Real.exp (C * Real.sqrt L)) =
      (n : ℝ) ^ 2 / (48 * (k : ℝ) ^ 2 * Real.exp (C * Real.sqrt L)) := by ring
  linarith

/-- **No Polynomial-Exponent Saving (`588.lean`: refutation of Erdős's `grunbaum_order` / any
`O(n^{2 - ε})` upper bound for `k ≥ 4`)**:
for every `k ≥ 4` and every `ε > 0`, for all sufficiently large `n`, there exist `n` points in
`ℝ²` with no `k + 1` collinear determining at least `n ^ (2 - ε)` distinct `k`-point lines. -/
theorem ppl022_not_poly_saving (k : ℕ) (hk : 4 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
        P.card = n ∧
        (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k) ∧
        (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = k) ∧
        (n : ℝ) ^ (2 - ε) ≤ (L.card : ℝ) := by
  obtain ⟨c, hc, C, hC, hev⟩ := ppl022_solymosi_stojakovic k hk
  rw [Filter.eventually_atTop] at hev ⊢
  obtain ⟨N₁, hN₁⟩ := hev
  -- Need `c * n ^ (2 - C / √(log n)) ≥ n ^ (2 - ε)`, i.e. `ε * log n ≥ C * √(log n) + log (1 / c)`
  set B : ℝ := max 1 ((C + |Real.log c| + 1) / ε)
  refine ⟨max N₁ (Nat.ceil (Real.exp (B ^ 2)) + 2), fun n hn => ?_⟩
  obtain ⟨P, L, hP, hnok, hL, hlb⟩ := hN₁ n ((le_max_left _ _).trans hn)
  refine ⟨P, L, hP, hnok, hL, ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hn_ge_exp : Real.exp (B ^ 2) ≤ (n : ℝ) := by
    have h1 : Nat.ceil (Real.exp (B ^ 2)) ≤ n := by
      have := (le_max_right N₁ _).trans hn; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  set logn : ℝ := Real.log (n : ℝ)
  have hlogn_ge : B ^ 2 ≤ logn := by
    have := Real.log_le_log (Real.exp_pos _) hn_ge_exp
    rwa [Real.log_exp] at this
  have hB_ge1 : 1 ≤ B := le_max_left _ _
  have hB_ge2 : (C + |Real.log c| + 1) / ε ≤ B := le_max_right _ _
  have hsqrt_ge : B ≤ Real.sqrt logn := by
    rw [← Real.sqrt_sq (show 0 ≤ B by linarith)]
    exact Real.sqrt_le_sqrt hlogn_ge
  have hsqrt_pos : 0 < Real.sqrt logn := by linarith
  have hlogn_pos : 0 < logn := by nlinarith
  have hsq : Real.sqrt logn * Real.sqrt logn = logn := Real.mul_self_sqrt (le_of_lt hlogn_pos)
  have hcmp : (n : ℝ) ^ (2 - ε) ≤ c * (n : ℝ) ^ (2 - C / Real.sqrt logn) := by
    rw [Real.rpow_def_of_pos hn_pos, Real.rpow_def_of_pos hn_pos,
      ← Real.exp_log hc, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlogc : -|Real.log c| ≤ Real.log c := neg_abs_le (Real.log c)
    have h1 : C + |Real.log c| + 1 ≤ ε * Real.sqrt logn := by
      have := (div_le_iff₀ hε).mp hB_ge2
      nlinarith
    have h2 : logn * (C / Real.sqrt logn) = C * Real.sqrt logn := by
      calc logn * (C / Real.sqrt logn)
          = (Real.sqrt logn * Real.sqrt logn) * (C / Real.sqrt logn) := by rw [hsq]
        _ = C * Real.sqrt logn := by field_simp [ne_of_gt hsqrt_pos]
    have h3 : |Real.log c| ≤ |Real.log c| * Real.sqrt logn := by
      have : 1 ≤ Real.sqrt logn := by linarith
      nlinarith [abs_nonneg (Real.log c)]
    nlinarith
  exact hcmp.trans hlb

/-- **Grünbaum (1976) Lower Bound (`588.lean`: `grunbaum`)**:
for every `k ≥ 4`, for all sufficiently large `n`, there exist `n` points in `ℝ²` with no `k + 1`
collinear determining at least `n ^ (1 + 1 / (k - 2))` distinct `k`-point lines. -/
theorem ppl022_grunbaum_lower (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
        P.card = n ∧
        (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k) ∧
        (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = k) ∧
        (n : ℝ) ^ (1 + 1 / ((k : ℝ) - 2)) ≤ (L.card : ℝ) := by
  have hk_r : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hε : 0 < 1 - 1 / ((k : ℝ) - 2) := by
    have h1 : (2 : ℝ) ≤ (k : ℝ) - 2 := by linarith
    have h2 : 1 / ((k : ℝ) - 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h1
    linarith
  have hev := ppl022_not_poly_saving k hk (1 - 1 / ((k : ℝ) - 2)) hε
  filter_upwards [hev] with n hn
  obtain ⟨P, L, hP, hnok, hL, hlb⟩ := hn
  refine ⟨P, L, hP, hnok, hL, ?_⟩
  rwa [show (2 : ℝ) - (1 - 1 / ((k : ℝ) - 2)) = 1 + 1 / ((k : ℝ) - 2) by ring] at hlb

/-- **Kárteszi (1963) Lower Bound (`588.lean`: `karteszi`)**:
for every `k ≥ 4`, for all sufficiently large `n`, there exist `n` points in `ℝ²` with no `k + 1`
collinear determining at least `n * log n` distinct `k`-point lines. -/
theorem ppl022_karteszi_lower (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (P : Finset (EuclideanSpace ℝ (Fin 2)))
        (L : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))),
        P.card = n ∧
        (∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
          Module.finrank ℝ ℓ.direction = 1 → (P.filter (· ∈ ℓ)).card ≤ k) ∧
        (∀ ℓ ∈ L, Module.finrank ℝ ℓ.direction = 1 ∧ (P.filter (· ∈ ℓ)).card = k) ∧
        (n : ℝ) * Real.log (n : ℝ) ≤ (L.card : ℝ) := by
  have hev := ppl022_not_poly_saving k hk (1 / 2) (by norm_num)
  filter_upwards [hev, Filter.eventually_ge_atTop 4] with n hn hn4
  obtain ⟨P, L, hP, hnok, hL, hlb⟩ := hn
  refine ⟨P, L, hP, hnok, hL, ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_le : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have h1 : Real.log (Real.sqrt (n : ℝ)) ≤ Real.sqrt (n : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have h2 : Real.log (n : ℝ) = 2 * Real.log (Real.sqrt (n : ℝ)) := by
      have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
      calc Real.log (n : ℝ) = Real.log (Real.sqrt (n : ℝ) ^ 2) := by rw [hsq]
        _ = 2 * Real.log (Real.sqrt (n : ℝ)) := by rw [Real.log_pow]; norm_num
    have h3 : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow _).symm
    have hhalf_pos : 0 < Real.sqrt (n : ℝ) / 2 := by positivity
    have h5 : Real.log (Real.sqrt (n : ℝ) / 2) ≤ Real.sqrt (n : ℝ) / 2 - 1 :=
      Real.log_le_sub_one_of_pos hhalf_pos
    have h6 : Real.log (Real.sqrt (n : ℝ) / 2) = Real.log (Real.sqrt (n : ℝ)) - Real.log 2 :=
      Real.log_div (ne_of_gt hsqrt_pos) (by norm_num)
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  have hmul : (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) ^ (2 - (1 : ℝ) / 2) := by
    calc (n : ℝ) * Real.log (n : ℝ)
        ≤ (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hn_pos)
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (2 - (1 : ℝ) / 2) := by rw [← Real.rpow_add hn_pos]; norm_num
  exact hmul.trans hlb

/-! ### Section 6: Structural Barrier Theorems -/

/-- **Barrier 1 (Finite-Field / Linear-Space Barrier)**:
for any finite field `F` of cardinality `k` and any dimension `d ≥ 1`, the affine space `Fin d → F`
has `k^d` points, **no `k + 1` points collinear** (every 1-dimensional affine line has at most `k`
points), and a family `L` of distinct 1-dimensional affine lines each containing **exactly `k`**
points that **saturates the trivial double-counting ceiling**:
`|L| * k * (k - 1) = k^d * (k^d - 1)`.
Thus no purely incidence-axiomatic / linear-space / `K_{2,2}`-free hypergraph argument can improve
the trivial constant `1 / (k(k - 1))` (for any prime power `k`), let alone prove `o(n^2)`. -/
theorem ppl022_linear_space_barrier_fq (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (d : ℕ) :
    ∃ L : Finset (AffineSubspace F (Fin d → F)),
      (∀ ℓ : AffineSubspace F (Fin d → F),
        Module.finrank F ℓ.direction = 1 →
        (Finset.univ.filter (· ∈ ℓ)).card ≤ Fintype.card F) ∧
      (∀ ℓ ∈ L, Module.finrank F ℓ.direction = 1 ∧
        (Finset.univ.filter (· ∈ ℓ)).card = Fintype.card F) ∧
      L.card * (Fintype.card F * (Fintype.card F - 1)) =
        Fintype.card F ^ d * (Fintype.card F ^ d - 1) := by
  let V := Fin d → F
  let mkLineF : V × V → AffineSubspace F V :=
    fun pq => AffineSubspace.mk' pq.1 (Submodule.span F ({pq.2 -ᵥ pq.1} : Set V))
  let pairs : Finset (V × V) := (Finset.univ ×ˢ Finset.univ).filter (fun pq => pq.1 ≠ pq.2)
  let L : Finset (AffineSubspace F V) := pairs.image mkLineF
  have hline_card_le : ∀ ℓ : AffineSubspace F V,
      Module.finrank F ℓ.direction = 1 →
      (Finset.univ.filter (· ∈ ℓ)).card ≤ Fintype.card F := by
    intro ℓ hℓ
    by_cases hne : (Finset.univ.filter (· ∈ ℓ)).Nonempty
    · obtain ⟨p, hp⟩ := hne
      have hpℓ : p ∈ ℓ := (Finset.mem_filter.mp hp).2
      have hpos : 0 < Module.finrank F ℓ.direction := by omega
      have hnt : ∃ v : ℓ.direction, v ≠ 0 := by
        by_contra h
        push Not at h
        have hsub : ℓ.direction = ⊥ := by
          ext x
          simp only [Submodule.mem_bot]
          constructor
          · intro hx; exact congrArg Subtype.val (h ⟨x, hx⟩)
          · rintro rfl; exact Submodule.zero_mem _
        rw [hsub, finrank_bot] at hℓ
        omega
      obtain ⟨⟨v, hv⟩, hv_ne⟩ := hnt
      have hv0 : v ≠ 0 := fun h => hv_ne (Subtype.ext h)
      have hle : Submodule.span F ({v} : Set V) ≤ ℓ.direction :=
        Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
      have : FiniteDimensional F ℓ.direction := Module.finite_of_finrank_pos hpos
      have hspan_dim : Module.finrank F (Submodule.span F ({v} : Set V)) = 1 :=
        finrank_span_singleton hv0
      have hdir : Submodule.span F ({v} : Set V) = ℓ.direction :=
        Submodule.eq_of_le_of_finrank_eq hle (hspan_dim.trans hℓ.symm)
      have hsub_img : Finset.univ.filter (· ∈ ℓ) ⊆
          (Finset.univ : Finset F).image (fun t : F => t • v +ᵥ p) := by
        intro x hx
        have hxℓ : x ∈ ℓ := (Finset.mem_filter.mp hx).2
        have hvsub : x -ᵥ p ∈ Submodule.span F ({v} : Set V) := by
          rw [hdir]; exact AffineSubspace.vsub_mem_direction hxℓ hpℓ
        rw [Submodule.mem_span_singleton] at hvsub
        obtain ⟨t, ht⟩ := hvsub
        exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, by rw [ht, vsub_vadd]⟩
      calc (Finset.univ.filter (· ∈ ℓ)).card
          ≤ ((Finset.univ : Finset F).image (fun t : F => t • v +ᵥ p)).card :=
            Finset.card_le_card hsub_img
        _ ≤ (Finset.univ : Finset F).card := Finset.card_image_le
        _ = Fintype.card F := Finset.card_univ
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  have hL_props : ∀ ℓ ∈ L, Module.finrank F ℓ.direction = 1 ∧
      (Finset.univ.filter (· ∈ ℓ)).card = Fintype.card F := by
    intro ℓ hℓ
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hℓ
    have hne : pq.1 ≠ pq.2 := (Finset.mem_filter.mp hpq).2
    have hv0 : pq.2 -ᵥ pq.1 ≠ 0 := vsub_ne_zero.mpr hne.symm
    have hdim : Module.finrank F (mkLineF pq).direction = 1 := by
      dsimp only [mkLineF]
      rw [AffineSubspace.direction_mk']
      exact finrank_span_singleton hv0
    have hmap_inj : Function.Injective (fun t : F => t • (pq.2 -ᵥ pq.1) +ᵥ pq.1) := by
      intro t₁ t₂ heq
      have h1 : t₁ • (pq.2 -ᵥ pq.1) = t₂ • (pq.2 -ᵥ pq.1) := vadd_right_cancel pq.1 heq
      have h2 : (t₁ - t₂) • (pq.2 -ᵥ pq.1) = 0 := by rw [sub_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with ht | hv
      · exact sub_eq_zero.mp ht
      · exact absurd hv hv0
    have hsub : (Finset.univ : Finset F).image (fun t : F => t • (pq.2 -ᵥ pq.1) +ᵥ pq.1) ⊆
        Finset.univ.filter (· ∈ mkLineF pq) := by
      intro x hx
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      dsimp only [mkLineF]
      rw [AffineSubspace.mem_mk', vadd_vsub]
      exact Submodule.mem_span_singleton.mpr ⟨t, rfl⟩
    have hge : Fintype.card F ≤ (Finset.univ.filter (· ∈ mkLineF pq)).card := by
      calc Fintype.card F = (Finset.univ : Finset F).card := (Finset.card_univ).symm
        _ = ((Finset.univ : Finset F).image (fun t : F => t • (pq.2 -ᵥ pq.1) +ᵥ pq.1)).card :=
            (Finset.card_image_of_injective _ hmap_inj).symm
        _ ≤ (Finset.univ.filter (· ∈ mkLineF pq)).card := Finset.card_le_card hsub
    exact ⟨hdim, le_antisymm (hline_card_le _ hdim) hge⟩
  -- Exact partition of 2-subsets of `V` by lines in `L`
  have hdisj : Set.PairwiseDisjoint (L : Set (AffineSubspace F V))
      (fun ℓ => (Finset.univ.filter (· ∈ ℓ)).powersetCard 2) := by
    intro ℓ₁ hℓ₁ ℓ₂ hℓ₂ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro s hs₁ hs₂
    rw [Finset.mem_powersetCard] at hs₁ hs₂
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs₁.2
    have hp₁ : p ∈ ℓ₁ := (Finset.mem_filter.mp (hs₁.1 (by simp))).2
    have hq₁ : q ∈ ℓ₁ := (Finset.mem_filter.mp (hs₁.1 (by simp))).2
    have hp₂ : p ∈ ℓ₂ := (Finset.mem_filter.mp (hs₂.1 (by simp))).2
    have hq₂ : q ∈ ℓ₂ := (Finset.mem_filter.mp (hs₂.1 (by simp))).2
    exact hne (affine_line_eq_of_two_mem (hL_props ℓ₁ hℓ₁).1 (hL_props ℓ₂ hℓ₂).1 hpq hp₁ hq₁ hp₂ hq₂)
  have hbiUnion_eq :
      L.biUnion (fun ℓ => (Finset.univ.filter (· ∈ ℓ)).powersetCard 2) =
      (Finset.univ : Finset V).powersetCard 2 := by
    ext s
    simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨_, _, _, hcard⟩; exact hcard
    · intro hcard
      obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hcard
      refine ⟨mkLineF (p, q), Finset.mem_image.mpr ⟨(p, q),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hpq⟩,
        rfl⟩, ?_, Finset.card_pair hpq⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases hx with rfl | rfl
      · exact AffineSubspace.self_mem_mk' _ _
      · dsimp only [mkLineF]; rw [AffineSubspace.mem_mk']; exact Submodule.subset_span rfl
  have hchoose_eq : L.card * (Fintype.card F).choose 2 = (Fintype.card F ^ d).choose 2 := by
    have hV_card : (Finset.univ : Finset V).card = Fintype.card F ^ d := by
      simp [V]
    calc L.card * (Fintype.card F).choose 2
        = ∑ ℓ ∈ L, ((Finset.univ.filter (· ∈ ℓ)).powersetCard 2).card := by
          rw [← smul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun ℓ hℓ => ?_
          rw [Finset.card_powersetCard, (hL_props ℓ hℓ).2]
      _ = (L.biUnion (fun ℓ => (Finset.univ.filter (· ∈ ℓ)).powersetCard 2)).card :=
          (Finset.card_biUnion hdisj).symm
      _ = ((Finset.univ : Finset V).powersetCard 2).card := by rw [hbiUnion_eq]
      _ = (Fintype.card F ^ d).choose 2 := by rw [Finset.card_powersetCard, hV_card]
  have hk2 : 2 * (Fintype.card F).choose 2 = Fintype.card F * (Fintype.card F - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd]
  have hn2 : 2 * (Fintype.card F ^ d).choose 2 = Fintype.card F ^ d * (Fintype.card F ^ d - 1) := by
    rw [Nat.choose_two_right, mul_comm, Nat.div_mul_cancel (Nat.even_mul_pred_self _).two_dvd]
  refine ⟨L, hline_card_le, hL_props, ?_⟩
  calc L.card * (Fintype.card F * (Fintype.card F - 1))
      = 2 * (L.card * (Fintype.card F).choose 2) := by rw [← hk2]; ring
    _ = 2 * (Fintype.card F ^ d).choose 2 := by rw [hchoose_eq]
    _ = Fintype.card F ^ d * (Fintype.card F ^ d - 1) := hn2

/-- **Barrier 1 Specialized to `k = 4` (Erdős #101 Linear-Space Ceiling Saturation)**:
for every `d ≥ 1`, there exists a 4-element field `F` (explicitly `𝔽₄ = GaloisField 2 2`) such that
the `n = 4^d`-point affine space `Fin d → F` has **no 5 points collinear** and achieves **exact**
`12 * |L| = n * (n - 1)` 4-point lines. -/
theorem ppl022_linear_space_barrier_k4 (d : ℕ) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F),
      Fintype.card F = 4 ∧
      ∃ L : Finset (AffineSubspace F (Fin d → F)),
        (∀ ℓ : AffineSubspace F (Fin d → F),
          Module.finrank F ℓ.direction = 1 →
          (Finset.univ.filter (· ∈ ℓ)).card ≤ 4) ∧
        (∀ ℓ ∈ L, Module.finrank F ℓ.direction = 1 ∧
          (Finset.univ.filter (· ∈ ℓ)).card = 4) ∧
        12 * L.card = 4 ^ d * (4 ^ d - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite (GaloisField 2 2)
  have hcard4 : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨L, hle, hL, hsat⟩ := ppl022_linear_space_barrier_fq (GaloisField 2 2) d
  rw [hcard4] at hle hL hsat
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hcard4, L, hle, hL, by linarith⟩

/-- **Barrier 2 (Real Topological / Pseudoline Barrier Core — Grid + Diagonals)**:
for every `M ≥ 1`, there exists a family `A` of `6 * M - 2` distinct affine lines in `ℝ²` and a set
`Q` of `M^2` distinct points in `ℝ²` such that:
1. Every point `p ∈ ℝ²` lies on **at most 4** lines of `A` (zero 5-fold intersections in `ℝ²`),
2. Every point `p ∈ Q` lies on **exactly 4** lines of `A`, with `A.card ^ 2 ≤ 36 * Q.card`,
3. Every line in `A` belongs to one of **4** parallel direction classes (so perturbing only the 4
   parallel bundles at infinity in `ℝP²` produces an `n`-pseudoline arrangement with no 5 concurrent
   and `≥ n^2 / 36` quadruple intersections, ruling out purely topological/Melchior/Crossing-Lemma
   proofs of Erdős #101). -/
theorem ppl022_grid_diagonals_pseudoline_core (M : ℕ) (hM : 1 ≤ M) :
    ∃ (A : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))))
      (Q : Finset (EuclideanSpace ℝ (Fin 2)))
      (d₁ d₂ d₃ d₄ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))),
      A.card = 6 * M - 2 ∧
      Q.card = M ^ 2 ∧
      A.card ^ 2 ≤ 36 * Q.card ∧
      (∀ ℓ ∈ A, Module.finrank ℝ ℓ.direction = 1 ∧
        (ℓ.direction = d₁ ∨ ℓ.direction = d₂ ∨ ℓ.direction = d₃ ∨ ℓ.direction = d₄)) ∧
      (∀ p : EuclideanSpace ℝ (Fin 2), (A.filter (p ∈ ·)).card ≤ 4) ∧
      (∀ p ∈ Q, (A.filter (p ∈ ·)).card = 4) := by
  let v₁ : EuclideanSpace ℝ (Fin 2) := mkPt 1 0
  let v₂ : EuclideanSpace ℝ (Fin 2) := mkPt 0 1
  let v₃ : EuclideanSpace ℝ (Fin 2) := mkPt 1 (-1)
  let v₄ : EuclideanSpace ℝ (Fin 2) := mkPt 1 1
  let d₁ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℝ ({v₁} : Set _)
  let d₂ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℝ ({v₂} : Set _)
  let d₃ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℝ ({v₃} : Set _)
  let d₄ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := Submodule.span ℝ ({v₄} : Set _)
  have hv₁ : v₁ ≠ 0 := by intro h; have := congrArg (fun x => x 0) h; simp [v₁, mkPt_zero] at this
  have hv₂ : v₂ ≠ 0 := by intro h; have := congrArg (fun x => x 1) h; simp [v₂, mkPt_one] at this
  have hv₃ : v₃ ≠ 0 := by intro h; have := congrArg (fun x => x 0) h; simp [v₃, mkPt_zero] at this
  have hv₄ : v₄ ≠ 0 := by intro h; have := congrArg (fun x => x 0) h; simp [v₄, mkPt_zero] at this
  have hd12 : d₁ ≠ d₂ := by
    intro h
    have hv1_mem : v₁ ∈ d₂ := by rw [← h]; exact Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at hv1_mem
    obtain ⟨c, hc⟩ := hv1_mem
    have := congrArg (fun x => x 0) hc
    simp [v₁, v₂, mkPt_zero] at this
  have hd13 : d₁ ≠ d₃ := by
    intro h
    have hv1_mem : v₁ ∈ d₃ := by rw [← h]; exact Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at hv1_mem
    obtain ⟨c, hc⟩ := hv1_mem
    have h0 := congrArg (fun x => x 0) hc
    have h1 := congrArg (fun x => x 1) hc
    simp [v₁, v₃, mkPt_zero, mkPt_one] at h0 h1
    linarith
  have hd14 : d₁ ≠ d₄ := by
    intro h
    have hv1_mem : v₁ ∈ d₄ := by rw [← h]; exact Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at hv1_mem
    obtain ⟨c, hc⟩ := hv1_mem
    have h0 := congrArg (fun x => x 0) hc
    have h1 := congrArg (fun x => x 1) hc
    simp [v₁, v₄, mkPt_zero, mkPt_one] at h0 h1
    linarith
  have hd23 : d₂ ≠ d₃ := by
    intro h
    have hv2_mem : v₂ ∈ d₃ := by rw [← h]; exact Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at hv2_mem
    obtain ⟨c, hc⟩ := hv2_mem
    have h0 := congrArg (fun x => x 0) hc
    have h1 := congrArg (fun x => x 1) hc
    simp [v₂, v₃, mkPt_zero, mkPt_one] at h0 h1
    linarith
  have hd24 : d₂ ≠ d₄ := by
    intro h
    have hv2_mem : v₂ ∈ d₄ := by rw [← h]; exact Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at hv2_mem
    obtain ⟨c, hc⟩ := hv2_mem
    have h0 := congrArg (fun x => x 0) hc
    have h1 := congrArg (fun x => x 1) hc
    simp [v₂, v₄, mkPt_zero, mkPt_one] at h0 h1
    linarith
  have hd34 : d₃ ≠ d₄ := by
    intro h
    have hv3_mem : v₃ ∈ d₄ := by rw [← h]; exact Submodule.subset_span rfl
    rw [Submodule.mem_span_singleton] at hv3_mem
    obtain ⟨c, hc⟩ := hv3_mem
    have h0 := congrArg (fun x => x 0) hc
    have h1 := congrArg (fun x => x 1) hc
    simp [v₃, v₄, mkPt_zero, mkPt_one] at h0 h1
    linarith
  -- Membership characterizations for the 4 line types
  let lineH : ℕ → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    fun j => AffineSubspace.mk' (mkPt 0 (j : ℝ)) d₁
  let lineV : ℕ → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    fun i => AffineSubspace.mk' (mkPt (i : ℝ) 0) d₂
  let lineA : ℕ → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    fun c => AffineSubspace.mk' (mkPt (c : ℝ) 0) d₃
  let lineD : ℕ → AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
    fun s => AffineSubspace.mk' (mkPt ((s : ℝ) - ((M - 1 : ℕ) : ℝ)) 0) d₄
  have hmemH : ∀ j p, p ∈ lineH j ↔ p 1 = (j : ℝ) := by
    intro j p
    rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      have := congrArg (fun x => x 1) ht
      simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply, v₁, mkPt_one] at this
      linarith
    · intro h1
      refine ⟨p 0, mkPt_ext ?_ ?_⟩
      · simp [v₁, mkPt_zero]
      · simp [v₁, mkPt_one, h1]
  have hmemV : ∀ i p, p ∈ lineV i ↔ p 0 = (i : ℝ) := by
    intro i p
    rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      have := congrArg (fun x => x 0) ht
      simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply, v₂, mkPt_zero] at this
      linarith
    · intro h0
      refine ⟨p 1, mkPt_ext ?_ ?_⟩
      · simp [v₂, mkPt_zero, h0]
      · simp [v₂, mkPt_one]
  have hmemA : ∀ c p, p ∈ lineA c ↔ p 0 + p 1 = (c : ℝ) := by
    intro c p
    rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      have h0 := congrArg (fun x => x 0) ht
      have h1 := congrArg (fun x => x 1) ht
      simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply, v₃, mkPt_zero, mkPt_one] at h0 h1
      linarith
    · intro hsum
      refine ⟨-p 1, mkPt_ext ?_ ?_⟩
      · simp [v₃, mkPt_zero]; linarith
      · simp [v₃, mkPt_one]
  have hmemD : ∀ s p, p ∈ lineD s ↔ p 0 - p 1 = (s : ℝ) - ((M - 1 : ℕ) : ℝ) := by
    intro s p
    rw [AffineSubspace.mem_mk', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, ht⟩
      have h0 := congrArg (fun x => x 0) ht
      have h1 := congrArg (fun x => x 1) ht
      simp only [PiLp.smul_apply, smul_eq_mul, vsub_eq_sub, PiLp.sub_apply, v₄, mkPt_zero, mkPt_one] at h0 h1
      linarith
    · intro hdiff
      refine ⟨p 1, mkPt_ext ?_ ?_⟩
      · simp [v₄, mkPt_zero]; linarith
      · simp [v₄, mkPt_one]
  have hinjH : Function.Injective lineH := by
    intro j₁ j₂ heq
    have : mkPt 0 (j₁ : ℝ) ∈ lineH j₂ := heq ▸ (hmemH j₁ _).mpr rfl
    rw [hmemH, mkPt_one] at this
    exact Nat.cast_injective this
  have hinjV : Function.Injective lineV := by
    intro i₁ i₂ heq
    have : mkPt (i₁ : ℝ) 0 ∈ lineV i₂ := heq ▸ (hmemV i₁ _).mpr rfl
    rw [hmemV, mkPt_zero] at this
    exact Nat.cast_injective this
  have hinjA : Function.Injective lineA := by
    intro c₁ c₂ heq
    have : mkPt (c₁ : ℝ) 0 ∈ lineA c₂ := heq ▸ (hmemA c₁ _).mpr (by simp [mkPt_zero, mkPt_one])
    rw [hmemA, mkPt_zero, mkPt_one, add_zero] at this
    exact Nat.cast_injective this
  have hinjD : Function.Injective lineD := by
    intro s₁ s₂ heq
    have : mkPt ((s₁ : ℝ) - ((M - 1 : ℕ) : ℝ)) 0 ∈ lineD s₂ :=
      heq ▸ (hmemD s₁ _).mpr (by simp [mkPt_zero, mkPt_one])
    rw [hmemD, mkPt_zero, mkPt_one, sub_zero] at this
    have : (s₁ : ℝ) = (s₂ : ℝ) := by linarith
    exact_mod_cast this
  let AH : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := (Finset.range M).image lineH
  let AV : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := (Finset.range M).image lineV
  let AA : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := (Finset.range (2 * M - 1)).image lineA
  let AD : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := (Finset.range (2 * M - 1)).image lineD
  let A := AH ∪ AV ∪ AA ∪ AD
  have hdirH : ∀ ℓ ∈ AH, ℓ.direction = d₁ := by
    intro ℓ hℓ; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hℓ; exact AffineSubspace.direction_mk' _ _
  have hdirV : ∀ ℓ ∈ AV, ℓ.direction = d₂ := by
    intro ℓ hℓ; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hℓ; exact AffineSubspace.direction_mk' _ _
  have hdirA : ∀ ℓ ∈ AA, ℓ.direction = d₃ := by
    intro ℓ hℓ; obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hℓ; exact AffineSubspace.direction_mk' _ _
  have hdirD : ∀ ℓ ∈ AD, ℓ.direction = d₄ := by
    intro ℓ hℓ; obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hℓ; exact AffineSubspace.direction_mk' _ _
  have hdisj_HV : Disjoint AH AV := Finset.disjoint_left.mpr fun ℓ h1 h2 =>
    hd12 ((hdirH ℓ h1).symm.trans (hdirV ℓ h2))
  have hdisj_HVA : Disjoint (AH ∪ AV) AA := Finset.disjoint_left.mpr fun ℓ h1 h2 => by
    rcases Finset.mem_union.mp h1 with hH | hV
    · exact hd13 ((hdirH ℓ hH).symm.trans (hdirA ℓ h2))
    · exact hd23 ((hdirV ℓ hV).symm.trans (hdirA ℓ h2))
  have hdisj_HVAD : Disjoint (AH ∪ AV ∪ AA) AD := Finset.disjoint_left.mpr fun ℓ h1 h2 => by
    rcases Finset.mem_union.mp h1 with hHV | hA
    · rcases Finset.mem_union.mp hHV with hH | hV
      · exact hd14 ((hdirH ℓ hH).symm.trans (hdirD ℓ h2))
      · exact hd24 ((hdirV ℓ hV).symm.trans (hdirD ℓ h2))
    · exact hd34 ((hdirA ℓ hA).symm.trans (hdirD ℓ h2))
  have hA_card : A.card = 6 * M - 2 := by
    simp only [A]
    rw [Finset.card_union_of_disjoint hdisj_HVAD,
        Finset.card_union_of_disjoint hdisj_HVA,
        Finset.card_union_of_disjoint hdisj_HV,
        Finset.card_image_of_injective _ hinjH,
        Finset.card_image_of_injective _ hinjV,
        Finset.card_image_of_injective _ hinjA,
        Finset.card_image_of_injective _ hinjD,
        Finset.card_range, Finset.card_range]
    omega
  -- Grid points `Q = {0, ..., M-1}^2`
  let Q : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.range M ×ˢ Finset.range M).image (fun ij => mkPt (ij.1 : ℝ) (ij.2 : ℝ))
  have hQ_inj : Function.Injective (fun ij : ℕ × ℕ => mkPt (ij.1 : ℝ) (ij.2 : ℝ)) := by
    intro a b heq
    have h0 : (a.1 : ℝ) = (b.1 : ℝ) := by
      have := congrArg (fun x => x 0) heq; simpa [mkPt_zero] using this
    have h1 : (a.2 : ℝ) = (b.2 : ℝ) := by
      have := congrArg (fun x => x 1) heq; simpa [mkPt_one] using this
    exact Prod.ext (by exact_mod_cast h0) (by exact_mod_cast h1)
  have hQ_card : Q.card = M ^ 2 := by
    rw [Finset.card_image_of_injective _ hQ_inj, Finset.card_product, Finset.card_range]
    ring
  -- Every point in `ℝ²` lies on at most 1 line from each of the 4 classes
  have hle4 : ∀ p : EuclideanSpace ℝ (Fin 2), (A.filter (p ∈ ·)).card ≤ 4 := by
    intro p
    have hle1_H : (AH.filter (p ∈ ·)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro ℓ₁ h₁ ℓ₂ h₂
      obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₁).1
      obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₂).1
      have e1 := (hmemH j₁ p).mp (Finset.mem_filter.mp h₁).2
      have e2 := (hmemH j₂ p).mp (Finset.mem_filter.mp h₂).2
      have : j₁ = j₂ := Nat.cast_injective (e1.symm.trans e2)
      rw [this]
    have hle1_V : (AV.filter (p ∈ ·)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro ℓ₁ h₁ ℓ₂ h₂
      obtain ⟨i₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₁).1
      obtain ⟨i₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₂).1
      have e1 := (hmemV i₁ p).mp (Finset.mem_filter.mp h₁).2
      have e2 := (hmemV i₂ p).mp (Finset.mem_filter.mp h₂).2
      have : i₁ = i₂ := Nat.cast_injective (e1.symm.trans e2)
      rw [this]
    have hle1_A : (AA.filter (p ∈ ·)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro ℓ₁ h₁ ℓ₂ h₂
      obtain ⟨c₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₁).1
      obtain ⟨c₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₂).1
      have e1 := (hmemA c₁ p).mp (Finset.mem_filter.mp h₁).2
      have e2 := (hmemA c₂ p).mp (Finset.mem_filter.mp h₂).2
      have : c₁ = c₂ := Nat.cast_injective (e1.symm.trans e2)
      rw [this]
    have hle1_D : (AD.filter (p ∈ ·)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro ℓ₁ h₁ ℓ₂ h₂
      obtain ⟨s₁, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₁).1
      obtain ⟨s₂, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h₂).1
      have e1 := (hmemD s₁ p).mp (Finset.mem_filter.mp h₁).2
      have e2 := (hmemD s₂ p).mp (Finset.mem_filter.mp h₂).2
      have : (s₁ : ℝ) = (s₂ : ℝ) := by linarith
      have : s₁ = s₂ := by exact_mod_cast this
      rw [this]
    simp only [A, Finset.filter_union]
    have u1 := Finset.card_union_le (AH.filter (p ∈ ·) ∪ AV.filter (p ∈ ·) ∪ AA.filter (p ∈ ·)) (AD.filter (p ∈ ·))
    have u2 := Finset.card_union_le (AH.filter (p ∈ ·) ∪ AV.filter (p ∈ ·)) (AA.filter (p ∈ ·))
    have u3 := Finset.card_union_le (AH.filter (p ∈ ·)) (AV.filter (p ∈ ·))
    omega
  -- Every grid point in `Q` lies on 4 distinct lines of `A`
  have heq4 : ∀ p ∈ Q, (A.filter (p ∈ ·)).card = 4 := by
    intro p hp
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    let ℓ₁ := lineH j
    let ℓ₂ := lineV i
    let ℓ₃ := lineA (i + j)
    let ℓ₄ := lineD (i + (M - 1) - j)
    have h1A : ℓ₁ ∈ A := Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hij.2, rfl⟩)))
    have h2A : ℓ₂ ∈ A := Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij.1, rfl⟩)))
    have h3A : ℓ₃ ∈ A := Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i + j, Finset.mem_range.mpr (by omega), rfl⟩))
    have h4A : ℓ₄ ∈ A := Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i + (M - 1) - j, Finset.mem_range.mpr (by omega), rfl⟩)
    have hm1 : mkPt (i : ℝ) (j : ℝ) ∈ ℓ₁ := (hmemH j _).mpr rfl
    have hm2 : mkPt (i : ℝ) (j : ℝ) ∈ ℓ₂ := (hmemV i _).mpr rfl
    have hm3 : mkPt (i : ℝ) (j : ℝ) ∈ ℓ₃ := (hmemA (i + j) _).mpr (by simp [mkPt_zero, mkPt_one])
    have hm4 : mkPt (i : ℝ) (j : ℝ) ∈ ℓ₄ := by
      rw [hmemD, mkPt_zero, mkPt_one]
      have hjle : j ≤ i + (M - 1) := by omega
      have hcast : ((i + (M - 1) - j : ℕ) : ℝ) = (i : ℝ) + ((M - 1 : ℕ) : ℝ) - (j : ℝ) := by
        rw [Nat.cast_sub hjle, Nat.cast_add]
      linarith
    have hne12 : ℓ₁ ≠ ℓ₂ := fun h => hd12 (by
      have := congrArg AffineSubspace.direction h
      simpa [ℓ₁, ℓ₂, lineH, lineV] using this)
    have hne13 : ℓ₁ ≠ ℓ₃ := fun h => hd13 (by
      have := congrArg AffineSubspace.direction h
      simpa [ℓ₁, ℓ₃, lineH, lineA] using this)
    have hne14 : ℓ₁ ≠ ℓ₄ := fun h => hd14 (by
      have := congrArg AffineSubspace.direction h
      simpa [ℓ₁, ℓ₄, lineH, lineD] using this)
    have hne23 : ℓ₂ ≠ ℓ₃ := fun h => hd23 (by
      have := congrArg AffineSubspace.direction h
      simpa [ℓ₂, ℓ₃, lineV, lineA] using this)
    have hne24 : ℓ₂ ≠ ℓ₄ := fun h => hd24 (by
      have := congrArg AffineSubspace.direction h
      simpa [ℓ₂, ℓ₄, lineV, lineD] using this)
    have hne34 : ℓ₃ ≠ ℓ₄ := fun h => hd34 (by
      have := congrArg AffineSubspace.direction h
      simpa [ℓ₃, ℓ₄, lineA, lineD] using this)
    have hsub : ({ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset _) ⊆ A.filter (mkPt (i : ℝ) (j : ℝ) ∈ ·) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact Finset.mem_filter.mpr ⟨by assumption, by assumption⟩
    have hge4 : 4 ≤ (A.filter (mkPt (i : ℝ) (j : ℝ) ∈ ·)).card := by
      calc 4 = ({ℓ₁, ℓ₂, ℓ₃, ℓ₄} : Finset _).card := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
              Finset.card_insert_of_notMem, Finset.card_singleton]
            · simp [hne34]
            · simp [hne23, hne24]
            · simp [hne12, hne13, hne14]
        _ ≤ (A.filter (mkPt (i : ℝ) (j : ℝ) ∈ ·)).card := Finset.card_le_card hsub
    exact le_antisymm (hle4 _) hge4
  refine ⟨A, Q, d₁, d₂, d₃, d₄, hA_card, hQ_card, ?_, ?_, hle4, heq4⟩
  · rw [hA_card, hQ_card]
    have hle : 6 * M - 2 ≤ 6 * M := Nat.sub_le _ _
    calc (6 * M - 2) ^ 2 ≤ (6 * M) ^ 2 := Nat.pow_le_pow_left hle 2
      _ = 36 * M ^ 2 := by ring
  · intro ℓ hℓ
    have h1 : Module.finrank ℝ d₁ = 1 := finrank_span_singleton hv₁
    have h2 : Module.finrank ℝ d₂ = 1 := finrank_span_singleton hv₂
    have h3 : Module.finrank ℝ d₃ = 1 := finrank_span_singleton hv₃
    have h4 : Module.finrank ℝ d₄ = 1 := finrank_span_singleton hv₄
    simp only [A, Finset.mem_union] at hℓ
    rcases hℓ with ((hH | hV) | hA') | hD'
    · rw [hdirH ℓ hH]; exact ⟨h1, Or.inl rfl⟩
    · rw [hdirV ℓ hV]; exact ⟨h2, Or.inr (Or.inl rfl)⟩
    · rw [hdirA ℓ hA']; exact ⟨h3, Or.inr (Or.inr (Or.inl rfl))⟩
    · rw [hdirD ℓ hD']; exact ⟨h4, Or.inr (Or.inr (Or.inr rfl))⟩

end PPL022
