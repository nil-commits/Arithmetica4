/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 123 (Erdős Problem #142 — Asymptotic Formula for `r_k(N)` Progression-Free Sets, $10,000)

**Honest Scope Notice:**
Erdős Problem #142 (`erdosproblems.com/142`, PPL 123, $10,000 prize) asks to prove an asymptotic
formula for `r_k(N)`, the maximum size of a subset `A ⊆ {1, ..., N}` containing no non-trivial
`k`-term arithmetic progression. The full asymptotic conjecture remains **OPEN** as of 2026
(current live frontier for `k = 3`: lower bound `N · exp(-(c_EHPS + o(1)) √(log N))` by
Elsholtz–Hunter–Proske–Sauermann 2024 improving Behrend 1946; upper bound
`N · exp(-c (log N)^(1/6) / log log N)` by Rushil Raghavan, March 2026, arXiv:2603.27045,
improving Bloom–Sisask `(log N)^(1/9)` and Kelley–Meka `(log N)^(1/12)`; for `k ≥ 5`:
Rankin 1961 / O'Bryant 2011 `N · exp(-c_k (log N)^(1/⌈log_2 k⌉})` vs Leng–Sah–Sawhney 2024
`N · exp(-(log log N)^(c_k))`).

This file provides a self-contained, pure-Mathlib Lean 4 formalization of the major structural,
lower-bound, and quantitative Fourier upper-bound milestones around `r_k(N)`, with **zero custom
or private definitions in any public theorem signature** and **zero `native_decide`**:

1. **Exact Structural Laws & Fekete Limit (for all `k ≥ 1`):**
   Monotonicity in `N` and `k`, exact equivalence `r_3(N) = rothNumberNat N`, subadditivity
   `r_k(M + N) ≤ r_k(M) + r_k(N)`, and Fekete density limit existence `r_k(N) / N → L_k ∈ [0, 1]`.
2. **Exact Small Values (`0` `native_decide`):**
   `r_3(1..9) = 1, 2, 2, 3, 4, 4, 4, 4, 5` and `r_4(1..10) = 1, 2, 3, 3, 4, 5, 5, 6, 7, 8`.
3. **Sharp Behrend (1946) Constant & Rankin (1961) General-`k` Sphere-Packing Lower Bound:**
   - Strictly improves Mathlib's `Behrend.roth_lower_bound` constant `-4` to Behrend's optimal
     `-2 * √(2 * log 2) ≈ -2.3548` (both asymptotically for every `ε > 0` and explicitly `-2.5`).
   - Proves Rankin's (1961) general-`k` lower bound `r_k(N) ≥ N * exp(-C_k * (log N)^(1 / Nat.clog 2 k))`
     for every `k ≥ 3` (new in Lean 4 / not in Mathlib).
4. **Roth (1953) Quantitative Fourier Density-Increment Upper Bound:**
   - Self-contained discrete Fourier analysis over `ZMod (2 * N + 1)` (zero measure theory),
     Dirichlet pigeonhole AP-partitioning, and density-increment iteration proving
     `r_3(N) ≤ C * N / log (log N)` (vastly stronger than Mathlib's tower-type `roth_3ap_theorem`),
     plus the corollary `r_3(N) / N → 0`.
-/

namespace PPL123

/-! ## Section 1: Internal Helpers & Structural Laws of `r_k(N)` -/

section StructuralLaws

private def IsKApFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A

private noncomputable def rK (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsKApFree k A ∧ A.card = m}

private lemma rK_set_bddAbove (k N : ℕ) :
    BddAbove {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsKApFree k A ∧ A.card = m} := by
  refine ⟨N, ?_⟩
  rintro m ⟨A, hA, _, rfl⟩
  calc
    A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
    _ = N := by simp

private lemma rK_set_nonempty {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ({m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsKApFree k A ∧ A.card = m}).Nonempty := by
  refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
  intro a d _ h
  have h0 := h 0 (by omega)
  simp at h0

private lemma card_le_rK {k N : ℕ} {A : Finset ℕ}
    (hsub : A ⊆ Finset.Icc 1 N) (hfree : IsKApFree k A) :
    A.card ≤ rK k N :=
  le_csSup (rK_set_bddAbove k N) ⟨A, hsub, hfree, rfl⟩

private lemma rK_le_of_forall {k N B : ℕ}
    (hB : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → IsKApFree k A → A.card ≤ B) :
    rK k N ≤ B := by
  unfold rK
  by_cases hne : ({m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsKApFree k A ∧ A.card = m}).Nonempty
  · refine csSup_le hne ?_
    rintro m ⟨A, hA, hf, rfl⟩
    exact hB A hA hf
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

private lemma exists_witness_rK {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsKApFree k A ∧ A.card = rK k N := by
  have hmem : rK k N ∈ {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsKApFree k A ∧ A.card = m} :=
    Nat.sSup_mem (rK_set_nonempty hk N) (rK_set_bddAbove k N)
  exact hmem

private lemma isKApFree_subset {k : ℕ} {A B : Finset ℕ} (hAB : A ⊆ B) (hB : IsKApFree k B) :
    IsKApFree k A := by
  intro a d hd h
  exact hB a d hd fun i hi => hAB (h i hi)

private lemma isKApFree_mono_k {k₁ k₂ : ℕ} {A : Finset ℕ} (hk : k₁ ≤ k₂) (h1 : IsKApFree k₁ A) :
    IsKApFree k₂ A := by
  intro a d hd h
  exact h1 a d hd fun i hi => h i (lt_of_lt_of_le hi hk)

private lemma isKApFree_image_add_left {k c : ℕ} {A : Finset ℕ} (hA : IsKApFree k A) :
    IsKApFree k (A.image (· + c)) := by
  intro a d hd h
  have h0 := h 0 (by
    by_contra hk0
    have hk0' : k = 0 := by omega
    subst hk0'
    exact hA 0 d hd (fun i hi => absurd hi (Nat.not_lt_zero i)))
  simp only [Finset.mem_image, zero_mul, add_zero] at h0
  rcases h0 with ⟨a₀, _, ha₀⟩
  apply hA a₀ d hd
  intro i hi
  have hi' := h i hi
  simp only [Finset.mem_image] at hi'
  rcases hi' with ⟨y, hy, hy_eq⟩
  have hyeq : y = a₀ + i * d := by omega
  rwa [← hyeq]

private lemma isKApFree_of_image_add_left {k c : ℕ} {A : Finset ℕ}
    (hA : IsKApFree k (A.image (· + c))) : IsKApFree k A := by
  intro a d hd h
  apply hA (a + c) d hd
  intro i hi
  rw [Finset.mem_image]
  refine ⟨a + i * d, h i hi, by omega⟩

private lemma isKApFree_three_iff_threeAPFree (A : Finset ℕ) :
    IsKApFree 3 A ↔ ThreeAPFree (A : Set ℕ) := by
  constructor
  · intro h a ha b hb c hc heq
    by_contra hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · apply h a (b - a) (by omega)
      intro i hi
      interval_cases i
      · simpa using ha
      · have h1 : a + 1 * (b - a) = b := by omega
        rw [h1]; exact hb
      · have h2 : a + 2 * (b - a) = c := by omega
        rw [h2]; exact hc
    · apply h c (b - c) (by omega)
      intro i hi
      interval_cases i
      · simpa using hc
      · have h1 : c + 1 * (b - c) = b := by omega
        rw [h1]; exact hb
      · have h2 : c + 2 * (b - c) = a := by omega
        rw [h2]; exact ha
  · intro h a d hd hmem
    have ha : a ∈ (A : Set ℕ) := by simpa using hmem 0 (by omega)
    have hb : a + d ∈ (A : Set ℕ) := by simpa using hmem 1 (by omega)
    have hc : a + 2 * d ∈ (A : Set ℕ) := by simpa using hmem 2 (by omega)
    have heq : a + (a + 2 * d) = (a + d) + (a + d) := by omega
    have := h ha hb hc heq
    omega

/-- Basic upper bound: `r_k(N) ≤ N` for all `k, N`. -/
theorem rK_le_self (k N : ℕ) :
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} ≤ N := by
  exact rK_le_of_forall fun A hA _ => le_trans (Finset.card_le_card hA) (by simp)

/-- Monotonicity in `N`: if `M ≤ N`, then `r_k(M) ≤ r_k(N)`. -/
theorem rK_mono_N (k M N : ℕ) (hMN : M ≤ N) :
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 M ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} ≤
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} := by
  exact rK_le_of_forall fun A hA hf =>
    card_le_rK (Finset.Subset.trans hA (Finset.Icc_subset_Icc_right hMN)) hf

/-- Monotonicity in `k`: if `k₁ ≤ k₂`, then `r_{k₁}(N) ≤ r_{k₂}(N)`. -/
theorem rK_mono_k (k₁ k₂ N : ℕ) (hk : k₁ ≤ k₂) :
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k₁, a + i * d ∈ A) ∧ A.card = m} ≤
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k₂, a + i * d ∈ A) ∧ A.card = m} := by
  exact rK_le_of_forall fun A hA hf => card_le_rK hA (isKApFree_mono_k hk hf)

/-- Exact bridge to Mathlib's `rothNumberNat`: for every `N : ℕ`, `r_3(N) = rothNumberNat N`. -/
theorem rK_three_eq_rothNumberNat (N : ℕ) :
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = rothNumberNat N := by
  change rK 3 N = rothNumberNat N
  apply le_antisymm
  · refine rK_le_of_forall fun A hA hf => ?_
    let B : Finset ℕ := A.image (· - 1)
    have hB_card : B.card = A.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      dsimp only at hxy
      have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hA hx)).1
      have hy1 : 1 ≤ y := (Finset.mem_Icc.mp (hA hy)).1
      omega
    have hB_sub : B ⊆ Finset.range N := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      have hx_icc := Finset.mem_Icc.mp (hA hx)
      rw [Finset.mem_range]
      omega
    have hB_free : ThreeAPFree (B : Set ℕ) := by
      rw [← isKApFree_three_iff_threeAPFree]
      have himg : B.image (· + 1) = A := by
        ext x
        simp only [B, Finset.mem_image]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          have hz1 : 1 ≤ z := (Finset.mem_Icc.mp (hA hz)).1
          have : z - 1 + 1 = z := by omega
          rwa [this]
        · intro hx
          have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hA hx)).1
          exact ⟨x - 1, ⟨x, hx, rfl⟩, by omega⟩
      exact isKApFree_of_image_add_left (c := 1) (himg.symm ▸ hf)
    rw [← hB_card]
    exact hB_free.le_addRothNumber hB_sub
  · obtain ⟨B, hB_sub, hB_card, hB_free⟩ := addRothNumber_spec (Finset.range N)
    rw [show rothNumberNat N = B.card from hB_card.symm]
    let A : Finset ℕ := B.image (· + 1)
    have hA_card : A.card = B.card :=
      Finset.card_image_of_injective B (fun x y h => by omega)
    have hA_sub : A ⊆ Finset.Icc 1 N := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      have hyN : y < N := Finset.mem_range.mp (hB_sub hy)
      rw [Finset.mem_Icc]
      omega
    have hA_free : IsKApFree 3 A :=
      isKApFree_image_add_left ((isKApFree_three_iff_threeAPFree B).mpr hB_free)
    rw [← hA_card]
    exact card_le_rK hA_sub hA_free

/-- Subadditivity of `r_k(N)` for every `k`: `r_k(M + N) ≤ r_k(M) + r_k(N)`. -/
theorem rK_subadditive (k M N : ℕ) :
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (M + N) ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} ≤
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 M ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} +
    sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} := by
  change rK k (M + N) ≤ rK k M + rK k N
  refine rK_le_of_forall fun A hA hf => ?_
  let A₁ : Finset ℕ := A.filter (· ≤ M)
  let A₂ : Finset ℕ := A.filter (fun x => M < x)
  have hcard : A.card = A₁.card + A₂.card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (p := (· ≤ M))
    simpa [A₁, A₂, not_le] using this.symm
  have hA₁_sub : A₁ ⊆ Finset.Icc 1 M := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_Icc]
    exact ⟨(Finset.mem_Icc.mp (hA hx.1)).1, hx.2⟩
  have hA₁_le : A₁.card ≤ rK k M :=
    card_le_rK hA₁_sub (isKApFree_subset (Finset.filter_subset _ _) hf)
  let B₂ : Finset ℕ := A₂.image (· - M)
  have hB₂_card : B₂.card = A₂.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    dsimp only at hxy
    have hxM : M < x := (Finset.mem_filter.mp hx).2
    have hyM : M < y := (Finset.mem_filter.mp hy).2
    omega
  have hB₂_sub : B₂ ⊆ Finset.Icc 1 N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxA := (Finset.mem_filter.mp hx).1
    have hxM := (Finset.mem_filter.mp hx).2
    have hxMN := (Finset.mem_Icc.mp (hA hxA)).2
    rw [Finset.mem_Icc]
    omega
  have hB₂_free : IsKApFree k B₂ := by
    have himg : B₂.image (· + M) = A₂ := by
      ext x
      simp only [B₂, Finset.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have hzM : M < z := (Finset.mem_filter.mp hz).2
        have : z - M + M = z := by omega
        rwa [this]
      · intro hx
        have hxM : M < x := (Finset.mem_filter.mp hx).2
        exact ⟨x - M, ⟨x, hx, rfl⟩, by omega⟩
    exact isKApFree_of_image_add_left (c := M) (himg.symm ▸ isKApFree_subset (Finset.filter_subset _ _) hf)
  have hA₂_le : A₂.card ≤ rK k N := by
    rw [← hB₂_card]
    exact card_le_rK hB₂_sub hB₂_free
  omega

/-- Fekete's subadditive limit theorem for `r_k(N)`: for every `k : ℕ`, the limiting density
`lim_{N → ∞} r_k(N) / N` exists and lies in `[0, 1]`. -/
theorem rK_fekete_limit_exists (k : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ L ≤ 1 ∧
      Filter.Tendsto
        (fun N : ℕ =>
          ((sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
            (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} : ℕ) : ℝ) / (N : ℝ))
        Filter.atTop (nhds L) := by
  let u : ℕ → ℝ := fun N => (rK k N : ℝ)
  have hsub : Subadditive u := by
    intro m n
    dsimp [u]
    have hnat : rK k (m + n) ≤ rK k m + rK k n := rK_subadditive k m n
    exact_mod_cast hnat
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htend := hsub.tendsto_lim hbdd
  refine ⟨hsub.lim, ?_, ?_, htend⟩
  · exact ge_of_tendsto htend (Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · refine le_of_tendsto htend (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [div_le_one hnpos]
    dsimp [u]
    have hle : rK k n ≤ n := rK_le_self k n
    exact_mod_cast hle

end StructuralLaws

/-! ## Section 2: Exact Small Values of `r_3(N)` and `r_4(N)` (Zero `native_decide`) -/

section SmallValues

private lemma rK_eq_self_of_lt {k N : ℕ} (hNk : N < k) : rK k N = N := by
  apply le_antisymm (rK_le_self k N)
  have hfree : IsKApFree k (Finset.Icc 1 N) := by
    intro a d hd h
    have h0mem : a ∈ Finset.Icc 1 N := by simpa using h 0 (by omega)
    have h0 : 1 ≤ a := (Finset.mem_Icc.mp h0mem).1
    have hlast : a + (k - 1) * d ≤ N := (Finset.mem_Icc.mp (h (k - 1) (by omega))).2
    have h1 : k - 1 ≤ (k - 1) * d := Nat.le_mul_of_pos_right (k - 1) hd
    omega
  calc
    N = (Finset.Icc 1 N).card := by simp
    _ ≤ rK k N := card_le_rK (Finset.Subset.refl (Finset.Icc 1 N)) hfree

private lemma rK_self_eq_pred {k : ℕ} (hk : 2 ≤ k) : rK k k = k - 1 := by
  apply le_antisymm
  · refine rK_le_of_forall fun A hA hf => ?_
    by_contra hgt
    have hcard : A.card = k := le_antisymm (le_trans (Finset.card_le_card hA) (by simp)) (by omega)
    have hEq : A = Finset.Icc 1 k := Finset.eq_of_subset_of_card_le hA (by simp [hcard])
    apply hf 1 1 (by omega)
    intro i hi
    rw [hEq, Finset.mem_Icc]
    omega
  · have hfree : IsKApFree k (Finset.Icc 1 (k - 1)) := by
      intro a d hd h
      have h0mem : a ∈ Finset.Icc 1 (k - 1) := by simpa using h 0 (by omega)
      have h0 : 1 ≤ a := (Finset.mem_Icc.mp h0mem).1
      have hlast : a + (k - 1) * d ≤ k - 1 := (Finset.mem_Icc.mp (h (k - 1) (by omega))).2
      have h1 : k - 1 ≤ (k - 1) * d := Nat.le_mul_of_pos_right (k - 1) hd
      omega
    calc
      k - 1 = (Finset.Icc 1 (k - 1)).card := by simp
      _ ≤ rK k k := card_le_rK (Finset.Icc_subset_Icc_right (Nat.sub_le k 1)) hfree

private lemma rK_three_eight_le_four : rK 3 8 ≤ 4 := by
  refine rK_le_of_forall fun A hA hf => ?_
  have h3ap : ∀ x y z : ℕ, x ∈ A → y ∈ A → z ∈ A → x < y → y - x = z - y → y < z → False := by
    intro x y z hx hy hz hxy hdiff hyz
    apply hf x (y - x) (by omega)
    intro i hi
    interval_cases i
    · simpa using hx
    · have h1 : x + 1 * (y - x) = y := by omega
      rw [h1]; exact hy
    · have h2 : x + 2 * (y - x) = z := by omega
      rw [h2]; exact hz
  let b : ℕ → ℕ := fun n => if n ∈ A then 1 else 0
  have hAcard : A.card = b 1 + b 2 + b 3 + b 4 + b 5 + b 6 + b 7 + b 8 := by
    have hsum : A.card = ∑ x ∈ Finset.Icc 1 8, b x := by
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc 1 8).filter (· ∈ A) = A := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun hx => ⟨hA hx, hx⟩⟩
      simp [hfilt]
    rw [hsum]
    have hIcc : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
    rw [hIcc]
    simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    ring
  rw [hAcard]
  have hno : ∀ x y z : ℕ, x < y → y < z → x + z = 2 * y → b x + b y + b z ≤ 2 := by
    intro x y z hxy hyz heq
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> by_cases hz : z ∈ A
    · exfalso; exact h3ap x y z hx hy hz hxy (by omega) hyz
    all_goals simp [b, hx, hy, hz]
  have hb01 : ∀ n, b n ≤ 1 := fun n => by dsimp [b]; split_ifs <;> omega
  have h123 := hno 1 2 3 (by omega) (by omega) (by omega)
  have h234 := hno 2 3 4 (by omega) (by omega) (by omega)
  have h567 := hno 5 6 7 (by omega) (by omega) (by omega)
  have h678 := hno 6 7 8 (by omega) (by omega) (by omega)
  have h135 := hno 1 3 5 (by omega) (by omega) (by omega)
  have h246 := hno 2 4 6 (by omega) (by omega) (by omega)
  have h357 := hno 3 5 7 (by omega) (by omega) (by omega)
  have h468 := hno 4 6 8 (by omega) (by omega) (by omega)
  have h147 := hno 1 4 7 (by omega) (by omega) (by omega)
  have h258 := hno 2 5 8 (by omega) (by omega) (by omega)
  have h345 := hno 3 4 5 (by omega) (by omega) (by omega)
  have h456 := hno 4 5 6 (by omega) (by omega) (by omega)
  have h1 : b 1 ≤ 1 := hb01 1
  have h2 : b 2 ≤ 1 := hb01 2
  have h3 : b 3 ≤ 1 := hb01 3
  have h4 : b 4 ≤ 1 := hb01 4
  have h5 : b 5 ≤ 1 := hb01 5
  have h6 : b 6 ≤ 1 := hb01 6
  have h7 : b 7 ≤ 1 := hb01 7
  have h8 : b 8 ≤ 1 := hb01 8
  omega

private lemma rK_four_seven_le_five : rK 4 7 ≤ 5 := by
  refine rK_le_of_forall fun A hA hf => ?_
  let b : ℕ → ℕ := fun n => if n ∈ A then 1 else 0
  have hAcard : A.card = b 1 + b 2 + b 3 + b 4 + b 5 + b 6 + b 7 := by
    have hsum : A.card = ∑ x ∈ Finset.Icc 1 7, b x := by
      rw [← Finset.sum_filter]
      have hfilt : (Finset.Icc 1 7).filter (· ∈ A) = A := by
        ext x
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun hx => ⟨hA hx, hx⟩⟩
      simp [hfilt]
    rw [hsum]
    have hIcc : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
    rw [hIcc]
    simp [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    ring
  rw [hAcard]
  have hno4 : ∀ a d : ℕ, 0 < d → b a + b (a + d) + b (a + 2 * d) + b (a + 3 * d) ≤ 3 := by
    intro a d hd
    by_cases h0 : a ∈ A <;> by_cases h1 : a + d ∈ A <;>
      by_cases h2 : a + 2 * d ∈ A <;> by_cases h3 : a + 3 * d ∈ A
    · exfalso
      apply hf a d hd
      intro i hi
      interval_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3
    all_goals simp [b, h0, h1, h2, h3]
  have h1234 : b 1 + b 2 + b 3 + b 4 ≤ 3 := by simpa using hno4 1 1 (by omega)
  have h4567 : b 4 + b 5 + b 6 + b 7 ≤ 3 := by simpa using hno4 4 1 (by omega)
  have h1357 : b 1 + b 3 + b 5 + b 7 ≤ 3 := by simpa using hno4 1 2 (by omega)
  have hb : ∀ n, b n ≤ 1 := fun n => by dsimp [b]; split_ifs <;> omega
  have h1 := hb 1; have h2 := hb 2; have h3 := hb 3; have h4 := hb 4
  have h5 := hb 5; have h6 := hb 6; have h7 := hb 7
  omega

private lemma witness_isKApFree_fin {k : ℕ} (hk : 2 ≤ k) {A : Finset ℕ} {N : ℕ}
    (hsub : A ⊆ Finset.Icc 1 N)
    (hdec : ∀ a ∈ Finset.Icc 1 N, ∀ d ∈ Finset.Icc 1 N, ¬ ∀ i ∈ Finset.range k, a + i * d ∈ A) :
    IsKApFree k A := by
  intro a d hd h
  have ha_mem : a ∈ A := by simpa using h 0 (by omega)
  have ha_icc : a ∈ Finset.Icc 1 N := hsub ha_mem
  have ha1_mem : a + d ∈ A := by simpa using h 1 (by omega)
  have ha1_le : a + d ≤ N := (Finset.mem_Icc.mp (hsub ha1_mem)).2
  have hd_icc : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hd, by omega⟩
  exact hdec a ha_icc d hd_icc fun i hi => h i (Finset.mem_range.mp hi)

/-- Exact small values of `r_3(N)` for `N = 1, ..., 9` (proved without `native_decide`):
`r_3(1..9) = 1, 2, 2, 3, 4, 4, 4, 4, 5`. -/
theorem rK_three_small_values :
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 1 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 1) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 2 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 2) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 3 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 2) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 4 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 3) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 5 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 4) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 6 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 4) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 7 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 4) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 8 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 4) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 9 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} = 5) := by
  change rK 3 1 = 1 ∧ rK 3 2 = 2 ∧ rK 3 3 = 2 ∧ rK 3 4 = 3 ∧
    rK 3 5 = 4 ∧ rK 3 6 = 4 ∧ rK 3 7 = 4 ∧ rK 3 8 = 4 ∧ rK 3 9 = 5
  have h1 : rK 3 1 = 1 := rK_eq_self_of_lt (by omega)
  have h2 : rK 3 2 = 2 := rK_eq_self_of_lt (by omega)
  have h3 : rK 3 3 = 2 := rK_self_eq_pred (by omega)
  have h4_le : rK 3 4 ≤ 3 := by
    have : rK 3 4 ≤ rK 3 3 + rK 3 1 := rK_subadditive 3 3 1
    omega
  have h4_ge : 3 ≤ rK 3 4 := by
    have hf : IsKApFree 3 ({1, 2, 4} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 4) (by decide) (by decide)
    exact le_trans (by decide : 3 ≤ ({1, 2, 4} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h4 : rK 3 4 = 3 := le_antisymm h4_le h4_ge
  have h5_ge : 4 ≤ rK 3 5 := by
    have hf : IsKApFree 3 ({1, 2, 4, 5} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 5) (by decide) (by decide)
    exact le_trans (by decide : 4 ≤ ({1, 2, 4, 5} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h8_le : rK 3 8 ≤ 4 := rK_three_eight_le_four
  have h56 : rK 3 5 ≤ rK 3 6 := rK_mono_N 3 5 6 (by omega)
  have h67 : rK 3 6 ≤ rK 3 7 := rK_mono_N 3 6 7 (by omega)
  have h78 : rK 3 7 ≤ rK 3 8 := rK_mono_N 3 7 8 (by omega)
  have h5 : rK 3 5 = 4 := by omega
  have h6 : rK 3 6 = 4 := by omega
  have h7 : rK 3 7 = 4 := by omega
  have h8 : rK 3 8 = 4 := by omega
  have h9_le : rK 3 9 ≤ 5 := by
    have : rK 3 9 ≤ rK 3 8 + rK 3 1 := rK_subadditive 3 8 1
    omega
  have h9_ge : 5 ≤ rK 3 9 := by
    have hf : IsKApFree 3 ({1, 2, 4, 8, 9} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 9) (by decide) (by decide)
    exact le_trans (by decide : 5 ≤ ({1, 2, 4, 8, 9} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h9 : rK 3 9 = 5 := le_antisymm h9_le h9_ge
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Exact small values of `r_4(N)` for `N = 1, ..., 10` (proved without `native_decide`):
`r_4(1..10) = 1, 2, 3, 3, 4, 5, 5, 6, 7, 8`. -/
theorem rK_four_small_values :
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 1 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 1) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 2 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 2) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 3 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 3) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 4 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 3) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 5 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 4) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 6 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 5) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 7 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 5) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 8 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 6) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 9 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 7) ∧
    (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 10 ∧ (∀ a d : ℕ, 0 < d → ¬ ∀ i < 4, a + i * d ∈ A) ∧ A.card = m} = 8) := by
  change rK 4 1 = 1 ∧ rK 4 2 = 2 ∧ rK 4 3 = 3 ∧ rK 4 4 = 3 ∧ rK 4 5 = 4 ∧
    rK 4 6 = 5 ∧ rK 4 7 = 5 ∧ rK 4 8 = 6 ∧ rK 4 9 = 7 ∧ rK 4 10 = 8
  have h1 : rK 4 1 = 1 := rK_eq_self_of_lt (by omega)
  have h2 : rK 4 2 = 2 := rK_eq_self_of_lt (by omega)
  have h3 : rK 4 3 = 3 := rK_eq_self_of_lt (by omega)
  have h4 : rK 4 4 = 3 := rK_self_eq_pred (by omega)
  have h5_le : rK 4 5 ≤ 4 := by
    have : rK 4 5 ≤ rK 4 4 + rK 4 1 := rK_subadditive 4 4 1
    omega
  have h5_ge : 4 ≤ rK 4 5 := by
    have hf : IsKApFree 4 ({1, 2, 3, 5} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 5) (by decide) (by decide)
    exact le_trans (by decide : 4 ≤ ({1, 2, 3, 5} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h5 : rK 4 5 = 4 := le_antisymm h5_le h5_ge
  have h6_ge : 5 ≤ rK 4 6 := by
    have hf : IsKApFree 4 ({1, 2, 3, 5, 6} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 6) (by decide) (by decide)
    exact le_trans (by decide : 5 ≤ ({1, 2, 3, 5, 6} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h7_le : rK 4 7 ≤ 5 := rK_four_seven_le_five
  have h67 : rK 4 6 ≤ rK 4 7 := rK_mono_N 4 6 7 (by omega)
  have h6 : rK 4 6 = 5 := by omega
  have h7 : rK 4 7 = 5 := by omega
  have h8_le : rK 4 8 ≤ 6 := by
    have : rK 4 8 ≤ rK 4 7 + rK 4 1 := rK_subadditive 4 7 1
    omega
  have h8_ge : 6 ≤ rK 4 8 := by
    have hf : IsKApFree 4 ({1, 2, 3, 5, 6, 8} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 8) (by decide) (by decide)
    exact le_trans (by decide : 6 ≤ ({1, 2, 3, 5, 6, 8} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h8 : rK 4 8 = 6 := le_antisymm h8_le h8_ge
  have h9_le : rK 4 9 ≤ 7 := by
    have : rK 4 9 ≤ rK 4 8 + rK 4 1 := rK_subadditive 4 8 1
    omega
  have h9_ge : 7 ≤ rK 4 9 := by
    have hf : IsKApFree 4 ({1, 2, 3, 5, 6, 8, 9} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 9) (by decide) (by decide)
    exact le_trans (by decide : 7 ≤ ({1, 2, 3, 5, 6, 8, 9} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h9 : rK 4 9 = 7 := le_antisymm h9_le h9_ge
  have h10_le : rK 4 10 ≤ 8 := by
    have : rK 4 10 ≤ rK 4 9 + rK 4 1 := rK_subadditive 4 9 1
    omega
  have h10_ge : 8 ≤ rK 4 10 := by
    have hf : IsKApFree 4 ({1, 2, 3, 5, 6, 8, 9, 10} : Finset ℕ) :=
      witness_isKApFree_fin (by omega) (N := 10) (by decide) (by decide)
    exact le_trans (by decide : 8 ≤ ({1, 2, 3, 5, 6, 8, 9, 10} : Finset ℕ).card) (card_le_rK (by decide) hf)
  have h10 : rK 4 10 = 8 := le_antisymm h10_le h10_ge
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end SmallValues

/-! ## Section 3: Sharp Behrend (1946) Constant & Rankin (1961) General-`k` Sphere-Packing Lower Bound -/

section BehrendAndRankin

private lemma base_repr_eq {b : ℕ} (hb : 2 ≤ b) :
    ∀ (d : ℕ) (u v : Fin d → ℕ),
      (∀ j, u j < b) → (∀ j, v j < b) →
      (∑ j : Fin d, u j * b ^ (j : ℕ)) = (∑ j : Fin d, v j * b ^ (j : ℕ)) →
      u = v
  | 0, u, v, _, _, _ => by
      funext j
      exact Fin.elim0 j
  | d + 1, u, v, hu, hv, heq => by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at heq
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ'] at heq
      have hpull : ∀ f : Fin d → ℕ,
          (∑ i : Fin d, f i * (b * b ^ (i : ℕ))) = b * (∑ i : Fin d, f i * b ^ (i : ℕ)) := by
        intro f
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hpull (fun i => u i.succ), hpull (fun i => v i.succ)] at heq
      have h0 : u 0 = v 0 := by
        have hmod := congrArg (· % b) heq
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (hu 0), Nat.mod_eq_of_lt (hv 0)] at hmod
        exact hmod
      have htail_eq :
          (∑ i : Fin d, u i.succ * b ^ (i : ℕ)) = (∑ i : Fin d, v i.succ * b ^ (i : ℕ)) := by
        have h1 : b * (∑ i : Fin d, u i.succ * b ^ (i : ℕ)) =
            b * (∑ i : Fin d, v i.succ * b ^ (i : ℕ)) := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega) h1
      have htail := base_repr_eq hb d (fun i => u i.succ) (fun i => v i.succ)
        (fun i => hu i.succ) (fun i => hv i.succ) htail_eq
      funext j
      refine Fin.cases h0 (fun i => congrFun htail i) j

private lemma geom_sum_mul_pred (b : ℕ) (hb : 1 ≤ b) :
    ∀ d : ℕ, (b - 1) * (∑ j : Fin d, b ^ (j : ℕ)) + 1 = b ^ d
  | 0 => by simp
  | d + 1 => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, mul_add]
      have ih := geom_sum_mul_pred b hb d
      have hmul : (b - 1) * b ^ d + b ^ d = b ^ (d + 1) := by
        rw [pow_succ']
        have : (b - 1 + 1) * b ^ d = b * b ^ d := by
          congr 1; omega
        linarith
      omega

private lemma base_repr_lt_pow {b d : ℕ} (hb : 2 ≤ b) (x : Fin d → ℕ) (hx : ∀ j, x j < b) :
    (∑ j : Fin d, x j * b ^ (j : ℕ)) < b ^ d := by
  have h1 : ∑ j : Fin d, x j * b ^ (j : ℕ) ≤ ∑ j : Fin d, (b - 1) * b ^ (j : ℕ) := by
    refine Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (by have := hx j; omega)
  rw [← Finset.mul_sum] at h1
  have h2 := geom_sum_mul_pred b (by omega) d
  omega

private lemma behrend_encode_le {m d : ℕ} (hm : 2 ≤ m) (x : Fin d → ℕ) (hx : ∀ j, x j < m) :
    1 + (∑ j : Fin d, x j * (2 * m - 1) ^ (j : ℕ)) ≤ (2 * m - 1) ^ d := by
  have hb : 2 ≤ 2 * m - 1 := by omega
  have h1 : 2 * (∑ j : Fin d, x j * (2 * m - 1) ^ (j : ℕ)) ≤
      (2 * m - 1 - 1) * (∑ j : Fin d, (2 * m - 1) ^ (j : ℕ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hxj : 2 * x j ≤ 2 * m - 1 - 1 := by have := hx j; omega
    calc
      2 * (x j * (2 * m - 1) ^ (j : ℕ)) = (2 * x j) * (2 * m - 1) ^ (j : ℕ) := by ring
      _ ≤ (2 * m - 1 - 1) * (2 * m - 1) ^ (j : ℕ) := Nat.mul_le_mul_right _ hxj
  have h2 := geom_sum_mul_pred (2 * m - 1) (by omega) d
  omega

private lemma one_sub_pow_ge_bernoulli {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ∀ n : ℕ, 1 - (n : ℝ) * u ≤ (1 - u) ^ n
  | 0 => by simp
  | n + 1 => by
      have ih := one_sub_pow_ge_bernoulli hu0 hu1 n
      have h1u : 0 ≤ 1 - u := by linarith
      have hstep : (1 - (n : ℝ) * u) * (1 - u) ≤ (1 - u) ^ n * (1 - u) :=
        mul_le_mul_of_nonneg_right ih h1u
      have hsq : 0 ≤ (n : ℝ) * u ^ 2 := by positivity
      rw [pow_succ]
      push_cast
      nlinarith

private lemma exp_ge_cube_div_27 {u : ℝ} (hu : 0 ≤ u) : u ^ 3 / 27 ≤ Real.exp u := by
  have h1 : u / 3 ≤ Real.exp (u / 3) := by linarith [Real.add_one_le_exp (u / 3)]
  have h2 : (u / 3) ^ 3 ≤ (Real.exp (u / 3)) ^ 3 :=
    pow_le_pow_left₀ (by linarith) h1 3
  have h3 : (Real.exp (u / 3)) ^ 3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h3] at h2
  linarith

/-- Finite exact Behrend (1946) sphere-packing lower bound:
for `d ≥ 1`, `m ≥ 2`, `(2 * m - 1)^d ≤ N`, `m^d ≤ r_3(N) * (d * (m - 1)^2 + 1)`. -/
private lemma behrend_finite {d m N : ℕ} (_hd : 1 ≤ d) (hm : 2 ≤ m)
    (hN : (2 * m - 1) ^ d ≤ N) :
    m ^ d ≤ rK 3 N * (d * (m - 1) ^ 2 + 1) := by
  classical
  let B : Finset (Fin d → ℕ) := Fintype.piFinset (fun _ : Fin d => Finset.range m)
  have hB_card : B.card = m ^ d := by
    simp [B]
  let sqNorm : (Fin d → ℕ) → ℕ := fun x => ∑ j : Fin d, (x j) ^ 2
  let T : ℕ := d * (m - 1) ^ 2
  have hmaps : ∀ x ∈ B, sqNorm x ∈ Finset.range (T + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hle : sqNorm x ≤ ∑ _j : Fin d, (m - 1) ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hxj : x j < m := Finset.mem_range.mp ((Fintype.mem_piFinset.mp hx) j)
      exact Nat.pow_le_pow_left (by omega) 2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  have hsum : ∑ r ∈ Finset.range (T + 1), (B.filter (fun x => sqNorm x = r)).card = B.card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      exact ⟨fun ⟨_, _, hx, _⟩ => hx, fun hx => ⟨sqNorm x, hmaps x hx, hx, rfl⟩⟩
    · intro r₁ _ r₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      exact hne ((Finset.mem_filter.mp hx₁).2.symm.trans (Finset.mem_filter.mp hx₂).2)
  have hpig : ∃ R ∈ Finset.range (T + 1),
      m ^ d ≤ (B.filter (fun x => sqNorm x = R)).card * (T + 1) := by
    by_contra hall
    push Not at hall
    have hlt : ∑ r ∈ Finset.range (T + 1), (B.filter (fun x => sqNorm x = r)).card * (T + 1) <
        ∑ _r ∈ Finset.range (T + 1), m ^ d := by
      refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (by omega)⟩ ?_
      intro r hr
      exact hall r hr
    rw [← Finset.sum_mul, hsum, hB_card, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt
    nlinarith
  rcases hpig with ⟨R, _, hR⟩
  let S : Finset (Fin d → ℕ) := B.filter (fun x => sqNorm x = R)
  let b : ℕ := 2 * m - 1
  have hb : 2 ≤ b := by omega
  let enc : (Fin d → ℕ) → ℕ := fun x => 1 + ∑ j : Fin d, x j * b ^ (j : ℕ)
  have henc_inj : Set.InjOn enc S := by
    intro x hx y hy hxy
    have hxB : ∀ j, x j < b := fun j => by
      have := Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) j)
      omega
    have hyB : ∀ j, y j < b := fun j => by
      have := Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hy).1) j)
      omega
    have hsum_eq : (∑ j : Fin d, x j * b ^ (j : ℕ)) = ∑ j : Fin d, y j * b ^ (j : ℕ) := by
      dsimp [enc] at hxy; omega
    exact base_repr_eq hb d x y hxB hyB hsum_eq
  let A : Finset ℕ := S.image enc
  have hA_card : A.card = S.card := Finset.card_image_of_injOn henc_inj
  have hA_sub : A ⊆ Finset.Icc 1 N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxB : ∀ j, x j < m := fun j =>
      Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) j)
    rw [Finset.mem_Icc]
    exact ⟨by dsimp [enc]; omega, le_trans (behrend_encode_le hm x hxB) hN⟩
  have hA_free : IsKApFree 3 A := by
    rw [isKApFree_three_iff_threeAPFree]
    intro u hu v hv w hw heq
    rcases Finset.mem_image.mp hu with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
    have hxB : ∀ j, x j < m := fun j =>
      Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) j)
    have hyB : ∀ j, y j < m := fun j =>
      Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hy).1) j)
    have hzB : ∀ j, z j < m := fun j =>
      Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hz).1) j)
    have hxR : sqNorm x = R := (Finset.mem_filter.mp hx).2
    have hyR : sqNorm y = R := (Finset.mem_filter.mp hy).2
    have hzR : sqNorm z = R := (Finset.mem_filter.mp hz).2
    have hsum_eq :
        (∑ j : Fin d, (x j + z j) * b ^ (j : ℕ)) = ∑ j : Fin d, (2 * y j) * b ^ (j : ℕ) := by
      have h1 : (∑ j : Fin d, x j * b ^ (j : ℕ)) + (∑ j : Fin d, z j * b ^ (j : ℕ)) =
          (∑ j : Fin d, y j * b ^ (j : ℕ)) + (∑ j : Fin d, y j * b ^ (j : ℕ)) := by
        dsimp [enc] at heq; omega
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib] at h1
      convert h1 using 2 with j
      · ring
      · ring
    have hcoord : (fun j => x j + z j) = (fun j => 2 * y j) :=
      base_repr_eq hb d _ _ (fun j => by have := hxB j; have := hzB j; omega)
        (fun j => by have := hyB j; omega) hsum_eq
    have hdiff_zero : ∑ j : Fin d, ((x j : ℤ) - (z j : ℤ)) ^ 2 = 0 := by
      have hident : ∀ j : Fin d,
          ((x j : ℤ) - (z j : ℤ)) ^ 2 =
            2 * (x j : ℤ) ^ 2 + 2 * (z j : ℤ) ^ 2 - 4 * (y j : ℤ) ^ 2 := by
        intro j
        have hcj : (x j : ℤ) + (z j : ℤ) = 2 * (y j : ℤ) := by
          have := congrFun hcoord j; exact_mod_cast this
        nlinarith
      simp_rw [hident, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      have hxR' : (∑ j : Fin d, (x j : ℤ) ^ 2) = (R : ℤ) := by exact_mod_cast hxR
      have hyR' : (∑ j : Fin d, (y j : ℤ) ^ 2) = (R : ℤ) := by exact_mod_cast hyR
      have hzR' : (∑ j : Fin d, (z j : ℤ) ^ 2) = (R : ℤ) := by exact_mod_cast hzR
      rw [hxR', hyR', hzR']; ring
    have hxz : x = z := by
      funext j
      have hsq0 : ((x j : ℤ) - (z j : ℤ)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).mp hdiff_zero j (Finset.mem_univ j)
      have hsub0 : (x j : ℤ) - (z j : ℤ) = 0 := sq_eq_zero_iff.mp hsq0
      omega
    have hxy : x = y := by
      funext j
      have hcj := congrFun hcoord j
      have hxj := congrFun hxz j
      omega
    rw [hxy]
  have hS_le : S.card ≤ rK 3 N := by
    rw [← hA_card]
    exact card_le_rK hA_sub hA_free
  exact le_trans hR (Nat.mul_le_mul_right _ hS_le)

/-- **Sharp Behrend (1946) Sphere-Packing Lower Bound (Strictly Improving Mathlib's `-4`):**
For every `ε > 0`, eventually for all `N ≥ N₀`,
`r_3(N) ≥ N * exp(-(2 * √(2 * log 2) + ε) * √(log N))`,
where `2 * √(2 * log 2) ≈ 2.35482` (compared to Mathlib's `Behrend.roth_lower_bound` constant `4`). -/
theorem behrend_sharp_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-(2 * Real.sqrt (2 * Real.log 2) + ε) * Real.sqrt (Real.log (N : ℝ))) ≤
        (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} : ℕ) := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt : Real.log 2 < 1 := by
    have : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    calc
      Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) this
      _ = 1 := Real.log_exp 1
  -- Choose threshold L₀ large enough that all elementary inequalities hold
  let C0 : ℝ := max 10000 (max (16 / ε ^ 2) (2000 / ε ^ 4))
  let N₀ : ℕ := Nat.ceil (Real.exp C0) + 10
  refine ⟨N₀, fun N hN => ?_⟩
  change (N : ℝ) * Real.exp (-(2 * Real.sqrt (2 * Real.log 2) + ε) * Real.sqrt (Real.log (N : ℝ))) ≤
    (rK 3 N : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hC0_ge : 10000 ≤ C0 := le_max_left _ _
  have hN_ge_exp : Real.exp C0 ≤ (N : ℝ) := by
    have h1 : Real.exp C0 ≤ (Nat.ceil (Real.exp C0) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp C0) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : Nat.ceil (Real.exp C0) ≤ N)
    linarith
  set L : ℝ := Real.log (N : ℝ)
  have hL_ge : C0 ≤ L := by
    have := Real.log_le_log (Real.exp_pos C0) hN_ge_exp
    rwa [Real.log_exp] at this
  have hL_pos : 0 < L := by linarith
  set x : ℝ := Real.sqrt (2 * L / Real.log 2)
  have hx_sq : x ^ 2 = 2 * L / Real.log 2 := Real.sq_sqrt (by positivity)
  have hx_ge : 100 ≤ x := by
    have h1 : (10000 : ℝ) ≤ 2 * L / Real.log 2 := by
      have : (2 * L) / 1 ≤ 2 * L / Real.log 2 :=
        div_le_div_of_nonneg_left (by linarith) hlog2_pos (le_of_lt hlog2_lt)
      linarith
    have h2 : Real.sqrt 10000 ≤ x := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt 10000 = 100 := by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  let d : ℕ := Nat.floor x
  have hd_le : (d : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hd_gt : x - 1 < (d : ℝ) := Nat.sub_one_lt_floor x
  have hd_ge4 : 4 ≤ d := by
    have : (4 : ℝ) ≤ (d : ℝ) := by linarith
    exact_mod_cast this
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  set R₀ : ℝ := (N : ℝ) ^ ((1 : ℝ) / (d : ℝ))
  have hR₀_eq : R₀ = Real.exp (L / (d : ℝ)) := by
    dsimp only [R₀, L]
    rw [Real.rpow_def_of_pos hN_pos]
    congr 1; ring
  have hR₀_pos : 0 < R₀ := by rw [hR₀_eq]; exact Real.exp_pos _
  -- Lower bound L / d ≥ √(L * log 2 / 2) and hence R₀ ≥ 8 * d
  have hLd_ge : Real.sqrt (L * Real.log 2 / 2) ≤ L / (d : ℝ) := by
    have h1 : L / x ≤ L / (d : ℝ) := div_le_div_of_nonneg_left (le_of_lt hL_pos) hd_pos hd_le
    have h2 : L / x = Real.sqrt (L * Real.log 2 / 2) := by
      have hxpos : 0 < x := by linarith
      rw [div_eq_iff (ne_of_gt hxpos)]
      have hprod : Real.sqrt (L * Real.log 2 / 2) * x =
          Real.sqrt ((L * Real.log 2 / 2) * (2 * L / Real.log 2)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [hprod]
      have hsimp : (L * Real.log 2 / 2) * (2 * L / Real.log 2) = L ^ 2 := by
        field_simp [ne_of_gt hlog2_pos]
      rw [hsimp, Real.sqrt_sq (le_of_lt hL_pos)]
    linarith
  have hR₀_ge_8d : 8 * (d : ℝ) ≤ R₀ := by
    have hu_nn : 0 ≤ L / (d : ℝ) := by positivity
    have hcube := exp_ge_cube_div_27 hu_nn
    rw [← hR₀_eq] at hcube
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hLd_sq : L / 4 ≤ (L / (d : ℝ)) ^ 2 := by
      have h1 : L * Real.log 2 / 2 ≤ (L / (d : ℝ)) ^ 2 := by
        have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hLd_ge 2
        rwa [Real.sq_sqrt (by positivity)] at hsq
      nlinarith
    have hLd_ge4 : 20 ≤ L / (d : ℝ) := by
      have : (20 : ℝ) ^ 2 ≤ (L / (d : ℝ)) ^ 2 := by linarith
      nlinarith
    have hLd_cube : 5 * L ≤ (L / (d : ℝ)) ^ 3 := by nlinarith
    -- Also x ≤ 2 * √L so d ≤ 2 * √L and 8 * d ≤ 16 * √L ≤ 5 * L / 27
    have hx_le : x ≤ 2 * Real.sqrt L := by
      have h1 : 2 * L / Real.log 2 ≤ 4 * L := by
        rw [div_le_iff₀ hlog2_pos]; nlinarith
      calc
        x ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt h1
        _ = 2 * Real.sqrt L := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hsqrtL_le : Real.sqrt L ≤ L / 100 := by
      have : (100 : ℝ) ^ 2 ≤ L := by linarith
      have hs : 100 ≤ Real.sqrt L := by
        have := Real.sqrt_le_sqrt this
        rwa [Real.sqrt_sq (by norm_num)] at this
      have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL_pos)
      nlinarith
    nlinarith
  let m : ℕ := Nat.floor (R₀ / 2)
  have hm_le : (m : ℝ) ≤ R₀ / 2 := Nat.floor_le (by linarith)
  have hm_gt : R₀ / 2 - 1 < (m : ℝ) := Nat.sub_one_lt_floor (R₀ / 2)
  have hm_ge2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ (m : ℝ) := by linarith [show (4 : ℝ) ≤ (d : ℝ) by exact_mod_cast hd_ge4]
    exact_mod_cast this
  have hpow_le_N : (2 * m - 1) ^ d ≤ N := by
    have h1 : ((2 * m - 1 : ℕ) : ℝ) ≤ R₀ := by
      have h2m : (2 * m : ℝ) ≤ R₀ := by linarith
      have : ((2 * m - 1 : ℕ) : ℝ) ≤ (2 * m : ℝ) := by exact_mod_cast Nat.sub_le (2 * m) 1
      linarith
    have h2 : (((2 * m - 1) ^ d : ℕ) : ℝ) ≤ R₀ ^ d := by
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h1 d
    have hR₀_pow : R₀ ^ d = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN_pos)]
      have : (1 : ℝ) / (d : ℝ) * (d : ℝ) = 1 := one_div_mul_cancel (ne_of_gt hd_pos)
      rw [this, Real.rpow_one]
    rw [hR₀_pow] at h2
    exact_mod_cast h2
  have hfin := behrend_finite (by omega : 1 ≤ d) hm_ge2 hpow_le_N
  have hden_le : d * (m - 1) ^ 2 + 1 ≤ d * m ^ 2 := by
    have h1 : (m - 1) + 1 = m := by omega
    have h2 : (m - 1) ^ 2 + 1 ≤ m ^ 2 := by nlinarith
    nlinarith
  have hfin_real : (m : ℝ) ^ d ≤ (rK 3 N : ℝ) * ((d : ℝ) * (m : ℝ) ^ 2) := by
    have h1 : m ^ d ≤ rK 3 N * (d * m ^ 2) :=
      le_trans hfin (Nat.mul_le_mul_left _ hden_le)
    exact_mod_cast h1
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hrK_ge : (m : ℝ) ^ (d - 2) / (d : ℝ) ≤ (rK 3 N : ℝ) := by
    rw [div_le_iff₀ hd_pos]
    have hsplit : (m : ℝ) ^ (d - 2) * (m : ℝ) ^ 2 = (m : ℝ) ^ d := by
      rw [← pow_add]
      congr 1; omega
    have h1 : (m : ℝ) ^ (d - 2) * (m : ℝ) ^ 2 ≤ (rK 3 N : ℝ) * (d : ℝ) * (m : ℝ) ^ 2 := by
      linarith
    exact le_of_mul_le_mul_right h1 (by positivity)
  -- Lower bound m^(d - 2) via Bernoulli's inequality
  have hm_fac : (R₀ / 2) * (1 - 2 / R₀) ≤ (m : ℝ) := by
    have : (R₀ / 2) * (1 - 2 / R₀) = R₀ / 2 - 1 := by field_simp [ne_of_gt hR₀_pos]
    linarith
  have hbern : (1 / 2 : ℝ) ≤ (1 - 2 / R₀) ^ (d - 2) := by
    have hu0 : 0 ≤ 2 / R₀ := by positivity
    have hu1 : 2 / R₀ ≤ 1 := by rw [div_le_one hR₀_pos]; linarith
    have hb := one_sub_pow_ge_bernoulli hu0 hu1 (d - 2)
    have hle : ((d - 2 : ℕ) : ℝ) * (2 / R₀) ≤ 1 / 2 := by
      have hd2 : ((d - 2 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d 2
      have h2 : (d : ℝ) * (2 / R₀) ≤ 1 / 4 := by
        rw [← mul_div_assoc, div_le_iff₀ hR₀_pos]; linarith
      nlinarith only [hd2, h2, hu0]
    linarith
  have hm_pow_ge : (1 / 2 : ℝ) * (R₀ / 2) ^ (d - 2) ≤ (m : ℝ) ^ (d - 2) := by
    have h1 : ((R₀ / 2) * (1 - 2 / R₀)) ^ (d - 2) ≤ (m : ℝ) ^ (d - 2) := by
      have h0 : 0 ≤ (R₀ / 2) * (1 - 2 / R₀) := by
        have : (R₀ / 2) * (1 - 2 / R₀) = R₀ / 2 - 1 := by field_simp [ne_of_gt hR₀_pos]
        linarith
      exact pow_le_pow_left₀ h0 hm_fac (d - 2)
    rw [mul_pow] at h1
    have h2 : (1 / 2 : ℝ) * (R₀ / 2) ^ (d - 2) ≤ (R₀ / 2) ^ (d - 2) * (1 - 2 / R₀) ^ (d - 2) := by
      have hnn := pow_nonneg (show 0 ≤ R₀ / 2 by linarith) (d - 2)
      nlinarith only [hbern, hnn]
    linarith
  -- Rewrite (1/2) * (R₀ / 2)^(d - 2) / d = (2 / d) * N * exp(-(d * log 2 + 2 * L / d))
  have hR₀_d_eq : (R₀ / 2) ^ (d - 2) = 4 * (N : ℝ) * Real.exp (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ)) := by
    have hpow2 : (2 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hR₀_d : R₀ ^ d = (N : ℝ) := by
      dsimp only [R₀]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN_pos)]
      rw [one_div_mul_cancel (ne_of_gt hd_pos), Real.rpow_one]
    have hR₀_sq : R₀ ^ 2 = Real.exp (2 * L / (d : ℝ)) := by
      rw [hR₀_eq, ← Real.exp_nat_mul]; congr 1; ring
    have hsplit_R : R₀ ^ (d - 2) * R₀ ^ 2 = (N : ℝ) := by
      rw [← pow_add, show d - 2 + 2 = d by omega, hR₀_d]
    have hsplit_2 : (2 : ℝ) ^ (d - 2) * 4 = (2 : ℝ) ^ d := by
      have : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [this, ← pow_add, show d - 2 + 2 = d by omega]
    rw [div_pow, show -(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ) = -((d : ℝ) * Real.log 2) + -(2 * L / (d : ℝ)) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_neg, ← hpow2, ← hR₀_sq]
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (d - 2) := by positivity
    have h2dpos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    have hRsqpos : (0 : ℝ) < R₀ ^ 2 := by positivity
    have hRsub : R₀ ^ (d - 2) = (N : ℝ) / R₀ ^ 2 := eq_div_of_mul_eq (ne_of_gt hRsqpos) hsplit_R
    have h2sub : (2 : ℝ) ^ (d - 2) = (2 : ℝ) ^ d / 4 := eq_div_of_mul_eq (by norm_num) hsplit_2
    rw [hRsub, h2sub]
    field_simp [ne_of_gt h2dpos, ne_of_gt hRsqpos]
  have hcomb : (N : ℝ) * Real.exp (-((d : ℝ) * Real.log 2 + 2 * L / (d : ℝ) + Real.log (d : ℝ))) ≤ (rK 3 N : ℝ) := by
    have h1 : (2 / (d : ℝ)) * (N : ℝ) * Real.exp (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ)) ≤ (rK 3 N : ℝ) := by
      have hdiv : ((1 / 2 : ℝ) * (R₀ / 2) ^ (d - 2)) / (d : ℝ) ≤ (m : ℝ) ^ (d - 2) / (d : ℝ) :=
        div_le_div_of_nonneg_right hm_pow_ge (le_of_lt hd_pos)
      rw [hR₀_d_eq] at hdiv
      have hsimp : (1 / 2 : ℝ) * (4 * (N : ℝ) * Real.exp (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ))) / (d : ℝ) =
          (2 / (d : ℝ)) * (N : ℝ) * Real.exp (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ)) := by ring
      linarith
    have h2 : (N : ℝ) * Real.exp (-((d : ℝ) * Real.log 2 + 2 * L / (d : ℝ) + Real.log (d : ℝ))) =
        (1 / (d : ℝ)) * (N : ℝ) * Real.exp (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ)) := by
      rw [show -((d : ℝ) * Real.log 2 + 2 * L / (d : ℝ) + Real.log (d : ℝ)) =
        (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ)) + (-Real.log (d : ℝ)) by ring,
        Real.exp_add, Real.exp_neg, Real.exp_log hd_pos]
      ring
    rw [h2]
    have hnn : 0 ≤ (N : ℝ) * Real.exp (-(d : ℝ) * Real.log 2 - 2 * L / (d : ℝ)) := by positivity
    have h12 : (1 / (d : ℝ)) ≤ (2 / (d : ℝ)) := by
      exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hd_pos)
    nlinarith
  -- Finally bound the exponent: d * log 2 + 2 * L / d + log d ≤ (2 * √(2 * log 2) + ε) * √L
  have hexp_le : (d : ℝ) * Real.log 2 + 2 * L / (d : ℝ) + Real.log (d : ℝ) ≤
      (2 * Real.sqrt (2 * Real.log 2) + ε) * Real.sqrt L := by
    have hsqrt_prod : Real.sqrt (2 * Real.log 2) * Real.sqrt L = x * Real.log 2 := by
      have h1 : Real.sqrt (2 * Real.log 2) * Real.sqrt L = Real.sqrt (2 * Real.log 2 * L) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h2 : x * Real.log 2 = Real.sqrt (2 * L / Real.log 2) * Real.sqrt ((Real.log 2) ^ 2) := by
        rw [Real.sqrt_sq (le_of_lt hlog2_pos)]
      rw [h1, h2, ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp [ne_of_gt hlog2_pos]
    have hterm1 : (d : ℝ) * Real.log 2 ≤ Real.sqrt (2 * Real.log 2) * Real.sqrt L := by
      rw [hsqrt_prod]
      exact mul_le_mul_of_nonneg_right hd_le (le_of_lt hlog2_pos)
    have h2L_div_x : 2 * L / x = Real.sqrt (2 * Real.log 2) * Real.sqrt L := by
      rw [hsqrt_prod, div_eq_iff (by linarith)]
      have : x * Real.log 2 * x = x ^ 2 * Real.log 2 := by ring
      rw [this, hx_sq]
      field_simp [ne_of_gt hlog2_pos]
    have hterm2 : 2 * L / (d : ℝ) ≤ Real.sqrt (2 * Real.log 2) * Real.sqrt L + 2 := by
      have hdiff : 2 * L / (d : ℝ) - 2 * L / x = 2 * L * (x - (d : ℝ)) / ((d : ℝ) * x) := by
        field_simp [ne_of_gt hd_pos, show x ≠ 0 by linarith only [hx_ge]]
      have hxd : x - (d : ℝ) ≤ 1 := by linarith only [hd_gt]
      have hdx : x ^ 2 / 2 ≤ (d : ℝ) * x := by
        have hx2 : x / 2 ≤ (d : ℝ) := by linarith only [hx_ge, hd_gt]
        have hxpos : 0 ≤ x := by linarith only [hx_ge]
        nlinarith only [hx2, hxpos]
      have hbound : 2 * L * (x - (d : ℝ)) / ((d : ℝ) * x) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have h2L : 2 * L = x ^ 2 * Real.log 2 := by
          rw [hx_sq]; field_simp [ne_of_gt hlog2_pos]
        have hx2nn : 0 ≤ x ^ 2 := sq_nonneg x
        have h2L_le : 2 * L ≤ x ^ 2 := by nlinarith only [h2L, hlog2_lt, hx2nn]
        have h2L_nn : 0 ≤ 2 * L := by linarith only [hL_pos]
        nlinarith only [h2L_le, h2L_nn, hxd, hdx]
      linarith only [hdiff, h2L_div_x, hbound]
    have hterm3 : Real.log (d : ℝ) ≤ 2 * Real.sqrt (d : ℝ) := by
      have hsq : Real.log (d : ℝ) = 2 * Real.log (Real.sqrt (d : ℝ)) := by
        conv_lhs => rw [← Real.sq_sqrt (le_of_lt hd_pos)]
        rw [Real.log_pow]; ring
      have hle := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hd_pos)
      linarith only [hsq, hle]
    have h2_le : (2 : ℝ) ≤ (ε / 2) * Real.sqrt L := by
      have h1 : 16 / ε ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL_ge
      have h2 : (4 / ε) ^ 2 ≤ L := by
        have : (4 / ε) ^ 2 = 16 / ε ^ 2 := by ring
        linarith only [this, h1]
      have h3 : 4 / ε ≤ Real.sqrt L := by
        have := Real.sqrt_le_sqrt h2
        rwa [Real.sqrt_sq (by positivity)] at this
      have h4 : 4 ≤ Real.sqrt L * ε := (div_le_iff₀ hε).mp h3
      linarith only [h4]
    have hsqrt_d_le : 2 * Real.sqrt (d : ℝ) ≤ (ε / 2) * Real.sqrt L := by
      have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
      have hx_le : x ≤ 2 * Real.sqrt L := by
        have h1 : 2 * L / Real.log 2 ≤ 4 * L := by
          rw [div_le_iff₀ hlog2_pos]; nlinarith only [hlog2_ge, hL_pos]
        calc
          x ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt h1
          _ = 2 * Real.sqrt L := by
            rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hd_le2 : (d : ℝ) ≤ 2 * Real.sqrt L := le_trans hd_le hx_le
      have hL_ge4 : 2000 / ε ^ 4 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL_ge
      have h1 : 32 * Real.sqrt L ≤ ε ^ 2 * L := by
        have hsqL_ge : 32 / ε ^ 2 ≤ Real.sqrt L := by
          have hsq : (32 / ε ^ 2) ^ 2 ≤ L := by
            have heq : (32 / ε ^ 2) ^ 2 = 1024 / ε ^ 4 := by ring
            have hle : 1024 / ε ^ 4 ≤ 2000 / ε ^ 4 :=
              div_le_div_of_nonneg_right (by norm_num) (by positivity)
            linarith only [heq, hle, hL_ge4]
          have := Real.sqrt_le_sqrt hsq
          rwa [Real.sqrt_sq (by positivity)] at this
        have hmul : 32 ≤ Real.sqrt L * ε ^ 2 := (div_le_iff₀ (by positivity)).mp hsqL_ge
        have hsq_eq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (le_of_lt hL_pos)
        have hnn := Real.sqrt_nonneg L
        nlinarith only [hmul, hsq_eq, hnn]
      have hsq_goal : (2 * Real.sqrt (d : ℝ)) ^ 2 ≤ ((ε / 2) * Real.sqrt L) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hd_pos), mul_pow, Real.sq_sqrt (le_of_lt hL_pos)]
        linarith only [hd_le2, h1]
      have hnn1 : 0 ≤ 2 * Real.sqrt (d : ℝ) := by positivity
      have hnn2 : 0 ≤ (ε / 2) * Real.sqrt L := by positivity
      nlinarith only [hsq_goal, hnn1, hnn2]
    linarith only [hterm1, hterm2, hterm3, h2_le, hsqrt_d_le]
  have hmono : Real.exp (-(2 * Real.sqrt (2 * Real.log 2) + ε) * Real.sqrt L) ≤
      Real.exp (-((d : ℝ) * Real.log 2 + 2 * L / (d : ℝ) + Real.log (d : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left hmono (le_of_lt hN_pos)) hcomb

/-- Concrete explicit constant `-5/2 = -2.5` strictly improving Mathlib's `-4`:
eventually `r_3(N) ≥ N * exp(-2.5 * √(log N))`. -/
theorem behrend_lower_bound_two_point_five :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-(5 / 2 : ℝ) * Real.sqrt (Real.log (N : ℝ))) ≤
        (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} : ℕ) := by
  have hlt : 2 * Real.sqrt (2 * Real.log 2) < (5 / 2 : ℝ) := by
    have hlog2 : Real.log 2 < 7 / 10 := by linarith [Real.log_two_lt_d9]
    have hsq : (2 * Real.sqrt (2 * Real.log 2)) ^ 2 < (5 / 2 : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      linarith
    nlinarith [Real.sqrt_nonneg (2 * Real.log 2)]
  obtain ⟨N₀, hN₀⟩ := behrend_sharp_lower_bound ((5 / 2 : ℝ) - 2 * Real.sqrt (2 * Real.log 2)) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h := hN₀ N hN
  have hsimp : -(2 * Real.sqrt (2 * Real.log 2) + ((5 / 2 : ℝ) - 2 * Real.sqrt (2 * Real.log 2))) = -(5 / 2 : ℝ) := by ring
  simpa [hsimp] using h

/-! ### Part 3B: Rankin (1961) General-`k` Sphere-Packing Lower Bound -/

private def PolyAPFree (D k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ P : Polynomial ℚ, P.natDegree ≤ D →
    (∀ i < k, ∃ n ∈ A, (n : ℚ) = P.eval (i : ℚ)) → P.natDegree = 0

private lemma polyAPFree_one_imp_isKApFree {k : ℕ} {A : Finset ℕ} (h : PolyAPFree 1 k A) :
    IsKApFree k A := by
  intro a d hd hmem
  let P : Polynomial ℚ := Polynomial.C (a : ℚ) + Polynomial.C (d : ℚ) * Polynomial.X
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hdeg : P.natDegree = 1 := by
    have h1 : P = Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (a : ℚ) := by ring
    rw [h1, Polynomial.natDegree_add_C, Polynomial.natDegree_C_mul hd0, Polynomial.natDegree_X]
  have hval : ∀ i < k, ∃ n ∈ A, (n : ℚ) = P.eval (i : ℚ) := by
    intro i hi
    refine ⟨a + i * d, hmem i hi, ?_⟩
    simp [P]
    ring
  have h0 := h P (by omega) hval
  omega

private lemma polyAPFree_singleton {D k : ℕ} (hDk : D < k) : PolyAPFree D k {0} := by
  intro P hdeg hval
  by_cases hP : P = 0
  · simp [hP]
  · exfalso
    have hroots : ∀ i ∈ Finset.range k, (i : ℚ) ∈ P.roots := by
      intro i hi
      rw [Polynomial.mem_roots hP, Polynomial.IsRoot.def]
      rcases hval i (Finset.mem_range.mp hi) with ⟨n, hn, heq⟩
      have hn0 : n = 0 := Finset.mem_singleton.mp hn
      subst hn0
      simpa using heq.symm
    let S : Finset ℚ := (Finset.range k).image (fun i : ℕ => (i : ℚ))
    have hS_card : S.card = k := by
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    have hS_sub : S.val ⊆ P.roots := by
      intro q hq
      rcases Finset.mem_image.mp (Finset.mem_val.mp hq) with ⟨i, hi, rfl⟩
      exact hroots i hi
    have hcard_le : S.card ≤ P.roots.card := by
      have hnd : S.val.Nodup := S.nodup
      have := Multiset.le_iff_subset hnd |>.mpr hS_sub
      exact Multiset.card_le_card this
    have hroots_le : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
    omega

private lemma polyAPFree_image_add {D k T : ℕ} {A : Finset ℕ} (hA : PolyAPFree D k A) :
    PolyAPFree D k (A.image (· + T)) := by
  intro P hdeg hval
  let Q : Polynomial ℚ := P - Polynomial.C (T : ℚ)
  have hQdeg : Q.natDegree = P.natDegree := by
    dsimp only [Q]
    rw [sub_eq_add_neg, ← map_neg]
    exact Polynomial.natDegree_add_C
  have hQval : ∀ i < k, ∃ n ∈ A, (n : ℚ) = Q.eval (i : ℚ) := by
    intro i hi
    rcases hval i hi with ⟨m, hm, hmeq⟩
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    refine ⟨n, hn, ?_⟩
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_C]
    push_cast at hmeq
    linarith
  have hQ0 := hA Q (by omega) hQval
  omega

private def fwdDiff : ℕ → (ℕ → ℚ) → ℕ → ℚ
  | 0, f, n => f n
  | r + 1, f, n => fwdDiff r f (n + 1) - fwdDiff r f n

private lemma fwdDiff_eq_sum :
    ∀ (r : ℕ) (f : ℕ → ℚ) (n : ℕ),
      fwdDiff r f n = ∑ j ∈ Finset.range (r + 1), (-1 : ℚ) ^ (r - j) * (Nat.choose r j : ℚ) * f (n + j)
  | 0, f, n => by simp [fwdDiff]
  | r + 1, f, n => by
      simp only [fwdDiff]
      rw [fwdDiff_eq_sum r f (n + 1), fwdDiff_eq_sum r f n]
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      rw [Finset.sum_range_succ']
      have htail :
          (∑ j ∈ Finset.range r, (-1 : ℚ) ^ (r - j) * (Nat.choose r j : ℚ) * f (n + 1 + j)) -
          (∑ j ∈ Finset.range r, (-1 : ℚ) ^ (r - (j + 1)) * (Nat.choose r (j + 1) : ℚ) * f (n + (j + 1))) =
          ∑ j ∈ Finset.range r,
            (-1 : ℚ) ^ (r + 1 - (j + 1)) * (Nat.choose (r + 1) (j + 1) : ℚ) * f (n + (j + 1)) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjr : j < r := Finset.mem_range.mp hj
        have h1 : r + 1 - (j + 1) = r - j := by omega
        have h2 : r - j = (r - (j + 1)) + 1 := by omega
        have hchoose : (Nat.choose (r + 1) (j + 1) : ℚ) = (Nat.choose r j : ℚ) + (Nat.choose r (j + 1) : ℚ) := by
          exact_mod_cast Nat.choose_succ_succ r j
        have hadd : n + 1 + j = n + (j + 1) := by omega
        rw [h1, hadd, hchoose, h2, pow_succ]
        ring
      have h0 : (-1 : ℚ) ^ (r + 1 - 0) * (Nat.choose (r + 1) 0 : ℚ) * f (n + 0) =
          -((-1 : ℚ) ^ (r - 0) * (Nat.choose r 0 : ℚ) * f (n + 0)) := by
        simp [pow_succ]
      have hlast : (-1 : ℚ) ^ (r + 1 - (r + 1)) * (Nat.choose (r + 1) (r + 1) : ℚ) * f (n + (r + 1)) =
          (-1 : ℚ) ^ (r - r) * (Nat.choose r r : ℚ) * f (n + 1 + r) := by
        have : n + (r + 1) = n + 1 + r := by omega
        simp [this]
      rw [Finset.sum_range_succ, h0, hlast, ← htail]
      ring

private lemma poly_comp_X_add_one_sub_natDegree_le {D : ℕ} (P : Polynomial ℚ) (hP : P.natDegree ≤ D + 1) :
    (P.comp (Polynomial.X + 1) - P).natDegree ≤ D := by
  by_cases hzero : P.comp (Polynomial.X + 1) - P = 0
  · simp [hzero]
  · refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    have hk1 : D + 1 ≤ k := by omega
    rw [Polynomial.coeff_sub]
    by_cases hgt : D + 1 < k
    · have hc1 : (P.comp (Polynomial.X + 1)).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hcd : (P.comp (Polynomial.X + 1)).natDegree ≤ P.natDegree * (Polynomial.X + 1 : Polynomial ℚ).natDegree :=
          Polynomial.natDegree_comp_le
        have hX1 : (Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
          simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
        rw [hX1, mul_one] at hcd
        omega
      have hc2 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hc1, hc2, sub_self]
    · have hkeq : k = D + 1 := by omega
      subst hkeq
      -- Show (P.comp (X + 1)).coeff (D + 1) = P.coeff (D + 1)
      have hcomp_coeff : ∀ (Q : Polynomial ℚ), Q.natDegree ≤ D + 1 →
          (Q.comp (Polynomial.X + 1)).coeff (D + 1) = Q.coeff (D + 1) := by
        intro Q hQ
        rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
        have hX1 : (Polynomial.X + 1 : Polynomial ℚ).natDegree = 1 := by
          simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
        have hterm : ∀ i ∈ Q.support,
            (Polynomial.C (Q.coeff i) * (Polynomial.X + 1) ^ i).coeff (D + 1) =
              if i = D + 1 then Q.coeff (D + 1) else 0 := by
          intro i hi
          have hi_le : i ≤ D + 1 := le_trans (Polynomial.le_natDegree_of_mem_supp i hi) hQ
          rw [Polynomial.coeff_C_mul]
          split_ifs with heq
          · subst heq
            have hmon : ((Polynomial.X + 1 : Polynomial ℚ) ^ (D + 1)).Monic :=
              (Polynomial.monic_X_add_C (1 : ℚ)).pow (D + 1)
            have hdeg : ((Polynomial.X + 1 : Polynomial ℚ) ^ (D + 1)).natDegree = D + 1 := by
              rw [Polynomial.natDegree_pow, hX1, mul_one]
            have hc := hmon.coeff_natDegree
            rw [hdeg] at hc
            rw [hc, mul_one]
          · have hlt : i < D + 1 := by omega
            have hdeg : ((Polynomial.X + 1 : Polynomial ℚ) ^ i).natDegree < D + 1 := by
              rw [Polynomial.natDegree_pow, hX1, mul_one]
              exact hlt
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
        rw [Finset.sum_congr rfl hterm]
        by_cases hmem : D + 1 ∈ Q.support
        · simp [hmem]
        · simp [Polynomial.notMem_support_iff.mp hmem]
      rw [hcomp_coeff P hP, sub_self]

private lemma fwdDiff_poly_zero :
    ∀ (D : ℕ) (P : Polynomial ℚ), P.natDegree ≤ D →
      ∀ n : ℕ, fwdDiff (D + 1) (fun i => P.eval (i : ℚ)) n = 0
  | 0, P, hP, n => by
      have hconst := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hP)
      rw [hconst]
      simp [fwdDiff]
  | D + 1, P, hP, n => by
      let Q : Polynomial ℚ := P.comp (Polynomial.X + 1) - P
      have hQdeg : Q.natDegree ≤ D := poly_comp_X_add_one_sub_natDegree_le P hP
      have hshift : ∀ r m, fwdDiff (r + 1) (fun i => P.eval (i : ℚ)) m =
          fwdDiff r (fun i => Q.eval (i : ℚ)) m := by
        intro r
        induction r with
        | zero =>
            intro m
            simp [fwdDiff, Q, Polynomial.eval_comp, Nat.cast_add, Nat.cast_one]
        | succ r ih =>
            intro m
            change fwdDiff (r + 1) (fun i => P.eval (i : ℚ)) (m + 1) -
              fwdDiff (r + 1) (fun i => P.eval (i : ℚ)) m =
              fwdDiff r (fun i => Q.eval (i : ℚ)) (m + 1) -
              fwdDiff r (fun i => Q.eval (i : ℚ)) m
            rw [ih (m + 1), ih m]
      rw [hshift (D + 1) n]
      exact fwdDiff_poly_zero D Q hQdeg n

private lemma exists_poly_antidiff_aux :
    ∀ (d : ℕ) (Q : Polynomial ℚ), Q.natDegree ≤ d →
      ∃ R : Polynomial ℚ, R.natDegree ≤ d + 1 ∧ R.comp (Polynomial.X + 1) - R = Q
  | 0, Q, hQ => by
      have hQeq := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hQ)
      refine ⟨Polynomial.C (Q.coeff 0) * Polynomial.X, ?_, ?_⟩
      · exact le_trans Polynomial.natDegree_mul_le (by simp)
      · rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        conv_rhs => rw [hQeq]
        ring
  | d + 1, Q, hQ => by
      let c : ℚ := Q.coeff (d + 1) / ((d + 2 : ℕ) : ℚ)
      let S : Polynomial ℚ := Polynomial.C c * Polynomial.X ^ (d + 2)
      have hSdeg : S.natDegree ≤ d + 2 := by
        calc
          S.natDegree ≤ (Polynomial.C c).natDegree + (Polynomial.X ^ (d + 2) : Polynomial ℚ).natDegree :=
            Polynomial.natDegree_mul_le
          _ = d + 2 := by simp
      let ΔS : Polynomial ℚ := S.comp (Polynomial.X + 1) - S
      have hΔS_deg : ΔS.natDegree ≤ d + 1 := poly_comp_X_add_one_sub_natDegree_le S hSdeg
      have hΔS_coeff : ΔS.coeff (d + 1) = Q.coeff (d + 1) := by
        have hScomp : S.comp (Polynomial.X + 1) = Polynomial.C c * (Polynomial.X + 1) ^ (d + 2) := by
          simp [S]
        rw [show ΔS = S.comp (Polynomial.X + 1) - S from rfl, hScomp,
          Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow]
        have hne : d + 1 ≠ d + 2 := by omega
        simp only [hne, ↓reduceIte, mul_zero, sub_zero]
        have hbin : ((Polynomial.X + 1 : Polynomial ℚ) ^ (d + 2)).coeff (d + 1) = ((d + 2 : ℕ) : ℚ) := by
          rw [add_pow, Polynomial.finsetSum_coeff]
          have hterm : ∀ k ∈ Finset.range (d + 3),
              (Polynomial.X ^ k * (1 : Polynomial ℚ) ^ (d + 2 - k) * (Nat.choose (d + 2) k : Polynomial ℚ)).coeff (d + 1) =
                if k = d + 1 then (Nat.choose (d + 2) (d + 1) : ℚ) else 0 := by
            intro k _
            rw [one_pow, mul_one, mul_comm, ← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul,
              Polynomial.coeff_X_pow]
            by_cases hkd : k = d + 1
            · subst hkd; simp
            · simp [hkd, Ne.symm hkd]
          rw [show d + 2 + 1 = d + 3 by omega, Finset.sum_congr rfl hterm]
          have hmem : d + 1 ∈ Finset.range (d + 3) := Finset.mem_range.mpr (by omega)
          rw [Finset.sum_ite_eq' _ _ _, if_pos hmem]
          have hch : Nat.choose (d + 2) (d + 1) = d + 2 := by
            simp [Nat.choose_succ_self_right]
          exact_mod_cast hch
        rw [hbin]
        dsimp [c]
        have hnz : ((d + 2 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hnz]
      let Q' : Polynomial ℚ := Q - ΔS
      have hQ'deg : Q'.natDegree ≤ d := by
        refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
        rw [Polynomial.coeff_sub]
        by_cases hkeq : k = d + 1
        · subst hkeq; rw [hΔS_coeff, sub_self]
        · have hkgt : d + 1 < k := by omega
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ hkgt),
            Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hΔS_deg hkgt), sub_self]
      obtain ⟨R', hR'deg, hR'eq⟩ := exists_poly_antidiff_aux d Q' hQ'deg
      refine ⟨S + R', ?_, ?_⟩
      · exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hSdeg (by omega))
      · rw [Polynomial.add_comp]
        have : (S.comp (Polynomial.X + 1) + R'.comp (Polynomial.X + 1)) - (S + R') =
            ΔS + (R'.comp (Polynomial.X + 1) - R') := by ring
        rw [this, hR'eq]
        dsimp [Q']
        ring

private lemma exists_poly_of_fwdDiff_zero :
    ∀ (D k : ℕ) (f : ℕ → ℚ),
      (∀ n, n + D + 1 < k → fwdDiff (D + 1) f n = 0) →
      ∃ P : Polynomial ℚ, P.natDegree ≤ D ∧ ∀ i < k, P.eval (i : ℚ) = f i
  | 0, k, f, hf => by
      refine ⟨Polynomial.C (f 0), by simp, ?_⟩
      intro i hi
      induction i with
      | zero => simp
      | succ i ih =>
          have hstep := hf i (by omega)
          simp only [fwdDiff] at hstep
          have hprev := ih (by omega)
          simp only [Polynomial.eval_C] at hprev ⊢
          linarith
  | D + 1, k, f, hf => by
      let g : ℕ → ℚ := fun n => f (n + 1) - f n
      have hshift : ∀ r m, fwdDiff (r + 1) f m = fwdDiff r g m := by
        intro r
        induction r with
        | zero => intro m; rfl
        | succ r ih =>
            intro m
            change fwdDiff (r + 1) f (m + 1) - fwdDiff (r + 1) f m =
              fwdDiff r g (m + 1) - fwdDiff r g m
            rw [ih (m + 1), ih m]
      have hg : ∀ n, n + D + 1 < k - 1 → fwdDiff (D + 1) g n = 0 := by
        intro n hn
        rw [← hshift (D + 1) n]
        exact hf n (by omega)
      obtain ⟨Q, hQdeg, hQeval⟩ := exists_poly_of_fwdDiff_zero D (k - 1) g hg
      obtain ⟨R, hRdeg, hReq⟩ := exists_poly_antidiff_aux D Q hQdeg
      let P : Polynomial ℚ := R + Polynomial.C (f 0 - R.eval 0)
      refine ⟨P, ?_, ?_⟩
      · exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hRdeg (by simp))
      · intro i hi
        induction i with
        | zero =>
            simp [P]
        | succ i ih =>
            have hprev := ih (by omega)
            have hdiff : P.eval ((i + 1 : ℕ) : ℚ) - P.eval (i : ℚ) = Q.eval (i : ℚ) := by
              have h1 : P.eval ((i + 1 : ℕ) : ℚ) - P.eval (i : ℚ) =
                  (R.comp (Polynomial.X + 1) - R).eval (i : ℚ) := by
                simp [P, Polynomial.eval_comp, Nat.cast_add, Nat.cast_one]
              rw [h1, hReq]
            have hgi : Q.eval (i : ℚ) = f (i + 1) - f i := hQeval i (by omega)
            linarith

private lemma sum_sq_poly_natDegree_eq_zero {d : ℕ} (c : ℚ) (P : Fin d → Polynomial ℚ)
    (hQ : (Polynomial.C c + ∑ j : Fin d, (P j) ^ 2).natDegree = 0) :
    ∀ j : Fin d, (P j).natDegree = 0 := by
  by_contra hne
  push Not at hne
  rcases hne with ⟨j₀, hj₀⟩
  let M : ℕ := Finset.univ.sup (fun j : Fin d => (P j).natDegree)
  have hM_pos : 1 ≤ M := by
    have hle : (P j₀).natDegree ≤ M :=
      Finset.le_sup (f := fun j : Fin d => (P j).natDegree) (Finset.mem_univ j₀)
    omega
  obtain ⟨jstar, _, hjstar⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j₀, Finset.mem_univ j₀⟩
    (fun j : Fin d => (P j).natDegree)
  have hPjstar_ne : P jstar ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hjstar
    omega
  have hcoeff_zero : (Polynomial.C c + ∑ j : Fin d, (P j) ^ 2).coeff (2 * M) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    omega
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add,
    Polynomial.finsetSum_coeff] at hcoeff_zero
  have hterm_nn : ∀ j : Fin d, 0 ≤ ((P j) ^ 2).coeff (2 * M) := by
    intro j
    have hj_le : (P j).natDegree ≤ M :=
      Finset.le_sup (f := fun i : Fin d => (P i).natDegree) (Finset.mem_univ j)
    by_cases hlt : (P j).natDegree < M
    · have hsq_lt : ((P j) ^ 2).natDegree < 2 * M := by
        have hle := Polynomial.natDegree_pow_le (p := P j) (n := 2)
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hsq_lt]
    · have heq : (P j).natDegree = M := by omega
      have hdeg_sq : ((P j) ^ 2).natDegree = 2 * M := by
        rw [Polynomial.natDegree_pow, heq]
      rw [← hdeg_sq, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_pow]
      exact sq_nonneg _
  have hjstar_pos : 0 < ((P jstar) ^ 2).coeff (2 * M) := by
    have heq : (P jstar).natDegree = M := hjstar.symm
    have hdeg_sq : ((P jstar) ^ 2).natDegree = 2 * M := by
      rw [Polynomial.natDegree_pow, heq]
    rw [← hdeg_sq, ← Polynomial.leadingCoeff, Polynomial.leadingCoeff_pow]
    exact sq_pos_of_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hPjstar_ne)
  have hsum_pos : 0 < ∑ j : Fin d, ((P j) ^ 2).coeff (2 * M) :=
    Finset.sum_pos' (fun j _ => hterm_nn j) ⟨jstar, Finset.mem_univ jstar, hjstar_pos⟩
  linarith

private lemma sum_choose_even_odd_le (D : ℕ) :
    (∑ j ∈ (Finset.range (D + 2)).filter (fun j => Even (D + 1 - j)), Nat.choose (D + 1) j) ≤ 2 ^ D ∧
    (∑ j ∈ (Finset.range (D + 2)).filter (fun j => ¬ Even (D + 1 - j)), Nat.choose (D + 1) j) ≤ 2 ^ D := by
  let E := ∑ j ∈ (Finset.range (D + 2)).filter (fun j => Even (D + 1 - j)), Nat.choose (D + 1) j
  let O := ∑ j ∈ (Finset.range (D + 2)).filter (fun j => ¬ Even (D + 1 - j)), Nat.choose (D + 1) j
  have hsum : E + O = 2 ^ (D + 1) := by
    rw [Finset.sum_filter_add_sum_filter_not]
    exact Nat.sum_range_choose (D + 1)
  have hdiff : (E : ℤ) - (O : ℤ) = 0 := by
    have halt : ∑ j ∈ Finset.range (D + 2), (-1 : ℤ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℤ) = 0 := by
      have h := add_pow (1 : ℤ) (-1 : ℤ) (D + 1)
      have h0 : (1 + (-1 : ℤ)) ^ (D + 1) = 0 := by simp
      rw [h0] at h
      symm
      convert h using 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp
    have hsplit :
        (∑ j ∈ Finset.range (D + 2), (-1 : ℤ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℤ)) =
          (E : ℤ) - (O : ℤ) := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (D + 2)) (p := fun j => Even (D + 1 - j))]
      have hE : (∑ j ∈ (Finset.range (D + 2)).filter (fun j => Even (D + 1 - j)),
          (-1 : ℤ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℤ)) = (E : ℤ) := by
        dsimp [E]; push_cast
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [(Finset.mem_filter.mp hj).2.neg_one_pow, one_mul]
      have hO : (∑ j ∈ (Finset.range (D + 2)).filter (fun j => ¬ Even (D + 1 - j)),
          (-1 : ℤ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℤ)) = -(O : ℤ) := by
        dsimp [O]; push_cast; rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hodd : Odd (D + 1 - j) := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hj).2
        rw [hodd.neg_one_pow]; ring
      rw [hE, hO]; ring
    linarith
  have h2pow : 2 ^ (D + 1) = 2 * 2 ^ D := by ring
  omega

/-- Single Rankin (1961) sphere-lifting step: lifts a `PolyAPFree (2 * D) k` set in `[0, T]`
to a `PolyAPFree D k` set in `[0, N - 1]` using shift averaging in `ℕ`. -/
private lemma rankin_step {D k d m N : ℕ} (hD : 1 ≤ D) (hDk : 2 * D < k)
    (_hd : 1 ≤ d) (hm : 2 ≤ m) (hN : (2 ^ D * m) ^ d ≤ N)
    {A : Finset ℕ} (hA_sub : A ⊆ Finset.range (d * (m - 1) ^ 2 + 1))
    (hA_free : PolyAPFree (2 * D) k A) :
    ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ PolyAPFree D k B ∧
      m ^ d * A.card ≤ (2 * (d * (m - 1) ^ 2) + 1) * B.card := by
  classical
  let T : ℕ := d * (m - 1) ^ 2
  let Bgrid : Finset (Fin d → ℕ) := Fintype.piFinset (fun _ : Fin d => Finset.range m)
  have hBgrid_card : Bgrid.card = m ^ d := by simp [Bgrid]
  let sqNorm : (Fin d → ℕ) → ℕ := fun x => ∑ j : Fin d, (x j) ^ 2
  have hsq_le : ∀ x ∈ Bgrid, sqNorm x ≤ T := by
    intro x hx
    have hle : sqNorm x ≤ ∑ _j : Fin d, (m - 1) ^ 2 := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hxj : x j < m := Finset.mem_range.mp ((Fintype.mem_piFinset.mp hx) j)
      exact Nat.pow_le_pow_left (by omega) 2
    simpa [T] using hle
  let A' : Finset ℕ := A.image (· + T)
  have hA'_free : PolyAPFree (2 * D) k A' := polyAPFree_image_add hA_free
  -- Shift-averaging identity: ∑_{s < 2T+1} |{x ∈ Bgrid : sqNorm x + s ∈ A'}| = m^d * A.card
  have hfiber : ∀ x ∈ Bgrid,
      ((Finset.range (2 * T + 1)).filter (fun s => sqNorm x + s ∈ A')).card = A.card := by
    intro x hx
    have hxr : sqNorm x ≤ T := hsq_le x hx
    symm
    refine Finset.card_bij (fun a _ => a + T - sqNorm x) ?_ ?_ ?_
    · intro a ha
      have haT : a ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hA_sub ha))
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [Finset.mem_image]
      exact ⟨a, ha, by omega⟩
    · intro a₁ _ a₂ _ heq
      omega
    · intro s hs
      rw [Finset.mem_filter] at hs
      rcases Finset.mem_image.mp hs.2 with ⟨a, ha, ha_eq⟩
      exact ⟨a, ha, by omega⟩
  have hdouble :
      ∑ s ∈ Finset.range (2 * T + 1), (Bgrid.filter (fun x => sqNorm x + s ∈ A')).card =
        m ^ d * A.card := by
    have h1 : ∀ s, (Bgrid.filter (fun x => sqNorm x + s ∈ A')).card =
        ∑ x ∈ Bgrid, if sqNorm x + s ∈ A' then 1 else 0 := by
      intro s; rw [Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ x ∈ Bgrid,
        (∑ s ∈ Finset.range (2 * T + 1), if sqNorm x + s ∈ A' then 1 else 0) = A.card := by
      intro x hx
      rw [← Finset.card_filter]
      exact hfiber x hx
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, hBgrid_card]
  have hpig : ∃ s ∈ Finset.range (2 * T + 1),
      m ^ d * A.card ≤ (2 * T + 1) * (Bgrid.filter (fun x => sqNorm x + s ∈ A')).card := by
    by_contra hall
    push Not at hall
    have hlt :
        ∑ s ∈ Finset.range (2 * T + 1), (2 * T + 1) * (Bgrid.filter (fun x => sqNorm x + s ∈ A')).card <
          ∑ _s ∈ Finset.range (2 * T + 1), (m ^ d * A.card) := by
      refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr (by omega)⟩ ?_
      intro s hs; exact hall s hs
    rw [← Finset.mul_sum, hdouble, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt
    omega
  rcases hpig with ⟨s, _, hs⟩
  let S : Finset (Fin d → ℕ) := Bgrid.filter (fun x => sqNorm x + s ∈ A')
  let b : ℕ := 2 ^ D * m
  have h2D_ge : 2 ≤ 2 ^ D := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by omega) hD
  have hb : 2 ≤ b := by dsimp [b]; nlinarith
  let enc : (Fin d → ℕ) → ℕ := fun x => ∑ j : Fin d, x j * b ^ (j : ℕ)
  have henc_inj : Set.InjOn enc S := by
    intro x hx y hy hxy
    have hxB : ∀ j, x j < b := fun j => by
      have := Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) j)
      dsimp [b]; nlinarith
    have hyB : ∀ j, y j < b := fun j => by
      have := Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hy).1) j)
      dsimp [b]; nlinarith
    exact base_repr_eq hb d x y hxB hyB hxy
  let B : Finset ℕ := S.image enc
  refine ⟨B, ?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxB : ∀ j, x j < b := fun j => by
      have := Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) j)
      dsimp [b]; nlinarith
    rw [Finset.mem_range]
    exact lt_of_lt_of_le (base_repr_lt_pow hb x hxB) hN
  · -- Prove PolyAPFree D k B
    intro P hPdeg hPval
    -- Choose witnesses x i ∈ S with enc (x i) = P.eval i for i < k
    have hex : ∀ i : ℕ, ∃ v : Fin d → ℕ, i < k → v ∈ S ∧ (enc v : ℚ) = P.eval (i : ℚ) := by
      intro i
      by_cases hi : i < k
      · rcases hPval i hi with ⟨n, hn, hneq⟩
        rcases Finset.mem_image.mp hn with ⟨v, hv, rfl⟩
        exact ⟨v, fun _ => ⟨hv, hneq⟩⟩
      · exact ⟨fun _ => 0, fun h => absurd h hi⟩
    choose x hx using hex
    -- Step 1: By zero (D+1)-th forward difference & base-b no-carry, each coordinate has zero (D+1)-th difference
    have hcoord_diff : ∀ (t : Fin d) (n : ℕ), n + D + 1 < k →
        fwdDiff (D + 1) (fun i => (x i t : ℚ)) n = 0 := by
      intro t n hn
      have hPzero := fwdDiff_poly_zero D P hPdeg n
      rw [fwdDiff_eq_sum] at hPzero
      have hrepl :
          (∑ j ∈ Finset.range (D + 2), (-1 : ℚ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℚ) * (enc (x (n + j)) : ℚ)) = 0 := by
        rw [← hPzero]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hlt : n + j < k := by have := Finset.mem_range.mp hj; omega
        rw [(hx (n + j) hlt).2]
      -- Separate into Even and Odd parts of (D + 1 - j)
      let Ev := (Finset.range (D + 2)).filter (fun j => Even (D + 1 - j))
      let Od := (Finset.range (D + 2)).filter (fun j => ¬ Even (D + 1 - j))
      have heq_nat :
          (∑ j ∈ Ev, Nat.choose (D + 1) j * enc (x (n + j))) =
          (∑ j ∈ Od, Nat.choose (D + 1) j * enc (x (n + j))) := by
        have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range (D + 2))
          (p := fun j => Even (D + 1 - j))
          (f := fun j => (-1 : ℚ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℚ) * (enc (x (n + j)) : ℚ))
        rw [hrepl] at hsplit
        have hE : (∑ j ∈ Ev, (-1 : ℚ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℚ) * (enc (x (n + j)) : ℚ)) =
            ((∑ j ∈ Ev, Nat.choose (D + 1) j * enc (x (n + j)) : ℕ) : ℚ) := by
          push_cast
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [(Finset.mem_filter.mp hj).2.neg_one_pow, one_mul]
        have hO : (∑ j ∈ Od, (-1 : ℚ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℚ) * (enc (x (n + j)) : ℚ)) =
            -((∑ j ∈ Od, Nat.choose (D + 1) j * enc (x (n + j)) : ℕ) : ℚ) := by
          push_cast; rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hodd : Odd (D + 1 - j) := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hj).2
          rw [hodd.neg_one_pow]; ring
        have hq : ((∑ j ∈ Ev, Nat.choose (D + 1) j * enc (x (n + j)) : ℕ) : ℚ) =
            ((∑ j ∈ Od, Nat.choose (D + 1) j * enc (x (n + j)) : ℕ) : ℚ) := by
          dsimp [Ev, Od] at hE hO ⊢
          linarith
        exact_mod_cast hq
      -- Rewrite both sides as base-b sums over Fin d
      have hswap : ∀ F : Finset ℕ,
          (∑ j ∈ F, Nat.choose (D + 1) j * enc (x (n + j))) =
            ∑ r : Fin d, (∑ j ∈ F, Nat.choose (D + 1) j * x (n + j) r) * b ^ (r : ℕ) := by
        intro F
        simp only [enc, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
      rw [hswap Ev, hswap Od] at heq_nat
      have hEO := sum_choose_even_odd_le D
      have hlt_b : ∀ (F : Finset ℕ), F ⊆ Finset.range (D + 2) →
          (∑ j ∈ F, Nat.choose (D + 1) j) ≤ 2 ^ D →
          ∀ r : Fin d, (∑ j ∈ F, Nat.choose (D + 1) j * x (n + j) r) < b := by
        intro F hFsub hFsum r
        have hle : ∑ j ∈ F, Nat.choose (D + 1) j * x (n + j) r ≤
            ∑ j ∈ F, Nat.choose (D + 1) j * (m - 1) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hlt : n + j < k := by have := Finset.mem_range.mp (hFsub hj); omega
          have hxm : x (n + j) r < m :=
            Finset.mem_range.mp ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp (hx (n + j) hlt).1).1) r)
          exact Nat.mul_le_mul_left _ (by omega)
        rw [← Finset.sum_mul] at hle
        have hle2 : (∑ j ∈ F, Nat.choose (D + 1) j) * (m - 1) ≤ 2 ^ D * (m - 1) :=
          Nat.mul_le_mul_right _ hFsum
        have hlt3 : 2 ^ D * (m - 1) < 2 ^ D * m := Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)
        exact lt_of_le_of_lt (le_trans hle hle2) hlt3
      have hcoord_eq := congrFun (base_repr_eq hb d _ _
        (hlt_b Ev (Finset.filter_subset _ _) hEO.1)
        (hlt_b Od (Finset.filter_subset _ _) hEO.2) heq_nat) t
      -- Convert back to fwdDiff = 0
      rw [fwdDiff_eq_sum]
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (D + 2)) (p := fun j => Even (D + 1 - j))]
      have hE' : (∑ j ∈ Ev, (-1 : ℚ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℚ) * (x (n + j) t : ℚ)) =
          ((∑ j ∈ Ev, Nat.choose (D + 1) j * x (n + j) t : ℕ) : ℚ) := by
        push_cast
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [(Finset.mem_filter.mp hj).2.neg_one_pow, one_mul]
      have hO' : (∑ j ∈ Od, (-1 : ℚ) ^ (D + 1 - j) * (Nat.choose (D + 1) j : ℚ) * (x (n + j) t : ℚ)) =
          -((∑ j ∈ Od, Nat.choose (D + 1) j * x (n + j) t : ℕ) : ℚ) := by
        push_cast; rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hodd : Odd (D + 1 - j) := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hj).2
        rw [hodd.neg_one_pow]; ring
      dsimp [Ev, Od] at hE' hO' hcoord_eq ⊢
      rw [hE', hO', hcoord_eq, add_neg_cancel]
    -- Step 2: Interpolate each coordinate by a degree ≤ D polynomial P_t
    have hexP : ∀ t : Fin d, ∃ Pt : Polynomial ℚ, Pt.natDegree ≤ D ∧ ∀ i < k, Pt.eval (i : ℚ) = (x i t : ℚ) :=
      fun t => exists_poly_of_fwdDiff_zero D k (fun i => (x i t : ℚ)) (hcoord_diff t)
    choose Pc hPc_deg hPc_eval using hexP
    -- Step 3: Form Q = C s + ∑ (Pc t)^2 of degree ≤ 2 * D taking values in A'
    let Q : Polynomial ℚ := Polynomial.C (s : ℚ) + ∑ t : Fin d, (Pc t) ^ 2
    have hQdeg : Q.natDegree ≤ 2 * D := by
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) ?_)
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      change Finset.univ.sup (fun t : Fin d => ((Pc t) ^ 2).natDegree) ≤ 2 * D
      rw [Finset.sup_le_iff]
      intro t _
      exact le_trans Polynomial.natDegree_pow_le (by have := hPc_deg t; omega)
    have hQval : ∀ i < k, ∃ n ∈ A', (n : ℚ) = Q.eval (i : ℚ) := by
      intro i hi
      refine ⟨sqNorm (x i) + s, (Finset.mem_filter.mp (hx i hi).1).2, ?_⟩
      simp only [Q, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum,
        Polynomial.eval_pow, sqNorm]
      push_cast
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hPc_eval t i hi]
    have hQ0 : Q.natDegree = 0 := hA'_free Q hQdeg hQval
    -- Step 4: Every Pc t is constant, so P agrees with P.eval 0 at k > D points, hence P is constant
    have hPc0 : ∀ t : Fin d, (Pc t).natDegree = 0 := sum_sq_poly_natDegree_eq_zero (s : ℚ) Pc hQ0
    have hPconst : ∀ i < k, P.eval (i : ℚ) = P.eval 0 := by
      intro i hi
      have h0 := (hx 0 (by omega)).2
      norm_num at h0
      rw [← (hx i hi).2, ← h0]
      congr 1; congr 1
      funext t
      have hqt : (x i t : ℚ) = (x 0 t : ℚ) := by
        rw [← hPc_eval t i hi, ← hPc_eval t 0 (by omega)]
        rw [Polynomial.eq_C_of_natDegree_eq_zero (hPc0 t)]
        simp
      exact_mod_cast hqt
    let R : Polynomial ℚ := P - Polynomial.C (P.eval 0)
    have hR0 : R = 0 := by
      by_contra hRne
      have hroots : ∀ i ∈ Finset.range k, (i : ℚ) ∈ R.roots := by
        intro i hi
        rw [Polynomial.mem_roots hRne, Polynomial.IsRoot.def]
        simp [R, hPconst i (Finset.mem_range.mp hi)]
      let U : Finset ℚ := (Finset.range k).image (fun i : ℕ => (i : ℚ))
      have hU_card : U.card = k := by
        rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      have hU_sub : U.val ⊆ R.roots := by
        intro q hq
        rcases Finset.mem_image.mp (Finset.mem_val.mp hq) with ⟨i, hi, rfl⟩
        exact hroots i hi
      have hcard_le : k ≤ R.roots.card := by
        rw [← hU_card]
        exact Multiset.card_le_card ((Multiset.le_iff_subset U.nodup).mpr hU_sub)
      have hRdeg : R.natDegree = P.natDegree := by
        dsimp [R]; rw [sub_eq_add_neg, ← map_neg]; exact Polynomial.natDegree_add_C
      have hrl := Polynomial.card_roots' R
      omega
    have hPeq : P = Polynomial.C (P.eval 0) := sub_eq_zero.mp hR0
    rw [hPeq]; simp
  · rw [Finset.card_image_of_injOn henc_inj]
    exact hs

/-- Inductive Rankin (1961) lower bound for all levels `ℓ ≥ 0` and degree bounds `D ≥ 1` with `2^ℓ * D < k`. -/
private lemma rankin_inductive :
    ∀ (ℓ D k : ℕ), 1 ≤ D → 2 ^ ℓ * D < k →
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ A : Finset ℕ, A ⊆ Finset.range N ∧ PolyAPFree D k A ∧
          (N : ℝ) * Real.exp (-C * (Real.log (N : ℝ)) ^ ((1 : ℝ) / ((ℓ + 1 : ℕ) : ℝ))) ≤ (A.card : ℝ)
  | 0, D, k, _, hDk => by
      refine ⟨1, by norm_num, 2, fun N hN => ?_⟩
      refine ⟨{0}, ?_, polyAPFree_singleton (by simpa using hDk), ?_⟩
      · intro x hx
        rw [Finset.mem_singleton.mp hx, Finset.mem_range]
        omega
      · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        simp only [Finset.card_singleton, Nat.cast_one, zero_add, div_one, Real.rpow_one,
          neg_mul, one_mul, Real.exp_neg, Real.exp_log hNpos]
        rw [mul_inv_cancel₀ (ne_of_gt hNpos)]
  | ℓ + 1, D, k, hD, hDk => by
      have hDk' : 2 ^ ℓ * (2 * D) < k := by
        have : 2 ^ (ℓ + 1) * D = 2 ^ ℓ * (2 * D) := by ring
        omega
      obtain ⟨C₁, hC₁_pos, N₁, hIH⟩ := rankin_inductive ℓ (2 * D) k (by omega) hDk'
      let α : ℝ := 1 / ((ℓ + 1 : ℕ) : ℝ)
      let β : ℝ := 1 / ((ℓ + 2 : ℕ) : ℝ)
      have hα_pos : 0 < α := by positivity
      have hβ_pos : 0 < β := by positivity
      have hβ_le_half : β ≤ 1 / 2 := by
        dsimp [β]
        have : (2 : ℝ) ≤ ((ℓ + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ ℓ + 2)
        exact one_div_le_one_div_of_le (by norm_num) this
      have hα_le_one : α ≤ 1 := by
        dsimp [α]
        have : (1 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ + 1)
        exact div_le_one_of_le₀ this (by positivity)
      have h1mβ_α : (1 - β) * α = β := by
        dsimp [α, β]
        have h1 : ((ℓ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have h2 : ((ℓ + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        have h3 : ((ℓ + 2 : ℕ) : ℝ) = ((ℓ + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
        field_simp [h1, h2]
        linarith
      let C_new : ℝ := 1 + (D : ℝ) * Real.log 2 + C₁ * (6 : ℝ) ^ α
      have hC_new_pos : 0 < C_new := by
        have : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      -- Threshold L₀ so that L^β ≥ 4 and R₀ ≥ max (2^(D+2) * d) (2^(D+1) * (N₁ + 4))
      let K_thresh : ℝ := max 100 (27 * ((2 : ℝ) ^ (D + 2) + (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4)))
      let L₀ : ℝ := max (4 ^ (ℓ + 2)) K_thresh
      let N₀ : ℕ := Nat.ceil (Real.exp L₀) + 10
      refine ⟨C_new, hC_new_pos, N₀, fun N hN => ?_⟩
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hN_ge_exp : Real.exp L₀ ≤ (N : ℝ) := by
        have h1 : Real.exp L₀ ≤ (Nat.ceil (Real.exp L₀) : ℝ) := Nat.le_ceil _
        have h2 : (Nat.ceil (Real.exp L₀) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast (by omega : Nat.ceil (Real.exp L₀) ≤ N)
        linarith
      set L : ℝ := Real.log (N : ℝ)
      have hL_ge : L₀ ≤ L := by
        have := Real.log_le_log (Real.exp_pos L₀) hN_ge_exp
        rwa [Real.log_exp] at this
      have hL_ge100 : 100 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL_ge
      have hL_pos : 0 < L := by linarith
      have hLβ_ge4 : 4 ≤ L ^ β := by
        have h1 : (4 : ℝ) ^ (ℓ + 2) ≤ L := le_trans (le_max_left _ _) hL_ge
        have h2 : ((4 : ℝ) ^ (ℓ + 2)) ^ β ≤ L ^ β :=
          Real.rpow_le_rpow (by positivity) h1 (le_of_lt hβ_pos)
        have h3 : ((4 : ℝ) ^ (ℓ + 2)) ^ β = 4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          have : ((ℓ + 2 : ℕ) : ℝ) * β = 1 := by
            dsimp [β]; exact mul_one_div_cancel (by positivity)
          rw [this, Real.rpow_one]
        linarith
      let d : ℕ := Nat.floor (L ^ β)
      have hd_le : (d : ℝ) ≤ L ^ β := Nat.floor_le (by positivity)
      have hd_gt : L ^ β - 1 < (d : ℝ) := Nat.sub_one_lt_floor (L ^ β)
      have hd_ge_half : L ^ β / 2 ≤ (d : ℝ) := by linarith
      have hd_ge4 : 4 ≤ d := Nat.le_floor hLβ_ge4
      have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      set R₀ : ℝ := (N : ℝ) ^ ((1 : ℝ) / (d : ℝ))
      have hR₀_eq : R₀ = Real.exp (L / (d : ℝ)) := by
        dsimp only [R₀, L]
        rw [Real.rpow_def_of_pos hN_pos]; congr 1; ring
      have hR₀_pos : 0 < R₀ := by rw [hR₀_eq]; exact Real.exp_pos _
      -- Lower bound L / d ≥ L^(1 - β) ≥ L^(1/2)
      have hLd_ge_sqrt : Real.sqrt L ≤ L / (d : ℝ) := by
        have h1 : L / L ^ β ≤ L / (d : ℝ) :=
          div_le_div_of_nonneg_left (le_of_lt hL_pos) hd_pos hd_le
        have h2 : L ^ β ≤ Real.sqrt L := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) hβ_le_half
        have h3 : Real.sqrt L ≤ L / L ^ β := by
          rw [le_div_iff₀ (by positivity)]
          calc
            Real.sqrt L * L ^ β ≤ Real.sqrt L * Real.sqrt L :=
              mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
            _ = L := Real.mul_self_sqrt (le_of_lt hL_pos)
        linarith
      have hR₀_ge_big : ((2 : ℝ) ^ (D + 2) + (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4)) * (d : ℝ) ≤ R₀ := by
        have hcube := exp_ge_cube_div_27 (show 0 ≤ L / (d : ℝ) by positivity)
        rw [← hR₀_eq] at hcube
        have h1 : (Real.sqrt L) ^ 3 ≤ (L / (d : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hLd_ge_sqrt 3
        have h2 : (Real.sqrt L) ^ 3 = L * Real.sqrt L := by
          rw [pow_succ, sq, Real.mul_self_sqrt (le_of_lt hL_pos)]
        have hd_le_sqrt : (d : ℝ) ≤ Real.sqrt L := by
          have : L ^ β ≤ Real.sqrt L := by
            rw [Real.sqrt_eq_rpow]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith) hβ_le_half
          linarith
        have hK_le : 27 * ((2 : ℝ) ^ (D + 2) + (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4)) ≤ L :=
          le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL_ge
        have h3 : 27 * ((2 : ℝ) ^ (D + 2) + (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4)) * (d : ℝ) ≤
            L * Real.sqrt L := by
          have hnn : 0 ≤ 27 * ((2 : ℝ) ^ (D + 2) + (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4)) := by positivity
          exact mul_le_mul hK_le hd_le_sqrt (Nat.cast_nonneg d) (le_of_lt hL_pos)
        linarith
      let m : ℕ := Nat.floor (R₀ / ((2 ^ D : ℕ) : ℝ))
      have h2D_pos : (0 : ℝ) < ((2 ^ D : ℕ) : ℝ) := by positivity
      have hm_le : (m : ℝ) ≤ R₀ / ((2 ^ D : ℕ) : ℝ) := Nat.floor_le (by positivity)
      have hm_gt : R₀ / ((2 ^ D : ℕ) : ℝ) - 1 < (m : ℝ) := Nat.sub_one_lt_floor _
      have hR₀_ge_2D2d : (2 : ℝ) ^ (D + 2) * (d : ℝ) ≤ R₀ := by
        have : 0 ≤ (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4) * (d : ℝ) := by positivity
        linarith
      have hR₀_ge_N1 : (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4) ≤ R₀ := by
        have h1 : (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4) ≤
            ((2 : ℝ) ^ (D + 2) + (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4)) * (d : ℝ) := by
          have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
          have ha : (0 : ℝ) ≤ (2 : ℝ) ^ (D + 2) := by positivity
          have hb : (0 : ℝ) ≤ (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4) := by positivity
          nlinarith only [hd1, ha, hb]
        linarith
      have hm_ge_N1 : N₁ + 2 ≤ m := by
        have h1 : (2 : ℝ) * ((N₁ : ℝ) + 4) ≤ R₀ / ((2 ^ D : ℕ) : ℝ) := by
          rw [le_div_iff₀ h2D_pos]
          have : (2 : ℝ) * ((N₁ : ℝ) + 4) * ((2 ^ D : ℕ) : ℝ) = (2 : ℝ) ^ (D + 1) * ((N₁ : ℝ) + 4) := by
            push_cast; ring
          linarith
        have h2 : ((N₁ + 2 : ℕ) : ℝ) ≤ (m : ℝ) := by push_cast; linarith
        exact_mod_cast h2
      have hm_ge2 : 2 ≤ m := by omega
      have hpow_le_N : (2 ^ D * m) ^ d ≤ N := by
        have h1 : ((2 ^ D * m : ℕ) : ℝ) ≤ R₀ := by
          rw [Nat.cast_mul]
          exact (le_div_iff₀' h2D_pos).mp hm_le
        have h2 : (((2 ^ D * m) ^ d : ℕ) : ℝ) ≤ R₀ ^ d := by
          rw [Nat.cast_pow]
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) h1 d
        have hR₀_d : R₀ ^ d = (N : ℝ) := by
          dsimp only [R₀]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN_pos),
            one_div_mul_cancel (ne_of_gt hd_pos), Real.rpow_one]
        rw [hR₀_d] at h2
        exact_mod_cast h2
      let T : ℕ := d * (m - 1) ^ 2
      have hT_ge : N₁ ≤ T + 1 := by
        have h1 : m - 1 ≤ (m - 1) ^ 2 := by nlinarith
        have h2 : (m - 1) ^ 2 ≤ d * (m - 1) ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
        dsimp only [T]; omega
      have h2Dk : 2 * D < k := by
        have h1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
        have h2 : 2 * D ≤ 2 ^ ℓ * (2 * D) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      obtain ⟨A, hA_sub, hA_free, hA_card⟩ := hIH (T + 1) hT_ge
      obtain ⟨B, hB_sub, hB_free, hB_card⟩ := rankin_step hD h2Dk (by omega) hm_ge2 hpow_le_N hA_sub hA_free
      refine ⟨B, hB_sub, hB_free, ?_⟩
      -- Bound log(T + 1) ≤ 3 * L / d
      have hT1_le_R3 : ((T + 1 : ℕ) : ℝ) ≤ R₀ ^ 3 := by
        have hT1_nat : T + 1 ≤ d * m ^ 2 := by
          have h1 : (m - 1) + 1 = m := by omega
          have h2 : (m - 1) ^ 2 + 1 ≤ m ^ 2 := by nlinarith only [h1, hm_ge2]
          dsimp only [T]
          nlinarith only [h2, hd_ge4]
        have h1 : ((T + 1 : ℕ) : ℝ) ≤ (d : ℝ) * (m : ℝ) ^ 2 := by exact_mod_cast hT1_nat
        have hm_le_R : (m : ℝ) ≤ R₀ := by
          have h2D1 : (1 : ℝ) ≤ ((2 ^ D : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
          calc (m : ℝ) ≤ R₀ / ((2 ^ D : ℕ) : ℝ) := hm_le
            _ ≤ R₀ / 1 := div_le_div_of_nonneg_left (le_of_lt hR₀_pos) (by norm_num) h2D1
            _ = R₀ := div_one _
        have hd_le_R : (d : ℝ) ≤ R₀ := by
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (D + 2) := by exact_mod_cast Nat.one_le_two_pow
          have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          nlinarith only [h2, hdnn, hR₀_ge_2D2d]
        have hm2_le : (m : ℝ) ^ 2 ≤ R₀ ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hm_le_R 2
        calc
          ((T + 1 : ℕ) : ℝ) ≤ (d : ℝ) * (m : ℝ) ^ 2 := h1
          _ ≤ R₀ * R₀ ^ 2 := mul_le_mul hd_le_R hm2_le (sq_nonneg _) (le_of_lt hR₀_pos)
          _ = R₀ ^ 3 := by ring
      have hlogT_le : Real.log ((T + 1 : ℕ) : ℝ) ≤ 3 * L / (d : ℝ) := by
        have hT1_pos : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
        have h1 := Real.log_le_log hT1_pos hT1_le_R3
        rw [Real.log_pow, hR₀_eq, Real.log_exp] at h1
        have h3eq : ((3 : ℕ) : ℝ) * (L / (d : ℝ)) = 3 * L / (d : ℝ) := by push_cast; ring
        linarith only [h1, h3eq]
      -- Lower bound m^d via Bernoulli
      have hm_pow_ge : (1 / 2 : ℝ) * (N : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2) ≤ (m : ℝ) ^ d := by
        have hm_fac : (R₀ / ((2 ^ D : ℕ) : ℝ)) * (1 - ((2 ^ D : ℕ) : ℝ) / R₀) ≤ (m : ℝ) := by
          have : (R₀ / ((2 ^ D : ℕ) : ℝ)) * (1 - ((2 ^ D : ℕ) : ℝ) / R₀) =
              R₀ / ((2 ^ D : ℕ) : ℝ) - 1 := by
            field_simp [ne_of_gt h2D_pos, ne_of_gt hR₀_pos]
          linarith only [this, hm_gt]
        have hbern : (1 / 2 : ℝ) ≤ (1 - ((2 ^ D : ℕ) : ℝ) / R₀) ^ d := by
          have hu0 : 0 ≤ ((2 ^ D : ℕ) : ℝ) / R₀ := by positivity
          have hu1 : ((2 ^ D : ℕ) : ℝ) / R₀ ≤ 1 := by
            rw [div_le_one hR₀_pos]
            have h2d : ((2 ^ D : ℕ) : ℝ) ≤ (2 : ℝ) ^ (D + 2) * (d : ℝ) := by
              rw [Nat.cast_pow, Nat.cast_ofNat]
              have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
              have h4 : (2 : ℝ) ^ D ≤ (2 : ℝ) ^ (D + 2) := by
                have h2d_nn : (0 : ℝ) ≤ (2 : ℝ) ^ D := by positivity
                rw [pow_add]
                have h22 : (2 : ℝ) ^ 2 = 4 := by norm_num
                linarith only [h2d_nn, h22]
              have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (D + 2) := by positivity
              nlinarith only [hd1, h4, hnn]
            linarith only [h2d, hR₀_ge_2D2d]
          have hb := one_sub_pow_ge_bernoulli hu0 hu1 d
          have hle : (d : ℝ) * (((2 ^ D : ℕ) : ℝ) / R₀) ≤ 1 / 2 := by
            rw [← mul_div_assoc, div_le_iff₀ hR₀_pos]
            have h4eq : (d : ℝ) * ((2 ^ D : ℕ) : ℝ) * 4 = (2 : ℝ) ^ (D + 2) * (d : ℝ) := by
              push_cast; ring
            linarith only [h4eq, hR₀_ge_2D2d, hR₀_pos]
          linarith only [hb, hle]
        have hfac_nn : 0 ≤ (R₀ / ((2 ^ D : ℕ) : ℝ)) * (1 - ((2 ^ D : ℕ) : ℝ) / R₀) := by
          have : (R₀ / ((2 ^ D : ℕ) : ℝ)) * (1 - ((2 ^ D : ℕ) : ℝ) / R₀) =
              R₀ / ((2 ^ D : ℕ) : ℝ) - 1 := by
            field_simp [ne_of_gt h2D_pos, ne_of_gt hR₀_pos]
          have hm2r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge2
          linarith only [this, hm_le, hm2r]
        have hpow1 := pow_le_pow_left₀ hfac_nn hm_fac d
        rw [mul_pow] at hpow1
        have hpow2 : (1 / 2 : ℝ) * (R₀ / ((2 ^ D : ℕ) : ℝ)) ^ d ≤ (m : ℝ) ^ d := by
          have hnn := pow_nonneg (show 0 ≤ R₀ / ((2 ^ D : ℕ) : ℝ) by positivity) d
          have hmul : (R₀ / ((2 ^ D : ℕ) : ℝ)) ^ d * (1 / 2 : ℝ) ≤
              (R₀ / ((2 ^ D : ℕ) : ℝ)) ^ d * (1 - ((2 ^ D : ℕ) : ℝ) / R₀) ^ d :=
            mul_le_mul_of_nonneg_left hbern hnn
          linarith only [hmul, hpow1]
        have hEq : (R₀ / ((2 ^ D : ℕ) : ℝ)) ^ d = (N : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2) := by
          rw [div_pow]
          have hR₀_d : R₀ ^ d = (N : ℝ) := by
            dsimp only [R₀]
            rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN_pos),
              one_div_mul_cancel (ne_of_gt hd_pos), Real.rpow_one]
          have h2Dd : (((2 ^ D : ℕ) : ℝ)) ^ d = Real.exp ((d : ℝ) * (D : ℝ) * Real.log 2) := by
            rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_assoc,
              Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num), ← pow_mul, mul_comm D d]
          rw [hR₀_d, h2Dd, div_eq_mul_inv, ← Real.exp_neg]
          congr 2; ring
        rw [hEq] at hpow2
        linarith only [hpow2]
      -- Combine everything to get B.card ≥ N * exp(-C_new * L^β)
      have hB_real : ((m : ℝ) ^ d) * (A.card : ℝ) ≤ ((2 * T + 1 : ℕ) : ℝ) * (B.card : ℝ) := by
        exact_mod_cast hB_card
      have h2T1_le : ((2 * T + 1 : ℕ) : ℝ) ≤ 2 * ((T + 1 : ℕ) : ℝ) := by
        have : 2 * T + 1 ≤ 2 * (T + 1) := by omega
        exact_mod_cast this
      have hT1_pos : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
      have hA_exp : Real.exp (-C₁ * (3 * L / (d : ℝ)) ^ α) ≤
          Real.exp (-C₁ * (Real.log ((T + 1 : ℕ) : ℝ)) ^ α) := by
        apply Real.exp_le_exp.mpr
        have hlogT_nn : 0 ≤ Real.log ((T + 1 : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T + 1))
        have hpow := Real.rpow_le_rpow hlogT_nn hlogT_le (le_of_lt hα_pos)
        nlinarith only [hpow, hC₁_pos]
      have hA_lb : ((T + 1 : ℕ) : ℝ) * Real.exp (-C₁ * (3 * L / (d : ℝ)) ^ α) ≤ (A.card : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_left hA_exp (le_of_lt hT1_pos)) hA_card
      have hprod_lb :
          ((1 / 2 : ℝ) * (N : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2)) *
            (((T + 1 : ℕ) : ℝ) * Real.exp (-C₁ * (3 * L / (d : ℝ)) ^ α)) ≤
            2 * ((T + 1 : ℕ) : ℝ) * (B.card : ℝ) := by
        have h1 : ((1 / 2 : ℝ) * (N : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2)) *
            (((T + 1 : ℕ) : ℝ) * Real.exp (-C₁ * (3 * L / (d : ℝ)) ^ α)) ≤
            (m : ℝ) ^ d * (A.card : ℝ) :=
          mul_le_mul hm_pow_ge hA_lb (by positivity) (by positivity)
        have h2 : ((2 * T + 1 : ℕ) : ℝ) * (B.card : ℝ) ≤ 2 * ((T + 1 : ℕ) : ℝ) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right h2T1_le (Nat.cast_nonneg _)
        linarith only [h1, hB_real, h2]
      have hB_lb : (1 / 4 : ℝ) * (N : ℝ) *
          Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2 - C₁ * (3 * L / (d : ℝ)) ^ α) ≤ (B.card : ℝ) := by
        have hrew : ((1 / 2 : ℝ) * (N : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2)) *
            (((T + 1 : ℕ) : ℝ) * Real.exp (-C₁ * (3 * L / (d : ℝ)) ^ α)) =
            (2 * ((T + 1 : ℕ) : ℝ)) * ((1 / 4 : ℝ) * (N : ℝ) *
              Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2 - C₁ * (3 * L / (d : ℝ)) ^ α)) := by
          rw [sub_eq_add_neg, Real.exp_add]; ring
        rw [hrew] at hprod_lb
        have h2Tpos : 0 < 2 * ((T + 1 : ℕ) : ℝ) := by positivity
        exact le_of_mul_le_mul_left hprod_lb h2Tpos
      -- Finally compare exponents
      have h3Ld_le : (3 * L / (d : ℝ)) ^ α ≤ (6 : ℝ) ^ α * L ^ β := by
        have hdiv : 3 * L / (d : ℝ) ≤ 6 * L ^ (1 - β) := by
          have h1 : 3 * L / (d : ℝ) ≤ 3 * L / (L ^ β / 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hd_ge_half
          have h2 : 3 * L / (L ^ β / 2) = 6 * L ^ (1 - β) := by
            rw [Real.rpow_sub hL_pos, Real.rpow_one]; ring
          linarith only [h1, h2]
        calc
          (3 * L / (d : ℝ)) ^ α ≤ (6 * L ^ (1 - β)) ^ α :=
            Real.rpow_le_rpow (by positivity) hdiv (le_of_lt hα_pos)
          _ = (6 : ℝ) ^ α * (L ^ (1 - β)) ^ α := Real.mul_rpow (by norm_num) (by positivity)
          _ = (6 : ℝ) ^ α * L ^ ((1 - β) * α) := by rw [← Real.rpow_mul (le_of_lt hL_pos)]
          _ = (6 : ℝ) ^ α * L ^ β := by rw [h1mβ_α]
      have hlog4_le : Real.log 4 ≤ L ^ β := by
        have hlog2_lt : Real.log 2 < 1 := by
          have : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
          calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) this
            _ = 1 := Real.log_exp 1
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
        linarith only [hlog2_lt, h4, hLβ_ge4]
      have hexp_cmp :
          Real.exp (-C_new * L ^ β) ≤
            (1 / 4 : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2 - C₁ * (3 * L / (d : ℝ)) ^ α) := by
        have hquarter : (1 / 4 : ℝ) = Real.exp (-Real.log 4) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
        rw [hquarter, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hterm1 : (d : ℝ) * (D : ℝ) * Real.log 2 ≤ (D : ℝ) * Real.log 2 * L ^ β := by
          have hnn : 0 ≤ (D : ℝ) * Real.log 2 := by
            have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
          have hmul := mul_le_mul_of_nonneg_right hd_le hnn
          linarith only [hmul]
        have hterm2 : C₁ * (3 * L / (d : ℝ)) ^ α ≤ C₁ * ((6 : ℝ) ^ α * L ^ β) :=
          mul_le_mul_of_nonneg_left h3Ld_le (le_of_lt hC₁_pos)
        dsimp only [C_new]
        linarith only [hterm1, hterm2, hlog4_le]
      have hfinal : (N : ℝ) * Real.exp (-C_new * L ^ β) ≤
          (1 / 4 : ℝ) * (N : ℝ) * Real.exp (-(d : ℝ) * (D : ℝ) * Real.log 2 - C₁ * (3 * L / (d : ℝ)) ^ α) := by
        have := mul_le_mul_of_nonneg_left hexp_cmp (le_of_lt hN_pos)
        linarith only [this]
      exact le_trans hfinal hB_lb

/-- **Rankin (1961) General-`k` Sphere-Packing Lower Bound (All `k ≥ 3`):**
For every integer `k ≥ 3`, there exist `C > 0` and `N₀ : ℕ` such that for all `N ≥ N₀`,
`r_k(N) ≥ N * exp(-C * (log N)^(1 / Nat.clog 2 k))`.
In particular, `r_3(N), r_4(N) ≥ N * exp(-C (log N)^(1/2))`,
`r_5(N)..r_8(N) ≥ N * exp(-C (log N)^(1/3))`, `r_9(N)..r_16(N) ≥ N * exp(-C (log N)^(1/4))`, etc. -/
theorem rankin_general_k_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (N : ℝ)) ^ ((1 : ℝ) / (Nat.clog 2 k : ℝ))) ≤
        (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} : ℕ) := by
  let ℓ : ℕ := Nat.clog 2 k - 1
  have hclog_ge2 : 2 ≤ Nat.clog 2 k := by
    by_contra hlt
    have hle1 : Nat.clog 2 k ≤ 1 := by omega
    have hpow := Nat.le_pow_clog (by omega : 1 < 2) k
    have hpow2 : 2 ^ Nat.clog 2 k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hle1
    omega
  have hℓ_succ : ℓ + 1 = Nat.clog 2 k := by omega
  have hpow_lt : 2 ^ ℓ * 1 < k := by
    rw [mul_one]
    have hlt : ℓ < Nat.clog 2 k := by omega
    exact (Nat.lt_clog_iff_pow_lt (by omega)).mp hlt
  obtain ⟨C, hC_pos, N₀, hN₀⟩ := rankin_inductive ℓ 1 k (by omega) hpow_lt
  refine ⟨C, hC_pos, N₀, fun N hN => ?_⟩
  change (N : ℝ) * Real.exp (-C * (Real.log (N : ℝ)) ^ ((1 : ℝ) / (Nat.clog 2 k : ℝ))) ≤ (rK k N : ℝ)
  obtain ⟨A, hA_sub, hA_free, hA_card⟩ := hN₀ N hN
  rw [hℓ_succ] at hA_card
  let A' : Finset ℕ := A.image (· + 1)
  have hA'_card : A'.card = A.card := Finset.card_image_of_injective A (fun x y h => by omega)
  have hA'_sub : A' ⊆ Finset.Icc 1 N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxN : x < N := Finset.mem_range.mp (hA_sub hx)
    rw [Finset.mem_Icc]; omega
  have hA'_free : IsKApFree k A' :=
    isKApFree_image_add_left (polyAPFree_one_imp_isKApFree hA_free)
  have hle : (A.card : ℝ) ≤ (rK k N : ℝ) := by
    have : A.card ≤ rK k N := by
      rw [← hA'_card]
      exact card_le_rK hA'_sub hA'_free
    exact_mod_cast this
  exact le_trans hA_card hle

end BehrendAndRankin

/-! ## Section 4: Roth (1953) Quantitative Fourier Density-Increment Upper Bound (`O(N / log log N)`) -/

section RothFourier

private noncomputable def eChar (M : ℕ) (x : ZMod M) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / (M : ℂ))

private lemma eChar_zero (M : ℕ) : eChar M 0 = 1 := by
  simp [eChar]

private lemma eChar_norm (M : ℕ) (x : ZMod M) : ‖eChar M x‖ = 1 := by
  dsimp only [eChar]
  have hrew : (2 * Real.pi * Complex.I * (x.val : ℂ) / (M : ℂ)) =
      (((2 * Real.pi * (x.val : ℝ) / (M : ℝ) : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [hrew, Complex.norm_exp_ofReal_mul_I]

private lemma eChar_add {M : ℕ} [NeZero M] (x y : ZMod M) :
    eChar M (x + y) = eChar M x * eChar M y := by
  dsimp only [eChar]
  rw [← Complex.exp_add]
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hval : (x + y).val = (x.val + y.val) % M := ZMod.val_add x y
  let q : ℕ := (x.val + y.val) / M
  have hdiv : M * q + (x + y).val = x.val + y.val := by
    rw [hval]; exact Nat.div_add_mod (x.val + y.val) M
  have hdivC : ((x.val : ℂ) + (y.val : ℂ)) = ((x + y).val : ℂ) + (q : ℂ) * (M : ℂ) := by
    have : (x.val + y.val : ℕ) = (x + y).val + q * M := by linarith
    exact_mod_cast this
  have hexp_eq :
      2 * Real.pi * Complex.I * (x.val : ℂ) / (M : ℂ) +
      2 * Real.pi * Complex.I * (y.val : ℂ) / (M : ℂ) =
      2 * Real.pi * Complex.I * ((x + y).val : ℂ) / (M : ℂ) +
      (q : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    have h1 : 2 * Real.pi * Complex.I * (x.val : ℂ) / (M : ℂ) +
        2 * Real.pi * Complex.I * (y.val : ℂ) / (M : ℂ) =
        2 * Real.pi * Complex.I * ((x.val : ℂ) + (y.val : ℂ)) / (M : ℂ) := by ring
    rw [h1, hdivC]
    field_simp [hMne]
  rw [hexp_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma eChar_neg {M : ℕ} [NeZero M] (x : ZMod M) :
    eChar M (-x) = starRingEnd ℂ (eChar M x) := by
  have hmul : eChar M (-x) * eChar M x = 1 := by
    rw [← eChar_add, neg_add_cancel, eChar_zero]
  have hconj : starRingEnd ℂ (eChar M x) * eChar M x = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, eChar_norm]
    norm_num
  have hne : eChar M x ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hne (hmul.trans hconj.symm)

private lemma eChar_ne_one_of_ne_zero {M : ℕ} [NeZero M] {x : ZMod M} (hx : x ≠ 0) :
    eChar M x ≠ 1 := by
  dsimp only [eChar]
  intro heq
  rw [Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨n, hn⟩
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hratio : ((x.val : ℂ) / (M : ℂ)) = (n : ℂ) := by
    have h1 : (2 * Real.pi * Complex.I : ℂ) * ((x.val : ℂ) / (M : ℂ)) =
        (2 * Real.pi * Complex.I : ℂ) * (n : ℂ) := by
      calc
        (2 * Real.pi * Complex.I : ℂ) * ((x.val : ℂ) / (M : ℂ)) =
            2 * Real.pi * Complex.I * (x.val : ℂ) / (M : ℂ) := by ring
        _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
        _ = (2 * Real.pi * Complex.I : ℂ) * (n : ℂ) := by ring
    exact mul_left_cancel₀ h2piI h1
  have hreal : (x.val : ℝ) / (M : ℝ) = (n : ℝ) := by
    have h1 : (((x.val : ℝ) / (M : ℝ) : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
      push_cast; exact hratio
    exact Complex.ofReal_injective h1
  have hval_pos : 0 < x.val := by
    by_contra h0
    have hval0 : x.val = 0 := by omega
    exact hx ((ZMod.val_eq_zero x).mp hval0)
  have hval_lt : x.val < M := ZMod.val_lt x
  have hlt1 : (0 : ℝ) < (n : ℝ) := by
    rw [← hreal]; exact div_pos (by exact_mod_cast hval_pos) hMpos
  have hlt2 : (n : ℝ) < 1 := by
    rw [← hreal, div_lt_one hMpos]; exact_mod_cast hval_lt
  have hn_pos : (0 : ℤ) < n := by exact_mod_cast hlt1
  have hn_lt1 : n < (1 : ℤ) := by exact_mod_cast hlt2
  omega

private lemma sum_eChar {M : ℕ} [NeZero M] (r : ZMod M) :
    (∑ x : ZMod M, eChar M (r * x)) = if r = 0 then (M : ℂ) else 0 := by
  split_ifs with hr
  · subst hr
    simp [eChar_zero, ZMod.card]
  · let S : ℂ := ∑ x : ZMod M, eChar M (r * x)
    have hshift : eChar M r * S = S := by
      dsimp only [S]
      rw [Finset.mul_sum]
      have h1 : (∑ x : ZMod M, eChar M r * eChar M (r * x)) =
          ∑ x : ZMod M, eChar M (r * (x + 1)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [mul_add, mul_one, add_comm, eChar_add]
      rw [h1]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod M)) (fun x => eChar M (r * x))
    have hmul0 : (eChar M r - 1) * S = 0 := by linear_combination hshift
    have hne : eChar M r - 1 ≠ 0 := sub_ne_zero.mpr (eChar_ne_one_of_ne_zero hr)
    exact (mul_eq_zero.mp hmul0).resolve_left hne

private noncomputable def dft (M : ℕ) [NeZero M] (f : ZMod M → ℂ) (r : ZMod M) : ℂ :=
  ∑ x : ZMod M, f x * eChar M (r * x)

private lemma parseval_dft {M : ℕ} [NeZero M] (f : ZMod M → ℂ) :
    (∑ r : ZMod M, ‖dft M f r‖ ^ 2) = (M : ℝ) * ∑ x : ZMod M, ‖f x‖ ^ 2 := by
  have hC : (∑ r : ZMod M, dft M f r * starRingEnd ℂ (dft M f r)) =
      (M : ℂ) * ∑ x : ZMod M, f x * starRingEnd ℂ (f x) := by
    have hexp : ∀ r : ZMod M,
        dft M f r * starRingEnd ℂ (dft M f r) =
          ∑ x : ZMod M, ∑ y : ZMod M, f x * starRingEnd ℂ (f y) * eChar M (r * (x - y)) := by
      intro r
      dsimp only [dft]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_mul, ← eChar_neg]
      have harg : eChar M (r * x) * eChar M (-(r * y)) = eChar M (r * (x - y)) := by
        rw [← eChar_add]; congr 1; ring
      calc
        f x * eChar M (r * x) * (starRingEnd ℂ (f y) * eChar M (-(r * y))) =
            f x * starRingEnd ℂ (f y) * (eChar M (r * x) * eChar M (-(r * y))) := by ring
        _ = f x * starRingEnd ℂ (f y) * eChar M (r * (x - y)) := by rw [harg]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2; ext x
      rw [Finset.sum_comm]
    have hinner : ∀ x : ZMod M,
        (∑ y : ZMod M, ∑ r : ZMod M, f x * starRingEnd ℂ (f y) * eChar M (r * (x - y))) =
          (M : ℂ) * (f x * starRingEnd ℂ (f x)) := by
      intro x
      have hpull : ∀ y : ZMod M,
          (∑ r : ZMod M, f x * starRingEnd ℂ (f y) * eChar M (r * (x - y))) =
            f x * starRingEnd ℂ (f y) * (if x - y = 0 then (M : ℂ) else 0) := by
        intro y
        rw [← Finset.mul_sum]
        congr 1
        have hcomm : (∑ r : ZMod M, eChar M (r * (x - y))) = ∑ r : ZMod M, eChar M ((x - y) * r) := by
          refine Finset.sum_congr rfl fun r _ => by rw [mul_comm]
        rw [hcomm, sum_eChar]
      simp_rw [hpull]
      have hite : ∀ y : ZMod M,
          f x * starRingEnd ℂ (f y) * (if x - y = 0 then (M : ℂ) else 0) =
            if y = x then (M : ℂ) * (f x * starRingEnd ℂ (f x)) else 0 := by
        intro y
        by_cases hxy : y = x
        · subst hxy; simp [mul_comm]
        · have hsub : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
          simp [hxy, hsub]
      simp_rw [hite]
      simp
    simp_rw [hinner, ← Finset.mul_sum]
  have hre := congrArg Complex.re hC
  have hmul_re : ∀ z : ℂ, (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  simp only [Complex.re_sum, hmul_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at hre
  exact hre

private lemma trilinear_3ap_eq_dft {M : ℕ} [NeZero M] (f g h : ZMod M → ℂ) :
    (∑ r : ZMod M, dft M f r * dft M g r * dft M h (-2 * r)) =
      (M : ℂ) * ∑ x : ZMod M, ∑ y : ZMod M, f x * g (2 * y - x) * h y := by
  have hexp : ∀ r : ZMod M,
      dft M f r * dft M g r * dft M h (-2 * r) =
        ∑ x : ZMod M, ∑ z : ZMod M, ∑ y : ZMod M,
          f x * g z * h y * eChar M ((x + z - 2 * y) * r) := by
    intro r
    dsimp only [dft]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_lhs => arg 1; rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have he : eChar M (r * x) * eChar M (r * z) * eChar M (-2 * r * y) =
        eChar M ((x + z - 2 * y) * r) := by
      rw [← eChar_add, ← eChar_add]
      congr 1; ring
    calc
      f x * eChar M (r * x) * (g z * eChar M (r * z)) * (h y * eChar M (-2 * r * y)) =
          f x * g z * h y * (eChar M (r * x) * eChar M (r * z) * eChar M (-2 * r * y)) := by ring
      _ = f x * g z * h y * eChar M ((x + z - 2 * y) * r) := by rw [he]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext x
    rw [Finset.sum_comm]
    arg 2; ext z
    rw [Finset.sum_comm]
  have hinner : ∀ x : ZMod M,
      (∑ z : ZMod M, ∑ y : ZMod M, ∑ r : ZMod M,
          f x * g z * h y * eChar M ((x + z - 2 * y) * r)) =
        (M : ℂ) * ∑ y : ZMod M, f x * g (2 * y - x) * h y := by
    intro x
    rw [Finset.sum_comm]
    have hinner2 : ∀ y : ZMod M,
        (∑ z : ZMod M, ∑ r : ZMod M, f x * g z * h y * eChar M ((x + z - 2 * y) * r)) =
          (M : ℂ) * (f x * g (2 * y - x) * h y) := by
      intro y
      have hterm : ∀ z : ZMod M,
          (∑ r : ZMod M, f x * g z * h y * eChar M ((x + z - 2 * y) * r)) =
            if z = 2 * y - x then (M : ℂ) * (f x * g (2 * y - x) * h y) else 0 := by
        intro z
        rw [← Finset.mul_sum, sum_eChar]
        by_cases hz : z = 2 * y - x
        · subst hz
          simp [mul_comm]
        · have hne : x + z - 2 * y ≠ 0 := by
            intro h0
            apply hz
            linear_combination h0
          simp [hz, hne]
      simp_rw [hterm]
      simp
    simp_rw [hinner2, ← Finset.mul_sum]
  simp_rw [hinner, ← Finset.mul_sum]

private lemma neg_two_mul_bijective_odd (N : ℕ) :
    Function.Bijective (fun r : ZMod (2 * N + 1) => (-2 : ZMod (2 * N + 1)) * r) := by
  have : NeZero (2 * N + 1) := ⟨by omega⟩
  have hinv : (-2 : ZMod (2 * N + 1)) * (-(N + 1 : ZMod (2 * N + 1))) = 1 := by
    have hnat : (2 * (N + 1) : ZMod (2 * N + 1)) = 1 := by
      have : (2 * (N + 1) : ℕ) = (2 * N + 1) + 1 := by omega
      calc
        (2 * (N + 1) : ZMod (2 * N + 1)) = ((2 * (N + 1) : ℕ) : ZMod (2 * N + 1)) := by push_cast; rfl
        _ = (((2 * N + 1) + 1 : ℕ) : ZMod (2 * N + 1)) := by rw [this]
        _ = 1 := by simp
    linear_combination hnat
  refine ⟨?_, ?_⟩
  · intro r₁ r₂ heq
    have h1 := congrArg (fun z => (-(N + 1 : ZMod (2 * N + 1))) * z) heq
    have hinv' : (-(N + 1 : ZMod (2 * N + 1))) * (-2 : ZMod (2 * N + 1)) = 1 := by
      linear_combination hinv
    calc
      r₁ = (-(N + 1 : ZMod (2 * N + 1))) * (-2 : ZMod (2 * N + 1)) * r₁ := by rw [hinv', one_mul]
      _ = (-(N + 1 : ZMod (2 * N + 1))) * ((-2 : ZMod (2 * N + 1)) * r₁) := by ring
      _ = (-(N + 1 : ZMod (2 * N + 1))) * ((-2 : ZMod (2 * N + 1)) * r₂) := h1
      _ = (-(N + 1 : ZMod (2 * N + 1))) * (-2 : ZMod (2 * N + 1)) * r₂ := by ring
      _ = r₂ := by rw [hinv', one_mul]
  · intro y
    refine ⟨(-(N + 1 : ZMod (2 * N + 1))) * y, ?_⟩
    calc
      (-2 : ZMod (2 * N + 1)) * ((-(N + 1 : ZMod (2 * N + 1))) * y) =
          ((-2 : ZMod (2 * N + 1)) * (-(N + 1 : ZMod (2 * N + 1)))) * y := by ring
      _ = y := by rw [hinv, one_mul]

private lemma roth_trilinear_bound {N : ℕ} [NeZero (2 * N + 1)] (f g h : ZMod (2 * N + 1) → ℂ)
    (hf0 : dft (2 * N + 1) f 0 = 0)
    (U : ℝ) (hU : ∀ r : ZMod (2 * N + 1), r ≠ 0 → ‖dft (2 * N + 1) f r‖ ≤ U) (hU0 : 0 ≤ U) :
    ‖∑ x : ZMod (2 * N + 1), ∑ y : ZMod (2 * N + 1), f x * g (2 * y - x) * h y‖ ≤
      U * Real.sqrt (∑ x : ZMod (2 * N + 1), ‖g x‖ ^ 2) *
          Real.sqrt (∑ x : ZMod (2 * N + 1), ‖h x‖ ^ 2) := by
  let M := 2 * N + 1
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have htri := trilinear_3ap_eq_dft f g h
  have hnorm_eq : (M : ℝ) * ‖∑ x : ZMod M, ∑ y : ZMod M, f x * g (2 * y - x) * h y‖ =
      ‖∑ r : ZMod M, dft M f r * dft M g r * dft M h (-2 * r)‖ := by
    have := congrArg norm htri
    rw [norm_mul, Complex.norm_natCast] at this
    exact this.symm
  have hsum_le : ‖∑ r : ZMod M, dft M f r * dft M g r * dft M h (-2 * r)‖ ≤
      U * ∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h (-2 * r)‖ := by
    calc
      ‖∑ r : ZMod M, dft M f r * dft M g r * dft M h (-2 * r)‖
          ≤ ∑ r : ZMod M, ‖dft M f r * dft M g r * dft M h (-2 * r)‖ := norm_sum_le _ _
      _ = ∑ r : ZMod M, ‖dft M f r‖ * (‖dft M g r‖ * ‖dft M h (-2 * r)‖) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [norm_mul, norm_mul]; ring
      _ ≤ ∑ r : ZMod M, U * (‖dft M g r‖ * ‖dft M h (-2 * r)‖) := by
            refine Finset.sum_le_sum fun r _ => ?_
            by_cases hr : r = 0
            · subst hr
              rw [hf0, norm_zero, zero_mul]
              positivity
            · exact mul_le_mul_of_nonneg_right (hU r hr) (by positivity)
      _ = U * ∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h (-2 * r)‖ := by rw [← Finset.mul_sum]
  have hcs : (∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h (-2 * r)‖) ≤
      Real.sqrt (∑ r : ZMod M, ‖dft M g r‖ ^ 2) *
      Real.sqrt (∑ r : ZMod M, ‖dft M h (-2 * r)‖ ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun r : ZMod M => ‖dft M g r‖) (fun r : ZMod M => ‖dft M h (-2 * r)‖)
    have hnn : 0 ≤ ∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h (-2 * r)‖ :=
      Finset.sum_nonneg fun r _ => by positivity
    have h1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
    exact h1
  have hbij : (∑ r : ZMod M, ‖dft M h (-2 * r)‖ ^ 2) = ∑ r : ZMod M, ‖dft M h r‖ ^ 2 :=
    Fintype.sum_bijective _ (neg_two_mul_bijective_odd N) _ _ fun _ => rfl
  rw [hbij, parseval_dft g, parseval_dft h] at hcs
  have hprod_sqrt :
      Real.sqrt ((M : ℝ) * ∑ x : ZMod M, ‖g x‖ ^ 2) *
      Real.sqrt ((M : ℝ) * ∑ x : ZMod M, ‖h x‖ ^ 2) =
      (M : ℝ) * Real.sqrt (∑ x : ZMod M, ‖g x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod M, ‖h x‖ ^ 2) := by
    rw [Real.sqrt_mul (le_of_lt hMpos), Real.sqrt_mul (le_of_lt hMpos)]
    have hMsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (le_of_lt hMpos)
    calc
      Real.sqrt (M : ℝ) * Real.sqrt (∑ x, ‖g x‖ ^ 2) * (Real.sqrt (M : ℝ) * Real.sqrt (∑ x, ‖h x‖ ^ 2)) =
          (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * Real.sqrt (∑ x, ‖g x‖ ^ 2) *
            Real.sqrt (∑ x, ‖h x‖ ^ 2) := by ring
      _ = (M : ℝ) * Real.sqrt (∑ x, ‖g x‖ ^ 2) * Real.sqrt (∑ x, ‖h x‖ ^ 2) := by rw [hMsq]
  rw [hprod_sqrt] at hcs
  have hcomb : (M : ℝ) * ‖∑ x : ZMod M, ∑ y : ZMod M, f x * g (2 * y - x) * h y‖ ≤
      (M : ℝ) * (U * Real.sqrt (∑ x : ZMod M, ‖g x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod M, ‖h x‖ ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hcs hU0
    linarith only [hnorm_eq, hsum_le, h1]
  exact le_of_mul_le_mul_left hcomb hMpos

private lemma roth_trilinear_bound_mid {N : ℕ} [NeZero (2 * N + 1)] (f g h : ZMod (2 * N + 1) → ℂ)
    (hf0 : dft (2 * N + 1) f 0 = 0)
    (U : ℝ) (hU : ∀ r : ZMod (2 * N + 1), r ≠ 0 → ‖dft (2 * N + 1) f r‖ ≤ U) (hU0 : 0 ≤ U) :
    ‖∑ x : ZMod (2 * N + 1), ∑ y : ZMod (2 * N + 1), g x * f (2 * y - x) * h y‖ ≤
      U * Real.sqrt (∑ x : ZMod (2 * N + 1), ‖g x‖ ^ 2) *
          Real.sqrt (∑ x : ZMod (2 * N + 1), ‖h x‖ ^ 2) := by
  have hsym : (∑ x : ZMod (2 * N + 1), ∑ y : ZMod (2 * N + 1), g x * f (2 * y - x) * h y) =
      ∑ x : ZMod (2 * N + 1), ∑ y : ZMod (2 * N + 1), f x * g (2 * y - x) * h y := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    let σ : ZMod (2 * N + 1) ≃ ZMod (2 * N + 1) :=
      { toFun := fun x => 2 * y - x
        invFun := fun x => 2 * y - x
        left_inv := fun x => by ring
        right_inv := fun x => by ring }
    have hcomp := Equiv.sum_comp σ (fun x => f x * g (2 * y - x) * h y)
    rw [← hcomp]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h2 : 2 * y - (2 * y - x) = x := by ring
    change g x * f (2 * y - x) * h y = f (2 * y - x) * g (2 * y - (2 * y - x)) * h y
    rw [h2]
    ring
  rw [hsym]
  exact roth_trilinear_bound f g h hf0 U hU hU0

private lemma roth_trilinear_bound_last {N : ℕ} [NeZero (2 * N + 1)] (f g h : ZMod (2 * N + 1) → ℂ)
    (hf0 : dft (2 * N + 1) f 0 = 0)
    (U : ℝ) (hU : ∀ r : ZMod (2 * N + 1), r ≠ 0 → ‖dft (2 * N + 1) f r‖ ≤ U) (hU0 : 0 ≤ U) :
    ‖∑ x : ZMod (2 * N + 1), ∑ y : ZMod (2 * N + 1), g x * h (2 * y - x) * f y‖ ≤
      U * Real.sqrt (∑ x : ZMod (2 * N + 1), ‖g x‖ ^ 2) *
          Real.sqrt (∑ x : ZMod (2 * N + 1), ‖h x‖ ^ 2) := by
  let M := 2 * N + 1
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have htri := trilinear_3ap_eq_dft g h f
  have hnorm_eq : (M : ℝ) * ‖∑ x : ZMod M, ∑ y : ZMod M, g x * h (2 * y - x) * f y‖ =
      ‖∑ r : ZMod M, dft M g r * dft M h r * dft M f (-2 * r)‖ := by
    have := congrArg norm htri
    rw [norm_mul, Complex.norm_natCast] at this
    exact this.symm
  have hsum_le : ‖∑ r : ZMod M, dft M g r * dft M h r * dft M f (-2 * r)‖ ≤
      U * ∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h r‖ := by
    calc
      ‖∑ r : ZMod M, dft M g r * dft M h r * dft M f (-2 * r)‖
          ≤ ∑ r : ZMod M, ‖dft M g r * dft M h r * dft M f (-2 * r)‖ := norm_sum_le _ _
      _ = ∑ r : ZMod M, ‖dft M f (-2 * r)‖ * (‖dft M g r‖ * ‖dft M h r‖) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [norm_mul, norm_mul]; ring
      _ ≤ ∑ r : ZMod M, U * (‖dft M g r‖ * ‖dft M h r‖) := by
            refine Finset.sum_le_sum fun r _ => ?_
            by_cases hr : (-2 : ZMod M) * r = 0
            · rw [hr, hf0, norm_zero, zero_mul]; positivity
            · exact mul_le_mul_of_nonneg_right (hU (-2 * r) hr) (by positivity)
      _ = U * ∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h r‖ := by rw [← Finset.mul_sum]
  have hcs : (∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h r‖) ≤
      Real.sqrt (∑ r : ZMod M, ‖dft M g r‖ ^ 2) *
      Real.sqrt (∑ r : ZMod M, ‖dft M h r‖ ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun r : ZMod M => ‖dft M g r‖) (fun r : ZMod M => ‖dft M h r‖)
    have hnn : 0 ≤ ∑ r : ZMod M, ‖dft M g r‖ * ‖dft M h r‖ :=
      Finset.sum_nonneg fun r _ => by positivity
    have h1 := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn, Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h1
    exact h1
  rw [parseval_dft g, parseval_dft h] at hcs
  have hprod_sqrt :
      Real.sqrt ((M : ℝ) * ∑ x : ZMod M, ‖g x‖ ^ 2) *
      Real.sqrt ((M : ℝ) * ∑ x : ZMod M, ‖h x‖ ^ 2) =
      (M : ℝ) * Real.sqrt (∑ x : ZMod M, ‖g x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod M, ‖h x‖ ^ 2) := by
    rw [Real.sqrt_mul (le_of_lt hMpos), Real.sqrt_mul (le_of_lt hMpos)]
    have hMsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (le_of_lt hMpos)
    calc
      Real.sqrt (M : ℝ) * Real.sqrt (∑ x, ‖g x‖ ^ 2) * (Real.sqrt (M : ℝ) * Real.sqrt (∑ x, ‖h x‖ ^ 2)) =
          (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * Real.sqrt (∑ x, ‖g x‖ ^ 2) *
            Real.sqrt (∑ x, ‖h x‖ ^ 2) := by ring
      _ = (M : ℝ) * Real.sqrt (∑ x, ‖g x‖ ^ 2) * Real.sqrt (∑ x, ‖h x‖ ^ 2) := by rw [hMsq]
  rw [hprod_sqrt] at hcs
  have hcomb : (M : ℝ) * ‖∑ x : ZMod M, ∑ y : ZMod M, g x * h (2 * y - x) * f y‖ ≤
      (M : ℝ) * (U * Real.sqrt (∑ x : ZMod M, ‖g x‖ ^ 2) *
        Real.sqrt (∑ x : ZMod M, ‖h x‖ ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hcs hU0
    linarith only [hnorm_eq, hsum_le, h1]
  exact le_of_mul_le_mul_left hcomb hMpos

/-- Core Roth Fourier-Bias Lemma on `Finset.range N`:
If `A ⊆ Finset.range N` is `3`-AP-free with density `α = A.card / N > 0` and `4 ≤ α^2 * N`,
then the balanced function `f(x) = 1_A(x) - α` on `{0, ..., N - 1}` has a nonzero frequency
`r : ZMod (2 * N + 1)` with `‖f̂(r)‖ ≥ α^2 * N / 12`. -/
private lemma roth_fourier_bias {N : ℕ} (hN : 1 ≤ N) {A : Finset ℕ}
    (hA_sub : A ⊆ Finset.range N) (hA_free : ThreeAPFree (A : Set ℕ))
    (h4 : (4 : ℝ) ≤ ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ)) :
    ∃ r : ZMod (2 * N + 1), r ≠ 0 ∧
      ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ) / 12 ≤
        ‖∑ x ∈ Finset.range N,
          ((if x ∈ A then (1 : ℂ) else 0) - (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * ((r.val * x : ℕ) : ℂ) / ((2 * N + 1 : ℕ) : ℂ))‖ := by
  classical
  have : NeZero (2 * N + 1) := ⟨by omega⟩
  let M : ℕ := 2 * N + 1
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hα_le1 : α ≤ 1 := by
    dsimp only [α]
    rw [div_le_one hNpos]
    have : A.card ≤ N := by
      have := Finset.card_le_card hA_sub; simpa using this
    exact_mod_cast this
  have hα_pos : 0 < α := by
    by_contra hle
    push Not at hle
    have hα0 : α = 0 := le_antisymm hle (by positivity)
    change (4 : ℝ) ≤ α ^ 2 * (N : ℝ) at h4
    rw [hα0] at h4
    norm_num at h4
  let indA : ZMod M → ℂ := fun x => if x.val ∈ A then 1 else 0
  let indI : ZMod M → ℂ := fun x => if x.val < N then 1 else 0
  let fBal : ZMod M → ℂ := fun x => indA x - (α : ℂ) * indI x
  -- Embed Finset.range N into ZMod M
  have hsum_range : ∀ g : ℕ → ℂ,
      (∑ x : ZMod M, if x.val < N then g x.val else 0) = ∑ n ∈ Finset.range N, g n := by
    intro g
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
    · intro x hx; exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    · intro x₁ _ x₂ _ hval; exact ZMod.val_injective M hval
    · intro n hn
      have hnN : n < N := Finset.mem_range.mp hn
      refine ⟨(n : ZMod M), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [ZMod.val_natCast_of_lt (by omega)]; exact hnN
      · exact ZMod.val_natCast_of_lt (by omega)
    · intro _ _; rfl
  have hindA_sum : (∑ x : ZMod M, indA x) = (A.card : ℂ) := by
    have h1 : ∀ x : ZMod M, indA x = if x.val < N then (if x.val ∈ A then (1 : ℂ) else 0) else 0 := by
      intro x; dsimp only [indA]
      by_cases hxN : x.val < N
      · rw [if_pos hxN]
      · rw [if_neg hxN]
        have hxA : x.val ∉ A := fun h => hxN (Finset.mem_range.mp (hA_sub h))
        rw [if_neg hxA]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), hsum_range (fun n => if n ∈ A then (1 : ℂ) else 0)]
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range N).filter (· ∈ A) = A := by
      ext n; simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun hn => ⟨hA_sub hn, hn⟩⟩
    simp [hfilt]
  have hindI_sum : (∑ x : ZMod M, indI x) = (N : ℂ) := by
    have := hsum_range (fun _ => (1 : ℂ))
    simpa [indI] using this
  have hf0 : dft M fBal 0 = 0 := by
    simp only [dft, zero_mul, eChar_zero, mul_one, fBal, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hindA_sum, hindI_sum]
    dsimp only [α]
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
    push_cast
    field_simp [hNne]
    ring
  -- L2 norms of indA and indI
  have hindA_l2 : (∑ x : ZMod M, ‖indA x‖ ^ 2) = (A.card : ℝ) := by
    have h1 : ∀ x : ZMod M, ‖indA x‖ ^ 2 = (indA x).re := by
      intro x; dsimp only [indA]; split_ifs <;> simp
    simp_rw [h1, ← Complex.re_sum, hindA_sum]; simp
  have hindI_l2 : (∑ x : ZMod M, ‖indI x‖ ^ 2) = (N : ℝ) := by
    have h1 : ∀ x : ZMod M, ‖indI x‖ ^ 2 = (indI x).re := by
      intro x; dsimp only [indI]; split_ifs <;> simp
    simp_rw [h1, ← Complex.re_sum, hindI_sum]; simp
  -- Count 3-APs in A: only diagonal terms x = y survive!
  have hT_A : (∑ x : ZMod M, ∑ y : ZMod M, indA x * indA (2 * y - x) * indA y) = (A.card : ℂ) := by
    have hterm : ∀ x y : ZMod M,
        indA x * indA (2 * y - x) * indA y = if x = y then indA x else 0 := by
      intro x y
      by_cases hxy : x = y
      · subst hxy
        have h2 : (2 : ZMod M) * x - x = x := by ring
        rw [h2, if_pos rfl]
        dsimp only [indA]; split_ifs <;> simp
      · rw [if_neg hxy]
        dsimp only [indA]
        by_cases hx : x.val ∈ A
        · by_cases hy : y.val ∈ A
          · by_cases hz : (2 * y - x).val ∈ A
            · exfalso
              have hxN : x.val < N := Finset.mem_range.mp (hA_sub hx)
              have hyN : y.val < N := Finset.mem_range.mp (hA_sub hy)
              have hzN : (2 * y - x).val < N := Finset.mem_range.mp (hA_sub hz)
              have hmod : ((x.val + (2 * y - x).val : ℕ) : ZMod M) = ((y.val + y.val : ℕ) : ZMod M) := by
                push_cast; simp; ring
              have heq_nat : x.val + (2 * y - x).val = y.val + y.val := by
                have h1 := congrArg ZMod.val hmod
                rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h1
                exact h1
              have hxy_val : x.val = y.val := hA_free hx hy hz heq_nat
              exact hxy (ZMod.val_injective M hxy_val)
            · simp [hx, hy, hz]
          · simp [hx, hy]
        · simp [hx]
    simp_rw [hterm]
    have hdiag : ∀ x : ZMod M, (∑ y : ZMod M, if x = y then indA x else 0) = indA x := by
      intro x; simp
    simp_rw [hdiag]
    exact hindA_sum
  -- Lower bound 3-APs in Finset.range N: at least N^2 / 2!
  have hT_I_re : (N : ℝ) ^ 2 / 2 ≤
      (∑ x : ZMod M, ∑ y : ZMod M, indI x * indI (2 * y - x) * indI y).re := by
    let P : Finset (ℕ × ℕ) :=
      ((Finset.range N) ×ˢ (Finset.range N)).filter (fun p => p.1 % 2 = p.2 % 2)
    have hP_card : (N : ℝ) ^ 2 / 2 ≤ (P.card : ℝ) := by
      let Ev := (Finset.range N).filter (fun n => n % 2 = 0)
      let Od := (Finset.range N).filter (fun n => n % 2 ≠ 0)
      have hEO : Ev.card + Od.card = N := by
        simpa [Ev, Od] using Finset.card_filter_add_card_filter_not (s := Finset.range N) (p := fun n => n % 2 = 0)
      have hP_eq : P = (Ev ×ˢ Ev) ∪ (Od ×ˢ Od) := by
        ext ⟨a, b⟩
        simp only [P, Ev, Od, Finset.mem_filter, Finset.mem_product, Finset.mem_union]
        constructor
        · rintro ⟨⟨ha, hb⟩, hmod⟩
          by_cases h0 : a % 2 = 0
          · left; exact ⟨⟨ha, h0⟩, ⟨hb, by omega⟩⟩
          · right; exact ⟨⟨ha, h0⟩, ⟨hb, by omega⟩⟩
        · rintro (⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩ | ⟨⟨ha, ha1⟩, ⟨hb, hb1⟩⟩)
          · exact ⟨⟨ha, hb⟩, by omega⟩
          · exact ⟨⟨ha, hb⟩, by omega⟩
      have hdisj : Disjoint (Ev ×ˢ Ev) (Od ×ˢ Od) := by
        rw [Finset.disjoint_left]
        rintro ⟨a, b⟩ h1 h2
        rw [Finset.mem_product, Finset.mem_filter] at h1 h2
        exact h2.1.2 h1.1.2
      have hcard : P.card = Ev.card ^ 2 + Od.card ^ 2 := by
        rw [hP_eq, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product, sq, sq]
      have hnat : N ^ 2 ≤ 2 * P.card := by
        rw [hcard, ← hEO]
        zify; nlinarith [sq_nonneg ((Ev.card : ℤ) - (Od.card : ℤ))]
      have hreal : (N : ℝ) ^ 2 ≤ 2 * (P.card : ℝ) := by exact_mod_cast hnat
      linarith only [hreal]
    -- Show P injects into pairs (x, y) : ZMod M × ZMod M where indI x * indI (2y - x) * indI y = 1
    let good : Finset (ZMod M × ZMod M) :=
      Finset.univ.filter (fun p => p.1.val < N ∧ (2 * p.2 - p.1).val < N ∧ p.2.val < N)
    have hre_eq : (∑ x : ZMod M, ∑ y : ZMod M, indI x * indI (2 * y - x) * indI y).re =
        (good.card : ℝ) := by
      rw [Complex.re_sum]
      simp_rw [Complex.re_sum]
      rw [← Fintype.sum_prod_type']
      have hterm : ∀ p : ZMod M × ZMod M,
          (indI p.1 * indI (2 * p.2 - p.1) * indI p.2).re =
            if p.1.val < N ∧ (2 * p.2 - p.1).val < N ∧ p.2.val < N then (1 : ℝ) else 0 := by
        rintro ⟨x, y⟩
        dsimp only [indI]
        by_cases h1 : x.val < N <;> by_cases h2 : (2 * y - x).val < N <;> by_cases h3 : y.val < N <;>
          simp [h1, h2, h3]
      simp_rw [hterm]
      rw [← Finset.sum_filter]
      simp [good]
    have hP_le_good : P.card ≤ good.card := by
      refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => ((p.1 : ZMod M), (((p.1 + p.2) / 2 : ℕ) : ZMod M))) ?_ ?_
      · rintro ⟨a, c⟩ hp
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
        rcases hp with ⟨⟨ha, hc⟩, hmod⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
        · rw [ZMod.val_natCast_of_lt (by omega)]; exact ha
        · have h2m : 2 * ((a + c) / 2) = a + c := by omega
          have heq : (2 : ZMod M) * (((a + c) / 2 : ℕ) : ZMod M) - (a : ZMod M) = (c : ZMod M) := by
            have h1 : ((2 * ((a + c) / 2) : ℕ) : ZMod M) = ((a + c : ℕ) : ZMod M) := by rw [h2m]
            push_cast at h1
            linear_combination h1
          rw [heq, ZMod.val_natCast_of_lt (by omega)]; exact hc
        · rw [ZMod.val_natCast_of_lt (by omega)]; omega
      · rintro ⟨a₁, c₁⟩ hp₁ ⟨a₂, c₂⟩ hp₂ heq
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp₁ hp₂
        have h1 : ((a₁ : ZMod M)) = ((a₂ : ZMod M)) := congrArg Prod.fst heq
        have h2 : (((a₁ + c₁) / 2 : ℕ) : ZMod M) = (((a₂ + c₂) / 2 : ℕ) : ZMod M) := congrArg Prod.snd heq
        have ha : a₁ = a₂ := by
          have := congrArg ZMod.val h1
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
          exact this
        have hm : (a₁ + c₁) / 2 = (a₂ + c₂) / 2 := by
          have := congrArg ZMod.val h2
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
          exact this
        have hc : c₁ = c₂ := by omega
        exact Prod.ext ha hc
    rw [hre_eq]
    exact le_trans hP_card (by exact_mod_cast hP_le_good)
  -- Telescoping 3-linear identity: T(A,A,A) - α^3 T(I,I,I) = T(f,A,A) + α T(I,f,A) + α^2 T(I,I,f)
  let T : (ZMod M → ℂ) → (ZMod M → ℂ) → (ZMod M → ℂ) → ℂ :=
    fun u v w => ∑ x : ZMod M, ∑ y : ZMod M, u x * v (2 * y - x) * w y
  have htelesc : T indA indA indA - ((α : ℂ) ^ 3) * T indI indI indI =
      T fBal indA indA + (α : ℂ) * T indI fBal indA + ((α : ℂ) ^ 2) * T indI indI fBal := by
    dsimp only [T]
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    dsimp only [fBal]
    ring
  -- Lower bound the LHS norm using real part
  have hlhs_ge : α ^ 3 * (N : ℝ) ^ 2 / 4 ≤ ‖T indA indA indA - ((α : ℂ) ^ 3) * T indI indI indI‖ := by
    have hneg_re : α ^ 3 * (N : ℝ) ^ 2 / 4 ≤ (((α : ℂ) ^ 3) * T indI indI indI - T indA indA indA).re := by
      have hTI_re : (((α : ℂ) ^ 3) * T indI indI indI).re = α ^ 3 * (T indI indI indI).re := by
        have hcast : ((α : ℂ) ^ 3) = ((α ^ 3 : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hTA_re : (T indA indA indA).re = α * (N : ℝ) := by
        dsimp only [T]; rw [hT_A]; simp [α, div_mul_cancel₀ _ (ne_of_gt hNpos)]
      rw [Complex.sub_re, hTI_re, hTA_re]
      have h1 : α ^ 3 * ((N : ℝ) ^ 2 / 2) ≤ α ^ 3 * (T indI indI indI).re :=
        mul_le_mul_of_nonneg_left hT_I_re (by positivity)
      have h2 : α * (N : ℝ) ≤ α ^ 3 * (N : ℝ) ^ 2 / 4 := by
        have hmul := mul_le_mul_of_nonneg_left h4 (show 0 ≤ α * (N : ℝ) by positivity)
        linarith only [hmul]
      linarith only [h1, h2]
    have hnorm : ‖T indA indA indA - ((α : ℂ) ^ 3) * T indI indI indI‖ =
        ‖((α : ℂ) ^ 3) * T indI indI indI - T indA indA indA‖ := norm_sub_rev _ _
    rw [hnorm]
    exact le_trans hneg_re (Complex.re_le_norm _)
  -- Pick r* ≠ 0 maximizing ‖dft M fBal r‖
  let S_nz : Finset (ZMod M) := Finset.univ.erase 0
  have hSnz_ne : S_nz.Nonempty := by
    refine ⟨(1 : ZMod M), Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    have : Fact (1 < M) := ⟨by omega⟩
    exact one_ne_zero
  obtain ⟨rstar, hrstar_mem, hrstar_max⟩ := Finset.exists_max_image S_nz (fun r => ‖dft M fBal r‖) hSnz_ne
  have hrstar_ne : rstar ≠ 0 := (Finset.mem_erase.mp hrstar_mem).1
  let U : ℝ := ‖dft M fBal rstar‖
  have hU_nn : 0 ≤ U := norm_nonneg _
  have hU_bound : ∀ r : ZMod M, r ≠ 0 → ‖dft M fBal r‖ ≤ U := fun r hr =>
    hrstar_max r (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)
  -- Upper bound the 3 RHS terms via roth_trilinear_bound
  have hb1 : ‖T fBal indA indA‖ ≤ U * (α * (N : ℝ)) := by
    have h := roth_trilinear_bound fBal indA indA hf0 U hU_bound hU_nn
    rw [hindA_l2, mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)] at h
    have hAeq : (A.card : ℝ) = α * (N : ℝ) := by
      dsimp only [α]; exact (div_mul_cancel₀ _ (ne_of_gt hNpos)).symm
    rw [hAeq] at h
    exact h
  have hb2 : ‖(α : ℂ) * T indI fBal indA‖ ≤ U * (α * (N : ℝ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hα_pos)]
    have h := roth_trilinear_bound_mid fBal indI indA hf0 U hU_bound hU_nn
    rw [hindI_l2, hindA_l2] at h
    have hAeq : (A.card : ℝ) = α * (N : ℝ) := by
      dsimp only [α]; exact (div_mul_cancel₀ _ (ne_of_gt hNpos)).symm
    have hsq : Real.sqrt (N : ℝ) * Real.sqrt (A.card : ℝ) ≤ (N : ℝ) := by
      rw [hAeq, Real.sqrt_mul (le_of_lt hα_pos)]
      have hαsq : Real.sqrt α ≤ 1 := by
        calc Real.sqrt α ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hα_le1
          _ = 1 := Real.sqrt_one
      have hNsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hNpos)
      calc
        Real.sqrt (N : ℝ) * (Real.sqrt α * Real.sqrt (N : ℝ)) =
            Real.sqrt α * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
        _ = Real.sqrt α * (N : ℝ) := by rw [hNsq]
        _ ≤ 1 * (N : ℝ) := mul_le_mul_of_nonneg_right hαsq (le_of_lt hNpos)
        _ = (N : ℝ) := one_mul _
    have h1 : ‖T indI fBal indA‖ ≤ U * (N : ℝ) := by
      calc ‖T indI fBal indA‖ ≤ U * Real.sqrt (N : ℝ) * Real.sqrt (A.card : ℝ) := h
        _ = U * (Real.sqrt (N : ℝ) * Real.sqrt (A.card : ℝ)) := by ring
        _ ≤ U * (N : ℝ) := mul_le_mul_of_nonneg_left hsq hU_nn
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hα_pos)
    linarith only [h2]
  have hb3 : ‖((α : ℂ) ^ 2) * T indI indI fBal‖ ≤ U * (α * (N : ℝ)) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hα_pos)]
    have h := roth_trilinear_bound_last fBal indI indI hf0 U hU_bound hU_nn
    rw [hindI_l2] at h
    have hNsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hNpos)
    have h1 : ‖T indI indI fBal‖ ≤ U * (N : ℝ) := by
      calc ‖T indI indI fBal‖ ≤ U * Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := h
        _ = U * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by ring
        _ = U * (N : ℝ) := by rw [hNsq]
    have h2 : α ^ 2 * ‖T indI indI fBal‖ ≤ α ^ 2 * (U * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg α)
    have h3 : α ^ 2 * (U * (N : ℝ)) ≤ α * (U * (N : ℝ)) := by
      have hα2 : α ^ 2 ≤ α := by nlinarith only [hα_pos, hα_le1]
      exact mul_le_mul_of_nonneg_right hα2 (by positivity)
    linarith only [h2, h3]
  have htri_rhs : ‖T indA indA indA - ((α : ℂ) ^ 3) * T indI indI indI‖ ≤ 3 * U * (α * (N : ℝ)) := by
    rw [htelesc]
    calc
      ‖T fBal indA indA + (α : ℂ) * T indI fBal indA + ((α : ℂ) ^ 2) * T indI indI fBal‖
          ≤ ‖T fBal indA indA + (α : ℂ) * T indI fBal indA‖ + ‖((α : ℂ) ^ 2) * T indI indI fBal‖ :=
        norm_add_le _ _
      _ ≤ ‖T fBal indA indA‖ + ‖(α : ℂ) * T indI fBal indA‖ + ‖((α : ℂ) ^ 2) * T indI indI fBal‖ := by
        linarith only [norm_add_le (T fBal indA indA) ((α : ℂ) * T indI fBal indA)]
      _ ≤ U * (α * (N : ℝ)) + U * (α * (N : ℝ)) + U * (α * (N : ℝ)) := by linarith only [hb1, hb2, hb3]
      _ = 3 * U * (α * (N : ℝ)) := by ring
  have hU_ge : α ^ 2 * (N : ℝ) / 12 ≤ U := by
    have hαN_pos : 0 < α * (N : ℝ) := mul_pos hα_pos hNpos
    have hcomb : α ^ 3 * (N : ℝ) ^ 2 / 4 ≤ 3 * U * (α * (N : ℝ)) := le_trans hlhs_ge htri_rhs
    have hrew : (α ^ 2 * (N : ℝ) / 12) * (3 * (α * (N : ℝ))) = α ^ 3 * (N : ℝ) ^ 2 / 4 := by ring
    have hmul : (α ^ 2 * (N : ℝ) / 12) * (3 * (α * (N : ℝ))) ≤ U * (3 * (α * (N : ℝ))) := by
      linarith only [hcomb, hrew]
    exact le_of_mul_le_mul_right hmul (by linarith only [hαN_pos])
  -- Rewrite dft M fBal rstar as a sum over Finset.range N
  have hdft_eq : dft M fBal rstar =
      ∑ x ∈ Finset.range N,
        ((if x ∈ A then (1 : ℂ) else 0) - ((α : ℂ))) *
          Complex.exp (2 * Real.pi * Complex.I * ((rstar.val * x : ℕ) : ℂ) / (M : ℂ)) := by
    dsimp only [dft, fBal, indA, indI]
    have hfilt : ∀ x : ZMod M,
        ((if x.val ∈ A then (1 : ℂ) else 0) - (α : ℂ) * (if x.val < N then 1 else 0)) * eChar M (rstar * x) =
          if x.val < N then
            ((if x.val ∈ A then (1 : ℂ) else 0) - (α : ℂ)) *
              Complex.exp (2 * Real.pi * Complex.I * ((rstar.val * x.val : ℕ) : ℂ) / (M : ℂ))
          else 0 := by
      intro x
      by_cases hxN : x.val < N
      · rw [if_pos hxN, if_pos hxN, mul_one]
        congr 1
        dsimp only [eChar]
        have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
        have hval : (rstar * x).val = (rstar.val * x.val) % M := ZMod.val_mul rstar x
        let q : ℕ := (rstar.val * x.val) / M
        have hdiv : M * q + (rstar * x).val = rstar.val * x.val := by
          rw [hval]; exact Nat.div_add_mod _ M
        have hdivC : ((rstar.val * x.val : ℕ) : ℂ) = ((rstar * x).val : ℂ) + (q : ℂ) * (M : ℂ) := by
          have : rstar.val * x.val = (rstar * x).val + q * M := by linarith
          exact_mod_cast this
        have hexp_eq :
            2 * Real.pi * Complex.I * ((rstar.val * x.val : ℕ) : ℂ) / (M : ℂ) =
              2 * Real.pi * Complex.I * ((rstar * x).val : ℂ) / (M : ℂ) +
                (q : ℤ) * (2 * Real.pi * Complex.I) := by
          rw [hdivC]; push_cast; field_simp [hMne]
        rw [hexp_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · rw [if_neg hxN, if_neg hxN, mul_zero]
        have hxA : x.val ∉ A := fun h => hxN (Finset.mem_range.mp (hA_sub h))
        simp [hxA]
    rw [Finset.sum_congr rfl (fun x _ => hfilt x)]
    exact hsum_range (fun n => ((if n ∈ A then (1 : ℂ) else 0) - (α : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((rstar.val * n : ℕ) : ℂ) / (M : ℂ)))
  refine ⟨rstar, hrstar_ne, ?_⟩
  rw [← hdft_eq]
  exact hU_ge

/-- **Public Spectral Dichotomy / Fourier-Bias Barrier Theorem (Roth 1953):**
Every `3`-AP-free subset `A ⊆ {1, ..., N}` of density `α = |A| / N` with `4 ≤ α^2 * N`
MUST exhibit a large non-trivial discrete Fourier coefficient `‖f̂(r)‖ ≥ α^2 * N / 12`
on `ZMod (2 * N + 1)` (`r ≠ 0`). -/
theorem roth_fourier_spectral_dichotomy (N : ℕ) (hN : 1 ≤ N) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N)
    (hA_free : ∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A)
    (h4 : (4 : ℝ) ≤ ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ)) :
    ∃ r : ZMod (2 * N + 1), r ≠ 0 ∧
      ((A.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ) / 12 ≤
        ‖∑ x ∈ Finset.Icc 1 N,
          ((if x ∈ A then (1 : ℂ) else 0) - (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * ((r.val * (x - 1) : ℕ) : ℂ) / ((2 * N + 1 : ℕ) : ℂ))‖ := by
  let B : Finset ℕ := A.image (· - 1)
  have hB_card : B.card = A.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    dsimp only at hxy
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hA_sub hx)).1
    have hy1 : 1 ≤ y := (Finset.mem_Icc.mp (hA_sub hy)).1
    omega
  have hB_sub : B ⊆ Finset.range N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxI := Finset.mem_Icc.mp (hA_sub hx)
    rw [Finset.mem_range]; omega
  have hB_free : ThreeAPFree (B : Set ℕ) := by
    rw [← isKApFree_three_iff_threeAPFree]
    have himg : B.image (· + 1) = A := by
      ext x; simp only [B, Finset.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have hz1 := (Finset.mem_Icc.mp (hA_sub hz)).1
        have : z - 1 + 1 = z := by omega
        rwa [this]
      · intro hx
        have hx1 := (Finset.mem_Icc.mp (hA_sub hx)).1
        exact ⟨x - 1, ⟨x, hx, rfl⟩, by omega⟩
    exact isKApFree_of_image_add_left (c := 1) (himg.symm ▸ hA_free)
  have h4B : (4 : ℝ) ≤ ((B.card : ℝ) / (N : ℝ)) ^ 2 * (N : ℝ) := by rwa [hB_card]
  obtain ⟨r, hr_ne, hbound⟩ := roth_fourier_bias hN hB_sub hB_free h4B
  rw [hB_card] at hbound
  refine ⟨r, hr_ne, ?_⟩
  have hsum_eq :
      (∑ x ∈ Finset.range N,
        ((if x ∈ B then (1 : ℂ) else 0) - (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((r.val * x : ℕ) : ℂ) / ((2 * N + 1 : ℕ) : ℂ))) =
      ∑ x ∈ Finset.Icc 1 N,
        ((if x ∈ A then (1 : ℂ) else 0) - (((A.card : ℝ) / (N : ℝ) : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((r.val * (x - 1) : ℕ) : ℂ) / ((2 * N + 1 : ℕ) : ℂ)) := by
    refine Finset.sum_bij (fun x _ => x + 1) ?_ ?_ ?_ ?_
    · intro x hx; rw [Finset.mem_Icc]; have := Finset.mem_range.mp hx; omega
    · intro x₁ _ x₂ _ h; omega
    · intro y hy; rw [Finset.mem_Icc] at hy
      exact ⟨y - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro x hx
      have hmem : x ∈ B ↔ x + 1 ∈ A := by
        simp only [B, Finset.mem_image]
        constructor
        · rintro ⟨z, hz, hzx⟩
          have hz1 := (Finset.mem_Icc.mp (hA_sub hz)).1
          have : x + 1 = z := by omega
          rwa [this]
        · intro h; exact ⟨x + 1, h, by omega⟩
      simp [hmem]
  rwa [← hsum_eq]

private lemma dirichlet_approx (θ : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ ∃ p : ℤ, |(q : ℝ) * θ - (p : ℝ)| ≤ 1 / (Q : ℝ) := by
  let f : ℕ → ℕ := fun k => Nat.floor ((Q : ℝ) * Int.fract ((k : ℝ) * θ))
  have hmaps : ∀ k ∈ Finset.range (Q + 1), f k ∈ Finset.range Q := by
    intro k _
    rw [Finset.mem_range]
    have hlt : Int.fract ((k : ℝ) * θ) < 1 := Int.fract_lt_one _
    have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    have hprod : (Q : ℝ) * Int.fract ((k : ℝ) * θ) < (Q : ℝ) := by nlinarith only [hQpos, hlt]
    exact (Nat.floor_lt (by positivity)).mpr hprod
  have hcard : (Finset.range Q).card < (Finset.range (Q + 1)).card := by simp
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hk₁' : k₁ ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₁)
  have hk₂' : k₂ ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₂)
  wlog hlt : k₁ < k₂ generalizing k₁ k₂
  · exact this k₂ hk₂ k₁ hk₁ hne.symm heq.symm hk₂' hk₁' (by omega)
  let q : ℕ := k₂ - k₁
  let p : ℤ := ⌊(k₂ : ℝ) * θ⌋ - ⌊(k₁ : ℝ) * θ⌋
  refine ⟨q, by omega, by omega, p, ?_⟩
  have hdiff : (q : ℝ) * θ - (p : ℝ) = Int.fract ((k₂ : ℝ) * θ) - Int.fract ((k₁ : ℝ) * θ) := by
    have hqcast : (q : ℝ) = (k₂ : ℝ) - (k₁ : ℝ) := by
      dsimp only [q]; rw [Nat.cast_sub (le_of_lt hlt)]
    dsimp only [p, Int.fract]
    rw [hqcast]
    push_cast
    ring
  rw [hdiff]
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have h1l : (f k₁ : ℝ) ≤ (Q : ℝ) * Int.fract ((k₁ : ℝ) * θ) :=
    Nat.floor_le (by positivity)
  have h1u : (Q : ℝ) * Int.fract ((k₁ : ℝ) * θ) < (f k₁ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h2l : (f k₂ : ℝ) ≤ (Q : ℝ) * Int.fract ((k₂ : ℝ) * θ) :=
    Nat.floor_le (by positivity)
  have h2u : (Q : ℝ) * Int.fract ((k₂ : ℝ) * θ) < (f k₂ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [heq] at h1l h1u
  have habs : |(Q : ℝ) * (Int.fract ((k₂ : ℝ) * θ) - Int.fract ((k₁ : ℝ) * θ))| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith only [h1l, h1u, h2l, h2u]
  rw [abs_mul, abs_of_pos hQpos] at habs
  exact (le_div_iff₀' hQpos).mpr habs

private lemma norm_cexp_I_sub_one (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
  have hsq : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (t / 2)) ^ 2 := by
    rw [Complex.exp_mul_I, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re,
      Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im,
      Complex.I_im, mul_one, sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.cos_ofReal_im, Complex.mul_im, zero_add, Complex.one_im]
    have htrig : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have h := Real.cos_two_mul (t / 2)
      have h2 : 2 * (t / 2) = t := by ring
      rw [h2] at h
      have hsc := Real.sin_sq_add_cos_sq (t / 2)
      linarith only [h, hsc]
    have hsc2 := Real.sin_sq_add_cos_sq t
    nlinarith only [htrig, hsc2]
  have hsin : |2 * Real.sin (t / 2)| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := Real.abs_sin_le_abs (x := t / 2)
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    linarith only [h]
  have h1 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ = |2 * Real.sin (t / 2)| := by
    have hnn1 : 0 ≤ ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ := norm_nonneg _
    have hnn2 : 0 ≤ |2 * Real.sin (t / 2)| := abs_nonneg _
    have hsq' : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = |2 * Real.sin (t / 2)| ^ 2 := by
      rw [sq_abs]; exact hsq
    nlinarith only [hsq', hnn1, hnn2]
  linarith only [h1, hsin]

set_option maxHeartbeats 800000 in
/-- **Roth (1953) Density Increment Lemma:**
If `A ⊆ Finset.range N` is `3`-AP-free with density `α = A.card / N > 0` and `500000 ≤ α^4 * N`,
then there exist `L ≥ 1` and a `3`-AP-free subset `A' ⊆ Finset.range L` with
`α^2 * √N / 1500 ≤ L` and `(α + α^2 / 32) * L ≤ A'.card`. -/
private lemma roth_density_increment {N : ℕ} {A : Finset ℕ}
    (hA_sub : A ⊆ Finset.range N) (hA_free : ThreeAPFree (A : Set ℕ))
    (hα_pos : 0 < (A.card : ℝ) / (N : ℝ))
    (hbig : (500000 : ℝ) ≤ ((A.card : ℝ) / (N : ℝ)) ^ 4 * (N : ℝ)) :
    ∃ (L : ℕ) (A' : Finset ℕ), 1 ≤ L ∧ A' ⊆ Finset.range L ∧ ThreeAPFree (A' : Set ℕ) ∧
      ((A.card : ℝ) / (N : ℝ)) ^ 2 * Real.sqrt (N : ℝ) / 1500 ≤ (L : ℝ) ∧
      (((A.card : ℝ) / (N : ℝ)) + ((A.card : ℝ) / (N : ℝ)) ^ 2 / 32) * (L : ℝ) ≤ (A'.card : ℝ) := by
  classical
  let α : ℝ := (A.card : ℝ) / (N : ℝ)
  have hN_pos_nat : 1 ≤ N := by
    by_contra h0
    have hN0 : N = 0 := by omega
    subst hN0; simp at hα_pos
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hα_le1 : α ≤ 1 := by
    dsimp only [α]
    rw [div_le_one hN_pos]
    have : A.card ≤ N := by have := Finset.card_le_card hA_sub; simpa using this
    exact_mod_cast this
  have h4 : (4 : ℝ) ≤ α ^ 2 * (N : ℝ) := by
    have hα2 : α ^ 4 ≤ α ^ 2 := by
      have h1 : α ^ 2 ≤ 1 := by nlinarith only [hα_pos, hα_le1]
      nlinarith only [h1, sq_nonneg α]
    have h1 : α ^ 4 * (N : ℝ) ≤ α ^ 2 * (N : ℝ) := mul_le_mul_of_nonneg_right hα2 (le_of_lt hN_pos)
    linarith only [hbig, h1]
  obtain ⟨r, hr_ne, hbias⟩ := roth_fourier_bias hN_pos_nat hA_sub hA_free h4
  let θ : ℝ := (r.val : ℝ) / ((2 * N + 1 : ℕ) : ℝ)
  let f : ℕ → ℝ := fun x => (if x ∈ A then (1 : ℝ) else 0) - α
  have hf_abs : ∀ x, |f x| ≤ 1 := by
    intro x; dsimp only [f]; split_ifs
    · rw [abs_le]; constructor <;> linarith only [hα_pos, hα_le1]
    · rw [abs_le]; constructor <;> linarith only [hα_pos, hα_le1]
  have hf_sum_zero : (∑ x ∈ Finset.range N, f x) = 0 := by
    dsimp only [f]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h1 : (∑ x ∈ Finset.range N, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
      rw [← Finset.sum_filter]
      have hfilt : (Finset.range N).filter (· ∈ A) = A := by
        ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun hx => ⟨hA_sub hx, hx⟩⟩
      simp [hfilt]
    rw [h1]
    dsimp only [α]
    rw [mul_div_cancel₀ _ (ne_of_gt hN_pos), sub_self]
  have hbias_f : α ^ 2 * (N : ℝ) / 12 ≤
      ‖∑ x ∈ Finset.range N, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ := by
    refine le_trans hbias (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    · dsimp only [f, α]; split_ifs <;> simp
    · congr 1; dsimp only [θ]; push_cast; ring
  -- Choose Q = ⌊√N⌋ and L = ⌊α^2 * Q / 700⌋
  let Q : ℕ := Nat.floor (Real.sqrt (N : ℝ))
  have hsqrtN_ge : 707 / α ^ 2 ≤ Real.sqrt (N : ℝ) := by
    have hsq : (707 / α ^ 2) ^ 2 ≤ (N : ℝ) := by
      have h1 : (707 : ℝ) ^ 2 ≤ 500000 := by norm_num
      have h2 : (707 / α ^ 2) ^ 2 = (707 : ℝ) ^ 2 / α ^ 4 := by ring
      rw [h2, div_le_iff₀ (by positivity)]
      linarith only [hbig, h1]
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at this
  have hQ_ge : 706 / α ^ 2 ≤ (Q : ℝ) := by
    have hgt := Nat.sub_one_lt_floor (Real.sqrt (N : ℝ))
    have h1 : (1 : ℝ) ≤ 1 / α ^ 2 := by
      rw [one_le_div (by positivity)]; nlinarith only [hα_pos, hα_le1]
    have hdiff : 707 / α ^ 2 - 1 / α ^ 2 = 706 / α ^ 2 := by ring
    dsimp only [Q]
    linarith only [hsqrtN_ge, hgt, h1, hdiff]
  have hQ_le : (Q : ℝ) ≤ Real.sqrt (N : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hQ_ge1 : 1 ≤ Q := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by
      have : (1 : ℝ) ≤ 706 / α ^ 2 := by
        rw [one_le_div (by positivity)]; nlinarith only [hα_pos, hα_le1]
      linarith only [hQ_ge, this]
    exact_mod_cast h1
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  let L : ℕ := Nat.floor (α ^ 2 * (Q : ℝ) / 700)
  have hL_le : (L : ℝ) ≤ α ^ 2 * (Q : ℝ) / 700 := Nat.floor_le (by positivity)
  have hL_gt : α ^ 2 * (Q : ℝ) / 700 - 1 < (L : ℝ) := Nat.sub_one_lt_floor _
  have hL_ge1_real : ((1 : ℕ) : ℝ) ≤ α ^ 2 * (Q : ℝ) / 700 := by
    have h1 : 706 ≤ α ^ 2 * (Q : ℝ) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < α ^ 2)).mp hQ_ge
      linarith only [this]
    push_cast
    linarith only [h1]
  have hL_ge1 : 1 ≤ L := Nat.le_floor hL_ge1_real
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hL_lb : α ^ 2 * Real.sqrt (N : ℝ) / 1500 ≤ (L : ℝ) := by
    have hQ_half : Real.sqrt (N : ℝ) * (706 / 707) ≤ (Q : ℝ) := by
      have hgt := Nat.sub_one_lt_floor (Real.sqrt (N : ℝ))
      have h707 : (707 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        have h1 : (1 : ℝ) ≤ 1 / α ^ 2 := by
          rw [one_le_div (by positivity)]; nlinarith only [hα_pos, hα_le1]
        have h2 : 707 * 1 ≤ 707 * (1 / α ^ 2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        have h3 : 707 * (1 / α ^ 2) = 707 / α ^ 2 := by ring
        linarith only [hsqrtN_ge, h2, h3]
      linarith only [hgt, h707]
    -- Since α^2 * Q / 700 ≥ 706/700 > 1, we have L ≥ 1; wait: if α^2 * Q / 700 ∈ [1, 2), L = 1 ≥ (1/2) * (α^2 * Q / 700)!
    have hL_half : α ^ 2 * (Q : ℝ) / 1400 ≤ (L : ℝ) := by
      by_cases hlt2 : α ^ 2 * (Q : ℝ) / 700 < 2
      · have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge1
        linarith only [hlt2, hL1]
      · push Not at hlt2
        linarith only [hL_gt, hlt2]
    have hmul : α ^ 2 * (Real.sqrt (N : ℝ) * (706 / 707)) / 1400 ≤ α ^ 2 * (Q : ℝ) / 1400 := by
      have h := mul_le_mul_of_nonneg_left hQ_half (sq_nonneg α)
      linarith only [h]
    have hcoef : α ^ 2 * Real.sqrt (N : ℝ) / 1500 ≤ α ^ 2 * (Real.sqrt (N : ℝ) * (706 / 707)) / 1400 := by
      have hnn : 0 ≤ α ^ 2 * Real.sqrt (N : ℝ) := by positivity
      nlinarith only [hnn]
    linarith only [hcoef, hmul, hL_half]
  -- Apply Dirichlet approximation to θ with bound Q
  obtain ⟨q, hq1, hqQ, p, hp⟩ := dirichlet_approx θ Q hQ_ge1
  have hq_pos : 0 < q := by omega
  -- Partition Finset.range N into disjoint length-L APs P(c, t) for c < q, t < T₀
  let T₀ : ℕ := (N / q) / L
  let idx : Finset (ℕ × ℕ) := (Finset.range q) ×ˢ (Finset.range T₀)
  let elem : (ℕ × ℕ) → ℕ → ℕ := fun ct j => ct.1 + (ct.2 * L + j) * q
  let P : (ℕ × ℕ) → Finset ℕ := fun ct => (Finset.range L).image (elem ct)
  have helem_lt : ∀ ct ∈ idx, ∀ j ∈ Finset.range L, elem ct j < N := by
    rintro ⟨c, t⟩ hct j hj
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hct
    rw [Finset.mem_range] at hj
    dsimp only [elem]
    have h1 : t * L + j < T₀ * L := by
      have ht : t + 1 ≤ T₀ := hct.2
      have hmul : (t + 1) * L ≤ T₀ * L := Nat.mul_le_mul_right L ht
      linarith
    have h2 : T₀ * L ≤ N / q := Nat.div_mul_le_self (N / q) L
    have h3 : (t * L + j + 1) * q ≤ (N / q) * q := Nat.mul_le_mul_right q (by omega)
    have h4 : (N / q) * q ≤ N := Nat.div_mul_le_self N q
    linarith [hct.1]
  have helem_inj : ∀ ct, Function.Injective (elem ct) := by
    rintro ⟨c, t⟩ j₁ j₂ heq
    dsimp only [elem] at heq
    have h1 : (t * L + j₁) * q = (t * L + j₂) * q := by omega
    have h2 : t * L + j₁ = t * L + j₂ := Nat.eq_of_mul_eq_mul_right hq_pos h1
    omega
  have hP_card : ∀ ct, (P ct).card = L := fun ct => by
    dsimp only [P]
    rw [Finset.card_image_of_injective _ (helem_inj ct), Finset.card_range]
  have hP_disj : Set.PairwiseDisjoint (idx : Set (ℕ × ℕ)) P := by
    rintro ⟨c₁, t₁⟩ h₁ ⟨c₂, t₂⟩ h₂ hne
    show Disjoint (P (c₁, t₁)) (P (c₂, t₂))
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range] at h₁ h₂
    rcases Finset.mem_image.mp hx₁ with ⟨j₁, hj₁, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨j₂, hj₂, heq⟩
    rw [Finset.mem_range] at hj₁ hj₂
    dsimp only [elem] at heq
    have hc : c₁ = c₂ := by
      have hmod := congrArg (· % q) heq
      rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt h₁.1, Nat.mod_eq_of_lt h₂.1] at hmod
      exact hmod.symm
    have hmul : t₁ * L + j₁ = t₂ * L + j₂ := by
      have : (t₂ * L + j₂) * q = (t₁ * L + j₁) * q := by omega
      exact (Nat.eq_of_mul_eq_mul_right hq_pos this).symm
    have ht : t₁ = t₂ := by
      have hdiv := congrArg (· / L) hmul
      rw [add_comm (t₁ * L) j₁, add_comm (t₂ * L) j₂,
        Nat.add_mul_div_right _ _ (by omega : 0 < L),
        Nat.add_mul_div_right _ _ (by omega : 0 < L),
        Nat.div_eq_of_lt hj₁, Nat.div_eq_of_lt hj₂, zero_add, zero_add] at hdiv
      exact hdiv
    exact hne (Prod.ext hc ht)
  let U_cov : Finset ℕ := idx.biUnion P
  have hU_sub : U_cov ⊆ Finset.range N := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨ct, hct, hxP⟩
    rcases Finset.mem_image.mp hxP with ⟨j, hj, rfl⟩
    exact Finset.mem_range.mpr (helem_lt ct hct j hj)
  have hU_card : U_cov.card = q * T₀ * L := by
    rw [Finset.card_biUnion hP_disj]
    simp_rw [hP_card, Finset.sum_const, smul_eq_mul]
    have hidx_card : idx.card = q * T₀ := by simp [idx]
    rw [hidx_card]
  let rem : Finset ℕ := (Finset.range N) \ U_cov
  have hrem_card : rem.card ≤ 2 * Q * L := by
    have hcard_eq : rem.card = N - q * T₀ * L := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hU_sub, Finset.card_range, hU_card]
    rw [hcard_eq]
    have h1 : N - q * (N / q) < q := by
      have hdm := Nat.div_add_mod N q
      have hm := Nat.mod_lt N hq_pos
      omega
    have h2 : N / q - T₀ * L < L := by
      have hdm : T₀ * L + (N / q) % L = N / q := by
        dsimp only [T₀]; rw [mul_comm]; exact Nat.div_add_mod (N / q) L
      have hm := Nat.mod_lt (N / q) (by omega : 0 < L)
      omega
    have h3 : q * (N / q) - q * T₀ * L ≤ q * L := by
      have hmul : q * (N / q - T₀ * L) ≤ q * L := Nat.mul_le_mul_left q (le_of_lt h2)
      rw [Nat.mul_sub_left_distrib] at hmul
      simpa [mul_assoc] using hmul
    have h4 : N - q * T₀ * L ≤ q + q * L := by omega
    have h5 : q ≤ q * L := Nat.le_mul_of_pos_right q (by omega)
    have h6 : q * L ≤ Q * L := Nat.mul_le_mul_right L hqQ
    have h7 : 2 * Q * L = Q * L + Q * L := by ring
    omega
  -- Bound Q * L ≤ α^2 * N / 700
  have hQL_le : (Q : ℝ) * (L : ℝ) ≤ α ^ 2 * (N : ℝ) / 700 := by
    have hQ2 : (Q : ℝ) * (Q : ℝ) ≤ (N : ℝ) := by
      calc (Q : ℝ) * (Q : ℝ) ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
            mul_le_mul hQ_le hQ_le (Nat.cast_nonneg Q) (Real.sqrt_nonneg _)
        _ = (N : ℝ) := Real.mul_self_sqrt (le_of_lt hN_pos)
    have h1 := mul_le_mul_of_nonneg_left hL_le (Nat.cast_nonneg Q)
    have h2 : (Q : ℝ) * (α ^ 2 * (Q : ℝ) / 700) = α ^ 2 * ((Q : ℝ) * (Q : ℝ)) / 700 := by ring
    have h3 : α ^ 2 * ((Q : ℝ) * (Q : ℝ)) / 700 ≤ α ^ 2 * (N : ℝ) / 700 := by
      have := mul_le_mul_of_nonneg_left hQ2 (sq_nonneg α)
      linarith only [this]
    linarith only [h1, h2, h3]
  -- Phase stability on each AP P(ct):
  -- ‖∑_{x ∈ P ct} f(x) e(x θ)‖ ≤ |∑_{x ∈ P ct} f(x)| + (2 π L / Q) * L
  have hAP_phase : ∀ ct : ℕ × ℕ,
      ‖∑ x ∈ P ct, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ ≤
        |∑ x ∈ P ct, f x| + (8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ) := by
    intro ct
    let x₀ : ℕ := elem ct 0
    let e₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((x₀ : ℝ) * θ : ℂ))
    have he₀_norm : ‖e₀‖ = 1 := by
      dsimp only [e₀]
      have hrew : (2 * Real.pi * Complex.I * ((x₀ : ℝ) * θ : ℂ)) =
          (((2 * Real.pi * ((x₀ : ℝ) * θ) : ℝ) : ℂ)) * Complex.I := by push_cast; ring
      rw [hrew, Complex.norm_exp_ofReal_mul_I]
    have hsplit :
        (∑ x ∈ P ct, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))) =
          e₀ * (∑ x ∈ P ct, (f x : ℂ)) +
          ∑ x ∈ P ct, (f x : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) - e₀) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hsplit]
    have hmain : ‖e₀ * (∑ x ∈ P ct, (f x : ℂ))‖ = |∑ x ∈ P ct, f x| := by
      rw [norm_mul, he₀_norm, one_mul, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    have herr : ‖∑ x ∈ P ct, (f x : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) - e₀)‖ ≤
        (8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ) := by
      calc
        ‖∑ x ∈ P ct, (f x : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) - e₀)‖
            ≤ ∑ x ∈ P ct, ‖(f x : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) - e₀)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _x ∈ P ct, (8 * (L : ℝ) / (Q : ℝ)) := by
            refine Finset.sum_le_sum fun x hx => ?_
            rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
            have hjL : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_of_lt (Finset.mem_range.mp hj)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have hdiff_exp :
                Complex.exp (2 * Real.pi * Complex.I * (((elem ct j : ℕ) : ℝ) * θ : ℂ)) - e₀ =
                  e₀ * (Complex.exp (((2 * Real.pi * (j : ℝ) * ((q : ℝ) * θ - (p : ℝ)) : ℝ) : ℂ) * Complex.I) - 1) := by
              have hxe : ((elem ct j : ℕ) : ℝ) = (x₀ : ℝ) + (j : ℝ) * (q : ℝ) := by
                dsimp only [x₀, elem]; push_cast; ring
              have harg : 2 * Real.pi * Complex.I * (((elem ct j : ℕ) : ℝ) * θ : ℂ) =
                  2 * Real.pi * Complex.I * ((x₀ : ℝ) * θ : ℂ) +
                  (((2 * Real.pi * (j : ℝ) * ((q : ℝ) * θ - (p : ℝ)) : ℝ) : ℂ) * Complex.I) +
                  ((j : ℤ) * p : ℤ) * (2 * Real.pi * Complex.I) := by
                rw [hxe]; push_cast; ring
              rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
              dsimp only [e₀]; ring
            rw [hdiff_exp, norm_mul, he₀_norm, one_mul]
            have hnorm_le := norm_cexp_I_sub_one (2 * Real.pi * (j : ℝ) * ((q : ℝ) * θ - (p : ℝ)))
            have habs_le : |2 * Real.pi * (j : ℝ) * ((q : ℝ) * θ - (p : ℝ))| ≤ 8 * (L : ℝ) / (Q : ℝ) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
                abs_of_pos Real.pi_pos, abs_of_nonneg (Nat.cast_nonneg j)]
              have hpi4 : Real.pi < 4 := lt_trans Real.pi_lt_d2 (by norm_num)
              have h1 : 2 * Real.pi * (j : ℝ) ≤ 8 * (L : ℝ) := by
                have h2pi : 2 * Real.pi ≤ 8 := by linarith only [hpi4]
                exact mul_le_mul h2pi hjL (Nat.cast_nonneg j) (by norm_num)
              calc
                2 * Real.pi * (j : ℝ) * |(q : ℝ) * θ - (p : ℝ)| ≤ (8 * (L : ℝ)) * (1 / (Q : ℝ)) :=
                  mul_le_mul h1 hp (abs_nonneg _) (by positivity)
                _ = 8 * (L : ℝ) / (Q : ℝ) := by ring
            have hf1 := hf_abs (elem ct j)
            have hn2 : ‖Complex.exp (((2 * Real.pi * (j : ℝ) * ((q : ℝ) * θ - (p : ℝ)) : ℝ) : ℂ) * Complex.I) - 1‖ ≤
                8 * (L : ℝ) / (Q : ℝ) := le_trans hnorm_le habs_le
            calc
              |f (elem ct j)| * ‖Complex.exp (((2 * Real.pi * (j : ℝ) * ((q : ℝ) * θ - (p : ℝ)) : ℝ) : ℂ) * Complex.I) - 1‖
                  ≤ 1 * (8 * (L : ℝ) / (Q : ℝ)) :=
                mul_le_mul hf1 hn2 (norm_nonneg _) (by norm_num)
              _ = 8 * (L : ℝ) / (Q : ℝ) := one_mul _
        _ = (8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ) := by
            rw [Finset.sum_const, hP_card ct, nsmul_eq_mul, mul_comm]
    calc
      ‖e₀ * (∑ x ∈ P ct, (f x : ℂ)) +
          ∑ x ∈ P ct, (f x : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) - e₀)‖
          ≤ ‖e₀ * (∑ x ∈ P ct, (f x : ℂ))‖ +
            ‖∑ x ∈ P ct, (f x : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) - e₀)‖ :=
        norm_add_le _ _
      _ ≤ |∑ x ∈ P ct, f x| + (8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ) := by linarith only [hmain, herr]
  -- Split the total Fourier sum into U_cov = biUnion P and rem
  have hsum_split :
      (∑ x ∈ Finset.range N, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))) =
        (∑ ct ∈ idx, ∑ x ∈ P ct, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))) +
        ∑ x ∈ rem, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) := by
    have hunion : U_cov ∪ rem = Finset.range N := Finset.union_sdiff_of_subset hU_sub
    have hdisj : Disjoint U_cov rem := Finset.disjoint_sdiff
    rw [← hunion, Finset.sum_union hdisj, Finset.sum_biUnion hP_disj]
  have hrem_norm :
      ‖∑ x ∈ rem, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ ≤
        2 * (Q : ℝ) * (L : ℝ) := by
    calc
      ‖∑ x ∈ rem, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖
          ≤ ∑ x ∈ rem, ‖(f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _x ∈ rem, (1 : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ = 1 := by
            have hrew : (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ)) =
                (((2 * Real.pi * ((x : ℝ) * θ) : ℝ) : ℂ)) * Complex.I := by push_cast; ring
            rw [hrew, Complex.norm_exp_ofReal_mul_I]
          rw [he, mul_one]; exact hf_abs x
      _ = (rem.card : ℝ) := by simp
      _ ≤ 2 * (Q : ℝ) * (L : ℝ) := by exact_mod_cast hrem_card
  have hsum_abs_ge : α ^ 2 * (N : ℝ) / 15 ≤ ∑ ct ∈ idx, |∑ x ∈ P ct, f x| := by
    have h1 : α ^ 2 * (N : ℝ) / 12 ≤
        (∑ ct ∈ idx, (|∑ x ∈ P ct, f x| + (8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ))) + 2 * (Q : ℝ) * (L : ℝ) := by
      calc
        α ^ 2 * (N : ℝ) / 12 ≤ ‖∑ x ∈ Finset.range N, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ := hbias_f
        _ ≤ ‖∑ ct ∈ idx, ∑ x ∈ P ct, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ +
            ‖∑ x ∈ rem, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖ := by
          rw [hsum_split]; exact norm_add_le _ _
        _ ≤ (∑ ct ∈ idx, ‖∑ x ∈ P ct, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))‖) +
            2 * (Q : ℝ) * (L : ℝ) := by
          linarith only [norm_sum_le idx (fun ct => ∑ x ∈ P ct, (f x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * θ : ℂ))), hrem_norm]
        _ ≤ (∑ ct ∈ idx, (|∑ x ∈ P ct, f x| + (8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ))) + 2 * (Q : ℝ) * (L : ℝ) := by
          have hsum_le := Finset.sum_le_sum fun ct (_ : ct ∈ idx) => hAP_phase ct
          linarith only [hsum_le]
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
    have hidxL_le_N : (idx.card : ℝ) * (L : ℝ) ≤ (N : ℝ) := by
      have hnat : idx.card * L ≤ N := by
        have h1 : idx.card * L = U_cov.card := by
          rw [hU_card]
          dsimp only [idx]
          rw [Finset.card_product, Finset.card_range, Finset.card_range]
        rw [h1]
        have := Finset.card_le_card hU_sub
        rwa [Finset.card_range] at this
      exact_mod_cast hnat
    have hphase_tot : (idx.card : ℝ) * ((8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ)) ≤ 8 * α ^ 2 * (N : ℝ) / 700 := by
      have hLQ : 8 * (L : ℝ) / (Q : ℝ) ≤ 8 * α ^ 2 / 700 := by
        rw [div_le_iff₀ hQ_pos]
        linarith only [hL_le]
      calc
        (idx.card : ℝ) * ((8 * (L : ℝ) / (Q : ℝ)) * (L : ℝ)) =
            (8 * (L : ℝ) / (Q : ℝ)) * ((idx.card : ℝ) * (L : ℝ)) := by ring
        _ ≤ (8 * α ^ 2 / 700) * (N : ℝ) :=
            mul_le_mul hLQ hidxL_le_N (by positivity) (by positivity)
        _ = 8 * α ^ 2 * (N : ℝ) / 700 := by ring
    have hrem_tot : 2 * (Q : ℝ) * (L : ℝ) ≤ 2 * α ^ 2 * (N : ℝ) / 700 := by linarith only [hQL_le]
    have hα2N_nn : 0 ≤ α ^ 2 * (N : ℝ) := by positivity
    linarith only [h1, hphase_tot, hrem_tot, hα2N_nn]
  -- Zero-sum trick: ∑_{ct ∈ idx} (∑_{x ∈ P ct} f x) = - ∑_{x ∈ rem} f x ≥ - 2 Q L
  have hsum_raw_ge : -(2 * α ^ 2 * (N : ℝ) / 700) ≤ ∑ ct ∈ idx, ∑ x ∈ P ct, f x := by
    have htot : (∑ ct ∈ idx, ∑ x ∈ P ct, f x) + (∑ x ∈ rem, f x) = 0 := by
      have hunion : U_cov ∪ rem = Finset.range N := Finset.union_sdiff_of_subset hU_sub
      have hdisj : Disjoint U_cov rem := Finset.disjoint_sdiff
      rw [← Finset.sum_biUnion hP_disj, ← Finset.sum_union hdisj, hunion]
      exact hf_sum_zero
    have hrem_ub : ∑ x ∈ rem, f x ≤ 2 * (Q : ℝ) * (L : ℝ) := by
      calc
        ∑ x ∈ rem, f x ≤ ∑ x ∈ rem, |f x| := Finset.sum_le_sum fun x _ => le_abs_self _
        _ ≤ ∑ _x ∈ rem, (1 : ℝ) := Finset.sum_le_sum fun x _ => hf_abs x
        _ = (rem.card : ℝ) := by simp
        _ ≤ 2 * (Q : ℝ) * (L : ℝ) := by exact_mod_cast hrem_card
    linarith only [htot, hrem_ub, hQL_le]
  -- Add |S| + S = 2 max(S, 0): at least one ct ∈ idx has ∑_{x ∈ P ct} f x ≥ α^2 * L / 32!
  have hα2_pos : 0 < α ^ 2 := sq_pos_of_pos hα_pos
  have hpos_sum : α ^ 2 * (N : ℝ) / 16 ≤ ∑ ct ∈ idx, (|∑ x ∈ P ct, f x| + ∑ x ∈ P ct, f x) := by
    rw [Finset.sum_add_distrib]
    have hα2N_nn : 0 ≤ α ^ 2 * (N : ℝ) := mul_nonneg (le_of_lt hα2_pos) (le_of_lt hN_pos)
    linarith only [hsum_abs_ge, hsum_raw_ge, hα2N_nn]
  have hidx_ne : idx.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty.mp hemp, Finset.sum_empty] at hpos_sum
    have hpos : 0 < α ^ 2 * (N : ℝ) / 16 := div_pos (mul_pos hα2_pos hN_pos) (by norm_num)
    linarith only [hpos_sum, hpos]
  have hex_ct : ∃ ct ∈ idx, α ^ 2 * (L : ℝ) / 32 ≤ ∑ x ∈ P ct, f x := by
    by_contra hall
    push Not at hall
    have hlt : ∑ ct ∈ idx, (|∑ x ∈ P ct, f x| + ∑ x ∈ P ct, f x) <
        ∑ _ct ∈ idx, (α ^ 2 * (L : ℝ) / 16) := by
      refine Finset.sum_lt_sum_of_nonempty hidx_ne fun ct hct => ?_
      have hct_lt := hall ct hct
      by_cases hneg : ∑ x ∈ P ct, f x ≤ 0
      · rw [abs_of_nonpos hneg, neg_add_cancel]
        exact div_pos (mul_pos hα2_pos hL_pos) (by norm_num)
      · push Not at hneg
        rw [abs_of_pos hneg]; linarith only [hct_lt]
    rw [Finset.sum_const, nsmul_eq_mul] at hlt
    have hidxL_le_N : (idx.card : ℝ) * (L : ℝ) ≤ (N : ℝ) := by
      have hnat : idx.card * L ≤ N := by
        have h1 : idx.card * L = U_cov.card := by
          rw [hU_card]
          dsimp only [idx]
          rw [Finset.card_product, Finset.card_range, Finset.card_range]
        rw [h1]
        have := Finset.card_le_card hU_sub
        rwa [Finset.card_range] at this
      exact_mod_cast hnat
    have hmul : (idx.card : ℝ) * (α ^ 2 * (L : ℝ) / 16) ≤ α ^ 2 * (N : ℝ) / 16 := by
      have hrew : (idx.card : ℝ) * (α ^ 2 * (L : ℝ) / 16) = (α ^ 2 / 16) * ((idx.card : ℝ) * (L : ℝ)) := by ring
      rw [hrew]
      have h := mul_le_mul_of_nonneg_left hidxL_le_N (div_nonneg (le_of_lt hα2_pos) (by norm_num : (0 : ℝ) ≤ 16))
      linarith only [h]
    linarith only [hpos_sum, hlt, hmul]
  rcases hex_ct with ⟨ct, hct, hct_ge⟩
  -- Pull back A ∩ P ct along elem ct to Finset.range L
  let A' : Finset ℕ := (Finset.range L).filter (fun j => elem ct j ∈ A)
  refine ⟨L, A', hL_ge1, Finset.filter_subset _ _, ?_, hL_lb, ?_⟩
  · -- ThreeAPFree A'
    intro j₁ hj₁ j₂ hj₂ j₃ hj₃ heq
    have hm₁ : elem ct j₁ ∈ (A : Set ℕ) := (Finset.mem_filter.mp hj₁).2
    have hm₂ : elem ct j₂ ∈ (A : Set ℕ) := (Finset.mem_filter.mp hj₂).2
    have hm₃ : elem ct j₃ ∈ (A : Set ℕ) := (Finset.mem_filter.mp hj₃).2
    have h3ap : elem ct j₁ + elem ct j₃ = elem ct j₂ + elem ct j₂ := by
      dsimp only [elem]
      calc
        ct.1 + (ct.2 * L + j₁) * q + (ct.1 + (ct.2 * L + j₃) * q)
            = 2 * ct.1 + (2 * (ct.2 * L) + (j₁ + j₃)) * q := by ring
        _ = 2 * ct.1 + (2 * (ct.2 * L) + (j₂ + j₂)) * q := by rw [heq]
        _ = ct.1 + (ct.2 * L + j₂) * q + (ct.1 + (ct.2 * L + j₂) * q) := by ring
    exact helem_inj ct (hA_free hm₁ hm₂ hm₃ h3ap)
  · -- Cardinality lower bound: (α + α^2 / 32) * L ≤ A'.card
    have hsum_f : (∑ x ∈ P ct, f x) = (A'.card : ℝ) - α * (L : ℝ) := by
      dsimp only [P]
      rw [Finset.sum_image (fun j₁ _ j₂ _ h => helem_inj ct h)]
      dsimp only [f]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (L : ℝ) α]
      congr 1
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith only [hct_ge, hsum_f]

private lemma roth_iter (α₀ : ℝ) (hα₀_pos : 0 < α₀) (hα₀_le1 : α₀ ≤ 1) :
    ∀ k : ℕ, ∀ (N : ℕ) (A : Finset ℕ), 1 ≤ N → A ⊆ Finset.range N → ThreeAPFree (A : Set ℕ) →
      α₀ ≤ (A.card : ℝ) / (N : ℝ) →
      33 / ((A.card : ℝ) / (N : ℝ)) < (k : ℝ) + 1 →
      Real.log (N : ℝ) + 2 * Real.log (1500 / α₀ ^ 2) <
        (2 : ℝ) ^ k * (Real.log (500000 / α₀ ^ 4) + 2 * Real.log (1500 / α₀ ^ 2))
  | 0, N, A, hN, hA_sub, _, hα_ge, hk_lt => by
      exfalso
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have hα_pos : 0 < (A.card : ℝ) / (N : ℝ) := lt_of_lt_of_le hα₀_pos hα_ge
      have hα_le1 : (A.card : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hNpos]
        have : A.card ≤ N := by have := Finset.card_le_card hA_sub; simpa using this
        exact_mod_cast this
      have h33 : 33 ≤ 33 / ((A.card : ℝ) / (N : ℝ)) := by
        rw [le_div_iff₀ hα_pos]; linarith only [hα_le1]
      norm_num at hk_lt
      linarith only [h33, hk_lt]
  | k + 1, N, A, hN, hA_sub, hA_free, hα_ge, hk_lt => by
      by_contra hge
      push Not at hge
      let B₀ : ℝ := Real.log (1500 / α₀ ^ 2)
      let M₀ : ℝ := Real.log (500000 / α₀ ^ 4) + 2 * B₀
      have hB₀_nn : 0 ≤ B₀ := by
        apply Real.log_nonneg
        rw [one_le_div (by positivity)]
        have : α₀ ^ 2 ≤ 1 := by nlinarith only [hα₀_pos, hα₀_le1]
        linarith only [this]
      have hlog500_nn : 0 ≤ Real.log (500000 / α₀ ^ 4) := by
        apply Real.log_nonneg
        rw [one_le_div (by positivity)]
        have h1 : α₀ ^ 2 ≤ 1 := by nlinarith only [hα₀_pos, hα₀_le1]
        have h2 : α₀ ^ 4 ≤ 1 := by nlinarith only [h1, sq_nonneg α₀]
        linarith only [h2]
      have h2k_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast Nat.one_le_two_pow
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      let α : ℝ := (A.card : ℝ) / (N : ℝ)
      have hα_pos : 0 < α := lt_of_lt_of_le hα₀_pos hα_ge
      have hα_le1 : α ≤ 1 := by
        dsimp only [α]
        rw [div_le_one hN_pos]
        have : A.card ≤ N := by have := Finset.card_le_card hA_sub; simpa using this
        exact_mod_cast this
      -- From hge, deduce 500000 ≤ α^4 * N
      have hbig : (500000 : ℝ) ≤ α ^ 4 * (N : ℝ) := by
        have hlogN_ge : Real.log (500000 / α₀ ^ 4) ≤ Real.log (N : ℝ) := by
          have h2pow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
          have hM₀_ge : Real.log (500000 / α₀ ^ 4) + 2 * B₀ ≤ (2 : ℝ) ^ k * M₀ := by
            have : 0 ≤ M₀ := by dsimp only [M₀]; linarith only [hlog500_nn, hB₀_nn]
            nlinarith only [h2k_ge1, this]
          dsimp only [M₀, B₀] at hge hM₀_ge ⊢
          nlinarith only [hge, h2pow, hM₀_ge, hB₀_nn, hlog500_nn]
        have hN_ge : 500000 / α₀ ^ 4 ≤ (N : ℝ) := by
          have h1 := Real.exp_le_exp.mpr hlogN_ge
          rwa [Real.exp_log (by positivity), Real.exp_log hN_pos] at h1
        have h1 : 500000 ≤ α₀ ^ 4 * (N : ℝ) := (div_le_iff₀' (by positivity)).mp hN_ge
        have hα4 : α₀ ^ 4 ≤ α ^ 4 := pow_le_pow_left₀ (le_of_lt hα₀_pos) hα_ge 4
        have h2 := mul_le_mul_of_nonneg_right hα4 (le_of_lt hN_pos)
        linarith only [h1, h2]
      obtain ⟨L, A', hL1, hA'_sub, hA'_free, hL_lb, hA'_card⟩ :=
        roth_density_increment hA_sub hA_free hα_pos hbig
      have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
      let α' : ℝ := (A'.card : ℝ) / (L : ℝ)
      have hα'_ge_step : α + α ^ 2 / 32 ≤ α' := (le_div_iff₀ hL_pos).mpr hA'_card
      have hα'_ge_α₀ : α₀ ≤ α' := by
        have : 0 ≤ α ^ 2 / 32 := by positivity
        linarith only [hα_ge, hα'_ge_step, this]
      have hα'_pos : 0 < α' := lt_of_lt_of_le hα₀_pos hα'_ge_α₀
      -- Potential drop: 33 / α' ≤ 33 / α - 1 < k + 1
      have hdrop : 33 / α' ≤ 33 / α - 1 := by
        have h1 : 33 / α' ≤ 33 / (α + α ^ 2 / 32) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hα'_ge_step
        have h2 : 33 / (α + α ^ 2 / 32) ≤ 33 / α - 1 := by
          have hden1 : 0 < α + α ^ 2 / 32 := by positivity
          have hdiff : 33 / α - 33 / (α + α ^ 2 / 32) = (33 / 32) / (1 + α / 32) := by
            field_simp [ne_of_gt hα_pos, ne_of_gt hden1]; ring
          have hge1 : 1 ≤ (33 / 32 : ℝ) / (1 + α / 32) := by
            rw [one_le_div (by positivity)]; linarith only [hα_le1]
          linarith only [hdiff, hge1]
        linarith only [h1, h2]
      have hk'_lt : 33 / α' < (k : ℝ) + 1 := by
        change 33 / α < ((k + 1 : ℕ) : ℝ) + 1 at hk_lt
        push_cast at hk_lt
        linarith only [hdrop, hk_lt]
      have hIH := roth_iter α₀ hα₀_pos hα₀_le1 k L A' hL1 hA'_sub hA'_free hα'_ge_α₀ hk'_lt
      -- On the other hand, log L + 2 B₀ ≥ (log N + 2 B₀) / 2 ≥ 2^k * M₀
      have hL_ge_α₀ : α₀ ^ 2 * Real.sqrt (N : ℝ) / 1500 ≤ (L : ℝ) := by
        have hα2 : α₀ ^ 2 ≤ α ^ 2 := pow_le_pow_left₀ (le_of_lt hα₀_pos) hα_ge 2
        have h1 := mul_le_mul_of_nonneg_right hα2 (Real.sqrt_nonneg (N : ℝ))
        linarith only [hL_lb, h1]
      have hlogL_ge : Real.log (N : ℝ) / 2 - B₀ ≤ Real.log (L : ℝ) := by
        have hpos_lhs : 0 < α₀ ^ 2 * Real.sqrt (N : ℝ) / 1500 := by positivity
        have h1 := Real.log_le_log hpos_lhs hL_ge_α₀
        have hrew : α₀ ^ 2 * Real.sqrt (N : ℝ) / 1500 = Real.sqrt (N : ℝ) / (1500 / α₀ ^ 2) := by
          field_simp [ne_of_gt hα₀_pos]
        rw [hrew, Real.log_div (ne_of_gt (Real.sqrt_pos.mpr hN_pos)) (by positivity),
          Real.log_sqrt (le_of_lt hN_pos)] at h1
        dsimp only [B₀]
        linarith only [h1]
      have h2pow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
      rw [h2pow] at hge
      dsimp only [B₀, M₀] at hge hlogL_ge
      linarith only [hge, hlogL_ge, hIH]

/-- **Roth (1953) Quantitative Fourier Density-Increment Upper Bound (`r_3(N) ≤ 100 * N / log log N`):**
Proved from scratch via self-contained discrete Fourier analysis over `ZMod (2 * N + 1)`,
Dirichlet pigeonhole AP-partitioning, and density-increment iteration (vastly improving
Mathlib's tower-type `roth_3ap_theorem`). -/
theorem roth_quantitative_upper_bound :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} : ℕ) : ℝ) ≤
        100 * (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  -- Choose N₀ so that log(log N) ≥ 10000 and log N ≥ exp(10000)
  let N₀ : ℕ := Nat.ceil (Real.exp (Real.exp 10000)) + 10
  refine ⟨N₀, fun N hN => ?_⟩
  change (rK 3 N : ℝ) ≤ 100 * (N : ℝ) / Real.log (Real.log (N : ℝ))
  obtain ⟨A₁, hA₁_sub, hA₁_free, hA₁_card⟩ := exists_witness_rK (k := 3) (by omega) N
  rw [← hA₁_card]
  have hN_ge_exp : Real.exp (Real.exp 10000) ≤ (N : ℝ) := by
    have h1 : Real.exp (Real.exp 10000) ≤ (Nat.ceil (Real.exp (Real.exp 10000)) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp (Real.exp 10000)) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp 10000)) ≤ N)
    linarith only [h1, h2]
  have hN_pos_nat : 1 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set L : ℝ := Real.log (N : ℝ)
  have hL_ge : Real.exp 10000 ≤ L := by
    have := Real.log_le_log (Real.exp_pos _) hN_ge_exp
    rwa [Real.log_exp] at this
  have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL_ge
  set LL : ℝ := Real.log L
  have hLL_ge : 10000 ≤ LL := by
    have := Real.log_le_log (Real.exp_pos 10000) hL_ge
    rwa [Real.log_exp] at this
  have hLL_pos : 0 < LL := by linarith only [hLL_ge]
  -- Transfer A₁ ⊆ Icc 1 N to B ⊆ range N
  let B : Finset ℕ := A₁.image (· - 1)
  have hB_card : B.card = A₁.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    dsimp only at hxy
    have hx1 := (Finset.mem_Icc.mp (hA₁_sub hx)).1
    have hy1 := (Finset.mem_Icc.mp (hA₁_sub hy)).1
    omega
  have hB_sub : B ⊆ Finset.range N := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hxI := Finset.mem_Icc.mp (hA₁_sub hx)
    rw [Finset.mem_range]; omega
  have hB_free : ThreeAPFree (B : Set ℕ) := by
    rw [← isKApFree_three_iff_threeAPFree]
    have himg : B.image (· + 1) = A₁ := by
      ext x; simp only [B, Finset.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have hz1 := (Finset.mem_Icc.mp (hA₁_sub hz)).1
        have : z - 1 + 1 = z := by omega
        rwa [this]
      · intro hx
        have hx1 := (Finset.mem_Icc.mp (hA₁_sub hx)).1
        exact ⟨x - 1, ⟨x, hx, rfl⟩, by omega⟩
    exact isKApFree_of_image_add_left (c := 1) (himg.symm ▸ hA₁_free)
  -- Proof by contradiction: suppose A₁.card > 100 * N / LL
  by_contra hgt
  push Not at hgt
  let α : ℝ := (B.card : ℝ) / (N : ℝ)
  have hα_gt : 100 / LL < α := by
    dsimp only [α]
    rw [hB_card, div_lt_div_iff₀ hLL_pos hN_pos]
    have hmul := (div_lt_iff₀ hLL_pos).mp hgt
    linarith only [hmul]
  have hα_pos : 0 < α := lt_trans (by positivity) hα_gt
  have hα_le1 : α ≤ 1 := by
    dsimp only [α]; rw [div_le_one hN_pos]
    have : B.card ≤ N := by have := Finset.card_le_card hB_sub; simpa using this
    exact_mod_cast this
  let k : ℕ := Nat.floor (33 / α)
  have hk_lt : 33 / α < (k : ℝ) + 1 := Nat.lt_floor_add_one (33 / α)
  have hk_le : (k : ℝ) ≤ 33 / α := Nat.floor_le (by positivity)
  have hiter := roth_iter α hα_pos hα_le1 k N B hN_pos_nat hB_sub hB_free le_rfl hk_lt
  -- Now upper bound the RHS of hiter by L, contradicting hiter!
  have hB₀_nn : 0 ≤ Real.log (1500 / α ^ 2) := by
    apply Real.log_nonneg
    rw [one_le_div (by positivity)]
    have : α ^ 2 ≤ 1 := by nlinarith only [hα_pos, hα_le1]
    linarith only [this]
  have h2k_le : (2 : ℝ) ^ k ≤ L ^ ((1 : ℝ) / 3) := by
    have hk_bound : (k : ℝ) ≤ 33 / 100 * LL := by
      have h1 : 33 / α ≤ 33 / (100 / LL) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (le_of_lt hα_gt)
      have h2 : 33 / (100 / LL) = 33 / 100 * LL := by
        field_simp [ne_of_gt hLL_pos]
      linarith only [hk_le, h1, h2]
    have hlog2_lt : Real.log 2 < 1 := by
      have : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      calc Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) this
        _ = 1 := Real.log_exp 1
    have h2k_eq : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hL13_eq : L ^ ((1 : ℝ) / 3) = Real.exp (((1 : ℝ) / 3) * LL) := by
      rw [Real.rpow_def_of_pos hL_pos]; dsimp only [LL]; congr 1; ring
    rw [h2k_eq, hL13_eq]
    apply Real.exp_le_exp.mpr
    have h1 : (k : ℝ) * Real.log 2 ≤ (33 / 100 * LL) * 1 :=
      mul_le_mul hk_bound (le_of_lt hlog2_lt) (le_of_lt (Real.log_pos (by norm_num))) (by positivity)
    linarith only [h1, hLL_pos]
  have hM_le : Real.log (500000 / α ^ 4) + 2 * Real.log (1500 / α ^ 2) ≤ L ^ ((1 : ℝ) / 3) := by
    have hsum_log : Real.log (500000 / α ^ 4) + 2 * Real.log (1500 / α ^ 2) ≤ 30 + 8 * LL := by
      have h1 : Real.log (500000 / α ^ 4) = Real.log 500000 - 4 * Real.log α := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]; ring
      have h2 : Real.log (1500 / α ^ 2) = Real.log 1500 - 2 * Real.log α := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]; ring
      have hlog_α : -Real.log α ≤ LL := by
        have h100 : (1 / LL) ≤ α := by
          have : 1 / LL ≤ 100 / LL := div_le_div_of_nonneg_right (by norm_num) (le_of_lt hLL_pos)
          linarith only [this, hα_gt]
        have hlog1 := Real.log_le_log (by positivity) h100
        rw [Real.log_div (by norm_num) (ne_of_gt hLL_pos), Real.log_one, zero_sub] at hlog1
        have hlogLL : Real.log LL ≤ LL := by linarith only [Real.log_le_sub_one_of_pos hLL_pos]
        linarith only [hlog1, hlogLL]
      have hlog500 : Real.log 500000 ≤ 14 := by
        have hlt : (500000 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
        have h1 := Real.log_le_log (by norm_num) hlt
        rw [Real.log_pow] at h1
        have hlog2 := Real.log_two_lt_d9
        push_cast at h1; linarith only [h1, hlog2]
      have hlog1500 : Real.log 1500 ≤ 8 := by
        have hlt : (1500 : ℝ) ≤ (2 : ℝ) ^ 11 := by norm_num
        have h1 := Real.log_le_log (by norm_num) hlt
        rw [Real.log_pow] at h1
        have hlog2 := Real.log_two_lt_d9
        push_cast at h1; linarith only [h1, hlog2]
      linarith only [h1, h2, hlog_α, hlog500, hlog1500]
    have hLL_le_L13 : 30 + 8 * LL ≤ L ^ ((1 : ℝ) / 3) := by
      have hL13_eq : L ^ ((1 : ℝ) / 3) = Real.exp (LL / 3) := by
        rw [Real.rpow_def_of_pos hL_pos]; dsimp only [LL]; congr 1; ring
      rw [hL13_eq]
      have hexp := exp_ge_cube_div_27 (show 0 ≤ LL / 3 by positivity)
      have h1 : 30 + 8 * LL ≤ (LL / 3) ^ 3 / 27 := by
        have hsq : 10000 * LL ≤ LL ^ 2 := by nlinarith only [hLL_ge]
        have hcu : 10000 * LL ^ 2 ≤ LL ^ 3 := by nlinarith only [hLL_ge, hsq]
        have hexpand : (LL / 3) ^ 3 / 27 = LL ^ 3 / 729 := by ring
        linarith only [hLL_ge, hsq, hcu, hexpand]
      linarith only [h1, hexp]
    linarith only [hsum_log, hLL_le_L13]
  have hrhs_le_L :
      (2 : ℝ) ^ k * (Real.log (500000 / α ^ 4) + 2 * Real.log (1500 / α ^ 2)) ≤ L := by
    have hM_nn : 0 ≤ Real.log (500000 / α ^ 4) + 2 * Real.log (1500 / α ^ 2) := by
      have h1 : 0 ≤ Real.log (500000 / α ^ 4) := by
        apply Real.log_nonneg; rw [one_le_div (by positivity)]
        have h2 : α ^ 2 ≤ 1 := by nlinarith only [hα_pos, hα_le1]
        have h4 : α ^ 4 ≤ 1 := by nlinarith only [h2, sq_nonneg α]
        linarith only [h4]
      linarith only [h1, hB₀_nn]
    calc
      (2 : ℝ) ^ k * (Real.log (500000 / α ^ 4) + 2 * Real.log (1500 / α ^ 2))
          ≤ L ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3) :=
        mul_le_mul h2k_le hM_le hM_nn (by positivity)
      _ = L ^ ((2 : ℝ) / 3) := by
          rw [← Real.rpow_add hL_pos]; norm_num
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hL_ge, Real.add_one_le_exp (10000 : ℝ)]) (by norm_num)
      _ = L := Real.rpow_one L
  linarith only [hiter, hB₀_nn, hrhs_le_L]

/-- **Fekete Limit at `k = 3` Equals Zero (Roth's Theorem):**
`r_3(N) / N → 0` as `N → ∞`, proved directly from our quantitative `O(N / log log N)` bound. -/
theorem rK_three_density_tendsto_zero :
    Filter.Tendsto
      (fun N : ℕ =>
        ((sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} : ℕ) : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := by
  obtain ⟨N₀, hN₀⟩ := roth_quantitative_upper_bound
  rw [Metric.tendsto_atTop]
  intro ε hε
  let M : ℕ := max (max N₀ 10) (Nat.ceil (Real.exp (Real.exp (200 / ε))) + 10)
  refine ⟨M, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hN_ge_N₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 10 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    exact_mod_cast (by omega : 0 < N)
  have hN_ge_exp : Real.exp (Real.exp (200 / ε)) ≤ (N : ℝ) := by
    have h1 : Real.exp (Real.exp (200 / ε)) ≤ (Nat.ceil (Real.exp (Real.exp (200 / ε))) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (Real.exp (Real.exp (200 / ε))) + 10 ≤ N := le_trans (le_max_right _ _) hN
    have h3 : (Nat.ceil (Real.exp (Real.exp (200 / ε))) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : Nat.ceil (Real.exp (Real.exp (200 / ε))) ≤ N)
    linarith only [h1, h3]
  have hLL_ge : 200 / ε ≤ Real.log (Real.log (N : ℝ)) := by
    have hL : Real.exp (200 / ε) ≤ Real.log (N : ℝ) := by
      have := Real.log_le_log (Real.exp_pos _) hN_ge_exp
      rwa [Real.log_exp] at this
    have := Real.log_le_log (Real.exp_pos _) hL
    rwa [Real.log_exp] at this
  have hLL_pos : 0 < Real.log (Real.log (N : ℝ)) := lt_of_lt_of_le (by positivity) hLL_ge
  have hbd : (rK 3 N : ℝ) ≤ 100 * (N : ℝ) / Real.log (Real.log (N : ℝ)) := hN₀ N hN_ge_N₀
  have hdiv : ((rK 3 N : ℕ) : ℝ) / (N : ℝ) ≤ 100 / Real.log (Real.log (N : ℝ)) := by
    rw [div_le_iff₀ hN_pos]
    have : 100 / Real.log (Real.log (N : ℝ)) * (N : ℝ) = 100 * (N : ℝ) / Real.log (Real.log (N : ℝ)) := by ring
    linarith only [hbd, this]
  have hlt : 100 / Real.log (Real.log (N : ℝ)) < ε := by
    rw [div_lt_iff₀ hLL_pos]
    have h200 : 200 ≤ Real.log (Real.log (N : ℝ)) * ε := (div_le_iff₀ hε).mp hLL_ge
    linarith only [h200]
  exact lt_of_le_of_lt hdiv hlt

end RothFourier

end PPL123
