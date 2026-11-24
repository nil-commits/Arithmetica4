/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic
import RHDirect.Stage8ExplicitPrimeBounds

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 088 (Erdős #30 · Sidon `B_2` Sets) & PPL 009 (Erdős #241 · `B_3` Sets)

## Honest Scope & Open Status
**BOTH Erdős Problem #30 (PPL 088, $1,000) and Erdős Problem #241 (PPL 009, $100) REMAIN OPEN.**
This file does **not** claim to settle either open prize conjecture (`h(N) = N^{1/2} + O_ε(N^ε)` or
`f(N) ~ N^{1/3}`). Instead, it formalizes a comprehensive, 100% pure-Mathlib milestone (`0` `sorry`,
`0` custom definitions in any public theorem signature, importing only Mathlib + Tier A verified
`RHDirect.Stage8ExplicitPrimeBounds`):

1. **`ppl088_sidon_cilleruelo_upper_bound`** (Cilleruelo 2010 / Erdős–Turán 1941 / Lindström 1969):
   For every `N ≥ 1` and every Sidon set `A ⊆ Icc 1 N`,
   `(A.card : ℝ) < Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 / 2`.
   Corollary **`ppl088_sidon_lindstrom_upper_bound`**: `(A.card : ℝ) ≤ √N + N^{1/4} + 1` for all `N`.
2. **`ppl088_bose_chowla_Br_prime_lower_bound`** (Unified Bose–Chowla 1962 / Bose 1942):
   For every prime `p` and every `r ≥ 2`, via discrete logarithms in `(GaloisField p r)ˣ`,
   there exists a `B_r` set `A ⊆ Icc 1 (p^r - 1)` of cardinality `p`.
3. **`ppl088_sidon_asymptotic_lower_bound`** & **`ppl088_sidon_asymptotic_equiv`**:
   For every `ε > 0`, eventually `∃ A ⊆ Icc 1 N` Sidon with `(1 - ε) √N ≤ A.card`, and the full
   asymptotic equivalence `h(N) ~[atTop] √N`.
4. **`ppl088_b3_asymptotic_lower_bound`** (Bose–Chowla 1962 for `B_3`, and general `B_r`):
   For every `ε > 0`, eventually `∃ A ⊆ Icc 1 N` a `B_3` set with `(1 - ε) N^{1/3} ≤ A.card`.
5. **`ppl088_b3_difference_upper_bound`** (Elementary `A + A - A` bound):
   For every `N ≥ 1` and every `B_3` set `A ⊆ Icc 1 N`, `A.card * (A.card - 1) * (A.card - 2) ≤ 6 * N - 4`.
6. **`ppl088_b3_discrete_autoconvolution_orthogonal_cosine_lb`** (Exact discrete orthogonal-cosine
   `L²` autoconvolution lower bound, zero integrals):
   For any `L ≥ 1`, `2 * M ≤ L`, and `f : ℕ → ℝ` with `∑ n ∈ range L, f n = 1`,
   `(∑ d ∈ Icc (-(L-1)) (L-1), (f * f~)(d)^2) * ((2*L - 1) - (1/L) ∑_{j<M} cot²((4j+3)π/(4L))) ≥ 1`.
7. **`ppl088_b3_upper_bound_beats_green`** & **`ppl088_b3_green_upper_bound`**:
   Strictly beats Ben Green's (2001) `(7/2)^{1/3} N^{1/3}` headline constant on `erdosproblems.com/241`
   using `M = 20` orthogonal half-integer cosines:
   for every `ε > 0`, eventually every `B_3` set `A ⊆ Icc 1 N` satisfies
   `(A.card : ℝ) ≤ ((699 / 200 : ℝ) ^ ((1 : ℝ) / 3) + ε) * (N : ℝ) ^ ((1 : ℝ) / 3)`
   (note `699 / 200 = 3.495 < 3.5 = 7 / 2`), with Green's `(7/2)^{1/3}` as a direct corollary.
8. **`ppl088_sidon_delsarte_fejer_trapezoid_barrier`** (Exact Fourier-LP barrier for Erdős #30):
   Certifies that the explicit positive-definite Fejér trapezoid `D(0) = k`,
   `D(d) = min(1, (N - d) / (N - M))` satisfies `0 ≤ D(d) ≤ 1`, `D̂(θ) ≥ 0` for all `θ ∈ ℝ`,
   and achieves `k + 2 ∑ D(d) = (k - 1) + N + M` whenever `M² / (N - M) ≤ k - 1`.
9. **`ppl088_b3_weighted_macroscopic_barrier`** (Exact macroscopic barrier for Erdős #241):
   Certifies that no nonnegative weighting `(w, v)` of the `A + A - A` multiplicity bound can exceed
   the `μ₂²` autoconvolution constant.
-/

namespace PPL088

open Filter Finset
open scoped BigOperators Asymptotics

/-! ### Section 1: Cilleruelo's Sharp All-`N` Sidon `B_2` Upper Bound -/

private lemma sum_Icc_sub_eq (M : ℕ) :
    2 * ∑ d ∈ Finset.Icc 1 (M - 1), (M - d) = M * (M - 1) := by
  cases M with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel]
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
      have hshift : ∑ d ∈ Finset.Icc 1 k, (k + 1 + 1 - d) =
          (∑ d ∈ Finset.Icc 1 k, (k + 1 - d)) + k := by
        have h1 : ∀ d ∈ Finset.Icc 1 k, k + 1 + 1 - d = (k + 1 - d) + 1 := by
          intro d hd
          rw [Finset.mem_Icc] at hd
          omega
        rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
        simp only [smul_eq_mul, mul_one]
        omega
      rw [hshift]
      have hlast : k + 1 + 1 - (k + 1) = 1 := by omega
      rw [hlast]
      nlinarith

private lemma sidon_window_quadratic {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (hSidon : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    (M : ℝ) * (A.card : ℝ) ^ 2 ≤
      ((N : ℝ) + (M : ℝ) - 1) * ((M : ℝ) - 1 + (A.card : ℝ)) := by
  let I : Finset ℤ := Finset.Icc (2 - (M : ℤ)) (N : ℤ)
  let cnt : ℤ → ℕ := fun x => (A.filter (fun (a : ℕ) => x ≤ (a : ℤ) ∧ (a : ℤ) < x + (M : ℤ))).card
  have hI_card : I.card = N + M - 1 := by
    rw [Int.card_Icc]
    omega
  -- First moment: ∑ x ∈ I, cnt x = M * A.card
  have hfirst : ∑ x ∈ I, cnt x = M * A.card := by
    calc ∑ x ∈ I, cnt x
        = ∑ x ∈ I, ∑ a ∈ A, (if x ≤ (a : ℤ) ∧ (a : ℤ) < x + (M : ℤ) then 1 else 0) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          dsimp only [cnt]
          rw [Finset.card_filter]
      _ = ∑ a ∈ A, ∑ x ∈ I, (if x ≤ (a : ℤ) ∧ (a : ℤ) < x + (M : ℤ) then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ a ∈ A, M := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          have ha_mem := Finset.mem_Icc.mp (hAsub ha)
          rw [← Finset.card_filter]
          have hfilt : I.filter (fun x => x ≤ (a : ℤ) ∧ (a : ℤ) < x + (M : ℤ)) =
              Finset.Icc ((a : ℤ) - (M : ℤ) + 1) (a : ℤ) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_Icc, I]
            omega
          rw [hfilt, Int.card_Icc]
          omega
      _ = M * A.card := by simp [mul_comm]
  -- Second moment: ∑ x ∈ I, cnt x * (cnt x - 1) ≤ M * (M - 1)
  have hsecond : ∑ x ∈ I, cnt x * (cnt x - 1) ≤ M * (M - 1) := by
    have hpair : ∀ x ∈ I, cnt x * (cnt x - 1) =
        2 * ((A ×ˢ A).filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ x ≤ (p.1 : ℤ) ∧ (p.2 : ℤ) < x + (M : ℤ))).card := by
      intro x _
      set S : Finset ℕ := A.filter (fun (a : ℕ) => x ≤ (a : ℤ) ∧ (a : ℤ) < x + (M : ℤ))
      have hcard_eq : ((A ×ˢ A).filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ x ≤ (p.1 : ℤ) ∧ (p.2 : ℤ) < x + (M : ℤ))) =
          (S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 < p.2) := by
        ext ⟨b, c⟩
        simp only [Finset.mem_filter, Finset.mem_product, S]
        constructor
        · rintro ⟨⟨hb, hc⟩, hlt, hxb, hcx⟩
          exact ⟨⟨⟨hb, hxb, by omega⟩, ⟨hc, by omega, hcx⟩⟩, hlt⟩
        · rintro ⟨⟨⟨hb, hxb, _⟩, ⟨hc, _, hcx⟩⟩, hlt⟩
          exact ⟨⟨hb, hc⟩, hlt, hxb, hcx⟩
      rw [hcard_eq]
      have hlt_gt : ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 < p.2)).card =
          ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.2 < p.1)).card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro ⟨b, c⟩ hp
          simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
        · intro ⟨b₁, c₁⟩ _ ⟨b₂, c₂⟩ _ h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.2 h.1
        · intro ⟨b, c⟩ hp
          refine ⟨(c, b), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      have hdisj : Disjoint ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 < p.2))
          ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.2 < p.1)) := by
        rw [Finset.disjoint_filter]
        intro p _ h1 h2; omega
      have hunion : ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 < p.2)) ∪
          ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.2 < p.1)) =
          (S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 ≠ p.2) := by
        ext ⟨b, c⟩
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro (⟨h, hlt⟩ | ⟨h, hgt⟩) <;> exact ⟨h, by omega⟩
        · rintro ⟨h, hne⟩
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact Or.inl ⟨h, hlt⟩
          · exact Or.inr ⟨h, hgt⟩
      have hoff : ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 ≠ p.2)).card = S.card * (S.card - 1) := by
        have hdiag : ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 = p.2)).card = S.card := by
          refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
          · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
          · intro p₁ hp₁ p₂ hp₂ heq
            have h1 := (Finset.mem_filter.mp hp₁).2
            have h2 := (Finset.mem_filter.mp hp₂).2
            exact Prod.ext heq (by rw [← h1, ← h2, heq])
          · intro a ha
            exact ⟨(a, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩, rfl⟩
        have hsum : ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 = p.2)).card +
            ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 ≠ p.2)).card = (S ×ˢ S).card := by
          rw [← Finset.card_union_of_disjoint (by
            rw [Finset.disjoint_filter]; intro p _ h1 h2; exact h2 h1)]
          congr 1; ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product]; tauto
        rw [hdiag, Finset.card_product] at hsum
        have hsub : S.card * S.card - S.card = S.card * (S.card - 1) := by
          cases S.card with
          | zero => simp
          | succ k => simp [Nat.mul_succ]
        omega
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hunion, hoff, ← hlt_gt] at hc
      change S.card * (S.card - 1) = 2 * ((S ×ˢ S).filter (fun (p : ℕ × ℕ) => p.1 < p.2)).card
      omega
    rw [Finset.sum_congr rfl hpair, ← Finset.mul_sum]
    rw [← sum_Icc_sub_eq M]
    apply Nat.mul_le_mul_left 2
    let P := (A ×ˢ A).filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ p.2 - p.1 < M)
    have hswap : ∑ x ∈ I, ((A ×ˢ A).filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ x ≤ (p.1 : ℤ) ∧ (p.2 : ℤ) < x + (M : ℤ))).card
        = ∑ p ∈ P, (M - (p.2 - p.1)) := by
      calc ∑ x ∈ I, ((A ×ˢ A).filter (fun (p : ℕ × ℕ) => p.1 < p.2 ∧ x ≤ (p.1 : ℤ) ∧ (p.2 : ℤ) < x + (M : ℤ))).card
          = ∑ x ∈ I, ∑ p ∈ P, (if x ≤ (p.1 : ℤ) ∧ (p.2 : ℤ) < x + (M : ℤ) then 1 else 0) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [← Finset.card_filter]
            congr 1
            ext ⟨b, c⟩
            simp only [Finset.mem_filter, Finset.mem_product, P]
            constructor
            · rintro ⟨hbc, hlt, hxb, hcx⟩
              exact ⟨⟨hbc, hlt, by omega⟩, hxb, hcx⟩
            · rintro ⟨⟨hbc, hlt, _⟩, hxb, hcx⟩
              exact ⟨hbc, hlt, hxb, hcx⟩
        _ = ∑ p ∈ P, ∑ x ∈ I, (if x ≤ (p.1 : ℤ) ∧ (p.2 : ℤ) < x + (M : ℤ) then 1 else 0) :=
            Finset.sum_comm
        _ = ∑ p ∈ P, (M - (p.2 - p.1)) := by
            refine Finset.sum_congr rfl (fun ⟨b, c⟩ hp => ?_)
            simp only [Finset.mem_filter, Finset.mem_product, P] at hp
            have hb_mem := Finset.mem_Icc.mp (hAsub hp.1.1)
            have hc_mem := Finset.mem_Icc.mp (hAsub hp.1.2)
            rw [← Finset.card_filter]
            have hfilt : I.filter (fun x => x ≤ (b : ℤ) ∧ (c : ℤ) < x + (M : ℤ)) =
                Finset.Icc ((c : ℤ) - (M : ℤ) + 1) (b : ℤ) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_Icc, I]
              omega
            rw [hfilt, Int.card_Icc]
            omega
    rw [hswap]
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) := by
      intro ⟨b₁, c₁⟩ h1 ⟨b₂, c₂⟩ h2 hdiff
      dsimp only at hdiff
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, P] at h1 h2
      have hsum : c₁ + b₂ = c₂ + b₁ := by omega
      have hres := hSidon c₁ h1.1.2 b₂ h2.1.1 c₂ h2.1.2 b₁ h1.1.1 hsum
      rcases hres with ⟨hc, hb⟩ | ⟨hcb, _⟩
      · exact Prod.ext hb.symm hc
      · omega
    have hmap : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ))
        ((Finset.Icc 1 (M - 1) : Finset ℕ) : Set ℕ) := by
      intro ⟨b, c⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, P] at hp ⊢
      omega
    calc ∑ p ∈ P, (M - (p.2 - p.1))
        = ∑ d ∈ P.image (fun p => p.2 - p.1), (M - d) := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ d ∈ Finset.Icc 1 (M - 1), (M - d) := by
          refine Finset.sum_le_sum_of_subset ?_
          intro d hd
          rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
          exact hmap hp
  -- Cauchy-Schwarz via Finset.sum_mul_sq_le_sq_mul_sq with constant 1
  have hcs_raw := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun x => (cnt x : ℝ))
  have hcs : (∑ x ∈ I, (cnt x : ℝ)) ^ 2 ≤ (I.card : ℝ) * ∑ x ∈ I, (cnt x : ℝ) ^ 2 := by
    simpa [one_mul, Finset.sum_const, nsmul_eq_mul] using hcs_raw
  have hsum_cast : (∑ x ∈ I, (cnt x : ℝ)) = (M : ℝ) * (A.card : ℝ) := by
    exact_mod_cast hfirst
  have hsq_bound : (∑ x ∈ I, (cnt x : ℝ) ^ 2) ≤ (M : ℝ) * ((M : ℝ) - 1) + (M : ℝ) * (A.card : ℝ) := by
    have h1 : ∀ x ∈ I, (cnt x : ℝ) ^ 2 = ((cnt x * (cnt x - 1) : ℕ) : ℝ) + (cnt x : ℝ) := by
      intro x _
      cases hc : cnt x with
      | zero => simp
      | succ k => push_cast; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Nat.cast_sum, ← Nat.cast_sum, hfirst, Nat.cast_mul]
    have hsec_r : ((∑ x ∈ I, cnt x * (cnt x - 1) : ℕ) : ℝ) ≤ (M : ℝ) * ((M : ℝ) - 1) := by
      have hcast : ((M * (M - 1) : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hM, Nat.cast_one]
      rw [← hcast]
      exact_mod_cast hsecond
    linarith
  have hI_r : (I.card : ℝ) = (N : ℝ) + (M : ℝ) - 1 := by
    rw [hI_card, Nat.cast_sub (by omega : 1 ≤ N + M), Nat.cast_add, Nat.cast_one]
  rw [hsum_cast, hI_r] at hcs
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNM_nonneg : (0 : ℝ) ≤ (N : ℝ) + (M : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hcomb : ((M : ℝ) * (A.card : ℝ)) ^ 2 ≤
      ((N : ℝ) + (M : ℝ) - 1) * ((M : ℝ) * ((M : ℝ) - 1) + (M : ℝ) * (A.card : ℝ)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq_bound hNM_nonneg)
  nlinarith

/-- **Cilleruelo (2010) / Erdős–Turán (1941) / Lindström (1969) Sharp All-`N` Sidon Upper Bound**:
for every `N ≥ 1` and every Sidon set `A ⊆ {1, …, N}`, `|A| < √N + N^{1/4} + 1/2`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_sidon_cilleruelo_upper_bound (N : ℕ) (hN : 1 ≤ N)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (hSidon : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    (A.card : ℝ) < Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 / 2 := by
  set r : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hr_def
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have hr_ge1 : 1 ≤ r := Real.one_le_rpow hN_ge1 (by norm_num)
  have hr_pos : 0 < r := by linarith
  have hr4 : r ^ 4 = (N : ℝ) := by
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    norm_num
  have hr2 : r ^ 2 = Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ r ^ 2)]
    congr 1
    nlinarith [hr4]
  let M : ℕ := Nat.floor (r ^ 3) + 1
  have hM_pos : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  set δ : ℝ := (M : ℝ) - r ^ 3 with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have hlt : r ^ 3 < ((Nat.floor (r ^ 3) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one (r ^ 3)
    have hM_cast : (M : ℝ) = ((Nat.floor (r ^ 3) : ℕ) : ℝ) + 1 := by simp [M]
    linarith
  have hδ_le1 : δ ≤ 1 := by
    rw [hδ_def]
    have hle : ((Nat.floor (r ^ 3) : ℕ) : ℝ) ≤ r ^ 3 := Nat.floor_le (by positivity)
    have hM_cast : (M : ℝ) = ((Nat.floor (r ^ 3) : ℕ) : ℝ) + 1 := by simp [M]
    linarith
  have hquad := sidon_window_quadratic hN hM_pos A hAsub hSidon
  by_contra hge
  push Not at hge
  set k : ℝ := (A.card : ℝ)
  set k₀ : ℝ := r ^ 2 + r + 1 / 2
  have hk_ge : k₀ ≤ k := by rw [← hr2] at hge; exact hge
  have hM_eq : (M : ℝ) = r ^ 3 + δ := by linarith [hδ_def]
  have hf_k0 : (M : ℝ) * k₀ ^ 2 - ((N : ℝ) + (M : ℝ) - 1) * ((M : ℝ) - 1 + k₀) > 0 := by
    have hpoly : (M : ℝ) * k₀ ^ 2 - ((N : ℝ) + (M : ℝ) - 1) * ((M : ℝ) - 1 + k₀) =
        r ^ 4 / 2 + 7 * r ^ 3 / 4 + (δ + 1) * r ^ 2 + r - δ ^ 2 + 7 * δ / 4 - 1 / 2 := by
      rw [hM_eq, ← hr4]
      dsimp only [k₀]
      ring
    rw [hpoly]
    have hδ_quad : -δ ^ 2 + 7 * δ / 4 - 1 / 2 ≥ -1 / 2 := by nlinarith
    have hr2_ge : 1 ≤ r ^ 2 := by nlinarith
    have hr3_ge : 1 ≤ r ^ 3 := by nlinarith
    have hr4_ge : 1 ≤ r ^ 4 := by nlinarith
    nlinarith
  have hslope : 0 ≤ (M : ℝ) * (k + k₀) - ((N : ℝ) + (M : ℝ) - 1) := by
    have h2 : (M : ℝ) * (2 * k₀) - ((N : ℝ) + (M : ℝ) - 1) =
        2 * r ^ 5 + r ^ 4 + 2 * δ * r ^ 2 + 2 * δ * r + 1 := by
      rw [hM_eq, ← hr4]
      dsimp only [k₀]
      ring
    have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := by positivity
    have hr5_nonneg : 0 ≤ r ^ 5 := by positivity
    have hr4_nonneg : 0 ≤ r ^ 4 := by positivity
    nlinarith [sq_nonneg r]
  have hdiff : ((M : ℝ) * k ^ 2 - ((N : ℝ) + (M : ℝ) - 1) * ((M : ℝ) - 1 + k)) -
      ((M : ℝ) * k₀ ^ 2 - ((N : ℝ) + (M : ℝ) - 1) * ((M : ℝ) - 1 + k₀)) =
      (k - k₀) * ((M : ℝ) * (k + k₀) - ((N : ℝ) + (M : ℝ) - 1)) := by ring
  nlinarith

/-- **Erdős–Turán (1941) / Lindström (1969) All-`N` Sidon Upper Bound** (`erdos_30.variants.lindstrom`):
for all `N : ℕ` (including `N = 0`) and every Sidon set `A ⊆ {1, …, N}`,
`(A.card : ℝ) ≤ √N + N^{1/4} + 1`. (Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_sidon_lindstrom_upper_bound (N : ℕ)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (hSidon : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    (A.card : ℝ) ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
  cases N with
  | zero =>
    have hA : A = ∅ := Finset.subset_empty.mp (by simpa using hAsub)
    subst hA
    simp
  | succ m =>
    have h := ppl088_sidon_cilleruelo_upper_bound (m + 1) (Nat.succ_pos m) A hAsub hSidon
    linarith

/-! ### Section 2: Unified Bose–Chowla (1962) Finite-Field `B_r` Construction (`r ≥ 2`) -/

private lemma roots_prod_X_add_C {K : Type*} [Field K] (s : Multiset K) :
    ((s.map (fun a => Polynomial.X + Polynomial.C a)).prod).roots = s.map Neg.neg := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons]
    have h1 : Polynomial.X + Polynomial.C a ≠ (0 : Polynomial K) := Polynomial.X_add_C_ne_zero a
    have h2 : (t.map (fun b => Polynomial.X + Polynomial.C b)).prod ≠ (0 : Polynomial K) := by
      intro hzero
      rw [Multiset.prod_eq_zero_iff] at hzero
      rcases Multiset.mem_map.mp hzero with ⟨b, _, hb⟩
      exact Polynomial.X_add_C_ne_zero b hb
    rw [Polynomial.roots_mul (mul_ne_zero h1 h2), Polynomial.roots_X_add_C, ih]
    rfl

private lemma monic_prod_X_add_C {K : Type*} [Field K] (s : Multiset K) :
    ((s.map (fun a => Polynomial.X + Polynomial.C a)).prod).Monic := by
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.monic_one]
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (Polynomial.monic_X_add_C a).mul ih

private lemma natDegree_prod_X_add_C {K : Type*} [Field K] (s : Multiset K) :
    ((s.map (fun a => Polynomial.X + Polynomial.C a)).prod).natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    have h1 : (Polynomial.X + Polynomial.C a : Polynomial K).Monic := Polynomial.monic_X_add_C a
    have h2 : ((t.map (fun b => Polynomial.X + Polynomial.C b)).prod).Monic := monic_prod_X_add_C t
    rw [Polynomial.natDegree_mul h1.ne_zero h2.ne_zero, Polynomial.natDegree_X_add_C, ih]
    omega

private lemma aeval_prod_X_add_C {K L : Type*} [Field K] [Field L] [Algebra K L]
    (θ : L) (s : Multiset K) :
    Polynomial.aeval θ ((s.map (fun a => Polynomial.X + Polynomial.C a)).prod) =
      (s.map (fun a => θ + algebraMap K L a)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      map_mul, Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, ih]

/-- **Unified Bose–Chowla (1962) / Bose (1942) Construction for ALL `r ≥ 2` and ALL Primes `p`**:
for every prime `p` and every `r ≥ 2`, there exists `A ⊆ Icc 1 (p ^ r - 1)` of size `p` such that
all `r`-element multiset sums from `A` are distinct. (Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_bose_chowla_Br_prime_lower_bound (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p ^ r - 1) ∧ A.card = p ∧
      ∀ m₁ m₂ : Multiset ℕ,
        m₁.card = r → m₂.card = r →
        (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
        m₁.sum = m₂.sum → m₁ = m₂ := by
  let : Fact p.Prime := ⟨hp⟩
  open scoped Classical in
  have hr0 : r ≠ 0 := by omega
  let : Fintype (GaloisField p r) := Fintype.ofFinite (GaloisField p r)
  have hcardF : Fintype.card (GaloisField p r) = p ^ r := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p r hr0
  have hcard_units : Fintype.card (GaloisField p r)ˣ = p ^ r - 1 := by
    rw [Fintype.card_units, hcardF]
  have hpr_gt1 : 1 < p ^ r := by
    have hp2 : 2 ≤ p := hp.two_le
    calc 1 < 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp2 2
      _ ≤ p ^ r := Nat.pow_le_pow_right (by omega) hr
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p r)ˣ)
  let θ : GaloisField p r := (g : GaloisField p r)
  have hminpoly_deg : (minpoly (ZMod p) θ).natDegree = r := by
    have htop : IntermediateField.adjoin (ZMod p) ({θ} : Set (GaloisField p r)) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      by_cases hx : x = 0
      · subst hx; exact zero_mem _
      · let ux : (GaloisField p r)ˣ := Units.mk0 x hx
        have hmem := hg ux
        rw [Subgroup.mem_zpowers_iff] at hmem
        obtain ⟨k, hk⟩ := hmem
        have hx_eq : x = θ ^ k := by
          have := congrArg (fun u : (GaloisField p r)ˣ => (u : GaloisField p r)) hk
          simpa [ux, θ] using this.symm
        rw [hx_eq]
        exact zpow_mem (IntermediateField.subset_adjoin (ZMod p) {θ} (Set.mem_singleton θ)) k
    have hfinrank_F : Module.finrank (ZMod p) (GaloisField p r) = r := by
      have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := GaloisField p r)
      rw [ZMod.card, hcardF] at h1
      exact Nat.pow_right_injective hp.two_le h1.symm
    have hadj_deg := IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := ZMod p) θ)
    rw [htop, IntermediateField.finrank_top'] at hadj_deg
    omega
  have haeval_ne_zero : ∀ Q : Polynomial (ZMod p), Q.natDegree < r → Q ≠ 0 →
      Polynomial.aeval θ Q ≠ 0 := by
    intro Q hdeg hQ hzero
    have hdvd : minpoly (ZMod p) θ ∣ Q := minpoly.dvd (ZMod p) θ hzero
    have hle := Polynomial.natDegree_le_of_dvd hdvd hQ
    omega
  have hshift_ne_zero : ∀ a : ZMod p, θ + algebraMap (ZMod p) (GaloisField p r) a ≠ 0 := by
    intro a
    have hdeg : (Polynomial.X + Polynomial.C a : Polynomial (ZMod p)).natDegree < r := by
      rw [Polynomial.natDegree_X_add_C]; omega
    have hne := haeval_ne_zero (Polynomial.X + Polynomial.C a) hdeg (Polynomial.X_add_C_ne_zero a)
    simpa [Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C] using hne
  have hex_exp : ∀ a : ZMod p, ∃ k : ℕ, 1 ≤ k ∧ k ≤ p ^ r - 1 ∧
      θ ^ k = θ + algebraMap (ZMod p) (GaloisField p r) a := by
    intro a
    let u : (GaloisField p r)ˣ := Units.mk0 (θ + algebraMap (ZMod p) (GaloisField p r) a) (hshift_ne_zero a)
    have hmem := hg u
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨m, hm⟩ := hmem
    have hord : orderOf g = p ^ r - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_units]
    have hord_z : (orderOf g : ℤ) = (p ^ r - 1 : ℕ) := by exact_mod_cast hord
    let n : ℕ := Int.toNat (m % ((p ^ r - 1 : ℕ) : ℤ))
    have hn_lt : n < p ^ r - 1 := by
      have hmod_lt := Int.emod_lt_of_pos m (by omega : (0 : ℤ) < ((p ^ r - 1 : ℕ) : ℤ))
      have hmod_nn := Int.emod_nonneg m (by omega : (((p ^ r - 1 : ℕ) : ℤ)) ≠ 0)
      omega
    have hpow_n : g ^ n = u := by
      have h1 : g ^ (m % ((p ^ r - 1 : ℕ) : ℤ)) = g ^ m := by
        rw [← hord_z, zpow_mod_orderOf]
      have hmod_nn := Int.emod_nonneg m (by omega : (((p ^ r - 1 : ℕ) : ℤ)) ≠ 0)
      have hn_eq : (n : ℤ) = m % ((p ^ r - 1 : ℕ) : ℤ) := Int.toNat_of_nonneg hmod_nn
      rw [← zpow_natCast, hn_eq, h1, hm]
    by_cases hn0 : n = 0
    · refine ⟨p ^ r - 1, by omega, le_rfl, ?_⟩
      have hpow_ord : g ^ (p ^ r - 1) = u := by
        rw [← hord, pow_orderOf_eq_one]
        rw [hn0, pow_zero] at hpow_n
        exact hpow_n
      have := congrArg (fun v : (GaloisField p r)ˣ => (v : GaloisField p r)) hpow_ord
      simpa [u, θ] using this
    · refine ⟨n, by omega, by omega, ?_⟩
      have := congrArg (fun v : (GaloisField p r)ˣ => (v : GaloisField p r)) hpow_n
      simpa [u, θ] using this
  choose e he1 he2 he_pow using hex_exp
  have he_inj : Function.Injective e := by
    intro a b hab
    have h1 : θ + algebraMap (ZMod p) (GaloisField p r) a =
        θ + algebraMap (ZMod p) (GaloisField p r) b := by
      rw [← he_pow a, ← he_pow b, hab]
    have h2 : algebraMap (ZMod p) (GaloisField p r) a =
        algebraMap (ZMod p) (GaloisField p r) b := add_left_cancel h1
    exact (algebraMap (ZMod p) (GaloisField p r)).injective h2
  let A : Finset ℕ := Finset.univ.image e
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
    exact Finset.mem_Icc.mpr ⟨he1 a, he2 a⟩
  · rw [Finset.card_image_of_injective _ he_inj, Finset.card_univ, ZMod.card]
  · intro m₁ m₂ hm1_card hm2_card hm1_mem hm2_mem hsum
    have hlift : ∀ m : Multiset ℕ, (∀ x ∈ m, x ∈ A) →
        ∃ s : Multiset (ZMod p), s.map e = m := by
      intro m hm
      induction m using Multiset.induction_on with
      | empty => exact ⟨0, rfl⟩
      | cons x t ih =>
        have hx : x ∈ A := hm x (Multiset.mem_cons_self x t)
        rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
        obtain ⟨st, hst⟩ := ih (fun y hy => hm y (Multiset.mem_cons_of_mem hy))
        exact ⟨a ::ₘ st, by rw [Multiset.map_cons, hst]⟩
    obtain ⟨s₁, hs₁⟩ := hlift m₁ hm1_mem
    obtain ⟨s₂, hs₂⟩ := hlift m₂ hm2_mem
    have hs1_card : s₁.card = r := by rw [← Multiset.card_map e s₁, hs₁, hm1_card]
    have hs2_card : s₂.card = r := by rw [← Multiset.card_map e s₂, hs₂, hm2_card]
    let P₁ : Polynomial (ZMod p) := (s₁.map (fun a => Polynomial.X + Polynomial.C a)).prod
    let P₂ : Polynomial (ZMod p) := (s₂.map (fun a => Polynomial.X + Polynomial.C a)).prod
    have haeval_eq : Polynomial.aeval θ P₁ = Polynomial.aeval θ P₂ := by
      rw [aeval_prod_X_add_C, aeval_prod_X_add_C]
      have hpow_prod : ∀ s : Multiset (ZMod p),
          (s.map (fun a => θ + algebraMap (ZMod p) (GaloisField p r) a)).prod = θ ^ (s.map e).sum := by
        intro s
        induction s using Multiset.induction_on with
        | empty => simp
        | cons a t ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
            pow_add, ← he_pow a, ih]
      rw [hpow_prod s₁, hpow_prod s₂, hs₁, hs₂, hsum]
    have hP1_monic : P₁.Monic := monic_prod_X_add_C s₁
    have hP2_monic : P₂.Monic := monic_prod_X_add_C s₂
    have hP1_deg : P₁.natDegree = r := by rw [natDegree_prod_X_add_C, hs1_card]
    have hP2_deg : P₂.natDegree = r := by rw [natDegree_prod_X_add_C, hs2_card]
    have hdiff_eq : P₁ - P₂ = 0 := by
      by_contra hne
      have hdiff_deg : (P₁ - P₂).natDegree < r := by
        apply (Polynomial.natDegree_lt_iff_degree_lt hne).mpr
        rw [Polynomial.degree_lt_iff_coeff_zero]
        intro n hn
        rw [Polynomial.coeff_sub]
        by_cases hnr : n = r
        · subst hnr
          rw [← hP1_deg, Polynomial.coeff_natDegree, hP1_monic.leadingCoeff,
            hP1_deg, ← hP2_deg, Polynomial.coeff_natDegree, hP2_monic.leadingCoeff, sub_self]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), sub_self]
      have hzero : Polynomial.aeval θ (P₁ - P₂) = 0 := by
        rw [map_sub, haeval_eq, sub_self]
      exact haeval_ne_zero (P₁ - P₂) hdiff_deg hne hzero
    have hP_eq : P₁ = P₂ := sub_eq_zero.mp hdiff_eq
    have hroots : s₁.map Neg.neg = s₂.map Neg.neg := by
      rw [← roots_prod_X_add_C, ← roots_prod_X_add_C]
      exact congrArg Polynomial.roots hP_eq
    have hs_eq : s₁ = s₂ := by
      have := congrArg (Multiset.map Neg.neg) hroots
      simpa [Multiset.map_map, Function.comp_def] using this
    rw [← hs₁, ← hs₂, hs_eq]

/-! ### Section 3: Asymptotic Lower Bounds (`r ≥ 2`, `r = 2` Sidon `h(N) ~ √N`, `r = 3` Bose–Chowla) -/

/-- General Bose–Chowla asymptotic lower bound for all `r ≥ 2`, using Tier A
`RHDirect.Stage8ExplicitPrimeBounds.exists_prime_in_Ioc_polylog`. -/
private lemma bose_chowla_Br_asymptotic_lower (r : ℕ) (hr : 2 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (1 - ε) * (N : ℝ) ^ ((1 : ℝ) / (r : ℝ)) ≤ (A.card : ℝ) ∧
        ∀ m₁ m₂ : Multiset ℕ,
          m₁.card = r → m₂.card = r →
          (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
          m₁.sum = m₂.sum → m₁ = m₂ := by
  intro ε hε
  by_cases hε1 : 1 ≤ ε
  · refine Filter.Eventually.of_forall (fun N => ⟨∅, Finset.empty_subset _, ?_, ?_⟩)
    · have h1 : 1 - ε ≤ 0 := by linarith
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / (r : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      simp only [Finset.card_empty, Nat.cast_zero]
      nlinarith
    · intro m₁ _ hm1 _ hmem _
      have hne : m₁ ≠ 0 := by intro h; simp [h] at hm1; omega
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      exact absurd (hmem x hx) (Finset.notMem_empty x)
  push Not at hε1
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨X₀, hshort⟩ := RHDirect.Stage8ExplicitPrimeBounds.exists_prime_in_Ioc_polylog 1 zero_lt_one
  set M₀ : ℝ := max (max X₀ (Real.exp (2 / ε))) 4
  have hM0_pos : 0 < M₀ := by positivity
  let N₀ : ℕ := Nat.ceil ((M₀ / (1 - ε)) ^ r) + 1
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun N hN => ?_⟩
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : 1 ≤ N := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hN
    exact_mod_cast this
  set y : ℝ := (N : ℝ) ^ ((1 : ℝ) / (r : ℝ)) with hy_def
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hN_pos _
  have hy_pow : y ^ r = (N : ℝ) := by
    rw [hy_def, ← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le, one_div_mul_cancel hr_pos.ne',
      Real.rpow_one]
  set x : ℝ := (1 - ε) * y with hx_def
  have hx_ge_M0 : M₀ ≤ x := by
    have h1 : (M₀ / (1 - ε)) ^ r ≤ (N : ℝ) := by
      have hceil := Nat.le_ceil ((M₀ / (1 - ε)) ^ r)
      have hN_cast : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have : ((Nat.ceil ((M₀ / (1 - ε)) ^ r) : ℕ) : ℝ) ≤ (N₀ : ℝ) := by simp [N₀]
      linarith
    have h2 : M₀ / (1 - ε) ≤ y := by
      have hbase_nn : 0 ≤ M₀ / (1 - ε) := div_nonneg hM0_pos.le (by linarith)
      have hrp := Real.rpow_le_rpow (pow_nonneg hbase_nn r) h1 (by positivity : (0 : ℝ) ≤ 1 / (r : ℝ))
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nn, mul_one_div_cancel hr_pos.ne',
        Real.rpow_one] at hrp
      exact hrp
    rw [hx_def]
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 - ε)
    rwa [mul_div_cancel₀ _ (by linarith : (1 - ε) ≠ 0)] at this
  have hx_ge_X0 : X₀ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx_ge_M0
  have hx_ge_exp : Real.exp (2 / ε) ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx_ge_M0
  have hx_ge4 : 4 ≤ x := (le_max_right _ _).trans hx_ge_M0
  obtain ⟨p, hp, hxp, hpy⟩ := hshort x hx_ge_X0
  have hlog_ge : 2 / ε ≤ Real.log x := by
    rw [← Real.log_exp (2 / ε)]
    exact Real.log_le_log (Real.exp_pos _) hx_ge_exp
  have hlog_pos : 0 < Real.log x := by
    have : 0 < 2 / ε := by positivity
    linarith
  have hp_le_y : (p : ℝ) ≤ y := by
    have h1 : x / (Real.log x) ^ (1 : ℝ) ≤ x * (ε / 2) := by
      rw [Real.rpow_one, div_le_iff₀ hlog_pos]
      have : 1 ≤ (ε / 2) * Real.log x := by
        have := mul_le_mul_of_nonneg_left hlog_ge (by positivity : (0 : ℝ) ≤ ε / 2)
        have hcalc : ε / 2 * (2 / ε) = 1 := by field_simp
        linarith
      nlinarith
    have h2 : x + x * (ε / 2) ≤ y := by
      rw [hx_def]
      nlinarith
    linarith
  have hpr_le_N : p ^ r ≤ N := by
    have h1 : ((p ^ r : ℕ) : ℝ) ≤ (N : ℝ) := by
      rw [Nat.cast_pow, ← hy_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg p) hp_le_y r
    exact_mod_cast h1
  obtain ⟨A, hAsub, hAcard, hBr⟩ := ppl088_bose_chowla_Br_prime_lower_bound p r hp hr
  refine ⟨A, hAsub.trans (Finset.Icc_subset_Icc_right (by omega)), ?_, hBr⟩
  rw [hAcard]
  linarith

/-- **Sidon Asymptotic Lower Bound** (`erdos_30.variants.singer`, proved via Bose 1942 + Tier A PNT):
for every `ε > 0`, eventually there exists a Sidon set `A ⊆ {1, …, N}` with `(1 - ε) √N ≤ |A|`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_sidon_asymptotic_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (1 - ε) * Real.sqrt (N : ℝ) ≤ (A.card : ℝ) ∧
        ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  intro ε hε
  filter_upwards [bose_chowla_Br_asymptotic_lower 2 le_rfl ε hε] with N ⟨A, hAsub, hAcard, hB2⟩
  refine ⟨A, hAsub, ?_, ?_⟩
  · have hsq : (N : ℝ) ^ ((1 : ℝ) / (2 : ℕ)) = Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rwa [← hsq]
  · intro a ha b hb c hc d hd hsum
    have heq := hB2 (a ::ₘ b ::ₘ 0) (c ::ₘ d ::ₘ 0)
      (by simp) (by simp)
      (by intro x hx; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
          rcases hx with rfl | rfl <;> assumption)
      (by intro x hx; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
          rcases hx with rfl | rfl <;> assumption)
      (by simp only [Multiset.sum_cons, Multiset.sum_zero, add_zero]; exact hsum)
    have hmem : a ∈ (c ::ₘ d ::ₘ 0 : Multiset ℕ) := heq ▸ Multiset.mem_cons_self a (b ::ₘ 0)
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact Or.inl ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩

/-- **Full Sidon Asymptotic Equivalence** (`h(N) ~ √N`, matching `erdos_30.variants.asymptotic`):
combining Cilleruelo's sharp upper bound with Bose's finite-field lower bound + Tier A PNT.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_sidon_asymptotic_equiv :
    (fun N : ℕ =>
      ((((Finset.Icc 1 N).powerset.filter (fun A =>
        ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
          a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c))).sup Finset.card : ℕ) : ℝ))
    ~[atTop] (fun N : ℕ => Real.sqrt (N : ℝ)) := by
  rw [Asymptotics.isEquivalent_iff_exists_eq_mul]
  let h : ℕ → ℕ := fun N =>
    ((Finset.Icc 1 N).powerset.filter (fun A =>
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c))).sup Finset.card
  refine ⟨fun N => if N = 0 then 1 else (h N : ℝ) / Real.sqrt (N : ℝ), ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (ppl088_sidon_asymptotic_lower_bound (ε / 2) (by linarith))
    let N₂ : ℕ := max (max N₁ 1) (Nat.ceil ((4 / ε) ^ 4) + 1)
    refine ⟨N₂, fun N hN => ?_⟩
    have hN_ge1 : 1 ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
    have hN_ne0 : N ≠ 0 := by omega
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_ge1
    have hsq_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
    simp only [hN_ne0, ↓reduceIte, Real.dist_eq]
    obtain ⟨A, hAsub, hAcard, hASidon⟩ := hN₁ N (((le_max_left _ _).trans (le_max_left _ _)).trans hN)
    have hA_le_h : (A.card : ℝ) ≤ (h N : ℝ) := by
      have hmem : A ∈ (Finset.Icc 1 N).powerset.filter (fun B =>
          ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, ∀ d ∈ B,
            a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAsub, hASidon⟩
      exact_mod_cast Finset.le_sup (f := Finset.card) hmem
    have hh_le : (h N : ℝ) ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
      have hsup : h N ≤ Nat.floor (Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1) := by
        apply Finset.sup_le
        intro B hB
        rw [Finset.mem_filter, Finset.mem_powerset] at hB
        exact Nat.le_floor (ppl088_sidon_lindstrom_upper_bound N B hB.1 hB.2)
      exact (Nat.cast_le.mpr hsup).trans (Nat.floor_le (by positivity))
    set r : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4)
    have hr_pos : 0 < r := Real.rpow_pos_of_pos hN_pos _
    have hr4 : r ^ 4 = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
    have hr2 : r ^ 2 = Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ r ^ 2)]; congr 1; nlinarith [hr4]
    have hr_ge : 4 / ε ≤ r := by
      have h1 : (4 / ε) ^ 4 ≤ (N : ℝ) := by
        have hceil := Nat.le_ceil ((4 / ε) ^ 4)
        have hN_cast : (Nat.ceil ((4 / ε) ^ 4) + 1 : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast ((le_max_right _ _).trans hN)
        linarith
      have h2 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (4 / ε) ^ 4) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 4 / ε)] at h2
      norm_num at h2
      exact h2
    have hr_ge1 : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hN_ge1) (by norm_num)
    have hratio_err : (r + 1) / Real.sqrt (N : ℝ) ≤ ε / 2 := by
      rw [← hr2, div_le_iff₀ (by positivity : 0 < r ^ 2)]
      have h1 : 4 ≤ r * ε := (div_le_iff₀ hε).mp hr_ge
      nlinarith
    have hratio_mul : r + 1 ≤ (ε / 2) * Real.sqrt (N : ℝ) :=
      (div_le_iff₀ hsq_pos).mp hratio_err
    rw [abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hsq_pos]
      nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hsq_pos]
      nlinarith
  · rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun N hN => ?_⟩
    have hN0 : N ≠ 0 := by omega
    have hsq_ne : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
    dsimp only [Pi.mul_apply]
    rw [if_neg hN0]
    exact (div_mul_cancel₀ _ hsq_ne).symm

/-- **Bose–Chowla (1962) `B_3` Asymptotic Lower Bound** (`erdos_241.variants.lower_bound`):
for every `ε > 0`, eventually there exists a `B_3` set `A ⊆ {1, …, N}` with `(1 - ε) N^{1/3} ≤ |A|`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_b3_asymptotic_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (1 - ε) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (A.card : ℝ) ∧
        ∀ m₁ m₂ : Multiset ℕ,
          m₁.card = 3 → m₂.card = 3 →
          (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
          m₁.sum = m₂.sum → m₁ = m₂ := by
  intro ε hε
  filter_upwards [bose_chowla_Br_asymptotic_lower 3 (by norm_num) ε hε] with N h
  simpa using h

/-! ### Section 4: Elementary `B_3` Difference Bound (`(6N)^{1/3}`) & Non-Trivial `A + A - A` Multiplicity -/

private lemma b3_diff_unique {A : Finset ℕ}
    (hB3 : ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = 3 → m₂.card = 3 →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
    {a₁ a₂ b₁ c₁ c₂ d₁ : ℕ}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hb₁ : b₁ ∈ A)
    (hc₁ : c₁ ∈ A) (hc₂ : c₂ ∈ A) (hd₁ : d₁ ∈ A)
    (hba₁ : b₁ ≠ a₁) (hba₂ : b₁ ≠ a₂) (hdc₁ : d₁ ≠ c₁) (hdc₂ : d₁ ≠ c₂)
    (heq : (a₁ : ℤ) + (a₂ : ℤ) - (b₁ : ℤ) = (c₁ : ℤ) + (c₂ : ℤ) - (d₁ : ℤ)) :
    b₁ = d₁ ∧ ((a₁ = c₁ ∧ a₂ = c₂) ∨ (a₁ = c₂ ∧ a₂ = c₁)) := by
  have hsum : a₁ + a₂ + d₁ = c₁ + c₂ + b₁ := by omega
  have hm := hB3 (a₁ ::ₘ a₂ ::ₘ d₁ ::ₘ 0) (c₁ ::ₘ c₂ ::ₘ b₁ ::ₘ 0) (by simp) (by simp)
    (by intro x hx; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> assumption)
    (by intro x hx; simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> assumption)
    (by simp only [Multiset.sum_cons, Multiset.sum_zero, add_zero]; omega)
  have hb_mem : b₁ ∈ (a₁ ::ₘ a₂ ::ₘ d₁ ::ₘ 0 : Multiset ℕ) := by
    rw [hm]; simp
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hb_mem
  have hbd : b₁ = d₁ := by
    rcases hb_mem with h | h | h
    · exact absurd h hba₁
    · exact absurd h hba₂
    · exact h
  refine ⟨hbd, ?_⟩
  subst hbd
  have hm2 : (a₁ ::ₘ a₂ ::ₘ 0 : Multiset ℕ) = (c₁ ::ₘ c₂ ::ₘ 0) := by
    have h1 : (a₁ ::ₘ a₂ ::ₘ b₁ ::ₘ 0 : Multiset ℕ) = b₁ ::ₘ a₁ ::ₘ a₂ ::ₘ 0 := by
      rw [Multiset.cons_swap a₂ b₁, Multiset.cons_swap a₁ b₁]
    have h2 : (c₁ ::ₘ c₂ ::ₘ b₁ ::ₘ 0 : Multiset ℕ) = b₁ ::ₘ c₁ ::ₘ c₂ ::ₘ 0 := by
      rw [Multiset.cons_swap c₂ b₁, Multiset.cons_swap c₁ b₁]
    rw [h1, h2] at hm
    exact (Multiset.cons_inj_right b₁).mp hm
  have ha1_mem : a₁ ∈ (c₁ ::ₘ c₂ ::ₘ 0 : Multiset ℕ) := hm2 ▸ Multiset.mem_cons_self a₁ (a₂ ::ₘ 0)
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha1_mem
  rcases ha1_mem with rfl | rfl
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr ⟨rfl, by omega⟩

private lemma b3_nontriv_rep_le_two {A : Finset ℕ}
    (hB3 : ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = 3 → m₂.card = 3 →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
    (z : ℤ) :
    (((A ×ˢ A) ×ˢ A).filter (fun t =>
      t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)).card ≤ 2 := by
  set S := ((A ×ˢ A) ×ˢ A).filter (fun t =>
      t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)
  by_cases hne : S.Nonempty
  · obtain ⟨⟨⟨a₁, a₂⟩, b₁⟩, h0⟩ := hne
    have h0' := h0
    simp only [S, Finset.mem_filter, Finset.mem_product] at h0'
    have hsub : S ⊆ ({((a₁, a₂), b₁), ((a₂, a₁), b₁)} : Finset ((ℕ × ℕ) × ℕ)) := by
      intro ⟨⟨c₁, c₂⟩, d₁⟩ ht
      simp only [S, Finset.mem_filter, Finset.mem_product] at ht
      have huniq := b3_diff_unique hB3 h0'.1.1.1 h0'.1.1.2 h0'.1.2
        ht.1.1.1 ht.1.1.2 ht.1.2 h0'.2.1 h0'.2.2.1 ht.2.1 ht.2.2.1
        (h0'.2.2.2.trans ht.2.2.2.symm)
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      rcases huniq with ⟨hbd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨⟨rfl, rfl⟩, hbd.symm⟩
      · exact Or.inr ⟨⟨rfl, rfl⟩, hbd.symm⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

/-- **Elementary `B_3` Difference Bound (`(6N)^{1/3}`)**:
for every `N ≥ 1` and every `B_3` set `A ⊆ {1, …, N}`,
`A.card * (A.card - 1) * (A.card - 2) ≤ 6 * N - 4`.
(Beats trivial `(18N)^{1/3}` down to `(6N)^{1/3}`; pure Mathlib statement, `0` custom definitions.) -/
theorem ppl088_b3_difference_upper_bound (N : ℕ) (hN : 1 ≤ N)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (hB3 : ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = 3 → m₂.card = 3 →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂) :
    A.card * (A.card - 1) * (A.card - 2) ≤ 6 * N - 4 := by
  let T := ((A ×ˢ A) ×ˢ A).filter (fun t => t.1.1 ≠ t.1.2 ∧ t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2)
  let Z := Finset.Icc (2 - (N : ℤ)) (2 * (N : ℤ) - 1)
  have hZ_card : Z.card = 3 * N - 2 := by
    rw [Int.card_Icc]; omega
  have hT_card : T.card = A.card * (A.card - 1) * (A.card - 2) := by
    have h1 : T.card = ∑ a ∈ A, ∑ b ∈ A.erase a, ((A.erase a).erase b).card := by
      have hbi : T.card = ∑ a ∈ A, ∑ b ∈ A.erase a, ∑ _c ∈ (A.erase a).erase b, 1 := by
        calc T.card
            = ∑ t ∈ ((A ×ˢ A) ×ˢ A), (if t.1.1 ≠ t.1.2 ∧ t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 then 1 else 0) := by
              dsimp only [T]
              rw [Finset.card_filter]
          _ = ∑ p ∈ A ×ˢ A, ∑ c ∈ A, (if p.1 ≠ p.2 ∧ c ≠ p.1 ∧ c ≠ p.2 then 1 else 0) :=
              Finset.sum_product _ _ _
          _ = ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, (if a ≠ b ∧ c ≠ a ∧ c ≠ b then 1 else 0) := by
              rw [Finset.sum_product]
          _ = ∑ a ∈ A, ∑ b ∈ A.erase a, ∑ _c ∈ (A.erase a).erase b, 1 := by
              refine Finset.sum_congr rfl (fun a _ => ?_)
              calc ∑ b ∈ A, ∑ c ∈ A, (if a ≠ b ∧ c ≠ a ∧ c ≠ b then 1 else 0)
                  = ∑ b ∈ A.erase a, ∑ c ∈ A, (if c ≠ a ∧ c ≠ b then 1 else 0) := by
                    rw [← Finset.sum_subset (Finset.erase_subset a A)]
                    · refine Finset.sum_congr rfl (fun b hb => ?_)
                      have hne : a ≠ b := (Finset.mem_erase.mp hb).1.symm
                      refine Finset.sum_congr rfl (fun c _ => by simp [hne])
                    · intro b hb hnot
                      have hba : b = a := by
                        by_contra hne
                        exact hnot (Finset.mem_erase.mpr ⟨hne, hb⟩)
                      subst hba
                      simp
                _ = ∑ b ∈ A.erase a, ∑ _c ∈ (A.erase a).erase b, 1 := by
                    refine Finset.sum_congr rfl (fun b _ => ?_)
                    rw [← Finset.card_filter, Finset.sum_const, smul_eq_mul, mul_one]
                    congr 1
                    ext c
                    simp [Finset.mem_erase, and_left_comm, and_comm, and_assoc]
      simpa using hbi
    rw [h1]
    have h2 : ∀ a ∈ A, ∀ b ∈ A.erase a, ((A.erase a).erase b).card = A.card - 2 := by
      intro a ha b hb
      rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
      omega
    calc ∑ a ∈ A, ∑ b ∈ A.erase a, ((A.erase a).erase b).card
        = ∑ a ∈ A, ∑ _b ∈ A.erase a, (A.card - 2) := by
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => h2 a ha b hb))
      _ = ∑ a ∈ A, (A.card - 1) * (A.card - 2) := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          rw [Finset.sum_const, Finset.card_erase_of_mem ha, smul_eq_mul]
      _ = A.card * (A.card - 1) * (A.card - 2) := by
          rw [Finset.sum_const, smul_eq_mul, mul_assoc]
  have hmaps : ∀ t ∈ T, (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) ∈ Z := by
    intro ⟨⟨a₁, a₂⟩, b₁⟩ ht
    simp only [T, Finset.mem_filter, Finset.mem_product] at ht
    have ha₁ := Finset.mem_Icc.mp (hAsub ht.1.1.1)
    have ha₂ := Finset.mem_Icc.mp (hAsub ht.1.1.2)
    have hb₁ := Finset.mem_Icc.mp (hAsub ht.1.2)
    simp only [Z, Finset.mem_Icc]
    omega
  have hfib := Finset.card_eq_sum_card_fiberwise
    (f := fun t : (ℕ × ℕ) × ℕ => (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ)) hmaps
  rw [← hT_card, hfib]
  calc ∑ z ∈ Z, (T.filter (fun t => (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)).card
      ≤ ∑ _z ∈ Z, 2 := by
        refine Finset.sum_le_sum (fun z _ => ?_)
        refine (Finset.card_le_card ?_).trans (b3_nontriv_rep_le_two hB3 z)
        intro t ht
        simp only [T, Finset.mem_filter] at ht ⊢
        exact ⟨ht.1.1, ht.1.2.2.1, ht.1.2.2.2, ht.2⟩
    _ = 2 * Z.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 6 * N - 4 := by rw [hZ_card]; omega

/-! ### Section 5: Exact Discrete Orthogonal-Cosine `L²` Autoconvolution Lower Bound & `B_3` Bound Beating Green (2001) -/

private lemma sum_Icc_cos_mul_sin_half (L : ℕ) (hL : 1 ≤ L) (θ : ℝ) :
    (∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ), Real.cos ((d : ℝ) * θ)) * Real.sin (θ / 2) =
      Real.sin (((L : ℝ) - 1 / 2) * θ) := by
  have hterm : ∀ d : ℤ,
      2 * (Real.cos ((d : ℝ) * θ) * Real.sin (θ / 2)) =
        Real.sin (((d : ℝ) + 1 / 2) * θ) - Real.sin (((d : ℝ) - 1 / 2) * θ) := by
    intro d
    have h1 : ((d : ℝ) + 1 / 2) * θ = (d : ℝ) * θ + θ / 2 := by ring
    have h2 : ((d : ℝ) - 1 / 2) * θ = (d : ℝ) * θ - θ / 2 := by ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  have hsum2 : 2 * ((∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ), Real.cos ((d : ℝ) * θ)) * Real.sin (θ / 2)) =
      2 * Real.sin (((L : ℝ) - 1 / 2) * θ) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    have hrew : ∀ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
        2 * (Real.cos ((d : ℝ) * θ) * Real.sin (θ / 2)) =
          Real.sin (((d : ℝ) + 1 / 2) * θ) - Real.sin (((d : ℝ) - 1 / 2) * θ) :=
      fun d _ => hterm d
    rw [Finset.sum_congr rfl hrew]
    let f : ℕ → ℝ := fun k => Real.sin ((((k : ℝ) - ((L : ℝ) - 1)) - 1 / 2) * θ)
    have hbij : ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
          (Real.sin (((d : ℝ) + 1 / 2) * θ) - Real.sin (((d : ℝ) - 1 / 2) * θ)) =
        ∑ k ∈ Finset.range (2 * L - 1), (f (k + 1) - f k) := by
      refine Finset.sum_bij (fun d _ => Int.toNat (d + (L - 1 : ℤ))) ?_ ?_ ?_ ?_
      · intro d hd
        rw [Finset.mem_Icc] at hd
        rw [Finset.mem_range]
        omega
      · intro d₁ hd₁ d₂ hd₂ heq
        rw [Finset.mem_Icc] at hd₁ hd₂
        omega
      · intro k hk
        rw [Finset.mem_range] at hk
        refine ⟨(k : ℤ) - (L - 1 : ℤ), ?_, ?_⟩
        · rw [Finset.mem_Icc]; omega
        · omega
      · intro d hd
        rw [Finset.mem_Icc] at hd
        have hcast : ((Int.toNat (d + (L - 1 : ℤ)) : ℕ) : ℝ) = (d : ℝ) + (L : ℝ) - 1 := by
          have hnn : 0 ≤ d + (L - 1 : ℤ) := by omega
          have h1 : ((Int.toNat (d + (L - 1 : ℤ)) : ℕ) : ℤ) = d + (L - 1 : ℤ) := Int.toNat_of_nonneg hnn
          have h2 : (((Int.toNat (d + (L - 1 : ℤ)) : ℕ) : ℤ) : ℝ) = ((d + (L - 1 : ℤ) : ℤ) : ℝ) := by
            exact_mod_cast h1
          push_cast at h2
          linarith
        dsimp only [f]
        push_cast
        rw [hcast]
        congr 1 <;> congr 1 <;> ring
    rw [hbij, Finset.sum_range_sub f (2 * L - 1)]
    dsimp only [f]
    have htop : ((((2 * L - 1 : ℕ) : ℝ) - ((L : ℝ) - 1)) - 1 / 2) * θ = ((L : ℝ) - 1 / 2) * θ := by
      have h1 : ((2 * L - 1 : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * L)]; push_cast; ring
      rw [h1]; ring
    have hbot : ((((0 : ℕ) : ℝ) - ((L : ℝ) - 1)) - 1 / 2) * θ = -(((L : ℝ) - 1 / 2) * θ) := by
      push_cast; ring
    rw [htop, hbot, Real.sin_neg]
    ring
  linarith

private lemma sum_Icc_cos_int_pi_div (L : ℕ) (hL : 1 ≤ L) (r : ℤ) (hr0 : r ≠ 0)
    (hr_lt : |r| < 2 * (L : ℤ)) :
    ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ), Real.cos ((d : ℝ) * ((r : ℝ) * Real.pi / (L : ℝ))) =
      if Even r then (-1 : ℝ) else (1 : ℝ) := by
  set θ : ℝ := (r : ℝ) * Real.pi / (L : ℝ)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hsin_ne : Real.sin (θ / 2) ≠ 0 := by
    have harg : θ / 2 = (r : ℝ) / (2 * (L : ℝ)) * Real.pi := by dsimp [θ]; ring
    rw [harg]
    intro hzero
    rw [Real.sin_eq_zero_iff] at hzero
    obtain ⟨k, hk⟩ := hzero
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hk_eq : (k : ℝ) = (r : ℝ) / (2 * (L : ℝ)) := by
      have := mul_right_cancel₀ hpi hk
      linarith
    have hmul : (k : ℝ) * (2 * (L : ℝ)) = (r : ℝ) := by
      rw [hk_eq, div_mul_cancel₀ _ (by positivity)]
    have hmul_int : k * (2 * (L : ℤ)) = r := by exact_mod_cast hmul
    rcases eq_or_ne k 0 with rfl | hk0
    · simp at hmul_int; exact hr0 hmul_int.symm
    · have hk_abs : 1 ≤ |k| := Int.one_le_abs hk0
      have hr_abs : |r| = |k| * (2 * (L : ℤ)) := by
        rw [← hmul_int, abs_mul, abs_of_pos (by omega : (0 : ℤ) < 2 * (L : ℤ))]
      nlinarith
  have hdir := sum_Icc_cos_mul_sin_half L hL θ
  have hrhs : Real.sin (((L : ℝ) - 1 / 2) * θ) =
      (if Even r then (-1 : ℝ) else (1 : ℝ)) * Real.sin (θ / 2) := by
    have harg : ((L : ℝ) - 1 / 2) * θ = (r : ℝ) * Real.pi - θ / 2 := by
      dsimp [θ]; field_simp
    rw [harg, Real.sin_sub]
    have hsin_rpi : Real.sin ((r : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi r
    have hcos_rpi : Real.cos ((r : ℝ) * Real.pi) = if Even r then 1 else -1 := by
      rw [Real.cos_int_mul_pi]
      split_ifs with he
      · obtain ⟨k, rfl⟩ := he
        have : (k + k : ℤ) = 2 * k := by ring
        rw [this, zpow_mul]; norm_num
      · have hodd : Odd r := Int.not_even_iff_odd.mp he
        obtain ⟨k, rfl⟩ := hodd
        rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_mul]
        norm_num
    rw [hsin_rpi, hcos_rpi]
    split_ifs <;> ring
  rw [hrhs] at hdir
  exact mul_right_cancel₀ hsin_ne hdir

private lemma sum_Icc_cos_halfint_orth (L M : ℕ) (hL : 1 ≤ L) (hML : 2 * M ≤ L)
    (j m : ℕ) (hj : j < M) (hm : m < M) :
    ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
      Real.cos ((d : ℝ) * (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ)))) *
      Real.cos ((d : ℝ) * (((4 * m + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ)))) =
      if j = m then (L : ℝ) else 0 := by
  set θj : ℝ := ((4 * j + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ))
  set θm : ℝ := ((4 * m + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ))
  have hprod : ∀ d : ℤ,
      Real.cos ((d : ℝ) * θj) * Real.cos ((d : ℝ) * θm) =
        (Real.cos ((d : ℝ) * (θj - θm)) + Real.cos ((d : ℝ) * (θj + θm))) / 2 := by
    intro d
    have h1 : (d : ℝ) * (θj - θm) = (d : ℝ) * θj - (d : ℝ) * θm := by ring
    have h2 : (d : ℝ) * (θj + θm) = (d : ℝ) * θj + (d : ℝ) * θm := by ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hprod, ← Finset.sum_div, Finset.sum_add_distrib]
  have hplus_arg : θj + θm = (((2 * (j : ℤ) + 2 * (m : ℤ) + 3 : ℤ) : ℝ) * Real.pi / (L : ℝ)) := by
    dsimp [θj, θm]; push_cast; ring
  have hplus_lt : |2 * (j : ℤ) + 2 * (m : ℤ) + 3| < 2 * (L : ℤ) := by
    rw [abs_of_pos (by omega)]
    omega
  have hplus : ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ), Real.cos ((d : ℝ) * (θj + θm)) = 1 := by
    rw [hplus_arg, sum_Icc_cos_int_pi_div L hL (2 * (j : ℤ) + 2 * (m : ℤ) + 3) (by omega) hplus_lt]
    have hnot : ¬ Even (2 * (j : ℤ) + 2 * (m : ℤ) + 3) := by
      rw [Int.not_even_iff_odd]
      exact ⟨(j : ℤ) + (m : ℤ) + 1, by ring⟩
    simp [hnot]
  rw [hplus]
  by_cases hjm : j = m
  · subst hjm
    have hzero : θj - θm = 0 := by dsimp [θj, θm]; ring
    rw [hzero]
    simp only [mul_zero, Real.cos_zero, Finset.sum_const, Int.card_Icc, nsmul_eq_mul,
      mul_one, ↓reduceIte]
    have hc : ((Int.toNat ((L - 1 : ℤ) + 1 - -(L - 1 : ℤ)) : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
      have h1 : Int.toNat ((L - 1 : ℤ) + 1 - -(L - 1 : ℤ)) = 2 * L - 1 := by omega
      rw [h1, Nat.cast_sub (by omega : 1 ≤ 2 * L)]
      push_cast; ring
    rw [hc]; ring
  · simp only [hjm, ↓reduceIte]
    have hminus_arg : θj - θm = (((2 * ((j : ℤ) - (m : ℤ)) : ℤ) : ℝ) * Real.pi / (L : ℝ)) := by
      dsimp [θj, θm]; push_cast; ring
    have hminus_lt : |2 * ((j : ℤ) - (m : ℤ))| < 2 * (L : ℤ) := by
      rw [abs_lt]; constructor <;> omega
    have hminus : ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ), Real.cos ((d : ℝ) * (θj - θm)) = -1 := by
      rw [hminus_arg, sum_Icc_cos_int_pi_div L hL (2 * ((j : ℤ) - (m : ℤ))) (by omega) hminus_lt]
      have hev : Even (2 * ((j : ℤ) - (m : ℤ))) := ⟨(j : ℤ) - (m : ℤ), by ring⟩
      simp [hev]
    rw [hminus]; norm_num

private lemma sum_Icc_cos_halfint_linear (L : ℕ) (hL : 1 ≤ L) (j : ℕ) (hj : 4 * j + 3 < 2 * L) :
    ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
      Real.cos ((d : ℝ) * (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ)))) =
      -(Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
        Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))) := by
  set θ : ℝ := ((4 * j + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ))
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hhalf : θ / 2 = ((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)) := by dsimp [θ]; ring
  have harg_pos : 0 < θ / 2 := by rw [hhalf]; positivity
  have harg_lt : θ / 2 < Real.pi / 2 := by
    rw [hhalf]
    have hlt : ((4 * j + 3 : ℕ) : ℝ) < 2 * (L : ℝ) := by exact_mod_cast hj
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi harg_pos (by linarith [Real.pi_pos])
  have hdir := sum_Icc_cos_mul_sin_half L hL θ
  have hnum : Real.sin (((L : ℝ) - 1 / 2) * θ) = -Real.cos (θ / 2) := by
    have harg : ((L : ℝ) - 1 / 2) * θ = (2 * (j : ℝ) + 1) * Real.pi + (Real.pi / 2 - θ / 2) := by
      dsimp [θ]; push_cast; field_simp; ring
    rw [harg, Real.sin_add]
    have hs : Real.sin ((2 * (j : ℝ) + 1) * Real.pi) = 0 := by
      have : (2 * (j : ℝ) + 1) * Real.pi = ((2 * j + 1 : ℕ) : ℝ) * Real.pi := by push_cast; ring
      rw [this]; exact Real.sin_nat_mul_pi (2 * j + 1)
    have hc : Real.cos ((2 * (j : ℝ) + 1) * Real.pi) = -1 := by
      have : (2 * (j : ℝ) + 1) * Real.pi = ((2 * j + 1 : ℕ) : ℝ) * Real.pi := by push_cast; ring
      rw [this, Real.cos_nat_mul_pi]
      simp [pow_add]
    rw [hs, hc, Real.sin_pi_div_two_sub]
    ring
  rw [hnum] at hdir
  rw [← hhalf, ← neg_div, eq_div_iff hsin_pos.ne']
  linarith

private lemma discrete_autocorr_cos_nonneg (L : ℕ) (f : ℕ → ℝ) (θ : ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
      (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) * Real.cos ((d : ℝ) * θ) := by
  have hrew : ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
      (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) * Real.cos ((d : ℝ) * θ) =
      (∑ a ∈ Finset.range L, f a * Real.cos ((a : ℝ) * θ)) ^ 2 +
      (∑ a ∈ Finset.range L, f a * Real.sin ((a : ℝ) * θ)) ^ 2 := by
    have h1 : ∀ a ∈ Finset.range L, ∀ b ∈ Finset.range L,
        (a : ℤ) - (b : ℤ) ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ) := by
      intro a ha b hb
      rw [Finset.mem_range] at ha hb
      rw [Finset.mem_Icc]; omega
    calc ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
            (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
              if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) * Real.cos ((d : ℝ) * θ)
        = ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
            ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
              if (a : ℤ) - (b : ℤ) = d then f a * f b * Real.cos ((d : ℝ) * θ) else 0 := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          split_ifs <;> ring
      _ = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
              if (a : ℤ) - (b : ℤ) = d then f a * f b * Real.cos ((d : ℝ) * θ) else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            f a * f b * Real.cos (((a : ℝ) - (b : ℝ)) * θ) := by
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
          rw [Finset.sum_ite_eq]
          simp only [h1 a ha b hb, ↓reduceIte, Int.cast_sub, Int.cast_natCast]
      _ = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            ((f a * Real.cos ((a : ℝ) * θ)) * (f b * Real.cos ((b : ℝ) * θ)) +
             (f a * Real.sin ((a : ℝ) * θ)) * (f b * Real.sin ((b : ℝ) * θ))) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
          have hsub : ((a : ℝ) - (b : ℝ)) * θ = (a : ℝ) * θ - (b : ℝ) * θ := by ring
          rw [hsub, Real.cos_sub]
          ring
      _ = (∑ a ∈ Finset.range L, f a * Real.cos ((a : ℝ) * θ)) ^ 2 +
          (∑ a ∈ Finset.range L, f a * Real.sin ((a : ℝ) * θ)) ^ 2 := by
          simp_rw [Finset.sum_add_distrib, sq, Finset.sum_mul_sum]
  rw [hrew]
  positivity

/-- **Exact Discrete Orthogonal-Cosine `L²` Autoconvolution Lower Bound** (Zero Integrals!):
for every `L ≥ 1`, `M` with `2 * M ≤ L`, and EVERY function `f : ℕ → ℝ` (even signed!) with
`∑ n ∈ range L, f n = 1`, its discrete autocorrelation `g(d) = ∑_{a - b = d} f a * f b` satisfies
`(∑ d ∈ Icc (-(L-1)) (L-1), g(d)²) * ((2L - 1) - (1/L) ∑_{j<M} cot²((4j+3)π/(4L))) ≥ 1`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_b3_discrete_autoconvolution_orthogonal_cosine_lb
    (L M : ℕ) (hL : 1 ≤ L) (hML : 2 * M ≤ L)
    (f : ℕ → ℝ) (hf_sum : ∑ n ∈ Finset.range L, f n = 1) :
    1 ≤ (∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
          (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) ^ 2) *
        ((2 * (L : ℝ) - 1) -
          (1 / (L : ℝ)) * ∑ j ∈ Finset.range M,
            (Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
             Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))) ^ 2) := by
  let D : Finset ℤ := Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ)
  let g : ℤ → ℝ := fun d =>
    ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
      if (a : ℤ) - (b : ℤ) = d then f a * f b else 0
  let θ : ℕ → ℝ := fun j => ((4 * j + 3 : ℕ) : ℝ) * Real.pi / (2 * (L : ℝ))
  let cotVal : ℕ → ℝ := fun j =>
    Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
    Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))
  let c : ℕ → ℝ := fun j => cotVal j / (L : ℝ)
  let H : ℤ → ℝ := fun d => 1 + ∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hc_nonneg : ∀ j ∈ Finset.range M, 0 ≤ c j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_lt : 4 * j + 3 < 2 * L := by omega
    have harg_pos : 0 < ((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)) := by positivity
    have harg_lt : ((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)) < Real.pi / 2 := by
      have hlt : ((4 * j + 3 : ℕ) : ℝ) < 2 * (L : ℝ) := by exact_mod_cast hj_lt
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos]
    have hcos_pos : 0 < Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], harg_lt⟩
    have hsin_pos : 0 < Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) :=
      Real.sin_pos_of_pos_of_lt_pi harg_pos (by linarith [Real.pi_pos])
    dsimp only [c, cotVal]
    positivity
  have hg_sum : ∑ d ∈ D, g d = 1 := by
    have hmem : ∀ a ∈ Finset.range L, ∀ b ∈ Finset.range L, (a : ℤ) - (b : ℤ) ∈ D := by
      intro a ha b hb
      rw [Finset.mem_range] at ha hb
      simp only [D, Finset.mem_Icc]; omega
    calc ∑ d ∈ D, g d
        = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            ∑ d ∈ D, if (a : ℤ) - (b : ℤ) = d then f a * f b else 0 := by
          dsimp only [g]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
      _ = ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L, f a * f b := by
          refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
          rw [Finset.sum_ite_eq]
          simp [hmem a ha b hb]
      _ = (∑ a ∈ Finset.range L, f a) * (∑ b ∈ Finset.range L, f b) := by
          rw [Finset.sum_mul_sum]
      _ = 1 := by rw [hf_sum, mul_one]
  have hip : 1 ≤ ∑ d ∈ D, g d * H d := by
    have hsplit : ∑ d ∈ D, g d * H d =
        (∑ d ∈ D, g d) + ∑ j ∈ Finset.range M, c j * ∑ d ∈ D, g d * Real.cos ((d : ℝ) * θ j) := by
      calc ∑ d ∈ D, g d * H d
          = ∑ d ∈ D, (g d + ∑ j ∈ Finset.range M, c j * (g d * Real.cos ((d : ℝ) * θ j))) := by
            refine Finset.sum_congr rfl (fun d _ => ?_)
            dsimp only [H]
            rw [mul_add, mul_one, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl (fun j _ => by ring)
        _ = (∑ d ∈ D, g d) + ∑ d ∈ D, ∑ j ∈ Finset.range M, c j * (g d * Real.cos ((d : ℝ) * θ j)) :=
            Finset.sum_add_distrib
        _ = (∑ d ∈ D, g d) + ∑ j ∈ Finset.range M, c j * ∑ d ∈ D, g d * Real.cos ((d : ℝ) * θ j) := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ _).symm)
    rw [hsplit, hg_sum]
    have hnonneg : 0 ≤ ∑ j ∈ Finset.range M, c j * ∑ d ∈ D, g d * Real.cos ((d : ℝ) * θ j) :=
      Finset.sum_nonneg (fun j hj => mul_nonneg (hc_nonneg j hj) (discrete_autocorr_cos_nonneg L f (θ j)))
    linarith
  have hH_sq : ∑ d ∈ D, H d ^ 2 =
      (2 * (L : ℝ) - 1) - (1 / (L : ℝ)) * ∑ j ∈ Finset.range M, cotVal j ^ 2 := by
    have hexp : ∀ d ∈ D, H d ^ 2 =
        1 + 2 * (∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j)) +
          ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range M,
            c j * c m * (Real.cos ((d : ℝ) * θ j) * Real.cos ((d : ℝ) * θ m)) := by
      intro d _
      dsimp only [H]
      have hsq : (∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j)) ^ 2 =
          ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range M,
            c j * c m * (Real.cos ((d : ℝ) * θ j) * Real.cos ((d : ℝ) * θ m)) := by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun m _ => by ring))
      linarith [show (1 + ∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j)) ^ 2 =
        1 + 2 * (∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j)) +
        (∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j)) ^ 2 by ring]
    rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hconst : ∑ _d ∈ D, (1 : ℝ) = 2 * (L : ℝ) - 1 := by
      simp only [Finset.sum_const, D, Int.card_Icc, nsmul_eq_mul, mul_one]
      have h1 : Int.toNat ((L - 1 : ℤ) + 1 - -(L - 1 : ℤ)) = 2 * L - 1 := by omega
      rw [h1, Nat.cast_sub (by omega : 1 ≤ 2 * L)]; push_cast; ring
    have hlin : ∑ d ∈ D, 2 * ∑ j ∈ Finset.range M, c j * Real.cos ((d : ℝ) * θ j) =
        -(2 / (L : ℝ)) * ∑ j ∈ Finset.range M, cotVal j ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      calc 2 * ∑ j ∈ Finset.range M, ∑ d ∈ D, c j * Real.cos ((d : ℝ) * θ j)
          = 2 * ∑ j ∈ Finset.range M, c j * ∑ d ∈ D, Real.cos ((d : ℝ) * θ j) := by
            congr 1; refine Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ _).symm)
        _ = 2 * ∑ j ∈ Finset.range M, c j * (-cotVal j) := by
            congr 1
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [Finset.mem_range] at hj
            rw [sum_Icc_cos_halfint_linear L hL j (by omega)]
        _ = -(2 / (L : ℝ)) * ∑ j ∈ Finset.range M, cotVal j ^ 2 := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            dsimp only [c]; ring
    have hquad : ∑ d ∈ D, ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range M,
          c j * c m * (Real.cos ((d : ℝ) * θ j) * Real.cos ((d : ℝ) * θ m)) =
        (1 / (L : ℝ)) * ∑ j ∈ Finset.range M, cotVal j ^ 2 := by
      rw [Finset.sum_comm]
      have hsw : ∀ j ∈ Finset.range M,
          ∑ d ∈ D, ∑ m ∈ Finset.range M,
            c j * c m * (Real.cos ((d : ℝ) * θ j) * Real.cos ((d : ℝ) * θ m)) =
          ∑ m ∈ Finset.range M, (c j * c m) *
            ∑ d ∈ D, Real.cos ((d : ℝ) * θ j) * Real.cos ((d : ℝ) * θ m) := by
        intro j _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => (Finset.mul_sum _ _ _).symm)
      rw [Finset.sum_congr rfl hsw]
      calc ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range M,
              (c j * c m) * ∑ d ∈ D, Real.cos ((d : ℝ) * θ j) * Real.cos ((d : ℝ) * θ m)
          = ∑ j ∈ Finset.range M, ∑ m ∈ Finset.range M,
              (c j * c m) * (if j = m then (L : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun m hm => ?_))
            rw [Finset.mem_range] at hj hm
            rw [sum_Icc_cos_halfint_orth L M hL hML j m hj hm]
        _ = ∑ j ∈ Finset.range M, (c j * c j) * (L : ℝ) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [mul_ite, mul_zero, Finset.sum_ite_eq, hj, ↓reduceIte]
        _ = (1 / (L : ℝ)) * ∑ j ∈ Finset.range M, cotVal j ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            dsimp only [c]; field_simp
    rw [hconst, hlin, hquad]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D g H
  have h1_le_sq : (1 : ℝ) ≤ (∑ d ∈ D, g d * H d) ^ 2 := by nlinarith
  rw [hH_sq] at hcs
  exact h1_le_sq.trans hcs

private lemma m20_cot_series_bound :
    (2525 : ℝ) / 10000 <
      (16 / Real.pi ^ 2) * ∑ j ∈ Finset.range 20, (1 : ℝ) / ((4 * j + 3 : ℕ) : ℝ) ^ 2 := by
  have hpi_lt : Real.pi < (31416 : ℝ) / 10000 := by
    have := Real.pi_lt_d4
    linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hpi_sq : Real.pi ^ 2 < ((31416 : ℝ) / 10000) ^ 2 := by nlinarith
  have hsum_val : (15578 : ℝ) / 100000 <
      ∑ j ∈ Finset.range 20, (1 : ℝ) / ((4 * j + 3 : ℕ) : ℝ) ^ 2 := by
    norm_num [Finset.sum_range_succ]
  have hinv : (16 : ℝ) / ((31416 : ℝ) / 10000) ^ 2 < 16 / Real.pi ^ 2 :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) hpi_sq
  have hnum : (2525 : ℝ) / 10000 < (16 / ((31416 : ℝ) / 10000) ^ 2) * (15578 / 100000) := by
    norm_num
  have hmul : (16 / ((31416 : ℝ) / 10000) ^ 2) * (15578 / 100000) <
      (16 / Real.pi ^ 2) * ∑ j ∈ Finset.range 20, (1 : ℝ) / ((4 * j + 3 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  linarith

private lemma cot_sq_ge_inv_sq_sub_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    1 / x ^ 2 - 1 ≤ (Real.cos x / Real.sin x) ^ 2 := by
  have hsin_pos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith [Real.pi_pos])
  have hsin_le : Real.sin x ≤ x := (Real.sin_lt hx0).le
  have hsq : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by linarith [Real.sin_sq_add_cos_sq x]
  rw [div_pow, hsq, sub_div, div_self (by positivity : Real.sin x ^ 2 ≠ 0)]
  have hsin_sq : Real.sin x ^ 2 ≤ x ^ 2 := by nlinarith
  have hinv : 1 / x ^ 2 ≤ 1 / Real.sin x ^ 2 := one_div_le_one_div_of_le (by positivity) hsin_sq
  linarith

/-- Fast 1-variable box-convolution collapse lemma:
`∑ n ∈ range (N + W), #{a ∈ A | a ≤ n < a + W} * F n = ∑ a ∈ A, ∑ x ∈ range W, F (a + x)`. -/
private lemma sum_range_mul_box {N W : ℕ} (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N)
    (F : ℕ → ℝ) :
    ∑ n ∈ Finset.range (N + W),
      ((A.filter (fun a => a ≤ n ∧ n < a + W)).card : ℝ) * F n =
    ∑ a ∈ A, ∑ x ∈ Finset.range W, F (a + x) := by
  calc ∑ n ∈ Finset.range (N + W),
          ((A.filter (fun a => a ≤ n ∧ n < a + W)).card : ℝ) * F n
      = ∑ n ∈ Finset.range (N + W), ∑ a ∈ A,
          if a ≤ n ∧ n < a + W then F n else 0 := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => by split_ifs <;> simp)
    _ = ∑ a ∈ A, ∑ n ∈ Finset.range (N + W), if a ≤ n ∧ n < a + W then F n else 0 :=
        Finset.sum_comm
    _ = ∑ a ∈ A, ∑ x ∈ Finset.range W, F (a + x) := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        have ha_le : a ≤ N := (Finset.mem_Icc.mp (hAsub ha)).2
        rw [← Finset.sum_filter]
        have hf : (Finset.range (N + W)).filter (fun n => a ≤ n ∧ n < a + W) = Finset.Ico a (a + W) := by
          ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
        rw [hf]
        refine Finset.sum_bij (fun n _ => n - a) ?_ ?_ ?_ ?_
        · intro n hn; rw [Finset.mem_Ico] at hn; rw [Finset.mem_range]; omega
        · intro n₁ h1 n₂ h2 heq; rw [Finset.mem_Ico] at h1 h2; omega
        · intro x hx; rw [Finset.mem_range] at hx
          refine ⟨a + x, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro n hn; rw [Finset.mem_Ico] at hn; congr 1; omega

/-- Fast autocorrelation-energy identity:
`∑ d ∈ Icc (-(L-1)) (L-1), (∑ n₁, ∑ n₂, [n₁ - n₂ = d] g n₁ * g n₂)^2 = ∑_{n₁-n₂ = m₁-m₂} g n₁ g n₂ g m₁ g m₂`. -/
private lemma sum_autocorr_sq_eq_four_sum (L : ℕ) (g : ℕ → ℝ) :
    ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
      (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L,
        if (n₁ : ℤ) - (n₂ : ℤ) = d then g n₁ * g n₂ else 0) ^ 2 =
    ∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L,
      ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
        if (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then g n₁ * g n₂ * g m₁ * g m₂ else 0 := by
  let D : Finset ℤ := Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ)
  have hsq : ∀ d ∈ D,
      (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L,
        if (n₁ : ℤ) - (n₂ : ℤ) = d then g n₁ * g n₂ else 0) ^ 2 =
      ∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L,
        ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
          if (n₁ : ℤ) - (n₂ : ℤ) = d ∧ (m₁ : ℤ) - (m₂ : ℤ) = d
          then g n₁ * g n₂ * g m₁ * g m₂ else 0 := by
    intro d _
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun n₁ _ => ?_)
    calc ∑ m₁ ∈ Finset.range L,
            (∑ n₂ ∈ Finset.range L, if (n₁ : ℤ) - (n₂ : ℤ) = d then g n₁ * g n₂ else 0) *
            (∑ m₂ ∈ Finset.range L, if (m₁ : ℤ) - (m₂ : ℤ) = d then g m₁ * g m₂ else 0)
        = ∑ m₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            if (n₁ : ℤ) - (n₂ : ℤ) = d ∧ (m₁ : ℤ) - (m₂ : ℤ) = d
            then g n₁ * g n₂ * g m₁ * g m₂ else 0 := by
          refine Finset.sum_congr rfl (fun m₁ _ => ?_)
          rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun n₂ _ => Finset.sum_congr rfl (fun m₂ _ => ?_))
          split_ifs <;> simp_all [mul_assoc]
      _ = ∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            if (n₁ : ℤ) - (n₂ : ℤ) = d ∧ (m₁ : ℤ) - (m₂ : ℤ) = d
            then g n₁ * g n₂ * g m₁ * g m₂ else 0 := Finset.sum_comm
  rw [Finset.sum_congr rfl hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n₁ hn₁ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun n₂ hn₂ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m₂ _ => ?_)
  have hmemD : (n₁ : ℤ) - (n₂ : ℤ) ∈ D := by
    rw [Finset.mem_range] at hn₁ hn₂
    simp only [D, Finset.mem_Icc]; omega
  by_cases heq : (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ)
  · rw [if_pos heq]
    have hcongr : ∀ d ∈ D,
        (if (n₁ : ℤ) - (n₂ : ℤ) = d ∧ (m₁ : ℤ) - (m₂ : ℤ) = d
         then g n₁ * g n₂ * g m₁ * g m₂ else 0) =
        (if (n₁ : ℤ) - (n₂ : ℤ) = d then g n₁ * g n₂ * g m₁ * g m₂ else 0) := by
      intro d _; simp [heq]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq, if_pos hmemD]
  · rw [if_neg heq]
    apply Finset.sum_eq_zero
    intro d _
    split_ifs with h
    · exact absurd (h.1.trans h.2.symm) heq
    · rfl

/-- Key `B_3` box-smoothing energy inequality (pure finite sums, zero integrals!):
for any `B_3` set `A ⊆ Icc 1 N` (`A.Nonempty`) and box width `W ≥ 1`, let `L = N + W` and
`f(n) = (1 / (|A| * W)) * #{a ∈ A | a ≤ n < a + W}` on `range L`. Then:
`(|A| : ℝ)^4 * ∑ d ∈ Icc (-(L-1)) (L-1), (f * f~)(d)^2 ≤ 2 * |A| + 2 * |A|^3 / W`. -/
private lemma b3_box_smoothing_energy {N W : ℕ} (_hN : 1 ≤ N) (hW : 1 ≤ W)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 N) (hAne : A.Nonempty)
    (hB3 : ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = 3 → m₂.card = 3 →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂) :
    let L := N + W
    let f : ℕ → ℝ := fun n =>
      ((A.filter (fun a => a ≤ n ∧ n < a + W)).card : ℝ) / ((A.card : ℝ) * (W : ℝ))
    (∑ n ∈ Finset.range L, f n = 1) ∧
    (A.card : ℝ) ^ 4 *
      (∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
        (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
          if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) ^ 2) ≤
      2 * (A.card : ℝ) + 2 * (A.card : ℝ) ^ 3 / (W : ℝ) := by
  intro L f
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hAne.card_pos
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hAWpos : (0 : ℝ) < (A.card : ℝ) * (W : ℝ) := mul_pos hApos hWpos
  have hf_sum : ∑ n ∈ Finset.range L, f n = 1 := by
    dsimp only [f]
    rw [← Finset.sum_div, div_eq_one_iff_eq hAWpos.ne']
    have h1 := sum_range_mul_box (W := W) A hAsub (fun _ => (1 : ℝ))
    simpa [L, Finset.sum_const, nsmul_eq_mul] using h1
  refine ⟨hf_sum, ?_⟩
  let ϕ : ℤ → ℝ := fun u =>
    (∑ x₁ ∈ Finset.range W, ∑ y₁ ∈ Finset.range W, ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
      if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) / (W : ℝ) ^ 4
  have hϕ_nonneg : ∀ u : ℤ, 0 ≤ ϕ u := by
    intro u; dsimp only [ϕ]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)))))
      (by positivity)
  let U : Finset ℤ := Finset.Icc (-(2 * (W : ℤ))) (2 * (W : ℤ))
  have hϕ_supp : ∀ u : ℤ, u ∉ U → ϕ u = 0 := by
    intro u hu
    dsimp only [ϕ]
    have h0 : (∑ x₁ ∈ Finset.range W, ∑ y₁ ∈ Finset.range W, ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
        if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero; intro x₁ hx₁
      apply Finset.sum_eq_zero; intro y₁ hy₁
      apply Finset.sum_eq_zero; intro y₂ hy₂
      apply Finset.sum_eq_zero; intro x₂ hx₂
      rw [Finset.mem_range] at hx₁ hy₁ hy₂ hx₂
      rw [if_neg]; intro heq
      apply hu; simp only [U, Finset.mem_Icc]; omega
    rw [h0, zero_div]
  have hϕ_sum : ∑ u ∈ U, ϕ u = 1 := by
    dsimp only [ϕ]
    rw [← Finset.sum_div, div_eq_one_iff_eq (by positivity : (W : ℝ) ^ 4 ≠ 0)]
    rw [Finset.sum_comm]
    have hsw1 : ∀ x₁ ∈ Finset.range W,
        (∑ u ∈ U, ∑ y₁ ∈ Finset.range W, ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
          if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) =
        (W : ℝ) ^ 3 := by
      intro x₁ hx₁
      rw [Finset.sum_comm]
      have hsw2 : ∀ y₁ ∈ Finset.range W,
          (∑ u ∈ U, ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
            if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) =
          (W : ℝ) ^ 2 := by
        intro y₁ hy₁
        rw [Finset.sum_comm]
        have hsw3 : ∀ y₂ ∈ Finset.range W,
            (∑ u ∈ U, ∑ x₂ ∈ Finset.range W,
              if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) =
            (W : ℝ) := by
          intro y₂ hy₂
          rw [Finset.sum_comm]
          have hsw4 : ∀ x₂ ∈ Finset.range W,
              (∑ u ∈ U, if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) = 1 := by
            intro x₂ hx₂
            rw [Finset.mem_range] at hx₁ hy₁ hy₂ hx₂
            rw [Finset.sum_ite_eq, if_pos (by simp only [U, Finset.mem_Icc]; omega)]
          rw [Finset.sum_congr rfl hsw4, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [Finset.sum_congr rfl hsw3, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      rw [Finset.sum_congr rfl hsw2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [Finset.sum_congr rfl hsw1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hϕ_le : ∀ u : ℤ, ϕ u ≤ 1 / (W : ℝ) := by
    intro u
    dsimp only [ϕ]
    rw [div_le_div_iff₀ (by positivity) hWpos, one_mul]
    have hinner : ∀ x₁ ∈ Finset.range W, ∀ y₁ ∈ Finset.range W, ∀ y₂ ∈ Finset.range W,
        (∑ x₂ ∈ Finset.range W, if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) ≤ 1 := by
      intro x₁ _ y₁ _ y₂ _
      by_cases hex : ∃ x₂ ∈ Finset.range W, (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u
      · rcases hex with ⟨x₀, hx₀, heq₀⟩
        have hcongr : ∀ x₂ ∈ Finset.range W,
            (if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) =
            (if x₀ = x₂ then (1 : ℝ) else 0) := by
          intro x₂ _; congr 1; exact propext (by omega)
        rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq, if_pos hx₀]
      · push Not at hex
        have h0 : ∑ x₂ ∈ Finset.range W, (if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) = 0 :=
          Finset.sum_eq_zero (fun x₂ hx₂ => if_neg (hex x₂ hx₂))
        linarith
    have hsum_le : (∑ x₁ ∈ Finset.range W, ∑ y₁ ∈ Finset.range W, ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
        if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) = u then (1 : ℝ) else 0) ≤ (W : ℝ) ^ 3 := by
      calc _ ≤ ∑ _x₁ ∈ Finset.range W, ∑ _y₁ ∈ Finset.range W, ∑ _y₂ ∈ Finset.range W, (1 : ℝ) :=
            Finset.sum_le_sum (fun x₁ hx₁ => Finset.sum_le_sum (fun y₁ hy₁ =>
              Finset.sum_le_sum (fun y₂ hy₂ => hinner x₁ hx₁ y₁ hy₁ y₂ hy₂)))
        _ = (W : ℝ) ^ 3 := by simp [Finset.sum_const, nsmul_eq_mul]; ring
    nlinarith [pow_nonneg hWpos.le 3]
  -- 3. Collapse |A|^4 * ∑ d, (f * f~)(d)^2 using sum_autocorr_sq_eq_four_sum + 4 calls to sum_range_mul_box!
  have hmain_id :
      (A.card : ℝ) ^ 4 *
        (∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
          (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L,
            if (n₁ : ℤ) - (n₂ : ℤ) = d then f n₁ * f n₂ else 0) ^ 2) =
      ∑ a₁ ∈ A, ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₂ ∈ A,
        ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) := by
    let cA : ℕ → ℝ := fun n => ((A.filter (fun a => a ≤ n ∧ n < a + W)).card : ℝ)
    rw [sum_autocorr_sq_eq_four_sum L f]
    have hfactor :
        (A.card : ℝ) ^ 4 *
          (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            if (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then f n₁ * f n₂ * f m₁ * f m₂ else 0) =
        (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
          cA n₁ * (cA n₂ * (cA m₁ * (cA m₂ *
            if (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0)))) / (W : ℝ) ^ 4 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun n₁ _ => ?_)
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun n₂ _ => ?_)
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun m₁ _ => ?_)
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun m₂ _ => ?_)
      dsimp only [f, cA]
      split_ifs
      · field_simp
      · ring
    rw [hfactor]
    -- Collapse n₁, then n₂, then m₁, then m₂ using sum_range_mul_box!
    have hcol4 :
        (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
          cA n₁ * (cA n₂ * (cA m₁ * (cA m₂ *
            if (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0)))) =
        ∑ a₁ ∈ A, ∑ x₁ ∈ Finset.range W, ∑ b₁ ∈ A, ∑ y₁ ∈ Finset.range W,
          ∑ b₂ ∈ A, ∑ y₂ ∈ Finset.range W, ∑ a₂ ∈ A, ∑ x₂ ∈ Finset.range W,
            if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = ((b₂ + y₂ : ℕ) : ℤ) - ((a₂ + x₂ : ℕ) : ℤ)
            then (1 : ℝ) else 0 := by
      -- Pull cA n₁ out of inner sums and apply sum_range_mul_box
      have hs1 : (∑ n₁ ∈ Finset.range L, ∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            cA n₁ * (cA n₂ * (cA m₁ * (cA m₂ *
              if (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0)))) =
          ∑ n₁ ∈ Finset.range L, cA n₁ * (∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            cA n₂ * (cA m₁ * (cA m₂ *
              if (n₁ : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0))) :=
        Finset.sum_congr rfl (fun n₁ _ => by simp_rw [← Finset.mul_sum])
      rw [hs1, sum_range_mul_box A hAsub]
      refine Finset.sum_congr rfl (fun a₁ _ => Finset.sum_congr rfl (fun x₁ _ => ?_))
      have hs2 : (∑ n₂ ∈ Finset.range L, ∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            cA n₂ * (cA m₁ * (cA m₂ *
              if ((a₁ + x₁ : ℕ) : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0))) =
          ∑ n₂ ∈ Finset.range L, cA n₂ * (∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            cA m₁ * (cA m₂ *
              if ((a₁ + x₁ : ℕ) : ℤ) - (n₂ : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl (fun n₂ _ => by simp_rw [← Finset.mul_sum])
      rw [hs2, sum_range_mul_box A hAsub]
      refine Finset.sum_congr rfl (fun b₁ _ => Finset.sum_congr rfl (fun y₁ _ => ?_))
      have hs3 : (∑ m₁ ∈ Finset.range L, ∑ m₂ ∈ Finset.range L,
            cA m₁ * (cA m₂ *
              if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0)) =
          ∑ m₁ ∈ Finset.range L, cA m₁ * (∑ m₂ ∈ Finset.range L,
            cA m₂ * if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = (m₁ : ℤ) - (m₂ : ℤ) then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl (fun m₁ _ => by rw [← Finset.mul_sum])
      rw [hs3, sum_range_mul_box A hAsub]
      refine Finset.sum_congr rfl (fun b₂ _ => Finset.sum_congr rfl (fun y₂ _ => ?_))
      exact sum_range_mul_box A hAsub _
    rw [hcol4]
    -- Reorder sums cleanly: move x₁, y₁, y₂ inside b₁, b₂, a₂
    have hreord :
        (∑ a₁ ∈ A, ∑ x₁ ∈ Finset.range W, ∑ b₁ ∈ A, ∑ y₁ ∈ Finset.range W,
          ∑ b₂ ∈ A, ∑ y₂ ∈ Finset.range W, ∑ a₂ ∈ A, ∑ x₂ ∈ Finset.range W,
            if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = ((b₂ + y₂ : ℕ) : ℤ) - ((a₂ + x₂ : ℕ) : ℤ)
            then (1 : ℝ) else 0) =
        ∑ a₁ ∈ A, ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₂ ∈ A,
          ∑ x₁ ∈ Finset.range W, ∑ y₁ ∈ Finset.range W, ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
            if (x₁ : ℤ) + (x₂ : ℤ) - (y₁ : ℤ) - (y₂ : ℤ) =
               (b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)
            then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl (fun a₁ _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b₁ _ => ?_)
      trans ∑ x₁ ∈ Finset.range W, ∑ b₂ ∈ A, ∑ y₁ ∈ Finset.range W,
          ∑ y₂ ∈ Finset.range W, ∑ a₂ ∈ A, ∑ x₂ ∈ Finset.range W,
            if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = ((b₂ + y₂ : ℕ) : ℤ) - ((a₂ + x₂ : ℕ) : ℤ)
            then (1 : ℝ) else 0
      · refine Finset.sum_congr rfl (fun x₁ _ => Finset.sum_comm)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b₂ _ => ?_)
      trans ∑ x₁ ∈ Finset.range W, ∑ y₁ ∈ Finset.range W, ∑ a₂ ∈ A,
          ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
            if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = ((b₂ + y₂ : ℕ) : ℤ) - ((a₂ + x₂ : ℕ) : ℤ)
            then (1 : ℝ) else 0
      · refine Finset.sum_congr rfl (fun x₁ _ => Finset.sum_congr rfl (fun y₁ _ => Finset.sum_comm))
      trans ∑ x₁ ∈ Finset.range W, ∑ a₂ ∈ A, ∑ y₁ ∈ Finset.range W,
          ∑ y₂ ∈ Finset.range W, ∑ x₂ ∈ Finset.range W,
            if ((a₁ + x₁ : ℕ) : ℤ) - ((b₁ + y₁ : ℕ) : ℤ) = ((b₂ + y₂ : ℕ) : ℤ) - ((a₂ + x₂ : ℕ) : ℤ)
            then (1 : ℝ) else 0
      · refine Finset.sum_congr rfl (fun x₁ _ => Finset.sum_comm)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a₂ _ => Finset.sum_congr rfl (fun x₁ _ =>
        Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ =>
          Finset.sum_congr rfl (fun x₂ _ => ?_)))))
      congr 1; exact propext (by omega)
    rw [hreord, Finset.sum_div]
    refine Finset.sum_congr rfl (fun a₁ _ => ?_)
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun b₁ _ => ?_)
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun b₂ _ => ?_)
    rw [Finset.sum_div]
  rw [hmain_id]
  have hsplit :
      ∑ a₁ ∈ A, ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₂ ∈ A, ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) =
      (∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
        if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) +
      (∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
        if ¬(a₁ ≠ b₁ ∧ a₁ ≠ b₂) then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) := by
    have hreord :
        ∑ a₁ ∈ A, ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₂ ∈ A, ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) =
        ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A, ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b₁ _ => Finset.sum_comm)
    rw [hreord]
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b₁ _ => Finset.sum_congr rfl (fun b₂ _ =>
      Finset.sum_congr rfl (fun a₁ _ => Finset.sum_congr rfl (fun a₂ _ => ?_))))
    split_ifs <;> ring
  rw [hsplit]
  let Z₀ : Finset ℤ := Finset.Icc (2 - (N : ℤ)) (2 * (N : ℤ) - 1)
  have hpart1 :
      ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
        (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) ≤
      2 * (A.card : ℝ) := by
    have hsw : ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
          (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) =
        ∑ a₂ ∈ A, ∑ z ∈ Z₀,
          ((((A ×ˢ A) ×ˢ A).filter (fun t =>
            t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)).card : ℝ) *
          ϕ (z - (a₂ : ℤ)) := by
      have h1 : ∀ a₂ ∈ A,
          ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A,
            (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) =
          ∑ z ∈ Z₀,
            ((((A ×ˢ A) ×ˢ A).filter (fun t =>
              t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)).card : ℝ) *
            ϕ (z - (a₂ : ℤ)) := by
        intro a₂ _
        calc ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A,
                (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0)
            = ∑ t ∈ (A ×ˢ A) ×ˢ A,
                if t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 then ϕ ((t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) - (a₂ : ℤ)) else 0 := by
              rw [Finset.sum_product, Finset.sum_product]
          _ = ∑ t ∈ (A ×ˢ A) ×ˢ A, ∑ z ∈ Z₀,
                if t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z
                then ϕ (z - (a₂ : ℤ)) else 0 := by
              refine Finset.sum_congr rfl (fun ⟨⟨b₁, b₂⟩, a₁⟩ ht => ?_)
              simp only [Finset.mem_product] at ht
              have hb₁ := Finset.mem_Icc.mp (hAsub ht.1.1)
              have hb₂ := Finset.mem_Icc.mp (hAsub ht.1.2)
              have ha₁ := Finset.mem_Icc.mp (hAsub ht.2)
              have hz_mem : (b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) ∈ Z₀ := by
                simp only [Z₀, Finset.mem_Icc]; omega
              by_cases hne : a₁ ≠ b₁ ∧ a₁ ≠ b₂
              · rw [if_pos hne]
                have hite : ∀ z ∈ Z₀,
                    (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ (b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) = z then ϕ (z - (a₂ : ℤ)) else 0) =
                    (if (b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) = z then ϕ (z - (a₂ : ℤ)) else 0) :=
                  fun z _ => by simp [hne.1, hne.2]
                rw [Finset.sum_congr rfl hite, Finset.sum_ite_eq, if_pos hz_mem]
              · rw [if_neg hne]
                symm; apply Finset.sum_eq_zero; intro z _
                have hnot : ¬ (a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ (b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) = z) := by tauto
                rw [if_neg hnot]
          _ = ∑ z ∈ Z₀, ∑ t ∈ (A ×ˢ A) ×ˢ A,
                if t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z
                then ϕ (z - (a₂ : ℤ)) else 0 := Finset.sum_comm
          _ = ∑ z ∈ Z₀,
                ((((A ×ˢ A) ×ˢ A).filter (fun t =>
                  t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)).card : ℝ) *
                ϕ (z - (a₂ : ℤ)) := by
              refine Finset.sum_congr rfl (fun z _ => ?_)
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      calc ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
              (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0)
          = ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₂ ∈ A, ∑ a₁ ∈ A,
              (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) :=
            Finset.sum_congr rfl (fun b₁ _ => Finset.sum_congr rfl (fun b₂ _ => Finset.sum_comm))
        _ = ∑ b₁ ∈ A, ∑ a₂ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A,
              (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) :=
            Finset.sum_congr rfl (fun b₁ _ => Finset.sum_comm)
        _ = ∑ a₂ ∈ A, ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A,
              (if a₁ ≠ b₁ ∧ a₁ ≠ b₂ then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) :=
            Finset.sum_comm
        _ = _ := Finset.sum_congr rfl h1
    rw [hsw]
    calc ∑ a₂ ∈ A, ∑ z ∈ Z₀,
            ((((A ×ˢ A) ×ˢ A).filter (fun t =>
              t.2 ≠ t.1.1 ∧ t.2 ≠ t.1.2 ∧ (t.1.1 : ℤ) + (t.1.2 : ℤ) - (t.2 : ℤ) = z)).card : ℝ) *
            ϕ (z - (a₂ : ℤ))
        ≤ ∑ a₂ ∈ A, ∑ z ∈ Z₀, (2 : ℝ) * ϕ (z - (a₂ : ℤ)) := by
          refine Finset.sum_le_sum (fun a₂ _ => Finset.sum_le_sum (fun z _ => ?_))
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast b3_nontriv_rep_le_two hB3 z) (hϕ_nonneg _)
      _ = ∑ a₂ ∈ A, 2 * ∑ z ∈ Z₀, ϕ (z - (a₂ : ℤ)) := by
          refine Finset.sum_congr rfl (fun a₂ _ => (Finset.mul_sum _ _ _).symm)
      _ ≤ ∑ _a₂ ∈ A, 2 * 1 := by
          refine Finset.sum_le_sum (fun a₂ _ => mul_le_mul_of_nonneg_left ?_ (by norm_num))
          have hsub : ∑ z ∈ Z₀, ϕ (z - (a₂ : ℤ)) =
              ∑ z ∈ Z₀.filter (fun z => z - (a₂ : ℤ) ∈ U), ϕ (z - (a₂ : ℤ)) := by
            symm
            refine Finset.sum_subset (Finset.filter_subset _ _) (fun z hz hnot => ?_)
            have hnotU : z - (a₂ : ℤ) ∉ U := fun h => hnot (Finset.mem_filter.mpr ⟨hz, h⟩)
            exact hϕ_supp _ hnotU
          rw [hsub]
          calc ∑ z ∈ Z₀.filter (fun z => z - (a₂ : ℤ) ∈ U), ϕ (z - (a₂ : ℤ))
              = ∑ u ∈ (Z₀.filter (fun z => z - (a₂ : ℤ) ∈ U)).image (fun z => z - (a₂ : ℤ)), ϕ u := by
                rw [Finset.sum_image]
                intro x _ y _ hxy; dsimp only at hxy; omega
            _ ≤ ∑ u ∈ U, ϕ u := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => hϕ_nonneg u)
                intro u hu
                rcases Finset.mem_image.mp hu with ⟨z, hz, rfl⟩
                exact (Finset.mem_filter.mp hz).2
            _ = 1 := hϕ_sum
      _ = 2 * (A.card : ℝ) := by simp [mul_comm]
  have hpart2 :
      ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
        (if ¬(a₁ ≠ b₁ ∧ a₁ ≠ b₂) then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0) ≤
      2 * (A.card : ℝ) ^ 3 / (W : ℝ) := by
    calc ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ a₂ ∈ A,
            (if ¬(a₁ ≠ b₁ ∧ a₁ ≠ b₂) then ϕ ((b₁ : ℤ) + (b₂ : ℤ) - (a₁ : ℤ) - (a₂ : ℤ)) else 0)
        ≤ ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ a₁ ∈ A, ∑ _a₂ ∈ A,
            (if a₁ = b₁ ∨ a₁ = b₂ then 1 / (W : ℝ) else 0) := by
          refine Finset.sum_le_sum (fun b₁ _ => Finset.sum_le_sum (fun b₂ _ =>
            Finset.sum_le_sum (fun a₁ _ => Finset.sum_le_sum (fun a₂ _ => ?_))))
          by_cases h : a₁ = b₁ ∨ a₁ = b₂
          · have h' : ¬(a₁ ≠ b₁ ∧ a₁ ≠ b₂) := by tauto
            rw [if_pos h', if_pos h]
            exact hϕ_le _
          · have h' : a₁ ≠ b₁ ∧ a₁ ≠ b₂ := by tauto
            simp [h']
      _ ≤ ∑ b₁ ∈ A, ∑ b₂ ∈ A, ∑ _a₂ ∈ A, (2 : ℝ) * (1 / (W : ℝ)) := by
          refine Finset.sum_le_sum (fun b₁ _ => Finset.sum_le_sum (fun b₂ _ => ?_))
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum (fun a₂ _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hsub : A.filter (fun a₁ => a₁ = b₁ ∨ a₁ = b₂) ⊆ ({b₁, b₂} : Finset ℕ) := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
            exact hx.2
          exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two
      _ = 2 * (A.card : ℝ) ^ 3 / (W : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

/-- **SHARPENED `B_3` Upper Bound Strictly Beating Ben Green's (2001) `(7/2)^{1/3}` Record**:
for every `ε > 0`, eventually for all `N`, EVERY `B_3` set `A ⊆ {1, …, N}` satisfies
`(|A| : ℝ) ≤ ((699 / 200 : ℝ) ^ (1 / 3) + ε) * N ^ (1 / 3)`
(note `699 / 200 = 3.495 < 3.5 = 7 / 2`, so `(699/200)^{1/3} ≈ 1.51757 < 1.51829 ≈ (7/2)^{1/3}`).
Proved purely elementarily with `M = 20` exact discrete orthogonal cosines (`0` integrals, `0` custom defs!). -/
theorem ppl088_b3_upper_bound_beats_green :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (∀ m₁ m₂ : Multiset ℕ,
          m₁.card = 3 → m₂.card = 3 →
          (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
          m₁.sum = m₂.sum → m₁ = m₂) →
        (A.card : ℝ) ≤ (((699 / 200 : ℝ) ^ ((1 : ℝ) / 3)) + ε) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  intro ε hε
  set C₀ : ℝ := (699 / 200 : ℝ) ^ ((1 : ℝ) / 3) with hC0_def
  have hC0_pos : 0 < C₀ := Real.rpow_pos_of_pos (by norm_num) _
  have hC0_cube : C₀ ^ 3 = 699 / 200 := by
    rw [hC0_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 699 / 200)]
    norm_num
  have hgap : (699 / 200 : ℝ) < (C₀ + ε) ^ 3 := by
    have : C₀ ^ 3 < (C₀ + ε) ^ 3 := pow_lt_pow_left₀ (by linarith) hC0_pos.le (by norm_num)
    linarith
  set η : ℝ := ((C₀ + ε) ^ 3 / (699 / 200) - 1) / 4 with hη_def
  have hη_pos : 0 < η := by
    have : 1 < (C₀ + ε) ^ 3 / (699 / 200) := (one_lt_div (by norm_num)).mpr hgap
    linarith
  set δ : ℝ := min η (1 / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hη_pos (by norm_num)
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_le_η : δ ≤ η := min_le_left _ _
  have hprod_le : (699 / 200 : ℝ) * (1 + δ) * (1 + δ) ≤ (C₀ + ε) ^ 3 := by
    have h1 : (1 + δ) * (1 + δ) ≤ 1 + 4 * η := by nlinarith
    have h2 : (699 / 200 : ℝ) * (1 + 4 * η) = (C₀ + ε) ^ 3 := by
      dsimp only [η]; field_simp; ring
    nlinarith
  let K : ℕ := Nat.ceil (2 / δ) + 1
  have hK_pos : 1 ≤ K := Nat.succ_le_succ (Nat.zero_le _)
  have hK_ge : 2 / δ ≤ (K : ℝ) := by
    have := Nat.le_ceil (2 / δ)
    have : ((Nat.ceil (2 / δ) : ℕ) : ℝ) ≤ (K : ℝ) := by simp [K]
    linarith
  set s20 : ℝ := ∑ j ∈ Finset.range 20, (1 : ℝ) / ((4 * j + 3 : ℕ) : ℝ) ^ 2
  have hgap20 : 0 < (16 / Real.pi ^ 2) * s20 - 2525 / 10000 := sub_pos.mpr m20_cot_series_bound
  let N₁ : ℕ := max 100 (Nat.ceil (20 / ((16 / Real.pi ^ 2) * s20 - 2525 / 10000)) + 1)
  let N₂ : ℕ := max (Nat.ceil (2 / δ) + 1) (Nat.ceil ((20 * (K : ℝ) / δ) ^ 3) + 100)
  rw [Filter.eventually_atTop]
  refine ⟨max N₁ N₂, fun N hN A hAsub hB3 => ?_⟩
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans hN
  have hN_ge100 : 100 ≤ N := (le_max_left _ _).trans hN1
  have hN_ge1 : 1 ≤ N := by omega
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_ge1
  by_cases hAne : A.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hAne, Finset.card_empty, Nat.cast_zero]
    positivity
  by_cases hA_small : A.card ≤ 3
  · have h3 : (A.card : ℝ) ≤ 3 := by exact_mod_cast hA_small
    have hN_cbrt : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
      have h64 : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 64 ≤ N)
      have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 64) h64 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h64_cbrt : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
        rw [show (64 : ℝ) = 4 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith
    have hC0_ge1 : 1 ≤ C₀ := Real.one_le_rpow (by norm_num) (by norm_num)
    nlinarith
  push Not at hA_small
  let W : ℕ := N / K + 1
  have hW_ge1 : 1 ≤ W := Nat.succ_le_succ (Nat.zero_le _)
  let L : ℕ := N + W
  have hL_ge40 : 40 ≤ L := by omega
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hN_le_L : (N : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Nat.le_add_right N W)
  have hcomb : (A.card : ℝ) ^ 4 / ((699 / 400 : ℝ) * (L : ℝ)) ≤
      2 * (A.card : ℝ) + 2 * (A.card : ℝ) ^ 3 / (W : ℝ) := by
    obtain ⟨hf_sum, henergy⟩ := b3_box_smoothing_energy hN_ge1 hW_ge1 A hAsub hAne hB3
    let f : ℕ → ℝ := fun n =>
      ((A.filter (fun a => a ≤ n ∧ n < a + W)).card : ℝ) / ((A.card : ℝ) * (W : ℝ))
    have horth := ppl088_b3_discrete_autoconvolution_orthogonal_cosine_lb L 20 (by omega) (by omega) f hf_sum
    have hden_le :
        (2 * (L : ℝ) - 1) - (1 / (L : ℝ)) * ∑ j ∈ Finset.range 20,
          (Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
           Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))) ^ 2 ≤
        (699 / 400 : ℝ) * (L : ℝ) := by
      have hsum_cot :
          (16 * (L : ℝ) ^ 2 / Real.pi ^ 2) * s20 - 20 ≤
          ∑ j ∈ Finset.range 20,
            (Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
             Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))) ^ 2 := by
        calc (16 * (L : ℝ) ^ 2 / Real.pi ^ 2) * s20 - 20
            = ∑ j ∈ Finset.range 20,
                (1 / (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) ^ 2 - 1) := by
              rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
              congr 1
              dsimp only [s20]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun j _ => ?_)
              have hne : ((4 * j + 3 : ℕ) : ℝ) ≠ 0 := by positivity
              have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
              field_simp; ring
          _ ≤ ∑ j ∈ Finset.range 20,
                (Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
                 Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))) ^ 2 := by
              refine Finset.sum_le_sum (fun j hj => ?_)
              rw [Finset.mem_range] at hj
              have hj_lt : 4 * j + 3 < 2 * L := by omega
              refine cot_sq_ge_inv_sq_sub_one (by positivity) ?_
              have hlt : ((4 * j + 3 : ℕ) : ℝ) < 2 * (L : ℝ) := by exact_mod_cast hj_lt
              rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [Real.pi_pos]
      have hdiv_cot : (16 / Real.pi ^ 2) * s20 * (L : ℝ) - 20 / (L : ℝ) ≤
          (1 / (L : ℝ)) * ∑ j ∈ Finset.range 20,
            (Real.cos (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ))) /
             Real.sin (((4 * j + 3 : ℕ) : ℝ) * Real.pi / (4 * (L : ℝ)))) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hsum_cot (by positivity : (0 : ℝ) ≤ 1 / (L : ℝ))
        have heq : (1 / (L : ℝ)) * ((16 * (L : ℝ) ^ 2 / Real.pi ^ 2) * s20 - 20) =
            (16 / Real.pi ^ 2) * s20 * (L : ℝ) - 20 / (L : ℝ) := by field_simp
        linarith
      have htail : 20 / (L : ℝ) ≤ ((16 / Real.pi ^ 2) * s20 - 2525 / 10000) * (L : ℝ) := by
        have hL_ge : 20 / ((16 / Real.pi ^ 2) * s20 - 2525 / 10000) ≤ (L : ℝ) := by
          have h1 : (Nat.ceil (20 / ((16 / Real.pi ^ 2) * s20 - 2525 / 10000)) : ℝ) ≤ (N : ℝ) := by
            have : Nat.ceil (20 / ((16 / Real.pi ^ 2) * s20 - 2525 / 10000)) ≤ N :=
              le_trans (Nat.le_succ _) ((le_max_right _ _).trans hN1)
            exact_mod_cast this
          linarith [Nat.le_ceil (20 / ((16 / Real.pi ^ 2) * s20 - 2525 / 10000))]
        have hL_ge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
        rw [div_le_iff₀ hL_pos]
        have h2 := (div_le_iff₀ hgap20).mp hL_ge
        nlinarith
      linarith
    have hauto_lb : 1 / ((699 / 400 : ℝ) * (L : ℝ)) ≤
        ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
          (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) ^ 2 := by
      have hsq_nn : 0 ≤ ∑ d ∈ Finset.Icc (-(L - 1 : ℤ)) (L - 1 : ℤ),
          (∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
            if (a : ℤ) - (b : ℤ) = d then f a * f b else 0) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      exact (div_le_iff₀ (by positivity)).mpr (horth.trans (mul_le_mul_of_nonneg_left hden_le hsq_nn))
    have h1 := mul_le_mul_of_nonneg_left hauto_lb (by positivity : (0 : ℝ) ≤ (A.card : ℝ) ^ 4)
    rw [mul_one_div] at h1
    exact h1.trans henergy
  -- Bound |A|^2 / W ≤ δ using ppl088_b3_difference_upper_bound
  have hdiff_bd := ppl088_b3_difference_upper_bound N hN_ge1 A hAsub hB3
  have hA_cube_le : (A.card : ℝ) ^ 3 ≤ 48 * (N : ℝ) := by
    have h1 : A.card ≤ 2 * (A.card - 2) := by omega
    have h2 : A.card ≤ 2 * (A.card - 1) := by omega
    have h3 : A.card ^ 3 ≤ 4 * (A.card * (A.card - 1) * (A.card - 2)) := by
      calc A.card ^ 3 = A.card * A.card * A.card := by ring
        _ ≤ A.card * (2 * (A.card - 1)) * (2 * (A.card - 2)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h1
        _ = 4 * (A.card * (A.card - 1) * (A.card - 2)) := by ring
    have h4 : A.card ^ 3 ≤ 24 * N := by omega
    have h5 : ((A.card ^ 3 : ℕ) : ℝ) ≤ ((24 * N : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5
    linarith
  have hW_ge_NK : (N : ℝ) / (K : ℝ) ≤ (W : ℝ) := by
    have hdiv : N ≤ K * (N / K) + K := by
      have := Nat.div_add_mod N K
      have hmod := Nat.mod_lt N hK_pos
      omega
    have hW_eq : K * (N / K) + K = K * W := by dsimp only [W]; ring
    rw [hW_eq] at hdiv
    have hr : (N : ℝ) ≤ (K : ℝ) * (W : ℝ) := by exact_mod_cast hdiv
    exact (div_le_iff₀ (by exact_mod_cast hK_pos)).mpr (by linarith)
  have hA2_div_W : (A.card : ℝ) ^ 2 / (W : ℝ) ≤ δ := by
    have hN_ge_pow : (20 * (K : ℝ) / δ) ^ 3 ≤ (N : ℝ) := by
      have h1 : Nat.ceil ((20 * (K : ℝ) / δ) ^ 3) ≤ N :=
        le_trans (Nat.le_add_right _ 100) ((le_max_right _ _).trans hN2)
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hA_cube_pow : ((A.card : ℝ) ^ 2) ^ 3 ≤ (δ * ((N : ℝ) / (K : ℝ))) ^ 3 := by
      have h1 : ((A.card : ℝ) ^ 2) ^ 3 = ((A.card : ℝ) ^ 3) ^ 2 := by ring
      rw [h1]
      calc ((A.card : ℝ) ^ 3) ^ 2 ≤ (48 * (N : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) hA_cube_le 2
        _ = 2304 * (N : ℝ) ^ 2 := by ring
        _ ≤ 8000 * (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]
        _ ≤ (δ / (K : ℝ)) ^ 3 * (N : ℝ) ^ 3 := by
            have hK_pos_r : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
            have h20 : (8000 : ℝ) * (K : ℝ) ^ 3 / δ ^ 3 ≤ (N : ℝ) := by
              have : (20 * (K : ℝ) / δ) ^ 3 = 8000 * (K : ℝ) ^ 3 / δ ^ 3 := by ring
              linarith
            have hmul := mul_le_mul_of_nonneg_right h20 (by positivity : (0 : ℝ) ≤ δ ^ 3 / (K : ℝ) ^ 3 * (N : ℝ) ^ 2)
            have hlhs : 8000 * (K : ℝ) ^ 3 / δ ^ 3 * (δ ^ 3 / (K : ℝ) ^ 3 * (N : ℝ) ^ 2) = 8000 * (N : ℝ) ^ 2 := by
              field_simp
            have hrhs : (N : ℝ) * (δ ^ 3 / (K : ℝ) ^ 3 * (N : ℝ) ^ 2) = (δ / (K : ℝ)) ^ 3 * (N : ℝ) ^ 3 := by
              field_simp
            linarith
        _ = (δ * ((N : ℝ) / (K : ℝ))) ^ 3 := by ring
    have hA2_le : (A.card : ℝ) ^ 2 ≤ δ * ((N : ℝ) / (K : ℝ)) := by
      by_contra hgt
      push Not at hgt
      have := pow_lt_pow_left₀ hgt (by positivity) (by norm_num : 3 ≠ 0)
      linarith
    have hW_pos_r : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW_ge1
    rw [div_le_iff₀ hW_pos_r]
    nlinarith
  have hL_le : (L : ℝ) ≤ (1 + δ) * (N : ℝ) := by
    have hW_le : (W : ℝ) ≤ (N : ℝ) / (K : ℝ) + 1 := by
      have h1 : (N / K : ℕ) * K ≤ N := Nat.div_mul_le_self N K
      have h2 : ((N / K : ℕ) : ℝ) ≤ (N : ℝ) / (K : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hK_pos)]
        exact_mod_cast h1
      have hW_cast : (W : ℝ) = ((N / K : ℕ) : ℝ) + 1 := by simp [W]
      linarith
    have hNK_le : (N : ℝ) / (K : ℝ) ≤ (δ / 2) * (N : ℝ) := by
      have h1 : 1 / (K : ℝ) ≤ δ / 2 := by
        rw [div_le_iff₀ (by exact_mod_cast hK_pos)]
        have := (div_le_iff₀ hδ_pos).mp hK_ge
        linarith
      have hmul := mul_le_mul_of_nonneg_right h1 hN_pos.le
      linarith [show (1 / (K : ℝ)) * (N : ℝ) = (N : ℝ) / (K : ℝ) by ring]
    have h1_le : (1 : ℝ) ≤ (δ / 2) * (N : ℝ) := by
      have h1 : Nat.ceil (2 / δ) ≤ N :=
        le_trans (Nat.le_succ _) ((le_max_left _ _).trans hN2)
      have h2 : 2 / δ ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
      have := (div_le_iff₀ hδ_pos).mp h2
      linarith
    have hL_cast : (L : ℝ) = (N : ℝ) + (W : ℝ) := by simp [L]
    linarith
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hAne.card_pos
  have hA_cube_final : (A.card : ℝ) ^ 3 ≤ ((C₀ + ε) * (N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
    have hmul := (div_le_iff₀ (by positivity : (0 : ℝ) < (699 / 400 : ℝ) * (L : ℝ))).mp hcomb
    have hrhs : 2 * (A.card : ℝ) + 2 * (A.card : ℝ) ^ 3 / (W : ℝ) ≤
        2 * (A.card : ℝ) * (1 + δ) := by
      have hrew : 2 * (A.card : ℝ) ^ 3 / (W : ℝ) = 2 * (A.card : ℝ) * ((A.card : ℝ) ^ 2 / (W : ℝ)) := by ring
      rw [hrew]
      nlinarith
    have h1 : (A.card : ℝ) ^ 4 ≤ (699 / 400 : ℝ) * (L : ℝ) * (2 * (A.card : ℝ) * (1 + δ)) := by
      have hmul' : (A.card : ℝ) ^ 4 ≤ (699 / 400 : ℝ) * (L : ℝ) * (2 * (A.card : ℝ) + 2 * (A.card : ℝ) ^ 3 / (W : ℝ)) := by
        linarith [hmul, show (2 * (A.card : ℝ) + 2 * (A.card : ℝ) ^ 3 / (W : ℝ)) * ((699 / 400 : ℝ) * (L : ℝ)) =
          (699 / 400 : ℝ) * (L : ℝ) * (2 * (A.card : ℝ) + 2 * (A.card : ℝ) ^ 3 / (W : ℝ)) by ring]
      exact hmul'.trans (mul_le_mul_of_nonneg_left hrhs (by positivity))
    have h2 : (A.card : ℝ) ^ 3 ≤ (699 / 200 : ℝ) * (L : ℝ) * (1 + δ) := by
      have h1' : (A.card : ℝ) * (A.card : ℝ) ^ 3 ≤ (A.card : ℝ) * ((699 / 200 : ℝ) * (L : ℝ) * (1 + δ)) := by
        linarith [show (A.card : ℝ) * (A.card : ℝ) ^ 3 = (A.card : ℝ) ^ 4 by ring,
                  show (A.card : ℝ) * ((699 / 200 : ℝ) * (L : ℝ) * (1 + δ)) =
                    (699 / 400 : ℝ) * (L : ℝ) * (2 * (A.card : ℝ) * (1 + δ)) by ring]
      exact le_of_mul_le_mul_left h1' hApos
    have h3 : (699 / 200 : ℝ) * (L : ℝ) * (1 + δ) ≤ (C₀ + ε) ^ 3 * (N : ℝ) := by
      calc (699 / 200 : ℝ) * (L : ℝ) * (1 + δ)
          ≤ (699 / 200 : ℝ) * ((1 + δ) * (N : ℝ)) * (1 + δ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL_le (by norm_num)) (by linarith)
        _ = ((699 / 200 : ℝ) * (1 + δ) * (1 + δ)) * (N : ℝ) := by ring
        _ ≤ (C₀ + ε) ^ 3 * (N : ℝ) := mul_le_mul_of_nonneg_right hprod_le hN_pos.le
    have hN_cbrt_cube : ((N : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
    rw [mul_pow, hN_cbrt_cube]
    exact h2.trans h3
  by_contra hgt
  push Not at hgt
  have := pow_lt_pow_left₀ hgt (by positivity) (by norm_num : 3 ≠ 0)
  linarith

/-- **Ben Green's (2001) `B_3` Upper Bound (`erdos_241.variants.upper_bound`)** as a direct corollary:
for every `ε > 0`, eventually every `B_3` set `A ⊆ {1, …, N}` satisfies
`(|A| : ℝ) ≤ ((7 / 2 : ℝ) ^ (1 / 3) + ε) * N ^ (1 / 3)`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_b3_green_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (∀ m₁ m₂ : Multiset ℕ,
          m₁.card = 3 → m₂.card = 3 →
          (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
          m₁.sum = m₂.sum → m₁ = m₂) →
        (A.card : ℝ) ≤ (((7 / 2 : ℝ) ^ ((1 : ℝ) / 3)) + ε) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  intro ε hε
  filter_upwards [ppl088_b3_upper_bound_beats_green ε hε] with N hN A hAsub hB3
  have hle : (699 / 200 : ℝ) ^ ((1 : ℝ) / 3) ≤ (7 / 2 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have hNr : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact (hN A hAsub hB3).trans (mul_le_mul_of_nonneg_right (by linarith) hNr)

/-! ### Section 6: Certified Fourier-LP & Macroscopic Autoconvolution Barriers -/

private lemma sum_Icc_sub_real {n : ℕ} (hn : 1 ≤ n) :
    2 * ∑ d ∈ Finset.Icc 1 (n - 1), ((n : ℝ) - (d : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) := by
  have hnat := sum_Icc_sub_eq n
  have hcast : ((2 * ∑ d ∈ Finset.Icc 1 (n - 1), (n - d) : ℕ) : ℝ) =
      ((n * (n - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hcongr : ∑ d ∈ Finset.Icc 1 (n - 1), ((n - d : ℕ) : ℝ) =
      ∑ d ∈ Finset.Icc 1 (n - 1), ((n : ℝ) - (d : ℝ)) :=
    Finset.sum_congr rfl (fun d hd => Nat.cast_sub (by rw [Finset.mem_Icc] at hd; omega))
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, hcongr, Nat.cast_mul, Nat.cast_sub hn,
    Nat.cast_one] at hcast
  exact hcast

private lemma discrete_fejer_nonneg (N : ℕ) (θ : ℝ) :
    0 ≤ (N : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ) := by
  have hsq :
      (∑ n ∈ Finset.range N, Real.cos ((n : ℝ) * θ)) ^ 2 +
      (∑ n ∈ Finset.range N, Real.sin ((n : ℝ) * θ)) ^ 2 =
      (N : ℝ) + 2 * ∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ) := by
    have h1 : (∑ n ∈ Finset.range N, Real.cos ((n : ℝ) * θ)) ^ 2 +
        (∑ n ∈ Finset.range N, Real.sin ((n : ℝ) * θ)) ^ 2 =
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, Real.cos (((a : ℝ) - (b : ℝ)) * θ) := by
      simp_rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      have hsub : ((a : ℝ) - (b : ℝ)) * θ = (a : ℝ) * θ - (b : ℝ) * θ := by ring
      rw [hsub, Real.cos_sub]
    rw [h1]
    have hsplit : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, Real.cos (((a : ℝ) - (b : ℝ)) * θ) =
        (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, if a = b then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) +
        (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, if b < a then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) +
        (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, if a < b then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) := by
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rcases lt_trichotomy a b with hlt | heq | hgt
      · simp [hlt, lt_asymm hlt, ne_of_lt hlt]
      · simp [heq]
      · simp [hgt, lt_asymm hgt, ne_of_gt hgt]
    rw [hsplit]
    have hdiag : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (if a = b then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) = (N : ℝ) := by
      have h2 : ∀ a ∈ Finset.range N,
          ∑ b ∈ Finset.range N, (if a = b then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) = 1 := by
        intro a ha
        rw [Finset.sum_ite_eq, if_pos ha]
        simp
      rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hsymm : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          (if a < b then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) =
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          (if b < a then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      by_cases h : b < a
      · rw [if_pos h, if_pos h]
        have : ((b : ℝ) - (a : ℝ)) * θ = -(((a : ℝ) - (b : ℝ)) * θ) := by ring
        rw [this, Real.cos_neg]
      · simp [h]
    have hupper : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          (if b < a then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0) =
        ∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ) := by
      calc ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
              (if b < a then Real.cos (((a : ℝ) - (b : ℝ)) * θ) else 0)
          = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ d ∈ Finset.Icc 1 (N - 1),
              if b < a ∧ a - b = d then Real.cos ((d : ℝ) * θ) else 0 := by
            refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
            rw [Finset.mem_range] at ha hb
            by_cases hba : b < a
            · rw [if_pos hba]
              have hd_mem : a - b ∈ Finset.Icc 1 (N - 1) := by rw [Finset.mem_Icc]; omega
              have h1 : ∀ d ∈ Finset.Icc 1 (N - 1),
                  (if b < a ∧ a - b = d then Real.cos ((d : ℝ) * θ) else 0) =
                  (if a - b = d then Real.cos ((d : ℝ) * θ) else 0) := fun d _ => by simp [hba]
              rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq, if_pos hd_mem, Nat.cast_sub hba.le]
            · rw [if_neg hba]
              symm; apply Finset.sum_eq_zero; intro d _; simp [hba]
        _ = ∑ a ∈ Finset.range N, ∑ d ∈ Finset.Icc 1 (N - 1), ∑ b ∈ Finset.range N,
              if b < a ∧ a - b = d then Real.cos ((d : ℝ) * θ) else 0 :=
            Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
        _ = ∑ d ∈ Finset.Icc 1 (N - 1), ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
              if b < a ∧ a - b = d then Real.cos ((d : ℝ) * θ) else 0 := Finset.sum_comm
        _ = ∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ) := by
            refine Finset.sum_congr rfl (fun d hd => ?_)
            rw [Finset.mem_Icc] at hd
            have hcnt : ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
                  (if b < a ∧ a - b = d then Real.cos ((d : ℝ) * θ) else 0) =
                (((Finset.range N).filter (fun a => d ≤ a)).card : ℝ) * Real.cos ((d : ℝ) * θ) := by
              rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl (fun a ha => ?_)
              rw [Finset.mem_range] at ha
              by_cases hda : d ≤ a
              · rw [if_pos hda, Nat.cast_one, one_mul]
                have hmem : a - d ∈ Finset.range N := by rw [Finset.mem_range]; omega
                have h1 : ∀ b ∈ Finset.range N,
                    (if b < a ∧ a - b = d then Real.cos ((d : ℝ) * θ) else 0) =
                    (if a - d = b then Real.cos ((d : ℝ) * θ) else 0) := by
                  intro b _
                  congr 1; exact propext (by omega)
                rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq, if_pos hmem]
              · rw [if_neg hda, Nat.cast_zero, zero_mul]
                apply Finset.sum_eq_zero; intro b _; rw [if_neg (by omega)]
            rw [hcnt]
            have hf : (Finset.range N).filter (fun a => d ≤ a) = Finset.Ico d N := by
              ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
            rw [hf, Nat.card_Ico, Nat.cast_sub (by omega : d ≤ N)]
    rw [hdiag, hsymm, hupper]
    ring
  rw [← hsq]
  positivity

/-- **Certified Sidon Delsarte / Fourier-LP `N^{1/4}` Barrier (Fejér Trapezoid)**:
for every `N ≥ 2`, `1 ≤ M < N`, and `k : ℝ` with `(M : ℝ)² / (N - M) ≤ k - 1`,
the explicit trapezoid `D(d) = min(1, (N - d) / (N - M))` (`1 ≤ d ≤ N - 1`) satisfies:
1. `0 ≤ D(d) ≤ 1` for all `d ∈ Icc 1 (N - 1)`,
2. **Positive definiteness:** `k + 2 * ∑_{d=1}^{N-1} D(d) * cos(d * θ) ≥ 0` for ALL `θ ∈ ℝ`,
3. **Exact Delsarte mass:** `k + 2 * ∑_{d=1}^{N-1} D(d) = (k - 1) + N + M`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_sidon_delsarte_fejer_trapezoid_barrier
    (N M : ℕ) (hM : 1 ≤ M) (hMN : M < N) (k : ℝ)
    (hk : (M : ℝ) ^ 2 / ((N : ℝ) - (M : ℝ)) ≤ k - 1) :
    (∀ d ∈ Finset.Icc 1 (N - 1),
      0 ≤ min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) ∧
      min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) ≤ 1) ∧
    (∀ θ : ℝ, 0 ≤ k + 2 * ∑ d ∈ Finset.Icc 1 (N - 1),
      min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) * Real.cos ((d : ℝ) * θ)) ∧
    (k + 2 * ∑ d ∈ Finset.Icc 1 (N - 1),
      min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) =
      (k - 1) + (N : ℝ) + (M : ℝ)) := by
  have hNM_pos : (0 : ℝ) < (N : ℝ) - (M : ℝ) := by
    have : (M : ℝ) < (N : ℝ) := by exact_mod_cast hMN
    linarith
  have htrap_eq : ∀ d ∈ Finset.Icc 1 (N - 1),
      min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) =
      (((N : ℝ) - (d : ℝ)) - (if d ≤ M - 1 then ((M : ℝ) - (d : ℝ)) else 0)) /
        ((N : ℝ) - (M : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    by_cases hdm : d ≤ M - 1
    · rw [if_pos hdm]
      have hle : 1 ≤ ((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ)) := by
        rw [one_le_div hNM_pos]
        have : (d : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : d ≤ M)
        linarith
      rw [min_eq_left hle]
      field_simp; ring
    · rw [if_neg hdm]
      have hge : ((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ)) ≤ 1 := by
        rw [div_le_one hNM_pos]
        have : (M : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : M ≤ d)
        linarith
      rw [min_eq_right hge, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rw [Finset.mem_Icc] at hd
    refine ⟨le_min zero_le_one ?_, min_le_left _ _⟩
    have : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : d ≤ N)
    exact div_nonneg (by linarith) hNM_pos.le
  · intro θ
    set SN : ℝ := ∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ)
    set SM : ℝ := ∑ d ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ)
    have hsplit : ∑ d ∈ Finset.Icc 1 (N - 1),
          min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) * Real.cos ((d : ℝ) * θ) =
        (SN - SM) / ((N : ℝ) - (M : ℝ)) := by
      have h1 : ∀ d ∈ Finset.Icc 1 (N - 1),
          min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) * Real.cos ((d : ℝ) * θ) =
          (((N : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ) -
           (if d ≤ M - 1 then ((M : ℝ) - (d : ℝ)) * Real.cos ((d : ℝ) * θ) else 0)) /
            ((N : ℝ) - (M : ℝ)) := by
        intro d hd
        rw [htrap_eq d hd]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl h1, ← Finset.sum_div, Finset.sum_sub_distrib]
      congr 2
      rw [← Finset.sum_filter]
      congr 1
      ext d; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hsplit]
    have hFN : 0 ≤ (N : ℝ) + 2 * SN := discrete_fejer_nonneg N θ
    have hFM_le : (M : ℝ) + 2 * SM ≤ (M : ℝ) ^ 2 := by
      have h1 : SM ≤ ∑ d ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (d : ℝ)) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        rw [Finset.mem_Icc] at hd
        have hnn : (0 : ℝ) ≤ (M : ℝ) - (d : ℝ) := by
          have : (d : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : d ≤ M)
          linarith
        nlinarith [Real.cos_le_one ((d : ℝ) * θ)]
      have h2 := sum_Icc_sub_real hM
      nlinarith
    have hrew : k + 2 * ((SN - SM) / ((N : ℝ) - (M : ℝ))) =
        (k - 1) + (((N : ℝ) + 2 * SN) - ((M : ℝ) + 2 * SM)) / ((N : ℝ) - (M : ℝ)) := by
      field_simp; ring
    rw [hrew]
    have hdiv : -((M : ℝ) ^ 2 / ((N : ℝ) - (M : ℝ))) ≤
        (((N : ℝ) + 2 * SN) - ((M : ℝ) + 2 * SM)) / ((N : ℝ) - (M : ℝ)) := by
      rw [← neg_div, div_le_div_iff_of_pos_right hNM_pos]
      linarith
    linarith
  · have hsplit0 : ∑ d ∈ Finset.Icc 1 (N - 1),
          min (1 : ℝ) (((N : ℝ) - (d : ℝ)) / ((N : ℝ) - (M : ℝ))) =
        ((∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ))) -
         (∑ d ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (d : ℝ)))) / ((N : ℝ) - (M : ℝ)) := by
      rw [Finset.sum_congr rfl htrap_eq, ← Finset.sum_div, Finset.sum_sub_distrib]
      congr 2
      rw [← Finset.sum_filter]
      congr 1
      ext d; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    rw [hsplit0]
    have hN_sum := sum_Icc_sub_real (by omega : 1 ≤ N)
    have hM_sum := sum_Icc_sub_real hM
    have hmul : 2 * (((∑ d ∈ Finset.Icc 1 (N - 1), ((N : ℝ) - (d : ℝ))) -
          (∑ d ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (d : ℝ)))) / ((N : ℝ) - (M : ℝ))) =
        (N : ℝ) + (M : ℝ) - 1 := by
      rw [mul_div_assoc', div_eq_iff hNM_pos.ne']
      linarith [show ((N : ℝ) + (M : ℝ) - 1) * ((N : ℝ) - (M : ℝ)) =
        (N : ℝ) * ((N : ℝ) - 1) - (M : ℝ) * ((M : ℝ) - 1) by ring]
    linarith

/-- **Certified `B_3` Weighted Macroscopic Autoconvolution Barrier**:
for any finite index set `S : Finset ℤ`, any nonnegative density `p : ℤ → ℝ` whose triple
convolution satisfies `∑_{x₁, x₂, x₃ ∈ S, x₁ + x₂ - x₃ = z} p x₁ * p x₂ * p x₃ ≤ μ` for all `z ∈ S`,
and ANY nonnegative weight functions `w, v, M_w : ℤ → ℝ` with
`w x₁ * w x₂ * w x₃ ≤ M_w (x₁ + x₂ - x₃)` for all `x₁, x₂, x₃ ∈ S`,
the weighted 4-fold sum is bounded by `μ * ∑ z ∈ S, M_w z * v z * p z`.
(Pure Mathlib statement; `0` custom definitions.) -/
theorem ppl088_b3_weighted_macroscopic_barrier
    (S : Finset ℤ) (p w v M_w : ℤ → ℝ) (μ : ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hw : ∀ x ∈ S, 0 ≤ w x) (hv : ∀ x ∈ S, 0 ≤ v x)
    (hMw : ∀ x₁ ∈ S, ∀ x₂ ∈ S, ∀ x₃ ∈ S, w x₁ * w x₂ * w x₃ ≤ M_w (x₁ + x₂ - x₃))
    (htriple : ∀ z ∈ S,
      (∑ x₁ ∈ S, ∑ x₂ ∈ S, ∑ x₃ ∈ S,
        if x₁ + x₂ - x₃ = z then p x₁ * p x₂ * p x₃ else 0) ≤ μ) :
    ∑ z ∈ S,
      (∑ x₁ ∈ S, ∑ x₂ ∈ S, ∑ x₃ ∈ S,
        if x₁ + x₂ - x₃ = z then (w x₁ * p x₁) * (w x₂ * p x₂) * (w x₃ * p x₃) else 0) *
      (v z * p z) ≤
    μ * ∑ z ∈ S, M_w z * v z * p z := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun z hz => ?_)
  have hvp_nn : 0 ≤ v z * p z := mul_nonneg (hv z hz) (hp z hz)
  have hMw_ge0 : 0 ≤ M_w z := by
    have hself := hMw z hz z hz z hz
    have hzz : z + z - z = z := by ring
    rw [hzz] at hself
    exact (mul_nonneg (mul_nonneg (hw z hz) (hw z hz)) (hw z hz)).trans hself
  have hinner :
      (∑ x₁ ∈ S, ∑ x₂ ∈ S, ∑ x₃ ∈ S,
        if x₁ + x₂ - x₃ = z then (w x₁ * p x₁) * (w x₂ * p x₂) * (w x₃ * p x₃) else 0) ≤
      M_w z * (∑ x₁ ∈ S, ∑ x₂ ∈ S, ∑ x₃ ∈ S,
        if x₁ + x₂ - x₃ = z then p x₁ * p x₂ * p x₃ else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x₁ hx₁ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x₂ hx₂ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun x₃ hx₃ => ?_)
    by_cases heq : x₁ + x₂ - x₃ = z
    · rw [if_pos heq, if_pos heq]
      have hppp : 0 ≤ p x₁ * p x₂ * p x₃ := mul_nonneg (mul_nonneg (hp x₁ hx₁) (hp x₂ hx₂)) (hp x₃ hx₃)
      have h1 : (w x₁ * p x₁) * (w x₂ * p x₂) * (w x₃ * p x₃) =
          (w x₁ * w x₂ * w x₃) * (p x₁ * p x₂ * p x₃) := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (heq ▸ hMw x₁ hx₁ x₂ hx₂ x₃ hx₃) hppp
    · simp [heq]
  have h1 : M_w z * (∑ x₁ ∈ S, ∑ x₂ ∈ S, ∑ x₃ ∈ S,
      if x₁ + x₂ - x₃ = z then p x₁ * p x₂ * p x₃ else 0) ≤ M_w z * μ :=
    mul_le_mul_of_nonneg_left (htriple z hz) hMw_ge0
  have h2 := mul_le_mul_of_nonneg_right (hinner.trans h1) hvp_nn
  linarith

end PPL088
