/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import RHDirect.Stage8ExplicitPrimeBounds

/-!
# PPL 124 (Erdős #39, $500), PPL 018 (Erdős #1191, $1,000) & PPL 168 (Erdős #41, $500):
# Infinite Sidon Sets, Generalized `B_h` Oscillation, Parity Barriers & World-Record Constructions

## Scope & Honest Labeling
This file formalizes unconditional frontier theorems, sharp oscillation bounds, parity barriers,
and landmark lower-bound constructions surrounding three open Erdős prize problems:
- **PPL 124 (Erdős #39, $500, OPEN):** Does there exist an infinite Sidon set `A ⊆ ℕ` with
  `|A ∩ [1, N]| ≫_ε N^{1/2 - ε}` for all `ε > 0`?
- **PPL 018 (Erdős #1191, $1,000, OPEN):** Sharp lower-density / upper-density behavior of infinite
  Sidon sets (e.g., whether `liminf |A ∩ [1, N]| / √(N / log N) = 0` or `limsup |A ∩ [1, N]| / √N = 1`).
- **PPL 168 (Erdős #41, $500, OPEN):** Must every infinite `B_3` set `A ⊆ ℕ` satisfy
  `liminf |A ∩ [1, N]| / N^{1/3} = 0`?

**Honest Scope:** None of these three full open cash-prize conjectures is claimed solved here.
Every public theorem below has a **100% pure-Mathlib type signature** (`0` custom or `private`
definitions in any public theorem type), `0` `sorry`, `0` custom axioms, and `leanchecker: PASS`.
-/

namespace PPL124

open Filter Finset
open scoped BigOperators ENNReal

/-! ### Shared Analytic & Combinatorial Utilities (Private) -/

private lemma harmonic_upper_bound (R : ℕ) (hR : 1 ≤ R) :
    ∑ j ∈ Finset.Icc 1 R, (1 : ℝ) / (j : ℝ) ≤ 1 + Real.log (R : ℝ) := by
  induction R, hR using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      have h1 : (m : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ Real.exp (-(1 / ((m + 1 : ℕ) : ℝ))) := by
        have := Real.add_one_le_exp (-(1 / ((m + 1 : ℕ) : ℝ)))
        have heq : -(1 / ((m + 1 : ℕ) : ℝ)) + 1 = (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
          push_cast
          field_simp
          ring
        linarith
      have h2 : Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤ -(1 / ((m + 1 : ℕ) : ℝ)) := by
        calc Real.log ((m : ℝ) / ((m + 1 : ℕ) : ℝ))
            ≤ Real.log (Real.exp (-(1 / ((m + 1 : ℕ) : ℝ)))) :=
              Real.log_le_log (div_pos hm_pos hm1_pos) h1
          _ = -(1 / ((m + 1 : ℕ) : ℝ)) := Real.log_exp _
      rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at h2
      linarith
    linarith

private lemma log_le_harmonic_pred (R : ℕ) (hR : 1 ≤ R) :
    Real.log (R : ℝ) ≤ ∑ j ∈ Finset.Icc 1 (R - 1), (1 : ℝ) / (j : ℝ) := by
  induction R, hR using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    have hsplit : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : m ∉ Finset.Icc 1 (m - 1) := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnotmem]
    have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
    have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hstep : Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
      rw [← Real.log_div hm1_pos.ne' hm_pos.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hm1_pos hm_pos)
      have heq : ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 = (1 : ℝ) / (m : ℝ) := by
        push_cast; field_simp; ring
      linarith
    linarith

private lemma weighted_inv_sqrt_diff_lower (R : ℕ) (hR : 2 ≤ R) :
    (Real.log (R : ℝ) - 1) / 2 ≤
      ∑ j ∈ Finset.Icc 1 (R - 1),
        (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * Real.sqrt (j : ℝ) := by
  have hterm : ∀ j ∈ Finset.Icc 1 (R - 1),
      (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)) ≤
        (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * Real.sqrt (j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
    have hj1_pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj_pos
    have hsj1 : 0 < Real.sqrt ((j + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hj1_pos
    have hsle : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)
    have hdiff : (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) *
        (Real.sqrt ((j + 1 : ℕ) : ℝ) + Real.sqrt (j : ℝ)) = 1 := by
      nlinarith [Real.sq_sqrt hj_pos.le, Real.sq_sqrt hj1_pos.le,
        show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
    have hsum_le : Real.sqrt ((j + 1 : ℕ) : ℝ) + Real.sqrt (j : ℝ) ≤
        2 * Real.sqrt ((j + 1 : ℕ) : ℝ) := by linarith
    have h1 : 1 / (2 * Real.sqrt ((j + 1 : ℕ) : ℝ)) ≤
        Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * Real.sqrt (j : ℝ) =
        (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
      field_simp
    rw [h2, le_div_iff₀ hsj1]
    have hsq : Real.sqrt ((j + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt hj1_pos.le
    calc (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)) * Real.sqrt ((j + 1 : ℕ) : ℝ)
        = 1 / (2 * Real.sqrt ((j + 1 : ℕ) : ℝ)) := by
          rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) (by positivity)]
          nlinarith [hsq]
      _ ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ) := h1
  have hsum1 : ∑ j ∈ Finset.Icc 1 (R - 1), (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)) ≤
      ∑ j ∈ Finset.Icc 1 (R - 1),
        (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * Real.sqrt (j : ℝ) :=
    Finset.sum_le_sum hterm
  have hshift : ∑ j ∈ Finset.Icc 1 (R - 1), (1 : ℝ) / ((j + 1 : ℕ) : ℝ) =
      ∑ m ∈ Finset.Icc 2 R, (1 : ℝ) / (m : ℝ) := by
    refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro a _ b _ hab; omega
    · intro m hm; simp only [Finset.mem_Icc] at hm
      exact ⟨m - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
    · intro j _; rfl
  have hharm : Real.log (R : ℝ) - 1 ≤ ∑ m ∈ Finset.Icc 2 R, (1 : ℝ) / (m : ℝ) := by
    have hlog := log_le_harmonic_pred R (by omega)
    have hsplit : Finset.Icc 1 (R - 1) = insert 1 (Finset.Icc 2 (R - 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h1not : (1 : ℕ) ∉ Finset.Icc 2 (R - 1) := by simp
    have hsub : Finset.Icc 2 (R - 1) ⊆ Finset.Icc 2 R := by
      intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
    have hle : ∑ m ∈ Finset.Icc 2 (R - 1), (1 : ℝ) / (m : ℝ) ≤
        ∑ m ∈ Finset.Icc 2 R, (1 : ℝ) / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    rw [hsplit, Finset.sum_insert h1not] at hlog
    have h1eq : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1eq] at hlog
    linarith
  have hhalf : (Real.log (R : ℝ) - 1) / 2 ≤
      ∑ j ∈ Finset.Icc 1 (R - 1), (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)) := by
    have heq : ∑ j ∈ Finset.Icc 1 (R - 1), (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ)) =
        (∑ j ∈ Finset.Icc 1 (R - 1), (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) / 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [heq, hshift]
    linarith
  linarith

private lemma abel_sum_inv_sqrt (b : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) :
    ∑ j ∈ Finset.Icc 1 R, b j / Real.sqrt (j : ℝ) =
      (∑ i ∈ Finset.Icc 1 R, b i) / Real.sqrt (R : ℝ) +
      ∑ j ∈ Finset.Icc 1 (R - 1),
        (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
          (∑ i ∈ Finset.Icc 1 j, b i) := by
  induction R, hR using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
    have hsplit_right :
        ∑ j ∈ Finset.Icc 1 m,
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
            (∑ i ∈ Finset.Icc 1 j, b i) =
        (1 / Real.sqrt (m : ℝ) - 1 / Real.sqrt ((m + 1 : ℕ) : ℝ)) *
            (∑ i ∈ Finset.Icc 1 m, b i) +
        ∑ j ∈ Finset.Icc 1 (m - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
            (∑ i ∈ Finset.Icc 1 j, b i) := by
      have hsplit : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m ∉ Finset.Icc 1 (m - 1) := by simp only [Finset.mem_Icc]; omega
      conv_lhs => arg 1; rw [hsplit]
      rw [Finset.sum_insert hnot]
    rw [hsplit_right, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    ring

private lemma liminf_eq_zero_of_nonneg_of_frequently_le {f : ℕ → ℝ}
    (hnn : ∀ n, 0 ≤ f n)
    (hf : ∀ ε > 0, ∃ᶠ n in atTop, f n ≤ ε) :
    liminf f atTop = 0 := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop f :=
    ⟨0, eventually_map.mpr (Eventually.of_forall hnn)⟩
  have hcob : IsCoboundedUnder (· ≥ ·) atTop f := by
    refine ⟨1, fun a ha => ?_⟩
    rw [eventually_map] at ha
    obtain ⟨n, hn1, hn2⟩ := (ha.and_frequently (hf 1 one_pos)).exists
    exact le_trans hn1 hn2
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    exact Filter.liminf_le_of_frequently_le (hf ε hε) hbdd
  · exact Filter.le_liminf_of_le hcob (Eventually.of_forall hnn)

private lemma ncard_inter_Icc_eq_filter_card (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    (A ∩ Set.Icc 1 N).ncard = ((Finset.Icc 1 N).filter (fun x => x ∈ A)).card := by
  rw [← Set.ncard_coe_finset ((Finset.Icc 1 N).filter (fun x => x ∈ A))]
  congr 1
  ext x
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc, Set.mem_inter_iff, Set.mem_Icc]
  tauto

private lemma descFactorial_mul_two_pow_ge (a m : ℕ) (h : 2 * m ≤ a) :
    a ^ m ≤ 2 ^ m * Nat.descFactorial a m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, pow_succ, pow_succ]
    have ih' := ih (by omega)
    have hfac : a ≤ 2 * (a - k) := by omega
    calc a ^ k * a
        ≤ (2 ^ k * a.descFactorial k) * (2 * (a - k)) := Nat.mul_le_mul ih' hfac
      _ = 2 ^ k * 2 * ((a - k) * a.descFactorial k) := by ring

private lemma factorial_mul_self_le_pow (m : ℕ) (hm : 2 ≤ m) :
    m.factorial * m ≤ m ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h1 : (k + 1) * k.factorial * (k + 1) ≤ (k + 1) ^ 2 * k.factorial := by ring_nf; rfl
    have h2 : k.factorial * k ≤ k ^ k := ih
    have h3 : k.factorial ≤ k ^ (k - 1) := by
      have hkpos : 0 < k := by omega
      have hkk : k ^ (k - 1) * k = k ^ k := by
        rw [← pow_succ, show k - 1 + 1 = k by omega]
      exact Nat.le_of_mul_le_mul_right (h2.trans_eq hkk.symm) hkpos
    have h4 : k ^ (k - 1) ≤ (k + 1) ^ (k - 1) := Nat.pow_le_pow_left (Nat.le_succ k) _
    calc (k + 1) * k.factorial * (k + 1)
        = (k + 1) ^ 2 * k.factorial := by ring
      _ ≤ (k + 1) ^ 2 * (k + 1) ^ (k - 1) := Nat.mul_le_mul_left _ (h3.trans h4)
      _ = (k + 1) ^ (2 + (k - 1)) := (pow_add _ _ _).symm
      _ = (k + 1) ^ (k + 1) := by congr 1; omega

/-!
## Part I — Infinite Sidon Upper Oscillation (Erdős 1941 — PPL 018 / #1191 & `B_2` Analogue of #41)
-/

/-- **Finite Sidon Upper Bound (`|A ∩ [1, N]| (|A ∩ [1, N]| - 1) ≤ 2 N`):**
Every Sidon set `A ⊆ ℕ` satisfies `a (a - 1) ≤ 2 N` where `a = |A ∩ [1, N]|`,
via injectivity of positive differences `a₂ - a₁ ∈ [1, N - 1]`. -/
theorem ppl124_finite_sidon_upper_bound (A : Set ℕ)
    (hSidon : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
      a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂)
    (N : ℕ) :
    (A ∩ Set.Icc 1 N).ncard * ((A ∩ Set.Icc 1 N).ncard - 1) ≤ 2 * N := by
  classical
  rw [ncard_inter_Icc_eq_filter_card]
  set S := (Finset.Icc 1 N).filter (fun x => x ∈ A)
  set P := (S ×ˢ S).filter (fun p => p.1 < p.2)
  have hP_card : 2 * P.card = S.card * (S.card - 1) := by
    have hlt_gt : ((S ×ˢ S).filter (fun p => p.2 < p.1)).card = P.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp; simp only [P, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ h; ext <;> [exact congrArg Prod.snd h; exact congrArg Prod.fst h]
      · intro p hp; simp only [P, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨(p.2, p.1), by simp [hp.1.1, hp.1.2, hp.2], rfl⟩
    have hdiag : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card = S.card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro p hp; simp only [Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
      · intro p₁ hp₁ p₂ hp₂ h
        simp only [Finset.mem_filter] at hp₁ hp₂
        ext; exact h; exact hp₁.2.symm.trans (h.trans hp₂.2)
      · intro x hx; exact ⟨(x, x), by simp [hx], rfl⟩
    have hpart : S.card * S.card = P.card + ((S ×ˢ S).filter (fun p => p.2 < p.1)).card +
        ((S ×ˢ S).filter (fun p => p.1 = p.2)).card := by
      have h1 : S ×ˢ S = P ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1)) ∪
          ((S ×ˢ S).filter (fun p => p.1 = p.2)) := by
        ext ⟨x, y⟩; simp only [P, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
        constructor
        · intro h; rcases lt_trichotomy x y with hlt | heq | hgt
          · exact Or.inl (Or.inl ⟨h, hlt⟩)
          · exact Or.inr ⟨h, heq⟩
          · exact Or.inl (Or.inr ⟨h, hgt⟩)
        · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      have hd1 : Disjoint P ((S ×ˢ S).filter (fun p => p.2 < p.1)) := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [P, Finset.mem_filter] at hp1 hp2; omega
      have hd2 : Disjoint (P ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1)))
          ((S ×ˢ S).filter (fun p => p.1 = p.2)) := by
        rw [Finset.disjoint_left]; intro p hp1 hp2
        simp only [P, Finset.mem_union, Finset.mem_filter] at hp1 hp2; omega
      have hcard := congrArg Finset.card h1
      rw [Finset.card_product, Finset.card_union_of_disjoint hd2,
        Finset.card_union_of_disjoint hd1] at hcard
      exact hcard
    rw [hlt_gt, hdiag] at hpart
    cases hS : S.card with
    | zero => simp [hS] at hpart; omega
    | succ k => rw [hS] at hpart; rw [Nat.succ_sub_one]; nlinarith
  have hinj : P.card ≤ N := by
    have hcard_le : P.card ≤ (Finset.Icc 1 N).card := by
      refine Finset.card_le_card_of_injOn (fun p => p.2 - p.1) ?_ ?_
      · intro p hp
        simp only [P, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
        omega
      · intro p₁ hp₁ p₂ hp₂ heq
        dsimp only at heq
        simp only [P, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
        have hsum : p₁.2 + p₂.1 = p₂.2 + p₁.1 := by omega
        rcases le_total p₁.2 p₂.1 with hle1 | hle1 <;> rcases le_total p₂.2 p₁.1 with hle2 | hle2
        · have := hSidon p₁.2 hp₁.1.2.2 p₂.1 hp₂.1.1.2 p₂.2 hp₂.1.2.2 p₁.1 hp₁.1.1.2 hle1 hle2 hsum
          omega
        · have := hSidon p₁.2 hp₁.1.2.2 p₂.1 hp₂.1.1.2 p₁.1 hp₁.1.1.2 p₂.2 hp₂.1.2.2 hle1 hle2
            (by omega)
          omega
        · have := hSidon p₂.1 hp₂.1.1.2 p₁.2 hp₁.1.2.2 p₂.2 hp₂.1.2.2 p₁.1 hp₁.1.1.2 hle1 hle2
            (by omega)
          omega
        · have := hSidon p₂.1 hp₂.1.1.2 p₁.2 hp₁.1.2.2 p₁.1 hp₁.1.1.2 p₂.2 hp₂.1.2.2 hle1 hle2
            (by omega)
          ext <;> omega
    simpa using hcard_le
  omega

/-- **Erdős (1941) Infinite Sidon Oscillation with Explicit Constant (`C = 6`):**
For every infinite Sidon set `A ⊆ ℕ`, there are infinitely many `N` with
`|A ∩ [1, N]| ≤ 6 * √(N / log N)`. -/
theorem ppl124_erdos1941_sidon_liminf_log (A : Set ℕ)
    (_hInf : A.Infinite)
    (hSidon : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
      a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) :
    ∃ᶠ N : ℕ in atTop,
      ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ 6 * Real.sqrt ((N : ℝ) / Real.log (N : ℝ)) := by
  classical
  by_contra hnot
  rw [Filter.not_frequently, Filter.eventually_atTop] at hnot
  obtain ⟨N₀, hN₀⟩ := hnot
  -- Pick a large integer L ≥ max N₀ 2 so that log L > 27 (kept abstract so Lean never expands 3^27)
  have hexL : ∃ L : ℕ, N₀ ≤ L ∧ 2 ≤ L ∧ (27 : ℝ) < Real.log (L : ℝ) := by
    have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hev := (hlog_top.eventually (eventually_gt_atTop (27 : ℝ))).and
      ((eventually_ge_atTop N₀).and (eventually_ge_atTop 2))
    obtain ⟨L, h1, h2, h3⟩ := hev.exists
    exact ⟨L, h2, h3, h1⟩
  obtain ⟨L, hL_ge_N0, hL_ge2, hlogL_gt⟩ := hexL
  have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Block counts B j = |A ∩ ((j-1)L, jL]| for j ∈ [1, L]
  let B : ℕ → ℕ := fun j => ((Finset.Ioc ((j - 1) * L) (j * L)).filter (fun x => x ∈ A)).card
  let T : ℕ → ℕ := fun j => ∑ i ∈ Finset.Icc 1 j, B i
  -- Partial sums T j equal |A ∩ [1, j * L]|
  have hT_eq : ∀ j : ℕ, 1 ≤ j → T j = (A ∩ Set.Icc 1 (j * L)).ncard := by
    intro j hj
    rw [ncard_inter_Icc_eq_filter_card]
    induction j, hj using Nat.le_induction with
    | base =>
      simp only [T, B, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, zero_mul, one_mul]
      congr 1
    | succ m hm ih =>
      simp only [T] at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      have hdisj : Disjoint ((Finset.Icc 1 (m * L)).filter (fun x => x ∈ A))
          ((Finset.Ioc (m * L) ((m + 1) * L)).filter (fun x => x ∈ A)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2; omega
      have hunion : ((Finset.Icc 1 (m * L)).filter (fun x => x ∈ A)) ∪
          ((Finset.Ioc (m * L) ((m + 1) * L)).filter (fun x => x ∈ A)) =
          ((Finset.Icc 1 ((m + 1) * L)).filter (fun x => x ∈ A)) := by
        ext x; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        constructor
        · rintro (⟨⟨h1, h2⟩, hA⟩ | ⟨⟨h1, h2⟩, hA⟩)
          · exact ⟨⟨h1, by nlinarith⟩, hA⟩
          · exact ⟨⟨by omega, h2⟩, hA⟩
        · rintro ⟨⟨h1, h2⟩, hA⟩
          by_cases hle : x ≤ m * L
          · exact Or.inl ⟨⟨h1, hle⟩, hA⟩
          · exact Or.inr ⟨⟨by omega, h2⟩, hA⟩
      have hB : B (m + 1) = ((Finset.Ioc (m * L) ((m + 1) * L)).filter (fun x => x ∈ A)).card := by
        simp [B]
      rw [hB, ← Finset.card_union_of_disjoint hdisj, hunion]
  -- Upper bound: ∑_{j=1}^L B(j)^2 ≤ 4 * L
  have hsum_B2 : ∑ j ∈ Finset.Icc 1 L, ((B j : ℝ) ^ 2) ≤ 4 * (L : ℝ) := by
    -- Pairs inside each block have distinct positive differences in [1, L - 1]
    let blk : ℕ → Finset ℕ := fun j => (Finset.Ioc ((j - 1) * L) (j * L)).filter (fun x => x ∈ A)
    let pairsOf : ℕ → Finset (ℕ × ℕ) := fun j => ((blk j) ×ˢ (blk j)).filter (fun p => p.1 < p.2)
    have hpair_card : ∀ j, 2 * (pairsOf j).card + B j = (B j) ^ 2 := by
      intro j
      have hcard_eq : (blk j).card = B j := rfl
      set S := blk j
      set P := pairsOf j
      have hlt_gt : ((S ×ˢ S).filter (fun p => p.2 < p.1)).card = P.card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp; simp only [P, pairsOf, Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
        · intro p₁ _ p₂ _ h; ext <;> [exact congrArg Prod.snd h; exact congrArg Prod.fst h]
        · intro p hp; simp only [P, pairsOf, Finset.mem_filter, Finset.mem_product] at hp
          exact ⟨(p.2, p.1), by simp only [S, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
      have hdiag : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card = S.card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
        · intro p₁ hp₁ p₂ hp₂ h
          simp only [Finset.mem_filter] at hp₁ hp₂
          ext; exact h; exact hp₁.2.symm.trans (h.trans hp₂.2)
        · intro x hx; exact ⟨(x, x), by simp [hx], rfl⟩
      have hpart : S.card * S.card = P.card + ((S ×ˢ S).filter (fun p => p.2 < p.1)).card +
          ((S ×ˢ S).filter (fun p => p.1 = p.2)).card := by
        have h1 : S ×ˢ S = P ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1)) ∪
            ((S ×ˢ S).filter (fun p => p.1 = p.2)) := by
          ext ⟨x, y⟩; simp only [P, pairsOf, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
          constructor
          · intro h; rcases lt_trichotomy x y with hlt | heq | hgt
            · exact Or.inl (Or.inl ⟨h, hlt⟩)
            · exact Or.inr ⟨h, heq⟩
            · exact Or.inl (Or.inr ⟨h, hgt⟩)
          · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
        have hd1 : Disjoint P ((S ×ˢ S).filter (fun p => p.2 < p.1)) := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [P, pairsOf, Finset.mem_filter] at hp1 hp2; omega
        have hd2 : Disjoint (P ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1)))
            ((S ×ˢ S).filter (fun p => p.1 = p.2)) := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [P, pairsOf, Finset.mem_union, Finset.mem_filter] at hp1 hp2; omega
        have hcard := congrArg Finset.card h1
        rw [Finset.card_product, Finset.card_union_of_disjoint hd2,
          Finset.card_union_of_disjoint hd1] at hcard
        exact hcard
      rw [hlt_gt, hdiag, hcard_eq] at hpart
      nlinarith
    have hdisj_pairs : (Finset.Icc 1 L : Set ℕ).PairwiseDisjoint pairsOf := by
      intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      simp only [pairsOf, blk, Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc] at hp1 hp2
      have : j₁ * L < j₂ * L ∨ j₂ * L < j₁ * L := by
        rcases lt_or_gt_of_ne hne with h | h
        · left; exact Nat.mul_lt_mul_of_pos_right h (by omega)
        · right; exact Nat.mul_lt_mul_of_pos_right h (by omega)
      rcases lt_or_gt_of_ne hne with h | h
      · have hle : j₁ ≤ j₂ - 1 := by omega
        have := Nat.mul_le_mul_right L hle
        omega
      · have hle : j₂ ≤ j₁ - 1 := by omega
        have := Nat.mul_le_mul_right L hle
        omega
    have htotal_pairs : ∑ j ∈ Finset.Icc 1 L, (pairsOf j).card ≤ L := by
      rw [← Finset.card_biUnion hdisj_pairs]
      have hle : ((Finset.Icc 1 L).biUnion pairsOf).card ≤ (Finset.Icc 1 L).card := by
        refine Finset.card_le_card_of_injOn (fun p => p.2 - p.1) ?_ ?_
        · intro p hp
          simp only [Finset.mem_coe, Finset.mem_biUnion, pairsOf, blk, Finset.mem_filter,
            Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
          obtain ⟨j, hj, ⟨⟨⟨h1, h2⟩, _⟩, ⟨h3, h4⟩, _⟩, hlt⟩ := hp
          have hmul : (j - 1) * L + L = j * L := by
            rw [← Nat.succ_mul]; congr 1; omega
          omega
        · intro p₁ hp₁ p₂ hp₂ heq
          dsimp only at heq
          simp only [Finset.mem_coe, Finset.mem_biUnion, pairsOf, blk, Finset.mem_filter,
            Finset.mem_product, Finset.mem_Ioc] at hp₁ hp₂
          obtain ⟨_, _, ⟨⟨_, hA11⟩, ⟨_, hA12⟩⟩, hlt1⟩ := hp₁
          obtain ⟨_, _, ⟨⟨_, hA21⟩, ⟨_, hA22⟩⟩, hlt2⟩ := hp₂
          have hsum : p₁.2 + p₂.1 = p₂.2 + p₁.1 := by omega
          rcases le_total p₁.2 p₂.1 with hle1 | hle1 <;> rcases le_total p₂.2 p₁.1 with hle2 | hle2
          · have := hSidon p₁.2 hA12 p₂.1 hA21 p₂.2 hA22 p₁.1 hA11 hle1 hle2 hsum; omega
          · have := hSidon p₁.2 hA12 p₂.1 hA21 p₁.1 hA11 p₂.2 hA22 hle1 hle2 (by omega); omega
          · have := hSidon p₂.1 hA21 p₁.2 hA12 p₂.2 hA22 p₁.1 hA11 hle1 hle2 (by omega); omega
          · have := hSidon p₂.1 hA21 p₁.2 hA12 p₁.1 hA11 p₂.2 hA22 hle1 hle2 (by omega)
            ext <;> omega
      simpa using hle
    have hTL_le : T L ≤ 2 * L := by
      rw [hT_eq L (by omega)]
      have hfin := ppl124_finite_sidon_upper_bound A hSidon (L * L)
      set a := (A ∩ Set.Icc 1 (L * L)).ncard
      by_contra hgt
      push Not at hgt
      have h1 : (2 * L + 1) * (2 * L) ≤ a * (a - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    have hsum_nat : ∑ j ∈ Finset.Icc 1 L, (B j) ^ 2 ≤ 4 * L := by
      have heq : ∑ j ∈ Finset.Icc 1 L, (B j) ^ 2 =
          2 * (∑ j ∈ Finset.Icc 1 L, (pairsOf j).card) + T L := by
        simp only [T, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => (hpair_card j).symm
      omega
    exact_mod_cast hsum_nat
  -- Lower bound on T j for all j ∈ [1, L]
  have hT_lower : ∀ j ∈ Finset.Icc 1 L,
      (6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) * Real.sqrt (j : ℝ) ≤ (T j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [hT_eq j hj.1]
    have hjL_ge : N₀ ≤ j * L := by
      calc N₀ ≤ L := hL_ge_N0
        _ = 1 * L := (one_mul L).symm
        _ ≤ j * L := Nat.mul_le_mul_right L hj.1
    have hlt := hN₀ (j * L) hjL_ge
    push Not at hlt
    have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
    have hjL_pos : (0 : ℝ) < ((j * L : ℕ) : ℝ) := Nat.cast_pos.mpr (by nlinarith)
    have hjL_le : ((j * L : ℕ) : ℝ) ≤ (L : ℝ) ^ 2 := by
      push_cast; nlinarith [show (j : ℝ) ≤ (L : ℝ) by exact_mod_cast hj.2]
    have hlog_pos : 0 < Real.log ((j * L : ℕ) : ℝ) := by
      apply Real.log_pos
      have : (2 : ℝ) ≤ ((j * L : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ j * L by nlinarith)
      linarith
    have hlog_le : Real.log ((j * L : ℕ) : ℝ) ≤ 2 * Real.log (L : ℝ) := by
      calc Real.log ((j * L : ℕ) : ℝ)
          ≤ Real.log ((L : ℝ) ^ 2) := Real.log_le_log hjL_pos hjL_le
        _ = 2 * Real.log (L : ℝ) := by rw [Real.log_pow]; norm_num
    have hsqrt_le : Real.sqrt (((j * L : ℕ) : ℝ) / (2 * Real.log (L : ℝ))) ≤
        Real.sqrt (((j * L : ℕ) : ℝ) / Real.log ((j * L : ℕ) : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left hjL_pos.le hlog_pos hlog_le
    have hrew : (6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) * Real.sqrt (j : ℝ) =
        6 * Real.sqrt (((j * L : ℕ) : ℝ) / (2 * Real.log (L : ℝ))) := by
      have hlogL_pos : 0 < Real.log (L : ℝ) := by linarith
      rw [mul_assoc, ← Real.sqrt_mul (div_nonneg hL_pos.le hlogL_pos.le)]
      rw [show (6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ) * (j : ℝ)) =
          6 * (Real.sqrt ((L : ℝ) / Real.log (L : ℝ) * (j : ℝ)) / Real.sqrt 2) by ring]
      rw [← Real.sqrt_div (by positivity)]
      congr 2
      push_cast; ring
    linarith
  -- Combine Abel summation + Cauchy-Schwarz
  let S_ab : ℝ := ∑ j ∈ Finset.Icc 1 L, (B j : ℝ) / Real.sqrt (j : ℝ)
  have hS_lower : (3 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) *
      (Real.log (L : ℝ) - 1) ≤ S_ab := by
    have habel := abel_sum_inv_sqrt (fun j => (B j : ℝ)) L (by omega)
    have hT_cast : ∀ j, ∑ i ∈ Finset.Icc 1 j, (B i : ℝ) = (T j : ℝ) := fun j => by
      simp [T]
    have hmain : (3 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) *
        (Real.log (L : ℝ) - 1) ≤
        ∑ j ∈ Finset.Icc 1 (L - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * (T j : ℝ) := by
      have hw := weighted_inv_sqrt_diff_lower L (by omega)
      have hc_nn : 0 ≤ (6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) := by positivity
      calc (3 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) * (Real.log (L : ℝ) - 1)
          = ((6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ))) *
              ((Real.log (L : ℝ) - 1) / 2) := by ring
        _ ≤ ((6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ))) *
              (∑ j ∈ Finset.Icc 1 (L - 1),
                (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * Real.sqrt (j : ℝ)) :=
            mul_le_mul_of_nonneg_left hw hc_nn
        _ = ∑ j ∈ Finset.Icc 1 (L - 1),
              (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
                ((6 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) * Real.sqrt (j : ℝ)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
        _ ≤ ∑ j ∈ Finset.Icc 1 (L - 1),
              (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * (T j : ℝ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j ∈ Finset.Icc 1 L := by
              simp only [Finset.mem_Icc] at hj ⊢; omega
            have hdiff_nn : 0 ≤ 1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
              have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by
                simp only [Finset.mem_Icc] at hj; omega)
              have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj_pos
              have hsle : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) :=
                Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)
              have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hsj hsle
              linarith
            exact mul_le_mul_of_nonneg_left (hT_lower j hj') hdiff_nn
    have hTL_nn : 0 ≤ (∑ i ∈ Finset.Icc 1 L, (B i : ℝ)) / Real.sqrt (L : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have hSab_def : S_ab = ∑ j ∈ Finset.Icc 1 L, (B j : ℝ) / Real.sqrt (j : ℝ) := rfl
    rw [hSab_def, habel]
    have hsum_eq : ∑ j ∈ Finset.Icc 1 (L - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
            (∑ i ∈ Finset.Icc 1 j, (B i : ℝ)) =
        ∑ j ∈ Finset.Icc 1 (L - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * (T j : ℝ) := by
      refine Finset.sum_congr rfl fun j _ => by rw [hT_cast]
    linarith
  have hS_upper : S_ab ^ 2 ≤ (1 + Real.log (L : ℝ)) * (4 * (L : ℝ)) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 L)
      (fun j => (1 : ℝ) / Real.sqrt (j : ℝ)) (fun j => (B j : ℝ))
    have hSab_eq : S_ab = ∑ j ∈ Finset.Icc 1 L, (1 / Real.sqrt (j : ℝ)) * (B j : ℝ) := by
      change ∑ j ∈ Finset.Icc 1 L, (B j : ℝ) / Real.sqrt (j : ℝ) = _
      refine Finset.sum_congr rfl fun j _ => by ring
    have hsq1 : ∑ j ∈ Finset.Icc 1 L, ((1 : ℝ) / Real.sqrt (j : ℝ)) ^ 2 =
        ∑ j ∈ Finset.Icc 1 L, (1 : ℝ) / (j : ℝ) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [Finset.mem_Icc] at hj
      rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg j)]
    rw [hSab_eq]
    calc (∑ j ∈ Finset.Icc 1 L, (1 / Real.sqrt (j : ℝ)) * (B j : ℝ)) ^ 2
        ≤ (∑ j ∈ Finset.Icc 1 L, (1 / Real.sqrt (j : ℝ)) ^ 2) *
            (∑ j ∈ Finset.Icc 1 L, (B j : ℝ) ^ 2) := hcs
      _ = (∑ j ∈ Finset.Icc 1 L, (1 : ℝ) / (j : ℝ)) *
            (∑ j ∈ Finset.Icc 1 L, (B j : ℝ) ^ 2) := by rw [hsq1]
      _ ≤ (1 + Real.log (L : ℝ)) * (4 * (L : ℝ)) :=
          mul_le_mul (harmonic_upper_bound L (by omega)) hsum_B2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by linarith)
  -- Final contradiction: (9/2) * (L / log L) * (log L - 1)^2 ≤ 4 * L * (1 + log L)
  have hlogL_pos : 0 < Real.log (L : ℝ) := by linarith
  have hlower_nn : 0 ≤ (3 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) *
      (Real.log (L : ℝ) - 1) := by
    have : 0 ≤ Real.log (L : ℝ) - 1 := by linarith
    positivity
  have hsq_le : ((3 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) *
      (Real.log (L : ℝ) - 1)) ^ 2 ≤ (1 + Real.log (L : ℝ)) * (4 * (L : ℝ)) :=
    (pow_le_pow_left₀ hlower_nn hS_lower 2).trans hS_upper
  have hlhs_simp : ((3 / Real.sqrt 2) * Real.sqrt ((L : ℝ) / Real.log (L : ℝ)) *
      (Real.log (L : ℝ) - 1)) ^ 2 =
      (9 / 2) * ((L : ℝ) / Real.log (L : ℝ)) * (Real.log (L : ℝ) - 1) ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (div_nonneg hL_pos.le hlogL_pos.le)]
    ring
  rw [hlhs_simp] at hsq_le
  -- Multiply both sides by log L > 0 and divide by L > 0
  have hmul : (9 / 2) * (L : ℝ) * (Real.log (L : ℝ) - 1) ^ 2 ≤
      4 * (L : ℝ) * (1 + Real.log (L : ℝ)) * Real.log (L : ℝ) := by
    have := mul_le_mul_of_nonneg_right hsq_le hlogL_pos.le
    have h1 : (9 / 2) * ((L : ℝ) / Real.log (L : ℝ)) * (Real.log (L : ℝ) - 1) ^ 2 *
        Real.log (L : ℝ) = (9 / 2) * (L : ℝ) * (Real.log (L : ℝ) - 1) ^ 2 := by
      field_simp
    linarith
  have hcancel : (9 / 2) * (Real.log (L : ℝ) - 1) ^ 2 ≤
      4 * (1 + Real.log (L : ℝ)) * Real.log (L : ℝ) := by
    nlinarith
  -- For x = log L > 27: (9/2)(x - 1)^2 - 4 x (1 + x) = (1/2) x^2 - 13 x + 9/2 > 0
  nlinarith

/-- **Erdős (1941) Infinite Sidon `liminf` Theorem (`B_2` Analogue of Erdős #41):**
For every infinite Sidon set `A ⊆ ℕ`, `liminf_{N → ∞} |A ∩ [1, N]| / √N = 0`. -/
theorem ppl124_erdos1941_sidon_liminf_sqrt_zero (A : Set ℕ)
    (hInf : A.Infinite)
    (hSidon : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
      a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) :
    liminf (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt (N : ℝ)) atTop = 0 := by
  refine liminf_eq_zero_of_nonneg_of_frequently_le (fun N => by positivity) fun ε hε => ?_
  have hfreq := ppl124_erdos1941_sidon_liminf_log A hInf hSidon
  have hev : ∀ᶠ N : ℕ in atTop, 6 / Real.sqrt (Real.log (N : ℝ)) ≤ ε ∧ 2 ≤ N := by
    have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ N : ℕ in atTop, (6 / ε) ^ 2 + 1 ≤ Real.log (N : ℝ) :=
      hlog_top.eventually (eventually_ge_atTop _)
    filter_upwards [h1, eventually_ge_atTop 2] with N hN hN2
    refine ⟨?_, hN2⟩
    have hlog_pos : 0 < Real.log (N : ℝ) := by
      have : (0 : ℝ) ≤ (6 / ε) ^ 2 := sq_nonneg _
      linarith
    have hsqrt_ge : 6 / ε ≤ Real.sqrt (Real.log (N : ℝ)) := by
      calc 6 / ε = Real.sqrt ((6 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_le_sqrt (by linarith)
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hlog_pos)]
    have := mul_le_mul_of_nonneg_left hsqrt_ge hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  refine (hfreq.and_eventually hev).mono fun N ⟨hN, hεN, hN2⟩ => ?_
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
  rw [div_le_iff₀ hsqrtN_pos]
  calc ((A ∩ Set.Icc 1 N).ncard : ℝ)
      ≤ 6 * Real.sqrt ((N : ℝ) / Real.log (N : ℝ)) := hN
    _ = (6 / Real.sqrt (Real.log (N : ℝ))) * Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_div hN_pos.le]; ring
    _ ≤ ε * Real.sqrt (N : ℝ) := mul_le_mul_of_nonneg_right hεN hsqrtN_pos.le

/-!
## Part II — Infinite Even-`B_{2k}` Oscillation (`B_4` & General `B_{2k}`), Odd-`B_3` Barrier & `B_3` Upper Bound (PPL 168 / #41)
-/

private lemma finset_val_sum_eq (X : Finset ℕ) : X.val.sum = ∑ x ∈ X, x := by
  change X.val.sum = (X.val.map id).sum
  simp

private lemma multiset_card_2k_sum_inj_half {k : ℕ} {A : Set ℕ}
    (hB2k : ∀ s t : Multiset ℕ, s.card = 2 * k → t.card = 2 * k →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t)
    {X Y : Finset ℕ} (hXA : ∀ x ∈ X, x ∈ A) (hYA : ∀ y ∈ Y, y ∈ A)
    (hXc : X.card = k) (hYc : Y.card = k) (hsum : ∑ x ∈ X, x = ∑ y ∈ Y, y) :
    X = Y := by
  have h1 : (X.val + X.val).card = 2 * k := by simp [hXc]; omega
  have h2 : (X.val + Y.val).card = 2 * k := by simp [hXc, hYc]; omega
  have h3 : ∀ x ∈ X.val + X.val, x ∈ A := by
    intro x hx; rcases Multiset.mem_add.mp hx with h | h <;> exact hXA x h
  have h4 : ∀ x ∈ X.val + Y.val, x ∈ A := by
    intro x hx; rcases Multiset.mem_add.mp hx with h | h
    · exact hXA x h
    · exact hYA x h
  have h5 : (X.val + X.val).sum = (X.val + Y.val).sum := by
    simp only [Multiset.sum_add, finset_val_sum_eq, hsum]
  have heq := hB2k (X.val + X.val) (X.val + Y.val) h1 h2 h3 h4 h5
  have hval : X.val = Y.val := add_left_cancel heq
  exact Finset.val_injective hval

private lemma multiset_card_2k_disjoint_diff_inj {k : ℕ} {A : Set ℕ}
    (hB2k : ∀ s t : Multiset ℕ, s.card = 2 * k → t.card = 2 * k →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t)
    {X₁ Y₁ X₂ Y₂ : Finset ℕ}
    (hX₁A : ∀ x ∈ X₁, x ∈ A) (hY₁A : ∀ x ∈ Y₁, x ∈ A)
    (hX₂A : ∀ x ∈ X₂, x ∈ A) (hY₂A : ∀ x ∈ Y₂, x ∈ A)
    (hX₁c : X₁.card = k) (hY₁c : Y₁.card = k) (hX₂c : X₂.card = k) (hY₂c : Y₂.card = k)
    (hD₁ : Disjoint X₁ Y₁) (hD₂ : Disjoint X₂ Y₂)
    (hsum : (∑ x ∈ X₁, x) + (∑ y ∈ Y₂, y) = (∑ x ∈ X₂, x) + (∑ y ∈ Y₁, y)) :
    X₁ = X₂ ∧ Y₁ = Y₂ := by
  have h1 : (X₁.val + Y₂.val).card = 2 * k := by simp [hX₁c, hY₂c]; omega
  have h2 : (X₂.val + Y₁.val).card = 2 * k := by simp [hX₂c, hY₁c]; omega
  have h3 : ∀ x ∈ X₁.val + Y₂.val, x ∈ A := by
    intro x hx; rcases Multiset.mem_add.mp hx with h | h
    · exact hX₁A x h
    · exact hY₂A x h
  have h4 : ∀ x ∈ X₂.val + Y₁.val, x ∈ A := by
    intro x hx; rcases Multiset.mem_add.mp hx with h | h
    · exact hX₂A x h
    · exact hY₁A x h
  have h5 : (X₁.val + Y₂.val).sum = (X₂.val + Y₁.val).sum := by
    simp only [Multiset.sum_add, finset_val_sum_eq]
    exact hsum
  have hm := hB2k (X₁.val + Y₂.val) (X₂.val + Y₁.val) h1 h2 h3 h4 h5
  have hcnt : ∀ u : ℕ, Multiset.count u X₁.val + Multiset.count u Y₂.val =
      Multiset.count u X₂.val + Multiset.count u Y₁.val := fun u => by
    have := congrArg (Multiset.count u) hm
    simpa [Multiset.count_add] using this
  have hmem_cnt : ∀ (S : Finset ℕ) (u : ℕ), Multiset.count u S.val = if u ∈ S then 1 else 0 := by
    intro S u
    by_cases hu : u ∈ S
    · simp only [hu, ↓reduceIte]
      exact Multiset.count_eq_one_of_mem S.nodup hu
    · simp only [hu, ↓reduceIte]
      exact Multiset.count_eq_zero.mpr hu
  constructor
  · ext u
    have hc := hcnt u
    rw [hmem_cnt X₁ u, hmem_cnt Y₂ u, hmem_cnt X₂ u, hmem_cnt Y₁ u] at hc
    have hd1 : u ∈ X₁ → u ∉ Y₁ := fun hu => Finset.disjoint_left.mp hD₁ hu
    have hd2 : u ∈ X₂ → u ∉ Y₂ := fun hu => Finset.disjoint_left.mp hD₂ hu
    by_cases h1 : u ∈ X₁ <;> by_cases h2 : u ∈ X₂ <;> by_cases h3 : u ∈ Y₁ <;> by_cases h4 : u ∈ Y₂ <;>
      simp_all
  · ext u
    have hc := hcnt u
    rw [hmem_cnt X₁ u, hmem_cnt Y₂ u, hmem_cnt X₂ u, hmem_cnt Y₁ u] at hc
    have hd1 : u ∈ X₁ → u ∉ Y₁ := fun hu => Finset.disjoint_left.mp hD₁ hu
    have hd2 : u ∈ X₂ → u ∉ Y₂ := fun hu => Finset.disjoint_left.mp hD₂ hu
    by_cases h1 : u ∈ X₁ <;> by_cases h2 : u ∈ X₂ <;> by_cases h3 : u ∈ Y₁ <;> by_cases h4 : u ∈ Y₂ <;>
      simp_all

private lemma finite_B2k_card_bound {k : ℕ} (hk : 1 ≤ k) {A : Set ℕ}
    (hB2k : ∀ s t : Multiset ℕ, s.card = 2 * k → t.card = 2 * k →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t)
    (L : ℕ) (hL : 1 ≤ L) :
    (A ∩ Set.Icc 1 (L ^ (2 * k))).ncard ≤ 4 * k * L := by
  classical
  rw [ncard_inter_Icc_eq_filter_card]
  set N := L ^ (2 * k)
  set AN := (Finset.Icc 1 N).filter (fun x => x ∈ A)
  set a := AN.card
  by_cases ha : a < 4 * k
  · have : 4 * k ≤ 4 * k * L := Nat.le_mul_of_pos_right _ (by omega)
    omega
  push Not at ha
  have hchoose : Nat.choose a (2 * k) ≤ 2 * k * N := by
    have hcard_le : (AN.powersetCard (2 * k)).card ≤ (Finset.Icc 1 (2 * k * N)).card := by
      refine Finset.card_le_card_of_injOn (fun X => ∑ x ∈ X, x) ?_ ?_
      · intro X hX
        simp only [Finset.mem_coe, Finset.mem_powersetCard] at hX
        simp only [Finset.mem_coe, Finset.mem_Icc]
        have hlo : X.card * 1 ≤ ∑ x ∈ X, x := by
          calc X.card * 1 = ∑ _x ∈ X, 1 := by simp
            _ ≤ ∑ x ∈ X, x := Finset.sum_le_sum fun x hx => by
                have := hX.1 hx; simp only [AN, Finset.mem_filter, Finset.mem_Icc] at this; omega
        have hhi : ∑ x ∈ X, x ≤ X.card * N := by
          calc ∑ x ∈ X, x ≤ ∑ _x ∈ X, N := Finset.sum_le_sum fun x hx => by
                have := hX.1 hx; simp only [AN, Finset.mem_filter, Finset.mem_Icc] at this; exact this.1.2
            _ = X.card * N := by simp
        rw [hX.2] at hlo hhi
        exact ⟨by omega, hhi⟩
      · intro X hX Y hY hsum
        simp only [Finset.mem_coe, Finset.mem_powersetCard] at hX hY
        dsimp only at hsum
        have hm := hB2k X.val Y.val hX.2 hY.2
          (fun x hx => (Finset.mem_filter.mp (hX.1 hx)).2)
          (fun y hy => (Finset.mem_filter.mp (hY.1 hy)).2)
          (by rw [finset_val_sum_eq, finset_val_sum_eq]; exact hsum)
        exact Finset.val_injective hm
    simpa [Finset.card_powersetCard, a] using hcard_le
  have hdesc := descFactorial_mul_two_pow_ge a (2 * k) (by omega)
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hfac := factorial_mul_self_le_pow (2 * k) (by omega)
  have hpow : a ^ (2 * k) ≤ (4 * k * L) ^ (2 * k) := by
    calc a ^ (2 * k)
        ≤ 2 ^ (2 * k) * ((2 * k).factorial * Nat.choose a (2 * k)) := hdesc
      _ ≤ 2 ^ (2 * k) * ((2 * k).factorial * (2 * k * L ^ (2 * k))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hchoose)
      _ = 2 ^ (2 * k) * ((2 * k).factorial * (2 * k)) * L ^ (2 * k) := by ring
      _ ≤ 2 ^ (2 * k) * (2 * k) ^ (2 * k) * L ^ (2 * k) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hfac)
      _ = (4 * k * L) ^ (2 * k) := by
          rw [← mul_pow, ← mul_pow]
          congr 1; ring
  exact le_of_pow_le_pow_left₀ (by omega : 2 * k ≠ 0) (Nat.zero_le _) hpow

/-- **General Even-`B_{2k}` Oscillation Theorem (Nash / Jia / Chen / O'Bryant Lineage):**
For every `k ≥ 1` and every infinite `B_{2k}`-set `A ⊆ ℕ` (all `2k`-element multiset sums distinct),
there exists a constant `C > 0` such that infinitely often `|A ∩ [1, N]| ≤ C * (N / log N)^{1/(2k)}`. -/
theorem ppl124_even_B2k_liminf_log (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ)
    (_hInf : A.Infinite)
    (hB2k : ∀ s t : Multiset ℕ, s.card = 2 * k → t.card = 2 * k →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t) :
    ∃ C : ℝ, 0 < C ∧ ∃ᶠ N : ℕ in atTop,
      ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤
        C * ((N : ℝ) / Real.log (N : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) := by
  classical
  -- Explicit constant C depending only on k
  let C₂ : ℝ := 2 + 2 * ((4 * k : ℝ) ^ (2 * k - 1)) + (4 * k : ℝ) ^ k
  have hC₂_pos : 0 < C₂ := by positivity
  -- Choose c large enough so (c^k / (2^k * k!))^2 / (24 * k^2) > 2 * C₂
  let K_const : ℝ := (2 ^ k * (k.factorial : ℝ)) * Real.sqrt (48 * (k : ℝ) ^ 2 * C₂) + 1
  have hK_pos : 0 < K_const := by positivity
  let C : ℝ := max (K_const ^ ((1 : ℝ) / (k : ℝ))) 2
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hCk_ge : K_const ≤ C ^ k := by
    have h1 : K_const ^ ((1 : ℝ) / (k : ℝ)) ≤ C := le_max_left _ _
    have h2 : (K_const ^ ((1 : ℝ) / (k : ℝ))) ^ k ≤ C ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK_pos.le] at h2
    have hkeq : (1 : ℝ) / (k : ℝ) * (k : ℝ) = 1 := by
      have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    rw [hkeq, Real.rpow_one] at h2
    exact h2
  refine ⟨C, hC_pos, ?_⟩
  by_contra hnot
  rw [Filter.not_frequently, Filter.eventually_atTop] at hnot
  obtain ⟨N₀, hN₀⟩ := hnot
  -- Pick a sufficiently large abstract integer L
  have hexL : ∃ L : ℕ, 2 * k ≤ L ∧ N₀ ≤ L ^ (2 * k - 1) / k ∧
      (100 : ℝ) < Real.log (L : ℝ) ∧
      (2 * k : ℝ) ≤ ((L ^ (2 * k - 1) / k : ℕ) : ℝ) / Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) ∧
      (2 * k : ℝ) ^ (2 * k) ≤ ((L ^ (2 * k - 1) / k : ℕ) : ℝ) / Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) := by
    -- As L → ∞, L^(2k-1) / (k * log(k * L^(2k))) ≥ L / (4 k^2 log L) → ∞
    have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hratio_top : Tendsto (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) atTop atTop := by
      have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
        simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h0' : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
        h0.comp tendsto_natCast_atTop_atTop
      have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) / (n : ℝ) := by
        filter_upwards [eventually_ge_atTop 2] with n hn
        exact div_pos (Real.log_pos (by exact_mod_cast hn)) (Nat.cast_pos.mpr (by omega))
      have hinv := Filter.Tendsto.inv_tendsto_nhdsGT_zero (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0' hpos)
      refine hinv.congr' ?_
      filter_upwards [eventually_ge_atTop 2] with n _
      simp [inv_div]
    let Bnd : ℝ := max (6 * (k : ℝ) ^ 2 * ((2 * k : ℝ) ^ (2 * k) + (2 * k : ℝ) + 1)) 100
    have hev := ((hlog_top.eventually (eventually_gt_atTop (100 : ℝ))).and
      (hratio_top.eventually (eventually_ge_atTop Bnd))).and
      ((eventually_ge_atTop (max (2 * k) (k * N₀ + k))).and (eventually_ge_atTop 2))
    obtain ⟨L, ⟨hlogL, hratL⟩, ⟨hL_ge, hL2⟩⟩ := hev.exists
    have hL2k : 2 * k ≤ L := (le_max_left _ _).trans hL_ge
    have hLN0 : k * N₀ + k ≤ L := (le_max_right _ _).trans hL_ge
    have hLpow_ge : L ≤ L ^ (2 * k - 1) := by
      conv_lhs => rw [← pow_one L]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hdiv_ge_N0 : N₀ ≤ L ^ (2 * k - 1) / k := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlogL_pos : 0 < Real.log (L : ℝ) := by linarith
    have hkL_le : ((k * L ^ (2 * k) : ℕ) : ℝ) ≤ (L : ℝ) ^ (2 * k + 1) := by
      push_cast
      have hkle : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show k ≤ L by omega)
      calc (k : ℝ) * (L : ℝ) ^ (2 * k)
          ≤ (L : ℝ) * (L : ℝ) ^ (2 * k) := mul_le_mul_of_nonneg_right hkle (by positivity)
        _ = (L : ℝ) ^ (2 * k + 1) := by rw [pow_succ]; ring
    have hlog_ub : Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) ≤ (3 * (k : ℝ)) * Real.log (L : ℝ) := by
      have hkL_pos : (0 : ℝ) < ((k * L ^ (2 * k) : ℕ) : ℝ) := Nat.cast_pos.mpr (by positivity)
      calc Real.log ((k * L ^ (2 * k) : ℕ) : ℝ)
          ≤ Real.log ((L : ℝ) ^ (2 * k + 1)) := Real.log_le_log hkL_pos hkL_le
        _ = ((2 * k + 1 : ℕ) : ℝ) * Real.log (L : ℝ) := Real.log_pow _ _
        _ ≤ (3 * (k : ℝ)) * Real.log (L : ℝ) := by
            have : ((2 * k + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) := by
              push_cast; linarith [show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk]
            exact mul_le_mul_of_nonneg_right this hlogL_pos.le
    have hlog_pos : 0 < Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) := by
      apply Real.log_pos
      have : 2 ≤ k * L ^ (2 * k) := by
        calc 2 ≤ L := hL2
          _ = L ^ 1 := (pow_one L).symm
          _ ≤ L ^ (2 * k) := Nat.pow_le_pow_right (by omega : 1 ≤ L) (by omega)
          _ = 1 * L ^ (2 * k) := (one_mul _).symm
          _ ≤ k * L ^ (2 * k) := Nat.mul_le_mul_right _ hk
      exact_mod_cast this
    have hdiv_lb : (L : ℝ) / (2 * (k : ℝ)) ≤ ((L ^ (2 * k - 1) / k : ℕ) : ℝ) := by
      have h1 : L ≤ 2 * (k * (L ^ (2 * k - 1) / k)) := by
        have hmod : L ^ (2 * k - 1) < k * (L ^ (2 * k - 1) / k) + k := by
          have := Nat.div_add_mod (L ^ (2 * k - 1)) k
          have := Nat.mod_lt (L ^ (2 * k - 1)) (by omega : 0 < k)
          omega
        have hk_le : k ≤ k * (L ^ (2 * k - 1) / k) := by
          have h1' : 1 ≤ L ^ (2 * k - 1) / k := by
            rw [Nat.le_div_iff_mul_le (by omega)]
            calc 1 * k = k := one_mul k
              _ ≤ L := by omega
              _ ≤ L ^ (2 * k - 1) := hLpow_ge
          nlinarith
        omega
      have h1R : (L : ℝ) ≤ 2 * (k : ℝ) * ((L ^ (2 * k - 1) / k : ℕ) : ℝ) := by
        have : (L : ℝ) ≤ ((2 * (k * (L ^ (2 * k - 1) / k)) : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at this; linarith
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hquot_ge : (2 * k : ℝ) ^ (2 * k) + (2 * k : ℝ) + 1 ≤
        ((L ^ (2 * k - 1) / k : ℕ) : ℝ) / Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) := by
      have hB : 6 * (k : ℝ) ^ 2 * ((2 * k : ℝ) ^ (2 * k) + (2 * k : ℝ) + 1) ≤ (L : ℝ) / Real.log (L : ℝ) :=
        (le_max_left _ _).trans hratL
      have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
      calc (2 * k : ℝ) ^ (2 * k) + (2 * k : ℝ) + 1
          ≤ (L : ℝ) / Real.log (L : ℝ) / (6 * (k : ℝ) ^ 2) := by
              rw [le_div_iff₀ (by positivity)]; linarith
        _ = ((L : ℝ) / (2 * (k : ℝ))) / (3 * (k : ℝ) * Real.log (L : ℝ)) := by ring
        _ ≤ ((L ^ (2 * k - 1) / k : ℕ) : ℝ) / Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) :=
              div_le_div₀ (by positivity) hdiv_lb hlog_pos hlog_ub
    exact ⟨L, hL2k, hdiv_ge_N0, hlogL, by linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * k) (2 * k)], by linarith⟩
  obtain ⟨L, hL2k, hdiv_ge_N0, hlogL_gt, hquot_ge1, hquot_ge2⟩ := hexL
  have hL_ge2 : 2 ≤ L := by omega
  have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlogL_pos : 0 < Real.log (L : ℝ) := by linarith
  -- Parameters: N = L^(2k), M = L^(2k-1), R = k * L, so R * M = k * N
  set N : ℕ := L ^ (2 * k)
  set M : ℕ := L ^ (2 * k - 1)
  set R : ℕ := k * L
  have hRM : R * M = k * N := by
    dsimp only [R, M, N]
    rw [mul_assoc, ← pow_succ']
    congr 2; omega
  have hM_pos : 0 < M := Nat.pow_pos (by omega)
  have hR_ge2 : 2 ≤ R := by dsimp only [R]; nlinarith
  -- k-fold sumset S_N of A ∩ [1, N]
  let AN : Finset ℕ := (Finset.Icc 1 N).filter (fun x => x ∈ A)
  let a : ℕ := AN.card
  have ha_le : a ≤ 4 * k * L := by
    have hfin := finite_B2k_card_bound hk hB2k L (by omega)
    rw [ncard_inter_Icc_eq_filter_card] at hfin
    exact hfin
  let sumOf : Finset ℕ → ℕ := fun X => ∑ x ∈ X, x
  let SN : Finset ℕ := (AN.powersetCard k).image sumOf
  have hsum_inj : Set.InjOn sumOf (AN.powersetCard k : Set (Finset ℕ)) := by
    intro X hX Y hY hsum
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hX hY
    exact multiset_card_2k_sum_inj_half hB2k
      (fun x hx => (Finset.mem_filter.mp (hX.1 hx)).2)
      (fun y hy => (Finset.mem_filter.mp (hY.1 hy)).2) hX.2 hY.2 hsum
  have hSN_sub : SN ⊆ Finset.Icc 1 (k * N) := by
    intro s hs
    simp only [SN, Finset.mem_image, Finset.mem_powersetCard] at hs
    obtain ⟨X, ⟨hXsub, hXc⟩, rfl⟩ := hs
    simp only [Finset.mem_Icc]
    have hlo : X.card * 1 ≤ ∑ x ∈ X, x := by
      calc X.card * 1 = ∑ _x ∈ X, 1 := by simp
        _ ≤ ∑ x ∈ X, x := Finset.sum_le_sum fun x hx => by
            have := hXsub hx; simp only [AN, Finset.mem_filter, Finset.mem_Icc] at this; omega
    have hhi : ∑ x ∈ X, x ≤ X.card * N := by
      calc ∑ x ∈ X, x ≤ ∑ _x ∈ X, N := Finset.sum_le_sum fun x hx => by
            have := hXsub hx; simp only [AN, Finset.mem_filter, Finset.mem_Icc] at this; exact this.1.2
        _ = X.card * N := by simp
    rw [hXc] at hlo hhi
    simp only [mul_one] at hlo
    exact ⟨hk.trans hlo, hhi⟩
  -- Block counts B j = |SN ∩ ((j-1)M, jM]| and partial sums T j = |SN ∩ [1, jM]|
  let blk : ℕ → Finset ℕ := fun j => SN ∩ Finset.Ioc ((j - 1) * M) (j * M)
  let B : ℕ → ℕ := fun j => (blk j).card
  let T : ℕ → ℕ := fun j => ∑ i ∈ Finset.Icc 1 j, B i
  have hT_eq : ∀ j : ℕ, 1 ≤ j → T j = (SN ∩ Finset.Icc 1 (j * M)).card := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      simp only [T, B, blk, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, zero_mul, one_mul]
      congr 1
    | succ m hm ih =>
      simp only [T] at ih ⊢
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      have hdisj : Disjoint (SN ∩ Finset.Icc 1 (m * M)) (blk (m + 1)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [blk, Finset.mem_inter, Finset.mem_Icc, Finset.mem_Ioc, Nat.add_sub_cancel] at hx1 hx2
        omega
      have hunion : (SN ∩ Finset.Icc 1 (m * M)) ∪ blk (m + 1) = SN ∩ Finset.Icc 1 ((m + 1) * M) := by
        ext x; simp only [blk, Finset.mem_union, Finset.mem_inter, Finset.mem_Icc, Finset.mem_Ioc]
        have hsucc : (m + 1 - 1) * M = m * M := by simp
        rw [hsucc]
        constructor
        · rintro (⟨hS, h1, h2⟩ | ⟨hS, h1, h2⟩)
          · exact ⟨hS, h1, by nlinarith⟩
          · exact ⟨hS, by omega, h2⟩
        · rintro ⟨hS, h1, h2⟩
          by_cases hle : x ≤ m * M
          · exact Or.inl ⟨hS, h1, hle⟩
          · exact Or.inr ⟨hS, by omega, h2⟩
      change (SN ∩ Finset.Icc 1 (m * M)).card + (blk (m + 1)).card = _
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
  -- Upper bound on ∑_{j=1}^R B(j)^2 ≤ C₂ * M
  have hsum_B2 : ∑ j ∈ Finset.Icc 1 R, ((B j : ℝ) ^ 2) ≤ C₂ * (M : ℝ) := by
    let pairsOf : ℕ → Finset (ℕ × ℕ) := fun j => ((blk j) ×ˢ (blk j)).filter (fun p => p.1 < p.2)
    have hpair_card : ∀ j, 2 * (pairsOf j).card + B j = (B j) ^ 2 := by
      intro j
      set S := blk j
      set P := pairsOf j
      have hlt_gt : ((S ×ˢ S).filter (fun p => p.2 < p.1)).card = P.card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp; simp only [P, pairsOf, Finset.mem_filter, Finset.mem_product] at hp ⊢
          exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
        · intro p₁ _ p₂ _ h; ext <;> [exact congrArg Prod.snd h; exact congrArg Prod.fst h]
        · intro p hp; simp only [P, pairsOf, Finset.mem_filter, Finset.mem_product] at hp
          exact ⟨(p.2, p.1), by simp only [S, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
      have hdiag : ((S ×ˢ S).filter (fun p => p.1 = p.2)).card = S.card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
        · intro p₁ hp₁ p₂ hp₂ h
          simp only [Finset.mem_filter] at hp₁ hp₂
          ext; exact h; exact hp₁.2.symm.trans (h.trans hp₂.2)
        · intro x hx; exact ⟨(x, x), by simp [hx], rfl⟩
      have hpart : S.card * S.card = P.card + ((S ×ˢ S).filter (fun p => p.2 < p.1)).card +
          ((S ×ˢ S).filter (fun p => p.1 = p.2)).card := by
        have h1 : S ×ˢ S = P ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1)) ∪
            ((S ×ˢ S).filter (fun p => p.1 = p.2)) := by
          ext ⟨x, y⟩; simp only [P, pairsOf, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
          constructor
          · intro h; rcases lt_trichotomy x y with hlt | heq | hgt
            · exact Or.inl (Or.inl ⟨h, hlt⟩)
            · exact Or.inr ⟨h, heq⟩
            · exact Or.inl (Or.inr ⟨h, hgt⟩)
          · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
        have hd1 : Disjoint P ((S ×ˢ S).filter (fun p => p.2 < p.1)) := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [P, pairsOf, Finset.mem_filter] at hp1 hp2; omega
        have hd2 : Disjoint (P ∪ ((S ×ˢ S).filter (fun p => p.2 < p.1)))
            ((S ×ˢ S).filter (fun p => p.1 = p.2)) := by
          rw [Finset.disjoint_left]; intro p hp1 hp2
          simp only [P, pairsOf, Finset.mem_union, Finset.mem_filter] at hp1 hp2; omega
        have hcard := congrArg Finset.card h1
        rw [Finset.card_product, Finset.card_union_of_disjoint hd2,
          Finset.card_union_of_disjoint hd1] at hcard
        exact hcard
      rw [hlt_gt, hdiag] at hpart
      change 2 * P.card + S.card = S.card ^ 2
      nlinarith
    have hdisj_pairs : (Finset.Icc 1 R : Set ℕ).PairwiseDisjoint pairsOf := by
      intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp1 hp2
      simp only [pairsOf, blk, Finset.mem_filter, Finset.mem_product, Finset.mem_inter,
        Finset.mem_Ioc] at hp1 hp2
      rcases lt_or_gt_of_ne hne with h | h
      · have hle : j₁ ≤ j₂ - 1 := by omega
        have := Nat.mul_le_mul_right M hle
        omega
      · have hle : j₂ ≤ j₁ - 1 := by omega
        have := Nat.mul_le_mul_right M hle
        omega
    -- Map each pair (s₁, s₂) in biUnion pairsOf to its unique (Y, X) in powersetCard k
    let AllPairs : Finset (ℕ × ℕ) := (Finset.Icc 1 R).biUnion pairsOf
    have hAllPairs_eq : ∑ j ∈ Finset.Icc 1 R, (pairsOf j).card = AllPairs.card :=
      (Finset.card_biUnion hdisj_pairs).symm
    -- Every pair (s₁, s₂) ∈ AllPairs comes from unique X, Y ∈ AN.powersetCard k with sumOf Y < sumOf X and sumOf X - sumOf Y ≤ M
    let XYAll : Finset (Finset ℕ × Finset ℕ) :=
      ((AN.powersetCard k) ×ˢ (AN.powersetCard k)).filter
        (fun P => sumOf P.1 < sumOf P.2 ∧ sumOf P.2 - sumOf P.1 ≤ M)
    have hAllPairs_le_XY : AllPairs.card ≤ XYAll.card := by
      -- Map XYAll → AllPairs is surjective onto AllPairs via (Y, X) ↦ (sumOf Y, sumOf X)
      have hsub : AllPairs ⊆ XYAll.image (fun P => (sumOf P.1, sumOf P.2)) := by
        intro p hp
        simp only [AllPairs, Finset.mem_biUnion, pairsOf, blk, Finset.mem_filter,
          Finset.mem_product, Finset.mem_inter, Finset.mem_Ioc, SN, Finset.mem_image] at hp
        obtain ⟨j, hj, ⟨⟨⟨Y, hY, hYs⟩, hYlo, hYhi⟩, ⟨⟨X, hX, hXs⟩, hXlo, hXhi⟩⟩, hlt⟩ := hp
        simp only [Finset.mem_image, XYAll, Finset.mem_filter, Finset.mem_product]
        have hmul : (j - 1) * M + M = j * M := by
          rw [← Nat.succ_mul]; congr 1; simp only [Finset.mem_Icc] at hj; omega
        refine ⟨(Y, X), ⟨⟨hY, hX⟩, ?_, ?_⟩, Prod.ext hYs hXs⟩
        · dsimp only; omega
        · dsimp only; omega
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    -- Split XYAll into Disjoint vs Overlapping
    let XYDisj := XYAll.filter (fun P => Disjoint P.1 P.2)
    let XYOver := XYAll.filter (fun P => ¬ Disjoint P.1 P.2)
    have hXY_split : XYAll.card = XYDisj.card + XYOver.card := by
      have h := Finset.card_filter_add_card_filter_not (s := XYAll) (p := fun P => Disjoint P.1 P.2)
      exact h.symm
    -- Bound XYDisj.card ≤ M via multiset_card_2k_disjoint_diff_inj
    have hXYDisj_le : XYDisj.card ≤ M := by
      have hcard_le : XYDisj.card ≤ (Finset.Icc 1 M).card := by
        refine Finset.card_le_card_of_injOn (fun P => sumOf P.2 - sumOf P.1) ?_ ?_
        · intro P hP
          simp only [XYDisj, XYAll, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hP ⊢
          omega
        · intro P₁ hP₁ P₂ hP₂ heq
          dsimp only at heq
          simp only [XYDisj, XYAll, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_powersetCard] at hP₁ hP₂
          have hsum : sumOf P₁.2 + sumOf P₂.1 = sumOf P₂.2 + sumOf P₁.1 := by omega
          have ⟨h2, h1⟩ := multiset_card_2k_disjoint_diff_inj hB2k
            (fun x hx => (Finset.mem_filter.mp (hP₁.1.1.2.1 hx)).2)
            (fun x hx => (Finset.mem_filter.mp (hP₁.1.1.1.1 hx)).2)
            (fun x hx => (Finset.mem_filter.mp (hP₂.1.1.2.1 hx)).2)
            (fun x hx => (Finset.mem_filter.mp (hP₂.1.1.1.1 hx)).2)
            hP₁.1.1.2.2 hP₁.1.1.1.2 hP₂.1.1.2.2 hP₂.1.1.1.2
            hP₁.2.symm hP₂.2.symm hsum
          exact Prod.ext h1 h2
      simpa using hcard_le
    -- Bound XYOver.card ≤ a * (a.choose (k - 1))^2 ≤ (4k)^(2k-1) * M
    have hXYOver_le : XYOver.card ≤ (4 * k) ^ (2 * k - 1) * M := by
      -- Map each overlapping (Y, X) to (z, Y.erase z, X.erase z) where z = (Y ∩ X).min'
      let Target : Finset (ℕ × Finset ℕ × Finset ℕ) :=
        AN ×ˢ ((AN.powersetCard (k - 1)) ×ˢ (AN.powersetCard (k - 1)))
      have hcard_le : XYOver.card ≤ Target.card := by
        have hmem_inter : ∀ P ∈ XYOver, (P.1 ∩ P.2).Nonempty := by
          intro P hP
          simp only [XYOver, Finset.mem_filter] at hP
          exact Finset.not_disjoint_iff_nonempty_inter.mp hP.2
        refine Finset.card_le_card_of_injOn
          (fun P => if h : (P.1 ∩ P.2).Nonempty then
            ((P.1 ∩ P.2).min' h, P.1.erase ((P.1 ∩ P.2).min' h), P.2.erase ((P.1 ∩ P.2).min' h))
            else (0, ∅, ∅)) ?_ ?_
        · intro P hP
          have hne := hmem_inter P hP
          simp only [hne, ↓reduceDIte, Target, Finset.mem_coe, Finset.mem_product,
            Finset.mem_powersetCard]
          simp only [XYOver, XYAll, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_powersetCard] at hP
          set z := (P.1 ∩ P.2).min' hne
          have hz_inter : z ∈ P.1 ∩ P.2 := Finset.min'_mem _ hne
          have hz1 : z ∈ P.1 := (Finset.mem_inter.mp hz_inter).1
          have hz2 : z ∈ P.2 := (Finset.mem_inter.mp hz_inter).2
          refine ⟨hP.1.1.1.1 hz1, ⟨(Finset.erase_subset z P.1).trans hP.1.1.1.1, ?_⟩,
            ⟨(Finset.erase_subset z P.2).trans hP.1.1.2.1, ?_⟩⟩
          · rw [Finset.card_erase_of_mem hz1, hP.1.1.1.2]
          · rw [Finset.card_erase_of_mem hz2, hP.1.1.2.2]
        · intro P₁ hP₁ P₂ hP₂ heq
          have hne1 := hmem_inter P₁ hP₁
          have hne2 := hmem_inter P₂ hP₂
          simp only [hne1, hne2, ↓reduceDIte, Prod.mk.injEq] at heq
          obtain ⟨hz, hY, hX⟩ := heq
          set z₁ := (P₁.1 ∩ P₁.2).min' hne1
          set z₂ := (P₂.1 ∩ P₂.2).min' hne2
          have hz1_1 : z₁ ∈ P₁.1 := (Finset.mem_inter.mp (Finset.min'_mem _ hne1)).1
          have hz1_2 : z₁ ∈ P₁.2 := (Finset.mem_inter.mp (Finset.min'_mem _ hne1)).2
          have hz2_1 : z₂ ∈ P₂.1 := (Finset.mem_inter.mp (Finset.min'_mem _ hne2)).1
          have hz2_2 : z₂ ∈ P₂.2 := (Finset.mem_inter.mp (Finset.min'_mem _ hne2)).2
          have h1 : P₁.1 = P₂.1 := by
            rw [← Finset.insert_erase hz1_1, ← Finset.insert_erase hz2_1, hY, hz]
          have h2 : P₁.2 = P₂.2 := by
            rw [← Finset.insert_erase hz1_2, ← Finset.insert_erase hz2_2, hX, hz]
          exact Prod.ext h1 h2
      have hTarget_card : Target.card ≤ a ^ (2 * k - 1) := by
        simp only [Target, Finset.card_product, Finset.card_powersetCard, a]
        have hch : AN.card.choose (k - 1) ≤ AN.card ^ (k - 1) := Nat.choose_le_pow _ _
        calc AN.card * (AN.card.choose (k - 1) * AN.card.choose (k - 1))
            ≤ AN.card * (AN.card ^ (k - 1) * AN.card ^ (k - 1)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul hch hch)
          _ = AN.card ^ (1 + (k - 1) + (k - 1)) := by rw [pow_add, pow_add, pow_one]; ring
          _ = AN.card ^ (2 * k - 1) := by congr 1; omega
      calc XYOver.card ≤ Target.card := hcard_le
        _ ≤ a ^ (2 * k - 1) := hTarget_card
        _ ≤ (4 * k * L) ^ (2 * k - 1) := Nat.pow_le_pow_left ha_le _
        _ = (4 * k) ^ (2 * k - 1) * M := by rw [mul_pow]
    -- Bound T R = SN.card ≤ a^k ≤ (4k)^k * M
    have hTR_le : T R ≤ (4 * k) ^ k * M := by
      rw [hT_eq R (by omega), hRM]
      have hcap : SN ∩ Finset.Icc 1 (k * N) = SN := Finset.inter_eq_left.mpr hSN_sub
      rw [hcap]
      have hSN_card : SN.card ≤ a ^ k := by
        calc SN.card ≤ (AN.powersetCard k).card := Finset.card_image_le
          _ = a.choose k := Finset.card_powersetCard k AN
          _ ≤ a ^ k := Nat.choose_le_pow a k
      have hLk : L ^ k ≤ M := Nat.pow_le_pow_right (by omega) (by omega)
      calc SN.card ≤ a ^ k := hSN_card
        _ ≤ (4 * k * L) ^ k := Nat.pow_le_pow_left ha_le k
        _ = (4 * k) ^ k * L ^ k := mul_pow _ _ _
        _ ≤ (4 * k) ^ k * M := Nat.mul_le_mul_left _ hLk
    have hsum_nat : ∑ j ∈ Finset.Icc 1 R, (B j) ^ 2 ≤
        (2 + 2 * (4 * k) ^ (2 * k - 1) + (4 * k) ^ k) * M := by
      have heq : ∑ j ∈ Finset.Icc 1 R, (B j) ^ 2 =
          2 * (∑ j ∈ Finset.Icc 1 R, (pairsOf j).card) + T R := by
        simp only [T, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => (hpair_card j).symm
      rw [heq, hAllPairs_eq]
      have hpairs : AllPairs.card ≤ M + (4 * k) ^ (2 * k - 1) * M := by
        omega
      nlinarith
    have hcast : ((∑ j ∈ Finset.Icc 1 R, (B j) ^ 2 : ℕ) : ℝ) ≤
        (((2 + 2 * (4 * k) ^ (2 * k - 1) + (4 * k) ^ k) * M : ℕ) : ℝ) := by
      exact_mod_cast hsum_nat
    push_cast at hcast
    exact hcast
  -- Lower bound on T j for all j ∈ [1, R]
  let coeff : ℝ := (C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) *
    Real.sqrt ((M : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ)))
  have hcoeff_pos : 0 < coeff := by positivity
  have hT_lower : ∀ j ∈ Finset.Icc 1 R, coeff * Real.sqrt (j : ℝ) ≤ (T j : ℝ) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [hT_eq j hj.1]
    set nj : ℕ := j * M / k
    have hnj_ge_div : L ^ (2 * k - 1) / k ≤ nj := by
      exact Nat.div_le_div_right (by dsimp only [M]; exact Nat.le_mul_of_pos_left _ (by omega))
    have hnj_ge_N0 : N₀ ≤ nj := hdiv_ge_N0.trans hnj_ge_div
    have hnj_le_kN : nj ≤ k * N := by
      have h1 : j * M ≤ R * M := Nat.mul_le_mul_right M hj.2
      rw [hRM] at h1
      exact (Nat.div_le_self _ _).trans h1
    have hnj_le_N : nj ≤ N := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      have h1 : j * M ≤ R * M := Nat.mul_le_mul_right M hj.2
      rw [hRM] at h1
      omega
    -- Every k-subset of A ∩ [1, nj] maps injectively into SN ∩ [1, j * M]
    let Anj : Finset ℕ := (Finset.Icc 1 nj).filter (fun x => x ∈ A)
    have hchoose_le_T : Nat.choose Anj.card k ≤ (SN ∩ Finset.Icc 1 (j * M)).card := by
      have hsub_img : (Anj.powersetCard k).image sumOf ⊆ SN ∩ Finset.Icc 1 (j * M) := by
        intro s hs
        simp only [Finset.mem_image, Finset.mem_powersetCard] at hs
        obtain ⟨X, ⟨hXsub, hXc⟩, rfl⟩ := hs
        have hX_AN : X ⊆ AN := fun x hx => by
          have := hXsub hx
          simp only [Anj, AN, Finset.mem_filter, Finset.mem_Icc] at this ⊢
          exact ⟨⟨this.1.1, this.1.2.trans hnj_le_N⟩, this.2⟩
        simp only [SN, Finset.mem_inter, Finset.mem_image, Finset.mem_powersetCard, Finset.mem_Icc]
        refine ⟨⟨X, ⟨hX_AN, hXc⟩, rfl⟩, ?_, ?_⟩
        · have hlo : X.card * 1 ≤ ∑ x ∈ X, x := by
            calc X.card * 1 = ∑ _x ∈ X, 1 := by simp
              _ ≤ ∑ x ∈ X, x := Finset.sum_le_sum fun x hx => by
                  have := hXsub hx; simp only [Anj, Finset.mem_filter, Finset.mem_Icc] at this; omega
          rw [hXc, mul_one] at hlo
          exact hk.trans hlo
        · have hhi : ∑ x ∈ X, x ≤ X.card * nj := by
            calc ∑ x ∈ X, x ≤ ∑ _x ∈ X, nj := Finset.sum_le_sum fun x hx => by
                  have := hXsub hx; simp only [Anj, Finset.mem_filter, Finset.mem_Icc] at this; exact this.1.2
              _ = X.card * nj := by simp
          rw [hXc] at hhi
          have hknj : k * nj ≤ j * M := Nat.mul_div_le (j * M) k
          exact hhi.trans hknj
      have hinj_Anj : Set.InjOn sumOf (Anj.powersetCard k : Set (Finset ℕ)) :=
        hsum_inj.mono fun X hX => by
          simp only [Finset.mem_coe, Finset.mem_powersetCard] at hX ⊢
          refine ⟨fun x hx => ?_, hX.2⟩
          have := hX.1 hx
          simp only [Anj, AN, Finset.mem_filter, Finset.mem_Icc] at this ⊢
          exact ⟨⟨this.1.1, this.1.2.trans hnj_le_N⟩, this.2⟩
      calc Nat.choose Anj.card k = (Anj.powersetCard k).card := (Finset.card_powersetCard k Anj).symm
        _ = ((Anj.powersetCard k).image sumOf).card := (Finset.card_image_of_injOn hinj_Anj).symm
        _ ≤ (SN ∩ Finset.Icc 1 (j * M)).card := Finset.card_le_card hsub_img
    -- Contradiction hypothesis gives lower bound on Anj.card
    have hlt := hN₀ nj hnj_ge_N0
    push Not at hlt
    rw [ncard_inter_Icc_eq_filter_card] at hlt
    -- Bound nj ≥ j * M / (2k) and log nj ≤ 3 k log L
    have hnj_lb : ((j * M : ℕ) : ℝ) / (2 * (k : ℝ)) ≤ (nj : ℝ) := by
      have h1 : j * M ≤ 2 * (k * nj) := by
        have hmod : j * M < k * nj + k := by
          have hdm := Nat.div_add_mod (j * M) k
          have hml := Nat.mod_lt (j * M) (by omega : 0 < k)
          change k * nj + j * M % k = j * M at hdm
          omega
        have hk_le : k ≤ k * nj := by
          have h1' : 1 ≤ nj := by
            have hLpow : L ≤ M := by
              dsimp only [M]; conv_lhs => rw [← pow_one L]
              exact Nat.pow_le_pow_right (by omega : 1 ≤ L) (by omega)
            have : L ≤ j * M := hLpow.trans (Nat.le_mul_of_pos_left _ (by omega))
            have : 1 ≤ j * M / k := by rw [Nat.le_div_iff_mul_le (by omega)]; omega
            exact this
          nlinarith
        omega
      have h1R : ((j * M : ℕ) : ℝ) ≤ 2 * (k : ℝ) * (nj : ℝ) := by
        have : ((j * M : ℕ) : ℝ) ≤ ((2 * (k * nj) : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at this ⊢; linarith
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hlog_nj_pos : 0 < Real.log (nj : ℝ) := by
      apply Real.log_pos
      have h2le : 2 ≤ nj := by
        have hLpow : L ≤ M := by
          dsimp only [M]; conv_lhs => rw [← pow_one L]
          exact Nat.pow_le_pow_right (by omega : 1 ≤ L) (by omega)
        have h2k : 2 * k ≤ j * M := by nlinarith [hj.1]
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      exact_mod_cast h2le
    have hlog_nj_le : Real.log (nj : ℝ) ≤ 3 * (k : ℝ) * Real.log (L : ℝ) := by
      have hnj_pos : (0 : ℝ) < (nj : ℝ) := by
        by_contra h0; push Not at h0
        have : nj = 0 := by exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
        rw [this, Nat.cast_zero, Real.log_zero] at hlog_nj_pos; linarith
      have hle_kN : (nj : ℝ) ≤ ((k * L ^ (2 * k) : ℕ) : ℝ) := by exact_mod_cast hnj_le_kN
      have hkL_le : ((k * L ^ (2 * k) : ℕ) : ℝ) ≤ (L : ℝ) ^ (2 * k + 1) := by
        push_cast
        have hkle : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show k ≤ L by omega)
        calc (k : ℝ) * (L : ℝ) ^ (2 * k)
            ≤ (L : ℝ) * (L : ℝ) ^ (2 * k) := mul_le_mul_of_nonneg_right hkle (by positivity)
          _ = (L : ℝ) ^ (2 * k + 1) := by rw [pow_succ]; ring
      calc Real.log (nj : ℝ) ≤ Real.log ((L : ℝ) ^ (2 * k + 1)) :=
            Real.log_le_log hnj_pos (hle_kN.trans hkL_le)
        _ = ((2 * k + 1 : ℕ) : ℝ) * Real.log (L : ℝ) := Real.log_pow _ _
        _ ≤ 3 * (k : ℝ) * Real.log (L : ℝ) := by
            have : ((2 * k + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) := by
              push_cast; linarith [show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast hk]
            exact mul_le_mul_of_nonneg_right this hlogL_pos.le
    -- Verify Anj.card ≥ 2 * k so descFactorial bound applies
    have hAnj_ge_2k : 2 * k ≤ Anj.card := by
      have hq : (2 * k : ℝ) ^ (2 * k) ≤ (nj : ℝ) / Real.log (nj : ℝ) := by
        have hlog_kN_pos : 0 < Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) := by
          apply Real.log_pos
          have : 2 ≤ k * L ^ (2 * k) := by
            have : 2 ≤ L ^ (2 * k) := by
              calc 2 ≤ L := hL_ge2
                _ = L ^ 1 := (pow_one L).symm
                _ ≤ L ^ (2 * k) := Nat.pow_le_pow_right (by omega : 1 ≤ L) (by omega)
            nlinarith
          exact_mod_cast this
        have hnj_ge : ((L ^ (2 * k - 1) / k : ℕ) : ℝ) ≤ (nj : ℝ) := by exact_mod_cast hnj_ge_div
        have hlog_le2 : Real.log (nj : ℝ) ≤ Real.log ((k * L ^ (2 * k) : ℕ) : ℝ) := by
          apply Real.log_le_log
          · by_contra h0; push Not at h0
            have : nj = 0 := by exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
            rw [this, Nat.cast_zero, Real.log_zero] at hlog_nj_pos; linarith
          · exact_mod_cast hnj_le_kN
        exact hquot_ge2.trans (div_le_div₀ (Nat.cast_nonneg _) hnj_ge hlog_nj_pos hlog_le2)
      have hrpow_ge : (2 * k : ℝ) ≤ ((nj : ℝ) / Real.log (nj : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) := by
        have h1 := Real.rpow_le_rpow (by positivity) hq (by positivity : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)))
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h1
        have hexp : ((2 * k : ℕ) : ℝ) * (1 / (2 * (k : ℝ))) = 1 := by
          push_cast; have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); field_simp
        rw [hexp, Real.rpow_one] at h1
        exact h1
      have hC_ge1 : (1 : ℝ) ≤ C := (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_right _ _)
      have hcard_R : (2 * k : ℝ) < (Anj.card : ℝ) := by
        calc (2 * k : ℝ) = 1 * (2 * k : ℝ) := (one_mul _).symm
          _ ≤ C * ((nj : ℝ) / Real.log (nj : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) :=
              mul_le_mul hC_ge1 hrpow_ge (by positivity) hC_pos.le
          _ < (Anj.card : ℝ) := hlt
      have hnat : 2 * k < Anj.card := by exact_mod_cast hcard_R
      omega
    -- Use descFactorial_mul_two_pow_ge: (Anj.card)^k / (2^k * k!) ≤ choose Anj.card k
    have hdesc := descFactorial_mul_two_pow_ge Anj.card k hAnj_ge_2k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
    have hdesc_R : ((Anj.card : ℝ) ^ k) ≤
        ((2 : ℝ) ^ k * (k.factorial : ℝ)) * ((Nat.choose Anj.card k : ℕ) : ℝ) := by
      have : ((Anj.card ^ k : ℕ) : ℝ) ≤ ((2 ^ k * (k.factorial * Nat.choose Anj.card k) : ℕ) : ℝ) := by
        exact_mod_cast hdesc
      push_cast at this; linarith
    have hAnj_pow_ge : C ^ k * Real.sqrt (((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ))) ≤
        (Anj.card : ℝ) ^ k := by
      have hratio_le : ((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ)) ≤
          (nj : ℝ) / Real.log (nj : ℝ) := by
        calc ((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ))
            = (((j * M : ℕ) : ℝ) / (2 * (k : ℝ))) / (3 * (k : ℝ) * Real.log (L : ℝ)) := by ring
          _ ≤ (nj : ℝ) / Real.log (nj : ℝ) :=
              div_le_div₀ (by positivity) hnj_lb hlog_nj_pos hlog_nj_le
      have hpow_le : (C * ((nj : ℝ) / Real.log (nj : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ)))) ^ k ≤
          (Anj.card : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hlt.le k
      have hrpow_k : (((nj : ℝ) / Real.log (nj : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ)))) ^ k =
          Real.sqrt ((nj : ℝ) / Real.log (nj : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg (Nat.cast_nonneg _) hlog_nj_pos.le)]
        have hexp : (1 : ℝ) / (2 * (k : ℝ)) * (k : ℝ) = 1 / 2 := by
          have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); field_simp
        rw [hexp, ← Real.sqrt_eq_rpow]
      rw [mul_pow, hrpow_k] at hpow_le
      have hsq_le : Real.sqrt (((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ))) ≤
          Real.sqrt ((nj : ℝ) / Real.log (nj : ℝ)) := Real.sqrt_le_sqrt hratio_le
      calc C ^ k * Real.sqrt (((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ)))
          ≤ C ^ k * Real.sqrt ((nj : ℝ) / Real.log (nj : ℝ)) :=
            mul_le_mul_of_nonneg_left hsq_le (by positivity)
        _ ≤ (Anj.card : ℝ) ^ k := hpow_le
    have hcoeff_eq : coeff * Real.sqrt (j : ℝ) =
        (C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) *
          Real.sqrt (((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ))) := by
      dsimp only [coeff]
      rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
      congr 2; push_cast; ring
    rw [hcoeff_eq]
    have hT_R : ((Nat.choose Anj.card k : ℕ) : ℝ) ≤ ((SN ∩ Finset.Icc 1 (j * M)).card : ℝ) := by
      exact_mod_cast hchoose_le_T
    have hden_pos : (0 : ℝ) < (2 : ℝ) ^ k * (k.factorial : ℝ) := by positivity
    calc (C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) *
            Real.sqrt (((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ)))
        = (C ^ k * Real.sqrt (((j * M : ℕ) : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ)))) /
            ((2 : ℝ) ^ k * (k.factorial : ℝ)) := by ring
      _ ≤ (Anj.card : ℝ) ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ)) :=
          div_le_div_of_nonneg_right hAnj_pow_ge hden_pos.le
      _ ≤ ((Nat.choose Anj.card k : ℕ) : ℝ) := by
          rw [div_le_iff₀ hden_pos]; linarith
      _ ≤ ((SN ∩ Finset.Icc 1 (j * M)).card : ℝ) := hT_R
  -- Combine Abel summation + Cauchy-Schwarz on ∑_{j=1}^R B(j) / √j
  let S_ab : ℝ := ∑ j ∈ Finset.Icc 1 R, (B j : ℝ) / Real.sqrt (j : ℝ)
  have hS_lower : (coeff / 2) * (Real.log (R : ℝ) - 1) ≤ S_ab := by
    have habel := abel_sum_inv_sqrt (fun j => (B j : ℝ)) R (by omega)
    have hT_cast : ∀ j, ∑ i ∈ Finset.Icc 1 j, (B i : ℝ) = (T j : ℝ) := fun j => by simp [T]
    have hmain : (coeff / 2) * (Real.log (R : ℝ) - 1) ≤
        ∑ j ∈ Finset.Icc 1 (R - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * (T j : ℝ) := by
      have hw := weighted_inv_sqrt_diff_lower R hR_ge2
      calc (coeff / 2) * (Real.log (R : ℝ) - 1)
          = coeff * ((Real.log (R : ℝ) - 1) / 2) := by ring
        _ ≤ coeff * (∑ j ∈ Finset.Icc 1 (R - 1),
              (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * Real.sqrt (j : ℝ)) :=
            mul_le_mul_of_nonneg_left hw hcoeff_pos.le
        _ = ∑ j ∈ Finset.Icc 1 (R - 1),
              (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
                (coeff * Real.sqrt (j : ℝ)) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
        _ ≤ ∑ j ∈ Finset.Icc 1 (R - 1),
              (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * (T j : ℝ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j ∈ Finset.Icc 1 R := by simp only [Finset.mem_Icc] at hj ⊢; omega
            have hdiff_nn : 0 ≤ 1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ) := by
              have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by
                simp only [Finset.mem_Icc] at hj; omega)
              have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj_pos
              have hsle : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) :=
                Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)
              have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hsj hsle
              linarith
            exact mul_le_mul_of_nonneg_left (hT_lower j hj') hdiff_nn
    have hTR_nn : 0 ≤ (∑ i ∈ Finset.Icc 1 R, (B i : ℝ)) / Real.sqrt (R : ℝ) :=
      div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have hSab_def : S_ab = ∑ j ∈ Finset.Icc 1 R, (B j : ℝ) / Real.sqrt (j : ℝ) := rfl
    rw [hSab_def, habel]
    have hsum_eq : ∑ j ∈ Finset.Icc 1 (R - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) *
            (∑ i ∈ Finset.Icc 1 j, (B i : ℝ)) =
        ∑ j ∈ Finset.Icc 1 (R - 1),
          (1 / Real.sqrt (j : ℝ) - 1 / Real.sqrt ((j + 1 : ℕ) : ℝ)) * (T j : ℝ) := by
      refine Finset.sum_congr rfl fun j _ => by rw [hT_cast]
    linarith
  have hS_upper : S_ab ^ 2 ≤ (1 + Real.log (R : ℝ)) * (C₂ * (M : ℝ)) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 R)
      (fun j => (1 : ℝ) / Real.sqrt (j : ℝ)) (fun j => (B j : ℝ))
    have hSab_eq : S_ab = ∑ j ∈ Finset.Icc 1 R, (1 / Real.sqrt (j : ℝ)) * (B j : ℝ) := by
      change ∑ j ∈ Finset.Icc 1 R, (B j : ℝ) / Real.sqrt (j : ℝ) = _
      refine Finset.sum_congr rfl fun j _ => by ring
    have hsq1 : ∑ j ∈ Finset.Icc 1 R, ((1 : ℝ) / Real.sqrt (j : ℝ)) ^ 2 =
        ∑ j ∈ Finset.Icc 1 R, (1 : ℝ) / (j : ℝ) := by
      refine Finset.sum_congr rfl fun j _ => by
        rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg j)]
    rw [hSab_eq]
    calc (∑ j ∈ Finset.Icc 1 R, (1 / Real.sqrt (j : ℝ)) * (B j : ℝ)) ^ 2
        ≤ (∑ j ∈ Finset.Icc 1 R, (1 / Real.sqrt (j : ℝ)) ^ 2) *
            (∑ j ∈ Finset.Icc 1 R, (B j : ℝ) ^ 2) := hcs
      _ = (∑ j ∈ Finset.Icc 1 R, (1 : ℝ) / (j : ℝ)) *
            (∑ j ∈ Finset.Icc 1 R, (B j : ℝ) ^ 2) := by rw [hsq1]
      _ ≤ (1 + Real.log (R : ℝ)) * (C₂ * (M : ℝ)) := by
          have hlogR_nn : 0 ≤ 1 + Real.log (R : ℝ) := by
            have : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
            linarith [Real.log_nonneg this]
          exact mul_le_mul (harmonic_upper_bound R (by omega)) hsum_B2
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) hlogR_nn
  -- Final algebraic contradiction using log R ≥ log L > 100 and log R ≤ 2 log L
  have hlogR_ge : Real.log (L : ℝ) ≤ Real.log (R : ℝ) := by
    apply Real.log_le_log hL_pos
    exact_mod_cast (show L ≤ k * L from Nat.le_mul_of_pos_left L (by omega))
  have hlogR_le : Real.log (R : ℝ) ≤ 2 * Real.log (L : ℝ) := by
    have hRle : (R : ℝ) ≤ (L : ℝ) ^ 2 := by
      dsimp only [R]; push_cast
      have hkle : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show k ≤ L by omega)
      nlinarith
    calc Real.log (R : ℝ) ≤ Real.log ((L : ℝ) ^ 2) := Real.log_le_log (by positivity) hRle
      _ = 2 * Real.log (L : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogR_gt : (100 : ℝ) < Real.log (R : ℝ) := by linarith
  have hlower_nn : 0 ≤ (coeff / 2) * (Real.log (R : ℝ) - 1) := by
    have : 0 ≤ Real.log (R : ℝ) - 1 := by linarith
    positivity
  have hsq_le : ((coeff / 2) * (Real.log (R : ℝ) - 1)) ^ 2 ≤
      (1 + Real.log (R : ℝ)) * (C₂ * (M : ℝ)) :=
    (pow_le_pow_left₀ hlower_nn hS_lower 2).trans hS_upper
  -- Expand coeff^2: coeff^2 / 4 > 2 * C₂ * M / log L
  have hcoeff_sq : 2 * C₂ * ((M : ℝ) / Real.log (L : ℝ)) < (coeff / 2) ^ 2 := by
    dsimp only [coeff]
    have hden_pos : (0 : ℝ) < (2 : ℝ) ^ k * (k.factorial : ℝ) := by positivity
    have hCk_gt : (2 ^ k * (k.factorial : ℝ)) * Real.sqrt (48 * (k : ℝ) ^ 2 * C₂) < C ^ k := by
      have : (2 ^ k * (k.factorial : ℝ)) * Real.sqrt (48 * (k : ℝ) ^ 2 * C₂) < K_const := by
        dsimp only [K_const]; linarith
      linarith
    have hratio_gt : Real.sqrt (48 * (k : ℝ) ^ 2 * C₂) < C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ)) := by
      rw [lt_div_iff₀ hden_pos]; linarith
    have hsq_gt : 48 * (k : ℝ) ^ 2 * C₂ < (C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) ^ 2 := by
      have h := pow_lt_pow_left₀ hratio_gt (Real.sqrt_nonneg _) (by norm_num : 2 ≠ 0)
      rwa [Real.sq_sqrt (by positivity)] at h
    have hM_pos_R : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have hrew : ((C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) *
        Real.sqrt ((M : ℝ) / (6 * (k : ℝ) ^ 2 * Real.log (L : ℝ))) / 2) ^ 2 =
        (C ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ))) ^ 2 *
          ((M : ℝ) / (24 * (k : ℝ) ^ 2 * Real.log (L : ℝ))) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [hrew]
    have hfactor_pos : (0 : ℝ) < (M : ℝ) / (24 * (k : ℝ) ^ 2 * Real.log (L : ℝ)) := by positivity
    have hmul := mul_lt_mul_of_pos_right hsq_gt hfactor_pos
    have hlhs : 48 * (k : ℝ) ^ 2 * C₂ * ((M : ℝ) / (24 * (k : ℝ) ^ 2 * Real.log (L : ℝ))) =
        2 * C₂ * ((M : ℝ) / Real.log (L : ℝ)) := by
      have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp; ring
    linarith
  have hlog_ineq : (1 + Real.log (R : ℝ)) * Real.log (L : ℝ) < 2 * (Real.log (R : ℝ) - 1) ^ 2 := by
    -- Since log L ≤ log R and log R > 100: (1 + log R) * log R < 2 (log R - 1)^2
    have h1 : (1 + Real.log (R : ℝ)) * Real.log (L : ℝ) ≤ (1 + Real.log (R : ℝ)) * Real.log (R : ℝ) :=
      mul_le_mul_of_nonneg_left hlogR_ge (by linarith)
    nlinarith
  have hM_pos_R : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hcontra : (1 + Real.log (R : ℝ)) * (C₂ * (M : ℝ)) <
      ((coeff / 2) * (Real.log (R : ℝ) - 1)) ^ 2 := by
    rw [mul_pow]
    have h1 : 2 * C₂ * ((M : ℝ) / Real.log (L : ℝ)) * (Real.log (R : ℝ) - 1) ^ 2 <
        (coeff / 2) ^ 2 * (Real.log (R : ℝ) - 1) ^ 2 :=
      mul_lt_mul_of_pos_right hcoeff_sq (by nlinarith)
    have h2 : (1 + Real.log (R : ℝ)) * (C₂ * (M : ℝ)) <
        2 * C₂ * ((M : ℝ) / Real.log (L : ℝ)) * (Real.log (R : ℝ) - 1) ^ 2 := by
      have h3 := mul_lt_mul_of_pos_right hlog_ineq (by positivity : (0 : ℝ) < C₂ * (M : ℝ) / Real.log (L : ℝ))
      have hl : (1 + Real.log (R : ℝ)) * Real.log (L : ℝ) * (C₂ * (M : ℝ) / Real.log (L : ℝ)) =
          (1 + Real.log (R : ℝ)) * (C₂ * (M : ℝ)) := by field_simp
      have hr : 2 * (Real.log (R : ℝ) - 1) ^ 2 * (C₂ * (M : ℝ) / Real.log (L : ℝ)) =
          2 * C₂ * ((M : ℝ) / Real.log (L : ℝ)) * (Real.log (R : ℝ) - 1) ^ 2 := by ring
      linarith
    linarith
  linarith

/-- **General Even-`B_{2k}` `liminf = 0` Theorem:**
For every `k ≥ 1` and every infinite `B_{2k}`-set `A ⊆ ℕ`,
`liminf_{N → ∞} |A ∩ [1, N]| / N^{1/(2k)} = 0`. -/
theorem ppl124_even_B2k_liminf_zero (k : ℕ) (hk : 1 ≤ k) (A : Set ℕ)
    (hInf : A.Infinite)
    (hB2k : ∀ s t : Multiset ℕ, s.card = 2 * k → t.card = 2 * k →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t) :
    liminf (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ))))
      atTop = 0 := by
  obtain ⟨C, hC_pos, hfreq⟩ := ppl124_even_B2k_liminf_log k hk A hInf hB2k
  refine liminf_eq_zero_of_nonneg_of_frequently_le (fun N => by positivity) fun ε hε => ?_
  have hev : ∀ᶠ N : ℕ in atTop,
      C / (Real.log (N : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) ≤ ε ∧ 2 ≤ N := by
    have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ N : ℕ in atTop, (C / ε) ^ (2 * k) + 1 ≤ Real.log (N : ℝ) :=
      hlog_top.eventually (eventually_ge_atTop _)
    filter_upwards [h1, eventually_ge_atTop 2] with N hN hN2
    refine ⟨?_, hN2⟩
    have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
    have hrpow_pos : 0 < (Real.log (N : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) := Real.rpow_pos_of_pos hlog_pos _
    have hge : C / ε ≤ (Real.log (N : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) := by
      have hstep := Real.rpow_le_rpow (by positivity) (show (C / ε) ^ (2 * k) ≤ Real.log (N : ℝ) by linarith)
        (by positivity : (0 : ℝ) ≤ 1 / (2 * (k : ℝ)))
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at hstep
      have hexp : ((2 * k : ℕ) : ℝ) * (1 / (2 * (k : ℝ))) = 1 := by
        push_cast; have hkpos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega); field_simp
      rwa [hexp, Real.rpow_one] at hstep
    rw [div_le_iff₀ hrpow_pos]
    have := mul_le_mul_of_nonneg_left hge hε.le
    rwa [mul_div_cancel₀ _ hε.ne'] at this
  refine (hfreq.and_eventually hev).mono fun N ⟨hN, hεN, hN2⟩ => ?_
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hNp_pos : 0 < (N : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ))) := Real.rpow_pos_of_pos hN_pos _
  rw [div_le_iff₀ hNp_pos]
  calc ((A ∩ Set.Icc 1 N).ncard : ℝ)
      ≤ C * ((N : ℝ) / Real.log (N : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ))) := hN
    _ = (C / (Real.log (N : ℝ)) ^ ((1 : ℝ) / (2 * (k : ℝ)))) * (N : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ))) := by
        rw [Real.div_rpow hN_pos.le hlog_pos.le]; ring
    _ ≤ ε * (N : ℝ) ^ ((1 : ℝ) / (2 * (k : ℝ))) := mul_le_mul_of_nonneg_right hεN hNp_pos.le

private lemma multiset_card4_sorted (s : Multiset ℕ) (hs : s.card = 4) :
    ∃ a₁ a₂ a₃ a₄ : ℕ, a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄ ∧ s = {a₁, a₂, a₃, a₄} := by
  let l := s.sort (· ≤ ·)
  have hl_len : l.length = 4 := by simp [l, hs]
  have hl_sorted : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort s (· ≤ ·)
  have hl_coe : (l : Multiset ℕ) = s := Multiset.sort_eq s (· ≤ ·)
  rcases l with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hl_len
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hl_sorted
  refine ⟨a₁, a₂, a₃, a₄, hl_sorted.1.1, hl_sorted.2.1.1, hl_sorted.2.2.1, ?_⟩
  rw [← hl_coe]
  rfl

/-- **Infinite `B_4` Oscillation Theorem (Nash 1989 / Chen 1996 Specialization):**
For every infinite `B_4`-set `A ⊆ ℕ` (all 4-term sums distinct up to permutation),
`liminf_{N → ∞} |A ∩ [1, N]| / N^{1/4} = 0`. -/
theorem ppl124_B4_liminf_zero (A : Set ℕ)
    (hInf : A.Infinite)
    (hB4 : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ a₄ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A, ∀ b₄ ∈ A,
      a₁ ≤ a₂ → a₂ ≤ a₃ → a₃ ≤ a₄ → b₁ ≤ b₂ → b₂ ≤ b₃ → b₃ ≤ b₄ →
      a₁ + a₂ + a₃ + a₄ = b₁ + b₂ + b₃ + b₄ →
      a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ ∧ a₄ = b₄) :
    liminf (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 4)) atTop = 0 := by
  have hB2k : ∀ s t : Multiset ℕ, s.card = 2 * 2 → t.card = 2 * 2 →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t := by
    intro s t hs ht hsA htA hsum
    obtain ⟨a₁, a₂, a₃, a₄, ha12, ha23, ha34, rfl⟩ := multiset_card4_sorted s hs
    obtain ⟨b₁, b₂, b₃, b₄, hb12, hb23, hb34, rfl⟩ := multiset_card4_sorted t ht
    have hsum' : a₁ + a₂ + a₃ + a₄ = b₁ + b₂ + b₃ + b₄ := by
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum; omega
    have ⟨e1, e2, e3, e4⟩ := hB4
      a₁ (hsA _ (by simp)) a₂ (hsA _ (by simp)) a₃ (hsA _ (by simp)) a₄ (hsA _ (by simp))
      b₁ (htA _ (by simp)) b₂ (htA _ (by simp)) b₃ (htA _ (by simp)) b₄ (htA _ (by simp))
      ha12 ha23 ha34 hb12 hb23 hb34 hsum'
    subst e1; subst e2; subst e3; subst e4; rfl
  have h := ppl124_even_B2k_liminf_zero 2 (by omega) A hInf hB2k
  convert h using 3
  norm_num

/-- **Exact Even/Odd Parity Structural Barrier (Why Even-Difference Cauchy–Schwarz Fails for `B_3`):**
A signed `h`-variable linear form `∑_{i < h} ε_i x_i` (`ε_i ∈ {-1, 1}`) can be translation-invariant
(`∀ x t, ∑ ε_i (x_i + t) = ∑ ε_i x_i`) **if and only if** `h` is even. -/
theorem ppl124_odd_parity_translation_barrier (h : ℕ) :
    (∃ ε : Fin h → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ (x : Fin h → ℤ) (t : ℤ),
        ∑ i : Fin h, ε i * (x i + t) = ∑ i : Fin h, ε i * x i) ↔ Even h := by
  constructor
  · rintro ⟨ε, hε, hinv⟩
    have hsum0 : ∑ i : Fin h, ε i = 0 := by
      have h0 := hinv (fun _ => 0) 1
      simpa using h0
    -- Every ε i is ≡ 1 (mod 2), so ∑ ε i ≡ h (mod 2)
    have hmod : (∑ i : Fin h, ε i) % 2 = (h : ℤ) % 2 := by
      have h1 : ∑ i : Fin h, (ε i - 1) = (∑ i : Fin h, ε i) - (h : ℤ) := by
        simp [Finset.sum_sub_distrib]
      have hdvd : (2 : ℤ) ∣ ∑ i : Fin h, (ε i - 1) := by
        refine Finset.dvd_sum fun i _ => ?_
        rcases hε i with h1' | h1' <;> rw [h1'] <;> omega
      rw [h1] at hdvd
      omega
    rw [hsum0] at hmod
    have hnat : h % 2 = 0 := by omega
    exact Nat.even_iff.mpr hnat
  · rintro ⟨k, rfl⟩
    refine ⟨fun i => if i.val < k then 1 else -1, fun i => by dsimp only; split_ifs <;> simp, fun x t => ?_⟩
    have hsum0 : ∑ i : Fin (k + k), (if i.val < k then (1 : ℤ) else -1) = 0 := by
      have hsplit : (Finset.univ : Finset (Fin (k + k))) =
          (Finset.univ.filter (fun i : Fin (k + k) => i.val < k)) ∪
          (Finset.univ.filter (fun i : Fin (k + k) => ¬ i.val < k)) := by
        ext i; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
        omega
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin (k + k) => i.val < k))
          (Finset.univ.filter (fun i : Fin (k + k) => ¬ i.val < k)) := by
        rw [Finset.disjoint_left]; intro i h1 h2; simp at h1 h2; omega
      rw [hsplit, Finset.sum_union hdisj]
      have hcard1 : (Finset.univ.filter (fun i : Fin (k + k) => i.val < k)).card = k := by
        conv_rhs => rw [← Fintype.card_fin k, ← Finset.card_univ]
        refine Finset.card_bij (fun (i : Fin (k + k)) hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k)) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) h)
        · intro j _; exact ⟨⟨j.val, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact j.isLt, rfl⟩
      have hcard2 : (Finset.univ.filter (fun i : Fin (k + k) => ¬ i.val < k)).card = k := by
        have htot := Finset.card_union_of_disjoint hdisj
        rw [← hsplit, Finset.card_univ, Fintype.card_fin, hcard1] at htot
        omega
      have hs1 : ∑ i ∈ Finset.univ.filter (fun i : Fin (k + k) => i.val < k),
          (if i.val < k then (1 : ℤ) else -1) = (k : ℤ) := by
        trans ∑ _i ∈ Finset.univ.filter (fun i : Fin (k + k) => i.val < k), (1 : ℤ)
        · refine Finset.sum_congr rfl fun i hi => by simp only [Finset.mem_filter] at hi; simp [hi.2]
        · simp [hcard1]
      have hs2 : ∑ i ∈ Finset.univ.filter (fun i : Fin (k + k) => ¬ i.val < k),
          (if i.val < k then (1 : ℤ) else -1) = -(k : ℤ) := by
        trans ∑ _i ∈ Finset.univ.filter (fun i : Fin (k + k) => ¬ i.val < k), (-1 : ℤ)
        · refine Finset.sum_congr rfl fun i hi => by simp only [Finset.mem_filter] at hi; simp [hi.2]
        · rw [Finset.sum_const, hcard2, nsmul_eq_mul]; ring
      linarith
    have hexpand : ∑ i : Fin (k + k), (if i.val < k then (1 : ℤ) else -1) * (x i + t) =
        (∑ i : Fin (k + k), (if i.val < k then (1 : ℤ) else -1) * x i) +
        (∑ i : Fin (k + k), (if i.val < k then (1 : ℤ) else -1)) * t := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand, hsum0, zero_mul, add_zero]

/-- **Concrete `B_3` Translation-Shift Obstruction:**
Every signed 3-variable form `∑_{i < 3} ε_i x_i` (`ε_i ∈ {-1, 1}`) shifts by a nonzero multiple
`c * t` (`c ∈ {-3, -1, 1, 3}`) under uniform translation `x_i ↦ x_i + t`. -/
theorem ppl124_B3_translation_shift_obstruction (ε : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ (x : Fin 3 → ℤ) (t : ℤ),
      ∑ i : Fin 3, ε i * (x i + t) = (∑ i : Fin 3, ε i * x i) + c * t := by
  refine ⟨∑ i : Fin 3, ε i, ?_, fun x t => ?_⟩
  · intro h0
    have : Even 3 := (ppl124_odd_parity_translation_barrier 3).mp ⟨ε, hε, fun x t => by
      have hexp : ∑ i : Fin 3, ε i * (x i + t) =
          (∑ i : Fin 3, ε i * x i) + (∑ i : Fin 3, ε i) * t := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hexp, h0, zero_mul, add_zero]⟩
    rcases this with ⟨m, hm⟩; omega
  · rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring

/-- **Disjointness of `B + B - B` Across Translated Blocks (Concrete Witness of the Odd-`B_3` Barrier):**
Unlike Sidon differences `a - b` (which collapse every translated block `B + 4jM` into `[-M, M]`),
the `B_3` signed form `a + b - c` maps disjoint translated blocks `B + 4jM` (`B ⊆ [0, M]`) into
**pairwise disjoint** intervals `[4jM - M, 4jM + 2M]`, preventing cross-block Cauchy–Schwarz collision. -/
theorem ppl124_B3_translated_blocks_disjoint_images (M : ℕ) (hM : 1 ≤ M)
    (B : Set ℤ) (hB : ∀ x ∈ B, 0 ≤ x ∧ x ≤ (M : ℤ)) :
    ∀ j₁ j₂ : ℤ, j₁ ≠ j₂ →
      Disjoint
        {z : ℤ | ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B,
          z = (a + 4 * j₁ * (M : ℤ)) + (b + 4 * j₁ * (M : ℤ)) - (c + 4 * j₁ * (M : ℤ))}
        {z : ℤ | ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B,
          z = (a + 4 * j₂ * (M : ℤ)) + (b + 4 * j₂ * (M : ℤ)) - (c + 4 * j₂ * (M : ℤ))} := by
  intro j₁ j₂ hne
  rw [Set.disjoint_left]
  rintro z ⟨a₁, ha₁, b₁, hb₁, c₁, hc₁, hz₁⟩ ⟨a₂, ha₂, b₂, hb₂, c₂, hc₂, hz₂⟩
  have h1a := hB a₁ ha₁; have h1b := hB b₁ hb₁; have h1c := hB c₁ hc₁
  have h2a := hB a₂ ha₂; have h2b := hB b₂ hb₂; have h2c := hB c₂ hc₂
  have hMpos : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast hM
  rcases lt_or_gt_of_ne hne with hlt | hgt <;> nlinarith

/-- **Sharp Unconditional Elementary Upper Bound for `B_3`-Sets (Beating Trivial `(18 N)^{1/3}` to `(6 N)^{1/3}`):**
For every `B_3`-set `A ⊆ ℕ` and every `N ≥ 1`, counting distinct positive values `b + c - a` and
`a + c - b` in `[1, 2N - 2]` over all unordered triples `a < b < c` in `A ∩ [1, N]` yields:
1. `Nat.choose |A ∩ [1, N]| 3 ≤ N - 1`,
2. `|A ∩ [1, N]| ≤ (6 N)^{1/3} + 2`,
3. `liminf_{N → ∞} |A ∩ [1, N]| / N^{1/3} ≤ 6^{1/3}`. -/
theorem ppl124_B3_unconditional_upper_bound (A : Set ℕ)
    (hB3 : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ a₃ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A, ∀ b₃ ∈ A,
      a₁ ≤ a₂ → a₂ ≤ a₃ → b₁ ≤ b₂ → b₂ ≤ b₃ →
      a₁ + a₂ + a₃ = b₁ + b₂ + b₃ → a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃) :
    (∀ N : ℕ, 1 ≤ N → Nat.choose (A ∩ Set.Icc 1 N).ncard 3 ≤ N - 1) ∧
    (∀ N : ℕ, 1 ≤ N → ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ (6 * (N : ℝ)) ^ ((1 : ℝ) / 3) + 2) ∧
    liminf (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3)) atTop ≤
      (6 : ℝ) ^ ((1 : ℝ) / 3) := by
  classical
  -- First prove the core combinatorial injection: 2 * choose a 3 ≤ 2 * (N - 1)
  have hB3_mset : ∀ {x₁ y₁ z₁ x₂ y₂ z₂ : ℕ},
      x₁ ∈ A → y₁ ∈ A → z₁ ∈ A → x₂ ∈ A → y₂ ∈ A → z₂ ∈ A →
      x₁ < y₁ → z₁ ≠ x₁ → z₁ ≠ y₁ → x₂ < y₂ → z₂ ≠ x₂ → z₂ ≠ y₂ →
      x₁ + y₁ + z₂ = x₂ + y₂ + z₁ → x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂ := by
    intro x₁ y₁ z₁ x₂ y₂ z₂ hx1 hy1 hz1 hx2 hy2 hz2 hxy1 hzx1 hzy1 hxy2 hzx2 hzy2 hsum
    -- Sort {x₁, y₁, z₂} and {x₂, y₂, z₁} as 3-tuples
    have hsort : ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
        ∃ u v w : ℕ, u ∈ A ∧ v ∈ A ∧ w ∈ A ∧ u ≤ v ∧ v ≤ w ∧
          ({u, v, w} : Multiset ℕ) = {a, b, c} ∧ u + v + w = a + b + c := by
      intro a b c ha hb hc
      let l := ({a, b, c} : Multiset ℕ).sort (· ≤ ·)
      have hl_len : l.length = 3 := by simp [l]
      have hl_sorted : l.Pairwise (· ≤ ·) := Multiset.pairwise_sort _ (· ≤ ·)
      have hl_coe : (l : Multiset ℕ) = {a, b, c} := Multiset.sort_eq _ (· ≤ ·)
      rcases l with _ | ⟨u, _ | ⟨v, _ | ⟨w, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hl_len
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hl_sorted
      have hcoe' : ({u, v, w} : Multiset ℕ) = {a, b, c} := hl_coe
      have hmem : ∀ t, t ∈ ({u, v, w} : Multiset ℕ) → t ∈ A := by
        intro t ht
        have : t ∈ ({a, b, c} : Multiset ℕ) := by rwa [← hcoe']
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at this
        rcases this with rfl | rfl | rfl <;> assumption
      have hsum_eq : u + v + w = a + b + c := by
        have := congrArg Multiset.sum hcoe'
        simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at this
        omega
      exact ⟨u, v, w, hmem u (by simp), hmem v (by simp), hmem w (by simp),
        hl_sorted.1.1, hl_sorted.2.1, hcoe', hsum_eq⟩
    obtain ⟨u₁, v₁, w₁, hu1, hv1, hw1, huv1, hvw1, hm1, hs1⟩ := hsort x₁ y₁ z₂ hx1 hy1 hz2
    obtain ⟨u₂, v₂, w₂, hu2, hv2, hw2, huv2, hvw2, hm2, hs2⟩ := hsort x₂ y₂ z₁ hx2 hy2 hz1
    have ⟨eu, ev, ew⟩ := hB3 u₁ hu1 v₁ hv1 w₁ hw1 u₂ hu2 v₂ hv2 w₂ hw2 huv1 hvw1 huv2 hvw2 (by omega)
    have hmeq : ({x₁, y₁, z₂} : Multiset ℕ) = {x₂, y₂, z₁} := by
      rw [← hm1, ← hm2, eu, ev, ew]
    have hz1_mem : z₁ ∈ ({x₁, y₁, z₂} : Multiset ℕ) := by rw [hmeq]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz1_mem
    have hz_eq : z₁ = z₂ := by rcases hz1_mem with h | h | h <;> [omega; omega; exact h]
    subst hz_eq
    have hpair : ({x₁, y₁} : Multiset ℕ) = {x₂, y₂} := by
      have h1 : z₁ ::ₘ ({x₁, y₁} : Multiset ℕ) = z₁ ::ₘ ({x₂, y₂} : Multiset ℕ) := by
        calc z₁ ::ₘ ({x₁, y₁} : Multiset ℕ)
            = ({x₁, y₁, z₁} : Multiset ℕ) := by
                ext u; simp [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]; ring
          _ = ({x₂, y₂, z₁} : Multiset ℕ) := hmeq
          _ = z₁ ::ₘ ({x₂, y₂} : Multiset ℕ) := by
                ext u; simp [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]; ring
      exact (Multiset.cons_inj_right z₁).mp h1
    have hx1_mem : x₁ ∈ ({x₂, y₂} : Multiset ℕ) := by rw [← hpair]; simp
    have hy1_mem : y₁ ∈ ({x₂, y₂} : Multiset ℕ) := by rw [← hpair]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx1_mem hy1_mem
    omega
  have hchoose_bd : ∀ N : ℕ, 1 ≤ N → Nat.choose (A ∩ Set.Icc 1 N).ncard 3 ≤ N - 1 := by
    intro N hN
    rw [ncard_inter_Icc_eq_filter_card]
    set S := (Finset.Icc 1 N).filter (fun x => x ∈ A)
    -- Every unordered 3-subset {a < b < c} gives TWO triples (b, c, a) and (a, c, b)
    -- in T := {(x, y, z) ∈ S^3 : x < y ∧ z < y ∧ z ≠ x} with 1 ≤ x + y - z ≤ 2N - 2
    let T1 : Finset (ℕ × ℕ × ℕ) :=
      (S ×ˢ (S ×ˢ S)).filter (fun t => t.2.2 < t.1 ∧ t.1 < t.2.1) -- (b, c, a) with a < b < c
    let T2 : Finset (ℕ × ℕ × ℕ) :=
      (S ×ˢ (S ×ˢ S)).filter (fun t => t.1 < t.2.2 ∧ t.2.2 < t.2.1) -- (a, c, b) with a < b < c
    have hT_disj : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]; intro t h1 h2
      simp only [T1, T2, Finset.mem_filter] at h1 h2; omega
    have hT1_card : T1.card = Nat.choose S.card 3 := by
      rw [← Finset.card_powersetCard 3 S]
      refine Finset.card_bij (fun t _ => ({t.2.2, t.1, t.2.1} : Finset ℕ)) ?_ ?_ ?_
      · intro t ht
        simp only [T1, Finset.mem_filter, Finset.mem_product] at ht
        simp only [Finset.mem_powersetCard]
        refine ⟨fun u hu => ?_, ?_⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl <;> tauto
        · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] <;>
            simp <;> omega
      · intro t₁ ht₁ t₂ ht₂ heq
        simp only [T1, Finset.mem_filter, Finset.mem_product] at ht₁ ht₂
        have hmem1 : ∀ u, u ∈ ({t₁.2.2, t₁.1, t₁.2.1} : Finset ℕ) ↔
            u ∈ ({t₂.2.2, t₂.1, t₂.2.1} : Finset ℕ) := fun u => by rw [heq]
        have h1a := (hmem1 t₁.2.2).mp (by simp)
        have h1b := (hmem1 t₁.1).mp (by simp)
        have h1c := (hmem1 t₁.2.1).mp (by simp)
        have h2a := (hmem1 t₂.2.2).mpr (by simp)
        have h2b := (hmem1 t₂.1).mpr (by simp)
        have h2c := (hmem1 t₂.2.1).mpr (by simp)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1a h1b h1c h2a h2b h2c
        ext <;> omega
      · intro X hX
        simp only [Finset.mem_powersetCard] at hX
        have hl_len : (X.sort (· ≤ ·)).length = 3 := by simp [hX.2]
        have hl_sorted : (X.sort (· ≤ ·)).Pairwise (· ≤ ·) := Finset.pairwise_sort X (· ≤ ·)
        have hl_nodup : (X.sort (· ≤ ·)).Nodup := Finset.sort_nodup X (· ≤ ·)
        rcases hl : X.sort (· ≤ ·) with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩ <;> simp [hl] at hl_len
        rw [hl] at hl_sorted hl_nodup
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hl_sorted
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hl_nodup
        have hXeq : ({a, b, c} : Finset ℕ) = X := by
          ext u
          rw [← Finset.mem_sort (r := (· ≤ ·)) (s := X), hl]
          simp
        refine ⟨(b, c, a), ?_, hXeq⟩
        simp only [T1, Finset.mem_filter, Finset.mem_product]
        have ha : a ∈ S := hX.1 (by rw [← hXeq]; simp)
        have hb : b ∈ S := hX.1 (by rw [← hXeq]; simp)
        have hc : c ∈ S := hX.1 (by rw [← hXeq]; simp)
        exact ⟨⟨hb, hc, ha⟩, lt_of_le_of_ne hl_sorted.1.1 hl_nodup.1.1,
          lt_of_le_of_ne hl_sorted.2.1 hl_nodup.2.1⟩
    have hT2_card : T2.card = T1.card := by
      refine Finset.card_bij (fun t _ => (t.2.2, t.2.1, t.1)) ?_ ?_ ?_
      · intro t ht; simp only [T1, T2, Finset.mem_filter, Finset.mem_product] at ht ⊢
        exact ⟨⟨ht.1.2.2, ht.1.2.1, ht.1.1⟩, ht.2.1, ht.2.2⟩
      · intro t₁ _ t₂ _ h; ext <;> simp_all
      · intro t ht; simp only [T1, Finset.mem_filter, Finset.mem_product] at ht
        exact ⟨(t.2.2, t.2.1, t.1), by simp only [T2, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨ht.1.2.2, ht.1.2.1, ht.1.1⟩, ht.2.1, ht.2.2⟩, rfl⟩
    have hinj : (T1 ∪ T2).card ≤ 2 * (N - 1) := by
      have hcard_le : (T1 ∪ T2).card ≤ (Finset.Icc 1 (2 * (N - 1))).card := by
        refine Finset.card_le_card_of_injOn (fun t => t.1 + t.2.1 - t.2.2) ?_ ?_
        · intro t ht
          simp only [T1, T2, Finset.mem_coe, Finset.mem_union, Finset.mem_filter,
            Finset.mem_product, S, Finset.mem_Icc] at ht ⊢
          rcases ht with ⟨⟨⟨⟨h1, h2⟩, _⟩, ⟨⟨h3, h4⟩, _⟩, ⟨⟨h5, h6⟩, _⟩⟩, h7, h8⟩ |
            ⟨⟨⟨⟨h1, h2⟩, _⟩, ⟨⟨h3, h4⟩, _⟩, ⟨⟨h5, h6⟩, _⟩⟩, h7, h8⟩ <;> omega
        · intro t₁ ht₁ t₂ ht₂ heq
          dsimp only at heq
          simp only [T1, T2, Finset.mem_coe, Finset.mem_union, Finset.mem_filter,
            Finset.mem_product, S] at ht₁ ht₂
          have h1 : t₁.1 ∈ A ∧ t₁.2.1 ∈ A ∧ t₁.2.2 ∈ A ∧ t₁.1 < t₁.2.1 ∧
              t₁.2.2 ≠ t₁.1 ∧ t₁.2.2 ≠ t₁.2.1 ∧ t₁.2.2 < t₁.1 + t₁.2.1 := by
            rcases ht₁ with ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩, h4, h5⟩ |
              ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩, h4, h5⟩ <;> exact ⟨h1, h2, h3, by omega, by omega, by omega, by omega⟩
          have h2 : t₂.1 ∈ A ∧ t₂.2.1 ∈ A ∧ t₂.2.2 ∈ A ∧ t₂.1 < t₂.2.1 ∧
              t₂.2.2 ≠ t₂.1 ∧ t₂.2.2 ≠ t₂.2.1 ∧ t₂.2.2 < t₂.1 + t₂.2.1 := by
            rcases ht₂ with ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩, h4, h5⟩ |
              ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩⟩, h4, h5⟩ <;> exact ⟨h1, h2, h3, by omega, by omega, by omega, by omega⟩
          have hsum : t₁.1 + t₁.2.1 + t₂.2.2 = t₂.1 + t₂.2.1 + t₁.2.2 := by omega
          have ⟨e1, e2, e3⟩ := hB3_mset h1.1 h1.2.1 h1.2.2.1 h2.1 h2.2.1 h2.2.2.1
            h1.2.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2.1
            h2.2.2.2.1 h2.2.2.2.2.1 h2.2.2.2.2.2.1 hsum
          exact Prod.ext e1 (Prod.ext e2 e3)
      simpa using hcard_le
    rw [Finset.card_union_of_disjoint hT_disj, hT2_card, hT1_card] at hinj
    omega
  have hreal_bd : ∀ N : ℕ, 1 ≤ N → ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ (6 * (N : ℝ)) ^ ((1 : ℝ) / 3) + 2 := by
    intro N hN
    set a := (A ∩ Set.Icc 1 N).ncard
    by_cases ha2 : a ≤ 2
    · have : (a : ℝ) ≤ 2 := by exact_mod_cast ha2
      linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 6 * (N : ℝ)) ((1 : ℝ) / 3)]
    push Not at ha2
    have hch := hchoose_bd N hN
    have hcube : (a - 2) ^ 3 ≤ 6 * N := by
      have hdesc : Nat.descFactorial a 3 = 6 * Nat.choose a 3 := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num
      have hle : (a - 2) ^ 3 ≤ Nat.descFactorial a 3 := by
        rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
          Nat.descFactorial_zero]
        have h1 : a - 2 ≤ a - 1 := by omega
        have h2 : a - 2 ≤ a := by omega
        have h3 : (a - 2) ^ 3 = (a - 2) * ((a - 2) * ((a - 2) * 1)) := by ring
        rw [h3]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 (Nat.mul_le_mul_right 1 h2))
      change Nat.choose a 3 ≤ N - 1 at hch
      omega
    have hcube_R : ((a - 2 : ℕ) : ℝ) ^ 3 ≤ 6 * (N : ℝ) := by exact_mod_cast hcube
    have hroot : ((a - 2 : ℕ) : ℝ) ≤ (6 * (N : ℝ)) ^ ((1 : ℝ) / 3) := by
      have h := Real.rpow_le_rpow (by positivity) hcube_R (by positivity : (0 : ℝ) ≤ 1 / 3)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at h
      norm_num at h
      exact h
    have hcast : ((a - 2 : ℕ) : ℝ) = (a : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    linarith
  refine ⟨hchoose_bd, hreal_bd, ?_⟩
  -- liminf ≤ 6^(1/3) follows from eventually ≤ 6^(1/3) + 2 / N^(1/3) → 6^(1/3)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3)) :=
    ⟨0, eventually_map.mpr (Eventually.of_forall fun N => by positivity)⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev : ∀ᶠ N : ℕ in atTop,
      ((A ∩ Set.Icc 1 N).ncard : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (6 : ℝ) ^ ((1 : ℝ) / 3) + ε := by
    have hpow_top : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ N : ℕ in atTop, 2 / ε ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
      hpow_top.eventually (eventually_ge_atTop _)
    filter_upwards [h1, eventually_ge_atTop 1] with N hN hN1
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN1
    have hNp_pos : 0 < (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hN_pos _
    rw [div_le_iff₀ hNp_pos]
    have hmul := hreal_bd N hN1
    rw [Real.mul_rpow (by norm_num) hN_pos.le] at hmul
    have h2 : 2 ≤ ε * (N : ℝ) ^ ((1 : ℝ) / 3) := by
      have := mul_le_mul_of_nonneg_left hN hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  exact Filter.liminf_le_of_frequently_le hev.frequently hbdd

/-!
## Part III-A — Greedy Infinite `B_h` (`N^{1/(2h-1)}`) & Mian–Chowla Sidon (`N^{1/3}`) Lower Bounds (PPL 124 / #39 & PPL 168 / #41)
-/

private def sumSet (S : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | j + 1 => ((sumSet S j) ×ˢ S).image (fun p => p.1 + p.2)

private lemma sumSet_card_le (S : Finset ℕ) : ∀ j : ℕ, (sumSet S j).card ≤ S.card ^ j
  | 0 => by simp [sumSet]
  | j + 1 => by
    simp only [sumSet, pow_succ]
    calc (((sumSet S j) ×ˢ S).image (fun p => p.1 + p.2)).card
        ≤ ((sumSet S j) ×ˢ S).card := Finset.card_image_le
      _ = (sumSet S j).card * S.card := Finset.card_product _ _
      _ ≤ S.card ^ j * S.card := Nat.mul_le_mul_right _ (sumSet_card_le S j)

private lemma multiset_sum_mem_sumSet (S : Finset ℕ) (U : Multiset ℕ)
    (hU : ∀ u ∈ U, u ∈ S) : U.sum ∈ sumSet S U.card := by
  induction U using Multiset.induction_on with
  | empty => simp [sumSet]
  | cons a t ih =>
    have ha : a ∈ S := hU a (Multiset.mem_cons_self a t)
    have ht : ∀ u ∈ t, u ∈ S := fun u hu => hU u (Multiset.mem_cons_of_mem hu)
    have hmem := ih ht
    simp only [Multiset.card_cons, Multiset.sum_cons, sumSet, Finset.mem_image, Finset.mem_product]
    exact ⟨(t.sum, a), ⟨hmem, ha⟩, by ring⟩

private def forbBh (h : ℕ) (S : Finset ℕ) : Finset ℕ :=
  S ∪ ((Finset.Icc 1 h) ×ˢ
        (((Finset.range h).biUnion (sumSet S)) ×ˢ
         ((Finset.range (h + 1)).biUnion (sumSet S)))).image
      (fun t => (t.2.2 - t.2.1) / t.1)

private lemma forbBh_card_le (h : ℕ) (hh : 2 ≤ h) (S : Finset ℕ) (hS : 1 ≤ S.card) :
    (forbBh h S).card ≤ (h ^ 2 * (h + 1) + 1) * S.card ^ (2 * h - 1) := by
  set n := S.card
  have hbi1 : ((Finset.range h).biUnion (sumSet S)).card ≤ h * n ^ (h - 1) := by
    calc ((Finset.range h).biUnion (sumSet S)).card
        ≤ ∑ j ∈ Finset.range h, (sumSet S j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range h, n ^ j := Finset.sum_le_sum fun j _ => sumSet_card_le S j
      _ ≤ ∑ _j ∈ Finset.range h, n ^ (h - 1) := Finset.sum_le_sum fun j hj => by
          simp only [Finset.mem_range] at hj
          exact Nat.pow_le_pow_right hS (by omega)
      _ = h * n ^ (h - 1) := by simp
  have hbi2 : ((Finset.range (h + 1)).biUnion (sumSet S)).card ≤ (h + 1) * n ^ h := by
    calc ((Finset.range (h + 1)).biUnion (sumSet S)).card
        ≤ ∑ j ∈ Finset.range (h + 1), (sumSet S j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Finset.range (h + 1), n ^ j := Finset.sum_le_sum fun j _ => sumSet_card_le S j
      _ ≤ ∑ _j ∈ Finset.range (h + 1), n ^ h := Finset.sum_le_sum fun j hj => by
          simp only [Finset.mem_range] at hj
          exact Nat.pow_le_pow_right hS (by omega)
      _ = (h + 1) * n ^ h := by simp
  have hprod : ((Finset.Icc 1 h) ×ˢ
        (((Finset.range h).biUnion (sumSet S)) ×ˢ
         ((Finset.range (h + 1)).biUnion (sumSet S)))).card ≤
      h ^ 2 * (h + 1) * n ^ (2 * h - 1) := by
    rw [Finset.card_product, Finset.card_product]
    have hIcc : (Finset.Icc 1 h).card = h := by simp
    rw [hIcc]
    calc h * (((Finset.range h).biUnion (sumSet S)).card *
              ((Finset.range (h + 1)).biUnion (sumSet S)).card)
        ≤ h * ((h * n ^ (h - 1)) * ((h + 1) * n ^ h)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hbi1 hbi2)
      _ = h ^ 2 * (h + 1) * (n ^ (h - 1) * n ^ h) := by ring
      _ = h ^ 2 * (h + 1) * n ^ (2 * h - 1) := by
          rw [← pow_add]; congr 2; omega
  have hn_le : n ≤ n ^ (2 * h - 1) := by
    conv_lhs => rw [← pow_one n]
    exact Nat.pow_le_pow_right hS (by omega)
  calc (forbBh h S).card
      ≤ S.card + (((Finset.Icc 1 h) ×ˢ
          (((Finset.range h).biUnion (sumSet S)) ×ˢ
           ((Finset.range (h + 1)).biUnion (sumSet S)))).image _).card := Finset.card_union_le _ _
    _ ≤ n + ((Finset.Icc 1 h) ×ˢ
          (((Finset.range h).biUnion (sumSet S)) ×ˢ
           ((Finset.range (h + 1)).biUnion (sumSet S)))).card := Nat.add_le_add_left Finset.card_image_le _
    _ ≤ n ^ (2 * h - 1) + h ^ 2 * (h + 1) * n ^ (2 * h - 1) := Nat.add_le_add hn_le hprod
    _ = (h ^ 2 * (h + 1) + 1) * n ^ (2 * h - 1) := by ring

private lemma insert_preserves_Bh {h : ℕ} (_hh : 2 ≤ h) {S : Finset ℕ}
    (hBh : ∀ s t : Multiset ℕ, s.card = h → t.card = h →
      (∀ u ∈ s, u ∈ S) → (∀ u ∈ t, u ∈ S) → s.sum = t.sum → s = t)
    {x : ℕ} (hx : x ∉ forbBh h S) :
    x ∉ S ∧ ∀ s t : Multiset ℕ, s.card = h → t.card = h →
      (∀ u ∈ s, u ∈ insert x S) → (∀ u ∈ t, u ∈ insert x S) → s.sum = t.sum → s = t := by
  have hxS : x ∉ S := fun hmem => hx (Finset.mem_union_left _ hmem)
  refine ⟨hxS, fun s t hs ht hsM htM hsum => ?_⟩
  by_contra hne
  -- Split s and t into copies of x and elements ≠ x (which all lie in S)
  have hsplit : ∀ (m : Multiset ℕ), (∀ u ∈ m, u ∈ insert x S) →
      m = Multiset.replicate (m.count x) x + m.filter (· ≠ x) ∧
      (∀ u ∈ m.filter (· ≠ x), u ∈ S) := by
    intro m hm
    constructor
    · ext u
      rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_filter]
      by_cases hu : u = x
      · subst hu; simp
      · simp [hu, Ne.symm hu]
    · intro u hu
      rw [Multiset.mem_filter] at hu
      have := hm u hu.1
      rw [Finset.mem_insert] at this
      exact this.resolve_left hu.2
  obtain ⟨hs_eq, hsU⟩ := hsplit s hsM
  obtain ⟨ht_eq, htV⟩ := hsplit t htM
  set c₁ := s.count x
  set c₂ := t.count x
  set U := s.filter (· ≠ x)
  set V := t.filter (· ≠ x)
  have hcU : c₁ + U.card = h := by
    have := congrArg Multiset.card hs_eq
    simp only [Multiset.card_add, Multiset.card_replicate] at this
    omega
  have hcV : c₂ + V.card = h := by
    have := congrArg Multiset.card ht_eq
    simp only [Multiset.card_add, Multiset.card_replicate] at this
    omega
  have hsum_eq : c₁ * x + U.sum = c₂ * x + V.sum := by
    have h1 := congrArg Multiset.sum hs_eq
    have h2 := congrArg Multiset.sum ht_eq
    simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at h1 h2
    omega
  -- Case 1: c₁ = c₂
  by_cases hceq : c₁ = c₂
  · have hUV_sum : U.sum = V.sum := by rw [hceq] at hsum_eq; omega
    have hUV_ne : U ≠ V := fun heq => hne (by rw [hs_eq, ht_eq, hceq, heq])
    by_cases hSempty : S = ∅
    · have hU0 : U = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]; intro u hu
        have := hsU u hu; simp [hSempty] at this
      have hV0 : V = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]; intro u hu
        have := htV u hu; simp [hSempty] at this
      exact hUV_ne (hU0.trans hV0.symm)
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
      let s' := Multiset.replicate c₁ y + U
      let t' := Multiset.replicate c₁ y + V
      have hs'c : s'.card = h := by simp [s', hcU]
      have ht'c : t'.card = h := by simp [t', hceq, hcV]
      have hs'm : ∀ u ∈ s', u ∈ S := by
        intro u hu; rcases Multiset.mem_add.mp hu with h1 | h1
        · rw [Multiset.mem_replicate] at h1; exact h1.2 ▸ hy
        · exact hsU u h1
      have ht'm : ∀ u ∈ t', u ∈ S := by
        intro u hu; rcases Multiset.mem_add.mp hu with h1 | h1
        · rw [Multiset.mem_replicate] at h1; exact h1.2 ▸ hy
        · exact htV u h1
      have hs'sum : s'.sum = t'.sum := by
        simp [s', t', hUV_sum]
      have heq' := hBh s' t' hs'c ht'c hs'm ht'm hs'sum
      exact hUV_ne (add_left_cancel heq')
  -- Case 2: c₁ ≠ c₂ → x ∈ forbBh h S
  · have hmem_forb : ∀ {a b : ℕ} {A₁ A₂ : Multiset ℕ},
        b < a → a + A₁.card = h → b + A₂.card = h →
        (∀ u ∈ A₁, u ∈ S) → (∀ u ∈ A₂, u ∈ S) →
        a * x + A₁.sum = b * x + A₂.sum → x ∈ forbBh h S := by
      intro a b A₁ A₂ hlt ha hb hA₁ hA₂ heq
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨(a - b, A₁.sum, A₂.sum), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion, Finset.mem_range]
        refine ⟨⟨by omega, by omega⟩, ⟨A₁.card, by omega, multiset_sum_mem_sumSet S A₁ hA₁⟩,
          ⟨A₂.card, by omega, multiset_sum_mem_sumSet S A₂ hA₂⟩⟩
      · have hmul : (a - b) * x = A₂.sum - A₁.sum := by
          have h1 : (a - b) * x + A₁.sum = A₂.sum := by
            have : a * x = (a - b) * x + b * x := by
              rw [← add_mul, Nat.sub_add_cancel hlt.le]
            omega
          omega
        rw [← hmul, Nat.mul_div_cancel_left x (by omega)]
    rcases lt_or_gt_of_ne hceq with hlt | hgt
    · exact hx (hmem_forb hlt hcV hcU htV hsU hsum_eq.symm)
    · exact hx (hmem_forb hgt hcU hcV hsU htV hsum_eq)

/-- **General Greedy Infinite `B_h` Lower Bound (`|A ∩ [1, N]| ≫_h N^{1/(2h - 1)}`):**
For every `h ≥ 2`, there exists an infinite `B_h`-set `A ⊆ ℕ` whose counting function satisfies
`((N - 1) / (h^2 (h + 1) + 2))^{1/(2h - 1)} ≤ |A ∩ [1, N]|` for all `N ≥ 2`
(in particular `≫ N^{1/3}` for Sidon sets `h = 2`, and `≫ N^{1/5}` for `B_3` sets `h = 3`). -/
theorem ppl124_greedy_Bh_lower_bound (h : ℕ) (hh : 2 ≤ h) :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ s t : Multiset ℕ, s.card = h → t.card = h →
        (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t) ∧
      ∀ N : ℕ, 2 ≤ N →
        (((N - 1 : ℕ) : ℝ) / ((h ^ 2 * (h + 1) + 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / (2 * (h : ℝ) - 1)) ≤
          ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
  classical
  -- Recursive construction of finite B_h sets S_n of card n + 1 with elements ≤ C_h * n^(2h-1) + 1
  let K : ℕ := h ^ 2 * (h + 1) + 1
  have hnext : ∀ S : Finset ℕ, ∃ x : ℕ, 1 ≤ x ∧ x ≤ (forbBh h S).card + 1 ∧ x ∉ forbBh h S := by
    intro S
    by_contra hnone
    push Not at hnone
    have hsub : Finset.Icc 1 ((forbBh h S).card + 1) ⊆ forbBh h S := by
      intro x hx; simp only [Finset.mem_Icc] at hx; exact hnone x hx.1 hx.2
    have hcard := Finset.card_le_card hsub
    simp at hcard
  let nextElem : Finset ℕ → ℕ := fun S => Classical.choose (hnext S)
  let seq : ℕ → Finset ℕ := Nat.rec {1} (fun _ S => insert (nextElem S) S)
  have hseq_props : ∀ n : ℕ,
      (seq n).card = n + 1 ∧
      (∀ x ∈ seq n, 1 ≤ x ∧ x ≤ K * n ^ (2 * h - 1) + 1) ∧
      (∀ s t : Multiset ℕ, s.card = h → t.card = h →
        (∀ u ∈ s, u ∈ seq n) → (∀ u ∈ t, u ∈ seq n) → s.sum = t.sum → s = t) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [seq], ?_, ?_⟩
      · intro x hx; simp [seq] at hx; subst hx; omega
      · intro s t hs ht hsM htM _
        have hrep : ∀ m : Multiset ℕ, m.card = h → (∀ u ∈ m, u ∈ ({1} : Finset ℕ)) →
            m = Multiset.replicate h 1 := by
          intro m hm hmem
          rw [Multiset.eq_replicate]
          refine ⟨hm, fun u hu => ?_⟩
          have := hmem u hu; simpa using this
        exact (hrep s hs hsM).trans (hrep t ht htM).symm
    | succ m ih =>
      obtain ⟨hcard, hbd, hBh⟩ := ih
      have hspec := Classical.choose_spec (hnext (seq m))
      change 1 ≤ nextElem (seq m) ∧ nextElem (seq m) ≤ (forbBh h (seq m)).card + 1 ∧
        nextElem (seq m) ∉ forbBh h (seq m) at hspec
      have ⟨hnotmem, hBh'⟩ := insert_preserves_Bh hh hBh hspec.2.2
      have hforb_le : (forbBh h (seq m)).card ≤ K * (m + 1) ^ (2 * h - 1) := by
        have := forbBh_card_le h hh (seq m) (by omega)
        rwa [hcard] at this
      refine ⟨?_, ?_, hBh'⟩
      · change (insert (nextElem (seq m)) (seq m)).card = m + 2
        rw [Finset.card_insert_of_notMem hnotmem, hcard]
      · intro x hx
        change x ∈ insert (nextElem (seq m)) (seq m) at hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ⟨hspec.1, by omega⟩
        · have hprev := hbd x hx'
          have hpow : m ^ (2 * h - 1) ≤ (m + 1) ^ (2 * h - 1) :=
            Nat.pow_le_pow_left (Nat.le_succ m) _
          exact ⟨hprev.1, by nlinarith⟩
  have hseq_mono : ∀ m n : ℕ, m ≤ n → seq m ⊆ seq n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Finset.Subset.rfl
    | succ k _ ih => exact ih.trans (Finset.subset_insert _ _)
  let A : Set ℕ := {x : ℕ | ∃ n : ℕ, x ∈ seq n}
  have hA_Bh : ∀ s t : Multiset ℕ, s.card = h → t.card = h →
      (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) → s.sum = t.sum → s = t := by
    intro s t hs ht hsA htA hsum
    -- Every element of s + t belongs to some seq n; take max n
    have hex : ∀ m : Multiset ℕ, (∀ x ∈ m, x ∈ A) → ∃ N : ℕ, ∀ x ∈ m, x ∈ seq N := by
      intro m hm
      induction m using Multiset.induction_on with
      | empty => exact ⟨0, by simp⟩
      | cons a u ih =>
        obtain ⟨n₁, hn₁⟩ := hm a (Multiset.mem_cons_self a u)
        obtain ⟨n₂, hn₂⟩ := ih (fun x hx => hm x (Multiset.mem_cons_of_mem hx))
        refine ⟨max n₁ n₂, fun x hx => ?_⟩
        rcases Multiset.mem_cons.mp hx with rfl | hx'
        · exact hseq_mono n₁ _ (le_max_left _ _) hn₁
        · exact hseq_mono n₂ _ (le_max_right _ _) (hn₂ x hx')
    obtain ⟨n₁, hn₁⟩ := hex s hsA
    obtain ⟨n₂, hn₂⟩ := hex t htA
    let n := max n₁ n₂
    exact (hseq_props n).2.2 s t hs ht
      (fun x hx => hseq_mono n₁ n (le_max_left _ _) (hn₁ x hx))
      (fun x hx => hseq_mono n₂ n (le_max_right _ _) (hn₂ x hx)) hsum
  have hA_inf : A.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro M
    have hcard_gt : M + 1 < (seq (M + 1)).card := by rw [(hseq_props (M + 1)).1]; omega
    by_contra hle
    push Not at hle
    have hsub : seq (M + 1) ⊆ Finset.Icc 0 M := by
      intro x hx
      simp only [Finset.mem_Icc]
      exact ⟨Nat.zero_le _, hle x ⟨M + 1, hx⟩⟩
    have hc := Finset.card_le_card hsub
    simp at hc; omega
  refine ⟨A, hA_inf, hA_Bh, fun N hN => ?_⟩
  -- For any N ≥ 2, let m be maximal with K * m^(2h-1) + 1 ≤ N; then seq m ⊆ A ∩ [1, N]
  have hex_m : ∃ m : ℕ, K * (m + 1) ^ (2 * h - 1) + 1 > N := by
    refine ⟨N, ?_⟩
    have hK1 : 1 ≤ K := by dsimp only [K]; omega
    have hpow : N + 1 ≤ (N + 1) ^ (2 * h - 1) := by
      calc N + 1 = (N + 1) ^ 1 := (pow_one _).symm
        _ ≤ (N + 1) ^ (2 * h - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  let m0 := Nat.find hex_m
  have hm0_spec : N < K * (m0 + 1) ^ (2 * h - 1) + 1 := Nat.find_spec hex_m
  have hsub : ∀ x ∈ seq m0, x ∈ A ∩ Set.Icc 1 N := by
    by_cases hm0 : m0 = 0
    · rw [hm0]; intro x hx
      have hx1 : x ∈ ({1} : Finset ℕ) := hx
      rw [Finset.mem_singleton] at hx1; subst hx1
      exact ⟨⟨0, Finset.mem_singleton_self 1⟩, by omega, by omega⟩
    · have hprev : ¬ (K * m0 ^ (2 * h - 1) + 1 > N) := by
        have := Nat.find_min hex_m (show m0 - 1 < m0 by omega)
        rwa [Nat.sub_add_cancel (by omega)] at this
      push Not at hprev
      intro x hx
      have hxb := (hseq_props m0).2.1 x hx
      exact ⟨⟨m0, hx⟩, hxb.1, hxb.2.trans hprev⟩
  have hcard_ge : m0 + 1 ≤ (A ∩ Set.Icc 1 N).ncard := by
    rw [← (hseq_props m0).1, ← Set.ncard_coe_finset (seq m0)]
    exact Set.ncard_le_ncard (fun x hx => hsub x (Finset.mem_coe.mp hx))
      ((Set.finite_Icc 1 N).subset Set.inter_subset_right)
  have hN_le : N - 1 ≤ (h ^ 2 * (h + 1) + 2) * (m0 + 1) ^ (2 * h - 1) := by
    have : N - 1 ≤ K * (m0 + 1) ^ (2 * h - 1) := by omega
    have hK_le : K ≤ h ^ 2 * (h + 1) + 2 := by dsimp only [K]; omega
    exact this.trans (Nat.mul_le_mul_right _ hK_le)
  have hN_R : ((N - 1 : ℕ) : ℝ) / ((h ^ 2 * (h + 1) + 2 : ℕ) : ℝ) ≤
      ((m0 + 1 : ℕ) : ℝ) ^ (2 * h - 1) := by
    rw [div_le_iff₀ (by positivity)]
    have hcast : ((N - 1 : ℕ) : ℝ) ≤
        (((h ^ 2 * (h + 1) + 2) * (m0 + 1) ^ (2 * h - 1) : ℕ) : ℝ) := by exact_mod_cast hN_le
    push_cast at hcast ⊢
    linarith
  have hroot : (((N - 1 : ℕ) : ℝ) / ((h ^ 2 * (h + 1) + 2 : ℕ) : ℝ)) ^ ((1 : ℝ) / (2 * (h : ℝ) - 1)) ≤
      ((m0 + 1 : ℕ) : ℝ) := by
    have hexp_pos : (0 : ℝ) < 2 * (h : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
      linarith
    have h1 := Real.rpow_le_rpow (by positivity) hN_R (by positivity : (0 : ℝ) ≤ 1 / (2 * (h : ℝ) - 1))
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at h1
    have hexp : ((2 * h - 1 : ℕ) : ℝ) * (1 / (2 * (h : ℝ) - 1)) = 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      field_simp
    rwa [hexp, Real.rpow_one] at h1
  exact hroot.trans (by exact_mod_cast hcard_ge)

/-- **Mian–Chowla Greedy Infinite Sidon Set (`|A ∩ [1, N]| ≫ N^{1/3}`):**
Specialization of the greedy `B_h` construction to `h = 2`: there exists an infinite Sidon set
`A ⊆ ℕ` with `((N - 1) / 14)^{1/3} ≤ |A ∩ [1, N]|` for all `N ≥ 2`. -/
theorem ppl124_mian_chowla_greedy_sidon :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) ∧
      ∀ N : ℕ, 2 ≤ N →
        (((N - 1 : ℕ) : ℝ) / 14) ^ ((1 : ℝ) / 3) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
  obtain ⟨A, hInf, hB2, hbd⟩ := ppl124_greedy_Bh_lower_bound 2 (by omega)
  refine ⟨A, hInf, ?_, ?_⟩
  · intro a₁ ha1 a₂ ha2 b₁ hb1 b₂ hb2 hle1 hle2 hsum
    have hm := hB2 {a₁, a₂} {b₁, b₂} (by simp) (by simp)
      (fun x hx => by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption)
      (fun x hx => by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption)
      (by simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]; omega)
    have ha1_mem : a₁ ∈ ({b₁, b₂} : Multiset ℕ) := by rw [← hm]; simp
    have ha2_mem : a₂ ∈ ({b₁, b₂} : Multiset ℕ) := by rw [← hm]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha1_mem ha2_mem
    omega
  · intro N hN
    have h := hbd N hN
    convert h using 2 <;> norm_num

/-!
## Part III-B — Krückeberg (1961) Landmark Upper-Density Construction (`limsup |A ∩ [1, N]| / √N ≥ 1 / √2`, PPL 018)
-/

/-- Ruzsa's (1993) modular finite-field Sidon set of size `p - 1` inside `[0, p(p - 1) - 1]`. -/
private lemma ruzsa_1993_finite_sidon (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∃ R : Finset ℕ, R.card = p - 1 ∧
      (∀ x ∈ R, x < p * (p - 1)) ∧
      (∀ a₁ ∈ R, ∀ a₂ ∈ R, ∀ b₁ ∈ R, ∀ b₂ ∈ R,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard_units : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hord : orderOf g = p - 1 := by
    rw [← hcard_units, ← Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  -- Define x_i = (p * i + (p - 1) * (p - val(g^i))) % (p * (p - 1)) for i ∈ Icc 1 (p - 1)
  let rVal : ℕ → ℕ := fun i => ((g ^ i : (ZMod p)ˣ) : ZMod p).val
  let xMap : ℕ → ℕ := fun i => (p * i + (p - 1) * (p - rVal i)) % (p * (p - 1))
  have hr_lt : ∀ i, rVal i < p := fun i => ZMod.val_lt _
  have hr_cast : ∀ i, (rVal i : ZMod p) = ((g ^ i : (ZMod p)ˣ) : ZMod p) := fun i => ZMod.natCast_zmod_val _
  have hx_lt : ∀ i, xMap i < p * (p - 1) := fun i =>
    Nat.mod_lt _ (Nat.mul_pos hp.pos (by omega))
  have hx_mod_pm1 : ∀ i, xMap i % (p - 1) = i % (p - 1) := by
    intro i
    dsimp only [xMap]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_left (p - 1) p)]
    have hsplit : p * i + (p - 1) * (p - rVal i) = i + (p - 1) * (i + (p - rVal i)) := by
      have hrl := hr_lt i
      zify [show 1 ≤ p by omega, show rVal i ≤ p by omega]
      ring
    rw [hsplit, Nat.add_mul_mod_self_left]
  have hx_mod_p : ∀ i, (xMap i : ZMod p) = ((g ^ i : (ZMod p)ˣ) : ZMod p) := by
    intro i
    have hmod : xMap i % p = rVal i := by
      dsimp only [xMap]
      rw [Nat.mod_mod_of_dvd _ (dvd_mul_right p (p - 1))]
      have hrl := hr_lt i
      have hsplit : p * i + (p - 1) * (p - rVal i) = rVal i + p * (i + (p - 1 - rVal i)) := by
        zify [show 1 ≤ p by omega, show rVal i ≤ p by omega, show rVal i ≤ p - 1 by omega]
        ring
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrl]
    have h1 : ((xMap i % p : ℕ) : ZMod p) = (xMap i : ZMod p) := ZMod.natCast_mod (xMap i) p
    rw [← h1, hmod, hr_cast]
  have hg_pow_inj : ∀ i ∈ Finset.Icc 1 (p - 1), ∀ j ∈ Finset.Icc 1 (p - 1),
      ((g ^ i : (ZMod p)ˣ) : ZMod p) = ((g ^ j : (ZMod p)ˣ) : ZMod p) → i = j := by
    intro i hi j hj heq
    simp only [Finset.mem_Icc] at hi hj
    have hu : g ^ i = g ^ j := Units.ext heq
    have hmod : i ≡ j [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hu
    rw [hord] at hmod
    have hsub : i - 1 < p - 1 ∧ j - 1 < p - 1 := by omega
    by_cases h1 : i = p - 1
    · subst h1
      have : j % (p - 1) = 0 := by rw [← hmod]; simp
      have hdvd : p - 1 ∣ j := Nat.dvd_of_mod_eq_zero this
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · by_cases h2 : j = p - 1
      · subst h2
        have : i % (p - 1) = 0 := by rw [hmod]; simp
        have hdvd : p - 1 ∣ i := Nat.dvd_of_mod_eq_zero this
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · have hi' : i % (p - 1) = i := Nat.mod_eq_of_lt (by omega)
        have hj' : j % (p - 1) = j := Nat.mod_eq_of_lt (by omega)
        change i % (p - 1) = j % (p - 1) at hmod
        omega
  have hx_inj : Set.InjOn xMap (Finset.Icc 1 (p - 1) : Set ℕ) := by
    intro i hi j hj heq
    apply hg_pow_inj i hi j hj
    rw [← hx_mod_p i, ← hx_mod_p j, heq]
  refine ⟨(Finset.Icc 1 (p - 1)).image xMap, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hx_inj]; simp
  · intro x hx; simp only [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact hx_lt i
  · intro a₁ ha1 a₂ ha2 b₁ hb1 b₂ hb2 hle1 hle2 hsum
    simp only [Finset.mem_image] at ha1 ha2 hb1 hb2
    obtain ⟨i, hi, rfl⟩ := ha1
    obtain ⟨j, hj, rfl⟩ := ha2
    obtain ⟨k, hk, rfl⟩ := hb1
    obtain ⟨l, hl, rfl⟩ := hb2
    -- Mod (p - 1): i + j ≡ k + l (mod p - 1) ⇒ g^i * g^j = g^k * g^l
    have hmod_sum : (i + j) % (p - 1) = (k + l) % (p - 1) := by
      have h1 : (xMap i + xMap j) % (p - 1) = (xMap k + xMap l) % (p - 1) := congrArg (· % (p - 1)) hsum
      have hlhs : (xMap i + xMap j) % (p - 1) = (i + j) % (p - 1) := by
        rw [Nat.add_mod, hx_mod_pm1 i, hx_mod_pm1 j, ← Nat.add_mod]
      have hrhs : (xMap k + xMap l) % (p - 1) = (k + l) % (p - 1) := by
        rw [Nat.add_mod, hx_mod_pm1 k, hx_mod_pm1 l, ← Nat.add_mod]
      rw [hlhs, hrhs] at h1
      exact h1
    have hprod_u : g ^ (i + j) = g ^ (k + l) :=
      pow_eq_pow_iff_modEq.mpr (by rw [hord]; exact hmod_sum)
    have hprod : ((g ^ i : (ZMod p)ˣ) : ZMod p) * ((g ^ j : (ZMod p)ˣ) : ZMod p) =
        ((g ^ k : (ZMod p)ˣ) : ZMod p) * ((g ^ l : (ZMod p)ˣ) : ZMod p) := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hprod_u
      simpa [pow_add] using this
    -- Mod p: g^i + g^j = g^k + g^l
    have hadd : ((g ^ i : (ZMod p)ˣ) : ZMod p) + ((g ^ j : (ZMod p)ˣ) : ZMod p) =
        ((g ^ k : (ZMod p)ˣ) : ZMod p) + ((g ^ l : (ZMod p)ˣ) : ZMod p) := by
      have := congrArg (fun n : ℕ => (n : ZMod p)) hsum
      push_cast at this
      rwa [hx_mod_p i, hx_mod_p j, hx_mod_p k, hx_mod_p l] at this
    -- In field ZMod p: (a - c)(a - d) = 0 ⇒ a = c ∨ a = d
    set α := ((g ^ i : (ZMod p)ˣ) : ZMod p)
    set β := ((g ^ j : (ZMod p)ˣ) : ZMod p)
    set γ := ((g ^ k : (ZMod p)ˣ) : ZMod p)
    set δ := ((g ^ l : (ZMod p)ˣ) : ZMod p)
    have hfac : (α - γ) * (α - δ) = 0 := by
      calc (α - γ) * (α - δ)
          = α ^ 2 - (γ + δ) * α + γ * δ := by ring
        _ = α ^ 2 - (α + β) * α + α * β := by rw [← hadd, ← hprod]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · have hac : α = γ := sub_eq_zero.mp h1
      have hbd : β = δ := by linear_combination hadd - hac
      have hik : i = k := hg_pow_inj i hi k hk hac
      have hjl : j = l := hg_pow_inj j hj l hl hbd
      subst hik; subst hjl; exact ⟨rfl, rfl⟩
    · have had : α = δ := sub_eq_zero.mp h1
      have hbc : β = γ := by linear_combination hadd - had
      have hil : i = l := hg_pow_inj i hi l hl had
      have hjk : j = k := hg_pow_inj j hj k hk hbc
      subst hil; subst hjk
      have heq1 : xMap i = xMap j := by omega
      exact ⟨heq1, heq1.symm⟩

/-- **Krückeberg (1961) Infinite Sidon Upper-Density Theorem (`limsup |A ∩ [1, N]| / √N ≥ 1 / √2`, PPL 018):**
There exists an infinite Sidon set `A ⊆ ℕ` achieving Krückeberg's landmark `1 / √2` upper-density
constant: for every `ε > 0`, infinitely many `N` satisfy `(1 / √2 - ε) √N ≤ |A ∩ [1, N]|`, and
`1 / √2 ≤ limsup_{N → ∞} |A ∩ [1, N]| / √N`. -/
theorem ppl124_kruckeberg_1961_limsup_inv_sqrt_two :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) ∧
      (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
        (1 / Real.sqrt 2 - ε) * Real.sqrt (N : ℝ) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ)) ∧
      (1 / Real.sqrt 2 ≤
        limsup (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt (N : ℝ)) atTop) := by
  classical
  -- Step function: given finite Sidon S ⊆ [1, M] and index n, extend with a pruned Ruzsa block
  let stepEx : ∀ (n M : ℕ) (S : Finset ℕ),
      (∀ x ∈ S, 1 ≤ x ∧ x ≤ M) →
      (∀ a₁ ∈ S, ∀ a₂ ∈ S, ∀ b₁ ∈ S, ∀ b₂ ∈ S,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) →
      ∃ (p M' : ℕ) (S' : Finset ℕ),
        S ⊆ S' ∧
        (n + 2) * (M + 2) < p ∧
        M < M' ∧ M' ≤ 2 * p ^ 2 + M + 1 ∧
        p - 1 - M ≤ S'.card ∧
        (∀ x ∈ S', 1 ≤ x ∧ x ≤ M') ∧
        (∀ a₁ ∈ S', ∀ a₂ ∈ S', ∀ b₁ ∈ S', ∀ b₂ ∈ S',
          a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) := by
    intro n M S hS_bd hS_sid
    obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (max 3 ((n + 2) * (M + 2) + 1))
    have hp3 : 3 ≤ p := (le_max_left _ _).trans hp_ge
    have hp_gt : (n + 2) * (M + 2) < p := by have := (le_max_right 3 _).trans hp_ge; omega
    obtain ⟨R, hR_card, hR_lt, hR_sid⟩ := ruzsa_1993_finite_sidon p hp_prime hp3
    -- Delete at most M elements from R that have a close predecessor within distance M
    let Bad := R.filter (fun s => ∃ s' ∈ R, s' < s ∧ s - s' ≤ M)
    have hBad_card : Bad.card ≤ M := by
      have hpick : ∀ s ∈ Bad, ∃ s' ∈ R, s' < s ∧ s - s' ≤ M := fun s hs => (Finset.mem_filter.mp hs).2
      have hcard_le : Bad.card ≤ (Finset.Icc 1 M).card := by
        refine Finset.card_le_card_of_injOn
          (fun s => if h : s ∈ Bad then s - Classical.choose (hpick s h) else 0) ?_ ?_
        · intro s hs
          have hs' : s ∈ Bad := hs
          simp only [hs', ↓reduceDIte, Finset.mem_coe, Finset.mem_Icc]
          have hspec := Classical.choose_spec (hpick s hs')
          omega
        · intro s₁ hs₁ s₂ hs₂ heq
          have hs₁' : s₁ ∈ Bad := hs₁
          have hs₂' : s₂ ∈ Bad := hs₂
          simp only [hs₁', hs₂', ↓reduceDIte] at heq
          set t₁ := Classical.choose (hpick s₁ hs₁')
          set t₂ := Classical.choose (hpick s₂ hs₂')
          have ht₁ := Classical.choose_spec (hpick s₁ hs₁')
          have ht₂ := Classical.choose_spec (hpick s₂ hs₂')
          have hs₁R : s₁ ∈ R := (Finset.mem_filter.mp hs₁').1
          have hs₂R : s₂ ∈ R := (Finset.mem_filter.mp hs₂').1
          have hsum : s₁ + t₂ = s₂ + t₁ := by omega
          rcases le_total s₁ t₂ with h1 | h1 <;> rcases le_total s₂ t₁ with h2 | h2
          · have := hR_sid s₁ hs₁R t₂ ht₂.1 s₂ hs₂R t₁ ht₁.1 h1 h2 hsum; omega
          · have := hR_sid s₁ hs₁R t₂ ht₂.1 t₁ ht₁.1 s₂ hs₂R h1 h2 (by omega); omega
          · have := hR_sid t₂ ht₂.1 s₁ hs₁R s₂ hs₂R t₁ ht₁.1 h1 h2 (by omega); omega
          · have := hR_sid t₂ ht₂.1 s₁ hs₁R t₁ ht₁.1 s₂ hs₂R h1 h2 (by omega); omega
      simpa using hcard_le
    let R' := R \ Bad
    have hR'_card : p - 1 - M ≤ R'.card := by
      have hsub : Bad ⊆ R := Finset.filter_subset _ _
      rw [Finset.card_sdiff_of_subset hsub, hR_card]
      omega
    have hR'_no_close : ∀ s₁ ∈ R', ∀ s₂ ∈ R', s₁ < s₂ → M < s₂ - s₁ := by
      intro s₁ hs1 s₂ hs2 hlt
      by_contra hle; push Not at hle
      have hs2_bad : s₂ ∈ Bad := by
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.mp hs2).1, s₁, (Finset.mem_sdiff.mp hs1).1, hlt, hle⟩
      exact (Finset.mem_sdiff.mp hs2).2 hs2_bad
    let T := M + p ^ 2 + 1
    let B := R'.image (· + T)
    let S' := S ∪ B
    let M' := T + p ^ 2
    have hM_lt_p2 : M < p ^ 2 := by nlinarith
    have hR'_lt : ∀ s ∈ R', s < p ^ 2 := fun s hs => by
      have := hR_lt s (Finset.mem_sdiff.mp hs).1
      have : p * (p - 1) ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left p (Nat.sub_le p 1)
      omega
    have hB_card : B.card = R'.card :=
      Finset.card_image_of_injective R' (fun a b h => by omega)
    have hS'_sid : ∀ a₁ ∈ S', ∀ a₂ ∈ S', ∀ b₁ ∈ S', ∀ b₂ ∈ S',
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂ := by
      intro a₁ ha1 a₂ ha2 b₁ hb1 b₂ hb2 hle1 hle2 hsum
      have hS_lt_T : ∀ x ∈ S, x ≤ M := fun x hx => (hS_bd x hx).2
      have hB_range : ∀ x ∈ B, T ≤ x ∧ x < T + p ^ 2 := by
        intro x hx; simp only [B, Finset.mem_image] at hx
        obtain ⟨s, hs, rfl⟩ := hx
        exact ⟨by omega, by have := hR'_lt s hs; omega⟩
      -- Case split on S vs B membership; the 3 sum bands [0, 2M], [T, 2T-2], [2T, ∞) are disjoint!
      rcases Finset.mem_union.mp ha1 with ha1S | ha1B <;>
      rcases Finset.mem_union.mp ha2 with ha2S | ha2B <;>
      rcases Finset.mem_union.mp hb1 with hb1S | hb1B <;>
      rcases Finset.mem_union.mp hb2 with hb2S | hb2B
      · exact hS_sid a₁ ha1S a₂ ha2S b₁ hb1S b₂ hb2S hle1 hle2 hsum
      · exfalso; have := hS_lt_T a₁ ha1S; have := hS_lt_T a₂ ha2S; have := hB_range b₂ hb2B; omega
      · exfalso; have := hS_lt_T a₁ ha1S; have := hS_lt_T a₂ ha2S; have := hB_range b₁ hb1B; omega
      · exfalso; have := hS_lt_T a₁ ha1S; have := hS_lt_T a₂ ha2S; have := hB_range b₁ hb1B; omega
      · exfalso; have := hB_range a₂ ha2B; have := hS_lt_T b₁ hb1S; have := hS_lt_T b₂ hb2S; omega
      · -- a₁, b₁ ∈ S and a₂, b₂ ∈ B
        simp only [B, Finset.mem_image] at ha2B hb2B
        obtain ⟨s₁, hs1, rfl⟩ := ha2B
        obtain ⟨s₂, hs2, rfl⟩ := hb2B
        have h1 := hS_lt_T a₁ ha1S; have h2 := hS_lt_T b₁ hb1S
        rcases lt_trichotomy s₁ s₂ with hlt | rfl | hgt
        · exfalso; have := hR'_no_close s₁ hs1 s₂ hs2 hlt; omega
        · exact ⟨by omega, rfl⟩
        · exfalso; have := hR'_no_close s₂ hs2 s₁ hs1 hgt; omega
      · exfalso; have := hB_range b₁ hb1B; have := hS_lt_T b₂ hb2S; omega
      · exfalso; have := hS_lt_T a₁ ha1S; have := hB_range a₂ ha2B; have := hB_range b₁ hb1B; have := hB_range b₂ hb2B; omega
      · exfalso; have := hB_range a₁ ha1B; have := hS_lt_T a₂ ha2S; omega
      · exfalso; have := hB_range a₁ ha1B; have := hS_lt_T a₂ ha2S; omega
      · exfalso; have := hB_range a₁ ha1B; have := hS_lt_T a₂ ha2S; omega
      · exfalso; have := hB_range a₁ ha1B; have := hS_lt_T a₂ ha2S; omega
      · exfalso; have := hB_range a₁ ha1B; have := hS_lt_T b₁ hb1S; have := hS_lt_T b₂ hb2S; omega
      · exfalso; have := hB_range a₁ ha1B; have := hB_range a₂ ha2B; have := hS_lt_T b₁ hb1S; have := hB_range b₂ hb2B; omega
      · exfalso; have := hB_range b₁ hb1B; have := hS_lt_T b₂ hb2S; omega
      · -- all 4 in B
        simp only [B, Finset.mem_image] at ha1B ha2B hb1B hb2B
        obtain ⟨s₁, hs1, rfl⟩ := ha1B
        obtain ⟨s₂, hs2, rfl⟩ := ha2B
        obtain ⟨t₁, ht1, rfl⟩ := hb1B
        obtain ⟨t₂, ht2, rfl⟩ := hb2B
        have ⟨e1, e2⟩ := hR_sid s₁ (Finset.mem_sdiff.mp hs1).1 s₂ (Finset.mem_sdiff.mp hs2).1
          t₁ (Finset.mem_sdiff.mp ht1).1 t₂ (Finset.mem_sdiff.mp ht2).1
          (by omega) (by omega) (by omega)
        exact ⟨by omega, by omega⟩
    refine ⟨p, M', S', Finset.subset_union_left, hp_gt, by dsimp only [M', T]; nlinarith,
      by dsimp only [M', T]; omega, ?_, ?_, hS'_sid⟩
    · calc p - 1 - M ≤ R'.card := hR'_card
        _ = B.card := hB_card.symm
        _ ≤ S'.card := Finset.card_le_card Finset.subset_union_right
    · intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxB
      · have := hS_bd x hxS; dsimp only [M', T]; omega
      · simp only [B, Finset.mem_image] at hxB
        obtain ⟨s, hs, rfl⟩ := hxB
        have := hR'_lt s hs
        dsimp only [M', T]; omega
  -- Iterate stepEx to build chain (M_n, S_n) with witness primes p_n
  let State := { st : ℕ × Finset ℕ //
    (∀ x ∈ st.2, 1 ≤ x ∧ x ≤ st.1) ∧
    (∀ a₁ ∈ st.2, ∀ a₂ ∈ st.2, ∀ b₁ ∈ st.2, ∀ b₂ ∈ st.2,
      a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) }
  let initState : State := ⟨(1, {1}),
    ⟨fun x hx => by simp at hx; omega,
     fun a₁ ha1 a₂ ha2 b₁ hb1 b₂ hb2 _ _ _ => by simp at ha1 ha2 hb1 hb2; omega⟩⟩
  let nextState : ℕ → State → State := fun n st =>
    let ex := stepEx n st.1.1 st.1.2 st.2.1 st.2.2
    let p := Classical.choose ex
    let ex1 := Classical.choose_spec ex
    let M' := Classical.choose ex1
    let ex2 := Classical.choose_spec ex1
    let S' := Classical.choose ex2
    let h := Classical.choose_spec ex2
    ⟨(M', S'), h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  let chain : ℕ → State := Nat.rec initState nextState
  have hstep_prop : ∀ n : ℕ,
      (chain n).1.2 ⊆ (chain (n + 1)).1.2 ∧
      ∃ p : ℕ, (n + 2) * ((chain n).1.1 + 2) < p ∧
        (chain n).1.1 < (chain (n + 1)).1.1 ∧
        (chain (n + 1)).1.1 ≤ 2 * p ^ 2 + (chain n).1.1 + 1 ∧
        p - 1 - (chain n).1.1 ≤ (chain (n + 1)).1.2.card := by
    intro n
    change (chain n).1.2 ⊆ (nextState n (chain n)).1.2 ∧ _
    dsimp only [nextState]
    set ex := stepEx n (chain n).1.1 (chain n).1.2 (chain n).2.1 (chain n).2.2
    set p := Classical.choose ex
    set ex1 := Classical.choose_spec ex
    set M' := Classical.choose ex1
    set ex2 := Classical.choose_spec ex1
    set S' := Classical.choose ex2
    have h := Classical.choose_spec ex2
    exact ⟨h.1, p, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  have hchain_mono : ∀ m n : ℕ, m ≤ n → (chain m).1.2 ⊆ (chain n).1.2 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Finset.Subset.rfl
    | succ k _ ih => exact ih.trans (hstep_prop k).1
  have hM_strict : ∀ n : ℕ, (chain n).1.1 < (chain (n + 1)).1.1 := fun n =>
    (hstep_prop n).2.choose_spec.2.1
  have hM_ge : ∀ n : ℕ, n + 1 ≤ (chain n).1.1 := by
    intro n
    induction n with
    | zero => simp [chain, initState]
    | succ k ih => have := hM_strict k; omega
  let A : Set ℕ := ⋃ n : ℕ, ((chain n).1.2 : Set ℕ)
  have hA_sid : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
      a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂ := by
    intro a₁ ha1 a₂ ha2 b₁ hb1 b₂ hb2 hle1 hle2 hsum
    obtain ⟨n₁, hn1⟩ := Set.mem_iUnion.mp ha1
    obtain ⟨n₂, hn2⟩ := Set.mem_iUnion.mp ha2
    obtain ⟨n₃, hn3⟩ := Set.mem_iUnion.mp hb1
    obtain ⟨n₄, hn4⟩ := Set.mem_iUnion.mp hb2
    let n := max (max n₁ n₂) (max n₃ n₄)
    exact (chain n).2.2 a₁ (hchain_mono n₁ n (le_trans (le_max_left _ _) (le_max_left _ _)) hn1)
      a₂ (hchain_mono n₂ n (le_trans (le_max_right _ _) (le_max_left _ _)) hn2)
      b₁ (hchain_mono n₃ n (le_trans (le_max_left _ _) (le_max_right _ _)) hn3)
      b₂ (hchain_mono n₄ n (le_trans (le_max_right _ _) (le_max_right _ _)) hn4)
      hle1 hle2 hsum
  -- Ratio along the subsequence N_n = (chain (n + 1)).1.1 → ≥ 1 / √2
  have hratio_subseq : ∀ n : ℕ,
      (1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) / Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) ≤
        ((A ∩ Set.Icc 1 (chain (n + 1)).1.1).ncard : ℝ) / Real.sqrt ((chain (n + 1)).1.1 : ℝ) := by
    intro n
    obtain ⟨_, p, hp_gt, hMlt, hMle, hcard_ge⟩ := hstep_prop n
    set Mn := (chain n).1.1
    set Mn1 := (chain (n + 1)).1.1
    have hsub : (chain (n + 1)).1.2 ⊆ (Finset.Icc 1 Mn1).filter (fun x => x ∈ A) := by
      intro x hx
      have hxb := (chain (n + 1)).2.1 x hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hxb, Set.mem_iUnion.mpr ⟨n + 1, hx⟩⟩
    rw [ncard_inter_Icc_eq_filter_card]
    have hcard_R : ((p - 1 - Mn : ℕ) : ℝ) ≤ (((Finset.Icc 1 Mn1).filter (fun x => x ∈ A)).card : ℝ) := by
      exact_mod_cast (hcard_ge.trans (Finset.card_le_card hsub))
    have hn2_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (by omega)
    have hnum_lb : (1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) ≤ ((p - 1 - Mn : ℕ) : ℝ) := by
      have h1 : (n + 2) * (Mn + 1) ≤ p := by nlinarith
      have h1R : ((n + 2 : ℕ) : ℝ) * ((Mn : ℝ) + 1) ≤ (p : ℝ) := by
        have : (((n + 2) * (Mn + 1) : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
        push_cast at this ⊢; linarith
      have hsub_cast : ((p - 1 - Mn : ℕ) : ℝ) = (p : ℝ) - 1 - (Mn : ℝ) := by
        have hle : 1 + Mn ≤ p := by nlinarith
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
      rw [hsub_cast]
      have hdiv : (Mn : ℝ) + 1 ≤ (p : ℝ) / ((n + 2 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hn2_pos]; linarith
      linarith [show (1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) = (p : ℝ) - (p : ℝ) / ((n + 2 : ℕ) : ℝ) by ring]
    have hden_ub : (Mn1 : ℝ) ≤ (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) ^ 2 := by
      have h1 : (n + 2) * (Mn + 1) ≤ p ^ 2 := by
        have hp_le_sq : p ≤ p ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left p (by omega)
        nlinarith
      have h1R : ((n + 2 : ℕ) : ℝ) * ((Mn : ℝ) + 1) ≤ (p : ℝ) ^ 2 := by
        have : (((n + 2) * (Mn + 1) : ℕ) : ℝ) ≤ ((p ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
        push_cast at this ⊢; linarith
      have hMleR : (Mn1 : ℝ) ≤ 2 * (p : ℝ) ^ 2 + (Mn : ℝ) + 1 := by
        have : (Mn1 : ℝ) ≤ ((2 * p ^ 2 + Mn + 1 : ℕ) : ℝ) := by exact_mod_cast hMle
        push_cast at this; linarith
      have hdiv : (Mn : ℝ) + 1 ≤ (p : ℝ) ^ 2 / ((n + 2 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hn2_pos]; linarith
      linarith [show (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) ^ 2 =
        2 * (p : ℝ) ^ 2 + (p : ℝ) ^ 2 / ((n + 2 : ℕ) : ℝ) by ring]
    have hsqrt_ub : Real.sqrt (Mn1 : ℝ) ≤ Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) := by
      calc Real.sqrt (Mn1 : ℝ)
          ≤ Real.sqrt ((2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) ^ 2) := Real.sqrt_le_sqrt hden_ub
        _ = Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * Real.sqrt ((p : ℝ) ^ 2) :=
            Real.sqrt_mul (by positivity) _
        _ = Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ) := by
            rw [Real.sqrt_sq hp_pos.le]
    have hMn1_pos : (0 : ℝ) < (Mn1 : ℝ) := Nat.cast_pos.mpr (by have := hM_ge (n + 1); omega)
    have hsqrt_pos : 0 < Real.sqrt (Mn1 : ℝ) := Real.sqrt_pos.mpr hMn1_pos
    have hnum_nn : 0 ≤ 1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
      have : (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ≤ 1 := div_le_one_of_le₀ this (by positivity)
      linarith
    calc (1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) / Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ))
        = ((1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ)) /
            (Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) * (p : ℝ)) := by
            field_simp
      _ ≤ (((Finset.Icc 1 Mn1).filter (fun x => x ∈ A)).card : ℝ) / Real.sqrt (Mn1 : ℝ) :=
          div_le_div₀ (by positivity) (hnum_lb.trans hcard_R) hsqrt_pos hsqrt_ub
  -- Deduce A.Infinite, frequent lower bound, and limsup ≥ 1 / √2
  have hfreq : ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
      (1 / Real.sqrt 2 - ε) * Real.sqrt (N : ℝ) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
    intro ε hε
    have htend : Tendsto (fun n : ℕ =>
        (1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) / Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)))
        atTop (nhds (1 / Real.sqrt 2)) := by
      have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (nhds 0) := by
        have h1 : Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
        exact (tendsto_inv_atTop_zero.comp h1).congr fun n => by simp [one_div]
      have hnum : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (nhds 1) := by
        simpa using tendsto_const_nhds.sub hinv
      have hden : Tendsto (fun n : ℕ => Real.sqrt (2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ))) atTop
          (nhds (Real.sqrt 2)) := by
        have h2 : Tendsto (fun n : ℕ => 2 + (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (nhds 2) := by
          simpa using tendsto_const_nhds.add hinv
        exact (Real.continuous_sqrt.tendsto 2).comp h2
      exact hnum.div hden (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hev := htend.eventually (Ioi_mem_nhds (show 1 / Real.sqrt 2 - ε < 1 / Real.sqrt 2 by linarith))
    rw [Filter.eventually_atTop] at hev
    obtain ⟨n₀, hn₀⟩ := hev
    rw [Filter.frequently_atTop]
    intro M
    let n := max n₀ M
    refine ⟨(chain (n + 1)).1.1, ?_, ?_⟩
    · have := hM_ge (n + 1); have : M ≤ n := le_max_right _ _; omega
    · have h1 : 1 / Real.sqrt 2 - ε ≤
          ((A ∩ Set.Icc 1 (chain (n + 1)).1.1).ncard : ℝ) / Real.sqrt ((chain (n + 1)).1.1 : ℝ) :=
        (hn₀ n (le_max_left _ _)).le.trans (hratio_subseq n)
      have hpos : 0 < Real.sqrt ((chain (n + 1)).1.1 : ℝ) :=
        Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by have := hM_ge (n + 1); omega))
      exact (le_div_iff₀ hpos).mp h1
  have hA_inf : A.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N, hN_ge, hN_bd⟩ := (Filter.frequently_atTop.mp (hfreq (1 / (2 * Real.sqrt 2)) (by positivity)))
      ((4 * hfin.toFinset.card + 8) ^ 2)
    have hcard_le : (A ∩ Set.Icc 1 N).ncard ≤ hfin.toFinset.card := by
      have hsub : A ∩ Set.Icc 1 N ⊆ hfin.toFinset := fun x hx => hfin.mem_toFinset.mpr hx.1
      calc (A ∩ Set.Icc 1 N).ncard ≤ (hfin.toFinset : Set ℕ).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = hfin.toFinset.card := Set.ncard_coe_finset _
    have hsqrt_ge : (4 * hfin.toFinset.card + 8 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      have h1 : ((4 * hfin.toFinset.card + 8 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN_ge
      have h2 := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_sq (Nat.cast_nonneg _)] at h2
      push_cast at h2; exact h2
    have hcoef : 1 / Real.sqrt 2 - 1 / (2 * Real.sqrt 2) = 1 / (2 * Real.sqrt 2) := by ring
    rw [hcoef] at hN_bd
    have hsqrt2_lt : Real.sqrt 2 < 2 := by
      have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 2 ^ 2)
      rwa [Real.sqrt_sq (by norm_num)] at this
    have hpos_c : (1 / 4 : ℝ) < 1 / (2 * Real.sqrt 2) := by
      rw [one_div_lt_one_div (by norm_num) (by positivity)]; linarith
    have hcard_R : ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hcard_le
    have h1 : (1 / 4 : ℝ) * (4 * (hfin.toFinset.card : ℝ) + 8) ≤
        (1 / (2 * Real.sqrt 2)) * Real.sqrt (N : ℝ) := by
      have hnn : (0 : ℝ) ≤ 4 * (hfin.toFinset.card : ℝ) + 8 := by positivity
      calc (1 / 4 : ℝ) * (4 * (hfin.toFinset.card : ℝ) + 8)
          ≤ (1 / (2 * Real.sqrt 2)) * (4 * (hfin.toFinset.card : ℝ) + 8) :=
            mul_le_mul_of_nonneg_right hpos_c.le hnn
        _ ≤ (1 / (2 * Real.sqrt 2)) * Real.sqrt (N : ℝ) :=
            mul_le_mul_of_nonneg_left hsqrt_ge (by positivity)
    linarith
  have hlimsup : 1 / Real.sqrt 2 ≤
      limsup (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt (N : ℝ)) atTop := by
    -- Bounded above by 2 (via finite Sidon bound a*(a-1) ≤ 2*N ⇒ a ≤ 2*√N for N ≥ 1)
    have hbdd_top : IsBoundedUnder (· ≤ ·) atTop
        (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt (N : ℝ)) := by
      refine ⟨2, eventually_map.mpr ?_⟩
      filter_upwards [eventually_ge_atTop 1] with N hN1
      have hfin := ppl124_finite_sidon_upper_bound A hA_sid N
      set a := (A ∩ Set.Icc 1 N).ncard
      have ha_le : (a : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
        by_cases ha1 : a ≤ 1
        · have h1 : (a : ℝ) ≤ 1 := by exact_mod_cast ha1
          have h2 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
            calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
              _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hN1)
          linarith
        · push Not at ha1
          have h2a : a ≤ 2 * (a - 1) := by omega
          have ha_sq : a ^ 2 ≤ 4 * N := by
            calc a ^ 2 = a * a := sq a
              _ ≤ a * (2 * (a - 1)) := Nat.mul_le_mul_left a h2a
              _ = 2 * (a * (a - 1)) := by ring
              _ ≤ 2 * (2 * N) := Nat.mul_le_mul_left 2 hfin
              _ = 4 * N := by ring
          have ha_sq_R : (a : ℝ) ^ 2 ≤ (2 * Real.sqrt (N : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
            have : ((a ^ 2 : ℕ) : ℝ) ≤ ((4 * N : ℕ) : ℝ) := by exact_mod_cast ha_sq
            push_cast at this; linarith
          have h := Real.sqrt_le_sqrt ha_sq_R
          rwa [Real.sqrt_sq (Nat.cast_nonneg a), Real.sqrt_sq (by positivity)] at h
      have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN1)
      exact (div_le_iff₀ hsqrtN_pos).mpr ha_le
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 : 1 / Real.sqrt 2 - ε ≤
        limsup (fun N : ℕ => ((A ∩ Set.Icc 1 N).ncard : ℝ) / Real.sqrt (N : ℝ)) atTop := by
      refine Filter.le_limsup_of_frequently_le ?_ hbdd_top
      refine ((hfreq ε hε).and_eventually (eventually_ge_atTop 1)).mono fun N ⟨hN, hN1⟩ => ?_
      have hsqrtN_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN1)
      exact (le_div_iff₀ hsqrtN_pos).mpr hN
    linarith
  exact ⟨A, hA_inf, hA_sid, hfreq, hlimsup⟩

/-!
## Part III-C — Ruzsa (1998) Standing 28-Year World-Record Infinite Sidon Set (`|A ∩ [1, N]| ≥ N^{√2 - 1 - o(1)}`, PPL 124 / #39)
-/

section Ruzsa1998

open MeasureTheory

-- Bit-block geometry: L r = 2r - 1, S k = k^2, W r = 2r + 5 = L r + 6, T k = k^2 + 6k
private def ruzsaL (r : ℕ) : ℕ := 2 * r - 1
private def ruzsaS (k : ℕ) : ℕ := k ^ 2
private def ruzsaW (r : ℕ) : ℕ := 2 * r + 5
private def ruzsaT (k : ℕ) : ℕ := k ^ 2 + 6 * k

private lemma ruzsaS_succ (k : ℕ) : ruzsaS (k + 1) = ruzsaS k + ruzsaL (k + 1) := by
  simp only [ruzsaS, ruzsaL]
  zify [show 1 ≤ 2 * (k + 1) by omega]
  ring

private lemma ruzsaT_succ (k : ℕ) : ruzsaT (k + 1) = ruzsaT k + ruzsaW (k + 1) := by
  simp only [ruzsaT, ruzsaW]; ring

private lemma ruzsa_packed_sum_lt (c : ℕ → ℕ) (K : ℕ)
    (hc : ∀ r ∈ Finset.Icc 1 K, c r < 2 ^ ruzsaW r) :
    ∑ r ∈ Finset.Icc 1 K, c r * 2 ^ ruzsaT (r - 1) < 2 ^ ruzsaT K := by
  induction K with
  | zero => simp [ruzsaT]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hlow : ∑ r ∈ Finset.Icc 1 k, c r * 2 ^ ruzsaT (r - 1) < 2 ^ ruzsaT k :=
      ih fun r hr => hc r (by simp only [Finset.mem_Icc] at hr ⊢; omega)
    have htop : c (k + 1) ≤ 2 ^ ruzsaW (k + 1) - 1 := by
      have := hc (k + 1) (by simp); omega
    have hpow_eq : 2 ^ ruzsaW (k + 1) * 2 ^ ruzsaT k = 2 ^ ruzsaT (k + 1) := by
      rw [← pow_add, add_comm, ← ruzsaT_succ]
    have h1 : c (k + 1) * 2 ^ ruzsaT k + 2 ^ ruzsaT k ≤ 2 ^ ruzsaT (k + 1) := by
      calc c (k + 1) * 2 ^ ruzsaT k + 2 ^ ruzsaT k
          = (c (k + 1) + 1) * 2 ^ ruzsaT k := by ring
        _ ≤ 2 ^ ruzsaW (k + 1) * 2 ^ ruzsaT k :=
            Nat.mul_le_mul_right _ (by have := hc (k + 1) (by simp); omega)
        _ = 2 ^ ruzsaT (k + 1) := hpow_eq
    simp only [Nat.add_sub_cancel]
    omega

private lemma ruzsa_packed_sum_inj (c₁ c₂ : ℕ → ℕ) (K : ℕ)
    (hc₁ : ∀ r ∈ Finset.Icc 1 K, c₁ r < 2 ^ ruzsaW r)
    (hc₂ : ∀ r ∈ Finset.Icc 1 K, c₂ r < 2 ^ ruzsaW r)
    (heq : ∑ r ∈ Finset.Icc 1 K, c₁ r * 2 ^ ruzsaT (r - 1) =
           ∑ r ∈ Finset.Icc 1 K, c₂ r * 2 ^ ruzsaT (r - 1)) :
    ∀ r ∈ Finset.Icc 1 K, c₁ r = c₂ r := by
  induction K with
  | zero => intro r hr; simp at hr
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)] at heq
    simp only [Nat.add_sub_cancel] at heq
    have hlow₁ := ruzsa_packed_sum_lt c₁ k fun r hr => hc₁ r (by simp only [Finset.mem_Icc] at hr ⊢; omega)
    have hlow₂ := ruzsa_packed_sum_lt c₂ k fun r hr => hc₂ r (by simp only [Finset.mem_Icc] at hr ⊢; omega)
    have hpos : 0 < 2 ^ ruzsaT k := by positivity
    have htop_eq : c₁ (k + 1) = c₂ (k + 1) := by
      have hdiv := congrArg (· / 2 ^ ruzsaT k) heq
      rw [Nat.add_mul_div_right _ _ hpos, Nat.add_mul_div_right _ _ hpos,
          Nat.div_eq_of_lt hlow₁, Nat.div_eq_of_lt hlow₂, zero_add, zero_add] at hdiv
      exact hdiv
    have hlow_eq : ∑ r ∈ Finset.Icc 1 k, c₁ r * 2 ^ ruzsaT (r - 1) =
        ∑ r ∈ Finset.Icc 1 k, c₂ r * 2 ^ ruzsaT (r - 1) := by
      rw [htop_eq] at heq; omega
    have hprev := ih (fun r hr => hc₁ r (by simp only [Finset.mem_Icc] at hr ⊢; omega))
      (fun r hr => hc₂ r (by simp only [Finset.mem_Icc] at hr ⊢; omega)) hlow_eq
    intro r hr
    simp only [Finset.mem_Icc] at hr
    by_cases hlast : r = k + 1
    · rwa [hlast]
    · exact hprev r (by simp only [Finset.mem_Icc]; omega)

private lemma ruzsa_slot_inj {L v₁ v₂ β₁ β₂ e₁ e₂ : ℕ}
    (hv₁ : v₁ < 2 ^ (L + 1)) (hv₂ : v₂ < 2 ^ (L + 1))
    (hβ₁ : β₁ < 4) (hβ₂ : β₂ < 4)
    (heq : v₁ + 2 ^ (L + 1) * β₁ + 2 ^ (L + 3) * e₁ =
           v₂ + 2 ^ (L + 1) * β₂ + 2 ^ (L + 3) * e₂) :
    v₁ = v₂ ∧ β₁ = β₂ ∧ e₁ = e₂ := by
  have hpos1 : 0 < 2 ^ (L + 1) := by positivity
  have hpow3 : 2 ^ (L + 3) = 2 ^ (L + 1) * 4 := by
    rw [show L + 3 = (L + 1) + 2 by omega, pow_add]; norm_num
  rw [hpow3] at heq
  have heq' : v₁ + 2 ^ (L + 1) * (β₁ + 4 * e₁) = v₂ + 2 ^ (L + 1) * (β₂ + 4 * e₂) := by
    linarith
  have hv : v₁ = v₂ := by
    have hmod := congrArg (· % 2 ^ (L + 1)) heq'
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hv₁, Nat.mod_eq_of_lt hv₂] at hmod
    exact hmod
  have hq : β₁ + 4 * e₁ = β₂ + 4 * e₂ := by
    have hdiv := congrArg (· / 2 ^ (L + 1)) heq'
    rw [Nat.add_mul_div_left _ _ hpos1, Nat.add_mul_div_left _ _ hpos1,
        Nat.div_eq_of_lt hv₁, Nat.div_eq_of_lt hv₂, zero_add, zero_add] at hdiv
    exact hdiv
  refine ⟨hv, ?_, ?_⟩ <;> omega

-- Binary digits of a natural number m < 2^k
private def binBit (m r : ℕ) : ℕ := (m / 2 ^ (r - 1)) % 2

private lemma binBit_lt_two (m r : ℕ) : binBit m r < 2 := Nat.mod_lt _ (by omega)

private lemma sum_binBit_eq (m k : ℕ) (hm : m < 2 ^ k) :
    ∑ r ∈ Finset.Icc 1 k, binBit m r * 2 ^ (r - 1) = m := by
  induction k generalizing m with
  | zero => simp at hm ⊢; omega
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1)]
    simp only [Nat.add_sub_cancel, binBit]
    have hlow : m % 2 ^ j < 2 ^ j := Nat.mod_lt _ (by positivity)
    have hih := ih (m % 2 ^ j) hlow
    have hcongr : ∑ r ∈ Finset.Icc 1 j, (m / 2 ^ (r - 1)) % 2 * 2 ^ (r - 1) =
        ∑ r ∈ Finset.Icc 1 j, ((m % 2 ^ j) / 2 ^ (r - 1)) % 2 * 2 ^ (r - 1) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      simp only [Finset.mem_Icc] at hr
      congr 1
      have hdvd : 2 ^ r ∣ 2 ^ j := Nat.pow_dvd_pow 2 hr.2
      have h1 : m % 2 ^ j = m % 2 ^ r + 2 ^ r * ((m % 2 ^ j) / 2 ^ r) := by
        have := Nat.mod_add_div (m % 2 ^ j) (2 ^ r)
        rw [Nat.mod_mod_of_dvd _ hdvd] at this
        exact this.symm
      have h2 : m = m % 2 ^ r + 2 ^ r * (m / 2 ^ r) := (Nat.mod_add_div m (2 ^ r)).symm
      have hpowr : 2 ^ r = 2 ^ (r - 1) * 2 := by
        conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ]
      have hpos : 0 < 2 ^ (r - 1) := by positivity
      have hdiv1 : m / 2 ^ (r - 1) = (m % 2 ^ r) / 2 ^ (r - 1) + 2 * (m / 2 ^ r) := by
        calc m / 2 ^ (r - 1)
            = (m % 2 ^ r + 2 ^ (r - 1) * (2 * (m / 2 ^ r))) / 2 ^ (r - 1) := by
              rw [← mul_assoc, ← hpowr, ← h2]
          _ = (m % 2 ^ r) / 2 ^ (r - 1) + 2 * (m / 2 ^ r) := Nat.add_mul_div_left _ _ hpos
      have hdiv2 : (m % 2 ^ j) / 2 ^ (r - 1) =
          (m % 2 ^ r) / 2 ^ (r - 1) + 2 * ((m % 2 ^ j) / 2 ^ r) := by
        calc (m % 2 ^ j) / 2 ^ (r - 1)
            = (m % 2 ^ r + 2 ^ (r - 1) * (2 * ((m % 2 ^ j) / 2 ^ r))) / 2 ^ (r - 1) := by
              rw [← mul_assoc, ← hpowr, ← h1]
          _ = (m % 2 ^ r) / 2 ^ (r - 1) + 2 * ((m % 2 ^ j) / 2 ^ r) := Nat.add_mul_div_left _ _ hpos
      rw [hdiv1, hdiv2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
    simp only [binBit] at hih
    rw [hcongr, hih]
    have hq_lt : m / 2 ^ j < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      simpa [pow_succ'] using hm
    rw [Nat.mod_eq_of_lt hq_lt, mul_comm, Nat.mod_add_div]

-- Fractional chunks and exact telescoping identity
private noncomputable def fracChunk (x : ℝ) (r : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ ruzsaL r * Int.fract ((2 : ℝ) ^ ruzsaS (r - 1) * x)⌋₊

private lemma fracChunk_lt (x : ℝ) (r : ℕ) : fracChunk x r < 2 ^ ruzsaL r := by
  dsimp only [fracChunk]
  rw [Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg _))]
  have hlt := Int.fract_lt_one ((2 : ℝ) ^ ruzsaS (r - 1) * x)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ruzsaL r := by positivity
  calc (2 : ℝ) ^ ruzsaL r * Int.fract ((2 : ℝ) ^ ruzsaS (r - 1) * x)
      < (2 : ℝ) ^ ruzsaL r * 1 := mul_lt_mul_of_pos_left hlt hpos
    _ = ((2 ^ ruzsaL r : ℕ) : ℝ) := by push_cast; ring

private lemma telescoping_fract (x : ℝ) (a b : ℕ) (hab : a ≤ b) :
    Int.fract ((2 : ℝ) ^ ruzsaS a * x) =
      (∑ r ∈ Finset.Icc (a + 1) b,
        (fracChunk x r : ℝ) / (2 : ℝ) ^ (ruzsaS r - ruzsaS a)) +
      Int.fract ((2 : ℝ) ^ ruzsaS b * x) / (2 : ℝ) ^ (ruzsaS b - ruzsaS a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Icc_succ_top (by omega : a + 1 ≤ m + 1)]
    have hSm_ge : ruzsaS a ≤ ruzsaS m := Nat.pow_le_pow_left hm 2
    have hSsucc : ruzsaS (m + 1) - ruzsaS a = (ruzsaS m - ruzsaS a) + ruzsaL (m + 1) := by
      rw [ruzsaS_succ]; omega
    have hstep : Int.fract ((2 : ℝ) ^ ruzsaS m * x) / (2 : ℝ) ^ (ruzsaS m - ruzsaS a) =
        (fracChunk x (m + 1) : ℝ) / (2 : ℝ) ^ (ruzsaS (m + 1) - ruzsaS a) +
        Int.fract ((2 : ℝ) ^ ruzsaS (m + 1) * x) / (2 : ℝ) ^ (ruzsaS (m + 1) - ruzsaS a) := by
      set y : ℝ := (2 : ℝ) ^ ruzsaL (m + 1) * Int.fract ((2 : ℝ) ^ ruzsaS m * x)
      have hy_nn : 0 ≤ y := mul_nonneg (by positivity) (Int.fract_nonneg _)
      have hfloor : (fracChunk x (m + 1) : ℝ) + Int.fract y = y := by
        have hdef : fracChunk x (m + 1) = ⌊y⌋₊ := by
          simp only [fracChunk, Nat.add_sub_cancel, y]
        have hfl : (⌊y⌋₊ : ℤ) = ⌊y⌋ :=
          (Int.floor_eq_iff.mpr ⟨by exact_mod_cast Nat.floor_le hy_nn,
            by exact_mod_cast Nat.lt_floor_add_one y⟩).symm
        have hflR : ((⌊y⌋₊ : ℕ) : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast hfl
        have hff := Int.fract_add_floor y
        rw [hdef, hflR]
        linarith
      have hfract_y : Int.fract y = Int.fract ((2 : ℝ) ^ ruzsaS (m + 1) * x) := by
        dsimp only [y]
        conv_lhs => arg 1; arg 2; rw [Int.fract]
        rw [mul_sub]
        have hpow : (2 : ℝ) ^ ruzsaL (m + 1) * ((2 : ℝ) ^ ruzsaS m * x) =
            (2 : ℝ) ^ ruzsaS (m + 1) * x := by
          rw [← mul_assoc, ← pow_add, add_comm, ← ruzsaS_succ]
        rw [hpow]
        have hint : (2 : ℝ) ^ ruzsaL (m + 1) * (⌊(2 : ℝ) ^ ruzsaS m * x⌋ : ℝ) =
            (((2 ^ ruzsaL (m + 1) : ℕ) * ⌊(2 : ℝ) ^ ruzsaS m * x⌋ : ℤ) : ℝ) := by
          push_cast; ring
        rw [hint, Int.fract_sub_intCast]
      have hpow_den : (2 : ℝ) ^ (ruzsaS (m + 1) - ruzsaS a) =
          (2 : ℝ) ^ (ruzsaS m - ruzsaS a) * (2 : ℝ) ^ ruzsaL (m + 1) := by
        rw [hSsucc, pow_add]
      rw [← hfract_y, ← add_div, hfloor, hpow_den]
      dsimp only [y]
      have hne : (2 : ℝ) ^ ruzsaL (m + 1) ≠ 0 := by positivity
      field_simp
    rw [ih, add_assoc, hstep]

-- Lebesgue measure bound on {α ∈ [1, 2] | ∃ m : ℤ, |L * α - m| < δ}
private lemma volume_near_int_le {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ_half : δ ≤ 1 / 2) :
    volume {α : ℝ | α ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ m : ℤ, |L * α - (m : ℝ)| < δ} ≤
      ENNReal.ofReal (2 * δ * (1 + 5 / L)) := by
  let lo : ℤ := ⌊L⌋ - 1
  let hi : ℤ := ⌊2 * L⌋ + 2
  have hsub : {α : ℝ | α ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ m : ℤ, |L * α - (m : ℝ)| < δ} ⊆
      ⋃ m ∈ (Finset.Icc lo hi), Set.Ioo (((m : ℝ) - δ) / L) (((m : ℝ) + δ) / L) := by
    intro α ⟨⟨hα1, hα2⟩, m, hm⟩
    rw [abs_lt] at hm
    simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_Ioo]
    refine ⟨m, ⟨?_, ?_⟩, ?_, ?_⟩
    · have h1 : (lo : ℝ) < (m : ℝ) := by
        dsimp only [lo]; push_cast
        have := Int.floor_le L
        nlinarith
      exact Int.le_of_lt (by exact_mod_cast h1)
    · have h2 : (m : ℝ) < (hi : ℝ) := by
        dsimp only [hi]; push_cast
        have := Int.lt_floor_add_one (2 * L)
        nlinarith
      exact Int.le_of_lt (by exact_mod_cast h2)
    · rw [div_lt_iff₀ hL]; linarith
    · rw [lt_div_iff₀ hL]; linarith
  have hcard_le : ((Finset.Icc lo hi).card : ℝ) ≤ L + 5 := by
    rw [Int.card_Icc]
    have hnonneg : 0 ≤ hi + 1 - lo := by
      dsimp only [lo, hi]
      have : ⌊L⌋ ≤ ⌊2 * L⌋ := Int.floor_mono (by linarith)
      omega
    have hcast : ((Int.toNat (hi + 1 - lo) : ℕ) : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast]
    dsimp only [lo, hi]; push_cast
    have h1 := Int.floor_le (2 * L)
    have h2 := Int.lt_floor_add_one L
    linarith
  calc volume {α : ℝ | α ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ m : ℤ, |L * α - (m : ℝ)| < δ}
      ≤ volume (⋃ m ∈ (Finset.Icc lo hi), Set.Ioo (((m : ℝ) - δ) / L) (((m : ℝ) + δ) / L)) :=
        measure_mono hsub
    _ ≤ ∑ m ∈ Finset.Icc lo hi, volume (Set.Ioo (((m : ℝ) - δ) / L) (((m : ℝ) + δ) / L)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _m ∈ Finset.Icc lo hi, ENNReal.ofReal (2 * δ / L) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Real.volume_Ioo]
        congr 1; ring
    _ = ((Finset.Icc lo hi).card : ℝ≥0∞) * ENNReal.ofReal (2 * δ / L) := by simp
    _ = ENNReal.ofReal (((Finset.Icc lo hi).card : ℝ) * (2 * δ / L)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((L + 5) * (2 * δ / L)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard_le (by positivity))
    _ = ENNReal.ofReal (2 * δ * (1 + 5 / L)) := by
        congr 1; field_simp

-- Prime shell parameters: θ_k = √2 - 1 - 1/√k, P_k = ⌊2^(θ_k * k^2)⌋₊, 𝒫_k = primes in (P_{k-1}, P_k]
private noncomputable def ruzsaTheta (k : ℕ) : ℝ :=
  Real.sqrt 2 - 1 - 1 / Real.sqrt (k : ℝ)

private noncomputable def ruzsaP (k : ℕ) : ℕ :=
  ⌊(2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)⌋₊

private noncomputable def ruzsaPrimes (k : ℕ) : Finset ℕ :=
  (Finset.Ioc (ruzsaP (k - 1)) (ruzsaP k)).filter Nat.Prime

private lemma ruzsaTheta_bounds {k : ℕ} (hk : 25 ≤ k) :
    (1 / 5 : ℝ) < ruzsaTheta k ∧ ruzsaTheta k < Real.sqrt 2 - 1 := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsk_ge : (5 : ℝ) ≤ Real.sqrt (k : ℝ) := by
    calc (5 : ℝ) = Real.sqrt (5 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hinv_le : 1 / Real.sqrt (k : ℝ) ≤ 1 / 5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsk_ge
  have hsqrt2_gt : (1.41 : ℝ) < Real.sqrt 2 := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.41 ^ 2) (by norm_num : (1.41 : ℝ) ^ 2 < 2)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hinv_pos : 0 < 1 / Real.sqrt (k : ℝ) := by positivity
  dsimp only [ruzsaTheta]
  constructor <;> linarith

private lemma ruzsaTheta_mono {k₁ k₂ : ℕ} (h1 : 1 ≤ k₁) (hle : k₁ ≤ k₂) :
    ruzsaTheta k₁ ≤ ruzsaTheta k₂ := by
  dsimp only [ruzsaTheta]
  have h1_pos : (0 : ℝ) < Real.sqrt (k₁ : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr h1)
  have hsle : Real.sqrt (k₁ : ℝ) ≤ Real.sqrt (k₂ : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hle)
  have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) h1_pos hsle
  linarith

private lemma ruzsaPrimes_card_lower :
    ∃ K₁ : ℕ, 100 ≤ K₁ ∧ ∀ k : ℕ, K₁ ≤ k →
      ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (8 * (k : ℝ) ^ 2) ≤ ((ruzsaPrimes k).card : ℝ) := by
  obtain ⟨C, hC_pos, hPNT⟩ := RHDirect.Stage8ExplicitPrimeBounds.effective_pnt_pi_two_term
  -- For x large enough (log x ≥ max 4 (4 * C)), (1/2) x / log x ≤ π(x) ≤ 2 x / log x
  have hpi_bounds : ∃ X₀ : ℝ, 16 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x →
      x / (2 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) ∧
      (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * x / Real.log x := by
    let L₀ : ℝ := max 4 (4 * C)
    refine ⟨max 16 (Real.exp L₀), le_max_left _ _, fun x hx => ?_⟩
    have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
    have hx4 : 4 ≤ x := by linarith
    have hlog_ge : L₀ ≤ Real.log x := by
      calc L₀ = Real.log (Real.exp L₀) := (Real.log_exp L₀).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hx)
    have hlog4 : 4 ≤ Real.log x := (le_max_left _ _).trans hlog_ge
    have hlogC : 4 * C ≤ Real.log x := (le_max_right _ _).trans hlog_ge
    have hlog_pos : 0 < Real.log x := by linarith
    have herr := abs_le.mp (hPNT x hx4)
    have hx_pos : 0 < x := by linarith
    have hterm2 : x / (Real.log x) ^ 2 ≤ x / (4 * Real.log x) := by
      rw [div_le_div_iff₀ (pow_pos hlog_pos 2) (by positivity)]
      have hsq : 4 * Real.log x ≤ (Real.log x) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hlog4 hlog_pos.le
      exact mul_le_mul_of_nonneg_left hsq hx_pos.le
    have hterm3 : C * x / (Real.log x) ^ 3 ≤ x / (4 * Real.log x) := by
      rw [div_le_div_iff₀ (pow_pos hlog_pos 3) (by positivity)]
      have h1 : 4 * C * Real.log x ≤ (Real.log x) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hlogC hlog_pos.le
      have h2 : (Real.log x) ^ 2 ≤ (Real.log x) ^ 3 := by
        have h1le : (1 : ℝ) ≤ Real.log x := by linarith
        nlinarith [sq_nonneg (Real.log x)]
      have h3 : 4 * C * Real.log x ≤ (Real.log x) ^ 3 := h1.trans h2
      have h4 : x * (4 * C * Real.log x) ≤ x * (Real.log x) ^ 3 :=
        mul_le_mul_of_nonneg_left h3 hx_pos.le
      linarith
    have hq4 : x / (4 * Real.log x) = (1 / 4) * (x / Real.log x) := by ring
    have hq2 : x / (2 * Real.log x) = (1 / 2) * (x / Real.log x) := by ring
    have hq2' : 2 * x / Real.log x = 2 * (x / Real.log x) := by ring
    have hxlog_nn : 0 ≤ x / Real.log x := div_nonneg hx_pos.le hlog_pos.le
    constructor
    · have : x / Real.log x + x / (Real.log x) ^ 2 - C * x / (Real.log x) ^ 3 ≤
          (Nat.primeCounting ⌊x⌋₊ : ℝ) := by linarith [herr.1]
      have hpos2 : 0 ≤ x / (Real.log x) ^ 2 := by positivity
      linarith
    · have : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
          x / Real.log x + x / (Real.log x) ^ 2 + C * x / (Real.log x) ^ 3 := by linarith [herr.2]
      linarith
  obtain ⟨X₀, hX₀_16, hX₀⟩ := hpi_bounds
  -- Choose K₁ ≥ 100 so that for all k ≥ K₁: 2^(θ_{k-1} (k-1)^2) ≥ X₀ and 2^(0.2*(2k-1)) ≥ 16
  have hexK : ∃ K₁ : ℕ, 100 ≤ K₁ ∧ X₀ ≤ (2 : ℝ) ^ ((1 / 5 : ℝ) * ((K₁ - 1 : ℕ) : ℝ) ^ 2) := by
    have htend : Tendsto (fun k : ℕ => (2 : ℝ) ^ ((1 / 5 : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2)) atTop atTop := by
      have h1 : Tendsto (fun k : ℕ => (1 / 5 : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro b
        refine ⟨Nat.ceil (5 * max b 0) + 2, fun k hk => ?_⟩
        have hkm1 : (Nat.ceil (5 * max b 0) + 1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show Nat.ceil (5 * max b 0) + 1 ≤ k - 1 by omega)
        have hge1 : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) (Nat.ceil (5 * max b 0))]
        have hsq : ((k - 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ 2 := by
          calc ((k - 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) * 1 := (mul_one _).symm
            _ ≤ ((k - 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hge1 (by linarith)
            _ = ((k - 1 : ℕ) : ℝ) ^ 2 := (sq _).symm
        have hceil : 5 * max b 0 ≤ (Nat.ceil (5 * max b 0) : ℝ) := Nat.le_ceil _
        linarith [le_max_left b 0]
      exact (tendsto_rpow_atTop_of_base_gt_one (2 : ℝ) (by norm_num : (1 : ℝ) < 2)).comp h1
    obtain ⟨K₁, h1, h2⟩ := ((htend.eventually (eventually_ge_atTop X₀)).and (eventually_ge_atTop 100)).exists
    exact ⟨K₁, h2, h1⟩
  obtain ⟨K₁, hK₁_100, hK₁_X₀⟩ := hexK
  refine ⟨K₁, hK₁_100, fun k hk => ?_⟩
  set x₂ : ℝ := (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)
  set x₁ : ℝ := (2 : ℝ) ^ (ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2)
  have hθ1 := ruzsaTheta_bounds (k := k - 1) (by omega)
  have hθ2 := ruzsaTheta_bounds (k := k) (by omega)
  have hθ_mono := ruzsaTheta_mono (k₁ := k - 1) (k₂ := k) (by omega) (by omega)
  have hx1_ge_X0 : X₀ ≤ x₁ := by
    have hexp_ge : (1 / 5 : ℝ) * ((K₁ - 1 : ℕ) : ℝ) ^ 2 ≤ ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2 := by
      have hle : ((K₁ - 1 : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show K₁ - 1 ≤ k - 1 by omega)
      have hsq : ((K₁ - 1 : ℕ) : ℝ) ^ 2 ≤ ((k - 1 : ℕ) : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
      exact mul_le_mul hθ1.1.le hsq (sq_nonneg _) (by linarith [hθ1.1])
    exact hK₁_X₀.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_ge)
  -- Show x₂ ≥ 16 * x₁ because exponent jumps by ≥ (1/5) * (2k - 1) ≥ 39 > 4
  have hx_ratio : 16 * x₁ ≤ x₂ := by
    have hdiff : (4 : ℝ) ≤ ruzsaTheta k * (k : ℝ) ^ 2 - ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2 := by
      have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
      have hk100 : (100 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 100 ≤ k by omega)
      rw [hkm1]
      have h1 : ruzsaTheta (k - 1) * ((k : ℝ) - 1) ^ 2 ≤ ruzsaTheta k * ((k : ℝ) - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hθ_mono (sq_nonneg _)
      have h2 : ruzsaTheta k * (2 * (k : ℝ) - 1) ≥ (1 / 5 : ℝ) * (2 * (k : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hθ2.1.le (by linarith)
      have h3 : ruzsaTheta k * (k : ℝ) ^ 2 - ruzsaTheta k * ((k : ℝ) - 1) ^ 2 =
          ruzsaTheta k * (2 * (k : ℝ) - 1) := by ring
      linarith
    have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    calc 16 * x₁ = (2 : ℝ) ^ (4 : ℝ) * (2 : ℝ) ^ (ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2) := by rw [h16]
      _ = (2 : ℝ) ^ (4 + ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2) := (Real.rpow_add (by norm_num) _ _).symm
      _ ≤ (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hx1_pos : 0 < x₁ := Real.rpow_pos_of_pos (by norm_num) _
  have hx2_pos : 0 < x₂ := Real.rpow_pos_of_pos (by norm_num) _
  have hx2_ge_X0 : X₀ ≤ x₂ := by linarith
  have hpi1 := (hX₀ x₁ hx1_ge_X0).2
  have hpi2 := (hX₀ x₂ hx2_ge_X0).1
  have hP1_le_P2 : ruzsaP (k - 1) ≤ ruzsaP k := Nat.floor_mono (by linarith)
  -- Connect (ruzsaPrimes k).card with primeCounting (P k) - primeCounting (P (k-1))
  have hcard_eq : (ruzsaPrimes k).card = Nat.primeCounting (ruzsaP k) - Nat.primeCounting (ruzsaP (k - 1)) := by
    have hpc : ∀ n : ℕ, Nat.primeCounting n = ((Finset.Icc 1 n).filter Nat.Prime).card := by
      intro n
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      congr 1; ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      constructor
      · rintro ⟨hm, hp⟩; exact ⟨⟨hp.one_lt.le, by omega⟩, hp⟩
      · rintro ⟨⟨_, hm⟩, hp⟩; exact ⟨by omega, hp⟩
    rw [hpc, hpc]
    have hsub : (Finset.Icc 1 (ruzsaP (k - 1))).filter Nat.Prime ⊆ (Finset.Icc 1 (ruzsaP k)).filter Nat.Prime := by
      intro m hm; simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      exact ⟨⟨hm.1.1, hm.1.2.trans hP1_le_P2⟩, hm.2⟩
    have hsdiff : ruzsaPrimes k = ((Finset.Icc 1 (ruzsaP k)).filter Nat.Prime) \
        ((Finset.Icc 1 (ruzsaP (k - 1))).filter Nat.Prime) := by
      ext m; simp only [ruzsaPrimes, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨⟨hp.one_lt.le, h2⟩, hp⟩, fun ⟨⟨_, hle⟩, _⟩ => by omega⟩
      · rintro ⟨⟨⟨_, h2⟩, hp⟩, hnot⟩
        refine ⟨⟨?_, h2⟩, hp⟩
        by_contra hle; push Not at hle
        exact hnot ⟨⟨hp.one_lt.le, hle⟩, hp⟩
    rw [hsdiff, Finset.card_sdiff_of_subset hsub]
  -- Now compare x₂ / (2 log x₂) - 2 x₁ / log x₁ ≥ x₂ / (4 log x₂) ≥ x₂ / (8 k^2)
  have hlog1_pos : 0 < Real.log x₁ := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log x₂ := Real.log_pos (by linarith)
  have hlog_ratio : Real.log x₂ ≤ 2 * Real.log x₁ := by
    have hlog2_eq : Real.log x₂ = (ruzsaTheta k * (k : ℝ) ^ 2) * Real.log 2 := by
      dsimp only [x₂]; rw [Real.log_rpow (by norm_num)]
    have hlog1_eq : Real.log x₁ = (ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2) * Real.log 2 := by
      dsimp only [x₁]; rw [Real.log_rpow (by norm_num)]
    rw [hlog2_eq, hlog1_eq]
    have hlog2_p : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hk100 : (100 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 100 ≤ k by omega)
    have h1 : ruzsaTheta k * (k : ℝ) ^ 2 ≤ 2 * (ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2) := by
      rw [hkm1]
      have hsk1 : (9 : ℝ) ≤ Real.sqrt ((k - 1 : ℕ) : ℝ) := by
        calc (9 : ℝ) = Real.sqrt (9 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
          _ ≤ Real.sqrt ((k - 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast (show 81 ≤ k - 1 by omega))
      have hinv1 : 1 / Real.sqrt ((k - 1 : ℕ) : ℝ) ≤ 1 / 9 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsk1
      have hsqrt2_gt : (1.4 : ℝ) < Real.sqrt 2 := by
        have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.4 ^ 2) (by norm_num : (1.4 : ℝ) ^ 2 < 2)
        rwa [Real.sqrt_sq (by norm_num)] at this
      have hth1_gt2 : (0.28 : ℝ) < ruzsaTheta (k - 1) := by dsimp only [ruzsaTheta]; linarith
      have hth2_lt2 : ruzsaTheta k < 0.42 := by
        have hsqrt2_lt2 : Real.sqrt 2 < 1.42 := by
          have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.42 ^ 2)
          rwa [Real.sqrt_sq (by norm_num)] at this
        linarith [hθ2.2]
      have hk_sq_le : 0.42 * (k : ℝ) ^ 2 ≤ 2 * (0.28 * ((k : ℝ) - 1) ^ 2) := by
        have hsub : 0.56 * ((k : ℝ) - 1) ^ 2 - 0.42 * (k : ℝ) ^ 2 =
            0.14 * (k : ℝ) * ((k : ℝ) - 8) + 0.56 := by ring
        have hpos_m : 0 ≤ 0.14 * (k : ℝ) * ((k : ℝ) - 8) := by
          have h1' : (0 : ℝ) ≤ 0.14 * (k : ℝ) := by linarith
          have h2' : (0 : ℝ) ≤ (k : ℝ) - 8 := by linarith
          exact mul_nonneg h1' h2'
        linarith
      calc ruzsaTheta k * (k : ℝ) ^ 2
          ≤ 0.42 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hth2_lt2.le (sq_nonneg _)
        _ ≤ 2 * (0.28 * ((k : ℝ) - 1) ^ 2) := hk_sq_le
        _ ≤ 2 * (ruzsaTheta (k - 1) * ((k : ℝ) - 1) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hth1_gt2.le (sq_nonneg _)) (by norm_num)
    calc (ruzsaTheta k * (k : ℝ) ^ 2) * Real.log 2
        ≤ (2 * (ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2)) * Real.log 2 :=
          mul_le_mul_of_nonneg_right h1 hlog2_p.le
      _ = 2 * ((ruzsaTheta (k - 1) * ((k - 1 : ℕ) : ℝ) ^ 2) * Real.log 2) := by ring
  have hpi1_le : (Nat.primeCounting (ruzsaP (k - 1)) : ℝ) ≤ x₂ / (4 * Real.log x₂) := by
    have h1 : 2 * x₁ / Real.log x₁ ≤ x₂ / (4 * Real.log x₂) := by
      rw [div_le_div_iff₀ hlog1_pos (by positivity)]
      calc 2 * x₁ * (4 * Real.log x₂)
          ≤ 2 * x₁ * (4 * (2 * Real.log x₁)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog_ratio (by norm_num)) (by positivity)
        _ = (16 * x₁) * Real.log x₁ := by ring
        _ ≤ x₂ * Real.log x₁ := mul_le_mul_of_nonneg_right hx_ratio hlog1_pos.le
    exact hpi1.trans h1
  have hdiff_ge : x₂ / (4 * Real.log x₂) ≤ ((ruzsaPrimes k).card : ℝ) := by
    have hmono : Nat.primeCounting (ruzsaP (k - 1)) ≤ Nat.primeCounting (ruzsaP k) :=
      Nat.monotone_primeCounting hP1_le_P2
    have hpi2' : x₂ / (2 * Real.log x₂) ≤ (Nat.primeCounting (ruzsaP k) : ℝ) := hpi2
    have h24 : x₂ / (2 * Real.log x₂) = 2 * (x₂ / (4 * Real.log x₂)) := by ring
    rw [hcard_eq, Nat.cast_sub hmono]
    linarith
  have hlog2_le_2k2 : Real.log x₂ ≤ 2 * (k : ℝ) ^ 2 := by
    dsimp only [x₂]; rw [Real.log_rpow (by norm_num)]
    have hlog2_lt : Real.log 2 < 1 := Real.log_lt_iff_lt_exp (by norm_num) |>.mpr (by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith)
    have hsqrt2_lt : Real.sqrt 2 < 1.5 := by
      have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.5 ^ 2)
      rwa [Real.sqrt_sq (by norm_num)] at this
    have hth2_lt : ruzsaTheta k < 1 := by linarith [hθ2.2]
    calc (ruzsaTheta k * (k : ℝ) ^ 2) * Real.log 2
        ≤ (1 * (k : ℝ) ^ 2) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hth2_lt.le (sq_nonneg _)) hlog2_lt.le
            (Real.log_pos (by norm_num)).le (by positivity)
      _ ≤ 2 * (k : ℝ) ^ 2 := by linarith [sq_nonneg (k : ℝ)]
  have hstep_div : x₂ / (8 * (k : ℝ) ^ 2) ≤ x₂ / (4 * Real.log x₂) :=
    div_le_div_of_nonneg_left hx2_pos.le (by positivity) (by linarith)
  exact hstep_div.trans hdiff_ge

-- Ruzsa encoding of prime p at level k with scaling parameter α ∈ [1, 2]
private noncomputable def ruzsaSlot (α : ℝ) (k p r : ℕ) : ℕ :=
  if r ≤ k then
    fracChunk (α * Real.logb 2 (p : ℝ)) r +
      2 ^ (ruzsaL r + 1) * binBit ⌊α * Real.logb 2 (p : ℝ)⌋₊ r +
      2 ^ (ruzsaL r + 3) * (if r = k then 1 else 0)
  else 0

private noncomputable def ruzsaCode (α : ℝ) (k p : ℕ) : ℕ :=
  ∑ r ∈ Finset.Icc 1 k, ruzsaSlot α k p r * 2 ^ ruzsaT (r - 1)

private lemma ruzsaSlot_lt_half_W (α : ℝ) (k p r : ℕ) :
    ruzsaSlot α k p r < 2 ^ (ruzsaL r + 5) := by
  dsimp only [ruzsaSlot]
  by_cases h : r ≤ k
  · rw [if_pos h]
    have hv := fracChunk_lt (α * Real.logb 2 (p : ℝ)) r
    have hb := binBit_lt_two ⌊α * Real.logb 2 (p : ℝ)⌋₊ r
    have h1 : 2 ^ ruzsaL r + 2 ^ (ruzsaL r + 1) * 1 + 2 ^ (ruzsaL r + 3) * 1 < 2 ^ (ruzsaL r + 5) := by
      have hpow1 : 2 ^ (ruzsaL r + 1) = 2 * 2 ^ ruzsaL r := by rw [pow_succ]; ring
      have hpow3 : 2 ^ (ruzsaL r + 3) = 8 * 2 ^ ruzsaL r := by
        rw [show ruzsaL r + 3 = ruzsaL r + 3 by rfl, pow_add]; ring
      have hpow5 : 2 ^ (ruzsaL r + 5) = 32 * 2 ^ ruzsaL r := by rw [pow_add]; ring
      have hpos : 0 < 2 ^ ruzsaL r := by positivity
      omega
    have he : (if r = k then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hb1 : binBit ⌊α * Real.logb 2 (p : ℝ)⌋₊ r ≤ 1 := by omega
    have hmul1 : 2 ^ (ruzsaL r + 1) * binBit ⌊α * Real.logb 2 (p : ℝ)⌋₊ r ≤ 2 ^ (ruzsaL r + 1) * 1 :=
      Nat.mul_le_mul_left _ hb1
    have hmul2 : 2 ^ (ruzsaL r + 3) * (if r = k then 1 else 0) ≤ 2 ^ (ruzsaL r + 3) * 1 :=
      Nat.mul_le_mul_left _ he
    omega
  · rw [if_neg h]
    exact Nat.two_pow_pos _

private lemma ruzsaCode_pos_and_lt (α : ℝ) (k p : ℕ) (hk : 1 ≤ k) :
    1 ≤ ruzsaCode α k p ∧ ruzsaCode α k p < 2 ^ ruzsaT k := by
  constructor
  · have hmem : k ∈ Finset.Icc 1 k := by simp [hk]
    have hterm : 1 ≤ ruzsaSlot α k p k * 2 ^ ruzsaT (k - 1) := by
      have hs : 1 ≤ ruzsaSlot α k p k := by
        simp only [ruzsaSlot, le_refl, ↓reduceIte, mul_one]
        have : 1 ≤ 2 ^ (ruzsaL k + 3) := Nat.one_le_two_pow
        omega
      exact Nat.mul_pos hs (by positivity)
    exact hterm.trans (Finset.single_le_sum (f := fun r => ruzsaSlot α k p r * 2 ^ ruzsaT (r - 1))
      (fun _ _ => Nat.zero_le _) hmem)
  · apply ruzsa_packed_sum_lt
    intro r hr
    simp only [Finset.mem_Icc] at hr
    have h1 := ruzsaSlot_lt_half_W α k p r
    have hW : ruzsaL r + 5 < ruzsaW r := by simp only [ruzsaL, ruzsaW]; omega
    exact h1.trans (Nat.pow_lt_pow_right (by omega) hW)

private lemma ruzsaCode_extend (α : ℝ) (k K p : ℕ) (h : k ≤ K) :
    ruzsaCode α k p = ∑ r ∈ Finset.Icc 1 K, ruzsaSlot α k p r * 2 ^ ruzsaT (r - 1) := by
  dsimp only [ruzsaCode]
  refine Finset.sum_subset (fun r hr => by simp only [Finset.mem_Icc] at hr ⊢; omega) ?_
  intro r hr hnot
  simp only [Finset.mem_Icc] at hr hnot
  have hgt : ¬ r ≤ k := by omega
  simp [ruzsaSlot, hgt]

private lemma sq_lt_two_pow (k : ℕ) (hk : 5 ≤ k) : k ^ 2 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h2m : 2 * m + 1 < 2 ^ m := by
      have hm2 : 2 * m + 1 ≤ m ^ 2 := by nlinarith
      omega
    have hsq : (m + 1) ^ 2 = m ^ 2 + (2 * m + 1) := by ring
    rw [hsq, pow_succ 2 m]
    omega

private lemma ruzsa_floor_lt_two_pow {α : ℝ} (hα : α ∈ Set.Icc (1 : ℝ) 2)
    {k p : ℕ} (hk : 25 ≤ k) (hp : p ∈ ruzsaPrimes k) :
    ⌊α * Real.logb 2 (p : ℝ)⌋₊ < 2 ^ k := by
  have hp_mem := Finset.mem_filter.mp hp
  have hp_prime : p.Prime := hp_mem.2
  have hp_le : p ≤ ruzsaP k := (Finset.mem_Ioc.mp hp_mem.1).2
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  have hlog_nn : 0 ≤ Real.logb 2 (p : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hp_prime.one_lt.le)
  have hθ := ruzsaTheta_bounds hk
  have hsqrt2_lt : Real.sqrt 2 < 1.5 := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.5 ^ 2)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hθ_half : ruzsaTheta k < 1 / 2 := by linarith [hθ.2]
  have hp_R : (p : ℝ) ≤ (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2) := by
    calc (p : ℝ) ≤ (ruzsaP k : ℝ) := by exact_mod_cast hp_le
      _ ≤ (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2) := Nat.floor_le (by positivity)
  have hlog_le : Real.logb 2 (p : ℝ) ≤ ruzsaTheta k * (k : ℝ) ^ 2 := by
    calc Real.logb 2 (p : ℝ)
        ≤ Real.logb 2 ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) :=
          Real.logb_le_logb_of_le (by norm_num) hp_pos hp_R
      _ = ruzsaTheta k * (k : ℝ) ^ 2 := Real.logb_rpow (by norm_num) (by norm_num)
  have hα_prod : α * Real.logb 2 (p : ℝ) < (k : ℝ) ^ 2 := by
    have hk_sq_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    calc α * Real.logb 2 (p : ℝ)
        ≤ 2 * (ruzsaTheta k * (k : ℝ) ^ 2) := mul_le_mul hα.2 hlog_le hlog_nn (by norm_num)
      _ < 2 * ((1 / 2) * (k : ℝ) ^ 2) := by
          have : ruzsaTheta k * (k : ℝ) ^ 2 < (1 / 2) * (k : ℝ) ^ 2 :=
            mul_lt_mul_of_pos_right hθ_half hk_sq_pos
          linarith
      _ = (k : ℝ) ^ 2 := by ring
  have hfl_lt : ⌊α * Real.logb 2 (p : ℝ)⌋₊ < k ^ 2 := by
    rw [Nat.floor_lt (mul_nonneg (by linarith [hα.1]) hlog_nn)]
    exact_mod_cast hα_prod
  exact hfl_lt.trans (sq_lt_two_pow k (by omega))

private lemma ruzsaCode_decode {α : ℝ} (hα : α ∈ Set.Icc (1 : ℝ) 2)
    {k₁ k₂ k'₁ k'₂ p₁ p₂ p'₁ p'₂ : ℕ}
    (hk₁ : 25 ≤ k₁) (hk12 : k₁ ≤ k₂) (hk'₁ : 25 ≤ k'₁) (hk'12 : k'₁ ≤ k'₂)
    (hp₁ : p₁ ∈ ruzsaPrimes k₁) (hp₂ : p₂ ∈ ruzsaPrimes k₂)
    (hp'₁ : p'₁ ∈ ruzsaPrimes k'₁) (hp'₂ : p'₂ ∈ ruzsaPrimes k'₂)
    (heq : ruzsaCode α k₁ p₁ + ruzsaCode α k₂ p₂ = ruzsaCode α k'₁ p'₁ + ruzsaCode α k'₂ p'₂) :
    (k₁ = k'₁ ∧ k₂ = k'₂) ∧
    |Real.logb 2 ((p₁ * p₂ : ℕ) : ℝ) - Real.logb 2 ((p'₁ * p'₂ : ℕ) : ℝ)| < 2 / (2 : ℝ) ^ ruzsaS k₁ ∧
    (k₁ < k₂ → ∃ m : ℤ,
      |(2 : ℝ) ^ ruzsaS k₁ * (α * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ))) - (m : ℝ)| <
        1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) := by
  let K := max k₂ k'₂
  rw [ruzsaCode_extend α k₁ K p₁ (hk12.trans (le_max_left _ _)),
      ruzsaCode_extend α k₂ K p₂ (le_max_left _ _),
      ruzsaCode_extend α k'₁ K p'₁ (hk'12.trans (le_max_right _ _)),
      ruzsaCode_extend α k'₂ K p'₂ (le_max_right _ _)] at heq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib] at heq
  have hsum_eq : ∑ r ∈ Finset.Icc 1 K, (ruzsaSlot α k₁ p₁ r + ruzsaSlot α k₂ p₂ r) * 2 ^ ruzsaT (r - 1) =
      ∑ r ∈ Finset.Icc 1 K, (ruzsaSlot α k'₁ p'₁ r + ruzsaSlot α k'₂ p'₂ r) * 2 ^ ruzsaT (r - 1) := by
    convert heq using 2 with r _ <;> ring
  have hslot_eq : ∀ r ∈ Finset.Icc 1 K,
      ruzsaSlot α k₁ p₁ r + ruzsaSlot α k₂ p₂ r = ruzsaSlot α k'₁ p'₁ r + ruzsaSlot α k'₂ p'₂ r := by
    apply ruzsa_packed_sum_inj _ _ K
    · intro r hr; simp only [Finset.mem_Icc] at hr
      have h1 := ruzsaSlot_lt_half_W α k₁ p₁ r; have h2 := ruzsaSlot_lt_half_W α k₂ p₂ r
      have hW : ruzsaW r = (ruzsaL r + 5) + 1 := by simp only [ruzsaL, ruzsaW]; omega
      rw [hW, pow_succ]; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr
      have h1 := ruzsaSlot_lt_half_W α k'₁ p'₁ r; have h2 := ruzsaSlot_lt_half_W α k'₂ p'₂ r
      have hW : ruzsaW r = (ruzsaL r + 5) + 1 := by simp only [ruzsaL, ruzsaW]; omega
      rw [hW, pow_succ]; omega
    · exact hsum_eq
  -- Unpack v, β, e fields at every r ∈ [1, K]
  let x₁ : ℝ := α * Real.logb 2 (p₁ : ℝ)
  let x₂ : ℝ := α * Real.logb 2 (p₂ : ℝ)
  let y₁ : ℝ := α * Real.logb 2 (p'₁ : ℝ)
  let y₂ : ℝ := α * Real.logb 2 (p'₂ : ℝ)
  have hfields : ∀ r ∈ Finset.Icc 1 K,
      ((if r ≤ k₁ then fracChunk x₁ r else 0) + (if r ≤ k₂ then fracChunk x₂ r else 0) =
       (if r ≤ k'₁ then fracChunk y₁ r else 0) + (if r ≤ k'₂ then fracChunk y₂ r else 0)) ∧
      ((if r ≤ k₁ then binBit ⌊x₁⌋₊ r else 0) + (if r ≤ k₂ then binBit ⌊x₂⌋₊ r else 0) =
       (if r ≤ k'₁ then binBit ⌊y₁⌋₊ r else 0) + (if r ≤ k'₂ then binBit ⌊y₂⌋₊ r else 0)) ∧
      ((if r = k₁ then 1 else 0) + (if r = k₂ then 1 else 0) =
       (if r = k'₁ then 1 else 0) + (if r = k'₂ then 1 else 0)) := by
    intro r hr
    have hs := hslot_eq r hr
    have hdecomp : ∀ (k p : ℕ), ruzsaSlot α k p r =
        (if r ≤ k then fracChunk (α * Real.logb 2 (p : ℝ)) r else 0) +
        2 ^ (ruzsaL r + 1) * (if r ≤ k then binBit ⌊α * Real.logb 2 (p : ℝ)⌋₊ r else 0) +
        2 ^ (ruzsaL r + 3) * (if r = k then 1 else 0) := by
      intro k p
      dsimp only [ruzsaSlot]
      split_ifs with h1 h2
      · rfl
      · rfl
      · omega
      · ring
    rw [hdecomp k₁ p₁, hdecomp k₂ p₂, hdecomp k'₁ p'₁, hdecomp k'₂ p'₂] at hs
    have hrearr :
        ((if r ≤ k₁ then fracChunk x₁ r else 0) + (if r ≤ k₂ then fracChunk x₂ r else 0)) +
        2 ^ (ruzsaL r + 1) * ((if r ≤ k₁ then binBit ⌊x₁⌋₊ r else 0) + (if r ≤ k₂ then binBit ⌊x₂⌋₊ r else 0)) +
        2 ^ (ruzsaL r + 3) * ((if r = k₁ then 1 else 0) + (if r = k₂ then 1 else 0)) =
        ((if r ≤ k'₁ then fracChunk y₁ r else 0) + (if r ≤ k'₂ then fracChunk y₂ r else 0)) +
        2 ^ (ruzsaL r + 1) * ((if r ≤ k'₁ then binBit ⌊y₁⌋₊ r else 0) + (if r ≤ k'₂ then binBit ⌊y₂⌋₊ r else 0)) +
        2 ^ (ruzsaL r + 3) * ((if r = k'₁ then 1 else 0) + (if r = k'₂ then 1 else 0)) := by
      dsimp only [x₁, x₂, y₁, y₂]; linarith
    apply ruzsa_slot_inj _ _ _ _ hrearr
    · have h1 := fracChunk_lt x₁ r; have h2 := fracChunk_lt x₂ r
      rw [pow_succ]; split_ifs <;> omega
    · have h1 := fracChunk_lt y₁ r; have h2 := fracChunk_lt y₂ r
      rw [pow_succ]; split_ifs <;> omega
    · have h1 := binBit_lt_two ⌊x₁⌋₊ r; have h2 := binBit_lt_two ⌊x₂⌋₊ r
      split_ifs <;> omega
    · have h1 := binBit_lt_two ⌊y₁⌋₊ r; have h2 := binBit_lt_two ⌊y₂⌋₊ r
      split_ifs <;> omega
  -- (a) Recover k₁ = k'₁ ∧ k₂ = k'₂ from marker field e_r
  have hk_eq : k₁ = k'₁ ∧ k₂ = k'₂ := by
    have he_k₁ := (hfields k₁ (by simp only [Finset.mem_Icc, K]; omega)).2.2
    have he_k₂ := (hfields k₂ (by simp only [Finset.mem_Icc, K]; omega)).2.2
    have he_k'₂ := (hfields k'₂ (by simp only [Finset.mem_Icc, K]; omega)).2.2
    have hle1 : k₂ ≤ k'₂ := by
      by_contra hgt
      push Not at hgt
      have hne1 : k₂ ≠ k'₁ := by omega
      have hne2 : k₂ ≠ k'₂ := by omega
      simp only [↓reduceIte, hne1, hne2] at he_k₂
      split_ifs at he_k₂ <;> omega
    have hle2 : k'₂ ≤ k₂ := by
      by_contra hgt
      push Not at hgt
      have hne1 : k'₂ ≠ k₁ := by omega
      have hne2 : k'₂ ≠ k₂ := by omega
      simp only [↓reduceIte, hne1, hne2] at he_k'₂
      split_ifs at he_k'₂ <;> omega
    have hk2 : k₂ = k'₂ := le_antisymm hle1 hle2
    rw [hk2] at he_k₁
    have hk1 : k₁ = k'₁ := by
      by_contra hne
      simp only [↓reduceIte, hne] at he_k₁
      split_ifs at he_k₁ <;> omega
    exact ⟨hk1, hk2⟩
  obtain ⟨rfl, rfl⟩ := hk_eq
  -- (b) Integer parts sum equally: ⌊x₁⌋₊ + ⌊x₂⌋₊ = ⌊y₁⌋₊ + ⌊y₂⌋₊
  have hfloor_sum : ⌊x₁⌋₊ + ⌊x₂⌋₊ = ⌊y₁⌋₊ + ⌊y₂⌋₊ := by
    have hfl1 := ruzsa_floor_lt_two_pow hα hk₁ hp₁
    have hfl2 := ruzsa_floor_lt_two_pow hα (hk₁.trans hk12) hp₂
    have hfl3 := ruzsa_floor_lt_two_pow hα hk₁ hp'₁
    have hfl4 := ruzsa_floor_lt_two_pow hα (hk₁.trans hk12) hp'₂
    have hb_eq : ∀ r ∈ Finset.Icc 1 k₂,
        (if r ≤ k₁ then binBit ⌊x₁⌋₊ r else 0) + binBit ⌊x₂⌋₊ r =
        (if r ≤ k₁ then binBit ⌊y₁⌋₊ r else 0) + binBit ⌊y₂⌋₊ r := by
      intro r hr
      have h2 := (hfields r (by simp only [Finset.mem_Icc, K] at hr ⊢; omega)).2.1
      have hr2 : r ≤ k₂ := (Finset.mem_Icc.mp hr).2
      simpa [hr2] using h2
    have hsum_bits :
        ∑ r ∈ Finset.Icc 1 k₂, ((if r ≤ k₁ then binBit ⌊x₁⌋₊ r else 0) + binBit ⌊x₂⌋₊ r) * 2 ^ (r - 1) =
        ∑ r ∈ Finset.Icc 1 k₂, ((if r ≤ k₁ then binBit ⌊y₁⌋₊ r else 0) + binBit ⌊y₂⌋₊ r) * 2 ^ (r - 1) :=
      Finset.sum_congr rfl fun r hr => by rw [hb_eq r hr]
    have hsplit_sum : ∀ (a b : ℕ), a < 2 ^ k₁ → b < 2 ^ k₂ →
        ∑ r ∈ Finset.Icc 1 k₂, ((if r ≤ k₁ then binBit a r else 0) + binBit b r) * 2 ^ (r - 1) = a + b := by
      intro a b ha hb
      have h1 : ∑ r ∈ Finset.Icc 1 k₂, ((if r ≤ k₁ then binBit a r else 0) + binBit b r) * 2 ^ (r - 1) =
          (∑ r ∈ Finset.Icc 1 k₂, (if r ≤ k₁ then binBit a r else 0) * 2 ^ (r - 1)) +
          (∑ r ∈ Finset.Icc 1 k₂, binBit b r * 2 ^ (r - 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun r _ => by ring
      rw [h1, sum_binBit_eq b k₂ hb]
      congr 1
      have hsub : Finset.Icc 1 k₁ ⊆ Finset.Icc 1 k₂ := fun r hr => by simp only [Finset.mem_Icc] at hr ⊢; omega
      rw [← Finset.sum_subset hsub]
      · calc ∑ r ∈ Finset.Icc 1 k₁, (if r ≤ k₁ then binBit a r else 0) * 2 ^ (r - 1)
            = ∑ r ∈ Finset.Icc 1 k₁, binBit a r * 2 ^ (r - 1) :=
              Finset.sum_congr rfl fun r hr => by simp [(Finset.mem_Icc.mp hr).2]
          _ = a := sum_binBit_eq a k₁ ha
      · intro r hr hnot
        simp only [Finset.mem_Icc] at hr hnot
        have : ¬ r ≤ k₁ := by omega
        simp [this]
    rw [hsplit_sum ⌊x₁⌋₊ ⌊x₂⌋₊ hfl1 hfl2, hsplit_sum ⌊y₁⌋₊ ⌊y₂⌋₊ hfl3 hfl4] at hsum_bits
    exact hsum_bits
  -- Combine floor equality + telescoping fractional chunks on 1..k₁
  have hrange1 : |Real.logb 2 ((p₁ * p₂ : ℕ) : ℝ) - Real.logb 2 ((p'₁ * p'₂ : ℕ) : ℝ)| <
      2 / (2 : ℝ) ^ ruzsaS k₁ := by
    have hv_eq : ∀ r ∈ Finset.Icc 1 k₁, fracChunk x₁ r + fracChunk x₂ r = fracChunk y₁ r + fracChunk y₂ r := by
      intro r hr
      have h1 := (hfields r (by simp only [Finset.mem_Icc, K] at hr ⊢; omega)).1
      have hr1 : r ≤ k₁ := (Finset.mem_Icc.mp hr).2
      have hr2 : r ≤ k₂ := hr1.trans hk12
      simpa [hr1, hr2] using h1
    have ht1 := telescoping_fract x₁ 0 k₁ (Nat.zero_le _)
    have ht2 := telescoping_fract x₂ 0 k₁ (Nat.zero_le _)
    have ht3 := telescoping_fract y₁ 0 k₁ (Nat.zero_le _)
    have ht4 := telescoping_fract y₂ 0 k₁ (Nat.zero_le _)
    simp only [ruzsaS, zero_pow (by norm_num : 2 ≠ 0), pow_zero, one_mul, Nat.sub_zero] at ht1 ht2 ht3 ht4
    have hsum_v :
        (∑ r ∈ Finset.Icc 1 k₁, (fracChunk x₁ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) +
        (∑ r ∈ Finset.Icc 1 k₁, (fracChunk x₂ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) =
        (∑ r ∈ Finset.Icc 1 k₁, (fracChunk y₁ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) +
        (∑ r ∈ Finset.Icc 1 k₁, (fracChunk y₂ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [← add_div, ← add_div]
      congr 1
      have := hv_eq r hr
      exact_mod_cast this
    have hfract_diff : (Int.fract x₁ + Int.fract x₂) - (Int.fract y₁ + Int.fract y₂) =
        ((Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₁) + Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₂)) -
         (Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₁) + Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₂))) /
          (2 : ℝ) ^ (k₁ ^ 2) := by
      rw [ht1, ht2, ht3, ht4]
      change ((∑ r ∈ Finset.Icc 1 k₁, (fracChunk x₁ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) +
          Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₁) / (2 : ℝ) ^ (k₁ ^ 2) +
          ((∑ r ∈ Finset.Icc 1 k₁, (fracChunk x₂ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) +
          Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₂) / (2 : ℝ) ^ (k₁ ^ 2))) -
        ((∑ r ∈ Finset.Icc 1 k₁, (fracChunk y₁ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) +
          Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₁) / (2 : ℝ) ^ (k₁ ^ 2) +
          ((∑ r ∈ Finset.Icc 1 k₁, (fracChunk y₂ r : ℝ) / (2 : ℝ) ^ (r ^ 2)) +
          Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₂) / (2 : ℝ) ^ (k₁ ^ 2))) = _
      have hrhs :
          ((Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₁) + Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₂)) -
           (Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₁) + Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₂))) /
            (2 : ℝ) ^ (k₁ ^ 2) =
          (Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₁) / (2 : ℝ) ^ (k₁ ^ 2) +
           Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * x₂) / (2 : ℝ) ^ (k₁ ^ 2)) -
          (Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₁) / (2 : ℝ) ^ (k₁ ^ 2) +
           Int.fract ((2 : ℝ) ^ (k₁ ^ 2) * y₂) / (2 : ℝ) ^ (k₁ ^ 2)) := by ring
      linarith
    have hx_nn : ∀ {k p : ℕ}, p ∈ ruzsaPrimes k → 0 ≤ α * Real.logb 2 (p : ℝ) := fun hp =>
      mul_nonneg (by linarith [hα.1])
        (Real.logb_nonneg (by norm_num) (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
    have hdec : ∀ z : ℝ, 0 ≤ z → z = (⌊z⌋₊ : ℝ) + Int.fract z := fun z hz => by
      have hfl : (⌊z⌋₊ : ℤ) = ⌊z⌋ :=
        (Int.floor_eq_iff.mpr ⟨by exact_mod_cast Nat.floor_le hz,
          by exact_mod_cast Nat.lt_floor_add_one z⟩).symm
      have hflR : ((⌊z⌋₊ : ℕ) : ℝ) = (⌊z⌋ : ℝ) := by exact_mod_cast hfl
      rw [hflR, add_comm, Int.fract_add_floor]
    have hxy_diff : (x₁ + x₂) - (y₁ + y₂) = (Int.fract x₁ + Int.fract x₂) - (Int.fract y₁ + Int.fract y₂) := by
      have h1 := hdec x₁ (hx_nn hp₁); have h2 := hdec x₂ (hx_nn hp₂)
      have h3 := hdec y₁ (hx_nn hp'₁); have h4 := hdec y₂ (hx_nn hp'₂)
      have hflR : (⌊x₁⌋₊ : ℝ) + (⌊x₂⌋₊ : ℝ) = (⌊y₁⌋₊ : ℝ) + (⌊y₂⌋₊ : ℝ) := by exact_mod_cast hfloor_sum
      linarith
    have habs_xy : |(x₁ + x₂) - (y₁ + y₂)| < 2 / (2 : ℝ) ^ ruzsaS k₁ := by
      rw [hxy_diff, hfract_diff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k₁ ^ 2))]
      simp only [ruzsaS]
      apply div_lt_div_of_pos_right _ (by positivity)
      rw [abs_lt]
      have f1 := Int.fract_nonneg ((2 : ℝ) ^ (k₁ ^ 2) * x₁)
      have f1' := Int.fract_lt_one ((2 : ℝ) ^ (k₁ ^ 2) * x₁)
      have f2 := Int.fract_nonneg ((2 : ℝ) ^ (k₁ ^ 2) * x₂)
      have f2' := Int.fract_lt_one ((2 : ℝ) ^ (k₁ ^ 2) * x₂)
      have f3 := Int.fract_nonneg ((2 : ℝ) ^ (k₁ ^ 2) * y₁)
      have f3' := Int.fract_lt_one ((2 : ℝ) ^ (k₁ ^ 2) * y₁)
      have f4 := Int.fract_nonneg ((2 : ℝ) ^ (k₁ ^ 2) * y₂)
      have f4' := Int.fract_lt_one ((2 : ℝ) ^ (k₁ ^ 2) * y₂)
      constructor <;> linarith
    have hlog_mul : ∀ {a b : ℕ}, 0 < a → 0 < b →
        Real.logb 2 ((a * b : ℕ) : ℝ) = Real.logb 2 (a : ℝ) + Real.logb 2 (b : ℝ) := fun ha hb => by
      push_cast; exact Real.logb_mul (Nat.cast_ne_zero.mpr ha.ne') (Nat.cast_ne_zero.mpr hb.ne')
    have hp1pos := (Finset.mem_filter.mp hp₁).2.pos
    have hp2pos := (Finset.mem_filter.mp hp₂).2.pos
    have hp'1pos := (Finset.mem_filter.mp hp'₁).2.pos
    have hp'2pos := (Finset.mem_filter.mp hp'₂).2.pos
    have hfac : (x₁ + x₂) - (y₁ + y₂) =
        α * (Real.logb 2 ((p₁ * p₂ : ℕ) : ℝ) - Real.logb 2 ((p'₁ * p'₂ : ℕ) : ℝ)) := by
      rw [hlog_mul hp1pos hp2pos, hlog_mul hp'1pos hp'2pos]
      dsimp only [x₁, x₂, y₁, y₂]; ring
    rw [hfac, abs_mul, abs_of_pos (by linarith [hα.1])] at habs_xy
    have hle1 : |Real.logb 2 ((p₁ * p₂ : ℕ) : ℝ) - Real.logb 2 ((p'₁ * p'₂ : ℕ) : ℝ)| ≤
        α * |Real.logb 2 ((p₁ * p₂ : ℕ) : ℝ) - Real.logb 2 ((p'₁ * p'₂ : ℕ) : ℝ)| := by
      have := mul_le_mul_of_nonneg_right hα.1
        (abs_nonneg (Real.logb 2 ((p₁ * p₂ : ℕ) : ℝ) - Real.logb 2 ((p'₁ * p'₂ : ℕ) : ℝ)))
      simpa using this
    exact hle1.trans_lt habs_xy
  -- (c) Range 2 (k₁ < k₂): telescoping on k₁ + 1 .. k₂
  have hrange2 : k₁ < k₂ → ∃ m : ℤ,
      |(2 : ℝ) ^ ruzsaS k₁ * (α * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ))) - (m : ℝ)| <
        1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) := by
    intro hlt
    have hv_eq : ∀ r ∈ Finset.Icc (k₁ + 1) k₂, fracChunk x₂ r = fracChunk y₂ r := by
      intro r hr
      have h1 := (hfields r (by simp only [Finset.mem_Icc, K] at hr ⊢; omega)).1
      have hr1 : ¬ r ≤ k₁ := by simp only [Finset.mem_Icc] at hr; omega
      have hr2 : r ≤ k₂ := (Finset.mem_Icc.mp hr).2
      simpa [hr1, hr2] using h1
    have ht2 := telescoping_fract x₂ k₁ k₂ hk12
    have ht4 := telescoping_fract y₂ k₁ k₂ hk12
    have hsum_eq' :
        ∑ r ∈ Finset.Icc (k₁ + 1) k₂, (fracChunk x₂ r : ℝ) / (2 : ℝ) ^ (ruzsaS r - ruzsaS k₁) =
        ∑ r ∈ Finset.Icc (k₁ + 1) k₂, (fracChunk y₂ r : ℝ) / (2 : ℝ) ^ (ruzsaS r - ruzsaS k₁) :=
      Finset.sum_congr rfl fun r hr => by rw [hv_eq r hr]
    refine ⟨⌊(2 : ℝ) ^ ruzsaS k₁ * x₂⌋ - ⌊(2 : ℝ) ^ ruzsaS k₁ * y₂⌋, ?_⟩
    have hdiff_eq : (2 : ℝ) ^ ruzsaS k₁ * (α * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ))) -
        ((⌊(2 : ℝ) ^ ruzsaS k₁ * x₂⌋ - ⌊(2 : ℝ) ^ ruzsaS k₁ * y₂⌋ : ℤ) : ℝ) =
        Int.fract ((2 : ℝ) ^ ruzsaS k₁ * x₂) - Int.fract ((2 : ℝ) ^ ruzsaS k₁ * y₂) := by
      push_cast
      have hx_eq : (2 : ℝ) ^ ruzsaS k₁ * (α * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ))) =
          (2 : ℝ) ^ ruzsaS k₁ * x₂ - (2 : ℝ) ^ ruzsaS k₁ * y₂ := by dsimp only [x₂, y₂]; ring
      rw [hx_eq, Int.fract, Int.fract]; ring
    rw [hdiff_eq, ht2, ht4, hsum_eq']
    have hcancel : (∑ r ∈ Finset.Icc (k₁ + 1) k₂, (fracChunk y₂ r : ℝ) / 2 ^ (ruzsaS r - ruzsaS k₁)) +
        Int.fract (2 ^ ruzsaS k₂ * x₂) / 2 ^ (ruzsaS k₂ - ruzsaS k₁) -
        ((∑ r ∈ Finset.Icc (k₁ + 1) k₂, (fracChunk y₂ r : ℝ) / 2 ^ (ruzsaS r - ruzsaS k₁)) +
        Int.fract (2 ^ ruzsaS k₂ * y₂) / 2 ^ (ruzsaS k₂ - ruzsaS k₁)) =
        (Int.fract (2 ^ ruzsaS k₂ * x₂) - Int.fract (2 ^ ruzsaS k₂ * y₂)) /
          (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) := by ring
    rw [hcancel, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))]
    apply div_lt_div_of_pos_right _ (by positivity)
    rw [abs_lt]
    have f2 := Int.fract_nonneg ((2 : ℝ) ^ ruzsaS k₂ * x₂)
    have f2' := Int.fract_lt_one ((2 : ℝ) ^ ruzsaS k₂ * x₂)
    have f4 := Int.fract_nonneg ((2 : ℝ) ^ ruzsaS k₂ * y₂)
    have f4' := Int.fract_lt_one ((2 : ℝ) ^ ruzsaS k₂ * y₂)
    constructor <;> linarith
  exact ⟨⟨rfl, rfl⟩, hrange1, hrange2⟩

-- Elementary logb 2 difference lower bound: for positive reals 0 < v < u, (u - v) / (2 * u) ≤ logb 2 u - logb 2 v
private lemma logb2_sub_ge {u v : ℝ} (hv : 0 < v) (hvu : v < u) :
    (u - v) / (2 * u) ≤ Real.logb 2 u - Real.logb 2 v := by
  have hu : 0 < u := hv.trans hvu
  rw [← Real.logb_div hu.ne' hv.ne', Real.logb]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith)
  have hln_ge : (u - v) / u ≤ Real.log (u / v) := by
    -- 1 - v/u ≤ log(u/v) because 1 - 1/t ≤ log t (from log(1/t) ≤ 1/t - 1)
    have h1 := Real.log_le_sub_one_of_pos (div_pos hv hu)
    rw [Real.log_div hv.ne' hu.ne'] at h1
    rw [Real.log_div hu.ne' hv.ne']
    have heq : (u - v) / u = 1 - v / u := by field_simp
    linarith
  have h1 : (u - v) / (2 * u) ≤ (u - v) / u := by
    have hnn : 0 ≤ u - v := by linarith
    exact div_le_div_of_nonneg_left hnn hu (by linarith)
  have h2 : (u - v) / u ≤ Real.log (u / v) / Real.log 2 := by
    rw [le_div_iff₀ hlog2_pos]
    calc (u - v) / u * Real.log 2 ≤ (u - v) / u * 1 :=
          mul_le_mul_of_nonneg_left hlog2_le (div_nonneg (by linarith) hu.le)
      _ = (u - v) / u := mul_one _
      _ ≤ Real.log (u / v) := hln_ge
  exact h1.trans h2

-- Unique prime-pair factorization: a positive integer has at most 2 ordered factorizations into primes
private lemma prime_mul_eq_iff {p₁ p₂ q₁ q₂ : ℕ}
    (hp₁ : p₁.Prime) (_hp₂ : p₂.Prime) (hq₁ : q₁.Prime) (hq₂ : q₂.Prime)
    (heq : p₁ * p₂ = q₁ * q₂) :
    (p₁ = q₁ ∧ p₂ = q₂) ∨ (p₁ = q₂ ∧ p₂ = q₁) := by
  have hdvd : p₁ ∣ q₁ * q₂ := ⟨p₂, heq.symm⟩
  rcases hp₁.dvd_mul.mp hdvd with h1 | h2
  · have e1 : p₁ = q₁ := (Nat.prime_dvd_prime_iff_eq hp₁ hq₁).mp h1
    subst e1
    have e2 : p₂ = q₂ := Nat.eq_of_mul_eq_mul_left hp₁.pos heq
    exact Or.inl ⟨rfl, e2⟩
  · have e1 : p₁ = q₂ := (Nat.prime_dvd_prime_iff_eq hp₁ hq₂).mp h2
    subst e1
    have e2 : p₂ = q₁ := Nat.eq_of_mul_eq_mul_left hp₁.pos (by linarith)
    exact Or.inr ⟨rfl, e2⟩

-- Zero same-level collisions & injectivity for k ≥ 25
private lemma ruzsaCode_same_level_inj {α : ℝ} (hα : α ∈ Set.Icc (1 : ℝ) 2)
    {k p₁ p₂ p'₁ p'₂ : ℕ} (hk : 25 ≤ k)
    (hp₁ : p₁ ∈ ruzsaPrimes k) (hp₂ : p₂ ∈ ruzsaPrimes k)
    (hp'₁ : p'₁ ∈ ruzsaPrimes k) (hp'₂ : p'₂ ∈ ruzsaPrimes k)
    (heq : ruzsaCode α k p₁ + ruzsaCode α k p₂ = ruzsaCode α k p'₁ + ruzsaCode α k p'₂) :
    (p₁ = p'₁ ∧ p₂ = p'₂) ∨ (p₁ = p'₂ ∧ p₂ = p'₁) := by
  have hdec := (ruzsaCode_decode hα hk le_rfl hk le_rfl hp₁ hp₂ hp'₁ hp'₂ heq).2.1
  have hP_le : ∀ p ∈ ruzsaPrimes k, (p : ℝ) ≤ (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2) := fun p hp => by
    have hle : p ≤ ruzsaP k := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    exact (Nat.cast_le.mpr hle).trans (Nat.floor_le (by positivity))
  have hθ := ruzsaTheta_bounds hk
  have hsqrt2_lt : Real.sqrt 2 < 1.42 := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.42 ^ 2)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hθ_lt : ruzsaTheta k < 0.42 := by linarith [hθ.2]
  -- 4 * (2^(θ k * k^2))^2 < 2^(k^2) since 2 + 0.84 * k^2 < k^2 for k ≥ 25
  have h4P2_lt : 4 * ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) ^ 2 < (2 : ℝ) ^ ruzsaS k := by
    have hk25 : (25 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hexp : 2 + 2 * (ruzsaTheta k * (k : ℝ) ^ 2) < ((k ^ 2 : ℕ) : ℝ) := by
      push_cast
      have h1 : 2 * (ruzsaTheta k * (k : ℝ) ^ 2) < 0.84 * (k : ℝ) ^ 2 := by
        have hk2pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
        calc 2 * (ruzsaTheta k * (k : ℝ) ^ 2) = (2 * ruzsaTheta k) * (k : ℝ) ^ 2 := by ring
          _ < 0.84 * (k : ℝ) ^ 2 := mul_lt_mul_of_pos_right (by linarith) hk2pos
      have hk2ge : (625 : ℝ) ≤ (k : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 25) hk25 2; norm_num at this; exact this
      linarith
    have hrew : 4 * ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) ^ 2 =
        (2 : ℝ) ^ (2 + 2 * (ruzsaTheta k * (k : ℝ) ^ 2)) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4, ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
      congr 1; push_cast; ring
    rw [hrew, ruzsaS, ← Real.rpow_natCast (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  have hprod_eq : p₁ * p₂ = p'₁ * p'₂ := by
    by_contra hne
    have hbound_prod : ∀ {u v : ℕ}, 0 < v → v < u →
        (u : ℝ) ≤ ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) ^ 2 →
        2 / (2 : ℝ) ^ ruzsaS k ≤ |Real.logb 2 (u : ℝ) - Real.logb 2 (v : ℝ)| := by
      intro u v hv hlt hu_le
      have hvR : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
      have hltR : (v : ℝ) < (u : ℝ) := Nat.cast_lt.mpr hlt
      have huR : (0 : ℝ) < (u : ℝ) := hvR.trans hltR
      have h1 : (1 : ℝ) ≤ (u : ℝ) - (v : ℝ) := by
        have : v + 1 ≤ u := hlt
        have : (v : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast this
        linarith
      have hlog_ge := logb2_sub_ge hvR hltR
      have habs : (u - v : ℝ) / (2 * u) ≤ |Real.logb 2 (u : ℝ) - Real.logb 2 (v : ℝ)| :=
        hlog_ge.trans (le_abs_self _)
      have h2 : 2 / (2 : ℝ) ^ ruzsaS k ≤ 1 / (2 * (u : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 4 * (u : ℝ) ≤ 4 * ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) ^ 2 := by linarith
        linarith
      have h3 : 1 / (2 * (u : ℝ)) ≤ ((u : ℝ) - (v : ℝ)) / (2 * (u : ℝ)) :=
        div_le_div_of_nonneg_right h1 (by positivity)
      exact (h2.trans h3).trans habs
    have hu1 : ((p₁ * p₂ : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) ^ 2 := by
      push_cast; rw [sq]; exact mul_le_mul (hP_le p₁ hp₁) (hP_le p₂ hp₂) (Nat.cast_nonneg _) (by positivity)
    have hu2 : ((p'₁ * p'₂ : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) ^ 2 := by
      push_cast; rw [sq]; exact mul_le_mul (hP_le p'₁ hp'₁) (hP_le p'₂ hp'₂) (Nat.cast_nonneg _) (by positivity)
    have hp12_pos : 0 < p₁ * p₂ := Nat.mul_pos (Finset.mem_filter.mp hp₁).2.pos (Finset.mem_filter.mp hp₂).2.pos
    have hp'12_pos : 0 < p'₁ * p'₂ := Nat.mul_pos (Finset.mem_filter.mp hp'₁).2.pos (Finset.mem_filter.mp hp'₂).2.pos
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hbound_prod hp12_pos hlt hu2
      rw [abs_sub_comm] at this
      linarith
    · have := hbound_prod hp'12_pos hgt hu1
      linarith
  exact prime_mul_eq_iff (Finset.mem_filter.mp hp₁).2 (Finset.mem_filter.mp hp₂).2
    (Finset.mem_filter.mp hp'₁).2 (Finset.mem_filter.mp hp'₂).2 hprod_eq

-- Quadruple count bound for Subcase 2a: #{(p₁, p'₁, p₂, p'₂) : p₁*p₂ ≠ p'₁*p'₂ ∧ |logb 2 (p₁p₂) - logb 2 (p'₁p'₂)| < 2 / 2^(S k₁)}
private lemma ruzsa_quadruple_card_bound {k₁ k₂ : ℕ} (_hk₁ : 25 ≤ k₁) (_hk12 : k₁ < k₂) :
    let Q := ((ruzsaPrimes k₁ ×ˢ ruzsaPrimes k₁) ×ˢ (ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂)).filter
      (fun q => q.2.1 ≠ q.2.2 ∧ q.1.1 * q.2.1 ≠ q.1.2 * q.2.2 ∧
        |Real.logb 2 ((q.1.1 * q.2.1 : ℕ) : ℝ) - Real.logb 2 ((q.1.2 * q.2.2 : ℕ) : ℝ)| <
          2 / (2 : ℝ) ^ ruzsaS k₁)
    (Q.card : ℝ) ≤ 32 * ((2 : ℝ) ^ (ruzsaTheta k₁ * (k₁ : ℝ) ^ 2)) ^ 2 *
        ((2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2)) ^ 2 / (2 : ℝ) ^ ruzsaS k₁ ∧
    (4 * (2 : ℝ) ^ (ruzsaTheta k₁ * (k₁ : ℝ) ^ 2) * (2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2) <
        (2 : ℝ) ^ ruzsaS k₁ → Q.card = 0) := by
  intro Q
  set X₁ : ℝ := (2 : ℝ) ^ (ruzsaTheta k₁ * (k₁ : ℝ) ^ 2)
  set X₂ : ℝ := (2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2)
  have hP1 : ∀ p ∈ ruzsaPrimes k₁, (p : ℝ) ≤ X₁ := fun p hp =>
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2).trans (Nat.floor_le (by positivity))
  have hP2 : ∀ p ∈ ruzsaPrimes k₂, (p : ℝ) ≤ X₂ := fun p hp =>
    (Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2).trans (Nat.floor_le (by positivity))
  -- Every q ∈ Q satisfies 0 < |p₁*p₂ - p'₁*p'₂| < 4 * X₁ * X₂ / 2^(S k₁)
  have hdiff_lt : ∀ q ∈ Q,
      1 ≤ |(q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)| ∧
      (|(q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)| : ℝ) < 4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := by
    intro q hq
    simp only [Q, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨⟨hp1, hp'1⟩, ⟨hp2, hp'2⟩⟩, _, hne, hlog⟩ := hq
    have hu_pos : (0 : ℝ) < ((q.1.1 * q.2.1 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.mul_pos (Finset.mem_filter.mp hp1).2.pos (Finset.mem_filter.mp hp2).2.pos)
    have hv_pos : (0 : ℝ) < ((q.1.2 * q.2.2 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.mul_pos (Finset.mem_filter.mp hp'1).2.pos (Finset.mem_filter.mp hp'2).2.pos)
    have hu_le : ((q.1.1 * q.2.1 : ℕ) : ℝ) ≤ X₁ * X₂ := by
      push_cast; exact mul_le_mul (hP1 _ hp1) (hP2 _ hp2) (Nat.cast_nonneg _) (by positivity)
    have hv_le : ((q.1.2 * q.2.2 : ℕ) : ℝ) ≤ X₁ * X₂ := by
      push_cast; exact mul_le_mul (hP1 _ hp'1) (hP2 _ hp'2) (Nat.cast_nonneg _) (by positivity)
    constructor
    · have hneZ : (q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast hne)
      exact Int.one_le_abs hneZ
    · have habs_eq : (|(q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)| : ℝ) =
          |((q.1.1 * q.2.1 : ℕ) : ℝ) - ((q.1.2 * q.2.2 : ℕ) : ℝ)| := by push_cast; rfl
      rw [habs_eq]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 := logb2_sub_ge hu_pos (Nat.cast_lt.mpr hlt)
        rw [abs_sub_comm] at hlog
        have h2 : ((q.1.2 * q.2.2 : ℕ) : ℝ) - ((q.1.1 * q.2.1 : ℕ) : ℝ) <
            2 * ((q.1.2 * q.2.2 : ℕ) : ℝ) * (2 / (2 : ℝ) ^ ruzsaS k₁) := by
          have h3 : (((q.1.2 * q.2.2 : ℕ) : ℝ) - ((q.1.1 * q.2.1 : ℕ) : ℝ)) /
              (2 * ((q.1.2 * q.2.2 : ℕ) : ℝ)) < 2 / (2 : ℝ) ^ ruzsaS k₁ :=
            h1.trans_lt ((le_abs_self _).trans_lt hlog)
          rw [div_lt_iff₀ (by positivity)] at h3
          linarith
        rw [abs_sub_comm, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hlt))]
        have h4 : 2 * ((q.1.2 * q.2.2 : ℕ) : ℝ) * (2 / (2 : ℝ) ^ ruzsaS k₁) ≤
            4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := by
          calc 2 * ((q.1.2 * q.2.2 : ℕ) : ℝ) * (2 / (2 : ℝ) ^ ruzsaS k₁)
              = ((q.1.2 * q.2.2 : ℕ) : ℝ) * (4 / (2 : ℝ) ^ ruzsaS k₁) := by ring
            _ ≤ (X₁ * X₂) * (4 / (2 : ℝ) ^ ruzsaS k₁) :=
                mul_le_mul_of_nonneg_right hv_le (by positivity)
            _ = 4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := by ring
        exact h2.trans_le h4
      · have h1 := logb2_sub_ge hv_pos (Nat.cast_lt.mpr hgt)
        have h2 : ((q.1.1 * q.2.1 : ℕ) : ℝ) - ((q.1.2 * q.2.2 : ℕ) : ℝ) <
            2 * ((q.1.1 * q.2.1 : ℕ) : ℝ) * (2 / (2 : ℝ) ^ ruzsaS k₁) := by
          have h3 : (((q.1.1 * q.2.1 : ℕ) : ℝ) - ((q.1.2 * q.2.2 : ℕ) : ℝ)) /
              (2 * ((q.1.1 * q.2.1 : ℕ) : ℝ)) < 2 / (2 : ℝ) ^ ruzsaS k₁ :=
            h1.trans_lt ((le_abs_self _).trans_lt hlog)
          rw [div_lt_iff₀ (by positivity)] at h3
          linarith
        rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
        have h4 : 2 * ((q.1.1 * q.2.1 : ℕ) : ℝ) * (2 / (2 : ℝ) ^ ruzsaS k₁) ≤
            4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := by
          calc 2 * ((q.1.1 * q.2.1 : ℕ) : ℝ) * (2 / (2 : ℝ) ^ ruzsaS k₁)
              = ((q.1.1 * q.2.1 : ℕ) : ℝ) * (4 / (2 : ℝ) ^ ruzsaS k₁) := by ring
            _ ≤ (X₁ * X₂) * (4 / (2 : ℝ) ^ ruzsaS k₁) :=
                mul_le_mul_of_nonneg_right hu_le (by positivity)
            _ = 4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := by ring
        exact h2.trans_le h4
  -- Case split on whether Δ := ⌊4 * X₁ * X₂ / 2^(S k₁)⌋₊ = 0
  have hzero : 4 * X₁ * X₂ < (2 : ℝ) ^ ruzsaS k₁ → Q.card = 0 := by
    intro hlt
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro q hq
    have ⟨h1, h2⟩ := hdiff_lt q hq
    have h1R : (1 : ℝ) ≤ (|(q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)| : ℝ) := by exact_mod_cast h1
    have hlt1 : 4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ < 1 := (div_lt_one (by positivity)).mpr hlt
    linarith
  refine ⟨?_, hzero⟩
  set Δ : ℕ := ⌊4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁⌋₊
  -- Map Q → (ruzsaPrimes k₁ ×ˢ ruzsaPrimes k₂) ×ˢ (Icc (-Δ : ℤ) Δ ×ˢ ({false, true} : Finset Bool))
  -- Wait: for fixed (p₁, p₂, d) with d = p₁*p₂ - p'₁*p'₂ ∈ [-Δ, Δ], p'₁*p'₂ is fixed,
  -- and at most 2 ordered prime pairs (p'₁, p'₂) have that product (distinguished by Bool: p'₁ ≤ p'₂)!
  let Tgt := (ruzsaPrimes k₁ ×ˢ ruzsaPrimes k₂) ×ˢ (Finset.Icc (-(Δ : ℤ)) (Δ : ℤ) ×ˢ (Finset.univ : Finset Bool))
  have hcard_le : Q.card ≤ Tgt.card := by
    refine Finset.card_le_card_of_injOn
      (fun q => ((q.1.1, q.2.1), ((q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ), decide (q.1.2 ≤ q.2.2)))) ?_ ?_
    · intro q hq
      have ⟨_, h2⟩ := hdiff_lt q hq
      simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      simp only [Tgt, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, and_true]
      refine ⟨⟨hq.1.1.1, hq.1.2.1⟩, ?_⟩
      have habs_le : |(q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)| ≤ (Δ : ℤ) := by
        have hlt_nat : Int.natAbs ((q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)) ≤ Δ := by
          apply Nat.le_floor
          have hcast : ((Int.natAbs ((q.1.1 * q.2.1 : ℤ) - (q.1.2 * q.2.2 : ℤ)) : ℕ) : ℝ) =
              |((q.1.1 * q.2.1 : ℤ) : ℝ) - ((q.1.2 * q.2.2 : ℤ) : ℝ)| := by
            rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub]
          have h2' : |((q.1.1 * q.2.1 : ℤ) : ℝ) - ((q.1.2 * q.2.2 : ℤ) : ℝ)| <
              4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := by
            simpa using h2
          linarith
        have := Int.ofNat_le.mpr hlt_nat
        rwa [Int.natCast_natAbs] at this
      exact abs_le.mp habs_le
    · intro q₁ hq₁ q₂ hq₂ heq
      dsimp only at heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨⟨hp1, hp2⟩, hdiff, hbool⟩ := heq
      simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq₁ hq₂
      have hprod_eq : q₁.1.2 * q₁.2.2 = q₂.1.2 * q₂.2.2 := by
        have : (q₁.1.2 * q₁.2.2 : ℤ) = (q₂.1.2 * q₂.2.2 : ℤ) := by rw [hp1, hp2] at hdiff; linarith
        exact_mod_cast this
      have hprime_pair := prime_mul_eq_iff
        (Finset.mem_filter.mp hq₁.1.1.2).2 (Finset.mem_filter.mp hq₁.1.2.2).2
        (Finset.mem_filter.mp hq₂.1.1.2).2 (Finset.mem_filter.mp hq₂.1.2.2).2 hprod_eq
      rcases hprime_pair with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext (Prod.ext hp1 e1) (Prod.ext hp2 e2)
      · -- Swapped: q₁.1.2 = q₂.2.2 and q₁.2.2 = q₂.1.2; since decide (q₁.1.2 ≤ q₁.2.2) = decide (q₂.1.2 ≤ q₂.2.2), they must be equal!
        have heq_p : q₁.1.2 = q₁.2.2 := by
          by_cases hle : q₁.1.2 ≤ q₁.2.2
          · have h1 : decide (q₂.1.2 ≤ q₂.2.2) = true := by rw [← hbool, decide_eq_true hle]
            have h2 := of_decide_eq_true h1; omega
          · have h1 : decide (q₂.1.2 ≤ q₂.2.2) = false := by rw [← hbool, decide_eq_false hle]
            have h2 := of_decide_eq_false h1; omega
        exact Prod.ext (Prod.ext hp1 (by omega)) (Prod.ext hp2 (by omega))
  by_cases hΔ0 : Δ = 0
  · have hQ0 : Q.card = 0 := hzero (by
      by_contra hge; push Not at hge
      have h1 : (1 : ℝ) ≤ 4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := (one_le_div (by positivity)).mpr hge
      have h2 : 1 ≤ Δ := Nat.le_floor (by simpa using h1)
      omega)
    rw [hQ0, Nat.cast_zero]; positivity
  -- Δ ≥ 1: Tgt.card = |𝒫 k₁| * |𝒫 k₂| * (2 Δ + 1) * 2 ≤ X₁ * X₂ * (6 Δ) ≤ 24 * X₁^2 * X₂^2 / 2^(S k₁)
  have hP1_card : ((ruzsaPrimes k₁).card : ℝ) ≤ X₁ := by
    have hsub : ruzsaPrimes k₁ ⊆ Finset.Icc 1 (ruzsaP k₁) := fun p hp => by
      simp only [ruzsaPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.2.one_lt.le, hp.1.2⟩
    have h1 : (ruzsaPrimes k₁).card ≤ ruzsaP k₁ := by simpa using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
  have hP2_card : ((ruzsaPrimes k₂).card : ℝ) ≤ X₂ := by
    have hsub : ruzsaPrimes k₂ ⊆ Finset.Icc 1 (ruzsaP k₂) := fun p hp => by
      simp only [ruzsaPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.2.one_lt.le, hp.1.2⟩
    have h1 : (ruzsaPrimes k₂).card ≤ ruzsaP k₂ := by simpa using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
  have hIcc_card : (Finset.Icc (-(Δ : ℤ)) (Δ : ℤ)).card = 2 * Δ + 1 := by
    rw [Int.card_Icc]; omega
  have hTgt_R : (Tgt.card : ℝ) ≤ 8 * X₁ * X₂ * (Δ : ℝ) := by
    have hcard_eq : Tgt.card = (ruzsaPrimes k₁).card * (ruzsaPrimes k₂).card * ((2 * Δ + 1) * 2) := by
      simp only [Tgt, Finset.card_product, hIcc_card, Finset.card_univ, Fintype.card_bool]
    have h2D : (2 * Δ + 1) * 2 ≤ 8 * Δ := by omega
    have hle : Tgt.card ≤ (ruzsaPrimes k₁).card * (ruzsaPrimes k₂).card * (8 * Δ) := by
      rw [hcard_eq]; exact Nat.mul_le_mul_left _ h2D
    have hleR : (Tgt.card : ℝ) ≤ ((ruzsaPrimes k₁).card : ℝ) * ((ruzsaPrimes k₂).card : ℝ) * (8 * (Δ : ℝ)) := by
      have : (Tgt.card : ℝ) ≤ (((ruzsaPrimes k₁).card * (ruzsaPrimes k₂).card * (8 * Δ) : ℕ) : ℝ) := by
        exact_mod_cast hle
      push_cast at this; linarith
    have hmul : ((ruzsaPrimes k₁).card : ℝ) * ((ruzsaPrimes k₂).card : ℝ) ≤ X₁ * X₂ :=
      mul_le_mul hP1_card hP2_card (Nat.cast_nonneg _) (by positivity)
    calc (Tgt.card : ℝ)
        ≤ ((ruzsaPrimes k₁).card : ℝ) * ((ruzsaPrimes k₂).card : ℝ) * (8 * (Δ : ℝ)) := hleR
      _ ≤ (X₁ * X₂) * (8 * (Δ : ℝ)) := mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = 8 * X₁ * X₂ * (Δ : ℝ) := by ring
  have hΔ_le : (Δ : ℝ) ≤ 4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁ := Nat.floor_le (by positivity)
  calc (Q.card : ℝ) ≤ (Tgt.card : ℝ) := by exact_mod_cast hcard_le
    _ ≤ 8 * X₁ * X₂ * (Δ : ℝ) := hTgt_R
    _ ≤ 8 * X₁ * X₂ * (4 * X₁ * X₂ / (2 : ℝ) ^ ruzsaS k₁) :=
        mul_le_mul_of_nonneg_left hΔ_le (by positivity)
    _ = 32 * X₁ ^ 2 * X₂ ^ 2 / (2 : ℝ) ^ ruzsaS k₁ := by ring

-- Harmonic pair sum: ∑_{p' < p in S} 1 / (p - p') ≤ |S| * (1 + log P) for S ⊆ Icc 1 P
private lemma sum_inv_diff_le {S : Finset ℕ} {P : ℕ} (hP : 1 ≤ P) (hS : ∀ p ∈ S, 1 ≤ p ∧ p ≤ P) :
    ∑ q ∈ (S ×ˢ S).filter (fun q => q.2 < q.1), (1 : ℝ) / ((q.1 : ℝ) - (q.2 : ℝ)) ≤
      (S.card : ℝ) * (1 + Real.log (P : ℝ)) := by
  -- Group by q.1 = p ∈ S; for each p, q.1 - q.2 runs injectively over Icc 1 P
  have hgroup : ∑ q ∈ (S ×ˢ S).filter (fun q => q.2 < q.1), (1 : ℝ) / ((q.1 : ℝ) - (q.2 : ℝ)) =
      ∑ p ∈ S, ∑ p' ∈ S.filter (fun p' => p' < p), (1 : ℝ) / ((p : ℝ) - (p' : ℝ)) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun q _ => ⟨q.1, q.2⟩) ?_ ?_ ?_ ?_
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_product] at hq
      simp [hq.1.1, hq.1.2, hq.2]
    · intro q₁ _ q₂ _ h
      rcases q₁ with ⟨a₁, b₁⟩
      rcases q₂ with ⟨a₂, b₂⟩
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      exact Prod.ext h.1 h.2
    · intro s hs; simp only [Finset.mem_sigma, Finset.mem_filter] at hs
      exact ⟨(s.1, s.2), by simp [hs.1, hs.2.1, hs.2.2], rfl⟩
    · intro _ _; rfl
  rw [hgroup]
  calc ∑ p ∈ S, ∑ p' ∈ S.filter (fun p' => p' < p), (1 : ℝ) / ((p : ℝ) - (p' : ℝ))
      ≤ ∑ _p ∈ S, (1 + Real.log (P : ℝ)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hinner : ∑ p' ∈ S.filter (fun p' => p' < p), (1 : ℝ) / ((p : ℝ) - (p' : ℝ)) ≤
            ∑ d ∈ Finset.Icc 1 P, (1 : ℝ) / (d : ℝ) := by
          have himg : ∑ p' ∈ S.filter (fun p' => p' < p), (1 : ℝ) / ((p : ℝ) - (p' : ℝ)) =
              ∑ d ∈ (S.filter (fun p' => p' < p)).image (fun p' => p - p'), (1 : ℝ) / (d : ℝ) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl fun p' hp' => ?_
              have hlt : p' < p := (Finset.mem_filter.mp hp').2
              rw [Nat.cast_sub hlt.le]
            · intro a ha b hb hab
              dsimp only at hab
              have ha' := (Finset.mem_filter.mp ha).2
              have hb' := (Finset.mem_filter.mp hb).2
              omega
          rw [himg]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro d hd
          simp only [Finset.mem_image, Finset.mem_filter] at hd
          obtain ⟨p', ⟨hp'S, hlt⟩, rfl⟩ := hd
          have hp_bd := hS p hp
          simp only [Finset.mem_Icc]; omega
        exact hinner.trans (harmonic_upper_bound P hP)
    _ = (S.card : ℝ) * (1 + Real.log (P : ℝ)) := by simp; ring

/-- **Ruzsa (1998) / Cilleruelo (2012) Standing 28-Year World-Record Infinite Sidon Set (`|A ∩ [1, N]| ≥ N^{√2 - 1 - o(1)}`):**
There exists a single infinite Sidon set `A ⊆ ℕ` whose counting function beats every exponent
strictly below `√2 - 1 ≈ 0.41421356`: for every `ε > 0`, there exists `N₀` such that
`N ^ (√2 - 1 - ε) ≤ |A ∩ [1, N]|` for all `N ≥ N₀`. -/
theorem ppl124_ruzsa_1998_world_record_sidon :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
  classical
  obtain ⟨K₁, hK₁_100, hPrimes_lb⟩ := ruzsaPrimes_card_lower
  -- Choose threshold K₀ ≥ K₁ so that for every k₂ ≥ K₀, the Markov bad-alpha volume is ≤ 2^{-(k₂ - K₀ + 2)}
  -- Key exponent saving: for k₂ ≥ K₀, every bad-event measure sum divided by |𝒫 k₂|/2 is ≤ 2^(-k₂^(3/2)/2) ≤ 2^(-k₂ - 2)
  have hexK₀ : ∃ K₀ : ℕ, K₁ ≤ K₀ ∧ ∀ k₂ : ℕ, K₀ ≤ k₂ →
      16 * (k₂ : ℝ) ^ 2 * ((k₂ : ℝ) * (
        120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
        2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
        20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2))) ≤
      1 / (2 : ℝ) ^ (k₂ + 2) := by
    -- Since k₂^(3/2) ≥ 4 * k₂ for k₂ ≥ 16, 2 * k₂^(3/2) - (k₂ + 2) ≥ k₂^(3/2) ≥ 4 * k₂,
    -- and (1/10) k₂^2 ≥ 2 * k₂ for k₂ ≥ 20; a single exponential 2^(-k₂) beats polynomial factors!
    have hpoly : Tendsto (fun k : ℕ =>
        (16 * (k : ℝ) ^ 3 * (120000 + 2 + 20 * (1 + (k : ℝ) ^ 2))) * (2 : ℝ) ^ (-(k : ℝ)))
        atTop (nhds 0) := by
      have h1 : ∀ k : ℕ, 1 ≤ k →
          (16 * (k : ℝ) ^ 3 * (120000 + 2 + 20 * (1 + (k : ℝ) ^ 2))) * (2 : ℝ) ^ (-(k : ℝ)) ≤
            2000000 * ((k : ℝ) ^ 5 / (Real.exp (Real.log 2 * (k : ℝ)))) := by
        intro k hk
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hk3 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 5 := by
          have : (k : ℝ) ^ 3 * 1 ≤ (k : ℝ) ^ 3 * (k : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
          linarith
        have hpoly_le : 16 * (k : ℝ) ^ 3 * (120000 + 2 + 20 * (1 + (k : ℝ) ^ 2)) ≤ 2000000 * (k : ℝ) ^ 5 := by
          have : 16 * (k : ℝ) ^ 3 * (120000 + 2 + 20 * (1 + (k : ℝ) ^ 2)) =
              1920352 * (k : ℝ) ^ 3 + 320 * (k : ℝ) ^ 5 := by ring
          linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) 5]
        have hexp_eq : (2 : ℝ) ^ (-(k : ℝ)) = 1 / Real.exp (Real.log 2 * (k : ℝ)) := by
          rw [Real.rpow_def_of_pos (by norm_num), mul_neg, Real.exp_neg, one_div]
        rw [hexp_eq, mul_one_div, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right hpoly_le (Real.exp_pos _).le
      -- (k^5 / exp(log 2 * k)) → 0 using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero
      have h2 : Tendsto (fun k : ℕ => (k : ℝ) ^ 5 / Real.exp (Real.log 2 * (k : ℝ))) atTop (nhds 0) := by
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5
        have hcomp : Tendsto (fun k : ℕ => (Real.log 2 * (k : ℝ)) ^ 5 * Real.exp (-(Real.log 2 * (k : ℝ))))
            atTop (nhds 0) :=
          hbase.comp ((tendsto_natCast_atTop_atTop).const_mul_atTop hlog2)
        have hdiv := hcomp.div_const ((Real.log 2) ^ 5)
        rw [zero_div] at hdiv
        refine hdiv.congr fun k => ?_
        rw [mul_pow, Real.exp_neg]
        field_simp
      have h2' : Tendsto (fun k : ℕ => 2000000 * ((k : ℝ) ^ 5 / Real.exp (Real.log 2 * (k : ℝ)))) atTop (nhds 0) := by
        simpa using h2.const_mul 2000000
      refine squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_ h2'
      filter_upwards [eventually_ge_atTop 1] with k hk
      exact h1 k hk
    have hev := (hpoly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).and
      (eventually_ge_atTop (max K₁ 100))
    obtain ⟨K₀, hK₀_small, hK₀_ge⟩ := hev.exists
    -- Actually need the bound for ALL k₂ ≥ K₀, not just K₀! Use Filter.eventually_atTop!
    have hev2 := (hpoly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
    rw [Filter.eventually_atTop] at hev2
    obtain ⟨K₂, hK₂⟩ := hev2
    refine ⟨max K₁ (max K₂ 100), le_max_left _ _, fun k₂ hk₂ => ?_⟩
    have hk₂_K₂ : K₂ ≤ k₂ := (le_max_left _ _).trans ((le_max_right _ _).trans hk₂)
    have hk₂_100 : 100 ≤ k₂ := (le_max_right _ _).trans ((le_max_right _ _).trans hk₂)
    have hsmall : (16 * (k₂ : ℝ) ^ 3 * (120000 + 2 + 20 * (1 + (k₂ : ℝ) ^ 2))) * (2 : ℝ) ^ (-(k₂ : ℝ)) < 1 / 4 :=
      hK₂ k₂ hk₂_K₂
    -- Compare each exponent with -2 * k₂ (since k₂ ≥ 100):
    -- 2 * k₂^(3/2) ≥ 20 * k₂ ≥ 2 * k₂, (1/10) * k₂^2 ≥ 10 * k₂ ≥ 2 * k₂, (1/2) * k₂^2 ≥ 50 * k₂ ≥ 2 * k₂
    have hk2_R : (100 : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hk₂_100
    have hsk2 : (10 : ℝ) ≤ Real.sqrt (k₂ : ℝ) := by
      calc (10 : ℝ) = Real.sqrt (10 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (k₂ : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have hk32 : (k₂ : ℝ) ^ ((3 : ℝ) / 2) = (k₂ : ℝ) * Real.sqrt (k₂ : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (Nat.cast_nonneg k₂) (by norm_num)]
      congr 1; norm_num
    have he1 : -(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2)) ≤ -(2 * (k₂ : ℝ)) := by
      rw [hk32]
      have : 10 * (k₂ : ℝ) ≤ (k₂ : ℝ) * Real.sqrt (k₂ : ℝ) := by
        calc 10 * (k₂ : ℝ) ≤ Real.sqrt (k₂ : ℝ) * (k₂ : ℝ) :=
              mul_le_mul_of_nonneg_right hsk2 (Nat.cast_nonneg _)
          _ = (k₂ : ℝ) * Real.sqrt (k₂ : ℝ) := mul_comm _ _
      linarith
    have he2 : -(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2 ≤ -(2 * (k₂ : ℝ)) := by
      have : 100 * (k₂ : ℝ) ≤ (k₂ : ℝ) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hk2_R (Nat.cast_nonneg _)
      linarith
    have he3 : -(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2 ≤ -(2 * (k₂ : ℝ)) := by linarith
    have hp1 : (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) ≤ (2 : ℝ) ^ (-(2 * (k₂ : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
    have hp2 : (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) ≤ (2 : ℝ) ^ (-(2 * (k₂ : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
    have hp3 : (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2) ≤ (2 : ℝ) ^ (-(2 * (k₂ : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he3
    have hsplit_pow : (2 : ℝ) ^ (-(2 * (k₂ : ℝ))) = (2 : ℝ) ^ (-(k₂ : ℝ)) * (2 : ℝ) ^ (-(k₂ : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have hpow_nat : (2 : ℝ) ^ (-(k₂ : ℝ)) / 4 = 1 / (2 : ℝ) ^ (k₂ + 2) := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_add]
      norm_num; ring
    have hsum_le :
        120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
        2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
        20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2) ≤
        (120000 + 2 + 20 * (1 + (k₂ : ℝ) ^ 2)) * (2 : ℝ) ^ (-(2 * (k₂ : ℝ))) := by
      have h1 := mul_le_mul_of_nonneg_left hp1 (by norm_num : (0 : ℝ) ≤ 120000)
      have h2 := mul_le_mul_of_nonneg_left hp2 (by norm_num : (0 : ℝ) ≤ 2)
      have h3 := mul_le_mul_of_nonneg_left hp3 (by positivity : (0 : ℝ) ≤ 20 * (1 + (k₂ : ℝ) ^ 2))
      linarith
    calc 16 * (k₂ : ℝ) ^ 2 * ((k₂ : ℝ) * (
          120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
          2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
          20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2)))
        ≤ 16 * (k₂ : ℝ) ^ 2 * ((k₂ : ℝ) *
            ((120000 + 2 + 20 * (1 + (k₂ : ℝ) ^ 2)) * (2 : ℝ) ^ (-(2 * (k₂ : ℝ))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_le (Nat.cast_nonneg _)) (by positivity)
      _ = ((16 * (k₂ : ℝ) ^ 3 * (120000 + 2 + 20 * (1 + (k₂ : ℝ) ^ 2))) * (2 : ℝ) ^ (-(k₂ : ℝ))) *
            (2 : ℝ) ^ (-(k₂ : ℝ)) := by rw [hsplit_pow]; ring
      _ ≤ (1 / 4) * (2 : ℝ) ^ (-(k₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right hsmall.le (by positivity)
      _ = 1 / (2 : ℝ) ^ (k₂ + 2) := by rw [← hpow_nat]; ring
  obtain ⟨K₀, hK₀_ge, hK₀_bd⟩ := hexK₀
  -- Define colliding predicate on level k₂ ≥ K₀
  let IsColl : ℝ → ℕ → ℕ → Prop := fun α k₂ p₂ =>
    ∃ k₁ ∈ Finset.Ico K₀ k₂, ∃ p₁ ∈ ruzsaPrimes k₁, ∃ p'₁ ∈ ruzsaPrimes k₁, ∃ p'₂ ∈ ruzsaPrimes k₂,
      p₂ ≠ p'₂ ∧ ruzsaCode α k₁ p₁ + ruzsaCode α k₂ p₂ = ruzsaCode α k₁ p'₁ + ruzsaCode α k₂ p'₂
  let BadAlpha : ℕ → Set ℝ := fun k₂ =>
    {α : ℝ | α ∈ Set.Icc (1 : ℝ) 2 ∧
      (ruzsaPrimes k₂).card ≤ 2 * ((ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂)).card}
  -- Bound volume (BadAlpha k₂) ≤ ENNReal.ofReal (1 / 2^(k₂ + 2)) for every k₂ ≥ K₀
  have hBad_vol : ∀ k₂ : ℕ, K₀ ≤ k₂ → volume (BadAlpha k₂) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ (k₂ + 2)) := by
    intro k₂ hk₂
    have hk₂_100 : 100 ≤ k₂ := hK₁_100.trans (hK₀_ge.trans hk₂)
    set X₂ : ℝ := (2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2)
    -- Define the explicit measurable covering sets for Subcase 2a and Subcase 2b
    let nearSet : ℕ → ℕ → ℕ → Set ℝ := fun k₁ p₂ p'₂ =>
      Set.Icc (1 : ℝ) 2 ∩ {α : ℝ | ∃ m : ℤ,
        |(2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)) * α - (m : ℝ)| <
          1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)}
    have hnear_meas : ∀ k₁ p₂ p'₂, MeasurableSet (nearSet k₁ p₂ p'₂) := by
      intro k₁ p₂ p'₂
      refine measurableSet_Icc.inter ?_
      have heq : {α : ℝ | ∃ m : ℤ,
          |(2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)) * α - (m : ℝ)| <
            1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)} =
          ⋃ m : ℤ, {α : ℝ |
            |(2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)) * α - (m : ℝ)| <
              1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)} := by
        ext α; simp
      rw [heq]
      refine MeasurableSet.iUnion fun m => ?_
      have hcont : Continuous (fun α : ℝ =>
          |(2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)) * α - (m : ℝ)|) := by
        continuity
      exact isOpen_lt hcont continuous_const |>.measurableSet
    -- For each k₁ ∈ Ico K₀ k₂, define measurable indicator sum g_{k₁}(α)
    let Q2a : ℕ → Finset ((ℕ × ℕ) × (ℕ × ℕ)) := fun k₁ =>
      ((ruzsaPrimes k₁ ×ˢ ruzsaPrimes k₁) ×ˢ (ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂)).filter
        (fun q => q.2.1 ≠ q.2.2 ∧ q.1.1 * q.2.1 ≠ q.1.2 * q.2.2 ∧
          |Real.logb 2 ((q.1.1 * q.2.1 : ℕ) : ℝ) - Real.logb 2 ((q.1.2 * q.2.2 : ℕ) : ℝ)| <
            2 / (2 : ℝ) ^ ruzsaS k₁)
    let P2b : Finset (ℕ × ℕ) :=
      (ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂).filter (fun q => q.2 < q.1)
    let g_k1 : ℕ → ℝ → ℝ≥0∞ := fun k₁ α =>
      if ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 ≤ (k₁ : ℝ) ^ 2 then
        ∑ q ∈ Q2a k₁, (nearSet k₁ q.2.1 q.2.2).indicator (fun _ => (1 : ℝ≥0∞)) α
      else
        2 * ∑ q ∈ P2b, (nearSet k₁ q.1 q.2).indicator (fun _ => (1 : ℝ≥0∞)) α
    let G : ℝ → ℝ≥0∞ := fun α => ∑ k₁ ∈ Finset.Ico K₀ k₂, g_k1 k₁ α
    have hG_meas : Measurable G := by
      refine Finset.measurable_sum _ fun k₁ _ => ?_
      dsimp only [g_k1]
      split_ifs
      · exact Finset.measurable_sum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.2.1 q.2.2)
      · exact measurable_const.mul (Finset.measurable_sum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.1 q.2))
    -- Pointwise domination: for α ∈ [1, 2], #{p₂ ∈ 𝒫 k₂ | IsColl α k₂ p₂} ≤ G α
    have hG_dom : ∀ α ∈ Set.Icc (1 : ℝ) 2,
        (((ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂)).card : ℝ≥0∞) ≤ G α := by
      intro α hα
      -- Each colliding p₂ is witnessed by some k₁ ∈ Ico K₀ k₂; count ≤ ∑_{k₁} #{p₂ colliding at k₁}
      let collAt : ℕ → Finset ℕ := fun k₁ =>
        (ruzsaPrimes k₂).filter (fun p₂ =>
          ∃ p₁ ∈ ruzsaPrimes k₁, ∃ p'₁ ∈ ruzsaPrimes k₁, ∃ p'₂ ∈ ruzsaPrimes k₂,
            p₂ ≠ p'₂ ∧ ruzsaCode α k₁ p₁ + ruzsaCode α k₂ p₂ = ruzsaCode α k₁ p'₁ + ruzsaCode α k₂ p'₂)
      have hsub_u : (ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂) ⊆
          (Finset.Ico K₀ k₂).biUnion collAt := by
        intro p₂ hp₂
        simp only [Finset.mem_filter, IsColl] at hp₂
        obtain ⟨hp₂P, k₁, hk₁, p₁, hp1, p'₁, hp'1, p'₂, hp'2, hne, heq⟩ := hp₂
        rw [Finset.mem_biUnion]
        exact ⟨k₁, hk₁, Finset.mem_filter.mpr ⟨hp₂P, p₁, hp1, p'₁, hp'1, p'₂, hp'2, hne, heq⟩⟩
      have hcard_sum : ((ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂)).card ≤
          ∑ k₁ ∈ Finset.Ico K₀ k₂, (collAt k₁).card :=
        (Finset.card_le_card hsub_u).trans Finset.card_biUnion_le
      calc (((ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂)).card : ℝ≥0∞)
          ≤ ((∑ k₁ ∈ Finset.Ico K₀ k₂, (collAt k₁).card : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard_sum
        _ = ∑ k₁ ∈ Finset.Ico K₀ k₂, ((collAt k₁).card : ℝ≥0∞) := by push_cast; rfl
        _ ≤ ∑ k₁ ∈ Finset.Ico K₀ k₂, g_k1 k₁ α := by
            refine Finset.sum_le_sum fun k₁ hk₁ => ?_
            have hk₁_lt : k₁ < k₂ := (Finset.mem_Ico.mp hk₁).2
            have hk₁_25 : 25 ≤ k₁ := by have := (Finset.mem_Ico.mp hk₁).1; omega
            dsimp only [g_k1]
            split_ifs with hsubcase
            · -- Subcase 2a: each p₂ ∈ collAt k₁ produces at least one q ∈ Q2a k₁ with q.2.1 = p₂ and α ∈ nearSet
              have hle_sum : ((collAt k₁).card : ℝ≥0∞) ≤
                  ∑ q ∈ Q2a k₁, (nearSet k₁ q.2.1 q.2.2).indicator (fun _ => (1 : ℝ≥0∞)) α := by
                have hnat : (collAt k₁).card ≤ (Q2a k₁ |>.filter (fun q => α ∈ nearSet k₁ q.2.1 q.2.2)).card := by
                  have hsub_img : collAt k₁ ⊆ (Q2a k₁ |>.filter (fun q => α ∈ nearSet k₁ q.2.1 q.2.2)).image (fun q => q.2.1) := by
                    intro p₂ hp₂
                    simp only [collAt, Finset.mem_filter] at hp₂
                    obtain ⟨hp₂P, p₁, hp1, p'₁, hp'1, p'₂, hp'2, hne, heq⟩ := hp₂
                    have hdec := ruzsaCode_decode hα hk₁_25 hk₁_lt.le hk₁_25 hk₁_lt.le hp1 hp₂P hp'1 hp'2 heq
                    have hprod_ne : p₁ * p₂ ≠ p'₁ * p'₂ := by
                      intro hpeq
                      rcases prime_mul_eq_iff (Finset.mem_filter.mp hp1).2 (Finset.mem_filter.mp hp₂P).2
                        (Finset.mem_filter.mp hp'1).2 (Finset.mem_filter.mp hp'2).2 hpeq with ⟨_, e2⟩ | ⟨e1, _⟩
                      · exact hne e2
                      · -- p₁ ∈ 𝒫 k₁ and p'₂ ∈ 𝒫 k₂ with k₁ < k₂ are disjoint!
                        have hle1 : p₁ ≤ ruzsaP k₁ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp1).1).2
                        have hgt2 : ruzsaP (k₂ - 1) < p'₂ := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp'2).1).1
                        have hmono : ruzsaP k₁ ≤ ruzsaP (k₂ - 1) := by
                          apply Nat.floor_mono
                          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
                          have h1 := ruzsaTheta_mono (k₁ := k₁) (k₂ := k₂ - 1) (by omega) (by omega)
                          have h2 : (k₁ : ℝ) ^ 2 ≤ ((k₂ - 1 : ℕ) : ℝ) ^ 2 :=
                            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show k₁ ≤ k₂ - 1 by omega)) 2
                          exact mul_le_mul h1 h2 (sq_nonneg _) (by linarith [(ruzsaTheta_bounds (k := k₂ - 1) (by omega)).1])
                        omega
                    rw [Finset.mem_image]
                    refine ⟨((p₁, p'₁), (p₂, p'₂)), ?_, rfl⟩
                    simp only [Q2a, Finset.mem_filter, Finset.mem_product]
                    refine ⟨⟨⟨⟨hp1, hp'1⟩, ⟨hp₂P, hp'2⟩⟩, hne, hprod_ne, hdec.2.1⟩, hα, ?_⟩
                    obtain ⟨m, hm⟩ := hdec.2.2 hk₁_lt
                    refine ⟨m, ?_⟩
                    convert hm using 2; ring
                  exact (Finset.card_le_card hsub_img).trans Finset.card_image_le
                calc ((collAt k₁).card : ℝ≥0∞)
                    ≤ ((Q2a k₁ |>.filter (fun q => α ∈ nearSet k₁ q.2.1 q.2.2)).card : ℝ≥0∞) := by exact_mod_cast hnat
                  _ = ∑ q ∈ Q2a k₁, (nearSet k₁ q.2.1 q.2.2).indicator (fun _ => (1 : ℝ≥0∞)) α := by
                      rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
              exact hle_sum
            · -- Subcase 2b: each p₂ ∈ collAt k₁ has some p'₂ ≠ p₂ with α ∈ nearSet k₁ p₂ p'₂ (so either (p₂, p'₂) or (p'₂, p₂) is in P2b!)
              have hnat : (collAt k₁).card ≤ 2 * (P2b.filter (fun q => α ∈ nearSet k₁ q.1 q.2)).card := by
                let F := P2b.filter (fun q => α ∈ nearSet k₁ q.1 q.2)
                have hsub_u : collAt k₁ ⊆ F.image Prod.fst ∪ F.image Prod.snd := by
                  intro p₂ hp₂
                  simp only [collAt, Finset.mem_filter] at hp₂
                  obtain ⟨hp₂P, p₁, hp1, p'₁, hp'1, p'₂, hp'2, hne, heq⟩ := hp₂
                  have hdec := ruzsaCode_decode hα hk₁_25 hk₁_lt.le hk₁_25 hk₁_lt.le hp1 hp₂P hp'1 hp'2 heq
                  obtain ⟨m, hm⟩ := hdec.2.2 hk₁_lt
                  rcases lt_or_gt_of_ne hne with hlt | hgt
                  · apply Finset.mem_union_right
                    rw [Finset.mem_image]
                    refine ⟨(p'₂, p₂), ?_, rfl⟩
                    simp only [F, P2b, Finset.mem_filter, Finset.mem_product]
                    refine ⟨⟨⟨hp'2, hp₂P⟩, hlt⟩, hα, -m, ?_⟩
                    have hneg : (2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p'₂ : ℝ) - Real.logb 2 (p₂ : ℝ)) * α - ((-m : ℤ) : ℝ) =
                        -((2 : ℝ) ^ ruzsaS k₁ * (α * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ))) - (m : ℝ)) := by
                      push_cast; ring
                    rw [hneg, abs_neg]; exact hm
                  · apply Finset.mem_union_left
                    rw [Finset.mem_image]
                    refine ⟨(p₂, p'₂), ?_, rfl⟩
                    simp only [F, P2b, Finset.mem_filter, Finset.mem_product]
                    refine ⟨⟨⟨hp₂P, hp'2⟩, hgt⟩, hα, m, ?_⟩
                    convert hm using 2; ring
                calc (collAt k₁).card ≤ (F.image Prod.fst ∪ F.image Prod.snd).card := Finset.card_le_card hsub_u
                  _ ≤ (F.image Prod.fst).card + (F.image Prod.snd).card := Finset.card_union_le _ _
                  _ ≤ F.card + F.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
                  _ = 2 * F.card := by ring
              calc ((collAt k₁).card : ℝ≥0∞)
                  ≤ ((2 * (P2b.filter (fun q => α ∈ nearSet k₁ q.1 q.2)).card : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
                _ = 2 * ∑ q ∈ P2b, (nearSet k₁ q.1 q.2).indicator (fun _ => (1 : ℝ≥0∞)) α := by
                    push_cast
                    rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    -- Bound the lintegral ∫⁻ α, G α ∂volume
    have hlint_k1 : ∀ k₁ ∈ Finset.Ico K₀ k₂,
        ∫⁻ α, g_k1 k₁ α ∂volume ≤
          ENNReal.ofReal (X₂ * (
            120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
            2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
            20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2))) := by
      intro k₁ hk₁
      have hk₁_ge : K₀ ≤ k₁ := (Finset.mem_Ico.mp hk₁).1
      have hk₁_lt : k₁ < k₂ := (Finset.mem_Ico.mp hk₁).2
      have hk₁_100 : 100 ≤ k₁ := hK₁_100.trans (hK₀_ge.trans hk₁_ge)
      have hδ_half : 1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) ≤ 1 / 2 := by
        have hdiff_ge1 : 1 ≤ ruzsaS k₂ - ruzsaS k₁ := by
          simp only [ruzsaS]
          have : k₁ ^ 2 < k₂ ^ 2 := Nat.pow_lt_pow_left hk₁_lt (by norm_num)
          omega
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdiff_ge1)
      have hnear_vol : ∀ p₂ ∈ ruzsaPrimes k₂, ∀ p'₂ ∈ ruzsaPrimes k₂, p₂ ≠ p'₂ →
          volume (nearSet k₁ p₂ p'₂) ≤
            ENNReal.ofReal (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) *
              (1 + 10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * (|(p₂ : ℝ) - (p'₂ : ℝ)|)))) := by
        intro p₂ hp2 p'₂ hp'2 hne
        set L := (2 : ℝ) ^ ruzsaS k₁ * |Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)|
        have hlog_ge : |(p₂ : ℝ) - (p'₂ : ℝ)| / (2 * X₂) ≤ |Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)| := by
          have hp2_le : (p₂ : ℝ) ≤ X₂ :=
            (Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp2).1).2).trans (Nat.floor_le (by positivity))
          have hp'2_le : (p'₂ : ℝ) ≤ X₂ :=
            (Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp'2).1).2).trans (Nat.floor_le (by positivity))
          have hp2_pos : (0 : ℝ) < (p₂ : ℝ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hp2).2.pos
          have hp'2_pos : (0 : ℝ) < (p'₂ : ℝ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hp'2).2.pos
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [abs_sub_comm (p₂ : ℝ), abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hlt)),
                abs_sub_comm (Real.logb 2 _)]
            have h1 := logb2_sub_ge hp2_pos (Nat.cast_lt.mpr hlt)
            have h2 : ((p'₂ : ℝ) - (p₂ : ℝ)) / (2 * X₂) ≤ ((p'₂ : ℝ) - (p₂ : ℝ)) / (2 * (p'₂ : ℝ)) :=
              div_le_div_of_nonneg_left (sub_nonneg.mpr (Nat.cast_le.mpr hlt.le)) (by positivity) (by linarith)
            exact (h2.trans h1).trans (le_abs_self _)
          · rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
            have h1 := logb2_sub_ge hp'2_pos (Nat.cast_lt.mpr hgt)
            have h2 : ((p₂ : ℝ) - (p'₂ : ℝ)) / (2 * X₂) ≤ ((p₂ : ℝ) - (p'₂ : ℝ)) / (2 * (p₂ : ℝ)) :=
              div_le_div_of_nonneg_left (sub_nonneg.mpr (Nat.cast_le.mpr hgt.le)) (by positivity) (by linarith)
            exact (h2.trans h1).trans (le_abs_self _)
        have habs_diff_pos : 0 < |(p₂ : ℝ) - (p'₂ : ℝ)| :=
          abs_pos.mpr (sub_ne_zero.mpr (Nat.cast_injective.ne hne))
        have hL_ge : (2 : ℝ) ^ ruzsaS k₁ * |(p₂ : ℝ) - (p'₂ : ℝ)| / (2 * X₂) ≤ L := by
          dsimp only [L]
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hlog_ge (by positivity)
        have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_ge
        have hsub : nearSet k₁ p₂ p'₂ ⊆
            {α : ℝ | α ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ m : ℤ, |L * α - (m : ℝ)| < 1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)} := by
          intro α ⟨hα, m, hm⟩
          refine ⟨hα, ?_⟩
          by_cases hsign : 0 ≤ Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)
          · refine ⟨m, ?_⟩
            have hLeq : L = (2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)) := by
              dsimp only [L]; rw [abs_of_nonneg hsign]
            rwa [hLeq]
          · push Not at hsign
            refine ⟨-m, ?_⟩
            have hLeq : L = -((2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ))) := by
              dsimp only [L]; rw [abs_of_neg hsign]; ring
            have heq' : L * α - ((-m : ℤ) : ℝ) =
                -((2 : ℝ) ^ ruzsaS k₁ * (Real.logb 2 (p₂ : ℝ) - Real.logb 2 (p'₂ : ℝ)) * α - (m : ℝ)) := by
              rw [hLeq]; push_cast; ring
            rw [heq', abs_neg]; exact hm
        calc volume (nearSet k₁ p₂ p'₂)
            ≤ volume {α : ℝ | α ∈ Set.Icc (1 : ℝ) 2 ∧ ∃ m : ℤ, |L * α - (m : ℝ)| < 1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)} :=
              measure_mono hsub
          _ ≤ ENNReal.ofReal (2 * (1 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) * (1 + 5 / L)) :=
              volume_near_int_le hL_pos (by positivity) hδ_half
          _ ≤ ENNReal.ofReal (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) *
                (1 + 10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * |(p₂ : ℝ) - (p'₂ : ℝ)|))) := by
              apply ENNReal.ofReal_le_ofReal
              rw [mul_one_div]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hdiv_le : 5 / L ≤ 10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * |(p₂ : ℝ) - (p'₂ : ℝ)|) := by
                have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 5) (by positivity) hL_ge
                have h2 : 5 / ((2 : ℝ) ^ ruzsaS k₁ * |(p₂ : ℝ) - (p'₂ : ℝ)| / (2 * X₂)) =
                    10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * |(p₂ : ℝ) - (p'₂ : ℝ)|) := by field_simp; ring
                linarith
              linarith
      dsimp only [g_k1]
      split_ifs with hsubcase
      · -- Subcase 2a: ruzsaTheta k₂ * k₂^2 ≤ k₁^2 ⇒ X₂ ≤ 2^(S k₁)
        rw [lintegral_finsetSum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.2.1 q.2.2)]
        have hX2_le : X₂ ≤ (2 : ℝ) ^ ruzsaS k₁ := by
          dsimp only [X₂, ruzsaS]
          rw [← Real.rpow_natCast (2 : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; exact hsubcase)
        have hterm_le : ∀ q ∈ Q2a k₁,
            ∫⁻ α, (nearSet k₁ q.2.1 q.2.2).indicator (fun _ => (1 : ℝ≥0∞)) α ∂volume ≤
              ENNReal.ofReal (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) := by
          intro q hq
          have hone : (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 := rfl
          rw [hone, lintegral_indicator_one (hnear_meas k₁ q.2.1 q.2.2)]
          simp only [Q2a, Finset.mem_filter, Finset.mem_product] at hq
          have hv := hnear_vol q.2.1 hq.1.2.1 q.2.2 hq.1.2.2 hq.2.1
          have hdiff1 : (1 : ℝ) ≤ |(q.2.1 : ℝ) - (q.2.2 : ℝ)| := by
            have hneZ : (q.2.1 : ℤ) - (q.2.2 : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq.2.1)
            have h1Z : (1 : ℤ) ≤ |(q.2.1 : ℤ) - (q.2.2 : ℤ)| := Int.one_le_abs hneZ
            have hR : (1 : ℝ) ≤ (|(q.2.1 : ℤ) - (q.2.2 : ℤ)| : ℝ) := by exact_mod_cast h1Z
            simpa using hR
          have hfrac_le : 10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * |(q.2.1 : ℝ) - (q.2.2 : ℝ)|) ≤ 10 := by
            rw [div_le_iff₀ (by positivity)]
            have h1 : X₂ ≤ (2 : ℝ) ^ ruzsaS k₁ * |(q.2.1 : ℝ) - (q.2.2 : ℝ)| := by
              calc X₂ ≤ (2 : ℝ) ^ ruzsaS k₁ := hX2_le
                _ = (2 : ℝ) ^ ruzsaS k₁ * 1 := (mul_one _).symm
                _ ≤ (2 : ℝ) ^ ruzsaS k₁ * |(q.2.1 : ℝ) - (q.2.2 : ℝ)| :=
                    mul_le_mul_of_nonneg_left hdiff1 (by positivity)
            linarith
          refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
          have h11 : 2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) *
              (1 + 10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * |(q.2.1 : ℝ) - (q.2.2 : ℝ)|)) ≤
              2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) * 11 :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h22 : 2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) * 11 =
              22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) := by ring
          linarith
        have hsum_bd : ∑ q ∈ Q2a k₁, ∫⁻ α, (nearSet k₁ q.2.1 q.2.2).indicator (fun _ => (1 : ℝ≥0∞)) α ∂volume ≤
            ENNReal.ofReal ((Q2a k₁).card * (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))) := by
          calc ∑ q ∈ Q2a k₁, ∫⁻ α, (nearSet k₁ q.2.1 q.2.2).indicator (fun _ => (1 : ℝ≥0∞)) α ∂volume
              ≤ ∑ _q ∈ Q2a k₁, ENNReal.ofReal (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) :=
                Finset.sum_le_sum hterm_le
            _ = ((Q2a k₁).card : ℝ≥0∞) * ENNReal.ofReal (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) := by simp
            _ = ENNReal.ofReal ((Q2a k₁).card * (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))) := by
                rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        refine hsum_bd.trans (ENNReal.ofReal_le_ofReal ?_)
        have ⟨hQ_bd, hQ_zero⟩ := ruzsa_quadruple_card_bound (k₁ := k₁) (k₂ := k₂) (by omega) hk₁_lt
        set X₁ : ℝ := (2 : ℝ) ^ (ruzsaTheta k₁ * (k₁ : ℝ) ^ 2)
        by_cases hzero : 4 * X₁ * X₂ < (2 : ℝ) ^ ruzsaS k₁
        · have h0 := hQ_zero hzero
          change (Q2a k₁).card = 0 at h0
          rw [h0, Nat.cast_zero, zero_mul]
          positivity
        · push Not at hzero
          -- 2^(S k₁) ≤ 4 * X₁ * X₂ ⇒ k₁^2 ≤ 2 + θ k₂ * (k₁^2 + k₂^2)
          have hθ₂ := ruzsaTheta_bounds (k := k₂) (by omega)
          have hθ_mono := ruzsaTheta_mono (k₁ := k₁) (k₂ := k₂) (by omega) hk₁_lt.le
          have hk1_ub : (1 - ruzsaTheta k₂) * (k₁ : ℝ) ^ 2 ≤ 2 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 := by
            have hlog_le : ((k₁ ^ 2 : ℕ) : ℝ) ≤ 2 + ruzsaTheta k₁ * (k₁ : ℝ) ^ 2 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 := by
              have hrew : 4 * X₁ * X₂ = (2 : ℝ) ^ (2 + ruzsaTheta k₁ * (k₁ : ℝ) ^ 2 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2) := by
                have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
                dsimp only [X₁, X₂]
                rw [h4, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
              rw [hrew, ruzsaS, ← Real.rpow_natCast] at hzero
              exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hzero
            push_cast at hlog_le
            have h1 : ruzsaTheta k₁ * (k₁ : ℝ) ^ 2 ≤ ruzsaTheta k₂ * (k₁ : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hθ_mono (sq_nonneg _)
            linarith
          -- Core Ruzsa √2 - 1 exponent algebra!
          -- 2 * θ k₁ * k₁^2 + θ k₂ * k₂^2 - k₂^2 ≤ 8 - 2 * k₂^(3/2)
          have hexp_save : 2 * (ruzsaTheta k₁ * (k₁ : ℝ) ^ 2) + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 - (k₂ : ℝ) ^ 2 ≤
              7 - 2 * (k₂ : ℝ) ^ ((3 : ℝ) / 2) := by
            have h1mθ_pos : 0 < 1 - ruzsaTheta k₂ := by
              have hsqrt2_lt : Real.sqrt 2 < 1.5 := by
                have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.5 ^ 2)
                rwa [Real.sqrt_sq (by norm_num)] at this
              linarith [hθ₂.2]
            have h1 : 2 * ruzsaTheta k₁ * (k₁ : ℝ) ^ 2 ≤ 2 * ruzsaTheta k₂ * (k₁ : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
            have hk1_div : (k₁ : ℝ) ^ 2 ≤ (2 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2) / (1 - ruzsaTheta k₂) :=
              (le_div_iff₀ h1mθ_pos).mpr (by linarith)
            have hθ₂_pos : 0 < ruzsaTheta k₂ := by linarith [hθ₂.1]
            have h2 : 2 * ruzsaTheta k₂ * (k₁ : ℝ) ^ 2 + (ruzsaTheta k₂ - 1) * (k₂ : ℝ) ^ 2 ≤
                4 * ruzsaTheta k₂ / (1 - ruzsaTheta k₂) -
                ((1 - 2 * ruzsaTheta k₂ - (ruzsaTheta k₂) ^ 2) / (1 - ruzsaTheta k₂)) * (k₂ : ℝ) ^ 2 := by
              have hm := mul_le_mul_of_nonneg_left hk1_div (by positivity : 0 ≤ 2 * ruzsaTheta k₂)
              have halg : 2 * ruzsaTheta k₂ * ((2 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2) / (1 - ruzsaTheta k₂)) +
                  (ruzsaTheta k₂ - 1) * (k₂ : ℝ) ^ 2 =
                  4 * ruzsaTheta k₂ / (1 - ruzsaTheta k₂) -
                  ((1 - 2 * ruzsaTheta k₂ - (ruzsaTheta k₂) ^ 2) / (1 - ruzsaTheta k₂)) * (k₂ : ℝ) ^ 2 := by
                field_simp; ring
              linarith
            -- Check 4 * θ / (1 - θ) ≤ 7 (since θ < 0.5 ⇒ 4θ/(1-θ) < 4 ≤ 7!)
            have hconst7 : 4 * ruzsaTheta k₂ / (1 - ruzsaTheta k₂) ≤ 7 := by
              rw [div_le_iff₀ h1mθ_pos]
              have hsqrt2_lt : Real.sqrt 2 < 1.5 := by
                have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.5 ^ 2)
                rwa [Real.sqrt_sq (by norm_num)] at this
              linarith [hθ₂.2]
            -- Check (1 - 2θ - θ^2) / (1 - θ) ≥ 2 / √k₂!
            -- Since θ = √2 - 1 - η with η = 1/√k₂ ≤ 1/10:
            -- 1 - 2θ - θ^2 = 2√2 * η - η^2 ≥ 2.7 * η, and 1 - θ ≤ 1, so ratio ≥ 2.7 * η ≥ 2 / √k₂!
            have hpoly_lb : 2 / Real.sqrt (k₂ : ℝ) ≤ (1 - 2 * ruzsaTheta k₂ - (ruzsaTheta k₂) ^ 2) / (1 - ruzsaTheta k₂) := by
              set η : ℝ := 1 / Real.sqrt (k₂ : ℝ)
              have hsk2_ge : (10 : ℝ) ≤ Real.sqrt (k₂ : ℝ) := by
                calc (10 : ℝ) = Real.sqrt (10 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
                  _ ≤ Real.sqrt (k₂ : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hk₂_100)
              have hη_pos : 0 < η := by positivity
              have hη_le : η ≤ 1 / 10 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsk2_ge
              have hident : 1 - 2 * ruzsaTheta k₂ - (ruzsaTheta k₂) ^ 2 = 2 * Real.sqrt 2 * η - η ^ 2 := by
                dsimp only [ruzsaTheta, η]
                have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
                nlinarith
              have hsqrt2_gt : (1.4 : ℝ) < Real.sqrt 2 := by
                have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.4 ^ 2) (by norm_num : (1.4 : ℝ) ^ 2 < 2)
                rwa [Real.sqrt_sq (by norm_num)] at this
              have hnum_ge : 2 * η ≤ 2 * Real.sqrt 2 * η - η ^ 2 := by
                have h1' : η ^ 2 ≤ (1 / 10) * η := by
                  rw [sq]; exact mul_le_mul_of_nonneg_right hη_le hη_pos.le
                have h2' : 2.8 * η ≤ 2 * Real.sqrt 2 * η :=
                  mul_le_mul_of_nonneg_right (by linarith) hη_pos.le
                linarith
              rw [le_div_iff₀ h1mθ_pos, hident]
              have h1mθ_le1 : 1 - ruzsaTheta k₂ ≤ 1 := by linarith
              calc (2 / Real.sqrt (k₂ : ℝ)) * (1 - ruzsaTheta k₂)
                  = 2 * η * (1 - ruzsaTheta k₂) := by dsimp only [η]; ring
                _ ≤ 2 * η * 1 := mul_le_mul_of_nonneg_left h1mθ_le1 (by positivity)
                _ = 2 * η := mul_one _
                _ ≤ 2 * Real.sqrt 2 * η - η ^ 2 := hnum_ge
            have hk32 : (2 / Real.sqrt (k₂ : ℝ)) * (k₂ : ℝ) ^ 2 = 2 * (k₂ : ℝ) ^ ((3 : ℝ) / 2) := by
              have hsk_pos : 0 < Real.sqrt (k₂ : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
              have hsq : Real.sqrt (k₂ : ℝ) * Real.sqrt (k₂ : ℝ) = (k₂ : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
              have hrp : (k₂ : ℝ) ^ ((3 : ℝ) / 2) = (k₂ : ℝ) * Real.sqrt (k₂ : ℝ) := by
                rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (Nat.cast_nonneg k₂) (by norm_num)]
                congr 1; norm_num
              rw [hrp, div_mul_eq_mul_div, div_eq_iff hsk_pos.ne']
              calc 2 * (k₂ : ℝ) ^ 2 = 2 * (k₂ : ℝ) * (Real.sqrt (k₂ : ℝ) * Real.sqrt (k₂ : ℝ)) := by rw [hsq]; ring
                _ = 2 * ((k₂ : ℝ) * Real.sqrt (k₂ : ℝ)) * Real.sqrt (k₂ : ℝ) := by ring
            have h3 := mul_le_mul_of_nonneg_right hpoly_lb (sq_nonneg (k₂ : ℝ))
            rw [hk32] at h3
            linarith
          -- Combine Q2a.card * (22 / 2^(S k₂ - S k₁)) ≤ 704 * X₁^2 * X₂^2 / 2^(S k₂) ≤ 704 * 128 * X₂ * 2^(-2 k₂^(3/2))
          have hpow_cancel : (2 : ℝ) ^ ruzsaS k₁ * (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) = (2 : ℝ) ^ ruzsaS k₂ := by
            rw [← pow_add]
            congr 1
            simp only [ruzsaS]
            exact Nat.add_sub_of_le (Nat.pow_le_pow_left hk₁_lt.le 2)
          have hmain_prod : ((Q2a k₁).card : ℝ) * (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) ≤
              704 * (X₁ ^ 2 * X₂ ^ 2 / (2 : ℝ) ^ ruzsaS k₂) := by
            have hmul := mul_le_mul_of_nonneg_right hQ_bd (by positivity : (0 : ℝ) ≤ 22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))
            have hrew : 32 * X₁ ^ 2 * X₂ ^ 2 / (2 : ℝ) ^ ruzsaS k₁ * (22 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) =
                704 * (X₁ ^ 2 * X₂ ^ 2 / (2 : ℝ) ^ ruzsaS k₂) := by
              rw [← hpow_cancel]; field_simp; ring
            linarith
          have hX12_bd : X₁ ^ 2 * X₂ / (2 : ℝ) ^ ruzsaS k₂ ≤ 128 * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2)) := by
            have hrew : X₁ ^ 2 * X₂ / (2 : ℝ) ^ ruzsaS k₂ =
                (2 : ℝ) ^ (2 * (ruzsaTheta k₁ * (k₁ : ℝ) ^ 2) + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 - (k₂ : ℝ) ^ 2) := by
              dsimp only [X₁, X₂, ruzsaS]
              rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num),
                  ← Real.rpow_add (by norm_num), ← Real.rpow_natCast (2 : ℝ),
                  ← Real.rpow_sub (by norm_num)]
              congr 1; push_cast; ring
            rw [hrew]
            have h128 : (128 : ℝ) * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2)) =
                (2 : ℝ) ^ (7 - 2 * (k₂ : ℝ) ^ ((3 : ℝ) / 2)) := by
              have h7 : (128 : ℝ) = (2 : ℝ) ^ (7 : ℝ) := by norm_num
              rw [h7, ← Real.rpow_add (by norm_num)]; congr 1; ring
            rw [h128]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_save
          have h704 : 704 * (X₁ ^ 2 * X₂ ^ 2 / (2 : ℝ) ^ ruzsaS k₂) ≤
              X₂ * (120000 * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2))) := by
            have h1 : X₁ ^ 2 * X₂ ^ 2 / (2 : ℝ) ^ ruzsaS k₂ = X₂ * (X₁ ^ 2 * X₂ / (2 : ℝ) ^ ruzsaS k₂) := by ring
            rw [h1]
            have h2 := mul_le_mul_of_nonneg_left hX12_bd (by positivity : 0 ≤ 704 * X₂)
            have h3 : 704 * 128 ≤ (120000 : ℝ) := by norm_num
            have h4 : 704 * X₂ * (128 * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2))) ≤
                X₂ * (120000 * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2))) := by
              have := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ X₂ * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2)))
              linarith
            linarith
          have hpos_extra : 0 ≤ X₂ * (2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
              20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2)) := by positivity
          linarith
      · -- Subcase 2b: k₁^2 < ruzsaTheta k₂ * k₂^2
        push Not at hsubcase
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.1 q.2)),
            lintegral_finsetSum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.1 q.2)]
        have hterm_le : ∀ q ∈ P2b,
            ∫⁻ α, (nearSet k₁ q.1 q.2).indicator (fun _ => (1 : ℝ≥0∞)) α ∂volume ≤
              ENNReal.ofReal (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
                20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ)))) := by
          intro q hq
          have hone : (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 := rfl
          rw [hone, lintegral_indicator_one (hnear_meas k₁ q.1 q.2)]
          simp only [P2b, Finset.mem_filter, Finset.mem_product] at hq
          have hv := hnear_vol q.1 hq.1.1 q.2 hq.1.2 (ne_of_gt hq.2)
          refine hv.trans (ENNReal.ofReal_le_ofReal ?_)
          rw [abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hq.2))]
          have hpow_c : (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) * (2 : ℝ) ^ ruzsaS k₁ = (2 : ℝ) ^ ruzsaS k₂ := by
            rw [← pow_add]
            congr 1
            simp only [ruzsaS]
            exact Nat.sub_add_cancel (Nat.pow_le_pow_left hk₁_lt.le 2)
          have hrew : 2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) *
              (1 + 10 * X₂ / ((2 : ℝ) ^ ruzsaS k₁ * ((q.1 : ℝ) - (q.2 : ℝ)))) =
              2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
              20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ))) := by
            rw [← hpow_c]; field_simp; ring
          linarith
        have hsum_bd : 2 * ∑ q ∈ P2b, ∫⁻ α, (nearSet k₁ q.1 q.2).indicator (fun _ => (1 : ℝ≥0∞)) α ∂volume ≤
            ENNReal.ofReal (2 * ∑ q ∈ P2b, (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
              20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ))))) := by
          have h1 := Finset.sum_le_sum hterm_le
          have h2 : ∑ q ∈ P2b, ENNReal.ofReal (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
                20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ)))) =
              ENNReal.ofReal (∑ q ∈ P2b, (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
                20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ))))) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            intro q hq
            have hlt := (Finset.mem_filter.mp hq).2
            have hsub_pos : 0 < (q.1 : ℝ) - (q.2 : ℝ) := sub_pos.mpr (Nat.cast_lt.mpr hlt)
            positivity
          rw [h2] at h1
          have h3 : (2 : ℝ≥0∞) * ENNReal.ofReal (∑ q ∈ P2b, (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
                20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ))))) =
              ENNReal.ofReal (2 * ∑ q ∈ P2b, (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) +
                20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (1 / ((q.1 : ℝ) - (q.2 : ℝ))))) := by
            rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
          exact (mul_le_mul' le_rfl h1).trans_eq h3
        refine hsum_bd.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        have hP2_card : ((ruzsaPrimes k₂).card : ℝ) ≤ X₂ := by
          have hsub : ruzsaPrimes k₂ ⊆ Finset.Icc 1 (ruzsaP k₂) := fun p hp => by
            simp only [ruzsaPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
            exact ⟨hp.2.one_lt.le, hp.1.2⟩
          have h1 : (ruzsaPrimes k₂).card ≤ ruzsaP k₂ := by simpa using Finset.card_le_card hsub
          exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by positivity))
        have hP2b_card : 2 * (P2b.card : ℝ) ≤ X₂ ^ 2 := by
          have hnat : 2 * P2b.card ≤ (ruzsaPrimes k₂).card ^ 2 := by
            have hle : P2b.card + ((ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂).filter (fun q => q.1 < q.2)).card ≤
                (ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂).card := by
              have hdisj : Disjoint P2b ((ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂).filter (fun q => q.1 < q.2)) := by
                rw [Finset.disjoint_left]; intro q h1 h2; simp only [P2b, Finset.mem_filter] at h1 h2; omega
              rw [← Finset.card_union_of_disjoint hdisj]
              exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
            have hsym : ((ruzsaPrimes k₂ ×ˢ ruzsaPrimes k₂).filter (fun q => q.1 < q.2)).card = P2b.card := by
              refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
              · intro q hq; simp only [P2b, Finset.mem_filter, Finset.mem_product] at hq ⊢; exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩
              · intro q₁ _ q₂ _ h; ext <;> [exact congrArg Prod.snd h; exact congrArg Prod.fst h]
              · intro q hq; simp only [P2b, Finset.mem_filter, Finset.mem_product] at hq
                exact ⟨(q.2, q.1), by simp only [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2⟩, rfl⟩
            rw [hsym, Finset.card_product, ← sq] at hle; omega
          have hR : 2 * (P2b.card : ℝ) ≤ ((ruzsaPrimes k₂).card : ℝ) ^ 2 := by exact_mod_cast hnat
          exact hR.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hP2_card 2)
        have hθ₂ := ruzsaTheta_bounds (k := k₂) (by omega)
        have hsqrt2_lt : Real.sqrt 2 < 1.42 := by
          have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.42 ^ 2)
          rwa [Real.sqrt_sq (by norm_num)] at this
        have hθ₂_lt : ruzsaTheta k₂ < 0.42 := by linarith [hθ₂.2]
        -- Term 1: 2 * P2b.card * (2 / 2^(S k₂ - S k₁)) ≤ 2 * X₂^2 / 2^(S k₂ - S k₁) ≤ 2 * X₂ * 2^(-(1/10) k₂^2)
        have hterm1 : 2 * ((P2b.card : ℝ) * (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))) ≤
            X₂ * (2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2)) := by
          have h1 : 2 * ((P2b.card : ℝ) * (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))) =
              (2 * (P2b.card : ℝ)) * (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) := by ring
          rw [h1]
          have h2 : (2 * (P2b.card : ℝ)) * (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) ≤
              X₂ ^ 2 * (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) :=
            mul_le_mul_of_nonneg_right hP2b_card (by positivity)
          have h3 : X₂ / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) ≤ (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) := by
            have hrew : X₂ / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁) =
                (2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 - ((ruzsaS k₂ - ruzsaS k₁ : ℕ) : ℝ)) := by
              dsimp only [X₂]
              rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_sub (by norm_num)]
            rw [hrew]
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have hsub_cast : ((ruzsaS k₂ - ruzsaS k₁ : ℕ) : ℝ) = (k₂ : ℝ) ^ 2 - (k₁ : ℝ) ^ 2 := by
              simp only [ruzsaS]
              rw [Nat.cast_sub (Nat.pow_le_pow_left hk₁_lt.le 2)]; push_cast; rfl
            rw [hsub_cast]
            have h084 : 2 * ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 ≤ 0.84 * (k₂ : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
            linarith
          have h4 : X₂ ^ 2 * (2 / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁)) =
              X₂ * (2 * (X₂ / (2 : ℝ) ^ (ruzsaS k₂ - ruzsaS k₁))) := by ring
          rw [h4] at h2
          exact h2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by norm_num)) (by positivity))
        -- Term 2: 2 * (20 * X₂ / 2^(S k₂)) * ∑_{P2b} 1/(p - p') ≤ 40 * X₂^2 * (1 + k₂^2) / 2^(S k₂)
        have hP2_pos : 1 ≤ ruzsaP k₂ := by
          have hX2_ge1 : (1 : ℝ) ≤ X₂ :=
            Real.one_le_rpow (by norm_num) (mul_nonneg (by linarith [hθ₂.1]) (sq_nonneg _))
          exact Nat.le_floor (by simpa using hX2_ge1)
        have hharm := sum_inv_diff_le hP2_pos (S := ruzsaPrimes k₂) fun p hp => by
          simp only [ruzsaPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
          exact ⟨hp.2.one_lt.le, hp.1.2⟩
        have hlogP_le : Real.log (ruzsaP k₂ : ℝ) ≤ (k₂ : ℝ) ^ 2 := by
          have hle : (ruzsaP k₂ : ℝ) ≤ X₂ := Nat.floor_le (by positivity)
          have hlogX : Real.log X₂ ≤ (k₂ : ℝ) ^ 2 := by
            dsimp only [X₂]; rw [Real.log_rpow (by norm_num)]
            have hlog2_le : Real.log 2 ≤ 1 := (Real.log_le_iff_le_exp (by norm_num)).mpr (by
              have := Real.add_one_le_exp (1 : ℝ); linarith)
            calc ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 * Real.log 2
                ≤ 1 * (k₂ : ℝ) ^ 2 * 1 := mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
                  hlog2_le (Real.log_pos (by norm_num)).le (by positivity)
              _ = (k₂ : ℝ) ^ 2 := by ring
          exact (Real.log_le_log (Nat.cast_pos.mpr hP2_pos) hle).trans hlogX
        have hterm2 : 2 * (20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ *
              ∑ q ∈ P2b, (1 : ℝ) / ((q.1 : ℝ) - (q.2 : ℝ))) ≤
            X₂ * (20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2)) := by
          -- Wait: 2 * 20 = 40, while 2^(θ k₂ * k₂^2 - k₂^2) ≤ 2^(-0.58 k₂^2) ≤ (1/2) * 2^(-0.5 k₂^2) for k₂ ≥ 100!
          have hsum_le : ∑ q ∈ P2b, (1 : ℝ) / ((q.1 : ℝ) - (q.2 : ℝ)) ≤ X₂ * (1 + (k₂ : ℝ) ^ 2) := by
            calc ∑ q ∈ P2b, (1 : ℝ) / ((q.1 : ℝ) - (q.2 : ℝ))
                ≤ ((ruzsaPrimes k₂).card : ℝ) * (1 + Real.log (ruzsaP k₂ : ℝ)) := hharm
              _ ≤ X₂ * (1 + (k₂ : ℝ) ^ 2) := mul_le_mul hP2_card (by linarith)
                  (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (ruzsaP k₂ : ℝ) by exact_mod_cast hP2_pos)])
                  (by positivity)
          have hpow_le : 2 * (X₂ / (2 : ℝ) ^ ruzsaS k₂) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2) := by
            have hrew : 2 * (X₂ / (2 : ℝ) ^ ruzsaS k₂) =
                (2 : ℝ) ^ (1 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 - (k₂ : ℝ) ^ 2) := by
              calc 2 * (X₂ / (2 : ℝ) ^ ruzsaS k₂)
                  = (2 : ℝ) ^ (1 : ℝ) * ((2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2) / (2 : ℝ) ^ ((k₂ ^ 2 : ℕ) : ℝ)) := by
                      rw [Real.rpow_one, Real.rpow_natCast]; rfl
                _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 - ((k₂ ^ 2 : ℕ) : ℝ)) := by
                      rw [← Real.rpow_sub (by norm_num)]
                _ = (2 : ℝ) ^ (1 + ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 - (k₂ : ℝ) ^ 2) := by
                      rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring
            rw [hrew]
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have hk2ge : (10000 : ℝ) ≤ (k₂ : ℝ) ^ 2 := by
              have : (100 : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hk₂_100
              have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 100) this 2; norm_num at this; exact this
            have h042 : ruzsaTheta k₂ * (k₂ : ℝ) ^ 2 ≤ 0.42 * (k₂ : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hθ₂_lt.le (sq_nonneg _)
            linarith
          calc 2 * (20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * ∑ q ∈ P2b, (1 : ℝ) / ((q.1 : ℝ) - (q.2 : ℝ)))
              ≤ 2 * (20 * X₂ / (2 : ℝ) ^ ruzsaS k₂ * (X₂ * (1 + (k₂ : ℝ) ^ 2))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_le (by positivity)) (by norm_num)
            _ = X₂ * (20 * (1 + (k₂ : ℝ) ^ 2) * (2 * (X₂ / (2 : ℝ) ^ ruzsaS k₂))) := by ring
            _ ≤ X₂ * (20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le (by positivity)) (by positivity)
        have hpos1 : 0 ≤ X₂ * (120000 * (2 : ℝ) ^ (-(2 : ℝ) * (k₂ : ℝ) ^ ((3 : ℝ) / 2))) := by positivity
        linarith
    -- Sum lintegral over k₁ ∈ Ico K₀ k₂ and apply Markov!
    have hlint_G : ∫⁻ α, G α ∂volume ≤
        ENNReal.ofReal ((k₂ : ℝ) * (X₂ * (
          120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
          2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
          20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2)))) := by
      rw [lintegral_finsetSum]
      · set M_val : ℝ := X₂ * (
            120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
            2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
            20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2))
        calc ∑ k₁ ∈ Finset.Ico K₀ k₂, ∫⁻ α, g_k1 k₁ α ∂volume
            ≤ ∑ _k₁ ∈ Finset.Ico K₀ k₂, ENNReal.ofReal M_val := Finset.sum_le_sum hlint_k1
          _ = ((Finset.Ico K₀ k₂).card : ℝ≥0∞) * ENNReal.ofReal M_val := by simp
          _ ≤ (k₂ : ℝ≥0∞) * ENNReal.ofReal M_val := by
              refine mul_le_mul' ?_ le_rfl
              exact_mod_cast (show (Finset.Ico K₀ k₂).card ≤ k₂ by simp)
          _ = ENNReal.ofReal ((k₂ : ℝ) * M_val) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      · intro k₁ _
        dsimp only [g_k1]
        split_ifs
        · exact Finset.measurable_sum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.2.1 q.2.2)
        · exact measurable_const.mul (Finset.measurable_sum _ fun q _ => measurable_const.indicator (hnear_meas k₁ q.1 q.2))
    -- Apply Markov: ((𝒫 k₂).card / 2) * volume (BadAlpha k₂) ≤ ∫⁻ α, G α ∂volume
    have hcard_lb := hPrimes_lb k₂ (hK₀_ge.trans hk₂)
    set c_thr : ℝ := X₂ / (16 * (k₂ : ℝ) ^ 2)
    have hc_pos : 0 < c_thr := by positivity
    have hBad_sub : BadAlpha k₂ ⊆ {α : ℝ | ENNReal.ofReal c_thr ≤ G α} := by
      intro α ⟨hα, hcard⟩
      have hdom := hG_dom α hα
      have hc_le : ENNReal.ofReal c_thr ≤ (((ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂)).card : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        have h1 : (2 : ℝ) * c_thr ≤ ((ruzsaPrimes k₂).card : ℝ) := by
          have : 2 * c_thr = X₂ / (8 * (k₂ : ℝ) ^ 2) := by dsimp only [c_thr]; ring
          linarith
        have h2 : ((ruzsaPrimes k₂).card : ℝ) ≤ 2 * (((ruzsaPrimes k₂).filter (fun p₂ => IsColl α k₂ p₂)).card : ℝ) := by
          exact_mod_cast hcard
        linarith
      exact hc_le.trans hdom
    have hmarkov : ENNReal.ofReal c_thr * volume (BadAlpha k₂) ≤ ∫⁻ α, G α ∂volume := by
      calc ENNReal.ofReal c_thr * volume (BadAlpha k₂)
          ≤ ENNReal.ofReal c_thr * volume {α : ℝ | ENNReal.ofReal c_thr ≤ G α} :=
            mul_le_mul' le_rfl (measure_mono hBad_sub)
        _ ≤ ∫⁻ α, G α ∂volume := mul_meas_ge_le_lintegral₀ hG_meas.aemeasurable _
    have hvol_le := hmarkov.trans hlint_G
    have hc_ne0 : ENNReal.ofReal c_thr ≠ 0 := (ENNReal.ofReal_pos.mpr hc_pos).ne'
    have hc_ne_top : ENNReal.ofReal c_thr ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hc_ne0) (Or.inl hc_ne_top)] at hvol_le
    refine hvol_le.trans ?_
    rw [← ENNReal.ofReal_div_of_pos hc_pos]
    apply ENNReal.ofReal_le_ofReal
    have hdiv_eq : (k₂ : ℝ) * (X₂ * (
        120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
        2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
        20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2))) / c_thr =
        16 * (k₂ : ℝ) ^ 2 * ((k₂ : ℝ) * (
        120000 * (2 : ℝ) ^ (-(2 : ℝ) * ((k₂ : ℝ) ^ ((3 : ℝ) / 2))) +
        2 * (2 : ℝ) ^ (-(1 / 10 : ℝ) * (k₂ : ℝ) ^ 2) +
        20 * (1 + (k₂ : ℝ) ^ 2) * (2 : ℝ) ^ (-(1 / 2 : ℝ) * (k₂ : ℝ) ^ 2))) := by
      dsimp only [c_thr]
      have hX2_ne : X₂ ≠ 0 := by positivity
      field_simp
    rw [hdiv_eq]
    exact hK₀_bd k₂ hk₂
  -- Union bound over all k₂ ≥ K₀: volume (⋃ k₂ ≥ K₀, BadAlpha k₂) ≤ 1/2 < 1 = volume [1, 2]
  have hexAlpha : ∃ α ∈ Set.Icc (1 : ℝ) 2, ∀ k₂ : ℕ, K₀ ≤ k₂ → α ∉ BadAlpha k₂ := by
    by_contra hnone
    push Not at hnone
    have hcover : Set.Icc (1 : ℝ) 2 ⊆ ⋃ k₂ : ℕ, if K₀ ≤ k₂ then BadAlpha k₂ else ∅ := by
      intro α hα
      obtain ⟨k₂, hk₂, hbad⟩ := hnone α hα
      rw [Set.mem_iUnion]
      exact ⟨k₂, by simp [hk₂, hbad]⟩
    have hvol_le : volume (Set.Icc (1 : ℝ) 2) ≤ ∑' k₂ : ℕ, ENNReal.ofReal (1 / (2 : ℝ) ^ (k₂ + 2)) := by
      calc volume (Set.Icc (1 : ℝ) 2)
          ≤ volume (⋃ k₂ : ℕ, if K₀ ≤ k₂ then BadAlpha k₂ else ∅) := measure_mono hcover
        _ ≤ ∑' k₂ : ℕ, volume (if K₀ ≤ k₂ then BadAlpha k₂ else ∅) := measure_iUnion_le _
        _ ≤ ∑' k₂ : ℕ, ENNReal.ofReal (1 / (2 : ℝ) ^ (k₂ + 2)) := by
            refine ENNReal.tsum_le_tsum fun k₂ => ?_
            split_ifs with h
            · exact hBad_vol k₂ h
            · simp
    have hgeom : (∑' k₂ : ℕ, ENNReal.ofReal (1 / (2 : ℝ) ^ (k₂ + 2))) = ENNReal.ofReal (1 / 2) := by
      have hsumm : Summable (fun k₂ : ℕ => (1 / (2 : ℝ) ^ (k₂ + 2))) := by
        have h1 : Summable (fun k₂ : ℕ => ((1 / 2 : ℝ) ^ k₂)) :=
          summable_geometric_of_lt_one (by norm_num) (by norm_num)
        refine (h1.mul_left (1 / 4)).congr fun k₂ => ?_
        rw [pow_add, one_div_pow]; norm_num
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hsumm]
      congr 1
      have htsum : (∑' k₂ : ℕ, (1 / (2 : ℝ) ^ (k₂ + 2))) = (1 / 4) * ∑' k₂ : ℕ, (1 / 2 : ℝ) ^ k₂ := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k₂ => ?_
        rw [pow_add, one_div_pow]; norm_num
      rw [htsum, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    rw [Real.volume_Icc, hgeom] at hvol_le
    have hlt : ENNReal.ofReal (1 / 2 : ℝ) < ENNReal.ofReal ((2 : ℝ) - 1) :=
      ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)
    exact not_lt_of_ge hvol_le hlt
  obtain ⟨α, hα, hα_good⟩ := hexAlpha
  -- Construct the universal infinite Sidon set A!
  let goodPrimes : ℕ → Finset ℕ := fun k => (ruzsaPrimes k).filter (fun p => ¬ IsColl α k p)
  let A : Set ℕ := {x : ℕ | ∃ k : ℕ, K₀ ≤ k ∧ ∃ p ∈ goodPrimes k, x = ruzsaCode α k p}
  -- 1. Prove A is Sidon!
  have hA_sid : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
      a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂ := by
    intro a₁ ha1 a₂ ha2 b₁ hb1 b₂ hb2 hle1 hle2 hsum
    obtain ⟨k₁, hk₁, p₁, hp1, rfl⟩ := ha1
    obtain ⟨k₂, hk₂, p₂, hp2, rfl⟩ := ha2
    obtain ⟨k'₁, hk'₁, p'₁, hp'1, rfl⟩ := hb1
    obtain ⟨k'₂, hk'₂, p'₂, hp'2, rfl⟩ := hb2
    -- Helper: order any pair by level k₁ ≤ k₂
    have hordered : ∀ {j₁ j₂ j'₁ j'₂ q₁ q₂ q'₁ q'₂ : ℕ},
        K₀ ≤ j₁ → j₁ ≤ j₂ → K₀ ≤ j'₁ → j'₁ ≤ j'₂ →
        q₁ ∈ goodPrimes j₁ → q₂ ∈ goodPrimes j₂ → q'₁ ∈ goodPrimes j'₁ → q'₂ ∈ goodPrimes j'₂ →
        ruzsaCode α j₁ q₁ + ruzsaCode α j₂ q₂ = ruzsaCode α j'₁ q'₁ + ruzsaCode α j'₂ q'₂ →
        (ruzsaCode α j₁ q₁ = ruzsaCode α j'₁ q'₁ ∧ ruzsaCode α j₂ q₂ = ruzsaCode α j'₂ q'₂) ∨
        (ruzsaCode α j₁ q₁ = ruzsaCode α j'₂ q'₂ ∧ ruzsaCode α j₂ q₂ = ruzsaCode α j'₁ q'₁) := by
      intro j₁ j₂ j'₁ j'₂ q₁ q₂ q'₁ q'₂ hj1 hj12 hj'1 hj'12 hq1 hq2 hq'1 hq'2 hce
      have hq1P : q₁ ∈ ruzsaPrimes j₁ := (Finset.mem_filter.mp hq1).1
      have hq2P : q₂ ∈ ruzsaPrimes j₂ := (Finset.mem_filter.mp hq2).1
      have hq'1P : q'₁ ∈ ruzsaPrimes j'₁ := (Finset.mem_filter.mp hq'1).1
      have hq'2P : q'₂ ∈ ruzsaPrimes j'₂ := (Finset.mem_filter.mp hq'2).1
      have hdec := ruzsaCode_decode hα (by omega) hj12 (by omega) hj'12 hq1P hq2P hq'1P hq'2P hce
      obtain ⟨rfl, rfl⟩ := hdec.1
      by_cases heqj : j₁ = j₂
      · subst heqj
        rcases ruzsaCode_same_level_inj hα (by omega) hq1P hq2P hq'1P hq'2P hce with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
      · have hlt : j₁ < j₂ := lt_of_le_of_ne hj12 heqj
        have hq2_eq : q₂ = q'₂ := by
          by_contra hne
          have hcoll : IsColl α j₂ q₂ :=
            ⟨j₁, Finset.mem_Ico.mpr ⟨hj1, hlt⟩, q₁, hq1P, q'₁, hq'1P, q'₂, hq'2P, hne, hce⟩
          exact (Finset.mem_filter.mp hq2).2 hcoll
        subst hq2_eq
        exact Or.inl ⟨by omega, rfl⟩
    have hpair : (ruzsaCode α k₁ p₁ = ruzsaCode α k'₁ p'₁ ∧ ruzsaCode α k₂ p₂ = ruzsaCode α k'₂ p'₂) ∨
        (ruzsaCode α k₁ p₁ = ruzsaCode α k'₂ p'₂ ∧ ruzsaCode α k₂ p₂ = ruzsaCode α k'₁ p'₁) := by
      rcases le_total k₁ k₂ with h1 | h1 <;> rcases le_total k'₁ k'₂ with h2 | h2
      · exact hordered hk₁ h1 hk'₁ h2 hp1 hp2 hp'1 hp'2 hsum
      · rcases hordered hk₁ h1 hk'₂ h2 hp1 hp2 hp'2 hp'1 (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr ⟨e1, e2⟩
        · exact Or.inl ⟨e1, e2⟩
      · rcases hordered hk₂ h1 hk'₁ h2 hp2 hp1 hp'1 hp'2 (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr ⟨e2, e1⟩
        · exact Or.inl ⟨e2, e1⟩
      · rcases hordered hk₂ h1 hk'₂ h2 hp2 hp1 hp'2 hp'1 (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e2, e1⟩
        · exact Or.inr ⟨e2, e1⟩
    rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1, e2⟩
    · exact ⟨by omega, by omega⟩
  -- 2. Prove the counting lower bound for every ε > 0!
  have hcount : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) := by
    intro ε hε
    -- For large k ≥ K_ε, every N ∈ [2^(T k), 2^(T (k+1))) satisfies:
    -- |A ∩ [1, N]| ≥ |goodPrimes k| ≥ |𝒫 k|/2 ≥ 2^(θ k * k^2) / (16 * k^2) ≥ (2^(T (k+1)))^(√2 - 1 - ε) ≥ N^(√2 - 1 - ε)!
    have hexKε : ∃ Kε : ℕ, K₀ ≤ Kε ∧ ∀ k : ℕ, Kε ≤ k →
        (Real.sqrt 2 - 1 - ε) * ((ruzsaT (k + 1) : ℕ) : ℝ) ≤
          ruzsaTheta k * (k : ℝ) ^ 2 - (4 + 2 * Real.logb 2 (k : ℝ)) := by
      -- Difference is ε * k^2 - (k^(3/2) + (√2-1)*(8k + 7) + 4 + 2 log_2 k) → +∞
      have htend : Tendsto (fun k : ℕ =>
          ε * (k : ℝ) ^ 2 - ((k : ℝ) ^ ((3 : ℝ) / 2) + 10 * (k : ℝ) + 20)) atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro b
        let M : ℕ := Nat.ceil ((max b 0 + 20) / ε + (20 / ε) ^ 2) + 100
        refine ⟨M, fun k hk => ?_⟩
        have hk_ge : ((max b 0 + 20) / ε + (20 / ε) ^ 2 : ℝ) ≤ (k : ℝ) := by
          have h1 : (Nat.ceil ((max b 0 + 20) / ε + (20 / ε) ^ 2) : ℝ) ≤ (k : ℝ) := by
            exact_mod_cast (show Nat.ceil ((max b 0 + 20) / ε + (20 / ε) ^ 2) ≤ k by omega)
          exact (Nat.le_ceil _).trans h1
        have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
        have h1 : (max b 0 + 20) / ε ≤ (k : ℝ) := by linarith [sq_nonneg (20 / ε)]
        have h2 : (20 / ε) ^ 2 ≤ (k : ℝ) := by linarith [div_nonneg (by linarith [le_max_right b 0] : (0 : ℝ) ≤ max b 0 + 20) hε.le]
        have hsk : 20 / ε ≤ Real.sqrt (k : ℝ) := by
          calc 20 / ε = Real.sqrt ((20 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
            _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt h2
        have hk32 : (k : ℝ) ^ ((3 : ℝ) / 2) = (k : ℝ) * Real.sqrt (k : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (Nat.cast_nonneg k) (by norm_num)]; congr 1; norm_num
        have hterm1 : (k : ℝ) ^ ((3 : ℝ) / 2) ≤ (ε / 20) * (k : ℝ) ^ 2 := by
          rw [hk32]
          have hsk_le : Real.sqrt (k : ℝ) ≤ (ε / 20) * (k : ℝ) := by
            have hmul := mul_le_mul_of_nonneg_right hsk (Real.sqrt_nonneg (k : ℝ))
            rw [Real.mul_self_sqrt (Nat.cast_nonneg k)] at hmul
            have hmul2 := mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ ε / 20)
            have hlhs : (ε / 20) * (20 / ε * Real.sqrt (k : ℝ)) = Real.sqrt (k : ℝ) := by field_simp
            linarith
          calc (k : ℝ) * Real.sqrt (k : ℝ) ≤ (k : ℝ) * ((ε / 20) * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left hsk_le (Nat.cast_nonneg _)
            _ = (ε / 20) * (k : ℝ) ^ 2 := by ring
        have hterm2 : 10 * (k : ℝ) ≤ (ε / 2) * (k : ℝ) ^ 2 := by
          have hk20 : 20 / ε ≤ (k : ℝ) := by
            have : (1 : ℝ) ≤ Real.sqrt (k : ℝ) := by
              calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
                _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ k by omega))
            have hsq : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
              calc Real.sqrt (k : ℝ) = Real.sqrt (k : ℝ) * 1 := (mul_one _).symm
                _ ≤ Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
                _ = (k : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
            exact hsk.trans hsq
          have hmul := mul_le_mul_of_nonneg_left hk20 (by positivity : 0 ≤ (ε / 2) * (k : ℝ))
          have hlhs : (ε / 2) * (k : ℝ) * (20 / ε) = 10 * (k : ℝ) := by field_simp; ring
          have hrhs : (ε / 2) * (k : ℝ) * (k : ℝ) = (ε / 2) * (k : ℝ) ^ 2 := by ring
          linarith
        have hterm3 : max b 0 + 20 ≤ (ε / 4) * (k : ℝ) ^ 2 := by
          have h4k : 4 * ((max b 0 + 20) / ε) ≤ (k : ℝ) ^ 2 := by
            have hk4 : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 4 ≤ k by omega)
            calc 4 * ((max b 0 + 20) / ε) ≤ 4 * (k : ℝ) := mul_le_mul_of_nonneg_left h1 (by norm_num)
              _ ≤ (k : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_right hk4 (Nat.cast_nonneg _)
              _ = (k : ℝ) ^ 2 := (sq _).symm
          have hmul := mul_le_mul_of_nonneg_left h4k (by positivity : 0 ≤ ε / 4)
          have hlhs : (ε / 4) * (4 * ((max b 0 + 20) / ε)) = max b 0 + 20 := by field_simp
          linarith
        have hk2_nn : (0 : ℝ) ≤ ε * (k : ℝ) ^ 2 := by positivity
        linarith [le_max_left b 0]
      have hev := htend.eventually (eventually_ge_atTop (0 : ℝ))
      rw [Filter.eventually_atTop] at hev
      obtain ⟨K₂, hK₂⟩ := hev
      refine ⟨max K₀ (max K₂ 100), le_max_left _ _, fun k hk => ?_⟩
      have hk_K₂ : K₂ ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
      have hk_100 : 100 ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
      have hpos_diff := hK₂ k hk_K₂
      have hT_eq : ((ruzsaT (k + 1) : ℕ) : ℝ) = (k : ℝ) ^ 2 + 8 * (k : ℝ) + 7 := by
        simp only [ruzsaT]; push_cast; ring
      rw [hT_eq]
      have hlog_le : Real.logb 2 (k : ℝ) ≤ (k : ℝ) := by
        have h1 : Real.log (k : ℝ) ≤ (k : ℝ) := (Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr (by omega))).trans (by linarith)
        have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
          have : (2 : ℝ) ^ 2 ≥ Real.exp 1 := by
            have := Real.exp_one_lt_d9; linarith
          have h := Real.log_le_log (Real.exp_pos 1) this
          rw [Real.log_exp, Real.log_pow] at h
          norm_num at h; linarith
        -- Wait: logb 2 k = log k / log 2 ≤ 2 * log k ≤ 2 * k; actually 2 * logb 2 k ≤ 4 * k!
        -- Even tighter: log_2 k ≤ k directly since k ≤ 2^k!
        have hk_le_pow : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
          rw [Real.rpow_natCast]
          exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
        calc Real.logb 2 (k : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (k : ℝ)) :=
              Real.logb_le_logb_of_le (by norm_num) (Nat.cast_pos.mpr (by omega)) hk_le_pow
          _ = (k : ℝ) := Real.logb_rpow (by norm_num) (by norm_num)
      have hsqrt2_lt : Real.sqrt 2 < 1.5 := by
        have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 1.5 ^ 2)
        rwa [Real.sqrt_sq (by norm_num)] at this
      have hθ_eq : ruzsaTheta k * (k : ℝ) ^ 2 = (Real.sqrt 2 - 1) * (k : ℝ) ^ 2 - (k : ℝ) ^ ((3 : ℝ) / 2) := by
        dsimp only [ruzsaTheta]
        have hk32 : (1 / Real.sqrt (k : ℝ)) * (k : ℝ) ^ 2 = (k : ℝ) ^ ((3 : ℝ) / 2) := by
          have hsk_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
          have hsq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
          have hrp : (k : ℝ) ^ ((3 : ℝ) / 2) = (k : ℝ) * Real.sqrt (k : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (Nat.cast_nonneg k) (by norm_num)]; congr 1; norm_num
          rw [hrp, one_div_mul_eq_div, div_eq_iff hsk_pos.ne']
          calc (k : ℝ) ^ 2 = (k : ℝ) * (Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ)) := by rw [hsq]; ring
            _ = (k : ℝ) * Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) := by ring
        linarith [show (Real.sqrt 2 - 1 - 1 / Real.sqrt (k : ℝ)) * (k : ℝ) ^ 2 =
          (Real.sqrt 2 - 1) * (k : ℝ) ^ 2 - (1 / Real.sqrt (k : ℝ)) * (k : ℝ) ^ 2 by ring]
      rw [hθ_eq]
      have hlin1 : (Real.sqrt 2 - 1 - ε) * ((k : ℝ) ^ 2 + 8 * (k : ℝ) + 7) ≤
          (Real.sqrt 2 - 1 - ε) * (k : ℝ) ^ 2 + 4 * (k : ℝ) + 4 := by
        have h1 : Real.sqrt 2 - 1 - ε < 1 / 2 := by linarith
        have hpos_8k : 0 ≤ 8 * (k : ℝ) + 7 := by positivity
        have h2 := mul_le_mul_of_nonneg_right h1.le hpos_8k
        linarith
      linarith
    obtain ⟨Kε, hKε_ge, hKε_bd⟩ := hexKε
    refine ⟨2 ^ ruzsaT Kε, fun N hN => ?_⟩
    -- Pick k ≥ Kε with 2^(T k) ≤ N < 2^(T (k + 1))
    have hex_k : ∃ k : ℕ, N < 2 ^ ruzsaT (k + 1) := by
      refine ⟨N, ?_⟩
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : N ≤ ruzsaT (N + 1) := by simp only [ruzsaT]; omega
      exact h1.trans_le (Nat.pow_le_pow_right (by omega) h2)
    let k := Nat.find hex_k
    have hk_lt : N < 2 ^ ruzsaT (k + 1) := Nat.find_spec hex_k
    have hk_ge_Kε : Kε ≤ k := by
      by_contra hlt; push Not at hlt
      have hk1_le : k + 1 ≤ Kε := by omega
      have hT_le : ruzsaT (k + 1) ≤ ruzsaT Kε := by
        simp only [ruzsaT]; nlinarith
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hT_le
      omega
    have hk_le_N : 2 ^ ruzsaT k ≤ N := by
      have hk_pos : 0 < k := by have := hK₁_100.trans (hK₀_ge.trans (hKε_ge.trans hk_ge_Kε)); omega
      have hmin := Nat.find_min hex_k (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hk_pos] at hmin
      omega
    -- Every p ∈ goodPrimes k maps injectively via ruzsaCode α k into A ∩ Icc 1 N
    have hk_ge_K0 : K₀ ≤ k := hKε_ge.trans hk_ge_Kε
    have hk_ge_100 : 100 ≤ k := hK₁_100.trans (hK₀_ge.trans hk_ge_K0)
    have hsub : (goodPrimes k).image (ruzsaCode α k) ⊆ (Finset.Icc 1 N).filter (fun x => x ∈ A) := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      have ⟨hpos, hltT⟩ := ruzsaCode_pos_and_lt α k p (by omega)
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpos, hltT.le.trans hk_le_N⟩, ⟨k, hk_ge_K0, p, hp, rfl⟩⟩
    have hinj_code : Set.InjOn (ruzsaCode α k) (goodPrimes k : Set ℕ) := by
      intro p₁ hp1 p₂ hp2 heq
      have h1 : p₁ ∈ ruzsaPrimes k := (Finset.mem_filter.mp hp1).1
      have h2 : p₂ ∈ ruzsaPrimes k := (Finset.mem_filter.mp hp2).1
      have hsum : ruzsaCode α k p₁ + ruzsaCode α k p₁ = ruzsaCode α k p₂ + ruzsaCode α k p₂ := by omega
      rcases ruzsaCode_same_level_inj hα (by omega) h1 h1 h2 h2 hsum with ⟨e, _⟩ | ⟨e, _⟩ <;> exact e
    rw [ncard_inter_Icc_eq_filter_card]
    have hcard_ge_good : (goodPrimes k).card ≤ ((Finset.Icc 1 N).filter (fun x => x ∈ A)).card := by
      rw [← Finset.card_image_of_injOn hinj_code]
      exact Finset.card_le_card hsub
    -- Since α ∉ BadAlpha k, 2 * (colliding).card < (ruzsaPrimes k).card, so (ruzsaPrimes k).card ≤ 2 * (goodPrimes k).card
    have hgood_ge : ((ruzsaPrimes k).card : ℝ) / 2 ≤ ((goodPrimes k).card : ℝ) := by
      have hnotbad : ¬ ((ruzsaPrimes k).card ≤ 2 * ((ruzsaPrimes k).filter (fun p => IsColl α k p)).card) := by
        intro hle; exact hα_good k hk_ge_K0 ⟨hα, hle⟩
      push Not at hnotbad
      have hpart := Finset.card_filter_add_card_filter_not (s := ruzsaPrimes k) (p := fun p => IsColl α k p)
      have hnat : (ruzsaPrimes k).card ≤ 2 * (goodPrimes k).card := by
        change (ruzsaPrimes k).card ≤ 2 * ((ruzsaPrimes k).filter (fun p => ¬ IsColl α k p)).card
        omega
      have hR : ((ruzsaPrimes k).card : ℝ) ≤ 2 * ((goodPrimes k).card : ℝ) := by exact_mod_cast hnat
      linarith
    have hprimes_k := hPrimes_lb k (hK₀_ge.trans hk_ge_K0)
    -- Now compare N^(√2 - 1 - ε) ≤ (2^(T(k+1)))^(√2 - 1 - ε) ≤ 2^(θ k * k^2) / (16 * k^2) ≤ (goodPrimes k).card
    have hN_pow_le : (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤
        ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (16 * (k : ℝ) ^ 2) := by
      by_cases hexp_nn : 0 ≤ Real.sqrt 2 - 1 - ε
      · have hN_le_R : (N : ℝ) ≤ (2 : ℝ) ^ ((ruzsaT (k + 1) : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; exact_mod_cast hk_lt.le
        have hstep1 : (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤
            (2 : ℝ) ^ ((Real.sqrt 2 - 1 - ε) * ((ruzsaT (k + 1) : ℕ) : ℝ)) := by
          calc (N : ℝ) ^ (Real.sqrt 2 - 1 - ε)
              ≤ ((2 : ℝ) ^ ((ruzsaT (k + 1) : ℕ) : ℝ)) ^ (Real.sqrt 2 - 1 - ε) :=
                Real.rpow_le_rpow (Nat.cast_nonneg N) hN_le_R hexp_nn
            _ = (2 : ℝ) ^ (((ruzsaT (k + 1) : ℕ) : ℝ) * (Real.sqrt 2 - 1 - ε)) :=
                (Real.rpow_mul (by norm_num) _ _).symm
            _ = (2 : ℝ) ^ ((Real.sqrt 2 - 1 - ε) * ((ruzsaT (k + 1) : ℕ) : ℝ)) := by ring_nf
        have hstep2 : (2 : ℝ) ^ ((Real.sqrt 2 - 1 - ε) * ((ruzsaT (k + 1) : ℕ) : ℝ)) ≤
            (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2 - (4 + 2 * Real.logb 2 (k : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hKε_bd k hk_ge_Kε)
        have hrew : (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2 - (4 + 2 * Real.logb 2 (k : ℝ))) =
            ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (16 * (k : ℝ) ^ 2) := by
          rw [Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num)]
          have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
          have hk2 : (2 : ℝ) ^ (2 * Real.logb 2 (k : ℝ)) = (k : ℝ) ^ 2 := by
            rw [mul_comm, Real.rpow_mul (by norm_num),
                Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.mpr (by omega))]
            norm_cast
          rw [h16, hk2]
        exact (hstep1.trans hstep2).trans_eq hrew
      · -- If √2 - 1 - ε < 0, then N^(√2 - 1 - ε) ≤ 1 ≤ 2^(θ k * k^2) / (16 * k^2)
        push Not at hexp_nn
        have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by
          have : 1 ≤ 2 ^ ruzsaT k := Nat.one_le_two_pow
          exact_mod_cast (this.trans hk_le_N)
        have h1 : (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hN_ge1 hexp_nn.le
        have h2 : (1 : ℝ) ≤ ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (16 * (k : ℝ) ^ 2) := by
          have hθ := ruzsaTheta_bounds (k := k) (by omega)
          have hlog_le : 4 + 2 * Real.logb 2 (k : ℝ) ≤ ruzsaTheta k * (k : ℝ) ^ 2 := by
            have hk_le_pow : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
              rw [Real.rpow_natCast]; exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
            have hlb : Real.logb 2 (k : ℝ) ≤ (k : ℝ) := by
              calc Real.logb 2 (k : ℝ) ≤ Real.logb 2 ((2 : ℝ) ^ (k : ℝ)) :=
                    Real.logb_le_logb_of_le (by norm_num) (Nat.cast_pos.mpr (by omega)) hk_le_pow
                _ = (k : ℝ) := Real.logb_rpow (by norm_num) (by norm_num)
            have hk100 : (100 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_100
            have h02 : (1 / 5 : ℝ) * (k : ℝ) ^ 2 ≤ ruzsaTheta k * (k : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hθ.1.le (sq_nonneg _)
            have h2k : 4 + 2 * (k : ℝ) ≤ (1 / 5 : ℝ) * (k : ℝ) ^ 2 := by
              have : 100 * (k : ℝ) ≤ (k : ℝ) ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hk100 (Nat.cast_nonneg _)
              linarith
            linarith
          have hrew : ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (16 * (k : ℝ) ^ 2) =
              (2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2 - (4 + 2 * Real.logb 2 (k : ℝ))) := by
            rw [Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num)]
            have h16 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
            have hk2 : (2 : ℝ) ^ (2 * Real.logb 2 (k : ℝ)) = (k : ℝ) ^ 2 := by
              rw [mul_comm, Real.rpow_mul (by norm_num),
                  Real.rpow_logb (by norm_num) (by norm_num) (Nat.cast_pos.mpr (by omega))]
              norm_cast
            rw [h16, hk2]
          rw [hrew]
          exact Real.one_le_rpow (by norm_num) (by linarith)
        exact h1.trans h2
    calc (N : ℝ) ^ (Real.sqrt 2 - 1 - ε)
        ≤ ((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (16 * (k : ℝ) ^ 2) := hN_pow_le
      _ = (((2 : ℝ) ^ (ruzsaTheta k * (k : ℝ) ^ 2)) / (8 * (k : ℝ) ^ 2)) / 2 := by ring
      _ ≤ ((ruzsaPrimes k).card : ℝ) / 2 := div_le_div_of_nonneg_right hprimes_k (by norm_num)
      _ ≤ ((goodPrimes k).card : ℝ) := hgood_ge
      _ ≤ (((Finset.Icc 1 N).filter (fun x => x ∈ A)).card : ℝ) := by exact_mod_cast hcard_ge_good
  -- 3. Deduce A.Infinite from hcount at ε = 1/4 (since √2 - 1 - 1/4 > 0.16 > 0)
  have hA_inf : A.Infinite := by
    by_contra hfin
    rw [Set.not_infinite] at hfin
    obtain ⟨N₀, hN₀⟩ := hcount (1 / 4) (by norm_num)
    have hexp_pos : (1 / 10 : ℝ) < Real.sqrt 2 - 1 - 1 / 4 := by
      have hsqrt2_gt : (1.4 : ℝ) < Real.sqrt 2 := by
        have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.4 ^ 2) (by norm_num : (1.4 : ℝ) ^ 2 < 2)
        rwa [Real.sqrt_sq (by norm_num)] at this
      linarith
    let N := max N₀ ((hfin.toFinset.card + 2) ^ 10)
    have hbd := hN₀ N (le_max_left _ _)
    have hcard_le : ((A ∩ Set.Icc 1 N).ncard : ℝ) ≤ (hfin.toFinset.card : ℝ) := by
      have hsub : A ∩ Set.Icc 1 N ⊆ hfin.toFinset := fun x hx => hfin.mem_toFinset.mpr hx.1
      have h1 : (A ∩ Set.Icc 1 N).ncard ≤ hfin.toFinset.card := by
        calc (A ∩ Set.Icc 1 N).ncard ≤ (hfin.toFinset : Set ℕ).ncard :=
              Set.ncard_le_ncard hsub (Finset.finite_toSet _)
          _ = hfin.toFinset.card := Set.ncard_coe_finset _
      exact_mod_cast h1
    have hN_ge : ((hfin.toFinset.card + 2 : ℕ) : ℝ) ^ (10 : ℕ) ≤ (N : ℝ) := by
      exact_mod_cast (le_max_right N₀ _)
    have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 1 ≤ (hfin.toFinset.card + 2) ^ 10 := Nat.one_le_pow _ _ (by omega)
      exact_mod_cast (this.trans (le_max_right N₀ _))
    have hpow_ge : ((hfin.toFinset.card + 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (Real.sqrt 2 - 1 - 1 / 4) := by
      calc ((hfin.toFinset.card + 2 : ℕ) : ℝ)
          = (((hfin.toFinset.card + 2 : ℕ) : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
        _ ≤ (N : ℝ) ^ ((1 : ℝ) / 10) := Real.rpow_le_rpow (by positivity) hN_ge (by norm_num)
        _ ≤ (N : ℝ) ^ (Real.sqrt 2 - 1 - 1 / 4) := Real.rpow_le_rpow_of_exponent_le hN_ge1 hexp_pos.le
    push_cast at hpow_ge
    linarith
  exact ⟨A, hA_inf, hA_sid, hcount⟩

end Ruzsa1998

end PPL124
