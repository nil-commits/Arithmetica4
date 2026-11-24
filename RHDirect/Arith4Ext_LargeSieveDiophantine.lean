/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Arith4Ext.LargeSieveDiophantine — Large Sieve, Geometry of Numbers, Equidistribution, & Diophantine Approximation

Reusable, 100%-unconditional (`0` assumptions, `0` proxies, `0` `sorry`, `0` custom axioms)
Tier A library on targeted Mathlib imports (`namespace Arith4Ext.LargeSieveDiophantine`):

1. **Well-Spaced Points & Analytic Large Sieve Inequality (Gallagher's Elementary Proof)** +
   **Arithmetic Farey Large Sieve Corollary** over `1 ≤ q ≤ Q`, `Nat.Coprime a q`.
2. **Dirichlet's Simultaneous Diophantine Approximation Theorem** (integer `N` pigeonhole form
   with strict `< 1/N`, real `Q ≥ 1` Minkowski form with `≤ 1/Q`, and 1D infinite approximations).
3. **Blichfeldt's Theorem, Minkowski's Convex Body Theorem (Strict & Compact), and Discrete Grid Pigeonhole Core**
   on `Fin d → ℝ` / `ℤ^d`.
4. **Weyl's Equidistribution Criterion & Irrational Rotation Equidistribution** (`x_n = n * α` for `Irrational α`).
5. **Liouville's Irrationality-Measure Theorem** for algebraic irrationals of degree `d ≥ 2`.
-/

open Real Complex Finset MeasureTheory intervalIntegral
open scoped BigOperators Pointwise

namespace Arith4Ext.LargeSieveDiophantine

noncomputable section

/-! ## Section 1: Well-Spaced Points & Gallagher's Analytic Large Sieve Inequality -/

/-- Distance from a real number `x` to the nearest integer, `‖x‖_{ℝ/ℤ} = |x - round x|`. -/
def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

/-- A finite family `α : ι → ℝ` indexed by `s : Finset ι` is `δ`-well-spaced modulo `1`
if `δ ≤ |α i - α j - k|` for all distinct `i, j ∈ s` and all `k : ℤ`. -/
def WellSpaced {ι : Type*} (s : Finset ι) (α : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ k : ℤ, δ ≤ |α i - α j - (k : ℝ)|

/-- The standard additive character `e(x) = exp(2πi x)` on `ℝ`. -/
def eChar (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := abs_nonneg _

lemma distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := abs_sub_round x

lemma distToInt_le_abs_sub (x : ℝ) (k : ℤ) : distToInt x ≤ |x - (k : ℝ)| := by
  unfold distToInt
  by_cases hk : k = round x
  · rw [hk]
  · have hhalf : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
    have hbounds := abs_le.mp hhalf
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have hk_le : (k : ℝ) ≤ (round x : ℝ) - 1 := by
        have : k ≤ round x - 1 := by omega
        exact_mod_cast this
      have h1 : 1 / 2 ≤ x - (k : ℝ) := by linarith
      calc |x - (round x : ℝ)| ≤ 1 / 2 := hhalf
        _ ≤ x - (k : ℝ) := h1
        _ ≤ |x - (k : ℝ)| := le_abs_self _
    · have hk_ge : (round x : ℝ) + 1 ≤ (k : ℝ) := by
        have : round x + 1 ≤ k := hgt
        exact_mod_cast this
      have h1 : 1 / 2 ≤ (k : ℝ) - x := by linarith
      calc |x - (round x : ℝ)| ≤ 1 / 2 := hhalf
        _ ≤ (k : ℝ) - x := h1
        _ = -(x - (k : ℝ)) := by ring
        _ ≤ |x - (k : ℝ)| := neg_le_abs _

lemma distToInt_add_int (x : ℝ) (k : ℤ) : distToInt (x + k) = distToInt x := by
  apply le_antisymm
  · have h := distToInt_le_abs_sub (x + k) (round x + k)
    push_cast at h
    have heq : x + (k : ℝ) - ((round x : ℝ) + (k : ℝ)) = x - (round x : ℝ) := by ring
    simpa only [distToInt, heq] using h
  · have h := distToInt_le_abs_sub x (round (x + k) - k)
    push_cast at h
    have heq : x - ((round (x + (k : ℝ)) : ℝ) - (k : ℝ)) = x + (k : ℝ) - (round (x + (k : ℝ)) : ℝ) := by ring
    simpa only [distToInt, heq] using h

lemma distToInt_neg (x : ℝ) : distToInt (-x) = distToInt x := by
  apply le_antisymm
  · have h := distToInt_le_abs_sub (-x) (-round x)
    push_cast at h
    have heq : |-x - -(round x : ℝ)| = |x - (round x : ℝ)| := by
      rw [← abs_neg]; congr 1; ring
    simpa only [distToInt, heq] using h
  · have h := distToInt_le_abs_sub x (-round (-x))
    push_cast at h
    have heq : |x - -(round (-x) : ℝ)| = |-x - (round (-x) : ℝ)| := by
      rw [← abs_neg]; congr 1; ring
    simpa only [distToInt, heq] using h

lemma wellSpaced_iff_distToInt {ι : Type*} (s : Finset ι) (α : ι → ℝ) (δ : ℝ) :
    WellSpaced s α δ ↔ ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ distToInt (α i - α j) := by
  constructor
  · intro h i hi j hj hij
    exact h i hi j hj hij (round (α i - α j))
  · intro h i hi j hj hij k
    exact (h i hi j hj hij).trans (distToInt_le_abs_sub (α i - α j) k)

lemma eChar_add (x y : ℝ) : eChar (x + y) = eChar x * eChar y := by
  unfold eChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eChar_int (k : ℤ) : eChar (k : ℝ) = 1 := by
  unfold eChar
  have : (2 : ℂ) * Real.pi * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [Complex.ofReal_intCast, this, Complex.exp_int_mul_two_pi_mul_I]

lemma eChar_add_int (x : ℝ) (k : ℤ) : eChar (x + k) = eChar x := by
  rw [eChar_add, eChar_int, mul_one]

lemma norm_eChar (x : ℝ) : ‖eChar x‖ = 1 := by
  unfold eChar
  have h : (2 : ℂ) * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

lemma conj_eChar (x : ℝ) : starRingEnd ℂ (eChar x) = eChar (-x) := by
  unfold eChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

lemma hasDerivAt_eChar_mul (c t : ℝ) :
    HasDerivAt (fun u : ℝ => eChar (c * u)) ((2 * Real.pi * Complex.I * c) * eChar (c * t)) t := by
  unfold eChar
  have h1 : HasDerivAt (fun u : ℝ => (2 : ℂ) * Real.pi * Complex.I * ((c * u : ℝ) : ℂ))
      ((2 : ℂ) * Real.pi * Complex.I * (c : ℂ)) t := by
    have hmul : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
    have h2 := hmul.const_mul ((2 : ℂ) * Real.pi * Complex.I * (c : ℂ))
    simpa [mul_assoc, Complex.ofReal_mul] using h2
  simpa [mul_comm] using h1.cexp

/-- Orthogonality of additive characters `e(k t)` over `[0, 1]`. -/
theorem integral_eChar_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, eChar ((k : ℝ) * t) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk
    simp [eChar]
  · set c : ℂ := 2 * Real.pi * Complex.I * (k : ℂ)
    have hc : c ≠ 0 := by
      simp [c, Real.pi_ne_zero, Complex.I_ne_zero, hk]
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => eChar ((k : ℝ) * u) / c) (eChar ((k : ℝ) * t)) t := by
      intro t _
      have hd := (hasDerivAt_eChar_mul (k : ℝ) t).div_const c
      simpa [c, mul_div_cancel_left₀ _ hc] using hd
    have hcont : Continuous (fun u : ℝ => eChar ((k : ℝ) * u)) := by
      unfold eChar
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
    have h1 : eChar ((k : ℝ) * 1) = 1 := by rw [mul_one]; exact eChar_int k
    have h0 : eChar ((k : ℝ) * 0) = 1 := by simp [eChar]
    rw [h1, h0, sub_self]

/-- Parseval's identity for finite exponential polynomials on `[0, 1]`. -/
theorem parseval_trig_poly (s : Finset ℤ) (a : ℤ → ℂ) :
    ∫ t in (0 : ℝ)..1, ‖∑ n ∈ s, a n * eChar ((n : ℝ) * t)‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have hcast : ∀ t : ℝ,
      ((‖∑ n ∈ s, a n * eChar ((n : ℝ) * t)‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ s, ∑ m ∈ s, a n * starRingEnd ℂ (a m) * eChar (((n - m : ℤ) : ℝ) * t) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [map_mul, conj_eChar]
    have hexp : eChar ((n : ℝ) * t) * eChar (-((m : ℝ) * t)) = eChar (((n - m : ℤ) : ℝ) * t) := by
      rw [← eChar_add]
      congr 1
      push_cast
      ring
    calc a n * eChar ((n : ℝ) * t) * (starRingEnd ℂ (a m) * eChar (-((m : ℝ) * t)))
        = a n * starRingEnd ℂ (a m) * (eChar ((n : ℝ) * t) * eChar (-((m : ℝ) * t))) := by ring
      _ = a n * starRingEnd ℂ (a m) * eChar (((n - m : ℤ) : ℝ) * t) := by rw [hexp]
  have hint_term : ∀ n m : ℤ,
      IntervalIntegrable (fun t : ℝ => a n * starRingEnd ℂ (a m) * eChar (((n - m : ℤ) : ℝ) * t))
        volume 0 1 := by
    intro n m
    have hc : Continuous (fun t : ℝ => a n * starRingEnd ℂ (a m) * eChar (((n - m : ℤ) : ℝ) * t)) := by
      unfold eChar
      fun_prop
    exact hc.intervalIntegrable 0 1
  have hC : ((∫ t in (0 : ℝ)..1, ‖∑ n ∈ s, a n * eChar ((n : ℝ) * t)‖ ^ 2 : ℝ) : ℂ) =
      ((∑ n ∈ s, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hcast]
    rw [intervalIntegral.integral_finsetSum]
    · trans ∑ n ∈ s, ∑ m ∈ s, a n * starRingEnd ℂ (a m) * (if n - m = 0 then (1 : ℂ) else 0)
      · apply Finset.sum_congr rfl
        intro n _
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro m _
          rw [intervalIntegral.integral_const_mul, integral_eChar_int]
        · intro m _
          exact hint_term n m
      · rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_eq_single n]
        · simp [Complex.mul_conj']
        · intro m _ hmn
          have : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
          simp [this]
        · intro hnot
          exact absurd hn hnot
    · intro n _
      have hc : Continuous (fun t : ℝ => ∑ m ∈ s, a n * starRingEnd ℂ (a m) * eChar (((n - m : ℤ) : ℝ) * t)) := by
        unfold eChar
        fun_prop
      exact hc.intervalIntegrable 0 1
  exact Complex.ofReal_injective hC

/-- **Gallagher's 1D Sobolev Inequality:** for any `C^1` function `f : ℝ → ℂ` on `[x - h, x + h]`
(`h > 0`),
`‖f x‖^2 ≤ (1 / (2 h)) ∫_{x-h}^{x+h} ‖f t‖^2 dt + ∫_{x-h}^{x+h} ‖f t‖ ‖f' t‖ dt`. -/
theorem gallagher_sobolev_sq (f f' : ℝ → ℂ) (x h : ℝ) (hh : 0 < h)
    (hf : ∀ t ∈ Set.Icc (x - h) (x + h), HasDerivAt f (f' t) t)
    (hf'_cont : ContinuousOn f' (Set.Icc (x - h) (x + h))) :
    ‖f x‖ ^ 2 ≤
      (1 / (2 * h)) * (∫ t in (x - h)..(x + h), ‖f t‖ ^ 2) +
        ∫ t in (x - h)..(x + h), ‖f t‖ * ‖f' t‖ := by
  set u : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  set u' : ℝ → ℝ := fun t => 2 * ((f t).re * (f' t).re + (f t).im * (f' t).im)
  have hf_cont : ContinuousOn f (Set.Icc (x - h) (x + h)) := by
    intro t ht
    exact (hf t ht).continuousAt.continuousWithinAt
  have hnorm_sq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
  have hu_eq : ∀ t, u t = (f t).re ^ 2 + (f t).im ^ 2 := fun t => hnorm_sq (f t)
  have hu_deriv : ∀ t ∈ Set.Icc (x - h) (x + h), HasDerivAt u (u' t) t := by
    intro t ht
    have hre : HasDerivAt (fun s => (f s).re) (f' t).re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht)
    have him : HasDerivAt (fun s => (f s).im) (f' t).im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hf t ht)
    have hsum := (hre.pow 2).fun_add (him.pow 2)
    have hfun : (fun s => (f s).re ^ 2 + (f s).im ^ 2) = u := by
      funext s; exact (hu_eq s).symm
    change HasDerivAt (fun s => (f s).re ^ 2 + (f s).im ^ 2) _ t at hsum
    rw [hfun] at hsum
    convert hsum using 1
    simp [u']
    ring
  have hu'_bound : ∀ t, |u' t| ≤ 2 * (‖f t‖ * ‖f' t‖) := by
    intro t
    have hcs : ((f t).re * (f' t).re + (f t).im * (f' t).im) ^ 2 ≤ (‖f t‖ * ‖f' t‖) ^ 2 := by
      rw [mul_pow, hnorm_sq (f t), hnorm_sq (f' t)]
      nlinarith [sq_nonneg ((f t).re * (f' t).im - (f t).im * (f' t).re)]
    have hnn : 0 ≤ ‖f t‖ * ‖f' t‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have habs : |(f t).re * (f' t).re + (f t).im * (f' t).im| ≤ ‖f t‖ * ‖f' t‖ := by
      nlinarith [sq_abs ((f t).re * (f' t).re + (f t).im * (f' t).im),
        abs_nonneg ((f t).re * (f' t).re + (f t).im * (f' t).im)]
    calc |u' t| = 2 * |(f t).re * (f' t).re + (f t).im * (f' t).im| := by
          simp [u', abs_mul]
      _ ≤ 2 * (‖f t‖ * ‖f' t‖) := by linarith
  have hu_cont : ContinuousOn u (Set.Icc (x - h) (x + h)) :=
    (hf_cont.norm).pow 2
  have hu'_cont : ContinuousOn u' (Set.Icc (x - h) (x + h)) := by
    have hre1 : ContinuousOn (fun t => (f t).re) (Set.Icc (x - h) (x + h)) :=
      Complex.continuous_re.comp_continuousOn hf_cont
    have him1 : ContinuousOn (fun t => (f t).im) (Set.Icc (x - h) (x + h)) :=
      Complex.continuous_im.comp_continuousOn hf_cont
    have hre2 : ContinuousOn (fun t => (f' t).re) (Set.Icc (x - h) (x + h)) :=
      Complex.continuous_re.comp_continuousOn hf'_cont
    have him2 : ContinuousOn (fun t => (f' t).im) (Set.Icc (x - h) (x + h)) :=
      Complex.continuous_im.comp_continuousOn hf'_cont
    exact continuousOn_const.mul ((hre1.mul hre2).add (him1.mul him2))
  have hprod_cont : ContinuousOn (fun t => ‖f t‖ * ‖f' t‖) (Set.Icc (x - h) (x + h)) :=
    hf_cont.norm.mul hf'_cont.norm
  have hsubL : Set.Icc (x - h) x ⊆ Set.Icc (x - h) (x + h) :=
    Set.Icc_subset_Icc_right (by linarith)
  have hsubR : Set.Icc x (x + h) ⊆ Set.Icc (x - h) (x + h) :=
    Set.Icc_subset_Icc_left (by linarith)
  have huIccL : Set.uIcc (x - h) x = Set.Icc (x - h) x := Set.uIcc_of_le (by linarith)
  have huIccR : Set.uIcc x (x + h) = Set.Icc x (x + h) := Set.uIcc_of_le (by linarith)
  -- Left half: g₁(t) = (t - (x - h)) * u(t)
  have hleft_eq :
      h * u x = ∫ t in (x - h)..x, (u t + (t - (x - h)) * u' t) := by
    have hderiv1 : ∀ t ∈ Set.uIcc (x - h) x,
        HasDerivAt (fun s => (s - (x - h)) * u s) (u t + (t - (x - h)) * u' t) t := by
      intro t ht
      rw [huIccL] at ht
      have hlin : HasDerivAt (fun s => s - (x - h)) 1 t := (hasDerivAt_id t).sub_const (x - h)
      simpa [one_mul] using hlin.fun_mul (hu_deriv t (hsubL ht))
    have hcont1 : ContinuousOn (fun t => u t + (t - (x - h)) * u' t) (Set.uIcc (x - h) x) := by
      rw [huIccL]
      exact (hu_cont.mono hsubL).add ((continuousOn_id.sub continuousOn_const).mul (hu'_cont.mono hsubL))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv1 hcont1.intervalIntegrable]
    ring
  have hleft_le :
      h * u x ≤ (∫ t in (x - h)..x, u t) + 2 * h * (∫ t in (x - h)..x, ‖f t‖ * ‖f' t‖) := by
    rw [hleft_eq]
    have hi_u : IntervalIntegrable u volume (x - h) x :=
      (hu_cont.mono hsubL).intervalIntegrable_of_Icc (by linarith)
    have hi_prod : IntervalIntegrable (fun t => ‖f t‖ * ‖f' t‖) volume (x - h) x :=
      (hprod_cont.mono hsubL).intervalIntegrable_of_Icc (by linarith)
    have hi_lhs : IntervalIntegrable (fun t => u t + (t - (x - h)) * u' t) volume (x - h) x :=
      ((hu_cont.mono hsubL).add ((continuousOn_id.sub continuousOn_const).mul (hu'_cont.mono hsubL))).intervalIntegrable_of_Icc (by linarith)
    have hi_rhs : IntervalIntegrable (fun t => u t + 2 * h * (‖f t‖ * ‖f' t‖)) volume (x - h) x :=
      hi_u.add (hi_prod.const_mul (2 * h))
    calc ∫ t in (x - h)..x, (u t + (t - (x - h)) * u' t)
        ≤ ∫ t in (x - h)..x, (u t + 2 * h * (‖f t‖ * ‖f' t‖)) := by
          apply intervalIntegral.integral_mono_on (by linarith) hi_lhs hi_rhs
          intro t ht
          have ht0 : 0 ≤ t - (x - h) := by linarith [ht.1]
          have hth : t - (x - h) ≤ h := by linarith [ht.2]
          have hstep : (t - (x - h)) * u' t ≤ 2 * h * (‖f t‖ * ‖f' t‖) := by
            calc (t - (x - h)) * u' t ≤ (t - (x - h)) * |u' t| :=
                  mul_le_mul_of_nonneg_left (le_abs_self _) ht0
              _ ≤ h * |u' t| := mul_le_mul_of_nonneg_right hth (abs_nonneg _)
              _ ≤ h * (2 * (‖f t‖ * ‖f' t‖)) := mul_le_mul_of_nonneg_left (hu'_bound t) hh.le
              _ = 2 * h * (‖f t‖ * ‖f' t‖) := by ring
          linarith
      _ = (∫ t in (x - h)..x, u t) + 2 * h * (∫ t in (x - h)..x, ‖f t‖ * ‖f' t‖) := by
          rw [intervalIntegral.integral_add hi_u (hi_prod.const_mul (2 * h)),
              intervalIntegral.integral_const_mul]
  -- Right half: g₂(t) = ((x + h) - t) * u(t)
  have hright_eq :
      h * u x = ∫ t in x..(x + h), (u t - ((x + h) - t) * u' t) := by
    have hderiv2 : ∀ t ∈ Set.uIcc x (x + h),
        HasDerivAt (fun s => ((x + h) - s) * u s) (-u t + ((x + h) - t) * u' t) t := by
      intro t ht
      rw [huIccR] at ht
      have hlin : HasDerivAt (fun s => (x + h) - s) (-1) t := by
        simpa using (hasDerivAt_const t (x + h)).fun_sub (hasDerivAt_id t)
      simpa using hlin.fun_mul (hu_deriv t (hsubR ht))
    have hcont2 : ContinuousOn (fun t => -u t + ((x + h) - t) * u' t) (Set.uIcc x (x + h)) := by
      rw [huIccR]
      exact (hu_cont.mono hsubR).neg.add ((continuousOn_const.sub continuousOn_id).mul (hu'_cont.mono hsubR))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv2 hcont2.intervalIntegrable
    have hneg : ∫ t in x..(x + h), (u t - ((x + h) - t) * u' t) =
        -(∫ t in x..(x + h), (-u t + ((x + h) - t) * u' t)) := by
      rw [← intervalIntegral.integral_neg]
      congr 1; funext t; ring
    rw [hneg, hftc]
    ring
  have hright_le :
      h * u x ≤ (∫ t in x..(x + h), u t) + 2 * h * (∫ t in x..(x + h), ‖f t‖ * ‖f' t‖) := by
    rw [hright_eq]
    have hi_u : IntervalIntegrable u volume x (x + h) :=
      (hu_cont.mono hsubR).intervalIntegrable_of_Icc (by linarith)
    have hi_prod : IntervalIntegrable (fun t => ‖f t‖ * ‖f' t‖) volume x (x + h) :=
      (hprod_cont.mono hsubR).intervalIntegrable_of_Icc (by linarith)
    have hi_lhs : IntervalIntegrable (fun t => u t - ((x + h) - t) * u' t) volume x (x + h) :=
      ((hu_cont.mono hsubR).sub ((continuousOn_const.sub continuousOn_id).mul (hu'_cont.mono hsubR))).intervalIntegrable_of_Icc (by linarith)
    have hi_rhs : IntervalIntegrable (fun t => u t + 2 * h * (‖f t‖ * ‖f' t‖)) volume x (x + h) :=
      hi_u.add (hi_prod.const_mul (2 * h))
    calc ∫ t in x..(x + h), (u t - ((x + h) - t) * u' t)
        ≤ ∫ t in x..(x + h), (u t + 2 * h * (‖f t‖ * ‖f' t‖)) := by
          apply intervalIntegral.integral_mono_on (by linarith) hi_lhs hi_rhs
          intro t ht
          have ht0 : 0 ≤ (x + h) - t := by linarith [ht.2]
          have hth : (x + h) - t ≤ h := by linarith [ht.1]
          have hstep : -(((x + h) - t) * u' t) ≤ 2 * h * (‖f t‖ * ‖f' t‖) := by
            calc -(((x + h) - t) * u' t) = ((x + h) - t) * (-u' t) := by ring
              _ ≤ ((x + h) - t) * |u' t| := mul_le_mul_of_nonneg_left (neg_le_abs _) ht0
              _ ≤ h * |u' t| := mul_le_mul_of_nonneg_right hth (abs_nonneg _)
              _ ≤ h * (2 * (‖f t‖ * ‖f' t‖)) := mul_le_mul_of_nonneg_left (hu'_bound t) hh.le
              _ = 2 * h * (‖f t‖ * ‖f' t‖) := by ring
          linarith
      _ = (∫ t in x..(x + h), u t) + 2 * h * (∫ t in x..(x + h), ‖f t‖ * ‖f' t‖) := by
          rw [intervalIntegral.integral_add hi_u (hi_prod.const_mul (2 * h)),
              intervalIntegral.integral_const_mul]
  -- Combine left and right halves
  have hi_uL : IntervalIntegrable u volume (x - h) x :=
    (hu_cont.mono hsubL).intervalIntegrable_of_Icc (by linarith)
  have hi_uR : IntervalIntegrable u volume x (x + h) :=
    (hu_cont.mono hsubR).intervalIntegrable_of_Icc (by linarith)
  have hi_pL : IntervalIntegrable (fun t => ‖f t‖ * ‖f' t‖) volume (x - h) x :=
    (hprod_cont.mono hsubL).intervalIntegrable_of_Icc (by linarith)
  have hi_pR : IntervalIntegrable (fun t => ‖f t‖ * ‖f' t‖) volume x (x + h) :=
    (hprod_cont.mono hsubR).intervalIntegrable_of_Icc (by linarith)
  have hadd_u := intervalIntegral.integral_add_adjacent_intervals hi_uL hi_uR
  have hadd_p := intervalIntegral.integral_add_adjacent_intervals hi_pL hi_pR
  have hcomb : 2 * h * u x ≤
      (∫ t in (x - h)..(x + h), u t) + 2 * h * (∫ t in (x - h)..(x + h), ‖f t‖ * ‖f' t‖) := by
    calc 2 * h * u x = h * u x + h * u x := by ring
      _ ≤ ((∫ t in (x - h)..x, u t) + 2 * h * (∫ t in (x - h)..x, ‖f t‖ * ‖f' t‖)) +
          ((∫ t in x..(x + h), u t) + 2 * h * (∫ t in x..(x + h), ‖f t‖ * ‖f' t‖)) :=
            add_le_add hleft_le hright_le
      _ = ((∫ t in (x - h)..x, u t) + ∫ t in x..(x + h), u t) +
          2 * h * ((∫ t in (x - h)..x, ‖f t‖ * ‖f' t‖) + ∫ t in x..(x + h), ‖f t‖ * ‖f' t‖) := by ring
      _ = (∫ t in (x - h)..(x + h), u t) + 2 * h * (∫ t in (x - h)..(x + h), ‖f t‖ * ‖f' t‖) := by
          rw [hadd_u, hadd_p]
  have h2h : 0 < 2 * h := by linarith
  have hdiv : u x ≤ (1 / (2 * h)) * (∫ t in (x - h)..(x + h), u t) +
      ∫ t in (x - h)..(x + h), ‖f t‖ * ‖f' t‖ := by
    rw [one_div]
    have := mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr h2h.le)
    rw [inv_mul_cancel_left₀ h2h.ne', mul_add, inv_mul_cancel_left₀ h2h.ne'] at this
    exact this
  exact hdiv

/-- Helper: for a continuous nonnegative 1-periodic function `g : ℝ → ℝ` and a `δ`-well-spaced
finite set of points `α` (`0 < δ ≤ 1`), the sum of local integrals over `[α_r - δ/2, α_r + δ/2]`
is bounded by `∫_0^1 g`. -/
theorem sum_intervalIntegral_le_of_wellSpaced {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hws : WellSpaced s α δ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (hg_nn : ∀ t, 0 ≤ g t)
    (hg_per : Function.Periodic g 1) :
    ∑ r ∈ s, ∫ t in (α r - δ / 2)..(α r + δ / 2), g t ≤ ∫ t in (0 : ℝ)..1, g t := by
  by_cases hs : s.Nonempty
  · -- Step 1: shift each integral to `[Int.fract (α r) - δ/2, Int.fract (α r) + δ/2]`
    have hshift : ∀ r ∈ s,
        ∫ t in (α r - δ / 2)..(α r + δ / 2), g t =
          ∫ t in (Int.fract (α r) - δ / 2)..(Int.fract (α r) + δ / 2), g t := by
      intro r _
      have hα : α r = Int.fract (α r) + (⌊α r⌋ : ℝ) := by
        linarith [Int.fract_add_floor (α r)]
      have h1 : α r - δ / 2 = (Int.fract (α r) - δ / 2) + (⌊α r⌋ : ℝ) := by linarith
      have h2 : α r + δ / 2 = (Int.fract (α r) + δ / 2) + (⌊α r⌋ : ℝ) := by linarith
      rw [h1, h2, ← intervalIntegral.integral_comp_add_right]
      congr 1; funext t
      simpa [mul_one] using hg_per.int_mul ⌊α r⌋ t
    rw [Finset.sum_congr rfl hshift]
    -- Step 2: `r ↦ Int.fract (α r)` is injective on `s`
    have hinj : Set.InjOn (fun r => Int.fract (α r)) (s : Set ι) := by
      intro i hi j hj heq
      by_contra hne
      have hdiff : α i - α j - ((⌊α i⌋ - ⌊α j⌋ : ℤ) : ℝ) = 0 := by
        have hi' : Int.fract (α i) = α i - ⌊α i⌋ := rfl
        have hj' : Int.fract (α j) = α j - ⌊α j⌋ := rfl
        push_cast
        linarith
      have hle := hws i hi j hj hne (⌊α i⌋ - ⌊α j⌋)
      rw [hdiff, abs_zero] at hle
      linarith
    set T : Finset ℝ := s.image (fun r => Int.fract (α r))
    have hsumT :
        ∑ r ∈ s, ∫ t in (Int.fract (α r) - δ / 2)..(Int.fract (α r) + δ / 2), g t =
          ∑ y ∈ T, ∫ t in (y - δ / 2)..(y + δ / 2), g t :=
      (Finset.sum_image (f := fun y => ∫ t in (y - δ / 2)..(y + δ / 2), g t) hinj).symm
    rw [hsumT]
    -- Step 3: Sort `T` in strictly increasing order `y 0 < y 1 < ... < y (m - 1)`
    set L : List ℝ := T.sort (· ≤ ·)
    have hL_len : 0 < L.length := by
      rw [Finset.length_sort]
      exact (hs.image _).card_pos
    have hL_nodup : L.Nodup := Finset.sort_nodup T (· ≤ ·)
    have hL_sorted : L.Pairwise (· < ·) :=
      ((Finset.pairwise_sort T (· ≤ ·)).and hL_nodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
    have hL_toFinset : L.toFinset = T := by
      ext y; simp [L]
    have hsumL :
        ∑ y ∈ T, ∫ t in (y - δ / 2)..(y + δ / 2), g t =
          ∑ i ∈ Finset.range L.length,
            if hi : i < L.length then ∫ t in (L[i] - δ / 2)..(L[i] + δ / 2), g t else 0 := by
      rw [← hL_toFinset, List.sum_toFinset _ hL_nodup]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => if hi : i < L.length then ∫ t in (L[i] - δ / 2)..(L[i] + δ / 2), g t else 0)]
      have hmap : List.map (fun y => ∫ t in (y - δ / 2)..(y + δ / 2), g t) L =
          List.ofFn (fun i : Fin L.length => ∫ t in (L[i.val] - δ / 2)..(L[i.val] + δ / 2), g t) := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2; simp
      rw [hmap, List.sum_ofFn]
      apply Finset.sum_congr rfl
      intro i _; simp [i.isLt]
    rw [hsumL]
    -- Step 4: Well-spacing of sorted elements `L[i]`
    have hmem_T : ∀ (i : ℕ) (hi : i < L.length), L[i] ∈ T := by
      intro i hi
      exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
    have hgap : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j → δ ≤ L[j] - L[i] := by
      intro i j hi hj hij
      rcases Finset.mem_image.mp (hmem_T i hi) with ⟨ri, hri, hri_eq⟩
      rcases Finset.mem_image.mp (hmem_T j hj) with ⟨rj, hrj, hrj_eq⟩
      have hlt : L[i] < L[j] := List.pairwise_iff_getElem.mp hL_sorted i j hi hj hij
      have hne : rj ≠ ri := by intro heq; subst heq; linarith
      have hws' := hws rj hrj ri hri hne (⌊α rj⌋ - ⌊α ri⌋)
      have heq : α rj - α ri - ((⌊α rj⌋ - ⌊α ri⌋ : ℤ) : ℝ) = L[j] - L[i] := by
        have h1 : Int.fract (α rj) = α rj - ⌊α rj⌋ := rfl
        have h2 : Int.fract (α ri) = α ri - ⌊α ri⌋ := rfl
        push_cast
        linarith
      rw [heq, abs_of_pos (by linarith)] at hws'
      exact hws'
    have hwrap : δ ≤ L[0] + 1 - L[L.length - 1] := by
      by_cases hm : L.length = 1
      · have hidx : L.length - 1 = 0 := by omega
        simp only [hidx]
        linarith
      · have h0lt : (0 : ℕ) < L.length - 1 := by omega
        have hlast_lt : L.length - 1 < L.length := by omega
        rcases Finset.mem_image.mp (hmem_T 0 hL_len) with ⟨r0, hr0, hr0_eq⟩
        rcases Finset.mem_image.mp (hmem_T (L.length - 1) hlast_lt) with ⟨r1, hr1, hr1_eq⟩
        have hlt : L[0] < L[L.length - 1] :=
          List.pairwise_iff_getElem.mp hL_sorted 0 (L.length - 1) hL_len hlast_lt h0lt
        have hne : r0 ≠ r1 := by intro heq; subst heq; linarith
        have hws' := hws r0 hr0 r1 hr1 hne (⌊α r0⌋ - ⌊α r1⌋ - 1)
        have hlt1 : L[L.length - 1] < 1 := by rw [← hr1_eq]; exact Int.fract_lt_one _
        have h0nn : (0 : ℝ) ≤ L[0] := by rw [← hr0_eq]; exact Int.fract_nonneg _
        have heq : α r0 - α r1 - ((⌊α r0⌋ - ⌊α r1⌋ - 1 : ℤ) : ℝ) = L[0] + 1 - L[L.length - 1] := by
          have h1 : Int.fract (α r0) = α r0 - ⌊α r0⌋ := rfl
          have h2 : Int.fract (α r1) = α r1 - ⌊α r1⌋ := rfl
          push_cast
          linarith
        rw [heq, abs_of_pos (by linarith)] at hws'
        exact hws'
    -- Step 5: Induction over `k ∈ [1, L.length]` for disjoint subintervals of `[L[0] - δ/2, L[k-1] + δ/2]`
    have hind : ∀ k : ℕ, (hk0 : 0 < k) → (hk : k ≤ L.length) →
        ∑ i ∈ Finset.range k,
          (if hi : i < L.length then ∫ t in (L[i] - δ / 2)..(L[i] + δ / 2), g t else 0) ≤
        ∫ t in (L[0] - δ / 2)..(L[k - 1]'(by omega) + δ / 2), g t := by
      intro k
      induction k with
      | zero => intro hk0; omega
      | succ k ih =>
        intro _ hk
        by_cases hk0 : k = 0
        · subst hk0
          simp [hL_len]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          rw [Finset.sum_range_succ, dif_pos (by omega : k < L.length)]
          have hih := ih hkpos (by omega)
          have hgap_k : δ ≤ L[k]'(by omega) - L[k - 1]'(by omega) :=
            hgap (k - 1) k (by omega) (by omega) (by omega)
          have hmid_le : L[k - 1]'(by omega) + δ / 2 ≤ L[k]'(by omega) - δ / 2 := by linarith
          have hgap_int_nn : (0 : ℝ) ≤ ∫ t in (L[k - 1]'(by omega) + δ / 2)..(L[k]'(by omega) - δ / 2), g t :=
            intervalIntegral.integral_nonneg hmid_le (fun t _ => hg_nn t)
          have hstep1 :
              ∫ t in (L[0] - δ / 2)..(L[k - 1]'(by omega) + δ / 2), g t ≤
                ∫ t in (L[0] - δ / 2)..(L[k]'(by omega) - δ / 2), g t := by
            have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
              (hg_cont.intervalIntegrable (L[0] - δ / 2) (L[k - 1]'(by omega) + δ / 2))
              (hg_cont.intervalIntegrable (L[k - 1]'(by omega) + δ / 2) (L[k]'(by omega) - δ / 2))
            linarith
          have hadd2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            (hg_cont.intervalIntegrable (L[0] - δ / 2) (L[k]'(by omega) - δ / 2))
            (hg_cont.intervalIntegrable (L[k]'(by omega) - δ / 2) (L[k]'(by omega) + δ / 2))
          simpa using (add_le_add (hih.trans hstep1) le_rfl).trans_eq hadd2
    have htotal := hind L.length hL_len le_rfl
    have hend_le : L[L.length - 1]'(by omega) + δ / 2 ≤ (L[0] - δ / 2) + 1 := by linarith
    have htail_nn : (0 : ℝ) ≤ ∫ t in (L[L.length - 1]'(by omega) + δ / 2)..((L[0] - δ / 2) + 1), g t :=
      intervalIntegral.integral_nonneg (μ := volume) hend_le (fun t _ => hg_nn t)
    have hadd_end := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hg_cont.intervalIntegrable (L[0] - δ / 2) (L[L.length - 1]'(by omega) + δ / 2))
      (hg_cont.intervalIntegrable (L[L.length - 1]'(by omega) + δ / 2) ((L[0] - δ / 2) + 1))
    have hper_eq : ∫ t in (L[0] - δ / 2)..((L[0] - δ / 2) + 1), g t = ∫ t in (0 : ℝ)..1, g t := by
      set a := L[0] - δ / 2
      have ha : a = Int.fract a + (⌊a⌋ : ℝ) := by linarith [Int.fract_add_floor a]
      have h1 : ∫ t in a..(a + 1), g t = ∫ t in Int.fract a..(Int.fract a + 1), g t := by
        have ha1 : a + 1 = (Int.fract a + 1) + (⌊a⌋ : ℝ) := by linarith
        calc ∫ t in a..(a + 1), g t
            = ∫ t in (Int.fract a + (⌊a⌋ : ℝ))..((Int.fract a + 1) + (⌊a⌋ : ℝ)), g t := by
              rw [← ha, ← ha1]
          _ = ∫ t in Int.fract a..(Int.fract a + 1), g (t + (⌊a⌋ : ℝ)) :=
              (intervalIntegral.integral_comp_add_right g (⌊a⌋ : ℝ)).symm
          _ = ∫ t in Int.fract a..(Int.fract a + 1), g t := by
              congr 1; funext t; simpa [mul_one] using hg_per.int_mul ⌊a⌋ t
      have h2 : ∫ t in Int.fract a..(Int.fract a + 1), g t =
          (∫ t in Int.fract a..1, g t) + ∫ t in (1 : ℝ)..(Int.fract a + 1), g t :=
        (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hg_cont.intervalIntegrable _ _) (hg_cont.intervalIntegrable _ _)).symm
      have h3 : ∫ t in (1 : ℝ)..(Int.fract a + 1), g t = ∫ t in (0 : ℝ)..Int.fract a, g t := by
        calc ∫ t in (1 : ℝ)..(Int.fract a + 1), g t
            = ∫ t in ((0 : ℝ) + 1)..(Int.fract a + 1), g t := by norm_num
          _ = ∫ t in (0 : ℝ)..Int.fract a, g (t + 1) :=
              (intervalIntegral.integral_comp_add_right g 1).symm
          _ = ∫ t in (0 : ℝ)..Int.fract a, g t := by
              congr 1; funext t; exact hg_per t
      have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hg_cont.intervalIntegrable (0 : ℝ) (Int.fract a))
        (hg_cont.intervalIntegrable (Int.fract a) 1)
      linarith
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => hg_nn t)

/-- **Analytic Large Sieve Inequality (Gallagher's Elementary Proof, integer frequency interval):**
For any `δ`-well-spaced points `α : ι → ℝ` (`0 < δ ≤ 1`), integer `M : ℤ`, length `N : ℕ`,
and complex coefficients `a : ℤ → ℂ`,
`∑ r ∈ s, ‖∑ n ∈ Finset.Icc M (M + N - 1), a n * e(n α_r)‖^2 ≤ (π N + 1 / δ) ∑ n, ‖a n‖^2`. -/
theorem large_sieve_gallagher {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hws : WellSpaced s α δ)
    (M : ℤ) (N : ℕ) (a : ℤ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Finset.Icc M (M + (N : ℤ) - 1), a n * eChar ((n : ℝ) * α r)‖ ^ 2 ≤
      (Real.pi * (N : ℝ) + 1 / δ) * ∑ n ∈ Finset.Icc M (M + (N : ℤ) - 1), ‖a n‖ ^ 2 := by
  set I : Finset ℤ := Finset.Icc M (M + (N : ℤ) - 1)
  by_cases hN : N = 0
  · subst hN
    have hI : I = ∅ := by
      ext n; simp [I]
    simp [hI]
  · have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    set c : ℝ := (M : ℝ) + ((N : ℝ) - 1) / 2
    set S : ℝ → ℂ := fun t => ∑ n ∈ I, a n * eChar ((n : ℝ) * t)
    set f : ℝ → ℂ := fun t => eChar (-(c * t)) * S t
    set S' : ℝ → ℂ := fun t => ∑ n ∈ I, ((2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * a n) * eChar ((n : ℝ) * t)
    set f' : ℝ → ℂ := fun t => eChar (-(c * t)) * S' t
    -- 1. `f t = ∑ n ∈ I, a n * e((n - c) * t)` and `HasDerivAt f (f' t) t`
    have hf_eq : ∀ t : ℝ, f t = ∑ n ∈ I, a n * eChar (((n : ℝ) - c) * t) := by
      intro t
      simp only [f, S, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      calc eChar (-(c * t)) * (a n * eChar ((n : ℝ) * t))
          = a n * (eChar (-(c * t)) * eChar ((n : ℝ) * t)) := by ring
        _ = a n * eChar (((n : ℝ) - c) * t) := by
            rw [← eChar_add]; congr 2; ring
    have hf'_eq : ∀ t : ℝ, f' t = ∑ n ∈ I, (2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * (a n * eChar (((n : ℝ) - c) * t)) := by
      intro t
      simp only [f', S', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      calc eChar (-(c * t)) * ((2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ) * a n) * eChar ((n : ℝ) * t))
          = (2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * (a n * (eChar (-(c * t)) * eChar ((n : ℝ) * t))) := by ring
        _ = (2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * (a n * eChar (((n : ℝ) - c) * t)) := by
            rw [← eChar_add]; congr 3; ring
    have hf_deriv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
      intro t
      have hsum : HasDerivAt (fun u : ℝ => ∑ n ∈ I, a n * eChar (((n : ℝ) - c) * u))
          (∑ n ∈ I, a n * ((2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * eChar (((n : ℝ) - c) * t))) t := by
        apply HasDerivAt.fun_sum
        intro n _
        exact (hasDerivAt_eChar_mul ((n : ℝ) - c) t).const_mul (a n)
      have hfun : (fun u : ℝ => ∑ n ∈ I, a n * eChar (((n : ℝ) - c) * u)) = f := by
        funext u; exact (hf_eq u).symm
      rw [hfun] at hsum
      convert hsum using 1
      rw [hf'_eq]
      apply Finset.sum_congr rfl
      intro n _; ring
    -- 2. Norms & 1-periodicity
    have hnorm_f : ∀ t : ℝ, ‖f t‖ = ‖S t‖ := by
      intro t; simp [f, norm_eChar]
    have hnorm_f' : ∀ t : ℝ, ‖f' t‖ = ‖S' t‖ := by
      intro t; simp [f', norm_eChar]
    have hS_per : Function.Periodic S 1 := by
      intro t
      simp only [S]
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      have : (n : ℝ) * (t + 1) = (n : ℝ) * t + (n : ℤ) := by ring
      rw [this, eChar_add_int]
    have hS'_per : Function.Periodic S' 1 := by
      intro t
      simp only [S']
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      have : (n : ℝ) * (t + 1) = (n : ℝ) * t + (n : ℤ) := by ring
      rw [this, eChar_add_int]
    have hcont_S : Continuous S := by
      simp only [S, eChar]; fun_prop
    have hcont_S' : Continuous S' := by
      simp only [S', eChar]; fun_prop
    have hcont_f' : Continuous f' := by
      simp only [f', S', eChar]; fun_prop
    -- 3. Apply Gallagher Sobolev at each `α r`
    have hpoint : ∀ r ∈ s,
        ‖S (α r)‖ ^ 2 ≤
          (1 / δ) * (∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2) +
            ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖S' t‖ := by
      intro r _
      have hsob := gallagher_sobolev_sq f f' (α r) (δ / 2) (by linarith)
        (fun t _ => hf_deriv t) hcont_f'.continuousOn
      have h2h : 2 * (δ / 2) = δ := by ring
      rw [h2h] at hsob
      simpa only [hnorm_f, hnorm_f'] using hsob
    -- 4. Sum over `r ∈ s` and apply disjoint periodic integral lemma
    have hsum_sob :
        ∑ r ∈ s, ‖S (α r)‖ ^ 2 ≤
          (1 / δ) * (∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2) +
            ∫ t in (0 : ℝ)..1, ‖S t‖ * ‖S' t‖ := by
      calc ∑ r ∈ s, ‖S (α r)‖ ^ 2
          ≤ ∑ r ∈ s, ((1 / δ) * (∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2) +
              ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖S' t‖) :=
            Finset.sum_le_sum hpoint
        _ = (1 / δ) * (∑ r ∈ s, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ ^ 2) +
            ∑ r ∈ s, ∫ t in (α r - δ / 2)..(α r + δ / 2), ‖S t‖ * ‖S' t‖ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ (1 / δ) * (∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2) +
            ∫ t in (0 : ℝ)..1, ‖S t‖ * ‖S' t‖ := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact sum_intervalIntegral_le_of_wellSpaced s α δ hδ0 hδ1 hws
                (fun t => ‖S t‖ ^ 2) (hcont_S.norm.pow 2) (fun t => sq_nonneg _)
                (fun t => by simp [hS_per t])
            · exact sum_intervalIntegral_le_of_wellSpaced s α δ hδ0 hδ1 hws
                (fun t => ‖S t‖ * ‖S' t‖) (hcont_S.norm.mul hcont_S'.norm)
                (fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _))
                (fun t => by simp [hS_per t, hS'_per t])
    -- 5. Pointwise AM-GM with `λ = π * N > 0`
    set lam : ℝ := Real.pi * (N : ℝ)
    have hlam : 0 < lam := mul_pos Real.pi_pos hNpos
    have hcross :
        ∫ t in (0 : ℝ)..1, ‖S t‖ * ‖S' t‖ ≤
          (lam / 2) * (∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2) +
            (1 / (2 * lam)) * (∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2) := by
      have hi1 : IntervalIntegrable (fun t => ‖S t‖ * ‖S' t‖) volume 0 1 :=
        (hcont_S.norm.mul hcont_S'.norm).intervalIntegrable 0 1
      have hiS : IntervalIntegrable (fun t => ‖S t‖ ^ 2) volume 0 1 :=
        (hcont_S.norm.pow 2).intervalIntegrable 0 1
      have hiS' : IntervalIntegrable (fun t => ‖S' t‖ ^ 2) volume 0 1 :=
        (hcont_S'.norm.pow 2).intervalIntegrable 0 1
      have hi2 : IntervalIntegrable (fun t => (lam / 2) * ‖S t‖ ^ 2 + (1 / (2 * lam)) * ‖S' t‖ ^ 2) volume 0 1 :=
        (hiS.const_mul _).add (hiS'.const_mul _)
      calc ∫ t in (0 : ℝ)..1, ‖S t‖ * ‖S' t‖
          ≤ ∫ t in (0 : ℝ)..1, ((lam / 2) * ‖S t‖ ^ 2 + (1 / (2 * lam)) * ‖S' t‖ ^ 2) := by
            apply intervalIntegral.integral_mono_on (by norm_num) hi1 hi2
            intro t _
            have hsq : 0 ≤ (lam * ‖S t‖ - ‖S' t‖) ^ 2 := sq_nonneg _
            have h2l : 0 < 2 * lam := by linarith
            have hmul : 2 * lam * (‖S t‖ * ‖S' t‖) ≤ lam ^ 2 * ‖S t‖ ^ 2 + ‖S' t‖ ^ 2 := by nlinarith
            have hdiv := mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr h2l.le)
            have hL : (2 * lam)⁻¹ * (2 * lam * (‖S t‖ * ‖S' t‖)) = ‖S t‖ * ‖S' t‖ := by
              field_simp [hlam.ne']
            have hR : (2 * lam)⁻¹ * (lam ^ 2 * ‖S t‖ ^ 2 + ‖S' t‖ ^ 2) =
                (lam / 2) * ‖S t‖ ^ 2 + (1 / (2 * lam)) * ‖S' t‖ ^ 2 := by
              field_simp [hlam.ne']
            linarith
        _ = (lam / 2) * (∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2) +
            (1 / (2 * lam)) * (∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2) := by
            rw [intervalIntegral.integral_add (hiS.const_mul _) (hiS'.const_mul _),
                intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    -- 6. Parseval for `S` and `S'`
    have hparseval_S : ∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2 = ∑ n ∈ I, ‖a n‖ ^ 2 :=
      parseval_trig_poly I a
    have hparseval_S' :
        ∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2 =
          ∑ n ∈ I, ‖(2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * a n‖ ^ 2 :=
      parseval_trig_poly I (fun n => (2 * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)) * a n)
    have hS'_bound :
        ∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2 ≤ lam ^ 2 * ∑ n ∈ I, ‖a n‖ ^ 2 := by
      rw [hparseval_S', Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn1 : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) ≤ (M : ℝ) + (N : ℝ) - 1 := by
        have : (n : ℝ) ≤ ((M + (N : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hn.2
        push_cast at this
        linarith
      have hdist : |(n : ℝ) - c| ≤ (N : ℝ) / 2 := by
        rw [abs_le]
        simp only [c]
        constructor <;> linarith
      have hcoeff_norm : ‖(2 : ℂ) * Real.pi * Complex.I * (((n : ℝ) - c : ℝ) : ℂ)‖ =
          2 * Real.pi * |(n : ℝ) - c| := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I,
          mul_one, Complex.norm_ofNat, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [norm_mul, mul_pow, hcoeff_norm]
      have hsq_le : (2 * Real.pi * |(n : ℝ) - c|) ^ 2 ≤ lam ^ 2 := by
        have h1 : 0 ≤ 2 * Real.pi * |(n : ℝ) - c| := by positivity
        have h2 : 2 * Real.pi * |(n : ℝ) - c| ≤ lam := by
          calc 2 * Real.pi * |(n : ℝ) - c| ≤ 2 * Real.pi * ((N : ℝ) / 2) :=
                mul_le_mul_of_nonneg_left hdist (by positivity)
            _ = lam := by simp [lam]; ring
        nlinarith
      exact mul_le_mul_of_nonneg_right hsq_le (sq_nonneg _)
    -- 7. Assemble final bound
    have hfinal :
        (1 / δ) * (∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2) +
          ((lam / 2) * (∫ t in (0 : ℝ)..1, ‖S t‖ ^ 2) +
            (1 / (2 * lam)) * (∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2)) ≤
        (lam + 1 / δ) * ∑ n ∈ I, ‖a n‖ ^ 2 := by
      have h2 : (1 / (2 * lam)) * (∫ t in (0 : ℝ)..1, ‖S' t‖ ^ 2) ≤
          (1 / (2 * lam)) * (lam ^ 2 * ∑ n ∈ I, ‖a n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hS'_bound (by positivity)
      have hsimp : (1 / (2 * lam)) * (lam ^ 2 * ∑ n ∈ I, ‖a n‖ ^ 2) =
          (lam / 2) * ∑ n ∈ I, ‖a n‖ ^ 2 := by
        field_simp [hlam.ne']
      rw [hparseval_S]
      linarith
    exact hsum_sob.trans ((add_le_add le_rfl hcross).trans hfinal)

/-- **Analytic Large Sieve Inequality (`ℕ` interval `Finset.Icc M (M + N - 1)` for `1 ≤ N`):**
Direct `ℕ`-indexed specialization of `large_sieve_gallagher`. -/
theorem large_sieve_gallagher_nat {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hws : WellSpaced s α δ)
    (M N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) :
    ∑ r ∈ s, ‖∑ n ∈ Finset.Icc M (M + N - 1), a n * eChar ((n : ℝ) * α r)‖ ^ 2 ≤
      (Real.pi * (N : ℝ) + 1 / δ) * ∑ n ∈ Finset.Icc M (M + N - 1), ‖a n‖ ^ 2 := by
  let aZ : ℤ → ℂ := fun n => if 0 ≤ n then a n.toNat else 0
  have hgal := large_sieve_gallagher s α δ hδ0 hδ1 hws (M : ℤ) N aZ
  have hsum_eq : ∀ {β : Type} [AddCommMonoid β] (f : ℕ → β),
      ∑ n ∈ Finset.Icc (M : ℤ) ((M : ℤ) + (N : ℤ) - 1), f n.toNat =
        ∑ n ∈ Finset.Icc M (M + N - 1), f n := by
    intro β _ f
    refine Finset.sum_nbij' (fun n => n.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    · intro n hn; rw [Finset.mem_Icc] at hn; omega
    · intro n _; simp
    · intro n _; rfl
  have hLHS :
      ∑ r ∈ s, ‖∑ n ∈ Finset.Icc (M : ℤ) ((M : ℤ) + (N : ℤ) - 1), aZ n * eChar ((n : ℝ) * α r)‖ ^ 2 =
        ∑ r ∈ s, ‖∑ n ∈ Finset.Icc M (M + N - 1), a n * eChar ((n : ℝ) * α r)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    have h1 : ∀ n ∈ Finset.Icc (M : ℤ) ((M : ℤ) + (N : ℤ) - 1),
        aZ n * eChar ((n : ℝ) * α r) = a n.toNat * eChar ((n.toNat : ℝ) * α r) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have h0 : 0 ≤ n := by omega
      have hcast : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0
      simp only [aZ, if_pos h0, hcast]
    rw [Finset.sum_congr rfl h1]
    exact hsum_eq (fun n => a n * eChar ((n : ℝ) * α r))
  have hRHS :
      ∑ n ∈ Finset.Icc (M : ℤ) ((M : ℤ) + (N : ℤ) - 1), ‖aZ n‖ ^ 2 =
        ∑ n ∈ Finset.Icc M (M + N - 1), ‖a n‖ ^ 2 := by
    have h1 : ∀ n ∈ Finset.Icc (M : ℤ) ((M : ℤ) + (N : ℤ) - 1),
        ‖aZ n‖ ^ 2 = ‖a n.toNat‖ ^ 2 := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have h0 : 0 ≤ n := by omega
      simp only [aZ, if_pos h0]
    rw [Finset.sum_congr rfl h1]
    exact hsum_eq (fun n => ‖a n‖ ^ 2)
  rwa [hLHS, hRHS] at hgal

/-- The finite set of reduced Farey fractions `(q, a)` with `1 ≤ q ≤ Q`, `1 ≤ a ≤ q`, `gcd a q = 1`. -/
def fareyFinset (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 Q).biUnion fun q =>
    ((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).image (fun a => (q, a))

/-- Farey fractions of order `Q` are `(1 / Q^2)`-well-spaced modulo `1`. -/
theorem farey_wellSpaced (Q : ℕ) :
    WellSpaced (fareyFinset Q) (fun p => (p.2 : ℝ) / (p.1 : ℝ)) (1 / (Q : ℝ) ^ 2) := by
  intro p1 hp1 p2 hp2 hne k
  simp only [fareyFinset, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Icc] at hp1 hp2
  rcases hp1 with ⟨q1, ⟨hq1_ge, hq1_le⟩, a1, ⟨⟨ha1_ge, ha1_le⟩, hcop1⟩, rfl⟩
  rcases hp2 with ⟨q2, ⟨hq2_ge, hq2_le⟩, a2, ⟨⟨ha2_ge, ha2_le⟩, hcop2⟩, rfl⟩
  have hq1_pos : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast (by omega : 0 < q1)
  have hq2_pos : (0 : ℝ) < (q2 : ℝ) := by exact_mod_cast (by omega : 0 < q2)
  have hnum_ne : (a1 : ℤ) * (q2 : ℤ) - (a2 : ℤ) * (q1 : ℤ) - k * (q1 : ℤ) * (q2 : ℤ) ≠ 0 := by
    intro hzero
    have hdvd1 : (q1 : ℤ) ∣ (a1 : ℤ) * (q2 : ℤ) := by
      refine ⟨(a2 : ℤ) + k * (q2 : ℤ), ?_⟩
      linarith
    have hq1_dvd_q2 : q1 ∣ q2 := by
      have h1 : q1 ∣ a1 * q2 := Int.ofNat_dvd.mp (by exact_mod_cast hdvd1)
      exact hcop1.symm.dvd_of_dvd_mul_left h1
    have hdvd2 : (q2 : ℤ) ∣ (a2 : ℤ) * (q1 : ℤ) := by
      refine ⟨(a1 : ℤ) - k * (q1 : ℤ), ?_⟩
      linarith
    have hq2_dvd_q1 : q2 ∣ q1 := by
      have h2 : q2 ∣ a2 * q1 := Int.ofNat_dvd.mp (by exact_mod_cast hdvd2)
      exact hcop2.symm.dvd_of_dvd_mul_left h2
    have hqeq : q1 = q2 := Nat.dvd_antisymm hq1_dvd_q2 hq2_dvd_q1
    subst hqeq
    have ha_diff : (a1 : ℤ) - (a2 : ℤ) = k * (q1 : ℤ) := by
      have hfac : ((a1 : ℤ) - (a2 : ℤ) - k * (q1 : ℤ)) * (q1 : ℤ) = 0 := by linarith
      rcases mul_eq_zero.mp hfac with h | h
      · linarith
      · omega
    have hk0 : k = 0 := by
      by_contra hk_ne
      have habs : (q1 : ℤ) ≤ |k * (q1 : ℤ)| := by
        rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ q1)]
        have : 1 ≤ |k| := Int.one_le_abs hk_ne
        nlinarith
      rw [← ha_diff] at habs
      have hlt : |(a1 : ℤ) - (a2 : ℤ)| < (q1 : ℤ) := by
        rw [abs_lt]; constructor <;> omega
      omega
    rw [hk0, zero_mul] at ha_diff
    have haeq : a1 = a2 := by omega
    exact hne (by rw [haeq])
  have habs_ge : (1 : ℝ) ≤ |(((a1 : ℤ) * (q2 : ℤ) - (a2 : ℤ) * (q1 : ℤ) - k * (q1 : ℤ) * (q2 : ℤ) : ℤ) : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |(a1 : ℤ) * (q2 : ℤ) - (a2 : ℤ) * (q1 : ℤ) - k * (q1 : ℤ) * (q2 : ℤ)| :=
      Int.one_le_abs hnum_ne
    exact_mod_cast h1
  have hfrac :
      (a1 : ℝ) / (q1 : ℝ) - (a2 : ℝ) / (q2 : ℝ) - (k : ℝ) =
        (((a1 : ℤ) * (q2 : ℤ) - (a2 : ℤ) * (q1 : ℤ) - k * (q1 : ℤ) * (q2 : ℤ) : ℤ) : ℝ) /
          ((q1 : ℝ) * (q2 : ℝ)) := by
    push_cast
    field_simp [hq1_pos.ne', hq2_pos.ne']
  dsimp only
  rw [hfrac, abs_div, abs_of_pos (mul_pos hq1_pos hq2_pos)]
  have hprod_le : (q1 : ℝ) * (q2 : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq1_le
    have h2 : (q2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq2_le
    nlinarith
  calc 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q1 : ℝ) * (q2 : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos hq1_pos hq2_pos) hprod_le
    _ ≤ |(((a1 : ℤ) * (q2 : ℤ) - (a2 : ℤ) * (q1 : ℤ) - k * (q1 : ℤ) * (q2 : ℤ) : ℤ) : ℝ)| /
          ((q1 : ℝ) * (q2 : ℝ)) := by
        exact div_le_div_of_nonneg_right habs_ge (mul_pos hq1_pos hq2_pos).le

/-- **Arithmetic Farey Large Sieve Corollary:**
For `Q ≥ 1`, `M : ℤ`, `N : ℕ`, and `c : ℤ → ℂ`,
`∑_{q=1}^Q ∑_{a=1, gcd(a,q)=1}^q ‖∑_{n=M}^{M+N-1} c_n e(n a/q)‖^2 ≤ (π N + Q^2) ∑ ‖c_n‖^2`. -/
theorem large_sieve_farey (Q : ℕ) (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ) (c : ℤ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q,
      ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
        ‖∑ n ∈ Finset.Icc M (M + (N : ℤ) - 1), c n * eChar ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 ≤
      (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc M (M + (N : ℤ) - 1), ‖c n‖ ^ 2 := by
  have hQpos : (0 : ℝ) < (Q : ℝ) ^ 2 := by
    have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
    positivity
  have hδ0 : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := one_div_pos.mpr hQpos
  have hδ1 : 1 / (Q : ℝ) ^ 2 ≤ 1 := by
    have hQge1 : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
      nlinarith
    exact (div_le_one hQpos).mpr hQge1
  have hgal := large_sieve_gallagher (fareyFinset Q)
    (fun p => (p.2 : ℝ) / (p.1 : ℝ)) (1 / (Q : ℝ) ^ 2) hδ0 hδ1 (farey_wellSpaced Q) M N c
  have hinv : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := one_div_one_div _
  rw [hinv] at hgal
  have hsum_eq :
      ∑ p ∈ fareyFinset Q,
        ‖∑ n ∈ Finset.Icc M (M + (N : ℤ) - 1), c n * eChar ((n : ℝ) * ((p.2 : ℝ) / (p.1 : ℝ)))‖ ^ 2 =
      ∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
          ‖∑ n ∈ Finset.Icc M (M + (N : ℤ) - 1), c n * eChar ((n : ℝ) * ((a : ℝ) / (q : ℝ)))‖ ^ 2 := by
    unfold fareyFinset
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_image]
      intro a1 _ a2 _ h
      exact (Prod.mk.inj h).2
    · intro q1 _ q2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_image] at hp1 hp2
      rcases hp1 with ⟨a1, _, rfl⟩
      rcases hp2 with ⟨a2, _, h⟩
      exact hne (Prod.mk.inj h).1.symm
  rwa [hsum_eq] at hgal

/-! ## Section 2: Blichfeldt's Theorem, Minkowski's Convex Body Theorem, & Discrete Grid Core -/

/-- Canonical embedding of an integer lattice vector `z : Fin d → ℤ` into `Fin d → ℝ`. -/
def intVec {d : ℕ} (z : Fin d → ℤ) : Fin d → ℝ := fun i => (z i : ℝ)

lemma intVec_injective {d : ℕ} : Function.Injective (intVec (d := d)) := by
  intro z1 z2 h
  funext i
  exact Int.cast_injective (congrFun h i)

/-- **Blichfeldt's Lattice-Point Theorem** on `Fin d → ℝ` / `ℤ^d`:
Any measurable subset `S ⊆ ℝ^d` with `1 < volume S` contains two distinct points `x, y ∈ S`
whose difference `x - y` is an integer lattice vector. -/
theorem blichfeldt_lattice {d : ℕ} (S : Set (Fin d → ℝ)) (hS_meas : MeasurableSet S)
    (hS_vol : (1 : ENNReal) < volume S) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ∀ i : Fin d, ∃ k : ℤ, x i - y i = (k : ℝ) := by
  let U : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)
  let cell : (Fin d → ℤ) → Set (Fin d → ℝ) :=
    fun z => Set.univ.pi (fun i => Set.Ico (z i : ℝ) ((z i : ℝ) + 1))
  let A : (Fin d → ℤ) → Set (Fin d → ℝ) :=
    fun z => (fun x => x + intVec z) ⁻¹' (S ∩ cell z)
  have hU_vol : volume U = 1 := by
    simp [U, MeasureTheory.volume_pi_pi, Real.volume_Ico]
  have hcell_meas : ∀ z : Fin d → ℤ, MeasurableSet (cell z) := fun z =>
    MeasurableSet.univ_pi (fun _ => measurableSet_Ico)
  have hS_eq : S = ⋃ z : Fin d → ℤ, S ∩ cell z := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      refine ⟨fun i => ⌊x i⌋, hx, ?_⟩
      intro i _
      exact ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩
    · rintro ⟨_, hx, _⟩
      exact hx
  have hcell_disj : Pairwise (Function.onFun Disjoint (fun z : Fin d → ℤ => S ∩ cell z)) := by
    intro z1 z2 hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx1 hx2
    apply hne
    funext i
    have h1 := hx1.2 i (Set.mem_univ i)
    have h2 := hx2.2 i (Set.mem_univ i)
    have hlt1 : (z1 i : ℝ) < (z2 i : ℝ) + 1 := lt_of_le_of_lt h1.1 h2.2
    have hlt2 : (z2 i : ℝ) < (z1 i : ℝ) + 1 := lt_of_le_of_lt h2.1 h1.2
    have hz1 : z1 i < z2 i + 1 := by exact_mod_cast hlt1
    have hz2 : z2 i < z1 i + 1 := by exact_mod_cast hlt2
    omega
  have hS_tsum : volume S = ∑' z : Fin d → ℤ, volume (S ∩ cell z) := by
    conv_lhs => rw [hS_eq]
    exact MeasureTheory.measure_iUnion hcell_disj (fun z => hS_meas.inter (hcell_meas z))
  have hA_meas : ∀ z : Fin d → ℤ, MeasurableSet (A z) := fun z =>
    (measurable_id.add measurable_const) (hS_meas.inter (hcell_meas z))
  have hA_vol : ∀ z : Fin d → ℤ, volume (A z) = volume (S ∩ cell z) := fun z =>
    MeasureTheory.measure_preimage_add_right volume (intVec z) (S ∩ cell z)
  have hA_sub : ∀ z : Fin d → ℤ, A z ⊆ U := by
    intro z w hw i _
    have h := hw.2 i (Set.mem_univ i)
    simp only [Pi.add_apply, intVec, Set.mem_Ico] at h ⊢
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hnot_disj : ¬ Pairwise (Function.onFun Disjoint A) := by
    intro hdisj
    have htsum : volume S = volume (⋃ z : Fin d → ℤ, A z) := by
      rw [hS_tsum]
      simp_rw [← hA_vol]
      exact (MeasureTheory.measure_iUnion hdisj hA_meas).symm
    have hle : volume (⋃ z : Fin d → ℤ, A z) ≤ volume U :=
      MeasureTheory.measure_mono (Set.iUnion_subset hA_sub)
    rw [htsum] at hS_vol
    rw [hU_vol] at hle
    exact not_lt_of_ge hle hS_vol
  rw [Pairwise] at hnot_disj
  push Not at hnot_disj
  rcases hnot_disj with ⟨z1, z2, hne, hnd⟩
  rw [Function.onFun, Set.not_disjoint_iff] at hnd
  rcases hnd with ⟨w, hw1, hw2⟩
  refine ⟨w + intVec z1, hw1.1, w + intVec z2, hw2.1, ?_, ?_⟩
  · intro heq
    apply hne
    apply intVec_injective
    exact add_left_cancel heq
  · intro i
    refine ⟨z1 i - z2 i, ?_⟩
    simp only [Pi.add_apply, intVec, Int.cast_sub]
    ring

/-- **Minkowski's Convex Body Theorem (Strict Volume Inequality)** on `Fin d → ℝ` / `ℤ^d`:
Every measurable, convex, centrally symmetric set `K ⊆ ℝ^d` with `2^d < volume K` contains
a nonzero integer lattice point `z ∈ ℤ^d \ {0}`. -/
theorem minkowski_convex_body {d : ℕ} (K : Set (Fin d → ℝ)) (hK_meas : MeasurableSet K)
    (hK_conv : Convex ℝ K) (hK_symm : ∀ x ∈ K, -x ∈ K)
    (hK_vol : (2 : ENNReal) ^ d < volume K) :
    ∃ z : Fin d → ℤ, z ≠ 0 ∧ intVec z ∈ K := by
  let S : Set (Fin d → ℝ) := (2⁻¹ : ℝ) • K
  have hS_pre : S = (fun x : Fin d → ℝ => (2 : ℝ) • x) ⁻¹' K := by
    ext x
    simp only [S, Set.mem_smul_set, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [smul_smul] using hy
    · intro hx
      exact ⟨(2 : ℝ) • x, hx, by simp [smul_smul]⟩
  have hS_meas : MeasurableSet S := by
    rw [hS_pre]
    exact (continuous_const_smul (2 : ℝ)).measurable hK_meas
  have hS_vol : (1 : ENNReal) < volume S := by
    have hsmul := MeasureTheory.Measure.addHaar_smul volume (2⁻¹ : ℝ) K
    have hrank : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
    rw [hrank, abs_of_pos (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ d)] at hsmul
    have hpow : ENNReal.ofReal ((2⁻¹ : ℝ) ^ d) = ((2 : ENNReal) ^ d)⁻¹ := by
      rw [inv_pow, ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 ^ d)]
      congr 1
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [show S = (2⁻¹ : ℝ) • K from rfl, hsmul, hpow]
    have h2ne0 : (2 : ENNReal) ^ d ≠ 0 := by positivity
    have h2top : (2 : ENNReal) ^ d ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    have hlt := ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.mpr h2top) (ENNReal.inv_ne_top.mpr h2ne0) hK_vol
    rwa [ENNReal.inv_mul_cancel h2ne0 h2top] at hlt
  rcases blichfeldt_lattice S hS_meas hS_vol with ⟨x, hx, y, hy, hxy, hdiff⟩
  choose z hz using hdiff
  have hz_ne : z ≠ 0 := by
    intro hz0
    apply hxy
    funext i
    have hi := hz i
    rw [hz0] at hi
    simp only [Pi.zero_apply, Int.cast_zero] at hi
    linarith
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  have hnegv : -v ∈ K := hK_symm v hv
  have hmid : (2⁻¹ : ℝ) • u + (2⁻¹ : ℝ) • (-v) ∈ K :=
    hK_conv hu hnegv (by norm_num) (by norm_num) (by norm_num)
  have heq : intVec z = (2⁻¹ : ℝ) • u + (2⁻¹ : ℝ) • (-v) := by
    funext i
    have hi := hz i
    simp only [intVec, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hi ⊢
    linarith
  exact ⟨z, hz_ne, heq ▸ hmid⟩

/-- **Minkowski's Convex Body Theorem (Compact Boundary Case, `d ≥ 1`):**
Every compact, convex, centrally symmetric body `K ⊆ ℝ^d` (`1 ≤ d`) with `2^d ≤ volume K`
contains a nonzero integer lattice point `z ∈ ℤ^d \ {0}`. -/
theorem minkowski_convex_body_compact {d : ℕ} (hd : 1 ≤ d) (K : Set (Fin d → ℝ))
    (hK_comp : IsCompact K) (hK_conv : Convex ℝ K) (hK_symm : ∀ x ∈ K, -x ∈ K)
    (hK_vol : (2 : ENNReal) ^ d ≤ volume K) :
    ∃ z : Fin d → ℤ, z ≠ 0 ∧ intVec z ∈ K := by
  have hK_closed : IsClosed K := hK_comp.isClosed
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  -- Obtain a uniform coordinate bound `R ≥ 0` on `K`
  rcases hK_comp.isBounded.subset_closedBall (0 : Fin d → ℝ) with ⟨R, hR⟩
  have hR_bound : ∀ x ∈ K, ∀ i : Fin d, |x i| ≤ max R 0 := by
    intro x hx i
    have hnorm : ‖x‖ ≤ R := by
      have := hR hx
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ R := hnorm
      _ ≤ max R 0 := le_max_left _ _
  -- For each `m : ℕ`, let `r m = 1 + 1 / (m + 1) > 1` and find `z_m ≠ 0` in `r m • K`
  let r : ℕ → ℝ := fun m => 1 + 1 / ((m : ℝ) + 1)
  have hr_gt1 : ∀ m : ℕ, 1 < r m := fun m => by
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hr_le2 : ∀ m : ℕ, r m ≤ 2 := fun m => by
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) m]
    have h2 : 1 / ((m : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr h1
    linarith
  have hexists : ∀ m : ℕ, ∃ z : Fin d → ℤ, z ≠ 0 ∧ intVec z ∈ (r m) • K := by
    intro m
    have hrpos : 0 < r m := by linarith [hr_gt1 m]
    have hKm_meas : MeasurableSet ((r m) • K) := by
      have hpre : (r m) • K = (fun x : Fin d → ℝ => (r m)⁻¹ • x) ⁻¹' K := by
        ext x
        simp only [Set.mem_smul_set, Set.mem_preimage]
        constructor
        · rintro ⟨y, hy, rfl⟩; simpa [inv_smul_smul₀ hrpos.ne'] using hy
        · intro hx; exact ⟨(r m)⁻¹ • x, hx, smul_inv_smul₀ hrpos.ne' x⟩
      rw [hpre]
      exact (continuous_const_smul (r m)⁻¹).measurable hK_meas
    have hKm_conv : Convex ℝ ((r m) • K) := hK_conv.smul (r m)
    have hKm_symm : ∀ x ∈ (r m) • K, -x ∈ (r m) • K := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨-y, hK_symm y hy, smul_neg (r m) y⟩
    have hKm_vol : (2 : ENNReal) ^ d < volume ((r m) • K) := by
      have hsmul := MeasureTheory.Measure.addHaar_smul volume (r m) K
      have hrank : Module.finrank ℝ (Fin d → ℝ) = d := Module.finrank_fin_fun ℝ
      rw [hrank, abs_of_pos (by positivity : (0 : ℝ) < (r m) ^ d)] at hsmul
      rw [hsmul]
      have hpow_gt : (1 : ℝ) < (r m) ^ d := one_lt_pow₀ (hr_gt1 m) (by omega)
      have hofReal_gt : (1 : ENNReal) < ENNReal.ofReal ((r m) ^ d) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr hpow_gt
      have h2ne0 : (2 : ENNReal) ^ d ≠ 0 := by positivity
      have h2top : (2 : ENNReal) ^ d ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
      calc (2 : ENNReal) ^ d = 1 * (2 : ENNReal) ^ d := (one_mul _).symm
        _ < ENNReal.ofReal ((r m) ^ d) * (2 : ENNReal) ^ d :=
            ENNReal.mul_lt_mul_left h2ne0 h2top hofReal_gt
        _ ≤ ENNReal.ofReal ((r m) ^ d) * volume K := by
            gcongr
    exact minkowski_convex_body ((r m) • K) hKm_meas hKm_conv hKm_symm hKm_vol
  choose zseq hz_ne hz_mem using hexists
  -- All `zseq m` lie in a finite integer box
  let B : ℤ := ⌈2 * max R 0⌉ + 1
  let box : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-B) B)
  have hmem_box : ∀ m : ℕ, zseq m ∈ box := by
    intro m
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    rcases hz_mem m with ⟨u, hu, hru⟩
    have hi : (zseq m i : ℝ) = r m * u i := by
      have := congrFun hru i
      simpa [intVec, Pi.smul_apply, smul_eq_mul] using this.symm
    have habs : |(zseq m i : ℝ)| ≤ 2 * max R 0 := by
      rw [hi, abs_mul, abs_of_pos (by linarith [hr_gt1 m])]
      calc r m * |u i| ≤ 2 * |u i| := mul_le_mul_of_nonneg_right (hr_le2 m) (abs_nonneg _)
        _ ≤ 2 * max R 0 := mul_le_mul_of_nonneg_left (hR_bound u hu i) (by norm_num)
    have hB : 2 * max R 0 ≤ (B : ℝ) := by
      have h1 : 2 * max R 0 ≤ (⌈2 * max R 0⌉ : ℝ) := Int.le_ceil _
      have h2 : (B : ℝ) = (⌈2 * max R 0⌉ : ℝ) + 1 := by simp [B]
      linarith
    have hleB : |(zseq m i : ℝ)| ≤ (B : ℝ) := habs.trans hB
    rw [abs_le] at hleB
    exact ⟨by exact_mod_cast hleB.1, by exact_mod_cast hleB.2⟩
  -- Infinite pigeonhole: some `z ∈ box` occurs infinitely often
  have hinf : ∃ z ∈ box, Set.Infinite {m : ℕ | zseq m = z} := by
    by_contra hall
    push Not at hall
    have huniv : (Set.univ : Set ℕ) = ⋃ z ∈ (box : Set (Fin d → ℤ)), {m : ℕ | zseq m = z} := by
      ext m
      simp only [Set.mem_univ, Set.mem_iUnion, Finset.mem_coe, Set.mem_ofPred_eq, true_iff]
      exact ⟨zseq m, hmem_box m, rfl⟩
    have hfin : (Set.univ : Set ℕ).Finite := by
      rw [huniv]
      exact box.finite_toSet.biUnion (fun z hz => hall z hz)
    exact Set.infinite_univ hfin
  rcases hinf with ⟨z, _, hz_inf⟩
  have hz0 : z ≠ 0 := by
    rcases hz_inf.nonempty with ⟨m, hm⟩
    exact hm ▸ hz_ne m
  -- Extract strictly increasing indices `m_k` with `zseq (m_k) = z`, so `(r (m_k))⁻¹ • intVec z ∈ K`
  have hmem_K : intVec z ∈ K := by
    rw [← hK_closed.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    -- Choose `m` large enough in `{m | zseq m = z}`
    have hbound : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ‖(r m)⁻¹ • intVec z - intVec z‖ < ε := by
      have htend : Filter.Tendsto (fun m : ℕ => (r m)⁻¹ • intVec z) Filter.atTop (nhds ((1 : ℝ) • intVec z)) := by
        have hr_tend : Filter.Tendsto r Filter.atTop (nhds 1) := by
          have h0 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa [r] using tendsto_const_nhds.add h0
        simpa using (hr_tend.inv₀ (by norm_num)).smul_const (intVec z)
      rw [one_smul, Metric.tendsto_atTop] at htend
      rcases htend ε hε with ⟨M, hM⟩
      exact ⟨M, fun m hm => by simpa [dist_eq_norm] using hM m hm⟩
    rcases hbound with ⟨M, hM⟩
    rcases hz_inf.exists_gt M with ⟨m, hm_eq, hm_gt⟩
    have hzm : intVec z ∈ (r m) • K := by
      have : zseq m = z := hm_eq
      rw [← this]
      exact hz_mem m
    rcases hzm with ⟨u, hu, hru⟩
    have hu_eq : u = (r m)⁻¹ • intVec z := by
      have hrpos : 0 < r m := by linarith [hr_gt1 m]
      rw [← hru, inv_smul_smul₀ hrpos.ne']
    refine ⟨u, hu, ?_⟩
    rw [hu_eq, dist_comm, dist_eq_norm]
    exact hM m hm_gt.le
  exact ⟨z, hz0, hmem_K⟩

/-- **Discrete Finite-Grid Pigeonhole Core (Discrete Blichfeldt Lemma):**
Any finite set `A ⊆ ℤ^d` with `m^d < |A|` (`1 ≤ m`) contains two distinct points `x, y ∈ A`
such that `m ∣ (x i - y i)` for every coordinate `i : Fin d`. -/
theorem discrete_blichfeldt_grid {d m : ℕ} (hm : 1 ≤ m) (A : Finset (Fin d → ℤ))
    (hcard : m ^ d < A.card) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ ∀ i : Fin d, (m : ℤ) ∣ (x i - y i) := by
  let B : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ => Finset.Ico (0 : ℤ) (m : ℤ))
  have hB_card : B.card = m ^ d := by
    rw [Fintype.card_piFinset]
    simp [Int.card_Ico, Finset.prod_const]
  let f : (Fin d → ℤ) → (Fin d → ℤ) := fun x i => x i % (m : ℤ)
  have hmaps : ∀ x ∈ A, f x ∈ B := by
    intro x _
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Ico]
    have hmpos : (0 : ℤ) < (m : ℤ) := by omega
    exact ⟨Int.emod_nonneg (x i) hmpos.ne', Int.emod_lt_of_pos (x i) hmpos⟩
  have hlt : B.card < A.card := hB_card ▸ hcard
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps with ⟨x, hx, y, hy, hxy, hfeq⟩
  refine ⟨x, hx, y, hy, hxy, fun i => ?_⟩
  have hi : x i % (m : ℤ) = y i % (m : ℤ) := congrFun hfeq i
  refine ⟨x i / (m : ℤ) - y i / (m : ℤ), ?_⟩
  have h1 := Int.emod_add_mul_ediv (x i) (m : ℤ)
  have h2 := Int.emod_add_mul_ediv (y i) (m : ℤ)
  linarith

/-! ## Section 3: Dirichlet's Simultaneous Diophantine Approximation Theorem -/

/-- **Dirichlet's Simultaneous Diophantine Approximation Theorem (Integer `N ≥ 1`, Strict Bound):**
For any `α : Fin d → ℝ` and `N ≥ 1`, there exists `q ∈ [1, N^d]` such that
`|q * α i - round (q * α i)| < 1 / N` for every `i : Fin d`. -/
theorem dirichlet_simultaneous_nat {d : ℕ} (α : Fin d → ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ^ d ∧
      ∀ i : Fin d, |(q : ℝ) * α i - (round ((q : ℝ) * α i) : ℝ)| < 1 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  let A : Finset ℕ := Finset.range (N ^ d + 1)
  let B : Finset (Fin d → ℕ) := Fintype.piFinset (fun _ => Finset.range N)
  let box : ℕ → (Fin d → ℕ) := fun k i => ⌊(N : ℝ) * Int.fract ((k : ℝ) * α i)⌋₊
  have hB_card : B.card = N ^ d := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const]
  have hmaps : ∀ k ∈ A, box k ∈ B := by
    intro k _
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hlt : (N : ℝ) * Int.fract ((k : ℝ) * α i) < (N : ℝ) := by
      have hf := Int.fract_lt_one ((k : ℝ) * α i)
      nlinarith
    exact Nat.floor_lt (mul_nonneg hNpos.le (Int.fract_nonneg _)) |>.mpr hlt
  have hlt : B.card < A.card := by
    rw [hB_card, Finset.card_range]
    omega
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps with ⟨k1, hk1, k2, hk2, hne, hbeq⟩
  rw [Finset.mem_range] at hk1 hk2
  -- WLOG `a < b` with `box a = box b`
  have hpair : ∃ a b : ℕ, a < b ∧ b ≤ N ^ d ∧ box a = box b := by
    rcases lt_or_gt_of_ne hne with h12 | h21
    · exact ⟨k1, k2, h12, by omega, hbeq⟩
    · exact ⟨k2, k1, h21, by omega, hbeq.symm⟩
  rcases hpair with ⟨a, b, hab, hb_le, hbox_eq⟩
  refine ⟨b - a, by omega, by omega, fun i => ?_⟩
  have hbi : ⌊(N : ℝ) * Int.fract ((a : ℝ) * α i)⌋₊ = ⌊(N : ℝ) * Int.fract ((b : ℝ) * α i)⌋₊ :=
    congrFun hbox_eq i
  have hfa_nn : 0 ≤ (N : ℝ) * Int.fract ((a : ℝ) * α i) :=
    mul_nonneg hNpos.le (Int.fract_nonneg _)
  have hfb_nn : 0 ≤ (N : ℝ) * Int.fract ((b : ℝ) * α i) :=
    mul_nonneg hNpos.le (Int.fract_nonneg _)
  have ha_ge : (⌊(N : ℝ) * Int.fract ((a : ℝ) * α i)⌋₊ : ℝ) ≤ (N : ℝ) * Int.fract ((a : ℝ) * α i) :=
    Nat.floor_le hfa_nn
  have ha_lt : (N : ℝ) * Int.fract ((a : ℝ) * α i) < (⌊(N : ℝ) * Int.fract ((a : ℝ) * α i)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hb_ge : (⌊(N : ℝ) * Int.fract ((a : ℝ) * α i)⌋₊ : ℝ) ≤ (N : ℝ) * Int.fract ((b : ℝ) * α i) := by
    rw [hbi]; exact Nat.floor_le hfb_nn
  have hb_lt : (N : ℝ) * Int.fract ((b : ℝ) * α i) < (⌊(N : ℝ) * Int.fract ((a : ℝ) * α i)⌋₊ : ℝ) + 1 := by
    rw [hbi]; exact Nat.lt_floor_add_one _
  have hdiff_lt : |Int.fract ((b : ℝ) * α i) - Int.fract ((a : ℝ) * α i)| < 1 / (N : ℝ) := by
    rw [abs_lt]
    have hmul_lt : |(N : ℝ) * (Int.fract ((b : ℝ) * α i) - Int.fract ((a : ℝ) * α i))| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [abs_mul, abs_of_pos hNpos] at hmul_lt
    have hdiv : |Int.fract ((b : ℝ) * α i) - Int.fract ((a : ℝ) * α i)| < 1 / (N : ℝ) := by
      rw [lt_div_iff₀ hNpos]
      linarith
    exact abs_lt.mp hdiv
  have hcast_sub : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := Nat.cast_sub hab.le
  have hq_eq : ((b - a : ℕ) : ℝ) * α i - ((⌊(b : ℝ) * α i⌋ - ⌊(a : ℝ) * α i⌋ : ℤ) : ℝ) =
      Int.fract ((b : ℝ) * α i) - Int.fract ((a : ℝ) * α i) := by
    rw [hcast_sub]
    have h1 : Int.fract ((b : ℝ) * α i) = (b : ℝ) * α i - ⌊(b : ℝ) * α i⌋ := rfl
    have h2 : Int.fract ((a : ℝ) * α i) = (a : ℝ) * α i - ⌊(a : ℝ) * α i⌋ := rfl
    push_cast
    linarith
  have hdist := distToInt_le_abs_sub (((b - a : ℕ) : ℝ) * α i) (⌊(b : ℝ) * α i⌋ - ⌊(a : ℝ) * α i⌋)
  rw [hq_eq] at hdist
  exact lt_of_le_of_lt hdist hdiff_lt

/-- **Dirichlet's Simultaneous Diophantine Approximation Theorem (Real `Q ≥ 1`):**
For any `α : Fin d → ℝ` and any real `Q ≥ 1`, there exists `q : ℕ` with `1 ≤ q` and `(q : ℝ) ≤ Q^d`
such that `|q * α i - round (q * α i)| ≤ 1 / Q` for every `i : Fin d`.
(Proved via Minkowski's Compact Convex Body Theorem in `ℝ^{d+1}`.) -/
theorem dirichlet_simultaneous_real {d : ℕ} (α : Fin d → ℝ) (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ Q ^ d ∧
      ∀ i : Fin d, |(q : ℝ) * α i - (round ((q : ℝ) * α i) : ℝ)| ≤ 1 / Q := by
  by_cases hQ1 : Q = 1
  · subst hQ1
    refine ⟨1, le_rfl, by simp, fun i => ?_⟩
    have h := abs_sub_round ((1 : ℕ) * α i)
    norm_num at h ⊢
    linarith
  · have hQgt : 1 < Q := lt_of_le_of_ne hQ (Ne.symm hQ1)
    have hQpos : 0 < Q := by linarith
    -- Define the shear linear equivalence `T : ℝ^{d+1} ≃ₗ[ℝ] ℝ^{d+1}` with `det T = 1`
    let fFun : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) := fun v j =>
      if h : j.val < d then v j - v (Fin.last d) * α ⟨j.val, h⟩ else v (Fin.last d)
    let gFun : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ) := fun w j =>
      if h : j.val < d then w j + w (Fin.last d) * α ⟨j.val, h⟩ else w (Fin.last d)
    let T : (Fin (d + 1) → ℝ) ≃ₗ[ℝ] (Fin (d + 1) → ℝ) :=
      { toFun := fFun
        invFun := gFun
        map_add' := fun u v => by
          funext j
          simp only [fFun, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c v => by
          funext j
          simp only [fFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring
        left_inv := fun v => by
          funext j
          have hlast : ¬ (Fin.last d).val < d := by simp
          by_cases hj : j.val < d
          · simp only [fFun, gFun, hj, hlast, ↓reduceDIte]; ring
          · have hjeq : Fin.last d = j := by ext; simp only [Fin.val_last]; have := j.isLt; omega
            simp only [fFun, gFun, hj, ↓reduceDIte, hjeq]
        right_inv := fun w => by
          funext j
          have hlast : ¬ (Fin.last d).val < d := by simp
          by_cases hj : j.val < d
          · simp only [fFun, gFun, hj, hlast, ↓reduceDIte]; ring
          · have hjeq : Fin.last d = j := by ext; simp only [Fin.val_last]; have := j.isLt; omega
            simp only [fFun, gFun, hj, ↓reduceDIte, hjeq] }
    -- The matrix of `T` is upper triangular with `1`s on the diagonal, hence `det T = 1`
    let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := LinearMap.toMatrix' (T : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ))
    have hM_entry : ∀ i j : Fin (d + 1),
        M i j = if hi : i.val < d then
            (if i = j then 1 else 0) - (if Fin.last d = j then 1 else 0) * α ⟨i.val, hi⟩
          else if Fin.last d = j then 1 else 0 := by
      intro i j
      simp only [M, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
      change fFun (Pi.single j 1) i = _
      by_cases hi : i.val < d
      · simp only [fFun, hi, ↓reduceDIte, Pi.single_apply]
      · simp only [fFun, hi, ↓reduceDIte, Pi.single_apply]
    have hM_tri : M.BlockTriangular id := by
      intro i j hij
      rw [hM_entry]
      have hij_ne : i ≠ j := ne_of_gt hij
      have hlast_ne : Fin.last d ≠ j := by
        intro heq
        have hjv : j.val = d := by rw [← heq]; rfl
        have hiv : i.val ≤ d := Nat.le_of_lt_succ i.isLt
        have hlt : j.val < i.val := hij
        omega
      by_cases hi : i.val < d
      · simp [hi, hij_ne, hlast_ne]
      · simp [hi, hlast_ne]
    have hM_diag : ∀ i : Fin (d + 1), M i i = 1 := by
      intro i
      rw [hM_entry]
      by_cases hi : i.val < d
      · have hne : Fin.last d ≠ i := by intro heq; rw [← heq] at hi; simp at hi
        simp [hi, hne]
      · have heq : Fin.last d = i := by
          ext; simp only [Fin.val_last]; have := i.isLt; omega
        simp [hi, heq]
    have hdetT : LinearMap.det (T : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) = 1 := by
      rw [← LinearMap.det_toMatrix', show LinearMap.toMatrix' (T : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) = M from rfl]
      rw [Matrix.det_of_isUpperTriangular hM_tri]
      simp [hM_diag]
    -- Define the box `B` and the convex body `K = T ⁻¹' B`
    let B : Set (Fin (d + 1) → ℝ) :=
      Set.univ.pi fun j => if j.val < d then Set.Icc (-(1 / Q)) (1 / Q) else Set.Icc (-(Q ^ d)) (Q ^ d)
    let K : Set (Fin (d + 1) → ℝ) := T ⁻¹' B
    have hB_comp : IsCompact B := isCompact_univ_pi fun j => by
      split_ifs <;> exact isCompact_Icc
    have hT_cont_symm : Continuous (T.symm : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ)) :=
      (T.symm : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)).continuous_of_finiteDimensional
    have hK_eq_img : K = T.symm '' B := by
      ext v
      simp only [K, Set.mem_preimage, Set.mem_image]
      constructor
      · intro hv; exact ⟨T v, hv, T.symm_apply_apply v⟩
      · rintro ⟨w, hw, rfl⟩; simpa using hw
    have hK_comp : IsCompact K := hK_eq_img ▸ hB_comp.image hT_cont_symm
    have hB_conv : Convex ℝ B := convex_pi fun j _ => by
      split_ifs <;> exact convex_Icc _ _
    have hK_conv : Convex ℝ K := hB_conv.linear_preimage (T : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ))
    have hK_symm : ∀ x ∈ K, -x ∈ K := by
      intro x hx j _
      have hj := hx j (Set.mem_univ j)
      simp only [map_neg, Pi.neg_apply]
      by_cases h : j.val < d
      · simp only [h, ↓reduceIte, Set.mem_Icc] at hj ⊢
        exact ⟨by linarith [hj.2], by linarith [hj.1]⟩
      · simp only [h, ↓reduceIte, Set.mem_Icc] at hj ⊢
        exact ⟨by linarith [hj.2], by linarith [hj.1]⟩
    have hB_vol : volume B = (2 : ENNReal) ^ (d + 1) := by
      simp only [B, MeasureTheory.volume_pi_pi]
      rw [Fin.prod_univ_castSucc]
      have hlast : ¬ (Fin.last d).val < d := by simp
      have hterm : ∀ i : Fin d,
          volume (if (i.castSucc : Fin (d + 1)).val < d then Set.Icc (-(1 / Q)) (1 / Q) else Set.Icc (-(Q ^ d)) (Q ^ d)) =
            ENNReal.ofReal (2 / Q) := by
        intro i
        have hilt : (i.castSucc : Fin (d + 1)).val < d := i.isLt
        rw [if_pos hilt, Real.volume_Icc]
        congr 1; ring
      have hlast_term :
          volume (if (Fin.last d).val < d then Set.Icc (-(1 / Q)) (1 / Q) else Set.Icc (-(Q ^ d)) (Q ^ d)) =
            ENNReal.ofReal (2 * Q ^ d) := by
        rw [if_neg hlast, Real.volume_Icc]
        congr 1; ring
      simp_rw [hterm, hlast_term]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 / Q),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 / Q) ^ d)]
      have hcalc : (2 / Q) ^ d * (2 * Q ^ d) = (2 : ℝ) ^ (d + 1) := by
        rw [div_pow, pow_succ]
        field_simp [hQpos.ne']
      rw [hcalc, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hdetTsymm : LinearMap.det (T.symm : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) = 1 := by
      have hcomp :
          LinearMap.det (T : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) *
            LinearMap.det (T.symm : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) = 1 := by
        rw [← LinearMap.det_comp]
        have hid : (T : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)).comp
            (T.symm : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ)) = LinearMap.id := by
          ext v; simp
        rw [hid, LinearMap.det_id]
      rw [hdetT, one_mul] at hcomp
      exact hcomp
    have hK_vol : volume K = (2 : ENNReal) ^ (d + 1) := by
      have hpre := MeasureTheory.Measure.addHaar_preimage_linearEquiv volume T B
      rw [hdetTsymm] at hpre
      simp only [abs_one, ENNReal.ofReal_one, one_mul] at hpre
      exact hpre.trans hB_vol
    -- Apply Minkowski's Compact Convex Body Theorem in `ℝ^{d+1}`
    rcases minkowski_convex_body_compact (by omega : 1 ≤ d + 1) K hK_comp hK_conv hK_symm
        (le_of_eq hK_vol.symm) with ⟨z, hz_ne, hz_mem⟩
    have hq_ne : z (Fin.last d) ≠ 0 := by
      intro hq0
      apply hz_ne
      funext j
      by_cases hj : j.val < d
      · have hmem := hz_mem j (Set.mem_univ j)
        change fFun (intVec z) j ∈ (if j.val < d then Set.Icc (-(1 / Q)) (1 / Q) else Set.Icc (-(Q ^ d)) (Q ^ d)) at hmem
        rw [if_pos hj] at hmem
        simp only [fFun, hj, ↓reduceDIte, intVec, hq0, Int.cast_zero, zero_mul, sub_zero,
          Set.mem_Icc] at hmem
        have habs : |(z j : ℝ)| ≤ 1 / Q := abs_le.mpr hmem
        have hlt1 : |(z j : ℝ)| < 1 := lt_of_le_of_lt habs ((div_lt_one hQpos).mpr hQgt)
        have hzabs : |z j| < 1 := by exact_mod_cast hlt1
        rw [abs_lt] at hzabs
        simp only [Pi.zero_apply]
        omega
      · have hjeq : j = Fin.last d := by ext; simp only [Fin.val_last]; have := j.isLt; omega
        rw [hjeq, hq0]; rfl
    have hlast_bound : |(z (Fin.last d) : ℝ)| ≤ Q ^ d := by
      have hmem := hz_mem (Fin.last d) (Set.mem_univ _)
      have hnl : ¬ (Fin.last d).val < d := by simp
      change fFun (intVec z) (Fin.last d) ∈
        (if (Fin.last d).val < d then Set.Icc (-(1 / Q)) (1 / Q) else Set.Icc (-(Q ^ d)) (Q ^ d)) at hmem
      rw [if_neg hnl] at hmem
      simp only [fFun, hnl, ↓reduceDIte, intVec, Set.mem_Icc] at hmem
      exact abs_le.mpr hmem
    let q : ℕ := (z (Fin.last d)).natAbs
    have hq_ge : 1 ≤ q := Int.natAbs_pos.mpr hq_ne
    have hq_le : (q : ℝ) ≤ Q ^ d := by
      have h1 : ((q : ℤ) : ℝ) = |(z (Fin.last d) : ℝ)| := by
        have hz : (q : ℤ) = |z (Fin.last d)| := Int.natCast_natAbs (z (Fin.last d))
        rw [hz, Int.cast_abs]
      have h2 : (q : ℝ) = ((q : ℤ) : ℝ) := by push_cast; rfl
      linarith
    refine ⟨q, hq_ge, hq_le, fun i => ?_⟩
    have hmem := hz_mem i.castSucc (Set.mem_univ _)
    have hilt : i.castSucc.val < d := i.isLt
    change fFun (intVec z) i.castSucc ∈
      (if i.castSucc.val < d then Set.Icc (-(1 / Q)) (1 / Q) else Set.Icc (-(Q ^ d)) (Q ^ d)) at hmem
    rw [if_pos hilt] at hmem
    simp only [fFun, hilt, ↓reduceDIte, intVec, Set.mem_Icc] at hmem
    have habs : |(z i.castSucc : ℝ) - (z (Fin.last d) : ℝ) * α i| ≤ 1 / Q := abs_le.mpr hmem
    -- Handle sign of `z (Fin.last d)`
    rcases lt_or_gt_of_ne hq_ne with hneg | hpos
    · have hqcast : (q : ℝ) = -(z (Fin.last d) : ℝ) := by
        have : (q : ℤ) = -z (Fin.last d) := by
          dsimp [q]; exact Int.ofNat_natAbs_of_nonpos hneg.le
        exact_mod_cast this
      have hdist := distToInt_le_abs_sub ((q : ℝ) * α i) (-z i.castSucc)
      have heq : |(q : ℝ) * α i - ((-z i.castSucc : ℤ) : ℝ)| =
          |(z i.castSucc : ℝ) - (z (Fin.last d) : ℝ) * α i| := by
        push_cast; rw [hqcast]; congr 1; ring
      exact hdist.trans (heq ▸ habs)
    · have hqcast : (q : ℝ) = (z (Fin.last d) : ℝ) := by
        have : (q : ℤ) = z (Fin.last d) := by
          dsimp [q]; exact Int.natAbs_of_nonneg hpos.le
        exact_mod_cast this
      have hdist := distToInt_le_abs_sub ((q : ℝ) * α i) (z i.castSucc)
      have heq : |(q : ℝ) * α i - (z i.castSucc : ℝ)| =
          |(z i.castSucc : ℝ) - (z (Fin.last d) : ℝ) * α i| := by
        rw [hqcast, abs_sub_comm]
      exact hdist.trans (heq ▸ habs)

/-- **1D Dirichlet Approximation Corollary for Irrationals:**
For any irrational `α`, there exist arbitrarily large integers `q > Q₀` with
`|q * α - round (q * α)| < 1 / q`. -/
theorem dirichlet_approx_1d_infinitely_many (α : ℝ) (hα : Irrational α) (Q₀ : ℕ) :
    ∃ q : ℕ, Q₀ < q ∧ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| < 1 / (q : ℝ) := by
  -- Find a positive lower bound `δ` for `|k * α - round (k * α)|` over `1 ≤ k ≤ Q₀`
  let S : Finset ℕ := Finset.Icc 1 Q₀
  have hpos_dist : ∀ k ∈ S, 0 < |(k : ℝ) * α - (round ((k : ℝ) * α) : ℝ)| := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    apply abs_pos.mpr
    intro heq
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hrat : α = ((round ((k : ℝ) * α) : ℚ) / (k : ℚ) : ℝ) := by
      push_cast
      have hmul : (k : ℝ) * α = (round ((k : ℝ) * α) : ℝ) := sub_eq_zero.mp heq
      rw [← hmul]
      field_simp [hk_ne]
    exact hα ⟨(round ((k : ℝ) * α) : ℚ) / (k : ℚ), by push_cast at hrat ⊢; exact hrat.symm⟩
  -- Pick `N : ℕ` large enough that `1 / N ≤ |k * α - round (k * α)|` for all `k ∈ S`
  have hN_exists : ∃ N : ℕ, 1 ≤ N ∧ ∀ k ∈ S, 1 / (N : ℝ) ≤ |(k : ℝ) * α - (round ((k : ℝ) * α) : ℝ)| := by
    by_cases hS : S.Nonempty
    · set δ := S.inf' hS (fun k => |(k : ℝ) * α - (round ((k : ℝ) * α) : ℝ)|)
      have hδpos : 0 < δ := (Finset.lt_inf'_iff hS).mpr hpos_dist
      refine ⟨max 1 (⌈1 / δ⌉₊ + 1), le_max_left _ _, fun k hk => ?_⟩
      have hk_ge : δ ≤ |(k : ℝ) * α - (round ((k : ℝ) * α) : ℝ)| := Finset.inf'_le _ hk
      have hN_ge : 1 / δ ≤ ((max 1 (⌈1 / δ⌉₊ + 1) : ℕ) : ℝ) := by
        have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈1 / δ⌉₊ : ℝ) ≤ ((max 1 (⌈1 / δ⌉₊ + 1) : ℕ) : ℝ) := by
          exact_mod_cast le_trans (Nat.le_succ _) (le_max_right 1 _)
        linarith
      have h1div : 1 / ((max 1 (⌈1 / δ⌉₊ + 1) : ℕ) : ℝ) ≤ δ := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((max 1 (⌈1 / δ⌉₊ + 1) : ℕ) : ℝ))]
        have := mul_le_mul_of_nonneg_left hN_ge hδpos.le
        rw [mul_div_cancel₀ _ hδpos.ne'] at this
        linarith
      exact h1div.trans hk_ge
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      exact ⟨1, le_rfl, fun k hk => by simp [hS] at hk⟩
  rcases hN_exists with ⟨N, hN1, hN_le⟩
  rcases dirichlet_simultaneous_nat (fun _ : Fin 1 => α) N hN1 with ⟨q, hq1, hq_le, hq_approx⟩
  have happrox := hq_approx 0
  have hq_gt : Q₀ < q := by
    by_contra hle
    have hmem : q ∈ S := Finset.mem_Icc.mpr ⟨hq1, by omega⟩
    have := hN_le q hmem
    linarith
  have hq_le_N : (q : ℝ) ≤ (N : ℝ) := by
    simp only [pow_one] at hq_le
    exact_mod_cast hq_le
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  refine ⟨q, hq_gt, lt_of_lt_of_le happrox ?_⟩
  exact one_div_le_one_div_of_le hqpos hq_le_N

/-! ## Section 4: Weyl's Equidistribution Criterion & Irrational Rotation Equidistribution -/

/-- Equidistribution modulo `1` of a real sequence `x : ℕ → ℝ`:
for every `0 ≤ a ≤ b ≤ 1`, the asymptotic fraction of `n < N` with `Int.fract (x n) ∈ [a, b)`
converges to `b - a`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Filter.Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) /
          (N : ℝ))
      Filter.atTop (nhds (b - a))

/-- Helper: 1-periodic continuous functions have shift-invariant unit-interval integrals. -/
lemma intervalIntegral_periodic_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (hg_cont : Continuous g) (hg_per : Function.Periodic g 1) (a : ℝ) :
    ∫ t in a..(a + 1), g t = ∫ t in (0 : ℝ)..1, g t := by
  have ha : a = Int.fract a + (⌊a⌋ : ℝ) := by linarith [Int.fract_add_floor a]
  have h1 : ∫ t in a..(a + 1), g t = ∫ t in Int.fract a..(Int.fract a + 1), g t := by
    have ha1 : a + 1 = (Int.fract a + 1) + (⌊a⌋ : ℝ) := by linarith
    calc ∫ t in a..(a + 1), g t
        = ∫ t in (Int.fract a + (⌊a⌋ : ℝ))..((Int.fract a + 1) + (⌊a⌋ : ℝ)), g t := by
          rw [← ha, ← ha1]
      _ = ∫ t in Int.fract a..(Int.fract a + 1), g (t + (⌊a⌋ : ℝ)) :=
          (intervalIntegral.integral_comp_add_right g (⌊a⌋ : ℝ)).symm
      _ = ∫ t in Int.fract a..(Int.fract a + 1), g t := by
          congr 1; funext t; simpa [mul_one] using hg_per.int_mul ⌊a⌋ t
  have h2 : ∫ t in Int.fract a..(Int.fract a + 1), g t =
      (∫ t in Int.fract a..1, g t) + ∫ t in (1 : ℝ)..(Int.fract a + 1), g t :=
    (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hg_cont.intervalIntegrable _ _) (hg_cont.intervalIntegrable _ _)).symm
  have h3 : ∫ t in (1 : ℝ)..(Int.fract a + 1), g t = ∫ t in (0 : ℝ)..Int.fract a, g t := by
    calc ∫ t in (1 : ℝ)..(Int.fract a + 1), g t
        = ∫ t in ((0 : ℝ) + 1)..(Int.fract a + 1), g t := by norm_num
      _ = ∫ t in (0 : ℝ)..Int.fract a, g (t + 1) :=
          (intervalIntegral.integral_comp_add_right g 1).symm
      _ = ∫ t in (0 : ℝ)..Int.fract a, g t := by
          congr 1; funext t; exact hg_per t
  have h4 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg_cont.intervalIntegrable (0 : ℝ) (Int.fract a))
    (hg_cont.intervalIntegrable (Int.fract a) 1)
  rw [h1, h2, h3, add_comm, h4]

/-- The `M`-th Fejér kernel `F_M(t) = (1/M) |∑_{k=0}^{M-1} e(k t)|^2`. -/
def fejerKernel (M : ℕ) (t : ℝ) : ℝ :=
  (1 / (M : ℝ)) * ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ ^ 2

lemma fejerKernel_nonneg (M : ℕ) (t : ℝ) : 0 ≤ fejerKernel M t := by
  unfold fejerKernel
  positivity

lemma fejerKernel_continuous (M : ℕ) : Continuous (fejerKernel M) := by
  unfold fejerKernel eChar
  fun_prop

lemma fejerKernel_periodic (M : ℕ) : Function.Periodic (fejerKernel M) 1 := by
  intro t
  unfold fejerKernel
  congr 3
  apply Finset.sum_congr rfl
  intro k _
  have h : (k : ℝ) * (t + 1) = (k : ℝ) * t + ((k : ℤ) : ℝ) := by push_cast; ring
  rw [h, eChar_add_int]

lemma eChar_nat_mul (k : ℕ) (t : ℝ) : eChar ((k : ℝ) * t) = (eChar t) ^ k := by
  induction k with
  | zero => simp [eChar]
  | succ k ih =>
    rw [pow_succ, ← ih, ← eChar_add]
    congr 1
    push_cast
    ring

lemma integral_fejerKernel (M : ℕ) (hM : 1 ≤ M) :
    ∫ t in (0 : ℝ)..1, fejerKernel M t = 1 := by
  unfold fejerKernel
  rw [intervalIntegral.integral_const_mul]
  have hsum_eq : ∀ t : ℝ,
      ∑ k ∈ Finset.range M, eChar ((k : ℝ) * t) =
        ∑ n ∈ Finset.Ico (0 : ℤ) (M : ℤ), (1 : ℂ) * eChar ((n : ℝ) * t) := by
    intro t
    refine Finset.sum_nbij' (fun k => (k : ℤ)) (fun n => n.toNat) ?_ ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Ico]; omega
    · intro n hn; rw [Finset.mem_Ico] at hn; rw [Finset.mem_range]; omega
    · intro k _; simp
    · intro n hn; rw [Finset.mem_Ico] at hn; omega
    · intro k _; simp
  simp_rw [hsum_eq]
  rw [parseval_trig_poly]
  simp only [norm_one, one_pow, Finset.sum_const, Int.card_Ico, sub_zero, Int.toNat_natCast,
    nsmul_eq_mul, mul_one]
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  field_simp [hMne]

/-- Quantitative lower bound `4 * distToInt t ≤ ‖e(t) - 1‖` via Jordan's inequality. -/
lemma norm_eChar_sub_one_ge (t : ℝ) : 4 * distToInt t ≤ ‖eChar t - 1‖ := by
  set u : ℝ := t - (round t : ℝ)
  have hu_eq : eChar t = eChar u := by
    have : t = u + (round t : ℤ) := by simp [u]
    rw [this, eChar_add_int]
  rw [hu_eq]
  have hnorm_sq : ‖eChar u - 1‖ ^ 2 = (2 * Real.sin (Real.pi * |u|)) ^ 2 := by
    have heul : eChar u = Complex.cos ((2 * Real.pi * u : ℝ) : ℂ) +
        Complex.sin ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
      unfold eChar
      have harg : (2 : ℂ) * Real.pi * Complex.I * (u : ℂ) = ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_mul_I]
    have hre : (eChar u - 1).re = Real.cos (2 * Real.pi * u) - 1 := by
      rw [heul, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.cos_ofReal_re,
          Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re]
      ring
    have him : (eChar u - 1).im = Real.sin (2 * Real.pi * u) := by
      rw [heul, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.cos_ofReal_im,
          Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im]
      ring
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have hcos2 : Real.cos (2 * Real.pi * u) = 1 - 2 * Real.sin (Real.pi * u) ^ 2 := by
      have h := Real.cos_two_mul (Real.pi * u)
      have hsc := Real.sin_sq_add_cos_sq (Real.pi * u)
      have h2 : 2 * (Real.pi * u) = 2 * Real.pi * u := by ring
      rw [h2] at h
      linarith
    have hsin2 : Real.sin (2 * Real.pi * u) = 2 * Real.sin (Real.pi * u) * Real.cos (Real.pi * u) := by
      have h := Real.sin_two_mul (Real.pi * u)
      have h2 : 2 * (Real.pi * u) = 2 * Real.pi * u := by ring
      rw [h2] at h
      exact h
    have hsin_abs : Real.sin (Real.pi * |u|) ^ 2 = Real.sin (Real.pi * u) ^ 2 := by
      rcases le_or_gt 0 u with hu | hu
      · rw [abs_of_nonneg hu]
      · rw [abs_of_neg hu, mul_neg, Real.sin_neg, neg_sq]
    rw [hcos2, hsin2]
    have hsc := Real.sin_sq_add_cos_sq (Real.pi * u)
    nlinarith
  have hpiu_nn : 0 ≤ Real.pi * |u| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
  have hpiu_le : Real.pi * |u| ≤ Real.pi / 2 := by
    have hu_half : |u| ≤ 1 / 2 := abs_sub_round t
    nlinarith [Real.pi_pos]
  have hsin_nn : 0 ≤ Real.sin (Real.pi * |u|) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hpiu_nn (by linarith [Real.pi_pos])
  have hnorm_eq : ‖eChar u - 1‖ = 2 * Real.sin (Real.pi * |u|) := by
    nlinarith [norm_nonneg (eChar u - 1)]
  have hjordan : 2 / Real.pi * (Real.pi * |u|) ≤ Real.sin (Real.pi * |u|) :=
    Real.mul_le_sin hpiu_nn hpiu_le
  have hsimp : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by
    field_simp [Real.pi_ne_zero]
  rw [hsimp] at hjordan
  change 4 * |u| ≤ ‖eChar u - 1‖
  linarith

/-- Pointwise tail bound for the Fejér kernel away from `ℤ`. -/
lemma fejerKernel_le_of_distToInt (M : ℕ) (hM : 1 ≤ M) (t δ : ℝ) (hδ : 0 < δ)
    (ht : δ ≤ distToInt t) :
    fejerKernel M t ≤ 1 / (4 * (M : ℝ) * δ ^ 2) := by
  have hgeom : (∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)) * (eChar t - 1) =
      eChar ((M : ℝ) * t) - 1 := by
    simp_rw [eChar_nat_mul]
    exact geom_sum_mul (eChar t) M
  have hnorm_prod : ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ * ‖eChar t - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖eChar ((M : ℝ) * t) - 1‖ ≤ ‖eChar ((M : ℝ) * t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_eChar, norm_one]; norm_num
  have hden : 4 * δ ≤ ‖eChar t - 1‖ := by
    linarith [norm_eChar_sub_one_ge t]
  have hsum_le : ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ ≤ 1 / (2 * δ) := by
    have h1 : ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ * (4 * δ) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hden (norm_nonneg _)) hnorm_prod
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]
    linarith
  have hsq_le : ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ ^ 2 ≤ 1 / (4 * δ ^ 2) := by
    have h1 : ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ ^ 2 ≤ (1 / (2 * δ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsum_le 2
    have h2 : (1 / (2 * δ)) ^ 2 = 1 / (4 * δ ^ 2) := by ring
    linarith
  unfold fejerKernel
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  calc (1 / (M : ℝ)) * ‖∑ k ∈ Finset.range M, eChar ((k : ℝ) * t)‖ ^ 2
      ≤ (1 / (M : ℝ)) * (1 / (4 * δ ^ 2)) := mul_le_mul_of_nonneg_left hsq_le (by positivity)
    _ = 1 / (4 * (M : ℝ) * δ ^ 2) := by ring

/-- **Fejér's Uniform Trigonometric Polynomial Approximation Theorem:**
Every continuous 1-periodic function `f : ℝ → ℂ` can be uniformly approximated within any `ε > 0`
by a finite exponential polynomial `∑ h ∈ s, c h * e(h x)`. -/
theorem fejer_trig_approx (f : ℝ → ℂ) (hf_cont : Continuous f) (hf_per : Function.Periodic f 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), ∀ x : ℝ, ‖f x - ∑ h ∈ s, c h * eChar ((h : ℝ) * x)‖ < ε := by
  -- 1. Uniform bound `B ≥ 1` on `‖f x‖`
  have hbdd : ∃ B : ℝ, 1 ≤ B ∧ ∀ x : ℝ, ‖f x‖ ≤ B := by
    rcases (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hf_cont.continuousOn with ⟨C, hC⟩
    refine ⟨max C 1, le_max_right _ _, fun x => ?_⟩
    have hx : f x = f (Int.fract x) := by
      have : x = Int.fract x + (⌊x⌋ : ℝ) := by linarith [Int.fract_add_floor x]
      conv_lhs => rw [this]
      simpa [mul_one] using hf_per.int_mul ⌊x⌋ (Int.fract x)
    rw [hx]
    have hmem : Int.fract x ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    exact (hC (Int.fract x) hmem).trans (le_max_left _ _)
  rcases hbdd with ⟨B, hB1, hB⟩
  -- 2. Uniform continuity of `f` on `ℝ` via compactness of `[-1, 2]` and 1-periodicity
  have hunif : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∀ x t : ℝ, |t| ≤ δ → ‖f x - f (x - t)‖ ≤ ε / 2 := by
    have huc := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).uniformContinuousOn_of_continuous hf_cont.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    rcases huc (ε / 2) (by linarith) with ⟨δ0, hδ0_pos, hδ0⟩
    set δ := min (δ0 / 2) (1 / 4)
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδle : δ ≤ 1 / 4 := min_le_right _ _
    refine ⟨δ, hδpos, hδle, fun x t ht => ?_⟩
    have hx1 : f x = f (Int.fract x) := by
      have : x = Int.fract x + (⌊x⌋ : ℝ) := by linarith [Int.fract_add_floor x]
      conv_lhs => rw [this]
      simpa [mul_one] using hf_per.int_mul ⌊x⌋ (Int.fract x)
    have hx2 : f (x - t) = f (Int.fract x - t) := by
      have : x - t = (Int.fract x - t) + (⌊x⌋ : ℝ) := by linarith [Int.fract_add_floor x]
      conv_lhs => rw [this]
      simpa [mul_one] using hf_per.int_mul ⌊x⌋ (Int.fract x - t)
    rw [hx1, hx2]
    have hm1 : Int.fract x ∈ Set.Icc (-1 : ℝ) 2 :=
      ⟨by linarith [Int.fract_nonneg x], by linarith [Int.fract_lt_one x]⟩
    have hm2 : Int.fract x - t ∈ Set.Icc (-1 : ℝ) 2 := by
      have htab := abs_le.mp (ht.trans hδle)
      exact ⟨by linarith [Int.fract_nonneg x, htab.2], by linarith [Int.fract_lt_one x, htab.1]⟩
    have hdist : dist (Int.fract x) (Int.fract x - t) < δ0 := by
      rw [Real.dist_eq]
      have hsub : Int.fract x - (Int.fract x - t) = t := by ring
      rw [hsub]
      calc |t| ≤ δ := ht
        _ ≤ δ0 / 2 := min_le_left _ _
        _ < δ0 := by linarith
    have hlt := hδ0 (Int.fract x) hm1 (Int.fract x - t) hm2 hdist
    rw [dist_eq_norm] at hlt
    exact hlt.le
  rcases hunif with ⟨δ, hδpos, hδle, huc⟩
  -- 3. Choose `M ≥ 1` so that tail bound `B / (2 * M * δ^2) < ε / 2`
  set M : ℕ := max 1 (⌈B / (ε * δ ^ 2)⌉₊ + 1)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_big : B / (ε * δ ^ 2) < (M : ℝ) := by
    have h1 : B / (ε * δ ^ 2) ≤ (⌈B / (ε * δ ^ 2)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈B / (ε * δ ^ 2)⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by
      have hle : ⌈B / (ε * δ ^ 2)⌉₊ + 1 ≤ M := le_max_right 1 _
      have hcast : ((⌈B / (ε * δ ^ 2)⌉₊ + 1 : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hle
      simpa using hcast
    linarith
  have htail_bound : B / (2 * (M : ℝ) * δ ^ 2) < ε / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (M : ℝ) * δ ^ 2)]
    have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε * δ ^ 2)).mp hM_big
    nlinarith
  -- 4. Define the trigonometric polynomial `P x = ∑ h ∈ Icc (-M) M, c h * e(h x)`
  set s : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let pairCount : ℤ → ℕ := fun h =>
    ((Finset.range M ×ˢ Finset.range M).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = h)).card
  let c : ℤ → ℂ := fun h =>
    ((pairCount h : ℝ) : ℂ) * ((1 / (M : ℝ) : ℝ) : ℂ) *
      ∫ u in (0 : ℝ)..1, f u * eChar (-((h : ℝ) * u))
  refine ⟨s, c, fun x => ?_⟩
  -- 5. Show `∑ h ∈ s, c h * e(h x) = ∫ t in (-1/2)..(1/2), f (x - t) * fejerKernel M t`
  have hP_eq : ∑ h ∈ s, c h * eChar ((h : ℝ) * x) =
      ∫ t in (-1 / 2 : ℝ)..(1 / 2), f (x - t) * ((fejerKernel M t : ℝ) : ℂ) := by
    -- First rewrite RHS as `∫ u in 0..1, f u * fejerKernel M (x - u)`
    have hconv_eq :
        ∫ t in (-1 / 2 : ℝ)..(1 / 2), f (x - t) * ((fejerKernel M t : ℝ) : ℂ) =
          ∫ u in (0 : ℝ)..1, f u * ((fejerKernel M (x - u) : ℝ) : ℂ) := by
      have hper_g : Function.Periodic (fun u => f u * ((fejerKernel M (x - u) : ℝ) : ℂ)) 1 := by
        intro u
        have h1 : f (u + 1) = f u := hf_per u
        have h2 : fejerKernel M (x - (u + 1)) = fejerKernel M (x - u) := by
          have : x - u = (x - (u + 1)) + 1 := by ring
          rw [this, fejerKernel_periodic M]
        dsimp only
        rw [h1, h2]
      have hcont_g : Continuous (fun u => f u * ((fejerKernel M (x - u) : ℝ) : ℂ)) :=
        hf_cont.mul (Complex.continuous_ofReal.comp ((fejerKernel_continuous M).comp (continuous_const.sub continuous_id)))
      have hsub := intervalIntegral.integral_comp_sub_left
        (fun u => f u * ((fejerKernel M (x - u) : ℝ) : ℂ)) x (a := (-1 / 2 : ℝ)) (b := 1 / 2)
      -- `∫ t in (-1/2)..(1/2), g(x - t) = ∫ u in (x - 1/2)..(x + 1/2), g u`
      have hsimp1 : ∀ t : ℝ, x - (x - t) = t := fun t => by ring
      simp_rw [hsimp1] at hsub
      have hbounds : x - (-1 / 2 : ℝ) = (x - 1 / 2) + 1 := by ring
      rw [hsub, hbounds]
      exact intervalIntegral_periodic_unit _ hcont_g hper_g (x - 1 / 2)
    rw [hconv_eq]
    -- Expand `(fejerKernel M (x - u) : ℂ)` as a double sum over `Finset.range M ×ˢ Finset.range M`
    have hexpand : ∀ u : ℝ,
        f u * ((fejerKernel M (x - u) : ℝ) : ℂ) =
          ∑ p ∈ Finset.range M ×ˢ Finset.range M,
            (((1 / (M : ℝ) : ℝ) : ℂ) * (f u * eChar (-((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * u))) *
              eChar ((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * x)) := by
      intro u
      unfold fejerKernel
      rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul,
          Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [conj_eChar]
      have hprod : eChar ((j : ℝ) * (x - u)) * eChar (-((k : ℝ) * (x - u))) =
          eChar (-((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * u)) * eChar ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * x) := by
        rw [← eChar_add, ← eChar_add]
        congr 1; push_cast; ring
      dsimp only
      calc f u * (((1 / (M : ℝ) : ℝ) : ℂ) * (eChar ((j : ℝ) * (x - u)) * eChar (-((k : ℝ) * (x - u)))))
          = ((1 / (M : ℝ) : ℝ) : ℂ) * (f u * (eChar ((j : ℝ) * (x - u)) * eChar (-((k : ℝ) * (x - u))))) := by ring
        _ = ((1 / (M : ℝ) : ℝ) : ℂ) * (f u * (eChar (-((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * u)) *
              eChar ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * x))) := by rw [hprod]
        _ = ((1 / (M : ℝ) : ℝ) : ℂ) * (f u * eChar (-((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * u))) *
              eChar ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * x) := by ring
    simp_rw [hexpand]
    rw [intervalIntegral.integral_finsetSum]
    · have hterm_int : ∀ p : ℕ × ℕ,
          ∫ u in (0 : ℝ)..1,
            (((1 / (M : ℝ) : ℝ) : ℂ) * (f u * eChar (-((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * u))) *
              eChar ((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * x)) =
          ((1 / (M : ℝ) : ℝ) : ℂ) *
            (∫ u in (0 : ℝ)..1, f u * eChar (-((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * u))) *
            eChar ((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * x) := by
        intro p
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
      simp_rw [hterm_int]
      symm
      rw [← Finset.sum_fiberwise_of_maps_to (t := s) (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))]
      · apply Finset.sum_congr rfl
        intro h _
        have hconst : ∀ p ∈ (Finset.range M ×ˢ Finset.range M).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = h),
            ((1 / (M : ℝ) : ℝ) : ℂ) *
              (∫ u in (0 : ℝ)..1, f u * eChar (-((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * u))) *
              eChar ((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * x) =
            ((1 / (M : ℝ) : ℝ) : ℂ) *
              (∫ u in (0 : ℝ)..1, f u * eChar (-((h : ℝ) * u))) * eChar ((h : ℝ) * x) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [hp.2]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
        simp only [c, pairCount, Complex.ofReal_natCast]
        ring
      · intro p hp
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
        rw [Finset.mem_Icc]
        omega
    · intro p _
      have hc : Continuous (fun u : ℝ =>
          ((1 / (M : ℝ) : ℝ) : ℂ) * (f u * eChar (-((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * u))) *
            eChar ((((p.1 : ℤ) - (p.2 : ℤ) : ℤ) : ℝ) * x)) := by
        unfold eChar
        fun_prop
      exact hc.intervalIntegrable 0 1
  rw [hP_eq]
  -- 6. Bound `‖f x - ∫_{-1/2}^{1/2} f(x - t) K_M(t) dt‖ < ε`
  have hK_int_half : ∫ t in (-1 / 2 : ℝ)..(1 / 2), fejerKernel M t = 1 := by
    have h1 : (1 / 2 : ℝ) = (-1 / 2 : ℝ) + 1 := by ring
    rw [h1, intervalIntegral_periodic_unit _ (fejerKernel_continuous M) (fejerKernel_periodic M) (-1 / 2),
        integral_fejerKernel M hM1]
  have hdiff_int :
      f x - ∫ t in (-1 / 2 : ℝ)..(1 / 2), f (x - t) * ((fejerKernel M t : ℝ) : ℂ) =
        ∫ t in (-1 / 2 : ℝ)..(1 / 2), (f x - f (x - t)) * ((fejerKernel M t : ℝ) : ℂ) := by
    have hfx_int : f x = ∫ t in (-1 / 2 : ℝ)..(1 / 2), f x * ((fejerKernel M t : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hK_int_half,
          Complex.ofReal_one, mul_one]
    have hi1 : IntervalIntegrable (fun t => f x * ((fejerKernel M t : ℝ) : ℂ)) volume (-1 / 2) (1 / 2) :=
      (continuous_const.mul (Complex.continuous_ofReal.comp (fejerKernel_continuous M))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => f (x - t) * ((fejerKernel M t : ℝ) : ℂ)) volume (-1 / 2) (1 / 2) :=
      ((hf_cont.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_ofReal.comp (fejerKernel_continuous M))).intervalIntegrable _ _
    conv_lhs => rw [hfx_int]
    rw [← intervalIntegral.integral_sub hi1 hi2]
    congr 1; funext t; ring
  rw [hdiff_int]
  have hnorm_le :
      ‖∫ t in (-1 / 2 : ℝ)..(1 / 2), (f x - f (x - t)) * ((fejerKernel M t : ℝ) : ℂ)‖ ≤
        ∫ t in (-1 / 2 : ℝ)..(1 / 2), ‖f x - f (x - t)‖ * fejerKernel M t := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (a := (-1 / 2 : ℝ)) (b := 1 / 2) (by norm_num)
      (f := fun t => (f x - f (x - t)) * ((fejerKernel M t : ℝ) : ℂ))
    have hnorm_eq : ∀ t, ‖(f x - f (x - t)) * ((fejerKernel M t : ℝ) : ℂ)‖ =
        ‖f x - f (x - t)‖ * fejerKernel M t := by
      intro t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg M t)]
    simpa only [hnorm_eq] using h1
  set ψ : ℝ → ℝ := fun t => ‖f x - f (x - t)‖ * fejerKernel M t
  have hψ_cont : Continuous ψ :=
    ((continuous_const.sub (hf_cont.comp (continuous_const.sub continuous_id))).norm).mul
      (fejerKernel_continuous M)
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hψ_cont.intervalIntegrable (-1 / 2) (-δ)) (hψ_cont.intervalIntegrable (-δ) δ)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hψ_cont.intervalIntegrable (-1 / 2) δ) (hψ_cont.intervalIntegrable δ (1 / 2))
  -- Middle piece `[-δ, δ]`
  have hmid : ∫ t in (-δ)..δ, ψ t ≤ ε / 2 := by
    have hle1 : ∫ t in (-δ)..δ, ψ t ≤ ∫ t in (-δ)..δ, (ε / 2) * fejerKernel M t := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hψ_cont.intervalIntegrable _ _) ((continuous_const.mul (fejerKernel_continuous M)).intervalIntegrable _ _)
      intro t ht
      have htab : |t| ≤ δ := abs_le.mpr ht
      exact mul_le_mul_of_nonneg_right (huc x t htab) (fejerKernel_nonneg M t)
    have hK_mid_le : ∫ t in (-δ)..δ, fejerKernel M t ≤ 1 := by
      have hK1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        ((fejerKernel_continuous M).intervalIntegrable (-1 / 2) (-δ))
        ((fejerKernel_continuous M).intervalIntegrable (-δ) δ)
      have hK2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        ((fejerKernel_continuous M).intervalIntegrable (-1 / 2) δ)
        ((fejerKernel_continuous M).intervalIntegrable δ (1 / 2))
      have hnn1 : (0 : ℝ) ≤ ∫ t in (-1 / 2 : ℝ)..(-δ), fejerKernel M t :=
        intervalIntegral.integral_nonneg (μ := volume) (by linarith) (fun t _ => fejerKernel_nonneg M t)
      have hnn2 : (0 : ℝ) ≤ ∫ t in δ..(1 / 2 : ℝ), fejerKernel M t :=
        intervalIntegral.integral_nonneg (μ := volume) (by linarith) (fun t _ => fejerKernel_nonneg M t)
      linarith
    rw [intervalIntegral.integral_const_mul] at hle1
    nlinarith
  -- Tail pieces `[-1/2, -δ]` and `[δ, 1/2]`
  have hdist_tail : ∀ t : ℝ, |t| ≤ 1 / 2 → δ ≤ |t| → δ ≤ distToInt t := by
    intro t ht_half ht_ge
    have hround : round t = 0 ∨ |t| = 1 / 2 := by
      by_cases hlt : |t| < 1 / 2
      · left
        have h1 : |t - (round t : ℝ)| ≤ 1 / 2 := abs_sub_round t
        have h2 : |(round t : ℝ)| < 1 := by
          have habs1 := abs_lt.mp hlt
          have habs2 := abs_le.mp h1
          rw [abs_lt]; constructor <;> linarith
        have h3 : |round t| < 1 := by exact_mod_cast h2
        rw [abs_lt] at h3; omega
      · right; linarith
    rcases hround with h0 | heq
    · unfold distToInt; rw [h0]; simpa using ht_ge
    · have : distToInt t = 1 / 2 := by
        unfold distToInt
        rcases eq_or_eq_neg_of_abs_eq heq with rfl | rfl
        · have : round (1 / 2 : ℝ) = 1 := by rw [round_eq]; norm_num
          rw [this]; norm_num
        · have : round (-(1 / 2 : ℝ)) = 0 := by rw [round_eq]; norm_num
          rw [this]; norm_num
      linarith
  have htail_pt : ∀ t : ℝ, |t| ≤ 1 / 2 → δ ≤ |t| → ψ t ≤ (2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2)) := by
    intro t ht_half ht_ge
    have hfnorm : ‖f x - f (x - t)‖ ≤ 2 * B := by
      calc ‖f x - f (x - t)‖ ≤ ‖f x‖ + ‖f (x - t)‖ := norm_sub_le _ _
        _ ≤ B + B := add_le_add (hB x) (hB (x - t))
        _ = 2 * B := by ring
    exact mul_le_mul hfnorm (fejerKernel_le_of_distToInt M hM1 t δ hδpos (hdist_tail t ht_half ht_ge))
      (fejerKernel_nonneg M t) (by positivity)
  have hleft_tail : ∫ t in (-1 / 2 : ℝ)..(-δ), ψ t ≤ (1 / 2) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
    calc ∫ t in (-1 / 2 : ℝ)..(-δ), ψ t
        ≤ ∫ _t in (-1 / 2 : ℝ)..(-δ), ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
          apply intervalIntegral.integral_mono_on (by linarith) (hψ_cont.intervalIntegrable _ _)
            intervalIntegrable_const
          intro t ht
          apply htail_pt t (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
          rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2]
      _ = (-δ - (-1 / 2)) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (1 / 2) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hright_tail : ∫ t in δ..(1 / 2 : ℝ), ψ t ≤ (1 / 2) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
    calc ∫ t in δ..(1 / 2 : ℝ), ψ t
        ≤ ∫ _t in δ..(1 / 2 : ℝ), ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
          apply intervalIntegral.integral_mono_on (by linarith) (hψ_cont.intervalIntegrable _ _)
            intervalIntegrable_const
          intro t ht
          apply htail_pt t (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
          rw [abs_of_pos (by linarith [ht.1])]; exact ht.1
      _ = (1 / 2 - δ) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (1 / 2) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have htail_sum :
      (1 / 2) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) +
        (1 / 2) * ((2 * B) * (1 / (4 * (M : ℝ) * δ ^ 2))) = B / (2 * (M : ℝ) * δ ^ 2) := by
    ring
  linarith

/-- Helper: a continuous function `g : ℝ → ℝ` on `[0, 1]` with `g 0 = 0 = g 1` composes with
`Int.fract` to give a continuous 1-periodic function on all of `ℝ`. -/
lemma continuous_comp_fract_of_zero_endpoints (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) :
    Continuous (fun t : ℝ => g (Int.fract t)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_cases hx_int : Int.fract x = 0
  · -- At integer `x`: `Int.fract x = 0`, and near `x`, `Int.fract y` is near `0` (for `y ≥ x`) or near `1` (for `y < x`)
    have h0 := Metric.continuousAt_iff.mp (hg.continuousAt (x := 0)) ε hε
    have h1 := Metric.continuousAt_iff.mp (hg.continuousAt (x := 1)) ε hε
    rcases h0 with ⟨δ0, hδ0_pos, hδ0⟩
    rcases h1 with ⟨δ1, hδ1_pos, hδ1⟩
    set δ := min (min δ0 δ1) (1 / 2)
    have hδpos : 0 < δ := lt_min (lt_min hδ0_pos hδ1_pos) (by norm_num)
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy ⊢
    rw [hx_int, hg0]
    have hx_eq : x = (⌊x⌋ : ℝ) := by linarith [Int.fract_add_floor x]
    rcases le_or_gt x y with hxy | hyx
    · have hfl : ⌊y⌋ = ⌊x⌋ := by
        apply Int.floor_eq_iff.mpr
        have hlt : y - x < 1 / 2 := (abs_lt.mp (lt_of_lt_of_le hy (min_le_right _ _))).2
        exact ⟨by linarith, by linarith⟩
      have hfy : Int.fract y = y - x := by
        show y - (⌊y⌋ : ℝ) = y - x; rw [hfl, ← hx_eq]
      rw [hfy]
      have hd0 : dist (y - x) 0 < δ0 := by
        rw [Real.dist_eq, sub_zero]
        exact lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
      simpa [Real.dist_eq, hg0] using hδ0 hd0
    · have hfl : ⌊y⌋ = ⌊x⌋ - 1 := by
        apply Int.floor_eq_iff.mpr
        have hgt : -(1 / 2) < y - x := (abs_lt.mp (lt_of_lt_of_le hy (min_le_right _ _))).1
        push_cast; exact ⟨by linarith, by linarith⟩
      have hfy : Int.fract y = y - x + 1 := by
        show y - (⌊y⌋ : ℝ) = y - x + 1; rw [hfl]; push_cast; linarith
      rw [hfy]
      have hd1 : dist (y - x + 1) 1 < δ1 := by
        rw [Real.dist_eq, add_sub_cancel_right]
        exact lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _))
      simpa [Real.dist_eq, hg1] using hδ1 hd1
  · -- Non-integer `x`: `0 < Int.fract x < 1`, so `Int.floor` is locally constant around `x`
    have hfx_pos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx_int)
    have hfx_lt1 : Int.fract x < 1 := Int.fract_lt_one x
    have hcont_g := Metric.continuousAt_iff.mp (hg.continuousAt (x := Int.fract x)) ε hε
    rcases hcont_g with ⟨δ0, hδ0_pos, hδ0⟩
    set δ := min δ0 (min (Int.fract x) (1 - Int.fract x))
    have hδpos : 0 < δ := lt_min hδ0_pos (lt_min hfx_pos (by linarith))
    refine ⟨δ, hδpos, fun y hy => ?_⟩
    rw [Real.dist_eq] at hy
    have hfl : ⌊y⌋ = ⌊x⌋ := by
      apply Int.floor_eq_iff.mpr
      have habs := abs_lt.mp hy
      have hle1 : δ ≤ Int.fract x := (min_le_right _ _).trans (min_le_left _ _)
      have hle2 : δ ≤ 1 - Int.fract x := (min_le_right _ _).trans (min_le_right _ _)
      have hxf : x - (⌊x⌋ : ℝ) = Int.fract x := rfl
      exact ⟨by linarith, by linarith⟩
    have hdiff : Int.fract y - Int.fract x = y - x := by
      show (y - (⌊y⌋ : ℝ)) - (x - (⌊x⌋ : ℝ)) = y - x
      rw [hfl]; ring
    apply hδ0
    rw [Real.dist_eq, hdiff]
    exact lt_of_lt_of_le hy (min_le_left _ _)

/-- **Weyl Criterion Part 1:** Exponential sums tending to `0` imply continuous 1-periodic
Cesàro averages converge to `∫_0^1 f`. -/
theorem weyl_continuous_of_exp (x : ℕ → ℝ)
    (hexp : ∀ h : ℤ, h ≠ 0 →
      Filter.Tendsto
        (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, eChar ((h : ℝ) * x n))
        Filter.atTop (nhds 0)) :
    ∀ f : ℝ → ℂ, Continuous f → Function.Periodic f 1 →
      Filter.Tendsto
        (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n))
        Filter.atTop (nhds (∫ t in (0 : ℝ)..1, f t)) := by
  intro f hf_cont hf_per
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases fejer_trig_approx f hf_cont hf_per (by linarith : 0 < ε / 3) with ⟨s, c, happrox⟩
  let P : ℝ → ℂ := fun t => ∑ h ∈ s, c h * eChar ((h : ℝ) * t)
  have hP_int : ∫ t in (0 : ℝ)..1, P t = if (0 : ℤ) ∈ s then c 0 else 0 := by
    simp only [P]
    rw [intervalIntegral.integral_finsetSum]
    · trans ∑ h ∈ s, c h * (if h = 0 then (1 : ℂ) else 0)
      · apply Finset.sum_congr rfl
        intro h _
        rw [intervalIntegral.integral_const_mul, integral_eChar_int]
      · split_ifs with h0
        · rw [Finset.sum_eq_single 0]
          · simp
          · intro h _ hne; simp [hne]
          · intro hn; exact absurd h0 hn
        · apply Finset.sum_eq_zero
          intro h hh
          have hne : h ≠ 0 := fun heq => h0 (heq ▸ hh)
          simp [hne]
    · intro h _
      have hc : Continuous (fun t : ℝ => c h * eChar ((h : ℝ) * t)) := by unfold eChar; fun_prop
      exact hc.intervalIntegrable 0 1
  -- Cesàro averages of `P` converge to `∫_0^1 P`
  have hP_tend : Filter.Tendsto
      (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n))
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, P t)) := by
    have hterm : ∀ h ∈ s, Filter.Tendsto
        (fun N : ℕ => c h * (((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, eChar ((h : ℝ) * x n)))
        Filter.atTop (nhds (c h * (if h = 0 then (1 : ℂ) else 0))) := by
      intro h _
      by_cases hh : h = 0
      · subst hh
        simp only [↓reduceIte, mul_one]
        have hev : ∀ᶠ N : ℕ in Filter.atTop,
            c 0 * (((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, eChar ((0 : ℤ) * x n)) = c 0 := by
          filter_upwards [Filter.eventually_ge_atTop 1] with N hN
          have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
          simp only [Int.cast_zero, zero_mul, eChar, Complex.ofReal_zero, mul_zero,
            Complex.exp_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          have : ((1 / (N : ℝ) : ℝ) : ℂ) * (N : ℂ) = 1 := by
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
            simp [hNne]
          rw [this, mul_one]
        exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
      · simp only [hh, ↓reduceIte, mul_zero]
        simpa [mul_zero] using (hexp h hh).const_mul (c h)
    have hsum_tend := tendsto_finsetSum s hterm
    have hlim_eq : ∑ h ∈ s, c h * (if h = 0 then (1 : ℂ) else 0) = ∫ t in (0 : ℝ)..1, P t := by
      rw [hP_int]
      split_ifs with h0
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro h _ hne; simp [hne]
        · intro hn; exact absurd h0 hn
      · apply Finset.sum_eq_zero
        intro h hh
        have hne : h ≠ 0 := fun heq => h0 (heq ▸ hh)
        simp [hne]
    rw [hlim_eq] at hsum_tend
    refine hsum_tend.congr fun N => ?_
    simp only [P]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [← Finset.mul_sum]
    ring
  rw [Metric.tendsto_atTop] at hP_tend
  rcases hP_tend (ε / 3) (by linarith) with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h1 : ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
      ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n)‖ ≤ ε / 3 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hNpos)]
    calc (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, (f (x n) - P (x n))‖
        ≤ (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ‖f (x n) - P (x n)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (1 / (N : ℝ)) * ∑ _n ∈ Finset.range N, (ε / 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => (happrox (x n)).le) (by positivity)
      _ = ε / 3 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [hNpos.ne']
  have h2 : ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n) - ∫ t in (0 : ℝ)..1, P t‖ < ε / 3 := by
    simpa [dist_eq_norm] using hN₀ N ((le_max_left N₀ 1).trans hN)
  have h3 : ‖(∫ t in (0 : ℝ)..1, P t) - ∫ t in (0 : ℝ)..1, f t‖ ≤ ε / 3 := by
    have hP_cont : Continuous P := by unfold P eChar; fun_prop
    rw [← intervalIntegral.integral_sub (hP_cont.intervalIntegrable 0 1) (hf_cont.intervalIntegrable 0 1)]
    calc ‖∫ t in (0 : ℝ)..1, (P t - f t)‖
        ≤ ∫ t in (0 : ℝ)..1, ‖P t - f t‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ _t in (0 : ℝ)..1, (ε / 3) := by
          apply intervalIntegral.integral_mono_on (by norm_num)
            ((hP_cont.sub hf_cont).norm.intervalIntegrable 0 1) intervalIntegrable_const
          intro t _
          change ‖P t - f t‖ ≤ ε / 3
          rw [norm_sub_rev]
          exact (happrox t).le
      _ = ε / 3 := by simp
  rw [dist_eq_norm]
  calc ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) - ∫ t in (0 : ℝ)..1, f t‖
      = ‖(((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
            ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n)) +
          ((((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n) - ∫ t in (0 : ℝ)..1, P t) +
            ((∫ t in (0 : ℝ)..1, P t) - ∫ t in (0 : ℝ)..1, f t))‖ := by congr 1; ring
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
            ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n)‖ +
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n) - ∫ t in (0 : ℝ)..1, P t) +
            ((∫ t in (0 : ℝ)..1, P t) - ∫ t in (0 : ℝ)..1, f t)‖ := norm_add_le _ _
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
            ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n)‖ +
          (‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, P (x n) - ∫ t in (0 : ℝ)..1, P t‖ +
            ‖(∫ t in (0 : ℝ)..1, P t) - ∫ t in (0 : ℝ)..1, f t‖) :=
        add_le_add le_rfl (norm_add_le _ _)
    _ < ε := by linarith

/-- **Weyl Criterion Part 2:** Convergence for all continuous 1-periodic functions implies
`EquidistributedMod1 x`. -/
theorem equidistributed_of_continuous (x : ℕ → ℝ)
    (hcont : ∀ f : ℝ → ℂ, Continuous f → Function.Periodic f 1 →
      Filter.Tendsto
        (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n))
        Filter.atTop (nhds (∫ t in (0 : ℝ)..1, f t))) :
    EquidistributedMod1 x := by
  -- Extract real-valued continuous 1-periodic convergence
  have hreal : ∀ g : ℝ → ℝ, Continuous g → Function.Periodic g 1 →
      Filter.Tendsto
        (fun N : ℕ => (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, g (x n))
        Filter.atTop (nhds (∫ t in (0 : ℝ)..1, g t)) := by
    intro g hg_cont hg_per
    have hC := hcont (fun t => (g t : ℂ)) (Complex.continuous_ofReal.comp hg_cont)
      (fun t => by simp [hg_per t])
    have hre := (Complex.continuous_re.tendsto _).comp hC
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re] at hre
    refine hre.congr fun N => ?_
    simp [← Complex.ofReal_sum]
  intro a b ha hab hb
  by_cases heq_ab : a = b
  · subst heq_ab
    simp only [sub_self]
    refine tendsto_const_nhds.congr fun N => ?_
    have hempty : (Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < a) = ∅ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
      intro _ h; linarith
    simp [hempty]
  · by_cases hfull : a = 0 ∧ b = 1
    · rcases hfull with ⟨rfl, rfl⟩
      simp only [sub_zero]
      have hev : ∀ᶠ N : ℕ in Filter.atTop,
          (((Finset.range N).filter (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1)).card : ℝ) /
            (N : ℝ) = 1 := by
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        have hfilt : (Finset.range N).filter (fun n => (0 : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < 1) =
            Finset.range N := by
          ext n; simp [Int.fract_nonneg, Int.fract_lt_one]
        rw [hfilt, Finset.card_range]
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
        exact div_self hNne
      exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
    · -- Proper non-empty subinterval `0 < b - a < 1`: shift `[a, b)` to interior `[a', b') ⊂ (0, 1)`
      have hL_pos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq_ab)
      have hL_lt1 : b - a < 1 := by
        by_contra hge
        have : a = 0 ∧ b = 1 := ⟨by linarith, by linarith⟩
        exact hfull this
      set L := b - a
      set shift := (1 - (a + b)) / 2
      set a' := (1 - L) / 2
      set b' := (1 + L) / 2
      have ha'_pos : 0 < a' := by simp only [a']; linarith
      have hb'_lt1 : b' < 1 := by simp only [b']; linarith
      have hab'_lt : a' < b' := by simp only [a', b']; linarith
      have hL' : b' - a' = L := by ring
      -- Exact equivalence: `fract y ∈ [a, b) ↔ fract (y + shift) ∈ [a', b')`
      have hshift_iff : ∀ y : ℝ,
          (a ≤ Int.fract y ∧ Int.fract y < b) ↔
            (a' ≤ Int.fract (y + shift) ∧ Int.fract (y + shift) < b') := by
        intro y
        have hsh_eq1 : a + shift = a' := by ring
        have hsh_eq2 : b + shift = b' := by ring
        constructor
        · rintro ⟨h1, h2⟩
          have hfl : ⌊y + shift⌋ = ⌊y⌋ := by
            apply Int.floor_eq_iff.mpr
            have hf : Int.fract y = y - (⌊y⌋ : ℝ) := rfl
            exact ⟨by linarith, by linarith⟩
          have hfr : Int.fract (y + shift) = Int.fract y + shift := by
            show y + shift - (⌊y + shift⌋ : ℝ) = (y - (⌊y⌋ : ℝ)) + shift
            rw [hfl]; ring
          rw [hfr]; exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩
          have hfl : ⌊y⌋ = ⌊y + shift⌋ := by
            apply Int.floor_eq_iff.mpr
            have hf : Int.fract (y + shift) = y + shift - (⌊y + shift⌋ : ℝ) := rfl
            exact ⟨by linarith, by linarith⟩
          have hfr : Int.fract y = Int.fract (y + shift) - shift := by
            show y - (⌊y⌋ : ℝ) = (y + shift - (⌊y + shift⌋ : ℝ)) - shift
            rw [hfl]; ring
          rw [hfr]; exact ⟨by linarith, by linarith⟩
      -- Prove convergence via trapezoid sandwich around `[a', b')`
      rw [Metric.tendsto_atTop]
      intro ε hε
      set η := min (min (a' / 2) ((1 - b') / 2)) (min ((b' - a') / 4) (ε / 4))
      have hη_pos : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
      have hη_a : η < a' := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
      have hη_b : η < 1 - b' := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
      have hη_L : 2 * η < b' - a' := by
        have : η ≤ (b' - a') / 4 := (min_le_right _ _).trans (min_le_left _ _)
        linarith
      have hη_ε : 2 * η < ε := by
        have : η ≤ ε / 4 := (min_le_right _ _).trans (min_le_right _ _)
        linarith
      -- Trapezoid constructor on `[0, 1]`
      let trap : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun u₁ u₂ v₁ v₂ t =>
        max 0 (min 1 (min ((t - u₁) / (u₂ - u₁)) ((v₂ - t) / (v₂ - v₁))))
      have htrap_cont : ∀ u₁ u₂ v₁ v₂, Continuous (trap u₁ u₂ v₁ v₂) := fun u₁ u₂ v₁ v₂ => by
        unfold trap; fun_prop
      have htrap_01 : ∀ u₁ u₂ v₁ v₂ t, 0 ≤ trap u₁ u₂ v₁ v₂ t ∧ trap u₁ u₂ v₁ v₂ t ≤ 1 := by
        intro u₁ u₂ v₁ v₂ t
        unfold trap
        exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
      have htrap_zero_left : ∀ u₁ u₂ v₁ v₂ t, u₁ < u₂ → t ≤ u₁ → trap u₁ u₂ v₁ v₂ t = 0 := by
        intro u₁ u₂ v₁ v₂ t hu ht
        unfold trap
        have hdiv : (t - u₁) / (u₂ - u₁) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        have hm1 : min ((t - u₁) / (u₂ - u₁)) ((v₂ - t) / (v₂ - v₁)) ≤ 0 := (min_le_left _ _).trans hdiv
        have hm2 : min 1 (min ((t - u₁) / (u₂ - u₁)) ((v₂ - t) / (v₂ - v₁))) ≤ 0 := (min_le_right _ _).trans hm1
        exact max_eq_left hm2
      have htrap_zero_right : ∀ u₁ u₂ v₁ v₂ t, v₁ < v₂ → v₂ ≤ t → trap u₁ u₂ v₁ v₂ t = 0 := by
        intro u₁ u₂ v₁ v₂ t hv ht
        unfold trap
        have hdiv : (v₂ - t) / (v₂ - v₁) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        have hm1 : min ((t - u₁) / (u₂ - u₁)) ((v₂ - t) / (v₂ - v₁)) ≤ 0 := (min_le_right _ _).trans hdiv
        have hm2 : min 1 (min ((t - u₁) / (u₂ - u₁)) ((v₂ - t) / (v₂ - v₁))) ≤ 0 := (min_le_right _ _).trans hm1
        exact max_eq_left hm2
      have htrap_one : ∀ u₁ u₂ v₁ v₂ t, u₁ < u₂ → v₁ < v₂ → u₂ ≤ t → t ≤ v₁ → trap u₁ u₂ v₁ v₂ t = 1 := by
        intro u₁ u₂ v₁ v₂ t hu hv ht1 ht2
        unfold trap
        have h1 : 1 ≤ (t - u₁) / (u₂ - u₁) := (one_le_div (by linarith)).mpr (by linarith)
        have h2 : 1 ≤ (v₂ - t) / (v₂ - v₁) := (one_le_div (by linarith)).mpr (by linarith)
        have hm : min 1 (min ((t - u₁) / (u₂ - u₁)) ((v₂ - t) / (v₂ - v₁))) = 1 :=
          min_eq_left (le_min h1 h2)
        rw [hm]; norm_num
      -- Upper and lower 1-periodic continuous functions on shifted argument `t + shift`
      let gPlus : ℝ → ℝ := fun t => trap (a' - η) a' b' (b' + η) (Int.fract (t + shift))
      let gMinus : ℝ → ℝ := fun t => trap a' (a' + η) (b' - η) b' (Int.fract (t + shift))
      have hgPlus_cont : Continuous gPlus :=
        (continuous_comp_fract_of_zero_endpoints _ (htrap_cont _ _ _ _)
          (htrap_zero_left _ _ _ _ 0 (by linarith) (by linarith))
          (htrap_zero_right _ _ _ _ 1 (by linarith) (by linarith))).comp (continuous_id.add continuous_const)
      have hgMinus_cont : Continuous gMinus :=
        (continuous_comp_fract_of_zero_endpoints _ (htrap_cont _ _ _ _)
          (htrap_zero_left _ _ _ _ 0 (by linarith) (by linarith))
          (htrap_zero_right _ _ _ _ 1 (by linarith) (by linarith))).comp (continuous_id.add continuous_const)
      have hgPlus_per : Function.Periodic gPlus 1 := fun t => by
        simp only [gPlus]
        have : t + 1 + shift = (t + shift) + (1 : ℤ) := by push_cast; ring
        rw [this, Int.fract_add_intCast]
      have hgMinus_per : Function.Periodic gMinus 1 := fun t => by
        simp only [gMinus]
        have : t + 1 + shift = (t + shift) + (1 : ℤ) := by push_cast; ring
        rw [this, Int.fract_add_intCast]
      -- Integral bounds for `gPlus` and `gMinus`
      have hgPlus_int : ∫ t in (0 : ℝ)..1, gPlus t ≤ L + 2 * η := by
        have hsh : ∫ t in (0 : ℝ)..1, gPlus t = ∫ u in (0 : ℝ)..1, trap (a' - η) a' b' (b' + η) u := by
          have h1 : ∫ t in (0 : ℝ)..1, gPlus t =
              ∫ u in shift..(shift + 1), trap (a' - η) a' b' (b' + η) (Int.fract u) := by
            have := intervalIntegral.integral_comp_add_right
              (fun u => trap (a' - η) a' b' (b' + η) (Int.fract u)) shift (a := (0 : ℝ)) (b := 1)
            rw [zero_add, add_comm 1 shift] at this
            exact this
          have h2 := intervalIntegral_periodic_unit
            (fun u => trap (a' - η) a' b' (b' + η) (Int.fract u))
            (continuous_comp_fract_of_zero_endpoints _ (htrap_cont _ _ _ _)
              (htrap_zero_left _ _ _ _ 0 (by linarith) (by linarith))
              (htrap_zero_right _ _ _ _ 1 (by linarith) (by linarith)))
            (fun u => by simp [Int.fract_add_one]) shift
          rw [h1, h2]
          apply intervalIntegral.integral_congr_ae
          filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ))] with u hu hmem
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
          have hne1 : u ≠ 1 := hu
          have hlt1 : u < 1 := lt_of_le_of_ne hmem.2 hne1
          have hfl : ⌊u⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hmem.1.le, hlt1⟩
          have hfr : Int.fract u = u := by show u - (⌊u⌋ : ℝ) = u; rw [hfl]; simp
          rw [hfr]
        rw [hsh]
        set F := trap (a' - η) a' b' (b' + η)
        have hFc := htrap_cont (a' - η) a' b' (b' + η)
        have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hFc.intervalIntegrable 0 (a' - η)) (hFc.intervalIntegrable (a' - η) (b' + η))
        have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hFc.intervalIntegrable 0 (b' + η)) (hFc.intervalIntegrable (b' + η) 1)
        have hI1 : ∫ u in (0 : ℝ)..(a' - η), F u = 0 := by
          trans (∫ _u in (0 : ℝ)..(a' - η), (0 : ℝ))
          · apply intervalIntegral.integral_congr
            intro u hu
            rw [Set.uIcc_of_le (by linarith)] at hu
            exact htrap_zero_left _ _ _ _ u (by linarith) hu.2
          · exact intervalIntegral.integral_zero
        have hI3 : ∫ u in (b' + η)..1, F u = 0 := by
          trans (∫ _u in (b' + η)..1, (0 : ℝ))
          · apply intervalIntegral.integral_congr
            intro u hu
            rw [Set.uIcc_of_le (by linarith)] at hu
            exact htrap_zero_right _ _ _ _ u (by linarith) hu.1
          · exact intervalIntegral.integral_zero
        have hI2 : ∫ u in (a' - η)..(b' + η), F u ≤ (b' + η) - (a' - η) := by
          calc ∫ u in (a' - η)..(b' + η), F u
              ≤ ∫ _u in (a' - η)..(b' + η), (1 : ℝ) :=
                intervalIntegral.integral_mono_on (by linarith) (hFc.intervalIntegrable _ _)
                  intervalIntegrable_const (fun u _ => (htrap_01 _ _ _ _ u).2)
            _ = (b' + η) - (a' - η) := by simp
        linarith
      have hgMinus_int : L - 2 * η ≤ ∫ t in (0 : ℝ)..1, gMinus t := by
        have hsh : ∫ t in (0 : ℝ)..1, gMinus t = ∫ u in (0 : ℝ)..1, trap a' (a' + η) (b' - η) b' u := by
          have h1 : ∫ t in (0 : ℝ)..1, gMinus t =
              ∫ u in shift..(shift + 1), trap a' (a' + η) (b' - η) b' (Int.fract u) := by
            have := intervalIntegral.integral_comp_add_right
              (fun u => trap a' (a' + η) (b' - η) b' (Int.fract u)) shift (a := (0 : ℝ)) (b := 1)
            rw [zero_add, add_comm 1 shift] at this
            exact this
          have h2 := intervalIntegral_periodic_unit
            (fun u => trap a' (a' + η) (b' - η) b' (Int.fract u))
            (continuous_comp_fract_of_zero_endpoints _ (htrap_cont _ _ _ _)
              (htrap_zero_left _ _ _ _ 0 (by linarith) (by linarith))
              (htrap_zero_right _ _ _ _ 1 (by linarith) (by linarith)))
            (fun u => by simp [Int.fract_add_one]) shift
          rw [h1, h2]
          apply intervalIntegral.integral_congr_ae
          filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ))] with u hu hmem
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
          have hne1 : u ≠ 1 := hu
          have hlt1 : u < 1 := lt_of_le_of_ne hmem.2 hne1
          have hfl : ⌊u⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hmem.1.le, hlt1⟩
          have hfr : Int.fract u = u := by show u - (⌊u⌋ : ℝ) = u; rw [hfl]; simp
          rw [hfr]
        rw [hsh]
        set F := trap a' (a' + η) (b' - η) b'
        have hFc := htrap_cont a' (a' + η) (b' - η) b'
        have hs1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hFc.intervalIntegrable 0 (a' + η)) (hFc.intervalIntegrable (a' + η) (b' - η))
        have hs2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
          (hFc.intervalIntegrable 0 (b' - η)) (hFc.intervalIntegrable (b' - η) 1)
        have hI1 : (0 : ℝ) ≤ ∫ u in (0 : ℝ)..(a' + η), F u :=
          intervalIntegral.integral_nonneg (μ := volume) (by linarith) (fun u _ => (htrap_01 _ _ _ _ u).1)
        have hI3 : (0 : ℝ) ≤ ∫ u in (b' - η)..1, F u :=
          intervalIntegral.integral_nonneg (μ := volume) (by linarith) (fun u _ => (htrap_01 _ _ _ _ u).1)
        have hI2 : ∫ u in (a' + η)..(b' - η), F u = (b' - η) - (a' + η) := by
          calc ∫ u in (a' + η)..(b' - η), F u
              = ∫ _u in (a' + η)..(b' - η), (1 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro u hu
                rw [Set.uIcc_of_le (by linarith)] at hu
                exact htrap_one _ _ _ _ u (by linarith) (by linarith) hu.1 hu.2
            _ = (b' - η) - (a' + η) := by simp
        linarith
      -- Pointwise sandwich `gMinus (x n) ≤ 1_{[a, b)}(fract (x n)) ≤ gPlus (x n)`
      have hsand : ∀ n : ℕ,
          gMinus (x n) ≤ (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) ∧
          (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) ≤ gPlus (x n) := by
        intro n
        by_cases hmem : a ≤ Int.fract (x n) ∧ Int.fract (x n) < b
        · rw [if_pos hmem]
          have hmem' := (hshift_iff (x n)).mp hmem
          exact ⟨(htrap_01 _ _ _ _ _).2,
            le_of_eq (htrap_one _ _ _ _ _ (by linarith) (by linarith) hmem'.1 hmem'.2.le).symm⟩
        · rw [if_neg hmem]
          have hnot' : ¬ (a' ≤ Int.fract (x n + shift) ∧ Int.fract (x n + shift) < b') :=
            fun h => hmem ((hshift_iff (x n)).mpr h)
          have hgm0 : gMinus (x n) = 0 := by
            by_cases hle : Int.fract (x n + shift) ≤ a'
            · exact htrap_zero_left _ _ _ _ _ (by linarith) hle
            · have hge : b' ≤ Int.fract (x n + shift) := by
                by_contra hlt; exact hnot' ⟨by linarith, by linarith⟩
              exact htrap_zero_right _ _ _ _ _ (by linarith) hge
          exact ⟨le_of_eq hgm0, (htrap_01 _ _ _ _ _).1⟩
      -- Use convergence of `gPlus` and `gMinus` averages
      have htP := Metric.tendsto_atTop.mp (hreal gPlus hgPlus_cont hgPlus_per) (ε - 2 * η) (by linarith)
      have htM := Metric.tendsto_atTop.mp (hreal gMinus hgMinus_cont hgMinus_per) (ε - 2 * η) (by linarith)
      rcases htP with ⟨N₁, hN₁⟩
      rcases htM with ⟨N₂, hN₂⟩
      refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
      have hN1 : 1 ≤ N := (le_max_right _ 1).trans hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      have havg_eq :
          (((Finset.range N).filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)).card : ℝ) / (N : ℝ) =
            (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
              (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) := by
        rw [Finset.sum_boole, one_div_mul_eq_div]
      rw [havg_eq, Real.dist_eq, abs_lt]
      have hle_plus :
          (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
              (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) ≤
            (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, gPlus (x n) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => (hsand n).2) (by positivity)
      have hge_minus :
          (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, gMinus (x n) ≤
            (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
              (if a ≤ Int.fract (x n) ∧ Int.fract (x n) < b then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => (hsand n).1) (by positivity)
      have h1 := hN₁ N (((le_max_left N₁ N₂).trans (le_max_left _ 1)).trans hN)
      have h2 := hN₂ N (((le_max_right N₁ N₂).trans (le_max_left _ 1)).trans hN)
      rw [Real.dist_eq, abs_lt] at h1 h2
      constructor <;> linarith

/-- **Weyl Criterion Part 3:** `EquidistributedMod1 x` implies continuous 1-periodic
Cesàro averages converge to `∫_0^1 f`. -/
theorem continuous_of_equidistributed (x : ℕ → ℝ) (heq : EquidistributedMod1 x) :
    ∀ f : ℝ → ℂ, Continuous f → Function.Periodic f 1 →
      Filter.Tendsto
        (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n))
        Filter.atTop (nhds (∫ t in (0 : ℝ)..1, f t)) := by
  intro f hf_cont hf_per
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Uniform continuity of `f` on `[0, 1]`
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).uniformContinuousOn_of_continuous hf_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc (ε / 3) (by linarith) with ⟨δ, hδ_pos, hδ⟩
  set M : ℕ := max 1 (⌈1 / δ⌉₊ + 1)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hinvM_lt : 1 / (M : ℝ) < δ := by
    have h1 : 1 / δ ≤ (⌈1 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / δ⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast le_max_right 1 (⌈1 / δ⌉₊ + 1)
    have hlt : 1 / δ < (M : ℝ) := by linarith
    rw [div_lt_iff₀ hMpos]
    have := (div_lt_iff₀ hδ_pos).mp hlt
    linarith
  -- Step function `step y = f (k / M)` where `k = ⌊M * fract y⌋₊ ∈ range M`
  let step : ℝ → ℂ := fun y => f ((⌊(M : ℝ) * Int.fract y⌋₊ : ℝ) / (M : ℝ))
  have hstep_approx : ∀ y : ℝ, ‖f y - step y‖ < ε / 3 := by
    intro y
    have hy_per : f y = f (Int.fract y) := by
      have : y = Int.fract y + (⌊y⌋ : ℝ) := by linarith [Int.fract_add_floor y]
      conv_lhs => rw [this]
      simpa [mul_one] using hf_per.int_mul ⌊y⌋ (Int.fract y)
    rw [hy_per]
    set k := ⌊(M : ℝ) * Int.fract y⌋₊
    have hk_lt : k < M := by
      apply (Nat.floor_lt (mul_nonneg hMpos.le (Int.fract_nonneg y))).mpr
      have := Int.fract_lt_one y
      nlinarith
    have hm1 : Int.fract y ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩
    have hm2 : (k : ℝ) / (M : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hMpos).mpr (by exact_mod_cast hk_lt.le)⟩
    have hdist : dist (Int.fract y) ((k : ℝ) / (M : ℝ)) < δ := by
      rw [Real.dist_eq]
      have hge : (k : ℝ) ≤ (M : ℝ) * Int.fract y := Nat.floor_le (mul_nonneg hMpos.le (Int.fract_nonneg y))
      have hlt : (M : ℝ) * Int.fract y < (k : ℝ) + 1 := Nat.lt_floor_add_one _
      have hsub_nn : 0 ≤ Int.fract y - (k : ℝ) / (M : ℝ) := by
        rw [sub_nonneg, div_le_iff₀ hMpos]; linarith
      have hsub_lt : Int.fract y - (k : ℝ) / (M : ℝ) < 1 / (M : ℝ) := by
        have : (M : ℝ) * (Int.fract y - (k : ℝ) / (M : ℝ)) < 1 := by
          have hdiv : (M : ℝ) * ((k : ℝ) / (M : ℝ)) = (k : ℝ) := mul_div_cancel₀ _ hMpos.ne'
          linarith
        rw [lt_div_iff₀ hMpos]; linarith
      rw [abs_of_nonneg hsub_nn]
      exact hsub_lt.trans hinvM_lt
    simpa [step, k, dist_eq_norm] using hδ (Int.fract y) hm1 ((k : ℝ) / (M : ℝ)) hm2 hdist
  -- Convergence of step-function Cesàro averages to `(1/M) ∑_{k < M} f (k/M)`
  have hstep_tend : Filter.Tendsto
      (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n))
      Filter.atTop (nhds (((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ)))) := by
    have hbin : ∀ k ∈ Finset.range M,
        Filter.Tendsto
          (fun N : ℕ =>
            ((((Finset.range N).filter (fun n =>
              (k : ℝ) / (M : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < ((k + 1 : ℕ) : ℝ) / (M : ℝ))).card : ℝ) /
              (N : ℝ) : ℂ) * f ((k : ℝ) / (M : ℝ)))
          Filter.atTop (nhds (((1 / (M : ℝ) : ℝ) : ℂ) * f ((k : ℝ) / (M : ℝ)))) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have ha : 0 ≤ (k : ℝ) / (M : ℝ) := by positivity
      have hab : (k : ℝ) / (M : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / (M : ℝ) := by
        apply div_le_div_of_nonneg_right _ hMpos.le
        exact_mod_cast Nat.le_succ k
      have hb : ((k + 1 : ℕ) : ℝ) / (M : ℝ) ≤ 1 :=
        (div_le_one hMpos).mpr (by exact_mod_cast hk)
      have heq_k := heq ((k : ℝ) / (M : ℝ)) (((k + 1 : ℕ) : ℝ) / (M : ℝ)) ha hab hb
      have hdiff : ((k + 1 : ℕ) : ℝ) / (M : ℝ) - (k : ℝ) / (M : ℝ) = 1 / (M : ℝ) := by
        push_cast; ring
      rw [hdiff] at heq_k
      simpa [Function.comp_def, Complex.ofReal_div] using
        ((Complex.continuous_ofReal.tendsto _).comp heq_k).mul_const (f ((k : ℝ) / (M : ℝ)))
    have hsum_tend := tendsto_finsetSum (Finset.range M) hbin
    rw [← Finset.mul_sum] at hsum_tend
    refine hsum_tend.congr fun N => ?_
    -- Partition `Finset.range N` by `k = ⌊M * fract (x n)⌋₊ ∈ Finset.range M`
    have hpart :
        ∑ k ∈ Finset.range M,
          ((((Finset.range N).filter (fun n =>
            (k : ℝ) / (M : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < ((k + 1 : ℕ) : ℝ) / (M : ℝ))).card : ℝ) : ℂ) *
            f ((k : ℝ) / (M : ℝ)) =
        ∑ n ∈ Finset.range N, step (x n) := by
      have hfilt_eq : ∀ k ∈ Finset.range M,
          (Finset.range N).filter (fun n =>
            (k : ℝ) / (M : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < ((k + 1 : ℕ) : ℝ) / (M : ℝ)) =
          (Finset.range N).filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k) := by
        intro k _
        ext n
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro _
        rw [Nat.floor_eq_iff (mul_nonneg hMpos.le (Int.fract_nonneg (x n)))]
        rw [div_le_iff₀ hMpos, lt_div_iff₀ hMpos]
        push_cast
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
      rw [Finset.sum_congr rfl (fun k hk => by rw [hfilt_eq k hk])]
      have hinner : ∀ k ∈ Finset.range M,
          ((((Finset.range N).filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k)).card : ℝ) : ℂ) *
            f ((k : ℝ) / (M : ℝ)) =
          ∑ n ∈ (Finset.range N).filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k), step (x n) := by
        intro k _
        symm
        calc ∑ n ∈ (Finset.range N).filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k), step (x n)
            = ∑ _n ∈ (Finset.range N).filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k),
                f ((k : ℝ) / (M : ℝ)) :=
              Finset.sum_congr rfl (fun n hn => by rw [Finset.mem_filter] at hn; simp only [step, hn.2])
          _ = ((((Finset.range N).filter (fun n => ⌊(M : ℝ) * Int.fract (x n)⌋₊ = k)).card : ℝ) : ℂ) *
                f ((k : ℝ) / (M : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul, Complex.ofReal_natCast]
      rw [Finset.sum_congr rfl hinner]
      exact Finset.sum_fiberwise_of_maps_to (fun n _ => by
        rw [Finset.mem_range]
        apply (Nat.floor_lt (mul_nonneg hMpos.le (Int.fract_nonneg (x n)))).mpr
        nlinarith [Int.fract_lt_one (x n)]) _
    calc ∑ k ∈ Finset.range M,
          ((((Finset.range N).filter (fun n =>
            (k : ℝ) / (M : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < ((k + 1 : ℕ) : ℝ) / (M : ℝ))).card : ℝ) /
            (N : ℝ) : ℂ) * f ((k : ℝ) / (M : ℝ))
        = ((1 / (N : ℝ) : ℝ) : ℂ) *
            ∑ k ∈ Finset.range M,
              ((((Finset.range N).filter (fun n =>
                (k : ℝ) / (M : ℝ) ≤ Int.fract (x n) ∧ Int.fract (x n) < ((k + 1 : ℕ) : ℝ) / (M : ℝ))).card : ℝ) : ℂ) *
                f ((k : ℝ) / (M : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [← Complex.ofReal_div, div_eq_mul_inv, ← one_div, Complex.ofReal_mul]
          ring
      _ = ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n) := by rw [hpart]
  -- Bound the Riemann sum approximation `‖(1/M) ∑_{k<M} f(k/M) - ∫_0^1 f‖ ≤ ε / 3`
  have hriemann :
      ‖((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ)) -
        ∫ t in (0 : ℝ)..1, f t‖ ≤ ε / 3 := by
    have hsplit : ∫ t in (0 : ℝ)..1, f t =
        ∑ k ∈ Finset.range M, ∫ t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), f t := by
      have hind : ∀ j : ℕ, ∫ t in (0 : ℝ)..((j : ℝ) / (M : ℝ)), f t =
          ∑ k ∈ Finset.range j, ∫ t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), f t := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          rw [Finset.sum_range_succ, ← ih]
          exact (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            (hf_cont.intervalIntegrable _ _) (hf_cont.intervalIntegrable _ _)).symm
      have hMdiv : (M : ℝ) / (M : ℝ) = 1 := div_self hMpos.ne'
      rw [← hMdiv]
      exact hind M
    have hsum_step :
        ((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ)) =
          ∑ k ∈ Finset.range M, ∫ _t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)),
            f ((k : ℝ) / (M : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [intervalIntegral.integral_const, Complex.real_smul]
      congr 2
      push_cast; ring
    rw [hsplit, hsum_step, ← Finset.sum_sub_distrib]
    calc ‖∑ k ∈ Finset.range M,
            ((∫ _t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), f ((k : ℝ) / (M : ℝ))) -
              ∫ t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), f t)‖
        ≤ ∑ k ∈ Finset.range M,
            ‖(∫ _t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), f ((k : ℝ) / (M : ℝ))) -
              ∫ t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), f t‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range M, ((1 / (M : ℝ)) * (ε / 3)) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_range] at hk
          have hle_ab : (k : ℝ) / (M : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / (M : ℝ) := by
            apply div_le_div_of_nonneg_right _ hMpos.le; exact_mod_cast Nat.le_succ k
          rw [← intervalIntegral.integral_sub intervalIntegrable_const (hf_cont.intervalIntegrable _ _)]
          calc ‖∫ t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)),
                  (f ((k : ℝ) / (M : ℝ)) - f t)‖
              ≤ ∫ t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)),
                  ‖f ((k : ℝ) / (M : ℝ)) - f t‖ :=
                intervalIntegral.norm_integral_le_integral_norm hle_ab
            _ ≤ ∫ _t in ((k : ℝ) / (M : ℝ))..(((k + 1 : ℕ) : ℝ) / (M : ℝ)), (ε / 3) := by
                apply intervalIntegral.integral_mono_on hle_ab
                  ((continuous_const.sub hf_cont).norm.intervalIntegrable _ _) intervalIntegrable_const
                intro t ht
                have hm1 : (k : ℝ) / (M : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
                  ⟨by positivity, (div_le_one hMpos).mpr (by exact_mod_cast hk.le)⟩
                have hm2 : t ∈ Set.Icc (0 : ℝ) 1 :=
                  ⟨le_trans (by positivity) ht.1,
                    le_trans ht.2 ((div_le_one hMpos).mpr (by exact_mod_cast hk))⟩
                have hdist : dist ((k : ℝ) / (M : ℝ)) t < δ := by
                  rw [Real.dist_eq, abs_of_nonpos (by linarith [ht.1])]
                  have hlen : ((k + 1 : ℕ) : ℝ) / (M : ℝ) - (k : ℝ) / (M : ℝ) = 1 / (M : ℝ) := by
                    push_cast; ring
                  linarith [ht.2]
                exact (by simpa [dist_eq_norm] using hδ _ hm1 _ hm2 hdist : ‖f ((k : ℝ) / (M : ℝ)) - f t‖ < ε / 3).le
            _ = (1 / (M : ℝ)) * (ε / 3) := by
                rw [intervalIntegral.integral_const, smul_eq_mul]
                congr 1; push_cast; ring
      _ = ε / 3 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [hMpos.ne']
  -- Combine all three `ε / 3` bounds
  rw [Metric.tendsto_atTop] at hstep_tend
  rcases hstep_tend (ε / 3) (by linarith) with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right N₀ 1).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h1 : ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
      ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n)‖ ≤ ε / 3 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hNpos)]
    calc (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, (f (x n) - step (x n))‖
        ≤ (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, ‖f (x n) - step (x n)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (1 / (N : ℝ)) * ∑ _n ∈ Finset.range N, (ε / 3) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => (hstep_approx (x n)).le) (by positivity)
      _ = ε / 3 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp [hNpos.ne']
  have h2 : ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n) -
      ((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ))‖ < ε / 3 := by
    simpa [dist_eq_norm] using hN₀ N ((le_max_left N₀ 1).trans hN)
  rw [dist_eq_norm]
  calc ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) - ∫ t in (0 : ℝ)..1, f t‖
      = ‖(((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
            ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n)) +
          ((((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n) -
              ((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ))) +
            (((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ)) -
              ∫ t in (0 : ℝ)..1, f t))‖ := by congr 1; ring
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
            ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n)‖ +
          ‖(((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n) -
              ((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ))) +
            (((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ)) -
              ∫ t in (0 : ℝ)..1, f t)‖ := norm_add_le _ _
    _ ≤ ‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, f (x n) -
            ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n)‖ +
          (‖((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, step (x n) -
              ((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ))‖ +
            ‖((1 / (M : ℝ) : ℝ) : ℂ) * ∑ k ∈ Finset.range M, f ((k : ℝ) / (M : ℝ)) -
              ∫ t in (0 : ℝ)..1, f t‖) := add_le_add le_rfl (norm_add_le _ _)
    _ < ε := by linarith

/-- **Weyl's Equidistribution Criterion (Full Equivalence):**
A real sequence `x : ℕ → ℝ` is equidistributed modulo `1` if and only if for every nonzero
integer `h : ℤ`, `(1 / N) ∑_{n < N} exp(2πi h x_n) → 0`. -/
theorem weyl_criterion (x : ℕ → ℝ) :
    EquidistributedMod1 x ↔
      ∀ h : ℤ, h ≠ 0 →
        Filter.Tendsto
          (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ n ∈ Finset.range N, eChar ((h : ℝ) * x n))
          Filter.atTop (nhds 0) := by
  constructor
  · intro heq h hh
    have hcont : Continuous (fun t : ℝ => eChar ((h : ℝ) * t)) := by unfold eChar; fun_prop
    have hper : Function.Periodic (fun t : ℝ => eChar ((h : ℝ) * t)) 1 := fun t => by
      dsimp only
      have : (h : ℝ) * (t + 1) = (h : ℝ) * t + (h : ℤ) := by ring
      rw [this, eChar_add_int]
    have ht := continuous_of_equidistributed x heq (fun t => eChar ((h : ℝ) * t)) hcont hper
    rw [integral_eChar_int, if_neg hh] at ht
    exact ht
  · intro hexp
    exact equidistributed_of_continuous x (weyl_continuous_of_exp x hexp)

/-- **Weyl's Irrational Rotation Equidistribution Theorem:**
For every irrational `α : ℝ`, the sequence `n ↦ n * α` is equidistributed modulo `1`. -/
theorem irrational_rotation_equidistributed (α : ℝ) (hα : Irrational α) :
    EquidistributedMod1 (fun n : ℕ => (n : ℝ) * α) := by
  rw [weyl_criterion]
  intro h hh
  have hne1 : eChar ((h : ℝ) * α) ≠ 1 := by
    intro heq
    have hdist0 : distToInt ((h : ℝ) * α) = 0 := by
      have hle := norm_eChar_sub_one_ge ((h : ℝ) * α)
      rw [heq, sub_self, norm_zero] at hle
      linarith [distToInt_nonneg ((h : ℝ) * α)]
    have hsub0 : (h : ℝ) * α - (round ((h : ℝ) * α) : ℝ) = 0 := abs_eq_zero.mp hdist0
    have hmul : (h : ℝ) * α = (round ((h : ℝ) * α) : ℝ) := sub_eq_zero.mp hsub0
    have hh_ne : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    have hrat : ((round ((h : ℝ) * α) : ℚ) / (h : ℚ) : ℝ) = α := by
      push_cast; rw [← hmul]; field_simp [hh_ne]
    exact hα ⟨(round ((h : ℝ) * α) : ℚ) / (h : ℚ), by simpa using hrat⟩
  have hden_pos : 0 < ‖eChar ((h : ℝ) * α) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set C : ℝ := 2 / ‖eChar ((h : ℝ) * α) - 1‖
  refine ⟨max 1 (⌈C / ε⌉₊ + 1), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left 1 _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hgeom :
      (∑ n ∈ Finset.range N, eChar ((h : ℝ) * ((n : ℝ) * α))) * (eChar ((h : ℝ) * α) - 1) =
        eChar ((N : ℝ) * ((h : ℝ) * α)) - 1 := by
    have hpow : ∀ n : ℕ, eChar ((h : ℝ) * ((n : ℝ) * α)) = (eChar ((h : ℝ) * α)) ^ n := by
      intro n
      rw [← eChar_nat_mul]
      congr 1; ring
    simp_rw [hpow, eChar_nat_mul]
    exact geom_sum_mul (eChar ((h : ℝ) * α)) N
  have hsum_bound : ‖∑ n ∈ Finset.range N, eChar ((h : ℝ) * ((n : ℝ) * α))‖ ≤ C := by
    have hprod : ‖∑ n ∈ Finset.range N, eChar ((h : ℝ) * ((n : ℝ) * α))‖ * ‖eChar ((h : ℝ) * α) - 1‖ ≤ 2 := by
      rw [← norm_mul, hgeom]
      calc ‖eChar ((N : ℝ) * ((h : ℝ) * α)) - 1‖ ≤ ‖eChar ((N : ℝ) * ((h : ℝ) * α))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_eChar, norm_one]; norm_num
    exact (le_div_iff₀ hden_pos).mpr hprod
  rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hNpos)]
  have hN_big : C / ε < (N : ℝ) := by
    have h1 : C / ε ≤ (⌈C / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈C / ε⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast le_trans (le_max_right 1 (⌈C / ε⌉₊ + 1)) hN
    linarith
  have hC_lt : C / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hNpos]
    have := (div_lt_iff₀ hε).mp hN_big
    linarith
  calc (1 / (N : ℝ)) * ‖∑ n ∈ Finset.range N, eChar ((h : ℝ) * ((n : ℝ) * α))‖
      ≤ (1 / (N : ℝ)) * C := mul_le_mul_of_nonneg_left hsum_bound (by positivity)
    _ = C / (N : ℝ) := by ring
    _ < ε := hC_lt

/-- **Kronecker's 1D Density Corollary:**
For every irrational `α` and every non-empty subinterval `[a, b) ⊆ [0, 1]`,
there exists `n : ℕ` with `Int.fract (n * α) ∈ [a, b)`. -/
theorem kronecker_dense_fract (α : ℝ) (hα : Irrational α) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ n : ℕ, a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b := by
  have heq := irrational_rotation_equidistributed α hα a b ha hab.le hb
  rw [Metric.tendsto_atTop] at heq
  rcases heq ((b - a) / 2) (by linarith) with ⟨N₀, hN₀⟩
  set N := max N₀ 1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hclose := hN₀ N (le_max_left N₀ 1)
  rw [Real.dist_eq, abs_lt] at hclose
  have hpos : (0 : ℝ) < (((Finset.range N).filter (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * α) ∧
      Int.fract ((n : ℝ) * α) < b)).card : ℝ) / (N : ℝ) := by linarith
  have hcard_pos : 0 < ((Finset.range N).filter (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * α) ∧
      Int.fract ((n : ℝ) * α) < b)).card := by
    by_contra h0
    have hcz : ((Finset.range N).filter (fun n : ℕ => a ≤ Int.fract ((n : ℝ) * α) ∧
        Int.fract ((n : ℝ) * α) < b)).card = 0 := by omega
    simp [hcz] at hpos
  rcases Finset.card_pos.mp hcard_pos with ⟨n, hn⟩
  exact ⟨n, (Finset.mem_filter.mp hn).2⟩

/-! ## Section 5: Liouville's Irrationality-Measure Theorem -/

/-- Any nonzero integer polynomial vanishing at an irrational real `α` has degree at least `2`. -/
theorem two_le_natDegree_of_irrational_aeval_zero {α : ℝ} (hα : Irrational α)
    {P : Polynomial ℤ} (hP_ne : P ≠ 0) (hP_root : Polynomial.aeval α P = 0) :
    2 ≤ P.natDegree := by
  by_contra hlt
  have hdeg : P.natDegree = 0 ∨ P.natDegree = 1 := by omega
  rcases hdeg with h0 | h1
  · have hP_eq : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hc0 : P.coeff 0 ≠ 0 := by intro hc; apply hP_ne; rw [hP_eq, hc, map_zero]
    rw [hP_eq, Polynomial.aeval_C] at hP_root
    have hR0 : (P.coeff 0 : ℝ) = 0 := by simpa using hP_root
    exact hc0 (by exact_mod_cast hR0)
  · have hP_eq : P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
      ext n
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · rcases eq_or_ne n 1 with rfl | hn1
        · simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
            one_ne_zero, ↓reduceIte, zero_add]
        · have hgt : P.natDegree < n := by omega
          simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
            Polynomial.coeff_eq_zero_of_natDegree_lt hgt, hn0, hn1, ↓reduceIte, add_zero]
    have hc1 : P.coeff 1 ≠ 0 := by
      rw [← h1]; exact Polynomial.leadingCoeff_ne_zero.mpr hP_ne
    rw [hP_eq, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X] at hP_root
    have hc1_ne : ((P.coeff 1 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hc1
    have hrat : ((-(P.coeff 0 : ℚ)) / (P.coeff 1 : ℚ) : ℝ) = α := by
      push_cast
      have hmul : ((P.coeff 1 : ℤ) : ℝ) * α = -((P.coeff 0 : ℤ) : ℝ) := by
        have : ((P.coeff 0 : ℤ) : ℝ) + ((P.coeff 1 : ℤ) : ℝ) * α = 0 := by
          simpa using hP_root
        linarith
      rw [← hmul]; field_simp [hc1_ne]
    exact hα ⟨-(P.coeff 0 : ℚ) / (P.coeff 1 : ℚ), by simpa using hrat⟩

/-- Pure algebraic Lipschitz bound for `x^k - α^k` on `|x - α| ≤ 1`. -/
lemma abs_pow_sub_pow_le {x α : ℝ} (hx : |x - α| ≤ 1) (k : ℕ) :
    |x ^ k - α ^ k| ≤ |x - α| * (k : ℝ) * (|α| + 1) ^ k := by
  have hx_le : |x| ≤ |α| + 1 := by
    calc |x| = |(x - α) + α| := by ring_nf
      _ ≤ |x - α| + |α| := abs_add_le _ _
      _ ≤ 1 + |α| := by linarith
      _ = |α| + 1 := by ring
  have hA1 : 1 ≤ |α| + 1 := by linarith [abs_nonneg α]
  induction k with
  | zero => simp
  | succ k ih =>
    have hdecomp : x ^ (k + 1) - α ^ (k + 1) = (x - α) * x ^ k + α * (x ^ k - α ^ k) := by ring
    rw [hdecomp]
    have hxpow : |x ^ k| ≤ (|α| + 1) ^ k := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg x) hx_le k
    calc |(x - α) * x ^ k + α * (x ^ k - α ^ k)|
        ≤ |(x - α) * x ^ k| + |α * (x ^ k - α ^ k)| := abs_add_le _ _
      _ = |x - α| * |x ^ k| + |α| * |x ^ k - α ^ k| := by rw [abs_mul, abs_mul]
      _ ≤ |x - α| * (|α| + 1) ^ k + (|α| + 1) * (|x - α| * (k : ℝ) * (|α| + 1) ^ k) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hxpow (abs_nonneg _)
          · exact mul_le_mul (by linarith) ih (abs_nonneg _) (by positivity)
      _ ≤ |x - α| * ((|α| + 1) * (|α| + 1) ^ k) + (|α| + 1) * (|x - α| * (k : ℝ) * (|α| + 1) ^ k) := by
          apply add_le_add _ le_rfl
          have h1 : (|α| + 1) ^ k ≤ (|α| + 1) * (|α| + 1) ^ k := by
            have hnn : 0 ≤ (|α| + 1) ^ k := by positivity
            nlinarith
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |x - α| * ((k + 1 : ℕ) : ℝ) * (|α| + 1) ^ (k + 1) := by
          push_cast; rw [pow_succ]; ring

/-- **Liouville's Irrationality-Measure Theorem (Integer Polynomial Form):**
For any irrational real `α` annihilated by a nonzero integer polynomial `P : Polynomial ℤ` of
degree `d = P.natDegree` (automatically `2 ≤ d`), there exists `c > 0` such that
`c / q^d ≤ |α - p / q|` for every `p : ℤ` and `q : ℕ` with `0 < q`. -/
theorem liouville_int_poly {α : ℝ} (hα : Irrational α) {P : Polynomial ℤ}
    (hP_ne : P ≠ 0) (hP_root : Polynomial.aeval α P = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c / (q : ℝ) ^ P.natDegree ≤ |α - (p : ℝ) / (q : ℝ)| := by
  set d := P.natDegree
  set Pr : Polynomial ℝ := P.map (Int.castRingHom ℝ)
  have hPr_ne : Pr ≠ 0 := by
    intro h0
    apply hP_ne
    ext n
    have := congrArg (fun Q => Q.coeff n) h0
    simp only [Pr, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
    exact_mod_cast this
  have hPr_eval : ∀ x : ℝ, Pr.eval x = Polynomial.aeval x P := fun x => by
    simp [Pr, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hPr_root : Pr.eval α = 0 := by rw [hPr_eval, hP_root]
  -- 1. Isolate `α` from all other real roots of `Pr`
  set S : Finset ℝ := Pr.roots.toFinset.erase α
  set δ : ℝ := if h : S.Nonempty then min 1 (S.inf' h (fun r => |α - r|)) else 1
  have hδ_pos : 0 < δ := by
    by_cases hS : S.Nonempty
    · simp only [δ, dif_pos hS]
      apply lt_min (by norm_num)
      rw [Finset.lt_inf'_iff hS]
      intro r hr
      exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm (Finset.mem_erase.mp hr).1))
    · simp only [δ, dif_neg hS]; norm_num
  have hδ_le1 : δ ≤ 1 := by
    by_cases hS : S.Nonempty
    · simp only [δ, dif_pos hS]; exact min_le_left _ _
    · simp only [δ, dif_neg hS]; norm_num
  have hno_root : ∀ x : ℝ, x ≠ α → |α - x| < δ → Pr.eval x ≠ 0 := by
    intro x hne hlt hzero
    have hx_mem : x ∈ S := by
      rw [Finset.mem_erase, Multiset.mem_toFinset, Polynomial.mem_roots hPr_ne]
      exact ⟨hne, hzero⟩
    have hS : S.Nonempty := ⟨x, hx_mem⟩
    have hle : δ ≤ |α - x| := by
      simp only [δ, dif_pos hS]
      exact (min_le_right _ _).trans (Finset.inf'_le (fun r => |α - r|) hx_mem)
    linarith
  -- 2. Algebraic Lipschitz constant `M ≥ 0` on `|x - α| ≤ 1`
  set M : ℝ := ∑ k ∈ Finset.range (d + 1), |(P.coeff k : ℝ)| * (k : ℝ) * (|α| + 1) ^ k
  have hM_nn : 0 ≤ M := Finset.sum_nonneg fun k _ => by positivity
  have hlip : ∀ x : ℝ, |x - α| ≤ 1 → |Pr.eval x - Pr.eval α| ≤ M * |x - α| := by
    intro x hx
    have hdeg_le : Pr.natDegree ≤ d := Polynomial.natDegree_map_le
    have heval_sum : ∀ y : ℝ, Pr.eval y = ∑ k ∈ Finset.range (d + 1), (P.coeff k : ℝ) * y ^ k := by
      intro y
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_le)]
      apply Finset.sum_congr rfl
      intro k _
      simp [Pr]
    rw [heval_sum x, heval_sum α, ← Finset.sum_sub_distrib]
    calc |∑ k ∈ Finset.range (d + 1), ((P.coeff k : ℝ) * x ^ k - (P.coeff k : ℝ) * α ^ k)|
        ≤ ∑ k ∈ Finset.range (d + 1), |(P.coeff k : ℝ) * x ^ k - (P.coeff k : ℝ) * α ^ k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (d + 1), |(P.coeff k : ℝ)| * (k : ℝ) * (|α| + 1) ^ k * |x - α| := by
          apply Finset.sum_le_sum
          intro k _
          have hfac : (P.coeff k : ℝ) * x ^ k - (P.coeff k : ℝ) * α ^ k =
              (P.coeff k : ℝ) * (x ^ k - α ^ k) := by ring
          rw [hfac, abs_mul]
          calc |(P.coeff k : ℝ)| * |x ^ k - α ^ k|
              ≤ |(P.coeff k : ℝ)| * (|x - α| * (k : ℝ) * (|α| + 1) ^ k) :=
                mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le hx k) (abs_nonneg _)
            _ = |(P.coeff k : ℝ)| * (k : ℝ) * (|α| + 1) ^ k * |x - α| := by ring
      _ = M * |x - α| := (Finset.sum_mul _ _ _).symm
  -- 3. Combine with denominator clearing using `c = min δ (1 / (M + 1))`
  set c : ℝ := min δ (1 / (M + 1))
  have hc_pos : 0 < c := lt_min hδ_pos (one_div_pos.mpr (by linarith))
  refine ⟨c, hc_pos, fun p q hq => ?_⟩
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqd_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ d := one_le_pow₀ hq_ge1
  set x : ℝ := (p : ℝ) / (q : ℝ)
  by_cases hfar : δ ≤ |α - x|
  · calc c / (q : ℝ) ^ d ≤ c / 1 := div_le_div_of_nonneg_left hc_pos.le (by norm_num) hqd_ge1
      _ = c := div_one c
      _ ≤ δ := min_le_left _ _
      _ ≤ |α - x| := hfar
  · have hnear : |α - x| < δ := lt_of_not_ge hfar
    have hx_ne : x ≠ α := by
      intro heq
      exact hα ⟨(p : ℚ) / (q : ℚ), by push_cast; exact heq⟩
    have hPx_ne : Pr.eval x ≠ 0 := hno_root x hx_ne hnear
    -- Clear denominator `q^d`: `q^d * Pr.eval (p / q)` is a nonzero integer
    let intVal : ℤ := ∑ k ∈ Finset.range (d + 1), P.coeff k * p ^ k * (q : ℤ) ^ (d - k)
    have hint_eq : ((q : ℝ) ^ d) * Pr.eval x = (intVal : ℝ) := by
      have hdeg_le : Pr.natDegree ≤ d := Polynomial.natDegree_map_le
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_le), Finset.mul_sum]
      simp only [intVal, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [Pr, Polynomial.coeff_map, eq_intCast, x, div_pow]
      have hpow_split : (q : ℝ) ^ d = (q : ℝ) ^ k * (q : ℝ) ^ (d - k) := by
        rw [← pow_add, add_tsub_cancel_of_le (Nat.lt_succ_iff.mp hk)]
      rw [hpow_split]
      field_simp [hq_pos.ne']
    have hint_ne : intVal ≠ 0 := by
      intro h0
      have hmul0 : (q : ℝ) ^ d * Pr.eval x = 0 := by rw [hint_eq, h0, Int.cast_zero]
      rcases mul_eq_zero.mp hmul0 with hqd0 | hpx0
      · exact (pow_pos hq_pos d).ne' hqd0
      · exact hPx_ne hpx0
    have hint_ge1 : (1 : ℝ) ≤ |(intVal : ℝ)| := by
      have : (1 : ℤ) ≤ |intVal| := Int.one_le_abs hint_ne
      exact_mod_cast this
    have hlower : 1 / (q : ℝ) ^ d ≤ |Pr.eval x| := by
      rw [div_le_iff₀ (pow_pos hq_pos d)]
      calc (1 : ℝ) ≤ |(intVal : ℝ)| := hint_ge1
        _ = |(q : ℝ) ^ d * Pr.eval x| := by rw [hint_eq]
        _ = |Pr.eval x| * (q : ℝ) ^ d := by
            rw [abs_mul, abs_of_pos (pow_pos hq_pos d), mul_comm]
    have hlip_x : |Pr.eval x| ≤ (M + 1) * |α - x| := by
      have hx1 : |x - α| ≤ 1 := by rw [abs_sub_comm]; linarith
      have hl := hlip x hx1
      rw [hPr_root, sub_zero, abs_sub_comm] at hl
      nlinarith [abs_nonneg (α - x)]
    calc c / (q : ℝ) ^ d
        ≤ (1 / (M + 1)) / (q : ℝ) ^ d :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (1 / (q : ℝ) ^ d) / (M + 1) := by ring
      _ ≤ |Pr.eval x| / (M + 1) := div_le_div_of_nonneg_right hlower (by positivity)
      _ ≤ ((M + 1) * |α - x|) / (M + 1) := div_le_div_of_nonneg_right hlip_x (by positivity)
      _ = |α - x| := mul_div_cancel_left₀ _ (by linarith)

/-- **Liouville's Irrationality-Measure Theorem (Algebraic Irrational / Minimal Polynomial Form):**
For every real algebraic irrational `α` (`IsAlgebraic ℚ α` and `Irrational α`), its minimal
polynomial over `ℚ` has degree `d = (minpoly ℚ α).natDegree ≥ 2`, and there exists `c > 0`
such that `c / q^d ≤ |α - p / q|` for all `p : ℤ` and `q : ℕ` with `0 < q`. -/
theorem liouville_algebraic_irrational {α : ℝ} (halg : IsAlgebraic ℚ α) (hα : Irrational α) :
    2 ≤ (minpoly ℚ α).natDegree ∧
      ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
        c / (q : ℝ) ^ (minpoly ℚ α).natDegree ≤ |α - (p : ℝ) / (q : ℝ)| := by
  have hint : IsIntegral ℚ α := halg.isIntegral
  set Q : Polynomial ℚ := minpoly ℚ α
  have hQ_ne : Q ≠ 0 := minpoly.ne_zero hint
  have hQ_root : Polynomial.aeval α Q = 0 := minpoly.aeval ℚ α
  -- Clear denominators of `Q : Polynomial ℚ` to obtain `P : Polynomial ℤ`
  set D : ℕ := ∏ i ∈ Finset.range (Q.natDegree + 1), (Q.coeff i).den
  have hD_pos : 0 < D := Finset.prod_pos fun i _ => (Q.coeff i).pos
  have hD_ne : (D : ℚ) ≠ 0 := by exact_mod_cast hD_pos.ne'
  let P : Polynomial ℤ := ∑ i ∈ Finset.range (Q.natDegree + 1),
    Polynomial.C ((Q.coeff i).num * ((D / (Q.coeff i).den : ℕ) : ℤ)) * Polynomial.X ^ i
  have hP_map : P.map (Int.castRingHom ℚ) = Polynomial.C (D : ℚ) * Q := by
    have hcoeff : ∀ i ∈ Finset.range (Q.natDegree + 1),
        (((Q.coeff i).num * ((D / (Q.coeff i).den : ℕ) : ℤ) : ℤ) : ℚ) = (D : ℚ) * Q.coeff i := by
      intro i hi
      have hdvd : (Q.coeff i).den ∣ D := Finset.dvd_prod_of_mem _ hi
      have hden_ne : ((Q.coeff i).den : ℚ) ≠ 0 := by exact_mod_cast (Q.coeff i).pos.ne'
      have hD_eq : (D : ℚ) = ((Q.coeff i).den : ℚ) * ((D / (Q.coeff i).den : ℕ) : ℚ) := by
        exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
      rw [Int.cast_mul, Int.cast_natCast, hD_eq]
      have hrat := Rat.mul_den_eq_num (Q.coeff i)
      have hratQ : (Q.coeff i) * ((Q.coeff i).den : ℚ) = ((Q.coeff i).num : ℚ) := by
        exact_mod_cast hrat
      linear_combination -(((D / (Q.coeff i).den : ℕ) : ℚ)) * hratQ
    rw [Polynomial.map_sum]
    conv_rhs => rw [Polynomial.as_sum_range' Q (Q.natDegree + 1) (Nat.lt_succ_self _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, eq_intCast,
      hcoeff i hi, ← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, ← map_mul]
  have hP_ne : P ≠ 0 := by
    intro h0
    have hmul0 : Polynomial.C (D : ℚ) * Q = 0 := by rw [← hP_map, h0, Polynomial.map_zero]
    rcases mul_eq_zero.mp hmul0 with hC0 | hQ0
    · exact hD_ne (Polynomial.C_eq_zero.mp hC0)
    · exact hQ_ne hQ0
  have hP_deg : P.natDegree = Q.natDegree := by
    have h1 : (P.map (Int.castRingHom ℚ)).natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
    rw [← h1, hP_map, Polynomial.natDegree_C_mul hD_ne]
  have hP_root : Polynomial.aeval α P = 0 := by
    have hcomp : Polynomial.aeval α P = Polynomial.aeval α (P.map (Int.castRingHom ℚ)) := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, Polynomial.aeval_map_algebraMap]
    rw [hcomp, hP_map, map_mul, hQ_root, mul_zero]
  have hdeg2 : 2 ≤ Q.natDegree :=
    hP_deg ▸ two_le_natDegree_of_irrational_aeval_zero hα hP_ne hP_root
  refine ⟨hdeg2, ?_⟩
  simpa only [hP_deg] using liouville_int_poly hα hP_ne hP_root

/-- **Liouville's Transcendence Criterion:**
If an irrational real `α` admits rational approximations `|α - p / q| < c / q^n` for every
`n ≥ 1` and `c > 0`, then `α` is transcendental over `ℚ`. -/
theorem transcendental_of_liouville_approx {α : ℝ} (hα : Irrational α)
    (happrox : ∀ (n : ℕ), 1 ≤ n → ∀ c : ℝ, 0 < c →
      ∃ (p : ℤ) (q : ℕ), 0 < q ∧ |α - (p : ℝ) / (q : ℝ)| < c / (q : ℝ) ^ n) :
    Transcendental ℚ α := by
  intro halg
  rcases liouville_algebraic_irrational halg hα with ⟨hdeg, c, hc_pos, hbound⟩
  rcases happrox (minpoly ℚ α).natDegree (by omega) c hc_pos with ⟨p, q, hq, hlt⟩
  exact not_lt_of_ge (hbound p q hq) hlt

end
end Arith4Ext.LargeSieveDiophantine
