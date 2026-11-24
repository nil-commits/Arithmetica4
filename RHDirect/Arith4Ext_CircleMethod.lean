/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import RHDirect.Arith4Ext_SieveCharacters

set_option linter.unusedSectionVars false

/-!
# Arith4Ext.CircleMethod — Circle Method, Ramanujan Sums, Weyl/Hua/Bilinear Bounds, & Mann's Theorem

Reusable, 100%-unconditional (`0` assumptions, `0` proxies, `0` `sorry`, `0` custom axioms)
Tier A additive & analytic number theory library on targeted Mathlib imports + audited Tier A
`RHDirect.Arith4Ext_SieveCharacters` (`namespace Arith4Ext.CircleMethod`):

1. **Circle Method Orthogonality & Major/Minor Arc Decomposition**: Exact integral extraction of
   `k`-fold additive representation counts, Parseval `L^2` identity, measurable major/minor arc
   splitting, and the `L^∞`–`L^2` minor-arc bound.
2. **Ramanujan Sums `c_q(n)` & Ternary Singular Series**: Möbius-inversion formula, exact
   multiplicativity, Hölder's closed form `c_q(n) = μ(q / gcd(q, n)) φ(q) / φ(q / gcd(q, n))`,
   orthogonality, absolute summability, Euler-product factorization, and explicit lower bound
   `𝔖₃(n) ≥ 1` for every odd `n`.
3. **Weyl Quadratic Sum, Hua's `L^4` Bound & Bilinear Type I–II Minor-Arc Bounds**: General
   Vinogradov reciprocal-distance sum bound, explicit `k = 2` Weyl quadratic exponential-sum
   bound, Hua's `L^4` bound `∫₀¹ |∑_{n ≤ N} e(α n^2)|^4 dα ≤ 9 N^2 (log N + 1)`, and general
   Cauchy–Schwarz bilinear Type II & dyadic Type I minor-arc bounds (pairing directly with
   `Arith4Ext.SieveCharacters.vaughan_bilinear_sum`).
4. **Schnirelmann Density, Schnirelmann's Theorem & Mann's 1942 Sharp Theorem**: Dyson `e`-transform
   proof of Mann's sharp theorem `min(1, σ(A) + σ(B)) ≤ σ(A + B)`, Schnirelmann's `α + β - α β`
   inequality, `σ(A) + σ(B) ≥ 1 ⇒ A + B = ℕ`, and Schnirelmann's finite-order additive basis
   theorem `∀ n, n ∈ h A` with `h = ⌈1 / σ(A)⌉`.
-/

open Real Complex Finset MeasureTheory intervalIntegral
open scoped BigOperators

namespace Arith4Ext.CircleMethod

noncomputable section

/-! ## Section 1: Circle Method Orthogonality & Major/Minor Arc Decomposition -/

/-- The standard circle-method additive character `e(x) = exp(2πi x)`. -/
def e (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

lemma e_zero : e 0 = 1 := by
  simp [e]

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma e_sub (x y : ℝ) : e (x - y) = e x * e (-y) := by
  rw [sub_eq_add_neg, e_add]

lemma e_neg (x : ℝ) : e (-x) = star (e x) := by
  unfold e
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have h0 : 2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ) +
        2 * Real.pi * Complex.I * (x : ℂ) = 0 := by push_cast; ring
    rw [h0, Complex.exp_zero]
  have hnorm : ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
    have harg : 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have h2 : star (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) *
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 := by
    change starRingEnd ℂ _ * _ = 1
    rw [mul_comm, Complex.mul_conj', hnorm]
    simp
  have hne : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have harg : 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

lemma e_int (m : ℤ) : e (m : ℝ) = 1 := by
  unfold e
  have harg : 2 * Real.pi * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

lemma e_nat (n : ℕ) : e (n : ℝ) = 1 := by
  simpa using e_int (n : ℤ)

lemma e_add_int (x : ℝ) (m : ℤ) : e (x + (m : ℝ)) = e x := by
  rw [e_add, e_int, mul_one]

lemma e_pow_nat (x : ℝ) (n : ℕ) : (e x) ^ n = e ((n : ℝ) * x) := by
  induction n with
  | zero => simp [e_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← e_add]
    congr 1
    push_cast
    ring

lemma continuous_e_mul (c : ℝ) : Continuous (fun α : ℝ => e (c * α)) := by
  unfold e
  refine Complex.continuous_exp.comp ?_
  have hfun : (fun α : ℝ => 2 * Real.pi * Complex.I * ((c * α : ℝ) : ℂ)) =
      fun α : ℝ => (2 * Real.pi * Complex.I * (c : ℂ)) * (α : ℂ) := by
    ext α; push_cast; ring
  rw [hfun]
  exact continuous_const.mul Complex.continuous_ofReal

/-- Exact orthogonality of `e(m α)` on `[0, 1]`:
`∫₀¹ e(m α) dα = 1` if `m = 0` and `0` if `m ≠ 0`. -/
theorem integral_e_int (m : ℤ) :
    (∫ α in (0 : ℝ)..1, e ((m : ℝ) * α)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [e_zero]
  · simp only [hm, ↓reduceIte]
    set c : ℂ := 2 * Real.pi * Complex.I * (m : ℂ)
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      have h1 : (2 : ℂ) ≠ 0 := by norm_num
      have h2 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have h3 : Complex.I ≠ 0 := Complex.I_ne_zero
      have h4 : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
    set F : ℝ → ℂ := fun α => e ((m : ℝ) * α) / c
    have hderiv : ∀ α ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (e ((m : ℝ) * α)) α := by
      intro α _
      have hlin : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c α := by
        have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 α := Complex.ofRealCLM.hasDerivAt
        simpa [mul_one] using h1.const_mul c
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)))
          (Complex.exp (c * (α : ℂ)) * c) α :=
        (Complex.hasDerivAt_exp (c * (α : ℂ))).comp α hlin
      have hdiv : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
          ((Complex.exp (c * (α : ℂ)) * c) / c) α := hexp.div_const c
      have hF_eq : F = fun t : ℝ => Complex.exp (c * (t : ℂ)) / c := by
        ext t
        dsimp [F, e, c]
        congr 2
        push_cast
        ring
      have hval_eq : (Complex.exp (c * (α : ℂ)) * c) / c = e ((m : ℝ) * α) := by
        rw [mul_div_cancel_right₀ _ hc_ne]
        dsimp [e, c]
        congr 1
        push_cast
        ring
      rw [hF_eq, ← hval_eq]
      exact hdiv
    have hint : IntervalIntegrable (fun α : ℝ => e ((m : ℝ) * α)) volume 0 1 :=
      (continuous_e_mul (m : ℝ)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp [F]
    rw [mul_one, mul_zero, e_int m, e_zero, sub_self]

/-- Exponential sum `S(α) = ∑_{n ∈ A} w(n) e(n α)`. -/
def expSum (A : Finset ℕ) (w : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ A, w n * e ((n : ℝ) * α)

lemma continuous_expSum (A : Finset ℕ) (w : ℕ → ℂ) : Continuous (expSum A w) := by
  unfold expSum
  exact continuous_finsetSum A fun n _ => continuous_const.mul (continuous_e_mul (n : ℝ))

/-- Weighted `k`-fold additive representation count
`R_k(n) = ∑_{x ∈ A^k, ∑_i x_i = n} ∏_i w(x_i)`. -/
def repCount (A : Finset ℕ) (w : ℕ → ℂ) (k n : ℕ) : ℂ :=
  ∑ x ∈ (Fintype.piFinset (fun _ : Fin k => A)).filter (fun x => ∑ i, x i = n),
    ∏ i : Fin k, w (x i)

lemma expSum_pow_eq (A : Finset ℕ) (w : ℕ → ℂ) (k : ℕ) (α : ℝ) :
    (expSum A w α) ^ k =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin k => A),
        (∏ i : Fin k, w (x i)) * e (((∑ i : Fin k, x i : ℕ) : ℝ) * α) := by
  unfold expSum
  have hpow : (∑ n ∈ A, w n * e ((n : ℝ) * α)) ^ k =
      ∏ _i : Fin k, ∑ n ∈ A, w n * e ((n : ℝ) * α) := by
    simp
  rw [hpow, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  have hprod_e : ∀ S : Finset (Fin k),
      ∏ i ∈ S, e ((x i : ℝ) * α) = e (((∑ i ∈ S, x i : ℕ) : ℝ) * α) := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => simp [e_zero]
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← e_add]
      congr 1
      push_cast
      ring
  exact hprod_e Finset.univ

/-- **Circle Method Exact Integral Extraction** of `k`-fold weighted representation counts:
`R_k(n) = ∫₀¹ S(α)^k e(-n α) dα`. -/
theorem circle_method_repCount_eq_integral (A : Finset ℕ) (w : ℕ → ℂ) (k n : ℕ) :
    repCount A w k n =
      ∫ α in (0 : ℝ)..1, (expSum A w α) ^ k * e (-((n : ℝ) * α)) := by
  have hexp : ∀ α : ℝ, (expSum A w α) ^ k * e (-((n : ℝ) * α)) =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin k => A),
        (∏ i : Fin k, w (x i)) * e (((((∑ i : Fin k, x i : ℕ) : ℤ) - (n : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    rw [expSum_pow_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, ← e_add]
    congr 1
    push_cast
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · unfold repCount
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_e_int]
    have hiff : ((∑ i : Fin k, x i : ℕ) : ℤ) - (n : ℤ) = 0 ↔ ∑ i : Fin k, x i = n := by
      constructor
      · intro h
        have h1 : ((∑ i : Fin k, x i : ℕ) : ℤ) = (n : ℤ) := sub_eq_zero.mp h
        exact Int.ofNat.inj h1
      · intro h; rw [h, sub_self]
    by_cases heq : ∑ i : Fin k, x i = n
    · rw [heq, sub_self]; simp
    · have hne : ((∑ i : Fin k, x i : ℕ) : ℤ) - (n : ℤ) ≠ 0 := fun h => heq (hiff.mp h)
      simp only [heq, hne, ↓reduceIte, mul_zero]
  · intro x _
    exact (continuous_const.mul (continuous_e_mul _)).intervalIntegrable 0 1

/-- Unweighted `k`-fold representation count extraction corollary:
`#{(x₁, ..., x_k) ∈ A^k : x₁ + ... + x_k = n} = ∫₀¹ (∑_{a ∈ A} e(a α))^k e(-n α) dα`. -/
theorem unweighted_repCount_eq_integral (A : Finset ℕ) (k n : ℕ) :
    (((Fintype.piFinset (fun _ : Fin k => A)).filter (fun x => ∑ i, x i = n)).card : ℂ) =
      ∫ α in (0 : ℝ)..1, (expSum A (fun _ => 1) α) ^ k * e (-((n : ℝ) * α)) := by
  have h := circle_method_repCount_eq_integral A (fun _ => 1) k n
  unfold repCount at h
  simpa using h

/-- **Exact Parseval `L^2` Identity** for exponential sums:
`∫₀¹ ‖∑_{n ∈ A} w(n) e(n α)‖^2 dα = ∑_{n ∈ A} ‖w(n)‖^2`. -/
theorem parseval_expSum (A : Finset ℕ) (w : ℕ → ℂ) :
    (∫ α in (0 : ℝ)..1, ‖expSum A w α‖ ^ 2) = ∑ n ∈ A, ‖w n‖ ^ 2 := by
  have hC : (∫ α in (0 : ℝ)..1, ((‖expSum A w α‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ A, ((‖w n‖ ^ 2 : ℝ) : ℂ) := by
    have hpt : ∀ α : ℝ, ((‖expSum A w α‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ A, ∑ n ∈ A, w m * star (w n) * e ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * α) := by
      intro α
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      unfold expSum
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul]
      change w m * e ((m : ℝ) * α) * (star (w n) * star (e ((n : ℝ) * α))) =
        w m * star (w n) * e ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * α)
      rw [← e_neg]
      have hmul : e ((m : ℝ) * α) * e (-((n : ℝ) * α)) =
          e ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * α) := by
        rw [← e_add]
        congr 1
        push_cast
        ring
      calc w m * e ((m : ℝ) * α) * (star (w n) * e (-((n : ℝ) * α)))
          = w m * star (w n) * (e ((m : ℝ) * α) * e (-((n : ℝ) * α))) := by ring
        _ = w m * star (w n) * e ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * α) := by rw [hmul]
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [intervalIntegral.integral_finsetSum]
      · have hinner : ∀ n ∈ A,
            (∫ α in (0 : ℝ)..1, w m * star (w n) * e ((((m : ℤ) - (n : ℤ) : ℤ) : ℝ) * α)) =
              if n = m then ((‖w m‖ ^ 2 : ℝ) : ℂ) else 0 := by
          intro n _
          rw [intervalIntegral.integral_const_mul, integral_e_int]
          by_cases hnm : n = m
          · subst hnm
            simp only [sub_self, ↓reduceIte, mul_one]
            push_cast
            exact Complex.mul_conj' (w n)
          · have hne : (m : ℤ) - (n : ℤ) ≠ 0 := by omega
            simp [hnm, hne]
        rw [Finset.sum_congr rfl hinner]
        simp [hm]
      · intro n _
        exact (continuous_const.mul (continuous_e_mul _)).intervalIntegrable 0 1
    · intro m _
      exact (continuous_finsetSum A fun n _ =>
        continuous_const.mul (continuous_e_mul _)).intervalIntegrable 0 1
  have hre := congr_arg Complex.re hC
  have hL : (∫ α in (0 : ℝ)..1, ((‖expSum A w α‖ ^ 2 : ℝ) : ℂ)).re =
      ∫ α in (0 : ℝ)..1, ‖expSum A w α‖ ^ 2 := by
    rw [← Complex.reCLM_apply]
    have hint : IntervalIntegrable (fun α : ℝ => ((‖expSum A w α‖ ^ 2 : ℝ) : ℂ)) volume 0 1 :=
      (Complex.continuous_ofReal.comp ((continuous_expSum A w).norm.pow 2)).intervalIntegrable 0 1
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint]
    rfl
  rw [hL, ← Complex.ofReal_sum, Complex.ofReal_re] at hre
  exact hre

/-- **Circle Method Major/Minor Arc Decomposition**:
For any measurable major-arc set `M : Set ℝ`,
`R_k(n) = ∫_{Ioc 0 1 ∩ M} S(α)^k e(-n α) dα + ∫_{Ioc 0 1 \ M} S(α)^k e(-n α) dα`. -/
theorem circle_method_major_minor_split (A : Finset ℕ) (w : ℕ → ℂ) (k n : ℕ)
    {M : Set ℝ} (hM : MeasurableSet M) :
    repCount A w k n =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, (expSum A w α) ^ k * e (-((n : ℝ) * α))) +
      (∫ α in Set.Ioc (0 : ℝ) 1 \ M, (expSum A w α) ^ k * e (-((n : ℝ) * α))) := by
  rw [circle_method_repCount_eq_integral, intervalIntegral.integral_of_le zero_le_one]
  set f : ℝ → ℂ := fun α => (expSum A w α) ^ k * e (-((n : ℝ) * α))
  have hf_cont : Continuous f :=
    ((continuous_expSum A w).pow k).mul (by
      have h : (fun α : ℝ => e (-((n : ℝ) * α))) = fun α : ℝ => e ((-(n : ℝ)) * α) := by
        ext α; congr 1; ring
      rw [h]
      exact continuous_e_mul (-(n : ℝ)))
  have hf_int : IntegrableOn f (Set.Ioc (0 : ℝ) 1) volume :=
    (hf_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hunion : Set.Ioc (0 : ℝ) 1 = (Set.Ioc (0 : ℝ) 1 ∩ M) ∪ (Set.Ioc (0 : ℝ) 1 \ M) :=
    (Set.inter_union_sdiff (Set.Ioc (0 : ℝ) 1) M).symm
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1 ∩ M) (Set.Ioc (0 : ℝ) 1 \ M) :=
    Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2
  conv_lhs => rw [hunion]
  exact MeasureTheory.setIntegral_union hdisj (measurableSet_Ioc.diff hM)
    (hf_int.mono_set Set.inter_subset_left) (hf_int.mono_set Set.sdiff_subset)

/-- **`L^∞`–`L^2` Minor-Arc Bound**:
For `k ≥ 2` and any measurable minor-arc set `E ⊆ (0, 1]` on which `‖S(α)‖ ≤ B`,
`‖∫_E S(α)^k e(-n α) dα‖ ≤ B^(k - 2) * ∫₀¹ ‖S(α)‖^2 dα`. -/
theorem minor_arc_Linfty_L2_bound (A : Finset ℕ) (w : ℕ → ℂ) {k : ℕ} (hk : 2 ≤ k) (n : ℕ)
    {E : Set ℝ} (hE : MeasurableSet E) (hE_sub : E ⊆ Set.Ioc (0 : ℝ) 1)
    {B : ℝ} (hB : 0 ≤ B) (hsup : ∀ α ∈ E, ‖expSum A w α‖ ≤ B) :
    ‖∫ α in E, (expSum A w α) ^ k * e (-((n : ℝ) * α))‖ ≤
      B ^ (k - 2) * ∫ α in (0 : ℝ)..1, ‖expSum A w α‖ ^ 2 := by
  have hcont_sq : Continuous (fun α : ℝ => ‖expSum A w α‖ ^ 2) :=
    (continuous_expSum A w).norm.pow 2
  have hint_Ioc : IntegrableOn (fun α : ℝ => ‖expSum A w α‖ ^ 2) (Set.Ioc (0 : ℝ) 1) volume :=
    hcont_sq.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hcont_norm : Continuous (fun α : ℝ => ‖(expSum A w α) ^ k * e (-((n : ℝ) * α))‖) := by
    refine (((continuous_expSum A w).pow k).mul ?_).norm
    have h : (fun α : ℝ => e (-((n : ℝ) * α))) = fun α : ℝ => e ((-(n : ℝ)) * α) := by
      ext α; congr 1; ring
    rw [h]
    exact continuous_e_mul (-(n : ℝ))
  have hint_E_norm : IntegrableOn (fun α : ℝ => ‖(expSum A w α) ^ k * e (-((n : ℝ) * α))‖) E volume :=
    (hcont_norm.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).mono_set hE_sub
  have hint_E_rhs : IntegrableOn (fun α : ℝ => B ^ (k - 2) * ‖expSum A w α‖ ^ 2) E volume :=
    (hint_Ioc.mono_set hE_sub).const_mul (B ^ (k - 2))
  calc ‖∫ α in E, (expSum A w α) ^ k * e (-((n : ℝ) * α))‖
      ≤ ∫ α in E, ‖(expSum A w α) ^ k * e (-((n : ℝ) * α))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ α in E, B ^ (k - 2) * ‖expSum A w α‖ ^ 2 := by
        refine MeasureTheory.setIntegral_mono_on hint_E_norm hint_E_rhs hE fun α hα => ?_
        rw [norm_mul, norm_pow, norm_e, mul_one]
        have hk_eq : k = (k - 2) + 2 := by omega
        conv_lhs => rw [hk_eq, pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hsup α hα) (k - 2))
          (sq_nonneg _)
    _ = B ^ (k - 2) * ∫ α in E, ‖expSum A w α‖ ^ 2 := MeasureTheory.integral_const_mul _ _
    _ ≤ B ^ (k - 2) * ∫ α in Set.Ioc (0 : ℝ) 1, ‖expSum A w α‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hB _)
        exact MeasureTheory.setIntegral_mono_set hint_Ioc
          (Filter.Eventually.of_forall fun α => sq_nonneg _)
          (Filter.Eventually.of_forall hE_sub)
    _ = B ^ (k - 2) * ∫ α in (0 : ℝ)..1, ‖expSum A w α‖ ^ 2 := by
        rw [intervalIntegral.integral_of_le zero_le_one]

/-- Minor-arc `L^∞`–`L^2` bound evaluated via Parseval:
`‖∫_E S(α)^k e(-n α) dα‖ ≤ B^(k - 2) * ∑_{m ∈ A} ‖w(m)‖^2`. -/
theorem minor_arc_Linfty_L2_bound_parseval (A : Finset ℕ) (w : ℕ → ℂ) {k : ℕ} (hk : 2 ≤ k) (n : ℕ)
    {E : Set ℝ} (hE : MeasurableSet E) (hE_sub : E ⊆ Set.Ioc (0 : ℝ) 1)
    {B : ℝ} (hB : 0 ≤ B) (hsup : ∀ α ∈ E, ‖expSum A w α‖ ≤ B) :
    ‖∫ α in E, (expSum A w α) ^ k * e (-((n : ℝ) * α))‖ ≤
      B ^ (k - 2) * ∑ m ∈ A, ‖w m‖ ^ 2 := by
  rw [← parseval_expSum A w]
  exact minor_arc_Linfty_L2_bound A w hk n hE hE_sub hB hsup

/-! ## Section 2: Ramanujan Sums `c_q(n)` & Ternary Singular Series -/

/-- The Ramanujan sum `c_q(n) = ∑_{1 ≤ a ≤ q, gcd(a, q) = 1} e(a n / q)`. -/
def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
    e ((a : ℝ) * (n : ℝ) / (q : ℝ))

lemma ramanujanSum_one (n : ℕ) : ramanujanSum 1 n = 1 := by
  unfold ramanujanSum
  have hf : (Finset.Icc 1 1).filter (fun a => Nat.Coprime a 1) = {1} := by
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro ⟨⟨h1, h2⟩, _⟩; omega
    · rintro rfl; simp
  rw [hf, Finset.sum_singleton]
  simp [e_nat]

lemma sum_e_div_eq_ite {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ∑ a ∈ Finset.Icc 1 q, e ((a : ℝ) * (n : ℝ) / (q : ℝ)) =
      if q ∣ n then (q : ℂ) else 0 := by
  have : NeZero q := ⟨by omega⟩
  have hcast : ∑ a ∈ Finset.Icc 1 q, e ((a : ℝ) * (n : ℝ) / (q : ℝ)) =
      ∑ x : ZMod q, Arith4Ext.SieveCharacters.zmodAddChar q (x * (n : ZMod q)) := by
    refine Finset.sum_bij (fun a _ => (a : ZMod q)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ h1 a₂ h2 heq
      simp only [Finset.mem_Icc] at h1 h2
      have hmod : a₁ % q = a₂ % q := by
        have := congr_arg ZMod.val heq
        rwa [ZMod.val_natCast, ZMod.val_natCast] at this
      by_cases h1q : a₁ = q
      · rw [h1q, Nat.mod_self] at hmod
        by_cases h2q : a₂ = q
        · omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hmod
          omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hmod
        by_cases h2q : a₂ = q
        · rw [h2q, Nat.mod_self] at hmod; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hmod; exact hmod
    · intro x _
      by_cases hx0 : x = 0
      · subst hx0
        refine ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩, ?_⟩
        simp
      · have hv_pos : 1 ≤ x.val := by
          by_contra h0
          exact hx0 ((ZMod.val_eq_zero x).mp (Nat.lt_one_iff.mp (Nat.not_le.mp h0)))
        have hv_lt : x.val < q := ZMod.val_lt x
        exact ⟨x.val, Finset.mem_Icc.mpr ⟨hv_pos, hv_lt.le⟩, ZMod.natCast_zmod_val x⟩
    · intro a _
      conv_rhs => rw [← Nat.cast_mul, Arith4Ext.SieveCharacters.zmodAddChar_apply_natCast]
      unfold e
      congr 1
      push_cast
      ring
  rw [hcast, Arith4Ext.SieveCharacters.sum_zmodAddChar]
  have hiff : (n : ZMod q) = 0 ↔ q ∣ n := ZMod.natCast_eq_zero_iff n q
  by_cases hd : q ∣ n
  · simp [hd, hiff.mpr hd]
  · have hne : (n : ZMod q) ≠ 0 := fun h => hd (hiff.mp h)
    simp [hd, hne]

lemma sum_divisors_ramanujanSum {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ∑ d ∈ q.divisors, ramanujanSum d n = if q ∣ n then (q : ℂ) else 0 := by
  rw [← sum_e_div_eq_ite hq n]
  -- Partition `a ∈ Icc 1 q` by `d = q / gcd(a, q) ∈ q.divisors`!
  have hmaps : ∀ a ∈ Finset.Icc 1 q, q / Nat.gcd a q ∈ q.divisors := by
    intro a _
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a q), by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_dvd : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_dvd hq
  set g := q / d
  have hgd : g * d = q := Nat.div_mul_cancel hd_dvd
  have hg_pos : 1 ≤ g := by
    by_contra h0
    have hg0 : g = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
    rw [hg0, zero_mul] at hgd
    omega
  unfold ramanujanSum
  symm
  refine Finset.sum_bij (fun a _ => a / g) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    have hgcd_eq : Nat.gcd a q = g := by
      have h1 : Nat.gcd a q ∣ q := Nat.gcd_dvd_right a q
      have h2 := Nat.mul_div_cancel' h1
      rw [ha.2] at h2
      have : Nat.gcd a q * d = g * d := h2.trans hgd.symm
      exact Nat.eq_of_mul_eq_mul_right hd_pos this
    have hg_dvd_a : g ∣ a := hgcd_eq ▸ Nat.gcd_dvd_left a q
    have ha_eq : g * (a / g) = a := Nat.mul_div_cancel' hg_dvd_a
    have h1 : 1 ≤ a / g := by
      by_contra h0
      have h0' : a / g = 0 := Nat.lt_one_iff.mp (Nat.not_le.mp h0)
      rw [h0', mul_zero] at ha_eq
      omega
    have h2 : a / g ≤ d := by
      have : g * (a / g) ≤ g * d := by rw [ha_eq, hgd]; exact ha.1.2
      exact Nat.le_of_mul_le_mul_left this hg_pos
    have hcop : Nat.Coprime (a / g) d := by
      have h3 := Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a (by omega : 0 < q))
      rwa [ha.2, hgcd_eq] at h3
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, hcop⟩
  · intro a₁ h1 a₂ h2 heq
    simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2
    have hgcd1 : Nat.gcd a₁ q = g := by
      have h := Nat.mul_div_cancel' (Nat.gcd_dvd_right a₁ q)
      rw [h1.2] at h
      exact Nat.eq_of_mul_eq_mul_right hd_pos (h.trans hgd.symm)
    have hgcd2 : Nat.gcd a₂ q = g := by
      have h := Nat.mul_div_cancel' (Nat.gcd_dvd_right a₂ q)
      rw [h2.2] at h
      exact Nat.eq_of_mul_eq_mul_right hd_pos (h.trans hgd.symm)
    have hmul1 : g * (a₁ / g) = a₁ := Nat.mul_div_cancel' (hgcd1 ▸ Nat.gcd_dvd_left a₁ q)
    have hmul2 : g * (a₂ / g) = a₂ := Nat.mul_div_cancel' (hgcd2 ▸ Nat.gcd_dvd_left a₂ q)
    rw [← hmul1, ← hmul2, heq]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    refine ⟨g * b, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hg_pos hb.1.1, by rw [← hgd]; exact Nat.mul_le_mul_left g hb.1.2⟩, ?_⟩,
      Nat.mul_div_cancel_left b hg_pos⟩
    have hgcd : Nat.gcd (g * b) q = g := by
      rw [← hgd, Nat.gcd_mul_left, hb.2.gcd_eq_one, mul_one]
    rw [hgcd, ← hgd, Nat.mul_div_cancel_left d hg_pos]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    have hgcd : Nat.gcd a q = g := by
      have h := Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)
      rw [ha.2] at h
      exact Nat.eq_of_mul_eq_mul_right hd_pos (h.trans hgd.symm)
    have ha_eq : (a : ℝ) = (g : ℝ) * ((a / g : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (hgcd ▸ Nat.gcd_dvd_left a q)).symm
    have hq_eq : (q : ℝ) = (g : ℝ) * (d : ℝ) := by exact_mod_cast hgd.symm
    have hg_ne : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    congr 1
    rw [ha_eq, hq_eq]
    field_simp [hg_ne, hd_ne]

/-- **Möbius Inversion Formula for Ramanujan Sums**:
For every `q ≥ 1` and `n : ℕ`,
`c_q(n) = ∑_{d ∣ gcd(q, n)} d * μ(q / d)`. -/
theorem ramanujanSum_eq_sum_moebius {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ramanujanSum q n =
      ∑ d ∈ (Nat.gcd q n).divisors,
        ((d : ℤ) * ArithmeticFunction.moebius (q / d) : ℂ) := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ)
    (f := fun d => ramanujanSum d n)
    (g := fun d => if d ∣ n then (d : ℂ) else 0)).mp
    (fun m hm => sum_divisors_ramanujanSum hm n) q hq
  rw [← hinv]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun a b =>
    (ArithmeticFunction.moebius a : ℂ) * (if b ∣ n then (b : ℂ) else 0))]
  have hsub : (Nat.gcd q n).divisors = q.divisors.filter (· ∣ n) := by
    ext d
    have hgcd_ne : Nat.gcd q n ≠ 0 := (Nat.gcd_pos_of_pos_left n hq).ne'
    simp [Nat.mem_divisors, hgcd_ne, show q ≠ 0 by omega, Nat.dvd_gcd_iff]
  rw [hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∣ n
  · simp only [hd, ↓reduceIte]
    push_cast
    ring
  · simp [hd]

lemma ramanujanSum_im_eq_zero {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    (ramanujanSum q n).im = 0 := by
  rw [ramanujanSum_eq_sum_moebius hq n]
  have hreal : (∑ d ∈ (Nat.gcd q n).divisors,
      ((d : ℤ) * ArithmeticFunction.moebius (q / d) : ℂ)) =
      (((∑ d ∈ (Nat.gcd q n).divisors,
        (d : ℤ) * ArithmeticFunction.moebius (q / d) : ℤ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hreal, Complex.ofReal_im]

/-- **Exact Multiplicativity of Ramanujan Sums**:
For coprime `q₁, q₂ ≥ 1`, `c_{q₁ q₂}(n) = c_{q₁}(n) * c_{q₂}(n)`. -/
theorem ramanujanSum_mul_coprime {q₁ q₂ : ℕ} (h1 : 1 ≤ q₁) (h2 : 1 ≤ q₂)
    (hcop : Nat.Coprime q₁ q₂) (n : ℕ) :
    ramanujanSum (q₁ * q₂) n = ramanujanSum q₁ n * ramanujanSum q₂ n := by
  let gFun : ArithmeticFunction ℂ :=
    { toFun := fun d => if d = 0 then 0 else if d ∣ n then (d : ℂ) else 0
      map_zero' := rfl }
  have hg_mult : gFun.IsMultiplicative := by
    refine ⟨by simp [gFun], fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · simp [gFun, ha]
    · by_cases hb : b = 0
      · simp [gFun, hb]
      · have hab_ne : a * b ≠ 0 := mul_ne_zero ha hb
        simp only [gFun, ArithmeticFunction.coe_mk, ha, hb, hab_ne, ↓reduceIte]
        have hdvd_iff : a * b ∣ n ↔ a ∣ n ∧ b ∣ n :=
          ⟨fun h => ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩,
           fun ⟨h1, h2⟩ => hab.mul_dvd_of_dvd_of_dvd h1 h2⟩
        by_cases ha_n : a ∣ n <;> by_cases hb_n : b ∣ n
        · simp [hdvd_iff, ha_n, hb_n]
        · simp [hdvd_iff, ha_n, hb_n]
        · simp [hdvd_iff, ha_n, hb_n]
        · simp [hdvd_iff, ha_n, hb_n]
  let muC : ArithmeticFunction ℂ := (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
  have hmu_mult : muC.IsMultiplicative := by
    refine ⟨by simp [muC], fun {a b} hab => ?_⟩
    have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
    simp only [muC, ArithmeticFunction.intCoe_apply]
    exact_mod_cast h
  have hconv_mult : (muC * gFun).IsMultiplicative := hmu_mult.mul hg_mult
  have heq : ∀ q : ℕ, 1 ≤ q → (muC * gFun) q = ramanujanSum q n := by
    intro q hq
    rw [ArithmeticFunction.mul_apply, ramanujanSum_eq_sum_moebius hq n]
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => muC a * gFun b)]
    have hsub : (Nat.gcd q n).divisors = q.divisors.filter (· ∣ n) := by
      ext d
      have hgcd_ne : Nat.gcd q n ≠ 0 := (Nat.gcd_pos_of_pos_left n hq).ne'
      simp [Nat.mem_divisors, hgcd_ne, show q ≠ 0 by omega, Nat.dvd_gcd_iff]
    rw [hsub, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd_pos : d ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hq).ne'
    simp only [muC, gFun, ArithmeticFunction.intCoe_apply, ArithmeticFunction.coe_mk, hd_pos,
      ↓reduceIte]
    by_cases hdn : d ∣ n
    · simp only [hdn, ↓reduceIte]; push_cast; ring
    · simp [hdn]
  rw [← heq (q₁ * q₂) (Nat.mul_pos h1 h2), ← heq q₁ h1, ← heq q₂ h2]
  exact hconv_mult.map_mul_of_coprime hcop

lemma ramanujanSum_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) (n : ℕ) :
    ramanujanSum (p ^ k) n =
      ((ArithmeticFunction.moebius (p ^ k / Nat.gcd (p ^ k) n) : ℂ) *
        (Nat.totient (p ^ k) : ℂ)) /
      (Nat.totient (p ^ k / Nat.gcd (p ^ k) n) : ℂ) := by
  have hpk_pos : 1 ≤ p ^ k := Nat.one_le_pow k p hp.pos
  rw [ramanujanSum_eq_sum_moebius hpk_pos n]
  have htot_pk : (Nat.totient (p ^ k) : ℂ) = (p : ℂ) ^ (k - 1) * ((p : ℂ) - 1) := by
    rw [Nat.totient_prime_pow hp hk]
    push_cast
    rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  by_cases hdiv_k : p ^ k ∣ n
  · -- Case 1: `p^k ∣ n`
    have hgcd : Nat.gcd (p ^ k) n = p ^ k := Nat.gcd_eq_left hdiv_k
    rw [hgcd, Nat.div_self hpk_pos]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul,
      Nat.totient_one, Nat.cast_one, div_one, htot_pk]
    -- Only `d = p^k` and `d = p^(k-1)` survive in `∑_{d ∣ p^k} d * μ(p^k / d)`
    rw [Nat.divisors_prime_pow hp]
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    have hrange : Finset.range (k + 1) = insert k (insert (k - 1) (Finset.range (k - 1))) := by
      ext j; simp only [Finset.mem_range, Finset.mem_insert]; omega
    rw [hrange, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
    have hrest : ∑ j ∈ Finset.range (k - 1),
        (((p ^ j : ℕ) : ℤ) * ArithmeticFunction.moebius (p ^ k / p ^ j) : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_lt : j < k - 1 := Finset.mem_range.mp hj
      rw [Nat.pow_div (by omega) hp.pos]
      have hmu0 : ArithmeticFunction.moebius (p ^ (k - j)) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show k - j ≠ 1 by omega]
      simp [hmu0]
    rw [hrest, add_zero, Nat.div_self hpk_pos, ArithmeticFunction.moebius_apply_one, Int.cast_one,
      mul_one, Nat.pow_div (by omega) hp.pos, show k - (k - 1) = 1 by omega, pow_one,
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    have hpow_eq : (p : ℂ) ^ k = (p : ℂ) ^ (k - 1) * (p : ℂ) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    rw [hpow_eq]
    ring
  · by_cases hdiv_km1 : p ^ (k - 1) ∣ n
    · -- Case 2: `p^(k-1) ∣ n` and `¬ p^k ∣ n`
      have hgcd : Nat.gcd (p ^ k) n = p ^ (k - 1) := by
        have hdvd_g : p ^ (k - 1) ∣ Nat.gcd (p ^ k) n :=
          Nat.dvd_gcd (pow_dvd_pow p (Nat.sub_le k 1)) hdiv_km1
        rcases (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ k) n) with ⟨j, hj_le, hj_eq⟩
        have hj_ge : k - 1 ≤ j := by
          rw [hj_eq] at hdvd_g
          exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd_g
        have hj_lt : j < k := by
          by_contra hge
          have heq : j = k := by omega
          rw [heq] at hj_eq
          exact hdiv_k (hj_eq ▸ Nat.gcd_dvd_right (p ^ k) n)
        have : j = k - 1 := by omega
        rw [hj_eq, this]
      rw [hgcd, Nat.pow_div (Nat.sub_le k 1) hp.pos, show k - (k - 1) = 1 by omega, pow_one,
        ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp, htot_pk]
      have hp1_ne : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (by have := hp.two_le; omega : p - 1 ≠ 0)
      have hp1_cast : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by
        rw [Nat.cast_sub hp.one_le, Nat.cast_one]
      rw [hp1_cast] at hp1_ne ⊢
      have hrhs : ((-1 : ℤ) : ℂ) * ((p : ℂ) ^ (k - 1) * ((p : ℂ) - 1)) / ((p : ℂ) - 1) =
          -((p : ℂ) ^ (k - 1)) := by
        field_simp [hp1_ne]
        ring
      rw [hrhs, Nat.divisors_prime_pow hp]
      simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
      have hrange : Finset.range (k - 1 + 1) = insert (k - 1) (Finset.range (k - 1)) :=
        Finset.range_add_one
      rw [hrange, Finset.sum_insert (by simp)]
      have hrest : ∑ j ∈ Finset.range (k - 1),
          (((p ^ j : ℕ) : ℤ) * ArithmeticFunction.moebius (p ^ k / p ^ j) : ℂ) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj_lt : j < k - 1 := Finset.mem_range.mp hj
        rw [Nat.pow_div (by omega) hp.pos]
        have hmu0 : ArithmeticFunction.moebius (p ^ (k - j)) = 0 := by
          rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
          simp [show k - j ≠ 1 by omega]
        simp [hmu0]
      rw [hrest, add_zero, Nat.pow_div (Nat.sub_le k 1) hp.pos, show k - (k - 1) = 1 by omega,
        pow_one, ArithmeticFunction.moebius_apply_prime hp]
      push_cast
      ring
    · -- Case 3: `¬ p^(k-1) ∣ n`, so `gcd(p^k, n) = p^j` with `j ≤ k - 2`
      rcases (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ k) n) with ⟨j, hj_le, hj_eq⟩
      have hj_le2 : j + 2 ≤ k := by
        by_contra hgt
        have hge : k - 1 ≤ j := by omega
        have hd : p ^ (k - 1) ∣ n :=
          (pow_dvd_pow p hge).trans (hj_eq ▸ Nat.gcd_dvd_right (p ^ k) n)
        exact hdiv_km1 hd
      rw [hj_eq, Nat.pow_div hj_le hp.pos]
      have hmu_rhs : ArithmeticFunction.moebius (p ^ (k - j)) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show k - j ≠ 1 by omega]
      rw [hmu_rhs, Int.cast_zero, zero_mul, zero_div]
      refine Finset.sum_eq_zero fun d hd => ?_
      rcases (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd) with ⟨i, hi_le, rfl⟩
      rw [Nat.pow_div (hi_le.trans hj_le) hp.pos]
      have hmu0 : ArithmeticFunction.moebius (p ^ (k - i)) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show k - i ≠ 1 by omega]
      simp [hmu0]

/-- **Hölder's Exact Formula (1936)** for Ramanujan sums:
For all `q ≥ 1` and `n : ℕ`,
`c_q(n) = μ(q / gcd(q, n)) * φ(q) / φ(q / gcd(q, n))`. -/
theorem ramanujanSum_holder {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    ramanujanSum q n =
      ((ArithmeticFunction.moebius (q / Nat.gcd q n) : ℂ) * (Nat.totient q : ℂ)) /
        (Nat.totient (q / Nat.gcd q n) : ℂ) := by
  -- Both sides are multiplicative in `q` and agree on prime powers!
  set RHS : ℕ → ℂ := fun m =>
    ((ArithmeticFunction.moebius (m / Nat.gcd m n) : ℂ) * (Nat.totient m : ℂ)) /
      (Nat.totient (m / Nat.gcd m n) : ℂ)
  have hRHS_one : RHS 1 = 1 := by simp [RHS]
  have hRHS_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Nat.Coprime a b →
      RHS (a * b) = RHS a * RHS b := by
    intro a b ha hb hcop
    dsimp [RHS]
    have hgcd_mul : Nat.gcd (a * b) n = Nat.gcd a n * Nat.gcd b n := by
      have hcop_g : Nat.Coprime (Nat.gcd a n) (Nat.gcd b n) :=
        (hcop.coprime_dvd_left (Nat.gcd_dvd_left a n)).coprime_dvd_right (Nat.gcd_dvd_left b n)
      refine Nat.dvd_antisymm ?_ ?_
      · have hd1 : Nat.gcd (a * b) n ∣ a * Nat.gcd b n := by
          have : Nat.gcd (a * b) n ∣ Nat.gcd (a * b) (a * n) :=
            Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left n a))
          rwa [Nat.gcd_mul_left] at this
        have hd2 : Nat.gcd (a * b) n ∣ Nat.gcd a n * b := by
          have : Nat.gcd (a * b) n ∣ Nat.gcd (a * b) (n * b) :=
            Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right n b))
          rwa [Nat.gcd_mul_right] at this
        have hd3 : Nat.gcd (a * b) n ∣ Nat.gcd a n * Nat.gcd b n := by
          have hstep : Nat.gcd (a * b) n ∣ Nat.gcd (a * Nat.gcd b n) (Nat.gcd a n * b) :=
            Nat.dvd_gcd hd1 hd2
          have hEq : Nat.gcd (a * Nat.gcd b n) (Nat.gcd a n * b) = Nat.gcd a n * Nat.gcd b n := by
            set ga := Nat.gcd a n
            set gb := Nat.gcd b n
            have hda : ga ∣ a := Nat.gcd_dvd_left a n
            have hdb : gb ∣ b := Nat.gcd_dvd_left b n
            rcases hda with ⟨a', ha'⟩
            rcases hdb with ⟨b', hb'⟩
            have hcop' : Nat.Coprime a' b' := by
              have h1 : a' ∣ a := ⟨ga, by linarith⟩
              have h2 : b' ∣ b := ⟨gb, by linarith⟩
              exact (hcop.coprime_dvd_left h1).coprime_dvd_right h2
            calc Nat.gcd (a * gb) (ga * b)
                = Nat.gcd ((ga * gb) * a') ((ga * gb) * b') := by
                  rw [ha', hb']; ring_nf
              _ = (ga * gb) * Nat.gcd a' b' := Nat.gcd_mul_left _ _ _
              _ = ga * gb := by rw [hcop'.gcd_eq_one, mul_one]
          rwa [hEq] at hstep
        exact hd3
      · exact hcop_g.mul_dvd_of_dvd_of_dvd
          (Nat.dvd_gcd ((Nat.gcd_dvd_left a n).trans (dvd_mul_right a b)) (Nat.gcd_dvd_right a n))
          (Nat.dvd_gcd ((Nat.gcd_dvd_left b n).trans (dvd_mul_left b a)) (Nat.gcd_dvd_right b n))
    have hda : Nat.gcd a n ∣ a := Nat.gcd_dvd_left a n
    have hdb : Nat.gcd b n ∣ b := Nat.gcd_dvd_left b n
    have hdiv_mul : (a * b) / Nat.gcd (a * b) n = (a / Nat.gcd a n) * (b / Nat.gcd b n) := by
      rw [hgcd_mul]
      exact Nat.mul_div_mul_comm hda hdb
    have hcop_div : Nat.Coprime (a / Nat.gcd a n) (b / Nat.gcd b n) :=
      (hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hda)).coprime_dvd_right (Nat.div_dvd_of_dvd hdb)
    rw [hdiv_mul, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_div,
      Nat.totient_mul hcop, Nat.totient_mul hcop_div]
    push_cast
    ring
  change ramanujanSum q n = RHS q
  have hprod : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : q ≠ 0)]
    rw [Finsupp.prod, Nat.support_factorization]
  have hprimes : ∀ p ∈ q.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
  have hpos_exp : ∀ p ∈ q.primeFactors, 1 ≤ q.factorization p := fun p hp =>
    Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) (by omega)
      (Nat.dvd_of_mem_primeFactors hp)
  set e : ℕ → ℕ := fun p => q.factorization p
  conv_lhs => rw [hprod]
  conv_rhs => rw [hprod]
  generalize q.primeFactors = S at hprimes hpos_exp ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp [ramanujanSum_one, hRHS_one]
  | @insert a s ha ih =>
    have ha_p : Nat.Prime a := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    have ha_e : 1 ≤ e a := hpos_exp a (Finset.mem_insert_self a s)
    have hs_e : ∀ p ∈ s, 1 ≤ e p := fun p hp => hpos_exp p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime (a ^ e a) (∏ p ∈ s, p ^ e p) :=
      Nat.Coprime.prod_right fun p hp =>
        ((Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))).pow _ _
    have hpos1 : 1 ≤ a ^ e a := Nat.one_le_pow _ a ha_p.pos
    have hpos2 : 1 ≤ ∏ p ∈ s, p ^ e p :=
      Finset.prod_pos fun p hp => pow_pos (hs_p p hp).pos _
    rw [Finset.prod_insert ha, ramanujanSum_mul_coprime hpos1 hpos2 hcop,
      hRHS_mul _ _ hpos1 hpos2 hcop, ramanujanSum_prime_pow ha_p ha_e n, ih hs_p hs_e]

lemma card_Icc_coprime_eq_totient {q : ℕ} (hq : 1 ≤ q) :
    ((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).card = Nat.totient q := by
  rw [Nat.totient_eq_card_coprime]
  refine Finset.card_bij (fun a _ => a % q) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at ha ⊢
    refine ⟨Nat.mod_lt a hq, ?_⟩
    show Nat.gcd q (a % q) = 1
    rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
    exact ha.2.gcd_eq_one
  · intro a₁ h1 a₂ h2 heq
    simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2
    by_cases h1q : a₁ = q
    · rw [h1q, Nat.mod_self] at heq
      by_cases h2q : a₂ = q
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)] at heq; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at heq
      by_cases h2q : a₂ = q
      · rw [h2q, Nat.mod_self] at heq; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at heq; exact heq
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    by_cases hr0 : r = 0
    · subst hr0
      have hq1 : q = 1 := by simpa using hr.2.gcd_eq_one
      subst hq1
      exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩, by simp⟩, by simp⟩
    · exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hr.1.le⟩, hr.2.symm⟩,
        Nat.mod_eq_of_lt hr.1⟩

/-- **Orthogonality of Ramanujan Sums**:
For any `q₁, q₂ ≥ 1` and any common multiple `Q ≥ 1` (`q₁ ∣ Q`, `q₂ ∣ Q`),
`∑_{n=1}^Q c_{q₁}(n) * star(c_{q₂}(n)) = Q * φ(q₁)` if `q₁ = q₂`, and `0` otherwise. -/
theorem ramanujanSum_orthogonality {q₁ q₂ Q : ℕ} (h1 : 1 ≤ q₁) (h2 : 1 ≤ q₂) (hQ : 1 ≤ Q)
    (hq1 : q₁ ∣ Q) (hq2 : q₂ ∣ Q) :
    ∑ n ∈ Finset.Icc 1 Q, ramanujanSum q₁ n * star (ramanujanSum q₂ n) =
      if q₁ = q₂ then (Q : ℂ) * (Nat.totient q₁ : ℂ) else 0 := by
  set R₁ := (Finset.Icc 1 q₁).filter (fun a => Nat.Coprime a q₁)
  set R₂ := (Finset.Icc 1 q₂).filter (fun b => Nat.Coprime b q₂)
  have hexpand : ∀ n ∈ Finset.Icc 1 Q,
      ramanujanSum q₁ n * star (ramanujanSum q₂ n) =
        ∑ a ∈ R₁, ∑ b ∈ R₂,
          e ((n : ℝ) * ((a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ))) := by
    intro n _
    unfold ramanujanSum
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change e ((a : ℝ) * (n : ℝ) / (q₁ : ℝ)) * star (e ((b : ℝ) * (n : ℝ) / (q₂ : ℝ))) = _
    rw [← e_neg, ← e_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  have hswap : ∑ a ∈ R₁, ∑ n ∈ Finset.Icc 1 Q, ∑ b ∈ R₂,
        e ((n : ℝ) * ((a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ))) =
      ∑ a ∈ R₁, ∑ b ∈ R₂, ∑ n ∈ Finset.Icc 1 Q,
        e ((n : ℝ) * ((a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ))) :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [hswap]
  have hinner : ∀ a ∈ R₁, ∀ b ∈ R₂,
      ∑ n ∈ Finset.Icc 1 Q, e ((n : ℝ) * ((a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ))) =
        if q₁ = q₂ ∧ a = b then (Q : ℂ) else 0 := by
    intro a ha b hb
    simp only [R₁, R₂, Finset.mem_filter, Finset.mem_Icc] at ha hb
    rcases hq1 with ⟨m₁, hm₁⟩
    rcases hq2 with ⟨m₂, hm₂⟩
    set K : ℤ := (a : ℤ) * (m₁ : ℤ) - (b : ℤ) * (m₂ : ℤ)
    have hK_eq : (a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ) = (K : ℝ) / (Q : ℝ) := by
      dsimp [K]
      have hq1_ne : (q₁ : ℝ) ≠ 0 := by exact_mod_cast (by omega : q₁ ≠ 0)
      have hq2_ne : (q₂ : ℝ) ≠ 0 := by exact_mod_cast (by omega : q₂ ≠ 0)
      have hQ_ne : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
      have hm1_r : (Q : ℝ) = (q₁ : ℝ) * (m₁ : ℝ) := by exact_mod_cast hm₁
      have hm2_r : (Q : ℝ) = (q₂ : ℝ) * (m₂ : ℝ) := by exact_mod_cast hm₂
      push_cast
      field_simp [hq1_ne, hq2_ne, hQ_ne]
      have heq1 : (a : ℝ) * (q₂ : ℝ) * (Q : ℝ) = (q₁ : ℝ) * (q₂ : ℝ) * ((a : ℝ) * (m₁ : ℝ)) := by
        rw [hm1_r]; ring
      have heq2 : (q₁ : ℝ) * (b : ℝ) * (Q : ℝ) = (q₁ : ℝ) * (q₂ : ℝ) * ((b : ℝ) * (m₂ : ℝ)) := by
        rw [hm2_r]; ring
      linarith
    have hK_dvd_iff : (Q : ℤ) ∣ K ↔ q₁ = q₂ ∧ a = b := by
      constructor
      · intro ⟨t, ht⟩
        -- `(a/q₁ - b/q₂) = t ∈ ℤ`; since `a/q₁ ∈ (0, 1]` and `b/q₂ ∈ (0, 1]`, `t = 0`!
        have ht_r : (a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ) = (t : ℝ) := by
          rw [hK_eq]
          have hQ_ne : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
          have hKt : (K : ℝ) = (Q : ℝ) * (t : ℝ) := by exact_mod_cast ht
          rw [hKt, mul_div_cancel_left₀ _ hQ_ne]
        have ha_pos_r : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
        have hq1_pos_r : (0 : ℝ) < (q₁ : ℝ) := by exact_mod_cast (by omega : 0 < q₁)
        have hb_pos_r : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
        have hq2_pos_r : (0 : ℝ) < (q₂ : ℝ) := by exact_mod_cast (by omega : 0 < q₂)
        have ha_pos : (0 : ℝ) < (a : ℝ) / (q₁ : ℝ) := div_pos ha_pos_r hq1_pos_r
        have ha_le1 : (a : ℝ) / (q₁ : ℝ) ≤ 1 := (div_le_one hq1_pos_r).mpr (by exact_mod_cast ha.1.2)
        have hb_pos : (0 : ℝ) < (b : ℝ) / (q₂ : ℝ) := div_pos hb_pos_r hq2_pos_r
        have hb_le1 : (b : ℝ) / (q₂ : ℝ) ≤ 1 := (div_le_one hq2_pos_r).mpr (by exact_mod_cast hb.1.2)
        have ht0 : t = 0 := by
          have h1 : (-1 : ℝ) < (t : ℝ) := by linarith
          have h2 : (t : ℝ) < 1 := by linarith
          have h1z : (-1 : ℤ) < t := by exact_mod_cast h1
          have h2z : t < 1 := by exact_mod_cast h2
          omega
        subst ht0
        have hfrac : (a : ℕ) * q₂ = (b : ℕ) * q₁ := by
          have hr : (a : ℝ) * (q₂ : ℝ) = (b : ℝ) * (q₁ : ℝ) := by
            have hq1_ne : (q₁ : ℝ) ≠ 0 := hq1_pos_r.ne'
            have hq2_ne : (q₂ : ℝ) ≠ 0 := hq2_pos_r.ne'
            have : (a : ℝ) / (q₁ : ℝ) = (b : ℝ) / (q₂ : ℝ) := by linarith
            field_simp [hq1_ne, hq2_ne] at this
            linarith
          exact_mod_cast hr
        have hq1_dvd_q2 : q₁ ∣ q₂ := ha.2.symm.dvd_of_dvd_mul_left ⟨b, by linarith⟩
        have hq2_dvd_q1 : q₂ ∣ q₁ := hb.2.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩
        have hq_eq : q₁ = q₂ := Nat.dvd_antisymm hq1_dvd_q2 hq2_dvd_q1
        subst hq_eq
        have ha_eq : a = b := Nat.eq_of_mul_eq_mul_right h1 hfrac
        exact ⟨rfl, ha_eq⟩
      · rintro ⟨rfl, rfl⟩
        have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left h1 (hm₁.symm.trans hm₂)
        subst hm_eq
        simp [K]
    -- Reduce `∑_{n=1}^Q e(n * K / Q)` to `sum_zmodAddChar`
    have : NeZero Q := ⟨by omega⟩
    have hsum_zmod : ∑ n ∈ Finset.Icc 1 Q,
          e ((n : ℝ) * ((a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ))) =
        ∑ x : ZMod Q, Arith4Ext.SieveCharacters.zmodAddChar Q (x * (K : ZMod Q)) := by
      -- Express via `e((n * K)/Q)`
      have hterm : ∀ n ∈ Finset.Icc 1 Q,
          e ((n : ℝ) * ((a : ℝ) / (q₁ : ℝ) - (b : ℝ) / (q₂ : ℝ))) =
            Arith4Ext.SieveCharacters.zmodAddChar Q ((n : ZMod Q) * (K : ZMod Q)) := by
        intro n _
        rw [hK_eq]
        -- Shift `K` by a positive multiple of `Q` to a `ℕ`
        have hQ_pos_z : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
        set r : ℕ := Int.toNat (K % (Q : ℤ))
        have hr_eq : (r : ℤ) = K % (Q : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg K hQ_pos_z.ne')
        have hK_mod : (K : ZMod Q) = (r : ZMod Q) := by
          have hd : (Q : ℤ) ∣ K - (r : ℤ) := by
            rw [hr_eq]
            exact ⟨K / (Q : ℤ), by linarith [Int.mul_ediv_add_emod K (Q : ℤ)]⟩
          exact (ZMod.intCast_eq_intCast_iff_dvd_sub (r : ℤ) K Q).mpr (by
            simpa [dvd_neg] using hd) |>.symm |> fun h => by simpa using h
        rw [hK_mod, ← Nat.cast_mul, Arith4Ext.SieveCharacters.zmodAddChar_apply_natCast]
        have hK_div : (K : ℝ) = (r : ℝ) + (Q : ℝ) * ((K / (Q : ℤ) : ℤ) : ℝ) := by
          have hz : K = (r : ℤ) + (Q : ℤ) * (K / (Q : ℤ)) := by
            rw [hr_eq]; linarith [Int.mul_ediv_add_emod K (Q : ℤ)]
          exact_mod_cast hz
        have hQ_ne : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
        have hdiff : (n : ℝ) * ((K : ℝ) / (Q : ℝ)) =
            ((n * r : ℕ) : ℝ) / (Q : ℝ) + (((n : ℤ) * (K / (Q : ℤ)) : ℤ) : ℝ) := by
          rw [hK_div]
          push_cast
          field_simp [hQ_ne]
        rw [hdiff, e_add_int]
        unfold e
        congr 1
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm]
      refine Finset.sum_bij (fun n _ => (n : ZMod Q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro n₁ h1n n₂ h2n heq
        simp only [Finset.mem_Icc] at h1n h2n
        have hmod : n₁ % Q = n₂ % Q := by
          have := congr_arg ZMod.val heq
          rwa [ZMod.val_natCast, ZMod.val_natCast] at this
        by_cases h1Q : n₁ = Q
        · rw [h1Q, Nat.mod_self] at hmod
          by_cases h2Q : n₂ = Q
          · omega
          · rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hmod
          by_cases h2Q : n₂ = Q
          · rw [h2Q, Nat.mod_self] at hmod; omega
          · rw [Nat.mod_eq_of_lt (by omega)] at hmod; exact hmod
      · intro x _
        by_cases hx0 : x = 0
        · subst hx0; exact ⟨Q, Finset.mem_Icc.mpr ⟨hQ, le_rfl⟩, by simp⟩
        · have hv1 : 1 ≤ x.val := by
            by_contra h0
            exact hx0 ((ZMod.val_eq_zero x).mp (Nat.lt_one_iff.mp (Nat.not_le.mp h0)))
          exact ⟨x.val, Finset.mem_Icc.mpr ⟨hv1, (ZMod.val_lt x).le⟩, ZMod.natCast_zmod_val x⟩
      · intro _ _; rfl
    rw [hsum_zmod, Arith4Ext.SieveCharacters.sum_zmodAddChar]
    have hK0_iff : (K : ZMod Q) = 0 ↔ (Q : ℤ) ∣ K := ZMod.intCast_zmod_eq_zero_iff_dvd K Q
    by_cases hcond : q₁ = q₂ ∧ a = b
    · simp [hcond, hK0_iff.mpr (hK_dvd_iff.mpr hcond)]
    · have hne : (K : ZMod Q) ≠ 0 := fun h => hcond (hK_dvd_iff.mp (hK0_iff.mp h))
      simp [hcond, hne]
  rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hinner a ha b hb]
  by_cases hqeq : q₁ = q₂
  · subst hqeq
    simp only [true_and, ↓reduceIte]
    have hcard : R₁.card = Nat.totient q₁ := card_Icc_coprime_eq_totient h1
    have hsum_R1 : ∑ a ∈ R₁, ∑ b ∈ R₂, (if a = b then (Q : ℂ) else 0) = (R₁.card : ℂ) * (Q : ℂ) := by
      have hR_eq : R₂ = R₁ := rfl
      rw [hR_eq]
      have h1 : ∀ a ∈ R₁, ∑ b ∈ R₁, (if a = b then (Q : ℂ) else 0) = (Q : ℂ) := fun a ha => by
        simp [ha]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_R1, hcard]
    ring
  · simp [hqeq]

/-! ### Ternary Odd-Goldbach Singular Series: Euler-Product Positivity & Lower Bound -/

/-- The `q`-th term of the ternary Goldbach singular series:
`A(n, q) = μ(q) * c_q(n) / φ(q)^3` (real-valued, equal to `0` at `q = 0`). -/
def ternarySingularTerm (n q : ℕ) : ℝ :=
  if q = 0 then 0 else
    (ArithmeticFunction.moebius q : ℝ) * (ramanujanSum q n).re / (Nat.totient q : ℝ) ^ 3

/-- The local Euler factor at a prime `p` for the ternary singular series:
`1 - 1/(p-1)^2` if `p ∣ n`, and `1 + 1/(p-1)^3` if `¬ p ∣ n`. -/
def ternaryLocalFactor (n p : ℕ) : ℝ :=
  if p ∣ n then 1 - ((p : ℝ) - 1)⁻¹ ^ 2 else 1 + ((p : ℝ) - 1)⁻¹ ^ 3

lemma abs_ramanujanSum_re_le_totient {q : ℕ} (hq : 1 ≤ q) (n : ℕ) :
    |(ramanujanSum q n).re| ≤ (Nat.totient q : ℝ) := by
  calc |(ramanujanSum q n).re| ≤ ‖ramanujanSum q n‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q),
          ‖e ((a : ℝ) * (n : ℝ) / (q : ℝ))‖ := norm_sum_le _ _
    _ = (((Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)).card : ℝ) := by
        simp [norm_e]
    _ = (Nat.totient q : ℝ) := by
        exact_mod_cast card_Icc_coprime_eq_totient hq

lemma cube_le_sixteen_mul_totient_pow_four {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 ≤ 16 * (Nat.totient q) ^ 4 := by
  -- Prove factor-by-factor over prime powers: `p=2` gives factor `8`, `p=3` gives factor `2`, `p≥5` gives factor `1`!
  have hpp : ∀ p k : ℕ, Nat.Prime p → 1 ≤ k →
      (p ^ k) ^ 3 ≤
        (if p = 2 then 8 else if p = 3 then 2 else 1) * (Nat.totient (p ^ k)) ^ 4 := by
    intro p k hp hk
    rw [Nat.totient_prime_pow hp hk, mul_pow, ← pow_mul, ← pow_mul]
    split_ifs with hp2 hp3
    · subst hp2
      have h1 : (2 - 1) ^ 4 = 1 := by norm_num
      rw [h1, mul_one, show 8 = 2 ^ 3 by norm_num, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · subst hp3
      have h1 : (3 - 1) ^ 4 = 16 := by norm_num
      rw [h1]
      -- Direct: `3^(3k) ≤ 32 * 3^(4k - 4) = 32 * 3^(3k - 3 + k - 1)`
      have hpow : 3 ^ (k * 3) = 3 ^ ((k - 1) * 4) * 3 ^ (4 - k) ∨ (k - 1) * 4 ≥ k * 3 := by
        by_cases hk4 : k ≥ 4
        · right; omega
        · left
          rw [← pow_add]
          congr 1; omega
      rcases hpow with heq | hge
      · rw [heq]
        have h32 : 3 ^ (4 - k) ≤ 2 * 16 := by
          have : 4 - k ≤ 3 := by omega
          calc 3 ^ (4 - k) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
            _ = 27 := by norm_num
            _ ≤ 2 * 16 := by norm_num
        calc 3 ^ ((k - 1) * 4) * 3 ^ (4 - k) ≤ 3 ^ ((k - 1) * 4) * (2 * 16) :=
              Nat.mul_le_mul_left _ h32
          _ = 2 * (3 ^ ((k - 1) * 4) * 16) := by ring
      · calc 3 ^ (k * 3) ≤ 3 ^ ((k - 1) * 4) := Nat.pow_le_pow_right (by norm_num) hge
          _ ≤ 2 * (3 ^ ((k - 1) * 4) * 16) := by omega
    · -- `p ≥ 5`: `(p - 1)^4 ≥ p^3` and `p^((k-1)*4) * p^3 ≥ p^(3k)`!
      have hp5 : 5 ≤ p := by
        have hp2' := hp.two_le
        have hne4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by decide)
        omega
      have hp4 : p ^ 3 ≤ (p - 1) ^ 4 := by
        have h1 : (p - 1 : ℕ) + 1 = p := Nat.sub_add_cancel (by omega)
        set m := p - 1
        have hm4 : 4 ≤ m := by omega
        have hp_eq : p = m + 1 := h1.symm
        rw [hp_eq]
        have hstep1 : (m + 1) ^ 3 ≤ 4 * m ^ 3 := by
          have h1' : (m : ℤ) ^ 3 * 3 ≥ 3 * (m : ℤ) ^ 2 + 3 * (m : ℤ) + 1 := by
            have hm4z : (4 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm4
            nlinarith [sq_nonneg ((m : ℤ) - 4)]
          have h2' : ((m + 1 : ℕ) : ℤ) ^ 3 ≤ 4 * ((m : ℤ) ^ 3) := by push_cast; linarith
          exact_mod_cast h2'
        calc (m + 1) ^ 3 ≤ 4 * m ^ 3 := hstep1
          _ ≤ m * m ^ 3 := Nat.mul_le_mul_right _ hm4
          _ = m ^ 4 := by ring
      have hexp : k * 3 = (k - 1) * 3 + 3 := by omega
      rw [one_mul, hexp, pow_add]
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_right hp.pos (by omega : (k - 1) * 3 ≤ (k - 1) * 4)) hp4
  -- Multiply over `q.primeFactors`
  have hprod : q = ∏ p ∈ q.primeFactors, p ^ q.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : q ≠ 0)]
    rw [Finsupp.prod, Nat.support_factorization]
  have htot_prod : Nat.totient q = ∏ p ∈ q.primeFactors, Nat.totient (p ^ q.factorization p) := by
    conv_lhs => rw [hprod]
    have hprimes : ∀ p ∈ q.primeFactors, Nat.Prime p := fun _ hp => Nat.prime_of_mem_primeFactors hp
    set e : ℕ → ℕ := fun p => q.factorization p
    generalize q.primeFactors = S at hprimes ⊢
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      have ha_p := hprimes a (Finset.mem_insert_self a s)
      have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime (a ^ e a) (∏ p ∈ s, p ^ e p) :=
        Nat.Coprime.prod_right fun p hp =>
          ((Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))).pow _ _
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.totient_mul hcop, ih hs_p]
  have hc_le : (∏ p ∈ q.primeFactors, (if p = 2 then 8 else if p = 3 then 2 else 1)) ≤ 16 := by
    have hsub : q.primeFactors.filter (fun p => p = 2 ∨ p = 3) ⊆ {2, 3} := by
      intro p hp; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
      exact hp.2
    have hprod_eq : (∏ p ∈ q.primeFactors, (if p = 2 then 8 else if p = 3 then 2 else 1)) =
        ∏ p ∈ q.primeFactors.filter (fun p => p = 2 ∨ p = 3),
          (if p = 2 then 8 else if p = 3 then 2 else 1) := by
      symm
      refine Finset.prod_subset (Finset.filter_subset _ _) fun p hp hnot => ?_
      simp only [Finset.mem_filter, not_and] at hnot
      have h23 : p ≠ 2 ∧ p ≠ 3 := not_or.mp (hnot hp)
      simp [h23.1, h23.2]
    rw [hprod_eq]
    calc ∏ p ∈ q.primeFactors.filter (fun p => p = 2 ∨ p = 3),
            (if p = 2 then 8 else if p = 3 then 2 else 1)
        ≤ ∏ p ∈ ({2, 3} : Finset ℕ), (if p = 2 then 8 else if p = 3 then 2 else 1) := by
          refine Finset.prod_le_prod_of_subset_of_one_le' hsub fun p _ _ => ?_
          split_ifs <;> omega
      _ = 16 := by decide
  rw [htot_prod]
  conv_lhs => rw [hprod]
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  calc ∏ p ∈ q.primeFactors, (p ^ q.factorization p) ^ 3
      ≤ ∏ p ∈ q.primeFactors,
          ((if p = 2 then 8 else if p = 3 then 2 else 1) *
            (Nat.totient (p ^ q.factorization p)) ^ 4) := by
        refine Finset.prod_le_prod' fun p hp => ?_
        have hp_p := Nat.prime_of_mem_primeFactors hp
        have hk := Nat.Prime.factorization_pos_of_dvd hp_p (by omega) (Nat.dvd_of_mem_primeFactors hp)
        exact hpp p (q.factorization p) hp_p hk
    _ = (∏ p ∈ q.primeFactors, (if p = 2 then 8 else if p = 3 then 2 else 1)) *
          ∏ p ∈ q.primeFactors, (Nat.totient (p ^ q.factorization p)) ^ 4 :=
        Finset.prod_mul_distrib
    _ ≤ 16 * ∏ p ∈ q.primeFactors, (Nat.totient (p ^ q.factorization p)) ^ 4 :=
        Nat.mul_le_mul_right _ hc_le

lemma abs_ternarySingularTerm_le (n q : ℕ) :
    |ternarySingularTerm n q| ≤ 4 * ((q : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
  by_cases hq0 : q = 0
  · subst hq0; simp [ternarySingularTerm]
  · have hq : 1 ≤ q := Nat.pos_of_ne_zero hq0
    have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have htot_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
    simp only [ternarySingularTerm, hq0, ↓reduceIte, abs_div, abs_mul,
      abs_pow, abs_of_pos htot_pos]
    have hmu : |(ArithmeticFunction.moebius q : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
    have hram := abs_ramanujanSum_re_le_totient hq n
    have h1 : |(ArithmeticFunction.moebius q : ℝ)| * |(ramanujanSum q n).re| /
        (Nat.totient q : ℝ) ^ 3 ≤ ((Nat.totient q : ℝ) ^ 2)⁻¹ := by
      calc |(ArithmeticFunction.moebius q : ℝ)| * |(ramanujanSum q n).re| / (Nat.totient q : ℝ) ^ 3
          ≤ 1 * (Nat.totient q : ℝ) / (Nat.totient q : ℝ) ^ 3 :=
            div_le_div_of_nonneg_right
              (mul_le_mul hmu hram (abs_nonneg _) zero_le_one) (by positivity)
        _ = ((Nat.totient q : ℝ) ^ 2)⁻¹ := by field_simp [htot_pos.ne']
    have h2 : ((Nat.totient q : ℝ) ^ 2)⁻¹ ≤ 4 * ((q : ℝ) ^ ((3 : ℝ) / 2))⁻¹ := by
      have hnat : ((q : ℝ) ^ 3) ≤ 16 * (Nat.totient q : ℝ) ^ 4 := by
        exact_mod_cast cube_le_sixteen_mul_totient_pow_four hq
      have hsq : ((q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (q : ℝ) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq_pos.le]
        norm_num
      have hroot : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (Nat.totient q : ℝ) ^ 2 := by
        have hsq_le : ((q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ (4 * (Nat.totient q : ℝ) ^ 2) ^ 2 := by
          rw [hsq]
          linarith [show (4 * (Nat.totient q : ℝ) ^ 2) ^ 2 = 16 * (Nat.totient q : ℝ) ^ 4 by ring]
        have hr := Real.sqrt_le_sqrt hsq_le
        rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hr
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    exact h1.trans h2

/-- Absolute summability of the ternary singular series `∑_q |μ(q) c_q(n) / φ(q)^3|`. -/
theorem summable_ternarySingularTerm (n : ℕ) :
    Summable (ternarySingularTerm n) := by
  have hdom : Summable (fun q : ℕ => 4 * ((q : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < (3 : ℝ) / 2)).mul_left 4
  exact Summable.of_norm_bounded hdom fun q => by
    simpa [Real.norm_eq_abs] using abs_ternarySingularTerm_le n q

lemma ternarySingularTerm_one (n : ℕ) : ternarySingularTerm n 1 = 1 := by
  simp [ternarySingularTerm, ramanujanSum_one]

lemma ternarySingularTerm_prime {p : ℕ} (hp : Nat.Prime p) (n : ℕ) :
    1 + ternarySingularTerm n p = ternaryLocalFactor n p := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have htot : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  simp only [ternarySingularTerm, ternaryLocalFactor, hp_ne, ↓reduceIte,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one, htot]
  have hram := ramanujanSum_prime_pow hp le_rfl n
  simp only [pow_one] at hram
  by_cases hpn : p ∣ n
  · simp only [hpn, ↓reduceIte]
    have hgcd : Nat.gcd p n = p := Nat.gcd_eq_left hpn
    rw [hgcd, Nat.div_self hp.pos] at hram
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Nat.totient_one,
      Nat.cast_one, div_one] at hram
    have hre : (ramanujanSum p n).re = (p : ℝ) - 1 := by
      rw [hram, Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
      simp
    rw [hre]
    field_simp [hp1_pos.ne']
    ring
  · simp only [hpn, ↓reduceIte]
    have hcop : Nat.Coprime p n := (hp.coprime_iff_not_dvd).mpr hpn
    rw [hcop.gcd_eq_one, Nat.div_one, ArithmeticFunction.moebius_apply_prime hp] at hram
    have htot_ne : (Nat.totient p : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hp.pos).ne'
    have hre : (ramanujanSum p n).re = -1 := by
      rw [hram, Int.cast_neg, Int.cast_one, neg_one_mul, neg_div, div_self htot_ne]
      simp
    rw [hre]
    field_simp [hp1_pos.ne']

lemma ternarySingularTerm_mul_coprime {q₁ q₂ : ℕ} (h1 : 1 ≤ q₁) (h2 : 1 ≤ q₂)
    (hcop : Nat.Coprime q₁ q₂) (n : ℕ) :
    ternarySingularTerm n (q₁ * q₂) = ternarySingularTerm n q₁ * ternarySingularTerm n q₂ := by
  have h12 : q₁ * q₂ ≠ 0 := (Nat.mul_pos h1 h2).ne'
  simp only [ternarySingularTerm, h12, show q₁ ≠ 0 by omega, show q₂ ≠ 0 by omega, ↓reduceIte]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    Nat.totient_mul hcop, ramanujanSum_mul_coprime h1 h2 hcop n]
  have him1 := ramanujanSum_im_eq_zero h1 n
  have him2 := ramanujanSum_im_eq_zero h2 n
  rw [Complex.mul_re, him1, him2, mul_zero, sub_zero]
  push_cast
  ring

/-- Exact finite Euler product for the ternary singular series over divisors of `P(z)`. -/
theorem sum_divisors_primorial_ternarySingularTerm (n z : ℕ) :
    ∑ q ∈ (Arith4Ext.SieveCharacters.primorial z).divisors, ternarySingularTerm n q =
      ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ternaryLocalFactor n p := by
  unfold Arith4Ext.SieveCharacters.primorial
  have hprimes : ∀ p ∈ (Finset.Icc 1 z).filter Nat.Prime, Nat.Prime p :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  generalize (Finset.Icc 1 z).filter Nat.Prime = S at hprimes ⊢
  classical
  induction S using Finset.induction_on with
  | empty => simp [ternarySingularTerm_one]
  | @insert a s ha ih =>
    have ha_p := hprimes a (Finset.mem_insert_self a s)
    have hs_p : ∀ p ∈ s, Nat.Prime p := fun p hp => hprimes p (Finset.mem_insert_of_mem hp)
    set M := ∏ p ∈ s, p
    have hM_pos : 1 ≤ M := Finset.prod_pos fun p hp => (hs_p p hp).pos
    have hcop : Nat.Coprime a M :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs_p p hp)).mpr (fun h => ha (h ▸ hp))
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Arith4Ext.SieveCharacters.divisors_prime_mul_of_coprime ha_p (by omega : M ≠ 0) hcop,
      Finset.sum_union (Arith4Ext.SieveCharacters.disjoint_divisors_image_prime_mul ha_p hcop),
      Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left ha_p.pos h)]
    have himg : ∑ q ∈ M.divisors, ternarySingularTerm n (a * q) =
        ternarySingularTerm n a * ∑ q ∈ M.divisors, ternarySingularTerm n q := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq_pos : 1 ≤ q := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hq) hM_pos
      have hcop_aq : Nat.Coprime a q := hcop.coprime_dvd_right (Nat.dvd_of_mem_divisors hq)
      exact ternarySingularTerm_mul_coprime ha_p.one_le hq_pos hcop_aq n
    rw [himg, ← one_add_mul, ternarySingularTerm_prime ha_p n, ih hs_p]

lemma bernoulli_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hx0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self x t)
    have hx1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x t)
    have ht := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hsum_nonneg : 0 ≤ ∑ i ∈ t, a i := Finset.sum_nonneg fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    calc 1 - (a x + ∑ i ∈ t, a i)
        ≤ (1 - a x) * (1 - ∑ i ∈ t, a i) := by nlinarith
      _ ≤ (1 - a x) * ∏ i ∈ t, (1 - a i) :=
          mul_le_mul_of_nonneg_left ht (by linarith)

lemma prod_ternaryLocalFactor_ge_one {n z : ℕ} (hn : Odd n) (hz : 2 ≤ z) :
    1 ≤ ∏ p ∈ (Finset.Icc 1 z).filter Nat.Prime, ternaryLocalFactor n p := by
  have h2_mem : 2 ∈ (Finset.Icc 1 z).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by norm_num, hz⟩, Nat.prime_two⟩
  rw [← Finset.mul_prod_erase _ _ h2_mem]
  have h2_ndvd : ¬ 2 ∣ n := fun h => by
    rcases hn with ⟨k, rfl⟩
    omega
  have hf2 : ternaryLocalFactor n 2 = 2 := by
    simp only [ternaryLocalFactor, h2_ndvd, ↓reduceIte]
    norm_num
  rw [hf2]
  set S := ((Finset.Icc 1 z).filter Nat.Prime).erase 2
  have hterm_ge : ∀ p ∈ S, 1 - ((p : ℝ) - 1)⁻¹ ^ 2 ≤ ternaryLocalFactor n p := by
    intro p hp
    unfold ternaryLocalFactor
    split_ifs
    · exact le_rfl
    · have hp_p := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_p.two_le
        linarith
      have h1 : 0 ≤ ((p : ℝ) - 1)⁻¹ ^ 2 := by positivity
      have h2 : 0 ≤ ((p : ℝ) - 1)⁻¹ ^ 3 := by positivity
      linarith
  have hprod_ge : ∏ p ∈ S, (1 - ((p : ℝ) - 1)⁻¹ ^ 2) ≤ ∏ p ∈ S, ternaryLocalFactor n p := by
    refine Finset.prod_le_prod (fun p hp => ?_) hterm_ge
    have hp_p := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
    have hne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 3 ≤ p := by have := hp_p.two_le; omega
      exact_mod_cast this
    have hinv : ((p : ℝ) - 1)⁻¹ ≤ 1 / 2 := by
      rw [← one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hsq : ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 / 4 := by nlinarith [inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)]
    linarith
  have hbern : 1 - ∑ p ∈ S, ((p : ℝ) - 1)⁻¹ ^ 2 ≤ ∏ p ∈ S, (1 - ((p : ℝ) - 1)⁻¹ ^ 2) := by
    refine bernoulli_prod_one_sub S _ (fun _ _ => by positivity) fun p hp => ?_
    have hp_p := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
    have hne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 3 ≤ p := by have := hp_p.two_le; omega
      exact_mod_cast this
    have hinv : ((p : ℝ) - 1)⁻¹ ≤ 1 := by
      rw [← one_div, div_le_one (by linarith)]; linarith
    nlinarith [inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)]
  -- Bound `∑_{p ∈ S} 1 / (p - 1)^2 ≤ 1/2` via `p - 1 = 2 * j` (`j ≥ 1`)
  have hsum_le : ∑ p ∈ S, ((p : ℝ) - 1)⁻¹ ^ 2 ≤ 1 / 2 := by
    have hmaps : S.image (fun p => (p - 1) / 2) ⊆ Finset.Icc 1 z := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨p, hp, rfl⟩
      have hp_mem := Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)
      have hp_Icc := Finset.mem_Icc.mp hp_mem.1
      have hne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
      have hp3 : 3 ≤ p := by have := hp_mem.2.two_le; omega
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hinj : Set.InjOn (fun p => (p - 1) / 2) ↑S := by
      intro p₁ h1 p₂ h2 heq
      dsimp only at heq
      have hp1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp h1))).2
      have hp2 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_coe.mp h2))).2
      have hne1 : p₁ ≠ 2 := (Finset.mem_erase.mp (Finset.mem_coe.mp h1)).1
      have hne2 : p₂ ≠ 2 := (Finset.mem_erase.mp (Finset.mem_coe.mp h2)).1
      have hodd1 : Odd p₁ := hp1.odd_of_ne_two hne1
      have hodd2 : Odd p₂ := hp2.odd_of_ne_two hne2
      rcases hodd1 with ⟨k₁, rfl⟩
      rcases hodd2 with ⟨k₂, rfl⟩
      omega
    have hreidx : ∑ p ∈ S, ((p : ℝ) - 1)⁻¹ ^ 2 =
        (1 / 4 : ℝ) * ∑ j ∈ S.image (fun p : ℕ => (p - 1) / 2), ((j : ℝ) ^ 2)⁻¹ := by
      rw [Finset.sum_image (f := fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) hinj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_p := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp)).2
      have hne2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
      rcases hp_p.odd_of_ne_two hne2 with ⟨k, rfl⟩
      have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
      rw [hdiv]
      push_cast
      have hsimp : (2 * (k : ℝ) + 1 - 1) = 2 * (k : ℝ) := by ring
      rw [hsimp, mul_inv, mul_pow]
      ring
    have hinv_sq : ∑ j ∈ Finset.Icc 1 z, ((j : ℝ) ^ 2)⁻¹ ≤ 2 := by
      have h1 : 1 ∈ Finset.Icc 1 z := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have hsplit : Finset.Icc 1 z = insert 1 (Finset.Icc 2 z) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp)]
      have h2 : ∑ j ∈ Finset.Icc 2 z, ((j : ℝ) ^ 2)⁻¹ ≤
          ∑ j ∈ Finset.Icc 2 z, ((j : ℝ) * ((j : ℝ) - 1))⁻¹ := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        exact inv_anti₀ (by nlinarith) (by nlinarith)
      have htele : ∀ M : ℕ, 1 ≤ M →
          ∑ j ∈ Finset.Icc 2 M, ((j : ℝ) * ((j : ℝ) - 1))⁻¹ = 1 - (M : ℝ)⁻¹ := by
        intro M hM
        induction M, hM using Nat.le_induction with
        | base => simp
        | succ M hM ihM =>
          have hI : Finset.Icc 2 (M + 1) = insert (M + 1) (Finset.Icc 2 M) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.sum_insert (by simp), ihM]
          have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
          have hM1_pos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
          push_cast
          field_simp [hM_pos.ne', hM1_pos.ne']
          ring
      rw [htele z (by omega)] at h2
      have hinv_nn : 0 ≤ (z : ℝ)⁻¹ := by positivity
      norm_num at h2 ⊢
      linarith
    rw [hreidx]
    calc (1 / 4 : ℝ) * ∑ j ∈ S.image (fun p : ℕ => (p - 1) / 2), ((j : ℝ) ^ 2)⁻¹
        ≤ (1 / 4 : ℝ) * ∑ j ∈ Finset.Icc 1 z, ((j : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hmaps fun _ _ _ => by positivity)
            (by norm_num)
      _ ≤ (1 / 4 : ℝ) * 2 := mul_le_mul_of_nonneg_left hinv_sq (by norm_num)
      _ = 1 / 2 := by norm_num
  linarith

/-- **Ternary Odd-Goldbach Singular Series Positivity & Explicit Lower Bound**:
For every odd `n : ℕ`, the infinite ternary singular series
`𝔖₃(n) = ∑' q, μ(q) c_q(n) / φ(q)^3` converges absolutely and satisfies `1 ≤ 𝔖₃(n)`. -/
theorem ternarySingularSeries_ge_one {n : ℕ} (hn : Odd n) :
    1 ≤ ∑' q : ℕ, ternarySingularTerm n q := by
  -- Show `∑_{q ∈ (primorial z).divisors} ternarySingularTerm n q → ∑' q, ternarySingularTerm n q`
  have hsum := summable_ternarySingularTerm n
  have hlim : Filter.Tendsto
      (fun z : ℕ => ∑ q ∈ (Arith4Ext.SieveCharacters.primorial z).divisors, ternarySingularTerm n q)
      Filter.atTop (nhds (∑' q : ℕ, ternarySingularTerm n q)) := by
    have hhas := hsum.hasSum
    change Filter.Tendsto (fun s : Finset ℕ => ∑ b ∈ s, ternarySingularTerm n b)
      Filter.atTop (nhds (∑' q : ℕ, ternarySingularTerm n q)) at hhas
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendsto_atTop] at hhas
    rcases hhas ε hε with ⟨s, hs⟩
    refine ⟨s.sup id, fun z hz => ?_⟩
    -- Let `t := s ∪ (primorial z).divisors`: then `s ⊆ t` and `∑_{q ∈ t} = ∑_{q ∈ (primorial z).divisors}`!
    set t := s ∪ (Arith4Ext.SieveCharacters.primorial z).divisors
    have ht_eq : ∑ q ∈ (Arith4Ext.SieveCharacters.primorial z).divisors, ternarySingularTerm n q =
        ∑ q ∈ t, ternarySingularTerm n q := by
      refine Finset.sum_subset Finset.subset_union_right fun q hqt hqnot => ?_
      have hqs : q ∈ s := (Finset.mem_union.mp hqt).resolve_right hqnot
      by_cases hq0 : q = 0
      · simp [ternarySingularTerm, hq0]
      · by_cases hsq : Squarefree q
        · exfalso
          apply hqnot
          have hq_le : q ≤ z := (Finset.le_sup (f := id) hqs).trans hz
          exact Nat.mem_divisors.mpr
            ⟨Arith4Ext.SieveCharacters.squarefree_dvd_primorial hsq hq_le,
             Arith4Ext.SieveCharacters.primorial_ne_zero z⟩
        · simp [ternarySingularTerm, hq0,
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    rw [ht_eq]
    exact hs t Finset.subset_union_left
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with z hz
  rw [sum_divisors_primorial_ternarySingularTerm]
  exact prod_ternaryLocalFactor_ge_one hn hz

/-! ## Section 3: Weyl Quadratic Sum, Hua's `L^4` Bound & Bilinear Type I–II Minor-Arc Bounds -/

/-- Distance from a real number `x` to the nearest integer: `‖x‖_ℝ/ℤ = |x - round x|`. -/
def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := abs_nonneg _

lemma distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := abs_sub_round x

lemma distToInt_le_abs_sub_int (x : ℝ) (m : ℤ) : distToInt x ≤ |x - (m : ℝ)| := by
  by_cases hm : m = round x
  · subst hm; exact le_rfl
  · have hge1 : (1 : ℝ) ≤ |(m : ℝ) - (round x : ℝ)| := by
      have hne : m - round x ≠ 0 := sub_ne_zero.mpr hm
      have hz : (1 : ℤ) ≤ |m - round x| := Int.one_le_abs hne
      exact_mod_cast hz
    have htri : |(m : ℝ) - (round x : ℝ)| ≤ |x - (m : ℝ)| + |x - (round x : ℝ)| := by
      have hsub : (m : ℝ) - (round x : ℝ) = (x - (round x : ℝ)) - (x - (m : ℝ)) := by ring
      rw [hsub]
      calc |(x - (round x : ℝ)) - (x - (m : ℝ))|
          ≤ |x - (round x : ℝ)| + |x - (m : ℝ)| := abs_sub _ _
        _ = |x - (m : ℝ)| + |x - (round x : ℝ)| := add_comm _ _
    have hhalf := distToInt_le_half x
    unfold distToInt at hhalf ⊢
    linarith

lemma distToInt_add_int (x : ℝ) (m : ℤ) : distToInt (x + (m : ℝ)) = distToInt x := by
  refine le_antisymm ?_ ?_
  · calc distToInt (x + (m : ℝ))
        ≤ |(x + (m : ℝ)) - (((round x + m : ℤ) : ℝ))| := distToInt_le_abs_sub_int _ _
      _ = |x - (round x : ℝ)| := by push_cast; ring_nf
  · calc distToInt x
        ≤ |x - (((round (x + (m : ℝ)) - m : ℤ) : ℝ))| := distToInt_le_abs_sub_int _ _
      _ = |(x + (m : ℝ)) - (round (x + (m : ℝ)) : ℝ)| := by push_cast; ring_nf

lemma distToInt_neg (x : ℝ) : distToInt (-x) = distToInt x := by
  refine le_antisymm ?_ ?_
  · calc distToInt (-x)
        ≤ |(-x) - (((-round x : ℤ) : ℝ))| := distToInt_le_abs_sub_int _ _
      _ = |-(x - (round x : ℝ))| := by push_cast; ring_nf
      _ = distToInt x := abs_neg _
  · calc distToInt x
        ≤ |x - (((-round (-x) : ℤ) : ℝ))| := distToInt_le_abs_sub_int _ _
      _ = |-((-x) - (round (-x) : ℝ))| := by push_cast; ring_nf
      _ = distToInt (-x) := abs_neg _

lemma distToInt_sub_ge (x y : ℝ) : distToInt x - |y| ≤ distToInt (x + y) := by
  have h1 : distToInt x ≤ |x - (round (x + y) : ℝ)| := distToInt_le_abs_sub_int x (round (x + y))
  have h2 : |x - (round (x + y) : ℝ)| ≤ distToInt (x + y) + |y| := by
    have heq : x - (round (x + y) : ℝ) = (x + y - (round (x + y) : ℝ)) - y := by ring
    rw [heq]
    exact abs_sub _ _
  linarith

/-- Safe truncated reciprocal distance `min(N, (2 ‖θ‖_ℝ/ℤ)⁻¹)` (evaluating to `N` when `‖θ‖ = 0`). -/
def minRecipDist (N θ : ℝ) : ℝ :=
  if distToInt θ = 0 then N else min N (2 * distToInt θ)⁻¹

lemma minRecipDist_nonneg {N : ℝ} (hN : 0 ≤ N) (θ : ℝ) : 0 ≤ minRecipDist N θ := by
  unfold minRecipDist
  split_ifs
  · exact hN
  · exact le_min hN (inv_nonneg.mpr (by linarith [distToInt_nonneg θ]))

lemma minRecipDist_le (N θ : ℝ) : minRecipDist N θ ≤ N := by
  unfold minRecipDist
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

lemma minRecipDist_le_inv_of_pos {N θ c : ℝ} (hc : 0 < c) (hge : c ≤ distToInt θ) :
    minRecipDist N θ ≤ (2 * c)⁻¹ := by
  have hne : distToInt θ ≠ 0 := by linarith
  simp only [minRecipDist, hne, ↓reduceIte]
  exact (min_le_right _ _).trans (inv_anti₀ (by linarith) (by linarith))

lemma minRecipDist_mono {N₁ N₂ : ℝ} (h : N₁ ≤ N₂) (θ : ℝ) :
    minRecipDist N₁ θ ≤ minRecipDist N₂ θ := by
  unfold minRecipDist
  split_ifs
  · exact h
  · exact min_le_min_right _ h

lemma minRecipDist_neg (N θ : ℝ) : minRecipDist N (-θ) = minRecipDist N θ := by
  simp [minRecipDist, distToInt_neg]

lemma minRecipDist_add_int (N θ : ℝ) (m : ℤ) :
    minRecipDist N (θ + (m : ℝ)) = minRecipDist N θ := by
  simp [minRecipDist, distToInt_add_int]

lemma four_mul_distToInt_le_norm_e_sub_one (θ : ℝ) :
    4 * distToInt θ ≤ ‖e θ - 1‖ := by
  set δ : ℝ := θ - (round θ : ℝ)
  have hθ : e θ = e δ := by
    have : θ = δ + (round θ : ℝ) := by dsimp [δ]; ring
    rw [this, e_add_int]
  rw [hθ]
  have hsin_eq : e δ - 1 = e (δ / 2) * (2 * Complex.I * ((Real.sin (Real.pi * δ) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sin, Complex.sin]
    have h1 : e (δ / 2) * e (δ / 2) = e δ := by rw [← e_add]; congr 1; ring
    have h2 : e (δ / 2) * e (-(δ / 2)) = 1 := by rw [← e_add]; simp [e_zero]
    have hexp1 : Complex.exp (((Real.pi * δ : ℝ) : ℂ) * Complex.I) = e (δ / 2) := by
      unfold e; congr 1; push_cast; ring
    have hexp2 : Complex.exp (-((Real.pi * δ : ℝ) : ℂ) * Complex.I) = e (-(δ / 2)) := by
      unfold e; congr 1; push_cast; ring
    rw [hexp1, hexp2]
    have htrig : 2 * Complex.I * ((e (-(δ / 2)) - e (δ / 2)) * Complex.I / 2) =
        e (δ / 2) - e (-(δ / 2)) := by
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      calc 2 * Complex.I * ((e (-(δ / 2)) - e (δ / 2)) * Complex.I / 2)
          = (e (-(δ / 2)) - e (δ / 2)) * Complex.I ^ 2 := by ring
        _ = (e (-(δ / 2)) - e (δ / 2)) * (-1) := by rw [hI2]
        _ = e (δ / 2) - e (-(δ / 2)) := by ring
    rw [htrig]
    calc e δ - 1
        = e (δ / 2) * e (δ / 2) - e (δ / 2) * e (-(δ / 2)) := by rw [h1, h2]
      _ = e (δ / 2) * (e (δ / 2) - e (-(δ / 2))) := by ring
  rw [hsin_eq, norm_mul, norm_e, one_mul, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one]
  have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2norm, Real.norm_eq_abs]
  have hδ_le : |δ| ≤ 1 / 2 := abs_sub_round θ
  have hpi_le : Real.pi * |δ| ≤ Real.pi / 2 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  have habs_sin : |Real.sin (Real.pi * δ)| = Real.sin (Real.pi * |δ|) := by
    by_cases h0 : 0 ≤ δ
    · have hpi_le' : Real.pi * δ ≤ Real.pi / 2 := by rwa [abs_of_nonneg h0] at hpi_le
      rw [abs_of_nonneg h0, abs_of_nonneg]
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    · have hlt : δ < 0 := lt_of_not_ge h0
      have hneg : 0 ≤ -δ := by linarith
      have hpi_le' : Real.pi * (-δ) ≤ Real.pi / 2 := by rwa [abs_of_neg hlt] at hpi_le
      have hsin_nn : 0 ≤ Real.sin (Real.pi * (-δ)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
      rw [abs_of_neg hlt, show Real.pi * δ = -(Real.pi * (-δ)) by ring, Real.sin_neg, abs_neg,
        abs_of_nonneg hsin_nn]
  rw [habs_sin]
  have hmul := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * |δ|) hpi_le
  have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have h2δ : 2 * |δ| ≤ Real.sin (Real.pi * |δ|) := by
    have heq : 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| := by field_simp [hpi_ne]
    rwa [heq] at hmul
  change 4 * |δ| ≤ 2 * Real.sin (Real.pi * |δ|)
  linarith

/-- Geometric-series bound for exponential sums over an interval `Icc a b`:
`‖∑_{n=a}^b e(n θ)‖ ≤ min(b - a + 1, (2 ‖θ‖_ℝ/ℤ)⁻¹)`. -/
theorem norm_sum_e_Icc_le_minRecipDist (a b : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖ ≤
      minRecipDist ((Finset.Icc a b).card : ℝ) θ := by
  have htriv : ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖ ≤ ((Finset.Icc a b).card : ℝ) := by
    calc ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖
        ≤ ∑ n ∈ Finset.Icc a b, ‖e ((n : ℝ) * θ)‖ := norm_sum_le _ _
      _ = ((Finset.Icc a b).card : ℝ) := by simp [norm_e]
  unfold minRecipDist
  by_cases h0 : distToInt θ = 0
  · simp only [h0, ↓reduceIte]; exact htriv
  · simp only [h0, ↓reduceIte]
    refine le_min htriv ?_
    have hpos : 0 < distToInt θ := lt_of_le_of_ne (distToInt_nonneg θ) (Ne.symm h0)
    by_cases hab : a ≤ b
    · have htele : ∀ m : ℕ, a ≤ m →
          (e θ - 1) * ∑ n ∈ Finset.Icc a m, e ((n : ℝ) * θ) =
            e (((m + 1 : ℕ) : ℝ) * θ) - e ((a : ℝ) * θ) := by
        intro m hm
        induction m, hm using Nat.le_induction with
        | base =>
          simp only [Finset.Icc_self, Finset.sum_singleton]
          rw [sub_mul, one_mul, ← e_add]
          have harg : θ + (a : ℝ) * θ = ((a + 1 : ℕ) : ℝ) * θ := by push_cast; ring
          rw [harg]
        | succ m hm ihm =>
          have hI : Finset.Icc a (m + 1) = insert (m + 1) (Finset.Icc a m) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.sum_insert (by simp), mul_add, ihm]
          have hstep : (e θ - 1) * e (((m + 1 : ℕ) : ℝ) * θ) =
              e (((m + 2 : ℕ) : ℝ) * θ) - e (((m + 1 : ℕ) : ℝ) * θ) := by
            rw [sub_mul, one_mul, ← e_add]
            have harg : θ + ((m + 1 : ℕ) : ℝ) * θ = ((m + 2 : ℕ) : ℝ) * θ := by push_cast; ring
            rw [harg]
          rw [hstep]
          ring
      have hnorm_prod : ‖e θ - 1‖ * ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖ ≤ 2 := by
        rw [← norm_mul, htele b hab]
        calc ‖e (((b + 1 : ℕ) : ℝ) * θ) - e ((a : ℝ) * θ)‖
            ≤ ‖e (((b + 1 : ℕ) : ℝ) * θ)‖ + ‖e ((a : ℝ) * θ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_e, norm_e]; norm_num
      have hlow := four_mul_distToInt_le_norm_e_sub_one θ
      have h4 : 4 * distToInt θ * ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖ ≤ 2 := by
        calc 4 * distToInt θ * ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖
            ≤ ‖e θ - 1‖ * ‖∑ n ∈ Finset.Icc a b, e ((n : ℝ) * θ)‖ :=
              mul_le_mul_of_nonneg_right hlow (norm_nonneg _)
          _ ≤ 2 := hnorm_prod
      rw [← one_div, le_div_iff₀ (by linarith)]
      linarith
    · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hab
      rw [hempty, Finset.sum_empty, norm_zero]
      exact inv_nonneg.mpr (by linarith)

lemma sum_inv_Icc_le_log_add_one {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ ≤ Real.log (n : ℝ) + 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ihm =>
    have hI : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hI, Finset.sum_insert (by simp)]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hm1_pos hm_pos)
    rw [Real.log_div hm1_pos.ne' hm_pos.ne', inv_div] at hlog
    have hdiff : 1 - (m : ℝ) / ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ)⁻¹ := by
      push_cast; field_simp [hm1_pos.ne']; ring
    rw [hdiff] at hlog
    push_cast at hlog ⊢
    linarith

lemma distToInt_div_nat {s q : ℕ} (hq : 1 ≤ q) (hs : s < q) :
    distToInt ((s : ℝ) / (q : ℝ)) = ((min s (q - s) : ℕ) : ℝ) / (q : ℝ) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  by_cases hhalf : 2 * s ≤ q
  · have hmin : min s (q - s) = s := min_eq_left (by omega)
    rw [hmin]
    have hle : (s : ℝ) / (q : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hq_pos (by norm_num)]
      exact_mod_cast (by omega : s * 2 ≤ 1 * q)
    refine le_antisymm ?_ ?_
    · calc distToInt ((s : ℝ) / (q : ℝ))
          ≤ |(s : ℝ) / (q : ℝ) - ((0 : ℤ) : ℝ)| := distToInt_le_abs_sub_int _ 0
        _ = (s : ℝ) / (q : ℝ) := by simp [abs_of_nonneg (div_nonneg (Nat.cast_nonneg s) hq_pos.le)]
    · by_cases hr0 : round ((s : ℝ) / (q : ℝ)) = 0
      · unfold distToInt; rw [hr0]; simp [abs_of_nonneg (div_nonneg (Nat.cast_nonneg s) hq_pos.le)]
      · by_cases hr1 : round ((s : ℝ) / (q : ℝ)) = 1
        · unfold distToInt; rw [hr1]
          have h1 : (s : ℝ) / (q : ℝ) ≤ 1 := by linarith
          rw [Int.cast_one, abs_of_nonpos (by linarith)]
          linarith
        · have hge2 : (1 : ℝ) ≤ |(s : ℝ) / (q : ℝ) - (round ((s : ℝ) / (q : ℝ)) : ℝ)| := by
            have hr := round ((s : ℝ) / (q : ℝ))
            have hcases : round ((s : ℝ) / (q : ℝ)) ≤ -1 ∨ 2 ≤ round ((s : ℝ) / (q : ℝ)) := by omega
            rcases hcases with hneg | hpos2
            · have hneg_r : (round ((s : ℝ) / (q : ℝ)) : ℝ) ≤ -1 := by exact_mod_cast hneg
              have hs_nn : (0 : ℝ) ≤ (s : ℝ) / (q : ℝ) := div_nonneg (Nat.cast_nonneg s) hq_pos.le
              rw [abs_of_nonneg (by linarith)]; linarith
            · have hpos_r : (2 : ℝ) ≤ (round ((s : ℝ) / (q : ℝ)) : ℝ) := by exact_mod_cast hpos2
              rw [abs_of_nonpos (by linarith)]; linarith
          unfold distToInt; linarith
  · have hmin : min s (q - s) = q - s := min_eq_right (by omega)
    rw [hmin]
    have hsub_r : ((q - s : ℕ) : ℝ) / (q : ℝ) = 1 - (s : ℝ) / (q : ℝ) := by
      rw [Nat.cast_sub hs.le, sub_div, div_self hq_pos.ne']
    rw [hsub_r]
    have hgt : (1 / 2 : ℝ) < (s : ℝ) / (q : ℝ) := by
      rw [div_lt_div_iff₀ (by norm_num) hq_pos]
      exact_mod_cast (by omega : 1 * q < s * 2)
    have hlt1 : (s : ℝ) / (q : ℝ) < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast hs)
    refine le_antisymm ?_ ?_
    · calc distToInt ((s : ℝ) / (q : ℝ))
          ≤ |(s : ℝ) / (q : ℝ) - ((1 : ℤ) : ℝ)| := distToInt_le_abs_sub_int _ 1
        _ = 1 - (s : ℝ) / (q : ℝ) := by rw [Int.cast_one, abs_of_nonpos (by linarith)]; ring
    · by_cases hr1 : round ((s : ℝ) / (q : ℝ)) = 1
      · unfold distToInt; rw [hr1, Int.cast_one, abs_of_nonpos (by linarith)]; ring_nf; exact le_rfl
      · by_cases hr0 : round ((s : ℝ) / (q : ℝ)) = 0
        · unfold distToInt; rw [hr0, Int.cast_zero, sub_zero, abs_of_nonneg (by linarith)]; linarith
        · have hcases : round ((s : ℝ) / (q : ℝ)) ≤ -1 ∨ 2 ≤ round ((s : ℝ) / (q : ℝ)) := by omega
          unfold distToInt
          rcases hcases with hneg | hpos2
          · have hneg_r : (round ((s : ℝ) / (q : ℝ)) : ℝ) ≤ -1 := by exact_mod_cast hneg
            rw [abs_of_nonneg (by linarith)]; linarith
          · have hpos_r : (2 : ℝ) ≤ (round ((s : ℝ) / (q : ℝ)) : ℝ) := by exact_mod_cast hpos2
            rw [abs_of_nonpos (by linarith)]; linarith

/-- **Vinogradov Linear Reciprocal-Distance Sum Bound**:
For `1 ≤ q`, `gcd(a, q) = 1`, `|α - a/q| ≤ 2/q^2`, and `0 ≤ N`,
`∑_{m=1}^M min(N, (2 ‖α m‖)⁻¹) ≤ (M / q + 1) * (5 N + 2 q (log q + 1))`. -/
theorem vinogradov_minRecipDist_sum {α : ℝ} {a : ℤ} {q M : ℕ} {N : ℝ}
    (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 2 / (q : ℝ) ^ 2)
    (hN : 0 ≤ N) :
    ∑ m ∈ Finset.Icc 1 M, minRecipDist N (α * (m : ℝ)) ≤
      ((M : ℝ) / (q : ℝ) + 1) * (5 * N + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- Step 1: Bound any single block `r ∈ range q` at shift `j * q`:
  have hblock : ∀ j : ℕ,
      ∑ r ∈ Finset.range q, minRecipDist N (α * ((j * q + r : ℕ) : ℝ)) ≤
        5 * N + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1) := by
    intro j
    set β : ℝ := α - (a : ℝ) / (q : ℝ)
    set t : ℤ := round ((q : ℝ) * (β * ((j * q : ℕ) : ℝ)))
    have : NeZero q := ⟨by omega⟩
    -- Residue permutation `r ↦ ((a * r + t : ZMod q)).val`
    set perm : ℕ → ℕ := fun r => ((a * (r : ℤ) + t : ℤ) : ZMod q).val
    have hperm_lt : ∀ r ∈ Finset.range q, perm r ∈ Finset.range q := fun r _ =>
      Finset.mem_range.mpr (ZMod.val_lt _)
    have hperm_inj : Set.InjOn perm ↑(Finset.range q) := by
      intro r₁ h1 r₂ h2 heq
      have h1lt : r₁ < q := Finset.mem_range.mp (Finset.mem_coe.mp h1)
      have h2lt : r₂ < q := Finset.mem_range.mp (Finset.mem_coe.mp h2)
      have hmod : ((a * (r₁ : ℤ) + t : ℤ) : ZMod q) = ((a * (r₂ : ℤ) + t : ℤ) : ZMod q) :=
        ZMod.val_injective q heq
      have hdiff0 : ((a * ((r₁ : ℤ) - (r₂ : ℤ)) : ℤ) : ZMod q) = 0 := by
        have hsub : (((a * (r₁ : ℤ) + t) - (a * (r₂ : ℤ) + t) : ℤ) : ZMod q) = 0 := by
          rw [Int.cast_sub, hmod, sub_self]
        have halg : (a * (r₁ : ℤ) + t) - (a * (r₂ : ℤ) + t) = a * ((r₁ : ℤ) - (r₂ : ℤ)) := by ring
        rwa [halg] at hsub
      have hdvd : (q : ℤ) ∣ a * ((r₁ : ℤ) - (r₂ : ℤ)) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hdiff0
      have hcop_z : IsCoprime (q : ℤ) a := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact_mod_cast hcop
      have hdvd_diff : (q : ℤ) ∣ (r₁ : ℤ) - (r₂ : ℤ) :=
        hcop_z.dvd_of_dvd_mul_left hdvd
      rcases hdvd_diff with ⟨c, hc⟩
      have hc0 : c = 0 := by
        have hlt1 : -(q : ℤ) < (q : ℤ) * c := by omega
        have hlt2 : (q : ℤ) * c < (q : ℤ) := by omega
        nlinarith
      rw [hc0, mul_zero] at hc
      omega
    -- Bound each term `minRecipDist N (α * (j * q + r))` in terms of `perm r`
    have hterm_le : ∀ r ∈ Finset.range q,
        minRecipDist N (α * ((j * q + r : ℕ) : ℝ)) ≤
          if min (perm r) (q - perm r) ≤ 2 then N
          else (q : ℝ) / (((min (perm r) (q - perm r) - 2 : ℕ) : ℝ)) := by
      intro r hr
      have hr_lt : r < q := Finset.mem_range.mp hr
      split_ifs with hsmall
      · exact minRecipDist_le N _
      · set s := perm r
        have hs_lt : s < q := ZMod.val_lt _
        set u := min s (q - s)
        have hu3 : 3 ≤ u := by omega
        -- Relate `α * (j * q + r)` to `s / q + δ` with `|δ| ≤ 5 / (2 * q)`
        have hdiv_z : (q : ℤ) ∣ (a * (r : ℤ) + t) - (s : ℤ) := by
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
          rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self]
        rcases hdiv_z with ⟨w, hw⟩
        set δ₁ : ℝ := β * ((j * q : ℕ) : ℝ) - (t : ℝ) / (q : ℝ)
        set δ₂ : ℝ := β * (r : ℝ)
        have hδ1 : |δ₁| ≤ 1 / (2 * (q : ℝ)) := by
          have heq : δ₁ = ((q : ℝ) * (β * ((j * q : ℕ) : ℝ)) - (t : ℝ)) / (q : ℝ) := by
            dsimp [δ₁]; field_simp [hq_pos.ne']
          rw [heq, abs_div, abs_of_pos hq_pos]
          have hround : |(q : ℝ) * (β * ((j * q : ℕ) : ℝ)) - (t : ℝ)| ≤ 1 / 2 := abs_sub_round _
          rw [div_le_div_iff₀ hq_pos (by positivity)]
          nlinarith
        have hδ2 : |δ₂| ≤ 2 / (q : ℝ) := by
          dsimp [δ₂]
          rw [abs_mul, abs_of_nonneg (a := (r : ℝ)) (Nat.cast_nonneg r)]
          have hr_r : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hr_lt.le
          calc |β| * (r : ℝ) ≤ (2 / (q : ℝ) ^ 2) * (q : ℝ) :=
                mul_le_mul happrox hr_r (Nat.cast_nonneg r) (by positivity)
            _ = 2 / (q : ℝ) := by field_simp [hq_pos.ne']
        have hδ : |δ₁ + δ₂| ≤ 5 / (2 * (q : ℝ)) := by
          calc |δ₁ + δ₂| ≤ |δ₁| + |δ₂| := abs_add_le _ _
            _ ≤ 1 / (2 * (q : ℝ)) + 2 / (q : ℝ) := add_le_add hδ1 hδ2
            _ = 5 / (2 * (q : ℝ)) := by field_simp [hq_pos.ne']; ring
        have hdecomp : α * ((j * q + r : ℕ) : ℝ) =
            ((s : ℝ) / (q : ℝ) + (δ₁ + δ₂)) + (((a * (j : ℤ) + w : ℤ) : ℝ)) := by
          have hα : α = (a : ℝ) / (q : ℝ) + β := by dsimp [β]; ring
          have hw_r : (a : ℝ) * (r : ℝ) + (t : ℝ) = (s : ℝ) + (q : ℝ) * (w : ℝ) := by
            have hz : a * (r : ℤ) + t = (s : ℤ) + (q : ℤ) * w := by linarith
            exact_mod_cast hz
          dsimp [δ₁, δ₂]
          rw [hα]
          push_cast
          field_simp [hq_pos.ne']
          nlinarith
        have hdist_ge : (((u - 2 : ℕ) : ℝ)) / (2 * (q : ℝ)) ≤
            distToInt (α * ((j * q + r : ℕ) : ℝ)) := by
          rw [hdecomp, distToInt_add_int]
          have hsub := distToInt_sub_ge ((s : ℝ) / (q : ℝ)) (δ₁ + δ₂)
          rw [distToInt_div_nat hq hs_lt] at hsub
          have hu_cast : ((u - 2 : ℕ) : ℝ) = (u : ℝ) - 2 := by
            rw [Nat.cast_sub (by omega)]; norm_num
          have hu_r : (3 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu3
          rw [hu_cast]
          have hstep : ((u : ℝ) - 2) / (2 * (q : ℝ)) ≤ (u : ℝ) / (q : ℝ) - 5 / (2 * (q : ℝ)) := by
            have h1 : (u : ℝ) / (q : ℝ) - 5 / (2 * (q : ℝ)) = (2 * (u : ℝ) - 5) / (2 * (q : ℝ)) := by
              field_simp [hq_pos.ne']
            rw [h1]
            exact div_le_div_of_nonneg_right (by linarith) (by positivity)
          linarith
        have hc_pos : (0 : ℝ) < (((u - 2 : ℕ) : ℝ)) / (2 * (q : ℝ)) := by
          have : (0 : ℝ) < ((u - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < u - 2)
          positivity
        have hinv := minRecipDist_le_inv_of_pos (N := N) hc_pos hdist_ge
        have hsimp : (2 * ((((u - 2 : ℕ) : ℝ)) / (2 * (q : ℝ))))⁻¹ =
            (q : ℝ) / (((u - 2 : ℕ) : ℝ)) := by
          have hu2_ne : (((u - 2 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (by omega : u - 2 ≠ 0)
          field_simp [hq_pos.ne', hu2_ne]
        rwa [hsimp] at hinv
    -- Sum over `r ∈ range q`, reindex by bijection `perm : range q → range q`
    have hperm_img : (Finset.range q).image perm = Finset.range q := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro s hs
        rcases Finset.mem_image.mp hs with ⟨r, hr, rfl⟩
        exact hperm_lt r hr
      · rw [Finset.card_image_of_injOn hperm_inj]
    set g : ℕ → ℝ := fun s =>
      if min s (q - s) ≤ 2 then N else (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ))
    have hsum1 : ∑ r ∈ Finset.range q, minRecipDist N (α * ((j * q + r : ℕ) : ℝ)) ≤
        ∑ s ∈ Finset.range q, g s := by
      calc ∑ r ∈ Finset.range q, minRecipDist N (α * ((j * q + r : ℕ) : ℝ))
          ≤ ∑ r ∈ Finset.range q, g (perm r) := Finset.sum_le_sum hterm_le
        _ = ∑ s ∈ (Finset.range q).image perm, g s := (Finset.sum_image hperm_inj).symm
        _ = ∑ s ∈ Finset.range q, g s := by rw [hperm_img]
    -- Split `range q` into `min s (q - s) ≤ 2` (card ≤ 5) and `min s (q - s) ≥ 3`
    have hsum_split : ∑ s ∈ Finset.range q, g s =
        (∑ s ∈ (Finset.range q).filter (fun s => min s (q - s) ≤ 2), N) +
        (∑ s ∈ (Finset.range q).filter (fun s => ¬ min s (q - s) ≤ 2),
          (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ))) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun s => min s (q - s) ≤ 2) g]
      congr 1
      · refine Finset.sum_congr rfl fun s hs => by
          have h := (Finset.mem_filter.mp hs).2; simp only [g, h, ↓reduceIte]
      · refine Finset.sum_congr rfl fun s hs => by
          have h := (Finset.mem_filter.mp hs).2; simp only [g, h, ↓reduceIte]
    have hsmall_le : ∑ s ∈ (Finset.range q).filter (fun s => min s (q - s) ≤ 2), N ≤ 5 * N := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard5 : ((Finset.range q).filter (fun s => min s (q - s) ≤ 2)).card ≤ 5 := by
        have hsub : (Finset.range q).filter (fun s => min s (q - s) ≤ 2) ⊆
            ({0, 1, 2, q - 2, q - 1} : Finset ℕ) := by
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
            Finset.mem_singleton] at hs ⊢
          omega
        calc ((Finset.range q).filter (fun s => min s (q - s) ≤ 2)).card
            ≤ ({0, 1, 2, q - 2, q - 1} : Finset ℕ).card := Finset.card_le_card hsub
          _ ≤ 5 := by
              calc ({0, 1, 2, q - 2, q - 1} : Finset ℕ).card
                  ≤ 1 + ({1, 2, q - 2, q - 1} : Finset ℕ).card := by
                    simpa [add_comm] using Finset.card_insert_le 0 {1, 2, q - 2, q - 1}
                _ ≤ 1 + (1 + ({2, q - 2, q - 1} : Finset ℕ).card) := by
                    have := Finset.card_insert_le 1 {2, q - 2, q - 1}; omega
                _ ≤ 1 + (1 + (1 + ({q - 2, q - 1} : Finset ℕ).card)) := by
                    have := Finset.card_insert_le 2 {q - 2, q - 1}; omega
                _ ≤ 5 := by
                    have := Finset.card_insert_le (q - 2) {q - 1}; simp at this; omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard5) hN
    have hbig_le : ∑ s ∈ (Finset.range q).filter (fun s => ¬ min s (q - s) ≤ 2),
          (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ)) ≤
        2 * (q : ℝ) * (Real.log (q : ℝ) + 1) := by
      set B := (Finset.range q).filter (fun s => ¬ min s (q - s) ≤ 2)
      rw [← Finset.sum_filter_add_sum_filter_not B (fun s => s ≤ q - s)]
      have hB1 : ∑ s ∈ B.filter (fun s => s ≤ q - s),
            (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ)) ≤
          (q : ℝ) * ∑ k ∈ Finset.Icc 1 q, (k : ℝ)⁻¹ := by
        have hrew : ∑ s ∈ B.filter (fun s => s ≤ q - s),
              (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ)) =
            (q : ℝ) * ∑ s ∈ B.filter (fun s => s ≤ q - s), (((s - 2 : ℕ) : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          have hle : s ≤ q - s := (Finset.mem_filter.mp hs).2
          rw [min_eq_left hle, div_eq_mul_inv]
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ hq_pos.le
        have hinj1 : Set.InjOn (fun s : ℕ => s - 2) ↑(B.filter (fun s => s ≤ q - s)) := by
          intro s₁ h1 s₂ h2 heq
          have hs1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1))
          have hs2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2))
          have hB1' := (Finset.mem_filter.mp hs1.1).2
          have hB2' := (Finset.mem_filter.mp hs2.1).2
          dsimp only at heq; omega
        have hsub1 : (B.filter (fun s => s ≤ q - s)).image (fun s : ℕ => s - 2) ⊆ Finset.Icc 1 q := by
          intro k hk
          rcases Finset.mem_image.mp hk with ⟨s, hs, rfl⟩
          have hs1 := Finset.mem_filter.mp hs
          have hBs := Finset.mem_filter.mp hs1.1
          have hlt := Finset.mem_range.mp hBs.1
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        rw [← Finset.sum_image (f := fun k : ℕ => (k : ℝ)⁻¹) hinj1]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by positivity
      have hB2 : ∑ s ∈ B.filter (fun s => ¬ s ≤ q - s),
            (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ)) ≤
          (q : ℝ) * ∑ k ∈ Finset.Icc 1 q, (k : ℝ)⁻¹ := by
        have hrew : ∑ s ∈ B.filter (fun s => ¬ s ≤ q - s),
              (q : ℝ) / (((min s (q - s) - 2 : ℕ) : ℝ)) =
            (q : ℝ) * ∑ s ∈ B.filter (fun s => ¬ s ≤ q - s), (((q - s - 2 : ℕ) : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s hs => ?_
          have hgt : ¬ s ≤ q - s := (Finset.mem_filter.mp hs).2
          rw [min_eq_right (by omega), div_eq_mul_inv]
        rw [hrew]
        refine mul_le_mul_of_nonneg_left ?_ hq_pos.le
        have hinj2 : Set.InjOn (fun s : ℕ => q - s - 2) ↑(B.filter (fun s => ¬ s ≤ q - s)) := by
          intro s₁ h1 s₂ h2 heq
          have hs1 := Finset.mem_filter.mp (Finset.mem_coe.mp h1)
          have hs2 := Finset.mem_filter.mp (Finset.mem_coe.mp h2)
          have hB1' := Finset.mem_filter.mp hs1.1
          have hB2' := Finset.mem_filter.mp hs2.1
          have hlt1 := Finset.mem_range.mp hB1'.1
          have hlt2 := Finset.mem_range.mp hB2'.1
          dsimp only at heq; omega
        have hsub2 : (B.filter (fun s => ¬ s ≤ q - s)).image (fun s : ℕ => q - s - 2) ⊆
            Finset.Icc 1 q := by
          intro k hk
          rcases Finset.mem_image.mp hk with ⟨s, hs, rfl⟩
          have hs1 := Finset.mem_filter.mp hs
          have hBs := Finset.mem_filter.mp hs1.1
          have hlt := Finset.mem_range.mp hBs.1
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        rw [← Finset.sum_image (f := fun k : ℕ => (k : ℝ)⁻¹) hinj2]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 fun _ _ _ => by positivity
      have hharm := sum_inv_Icc_le_log_add_one hq
      nlinarith
    linarith
  -- Step 2: Embed `m ∈ Icc 1 M` into `(m / q, m % q) ∈ range (M / q + 1) ×ˢ range q`
  have hmaps : (Finset.Icc 1 M).image (fun m => (m / q, m % q)) ⊆
      Finset.range (M / q + 1) ×ˢ Finset.range q := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨m, hm, rfl⟩
    have hm_le := (Finset.mem_Icc.mp hm).2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hm_le)),
       Finset.mem_range.mpr (Nat.mod_lt m hq)⟩
  have hinj : Set.InjOn (fun m : ℕ => (m / q, m % q)) ↑(Finset.Icc 1 M) := by
    intro m₁ _ m₂ _ heq
    simp only [Prod.mk.injEq] at heq
    have h1 := Nat.div_add_mod m₁ q
    have h2 := Nat.div_add_mod m₂ q
    rw [heq.1, heq.2] at h1
    linarith
  have hreidx : ∑ m ∈ Finset.Icc 1 M, minRecipDist N (α * (m : ℝ)) =
      ∑ p ∈ (Finset.Icc 1 M).image (fun m => (m / q, m % q)),
        minRecipDist N (α * ((p.1 * q + p.2 : ℕ) : ℝ)) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    have := Nat.div_add_mod m q
    exact_mod_cast (by linarith : m = m / q * q + m % q)
  have hlog_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hB_nn : 0 ≤ 5 * N + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1) := by positivity
  calc ∑ m ∈ Finset.Icc 1 M, minRecipDist N (α * (m : ℝ))
      = ∑ p ∈ (Finset.Icc 1 M).image (fun m => (m / q, m % q)),
          minRecipDist N (α * ((p.1 * q + p.2 : ℕ) : ℝ)) := hreidx
    _ ≤ ∑ p ∈ Finset.range (M / q + 1) ×ˢ Finset.range q,
          minRecipDist N (α * ((p.1 * q + p.2 : ℕ) : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hmaps fun _ _ _ => minRecipDist_nonneg hN _
    _ = ∑ j ∈ Finset.range (M / q + 1),
          ∑ r ∈ Finset.range q, minRecipDist N (α * ((j * q + r : ℕ) : ℝ)) :=
        Finset.sum_product _ _ _
    _ ≤ ∑ _j ∈ Finset.range (M / q + 1), (5 * N + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) :=
        Finset.sum_le_sum fun j _ => hblock j
    _ = ((M / q + 1 : ℕ) : ℝ) * (5 * N + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) := by
        simp; ring
    _ ≤ ((M : ℝ) / (q : ℝ) + 1) * (5 * N + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ hB_nn
        push_cast
        linarith [Nat.cast_div_le (α := ℝ) (m := M) (n := q)]

/-! ### Weyl Quadratic Exponential Sum Bound (`k = 2`) -/

/-- The Weyl quadratic exponential sum `W_N(α) = ∑_{n=1}^N e(α n^2)`. -/
def weylQuadSum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, e (α * (n : ℝ) ^ 2)

lemma continuous_weylQuadSum (N : ℕ) : Continuous (weylQuadSum N) := by
  unfold weylQuadSum
  refine continuous_finsetSum _ fun n _ => ?_
  have hfun : (fun α : ℝ => e (α * (n : ℝ) ^ 2)) = fun α : ℝ => e (((n : ℝ) ^ 2) * α) := by
    ext α; congr 1; ring
  rw [hfun]
  exact continuous_e_mul _

/-- **Weyl Differencing Inequality** for quadratic exponential sums:
`‖∑_{n=1}^N e(α n^2)‖^2 ≤ N + 2 ∑_{h=1}^{N-1} min(N, (2 ‖2 α h‖)⁻¹)`. -/
theorem weyl_quadratic_differencing (N : ℕ) (α : ℝ) :
    ‖weylQuadSum N α‖ ^ 2 ≤
      (N : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) (2 * α * (h : ℝ)) := by
  have hexp : ((‖weylQuadSum N α‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, e (α * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    unfold weylQuadSum
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    change e (α * (m : ℝ) ^ 2) * star (e (α * (n : ℝ) ^ 2)) = _
    rw [← e_neg, ← e_add]
    congr 1; ring
  -- Partition `Icc 1 N ×ˢ Icc 1 N` into `m = n`, `m > n`, and `m < n`
  set P := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
  have hpart : ∑ p ∈ P, e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)) =
      (∑ p ∈ P.filter (fun p => p.1 = p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) +
      (∑ p ∈ P.filter (fun p => p.2 < p.1), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) +
      (∑ p ∈ P.filter (fun p => p.1 < p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) := by
    rw [add_assoc, ← Finset.sum_filter_add_sum_filter_not P (fun p => p.1 = p.2)]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (P.filter (fun p => ¬ p.1 = p.2)) (fun p => p.2 < p.1)]
    congr 1
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p; simp only [Finset.mem_filter]
      exact ⟨fun ⟨⟨hP, _⟩, hlt⟩ => ⟨hP, hlt⟩, fun ⟨hP, hlt⟩ => ⟨⟨hP, by omega⟩, hlt⟩⟩
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext p; simp only [Finset.mem_filter]
      exact ⟨fun ⟨⟨hP, hne⟩, hnot⟩ => ⟨hP, by omega⟩, fun ⟨hP, hlt⟩ => ⟨⟨hP, by omega⟩, by omega⟩⟩
  have hdiag : ∑ p ∈ P.filter (fun p => p.1 = p.2),
        e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)) = (N : ℂ) := by
    have h1 : ∀ p ∈ P.filter (fun p => p.1 = p.2),
        e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)) = 1 := fun p hp => by
      have heq := (Finset.mem_filter.mp hp).2
      rw [heq, sub_self, mul_zero, e_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    have hcard : (P.filter (fun p => p.1 = p.2)).card = (Finset.Icc 1 N).card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      · intro p₁ h1 p₂ h2 heq
        have hp1 := (Finset.mem_filter.mp h1).2
        have hp2 := (Finset.mem_filter.mp h2).2
        exact Prod.ext heq (hp1.symm.trans (heq.trans hp2))
      · intro n hn
        exact ⟨(n, n), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hn, hn⟩, rfl⟩, rfl⟩
    rw [hcard, Nat.card_Icc]; omega
  have hupper : ‖∑ p ∈ P.filter (fun p => p.2 < p.1),
        e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ ≤
      ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) (2 * α * (h : ℝ)) := by
    -- Reindex `(m, n)` with `n < m` to `h = m - n ∈ Icc 1 (N - 1)` and `n ∈ Icc 1 (N - h)`
    have hbij : ∑ p ∈ P.filter (fun p => p.2 < p.1), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)) =
        ∑ h ∈ Finset.Icc 1 (N - 1), e (α * (h : ℝ) ^ 2) *
          ∑ n ∈ Finset.Icc 1 (N - h), e ((n : ℝ) * (2 * α * (h : ℝ))) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => (⟨p.1 - p.2, p.2⟩ : (h : ℕ) × ℕ)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_sigma] at hp ⊢
        omega
      · intro p₁ h1 p₂ h2 heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        simp only [Finset.mem_filter] at h1 h2
        exact Prod.ext (by omega) heq.2
      · intro ⟨h, n⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
        have hle_hN : h ≤ N := by
          by_contra hgt
          have : N - h = 0 := Nat.sub_eq_zero_of_le (by omega)
          omega
        have hnh : n + h ≤ N := Nat.add_le_of_le_sub hle_hN hx.2.2
        have hn_le : n ≤ N := hx.2.2.trans (Nat.sub_le N h)
        refine ⟨(n + h, n), ?_, ?_⟩
        · simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
        · simp only [Sigma.mk.inj_iff, heq_eq_eq]; exact ⟨by omega, trivial⟩
      · intro p hp
        have hlt : p.2 < p.1 := (Finset.mem_filter.mp hp).2
        rw [← e_add]
        congr 1
        have hsub : ((p.1 - p.2 : ℕ) : ℝ) = (p.1 : ℝ) - (p.2 : ℝ) := Nat.cast_sub hlt.le
        rw [hsub]
        ring
    rw [hbij]
    calc ‖∑ h ∈ Finset.Icc 1 (N - 1), e (α * (h : ℝ) ^ 2) *
            ∑ n ∈ Finset.Icc 1 (N - h), e ((n : ℝ) * (2 * α * (h : ℝ)))‖
        ≤ ∑ h ∈ Finset.Icc 1 (N - 1),
            ‖e (α * (h : ℝ) ^ 2) *
              ∑ n ∈ Finset.Icc 1 (N - h), e ((n : ℝ) * (2 * α * (h : ℝ)))‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) (2 * α * (h : ℝ)) := by
          refine Finset.sum_le_sum fun h _ => ?_
          rw [norm_mul, norm_e, one_mul]
          refine (norm_sum_e_Icc_le_minRecipDist 1 (N - h) _).trans ?_
          refine minRecipDist_mono ?_ _
          rw [Nat.card_Icc]
          exact_mod_cast (by omega : N - h + 1 - 1 ≤ N)
  have hlower : ‖∑ p ∈ P.filter (fun p => p.1 < p.2),
        e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ =
      ‖∑ p ∈ P.filter (fun p => p.2 < p.1),
        e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ := by
    have hconj : ∑ p ∈ P.filter (fun p => p.1 < p.2),
          e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)) =
        star (∑ p ∈ P.filter (fun p => p.2 < p.1),
          e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) := by
      rw [star_sum]
      refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
      · intro p₁ _ p₂ _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext heq.2 heq.1
      · intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_product] at hp
        exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
      · intro p _
        rw [← e_neg]
        congr 1; ring
    rw [hconj, norm_star]
  have hnorm_lhs : ‖((‖weylQuadSum N α‖ ^ 2 : ℝ) : ℂ)‖ = ‖weylQuadSum N α‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rw [← hnorm_lhs, hexp, ← Finset.sum_product', hpart]
  calc ‖(∑ p ∈ P.filter (fun p => p.1 = p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) +
          (∑ p ∈ P.filter (fun p => p.2 < p.1), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) +
          (∑ p ∈ P.filter (fun p => p.1 < p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)))‖
      ≤ ‖(∑ p ∈ P.filter (fun p => p.1 = p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))) +
          (∑ p ∈ P.filter (fun p => p.2 < p.1), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)))‖ +
        ‖∑ p ∈ P.filter (fun p => p.1 < p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ :=
        norm_add_le _ _
    _ ≤ ‖∑ p ∈ P.filter (fun p => p.1 = p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ +
        ‖∑ p ∈ P.filter (fun p => p.2 < p.1), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ +
        ‖∑ p ∈ P.filter (fun p => p.1 < p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2))‖ := by
        linarith [norm_add_le
          (∑ p ∈ P.filter (fun p => p.1 = p.2), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)))
          (∑ p ∈ P.filter (fun p => p.2 < p.1), e (α * ((p.1 : ℝ) ^ 2 - (p.2 : ℝ) ^ 2)))]
    _ ≤ (N : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) (2 * α * (h : ℝ)) := by
        rw [hdiag, Complex.norm_natCast, hlower]
        linarith

/-- **Explicit Weyl Quadratic Exponential-Sum Bound (`k = 2`)**:
If `1 ≤ q`, `gcd(a, q) = 1`, and `|α - a/q| ≤ 1/q^2`, then for every `N : ℕ`,
`‖∑_{n=1}^N e(α n^2)‖^2 ≤ 20 * (N^2 / q + N + q) * (log q + 1)`. -/
theorem weyl_quadratic_bound {α : ℝ} {a : ℤ} {q N : ℕ}
    (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖weylQuadSum N α‖ ^ 2 ≤
      20 * ((N : ℝ) ^ 2 / (q : ℝ) + (N : ℝ) + (q : ℝ)) * (Real.log (q : ℝ) + 1) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- Reduce `2 * a / q` to lowest terms `a' / q'` with `q / 2 ≤ q' ≤ q` and `|2α - a'/q'| ≤ 2/q'^2`
  have hred : ∃ (a' : ℤ) (q' : ℕ), 1 ≤ q' ∧ q' ≤ q ∧ q ≤ 2 * q' ∧
      Int.gcd a' q' = 1 ∧ |2 * α - (a' : ℝ) / (q' : ℝ)| ≤ 2 / (q' : ℝ) ^ 2 := by
    by_cases h2 : 2 ∣ q
    · rcases h2 with ⟨q', hq'⟩
      have hq'1 : 1 ≤ q' := by omega
      have hq'_pos : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'1
      have hcop' : Int.gcd a q' = 1 := by
        have hdvd : Nat.gcd a.natAbs q' ∣ Nat.gcd a.natAbs q :=
          Nat.dvd_gcd (Nat.gcd_dvd_left a.natAbs q')
            ((Nat.gcd_dvd_right a.natAbs q').trans ⟨2, by omega⟩)
        change Nat.gcd a.natAbs q' = 1
        have hcop_nat : Nat.gcd a.natAbs q = 1 := hcop
        rw [hcop_nat] at hdvd
        exact Nat.dvd_one.mp hdvd
      refine ⟨a, q', hq'1, by omega, by omega, hcop', ?_⟩
      have hq_r : (q : ℝ) = 2 * (q' : ℝ) := by exact_mod_cast hq'
      have heq : 2 * α - (a : ℝ) / (q' : ℝ) = 2 * (α - (a : ℝ) / (q : ℝ)) := by
        rw [hq_r]; field_simp [hq'_pos.ne']
      rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc 2 * |α - (a : ℝ) / (q : ℝ)|
          ≤ 2 * (1 / (q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left happrox (by norm_num)
        _ = 1 / (2 * (q' : ℝ) ^ 2) := by rw [hq_r]; field_simp [hq'_pos.ne']
        _ ≤ 2 / (q' : ℝ) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [sq_pos_of_pos hq'_pos]
    · refine ⟨2 * a, q, hq, le_rfl, by omega, ?_, ?_⟩
      · have hcop2 : Nat.Coprime 2 q := by
          rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; exact h2
        have hcop_a : Nat.Coprime a.natAbs q := hcop
        change Nat.gcd (2 * a).natAbs q = 1
        rw [Int.natAbs_mul, show (2 : ℤ).natAbs = 2 by rfl]
        exact (hcop2.mul_left hcop_a).gcd_eq_one
      · have heq : 2 * α - ((2 * a : ℤ) : ℝ) / (q : ℝ) = 2 * (α - (a : ℝ) / (q : ℝ)) := by
          push_cast; ring
        rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        calc 2 * |α - (a : ℝ) / (q : ℝ)|
            ≤ 2 * (1 / (q : ℝ) ^ 2) := mul_le_mul_of_nonneg_left happrox (by norm_num)
          _ = 2 / (q : ℝ) ^ 2 := by ring
  rcases hred with ⟨a', q', hq'1, hq'_le, hq_le2, hcop', happrox'⟩
  have hq'_pos : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'1
  have hvin := vinogradov_minRecipDist_sum (M := N - 1) (N := (N : ℝ))
    hq'1 hcop' happrox' (Nat.cast_nonneg N)
  have hdiff := weyl_quadratic_differencing N α
  have hsum_eq : ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) (2 * α * (h : ℝ)) =
      ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) ((2 * α) * (h : ℝ)) := rfl
  have hlog_le : Real.log (q' : ℝ) + 1 ≤ Real.log (q : ℝ) + 1 := by
    linarith [Real.log_le_log hq'_pos (show (q' : ℝ) ≤ (q : ℝ) by exact_mod_cast hq'_le)]
  have hlog_ge1 : 1 ≤ Real.log (q : ℝ) + 1 := by
    linarith [Real.log_nonneg (by exact_mod_cast hq : (1 : ℝ) ≤ (q : ℝ))]
  have hq'_r_le : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq'_le
  have hq_r_le2 : (q : ℝ) ≤ 2 * (q' : ℝ) := by exact_mod_cast hq_le2
  have hNm1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
  have hdiv_le : ((N - 1 : ℕ) : ℝ) / (q' : ℝ) ≤ 2 * (N : ℝ) / (q : ℝ) := by
    rw [div_le_div_iff₀ hq'_pos hq_pos]
    have h1 : ((N - 1 : ℕ) : ℝ) * (q : ℝ) ≤ (N : ℝ) * (q : ℝ) :=
      mul_le_mul_of_nonneg_right hNm1 hq_pos.le
    have h2 : (N : ℝ) * (q : ℝ) ≤ (N : ℝ) * (2 * (q' : ℝ)) :=
      mul_le_mul_of_nonneg_left hq_r_le2 (Nat.cast_nonneg N)
    linarith
  have hvin2 : ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (N : ℝ) (2 * α * (h : ℝ)) ≤
      (2 * (N : ℝ) / (q : ℝ) + 1) * (5 * (N : ℝ) + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) := by
    refine hvin.trans ?_
    refine mul_le_mul (by linarith) ?_ (by positivity) (by positivity)
    have hmul : (q' : ℝ) * (Real.log (q' : ℝ) + 1) ≤ (q : ℝ) * (Real.log (q : ℝ) + 1) :=
      mul_le_mul hq'_r_le hlog_le (by linarith [Real.log_nonneg (by exact_mod_cast hq'1 : (1 : ℝ) ≤ q')])
        hq_pos.le
    linarith
  have hprod_expand :
      (2 * (N : ℝ) / (q : ℝ) + 1) * (5 * (N : ℝ) + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) =
      10 * ((N : ℝ) ^ 2 / (q : ℝ)) + 5 * (N : ℝ) +
        (4 * (N : ℝ) + 2 * (q : ℝ)) * (Real.log (q : ℝ) + 1) := by
    field_simp [hq_pos.ne']
    ring
  rw [hprod_expand] at hvin2
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN2q_nn : (0 : ℝ) ≤ (N : ℝ) ^ 2 / (q : ℝ) := by positivity
  nlinarith

/-! ### Hua's `L^4` Mean-Value Bound for Quadratic Exponential Sums -/

lemma hua_L4_eq_card (N : ℕ) :
    (∫ α in (0 : ℝ)..1, ‖weylQuadSum N α‖ ^ 4) =
      (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
        (fun x => x.1 ^ 2 + x.2.1 ^ 2 = x.2.2.1 ^ 2 + x.2.2.2 ^ 2)).card : ℝ) := by
  set I := Finset.Icc 1 N
  set Q := I ×ˢ I ×ˢ I ×ˢ I
  have hC : (∫ α in (0 : ℝ)..1, ((‖weylQuadSum N α‖ ^ 4 : ℝ) : ℂ)) =
      ((Q.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 = x.2.2.1 ^ 2 + x.2.2.2 ^ 2)).card : ℂ) := by
    have hpt : ∀ α : ℝ, ((‖weylQuadSum N α‖ ^ 4 : ℝ) : ℂ) =
        ∑ x ∈ Q, e (((((x.1 ^ 2 + x.2.1 ^ 2 : ℕ) : ℤ) - ((x.2.2.1 ^ 2 + x.2.2.2 ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) * α) := by
      intro α
      have hsq : ((‖weylQuadSum N α‖ ^ 4 : ℝ) : ℂ) =
          (weylQuadSum N α * weylQuadSum N α) * star (weylQuadSum N α * weylQuadSum N α) := by
        have h1 : ‖weylQuadSum N α‖ ^ 4 = (‖weylQuadSum N α‖ ^ 2) ^ 2 := by ring
        rw [h1, Complex.ofReal_pow, Complex.ofReal_pow, ← Complex.mul_conj']
        change (weylQuadSum N α * star (weylQuadSum N α)) ^ 2 = _
        rw [star_mul']
        ring
      rw [hsq]
      unfold weylQuadSum
      rw [Finset.sum_mul_sum, star_sum, Finset.sum_mul_sum]
      simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
      simp_rw [Q, Finset.sum_product]
      refine Finset.sum_congr rfl fun x1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun y1 _ =>
        Finset.sum_congr rfl fun y2 _ => ?_
      rw [star_mul', ← e_neg, ← e_neg, ← e_add, ← e_add, ← e_add]
      congr 1
      push_cast
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_e_int]
      have hiff : ((x.1 ^ 2 + x.2.1 ^ 2 : ℕ) : ℤ) - ((x.2.2.1 ^ 2 + x.2.2.2 ^ 2 : ℕ) : ℤ) = 0 ↔
          x.1 ^ 2 + x.2.1 ^ 2 = x.2.2.1 ^ 2 + x.2.2.2 ^ 2 := by
        constructor
        · intro h; exact Int.ofNat.inj (sub_eq_zero.mp h)
        · intro h; rw [h, sub_self]
      by_cases heq : x.1 ^ 2 + x.2.1 ^ 2 = x.2.2.1 ^ 2 + x.2.2.2 ^ 2
      · rw [heq, sub_self]; simp
      · have hne : ((x.1 ^ 2 + x.2.1 ^ 2 : ℕ) : ℤ) - ((x.2.2.1 ^ 2 + x.2.2.2 ^ 2 : ℕ) : ℤ) ≠ 0 :=
          fun h => heq (hiff.mp h)
        simp only [heq, hne, ↓reduceIte]
    · intro x _
      exact (continuous_e_mul _).intervalIntegrable 0 1
  have hre := congr_arg Complex.re hC
  have hL : (∫ α in (0 : ℝ)..1, ((‖weylQuadSum N α‖ ^ 4 : ℝ) : ℂ)).re =
      ∫ α in (0 : ℝ)..1, ‖weylQuadSum N α‖ ^ 4 := by
    rw [← Complex.reCLM_apply]
    have hint : IntervalIntegrable (fun α : ℝ => ((‖weylQuadSum N α‖ ^ 4 : ℝ) : ℂ)) volume 0 1 :=
      (Complex.continuous_ofReal.comp ((continuous_weylQuadSum N).norm.pow 4)).intervalIntegrable 0 1
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint]
    rfl
  rw [hL, Complex.natCast_re] at hre
  exact hre

lemma sum_inv_max_le_two_mul (M : ℕ) :
    ∑ u ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M, ((max u r : ℕ) : ℝ)⁻¹ ≤ 2 * (M : ℝ) := by
  have hsplit : ∑ u ∈ Finset.Icc 1 M, ∑ r ∈ Finset.Icc 1 M, ((max u r : ℕ) : ℝ)⁻¹ =
      (∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.1 ≤ p.2),
        ((max p.1 p.2 : ℕ) : ℝ)⁻¹) +
      (∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => ¬ p.1 ≤ p.2),
        ((max p.1 p.2 : ℕ) : ℝ)⁻¹) := by
    rw [← Finset.sum_product', Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have h1 : ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.1 ≤ p.2),
        ((max p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (M : ℝ) := by
    have heq : ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => p.1 ≤ p.2),
          ((max p.1 p.2 : ℕ) : ℝ)⁻¹ =
        ∑ r ∈ Finset.Icc 1 M, ∑ _u ∈ Finset.Icc 1 r, (r : ℝ)⁻¹ := by
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => (⟨p.2, p.1⟩ : (r : ℕ) × ℕ)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_sigma] at hp ⊢
        omega
      · intro p₁ _ p₂ _ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        exact Prod.ext heq.2 heq.1
      · intro ⟨r, u⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
        exact ⟨(u, r), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hx.2.1, by omega⟩,
            Finset.mem_Icc.mpr hx.1⟩, hx.2.2⟩, rfl⟩
      · intro p hp
        have hle := (Finset.mem_filter.mp hp).2
        rw [max_eq_right hle]
    rw [heq]
    have hinner : ∀ r ∈ Finset.Icc 1 M, ∑ _u ∈ Finset.Icc 1 r, (r : ℝ)⁻¹ = 1 := fun r hr => by
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      rw [Finset.sum_const, Nat.card_Icc, show r + 1 - 1 = r by omega, nsmul_eq_mul,
        mul_inv_cancel₀ (by exact_mod_cast (by omega : r ≠ 0))]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    exact_mod_cast (by omega : M + 1 - 1 ≤ M)
  have h2 : ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => ¬ p.1 ≤ p.2),
        ((max p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (M : ℝ) := by
    have heq : ∑ p ∈ (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter (fun p => ¬ p.1 ≤ p.2),
          ((max p.1 p.2 : ℕ) : ℝ)⁻¹ =
        ∑ u ∈ Finset.Icc 1 M, ∑ _r ∈ Finset.Icc 1 (u - 1), (u : ℝ)⁻¹ := by
      rw [Finset.sum_sigma']
      refine Finset.sum_bij (fun p _ => (⟨p.1, p.2⟩ : (u : ℕ) × ℕ)) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_sigma] at hp ⊢
        omega
      · intro p₁ _ p₂ _ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        exact Prod.ext heq.1 heq.2
      · intro ⟨u, r⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
        exact ⟨(u, r), Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hx.1,
            Finset.mem_Icc.mpr ⟨hx.2.1, by omega⟩⟩, by omega⟩, rfl⟩
      · intro p hp
        have hgt := (Finset.mem_filter.mp hp).2
        rw [max_eq_left (by omega)]
    rw [heq]
    have hinner : ∀ u ∈ Finset.Icc 1 M, ∑ _r ∈ Finset.Icc 1 (u - 1), (u : ℝ)⁻¹ ≤ 1 := fun u hu => by
      have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      have hle : ((u - 1 + 1 - 1 : ℕ) : ℝ) ≤ (u : ℝ) := by exact_mod_cast (by omega : u - 1 + 1 - 1 ≤ u)
      calc ((u - 1 + 1 - 1 : ℕ) : ℝ) * (u : ℝ)⁻¹
          ≤ (u : ℝ) * (u : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 1 := mul_inv_cancel₀ (by exact_mod_cast (by omega : u ≠ 0))
    calc ∑ u ∈ Finset.Icc 1 M, ∑ _r ∈ Finset.Icc 1 (u - 1), (u : ℝ)⁻¹
        ≤ ∑ _u ∈ Finset.Icc 1 M, (1 : ℝ) := Finset.sum_le_sum hinner
      _ = ((Finset.Icc 1 M).card : ℝ) := by simp
      _ ≤ (M : ℝ) := by rw [Nat.card_Icc]; exact_mod_cast (by omega : M + 1 - 1 ≤ M)
  linarith

/-- **Hua's `L^4` Mean-Value Bound (1938)** for quadratic exponential sums:
For every `N ≥ 1`,
`∫₀¹ ‖∑_{n=1}^N e(α n^2)‖^4 dα ≤ 9 * N^2 * (log N + 1)`. -/
theorem hua_L4_bound {N : ℕ} (hN : 1 ≤ N) :
    (∫ α in (0 : ℝ)..1, ‖weylQuadSum N α‖ ^ 4) ≤
      9 * (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) := by
  rw [hua_L4_eq_card]
  set I := Finset.Icc 1 N
  set Q := I ×ˢ I ×ˢ I ×ˢ I
  set Sol := Q.filter (fun x => x.1 ^ 2 + x.2.1 ^ 2 = x.2.2.1 ^ 2 + x.2.2.2 ^ 2)
  -- Partition `Sol` into `x₁ = y₁`, `x₁ > y₁`, and `x₁ < y₁`
  have hcard_split : Sol.card =
      (Sol.filter (fun x => x.1 = x.2.2.1)).card +
      (Sol.filter (fun x => x.2.2.1 < x.1)).card +
      (Sol.filter (fun x => x.1 < x.2.2.1)).card := by
    have h1 : (Sol.filter (fun x => x.1 = x.2.2.1)).card +
        (Sol.filter (fun x => ¬ x.1 = x.2.2.1)).card = Sol.card := by
      simpa using Finset.sum_filter_add_sum_filter_not Sol (fun x => x.1 = x.2.2.1) (fun _ => (1 : ℕ))
    have h2 : ((Sol.filter (fun x => ¬ x.1 = x.2.2.1)).filter (fun x => x.2.2.1 < x.1)).card +
        ((Sol.filter (fun x => ¬ x.1 = x.2.2.1)).filter (fun x => ¬ x.2.2.1 < x.1)).card =
        (Sol.filter (fun x => ¬ x.1 = x.2.2.1)).card := by
      simpa using Finset.sum_filter_add_sum_filter_not (Sol.filter (fun x => ¬ x.1 = x.2.2.1))
        (fun x => x.2.2.1 < x.1) (fun _ => (1 : ℕ))
    have hA : (Sol.filter (fun x => ¬ x.1 = x.2.2.1)).filter (fun x => x.2.2.1 < x.1) =
        Sol.filter (fun x => x.2.2.1 < x.1) := by
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun ⟨⟨hS, _⟩, hlt⟩ => ⟨hS, hlt⟩, fun ⟨hS, hlt⟩ => ⟨⟨hS, by omega⟩, hlt⟩⟩
    have hB : (Sol.filter (fun x => ¬ x.1 = x.2.2.1)).filter (fun x => ¬ x.2.2.1 < x.1) =
        Sol.filter (fun x => x.1 < x.2.2.1) := by
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun ⟨⟨hS, hne⟩, hnot⟩ => ⟨hS, by omega⟩, fun ⟨hS, hlt⟩ => ⟨⟨hS, by omega⟩, by omega⟩⟩
    rw [hA, hB] at h2
    omega
  -- Diagonal `x₁ = y₁` implies `x₂ = y₂`, so card = `N^2`
  have hdiag : (Sol.filter (fun x => x.1 = x.2.2.1)).card ≤ N ^ 2 := by
    have hsub : (Sol.filter (fun x => x.1 = x.2.2.1)).image (fun x => (x.1, x.2.1)) ⊆ I ×ˢ I := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
      have hxQ := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
      simp only [Q, Finset.mem_product] at hxQ ⊢
      exact ⟨hxQ.1, hxQ.2.1⟩
    have hinj : Set.InjOn (fun x : ℕ × ℕ × ℕ × ℕ => (x.1, x.2.1))
        ↑(Sol.filter (fun x => x.1 = x.2.2.1)) := by
      intro x hx y hy heq
      simp only [Prod.mk.injEq] at heq
      have hx1 := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      have hy1 := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
      have hxeq := (Finset.mem_filter.mp hx1.1).2
      have hyeq := (Finset.mem_filter.mp hy1.1).2
      have hx_y2 : x.2.1 = x.2.2.2 := by
        have hsq : x.2.1 ^ 2 = x.2.2.2 ^ 2 := by rw [hx1.2] at hxeq; omega
        nlinarith
      have hy_y2 : y.2.1 = y.2.2.2 := by
        have hsq : y.2.1 ^ 2 = y.2.2.2 ^ 2 := by rw [hy1.2] at hyeq; omega
        nlinarith
      exact Prod.ext heq.1 (Prod.ext heq.2 (Prod.ext (by omega) (by omega)))
    calc (Sol.filter (fun x => x.1 = x.2.2.1)).card
        = ((Sol.filter (fun x => x.1 = x.2.2.1)).image (fun x => (x.1, x.2.1))).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (I ×ˢ I).card := Finset.card_le_card hsub
      _ = N ^ 2 := by rw [Finset.card_product, Nat.card_Icc]; simp [pow_two]
  -- Symmetry `x₁ < y₁` has the same cardinality as `y₁ < x₁`
  have hsymm : (Sol.filter (fun x => x.1 < x.2.2.1)).card =
      (Sol.filter (fun x => x.2.2.1 < x.1)).card := by
    refine Finset.card_bij (fun x _ => (x.2.2.1, x.2.2.2, x.1, x.2.1)) ?_ ?_ ?_
    · intro x hx
      simp only [Sol, Q, Finset.mem_filter, Finset.mem_product] at hx ⊢
      exact ⟨⟨⟨hx.1.1.2.2.1, hx.1.1.2.2.2, hx.1.1.1, hx.1.1.2.1⟩, hx.1.2.symm⟩, hx.2⟩
    · intro x _ y _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2.2.1 (Prod.ext heq.2.2.2 (Prod.ext heq.1 heq.2.1))
    · intro y hy
      simp only [Sol, Q, Finset.mem_filter, Finset.mem_product] at hy
      exact ⟨(y.2.2.1, y.2.2.2, y.1, y.2.1),
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hy.1.1.2.2.1, Finset.mem_product.mpr
            ⟨hy.1.1.2.2.2, Finset.mem_product.mpr ⟨hy.1.1.1, hy.1.1.2.1⟩⟩⟩, hy.1.2.symm⟩, hy.2⟩, rfl⟩
  -- Off-diagonal bound for `T := Sol.filter (fun x => x.2.2.1 < x.1)`
  set T := Sol.filter (fun x => x.2.2.1 < x.1)
  set fMap : (ℕ × ℕ × ℕ × ℕ) → ((d : ℕ) × (u' : ℕ) × (r' : ℕ) × ℕ) := fun x =>
    let u := x.1 - x.2.2.1
    let r := x.2.2.2 - x.2.1
    let d := Nat.gcd u r
    ⟨d, u / d, r / d, (x.1 + x.2.2.1) / (r / d)⟩
  set Dom : Finset ((d : ℕ) × (u' : ℕ) × (r' : ℕ) × ℕ) :=
    (Finset.Icc 1 N).sigma fun d =>
      (Finset.Icc 1 (N / d)).sigma fun u' =>
        (Finset.Icc 1 (N / d)).sigma fun r' =>
          Finset.Icc 1 (2 * N / max u' r')
  have hf_maps : T.image fMap ⊆ Dom := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    simp only [T, Sol, Q, Finset.mem_filter, Finset.mem_product, I, Finset.mem_Icc] at hx
    have hlt1 : x.2.2.1 < x.1 := hx.2
    have hlt2 : x.2.1 < x.2.2.2 := by nlinarith [hx.1.2]
    set u := x.1 - x.2.2.1
    set v := x.1 + x.2.2.1
    set r := x.2.2.2 - x.2.1
    set s := x.2.2.2 + x.2.1
    have huv_rs : u * v = r * s := by
      have h1 : (u : ℤ) * (v : ℤ) = (r : ℤ) * (s : ℤ) := by
        dsimp [u, v, r, s]
        have hu : ((x.1 - x.2.2.1 : ℕ) : ℤ) = (x.1 : ℤ) - (x.2.2.1 : ℤ) := Int.ofNat_sub hlt1.le
        have hr : ((x.2.2.2 - x.2.1 : ℕ) : ℤ) = (x.2.2.2 : ℤ) - (x.2.1 : ℤ) := Int.ofNat_sub hlt2.le
        have hsq : (x.1 : ℤ) ^ 2 + (x.2.1 : ℤ) ^ 2 = (x.2.2.1 : ℤ) ^ 2 + (x.2.2.2 : ℤ) ^ 2 := by
          exact_mod_cast hx.1.2
        rw [hu, hr]; nlinarith
      exact_mod_cast h1
    set d := Nat.gcd u r
    have hu_pos : 1 ≤ u := by omega
    have hr_pos : 1 ≤ r := by omega
    have hd_pos : 1 ≤ d := Nat.gcd_pos_of_pos_left r hu_pos
    have hd_le_u : d ≤ u := Nat.le_of_dvd hu_pos (Nat.gcd_dvd_left u r)
    have hd_le_N : d ≤ N := hd_le_u.trans (by omega)
    have hu'_mul : d * (u / d) = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u r)
    have hr'_mul : d * (r / d) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right u r)
    have hu'_pos : 1 ≤ u / d :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hu'_mul; omega
    have hr'_pos : 1 ≤ r / d :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hr'_mul; omega
    have hu'_le : u / d ≤ N / d := Nat.div_le_div_right (by omega : u ≤ N)
    have hr'_le : r / d ≤ N / d := Nat.div_le_div_right (by omega : r ≤ N)
    have hcop' : Nat.Coprime (u / d) (r / d) := Nat.coprime_div_gcd_div_gcd hd_pos
    have hmul' : (u / d) * v = (r / d) * s := by
      have : d * ((u / d) * v) = d * ((r / d) * s) := by
        calc d * ((u / d) * v) = (d * (u / d)) * v := by ring
          _ = u * v := by rw [hu'_mul]
          _ = r * s := huv_rs
          _ = (d * (r / d)) * s := by rw [hr'_mul]
          _ = d * ((r / d) * s) := by ring
      exact Nat.eq_of_mul_eq_mul_left hd_pos this
    have hr'_dvd_v : r / d ∣ v := hcop'.symm.dvd_of_dvd_mul_left ⟨s, hmul'⟩
    have hv_eq : (r / d) * (v / (r / d)) = v := Nat.mul_div_cancel' hr'_dvd_v
    have hs_eq : (u / d) * (v / (r / d)) = s := by
      have : (r / d) * ((u / d) * (v / (r / d))) = (r / d) * s := by
        calc (r / d) * ((u / d) * (v / (r / d)))
            = (u / d) * ((r / d) * (v / (r / d))) := by ring
          _ = (u / d) * v := by rw [hv_eq]
          _ = (r / d) * s := hmul'
      exact Nat.eq_of_mul_eq_mul_left hr'_pos this
    have hk_pos : 1 ≤ v / (r / d) :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hv_eq; omega
    have hk_le : v / (r / d) ≤ 2 * N / max (u / d) (r / d) := by
      rw [Nat.le_div_iff_mul_le (lt_of_lt_of_le hu'_pos (le_max_left _ _))]
      by_cases hle : u / d ≤ r / d
      · rw [max_eq_right hle, mul_comm, hv_eq]; omega
      · rw [max_eq_left (by omega), mul_comm, hs_eq]; omega
    simp only [Dom, fMap, Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hd_pos, hd_le_N⟩, ⟨hu'_pos, hu'_le⟩, ⟨hr'_pos, hr'_le⟩, ⟨hk_pos, hk_le⟩⟩
  have hf_inj : Set.InjOn fMap ↑T := by
    intro x hx y hy heq
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    have hxsol := (Finset.mem_filter.mp hx'.1).2
    have hysol := (Finset.mem_filter.mp hy'.1).2
    have hxlt1 : x.2.2.1 < x.1 := hx'.2
    have hxlt2 : x.2.1 < x.2.2.2 := by nlinarith [hxsol]
    have hylt1 : y.2.2.1 < y.1 := hy'.2
    have hylt2 : y.2.1 < y.2.2.2 := by nlinarith [hysol]
    simp only [fMap, Sigma.mk.inj_iff, heq_eq_eq] at heq
    rcases heq with ⟨hd_eq, hu'_eq, hr'_eq, hk_eq⟩
    have hux : Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1) * ((x.1 - x.2.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1)) = x.1 - x.2.2.1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have huy : Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1) * ((y.1 - y.2.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1)) = y.1 - y.2.2.1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hrx : Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1) * ((x.2.2.2 - x.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1)) = x.2.2.2 - x.2.1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have hry : Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1) * ((y.2.2.2 - y.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1)) = y.2.2.2 - y.2.1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have hu_eq : x.1 - x.2.2.1 = y.1 - y.2.2.1 := by rw [← hux, ← huy, hu'_eq, hd_eq]
    have hr_eq : x.2.2.2 - x.2.1 = y.2.2.2 - y.2.1 := by rw [← hrx, ← hry, hr'_eq, hd_eq]
    -- Show `r' ∣ v` for both `x` and `y`, so `v` is also determined!
    have huv_x : (x.1 - x.2.2.1) * (x.1 + x.2.2.1) = (x.2.2.2 - x.2.1) * (x.2.2.2 + x.2.1) := by
      have h1 : ((x.1 - x.2.2.1 : ℕ) : ℤ) * ((x.1 + x.2.2.1 : ℕ) : ℤ) =
          ((x.2.2.2 - x.2.1 : ℕ) : ℤ) * ((x.2.2.2 + x.2.1 : ℕ) : ℤ) := by
        rw [Int.ofNat_sub hxlt1.le, Int.ofNat_sub hxlt2.le]
        have : (x.1 : ℤ) ^ 2 + (x.2.1 : ℤ) ^ 2 = (x.2.2.1 : ℤ) ^ 2 + (x.2.2.2 : ℤ) ^ 2 := by
          exact_mod_cast hxsol
        push_cast; nlinarith
      exact_mod_cast h1
    have huv_y : (y.1 - y.2.2.1) * (y.1 + y.2.2.1) = (y.2.2.2 - y.2.1) * (y.2.2.2 + y.2.1) := by
      have h1 : ((y.1 - y.2.2.1 : ℕ) : ℤ) * ((y.1 + y.2.2.1 : ℕ) : ℤ) =
          ((y.2.2.2 - y.2.1 : ℕ) : ℤ) * ((y.2.2.2 + y.2.1 : ℕ) : ℤ) := by
        rw [Int.ofNat_sub hylt1.le, Int.ofNat_sub hylt2.le]
        have : (y.1 : ℤ) ^ 2 + (y.2.1 : ℤ) ^ 2 = (y.2.2.1 : ℤ) ^ 2 + (y.2.2.2 : ℤ) ^ 2 := by
          exact_mod_cast hysol
        push_cast; nlinarith
      exact_mod_cast h1
    have hdx_pos : 0 < Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have hdy_pos : 0 < Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1) :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have hcopx := Nat.coprime_div_gcd_div_gcd hdx_pos
    have hcopy := Nat.coprime_div_gcd_div_gcd hdy_pos
    have hmulx' : ((x.1 - x.2.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1)) * (x.1 + x.2.2.1) =
        ((x.2.2.2 - x.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1)) * (x.2.2.2 + x.2.1) :=
      Nat.eq_of_mul_eq_mul_left hdx_pos (by
        calc Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1) *
              (((x.1 - x.2.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1)) * (x.1 + x.2.2.1))
            = (Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1) *
              ((x.1 - x.2.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1))) * (x.1 + x.2.2.1) := by ring
          _ = (x.1 - x.2.2.1) * (x.1 + x.2.2.1) := by rw [hux]
          _ = (x.2.2.2 - x.2.1) * (x.2.2.2 + x.2.1) := huv_x
          _ = (Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1) *
              ((x.2.2.2 - x.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1))) * (x.2.2.2 + x.2.1) := by rw [hrx]
          _ = _ := by ring)
    have hmuly' : ((y.1 - y.2.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1)) * (y.1 + y.2.2.1) =
        ((y.2.2.2 - y.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1)) * (y.2.2.2 + y.2.1) :=
      Nat.eq_of_mul_eq_mul_left hdy_pos (by
        calc Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1) *
              (((y.1 - y.2.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1)) * (y.1 + y.2.2.1))
            = (Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1) *
              ((y.1 - y.2.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1))) * (y.1 + y.2.2.1) := by ring
          _ = (y.1 - y.2.2.1) * (y.1 + y.2.2.1) := by rw [huy]
          _ = (y.2.2.2 - y.2.1) * (y.2.2.2 + y.2.1) := huv_y
          _ = (Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1) *
              ((y.2.2.2 - y.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1))) * (y.2.2.2 + y.2.1) := by rw [hry]
          _ = _ := by ring)
    have hvx : ((x.2.2.2 - x.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1)) *
        ((x.1 + x.2.2.1) / ((x.2.2.2 - x.2.1) / Nat.gcd (x.1 - x.2.2.1) (x.2.2.2 - x.2.1))) =
        x.1 + x.2.2.1 :=
      Nat.mul_div_cancel' (hcopx.symm.dvd_of_dvd_mul_left ⟨x.2.2.2 + x.2.1, hmulx'⟩)
    have hvy : ((y.2.2.2 - y.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1)) *
        ((y.1 + y.2.2.1) / ((y.2.2.2 - y.2.1) / Nat.gcd (y.1 - y.2.2.1) (y.2.2.2 - y.2.1))) =
        y.1 + y.2.2.1 :=
      Nat.mul_div_cancel' (hcopy.symm.dvd_of_dvd_mul_left ⟨y.2.2.2 + y.2.1, hmuly'⟩)
    have hv_eq : x.1 + x.2.2.1 = y.1 + y.2.2.1 := by rw [← hvx, ← hvy, hk_eq, hr'_eq]
    have hs_eq : x.2.2.2 + x.2.1 = y.2.2.2 + y.2.1 := by
      have : (x.2.2.2 - x.2.1) * (x.2.2.2 + x.2.1) = (x.2.2.2 - x.2.1) * (y.2.2.2 + y.2.1) := by
        rw [← huv_x, hu_eq, hv_eq, huv_y, ← hr_eq]
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < x.2.2.2 - x.2.1) this
    exact Prod.ext (by omega) (Prod.ext (by omega) (Prod.ext (by omega) (by omega)))
  have hT_le : (T.card : ℝ) ≤ 4 * (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) := by
    have hcard_dom : T.card ≤ Dom.card := by
      rw [← Finset.card_image_of_injOn hf_inj]
      exact Finset.card_le_card hf_maps
    have hdom_eval : Dom.card =
        ∑ d ∈ Finset.Icc 1 N, ∑ u' ∈ Finset.Icc 1 (N / d), ∑ r' ∈ Finset.Icc 1 (N / d),
          (2 * N / max u' r') := by
      simp only [Dom, Finset.card_sigma, Nat.card_Icc]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Nat.add_sub_cancel _ 1
    have hdom_real : (Dom.card : ℝ) ≤ 4 * (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) := by
      rw [hdom_eval]
      push_cast
      calc ∑ d ∈ Finset.Icc 1 N, ∑ u' ∈ Finset.Icc 1 (N / d), ∑ r' ∈ Finset.Icc 1 (N / d),
              ((2 * N / max u' r' : ℕ) : ℝ)
          ≤ ∑ d ∈ Finset.Icc 1 N, ∑ u' ∈ Finset.Icc 1 (N / d), ∑ r' ∈ Finset.Icc 1 (N / d),
              (2 * (N : ℝ)) * ((max u' r' : ℕ) : ℝ)⁻¹ := by
            refine Finset.sum_le_sum fun d _ => Finset.sum_le_sum fun u' _ =>
              Finset.sum_le_sum fun r' _ => ?_
            rw [← div_eq_mul_inv]
            have hdiv := Nat.cast_div_le (α := ℝ) (m := 2 * N) (n := max u' r')
            rw [Nat.cast_mul, Nat.cast_ofNat] at hdiv
            exact hdiv
        _ = ∑ d ∈ Finset.Icc 1 N, (2 * (N : ℝ)) *
              (∑ u' ∈ Finset.Icc 1 (N / d), ∑ r' ∈ Finset.Icc 1 (N / d),
                ((max u' r' : ℕ) : ℝ)⁻¹) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u' _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ d ∈ Finset.Icc 1 N, (2 * (N : ℝ)) * (2 * ((N / d : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun d _ =>
              mul_le_mul_of_nonneg_left (sum_inv_max_le_two_mul (N / d)) (by positivity)
        _ ≤ ∑ d ∈ Finset.Icc 1 N, (4 * (N : ℝ) ^ 2) * (d : ℝ)⁻¹ := by
            refine Finset.sum_le_sum fun d _ => ?_
            have hd_div : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
            rw [div_eq_mul_inv] at hd_div
            have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
            nlinarith
        _ = 4 * (N : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
        _ ≤ 4 * (N : ℝ) ^ 2 * (Real.log (N : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log_add_one hN) (by positivity)
    exact (Nat.cast_le.mpr hcard_dom).trans hdom_real
  have hlog_ge1 : 1 ≤ Real.log (N : ℝ) + 1 := by
    linarith [Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))]
  have hdiag_r : ((Sol.filter (fun x => x.1 = x.2.2.1)).card : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast hdiag
  have hsplit_r : (Sol.card : ℝ) =
      ((Sol.filter (fun x => x.1 = x.2.2.1)).card : ℝ) + 2 * (T.card : ℝ) := by
    have : Sol.card = (Sol.filter (fun x => x.1 = x.2.2.1)).card + 2 * T.card := by
      rw [hcard_split, hsymm]; ring
    exact_mod_cast this
  rw [hsplit_r]
  nlinarith [sq_nonneg (N : ℝ)]

/-! ### Bilinear Type I–II Minor-Arc Bounds & Vaughan Bridge -/

/-- **General Cauchy–Schwarz Bilinear (Type II) Minor-Arc Bound**:
For arbitrary complex weights `a, b : ℕ → ℂ`, `1 ≤ q`, `gcd(p, q) = 1`, and `|α - p/q| ≤ 1/q^2`,
`‖∑_{m=1}^M ∑_{n=1}^N a_m b_n e(α m n)‖^2 ≤ 11 (∑_{m=1}^M ‖a_m‖^2) (∑_{n=1}^N ‖b_n‖^2) (M N / q + M + N + q) (log q + 1)`. -/
theorem bilinear_minor_arc_bound (a b : ℕ → ℂ) {α : ℝ} {p : ℤ} {q M N : ℕ}
    (hq : 1 ≤ q) (hcop : Int.gcd p q = 1)
    (happrox : |α - (p : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, a m * b n * e (α * (m : ℝ) * (n : ℝ))‖ ^ 2 ≤
      11 * (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) * (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
        ((M : ℝ) * (N : ℝ) / (q : ℝ) + (M : ℝ) + (N : ℝ) + (q : ℝ)) *
        (Real.log (q : ℝ) + 1) := by
  set B : ℕ → ℂ := fun m => ∑ n ∈ Finset.Icc 1 N, b n * e (α * (m : ℝ) * (n : ℝ))
  have hfactor : ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        a m * b n * e (α * (m : ℝ) * (n : ℝ)) =
      ∑ m ∈ Finset.Icc 1 M, a m * B m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp [B]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [hfactor]
  -- Step 1: Cauchy–Schwarz in `m`
  have hCS : ‖∑ m ∈ Finset.Icc 1 M, a m * B m‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) * (∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2) := by
    calc ‖∑ m ∈ Finset.Icc 1 M, a m * B m‖ ^ 2
        ≤ (∑ m ∈ Finset.Icc 1 M, ‖a m‖ * ‖B m‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          calc ‖∑ m ∈ Finset.Icc 1 M, a m * B m‖
              ≤ ∑ m ∈ Finset.Icc 1 M, ‖a m * B m‖ := norm_sum_le _ _
            _ = ∑ m ∈ Finset.Icc 1 M, ‖a m‖ * ‖B m‖ := by simp_rw [norm_mul]
      _ ≤ (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) * (∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 M) (fun m => ‖a m‖) (fun m => ‖B m‖)
  -- Step 2: Expand `∑_{m=1}^M ‖B m‖^2` and sum over `m` first
  have hB2_eq : ((∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
        b n₁ * star (b n₂) * ∑ m ∈ Finset.Icc 1 M, e ((m : ℝ) * (α * ((n₁ : ℝ) - (n₂ : ℝ)))) := by
    rw [Complex.ofReal_sum]
    have hpt : ∀ m ∈ Finset.Icc 1 M, ((‖B m‖ ^ 2 : ℝ) : ℂ) =
        ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
          b n₁ * star (b n₂) * e ((m : ℝ) * (α * ((n₁ : ℝ) - (n₂ : ℝ)))) := by
      intro m _
      rw [Complex.ofReal_pow, ← Complex.mul_conj']
      dsimp [B]
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
      rw [map_mul]
      change b n₁ * e (α * (m : ℝ) * (n₁ : ℝ)) *
          (star (b n₂) * star (e (α * (m : ℝ) * (n₂ : ℝ)))) = _
      rw [← e_neg]
      calc b n₁ * e (α * (m : ℝ) * (n₁ : ℝ)) *
            (star (b n₂) * e (-(α * (m : ℝ) * (n₂ : ℝ))))
          = b n₁ * star (b n₂) *
            (e (α * (m : ℝ) * (n₁ : ℝ)) * e (-(α * (m : ℝ) * (n₂ : ℝ)))) := by ring
        _ = b n₁ * star (b n₂) * e ((m : ℝ) * (α * ((n₁ : ℝ) - (n₂ : ℝ)))) := by
            rw [← e_add]; congr 2; ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n₂ _ => ?_
    rw [Finset.mul_sum]
  have hB2_bound : ∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2 ≤
      (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
        ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ))) := by
    have hnorm_eq : ‖((∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2 : ℝ) : ℂ)‖ =
        ∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rw [← hnorm_eq, hB2_eq]
    calc ‖∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
            b n₁ * star (b n₂) * ∑ m ∈ Finset.Icc 1 M, e ((m : ℝ) * (α * ((n₁ : ℝ) - (n₂ : ℝ))))‖
        ≤ ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
            ‖b n₁‖ * ‖b n₂‖ * ‖∑ m ∈ Finset.Icc 1 M, e ((m : ℝ) * (α * ((n₁ : ℝ) - (n₂ : ℝ))))‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₁ _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₂ _ => ?_)
          rw [norm_mul, norm_mul, norm_star]
      _ ≤ ∑ n₁ ∈ Finset.Icc 1 N, ∑ n₂ ∈ Finset.Icc 1 N,
            ‖b n₁‖ * ‖b n₂‖ * minRecipDist (M : ℝ) (α * ((n₁ : ℝ) - (n₂ : ℝ))) := by
          refine Finset.sum_le_sum fun n₁ _ => Finset.sum_le_sum fun n₂ _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine (norm_sum_e_Icc_le_minRecipDist 1 M _).trans (minRecipDist_mono ?_ _)
          rw [Nat.card_Icc]; exact_mod_cast (by omega : M + 1 - 1 ≤ M)
      _ = (∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 = p.2),
              ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))) +
          (∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.2 < p.1),
              ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))) +
          (∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 < p.2),
              ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ)))) := by
          set P := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
          rw [← Finset.sum_product', add_assoc, ← Finset.sum_filter_add_sum_filter_not P (fun p => p.1 = p.2)]
          congr 1
          rw [← Finset.sum_filter_add_sum_filter_not (P.filter (fun p => ¬ p.1 = p.2)) (fun p => p.2 < p.1)]
          congr 1
          · refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext p; simp only [Finset.mem_filter]
            exact ⟨fun ⟨⟨hP, _⟩, hlt⟩ => ⟨hP, hlt⟩, fun ⟨hP, hlt⟩ => ⟨⟨hP, by omega⟩, hlt⟩⟩
          · refine Finset.sum_congr ?_ (fun _ _ => rfl)
            ext p; simp only [Finset.mem_filter]
            exact ⟨fun ⟨⟨hP, hne⟩, hnot⟩ => ⟨hP, by omega⟩, fun ⟨hP, hlt⟩ => ⟨⟨hP, by omega⟩, by omega⟩⟩
      _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) * (M : ℝ) +
          2 * ((∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
            ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ))) := by
          set P := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
          have hD : ∑ p ∈ P.filter (fun p => p.1 = p.2),
                ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
              (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) * (M : ℝ) := by
            rw [Finset.sum_mul]
            have hbij : ∑ p ∈ P.filter (fun p => p.1 = p.2),
                  ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) =
                ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 * minRecipDist (M : ℝ) 0 := by
              refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
              · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
              · intro p₁ h1 p₂ h2 heq
                have hp1 := (Finset.mem_filter.mp h1).2
                have hp2 := (Finset.mem_filter.mp h2).2
                exact Prod.ext heq (hp1.symm.trans (heq.trans hp2))
              · intro n hn
                exact ⟨(n, n), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hn, hn⟩, rfl⟩, rfl⟩
              · intro p hp
                have heq := (Finset.mem_filter.mp hp).2
                rw [heq, sub_self, mul_zero, pow_two]
            rw [hbij]
            refine Finset.sum_le_sum fun n _ =>
              mul_le_mul_of_nonneg_left (minRecipDist_le (M : ℝ) 0) (sq_nonneg _)
          have hAMGM : ∀ h : ℕ, 1 ≤ h →
              ∑ n ∈ Finset.Icc 1 (N - h), ‖b (n + h)‖ * ‖b n‖ ≤
                ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
            intro h hh
            calc ∑ n ∈ Finset.Icc 1 (N - h), ‖b (n + h)‖ * ‖b n‖
                ≤ ∑ n ∈ Finset.Icc 1 (N - h), (‖b (n + h)‖ ^ 2 + ‖b n‖ ^ 2) / 2 :=
                  Finset.sum_le_sum fun n _ => by nlinarith [sq_nonneg (‖b (n + h)‖ - ‖b n‖)]
              _ = ((∑ n ∈ Finset.Icc 1 (N - h), ‖b (n + h)‖ ^ 2) +
                   (∑ n ∈ Finset.Icc 1 (N - h), ‖b n‖ ^ 2)) / 2 := by
                  rw [← Finset.sum_div, Finset.sum_add_distrib]
              _ ≤ ((∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) +
                   (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) / 2 := by
                  refine div_le_div_of_nonneg_right (add_le_add ?_ ?_) (by norm_num)
                  · have hsub1 : (Finset.Icc 1 (N - h)).image (· + h) ⊆ Finset.Icc 1 N := by
                      intro k hk
                      rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
                      simp only [Finset.mem_Icc] at hn ⊢; omega
                    rw [← Finset.sum_image (f := fun k => ‖b k‖ ^ 2) (fun _ _ _ _ heq => by omega)]
                    exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => sq_nonneg _
                  · exact Finset.sum_le_sum_of_subset_of_nonneg
                      (Finset.Icc_subset_Icc_right (Nat.sub_le N h)) fun _ _ _ => sq_nonneg _
              _ = ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by ring
          have hU : ∑ p ∈ P.filter (fun p => p.2 < p.1),
                ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) ≤
              (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
                ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ)) := by
            have hbij : ∑ p ∈ P.filter (fun p => p.2 < p.1),
                  ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) =
                ∑ h ∈ Finset.Icc 1 (N - 1),
                  (∑ n ∈ Finset.Icc 1 (N - h), ‖b (n + h)‖ * ‖b n‖) *
                    minRecipDist (M : ℝ) (α * (h : ℝ)) := by
              simp_rw [Finset.sum_mul]
              rw [Finset.sum_sigma']
              refine Finset.sum_bij (fun p _ => (⟨p.1 - p.2, p.2⟩ : (h : ℕ) × ℕ)) ?_ ?_ ?_ ?_
              · intro p hp
                simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_sigma] at hp ⊢
                omega
              · intro p₁ h1 p₂ h2 heq
                simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
                simp only [Finset.mem_filter] at h1 h2
                exact Prod.ext (by omega) heq.2
              · intro ⟨h, n⟩ hx
                simp only [Finset.mem_sigma, Finset.mem_Icc] at hx
                have hle_hN : h ≤ N := by
                  by_contra hgt
                  have : N - h = 0 := Nat.sub_eq_zero_of_le (by omega)
                  omega
                have hnh : n + h ≤ N := Nat.add_le_of_le_sub hle_hN hx.2.2
                have hn_le : n ≤ N := hx.2.2.trans (Nat.sub_le N h)
                refine ⟨(n + h, n), ?_, ?_⟩
                · simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
                · simp only [Sigma.mk.inj_iff, heq_eq_eq]; exact ⟨by omega, trivial⟩
              · intro p hp
                have hlt : p.2 < p.1 := (Finset.mem_filter.mp hp).2
                have h1 : p.2 + (p.1 - p.2) = p.1 := by omega
                have h2 : ((p.1 - p.2 : ℕ) : ℝ) = (p.1 : ℝ) - (p.2 : ℝ) := Nat.cast_sub hlt.le
                rw [h1, h2]
            rw [hbij, Finset.mul_sum]
            refine Finset.sum_le_sum fun h hh =>
              mul_le_mul_of_nonneg_right (hAMGM h (Finset.mem_Icc.mp hh).1)
                (minRecipDist_nonneg (Nat.cast_nonneg M) _)
          have hL : ∑ p ∈ P.filter (fun p => p.1 < p.2),
                ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) =
              ∑ p ∈ P.filter (fun p => p.2 < p.1),
                ‖b p.1‖ * ‖b p.2‖ * minRecipDist (M : ℝ) (α * ((p.1 : ℝ) - (p.2 : ℝ))) := by
            refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
            · intro p hp
              simp only [P, Finset.mem_filter, Finset.mem_product] at hp ⊢
              exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
            · intro p₁ _ p₂ _ heq
              simp only [Prod.mk.injEq] at heq
              exact Prod.ext heq.2 heq.1
            · intro p hp
              simp only [P, Finset.mem_filter, Finset.mem_product] at hp
              exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1.2, hp.1.1⟩, hp.2⟩, rfl⟩
            · intro p _
              have hneg : α * ((p.1 : ℝ) - (p.2 : ℝ)) = -(α * ((p.2 : ℝ) - (p.1 : ℝ))) := by ring
              rw [hneg, minRecipDist_neg]
              ring
          linarith
      _ = (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
            ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ))) := by
          ring
  -- Step 3: Apply `vinogradov_minRecipDist_sum`
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have happrox2 : |α - (p : ℝ) / (q : ℝ)| ≤ 2 / (q : ℝ) ^ 2 :=
    happrox.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity))
  have hvin := vinogradov_minRecipDist_sum (M := N - 1) (N := (M : ℝ))
    hq hcop happrox2 (Nat.cast_nonneg M)
  have hNm1 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
  have hlog_ge1 : 1 ≤ Real.log (q : ℝ) + 1 := by
    linarith [Real.log_nonneg (by exact_mod_cast hq : (1 : ℝ) ≤ (q : ℝ))]
  have hvin2 : (M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ)) ≤
      11 * ((M : ℝ) * (N : ℝ) / (q : ℝ) + (M : ℝ) + (N : ℝ) + (q : ℝ)) *
        (Real.log (q : ℝ) + 1) := by
    have hstep1 : ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ)) ≤
        ((N : ℝ) / (q : ℝ) + 1) * (5 * (M : ℝ) + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) :=
      hvin.trans (mul_le_mul_of_nonneg_right
        (by linarith [div_le_div_of_nonneg_right hNm1 hq_pos.le]) (by positivity))
    have hexpand : ((N : ℝ) / (q : ℝ) + 1) * (5 * (M : ℝ) + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1)) =
        5 * ((M : ℝ) * (N : ℝ) / (q : ℝ)) + 5 * (M : ℝ) +
          (2 * (N : ℝ) + 2 * (q : ℝ)) * (Real.log (q : ℝ) + 1) := by
      field_simp [hq_pos.ne']
    rw [hexpand] at hstep1
    have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hMNq_nn : (0 : ℝ) ≤ (M : ℝ) * (N : ℝ) / (q : ℝ) := by positivity
    nlinarith
  have ha_nn : 0 ≤ ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb_nn : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖∑ m ∈ Finset.Icc 1 M, a m * B m‖ ^ 2
      ≤ (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) * (∑ m ∈ Finset.Icc 1 M, ‖B m‖ ^ 2) := hCS
    _ ≤ (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          ((∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
            ((M : ℝ) + 2 * ∑ h ∈ Finset.Icc 1 (N - 1), minRecipDist (M : ℝ) (α * (h : ℝ)))) :=
        mul_le_mul_of_nonneg_left hB2_bound ha_nn
    _ ≤ (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          ((∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
            (11 * ((M : ℝ) * (N : ℝ) / (q : ℝ) + (M : ℝ) + (N : ℝ) + (q : ℝ)) *
              (Real.log (q : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hvin2 hb_nn) ha_nn
    _ = 11 * (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) * (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) *
          ((M : ℝ) * (N : ℝ) / (q : ℝ) + (M : ℝ) + (N : ℝ) + (q : ℝ)) *
          (Real.log (q : ℝ) + 1) := by ring

/-- **Type I Linear Exponential-Sum Minor-Arc Bound**:
For bounded outer weights `‖a d‖ ≤ A` on `1 ≤ d ≤ D` and inner intervals of length `≤ K`,
`‖∑_{d=1}^D a_d ∑_{m=L_d}^{R_d} e(α d m)‖ ≤ A * (D / q + 1) * (5 K + 2 q (log q + 1))`. -/
theorem typeI_minor_arc_bound (a : ℕ → ℂ) (L R : ℕ → ℕ) {α : ℝ} {p : ℤ} {q D : ℕ} {A K : ℝ}
    (hq : 1 ≤ q) (hcop : Int.gcd p q = 1)
    (happrox : |α - (p : ℝ) / (q : ℝ)| ≤ 2 / (q : ℝ) ^ 2)
    (hA : 0 ≤ A) (ha_le : ∀ d ∈ Finset.Icc 1 D, ‖a d‖ ≤ A)
    (hK : 0 ≤ K) (hcard_le : ∀ d ∈ Finset.Icc 1 D, ((Finset.Icc (L d) (R d)).card : ℝ) ≤ K) :
    ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ m ∈ Finset.Icc (L d) (R d), e (α * (d : ℝ) * (m : ℝ))‖ ≤
      A * (((D : ℝ) / (q : ℝ) + 1) * (5 * K + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1))) := by
  calc ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ m ∈ Finset.Icc (L d) (R d), e (α * (d : ℝ) * (m : ℝ))‖
      ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d * ∑ m ∈ Finset.Icc (L d) (R d), e (α * (d : ℝ) * (m : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 D, A * minRecipDist K (α * (d : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [norm_mul]
        have hinner : ‖∑ m ∈ Finset.Icc (L d) (R d), e (α * (d : ℝ) * (m : ℝ))‖ ≤
            minRecipDist K (α * (d : ℝ)) := by
          have hrew : ∑ m ∈ Finset.Icc (L d) (R d), e (α * (d : ℝ) * (m : ℝ)) =
              ∑ m ∈ Finset.Icc (L d) (R d), e ((m : ℝ) * (α * (d : ℝ))) :=
            Finset.sum_congr rfl fun m _ => by congr 1; ring
          rw [hrew]
          exact (norm_sum_e_Icc_le_minRecipDist (L d) (R d) _).trans
            (minRecipDist_mono (hcard_le d hd) _)
        exact mul_le_mul (ha_le d hd) hinner (norm_nonneg _) hA
    _ = A * ∑ d ∈ Finset.Icc 1 D, minRecipDist K (α * (d : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ A * (((D : ℝ) / (q : ℝ) + 1) * (5 * K + 2 * (q : ℝ) * (Real.log (q : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (vinogradov_minRecipDist_sum hq hcop happrox hK) hA

/-- **Direct Vaughan-to-Circle-Method Bridge** (pairing with `Arith4Ext.SieveCharacters.vaughan_bilinear_sum`):
Decomposes the prime exponential sum `∑_{U < n ≤ N} Λ(n) e(α n)` into Type I_1, Type I_2, and Type II
bilinear exponential sums directly amenable to `typeI_minor_arc_bound` and `bilinear_minor_arc_bound`. -/
theorem vaughan_expSum_decomp (α : ℝ) {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) (N : ℕ) :
    ∑ n ∈ Finset.Ioc U N, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * e (α * (n : ℝ)) =
      (∑ d ∈ Finset.Icc 1 V, (ArithmeticFunction.moebius d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 (N / d)).filter (fun m => U < d * m),
            (Real.log (m : ℝ) : ℂ) * e (α * (d : ℝ) * (m : ℝ))) -
      (∑ d ∈ Finset.Icc 1 (U * V), (Arith4Ext.SieveCharacters.vaughanCoeffI U V d : ℂ) *
          ∑ m ∈ (Finset.Icc 1 (N / d)).filter (fun m => U < d * m),
            e (α * (d : ℝ) * (m : ℝ))) -
      (∑ m ∈ Finset.Ioc U (N / V), ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ) *
          ∑ k ∈ Finset.Ioc V (N / m), (Arith4Ext.SieveCharacters.vaughanCoeffII V k : ℂ) *
            e (α * (m : ℝ) * (k : ℝ))) := by
  have hv := Arith4Ext.SieveCharacters.vaughan_bilinear_sum (fun n => e (α * (n : ℝ))) hU hV N
  simpa only [Nat.cast_mul, mul_assoc] using hv

/-! ## Section 4: Schnirelmann Density, Schnirelmann's Theorem & Mann's 1942 Sharp Theorem -/

/-- The counting function `A(n) = |A ∩ {1, ..., n}|` for a set `A ⊆ ℕ`. -/
def schnirelmannCount (A : Set ℕ) (n : ℕ) : ℕ := by
  classical exact ((Finset.Icc 1 n).filter (· ∈ A)).card

/-- The **Schnirelmann density** `σ(A) = inf_{n ≥ 1} A(n) / n`. -/
def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf (Set.range fun k : ℕ => (schnirelmannCount A (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ))

/-- The Minkowski sumset `A + B = { a + b | a ∈ A, b ∈ B }`. -/
def sumset (A B : Set ℕ) : Set ℕ :=
  { c : ℕ | ∃ a ∈ A, ∃ b ∈ B, a + b = c }

/-- The `k`-fold iterated sumset `k A = A + ... + A` (`0 A = {0}`). -/
def iterSumset (A : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => sumset (iterSumset A k) A

lemma zero_mem_sumset {A B : Set ℕ} (h0A : 0 ∈ A) (h0B : 0 ∈ B) : 0 ∈ sumset A B :=
  ⟨0, h0A, 0, h0B, rfl⟩

lemma zero_mem_iterSumset {A : Set ℕ} (h0A : 0 ∈ A) (k : ℕ) : 0 ∈ iterSumset A k := by
  induction k with
  | zero => exact Set.mem_singleton 0
  | succ k ih => exact zero_mem_sumset ih h0A

lemma schnirelmannCount_le (A : Set ℕ) (n : ℕ) : schnirelmannCount A n ≤ n := by
  classical
  unfold schnirelmannCount
  calc ((Finset.Icc 1 n).filter (· ∈ A)).card
      ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n := by rw [Nat.card_Icc]; omega

lemma schnirelmannDensity_nonneg (A : Set ℕ) : 0 ≤ schnirelmannDensity A := by
  unfold schnirelmannDensity
  refine Real.sInf_nonneg ?_
  rintro x ⟨k, rfl⟩
  positivity

lemma schnirelmannDensity_le_div (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n) :
    schnirelmannDensity A ≤ (schnirelmannCount A n : ℝ) / (n : ℝ) := by
  unfold schnirelmannDensity
  have hbdd : BddBelow (Set.range fun k : ℕ => (schnirelmannCount A (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩
  have hmem : (schnirelmannCount A n : ℝ) / (n : ℝ) ∈
      Set.range fun k : ℕ => (schnirelmannCount A (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) :=
    ⟨n - 1, by dsimp only; rw [Nat.sub_add_cancel hn]⟩
  exact csInf_le hbdd hmem

lemma schnirelmannDensity_le_one (A : Set ℕ) : schnirelmannDensity A ≤ 1 := by
  calc schnirelmannDensity A
      ≤ (schnirelmannCount A 1 : ℝ) / (1 : ℝ) := by simpa using schnirelmannDensity_le_div A le_rfl
    _ ≤ (1 : ℝ) / (1 : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast schnirelmannCount_le A 1) zero_le_one
    _ = 1 := by norm_num

lemma le_schnirelmannDensity_iff (A : Set ℕ) (γ : ℝ) :
    γ ≤ schnirelmannDensity A ↔
      ∀ n : ℕ, 1 ≤ n → γ * (n : ℝ) ≤ (schnirelmannCount A n : ℝ) := by
  unfold schnirelmannDensity
  have hne : (Set.range fun k : ℕ => (schnirelmannCount A (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ)).Nonempty :=
    ⟨_, 0, rfl⟩
  rw [le_csInf_iff
    ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩ hne]
  constructor
  · intro h n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hle : γ ≤ (schnirelmannCount A n : ℝ) / (n : ℝ) :=
      h _ ⟨n - 1, by dsimp only; rw [Nat.sub_add_cancel hn]⟩
    exact (le_div_iff₀ hn_pos).mp hle
  · rintro h _ ⟨k, rfl⟩
    have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    exact (le_div_iff₀ hk_pos).mpr (h (k + 1) (Nat.succ_pos k))

lemma schnirelmannDensity_eq_one_iff {A : Set ℕ} :
    schnirelmannDensity A = 1 ↔ ∀ n : ℕ, 1 ≤ n → n ∈ A := by
  constructor
  · intro h1 n hn
    have hle := (le_schnirelmannDensity_iff A 1).mp h1.ge n hn
    rw [one_mul] at hle
    have hcard_ge : n ≤ schnirelmannCount A n := by exact_mod_cast hle
    have hcard_eq : schnirelmannCount A n = n := le_antisymm (schnirelmannCount_le A n) hcard_ge
    classical
    have hsub_eq : (Finset.Icc 1 n).filter (· ∈ A) = Finset.Icc 1 n := by
      refine Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) ?_
      rw [Nat.card_Icc, show n + 1 - 1 = n by omega]
      exact hcard_ge
    have hmem : n ∈ (Finset.Icc 1 n).filter (· ∈ A) := by
      rw [hsub_eq]; exact Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
    exact (Finset.mem_filter.mp hmem).2
  · intro hall
    refine le_antisymm (schnirelmannDensity_le_one A) ?_
    rw [le_schnirelmannDensity_iff]
    intro n hn
    rw [one_mul]
    classical
    have hsub_eq : (Finset.Icc 1 n).filter (· ∈ A) = Finset.Icc 1 n := by
      ext x; simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨fun h => h.1, fun h => ⟨h, hall x h.1⟩⟩
    have hcnt : schnirelmannCount A n = n := by
      unfold schnirelmannCount
      rw [hsub_eq, Nat.card_Icc]; omega
    exact_mod_cast hcnt.ge

/-! ### Dyson's `e`-Transform & Finite Mann Theorem -/

private def finCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.filter (fun x => 1 ≤ x ∧ x ≤ n)).card

private def finSumset (A B : Finset ℕ) : Finset ℕ :=
  (A ×ˢ B).image (fun p => p.1 + p.2)

private lemma mem_finSumset_iff {A B : Finset ℕ} {c : ℕ} :
    c ∈ finSumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = c := by
  simp only [finSumset, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h⟩; exact ⟨a, ha, b, hb, h⟩
  · rintro ⟨a, ha, b, hb, h⟩; exact ⟨a, b, ⟨ha, hb⟩, h⟩

private lemma finCount_zero (A : Finset ℕ) : finCount A 0 = 0 := by
  unfold finCount
  have h : A.filter (fun x => 1 ≤ x ∧ x ≤ 0) = ∅ := by
    ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]; omega
  rw [h, Finset.card_empty]

private lemma finCount_mono_set {A B : Finset ℕ} (hAB : A ⊆ B) (n : ℕ) :
    finCount A n ≤ finCount B n :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

private lemma finCount_mono_nat (A : Finset ℕ) {m n : ℕ} (hmn : m ≤ n) :
    finCount A m ≤ finCount A n := by
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, hx.2.2.trans hmn⟩

private lemma finCount_split (A : Finset ℕ) {k m : ℕ} (hkm : k ≤ m) :
    finCount A m = finCount A k + (A.filter (fun x => k < x ∧ x ≤ m)).card := by
  unfold finCount
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_union]
    exact ⟨fun ⟨hxA, h1, h2⟩ => if hxk : x ≤ k then Or.inl ⟨hxA, h1, hxk⟩ else Or.inr ⟨hxA, by omega, h2⟩,
      fun h => by rcases h with ⟨hxA, h1, h2⟩ | ⟨hxA, h1, h2⟩ <;> exact ⟨hxA, by omega, by omega⟩⟩
  · rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_filter] at h1 h2
    omega

/-- Fundamental counting identity for Dyson's `e`-transform:
For `0 ∈ B`, `e ∈ A`, and `e ≤ m ≤ N`,
`A'(m) + B'(m - e) = A(m) + B(m - e)`. -/
private lemma finCount_dyson_e_eq {N e m : ℕ} {A B : Finset ℕ}
    (h0B : 0 ∈ B) (heA : e ∈ A) (hem : e ≤ m) (hmN : m ≤ N) :
    finCount ((A ∪ B.image (· + e)).filter (· ≤ N)) m +
      finCount (B.filter (fun b => b + e ∈ A)) (m - e) =
    finCount A m + finCount B (m - e) := by
  set A' := (A ∪ B.image (· + e)).filter (· ≤ N)
  set B' := B.filter (fun b => b + e ∈ A)
  set X := A.filter (fun x => 1 ≤ x ∧ x ≤ m)
  set Y := (B.image (· + e)).filter (fun x => 1 ≤ x ∧ x ≤ m)
  have hXY_union : A'.filter (fun x => 1 ≤ x ∧ x ≤ m) = X ∪ Y := by
    ext x
    simp only [A', X, Y, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      rcases h1 with hA | hB
      · exact Or.inl ⟨hA, h2⟩
      · exact Or.inr ⟨hB, h2⟩
    · rintro (⟨hA, h2⟩ | ⟨hB, h2⟩)
      · exact ⟨⟨Or.inl hA, h2.2.trans hmN⟩, h2⟩
      · exact ⟨⟨Or.inr hB, h2.2.trans hmN⟩, h2⟩
  set Z := B.filter (fun b => 1 ≤ b + e ∧ b + e ≤ m)
  set Z' := B'.filter (fun b => 1 ≤ b + e ∧ b + e ≤ m)
  have hY_eq : Y = Z.image (· + e) := by
    ext x
    simp only [Y, Z, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, h1, h2⟩; exact ⟨b, ⟨hb, h1, h2⟩, rfl⟩
    · rintro ⟨b, ⟨hb, h1, h2⟩, rfl⟩; exact ⟨⟨b, hb, rfl⟩, h1, h2⟩
  have hXY_inter : X ∩ Y = Z'.image (· + e) := by
    ext x
    simp only [X, Y, Z', B', Finset.mem_inter, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨hxA, h1, h2⟩, ⟨b, hb, rfl⟩, _⟩
      exact ⟨b, ⟨⟨hb, hxA⟩, h1, h2⟩, rfl⟩
    · rintro ⟨b, ⟨⟨hb, hbeA⟩, h1, h2⟩, rfl⟩
      exact ⟨⟨hbeA, h1, h2⟩, ⟨b, hb, rfl⟩, h1, h2⟩
  have hcard_Y : Y.card = Z.card := by
    rw [hY_eq, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
  have hcard_inter : (X ∩ Y).card = Z'.card := by
    rw [hXY_inter, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
  have hinc := Finset.card_union_add_card_inter X Y
  rw [← hXY_union, hcard_Y, hcard_inter] at hinc
  change finCount A' m + Z'.card = finCount A m + Z.card at hinc
  by_cases he0 : e = 0
  · subst he0
    have hZ : Z = B.filter (fun b => 1 ≤ b ∧ b ≤ m - 0) := by
      ext b; simp only [Z, Finset.mem_filter]
      exact ⟨fun ⟨hb, h1, h2⟩ => ⟨hb, by omega, by omega⟩, fun ⟨hb, h1, h2⟩ => ⟨hb, by omega, by omega⟩⟩
    have hZ' : Z' = B'.filter (fun b => 1 ≤ b ∧ b ≤ m - 0) := by
      ext b; simp only [Z', Finset.mem_filter]
      exact ⟨fun ⟨hb, h1, h2⟩ => ⟨hb, by omega, by omega⟩, fun ⟨hb, h1, h2⟩ => ⟨hb, by omega, by omega⟩⟩
    rw [hZ, hZ'] at hinc
    exact hinc
  · have hZ : Z = insert 0 (B.filter (fun b => 1 ≤ b ∧ b ≤ m - e)) := by
      ext b; simp only [Z, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hb, h1, h2⟩
        by_cases hb0 : b = 0
        · exact Or.inl hb0
        · exact Or.inr ⟨hb, by omega, by omega⟩
      · rintro (rfl | ⟨hb, h1, h2⟩)
        · exact ⟨h0B, by omega, by omega⟩
        · exact ⟨hb, by omega, by omega⟩
    have h0B' : 0 ∈ B' := Finset.mem_filter.mpr ⟨h0B, by simpa using heA⟩
    have hZ' : Z' = insert 0 (B'.filter (fun b => 1 ≤ b ∧ b ≤ m - e)) := by
      ext b; simp only [Z', Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hb, h1, h2⟩
        by_cases hb0 : b = 0
        · exact Or.inl hb0
        · exact Or.inr ⟨hb, by omega, by omega⟩
      · rintro (rfl | ⟨hb, h1, h2⟩)
        · exact ⟨h0B', by omega, by omega⟩
        · exact ⟨hb, by omega, by omega⟩
    rw [hZ, hZ', Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp)] at hinc
    change finCount A' m + (finCount B' (m - e) + 1) = finCount A m + (finCount B (m - e) + 1) at hinc
    omega

/-- **Finite Mann–Dyson Theorem**:
For any `N : ℕ`, `0 ≤ γ ≤ 1`, and finite sets `A, B ⊆ {0, ..., N}` with `0 ∈ A`, `0 ∈ B`
satisfying `A(m) + B(m) ≥ γ m` for all `1 ≤ m ≤ N`, we have `(A + B)(N) ≥ γ N`. -/
private lemma mann_dyson_finite (N : ℕ) (γ : ℝ) (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∀ k : ℕ, ∀ A B : Finset ℕ,
      finCount B N = k →
      0 ∈ A → 0 ∈ B →
      (∀ a ∈ A, a ≤ N) → (∀ b ∈ B, b ≤ N) →
      (∀ m ∈ Finset.Icc 1 N, γ * (m : ℝ) ≤ (finCount A m : ℝ) + (finCount B m : ℝ)) →
      γ * (N : ℝ) ≤ (finCount (finSumset A B) N : ℝ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A B hk h0A h0B hA_le hB_le hsum
    by_cases hN0 : N = 0
    · subst hN0; simp [finCount_zero]
    have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
    by_cases hk0 : k = 0
    · -- Base case: `B ∩ [1, N] = ∅`
      have hA_sub : A ⊆ finSumset A B := fun a ha =>
        mem_finSumset_iff.mpr ⟨a, ha, 0, h0B, add_zero a⟩
      have hN_sum := hsum N (Finset.mem_Icc.mpr ⟨hN1, le_rfl⟩)
      rw [hk, hk0, Nat.cast_zero, add_zero] at hN_sum
      exact hN_sum.trans (by exact_mod_cast finCount_mono_set hA_sub N)
    · -- Inductive step: `B ∩ [1, N]` is nonempty; apply Dyson's `e`-transform!
      set Bpos := B.filter (fun b => 1 ≤ b)
      have hBpos_ne : Bpos.Nonempty := by
        have hpos : 0 < (B.filter (fun x => 1 ≤ x ∧ x ≤ N)).card := by
          change 0 < finCount B N; omega
        rcases Finset.card_pos.mp hpos with ⟨b, hb⟩
        have hb' := Finset.mem_filter.mp hb
        exact ⟨b, Finset.mem_filter.mpr ⟨hb'.1, hb'.2.1⟩⟩
      set S := A.filter (fun a => ∃ b ∈ Bpos, a + b ∉ A)
      have hS_ne : S.Nonempty := by
        set amax := A.max' ⟨0, h0A⟩
        rcases hBpos_ne with ⟨b1, hb1⟩
        have hb1_ge : 1 ≤ b1 := (Finset.mem_filter.mp hb1).2
        refine ⟨amax, Finset.mem_filter.mpr ⟨Finset.max'_mem A ⟨0, h0A⟩, b1, hb1, ?_⟩⟩
        intro hmem
        have hle := Finset.le_max' A (amax + b1) hmem
        omega
      set e := S.min' hS_ne
      have heS : e ∈ S := Finset.min'_mem S hS_ne
      have heA : e ∈ A := (Finset.mem_filter.mp heS).1
      have hP1 : ∃ b ∈ Bpos, e + b ∉ A := (Finset.mem_filter.mp heS).2
      have hP2 : ∀ a ∈ A, a < e → ∀ b ∈ Bpos, a + b ∈ A := by
        intro a ha hale b hb
        by_contra hnot
        have haS : a ∈ S := Finset.mem_filter.mpr ⟨ha, b, hb, hnot⟩
        have hle : e ≤ a := Finset.min'_le S a haS
        omega
      set A' := (A ∪ B.image (· + e)).filter (· ≤ N)
      set B' := B.filter (fun b => b + e ∈ A)
      have h0A' : 0 ∈ A' := Finset.mem_filter.mpr ⟨Finset.mem_union_left _ h0A, Nat.zero_le N⟩
      have h0B' : 0 ∈ B' := Finset.mem_filter.mpr ⟨h0B, by simpa using heA⟩
      have hA'_le : ∀ a ∈ A', a ≤ N := fun a ha => (Finset.mem_filter.mp ha).2
      have hB'_le : ∀ b ∈ B', b ≤ N := fun b hb => hB_le b (Finset.mem_filter.mp hb).1
      have hsum_sub : finSumset A' B' ⊆ finSumset A B := by
        intro c hc
        rcases mem_finSumset_iff.mp hc with ⟨a', ha', b', hb', rfl⟩
        have ha'_u := (Finset.mem_filter.mp ha').1
        have hb'_f := Finset.mem_filter.mp hb'
        rcases Finset.mem_union.mp ha'_u with haA | haB
        · exact mem_finSumset_iff.mpr ⟨a', haA, b', hb'_f.1, rfl⟩
        · rcases Finset.mem_image.mp haB with ⟨b, hb, rfl⟩
          exact mem_finSumset_iff.mpr ⟨b' + e, hb'_f.2, b, hb, by omega⟩
      have hB'_lt : finCount B' N < k := by
        rw [← hk]
        unfold finCount
        refine Finset.card_lt_card ?_
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset_filter _ (Finset.filter_subset _ _), ?_⟩
        intro heq
        rcases hP1 with ⟨b1, hb1, hnotA⟩
        have hb1_f := Finset.mem_filter.mp hb1
        have hb1_in : b1 ∈ B.filter (fun x => 1 ≤ x ∧ x ≤ N) :=
          Finset.mem_filter.mpr ⟨hb1_f.1, hb1_f.2, hB_le b1 hb1_f.1⟩
        rw [← heq] at hb1_in
        have hb1_B' := (Finset.mem_filter.mp hb1_in).1
        have hbeA : b1 + e ∈ A := (Finset.mem_filter.mp hb1_B').2
        rw [add_comm] at hbeA
        exact hnotA hbeA
      -- Verify `γ * m ≤ A'(m) + B'(m)` for every `m ∈ Icc 1 N`!
      have hsum' : ∀ m ∈ Finset.Icc 1 N,
          γ * (m : ℝ) ≤ (finCount A' m : ℝ) + (finCount B' m : ℝ) := by
        by_cases he0 : e = 0
        · intro m hm
          have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
          have heq := finCount_dyson_e_eq h0B heA (by omega : e ≤ m) hmN
          change finCount A' m + finCount B' (m - e) = finCount A m + finCount B (m - e) at heq
          rw [he0, Nat.sub_zero] at heq
          have heq_r : (finCount A' m : ℝ) + (finCount B' m : ℝ) =
              (finCount A m : ℝ) + (finCount B m : ℝ) := by exact_mod_cast heq
          linarith [hsum m hm]
        · -- Step A: Strong induction proving `∀ t < e, γ * t ≤ A(t)`
          have hStepA : ∀ t : ℕ, t < e → γ * (t : ℝ) ≤ (finCount A t : ℝ) := by
            intro t
            induction t using Nat.strong_induction_on with
            | h t iht =>
              intro ht_lt
              by_cases ht0 : t = 0
              · subst ht0; simp [finCount_zero]
              set bmin := Bpos.min' hBpos_ne
              have hbmin_pos : bmin ∈ Bpos := Finset.min'_mem Bpos hBpos_ne
              have hbmin_ge1 : 1 ≤ bmin := (Finset.mem_filter.mp hbmin_pos).2
              have ht_leN : t ≤ N := le_trans ht_lt.le (hA_le e heA)
              by_cases hlt_b : t < bmin
              · -- `B(t) = 0`, so `A(t) = A(t) + B(t) ≥ γ t`
                have hBt0 : finCount B t = 0 := by
                  unfold finCount
                  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                  intro b hb ⟨hb1, hbt⟩
                  have hle : bmin ≤ b := Finset.min'_le Bpos b (Finset.mem_filter.mpr ⟨hb, hb1⟩)
                  omega
                have hst := hsum t (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero ht0, ht_leN⟩)
                rw [hBt0, Nat.cast_zero, add_zero] at hst
                exact hst
              · by_cases heq_b : t = bmin
                · -- `bmin = 0 + bmin ∈ A` by (P2), so `A(bmin) = A(bmin - 1) + 1 ≥ γ bmin`
                  have hbmin_A : t ∈ A := by
                    rw [heq_b]
                    simpa [zero_add] using hP2 0 h0A (Nat.pos_of_ne_zero he0) bmin hbmin_pos
                  have hsplit := finCount_split A (show t - 1 ≤ t by omega)
                  have hsing : A.filter (fun x => t - 1 < x ∧ x ≤ t) = {t} := by
                    ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
                    constructor
                    · intro ⟨_, h1, h2⟩; omega
                    · rintro rfl; exact ⟨hbmin_A, by omega, le_rfl⟩
                  rw [hsing, Finset.card_singleton] at hsplit
                  have hprev := iht (t - 1) (by omega) (by omega)
                  have ht_cast : (t : ℝ) = ((t - 1 : ℕ) : ℝ) + 1 := by
                    exact_mod_cast (show t = (t - 1) + 1 by omega)
                  have hsplit_r : (finCount A t : ℝ) = (finCount A (t - 1) : ℝ) + 1 := by
                    exact_mod_cast hsplit
                  rw [hsplit_r, ht_cast]
                  nlinarith
                · -- `bmin < t < e`: split `[1, t]` at `bmin` and shift `A ∩ [1, t - bmin]` by `+ bmin`!
                  have hbmin_lt_t : bmin < t := by omega
                  have hsplit := finCount_split A hbmin_lt_t.le
                  have hshift : finCount A (t - bmin) ≤ (A.filter (fun x => bmin < x ∧ x ≤ t)).card := by
                    unfold finCount
                    have hsub : (A.filter (fun x => 1 ≤ x ∧ x ≤ t - bmin)).image (· + bmin) ⊆
                        A.filter (fun x => bmin < x ∧ x ≤ t) := by
                      intro y hy
                      rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
                      have ha' := Finset.mem_filter.mp ha
                      have ha_lt_e : a < e := by omega
                      exact Finset.mem_filter.mpr
                        ⟨hP2 a ha'.1 ha_lt_e bmin hbmin_pos, by omega, by omega⟩
                    rw [← Finset.card_image_of_injective _ (fun _ _ h => by dsimp only at h; omega : Function.Injective (· + bmin))]
                    exact Finset.card_le_card hsub
                  have h1 := iht bmin hbmin_lt_t (by omega)
                  have h2 := iht (t - bmin) (by omega) (by omega)
                  have ht_eq : (t : ℝ) = (bmin : ℝ) + ((t - bmin : ℕ) : ℝ) := by
                    exact_mod_cast (show t = bmin + (t - bmin) by omega)
                  have hge_r : (finCount A bmin : ℝ) + (finCount A (t - bmin) : ℝ) ≤ (finCount A t : ℝ) := by
                    exact_mod_cast (by omega : finCount A bmin + finCount A (t - bmin) ≤ finCount A t)
                  rw [ht_eq]
                  linarith
          -- Now verify `γ * m ≤ A'(m) + B'(m)` for every `m ∈ Icc 1 N`
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
          by_cases hlt_e : m < e
          · -- Step B: `m < e`, so `A'(m) + B'(m) ≥ A(m) ≥ γ m`
            have hA_sub_A' : A ⊆ A' := fun a ha =>
              Finset.mem_filter.mpr ⟨Finset.mem_union_left _ ha, hA_le a ha⟩
            have h1 : (finCount A m : ℝ) ≤ (finCount A' m : ℝ) := by
              exact_mod_cast finCount_mono_set hA_sub_A' m
            have h2 : (0 : ℝ) ≤ (finCount B' m : ℝ) := Nat.cast_nonneg _
            linarith [hStepA m hlt_e]
          · -- Step C: `e ≤ m ≤ N`
            have hem : e ≤ m := Nat.not_lt.mp hlt_e
            have hdyson := finCount_dyson_e_eq h0B heA hem hmN
            change finCount A' m + finCount B' (m - e) = finCount A m + finCount B (m - e) at hdyson
            have hmonoB' : finCount B' (m - e) ≤ finCount B' m := finCount_mono_nat B' (Nat.sub_le m e)
            have hge_dyson : (finCount A m : ℝ) + (finCount B (m - e) : ℝ) ≤
                (finCount A' m : ℝ) + (finCount B' m : ℝ) := by
              exact_mod_cast (by omega : finCount A m + finCount B (m - e) ≤ finCount A' m + finCount B' m)
            set Bmid := B.filter (fun b => m - e < b ∧ b ≤ m)
            by_cases hmid : Bmid.Nonempty
            · set b0 := Bmid.min' hmid
              have hb0_mem : b0 ∈ Bmid := Finset.min'_mem Bmid hmid
              have hb0_f := Finset.mem_filter.mp hb0_mem
              have hb0_B : b0 ∈ B := hb0_f.1
              have hb0_gt : m - e < b0 := hb0_f.2.1
              have hb0_le : b0 ≤ m := hb0_f.2.2
              have hb0_ge1 : 1 ≤ b0 := by omega
              have hb0_pos : b0 ∈ Bpos := Finset.mem_filter.mpr ⟨hb0_B, hb0_ge1⟩
              have hB_eq : finCount B (b0 - 1) = finCount B (m - e) := by
                unfold finCount
                congr 1; ext b; simp only [Finset.mem_filter]
                constructor
                · rintro ⟨hb, hb1, hble⟩
                  refine ⟨hb, hb1, ?_⟩
                  by_contra hgt
                  have hbm : b ∈ Bmid := Finset.mem_filter.mpr ⟨hb, by omega, by omega⟩
                  have hmin := Finset.min'_le Bmid b hbm
                  omega
                · rintro ⟨hb, hb1, hble⟩
                  exact ⟨hb, hb1, by omega⟩
              have hsplitA := finCount_split A (show b0 - 1 ≤ m by omega)
              -- Shift `U := A.filter (· ≤ m - b0)` by `+ b0` into `A.filter (b0 - 1 < · ∧ · ≤ m)`
              set U := A.filter (fun a => a ≤ m - b0)
              have hU_card : U.card = finCount A (m - b0) + 1 := by
                have hU_eq : U = insert 0 (A.filter (fun x => 1 ≤ x ∧ x ≤ m - b0)) := by
                  ext x; simp only [U, Finset.mem_filter, Finset.mem_insert]
                  constructor
                  · intro ⟨hxA, hxle⟩
                    by_cases hx0 : x = 0
                    · exact Or.inl hx0
                    · exact Or.inr ⟨hxA, by omega, hxle⟩
                  · rintro (rfl | ⟨hxA, _, hxle⟩)
                    · exact ⟨h0A, Nat.zero_le _⟩
                    · exact ⟨hxA, hxle⟩
                rw [hU_eq, Finset.card_insert_of_notMem (by simp)]
                rfl
              have hshiftA : U.card ≤ (A.filter (fun x => b0 - 1 < x ∧ x ≤ m)).card := by
                have hsub : U.image (· + b0) ⊆ A.filter (fun x => b0 - 1 < x ∧ x ≤ m) := by
                  intro y hy
                  rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
                  have ha' := Finset.mem_filter.mp ha
                  have ha_lt_e : a < e := by omega
                  exact Finset.mem_filter.mpr ⟨hP2 a ha'.1 ha_lt_e b0 hb0_pos, by omega, by omega⟩
                rw [← Finset.card_image_of_injective _ (fun _ _ h => by dsimp only at h; omega : Function.Injective (· + b0))]
                exact Finset.card_le_card hsub
              have hprev_sum : γ * ((b0 - 1 : ℕ) : ℝ) ≤
                  (finCount A (b0 - 1) : ℝ) + (finCount B (b0 - 1) : ℝ) := by
                by_cases hb01 : b0 = 1
                · rw [hb01]; simp [finCount_zero]
                · exact hsum (b0 - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
              have hrem : γ * ((m - b0 : ℕ) : ℝ) ≤ (finCount A (m - b0) : ℝ) :=
                hStepA (m - b0) (by omega)
              have hcomb_nat :
                  finCount A (b0 - 1) + finCount B (b0 - 1) + finCount A (m - b0) + 1 ≤
                    finCount A m + finCount B (m - e) := by
                omega
              have hcomb_r :
                  (finCount A (b0 - 1) : ℝ) + (finCount B (b0 - 1) : ℝ) +
                    (finCount A (m - b0) : ℝ) + 1 ≤
                  (finCount A m : ℝ) + (finCount B (m - e) : ℝ) := by
                exact_mod_cast hcomb_nat
              have hm_eq : (m : ℝ) = ((b0 - 1 : ℕ) : ℝ) + ((m - b0 : ℕ) : ℝ) + 1 := by
                exact_mod_cast (show m = (b0 - 1) + (m - b0) + 1 by omega)
              rw [hm_eq]
              nlinarith
            · -- `Bmid = ∅`, so `B(m - e) = B(m)`!
              have hB_eq : finCount B (m - e) = finCount B m := by
                unfold finCount
                congr 1; ext b; simp only [Finset.mem_filter]
                constructor
                · rintro ⟨hb, hb1, hble⟩; exact ⟨hb, hb1, hble.trans (Nat.sub_le m e)⟩
                · rintro ⟨hb, hb1, hble⟩
                  refine ⟨hb, hb1, ?_⟩
                  by_contra hgt
                  exact hmid ⟨b, Finset.mem_filter.mpr ⟨hb, by omega, hble⟩⟩
              rw [hB_eq] at hge_dyson
              linarith [hsum m hm]
      -- Apply strong induction to `(A', B')`!
      have hind := ih (finCount B' N) hB'_lt A' B' rfl h0A' h0B' hA'_le hB'_le hsum'
      exact hind.trans (by exact_mod_cast finCount_mono_set hsum_sub N)

/-- **Mann's Theorem (1942 — Sharp Schnirelmann Density Sumset Theorem)**:
For any sets `A, B ⊆ ℕ` containing `0`,
`min 1 (σ(A) + σ(B)) ≤ σ(A + B)`. -/
theorem mann_theorem {A B : Set ℕ} (h0A : 0 ∈ A) (h0B : 0 ∈ B) :
    min 1 (schnirelmannDensity A + schnirelmannDensity B) ≤ schnirelmannDensity (sumset A B) := by
  set γ : ℝ := min 1 (schnirelmannDensity A + schnirelmannDensity B)
  have hγ0 : 0 ≤ γ := le_min zero_le_one (add_nonneg (schnirelmannDensity_nonneg A) (schnirelmannDensity_nonneg B))
  have hγ1 : γ ≤ 1 := min_le_left _ _
  rw [le_schnirelmannDensity_iff]
  intro N hN
  classical
  set Af : Finset ℕ := (Finset.Icc 0 N).filter (· ∈ A)
  set Bf : Finset ℕ := (Finset.Icc 0 N).filter (· ∈ B)
  have h0Af : 0 ∈ Af := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le N⟩, h0A⟩
  have h0Bf : 0 ∈ Bf := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le N⟩, h0B⟩
  have hAf_le : ∀ a ∈ Af, a ≤ N := fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
  have hBf_le : ∀ b ∈ Bf, b ≤ N := fun b hb => (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
  have hAf_cnt : ∀ m ∈ Finset.Icc 1 N, finCount Af m = schnirelmannCount A m := by
    intro m hm
    have hmN := (Finset.mem_Icc.mp hm).2
    unfold finCount schnirelmannCount
    congr 1; ext x; simp only [Af, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_, hxA⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, hxA⟩
    · rintro ⟨⟨h1, h2⟩, hxA⟩; exact ⟨⟨⟨by omega, by omega⟩, hxA⟩, h1, h2⟩
  have hBf_cnt : ∀ m ∈ Finset.Icc 1 N, finCount Bf m = schnirelmannCount B m := by
    intro m hm
    have hmN := (Finset.mem_Icc.mp hm).2
    unfold finCount schnirelmannCount
    congr 1; ext x; simp only [Bf, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨_, hxB⟩, h1, h2⟩; exact ⟨⟨h1, h2⟩, hxB⟩
    · rintro ⟨⟨h1, h2⟩, hxB⟩; exact ⟨⟨⟨by omega, by omega⟩, hxB⟩, h1, h2⟩
  have hsum : ∀ m ∈ Finset.Icc 1 N, γ * (m : ℝ) ≤ (finCount Af m : ℝ) + (finCount Bf m : ℝ) := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    rw [hAf_cnt m hm, hBf_cnt m hm]
    have hA_m := (le_schnirelmannDensity_iff A (schnirelmannDensity A)).mp le_rfl m hm1
    have hB_m := (le_schnirelmannDensity_iff B (schnirelmannDensity B)).mp le_rfl m hm1
    have hγ_le : γ ≤ schnirelmannDensity A + schnirelmannDensity B := min_le_right _ _
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hfin := mann_dyson_finite N γ hγ0 hγ1 (finCount Bf N) Af Bf rfl h0Af h0Bf hAf_le hBf_le hsum
  have hsub_cnt : finCount (finSumset Af Bf) N ≤ schnirelmannCount (sumset A B) N := by
    unfold finCount schnirelmannCount
    refine Finset.card_le_card fun c hc => ?_
    have hc' := Finset.mem_filter.mp hc
    rcases mem_finSumset_iff.mp hc'.1 with ⟨a, ha, b, hb, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hc'.2,
      ⟨a, (Finset.mem_filter.mp ha).2, b, (Finset.mem_filter.mp hb).2, rfl⟩⟩
  exact hfin.trans (by exact_mod_cast hsub_cnt)

/-- **Schnirelmann's Theorem (1930)**:
For any sets `A, B ⊆ ℕ` containing `0`,
`σ(A) + σ(B) - σ(A) * σ(B) ≤ σ(A + B)`. -/
theorem schnirelmann_density_add_ge {A B : Set ℕ} (h0A : 0 ∈ A) (h0B : 0 ∈ B) :
    schnirelmannDensity A + schnirelmannDensity B - schnirelmannDensity A * schnirelmannDensity B ≤
      schnirelmannDensity (sumset A B) := by
  have hA0 := schnirelmannDensity_nonneg A
  have hB0 := schnirelmannDensity_nonneg B
  have hA1 := schnirelmannDensity_le_one A
  have hB1 := schnirelmannDensity_le_one B
  have hle : schnirelmannDensity A + schnirelmannDensity B -
      schnirelmannDensity A * schnirelmannDensity B ≤
      min 1 (schnirelmannDensity A + schnirelmannDensity B) :=
    le_min (by nlinarith) (by nlinarith)
  exact hle.trans (mann_theorem h0A h0B)

/-- **Schnirelmann Sumset Coverage Criterion**:
If `0 ∈ A`, `0 ∈ B`, and `σ(A) + σ(B) ≥ 1`, then `A + B = ℕ`. -/
theorem schnirelmann_add_eq_univ_of_sum_ge_one {A B : Set ℕ} (h0A : 0 ∈ A) (h0B : 0 ∈ B)
    (hge : 1 ≤ schnirelmannDensity A + schnirelmannDensity B) :
    ∀ n : ℕ, n ∈ sumset A B := by
  have h1 : schnirelmannDensity (sumset A B) = 1 :=
    le_antisymm (schnirelmannDensity_le_one _)
      ((le_min le_rfl hge).trans (mann_theorem h0A h0B))
  intro n
  by_cases hn0 : n = 0
  · subst hn0; exact zero_mem_sumset h0A h0B
  · exact schnirelmannDensity_eq_one_iff.mp h1 n (Nat.pos_of_ne_zero hn0)

/-- Lower bound for iterated sumsets via Mann's Theorem:
`min 1 (k * σ(A)) ≤ σ(k A)` for all `k : ℕ` when `0 ∈ A`. -/
theorem schnirelmann_density_iterSumset_ge {A : Set ℕ} (h0A : 0 ∈ A) (k : ℕ) :
    min 1 ((k : ℝ) * schnirelmannDensity A) ≤ schnirelmannDensity (iterSumset A k) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact (min_le_right 1 0).trans (schnirelmannDensity_nonneg _)
  | succ k ih =>
    have hmann := mann_theorem (zero_mem_iterSumset h0A k) h0A
    have hstep : min 1 (((k + 1 : ℕ) : ℝ) * schnirelmannDensity A) ≤
        min 1 (schnirelmannDensity (iterSumset A k) + schnirelmannDensity A) := by
      refine le_min (min_le_left _ _) ?_
      by_cases hk : 1 ≤ (k : ℝ) * schnirelmannDensity A
      · have h1 : 1 ≤ schnirelmannDensity (iterSumset A k) := by
          rwa [min_eq_left hk] at ih
        have hA0 := schnirelmannDensity_nonneg A
        exact (min_le_left _ _).trans (by linarith)
      · have hlt : (k : ℝ) * schnirelmannDensity A ≤ 1 := le_of_not_ge hk
        rw [min_eq_right hlt] at ih
        have hcast : ((k + 1 : ℕ) : ℝ) * schnirelmannDensity A =
            (k : ℝ) * schnirelmannDensity A + schnirelmannDensity A := by push_cast; ring
        exact (min_le_right _ _).trans (by linarith)
    exact hstep.trans hmann

/-- **Schnirelmann's Finite-Order Additive Basis Theorem**:
Every set `A ⊆ ℕ` with `0 ∈ A` and positive Schnirelmann density `σ(A) > 0` is an additive basis
of finite order `h ≤ ⌈1 / σ(A)⌉` (so every `n : ℕ` is a sum of `h` elements of `A`). -/
theorem schnirelmann_basis_theorem {A : Set ℕ} (h0A : 0 ∈ A) (hpos : 0 < schnirelmannDensity A) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ Nat.ceil (schnirelmannDensity A)⁻¹ ∧ ∀ n : ℕ, n ∈ iterSumset A h := by
  set h : ℕ := Nat.ceil (schnirelmannDensity A)⁻¹
  have hle1 := schnirelmannDensity_le_one A
  have hinv_ge1 : 1 ≤ (schnirelmannDensity A)⁻¹ := (one_le_inv₀ hpos).mpr hle1
  have hh_ge1 : 1 ≤ h := by
    have : (1 : ℝ) ≤ (h : ℝ) := hinv_ge1.trans (Nat.le_ceil _)
    exact_mod_cast this
  have hprod : 1 ≤ (h : ℝ) * schnirelmannDensity A := by
    calc (1 : ℝ) = (schnirelmannDensity A)⁻¹ * schnirelmannDensity A := (inv_mul_cancel₀ hpos.ne').symm
      _ ≤ (h : ℝ) * schnirelmannDensity A := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hpos.le
  have hdens1 : schnirelmannDensity (iterSumset A h) = 1 :=
    le_antisymm (schnirelmannDensity_le_one _)
      ((le_min le_rfl hprod).trans (schnirelmann_density_iterSumset_ge h0A h))
  refine ⟨h, hh_ge1, le_rfl, fun n => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0; exact zero_mem_iterSumset h0A h
  · exact schnirelmannDensity_eq_one_iff.mp hdens1 n (Nat.pos_of_ne_zero hn0)

end
end Arith4Ext.CircleMethod
