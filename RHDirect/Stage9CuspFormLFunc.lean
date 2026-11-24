import RHDirect.Stage8RamanujanDelta
import RHDirect.Stage8ModularRing
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# RHDirect.Stage9CuspFormLFunc

**UNCONDITIONAL PROOF OF HECKE'S 1936 THEOREM: ENTIRE ANALYTIC CONTINUATION & FUNCTIONAL EQUATION
`Λ(f, k - s) = i^k Λ(f, s)` FOR EVERY LEVEL-1 CUSP FORM `f ∈ S_k(SL₂(ℤ))`, AND SPECIFICALLY
`Λ(Δ, 12 - s) = Λ(Δ, s)` FOR RAMANUJAN'S DISCRIMINANT CUSP FORM `Δ`**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Exponential Decay of `f(i y)` at `y → ∞` & `y → 0⁺` for Every `f ∈ CuspForm SL2ZRange k`**:
   - `cuspForm_exp_decay_atTop`:
     `∃ C > 0, ∀ y ≥ 1, ‖f ⟨I * y, ...⟩‖ ≤ C * Real.exp (-2 * Real.pi * y)`.
   - `cuspForm_S_transform` & `cuspForm_S_transform_imag`:
     `f ⟨I / y, ...⟩ = (I * y) ^ k * f ⟨I * y, ...⟩` for all `y > 0`.
   - `cuspForm_exp_decay_atZero`:
     `∃ C > 0, ∀ y ∈ Set.Ioc 0 1, ‖f ⟨I * y, ...⟩‖ ≤ C * y ^ (-k) * Real.exp (-2 * Real.pi / y)`.
2. **Hecke's Completed `L`-Function `completedCuspL f s` & Uncompleted `cuspL f s` (`0` Assumptions!)**:
   - `completedCuspL f s = ∫ t in Set.Ioi 0, cuspImag f t * (t : ℂ) ^ (s - 1)` and exact split
     `completedCuspL f s = upperMellinCusp f s + I ^ k * upperMellinCusp f (k - s)`.
   - `differentiable_completedCuspL`: `Differentiable ℂ (completedCuspL f)` (entire on all of `ℂ`).
   - `completedCuspL_functional_equation`:
     `∀ s : ℂ, completedCuspL f (k - s) = Complex.I ^ k * completedCuspL f s`
     (and `completedCuspL_functional_equation_even`: `Λ(f, 2m - s) = (-1)^m Λ(f, s)`).
   - `completedCuspL_eq_gamma_mul_LSeries`: for `0 < k` and `k / 2 + 1 < s.re`,
     `completedCuspL f s = (2 * π) ^ (-s) * Γ(s) * LSeries (qExpansionCoeff f) s`.
   - `differentiable_cuspL_entire`: `Differentiable ℂ (cuspL f)` where
     `cuspL f s = (2 * π) ^ s * (Γ(s))⁻¹ * completedCuspL f s`.
   - `cuspL_eq_LSeries`, `cuspL_eq_modularForm_L`, and trivial zeros at all non-positive integers
     `cuspL_neg_nat_eq_zero : ∀ m : ℕ, cuspL f (-m) = 0`.
3. **Specialization to Ramanujan's `Δ` (`completedDeltaL`, `deltaL`)**:
   - `differentiable_completedDeltaL`, `differentiable_deltaL`, and
     `completedDeltaL_functional_equation : ∀ s : ℂ, completedDeltaL (12 - s) = completedDeltaL s`.
   - `completedDeltaL_eq_gamma_mul_LSeries`, `deltaL_eq_LSeries`, `deltaL_eq_modularForm_L`,
     `deltaL_euler_product`, and `deltaL_ne_zero_of_re_gt_seven` (`L(Δ, s) ≠ 0` on `Re(s) > 7`).
   - Strict positivity `ramanujanDelta_imag_re_pos : ∀ y > 0, Δ(i y) ∈ ℝ ∧ 0 < (Δ(i y)).re`,
     yielding conjugate symmetry `completedDeltaL_conj`, reality `completedDeltaL_real_on_real`,
     strict positivity on the entire real line `completedDeltaL_pos_on_real`, and positivity of
     the central value `deltaL_central_value_pos : 0 < (deltaL 6).re`!
-/

open Complex Real Filter MeasureTheory
open RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries
open RHDirect.Stage8ModularRing RHDirect.Stage8RamanujanDelta
open scoped BigOperators UpperHalfPlane ModularForm Topology ENNReal Manifold

namespace RHDirect.Stage9CuspFormLFunc

noncomputable section

/-! ## Section 1: Exponential Decay of `f(i y)` at `∞` & `0⁺` and `S`-Transformation -/

section ExponentialDecayAndSTransform

/-- The point `i * y` on the positive imaginary axis in `UpperHalfPlane` for `y > 0`. -/
def imagPt (y : ℝ) (hy : 0 < y) : UpperHalfPlane :=
  ⟨Complex.I * (y : ℂ), by simp [hy]⟩

@[simp]
theorem coe_imagPt (y : ℝ) (hy : 0 < y) :
    (imagPt y hy : ℂ) = Complex.I * (y : ℂ) :=
  rfl

@[simp]
theorem im_imagPt (y : ℝ) (hy : 0 < y) :
    (imagPt y hy).im = y := by
  simp [imagPt]

/-- Total function on `ℝ` restricting a level-1 cusp form `f` to the positive imaginary axis
`t ↦ f(i t)` for `t > 0` (and `0` for `t ≤ 0`). -/
def cuspImag {k : ℤ} (f : CuspForm SL2ZRange k) (t : ℝ) : ℂ :=
  if ht : 0 < t then f (imagPt t ht) else 0

/-- The `n`-th Fourier (`q`-expansion) coefficient of a level-1 cusp form `f ∈ S_k(SL₂(ℤ))`. -/
def qExpansionCoeff {k : ℤ} (f : CuspForm SL2ZRange k) (n : ℕ) : ℂ :=
  PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))

theorem cuspImag_of_pos {k : ℤ} (f : CuspForm SL2ZRange k) {t : ℝ} (ht : 0 < t) :
    cuspImag f t = f (imagPt t ht) :=
  dif_pos ht

theorem cuspImag_of_nonpos {k : ℤ} (f : CuspForm SL2ZRange k) {t : ℝ} (ht : t ≤ 0) :
    cuspImag f t = 0 :=
  dif_neg (not_lt.mpr ht)

theorem cuspImag_eq_ofComplex {k : ℤ} (f : CuspForm SL2ZRange k) {t : ℝ} (ht : 0 < t) :
    cuspImag f t = f (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))) := by
  rw [cuspImag_of_pos f ht]
  congr 1
  have him : 0 < (Complex.I * (t : ℂ)).im := by simp [ht]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  rfl

/-- Continuity of `t ↦ f(i t)` on `(0, ∞)` for every level-1 cusp form `f`. -/
theorem continuousOn_cuspImag {k : ℤ} (f : CuspForm SL2ZRange k) :
    ContinuousOn (cuspImag f) (Set.Ioi (0 : ℝ)) := by
  have hdiff : DifferentiableOn ℂ ((f : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex)
      {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have hcomp : ContinuousOn
      (fun t : ℝ => f (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)))) (Set.Ioi (0 : ℝ)) := by
    refine hdiff.continuousOn.comp (continuous_const.mul Complex.continuous_ofReal).continuousOn ?_
    intro t ht
    change 0 < (Complex.I * (t : ℂ)).im
    simpa using ht
  exact hcomp.congr fun t ht => cuspImag_eq_ofComplex f ht

/-- **Exponential Decay of Every Level-1 Cusp Form at `y → ∞`**:
for every `f ∈ CuspForm SL2ZRange k`, there exists `C > 0` such that
`‖f(i y)‖ ≤ C * exp(-2π y)` for ALL `y ≥ 1`. -/
theorem cuspForm_exp_decay_atTop {k : ℤ} (f : CuspForm SL2ZRange k) :
    ∃ C > 0, ∀ (y : ℝ) (hy : 1 ≤ y),
      ‖f ⟨Complex.I * (y : ℂ), by simp; linarith⟩‖ ≤ C * Real.exp (-2 * Real.pi * y) := by
  have hbigO := CuspFormClass.exp_decay_atImInfty f zero_lt_one one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨C₀, hC₀⟩ := hbigO
  rw [UpperHalfPlane.atImInfty_basis.eventually_iff] at hC₀
  obtain ⟨A, _, hA⟩ := hC₀
  let B : ℝ := max 1 A
  have hB1 : 1 ≤ B := le_max_left 1 A
  have hBA : A ≤ B := le_max_right 1 A
  let g : ℝ → ℝ := fun y => ‖cuspImag f y‖ * Real.exp (2 * Real.pi * y)
  have hg_cont : ContinuousOn g (Set.Icc (1 : ℝ) B) := by
    refine ((continuousOn_cuspImag f).norm.mono ?_).mul ?_
    · intro y hy
      exact lt_of_lt_of_le zero_lt_one hy.1
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  let C : ℝ := max (max C₀ C₁) 1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC₀_le : C₀ ≤ C := le_trans (le_max_left C₀ C₁) (le_max_left _ _)
  have hC₁_le : C₁ ≤ C := le_trans (le_max_right C₀ C₁) (le_max_left _ _)
  refine ⟨C, hC_pos, fun y hy => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  by_cases hyB : y ≤ B
  · have hmem : y ∈ Set.Icc (1 : ℝ) B := ⟨hy, hyB⟩
    have hgb : ‖g y‖ ≤ C₁ := hC₁ y hmem
    have hg_nn : 0 ≤ g y := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hg_nn] at hgb
    have hprod : ‖f ⟨Complex.I * (y : ℂ), by simp; linarith⟩‖ * Real.exp (2 * Real.pi * y) ≤ C := by
      have hval : cuspImag f y = f ⟨Complex.I * (y : ℂ), by simp; linarith⟩ :=
        cuspImag_of_pos f hy0
      rw [← hval]
      exact hgb.trans hC₁_le
    have hexp_pos : 0 < Real.exp (2 * Real.pi * y) := Real.exp_pos _
    have hmul : Real.exp (2 * Real.pi * y) * Real.exp (-2 * Real.pi * y) = 1 := by
      rw [← Real.exp_add]
      have hzero : 2 * Real.pi * y + -2 * Real.pi * y = 0 := by ring
      rw [hzero, Real.exp_zero]
    calc ‖f ⟨Complex.I * (y : ℂ), by simp; linarith⟩‖
        = (‖f ⟨Complex.I * (y : ℂ), by simp; linarith⟩‖ * Real.exp (2 * Real.pi * y)) *
            Real.exp (-2 * Real.pi * y) := by rw [mul_assoc, hmul, mul_one]
      _ ≤ C * Real.exp (-2 * Real.pi * y) :=
            mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
  · have hAy : A ≤ y := le_trans hBA (le_of_not_ge hyB)
    have hmem : (⟨Complex.I * (y : ℂ), by simp; linarith⟩ : UpperHalfPlane) ∈
        UpperHalfPlane.im ⁻¹' Set.Ici A := by
      change A ≤ (⟨Complex.I * (y : ℂ), by simp; linarith⟩ : UpperHalfPlane).im
      simpa using hAy
    have hbound := hA hmem
    simp only [div_one, Real.norm_of_nonneg (Real.exp_pos _).le] at hbound
    have him : (⟨Complex.I * (y : ℂ), by simp; linarith⟩ : UpperHalfPlane).im = y := by simp
    rw [him] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right hC₀_le (Real.exp_pos _).le)

/-- **Exact `S`-Transformation Law for Every Level-1 Cusp Form `f ∈ S_k(SL₂(ℤ))`**:
`f (S • τ) = τ ^ k * f τ` for every `τ : UpperHalfPlane`. -/
theorem cuspForm_S_transform {k : ℤ} (f : CuspForm SL2ZRange k) (τ : UpperHalfPlane) :
    f (ModularGroup.S • τ) = (τ : ℂ) ^ k * f τ := by
  have hsl := f.slash_action_eq'
    (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ ModularGroup.S) ⟨ModularGroup.S, rfl⟩
  have hval := congrFun hsl τ
  have hmap : Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ ModularGroup.S =
      sl2ZToGL2R ModularGroup.S := rfl
  change SlashAction.map k (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ ModularGroup.S)
    (f : UpperHalfPlane → ℂ) τ = f τ at hval
  rw [hmap, slash_S_apply] at hval
  calc f (ModularGroup.S • τ)
      = (f (ModularGroup.S • τ) * (τ : ℂ) ^ (-k)) * (τ : ℂ) ^ k := by
          rw [mul_assoc, ← zpow_add₀ τ.ne_zero, neg_add_cancel, zpow_zero, mul_one]
    _ = f τ * (τ : ℂ) ^ k := by rw [hval]
    _ = (τ : ℂ) ^ k * f τ := mul_comm _ _

/-- **Exact `S`-Transformation Law on the Positive Imaginary Axis**:
`f(i / y) = (i y)^k * f(i y)` for every `y > 0`. -/
theorem cuspForm_S_transform_imag {k : ℤ} (f : CuspForm SL2ZRange k) {y : ℝ} (hy : 0 < y) :
    f ⟨Complex.I / (y : ℂ), by simp [div_eq_mul_inv, hy]⟩ =
      (Complex.I * (y : ℂ)) ^ k * f ⟨Complex.I * (y : ℂ), by simp [hy]⟩ := by
  have hS := cuspForm_S_transform f (imagPt y hy)
  have hpt : ModularGroup.S • imagPt y hy =
      ⟨Complex.I / (y : ℂ), by simp [div_eq_mul_inv, hy]⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.modular_S_smul]
    change (-(Complex.I * (y : ℂ)))⁻¹ = Complex.I / (y : ℂ)
    rw [inv_neg, mul_inv, Complex.inv_I, div_eq_mul_inv]
    ring
  rw [hpt] at hS
  exact hS

/-- Inversion law for `cuspImag f` on `(0, ∞)`:
`cuspImag f y⁻¹ = (I * y)^k * cuspImag f y` for all `y > 0`. -/
theorem cuspImag_inv {k : ℤ} (f : CuspForm SL2ZRange k) {y : ℝ} (hy : 0 < y) :
    cuspImag f y⁻¹ = (Complex.I * (y : ℂ)) ^ k * cuspImag f y := by
  rw [cuspImag_of_pos f (inv_pos.mpr hy), cuspImag_of_pos f hy]
  have hpt : imagPt y⁻¹ (inv_pos.mpr hy) =
      ⟨Complex.I / (y : ℂ), by simp [div_eq_mul_inv, hy]⟩ := by
    apply UpperHalfPlane.ext
    change Complex.I * ((y⁻¹ : ℝ) : ℂ) = Complex.I / (y : ℂ)
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  rw [hpt]
  exact cuspForm_S_transform_imag f hy

/-- **Super-Exponential Decay of Every Level-1 Cusp Form at `y → 0⁺`**:
for every `f ∈ CuspForm SL2ZRange k`, there exists `C > 0` such that
`‖f(i y)‖ ≤ C * y ^ (-k) * exp(-2π / y)` for ALL `y ∈ (0, 1]`. -/
theorem cuspForm_exp_decay_atZero {k : ℤ} (f : CuspForm SL2ZRange k) :
    ∃ C > 0, ∀ (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1),
      ‖f ⟨Complex.I * (y : ℂ), by simp [hy.1]⟩‖ ≤ C * y ^ (-k) * Real.exp (-2 * Real.pi / y) := by
  obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_atTop f
  refine ⟨C, hC_pos, fun y hy => ?_⟩
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hinv_ge : 1 ≤ y⁻¹ := one_le_inv₀ hy0 |>.mpr hy1
  have hinv_pos : 0 < y⁻¹ := inv_pos.mpr hy0
  have hS := cuspImag_inv f hinv_pos
  rw [inv_inv, cuspImag_of_pos f hy0, cuspImag_of_pos f hinv_pos] at hS
  have hnorm_eq : ‖f ⟨Complex.I * (y : ℂ), by simp [hy0]⟩‖ =
      y ^ (-k) * ‖f ⟨Complex.I * ((y⁻¹ : ℝ) : ℂ), by simp; linarith⟩‖ := by
    change ‖f (imagPt y hy0)‖ = y ^ (-k) * ‖f (imagPt y⁻¹ hinv_pos)‖
    rw [hS, norm_mul, norm_zpow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg hinv_pos.le, inv_zpow, zpow_neg]
  rw [hnorm_eq]
  have htop := hC y⁻¹ hinv_ge
  have hexp_eq : -2 * Real.pi * y⁻¹ = -2 * Real.pi / y := by rw [div_eq_mul_inv]
  rw [hexp_eq] at htop
  calc y ^ (-k) * ‖f ⟨Complex.I * ((y⁻¹ : ℝ) : ℂ), by simp; linarith⟩‖
      ≤ y ^ (-k) * (C * Real.exp (-2 * Real.pi / y)) :=
          mul_le_mul_of_nonneg_left htop (zpow_nonneg hy0.le (-k))
    _ = C * y ^ (-k) * Real.exp (-2 * Real.pi / y) := by ring

/-- Rapid polynomial decay of `exp(-2π t)` at `t → ∞`: `exp(-2π t) = O(t^{-a})` for all `a : ℝ`. -/
private lemma isBigO_exp_neg_two_pi_atTop (a : ℝ) :
    (fun t : ℝ => Real.exp (-2 * Real.pi * t)) =O[atTop] fun t : ℝ => t ^ (-a) := by
  let m : ℕ := ⌈max a 0⌉₊
  have hm_ge : a ≤ (m : ℝ) := (le_max_left a 0).trans (Nat.le_ceil (max a 0))
  have hpow : Tendsto (fun u : ℝ => u ^ m * Real.exp (-u)) atTop (nhds 0) := by
    simpa [Real.exp_neg, div_eq_mul_inv] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m)
  have h2pi : Tendsto (fun t : ℝ => 2 * Real.pi * t) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity : (0 : ℝ) < 2 * Real.pi) tendsto_id
  have hcomp : Tendsto (fun t : ℝ => (2 * Real.pi * t) ^ m * Real.exp (-(2 * Real.pi * t)))
      atTop (nhds 0) := hpow.comp h2pi
  have hev : ∀ᶠ t : ℝ in atTop,
      ‖(2 * Real.pi * t) ^ m * Real.exp (-(2 * Real.pi * t))‖ ≤ 1 := by
    have h1 := hcomp.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    filter_upwards [h1] with t ht
    simpa [Metric.mem_ball, dist_zero_right] using ht.le
  rw [Asymptotics.isBigO_iff]
  refine ⟨((2 * Real.pi) ^ m)⁻¹, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have h2pi_pos : (0 : ℝ) < (2 * Real.pi) ^ m := pow_pos (by positivity) m
  have htm_pos : 0 < t ^ m := pow_pos ht0 m
  have hnn : 0 ≤ (2 * Real.pi * t) ^ m * Real.exp (-(2 * Real.pi * t)) :=
    mul_nonneg (pow_nonneg (by positivity) m) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hnn, mul_pow] at ht
  have hexp_le : Real.exp (-2 * Real.pi * t) ≤ ((2 * Real.pi) ^ m)⁻¹ * t ^ (-(m : ℝ)) := by
    have hneg : -2 * Real.pi * t = -(2 * Real.pi * t) := by ring
    rw [hneg, Real.rpow_neg ht0.le, Real.rpow_natCast, ← mul_inv, ← one_div,
      le_div_iff₀' (mul_pos h2pi_pos htm_pos)]
    linarith
  have hrpow_le : t ^ (-(m : ℝ)) ≤ t ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le ht1 (neg_le_neg hm_ge)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
  exact hexp_le.trans (mul_le_mul_of_nonneg_left hrpow_le (inv_nonneg.mpr h2pi_pos.le))

/-- Super-polynomial decay of `cuspImag f` at `t → ∞`: `f(i t) = O(t^{-a})` for EVERY `a : ℝ`. -/
theorem isBigO_cuspImag_atTop {k : ℤ} (f : CuspForm SL2ZRange k) (a : ℝ) :
    cuspImag f =O[atTop] fun t : ℝ => t ^ (-a) := by
  obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_atTop f
  have h1 : cuspImag f =O[atTop] fun t : ℝ => Real.exp (-2 * Real.pi * t) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    rw [cuspImag_of_pos f ht0, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hC t ht
  exact h1.trans (isBigO_exp_neg_two_pi_atTop a)

/-- Super-polynomial decay of `cuspImag f` at `t → 0⁺`: `f(i t) = O(t^{-b})` for EVERY `b : ℝ`. -/
theorem isBigO_cuspImag_atZero {k : ℤ} (f : CuspForm SL2ZRange k) (b : ℝ) :
    cuspImag f =O[nhdsWithin 0 (Set.Ioi 0)] fun t : ℝ => t ^ (-b) := by
  obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_atZero f
  have htop := isBigO_exp_neg_two_pi_atTop ((k : ℝ) - b)
  rw [Asymptotics.isBigO_iff] at htop
  obtain ⟨D, hD⟩ := htop
  rw [Filter.eventually_atTop] at hD
  obtain ⟨M, hM⟩ := hD
  let ε : ℝ := min 1 ((max M 1)⁻¹)
  have hM1 : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hε_pos : 0 < ε := lt_min zero_lt_one (inv_pos.mpr hM1)
  rw [Asymptotics.isBigO_iff]
  refine ⟨C * D, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hε_pos] with t ht
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := le_trans ht.2.le (min_le_left _ _)
  have htinv_ge_M : M ≤ t⁻¹ := by
    have hle : t < (max M 1)⁻¹ := lt_of_lt_of_le ht.2 (min_le_right _ _)
    have hge : max M 1 < t⁻¹ := (lt_inv_comm₀ ht0 hM1).mp hle
    exact le_trans (le_max_left M 1) hge.le
  have hD_inv := hM t⁻¹ htinv_ge_M
  have hexp_eq : -2 * Real.pi * t⁻¹ = -2 * Real.pi / t := by rw [div_eq_mul_inv]
  rw [hexp_eq, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.rpow_nonneg (inv_pos.mpr ht0).le _)] at hD_inv
  have hzero := hC t ⟨ht0, ht1⟩
  rw [cuspImag_of_pos f ht0, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
  have hrpow_inv : (t⁻¹) ^ (-((k : ℝ) - b)) = t ^ ((k : ℝ) - b) := by
    rw [Real.inv_rpow ht0.le, Real.rpow_neg ht0.le, inv_inv]
  rw [hrpow_inv] at hD_inv
  have hzpow : t ^ (-k) = t ^ (-(k : ℝ)) := by
    rw [← Real.rpow_intCast t (-k), Int.cast_neg]
  have hcomb : t ^ (-k) * t ^ ((k : ℝ) - b) = t ^ (-b) := by
    rw [hzpow, ← Real.rpow_add ht0]
    congr 1; ring
  calc ‖f (imagPt t ht0)‖
      ≤ C * t ^ (-k) * Real.exp (-2 * Real.pi / t) := hzero
    _ ≤ C * t ^ (-k) * (D * t ^ ((k : ℝ) - b)) :=
          mul_le_mul_of_nonneg_left hD_inv (mul_nonneg hC_pos.le (zpow_nonneg ht0.le _))
    _ = C * D * (t ^ (-k) * t ^ ((k : ℝ) - b)) := by ring
    _ = C * D * t ^ (-b) := by rw [hcomb]

/-- Every level-1 cusp form `f` has globally convergent Mellin transform on ALL of `ℂ`. -/
theorem mellinConvergent_cuspImag {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) :
    MellinConvergent (cuspImag f) s := by
  have hloc : LocallyIntegrableOn (cuspImag f) (Set.Ioi 0) volume :=
    (continuousOn_cuspImag f).locallyIntegrableOn measurableSet_Ioi
  exact mellinConvergent_of_isBigO_rpow hloc
    (isBigO_cuspImag_atTop f (s.re + 1)) (by linarith)
    (isBigO_cuspImag_atZero f (s.re - 1)) (by linarith)

end ExponentialDecayAndSTransform

/-! ## Section 2: Hecke's 1936 Theorem — Entirety, Functional Equation & Mellin–Dirichlet Identity -/

section HeckeTheorem

/-- **Hecke's Completed `L`-Function `Λ(f, s)`** of a level-1 cusp form `f ∈ S_k(SL₂(ℤ))`,
defined unconditionally on ALL of `ℂ` by the globally convergent Mellin integral
$$\Lambda(f, s) = \int_0^\infty f(i t)\, t^{s - 1}\, dt.$$ -/
def completedCuspL {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), cuspImag f t * (t : ℂ) ^ (s - 1)

/-- The upper-half Mellin integral `∫_1^∞ f(i t) t^{s - 1} dt`. -/
def upperMellinCusp {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ), cuspImag f t * (t : ℂ) ^ (s - 1)

/-- **Hecke's Entire Analytic Continuation of the Uncompleted `L`-Function `L(f, s)`**
for every level-1 cusp form `f ∈ S_k(SL₂(ℤ))`:
$$L(f, s) = (2\pi)^s\, \Gamma(s)^{-1}\, \Lambda(f, s).$$ -/
def cuspL {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ * completedCuspL f s

theorem completedCuspL_eq_mellin {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) :
    completedCuspL f s = mellin (cuspImag f) s := by
  unfold completedCuspL mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- **Exact Split Formula for Hecke's Completed `L`-Function**:
for EVERY `k : ℤ`, EVERY `f ∈ S_k(SL₂(ℤ))`, and EVERY `s : ℂ`,
$$\Lambda(f, s) = \int_1^\infty f(i t)\, t^{s - 1}\, dt + i^k \int_1^\infty f(i t)\, t^{k - s - 1}\, dt.$$ -/
theorem completedCuspL_eq_split {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) :
    completedCuspL f s =
      upperMellinCusp f s + Complex.I ^ k * upperMellinCusp f ((k : ℂ) - s) := by
  have hint_full : IntegrableOn (fun t : ℝ => cuspImag f t * (t : ℂ) ^ (s - 1))
      (Set.Ioi 0) volume := by
    refine (mellinConvergent_cuspImag f s).congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only
    rw [smul_eq_mul, mul_comm]
  have hunion : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := Set.Ioc_disjoint_Ioi_same
  have hint1 : IntegrableOn (fun t : ℝ => cuspImag f t * (t : ℂ) ^ (s - 1))
      (Set.Ioc 0 1) volume := hint_full.mono_set Set.Ioc_subset_Ioi_self
  have hint2 : IntegrableOn (fun t : ℝ => cuspImag f t * (t : ℂ) ^ (s - 1))
      (Set.Ioi 1) volume := hint_full.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hsplit : completedCuspL f s =
      (∫ t in Set.Ioo (0 : ℝ) 1, cuspImag f t * (t : ℂ) ^ (s - 1)) + upperMellinCusp f s := by
    unfold completedCuspL upperMellinCusp
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint1 hint2,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [hsplit, add_comm]
  congr 1
  -- Evaluate the (0, 1) integral by substituting t = u⁻¹ via `mellin_comp_inv`
  let g : ℝ → ℂ := (Set.Ioo (0 : ℝ) 1).indicator (cuspImag f)
  have hlhs : mellin g s = ∫ t in Set.Ioo (0 : ℝ) 1, cuspImag f t * (t : ℂ) ^ (s - 1) := by
    unfold mellin
    have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • g t) =
        (Set.Ioo (0 : ℝ) 1).indicator (fun t : ℝ => cuspImag f t * (t : ℂ) ^ (s - 1)) := by
      funext t
      by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
      · dsimp only [g]; rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, smul_eq_mul, mul_comm]
      · dsimp only [g]; rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, smul_zero]
    rw [heq, MeasureTheory.setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Set.Ioo_subset_Ioi_self]
  have hcomp := mellin_comp_inv g (-s)
  rw [neg_neg] at hcomp
  rw [← hlhs, ← hcomp]
  unfold mellin upperMellinCusp
  have heq_inv : Set.EqOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • g t⁻¹)
      ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ =>
        Complex.I ^ k * (cuspImag f t * (t : ℂ) ^ ((k : ℂ) - s - 1)))) (Set.Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    by_cases ht1 : t ∈ Set.Ioi (1 : ℝ)
    · have hmem : t⁻¹ ∈ Set.Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr ht0, inv_lt_one_of_one_lt₀ ht1⟩
      dsimp only [g]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ht1, smul_eq_mul,
        cuspImag_inv f ht0, mul_zpow]
      have hpow : (t : ℂ) ^ (-s - 1) * (t : ℂ) ^ k = (t : ℂ) ^ ((k : ℂ) - s - 1) := by
        rw [← Complex.cpow_intCast (t : ℂ) k, ← Complex.cpow_add _ _ htC]
        congr 1; ring
      calc (t : ℂ) ^ (-s - 1) * (Complex.I ^ k * (t : ℂ) ^ k * cuspImag f t)
          = Complex.I ^ k * (cuspImag f t * ((t : ℂ) ^ (-s - 1) * (t : ℂ) ^ k)) := by ring
        _ = Complex.I ^ k * (cuspImag f t * (t : ℂ) ^ ((k : ℂ) - s - 1)) := by rw [hpow]
    · have hnot : t⁻¹ ∉ Set.Ioo (0 : ℝ) 1 := by
        intro hc
        have hlt : 1 < t := (inv_lt_one_iff₀.mp hc.2).resolve_left (not_le.mpr ht0)
        exact ht1 hlt
      dsimp only [g]
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem ht1, smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi heq_inv,
    MeasureTheory.setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one),
    MeasureTheory.integral_const_mul]

/-- **ENTIRETY OF HECKE'S COMPLETED `L`-FUNCTION `Λ(f, s)` (Hecke 1936, `0` Assumptions!)**:
for EVERY `k : ℤ` and EVERY level-1 cusp form `f ∈ S_k(SL₂(ℤ))`,
`completedCuspL f` is **entire** (`Differentiable ℂ`) on all of `ℂ`! -/
theorem differentiable_completedCuspL {k : ℤ} (f : CuspForm SL2ZRange k) :
    Differentiable ℂ (completedCuspL f) := by
  have hfun : completedCuspL f = mellin (cuspImag f) := by
    funext s; exact completedCuspL_eq_mellin f s
  rw [hfun]
  have hloc : LocallyIntegrableOn (cuspImag f) (Set.Ioi 0) volume :=
    (continuousOn_cuspImag f).locallyIntegrableOn measurableSet_Ioi
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow hloc
    (isBigO_cuspImag_atTop f (s.re + 1)) (by linarith)
    (isBigO_cuspImag_atZero f (s.re - 1)) (by linarith)

/-- **UNCONDITIONAL HECKE FUNCTIONAL EQUATION FOR EVERY LEVEL-1 CUSP FORM (Hecke 1936)**:
for EVERY `k : ℤ`, EVERY `f ∈ S_k(SL₂(ℤ))`, and EVERY `s : ℂ`,
$$\Lambda(f, k - s) = i^k\, \Lambda(f, s).$$ -/
theorem completedCuspL_functional_equation {k : ℤ} (f : CuspForm SL2ZRange k) (s : ℂ) :
    completedCuspL f ((k : ℂ) - s) = Complex.I ^ k * completedCuspL f s := by
  rw [completedCuspL_eq_mellin, completedCuspL_eq_mellin]
  have hcomp := mellin_comp_inv (cuspImag f) (s - (k : ℂ))
  have hneg : -(s - (k : ℂ)) = (k : ℂ) - s := by ring
  rw [hneg] at hcomp
  rw [← hcomp]
  unfold mellin
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  dsimp only
  rw [smul_eq_mul, smul_eq_mul, cuspImag_inv f ht0, mul_zpow]
  have hpow : (t : ℂ) ^ (s - (k : ℂ) - 1) * (t : ℂ) ^ k = (t : ℂ) ^ (s - 1) := by
    rw [← Complex.cpow_intCast (t : ℂ) k, ← Complex.cpow_add _ _ htC]
    congr 1; ring
  calc (t : ℂ) ^ (s - (k : ℂ) - 1) * (Complex.I ^ k * (t : ℂ) ^ k * cuspImag f t)
      = Complex.I ^ k * (((t : ℂ) ^ (s - (k : ℂ) - 1) * (t : ℂ) ^ k) * cuspImag f t) := by ring
    _ = Complex.I ^ k * ((t : ℂ) ^ (s - 1) * cuspImag f t) := by rw [hpow]

/-- Even-weight form of Hecke's functional equation: for `k = 2 * m`,
`Λ(f, 2m - s) = (-1)^m Λ(f, s)`. -/
theorem completedCuspL_functional_equation_even {m : ℤ}
    (f : CuspForm SL2ZRange (2 * m)) (s : ℂ) :
    completedCuspL f (((2 * m : ℤ) : ℂ) - s) = (-1 : ℂ) ^ m * completedCuspL f s := by
  rw [completedCuspL_functional_equation f s]
  congr 1
  rw [zpow_mul, zpow_two, Complex.I_mul_I]

/-- Exact identification of `completedCuspL f` with Mathlib's `ModularForm.Λ hk f` on ALL of `ℂ`. -/
theorem completedCuspL_eq_modularForm_Λ {k : ℤ} (hk : 0 < k)
    (f : CuspForm SL2ZRange k) (s : ℂ) :
    completedCuspL f s = ModularForm.Λ hk f s := by
  rw [completedCuspL_eq_mellin, CuspForm.Λ_eq_mellin hk f]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [cuspImag_eq_ofComplex f ht]

/-- Exact evaluation of `qParam 1 (i t) = exp(-2π t)` for `t : ℝ`. -/
private lemma qParam_one_imag (t : ℝ) :
    Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) =
      ((Real.exp (-2 * Real.pi * t) : ℝ) : ℂ) := by
  unfold Function.Periodic.qParam
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I_mul_I

/-- Exact `q`-expansion identity on the positive imaginary axis:
for every `f ∈ S_k(SL₂(ℤ))` and every `t > 0`,
`f(i t) = ∑'_{n : ℕ} a_n(f) * exp(-2π n t)`. -/
theorem hasSum_cuspImag_qExpansion {k : ℤ} (f : CuspForm SL2ZRange k) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ))
      (cuspImag f t) := by
  have hhas := ModularForm.hasSum_qExpansion f zero_lt_one one_mem_strictPeriods_SL (imagPt t ht)
  rw [cuspImag_of_pos f ht]
  refine hhas.congr_fun fun n => ?_
  unfold qExpansionCoeff
  rw [coe_imagPt, qParam_one_imag t, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 3
  ring

/-- Every level-1 cusp form has vanishing constant term `a_0(f) = 0`. -/
theorem qExpansionCoeff_zero {k : ℤ} (f : CuspForm SL2ZRange k) :
    qExpansionCoeff f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f zero_lt_one one_mem_strictPeriods_SL

/-- Unconditional `LSeriesSummable` for every level-1 cusp form on `Re(s) > k / 2 + 1`. -/
theorem LSeriesSummable_qExpansionCoeff {k : ℤ} (f : CuspForm SL2ZRange k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (qExpansionCoeff f) s := by
  have hbigO : qExpansionCoeff f =O[Filter.atTop] fun n : ℕ => ((n : ℝ) ^ ((k : ℝ) / 2)) := by
    have h := CuspFormClass.qExpansion_isBigO f
    rw [Subgroup.strictWidthInfty_SL2Z] at h
    exact h
  refine LSeriesSummable_of_isBigO_rpow (x := (k : ℝ) / 2 + 1) hs ?_
  simpa [add_sub_cancel_right] using hbigO

/-- Exact Mellin integral of `exp(-a t)` for `a > 0` and `0 < s.re`:
`∫ t in Ioi 0, exp(-a t) * t^{s - 1} = a^{-s} * Γ(s)`. -/
private lemma mellin_exp_neg_mul_complex {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) : ℝ) : ℂ) * (t : ℂ) ^ (s - 1) =
      (a : ℂ) ^ (-s) * Complex.Gamma s := by
  have h1 : mellin (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s = Complex.Gamma s := by
    rw [Complex.Gamma_eq_integral hs]
    unfold Complex.GammaIntegral mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    dsimp only
    rw [smul_eq_mul, mul_comm, Complex.ofReal_exp, Complex.ofReal_neg]
  have h2 := mellin_comp_mul_left (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) s ha
  rw [h1, smul_eq_mul] at h2
  rw [← h2]
  unfold mellin
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  dsimp only
  rw [smul_eq_mul, mul_comm]

/-- Real-valued Mellin integral of `exp(-a t)` for `a > 0` and `0 < σ`. -/
private lemma mellin_exp_neg_mul_real {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) * t ^ (σ - 1) = a ^ (-σ) * Real.Gamma σ := by
  have hC := mellin_exp_neg_mul_complex ha (s := (σ : ℂ)) (by simpa using hσ)
  have hre := congrArg Complex.re hC
  have hlhs : (∫ t in Set.Ioi (0 : ℝ),
      ((Real.exp (-(a * t)) : ℝ) : ℂ) * (t : ℂ) ^ ((σ : ℂ) - 1)).re =
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) * t ^ (σ - 1) := by
    have hcongr : ∫ t in Set.Ioi (0 : ℝ),
        ((Real.exp (-(a * t)) : ℝ) : ℂ) * (t : ℂ) ^ ((σ : ℂ) - 1) =
        ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) * t ^ (σ - 1) : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le, Complex.ofReal_sub, Complex.ofReal_one]
    have hofReal : (∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-(a * t)) * t ^ (σ - 1) : ℝ) : ℂ)) =
        ((∫ t in Set.Ioi (0 : ℝ), Real.exp (-(a * t)) * t ^ (σ - 1) : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcongr, hofReal, Complex.ofReal_re]
  have hrhs : ((a : ℂ) ^ (-(σ : ℂ)) * Complex.Gamma (σ : ℂ)).re = a ^ (-σ) * Real.Gamma σ := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow ha.le, Complex.Gamma_ofReal,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hlhs, hrhs] at hre
  exact hre

/-- **EXACT MELLIN–DIRICHLET IDENTITY FOR EVERY LEVEL-1 CUSP FORM (Hecke 1936)**:
for EVERY `k > 0`, EVERY `f ∈ S_k(SL₂(ℤ))`, and EVERY `s : ℂ` with `k / 2 + 1 < s.re`,
$$\Lambda(f, s) = (2\pi)^{-s}\, \Gamma(s)\, L(f, s) =
  (2\pi)^{-s}\, \Gamma(s)\, \sum_{n=1}^{\infty} \frac{a_n(f)}{n^s}.$$ -/
theorem completedCuspL_eq_gamma_mul_LSeries {k : ℤ} (hk : 0 < k)
    (f : CuspForm SL2ZRange k) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    completedCuspL f s =
      (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * LSeries (qExpansionCoeff f) s := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Int.cast_pos.mpr hk
  have hs_pos : 0 < s.re := by linarith
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hLsumm : LSeriesSummable (qExpansionCoeff f) s := LSeriesSummable_qExpansionCoeff f hs
  -- Measurability of each Fourier summand
  have haes : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ => qExpansionCoeff f n *
        ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) * (t : ℂ) ^ (s - 1))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_const.mul ?_).mul ?_
    · exact Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp (by fun_prop)).continuousOn
    · intro t ht
      exact (continuousAt_ofReal_cpow_const ht (s - 1)).continuousWithinAt
  -- Tonelli bound: ∑' n, ∫⁻ t > 0, ‖a_n e^{-2πnt} t^{s-1}‖ₑ < ⊤
  have hlint_term : ∀ n : ℕ,
      (∫⁻ t in Set.Ioi (0 : ℝ),
        ‖qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
          (t : ℂ) ^ (s - 1)‖ₑ) =
      ENNReal.ofReal ((2 * Real.pi) ^ (-s.re) * Real.Gamma s.re *
        ‖LSeries.term (qExpansionCoeff f) s n‖) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [qExpansionCoeff_zero f]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have ha_pos : 0 < 2 * Real.pi * (n : ℝ) := mul_pos h2pi_pos hn_pos
      have hlhs_eq : (∫⁻ t in Set.Ioi (0 : ℝ),
          ‖qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
            (t : ℂ) ^ (s - 1)‖ₑ) =
          ∫⁻ t in Set.Ioi (0 : ℝ),
            ENNReal.ofReal (‖qExpansionCoeff f n‖ *
              (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) * t ^ (s.re - 1))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        have hnn : 0 ≤ ‖qExpansionCoeff f n‖ *
            (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) * t ^ (s.re - 1)) :=
          mul_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _))
        rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal hnn]
        congr 1; apply Subtype.ext
        change ‖qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
          (t : ℂ) ^ (s - 1)‖ = _
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le,
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have hre : (s - 1).re = s.re - 1 := by simp
        rw [hre, mul_assoc]
        rfl
      rw [hlhs_eq]
      have hint_base : IntegrableOn
          (fun t : ℝ => Real.exp (-(2 * Real.pi * (n : ℝ) * t)) * t ^ (s.re - 1))
          (Set.Ioi 0) volume :=
        integrableOn_exp_neg_mul_rpow ha_pos hs_pos
      have hint : IntegrableOn
          (fun t : ℝ => ‖qExpansionCoeff f n‖ *
            (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) * t ^ (s.re - 1)))
          (Set.Ioi 0) volume :=
        hint_base.const_mul _
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          fun t : ℝ => ‖qExpansionCoeff f n‖ *
            (Real.exp (-(2 * Real.pi * (n : ℝ) * t)) * t ^ (s.re - 1)) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _))
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn,
        MeasureTheory.integral_const_mul, mellin_exp_neg_mul_real ha_pos hs_pos]
      congr 1
      rw [LSeries.term_of_ne_zero hn, norm_div,
        show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
        Real.mul_rpow h2pi_pos.le hn_pos.le, Real.rpow_neg hn_pos.le, div_eq_mul_inv]
      ring
  have hne_top : (∑' n : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
      ‖qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
        (t : ℂ) ^ (s - 1)‖ₑ) ≠ ⊤ := by
    simp_rw [hlint_term]
    have hsum_real : Summable (fun n : ℕ =>
        (2 * Real.pi) ^ (-s.re) * Real.Gamma s.re * ‖LSeries.term (qExpansionCoeff f) s n‖) :=
      hLsumm.norm.mul_left _
    have hnn_real : ∀ n : ℕ, 0 ≤
        (2 * Real.pi) ^ (-s.re) * Real.Gamma s.re * ‖LSeries.term (qExpansionCoeff f) s n‖ := by
      intro n
      exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg h2pi_pos.le _) (Real.Gamma_pos_of_pos hs_pos).le)
        (norm_nonneg _)
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn_real hsum_real]
    exact ENNReal.ofReal_ne_top
  -- Interchange integral and infinite sum
  have hcongr : completedCuspL f s =
      ∫ t in Set.Ioi (0 : ℝ), ∑' n : ℕ,
        qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
          (t : ℂ) ^ (s - 1) := by
    unfold completedCuspL
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← (hasSum_cuspImag_qExpansion f ht).tsum_eq, tsum_mul_right]
  rw [hcongr, MeasureTheory.integral_tsum haes hne_top]
  have hterm : ∀ n : ℕ,
      (∫ t in Set.Ioi (0 : ℝ),
        qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
          (t : ℂ) ^ (s - 1)) =
      (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * LSeries.term (qExpansionCoeff f) s n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [qExpansionCoeff_zero f]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have ha_pos : 0 < 2 * Real.pi * (n : ℝ) := mul_pos h2pi_pos hn_pos
      have hfun : (fun t : ℝ =>
          qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) *
            (t : ℂ) ^ (s - 1)) =
          fun t : ℝ => qExpansionCoeff f n *
            (((Real.exp (-(2 * Real.pi * (n : ℝ) * t)) : ℝ) : ℂ) * (t : ℂ) ^ (s - 1)) := by
        funext t; ring
      rw [hfun, MeasureTheory.integral_const_mul, mellin_exp_neg_mul_complex ha_pos hs_pos]
      have hsplit : ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) ^ (-s) =
          (2 * (Real.pi : ℂ)) ^ (-s) * ((n : ℂ) ^ s)⁻¹ := by
        have hmul := Complex.mul_cpow_ofReal_nonneg h2pi_pos.le hn_pos.le (-s)
        rw [Complex.ofReal_mul, hmul, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_natCast, Complex.cpow_neg (n : ℂ) s]
      rw [hsplit, LSeries.term_of_ne_zero hn, div_eq_mul_inv]
      ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  rfl

/-- **ENTIRETY OF THE UNCOMPLETED `L`-FUNCTION `L(f, s)` (Hecke 1936, `0` Assumptions!)**:
`cuspL f` is **entire** (`Differentiable ℂ`) on all of `ℂ` for EVERY level-1 cusp form `f`! -/
theorem differentiable_cuspL_entire {k : ℤ} (f : CuspForm SL2ZRange k) :
    Differentiable ℂ (cuspL f) := by
  unfold cuspL
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h1 : Differentiable ℂ (fun s : ℂ => (2 * (Real.pi : ℂ)) ^ s) :=
    differentiable_id.const_cpow (Or.inl h2pi_ne)
  exact (h1.mul Complex.differentiable_one_div_Gamma).mul (differentiable_completedCuspL f)

/-- **Agreement of `cuspL f s` with the Dirichlet Series `LSeries (qExpansionCoeff f) s`**
on the half-plane `Re(s) > k / 2 + 1`. -/
theorem cuspL_eq_LSeries {k : ℤ} (hk : 0 < k) (f : CuspForm SL2ZRange k)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    cuspL f s = LSeries (qExpansionCoeff f) s := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := Int.cast_pos.mpr hk
  have hs_pos : 0 < s.re := by linarith
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hgam_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs_pos
  unfold cuspL
  rw [completedCuspL_eq_gamma_mul_LSeries hk f hs]
  have hpow : (2 * (Real.pi : ℂ)) ^ s * (2 * (Real.pi : ℂ)) ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ h2pi_ne, add_neg_cancel, Complex.cpow_zero]
  calc (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ *
          ((2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * LSeries (qExpansionCoeff f) s)
      = ((2 * (Real.pi : ℂ)) ^ s * (2 * (Real.pi : ℂ)) ^ (-s)) *
          ((Complex.Gamma s)⁻¹ * Complex.Gamma s) * LSeries (qExpansionCoeff f) s := by ring
    _ = 1 * 1 * LSeries (qExpansionCoeff f) s := by rw [hpow, inv_mul_cancel₀ hgam_ne]
    _ = LSeries (qExpansionCoeff f) s := by ring

/-- Exact global identification `cuspL f s = ModularForm.L hk f s` for EVERY `s : ℂ`. -/
theorem cuspL_eq_modularForm_L {k : ℤ} (hk : 0 < k) (f : CuspForm SL2ZRange k) (s : ℂ) :
    cuspL f s = ModularForm.L hk f s := by
  unfold cuspL ModularForm.L
  rw [completedCuspL_eq_modularForm_Λ hk f s, Complex.Gammaℂ_def]
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow_ne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl h2pi_ne)
  have hpow_inv : ((2 * (Real.pi : ℂ)) ^ (-s))⁻¹ = (2 * (Real.pi : ℂ)) ^ s := by
    rw [Complex.cpow_neg, inv_inv]
  by_cases hgam : Complex.Gamma s = 0
  · simp [hgam]
  · rw [div_eq_mul_inv, mul_inv, mul_inv, hpow_inv]
    field_simp [h2_ne, hgam]

/-- **Trivial Zeros of `L(f, s)` at All Non-Positive Integers**:
for EVERY level-1 cusp form `f ∈ S_k(SL₂(ℤ))` and EVERY `m : ℕ`, `cuspL f (-m) = 0`! -/
theorem cuspL_neg_nat_eq_zero {k : ℤ} (f : CuspForm SL2ZRange k) (m : ℕ) :
    cuspL f (-(m : ℂ)) = 0 := by
  unfold cuspL
  rw [Complex.Gamma_neg_nat_eq_zero m, inv_zero, mul_zero, zero_mul]

end HeckeTheorem

/-! ## Section 3: Specialization to Ramanujan's `Δ(τ)` (`completedDeltaL`, `deltaL`) -/

section RamanujanDeltaLFunction

/-- **Hecke's Completed Ramanujan `L`-Function `Λ(Δ, s)`**. -/
def completedDeltaL (s : ℂ) : ℂ :=
  completedCuspL ramanujanDelta s

/-- **Entire Analytic Continuation of Ramanujan's `L`-Function `L(Δ, s)`**. -/
def deltaL (s : ℂ) : ℂ :=
  cuspL ramanujanDelta s

@[simp]
theorem qExpansionCoeff_ramanujanDelta (n : ℕ) :
    qExpansionCoeff ramanujanDelta n = (ramanujanTau n : ℂ) :=
  (ramanujanTau_cast_eq_qExpansion_coeff n).symm

/-- **Entirety of `Λ(Δ, s)` on ALL of `ℂ`**. -/
theorem differentiable_completedDeltaL : Differentiable ℂ completedDeltaL :=
  differentiable_completedCuspL ramanujanDelta

/-- **Entirety of `L(Δ, s)` on ALL of `ℂ`**. -/
theorem differentiable_deltaL : Differentiable ℂ deltaL :=
  differentiable_cuspL_entire ramanujanDelta

/-- **UNCONDITIONAL FUNCTIONAL EQUATION FOR RAMANUJAN'S `Δ` (Hecke 1936, `0` Assumptions!)**:
for EVERY `s : ℂ`,
$$\Lambda(\Delta, 12 - s) = \Lambda(\Delta, s).$$ -/
theorem completedDeltaL_functional_equation (s : ℂ) :
    completedDeltaL (12 - s) = completedDeltaL s := by
  unfold completedDeltaL
  have h := completedCuspL_functional_equation ramanujanDelta s
  have hI12 : Complex.I ^ (12 : ℤ) = 1 := by
    change Complex.I ^ (12 : ℕ) = 1
    calc Complex.I ^ 12 = (Complex.I ^ 2) ^ 6 := by ring
      _ = (-1 : ℂ) ^ 6 := by rw [Complex.I_sq]
      _ = 1 := by norm_num
  have h12 : ((12 : ℤ) : ℂ) = (12 : ℂ) := by norm_num
  rw [h12, hI12, one_mul] at h
  exact h

/-- **Exact Mellin–Dirichlet Identity for `Λ(Δ, s)` on `Re(s) > 7`**:
`Λ(Δ, s) = (2π)^{-s} Γ(s) ∑_{n ≥ 1} τ(n) n^{-s}`. -/
theorem completedDeltaL_eq_gamma_mul_LSeries {s : ℂ} (hs : 7 < s.re) :
    completedDeltaL s =
      (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
        LSeries (fun n => (ramanujanTau n : ℂ)) s := by
  have hfun : qExpansionCoeff ramanujanDelta = fun n => (ramanujanTau n : ℂ) := by
    funext n; exact qExpansionCoeff_ramanujanDelta n
  unfold completedDeltaL
  rw [completedCuspL_eq_gamma_mul_LSeries (by norm_num : (0 : ℤ) < 12) ramanujanDelta
    (by norm_num; linarith), hfun]

/-- **Agreement `deltaL s = LSeries τ s` on `Re(s) > 7`**. -/
theorem deltaL_eq_LSeries {s : ℂ} (hs : 7 < s.re) :
    deltaL s = LSeries (fun n => (ramanujanTau n : ℂ)) s := by
  have hfun : qExpansionCoeff ramanujanDelta = fun n => (ramanujanTau n : ℂ) := by
    funext n; exact qExpansionCoeff_ramanujanDelta n
  unfold deltaL
  rw [cuspL_eq_LSeries (by norm_num : (0 : ℤ) < 12) ramanujanDelta (by norm_num; linarith), hfun]

/-- **Exact Global Agreement with Mathlib's `ModularForm.L` for `Δ`** on ALL of `ℂ`. -/
theorem deltaL_eq_modularForm_L (s : ℂ) :
    deltaL s = ModularForm.L (by norm_num : (0 : ℤ) < 12) ramanujanDelta s :=
  cuspL_eq_modularForm_L (by norm_num : (0 : ℤ) < 12) ramanujanDelta s

/-- **Trivial Zeros of `L(Δ, s)` at Every Non-Positive Integer `s = -m` (`m : ℕ`)**. -/
theorem deltaL_neg_nat_eq_zero (m : ℕ) : deltaL (-(m : ℂ)) = 0 :=
  cuspL_neg_nat_eq_zero ramanujanDelta m

/-- **UNCONDITIONAL DEGREE-2 EULER PRODUCT FOR `deltaL s` ON `Re(s) > 7`**:
connecting directly to `Stage8RamanujanDelta.ramanujanDelta_LSeries_eulerProduct`! -/
theorem deltaL_euler_product {s : ℂ} (hs : 7 < s.re) :
    deltaL s =
      ∏' p : Nat.Primes,
        (1 - (ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ := by
  rw [deltaL_eq_LSeries hs]
  exact ramanujanDelta_LSeries_eulerProduct hs

/-- **NON-VANISHING OF `L(Δ, s)` IN THE EULER PRODUCT HALF-PLANE `Re(s) > 7`**:
for EVERY `s : ℂ` with `7 < s.re`, `deltaL s ≠ 0`! -/
theorem deltaL_ne_zero_of_re_gt_seven {s : ℂ} (hs : 7 < s.re) :
    deltaL s ≠ 0 := by
  rw [deltaL_eq_LSeries hs]
  let a : Nat.Primes → ℂ := fun p =>
    -(ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s)
  have hsum_tau : Summable (fun p : Nat.Primes => -(ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s)) := by
    have hL : Summable (fun p : Nat.Primes => LSeries.term (fun n => (ramanujanTau n : ℂ)) s p.1) :=
      (LSeriesSummable_ramanujanTau hs).comp_injective (Subtype.val_injective (p := Nat.Prime))
    have hneg := hL.neg
    refine hneg.congr fun p => ?_
    have hp0 : p.1 ≠ 0 := p.prop.ne_zero
    simp only [LSeries.term_of_ne_zero hp0, div_eq_mul_inv, Complex.cpow_neg]
    ring
  have hsum_pow : Summable (fun p : Nat.Primes => (p.1 : ℂ) ^ (11 - 2 * s)) := by
    have hre : 1 < 2 * s.re - 11 := by linarith
    have hreal : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * s.re - 11))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr hre
    have hsub : Summable (fun p : Nat.Primes => ((p.1 : ℝ) ^ (2 * s.re - 11))⁻¹) :=
      hreal.comp_injective (Subtype.val_injective (p := Nat.Prime))
    refine Summable.of_norm (hsub.congr fun p => ?_)
    have hp_pos : (0 : ℝ) < (p.1 : ℝ) := Nat.cast_pos.mpr p.prop.pos
    have hre_exp : (11 - 2 * s).re = -(2 * s.re - 11) := by simp
    change ((p.1 : ℝ) ^ (2 * s.re - 11))⁻¹ = ‖(p.1 : ℂ) ^ (11 - 2 * s)‖
    rw [show (p.1 : ℂ) = ((p.1 : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, hre_exp, Real.rpow_neg hp_pos.le]
  have hsum_a : Summable a := hsum_tau.add hsum_pow
  have hmult : Multipliable (fun p : Nat.Primes => 1 + a p) :=
    Complex.multipliable_one_add_of_summable hsum_a
  -- Extract convergence of finite products over `B.primesBelow`
  let embed : ℕ → Finset Nat.Primes := fun B =>
    Finset.map
      ⟨fun (x : {p // p ∈ B.primesBelow}) => (⟨x.1, Nat.prime_of_mem_primesBelow x.2⟩ : Nat.Primes),
       fun x y hxy => Subtype.ext (congrArg (fun p : Nat.Primes => p.1) hxy)⟩
      B.primesBelow.attach
  have hembed_atTop : Tendsto embed atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro S
    rw [Filter.eventually_atTop]
    refine ⟨S.sup (fun p => p.1) + 1, fun B hB => ?_⟩
    intro p hpS
    have hlt : p.1 < B := by
      have hle : p.1 ≤ S.sup (fun q => q.1) := Finset.le_sup (f := fun q : Nat.Primes => q.1) hpS
      omega
    have hmem : p.1 ∈ B.primesBelow := Nat.mem_primesBelow.mpr ⟨hlt, p.prop⟩
    rw [Finset.mem_map]
    exact ⟨⟨p.1, hmem⟩, Finset.mem_attach _ _, rfl⟩
  have hprod_tendsto : Tendsto
      (fun B : ℕ => ∏ p ∈ B.primesBelow,
        (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s)))
      atTop (nhds (∏' p : Nat.Primes, (1 + a p))) := by
    have h1 := hmult.hasProd.comp hembed_atTop
    refine h1.congr fun B => ?_
    dsimp only [Function.comp_apply, embed]
    rw [Finset.prod_map, ← Finset.prod_attach B.primesBelow]
    refine Finset.prod_congr rfl fun x _ => ?_
    change 1 + (-(ramanujanTau x.1 : ℂ) * (x.1 : ℂ) ^ (-s) + (x.1 : ℂ) ^ (11 - 2 * s)) =
      1 - (ramanujanTau x.1 : ℂ) * (x.1 : ℂ) ^ (-s) + (x.1 : ℂ) ^ (11 - 2 * s)
    ring
  have hinv_tendsto := ramanujanDelta_LSeries_eulerProduct_tendsto hs
  have hmul_tendsto := hprod_tendsto.mul hinv_tendsto
  have hconst_one : ∀ B : ℕ,
      (∏ p ∈ B.primesBelow,
        (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))) *
      (∏ p ∈ B.primesBelow,
        (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹) = 1 := by
    intro B
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hp' : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hfac_ne := degree2EulerFactor_ne_zero isNormalizedHeckeEigenform_ramanujanTau
      (LSeriesSummable_ramanujanTau hs) hp'
    have hfac_eq : degree2EulerFactor 12 (1 : DirichletCharacter ℂ 1) (ramanujanTau p : ℂ) p s =
        (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹ := by
      simp only [degree2EulerFactor, trivialChar_one_apply, one_mul]
      norm_num
    rw [hfac_eq] at hfac_ne
    have hne : 1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s) ≠ 0 :=
      fun h0 => hfac_ne (by rw [h0, inv_zero])
    exact mul_inv_cancel₀ hne
  have heq_one : (∏' p : Nat.Primes, (1 + a p)) * LSeries (fun n => (ramanujanTau n : ℂ)) s = 1 := by
    have hlim1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) := tendsto_const_nhds
    have hmul' : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop
        (nhds ((∏' p : Nat.Primes, (1 + a p)) * LSeries (fun n => (ramanujanTau n : ℂ)) s)) :=
      hmul_tendsto.congr hconst_one
    exact tendsto_nhds_unique hmul' hlim1
  exact right_ne_zero_of_mul_eq_one heq_one

/-! ### Reality, Strict Positivity of `Δ(i y) > 0`, and Real-Line Positivity of `Λ(Δ, σ)` -/

/-- For every `y > 0`, `Δ(i y)` is real (`(Δ(i y)).im = 0`). -/
theorem ramanujanDelta_imag_im_eq_zero {y : ℝ} (hy : 0 < y) :
    (ramanujanDelta (imagPt y hy)).im = 0 := by
  have hhas := hasSum_cuspImag_qExpansion ramanujanDelta hy
  rw [cuspImag_of_pos ramanujanDelta hy] at hhas
  have him := Complex.continuous_im.continuousAt.tendsto.comp hhas
  have hzero : ∀ s : Finset ℕ,
      (∑ n ∈ s, qExpansionCoeff ramanujanDelta n *
        ((Real.exp (-(2 * Real.pi * (n : ℝ) * y)) : ℝ) : ℂ)).im = 0 := by
    intro s
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [qExpansionCoeff_ramanujanDelta n, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  have him0 : Tendsto (fun _ : Finset ℕ => (0 : ℝ)) atTop
      (nhds (ramanujanDelta (imagPt y hy)).im) :=
    him.congr hzero
  exact tendsto_nhds_unique him0 tendsto_const_nhds

/-- Exact value `Δ(i) > 0` (from `E₆(i) = 0`, `E₄(i) = 1 + 240 ∑_{n ≥ 1} σ₃(n) e^{-2πn} ≥ 1`,
and `Δ(i) = E₄(i)³ / 1728`). -/
private lemma ramanujanDelta_at_I_re_pos :
    0 < (ramanujanDelta (imagPt 1 zero_lt_one)).re := by
  have hpt : imagPt 1 zero_lt_one = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    simp [imagPt]
  rw [hpt, ramanujanDelta_apply UpperHalfPlane.I, E6_at_I]
  have hhasE4 := ModularForm.hasSum_qExpansion ModularForm.E₄ zero_lt_one
    one_mem_strictPeriods_SL UpperHalfPlane.I
  rw [← E4_eq_modularForm_E4 UpperHalfPlane.I] at hhasE4
  have hqI : Function.Periodic.qParam 1 (UpperHalfPlane.I : ℂ) =
      ((Real.exp (-2 * Real.pi) : ℝ) : ℂ) := by
    have h := qParam_one_imag 1
    simpa [mul_one] using h
  have hterm : ∀ m : ℕ,
      (((if m = 0 then (1 : ℝ) else 240 * (ArithmeticFunction.sigma 3 m : ℝ)) *
          (Real.exp (-2 * Real.pi)) ^ m : ℝ) : ℂ) =
      PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ)) *
        Function.Periodic.qParam 1 (UpperHalfPlane.I : ℂ) ^ m := by
    intro m
    rw [← E4_eq_coe, E4_qExpansion_coeff m, hqI, ← Complex.ofReal_pow]
    split_ifs <;> push_cast <;> rfl
  have hhasE4' : HasSum
      (fun m : ℕ => (((if m = 0 then (1 : ℝ) else 240 * (ArithmeticFunction.sigma 3 m : ℝ)) *
        (Real.exp (-2 * Real.pi)) ^ m : ℝ) : ℂ))
      (E4 UpperHalfPlane.I) :=
    hhasE4.congr_fun hterm
  have hE4_im : (E4 UpperHalfPlane.I).im = 0 := by
    have him := Complex.continuous_im.continuousAt.tendsto.comp hhasE4'
    have h0 : ∀ s : Finset ℕ, (∑ m ∈ s,
        (((if m = 0 then (1 : ℝ) else 240 * (ArithmeticFunction.sigma 3 m : ℝ)) *
          (Real.exp (-2 * Real.pi)) ^ m : ℝ) : ℂ)).im = 0 := by
      intro s; rw [Complex.im_sum]
      exact Finset.sum_eq_zero fun m _ => Complex.ofReal_im _
    exact tendsto_nhds_unique (him.congr h0) tendsto_const_nhds
  have hE4_re_ge : (1 : ℝ) ≤ (E4 UpperHalfPlane.I).re := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hhasE4'
    have hre_term : ∀ m : ℕ,
        (0 : ℝ) ≤ (if m = 0 then (1 : ℝ) else 240 * (ArithmeticFunction.sigma 3 m : ℝ)) *
          (Real.exp (-2 * Real.pi)) ^ m := by
      intro m
      refine mul_nonneg ?_ (pow_nonneg (Real.exp_pos _).le m)
      split_ifs <;> positivity
    have hge : ∀ᶠ s : Finset ℕ in atTop,
        (1 : ℝ) ≤ (∑ m ∈ s,
          (((if m = 0 then (1 : ℝ) else 240 * (ArithmeticFunction.sigma 3 m : ℝ)) *
            (Real.exp (-2 * Real.pi)) ^ m : ℝ) : ℂ)).re := by
      filter_upwards [Filter.eventually_ge_atTop ({0} : Finset ℕ)] with s hs
      have h0mem : (0 : ℕ) ∈ s := hs (Finset.mem_singleton_self 0)
      rw [Complex.re_sum]
      simp_rw [Complex.ofReal_re]
      have hsingle := Finset.single_le_sum (f := fun m : ℕ =>
          (if m = 0 then (1 : ℝ) else 240 * (ArithmeticFunction.sigma 3 m : ℝ)) *
            (Real.exp (-2 * Real.pi)) ^ m)
        (fun m _ => hre_term m) h0mem
      simpa using hsingle
    exact ge_of_tendsto hre hge
  have hE4_eq : E4 UpperHalfPlane.I = ((E4 UpperHalfPlane.I).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hE4_im]
  rw [hE4_eq]
  have hval : ((((E4 UpperHalfPlane.I).re : ℂ) ^ 3 - 0 ^ 2) / 1728 : ℂ) =
      ((((E4 UpperHalfPlane.I).re ^ 3 / 1728 : ℝ)) : ℂ) := by
    push_cast; ring
  rw [hval, Complex.ofReal_re]
  positivity

/-- **Strict Positivity of Ramanujan's Discriminant Along the Entire Positive Imaginary Axis**:
for EVERY `y > 0`, `Δ(i y)` is real and strictly positive (`0 < (Δ(i y)).re`)! -/
theorem ramanujanDelta_imag_re_pos {y : ℝ} (hy : 0 < y) :
    0 < (ramanujanDelta (imagPt y hy)).re := by
  let g : ℝ → ℝ := fun t => (cuspImag ramanujanDelta t).re
  have hg_cont : ContinuousOn g (Set.Ioi (0 : ℝ)) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_cuspImag ramanujanDelta)
  have hg_ne : ∀ t ∈ Set.Ioi (0 : ℝ), g t ≠ 0 := by
    intro t ht h0
    have him : (ramanujanDelta (imagPt t ht)).im = 0 := ramanujanDelta_imag_im_eq_zero ht
    have hre : (ramanujanDelta (imagPt t ht)).re = 0 := by
      simpa [g, cuspImag_of_pos ramanujanDelta ht] using h0
    have hzero : ramanujanDelta (imagPt t ht) = 0 := Complex.ext hre him
    rw [ramanujanDelta_coe] at hzero
    exact discriminant_ne_zero (imagPt t ht) hzero
  have hg1 : 0 < g 1 := by
    simpa [g, cuspImag_of_pos ramanujanDelta zero_lt_one] using ramanujanDelta_at_I_re_pos
  have hgy_eq : g y = (ramanujanDelta (imagPt y hy)).re := by
    simp [g, cuspImag_of_pos ramanujanDelta hy]
  by_contra hle
  rw [← hgy_eq] at hle
  have hlt : g y < 0 := lt_of_le_of_ne (not_lt.mp hle) (hg_ne y hy)
  have hconn : IsPreconnected (Set.Ioi (0 : ℝ)) := convex_Ioi (0 : ℝ) |>.isPreconnected
  have himg_conn : IsPreconnected (g '' Set.Ioi (0 : ℝ)) := hconn.image g hg_cont
  have h0mem : (0 : ℝ) ∈ Set.Icc (g y) (g 1) := ⟨hlt.le, hg1.le⟩
  have hsub : Set.Icc (g y) (g 1) ⊆ g '' Set.Ioi (0 : ℝ) :=
    himg_conn.Icc_subset ⟨y, Set.mem_Ioi.mpr hy, rfl⟩ ⟨1, Set.mem_Ioi.mpr zero_lt_one, rfl⟩
  obtain ⟨t, ht, hgt⟩ := hsub h0mem
  exact hg_ne t ht hgt

theorem cuspImag_ramanujanDelta_eq_ofReal {y : ℝ} (hy : 0 < y) :
    cuspImag ramanujanDelta y = ((cuspImag ramanujanDelta y).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im, cuspImag_of_pos ramanujanDelta hy]
    exact ramanujanDelta_imag_im_eq_zero hy

/-- **Conjugate Symmetry of `Λ(Δ, s)`**:
`Λ(Δ, conj s) = conj (Λ(Δ, s))` for EVERY `s : ℂ`. -/
theorem completedDeltaL_conj (s : ℂ) :
    completedDeltaL (starRingEnd ℂ s) = starRingEnd ℂ (completedDeltaL s) := by
  unfold completedDeltaL completedCuspL
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_pos.ne
  have hcpow := Complex.cpow_conj (t : ℂ) (s - 1) harg
  rw [Complex.conj_ofReal, map_sub, map_one] at hcpow
  rw [map_mul, ← hcpow]
  congr 1
  rw [cuspImag_ramanujanDelta_eq_ofReal ht0, Complex.conj_ofReal]

/-- **Reality of `Λ(Δ, σ)` on the Real Axis**:
for EVERY `σ : ℝ`, `(Λ(Δ, σ)).im = 0`. -/
theorem completedDeltaL_real_on_real (σ : ℝ) :
    (completedDeltaL (σ : ℂ)).im = 0 := by
  have h := completedDeltaL_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **STRICT POSITIVITY OF `Λ(Δ, σ)` ON THE ENTIRE REAL LINE**:
for EVERY `σ : ℝ`, `0 < (Λ(Δ, σ)).re`! -/
theorem completedDeltaL_pos_on_real (σ : ℝ) :
    0 < (completedDeltaL (σ : ℂ)).re := by
  let hfun : ℝ → ℝ := fun t => (cuspImag ramanujanDelta t).re * t ^ (σ - 1)
  have heq : completedDeltaL (σ : ℂ) =
      ((∫ t in Set.Ioi (0 : ℝ), hfun t : ℝ) : ℂ) := by
    unfold completedDeltaL completedCuspL
    have hofReal : (∫ t in Set.Ioi (0 : ℝ), (hfun t : ℂ)) =
        ((∫ t in Set.Ioi (0 : ℝ), hfun t : ℝ) : ℂ) := integral_ofReal
    rw [← hofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    dsimp only [hfun]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le, Complex.ofReal_sub, Complex.ofReal_one]
    congr 1
    exact cuspImag_ramanujanDelta_eq_ofReal ht0
  rw [heq, Complex.ofReal_re]
  have hintC : IntegrableOn (fun t : ℝ => cuspImag ramanujanDelta t * (t : ℂ) ^ ((σ : ℂ) - 1))
      (Set.Ioi 0) volume := by
    refine (mellinConvergent_cuspImag ramanujanDelta (σ : ℂ)).congr_fun
      (fun t _ => by dsimp only; rw [smul_eq_mul, mul_comm]) measurableSet_Ioi
  have hintR : IntegrableOn hfun (Set.Ioi 0) volume := by
    refine IntegrableOn.congr_fun hintC.re (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    dsimp only [hfun]
    change ((cuspImag ramanujanDelta t * (t : ℂ) ^ ((σ : ℂ) - 1))).re = _
    have h1 : cuspImag ramanujanDelta t * (t : ℂ) ^ ((σ : ℂ) - 1) =
        (((cuspImag ramanujanDelta t).re * t ^ (σ - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0.le, Complex.ofReal_sub, Complex.ofReal_one]
      congr 1
      exact cuspImag_ramanujanDelta_eq_ofReal ht0
    rw [h1, Complex.ofReal_re]
  have hpos_on : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < hfun t := by
    intro t ht
    have ht0 : 0 < t := ht
    dsimp only [hfun]
    rw [cuspImag_of_pos ramanujanDelta ht0]
    exact mul_pos (ramanujanDelta_imag_re_pos ht0) (Real.rpow_pos_of_pos ht0 _)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] hfun := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hpos_on t ht).le
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hintR]
  have hsupp : Function.support hfun ∩ Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
    intro ht
    exact (hpos_on t ht).ne'
  rw [hsupp]
  exact Real.volume_Ioi ▸ ENNReal.zero_lt_top

/-- **Conjugate Symmetry of `L(Δ, s)`**: `L(Δ, conj s) = conj (L(Δ, s))` for all `s : ℂ`. -/
theorem deltaL_conj (s : ℂ) :
    deltaL (starRingEnd ℂ s) = starRingEnd ℂ (deltaL s) := by
  have harg : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
    have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg hpos.le]
    exact Real.pi_pos.ne
  have h2pi_conj : starRingEnd ℂ (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) := by
    rw [map_mul, map_ofNat, Complex.conj_ofReal]
  have hcpow := Complex.cpow_conj (2 * (Real.pi : ℂ)) s harg
  rw [h2pi_conj] at hcpow
  change (2 * (Real.pi : ℂ)) ^ (starRingEnd ℂ s) * (Complex.Gamma (starRingEnd ℂ s))⁻¹ *
      completedDeltaL (starRingEnd ℂ s) =
    starRingEnd ℂ ((2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ * completedDeltaL s)
  rw [map_mul, map_mul, map_inv₀, ← hcpow, Complex.Gamma_conj, completedDeltaL_conj s]

/-- **Reality of `L(Δ, σ)` on the Real Axis**: `(L(Δ, σ)).im = 0` for all `σ : ℝ`. -/
theorem deltaL_real_on_real (σ : ℝ) : (deltaL (σ : ℂ)).im = 0 := by
  have h := deltaL_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

/-- **Strict Positivity of `L(Δ, σ)` on the Positive Real Axis `(0, ∞)`**:
for EVERY `σ > 0`, `0 < (L(Δ, σ)).re`! -/
theorem deltaL_pos_on_pos_real {σ : ℝ} (hσ : 0 < σ) :
    0 < (deltaL (σ : ℂ)).re := by
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hL_eq : completedDeltaL (σ : ℂ) = ((completedDeltaL (σ : ℂ)).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [completedDeltaL_real_on_real σ]
  have hval : deltaL (σ : ℂ) =
      ((((2 * Real.pi) ^ σ * (Real.Gamma σ)⁻¹ * (completedDeltaL (σ : ℂ)).re : ℝ)) : ℂ) := by
    unfold deltaL cuspL
    change (2 * (Real.pi : ℂ)) ^ (σ : ℂ) * (Complex.Gamma (σ : ℂ))⁻¹ * completedDeltaL (σ : ℂ) = _
    rw [hL_eq, show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow h2pi_pos.le, Complex.Gamma_ofReal]
    push_cast
    rfl
  rw [hval, Complex.ofReal_re]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos h2pi_pos σ)
    (inv_pos.mpr (Real.Gamma_pos_of_pos hσ))) (completedDeltaL_pos_on_real σ)

/-- **Positivity of the Central Value `L(Δ, 6) > 0`** (unconditional corollary of `Δ(i y) > 0`!). -/
theorem deltaL_central_value_pos : 0 < (deltaL 6).re := by
  simpa using deltaL_pos_on_pos_real (by norm_num : (0 : ℝ) < 6)

end RamanujanDeltaLFunction

end

end RHDirect.Stage9CuspFormLFunc
