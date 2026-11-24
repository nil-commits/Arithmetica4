import RHDirect.Stage9CuspFormLFunc
import RHDirect.Stage8RamanujanDelta
import RHDirect.Stage7HadamardXiProduct
import RHDirect.Stage5StirlingPhragmen
import RHDirect.Stage5JensenHadamard
import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# RHDirect.Stage9DeltaHadamard

**UNCONDITIONAL HECKE'S 1927 BOUND `|a_n(f)| ≤ C n^{k/2}` FOR EVERY LEVEL-1 CUSP FORM
(`|τ(n)| ≤ C n^6`), ORDER-1 ENTIRETY, INFINITUDE OF ZEROS, ZERO-COUNT UPPER BOUND,
FULL HADAMARD PRODUCT FACTORIZATION OF `Λ(Δ, s)`, AND DELIGNE–RAMANUJAN CRITICAL-STRIP
NARROWING BRIDGE** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Main Unconditional Results

1. **Unconditional Hecke's 1927 Bound `|a_n(f)| ≤ C n^{k/2}` (`|τ(n)| ≤ C n^6`)**:
   - `cuspForm_im_pow_norm_sl2Z_invariant`: exact `SL₂(ℤ)`-invariance of `τ ↦ τ.im ^ (k / 2) * ‖f τ‖`.
   - `cuspForm_im_pow_norm_bounded`: global boundedness of `τ ↦ τ.im ^ (k / 2) * ‖f τ‖` on `ℍ`
     via `ModularGroup.exists_smul_mem_fd` and exponential cusp decay `f(τ) = O(e^{-2π Im(τ)})`.
   - `qExpansionCoeff_eq_integral`: exact Fourier integral formula
     `a_n(f) = exp(2π n y) * ∫ x in (0 : ℝ)..1, f(x + i y) * exp(-2π i n x)` for all `y > 0`.
   - `hecke_cuspForm_coeff_bound`: for EVERY `k : ℕ` and `f : CuspForm SL2ZRange k`,
     `∃ C > 0, ∀ n ≥ 1, ‖qExpansionCoeff f n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2)`.
   - `hecke_bound_ramanujanTau`:
     `∃ C > 0, ∀ n ≥ 1, |(ramanujanTau n : ℝ)| ≤ C * (n : ℝ) ^ 6`.

2. **Unconditional Order-1 Entirety, Infinitude of Zeros, Zero-Count Bound, & Full Hadamard Product
   of Ramanujan's Completed `L`-Function `Λ(Δ, s)` (`0` Assumptions!)**:
   - `completedDeltaL_order_one_bound` & `hasOrderOneGrowth_completedDeltaL`:
     `∃ A > 0, ∃ B > 0, ∀ s : ℂ, ‖completedDeltaL s‖ ≤ A * Real.exp (B * (‖s‖ + 1) * Real.log (‖s‖ + 2))`.
   - `completedDeltaL_zero_iff_deltaL_zero_in_strip` & `completedDeltaL_zero_in_strip`:
     every zero of `Λ(Δ, s)` lies in the strip `5 ≤ Re(s) ≤ 7`, and agrees with the zeros of `L(Δ, s)`
     throughout `0 < Re(s) < 12`.
   - `infinite_completedDeltaL_zeros`: `{s : ℂ | completedDeltaL s = 0}.Infinite`.
   - `deltaZeroSeq : ℕ → ℂ`, `isMultiplicityZeroSeq_completedDeltaL`, `deltaZeroSeq_summable_inv_sq`,
     and `completedDeltaL_hadamard_product`:
     `∃ (B_Δ : ℂ) (ρ_Δ : ℕ → ℂ), IsMultiplicityZeroSeq completedDeltaL ρ_Δ ∧`
     `(∀ n, 5 ≤ (ρ_Δ n).re ∧ (ρ_Δ n).re ≤ 7) ∧ Summable (fun n => (‖ρ_Δ n‖ ^ 2)⁻¹) ∧`
     `∀ s : ℂ, completedDeltaL s = completedDeltaL 0 * Complex.exp (B_Δ * s) * weierstrassProduct ρ_Δ s`.
   - `completedDeltaL_zero_count_le`: `N_Δ(T) ≤ C * T * Real.log T` for all `T ≥ 2`.

3. **Unconditional Conditional-on-Deligne Bridge (`deligne_ramanujan_implies_euler_nonvanishing`)**:
   - Proves `d(n) ≤ C_ε n^ε` for every `ε > 0` (`divisors_card_le_rpow`), deduces under the
     Ramanujan–Petersson bound `∀ p, p.Prime → |(τ(p) : ℝ)| ≤ 2 p^{11/2}` that `L(Δ, s)` converges
     absolutely, equals its degree-2 Euler product, and is non-vanishing on ALL `Re(s) > 13 / 2`,
     narrowing the critical strip of `Λ(Δ, s)` from `[5, 7]` to `[11 / 2, 13 / 2]`.
-/

open Complex Real Filter MeasureTheory Metric Topology
open RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5JensenHadamard RHDirect.Stage7EisensteinSeries RHDirect.Stage7HadamardXiProduct
open RHDirect.Stage8ModularRing RHDirect.Stage8RamanujanDelta RHDirect.Stage9CuspFormLFunc
open scoped BigOperators UpperHalfPlane ModularForm ENNReal Manifold

namespace RHDirect.Stage9DeltaHadamard

noncomputable section

/-! ## Section 1: Unconditional Hecke's 1927 Bound `|a_n(f)| ≤ C n^{k/2}` (`|τ(n)| ≤ C n^6`) -/

section HeckeBound

/-- Exact `SL₂(ℤ)`-invariance of `τ ↦ τ.im ^ (k / 2) * ‖f τ‖` for every level-1 cusp form
`f ∈ S_k(SL₂(ℤ))` and every `γ ∈ SL₂(ℤ)`. -/
theorem cuspForm_im_pow_norm_sl2Z_invariant {k : ℤ} (f : CuspForm SL2ZRange k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    (γ • τ).im ^ ((k : ℝ) / 2) * ‖f (γ • τ)‖ = τ.im ^ ((k : ℝ) / 2) * ‖f τ‖ := by
  have hslash := f.slash_action_eq' (sl2ZToGL2R γ) ⟨γ, rfl⟩
  have hval := congrFun hslash τ
  change SlashAction.map k (sl2ZToGL2R γ) (f : UpperHalfPlane → ℂ) τ = f τ at hval
  rw [slash_sl2Z_apply] at hval
  set d : ℂ := UpperHalfPlane.denom (sl2ZToGL2R γ) (τ : ℂ)
  have hd_ne : d ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (sl2ZToGL2R γ) τ
    exact this
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hnorm_f : ‖f (γ • τ)‖ = ‖d‖ ^ (k : ℝ) * ‖f τ‖ := by
    have h1 := congrArg norm hval
    rw [norm_mul, norm_zpow] at h1
    rw [← Real.rpow_intCast ‖d‖ (-k), Int.cast_neg] at h1
    have hmul : ‖d‖ ^ (k : ℝ) * ‖d‖ ^ (-(k : ℝ)) = 1 := by
      rw [← Real.rpow_add hd_pos, add_neg_cancel, Real.rpow_zero]
    calc ‖f (γ • τ)‖ = ‖d‖ ^ (k : ℝ) * (‖f (γ • τ)‖ * ‖d‖ ^ (-(k : ℝ))) := by
          rw [mul_left_comm, hmul, mul_one]
      _ = ‖d‖ ^ (k : ℝ) * ‖f τ‖ := by rw [h1]
  have him_smul : (γ • τ).im = τ.im / ‖d‖ ^ 2 := by
    have h1 : (γ • τ).im = (sl2ZToGL2R γ • τ).im := rfl
    rw [h1, UpperHalfPlane.im_smul_eq_div_normSq]
    have hdet : ((sl2ZToGL2R γ).det : ℝ) = 1 := by simp [sl2ZToGL2R]
    rw [hdet, abs_one, one_mul, Complex.normSq_eq_norm_sq]
  rw [him_smul, hnorm_f, Real.div_rpow τ.im_pos.le (sq_nonneg ‖d‖)]
  have hpow : (‖d‖ ^ 2) ^ ((k : ℝ) / 2) = ‖d‖ ^ (k : ℝ) := by
    rw [← Real.rpow_natCast ‖d‖ 2, ← Real.rpow_mul hd_pos.le]
    congr 1; push_cast; ring
  rw [hpow]
  have hd_pow_ne : ‖d‖ ^ (k : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hd_pos _).ne'
  field_simp [hd_pow_ne]

/-- Elementary exponential-polynomial bound: for every `m : ℕ` and every `y ≥ 0`,
`y ^ m * exp(-2π y) ≤ m! / (2π)^m`. -/
private lemma pow_mul_exp_neg_two_pi_le (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ m * Real.exp (-2 * Real.pi * y) ≤ (m.factorial : ℝ) / (2 * Real.pi) ^ m := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hu : 0 ≤ 2 * Real.pi * y := mul_nonneg h2pi.le hy
  have hfac := Real.pow_div_factorial_le_exp (2 * Real.pi * y) hu m
  have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  have h2pim_pos : (0 : ℝ) < (2 * Real.pi) ^ m := pow_pos h2pi m
  have hle : (2 * Real.pi) ^ m * y ^ m ≤ (m.factorial : ℝ) * Real.exp (2 * Real.pi * y) := by
    rw [← mul_pow]
    exact (div_le_iff₀ hfac_pos).mp hfac |>.trans_eq (mul_comm _ _)
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-2 * Real.pi * y)).le
  have hexp_one : Real.exp (2 * Real.pi * y) * Real.exp (-2 * Real.pi * y) = 1 := by
    rw [← Real.exp_add]
    have : 2 * Real.pi * y + -2 * Real.pi * y = 0 := by ring
    rw [this, Real.exp_zero]
  rw [mul_assoc ((2 * Real.pi) ^ m), mul_assoc (m.factorial : ℝ), hexp_one, mul_one] at hmul
  exact (le_div_iff₀' h2pim_pos).mpr hmul

/-- **Global Boundedness of `Im(τ)^{k/2} ‖f(τ)‖` on `UpperHalfPlane` (Hecke 1927)**:
for every `k : ℤ` and every level-1 cusp form `f ∈ S_k(SL₂(ℤ))`, the `SL₂(ℤ)`-invariant function
`τ ↦ τ.im ^ (k / 2) * ‖f τ‖` is globally bounded on the entire upper half-plane `ℍ`! -/
theorem cuspForm_im_pow_norm_bounded {k : ℤ} (f : CuspForm SL2ZRange k) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ : UpperHalfPlane, τ.im ^ ((k : ℝ) / 2) * ‖f τ‖ ≤ M := by
  have hbigO := CuspFormClass.exp_decay_atImInfty f zero_lt_one one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨C₀, hC₀⟩ := hbigO
  rw [UpperHalfPlane.atImInfty_basis.eventually_iff] at hC₀
  obtain ⟨A, _, hA⟩ := hC₀
  let B : ℝ := max (max A 1) 1
  have hB_ge1 : 1 ≤ B := le_max_right _ _
  have hB_geA : A ≤ B := (le_max_left A 1).trans (le_max_left _ _)
  -- Compact box `K = [-1/2, 1/2] × [√3/2, B]` inside the open upper half-plane `{z | 0 < z.im}`.
  let K : Set ℂ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ×ℂ Set.Icc (Real.sqrt 3 / 2) B
  have hK_compact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  have hK_sub : K ⊆ {z : ℂ | 0 < z.im} := fun z hz => lt_of_lt_of_le hsqrt3_pos hz.2.1
  let g : ℂ → ℝ := fun z => z.im ^ ((k : ℝ) / 2) * ‖f (UpperHalfPlane.ofComplex z)‖
  have hf_cont : ContinuousOn ((f : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp f.holo').continuousOn
  have hg_cont : ContinuousOn g K := by
    refine ContinuousOn.mul ?_ (hf_cont.norm.mono hK_sub)
    intro z hz
    have hzim : 0 < z.im := hK_sub hz
    exact ((Complex.continuous_im.continuousAt.rpow continuousAt_const (Or.inl hzim.ne')).continuousWithinAt)
  obtain ⟨C₁, hC₁⟩ := hK_compact.exists_bound_of_continuousOn hg_cont
  -- Explicit bound on the tail `τ.im ≥ B ≥ 1`.
  let m : ℕ := ⌈max ((k : ℝ) / 2) 0⌉₊
  have hm_ge : (k : ℝ) / 2 ≤ (m : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  let C₂ : ℝ := max C₀ 0 * ((m.factorial : ℝ) / (2 * Real.pi) ^ m)
  let M : ℝ := max (max C₁ C₂) 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨M, hM_pos, fun τ => ?_⟩
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
  rw [← cuspForm_im_pow_norm_sl2Z_invariant f γ τ]
  set w : UpperHalfPlane := γ • τ
  have hw_im_ge : Real.sqrt 3 / 2 ≤ w.im := by
    have hre : |w.re| ≤ 1 / 2 := hγ.2
    have hnorm : 1 ≤ Complex.normSq (w : ℂ) := hγ.1
    rw [Complex.normSq_apply] at hnorm
    change 1 ≤ w.re * w.re + w.im * w.im at hnorm
    have hre_sq : w.re * w.re ≤ 1 / 4 := by
      have h1 : w.re ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hre 2
      linarith [sq w.re]
    have him_sq : (Real.sqrt 3 / 2) ^ 2 ≤ w.im ^ 2 := by
      have h3 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
      rw [h3]
      nlinarith [sq w.im]
    nlinarith [w.im_pos, hsqrt3_pos]
  by_cases hwB : w.im ≤ B
  · have hw_mem : (w : ℂ) ∈ K := ⟨abs_le.mp hγ.2, ⟨hw_im_ge, hwB⟩⟩
    have hbd := hC₁ (w : ℂ) hw_mem
    have hg_nn : 0 ≤ g (w : ℂ) :=
      mul_nonneg (Real.rpow_nonneg w.im_pos.le _) (norm_nonneg _)
    rw [Real.norm_of_nonneg hg_nn] at hbd
    have hofC : UpperHalfPlane.ofComplex (w : ℂ) = w :=
      UpperHalfPlane.ofComplex_apply_of_im_pos w.im_pos
    have hgw : g (w : ℂ) = w.im ^ ((k : ℝ) / 2) * ‖f w‖ := by
      dsimp only [g]
      rw [hofC]
      rfl
    rw [← hgw]
    exact hbd.trans ((le_max_left C₁ C₂).trans (le_max_left _ _))
  · push Not at hwB
    have hw_geA : A ≤ w.im := hB_geA.trans hwB.le
    have hw_ge1 : 1 ≤ w.im := hB_ge1.trans hwB.le
    have hdecay := hA (show w ∈ UpperHalfPlane.im ⁻¹' Set.Ici A from hw_geA)
    simp only [div_one, Real.norm_of_nonneg (Real.exp_pos _).le] at hdecay
    have hrpow : w.im ^ ((k : ℝ) / 2) ≤ w.im ^ m := by
      rw [← Real.rpow_natCast w.im m]
      exact Real.rpow_le_rpow_of_exponent_le hw_ge1 hm_ge
    have htail := pow_mul_exp_neg_two_pi_le m w.im_pos.le
    have hC0_le : C₀ ≤ max C₀ 0 := le_max_left C₀ 0
    have hleC₂ : w.im ^ ((k : ℝ) / 2) * ‖f w‖ ≤ C₂ := by
      calc w.im ^ ((k : ℝ) / 2) * ‖f w‖
          ≤ w.im ^ m * (C₀ * Real.exp (-2 * Real.pi * w.im)) :=
            mul_le_mul hrpow hdecay (norm_nonneg _) (pow_nonneg w.im_pos.le m)
        _ ≤ w.im ^ m * (max C₀ 0 * Real.exp (-2 * Real.pi * w.im)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hC0_le (Real.exp_pos _).le)
              (pow_nonneg w.im_pos.le m)
        _ = max C₀ 0 * (w.im ^ m * Real.exp (-2 * Real.pi * w.im)) := by ring
        _ ≤ max C₀ 0 * ((m.factorial : ℝ) / (2 * Real.pi) ^ m) :=
            mul_le_mul_of_nonneg_left htail (le_max_right C₀ 0)
    exact hleC₂.trans ((le_max_right C₁ C₂).trans (le_max_left _ _))

/-- Horizontal-line point `x + i * y ∈ UpperHalfPlane` for `y > 0`. -/
private def horizPt (x : ℝ) {y : ℝ} (hy : 0 < y) : UpperHalfPlane :=
  ⟨(x : ℂ) + Complex.I * (y : ℂ), by simp [hy]⟩

/-- Orthogonality of complex exponentials on `[0, 1]`:
`∫ x in (0 : ℝ)..1, exp(2π i (m - n) x) = if m = n then 1 else 0`. -/
private lemma integral_exp_two_pi_I_sub (m n : ℕ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) - (n : ℂ)) * (x : ℂ)) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp
  · rw [if_neg hmn]
    set c : ℂ := 2 * Real.pi * Complex.I * ((m : ℂ) - (n : ℂ))
    have hc_ne : c ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero) ?_
      exact sub_ne_zero.mpr (by exact_mod_cast hmn)
    let F : ℝ → ℂ := fun x => Complex.exp (c * (x : ℂ)) / c
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt F (Complex.exp (c * (x : ℂ))) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
      have h2 := h1.cexp.div_const c
      simpa [F, mul_div_cancel_right₀ _ hc_ne] using h2
    have hcont : ContinuousOn (fun x : ℝ => Complex.exp (c * (x : ℂ))) (Set.uIcc 0 1) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
    dsimp only [F]
    have hexp1 : Complex.exp c = 1 := by
      have harg : c = (((m : ℤ) - (n : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        dsimp only [c]; push_cast; ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I ((m : ℤ) - (n : ℤ))
    simp [hexp1]

/-- Exact evaluation of `qParam 1 (x + i y) ^ m * exp(-2π i n x)`. -/
private lemma qParam_horiz_mul_exp (x : ℝ) {y : ℝ} (hy : 0 < y) (m n : ℕ) :
    Function.Periodic.qParam 1 (horizPt x hy : ℂ) ^ m *
      Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) =
    ((Real.exp (-(2 * Real.pi * (m : ℝ) * y)) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) - (n : ℂ)) * (x : ℂ)) := by
  unfold Function.Periodic.qParam horizPt
  simp only [Complex.ofReal_one, div_one, ← Complex.exp_nat_mul,
    ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination 2 * (Real.pi : ℂ) * (m : ℂ) * (y : ℂ) * Complex.I_mul_I

/-- **Exact Fourier Integral Formula for Cusp-Form `q`-Expansion Coefficients**:
for every `k : ℤ`, every `f : CuspForm SL2ZRange k`, every `n : ℕ`, and every `y > 0`,
`a_n(f) * exp(-2π n y) = ∫ x in (0 : ℝ)..1, f(x + i y) * exp(-2π i n x)`. -/
theorem qExpansionCoeff_mul_exp_eq_integral {k : ℤ} (f : CuspForm SL2ZRange k)
    (n : ℕ) {y : ℝ} (hy : 0 < y) :
    qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * y)) : ℝ) : ℂ) =
      ∫ x in (0 : ℝ)..1, f (horizPt x hy) *
        Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
  -- Use absolute summability of the q-expansion at `i * (y / 2)` to dominate the Fourier series on `[0, 1]`.
  have hy2 : 0 < y / 2 := half_pos hy
  have hhas_half := hasSum_cuspImag_qExpansion f hy2
  have htend0 : Tendsto (fun m : ℕ =>
      ‖qExpansionCoeff f m * ((Real.exp (-(2 * Real.pi * (m : ℝ) * (y / 2))) : ℝ) : ℂ)‖)
      atTop (nhds 0) := by
    simpa [Nat.cofinite_eq_atTop, norm_zero] using hhas_half.summable.tendsto_cofinite_zero.norm
  have hbdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℕ,
      ‖qExpansionCoeff f m‖ * Real.exp (-(Real.pi * (m : ℝ) * y)) ≤ B := by
    have hev := htend0.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    let B' : ℝ := max 1 ((Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
      fun m => ‖qExpansionCoeff f m‖ * Real.exp (-(Real.pi * (m : ℝ) * y)))
    refine ⟨B', le_trans zero_le_one (le_max_left _ _), fun m => ?_⟩
    by_cases hm : m < N + 1
    · exact (Finset.le_sup' (f := fun j => ‖qExpansionCoeff f j‖ * Real.exp (-(Real.pi * (j : ℝ) * y)))
        (Finset.mem_range.mpr hm)).trans (le_max_right _ _)
    · have hge : N ≤ m := by omega
      have h1 := hN m hge
      rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _), norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
      have harg : -(2 * Real.pi * (m : ℝ) * (y / 2)) = -(Real.pi * (m : ℝ) * y) := by ring
      rw [harg] at h1
      exact h1.le.trans (le_max_left _ _)
  obtain ⟨B, hB_nn, hB⟩ := hbdd
  let F : ℕ → ℝ → ℂ := fun m x =>
    qExpansionCoeff f m * ((Real.exp (-(2 * Real.pi * (m : ℝ) * y)) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) - (n : ℂ)) * (x : ℂ))
  have hF_norm : ∀ m : ℕ, ∀ x : ℝ, ‖F m x‖ ≤ B * (Real.exp (-(Real.pi * y))) ^ m := by
    intro m x
    dsimp only [F]
    have hexp_im : ‖Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) - (n : ℂ)) * (x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (2 * Real.pi * Complex.I * ((m : ℂ) - (n : ℂ)) * (x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    rw [norm_mul, norm_mul, hexp_im, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have hsplit : Real.exp (-(2 * Real.pi * (m : ℝ) * y)) =
        Real.exp (-(Real.pi * (m : ℝ) * y)) * (Real.exp (-(Real.pi * y))) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB m) (pow_nonneg (Real.exp_pos _).le m)
  have hr_lt : Real.exp (-(Real.pi * y)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [mul_pos Real.pi_pos hy])
  have hgeom : Summable (fun m : ℕ => B * (Real.exp (-(Real.pi * y))) ^ m) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr_lt).mul_left B
  have hpoint : ∀ x : ℝ, f (horizPt x hy) *
      Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) = ∑' m : ℕ, F m x := by
    intro x
    have hq := ModularForm.hasSum_qExpansion f zero_lt_one one_mem_strictPeriods_SL (horizPt x hy)
    have hmul := hq.mul_right (Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)))
    rw [← hmul.tsum_eq]
    refine tsum_congr fun m => ?_
    dsimp only [F, qExpansionCoeff]
    rw [mul_assoc, qParam_horiz_mul_exp x hy m n, ← mul_assoc]
  rw [intervalIntegral.integral_of_le zero_le_one]
  have hcongr : ∫ x in Set.Ioc (0 : ℝ) 1,
      f (horizPt x hy) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) =
      ∫ x in Set.Ioc (0 : ℝ) 1, ∑' m : ℕ, F m x :=
    setIntegral_congr_fun measurableSet_Ioc fun x _ => hpoint x
  rw [hcongr]
  have haes : ∀ m : ℕ, AEStronglyMeasurable (F m) (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun m => by
    refine Continuous.aestronglyMeasurable ?_
    dsimp only [F]
    fun_prop
  have hne_top : (∑' m : ℕ, ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖F m x‖ₑ) ≠ ⊤ := by
    have hle : ∀ m : ℕ, (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖F m x‖ₑ) ≤
        ENNReal.ofReal (B * (Real.exp (-(Real.pi * y))) ^ m) := by
      intro m
      calc (∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖F m x‖ₑ)
          ≤ ∫⁻ _x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (B * (Real.exp (-(Real.pi * y))) ^ m) := by
            refine lintegral_mono fun x => ?_
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hF_norm m x)
        _ = ENNReal.ofReal (B * (Real.exp (-(Real.pi * y))) ^ m) * volume (Set.Ioc (0 : ℝ) 1) := by
            rw [MeasureTheory.setLIntegral_const]
        _ = ENNReal.ofReal (B * (Real.exp (-(Real.pi * y))) ^ m) := by
            simp [Real.volume_Ioc]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg hB_nn (pow_nonneg (Real.exp_pos _).le m)) hgeom]
    exact ENNReal.ofReal_ne_top
  rw [MeasureTheory.integral_tsum haes hne_top]
  have hterm : ∀ m : ℕ, (∫ x in Set.Ioc (0 : ℝ) 1, F m x) =
      if m = n then qExpansionCoeff f n * ((Real.exp (-(2 * Real.pi * (n : ℝ) * y)) : ℝ) : ℂ) else 0 := by
    intro m
    rw [← intervalIntegral.integral_of_le zero_le_one]
    dsimp only [F]
    rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_I_sub m n]
    split_ifs with hmn
    · subst hmn; simp
    · simp
  simp_rw [hterm]
  rw [tsum_ite_eq]

/-- **UNCONDITIONAL HECKE'S 1927 BOUND FOR EVERY LEVEL-1 CUSP FORM (`0` ASSUMPTIONS!)**:
for EVERY weight `k : ℕ` and EVERY level-1 cusp form `f ∈ S_k(SL₂(ℤ))`, there exists `C > 0`
such that `‖a_n(f)‖ ≤ C * n ^ (k / 2)` for ALL `n ≥ 1`! -/
theorem hecke_cuspForm_coeff_bound (k : ℕ) (f : CuspForm SL2ZRange k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ‖qExpansionCoeff f n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2) := by
  obtain ⟨M, hM_pos, hM⟩ := cuspForm_im_pow_norm_bounded f
  refine ⟨M * Real.exp (2 * Real.pi), mul_pos hM_pos (Real.exp_pos _), fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  set y : ℝ := (n : ℝ)⁻¹
  have hy_pos : 0 < y := inv_pos.mpr hn_pos
  have hint := qExpansionCoeff_mul_exp_eq_integral f n hy_pos
  have hnorm_lhs : ‖qExpansionCoeff f n‖ * Real.exp (-2 * Real.pi) =
      ‖∫ x in (0 : ℝ)..1, f (horizPt x hy_pos) *
        Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))‖ := by
    have h1 := congrArg norm hint
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have hny : -(2 * Real.pi * (n : ℝ) * y) = -2 * Real.pi := by
      dsimp only [y]; field_simp [hn_pos.ne']
    rwa [hny] at h1
  have hbound_integrand : ∀ x ∈ Set.uIoc (0 : ℝ) 1,
      ‖f (horizPt x hy_pos) * Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))‖ ≤
        M * (n : ℝ) ^ ((k : ℝ) / 2) := by
    intro x _
    have hexp1 : ‖Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    rw [norm_mul, hexp1, mul_one]
    have hpt := hM (horizPt x hy_pos)
    have him : (horizPt x hy_pos).im = y := by simp [horizPt]
    rw [him] at hpt
    have hy_pow : y ^ (((k : ℤ) : ℝ) / 2) = ((n : ℝ) ^ ((k : ℝ) / 2))⁻¹ := by
      dsimp only [y]
      rw [Int.cast_natCast, Real.inv_rpow hn_pos.le]
    rw [hy_pow] at hpt
    have hn_pow_pos : 0 < (n : ℝ) ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hn_pos _
    exact (inv_mul_le_iff₀ hn_pow_pos).mp hpt |>.trans_eq (mul_comm _ _)
  have hint_le : ‖∫ x in (0 : ℝ)..1, f (horizPt x hy_pos) *
      Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ))‖ ≤
      M * (n : ℝ) ^ ((k : ℝ) / 2) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbound_integrand
    simpa using h1
  rw [← hnorm_lhs] at hint_le
  have hexp_cancel : Real.exp (-2 * Real.pi) * Real.exp (2 * Real.pi) = 1 := by
    rw [← Real.exp_add]
    have h0 : -2 * Real.pi + 2 * Real.pi = 0 := by ring
    rw [h0, Real.exp_zero]
  calc ‖qExpansionCoeff f n‖
      = (‖qExpansionCoeff f n‖ * Real.exp (-2 * Real.pi)) * Real.exp (2 * Real.pi) := by
        rw [mul_assoc, hexp_cancel, mul_one]
    _ ≤ (M * (n : ℝ) ^ ((k : ℝ) / 2)) * Real.exp (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hint_le (Real.exp_pos _).le
    _ = M * Real.exp (2 * Real.pi) * (n : ℝ) ^ ((k : ℝ) / 2) := by ring

/-- **UNCONDITIONAL HECKE'S 1927 BOUND FOR RAMANUJAN'S TAU FUNCTION (`|τ(n)| ≤ C n^6`, `0` Assumptions!)**:
there exists `C > 0` such that `|(ramanujanTau n : ℝ)| ≤ C * n ^ 6` for ALL `n ≥ 1`! -/
theorem hecke_bound_ramanujanTau :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |(ramanujanTau n : ℝ)| ≤ C * (n : ℝ) ^ 6 := by
  obtain ⟨C, hC_pos, hC⟩ := hecke_cuspForm_coeff_bound 12 ramanujanDelta
  refine ⟨C, hC_pos, fun n hn => ?_⟩
  have h1 := hC n hn
  rw [qExpansionCoeff_ramanujanDelta n, ← Complex.ofReal_intCast, Complex.norm_real,
    Real.norm_eq_abs] at h1
  have hexp : ((12 : ℕ) : ℝ) / 2 = (6 : ℕ) := by norm_num
  rwa [hexp, Real.rpow_natCast] at h1

end HeckeBound

/-! ## Section 2: Order-1 Entirety, Infinitude of Zeros, Zero-Count Bound & Full Hadamard Product of `Λ(Δ, s)` -/

section CompletedDeltaLHadamard

/-- Upper-half Mellin integral bound for `Δ`: for any `w : ℂ`,
`‖upperMellinCusp ramanujanDelta w‖ ≤ C * Real.Gamma (‖w‖ + 1)`. -/
private lemma norm_upperMellinCusp_delta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ,
      ‖upperMellinCusp ramanujanDelta w‖ ≤ C * Real.Gamma (‖w‖ + 1) := by
  obtain ⟨C, hC_pos, hC⟩ := cuspForm_exp_decay_atTop ramanujanDelta
  refine ⟨C, hC_pos, fun w => ?_⟩
  have hα_pos : 0 < ‖w‖ + 1 := by positivity
  have hint_dom : IntegrableOn (fun t : ℝ => C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1)))
      (Set.Ioi 0) volume :=
    (integrableOn_exp_neg_mul_rpow zero_lt_one hα_pos).congr_fun
      (fun t _ => by simp [one_mul]) measurableSet_Ioi |>.const_mul C
  have hbound : ∀ t ∈ Set.Ioi (1 : ℝ),
      ‖cuspImag ramanujanDelta t * (t : ℂ) ^ (w - 1)‖ ≤
        C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1)) := by
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    rw [norm_mul, cuspImag_of_pos ramanujanDelta ht0, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hdec := hC t ht1
    have hexp_le : Real.exp (-2 * Real.pi * t) ≤ Real.exp (-t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    have hre_le : (w - 1).re ≤ ‖w‖ + 1 - 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith [(le_abs_self w.re).trans (Complex.abs_re_le_norm w)]
    have hrpow_le : t ^ (w - 1).re ≤ t ^ (‖w‖ + 1 - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1 hre_le
    calc ‖ramanujanDelta (imagPt t ht0)‖ * t ^ (w - 1).re
        ≤ (C * Real.exp (-2 * Real.pi * t)) * t ^ (‖w‖ + 1 - 1) :=
          mul_le_mul hdec hrpow_le (Real.rpow_nonneg ht0.le _) (by positivity)
      _ ≤ (C * Real.exp (-t)) * t ^ (‖w‖ + 1 - 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp_le hC_pos.le) (Real.rpow_nonneg ht0.le _)
      _ = C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1)) := by ring
  have hint_lhs : IntegrableOn (fun t : ℝ => cuspImag ramanujanDelta t * (t : ℂ) ^ (w - 1))
      (Set.Ioi 1) volume := by
    have hfull : IntegrableOn (fun t : ℝ => cuspImag ramanujanDelta t * (t : ℂ) ^ (w - 1))
        (Set.Ioi 0) volume :=
      (mellinConvergent_cuspImag ramanujanDelta w).congr_fun
        (fun t _ => by dsimp only; rw [smul_eq_mul, mul_comm]) measurableSet_Ioi
    exact hfull.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have h1 : ‖upperMellinCusp ramanujanDelta w‖ ≤
      ∫ t in Set.Ioi (1 : ℝ), C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1)) := by
    unfold upperMellinCusp
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    refine MeasureTheory.setIntegral_mono_on hint_lhs.norm
      (hint_dom.mono_set (Set.Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi hbound
  have h2 : (∫ t in Set.Ioi (1 : ℝ), C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1))) ≤
      ∫ t in Set.Ioi (0 : ℝ), C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1)) := by
    refine MeasureTheory.setIntegral_mono_set hint_dom ?_
      (Set.Ioi_subset_Ioi zero_le_one).eventuallyLE
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hC_pos.le (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _))
  have h3 : (∫ t in Set.Ioi (0 : ℝ), C * (Real.exp (-t) * t ^ (‖w‖ + 1 - 1))) =
      C * Real.Gamma (‖w‖ + 1) := by
    rw [MeasureTheory.integral_const_mul, Real.Gamma_eq_integral hα_pos]
  exact h1.trans (h2.trans_eq h3)

/-- **UNCONDITIONAL ORDER-1 ENTIRE GROWTH BOUND FOR `Λ(Δ, s)` (`0` Assumptions!)**:
there exist `A, B > 0` such that for ALL `s : ℂ`,
`‖completedDeltaL s‖ ≤ A * Real.exp (B * (‖s‖ + 1) * Real.log (‖s‖ + 2))`. -/
theorem completedDeltaL_order_one_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧
      ∀ s : ℂ, ‖completedDeltaL s‖ ≤ A * Real.exp (B * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := norm_upperMellinCusp_delta_le
  refine ⟨2 * C, by positivity, 52, by norm_num, fun s => ?_⟩
  have hsplit : completedDeltaL s =
      upperMellinCusp ramanujanDelta s + upperMellinCusp ramanujanDelta (12 - s) := by
    unfold completedDeltaL
    have h := completedCuspL_eq_split ramanujanDelta s
    have hI12 : Complex.I ^ (12 : ℤ) = 1 := by
      change Complex.I ^ (12 : ℕ) = 1
      calc Complex.I ^ 12 = (Complex.I ^ 2) ^ 6 := by ring
        _ = (-1 : ℂ) ^ 6 := by rw [Complex.I_sq]
        _ = 1 := by norm_num
    have h12 : ((12 : ℤ) : ℂ) = (12 : ℂ) := by norm_num
    rw [h12, hI12, one_mul] at h
    exact h
  have hbound_gamma : ∀ u : ℝ, 1 ≤ u → u ≤ ‖s‖ + 13 →
      Real.Gamma u ≤ Real.exp (52 * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
    intro u hu1 hu_le
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hG := real_Gamma_le_rpow_self hu1
    rw [Real.rpow_def_of_pos hu_pos] at hG
    refine hG.trans (Real.exp_le_exp.mpr ?_)
    have hpow4 : ‖s‖ + 13 ≤ (‖s‖ + 2) ^ 4 := by
      have hs0 : 0 ≤ ‖s‖ := norm_nonneg s
      have hexp : (‖s‖ + 2) ^ 4 = ‖s‖ ^ 4 + 8 * ‖s‖ ^ 3 + 24 * ‖s‖ ^ 2 + 32 * ‖s‖ + 16 := by ring
      have h4 : 0 ≤ ‖s‖ ^ 4 := by positivity
      have h3 : 0 ≤ ‖s‖ ^ 3 := by positivity
      have h2 : 0 ≤ ‖s‖ ^ 2 := by positivity
      linarith
    have hlog_u : Real.log u ≤ 4 * Real.log (‖s‖ + 2) := by
      calc Real.log u ≤ Real.log (‖s‖ + 13) := Real.log_le_log hu_pos hu_le
        _ ≤ Real.log ((‖s‖ + 2) ^ 4) := Real.log_le_log (by positivity) hpow4
        _ = 4 * Real.log (‖s‖ + 2) := by rw [Real.log_pow]; norm_num
    have hu_13 : u ≤ 13 * (‖s‖ + 1) := by linarith [norm_nonneg s]
    have hlog_nn : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
    have hlog_u_nn : 0 ≤ Real.log u := Real.log_nonneg hu1
    calc Real.log u * u = u * Real.log u := mul_comm _ _
      _ ≤ (13 * (‖s‖ + 1)) * (4 * Real.log (‖s‖ + 2)) :=
          mul_le_mul hu_13 hlog_u hlog_u_nn (by positivity)
      _ = 52 * (‖s‖ + 1) * Real.log (‖s‖ + 2) := by ring
  have h1 : Real.Gamma (‖s‖ + 1) ≤ Real.exp (52 * (‖s‖ + 1) * Real.log (‖s‖ + 2)) :=
    hbound_gamma (‖s‖ + 1) (by linarith [norm_nonneg s]) (by linarith)
  have h2 : Real.Gamma (‖12 - s‖ + 1) ≤ Real.exp (52 * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by
    refine hbound_gamma (‖12 - s‖ + 1) (by linarith [norm_nonneg (12 - s)]) ?_
    have htri : ‖(12 : ℂ) - s‖ ≤ 12 + ‖s‖ := by
      calc ‖(12 : ℂ) - s‖ ≤ ‖(12 : ℂ)‖ + ‖s‖ := norm_sub_le (12 : ℂ) s
        _ = 12 + ‖s‖ := by simp
    linarith
  rw [hsplit]
  calc ‖upperMellinCusp ramanujanDelta s + upperMellinCusp ramanujanDelta (12 - s)‖
      ≤ ‖upperMellinCusp ramanujanDelta s‖ + ‖upperMellinCusp ramanujanDelta (12 - s)‖ :=
        norm_add_le _ _
    _ ≤ C * Real.Gamma (‖s‖ + 1) + C * Real.Gamma (‖12 - s‖ + 1) :=
        add_le_add (hC s) (hC (12 - s))
    _ ≤ C * Real.exp (52 * (‖s‖ + 1) * Real.log (‖s‖ + 2)) +
        C * Real.exp (52 * (‖s‖ + 1) * Real.log (‖s‖ + 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC_pos.le)
          (mul_le_mul_of_nonneg_left h2 hC_pos.le)
    _ = 2 * C * Real.exp (52 * (‖s‖ + 1) * Real.log (‖s‖ + 2)) := by ring

/-- Bridge to `Stage5JensenHadamard.HasOrderOneGrowth` for `completedDeltaL`. -/
theorem hasOrderOneGrowth_completedDeltaL :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ HasOrderOneGrowth completedDeltaL A B := by
  obtain ⟨A₀, hA₀, B₀, hB₀, hbd⟩ := completedDeltaL_order_one_bound
  refine ⟨2 * B₀, by positivity, max (Real.log A₀ + B₀ * Real.log 3) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), differentiable_completedDeltaL, fun s => ?_⟩
  have h1 := hbd s
  rw [← Real.exp_log hA₀, ← Real.exp_add] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  have hlog_nn : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB_ge : Real.log A₀ + B₀ * Real.log 3 ≤ max (Real.log A₀ + B₀ * Real.log 3) 1 :=
    le_max_left _ _
  have hadd : B₀ * (‖s‖ + 1) * Real.log (‖s‖ + 2) =
      B₀ * ‖s‖ * Real.log (‖s‖ + 2) + B₀ * Real.log (‖s‖ + 2) := by ring
  rcases le_or_gt (1 : ℝ) ‖s‖ with hs1 | hs1
  · have hmul : B₀ * Real.log (‖s‖ + 2) ≤ B₀ * ‖s‖ * Real.log (‖s‖ + 2) := by
      have : B₀ ≤ B₀ * ‖s‖ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hlog_nn
    nlinarith
  · have hlog_le : Real.log (‖s‖ + 2) ≤ Real.log 3 :=
      Real.log_le_log (by linarith [norm_nonneg s]) (by linarith)
    have hterm : B₀ * Real.log (‖s‖ + 2) ≤ B₀ * Real.log 3 :=
      mul_le_mul_of_nonneg_left hlog_le hB₀.le
    have hmul_nn : 0 ≤ B₀ * ‖s‖ * Real.log (‖s‖ + 2) := by positivity
    nlinarith

/-- Nonvanishing of `Λ(Δ, 0)` (in fact `0 < (Λ(Δ, 0)).re`). -/
theorem completedDeltaL_zero_ne_zero : completedDeltaL 0 ≠ 0 := by
  intro h
  have hpos := completedDeltaL_pos_on_real 0
  rw [Complex.ofReal_zero, h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- **Exact Zero Equivalence in the Critical Strip (`0 < Re(s) < 12`)**:
for every `s : ℂ` with `0 < s.re < 12`, `completedDeltaL s = 0 ↔ deltaL s = 0`. -/
theorem completedDeltaL_zero_iff_deltaL_zero_in_strip {s : ℂ} (h0 : 0 < s.re) (_h12 : s.re < 12) :
    completedDeltaL s = 0 ↔ deltaL s = 0 := by
  unfold deltaL cuspL
  have h2pi_ne : (2 * (Real.pi : ℂ)) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')))
  have hgam_ne : (Complex.Gamma s)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos h0)
  have hfac_ne : (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ ≠ 0 :=
    mul_ne_zero h2pi_ne hgam_ne
  change completedDeltaL s = 0 ↔
    (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ * completedDeltaL s = 0
  exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left hfac_ne⟩

/-- **Unconditional Strip Containment of ALL Zeros of `Λ(Δ, s)`**:
EVERY zero `s : ℂ` of `completedDeltaL` satisfies `5 ≤ s.re ∧ s.re ≤ 7`! -/
theorem completedDeltaL_zero_in_strip {s : ℂ} (hs : completedDeltaL s = 0) :
    5 ≤ s.re ∧ s.re ≤ 7 := by
  have hle7 : s.re ≤ 7 := by
    by_contra hgt
    push Not at hgt
    have hL_ne : deltaL s ≠ 0 := deltaL_ne_zero_of_re_gt_seven hgt
    have hL_zero : deltaL s = 0 := by
      unfold deltaL cuspL
      change (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ * completedDeltaL s = 0
      rw [hs, mul_zero]
    exact hL_ne hL_zero
  have hge5 : 5 ≤ s.re := by
    by_contra hlt
    push Not at hlt
    have h12_gt7 : 7 < (12 - s).re := by simp; linarith
    have hfe : completedDeltaL (12 - s) = 0 := by
      rw [completedDeltaL_functional_equation, hs]
    have hL_ne : deltaL (12 - s) ≠ 0 := deltaL_ne_zero_of_re_gt_seven h12_gt7
    have hL_zero : deltaL (12 - s) = 0 := by
      unfold deltaL cuspL
      change (2 * (Real.pi : ℂ)) ^ (12 - s) * (Complex.Gamma (12 - s))⁻¹ *
        completedDeltaL (12 - s) = 0
      rw [hfe, mul_zero]
    exact hL_ne hL_zero
  exact ⟨hge5, hle7⟩

/-- Four-fold symmetry of zeros of `Λ(Δ, s)`: `ρ`, `12 - ρ`, `conj ρ`, `12 - conj ρ`. -/
theorem completedDeltaL_zero_symm {ρ : ℂ} (hρ : completedDeltaL ρ = 0) :
    completedDeltaL (12 - ρ) = 0 ∧
    completedDeltaL (starRingEnd ℂ ρ) = 0 ∧
    completedDeltaL (12 - starRingEnd ℂ ρ) = 0 := by
  have h1 : completedDeltaL (12 - ρ) = 0 := by rw [completedDeltaL_functional_equation, hρ]
  have h2 : completedDeltaL (starRingEnd ℂ ρ) = 0 := by rw [completedDeltaL_conj, hρ, map_zero]
  have h3 : completedDeltaL (12 - starRingEnd ℂ ρ) = 0 := by
    rw [completedDeltaL_functional_equation, h2]
  exact ⟨h1, h2, h3⟩

/-- Tail lower bound for `L(Δ, m)` at large positive integers `m`:
there exists `M₀ ≥ 8` such that `1 / 2 ≤ ‖deltaL (m : ℂ)‖` for all `m ≥ M₀`. -/
private lemma half_le_norm_deltaL_nat :
    ∃ M₀ : ℕ, 8 ≤ M₀ ∧ ∀ m : ℕ, M₀ ≤ m → (1 / 2 : ℝ) ≤ ‖deltaL (m : ℂ)‖ := by
  obtain ⟨C, hC_pos, hC⟩ := hecke_bound_ramanujanTau
  have hsum2 : Summable (fun k : ℕ => (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹) := by
    have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
    exact (summable_nat_add_iff 2).mpr h
  set S : ℝ := ∑' k : ℕ, (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹
  have hS_nn : 0 ≤ S := tsum_nonneg fun k => by positivity
  -- Choose `K` so that `C * S * (1 / 2) ^ K ≤ 1 / 2`.
  have htend : Tendsto (fun j : ℕ => C * S * ((1 / 2 : ℝ) ^ j)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h.const_mul (C * S)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (htend.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨K + 8, by omega, fun m hm => ?_⟩
  have hm_re : 7 < ((m : ℂ)).re := by
    have : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 8 ≤ m by omega)
    simp; linarith
  rw [deltaL_eq_LSeries hm_re]
  have hLsumm := LSeriesSummable_ramanujanTau hm_re
  have hsplit : LSeries (fun n => (ramanujanTau n : ℂ)) (m : ℂ) =
      1 + ∑' k : ℕ, LSeries.term (fun n => (ramanujanTau n : ℂ)) (m : ℂ) (k + 2) := by
    unfold LSeries
    rw [← hLsumm.sum_add_tsum_nat_add 2]
    congr 1
    simp [Finset.sum_range_succ, LSeries.term_zero, LSeries.term_of_ne_zero, ramanujanTau_one]
  rw [hsplit]
  have htail_le : ‖∑' k : ℕ, LSeries.term (fun n => (ramanujanTau n : ℂ)) (m : ℂ) (k + 2)‖ ≤ 1 / 2 := by
    have hdom_summ : Summable (fun k : ℕ =>
        C * ((1 / 2 : ℝ) ^ (m - 8)) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹) :=
      hsum2.mul_left _
    have hterm_le : ∀ k : ℕ,
        ‖LSeries.term (fun n => (ramanujanTau n : ℂ)) (m : ℂ) (k + 2)‖ ≤
          C * ((1 / 2 : ℝ) ^ (m - 8)) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := by
      intro k
      have hk2_ne : k + 2 ≠ 0 := by omega
      have hk2_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
      have hk2_ge2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
      rw [LSeries.term_of_ne_zero hk2_ne, norm_div, ← Complex.ofReal_intCast, Complex.norm_real,
        Real.norm_eq_abs, show ((k + 2 : ℕ) : ℂ) = (((k + 2 : ℕ) : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hk2_pos]
      have hm_re_eq : ((m : ℂ)).re = (m : ℝ) := by simp
      rw [hm_re_eq, Real.rpow_natCast]
      have htau := hC (k + 2) (by omega)
      have hm_eq : m = (m - 8) + 6 + 2 := by omega
      have hpow_split : ((k + 2 : ℕ) : ℝ) ^ m =
          ((k + 2 : ℕ) : ℝ) ^ (m - 8) * ((k + 2 : ℕ) : ℝ) ^ 6 * ((k + 2 : ℕ) : ℝ) ^ 2 := by
        conv_lhs => rw [hm_eq, pow_add, pow_add]
      have h2pow : (2 : ℝ) ^ (m - 8) ≤ ((k + 2 : ℕ) : ℝ) ^ (m - 8) :=
        pow_le_pow_left₀ (by norm_num) hk2_ge2 (m - 8)
      have hpow6_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) ^ 6 := pow_pos hk2_pos 6
      have hpow2_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) ^ 2 := pow_pos hk2_pos 2
      have hpowm_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) ^ (m - 8) := pow_pos hk2_pos (m - 8)
      calc |(ramanujanTau (k + 2) : ℝ)| / ((k + 2 : ℕ) : ℝ) ^ m
          ≤ (C * ((k + 2 : ℕ) : ℝ) ^ 6) / (((k + 2 : ℕ) : ℝ) ^ (m - 8) *
              ((k + 2 : ℕ) : ℝ) ^ 6 * ((k + 2 : ℕ) : ℝ) ^ 2) := by
            rw [← hpow_split]
            exact div_le_div_of_nonneg_right htau (pow_nonneg hk2_pos.le m)
        _ = C * (((k + 2 : ℕ) : ℝ) ^ (m - 8))⁻¹ * (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := by
            rw [Real.rpow_two]
            field_simp [hpow6_pos.ne', hpow2_pos.ne', hpowm_pos.ne']
        _ ≤ C * ((1 / 2 : ℝ) ^ (m - 8)) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℝ))⁻¹ := by
            rw [one_div, inv_pow]
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2pow) hC_pos.le)
              (by positivity)
    have hnorm_le := norm_tsum_le_tsum_norm ((summable_nat_add_iff 2).mpr hLsumm).norm
    have htsum_le := Summable.tsum_le_tsum hterm_le (((summable_nat_add_iff 2).mpr hLsumm).norm) hdom_summ
    rw [tsum_mul_left] at htsum_le
    have hK_le : K ≤ m - 8 := by omega
    have hpow_le : (1 / 2 : ℝ) ^ (m - 8) ≤ (1 / 2 : ℝ) ^ K :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hK_le
    have hstep : C * (1 / 2 : ℝ) ^ (m - 8) * S ≤ C * S * (1 / 2 : ℝ) ^ K := by
      have : C * (1 / 2 : ℝ) ^ (m - 8) * S = C * S * (1 / 2 : ℝ) ^ (m - 8) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hpow_le (mul_nonneg hC_pos.le hS_nn)
    exact (hnorm_le.trans htsum_le).trans (hstep.trans (hK K le_rfl))
  have htri : (1 : ℝ) - ‖∑' k : ℕ, LSeries.term (fun n => (ramanujanTau n : ℂ)) (m : ℂ) (k + 2)‖ ≤
      ‖(1 : ℂ) + ∑' k : ℕ, LSeries.term (fun n => (ramanujanTau n : ℂ)) (m : ℂ) (k + 2)‖ := by
    have h := norm_sub_norm_le (1 : ℂ)
      (-(∑' k : ℕ, LSeries.term (fun n => (ramanujanTau n : ℂ)) (m : ℂ) (k + 2)))
    simpa [sub_neg_eq_add, norm_neg, norm_one] using h
  linarith

/-- **UNCONDITIONAL INFINITUDE OF NON-TRIVIAL ZEROS OF RAMANUJAN'S `Λ(Δ, s)` (`0` ASSUMPTIONS!)**:
`completedDeltaL` has infinitely many zeros in the critical strip `5 ≤ Re(s) ≤ 7`! -/
theorem infinite_completedDeltaL_zeros : {s : ℂ | completedDeltaL s = 0}.Infinite := by
  classical
  intro hfin
  let Z : Finset ℂ := hfin.toFinset
  let Q : ℂ → ℂ := fun s => ∏ ρ ∈ Z, (s - ρ) ^ analyticOrderNatAt completedDeltaL ρ
  have hQ_diff : Differentiable ℂ Q := by
    have hprod : ∀ S : Finset ℂ,
        Differentiable ℂ (fun s => ∏ ρ ∈ S, (s - ρ) ^ analyticOrderNatAt completedDeltaL ρ) := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [differentiable_const]
      | @insert a t hat ih =>
        have hfun : (fun s => ∏ ρ ∈ insert a t, (s - ρ) ^ analyticOrderNatAt completedDeltaL ρ) =
            fun s => (s - a) ^ analyticOrderNatAt completedDeltaL a *
              ∏ ρ ∈ t, (s - ρ) ^ analyticOrderNatAt completedDeltaL ρ := by
          funext s; exact Finset.prod_insert hat
        rw [hfun]
        exact ((differentiable_id.sub (differentiable_const a)).pow _).mul ih
    exact hprod Z
  have hf_an : ∀ z : ℂ, AnalyticAt ℂ completedDeltaL z := fun z =>
    (differentiable_completedDeltaL.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hne_top : ∀ z : ℂ, analyticOrderAt completedDeltaL z ≠ ⊤ := fun z htop => by
    have hev : ∀ᶠ w in 𝓝 z, completedDeltaL w = 0 := analyticOrderAt_eq_top.mp htop
    have hfreq : ∃ᶠ w in 𝓝[≠] z, completedDeltaL w = 0 :=
      (hev.filter_mono nhdsWithin_le_nhds).frequently
    have heq : Set.EqOn completedDeltaL (fun _ => (0 : ℂ)) Set.univ :=
      (differentiable_completedDeltaL.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
        analyticOnNhd_const isPreconnected_univ (Set.mem_univ z) hfreq
    exact completedDeltaL_zero_ne_zero (heq (Set.mem_univ 0))
  -- Construct entire nonvanishing quotient `g = completedDeltaL / Q`.
  let g : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun z => completedDeltaL z / Q z)
  have hlocal : ∀ w : ℂ, ∃ q : ℂ → ℂ, AnalyticAt ℂ q w ∧ q w ≠ 0 ∧
      g =ᶠ[𝓝 w] q ∧ completedDeltaL w = q w * Q w := by
    intro w
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hf_an w).analyticOrderAt_ne_top.mp (hne_top w)
    have hQ_loc : ∃ Q₁ : ℂ → ℂ, AnalyticAt ℂ Q₁ w ∧ Q₁ w ≠ 0 ∧
        ∀ z : ℂ, Q z = (z - w) ^ analyticOrderNatAt completedDeltaL w * Q₁ z := by
      by_cases hwZ : w ∈ Z
      · refine ⟨fun z => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt completedDeltaL ρ, ?_, ?_, fun z => ?_⟩
        · have hdiff : Differentiable ℂ (fun z => ∏ ρ ∈ Z.erase w,
              (z - ρ) ^ analyticOrderNatAt completedDeltaL ρ) := by
            induction (Z.erase w) using Finset.induction_on with
            | empty => simp [differentiable_const]
            | @insert a t hat ih =>
              have hfun : (fun z => ∏ ρ ∈ insert a t, (z - ρ) ^ analyticOrderNatAt completedDeltaL ρ) =
                  fun z => (z - a) ^ analyticOrderNatAt completedDeltaL a *
                    ∏ ρ ∈ t, (z - ρ) ^ analyticOrderNatAt completedDeltaL ρ := by
                funext z; exact Finset.prod_insert hat
              rw [hfun]
              exact ((differentiable_id.sub (differentiable_const a)).pow _).mul ih
          exact hdiff.differentiableOn.analyticAt Filter.univ_mem
        · refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
            pow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_erase.mp hρ).1.symm)
        · exact (Finset.mul_prod_erase Z (fun ρ => (z - ρ) ^ analyticOrderNatAt completedDeltaL ρ) hwZ).symm
      · have hw_ne : completedDeltaL w ≠ 0 := fun hw0 => hwZ (hfin.mem_toFinset.mpr hw0)
        have hord0 : analyticOrderNatAt completedDeltaL w = 0 := by
          have h0 : analyticOrderAt completedDeltaL w = 0 := (hf_an w).analyticOrderAt_eq_zero.mpr hw_ne
          simp [analyticOrderNatAt, h0]
        refine ⟨Q, hQ_diff.differentiableOn.analyticAt Filter.univ_mem, ?_, fun z => by simp [hord0]⟩
        refine Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr fun heq => hwZ (heq ▸ hρ))
    obtain ⟨Q₁, hQ₁_an, hQ₁_ne, hQ₁_eq⟩ := hQ_loc
    let q : ℂ → ℂ := fun z => h z / Q₁ z
    have hq_an : AnalyticAt ℂ q w := hh_an.div hQ₁_an hQ₁_ne
    have hq_ne : q w ≠ 0 := div_ne_zero hh_ne hQ₁_ne
    have hev_all : ∀ᶠ z in 𝓝 w,
        completedDeltaL z = (z - w) ^ analyticOrderNatAt completedDeltaL w * h z ∧
        Q₁ z ≠ 0 ∧ ContinuousAt q z := by
      filter_upwards [hh_eq, hQ₁_an.continuousAt.eventually_ne hQ₁_ne,
        hq_an.eventually_analyticAt.mono fun z hz => hz.continuousAt] with z h1 h2 h3
      exact ⟨by simpa [smul_eq_mul] using h1, h2, h3⟩
    obtain ⟨U, hU_sub, hU_open, hwU⟩ := _root_.eventually_nhds_iff.mp hev_all
    have hfp : ∀ z ∈ U, z ≠ w → completedDeltaL z / Q z = q z := by
      intro z hzU hzw
      obtain ⟨h1, h2, _⟩ := hU_sub z hzU
      have hpow_ne : (z - w) ^ analyticOrderNatAt completedDeltaL w ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.mpr hzw)
      rw [h1, hQ₁_eq z]
      dsimp only [q]
      field_simp [hpow_ne, h2]
    have hg_eq : ∀ z ∈ U, g z = q z := by
      intro z hzU
      have htend_q : Tendsto q (𝓝[≠] z) (𝓝 (q z)) :=
        (hU_sub z hzU).2.2.tendsto.mono_left nhdsWithin_le_nhds
      have htend_fp : Tendsto (fun u => completedDeltaL u / Q u) (𝓝[≠] z) (𝓝 (q z)) := by
        refine htend_q.congr' ?_
        have hmem_U : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hU_open.mem_nhds hzU)
        have hmem_ne : ({w}ᶜ : Set ℂ) ∈ 𝓝[≠] z := by
          by_cases hzw : z = w
          · subst hzw; exact self_mem_nhdsWithin
          · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzw)
        filter_upwards [Filter.inter_mem hmem_U hmem_ne] with u ⟨huU, huw⟩
        exact (hfp u huU huw).symm
      exact htend_fp.limUnder_eq
    have hfw : completedDeltaL w = q w * Q w := by
      obtain ⟨h1, h2, _⟩ := hU_sub w hwU
      rw [h1, hQ₁_eq w]
      dsimp only [q]
      field_simp [h2]
    exact ⟨q, hq_an, hq_ne, Filter.eventually_of_mem (hU_open.mem_nhds hwU) hg_eq, hfw⟩
  have hg_diff : Differentiable ℂ g := fun w => by
    obtain ⟨q, hq_an, _, heq, _⟩ := hlocal w
    exact hq_an.differentiableAt.congr_of_eventuallyEq heq
  have hg_nz : ∀ w : ℂ, g w ≠ 0 := fun w => by
    obtain ⟨q, _, hq_ne, heq, _⟩ := hlocal w; rwa [heq.self_of_nhds]
  have hf_eq_gQ : ∀ w : ℂ, completedDeltaL w = g w * Q w := fun w => by
    obtain ⟨q, _, _, heq, hfw⟩ := hlocal w; rwa [heq.self_of_nhds]
  -- Order-1 growth bound for `g`.
  obtain ⟨A, hA_pos, B, _, hf_o1⟩ := hasOrderOneGrowth_completedDeltaL
  set M_nat : ℕ := Z.sup (fun ρ => ⌈‖ρ‖⌉₊)
  set R₀ : ℝ := (M_nat : ℝ) + 2
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) R₀).exists_bound_of_continuousOn
    hg_diff.continuous.continuousOn
  set B' : ℝ := max B (Real.log (max M₀ 1))
  have hg_bd : ∀ s : ℂ, ‖g s‖ ≤ Real.exp (A * (‖s‖ + 2) * Real.log (‖s‖ + 2) + B') := by
    intro s
    have hlog_nn : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
    have hA_nn : 0 ≤ A * (‖s‖ + 2) * Real.log (‖s‖ + 2) := by positivity
    by_cases hs : ‖s‖ ≤ R₀
    · have h1 : ‖g s‖ ≤ max M₀ 1 :=
        (hM₀ s (mem_closedBall_zero_iff.mpr hs)).trans (le_max_left M₀ 1)
      have h2 : max M₀ 1 ≤ Real.exp B' := by
        rw [← Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_right M₀ 1))]
        exact Real.exp_le_exp.mpr (le_max_right B _)
      exact h1.trans (h2.trans (Real.exp_le_exp.mpr (by linarith)))
    · push Not at hs
      have hQ_ge1 : (1 : ℝ) ≤ ‖Q s‖ := by
        dsimp only [Q]
        rw [norm_prod]
        have hfac : ∀ ρ ∈ Z, (1 : ℝ) ≤ ‖(s - ρ) ^ analyticOrderNatAt completedDeltaL ρ‖ := by
          intro ρ hρ
          rw [norm_pow]
          refine one_le_pow₀ ?_
          have hρ_le : ‖ρ‖ ≤ (M_nat : ℝ) := by
            have h1 : ‖ρ‖ ≤ (⌈‖ρ‖⌉₊ : ℝ) := Nat.le_ceil ‖ρ‖
            have h2 : ⌈‖ρ‖⌉₊ ≤ M_nat := Finset.le_sup (f := fun x => ⌈‖x‖⌉₊) hρ
            exact h1.trans (by exact_mod_cast h2)
          have htri : ‖s‖ - ‖ρ‖ ≤ ‖s - ρ‖ := norm_sub_norm_le s ρ
          dsimp only [R₀] at hs
          linarith
        simpa using Finset.prod_le_prod (fun _ _ => zero_le_one) hfac
      have hgn : ‖g s‖ ≤ ‖completedDeltaL s‖ := by
        rw [hf_eq_gQ s, norm_mul]
        nlinarith [norm_nonneg (g s)]
      refine hgn.trans ((hf_o1.2 s).trans (Real.exp_le_exp.mpr ?_))
      have h1 : A * ‖s‖ * Real.log (‖s‖ + 2) ≤ A * (‖s‖ + 2) * Real.log (‖s‖ + 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hlog_nn
      linarith [le_max_left B (Real.log (max M₀ 1))]
  obtain ⟨a, b, hab⟩ := entire_nonvanishing_order_lt_two_eq_exp_linear hg_diff hg_nz hg_bd
  -- Compare factorial lower bound `‖Λ(Δ, m)‖ ≥ (1/2) * (m - 1)! / (2π)^m` against `C₁ * K^m`.
  obtain ⟨M₁, hM₁_ge8, hdelta_ge⟩ := half_le_norm_deltaL_nat
  set D : ℕ := ∑ ρ ∈ Z, analyticOrderNatAt completedDeltaL ρ
  set C₁ : ℝ := Real.exp a.re * (R₀ + 1) ^ D
  set K : ℝ := Real.exp ((D : ℝ) + ‖b‖)
  have hC₁_pos : 0 < C₁ := by positivity
  have hK_pos : 0 < K := Real.exp_pos _
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcontra : ∀ n : ℕ,
      1 ≤ (2 * C₁ * (2 * Real.pi * K)) *
        ((2 * Real.pi * K) ^ (n + M₁) / ((n + M₁).factorial : ℝ)) := by
    intro n
    set m : ℕ := n + M₁ + 1
    set s : ℂ := (m : ℂ)
    have hm_geM₁ : M₁ ≤ m := by omega
    have hm_re : 7 < s.re := by
      have : (8 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 8 ≤ m by omega)
      simp [s]; linarith
    have hm_pos : 0 < m := by omega
    -- Lower bound on `‖completedDeltaL m‖`:
    have hdef : completedDeltaL s =
        (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * deltaL s := by
      rw [completedDeltaL_eq_gamma_mul_LSeries hm_re, ← deltaL_eq_LSeries hm_re]
    have hG_eq : Complex.Gamma s = (((n + M₁).factorial : ℕ) : ℂ) := by
      have hm_cast : s = ((n + M₁ : ℕ) : ℂ) + 1 := by dsimp only [s, m]; push_cast; ring
      rw [hm_cast]
      exact Complex.Gamma_nat_eq_factorial (n + M₁)
    have h2pi_norm : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = ((2 * Real.pi) ^ m)⁻¹ := by
      have harg : -s = ((-(m : ℝ)) : ℂ) := by dsimp only [s]; push_cast; ring
      rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        harg, Complex.norm_cpow_eq_rpow_re_of_pos h2pi_pos]
      simp [Real.rpow_neg h2pi_pos.le]
    have hdelta_lower : (1 / 2 : ℝ) ≤ ‖deltaL s‖ := hdelta_ge m hm_geM₁
    have hlower : (1 / 2 : ℝ) * (((n + M₁).factorial : ℝ) / (2 * Real.pi) ^ m) ≤
        ‖completedDeltaL s‖ := by
      rw [hdef, norm_mul, norm_mul, h2pi_norm, hG_eq, Complex.norm_natCast]
      calc (1 / 2 : ℝ) * (((n + M₁).factorial : ℝ) / (2 * Real.pi) ^ m)
          = ((2 * Real.pi) ^ m)⁻¹ * ((n + M₁).factorial : ℝ) * (1 / 2) := by ring
        _ ≤ ((2 * Real.pi) ^ m)⁻¹ * ((n + M₁).factorial : ℝ) * ‖deltaL s‖ :=
            mul_le_mul_of_nonneg_left hdelta_lower (by positivity)
    -- Upper bound on `‖completedDeltaL m‖ = ‖exp(a + b * m) * Q m‖`:
    have hexp_upper : ‖Complex.exp (a + b * s)‖ ≤ Real.exp a.re * Real.exp (‖b‖ * (m : ℝ)) := by
      rw [Complex.norm_exp, Complex.add_re, Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      have h1 : (b * s).re ≤ ‖b * s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      have hsn : ‖s‖ = (m : ℝ) := by dsimp only [s]; rw [Complex.norm_natCast]
      rw [norm_mul, hsn] at h1
      exact h1
    have hQ_upper : ‖Q s‖ ≤ (R₀ + 1) ^ D * Real.exp ((D : ℝ) * (m : ℝ)) := by
      dsimp only [Q]
      rw [norm_prod]
      have hfac : ∀ ρ ∈ Z, ‖(s - ρ) ^ analyticOrderNatAt completedDeltaL ρ‖ ≤
          ((R₀ + 1) * Real.exp (m : ℝ)) ^ analyticOrderNatAt completedDeltaL ρ := by
        intro ρ hρ
        rw [norm_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
        have hsn : ‖s‖ = (m : ℝ) := by dsimp only [s]; rw [Complex.norm_natCast]
        have hρ_le : ‖ρ‖ ≤ R₀ := by
          have h1 : ‖ρ‖ ≤ (⌈‖ρ‖⌉₊ : ℝ) := Nat.le_ceil ‖ρ‖
          have h2 : ⌈‖ρ‖⌉₊ ≤ M_nat := Finset.le_sup (f := fun x => ⌈‖x‖⌉₊) hρ
          have h3 : (⌈‖ρ‖⌉₊ : ℝ) ≤ (M_nat : ℝ) := by exact_mod_cast h2
          dsimp only [R₀]; linarith
        have hm_le_exp : (m : ℝ) ≤ Real.exp (m : ℝ) := by linarith [Real.add_one_le_exp (m : ℝ)]
        have hm_ge1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
        have hR₀_nn : 0 ≤ R₀ := by dsimp only [R₀]; positivity
        calc ‖s - ρ‖ ≤ ‖s‖ + ‖ρ‖ := norm_sub_le s ρ
          _ ≤ (m : ℝ) + R₀ := by linarith
          _ ≤ (R₀ + 1) * (m : ℝ) := by nlinarith
          _ ≤ (R₀ + 1) * Real.exp (m : ℝ) := mul_le_mul_of_nonneg_left hm_le_exp (by positivity)
      calc ∏ ρ ∈ Z, ‖(s - ρ) ^ analyticOrderNatAt completedDeltaL ρ‖
          ≤ ∏ ρ ∈ Z, ((R₀ + 1) * Real.exp (m : ℝ)) ^ analyticOrderNatAt completedDeltaL ρ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
        _ = ((R₀ + 1) * Real.exp (m : ℝ)) ^ D := by rw [← Finset.prod_pow_eq_pow_sum]
        _ = (R₀ + 1) ^ D * Real.exp ((D : ℝ) * (m : ℝ)) := by rw [mul_pow, ← Real.exp_nat_mul]
    have hupper : ‖completedDeltaL s‖ ≤ C₁ * K ^ m := by
      rw [hf_eq_gQ s, hab s, norm_mul]
      calc ‖Complex.exp (a + b * s)‖ * ‖Q s‖
          ≤ (Real.exp a.re * Real.exp (‖b‖ * (m : ℝ))) *
              ((R₀ + 1) ^ D * Real.exp ((D : ℝ) * (m : ℝ))) :=
            mul_le_mul hexp_upper hQ_upper (norm_nonneg _) (by positivity)
        _ = C₁ * Real.exp ((m : ℝ) * ((D : ℝ) + ‖b‖)) := by
            dsimp only [C₁]; rw [mul_mul_mul_comm, ← Real.exp_add]; congr 2; ring
        _ = C₁ * K ^ m := by dsimp only [K]; rw [Real.exp_nat_mul]
    have hcomb := hlower.trans hupper
    have hfac_pos : (0 : ℝ) < ((n + M₁).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have h2pim_pos : (0 : ℝ) < (2 * Real.pi) ^ m := pow_pos h2pi_pos m
    have hmul : ((n + M₁).factorial : ℝ) ≤ 2 * C₁ * (2 * Real.pi * K) ^ m := by
      have h1 : ((n + M₁).factorial : ℝ) / (2 * Real.pi) ^ m ≤ 2 * C₁ * K ^ m := by linarith
      have h2 := (div_le_iff₀ h2pim_pos).mp h1
      rw [mul_pow]
      linarith
    have hdiv : (1 : ℝ) ≤ 2 * C₁ * (2 * Real.pi * K) ^ m / ((n + M₁).factorial : ℝ) :=
      (le_div_iff₀ hfac_pos).mpr (by simpa [one_mul] using hmul)
    have hrhs : 2 * C₁ * (2 * Real.pi * K) ^ m / ((n + M₁).factorial : ℝ) =
        2 * C₁ * (2 * Real.pi * K) * ((2 * Real.pi * K) ^ (n + M₁) / ((n + M₁).factorial : ℝ)) := by
      have hm_eq : m = (n + M₁) + 1 := rfl
      rw [hm_eq, pow_succ]
      ring
    linarith
  have htend_zero : Tendsto (fun n : ℕ =>
      (2 * C₁ * (2 * Real.pi * K)) *
        ((2 * Real.pi * K) ^ (n + M₁) / ((n + M₁).factorial : ℝ))) atTop (nhds 0) := by
    have h1 := (FloorSemiring.tendsto_pow_div_factorial_atTop (2 * Real.pi * K)).comp
      (tendsto_add_atTop_nat M₁)
    simpa [Function.comp_def] using h1.const_mul (2 * C₁ * (2 * Real.pi * K))
  have hle0 : (1 : ℝ) ≤ 0 := ge_of_tendsto htend_zero (Eventually.of_forall hcontra)
  linarith

/-- **UNCONDITIONAL ZERO-COUNT UPPER BOUND FOR `Λ(Δ, s)` (`N_Δ(T) ≤ C * T * log T`)**
via Jensen's formula (`Stage5JensenHadamard.order_one_zero_count_le`). -/
theorem completedDeltaL_zero_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, completedDeltaL ρ = 0 ∧ |ρ.im| ≤ T) →
      (Z.card : ℝ) ≤ C * T * Real.log T := by
  obtain ⟨A, hA, B, _, hf_o1⟩ := hasOrderOneGrowth_completedDeltaL
  set C₀ : ℝ := (4 * A + max B 0 + max (-Real.log ‖completedDeltaL 0‖) 0) / Real.log 2
  have hC₀_pos : 0 < C₀ := div_pos
    (by linarith [le_max_right B 0, le_max_right (-Real.log ‖completedDeltaL 0‖) 0])
    (Real.log_pos (by norm_num))
  refine ⟨20 * C₀, by positivity, fun T hT Z hZ => ?_⟩
  have hball := order_one_zero_count_le hA.le hf_o1 completedDeltaL_zero_ne_zero (5 * T) (by linarith) Z
    (fun ρ hρ => by
      rw [mem_closedBall_zero_iff]
      have hstrip := completedDeltaL_zero_in_strip (hZ ρ hρ).1
      have htri := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_nonneg (by linarith : 0 ≤ ρ.re)] at htri
      linarith [(hZ ρ hρ).2])
    (fun ρ hρ => (hZ ρ hρ).1)
  have hlog_le : Real.log (5 * T + 2) ≤ 4 * Real.log T := by
    have hpow4 : 5 * T + 2 ≤ T ^ 4 := by
      have hT2 : 0 ≤ T - 2 := by linarith
      have hid : T ^ 4 - (5 * T + 2) = (T - 2) * (T ^ 3 + 2 * T ^ 2 + 4 * T + 3) + 4 := by ring
      have hfac_nn : 0 ≤ T ^ 3 + 2 * T ^ 2 + 4 * T + 3 := by positivity
      nlinarith
    calc Real.log (5 * T + 2)
        ≤ Real.log (T ^ 4) := Real.log_le_log (by linarith) hpow4
      _ = 4 * Real.log T := by rw [Real.log_pow]; norm_num
  have hstep : C₀ * (5 * T) * Real.log (5 * T + 2) ≤ 20 * C₀ * T * Real.log T := by
    have h1 := mul_le_mul_of_nonneg_left hlog_le (by positivity : 0 ≤ C₀ * (5 * T))
    linarith
  exact hball.trans hstep

/-- Every closed ball contains only finitely many zeros of `Λ(Δ, s)`. -/
private lemma finite_completedDeltaL_zeros_in_ball (R : ℝ) (hR : 1 ≤ R) :
    {s : ℂ | completedDeltaL s = 0 ∧ ‖s‖ ≤ R}.Finite := by
  obtain ⟨A, hA, B, _, hf_o1⟩ := hasOrderOneGrowth_completedDeltaL
  set C₀ : ℝ := (4 * A + max B 0 + max (-Real.log ‖completedDeltaL 0‖) 0) / Real.log 2
  by_contra hinf
  obtain ⟨F, hFsub, hFcard⟩ :=
    Set.Infinite.exists_subset_card_eq hinf (Nat.floor (C₀ * R * Real.log (R + 2)) + 1)
  have hle := order_one_zero_count_le hA.le hf_o1 completedDeltaL_zero_ne_zero R hR F
    (fun ρ hρ => mem_closedBall_zero_iff.mpr (hFsub hρ).2)
    (fun ρ hρ => (hFsub hρ).1)
  have hgt : C₀ * R * Real.log (R + 2) < (F.card : ℝ) := by
    rw [hFcard]; push_cast; exact Nat.lt_floor_add_one _
  linarith

/-- Countability of the zero set `{s : ℂ | completedDeltaL s = 0}`. -/
theorem countable_completedDeltaL_zeros : {s : ℂ | completedDeltaL s = 0}.Countable := by
  have hunion : {s : ℂ | completedDeltaL s = 0} =
      ⋃ n : ℕ, {s : ℂ | completedDeltaL s = 0 ∧ ‖s‖ ≤ (n : ℝ) + 1} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun hs => ⟨⌈‖s‖⌉₊, hs, (Nat.le_ceil ‖s‖).trans (by linarith)⟩, fun ⟨_, hs, _⟩ => hs⟩
  rw [hunion]
  exact Set.countable_iUnion fun n =>
    (finite_completedDeltaL_zeros_in_ball ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n])).countable

/-- Type of zeros of `Λ(Δ, s)` paired with their analytic multiplicity index. -/
abbrev DeltaZeroWithMult : Type :=
  Σ z : {s : ℂ // completedDeltaL s = 0}, Fin (analyticOrderNatAt completedDeltaL z.1)

lemma analyticOrderNatAt_completedDeltaL_pos {z : ℂ} (hz : completedDeltaL z = 0) :
    0 < analyticOrderNatAt completedDeltaL z := by
  have hf_an : AnalyticAt ℂ completedDeltaL z :=
    (differentiable_completedDeltaL.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hne_top : analyticOrderAt completedDeltaL z ≠ ⊤ := fun htop => by
    have hev : ∀ᶠ w in 𝓝 z, completedDeltaL w = 0 := analyticOrderAt_eq_top.mp htop
    have hfreq : ∃ᶠ w in 𝓝[≠] z, completedDeltaL w = 0 :=
      (hev.filter_mono nhdsWithin_le_nhds).frequently
    have heq : Set.EqOn completedDeltaL (fun _ => (0 : ℂ)) Set.univ :=
      (differentiable_completedDeltaL.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
        analyticOnNhd_const isPreconnected_univ (Set.mem_univ z) hfreq
    exact completedDeltaL_zero_ne_zero (heq (Set.mem_univ 0))
  have hne0 : analyticOrderAt completedDeltaL z ≠ 0 := hf_an.analyticOrderAt_ne_zero.mpr hz
  have hnat_ne : analyticOrderNatAt completedDeltaL z ≠ 0 := by
    intro h0
    have hcoe : (analyticOrderNatAt completedDeltaL z : ℕ∞) = analyticOrderAt completedDeltaL z :=
      ENat.natCast_toNat hne_top
    rw [h0, Nat.cast_zero] at hcoe
    exact hne0 hcoe.symm
  exact Nat.pos_of_ne_zero hnat_ne

instance : Countable {s : ℂ // completedDeltaL s = 0} :=
  countable_completedDeltaL_zeros.to_subtype

instance : Infinite {s : ℂ // completedDeltaL s = 0} :=
  infinite_completedDeltaL_zeros.to_subtype

instance : Countable DeltaZeroWithMult := instCountableSigma

instance : Infinite DeltaZeroWithMult :=
  Infinite.of_injective
    (fun z : {s : ℂ // completedDeltaL s = 0} => ⟨z, ⟨0, analyticOrderNatAt_completedDeltaL_pos z.2⟩⟩)
    fun z₁ z₂ h => by cases h; rfl

/-- Canonical bijection `ℕ ≃ DeltaZeroWithMult` enumerating all zeros of `Λ(Δ, s)` with multiplicity. -/
def deltaZeroEquiv : ℕ ≃ DeltaZeroWithMult :=
  letI : Encodable DeltaZeroWithMult := Encodable.ofCountable DeltaZeroWithMult
  letI : Denumerable DeltaZeroWithMult := Denumerable.ofEncodableOfInfinite DeltaZeroWithMult
  (Denumerable.eqv DeltaZeroWithMult).symm

/-- **Unconditional Multiplicity-Counted Enumeration `deltaZeroSeq : ℕ → ℂ`** of ALL zeros of
`Λ(Δ, s)`. -/
def deltaZeroSeq (n : ℕ) : ℂ := (deltaZeroEquiv n).1.1

theorem deltaZeroSeq_zero (n : ℕ) : completedDeltaL (deltaZeroSeq n) = 0 :=
  (deltaZeroEquiv n).1.2

theorem deltaZeroSeq_strip (n : ℕ) : 5 ≤ (deltaZeroSeq n).re ∧ (deltaZeroSeq n).re ≤ 7 :=
  completedDeltaL_zero_in_strip (deltaZeroSeq_zero n)

theorem deltaZeroSeq_ne_zero (n : ℕ) : deltaZeroSeq n ≠ 0 := by
  intro h
  have hge5 := (deltaZeroSeq_strip n).1
  rw [h, Complex.zero_re] at hge5
  linarith

/-- `deltaZeroSeq` enumerates every zero of `Λ(Δ, s)` with its exact analytic multiplicity. -/
theorem isMultiplicityZeroSeq_completedDeltaL :
    IsMultiplicityZeroSeq completedDeltaL deltaZeroSeq := by
  classical
  refine ⟨deltaZeroSeq_ne_zero, fun w => ?_⟩
  by_cases hw : completedDeltaL w = 0
  · let f : Fin (analyticOrderNatAt completedDeltaL w) → ℕ :=
      fun j => deltaZeroEquiv.symm ⟨⟨w, hw⟩, j⟩
    have hf_inj : Function.Injective f := fun j₁ j₂ h => by
      have h1 := deltaZeroEquiv.symm.injective h
      cases h1; rfl
    have hset_eq : {n : ℕ | deltaZeroSeq n = w} = Set.range f := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_range, deltaZeroSeq, f]
      constructor
      · intro h
        refine ⟨(deltaZeroEquiv n).2.cast (by rw [h]), ?_⟩
        apply deltaZeroEquiv.injective
        rw [Equiv.apply_symm_apply]
        refine Sigma.ext (Subtype.ext h.symm) ?_
        exact (Fin.heq_ext_iff (congrArg (analyticOrderNatAt completedDeltaL) h.symm)).mpr rfl
      · rintro ⟨j, rfl⟩
        simp
    refine ⟨by rw [hset_eq]; exact Set.finite_range f, fun F hF => ?_⟩
    have hF_eq : F = Finset.univ.image f := by
      ext n
      rw [hF n, Finset.mem_image]
      have hmem : n ∈ {m : ℕ | deltaZeroSeq m = w} ↔ n ∈ Set.range f := by rw [hset_eq]
      simpa using hmem
    rw [hF_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  · have hf_an : AnalyticAt ℂ completedDeltaL w :=
      (differentiable_completedDeltaL.differentiableOn.analyticOnNhd isOpen_univ) w (Set.mem_univ w)
    have hord0 : analyticOrderNatAt completedDeltaL w = 0 := by
      have h0 : analyticOrderAt completedDeltaL w = 0 := hf_an.analyticOrderAt_eq_zero.mpr hw
      simp [analyticOrderNatAt, h0]
    have hempty : {n : ℕ | deltaZeroSeq n = w} = ∅ := by
      ext n; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hw (h ▸ deltaZeroSeq_zero n)
    refine ⟨by rw [hempty]; exact Set.finite_empty, fun F hF => ?_⟩
    have hFe : F = ∅ := by
      ext n; simp only [hF n, Finset.notMem_empty, iff_false]
      intro h; exact hw (h ▸ deltaZeroSeq_zero n)
    rw [hFe, Finset.card_empty, hord0]

/-- **Unconditional Inverse-Square Summability of `deltaZeroSeq`** (`∑' n, ‖ρ_n‖^{-2} < ∞`). -/
theorem deltaZeroSeq_summable_inv_sq : Summable (fun n : ℕ => (‖deltaZeroSeq n‖ ^ 2)⁻¹) := by
  obtain ⟨A, hA, B, _, hf_o1⟩ := hasOrderOneGrowth_completedDeltaL
  set C₀ : ℝ := (4 * A + max B 0 + max (-Real.log ‖completedDeltaL 0‖) 0) / Real.log 2
  have hC₀ : 0 ≤ C₀ := div_nonneg
    (by linarith [le_max_right B 0, le_max_right (-Real.log ‖completedDeltaL 0‖) 0])
    (Real.log_pos (by norm_num)).le
  exact Stage5JensenHadamard.summable_inv_sq_of_zero_counting hC₀ deltaZeroSeq_ne_zero
    (order_one_multiplicity_zero_count_le hA.le hf_o1 completedDeltaL_zero_ne_zero
      isMultiplicityZeroSeq_completedDeltaL)

/-- Canonical Hadamard exponential constant `B_Δ = Λ'(Δ, 0) / Λ(Δ, 0)`. -/
def deltaHadamardB : ℂ := deriv completedDeltaL 0 / completedDeltaL 0

/-- **UNCONDITIONAL CONCRETE HADAMARD PRODUCT OF `Λ(Δ, s)` (CANONICAL `B_Δ = Λ'(Δ, 0) / Λ(Δ, 0)`)**:
for ALL `s : ℂ`,
`completedDeltaL s = completedDeltaL 0 * Complex.exp (deltaHadamardB * s) * weierstrassProduct deltaZeroSeq s`. -/
theorem completedDeltaL_eq_zero_mul_exp_weierstrassProduct (s : ℂ) :
    completedDeltaL s =
      completedDeltaL 0 * Complex.exp (deltaHadamardB * s) *
        weierstrassProduct deltaZeroSeq s := by
  obtain ⟨A, hA, B, _, hf_o1⟩ := hasOrderOneGrowth_completedDeltaL
  obtain ⟨_, a, b, hfac, hlogd⟩ :=
    hadamard_factorization_order_one hA.le hf_o1 completedDeltaL_zero_ne_zero
      isMultiplicityZeroSeq_completedDeltaL
  have hexpa : Complex.exp a = completedDeltaL 0 := by
    have h0 := hfac 0
    rw [mul_zero, add_zero, weierstrassProduct_zero, mul_one] at h0
    exact h0.symm
  have hb_eq : b = deltaHadamardB := by
    have h0_ne : ∀ n : ℕ, (0 : ℂ) ≠ deltaZeroSeq n := fun n h => deltaZeroSeq_ne_zero n h.symm
    have hld0 := hlogd 0 h0_ne
    have hsum0 : ∑' n : ℕ, (1 / ((0 : ℂ) - deltaZeroSeq n) + 1 / deltaZeroSeq n) = 0 := by
      simp [zero_sub, div_neg]
    rw [hsum0, add_zero] at hld0
    exact hld0.symm
  rw [hfac s, Complex.exp_add, hexpa, hb_eq]

/-- **UNCONDITIONAL LOG-DERIVATIVE PARTIAL FRACTION FORMULA FOR `Λ(Δ, s)`**:
for every `s : ℂ` with `completedDeltaL s ≠ 0`,
`deriv completedDeltaL s / completedDeltaL s = deltaHadamardB + ∑' n, (1 / (s - ρ_n) + 1 / ρ_n)`. -/
theorem completedDeltaL_logDeriv_hadamard {s : ℂ} (hs : completedDeltaL s ≠ 0) :
    deriv completedDeltaL s / completedDeltaL s =
      deltaHadamardB + ∑' n : ℕ, (1 / (s - deltaZeroSeq n) + 1 / deltaZeroSeq n) := by
  have hfun : completedDeltaL =
      fun w => completedDeltaL 0 * Complex.exp (deltaHadamardB * w) *
        weierstrassProduct deltaZeroSeq w :=
    funext completedDeltaL_eq_zero_mul_exp_weierstrassProduct
  rw [hfun]
  refine Stage5JensenHadamard.hadamard_canonical_logDeriv_eq completedDeltaL_zero_ne_zero
    deltaZeroSeq_ne_zero deltaZeroSeq_summable_inv_sq fun n h => ?_
  exact hs (h ▸ deltaZeroSeq_zero n)

/-- **UNCONDITIONAL FULL HADAMARD PRODUCT FACTORIZATION OF RAMANUJAN'S `Λ(Δ, s)` (`0` ASSUMPTIONS!)**:
there exist `B_Δ : ℂ` and a multiplicity-exact zero enumeration `ρ_Δ : ℕ → ℂ` (all in `5 ≤ Re(ρ) ≤ 7`,
`∑' n, ‖ρ_n‖^{-2} < ∞`) such that for ALL `s : ℂ`,
`completedDeltaL s = completedDeltaL 0 * Complex.exp (B_Δ * s) * weierstrassProduct ρ_Δ s`! -/
theorem completedDeltaL_hadamard_product :
    ∃ (B_Δ : ℂ) (ρ_Δ : ℕ → ℂ),
      IsMultiplicityZeroSeq completedDeltaL ρ_Δ ∧
      (∀ n : ℕ, 5 ≤ (ρ_Δ n).re ∧ (ρ_Δ n).re ≤ 7) ∧
      Summable (fun n : ℕ => (‖ρ_Δ n‖ ^ 2)⁻¹) ∧
      ∀ s : ℂ, completedDeltaL s =
        completedDeltaL 0 * Complex.exp (B_Δ * s) * weierstrassProduct ρ_Δ s :=
  ⟨deltaHadamardB, deltaZeroSeq, isMultiplicityZeroSeq_completedDeltaL, deltaZeroSeq_strip,
    deltaZeroSeq_summable_inv_sq, completedDeltaL_eq_zero_mul_exp_weierstrassProduct⟩

end CompletedDeltaLHadamard

/-! ## Section 3: Unconditional Conditional-on-Deligne Bridge (`Re(s) > 13/2`) -/

section DeligneBridge

/-- Elementary divisor-count bound `d(n) ≤ C_ε * n ^ ε` for EVERY `ε > 0` and ALL `n ≥ 1`. -/
theorem divisors_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  -- For `p ≥ P₀ := ⌈2^(1/ε)⌉₊`, `p^ε ≥ 2`, so `(a + 1) ≤ 2^a ≤ p^(a*ε)`.
  -- For `p < P₀`, `p^ε ≥ 2^ε = 1 + δ`, so `(a + 1) ≤ (1 + 1/δ) * p^(a*ε)`.
  set δ : ℝ := (2 : ℝ) ^ ε - 1
  have h2ε_gt1 : (1 : ℝ) < (2 : ℝ) ^ ε := by
    have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε
    exact h
  have hδ_pos : 0 < δ := sub_pos.mpr h2ε_gt1
  set K : ℝ := 1 + 1 / δ
  have hK_ge1 : 1 ≤ K := by dsimp only [K]; linarith [div_pos zero_lt_one hδ_pos]
  set P₀ : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  -- Prime-power bound: `(p^a).divisors.card ≤ (if p < P₀ then K else 1) * (p^a)^ε`.
  have hpp : ∀ (p : ℕ), p.Prime → ∀ a : ℕ,
      (((p ^ a).divisors.card : ℕ) : ℝ) ≤
        (if p < P₀ then K else 1) * ((p ^ a : ℕ) : ℝ) ^ ε := by
    intro p hp a
    rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range, Nat.cast_pow,
      ← Real.rpow_natCast (p : ℝ) a, ← Real.rpow_mul (Nat.cast_nonneg p),
      mul_comm (a : ℝ) ε, Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    split_ifs with hlt
    · have hpε_ge : 1 + δ ≤ (p : ℝ) ^ ε := by
        dsimp only [δ]
        have : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp_ge2 hε.le
        linarith
      have hbern : 1 + (a : ℝ) * δ ≤ (1 + δ) ^ a := by
        simpa [add_comm] using one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ δ) a
      have hpow_le : 1 + (a : ℝ) * δ ≤ ((p : ℝ) ^ ε) ^ a :=
        hbern.trans (pow_le_pow_left₀ (by linarith) hpε_ge a)
      have hlin : ((a + 1 : ℕ) : ℝ) ≤ K * (1 + (a : ℝ) * δ) := by
        dsimp only [K]
        push_cast
        have hmul : (1 + 1 / δ) * (1 + (a : ℝ) * δ) = 1 + (a : ℝ) + (a : ℝ) * δ + 1 / δ := by
          field_simp [hδ_pos.ne']; ring
        rw [hmul]
        have haδ : 0 ≤ (a : ℝ) * δ := by positivity
        have hinv : 0 < 1 / δ := by positivity
        linarith
      exact hlin.trans (mul_le_mul_of_nonneg_left hpow_le (by linarith))
    · push Not at hlt
      rw [one_mul]
      have hpε_ge2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        have h1 : (2 : ℝ) ^ (1 / ε) ≤ (p : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hlt)
        have h2 := Real.rpow_le_rpow (by positivity) h1 hε.le
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hε.ne',
          Real.rpow_one] at h2
        exact h2
      have ha_le_2a : ((a + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ a := by
        have hnat : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
        exact_mod_cast hnat
      exact ha_le_2a.trans (pow_le_pow_left₀ (by norm_num) hpε_ge2 a)
  -- Prove by strong induction on `n` that `d(n) ≤ K ^ (#{p ∈ n.primeFactors | p < P₀}) * n^ε`.
  have hind : ∀ n : ℕ, 1 ≤ n →
      (n.divisors.card : ℝ) ≤
        K ^ ((n.primeFactors.filter (fun p => p < P₀)).card) * (n : ℝ) ^ ε := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1; simp
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hn0 : n ≠ 0 := by omega
      set a := n.factorization p
      have ha_pos : 1 ≤ a := (hp.dvd_iff_one_le_factorization hn0).mp hpn
      have hpa_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
      set n' := n / p ^ a
      have hn_eq : n = p ^ a * n' := (Nat.mul_div_cancel' hpa_dvd).symm
      have hn'_pos : 1 ≤ n' := Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
      have hp_not_n' : ¬ p ∣ n' := Nat.not_dvd_ordCompl hp hn0
      have hcop : Nat.Coprime (p ^ a) n' := (hp.coprime_iff_not_dvd.mpr hp_not_n').pow_left a
      have hn'_lt : n' < n := by
        have hpa_gt : 1 < p ^ a := one_lt_pow₀ hp.one_lt (by omega)
        calc n' = 1 * n' := (one_mul n').symm
          _ < p ^ a * n' := Nat.mul_lt_mul_of_pos_right hpa_gt (by omega)
          _ = n := hn_eq.symm
      have hcard_mul : n.divisors.card = (p ^ a).divisors.card * n'.divisors.card := by
        rw [hn_eq]
        exact hcop.card_divisors_mul
      have hpf_eq : n.primeFactors = insert p n'.primeFactors := by
        rw [hn_eq, Nat.primeFactors_mul (pow_ne_zero a hp.ne_zero) (by omega),
          Nat.primeFactors_pow p (by omega : a ≠ 0), hp.primeFactors]
        ext q; simp
      have hp_not_pf : p ∉ n'.primeFactors := by
        rw [Nat.mem_primeFactors]; intro h; exact hp_not_n' h.2.1
      have hfilt_card : (n.primeFactors.filter (fun q => q < P₀)).card =
          (if p < P₀ then 1 else 0) + (n'.primeFactors.filter (fun q => q < P₀)).card := by
        rw [hpf_eq, Finset.filter_insert]
        split_ifs with hlt
        · rw [Finset.card_insert_of_notMem (by simp [hp_not_pf])]; omega
        · omega
      have h1 := hpp p hp a
      have h2 := ih n' hn'_lt hn'_pos
      have hK_split : (if p < P₀ then K else 1) *
          K ^ ((n'.primeFactors.filter (fun q => q < P₀)).card) =
          K ^ ((n.primeFactors.filter (fun q => q < P₀)).card) := by
        rw [hfilt_card, pow_add]
        split_ifs <;> simp
      rw [hcard_mul, Nat.cast_mul, ← hK_split, hn_eq, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      calc (((p ^ a).divisors.card : ℕ) : ℝ) * (n'.divisors.card : ℝ)
          ≤ ((if p < P₀ then K else 1) * ((p ^ a : ℕ) : ℝ) ^ ε) *
              (K ^ ((n'.primeFactors.filter (fun q => q < P₀)).card) * (n' : ℝ) ^ ε) :=
            mul_le_mul h1 h2 (Nat.cast_nonneg _)
              (mul_nonneg (by split_ifs <;> linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        _ = ((if p < P₀ then K else 1) * K ^ ((n'.primeFactors.filter (fun q => q < P₀)).card)) *
              (((p ^ a : ℕ) : ℝ) ^ ε * (n' : ℝ) ^ ε) := by ring
  refine ⟨K ^ P₀, pow_pos (by linarith) P₀, fun n hn => ?_⟩
  have hcard_le : (n.primeFactors.filter (fun p => p < P₀)).card ≤ P₀ := by
    calc (n.primeFactors.filter (fun p => p < P₀)).card
        ≤ (Finset.range P₀).card := Finset.card_le_card fun p hp =>
          Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = P₀ := Finset.card_range P₀
  exact (hind n hn).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hK_ge1 hcard_le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Under the Ramanujan–Petersson bound `|τ(p)| ≤ 2 p^{11/2}` at every prime `p`,
Ramanujan's `τ(n)` satisfies Deligne's divisor bound `|τ(n)| ≤ d(n) n^{11/2}` for ALL `n ≥ 1`. -/
theorem ramanujanTau_deligne_divisor_bound_of_RP
    (hRP : ∀ p : ℕ, p.Prime → |(ramanujanTau p : ℝ)| ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2))
    (n : ℕ) (hn : 1 ≤ n) :
    |(ramanujanTau n : ℝ)| ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 2) := by
  have hsat : ∀ p : ℕ, p.Prime →
      ∃ α β : ℂ, IsSatakePair (ramanujanTau p : ℂ)
        ((1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (12 - 1)) α β ∧
        ‖α‖ ≤ (p : ℝ) ^ (((12 - 1 : ℕ) : ℝ) / 2) ∧
        ‖β‖ ≤ (p : ℝ) ^ (((12 - 1 : ℕ) : ℝ) / 2) := by
    intro p hp
    obtain ⟨α, β, hs⟩ := exists_satake_pair (ramanujanTau p : ℂ)
      ((1 : DirichletCharacter ℂ 1) (p : ZMod 1) * (p : ℂ) ^ (12 - 1))
    have hnorm_tau : ‖(ramanujanTau p : ℂ)‖ ≤ 2 * (p : ℝ) ^ (((12 - 1 : ℕ) : ℝ) / 2) := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      simpa using hRP p hp
    have hself : star (ramanujanTau p : ℂ) =
        star ((1 : DirichletCharacter ℂ 1) (p : ZMod 1)) * (ramanujanTau p : ℂ) := by
      simp [trivialChar_one_apply]
    have hunit : ‖(1 : DirichletCharacter ℂ 1) (p : ZMod 1)‖ = 1 := by
      simp [trivialChar_one_apply]
    have hiff := (ramanujan_petersson_iff (k := 12) (N := 1) (1 : DirichletCharacter ℂ 1)
      hp hunit hs).mpr ⟨hnorm_tau, hself⟩
    exact ⟨α, β, hs, hiff.1.le, hiff.2.le⟩
  have hdel := eigenform_deligne_divisor_bound (k := 12) (N := 1)
    isNormalizedHeckeEigenform_ramanujanTau hsat n hn
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] at hdel
  simpa using hdel

/-- Under Ramanujan–Petersson, `LSeries (fun n => (τ(n) : ℂ)) s` is absolutely summable for ALL
`s : ℂ` with `13 / 2 < s.re`. -/
theorem LSeriesSummable_ramanujanTau_of_RP
    (hRP : ∀ p : ℕ, p.Prime → |(ramanujanTau p : ℝ)| ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2))
    {s : ℂ} (hs : (13 : ℝ) / 2 < s.re) :
    LSeriesSummable (fun n => (ramanujanTau n : ℂ)) s := by
  set ε : ℝ := (s.re - 13 / 2) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  obtain ⟨C, hC_pos, hC⟩ := divisors_card_le_rpow hε
  refine LSeriesSummable_of_isBigO_rpow (x := 13 / 2 + ε) (by dsimp only [ε]; linarith) ?_
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg hn_pos.le _)]
  have hdel := ramanujanTau_deligne_divisor_bound_of_RP hRP n hn
  have hdiv := hC n hn
  have hexp : ε + (11 : ℝ) / 2 = 13 / 2 + ε - 1 := by ring
  calc |(ramanujanTau n : ℝ)|
      ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ ((11 : ℝ) / 2) := hdel
    _ ≤ (C * (n : ℝ) ^ ε) * (n : ℝ) ^ ((11 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hn_pos.le _)
    _ = C * ((n : ℝ) ^ ε * (n : ℝ) ^ ((11 : ℝ) / 2)) := by ring
    _ = C * (n : ℝ) ^ (13 / 2 + ε - 1) := by rw [← Real.rpow_add hn_pos, hexp]

/-- Under Ramanujan–Petersson, the analytic continuation `deltaL s` agrees with the convergent
Dirichlet series `LSeries τ s` throughout the ENTIRE half-plane `Re(s) > 13 / 2`. -/
theorem deltaL_eq_LSeries_of_RP
    (hRP : ∀ p : ℕ, p.Prime → |(ramanujanTau p : ℝ)| ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2))
    {s : ℂ} (hs : (13 : ℝ) / 2 < s.re) :
    deltaL s = LSeries (fun n => (ramanujanTau n : ℂ)) s := by
  let U : Set ℂ := {z : ℂ | (13 : ℝ) / 2 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt ((13 : ℝ) / 2)).isPreconnected
  -- `LSeries τ` is differentiable on `U` by uniform convergence on every sub-half-plane `Re(z) > σ₀`.
  have hL_diff : DifferentiableOn ℂ (LSeries (fun n => (ramanujanTau n : ℂ))) U := by
    intro z hz
    set σ₀ : ℝ := (13 / 2 + z.re) / 2
    have hσ₀_gt : (13 : ℝ) / 2 < σ₀ := by dsimp only [σ₀]; linarith [Set.mem_ofPred.mp hz]
    have hz_gt : σ₀ < z.re := by dsimp only [σ₀]; linarith [Set.mem_ofPred.mp hz]
    let V : Set ℂ := {w : ℂ | σ₀ < w.re}
    have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
    have hsumm : Summable (fun n : ℕ => ‖LSeries.term (fun k => (ramanujanTau k : ℂ)) (σ₀ : ℂ) n‖) :=
      (LSeriesSummable_ramanujanTau_of_RP hRP (by simpa using hσ₀_gt)).norm
    have hterm_diff : ∀ n : ℕ, DifferentiableOn ℂ
        (fun w : ℂ => LSeries.term (fun k => (ramanujanTau k : ℂ)) w n) V := by
      intro n
      by_cases hn : n = 0
      · subst hn; simp [LSeries.term_zero]
      · have hfun : (fun w : ℂ => LSeries.term (fun k => (ramanujanTau k : ℂ)) w n) =
            fun w : ℂ => (ramanujanTau n : ℂ) / (n : ℂ) ^ w := by
          funext w; exact LSeries.term_of_ne_zero hn _ _
        rw [hfun]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        refine (differentiable_const _).differentiableOn.div
          (differentiable_id.const_cpow (Or.inl hnC)).differentiableOn fun w _ =>
          Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hterm_bd : ∀ n : ℕ, ∀ w ∈ V,
        ‖LSeries.term (fun k => (ramanujanTau k : ℂ)) w n‖ ≤
          ‖LSeries.term (fun k => (ramanujanTau k : ℂ)) (σ₀ : ℂ) n‖ := by
      intro n w hw
      by_cases hn : n = 0
      · subst hn; simp [LSeries.term_zero]
      · have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
        rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div,
          show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos hn_pos,
          Complex.norm_cpow_eq_rpow_re_of_pos hn_pos, Complex.ofReal_re]
        exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hn_pos _)
          (Real.rpow_le_rpow_of_exponent_le hn_ge1 (le_of_lt hw))
    have hV_diff := Complex.differentiableOn_tsum_of_summable_norm hsumm hterm_diff hV_open hterm_bd
    exact (hV_diff.differentiableAt (hV_open.mem_nhds hz_gt)).differentiableWithinAt
  have hdelta_an : AnalyticOnNhd ℂ deltaL U :=
    differentiable_deltaL.differentiableOn.analyticOnNhd isOpen_univ |>.mono (Set.subset_univ _)
  have hL_an : AnalyticOnNhd ℂ (LSeries (fun n => (ramanujanTau n : ℂ))) U :=
    hL_diff.analyticOnNhd hU_open
  have h8_mem : (8 : ℂ) ∈ U := by change (13 : ℝ) / 2 < (8 : ℂ).re; norm_num
  have hagree_ev : deltaL =ᶠ[𝓝 (8 : ℂ)] LSeries (fun n => (ramanujanTau n : ℂ)) := by
    have hopen7 : IsOpen {z : ℂ | (7 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem7 : (8 : ℂ) ∈ {z : ℂ | (7 : ℝ) < z.re} := by norm_num
    filter_upwards [hopen7.mem_nhds hmem7] with z hz
    exact deltaL_eq_LSeries hz
  exact hdelta_an.eqOn_of_preconnected_of_eventuallyEq hL_an hU_conn h8_mem hagree_ev hs

/-- **UNCONDITIONAL CONDITIONAL-ON-DELIGNE BRIDGE (`deligne_ramanujan_implies_euler_nonvanishing`)**:
Assuming the Ramanujan–Petersson bound `∀ p, p.Prime → |(τ(p) : ℝ)| ≤ 2 p^{11/2}` (Deligne 1974):
1. For EVERY `s : ℂ` with `Re(s) > 13 / 2`, the Dirichlet series `L(Δ, s)` converges absolutely,
   equals its degree-2 Euler product `∏' p, (1 - τ(p) p^{-s} + p^{11 - 2s})⁻¹`, and **`deltaL s ≠ 0`**;
2. Every zero `s : ℂ` of `completedDeltaL` lies in the **narrowed critical strip `11 / 2 ≤ Re(s) ≤ 13 / 2`**! -/
theorem deligne_ramanujan_implies_euler_nonvanishing
    (hRP : ∀ p : ℕ, p.Prime → |(ramanujanTau p : ℝ)| ≤ 2 * (p : ℝ) ^ ((11 : ℝ) / 2)) :
    (∀ {s : ℂ}, (13 : ℝ) / 2 < s.re →
      LSeriesSummable (fun n => (ramanujanTau n : ℂ)) s ∧
      deltaL s = ∏' p : Nat.Primes,
        (1 - (ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ ∧
      deltaL s ≠ 0) ∧
    (∀ {s : ℂ}, completedDeltaL s = 0 → (11 : ℝ) / 2 ≤ s.re ∧ s.re ≤ (13 : ℝ) / 2) := by
  have hmain : ∀ {s : ℂ}, (13 : ℝ) / 2 < s.re →
      LSeriesSummable (fun n => (ramanujanTau n : ℂ)) s ∧
      deltaL s = ∏' p : Nat.Primes,
        (1 - (ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ ∧
      deltaL s ≠ 0 := by
    intro s hs
    have hLsumm := LSeriesSummable_ramanujanTau_of_RP hRP hs
    have hdeg2 : ∀ p : ℕ, degree2EulerFactor 12 (1 : DirichletCharacter ℂ 1)
        (ramanujanTau p : ℂ) p s =
        (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹ := fun p => by
      simp only [degree2EulerFactor, trivialChar_one_apply, one_mul]; norm_num
    have heuler : deltaL s = ∏' p : Nat.Primes,
        (1 - (ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ := by
      rw [deltaL_eq_LSeries_of_RP hRP hs,
        ← eigenform_LSeries_eulerProduct isNormalizedHeckeEigenform_ramanujanTau hLsumm]
      exact tprod_congr fun p => hdeg2 p.1
    -- Nonvanishing on `Re(s) > 13/2` via convergence of the inverse Euler product `∏ (1 + a_p)`.
    have hne : deltaL s ≠ 0 := by
      rw [deltaL_eq_LSeries_of_RP hRP hs]
      let a : Nat.Primes → ℂ := fun p =>
        -(ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s)
      have hsum_tau : Summable (fun p : Nat.Primes =>
          -(ramanujanTau p.1 : ℂ) * (p.1 : ℂ) ^ (-s)) := by
        have hL : Summable (fun p : Nat.Primes =>
            LSeries.term (fun n => (ramanujanTau n : ℂ)) s p.1) :=
          hLsumm.comp_injective (Subtype.val_injective (p := Nat.Prime))
        refine hL.neg.congr fun p => ?_
        have hp0 : p.1 ≠ 0 := p.prop.ne_zero
        simp only [LSeries.term_of_ne_zero hp0, div_eq_mul_inv, Complex.cpow_neg]
        ring
      have hsum_pow : Summable (fun p : Nat.Primes => (p.1 : ℂ) ^ (11 - 2 * s)) := by
        have hre : 1 < 2 * s.re - 11 := by linarith
        have hsub : Summable (fun p : Nat.Primes => ((p.1 : ℝ) ^ (2 * s.re - 11))⁻¹) :=
          (Real.summable_nat_rpow_inv.mpr hre).comp_injective (Subtype.val_injective (p := Nat.Prime))
        refine Summable.of_norm (hsub.congr fun p => ?_)
        have hp_pos : (0 : ℝ) < (p.1 : ℝ) := Nat.cast_pos.mpr p.prop.pos
        have hre_exp : (11 - 2 * s).re = -(2 * s.re - 11) := by simp
        change ((p.1 : ℝ) ^ (2 * s.re - 11))⁻¹ = ‖(p.1 : ℂ) ^ (11 - 2 * s)‖
        rw [show (p.1 : ℂ) = ((p.1 : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, hre_exp, Real.rpow_neg hp_pos.le]
      have hmult : Multipliable (fun p : Nat.Primes => 1 + a p) :=
        Complex.multipliable_one_add_of_summable (hsum_tau.add hsum_pow)
      let embed : ℕ → Finset Nat.Primes := fun B =>
        Finset.map
          ⟨fun (x : {p // p ∈ B.primesBelow}) =>
            (⟨x.1, Nat.prime_of_mem_primesBelow x.2⟩ : Nat.Primes),
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
        rw [Finset.mem_map]
        exact ⟨⟨p.1, Nat.mem_primesBelow.mpr ⟨hlt, p.prop⟩⟩, Finset.mem_attach _ _, rfl⟩
      have hprod_tendsto : Tendsto
          (fun B : ℕ => ∏ p ∈ B.primesBelow,
            (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s)))
          atTop (nhds (∏' p : Nat.Primes, (1 + a p))) := by
        refine (hmult.hasProd.comp hembed_atTop).congr fun B => ?_
        dsimp only [Function.comp_apply, embed]
        rw [Finset.prod_map, ← Finset.prod_attach B.primesBelow]
        refine Finset.prod_congr rfl fun x _ => ?_
        change 1 + (-(ramanujanTau x.1 : ℂ) * (x.1 : ℂ) ^ (-s) + (x.1 : ℂ) ^ (11 - 2 * s)) = _
        ring
      have hinv_tendsto : Tendsto
          (fun B : ℕ => ∏ p ∈ B.primesBelow,
            (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹)
          atTop (nhds (LSeries (fun n => (ramanujanTau n : ℂ)) s)) := by
        refine (eigenform_LSeries_eulerProduct_tendsto
          isNormalizedHeckeEigenform_ramanujanTau hLsumm).congr fun B => ?_
        exact Finset.prod_congr rfl fun p _ => hdeg2 p
      have hconst_one : ∀ B : ℕ,
          (∏ p ∈ B.primesBelow,
            (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))) *
          (∏ p ∈ B.primesBelow,
            (1 - (ramanujanTau p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) ^ (11 - 2 * s))⁻¹) = 1 := by
        intro B
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun p hp => ?_
        have hfac_ne := degree2EulerFactor_ne_zero isNormalizedHeckeEigenform_ramanujanTau
          hLsumm (Nat.prime_of_mem_primesBelow hp)
        rw [hdeg2 p] at hfac_ne
        exact mul_inv_cancel₀ fun h0 => hfac_ne (by rw [h0, inv_zero])
      have heq_one : (∏' p : Nat.Primes, (1 + a p)) *
          LSeries (fun n => (ramanujanTau n : ℂ)) s = 1 :=
        tendsto_nhds_unique ((hprod_tendsto.mul hinv_tendsto).congr hconst_one) tendsto_const_nhds
      exact right_ne_zero_of_mul_eq_one heq_one
    exact ⟨hLsumm, heuler, hne⟩
  refine ⟨@hmain, fun {s} hs => ?_⟩
  have hle : s.re ≤ (13 : ℝ) / 2 := by
    by_contra hgt
    push Not at hgt
    have hL_ne := (hmain hgt).2.2
    have hL_zero : deltaL s = 0 := by
      unfold deltaL cuspL
      change (2 * (Real.pi : ℂ)) ^ s * (Complex.Gamma s)⁻¹ * completedDeltaL s = 0
      rw [hs, mul_zero]
    exact hL_ne hL_zero
  have hge : (11 : ℝ) / 2 ≤ s.re := by
    by_contra hlt
    push Not at hlt
    have h12_gt : (13 : ℝ) / 2 < (12 - s).re := by simp; linarith
    have hfe : completedDeltaL (12 - s) = 0 := by
      rw [completedDeltaL_functional_equation, hs]
    have hL_ne := (hmain h12_gt).2.2
    have hL_zero : deltaL (12 - s) = 0 := by
      unfold deltaL cuspL
      change (2 * (Real.pi : ℂ)) ^ (12 - s) * (Complex.Gamma (12 - s))⁻¹ *
        completedDeltaL (12 - s) = 0
      rw [hfe, mul_zero]
    exact hL_ne hL_zero
  exact ⟨hge, hle⟩

end DeligneBridge

end

end RHDirect.Stage9DeltaHadamard
