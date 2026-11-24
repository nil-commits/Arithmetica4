import RHDirect.Stage2PrimePairs
import RHDirect.Stage2DirichletAP
import RHDirect.Stage4ExplicitFormula
import RHDirect.Stage5ContourExplicit
import RHDirect.Stage6LFunctionOrder
import RHDirect.Stage7SiegelWalfisz
import RHDirect.Stage8HadamardLFunction
import RHDirect.Stage8GRHEquivalence
import RHDirect.Stage8UniformAP
import RHDirect.Stage9ExplicitFormula
import RHDirect.Stage9LandauSiegel
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Analytic.Order

/-!
# RHDirect.Stage11LinnikBridge

Completely **UNCONDITIONAL** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) Stage 11
formalization of:

1. **Uniform Good Horizontal Contours & Left-Vertical Bounds for Every Primitive `L(s, χ)`**:
   - Exact logarithmic-derivative decompositions of `negLogDerivL ψ s` across `Re(s) > -1` for
     both odd and even primitive Dirichlet characters `ψ ≠ 1`.
   - Uniform left-vertical bound `‖negLogDerivL ψ (-1/2 + I * t)‖ ≤ C * Real.log (q * (|t| + 2))`.
   - Uniform good horizontal contour height selection `exists_good_contour_height_primitive`:
     for every primitive `ψ ≠ 1` mod `q` and `T ≥ 4`, there exists `T' ∈ [T, T + 1]` avoiding all
     zeros of `completedLFunction ψ` by `≥ c / Real.log (q * T)` on which
     `‖negLogDerivL ψ (σ ± I * T')‖ ≤ C * (Real.log (q * T)) ^ 2` uniformly for `-1/2 ≤ σ ≤ 2`.

2. **Gallagher / Cesàro-1 Smoothed Dyadic Explicit Formula for Every `χ mod m` & `ψ₁(x; m, a)`**:
   - Entire tent Mellin kernel `dyadicKernel s = (2^(s+1) - 2*(3/2)^(s+1) + 1) / (s*(s+1))`
     whose zero at `s = 0` eliminates both the `(-L'/L)(0, χ)` singularity and the `1 / |ρ|`
     blowup near `ρ = 0` when a Siegel zero `β₁ → 1` produces a symmetric zero `1 - β₁ → 0`.
   - Unconditional smoothed dyadic explicit formulas `explicit_formula_dyadic2_psi1Char` and
     `smoothed_ap_dyadic_explicit_formula` directly on Mathlib's `DirichletCharacter.LFunction`.

3. **Exact Clean Reduction `(DeuringHeilbronnHypothesis + LogFreeZeroDensityHypothesis) →
   Stage2PrimePairs.LinnikAPDyadic → LinnikAPInterval → PairEx / PairSupply / SmallOne`**:
   - Unconditional simplicity of any Siegel zero (`siegel_zero_simple_unconditional`).
   - Exact clean predicates `DeuringHeilbronnHypothesis` and `LogFreeZeroDensityHypothesis`
     matching `Stage11DeuringHeilbronn` and `Stage11LogFreeDensity`.
   - Complete proof of `linnikAPDyadic_of_dh_and_logfree`, `linnikAPInterval_of_dh_and_logfree`,
     `pairSupply_of_dh_and_logfree`, `pairEx_of_dh_and_logfree`, and `smallOne_of_dh_and_logfree`.

4. **Sharp `GRH`-Conditional Linnik Constant (`L = 2 + ε` & `L = 3`)**:
   - `smoothed_ap_dyadic_of_GRH`, `exists_prime_in_dyadic_ap_of_GRH_sharp`,
     `linnik_exp_three_eventually_of_GRH`, and `linnikAPDyadic_of_GRH`.
-/

noncomputable section

open Complex DirichletCharacter MeasureTheory Set Filter Topology Finset Metric
open scoped BigOperators Real ArithmeticFunction.vonMangoldt

namespace RHDirect.Stage11LinnikBridge

open RHDirect.Stage2PrimePairs
open RHDirect.Stage2DirichletAP
open RHDirect.Stage3ZeroFreeRegion
open RHDirect.Stage4ExplicitFormula
open RHDirect.Stage5ContourExplicit
open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree
open RHDirect.Stage5DirichletLZeroFree
open RHDirect.Stage6LFunctionOrder
open RHDirect.Stage7HadamardXiProduct
open RHDirect.Stage7SiegelWalfisz
open RHDirect.Stage8HadamardLFunction
open RHDirect.Stage8GRHEquivalence
open RHDirect.Stage8UniformAP
open RHDirect.Stage9ExplicitFormula
open RHDirect.Stage9LandauSiegel

/-! ## Section 1: Uniform Log-Derivative Bounds & Good Horizontal Contours for Primitive `L(s, χ)` -/

/-- Exact digamma functional equation `digamma (w + 1) = digamma w + 1 / w` on `Re(w) > 0`. -/
lemma digamma_add_one_eq {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma (w + 1) = Complex.digamma w + 1 / w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  have hG_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hG_diff : DifferentiableAt ℂ Complex.Gamma w :=
    Complex.differentiableAt_Gamma w fun m hEq => by
      have hre := congrArg Complex.re hEq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[𝓝 w] fun z : ℂ => z * Complex.Gamma z := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
    exact Complex.Gamma_add_one z hz0
  have hd : deriv (fun z : ℂ => Complex.Gamma (z + 1)) w =
      Complex.Gamma w + w * deriv Complex.Gamma w := by
    have hmul : HasDerivAt (fun z : ℂ => z * Complex.Gamma z)
        (1 * Complex.Gamma w + w * deriv Complex.Gamma w) w :=
      (hasDerivAt_id' w).mul hG_diff.hasDerivAt
    rw [hev.deriv_eq, hmul.deriv, one_mul]
  have hshift : deriv (fun z : ℂ => Complex.Gamma (z + 1)) w = deriv Complex.Gamma (w + 1) := by
    simpa using deriv_comp_add_const Complex.Gamma (1 : ℂ) w
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, ← hshift, hd,
    Complex.Gamma_add_one w hw0]
  field_simp [hw0, hG_ne]
  ring

/-- Uniform logarithmic bound on `Complex.digamma` across `1 / 4 ≤ Re(w) ≤ 2`. -/
theorem norm_digamma_quarter_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 1 / 4 ≤ w.re → w.re ≤ 2 →
      ‖Complex.digamma w‖ ≤ C * Real.log (|w.im| + 2) := by
  obtain ⟨C₀, hC₀_pos, hdig⟩ := Stage9ExplicitFormula.norm_digamma_strip_le
  refine ⟨C₀ + 8, by positivity, fun w hlo hhi => ?_⟩
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (|w.im| + 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg w.im]))
  by_cases hhalf : 1 / 2 ≤ w.re
  · exact (hdig w hhalf hhi).trans (by nlinarith)
  · push Not at hhalf
    have heq : Complex.digamma w = Complex.digamma (w + 1) - 1 / w := by
      linear_combination -(digamma_add_one_eq (by linarith : 0 < w.re))
    rw [heq]
    have h1 : ‖Complex.digamma (w + 1)‖ ≤ C₀ * Real.log (|w.im| + 2) := by
      have h := hdig (w + 1) (by simp; linarith) (by simp; linarith)
      simpa using h
    have h2 : ‖(1 : ℂ) / w‖ ≤ 4 := by
      rw [norm_div, norm_one]
      have hre : 1 / 4 ≤ ‖w‖ := by
        have h := Complex.abs_re_le_norm w
        rw [abs_of_pos (by linarith)] at h; linarith
      rw [div_le_iff₀ (by linarith)]; linarith
    calc ‖Complex.digamma (w + 1) - 1 / w‖
        ≤ ‖Complex.digamma (w + 1)‖ + ‖(1 : ℂ) / w‖ := norm_sub_le _ _
      _ ≤ C₀ * Real.log (|w.im| + 2) + 4 := add_le_add h1 h2
      _ ≤ (C₀ + 8) * Real.log (|w.im| + 2) := by nlinarith

/-- Exact logarithmic-derivative decomposition for **odd** primitive `ψ` across `Re(s) > -1`:
`negLogDerivL ψ s = -logDeriv (completedLFunction ψ) s - log π / 2 + (1/2) digamma ((s + 1) / 2)`. -/
theorem negLogDerivL_eq_neg_logDeriv_completedL_odd {q : ℕ} [NeZero q]
    {ψ : DirichletCharacter ℂ q} (hodd : ψ.Odd) (hψ : ψ ≠ 1) {s : ℂ}
    (hs : -1 < s.re) (hΛ : DirichletCharacter.completedLFunction ψ s ≠ 0) :
    Stage3ZeroFreeRegion.negLogDerivL ψ s =
      -logDeriv (DirichletCharacter.completedLFunction ψ) s -
        ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hq_ne1 : q ≠ 1 := by omega
  have hopen : IsOpen {w : ℂ | -1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG_ne_all : ∀ w : ℂ, -1 < w.re → DirichletCharacter.gammaFactor ψ w ≠ 0 := fun w hw => by
    rw [hodd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hev : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 s]
      fun w : ℂ => DirichletCharacter.LFunction ψ w * DirichletCharacter.gammaFactor ψ w := by
    filter_upwards [hopen.mem_nhds hs] with w hw
    exact completedLFunction_eq_LFunction_mul_gammaFactor ψ (.inr hq_ne1) (hG_ne_all w hw)
  have hG_ne : DirichletCharacter.gammaFactor ψ s ≠ 0 := hG_ne_all s hs
  have hL_ne : DirichletCharacter.LFunction ψ s ≠ 0 := fun hz => hΛ (by
    have hs_eq := hev.self_of_nhds
    dsimp only at hs_eq
    rw [hs_eq, hz, zero_mul])
  have hL_diff : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) s :=
    (DirichletCharacter.differentiable_LFunction hψ) s
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hG_diff : DifferentiableAt ℂ (DirichletCharacter.gammaFactor ψ) s := by
    have hfun : DirichletCharacter.gammaFactor ψ =
        fun z : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-(z + 1) / 2)) *
          Complex.Gamma ((z + 1) / 2) := by
      funext z; rw [hodd.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
    rw [hfun]
    have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-(z + 1) / 2))) s := by
      fun_prop
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 1) / 2)) s :=
      (Complex.differentiableAt_Gamma ((s + 1) / 2) fun m hEq => by
        have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) m]).comp s
          ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2)
    exact h1.mul h2
  have hld_G : logDeriv (DirichletCharacter.gammaFactor ψ) s =
      -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
    have hfun : DirichletCharacter.gammaFactor ψ = fun z => Complex.Gammaℝ (z + 1) :=
      funext fun z => hodd.gammaFactor_def z
    rw [logDeriv_apply, hfun]
    have hsh : deriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s = deriv Complex.Gammaℝ (s + 1) := by
      simpa using deriv_comp_add_const Complex.Gammaℝ (1 : ℂ) s
    rw [hsh]
    exact Stage8HadamardLFunction.logDeriv_Gammaℝ (by simp; linarith)
  have hld_Λ : logDeriv (DirichletCharacter.completedLFunction ψ) s =
      logDeriv (DirichletCharacter.LFunction ψ) s + logDeriv (DirichletCharacter.gammaFactor ψ) s := by
    have h1 : logDeriv (DirichletCharacter.completedLFunction ψ) s =
        logDeriv (fun w => DirichletCharacter.LFunction ψ w * DirichletCharacter.gammaFactor ψ w) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
    rw [h1, logDeriv_mul s hL_ne hG_ne hL_diff hG_diff]
  rw [hld_G, logDeriv_apply, logDeriv_apply] at hld_Λ
  unfold Stage3ZeroFreeRegion.negLogDerivL
  rw [neg_div, logDeriv_apply]
  linear_combination hld_Λ

/-- Exact factorization for **even** non-principal `ψ` on `Re(s) > -2, s ≠ 0`:
`(s / 2) * completedLFunction ψ s = LFunction ψ s * π ^ (-s / 2) * Gamma (s / 2 + 1)`. -/
lemma even_completedL_factorization {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    (heven : ψ.Even) (hψ : ψ ≠ 1) {s : ℂ} (hs : -2 < s.re) (hs0 : s ≠ 0) :
    (s / 2) * DirichletCharacter.completedLFunction ψ s =
      DirichletCharacter.LFunction ψ s * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) := by
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hs2_ne : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  have hG_ne : DirichletCharacter.gammaFactor ψ s ≠ 0 := by
    rw [heven.gammaFactor_def]
    intro hg
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
    cases n with
    | zero => simp at hn; exact hs0 hn
    | succ m =>
      have hre := congrArg Complex.re hn
      simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero] at hre
      have hm1 : (1 : ℝ) ≤ ((m.succ : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      linarith
  rw [completedLFunction_eq_LFunction_mul_gammaFactor ψ (.inl hs0) hG_ne,
    heven.gammaFactor_def, Complex.Gammaℝ_def, Complex.Gamma_add_one (s / 2) hs2_ne]
  ring

/-- Exact logarithmic-derivative decomposition for **even** non-principal `ψ` across `Re(s) > -2`,
`s ≠ 0`:
`negLogDerivL ψ s = -logDeriv (completedLFunction ψ) s - 1 / s - log π / 2 + (1/2) digamma (s / 2 + 1)`. -/
theorem negLogDerivL_eq_neg_logDeriv_completedL_even {q : ℕ} [NeZero q]
    {ψ : DirichletCharacter ℂ q} (heven : ψ.Even) (hψ : ψ ≠ 1) {s : ℂ}
    (hs : -2 < s.re) (hs0 : s ≠ 0) (hΛ : DirichletCharacter.completedLFunction ψ s ≠ 0) :
    Stage3ZeroFreeRegion.negLogDerivL ψ s =
      -logDeriv (DirichletCharacter.completedLFunction ψ) s - 1 / s -
        ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs2_re : 0 < (s / 2 + 1).re := by simp; linarith
  have hG_ne : Complex.Gamma (s / 2 + 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2_re
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpiC]; exact Complex.exp_ne_zero _
  have hs2_ne : s / 2 ≠ 0 := div_ne_zero hs0 two_ne_zero
  have hL_ne : DirichletCharacter.LFunction ψ s ≠ 0 := fun hz => by
    have hfac := even_completedL_factorization heven hψ hs hs0
    rw [hz, zero_mul, zero_mul] at hfac
    exact mul_ne_zero hs2_ne hΛ hfac
  have hopen : IsOpen ({w : ℂ | -2 < w.re} \ {(0 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev : (fun w : ℂ => (w / 2) * DirichletCharacter.completedLFunction ψ w) =ᶠ[𝓝 s]
      fun w : ℂ => DirichletCharacter.LFunction ψ w * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1) := by
    filter_upwards [hopen.mem_nhds ⟨hs, hs0⟩] with w hw
    exact even_completedL_factorization heven hψ hw.1 hw.2
  have hd_pow : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      (-((Real.log Real.pi / 2 : ℝ) : ℂ) * (Real.pi : ℂ) ^ (-s / 2)) s := by
    have hEq : (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) =
        fun w : ℂ => cexp (-((Real.log Real.pi / 2 : ℝ) : ℂ) * w) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero hpiC, ← Complex.ofReal_log Real.pi_pos.le]
      congr 1; push_cast; ring
    rw [hEq]
    have hlin : HasDerivAt (fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) * w)
        (-((Real.log Real.pi / 2 : ℝ) : ℂ)) s := by
      simpa using (hasDerivAt_id s).const_mul (-((Real.log Real.pi / 2 : ℝ) : ℂ))
    exact hlin.cexp.congr_deriv (by rw [congrFun hEq s]; ring)
  have hd_Gam : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2 + 1))
      ((1 / 2 : ℂ) * deriv Complex.Gamma (s / 2 + 1)) s := by
    have hG_diff : DifferentiableAt ℂ Complex.Gamma (s / 2 + 1) :=
      Complex.differentiableAt_Gamma (s / 2 + 1) fun m hEq => by
        have hre := congrArg Complex.re hEq
        simp only [Complex.neg_re, Complex.natCast_re] at hre
        linarith [Nat.cast_nonneg (α := ℝ) m]
    have hlin : HasDerivAt (fun w : ℂ => w / 2 + 1) (1 / 2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).div_const (2 : ℂ)).add_const (1 : ℂ)
    exact (hG_diff.hasDerivAt.comp s hlin).congr_deriv (by ring)
  have hd_s2 : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hd_Λ : DifferentiableAt ℂ (DirichletCharacter.completedLFunction ψ) s :=
    (differentiable_completedLFunction_prim hψ) s
  have hd_L : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) s :=
    (DirichletCharacter.differentiable_LFunction hψ) s
  have hld_eq :
      logDeriv (fun w : ℂ => (w / 2) * DirichletCharacter.completedLFunction ψ w) s =
      logDeriv (fun w : ℂ => DirichletCharacter.LFunction ψ w * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1)) s := by
    have hs_eq := hev.self_of_nhds
    dsimp only at hs_eq
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hs_eq]
  have hLHS : logDeriv (fun w : ℂ => (w / 2) * DirichletCharacter.completedLFunction ψ w) s =
      1 / s + logDeriv (DirichletCharacter.completedLFunction ψ) s := by
    rw [logDeriv_mul s hs2_ne hΛ hd_s2.differentiableAt hd_Λ, logDeriv_apply, hd_s2.deriv]
    congr 1; field_simp [hs0]
  have hRHS : logDeriv (fun w : ℂ => DirichletCharacter.LFunction ψ w * (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2 + 1)) s =
      logDeriv (DirichletCharacter.LFunction ψ) s - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
    rw [logDeriv_mul (f := fun w => DirichletCharacter.LFunction ψ w * (Real.pi : ℂ) ^ (-w / 2))
          (g := fun w => Complex.Gamma (w / 2 + 1)) s (mul_ne_zero hL_ne hpow_ne) hG_ne
          (hd_L.mul hd_pow.differentiableAt) hd_Gam.differentiableAt,
        logDeriv_mul s hL_ne hpow_ne hd_L hd_pow.differentiableAt]
    have ht1 : logDeriv (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s = -((Real.log Real.pi / 2 : ℝ) : ℂ) := by
      rw [logDeriv_apply, hd_pow.deriv]; field_simp [hpow_ne]
    have ht2 : logDeriv (fun w : ℂ => Complex.Gamma (w / 2 + 1)) s = (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
      rw [logDeriv_apply, hd_Gam.deriv, Complex.digamma_def, logDeriv_apply]; ring
    rw [ht1, ht2]; ring
  rw [hLHS, hRHS, logDeriv_apply, logDeriv_apply] at hld_eq
  unfold Stage3ZeroFreeRegion.negLogDerivL
  rw [neg_div, logDeriv_apply]
  linear_combination hld_eq

/-- Local helper: Dirichlet series bound `‖negLogDerivL χ (σ + I * t)‖ ≤ ∑' n, Λ n * n ^ (-σ)`
for `1 < σ`. -/
private lemma norm_negLogDerivL_le_tsum_local {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {c : ℝ} (hc : 1 < c) (t : ℝ) :
    ‖Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ))‖ ≤
      ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c) := by
  have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc]
  rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
  have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    simpa using h
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsumL.norm).trans (hsumL.norm.tsum_le_tsum (fun n => ?_) hsumR)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn.ne', ↓reduceIte, norm_div, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.norm_natCast_cpow_of_pos hn]
    have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hre, Real.rpow_neg hnR.le, div_eq_mul_inv]
    calc ‖χ (n : ZMod q)‖ * Λ n * ((n : ℝ) ^ c)⁻¹
        ≤ 1 * Λ n * ((n : ℝ) ^ c)⁻¹ := by gcongr; exact χ.norm_le_one _
      _ = Λ n * ((n : ℝ) ^ c)⁻¹ := by ring

/-- Uniform logarithmic bound on `‖logDeriv (completedLFunction ψ) (σ + I * t)‖` for `3 / 2 ≤ σ ≤ 2`,
ALL primitive `ψ ≠ 1` mod `q`, and ALL `t : ℝ`. -/
lemma norm_logDeriv_completedL_right_strip_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ ≠ 1 → ∀ σ : ℝ, 3 / 2 ≤ σ → σ ≤ 2 → ∀ t : ℝ,
        ‖logDeriv (DirichletCharacter.completedLFunction ψ) ((σ : ℂ) + I * (t : ℂ))‖ ≤
          C * Real.log (|t| + 2) := by
  obtain ⟨Cd, hCd_pos, hdig⟩ := norm_digamma_quarter_strip_le
  set C : ℝ := 2 * (26 + Real.log Real.pi / 2) + Cd
  have hpi_nn : 0 ≤ Real.log Real.pi / 2 :=
    div_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi])) (by norm_num)
  refine ⟨C, by positivity, fun q _ ψ _ hψ σ hσ1 hσ2 t => ?_⟩
  set s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs_re : s.re = σ := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; linarith
  have hΛ_ne : DirichletCharacter.completedLFunction ψ s ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hψ (by linarith)
  have hL_bd : ‖Stage3ZeroFreeRegion.negLogDerivL ψ s‖ ≤ 24 := by
    have h1 := norm_negLogDerivL_le_tsum_local ψ (by linarith : 1 < σ) t
    have h2 := Stage4ExplicitFormula.tsum_vonMangoldt_mul_rpow_le (c := σ) (by linarith)
    have h3 : 6 * σ / (σ - 1) ≤ 24 := by rw [div_le_iff₀ (by linarith)]; linarith
    exact (h1.trans h2).trans h3
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  rcases ψ.even_or_odd with he | ho
  · have hdec := negLogDerivL_eq_neg_logDeriv_completedL_even he hψ (by linarith : -2 < s.re) hs0 hΛ_ne
    have hld_eq : logDeriv (DirichletCharacter.completedLFunction ψ) s =
        -Stage3ZeroFreeRegion.negLogDerivL ψ s - 1 / s -
          ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
      linear_combination hdec
    have hinv_s : ‖(1 : ℂ) / s‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have hre : 3 / 2 ≤ ‖s‖ := by
        have h := Complex.abs_re_le_norm s; rw [hs_re, abs_of_pos (by linarith)] at h; linarith
      rw [div_le_one (by linarith)]; linarith
    have hdig_le : ‖Complex.digamma (s / 2 + 1)‖ ≤ Cd * Real.log (|t| + 2) := by
      have h1 := hdig (s / 2 + 1) (by simp [hs_re]; linarith) (by simp [hs_re]; linarith)
      have him : |(s / 2 + 1).im| + 2 ≤ |t| + 2 := by
        have h2 : (s / 2 + 1).im = t / 2 := by simp [hs_im]
        rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg t]
      exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
    rw [hld_eq]
    have h1 := norm_add_le (-Stage3ZeroFreeRegion.negLogDerivL ψ s - 1 / s - ((Real.log Real.pi / 2 : ℝ) : ℂ))
      ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
    have h2 := norm_sub_le (-Stage3ZeroFreeRegion.negLogDerivL ψ s - 1 / s) ((Real.log Real.pi / 2 : ℝ) : ℂ)
    have h3 := norm_sub_le (-Stage3ZeroFreeRegion.negLogDerivL ψ s) (1 / s)
    rw [norm_neg] at h3
    rw [Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
    dsimp only [C]; nlinarith
  · have hdec := negLogDerivL_eq_neg_logDeriv_completedL_odd ho hψ (by linarith : -1 < s.re) hΛ_ne
    have hld_eq : logDeriv (DirichletCharacter.completedLFunction ψ) s =
        -Stage3ZeroFreeRegion.negLogDerivL ψ s -
          ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
      linear_combination hdec
    have hdig_le : ‖Complex.digamma ((s + 1) / 2)‖ ≤ Cd * Real.log (|t| + 2) := by
      have h1 := hdig ((s + 1) / 2) (by simp [hs_re]; linarith) (by simp [hs_re]; linarith)
      have him : |((s + 1) / 2).im| + 2 ≤ |t| + 2 := by
        have h2 : ((s + 1) / 2).im = t / 2 := by simp [hs_im]
        rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg t]
      exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
    rw [hld_eq]
    have h1 := norm_add_le (-Stage3ZeroFreeRegion.negLogDerivL ψ s - ((Real.log Real.pi / 2 : ℝ) : ℂ))
      ((1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2))
    have h2 := norm_sub_le (-Stage3ZeroFreeRegion.negLogDerivL ψ s) ((Real.log Real.pi / 2 : ℝ) : ℂ)
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
    dsimp only [C]; nlinarith

/-- **UNCONDITIONAL LEFT-VERTICAL LOG-DERIVATIVE BOUND ON `Re(s) = -1 / 2`** for EVERY primitive
`ψ ≠ 1` mod `q`:
`‖negLogDerivL ψ (-1/2 + I * t)‖ ≤ C * Real.log (q * (|t| + 2))`. -/
theorem norm_negLogDerivL_neg_half_line_le_primitive :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ ≠ 1 → ∀ t : ℝ,
        ‖Stage3ZeroFreeRegion.negLogDerivL ψ (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          C * Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨CΛ, hCΛ_pos, hΛ_right⟩ := norm_logDeriv_completedL_right_strip_le
  obtain ⟨Cd, hCd_pos, hdig⟩ := norm_digamma_quarter_strip_le
  have hpi_nn : 0 ≤ Real.log Real.pi / 2 :=
    div_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi])) (by norm_num)
  set C : ℝ := CΛ + Cd + 2 + 2 * (2 + Real.log Real.pi / 2)
  refine ⟨C, by positivity, fun q _ ψ hprim hψ t => ?_⟩
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
  have hlogt_ge : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  have hlog_qt : Real.log ((q : ℝ) * (|t| + 2)) = Real.log (q : ℝ) + Real.log (|t| + 2) :=
    Real.log_mul hq_pos.ne' (by linarith [abs_nonneg t])
  set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)
  have hs_re : s.re = -1 / 2 := by simp [s]
  have hs_im : s.im = t := by simp [s]
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; norm_num at hs_re
  have hΛ_ne : DirichletCharacter.completedLFunction ψ s ≠ 0 :=
    completedLFunction_ne_zero_of_re_le_zero hprim hψ (by linarith)
  -- Reflect `logDeriv Λ_sym` from `-1/2 + I * t` to `1 - conj s = 3/2 + I * t`!
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + I * (t : ℂ)
  have hw_eq : 1 - starRingEnd ℂ s = w := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, hs_re, w, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im,
        mul_zero, sub_self, add_zero]
      norm_num
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, hs_im, w, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re,
        one_mul, zero_add, sub_neg_eq_add]
  have hΛw_ne : DirichletCharacter.completedLFunction ψ w ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hψ (by simp [w]; norm_num)
  have hsym_s_ne : symmetricCompletedLFunction ψ s ≠ 0 :=
    (symmetricCompletedLFunction_eq_zero_iff ψ s).not.mpr hΛ_ne
  have hrefl := Stage8HadamardLFunction.logDeriv_symmetricCompletedLFunction_one_sub_conj hprim hψ hsym_s_ne
  rw [hw_eq, Stage8HadamardLFunction.logDeriv_symmetricCompletedLFunction_eq hψ hΛw_ne,
    Stage8HadamardLFunction.logDeriv_symmetricCompletedLFunction_eq hψ hΛ_ne] at hrefl
  have hld_Λ_s : ‖logDeriv (DirichletCharacter.completedLFunction ψ) s‖ ≤
      (CΛ + 1) * Real.log ((q : ℝ) * (|t| + 2)) := by
    have hsym_w_bd : ‖((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
        logDeriv (DirichletCharacter.completedLFunction ψ) w‖ ≤
        (CΛ + 1 / 2) * Real.log ((q : ℝ) * (|t| + 2)) := by
      have h1 := norm_add_le ((Real.log (q : ℝ) / 2 : ℝ) : ℂ)
        (logDeriv (DirichletCharacter.completedLFunction ψ) w)
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
      have h2 := hΛ_right q ψ hprim hψ (3 / 2) le_rfl (by norm_num) t
      rw [hlog_qt]; nlinarith
    have hsym_s_norm : ‖((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
        logDeriv (DirichletCharacter.completedLFunction ψ) s‖ ≤
        (CΛ + 1 / 2) * Real.log ((q : ℝ) * (|t| + 2)) := by
      have hnorm : ‖((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
          deriv (DirichletCharacter.completedLFunction ψ) s / DirichletCharacter.completedLFunction ψ s‖ =
          ‖((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
          deriv (DirichletCharacter.completedLFunction ψ) w / DirichletCharacter.completedLFunction ψ w‖ := by
        rw [hrefl, norm_neg, Complex.norm_conj]
      simpa only [logDeriv_apply] using hnorm.le.trans hsym_w_bd
    have htri : ‖logDeriv (DirichletCharacter.completedLFunction ψ) s‖ ≤
        ‖((Real.log (q : ℝ) / 2 : ℝ) : ℂ) + logDeriv (DirichletCharacter.completedLFunction ψ) s‖ +
        ‖((Real.log (q : ℝ) / 2 : ℝ) : ℂ)‖ := by
      have h := norm_sub_le (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) +
        logDeriv (DirichletCharacter.completedLFunction ψ) s) ((Real.log (q : ℝ) / 2 : ℝ) : ℂ)
      simpa using h
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at htri
    rw [hlog_qt] at hsym_s_norm ⊢
    nlinarith
  rcases ψ.even_or_odd with he | ho
  · rw [negLogDerivL_eq_neg_logDeriv_completedL_even he hψ (by linarith : -2 < s.re) hs0 hΛ_ne]
    have hinv_s : ‖(1 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div, norm_one]
      have hre : 1 / 2 ≤ ‖s‖ := by
        have h := Complex.abs_re_le_norm s
        rw [hs_re, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num] at h; exact h
      rw [div_le_iff₀ (by linarith)]; linarith
    have hdig_le : ‖Complex.digamma (s / 2 + 1)‖ ≤ Cd * Real.log (|t| + 2) := by
      have h1 := hdig (s / 2 + 1) (by simp [hs_re]; norm_num) (by simp [hs_re]; norm_num)
      have him : |(s / 2 + 1).im| + 2 ≤ |t| + 2 := by
        have h2 : (s / 2 + 1).im = t / 2 := by simp [hs_im]
        rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg t]
      exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
    have h1 := norm_add_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s - 1 / s -
      ((Real.log Real.pi / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
    have h2 := norm_sub_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s - 1 / s)
      ((Real.log Real.pi / 2 : ℝ) : ℂ)
    have h3 := norm_sub_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s) (1 / s)
    rw [norm_neg] at h3
    rw [Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
    rw [hlog_qt] at hld_Λ_s ⊢
    dsimp only [C]; nlinarith
  · rw [negLogDerivL_eq_neg_logDeriv_completedL_odd ho hψ (by linarith : -1 < s.re) hΛ_ne]
    have hdig_le : ‖Complex.digamma ((s + 1) / 2)‖ ≤ Cd * Real.log (|t| + 2) := by
      have h1 := hdig ((s + 1) / 2) (by simp [hs_re]; norm_num) (by simp [hs_re]; norm_num)
      have him : |((s + 1) / 2).im| + 2 ≤ |t| + 2 := by
        have h2 : ((s + 1) / 2).im = t / 2 := by simp [hs_im]
        rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg t]
      exact h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)
    have h1 := norm_add_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s -
      ((Real.log Real.pi / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2))
    have h2 := norm_sub_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s)
      ((Real.log Real.pi / 2 : ℝ) : ℂ)
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
    rw [hlog_qt] at hld_Λ_s ⊢
    dsimp only [C]; nlinarith

/-- Finiteness of the indices `n : ℕ` where `|(completedLZeroSeq hprim hψ n).im| ≤ R`. -/
lemma finite_completedLZeroSeq_abs_im_le {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (R : ℝ) :
    {n : ℕ | |(completedLZeroSeq hprim hψ n).im| ≤ R}.Finite := by
  have ht := Stage5JensenHadamard.tendsto_norm_atTop_of_summable_inv_sq
    (completedLZeroSeq_ne_zero hprim hψ) (completedLZeroSeq_summable_inv_sq hprim hψ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (ht.eventually (Filter.eventually_gt_atTop (max R 0 + 2)))
  refine (Set.finite_Iio N).subset fun n hn => ?_
  by_contra hge
  have hgt := hN n (not_lt.mp hge)
  have hstrip := completedLZeroSeq_strip hprim hψ n
  have htri := Complex.norm_le_abs_re_add_abs_im (completedLZeroSeq hprim hψ n)
  rw [abs_of_pos hstrip.1] at htri
  have hR : |(completedLZeroSeq hprim hψ n).im| ≤ max R 0 := le_trans hn (le_max_left R 0)
  linarith [hstrip.2]

/-- Exact equality between the cardinality of `{n | a ≤ |(completedLZeroSeq hprim hψ n).im| < b}`
(`0 ≤ a ≤ b`) and `lFunctionZeroCount hprim hψ b - lFunctionZeroCount hprim hψ a`. -/
lemma card_completedLZeroSeq_abs_im_Ico_eq {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {a b : ℝ} (hab : a ≤ b) (F : Finset ℕ)
    (hF : ∀ n : ℕ, n ∈ F ↔ a ≤ |(completedLZeroSeq hprim hψ n).im| ∧
      |(completedLZeroSeq hprim hψ n).im| < b) :
    (F.card : ℝ) = lFunctionZeroCount hprim hψ b - lFunctionZeroCount hprim hψ a := by
  classical
  have hsub : lFunctionZeroSet hprim hψ a ⊆ lFunctionZeroSet hprim hψ b := by
    intro ρ hρ
    simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρ ⊢
    exact ⟨⟨hρ.1.1, (hρ.2.le.trans hab).trans (le_max_left b 2)⟩, hρ.2.trans_le hab⟩
  set D : Finset ℂ := lFunctionZeroSet hprim hψ b \ lFunctionZeroSet hprim hψ a
  have hmaps : ∀ n ∈ F, completedLZeroSeq hprim hψ n ∈ D := by
    intro n hn
    obtain ⟨h1, h2⟩ := (hF n).mp hn
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨⟨completedLZeroSeq_zero hprim hψ n, h2.le.trans (le_max_left b 2)⟩, h2⟩
    · simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      rintro ⟨_, hlt⟩; linarith
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hcard_fib : ∀ ρ ∈ D,
      (F.filter fun n => completedLZeroSeq hprim hψ n = ρ).card =
        analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ := by
    intro ρ hρ
    rw [Finset.mem_sdiff] at hρ
    have hρb := hρ.1
    simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hρb
    have hρ_ge : a ≤ |ρ.im| := by
      by_contra hlt
      apply hρ.2
      simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨⟨hρb.1.1, (not_le.mp hlt).le.trans (le_max_left a 2)⟩, not_le.mp hlt⟩
    exact ((isMultiplicityZeroSeq_completedLFunction hprim hψ).2 ρ).2 _ fun n => by
      simp only [Finset.mem_filter, hF]
      exact ⟨fun h => h.2, fun h => ⟨⟨h ▸ hρ_ge, h ▸ hρb.2⟩, h⟩⟩
  have hnat : F.card = ∑ ρ ∈ D, analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ := by
    rw [hfib]; exact Finset.sum_congr rfl hcard_fib
  rw [hnat, Nat.cast_sum]
  unfold lFunctionZeroCount
  rw [Finset.sum_sdiff_eq_sub hsub]

/-- **Multiplicity-Counted Short-Interval Zero-Count Bound for Every Primitive `L(s, ψ)`**:
`∃ C > 0, ∀ q [NeZero q] (ψ : DirichletCharacter ℂ q) hprim hψ (a b : ℝ), 2 ≤ a → a ≤ b → b ≤ a + 6 →
  lFunctionZeroCount hprim hψ b - lFunctionZeroCount hprim hψ a ≤ C * Real.log (q * b)`. -/
lemma lFunctionZeroCount_short_interval_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q)
      (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) (a b : ℝ),
      2 ≤ a → a ≤ b → b ≤ a + 6 →
        lFunctionZeroCount hprim hψ b - lFunctionZeroCount hprim hψ a ≤
          C * Real.log ((q : ℝ) * b) := by
  obtain ⟨C₀, hC₀_pos, hasymp⟩ := Stage8GRHEquivalence.lFunctionZeroCount_asymptotic
  refine ⟨2 * C₀ + 12, by positivity, fun q _ ψ hprim hψ a b ha hab hba => ?_⟩
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  let M : ℝ → ℝ := fun t => (t / Real.pi) * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1))
  have ha_bd := abs_le.mp (hasymp q ψ hprim hψ a ha)
  have hb_bd := abs_le.mp (hasymp q ψ hprim hψ b (ha.trans hab))
  have hlog_ab : Real.log ((q : ℝ) * a) ≤ Real.log ((q : ℝ) * b) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hab hq_pos.le)
  have hlog_qb_nn : 0 ≤ Real.log ((q : ℝ) * b) := Real.log_nonneg (by nlinarith)
  have hM_diff : M b - M a ≤ 12 * Real.log ((q : ℝ) * b) := by
    have hderiv : ∀ u ∈ Set.uIcc a b,
        HasDerivAt M ((1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))) u := by
      intro u hu
      rw [Set.uIcc_of_le hab] at hu
      have hu0 : 0 < u := by linarith [hu.1]
      have h1 : HasDerivAt (fun x : ℝ => x / Real.pi) (1 / Real.pi) u := by
        simpa using (hasDerivAt_id u).div_const Real.pi
      have h2 : HasDerivAt (fun x : ℝ => Real.log ((q : ℝ) * x / (2 * Real.pi * Real.exp 1))) (u⁻¹) u := by
        have hlin : HasDerivAt (fun x : ℝ => (q : ℝ) * x / (2 * Real.pi * Real.exp 1))
            ((q : ℝ) / (2 * Real.pi * Real.exp 1)) u := by
          simpa using ((hasDerivAt_id u).const_mul (q : ℝ)).div_const (2 * Real.pi * Real.exp 1)
        refine (hlin.log (by positivity)).congr_deriv ?_
        field_simp [hq_pos.ne', hu0.ne', Real.pi_pos.ne', (Real.exp_pos 1).ne']
      refine (h1.mul h2).congr_deriv ?_
      have hlog : Real.log ((q : ℝ) * u / (2 * Real.pi * Real.exp 1)) =
          Real.log ((q : ℝ) * u / (2 * Real.pi)) - 1 := by
        rw [show (q : ℝ) * u / (2 * Real.pi * Real.exp 1) = ((q : ℝ) * u / (2 * Real.pi)) / Real.exp 1 by ring,
          Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp]
      rw [hlog]; field_simp [hu0.ne', Real.pi_pos.ne']; ring
    have hcont : ContinuousOn (fun u : ℝ => (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi)))
        (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine continuousOn_const.mul (Real.continuousOn_log.comp
        ((continuousOn_const.mul continuousOn_id).div_const _) fun u hu => ?_)
      have hu0 : 0 < u := by linarith [hu.1]
      exact (by positivity : 0 < (q : ℝ) * u / (2 * Real.pi)).ne'
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have hpt : ∀ u ∈ Set.Icc a b,
        (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi)) ≤ 2 * Real.log ((q : ℝ) * b) := by
      intro u hu
      have hlu : Real.log ((q : ℝ) * u / (2 * Real.pi)) ≤ Real.log ((q : ℝ) * b) := by
        have hqu_pos : 0 < (q : ℝ) * u := mul_pos hq_pos (by linarith [hu.1])
        rw [Real.log_div hqu_pos.ne' (by positivity)]
        have h2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
        linarith [Real.log_le_log hqu_pos (mul_le_mul_of_nonneg_left hu.2 hq_pos.le)]
      have hinv : 1 / Real.pi ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      rcases le_total 0 (Real.log ((q : ℝ) * u / (2 * Real.pi))) with hnn | hnp
      · calc (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))
            ≤ 1 * Real.log ((q : ℝ) * b) := mul_le_mul hinv hlu hnn zero_le_one
          _ ≤ 2 * Real.log ((q : ℝ) * b) := by linarith
      · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp).trans (by linarith)
    calc ∫ u in a..b, (1 / Real.pi) * Real.log ((q : ℝ) * u / (2 * Real.pi))
        ≤ ∫ _u in a..b, (2 * Real.log ((q : ℝ) * b)) :=
          intervalIntegral.integral_mono_on hab hcont.intervalIntegrable intervalIntegrable_const hpt
      _ = (b - a) * (2 * Real.log ((q : ℝ) * b)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ 6 * (2 * Real.log ((q : ℝ) * b)) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ = 12 * Real.log ((q : ℝ) * b) := by ring
  nlinarith

/-- **SHARP ZERO-DENSITY GAP & GOOD HORIZONTAL CONTOUR SELECTION FOR EVERY PRIMITIVE `L(s, ψ)`
(`exists_good_contour_height_primitive`, `0` ASSUMPTIONS!)**:
there exist universal constants `c > 0` and `C > 0` such that for EVERY `q [NeZero q]`,
EVERY primitive `ψ ≠ 1` mod `q`, and EVERY `T ≥ 4`, there exists `T' ∈ [T, T + 1]` at vertical
distance `≥ c / Real.log (q * T)` from ALL zeros of `completedLFunction ψ` (both `+T'` and `-T'`),
on which `‖negLogDerivL ψ (σ ± I * T')‖ ≤ C * (Real.log (q * T)) ^ 2` uniformly for ALL
`-1 / 2 ≤ σ ≤ 2`! -/
theorem exists_good_contour_height_primitive :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
        ψ.IsPrimitive → ψ ≠ 1 → ∀ T : ℝ, 4 ≤ T →
          ∃ T' ∈ Set.Icc T (T + 1),
            (∀ ρ : ℂ, DirichletCharacter.completedLFunction ψ ρ = 0 →
              c / Real.log ((q : ℝ) * T) ≤ |T' - ρ.im| ∧
              c / Real.log ((q : ℝ) * T) ≤ |(-T') - ρ.im|) ∧
            (∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 →
              ‖Stage3ZeroFreeRegion.negLogDerivL ψ ((σ : ℂ) + I * (T' : ℂ))‖ ≤
                C * (Real.log ((q : ℝ) * T)) ^ 2 ∧
              ‖Stage3ZeroFreeRegion.negLogDerivL ψ ((σ : ℂ) - I * (T' : ℂ))‖ ≤
                C * (Real.log ((q : ℝ) * T)) ^ 2) := by
  classical
  obtain ⟨C_N, hCN_pos, hshort⟩ := lFunctionZeroCount_short_interval_le
  obtain ⟨CΛ, hCΛ_pos, hΛ_right⟩ := norm_logDeriv_completedL_right_strip_le
  obtain ⟨Cd, hCd_pos, hdig⟩ := norm_digamma_quarter_strip_le
  set K_N : ℝ := 4 * C_N + 4
  have hKN_pos : 0 < K_N := by positivity
  set c : ℝ := min (1 / (4 * K_N)) (1 / 2)
  have hc_pos : 0 < c := lt_min (by positivity) (by norm_num)
  have hlogpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hpi_nn : 0 ≤ Real.log Real.pi / 2 := div_nonneg hlogpi_nn (by norm_num)
  set C : ℝ := 32 * (CΛ + 1) + 4 * K_N / c + 4 * K_N + 2 * Cd + 4 + Real.log Real.pi
  refine ⟨c, hc_pos, C, by positivity, fun q _ ψ hprim hψ T hT => ?_⟩
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqT_ge8 : (8 : ℝ) ≤ (q : ℝ) * T := by nlinarith
  have hlog_gt1 : 1 < Real.log ((q : ℝ) * T) := by
    have h4 : Real.exp 1 < (q : ℝ) * T := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlog_pos : 0 < Real.log ((q : ℝ) * T) := zero_lt_one.trans hlog_gt1
  have hfin_band : {n : ℕ | T - 1 ≤ |(completedLZeroSeq hprim hψ n).im| ∧
      |(completedLZeroSeq hprim hψ n).im| < T + 3}.Finite :=
    (finite_completedLZeroSeq_abs_im_le hprim hψ (T + 3)).subset fun _ hn => hn.2.le
  set F_band : Finset ℕ := hfin_band.toFinset
  have hF_band_card : (F_band.card : ℝ) ≤ K_N * Real.log ((q : ℝ) * T) := by
    have h1 := card_completedLZeroSeq_abs_im_Ico_eq hprim hψ (a := T - 1) (b := T + 3)
      (by linarith) F_band fun _ => hfin_band.mem_toFinset
    have h2 := hshort q ψ hprim hψ (T - 1) (T + 3) (by linarith) (by linarith) (by linarith)
    have hlog_cmp : Real.log ((q : ℝ) * (T + 3)) ≤ 2 * Real.log ((q : ℝ) * T) := by
      have hsq : (q : ℝ) * (T + 3) ≤ ((q : ℝ) * T) ^ 2 := by nlinarith
      calc Real.log ((q : ℝ) * (T + 3)) ≤ Real.log (((q : ℝ) * T) ^ 2) := Real.log_le_log (by positivity) hsq
        _ = 2 * Real.log ((q : ℝ) * T) := by rw [Real.log_pow]; norm_num
    rw [h1]; dsimp only [K_N]; nlinarith
  set Z_band : Finset ℂ := F_band.image (completedLZeroSeq hprim hψ)
  have hZ_card : Z_band.card ≤ F_band.card := Finset.card_image_le
  obtain ⟨T', hT'_mem, hT'_gap⟩ := Stage5ContourExplicit.exists_good_height_pigeonhole_symm
    (by linarith : 0 ≤ T) Z_band hZ_card
  have hgap_ge : c / Real.log ((q : ℝ) * T) ≤ 1 / (2 * ((F_band.card : ℝ) + 1)) := by
    have hden_le : 2 * ((F_band.card : ℝ) + 1) ≤ 4 * K_N * Real.log ((q : ℝ) * T) := by
      have h1 : (1 : ℝ) ≤ K_N * Real.log ((q : ℝ) * T) := by dsimp only [K_N]; nlinarith
      linarith
    have hc1 : c ≤ 1 / (4 * K_N) := min_le_left _ _
    calc c / Real.log ((q : ℝ) * T)
        ≤ (1 / (4 * K_N)) / Real.log ((q : ℝ) * T) := div_le_div_of_nonneg_right hc1 hlog_pos.le
      _ = 1 / (4 * K_N * Real.log ((q : ℝ) * T)) := div_div 1 (4 * K_N) (Real.log ((q : ℝ) * T))
      _ ≤ 1 / (2 * ((F_band.card : ℝ) + 1)) := div_le_div_of_nonneg_left zero_le_one (by positivity) hden_le
  have hc_div_le1 : c / Real.log ((q : ℝ) * T) ≤ 1 := by
    have hc2 : c ≤ 1 / 2 := min_le_right _ _
    rw [div_le_one hlog_pos]; linarith
  have hgap_all : ∀ ρ : ℂ, DirichletCharacter.completedLFunction ψ ρ = 0 →
      c / Real.log ((q : ℝ) * T) ≤ |T' - ρ.im| ∧ c / Real.log ((q : ℝ) * T) ≤ |(-T') - ρ.im| := by
    intro ρ hρ
    by_cases hband : T - 1 ≤ |ρ.im| ∧ |ρ.im| < T + 3
    · obtain ⟨n, hn⟩ := (isMultiplicityZeroSeq_completedLFunction hprim hψ).exists_of_eq_zero
        (differentiable_completedLFunction_prim hψ) (completedLFunction_zero_ne_zero hprim hψ) hρ
      have hn_mem : n ∈ F_band := hfin_band.mem_toFinset.mpr
        (by change T - 1 ≤ |(completedLZeroSeq hprim hψ n).im| ∧ |(completedLZeroSeq hprim hψ n).im| < T + 3
            rw [hn]; exact hband)
      have hρ_mem : ρ ∈ Z_band := Finset.mem_image.mpr ⟨n, hn_mem, hn⟩
      have hg := hT'_gap ρ hρ_mem
      exact ⟨hgap_ge.trans hg.1, hgap_ge.trans hg.2⟩
    · have hfar : 1 ≤ |T' - (|ρ.im|)| := by
        by_cases h1 : |ρ.im| < T - 1
        · rw [abs_of_pos (by linarith [hT'_mem.1])]; linarith [hT'_mem.1]
        · have h2 : T + 3 ≤ |ρ.im| := by push Not at hband h1; exact hband h1
          rw [abs_of_neg (by linarith [hT'_mem.2])]; linarith [hT'_mem.2]
      have hd1 : 1 ≤ |T' - ρ.im| := hfar.trans (by
        simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T')] using abs_abs_sub_abs_le_abs_sub T' ρ.im)
      have hd2 : 1 ≤ |(-T') - ρ.im| := by
        have hrew : |(-T') - ρ.im| = |T' - (-ρ.im)| := by
          rw [← abs_neg ((-T') - ρ.im)]; congr 1; ring
        rw [hrew]
        exact hfar.trans (by
          simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T'), abs_neg] using
            abs_abs_sub_abs_le_abs_sub T' (-ρ.im))
      exact ⟨hc_div_le1.trans hd1, hc_div_le1.trans hd2⟩
  -- Uniform bound on `‖negLogDerivL ψ (σ + I * y)‖` for `y = ±T'` and `-1 / 2 ≤ σ ≤ 2`
  have hline_bd : ∀ y : ℝ, (y = T' ∨ y = -T') → ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 2 →
      ‖Stage3ZeroFreeRegion.negLogDerivL ψ ((σ : ℂ) + I * (y : ℂ))‖ ≤
        C * (Real.log ((q : ℝ) * T)) ^ 2 := by
    intro y hy σ hσ1 hσ2
    have habs_y : |y| = T' := by
      rcases hy with rfl | rfl
      · exact abs_of_pos (by linarith [hT'_mem.1])
      · rw [abs_neg, abs_of_pos (by linarith [hT'_mem.1])]
    have hy_ge4 : 4 ≤ |y| := by rw [habs_y]; linarith [hT'_mem.1]
    have hy_le : |y| + 2 ≤ ((q : ℝ) * T) ^ 2 := by rw [habs_y]; nlinarith [hT'_mem.2]
    have hlog_y : Real.log (|y| + 2) ≤ 2 * Real.log ((q : ℝ) * T) := by
      calc Real.log (|y| + 2) ≤ Real.log (((q : ℝ) * T) ^ 2) := Real.log_le_log (by positivity) hy_le
        _ = 2 * Real.log ((q : ℝ) * T) := by rw [Real.log_pow]; norm_num
    set s : ℂ := (σ : ℂ) + I * (y : ℂ)
    set s₀ : ℂ := (2 : ℂ) + I * (y : ℂ)
    have hs_re : s.re = σ := by simp [s]
    have hs_im : s.im = y := by simp [s]
    have hs0 : s ≠ 0 := fun h => by
      have := congrArg Complex.im h; simp [hs_im] at this; rw [this, abs_zero] at hy_ge4; linarith
    have hgap_y : ∀ n : ℕ, c / Real.log ((q : ℝ) * T) ≤ |y - (completedLZeroSeq hprim hψ n).im| := fun n => by
      have hg := hgap_all (completedLZeroSeq hprim hψ n) (completedLZeroSeq_zero hprim hψ n)
      rcases hy with rfl | rfl
      · exact hg.1
      · exact hg.2
    have hΛ_s : DirichletCharacter.completedLFunction ψ s ≠ 0 := fun h0 => by
      obtain ⟨n, hn⟩ := (isMultiplicityZeroSeq_completedLFunction hprim hψ).exists_of_eq_zero
        (differentiable_completedLFunction_prim hψ) (completedLFunction_zero_ne_zero hprim hψ) h0
      have hg := hgap_y n
      rw [hn, hs_im, sub_self, abs_zero] at hg
      have : 0 < c / Real.log ((q : ℝ) * T) := div_pos hc_pos hlog_pos
      linarith
    have hΛ_s₀ : DirichletCharacter.completedLFunction ψ s₀ ≠ 0 :=
      completedLFunction_ne_zero_of_one_le_re hψ (by simp [s₀])
    have hld_s₀ : ‖logDeriv (DirichletCharacter.completedLFunction ψ) s₀‖ ≤
        2 * CΛ * Real.log ((q : ℝ) * T) := by
      have h1 := hΛ_right q ψ hprim hψ 2 (by norm_num) le_rfl y
      have hs₀_eq : ((2 : ℝ) : ℂ) + I * (y : ℂ) = s₀ := by simp [s₀]
      rw [hs₀_eq] at h1
      exact (h1.trans (mul_le_mul_of_nonneg_left hlog_y hCΛ_pos.le)).trans_eq (by ring)
    have hs_ne : ∀ n : ℕ, s ≠ completedLZeroSeq hprim hψ n := fun n h => hΛ_s (h ▸ completedLZeroSeq_zero hprim hψ n)
    have hs₀_ne : ∀ n : ℕ, s₀ ≠ completedLZeroSeq hprim hψ n := fun n h => hΛ_s₀ (h ▸ completedLZeroSeq_zero hprim hψ n)
    have hsumm_s := Stage5JensenHadamard.summable_hadamard_term
      (completedLZeroSeq_ne_zero hprim hψ) (completedLZeroSeq_summable_inv_sq hprim hψ) hs_ne
    have hsumm_s₀ := Stage5JensenHadamard.summable_hadamard_term
      (completedLZeroSeq_ne_zero hprim hψ) (completedLZeroSeq_summable_inv_sq hprim hψ) hs₀_ne
    have hdiff_eq : logDeriv (DirichletCharacter.completedLFunction ψ) s -
        logDeriv (DirichletCharacter.completedLFunction ψ) s₀ =
        ∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n)) := by
      rw [logDeriv_apply, logDeriv_apply,
        completedLFunction_logDeriv_hadamard hprim hψ s hΛ_s,
        completedLFunction_logDeriv_hadamard hprim hψ s₀ hΛ_s₀]
      have hsub : (completedLHadamardB ψ + ∑' n, (1 / (s - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) -
          (completedLHadamardB ψ + ∑' n, (1 / (s₀ - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) =
          (∑' n, (1 / (s - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) -
          (∑' n, (1 / (s₀ - completedLZeroSeq hprim hψ n) + 1 / completedLZeroSeq hprim hψ n)) := by ring
      rw [hsub, ← hsumm_s.tsum_sub hsumm_s₀]
      exact tsum_congr fun n => by ring
    have hre_summ : Summable (fun n : ℕ => (1 / (s₀ - completedLZeroSeq hprim hψ n)).re) :=
      Stage5JensenHadamard.summable_re_inv_sub_of_strip
        (completedLZeroSeq_strip hprim hψ) (completedLZeroSeq_summable_inv_sq hprim hψ) hs₀_ne
    have hre_pos : ∀ n : ℕ, 0 < (1 / (s₀ - completedLZeroSeq hprim hψ n)).re := fun n =>
      Stage5JensenHadamard.re_inv_sub_pos_of_strip
        (completedLZeroSeq_strip hprim hψ n).1 (completedLZeroSeq_strip hprim hψ n).2 (by simp [s₀])
    have hfar_term : ∀ n : ℕ, n ∉ F_band →
        ‖1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n)‖ ≤
          15 * (1 / (s₀ - completedLZeroSeq hprim hψ n)).re := by
      intro n hn
      have hnot_band : ¬ (T - 1 ≤ |(completedLZeroSeq hprim hψ n).im| ∧ |(completedLZeroSeq hprim hψ n).im| < T + 3) :=
        fun h => hn (hfin_band.mem_toFinset.mpr h)
      have hdist1 : 1 ≤ |y - (completedLZeroSeq hprim hψ n).im| := by
        have hfar : 1 ≤ |T' - (|(completedLZeroSeq hprim hψ n).im|)| := by
          by_cases h1 : |(completedLZeroSeq hprim hψ n).im| < T - 1
          · rw [abs_of_pos (by linarith [hT'_mem.1])]; linarith [hT'_mem.1]
          · have h2 : T + 3 ≤ |(completedLZeroSeq hprim hψ n).im| := by push Not at hnot_band h1; exact hnot_band h1
            rw [abs_of_neg (by linarith [hT'_mem.2])]; linarith [hT'_mem.2]
        rcases hy with hy1 | hy2
        · rw [hy1]
          exact hfar.trans (by
            simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T')] using
              abs_abs_sub_abs_le_abs_sub T' (completedLZeroSeq hprim hψ n).im)
        · rw [hy2]
          have hrew : |(-T') - (completedLZeroSeq hprim hψ n).im| =
              |T' - (-(completedLZeroSeq hprim hψ n).im)| := by
            rw [← abs_neg ((-T') - (completedLZeroSeq hprim hψ n).im)]; congr 1; ring
          rw [hrew]
          exact hfar.trans (by
            simpa [abs_of_nonneg (by linarith [hT'_mem.1] : 0 ≤ T'), abs_neg] using
              abs_abs_sub_abs_le_abs_sub T' (-(completedLZeroSeq hprim hψ n).im))
      have hsub_ne1 : s - completedLZeroSeq hprim hψ n ≠ 0 := sub_ne_zero.mpr (hs_ne n)
      have hsub_ne2 : s₀ - completedLZeroSeq hprim hψ n ≠ 0 := sub_ne_zero.mpr (hs₀_ne n)
      have hident : 1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n) =
          (s₀ - s) / ((s - completedLZeroSeq hprim hψ n) * (s₀ - completedLZeroSeq hprim hψ n)) := by
        field_simp [hsub_ne1, hsub_ne2]; ring
      rw [hident, norm_div, norm_mul]
      have hs0s_norm : ‖s₀ - s‖ ≤ 3 := by
        have hdiff : s₀ - s = ((2 - σ : ℝ) : ℂ) := Complex.ext (by simp [s, s₀]) (by simp [s, s₀])
        rw [hdiff, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
      have hd_s : |y - (completedLZeroSeq hprim hψ n).im| ≤ ‖s - completedLZeroSeq hprim hψ n‖ := by
        simpa [s] using Complex.abs_im_le_norm (s - completedLZeroSeq hprim hψ n)
      have hd_s0 : |y - (completedLZeroSeq hprim hψ n).im| ≤ ‖s₀ - completedLZeroSeq hprim hψ n‖ := by
        simpa [s₀] using Complex.abs_im_le_norm (s₀ - completedLZeroSeq hprim hψ n)
      have hsq_pos : 0 < |y - (completedLZeroSeq hprim hψ n).im| ^ 2 := by positivity
      have hprod_ge : |y - (completedLZeroSeq hprim hψ n).im| ^ 2 ≤
          ‖s - completedLZeroSeq hprim hψ n‖ * ‖s₀ - completedLZeroSeq hprim hψ n‖ := by
        rw [sq]; exact mul_le_mul hd_s hd_s0 (abs_nonneg _) (norm_nonneg _)
      have hst := completedLZeroSeq_strip hprim hψ n
      have hre_lb : 1 / (5 * |y - (completedLZeroSeq hprim hψ n).im| ^ 2) ≤
          (1 / (s₀ - completedLZeroSeq hprim hψ n)).re := by
        rw [Stage5JensenHadamard.re_inv_sub_eq]
        have hs₀_re : s₀.re = 2 := by simp [s₀]
        have hs₀_im : s₀.im = y := by simp [s₀]
        rw [hs₀_re, hs₀_im]
        have hnum_ge1 : (1 : ℝ) ≤ 2 - (completedLZeroSeq hprim hψ n).re := by linarith [hst.2]
        have hden_le : (2 - (completedLZeroSeq hprim hψ n).re) ^ 2 +
            (y - (completedLZeroSeq hprim hψ n).im) ^ 2 ≤
            5 * |y - (completedLZeroSeq hprim hψ n).im| ^ 2 := by
          rw [sq_abs]
          have h1 : (2 - (completedLZeroSeq hprim hψ n).re) ^ 2 ≤ 4 := by nlinarith [hst.1, hst.2]
          have h2 : (1 : ℝ) ≤ (y - (completedLZeroSeq hprim hψ n).im) ^ 2 := by rw [← sq_abs]; nlinarith
          linarith
        exact div_le_div₀ (by positivity) hnum_ge1 (by positivity) hden_le
      calc ‖s₀ - s‖ / (‖s - completedLZeroSeq hprim hψ n‖ * ‖s₀ - completedLZeroSeq hprim hψ n‖)
          ≤ 3 / |y - (completedLZeroSeq hprim hψ n).im| ^ 2 := div_le_div₀ (by norm_num) hs0s_norm hsq_pos hprod_ge
        _ = 15 * (1 / (5 * |y - (completedLZeroSeq hprim hψ n).im| ^ 2)) := by ring
        _ ≤ 15 * (1 / (s₀ - completedLZeroSeq hprim hψ n)).re := mul_le_mul_of_nonneg_left hre_lb (by norm_num)
    have hnear_term : ∀ n ∈ F_band,
        ‖1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n)‖ ≤
          Real.log ((q : ℝ) * T) / c + 1 := by
      intro n _
      have h1 : ‖(1 : ℂ) / (s - completedLZeroSeq hprim hψ n)‖ ≤ Real.log ((q : ℝ) * T) / c := by
        rw [norm_div, norm_one]
        have hd : c / Real.log ((q : ℝ) * T) ≤ ‖s - completedLZeroSeq hprim hψ n‖ :=
          (hgap_y n).trans (by simpa [s] using Complex.abs_im_le_norm (s - completedLZeroSeq hprim hψ n))
        calc 1 / ‖s - completedLZeroSeq hprim hψ n‖
            ≤ 1 / (c / Real.log ((q : ℝ) * T)) :=
              div_le_div_of_nonneg_left zero_le_one (div_pos hc_pos hlog_pos) hd
          _ = Real.log ((q : ℝ) * T) / c := one_div_div c (Real.log ((q : ℝ) * T))
      have h2 : ‖(1 : ℂ) / (s₀ - completedLZeroSeq hprim hψ n)‖ ≤ 1 := by
        rw [norm_div, norm_one]
        have hd : 1 ≤ ‖s₀ - completedLZeroSeq hprim hψ n‖ := by
          have h := Complex.abs_re_le_norm (s₀ - completedLZeroSeq hprim hψ n)
          have hr : (s₀ - completedLZeroSeq hprim hψ n).re = 2 - (completedLZeroSeq hprim hψ n).re := by simp [s₀]
          rw [hr, abs_of_pos (by linarith [(completedLZeroSeq_strip hprim hψ n).2])] at h
          linarith [(completedLZeroSeq_strip hprim hψ n).2]
        exact div_le_one_of_le₀ hd (norm_nonneg _)
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hsumm_norm : Summable (fun n : ℕ =>
        ‖1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n)‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
        ((hre_summ.mul_left 15).add (summable_of_ne_finset_zero (s := F_band)
          (f := fun n => if n ∈ F_band then Real.log ((q : ℝ) * T) / c + 1 else 0) (fun n hn => by simp [hn])))
      by_cases hn : n ∈ F_band
      · simp only [hn, ↓reduceIte]; linarith [hnear_term n hn, hre_pos n]
      · simp only [hn, ↓reduceIte, add_zero]; exact hfar_term n hn
    have htsum_bd : ‖∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hψ n) -
        1 / (s₀ - completedLZeroSeq hprim hψ n))‖ ≤
        (F_band.card : ℝ) * (Real.log ((q : ℝ) * T) / c + 1) +
        15 * (deriv (symmetricCompletedLFunction ψ) s₀ / symmetricCompletedLFunction ψ s₀).re := by
      let u : ℕ → ℝ := fun n =>
        ‖1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n)‖
      let v : ℕ → ℝ := fun n => (1 / (s₀ - completedLZeroSeq hprim hψ n)).re
      have hu_summ : Summable u := hsumm_norm
      have hv_summ : Summable v := hre_summ
      have hsplit : (∑ n ∈ F_band, u n) + ∑' x : {n // n ∉ F_band}, u x.1 = ∑' n : ℕ, u n :=
        hu_summ.sum_add_tsum_compl (s := F_band)
      have hnear_sum : ∑ n ∈ F_band, u n ≤
          (F_band.card : ℝ) * (Real.log ((q : ℝ) * T) / c + 1) := by
        calc ∑ n ∈ F_band, u n
            ≤ ∑ _n ∈ F_band, (Real.log ((q : ℝ) * T) / c + 1) := Finset.sum_le_sum hnear_term
          _ = (F_band.card : ℝ) * (Real.log ((q : ℝ) * T) / c + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      have hfar_sum : ∑' x : {n // n ∉ F_band}, u x.1 ≤
          15 * (deriv (symmetricCompletedLFunction ψ) s₀ / symmetricCompletedLFunction ψ s₀).re := by
        have hu_sub : Summable (fun x : {n // n ∉ F_band} => u x.1) := hu_summ.subtype _
        have hv_sub : Summable (fun x : {n // n ∉ F_band} => 15 * v x.1) := (hv_summ.mul_left 15).subtype _
        have h1 : ∑' x : {n // n ∉ F_band}, u x.1 ≤ ∑' x : {n // n ∉ F_band}, 15 * v x.1 :=
          hu_sub.tsum_le_tsum (fun x => hfar_term x.1 x.2) hv_sub
        have h2 : ∑' x : {n // n ∉ F_band}, v x.1 ≤ ∑' n : ℕ, v n := by
          have hsp : (∑ n ∈ F_band, v n) + ∑' x : {n // n ∉ F_band}, v x.1 = ∑' n : ℕ, v n :=
            hv_summ.sum_add_tsum_compl (s := F_band)
          have hnn : 0 ≤ ∑ n ∈ F_band, v n := Finset.sum_nonneg fun n _ => (hre_pos n).le
          linarith
        rw [tsum_mul_left] at h1
        have hsym_eq : (deriv (symmetricCompletedLFunction ψ) s₀ / symmetricCompletedLFunction ψ s₀).re =
            ∑' n : ℕ, v n := symmetricCompletedLFunction_re_logDeriv_eq_tsum hprim hψ (by simp [s₀])
        linarith
      calc ‖∑' n : ℕ, (1 / (s - completedLZeroSeq hprim hψ n) - 1 / (s₀ - completedLZeroSeq hprim hψ n))‖
          ≤ ∑' n : ℕ, u n := norm_tsum_le_tsum_norm hu_summ
        _ = (∑ n ∈ F_band, u n) + ∑' x : {n // n ∉ F_band}, u x.1 := hsplit.symm
        _ ≤ (F_band.card : ℝ) * (Real.log ((q : ℝ) * T) / c + 1) +
            15 * (deriv (symmetricCompletedLFunction ψ) s₀ / symmetricCompletedLFunction ψ s₀).re :=
          add_le_add hnear_sum hfar_sum
    have hre_sym_s₀ : (deriv (symmetricCompletedLFunction ψ) s₀ / symmetricCompletedLFunction ψ s₀).re ≤
        2 * (CΛ + 1) * Real.log ((q : ℝ) * T) := by
      rw [Stage8HadamardLFunction.logDeriv_symmetricCompletedLFunction_eq hψ hΛ_s₀,
        Complex.add_re, Complex.ofReal_re]
      have h1 : (deriv (DirichletCharacter.completedLFunction ψ) s₀ /
          DirichletCharacter.completedLFunction ψ s₀).re ≤ 2 * CΛ * Real.log ((q : ℝ) * T) := by
        have h := (le_abs_self _).trans (Complex.abs_re_le_norm (logDeriv (DirichletCharacter.completedLFunction ψ) s₀))
        rw [logDeriv_apply] at h; exact h.trans hld_s₀
      have hlogq_le : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * T) :=
        Real.log_le_log hq_pos (by nlinarith)
      linarith
    have hld_Λ_s : ‖logDeriv (DirichletCharacter.completedLFunction ψ) s‖ ≤
        (32 * (CΛ + 1) + K_N / c + K_N) * (Real.log ((q : ℝ) * T)) ^ 2 := by
      have htri : ‖logDeriv (DirichletCharacter.completedLFunction ψ) s‖ ≤
          ‖logDeriv (DirichletCharacter.completedLFunction ψ) s -
            logDeriv (DirichletCharacter.completedLFunction ψ) s₀‖ +
          ‖logDeriv (DirichletCharacter.completedLFunction ψ) s₀‖ := by
        simpa [sub_add_cancel] using norm_add_le
          (logDeriv (DirichletCharacter.completedLFunction ψ) s -
            logDeriv (DirichletCharacter.completedLFunction ψ) s₀)
          (logDeriv (DirichletCharacter.completedLFunction ψ) s₀)
      rw [hdiff_eq] at htri
      have hF_mul : (F_band.card : ℝ) * (Real.log ((q : ℝ) * T) / c + 1) ≤
          (K_N / c + K_N) * (Real.log ((q : ℝ) * T)) ^ 2 := by
        have h1 : (F_band.card : ℝ) * (Real.log ((q : ℝ) * T) / c + 1) ≤
            (K_N * Real.log ((q : ℝ) * T)) * (Real.log ((q : ℝ) * T) / c + Real.log ((q : ℝ) * T)) :=
          mul_le_mul hF_band_card (by linarith) (by positivity) (by positivity)
        linarith [show (K_N * Real.log ((q : ℝ) * T)) * (Real.log ((q : ℝ) * T) / c + Real.log ((q : ℝ) * T)) =
          (K_N / c + K_N) * (Real.log ((q : ℝ) * T)) ^ 2 by ring]
      have hlog_sq : Real.log ((q : ℝ) * T) ≤ (Real.log ((q : ℝ) * T)) ^ 2 := by nlinarith
      nlinarith
    have hlog_sq1 : (1 : ℝ) ≤ (Real.log ((q : ℝ) * T)) ^ 2 := by nlinarith
    have hlog_sq : Real.log ((q : ℝ) * T) ≤ (Real.log ((q : ℝ) * T)) ^ 2 := by nlinarith
    have hK_div : 0 ≤ K_N / c := div_nonneg hKN_pos.le hc_pos.le
    have hA : (32 * (CΛ + 1) + K_N / c + K_N) * (Real.log ((q : ℝ) * T)) ^ 2 ≤
        (32 * (CΛ + 1) + 4 * K_N / c + 4 * K_N) * (Real.log ((q : ℝ) * T)) ^ 2 := by
      have hcoef : 32 * (CΛ + 1) + K_N / c + K_N ≤ 32 * (CΛ + 1) + 4 * K_N / c + 4 * K_N := by
        have h4 : 4 * K_N / c = 4 * (K_N / c) := by ring
        linarith
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    rcases ψ.even_or_odd with he | ho
    · rw [negLogDerivL_eq_neg_logDeriv_completedL_even he hψ (by linarith : -2 < s.re) hs0 hΛ_s]
      have hinv_s : ‖(1 : ℂ) / s‖ ≤ 1 := by
        rw [norm_div, norm_one]
        have h1 : 4 ≤ ‖s‖ := hy_ge4.trans (by simpa [hs_im] using Complex.abs_im_le_norm s)
        rw [div_le_one (by linarith)]; linarith
      have hdig_le : ‖Complex.digamma (s / 2 + 1)‖ ≤ 2 * Cd * Real.log ((q : ℝ) * T) := by
        have h1 := hdig (s / 2 + 1) (by simp [hs_re]; linarith) (by simp [hs_re]; linarith)
        have him : |(s / 2 + 1).im| + 2 ≤ |y| + 2 := by
          have h2 : (s / 2 + 1).im = y / 2 := by simp [hs_im]
          rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg y]
        exact (h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)).trans
          (by nlinarith)
      have h1 := norm_add_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s - 1 / s -
        ((Real.log Real.pi / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
      have h2 := norm_sub_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s - 1 / s)
        ((Real.log Real.pi / 2 : ℝ) : ℂ)
      have h3 := norm_sub_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s) (1 / s)
      rw [norm_neg] at h3
      rw [Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
      have hB : 1 + Real.log Real.pi / 2 + (1 / 2) * (2 * Cd * Real.log ((q : ℝ) * T)) ≤
          (2 * Cd + 4 + Real.log Real.pi) * (Real.log ((q : ℝ) * T)) ^ 2 := by
        nlinarith [hCd_pos, hpi_nn, hlog_sq1, hlog_sq]
      dsimp only [C]; linarith
    · rw [negLogDerivL_eq_neg_logDeriv_completedL_odd ho hψ (by linarith : -1 < s.re) hΛ_s]
      have hdig_le : ‖Complex.digamma ((s + 1) / 2)‖ ≤ 2 * Cd * Real.log ((q : ℝ) * T) := by
        have h1 := hdig ((s + 1) / 2) (by simp [hs_re]; linarith) (by simp [hs_re]; linarith)
        have him : |((s + 1) / 2).im| + 2 ≤ |y| + 2 := by
          have h2 : ((s + 1) / 2).im = y / 2 := by simp [hs_im]
          rw [h2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [abs_nonneg y]
        exact (h1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him) hCd_pos.le)).trans
          (by nlinarith)
      have h1 := norm_add_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s -
        ((Real.log Real.pi / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2))
      have h2 := norm_sub_le (-logDeriv (DirichletCharacter.completedLFunction ψ) s)
        ((Real.log Real.pi / 2 : ℝ) : ℂ)
      rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hpi_nn] at h2
      rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at h1
      have hB : Real.log Real.pi / 2 + (1 / 2) * (2 * Cd * Real.log ((q : ℝ) * T)) ≤
          (2 * Cd + 4 + Real.log Real.pi) * (Real.log ((q : ℝ) * T)) ^ 2 := by
        nlinarith [hCd_pos, hpi_nn, hlog_sq1, hlog_sq]
      dsimp only [C]; linarith
  refine ⟨T', hT'_mem, hgap_all, fun σ hσ1 hσ2 => ?_⟩
  refine ⟨hline_bd T' (Or.inl rfl) σ hσ1 hσ2, ?_⟩
  have hneg : (σ : ℂ) - I * (T' : ℂ) = (σ : ℂ) + I * ((-T' : ℝ) : ℂ) := by push_cast; ring
  rw [hneg]
  exact hline_bd (-T') (Or.inr rfl) σ hσ1 hσ2

/-! ## Section 2: Unified Zero Box, Entire Tent Kernel `dyadicKernel`, & Smoothed Dyadic Explicit Formulas -/

/-- Finiteness of all critical-strip zeros of `DirichletCharacter.LFunction χ` with `|ρ.im| ≤ T`. -/
lemma finite_LFunction_zeros_in_box {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0 ∧ |ρ.im| ≤ T}.Finite := by
  by_cases hχ : χ = 1
  · subst hχ
    refine (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).subset fun ρ hρ => ?_
    have hρ1 : ρ ≠ 1 := fun h => by have hre := hρ.2.1; rw [h, Complex.one_re] at hre; linarith
    exact ⟨hρ.1, hρ.2.1,
      (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos m hρ.1 hρ1).mp hρ.2.2.1,
      hρ.2.2.2⟩
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψ_ne1 : χ.primitiveCharacter ≠ 1 := fun h1 => hχ (by
      rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
    refine (Stage8HadamardLFunction.finite_completedLFunction_zeros_le_height
      χ.primitiveCharacter_isPrimitive hψ_ne1 (le_max_right T 2)).subset fun ρ hρ => ?_
    have hLψ : DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 :=
      (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ hρ.1 (.inl hχ)).mp hρ.2.2.1
    exact ⟨(completedLFunction_eq_zero_iff_LFunction_of_re_pos χ.primitiveCharacter hρ.1).mpr hLψ,
      hρ.2.2.2.trans (le_max_left T 2)⟩

/-- Finite set of all critical-strip zeros of `DirichletCharacter.LFunction χ` with `|ρ.im| ≤ T`. -/
def lZerosInBox {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (T : ℝ) : Finset ℂ :=
  (finite_LFunction_zeros_in_box χ T).toFinset

/-- Analytic multiplicity of a critical-strip zero of `DirichletCharacter.LFunction χ`. -/
def lZeroMult {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

lemma mem_lZerosInBox {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} {T : ℝ} {ρ : ℂ} :
    ρ ∈ lZerosInBox χ T ↔
      0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0 ∧ |ρ.im| ≤ T :=
  (finite_LFunction_zeros_in_box χ T).mem_toFinset

lemma lZerosInBox_mono {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) :
    lZerosInBox χ T₁ ⊆ lZerosInBox χ T₂ := fun _ hρ => by
  have hm := mem_lZerosInBox.mp hρ
  exact mem_lZerosInBox.mpr ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.trans hT⟩

lemma lZerosInBox_one_eq_zetaZerosInBox (m : ℕ) [NeZero m] (T : ℝ) :
    lZerosInBox (1 : DirichletCharacter ℂ m) T = Stage9ExplicitFormula.zetaZerosInBox T := by
  ext ρ
  simp only [mem_lZerosInBox, Stage9ExplicitFormula.zetaZerosInBox, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, hz, him⟩
    have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; linarith
    exact ⟨h0, h1, (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos m h0 hne1).mp hz, him⟩
  · rintro ⟨h0, h1, hz, him⟩
    have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; linarith
    exact ⟨h0, h1, (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos m h0 hne1).mpr hz, him⟩

lemma lZerosInBox_eq_primitive {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1) (T : ℝ) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    lZerosInBox χ T = lZerosInBox χ.primitiveCharacter T := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  ext ρ
  simp only [mem_lZerosInBox]
  constructor
  · rintro ⟨h0, h1, hz, him⟩
    exact ⟨h0, h1, (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ)).mp hz, him⟩
  · rintro ⟨h0, h1, hz, him⟩
    exact ⟨h0, h1, (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ h0 (.inl hχ)).mpr hz, him⟩

/-- Helper: analytic order of `f * g` at `ρ` equals analytic order of `f` when `g` is analytic and
nonvanishing at `ρ`. -/
private lemma analyticOrderNatAt_mul_of_ne_zero {f g : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticAt ℂ f ρ) (hg : AnalyticAt ℂ g ρ) (hg_ne : g ρ ≠ 0) :
    analyticOrderNatAt (fun z => f z * g z) ρ = analyticOrderNatAt f ρ := by
  by_cases htop : analyticOrderAt f ρ = ⊤
  · have hfg_top : analyticOrderAt (fun z => f z * g z) ρ = ⊤ := by
      rw [analyticOrderAt_eq_top] at htop ⊢
      filter_upwards [htop] with z hz; simp [hz]
    simp only [analyticOrderNatAt, htop, hfg_top]
  · obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := hf.analyticOrderAt_ne_top.mp htop
    have hfg_an : AnalyticAt ℂ (fun z => f z * g z) ρ := hf.mul hg
    have hfg_eq : (fun z => f z * g z) =ᶠ[𝓝 ρ]
        fun z => (z - ρ) ^ analyticOrderNatAt f ρ • (h z * g z) := by
      filter_upwards [hh_eq] with z hz
      simp only [smul_eq_mul] at hz ⊢
      rw [hz]; ring
    have hord : analyticOrderAt (fun z => f z * g z) ρ = (analyticOrderNatAt f ρ : ℕ∞) :=
      hfg_an.analyticOrderAt_eq_natCast.mpr ⟨fun z => h z * g z, hh_an.mul hg, mul_ne_zero hh_ne hg_ne, hfg_eq⟩
    simp only [analyticOrderNatAt, hord, ENat.toNat_natCast]

/-- Helper: the finite Euler factor product `∏_{p ∈ m.primeFactors} (1 - ψ p * p^(-z))` is entire. -/
private lemma analyticAt_eulerFactorProd {d m : ℕ} [NeZero d] (ψ : DirichletCharacter ℂ d) (ρ : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ∏ p ∈ m.primeFactors, (1 - ψ (p : ZMod d) * (p : ℂ) ^ (-z))) ρ := by
  have hdiff : Differentiable ℂ (fun z : ℂ => ∏ p ∈ m.primeFactors, (1 - ψ (p : ZMod d) * (p : ℂ) ^ (-z))) := by
    intro z
    refine DifferentiableAt.fun_finsetProd fun p hp => ?_
    have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hpow : (fun w : ℂ => (p : ℂ) ^ (-w)) = fun w => cexp (Complex.log (p : ℂ) * (-w)) :=
      funext fun w => Complex.cpow_def_of_ne_zero hp_ne (-w)
    have hpow_d : DifferentiableAt ℂ (fun w : ℂ => (p : ℂ) ^ (-w)) z := by rw [hpow]; fun_prop
    exact (differentiableAt_const 1).sub ((differentiableAt_const _).mul hpow_d)
  exact hdiff.differentiableOn.analyticAt Filter.univ_mem

/-- For principal `1 mod m` and `0 < ρ.re < 1`, `lZeroMult 1 ρ = analyticOrderNatAt xi ρ`. -/
lemma lZeroMult_one_eq_xi (m : ℕ) [NeZero m] {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    lZeroMult (1 : DirichletCharacter ℂ m) ρ = analyticOrderNatAt xi ρ := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; linarith
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; linarith
  have hopen : IsOpen ({z : ℂ | 0 < z.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev_L : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m) =ᶠ[𝓝 ρ]
      fun z => riemannZeta z * ∏ p ∈ m.primeFactors, (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-z)) := by
    filter_upwards [hopen.mem_nhds ⟨h0, hρ1⟩] with z hz
    have h := DirichletCharacter.LFunction_changeLevel m.one_dvd (1 : DirichletCharacter ℂ 1) (.inr hz.2)
    rw [map_one, DirichletCharacter.LFunction_modOne_eq] at h
    exact h
  have hZ_an : AnalyticAt ℂ riemannZeta ρ :=
    ((differentiableOn_riemannZeta).analyticOnNhd isOpen_compl_singleton) ρ hρ1
  have hE_an := analyticAt_eulerFactorProd (m := m) (1 : DirichletCharacter ℂ 1) ρ
  have hE_ne := RHDirect.eulerFactorProd_ne_zero_of_re_pos (N := m) (1 : DirichletCharacter ℂ 1) h0
  have hord1 : lZeroMult (1 : DirichletCharacter ℂ m) ρ = analyticOrderNatAt riemannZeta ρ := by
    unfold lZeroMult
    have heq : analyticOrderAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m)) ρ =
        analyticOrderAt (fun z => riemannZeta z *
          ∏ p ∈ m.primeFactors, (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-z))) ρ :=
      analyticOrderAt_congr hev_L
    simp only [analyticOrderNatAt, heq]
    exact analyticOrderNatAt_mul_of_ne_zero hZ_an hE_an hE_ne
  have hopen2 : IsOpen ({z : ℂ | -2 < z.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  let g : ℂ → ℂ := fun z => 2 * (z - 1) * (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2 + 1)
  have hev_xi : xi =ᶠ[𝓝 ρ] fun z => riemannZeta z * g z := by
    filter_upwards [hopen2.mem_nhds ⟨show -2 < ρ.re by linarith, hρ1⟩] with z hz
    rw [Stage9ExplicitFormula.xi_eq_two_mul_sub_one_mul_Gamma_add_one_mul_riemannZeta hz.1 hz.2]
    dsimp only [g]; ring
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hg_an : AnalyticAt ℂ g ρ := by
    have hopen3 : IsOpen {z : ℂ | -2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticAt ?_ (hopen3.mem_nhds (show -2 < ρ.re by linarith))
    intro z hz
    have hz_re : -2 < z.re := hz
    have hpow : (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) = fun w => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) :=
      funext fun w => Complex.cpow_def_of_ne_zero hpiC (-w / 2)
    have hpow_d : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) z := by rw [hpow]; fun_prop
    have hG_d : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2 + 1)) z :=
      (Complex.differentiableAt_Gamma (z / 2 + 1) fun k hEq => by
        have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
        ((differentiableAt_id.div_const 2).add (differentiableAt_const 1))
    exact (((differentiableAt_const 2).mul (differentiableAt_id.sub (differentiableAt_const 1))).mul hpow_d |>.mul hG_d).differentiableWithinAt
  have hg_ne : g ρ ≠ 0 := by
    dsimp only [g]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hρ1)) ?_) ?_
    · rw [Complex.cpow_def_of_ne_zero hpiC]; exact Complex.exp_ne_zero _
    · exact Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hord2 : analyticOrderNatAt xi ρ = analyticOrderNatAt riemannZeta ρ := by
    have heq : analyticOrderAt xi ρ = analyticOrderAt (fun z => riemannZeta z * g z) ρ :=
      analyticOrderAt_congr hev_xi
    simp only [analyticOrderNatAt, heq]
    exact analyticOrderNatAt_mul_of_ne_zero hZ_an hg_an hg_ne
  rw [hord1, hord2]

/-- For any non-principal `χ ≠ 1` mod `m` and `0 < ρ.re < 1`,
`lZeroMult χ ρ = analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ`. -/
lemma lZeroMult_eq_primitive {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1)
    {ρ : ℂ} (h0 : 0 < ρ.re) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    lZeroMult χ ρ = analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ_ne1 : χ.primitiveCharacter ≠ 1 := fun h1 => hχ (by
    rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
  have hLψ_an : AnalyticAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) ρ :=
    ((DirichletCharacter.differentiable_LFunction hψ_ne1).differentiableOn.analyticOnNhd isOpen_univ) ρ (Set.mem_univ ρ)
  have hE_an := analyticAt_eulerFactorProd (m := m) χ.primitiveCharacter ρ
  have hE_ne := RHDirect.eulerFactorProd_ne_zero_of_re_pos (N := m) χ.primitiveCharacter h0
  have hev_L : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ]
      fun z => DirichletCharacter.LFunction χ.primitiveCharacter z *
        ∏ p ∈ m.primeFactors, (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z)) := by
    filter_upwards [Filter.univ_mem] with z _
    have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inl hψ_ne1) (s := z)
    rw [χ.changeLevel_primitiveCharacter] at h
    exact h
  have hord1 : lZeroMult χ ρ = analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) ρ := by
    unfold lZeroMult
    have heq : analyticOrderAt (DirichletCharacter.LFunction χ) ρ =
        analyticOrderAt (fun z => DirichletCharacter.LFunction χ.primitiveCharacter z *
          ∏ p ∈ m.primeFactors, (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))) ρ :=
      analyticOrderAt_congr hev_L
    simp only [analyticOrderNatAt, heq]
    exact analyticOrderNatAt_mul_of_ne_zero hLψ_an hE_an hE_ne
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev_Λ : DirichletCharacter.completedLFunction χ.primitiveCharacter =ᶠ[𝓝 ρ]
      fun z => DirichletCharacter.LFunction χ.primitiveCharacter z *
        DirichletCharacter.gammaFactor χ.primitiveCharacter z := by
    filter_upwards [hopen.mem_nhds h0] with z hz
    exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ.primitiveCharacter hz
  have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hG_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ.primitiveCharacter) ρ := by
    refine DifferentiableOn.analyticAt ?_ (hopen.mem_nhds h0)
    intro z hz
    have hz_re : 0 < z.re := hz
    rcases χ.primitiveCharacter.even_or_odd with he | ho
    · have hfun : DirichletCharacter.gammaFactor χ.primitiveCharacter =
          fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) :=
        funext fun w => by rw [he.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
      rw [hfun]
      have h1 : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2))) z := by fun_prop
      have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
        (Complex.differentiableAt_Gamma (z / 2) fun k hEq => by
          have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
          (differentiableAt_id.div_const 2)
      exact (h1.mul h2).differentiableWithinAt
    · have hfun : DirichletCharacter.gammaFactor χ.primitiveCharacter =
          fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2)) * Complex.Gamma ((w + 1) / 2) :=
        funext fun w => by rw [ho.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
      rw [hfun]
      have h1 : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2))) z := by fun_prop
      have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((w + 1) / 2)) z :=
        (Complex.differentiableAt_Gamma ((z + 1) / 2) fun k hEq => by
          have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
          ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2)
      exact (h1.mul h2).differentiableWithinAt
  have hG_ne := gammaFactor_ne_zero_of_re_pos χ.primitiveCharacter h0
  have hord2 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ =
      analyticOrderNatAt (DirichletCharacter.LFunction χ.primitiveCharacter) ρ := by
    have heq : analyticOrderAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ =
        analyticOrderAt (fun z => DirichletCharacter.LFunction χ.primitiveCharacter z *
          DirichletCharacter.gammaFactor χ.primitiveCharacter z) ρ :=
      analyticOrderAt_congr hev_Λ
    simp only [analyticOrderNatAt, heq]
    exact analyticOrderNatAt_mul_of_ne_zero hLψ_an hG_an hG_ne
  dsimp only
  rw [hord1, hord2]

/-- **Multiplicity-Counted Cumulative Zero-Count Upper Bound for ALL `χ mod m`** (`m ≥ 2, T ≥ 1`):
`∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) ≤ C * T * Real.log (m * (T + 2))`. -/
theorem lZeroCount_box_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (T : ℝ), 1 ≤ T →
      ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) ≤ C * T * Real.log ((m : ℝ) * (T + 2)) := by
  obtain ⟨C_ζ, hCζ_pos, hζ_asymp⟩ := Stage9ExplicitFormula.riemann_von_mangoldt_zeta_asymptotic
  obtain ⟨C_L, hCL_pos, hL_asymp⟩ := Stage8GRHEquivalence.lFunctionZeroCount_asymptotic
  set C : ℝ := 4 * (C_ζ + C_L + 4)
  refine ⟨C, by positivity, fun m _ hm χ T hT => ?_⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog_mT_pos : 0 < Real.log ((m : ℝ) * (T + 2)) := Real.log_pos (by nlinarith)
  have hlog_T2_le : Real.log (T + 2) ≤ Real.log ((m : ℝ) * (T + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  by_cases hχ : χ = 1
  · subst hχ
    rw [lZerosInBox_one_eq_zetaZerosInBox]
    have hsum_le : ∑ ρ ∈ Stage9ExplicitFormula.zetaZerosInBox T,
        (lZeroMult (1 : DirichletCharacter ℂ m) ρ : ℝ) ≤
        2 * Stage7VonMangoldtExplicit.xiZeroCount (T + 1) := by
      have hcongr : ∑ ρ ∈ Stage9ExplicitFormula.zetaZerosInBox T,
          (lZeroMult (1 : DirichletCharacter ℂ m) ρ : ℝ) =
          ∑ ρ ∈ Stage9ExplicitFormula.zetaZerosInBox T, (analyticOrderNatAt xi ρ : ℝ) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
        rw [lZeroMult_one_eq_xi m hm'.1 hm'.2.1]
      rw [hcongr]
      -- Split into `Im > 0` and `Im < 0` (note: `riemannZeta` has no real zeros in `(0, 1)`!)
      set Z := Stage9ExplicitFormula.zetaZerosInBox T
      have hno_real : ∀ ρ ∈ Z, ρ.im ≠ 0 := fun ρ hρ him => by
        have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
        have hρ_eq : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
        have hneg := Stage9LandauSiegel.riemannZeta_neg_on_Ioo hm'.1 hm'.2.1
        rw [hρ_eq] at hm'
        have := congrArg Complex.re hm'.2.2.1
        simp at this; linarith [hneg.1]
      have hpos_sub : Z.filter (fun ρ => 0 < ρ.im) ⊆ Stage7VonMangoldtExplicit.xiZeroSetPos (T + 1) := by
        intro ρ hρ
        rcases Finset.mem_filter.mp hρ with ⟨hρZ, hpos⟩
        have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρZ
        have him_le : |ρ.im| ≤ T := hm'.2.2.2
        simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨hm'.1, hm'.2.1, hm'.2.2.1, by linarith⟩, hpos, by linarith [abs_of_pos hpos]⟩
      have hneg_map : ∀ ρ ∈ Z.filter (fun ρ => ρ.im < 0),
          starRingEnd ℂ ρ ∈ Stage7VonMangoldtExplicit.xiZeroSetPos (T + 1) := by
        intro ρ hρ
        rcases Finset.mem_filter.mp hρ with ⟨hρZ, hneg⟩
        have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρZ
        have him_le : |ρ.im| ≤ T := hm'.2.2.2
        have hζc := (RHDirect.riemannZeta_fourfold_zero_symmetry hm'.1 hm'.2.1 hm'.2.2.1).1
        simp only [Stage7VonMangoldtExplicit.xiZeroSetPos, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨⟨by simpa using hm'.1, by simpa using hm'.2.1, hζc, by simpa using (by linarith : |ρ.im| ≤ T + 1)⟩,
          by simp; linarith, by simp; linarith [abs_of_neg hneg]⟩
      have hdisj : Disjoint (Z.filter (fun ρ => 0 < ρ.im)) (Z.filter (fun ρ => ρ.im < 0)) :=
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
      have hunion : Z.filter (fun ρ => 0 < ρ.im) ∪ Z.filter (fun ρ => ρ.im < 0) = Z := by
        ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h; rcases lt_or_gt_of_ne (hno_real ρ h) with hlt | hgt
          · exact Or.inr ⟨h, hlt⟩
          · exact Or.inl ⟨h, hgt⟩
      have h1 : ∑ ρ ∈ Z.filter (fun ρ => 0 < ρ.im), (analyticOrderNatAt xi ρ : ℝ) ≤
          Stage7VonMangoldtExplicit.xiZeroCount (T + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hpos_sub fun _ _ _ => Nat.cast_nonneg _
      have h2 : ∑ ρ ∈ Z.filter (fun ρ => ρ.im < 0), (analyticOrderNatAt xi ρ : ℝ) ≤
          Stage7VonMangoldtExplicit.xiZeroCount (T + 1) := by
        have hinj : Set.InjOn (starRingEnd ℂ) (Z.filter (fun ρ => ρ.im < 0) : Set ℂ) :=
          fun a _ b _ h => (starRingEnd ℂ).injective h
        have hsum_img : ∑ ρ ∈ Z.filter (fun ρ => ρ.im < 0), (analyticOrderNatAt xi ρ : ℝ) =
            ∑ w ∈ (Z.filter (fun ρ => ρ.im < 0)).image (starRingEnd ℂ), (analyticOrderNatAt xi w : ℝ) := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          rw [Stage7VonMangoldtExplicit.analyticOrderNatAt_xi_conj]
        rw [hsum_img]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => ?_) fun _ _ _ => Nat.cast_nonneg _
        rcases Finset.mem_image.mp hw with ⟨ρ, hρ, rfl⟩
        exact hneg_map ρ hρ
      rw [← hunion, Finset.sum_union hdisj]
      linarith
    have has := (abs_le.mp (hζ_asymp (T + 1) (by linarith))).2
    have hlog_le : Real.log ((T + 1) / (2 * Real.pi * Real.exp 1)) ≤ Real.log ((m : ℝ) * (T + 2)) := by
      refine Real.log_le_log (by positivity) ?_
      have hden : (1 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by
        have := Real.pi_gt_three; have := Real.exp_one_gt_d9; nlinarith
      calc (T + 1) / (2 * Real.pi * Real.exp 1) ≤ (T + 1) / 1 :=
            div_le_div_of_nonneg_left (by linarith) zero_lt_one hden
        _ = T + 1 := div_one _
        _ ≤ (m : ℝ) * (T + 2) := by nlinarith
    have hlog_T1 : Real.log (T + 1) ≤ Real.log ((m : ℝ) * (T + 2)) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hmain : ((T + 1) / (2 * Real.pi)) * Real.log ((T + 1) / (2 * Real.pi * Real.exp 1)) ≤
        2 * T * Real.log ((m : ℝ) * (T + 2)) := by
      have hdiv : (T + 1) / (2 * Real.pi) ≤ 2 * T := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
      rcases le_total 0 (Real.log ((T + 1) / (2 * Real.pi * Real.exp 1))) with hnn | hnp
      · exact mul_le_mul hdiv hlog_le hnn (by positivity)
      · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp).trans (by positivity)
    have hC1 : C_ζ * Real.log (T + 1) ≤ C_ζ * T * Real.log ((m : ℝ) * (T + 2)) := by
      have h1 : Real.log (T + 1) ≤ T * Real.log ((m : ℝ) * (T + 2)) := by nlinarith
      nlinarith
    have hTlog_nn : 0 ≤ T * Real.log ((m : ℝ) * (T + 2)) := by positivity
    dsimp only [C]; nlinarith
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψ_ne1 : χ.primitiveCharacter ≠ 1 := fun h1 => hχ (by
      rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
    have hd_le : (χ.conductor : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos m) χ.conductor_dvd_level
    have hd_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ.conductor)
    have hsum_le : ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) ≤
        lFunctionZeroCount χ.primitiveCharacter_isPrimitive hψ_ne1 (T + 1) := by
      have hcongr : ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) =
          ∑ ρ ∈ lZerosInBox χ T,
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ : ℝ) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        exact congrArg Nat.cast (lZeroMult_eq_primitive hχ (mem_lZerosInBox.mp hρ).1)
      rw [hcongr]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) fun _ _ _ => Nat.cast_nonneg _
      have hm' := mem_lZerosInBox.mp hρ
      have hLψ := (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ hm'.1 (.inl hχ)).mp hm'.2.2.1
      have hΛψ := (completedLFunction_eq_zero_iff_LFunction_of_re_pos χ.primitiveCharacter hm'.1).mpr hLψ
      simp only [lFunctionZeroSet, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨⟨hΛψ, (by linarith [hm'.2.2.2] : |ρ.im| ≤ T + 1).trans (le_max_left _ 2)⟩, by linarith [hm'.2.2.2]⟩
    have has := (abs_le.mp (hL_asymp χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
      hψ_ne1 (T + 1) (by linarith))).2
    have hlog_dT1 : Real.log ((χ.conductor : ℝ) * (T + 1)) ≤ Real.log ((m : ℝ) * (T + 2)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hlog_div : Real.log ((χ.conductor : ℝ) * (T + 1) / (2 * Real.pi * Real.exp 1)) ≤
        Real.log ((m : ℝ) * (T + 2)) := by
      refine Real.log_le_log (by positivity) ?_
      have hden : (1 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by
        have := Real.pi_gt_three; have := Real.exp_one_gt_d9; nlinarith
      calc (χ.conductor : ℝ) * (T + 1) / (2 * Real.pi * Real.exp 1)
          ≤ (χ.conductor : ℝ) * (T + 1) / 1 := div_le_div_of_nonneg_left (by positivity) zero_lt_one hden
        _ = (χ.conductor : ℝ) * (T + 1) := div_one _
        _ ≤ (m : ℝ) * (T + 2) := by nlinarith
    have hmain : ((T + 1) / Real.pi) * Real.log ((χ.conductor : ℝ) * (T + 1) / (2 * Real.pi * Real.exp 1)) ≤
        2 * T * Real.log ((m : ℝ) * (T + 2)) := by
      have hdiv : (T + 1) / Real.pi ≤ 2 * T := by
        rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
      rcases le_total 0 (Real.log ((χ.conductor : ℝ) * (T + 1) / (2 * Real.pi * Real.exp 1))) with hnn | hnp
      · exact mul_le_mul hdiv hlog_div hnn (by positivity)
      · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnp).trans (by positivity)
    have hC2 : C_L * Real.log ((χ.conductor : ℝ) * (T + 1)) ≤ C_L * T * Real.log ((m : ℝ) * (T + 2)) := by
      have h1 : Real.log ((χ.conductor : ℝ) * (T + 1)) ≤ T * Real.log ((m : ℝ) * (T + 2)) := by nlinarith
      nlinarith
    have hTlog_nn : 0 ≤ T * Real.log ((m : ℝ) * (T + 2)) := by positivity
    dsimp only [C]; nlinarith

/-- Elementary weighted geometric sum identity:
`∑ k ∈ Finset.range N, ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k = 4 - 2 * ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ N`. -/
private lemma sum_nat_add_one_mul_half_pow (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k =
      4 - 2 * ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp; norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast; ring

private lemma sum_half_pow_le_two (N : ℕ) :
    ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k ≤ 2 := by
  have h : ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k = 2 - 2 * (1 / 2 : ℝ) ^ N := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [h]; linarith [show (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ N by positivity]

/-- **Dyadic-Shell Tail Bound on `∑_{T₀ < |ρ.im| ≤ T} m_ρ / (1 + ρ.im ^ 2)`** (`0` Assumptions!):
`∃ C > 0, ∀ m ≥ 2, ∀ χ mod m, ∀ T₀ ≥ 1, ∀ T ≥ T₀,
  ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => T₀ < |ρ.im|), (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
    C * Real.log (m * (T₀ + 2)) / T₀`. -/
theorem sum_tail_inv_im_sq_lZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (T₀ T : ℝ),
      1 ≤ T₀ → T₀ ≤ T →
      ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => T₀ < |ρ.im|),
          (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
        C * Real.log ((m : ℝ) * (T₀ + 2)) / T₀ := by
  classical
  obtain ⟨C₀, hC₀_pos, hbox⟩ := lZeroCount_box_le
  refine ⟨12 * C₀, by positivity, fun m _ hm χ T₀ T hT₀ hT₀T => ?_⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hT₀_pos : 0 < T₀ := by linarith
  set N : ℕ := ⌈Real.log (T / T₀) / Real.log 2⌉₊ + 1
  let shell : ℕ → Finset ℂ := fun k =>
    (lZerosInBox χ (T₀ * (2 : ℝ) ^ (k + 1))).filter (fun ρ => T₀ * (2 : ℝ) ^ k ≤ |ρ.im|)
  have hcover : (lZerosInBox χ T).filter (fun ρ => T₀ < |ρ.im|) ⊆ (Finset.range N).biUnion shell := by
    intro ρ hρ
    rcases Finset.mem_filter.mp hρ with ⟨hρT, hgt⟩
    have hm' := mem_lZerosInBox.mp hρT
    rw [Finset.mem_biUnion]
    set k : ℕ := ⌊Real.log (|ρ.im| / T₀) / Real.log 2⌋₊
    have hrat_gt1 : 1 < |ρ.im| / T₀ := (one_lt_div hT₀_pos).mpr hgt
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog_nn : 0 ≤ Real.log (|ρ.im| / T₀) / Real.log 2 :=
      div_nonneg (Real.log_nonneg hrat_gt1.le) hlog2_pos.le
    have hk_le : (k : ℝ) ≤ Real.log (|ρ.im| / T₀) / Real.log 2 := Nat.floor_le hlog_nn
    have hk_lt : Real.log (|ρ.im| / T₀) / Real.log 2 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hk_lt_N : k < N := by
      have h1 : Real.log (|ρ.im| / T₀) / Real.log 2 ≤ Real.log (T / T₀) / Real.log 2 :=
        div_le_div_of_nonneg_right (Real.log_le_log (by positivity)
          (div_le_div_of_nonneg_right hm'.2.2.2 hT₀_pos.le)) hlog2_pos.le
      have h2 : (k : ℝ) ≤ (⌈Real.log (T / T₀) / Real.log 2⌉₊ : ℝ) :=
        (hk_le.trans h1).trans (Nat.le_ceil _)
      have hk_nat : k ≤ ⌈Real.log (T / T₀) / Real.log 2⌉₊ := by exact_mod_cast h2
      dsimp only [N]; omega
    have h2k_le : (2 : ℝ) ^ k ≤ |ρ.im| / T₀ := by
      have h1 : (k : ℝ) * Real.log 2 ≤ Real.log (|ρ.im| / T₀) := (le_div_iff₀ hlog2_pos).mp hk_le
      rw [← Real.rpow_natCast (2 : ℝ) k, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        mul_comm]
      exact (Real.le_log_iff_exp_le (by positivity)).mp h1
    have h2k1_gt : |ρ.im| / T₀ < (2 : ℝ) ^ (k + 1) := by
      have h1 : Real.log (|ρ.im| / T₀) < ((k : ℝ) + 1) * Real.log 2 := (div_lt_iff₀ hlog2_pos).mp hk_lt
      rw [← Real.rpow_natCast (2 : ℝ) (k + 1), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        Nat.cast_add, Nat.cast_one, mul_comm]
      exact (Real.log_lt_iff_lt_exp (by positivity)).mp h1
    refine ⟨k, Finset.mem_range.mpr hk_lt_N, Finset.mem_filter.mpr ⟨mem_lZerosInBox.mpr
      ⟨hm'.1, hm'.2.1, hm'.2.2.1, ?_⟩, ?_⟩⟩
    · exact ((div_lt_iff₀ hT₀_pos).mp h2k1_gt).le.trans_eq (mul_comm _ _)
    · exact (mul_comm ((2 : ℝ) ^ k) T₀).symm ▸ (le_div_iff₀ hT₀_pos).mp h2k_le
  have hterm_nn : ∀ ρ : ℂ, 0 ≤ (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) := fun _ => by positivity
  have hbi_le : ∑ ρ ∈ (Finset.range N).biUnion shell, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
      ∑ k ∈ Finset.range N, ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) := by
    induction N with
    | zero => simp
    | succ M ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
      have hu : ∑ ρ ∈ shell M ∪ (Finset.range M).biUnion shell, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
          (∑ ρ ∈ shell M, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) +
          ∑ ρ ∈ (Finset.range M).biUnion shell, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) := by
        rw [← Finset.sum_union_inter]
        linarith [Finset.sum_nonneg (s := shell M ∩ (Finset.range M).biUnion shell) fun ρ _ => hterm_nn ρ]
      linarith
  have hshell_bd : ∀ k : ℕ, ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
      2 * C₀ * (Real.log ((m : ℝ) * (T₀ + 2)) / T₀) * (((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k) := by
    intro k
    have hden_ge : ∀ ρ ∈ shell k, (T₀ * (2 : ℝ) ^ k) ^ 2 ≤ 1 + ρ.im ^ 2 := fun ρ hρ => by
      have h1 : T₀ * (2 : ℝ) ^ k ≤ |ρ.im| := (Finset.mem_filter.mp hρ).2
      have h2 : (T₀ * (2 : ℝ) ^ k) ^ 2 ≤ |ρ.im| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [sq_abs] at h2; linarith
    have hsum1 : ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
        (∑ ρ ∈ lZerosInBox χ (T₀ * (2 : ℝ) ^ (k + 1)), (lZeroMult χ ρ : ℝ)) / (T₀ * (2 : ℝ) ^ k) ^ 2 := by
      calc ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)
          ≤ ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (T₀ * (2 : ℝ) ^ k) ^ 2 :=
            Finset.sum_le_sum fun ρ hρ => div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (hden_ge ρ hρ)
        _ = (∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ)) / (T₀ * (2 : ℝ) ^ k) ^ 2 := (Finset.sum_div _ _ _).symm
        _ ≤ (∑ ρ ∈ lZerosInBox χ (T₀ * (2 : ℝ) ^ (k + 1)), (lZeroMult χ ρ : ℝ)) / (T₀ * (2 : ℝ) ^ k) ^ 2 :=
            div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => Nat.cast_nonneg _) (by positivity)
    have hT_ge1 : 1 ≤ T₀ * (2 : ℝ) ^ (k + 1) := by
      have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      nlinarith
    have hcnt := hbox m hm χ (T₀ * (2 : ℝ) ^ (k + 1)) hT_ge1
    have hlog_le : Real.log ((m : ℝ) * (T₀ * (2 : ℝ) ^ (k + 1) + 2)) ≤
        ((k : ℝ) + 2) * Real.log ((m : ℝ) * (T₀ + 2)) := by
      have h2p : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
      have hbase : (2 : ℝ) ≤ (m : ℝ) * (T₀ + 2) := by nlinarith
      have harg : (m : ℝ) * (T₀ * (2 : ℝ) ^ (k + 1) + 2) ≤ ((m : ℝ) * (T₀ + 2)) ^ (k + 2) := by
        have hstep1 : T₀ * (2 : ℝ) ^ (k + 1) + 2 ≤ (T₀ + 2) * (2 : ℝ) ^ (k + 1) := by nlinarith
        have hstep2 : (2 : ℝ) ^ (k + 1) ≤ ((m : ℝ) * (T₀ + 2)) ^ (k + 1) :=
          pow_le_pow_left₀ (by norm_num) hbase (k + 1)
        calc (m : ℝ) * (T₀ * (2 : ℝ) ^ (k + 1) + 2)
            ≤ (m : ℝ) * ((T₀ + 2) * (2 : ℝ) ^ (k + 1)) := mul_le_mul_of_nonneg_left hstep1 (by positivity)
          _ = ((m : ℝ) * (T₀ + 2)) * (2 : ℝ) ^ (k + 1) := by ring
          _ ≤ ((m : ℝ) * (T₀ + 2)) * ((m : ℝ) * (T₀ + 2)) ^ (k + 1) :=
              mul_le_mul_of_nonneg_left hstep2 (by positivity)
          _ = ((m : ℝ) * (T₀ + 2)) ^ (k + 2) := by rw [← pow_succ']
      calc Real.log ((m : ℝ) * (T₀ * (2 : ℝ) ^ (k + 1) + 2))
          ≤ Real.log (((m : ℝ) * (T₀ + 2)) ^ (k + 2)) := Real.log_le_log (by positivity) harg
        _ = ((k + 2 : ℕ) : ℝ) * Real.log ((m : ℝ) * (T₀ + 2)) := Real.log_pow _ _
        _ = ((k : ℝ) + 2) * Real.log ((m : ℝ) * (T₀ + 2)) := by push_cast; ring
    have hnum : ∑ ρ ∈ lZerosInBox χ (T₀ * (2 : ℝ) ^ (k + 1)), (lZeroMult χ ρ : ℝ) ≤
        C₀ * (T₀ * (2 : ℝ) ^ (k + 1)) * (((k : ℝ) + 2) * Real.log ((m : ℝ) * (T₀ + 2))) :=
      hcnt.trans (mul_le_mul_of_nonneg_left hlog_le (by positivity))
    calc ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)
        ≤ C₀ * (T₀ * (2 : ℝ) ^ (k + 1)) * (((k : ℝ) + 2) * Real.log ((m : ℝ) * (T₀ + 2))) /
            (T₀ * (2 : ℝ) ^ k) ^ 2 := hsum1.trans (div_le_div_of_nonneg_right hnum (by positivity))
      _ = 2 * C₀ * (Real.log ((m : ℝ) * (T₀ + 2)) / T₀) * (((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k) := by
            have h2k : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
            rw [one_div_pow, pow_succ, mul_pow, sq ((2 : ℝ) ^ k)]
            field_simp [hT₀_pos.ne', h2k]
  have hgeom : ∑ k ∈ Finset.range N, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k ≤ 6 := by
    have hsplit : ∑ k ∈ Finset.range N, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k =
        (∑ k ∈ Finset.range N, ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) +
        ∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit, sum_nat_add_one_mul_half_pow N]
    have hnn : 0 ≤ 2 * ((N : ℝ) + 2) * (1 / 2 : ℝ) ^ N := by positivity
    linarith [sum_half_pow_le_two N]
  have hlog_nn : 0 ≤ Real.log ((m : ℝ) * (T₀ + 2)) := Real.log_nonneg (by nlinarith)
  calc ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => T₀ < |ρ.im|), (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)
      ≤ ∑ ρ ∈ (Finset.range N).biUnion shell, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun ρ _ _ => hterm_nn ρ
    _ ≤ ∑ k ∈ Finset.range N, ∑ ρ ∈ shell k, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) := hbi_le
    _ ≤ ∑ k ∈ Finset.range N,
          2 * C₀ * (Real.log ((m : ℝ) * (T₀ + 2)) / T₀) * (((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k) :=
        Finset.sum_le_sum fun k _ => hshell_bd k
    _ = 2 * C₀ * (Real.log ((m : ℝ) * (T₀ + 2)) / T₀) *
          ∑ k ∈ Finset.range N, ((k : ℝ) + 2) * (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * C₀ * (Real.log ((m : ℝ) * (T₀ + 2)) / T₀) * 6 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 12 * C₀ * Real.log ((m : ℝ) * (T₀ + 2)) / T₀ := by ring

/-- **Uniform Full-Box Bound `∑_{ρ ∈ lZerosInBox χ T} m_ρ / (1 + ρ.im ^ 2) ≤ C * Real.log m`** (`0` Assumptions!). -/
theorem sum_inv_one_add_im_sq_lZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (T : ℝ), 1 ≤ T →
      ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤ C * Real.log (m : ℝ) := by
  classical
  obtain ⟨C₀, hC₀_pos, hbox⟩ := lZeroCount_box_le
  obtain ⟨C₁, hC₁_pos, htail⟩ := sum_tail_inv_im_sq_lZeros_le
  refine ⟨3 * (C₀ + C₁), by positivity, fun m _ hm χ T hT => ?_⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog3m : Real.log ((m : ℝ) * (1 + 2)) ≤ 3 * Real.log (m : ℝ) := by
    have harg : (m : ℝ) * (1 + 2) ≤ (m : ℝ) ^ 3 := by
      have hsq : 4 ≤ (m : ℝ) ^ 2 := by nlinarith
      have hcu : (m : ℝ) ^ 3 = (m : ℝ) * (m : ℝ) ^ 2 := by ring
      nlinarith
    calc Real.log ((m : ℝ) * (1 + 2)) ≤ Real.log ((m : ℝ) ^ 3) := Real.log_le_log (by positivity) harg
      _ = 3 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
  have hsplit : ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) =
      (∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1), (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) +
      ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => 1 < |ρ.im|), (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) := by
    have hdisj : Disjoint ((lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1))
        ((lZerosInBox χ T).filter (fun ρ => 1 < |ρ.im|)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
    have hu : (lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1) ∪
        (lZerosInBox χ T).filter (fun ρ => 1 < |ρ.im|) = lZerosInBox χ T := by
      ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; rcases le_or_gt |ρ.im| 1 with hle | hgt
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, hgt⟩
    conv_lhs => rw [← hu]
    rw [Finset.sum_union hdisj]
  have hlow : ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1),
      (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤ 3 * C₀ * Real.log (m : ℝ) := by
    have hsub : (lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1) ⊆ lZerosInBox χ 1 := fun ρ hρ => by
      rcases Finset.mem_filter.mp hρ with ⟨h1, h2⟩
      have hm' := mem_lZerosInBox.mp h1
      exact mem_lZerosInBox.mpr ⟨hm'.1, hm'.2.1, hm'.2.2.1, h2⟩
    calc ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1), (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)
        ≤ ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => |ρ.im| ≤ 1), (lZeroMult χ ρ : ℝ) :=
          Finset.sum_le_sum fun ρ _ => div_le_self (Nat.cast_nonneg _) (by nlinarith)
      _ ≤ ∑ ρ ∈ lZerosInBox χ 1, (lZeroMult χ ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
      _ ≤ C₀ * 1 * Real.log ((m : ℝ) * (1 + 2)) := hbox m hm χ 1 le_rfl
      _ ≤ C₀ * 1 * (3 * Real.log (m : ℝ)) := mul_le_mul_of_nonneg_left hlog3m (by positivity)
      _ = 3 * C₀ * Real.log (m : ℝ) := by ring
  have hhi : ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => 1 < |ρ.im|),
      (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤ 3 * C₁ * Real.log (m : ℝ) := by
    have h1 := htail m hm χ 1 T le_rfl hT
    rw [div_one] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_left hlog3m hC₁_pos.le).trans_eq (by ring))
  linarith

/-! ### Dyadic Second Difference, Tent Weight, & Entire Mellin Kernel `dyadicKernel` -/

/-- Integrated (Cesàro-1) Chebyshev sum in an arithmetic progression:
`psi1AP m a x = ∑_{n ≤ x, n ≡ a [MOD m]} Λ(n) * max (x - n) 0`. -/
def psi1AP (m a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), if n ≡ a [MOD m] then Λ n * max (x - (n : ℝ)) 0 else 0

/-- Complex dyadic second difference `Δ₂ f X := f (2 X) - 2 f ((3 / 2) X) + f X`. -/
def dyadic2 (f : ℝ → ℂ) (X : ℝ) : ℂ :=
  f (2 * X) - 2 * f ((3 / 2 : ℝ) * X) + f X

/-- Real dyadic second difference `Δ₂ f X := f (2 X) - 2 f ((3 / 2) X) + f X`. -/
def dyadic2Real (f : ℝ → ℝ) (X : ℝ) : ℝ :=
  f (2 * X) - 2 * f ((3 / 2 : ℝ) * X) + f X

/-- Exact character-orthogonality decomposition of `psi1AP m a x` into `psi1Char χ x`. -/
theorem psi1AP_eq_char_sum {m a : ℕ} [NeZero m] (hcop : Nat.Coprime a m) (x : ℝ) :
    ((psi1AP m a x : ℝ) : ℂ) =
      (m.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m,
          starRingEnd ℂ (χ (a : ZMod m)) * Stage4ExplicitFormula.psi1Char χ x := by
  unfold psi1AP Stage4ExplicitFormula.psi1Char
  rw [Complex.ofReal_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  have horth := Stage2DirichletAP.char_orthogonality_indicator_nat hcop n
  have hrearr :
      ∑ χ : DirichletCharacter ℂ m,
          (m.totient : ℂ)⁻¹ *
            (starRingEnd ℂ (χ (a : ZMod m)) *
              ((Λ n : ℂ) * χ (n : ZMod m) * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ))) =
        ((m.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) * χ (n : ZMod m)) *
          ((Λ n : ℂ) * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ)) := by
    rw [← Finset.mul_sum, mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ _ => by ring
  rw [hrearr, horth]
  by_cases hmod : n ≡ a [MOD m]
  · simp [hmod]
  · simp [hmod]

/-- Exact character-orthogonality decomposition of `dyadic2Real (psi1AP m a) X`. -/
theorem dyadic2Real_psi1AP_eq_char_sum {m a : ℕ} [NeZero m] (hcop : Nat.Coprime a m) (X : ℝ) :
    ((dyadic2Real (psi1AP m a) X : ℝ) : ℂ) =
      (m.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m,
          starRingEnd ℂ (χ (a : ZMod m)) * dyadic2 (Stage4ExplicitFormula.psi1Char χ) X := by
  unfold dyadic2Real dyadic2
  push_cast
  rw [psi1AP_eq_char_sum hcop (2 * X), psi1AP_eq_char_sum hcop ((3 / 2 : ℝ) * X),
    psi1AP_eq_char_sum hcop X]
  have h1 : ∀ f g h : DirichletCharacter ℂ m → ℂ,
      (m.totient : ℂ)⁻¹ * (∑ χ, f χ) - 2 * ((m.totient : ℂ)⁻¹ * (∑ χ, g χ)) +
        (m.totient : ℂ)⁻¹ * (∑ χ, h χ) =
      (m.totient : ℂ)⁻¹ * ∑ χ, (f χ - 2 * g χ + h χ) := fun f g h => by
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]; ring
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => by ring

/-- Pointwise tent weight identity for `dyadic2Real`: for `0 ≤ X` and any `t : ℝ`,
`w_X(t) := max (2 X - t) 0 - 2 * max ((3 / 2) X - t) 0 + max (X - t) 0` vanishes outside `(X, 2 X)`
and satisfies `0 ≤ w_X(t) ≤ X / 2`. -/
private lemma tent_weight_bounds {X : ℝ} (hX : 0 ≤ X) (t : ℝ) :
    let w := max (2 * X - t) 0 - 2 * max ((3 / 2 : ℝ) * X - t) 0 + max (X - t) 0
    0 ≤ w ∧ w ≤ X / 2 ∧ (t ≤ X → w = 0) ∧ (2 * X ≤ t → w = 0) := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [w]
    by_cases h1 : t ≤ X
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · by_cases h2 : t ≤ (3 / 2 : ℝ) * X
      · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
      · by_cases h3 : t ≤ 2 * X
        · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
        · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; norm_num
  · dsimp only [w]
    by_cases h1 : t ≤ X
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · by_cases h2 : t ≤ (3 / 2 : ℝ) * X
      · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
      · by_cases h3 : t ≤ 2 * X
        · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
        · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
  · intro ht; dsimp only [w]
    rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · intro ht; dsimp only [w]
    rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; ring

/-- Exact finite-sum formula for `dyadic2Real (psi1AP m a) X` over `(X, 2 X]` and its sharp upper
bound by `(X / 2) * (chebyshevPsiAP m a (2 X) - chebyshevPsiAP m a X)`. -/
theorem dyadic2Real_psi1AP_le (m a : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    0 ≤ dyadic2Real (psi1AP m a) X ∧
      dyadic2Real (psi1AP m a) X ≤
        (X / 2) * (chebyshevPsiAP m a (2 * X) - chebyshevPsiAP m a X) := by
  have hfl1 : ⌊X⌋₊ + 1 ≤ ⌊2 * X⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  have hfl2 : ⌊(3 / 2 : ℝ) * X⌋₊ + 1 ≤ ⌊2 * X⌋₊ + 1 :=
    Nat.add_le_add_right (Nat.floor_mono (by linarith)) 1
  -- Extend all three sums to `Finset.range (⌊2 * X⌋₊ + 1)`
  have hext : ∀ y : ℝ, 0 ≤ y → y ≤ 2 * X →
      psi1AP m a y = ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
        if n ≡ a [MOD m] then Λ n * max (y - (n : ℝ)) 0 else 0 := fun y hy hy2 => by
    unfold psi1AP
    refine Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hy2) 1)) ?_
    intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    have hyn : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hn)
    have hmax : max (y - (n : ℝ)) 0 = 0 := max_eq_right (by linarith)
    simp [hmax]
  have hrew : dyadic2Real (psi1AP m a) X =
      ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
        if n ≡ a [MOD m] then
          Λ n * (max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0)
        else 0 := by
    unfold dyadic2Real
    rw [hext (2 * X) (by linarith) le_rfl, hext ((3 / 2 : ℝ) * X) (by linarith) (by linarith),
      hext X hX (by linarith), Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
  rw [hrew]
  refine ⟨Finset.sum_nonneg fun n _ => ?_, ?_⟩
  · split_ifs
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (tent_weight_bounds hX n).1
    · exact le_rfl
  · have hdiff : chebyshevPsiAP m a (2 * X) - chebyshevPsiAP m a X =
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1),
          if n ≡ a [MOD m] then Λ n else 0 := by
      unfold chebyshevPsiAP
      exact (eq_sub_of_add_eq (Finset.sum_sdiff (Finset.range_mono hfl1))).symm
    rw [hdiff, Finset.mul_sum]
    have hsplit_sum :
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
            (if n ≡ a [MOD m] then
              Λ n * (max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0)
             else 0) =
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1) \ Finset.range (⌊X⌋₊ + 1),
            (if n ≡ a [MOD m] then
              Λ n * (max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0)
             else 0) := by
      rw [← Finset.sum_sdiff (Finset.range_mono hfl1)]
      have hzero : ∑ n ∈ Finset.range (⌊X⌋₊ + 1),
          (if n ≡ a [MOD m] then
            Λ n * (max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0)
           else 0) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        have hnle : (n : ℝ) ≤ X := by
          have h1 : (n : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          exact h1.trans (Nat.floor_le hX)
        simp [(tent_weight_bounds hX n).2.2.1 hnle]
      rw [hzero, add_zero]
    rw [hsplit_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    split_ifs
    · calc Λ n * (max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0)
          ≤ Λ n * (X / 2) := mul_le_mul_of_nonneg_left (tent_weight_bounds hX n).2.1 ArithmeticFunction.vonMangoldt_nonneg
        _ = (X / 2) * Λ n := mul_comm _ _
    · simp

/-- **Exact Quantitative Prime Extraction from `dyadic2Real (psi1AP m a) X`**:
if `1 ≤ X` and `(X / 2) * √(2 X) * log (2 X) < dyadic2Real (psi1AP m a) X`, then there exists
a prime `p ≡ a [MOD m]` strictly inside `(X, 2 * X]`. -/
theorem exists_prime_in_Ioc_of_dyadic2_psi1AP_gt (m a : ℕ) {X : ℝ} (hX : 1 ≤ X)
    (hgt : (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) < dyadic2Real (psi1AP m a) X) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD m] ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ 2 * X := by
  have hle := (dyadic2Real_psi1AP_le m a (X := X) (by linarith)).2
  have hdiff_gt : Real.sqrt (2 * X) * Real.log (2 * X) <
      chebyshevPsiAP m a (2 * X) - chebyshevPsiAP m a X := by
    have hX2 : 0 < X / 2 := by linarith
    have h1 : (X / 2) * (Real.sqrt (2 * X) * Real.log (2 * X)) <
        (X / 2) * (chebyshevPsiAP m a (2 * X) - chebyshevPsiAP m a X) := by linarith
    exact lt_of_mul_lt_mul_left h1 hX2.le
  exact Stage2DirichletAP.exists_prime_in_Ioc_of_psiAP_diff_gt m a hX (by linarith) hdiff_gt

/-- Helper: `(p ^ k).minFac = p` for any prime `p` and `k ≥ 1`. -/
private lemma minFac_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : (p ^ k).minFac = p := by
  have hne1 : p ^ k ≠ 1 := by
    have : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  have hmf_p : (p ^ k).minFac.Prime := Nat.minFac_prime hne1
  have hdvd : (p ^ k).minFac ∣ p := hmf_p.dvd_of_dvd_pow (Nat.minFac_dvd (p ^ k))
  exact (Nat.prime_dvd_prime_iff_eq hmf_p hp).mp hdvd

/-- **Sharp Dyadic Coprime-Reduction Bound (`(X / 2) * log m`)**:
for any `χ : DirichletCharacter ℂ m` (`m ≥ 2`) and its underlying primitive character `ψ`,
`‖dyadic2 (psi1Char χ) X - dyadic2 (psi1Char ψ) X‖ ≤ (X / 2) * Real.log m` (and similarly for
`χ = 1` vs `Stage6EffectivePNT.psi1`)! -/
lemma norm_dyadic2_psi1Char_sub_primitive_le {m : ℕ} [NeZero m] (_hm : 2 ≤ m)
    (χ : DirichletCharacter ℂ m) {X : ℝ} (hX : 1 ≤ X) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    ‖dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
      dyadic2 (Stage4ExplicitFormula.psi1Char χ.primitiveCharacter) X‖ ≤
      (X / 2) * Real.log (m : ℝ) := by
  classical
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ := χ.primitiveCharacter
  have hext : ∀ {d : ℕ} [NeZero d] (η : DirichletCharacter ℂ d) (y : ℝ), 0 ≤ y → y ≤ 2 * X →
      Stage4ExplicitFormula.psi1Char η y =
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1), (Λ n : ℂ) * η n * ((max (y - (n : ℝ)) 0 : ℝ) : ℂ) := by
    intro d _ η y hy hy2
    unfold Stage4ExplicitFormula.psi1Char
    refine Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hy2) 1)) ?_
    intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    have hyn : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hn)
    have hmax : max (y - (n : ℝ)) 0 = 0 := max_eq_right (by linarith)
    simp [hmax]
  let wX : ℕ → ℝ := fun n =>
    max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0
  have hdy : ∀ {d : ℕ} [NeZero d] (η : DirichletCharacter ℂ d),
      dyadic2 (Stage4ExplicitFormula.psi1Char η) X =
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1), (Λ n : ℂ) * η n * ((wX n : ℝ) : ℂ) := by
    intro d _ η
    unfold dyadic2
    rw [hext η (2 * X) (by linarith) le_rfl, hext η ((3 / 2 : ℝ) * X) (by linarith) (by linarith),
      hext η X (by linarith) (by linarith), Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by dsimp only [wX]; push_cast; ring
  have hcop_eq : ∀ n : ℕ, Nat.Coprime n m → χ (n : ZMod m) = ψ (n : ZMod χ.conductor) := by
    intro n hcop
    rcases (ZMod.isUnit_iff_coprime n m).mpr hcop with ⟨u, hu_eq⟩
    have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ χ.conductor_dvd_level u
    rw [χ.changeLevel_primitiveCharacter, hu_eq] at h1
    simpa [ZMod.cast_natCast χ.conductor_dvd_level] using h1
  set S : Finset ℕ := (Finset.range (⌊2 * X⌋₊ + 1)).filter
    fun n => X < (n : ℝ) ∧ ¬ Nat.Coprime n m ∧ IsPrimePow n
  have hnorm_sum :
      ‖∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
          ((Λ n : ℂ) * χ n * ((wX n : ℝ) : ℂ) - (Λ n : ℂ) * ψ n * ((wX n : ℝ) : ℂ))‖ ≤
        ∑ n ∈ S, (X / 2) * Λ n := by
    calc ‖∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1), _‖
        ≤ ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
            ‖(Λ n : ℂ) * χ n * ((wX n : ℝ) : ℂ) - (Λ n : ℂ) * ψ n * ((wX n : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1), if n ∈ S then (X / 2) * Λ n else 0 := by
          refine Finset.sum_le_sum fun n hn => ?_
          by_cases hXlt : X < (n : ℝ)
          · by_cases hcop : Nat.Coprime n m
            · have h0 : (Λ n : ℂ) * χ n * ((wX n : ℝ) : ℂ) - (Λ n : ℂ) * ψ n * ((wX n : ℝ) : ℂ) = 0 := by
                rw [hcop_eq n hcop]; ring
              rw [h0, norm_zero]; split_ifs <;> positivity
            · by_cases hpp : IsPrimePow n
              · have hmem : n ∈ S := Finset.mem_filter.mpr ⟨hn, hXlt, hcop, hpp⟩
                rw [if_pos hmem]
                have hχ0 : χ (n : ZMod m) = 0 := MulChar.map_nonunit χ (fun hu => hcop ((ZMod.isUnit_iff_coprime n m).mp hu))
                have hψ1 : ‖ψ (n : ZMod χ.conductor)‖ ≤ 1 := ψ.norm_le_one _
                have hw_bd := tent_weight_bounds (by linarith : 0 ≤ X) n
                rw [hχ0, mul_zero, zero_mul, zero_sub, norm_neg, norm_mul, norm_mul,
                  Complex.norm_real, Complex.norm_real,
                  Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
                  Real.norm_of_nonneg hw_bd.1]
                calc Λ n * ‖ψ (n : ZMod χ.conductor)‖ * wX n
                    ≤ Λ n * 1 * (X / 2) :=
                      mul_le_mul (mul_le_mul_of_nonneg_left hψ1 ArithmeticFunction.vonMangoldt_nonneg)
                        hw_bd.2.1 hw_bd.1 (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg zero_le_one)
                  _ = (X / 2) * Λ n := by ring
              · have hΛ0 : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
                rw [hΛ0]; simp
          · have hwn0 : wX n = 0 := (tent_weight_bounds (by linarith) n).2.2.1 (not_lt.mp hXlt)
            rw [hwn0]; simp
            split_ifs <;> positivity
      _ = ∑ n ∈ S, (X / 2) * Λ n := by
          rw [← Finset.sum_filter]
          congr 1; ext n; simp only [Finset.mem_filter, S]; tauto
  have hmaps : ∀ n ∈ S, n.minFac ∈ m.primeFactors := fun n hn => by
    obtain ⟨_, _, hncop, hpp⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, k, hp, hkpos, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [minFac_prime_pow hp hkpos]
    refine Nat.mem_primeFactors.mpr ⟨hp, ?_, (NeZero.pos m).ne'⟩
    by_contra hndvd
    exact hncop ((hp.coprime_iff_not_dvd.mpr hndvd).pow_left k)
  have hinj : Set.InjOn Nat.minFac (S : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    obtain ⟨hr1, hX1, _, hpp1⟩ := Finset.mem_filter.mp hn₁
    obtain ⟨hr2, hX2, _, hpp2⟩ := Finset.mem_filter.mp hn₂
    obtain ⟨p₁, k₁, hp1, hk1, rfl⟩ := (isPrimePow_nat_iff n₁).mp hpp1
    obtain ⟨p₂, k₂, hp2, hk2, rfl⟩ := (isPrimePow_nat_iff n₂).mp hpp2
    rw [minFac_prime_pow hp1 hk1, minFac_prime_pow hp2 hk2] at heq; subst heq
    have hle1 : ((p₁ ^ k₁ : ℕ) : ℝ) ≤ 2 * X := by
      have h1 : ((p₁ ^ k₁ : ℕ) : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hr1)
      exact h1.trans (Nat.floor_le (by linarith))
    have hle2 : ((p₁ ^ k₂ : ℕ) : ℝ) ≤ 2 * X := by
      have h1 : ((p₁ ^ k₂ : ℕ) : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hr2)
      exact h1.trans (Nat.floor_le (by linarith))
    have hk_eq : k₁ = k₂ := by
      rcases lt_trichotomy k₁ k₂ with hlt | rfl | hgt
      · exfalso
        have hpow : p₁ * p₁ ^ k₁ ≤ p₁ ^ k₂ := by
          rw [← pow_succ']; exact Nat.pow_le_pow_right hp1.pos hlt
        have h2p : (2 : ℝ) * ((p₁ ^ k₁ : ℕ) : ℝ) ≤ ((p₁ ^ k₂ : ℕ) : ℝ) := by
          have hp2' : 2 ≤ p₁ := hp1.two_le
          have : 2 * p₁ ^ k₁ ≤ p₁ ^ k₂ := (Nat.mul_le_mul_right _ hp2').trans hpow
          exact_mod_cast this
        linarith
      · rfl
      · exfalso
        have hpow : p₁ * p₁ ^ k₂ ≤ p₁ ^ k₁ := by
          rw [← pow_succ']; exact Nat.pow_le_pow_right hp1.pos hgt
        have h2p : (2 : ℝ) * ((p₁ ^ k₂ : ℕ) : ℝ) ≤ ((p₁ ^ k₁ : ℕ) : ℝ) := by
          have hp2' : 2 ≤ p₁ := hp1.two_le
          have : 2 * p₁ ^ k₂ ≤ p₁ ^ k₁ := (Nat.mul_le_mul_right _ hp2').trans hpow
          exact_mod_cast this
        linarith
    rw [hk_eq]
  have hΛ_eq : ∀ n ∈ S, Λ n = Real.log (n.minFac : ℝ) := fun n hn => by
    obtain ⟨_, _, _, hpp⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    rw [minFac_prime_pow hp hk,
      ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hsum_log : ∑ n ∈ S, Λ n ≤ Real.log (m : ℝ) := by
    calc ∑ n ∈ S, Λ n
        = ∑ n ∈ S, Real.log (n.minFac : ℝ) := Finset.sum_congr rfl hΛ_eq
      _ = ∑ p ∈ S.image Nat.minFac, Real.log (p : ℝ) :=
          (Finset.sum_image (f := fun p : ℕ => Real.log (p : ℝ)) hinj).symm
      _ ≤ ∑ p ∈ m.primeFactors, Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
            fun p _ _ => Real.log_natCast_nonneg p
      _ = Real.log (∏ p ∈ m.primeFactors, (p : ℝ)) :=
          (Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero).symm
      _ ≤ Real.log (m : ℝ) := by
          refine Real.log_le_log (Finset.prod_pos fun p hp =>
            Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos) ?_
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.le_of_dvd (NeZero.pos m) (Nat.prod_primeFactors_dvd m)
  dsimp only
  rw [hdy χ, hdy ψ, ← Finset.sum_sub_distrib]
  calc ‖∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
        ((Λ n : ℂ) * χ n * ((wX n : ℝ) : ℂ) - (Λ n : ℂ) * ψ n * ((wX n : ℝ) : ℂ))‖
      ≤ ∑ n ∈ S, (X / 2) * Λ n := hnorm_sum
    _ = (X / 2) * ∑ n ∈ S, Λ n := (Finset.mul_sum _ _ _).symm
    _ ≤ (X / 2) * Real.log (m : ℝ) := mul_le_mul_of_nonneg_left hsum_log (by linarith)

/-- The numerator `2^(s+1) - 2*(3/2)^(s+1) + 1` of the dyadic second-difference Mellin kernel. -/
def dyadicW (s : ℂ) : ℂ :=
  (2 : ℂ) ^ (s + 1) - 2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1) + 1

/-- The entire (on `s ≠ -1`) dyadic second-difference Mellin kernel
`dyadicKernel s = dslope dyadicW 0 s / (s + 1) = (2^(s+1) - 2*(3/2)^(s+1) + 1) / (s * (s + 1))`. -/
def dyadicKernel (s : ℂ) : ℂ :=
  dslope dyadicW 0 s / (s + 1)

lemma dyadicW_zero : dyadicW 0 = 0 := by
  unfold dyadicW
  rw [zero_add, Complex.cpow_one, Complex.cpow_one]
  push_cast; ring

lemma differentiable_dyadicW : Differentiable ℂ dyadicW := by
  unfold dyadicW
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h32 : ((3 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by norm_num : (3 / 2 : ℝ) ≠ 0)
  have hEq : (fun s : ℂ => (2 : ℂ) ^ (s + 1) - 2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1) + 1) =
      fun s : ℂ => cexp (Complex.log (2 : ℂ) * (s + 1)) -
        2 * cexp (Complex.log ((3 / 2 : ℝ) : ℂ) * (s + 1)) + 1 := by
    funext s; rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h32]
  rw [hEq]; fun_prop

lemma dyadicKernel_eq_div {s : ℂ} (hs0 : s ≠ 0) :
    dyadicKernel s = dyadicW s / (s * (s + 1)) := by
  unfold dyadicKernel
  rw [dslope_of_ne dyadicW hs0, slope_def_field, dyadicW_zero, sub_zero, sub_zero, div_div]

lemma dyadicKernel_one : dyadicKernel 1 = (1 / 4 : ℂ) := by
  rw [dyadicKernel_eq_div one_ne_zero]
  unfold dyadicW
  norm_num [show (1 : ℂ) + 1 = 2 by ring]

lemma differentiableOn_dyadicKernel_re_gt_neg_one :
    DifferentiableOn ℂ dyadicKernel {s : ℂ | -1 < s.re} := by
  have hd_slope : Differentiable ℂ (dslope dyadicW 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr differentiable_dyadicW.differentiableOn)
  intro s hs
  have hs_re : -1 < s.re := hs
  refine ((hd_slope s).div (differentiableAt_id.add (differentiableAt_const 1)) (fun h0 => ?_)).differentiableWithinAt
  have := congrArg Complex.re h0; simp at this; linarith

/-- Exact Mellin-integral representation of `dyadicKernel` on `Re(s) > -1`:
`dyadicKernel s = ∫ u in (1 : ℝ)..2, ((if u ≤ 3/2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)`. -/
theorem dyadicKernel_eq_integral {s : ℂ} (hs : -1 < s.re) :
    dyadicKernel s =
      ∫ u in (1 : ℝ)..2,
        ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1) := by
  let I_fn : ℂ → ℂ := fun z =>
    ∫ u in (1 : ℝ)..2, ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1)
  have hI_split : ∀ z : ℂ, I_fn z =
      (∫ u in (1 : ℝ)..(3 / 2 : ℝ), ((u - 1 : ℝ) : ℂ) * (u : ℂ) ^ (z - 1)) +
      (∫ u in (3 / 2 : ℝ)..(2 : ℝ), ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1)) := by
    intro z
    have hpow_c : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (z - 1)) (Set.Icc 1 2) := fun u hu =>
      (Complex.continuousAt_ofReal_cpow_const u (z - 1) (.inr (by linarith [hu.1] : (u : ℝ) ≠ 0))).continuousWithinAt
    have h1_int : IntervalIntegrable (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1))
        volume (1 : ℝ) (3 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ => u - 1)).continuousOn).mul
        (hpow_c.mono fun u hu => by rw [Set.uIcc_of_le (by norm_num)] at hu; exact ⟨hu.1, by linarith [hu.2]⟩)).congr ?_
      intro u hu; rw [Set.uIcc_of_le (by norm_num)] at hu; simp [hu.2]
    have h2_int : IntervalIntegrable (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1))
        volume (3 / 2) 2 := by
      have hcongr : Set.EqOn
          (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1))
          (fun u : ℝ => ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1)) (Set.Ioc (3 / 2) 2) := by
        intro u hu; simp [not_le.mpr hu.1]
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr ?_
      refine IntegrableOn.congr_fun ?_ hcongr.symm measurableSet_Ioc
      refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp ?_)
      exact (((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ => (2 : ℝ) - u)).continuousOn).mul
        (hpow_c.mono fun u hu => by rw [Set.uIcc_of_le (by norm_num)] at hu; exact ⟨by linarith [hu.1], hu.2⟩)).intervalIntegrable
    dsimp only [I_fn]
    rw [← intervalIntegral.integral_add_adjacent_intervals h1_int h2_int]
    congr 1
    · refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu; simp [hu.2]
    · refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with u hu
      rw [Set.uIoc_of_le (by norm_num)] at hu
      simp [not_le.mpr hu.1]
  have hEval_ne0 : ∀ z : ℂ, z ≠ 0 → z ≠ -1 → dyadicKernel z = I_fn z := by
    intro z hz0 hz1
    have hz1' : z + 1 ≠ 0 := fun h => hz1 (by linear_combination h)
    rw [dyadicKernel_eq_div hz0, hI_split z]
    have hftc : ∀ a b : ℝ, 1 ≤ a → a ≤ b → ∀ α : ℂ, α ≠ 0 →
        ∫ u in a..b, (u : ℂ) ^ (α - 1) = ((b : ℂ) ^ α - (a : ℂ) ^ α) / α := by
      intro a b ha hab α hα
      have hd : ∀ u ∈ Set.uIcc a b,
          HasDerivAt (fun t : ℝ => (t : ℂ) ^ α / α) ((u : ℂ) ^ (α - 1)) u := by
        intro u hu
        rw [Set.uIcc_of_le hab] at hu
        have hu0 : 0 < u := by linarith [hu.1]
        have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
        have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ α) (α * (u : ℂ) ^ (α - 1)) u := by
          have hlog : HasDerivAt (fun t : ℝ => Complex.log (t : ℂ)) ((u : ℂ)⁻¹) u := by
            have h := (Complex.hasDerivAt_log (Or.inl (by simpa using hu0))).comp_ofReal
            simpa using h
          have hev : (fun t : ℝ => (t : ℂ) ^ α) =ᶠ[𝓝 u] fun t : ℝ => cexp (Complex.log (t : ℂ) * α) := by
            filter_upwards [(isOpen_Ioi.mem_nhds hu0)] with t ht
            exact Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') α
          refine ((hlog.mul_const α).cexp.congr_of_eventuallyEq hev).congr_deriv ?_
          rw [← Complex.cpow_def_of_ne_zero huC α, Complex.cpow_sub _ _ huC, Complex.cpow_one]
          field_simp [huC]
        refine (h1.div_const α).congr_deriv ?_
        field_simp [hα]
      have hc : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (α - 1)) (Set.uIcc a b) := by
        intro u hu
        rw [Set.uIcc_of_le hab] at hu
        exact (Complex.continuousAt_ofReal_cpow_const u (α - 1) (.inr (by linarith [hu.1] : u ≠ 0))).continuousWithinAt
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, sub_div]
    have hint_pow : ∀ a b : ℝ, 1 ≤ a → a ≤ b → ∀ β : ℂ,
        IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ β) volume a b := fun a b ha hab β => by
      refine ContinuousOn.intervalIntegrable fun u hu => ?_
      rw [Set.uIcc_of_le hab] at hu
      exact (Complex.continuousAt_ofReal_cpow_const u β (.inr (by linarith [hu.1] : u ≠ 0))).continuousWithinAt
    have hmul_pow : ∀ (u : ℝ), 0 < u → (u : ℂ) * (u : ℂ) ^ (z - 1) = (u : ℂ) ^ z := fun u hu => by
      have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
      conv_lhs => lhs; rw [← Complex.cpow_one (u : ℂ)]
      rw [← Complex.cpow_add _ _ huC]; congr 1; ring
    have h1 : ∫ u in (1 : ℝ)..(3 / 2 : ℝ), ((u - 1 : ℝ) : ℂ) * (u : ℂ) ^ (z - 1) =
        (((3 / 2 : ℝ) : ℂ) ^ (z + 1) - 1) / (z + 1) - (((3 / 2 : ℝ) : ℂ) ^ z - 1) / z := by
      have hcongr : Set.EqOn (fun u : ℝ => ((u - 1 : ℝ) : ℂ) * (u : ℂ) ^ (z - 1))
          (fun u : ℝ => (u : ℂ) ^ ((z + 1) - 1) - (u : ℂ) ^ (z - 1)) (Set.uIcc 1 (3 / 2)) := by
        intro u hu; rw [Set.uIcc_of_le (by norm_num)] at hu
        dsimp only; rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul,
          hmul_pow u (by linarith [hu.1]), add_sub_cancel_right]
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_sub (hint_pow 1 (3 / 2) le_rfl (by norm_num) _)
          (hint_pow 1 (3 / 2) le_rfl (by norm_num) _),
        hftc 1 (3 / 2) le_rfl (by norm_num) (z + 1) hz1',
        hftc 1 (3 / 2) le_rfl (by norm_num) z hz0]
      simp [Complex.one_cpow]
    have h2 : ∫ u in (3 / 2 : ℝ)..(2 : ℝ), ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1) =
        2 * (((2 : ℂ) ^ z - ((3 / 2 : ℝ) : ℂ) ^ z) / z) -
          (((2 : ℂ) ^ (z + 1) - ((3 / 2 : ℝ) : ℂ) ^ (z + 1)) / (z + 1)) := by
      have hcongr : Set.EqOn (fun u : ℝ => ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ (z - 1))
          (fun u : ℝ => 2 * (u : ℂ) ^ (z - 1) - (u : ℂ) ^ ((z + 1) - 1)) (Set.uIcc (3 / 2) 2) := by
        intro u hu; rw [Set.uIcc_of_le (by norm_num)] at hu
        dsimp only; rw [Complex.ofReal_sub, Complex.ofReal_ofNat, sub_mul,
          hmul_pow u (by linarith [hu.1]), add_sub_cancel_right]
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_sub ((hint_pow (3 / 2) 2 (by norm_num) (by norm_num) _).const_mul 2)
          (hint_pow (3 / 2) 2 (by norm_num) (by norm_num) _),
        intervalIntegral.integral_const_mul,
        hftc (3 / 2) 2 (by norm_num) (by norm_num) z hz0,
        hftc (3 / 2) 2 (by norm_num) (by norm_num) (z + 1) hz1']
      simp
    rw [h1, h2]
    have h2pow : (2 : ℂ) * (2 : ℂ) ^ z = (2 : ℂ) ^ (z + 1) := by
      conv_lhs => lhs; rw [← Complex.cpow_one (2 : ℂ)]
      rw [← Complex.cpow_add _ _ two_ne_zero]; congr 1; ring
    have h32pow : (3 : ℂ) * ((3 / 2 : ℝ) : ℂ) ^ z = 2 * ((3 / 2 : ℝ) : ℂ) ^ (z + 1) := by
      have hne : ((3 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by norm_num : (3 / 2 : ℝ) ≠ 0)
      have hmul : (2 : ℂ) * ((3 / 2 : ℝ) : ℂ) = 3 := by push_cast; ring
      rw [Complex.cpow_add _ _ hne, Complex.cpow_one]
      linear_combination -(((3 / 2 : ℝ) : ℂ) ^ z) * hmul
    unfold dyadicW
    field_simp [hz0, hz1']
    linear_combination -(z + 1) * h2pow + (z + 1) * h32pow
  by_cases hs0 : s = 0
  · subst hs0
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have h32 : ((3 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by norm_num : (3 / 2 : ℝ) ≠ 0)
    have hd_W : HasDerivAt dyadicW
        ((2 : ℂ) * ((Real.log 2 : ℝ) : ℂ) - 3 * ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ)) 0 := by
      have hEq : dyadicW = fun z : ℂ =>
          cexp (((Real.log 2 : ℝ) : ℂ) * (z + 1)) -
          2 * cexp (((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) * (z + 1)) + 1 := by
        funext z
        unfold dyadicW
        rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h32,
          show Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) by
            exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm,
          show Complex.log ((3 / 2 : ℝ) : ℂ) = ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) by
            exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 3 / 2)).symm]
      rw [hEq]
      have h1 : HasDerivAt (fun z : ℂ => cexp (((Real.log 2 : ℝ) : ℂ) * (z + 1)))
          (cexp (((Real.log 2 : ℝ) : ℂ) * ((0 : ℂ) + 1)) * ((Real.log 2 : ℝ) : ℂ)) 0 := by
        have hlin : HasDerivAt (fun z : ℂ => ((Real.log 2 : ℝ) : ℂ) * (z + 1))
            ((Real.log 2 : ℝ) : ℂ) 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).add_const (1 : ℂ)).const_mul ((Real.log 2 : ℝ) : ℂ)
        exact hlin.cexp
      have h2' : HasDerivAt (fun z : ℂ => 2 * cexp (((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) * (z + 1)))
          (2 * (cexp (((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) * ((0 : ℂ) + 1)) *
            ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ))) 0 := by
        have hlin : HasDerivAt (fun z : ℂ => ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) * (z + 1))
            ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) 0 := by
          simpa using ((hasDerivAt_id (0 : ℂ)).add_const (1 : ℂ)).const_mul ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ)
        exact hlin.cexp.const_mul 2
      refine ((h1.sub h2').add_const (1 : ℂ)).congr_deriv ?_
      have he2 : cexp (((Real.log 2 : ℝ) : ℂ) * ((0 : ℂ) + 1)) = (2 : ℂ) := by
        rw [zero_add, mul_one, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
      have he32 : cexp (((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) * ((0 : ℂ) + 1)) = ((3 / 2 : ℝ) : ℂ) := by
        rw [zero_add, mul_one, ← Complex.ofReal_exp, Real.exp_log (by norm_num)]
      rw [he2, he32]; push_cast; ring
    have hK0 : dyadicKernel 0 = (2 : ℂ) * ((Real.log 2 : ℝ) : ℂ) - 3 * ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) := by
      unfold dyadicKernel
      rw [dslope_same, zero_add, div_one, hd_W.deriv]
    have hI0 : I_fn 0 = (2 : ℂ) * ((Real.log 2 : ℝ) : ℂ) - 3 * ((Real.log (3 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [hI_split 0]
      have hpow_neg1 : ∀ u : ℝ, 0 < u → (u : ℂ) ^ ((0 : ℂ) - 1) = ((u⁻¹ : ℝ) : ℂ) := fun u _ => by
        rw [zero_sub, Complex.cpow_neg_one, Complex.ofReal_inv]
      have h1_eq : ∫ u in (1 : ℝ)..(3 / 2 : ℝ), ((u - 1 : ℝ) : ℂ) * (u : ℂ) ^ ((0 : ℂ) - 1) =
          (((1 / 2 - Real.log (3 / 2 : ℝ) : ℝ) : ℂ)) := by
        have hcongr : Set.EqOn (fun u : ℝ => ((u - 1 : ℝ) : ℂ) * (u : ℂ) ^ ((0 : ℂ) - 1))
            (fun u : ℝ => (((1 - u⁻¹ : ℝ) : ℂ))) (Set.uIcc 1 (3 / 2)) := by
          intro u hu; rw [Set.uIcc_of_le (by norm_num)] at hu
          have hu0 : 0 < u := by linarith [hu.1]
          dsimp only; rw [hpow_neg1 u hu0, ← Complex.ofReal_mul]; congr 1
          field_simp [hu0.ne']
        rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal]
        congr 1
        have hint_inv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume (1 : ℝ) (3 / 2) :=
          (ContinuousOn.inv₀ continuousOn_id fun u hu => by
            rw [Set.uIcc_of_le (by norm_num)] at hu; dsimp only [id_eq]; linarith [hu.1]).intervalIntegrable
        rw [intervalIntegral.integral_sub intervalIntegrable_const hint_inv,
          intervalIntegral.integral_const, smul_eq_mul, integral_inv_of_pos zero_lt_one (by norm_num),
          div_one]
        norm_num
      have h2_eq : ∫ u in (3 / 2 : ℝ)..(2 : ℝ), ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ ((0 : ℂ) - 1) =
          (((2 * Real.log (2 / (3 / 2 : ℝ)) - 1 / 2 : ℝ) : ℂ)) := by
        have hcongr : Set.EqOn (fun u : ℝ => ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ ((0 : ℂ) - 1))
            (fun u : ℝ => (((2 * u⁻¹ - 1 : ℝ) : ℂ))) (Set.uIcc (3 / 2) 2) := by
          intro u hu; rw [Set.uIcc_of_le (by norm_num)] at hu
          have hu0 : 0 < u := by linarith [hu.1]
          dsimp only; rw [hpow_neg1 u hu0, ← Complex.ofReal_mul]; congr 1
          field_simp [hu0.ne']
        rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal]
        congr 1
        have hint_inv : IntervalIntegrable (fun u : ℝ => u⁻¹) volume (3 / 2 : ℝ) 2 :=
          (ContinuousOn.inv₀ continuousOn_id fun u hu => by
            rw [Set.uIcc_of_le (by norm_num)] at hu; dsimp only [id_eq]; linarith [hu.1]).intervalIntegrable
        rw [intervalIntegral.integral_sub (hint_inv.const_mul 2) intervalIntegrable_const,
          intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num),
          intervalIntegral.integral_const, smul_eq_mul]
        norm_num
      rw [h1_eq, h2_eq, show (2 : ℝ) / (3 / 2 : ℝ) = 4 / 3 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    exact hK0.trans hI0.symm
  · have hs1 : s ≠ -1 := fun h => by rw [h, Complex.neg_re, Complex.one_re] at hs; linarith
    exact hEval_ne0 s hs0 hs1

/-- Exact value of the real tent integral `∫_1^2 w₁(u) du = 1 / 4`. -/
private lemma integral_tent_eq_quarter :
    ∫ u in (1 : ℝ)..2, (if u ≤ 3 / 2 then u - 1 else 2 - u) = (1 / 4 : ℝ) := by
  have h1 : IntervalIntegrable (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u) volume (1 : ℝ) (3 / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ((by fun_prop : Continuous fun u : ℝ => u - 1).continuousOn).congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num)] at hu; simp [hu.2]
  have h2 : IntervalIntegrable (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u) volume (3 / 2 : ℝ) 2 := by
    have hcongr2 : Set.EqOn (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u)
        (fun u : ℝ => (2 : ℝ) - u) (Set.Ioc (3 / 2) 2) := fun u hu => by simp [not_le.mpr hu.1]
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr ?_
    refine IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous fun u : ℝ => (2 : ℝ) - u).intervalIntegrable _ _))
      hcongr2.symm measurableSet_Ioc
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hi1 : ∫ u in (1 : ℝ)..(3 / 2 : ℝ), (if u ≤ 3 / 2 then u - 1 else 2 - u) = 1 / 8 := by
    have hcongr1 : ∫ u in (1 : ℝ)..(3 / 2 : ℝ), (if u ≤ 3 / 2 then u - 1 else 2 - u) =
        ∫ u in (1 : ℝ)..(3 / 2 : ℝ), (u - 1) :=
      intervalIntegral.integral_congr fun u hu => by rw [Set.uIcc_of_le (by norm_num)] at hu; simp [hu.2]
    rw [hcongr1]
    have hd : ∀ u ∈ Set.uIcc (1 : ℝ) (3 / 2), HasDerivAt (fun x : ℝ => (x - 1) ^ 2 / 2) (u - 1) u := by
      intro u _
      have h := (((hasDerivAt_id u).sub_const 1).pow 2).div_const 2
      exact h.congr_deriv (by simp)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun u : ℝ => u - 1).intervalIntegrable _ _)]
    norm_num
  have hi2 : ∫ u in (3 / 2 : ℝ)..(2 : ℝ), (if u ≤ 3 / 2 then u - 1 else 2 - u) = 1 / 8 := by
    have hcongr : ∫ u in (3 / 2 : ℝ)..(2 : ℝ), (if u ≤ 3 / 2 then u - 1 else 2 - u) =
        ∫ u in (3 / 2 : ℝ)..(2 : ℝ), (2 - u) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with u hu
      rw [Set.uIoc_of_le (by norm_num)] at hu; simp [not_le.mpr hu.1]
    rw [hcongr]
    have hd : ∀ u ∈ Set.uIcc (3 / 2 : ℝ) 2, HasDerivAt (fun x : ℝ => -((2 - x) ^ 2 / 2)) (2 - u) u := by
      intro u _
      have h := ((((hasDerivAt_const u (2 : ℝ)).sub (hasDerivAt_id u)).pow 2).div_const 2).neg
      exact h.congr_deriv (by simp; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun u : ℝ => (2 : ℝ) - u).intervalIntegrable _ _)]
    norm_num
  rw [hi1, hi2]; norm_num

/-- **Uniform `1 / 4` Bound on `‖dyadicKernel s‖` for ALL `-1 < Re(s) ≤ 1`** (including `s = 0`
and every critical-strip zero `ρ`, completely eliminating any `1 / |ρ|` blowup near `0`!). -/
theorem norm_dyadicKernel_le_quarter {s : ℂ} (hlo : -1 < s.re) (hhi : s.re ≤ 1) :
    ‖dyadicKernel s‖ ≤ 1 / 4 := by
  rw [dyadicKernel_eq_integral hlo]
  have hint_w : IntervalIntegrable (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u) volume (1 : ℝ) 2 := by
    have h1 : IntervalIntegrable (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u) volume (1 : ℝ) (3 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine ((by fun_prop : Continuous fun u : ℝ => u - 1).continuousOn).congr fun u hu => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hu; simp [hu.2]
    have h2 : IntervalIntegrable (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u) volume (3 / 2 : ℝ) 2 := by
      have hcongr2 : Set.EqOn (fun u : ℝ => if u ≤ 3 / 2 then u - 1 else 2 - u)
          (fun u : ℝ => (2 : ℝ) - u) (Set.Ioc (3 / 2) 2) := fun u hu => by simp [not_le.mpr hu.1]
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr ?_
      refine IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        ((by fun_prop : Continuous fun u : ℝ => (2 : ℝ) - u).intervalIntegrable _ _))
        hcongr2.symm measurableSet_Ioc
    exact h1.trans h2
  have hint_f : IntervalIntegrable
      (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)) volume (1 : ℝ) 2 := by
    have hpow_c : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (s - 1)) (Set.Icc 1 2) := fun u hu =>
      (Complex.continuousAt_ofReal_cpow_const u (s - 1) (.inr (by linarith [hu.1] : u ≠ 0))).continuousWithinAt
    have h1 : IntervalIntegrable (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1))
        volume (1 : ℝ) (3 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine (((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ => u - 1)).continuousOn).mul
        (hpow_c.mono fun u hu => by rw [Set.uIcc_of_le (by norm_num)] at hu; exact ⟨hu.1, by linarith [hu.2]⟩)).congr ?_
      intro u hu; rw [Set.uIcc_of_le (by norm_num)] at hu; simp [hu.2]
    have h2 : IntervalIntegrable (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1))
        volume (3 / 2 : ℝ) 2 := by
      have hcongr2 : Set.EqOn
          (fun u : ℝ => ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1))
          (fun u : ℝ => ((2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)) (Set.Ioc (3 / 2) 2) := fun u hu => by
        simp [not_le.mpr hu.1]
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr ?_
      refine IntegrableOn.congr_fun ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        ((((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ => (2 : ℝ) - u)).continuousOn).mul
          (hpow_c.mono fun u hu => by rw [Set.uIcc_of_le (by norm_num)] at hu; exact ⟨by linarith [hu.1], hu.2⟩)).intervalIntegrable))
        hcongr2.symm measurableSet_Ioc
    exact h1.trans h2
  calc ‖∫ u in (1 : ℝ)..2, ((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)‖
      ≤ ∫ u in (1 : ℝ)..2, ‖((if u ≤ 3 / 2 then u - 1 else 2 - u : ℝ) : ℂ) * (u : ℂ) ^ (s - 1)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ u in (1 : ℝ)..2, (if u ≤ 3 / 2 then u - 1 else 2 - u) := by
        refine intervalIntegral.integral_mono_on (by norm_num) hint_f.norm hint_w fun u hu => ?_
        have hu1 : 1 ≤ u := hu.1
        have hu2 : u ≤ 2 := hu.2
        have hw_nn : 0 ≤ (if u ≤ 3 / 2 then u - 1 else 2 - u) := by split_ifs <;> linarith
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw_nn,
          Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
        have hre : (s - 1).re = s.re - 1 := by simp
        rw [hre]
        have hpow : u ^ (s.re - 1) ≤ 1 := by
          calc u ^ (s.re - 1) ≤ u ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
            _ = 1 := Real.rpow_zero u
        nlinarith
    _ = 1 / 4 := integral_tent_eq_quarter

/-- **Sharp Inverse-Square Bound on `‖dyadicKernel s‖` across `-1 / 2 ≤ Re(s) ≤ 1`**:
`‖dyadicKernel s‖ ≤ 20 / (1 + s.im ^ 2)` (combining `≤ 1/4` near `s = 0` with `≤ 10 / s.im ^ 2`
for `|s.im| ≥ 1`). -/
theorem norm_dyadicKernel_le_inv_sq {s : ℂ} (hlo : -1 / 2 ≤ s.re) (hhi : s.re ≤ 1) :
    ‖dyadicKernel s‖ ≤ 20 / (1 + s.im ^ 2) := by
  by_cases him : |s.im| ≤ 1
  · have hq := norm_dyadicKernel_le_quarter (by linarith) hhi
    have hsq : s.im ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg s.im]
    have h1 : (1 / 4 : ℝ) ≤ 20 / (1 + s.im ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    exact hq.trans h1
  · push Not at him
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at him; linarith
    rw [dyadicKernel_eq_div hs0, norm_div, norm_mul]
    have hW_le : ‖dyadicW s‖ ≤ 10 := by
      unfold dyadicW
      have h1 := norm_add_le ((2 : ℂ) ^ (s + 1) - 2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1)) 1
      have h2 := norm_sub_le ((2 : ℂ) ^ (s + 1)) (2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1))
      have hn2 : ‖(2 : ℂ) ^ (s + 1)‖ ≤ 4 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
        have hre : (s + 1).re = s.re + 1 := by simp
        rw [hre]
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : s.re + 1 ≤ 2)).trans_eq
          (by rw [Real.rpow_two]; norm_num)
      have hn32 : ‖2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1)‖ ≤ 9 / 2 := by
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
        have hre : (s + 1).re = s.re + 1 := by simp
        rw [hre]
        have hle : (3 / 2 : ℝ) ^ (s.re + 1) ≤ 9 / 4 := by
          calc (3 / 2 : ℝ) ^ (s.re + 1) ≤ (3 / 2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = (3 / 2 : ℝ) ^ (2 : ℕ) := Real.rpow_two (3 / 2 : ℝ)
            _ = 9 / 4 := by norm_num
        linarith
      rw [norm_one] at h1
      linarith
    have hd1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hd2 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
    have hprod : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
      rw [← sq_abs, sq]; exact mul_le_mul hd1 hd2 (abs_nonneg _) (norm_nonneg _)
    have hsq_gt1 : 1 < s.im ^ 2 := by rw [← sq_abs]; nlinarith
    calc ‖dyadicW s‖ / (‖s‖ * ‖s + 1‖)
        ≤ 10 / s.im ^ 2 := div_le_div₀ (by norm_num) hW_le (by linarith) hprod
      _ ≤ 20 / (1 + s.im ^ 2) := by
          rw [div_le_div_iff₀ (by linarith) (by positivity)]; nlinarith

/-- Uniform horizontal bound `‖dyadicKernel s‖ ≤ 16 / s.im ^ 2` for `-1 / 2 ≤ Re(s) ≤ 2` and
`1 ≤ |s.im|`. -/
lemma norm_dyadicKernel_horiz_le {s : ℂ} (_hlo : -1 / 2 ≤ s.re) (hhi : s.re ≤ 2) (him : 1 ≤ |s.im|) :
    ‖dyadicKernel s‖ ≤ 16 / s.im ^ 2 := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_im, abs_zero] at him; linarith
  rw [dyadicKernel_eq_div hs0, norm_div, norm_mul]
  have hW_le : ‖dyadicW s‖ ≤ 16 := by
    unfold dyadicW
    have h1 := norm_add_le ((2 : ℂ) ^ (s + 1) - 2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1)) 1
    have h2 := norm_sub_le ((2 : ℂ) ^ (s + 1)) (2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1))
    have hn2 : ‖(2 : ℂ) ^ (s + 1)‖ ≤ 8 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      have hre : (s + 1).re = s.re + 1 := by simp
      rw [hre]
      exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : s.re + 1 ≤ 3)).trans_eq
        (by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num)
    have hn32 : ‖2 * ((3 / 2 : ℝ) : ℂ) ^ (s + 1)‖ ≤ 27 / 4 := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      have hre : (s + 1).re = s.re + 1 := by simp
      rw [hre]
      have hle : (3 / 2 : ℝ) ^ (s.re + 1) ≤ 27 / 8 := by
        calc (3 / 2 : ℝ) ^ (s.re + 1) ≤ (3 / 2 : ℝ) ^ (3 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = (3 / 2 : ℝ) ^ (3 : ℕ) := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          _ = 27 / 8 := by norm_num
      linarith
    rw [norm_one] at h1
    linarith
  have hd1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hd2 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have hprod : s.im ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← sq_abs, sq]; exact mul_le_mul hd1 hd2 (abs_nonneg _) (norm_nonneg _)
  have hsq_pos : 0 < s.im ^ 2 := by rw [← sq_abs]; positivity
  exact div_le_div₀ (by norm_num) hW_le hsq_pos hprod

/-- **EXACT SIEGEL-ZERO CANCELLATION LOWER BOUND**:
for any real `β ∈ (0, 1)`, any `X ≥ 1`, and any unit-modulus coefficient `c : ℂ` (`‖c‖ ≤ 1`),
`(1 / 4) * X ^ 2 - (c * (X : ℂ) ^ ((β : ℂ) + 1) * dyadicKernel (β : ℂ)).re ≥
  (1 / 4) * X ^ 2 * (1 - X ^ (β - 1))`! -/
theorem siegel_main_sub_kernel_ge {β X : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hX : 1 ≤ X)
    {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (1 / 4 : ℝ) * X ^ 2 * (1 - X ^ (β - 1)) ≤
      (1 / 4 : ℝ) * X ^ 2 - (c * (X : ℂ) ^ ((β : ℂ) + 1) * dyadicKernel (β : ℂ)).re := by
  have hX0 : 0 < X := by linarith
  have hnorm : ‖c * (X : ℂ) ^ ((β : ℂ) + 1) * dyadicKernel (β : ℂ)‖ ≤ (1 / 4 : ℝ) * X ^ (β + 1) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
    have hre : ((β : ℂ) + 1).re = β + 1 := by simp
    rw [hre]
    have hK := norm_dyadicKernel_le_quarter (s := (β : ℂ)) (by simp; linarith) (by simp [hβ1.le])
    calc ‖c‖ * X ^ (β + 1) * ‖dyadicKernel (β : ℂ)‖
        ≤ 1 * X ^ (β + 1) * (1 / 4) := by gcongr
      _ = (1 / 4 : ℝ) * X ^ (β + 1) := by ring
  have hre_le : (c * (X : ℂ) ^ ((β : ℂ) + 1) * dyadicKernel (β : ℂ)).re ≤
      (1 / 4 : ℝ) * X ^ (β + 1) :=
    ((le_abs_self _).trans (Complex.abs_re_le_norm _)).trans hnorm
  have hpow : X ^ 2 * X ^ (β - 1) = X ^ (β + 1) := by
    rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; ring
  nlinarith

/-! ### Unconditional Smoothed Dyadic Explicit Formulas (`0` Assumptions!) -/

/-- Holomorphic quotient helper (matching `Stage9ExplicitFormula`): removes a finite zero set `Z`
with exact multiplicities from an analytic function on an open set `U`. -/
private lemma exists_holomorphic_quotient_by_zeros_local {f : ℂ → ℂ} {U : Set ℂ}
    (hf_an : AnalyticOnNhd ℂ f U) (hntop : ∀ z ∈ U, analyticOrderAt f z ≠ ⊤)
    (Z : Finset ℂ) (hZ_all : ∀ z ∈ U, f z = 0 → z ∈ Z) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ (∀ z ∈ U, g z ≠ 0) ∧
      ∀ z ∈ U, f z = g z * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ := by
  classical
  let Q : ℂ → ℂ := fun z => ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ
  have hQ_diff : Differentiable ℂ Q := fun z =>
    DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub (differentiableAt_const ρ)).pow _
  let g : ℂ → ℂ := fun w => limUnder (𝓝[≠] w) (fun z => f z / Q z)
  have hlocal : ∀ w ∈ U, ∃ q : ℂ → ℂ, AnalyticAt ℂ q w ∧ q w ≠ 0 ∧
      g =ᶠ[𝓝 w] q ∧ f w = q w * Q w := by
    intro w hwU
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (hf_an w hwU).analyticOrderAt_ne_top.mp (hntop w hwU)
    have hQ_loc : ∃ Q₁ : ℂ → ℂ, AnalyticAt ℂ Q₁ w ∧ Q₁ w ≠ 0 ∧
        ∀ z : ℂ, Q z = (z - w) ^ analyticOrderNatAt f w * Q₁ z := by
      by_cases hwZ : w ∈ Z
      · refine ⟨fun z => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt f ρ, ?_, ?_, fun z => ?_⟩
        · have hd : Differentiable ℂ (fun z : ℂ => ∏ ρ ∈ Z.erase w, (z - ρ) ^ analyticOrderNatAt f ρ) :=
            fun z => DifferentiableAt.fun_finsetProd fun ρ _ =>
              (differentiableAt_id.sub (differentiableAt_const ρ)).pow _
          exact hd.differentiableOn.analyticAt Filter.univ_mem
        · exact Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
            pow_ne_zero _ (sub_ne_zero.mpr (Finset.mem_erase.mp hρ).1.symm)
        · exact (Finset.mul_prod_erase Z (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ) hwZ).symm
      · have hfw_ne : f w ≠ 0 := fun hw0 => hwZ (hZ_all w hwU hw0)
        have hord0 : analyticOrderNatAt f w = 0 := by
          have h0 : analyticOrderAt f w = 0 := (hf_an w hwU).analyticOrderAt_eq_zero.mpr hfw_ne
          simp [analyticOrderNatAt, h0]
        refine ⟨Q, hQ_diff.differentiableOn.analyticAt Filter.univ_mem, ?_, fun z => by simp [hord0]⟩
        exact Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
          pow_ne_zero _ (sub_ne_zero.mpr fun heq => hwZ (heq ▸ hρ))
    obtain ⟨Q₁, hQ₁_an, hQ₁_ne, hQ₁_eq⟩ := hQ_loc
    let q : ℂ → ℂ := fun z => h z / Q₁ z
    have hq_an : AnalyticAt ℂ q w := hh_an.div hQ₁_an hQ₁_ne
    have hq_ne : q w ≠ 0 := div_ne_zero hh_ne hQ₁_ne
    have hev_all : ∀ᶠ z in 𝓝 w,
        f z = (z - w) ^ analyticOrderNatAt f w * h z ∧ Q₁ z ≠ 0 ∧ ContinuousAt q z := by
      filter_upwards [hh_eq, hQ₁_an.continuousAt.eventually_ne hQ₁_ne,
        hq_an.eventually_analyticAt.mono fun z hz => hz.continuousAt] with z h1 h2 h3
      exact ⟨by simpa [smul_eq_mul] using h1, h2, h3⟩
    obtain ⟨V, hV_sub, hV_open, hwV⟩ := _root_.eventually_nhds_iff.mp hev_all
    have hfp : ∀ z ∈ V, z ≠ w → f z / Q z = q z := by
      intro z hzV hzw
      obtain ⟨h1, h2, _⟩ := hV_sub z hzV
      have hpow_ne : (z - w) ^ analyticOrderNatAt f w ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzw)
      rw [h1, hQ₁_eq z]; dsimp only [q]; field_simp [hpow_ne, h2]
    have hg_eq : ∀ z ∈ V, g z = q z := by
      intro z hzV
      have htend_q : Tendsto q (𝓝[≠] z) (𝓝 (q z)) :=
        (hV_sub z hzV).2.2.tendsto.mono_left nhdsWithin_le_nhds
      have htend_fp : Tendsto (fun u => f u / Q u) (𝓝[≠] z) (𝓝 (q z)) := by
        refine htend_q.congr' ?_
        have hmem_V : V ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hV_open.mem_nhds hzV)
        have hmem_ne : ({w}ᶜ : Set ℂ) ∈ 𝓝[≠] z := by
          by_cases hzw : z = w
          · subst hzw; exact self_mem_nhdsWithin
          · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzw)
        filter_upwards [Filter.inter_mem hmem_V hmem_ne] with u ⟨huV, huw⟩
        exact (hfp u huV huw).symm
      exact htend_fp.limUnder_eq
    have hfw : f w = q w * Q w := by
      obtain ⟨h1, h2, _⟩ := hV_sub w hwV
      rw [h1, hQ₁_eq w]; dsimp only [q]; field_simp [h2]
    exact ⟨q, hq_an, hq_ne, Filter.eventually_of_mem (hV_open.mem_nhds hwV) hg_eq, hfw⟩
  refine ⟨g, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨q, hq_an, _, heq, _⟩ := hlocal w hw
    exact (hq_an.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt
  · obtain ⟨q, _, hq_ne, heq, _⟩ := hlocal w hw
    rwa [heq.self_of_nhds]
  · obtain ⟨q, _, _, heq, hfw⟩ := hlocal w hw
    rwa [heq.self_of_nhds]

open Classical in
/-- Exact meromorphic regularization of `negLogDerivL ψ` on `closedRect (-1/2) c (-T') T'` for any
primitive `ψ ≠ 1` mod `q` when `1 < c`, `0 < T'`, and no zero of `completedLFunction ψ` lies on
`Im(s) = ±T'`:
- for odd `ψ`: poles are ONLY `Z := lZerosInBox ψ T'` with residues `-m_ρ`;
- for even `ψ`: poles are `insert 0 Z` with residue `-1` at `0` and `-m_ρ` at `ρ ∈ Z`. -/
private lemma exists_meromorphic_negLogDerivL_rect_primitive {q : ℕ} [NeZero q]
    {ψ : DirichletCharacter ℂ q} (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1) {c T' : ℝ}
    (hc : 1 < c) (hT' : 0 < T')
    (havoid : ∀ ρ : ℂ, DirichletCharacter.completedLFunction ψ ρ = 0 → T' ≠ ρ.im ∧ -T' ≠ ρ.im) :
    let Z : Finset ℂ := lZerosInBox ψ T'
    let J : Finset ℂ := if ψ.Even then insert (0 : ℂ) Z else Z
    let a : ℂ → ℂ := fun p => if p = 0 then (-1 : ℂ) else -(lZeroMult ψ p : ℂ)
    ∃ L : ℂ → ℂ,
      (∀ p ∈ J, p ∈ Stage5ContourExplicit.openRect (-1 / 2) c (-T') T') ∧
      DifferentiableOn ℂ (fun s => L s - ∑ p ∈ J, a p / (s - p))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') ∧
      (∀ s ∈ Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T', s ∉ J →
        L s = Stage3ZeroFreeRegion.negLogDerivL ψ s) := by
  classical
  intro Z J a
  have h0_not_Z : (0 : ℂ) ∉ Z := fun h => by
    have hm := mem_lZerosInBox.mp h; simp at hm
  have hZ_open : ∀ ρ ∈ Z, ρ ∈ Stage5ContourExplicit.openRect (-1 / 2) c (-T') T' ∧ ρ ≠ 0 := by
    intro ρ hρ
    have hm := mem_lZerosInBox.mp hρ
    have hΛ0 := (completedLFunction_eq_zero_iff_LFunction_of_re_pos ψ hm.1).mpr hm.2.2.1
    have hne := havoid ρ hΛ0
    have him_lt : |ρ.im| < T' := lt_of_le_of_ne hm.2.2.2 fun hEq => by
      rcases (abs_eq hT'.le).mp hEq with hp | hn
      · exact hne.1 hp.symm
      · exact hne.2 (by linarith)
    refine ⟨⟨⟨by linarith [hm.1], by linarith [hm.2.1]⟩, abs_lt.mp him_lt⟩, ?_⟩
    intro h0; have h0re := hm.1; rw [h0, Complex.zero_re] at h0re; exact lt_irrefl 0 h0re
  set Z_big : Finset ℂ := lZerosInBox ψ (T' + 1)
  set Z_out : Finset ℂ := Z_big.filter fun ρ => T' < |ρ.im|
  obtain ⟨δ, hδ_pos, hδ_lt_half, hδ_avoid⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∀ ρ ∈ Z_out, T' + δ < |ρ.im| := by
    by_cases hemp : Z_out = ∅
    · exact ⟨1 / 4, by norm_num, by norm_num, fun ρ hρ => by rw [hemp] at hρ; exact absurd hρ (Finset.notMem_empty _)⟩
    · have hne : Z_out.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      set m := Z_out.inf' hne fun ρ => |ρ.im| - T'
      have hm_pos : 0 < m := (Finset.lt_inf'_iff hne).mpr fun ρ hρ => sub_pos.mpr (Finset.mem_filter.mp hρ).2
      refine ⟨min (1 / 4) (m / 2), lt_min (by norm_num) (by linarith),
        (min_le_left _ _).trans_lt (by norm_num), fun ρ hρ => ?_⟩
      have h1 : m ≤ |ρ.im| - T' := Finset.inf'_le (fun w => |w.im| - T') hρ
      have h2 : min (1 / 4) (m / 2) ≤ m / 2 := min_le_right _ _
      linarith
  set U : Set ℂ := {z : ℂ | -3 / 4 < z.re ∧ z.re < c + 1 ∧ |z.im| < T' + δ}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hrect_sub_U : Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' ⊆ U := fun z hz =>
    ⟨by linarith [hz.1.1], by linarith [hz.1.2], by have := abs_le.mpr hz.2; linarith⟩
  have hΛ_an : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction ψ) U :=
    ((differentiable_completedLFunction_prim hψ).differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ U)
  have hΛ_ntop : ∀ z ∈ U, analyticOrderAt (DirichletCharacter.completedLFunction ψ) z ≠ ⊤ := fun z _ htop => by
    have h0 := ((differentiable_completedLFunction_prim hψ).differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ 0)
    exact completedLFunction_zero_ne_zero hprim hψ h0
  have hZ_all : ∀ z ∈ U, DirichletCharacter.completedLFunction ψ z = 0 → z ∈ Z := by
    intro z hz h0
    obtain ⟨h0re, h1re, hL0⟩ := (completedLFunction_eq_zero_iff_critical_strip_LFunction_zero hprim hψ z).mp h0
    have hle_big : |z.im| ≤ T' + 1 := by linarith [hz.2.2, hδ_lt_half]
    have hmem_big : z ∈ Z_big := mem_lZerosInBox.mpr ⟨h0re, h1re, hL0, hle_big⟩
    have hle_T' : |z.im| ≤ T' := by
      by_contra hgt; push Not at hgt
      have hmem_out : z ∈ Z_out := Finset.mem_filter.mpr ⟨hmem_big, hgt⟩
      linarith [hδ_avoid z hmem_out, hz.2.2]
    exact mem_lZerosInBox.mpr ⟨h0re, h1re, hL0, hle_T'⟩
  obtain ⟨g, hg_diff, hg_nz, hΛ_fac⟩ := exists_holomorphic_quotient_by_zeros_local hΛ_an hΛ_ntop Z hZ_all
  have hg_ld_diff : DifferentiableOn ℂ (logDeriv g) U := by
    have hgd : DifferentiableOn ℂ (deriv g) U := hg_diff.deriv hU_open
    have hld_eq : logDeriv g = fun s => deriv g s / g s := funext fun s => logDeriv_apply g s
    rw [hld_eq]; exact hgd.div hg_diff hg_nz
  let H : ℂ → ℂ := fun s =>
    -logDeriv g s - ((Real.log Real.pi / 2 : ℝ) : ℂ) +
      (1 / 2 : ℂ) * Complex.digamma (if ψ.Even then s / 2 + 1 else (s + 1) / 2)
  have hH_diff : DifferentiableOn ℂ H (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') := by
    have hdig_d : DifferentiableOn ℂ
        (fun s : ℂ => Complex.digamma (if ψ.Even then s / 2 + 1 else (s + 1) / 2))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') := by
      have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
      by_cases he : ψ.Even
      · simp only [he, ↓reduceIte]
        intro s hs
        have hre : 0 < (s / 2 + 1).re := by simp; linarith [hs.1.1]
        have hd1 : DifferentiableAt ℂ Complex.digamma (s / 2 + 1) :=
          (Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos (s / 2 + 1) hre).differentiableAt (hopen.mem_nhds hre)
        exact (hd1.comp s ((differentiableAt_id.div_const (2 : ℂ)).add (differentiableAt_const 1))).differentiableWithinAt
      · simp only [he, ↓reduceIte]
        intro s hs
        have hre : 0 < ((s + 1) / 2).re := by simp; linarith [hs.1.1]
        have hd1 : DifferentiableAt ℂ Complex.digamma ((s + 1) / 2) :=
          (Stage7VonMangoldtExplicit.differentiableOn_digamma_re_pos ((s + 1) / 2) hre).differentiableAt (hopen.mem_nhds hre)
        exact (hd1.comp s ((differentiableAt_id.add (differentiableAt_const 1)).div_const (2 : ℂ))).differentiableWithinAt
    exact (((hg_ld_diff.mono hrect_sub_U).neg).sub (differentiableOn_const _)).add
      ((differentiableOn_const _).mul hdig_d)
  let L : ℂ → ℂ := fun s => H s + ∑ p ∈ J, a p / (s - p)
  -- Helper: for `ρ ∈ Z`, `lZeroMult ψ ρ = analyticOrderNatAt (completedLFunction ψ) ρ`
  have hmult_eq : ∀ ρ ∈ Z, lZeroMult ψ ρ = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ := by
    intro ρ hρ
    have h0 := (mem_lZerosInBox.mp hρ).1
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev_Λ : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 ρ]
        fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z := by
      filter_upwards [hopen.mem_nhds h0] with z hz
      exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ hz
    have hL_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) ρ :=
      ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ) ρ (Set.mem_univ ρ)
    have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hG_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor ψ) ρ := by
      refine DifferentiableOn.analyticAt ?_ (hopen.mem_nhds h0)
      intro z hz
      have hz_re : 0 < z.re := hz
      rcases ψ.even_or_odd with he | ho
      · have hfun : DirichletCharacter.gammaFactor ψ =
            fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) :=
          funext fun w => by rw [he.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
        rw [hfun]
        have h1 : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2))) z := by fun_prop
        have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
          (Complex.differentiableAt_Gamma (z / 2) fun k hEq => by
            have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
            (differentiableAt_id.div_const 2)
        exact (h1.mul h2).differentiableWithinAt
      · have hfun : DirichletCharacter.gammaFactor ψ =
            fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2)) * Complex.Gamma ((w + 1) / 2) :=
          funext fun w => by rw [ho.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
        rw [hfun]
        have h1 : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2))) z := by fun_prop
        have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma ((w + 1) / 2)) z :=
          (Complex.differentiableAt_Gamma ((z + 1) / 2) fun k hEq => by
            have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
            ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2)
        exact (h1.mul h2).differentiableWithinAt
    have hG_ne := gammaFactor_ne_zero_of_re_pos ψ h0
    have heq : analyticOrderAt (DirichletCharacter.completedLFunction ψ) ρ =
        analyticOrderAt (fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z) ρ :=
      analyticOrderAt_congr hev_Λ
    unfold lZeroMult
    simp only [analyticOrderNatAt, heq]
    exact (analyticOrderNatAt_mul_of_ne_zero hL_an hG_an hG_ne).symm
  refine ⟨L, ?_, ?_, ?_⟩
  · intro p hp
    dsimp only [J] at hp
    by_cases he : ψ.Even
    · rw [if_pos he] at hp
      rcases Finset.mem_insert.mp hp with rfl | hpZ
      · exact ⟨⟨by simp; norm_num, by simp; linarith⟩, by simp [hT']⟩
      · exact (hZ_open p hpZ).1
    · rw [if_neg he] at hp
      exact (hZ_open p hp).1
  · have hEq : (fun s => L s - ∑ p ∈ J, a p / (s - p)) = H := funext fun s => by dsimp only [L]; ring
    rw [hEq]; exact hH_diff
  · intro s hs hsJ
    have hsU : s ∈ U := hrect_sub_U hs
    have hsZ : s ∉ Z := fun h => hsJ (by
      dsimp only [J]
      split_ifs
      · exact Finset.mem_insert_of_mem h
      · exact h)
    have hΛ_ne : DirichletCharacter.completedLFunction ψ s ≠ 0 := fun h0 => hsZ (hZ_all s hsU h0)
    let Q : ℂ → ℂ := fun z => ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ
    have hQ_ne : Q s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun hEq => hsZ (hEq ▸ hρ))
    have hQ_diff : DifferentiableAt ℂ Q s :=
      DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub (differentiableAt_const ρ)).pow _
    have hg_d : DifferentiableAt ℂ g s := (hg_diff s hsU).differentiableAt (hU_open.mem_nhds hsU)
    have hΛ_ev : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 s] fun z => g z * Q z :=
      Filter.eventually_of_mem (hU_open.mem_nhds hsU) hΛ_fac
    have hld_Q : logDeriv Q s = ∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) / (s - ρ) := by
      have h1 := logDeriv_prod (s := Z)
        (f := fun ρ (z : ℂ) => (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ) (x := s)
        (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr fun hEq => hsZ (hEq ▸ hρ)))
        (fun ρ _ => (differentiableAt_id.sub (differentiableAt_const ρ)).pow _)
      change logDeriv Q s = _
      dsimp only [Q]; rw [h1]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hsub_ne : s - ρ ≠ 0 := sub_ne_zero.mpr fun hEq => hsZ (hEq ▸ hρ)
      rw [logDeriv_apply, hmult_eq ρ hρ]
      have hd : HasDerivAt
          (fun z : ℂ => (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ)
          ((analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ : ℂ) *
            (s - ρ) ^ (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ - 1)) s := by
        simpa using ((hasDerivAt_id s).sub_const ρ).fun_pow
          (analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ)
      rw [hd.deriv]
      cases hm : analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ with
      | zero => simp
      | succ k => rw [Nat.succ_sub_one, pow_succ]; field_simp [hsub_ne]
    have hld_Λ : logDeriv (DirichletCharacter.completedLFunction ψ) s =
        logDeriv g s + ∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) / (s - ρ) := by
      rw [← hld_Q, logDeriv_apply, logDeriv_apply, logDeriv_apply, hΛ_ev.deriv_eq,
        (hg_d.hasDerivAt.fun_mul hQ_diff.hasDerivAt).deriv]
      have hself := hΛ_ev.self_of_nhds; dsimp only at hself; rw [hself]
      have hgne := hg_nz s hsU
      field_simp [hgne, hQ_ne]
    rcases ψ.even_or_odd with he | ho
    · have hs0 : s ≠ 0 := fun h => hsJ (by dsimp only [J]; rw [if_pos he]; exact h ▸ Finset.mem_insert_self 0 Z)
      have hsum_J : ∑ p ∈ J, a p / (s - p) =
          -(1 / s) - ∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) / (s - ρ) := by
        dsimp only [J, a]; rw [if_pos he, Finset.sum_insert h0_not_Z, if_pos rfl, sub_zero, neg_div]
        have hZ_terms : ∑ ρ ∈ Z, (if ρ = 0 then (-1 : ℂ) else -(lZeroMult ψ ρ : ℂ)) / (s - ρ) =
            -(∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) / (s - ρ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          rw [if_neg (hZ_open ρ hρ).2, neg_div]
        rw [hZ_terms]; ring
      rw [negLogDerivL_eq_neg_logDeriv_completedL_even he hψ (by linarith [hs.1.1]) hs0 hΛ_ne, hld_Λ]
      dsimp only [L, H]; rw [if_pos he, hsum_J]; ring
    · have hne_ev : ¬ ψ.Even := fun he => by
        have h1 : ψ (-1) = 1 := he
        have h2 : ψ (-1) = -1 := ho
        rw [h1] at h2; norm_num at h2
      have hsum_J : ∑ p ∈ J, a p / (s - p) = -(∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) / (s - ρ)) := by
        dsimp only [J, a]; rw [if_neg hne_ev, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [if_neg (hZ_open ρ hρ).2, neg_div]
      rw [negLogDerivL_eq_neg_logDeriv_completedL_odd ho hψ (by linarith [hs.1.1]) hΛ_ne, hld_Λ]
      dsimp only [L, H]; rw [if_neg hne_ev, hsum_J]; ring

/-- **UNCONDITIONAL SMOOTHED DYADIC EXPLICIT FORMULA FOR EVERY PRIMITIVE `ψ ≠ 1` (`0` ASSUMPTIONS!)**:
there exists a universal constant `C > 0` such that for EVERY `q [NeZero q]`, EVERY primitive
`ψ ≠ 1` mod `q`, EVERY `X ≥ 4`, and EVERY `T ≥ 4`:
`‖dyadic2 (psi1Char ψ) X - (-∑ ρ ∈ lZerosInBox ψ T, m_ρ * X^{ρ+1} * dyadicKernel ρ)‖ ≤
  C * (X^2 * (Real.log (q * X) + Real.log T)^2 / T + X * Real.log (q * X))`. -/
theorem explicit_formula_dyadic2_psi1Char_primitive :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
      ψ.IsPrimitive → ψ ≠ 1 → ∀ X T : ℝ, 4 ≤ X → 4 ≤ T →
        ‖dyadic2 (Stage4ExplicitFormula.psi1Char ψ) X -
            (-(∑ ρ ∈ lZerosInBox ψ T, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ))‖ ≤
          C * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T + X * Real.log ((q : ℝ) * X)) := by
  classical
  obtain ⟨c_gap, hc_gap, C_h, hCh_pos, hgood⟩ := exists_good_contour_height_primitive
  obtain ⟨C_L, hCL_pos, hleft_bd⟩ := norm_negLogDerivL_neg_half_line_le_primitive
  obtain ⟨C_N, hCN_pos, hshort⟩ := lFunctionZeroCount_short_interval_le
  set C : ℝ := 2000 + 250 * C_h + 100 * C_L + 64 * C_N
  refine ⟨C, by positivity, fun q _ ψ hprim hψ X T hX hT => ?_⟩
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX0.ne'
  have hlogX_gt1 : 1 < Real.log X := by
    have h4 : Real.exp 1 < X := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlogT_gt1 : 1 < Real.log T := by
    have h4 : Real.exp 1 < T := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlogqX_gt1 : 1 < Real.log ((q : ℝ) * X) :=
    hlogX_gt1.trans_le (Real.log_le_log hX0 (by nlinarith))
  have hlogqT_le : Real.log ((q : ℝ) * T) ≤ Real.log ((q : ℝ) * X) + Real.log T := by
    rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul (by positivity) hX0.ne']
    linarith
  -- Choose `c = 1 + 1 / Real.log X ∈ (1, 2)` and good height `T' ∈ [T, T + 1]`
  set c : ℝ := 1 + 1 / Real.log X
  have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos (zero_lt_one.trans hlogX_gt1)]
  have hc_lt2 : c < 2 := by
    dsimp only [c]
    have h1 : 1 / Real.log X < 1 := (div_lt_one (zero_lt_one.trans hlogX_gt1)).mpr hlogX_gt1
    linarith
  have hXc_eq : X ^ c = X * Real.exp 1 := by
    dsimp only [c]
    rw [Real.rpow_add hX0, Real.rpow_one, Real.rpow_def_of_pos hX0,
      mul_one_div_cancel (zero_lt_one.trans hlogX_gt1).ne']
  have hXc1_le : X ^ (c + 1) ≤ 3 * X ^ 2 := by
    rw [Real.rpow_add hX0, Real.rpow_one, hXc_eq]
    have he := Real.exp_one_lt_d9; nlinarith
  obtain ⟨T', hT'_mem, hT'_gap, hT'_bd⟩ := hgood q ψ hprim hψ T hT
  have hT'_geT : T ≤ T' := hT'_mem.1
  have hT'_le : T' ≤ T + 1 := hT'_mem.2
  have hT'_pos : 0 < T' := by linarith
  have hlogqT_pos : 0 < Real.log ((q : ℝ) * T) := Real.log_pos (by nlinarith)
  have havoid : ∀ ρ : ℂ, DirichletCharacter.completedLFunction ψ ρ = 0 → T' ≠ ρ.im ∧ -T' ≠ ρ.im := by
    intro ρ hρ
    have hg := hT'_gap ρ hρ
    have hpos : 0 < c_gap / Real.log ((q : ℝ) * T) := div_pos hc_gap hlogqT_pos
    exact ⟨fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.1],
           fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.2]⟩
  -- Step 1: Truncated Perron approximation for `dyadic2 (psi1Char ψ) X` at `(c, T')`
  have hPerron_pt : ∀ α : ℝ, 1 ≤ α → α ≤ 2 →
      ‖Stage4ExplicitFormula.psi1Char ψ (α * X) -
        Stage4ExplicitFormula.truncatedPerronPsi1 ψ (α * X) c T'‖ ≤
        100 * (X ^ 2 * Real.log X / T) := by
    intro α hα1 hα2
    have h1 := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le ψ (mul_pos (by linarith) hX0) hc_gt1 hT'_pos
    have hpow : (α * X) ^ (c + 1) ≤ 24 * X ^ 2 := by
      rw [Real.mul_rpow (by linarith) hX0.le]
      have hαc : α ^ (c + 1) ≤ 8 := by
        calc α ^ (c + 1) ≤ (2 : ℝ) ^ (c + 1) := Real.rpow_le_rpow (by linarith) hα2 (by linarith)
          _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 8 := by rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      nlinarith [Real.rpow_nonneg hX0.le (c + 1)]
    have hc1 : c - 1 = 1 / Real.log X := by dsimp only [c]; ring
    have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    calc ‖Stage4ExplicitFormula.psi1Char ψ (α * X) -
            Stage4ExplicitFormula.truncatedPerronPsi1 ψ (α * X) c T'‖
        ≤ (6 * c / Real.pi) * (α * X) ^ (c + 1) / ((c - 1) * T') := h1
      _ ≤ (12 / 3) * (24 * X ^ 2) / ((1 / Real.log X) * T) := by
          rw [hc1]
          refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
          · exact mul_le_mul (div_le_div₀ (by linarith) (by linarith) (by norm_num) hpi3) hpow (by positivity) (by positivity)
          · exact mul_le_mul_of_nonneg_left hT'_geT (by positivity)
      _ = 96 * (X ^ 2 * Real.log X / T) := by
          field_simp [(zero_lt_one.trans hlogX_gt1).ne', hT0.ne']; ring
      _ ≤ 100 * (X ^ 2 * Real.log X / T) := by nlinarith [show 0 ≤ X ^ 2 * Real.log X / T by positivity]
  have hPerron_dy :
      ‖dyadic2 (Stage4ExplicitFormula.psi1Char ψ) X -
        dyadic2 (fun y => Stage4ExplicitFormula.truncatedPerronPsi1 ψ y c T') X‖ ≤
        400 * (X ^ 2 * Real.log X / T) := by
    unfold dyadic2
    set e2 := Stage4ExplicitFormula.psi1Char ψ (2 * X) - Stage4ExplicitFormula.truncatedPerronPsi1 ψ (2 * X) c T'
    set e32 := Stage4ExplicitFormula.psi1Char ψ ((3 / 2 : ℝ) * X) - Stage4ExplicitFormula.truncatedPerronPsi1 ψ ((3 / 2 : ℝ) * X) c T'
    set e1 := Stage4ExplicitFormula.psi1Char ψ X - Stage4ExplicitFormula.truncatedPerronPsi1 ψ X c T'
    have hrew : (Stage4ExplicitFormula.psi1Char ψ (2 * X) -
        2 * Stage4ExplicitFormula.psi1Char ψ ((3 / 2 : ℝ) * X) + Stage4ExplicitFormula.psi1Char ψ X) -
        (Stage4ExplicitFormula.truncatedPerronPsi1 ψ (2 * X) c T' -
        2 * Stage4ExplicitFormula.truncatedPerronPsi1 ψ ((3 / 2 : ℝ) * X) c T' +
        Stage4ExplicitFormula.truncatedPerronPsi1 ψ X c T') = e2 - 2 * e32 + e1 := by
      dsimp only [e2, e32, e1]; ring
    rw [hrew]
    have h1 := norm_add_le (e2 - 2 * e32) e1
    have h2 := norm_sub_le e2 (2 * e32)
    rw [norm_mul, Complex.norm_ofNat] at h2
    have hb2 := hPerron_pt 2 (by norm_num) le_rfl
    have hb32 := hPerron_pt (3 / 2) (by norm_num) (by norm_num)
    have hb1 : ‖e1‖ ≤ 100 * (X ^ 2 * Real.log X / T) := by
      simpa only [one_mul] using hPerron_pt 1 le_rfl (by norm_num)
    linarith
  -- Step 2: Meromorphic regularization + multiplicative contour shift with `W s = X^(s+1) * dyadicKernel s`!
  obtain ⟨L, hJ_open, hL_diff, hL_eq⟩ :=
    exists_meromorphic_negLogDerivL_rect_primitive hprim hψ hc_gt1 hT'_pos havoid
  set Z : Finset ℂ := lZerosInBox ψ T'
  set J : Finset ℂ := if ψ.Even then insert (0 : ℂ) Z else Z
  set a : ℂ → ℂ := fun p => if p = 0 then (-1 : ℂ) else -(lZeroMult ψ p : ℂ)
  let W : ℂ → ℂ := fun s => (X : ℂ) ^ (s + 1) * dyadicKernel s
  have hpow_diff : Differentiable ℂ (fun s : ℂ => (X : ℂ) ^ (s + 1)) := by
    have hEq : (fun s : ℂ => (X : ℂ) ^ (s + 1)) = fun s => cexp (Complex.log (X : ℂ) * (s + 1)) :=
      funext fun s => Complex.cpow_def_of_ne_zero hXC (s + 1)
    rw [hEq]; fun_prop
  have hW_diff : DifferentiableOn ℂ W (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T') :=
    hpow_diff.differentiableOn.mul (differentiableOn_dyadicKernel_re_gt_neg_one.mono fun s hs => by
      change -1 < s.re; linarith [hs.1.1])
  have hshift := Stage5ContourExplicit.vertical_contour_shift_mul_eq_sum_residues
    L W (by linarith : (-1 / 2 : ℝ) < c) hT'_pos J id a hJ_open hL_diff hW_diff
  simp only [id_eq] at hshift
  -- Identify the right vertical integral with `dyadic2 (truncatedPerronPsi1 ψ · c T') X`!
  have hR_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T')..T', L ((c : ℂ) + I * (t : ℂ)) * W ((c : ℂ) + I * (t : ℂ))) =
      dyadic2 (fun y => Stage4ExplicitFormula.truncatedPerronPsi1 ψ y c T') X := by
    have hint_y : ∀ y : ℝ, 0 < y → IntervalIntegrable (fun t : ℝ =>
        Stage3ZeroFreeRegion.negLogDerivL ψ ((c : ℂ) + I * (t : ℂ)) *
          (y : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ)) /
          (((c : ℂ) + I * (t : ℂ)) * ((c : ℂ) + 1 + I * (t : ℂ)))) volume (-T') T' := by
      intro y hy
      have hL_cont : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL ψ ((c : ℂ) + I * (t : ℂ)))
          (Set.uIcc (-T') T') := by
        have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
        have hL_c : ContinuousOn (Stage3ZeroFreeRegion.negLogDerivL ψ) {z : ℂ | 1 < z.re} := fun z hz => by
          have hd : DifferentiableAt ℂ (DirichletCharacter.LFunction ψ) z :=
            (DirichletCharacter.differentiable_LFunction hψ) z
          have hnz : DirichletCharacter.LFunction ψ z ≠ 0 :=
            DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (.inl hψ) hz.le
          have han : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) z :=
            ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
          unfold Stage3ZeroFreeRegion.negLogDerivL
          exact (han.deriv.continuousAt.neg.div hd.continuousAt hnz).continuousWithinAt
        exact hL_c.comp (by fun_prop) fun t _ => by change 1 < ((c : ℂ) + I * (t : ℂ)).re; simp [hc_gt1]
      have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
      have hpow_c : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ))) := by
        have hEq : (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + 1 + I * (t : ℂ))) =
            fun t : ℝ => cexp (Complex.log (y : ℂ) * ((c : ℂ) + 1 + I * (t : ℂ))) :=
          funext fun t => Complex.cpow_def_of_ne_zero hyC _
        rw [hEq]; fun_prop
      refine ((hL_cont.mul hpow_c.continuousOn).div (by fun_prop) fun t _ h0 => ?_).intervalIntegrable
      rcases mul_eq_zero.mp h0 with h1 | h2
      · have := congrArg Complex.re h1; simp at this; linarith
      · have := congrArg Complex.re h2; simp at this; linarith
    unfold dyadic2 Stage4ExplicitFormula.truncatedPerronPsi1
    have halg : ∀ a₁ a₂ a₃ : ℂ,
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * a₁ - 2 * (((2 * Real.pi : ℝ) : ℂ)⁻¹ * a₂) +
          ((2 * Real.pi : ℝ) : ℂ)⁻¹ * a₃ =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (a₁ - 2 * a₂ + a₃) := fun _ _ _ => by ring
    rw [halg, ← intervalIntegral.integral_const_mul (2 : ℂ),
      ← intervalIntegral.integral_sub (hint_y (2 * X) (by linarith)) ((hint_y ((3 / 2 : ℝ) * X) (by linarith)).const_mul 2),
      ← intervalIntegral.integral_add ((hint_y (2 * X) (by linarith)).sub ((hint_y ((3 / 2 : ℝ) * X) (by linarith)).const_mul 2))
        (hint_y X hX0)]
    congr 1
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    set s : ℂ := (c : ℂ) + I * (t : ℂ)
    have hs_eq : L s = Stage3ZeroFreeRegion.negLogDerivL ψ s :=
      hL_eq s ⟨⟨by simp [s]; linarith, by simp [s]⟩, by simpa [s] using ht⟩ fun hmem => by
        have := (hJ_open s hmem).1.2; simp [s] at this
    have hs0 : s ≠ 0 := fun h => by have := congrArg Complex.re h; simp [s] at this; linarith
    have hs1 : s + 1 = (c : ℂ) + 1 + I * (t : ℂ) := by dsimp only [s]; ring
    have hmul_cpow : ∀ α : ℝ, 0 < α → ((α * X : ℝ) : ℂ) ^ (s + 1) = (α : ℂ) ^ (s + 1) * (X : ℂ) ^ (s + 1) := by
      intro α hα
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hα.le hX0.le]
    rw [hs_eq]
    dsimp only [W]
    rw [dyadicKernel_eq_div hs0, hs1]
    have h2X := hmul_cpow 2 (by norm_num)
    have h32X := hmul_cpow (3 / 2) (by norm_num)
    rw [hs1] at h2X h32X
    unfold dyadicW
    rw [hs1, h2X, h32X]
    push_cast; ring
  rw [hR_eq] at hshift
  -- Continuity of `L` on boundary edges
  have hL_cont_edge : ContinuousOn L
      (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' \ (J : Set ℂ)) := by
    have hH_cont := hL_diff.continuousOn.mono (Set.sdiff_subset : _ \ (J : Set ℂ) ⊆ _)
    have hP_cont : ContinuousOn (fun s => ∑ p ∈ J, a p / (s - p))
        (Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' \ (J : Set ℂ)) :=
      continuousOn_finsetSum J fun p hp => continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) fun s hs h0 =>
          hs.2 (Finset.mem_coe.mpr ((sub_eq_zero.mp h0) ▸ hp))
    exact (hH_cont.add hP_cont).congr fun s _ => by
      change L s = (L s - ∑ p ∈ J, a p / (s - p)) + ∑ p ∈ J, a p / (s - p); ring
  have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T')..T', L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) * W (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))‖ ≤
      100 * C_L * (X * Real.log ((q : ℝ) * X)) := by
    have hcont_L : ContinuousOn (fun t : ℝ =>
        L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) * W (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))) (Set.uIcc (-T') T') := by
      rw [Set.uIcc_of_le (by linarith)]
      have h1 : ContinuousOn (fun t : ℝ => L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))) (Set.Icc (-T') T') :=
        hL_cont_edge.comp (by fun_prop) fun t ht => ⟨⟨⟨by simp, by simp; linarith⟩, by simpa using ht⟩,
          fun hmem => by have := (hJ_open _ (Finset.mem_coe.mp hmem)).1.1; simp at this⟩
      have h2 : ContinuousOn (fun t : ℝ => W (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))) (Set.Icc (-T') T') :=
        hW_diff.continuousOn.comp (by fun_prop) fun t ht => ⟨⟨by simp, by simp; linarith⟩, by simpa using ht⟩
      exact h1.mul h2
    have hker1_cont : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) :=
      (continuous_const.add (continuous_id.pow 2)).inv₀ fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne'
    have hker2_cont : Continuous (fun t : ℝ => Real.log (|t| + 2) / (1 + t ^ 2)) :=
      ((continuous_abs.add continuous_const).log fun t => (by linarith [abs_nonneg t] : |t| + 2 ≠ 0)).div
        (by fun_prop) fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne'
    have hker1_int : ∫ t in (-T')..T', (1 + t ^ 2)⁻¹ ≤ Real.pi := by
      have h2 : ∫ t in (-T')..T', (1 + t ^ 2)⁻¹ ≤ ∫ t : ℝ, (1 + t ^ 2)⁻¹ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact MeasureTheory.setIntegral_le_integral integrable_inv_one_add_sq (Eventually.of_forall fun _ => by positivity)
      exact h2.trans_eq integral_univ_inv_one_add_sq
    have hker2_int : ∫ t in (-T')..T', Real.log (|t| + 2) / (1 + t ^ 2) ≤ 20 := by
      have hmid : ∫ t in (-1 : ℝ)..1, Real.log (|t| + 2) / (1 + t ^ 2) ≤ 4 := by
        calc ∫ t in (-1 : ℝ)..1, Real.log (|t| + 2) / (1 + t ^ 2)
            ≤ ∫ _t in (-1 : ℝ)..1, (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by norm_num) (hker2_cont.intervalIntegrable _ _)
                intervalIntegrable_const fun t ht => by
                  have habs : |t| ≤ 1 := abs_le.mpr ht
                  have h1 : Real.log (|t| + 2) ≤ 2 := by
                    linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 2)]
                  exact (div_le_self (Real.log_nonneg (by linarith [abs_nonneg t])) (by nlinarith)).trans h1
          _ = 4 := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
      have hpos_tail : ∫ t in (1 : ℝ)..T', Real.log (|t| + 2) / (1 + t ^ 2) ≤ 8 := by
        have hint_p : IntervalIntegrable (fun t : ℝ => (4 : ℝ) * t ^ (-(3 / 2 : ℝ))) volume (1 : ℝ) T' := by
          refine (ContinuousOn.const_mul (ContinuousOn.rpow_const continuousOn_id fun t ht => ?_) 4).intervalIntegrable
          left; rw [Set.uIcc_of_le (by linarith)] at ht; dsimp only [id_eq]; linarith [ht.1]
        have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T', Real.log (|t| + 2) / (1 + t ^ 2) ≤ 4 * t ^ (-(3 / 2 : ℝ)) := by
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          rw [abs_of_pos ht0]
          have hlog : Real.log (t + 2) ≤ 4 * t ^ (1 / 2 : ℝ) := by
            have h1 : Real.log (t + 2) ≤ Real.log (3 * t) := Real.log_le_log (by linarith) (by linarith [ht.1])
            have h2 : Real.log (3 * t) = Real.log 3 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
            have h3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
            have h4 : Real.log t ≤ 2 * t ^ (1 / 2 : ℝ) := by
              have hl : Real.log t = 2 * Real.log (Real.sqrt t) := by rw [Real.log_sqrt ht0.le]; ring
              rw [hl, ← Real.sqrt_eq_rpow]
              linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht0)]
            have hsq1 : (1 : ℝ) ≤ t ^ (1 / 2 : ℝ) := Real.one_le_rpow ht.1 (by norm_num)
            linarith
          have hpow_eq : 4 * t ^ (1 / 2 : ℝ) / t ^ 2 = 4 * t ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_two t, mul_div_assoc, ← Real.rpow_sub ht0]; congr 2; norm_num
          calc Real.log (t + 2) / (1 + t ^ 2)
              ≤ (4 * t ^ (1 / 2 : ℝ)) / t ^ 2 :=
                div_le_div₀ (by positivity) hlog (by positivity) (by linarith)
            _ = 4 * t ^ (-(3 / 2 : ℝ)) := hpow_eq
        calc ∫ t in (1 : ℝ)..T', Real.log (|t| + 2) / (1 + t ^ 2)
            ≤ ∫ t in (1 : ℝ)..T', (4 : ℝ) * t ^ (-(3 / 2 : ℝ)) :=
              intervalIntegral.integral_mono_on (by linarith) (hker2_cont.intervalIntegrable _ _) hint_p hpt
          _ = 4 * ((T' ^ (-(1 / 2 : ℝ)) - 1) / (-(1 / 2 : ℝ))) := by
              rw [intervalIntegral.integral_const_mul,
                integral_rpow (Or.inr ⟨by norm_num, fun h => by rw [Set.uIcc_of_le (by linarith)] at h; linarith [h.1]⟩),
                Real.one_rpow]
              norm_num
          _ = 8 * (1 - T' ^ (-(1 / 2 : ℝ))) := by ring
          _ ≤ 8 := by linarith [Real.rpow_nonneg hT'_pos.le (-(1 / 2 : ℝ))]
      have hneg_tail : ∫ t in (-T')..(-1 : ℝ), Real.log (|t| + 2) / (1 + t ^ 2) ≤ 8 := by
        have hcomp : ∫ t in (-T')..(-1 : ℝ), Real.log (|t| + 2) / (1 + t ^ 2) =
            ∫ u in (1 : ℝ)..T', Real.log (|u| + 2) / (1 + u ^ 2) := by
          have h1 := intervalIntegral.integral_comp_neg (f := fun u : ℝ => Real.log (|u| + 2) / (1 + u ^ 2))
            (a := -T') (b := -1)
          simp only [neg_neg, abs_neg, neg_sq] at h1; exact h1
        rw [hcomp]; exact hpos_tail
      have hs1 := intervalIntegral.integral_add_adjacent_intervals
        (hker2_cont.intervalIntegrable (μ := volume) (-T') (-1)) (hker2_cont.intervalIntegrable (μ := volume) (-1) 1)
      have hs2 := intervalIntegral.integral_add_adjacent_intervals
        (hker2_cont.intervalIntegrable (μ := volume) (-T') 1) (hker2_cont.intervalIntegrable (μ := volume) 1 T')
      linarith
    have hpt : ∀ t ∈ Set.Icc (-T') T',
        ‖L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) * W (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          (20 * C_L * Real.sqrt X) * (Real.log (q : ℝ) * (1 + t ^ 2)⁻¹ + Real.log (|t| + 2) / (1 + t ^ 2)) := by
      intro t ht
      set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)
      have hs_eq : L s = Stage3ZeroFreeRegion.negLogDerivL ψ s :=
        hL_eq s ⟨⟨by simp [s], by simp [s]; linarith⟩, by simpa [s] using ht⟩ fun hmem => by
          have := (hJ_open s hmem).1.1; simp [s] at this
      rw [hs_eq, norm_mul]
      dsimp only [W]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : (s + 1).re = 1 / 2 := by simp [s]; norm_num
      rw [hre, ← Real.sqrt_eq_rpow]
      have hL1 := hleft_bd q ψ hprim hψ t
      rw [Real.log_mul (by positivity) (by linarith [abs_nonneg t])] at hL1
      have hK1 : ‖dyadicKernel s‖ ≤ 20 / (1 + t ^ 2) := by
        simpa [s] using norm_dyadicKernel_le_inv_sq (s := s) (by simp [s]) (by simp [s]; norm_num)
      have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
      have hlogt_nn : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
      calc ‖Stage3ZeroFreeRegion.negLogDerivL ψ s‖ * (Real.sqrt X * ‖dyadicKernel s‖)
          ≤ (C_L * (Real.log (q : ℝ) + Real.log (|t| + 2))) * (Real.sqrt X * (20 / (1 + t ^ 2))) :=
            mul_le_mul hL1 (mul_le_mul_of_nonneg_left hK1 (Real.sqrt_nonneg X)) (by positivity) (by positivity)
        _ = (20 * C_L * Real.sqrt X) * (Real.log (q : ℝ) * (1 + t ^ 2)⁻¹ + Real.log (|t| + 2) / (1 + t ^ 2)) := by
            rw [div_eq_mul_inv]; ring
    have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hsqrt_le : Real.sqrt X ≤ X := by
      have h1 : Real.sqrt X ≤ Real.sqrt (X ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq hX0.le] at h1
    have hlogq_le : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
    have hlogq_nn : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by linarith)
    calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T')..T', _‖
        ≤ (2 * Real.pi)⁻¹ * ∫ t in (-T')..T', ‖_‖ :=
          mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (by positivity)
      _ ≤ (2 * Real.pi)⁻¹ * ∫ t in (-T')..T',
            (20 * C_L * Real.sqrt X) * (Real.log (q : ℝ) * (1 + t ^ 2)⁻¹ + Real.log (|t| + 2) / (1 + t ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact intervalIntegral.integral_mono_on (by linarith) hcont_L.intervalIntegrable.norm
            ((((hker1_cont.intervalIntegrable _ _).const_mul _).add (hker2_cont.intervalIntegrable _ _)).const_mul _) hpt
      _ = (2 * Real.pi)⁻¹ * ((20 * C_L * Real.sqrt X) *
            (Real.log (q : ℝ) * (∫ t in (-T')..T', (1 + t ^ 2)⁻¹) +
              ∫ t in (-T')..T', Real.log (|t| + 2) / (1 + t ^ 2))) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_add ((hker1_cont.intervalIntegrable _ _).const_mul _)
              (hker2_cont.intervalIntegrable _ _),
            intervalIntegral.integral_const_mul]
      _ ≤ (1 / 6) * ((20 * C_L * X) * (Real.log ((q : ℝ) * X) * 4 + 20)) := by
          have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
          have h2pi6 : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
          have hinv6 : (2 * Real.pi)⁻¹ ≤ 1 / 6 := by
            rw [one_div]; exact inv_anti₀ (by norm_num) h2pi6
          have hint_le : Real.log (q : ℝ) * (∫ t in (-T')..T', (1 + t ^ 2)⁻¹) +
              (∫ t in (-T')..T', Real.log (|t| + 2) / (1 + t ^ 2)) ≤ Real.log ((q : ℝ) * X) * 4 + 20 := by
            have h1 : Real.log (q : ℝ) * (∫ t in (-T')..T', (1 + t ^ 2)⁻¹) ≤ Real.log ((q : ℝ) * X) * 4 :=
              mul_le_mul hlogq_le (hker1_int.trans hpi4)
                (intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity) (by linarith)
            linarith
          have hnn_int1 : 0 ≤ ∫ t in (-T')..T', (1 + t ^ 2)⁻¹ :=
            intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
          have hnn_int2 : 0 ≤ ∫ t in (-T')..T', Real.log (|t| + 2) / (1 + t ^ 2) :=
            intervalIntegral.integral_nonneg (by linarith) fun t _ =>
              div_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) (by positivity)
          exact mul_le_mul hinv6
            (mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le (by positivity)) hint_le
              (by positivity) (by positivity))
            (by positivity) (by norm_num)
      _ ≤ 100 * C_L * (X * Real.log ((q : ℝ) * X)) := by
          have h1 : Real.log ((q : ℝ) * X) * 4 + 20 ≤ 24 * Real.log ((q : ℝ) * X) := by linarith
          have h2 : 0 ≤ C_L * X := by positivity
          nlinarith
  -- Step 4: Horizontal bounds on `Im(s) = ±T'`
  have hHoriz_bd : ∀ sg : Bool,
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in (-1 / 2 : ℝ)..c,
          L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) *
          W ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))))‖ ≤
        125 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by
    intro sg
    have harg_eq : ∀ σ : ℝ, (σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ)) =
        if sg then (σ : ℂ) + I * (T' : ℂ) else (σ : ℂ) - I * (T' : ℂ) := fun σ => by cases sg <;> simp [sub_eq_add_neg]
    have hcont_H : ContinuousOn (fun σ : ℝ =>
        L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) *
        W ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ)))) (Set.uIcc (-1 / 2) c) := by
      rw [Set.uIcc_of_le (by linarith)]
      have h1 : ContinuousOn (fun σ : ℝ => L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))))
          (Set.Icc (-1 / 2) c) :=
        hL_cont_edge.comp (by fun_prop) fun σ hσ => by
          rw [harg_eq σ]; cases sg
          · refine ⟨⟨by simpa using hσ, by simp [hT'_pos.le]⟩, fun hmem => ?_⟩
            have := (hJ_open _ (Finset.mem_coe.mp hmem)).2.1; simp at this
          · refine ⟨⟨by simpa using hσ, by simp [hT'_pos.le]⟩, fun hmem => ?_⟩
            have := (hJ_open _ (Finset.mem_coe.mp hmem)).2.2; simp at this
      have h2 : ContinuousOn (fun σ : ℝ => W ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))))
          (Set.Icc (-1 / 2) c) :=
        hW_diff.continuousOn.comp (by fun_prop) fun σ hσ => by
          rw [harg_eq σ]; cases sg <;> exact ⟨by simpa using hσ, by simp [hT'_pos.le]⟩
      exact h1.mul h2
    have hpt : ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) c,
        ‖L ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ))) *
          W ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' : ℂ)))‖ ≤
          48 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by
      intro σ hσ
      rw [harg_eq σ]
      have hσ1 : -1 / 2 ≤ σ := hσ.1
      have hσ2 : σ ≤ 2 := by linarith [hσ.2]
      have hlog_sq_le : (Real.log ((q : ℝ) * T)) ^ 2 ≤ (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 :=
        pow_le_pow_left₀ hlogqT_pos.le hlogqT_le 2
      have hXσ : X ^ (σ + 1) ≤ 3 * X ^ 2 :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hσ.2] : σ + 1 ≤ c + 1)).trans hXc1_le
      have hT_sq : T ≤ T' ^ 2 := by nlinarith [hT, hT'_geT]
      cases sg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        set s : ℂ := (σ : ℂ) - I * (T' : ℂ)
        have hs_mem : s ∈ Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' :=
          ⟨⟨by simp [s]; exact hσ.1, by simp [s]; exact hσ.2⟩, ⟨by simp [s], by simp [s]; linarith⟩⟩
        have hs_eq : L s = Stage3ZeroFreeRegion.negLogDerivL ψ s :=
          hL_eq s hs_mem fun hmem => by
            have := (hJ_open s hmem).2.1; simp [s] at this
        rw [hs_eq, norm_mul]
        dsimp only [W]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
        have hre : (s + 1).re = σ + 1 := by simp [s]
        rw [hre]
        have hL1 := (hT'_bd σ hσ1 hσ2).2.trans (mul_le_mul_of_nonneg_left hlog_sq_le hCh_pos.le)
        have hK1 : ‖dyadicKernel s‖ ≤ 16 / T := by
          have hk := norm_dyadicKernel_horiz_le (s := s) (by simp [s, hσ1]) (by simp [s, hσ2])
            (by simp [s, abs_of_pos hT'_pos]; linarith)
          have him2 : s.im ^ 2 = T' ^ 2 := by simp [s]
          rw [him2] at hk
          exact hk.trans (div_le_div_of_nonneg_left (by norm_num) hT0 hT_sq)
        calc ‖Stage3ZeroFreeRegion.negLogDerivL ψ s‖ * (X ^ (σ + 1) * ‖dyadicKernel s‖)
            ≤ (C_h * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2) * ((3 * X ^ 2) * (16 / T)) :=
              mul_le_mul hL1 (mul_le_mul hXσ hK1 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
          _ = 48 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by ring
      · simp only [↓reduceIte]
        set s : ℂ := (σ : ℂ) + I * (T' : ℂ)
        have hs_mem : s ∈ Stage5ContourExplicit.closedRect (-1 / 2) c (-T') T' :=
          ⟨⟨by simp [s]; exact hσ.1, by simp [s]; exact hσ.2⟩, ⟨by simp [s]; linarith, by simp [s]⟩⟩
        have hs_eq : L s = Stage3ZeroFreeRegion.negLogDerivL ψ s :=
          hL_eq s hs_mem fun hmem => by
            have := (hJ_open s hmem).2.2; simp [s] at this
        rw [hs_eq, norm_mul]
        dsimp only [W]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
        have hre : (s + 1).re = σ + 1 := by simp [s]
        rw [hre]
        have hL1 := (hT'_bd σ hσ1 hσ2).1.trans (mul_le_mul_of_nonneg_left hlog_sq_le hCh_pos.le)
        have hK1 : ‖dyadicKernel s‖ ≤ 16 / T := by
          have hk := norm_dyadicKernel_horiz_le (s := s) (by simp [s, hσ1]) (by simp [s, hσ2])
            (by simp [s, abs_of_pos hT'_pos]; linarith)
          have him2 : s.im ^ 2 = T' ^ 2 := by simp [s]
          rw [him2] at hk
          exact hk.trans (div_le_div_of_nonneg_left (by norm_num) hT0 hT_sq)
        calc ‖Stage3ZeroFreeRegion.negLogDerivL ψ s‖ * (X ^ (σ + 1) * ‖dyadicKernel s‖)
            ≤ (C_h * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2) * ((3 * X ^ 2) * (16 / T)) :=
              mul_le_mul hL1 (mul_le_mul hXσ hK1 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
          _ = 48 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by ring
    have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hlen : c - (-1 / 2 : ℝ) ≤ 5 / 2 := by linarith
    calc (2 * Real.pi)⁻¹ * ‖∫ σ in (-1 / 2 : ℝ)..c, _‖
        ≤ 1 * ∫ σ in (-1 / 2 : ℝ)..c, ‖_‖ :=
          mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
            (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
      _ ≤ ∫ _σ in (-1 / 2 : ℝ)..c, (48 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T)) := by
          rw [one_mul]
          exact intervalIntegral.integral_mono_on (by linarith) hcont_H.intervalIntegrable.norm
            intervalIntegrable_const hpt
      _ = (c - (-1 / 2 : ℝ)) * (48 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (5 / 2) * (48 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T)) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
      _ ≤ 125 * C_h * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by
          nlinarith [show 0 ≤ X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T by positivity]
  -- Step 5: Bound the zero-sum shift `T' → T` by `64 * C_N * (X^2 * (log (q*X) + log T)^2 / T)`
  have hzero_diff :
      ‖(∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) -
        (∑ ρ ∈ lZerosInBox ψ T, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)‖ ≤
        64 * C_N * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by
    have hsub : lZerosInBox ψ T ⊆ Z := lZerosInBox_mono ψ hT'_geT
    rw [← Finset.sum_sdiff_eq_sub hsub]
    set D : Finset ℂ := Z \ lZerosInBox ψ T
    have hD_term : ∀ ρ ∈ D,
        ‖(lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
          (lZeroMult ψ ρ : ℝ) * (20 * X ^ 2 / T) := by
      intro ρ hρ
      rw [Finset.mem_sdiff] at hρ
      have hm := mem_lZerosInBox.mp hρ.1
      have hgt : T < |ρ.im| := by
        by_contra hle; exact hρ.2 (mem_lZerosInBox.mpr ⟨hm.1, hm.2.1, hm.2.2.1, not_lt.mp hle⟩)
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : (ρ + 1).re = ρ.re + 1 := by simp
      rw [hre]
      have hXρ : X ^ (ρ.re + 1) ≤ X ^ 2 :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hm.2.1] : ρ.re + 1 ≤ 2)).trans_eq
          (Real.rpow_two X)
      have hKρ : ‖dyadicKernel ρ‖ ≤ 20 / T := by
        have hk := norm_dyadicKernel_le_inv_sq (s := ρ) (by linarith [hm.1]) hm.2.1.le
        have hden : T ≤ 1 + ρ.im ^ 2 := by rw [← sq_abs]; nlinarith
        exact hk.trans (div_le_div_of_nonneg_left (by norm_num) hT0 hden)
      calc (lZeroMult ψ ρ : ℝ) * X ^ (ρ.re + 1) * ‖dyadicKernel ρ‖
          ≤ (lZeroMult ψ ρ : ℝ) * X ^ 2 * (20 / T) := by gcongr
        _ = (lZeroMult ψ ρ : ℝ) * (20 * X ^ 2 / T) := by ring
    have hD_count : ∑ ρ ∈ D, (lZeroMult ψ ρ : ℝ) ≤ 2 * C_N * (Real.log ((q : ℝ) * X) + Real.log T) := by
      have hfin_D : {n : ℕ | T ≤ |(completedLZeroSeq hprim hψ n).im| ∧ |(completedLZeroSeq hprim hψ n).im| < T + 2}.Finite :=
        (finite_completedLZeroSeq_abs_im_le hprim hψ (T + 2)).subset fun _ hn => hn.2.le
      set F_D : Finset ℕ := hfin_D.toFinset
      have hF_card := card_completedLZeroSeq_abs_im_Ico_eq hprim hψ (a := T) (b := T + 2)
        (by linarith) F_D fun _ => hfin_D.mem_toFinset
      have hsum_le_card : ∑ ρ ∈ D, (lZeroMult ψ ρ : ℝ) ≤ (F_D.card : ℝ) := by
        have hnat : ∑ ρ ∈ D, lZeroMult ψ ρ ≤ F_D.card := by
          have hmaps : ∀ ρ ∈ D, ∀ n, completedLZeroSeq hprim hψ n = ρ → n ∈ F_D := fun ρ hρ n hn => by
            rw [Finset.mem_sdiff] at hρ
            have hm := mem_lZerosInBox.mp hρ.1
            have hgt : T < |ρ.im| := by
              by_contra hle; exact hρ.2 (mem_lZerosInBox.mpr ⟨hm.1, hm.2.1, hm.2.2.1, not_lt.mp hle⟩)
            exact hfin_D.mem_toFinset.mpr ⟨by rw [hn]; exact hgt.le, by rw [hn]; linarith [hm.2.2.2, hT'_le]⟩
          have hcard_eq : ∀ ρ ∈ D, lZeroMult ψ ρ = (F_D.filter fun n => completedLZeroSeq hprim hψ n = ρ).card := by
            intro ρ hρ
            have hm := mem_lZerosInBox.mp (Finset.mem_sdiff.mp hρ).1
            have hord := lZeroMult_eq_primitive hψ hm.1
            -- Since `ψ` is primitive, `ψ.primitiveCharacter` equals `ψ` — easier: direct order equality
            have hord2 : lZeroMult ψ ρ = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) ρ := by
              have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
              have hev : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 ρ]
                  fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z := by
                filter_upwards [hopen.mem_nhds hm.1] with z hz
                exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ hz
              have hL_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) ρ :=
                ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ) ρ (Set.mem_univ ρ)
              have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
              have hG_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor ψ) ρ := by
                refine DifferentiableOn.analyticAt ?_ (hopen.mem_nhds hm.1)
                intro z hz
                have hz_re : 0 < z.re := hz
                rcases ψ.even_or_odd with he | ho
                · have hfun : DirichletCharacter.gammaFactor ψ =
                      fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) :=
                    funext fun w => by rw [he.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
                  rw [hfun]
                  exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2))) z).mul
                    ((Complex.differentiableAt_Gamma (z / 2) fun k hEq => by
                      have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
                      (differentiableAt_id.div_const 2))).differentiableWithinAt
                · have hfun : DirichletCharacter.gammaFactor ψ =
                      fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2)) * Complex.Gamma ((w + 1) / 2) :=
                    funext fun w => by rw [ho.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
                  rw [hfun]
                  exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2))) z).mul
                    ((Complex.differentiableAt_Gamma ((z + 1) / 2) fun k hEq => by
                      have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
                      ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2))).differentiableWithinAt
              have heq := analyticOrderAt_congr hev
              unfold lZeroMult; simp only [analyticOrderNatAt, heq]
              exact (analyticOrderNatAt_mul_of_ne_zero hL_an hG_an (gammaFactor_ne_zero_of_re_pos ψ hm.1)).symm
            rw [hord2]
            exact (((isMultiplicityZeroSeq_completedLFunction hprim hψ).2 ρ).2 _ fun n => by
              simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hmaps ρ hρ n h, h⟩⟩).symm
          calc ∑ ρ ∈ D, lZeroMult ψ ρ
              = ∑ ρ ∈ D, (F_D.filter fun n => completedLZeroSeq hprim hψ n = ρ).card := Finset.sum_congr rfl hcard_eq
            _ = ∑ ρ ∈ D, ((F_D.filter fun n => completedLZeroSeq hprim hψ n ∈ D).filter fun n =>
                  completedLZeroSeq hprim hψ n = ρ).card := by
                refine Finset.sum_congr rfl fun ρ hρ => congrArg Finset.card ?_
                ext n; simp only [Finset.mem_filter]
                exact ⟨fun h => ⟨⟨h.1, h.2.symm ▸ hρ⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
            _ = (F_D.filter fun n => completedLZeroSeq hprim hψ n ∈ D).card :=
                (Finset.card_eq_sum_card_fiberwise (f := completedLZeroSeq hprim hψ)
                  (s := F_D.filter fun n => completedLZeroSeq hprim hψ n ∈ D) (t := D)
                  fun _ hn => (Finset.mem_filter.mp hn).2).symm
            _ ≤ F_D.card := Finset.card_filter_le _ _
        exact_mod_cast hnat
      have hsh := hshort q ψ hprim hψ T (T + 2) (by linarith) (by linarith) (by linarith)
      have hlog_cmp : Real.log ((q : ℝ) * (T + 2)) ≤ 2 * (Real.log ((q : ℝ) * X) + Real.log T) := by
        have hqT8 : 8 ≤ (q : ℝ) * T := by nlinarith
        have hsq : (q : ℝ) * (T + 2) ≤ ((q : ℝ) * T) ^ 2 := by nlinarith
        calc Real.log ((q : ℝ) * (T + 2)) ≤ Real.log (((q : ℝ) * T) ^ 2) := Real.log_le_log (by positivity) hsq
          _ = 2 * Real.log ((q : ℝ) * T) := by rw [Real.log_pow]; norm_num
          _ ≤ 2 * (Real.log ((q : ℝ) * X) + Real.log T) := by linarith
      nlinarith
    have hlog_sq : Real.log ((q : ℝ) * X) + Real.log T ≤ (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 := by nlinarith
    calc ‖∑ ρ ∈ D, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖
        ≤ ∑ ρ ∈ D, ‖(lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ D, (lZeroMult ψ ρ : ℝ) * (20 * X ^ 2 / T) := Finset.sum_le_sum hD_term
      _ = (∑ ρ ∈ D, (lZeroMult ψ ρ : ℝ)) * (20 * X ^ 2 / T) := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * C_N * (Real.log ((q : ℝ) * X) + Real.log T)) * (20 * X ^ 2 / T) :=
          mul_le_mul_of_nonneg_right hD_count (by positivity)
      _ ≤ (2 * C_N * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2) * (20 * X ^ 2 / T) := by gcongr
      _ = 40 * C_N * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by ring
      _ ≤ 64 * C_N * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by
          nlinarith [show 0 ≤ X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T by positivity]
  -- Step 6: Evaluate residue sum `∑ p ∈ J, a p * W p` and combine!
  have hres_diff : ‖(∑ p ∈ J, a p * W p) -
      (-(∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ))‖ ≤ X := by
    have h0_not_Z : (0 : ℂ) ∉ Z := fun h => by have hm := mem_lZerosInBox.mp h; simp at hm
    have hZ_sum : ∑ ρ ∈ Z, a ρ * W ρ =
        -(∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hρ0 : ρ ≠ 0 := fun h => h0_not_Z (h ▸ hρ)
      dsimp only [a, W]; rw [if_neg hρ0]; ring
    dsimp only [J]
    by_cases he : ψ.Even
    · rw [if_pos he, Finset.sum_insert h0_not_Z, hZ_sum, add_sub_cancel_right]
      dsimp only [a, W]; rw [if_pos rfl, zero_add, Complex.cpow_one, neg_one_mul, norm_neg,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg hX0.le]
      have hK0 := norm_dyadicKernel_le_quarter (s := 0) (by simp) (by simp)
      nlinarith
    · rw [if_neg he, hZ_sum, sub_self, norm_zero]; linarith
  have htop_bd := hHoriz_bd true
  have hbot_bd := hHoriz_bd false
  simp only [↓reduceIte, one_mul, Bool.false_eq_true, neg_mul, ← sub_eq_add_neg] at htop_bd hbot_bd
  set B1 := dyadic2 (Stage4ExplicitFormula.psi1Char ψ) X -
    dyadic2 (fun y => Stage4ExplicitFormula.truncatedPerronPsi1 ψ y c T') X
  set B2 := (∑ p ∈ J, a p * W p) - (-(∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ))
  set B3 := ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    (∫ t in (-T')..T', L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) * W (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)))
  set B4 := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ σ in (-1 / 2 : ℝ)..c, L ((σ : ℂ) + I * (T' : ℂ)) * W ((σ : ℂ) + I * (T' : ℂ)))
  set B5 := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ σ in (-1 / 2 : ℝ)..c, L ((σ : ℂ) - I * (T' : ℂ)) * W ((σ : ℂ) - I * (T' : ℂ)))
  set B6 := (∑ ρ ∈ Z, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) -
    (∑ ρ ∈ lZerosInBox ψ T, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)
  have hsplit : dyadic2 (Stage4ExplicitFormula.psi1Char ψ) X -
      (-(∑ ρ ∈ lZerosInBox ψ T, (lZeroMult ψ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)) =
      B1 + B2 + B3 + B4 - B5 - B6 := by
    dsimp only [B1, B2, B3, B4, B5, B6]
    linear_combination hshift
  rw [hsplit]
  have h1 := norm_sub_le (B1 + B2 + B3 + B4 - B5) B6
  have h2 := norm_sub_le (B1 + B2 + B3 + B4) B5
  have h3 := norm_add_le (B1 + B2 + B3) B4
  have h4 := norm_add_le (B1 + B2) B3
  have h5 := norm_add_le B1 B2
  have hlogX_le : Real.log X ≤ (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 := by
    have h1' : Real.log X ≤ Real.log ((q : ℝ) * X) + Real.log T := by
      linarith [Real.log_le_log hX0 (by nlinarith : X ≤ (q : ℝ) * X)]
    nlinarith
  have hB1_le : ‖B1‖ ≤ 400 * (X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T) := by
    refine hPerron_dy.trans ?_
    gcongr
  have hB2_le : ‖B2‖ ≤ X * Real.log ((q : ℝ) * X) := hres_diff.trans (by nlinarith)
  have hnn1 : 0 ≤ X ^ 2 * (Real.log ((q : ℝ) * X) + Real.log T) ^ 2 / T := by positivity
  have hnn2 : 0 ≤ X * Real.log ((q : ℝ) * X) := by positivity
  dsimp only [C]
  nlinarith

/-- Helper: conjugation of a positive real base raised to a complex power:
`starRingEnd ℂ ((x : ℂ) ^ s) = (x : ℂ) ^ (starRingEnd ℂ s)` for `0 < x`. -/
private lemma conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    starRingEnd ℂ ((x : ℂ) ^ s) = (x : ℂ) ^ (starRingEnd ℂ s) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [Complex.cpow_def_of_ne_zero hxC, Complex.cpow_def_of_ne_zero hxC,
    ← Complex.exp_conj, map_mul, ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

/-- Helper: conjugation symmetry `starRingEnd ℂ (dyadicKernel s) = dyadicKernel (starRingEnd ℂ s)`
for `s ≠ 0`. -/
private lemma conj_dyadicKernel {s : ℂ} (hs : s ≠ 0) :
    starRingEnd ℂ (dyadicKernel s) = dyadicKernel (starRingEnd ℂ s) := by
  have hsc : starRingEnd ℂ s ≠ 0 := fun h => hs ((map_eq_zero (starRingEnd ℂ)).mp h)
  rw [dyadicKernel_eq_div hs, dyadicKernel_eq_div hsc, map_div₀, map_mul, map_add, map_one]
  congr 1
  unfold dyadicW
  rw [map_add, map_sub, map_one, map_mul, map_ofNat,
    show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    conj_ofReal_cpow (by norm_num : (0 : ℝ) < 2),
    conj_ofReal_cpow (by norm_num : (0 : ℝ) < 3 / 2), map_add, map_one]

private lemma card_dirichletChar_eq_totient_local (m : ℕ) [NeZero m] :
    (Fintype.card (DirichletCharacter ℂ m) : ℝ) = (m.totient : ℝ) := by
  have horth := Stage2DirichletAP.char_orthogonality_indicator_nat (q := m) (a := 1) (Nat.coprime_one_left m) 1
  simp only [Nat.ModEq.refl, ↓reduceIte, Nat.cast_one, map_one, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at horth
  have htot_ne : (m.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  have hC : (Fintype.card (DirichletCharacter ℂ m) : ℂ) = (m.totient : ℂ) := by
    have h := congrArg (fun z : ℂ => (m.totient : ℂ) * z) horth
    rw [← mul_assoc, mul_inv_cancel₀ htot_ne, one_mul, mul_one] at h
    exact h
  have hre := congrArg Complex.re hC
  simpa using hre

/-- Helper: for principal `1 mod m` (`m ≥ 2`), `dyadic2 (psi1Char 1) X` differs from
`(dyadic2Real Stage6EffectivePNT.psi1 X : ℂ)` by at most `(X / 2) * Real.log m`. -/
private lemma norm_dyadic2_psi1Char_one_sub_psi1_le {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {X : ℝ} (hX : 1 ≤ X) :
    ‖dyadic2 (Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ m)) X -
      ((dyadic2Real Stage6EffectivePNT.psi1 X : ℝ) : ℂ)‖ ≤ (X / 2) * Real.log (m : ℝ) := by
  have hbound := norm_dyadic2_psi1Char_sub_primitive_le hm (1 : DirichletCharacter ℂ m) hX
  have : NeZero ((1 : DirichletCharacter ℂ m).conductor) := ⟨(1 : DirichletCharacter ℂ m).conductor_ne_zero⟩
  have hcond1 : (1 : DirichletCharacter ℂ m).conductor = 1 := DirichletCharacter.conductor_one
  have hprim_eq : ∀ y : ℝ,
      Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ m).primitiveCharacter y =
        (Stage6EffectivePNT.psi1 y : ℂ) := fun y => by
    rw [Stage6EffectivePNT.psi1_eq_psi1Char_one]
    unfold Stage4ExplicitFormula.psi1Char
    refine Finset.sum_congr rfl fun n _ => ?_
    have hval1 : ((1 : DirichletCharacter ℂ m).primitiveCharacter) (n : ZMod (1 : DirichletCharacter ℂ m).conductor) = 1 := by
      have : Subsingleton (ZMod (1 : DirichletCharacter ℂ m).conductor) := by rw [hcond1]; infer_instance
      have h1 : (n : ZMod (1 : DirichletCharacter ℂ m).conductor) = 1 := Subsingleton.elim _ _
      rw [h1, map_one]
    have hval2 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
      rw [Stage2DirichletAP.principal_char_apply_nat (q := 1) n]; simp
    rw [hval1, hval2]
  have hdy_eq : dyadic2 (Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ m).primitiveCharacter) X =
      ((dyadic2Real Stage6EffectivePNT.psi1 X : ℝ) : ℂ) := by
    unfold dyadic2 dyadic2Real
    rw [hprim_eq (2 * X), hprim_eq ((3 / 2 : ℝ) * X), hprim_eq X]
    push_cast; ring
  dsimp only at hbound
  rwa [hdy_eq] at hbound

open Classical in
/-- **UNCONDITIONAL SMOOTHED DYADIC EXPLICIT FORMULA FOR EVERY `χ mod m` (PRINCIPAL & NON-PRINCIPAL!)**:
there exists a universal constant `C > 0` such that for EVERY `m ≥ 2` (`[NeZero m]`),
EVERY `χ : DirichletCharacter ℂ m`, EVERY `X ≥ 4`, and EVERY `T ≥ 4`:
`‖dyadic2 (psi1Char χ) X - ((if χ = 1 then (1 / 4 : ℂ) * X ^ 2 else 0) -
    ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * X ^ (ρ + 1) * dyadicKernel ρ)‖ ≤
  C * (X ^ 2 * (Real.log (m * X) + Real.log T) ^ 2 / T + X * Real.log (m * X))`. -/
theorem explicit_formula_dyadic2_psi1Char :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (X T : ℝ),
      4 ≤ X → 4 ≤ T →
        ‖dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
            ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
              ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)‖ ≤
          C * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T + X * Real.log ((m : ℝ) * X)) := by
  classical
  obtain ⟨C_prim, hCprim_pos, hprim_ef⟩ := explicit_formula_dyadic2_psi1Char_primitive
  obtain ⟨C_ζ, hCζ_pos, hζ_ef⟩ := Stage9ExplicitFormula.von_mangoldt_explicit_formula_psi1
  obtain ⟨C_tail, hCtail_pos, htail_bd⟩ := sum_tail_inv_im_sq_lZeros_le
  set C : ℝ := C_prim + 12 * C_ζ + 100 * C_tail + 4
  refine ⟨C, by positivity, fun m _ hm χ X T hX hT => ?_⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hX0 : 0 < X := by linarith
  have hT0 : 0 < T := by linarith
  have hlogX_gt1 : 1 < Real.log X := by
    have h4 : Real.exp 1 < X := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlogT_gt1 : 1 < Real.log T := by
    have h4 : Real.exp 1 < T := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlogmX_gt1 : 1 < Real.log ((m : ℝ) * X) :=
    hlogX_gt1.trans_le (Real.log_le_log hX0 (by nlinarith))
  have hnn1 : 0 ≤ X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T := by positivity
  have hnn2 : 0 ≤ X * Real.log ((m : ℝ) * X) := by positivity
  by_cases hχ : χ = 1
  · subst hχ
    rw [if_pos rfl]
    have hcop := norm_dyadic2_psi1Char_one_sub_psi1_le hm (by linarith : 1 ≤ X)
    -- Apply `von_mangoldt_explicit_formula_psi1` at `2 X`, `(3 / 2) X`, `X`
    let term : ℝ → ℕ → ℂ := fun y n =>
      (y : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) /
        (Stage7HadamardXiProduct.xiZeroSeq n * (Stage7HadamardXiProduct.xiZeroSeq n + 1))
    let f : ℕ → ℂ := fun n =>
      (X : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) * dyadicKernel (Stage7HadamardXiProduct.xiZeroSeq n)
    have hsumm2 := Stage9ExplicitFormula.summable_psi1ZeroSeries (x := 2 * X) (by linarith)
    have hsumm32 := Stage9ExplicitFormula.summable_psi1ZeroSeries (x := (3 / 2 : ℝ) * X) (by linarith)
    have hsumm1 := Stage9ExplicitFormula.summable_psi1ZeroSeries (x := X) hX0
    have hf_eq : ∀ n : ℕ, term (2 * X) n - 2 * term ((3 / 2 : ℝ) * X) n + term X n = f n := fun n => by
      dsimp only [term, f]
      have hρ0 := Stage7HadamardXiProduct.xiZeroSeq_ne_zero n
      rw [dyadicKernel_eq_div hρ0]
      have h2X : ((2 * X : ℝ) : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) =
          (2 : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) * (X : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) := by
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hX0.le]; push_cast; rfl
      have h32X : (((3 / 2 : ℝ) * X : ℝ) : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) =
          ((3 / 2 : ℝ) : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) * (X : ℂ) ^ (Stage7HadamardXiProduct.xiZeroSeq n + 1) := by
        rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) hX0.le]
      rw [h2X, h32X]; unfold dyadicW; ring
    have hf_summ : Summable f := by
      have h := (hsumm2.sub (hsumm32.mul_left 2)).add hsumm1
      exact h.congr hf_eq
    have htsum_dy : (∑' n, term (2 * X) n) - 2 * (∑' n, term ((3 / 2 : ℝ) * X) n) + (∑' n, term X n) =
        ∑' n, f n := by
      rw [← tsum_mul_left, ← hsumm2.tsum_sub (hsumm32.mul_left 2),
        ← (hsumm2.sub (hsumm32.mul_left 2)).tsum_add hsumm1]
      exact tsum_congr hf_eq
    have hre_dy : |dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - (∑' n, f n).re)| ≤
        12 * C_ζ * (X * Real.log ((m : ℝ) * X)) := by
      have h1 := hζ_ef (2 * X) (by linarith)
      have h2 := hζ_ef ((3 / 2 : ℝ) * X) (by linarith)
      have h3 := hζ_ef X (by linarith)
      have hrew : dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - (∑' n, f n).re) =
          (Stage6EffectivePNT.psi1 (2 * X) - ((2 * X) ^ 2 / 2 - (∑' n, term (2 * X) n).re)) -
          2 * (Stage6EffectivePNT.psi1 ((3 / 2 : ℝ) * X) - (((3 / 2 : ℝ) * X) ^ 2 / 2 - (∑' n, term ((3 / 2 : ℝ) * X) n).re)) +
          (Stage6EffectivePNT.psi1 X - (X ^ 2 / 2 - (∑' n, term X n).re)) := by
        have hre_eq := congrArg Complex.re htsum_dy
        simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
          zero_mul, sub_zero] at hre_eq
        unfold dyadic2Real; linarith
      rw [hrew]
      have ha1 := abs_add_le
        ((Stage6EffectivePNT.psi1 (2 * X) - ((2 * X) ^ 2 / 2 - (∑' n, term (2 * X) n).re)) -
          2 * (Stage6EffectivePNT.psi1 ((3 / 2 : ℝ) * X) - (((3 / 2 : ℝ) * X) ^ 2 / 2 - (∑' n, term ((3 / 2 : ℝ) * X) n).re)))
        (Stage6EffectivePNT.psi1 X - (X ^ 2 / 2 - (∑' n, term X n).re))
      have ha2 := abs_sub_le
        (Stage6EffectivePNT.psi1 (2 * X) - ((2 * X) ^ 2 / 2 - (∑' n, term (2 * X) n).re)) 0
        (2 * (Stage6EffectivePNT.psi1 ((3 / 2 : ℝ) * X) - (((3 / 2 : ℝ) * X) ^ 2 / 2 - (∑' n, term ((3 / 2 : ℝ) * X) n).re)))
      rw [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha2
      have hlog2X : Real.log (2 * X) ≤ Real.log ((m : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
      have hlog32X : Real.log ((3 / 2 : ℝ) * X) ≤ Real.log ((m : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
      have hlogX : Real.log X ≤ Real.log ((m : ℝ) * X) := Real.log_le_log hX0 (by nlinarith)
      have h1' : |Stage6EffectivePNT.psi1 (2 * X) - ((2 * X) ^ 2 / 2 - (∑' n, term (2 * X) n).re)| ≤
          2 * C_ζ * (X * Real.log ((m : ℝ) * X)) := by
        dsimp only [term]
        calc _ ≤ C_ζ * (2 * X) * Real.log (2 * X) := h1
          _ ≤ C_ζ * (2 * X) * Real.log ((m : ℝ) * X) := mul_le_mul_of_nonneg_left hlog2X (by positivity)
          _ = 2 * C_ζ * (X * Real.log ((m : ℝ) * X)) := by ring
      have h2' : |Stage6EffectivePNT.psi1 ((3 / 2 : ℝ) * X) - (((3 / 2 : ℝ) * X) ^ 2 / 2 - (∑' n, term ((3 / 2 : ℝ) * X) n).re)| ≤
          (3 / 2 : ℝ) * C_ζ * (X * Real.log ((m : ℝ) * X)) := by
        dsimp only [term]
        calc _ ≤ C_ζ * ((3 / 2 : ℝ) * X) * Real.log ((3 / 2 : ℝ) * X) := h2
          _ ≤ C_ζ * ((3 / 2 : ℝ) * X) * Real.log ((m : ℝ) * X) := mul_le_mul_of_nonneg_left hlog32X (by positivity)
          _ = (3 / 2 : ℝ) * C_ζ * (X * Real.log ((m : ℝ) * X)) := by ring
      have h3' : |Stage6EffectivePNT.psi1 X - (X ^ 2 / 2 - (∑' n, term X n).re)| ≤
          C_ζ * (X * Real.log ((m : ℝ) * X)) := by
        dsimp only [term]
        calc _ ≤ C_ζ * X * Real.log X := h3
          _ ≤ C_ζ * X * Real.log ((m : ℝ) * X) := mul_le_mul_of_nonneg_left hlogX (by positivity)
          _ = C_ζ * (X * Real.log ((m : ℝ) * X)) := by ring
      have hnnC : 0 ≤ C_ζ * (X * Real.log ((m : ℝ) * X)) := mul_nonneg hCζ_pos.le hnn2
      linarith
    -- Identify the finite sum `S_T := ∑ ρ ∈ lZerosInBox 1 T, ...` with `∑ n ∈ F_T, f n` and verify `S_T` is real!
    set S_T : ℂ := ∑ ρ ∈ lZerosInBox (1 : DirichletCharacter ℂ m) T,
      (lZeroMult (1 : DirichletCharacter ℂ m) ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ
    have hST_eq_zeta : S_T = ∑ ρ ∈ Stage9ExplicitFormula.zetaZerosInBox T,
        (analyticOrderNatAt xi ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ := by
      dsimp only [S_T]
      rw [lZerosInBox_one_eq_zetaZerosInBox]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
      rw [lZeroMult_one_eq_xi m hm'.1 hm'.2.1]
    have hST_real : S_T = ((S_T.re : ℝ) : ℂ) := by
      have hconj : starRingEnd ℂ S_T = S_T := by
        rw [hST_eq_zeta, map_sum]
        refine Finset.sum_bij (fun ρ _ => starRingEnd ℂ ρ) ?_ ?_ ?_ ?_
        · intro ρ hρ
          have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
          have hζc := (RHDirect.riemannZeta_fourfold_zero_symmetry hm'.1 hm'.2.1 hm'.2.2.1).1
          exact (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr
            ⟨by simpa using hm'.1, by simpa using hm'.2.1, hζc, by simpa using hm'.2.2.2⟩
        · intro a _ b _ h; exact (starRingEnd ℂ).injective h
        · intro w hw
          have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hw
          have hζc := (RHDirect.riemannZeta_fourfold_zero_symmetry hm'.1 hm'.2.1 hm'.2.2.1).1
          exact ⟨starRingEnd ℂ w,
            (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr
              ⟨by simpa using hm'.1, by simpa using hm'.2.1, hζc, by simpa using hm'.2.2.2⟩,
            by simp⟩
        · intro ρ hρ
          have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
          have hre0 : 0 < ρ.re := hm'.1
          have hρ0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at hre0; exact lt_irrefl 0 hre0
          rw [map_mul, map_mul, map_natCast, conj_ofReal_cpow hX0, map_add, map_one,
            conj_dyadicKernel hρ0, Stage7VonMangoldtExplicit.analyticOrderNatAt_xi_conj]
      have him : S_T.im = 0 := by
        have h := congrArg Complex.im hconj; simp at h; linarith
      exact Complex.ext (by simp) (by simp [him])
    set F_T : Finset ℕ := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T).toFinset
    have hFT_sum : ∑ n ∈ F_T, f n = S_T := by
      rw [hST_eq_zeta]
      have hmaps : ∀ n ∈ F_T, Stage7HadamardXiProduct.xiZeroSeq n ∈ Stage9ExplicitFormula.zetaZerosInBox T := fun n hn => by
        have hst := Stage7HadamardXiProduct.xiZeroSeq_strip n
        have hζ0 := Stage7HadamardXiProduct.xiZeroSeq_riemannZeta_zero n
        have him := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T).mem_toFinset.mp hn
        exact (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr ⟨hst.1, hst.2, hζ0, him⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hsum_c : ∑ n ∈ F_T.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ), f n =
          ((F_T.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ)).card : ℂ) *
            ((X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := by
        calc ∑ n ∈ F_T.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ), f n
            = ∑ _n ∈ F_T.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ),
                ((X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) :=
              Finset.sum_congr rfl fun n hn => by dsimp only [f]; rw [(Finset.mem_filter.mp hn).2]
          _ = ((F_T.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ)).card : ℂ) *
                ((X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum_c]
      have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρ
      have him_T : |ρ.im| ≤ T := hm'.2.2.2
      have hcard : (F_T.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ)).card = analyticOrderNatAt xi ρ :=
        ((Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi.2 ρ).2 _ fun n => by
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨(Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T).mem_toFinset.mpr
            (by change |(Stage7HadamardXiProduct.xiZeroSeq n).im| ≤ T; rw [h]; exact him_T), h⟩⟩)
      rw [hcard]; ring
    -- Bound tail `‖(∑' n, f n) - S_T‖ ≤ 100 * C_tail * X^2 * (log (m * X) + log T)^2 / T`
    have htail_norm : ‖(∑' n, f n) - S_T‖ ≤
        100 * C_tail * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T) := by
      have hsplit : (∑' n, f n) - S_T = ∑' n : ↑((F_T : Set ℕ)ᶜ), f n.1 := by
        have hcomp := hf_summ.sum_add_tsum_compl (s := F_T)
        rw [hFT_sum] at hcomp
        linear_combination -hcomp
      rw [hsplit]
      have hf_sub : Summable (fun n : ↑((F_T : Set ℕ)ᶜ) => ‖f n.1‖) :=
        hf_summ.norm.subtype _
      have hnorm_le : ‖∑' n : ↑((F_T : Set ℕ)ᶜ), f n.1‖ ≤ ∑' n : ↑((F_T : Set ℕ)ᶜ), ‖f n.1‖ :=
        norm_tsum_le_tsum_norm hf_sub
      have hbound_fin : ∀ s : Finset ↑((F_T : Set ℕ)ᶜ),
          ∑ n ∈ s, ‖f n.1‖ ≤ 20 * C_tail * X ^ 2 * Real.log ((m : ℝ) * (T + 2)) / T := by
        intro s
        by_cases hs : s = ∅
        · subst hs; simp
          exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))) hT0.le
        · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
          set R : ℝ := max T (s.sup' hsne fun n => |(Stage7HadamardXiProduct.xiZeroSeq n.1).im|)
          have hRT : T ≤ R := le_max_left _ _
          have hR1 : 1 ≤ R := by linarith
          set F_R : Finset ℕ := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le R).toFinset
          set G : Finset ℕ := F_R.filter fun n => T < |(Stage7HadamardXiProduct.xiZeroSeq n).im|
          have hs_sub : s.image Subtype.val ⊆ G := by
            intro n hn
            rcases Finset.mem_image.mp hn with ⟨⟨k, hk⟩, hks, rfl⟩
            have hk_not : k ∉ F_T := by simpa using hk
            have hgt : T < |(Stage7HadamardXiProduct.xiZeroSeq k).im| := by
              by_contra hle; exact hk_not ((Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T).mem_toFinset.mpr (not_lt.mp hle))
            have hleR : |(Stage7HadamardXiProduct.xiZeroSeq k).im| ≤ R :=
              (Finset.le_sup' (fun x : ↑((F_T : Set ℕ)ᶜ) => |(Stage7HadamardXiProduct.xiZeroSeq x.1).im|) hks).trans (le_max_right _ _)
            exact Finset.mem_filter.mpr ⟨(Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le R).mem_toFinset.mpr hleR, hgt⟩
          have hG_maps : ∀ n ∈ G, Stage7HadamardXiProduct.xiZeroSeq n ∈
              (lZerosInBox (1 : DirichletCharacter ℂ m) R).filter (fun ρ => T < |ρ.im|) := fun n hn => by
            rcases Finset.mem_filter.mp hn with ⟨hRmem, hgt⟩
            have hst := Stage7HadamardXiProduct.xiZeroSeq_strip n
            have hζ0 := Stage7HadamardXiProduct.xiZeroSeq_riemannZeta_zero n
            have him := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le R).mem_toFinset.mp hRmem
            refine Finset.mem_filter.mpr ⟨?_, hgt⟩
            rw [lZerosInBox_one_eq_zetaZerosInBox]
            exact (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height R).mem_toFinset.mpr ⟨hst.1, hst.2, hζ0, him⟩
          have hpt_f : ∀ n : ℕ, ‖f n‖ ≤ 20 * X ^ 2 / (1 + (Stage7HadamardXiProduct.xiZeroSeq n).im ^ 2) := fun n => by
            have hst := Stage7HadamardXiProduct.xiZeroSeq_strip n
            dsimp only [f]
            rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
            have hre : (Stage7HadamardXiProduct.xiZeroSeq n + 1).re = (Stage7HadamardXiProduct.xiZeroSeq n).re + 1 := by simp
            rw [hre]
            have hX2 : X ^ ((Stage7HadamardXiProduct.xiZeroSeq n).re + 1) ≤ X ^ 2 :=
              (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hst.2])).trans_eq (Real.rpow_two X)
            have hK := norm_dyadicKernel_le_inv_sq (s := Stage7HadamardXiProduct.xiZeroSeq n)
              (by linarith [hst.1]) hst.2.le
            calc X ^ ((Stage7HadamardXiProduct.xiZeroSeq n).re + 1) * ‖dyadicKernel (Stage7HadamardXiProduct.xiZeroSeq n)‖
                ≤ X ^ 2 * (20 / (1 + (Stage7HadamardXiProduct.xiZeroSeq n).im ^ 2)) :=
                  mul_le_mul hX2 hK (norm_nonneg _) (by positivity)
              _ = 20 * X ^ 2 / (1 + (Stage7HadamardXiProduct.xiZeroSeq n).im ^ 2) := by ring
          calc ∑ n ∈ s, ‖f n.1‖
              = ∑ n ∈ s.image Subtype.val, ‖f n‖ :=
                (Finset.sum_image (f := fun n => ‖f n‖) fun _ _ _ _ h => Subtype.ext h).symm
            _ ≤ ∑ n ∈ G, ‖f n‖ := Finset.sum_le_sum_of_subset_of_nonneg hs_sub fun _ _ _ => norm_nonneg _
            _ ≤ ∑ n ∈ G, (20 * X ^ 2 / (1 + (Stage7HadamardXiProduct.xiZeroSeq n).im ^ 2)) :=
                Finset.sum_le_sum fun n _ => hpt_f n
            _ = ∑ ρ ∈ (lZerosInBox (1 : DirichletCharacter ℂ m) R).filter (fun ρ => T < |ρ.im|),
                  ∑ n ∈ G.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ),
                    (20 * X ^ 2 / (1 + (Stage7HadamardXiProduct.xiZeroSeq n).im ^ 2)) :=
                (Finset.sum_fiberwise_of_maps_to hG_maps _).symm
            _ = ∑ ρ ∈ (lZerosInBox (1 : DirichletCharacter ℂ m) R).filter (fun ρ => T < |ρ.im|),
                  (20 * X ^ 2) * ((lZeroMult (1 : DirichletCharacter ℂ m) ρ : ℝ) / (1 + ρ.im ^ 2)) := by
                refine Finset.sum_congr rfl fun ρ hρ => ?_
                have hρ_box := (Finset.mem_filter.mp hρ).1
                have hρ_gt := (Finset.mem_filter.mp hρ).2
                rw [lZerosInBox_one_eq_zetaZerosInBox] at hρ_box
                have hm' := (Stage6XiZeroDensity.finite_riemannZeta_zeros_le_height R).mem_toFinset.mp hρ_box
                have him_R : |ρ.im| ≤ R := hm'.2.2.2
                rw [Finset.sum_congr rfl (fun n hn => by rw [(Finset.mem_filter.mp hn).2]),
                  Finset.sum_const, nsmul_eq_mul]
                have hcard : (G.filter (fun n => Stage7HadamardXiProduct.xiZeroSeq n = ρ)).card =
                    lZeroMult (1 : DirichletCharacter ℂ m) ρ := by
                  rw [lZeroMult_one_eq_xi m hm'.1 hm'.2.1]
                  exact ((Stage7HadamardXiProduct.isMultiplicityZeroSeq_xi.2 ρ).2 _ fun n => by
                    simp only [Finset.mem_filter, G]
                    exact ⟨fun h => h.2, fun h => ⟨⟨(Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le R).mem_toFinset.mpr
                      (by change |(Stage7HadamardXiProduct.xiZeroSeq n).im| ≤ R; rw [h]; exact him_R),
                      by rw [h]; exact hρ_gt⟩, h⟩⟩)
                rw [hcard]; ring
            _ = (20 * X ^ 2) * ∑ ρ ∈ (lZerosInBox (1 : DirichletCharacter ℂ m) R).filter (fun ρ => T < |ρ.im|),
                  (lZeroMult (1 : DirichletCharacter ℂ m) ρ : ℝ) / (1 + ρ.im ^ 2) := (Finset.mul_sum _ _ _).symm
            _ ≤ (20 * X ^ 2) * (C_tail * Real.log ((m : ℝ) * (T + 2)) / T) :=
                mul_le_mul_of_nonneg_left (htail_bd m hm 1 T R (by linarith) hRT) (by positivity)
            _ = 20 * C_tail * X ^ 2 * Real.log ((m : ℝ) * (T + 2)) / T := by ring
      have htsum_le : ∑' n : ↑((F_T : Set ℕ)ᶜ), ‖f n.1‖ ≤
          20 * C_tail * X ^ 2 * Real.log ((m : ℝ) * (T + 2)) / T :=
        Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hbound_fin
      have hlog_cmp : Real.log ((m : ℝ) * (T + 2)) ≤ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 := by
        have h1 : Real.log ((m : ℝ) * (T + 2)) ≤ 2 * (Real.log ((m : ℝ) * X) + Real.log T) := by
          have hmT8 : 8 ≤ (m : ℝ) * T := by nlinarith
          have hsq : (m : ℝ) * (T + 2) ≤ ((m : ℝ) * T) ^ 2 := by nlinarith
          have h2 : Real.log ((m : ℝ) * T) ≤ Real.log ((m : ℝ) * X) + Real.log T := by
            rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul (by positivity) hX0.ne']; linarith
          calc Real.log ((m : ℝ) * (T + 2)) ≤ Real.log (((m : ℝ) * T) ^ 2) := Real.log_le_log (by positivity) hsq
            _ = 2 * Real.log ((m : ℝ) * T) := by rw [Real.log_pow]; norm_num
            _ ≤ 2 * (Real.log ((m : ℝ) * X) + Real.log T) := by linarith
        nlinarith
      calc ‖∑' n : ↑((F_T : Set ℕ)ᶜ), f n.1‖
          ≤ 20 * C_tail * X ^ 2 * Real.log ((m : ℝ) * (T + 2)) / T := hnorm_le.trans htsum_le
        _ ≤ 20 * C_tail * X ^ 2 * (2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2) / T := by gcongr
        _ = 40 * C_tail * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T) := by ring
        _ ≤ 100 * C_tail * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T) := by nlinarith
    have hmain_real : ‖((dyadic2Real Stage6EffectivePNT.psi1 X : ℝ) : ℂ) -
        ((1 / 4 : ℂ) * (X : ℂ) ^ 2 - S_T)‖ ≤
        12 * C_ζ * (X * Real.log ((m : ℝ) * X)) +
          100 * C_tail * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T) := by
      have hrew : ((dyadic2Real Stage6EffectivePNT.psi1 X : ℝ) : ℂ) - ((1 / 4 : ℂ) * (X : ℂ) ^ 2 - S_T) =
          (((dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - S_T.re) : ℝ) : ℂ)) := by
        conv_lhs => rw [hST_real]
        push_cast; ring
      rw [hrew, Complex.norm_real, Real.norm_eq_abs]
      have htri : |dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - S_T.re)| ≤
          |dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - (∑' n, f n).re)| +
          |((∑' n, f n) - S_T).re| := by
        have h := abs_add_le (dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - (∑' n, f n).re))
          (S_T.re - (∑' n, f n).re)
        have heq : (dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - (∑' n, f n).re)) +
            (S_T.re - (∑' n, f n).re) =
            dyadic2Real Stage6EffectivePNT.psi1 X - ((1 / 4 : ℝ) * X ^ 2 - S_T.re) := by ring
        rw [heq] at h
        have habs : |S_T.re - (∑' n, f n).re| = |((∑' n, f n) - S_T).re| := by
          rw [Complex.sub_re, abs_sub_comm]
        linarith
      have hre_le : |((∑' n, f n) - S_T).re| ≤ ‖(∑' n, f n) - S_T‖ := Complex.abs_re_le_norm _
      linarith
    have htri_tot := norm_add_le
      (dyadic2 (Stage4ExplicitFormula.psi1Char (1 : DirichletCharacter ℂ m)) X -
        ((dyadic2Real Stage6EffectivePNT.psi1 X : ℝ) : ℂ))
      (((dyadic2Real Stage6EffectivePNT.psi1 X : ℝ) : ℂ) - ((1 / 4 : ℂ) * (X : ℂ) ^ 2 - S_T))
    rw [sub_add_sub_cancel] at htri_tot
    have hlogm_le : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
    dsimp only [C]
    nlinarith
  · rw [if_neg hχ, zero_sub]
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hψ_ne1 : χ.primitiveCharacter ≠ 1 := fun h1 => hχ (by rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
    have hcop := norm_dyadic2_psi1Char_sub_primitive_le hm χ (by linarith : 1 ≤ X)
    dsimp only at hcop
    have hef := hprim_ef χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hψ_ne1 X T hX hT
    have hsum_eq :
        ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ =
        ∑ ρ ∈ lZerosInBox χ.primitiveCharacter T,
          (lZeroMult χ.primitiveCharacter ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ := by
      rw [lZerosInBox_eq_primitive hχ]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have h0 := (mem_lZerosInBox.mp hρ).1
      have h1 := lZeroMult_eq_primitive hχ h0
      have hord_ψ : lZeroMult χ.primitiveCharacter ρ =
          analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ := by
        have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
        have hev : DirichletCharacter.completedLFunction χ.primitiveCharacter =ᶠ[𝓝 ρ]
            fun z => DirichletCharacter.LFunction χ.primitiveCharacter z *
              DirichletCharacter.gammaFactor χ.primitiveCharacter z := by
          filter_upwards [hopen.mem_nhds h0] with z hz
          exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ.primitiveCharacter hz
        have hL_an : AnalyticAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) ρ :=
          ((DirichletCharacter.differentiable_LFunction hψ_ne1).differentiableOn.analyticOnNhd isOpen_univ) ρ (Set.mem_univ ρ)
        have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        have hG_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ.primitiveCharacter) ρ := by
          refine DifferentiableOn.analyticAt ?_ (hopen.mem_nhds h0)
          intro z hz
          have hz_re : 0 < z.re := hz
          rcases χ.primitiveCharacter.even_or_odd with he | ho
          · have hfun : DirichletCharacter.gammaFactor χ.primitiveCharacter =
                fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) :=
              funext fun w => by rw [he.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
            rw [hfun]
            exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2))) z).mul
              ((Complex.differentiableAt_Gamma (z / 2) fun k hEq => by
                have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
                (differentiableAt_id.div_const 2))).differentiableWithinAt
          · have hfun : DirichletCharacter.gammaFactor χ.primitiveCharacter =
                fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2)) * Complex.Gamma ((w + 1) / 2) :=
              funext fun w => by rw [ho.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
            rw [hfun]
            exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2))) z).mul
              ((Complex.differentiableAt_Gamma ((z + 1) / 2) fun k hEq => by
                have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
                ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2))).differentiableWithinAt
        have heq := analyticOrderAt_congr hev
        unfold lZeroMult; simp only [analyticOrderNatAt, heq]
        exact (analyticOrderNatAt_mul_of_ne_zero hL_an hG_an (gammaFactor_ne_zero_of_re_pos χ.primitiveCharacter h0)).symm
      dsimp only at h1
      rw [h1, hord_ψ]
    rw [hsum_eq]
    have htri := norm_add_le
      (dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
        dyadic2 (Stage4ExplicitFormula.psi1Char χ.primitiveCharacter) X)
      (dyadic2 (Stage4ExplicitFormula.psi1Char χ.primitiveCharacter) X -
        (-(∑ ρ ∈ lZerosInBox χ.primitiveCharacter T,
          (lZeroMult χ.primitiveCharacter ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)))
    rw [sub_add_sub_cancel] at htri
    have hd_le : (χ.conductor : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos m) χ.conductor_dvd_level
    have hlog_le : Real.log ((χ.conductor : ℝ) * X) ≤ Real.log ((m : ℝ) * X) :=
      Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos χ.conductor)) hX0) (by nlinarith)
    have hd1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast (NeZero.pos χ.conductor)
    have hlog_sq_le : (Real.log ((χ.conductor : ℝ) * X) + Real.log T) ^ 2 ≤
        (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg (by nlinarith : 1 ≤ (χ.conductor : ℝ) * X)]) (by linarith) 2
    have hlogm_le : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
    have hef2 : C_prim * (X ^ 2 * (Real.log ((χ.conductor : ℝ) * X) + Real.log T) ^ 2 / T +
          X * Real.log ((χ.conductor : ℝ) * X)) ≤
        C_prim * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T +
          X * Real.log ((m : ℝ) * X)) := by gcongr
    dsimp only [C]
    nlinarith

/-- **UNCONDITIONAL GALLAGHER / CESÀRO-1 SMOOTHED DYADIC EXPLICIT FORMULA FOR `ψ₁(x; m, a)`
(`0` ASSUMPTIONS!)**:
there exists a universal constant `C > 0` such that for EVERY modulus `m ≥ 2` (`[NeZero m]`),
EVERY residue `a` coprime to `m`, EVERY `X ≥ 4`, and EVERY `T ≥ 4`:
`‖(dyadic2Real (psi1AP m a) X : ℂ) -
    (m.totient : ℂ)⁻¹ * ((1 / 4 : ℂ) * X ^ 2 -
      ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ a) *
        ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * X ^ (ρ + 1) * dyadicKernel ρ)‖ ≤
  C * (X ^ 2 * (Real.log (m * X) + Real.log T) ^ 2 / T + X * Real.log (m * X))`. -/
theorem smoothed_ap_dyadic_explicit_formula :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a : ℕ) [NeZero m], 2 ≤ m → Nat.Coprime a m →
      ∀ X T : ℝ, 4 ≤ X → 4 ≤ T →
        ‖((dyadic2Real (psi1AP m a) X : ℝ) : ℂ) -
            (m.totient : ℂ)⁻¹ *
              ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
                ∑ χ : DirichletCharacter ℂ m,
                  starRingEnd ℂ (χ (a : ZMod m)) *
                    ∑ ρ ∈ lZerosInBox χ T,
                      (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)‖ ≤
          C * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T + X * Real.log ((m : ℝ) * X)) := by
  classical
  obtain ⟨C, hC_pos, hef⟩ := explicit_formula_dyadic2_psi1Char
  refine ⟨C, hC_pos, fun m a _ hm hcop X T hX hT => ?_⟩
  rw [dyadic2Real_psi1AP_eq_char_sum hcop X]
  have h1_apply : (1 : DirichletCharacter ℂ m) (a : ZMod m) = 1 := by
    rw [Stage2DirichletAP.principal_char_apply_nat a, if_pos hcop]
  have hmain_sum : ∑ χ : DirichletCharacter ℂ m,
      starRingEnd ℂ (χ (a : ZMod m)) * (if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) =
      (1 / 4 : ℂ) * (X : ℂ) ^ 2 := by
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ m)]
    · rw [if_pos rfl, h1_apply, map_one, one_mul]
    · intro χ _ hne; rw [if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hdiff_eq :
      (m.totient : ℂ)⁻¹ *
          (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
            dyadic2 (Stage4ExplicitFormula.psi1Char χ) X) -
      (m.totient : ℂ)⁻¹ *
          ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
            ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
              ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) =
      (m.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ m,
            starRingEnd ℂ (χ (a : ZMod m)) *
              (dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
                ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
                  ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)) := by
    rw [← mul_sub]; congr 1
    conv_lhs => rw [← hmain_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun χ _ => by ring
  rw [hdiff_eq, norm_mul, norm_inv, Complex.norm_natCast]
  have htot_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have hcard_char : (Fintype.card (DirichletCharacter ℂ m) : ℝ) = (m.totient : ℝ) :=
    card_dirichletChar_eq_totient_local m
  set E : ℝ := C * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T + X * Real.log ((m : ℝ) * X))
  have hsum_bd : ‖∑ χ : DirichletCharacter ℂ m,
      starRingEnd ℂ (χ (a : ZMod m)) *
        (dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
          ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
            ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ))‖ ≤
      (m.totient : ℝ) * E := by
    calc ‖∑ χ : DirichletCharacter ℂ m, _‖
        ≤ ∑ χ : DirichletCharacter ℂ m,
            ‖starRingEnd ℂ (χ (a : ZMod m))‖ *
              ‖dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
                ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
                  ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_); rw [norm_mul]
      _ ≤ ∑ _χ : DirichletCharacter ℂ m, E := by
          refine Finset.sum_le_sum fun χ _ => ?_
          have hχ1 : ‖starRingEnd ℂ (χ (a : ZMod m))‖ ≤ 1 := by
            rw [Complex.norm_conj]; exact χ.norm_le_one _
          calc _ ≤ 1 * E := mul_le_mul hχ1 (hef m hm χ X T hX hT) (norm_nonneg _) zero_le_one
            _ = E := one_mul E
      _ = (Fintype.card (DirichletCharacter ℂ m) : ℝ) * E := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (m.totient : ℝ) * E := by rw [hcard_char]
  calc (m.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ m, _‖
      ≤ (m.totient : ℝ)⁻¹ * ((m.totient : ℝ) * E) := mul_le_mul_of_nonneg_left hsum_bd (by positivity)
    _ = E := inv_mul_cancel_left₀ htot_pos.ne' E

/-! ## Section 3: Unconditional Siegel-Zero Simplicity & Clean Phase B Predicates -/

/-- **UNCONDITIONAL SIMPLICITY OF SIEGEL ZEROS (`0` ASSUMPTIONS!)**:
there exists an absolute constant `c > 0` such that for EVERY primitive real non-principal
character `ψ : DirichletCharacter ℂ q` (`q [NeZero q]`), any real zero `β` of `LFunction ψ`
satisfying `1 - c / Real.log (2 * q) ≤ β` is a SIMPLE zero (`lZeroMult ψ (β : ℂ) = 1`). -/
theorem siegel_zero_simple_unconditional :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q),
        ψ.IsPrimitive → ψ ≠ 1 → ψ ^ 2 = 1 →
        ∀ β : ℝ, 1 - c / Real.log (2 * (q : ℝ)) ≤ β →
          DirichletCharacter.LFunction ψ (β : ℂ) = 0 →
          lZeroMult ψ (β : ℂ) = 1 := by
  classical
  obtain ⟨C_dig, hCdig_pos, hdig_bd⟩ := norm_digamma_quarter_strip_le
  set c : ℝ := 1 / (40 * (2 + C_dig))
  refine ⟨c, by positivity, fun q _ ψ hprim hψ hψ2 β hβ_ge hz => ?_⟩
  have hq2 : 2 ≤ q := two_le_of_dirichletChar_ne_one hψ
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hlog2q_gt1 : 1 < Real.log (2 * (q : ℝ)) := by
    have h4 : Real.exp 1 < 2 * (q : ℝ) := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
  have hlog2q_pos : 0 < Real.log (2 * (q : ℝ)) := zero_lt_one.trans hlog2q_gt1
  have hβ_lt1 : β < 1 := by
    by_contra hge; push Not at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (.inl hψ) (by simpa using hge) hz
  set δ : ℝ := 1 - β
  have hδ_pos : 0 < δ := by linarith
  have hδ_le : δ ≤ c / Real.log (2 * (q : ℝ)) := by linarith
  have hδ_lt_qtr : δ < 1 / 4 := by
    have h1 : c / Real.log (2 * (q : ℝ)) ≤ c := div_le_self (by positivity) hlog2q_gt1.le
    have h2 : c < 1 / 4 := by
      dsimp only [c]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hβ_pos : 0 < β := by linarith
  -- First check `1 ≤ lZeroMult ψ (β : ℂ)` since `LFunction ψ` is entire, vanishes at `β`, and is not identically zero.
  have hmult_pos : 1 ≤ lZeroMult ψ (β : ℂ) := by
    have hL_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) (β : ℂ) :=
      ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
    have hntop : analyticOrderAt (DirichletCharacter.LFunction ψ) (β : ℂ) ≠ ⊤ := fun htop => by
      have h0 := ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ (β : ℂ)) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ (2 : ℂ))
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (.inl hψ) (by simp) h0
    have hne0 : analyticOrderAt (DirichletCharacter.LFunction ψ) (β : ℂ) ≠ 0 := by
      rw [hL_an.analyticOrderAt_ne_zero]; exact hz
    unfold lZeroMult
    have hcast : (analyticOrderNatAt (DirichletCharacter.LFunction ψ) (β : ℂ) : ℕ∞) =
        analyticOrderAt (DirichletCharacter.LFunction ψ) (β : ℂ) :=
      ENat.natCast_toNat hntop
    have hne0_nat : analyticOrderNatAt (DirichletCharacter.LFunction ψ) (β : ℂ) ≠ 0 := fun h0 => by
      rw [h0, Nat.cast_zero] at hcast; exact hne0 hcast.symm
    omega
  -- Now prove `lZeroMult ψ (β : ℂ) < 2` by evaluating `0 ≤ Re(-ζ'/ζ)(σ) + Re(-L'/L)(σ, ψ)` at `σ = 1 + 4 δ`!
  suffices hlt2 : lZeroMult ψ (β : ℂ) < 2 by omega
  by_contra hge2; push Not at hge2
  set σ : ℝ := 1 + 4 * δ
  have hσ_gt1 : 1 < σ := by dsimp only [σ]; linarith
  have hσ_le2 : σ ≤ 2 := by dsimp only [σ]; linarith
  -- Positivity `0 ≤ Re(-ζ'/ζ)(σ) + Re(-L'/L)(σ, ψ)` from 3-4-1 at `γ = 0` with `ψ ^ 2 = 1`!
  have hpos_sum : 0 ≤ (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re +
      (Stage3ZeroFreeRegion.negLogDerivL ψ (σ : ℂ)).re := by
    have h341 := Stage3ZeroFreeRegion.three_four_one_zeta_negLogDerivL_re_nonneg ψ hσ_gt1 0
    simp only [Complex.ofReal_zero, mul_zero, add_zero, hψ2] at h341
    have h1_le : (Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤
        (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re := by
      have hnorm := Stage5DirichletLZeroFree.norm_negLogDerivL_le_negLogDerivZeta_re
        (1 : DirichletCharacter ℂ q) hσ_gt1 0
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at hnorm
      exact (Complex.re_le_norm _).trans hnorm
    linarith
  have hζ_up : (Stage3ZeroFreeRegion.negLogDerivZeta (σ : ℂ)).re ≤ 1 / (4 * δ) + 1 := by
    have h := Stage5ZetaZeroFree.negLogDerivZeta_real_le hσ_gt1
    have hsub : σ - 1 = 4 * δ := by dsimp only [σ]; ring
    rwa [hsub] at h
  -- Upper bound `(negLogDerivL ψ σ).re` via Hadamard partial fractions `completedLFunction_re_logDeriv_eq_tsum`!
  have hΛ_ne : DirichletCharacter.completedLFunction ψ (σ : ℂ) ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hψ (by simp; linarith)
  have hΛ_re := completedLFunction_re_logDeriv_eq_tsum hprim hψ (s := (σ : ℂ)) (by simp [hσ_gt1])
  have hL_re_le : (Stage3ZeroFreeRegion.negLogDerivL ψ (σ : ℂ)).re ≤
      (1 / 2 : ℝ) * Real.log (q : ℝ) + C_dig * Real.log 2 -
        ∑' n : ℕ, (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re := by
    have hlogpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rcases ψ.even_or_odd with he | ho
    · have heq := negLogDerivL_eq_neg_logDeriv_completedL_even he hψ (by simp; linarith)
        (Complex.ofReal_ne_zero.mpr (by linarith)) hΛ_ne
      have hre := congrArg Complex.re heq
      rw [logDeriv_apply, Complex.add_re, Complex.sub_re, Complex.sub_re, Complex.neg_re,
        Complex.ofReal_re, hΛ_re] at hre
      have hdig := hdig_bd ((σ : ℂ) / 2 + 1) (by simp; linarith) (by simp; linarith)
      have hdig_im : (((σ : ℂ) / 2 + 1).im) = 0 := by simp
      rw [hdig_im, abs_zero, zero_add] at hdig
      have hdig_re : ((1 / 2 : ℂ) * Complex.digamma ((σ : ℂ) / 2 + 1)).re ≤ C_dig * Real.log 2 := by
        have h1 : ((1 / 2 : ℂ) * Complex.digamma ((σ : ℂ) / 2 + 1)).re =
            (1 / 2 : ℝ) * (Complex.digamma ((σ : ℂ) / 2 + 1)).re := by
          simp [Complex.mul_re]
        rw [h1]
        have h2 := (Complex.re_le_norm _).trans hdig
        have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        nlinarith
      have hinv_pos : 0 < (1 / (σ : ℂ)).re := by
        rw [one_div, Complex.inv_re, Complex.ofReal_re, Complex.normSq_ofReal]; positivity
      linarith
    · have heq := negLogDerivL_eq_neg_logDeriv_completedL_odd ho hψ (by simp; linarith) hΛ_ne
      have hre := congrArg Complex.re heq
      rw [logDeriv_apply, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re, hΛ_re] at hre
      have hdig := hdig_bd (((σ : ℂ) + 1) / 2) (by simp; linarith) (by simp; linarith)
      have hdig_im : ((((σ : ℂ) + 1) / 2).im) = 0 := by simp
      rw [hdig_im, abs_zero, zero_add] at hdig
      have hdig_re : ((1 / 2 : ℂ) * Complex.digamma (((σ : ℂ) + 1) / 2)).re ≤ C_dig * Real.log 2 := by
        have h1 : ((1 / 2 : ℂ) * Complex.digamma (((σ : ℂ) + 1) / 2)).re =
            (1 / 2 : ℝ) * (Complex.digamma (((σ : ℂ) + 1) / 2)).re := by
          simp [Complex.mul_re]
        rw [h1]
        have h2 := (Complex.re_le_norm _).trans hdig
        have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        nlinarith
      linarith
  -- Lower bound the nonnegative `tsum` by the `lZeroMult ψ β ≥ 2` terms equal to `β`!
  have hterm_nn : ∀ n : ℕ, 0 ≤ (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re := fun n => by
    have hst := completedLZeroSeq_strip hprim hψ n
    rw [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
    exact div_nonneg (by linarith [hst.2]) (Complex.normSq_nonneg _)
  have hterm_summ : Summable (fun n : ℕ => (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re) := by
    have hinv_sq := completedLZeroSeq_summable_inv_sq hprim hψ
    have hfin : {n : ℕ | ‖completedLZeroSeq hprim hψ n‖ ≤ 4}.Finite := by
      refine (finite_completedLZeroSeq_abs_im_le hprim hψ 4).subset fun n hn => ?_
      exact (Complex.abs_im_le_norm _).trans hn
    refine Summable.of_nonneg_of_le hterm_nn (f := fun n =>
      if n ∈ hfin.toFinset then (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re
      else 8 * (‖completedLZeroSeq hprim hψ n‖ ^ 2)⁻¹) ?_ ?_
    · intro n
      by_cases hn : n ∈ hfin.toFinset
      · rw [if_pos hn]
      · rw [if_neg hn]
        have hgt4 : 4 < ‖completedLZeroSeq hprim hψ n‖ := not_le.mp fun h => hn (hfin.mem_toFinset.mpr h)
        have hst := completedLZeroSeq_strip hprim hψ n
        have hnorm_sub : ‖completedLZeroSeq hprim hψ n‖ / 2 ≤ ‖(σ : ℂ) - completedLZeroSeq hprim hψ n‖ := by
          have h1 := norm_sub_norm_le (completedLZeroSeq hprim hψ n) (σ : ℂ)
          have hσn : ‖(σ : ℂ)‖ ≤ 2 := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
          rw [norm_sub_rev]; linarith
        have hsq : ‖completedLZeroSeq hprim hψ n‖ ^ 2 / 4 ≤ Complex.normSq ((σ : ℂ) - completedLZeroSeq hprim hψ n) := by
          rw [Complex.normSq_eq_norm_sq]
          have := pow_le_pow_left₀ (by positivity) hnorm_sub 2
          linarith
        rw [one_div, Complex.inv_re, Complex.sub_re, Complex.ofReal_re]
        calc (σ - (completedLZeroSeq hprim hψ n).re) / Complex.normSq ((σ : ℂ) - completedLZeroSeq hprim hψ n)
            ≤ 2 / (‖completedLZeroSeq hprim hψ n‖ ^ 2 / 4) :=
              div_le_div₀ (by norm_num) (by linarith [hst.1]) (by positivity) hsq
          _ = 8 * (‖completedLZeroSeq hprim hψ n‖ ^ 2)⁻¹ := by ring
    · have hdiff_s : Summable (fun n : ℕ =>
          (if n ∈ hfin.toFinset then (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re
           else 8 * (‖completedLZeroSeq hprim hψ n‖ ^ 2)⁻¹) -
          8 * (‖completedLZeroSeq hprim hψ n‖ ^ 2)⁻¹) :=
        summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => by rw [if_neg hn, sub_self]
      exact (hdiff_s.add (hinv_sq.mul_left 8)).congr fun n => by ring
  set F_β : Finset ℕ := (finite_completedLZeroSeq_abs_im_le hprim hψ 1).toFinset.filter
    fun n => completedLZeroSeq hprim hψ n = (β : ℂ)
  have hFβ_card : F_β.card = lZeroMult ψ (β : ℂ) := by
    have hord_Λ : lZeroMult ψ (β : ℂ) = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ) (β : ℂ) := by
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hev : DirichletCharacter.completedLFunction ψ =ᶠ[𝓝 (β : ℂ)]
          fun z => DirichletCharacter.LFunction ψ z * DirichletCharacter.gammaFactor ψ z := by
        filter_upwards [hopen.mem_nhds (by simpa using hβ_pos)] with z hz
        exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ hz
      have hL_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) (β : ℂ) :=
        ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
      have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
      have hG_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor ψ) (β : ℂ) := by
        refine DifferentiableOn.analyticAt ?_ (hopen.mem_nhds (by simpa using hβ_pos))
        intro z hz; have hz_re : 0 < z.re := hz
        rcases ψ.even_or_odd with he | ho
        · have hfun : DirichletCharacter.gammaFactor ψ =
              fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) :=
            funext fun w => by rw [he.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
          rw [hfun]
          exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2))) z).mul
            ((Complex.differentiableAt_Gamma (z / 2) fun k hEq => by
              have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
              (differentiableAt_id.div_const 2))).differentiableWithinAt
        · have hfun : DirichletCharacter.gammaFactor ψ =
              fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2)) * Complex.Gamma ((w + 1) / 2) :=
            funext fun w => by rw [ho.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
          rw [hfun]
          exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2))) z).mul
            ((Complex.differentiableAt_Gamma ((z + 1) / 2) fun k hEq => by
              have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
              ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2))).differentiableWithinAt
      have heq := analyticOrderAt_congr hev
      unfold lZeroMult; simp only [analyticOrderNatAt, heq]
      exact (analyticOrderNatAt_mul_of_ne_zero hL_an hG_an (gammaFactor_ne_zero_of_re_pos ψ (by simpa using hβ_pos))).symm
    rw [hord_Λ]
    exact (((isMultiplicityZeroSeq_completedLFunction hprim hψ).2 (β : ℂ)).2 F_β fun n => by
      simp only [F_β, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(finite_completedLZeroSeq_abs_im_le hprim hψ 1).mem_toFinset.mpr
        (by change |(completedLZeroSeq hprim hψ n).im| ≤ 1; rw [h]; simp), h⟩⟩)
  have htsum_ge : 2 / (5 * δ) ≤ ∑' n : ℕ, (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re := by
    have h1 : ∑ n ∈ F_β, (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re ≤
        ∑' n : ℕ, (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re :=
      hterm_summ.sum_le_tsum F_β fun n _ => hterm_nn n
    have hsum_val : ∑ n ∈ F_β, (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re =
        (F_β.card : ℝ) * (1 / (5 * δ)) := by
      have hterm_eq : ∀ n ∈ F_β, (1 / ((σ : ℂ) - completedLZeroSeq hprim hψ n)).re = 1 / (5 * δ) := fun n hn => by
        rw [(Finset.mem_filter.mp hn).2, ← Complex.ofReal_sub, one_div, ← Complex.ofReal_inv,
          Complex.ofReal_re, ← one_div]
        congr 1; dsimp only [σ, δ]; ring
      rw [Finset.sum_congr rfl hterm_eq, Finset.sum_const, nsmul_eq_mul]
    rw [hsum_val, hFβ_card] at h1
    have hm2 : (2 : ℝ) ≤ (lZeroMult ψ (β : ℂ) : ℝ) := by exact_mod_cast hge2
    have h2 : 2 / (5 * δ) ≤ (lZeroMult ψ (β : ℂ) : ℝ) * (1 / (5 * δ)) := by
      rw [show (2 : ℝ) / (5 * δ) = 2 * (1 / (5 * δ)) by ring]
      exact mul_le_mul_of_nonneg_right hm2 (by positivity)
    exact h2.trans h1
  -- Contradiction: `0 ≤ (1/(4δ) - 2/(5δ)) + (1/2) log q + 1 + C_dig log 2 < 0`!
  have hcomb : 3 / (20 * δ) ≤ (1 / 2 : ℝ) * Real.log (q : ℝ) + 1 + C_dig * Real.log 2 := by
    have hdiff : 1 / (4 * δ) - 2 / (5 * δ) = -(3 / (20 * δ)) := by field_simp [hδ_pos.ne']; ring
    linarith
  have hlogq_le : Real.log (q : ℝ) ≤ Real.log (2 * (q : ℝ)) := Real.log_le_log (by positivity) (by linarith)
  have hlog2_le : Real.log 2 ≤ Real.log (2 * (q : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hrhs_le : (1 / 2 : ℝ) * Real.log (q : ℝ) + 1 + C_dig * Real.log 2 ≤ (2 + C_dig) * Real.log (2 * (q : ℝ)) := by
    nlinarith
  have hlhs_ge : 6 * (2 + C_dig) * Real.log (2 * (q : ℝ)) ≤ 3 / (20 * δ) := by
    have h1 : 3 / (20 * (c / Real.log (2 * (q : ℝ)))) ≤ 3 / (20 * δ) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    have h2 : 3 / (20 * (c / Real.log (2 * (q : ℝ)))) = 6 * (2 + C_dig) * Real.log (2 * (q : ℝ)) := by
      dsimp only [c]; field_simp [hlog2q_pos.ne', (by positivity : (0 : ℝ) < 2 + C_dig).ne']; ring
    linarith
  nlinarith

/-- **EXACT DEURING–HEILBRONN ZERO-REPULSION PREDICATE** (matching `Stage11DeuringHeilbronn`):
if a primitive real non-principal character `χ₁ mod q₁` has a real zero `β₁ ∈ (1/2, 1)` close to `1`,
then every other critical-strip zero `ρ` (`|ρ.im| ≤ T`) of any primitive `χ mod q` satisfies
`1 - ρ.re ≥ c₁ * log(c₂ / ((1 - β₁) * log(q * q₁ * T))) / log(q * q₁ * T)`. -/
def DeuringHeilbronnHypothesis : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁),
      χ₁.IsPrimitive → χ₁ ^ 2 = 1 → χ₁ ≠ 1 →
      ∀ β₁ : ℝ, 1 / 2 < β₁ → β₁ < 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive →
        ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
        (PChar.of χ ≠ PChar.of χ₁ ∨ ρ ≠ (β₁ : ℂ)) →
        ∀ T : ℝ, 2 ≤ T → |ρ.im| ≤ T →
        1 - β₁ < c₂ / Real.log ((q : ℝ) * (q₁ : ℝ) * T) →
        1 - ρ.re ≥ c₁ * Real.log (c₂ / ((1 - β₁) * Real.log ((q : ℝ) * (q₁ : ℝ) * T))) /
          Real.log ((q : ℝ) * (q₁ : ℝ) * T)

/-- Multiplicity-counted total number of zeros of all `χ mod m` in `σ ≤ Re(ρ) < 1`, `|Im(ρ)| ≤ T`:
`∑_{χ mod m} N(σ, T, χ)`. -/
noncomputable def dirichletZeroBoxCount (m : ℕ) [NeZero m] (σ T : ℝ) : ℕ :=
  ∑ χ : DirichletCharacter ℂ m,
    ∑ ρ ∈ (lZerosInBox χ T).filter (fun ρ => σ ≤ ρ.re), lZeroMult χ ρ

/-- **EXACT LOG-FREE ZERO-DENSITY PREDICATE** (matching `Stage11LogFreeDensity`):
`∑_{χ mod m} N(σ, T, χ) ≤ C * (m * (T + 2)) ^ (A * (1 - σ))` uniformly for `m ≥ 2`,
`1/2 ≤ σ ≤ 1`, `T ≥ 1`. -/
def LogFreeZeroDensityHypothesis : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
    ∀ (m : ℕ) [NeZero m], 2 ≤ m →
    ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (dirichletZeroBoxCount m σ T : ℝ) ≤ C * ((m : ℝ) * (T + 2)) ^ (A * (1 - σ))

/-! ## Section 4: Complete Linnik Reduction `(Deuring–Heilbronn + Log-Free Density) → LinnikAPDyadic → LinnikAPInterval` -/

/-- Elementary lower bound `(1 / 2) * min 1 u ≤ 1 - Real.exp (-u)` for all `u ≥ 0`. -/
private lemma half_min_one_le_one_sub_exp_neg {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2 : ℝ) * min 1 u ≤ 1 - Real.exp (-u) := by
  have h1 : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp u])
  have h2 : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    have hsub : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp [(by linarith : (0 : ℝ) < 1 + u).ne']; ring
    linarith
  rcases le_total u 1 with hle | hge
  · rw [min_eq_right hle]
    have h3 : (1 / 2 : ℝ) * u ≤ u / (1 + u) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  · rw [min_eq_left hge]
    have h3 : (1 / 2 : ℝ) * 1 ≤ u / (1 + u) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    linarith

/-- At a fixed modulus `m`, two characters with the same primitive character (`PChar.of χ₁ = PChar.of χ₂`)
are equal! -/
private lemma eq_of_pchar_of_eq {m : ℕ} [NeZero m] {χ₁ χ₂ : DirichletCharacter ℂ m}
    (h : PChar.of χ₁ = PChar.of χ₂) : χ₁ = χ₂ := by
  ext u
  have hnat : (((u : ZMod m).val : ℕ) : ZMod m) = (u : ZMod m) := ZMod.natCast_zmod_val (u : ZMod m)
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁.primitiveCharacter χ₁.conductor_dvd_level u
  have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂.primitiveCharacter χ₂.conductor_dvd_level u
  rw [χ₁.changeLevel_primitiveCharacter] at h1
  rw [χ₂.changeLevel_primitiveCharacter] at h2
  rw [h1, h2, ← hnat, ZMod.cast_natCast χ₁.conductor_dvd_level, ZMod.cast_natCast χ₂.conductor_dvd_level]
  exact congrArg (fun P : PChar => P.χ ((u : ZMod m).val : ZMod P.N)) h

/-- Helper: `Real.log x ≤ 4 * x ^ (1 / 4 : ℝ)` for all `x ≥ 1`. -/
private lemma log_le_four_mul_rpow_quarter {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
  linarith [show x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * x ^ (1 / 4 : ℝ) by ring]

/-- **Right-Half Zero-Sum Bound from Log-Free Zero Density (`0` Additional Assumptions!)**:
given `LogFreeZeroDensityHypothesis` with constants `(C_D, A)`, if every zero `(χ, ρ)` in the
right half `1 / 2 ≤ ρ.re < 1`, `|ρ.im| ≤ T₀` satisfying `bad χ ρ` obeys the zero-free gap
`lam₀ / log M ≤ 1 - ρ.re` (where `M = m * (T₀ + 2)` and `R = log X / log M ≥ max (2 * A) 2`),
then `∑_χ ∑_{ρ ∈ right, bad} m_ρ * X ^ (ρ.re - 1) ≤ 2 * C_D * exp A * exp (-(R / 2) * lam₀)`. -/
lemma sum_right_half_zeros_le_of_logfree {C_D A : ℝ} (hCD : 0 < C_D) (hA : 1 ≤ A)
    (hLF : ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (dirichletZeroBoxCount m σ T : ℝ) ≤ C_D * ((m : ℝ) * (T + 2)) ^ (A * (1 - σ)))
    {m : ℕ} [NeZero m] (hm : 2 ≤ m) {T₀ X lam₀ : ℝ} (hT₀ : 1 ≤ T₀) (hX : 4 ≤ X) (hlam₀ : 0 ≤ lam₀)
    (bad : DirichletCharacter ℂ m → ℂ → Prop) [∀ χ ρ, Decidable (bad χ ρ)]
    (hgap : ∀ (χ : DirichletCharacter ℂ m) (ρ : ℂ), ρ ∈ lZerosInBox χ T₀ → 1 / 2 ≤ ρ.re →
      bad χ ρ → lam₀ / Real.log ((m : ℝ) * (T₀ + 2)) ≤ 1 - ρ.re)
    (hR : max (2 * A) 2 ≤ Real.log X / Real.log ((m : ℝ) * (T₀ + 2))) :
    ∑ χ : DirichletCharacter ℂ m,
      ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ),
        (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
      2 * C_D * Real.exp A * Real.exp (-(Real.log X / Real.log ((m : ℝ) * (T₀ + 2)) / 2) * lam₀) := by
  classical
  set M : ℝ := (m : ℝ) * (T₀ + 2)
  set L_M : ℝ := Real.log M
  set R : ℝ := Real.log X / L_M
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM_ge6 : (6 : ℝ) ≤ M := by dsimp only [M]; nlinarith
  have hM_pos : 0 < M := by linarith
  have hLM_gt1 : 1 < L_M := by
    have : Real.exp 1 < M := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLM_pos : 0 < L_M := zero_lt_one.trans hLM_gt1
  have hX0 : 0 < X := by linarith
  have hR_2A : 2 * A ≤ R := (le_max_left _ _).trans hR
  have hR_2 : 2 ≤ R := (le_max_right _ _).trans hR
  have hRA_ge : R / 2 ≤ R - A := by linarith
  have hRA_ge1 : 1 ≤ R - A := by linarith
  set K : ℕ := ⌈L_M⌉₊ + 1
  let σ_slice : ℕ → ℝ := fun j => 1 - (lam₀ + (j : ℝ)) / L_M
  let s_slice : ℕ → ℝ := fun j => max (1 / 2 : ℝ) (σ_slice (j + 1))
  let F : DirichletCharacter ℂ m → Finset ℂ :=
    fun χ => (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ)
  let slice : ℕ → DirichletCharacter ℂ m → Finset ℂ :=
    fun j χ => (F χ).filter fun ρ =>
      (lam₀ + (j : ℝ)) / L_M ≤ 1 - ρ.re ∧ 1 - ρ.re < (lam₀ + ((j : ℝ) + 1)) / L_M
  -- Every `ρ ∈ F χ` belongs to `slice j χ` for some `j < K`
  have hcover : ∀ χ : DirichletCharacter ℂ m, F χ ⊆ (Finset.range K).biUnion (fun j => slice j χ) := by
    intro χ ρ hρ
    rw [Finset.mem_biUnion]
    obtain ⟨hρ_box, hre_half, hbad⟩ := Finset.mem_filter.mp hρ
    have hgap_ρ := hgap χ ρ hρ_box hre_half hbad
    set u : ℝ := (1 - ρ.re) * L_M - lam₀
    have hu_nn : 0 ≤ u := by
      dsimp only [u]; linarith [(div_le_iff₀ hLM_pos).mp hgap_ρ]
    have hu_lt_K : u < (K : ℝ) := by
      have h1 : 1 - ρ.re ≤ 1 / 2 := by linarith
      have h2 : (1 - ρ.re) * L_M ≤ L_M := by nlinarith
      have h3 : L_M ≤ (⌈L_M⌉₊ : ℝ) := Nat.le_ceil L_M
      dsimp only [K, u]; push_cast; linarith
    set j : ℕ := ⌊u⌋₊
    have hj_lt_K : j < K := by
      have h1 : (j : ℝ) ≤ u := Nat.floor_le hu_nn
      exact_mod_cast (h1.trans_lt hu_lt_K)
    refine ⟨j, Finset.mem_range.mpr hj_lt_K, Finset.mem_filter.mpr ⟨hρ, ?_, ?_⟩⟩
    · rw [div_le_iff₀ hLM_pos]
      have h1 : (j : ℝ) ≤ u := Nat.floor_le hu_nn
      dsimp only [u] at h1; linarith
    · rw [lt_div_iff₀ hLM_pos]
      have h1 : u < (j : ℝ) + 1 := Nat.lt_floor_add_one u
      dsimp only [u] at h1; linarith
  -- Bound each character's sum by the sum over `j < K`
  have hchar_le : ∀ χ : DirichletCharacter ℂ m,
      ∑ ρ ∈ F χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
        ∑ j ∈ Finset.range K, ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := by
    intro χ
    have h1 : ∑ ρ ∈ F χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
        ∑ ρ ∈ (Finset.range K).biUnion (fun j => slice j χ), (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (hcover χ) fun _ _ _ => by positivity
    have hbi : ∀ N : ℕ, ∑ ρ ∈ (Finset.range N).biUnion (fun j => slice j χ),
          (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
        ∑ j ∈ Finset.range N, ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
        have hu : ∑ ρ ∈ slice N χ ∪ (Finset.range N).biUnion (fun j => slice j χ),
              (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
            (∑ ρ ∈ slice N χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)) +
            ∑ ρ ∈ (Finset.range N).biUnion (fun j => slice j χ),
              (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := by
          rw [← Finset.sum_union_inter]
          have hnn_inter : 0 ≤ ∑ ρ ∈ slice N χ ∩ (Finset.range N).biUnion (fun j => slice j χ),
              (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) :=
            Finset.sum_nonneg fun _ _ => by positivity
          linarith
        linarith
    exact h1.trans (hbi K)
  -- Bound each slice `j` summed over ALL `χ mod m`
  have hslice_bd : ∀ j : ℕ,
      ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
        C_D * Real.exp A * Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j := by
    intro j
    have hs_lo : 1 / 2 ≤ s_slice j := le_max_left _ _
    have hs_hi : s_slice j ≤ 1 := max_le (by norm_num) (by
      dsimp only [σ_slice]; have hnn : 0 ≤ (lam₀ + ((j + 1 : ℕ) : ℝ)) / L_M := by positivity
      linarith)
    have h1_sub_s : 1 - s_slice j ≤ (lam₀ + (j : ℝ) + 1) / L_M := by
      have h1 : σ_slice (j + 1) ≤ s_slice j := le_max_right _ _
      dsimp only [σ_slice] at h1; push_cast at h1; rw [← add_assoc] at h1; linarith
    have hterm_le : ∀ χ : DirichletCharacter ℂ m, ∀ ρ ∈ slice j χ,
        (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤
          (lZeroMult χ ρ : ℝ) * Real.exp (-R * (lam₀ + (j : ℝ))) := by
      intro χ ρ hρ
      have hlo := (Finset.mem_filter.mp hρ).2.1
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [Real.rpow_def_of_pos hX0]
      refine Real.exp_le_exp.mpr ?_
      have hlogX_eq : Real.log X = R * L_M := by dsimp only [R]; field_simp [hLM_pos.ne']
      rw [hlogX_eq]
      have h1 : (lam₀ + (j : ℝ)) ≤ (1 - ρ.re) * L_M := (div_le_iff₀ hLM_pos).mp hlo
      have hR_pos : 0 ≤ R := by linarith
      nlinarith
    have hsub_s : ∀ χ : DirichletCharacter ℂ m,
        slice j χ ⊆ (lZerosInBox χ T₀).filter (fun ρ => s_slice j ≤ ρ.re) := by
      intro χ ρ hρ
      rcases Finset.mem_filter.mp hρ with ⟨hF, _, hhi⟩
      rcases Finset.mem_filter.mp hF with ⟨hbox, hhalf, _⟩
      refine Finset.mem_filter.mpr ⟨hbox, max_le hhalf ?_⟩
      dsimp only [σ_slice]; push_cast; linarith
    have hcount_le : ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) ≤
        (dirichletZeroBoxCount m (s_slice j) T₀ : ℝ) := by
      unfold dirichletZeroBoxCount
      push_cast
      refine Finset.sum_le_sum fun χ _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (hsub_s χ) fun _ _ _ => Nat.cast_nonneg _
    have hlf := hLF m hm (s_slice j) T₀ hs_lo hs_hi hT₀
    have hM_pow : M ^ (A * (1 - s_slice j)) ≤ Real.exp (A * (lam₀ + (j : ℝ) + 1)) := by
      rw [Real.rpow_def_of_pos hM_pos]
      refine Real.exp_le_exp.mpr ?_
      have h1 : L_M * (A * (1 - s_slice j)) = A * ((1 - s_slice j) * L_M) := by ring
      rw [h1]
      have h2 : (1 - s_slice j) * L_M ≤ lam₀ + (j : ℝ) + 1 := (le_div_iff₀ hLM_pos).mp h1_sub_s
      nlinarith
    have hexp_prod : Real.exp (A * (lam₀ + (j : ℝ) + 1)) * Real.exp (-R * (lam₀ + (j : ℝ))) ≤
        Real.exp A * Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j := by
      rw [← Real.exp_add]
      have hsplit : A * (lam₀ + (j : ℝ) + 1) + (-R * (lam₀ + (j : ℝ))) =
          A + (-(R - A) * lam₀) + (-(R - A) * (j : ℝ)) := by ring
      rw [hsplit, Real.exp_add, Real.exp_add]
      have h1 : Real.exp (-(R - A) * lam₀) ≤ Real.exp (-(R / 2) * lam₀) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (-(R - A) * (j : ℝ)) ≤ (1 / 2 : ℝ) ^ j := by
        have hstep1 : Real.exp (-(R - A) * (j : ℝ)) ≤ Real.exp (-((j : ℝ))) :=
          Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
        have hstep2 : Real.exp (-((j : ℝ))) = (Real.exp (-1)) ^ j := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        have hstep3 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (by norm_num) (by linarith [Real.exp_one_gt_d9])
        rw [hstep2] at hstep1
        exact hstep1.trans (pow_le_pow_left₀ (Real.exp_pos _).le hstep3 j)
      have hmul := mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
      calc Real.exp A * Real.exp (-(R - A) * lam₀) * Real.exp (-(R - A) * (j : ℝ))
          = Real.exp A * (Real.exp (-(R - A) * lam₀) * Real.exp (-(R - A) * (j : ℝ))) := by ring
        _ ≤ Real.exp A * (Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left hmul (Real.exp_pos _).le
        _ = Real.exp A * Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j := by ring
    calc ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)
        ≤ ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ slice j χ,
            (lZeroMult χ ρ : ℝ) * Real.exp (-R * (lam₀ + (j : ℝ))) :=
          Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ρ hρ => hterm_le χ ρ hρ
      _ = (∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ)) *
            Real.exp (-R * (lam₀ + (j : ℝ))) := by
          simp_rw [← Finset.sum_mul]
      _ ≤ (C_D * Real.exp (A * (lam₀ + (j : ℝ) + 1))) * Real.exp (-R * (lam₀ + (j : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (hcount_le.trans (hlf.trans (mul_le_mul_of_nonneg_left hM_pow hCD.le))) (Real.exp_pos _).le
      _ = C_D * (Real.exp (A * (lam₀ + (j : ℝ) + 1)) * Real.exp (-R * (lam₀ + (j : ℝ)))) := by ring
      _ ≤ C_D * (Real.exp A * Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hexp_prod hCD.le
      _ = C_D * Real.exp A * Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j := by ring
  calc ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ F χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)
      ≤ ∑ χ : DirichletCharacter ℂ m, ∑ j ∈ Finset.range K,
          ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) :=
        Finset.sum_le_sum fun χ _ => hchar_le χ
    _ = ∑ j ∈ Finset.range K, ∑ χ : DirichletCharacter ℂ m,
          ∑ ρ ∈ slice j χ, (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range K, C_D * Real.exp A * Real.exp (-(R / 2) * lam₀) * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum fun j _ => hslice_bd j
    _ = (C_D * Real.exp A * Real.exp (-(R / 2) * lam₀)) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (C_D * Real.exp A * Real.exp (-(R / 2) * lam₀)) * 2 :=
        mul_le_mul_of_nonneg_left (sum_half_pow_le_two K) (by positivity)
    _ = 2 * C_D * Real.exp A * Real.exp (-(R / 2) * lam₀) := by ring

/-- **HEADLINE PHASE B BRIDGE (`(Deuring–Heilbronn + Log-Free Zero Density) → Stage2PrimePairs.LinnikAPDyadic`)**:
completely unconditional reduction (`0` extra assumptions beyond `DeuringHeilbronnHypothesis` and
`LogFreeZeroDensityHypothesis`) producing a universal Linnik exponent `L ≥ 1` such that for EVERY
modulus `m ≥ 2`, EVERY `a` coprime to `m`, and EVERY `X ≥ m ^ L`, there exists a prime
`p ≡ a [MOD m]` in the dyadic interval `(X, 2 * X]`. -/
theorem linnikAPDyadic_of_dh_and_logfree
    (hDH : DeuringHeilbronnHypothesis) (hLF : LogFreeZeroDensityHypothesis) :
    Stage2PrimePairs.LinnikAPDyadic := by
  classical
  obtain ⟨c₁, c₂, hc₁_pos, hc₂_pos, hdh⟩ := hDH
  obtain ⟨C_D, A, hCD_pos, hA_ge1, hlf⟩ := hLF
  obtain ⟨C_exp, hCexp_pos, hexp_ap⟩ := smoothed_ap_dyadic_explicit_formula
  obtain ⟨C_tail, hCtail_pos, htail_bd⟩ := sum_tail_inv_im_sq_lZeros_le
  obtain ⟨C_cnt, hCcnt_pos, hcnt_bd⟩ := lZeroCount_box_le
  obtain ⟨c_ζ, hcζ_pos, hzf_ζ⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  obtain ⟨c_simp, hcsimp_pos, hsimp⟩ := siegel_zero_simple_unconditional
  obtain ⟨c_S, hcS_pos, hsiegel_excl⟩ := Stage9LandauSiegel.siegel_real_zero_exclusion (1 / 2) (by norm_num)
  -- Universal Siegel-zero threshold `δ₀` and uniform lower-bound constant `c_S'` for `η`
  set δ₀ : ℝ := min (1 / 60000) (min c_ζ (min (c_simp / 4) (min (c₂ / 4) (1 / 4))))
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_60k : δ₀ ≤ 1 / 60000 := min_le_left _ _
  have hδ₀_ζ : δ₀ ≤ c_ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀_simp : δ₀ ≤ c_simp / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₀_c2 : δ₀ ≤ c₂ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ₀_qtr : δ₀ ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  set c_S' : ℝ := min 1 c_S
  have hcS'_pos : 0 < c_S' := by positivity
  -- Choose `C_T0 ≥ 4` so `T₀ = C_T0 * m ^ 3` crushes the high-`|γ| > T₀` tail for ALL `m ≥ 2`!
  set K_tail : ℝ := max 16 (2560 * C_tail / c_S')
  have hKtail_ge16 : 16 ≤ K_tail := le_max_left _ _
  set C_T0 : ℝ := 4 * K_tail ^ 2
  have hCT0_ge4 : 4 ≤ C_T0 := by dsimp only [C_T0]; nlinarith
  have hCT0_pos : 0 < C_T0 := by linarith
  -- Choose `K_M : ℕ` so `M = m * (C_T0 * m ^ 3 + 2) ≤ m ^ K_M` for ALL `m ≥ 2`
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K_M : ℕ := 4 + ⌈Real.log (C_T0 + 2) / Real.log 2⌉₊ + 1
  have hKM_ge5 : 5 ≤ K_M := by dsimp only [K_M]; omega
  -- Choose `R₀` large enough to crush right-half zeros (Cases 1 & 2) AND left-half zeros!
  set B_right : ℝ := max 1 (32 * C_D * Real.exp A * (1 + 2 / c₂))
  have hBright_ge1 : 1 ≤ B_right := le_max_left _ _
  have hBright_ge_expr : 32 * C_D * Real.exp A * (1 + 2 / c₂) ≤ B_right := le_max_right _ _
  set R_c1 : ℝ := (2 / δ₀) * Real.log (2 * B_right)
  set R_c2 : ℝ := (4 / c₁) * (1 + Real.log (2 * B_right) / Real.log 2)
  set R_left : ℝ := 12 + 2 * (Real.log (64 * C_cnt / c_S' + 1) / Real.log 2)
  set R₀ : ℝ := max (max (2 * A) 12) (max (max R_c1 R_c2) (max R_left (8 / c₁)))
  have hR0_2A : 2 * A ≤ R₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hR0_12 : 12 ≤ R₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hR0_c1 : R_c1 ≤ R₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hR0_c2 : R_c2 ≤ R₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hR0_left : R_left ≤ R₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hR0_8c1 : 8 / c₁ ≤ R₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  -- Final Linnik exponent `L`
  set L_err : ℝ := 20 + 4 * (Real.log (64 * (260 * C_exp + 8) / c_S' + 1) / Real.log 2)
  set L : ℝ := max ((K_M : ℝ) * R₀) L_err
  have hL_ge20 : 20 ≤ L := by
    have hnn : 0 ≤ Real.log (64 * (260 * C_exp + 8) / c_S' + 1) / Real.log 2 :=
      div_nonneg (Real.log_nonneg (by linarith [div_pos (by positivity : 0 < 64 * (260 * C_exp + 8)) hcS'_pos])) hlog2_pos.le
    exact (by dsimp only [L_err]; linarith : 20 ≤ L_err).trans (le_max_right _ _)
  refine ⟨L, by linarith, fun m a hm hcop X hX_mL => ?_⟩
  have : NeZero m := ⟨by omega⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlogm_pos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hlog2_le_m : Real.log 2 ≤ Real.log (m : ℝ) := Real.log_le_log (by norm_num) hmR
  -- Basic lower bounds on `X`
  have hX_ge_m20 : (m : ℝ) ^ (20 : ℝ) ≤ X :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hL_ge20).trans hX_mL
  have hX_ge4 : 4 ≤ X := by
    have h2 : (4 : ℝ) ≤ (m : ℝ) ^ (20 : ℝ) := by
      rw [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (by norm_num : (4 : ℝ) ≤ 2 ^ 20).trans (pow_le_pow_left₀ (by norm_num) hmR 20)
    linarith
  have hX0 : 0 < X := by linarith
  have hlogX_gt1 : 1 < Real.log X := by
    have : Real.exp 1 < X := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  -- Setup `T₀ = C_T0 * m^3`, `M = m * (T₀ + 2)`, `L_M = log M`, `R = log X / L_M ≥ R₀`
  set T₀ : ℝ := C_T0 * (m : ℝ) ^ 3
  have hT₀_ge4 : 4 ≤ T₀ := by
    have hm3 : (8 : ℝ) ≤ (m : ℝ) ^ 3 := by
      have : (2 : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hmR 3
      linarith
    dsimp only [T₀]; nlinarith
  set M : ℝ := (m : ℝ) * (T₀ + 2)
  set L_M : ℝ := Real.log M
  set R : ℝ := Real.log X / L_M
  have hM_ge12 : 12 ≤ M := by dsimp only [M]; nlinarith
  have hM_pos : 0 < M := by linarith
  have hLM_gt1 : 1 < L_M := by
    have : Real.exp 1 < M := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLM_pos : 0 < L_M := zero_lt_one.trans hLM_gt1
  have hM_le_mKM : M ≤ (m : ℝ) ^ K_M := by
    have hC2_le : C_T0 + 2 ≤ (2 : ℝ) ^ (⌈Real.log (C_T0 + 2) / Real.log 2⌉₊ + 1) := by
      have h1 : Real.log (C_T0 + 2) ≤ ((⌈Real.log (C_T0 + 2) / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * Real.log 2 := by
        have hceil := Nat.le_ceil (Real.log (C_T0 + 2) / Real.log 2)
        have h2 := (div_le_iff₀ hlog2_pos).mp hceil
        push_cast; linarith
      rw [← Real.rpow_natCast (2 : ℝ), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      exact (Real.log_le_iff_le_exp (by linarith)).mp h1
    have hC2_m : C_T0 + 2 ≤ (m : ℝ) ^ (⌈Real.log (C_T0 + 2) / Real.log 2⌉₊ + 1) :=
      hC2_le.trans (pow_le_pow_left₀ (by norm_num) hmR _)
    have hM_step : M ≤ (C_T0 + 2) * (m : ℝ) ^ 4 := by
      have hm3_ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ (by linarith)
      dsimp only [M, T₀]; nlinarith
    calc M ≤ (C_T0 + 2) * (m : ℝ) ^ 4 := hM_step
      _ ≤ (m : ℝ) ^ (⌈Real.log (C_T0 + 2) / Real.log 2⌉₊ + 1) * (m : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hC2_m (by positivity)
      _ = (m : ℝ) ^ K_M := by rw [← pow_add]; congr 1; dsimp only [K_M]; omega
  have hLM_le : L_M ≤ (K_M : ℝ) * Real.log (m : ℝ) := by
    calc L_M ≤ Real.log ((m : ℝ) ^ K_M) := Real.log_le_log hM_pos hM_le_mKM
      _ = (K_M : ℝ) * Real.log (m : ℝ) := Real.log_pow _ _
  have hlogX_ge_L : L * Real.log (m : ℝ) ≤ Real.log X := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hm_pos L) hX_mL
    rwa [Real.log_rpow hm_pos] at h1
  have hR_ge_R0 : R₀ ≤ R := by
    dsimp only [R]
    rw [le_div_iff₀ hLM_pos]
    have h1 : R₀ * L_M ≤ ((K_M : ℝ) * R₀) * Real.log (m : ℝ) := by
      have hR0_nn : 0 ≤ R₀ := by linarith
      nlinarith
    have h2 : ((K_M : ℝ) * R₀) * Real.log (m : ℝ) ≤ L * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hlogm_pos.le
    linarith
  have hX_ge_MR0 : M ^ R₀ ≤ X := by
    rw [Real.rpow_def_of_pos hM_pos, ← Real.le_log_iff_exp_le hX0]
    have := (le_div_iff₀ hLM_pos).mp hR_ge_R0
    nlinarith
  -- Apply `smoothed_ap_dyadic_explicit_formula` at `T_big := X ^ 2`
  set T_big : ℝ := X ^ 2
  have hTbig_ge_T0 : T₀ ≤ T_big := by
    have h1 : M ≤ M ^ R₀ := by
      calc M = M ^ (1 : ℝ) := (Real.rpow_one M).symm
        _ ≤ M ^ R₀ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : T₀ ≤ M := by dsimp only [M]; nlinarith
    have h3 : X ≤ X ^ 2 := by nlinarith
    dsimp only [T_big]; linarith
  have hTbig_ge4 : 4 ≤ T_big := by linarith
  have hef := hexp_ap m a hm hcop X T_big hX_ge4 hTbig_ge4
  -- Uniform lower bound constant `c_S' / √m`
  have htot_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have htot_le_m : (m.totient : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.totient_le m
  have hcard_char : (Fintype.card (DirichletCharacter ℂ m) : ℝ) = (m.totient : ℝ) :=
    card_dirichletChar_eq_totient_local m
  -- Common error-term bounds (all normalized by `φ(m) / X ^ 2` and bounded by `(1 / 64) * (c_S' / √m)`)!
  -- (A) High-`|γ| > T₀` tail summed over all `χ mod m`:
  have hTail_bd :
      (∑ χ : DirichletCharacter ℂ m,
        ∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
          ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖) ≤
      (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 := by
    have hper_χ : ∀ χ : DirichletCharacter ℂ m,
        ∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
          ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
        20 * C_tail * (Real.log M / T₀) * X ^ 2 := fun χ => by
      have hterm : ∀ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
          ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
            (20 * X ^ 2) * ((lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) := fun ρ hρ => by
        have hm' := mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
        have hre : (ρ + 1).re = ρ.re + 1 := by simp
        rw [hre]
        have hX2 : X ^ (ρ.re + 1) ≤ X ^ 2 :=
          (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hm'.2.1])).trans_eq (Real.rpow_two X)
        have hK := norm_dyadicKernel_le_inv_sq (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
        calc (lZeroMult χ ρ : ℝ) * X ^ (ρ.re + 1) * ‖dyadicKernel ρ‖
            ≤ (lZeroMult χ ρ : ℝ) * X ^ 2 * (20 / (1 + ρ.im ^ 2)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hX2 (Nat.cast_nonneg _)) hK (norm_nonneg _) (by positivity)
          _ = (20 * X ^ 2) * ((lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) := by ring
      calc ∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|), _
          ≤ ∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
              (20 * X ^ 2) * ((lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) := Finset.sum_le_sum hterm
        _ = (20 * X ^ 2) * ∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
              (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) := (Finset.mul_sum _ _ _).symm
        _ ≤ (20 * X ^ 2) * (C_tail * Real.log M / T₀) :=
            mul_le_mul_of_nonneg_left (htail_bd m hm χ T₀ T_big (by linarith) hTbig_ge_T0) (by positivity)
        _ = 20 * C_tail * (Real.log M / T₀) * X ^ 2 := by ring
    have hlogM_le : Real.log M ≤ (2 * K_tail + 4) * (m : ℝ) := by
      have hM_le2 : M ≤ 2 * C_T0 * (m : ℝ) ^ 4 := by
        have hm3 : (1 : ℝ) ≤ (m : ℝ) ^ 3 := one_le_pow₀ (by linarith)
        dsimp only [M, T₀]; nlinarith
      have hlog1 : Real.log M ≤ Real.log (2 * C_T0) + 4 * Real.log (m : ℝ) := by
        calc Real.log M ≤ Real.log (2 * C_T0 * (m : ℝ) ^ 4) := Real.log_le_log hM_pos hM_le2
          _ = Real.log (2 * C_T0) + Real.log ((m : ℝ) ^ 4) := Real.log_mul (by positivity) (by positivity)
          _ = Real.log (2 * C_T0) + 4 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
      have hlogC : Real.log (2 * C_T0) ≤ 2 * K_tail := by
        have h1 : 2 * C_T0 = 8 * K_tail ^ 2 := by dsimp only [C_T0]; ring
        rw [h1]
        have hsqrt : Real.sqrt (8 * K_tail ^ 2) ≤ 3 * K_tail := by
          have : 8 * K_tail ^ 2 ≤ (3 * K_tail) ^ 2 := by nlinarith
          exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq (by linarith))
        have hlog_rt : Real.log (8 * K_tail ^ 2) = 2 * Real.log (Real.sqrt (8 * K_tail ^ 2)) := by
          rw [Real.log_sqrt (by positivity)]; ring
        -- Even tighter: `log (8 K^2) = log 8 + 2 log K ≤ 3 + 2 (√K) ≤ 2 K` for `K ≥ 4`!
        have hlogK : Real.log K_tail ≤ K_tail / 2 := by
          have h1' : Real.log K_tail = 2 * Real.log (Real.sqrt K_tail) := by
            rw [Real.log_sqrt (by linarith)]; ring
          have h2' : Real.log (Real.sqrt K_tail) ≤ Real.sqrt K_tail - 1 :=
            Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
          have h3' : 4 * Real.sqrt K_tail ≤ K_tail := by
            have : (4 : ℝ) ≤ Real.sqrt K_tail := Real.le_sqrt_of_sq_le (by linarith)
            nlinarith [Real.sq_sqrt (by linarith : 0 ≤ K_tail)]
          linarith
        have hlog8 : Real.log 8 ≤ 3 := by
          have h1' : Real.log 8 = 3 * Real.log 2 := by
            rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
          linarith [Real.log_two_lt_d9]
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast; linarith
      have hlogm_le : Real.log (m : ℝ) ≤ (m : ℝ) := by linarith [Real.log_le_sub_one_of_pos hm_pos]
      nlinarith
    have hcoeff : (m : ℝ) * (20 * C_tail * (Real.log M / T₀)) ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) := by
      have h1 : Real.log M / T₀ ≤ ((2 * K_tail + 4) / (4 * K_tail ^ 2)) / (m : ℝ) ^ 2 := by
        calc Real.log M / T₀
            ≤ ((2 * K_tail + 4) * (m : ℝ)) / (4 * K_tail ^ 2 * (m : ℝ) ^ 3) := by
              dsimp only [T₀, C_T0]; gcongr
          _ = ((2 * K_tail + 4) / (4 * K_tail ^ 2)) / (m : ℝ) ^ 2 := by
              field_simp [(by positivity : (0 : ℝ) < K_tail).ne', hm_pos.ne']
      have h2 : (2 * K_tail + 4) / (4 * K_tail ^ 2) ≤ 1 / K_tail := by
        rw [div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith
      have h3 : (1 / K_tail) ≤ c_S' / (2560 * C_tail) := by
        have hK_ge : 2560 * C_tail / c_S' ≤ K_tail := le_max_right _ _
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        have := (div_le_iff₀ hcS'_pos).mp hK_ge; linarith
      have hinv_m : 1 / (m : ℝ) ≤ 1 / Real.sqrt (m : ℝ) :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hm_pos)
          ((Real.sqrt_le_sqrt (by nlinarith : (m : ℝ) ≤ (m : ℝ) ^ 2)).trans_eq (Real.sqrt_sq hm_pos.le))
      calc (m : ℝ) * (20 * C_tail * (Real.log M / T₀))
          ≤ (m : ℝ) * (20 * C_tail * (((2 * K_tail + 4) / (4 * K_tail ^ 2)) / (m : ℝ) ^ 2)) := by gcongr
        _ ≤ (m : ℝ) * (20 * C_tail * ((1 / K_tail) / (m : ℝ) ^ 2)) := by gcongr
        _ ≤ (m : ℝ) * (20 * C_tail * ((c_S' / (2560 * C_tail)) / (m : ℝ) ^ 2)) := by gcongr
        _ = (c_S' / 128) * (1 / (m : ℝ)) := by field_simp [hm_pos.ne', hCtail_pos.ne']; ring
        _ ≤ (c_S' / 128) * (1 / Real.sqrt (m : ℝ)) := mul_le_mul_of_nonneg_left hinv_m (by positivity)
        _ ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) := by
            have : 0 ≤ c_S' / Real.sqrt (m : ℝ) := by positivity
            linarith [show (c_S' / 128) * (1 / Real.sqrt (m : ℝ)) = (1 / 128 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) by ring]
    calc ∑ χ : DirichletCharacter ℂ m, _
        ≤ ∑ _χ : DirichletCharacter ℂ m, 20 * C_tail * (Real.log M / T₀) * X ^ 2 :=
          Finset.sum_le_sum fun χ _ => hper_χ χ
      _ = (m.totient : ℝ) * (20 * C_tail * (Real.log M / T₀) * X ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_char]
      _ ≤ (m : ℝ) * (20 * C_tail * (Real.log M / T₀)) * X ^ 2 := by
          have : 0 ≤ 20 * C_tail * (Real.log M / T₀) * X ^ 2 := by positivity
          nlinarith
      _ ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
  -- (B) Left-half zeros `0 < ρ.re < 1/2`, `|ρ.im| ≤ T₀` summed over all `χ mod m`:
  have hLeft_bd :
      (∑ χ : DirichletCharacter ℂ m,
        ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
          ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖) ≤
      (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 := by
    have hper_χ : ∀ χ : DirichletCharacter ℂ m,
        ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
          ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
        C_cnt * T₀ * L_M * X ^ (3 / 2 : ℝ) := fun χ => by
      have hterm : ∀ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
          ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
            (lZeroMult χ ρ : ℝ) * X ^ (3 / 2 : ℝ) := fun ρ hρ => by
        have hm' := mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
        have hlt := (Finset.mem_filter.mp hρ).2
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
        have hre : (ρ + 1).re = ρ.re + 1 := by simp
        rw [hre]
        have hX32 : X ^ (ρ.re + 1) ≤ X ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        have hK := (norm_dyadicKernel_le_quarter (s := ρ) (by linarith [hm'.1]) hm'.2.1.le).trans (by norm_num : (1 / 4 : ℝ) ≤ 1)
        calc (lZeroMult χ ρ : ℝ) * X ^ (ρ.re + 1) * ‖dyadicKernel ρ‖
            ≤ (lZeroMult χ ρ : ℝ) * X ^ (3 / 2 : ℝ) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left hX32 (Nat.cast_nonneg _)) hK (norm_nonneg _) (by positivity)
          _ = (lZeroMult χ ρ : ℝ) * X ^ (3 / 2 : ℝ) := mul_one _
      calc ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2), _
          ≤ ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
              (lZeroMult χ ρ : ℝ) * X ^ (3 / 2 : ℝ) := Finset.sum_le_sum hterm
        _ = (∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2), (lZeroMult χ ρ : ℝ)) * X ^ (3 / 2 : ℝ) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ (∑ ρ ∈ lZerosInBox χ T₀, (lZeroMult χ ρ : ℝ)) * X ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun _ _ _ => Nat.cast_nonneg _) (by positivity)
        _ ≤ (C_cnt * T₀ * L_M) * X ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (hcnt_bd m hm χ T₀ (by linarith)) (by positivity)
        _ = C_cnt * T₀ * L_M * X ^ (3 / 2 : ℝ) := by ring
    have hX32_eq : X ^ (3 / 2 : ℝ) = X ^ 2 * X ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; norm_num
    have hcoeff : (m : ℝ) * (C_cnt * T₀ * L_M) * X ^ (-(1 / 2 : ℝ)) ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) := by
      have hLM_M : L_M ≤ M := by linarith [Real.log_le_sub_one_of_pos hM_pos]
      have hmT_M : (m : ℝ) * T₀ ≤ M := by dsimp only [M]; nlinarith
      have hX_inv_half : X ^ (-(1 / 2 : ℝ)) ≤ M ^ (-(R₀ / 2)) := by
        rw [Real.rpow_neg hX0.le, Real.rpow_neg hM_pos.le]
        refine inv_anti₀ (Real.rpow_pos_of_pos hM_pos _) ?_
        have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hM_pos.le _) hX_ge_MR0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [← Real.rpow_mul hM_pos.le] at h1
        exact h1.trans_eq (by congr 1) |> fun h => by rwa [show R₀ * (1 / 2 : ℝ) = R₀ / 2 by ring] at h
      have hM_pow_split : M ^ 2 * M ^ (-(R₀ / 2)) ≤ M ^ (-(1 : ℝ)) * M ^ (-(R₀ / 2 - 3)) := by
        rw [← Real.rpow_two M, ← Real.rpow_add hM_pos, ← Real.rpow_add hM_pos]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hM_neg1 : M ^ (-(1 : ℝ)) ≤ 1 / Real.sqrt (m : ℝ) := by
        rw [Real.rpow_neg_one, ← one_div]
        refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr hm_pos) ?_
        have hsqrt_m : Real.sqrt (m : ℝ) ≤ (m : ℝ) :=
          (Real.sqrt_le_sqrt (by nlinarith : (m : ℝ) ≤ (m : ℝ) ^ 2)).trans_eq (Real.sqrt_sq hm_pos.le)
        have hm_M : (m : ℝ) ≤ M := by dsimp only [M]; nlinarith
        linarith
      have hM_tail : M ^ (-(R₀ / 2 - 3)) ≤ c_S' / (64 * C_cnt) := by
        have h1 : (2 : ℝ) ^ (R₀ / 2 - 3) ≤ M ^ (R₀ / 2 - 3) :=
          Real.rpow_le_rpow (by norm_num) (by linarith) (by linarith)
        have h2 : 64 * C_cnt / c_S' ≤ (2 : ℝ) ^ (R₀ / 2 - 3) := by
          have hR_step : Real.log (64 * C_cnt / c_S' + 1) / Real.log 2 ≤ R₀ / 2 - 3 := by
            dsimp only [R_left] at hR0_left; linarith
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2)]
          have h3 : 64 * C_cnt / c_S' + 1 ≤ Real.exp ((R₀ / 2 - 3) * Real.log 2) :=
            (Real.log_le_iff_le_exp (by positivity)).mp ((div_le_iff₀ hlog2_pos).mp hR_step)
          linarith
        rw [Real.rpow_neg hM_pos.le]
        have h3 : 64 * C_cnt / c_S' ≤ M ^ (R₀ / 2 - 3) := h2.trans h1
        rw [div_le_iff₀ hcS'_pos] at h3
        rw [le_div_iff₀ (by positivity)]
        have := (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hM_pos _)).mpr (by linarith : 64 * C_cnt ≤ M ^ (R₀ / 2 - 3) * c_S')
        linarith [show (M ^ (R₀ / 2 - 3))⁻¹ * (64 * C_cnt) = (M ^ (R₀ / 2 - 3))⁻¹ * (64 * C_cnt) by rfl]
      calc (m : ℝ) * (C_cnt * T₀ * L_M) * X ^ (-(1 / 2 : ℝ))
          = C_cnt * (((m : ℝ) * T₀) * L_M) * X ^ (-(1 / 2 : ℝ)) := by ring
        _ ≤ C_cnt * (M * M) * M ^ (-(R₀ / 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hmT_M hLM_M hLM_pos.le hM_pos.le) hCcnt_pos.le)
              hX_inv_half (by positivity) (by positivity)
        _ = C_cnt * (M ^ 2 * M ^ (-(R₀ / 2))) := by ring
        _ ≤ C_cnt * (M ^ (-(1 : ℝ)) * M ^ (-(R₀ / 2 - 3))) := mul_le_mul_of_nonneg_left hM_pow_split hCcnt_pos.le
        _ ≤ C_cnt * ((1 / Real.sqrt (m : ℝ)) * (c_S' / (64 * C_cnt))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hM_neg1 hM_tail (by positivity) (by positivity)) hCcnt_pos.le
        _ = (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) := by field_simp [hCcnt_pos.ne']
    calc ∑ χ : DirichletCharacter ℂ m, _
        ≤ ∑ _χ : DirichletCharacter ℂ m, C_cnt * T₀ * L_M * X ^ (3 / 2 : ℝ) :=
          Finset.sum_le_sum fun χ _ => hper_χ χ
      _ = (m.totient : ℝ) * (C_cnt * T₀ * L_M * X ^ (3 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_char]
      _ ≤ (m : ℝ) * (C_cnt * T₀ * L_M) * X ^ (-(1 / 2 : ℝ)) * X ^ 2 := by
          rw [hX32_eq]
          have hnn_rhs : 0 ≤ C_cnt * T₀ * L_M * (X ^ 2 * X ^ (-(1 / 2 : ℝ))) := by positivity
          have hmul := mul_le_mul_of_nonneg_right htot_le_m hnn_rhs
          linarith
      _ ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
  -- (C) Explicit-formula error + prime-power threshold (multiplied by `φ(m)`):
  have hErr_pp_bd :
      (m.totient : ℝ) *
        (C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X)) +
          (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)) ≤
      (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 := by
    have hmX_ge1 : (1 : ℝ) ≤ (m : ℝ) * X :=
      (by norm_num : (1 : ℝ) ≤ 2 * 4).trans (mul_le_mul hmR hX_ge4 (by norm_num) hm_pos.le)
    have hm_le_X : (m : ℝ) ≤ X := by
      have h1 : (m : ℝ) ≤ (m : ℝ) ^ (20 : ℝ) := by
        calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (m : ℝ) ^ (20 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      linarith
    have hlogmX : Real.log ((m : ℝ) * X) ≤ 2 * Real.log X := by
      rw [Real.log_mul hm_pos.ne' hX0.ne']
      linarith [Real.log_le_log hm_pos hm_le_X]
    have hlogTbig : Real.log T_big = 2 * Real.log X := by
      dsimp only [T_big]; rw [Real.log_pow]; norm_num
    have hlogX_rpow : Real.log X ≤ 4 * X ^ (1 / 4 : ℝ) := log_le_four_mul_rpow_quarter (by linarith)
    have hlog2X : Real.log (2 * X) ≤ 8 * X ^ (1 / 4 : ℝ) := by
      have h1 : Real.log (2 * X) ≤ 2 * Real.log X := by
        rw [Real.log_mul (by norm_num) hX0.ne']
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ X)]
      linarith
    have hX_inv34 : X ^ (-(3 / 4 : ℝ)) ≤ X ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hX_inv32 : X ^ (-(3 / 2 : ℝ)) ≤ X ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hterm1 : X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big ≤ 256 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      have hsum_log : Real.log ((m : ℝ) * X) + Real.log T_big ≤ 16 * X ^ (1 / 4 : ℝ) := by linarith
      have hsq : (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 ≤ 256 * X ^ (1 / 2 : ℝ) := by
        have hnn_l1 : 0 ≤ Real.log ((m : ℝ) * X) := Real.log_nonneg hmX_ge1
        have hnn_l2 : 0 ≤ Real.log T_big := Real.log_nonneg (by linarith)
        have h := pow_le_pow_left₀ (by linarith) hsum_log 2
        rw [mul_pow, ← Real.rpow_natCast (X ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hX0.le] at h
        norm_num at h; exact h
      have hcancel : X ^ 2 * (256 * X ^ (1 / 2 : ℝ)) / X ^ 2 = 256 * X ^ (1 / 2 : ℝ) := by
        field_simp [(by positivity : X ^ 2 ≠ 0)]
      have hpow_eq : X ^ (1 / 2 : ℝ) = X ^ (-(3 / 2 : ℝ)) * X ^ 2 := by
        rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; norm_num
      calc X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big
          ≤ X ^ 2 * (256 * X ^ (1 / 2 : ℝ)) / X ^ 2 := by dsimp only [T_big]; gcongr
        _ = 256 * (X ^ (-(3 / 2 : ℝ)) * X ^ 2) := by rw [hcancel, hpow_eq]
        _ ≤ 256 * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by gcongr
        _ = 256 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by ring
    have hterm3 : (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) ≤ 8 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      have hsqrt2 : Real.sqrt (2 * X) ≤ 2 * X ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow X]
        have hrt2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
        exact mul_le_mul_of_nonneg_right hrt2 (Real.rpow_nonneg hX0.le (1 / 2 : ℝ))
      have hpow_eq : X * X ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
        conv_lhs => lhs; lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_two X, ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; norm_num
      calc (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)
          ≤ (X / 2) * (2 * X ^ (1 / 2 : ℝ)) * (8 * X ^ (1 / 4 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hsqrt2 (by positivity)) hlog2X
              (Real.log_nonneg (by linarith)) (by positivity)
        _ = 8 * (X * X ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ)) := by ring
        _ = 8 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by rw [hpow_eq]; ring
    have hcoeff : (m : ℝ) * ((260 * C_exp + 8) * X ^ (-(1 / 4 : ℝ))) ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) := by
      have hX_inv14 : X ^ (-(1 / 4 : ℝ)) ≤ (m : ℝ) ^ (-(L / 4)) := by
        rw [Real.rpow_neg hX0.le, Real.rpow_neg hm_pos.le]
        refine inv_anti₀ (Real.rpow_pos_of_pos hm_pos _) ?_
        have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hm_pos.le _) hX_mL (by norm_num : (0 : ℝ) ≤ 1 / 4)
        rw [← Real.rpow_mul hm_pos.le, show L * (1 / 4 : ℝ) = L / 4 by ring] at h1
        exact h1
      have hm_split : (m : ℝ) * (m : ℝ) ^ (-(L / 4)) ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-(L / 4 - 2)) := by
        conv_lhs => lhs; rw [← Real.rpow_one (m : ℝ)]
        rw [← Real.rpow_add hm_pos, ← Real.rpow_add hm_pos]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hm_tail : (m : ℝ) ^ (-(L / 4 - 2)) ≤ c_S' / (64 * (260 * C_exp + 8)) := by
        have hL_step : Real.log (64 * (260 * C_exp + 8) / c_S' + 1) / Real.log 2 ≤ L / 4 - 2 := by
          have hle : L_err ≤ L := le_max_right _ _
          dsimp only [L_err] at hle; linarith
        have h1 : 64 * (260 * C_exp + 8) / c_S' ≤ (2 : ℝ) ^ (L / 4 - 2) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2)]
          have h2 : 64 * (260 * C_exp + 8) / c_S' + 1 ≤ Real.exp ((L / 4 - 2) * Real.log 2) :=
            (Real.log_le_iff_le_exp (by positivity)).mp ((div_le_iff₀ hlog2_pos).mp hL_step)
          linarith
        have h2 : (2 : ℝ) ^ (L / 4 - 2) ≤ (m : ℝ) ^ (L / 4 - 2) :=
          Real.rpow_le_rpow (by norm_num) hmR (by linarith)
        have h3 : 64 * (260 * C_exp + 8) / c_S' ≤ (m : ℝ) ^ (L / 4 - 2) := h1.trans h2
        rw [div_le_iff₀ hcS'_pos] at h3
        rw [Real.rpow_neg hm_pos.le, le_div_iff₀ (by positivity)]
        exact (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hm_pos _)).mpr (by linarith)
      have hm_sqrt : (m : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (m : ℝ) := by
        rw [Real.rpow_neg hm_pos.le, ← Real.sqrt_eq_rpow, one_div]
      calc (m : ℝ) * ((260 * C_exp + 8) * X ^ (-(1 / 4 : ℝ)))
          = (260 * C_exp + 8) * ((m : ℝ) * X ^ (-(1 / 4 : ℝ))) := by ring
        _ ≤ (260 * C_exp + 8) * ((m : ℝ) * (m : ℝ) ^ (-(L / 4))) := by gcongr
        _ ≤ (260 * C_exp + 8) * ((m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-(L / 4 - 2))) := by gcongr
        _ ≤ (260 * C_exp + 8) * ((1 / Real.sqrt (m : ℝ)) * (c_S' / (64 * (260 * C_exp + 8)))) := by
            rw [hm_sqrt]; gcongr
        _ = (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) := by field_simp [(by positivity : (0 : ℝ) < 260 * C_exp + 8).ne']
    have hsum_in : C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X)) +
        (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) ≤ (260 * C_exp + 8) * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      have hterm2' : X * Real.log ((m : ℝ) * X) ≤ 4 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
        have hX_half : X ^ (-(3 / 4 : ℝ)) ≤ (1 / 2 : ℝ) * X ^ (-(1 / 4 : ℝ)) := by
          have h1' : X ^ (1 / 2 : ℝ) ≥ 2 := Real.le_sqrt_of_sq_le (by linarith) |>.trans_eq (Real.sqrt_eq_rpow X)
          have h2' : X ^ (-(3 / 4 : ℝ)) = X ^ (-(1 / 2 : ℝ)) * X ^ (-(1 / 4 : ℝ)) := by
            rw [← Real.rpow_add hX0]; congr 1; norm_num
          rw [h2', Real.rpow_neg hX0.le]
          exact mul_le_mul_of_nonneg_right ((inv_le_comm₀ (Real.rpow_pos_of_pos hX0 _) (by norm_num)).mpr (by norm_num; exact h1')) (by positivity)
        have hpow_eq : X * X ^ (1 / 4 : ℝ) = X ^ (-(3 / 4 : ℝ)) * X ^ 2 := by
          conv_lhs => lhs; rw [← Real.rpow_one X]
          rw [← Real.rpow_two X, ← Real.rpow_add hX0, ← Real.rpow_add hX0]; congr 1; norm_num
        calc X * Real.log ((m : ℝ) * X) ≤ X * (8 * X ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith) hX0.le
          _ = 8 * (X ^ (-(3 / 4 : ℝ)) * X ^ 2) := by rw [← hpow_eq]; ring
          _ ≤ 8 * ((1 / 2 : ℝ) * X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by gcongr
          _ = 4 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by ring
      have h12 : X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X) ≤
          260 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by linarith
      have hmulC : C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X)) ≤
          C_exp * (260 * X ^ (-(1 / 4 : ℝ)) * X ^ 2) := mul_le_mul_of_nonneg_left h12 hCexp_pos.le
      linarith
    have hnn_in : 0 ≤ C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big +
        X * Real.log ((m : ℝ) * X)) + (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) := by
      have h1 : 0 ≤ Real.log ((m : ℝ) * X) := Real.log_nonneg hmX_ge1
      have h2 : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
      have h3 : 0 ≤ X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big := by positivity
      have h4 : 0 ≤ X * Real.log ((m : ℝ) * X) := mul_nonneg hX0.le h1
      have h5 : 0 ≤ (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) :=
        mul_nonneg (by positivity) h2
      exact add_nonneg (mul_nonneg hCexp_pos.le (add_nonneg h3 h4)) h5
    calc (m.totient : ℝ) * _
        ≤ (m : ℝ) * ((260 * C_exp + 8) * X ^ (-(1 / 4 : ℝ)) * X ^ 2) :=
          mul_le_mul htot_le_m hsum_in hnn_in hm_pos.le
      _ = (m : ℝ) * ((260 * C_exp + 8) * X ^ (-(1 / 4 : ℝ))) * X ^ 2 := by ring
      _ ≤ (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
  -- Helper: split a single character's zero sum at `T₀` and `1/2`
  have hsplit_box : ∀ χ : DirichletCharacter ℂ m,
      ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ =
      (∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
          (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) +
      (∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
          (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) +
      (∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
          (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := by
    intro χ
    have hdisj1 : Disjoint (lZerosInBox χ T₀) ((lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|)) := by
      rw [Finset.disjoint_left]
      intro ρ h1 h2; linarith [(mem_lZerosInBox.mp h1).2.2.2, (Finset.mem_filter.mp h2).2]
    have hu1 : lZerosInBox χ T₀ ∪ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|) = lZerosInBox χ T_big := by
      ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact lZerosInBox_mono χ hTbig_ge_T0 h
        · exact h
      · intro h
        have hm' := mem_lZerosInBox.mp h
        rcases le_or_gt |ρ.im| T₀ with hle | hgt
        · exact Or.inl (mem_lZerosInBox.mpr ⟨hm'.1, hm'.2.1, hm'.2.2.1, hle⟩)
        · exact Or.inr ⟨h, hgt⟩
    have hdisj2 : Disjoint ((lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re))
        ((lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
    have hu2 : (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re) ∪
        (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2) = lZerosInBox χ T₀ := by
      ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; rcases le_or_gt (1 / 2 : ℝ) ρ.re with hle | hgt
        · exact Or.inl ⟨h, hle⟩
        · exact Or.inr ⟨h, hgt⟩
    calc ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ
        = ∑ ρ ∈ lZerosInBox χ T₀ ∪ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
            (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ := by rw [hu1]
      _ = (∑ ρ ∈ lZerosInBox χ T₀, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) +
          (∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
            (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := Finset.sum_union hdisj1
      _ = ((∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
              (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) +
            (∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
              (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)) +
          (∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
            (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := by
        rw [← Finset.sum_union hdisj2, hu2]
  -- Extract the exact prime once we show `dyadic2Real (psi1AP m a) X > (X / 2) * √(2 X) * log (2 X)`!
  refine exists_prime_in_Ioc_of_dyadic2_psi1AP_gt m a (by linarith) ?_
  -- Split into Case 2 (Siegel zero exists with `1 - β₁ < δ₀ / L_M`) vs Case 1 (no such Siegel zero)!
  by_cases hSiegel : ∃ (χ₀ : DirichletCharacter ℂ m) (β₁ : ℝ),
      1 - δ₀ / L_M < β₁ ∧ β₁ < 1 ∧ DirichletCharacter.LFunction χ₀ (β₁ : ℂ) = 0
  · -- **CASE 2 (SIEGEL ZERO EXISTS)**: isolate `(χ₀, β₁)` and apply Deuring–Heilbronn + Log-Free Density!
    rcases hSiegel with ⟨χ₀, β₁, hβ₁_lo, hβ₁_hi, hLχ₀_0⟩
    have hβ₁_gt_half : 1 / 2 < β₁ := by
      have h1 : δ₀ / L_M ≤ 1 / 4 := (div_le_self hδ₀_pos.le hLM_gt1.le).trans hδ₀_qtr
      linarith
    have hβ₁_pos : 0 < β₁ := by linarith
    have hχ₀_ne1 : χ₀ ≠ 1 := by
      intro h1; subst h1
      have hβ₁_ne1 : (β₁ : ℂ) ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
      have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m)
        (s := (β₁ : ℂ)) (by simpa using hβ₁_pos) hβ₁_ne1).mp hLχ₀_0
      have hneg := Stage9LandauSiegel.riemannZeta_neg_on_Ioo hβ₁_pos hβ₁_hi
      have := congrArg Complex.re hζ0; simp at this; linarith [hneg.1]
    have hχ₀_sq : χ₀ ^ 2 = 1 := by
      by_contra hne2
      have hzf := Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree χ₀ hne2
        (s := (β₁ : ℂ)) ?_
      · exact hzf hLχ₀_0
      · have hlog_le : Real.log ((m : ℝ) * (|((β₁ : ℂ).im)| + 2)) ≤ L_M := by
          simp only [Complex.ofReal_im, abs_zero, zero_add]
          refine Real.log_le_log (by positivity) ?_
          dsimp only [M]
          exact mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ≤ T₀ + 2) hm_pos.le
        have h1 : δ₀ / L_M ≤ 1 / (14000 * Real.log ((m : ℝ) * (|((β₁ : ℂ).im)| + 2))) := by
          have hlog_pos : 0 < Real.log ((m : ℝ) * (|((β₁ : ℂ).im)| + 2)) := by
            simp only [Complex.ofReal_im, abs_zero, zero_add]
            exact Real.log_pos (by linarith : (1 : ℝ) < (m : ℝ) * 2)
          calc δ₀ / L_M ≤ (1 / 14000 : ℝ) / L_M := div_le_div_of_nonneg_right (hδ₀_60k.trans (by norm_num)) hLM_pos.le
            _ ≤ (1 / 14000 : ℝ) / Real.log ((m : ℝ) * (|((β₁ : ℂ).im)| + 2)) :=
                div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_le
            _ = 1 / (14000 * Real.log ((m : ℝ) * (|((β₁ : ℂ).im)| + 2))) := by ring
        simp only [Complex.ofReal_re]; linarith
    -- Underlying primitive character `ψ₁ = χ₀.primitiveCharacter`
    have : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
    set ψ₁ := χ₀.primitiveCharacter
    have hψ₁_prim : ψ₁.IsPrimitive := χ₀.primitiveCharacter_isPrimitive
    have hψ₁_ne1 : ψ₁ ≠ 1 := fun h1 => hχ₀_ne1 (by
      rw [← χ₀.changeLevel_primitiveCharacter]
      change DirichletCharacter.changeLevel _ ψ₁ = 1
      rw [h1, map_one])
    have hψ₁_sq : ψ₁ ^ 2 = 1 :=
      DirichletCharacter.changeLevel_injective χ₀.conductor_dvd_level
        (by rw [map_pow, map_one, χ₀.changeLevel_primitiveCharacter, hχ₀_sq])
    have hLψ₁_0 : DirichletCharacter.LFunction ψ₁ (β₁ : ℂ) = 0 :=
      (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ₀ (by simpa using hβ₁_pos) (.inl hχ₀_ne1)).mp hLχ₀_0
    have hq₁_le_m : (χ₀.conductor : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos m) χ₀.conductor_dvd_level
    have hq₁_pos : (0 : ℝ) < (χ₀.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ₀.conductor)
    -- Simplicity `lZeroMult χ₀ (β₁ : ℂ) = 1`!
    have hmult_β₁ : lZeroMult χ₀ (β₁ : ℂ) = 1 := by
      have hlog2q₁_le : Real.log (2 * (χ₀.conductor : ℝ)) ≤ L_M := by
        refine Real.log_le_log (by positivity) ?_
        dsimp only [M]
        rw [mul_comm (2 : ℝ)]
        exact mul_le_mul hq₁_le_m (by linarith : (2 : ℝ) ≤ T₀ + 2) (by norm_num) hm_pos.le
      have hlog2q₁_pos : 0 < Real.log (2 * (χ₀.conductor : ℝ)) :=
        Real.log_pos (by have := two_le_of_dirichletChar_ne_one hψ₁_ne1; exact_mod_cast (by omega : 1 < 2 * χ₀.conductor))
      have hβ_ge_simp : 1 - c_simp / Real.log (2 * (χ₀.conductor : ℝ)) ≤ β₁ := by
        have h1 : δ₀ / L_M ≤ c_simp / Real.log (2 * (χ₀.conductor : ℝ)) := by
          calc δ₀ / L_M ≤ (c_simp / 4) / L_M := div_le_div_of_nonneg_right hδ₀_simp hLM_pos.le
            _ ≤ c_simp / L_M := div_le_div_of_nonneg_right (by linarith) hLM_pos.le
            _ ≤ c_simp / Real.log (2 * (χ₀.conductor : ℝ)) := div_le_div_of_nonneg_left hcsimp_pos.le hlog2q₁_pos hlog2q₁_le
        linarith
      have hsimp1 := hsimp χ₀.conductor ψ₁ hψ₁_prim hψ₁_ne1 hψ₁_sq β₁ hβ_ge_simp hLψ₁_0
      have hord1 := lZeroMult_eq_primitive (χ := χ₀) (ρ := (β₁ : ℂ)) hχ₀_ne1 (by simpa using hβ₁_pos)
      dsimp only at hord1
      have hord_ψ₁ : lZeroMult ψ₁ (β₁ : ℂ) = analyticOrderNatAt (DirichletCharacter.completedLFunction ψ₁) (β₁ : ℂ) := by
        have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
        have hev : DirichletCharacter.completedLFunction ψ₁ =ᶠ[𝓝 (β₁ : ℂ)]
            fun z => DirichletCharacter.LFunction ψ₁ z * DirichletCharacter.gammaFactor ψ₁ z := by
          filter_upwards [hopen.mem_nhds (by simpa using hβ₁_pos)] with z hz
          exact completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos ψ₁ hz
        have hL_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ₁) (β₁ : ℂ) :=
          ((DirichletCharacter.differentiable_LFunction hψ₁_ne1).differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
        have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
        have hG_an : AnalyticAt ℂ (DirichletCharacter.gammaFactor ψ₁) (β₁ : ℂ) := by
          refine DifferentiableOn.analyticAt ?_ (hopen.mem_nhds (by simpa using hβ₁_pos))
          intro z hz; have hz_re : 0 < z.re := hz
          rcases ψ₁.even_or_odd with he | ho
          · have hfun : DirichletCharacter.gammaFactor ψ₁ =
                fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) * Complex.Gamma (w / 2) :=
              funext fun w => by rw [he.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
            rw [hfun]
            exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2))) z).mul
              ((Complex.differentiableAt_Gamma (z / 2) fun k hEq => by
                have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
                (differentiableAt_id.div_const 2))).differentiableWithinAt
          · have hfun : DirichletCharacter.gammaFactor ψ₁ =
                fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2)) * Complex.Gamma ((w + 1) / 2) :=
              funext fun w => by rw [ho.gammaFactor_def, Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero hpiC]
            rw [hfun]
            exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-(w + 1) / 2))) z).mul
              ((Complex.differentiableAt_Gamma ((z + 1) / 2) fun k hEq => by
                have hre := congrArg Complex.re hEq; simp at hre; linarith [Nat.cast_nonneg (α := ℝ) k, hz_re]).comp z
                ((differentiableAt_id.add (differentiableAt_const 1)).div_const 2))).differentiableWithinAt
        have heq := analyticOrderAt_congr hev
        unfold lZeroMult; simp only [analyticOrderNatAt, heq]
        exact (analyticOrderNatAt_mul_of_ne_zero hL_an hG_an (gammaFactor_ne_zero_of_re_pos ψ₁ (by simpa using hβ₁_pos))).symm
      rw [hord1, ← hord_ψ₁, hsimp1]
    -- Siegel lower bound on `1 - β₁`: `c_S / √m ≤ 1 - β₁`, so `c_S' / √m ≤ min 1 (R * δ)`!
    set δ : ℝ := (1 - β₁) * L_M
    have hδ_pos : 0 < δ := mul_pos (by linarith) hLM_pos
    have hδ_lt_δ₀ : δ < δ₀ := by
      dsimp only [δ]; exact (lt_div_iff₀ hLM_pos).mp (by linarith)
    set η : ℝ := min 1 (R * δ)
    have hη_ge : c_S' / Real.sqrt (m : ℝ) ≤ η := by
      have h1β_gt : c_S / (χ₀.conductor : ℝ) ^ (1 / 2 : ℝ) < 1 - β₁ := by
        by_contra hle; push Not at hle
        exact hsiegel_excl χ₀.conductor ψ₁ hψ₁_prim hψ₁_sq hψ₁_ne1 β₁ (by linarith) hLψ₁_0
      have hq_sqrt : Real.sqrt (χ₀.conductor : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hq₁_le_m
      have h1β_m : c_S' / Real.sqrt (m : ℝ) ≤ 1 - β₁ := by
        rw [← Real.sqrt_eq_rpow] at h1β_gt
        calc c_S' / Real.sqrt (m : ℝ) ≤ c_S / Real.sqrt (m : ℝ) :=
              div_le_div_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
          _ ≤ c_S / Real.sqrt (χ₀.conductor : ℝ) :=
              div_le_div_of_nonneg_left hcS_pos.le (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos χ₀.conductor))) hq_sqrt
          _ ≤ 1 - β₁ := h1β_gt.le
      have hRδ_eq : R * δ = (1 - β₁) * Real.log X := by
        dsimp only [R, δ]; field_simp [hLM_pos.ne']
      refine le_min ?_ ?_
      · calc c_S' / Real.sqrt (m : ℝ) ≤ 1 / Real.sqrt (m : ℝ) :=
              div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
          _ ≤ 1 := div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith)) (Real.sqrt_nonneg _)
      · rw [hRδ_eq]
        have h1 : 1 - β₁ ≤ (1 - β₁) * Real.log X := by
          have := mul_le_mul_of_nonneg_left hlogX_gt1.le (by linarith : 0 ≤ 1 - β₁)
          linarith
        exact h1β_m.trans h1
    have hη_pos : 0 < η := lt_of_lt_of_le (by positivity) hη_ge
    -- Deuring–Heilbronn gap for every other right-half zero `(χ, ρ) ≠ (χ₀, β₁)` with `|ρ.im| ≤ T₀`:
    set lam₀ : ℝ := (c₁ / 2) * Real.log (c₂ / (2 * δ))
    have h2δ_le : 2 * δ ≤ c₂ / 2 := by linarith
    have hratio_ge2 : 2 ≤ c₂ / (2 * δ) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hlam₀_pos : 0 < lam₀ := mul_pos (by positivity) (Real.log_pos (by linarith))
    let bad : DirichletCharacter ℂ m → ℂ → Prop := fun χ ρ => χ ≠ χ₀ ∨ ρ ≠ (β₁ : ℂ)
    have hgap_DH : ∀ (χ : DirichletCharacter ℂ m) (ρ : ℂ), ρ ∈ lZerosInBox χ T₀ → 1 / 2 ≤ ρ.re →
        bad χ ρ → lam₀ / L_M ≤ 1 - ρ.re := by
      intro χ ρ hρ _ hbad
      have hm' := mem_lZerosInBox.mp hρ
      have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      set ψ := χ.primitiveCharacter
      have hLψ0 : DirichletCharacter.LFunction ψ ρ = 0 := by
        by_cases hχ1 : χ = 1
        · subst hχ1
          have hρ_ne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hm'; exact lt_irrefl 1 hm'.2.1
          have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m) hm'.1 hρ_ne1).mp hm'.2.2.1
          have hcond1 : (1 : DirichletCharacter ℂ m).conductor = 1 := DirichletCharacter.conductor_one
          have hψ_eq1 : DirichletCharacter.LFunction ψ ρ = riemannZeta ρ := by
            have h1 := DirichletCharacter.LFunction_changeLevel
              (Nat.one_dvd (1 : DirichletCharacter ℂ m).conductor) (1 : DirichletCharacter ℂ 1)
              (.inr hρ_ne1) (s := ρ)
            have hprim1 : ψ = DirichletCharacter.changeLevel (Nat.one_dvd _) (1 : DirichletCharacter ℂ 1) := by
              ext a
              have : Subsingleton (ZMod (1 : DirichletCharacter ℂ m).conductor) := by rw [hcond1]; infer_instance
              have ha1 : a = 1 := Subsingleton.elim _ _
              rw [ha1, Units.val_one, map_one, map_one]
            rw [hprim1, h1, DirichletCharacter.LFunction_modOne_eq, hcond1]
            simp
          rw [hψ_eq1]; exact hζ0
        · exact (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ hm'.1 (.inl hχ1)).mp hm'.2.2.1
      have hne_pair : PChar.of ψ ≠ PChar.of ψ₁ ∨ ρ ≠ (β₁ : ℂ) := by
        rcases hbad with hχ_ne | hρ_ne
        · left
          intro heq
          apply hχ_ne
          apply eq_of_pchar_of_eq
          have h1 : PChar.of ψ = PChar.of χ := PChar.of_self (PChar.of χ)
          have h2 : PChar.of ψ₁ = PChar.of χ₀ := PChar.of_self (PChar.of χ₀)
          rw [← h1, ← h2]; exact heq
        · exact Or.inr hρ_ne
      set logQ : ℝ := Real.log ((χ.conductor : ℝ) * (χ₀.conductor : ℝ) * T₀)
      have hq_le_m : (χ.conductor : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos m) χ.conductor_dvd_level
      have hlogQ_pos : 0 < logQ := by
        have h1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by exact_mod_cast (NeZero.pos χ.conductor)
        have h2 : (1 : ℝ) ≤ (χ₀.conductor : ℝ) := by exact_mod_cast (NeZero.pos χ₀.conductor)
        have h12 : (1 : ℝ) ≤ (χ.conductor : ℝ) * (χ₀.conductor : ℝ) :=
          (by norm_num : (1 : ℝ) = 1 * 1) ▸ mul_le_mul h1 h2 zero_le_one (by linarith)
        have h12T : (4 : ℝ) ≤ (χ.conductor : ℝ) * (χ₀.conductor : ℝ) * T₀ :=
          (by norm_num : (4 : ℝ) = 1 * 4) ▸ mul_le_mul h12 hT₀_ge4 (by norm_num) (by linarith)
        exact Real.log_pos (by linarith)
      have hlogQ_le_2LM : logQ ≤ 2 * L_M := by
        have harg : (χ.conductor : ℝ) * (χ₀.conductor : ℝ) * T₀ ≤ M ^ 2 := by
          have hqq : (χ.conductor : ℝ) * (χ₀.conductor : ℝ) ≤ (m : ℝ) * (m : ℝ) :=
            mul_le_mul hq_le_m hq₁_le_m (Nat.cast_nonneg _) hm_pos.le
          have hT2 : T₀ ≤ (T₀ + 2) * (T₀ + 2) := by
            have h1 : T₀ ≤ T₀ + 2 := by linarith
            have h2 : (1 : ℝ) ≤ T₀ + 2 := by linarith
            exact h1.trans (by simpa using mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ T₀ + 2))
          calc (χ.conductor : ℝ) * (χ₀.conductor : ℝ) * T₀
              ≤ ((m : ℝ) * (m : ℝ)) * ((T₀ + 2) * (T₀ + 2)) :=
                mul_le_mul hqq hT2 (by linarith) (by positivity)
            _ = M ^ 2 := by dsimp only [M]; ring
        have hq_pos : (0 : ℝ) < (χ.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos χ.conductor)
        calc logQ ≤ Real.log (M ^ 2) := Real.log_le_log (by positivity) harg
          _ = 2 * L_M := by dsimp only [L_M]; rw [Real.log_pow]; norm_num
      have h1β_lt : 1 - β₁ < c₂ / logQ := by
        rw [lt_div_iff₀ hlogQ_pos]
        have h1 : (1 - β₁) * logQ ≤ (1 - β₁) * (2 * L_M) := mul_le_mul_of_nonneg_left hlogQ_le_2LM (by linarith)
        have h2 : (1 - β₁) * (2 * L_M) = 2 * δ := by dsimp only [δ]; ring
        linarith
      have hdh_app := hdh χ₀.conductor ψ₁ hψ₁_prim hψ₁_sq hψ₁_ne1 β₁ hβ₁_gt_half hβ₁_hi hLψ₁_0
        χ.conductor ψ χ.primitiveCharacter_isPrimitive ρ hm'.1 hm'.2.1 hLψ0 hne_pair T₀ (by linarith) hm'.2.2.2 h1β_lt
      have hlog_mono : Real.log (c₂ / (2 * δ)) ≤ Real.log (c₂ / ((1 - β₁) * logQ)) := by
        refine Real.log_le_log (by positivity) ?_
        refine div_le_div_of_nonneg_left hc₂_pos.le (by positivity) ?_
        have : (1 - β₁) * logQ ≤ (1 - β₁) * (2 * L_M) := mul_le_mul_of_nonneg_left hlogQ_le_2LM (by linarith)
        dsimp only [δ]; linarith
      have hdiv_mono : Real.log (c₂ / (2 * δ)) / (2 * L_M) ≤ Real.log (c₂ / ((1 - β₁) * logQ)) / logQ := by
        have hratio_ge1 : 1 ≤ c₂ / ((1 - β₁) * logQ) := by
          rw [one_le_div (mul_pos (by linarith) hlogQ_pos)]
          exact ((lt_div_iff₀ hlogQ_pos).mp h1β_lt).le
        calc Real.log (c₂ / (2 * δ)) / (2 * L_M)
            ≤ Real.log (c₂ / ((1 - β₁) * logQ)) / (2 * L_M) :=
              div_le_div_of_nonneg_right hlog_mono (by positivity)
          _ ≤ Real.log (c₂ / ((1 - β₁) * logQ)) / logQ :=
              div_le_div_of_nonneg_left (Real.log_nonneg hratio_ge1) hlogQ_pos hlogQ_le_2LM
      calc lam₀ / L_M = c₁ * (Real.log (c₂ / (2 * δ)) / (2 * L_M)) := by dsimp only [lam₀]; ring
        _ ≤ c₁ * (Real.log (c₂ / ((1 - β₁) * logQ)) / logQ) := mul_le_mul_of_nonneg_left hdiv_mono hc₁_pos.le
        _ = c₁ * Real.log (c₂ / ((1 - β₁) * logQ)) / logQ := by ring
        _ ≤ 1 - ρ.re := hdh_app
    -- Bound the right-half non-exceptional zeros via `sum_right_half_zeros_le_of_logfree`!
    have hRight_bd :
        (∑ χ : DirichletCharacter ℂ m,
          ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ),
            ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖) ≤
        (1 / 32 : ℝ) * η * X ^ 2 := by
      have hsum_le :
          (∑ χ : DirichletCharacter ℂ m,
            ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ),
              ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖) ≤
          ((1 / 4 : ℝ) * X ^ 2) *
            (∑ χ : DirichletCharacter ℂ m,
              ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ),
                (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have hm' := mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
        have hre : (ρ + 1).re = ρ.re + 1 := by simp
        rw [hre]
        have hX_split : X ^ (ρ.re + 1) = X ^ 2 * X ^ (ρ.re - 1) := by
          rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; ring
        have hK := norm_dyadicKernel_le_quarter (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
        rw [hX_split]
        calc (lZeroMult χ ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * ‖dyadicKernel ρ‖
            ≤ (lZeroMult χ ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * (1 / 4 : ℝ) :=
              mul_le_mul_of_nonneg_left hK (by positivity)
          _ = (1 / 4 : ℝ) * X ^ 2 * ((lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)) := by ring
      have hlf_bd := sum_right_half_zeros_le_of_logfree hCD_pos hA_ge1 hlf hm (by linarith) hX_ge4 hlam₀_pos.le
        bad hgap_DH (le_trans (max_le_max_left _ (by norm_num : (2 : ℝ) ≤ 12))
          (le_trans (le_max_left _ _) hR_ge_R0))
      -- Bound `(1 / 2) * C_D * exp A * exp (-(R / 2) * lam₀) ≤ (1 / 32) * η`!
      have hexp_val : Real.exp (-(R / 2) * lam₀) = (2 * δ / c₂) ^ (R * c₁ / 4) := by
        have h1 : -(R / 2) * lam₀ = (R * c₁ / 4) * Real.log (2 * δ / c₂) := by
          dsimp only [lam₀]
          rw [Real.log_div hc₂_pos.ne' (by positivity), Real.log_div (by positivity) hc₂_pos.ne']
          ring
        rw [h1, Real.rpow_def_of_pos (by positivity), mul_comm]
      have hE_ge2 : 2 ≤ R * c₁ / 4 := by
        have : 8 / c₁ ≤ R := hR0_8c1.trans hR_ge_R0
        have := (div_le_iff₀ hc₁_pos).mp this; linarith
      have hhalf_pow : (1 / 2 : ℝ) ^ (R * c₁ / 4 - 1) ≤ 1 / (2 * B_right) := by
        have hR_step : Real.log (2 * B_right) / Real.log 2 ≤ R * c₁ / 4 - 1 := by
          have h1 : R_c2 ≤ R := hR0_c2.trans hR_ge_R0
          dsimp only [R_c2] at h1
          have h2 : 1 + Real.log (2 * B_right) / Real.log 2 ≤ R * c₁ / 4 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hc₁_pos] at h1; linarith
          linarith
        rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), one_div]
        refine inv_anti₀ (by positivity) ?_
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hstep2 : Real.log (2 * B_right) ≤ Real.log 2 * (R * c₁ / 4 - 1) := by
          rw [mul_comm (Real.log 2)]; exact (div_le_iff₀ hlog2_pos).mp hR_step
        exact (Real.log_le_iff_le_exp (by positivity)).mp hstep2
      have hpow_le : (2 * δ / c₂) ^ (R * c₁ / 4) ≤ (1 / (2 * B_right)) * (2 * δ / c₂) := by
        have h1 : (2 * δ / c₂) ^ (R * c₁ / 4) = (2 * δ / c₂) ^ (R * c₁ / 4 - 1) * (2 * δ / c₂) := by
          conv_rhs => rhs; rw [← Real.rpow_one (2 * δ / c₂)]
          rw [← Real.rpow_add (by positivity)]; congr 1; ring
        have h2 : (2 * δ / c₂) ≤ 1 / 2 := by rw [div_le_iff₀ hc₂_pos]; linarith
        rw [h1]
        exact mul_le_mul_of_nonneg_right
          ((Real.rpow_le_rpow (by positivity) h2 (by linarith)).trans hhalf_pow) (by positivity)
      have hpow_le1 : (2 * δ / c₂) ^ (R * c₁ / 4) ≤ 1 / (2 * B_right) := by
        have h2 : 2 * δ / c₂ ≤ 1 := by rw [div_le_iff₀ hc₂_pos]; linarith
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1 / (2 * B_right))
        rw [mul_one] at h3
        exact hpow_le.trans h3
      have hcomb : (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * lam₀) ≤ (1 / 32 : ℝ) * η := by
        rw [hexp_val]
        rcases le_total (R * δ) 1 with hle1 | hge1
        · have hη_eq : η = R * δ := min_eq_right hle1
          have hδ_le_η : δ ≤ η := by
            rw [hη_eq]
            have hR1 : (1 : ℝ) ≤ R := by linarith
            simpa using mul_le_mul_of_nonneg_right hR1 hδ_pos.le
          have h1 : (1 / 2 : ℝ) * C_D * Real.exp A * ((1 / (2 * B_right)) * (2 * δ / c₂)) ≤ (1 / 32 : ℝ) * δ := by
            have hB_ge : 32 * C_D * Real.exp A * (2 / c₂) ≤ B_right := by
              have h1' : 32 * C_D * Real.exp A * (2 / c₂) ≤ 32 * C_D * Real.exp A * (1 + 2 / c₂) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              exact h1'.trans hBright_ge_expr
            have hrew : (1 / 2 : ℝ) * C_D * Real.exp A * ((1 / (2 * B_right)) * (2 * δ / c₂)) =
                ((1 / 2 : ℝ) * C_D * Real.exp A * (2 / c₂) / (2 * B_right)) * δ := by ring
            rw [hrew]
            refine mul_le_mul_of_nonneg_right ?_ hδ_pos.le
            rw [div_le_iff₀ (by positivity)]; linarith
          calc (1 / 2 : ℝ) * C_D * Real.exp A * (2 * δ / c₂) ^ (R * c₁ / 4)
              ≤ (1 / 2 : ℝ) * C_D * Real.exp A * ((1 / (2 * B_right)) * (2 * δ / c₂)) :=
                mul_le_mul_of_nonneg_left hpow_le (by positivity)
            _ ≤ (1 / 32 : ℝ) * δ := h1
            _ ≤ (1 / 32 : ℝ) * η := by linarith
        · have hη_eq : η = 1 := min_eq_left hge1
          rw [hη_eq, mul_one]
          have hB_ge : 32 * C_D * Real.exp A ≤ B_right := by
            have h1' : 32 * C_D * Real.exp A * 1 ≤ 32 * C_D * Real.exp A * (1 + 2 / c₂) :=
              mul_le_mul_of_nonneg_left (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hc₂_pos]) (by positivity)
            rw [mul_one] at h1'
            exact h1'.trans hBright_ge_expr
          calc (1 / 2 : ℝ) * C_D * Real.exp A * (2 * δ / c₂) ^ (R * c₁ / 4)
              ≤ (1 / 2 : ℝ) * C_D * Real.exp A * (1 / (2 * B_right)) :=
                mul_le_mul_of_nonneg_left hpow_le1 (by positivity)
            _ ≤ 1 / 32 := by
                rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
      calc ∑ χ : DirichletCharacter ℂ m, _
          ≤ ((1 / 4 : ℝ) * X ^ 2) * (2 * C_D * Real.exp A * Real.exp (-(R / 2) * lam₀)) :=
            hsum_le.trans (mul_le_mul_of_nonneg_left hlf_bd (by positivity))
        _ = ((1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * lam₀)) * X ^ 2 := by ring
        _ ≤ (1 / 32 : ℝ) * η * X ^ 2 := mul_le_mul_of_nonneg_right hcomb (by positivity)
    -- Siegel main term lower bound: `(1 / 4) X^2 - ‖χ₀(a)⁻¹ * X^(β₁ + 1) * dyadicKernel β₁‖ ≥ (1 / 8) * η * X^2`!
    have hSiegel_main :
        (1 / 8 : ℝ) * η * X ^ 2 ≤
          (1 / 4 : ℝ) * X ^ 2 -
            ‖starRingEnd ℂ (χ₀ (a : ZMod m)) *
              ((lZeroMult χ₀ (β₁ : ℂ) : ℂ) * (X : ℂ) ^ ((β₁ : ℂ) + 1) * dyadicKernel (β₁ : ℂ))‖ := by
      rw [hmult_β₁, Nat.cast_one, one_mul, norm_mul, norm_mul, Complex.norm_conj,
        Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : ((β₁ : ℂ) + 1).re = β₁ + 1 := by simp
      rw [hre]
      have hχ1 : ‖χ₀ (a : ZMod m)‖ ≤ 1 := χ₀.norm_le_one _
      have hK := norm_dyadicKernel_le_quarter (s := (β₁ : ℂ)) (by simp; linarith) (by simp; linarith)
      have hX_split : X ^ (β₁ + 1) = X ^ 2 * Real.exp (-(R * δ)) := by
        rw [Real.rpow_def_of_pos hX0, ← Real.rpow_two X, Real.rpow_def_of_pos hX0, ← Real.exp_add]
        congr 1; have hRδ : R * δ = (1 - β₁) * Real.log X := by dsimp only [R, δ]; field_simp [hLM_pos.ne']
        rw [hRδ]; ring
      have hterm_le : ‖χ₀ (a : ZMod m)‖ * (X ^ (β₁ + 1) * ‖dyadicKernel (β₁ : ℂ)‖) ≤
          (1 / 4 : ℝ) * X ^ 2 * Real.exp (-(R * δ)) := by
        rw [hX_split]
        calc ‖χ₀ (a : ZMod m)‖ * (X ^ 2 * Real.exp (-(R * δ)) * ‖dyadicKernel (β₁ : ℂ)‖)
            ≤ 1 * (X ^ 2 * Real.exp (-(R * δ)) * (1 / 4 : ℝ)) :=
              mul_le_mul hχ1 (mul_le_mul_of_nonneg_left hK (by positivity)) (by positivity) zero_le_one
          _ = (1 / 4 : ℝ) * X ^ 2 * Real.exp (-(R * δ)) := by ring
      have hmin := half_min_one_le_one_sub_exp_neg (u := R * δ) (by positivity)
      have hmul_min := mul_le_mul_of_nonneg_right hmin (by positivity : 0 ≤ (1 / 4 : ℝ) * X ^ 2)
      dsimp only [η]
      linarith
    -- Assemble all pieces in Case 2!
    have hβ₁_mem : (β₁ : ℂ) ∈ (lZerosInBox χ₀ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re) :=
      Finset.mem_filter.mpr ⟨mem_lZerosInBox.mpr ⟨by simp [hβ₁_pos], by simp [hβ₁_hi], hLχ₀_0,
        by simp; linarith⟩, by simp; linarith⟩
    have hsum_split_tot :
        ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ =
        starRingEnd ℂ (χ₀ (a : ZMod m)) *
          ((lZeroMult χ₀ (β₁ : ℂ) : ℂ) * (X : ℂ) ^ ((β₁ : ℂ) + 1) * dyadicKernel (β₁ : ℂ)) +
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ),
            (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) +
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2),
            (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) +
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|),
            (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ) := by
      simp_rw [hsplit_box, mul_add, Finset.sum_add_distrib]
      congr 1; congr 1
      have hpeel : ∀ χ : DirichletCharacter ℂ m,
          starRingEnd ℂ (χ (a : ZMod m)) *
            ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
              (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ =
          (if χ = χ₀ then starRingEnd ℂ (χ₀ (a : ZMod m)) *
              ((lZeroMult χ₀ (β₁ : ℂ) : ℂ) * (X : ℂ) ^ ((β₁ : ℂ) + 1) * dyadicKernel (β₁ : ℂ))
           else 0) +
          starRingEnd ℂ (χ (a : ZMod m)) *
            ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ),
              (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ := by
        intro χ
        by_cases hEq : χ = χ₀
        · subst hEq; rw [if_pos rfl]
          have hfilt : (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ) =
              ((lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re)).erase (β₁ : ℂ) := by
            ext ρ; simp only [Finset.mem_filter, Finset.mem_erase, bad, ne_eq, not_true_eq_false, false_or]
            tauto
          rw [hfilt, ← Finset.add_sum_erase _ _ hβ₁_mem, mul_add]
        · rw [if_neg hEq, zero_add]
          congr 2; ext ρ
          simp only [Finset.mem_filter, bad]
          exact ⟨fun h => ⟨h.1, h.2, Or.inl hEq⟩, fun h => ⟨h.1, h.2.1⟩⟩
      simp_rw [hpeel, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_ite_eq' Finset.univ χ₀, if_pos (Finset.mem_univ _)]
    -- Take real parts in `hef` and multiply by `φ(m)`!
    have hre_ef : (m.totient : ℝ) * dyadic2Real (psi1AP m a) X ≥
        (1 / 4 : ℝ) * X ^ 2 -
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ).re -
        (m.totient : ℝ) * (C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big +
          X * Real.log ((m : ℝ) * X))) := by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hef)).1
      rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re] at h1
      have hinv_re : ((m.totient : ℂ)⁻¹).re = (m.totient : ℝ)⁻¹ := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
      have hinv_im : ((m.totient : ℂ)⁻¹).im = 0 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
      rw [hinv_re, hinv_im, zero_mul, sub_zero, Complex.sub_re] at h1
      have hq_re : ((1 / 4 : ℂ) * (X : ℂ) ^ 2).re = (1 / 4 : ℝ) * X ^ 2 := by
        rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
          Complex.ofReal_re]
      rw [hq_re] at h1
      have hmul := mul_le_mul_of_nonneg_left h1 htot_pos.le
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ htot_pos.ne', one_mul] at hmul
      linarith
    have hZ_re_le :
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ).re ≤
        ‖starRingEnd ℂ (χ₀ (a : ZMod m)) *
          ((lZeroMult χ₀ (β₁ : ℂ) : ℂ) * (X : ℂ) ^ ((β₁ : ℂ) + 1) * dyadicKernel (β₁ : ℂ))‖ +
        (1 / 32 : ℝ) * η * X ^ 2 + (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 +
          (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 := by
      rw [hsum_split_tot, Complex.add_re, Complex.add_re, Complex.add_re]
      have hnorm_sum_χ : ∀ (F_χ : DirichletCharacter ℂ m → Finset ℂ),
          (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
            ∑ ρ ∈ F_χ χ, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ).re ≤
          ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ F_χ χ,
            ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ := fun F_χ => by
        refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_))
        rw [norm_mul, Complex.norm_conj]
        calc ‖χ (a : ZMod m)‖ * ‖∑ ρ ∈ F_χ χ, _‖
            ≤ 1 * ∑ ρ ∈ F_χ χ, ‖_‖ := mul_le_mul (χ.norm_le_one _) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
          _ = ∑ ρ ∈ F_χ χ, ‖_‖ := one_mul _
      have h0 := Complex.re_le_norm (starRingEnd ℂ (χ₀ (a : ZMod m)) *
          ((lZeroMult χ₀ (β₁ : ℂ) : ℂ) * (X : ℂ) ^ ((β₁ : ℂ) + 1) * dyadicKernel (β₁ : ℂ)))
      have h1 := (hnorm_sum_χ fun χ => (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad χ ρ)).trans hRight_bd
      have h2 := (hnorm_sum_χ fun χ => (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2)).trans hLeft_bd
      have h3 := (hnorm_sum_χ fun χ => (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|)).trans hTail_bd
      linarith
    have hη_cs : (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 ≤ η * X ^ 2 :=
      mul_le_mul_of_nonneg_right hη_ge (by positivity)
    have hstrict : (m.totient : ℝ) * ((X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)) <
        (m.totient : ℝ) * dyadic2Real (psi1AP m a) X := by
      have hpos_gap : 0 < (1 / 32 : ℝ) * η * X ^ 2 := by positivity
      linarith
    exact lt_of_mul_lt_mul_left hstrict htot_pos.le
  · -- **CASE 1 (NO SIEGEL ZERO)**: every zero `(χ, ρ)` in `|ρ.im| ≤ T₀` satisfies `1 - ρ.re ≥ δ₀ / L_M`!
    push Not at hSiegel
    have hgap_c1 : ∀ (χ : DirichletCharacter ℂ m) (ρ : ℂ), ρ ∈ lZerosInBox χ T₀ → 1 / 2 ≤ ρ.re →
        True → δ₀ / L_M ≤ 1 - ρ.re := by
      intro χ ρ hρ _ _
      have hm' := mem_lZerosInBox.mp hρ
      have hlog_le : Real.log ((m : ℝ) * (|ρ.im| + 2)) ≤ L_M :=
        Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith [hm'.2.2.2]) hm_pos.le)
      have hlog_pos : 0 < Real.log ((m : ℝ) * (|ρ.im| + 2)) := by
        have h1 : (2 : ℝ) ≤ |ρ.im| + 2 := by linarith [abs_nonneg ρ.im]
        have h2 : (4 : ℝ) ≤ (m : ℝ) * (|ρ.im| + 2) :=
          (by norm_num : (4 : ℝ) = 2 * 2) ▸ mul_le_mul hmR h1 (by norm_num) hm_pos.le
        exact Real.log_pos (by linarith)
      by_cases hχ1 : χ = 1
      · subst hχ1
        have hρ_ne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hm'; exact lt_irrefl 1 hm'.2.1
        have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m) hm'.1 hρ_ne1).mp hm'.2.2.1
        have hlogρ_le : Real.log (|ρ.im| + 2) ≤ L_M := by
          refine Real.log_le_log (by linarith [abs_nonneg ρ.im]) ?_
          dsimp only [M]
          have h1 : |ρ.im| + 2 ≤ T₀ + 2 := by linarith [hm'.2.2.2]
          have h2 : T₀ + 2 ≤ (m : ℝ) * (T₀ + 2) := by
            have : (1 : ℝ) * (T₀ + 2) ≤ (m : ℝ) * (T₀ + 2) :=
              mul_le_mul_of_nonneg_right (by linarith) (by linarith)
            linarith
          exact h1.trans h2
        have hlogρ_pos : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
        have hlt : ρ.re < 1 - c_ζ / Real.log (|ρ.im| + 2) := by
          by_contra hge; push Not at hge
          exact hzf_ζ ρ hge hρ_ne1 hζ0
        have hdiv : δ₀ / L_M ≤ c_ζ / Real.log (|ρ.im| + 2) :=
          (div_le_div_of_nonneg_right hδ₀_ζ hLM_pos.le).trans
            (div_le_div_of_nonneg_left hcζ_pos.le hlogρ_pos hlogρ_le)
        linarith
      · by_cases hχ2 : χ ^ 2 ≠ 1
        · have hlt : ρ.re < 1 - 1 / (14000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
            by_contra hge; push Not at hge
            exact Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree χ hχ2 hge hm'.2.2.1
          have hdiv : δ₀ / L_M ≤ 1 / (14000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
            calc δ₀ / L_M ≤ (1 / 14000 : ℝ) / L_M :=
                  div_le_div_of_nonneg_right (hδ₀_60k.trans (by norm_num)) hLM_pos.le
              _ ≤ (1 / 14000 : ℝ) / Real.log ((m : ℝ) * (|ρ.im| + 2)) :=
                  div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_le
              _ = 1 / (14000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by ring
          linarith
        · push Not at hχ2
          by_cases him : ρ.im ≠ 0
          · have hlt : ρ.re < 1 - 1 / (60000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
              by_contra hge; push Not at hge
              exact Stage8UniformAP.LFunction_real_char_nonreal_zeroFree hχ1 hχ2 him hge hm'.2.2.1
            have hdiv : δ₀ / L_M ≤ 1 / (60000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
              calc δ₀ / L_M ≤ (1 / 60000 : ℝ) / L_M :=
                    div_le_div_of_nonneg_right hδ₀_60k hLM_pos.le
                _ ≤ (1 / 60000 : ℝ) / Real.log ((m : ℝ) * (|ρ.im| + 2)) :=
                    div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_le
                _ = 1 / (60000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by ring
            linarith
          · push Not at him
            have hρ_eq : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
            by_contra hlt; push Not at hlt
            exact hSiegel χ ρ.re (by linarith) hm'.2.1 (hρ_eq ▸ hm'.2.2.1)
    have hRight_bd :
        (∑ χ : DirichletCharacter ℂ m,
          ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
            ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖) ≤
        (1 / 32 : ℝ) * X ^ 2 := by
      have hfilt_eq : ∀ χ : DirichletCharacter ℂ m,
          (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re) =
            (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ True) := fun _ => by simp
      have hsum_le :
          (∑ χ : DirichletCharacter ℂ m,
            ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ True),
              ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖) ≤
          ((1 / 4 : ℝ) * X ^ 2) *
            (∑ χ : DirichletCharacter ℂ m,
              ∑ ρ ∈ (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ True),
                (lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun χ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun ρ hρ => ?_
        have hm' := mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
        have hre : (ρ + 1).re = ρ.re + 1 := by simp
        rw [hre]
        have hX_split : X ^ (ρ.re + 1) = X ^ 2 * X ^ (ρ.re - 1) := by
          rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; ring
        have hK := norm_dyadicKernel_le_quarter (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
        rw [hX_split]
        calc (lZeroMult χ ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * ‖dyadicKernel ρ‖
            ≤ (lZeroMult χ ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * (1 / 4 : ℝ) :=
              mul_le_mul_of_nonneg_left hK (by positivity)
          _ = (1 / 4 : ℝ) * X ^ 2 * ((lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)) := by ring
      have hlf_bd := sum_right_half_zeros_le_of_logfree hCD_pos hA_ge1 hlf hm (by linarith) hX_ge4 hδ₀_pos.le
        (fun _ _ => True) hgap_c1 (le_trans (max_le_max_left _ (by norm_num : (2 : ℝ) ≤ 12))
          (le_trans (le_max_left _ _) hR_ge_R0))
      have hexp_le : Real.exp (-(R / 2) * δ₀) ≤ 1 / (2 * B_right) := by
        have h1 : Real.log (2 * B_right) ≤ (R / 2) * δ₀ := by
          have hR1 : R_c1 ≤ R := hR0_c1.trans hR_ge_R0
          dsimp only [R_c1] at hR1
          have := mul_le_mul_of_nonneg_right hR1 hδ₀_pos.le
          field_simp [hδ₀_pos.ne'] at this; linarith
        rw [show -(R / 2) * δ₀ = -((R / 2) * δ₀) by ring, Real.exp_neg, one_div]
        exact inv_anti₀ (by positivity) ((Real.log_le_iff_le_exp (by positivity)).mp h1)
      have hB_ge : 32 * C_D * Real.exp A ≤ B_right := by
        have h1' : 32 * C_D * Real.exp A * 1 ≤ 32 * C_D * Real.exp A * (1 + 2 / c₂) :=
          mul_le_mul_of_nonneg_left (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hc₂_pos]) (by positivity)
        rw [mul_one] at h1'
        exact h1'.trans hBright_ge_expr
      have hcomb : (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * δ₀) ≤ 1 / 32 := by
        calc (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * δ₀)
            ≤ (1 / 2 : ℝ) * C_D * Real.exp A * (1 / (2 * B_right)) :=
              mul_le_mul_of_nonneg_left hexp_le (by positivity)
          _ ≤ 1 / 32 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
      simp_rw [hfilt_eq]
      calc ∑ χ : DirichletCharacter ℂ m, _
          ≤ ((1 / 4 : ℝ) * X ^ 2) * (2 * C_D * Real.exp A * Real.exp (-(R / 2) * δ₀)) :=
            hsum_le.trans (mul_le_mul_of_nonneg_left hlf_bd (by positivity))
        _ = ((1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * δ₀)) * X ^ 2 := by ring
        _ ≤ (1 / 32 : ℝ) * X ^ 2 := mul_le_mul_of_nonneg_right hcomb (by positivity)
    have hcs_le1 : c_S' / Real.sqrt (m : ℝ) ≤ 1 := by
      calc c_S' / Real.sqrt (m : ℝ) ≤ 1 / Real.sqrt (m : ℝ) :=
            div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
        _ ≤ 1 := div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith)) (Real.sqrt_nonneg _)
    have hre_ef : (m.totient : ℝ) * dyadic2Real (psi1AP m a) X ≥
        (1 / 4 : ℝ) * X ^ 2 -
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ).re -
        (m.totient : ℝ) * (C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big +
          X * Real.log ((m : ℝ) * X))) := by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hef)).1
      rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re] at h1
      have hinv_re : ((m.totient : ℂ)⁻¹).re = (m.totient : ℝ)⁻¹ := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
      have hinv_im : ((m.totient : ℂ)⁻¹).im = 0 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
      rw [hinv_re, hinv_im, zero_mul, sub_zero, Complex.sub_re] at h1
      have hq_re : ((1 / 4 : ℂ) * (X : ℂ) ^ 2).re = (1 / 4 : ℝ) * X ^ 2 := by
        rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
          Complex.ofReal_re]
      rw [hq_re] at h1
      have hmul := mul_le_mul_of_nonneg_left h1 htot_pos.le
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ htot_pos.ne', one_mul] at hmul
      linarith
    have hZ_re_le :
        (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T_big, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ).re ≤
        (1 / 32 : ℝ) * X ^ 2 + (1 / 64 : ℝ) * X ^ 2 + (1 / 64 : ℝ) * X ^ 2 := by
      have hnorm_sum_χ : ∀ (F_χ : DirichletCharacter ℂ m → Finset ℂ),
          (∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
            ∑ ρ ∈ F_χ χ, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ).re ≤
          ∑ χ : DirichletCharacter ℂ m, ∑ ρ ∈ F_χ χ,
            ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ := fun F_χ => by
        refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_))
        rw [norm_mul, Complex.norm_conj]
        calc ‖χ (a : ZMod m)‖ * ‖∑ ρ ∈ F_χ χ, _‖
            ≤ 1 * ∑ ρ ∈ F_χ χ, ‖_‖ := mul_le_mul (χ.norm_le_one _) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
          _ = ∑ ρ ∈ F_χ χ, ‖_‖ := one_mul _
      simp_rw [hsplit_box, mul_add, Finset.sum_add_distrib, Complex.add_re]
      have hcs_X2 : (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 ≤ (1 / 64 : ℝ) * X ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hcs_le1 (by positivity : 0 ≤ (1 / 64 : ℝ) * X ^ 2)
        linarith
      have h1 := (hnorm_sum_χ fun χ => (lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re)).trans hRight_bd
      have h2 := (hnorm_sum_χ fun χ => (lZerosInBox χ T₀).filter (fun ρ => ρ.re < 1 / 2)).trans
        (hLeft_bd.trans hcs_X2)
      have h3 := (hnorm_sum_χ fun χ => (lZerosInBox χ T_big).filter (fun ρ => T₀ < |ρ.im|)).trans
        (hTail_bd.trans hcs_X2)
      linarith
    have hstrict : (m.totient : ℝ) * ((X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)) <
        (m.totient : ℝ) * dyadic2Real (psi1AP m a) X := by
      have hpos_gap : 0 < (1 / 8 : ℝ) * X ^ 2 := by positivity
      have hcs_X2 : (1 / 64 : ℝ) * (c_S' / Real.sqrt (m : ℝ)) * X ^ 2 ≤ (1 / 64 : ℝ) * X ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hcs_le1 (by positivity : 0 ≤ (1 / 64 : ℝ) * X ^ 2)
        linarith
      have hErr_le : (m.totient : ℝ) *
          (C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X)) +
            (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)) ≤ (1 / 64 : ℝ) * X ^ 2 :=
        hErr_pp_bd.trans hcs_X2
      linarith
    exact lt_of_mul_lt_mul_left hstrict htot_pos.le

/-- **Direct Corollary**: `(Deuring–Heilbronn + Log-Free Density) → Stage2PrimePairs.LinnikAPInterval`. -/
theorem linnikAPInterval_of_dh_and_logfree
    (hDH : DeuringHeilbronnHypothesis) (hLF : LogFreeZeroDensityHypothesis) :
    Stage2PrimePairs.LinnikAPInterval :=
  Stage2PrimePairs.linnikAPInterval_of_dyadic (linnikAPDyadic_of_dh_and_logfree hDH hLF)

/-- **Direct Corollary**: `(Deuring–Heilbronn + Log-Free Density) → HostFieldSupply.PairSupply`. -/
theorem pairSupply_of_dh_and_logfree
    (hDH : DeuringHeilbronnHypothesis) (hLF : LogFreeZeroDensityHypothesis) :
    HostFieldSupply.PairSupply :=
  Stage2PrimePairs.pairSupply_of_linnikAPInterval (linnikAPInterval_of_dh_and_logfree hDH hLF)

/-- **Direct Corollary**: `(Deuring–Heilbronn + Log-Free Density) → ThetaSlopeEngine.PairEx`. -/
theorem pairEx_of_dh_and_logfree
    (hDH : DeuringHeilbronnHypothesis) (hLF : LogFreeZeroDensityHypothesis) :
    ThetaSlopeEngine.PairEx :=
  Stage2PrimePairs.pairEx_of_linnikAPInterval (linnikAPInterval_of_dh_and_logfree hDH hLF)

/-- **Direct Corollary**: `(Deuring–Heilbronn + Log-Free Density) → HostFieldSupply.SmallOne`. -/
theorem smallOne_of_dh_and_logfree
    (hDH : DeuringHeilbronnHypothesis) (hLF : LogFreeZeroDensityHypothesis) :
    HostFieldSupply.SmallOne :=
  Stage2PrimePairs.smallOne_of_linnikAPInterval (linnikAPInterval_of_dh_and_logfree hDH hLF)

/-! ## Section 5: Sharp `GRH`-Conditional Linnik Constant (`L = 2 + ε` & `L = 3`) -/

/-- **SHARP `GRH` ASYMPTOTIC FOR `dyadic2Real (psi1AP m a) X`**:
under `DirichletLZerosOnLine`, there exists `C > 0` such that for all `m ≥ 2`, `Nat.Coprime a m`,
and `X ≥ 4`:
`|dyadic2Real (psi1AP m a) X - (1 / 4) * X ^ 2 / φ(m)| ≤ C * X ^ (3 / 2) * Real.log (m * X)`. -/
theorem smoothed_ap_dyadic_of_GRH (hGRH : DirichletLZerosOnLine) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a : ℕ) [NeZero m], 2 ≤ m → Nat.Coprime a m →
      ∀ X : ℝ, 4 ≤ X →
        |dyadic2Real (psi1AP m a) X - (1 / 4 : ℝ) * X ^ 2 / (m.totient : ℝ)| ≤
          C * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
  classical
  obtain ⟨C_exp, hCexp_pos, hexp⟩ := smoothed_ap_dyadic_explicit_formula
  obtain ⟨C_sum, hCsum_pos, hsum⟩ := sum_inv_one_add_im_sq_lZeros_le
  set C : ℝ := 20 * C_sum + 20 * C_exp
  refine ⟨C, by positivity, fun m a _ hm hcop X hX => ?_⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hX0 : 0 < X := by linarith
  set T : ℝ := (m : ℝ) * X ^ 2
  have hT_ge4 : 4 ≤ T := by dsimp only [T]; nlinarith
  have hef := hexp m a hm hcop X T hX hT_ge4
  have htot_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have hcard_char : (Fintype.card (DirichletCharacter ℂ m) : ℝ) = (m.totient : ℝ) :=
    card_dirichletChar_eq_totient_local m
  -- Under GRH, every `ρ ∈ lZerosInBox χ T` has `ρ.re = 1 / 2`!
  have hzero_norm :
      ‖(m.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
      20 * C_sum * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hlogm_le : Real.log (m : ℝ) ≤ Real.log ((m : ℝ) * X) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hper_χ : ∀ χ : DirichletCharacter ℂ m,
        ‖starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ ≤
        20 * C_sum * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := fun χ => by
      rw [norm_mul, Complex.norm_conj]
      calc ‖χ (a : ZMod m)‖ * ‖∑ ρ ∈ lZerosInBox χ T, _‖
          ≤ 1 * ∑ ρ ∈ lZerosInBox χ T, ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ :=
            mul_le_mul (χ.norm_le_one _) (norm_sum_le _ _) (norm_nonneg _) zero_le_one
        _ = ∑ ρ ∈ lZerosInBox χ T, ‖(lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ := one_mul _
        _ ≤ ∑ ρ ∈ lZerosInBox χ T, (20 * X ^ (3 / 2 : ℝ)) * ((lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            have hm' := mem_lZerosInBox.mp hρ
            have hre_half : ρ.re = 1 / 2 := hGRH m χ ρ hm'.1 hm'.2.1 hm'.2.2.1
            rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
            have hre : (ρ + 1).re = 3 / 2 := by simp [hre_half]; norm_num
            rw [hre]
            have hK := norm_dyadicKernel_le_inv_sq (s := ρ) (by linarith) (by linarith)
            calc (lZeroMult χ ρ : ℝ) * X ^ (3 / 2 : ℝ) * ‖dyadicKernel ρ‖
                ≤ (lZeroMult χ ρ : ℝ) * X ^ (3 / 2 : ℝ) * (20 / (1 + ρ.im ^ 2)) :=
                  mul_le_mul_of_nonneg_left hK (by positivity)
              _ = (20 * X ^ (3 / 2 : ℝ)) * ((lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2)) := by ring
        _ = (20 * X ^ (3 / 2 : ℝ)) * ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (20 * X ^ (3 / 2 : ℝ)) * (C_sum * Real.log (m : ℝ)) :=
            mul_le_mul_of_nonneg_left (hsum m hm χ T (by linarith)) (by positivity)
        _ ≤ (20 * X ^ (3 / 2 : ℝ)) * (C_sum * Real.log ((m : ℝ) * X)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogm_le hCsum_pos.le) (by positivity)
        _ = 20 * C_sum * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by ring
    calc (m.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ m, _‖
        ≤ (m.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ m,
            ‖starRingEnd ℂ (χ (a : ZMod m)) *
              ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (m.totient : ℝ)⁻¹ * ∑ _χ : DirichletCharacter ℂ m, 20 * C_sum * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => hper_χ χ) (by positivity)
      _ = (m.totient : ℝ)⁻¹ * ((m.totient : ℝ) * (20 * C_sum * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_char]
      _ = 20 * C_sum * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := inv_mul_cancel_left₀ htot_pos.ne' _
  -- Bound explicit-formula error at `T = m * X ^ 2` by `20 * C_exp * X ^ (3 / 2) * Real.log (m * X)`!
  have herr_le :
      C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T + X * Real.log ((m : ℝ) * X)) ≤
      20 * C_exp * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
    have hlogm_le : Real.log (m : ℝ) ≤ (m : ℝ) := by linarith [Real.log_le_sub_one_of_pos hm_pos]
    have hlogX_le : Real.log X ≤ X := by linarith [Real.log_le_sub_one_of_pos hX0]
    have hlogT_le : Real.log T ≤ 2 * Real.log ((m : ℝ) * X) := by
      have harg : T ≤ ((m : ℝ) * X) ^ 2 := by dsimp only [T]; nlinarith
      calc Real.log T ≤ Real.log (((m : ℝ) * X) ^ 2) := Real.log_le_log (by positivity) harg
        _ = 2 * Real.log ((m : ℝ) * X) := by rw [Real.log_pow]; norm_num
    have hlog_sum : Real.log ((m : ℝ) * X) + Real.log T ≤ 3 * Real.log ((m : ℝ) * X) := by linarith
    have hlog_nn : 0 ≤ Real.log ((m : ℝ) * X) := Real.log_nonneg (by nlinarith)
    have hlog_div_m : Real.log ((m : ℝ) * X) / (m : ℝ) ≤ X := by
      rw [div_le_iff₀ hm_pos, Real.log_mul hm_pos.ne' hX0.ne']
      nlinarith
    have hX_le_X32 : X ≤ X ^ (3 / 2 : ℝ) := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ ≤ X ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hterm1 : X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T ≤
        9 * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
      have hsq : (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 ≤ 9 * (Real.log ((m : ℝ) * X)) ^ 2 := by
        have h := pow_le_pow_left₀ (by linarith [Real.log_nonneg (by linarith : 1 ≤ T)]) hlog_sum 2
        linarith
      have hcancel : X ^ 2 * (9 * (Real.log ((m : ℝ) * X)) ^ 2) / T =
          9 * (Real.log ((m : ℝ) * X) / (m : ℝ)) * Real.log ((m : ℝ) * X) := by
        dsimp only [T]; field_simp [hm_pos.ne', (by positivity : X ^ 2 ≠ 0)]
      calc X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T
          ≤ X ^ 2 * (9 * (Real.log ((m : ℝ) * X)) ^ 2) / T := by gcongr
        _ = 9 * (Real.log ((m : ℝ) * X) / (m : ℝ)) * Real.log ((m : ℝ) * X) := hcancel
        _ ≤ 9 * X * Real.log ((m : ℝ) * X) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_div_m (by norm_num)) hlog_nn
        _ ≤ 9 * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by gcongr
    have hterm2 : X * Real.log ((m : ℝ) * X) ≤ X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by gcongr
    have hnn3 : 0 ≤ X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by positivity
    nlinarith
  have htri : |dyadic2Real (psi1AP m a) X - (1 / 4 : ℝ) * X ^ 2 / (m.totient : ℝ)| ≤
      ‖((dyadic2Real (psi1AP m a) X : ℝ) : ℂ) -
          (m.totient : ℂ)⁻¹ *
            ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
              ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
                ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)‖ +
      ‖(m.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
            ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ‖ := by
    have hrew : ((dyadic2Real (psi1AP m a) X - (1 / 4 : ℝ) * X ^ 2 / (m.totient : ℝ) : ℝ) : ℂ) =
        (((dyadic2Real (psi1AP m a) X : ℝ) : ℂ) -
          (m.totient : ℂ)⁻¹ *
            ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
              ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
                ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)) -
        (m.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
            ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ := by
      push_cast; rw [div_eq_mul_inv]; ring
    have hnorm := norm_sub_le
      (((dyadic2Real (psi1AP m a) X : ℝ) : ℂ) -
        (m.totient : ℂ)⁻¹ *
          ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
            ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
              ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ))
      ((m.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m, starRingEnd ℂ (χ (a : ZMod m)) *
          ∑ ρ ∈ lZerosInBox χ T, (lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * dyadicKernel ρ)
    rw [← hrew, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  dsimp only [C]; linarith

/-- **SHARP `GRH` LINNIK EXPONENT `L = 2 + ε`** (every `ε > 0`, all sufficiently large moduli `m ≥ M₀`):
under `DirichletLZerosOnLine`, for every `ε > 0` there exists `M₀ : ℕ` such that for all `m ≥ M₀`,
`Nat.Coprime a m`, and `X ≥ m ^ (2 + ε)`, there exists a prime `p ≡ a [MOD m]` in `(X, 2 * X]`. -/
theorem exists_prime_in_dyadic_ap_of_GRH_sharp (hGRH : DirichletLZerosOnLine)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ (m a : ℕ), M₀ ≤ m → Nat.Coprime a m →
      ∀ X : ℝ, (m : ℝ) ^ (2 + ε) ≤ X →
        ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD m] ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ 2 * X := by
  obtain ⟨C, hC_pos, hgrh⟩ := smoothed_ap_dyadic_of_GRH hGRH
  set α : ℝ := min (ε / (8 + 4 * ε)) (1 / 4)
  have hα_pos : 0 < α := by positivity
  have hα_lt_half : α ≤ 1 / 4 := min_le_right _ _
  have hα_bound : (1 / 2 - α) * (2 + ε) ≥ 1 + ε / 4 := by
    have h1 : α ≤ ε / (8 + 4 * ε) := min_le_left _ _
    have h2 : α * (2 + ε) ≤ ε / 4 := by
      have hden : 0 < 8 + 4 * ε := by linarith
      have := (le_div_iff₀ hden).mp h1
      linarith
    linarith
  set K : ℝ := 8 * (C + 2) / α + 1
  have hK_pos : 0 < K := by positivity
  set M₀ : ℕ := max 2 (⌈K ^ (4 / ε)⌉₊ + 1)
  refine ⟨M₀, le_max_left _ _, fun m a hm hcop X hX_m => ?_⟩
  have hm2 : 2 ≤ m := (le_max_left _ _).trans hm
  have : NeZero m := ⟨by omega⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hX_ge4 : 4 ≤ X := by
    have h1 : (4 : ℝ) ≤ (m : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]; nlinarith
    exact h1.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hX_m)
  have hX0 : 0 < X := by linarith
  have hm_le_X : (m : ℝ) ≤ X := by
    have h1 : (m : ℝ) ≤ (m : ℝ) ^ (2 + ε) := by
      calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (m : ℝ) ^ (2 + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    linarith
  have hasymp := hgrh m a hm2 hcop X hX_ge4
  have hlow := (abs_le.mp hasymp).1
  refine exists_prime_in_Ioc_of_dyadic2_psi1AP_gt m a (by linarith) ?_
  have htot_le_m : (m.totient : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.totient_le m
  have htot_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have hmain_ge : (1 / 4 : ℝ) * X ^ 2 / (m : ℝ) ≤ (1 / 4 : ℝ) * X ^ 2 / (m.totient : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) htot_pos htot_le_m
  -- Bound `(X / 2) * √(2 X) * log (2 X) ≤ 2 * X ^ (3 / 2) * log (m * X)`
  have hpp_le : (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) ≤
      2 * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
    have hsqrt2 : Real.sqrt (2 * X) ≤ 2 * X ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow X]
      have : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      nlinarith [Real.rpow_nonneg hX0.le (1 / 2 : ℝ)]
    have hlog2 : Real.log (2 * X) ≤ Real.log ((m : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
    have hX32 : X * X ^ (1 / 2 : ℝ) = X ^ (3 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]; congr 1; norm_num
    calc (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)
        ≤ (X / 2) * (2 * X ^ (1 / 2 : ℝ)) * Real.log ((m : ℝ) * X) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqrt2 (by positivity)) hlog2
            (Real.log_nonneg (by linarith)) (by positivity)
      _ = X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by rw [← hX32]; ring
      _ ≤ 2 * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
          have : 0 ≤ X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) :=
            mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
          linarith
  -- Show `(C + 2) * X ^ (3 / 2) * log (m * X) < (1 / 4) * X ^ 2 / m`!
  have hlogmX : Real.log ((m : ℝ) * X) ≤ (2 / α) * X ^ α := by
    have h1 : Real.log ((m : ℝ) * X) ≤ 2 * Real.log X := by
      rw [Real.log_mul hm_pos.ne' hX0.ne']; linarith [Real.log_le_log hm_pos hm_le_X]
    have h2 : Real.log X ≤ X ^ α / α := Real.log_le_rpow_div hX0.le hα_pos
    linarith [show 2 * (X ^ α / α) = (2 / α) * X ^ α by ring]
  have hm_eps : K < (m : ℝ) ^ (ε / 4) := by
    have hm_gt : K ^ (4 / ε) < (m : ℝ) := by
      have h1 : ⌈K ^ (4 / ε)⌉₊ + 1 ≤ m := (le_max_right _ _).trans hm
      have h2 : K ^ (4 / ε) ≤ (⌈K ^ (4 / ε)⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (⌈K ^ (4 / ε)⌉₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h1
      linarith
    have hpow := Real.rpow_lt_rpow (by positivity) hm_gt (by positivity : 0 < ε / 4)
    rw [← Real.rpow_mul hK_pos.le, show (4 / ε) * (ε / 4) = 1 by field_simp [hε.ne'], Real.rpow_one] at hpow
    exact hpow
  have hX_beat : 4 * (C + 2) * (2 / α) * (m : ℝ) < X ^ (1 / 2 - α) := by
    have h1 : (m : ℝ) ^ (1 + ε / 4) ≤ X ^ (1 / 2 - α) := by
      calc (m : ℝ) ^ (1 + ε / 4)
          ≤ (m : ℝ) ^ ((1 / 2 - α) * (2 + ε)) := Real.rpow_le_rpow_of_exponent_le (by linarith) hα_bound
        _ = ((m : ℝ) ^ (2 + ε)) ^ (1 / 2 - α) := by rw [← Real.rpow_mul hm_pos.le, mul_comm]
        _ ≤ X ^ (1 / 2 - α) := Real.rpow_le_rpow (by positivity) hX_m (by linarith)
    have h2 : 4 * (C + 2) * (2 / α) * (m : ℝ) < (m : ℝ) ^ (1 + ε / 4) := by
      rw [Real.rpow_add hm_pos, Real.rpow_one]
      have hK_gt : 4 * (C + 2) * (2 / α) < K := by dsimp only [K]; ring_nf; linarith
      have hlt : 4 * (C + 2) * (2 / α) < (m : ℝ) ^ (ε / 4) := hK_gt.trans hm_eps
      nlinarith
    exact h2.trans_le h1
  have hstrict : (C + 2) * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) < (1 / 4 : ℝ) * X ^ 2 / (m : ℝ) := by
    have h1 : (C + 2) * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) ≤
        (C + 2) * (2 / α) * X ^ (3 / 2 + α) := by
      have hpow : X ^ (3 / 2 : ℝ) * X ^ α = X ^ (3 / 2 + α) := (Real.rpow_add hX0 _ _).symm
      calc (C + 2) * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X)
          ≤ (C + 2) * X ^ (3 / 2 : ℝ) * ((2 / α) * X ^ α) := by gcongr
        _ = (C + 2) * (2 / α) * (X ^ (3 / 2 : ℝ) * X ^ α) := by ring
        _ = (C + 2) * (2 / α) * X ^ (3 / 2 + α) := by rw [hpow]
    have h2 : (C + 2) * (2 / α) * X ^ (3 / 2 + α) < (1 / 4 : ℝ) * X ^ 2 / (m : ℝ) := by
      rw [lt_div_iff₀ hm_pos]
      have hmul := mul_lt_mul_of_pos_right hX_beat (Real.rpow_pos_of_pos hX0 (3 / 2 + α))
      have hpow : X ^ (1 / 2 - α) * X ^ (3 / 2 + α) = X ^ 2 := by
        rw [← Real.rpow_add hX0, ← Real.rpow_two X]; congr 1; ring
      rw [hpow] at hmul
      linarith
    exact h1.trans_lt h2
  linarith

/-- **SHARP `GRH` LINNIK EXPONENT `L = 3`** (eventually for all `m ≥ M₀`):
under `DirichletLZerosOnLine`, there exists `M₀ ≥ 2` such that for every `m ≥ M₀`,
`Nat.Coprime a m`, and `X ≥ m ^ 3`, there exists a prime `p ≡ a [MOD m]` in `(X, 2 * X]`. -/
theorem linnik_exp_three_eventually_of_GRH (hGRH : DirichletLZerosOnLine) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ (m a : ℕ), M₀ ≤ m → Nat.Coprime a m →
      ∀ X : ℝ, (m : ℝ) ^ (3 : ℝ) ≤ X →
        ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD m] ∧ X < (p : ℝ) ∧ (p : ℝ) ≤ 2 * X := by
  have h := exists_prime_in_dyadic_ap_of_GRH_sharp hGRH (ε := 1) one_pos
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using h

/-- **FULL `GRH` DISCHARGE OF `Stage2PrimePairs.LinnikAPDyadic` (ALL `m ≥ 2`!)**:
`DirichletLZerosOnLine → Stage2PrimePairs.LinnikAPDyadic`. -/
theorem linnikAPDyadic_of_GRH (hGRH : DirichletLZerosOnLine) :
    Stage2PrimePairs.LinnikAPDyadic := by
  obtain ⟨C, hC_pos, hgrh⟩ := smoothed_ap_dyadic_of_GRH hGRH
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L : ℝ := max 4 (4 + 4 * (Real.log (32 * (C + 2) + 1) / Real.log 2))
  have hL_ge4 : 4 ≤ L := le_max_left _ _
  refine ⟨L, by linarith, fun m a hm hcop X hX_mL => ?_⟩
  have : NeZero m := ⟨by omega⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hX_ge4 : 4 ≤ X := by
    have h1 : (4 : ℝ) ≤ (m : ℝ) ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (by norm_num : (4 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hmR 4)
    exact h1.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith) hL_ge4).trans hX_mL)
  have hX0 : 0 < X := by linarith
  have hm_le_X : (m : ℝ) ≤ X := by
    calc (m : ℝ) = (m : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (m : ℝ) ^ L := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ X := hX_mL
  have hasymp := hgrh m a hm hcop X hX_ge4
  have hlow := (abs_le.mp hasymp).1
  refine exists_prime_in_Ioc_of_dyadic2_psi1AP_gt m a (by linarith) ?_
  have htot_le_m : (m.totient : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.totient_le m
  have htot_pos : (0 : ℝ) < (m.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos m))
  have hmain_ge : (1 / 4 : ℝ) * X ^ 2 / (m : ℝ) ≤ (1 / 4 : ℝ) * X ^ 2 / (m.totient : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) htot_pos htot_le_m
  have hpp_le : (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X) ≤
      2 * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
    have hsqrt2 : Real.sqrt (2 * X) ≤ 2 * X ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow X]
      have : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
      nlinarith [Real.rpow_nonneg hX0.le (1 / 2 : ℝ)]
    have hlog2 : Real.log (2 * X) ≤ Real.log ((m : ℝ) * X) := Real.log_le_log (by positivity) (by nlinarith)
    have hX32 : X * X ^ (1 / 2 : ℝ) = X ^ (3 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0]; congr 1; norm_num
    calc (X / 2) * Real.sqrt (2 * X) * Real.log (2 * X)
        ≤ (X / 2) * (2 * X ^ (1 / 2 : ℝ)) * Real.log ((m : ℝ) * X) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqrt2 (by positivity)) hlog2
            (Real.log_nonneg (by linarith)) (by positivity)
      _ = X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by rw [← hX32]; ring
      _ ≤ 2 * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) := by
          have : 0 ≤ X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) :=
            mul_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
          linarith
  have hlogmX : Real.log ((m : ℝ) * X) ≤ 8 * X ^ (1 / 4 : ℝ) := by
    have h1 : Real.log ((m : ℝ) * X) ≤ 2 * Real.log X := by
      rw [Real.log_mul hm_pos.ne' hX0.ne']; linarith [Real.log_le_log hm_pos hm_le_X]
    linarith [log_le_four_mul_rpow_quarter (by linarith : 1 ≤ X)]
  have hX14_gt : 32 * (C + 2) * (m : ℝ) < X ^ (1 / 4 : ℝ) := by
    have hL_step : Real.log (32 * (C + 2) + 1) / Real.log 2 ≤ L / 4 - 1 := by
      have h1 : 4 + 4 * (Real.log (32 * (C + 2) + 1) / Real.log 2) ≤ L := le_max_right _ _
      linarith
    have h32_lt : 32 * (C + 2) < (m : ℝ) ^ (L / 4 - 1) := by
      have h1 : 32 * (C + 2) + 1 ≤ (2 : ℝ) ^ (L / 4 - 1) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2)]
        exact (Real.log_le_iff_le_exp (by positivity)).mp ((div_le_iff₀ hlog2_pos).mp hL_step)
      have h2 : (2 : ℝ) ^ (L / 4 - 1) ≤ (m : ℝ) ^ (L / 4 - 1) :=
        Real.rpow_le_rpow (by norm_num) hmR (by linarith)
      linarith
    have hmL4 : (m : ℝ) ^ (L / 4) ≤ X ^ (1 / 4 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hX_mL (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_mul hm_pos.le, show L * (1 / 4 : ℝ) = L / 4 by ring] at h
      exact h
    have hsplit : (m : ℝ) ^ (L / 4) = (m : ℝ) ^ (L / 4 - 1) * (m : ℝ) := by
      conv_rhs => rhs; rw [← Real.rpow_one (m : ℝ)]
      rw [← Real.rpow_add hm_pos]; congr 1; ring
    rw [hsplit] at hmL4
    nlinarith
  have hstrict : (C + 2) * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) < (1 / 4 : ℝ) * X ^ 2 / (m : ℝ) := by
    have h1 : (C + 2) * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X) ≤ 8 * (C + 2) * X ^ (7 / 4 : ℝ) := by
      have hpow : X ^ (3 / 2 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (7 / 4 : ℝ) := by
        rw [← Real.rpow_add hX0]; congr 1; norm_num
      calc (C + 2) * X ^ (3 / 2 : ℝ) * Real.log ((m : ℝ) * X)
          ≤ (C + 2) * X ^ (3 / 2 : ℝ) * (8 * X ^ (1 / 4 : ℝ)) := by gcongr
        _ = 8 * (C + 2) * (X ^ (3 / 2 : ℝ) * X ^ (1 / 4 : ℝ)) := by ring
        _ = 8 * (C + 2) * X ^ (7 / 4 : ℝ) := by rw [hpow]
    have h2 : 8 * (C + 2) * X ^ (7 / 4 : ℝ) < (1 / 4 : ℝ) * X ^ 2 / (m : ℝ) := by
      rw [lt_div_iff₀ hm_pos]
      have hmul := mul_lt_mul_of_pos_right hX14_gt (Real.rpow_pos_of_pos hX0 (7 / 4 : ℝ))
      have hpow : X ^ (1 / 4 : ℝ) * X ^ (7 / 4 : ℝ) = X ^ 2 := by
        rw [← Real.rpow_add hX0, ← Real.rpow_two X]; congr 1; norm_num
      rw [hpow] at hmul
      linarith
    exact h1.trans_lt h2
  linarith

/-- **Direct GRH Corollary**: `DirichletLZerosOnLine → Stage2PrimePairs.LinnikAPInterval`. -/
theorem linnikAPInterval_of_GRH (hGRH : DirichletLZerosOnLine) :
    Stage2PrimePairs.LinnikAPInterval :=
  Stage2PrimePairs.linnikAPInterval_of_dyadic (linnikAPDyadic_of_GRH hGRH)

/-- **Direct GRH Corollary**: `DirichletLZerosOnLine → HostFieldSupply.PairSupply`. -/
theorem pairSupply_of_GRH (hGRH : DirichletLZerosOnLine) :
    HostFieldSupply.PairSupply :=
  Stage2PrimePairs.pairSupply_of_linnikAPInterval (linnikAPInterval_of_GRH hGRH)

/-- **Direct GRH Corollary**: `DirichletLZerosOnLine → ThetaSlopeEngine.PairEx`. -/
theorem pairEx_of_GRH (hGRH : DirichletLZerosOnLine) :
    ThetaSlopeEngine.PairEx :=
  Stage2PrimePairs.pairEx_of_linnikAPInterval (linnikAPInterval_of_GRH hGRH)

/-- **Direct GRH Corollary**: `DirichletLZerosOnLine → HostFieldSupply.SmallOne`. -/
theorem smallOne_of_GRH (hGRH : DirichletLZerosOnLine) :
    HostFieldSupply.SmallOne :=
  Stage2PrimePairs.smallOne_of_linnikAPInterval (linnikAPInterval_of_GRH hGRH)

end RHDirect.Stage11LinnikBridge

end



