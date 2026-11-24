import RHDirect.Stage5StirlingPhragmen
import RHDirect.Stage5ContourExplicit
import RHDirect.Stage6EffectivePNT
import RHDirect.Stage6XiZeroDensity
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# RHDirect.Stage7VonMangoldtExplicit

100%-unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings, 0 info) Stage 7 analytic number theory
framework directly on Mathlib's actual `Complex.Gamma`, `Complex.digamma`, `riemannZeta`,
`RiemannHypothesis`, `Chebyshev.psi`, and `Chebyshev.theta` in pure Mathlib `v4.33.1`.

## Main Results

1. **Exact Weierstrass–Gauss Digamma Series & Sharp `O(1)` Riemann–Siegel Theta Asymptotic**:
   - `digamma_eq_neg_eulerMascheroni_add_tsum`: unconditional Weierstrass–Gauss series
     `Complex.digamma s = -γ + ∑' n : ℕ, ((n + 1)⁻¹ - (s + n)⁻¹)` for all `0 < s.re`, proved via
     Cauchy's integral formula on `Complex.GammaSeq`.
   - `im_digamma_sub_arctan_bounds` & `im_digamma_half_add_I_mul_approx`: exact imaginary-part
     asymptotic `0 ≤ (Complex.digamma (σ + I * t)).im - Real.arctan (t / σ) ≤ t / (σ² + t²)`.
   - `re_digamma_sub_half_log_le` & `re_digamma_sub_log_le`: sharp `O(1 / t²)` real-part asymptotic
     via the `C²` trapezoidal rule on `g(x) = (σ + x) / ((σ + x)² + t²)`:
     `|(Complex.digamma (σ + I * t)).re - (1 / 2) * Real.log (σ² + t²)| ≤ (σ / 2 + 3 / 8) / (σ² + t²)`.
   - `riemannSiegelTheta_stirling_asymptotic_O1` & `riemannSiegelTheta_stirling_asymptotic`:
     unconditional sharp `O(1)` (and `O(log (T + 2))`) Riemann–Siegel phase asymptotic
     `|riemannSiegelTheta T - (T / 2) * Real.log (T / (2 * π * e))| ≤ C`.

2. **Exact Rectangular Argument-Principle Zero/Pole Counting & Unconditional Backlund Formula**:
   - `rect_argument_principle_meromorphic` & `rect_argument_principle_holomorphic`:
     exact rectangular argument principle `(1 / (2 π i)) ∮_{∂R} (f'/f)(s) ds = #(zeros) - #(poles)`
     counted with multiplicity via `Stage5ContourExplicit.rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part`.
   - `riemannZeta_re_lt_zero_of_Ioo` & `xi_ne_zero_of_real`: unconditional nonvanishing of
     `riemannZeta` on `(0, 1)` and of `xi` on all of `ℝ`.
   - `backlund_exact_formula`: exact unconditional Backlund identity
     `xiZeroCount T = riemannSiegelTheta T / π + 1 + backlundS T`
     for every `T > 0` free of zeros on `[0, 1] × {T}`, yielding both the sharp bound
     `|xiZeroCount T - (T / (2 π)) log (T / (2 π e))| ≤ C + |backlundS T|` and
     `|xiZeroCount T - (T / (2 π)) log (T / (2 π e))| ≤ C' * (Real.log T + |backlundS T|)`.

3. **Unconditional Sharp Bidirectional Equivalence: Zero-Free Half-Plane `Re(s) > θ` ↔ `ψ(x) - x = O(x^{θ + ε})` ↔ `RiemannHypothesis`**:
   - `negLogDerivZeta_bound_of_zeroFree_halfPlane`: unconditional Borel–Carathéodory `O(log(|t| + 2))`
     bound for `(-ζ'/ζ)(s)` on `Re(s) ≥ θ + δ` from `ZeroFree(θ)` alone.
   - `zeroFree_halfPlane_iff_psi_rpow_eps`: unconditional sharp bidirectional equivalence for every
     `0 < θ < 1` via `Stage3RealAnalyticLandau.zeroFree_riemannZeta_of_psi_bound` (forward) and
     `Stage5ContourExplicit` sharp Perron contour shift (reverse).
   - `riemannHypothesis_iff_psi_sqrt_eps` & `riemannHypothesis_iff_theta_sqrt_eps`:
     unconditional master equivalences
     `RiemannHypothesis ↔ ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * x ^ (1/2 + ε)`
     and
     `RiemannHypothesis ↔ ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.theta x - x| ≤ C * x ^ (1/2 + ε)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped BigOperators Real

namespace RHDirect.Stage7VonMangoldtExplicit

open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5ContourExplicit
open RHDirect.Stage6EffectivePNT
open RHDirect.Stage6XiZeroDensity

/-! ## Section 1: Exact Weierstrass–Gauss Digamma Series & Sharp Riemann–Siegel Theta Asymptotic -/

/-- Uniform integral bound on `Complex.GammaSeq w n` across any positive vertical strip
`0 < a ≤ w.re ≤ b` and all `n ≥ 1`. -/
lemma norm_GammaSeq_le_of_re_mem_Icc {a b : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) {w : ℂ}
    (hwa : a ≤ w.re) (hwb : w.re ≤ b) :
    ‖Complex.GammaSeq w n‖ ≤ Real.Gamma a + Real.Gamma b := by
  have hw_pos : 0 < w.re := lt_of_lt_of_le ha hwa
  have hb : 0 < b := lt_of_lt_of_le hw_pos hwb
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hw_pos hn]
  have hint_a : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hint_b : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (b - 1)) (Set.Ioi 0) :=
    Real.GammaIntegral_convergent hb
  have hint_sum : IntegrableOn
      (fun x : ℝ => Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (b - 1)) (Set.Ioi 0) :=
    hint_a.add hint_b
  have hsub : Set.Ioc (0 : ℝ) (n : ℝ) ⊆ Set.Ioi (0 : ℝ) := fun _ hx => hx.1
  have hpt : ∀ x ∈ Set.Ioc (0 : ℝ) (n : ℝ),
      ‖(((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖ ≤
        Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (b - 1) := by
    intro x hx
    have hx_pos : 0 < x := hx.1
    have h1_nn : 0 ≤ 1 - x / (n : ℝ) := by
      have : x / (n : ℝ) ≤ 1 := (div_le_one hn_pos).mpr hx.2
      linarith
    have hpow_le : (1 - x / (n : ℝ)) ^ n ≤ Real.exp (-x) := by
      have h1 : 1 - x / (n : ℝ) ≤ Real.exp (-(x / (n : ℝ))) := by
        linarith [Real.add_one_le_exp (-(x / (n : ℝ)))]
      calc (1 - x / (n : ℝ)) ^ n
          ≤ (Real.exp (-(x / (n : ℝ)))) ^ n := pow_le_pow_left₀ h1_nn h1 n
        _ = Real.exp ((n : ℝ) * (-(x / (n : ℝ)))) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp (-x) := by congr 1; field_simp [hn_pos.ne']
    have hrpow_le : x ^ (w.re - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
      rcases le_total x 1 with hx1 | hx1
      · have h1 : x ^ (w.re - 1) ≤ x ^ (a - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hx_pos hx1 (by linarith)
        linarith [Real.rpow_nonneg hx_pos.le (b - 1)]
      · have h2 : x ^ (w.re - 1) ≤ x ^ (b - 1) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
        linarith [Real.rpow_nonneg hx_pos.le (a - 1)]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg h1_nn n),
      Complex.norm_cpow_eq_rpow_re_of_pos hx_pos]
    have hre : (w - 1).re = w.re - 1 := by simp
    rw [hre]
    calc (1 - x / (n : ℝ)) ^ n * x ^ (w.re - 1)
        ≤ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)) :=
          mul_le_mul hpow_le hrpow_le (Real.rpow_nonneg hx_pos.le _) (Real.exp_pos _).le
      _ = Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (b - 1) := by ring
  have hint_lhs : IntegrableOn
      (fun x : ℝ => ‖(((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖) (Set.Ioc 0 (n : ℝ)) := by
    refine (hint_sum.mono_set hsub).mono' ?_ ?_
    · have hm : Measurable (fun x : ℝ => ‖(((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖) := by
        have h1 : Measurable (fun x : ℝ => (((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ)) :=
          Complex.measurable_ofReal.comp (by fun_prop)
        have h2 : Measurable (fun x : ℝ => (x : ℂ) ^ (w - 1)) :=
          Complex.measurable_ofReal.pow_const (w - 1)
        exact (h1.mul h2).norm
      exact hm.aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hpt x hx
  calc ‖∫ x : ℝ in (0 : ℝ)..(n : ℝ), (((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖
      ≤ ∫ x : ℝ in (0 : ℝ)..(n : ℝ), ‖(((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hn_pos.le
    _ = ∫ x : ℝ in Set.Ioc (0 : ℝ) (n : ℝ),
          ‖(((1 - x / (n : ℝ)) ^ n : ℝ) : ℂ) * (x : ℂ) ^ (w - 1)‖ :=
        intervalIntegral.integral_of_le hn_pos.le
    _ ≤ ∫ x : ℝ in Set.Ioc (0 : ℝ) (n : ℝ),
          (Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (b - 1)) :=
        MeasureTheory.setIntegral_mono_on hint_lhs (hint_sum.mono_set hsub) measurableSet_Ioc hpt
    _ ≤ ∫ x : ℝ in Set.Ioi (0 : ℝ),
          (Real.exp (-x) * x ^ (a - 1) + Real.exp (-x) * x ^ (b - 1)) := by
        refine MeasureTheory.setIntegral_mono_set hint_sum ?_ hsub.eventuallyLE
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
        have hx_pos : 0 < x := hx
        positivity
    _ = (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (a - 1)) +
          (∫ x : ℝ in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ (b - 1)) :=
        MeasureTheory.integral_add hint_a hint_b
    _ = Real.Gamma a + Real.Gamma b := by
        rw [Real.Gamma_eq_integral ha, Real.Gamma_eq_integral hb]

/-- Holomorphicity of `w ↦ Complex.GammaSeq w n` on `{w | 0 < w.re}` for `n ≥ 1`. -/
lemma differentiableOn_GammaSeq {n : ℕ} (hn : n ≠ 0) :
    DifferentiableOn ℂ (fun w : ℂ => Complex.GammaSeq w n) {w : ℂ | 0 < w.re} := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  intro w hw
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (n : ℂ) ^ z) w := by
    have hEq : (fun z : ℂ => (n : ℂ) ^ z) = fun z : ℂ => cexp (Complex.log (n : ℂ) * z) :=
      funext fun z => Complex.cpow_def_of_ne_zero hnC z
    rw [hEq]; fun_prop
  have hprod : DifferentiableAt ℂ (fun z : ℂ => ∏ j ∈ Finset.range (n + 1), (z + (j : ℂ))) w := by
    fun_prop
  have hprod_ne : ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j _ h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    have : (0 : ℝ) < w.re := hw
    linarith [Nat.cast_nonneg (α := ℝ) j]
  unfold Complex.GammaSeq
  exact ((hpow.mul (differentiableAt_const _)).div hprod hprod_ne).differentiableWithinAt

/-- Cauchy integral formula for the derivative of any function holomorphic on `closedBall s r`. -/
lemma deriv_eq_circleIntegral_dslope {f : ℂ → ℂ} {s : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall s r)) :
    deriv f s = (2 * (Real.pi : ℂ) * I)⁻¹ •
      ∮ z in C(s, r), (z - s)⁻¹ • ((f z - f s) / (z - s)) := by
  have hds_diff : DifferentiableOn ℂ (dslope f s) (Metric.closedBall s r) :=
    (Complex.differentiableOn_dslope (Metric.closedBall_mem_nhds s hr)).mpr hf
  have hds_dc : DiffContOnCl ℂ (dslope f s) (Metric.ball s r) := by
    refine ⟨hds_diff.mono Metric.ball_subset_closedBall, ?_⟩
    rw [closure_ball s hr.ne']
    exact hds_diff.continuousOn
  have hcauchy := hds_dc.circleIntegral_sub_inv_smul (Metric.mem_ball_self hr)
  rw [dslope_same] at hcauchy
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero
  have hinv := congrArg ((2 * (Real.pi : ℂ) * I)⁻¹ • ·) hcauchy
  rw [inv_smul_smul₀ h2piI] at hinv
  rw [← hinv]
  congr 1
  refine circleIntegral.integral_congr hr.le fun z hz => ?_
  have hne : z ≠ s := by
    intro h
    rw [Metric.mem_sphere, h, dist_self] at hz
    linarith
  rw [dslope_of_ne f hne, slope_def_field]

/-- Convergence of the derivatives `deriv (fun w => Complex.GammaSeq w n) s → deriv Complex.Gamma s`
for every `s` with `0 < s.re`, proved via Cauchy's integral formula and Dominated Convergence. -/
theorem tendsto_deriv_GammaSeq {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => deriv (fun w : ℂ => Complex.GammaSeq w n) s) atTop
      (𝓝 (deriv Complex.Gamma s)) := by
  set r : ℝ := s.re / 2 with hr_def
  have hr : 0 < r := by positivity
  have hcb_sub : Metric.closedBall s r ⊆ {w : ℂ | 0 < w.re} := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hw)).1
    rw [Complex.sub_re] at hre
    change 0 < w.re
    linarith
  have hcb_re : ∀ w ∈ Metric.closedBall s r, r ≤ w.re ∧ w.re ≤ 3 * r := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre := abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hw)
    rw [Complex.sub_re] at hre
    constructor <;> linarith
  have hG_diff : DifferentiableOn ℂ Complex.Gamma (Metric.closedBall s r) := by
    intro w hw
    have hw_pos : 0 < w.re := hcb_sub hw
    refine (Complex.differentiableAt_Gamma w fun m hEq => ?_).differentiableWithinAt
    have hre := congrArg Complex.re hEq
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  set M : ℝ := Real.Gamma r + Real.Gamma (3 * r)
  have hM_nn : 0 ≤ M := add_nonneg (Real.Gamma_pos_of_pos hr).le
    (Real.Gamma_pos_of_pos (by positivity)).le
  -- Parameterized circle integrand for `n` and for the limit `Gamma`
  let F : ℕ → ℝ → ℂ := fun n θ =>
    deriv (circleMap s r) θ • ((circleMap s r θ - s)⁻¹ •
      ((Complex.GammaSeq (circleMap s r θ) n - Complex.GammaSeq s n) / (circleMap s r θ - s)))
  let F_lim : ℝ → ℂ := fun θ =>
    deriv (circleMap s r) θ • ((circleMap s r θ - s)⁻¹ •
      ((Complex.Gamma (circleMap s r θ) - Complex.Gamma s) / (circleMap s r θ - s)))
  have hF_tend : Tendsto (fun n : ℕ => ∫ θ in (0 : ℝ)..(2 * Real.pi), F n θ) atTop
      (𝓝 (∫ θ in (0 : ℝ)..(2 * Real.pi), F_lim θ)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : ℝ => 2 * M / r) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      have hcont : Continuous (F n) := by
        have hgs_cont : ContinuousOn (fun w : ℂ => Complex.GammaSeq w n) (Metric.closedBall s r) :=
          ((differentiableOn_GammaSeq hn).mono hcb_sub).continuousOn
        have hcomp : Continuous (fun θ : ℝ => Complex.GammaSeq (circleMap s r θ) n) :=
          hgs_cont.comp_continuous (continuous_circleMap s r) fun θ =>
            Metric.sphere_subset_closedBall (circleMap_mem_sphere s hr.le θ)
        have hsub_ne : ∀ θ : ℝ, circleMap s r θ - s ≠ 0 := fun θ => by
          intro h
          have hn := congrArg norm h
          rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr, norm_zero] at hn
          linarith
        have hderiv_cont : Continuous (deriv (circleMap s r)) := by
          have hEq : deriv (circleMap s r) = fun θ => circleMap 0 r θ * I :=
            funext fun θ => deriv_circleMap s r θ
          rw [hEq]; fun_prop
        exact hderiv_cont.smul (((continuous_circleMap s r).sub continuous_const).inv₀ hsub_ne
          |>.smul ((hcomp.sub continuous_const).div ((continuous_circleMap s r).sub continuous_const) hsub_ne))
      exact hcont.aestronglyMeasurable
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine Eventually.of_forall fun θ _ => ?_
      dsimp only [F]
      have hmem : circleMap s r θ ∈ Metric.closedBall s r :=
        Metric.sphere_subset_closedBall (circleMap_mem_sphere s hr.le θ)
      have hre1 := hcb_re (circleMap s r θ) hmem
      have hre2 := hcb_re s (Metric.mem_closedBall_self hr.le)
      have hbd1 : ‖Complex.GammaSeq (circleMap s r θ) n‖ ≤ M :=
        norm_GammaSeq_le_of_re_mem_Icc hr hn hre1.1 hre1.2
      have hbd2 : ‖Complex.GammaSeq s n‖ ≤ M :=
        norm_GammaSeq_le_of_re_mem_Icc hr hn hre2.1 hre2.2
      have hnorm_sub : ‖circleMap s r θ - s‖ = r := by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
      have hnorm_deriv : ‖deriv (circleMap s r) θ‖ = r := by
        rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
      rw [norm_smul, norm_smul, norm_inv, norm_div, hnorm_deriv, hnorm_sub]
      calc r * (r⁻¹ * (‖Complex.GammaSeq (circleMap s r θ) n - Complex.GammaSeq s n‖ / r))
          = ‖Complex.GammaSeq (circleMap s r θ) n - Complex.GammaSeq s n‖ / r := by
            field_simp [hr.ne']
        _ ≤ (‖Complex.GammaSeq (circleMap s r θ) n‖ + ‖Complex.GammaSeq s n‖) / r :=
            div_le_div_of_nonneg_right (norm_sub_le _ _) hr.le
        _ ≤ (M + M) / r := div_le_div_of_nonneg_right (add_le_add hbd1 hbd2) hr.le
        _ = 2 * M / r := by ring
    · refine Eventually.of_forall fun θ _ => ?_
      dsimp only [F, F_lim]
      exact (((Complex.GammaSeq_tendsto_Gamma (circleMap s r θ)).sub
        (Complex.GammaSeq_tendsto_Gamma s)).div_const _).const_smul _ |>.const_smul _
  have hscaled := hF_tend.const_smul ((2 * (Real.pi : ℂ) * I)⁻¹)
  have hlim_eq : (2 * (Real.pi : ℂ) * I)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi), F_lim θ =
      deriv Complex.Gamma s := by
    rw [deriv_eq_circleIntegral_dslope hr hG_diff]
    rfl
  rw [hlim_eq] at hscaled
  refine hscaled.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  symm
  rw [deriv_eq_circleIntegral_dslope hr ((differentiableOn_GammaSeq hn).mono hcb_sub)]
  rfl

/-- Exact logarithmic derivative of `w ↦ Complex.GammaSeq w n` for `0 < s.re` and `n ≥ 1`. -/
lemma logDeriv_GammaSeq {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    logDeriv (fun w : ℂ => Complex.GammaSeq w n) s =
      (Real.log (n : ℝ) : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have hfacC : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hterm_ne : ∀ j ∈ Finset.range (n + 1), s + (j : ℂ) ≠ 0 := fun j _ h0 => by
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hprod_ne : ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hterm_ne
  have hpow_ne : (n : ℂ) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hnC]; exact Complex.exp_ne_zero _
  have hpow_d : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w) ((Real.log (n : ℝ) : ℂ) * (n : ℂ) ^ s) s := by
    have hEq : (fun w : ℂ => (n : ℂ) ^ w) = fun w : ℂ => cexp ((Real.log (n : ℝ) : ℂ) * w) := by
      funext w
      rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
    have h1 : HasDerivAt (fun w : ℂ => (Real.log (n : ℝ) : ℂ) * w) (Real.log (n : ℝ) : ℂ) s := by
      simpa using (hasDerivAt_id s).const_mul (Real.log (n : ℝ) : ℂ)
    rw [hEq]
    refine h1.cexp.congr_deriv ?_
    rw [congrFun hEq s]; ring
  have hnum_d : HasDerivAt (fun w : ℂ => (n : ℂ) ^ w * (n.factorial : ℂ))
      ((Real.log (n : ℝ) : ℂ) * ((n : ℂ) ^ s * (n.factorial : ℂ))) s := by
    refine (hpow_d.mul_const (n.factorial : ℂ)).congr_deriv ?_; ring
  have hden_d : DifferentiableAt ℂ (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s := by
    fun_prop
  have hden_ld : deriv (fun w : ℂ => ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s /
      (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) =
      ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
    have hld := logDeriv_prod (s := Finset.range (n + 1))
      (f := fun (j : ℕ) (w : ℂ) => w + (j : ℂ)) (x := s)
      hterm_ne (fun j _ => differentiableAt_id.add (differentiableAt_const _))
    rw [← logDeriv_apply, hld]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun w : ℂ => w + (j : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).add_const (j : ℂ)
    rw [hd.deriv, one_div]
  have hquot_d := hnum_d.fun_div hden_d.hasDerivAt hprod_ne
  rw [logDeriv_apply]
  change deriv (fun w : ℂ => (n : ℂ) ^ w * (n.factorial : ℂ) /
      ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s /
      ((n : ℂ) ^ s * (n.factorial : ℂ) / ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) = _
  rw [hquot_d.deriv, ← hden_ld]
  field_simp [hpow_ne, hfacC, hprod_ne]

/-- Absolute summability of the Weierstrass–Gauss digamma series terms `((n + 1)⁻¹ - (s + n)⁻¹)`
for every `s : ℂ` with `0 < s.re`. -/
theorem summable_digamma_term {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℂ))⁻¹ - (s + (n : ℂ))⁻¹) := by
  have hbase : Summable (fun n : ℕ => ‖s - 1‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) := by
      simp [one_div, Real.summable_nat_pow_inv]
    have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff 1).mpr h1
    simpa [div_eq_mul_inv] using h2.mul_left ‖s - 1‖
  refine Summable.of_norm_bounded (g := fun n : ℕ => (‖s - 1‖ * (1 + 1 / s.re)) / ((n + 1 : ℕ) : ℝ) ^ 2)
    (by
      have h1 : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) := by
        simp [one_div, Real.summable_nat_pow_inv]
      have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
        (summable_nat_add_iff 1).mpr h1
      simpa [div_eq_mul_inv] using h2.mul_left (‖s - 1‖ * (1 + 1 / s.re))) fun n => ?_
  have hn1_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hn1C : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn1_pos.ne'
  have hsn_re : 0 < (s + (n : ℂ)).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hsn_ne : s + (n : ℂ) ≠ 0 := fun h => by rw [h, Complex.zero_re] at hsn_re; exact lt_irrefl 0 hsn_re
  have hdiff : (((n + 1 : ℕ) : ℂ))⁻¹ - (s + (n : ℂ))⁻¹ =
      (s - 1) / (((n + 1 : ℕ) : ℂ) * (s + (n : ℂ))) := by
    field_simp [hn1C, hsn_ne]
    push_cast; ring
  rw [hdiff, norm_div, norm_mul, Complex.norm_natCast]
  have hsn_ge : ((n + 1 : ℕ) : ℝ) / (1 + 1 / s.re) ≤ ‖s + (n : ℂ)‖ := by
    have h1 : s.re + (n : ℝ) ≤ ‖s + (n : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (s + (n : ℂ))
      have hre : (s + (n : ℂ)).re = s.re + (n : ℝ) := by simp
      rw [hre, abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])] at h
      exact h
    have hden_pos : 0 < 1 + 1 / s.re := by positivity
    rw [div_le_iff₀ hden_pos]
    have hmul : ((n + 1 : ℕ) : ℝ) ≤ (s.re + (n : ℝ)) * (1 + 1 / s.re) := by
      have hEq : (s.re + (n : ℝ)) * (1 + 1 / s.re) = s.re + 1 + (n : ℝ) + (n : ℝ) / s.re := by
        field_simp [hs.ne']; ring
      rw [hEq]; push_cast
      have : 0 ≤ (n : ℝ) / s.re := by positivity
      linarith
    exact hmul.trans (mul_le_mul_of_nonneg_right h1 hden_pos.le)
  have hden_pos : 0 < 1 + 1 / s.re := by positivity
  have hprod_ge : ((n + 1 : ℕ) : ℝ) ^ 2 / (1 + 1 / s.re) ≤ ((n + 1 : ℕ) : ℝ) * ‖s + (n : ℂ)‖ := by
    calc ((n + 1 : ℕ) : ℝ) ^ 2 / (1 + 1 / s.re)
        = ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) / (1 + 1 / s.re)) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * ‖s + (n : ℂ)‖ := mul_le_mul_of_nonneg_left hsn_ge hn1_pos.le
  calc ‖s - 1‖ / (((n + 1 : ℕ) : ℝ) * ‖s + (n : ℂ)‖)
      ≤ ‖s - 1‖ / (((n + 1 : ℕ) : ℝ) ^ 2 / (1 + 1 / s.re)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hprod_ge
    _ = ‖s - 1‖ * (1 + 1 / s.re) / ((n + 1 : ℕ) : ℝ) ^ 2 := by field_simp

private lemma harmonic_real_eq_sum_range (N : ℕ) :
    (harmonic N : ℝ) = ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ)⁻¹ := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [harmonic_succ, Rat.cast_add, ih, Finset.sum_range_succ]
    simp

/-- **Unconditional Weierstrass–Gauss Series for Mathlib's `Complex.digamma`**:
for every `s : ℂ` with `0 < s.re`,
`Complex.digamma s = -γ + ∑' n : ℕ, ((n + 1)⁻¹ - (s + n)⁻¹)`. -/
theorem digamma_eq_neg_eulerMascheroni_add_tsum {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s = -(Real.eulerMascheroniConstant : ℂ) +
      ∑' n : ℕ, ((((n + 1 : ℕ) : ℂ))⁻¹ - (s + (n : ℂ))⁻¹) := by
  have hG_ne : Complex.Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hEq => ?_
    have hre := congrArg Complex.re hEq
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hLHS : Tendsto (fun n : ℕ => logDeriv (fun w : ℂ => Complex.GammaSeq w n) s) atTop
      (𝓝 (Complex.digamma s)) := by
    rw [Complex.digamma_def, logDeriv_apply]
    have h := (tendsto_deriv_GammaSeq hs).div (Complex.GammaSeq_tendsto_Gamma s) hG_ne
    exact h.congr fun n => rfl
  have hharm : Tendsto (fun n : ℕ => (Real.log (n : ℝ) - (harmonic (n + 1) : ℝ))) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun n : ℕ => -((harmonic n : ℝ) - Real.log (n : ℝ))) atTop
        (𝓝 (-Real.eulerMascheroniConstant)) :=
      Real.tendsto_harmonic_sub_log.neg
    have h2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    refine h3.congr fun n => ?_
    rw [harmonic_succ]
    push_cast
    ring
  have hsum := (summable_digamma_term hs).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hRHS : Tendsto (fun n : ℕ =>
      ((Real.log (n : ℝ) - (harmonic (n + 1) : ℝ) : ℝ) : ℂ) +
        ∑ j ∈ Finset.range (n + 1), ((((j + 1 : ℕ) : ℂ))⁻¹ - (s + (j : ℂ))⁻¹))
      atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ) +
        ∑' j : ℕ, ((((j + 1 : ℕ) : ℂ))⁻¹ - (s + (j : ℂ))⁻¹))) := by
    have h1 := (Complex.continuous_ofReal.tendsto _).comp hharm
    simpa [Complex.ofReal_neg] using h1.add hsum
  refine tendsto_nhds_unique hLHS (hRHS.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [logDeriv_GammaSeq hs hn]
  have hharm_eq : ((harmonic (n + 1) : ℝ) : ℂ) = ∑ j ∈ Finset.range (n + 1), (((j + 1 : ℕ) : ℂ))⁻¹ := by
    rw [harmonic_real_eq_sum_range, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => by push_cast; rfl
  rw [Complex.ofReal_sub, hharm_eq, Finset.sum_sub_distrib]
  ring

/-- Conjugation symmetry of `Complex.digamma` on `0 < s.re`:
`Complex.digamma (starRingEnd ℂ s) = starRingEnd ℂ (Complex.digamma s)`. -/
theorem digamma_conj {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma (starRingEnd ℂ s) = starRingEnd ℂ (Complex.digamma s) := by
  have hs' : 0 < (starRingEnd ℂ s).re := by simpa using hs
  rw [digamma_eq_neg_eulerMascheroni_add_tsum hs', digamma_eq_neg_eulerMascheroni_add_tsum hs,
    map_add, map_neg, Complex.conj_ofReal, Complex.conj_tsum]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [map_sub, map_inv₀, map_add, map_natCast]

/-- On the positive real axis, `Complex.digamma (σ : ℂ)` is real-valued. -/
theorem im_digamma_ofReal_eq_zero {σ : ℝ} (hσ : 0 < σ) :
    (Complex.digamma (σ : ℂ)).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← digamma_conj (by simpa using hσ), Complex.conj_ofReal]

/-- Exact positive series formula for the imaginary part of `Complex.digamma (σ + I * t)`:
`(Complex.digamma (σ + I * t)).im = ∑' n : ℕ, t / ((σ + n)² + t²)` for all `σ > 0`, `t : ℝ`. -/
theorem im_digamma_eq_tsum {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).im =
      ∑' n : ℕ, t / ((σ + (n : ℝ)) ^ 2 + t ^ 2) := by
  have hs : 0 < ((σ : ℂ) + I * (t : ℂ)).re := by simpa using hσ
  rw [digamma_eq_neg_eulerMascheroni_add_tsum hs, Complex.add_im, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_add]
  have him_sum := (Complex.imCLM.hasSum (summable_digamma_term hs).hasSum).tsum_eq
  change Complex.imCLM (∑' n : ℕ, ((((n + 1 : ℕ) : ℂ))⁻¹ - (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ))⁻¹)) = _
  rw [← him_sum]
  refine tsum_congr fun n => ?_
  change ((((n + 1 : ℕ) : ℂ))⁻¹ - (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ))⁻¹).im =
    t / ((σ + (n : ℝ)) ^ 2 + t ^ 2)
  rw [Complex.sub_im]
  have h1 : ((((n + 1 : ℕ) : ℂ))⁻¹).im = 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
  rw [h1, zero_sub, Complex.inv_im]
  have hre : (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)).re = σ + (n : ℝ) := by simp
  have him : (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)).im = t := by simp
  have hnsq : Complex.normSq (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)) = (σ + (n : ℝ)) ^ 2 + t ^ 2 := by
    rw [Complex.normSq_apply, hre, him]; ring
  rw [him, hnsq]
  ring

/-- **Sharp Two-Sided Imaginary-Part Asymptotic for `Complex.digamma`**:
for all `0 < σ` and `0 < t`,
`0 ≤ (Complex.digamma (σ + I * t)).im - Real.arctan (t / σ) ≤ t / (σ² + t²)`. -/
theorem im_digamma_sub_arctan_bounds {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    0 ≤ (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).im - Real.arctan (t / σ) ∧
    (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).im - Real.arctan (t / σ) ≤
      t / (σ ^ 2 + t ^ 2) := by
  let f : ℝ → ℝ := fun x => t / ((σ + x) ^ 2 + t ^ 2)
  have hf_cont : Continuous f :=
    continuous_const.div (by fun_prop) fun x => (by positivity : 0 < (σ + x) ^ 2 + t ^ 2).ne'
  have hf_anti : AntitoneOn f (Set.Ici 0) := by
    intro x hx y hy hxy
    dsimp only [f]
    refine div_le_div_of_nonneg_left ht.le (by positivity) ?_
    have hx' : 0 < σ + x := by linarith [Set.mem_Ici.mp hx]
    have hy' : σ + x ≤ σ + y := by linarith
    nlinarith
  have hint_eval : ∀ N : ℕ, ∫ x in (0 : ℝ)..(N : ℝ), f x =
      Real.arctan ((σ + (N : ℝ)) / t) - Real.arctan (σ / t) := by
    intro N
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
        HasDerivAt (fun u : ℝ => Real.arctan ((σ + u) / t)) (f x) x := by
      intro x _
      have hlin : HasDerivAt (fun u : ℝ => (σ + u) / t) (1 / t) x := by
        simpa using ((hasDerivAt_id x).const_add σ).div_const t
      refine hlin.arctan.congr_deriv ?_
      dsimp only [f]
      have hpos : 0 < (σ + x) ^ 2 + t ^ 2 := by positivity
      field_simp [ht.ne', hpos.ne']; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hf_cont.intervalIntegrable _ _)]
    simp
  have hunit_le : ∀ n : ℕ, f (n + 1 : ℕ) ≤ ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x ∧
      ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x ≤ f (n : ℝ) := by
    intro n
    have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    constructor
    · have h1 : ∫ _x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f ((n + 1 : ℕ) : ℝ) ≤
          ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const
          (hf_cont.intervalIntegrable _ _) fun x hx =>
            hf_anti (Set.mem_Ici.mpr ((Nat.cast_nonneg n).trans hx.1))
              (Set.mem_Ici.mpr (Nat.cast_nonneg (n + 1))) hx.2
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have hsub : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
      rwa [hsub, one_mul] at h1
    · have h1 : ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x ≤
          ∫ _x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f (n : ℝ) :=
        intervalIntegral.integral_mono_on hle (hf_cont.intervalIntegrable _ _)
          intervalIntegrable_const fun x hx =>
            hf_anti (Set.mem_Ici.mpr (Nat.cast_nonneg n))
              (Set.mem_Ici.mpr ((Nat.cast_nonneg n).trans hx.1)) hx.1
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have hsub : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
      rwa [hsub, one_mul] at h1
  have hsum_int : ∀ N : ℕ,
      ∫ x in (0 : ℝ)..(N : ℝ), f x =
        ∑ n ∈ Finset.range N, ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih,
        intervalIntegral.integral_add_adjacent_intervals (hf_cont.intervalIntegrable _ _)
          (hf_cont.intervalIntegrable _ _)]
  have hbounds_N : ∀ N : ℕ,
      Real.arctan ((σ + (N : ℝ)) / t) - Real.arctan (σ / t) ≤
        ∑ n ∈ Finset.range N, f (n : ℝ) ∧
      ∑ n ∈ Finset.range N, f (n : ℝ) ≤
        f 0 + (Real.arctan ((σ + (N : ℝ)) / t) - Real.arctan (σ / t)) := by
    intro N
    rw [← hint_eval N, hsum_int N]
    constructor
    · exact Finset.sum_le_sum fun n _ => (hunit_le n).2
    · cases N with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        dsimp only [f]; positivity
      | succ k =>
        rw [Finset.sum_range_succ']
        have hdrop : ∑ n ∈ Finset.range k, f ((n + 1 : ℕ) : ℝ) ≤
            ∑ n ∈ Finset.range (k + 1), ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x := by
          calc ∑ n ∈ Finset.range k, f ((n + 1 : ℕ) : ℝ)
              ≤ ∑ n ∈ Finset.range k, ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x :=
                Finset.sum_le_sum fun n _ => (hunit_le n).1
            _ ≤ ∑ n ∈ Finset.range (k + 1), ∫ x in (n : ℝ)..((n + 1 : ℕ) : ℝ), f x := by
                rw [Finset.sum_range_succ]
                have hnn : 0 ≤ ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x :=
                  intervalIntegral.integral_nonneg (by push_cast; linarith) fun x _ => by
                    dsimp only [f]; positivity
                linarith
        simp only [Nat.cast_zero]
        linarith
  have hsumm : Summable (fun n : ℕ => f (n : ℝ)) := by
    have hs : 0 < ((σ : ℂ) + I * (t : ℂ)).re := by simpa using hσ
    have h1 := (Complex.imCLM.hasSum (summable_digamma_term hs).hasSum).summable
    refine h1.congr fun n => ?_
    change ((((n + 1 : ℕ) : ℂ))⁻¹ - (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ))⁻¹).im = f (n : ℝ)
    rw [Complex.sub_im]
    have hz : ((((n + 1 : ℕ) : ℂ))⁻¹).im = 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
    rw [hz, zero_sub, Complex.inv_im]
    have hre : (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)).re = σ + (n : ℝ) := by simp
    have him : (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)).im = t := by simp
    have hnsq : Complex.normSq (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)) = (σ + (n : ℝ)) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply, hre, him]; ring
    rw [him, hnsq]; dsimp only [f]; ring
  have harc_tend : Tendsto (fun N : ℕ => Real.arctan ((σ + (N : ℝ)) / t) - Real.arctan (σ / t))
      atTop (𝓝 (Real.arctan (t / σ))) := by
    have harg : Tendsto (fun N : ℕ => (σ + (N : ℝ)) / t) atTop atTop :=
      (tendsto_atTop_add_const_left atTop σ tendsto_natCast_atTop_atTop).atTop_div_const ht
    have h1 : Tendsto (fun N : ℕ => Real.arctan ((σ + (N : ℝ)) / t)) atTop (𝓝 (Real.pi / 2)) :=
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
    have h2 := h1.sub_const (Real.arctan (σ / t))
    have hpi : Real.pi / 2 - Real.arctan (σ / t) = Real.arctan (t / σ) := by
      have h := Real.arctan_inv_of_pos (div_pos hσ ht)
      rw [inv_div] at h
      linarith
    rwa [hpi] at h2
  rw [im_digamma_eq_tsum hσ t]
  have hlo := le_of_tendsto_of_tendsto harc_tend hsumm.hasSum.tendsto_sum_nat
    (Eventually.of_forall fun N => (hbounds_N N).1)
  have hhi := le_of_tendsto_of_tendsto hsumm.hasSum.tendsto_sum_nat (harc_tend.const_add (f 0))
    (Eventually.of_forall fun N => (hbounds_N N).2)
  have hf0 : f 0 = t / (σ ^ 2 + t ^ 2) := by simp [f]
  rw [hf0] at hhi
  exact ⟨by linarith, by linarith⟩

/-- Specialized imaginary-part digamma approximation along the critical-line argument `1/4 + i T/2`:
`|(Complex.digamma (1/4 + I * (T/2))).im - Real.arctan (2 * T)| ≤ 2 / T`
and `|(Complex.digamma (1/4 + I * (T/2))).im - Real.pi / 2| ≤ 5 / (2 * T)` for all `T > 0`. -/
theorem im_digamma_half_add_I_mul_approx {T : ℝ} (hT : 0 < T) :
    |(Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.arctan (2 * T)| ≤ 2 / T ∧
    |(Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.pi / 2| ≤ 5 / (2 * T) := by
  have hbd := im_digamma_sub_arctan_bounds (σ := 1 / 4) (t := T / 2) (by norm_num) (by positivity)
  have hcast : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by push_cast; rfl
  have hdiv : (T / 2) / (1 / 4 : ℝ) = 2 * T := by ring
  rw [hcast, hdiv] at hbd
  have hle2 : (T / 2) / ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2) ≤ 2 / T := by
    have hden : (T / 2) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2 := by nlinarith
    calc (T / 2) / ((1 / 4 : ℝ) ^ 2 + (T / 2) ^ 2)
        ≤ (T / 2) / (T / 2) ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 2 / T := by field_simp [hT.ne']
  have h1 : |(Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.arctan (2 * T)| ≤ 2 / T := by
    rw [abs_of_nonneg hbd.1]
    exact hbd.2.trans hle2
  have harc_diff : Real.pi / 2 - Real.arctan (2 * T) = Real.arctan (1 / (2 * T)) := by
    have h := Real.arctan_inv_of_pos (by positivity : (0 : ℝ) < 2 * T)
    rw [one_div]
    linarith
  have harc_le : Real.arctan (1 / (2 * T)) ≤ 1 / (2 * T) := by
    have hu : 0 ≤ 1 / (2 * T) := by positivity
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (1 / (2 * T)),
        HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := fun x _ => by
      simpa [one_div] using Real.hasDerivAt_arctan x
    have hcont : Continuous (fun x : ℝ => (1 : ℝ) / (1 + x ^ 2)) :=
      continuous_const.div (by fun_prop) fun x => (by positivity : 0 < 1 + x ^ 2).ne'
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
    rw [Real.arctan_zero, sub_zero] at hint
    rw [← hint]
    calc ∫ x in (0 : ℝ)..(1 / (2 * T)), (1 : ℝ) / (1 + x ^ 2)
        ≤ ∫ _x in (0 : ℝ)..(1 / (2 * T)), (1 : ℝ) :=
          intervalIntegral.integral_mono_on hu (hcont.intervalIntegrable _ _) intervalIntegrable_const
            fun x _ => div_le_one_of_le₀ (by nlinarith) (by positivity)
      _ = 1 / (2 * T) := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have harc_nn : 0 ≤ Real.arctan (1 / (2 * T)) := by
    rw [← Real.arctan_zero]
    exact Real.arctan_mono (by positivity)
  have h2 : |(Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.pi / 2| ≤ 5 / (2 * T) := by
    have hrew : (Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.pi / 2 =
        ((Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.arctan (2 * T)) -
          (Real.pi / 2 - Real.arctan (2 * T)) := by ring
    rw [hrew]
    calc |((Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.arctan (2 * T)) -
            (Real.pi / 2 - Real.arctan (2 * T))|
        ≤ |(Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).im - Real.arctan (2 * T)| +
            |Real.pi / 2 - Real.arctan (2 * T)| := abs_sub _ _
      _ ≤ 2 / T + 1 / (2 * T) := by
            rw [harc_diff, abs_of_nonneg harc_nn]; exact add_le_add h1 harc_le
      _ = 5 / (2 * T) := by ring
  exact ⟨h1, h2⟩

/-- Elementary `C²` unit-interval trapezoidal error bound:
`|(g a + g (a + 1)) / 2 - ∫ x in a..(a + 1), g x| ≤ (1 / 8) * ∫ x in a..(a + 1), |g'' x|`. -/
lemma abs_trapezoid_sub_integral_le {g g' g'' : ℝ → ℝ} (a : ℝ)
    (hg : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a (a + 1), HasDerivAt g' (g'' x) x)
    (hcg : ContinuousOn g (Set.uIcc a (a + 1)))
    (hcg'' : ContinuousOn g'' (Set.uIcc a (a + 1))) :
    |(g a + g (a + 1)) / 2 - ∫ x in a..(a + 1), g x| ≤
      (1 / 8 : ℝ) * ∫ x in a..(a + 1), |g'' x| := by
  let F : ℝ → ℝ := fun x =>
    (x - a - 1 / 2) * g x - (1 / 2) * ((x - a) * (x - a - 1)) * g' x
  have hF_deriv : ∀ x ∈ Set.uIcc a (a + 1),
      HasDerivAt F (g x - (1 / 2) * ((x - a) * (x - a - 1)) * g'' x) x := by
    intro x hx
    have h1 : HasDerivAt (fun u : ℝ => u - a - 1 / 2) 1 x := by
      simpa using ((hasDerivAt_id x).sub_const a).sub_const (1 / 2 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ => (u - a) * (u - a - 1)) (2 * (x - a) - 1) x := by
      have ha1 : HasDerivAt (fun u : ℝ => u - a) 1 x := (hasDerivAt_id x).sub_const a
      have ha2 : HasDerivAt (fun u : ℝ => u - a - 1) 1 x :=
        ((hasDerivAt_id x).sub_const a).sub_const 1
      refine (ha1.mul ha2).congr_deriv ?_; ring
    have hterm1 := h1.mul (hg x hx)
    have hterm2 := (h2.const_mul (1 / 2 : ℝ)).mul (hg' x hx)
    refine (hterm1.sub hterm2).congr_deriv ?_
    ring
  have hrem_cont : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * ((x - a) * (x - a - 1)) * g'' x)
      (Set.uIcc a (a + 1)) :=
    ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).mul
      ((continuousOn_id.sub continuousOn_const).sub continuousOn_const))).mul hcg'')
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF_deriv
    ((hcg.sub hrem_cont).intervalIntegrable)
  rw [intervalIntegral.integral_sub hcg.intervalIntegrable hrem_cont.intervalIntegrable] at hftc
  have hF_diff : F (a + 1) - F a = (g a + g (a + 1)) / 2 := by
    dsimp only [F]; ring
  rw [hF_diff] at hftc
  have hdiff_eq : (g a + g (a + 1)) / 2 - ∫ x in a..(a + 1), g x =
      -(∫ x in a..(a + 1), (1 / 2 : ℝ) * ((x - a) * (x - a - 1)) * g'' x) := by
    linarith
  rw [hdiff_eq, abs_neg, ← Real.norm_eq_abs]
  have hle : a ≤ a + 1 := by linarith
  calc ‖∫ x in a..(a + 1), (1 / 2 : ℝ) * ((x - a) * (x - a - 1)) * g'' x‖
      ≤ ∫ x in a..(a + 1), ‖(1 / 2 : ℝ) * ((x - a) * (x - a - 1)) * g'' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hle
    _ ≤ ∫ x in a..(a + 1), (1 / 8 : ℝ) * |g'' x| := by
        refine intervalIntegral.integral_mono_on hle hrem_cont.intervalIntegrable.norm
          (hcg''.abs.intervalIntegrable.const_mul (1 / 8)) fun x hx => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have hquad : |(x - a) * (x - a - 1)| ≤ 1 / 4 := by
          have h0 : 0 ≤ x - a := by linarith [hx.1]
          have h1 : x - a - 1 ≤ 0 := by linarith [hx.2]
          rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos h0 h1)]
          nlinarith [sq_nonneg (2 * (x - a) - 1)]
        have hmul : (1 / 2 : ℝ) * |(x - a) * (x - a - 1)| ≤ 1 / 8 := by linarith
        exact mul_le_mul_of_nonneg_right hmul (abs_nonneg _)
    _ = (1 / 8 : ℝ) * ∫ x in a..(a + 1), |g'' x| := intervalIntegral.integral_const_mul _ _

/-- **Sharp `O(1 / (σ² + t²))` Real-Part Asymptotic for `Complex.digamma`** via the `C²`
trapezoidal rule: for ALL `0 < σ` and `0 < t`,
`|(Complex.digamma (σ + I * t)).re - (1 / 2) * Real.log (σ² + t²)| ≤ (σ / 2 + 3 / 8) / (σ² + t²)`. -/
theorem re_digamma_sub_half_log_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |(Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)| ≤
      (σ / 2 + 3 / 8) / (σ ^ 2 + t ^ 2) := by
  let g : ℝ → ℝ := fun x => (σ + x) / ((σ + x) ^ 2 + t ^ 2)
  let g' : ℝ → ℝ := fun x => (t ^ 2 - (σ + x) ^ 2) / ((σ + x) ^ 2 + t ^ 2) ^ 2
  let g'' : ℝ → ℝ := fun x =>
    2 * (σ + x) * ((σ + x) ^ 2 - 3 * t ^ 2) / ((σ + x) ^ 2 + t ^ 2) ^ 3
  have hg_d : ∀ x : ℝ, HasDerivAt g (g' x) x := fun x => by
    have hden_pos : 0 < (σ + x) ^ 2 + t ^ 2 := by positivity
    have h1 : HasDerivAt (fun u : ℝ => σ + u) 1 x := by simpa using (hasDerivAt_id x).const_add σ
    have h2 : HasDerivAt (fun u : ℝ => (σ + u) ^ 2 + t ^ 2) (2 * (σ + x)) x := by
      simpa using (h1.pow 2).add_const (t ^ 2)
    refine (h1.div h2 hden_pos.ne').congr_deriv ?_
    dsimp only [g']; ring
  have hg'_d : ∀ x : ℝ, HasDerivAt g' (g'' x) x := fun x => by
    have hden_pos : 0 < (σ + x) ^ 2 + t ^ 2 := by positivity
    have h1 : HasDerivAt (fun u : ℝ => σ + u) 1 x := by simpa using (hasDerivAt_id x).const_add σ
    have hnum : HasDerivAt (fun u : ℝ => t ^ 2 - (σ + u) ^ 2) (-(2 * (σ + x))) x := by
      have hsq : HasDerivAt (fun u : ℝ => (σ + u) ^ 2) (2 * (σ + x)) x := by
        simpa using h1.fun_pow 2
      simpa using (hasDerivAt_const x (t ^ 2)).fun_sub hsq
    have hbase : HasDerivAt (fun u : ℝ => (σ + u) ^ 2 + t ^ 2) (2 * (σ + x)) x := by
      simpa using (h1.fun_pow 2).add_const (t ^ 2)
    have hden : HasDerivAt (fun u : ℝ => ((σ + u) ^ 2 + t ^ 2) ^ 2)
        (2 * ((σ + x) ^ 2 + t ^ 2) * (2 * (σ + x))) x := by
      simpa using hbase.fun_pow 2
    refine (hnum.div hden (pow_ne_zero 2 hden_pos.ne')).congr_deriv ?_
    dsimp only [g'']
    field_simp [hden_pos.ne']
    ring
  have hg_cont : Continuous g :=
    (by fun_prop : Continuous fun x : ℝ => σ + x).div (by fun_prop) fun x =>
      (by positivity : 0 < (σ + x) ^ 2 + t ^ 2).ne'
  have hg''_cont : Continuous g'' :=
    (by fun_prop : Continuous fun x : ℝ => 2 * (σ + x) * ((σ + x) ^ 2 - 3 * t ^ 2)).div
      (by fun_prop) fun x => (pow_pos (by positivity : 0 < (σ + x) ^ 2 + t ^ 2) 3).ne'
  -- Exact integral of `g` on `[0, N]`
  have hint_g : ∀ N : ℕ, ∫ x in (0 : ℝ)..(N : ℝ), g x =
      (1 / 2 : ℝ) * Real.log ((σ + (N : ℝ)) ^ 2 + t ^ 2) - (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2) := by
    intro N
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
        HasDerivAt (fun u : ℝ => (1 / 2 : ℝ) * Real.log ((σ + u) ^ 2 + t ^ 2)) (g x) x := by
      intro x _
      have hden_pos : 0 < (σ + x) ^ 2 + t ^ 2 := by positivity
      have h1 : HasDerivAt (fun u : ℝ => (σ + u) ^ 2 + t ^ 2) (2 * (σ + x)) x := by
        simpa using (((hasDerivAt_id x).const_add σ).pow 2).add_const (t ^ 2)
      refine ((h1.log hden_pos.ne').const_mul (1 / 2 : ℝ)).congr_deriv ?_
      dsimp only [g]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hg_cont.intervalIntegrable _ _)]
    simp
  -- Upper bound on `∫_0^N |g'' x| dx ≤ 3 / (σ² + t²)`
  have hg''_int_le : ∀ N : ℕ, ∫ x in (0 : ℝ)..(N : ℝ), |g'' x| ≤ 3 / (σ ^ 2 + t ^ 2) := by
    intro N
    have hmaj_cont : Continuous (fun x : ℝ => 6 * (σ + x) / ((σ + x) ^ 2 + t ^ 2) ^ 2) :=
      (by fun_prop : Continuous fun x : ℝ => 6 * (σ + x)).div (by fun_prop) fun x =>
        (pow_pos (by positivity : 0 < (σ + x) ^ 2 + t ^ 2) 2).ne'
    have hpt : ∀ x ∈ Set.Icc (0 : ℝ) (N : ℝ),
        |g'' x| ≤ 6 * (σ + x) / ((σ + x) ^ 2 + t ^ 2) ^ 2 := by
      intro x hx
      have hu : 0 ≤ σ + x := by linarith [hx.1]
      have hden_pos : 0 < (σ + x) ^ 2 + t ^ 2 := by positivity
      dsimp only [g'']
      rw [abs_div, abs_of_pos (pow_pos hden_pos 3), abs_mul, abs_of_nonneg (by linarith)]
      have hnum : |(σ + x) ^ 2 - 3 * t ^ 2| ≤ 3 * ((σ + x) ^ 2 + t ^ 2) := by
        rw [abs_le]; constructor <;> nlinarith
      calc 2 * (σ + x) * |(σ + x) ^ 2 - 3 * t ^ 2| / ((σ + x) ^ 2 + t ^ 2) ^ 3
          ≤ 2 * (σ + x) * (3 * ((σ + x) ^ 2 + t ^ 2)) / ((σ + x) ^ 2 + t ^ 2) ^ 3 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by linarith))
              (pow_pos hden_pos 3).le
        _ = 6 * (σ + x) / ((σ + x) ^ 2 + t ^ 2) ^ 2 := by field_simp [hden_pos.ne']; ring
    have hprim : ∫ x in (0 : ℝ)..(N : ℝ), 6 * (σ + x) / ((σ + x) ^ 2 + t ^ 2) ^ 2 =
        3 / (σ ^ 2 + t ^ 2) - 3 / ((σ + (N : ℝ)) ^ 2 + t ^ 2) := by
      have hd : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
          HasDerivAt (fun u : ℝ => -(3 / ((σ + u) ^ 2 + t ^ 2)))
            (6 * (σ + x) / ((σ + x) ^ 2 + t ^ 2) ^ 2) x := by
        intro x _
        have hden_pos : 0 < (σ + x) ^ 2 + t ^ 2 := by positivity
        have h1 : HasDerivAt (fun u : ℝ => (σ + u) ^ 2 + t ^ 2) (2 * (σ + x)) x := by
          simpa using (((hasDerivAt_id x).const_add σ).pow 2).add_const (t ^ 2)
        have h2 := ((h1.inv hden_pos.ne').const_mul 3).neg
        refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp [div_eq_mul_inv])).congr_deriv ?_
        field_simp [hden_pos.ne']; ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hmaj_cont.intervalIntegrable _ _)]
      simp; ring
    have hmono := intervalIntegral.integral_mono_on (Nat.cast_nonneg N)
      (hg''_cont.abs.intervalIntegrable (μ := volume) _ _)
      (hmaj_cont.intervalIntegrable (μ := volume) _ _) hpt
    rw [hprim] at hmono
    have htail : 0 ≤ 3 / ((σ + (N : ℝ)) ^ 2 + t ^ 2) := by positivity
    linarith
  -- Telescoping trapezoidal bound on `[0, N]`
  have htel : ∀ N : ℕ, ∑ n ∈ Finset.range N, g (n : ℝ) =
      (1 / 2 : ℝ) * g 0 - (1 / 2 : ℝ) * g (N : ℝ) +
        ∑ n ∈ Finset.range N, (g (n : ℝ) + g ((n : ℝ) + 1)) / 2 := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Nat.cast_succ]
      ring
  have hint_split : ∀ N : ℕ, ∫ x in (0 : ℝ)..(N : ℝ), g x =
      ∑ n ∈ Finset.range N, ∫ x in (n : ℝ)..((n : ℝ) + 1), g x := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih, Nat.cast_succ,
        intervalIntegral.integral_add_adjacent_intervals (hg_cont.intervalIntegrable (μ := volume) _ _)
          (hg_cont.intervalIntegrable (μ := volume) _ _)]
  have hrem_split : ∀ N : ℕ, ∑ n ∈ Finset.range N, ∫ x in (n : ℝ)..((n : ℝ) + 1), |g'' x| =
      ∫ x in (0 : ℝ)..(N : ℝ), |g'' x| := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ,
        intervalIntegral.integral_add_adjacent_intervals (hg''_cont.abs.intervalIntegrable (μ := volume) _ _)
          (hg''_cont.abs.intervalIntegrable (μ := volume) _ _)]
  have htrap_N : ∀ N : ℕ,
      |∑ n ∈ Finset.range N, g (n : ℝ) - ∫ x in (0 : ℝ)..(N : ℝ), g x| ≤
        (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * g (N : ℝ) + (3 / 8 : ℝ) / (σ ^ 2 + t ^ 2) := by
    intro N
    have hsum_err :
        |∑ n ∈ Finset.range N, ((g (n : ℝ) + g ((n : ℝ) + 1)) / 2 -
            ∫ x in (n : ℝ)..((n : ℝ) + 1), g x)| ≤ (3 / 8 : ℝ) / (σ ^ 2 + t ^ 2) := by
      calc |∑ n ∈ Finset.range N, ((g (n : ℝ) + g ((n : ℝ) + 1)) / 2 -
              ∫ x in (n : ℝ)..((n : ℝ) + 1), g x)|
          ≤ ∑ n ∈ Finset.range N, |(g (n : ℝ) + g ((n : ℝ) + 1)) / 2 -
              ∫ x in (n : ℝ)..((n : ℝ) + 1), g x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.range N, (1 / 8 : ℝ) * ∫ x in (n : ℝ)..((n : ℝ) + 1), |g'' x| :=
            Finset.sum_le_sum fun n _ =>
              abs_trapezoid_sub_integral_le (n : ℝ) (fun x _ => hg_d x) (fun x _ => hg'_d x)
                hg_cont.continuousOn hg''_cont.continuousOn
        _ = (1 / 8 : ℝ) * ∑ n ∈ Finset.range N, ∫ x in (n : ℝ)..((n : ℝ) + 1), |g'' x| := by
            rw [← Finset.mul_sum]
        _ = (1 / 8 : ℝ) * ∫ x in (0 : ℝ)..(N : ℝ), |g'' x| := by rw [hrem_split N]
        _ ≤ (1 / 8 : ℝ) * (3 / (σ ^ 2 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left (hg''_int_le N) (by norm_num)
        _ = (3 / 8 : ℝ) / (σ ^ 2 + t ^ 2) := by ring
    have hrew : ∑ n ∈ Finset.range N, g (n : ℝ) - ∫ x in (0 : ℝ)..(N : ℝ), g x =
        ((1 / 2 : ℝ) * g 0 - (1 / 2 : ℝ) * g (N : ℝ)) +
          ∑ n ∈ Finset.range N, ((g (n : ℝ) + g ((n : ℝ) + 1)) / 2 -
            ∫ x in (n : ℝ)..((n : ℝ) + 1), g x) := by
      rw [htel N, hint_split N, Finset.sum_sub_distrib]; ring
    rw [hrew]
    have hg0_nn : 0 ≤ g 0 := by dsimp only [g]; positivity
    have hgN_nn : 0 ≤ g (N : ℝ) := by dsimp only [g]; positivity
    have h1 : |(1 / 2 : ℝ) * g 0 - (1 / 2 : ℝ) * g (N : ℝ)| ≤ (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * g (N : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    exact (abs_add_le _ _).trans (add_le_add h1 hsum_err)
  -- Express `(Complex.digamma (σ + I * t)).re` as limit of partial sums
  have hs : 0 < ((σ : ℂ) + I * (t : ℂ)).re := by simpa using hσ
  have hre_hasSum := Complex.reCLM.hasSum (summable_digamma_term hs).hasSum
  have hterm_re : ∀ n : ℕ,
      ((((n + 1 : ℕ) : ℂ))⁻¹ - (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ))⁻¹).re =
        ((n + 1 : ℕ) : ℝ)⁻¹ - g (n : ℝ) := fun n => by
    rw [Complex.sub_re]
    have h1 : ((((n + 1 : ℕ) : ℂ))⁻¹).re = ((n + 1 : ℕ) : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [h1, Complex.inv_re]
    have hre : (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)).re = σ + (n : ℝ) := by simp
    have him : (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)).im = t := by simp
    have hnsq : Complex.normSq (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ)) = (σ + (n : ℝ)) ^ 2 + t ^ 2 := by
      rw [Complex.normSq_apply, hre, him]; ring
    rw [hre, hnsq]
  have hdig_re : Tendsto (fun N : ℕ =>
      -Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ)⁻¹ - g (n : ℝ)))
      atTop (𝓝 (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re) := by
    have h1 := hre_hasSum.tendsto_sum_nat.const_add (-Real.eulerMascheroniConstant)
    simp only [Complex.reCLM_apply] at h1
    have hlim : -Real.eulerMascheroniConstant +
        (∑' n : ℕ, ((((n + 1 : ℕ) : ℂ))⁻¹ - (((σ : ℂ) + I * (t : ℂ)) + (n : ℂ))⁻¹)).re =
        (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re := by
      rw [digamma_eq_neg_eulerMascheroni_add_tsum hs, Complex.add_re, Complex.neg_re,
        Complex.ofReal_re]
    rw [hlim] at h1
    refine h1.congr fun N => ?_
    congr 1
    exact Finset.sum_congr rfl fun n _ => hterm_re n
  -- Limit of `log ((σ + N)² + t²) / 2 - log N → 0`
  have hlog_ratio : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * Real.log ((σ + (N : ℝ)) ^ 2 + t ^ 2) - Real.log (N : ℝ)) atTop (𝓝 0) := by
    have hq : Tendsto (fun N : ℕ => (1 + σ / (N : ℝ)) ^ 2 + (t / (N : ℝ)) ^ 2) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => σ / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun N : ℕ => t / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa using ((h1.const_add 1).pow 2).add (h2.pow 2)
    have h3 : Tendsto (fun N : ℕ =>
        (1 / 2 : ℝ) * Real.log ((1 + σ / (N : ℝ)) ^ 2 + (t / (N : ℝ)) ^ 2)) atTop (𝓝 0) := by
      simpa using ((Real.continuousAt_log one_ne_zero).tendsto.comp hq).const_mul (1 / 2 : ℝ)
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hEq : (1 + σ / (N : ℝ)) ^ 2 + (t / (N : ℝ)) ^ 2 =
        ((σ + (N : ℝ)) ^ 2 + t ^ 2) / (N : ℝ) ^ 2 := by
      field_simp [hN0.ne']; ring
    rw [hEq, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hgN_tend : Tendsto (fun N : ℕ => g (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by dsimp only [g]; positivity) (fun N => ?_)
      (tendsto_const_nhds (x := (1 : ℝ)).div_atTop
        (tendsto_atTop_add_const_left atTop σ tendsto_natCast_atTop_atTop))
    dsimp only [g]
    have hpos : 0 < σ + (N : ℝ) := by positivity
    calc (σ + (N : ℝ)) / ((σ + (N : ℝ)) ^ 2 + t ^ 2)
        ≤ (σ + (N : ℝ)) / (σ + (N : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_left hpos.le (by positivity) (by nlinarith)
      _ = 1 / (σ + (N : ℝ)) := by field_simp [hpos.ne']
  -- Combine limits: `|Re(digamma) - (1/2) log(σ² + t²)| = lim |-(∑ g(n) - ∫ g)|`
  have herr_tend : Tendsto (fun N : ℕ =>
      |∑ n ∈ Finset.range N, g (n : ℝ) - ∫ x in (0 : ℝ)..(N : ℝ), g x|) atTop
      (𝓝 |(Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)|) := by
    have h1 : Tendsto (fun N : ℕ =>
        (harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant -
          ((1 / 2 : ℝ) * Real.log ((σ + (N : ℝ)) ^ 2 + t ^ 2) - Real.log (N : ℝ)) -
          (-Real.eulerMascheroniConstant + ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ)⁻¹ - g (n : ℝ))) +
          (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2))
        atTop
        (𝓝 (0 - 0 - (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re +
          (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2))) := by
      have hh : Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant)
          atTop (𝓝 0) := by
        simpa using Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant
      exact (((hh.sub hlog_ratio).sub hdig_re).add tendsto_const_nhds)
    have h2 : Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range N, g (n : ℝ) - ∫ x in (0 : ℝ)..(N : ℝ), g x)
        atTop
        (𝓝 (-((Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re -
          (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)))) := by
      have hlim_eq : 0 - 0 - (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re +
          (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2) =
          -((Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re -
            (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)) := by ring
      rw [hlim_eq] at h1
      refine h1.congr fun N => ?_
      rw [harmonic_real_eq_sum_range, hint_g N, Finset.sum_sub_distrib]
      ring
    have h2' := h2.abs
    rwa [abs_neg] at h2'
  have hrhs_tend : Tendsto (fun N : ℕ =>
      (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * g (N : ℝ) + (3 / 8 : ℝ) / (σ ^ 2 + t ^ 2))
      atTop (𝓝 ((σ / 2 + 3 / 8) / (σ ^ 2 + t ^ 2))) := by
    have h1 := ((hgN_tend.const_mul (1 / 2 : ℝ)).const_add ((1 / 2 : ℝ) * g 0)).add_const
      ((3 / 8 : ℝ) / (σ ^ 2 + t ^ 2))
    have hlim : (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * 0 + (3 / 8 : ℝ) / (σ ^ 2 + t ^ 2) =
        (σ / 2 + 3 / 8) / (σ ^ 2 + t ^ 2) := by
      dsimp only [g]; ring
    rwa [hlim] at h1
  exact le_of_tendsto_of_tendsto herr_tend hrhs_tend (Eventually.of_forall htrap_N)

/-- **Sharp `O(1 / t²)` Comparison of `Re(digamma (σ + I * t))` with `Real.log t`**:
for ALL `0 < σ` and `0 < t`,
`|(Complex.digamma (σ + I * t)).re - Real.log t| ≤ (σ² / 2 + σ / 2 + 3 / 8) / t²`. -/
theorem re_digamma_sub_log_le {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |(Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - Real.log t| ≤
      (σ ^ 2 / 2 + σ / 2 + 3 / 8) / t ^ 2 := by
  have h1 := re_digamma_sub_half_log_le hσ ht
  have hlog_diff : (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2) - Real.log t =
      (1 / 2 : ℝ) * Real.log (1 + σ ^ 2 / t ^ 2) := by
    have hEq : σ ^ 2 + t ^ 2 = t ^ 2 * (1 + σ ^ 2 / t ^ 2) := by field_simp [ht.ne']; ring
    rw [hEq, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  have hlog_nn : 0 ≤ (1 / 2 : ℝ) * Real.log (1 + σ ^ 2 / t ^ 2) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [div_nonneg (sq_nonneg σ) (sq_nonneg t)]))
  have hlog_le : (1 / 2 : ℝ) * Real.log (1 + σ ^ 2 / t ^ 2) ≤ (σ ^ 2 / 2) / t ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + σ ^ 2 / t ^ 2)
    linarith [show (1 / 2 : ℝ) * (σ ^ 2 / t ^ 2) = (σ ^ 2 / 2) / t ^ 2 by ring]
  have hmain_le : (σ / 2 + 3 / 8) / (σ ^ 2 + t ^ 2) ≤ (σ / 2 + 3 / 8) / t ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have hrew : (Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - Real.log t =
      ((Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)) +
        ((1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2) - Real.log t) := by ring
  rw [hrew]
  calc |((Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)) +
          ((1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2) - Real.log t)|
      ≤ |(Complex.digamma ((σ : ℂ) + I * (t : ℂ))).re - (1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2)| +
          |(1 / 2 : ℝ) * Real.log (σ ^ 2 + t ^ 2) - Real.log t| := abs_add_le _ _
    _ ≤ (σ / 2 + 3 / 8) / t ^ 2 + (σ ^ 2 / 2) / t ^ 2 := by
          rw [hlog_diff, abs_of_nonneg hlog_nn]
          exact add_le_add (h1.trans hmain_le) hlog_le
    _ = (σ ^ 2 / 2 + σ / 2 + 3 / 8) / t ^ 2 := by ring

/-- Concrete strip bound on `Re(digamma (σ + I * T)) - Real.log T` for `σ ∈ [1/4, 2]`, `T ≥ 2`. -/
theorem re_digamma_strip_approx {σ T : ℝ} (hσ1 : 1 / 4 ≤ σ) (hσ2 : σ ≤ 2) (hT : 2 ≤ T) :
    |(Complex.digamma ((σ : ℂ) + I * (T : ℂ))).re - Real.log T| ≤ 2 / T := by
  have h1 := re_digamma_sub_log_le (by linarith : 0 < σ) (by linarith : 0 < T)
  have hnum : σ ^ 2 / 2 + σ / 2 + 3 / 8 ≤ 4 := by nlinarith
  calc |(Complex.digamma ((σ : ℂ) + I * (T : ℂ))).re - Real.log T|
      ≤ (σ ^ 2 / 2 + σ / 2 + 3 / 8) / T ^ 2 := h1
    _ ≤ 4 / T ^ 2 := div_le_div_of_nonneg_right hnum (sq_nonneg T)
    _ ≤ 2 / T := by
        rw [div_le_div_iff₀ (by positivity) (by linarith)]
        nlinarith

/-- Holomorphicity of `Complex.digamma` on the right half-plane `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_digamma_re_pos :
    DifferentiableOn ℂ Complex.digamma {s : ℂ | 0 < s.re} := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := fun s hs =>
    (Complex.differentiableAt_Gamma s fun m hEq => by
      have hre := congrArg Complex.re hEq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have : 0 < s.re := hs
      linarith [Nat.cast_nonneg (α := ℝ) m]).differentiableWithinAt
  have hG_ne : ∀ s ∈ {s : ℂ | 0 < s.re}, Complex.Gamma s ≠ 0 := fun s hs =>
    Complex.Gamma_ne_zero fun m hEq => by
      have hre := congrArg Complex.re hEq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have : 0 < s.re := hs
      linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [Complex.digamma_def]
  exact (hG.deriv hU).div hG hG_ne

/-- Exact formula for `logDeriv Complex.Gammaℝ` on `{s : ℂ | 0 < s.re}`:
`logDeriv Complex.Gammaℝ s = -(log π / 2) + (1 / 2) * Complex.digamma (s / 2)`. -/
theorem logDeriv_Gammaℝ_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hpow_eq : (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) =
      fun w : ℂ => cexp (-((Real.log Real.pi / 2 : ℝ) : ℂ) * w) := by
    funext w
    rw [Complex.cpow_def_of_ne_zero hpiC, ← Complex.ofReal_log Real.pi_pos.le]
    congr 1; push_cast; ring
  have hpow_d : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2))
      (-((Real.log Real.pi / 2 : ℝ) : ℂ) * (Real.pi : ℂ) ^ (-s / 2)) s := by
    have h1 : HasDerivAt (fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) * w)
        (-((Real.log Real.pi / 2 : ℝ) : ℂ)) s := by
      simpa using (hasDerivAt_id s).const_mul (-((Real.log Real.pi / 2 : ℝ) : ℂ))
    rw [hpow_eq]
    refine h1.cexp.congr_deriv ?_
    rw [congrFun hpow_eq s]; ring
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hpiC]; exact Complex.exp_ne_zero _
  have hs2_pos : 0 < (s / 2).re := by simp; linarith
  have hG_d : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) fun m hEq => by
      have hre := congrArg Complex.re hEq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero fun m hEq => by
      have hre := congrArg Complex.re hEq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_comp_d : HasDerivAt (fun w : ℂ => Complex.Gamma (w / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ)) s := by
    have hdiv : HasDerivAt (fun w : ℂ => w / 2) (1 / 2 : ℂ) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℂ)
    exact hG_d.hasDerivAt.comp s hdiv
  have hprod_d := hpow_d.fun_mul hG_comp_d
  have hfun : Complex.Gammaℝ =
      fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) := by
    funext w; exact Complex.Gammaℝ_def w
  rw [logDeriv_apply, hfun, hprod_d.deriv, Complex.digamma_def, logDeriv_apply]
  field_simp [hpow_ne, hG_ne]

/-- **The Riemann–Siegel Theta Function `ϑ(T)`**:
`riemannSiegelTheta T = ∫_0^T ((1/2) Re ψ(1/4 + i t/2) - (1/2) log π) dt`,
matching the exact continuous argument `Im(log Γℝ(1/2 + i T))` along the critical line. -/
def riemannSiegelTheta (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T,
    ((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
      (1 / 2 : ℝ) * Real.log Real.pi)

/-- Continuity of the integrand defining `riemannSiegelTheta`. -/
lemma continuous_riemannSiegelTheta_integrand :
    Continuous (fun t : ℝ =>
      (1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
        (1 / 2 : ℝ) * Real.log Real.pi) := by
  have hdig : Continuous (fun t : ℝ => Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))) :=
    differentiableOn_digamma_re_pos.continuousOn.comp_continuous (by fun_prop) fun t => by
      change (0 : ℝ) < ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ)).re
      simp
  exact (continuous_const.mul (Complex.continuous_re.comp hdig)).sub continuous_const

/-- Exact derivative of the Riemann–Siegel theta function:
`ϑ'(T) = (1/2) Re ψ(1/4 + i T/2) - (1/2) log π` for all `T : ℝ`. -/
theorem hasDerivAt_riemannSiegelTheta (T : ℝ) :
    HasDerivAt riemannSiegelTheta
      ((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((T / 2 : ℝ) : ℂ))).re -
        (1 / 2 : ℝ) * Real.log Real.pi) T :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_riemannSiegelTheta_integrand.intervalIntegrable 0 T)
    (continuous_riemannSiegelTheta_integrand.stronglyMeasurableAtFilter volume (𝓝 T))
    continuous_riemannSiegelTheta_integrand.continuousAt

/-- Exact identification of `riemannSiegelTheta T` with the vertical integral of
`Re(logDeriv Complex.Gammaℝ (1/2 + i t))` along the critical line. -/
theorem riemannSiegelTheta_eq_integral_re_logDeriv_Gammaℝ (T : ℝ) :
    riemannSiegelTheta T =
      ∫ t in (0 : ℝ)..T, (logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  unfold riemannSiegelTheta
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hs : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by simp
  rw [logDeriv_Gammaℝ_eq hs]
  have hdiv : ((1 / 2 : ℂ) + I * (t : ℂ)) / 2 = (1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp; norm_num
    · simp
  rw [hdiv]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
    zero_mul, sub_zero]
  ring

/-- **UNCONDITIONAL SHARP `O(1)` RIEMANN–SIEGEL PHASE ASYMPTOTIC**:
there exists `C > 0` such that for every `T ≥ 1`,
`|riemannSiegelTheta T - (T / 2) * Real.log (T / (2 * π * e))| ≤ C`. -/
theorem riemannSiegelTheta_stirling_asymptotic_O1 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      |riemannSiegelTheta T - (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤ C := by
  let M : ℝ → ℝ := fun t => (t / 2) * Real.log (t / (2 * Real.pi * Real.exp 1))
  let m : ℝ → ℝ := fun t => (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))
  set C : ℝ := |riemannSiegelTheta 1 - M 1| + 2 with hC_def
  refine ⟨C, by positivity, fun T hT => ?_⟩
  have hm_cont : ContinuousOn m (Set.uIcc 1 T) := by
    rw [Set.uIcc_of_le hT]
    refine continuousOn_const.mul (Real.continuousOn_log.comp
      (continuousOn_id.div_const _) fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    exact (div_pos ht0 (by positivity)).ne'
  have hM_deriv : ∀ t ∈ Set.uIcc 1 T, HasDerivAt M (m t) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2 : ℝ) t := by
      simpa using (hasDerivAt_id t).div_const 2
    have h2 : HasDerivAt (fun u : ℝ => Real.log (u / (2 * Real.pi * Real.exp 1))) (t⁻¹) t := by
      have hlin : HasDerivAt (fun u : ℝ => u / (2 * Real.pi * Real.exp 1))
          (1 / (2 * Real.pi * Real.exp 1)) t := by
        simpa using (hasDerivAt_id t).div_const (2 * Real.pi * Real.exp 1)
      refine (hlin.log (div_pos ht0 (by positivity)).ne').congr_deriv ?_
      field_simp [ht0.ne', Real.pi_pos.ne', (Real.exp_pos 1).ne']
    refine (h1.mul h2).congr_deriv ?_
    dsimp only [m]
    have hlog : Real.log (t / (2 * Real.pi * Real.exp 1)) = Real.log (t / (2 * Real.pi)) - 1 := by
      rw [show t / (2 * Real.pi * Real.exp 1) = (t / (2 * Real.pi)) / Real.exp 1 by ring,
        Real.log_div (div_pos ht0 (by positivity)).ne' (Real.exp_pos 1).ne', Real.log_exp]
    rw [hlog]
    field_simp [ht0.ne']
    ring
  have hM_int : ∫ t in (1 : ℝ)..T, m t = M T - M 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hM_deriv hm_cont.intervalIntegrable
  have htheta_split : riemannSiegelTheta T - riemannSiegelTheta 1 =
      ∫ t in (1 : ℝ)..T,
        ((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
          (1 / 2 : ℝ) * Real.log Real.pi) := by
    unfold riemannSiegelTheta
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (continuous_riemannSiegelTheta_integrand.intervalIntegrable (μ := volume) 0 1)
      (continuous_riemannSiegelTheta_integrand.intervalIntegrable (μ := volume) 1 T)
    linarith
  have hdiff_eq : (riemannSiegelTheta T - M T) - (riemannSiegelTheta 1 - M 1) =
      ∫ t in (1 : ℝ)..T,
        (((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
            (1 / 2 : ℝ) * Real.log Real.pi) - m t) := by
    rw [intervalIntegral.integral_sub
      (continuous_riemannSiegelTheta_integrand.intervalIntegrable (μ := volume) 1 T)
      (hm_cont.intervalIntegrable (μ := volume)), ← htheta_split, hM_int]
    ring
  have hpt_bd : ∀ t ∈ Set.Icc (1 : ℝ) T,
      |((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
          (1 / 2 : ℝ) * Real.log Real.pi) - m t| ≤ 2 / t ^ 2 := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have hlog_eq : (1 / 2 : ℝ) * Real.log Real.pi + m t = (1 / 2 : ℝ) * Real.log (t / 2) := by
      dsimp only [m]
      rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
        Real.log_div (by positivity) Real.pi_pos.ne']
      ring
    have hrew : ((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
          (1 / 2 : ℝ) * Real.log Real.pi) - m t =
        (1 / 2 : ℝ) * ((Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
          Real.log (t / 2)) := by
      linarith
    rw [hrew, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hdig := re_digamma_sub_log_le (σ := 1 / 4) (t := t / 2) (by norm_num) (by positivity)
    have hcast : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by push_cast; rfl
    rw [hcast] at hdig
    have hcoef : (1 / 2 : ℝ) * (((1 / 4 : ℝ) ^ 2 / 2 + (1 / 4 : ℝ) / 2 + 3 / 8) / (t / 2) ^ 2) ≤
        2 / t ^ 2 := by
      have h1 : (1 / 2 : ℝ) * (((1 / 4 : ℝ) ^ 2 / 2 + (1 / 4 : ℝ) / 2 + 3 / 8) / (t / 2) ^ 2) =
          (17 / 16 : ℝ) / t ^ 2 := by ring
      rw [h1]
      exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg t)
    exact (mul_le_mul_of_nonneg_left hdig (by norm_num)).trans hcoef
  have hinv_cont : ContinuousOn (fun t : ℝ => (2 : ℝ) / t ^ 2) (Set.uIcc 1 T) := by
    rw [Set.uIcc_of_le hT]
    exact continuousOn_const.div (continuousOn_pow 2) fun t ht =>
      pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne'
  have hinv_int : ∫ t in (1 : ℝ)..T, (2 : ℝ) / t ^ 2 = 2 - 2 / T := by
    have hd : ∀ t ∈ Set.uIcc (1 : ℝ) T, HasDerivAt (fun u : ℝ => -(2 / u)) (2 / t ^ 2) t := by
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have ht0 : t ≠ 0 := (zero_lt_one.trans_le ht.1).ne'
      exact (((hasDerivAt_inv ht0).const_mul 2).neg.congr_of_eventuallyEq
        (Eventually.of_forall fun u => by simp [div_eq_mul_inv])).congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hinv_cont.intervalIntegrable]
    ring
  have hint_le : |(riemannSiegelTheta T - M T) - (riemannSiegelTheta 1 - M 1)| ≤ 2 := by
    rw [hdiff_eq, ← Real.norm_eq_abs]
    calc ‖∫ t in (1 : ℝ)..T,
            (((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
                (1 / 2 : ℝ) * Real.log Real.pi) - m t)‖
        ≤ ∫ t in (1 : ℝ)..T,
            ‖((1 / 2 : ℝ) * (Complex.digamma ((1 / 4 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re -
                (1 / 2 : ℝ) * Real.log Real.pi) - m t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hT
      _ ≤ ∫ t in (1 : ℝ)..T, (2 : ℝ) / t ^ 2 :=
          intervalIntegral.integral_mono_on hT
            ((continuous_riemannSiegelTheta_integrand.intervalIntegrable 1 T).sub
              hm_cont.intervalIntegrable).norm
            hinv_cont.intervalIntegrable fun t ht => by
              rw [Real.norm_eq_abs]; exact hpt_bd t ht
      _ = 2 - 2 / T := hinv_int
      _ ≤ 2 := by linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (zero_le_one.trans hT)]
  have htri : |riemannSiegelTheta T - M T| ≤
      |(riemannSiegelTheta T - M T) - (riemannSiegelTheta 1 - M 1)| + |riemannSiegelTheta 1 - M 1| := by
    simpa [sub_add_cancel] using abs_add_le
      ((riemannSiegelTheta T - M T) - (riemannSiegelTheta 1 - M 1)) (riemannSiegelTheta 1 - M 1)
  dsimp only [C, M] at htri ⊢
  linarith

/-- Unconditional Riemann–Siegel phase asymptotics in `O(log (T + 2))` and normalized `ϑ(T) / π`
forms. -/
theorem riemannSiegelTheta_stirling_asymptotic :
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      |riemannSiegelTheta T - (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        C * Real.log (T + 2)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      |riemannSiegelTheta T / Real.pi -
        (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤ C) := by
  obtain ⟨C₀, hC₀, hbd⟩ := riemannSiegelTheta_stirling_asymptotic_O1
  constructor
  · refine ⟨C₀ / Real.log 2, div_pos hC₀ (Real.log_pos (by norm_num)), fun T hT => ?_⟩
    have h1 := hbd T (by linarith)
    have hlog_ge : Real.log 2 ≤ Real.log (T + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hC_le : C₀ ≤ (C₀ / Real.log 2) * Real.log (T + 2) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
      exact mul_le_mul_of_nonneg_left hlog_ge hC₀.le
    exact h1.trans hC_le
  · refine ⟨C₀ / Real.pi, div_pos hC₀ Real.pi_pos, fun T hT => ?_⟩
    have hrew : riemannSiegelTheta T / Real.pi -
        (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) =
        (riemannSiegelTheta T - (T / 2) * Real.log (T / (2 * Real.pi * Real.exp 1))) / Real.pi := by
      ring
    rw [hrew, abs_div, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right (hbd T hT) Real.pi_pos.le

/-! ## Section 2: Exact Rectangular Argument Principle & Unconditional Backlund Formula -/

/-- Local logarithmic-derivative expansion at a point where `f z = (z - p)^n * g z` with `g`
analytic and nonvanishing at `p`. -/
private lemma logDeriv_eq_zpow_add_logDeriv_near {f g : ℂ → ℂ} {p : ℂ} {n : ℤ}
    (hg_an : AnalyticAt ℂ g p) (hg_ne : g p ≠ 0)
    (hfeq : ∀ᶠ z in 𝓝[≠] p, f z = (z - p) ^ n • g z) :
    ∀ᶠ z in 𝓝[≠] p, logDeriv f z = (n : ℂ) / (z - p) + logDeriv g z := by
  have h1 : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ g z := hg_an.eventually_analyticAt
  have h2 : ∀ᶠ z in 𝓝 p, g z ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
  rw [eventually_nhdsWithin_iff] at hfeq
  obtain ⟨U, hU_sub, hU_open, hpU⟩ := mem_nhds_iff.mp (hfeq.and (h1.and h2))
  refine eventually_nhdsWithin_iff.mpr ?_
  filter_upwards [hU_open.mem_nhds hpU] with z hzU hzne
  have hsub_ne : z - p ≠ 0 := sub_ne_zero.mpr hzne
  have hopen_z : IsOpen (U \ {p}) := hU_open.sdiff isClosed_singleton
  have hz_mem : z ∈ U \ {p} := ⟨hzU, hzne⟩
  have hfev : f =ᶠ[𝓝 z] fun w : ℂ => (w - p) ^ n * g w := by
    filter_upwards [hopen_z.mem_nhds hz_mem] with w hw
    simpa [smul_eq_mul] using (hU_sub hw.1).1 hw.2
  have hgz_an : AnalyticAt ℂ g z := (hU_sub hzU).2.1
  have hgz_ne : g z ≠ 0 := (hU_sub hzU).2.2
  have hzpow_d : HasDerivAt (fun w : ℂ => (w - p) ^ n) ((n : ℂ) * (z - p) ^ (n - 1)) z := by
    have hlin : HasDerivAt (fun w : ℂ => w - p) 1 z := (hasDerivAt_id z).sub_const p
    have hzpow := (hasDerivAt_zpow n (z - p) (Or.inl hsub_ne)).comp z hlin
    change HasDerivAt ((fun x : ℂ => x ^ n) ∘ fun w : ℂ => w - p) ((n : ℂ) * (z - p) ^ (n - 1)) z
    simpa using hzpow
  have hprod_d := hzpow_d.fun_mul hgz_an.differentiableAt.hasDerivAt
  have hfz_eq : f z = (z - p) ^ n * g z := hfev.self_of_nhds
  rw [logDeriv_apply, logDeriv_apply, hfev.deriv_eq, hprod_d.deriv, hfz_eq]
  have hzpow_ne : (z - p) ^ n ≠ 0 := zpow_ne_zero n hsub_ne
  have hpow_rel : (z - p) ^ (n - 1) = (z - p) ^ n / (z - p) := by
    rw [zpow_sub₀ hsub_ne, zpow_one]
  rw [hpow_rel]
  field_simp [hsub_ne, hzpow_ne, hgz_ne]

/-- **Exact Rectangular Argument-Principle Zero/Pole Counting Theorem (Meromorphic Form)**:
for any meromorphic function `f` on an open neighborhood `U` of `closedRect σ₀ c y₀ y₁` (`σ₀ < c`,
`y₀ < y₁`) with finite zero/pole set `P ⊆ openRect σ₀ c y₀ y₁` of integer orders `k : ℂ → ℤ`,
analytic and nonvanishing on `closedRect σ₀ c y₀ y₁ \ P`,
`(1 / (2 π i)) ∮_{∂R} (f'/f)(s) ds = ∑_{p ∈ P} k(p) = #(zeros) - #(poles)` (counted with
multiplicity), proved directly from `Stage5ContourExplicit.rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part`. -/
theorem rect_argument_principle_meromorphic {f : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hσc : σ₀ < c) (hy : y₀ < y₁)
    (P : Finset ℂ) (k : ℂ → ℤ)
    (hP : ∀ p ∈ P, p ∈ Stage5ContourExplicit.openRect σ₀ c y₀ y₁)
    (hmer : ∀ p ∈ P, MeromorphicAt f p)
    (hord : ∀ p ∈ P, meromorphicOrderAt f p = (k p : WithTop ℤ))
    (hreg : ∀ s ∈ Stage5ContourExplicit.closedRect σ₀ c y₀ y₁, s ∉ P →
      AnalyticAt ℂ f s ∧ f s ≠ 0) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        Stage5ContourExplicit.rectBoundaryIntegral (logDeriv f) σ₀ c y₀ y₁ =
      ∑ p ∈ P, (k p : ℂ) ∧
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        Stage5ContourExplicit.rectBoundaryIntegral (logDeriv f) σ₀ c y₀ y₁ =
      (∑ z ∈ P.filter (fun p => 0 < k p), (k z : ℂ)) -
      (∑ q ∈ P.filter (fun p => k p < 0), ((-k q : ℤ) : ℂ)) := by
  classical
  -- Extract the local nonvanishing analytic factor `g p` at each `p ∈ P`
  have hex : ∀ p : ℂ, ∃ g : ℂ → ℂ,
      p ∈ P → AnalyticAt ℂ g p ∧ g p ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] p, f z = (z - p) ^ (k p) • g z := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff (hmer p hp)).mp (hord p hp)
      exact ⟨g, fun _ => ⟨hg_an, hg_ne, hg_eq⟩⟩
    · exact ⟨fun _ => 1, fun h => (hp h).elim⟩
  choose g hg using hex
  let G : ℂ → ℂ := fun s =>
    if s ∈ P then
      logDeriv (g s) s - ∑ q ∈ P.erase s, (k q : ℂ) / (s - q)
    else
      logDeriv f s - ∑ q ∈ P, (k q : ℂ) / (s - q)
  have hG_diff : DifferentiableOn ℂ G (Stage5ContourExplicit.closedRect σ₀ c y₀ y₁) := by
    intro s hs
    by_cases hsP : s ∈ P
    · -- At `s ∈ P`: `G` agrees on a full neighborhood `𝓝 s` with `logDeriv (g s) w - ∑_{q ≠ s} k q / (w - q)`
      obtain ⟨hgs_an, hgs_ne, hgs_eq⟩ := hg s hsP
      have hld_near := logDeriv_eq_zpow_add_logDeriv_near hgs_an hgs_ne hgs_eq
      have hdisj : ((P.erase s : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 s :=
        (Finset.finite_toSet _).isClosed.isOpen_compl.mem_nhds (by simp)
      rw [eventually_nhdsWithin_iff] at hld_near
      have hev_G : G =ᶠ[𝓝 s] fun w : ℂ =>
          logDeriv (g s) w - ∑ q ∈ P.erase s, (k q : ℂ) / (w - q) := by
        filter_upwards [hld_near, hdisj] with w hw_ld hw_not
        by_cases hws : w = s
        · subst hws; simp [G, hsP]
        · have hwP : w ∉ P := fun hwP' => hw_not (Finset.mem_erase.mpr ⟨hws, hwP'⟩)
          simp only [G, hwP, ↓reduceIte, hw_ld hws]
          rw [← Finset.add_sum_erase P (fun q => (k q : ℂ) / (w - q)) hsP]
          ring
      have hdiff_ld : DifferentiableAt ℂ (logDeriv (g s)) s := by
        have h1 : DifferentiableAt ℂ (deriv (g s)) s := hgs_an.deriv.differentiableAt
        exact h1.div hgs_an.differentiableAt hgs_ne
      have hdiff_sum : DifferentiableAt ℂ (fun w : ℂ => ∑ q ∈ P.erase s, (k q : ℂ) / (w - q)) s := by
        refine DifferentiableAt.fun_sum fun q hq => ?_
        have hne : s - q ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm
        exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hne
      exact ((hdiff_ld.sub hdiff_sum).congr_of_eventuallyEq hev_G).differentiableWithinAt
    · -- Away from `P`: `G` agrees near `s` with `logDeriv f w - ∑_{q ∈ P} k q / (w - q)`
      obtain ⟨hfs_an, hfs_ne⟩ := hreg s hs hsP
      have hdisj : ((P : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 s :=
        (Finset.finite_toSet P).isClosed.isOpen_compl.mem_nhds (by simpa using hsP)
      have hev_G : G =ᶠ[𝓝 s] fun w : ℂ => logDeriv f w - ∑ q ∈ P, (k q : ℂ) / (w - q) := by
        filter_upwards [hdisj] with w hw
        have hwP : w ∉ P := by simpa using hw
        simp [G, hwP]
      have hdiff_ld : DifferentiableAt ℂ (logDeriv f) s :=
        hfs_an.deriv.differentiableAt.div hfs_an.differentiableAt hfs_ne
      have hdiff_sum : DifferentiableAt ℂ (fun w : ℂ => ∑ q ∈ P, (k q : ℂ) / (w - q)) s := by
        refine DifferentiableAt.fun_sum fun q hq => ?_
        have hne : s - q ≠ 0 := sub_ne_zero.mpr fun hEq => hsP (hEq ▸ hq)
        exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hne
      exact ((hdiff_ld.sub hdiff_sum).congr_of_eventuallyEq hev_G).differentiableWithinAt
  have hbdry : ∀ s ∈ Stage5ContourExplicit.closedRect σ₀ c y₀ y₁, (∀ p ∈ P, s ≠ p) →
      logDeriv f s = G s + ∑ p ∈ P, (k p : ℂ) / (s - p) := by
    intro s _ hne
    have hsP : s ∉ P := fun hsP' => hne s hsP' rfl
    simp only [G, hsP, ↓reduceIte]
    ring
  have hrect := Stage5ContourExplicit.rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part
    (logDeriv f) G hσc hy P id (fun p => (k p : ℂ)) hP hG_diff hbdry
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero
  have hmain : (2 * (Real.pi : ℂ) * I)⁻¹ *
      Stage5ContourExplicit.rectBoundaryIntegral (logDeriv f) σ₀ c y₀ y₁ =
      ∑ p ∈ P, (k p : ℂ) := by
    rw [hrect, ← mul_assoc, inv_mul_cancel₀ h2piI, one_mul]
  refine ⟨hmain, ?_⟩
  rw [hmain]
  have hsplit : ∑ p ∈ P, (k p : ℂ) =
      (∑ z ∈ P.filter (fun p => 0 < k p), (k z : ℂ)) +
      (∑ q ∈ P.filter (fun p => ¬ 0 < k p), (k q : ℂ)) :=
    (Finset.sum_filter_add_sum_filter_not P (fun p => 0 < k p) (fun p => (k p : ℂ))).symm
  rw [hsplit]
  have hneg : ∑ q ∈ P.filter (fun p => ¬ 0 < k p), (k q : ℂ) =
      -(∑ q ∈ P.filter (fun p => k p < 0), ((-k q : ℤ) : ℂ)) := by
    have hzero : ∑ q ∈ P.filter (fun p => ¬ 0 < k p), (k q : ℂ) =
        ∑ q ∈ P.filter (fun p => k p < 0), (k q : ℂ) := by
      symm
      refine Finset.sum_subset (fun q hq => ?_) fun q hq hnot => ?_
      · obtain ⟨hqP, hlt⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨hqP, by omega⟩
      · obtain ⟨hqP, hle⟩ := Finset.mem_filter.mp hq
        have hge : ¬ k q < 0 := fun hlt => hnot (Finset.mem_filter.mpr ⟨hqP, hlt⟩)
        have h0 : k q = 0 := by omega
        simp [h0]
    rw [hzero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => by push_cast; ring
  rw [hneg, ← sub_eq_add_neg]

/-- **Exact Rectangular Argument-Principle Zero Counting Theorem (Holomorphic Form)**:
for any function `f` analytic on `closedRect σ₀ c y₀ y₁` (`σ₀ < c`, `y₀ < y₁`) with finite zero set
`Z ⊆ openRect σ₀ c y₀ y₁` (each of finite order) and nonvanishing on `closedRect \ Z`,
`(1 / (2 π i)) ∮_{∂R} (f'/f)(s) ds = ∑_{z ∈ Z} analyticOrderNatAt f z`. -/
theorem rect_argument_principle_holomorphic {f : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hσc : σ₀ < c) (hy : y₀ < y₁)
    (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ Stage5ContourExplicit.openRect σ₀ c y₀ y₁)
    (han : ∀ s ∈ Stage5ContourExplicit.closedRect σ₀ c y₀ y₁, AnalyticAt ℂ f s)
    (hntop : ∀ z ∈ Z, analyticOrderAt f z ≠ ⊤)
    (hnz : ∀ s ∈ Stage5ContourExplicit.closedRect σ₀ c y₀ y₁, s ∉ Z → f s ≠ 0) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        Stage5ContourExplicit.rectBoundaryIntegral (logDeriv f) σ₀ c y₀ y₁ =
      ∑ z ∈ Z, (analyticOrderNatAt f z : ℂ) := by
  have hP_sub : ∀ z ∈ Z, z ∈ Stage5ContourExplicit.closedRect σ₀ c y₀ y₁ := fun z hz => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hZ z hz
    exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
  have hmain := (rect_argument_principle_meromorphic hσc hy Z
    (fun z => (analyticOrderNatAt f z : ℤ)) hZ
    (fun z hz => (han z (hP_sub z hz)).meromorphicAt)
    (fun z hz => by
      rw [(han z (hP_sub z hz)).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt (hntop z hz)]
      rfl)
    (fun s hs hsZ => ⟨han s hs, hnz s hs hsZ⟩)).1
  simpa only [Int.cast_natCast] using hmain

/-- **Unconditional Nonvanishing of `riemannZeta` on the Real Interval `(0, 1)`**:
for every real `σ ∈ (0, 1)`, `(riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) < 0` (hence `riemannZeta σ ≠ 0`),
proved directly from `Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin`. -/
theorem riemannZeta_re_lt_zero_of_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hσ1 : (σ : ℂ) ≠ 1 := fun h => h1.ne (by exact_mod_cast h)
  have hem := Stage5ZetaZeroFree.riemannZeta_sub_pole_eq_eulerMaclaurin (s := (σ : ℂ))
    (by simpa using h0) hσ1
  have hint_real : ∫ t in Set.Ioi (1 : ℝ),
      ((Stage5ZetaZeroFree.fractNat t : ℝ) : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1) =
      ((∫ t in Set.Ioi (1 : ℝ), Stage5ZetaZeroFree.fractNat t * t ^ (-σ - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hpow : (t : ℂ) ^ (-(σ : ℂ) - 1) = ((t ^ (-σ - 1) : ℝ) : ℂ) := by
      have hexp : -(σ : ℂ) - 1 = (((-σ - 1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hexp, Complex.ofReal_cpow ht0.le]
    rw [hpow, ← Complex.ofReal_mul]
  have hint_nn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), Stage5ZetaZeroFree.fractNat t * t ^ (-σ - 1) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    exact mul_nonneg (Stage5ZetaZeroFree.fractNat_nonneg ht0.le) (Real.rpow_nonneg ht0.le _)
  have hre := congrArg Complex.re hem
  rw [hint_real] at hre
  have hpole : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    have hcast : (1 : ℂ) / ((σ : ℂ) - 1) = ((1 / (σ - 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.ofReal_re]
  rw [Complex.sub_re, hpole, Complex.sub_re, Complex.one_re, ← Complex.ofReal_mul,
    Complex.ofReal_re] at hre
  have hfrac : 1 / (σ - 1) + 1 = σ / (σ - 1) := by
    have hne : σ - 1 ≠ 0 := by linarith
    field_simp [hne]; ring
  have hneg : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg h0 (by linarith)
  nlinarith

/-- **Unconditional Nonvanishing of `xi` on the Entire Real Line `ℝ`**:
`xi (σ : ℂ) ≠ 0` for all `σ : ℝ`. -/
theorem xi_ne_zero_of_real (σ : ℝ) : xi (σ : ℂ) ≠ 0 := by
  intro h0
  obtain ⟨hgt0, hlt1, hz⟩ := (xi_eq_zero_iff_critical_strip_zeta_zero (σ : ℂ)).mp h0
  simp only [Complex.ofReal_re] at hgt0 hlt1
  have hre := riemannZeta_re_lt_zero_of_Ioo hgt0 hlt1
  rw [hz, Complex.zero_re] at hre
  exact lt_irrefl 0 hre

/-- Auxiliary conjugation symmetry of the analytic zero order of `xi`:
`analyticOrderNatAt xi (starRingEnd ℂ ρ) = analyticOrderNatAt xi ρ`. -/
lemma analyticOrderNatAt_xi_conj (ρ : ℂ) :
    analyticOrderNatAt xi (starRingEnd ℂ ρ) = analyticOrderNatAt xi ρ := by
  have hxi_an : AnalyticOnNhd ℂ xi Set.univ := differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ
  have hntop : ∀ z : ℂ, analyticOrderAt xi z ≠ ⊤ := fun z htop => by
    have h0 := analyticOrderAt_eq_top.mp htop
    have hxi0 : xi 0 = 0 := hxi_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ 0)
    simp at hxi0
  obtain ⟨g, hg_an, hg_ne, hgeq⟩ := (hxi_an ρ (Set.mem_univ ρ)).analyticOrderAt_ne_top.mp (hntop ρ)
  set m := analyticOrderNatAt xi ρ
  -- Construct `g'(w) = conj (g (conj w))`, analytic near `conj ρ` with `g' (conj ρ) ≠ 0`
  let g' : ℂ → ℂ := fun w => starRingEnd ℂ (g (starRingEnd ℂ w))
  have hg'_an : AnalyticAt ℂ g' (starRingEnd ℂ ρ) := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ g) ρ hg_an
    have hg'_diff : DifferentiableOn ℂ g' (Metric.ball (starRingEnd ℂ ρ) r) := by
      intro w hw
      have hcw : starRingEnd ℂ w ∈ Metric.ball ρ r := by
        rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
        have h1 : starRingEnd ℂ w - ρ = starRingEnd ℂ (w - starRingEnd ℂ ρ) := by simp
        rw [h1, Complex.norm_conj]
        exact hw
      have hd : HasDerivAt g (deriv g (starRingEnd ℂ w)) (starRingEnd ℂ w) :=
        (hball hcw).differentiableAt.hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      have hconj_nhds : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (by simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with h hh
        exact (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hh
      have hcomp : Tendsto (fun t : ℂ =>
          starRingEnd ℂ ((starRingEnd ℂ t)⁻¹ • (g (starRingEnd ℂ w + starRingEnd ℂ t) - g (starRingEnd ℂ w))))
          (𝓝[≠] (0 : ℂ)) (𝓝 (starRingEnd ℂ (deriv g (starRingEnd ℂ w)))) :=
        (Complex.continuous_conj.tendsto _).comp (hd.comp hconj_nhds)
      have hderiv_g' : HasDerivAt g' (starRingEnd ℂ (deriv g (starRingEnd ℂ w))) w := by
        rw [hasDerivAt_iff_tendsto_slope_zero]
        refine hcomp.congr fun t => ?_
        dsimp only [g']
        simp only [smul_eq_mul, map_mul, map_inv₀, map_sub, Complex.conj_conj, ← map_add]
      exact hderiv_g'.differentiableAt.differentiableWithinAt
    exact (hg'_diff.analyticOnNhd Metric.isOpen_ball) (starRingEnd ℂ ρ) (Metric.mem_ball_self hr)
  have hg'_ne : g' (starRingEnd ℂ ρ) ≠ 0 := by
    dsimp only [g']
    rw [Complex.conj_conj]
    exact (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hg_ne
  have hg'_eq : ∀ᶠ w in 𝓝 (starRingEnd ℂ ρ), xi w = (w - starRingEnd ℂ ρ) ^ m • g' w := by
    have hconj_tend : Tendsto (starRingEnd ℂ) (𝓝 (starRingEnd ℂ ρ)) (𝓝 ρ) := by
      simpa using Complex.continuous_conj.tendsto (starRingEnd ℂ ρ)
    filter_upwards [hconj_tend.eventually hgeq] with w hw
    have h1 : xi w = starRingEnd ℂ (xi (starRingEnd ℂ w)) := by
      rw [xi_conj, Complex.conj_conj]
    rw [h1, hw]
    dsimp only [g']
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]
  have hord_eq : analyticOrderAt xi (starRingEnd ℂ ρ) = (m : ENat) :=
    (hxi_an (starRingEnd ℂ ρ) (Set.mem_univ _)).analyticOrderAt_eq_natCast.mpr ⟨g', hg'_an, hg'_ne, hg'_eq⟩
  have hcast : (analyticOrderNatAt xi (starRingEnd ℂ ρ) : ENat) = (m : ENat) := by
    rw [Nat.cast_analyticOrderNatAt (hntop (starRingEnd ℂ ρ)), hord_eq]
  exact Nat.cast_injective hcast

/-- Finite set of critical-strip zeros of `xi` (equivalently `riemannZeta`) with `0 < ρ.im < T`. -/
def xiZeroSetPos (T : ℝ) : Finset ℂ :=
  ((finite_riemannZeta_zeros_le_height T).toFinset).filter fun ρ => 0 < ρ.im ∧ ρ.im < T

/-- **Exact Multiplicity-Weighted Zero Count `N(T)` of `xi` / `riemannZeta` in `(0, 1) × (0, T)`**. -/
def xiZeroCount (T : ℝ) : ℝ :=
  ∑ ρ ∈ xiZeroSetPos T, (analyticOrderNatAt xi ρ : ℝ)

/-- **Exact Continuous Argument Variation `Δ_{C_T} arg ζ(s)` along the Quarter-Contour
`[2, 2 + i T] ∪ [2 + i T, 1/2 + i T]`** (real-analytic integral form). -/
def backlundArgZeta (T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re) -
  (∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im)

/-- **Backlund Remainder Function `S(T) = (1 / π) Δ_{C_T} arg ζ(s)`**. -/
def backlundS (T : ℝ) : ℝ := backlundArgZeta T / Real.pi

/-- Functional-equation and conjugation symmetries of `logDeriv xi`. -/
lemma logDeriv_xi_symm (s : ℂ) :
    logDeriv xi (1 - s) = -logDeriv xi s ∧
    logDeriv xi (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv xi s) := by
  constructor
  · have h1 : HasDerivAt (fun w : ℂ => xi (1 - w)) (deriv xi (1 - s) * (-1)) s := by
      have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
        simpa using (hasDerivAt_const s (1 : ℂ)).fun_sub (hasDerivAt_id s)
      exact (differentiable_xi (1 - s)).hasDerivAt.comp s hsub
    have hEq : (fun w : ℂ => xi (1 - w)) = xi := funext xi_one_sub
    rw [hEq] at h1
    have hd : deriv xi s = -deriv xi (1 - s) := by
      have := h1.deriv; linear_combination this
    rw [logDeriv_apply, logDeriv_apply, xi_one_sub, hd]
    ring
  · have hd : HasDerivAt xi (deriv xi (starRingEnd ℂ s)) (starRingEnd ℂ s) :=
      (differentiable_xi (starRingEnd ℂ s)).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope_zero] at hd
    have hconj_nhds : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact (map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mpr hh
    have hcomp : Tendsto (fun t : ℂ =>
        starRingEnd ℂ ((starRingEnd ℂ t)⁻¹ • (xi (starRingEnd ℂ s + starRingEnd ℂ t) - xi (starRingEnd ℂ s))))
        (𝓝[≠] (0 : ℂ)) (𝓝 (starRingEnd ℂ (deriv xi (starRingEnd ℂ s)))) :=
      (Complex.continuous_conj.tendsto _).comp (hd.comp hconj_nhds)
    have hderiv_eq : HasDerivAt xi (starRingEnd ℂ (deriv xi (starRingEnd ℂ s))) s := by
      rw [hasDerivAt_iff_tendsto_slope_zero]
      refine hcomp.congr fun t => ?_
      simp only [smul_eq_mul, map_mul, map_inv₀, map_sub, ← xi_conj, Complex.conj_conj, ← map_add]
    have hd_conj : deriv xi (starRingEnd ℂ s) = starRingEnd ℂ (deriv xi s) := by
      have := congrArg (starRingEnd ℂ) hderiv_eq.deriv
      simpa using this.symm
    rw [logDeriv_apply, logDeriv_apply, hd_conj, xi_conj, map_div₀]

/-- **Exact Quarter-Contour Argument Principle for `xi` (Unconditional)**:
for every `T > 0` with no zero of `riemannZeta` on `[0, 1] × {T}`,
`xiZeroCount T = (1 / π) * (∫_0^T Re(logDeriv xi (2 + i t)) dt - ∫_{1/2}^2 Im(logDeriv xi (σ + i T)) dσ)`. -/
theorem xiZeroCount_eq_quarter_contour {T : ℝ} (hT : 0 < T)
    (hnz : ∀ σ ∈ Set.Icc (0 : ℝ) 1, riemannZeta ((σ : ℂ) + I * (T : ℂ)) ≠ 0) :
    xiZeroCount T = (1 / Real.pi) *
      ((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re) -
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im)) := by
  classical
  -- Full zero set in `openRect (-1) 2 (-T) T`
  let Z_full : Finset ℂ := ((finite_riemannZeta_zeros_le_height T).toFinset).filter fun ρ => |ρ.im| < T
  have hxi_an : AnalyticOnNhd ℂ xi Set.univ := differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ
  have hntop : ∀ z : ℂ, analyticOrderAt xi z ≠ ⊤ := fun z htop => by
    have h0 := analyticOrderAt_eq_top.mp htop
    have hxi0 : xi 0 = 0 := hxi_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) h0 (Set.mem_univ 0)
    simp at hxi0
  have hZ_rect : ∀ ρ ∈ Z_full, ρ ∈ Stage5ContourExplicit.openRect (-1) 2 (-T) T := by
    intro ρ hρ
    obtain ⟨hρT, hlt⟩ := Finset.mem_filter.mp hρ
    have hmem := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp hρT
    exact ⟨⟨by linarith [hmem.1], by linarith [hmem.2.1]⟩, abs_lt.mp hlt⟩
  have hnz_outside : ∀ s ∈ Stage5ContourExplicit.closedRect (-1) 2 (-T) T, s ∉ Z_full → xi s ≠ 0 := by
    intro s hs hsZ h0
    obtain ⟨h0re, h1re, hz⟩ := (xi_eq_zero_iff_critical_strip_zeta_zero s).mp h0
    have habs : |s.im| ≤ T := abs_le.mpr hs.2
    rcases eq_or_lt_of_le habs with hEq | hlt
    · rcases abs_eq hT.le |>.mp hEq with himT | himNeg
      · have hs_eq : s = (s.re : ℂ) + I * (T : ℂ) := Complex.ext (by simp) (by simp [himT])
        rw [hs_eq] at hz
        exact hnz s.re ⟨h0re.le, h1re.le⟩ hz
      · have hconj0 : riemannZeta (starRingEnd ℂ s) = 0 :=
          (riemannZeta_zero_symm_one_sub h0re h1re hz).2.1
        have hs_eq : starRingEnd ℂ s = (s.re : ℂ) + I * (T : ℂ) :=
          Complex.ext (by simp) (by simp [himNeg])
        rw [hs_eq] at hconj0
        exact hnz s.re ⟨h0re.le, h1re.le⟩ hconj0
    · apply hsZ
      refine Finset.mem_filter.mpr ⟨(finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr
        ⟨h0re, h1re, hz, habs⟩, hlt⟩
  have harg := rect_argument_principle_holomorphic (f := xi) (σ₀ := -1) (c := 2) (y₀ := -T) (y₁ := T)
    (by norm_num) (by linarith) Z_full hZ_rect
    (fun s _ => hxi_an s (Set.mem_univ s)) (fun z _ => hntop z) hnz_outside
  -- Split `Z_full` into positive and negative imaginary parts (no real zeros!)
  have hsum_full : ∑ ρ ∈ Z_full, (analyticOrderNatAt xi ρ : ℝ) = 2 * xiZeroCount T := by
    let Z_neg : Finset ℂ := Z_full.filter fun ρ => ρ.im < 0
    have hZ_pos_eq : Z_full.filter (fun ρ => 0 < ρ.im) = xiZeroSetPos T := by
      ext ρ
      simp only [Z_full, xiZeroSetPos, Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, (abs_lt.mp h2).2⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, abs_lt.mpr ⟨by linarith, h3⟩⟩, h2⟩
    have hnot_eq_neg : Z_full.filter (fun ρ => ¬ 0 < ρ.im) = Z_neg := by
      ext ρ
      simp only [Z_neg, Finset.mem_filter]
      constructor
      · rintro ⟨hρ, hle⟩
        refine ⟨hρ, lt_of_le_of_ne (not_lt.mp hle) fun him0 => ?_⟩
        have hmem := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp (Finset.mem_filter.mp hρ).1
        have hxiρ : xi ρ = 0 := (xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨hmem.1, hmem.2.1, hmem.2.2.1⟩
        have hreal : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him0])
        rw [hreal] at hxiρ
        exact xi_ne_zero_of_real ρ.re hxiρ
      · rintro ⟨hρ, hlt⟩; exact ⟨hρ, not_lt.mpr hlt.le⟩
    have hZ_neg_image : Z_neg = (xiZeroSetPos T).image (starRingEnd ℂ) := by
      ext ρ
      simp only [Z_neg, Z_full, xiZeroSetPos, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hmem := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp h1
        refine ⟨starRingEnd ℂ ρ, ⟨(finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr
          ⟨by simpa using hmem.1, by simpa using hmem.2.1,
            (riemannZeta_zero_symm_one_sub hmem.1 hmem.2.1 hmem.2.2.1).2.1, by simpa using hmem.2.2.2⟩,
          by simp; linarith, by simp; linarith [(abs_lt.mp h2).1]⟩, by simp⟩
      · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
        have hmem := (finite_riemannZeta_zeros_le_height T).mem_toFinset.mp h1
        exact ⟨⟨(finite_riemannZeta_zeros_le_height T).mem_toFinset.mpr
          ⟨by simpa using hmem.1, by simpa using hmem.2.1,
            (riemannZeta_zero_symm_one_sub hmem.1 hmem.2.1 hmem.2.2.1).2.1, by simpa using hmem.2.2.2⟩,
          by simp; rw [abs_of_pos h2]; exact h3⟩, by simp; linarith⟩
    have hneg_sum : ∑ ρ ∈ Z_neg, (analyticOrderNatAt xi ρ : ℝ) = xiZeroCount T := by
      rw [hZ_neg_image, Finset.sum_image (fun a _ b _ h => (starRingEnd ℂ).injective h)]
      unfold xiZeroCount
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [analyticOrderNatAt_xi_conj]
    rw [← Finset.sum_filter_add_sum_filter_not Z_full (fun ρ => 0 < ρ.im), hZ_pos_eq,
      hnot_eq_neg, hneg_sum]
    unfold xiZeroCount; ring
  -- Evaluate `rectBoundaryIntegral (logDeriv xi) (-1) 2 (-T) T` via 4-fold symmetry!
  have hF_symm_bot : ∀ σ : ℝ,
      logDeriv xi ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) = starRingEnd ℂ (logDeriv xi ((σ : ℂ) + (T : ℂ) * I)) := by
    intro σ
    have harg1 : (σ : ℂ) + ((-T : ℝ) : ℂ) * I = starRingEnd ℂ ((σ : ℂ) + (T : ℂ) * I) :=
      Complex.ext (by simp) (by simp)
    rw [harg1, (logDeriv_xi_symm _).2]
  have hF_symm_left : ∀ t : ℝ,
      logDeriv xi (((-1 : ℝ) : ℂ) + (t : ℂ) * I) = -starRingEnd ℂ (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)) := by
    intro t
    have harg1 : ((-1 : ℝ) : ℂ) + (t : ℂ) * I = 1 - starRingEnd ℂ ((2 : ℂ) + (t : ℂ) * I) :=
      Complex.ext (by simp; norm_num) (by simp)
    rw [harg1, (logDeriv_xi_symm _).1, (logDeriv_xi_symm _).2]
  have hF_symm_top_half : ∀ u : ℝ,
      (logDeriv xi (((1 - u : ℝ) : ℂ) + (T : ℂ) * I)).im = (logDeriv xi ((u : ℂ) + (T : ℂ) * I)).im := by
    intro u
    have harg1 : ((1 - u : ℝ) : ℂ) + (T : ℂ) * I = 1 - starRingEnd ℂ ((u : ℂ) + (T : ℂ) * I) :=
      Complex.ext (by simp) (by simp)
    rw [harg1, (logDeriv_xi_symm _).1, (logDeriv_xi_symm _).2]
    simp
  -- Continuity of `logDeriv xi` on the top horizontal and right vertical segments
  have hcont_top : ContinuousOn (fun σ : ℝ => logDeriv xi ((σ : ℂ) + (T : ℂ) * I)) (Set.Icc (-1 : ℝ) 2) := by
    intro σ hσ
    have hmem : ((σ : ℂ) + (T : ℂ) * I) ∈ Stage5ContourExplicit.closedRect (-1) 2 (-T) T :=
      ⟨by simpa using hσ, by simp [hT.le]⟩
    have hnotZ : ((σ : ℂ) + (T : ℂ) * I) ∉ Z_full := fun hz => by
      have := (hZ_rect _ hz).2.2; simp at this
    have hne : xi ((σ : ℂ) + (T : ℂ) * I) ≠ 0 := hnz_outside _ hmem hnotZ
    have hld_cont : ContinuousAt (logDeriv xi) ((σ : ℂ) + (T : ℂ) * I) :=
      ((hxi_an _ (Set.mem_univ _)).deriv.continuousAt).div differentiable_xi.continuous.continuousAt hne
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (T : ℂ) * I) hld_cont (by fun_prop)).continuousWithinAt
  have hcont_right : ContinuousOn (fun t : ℝ => logDeriv xi ((2 : ℂ) + (t : ℂ) * I)) (Set.Icc (-T) T) := by
    intro t ht
    have hne : xi ((2 : ℂ) + (t : ℂ) * I) ≠ 0 := xi_ne_zero_of_one_le_re (by simp)
    have hld_cont : ContinuousAt (logDeriv xi) ((2 : ℂ) + (t : ℂ) * I) :=
      ((hxi_an _ (Set.mem_univ _)).deriv.continuousAt).div differentiable_xi.continuous.continuousAt hne
    exact (ContinuousAt.comp (f := fun y : ℝ => (2 : ℂ) + (y : ℂ) * I) hld_cont (by fun_prop)).continuousWithinAt
  -- Simplify horizontal difference: `∫_{-1}^2 (conj F - F) = -4 * I * ∫_{1/2}^2 Im F`
  have hhoriz :
      (∫ x in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
      (∫ x in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + (T : ℂ) * I)) =
      -4 * I * ((∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im : ℝ) : ℂ) := by
    have hint1 : IntervalIntegrable (fun x : ℝ => logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) volume (-1) 2 := by
      have hEq : (fun x : ℝ => logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) =
          fun x : ℝ => starRingEnd ℂ (logDeriv xi ((x : ℂ) + (T : ℂ) * I)) := funext hF_symm_bot
      rw [hEq]
      exact ((Complex.continuous_conj.comp_continuousOn hcont_top).mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable
    have hint2 : IntervalIntegrable (fun x : ℝ => logDeriv xi ((x : ℂ) + (T : ℂ) * I)) volume (-1) 2 :=
      (hcont_top.mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable
    rw [← intervalIntegral.integral_sub hint1 hint2]
    have hpt : ∀ x : ℝ,
        logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I) - logDeriv xi ((x : ℂ) + (T : ℂ) * I) =
          (-2 * I) * (((logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im : ℝ) : ℂ) := fun x => by
      rw [hF_symm_bot x]
      apply Complex.ext <;> simp
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    have him_cont : ContinuousOn (fun σ : ℝ => (logDeriv xi ((σ : ℂ) + (T : ℂ) * I)).im) (Set.Icc (-1 : ℝ) 2) :=
      Complex.continuous_im.comp_continuousOn hcont_top
    have hint_l : IntervalIntegrable (fun σ : ℝ => (logDeriv xi ((σ : ℂ) + (T : ℂ) * I)).im) volume (-1) (1 / 2) :=
      (him_cont.mono (by rw [Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)).intervalIntegrable
    have hint_r : IntervalIntegrable (fun σ : ℝ => (logDeriv xi ((σ : ℂ) + (T : ℂ) * I)).im) volume (1 / 2) 2 :=
      (him_cont.mono (by rw [Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_l hint_r]
    have hrefl : ∫ σ in (-1 : ℝ)..(1 / 2 : ℝ), (logDeriv xi ((σ : ℂ) + (T : ℂ) * I)).im =
        ∫ u in (1 / 2 : ℝ)..2, (logDeriv xi ((u : ℂ) + (T : ℂ) * I)).im := by
      have h1 := intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im) (1 : ℝ) (a := (1 / 2 : ℝ)) (b := 2)
      norm_num at h1
      rw [← h1]
      exact intervalIntegral.integral_congr fun u _ => by
        simpa only [Complex.ofReal_sub, Complex.ofReal_one] using hF_symm_top_half u
    rw [hrefl]
    have hcomm : ∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + (T : ℂ) * I)).im =
        ∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im :=
      intervalIntegral.integral_congr fun σ _ => by rw [mul_comm I (T : ℂ)]
    rw [hcomm]
    push_cast; ring
  -- Simplify vertical difference: `I * ∫_{-T}^T F(2+it) - I * ∫_{-T}^T F(-1+it) = 4 * I * ∫_0^T Re F(2+it)`
  have hvert :
      I * (∫ t in (-T)..T, logDeriv xi ((2 : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in (-T)..T, logDeriv xi (((-1 : ℝ) : ℂ) + (t : ℂ) * I)) =
      4 * I * ((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re : ℝ) : ℂ) := by
    have hleft_eq : ∫ t in (-T)..T, logDeriv xi (((-1 : ℝ) : ℂ) + (t : ℂ) * I) =
        -(∫ t in (-T)..T, starRingEnd ℂ (logDeriv xi ((2 : ℂ) + (t : ℂ) * I))) := by
      simp_rw [hF_symm_left, intervalIntegral.integral_neg]
    have hint_r : IntervalIntegrable (fun t : ℝ => logDeriv xi ((2 : ℂ) + (t : ℂ) * I)) volume (-T) T :=
      (hcont_right.mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
    have hint_rc : IntervalIntegrable (fun t : ℝ => starRingEnd ℂ (logDeriv xi ((2 : ℂ) + (t : ℂ) * I))) volume (-T) T :=
      ((Complex.continuous_conj.comp_continuousOn hcont_right).mono (by rw [Set.uIcc_of_le (by linarith)])).intervalIntegrable
    rw [hleft_eq, mul_neg, sub_neg_eq_add, ← mul_add, ← intervalIntegral.integral_add hint_r hint_rc]
    have hpt : ∀ t : ℝ,
        logDeriv xi ((2 : ℂ) + (t : ℂ) * I) + starRingEnd ℂ (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)) =
          2 * (((logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re : ℝ) : ℂ) := fun t => by
      apply Complex.ext <;> simp
      ring
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    have hre_cont : ContinuousOn (fun t : ℝ => (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re) (Set.Icc (-T) T) :=
      Complex.continuous_re.comp_continuousOn hcont_right
    have hint_neg : IntervalIntegrable (fun t : ℝ => (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re) volume (-T) 0 :=
      (hre_cont.mono (by rw [Set.uIcc_of_le (by linarith)]; intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)).intervalIntegrable
    have hint_pos : IntervalIntegrable (fun t : ℝ => (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re) volume 0 T :=
      (hre_cont.mono (by rw [Set.uIcc_of_le hT.le]; intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_neg hint_pos]
    have heven : ∫ t in (-T)..(0 : ℝ), (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re =
        ∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re := by
      have h1 := intervalIntegral.integral_comp_neg
        (f := fun t : ℝ => (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re) (a := (0 : ℝ)) (b := T)
      simp only [neg_zero] at h1
      rw [← h1]
      refine intervalIntegral.integral_congr fun t _ => ?_
      have harg1 : (2 : ℂ) + ((-t : ℝ) : ℂ) * I = starRingEnd ℂ ((2 : ℂ) + (t : ℂ) * I) :=
        Complex.ext (by simp) (by simp)
      rw [harg1, (logDeriv_xi_symm _).2, Complex.conj_re]
    rw [heven]
    have hcomm : ∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + (t : ℂ) * I)).re =
        ∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re :=
      intervalIntegral.integral_congr fun t _ => by rw [mul_comm I (t : ℂ)]
    rw [hcomm]
    push_cast; ring
  -- Combine `harg`, `hhoriz`, `hvert`, and `hsum_full`!
  have hbdry_eval : Stage5ContourExplicit.rectBoundaryIntegral (logDeriv xi) (-1) 2 (-T) T =
      4 * I * (((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im) : ℝ) : ℂ) := by
    unfold Stage5ContourExplicit.rectBoundaryIntegral
    simp only [Complex.ofReal_ofNat]
    have hrew : ((∫ x in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          ∫ x in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + (T : ℂ) * I)) +
        I * (∫ y in (-T)..T, logDeriv xi ((2 : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in (-T)..T, logDeriv xi (((-1 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ((∫ x in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
          ∫ x in (-1 : ℝ)..2, logDeriv xi ((x : ℂ) + (T : ℂ) * I)) +
        (I * (∫ y in (-T)..T, logDeriv xi ((2 : ℂ) + (y : ℂ) * I)) -
          I * (∫ y in (-T)..T, logDeriv xi (((-1 : ℝ) : ℂ) + (y : ℂ) * I))) := by ring
    rw [hrew, hhoriz, hvert]
    push_cast; ring
  rw [hbdry_eval] at harg
  have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hLHS : (2 * (Real.pi : ℂ) * I)⁻¹ *
      (4 * I * (((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im) : ℝ) : ℂ)) =
      (((2 / Real.pi) * ((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im)) : ℝ) : ℂ) := by
    push_cast; field_simp [hpiC, Complex.I_ne_zero]; ring
  have hRHS : (∑ z ∈ Z_full, (analyticOrderNatAt xi z : ℂ)) =
      ((∑ z ∈ Z_full, (analyticOrderNatAt xi z : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]; refine Finset.sum_congr rfl fun _ _ => by simp
  rw [hLHS, hRHS, Complex.ofReal_inj, hsum_full] at harg
  have h2eq : (2 / Real.pi) * ((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re) -
      (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im)) =
      2 * ((1 / Real.pi) * ((∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re) -
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im))) := by ring
  linarith

/-- **Exact Quarter-Contour Argument Change of `s (s - 1)`**:
identically equal to `Real.pi` for EVERY `T > 0` (yielding the exact `+ 1` in Backlund's formula!). -/
theorem quarter_contour_arg_s_mul_s_sub_one {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ((((2 : ℂ) + I * (t : ℂ))⁻¹ + ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹)).re) -
    (∫ σ in (1 / 2 : ℝ)..2, ((((σ : ℂ) + I * (T : ℂ))⁻¹ + ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹)).im) =
      Real.pi := by
  -- 1. Vertical segment: `∫_0^T (2 / (4 + t²) + 1 / (1 + t²)) dt = arctan(T / 2) + arctan(T)`
  have hv_pt : ∀ t : ℝ,
      ((((2 : ℂ) + I * (t : ℂ))⁻¹ + ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹)).re =
        2 / (4 + t ^ 2) + 1 / (1 + t ^ 2) := fun t => by
    rw [Complex.add_re, Complex.inv_re, Complex.inv_re]
    have h1 : Complex.normSq ((2 : ℂ) + I * (t : ℂ)) = 4 + t ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    have h2 : Complex.normSq ((2 : ℂ) + I * (t : ℂ) - 1) = 1 + t ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    rw [h1, h2]; simp; norm_num
  have hv_int : ∫ t in (0 : ℝ)..T, (2 / (4 + t ^ 2) + 1 / (1 + t ^ 2)) =
      Real.arctan (T / 2) + Real.arctan T := by
    have hd : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        HasDerivAt (fun u : ℝ => Real.arctan (u / 2) + Real.arctan u)
          (2 / (4 + t ^ 2) + 1 / (1 + t ^ 2)) t := fun t _ => by
      have h1 : HasDerivAt (fun u : ℝ => Real.arctan (u / 2)) (2 / (4 + t ^ 2)) t := by
        have hlin : HasDerivAt (fun u : ℝ => u / 2) (1 / 2 : ℝ) t := by
          simpa using (hasDerivAt_id t).div_const 2
        refine hlin.arctan.congr_deriv ?_
        have hpos : 0 < 4 + t ^ 2 := by positivity
        field_simp [hpos.ne']; ring
      have h2 : HasDerivAt Real.arctan (1 / (1 + t ^ 2)) t := by
        simpa [one_div] using Real.hasDerivAt_arctan t
      exact h1.add h2
    have hcont : Continuous (fun t : ℝ => 2 / (4 + t ^ 2) + 1 / (1 + t ^ 2)) :=
      (continuous_const.div (by fun_prop : Continuous fun t : ℝ => 4 + t ^ 2)
          fun t => (by positivity : 0 < 4 + t ^ 2).ne').add
        (continuous_const.div (by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2)
          fun t => (by positivity : 0 < 1 + t ^ 2).ne')
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    simp
  -- 2. Horizontal segment: `-∫_{1/2}^2 (-T / (σ² + T²) - T / ((σ - 1)² + T²)) dσ`
  --    `= arctan(2 / T) + arctan(1 / T)` (with `arctan(1 / (2 T))` cancelling identically!)
  have hh_pt : ∀ σ : ℝ,
      ((((σ : ℂ) + I * (T : ℂ))⁻¹ + ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹)).im =
        -(T / (σ ^ 2 + T ^ 2) + T / ((σ - 1) ^ 2 + T ^ 2)) := fun σ => by
    rw [Complex.add_im, Complex.inv_im, Complex.inv_im]
    have h1 : Complex.normSq ((σ : ℂ) + I * (T : ℂ)) = σ ^ 2 + T ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    have h2 : Complex.normSq ((σ : ℂ) + I * (T : ℂ) - 1) = (σ - 1) ^ 2 + T ^ 2 := by
      rw [Complex.normSq_apply]; simp; ring
    rw [h1, h2]; simp; ring
  have hh_int : ∫ σ in (1 / 2 : ℝ)..2, (T / (σ ^ 2 + T ^ 2) + T / ((σ - 1) ^ 2 + T ^ 2)) =
      Real.arctan (2 / T) + Real.arctan (1 / T) := by
    have hd : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        HasDerivAt (fun u : ℝ => Real.arctan (u / T) + Real.arctan ((u - 1) / T))
          (T / (σ ^ 2 + T ^ 2) + T / ((σ - 1) ^ 2 + T ^ 2)) σ := fun σ _ => by
      have h1 : HasDerivAt (fun u : ℝ => Real.arctan (u / T)) (T / (σ ^ 2 + T ^ 2)) σ := by
        have hlin : HasDerivAt (fun u : ℝ => u / T) (1 / T) σ := by
          simpa using (hasDerivAt_id σ).div_const T
        refine hlin.arctan.congr_deriv ?_
        have hpos : 0 < σ ^ 2 + T ^ 2 := by positivity
        field_simp [hT.ne', hpos.ne']; ring
      have h2 : HasDerivAt (fun u : ℝ => Real.arctan ((u - 1) / T)) (T / ((σ - 1) ^ 2 + T ^ 2)) σ := by
        have hlin : HasDerivAt (fun u : ℝ => (u - 1) / T) (1 / T) σ := by
          simpa using ((hasDerivAt_id σ).sub_const 1).div_const T
        refine hlin.arctan.congr_deriv ?_
        have hpos : 0 < (σ - 1) ^ 2 + T ^ 2 := by positivity
        field_simp [hT.ne', hpos.ne']; ring
      exact h1.add h2
    have hcont : Continuous (fun σ : ℝ => T / (σ ^ 2 + T ^ 2) + T / ((σ - 1) ^ 2 + T ^ 2)) :=
      (continuous_const.div (by fun_prop) fun σ => (by positivity : 0 < σ ^ 2 + T ^ 2).ne').add
        (continuous_const.div (by fun_prop) fun σ => (by positivity : 0 < (σ - 1) ^ 2 + T ^ 2).ne')
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    have hsub1 : ((2 : ℝ) - 1) / T = 1 / T := by ring
    have hsub2 : ((1 / 2 : ℝ) - 1) / T = -((1 / 2 : ℝ) / T) := by ring
    rw [hsub1, hsub2, Real.arctan_neg]
    ring
  simp_rw [hv_pt, hh_pt]
  rw [hv_int, intervalIntegral.integral_neg, sub_neg_eq_add, hh_int]
  have hpi1 : Real.arctan (T / 2) + Real.arctan (2 / T) = Real.pi / 2 := by
    have h := Real.arctan_inv_of_pos (by positivity : 0 < T / 2)
    rw [inv_div] at h
    linarith
  have hpi2 : Real.arctan T + Real.arctan (1 / T) = Real.pi / 2 := by
    have h := Real.arctan_inv_of_pos hT
    rw [one_div]
    linarith
  linarith

/-- **Exact Quarter-Contour Argument Change of `Complex.Gammaℝ`**:
identically equal to `riemannSiegelTheta T` for EVERY `T > 0` by Cauchy's rectangle theorem on
`[1/2, 2] × [0, T]`! -/
theorem quarter_contour_arg_Gammaℝ {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re) -
    (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Complex.Gammaℝ ((σ : ℂ) + I * (T : ℂ))).im) =
      riemannSiegelTheta T := by
  -- `logDeriv Complex.Gammaℝ` is holomorphic on `closedRect (1/2) 2 0 T`
  have hdiff : DifferentiableOn ℂ (logDeriv Complex.Gammaℝ)
      (Stage5ContourExplicit.closedRect (1 / 2) 2 0 T) := by
    intro s hs
    have hs_pos : 0 < s.re := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hs.1.1
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : logDeriv Complex.Gammaℝ =ᶠ[𝓝 s]
        fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (w / 2) := by
      filter_upwards [hopen.mem_nhds hs_pos] with w hw using logDeriv_Gammaℝ_eq hw
    have hdig_d : DifferentiableAt ℂ (fun w : ℂ => Complex.digamma (w / 2)) s := by
      have h1 : DifferentiableAt ℂ Complex.digamma (s / 2) :=
        (differentiableOn_digamma_re_pos (s / 2) (by simp; linarith)).differentiableAt
          (hopen.mem_nhds (by simp; linarith))
      exact h1.comp s (differentiableAt_id.div_const (2 : ℂ))
    have hd : DifferentiableAt ℂ
        (fun w : ℂ => -((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (w / 2)) s :=
      (differentiableAt_const _).add ((differentiableAt_const _).mul hdig_d)
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  have hcauchy := Stage5ContourExplicit.rectBoundaryIntegral_eq_zero_of_differentiableOn
    (by norm_num : (1 / 2 : ℝ) ≤ 2) hT.le hdiff
  have him := congrArg Complex.im hcauchy
  unfold Stage5ContourExplicit.rectBoundaryIntegral at him
  -- Helper: `(∫ f).im = ∫ (f ·).im` and `(I * ∫ f).im = ∫ (f ·).re`
  have hcont := hdiff.continuousOn
  have hint_bot : IntervalIntegrable (fun x : ℝ => logDeriv Complex.Gammaℝ ((x : ℂ) + ((0 : ℝ) : ℂ) * I))
      volume (1 / 2) 2 :=
    (hcont.comp (by fun_prop) fun x hx => by
      rw [Set.uIcc_of_le (by norm_num)] at hx; exact ⟨by simpa using hx, by simp [hT.le]⟩).intervalIntegrable
  have hint_top : IntervalIntegrable (fun x : ℝ => logDeriv Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * I))
      volume (1 / 2) 2 :=
    (hcont.comp (by fun_prop) fun x hx => by
      rw [Set.uIcc_of_le (by norm_num)] at hx; exact ⟨by simpa using hx, by simp [hT.le]⟩).intervalIntegrable
  have hint_r : IntervalIntegrable (fun y : ℝ => logDeriv Complex.Gammaℝ ((2 : ℂ) + (y : ℂ) * I))
      volume 0 T :=
    (hcont.comp (by fun_prop) fun y hy => by
      rw [Set.uIcc_of_le hT.le] at hy; exact ⟨by simp; norm_num, by simpa using hy⟩).intervalIntegrable
  have hint_l : IntervalIntegrable (fun y : ℝ => logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I))
      volume 0 T :=
    (hcont.comp (by fun_prop) fun y hy => by
      rw [Set.uIcc_of_le hT.le] at hy; exact ⟨by simp; norm_num, by simpa using hy⟩).intervalIntegrable
  have hbot_im : (∫ x in (1 / 2 : ℝ)..2, logDeriv Complex.Gammaℝ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 := by
    have h1 := Complex.imCLM.intervalIntegral_comp_comm hint_bot
    simp only [Complex.imCLM_apply] at h1
    rw [← h1]
    have hzero : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (logDeriv Complex.Gammaℝ ((x : ℂ) + ((0 : ℝ) : ℂ) * I)).im = 0 := by
      intro x hx
      rw [Set.uIcc_of_le (by norm_num)] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rw [logDeriv_Gammaℝ_eq (by simpa using hx0)]
      have hdiv : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [hdiv, Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im]
      simp only [neg_zero, zero_add, Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im,
        Complex.one_im, zero_div, zero_mul, add_zero]
      rw [im_digamma_ofReal_eq_zero (by positivity : 0 < x / 2), mul_zero]
    rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]
  have htop_im : (∫ x in (1 / 2 : ℝ)..2, logDeriv Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * I)).im =
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv Complex.Gammaℝ ((σ : ℂ) + I * (T : ℂ))).im := by
    have h1 := Complex.imCLM.intervalIntegral_comp_comm hint_top
    simp only [Complex.imCLM_apply] at h1
    rw [← h1]
    exact intervalIntegral.integral_congr fun σ _ => by rw [mul_comm I (T : ℂ)]
  have hr_re : (∫ y in (0 : ℝ)..T, logDeriv Complex.Gammaℝ ((2 : ℂ) + (y : ℂ) * I)).re =
      ∫ t in (0 : ℝ)..T, (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re := by
    have h1 := Complex.reCLM.intervalIntegral_comp_comm hint_r
    simp only [Complex.reCLM_apply] at h1
    rw [← h1]
    exact intervalIntegral.integral_congr fun t _ => by rw [mul_comm I (t : ℂ)]
  have hl_re : (∫ y in (0 : ℝ)..T, logDeriv Complex.Gammaℝ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)).re =
      riemannSiegelTheta T := by
    have h1 := Complex.reCLM.intervalIntegral_comp_comm hint_l
    simp only [Complex.reCLM_apply] at h1
    rw [← h1, riemannSiegelTheta_eq_integral_re_logDeriv_Gammaℝ]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
    rw [hcast, mul_comm I (t : ℂ)]
  simp only [Complex.ofReal_ofNat, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im, hbot_im, htop_im, hr_re, hl_re] at him
  linarith

/-- Pointwise decomposition of `logDeriv xi s` into `1 / s + 1 / (s - 1) + logDeriv Gammaℝ s + logDeriv ζ s`
for every `s` with `0 < s.re`, `s ≠ 1`, and `riemannZeta s ≠ 0`. -/
lemma logDeriv_xi_decomp {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hnz : riemannZeta s ≠ 0) :
    logDeriv xi s = (s⁻¹ + (s - 1)⁻¹) + logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl 0 hs
  have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG_ne : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  have hopen : IsOpen ({w : ℂ | 0 < w.re} \ {(1 : ℂ)}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hev : xi =ᶠ[𝓝 s] fun w : ℂ => w * (w - 1) * w.Gammaℝ * riemannZeta w := by
    filter_upwards [hopen.mem_nhds ⟨hs, hs1⟩] with w hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw; exact lt_irrefl 0 (by simpa using hw.1)
    exact xi_eq_mul_Gammaℝ_mul_riemannZeta hw0 hw.2 (Complex.Gammaℝ_ne_zero_of_re_pos hw.1)
  have hG_diff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have hfun : Complex.Gammaℝ = fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) :=
      funext Complex.Gammaℝ_def
    rw [hfun]
    have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) s := by
      have hEq : (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) =
          fun w : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-w / 2)) :=
        funext fun w => Complex.cpow_def_of_ne_zero hpiC _
      rw [hEq]; fun_prop
    have hGam : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s := by
      have h1 : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
        Complex.differentiableAt_Gamma (s / 2) fun m hEq => by
          have hre := congrArg Complex.re hEq
          simp only [Complex.neg_re, Complex.natCast_re] at hre
          have : 0 < (s / 2).re := by simp; linarith
          linarith [Nat.cast_nonneg (α := ℝ) m]
      exact h1.comp s (differentiableAt_id.div_const (2 : ℂ))
    exact hpow.mul hGam
  have hZ_diff : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hpoly_d : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hfull_d := ((hpoly_d.fun_mul hG_diff.hasDerivAt).fun_mul hZ_diff.hasDerivAt)
  rw [logDeriv_apply, logDeriv_apply, logDeriv_apply, hev.deriv_eq, hfull_d.deriv, hev.self_of_nhds]
  field_simp [hs0, hsub_ne, hG_ne, hnz]

/-- **EXACT UNCONDITIONAL BACKLUND ZERO-COUNT FORMULA ON MATHLIB'S `riemannZeta`**:
for every `T > 0` with no critical-strip zero on `Im(s) = T`:
`xiZeroCount T = riemannSiegelTheta T / π + 1 + backlundS T`! -/
theorem backlund_exact_formula {T : ℝ} (hT : 0 < T)
    (hnz : ∀ σ ∈ Set.Icc (0 : ℝ) 1, riemannZeta ((σ : ℂ) + I * (T : ℂ)) ≠ 0) :
    xiZeroCount T = riemannSiegelTheta T / Real.pi + 1 + backlundS T := by
  -- Continuity of the three decomposed pieces along `[2, 2 + i T]` and `[1/2 + i T, 2 + i T]`
  have hZ_nz_right : ∀ t : ℝ, riemannZeta ((2 : ℂ) + I * (t : ℂ)) ≠ 0 := fun t =>
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hZ_nz_top : ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 2, riemannZeta ((σ : ℂ) + I * (T : ℂ)) ≠ 0 := by
    intro σ hσ
    rcases lt_or_ge σ 1 with hlt | hge
    · exact hnz σ ⟨by linarith [hσ.1], hlt.le⟩
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hge)
  have hG_cont_r : ContinuousOn (fun t : ℝ => (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re)
      (Set.uIcc 0 T) := by
    have hEq : (fun t : ℝ => (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re) =
        fun t : ℝ => -(Real.log Real.pi / 2) + (1 / 2) * (Complex.digamma ((1 : ℂ) + I * ((t / 2 : ℝ) : ℂ))).re := by
      funext t
      rw [logDeriv_Gammaℝ_eq (by simp)]
      have hdiv : ((2 : ℂ) + I * (t : ℂ)) / 2 = (1 : ℂ) + I * ((t / 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp
      rw [hdiv]
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
        Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im, zero_div,
        zero_mul, sub_zero]
    rw [hEq]
    refine (continuous_const.add (continuous_const.mul (Complex.continuous_re.comp
      (differentiableOn_digamma_re_pos.continuousOn.comp_continuous (by fun_prop) fun t => by
        change 0 < ((1 : ℂ) + I * ((t / 2 : ℝ) : ℂ)).re; simp)))).continuousOn
  have hG_cont_t : ContinuousOn (fun σ : ℝ => (logDeriv Complex.Gammaℝ ((σ : ℂ) + I * (T : ℂ))).im)
      (Set.uIcc (1 / 2) 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    have hdig : ContinuousOn (fun σ : ℝ => Complex.digamma (((σ : ℂ) + I * (T : ℂ)) / 2)) (Set.Icc (1 / 2) 2) :=
      differentiableOn_digamma_re_pos.continuousOn.comp (by fun_prop) fun σ hσ => by
        change 0 < (((σ : ℂ) + I * (T : ℂ)) / 2).re; simp; linarith [hσ.1]
    have hcont : ContinuousOn (fun σ : ℝ => (-(Real.log Real.pi / 2 : ℝ) : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (((σ : ℂ) + I * (T : ℂ)) / 2)) (Set.Icc (1 / 2) 2) :=
      continuousOn_const.add (continuousOn_const.mul hdig)
    refine (Complex.continuous_im.comp_continuousOn hcont).congr fun σ hσ => ?_
    dsimp only [Function.comp_apply]
    rw [logDeriv_Gammaℝ_eq (by simp; linarith [hσ.1])]
  have hP_cont_r : Continuous (fun t : ℝ =>
      (((2 : ℂ) + I * (t : ℂ))⁻¹ + ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹).re) := by
    have h1 : Continuous (fun t : ℝ => ((2 : ℂ) + I * (t : ℂ))⁻¹) :=
      Continuous.inv₀ (by fun_prop) fun t h0 => by have := congrArg Complex.re h0; simp at this
    have h2 : Continuous (fun t : ℝ => ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹) :=
      Continuous.inv₀ (by fun_prop) fun t h0 => by
        have := congrArg Complex.re h0; simp at this; norm_num at this
    exact Complex.continuous_re.comp (h1.add h2)
  have hP_cont_t : Continuous (fun σ : ℝ =>
      (((σ : ℂ) + I * (T : ℂ))⁻¹ + ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹).im) := by
    have h1 : Continuous (fun σ : ℝ => ((σ : ℂ) + I * (T : ℂ))⁻¹) :=
      Continuous.inv₀ (by fun_prop) fun σ h0 => by have := congrArg Complex.im h0; simp at this; linarith
    have h2 : Continuous (fun σ : ℝ => ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹) :=
      Continuous.inv₀ (by fun_prop) fun σ h0 => by have := congrArg Complex.im h0; simp at this; linarith
    exact Complex.continuous_im.comp (h1.add h2)
  have hZ_an_all : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z (hz : z ≠ (1 : ℂ)) => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_compl_singleton
  have hZ_cont_r : ContinuousOn (fun t : ℝ => (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re)
      (Set.uIcc 0 T) := by
    refine Complex.continuous_re.comp_continuousOn fun t _ => ?_
    have hne1 : ((2 : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this
    have hZ_an : AnalyticAt ℂ riemannZeta ((2 : ℂ) + I * (t : ℂ)) := hZ_an_all _ hne1
    have hld : ContinuousAt (logDeriv riemannZeta) ((2 : ℂ) + I * (t : ℂ)) :=
      hZ_an.deriv.continuousAt.div hZ_an.continuousAt (hZ_nz_right t)
    exact (ContinuousAt.comp (f := fun y : ℝ => (2 : ℂ) + I * (y : ℂ)) hld (by fun_prop)).continuousWithinAt
  have hZ_cont_t : ContinuousOn (fun σ : ℝ => (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im)
      (Set.uIcc (1 / 2) 2) := by
    rw [Set.uIcc_of_le (by norm_num)]
    refine Complex.continuous_im.comp_continuousOn fun σ hσ => ?_
    have hne1 : ((σ : ℂ) + I * (T : ℂ)) ≠ 1 := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hZ_an : AnalyticAt ℂ riemannZeta ((σ : ℂ) + I * (T : ℂ)) := hZ_an_all _ hne1
    have hld : ContinuousAt (logDeriv riemannZeta) ((σ : ℂ) + I * (T : ℂ)) :=
      hZ_an.deriv.continuousAt.div hZ_an.continuousAt (hZ_nz_top σ hσ)
    exact (ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + I * (T : ℂ)) hld (by fun_prop)).continuousWithinAt
  -- Decompose vertical and horizontal integrals
  have hv_split :
      ∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re =
        (∫ t in (0 : ℝ)..T, ((((2 : ℂ) + I * (t : ℂ))⁻¹ + ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹)).re) +
        (∫ t in (0 : ℝ)..T, (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re) +
        (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re) := by
    have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) T,
        (logDeriv xi ((2 : ℂ) + I * (t : ℂ))).re =
          ((((2 : ℂ) + I * (t : ℂ))⁻¹ + ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹)).re +
          (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re +
          (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re := fun t _ => by
      have hne1 : ((2 : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this
      rw [logDeriv_xi_decomp (by simp) hne1 (hZ_nz_right t), Complex.add_re, Complex.add_re]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add
        ((hP_cont_r.intervalIntegrable (μ := volume) 0 T).add (hG_cont_r.intervalIntegrable (μ := volume)))
        (hZ_cont_r.intervalIntegrable (μ := volume)),
      intervalIntegral.integral_add (hP_cont_r.intervalIntegrable (μ := volume) 0 T)
        (hG_cont_r.intervalIntegrable (μ := volume))]
  have hh_split :
      ∫ σ in (1 / 2 : ℝ)..2, (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im =
        (∫ σ in (1 / 2 : ℝ)..2, ((((σ : ℂ) + I * (T : ℂ))⁻¹ + ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹)).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Complex.Gammaℝ ((σ : ℂ) + I * (T : ℂ))).im) +
        (∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im) := by
    have hcongr : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
        (logDeriv xi ((σ : ℂ) + I * (T : ℂ))).im =
          ((((σ : ℂ) + I * (T : ℂ))⁻¹ + ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹)).im +
          (logDeriv Complex.Gammaℝ ((σ : ℂ) + I * (T : ℂ))).im +
          (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im := fun σ hσ => by
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      have hne1 : ((σ : ℂ) + I * (T : ℂ)) ≠ 1 := fun h => by
        have := congrArg Complex.im h; simp at this; linarith
      rw [logDeriv_xi_decomp (by simp; linarith [hσ.1]) hne1 (hZ_nz_top σ hσ),
        Complex.add_im, Complex.add_im]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_add
        ((hP_cont_t.intervalIntegrable (μ := volume) (1 / 2) 2).add (hG_cont_t.intervalIntegrable (μ := volume)))
        (hZ_cont_t.intervalIntegrable (μ := volume)),
      intervalIntegral.integral_add (hP_cont_t.intervalIntegrable (μ := volume) (1 / 2) 2)
        (hG_cont_t.intervalIntegrable (μ := volume))]
  rw [xiZeroCount_eq_quarter_contour hT hnz, hv_split, hh_split]
  have h1 := quarter_contour_arg_s_mul_s_sub_one hT
  have h2 := quarter_contour_arg_Gammaℝ hT
  unfold backlundS backlundArgZeta
  have hcomb :
      ((∫ t in (0 : ℝ)..T, ((((2 : ℂ) + I * (t : ℂ))⁻¹ + ((2 : ℂ) + I * (t : ℂ) - 1)⁻¹)).re) +
       (∫ t in (0 : ℝ)..T, (logDeriv Complex.Gammaℝ ((2 : ℂ) + I * (t : ℂ))).re) +
       (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re)) -
      ((∫ σ in (1 / 2 : ℝ)..2, ((((σ : ℂ) + I * (T : ℂ))⁻¹ + ((σ : ℂ) + I * (T : ℂ) - 1)⁻¹)).im) +
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv Complex.Gammaℝ ((σ : ℂ) + I * (T : ℂ))).im) +
       (∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im)) =
      Real.pi + riemannSiegelTheta T +
        ((∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((2 : ℂ) + I * (t : ℂ))).re) -
         (∫ σ in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((σ : ℂ) + I * (T : ℂ))).im)) := by
    linarith
  rw [hcomb]
  field_simp [Real.pi_pos.ne']
  ring

/-- **UNCONDITIONAL BACKLUND RIEMANN–VON MANGOLDT ASYMPTOTIC ZERO-COUNT BOUND**:
combining `backlund_exact_formula` with the sharp `O(1)` Stirling phase asymptotic
`riemannSiegelTheta_stirling_asymptotic_O1`, unconditionally:
1. Sharp `O(1) + |S(T)|` form for all `T ≥ 1`:
   `|xiZeroCount T - (T / (2 π)) log (T / (2 π e))| ≤ C + |backlundS T|`,
2. Standard `O(log T + |S(T)|)` form for all `T ≥ 2`:
   `|xiZeroCount T - (T / (2 π)) log (T / (2 π e))| ≤ C' * (Real.log T + |backlundS T|)`. -/
theorem backlund_riemann_von_mangoldt_bound :
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, riemannZeta ((σ : ℂ) + I * (T : ℂ)) ≠ 0) →
      |xiZeroCount T - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        C + |backlundS T|) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, riemannZeta ((σ : ℂ) + I * (T : ℂ)) ≠ 0) →
      |xiZeroCount T - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        C * (Real.log T + |backlundS T|)) := by
  obtain ⟨C₀, hC₀, hth⟩ := riemannSiegelTheta_stirling_asymptotic.2
  have hsharp : ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∀ σ ∈ Set.Icc (0 : ℝ) 1, riemannZeta ((σ : ℂ) + I * (T : ℂ)) ≠ 0) →
      |xiZeroCount T - (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| ≤
        C + |backlundS T| := by
    refine ⟨C₀ + 1, by linarith, fun T hT hnz => ?_⟩
    rw [backlund_exact_formula (by linarith) hnz]
    have hrew : riemannSiegelTheta T / Real.pi + 1 + backlundS T -
        (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) =
        (riemannSiegelTheta T / Real.pi -
          (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))) + (1 + backlundS T) := by
      ring
    rw [hrew]
    calc |(riemannSiegelTheta T / Real.pi -
            (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))) + (1 + backlundS T)|
        ≤ |riemannSiegelTheta T / Real.pi -
            (T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1))| + |1 + backlundS T| :=
          abs_add_le _ _
      _ ≤ C₀ + (1 + |backlundS T|) := by
          have h1 := hth T hT
          have h2 : |1 + backlundS T| ≤ 1 + |backlundS T| := by
            simpa using abs_add_le (1 : ℝ) (backlundS T)
          linarith
      _ = (C₀ + 1) + |backlundS T| := by ring
  refine ⟨hsharp, ?_⟩
  obtain ⟨C₁, hC₁, hbd⟩ := hsharp
  refine ⟨max (2 * C₁) 1, by positivity, fun T hT hnz => ?_⟩
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT : (1 / 2 : ℝ) ≤ Real.log T := hlog2.trans (Real.log_le_log (by norm_num) hT)
  have h1 := hbd T (by linarith) hnz
  have hC_ge1 : 1 ≤ max (2 * C₁) 1 := le_max_right _ _
  have hC_ge2 : 2 * C₁ ≤ max (2 * C₁) 1 := le_max_left _ _
  have hterm1 : C₁ ≤ max (2 * C₁) 1 * Real.log T := by nlinarith
  have hterm2 : |backlundS T| ≤ max (2 * C₁) 1 * |backlundS T| :=
    le_mul_of_one_le_left (abs_nonneg _) hC_ge1
  linarith

/-! ## Section 3: Unconditional Sharp Bidirectional Equivalence: Zero-Free Half-Plane `Re(s) > θ`
↔ `Chebyshev.psi x - x = O(x^{θ + ε})` ↔ `Chebyshev.theta x - x = O(x^{θ + ε})` ↔ `RiemannHypothesis` -/

/-- **Unconditional Borel–Carathéodory Log-Derivative Bound in Any Zero-Free Half-Plane**:
if `0 < θ < 1`, `0 < δ`, `θ + δ < 1`, and `riemannZeta` has no zeros on `Re(s) > θ` (`s ≠ 1`),
then there exists `C > 0` such that:
1. `‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (|s.im| + 2)` for all `θ + δ ≤ s.re ≤ 3`
   and `4 ≤ |s.im|`, and
2. `zetaReg s ≠ 0 ∧ ‖negLogDerivZetaReg s‖ ≤ C` on the compact rectangle `[θ + δ, 3] × [-4, 4]`. -/
theorem negLogDerivZeta_bound_of_zeroFree_halfPlane {θ δ : ℝ}
    (hθ0 : 0 < θ) (hδ0 : 0 < δ) (hθδ : θ + δ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ s : ℂ, θ + δ ≤ s.re → s.re ≤ 3 → 4 ≤ |s.im| →
        ‖-deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log (|s.im| + 2)) ∧
      (∀ s : ℂ, θ + δ ≤ s.re → s.re ≤ 3 → |s.im| ≤ 4 →
        zetaReg s ≠ 0 ∧ ‖negLogDerivZetaReg s‖ ≤ C) := by
  -- Part A: Compact box `[θ + δ, 3] × [-4, 4]` via `zetaReg` / `negLogDerivZetaReg`
  set K : Set ℂ := {z : ℂ | θ + δ ≤ z.re ∧ z.re ≤ 3 ∧ |z.im| ≤ 4}
  have hK_comp : IsCompact K := by
    have hsub : K = Complex.equivRealProdCLM.symm '' (Set.Icc (θ + δ) 3 ×ˢ Set.Icc (-4 : ℝ) 4) := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, Complex.ext (by simp) (by simp)⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hsub]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hK_sub : K ⊆ {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
    intro z hz
    have hz_pos : 0 < z.re := by linarith [hz.1]
    refine ⟨hz_pos, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [zetaReg_one]; exact one_ne_zero
    · rw [zetaReg_eq_mul_riemannZeta hz_pos hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (hzf z (by linarith [hz.1]) hz1)
  obtain ⟨M_box, hM_box⟩ :=
    hK_comp.exists_bound_of_continuousOn ((differentiableOn_negLogDerivZetaReg.mono hK_sub).continuousOn)
  -- Part B: Tall strip `θ + δ ≤ s.re ≤ 3`, `4 ≤ |s.im|` via Borel–Carathéodory centered at `s₀ = 3 + i t`
  set R_open : ℝ := 3 - θ - δ / 4
  set R : ℝ := 3 - θ - δ / 2
  set r : ℝ := 3 - θ - δ
  have hR_open_pos : 0 < R_open := by dsimp only [R_open]; linarith
  have hR_pos : 0 < R := by dsimp only [R]; linarith
  have hrR : r < R := by dsimp only [r, R]; linarith
  have hR_open_lt3 : R_open < 3 := by dsimp only [R_open]; linarith
  set A_zeta : ℝ := 2 * (3 + 12 / (θ + δ / 2))
  have hA_ge2 : 2 ≤ A_zeta := by
    dsimp only [A_zeta]
    have : 0 < 12 / (θ + δ / 2) := by positivity
    linarith
  set C_M : ℝ := Real.log A_zeta + 1
  have hCM_pos : 0 < C_M := by
    have : 0 < Real.log A_zeta := Real.log_pos (by linarith)
    linarith
  set C_tall : ℝ := (2 * R / (R - r) ^ 2) * C_M
  have hC_tall_pos : 0 < C_tall := by
    have : 0 < R - r := by dsimp only [R, r]; linarith
    positivity
  set C : ℝ := max (max M_box 1) C_tall
  have hC_pos : 0 < C := lt_of_lt_of_le hC_tall_pos (le_max_right _ _)
  refine ⟨C, hC_pos, fun s hre_lo hre_hi him => ?_, fun s hre_lo hre_hi him => ?_⟩
  · -- Tall strip case: `4 ≤ |s.im|`
    set t : ℝ := s.im
    set s₀ : ℂ := (3 : ℂ) + I * (t : ℂ)
    have hs₀_re : s₀.re = 3 := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    have hball_ne1 : ∀ z ∈ Metric.ball s₀ R_open, z ≠ 1 := by
      intro z hz h1
      subst h1
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h1 := (Complex.abs_im_le_norm ((1 : ℂ) - s₀)).trans_lt hz
      rw [Complex.sub_im, Complex.one_im, hs₀_im, zero_sub, abs_neg] at h1
      linarith
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, riemannZeta z ≠ 0 := by
      intro z hz
      have hz1 : z ≠ 1 := hball_ne1 z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)).1
      rw [Complex.sub_re, hs₀_re] at hre
      have hz_re : θ < z.re := by dsimp only [R_open] at hre; linarith
      exact hzf z hz_re hz1
    have hball_diff : DifferentiableOn ℂ riemannZeta (Metric.ball s₀ R_open) := fun z hz =>
      (differentiableAt_riemannZeta (hball_ne1 z hz)).differentiableWithinAt
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    set L : ℝ := Real.log (|t| + 2)
    have hL_gt1 : 1 < L := by
      have h3 : Real.exp 1 < |t| + 2 := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h3)
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ C_M * L := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hcb_sub hz
      have hz1 : z ≠ 1 := hball_ne1 z hz_ball
      have hznz : riemannZeta z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_re_lo : θ + δ / 2 ≤ z.re := by dsimp only [R] at hre_diff; linarith
      have hz_re_hi : z.re ≤ 6 := by dsimp only [R] at hre_diff; linarith
      have hz_im_lo : 1 ≤ |z.im| := by
        have htri : |t| ≤ |z.im| + |z.im - t| := by
          have := abs_add_le z.im (t - z.im)
          rw [add_sub_cancel, abs_sub_comm] at this; exact this
        have hR_le3 : R ≤ 3 := by dsimp only [R]; linarith
        linarith [abs_le.mpr him_diff]
      have hz_im_hi : |z.im| ≤ |t| + 3 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le3 : R ≤ 3 := by dsimp only [R]; linarith
        linarith [abs_le.mpr him_diff]
      have hz_bd : ‖riemannZeta z‖ ≤ (3 + 12 / (θ + δ / 2)) * (|t| + 2) := by
        have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith : 0 < z.re) hz1
        have hsub_ge : 1 ≤ ‖z - 1‖ := by
          have := Complex.abs_im_le_norm (z - 1)
          simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
          linarith
        have hinv_le : 1 / ‖z - 1‖ ≤ 1 := div_le_one_of_le₀ hsub_ge (norm_nonneg _)
        have hnorm_z : ‖z‖ ≤ 3 * (|t| + 2) := by
          have := Complex.norm_le_abs_re_add_abs_im z
          rw [abs_of_pos (by linarith : 0 < z.re)] at this
          linarith
        have hdiv_le : ‖z‖ / z.re ≤ (3 / (θ + δ / 2)) * (|t| + 2) := by
          calc ‖z‖ / z.re ≤ (3 * (|t| + 2)) / (θ + δ / 2) :=
                div_le_div₀ (by positivity) hnorm_z (by positivity) hz_re_lo
            _ = (3 / (θ + δ / 2)) * (|t| + 2) := by ring
        have h12 : 3 / (θ + δ / 2) ≤ 12 / (θ + δ / 2) :=
          div_le_div_of_nonneg_right (by norm_num) (by positivity)
        have ht2 : 1 ≤ |t| + 2 := by linarith
        nlinarith [norm_nonneg (riemannZeta z)]
      have hinv_s₀ : ‖1 / riemannZeta s₀‖ ≤ 2 := by
        have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (σ := 3) (by norm_num) t
        have h1 := h.2.1.trans h.2.2
        have hs₀_eq' : ((3 : ℝ) : ℂ) + I * (t : ℂ) = s₀ := by simp [s₀]
        rw [hs₀_eq'] at h1
        linarith
      have hratio_le : ‖riemannZeta z / riemannZeta s₀‖ ≤ A_zeta * (|t| + 2) := by
        rw [show riemannZeta z / riemannZeta s₀ = riemannZeta z * (1 / riemannZeta s₀) by ring, norm_mul]
        calc ‖riemannZeta z‖ * ‖1 / riemannZeta s₀‖
            ≤ ((3 + 12 / (θ + δ / 2)) * (|t| + 2)) * 2 :=
              mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = A_zeta * (|t| + 2) := by dsimp only [A_zeta]; ring
      have hre_eq : (Log z).re = Real.log ‖riemannZeta z / riemannZeta s₀‖ := by
        have hexp : Real.exp (Log z).re = ‖riemannZeta z / riemannZeta s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      rw [hre_eq]
      calc Real.log ‖riemannZeta z / riemannZeta s₀‖
          ≤ Real.log (A_zeta * (|t| + 2)) :=
            Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)) hratio_le
        _ = Real.log A_zeta + L := Real.log_mul (by linarith) (by linarith)
        _ ≤ C_M * L := by
            have hlogA : 0 ≤ Real.log A_zeta := Real.log_nonneg (by linarith)
            dsimp only [C_M]; nlinarith
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - 3 : ℝ) : ℂ)) := Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      dsimp only [r]; constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hneg_norm : ‖-deriv riemannZeta s / riemannZeta s‖ = ‖deriv riemannZeta s / riemannZeta s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ (2 * R / (R - r) ^ 2) * (C_M * L) := hbc
      _ = C_tall * L := by dsimp only [C_tall]; ring
      _ ≤ C * L := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  · -- Compact box case: `|s.im| ≤ 4`
    have hsK : s ∈ K := ⟨hre_lo, hre_hi, him⟩
    exact ⟨(hK_sub hsK).2, (hM_box s hsK).trans ((le_max_left M_box 1).trans (le_max_left _ _))⟩

/-- Elementary helper: for any `α > 0`, there is `K > 0` such that `(Real.log (x + 2)) ^ 2 ≤ K * x ^ α`
for all `x ≥ 2`. -/
private lemma log_add_two_sq_le_rpow {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2 ≤ x → (Real.log (x + 2)) ^ 2 ≤ K * x ^ α := by
  set β : ℝ := α / 2 with hβ_def
  have hβ : 0 < β := by positivity
  refine ⟨(2 / β) ^ 2, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (x + 2) ≤ 2 * Real.log x := by
    have hsq : x + 2 ≤ x ^ 2 := by nlinarith
    calc Real.log (x + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hrpow := Real.log_le_rpow_div hx0.le hβ
  have hlin : Real.log (x + 2) ≤ (2 / β) * x ^ β := by
    calc Real.log (x + 2) ≤ 2 * Real.log x := hlog
      _ ≤ 2 * (x ^ β / β) := mul_le_mul_of_nonneg_left hrpow (by norm_num)
      _ = (2 / β) * x ^ β := by ring
  calc (Real.log (x + 2)) ^ 2
      ≤ ((2 / β) * x ^ β) ^ 2 :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlin 2
    _ = (2 / β) ^ 2 * (x ^ β * x ^ β) := by ring
    _ = (2 / β) ^ 2 * x ^ α := by rw [← Real.rpow_add hx0, hβ_def, add_halves]

/-- **UNCONDITIONAL REVERSE DIRECTION (`ZeroFree(θ) → |ψ(x) - x| = O(x^{θ + ε})`)**:
for ANY `0 < θ < 1`, if `riemannZeta` has no zeros in `Re(s) > θ` (`s ≠ 1`), then for every `ε > 0`,
there exists `C > 0` such that `|Chebyshev.psi x - x| ≤ C * x ^ (θ + ε)` for all `x ≥ 2`,
proved directly via `negLogDerivZeta_bound_of_zeroFree_halfPlane` and the sharp Perron contour
shift `Stage5ContourExplicit.vertical_contour_shift_mul_eq_sum_residues`! -/
theorem psi_rpow_eps_of_zeroFree_halfPlane {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ (θ + ε) := by
  intro ε hε
  -- Shrink `ε` to `ε' = min ε ((1 - θ) / 2)` so `σ = θ + ε' / 2 < 1`
  set ε' : ℝ := min ε ((1 - θ) / 2) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by linarith)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_lt : ε' ≤ (1 - θ) / 2 := min_le_right _ _
  set σ : ℝ := θ + ε' / 2 with hσ_def
  have hσ_pos : 0 < σ := by linarith
  have hσ_lt1 : σ < 1 := by linarith
  obtain ⟨C₀, hC₀_pos, hbd_tall, hbd_box⟩ :=
    negLogDerivZeta_bound_of_zeroFree_halfPlane hθ0 (by positivity : 0 < ε' / 2) (by linarith) hzf
  -- Unified vertical bound on `Re(s) = σ`: `‖(-ζ'/ζ)(σ + i t)‖ ≤ K_L * Real.log (|t| + 2)` for ALL `t : ℝ`
  set K_L : ℝ := max C₀ (2 * (C₀ + 1 / (1 - σ)))
  have hKL_pos : 0 < K_L := lt_of_lt_of_le hC₀_pos (le_max_left _ _)
  have hbd_vert : ∀ t : ℝ, ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (t : ℂ))‖ ≤
      K_L * Real.log (|t| + 2) := by
    intro t
    unfold Stage3ZeroFreeRegion.negLogDerivZeta
    by_cases ht4 : 4 ≤ |t|
    · have h1 := hbd_tall ((σ : ℂ) + I * (t : ℂ)) (by simp [σ]) (by simp; linarith) (by simpa using ht4)
      have him_eq : ((σ : ℂ) + I * (t : ℂ)).im = t := by simp
      rw [him_eq] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.log_nonneg (by linarith [abs_nonneg t])))
    · push Not at ht4
      have hs1 : ((σ : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      have hbox := hbd_box ((σ : ℂ) + I * (t : ℂ)) (by simp [σ]) (by simp; linarith) (by simpa using ht4.le)
      have hsnz : riemannZeta ((σ : ℂ) + I * (t : ℂ)) ≠ 0 := by
        have h1 := hbox.1
        rw [zetaReg_eq_mul_riemannZeta (by simpa using hσ_pos) hs1] at h1
        exact (mul_ne_zero_iff.mp h1).2
      have hreg := negLogDerivZetaReg_eq_sub_pole (by simpa using hσ_pos) hs1 hsnz
      have hrew : -deriv riemannZeta ((σ : ℂ) + I * (t : ℂ)) / riemannZeta ((σ : ℂ) + I * (t : ℂ)) =
          negLogDerivZetaReg ((σ : ℂ) + I * (t : ℂ)) + 1 / (((σ : ℂ) + I * (t : ℂ)) - 1) := by
        linear_combination -hreg
      have hpole : ‖(1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - 1)‖ ≤ 1 / (1 - σ) := by
        rw [norm_div, norm_one]
        have hden : 1 - σ ≤ ‖((σ : ℂ) + I * (t : ℂ)) - 1‖ := by
          have h := Complex.abs_re_le_norm (((σ : ℂ) + I * (t : ℂ)) - 1)
          have hre : (((σ : ℂ) + I * (t : ℂ)) - 1).re = σ - 1 := by simp
          rw [hre, abs_of_neg (by linarith)] at h; linarith
        exact div_le_div_of_nonneg_left zero_le_one (by linarith) hden
      have hlog2 : (1 / 2 : ℝ) ≤ Real.log (|t| + 2) :=
        (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
          (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
      rw [hrew]
      calc ‖negLogDerivZetaReg ((σ : ℂ) + I * (t : ℂ)) + 1 / (((σ : ℂ) + I * (t : ℂ)) - 1)‖
          ≤ ‖negLogDerivZetaReg ((σ : ℂ) + I * (t : ℂ))‖ + ‖(1 : ℂ) / (((σ : ℂ) + I * (t : ℂ)) - 1)‖ :=
            norm_add_le _ _
        _ ≤ C₀ + 1 / (1 - σ) := add_le_add hbox.2 hpole
        _ ≤ (2 * (C₀ + 1 / (1 - σ))) * Real.log (|t| + 2) := by
            have hnn : 0 ≤ C₀ + 1 / (1 - σ) := by positivity
            nlinarith
        _ ≤ K_L * Real.log (|t| + 2) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  -- Absorb `(log(x + 2))²` into `x ^ (ε' / 2)`
  obtain ⟨K_log, hK_log_pos, hK_log⟩ := log_add_two_sq_le_rpow (α := ε' / 2) (by positivity)
  set C_main : ℝ := 4800 + K_L * (2 / σ + 2) + 18 * C₀
  have hC_main_pos : 0 < C_main := by positivity
  set C_large : ℝ := C_main * K_log
  set C_fin : ℝ := max C_large 28
  refine ⟨C_fin, by positivity, fun x hx2 => ?_⟩
  by_cases hx4 : 4 ≤ x
  · -- Main regime `x ≥ 4`: sharp Perron shift from `c = 1 + 1 / log x` to `σ = θ + ε' / 2` with `T = x`!
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    have hlogx_gt1 : 1 < Real.log x := by
      have h4 : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
    have hlogx_pos : 0 < Real.log x := zero_lt_one.trans hlogx_gt1
    set c : ℝ := 1 + 1 / Real.log x with hc_def
    have hc1 : 1 < c := by rw [hc_def]; linarith [div_pos one_pos hlogx_pos]
    have hc2 : c ≤ 2 := by
      rw [hc_def]
      have : 1 / Real.log x ≤ 1 := (div_le_one hlogx_pos).mpr hlogx_gt1.le
      linarith
    have hc3 : c ≤ 3 := by linarith
    have hxc_le : x ^ c ≤ 3 * x := by
      have h1 : x ^ c = x * x ^ (1 / Real.log x) := by
        rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
      have h2 : x ^ (1 / Real.log x) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hlogx_pos.ne']
      rw [h1, h2]
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      nlinarith
    -- Step 1: Sharp Perron truncation at `T = x`
    have hPerron_raw := Stage5ContourExplicit.norm_chebyshevPsiChar_sub_truncatedPerron_le
      (1 : DirichletCharacter ℂ 1) hx2 (by linarith : 1 ≤ x)
    have hpsi_eq : Stage2DirichletAP.chebyshevPsiChar (1 : DirichletCharacter ℂ 1) x =
        (Chebyshev.psi x : ℂ) := by
      rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      unfold Stage2DirichletAP.chebyshevPsiChar RHDirect.chebyshevPsi
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Stage2DirichletAP.principal_char_apply_nat, if_pos (Nat.coprime_one_right n), one_mul]
    rw [hpsi_eq] at hPerron_raw
    have hlog_cmp : Real.log x + 1 ≤ 2 * Real.log (x + 2) := by
      have h1 : Real.log x ≤ Real.log (x + 2) := Real.log_le_log hx0 (by linarith)
      linarith
    have hPerron : ‖(Chebyshev.psi x : ℂ) -
        Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x‖ ≤
        4800 * (Real.log (x + 2)) ^ 2 := by
      have hxx : x / x = 1 := div_self hx0.ne'
      rw [hxx, one_mul] at hPerron_raw
      have hsq : (Real.log x + 1) ^ 2 + (Real.log x + 1) ≤ 2 * (Real.log x + 1) ^ 2 := by nlinarith
      have hsq2 : (Real.log x + 1) ^ 2 ≤ 4 * (Real.log (x + 2)) ^ 2 := by
        calc (Real.log x + 1) ^ 2 ≤ (2 * Real.log (x + 2)) ^ 2 :=
              pow_le_pow_left₀ (by linarith) hlog_cmp 2
          _ = 4 * (Real.log (x + 2)) ^ 2 := by ring
      linarith
    -- Step 2: Exact zero-free contour shift of `truncatedPerronPsi 1 x c x` to `Re(s) = σ`
    -- via `rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part` + `vertical_contour_shift_of_rectBoundaryIntegral`!
    let W : ℂ → ℂ := fun s => (x : ℂ) ^ s / s
    have hW_one : W 1 = (x : ℂ) := by simp [W, Complex.cpow_one]
    have hW_diff : DifferentiableOn ℂ W (Stage5ContourExplicit.closedRect σ c (-x) x) := by
      intro s hs
      have hs_pos : 0 < s.re := lt_of_lt_of_le hσ_pos hs.1.1
      have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_pos; exact lt_irrefl 0 hs_pos
      have hpow : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ w) s := by
        have hEq : (fun w : ℂ => (x : ℂ) ^ w) = fun w : ℂ => cexp (Complex.log (x : ℂ) * w) :=
          funext fun w => Complex.cpow_def_of_ne_zero hxC w
        rw [hEq]; fun_prop
      exact (hpow.div differentiableAt_id hs0).differentiableWithinAt
    have hrect_sub_U : Stage5ContourExplicit.closedRect σ c (-x) x ⊆ {z : ℂ | 0 < z.re ∧ zetaReg z ≠ 0} := by
      intro z hz
      have hz_pos : 0 < z.re := lt_of_lt_of_le hσ_pos hz.1.1
      refine ⟨hz_pos, ?_⟩
      by_cases hz1 : z = 1
      · subst hz1; rw [zetaReg_one]; exact one_ne_zero
      · rw [zetaReg_eq_mul_riemannZeta hz_pos hz1]
        exact mul_ne_zero (sub_ne_zero.mpr hz1) (hzf z (by linarith [hz.1.1]) hz1)
    have h1_open : (1 : ℂ) ∈ Stage5ContourExplicit.openRect σ c (-x) x :=
      ⟨by simp [hσ_lt1, hc1], by simp [hx0]⟩
    have h1_nhds : Stage5ContourExplicit.closedRect σ c (-x) x ∈ 𝓝 (1 : ℂ) := by
      have hopen : IsOpen (Stage5ContourExplicit.openRect σ c (-x) x) := isOpen_Ioo.reProdIm isOpen_Ioo
      have hsub : Stage5ContourExplicit.openRect σ c (-x) x ⊆ Stage5ContourExplicit.closedRect σ c (-x) x :=
        fun _ ⟨h1, h2⟩ => ⟨Set.Ioo_subset_Icc_self h1, Set.Ioo_subset_Icc_self h2⟩
      exact Filter.mem_of_superset (hopen.mem_nhds h1_open) hsub
    let G : ℂ → ℂ := fun s => negLogDerivZetaReg s * W s + dslope W 1 s
    have hG_diff : DifferentiableOn ℂ G (Stage5ContourExplicit.closedRect σ c (-x) x) :=
      ((differentiableOn_negLogDerivZetaReg.mono hrect_sub_U).mul hW_diff).add
        ((Complex.differentiableOn_dslope h1_nhds).mpr hW_diff)
    let F : ℂ → ℂ := fun s => Stage3ZeroFreeRegion.negLogDerivZeta s * W s
    have hbdry : ∀ s ∈ Stage5ContourExplicit.closedRect σ c (-x) x,
        (∀ p ∈ ({(1 : ℂ)} : Finset ℂ), s ≠ p) →
        F s = G s + ∑ p ∈ ({(1 : ℂ)} : Finset ℂ), (x : ℂ) / (s - p) := by
      intro s hs hne
      have hs1 : s ≠ 1 := hne 1 (Finset.mem_singleton_self 1)
      have hsU := hrect_sub_U hs
      have hsnz : riemannZeta s ≠ 0 := by
        have h1 := hsU.2
        rw [zetaReg_eq_mul_riemannZeta hsU.1 hs1] at h1
        exact (mul_ne_zero_iff.mp h1).2
      have hreg := negLogDerivZetaReg_eq_sub_pole hsU.1 hs1 hsnz
      simp only [Finset.sum_singleton, F, G, Stage3ZeroFreeRegion.negLogDerivZeta]
      rw [hreg, dslope_of_ne W hs1, slope_def_field, hW_one]
      have hsub_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      field_simp [hsub_ne]; ring
    have hrect := Stage5ContourExplicit.rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part
      F G (by linarith) (by linarith) {(1 : ℂ)} id (fun _ => (x : ℂ))
      (fun p hp => by rw [Finset.mem_singleton.mp hp]; exact h1_open) hG_diff hbdry
    simp only [Finset.sum_singleton] at hrect
    have hshift := Stage5ContourExplicit.vertical_contour_shift_of_rectBoundaryIntegral hrect
    have hL1_eq : ∀ s : ℂ, Stage3ZeroFreeRegion.negLogDerivL (1 : DirichletCharacter ℂ 1) s =
        Stage3ZeroFreeRegion.negLogDerivZeta s := fun s => by
      unfold Stage3ZeroFreeRegion.negLogDerivL Stage3ZeroFreeRegion.negLogDerivZeta
      rw [DirichletCharacter.LFunction_modOne_eq]
    have hperron_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((c : ℂ) + I * (t : ℂ))) =
        Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x := by
      unfold Stage5ContourExplicit.truncatedPerronPsi
      congr 1
      refine intervalIntegral.integral_congr fun t _ => ?_
      dsimp only [F, W]
      rw [hL1_eq, mul_div_assoc]
    rw [hperron_eq] at hshift
    -- Step 3: Bound the left-vertical integral on `Re(s) = σ`
    have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ)))‖ ≤
        K_L * (2 / σ + 2) * x ^ σ * (Real.log (x + 2)) ^ 2 := by
      have hF_cont : ContinuousOn (fun t : ℝ => F ((σ : ℂ) + I * (t : ℂ))) (Set.uIcc (-x) x) := by
        rw [Set.uIcc_of_le (by linarith)]
        have hsub : (fun t : ℝ => (σ : ℂ) + I * (t : ℂ)) '' Set.Icc (-x) x ⊆
            Stage5ContourExplicit.closedRect σ c (-x) x := by
          rintro _ ⟨t, ht, rfl⟩; exact ⟨by simp; linarith, by simpa using ht⟩
        have hmap : ContinuousOn (fun t : ℝ => (σ : ℂ) + I * (t : ℂ)) (Set.Icc (-x) x) := by fun_prop
        have h1 : ContinuousOn (fun s => G s + (x : ℂ) / (s - 1))
            ((fun t : ℝ => (σ : ℂ) + I * (t : ℂ)) '' Set.Icc (-x) x) := by
          refine (hG_diff.continuousOn.mono hsub).add (continuousOn_const.div
            (continuousOn_id.sub continuousOn_const) ?_)
          rintro _ ⟨t, _, rfl⟩ h0
          have := congrArg Complex.re h0; simp at this; linarith
        refine (h1.comp hmap (Set.mapsTo_image _ _)).congr fun t ht => ?_
        dsimp only [Function.comp_apply]
        have hne : ∀ p ∈ ({(1 : ℂ)} : Finset ℂ), ((σ : ℂ) + I * (t : ℂ)) ≠ p := by
          intro p hp hEq; rw [Finset.mem_singleton.mp hp] at hEq
          have := congrArg Complex.re hEq; simp at this; linarith
        have := hbdry ((σ : ℂ) + I * (t : ℂ)) ⟨by simp; linarith, by simpa using ht⟩ hne
        simpa only [Finset.sum_singleton] using this
      have hinv_cont : Continuous (fun t : ℝ => ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹) := by
        refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
        rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this; linarith
      have hinv_int : ∫ t in (-x)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ (2 / σ + 2) * Real.log (x + 2) := by
        have hmid : ∫ t in (-1 : ℝ)..1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 / σ := by
          have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ σ⁻¹ := fun t _ => by
            have hden : σ ≤ ‖(σ : ℂ) + I * (t : ℂ)‖ := by
              simpa [abs_of_pos hσ_pos] using Complex.abs_re_le_norm ((σ : ℂ) + I * (t : ℂ))
            exact inv_anti₀ hσ_pos hden
          calc ∫ t in (-1 : ℝ)..1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹
              ≤ ∫ _t in (-1 : ℝ)..1, σ⁻¹ :=
                intervalIntegral.integral_mono_on (by norm_num) (hinv_cont.intervalIntegrable _ _)
                  intervalIntegrable_const hpt
            _ = 2 / σ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
        have hpos_tail : ∫ t in (1 : ℝ)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log x := by
          have hint_t : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 : ℝ) x := by
            refine (ContinuousOn.inv₀ continuousOn_id fun t ht => ?_).intervalIntegrable
            rw [Set.uIcc_of_le hx1] at ht; dsimp only [id_eq]; linarith [ht.1]
          calc ∫ t in (1 : ℝ)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹
              ≤ ∫ t in (1 : ℝ)..x, t⁻¹ :=
                intervalIntegral.integral_mono_on hx1 (hinv_cont.intervalIntegrable _ _) hint_t fun t ht => by
                  have ht0 : 0 < t := zero_lt_one.trans_le ht.1
                  have hden : t ≤ ‖(σ : ℂ) + I * (t : ℂ)‖ := by
                    simpa [abs_of_pos ht0] using Complex.abs_im_le_norm ((σ : ℂ) + I * (t : ℂ))
                  exact inv_anti₀ ht0 hden
            _ = Real.log x := by rw [integral_inv_of_pos zero_lt_one hx0, div_one]
        have hneg_tail : ∫ t in (-x)..(-1 : ℝ), ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log x := by
          have hcomp : ∫ t in (-x)..(-1 : ℝ), ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ =
              ∫ u in (1 : ℝ)..x, ‖(σ : ℂ) + I * (u : ℂ)‖⁻¹ := by
            have h1 := intervalIntegral.integral_comp_neg
              (f := fun u : ℝ => ‖(σ : ℂ) + I * (u : ℂ)‖⁻¹) (a := -x) (b := -1)
            simp only [neg_neg] at h1
            rw [← h1]
            refine intervalIntegral.integral_congr fun t _ => ?_
            congr 1; rw [← Complex.norm_conj]; congr 1
            apply Complex.ext <;> simp
          rw [hcomp]; exact hpos_tail
        have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
          (hinv_cont.intervalIntegrable (μ := volume) (-x) (-1))
          (hinv_cont.intervalIntegrable (μ := volume) (-1) 1)
        have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
          (hinv_cont.intervalIntegrable (μ := volume) (-x) 1)
          (hinv_cont.intervalIntegrable (μ := volume) 1 x)
        have hlog_le : Real.log x ≤ Real.log (x + 2) := Real.log_le_log hx0 (by linarith)
        have hlog_ge1 : 1 ≤ Real.log (x + 2) := hlogx_gt1.le.trans hlog_le
        have h2σ : 2 / σ ≤ (2 / σ) * Real.log (x + 2) := le_mul_of_one_le_right (by positivity) hlog_ge1
        linarith
      have hpt : ∀ t ∈ Set.Icc (-x) x,
          ‖F ((σ : ℂ) + I * (t : ℂ))‖ ≤
            (K_L * Real.log (x + 2) * x ^ σ) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
        intro t ht
        have habs_t : |t| ≤ x := abs_le.mpr ht
        have hlog_le : Real.log (|t| + 2) ≤ Real.log (x + 2) :=
          Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
        dsimp only [F, W]
        rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
        rw [hre, div_eq_mul_inv, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            ((hbd_vert t).trans (mul_le_mul_of_nonneg_left hlog_le hKL_pos.le))
            (Real.rpow_nonneg hx0.le _))
          (inv_nonneg.mpr (norm_nonneg _))
      have hlog_nn : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))‖
          ≤ 1 * ∫ t in (-x)..x, ‖F ((σ : ℂ) + I * (t : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith))
              (norm_nonneg _) zero_le_one
        _ ≤ ∫ t in (-x)..x, (K_L * Real.log (x + 2) * x ^ σ) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hF_cont.intervalIntegrable.norm
              ((hinv_cont.intervalIntegrable _ _).const_mul _) hpt
        _ = (K_L * Real.log (x + 2) * x ^ σ) * ∫ t in (-x)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (K_L * Real.log (x + 2) * x ^ σ) * ((2 / σ + 2) * Real.log (x + 2)) :=
            mul_le_mul_of_nonneg_left hinv_int (by positivity)
        _ = K_L * (2 / σ + 2) * x ^ σ * (Real.log (x + 2)) ^ 2 := by ring
    -- Step 4: Bound top and bottom horizontal integrals on `Im(s) = ±x`
    have hHoriz_bd : ∀ s_im : ℝ, (s_im = x ∨ s_im = -x) →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (s_im : ℂ)))‖ ≤
          9 * C₀ * Real.log (x + 2) := by
      intro s_im hsim
      have hlog_nn : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
      have habs_sim : |s_im| = x := by rcases hsim with rfl | rfl <;> simp [abs_of_pos hx0]
      have hF_cont : ContinuousOn (fun u : ℝ => F ((u : ℂ) + I * (s_im : ℂ))) (Set.uIcc σ c) := by
        rw [Set.uIcc_of_le (by linarith)]
        have hsub : (fun u : ℝ => (u : ℂ) + I * (s_im : ℂ)) '' Set.Icc σ c ⊆
            Stage5ContourExplicit.closedRect σ c (-x) x := by
          rintro _ ⟨u, hu, rfl⟩; exact ⟨by simpa using hu, by simp [abs_le.mp (le_of_eq habs_sim)]⟩
        have hmap : ContinuousOn (fun u : ℝ => (u : ℂ) + I * (s_im : ℂ)) (Set.Icc σ c) := by fun_prop
        have h1 : ContinuousOn (fun s => G s + (x : ℂ) / (s - 1))
            ((fun u : ℝ => (u : ℂ) + I * (s_im : ℂ)) '' Set.Icc σ c) := by
          refine (hG_diff.continuousOn.mono hsub).add (continuousOn_const.div
            (continuousOn_id.sub continuousOn_const) ?_)
          rintro _ ⟨u, _, rfl⟩ h0
          have := congrArg Complex.im h0; simp at this; rw [this, abs_zero] at habs_sim; linarith
        refine (h1.comp hmap (Set.mapsTo_image _ _)).congr fun u hu => ?_
        dsimp only [Function.comp_apply]
        have hne : ∀ p ∈ ({(1 : ℂ)} : Finset ℂ), ((u : ℂ) + I * (s_im : ℂ)) ≠ p := by
          intro p hp hEq; rw [Finset.mem_singleton.mp hp] at hEq
          have := congrArg Complex.im hEq; simp at this; rw [this, abs_zero] at habs_sim; linarith
        have := hbdry ((u : ℂ) + I * (s_im : ℂ)) ⟨by simpa using hu, by simp [abs_le.mp (le_of_eq habs_sim)]⟩ hne
        simpa only [Finset.sum_singleton] using this
      have hpt : ∀ u ∈ Set.Icc σ c, ‖F ((u : ℂ) + I * (s_im : ℂ))‖ ≤ 3 * C₀ * Real.log (x + 2) := by
        intro u hu
        have hL := hbd_tall ((u : ℂ) + I * (s_im : ℂ)) (by simpa [σ] using hu.1)
          (by simp; linarith [hu.2]) (by simp [habs_sim]; linarith)
        have him_eq : ((u : ℂ) + I * (s_im : ℂ)).im = s_im := by simp
        rw [him_eq, habs_sim] at hL
        have hx_pow : x ^ u ≤ 3 * x := (Real.rpow_le_rpow_of_exponent_le hx1 hu.2).trans hxc_le
        have hden : x ≤ ‖(u : ℂ) + I * (s_im : ℂ)‖ := by
          simpa [habs_sim] using Complex.abs_im_le_norm ((u : ℂ) + I * (s_im : ℂ))
        dsimp only [F, W, Stage3ZeroFreeRegion.negLogDerivZeta]
        rw [norm_mul, norm_div ((x : ℂ) ^ _), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((u : ℂ) + I * (s_im : ℂ)).re = u := by simp
        rw [hre]
        calc ‖-deriv riemannZeta ((u : ℂ) + I * (s_im : ℂ)) / riemannZeta ((u : ℂ) + I * (s_im : ℂ))‖ *
              (x ^ u / ‖(u : ℂ) + I * (s_im : ℂ)‖)
            ≤ (C₀ * Real.log (x + 2)) * ((3 * x) / x) :=
              mul_le_mul hL (div_le_div₀ (by positivity) hx_pow hx0 hden) (by positivity) (by positivity)
          _ = 3 * C₀ * Real.log (x + 2) := by field_simp [hx0.ne']
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hlen : c - σ ≤ 3 := by linarith
      calc (2 * Real.pi)⁻¹ * ‖∫ u in σ..c, F ((u : ℂ) + I * (s_im : ℂ))‖
          ≤ 1 * ∫ u in σ..c, ‖F ((u : ℂ) + I * (s_im : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith))
              (norm_nonneg _) zero_le_one
        _ ≤ ∫ _u in σ..c, (3 * C₀ * Real.log (x + 2)) := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hF_cont.intervalIntegrable.norm
              intervalIntegrable_const hpt
        _ = (c - σ) * (3 * C₀ * Real.log (x + 2)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 3 * (3 * C₀ * Real.log (x + 2)) :=
            mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 9 * C₀ * Real.log (x + 2) := by ring
    -- Step 5: Combine all four bounds and absorb `(log(x + 2))²` into `x ^ (ε' / 2)`!
    have hbot_eq : (∫ u in σ..c, F ((u : ℂ) - I * (x : ℂ))) =
        ∫ u in σ..c, F ((u : ℂ) + I * ((-x : ℝ) : ℂ)) :=
      intervalIntegral.integral_congr fun u _ => by congr 1; push_cast; ring
    have hshift_sub :
        ‖Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x - (x : ℂ)‖ ≤
          K_L * (2 / σ + 2) * x ^ σ * (Real.log (x + 2)) ^ 2 + 18 * C₀ * Real.log (x + 2) := by
      have hrew : Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x - (x : ℂ) =
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ)))) +
          ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (x : ℂ)))) -
          ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) - I * (x : ℂ)))) := by
        linear_combination hshift
      rw [hrew, hbot_eq]
      have ht1 := norm_sub_le
        ((((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ)))) +
          ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (x : ℂ)))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * ((-x : ℝ) : ℂ))))
      have ht2 := norm_add_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (x : ℂ))))
      have htop := hHoriz_bd x (Or.inl rfl)
      have hbot := hHoriz_bd (-x) (Or.inr rfl)
      linarith
    have hcast : |Chebyshev.psi x - x| = ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have htri : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ ≤
        ‖(Chebyshev.psi x : ℂ) - Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x‖ +
        ‖Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x - (x : ℂ)‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le
        ((Chebyshev.psi x : ℂ) - Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x)
        (Stage5ContourExplicit.truncatedPerronPsi (1 : DirichletCharacter ℂ 1) x c x - (x : ℂ))
    have hxσ_ge1 : 1 ≤ x ^ σ := Real.one_le_rpow hx1 hσ_pos.le
    have hlog_ge1 : 1 ≤ Real.log (x + 2) :=
      hlogx_gt1.le.trans (Real.log_le_log hx0 (by linarith))
    have hlog_le_sq : Real.log (x + 2) ≤ (Real.log (x + 2)) ^ 2 := by nlinarith
    have hcomb : |Chebyshev.psi x - x| ≤ C_main * x ^ σ * (Real.log (x + 2)) ^ 2 := by
      rw [hcast]
      have h1 : 4800 * (Real.log (x + 2)) ^ 2 ≤ 4800 * x ^ σ * (Real.log (x + 2)) ^ 2 := by
        nlinarith [sq_nonneg (Real.log (x + 2))]
      have h2 : 18 * C₀ * Real.log (x + 2) ≤ 18 * C₀ * x ^ σ * (Real.log (x + 2)) ^ 2 := by
        have ha : Real.log (x + 2) ≤ x ^ σ * (Real.log (x + 2)) ^ 2 := by nlinarith
        nlinarith
      dsimp only [C_main]
      linarith
    have hpow_comb : x ^ σ * x ^ (ε' / 2) = x ^ (θ + ε') := by
      rw [← Real.rpow_add hx0, hσ_def]; congr 1; ring
    have hpow_le : x ^ (θ + ε') ≤ x ^ (θ + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc |Chebyshev.psi x - x|
        ≤ C_main * x ^ σ * (Real.log (x + 2)) ^ 2 := hcomb
      _ ≤ C_main * x ^ σ * (K_log * x ^ (ε' / 2)) :=
          mul_le_mul_of_nonneg_left (hK_log x hx2) (by positivity)
      _ = C_large * (x ^ σ * x ^ (ε' / 2)) := by dsimp only [C_large]; ring
      _ = C_large * x ^ (θ + ε') := by rw [hpow_comb]
      _ ≤ C_large * x ^ (θ + ε) := mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ ≤ C_fin * x ^ (θ + ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  · -- Small regime `2 ≤ x < 4`
    push Not at hx4
    have hpsi_le : Chebyshev.psi x ≤ 6 * x := by
      rw [← Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      exact Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith)
    have hpsi_nn : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
    have habs : |Chebyshev.psi x - x| ≤ 7 * x := by rw [abs_le]; constructor <;> linarith
    have hpow : (1 : ℝ) ≤ x ^ (θ + ε) := Real.one_le_rpow (by linarith) (by positivity)
    have hC28 : 28 ≤ C_fin := le_max_right _ _
    have h7x : 7 * x ≤ 28 := by linarith
    nlinarith

/-- **UNCONDITIONAL FORWARD DIRECTION (`|ψ(x) - x| = O(x^{θ + ε}) → ZeroFree(θ)`)**:
wired directly from `Stage3RealAnalyticLandau.zeroFree_riemannZeta_of_psi_bound`. -/
theorem zeroFree_halfPlane_of_psi_rpow_eps {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hpsi : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ (θ + ε)) :
    ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  rcases lt_or_ge s.re 1 with hlt1 | hge1
  · set ε : ℝ := (s.re - θ) / 2 with hε_def
    have hε0 : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨C, hC_pos, hCbd⟩ := hpsi ε hε0
    -- Extend `∀ x ≥ 2` to `∀ x ≥ 1` cleanly (on `[1, 2)`, `Chebyshev.psi x = 0`, so `|ψ(x) - x| = x ≤ 2`).
    have hCbd1 : ∀ x : ℝ, 1 ≤ x → |RHDirect.chebyshevPsi x - x| ≤ max C 2 * x ^ (θ + ε) := by
      intro x hx1
      rw [Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi]
      by_cases hx2 : 2 ≤ x
      · exact (hCbd x hx2).trans
          (mul_le_mul_of_nonneg_right (le_max_left C 2) (Real.rpow_nonneg (by linarith) _))
      · push Not at hx2
        have hfl : ⌊x⌋₊ = 1 := (Nat.floor_eq_iff (by linarith)).mpr ⟨by norm_num; exact hx1, by norm_num; exact hx2⟩
        have hpsi0 : Chebyshev.psi x = 0 := by
          unfold Chebyshev.psi
          rw [hfl]
          have hIoc : Finset.Ioc 0 1 = {1} := by decide
          rw [hIoc, Finset.sum_singleton, ArithmeticFunction.vonMangoldt_apply_one]
        rw [hpsi0, zero_sub, abs_neg, abs_of_pos (by linarith)]
        have hpow : (1 : ℝ) ≤ x ^ (θ + ε) := Real.one_le_rpow hx1 (by positivity)
        have h2 : (2 : ℝ) ≤ max C 2 := le_max_right C 2
        nlinarith
    exact (Stage3RealAnalyticLandau.zeroFree_riemannZeta_of_psi_bound
      (by positivity : 0 ≤ max C 2) (by rw [hε_def]; linarith) hCbd1).1 s (by rw [hε_def]; linarith) hs1
  · exact riemannZeta_ne_zero_of_one_le_re hge1

/-- **UNCONDITIONAL SHARP BIDIRECTIONAL EQUIVALENCE: ZERO-FREE HALF-PLANE `Re(s) > θ` ↔ `ψ(x) - x = O(x^{θ + ε})`**:
for EVERY `0 < θ < 1` (zero extra assumptions!):
`(∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) ↔ ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, |Chebyshev.psi x - x| ≤ C * x ^ (θ + ε)`. -/
theorem zeroFree_halfPlane_iff_psi_rpow_eps {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ (θ + ε)) :=
  ⟨psi_rpow_eps_of_zeroFree_halfPlane hθ0 hθ1, zeroFree_halfPlane_of_psi_rpow_eps hθ0 hθ1⟩

/-- **Unconditional Equivalence Between `Chebyshev.psi` and `Chebyshev.theta` Error Bounds**
for any exponent `θ ≥ 1 / 2`: via `Stage3RealAnalyticLandau.psi_theta_sandwich`
(`|ψ(x) - ϑ(x)| ≤ 2 √x log x`). -/
theorem psi_rpow_eps_iff_theta_rpow_eps {θ : ℝ} (hθ : 1 / 2 ≤ θ) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ (θ + ε)) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.theta x - x| ≤ C * x ^ (θ + ε)) := by
  have hdiff_rpow : ∀ ε : ℝ, 0 < ε →
      ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - Chebyshev.theta x| ≤ (2 / ε) * x ^ (θ + ε) := by
    intro ε hε x hx2
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hsnd := Stage3RealAnalyticLandau.psi_theta_sandwich hx1
    rw [Stage3RealAnalyticLandau.chebyshevPsi_eq_mathlib_psi] at hsnd
    rw [abs_of_nonneg (sub_nonneg.mpr hsnd.1)]
    have hlog := Real.log_le_rpow_div hx0.le hε
    have hsqrt : Real.sqrt x ≤ x ^ θ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx1 hθ
    calc Chebyshev.psi x - Chebyshev.theta x
        ≤ 2 * Real.sqrt x * Real.log x := hsnd.2
      _ ≤ 2 * x ^ θ * (x ^ ε / ε) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hlog
            (Real.log_nonneg hx1) (by positivity)
      _ = (2 / ε) * (x ^ θ * x ^ ε) := by ring
      _ = (2 / ε) * x ^ (θ + ε) := by rw [← Real.rpow_add hx0]
  constructor
  · intro hpsi ε hε
    obtain ⟨C, hC, hbd⟩ := hpsi ε hε
    refine ⟨C + 2 / ε, by positivity, fun x hx2 => ?_⟩
    have htri : |Chebyshev.theta x - x| ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
      have h1 := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
      rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at h1
      linarith
    linarith [hbd x hx2, hdiff_rpow ε hε x hx2]
  · intro hth ε hε
    obtain ⟨C, hC, hbd⟩ := hth ε hε
    refine ⟨C + 2 / ε, by positivity, fun x hx2 => ?_⟩
    have htri : |Chebyshev.psi x - x| ≤ |Chebyshev.theta x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
      have h1 := abs_sub_le (Chebyshev.psi x) (Chebyshev.theta x) x
      linarith
    linarith [hbd x hx2, hdiff_rpow ε hε x hx2]

/-- **MASTER UNCONDITIONAL EQUIVALENCE #1 (`RiemannHypothesis ↔ ψ(x) - x = O(x^{1/2 + ε})`)**:
directly on Mathlib's actual `RiemannHypothesis` and `Chebyshev.psi` (0 assumptions!). -/
theorem riemannHypothesis_iff_psi_sqrt_eps :
    RiemannHypothesis ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.psi x - x| ≤ C * x ^ ((1 : ℝ) / 2 + ε)) := by
  rw [RHDirect.riemannHypothesis_iff_nonvanishingRightOfHalf]
  exact zeroFree_halfPlane_iff_psi_rpow_eps (by norm_num) (by norm_num)

/-- **MASTER UNCONDITIONAL EQUIVALENCE #2 (`RiemannHypothesis ↔ ϑ(x) - x = O(x^{1/2 + ε})`)**:
directly on Mathlib's actual `RiemannHypothesis` and `Chebyshev.theta` (0 assumptions!). -/
theorem riemannHypothesis_iff_theta_sqrt_eps :
    RiemannHypothesis ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |Chebyshev.theta x - x| ≤ C * x ^ ((1 : ℝ) / 2 + ε)) :=
  riemannHypothesis_iff_psi_sqrt_eps.trans (psi_rpow_eps_iff_theta_rpow_eps le_rfl)

/-- **COMBINED MASTER EQUIVALENCE (`RiemannHypothesis ↔ ψ(x) - x = O(x^{1/2 + ε}) ∧ ϑ(x) - x = O(x^{1/2 + ε})`)**. -/
theorem riemannHypothesis_iff_psi_and_theta_sqrt_eps :
    RiemannHypothesis ↔
    ((∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        |Chebyshev.psi x - x| ≤ C * x ^ ((1 : ℝ) / 2 + ε)) ∧
     (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        |Chebyshev.theta x - x| ≤ C * x ^ ((1 : ℝ) / 2 + ε))) :=
  ⟨fun hRH => ⟨riemannHypothesis_iff_psi_sqrt_eps.mp hRH, riemannHypothesis_iff_theta_sqrt_eps.mp hRH⟩,
   fun h => riemannHypothesis_iff_psi_sqrt_eps.mpr h.1⟩

end RHDirect.Stage7VonMangoldtExplicit
