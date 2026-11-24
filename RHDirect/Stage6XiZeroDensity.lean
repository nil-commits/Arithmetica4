import RHDirect.Stage5StirlingPhragmen
import RHDirect.Stage5JensenHadamard
import RHDirect.Stage5ZetaZeroFree
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# RHDirect.Stage6XiZeroDensity

Completely **UNCONDITIONAL** (0 assumptions, 0 `sorry`, 0 custom `axiom`s) critical-strip
symmetry, two-sided de la Vallée Poussin zero-free strip, Riemann–von Mangoldt global &
short-interval zero-counting upper bounds, zero finiteness, and convergence-exponent
summability theorems directly on Mathlib's actual `riemannZeta` in pure Mathlib `v4.33.1`.

## Main Results
1. **Unconditional Critical-Strip Symmetry & Two-Sided de la Vallée Poussin Zero-Free Strip**:
   - `schwarz_reflection_entire`: general Schwarz reflection for entire functions real on `(1, ∞)`.
   - `xi_conj`: `xi (starRingEnd ℂ s) = starRingEnd ℂ (xi s)` for all `s : ℂ`.
   - `riemannZeta_zero_symm_one_sub`: every critical-strip zero `ρ` of `riemannZeta` induces
     zeros at `1 - ρ`, `starRingEnd ℂ ρ`, and `1 - starRingEnd ℂ ρ`.
   - `riemannZeta_two_sided_zeroFree_strip`:
     `∃ c > 0, ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →`
     `c / Real.log (|ρ.im| + 2) < ρ.re ∧ ρ.re < 1 - c / Real.log (|ρ.im| + 2)`.
2. **Unconditional Global & Short-Interval Riemann–von Mangoldt Upper Zero-Count Bounds**:
   - `hasOrderOneGrowth_xi`: `xi` satisfies `Stage5JensenHadamard.HasOrderOneGrowth`.
   - `riemannZeta_zero_count_ball_le`: `N_ball(R) ≤ C * R * Real.log (R + 2)` for all `R ≥ 2`.
   - `riemannZeta_zero_count_height_le`: `N(T) ≤ C * T * Real.log (T + 2)` for all `T ≥ 2`.
   - `norm_xi_two_add_I_mul_ge` & `norm_xi_strip_stirling_decay`: sharp matching lower bound
     at `2 + I * T` and vertical-strip Stirling exponential decay on `-2 ≤ Re(s) ≤ 6`.
   - `riemannZeta_zero_count_unit_interval_le` (and `riemannZeta_zero_count_unit_interval_le_nonneg`):
     short-interval bound `N(T + 1) - N(T) ≤ C * Real.log (|T| + 2)` for all `T : ℝ` via Jensen's
     formula on `xi` centered at `2 + I * T`.
3. **Unconditional Discreteness, Finiteness, & Convergence-Exponent Summability**:
   - `finite_riemannZeta_zeros_le_height`: finiteness of critical-strip zeros with `|Im(ρ)| ≤ T`.
   - `countable_critical_strip_riemannZeta_zeros`: countability of all critical-strip zeros.
   - `riemannZeta_zeros_summable_rpow_neg`: `Summable (fun n => ‖ρ n‖ ^ (-σ))` for every `σ > 1`
     and every injective enumeration `ρ : ℕ → ℂ` of critical-strip zeros of `riemannZeta`.
   - `riemannZeta_zeros_summable_inv_sq`: `Summable (fun n => (‖ρ n‖ ^ 2)⁻¹)`.
-/

noncomputable section

open Complex Finset Filter Topology Metric
open scoped BigOperators Real

namespace RHDirect.Stage6XiZeroDensity

open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5JensenHadamard
open RHDirect.Stage5ZetaZeroFree

/-! ## Section 1: Schwarz Reflection, Critical-Strip Symmetry, & Two-Sided Zero-Free Strip -/

/-- Auxiliary differentiability of the Schwarz reflection `s ↦ conj (f (conj s))` for any
entire function `f : ℂ → ℂ`. -/
private lemma hasDerivAt_conj_comp_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) (s : ℂ) :
    HasDerivAt (fun z : ℂ => starRingEnd ℂ (f (starRingEnd ℂ z)))
      (starRingEnd ℂ (deriv f (starRingEnd ℂ s))) s := by
  have hd : HasDerivAt f (deriv f (starRingEnd ℂ s)) (starRingEnd ℂ s) :=
    (hf (starRingEnd ℂ s)).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd ⊢
  have hconj_cont : Continuous (starRingEnd ℂ) := Complex.continuous_conj
  have hconj_nhds : Tendsto (starRingEnd ℂ) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using (hconj_cont.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact map_ne_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective |>.mpr hh
  have hcomp : Tendsto (fun t : ℂ =>
      starRingEnd ℂ ((starRingEnd ℂ t)⁻¹ • (f (starRingEnd ℂ s + starRingEnd ℂ t) - f (starRingEnd ℂ s))))
      (𝓝[≠] (0 : ℂ)) (𝓝 (starRingEnd ℂ (deriv f (starRingEnd ℂ s)))) :=
    (hconj_cont.tendsto _).comp (hd.comp hconj_nhds)
  refine hcomp.congr fun t => ?_
  simp only [smul_eq_mul, map_mul, map_inv₀, map_sub, Complex.conj_conj, ← map_add]

/-- **General Schwarz Reflection Principle for Entire Functions**:
if `f : ℂ → ℂ` is entire and real-valued on `(1, ∞)`, then `f (conj s) = conj (f s)` for all `s : ℂ`. -/
theorem schwarz_reflection_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ σ : ℝ, 1 < σ → (f (σ : ℂ)).im = 0) (s : ℂ) :
    f (starRingEnd ℂ s) = starRingEnd ℂ (f s) := by
  set g : ℂ → ℂ := fun z => starRingEnd ℂ (f (starRingEnd ℂ z))
  have hg_diff : Differentiable ℂ g := fun z => (hasDerivAt_conj_comp_conj hf z).differentiableAt
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hg_an : AnalyticOnNhd ℂ g Set.univ := hg_diff.differentiableOn.analyticOnNhd isOpen_univ
  -- `g` and `f` agree along the sequence `u n = 2 + 1 / (n + 1)` tending to `2` in `𝓝[≠] 2`.
  let u : ℕ → ℂ := fun n => (((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ))
  have hu_tend : Tendsto u atTop (𝓝[≠] (2 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hreal_tend : Tendsto (fun n : ℕ => (2 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (2 : ℝ)) := by
        simpa using (tendsto_const_nhds (x := (2 : ℝ))).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hcomp := (Complex.continuous_ofReal.tendsto (2 : ℝ)).comp hreal_tend
      simpa [u, Function.comp_def] using hcomp
    · refine Eventually.of_forall fun n => ?_
      change (((2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) ≠ ((2 : ℝ) : ℂ)
      rw [ne_eq, Complex.ofReal_inj]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), g z = f z := by
    refine hu_tend.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
    have hgt1 : (1 : ℝ) < 2 + 1 / ((n : ℝ) + 1) := by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have him : (f (u n)).im = 0 := hreal _ hgt1
    dsimp only [g, u]
    rw [Complex.conj_ofReal, Complex.conj_eq_iff_im.mpr him]
  have heq : Set.EqOn g f Set.univ :=
    hg_an.eqOn_of_preconnected_of_frequently_eq hf_an isPreconnected_univ (Set.mem_univ (2 : ℂ)) hfreq
  have hgs : starRingEnd ℂ (f (starRingEnd ℂ s)) = f s := heq (Set.mem_univ s)
  have h := congrArg (starRingEnd ℂ) hgs
  simpa using h

/-- `xi` is real-valued on the real half-line `(1, ∞)`. -/
lemma xi_im_eq_zero_of_one_lt_real {σ : ℝ} (hσ : 1 < σ) :
    (xi (σ : ℂ)).im = 0 := by
  have hs0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hs1 : (σ : ℂ) ≠ 1 := by
    intro h; have := Complex.ofReal_injective h; linarith
  have hs_re : 1 < (σ : ℂ).re := by simp [hσ]
  have hdef : xi (σ : ℂ) =
      (σ : ℂ) * ((σ : ℂ) - 1) * ((Real.pi : ℂ) ^ (-(σ : ℂ) / 2) *
        Complex.Gamma ((σ : ℂ) / 2) * riemannZeta (σ : ℂ)) := by
    rw [xi_eq_mul_completedRiemannZeta hs0 hs1, completedZeta_eq_tsum_of_one_lt_re hs_re,
      ← zeta_eq_tsum_one_div_nat_cpow hs_re]
  rw [← Complex.conj_eq_iff_im, hdef]
  have hpi : starRingEnd ℂ ((Real.pi : ℂ) ^ (-(σ : ℂ) / 2)) = (Real.pi : ℂ) ^ (-(σ : ℂ) / 2) := by
    have hexp : -(σ : ℂ) / 2 = (((-σ / 2 : ℝ) : ℂ)) := by push_cast; ring
    rw [hexp, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.conj_ofReal]
  have hG : starRingEnd ℂ (Complex.Gamma ((σ : ℂ) / 2)) = Complex.Gamma ((σ : ℂ) / 2) := by
    rw [← Complex.Gamma_conj]
    congr 1
    rw [map_div₀, Complex.conj_ofReal, map_ofNat]
  have hZ : starRingEnd ℂ (riemannZeta (σ : ℂ)) = riemannZeta (σ : ℂ) :=
    Complex.conj_eq_iff_im.mpr (riemannZeta_real_bounds hσ).1
  simp only [map_mul, map_sub, map_one, Complex.conj_ofReal, hpi, hG, hZ]

/-- **Unconditional Conjugation Symmetry of Mathlib's Completed Zeta `ξ(s)`**:
`xi (starRingEnd ℂ s) = starRingEnd ℂ (xi s)` for all `s : ℂ`. -/
theorem xi_conj (s : ℂ) : xi (starRingEnd ℂ s) = starRingEnd ℂ (xi s) :=
  schwarz_reflection_entire differentiable_xi (fun _ hσ => xi_im_eq_zero_of_one_lt_real hσ) s

/-- **Unconditional Critical-Strip 4-Fold Zero Symmetry on Mathlib's Actual `riemannZeta`**:
if `0 < ρ.re < 1` and `riemannZeta ρ = 0`, then `1 - ρ`, `conj ρ`, and `1 - conj ρ` are also
critical-strip zeros of `riemannZeta`. -/
theorem riemannZeta_zero_symm_one_sub {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 ∧
    riemannZeta (starRingEnd ℂ ρ) = 0 ∧
    riemannZeta (1 - starRingEnd ℂ ρ) = 0 := by
  have hxi : xi ρ = 0 := (xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨h0, h1, hρ⟩
  have hxi_1sub : xi (1 - ρ) = 0 := by rw [xi_one_sub, hxi]
  have hxi_conj : xi (starRingEnd ℂ ρ) = 0 := by rw [xi_conj, hxi, map_zero]
  have hxi_1sub_conj : xi (1 - starRingEnd ℂ ρ) = 0 := by rw [xi_one_sub, hxi_conj]
  exact ⟨((xi_eq_zero_iff_critical_strip_zeta_zero (1 - ρ)).mp hxi_1sub).2.2,
    ((xi_eq_zero_iff_critical_strip_zeta_zero (starRingEnd ℂ ρ)).mp hxi_conj).2.2,
    ((xi_eq_zero_iff_critical_strip_zeta_zero (1 - starRingEnd ℂ ρ)).mp hxi_1sub_conj).2.2⟩

/-- **UNCONDITIONAL TWO-SIDED DE LA VALLÉE POUSSIN ZERO-FREE STRIP ON MATHLIB'S `riemannZeta` (0 ASSUMPTIONS!)**:
there exists `c > 0` such that every critical-strip zero `ρ` of `riemannZeta` satisfies
`c / Real.log (|ρ.im| + 2) < ρ.re < 1 - c / Real.log (|ρ.im| + 2)`. -/
theorem riemannZeta_two_sided_zeroFree_strip :
    ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 →
        c / Real.log (|ρ.im| + 2) < ρ.re ∧ ρ.re < 1 - c / Real.log (|ρ.im| + 2) := by
  obtain ⟨c, hc, hzf⟩ := riemannZeta_deLaValleePoussin_zeroFree
  refine ⟨c, hc, fun ρ h0 h1 hρ => ?_⟩
  have hne1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hright : ρ.re < 1 - c / Real.log (|ρ.im| + 2) := by
    by_contra hge
    exact hzf ρ (not_lt.mp hge) hne1 hρ
  have hsym := (riemannZeta_zero_symm_one_sub h0 h1 hρ).1
  have h1ρ_ne1 : 1 - ρ ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hleft_raw : (1 - ρ).re < 1 - c / Real.log (|(1 - ρ).im| + 2) := by
    by_contra hge
    exact hzf (1 - ρ) (not_lt.mp hge) h1ρ_ne1 hsym
  have h1ρ_re : (1 - ρ).re = 1 - ρ.re := by simp
  have h1ρ_im : |(1 - ρ).im| = |ρ.im| := by simp
  rw [h1ρ_re, h1ρ_im] at hleft_raw
  exact ⟨by linarith, hright⟩

/-! ## Section 2: Unconditional Global Riemann–von Mangoldt Zero-Counting Bounds -/

/-- Unconditional bridge from `Stage5StirlingPhragmen.norm_xi_order_one_bound` to
`Stage5JensenHadamard.HasOrderOneGrowth`. -/
theorem hasOrderOneGrowth_xi :
    ∃ A : ℝ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ HasOrderOneGrowth xi A B := by
  obtain ⟨A, hA, B, hB, hbound⟩ := norm_xi_order_one_bound
  refine ⟨3 * A, by positivity, B + 2 * A * Real.log 3,
    by have : 0 < Real.log 3 := Real.log_pos (by norm_num); positivity,
    differentiable_xi, fun s => ?_⟩
  refine le_trans (hbound s) (Real.exp_le_exp.mpr ?_)
  have hlog_nn : 0 ≤ Real.log (‖s‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg s])
  rcases le_or_gt (1 : ℝ) ‖s‖ with hs1 | hs1
  · have hlog3_nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hmul : 2 * A * Real.log (‖s‖ + 2) ≤ 2 * A * ‖s‖ * Real.log (‖s‖ + 2) := by
      have h1 : 2 * A ≤ 2 * A * ‖s‖ := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 hlog_nn
    have hadd : A * (‖s‖ + 2) * Real.log (‖s‖ + 2) =
        A * ‖s‖ * Real.log (‖s‖ + 2) + 2 * A * Real.log (‖s‖ + 2) := by ring
    nlinarith
  · have hlog_le : Real.log (‖s‖ + 2) ≤ Real.log 3 :=
      Real.log_le_log (by linarith [norm_nonneg s]) (by linarith)
    have hterm : 2 * A * Real.log (‖s‖ + 2) ≤ 2 * A * Real.log 3 :=
      mul_le_mul_of_nonneg_left hlog_le (by positivity)
    have hmul_nn : 0 ≤ A * ‖s‖ * Real.log (‖s‖ + 2) := by positivity
    have hadd : A * (‖s‖ + 2) * Real.log (‖s‖ + 2) =
        A * ‖s‖ * Real.log (‖s‖ + 2) + 2 * A * Real.log (‖s‖ + 2) := by ring
    nlinarith

/-- **UNCONDITIONAL RIEMANN–VON MANGOLDT ZERO-COUNT BOUND ON BALLS (`0` ASSUMPTIONS!)**:
there exists `C > 0` such that for all `R ≥ 2` and every finite set `Z` of critical-strip zeros
of Mathlib's `riemannZeta` with `‖ρ‖ ≤ R`, `(Z.card : ℝ) ≤ C * R * Real.log (R + 2)`. -/
theorem riemannZeta_zero_count_ball_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 2 ≤ R → ∀ Z : Finset ℂ,
        (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ ‖ρ‖ ≤ R) →
        (Z.card : ℝ) ≤ C * R * Real.log (R + 2) := by
  obtain ⟨A, hA, B, hB, hxi⟩ := hasOrderOneGrowth_xi
  have hxi0 : xi 0 ≠ 0 := by simp
  set C : ℝ := (4 * A + max B 0 + max (-Real.log ‖xi 0‖) 0) / Real.log 2
  have hC_pos : 0 < C := div_pos (by linarith [le_max_right B 0, le_max_right (-Real.log ‖xi 0‖) 0])
    (Real.log_pos (by norm_num))
  refine ⟨C, hC_pos, fun R hR Z hZ => ?_⟩
  refine order_one_zero_count_le hA.le hxi hxi0 R (by linarith) Z ?_ ?_
  · intro ρ hρ
    exact mem_closedBall_zero_iff.mpr (hZ ρ hρ).2.2.2
  · intro ρ hρ
    have h := hZ ρ hρ
    exact (xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨h.1, h.2.1, h.2.2.1⟩

/-- **UNCONDITIONAL RIEMANN–VON MANGOLDT ZERO-COUNT BOUND UP TO HEIGHT `T` (`0` ASSUMPTIONS!)**:
there exists `C > 0` such that for all `T ≥ 2` and every finite set `Z` of critical-strip zeros
of Mathlib's `riemannZeta` with `|ρ.im| ≤ T`, `(Z.card : ℝ) ≤ C * T * Real.log (T + 2)`. -/
theorem riemannZeta_zero_count_height_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
        (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ T) →
        (Z.card : ℝ) ≤ C * T * Real.log (T + 2) := by
  obtain ⟨C₀, hC₀, hball⟩ := riemannZeta_zero_count_ball_le
  refine ⟨4 * C₀, by positivity, fun T hT Z hZ => ?_⟩
  have hball_bd := hball (2 * T) (by linarith) Z (fun ρ hρ => by
    have h := hZ ρ hρ
    refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    have htri := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos h.1] at htri
    linarith [h.2.1, h.2.2.2])
  have hlog : Real.log (2 * T + 2) ≤ 2 * Real.log (T + 2) := by
    have hsq : 2 * T + 2 ≤ (T + 2) ^ 2 := by nlinarith
    calc Real.log (2 * T + 2)
        ≤ Real.log ((T + 2) ^ 2) := Real.log_le_log (by linarith) hsq
      _ = 2 * Real.log (T + 2) := by rw [Real.log_pow]; norm_num
  have hmul : C₀ * (2 * T) * Real.log (2 * T + 2) ≤ 4 * C₀ * T * Real.log (T + 2) := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ C₀ * (2 * T))
    linarith
  exact hball_bd.trans hmul

/-! ## Section 3: Unconditional Short-Interval Zero-Count Bound `N(T + 1) - N(T) ≤ C log(|T| + 2)` -/

/-- Elementary hyperbolic-sine inequality: `Real.sinh x ≤ x * Real.exp x` for all `x ≥ 0`. -/
private lemma sinh_le_mul_exp {x : ℝ} (_hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.exp x := by
  rw [Real.sinh_eq]
  have h1 : -2 * x + 1 ≤ Real.exp (-2 * x) := Real.add_one_le_exp (-2 * x)
  have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos x).le
  have hexp : Real.exp (-2 * x) * Real.exp x = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp] at h2
  linarith

/-- Sharp exponential lower bound on the 1-line for Mathlib's `Complex.Gamma`:
`Real.exp (-Real.pi * |t| / 2) ≤ ‖Complex.Gamma (1 + I * t)‖` for all `t : ℝ`. -/
theorem norm_Gamma_one_add_I_mul_ge (t : ℝ) :
    Real.exp (-Real.pi * |t| / 2) ≤ ‖Complex.Gamma (1 + I * (t : ℂ))‖ := by
  by_cases ht : t = 0
  · subst ht
    simp [Complex.Gamma_one]
  · have hsq := norm_sq_Gamma_one_add_I_mul ht
    have hpi_t_pos : 0 < Real.pi * |t| := mul_pos Real.pi_pos (abs_pos.mpr ht)
    have hratio : Real.pi * t / Real.sinh (Real.pi * t) =
        Real.pi * |t| / Real.sinh (Real.pi * |t|) := by
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · rw [abs_of_neg hlt, mul_neg, Real.sinh_neg, div_neg, neg_div, neg_neg]
      · rw [abs_of_pos hgt]
    rw [hratio] at hsq
    have hsinh_pos : 0 < Real.sinh (Real.pi * |t|) := by
      rw [Real.sinh_eq]
      have hlt : Real.exp (-(Real.pi * |t|)) < Real.exp (Real.pi * |t|) :=
        Real.exp_lt_exp.mpr (by linarith)
      linarith
    have hsinh_le : Real.sinh (Real.pi * |t|) ≤ (Real.pi * |t|) * Real.exp (Real.pi * |t|) :=
      sinh_le_mul_exp hpi_t_pos.le
    have hsq_ge : (Real.exp (-Real.pi * |t| / 2)) ^ 2 ≤ ‖Complex.Gamma (1 + I * (t : ℂ))‖ ^ 2 := by
      rw [hsq, ← Real.exp_nat_mul]
      have harg : ((2 : ℕ) : ℝ) * (-Real.pi * |t| / 2) = -(Real.pi * |t|) := by push_cast; ring
      rw [harg, Real.exp_neg, le_div_iff₀ hsinh_pos, inv_mul_le_iff₀ (Real.exp_pos _)]
      linarith
    nlinarith [sq_nonneg (‖Complex.Gamma (1 + I * (t : ℂ))‖ - Real.exp (-Real.pi * |t| / 2)),
      norm_nonneg (Complex.Gamma (1 + I * (t : ℂ))), Real.exp_pos (-Real.pi * |t| / 2)]

/-- **Exact Exponential Lower Bound for `xi` on the 2-line**:
for every `T : ℝ`, `(1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) ≤ ‖xi (2 + I * T)‖`. -/
theorem norm_xi_two_add_I_mul_ge (T : ℝ) :
    (1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) ≤ ‖xi ((2 : ℂ) + I * (T : ℂ))‖ := by
  set s : ℂ := (2 : ℂ) + I * (T : ℂ)
  have hs_re : s.re = 2 := by simp [s]
  have hs0 : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs_re; norm_num at hs_re
  have hs1 : s ≠ 1 := by intro h; rw [h, Complex.one_re] at hs_re; norm_num at hs_re
  have hs_gt1 : 1 < s.re := by linarith
  have hdef : xi s = s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) *
      Complex.Gamma (s / 2) * riemannZeta s) := by
    rw [xi_eq_mul_completedRiemannZeta hs0 hs1, completedZeta_eq_tsum_of_one_lt_re hs_gt1,
      ← zeta_eq_tsum_one_div_nat_cpow hs_gt1]
  rw [hdef, norm_mul, norm_mul, norm_mul, norm_mul]
  -- 1. `‖s‖ ≥ 2` and `‖s - 1‖ ≥ 1`
  have hs_ge2 : (2 : ℝ) ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    rw [hs_re, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact h
  have hs1_ge1 : (1 : ℝ) ≤ ‖s - 1‖ := by
    have h := Complex.abs_re_le_norm (s - 1)
    have hre : (s - 1).re = 1 := by simp [hs_re]; norm_num
    rw [hre, abs_of_pos zero_lt_one] at h
    exact h
  -- 2. `‖π^(-s/2)‖ = 1 / π`
  have hpi_eq : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = 1 / Real.pi := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-s / 2).re = -1 := by simp [hs_re]
    rw [hre, Real.rpow_neg_one, one_div]
  -- 3. `‖Γ(s/2)‖ ≥ exp(-π |T| / 4)`
  have hG_ge : Real.exp (-Real.pi * |T| / 4) ≤ ‖Complex.Gamma (s / 2)‖ := by
    have hs2 : s / 2 = 1 + I * ((T / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s]
    rw [hs2]
    have h := norm_Gamma_one_add_I_mul_ge (T / 2)
    have habs : -Real.pi * |T / 2| / 2 = -Real.pi * |T| / 4 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    rwa [habs] at h
  -- 4. `‖ζ(2 + I * T)‖ ≥ 1 / 2` from `‖1 / ζ(2 + I * T)‖ ≤ 2`
  have hZ_ge : (1 / 2 : ℝ) ≤ ‖riemannZeta s‖ := by
    have hinv := norm_riemannZeta_and_inv_of_one_lt_re (σ := 2) (by norm_num) T
    have hinv2 : ‖1 / riemannZeta s‖ ≤ 2 := by
      have h1 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
      have hs_eq : ((2 : ℝ) : ℂ) + I * (T : ℂ) = s := by simp [s]
      rw [hs_eq] at hinv
      exact (hinv.2.1.trans hinv.2.2).trans (le_of_eq h1)
    have hnz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hnz
    rw [norm_div, norm_one, div_le_iff₀ hpos] at hinv2
    linarith
  rw [hpi_eq]
  have hstep1 : (2 : ℝ) ≤ ‖s‖ * ‖s - 1‖ := by nlinarith
  have hstep2 : (1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) * (1 / 2) ≤
      (1 / Real.pi) * ‖Complex.Gamma (s / 2)‖ * ‖riemannZeta s‖ := by
    have h1 : (1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) ≤
        (1 / Real.pi) * ‖Complex.Gamma (s / 2)‖ :=
      mul_le_mul_of_nonneg_left hG_ge (by positivity)
    exact mul_le_mul h1 hZ_ge (by norm_num) (by positivity)
  have hstep3 := mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
  linarith [show (2 : ℝ) * (1 / Real.pi * Real.exp (-Real.pi * |T| / 4) * (1 / 2)) =
      1 / Real.pi * Real.exp (-Real.pi * |T| / 4) by ring]

/-- **Vertical-Strip Stirling Exponential Decay of `xi` on `-2 ≤ Re(s) ≤ 6`**:
there exists `K > 0` such that for every `s : ℂ` with `-2 ≤ s.re ≤ 6`,
`‖xi s‖ ≤ K * (|s.im| + 2) ^ 7 * Real.exp (-Real.pi * |s.im| / 4)`. -/
theorem norm_xi_strip_stirling_decay :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 6 →
      ‖xi s‖ ≤ K * (|s.im| + 2) ^ 7 * Real.exp (-Real.pi * |s.im| / 4) := by
  obtain ⟨Cg, hCg_pos, hCg⟩ := norm_Gamma_strip_stirling_upper 4
  obtain ⟨Cs, hCs_pos, hCs⟩ := norm_xi_bounded_on_strip (1 / 2) 2
  set K₁ : ℝ := 192 * Cg
  set K₂ : ℝ := 16 * Cs * Real.exp (Real.pi / 4)
  set K : ℝ := max K₁ K₂
  have hK_pos : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left K₁ K₂)
  -- First prove the bound for `1 / 2 ≤ w.re ≤ 6`.
  have hright : ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 6 →
      ‖xi w‖ ≤ K * (|w.im| + 2) ^ 7 * Real.exp (-Real.pi * |w.im| / 4) := by
    intro w hlo hhi
    by_cases hbox : w.re ≤ 2 ∧ |w.im| ≤ 1
    · -- Compact box `[1/2, 2] × [-1, 1]`: use `norm_xi_bounded_on_strip`.
      have hst := hCs w hlo hbox.1
      have hnorm_w : ‖w‖ ≤ 3 := by
        have htri := Complex.norm_le_abs_re_add_abs_im w
        rw [abs_of_pos (by linarith : 0 < w.re)] at htri
        linarith [hbox.1, hbox.2]
      have hsq : (‖w‖ + 1) ^ 2 ≤ 16 := by nlinarith [norm_nonneg w]
      have hpow7 : (1 : ℝ) ≤ (|w.im| + 2) ^ 7 := by
        exact one_le_pow₀ (by linarith [abs_nonneg w.im])
      have hexp_ge : Real.exp (-Real.pi / 4) ≤ Real.exp (-Real.pi * |w.im| / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, hbox.2]
      have hprod : Real.exp (Real.pi / 4) * Real.exp (-Real.pi / 4) = 1 := by
        rw [← Real.exp_add, show Real.pi / 4 + -Real.pi / 4 = 0 by ring, Real.exp_zero]
      calc ‖xi w‖ ≤ Cs * (‖w‖ + 1) ^ 2 := hst
        _ ≤ Cs * 16 := mul_le_mul_of_nonneg_left hsq hCs_pos.le
        _ = (16 * Cs * Real.exp (Real.pi / 4)) * Real.exp (-Real.pi / 4) := by
            rw [mul_assoc, hprod, mul_one]; ring
        _ ≤ K₂ * Real.exp (-Real.pi * |w.im| / 4) :=
            mul_le_mul_of_nonneg_left hexp_ge (by positivity)
        _ ≤ K * Real.exp (-Real.pi * |w.im| / 4) :=
            mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) (Real.exp_pos _).le
        _ ≤ K * (|w.im| + 2) ^ 7 * Real.exp (-Real.pi * |w.im| / 4) := by
            have h1 : K ≤ K * (|w.im| + 2) ^ 7 := by nlinarith
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    · -- Away from the box: either `2 < w.re ≤ 6` or (`1/2 ≤ w.re ≤ 2` and `1 < |w.im|`).
      have hw0 : w ≠ 0 := by intro h; rw [h, Complex.zero_re] at hlo; linarith
      have hw1 : w ≠ 1 := by
        intro h; apply hbox; rw [h, Complex.one_re, Complex.one_im, abs_zero]
        exact ⟨by norm_num, by norm_num⟩
      have hGnz : w.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
      have hdef : xi w = w * (w - 1) * ((Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)) *
          riemannZeta w := by
        rw [xi_eq_mul_Gammaℝ_mul_riemannZeta hw0 hw1 hGnz, Complex.Gammaℝ_def]
      rw [hdef, norm_mul, norm_mul, norm_mul, norm_mul]
      -- Bound `‖ζ(w)‖ ≤ 3 * (|w.im| + 2)`
      have hZ_le : ‖riemannZeta w‖ ≤ 3 * (|w.im| + 2) := by
        by_cases hw2 : 2 ≤ w.re
        · exact (norm_riemannZeta_le_two_of_two_le_re hw2).trans (by linarith [abs_nonneg w.im])
        · push Not at hw2
          have him1 : 1 ≤ |w.im| := by
            by_contra hlt; push Not at hlt
            exact hbox ⟨hw2.le, hlt.le⟩
          exact norm_riemannZeta_strip_le hlo hw2.le him1
      -- Bound `‖w * (w - 1)‖ ≤ 16 * (|w.im| + 2)^2`
      have hnorm_w : ‖w‖ ≤ |w.im| + 6 := by
        have htri := Complex.norm_le_abs_re_add_abs_im w
        rw [abs_of_pos (by linarith : 0 < w.re)] at htri
        linarith
      have hpoly : ‖w‖ * ‖w - 1‖ ≤ 16 * (|w.im| + 2) ^ 2 := by
        have h1 : ‖w‖ ≤ 4 * (|w.im| + 2) := by linarith [abs_nonneg w.im]
        have h2 : ‖w - 1‖ ≤ 4 * (|w.im| + 2) := by
          have htri : ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w 1
          linarith [abs_nonneg w.im]
        nlinarith [norm_nonneg w, norm_nonneg (w - 1)]
      -- Bound `‖π^(-w/2)‖ ≤ 1`
      have hpi_le : ‖(Real.pi : ℂ) ^ (-w / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        have hre : (-w / 2).re = -w.re / 2 := by simp
        rw [hre]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi]) (by linarith)
      -- Bound `‖Γ(w/2)‖ = ‖Γ(w/2 + 1)‖ / ‖w/2‖ ≤ 4 * Cg * (|w.im| + 2)^4 * exp(-π |w.im| / 4)`
      have hG_le : ‖Complex.Gamma (w / 2)‖ ≤
          4 * Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4) := by
        have hw2_ne : w / 2 ≠ 0 := div_ne_zero hw0 (by norm_num)
        have hrec := Complex.Gamma_add_one (w / 2) hw2_ne
        have hw2_norm : (1 / 4 : ℝ) ≤ ‖w / 2‖ := by
          have h := Complex.abs_re_le_norm (w / 2)
          have hre : (w / 2).re = w.re / 2 := by simp
          rw [hre, abs_of_pos (by linarith : 0 < w.re / 2)] at h
          linarith
        have hdiv : ‖Complex.Gamma (w / 2)‖ ≤ 4 * ‖Complex.Gamma (w / 2 + 1)‖ := by
          have hnorm := congrArg norm hrec
          rw [norm_mul] at hnorm
          have hpos : 0 < ‖w / 2‖ := by linarith
          have h1 : ‖Complex.Gamma (w / 2)‖ = ‖Complex.Gamma (w / 2 + 1)‖ / ‖w / 2‖ := by
            rw [hnorm, mul_div_cancel_left₀ _ hpos.ne']
          rw [h1, div_le_iff₀ hpos]
          nlinarith [norm_nonneg (Complex.Gamma (w / 2 + 1))]
        have hsplit : w / 2 + 1 = ((w.re / 2 + 1 : ℝ) : ℂ) + I * ((w.im / 2 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        have hσ_mem : w.re / 2 + 1 ∈ Set.Icc (1 / 2 : ℝ) 4 := ⟨by linarith, by linarith⟩
        have hst := hCg (w.re / 2 + 1) hσ_mem (w.im / 2)
        rw [← hsplit] at hst
        have habs_im : -Real.pi * |w.im / 2| / 2 = -Real.pi * |w.im| / 4 := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
        rw [habs_im] at hst
        have hpow_le : (|w.im / 2| + 2) ^ (w.re / 2 + 1 - 1 / 2) ≤ (|w.im| + 2) ^ (4 : ℕ) := by
          have hbase1 : |w.im / 2| + 2 ≤ |w.im| + 2 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            linarith [abs_nonneg w.im]
          have hbase_ge1 : (1 : ℝ) ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
          have hexp_le : w.re / 2 + 1 - 1 / 2 ≤ (4 : ℝ) := by linarith
          calc (|w.im / 2| + 2) ^ (w.re / 2 + 1 - 1 / 2)
              ≤ (|w.im| + 2) ^ (w.re / 2 + 1 - 1 / 2) :=
                Real.rpow_le_rpow (by positivity) hbase1 (by linarith)
            _ ≤ (|w.im| + 2) ^ (4 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hbase_ge1 hexp_le
            _ = (|w.im| + 2) ^ (4 : ℕ) := Real.rpow_natCast _ 4
        have hst2 : ‖Complex.Gamma (w / 2 + 1)‖ ≤
            Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4) := by
          refine hst.trans ?_
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow_le hCg_pos.le) (Real.exp_pos _).le
        linarith
      -- Combine all four bounds
      have hGpi : ‖(Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖ ≤
          4 * Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4) := by
        calc ‖(Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖
            ≤ 1 * (4 * Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4)) :=
              mul_le_mul hpi_le hG_le (norm_nonneg _) zero_le_one
          _ = 4 * Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4) := one_mul _
      have hcomb1 : ‖w‖ * ‖w - 1‖ * (‖(Real.pi : ℂ) ^ (-w / 2)‖ * ‖Complex.Gamma (w / 2)‖) ≤
          (16 * (|w.im| + 2) ^ 2) * (4 * Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4)) :=
        mul_le_mul hpoly hGpi (by positivity) (by positivity)
      have hcomb2 := mul_le_mul hcomb1 hZ_le (norm_nonneg _) (by positivity)
      have hK1_le : K₁ ≤ K := le_max_left K₁ K₂
      have hsimp : (16 * (|w.im| + 2) ^ 2) *
            (4 * Cg * (|w.im| + 2) ^ 4 * Real.exp (-Real.pi * |w.im| / 4)) * (3 * (|w.im| + 2)) =
          K₁ * (|w.im| + 2) ^ 7 * Real.exp (-Real.pi * |w.im| / 4) := by
        dsimp only [K₁]; ring
      rw [hsimp] at hcomb2
      exact hcomb2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK1_le (by positivity)) (Real.exp_pos _).le)
  -- Reflect `-2 ≤ s.re < 1 / 2` across `Re(s) = 1 / 2` using `xi (1 - s) = xi s`.
  refine ⟨K, hK_pos, fun s hlo hhi => ?_⟩
  rcases le_or_gt (1 / 2 : ℝ) s.re with hs | hs
  · exact hright s hs hhi
  · rw [← xi_one_sub s]
    have hre1 : 1 / 2 ≤ (1 - s).re := by simp; linarith
    have hre2 : (1 - s).re ≤ 6 := by simp; linarith
    have him : |(1 - s).im| = |s.im| := by simp
    simpa [him] using hright (1 - s) hre1 hre2

/-- **UNCONDITIONAL SHORT-INTERVAL ZERO-COUNT BOUND `N(T + 1) - N(T) ≤ C log(|T| + 2)` (`0` ASSUMPTIONS!)**:
proved via Jensen's formula on `xi` centered at `s₀ = 2 + I * T` with `r = 3`, `R = 4`, using
`‖1 / ζ(2 + I * T)‖ ≤ 2` and the exact cancellation of `exp(-π |T| / 4)`. -/
theorem riemannZeta_zero_count_unit_interval_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, ∀ Z : Finset ℂ,
        (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1) →
        (Z.card : ℝ) ≤ C * Real.log (|T| + 2) := by
  obtain ⟨K, hK_pos, hK⟩ := norm_xi_strip_stirling_decay
  set A₀ : ℝ := Real.pi * K * (3 : ℝ) ^ 7 * Real.exp Real.pi
  have hA₀_pos : 0 < A₀ := by positivity
  set log43 : ℝ := Real.log (4 / 3)
  have hlog43_pos : 0 < log43 := Real.log_pos (by norm_num)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := (max (Real.log A₀) 0 / Real.log 2 + 7) / log43
  have hC_pos : 0 < C := by
    have : 0 ≤ max (Real.log A₀) 0 / Real.log 2 := div_nonneg (le_max_right _ _) hlog2_pos.le
    exact div_pos (by linarith) hlog43_pos
  refine ⟨C, hC_pos, fun T Z hZ => ?_⟩
  classical
  set s₀ : ℂ := (2 : ℂ) + I * (T : ℂ)
  set g : ℂ → ℂ := fun w => xi (s₀ + w)
  have hg_diff : Differentiable ℂ g :=
    differentiable_xi.comp ((differentiable_const s₀).add differentiable_id)
  have hg0_ge : (1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) ≤ ‖g 0‖ := by
    simpa [g, s₀] using norm_xi_two_add_I_mul_ge T
  have hg0_ne : g 0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hg0_ge
    have hpos : (0 : ℝ) < (1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) := by positivity
    linarith
  set M : ℝ := K * (3 * (|T| + 2)) ^ 7 * Real.exp Real.pi * Real.exp (-Real.pi * |T| / 4)
  have hM_bound : ∀ w ∈ sphere (0 : ℂ) 4, ‖g w‖ ≤ M := by
    intro w hw
    have hwn : ‖w‖ = 4 := mem_sphere_zero_iff_norm.mp hw
    have hw_re : |w.re| ≤ 4 := (Complex.abs_re_le_norm w).trans hwn.le
    have hw_im : |w.im| ≤ 4 := (Complex.abs_im_le_norm w).trans hwn.le
    set z : ℂ := s₀ + w
    have hz_re_eq : z.re = 2 + w.re := by simp [z, s₀]
    have hz_im_eq : z.im = T + w.im := by simp [z, s₀]
    have hz_re_lo : -2 ≤ z.re := by linarith [(abs_le.mp hw_re).1]
    have hz_re_hi : z.re ≤ 6 := by linarith [(abs_le.mp hw_re).2]
    have hz_im_hi : |z.im| + 2 ≤ 3 * (|T| + 2) := by
      have htri : |z.im| ≤ |T| + |w.im| := by rw [hz_im_eq]; exact abs_add_le T w.im
      linarith [abs_nonneg T]
    have hz_im_lo : -|z.im| ≤ 4 - |T| := by
      have htri : |T| ≤ |z.im| + |w.im| := by
        have := abs_sub_le (T + w.im) w.im 0
        have h1 : T + w.im - w.im = T := by ring
        rw [hz_im_eq]
        have h2 := abs_add_le (T + w.im) (-w.im)
        rw [add_neg_cancel_right, abs_neg] at h2
        exact h2
      linarith
    have hxi_z := hK z hz_re_lo hz_re_hi
    have hpow : (|z.im| + 2) ^ 7 ≤ (3 * (|T| + 2)) ^ 7 :=
      pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) hz_im_hi 7
    have hexp : Real.exp (-Real.pi * |z.im| / 4) ≤
        Real.exp Real.pi * Real.exp (-Real.pi * |T| / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    change ‖xi z‖ ≤ M
    calc ‖xi z‖
        ≤ K * (|z.im| + 2) ^ 7 * Real.exp (-Real.pi * |z.im| / 4) := hxi_z
      _ ≤ K * (3 * (|T| + 2)) ^ 7 * (Real.exp Real.pi * Real.exp (-Real.pi * |T| / 4)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hK_pos.le) hexp (Real.exp_pos _).le (by positivity)
      _ = M := by dsimp only [M]; ring
  -- Shift the finite zero set `Z` by `-s₀` into `closedBall 0 3`.
  let W : Finset ℂ := Z.image (fun ρ => ρ - s₀)
  have hW_card : W.card = Z.card :=
    Finset.card_image_of_injective Z (fun a b hab => by linear_combination hab)
  have hW_ball : ∀ w ∈ W, w ∈ closedBall (0 : ℂ) 3 := by
    intro w hw
    obtain ⟨ρ, hρZ, rfl⟩ := Finset.mem_image.mp hw
    have h := hZ ρ hρZ
    rw [mem_closedBall_zero_iff]
    have hre : (ρ - s₀).re = ρ.re - 2 := by simp [s₀]
    have him : (ρ - s₀).im = ρ.im - T := by simp [s₀]
    have htri := Complex.norm_le_abs_re_add_abs_im (ρ - s₀)
    rw [hre, him, abs_of_neg (by linarith : ρ.re - 2 < 0), abs_of_nonneg (by linarith : 0 ≤ ρ.im - T)] at htri
    linarith [h.1, h.2.2.2.2]
  have hW_zero : ∀ w ∈ W, g w = 0 := by
    intro w hw
    obtain ⟨ρ, hρZ, rfl⟩ := Finset.mem_image.mp hw
    have h := hZ ρ hρZ
    change xi (s₀ + (ρ - s₀)) = 0
    rw [add_sub_cancel]
    exact (xi_eq_zero_iff_critical_strip_zeta_zero ρ).mpr ⟨h.1, h.2.1, h.2.2.1⟩
  have hj := jensen_zero_count_le (r := 3) (R := 4) (by norm_num) (by norm_num)
    hg_diff.diffContOnCl hg0_ne hM_bound W hW_ball hW_zero
  rw [hW_card] at hj
  -- Cancel `exp(-π |T| / 4)` in `M / ‖g 0‖`!
  have hratio_le : M / ‖g 0‖ ≤ A₀ * (|T| + 2) ^ 7 := by
    have hM_eq : M = (A₀ * (|T| + 2) ^ 7) * ((1 / Real.pi) * Real.exp (-Real.pi * |T| / 4)) := by
      dsimp only [M, A₀]
      rw [mul_pow]
      field_simp [Real.pi_pos.ne']
    rw [hM_eq]
    have hpos_den : (0 : ℝ) < (1 / Real.pi) * Real.exp (-Real.pi * |T| / 4) := by positivity
    rw [div_le_iff₀ (norm_pos_iff.mpr hg0_ne)]
    exact mul_le_mul_of_nonneg_left hg0_ge (by positivity)
  have hM_pos : 0 < M := by positivity
  have hlog_le : Real.log (M / ‖g 0‖) ≤
      (max (Real.log A₀) 0 / Real.log 2 + 7) * Real.log (|T| + 2) := by
    have h1 : Real.log (M / ‖g 0‖) ≤ Real.log (A₀ * (|T| + 2) ^ 7) :=
      Real.log_le_log (div_pos hM_pos (norm_pos_iff.mpr hg0_ne)) hratio_le
    rw [Real.log_mul hA₀_pos.ne' (by positivity), Real.log_pow] at h1
    have hlogT_ge : Real.log 2 ≤ Real.log (|T| + 2) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg T])
    have hA_term : Real.log A₀ ≤ (max (Real.log A₀) 0 / Real.log 2) * Real.log (|T| + 2) := by
      have h2 : max (Real.log A₀) 0 ≤ (max (Real.log A₀) 0 / Real.log 2) * Real.log (|T| + 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
        exact mul_le_mul_of_nonneg_left hlogT_ge (le_max_right _ _)
      exact (le_max_left _ _).trans h2
    push_cast at h1
    linarith
  calc (Z.card : ℝ)
      ≤ Real.log (M / ‖g 0‖) / log43 := hj
    _ ≤ ((max (Real.log A₀) 0 / Real.log 2 + 7) * Real.log (|T| + 2)) / log43 :=
        div_le_div_of_nonneg_right hlog_le hlog43_pos.le
    _ = C * Real.log (|T| + 2) := by dsimp only [C]; ring

/-- Nonnegative-height form of the short-interval zero-count bound:
`N(T + 1) - N(T) ≤ C * Real.log (T + 2)` for all `T ≥ 0`. -/
theorem riemannZeta_zero_count_unit_interval_le_nonneg :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 0 ≤ T → ∀ Z : Finset ℂ,
        (∀ ρ ∈ Z, 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ T ≤ ρ.im ∧ ρ.im ≤ T + 1) →
        (Z.card : ℝ) ≤ C * Real.log (T + 2) := by
  obtain ⟨C, hC, hbd⟩ := riemannZeta_zero_count_unit_interval_le
  refine ⟨C, hC, fun T hT Z hZ => ?_⟩
  simpa [abs_of_nonneg hT] using hbd T Z hZ

/-! ## Section 4: Unconditional Discreteness, Finiteness, & Zero-Sequence Summability -/

/-- **Unconditional Finiteness of Critical-Strip Zeros up to Any Bounded Height `T`**:
for every `T : ℝ`, `{ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ T}` is finite. -/
theorem finite_riemannZeta_zeros_le_height (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ T}.Finite := by
  obtain ⟨C, _, hbd⟩ := riemannZeta_zero_count_height_le
  set T' : ℝ := max T 2
  have hT'2 : 2 ≤ T' := le_max_right T 2
  by_contra hinf
  obtain ⟨Z, hZsub, hZcard⟩ :=
    Set.Infinite.exists_subset_card_eq hinf (Nat.floor (C * T' * Real.log (T' + 2)) + 1)
  have hle := hbd T' hT'2 Z (fun ρ hρ => by
    have h := hZsub hρ
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans (le_max_left T 2)⟩)
  have hgt : C * T' * Real.log (T' + 2) < (Z.card : ℝ) := by
    rw [hZcard]
    push_cast
    exact Nat.lt_floor_add_one _
  linarith

/-- Unconditional finiteness of critical-strip zeros in any closed ball `‖ρ‖ ≤ R`. -/
theorem finite_riemannZeta_zeros_in_ball (R : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ ‖ρ‖ ≤ R}.Finite := by
  refine (finite_riemannZeta_zeros_le_height R).subset fun ρ hρ => ?_
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, (Complex.abs_im_le_norm ρ).trans hρ.2.2.2⟩

/-- Unconditional countability of the set of all critical-strip zeros of Mathlib's `riemannZeta`. -/
theorem countable_critical_strip_riemannZeta_zeros :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}.Countable := by
  have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0} ⊆
      ⋃ n : ℕ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 ∧ |ρ.im| ≤ (n : ℝ)} := by
    intro ρ hρ
    refine Set.mem_iUnion.mpr ⟨⌈|ρ.im|⌉₊, hρ.1, hρ.2.1, hρ.2.2, Nat.le_ceil |ρ.im|⟩
  exact (Set.countable_iUnion fun n : ℕ => (finite_riemannZeta_zeros_le_height (n : ℝ)).countable).mono hsub

/-- **UNCONDITIONAL CONVERGENCE-EXPONENT SUMMABILITY OF `riemannZeta` ZEROS (`0` ASSUMPTIONS!)**:
for EVERY injective enumeration `ρ : ℕ → ℂ` of critical-strip zeros of Mathlib's `riemannZeta`
and EVERY `σ > 1`, `∑' n, ‖ρ n‖ ^ (-σ)` converges unconditionally! -/
theorem riemannZeta_zeros_summable_rpow_neg {ρ : ℕ → ℂ} (hinj : Function.Injective ρ)
    (hzeros : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1 ∧ riemannZeta (ρ n) = 0)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n => ‖ρ n‖ ^ (-σ)) := by
  obtain ⟨A, hA, B, _, hxi⟩ := hasOrderOneGrowth_xi
  have hxi0 : xi 0 ≠ 0 := by simp
  refine order_one_zero_seq_summable_rpow_neg hA.le hxi hxi0 hinj (fun n => ?_) hσ
  exact (xi_eq_zero_iff_critical_strip_zeta_zero (ρ n)).mpr (hzeros n)

/-- **UNCONDITIONAL INVERSE-SQUARE SUMMABILITY OF `riemannZeta` ZEROS (`0` ASSUMPTIONS!)**:
for EVERY injective enumeration `ρ : ℕ → ℂ` of critical-strip zeros of Mathlib's `riemannZeta`,
`∑' n, (‖ρ n‖ ^ 2)⁻¹` converges unconditionally! -/
theorem riemannZeta_zeros_summable_inv_sq {ρ : ℕ → ℂ} (hinj : Function.Injective ρ)
    (hzeros : ∀ n, 0 < (ρ n).re ∧ (ρ n).re < 1 ∧ riemannZeta (ρ n) = 0) :
    Summable (fun n => (‖ρ n‖ ^ 2)⁻¹) := by
  obtain ⟨A, hA, B, _, hxi⟩ := hasOrderOneGrowth_xi
  have hxi0 : xi 0 ≠ 0 := by simp
  refine order_one_zero_seq_summable_inv_sq hA.le hxi hxi0 hinj (fun n => ?_)
  exact (xi_eq_zero_iff_critical_strip_zeta_zero (ρ n)).mpr (hzeros n)

end RHDirect.Stage6XiZeroDensity
