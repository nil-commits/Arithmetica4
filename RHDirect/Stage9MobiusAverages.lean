import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage5StirlingPhragmen
import RHDirect.Stage5ContourExplicit
import RHDirect.Stage6EffectivePNT
import RHDirect.Stage7VonMangoldtExplicit
import RHDirect.Stage8MertensTheorems
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic

/-!
# RHDirect.Stage9MobiusAverages

**UNCONDITIONAL EFFECTIVE MÖBIUS SUMMATORY CANCELLATION (`|M(x)| ≤ C x exp(-c √(log x))`),
`∑' n, μ(n) / n = 0`, LITTLEWOOD'S BIDIRECTIONAL EQUIVALENCE `RH ↔ M(x) = O(x^{1/2+ε})`,
AND EXACT CLASSICAL AVERAGE ORDERS OF `μ²(n)`, `φ(n)`, `σ₁(n)`, AND `σ₀(n)`**
(0 assumptions, 0 `sorry`, 0 custom `axiom`s) in pure Mathlib `v4.33.1`.

## Main Results
1. **Unconditional Effective Mertens Function Bound & von Mangoldt–Landau Cancellation**:
   - `mertensM x = ∑_{1 ≤ n ≤ ⌊x⌋₊} (μ(n) : ℝ)`,
   - `effective_mertens_bound`:
     `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |mertensM x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`,
   - `mertensM_little_o`: `Tendsto (fun x => mertensM x / x) atTop (𝓝 0)`,
   - `tsum_moebius_div_nat_eq_zero`:
     `Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / n) atTop (𝓝 0)`.
2. **Littlewood's 1912 Bidirectional Equivalence (`RH ↔ M(x) = O(x^{1/2 + ε})`)**:
   - `riemannHypothesis_iff_mertensM_sqrt_eps`:
     `RiemannHypothesis ↔ ∀ ε > 0, ∃ C > 0, ∀ x ≥ 2, |mertensM x| ≤ C * x ^ (1/2 + ε)`.
3. **Exact Classical Average Orders (`6/π²`, `3/π²`, `π²/12`, Dirichlet Hyperbola)**:
   - `squarefree_counting_asymp`:
     `∃ C > 0, ∀ x ≥ 1, |#({n ∈ [1, ⌊x⌋₊] | Squarefree n}) - (6 / π²) x| ≤ C √x`,
   - `sum_totient_asymp`:
     `∃ C > 0, ∀ x ≥ 2, |∑_{1 ≤ n ≤ ⌊x⌋₊} φ(n) - (3 / π²) x²| ≤ C x log x`,
   - `coprime_pairs_density`:
     `#({(a, b) ∈ [1, N]² | Coprime a b}) / N² → 6 / π²`,
   - `sum_sigma_one_asymp`:
     `∃ C > 0, ∀ x ≥ 2, |∑_{1 ≤ n ≤ ⌊x⌋₊} σ₁(n) - (π² / 12) x²| ≤ C x log x`,
   - `sum_sigma_zero_asymp`:
     `∃ C > 0, ∀ x ≥ 1, |∑_{1 ≤ n ≤ ⌊x⌋₊} σ₀(n) - x (log x + 2 γ - 1)| ≤ C √x`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped BigOperators Real

namespace RHDirect.Stage9MobiusAverages

/-! ## Section 1: Core Definitions, Basic `μ` / `M(x)` Properties, & Holomorphic `1 / ζ(s)` -/

/-- The Mertens summatory function `M(x) = ∑_{1 ≤ n ≤ ⌊x⌋₊} μ(n)`. -/
def mertensM (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)

/-- Holomorphic regularization of `1 / riemannZeta z` on `{z | 0 < z.re ∧ zetaReg z ≠ 0}`,
with a removable zero `invZetaReg 1 = 0` at `z = 1`. -/
def invZetaReg (z : ℂ) : ℂ :=
  (z - 1) / Stage6EffectivePNT.zetaReg z

theorem invZetaReg_one : invZetaReg 1 = 0 := by
  simp [invZetaReg]

theorem invZetaReg_eq_inv_riemannZeta {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1)
    (hnz : riemannZeta z ≠ 0) :
    invZetaReg z = (riemannZeta z)⁻¹ := by
  unfold invZetaReg
  rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hz hz1]
  have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp [hsub, hnz]

theorem differentiableOn_invZetaReg :
    DifferentiableOn ℂ invZetaReg {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} := by
  have hsub : {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} ⊆ {z : ℂ | 0 < z.re} :=
    fun _ hz => hz.1
  unfold invZetaReg
  exact (differentiableOn_id.sub (differentiableOn_const 1)).div
    (Stage6EffectivePNT.differentiableOn_zetaReg.mono hsub) (fun _ hz => hz.2)

lemma abs_moebius_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  by_cases h : Squarefree n
  · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
    push_cast
    rw [abs_pow, abs_neg, abs_one, one_pow]
  · simp [ArithmeticFunction.moebius, h]

lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  have h : (ArithmeticFunction.moebius n : ℂ) = (((ArithmeticFunction.moebius n : ℝ) : ℂ)) := by
    norm_cast
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact abs_moebius_le_one n

lemma abs_mertensM_le {x : ℝ} (hx : 0 ≤ x) : |mertensM x| ≤ x := by
  unfold mertensM
  calc |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := Finset.sum_le_sum fun n _ => abs_moebius_le_one n
    _ = (⌊x⌋₊ : ℝ) := by simp
    _ ≤ x := Nat.floor_le hx

lemma mertensM_eq_realStepSum (x : ℝ) :
    mertensM x = Stage8MertensTheorems.realStepSum (fun n => (ArithmeticFunction.moebius n : ℝ)) x :=
  rfl

lemma stepSum_moebius_eq_mertensM (x : ℝ) :
    Stage3RealAnalyticLandau.stepSum (fun n => (ArithmeticFunction.moebius n : ℂ)) x =
      (mertensM x : ℂ) := by
  unfold Stage3RealAnalyticLandau.stepSum mertensM
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => by norm_cast

lemma measurable_mertensM : Measurable mertensM := by
  rw [show mertensM = Stage8MertensTheorems.realStepSum (fun n => (ArithmeticFunction.moebius n : ℝ)) from rfl]
  exact Stage8MertensTheorems.measurable_realStepSum _

theorem LSeriesSummable_moebius {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  have hzeta : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  refine Summable.of_norm_bounded hzeta.norm fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one, norm_div]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    simpa using norm_moebius_le_one n

theorem LSeries_moebius_eq_inv_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s = (riemannZeta s)⁻¹ := by
  have hmul := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hmul
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  exact eq_inv_of_mul_eq_one_right (by simpa using hmul)

theorem inv_riemannZeta_eq_mellin_mertensM {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = s * ∫ t in Ioi (1 : ℝ), (mertensM t : ℂ) * (t : ℂ) ^ (-s - 1) := by
  rw [← LSeries_moebius_eq_inv_riemannZeta hs]
  have hbd : ∀ t : ℝ, 1 ≤ t →
      ‖Stage3RealAnalyticLandau.stepSum (fun n => (ArithmeticFunction.moebius n : ℂ)) t‖ ≤
        1 * t ^ (1 : ℝ) := by
    intro t ht
    rw [stepSum_moebius_eq_mertensM, Complex.norm_real, Real.norm_eq_abs, one_mul, Real.rpow_one]
    exact abs_mertensM_le (zero_le_one.trans ht)
  have hmel := Stage3RealAnalyticLandau.LSeries_eq_mul_mellin_stepSum hbd hs (LSeriesSummable_moebius hs)
  rw [hmel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [stepSum_moebius_eq_mertensM]

/-! ## Section 2: Quantitative `1 / ζ(s)` Bounds in Zero-Free Regions & Hadamard Three-Circles -/

/-- **Unconditional Quantitative `1 / ζ(s)` Bound in the de la Vallée Poussin Zero-Free Region**:
there exist `c₁ > 0` and `C₁ > 0` such that for all `s : ℂ` with `4 ≤ |s.im|` and
`1 - c₁ / Real.log (|s.im| + 2) ≤ s.re ≤ 2`,
`‖(riemannZeta s)⁻¹‖ ≤ C₁ * (Real.log (|s.im| + 2)) ^ 5`. -/
theorem inv_riemannZeta_zeroFree_bound :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ s : ℂ, 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re → s.re ≤ 2 → 4 ≤ |s.im| →
        ‖(riemannZeta s)⁻¹‖ ≤ C₁ * (Real.log (|s.im| + 2)) ^ 5 := by
  obtain ⟨c₀, hc₀_pos, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  set c : ℝ := min c₀ (1 / 4) with hc_def
  have hc_pos : 0 < c := lt_min hc₀_pos (by norm_num)
  have hc_le_c₀ : c ≤ c₀ := min_le_left _ _
  have hc_le_qtr : c ≤ 1 / 4 := min_le_right _ _
  set c₁ : ℝ := c / 16 with hc₁_def
  have hc₁_pos : 0 < c₁ := by positivity
  set C_right : ℝ := 2 / c₁
  set C_left : ℝ := (16 / c) * (1152 / c) ^ 2
  have hC_left_pos : 0 < C_left := by positivity
  set C₁ : ℝ := max C_right C_left
  have hC₁_pos : 0 < C₁ := lt_of_lt_of_le hC_left_pos (le_max_right _ _)
  refine ⟨c₁, hc₁_pos, C₁, hC₁_pos, fun s hre_lo hre_hi him => ?_⟩
  set t : ℝ := s.im
  set L : ℝ := Real.log (|t| + 2) with hL_def
  have hL_gt1 : 1 < L := by
    have h6 : Real.exp 1 < |t| + 2 := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h6)
  have hL_pos : 0 < L := zero_lt_one.trans hL_gt1
  by_cases hright : 1 + c₁ / L ≤ s.re
  · -- Right sub-regime: `s.re ≥ 1 + c₁ / L`
    have hs_re_gt1 : 1 < s.re := by linarith [div_pos hc₁_pos hL_pos]
    have hs_eq : s = (s.re : ℂ) + I * (t : ℂ) := Complex.ext (by simp) (by simp [t])
    have hbd := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re hs_re_gt1 t
    have hnorm_le : ‖(riemannZeta s)⁻¹‖ ≤ s.re / (s.re - 1) := by
      have h1 := hbd.2.1.trans hbd.2.2
      rw [← hs_eq, one_div] at h1
      exact h1
    have hdiv_le : s.re / (s.re - 1) ≤ (2 / c₁) * L := by
      have hsub_ge : c₁ / L ≤ s.re - 1 := by linarith
      calc s.re / (s.re - 1) ≤ 2 / (c₁ / L) :=
            div_le_div₀ (by norm_num) hre_hi (div_pos hc₁_pos hL_pos) hsub_ge
        _ = (2 / c₁) * L := by field_simp [hc₁_pos.ne', hL_pos.ne']
    have hL_le_L5 : L ≤ L ^ 5 := by
      have h1 : L ^ (1 : ℕ) ≤ L ^ (5 : ℕ) := pow_le_pow_right₀ hL_gt1.le (by norm_num)
      simpa using h1
    calc ‖(riemannZeta s)⁻¹‖ ≤ (2 / c₁) * L := hnorm_le.trans hdiv_le
      _ ≤ (2 / c₁) * L ^ 5 := mul_le_mul_of_nonneg_left hL_le_L5 (by positivity)
      _ = C_right * L ^ 5 := rfl
      _ ≤ C₁ * L ^ 5 := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hL_pos.le 5)
  · -- Zero-free strip regime: `1 - c₁ / L ≤ s.re < 1 + c₁ / L`
    push Not at hright
    set η : ℝ := c / (8 * L) with hη_def
    have hη_pos : 0 < η := by positivity
    have hη_le : η ≤ 1 / 32 := by
      dsimp only [η]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    set R_open : ℝ := 5 * η
    set R : ℝ := 4 * η
    set r : ℝ := 2 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (t : ℂ) with hs₀_def
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = t := by simp [s₀]
    have hball_ne1 : ∀ z ∈ Metric.ball s₀ R_open, z ≠ 1 := by
      intro z hz h1
      subst h1
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have him_diff := (Complex.abs_im_le_norm ((1 : ℂ) - s₀)).trans_lt hz
      rw [Complex.sub_im, Complex.one_im, hs₀_im, zero_sub, abs_neg] at him_diff
      have hR_lt : R_open < 1 := by dsimp only [R_open]; linarith
      linarith
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, riemannZeta z ≠ 0 := by
      intro z hz
      have hz1 : z ≠ 1 := hball_ne1 z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hz_im_le : |z.im| ≤ |t| + 1 / 2 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        have hR_le_half : R_open ≤ 1 / 2 := by dsimp only [R_open]; linarith
        linarith [abs_le.mpr him_diff]
      have hlog_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv_ge : c / (2 * L) ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c / (2 * L) ≤ c / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_left hc_pos.le hlogz_pos hlog_le
          _ ≤ c₀ / Real.log (|z.im| + 2) :=
              div_le_div_of_nonneg_right hc_le_c₀ hlogz_pos.le
      have h4η : 4 * η = c / (2 * L) := by dsimp only [η]; ring
      have hz_re_ge : 1 - c₀ / Real.log (|z.im| + 2) ≤ z.re := by
        dsimp only [R_open] at hre_diff
        linarith
      exact hzf₀ z hz_re_ge hz1
    have hball_diff : DifferentiableOn ℂ riemannZeta (Metric.ball s₀ R_open) := fun z hz =>
      (differentiableAt_riemannZeta (hball_ne1 z hz)).differentiableWithinAt
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hball_R_sub : Metric.ball s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.ball_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_R : DifferentiableOn ℂ Log (Metric.ball s₀ R) := fun z hz =>
      (hLog_d z (hball_R_sub hz)).differentiableAt.differentiableWithinAt
    -- Sharp bound on `‖1 / ζ(s₀)‖ ≤ 16 L / c`
    have hinv_s₀ : ‖(riemannZeta s₀)⁻¹‖ ≤ 16 * L / c := by
      have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (by linarith : 1 < 1 + η) t
      have h1 := h.2.1.trans h.2.2
      have hsub : (1 + η) - 1 = η := by ring
      rw [hsub, one_div] at h1
      have hs₀_eq' : ((1 + η : ℝ) : ℂ) + I * (t : ℂ) = s₀ := rfl
      rw [hs₀_eq'] at h1
      have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by linarith) hη_pos.le
      have h3 : 2 / η = 16 * L / c := by dsimp only [η]; field_simp [hc_pos.ne', hL_pos.ne']; ring
      linarith
    -- Upper bound `(Log z).re ≤ log(1152 / c) + 2 * log L` on `ball s₀ R` using `norm_riemannZeta_near_one_le`!
    set M : ℝ := Real.log (1152 / c) + 2 * Real.log L with hM_def
    have hLog_re_le : ∀ z ∈ Metric.ball s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball : z ∈ Metric.ball s₀ R_open := hball_R_sub hz
      have hznz : riemannZeta z ≠ 0 := hball_nz z hz_ball
      have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_diff := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_diff
      rw [Complex.sub_im, hs₀_im] at him_diff
      have hR_le_8 : R ≤ 1 / 8 := by dsimp only [R]; linarith
      have hz_re_hi : z.re ≤ 2 := by linarith
      have hz_im_lo : 2 ≤ |z.im| := by
        have htri : |t| ≤ |z.im| + |z.im - t| := by
          have := abs_sub_le t z.im 0
          linarith [abs_sub_comm t z.im, show |t - 0| = |t| by simp, show |z.im - 0| = |z.im| by simp]
        linarith [abs_le.mpr him_diff]
      have hz_im_hi : |z.im| ≤ |t| + 1 / 8 := by
        have htri : |z.im| ≤ |t| + |z.im - t| := by
          simpa [add_sub_cancel] using abs_add_le t (z.im - t)
        linarith [abs_le.mpr him_diff]
      have hlogz_le : Real.log (|z.im| + 2) ≤ 2 * L := by
        have hsq : |z.im| + 2 ≤ (|t| + 2) ^ 2 := by nlinarith
        have h1 := Real.log_le_log (by linarith [abs_nonneg z.im]) hsq
        rw [Real.log_pow] at h1
        simpa [L] using h1
      have hlogz_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hz_re_lo : 1 - 1 / Real.log (|z.im| + 2) ≤ z.re := by
        have h3η : 3 * η ≤ 1 / (2 * L) := by
          dsimp only [η]
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have hinv_ge : 1 / (2 * L) ≤ 1 / Real.log (|z.im| + 2) :=
          div_le_div_of_nonneg_left zero_le_one hlogz_pos hlogz_le
        dsimp only [R] at hre_diff
        linarith
      have hz_bd : ‖riemannZeta z‖ ≤ 72 * L := by
        have hz_eq : ((z.re : ℝ) : ℂ) + I * (z.im : ℂ) = z := Complex.ext (by simp) (by simp)
        have h1 := Stage5ZetaZeroFree.norm_riemannZeta_near_one_le hz_re_lo hz_re_hi hz_im_lo
        rw [hz_eq] at h1
        linarith
      have hratio_le : ‖riemannZeta z / riemannZeta s₀‖ ≤ (1152 / c) * L ^ 2 := by
        rw [div_eq_mul_inv, norm_mul]
        calc ‖riemannZeta z‖ * ‖(riemannZeta s₀)⁻¹‖
            ≤ (72 * L) * (16 * L / c) := mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ = (1152 / c) * L ^ 2 := by ring
      have hre_eq : (Log z).re = Real.log ‖riemannZeta z / riemannZeta s₀‖ := by
        have hexp : Real.exp (Log z).re = ‖riemannZeta z / riemannZeta s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      have hratio_pos : 0 < ‖riemannZeta z / riemannZeta s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      rw [hre_eq]
      calc Real.log ‖riemannZeta z / riemannZeta s₀‖
          ≤ Real.log ((1152 / c) * L ^ 2) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log (1152 / c) + Real.log (L ^ 2) := Real.log_mul (by positivity) (by positivity)
        _ = Real.log (1152 / c) + 2 * Real.log L := by rw [Real.log_pow]; push_cast; rfl
    -- Apply `borelCaratheodory_sub_center` at `s` (`‖s - s₀‖ ≤ r = 2 η < 4 η = R`)
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀, t])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hc₁_eq : c₁ / L = η / 2 := by dsimp only [c₁, η]; ring
      dsimp only [r]
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_sub_center hR_pos hrR hLog_diff_R hLog_re_le hs_dist
    rw [hLog0, sub_zero, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * r / (R - r) = 2 := by
      dsimp only [r, R]; field_simp [hη_pos.ne']; ring
    rw [hcoeff] at hbc
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hball_R_sub (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hs_dist.trans_lt hrR))
    have hinv_eq : (riemannZeta s)⁻¹ = (riemannZeta s₀)⁻¹ * cexp (-Log s) := by
      have hexp := hLog_exp s hs_ball
      have hsnz : riemannZeta s ≠ 0 := hball_nz s hs_ball
      have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Complex.exp_neg, hexp, inv_div]
      field_simp [hsnz, hs₀_nz]
    have hneg_re_le : (-Log s).re ≤ 2 * M := by
      rw [Complex.neg_re]
      have h1 := (abs_le.mp (Complex.abs_re_le_norm (Log s))).1
      linarith
    have hexp_2M : Real.exp (2 * M) = (1152 / c) ^ 2 * L ^ 4 := by
      dsimp only [M]
      rw [show 2 * (Real.log (1152 / c) + 2 * Real.log L) =
            2 * Real.log (1152 / c) + 4 * Real.log L by ring,
        Real.exp_add, show 2 * Real.log (1152 / c) = Real.log ((1152 / c) ^ 2) by
          rw [Real.log_pow]; push_cast; rfl,
        show 4 * Real.log L = Real.log (L ^ 4) by rw [Real.log_pow]; push_cast; rfl,
        Real.exp_log (by positivity), Real.exp_log (by positivity)]
    rw [hinv_eq, norm_mul, Complex.norm_exp]
    calc ‖(riemannZeta s₀)⁻¹‖ * Real.exp (-Log s).re
        ≤ (16 * L / c) * Real.exp (2 * M) :=
          mul_le_mul hinv_s₀ (Real.exp_le_exp.mpr hneg_re_le) (Real.exp_pos _).le (by positivity)
      _ = (16 * L / c) * ((1152 / c) ^ 2 * L ^ 4) := by rw [hexp_2M]
      _ = C_left * L ^ 5 := by dsimp only [C_left]; ring
      _ ≤ C₁ * L ^ 5 := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hL_pos.le 5)

/-- **Unconditional Boundedness of `invZetaReg` on the Compact Box `[1 - c₂, 2] × [-4, 4]`**. -/
theorem invZetaReg_bounded_near_one :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ s : ℂ, 1 - c₂ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 4 →
        Stage6EffectivePNT.zetaReg s ≠ 0 ∧ ‖invZetaReg s‖ ≤ C₂ := by
  obtain ⟨c₀, hc₀_pos, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  have hlog6_pos : 0 < Real.log 6 := Real.log_pos (by norm_num)
  set c₂ : ℝ := min (1 / 4) (c₀ / (2 * Real.log 6)) with hc₂_def
  have hc₂_pos : 0 < c₂ := lt_min (by norm_num) (by positivity)
  set K : Set ℂ := {z : ℂ | 1 - c₂ ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ 4}
  have hK_comp : IsCompact K := by
    have hsub : K = Complex.equivRealProdCLM.symm '' (Set.Icc (1 - c₂) 2 ×ˢ Set.Icc (-4 : ℝ) 4) := by
      ext z
      simp only [K, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨(z.re, z.im), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, Complex.ext (by simp) (by simp)⟩
      · rintro ⟨⟨x, y⟩, ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, rfl⟩
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩
    rw [hsub]
    exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous
  have hK_sub : K ⊆ {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} := by
    intro z hz
    have hc₂_le_qtr : c₂ ≤ 1 / 4 := min_le_left _ _
    have hc₂_le_log : c₂ ≤ c₀ / (2 * Real.log 6) := min_le_right _ _
    have hz_re : 0 < z.re := by linarith [hz.1]
    refine ⟨hz_re, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [Stage6EffectivePNT.zetaReg_one]; exact one_ne_zero
    · rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hz_re hz1]
      refine mul_ne_zero (sub_ne_zero.mpr hz1) ?_
      have hlog_le : Real.log (|z.im| + 2) ≤ Real.log 6 :=
        Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith [hz.2.2])
      have hlog_pos : 0 < Real.log (|z.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg z.im])
      have hdiv : c₂ ≤ c₀ / Real.log (|z.im| + 2) := by
        calc c₂ ≤ c₀ / (2 * Real.log 6) := hc₂_le_log
          _ ≤ c₀ / Real.log 6 := div_le_div_of_nonneg_left hc₀_pos.le hlog6_pos (by linarith)
          _ ≤ c₀ / Real.log (|z.im| + 2) := div_le_div_of_nonneg_left hc₀_pos.le hlog_pos hlog_le
      exact hzf₀ z (by linarith [hz.1]) hz1
  obtain ⟨M, hM⟩ := hK_comp.exists_bound_of_continuousOn
    ((differentiableOn_invZetaReg.mono hK_sub).continuousOn)
  refine ⟨c₂, hc₂_pos, max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun s hlo hhi him => ?_⟩
  have hsK : s ∈ K := ⟨hlo, hhi, him⟩
  exact ⟨(hK_sub hsK).2, (hM s hsK).trans (le_max_left _ _)⟩

/-- **Hadamard Three-Circles Inequality** (evaluated at `s₀ - r₂`) deduced directly from
`Stage5StirlingPhragmen.phragmen_lindelof_convexity_subgaussian` applied to `w ↦ f (s₀ + cexp w)`. -/
theorem hadamard_three_circles_left {f : ℂ → ℂ} {s₀ : ℂ} {r₁ r₂ r₃ M₁ M₃ : ℝ}
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ ≤ r₂) (hr₂₃ : r₂ ≤ r₃) (hr₁₃ : r₁ < r₃)
    (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    (hf : DifferentiableOn ℂ f (Metric.closedBall s₀ r₃))
    (hbd₁ : ∀ z : ℂ, ‖z - s₀‖ = r₁ → ‖f z‖ ≤ M₁)
    (hbd₃ : ∀ z ∈ Metric.closedBall s₀ r₃, ‖f z‖ ≤ M₃) :
    ‖f (s₀ - (r₂ : ℂ))‖ ≤
      M₁ ^ ((Real.log r₃ - Real.log r₂) / (Real.log r₃ - Real.log r₁)) *
      M₃ ^ ((Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁)) := by
  have hr₂ : 0 < r₂ := lt_of_lt_of_le hr₁ hr₁₂
  have hr₃ : 0 < r₃ := lt_of_lt_of_le hr₂ hr₂₃
  set a : ℝ := Real.log r₁
  set b : ℝ := Real.log r₃
  have hab : a < b := Real.log_lt_log hr₁ hr₁₃
  let g : ℂ → ℂ := fun w => f (s₀ + cexp w)
  have hmaps : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → s₀ + cexp w ∈ Metric.closedBall s₀ r₃ := by
    intro w _ hw_hi
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw_hi).trans_eq (Real.exp_log hr₃)
  have hdiff_g : DifferentiableOn ℂ g (Complex.re ⁻¹' Set.Ioo a b) := by
    refine hf.comp (differentiableOn_const s₀ |>.add differentiable_exp.differentiableOn) ?_
    intro w hw
    exact hmaps w hw.1.le hw.2.le
  have hcont_g : ContinuousOn g (Complex.re ⁻¹' Set.Icc a b) := by
    refine hf.continuousOn.comp
      (continuousOn_const.add Complex.continuous_exp.continuousOn) ?_
    intro w hw
    exact hmaps w hw.1 hw.2
  have hgrow_g : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖g w‖ ≤ M₃ * Real.exp (0 * |w.im| ^ (0 : ℝ)) := by
    intro w h1 h2
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact hbd₃ (s₀ + cexp w) (hmaps w h1 h2)
  have hleft_g : ∀ τ : ℝ, ‖g ((a : ℂ) + I * (τ : ℂ))‖ ≤ M₁ := by
    intro τ
    refine hbd₁ (s₀ + cexp ((a : ℂ) + I * (τ : ℂ))) ?_
    rw [add_sub_cancel_left, Complex.norm_exp]
    have hre : ((a : ℂ) + I * (τ : ℂ)).re = a := by simp
    rw [hre, Real.exp_log hr₁]
  have hright_g : ∀ τ : ℝ, ‖g ((b : ℂ) + I * (τ : ℂ))‖ ≤ M₃ := by
    intro τ
    exact hbd₃ _ (hmaps _ (by simp [hab.le]) (by simp))
  have hσ_mem : Real.log r₂ ∈ Set.Icc a b :=
    ⟨Real.log_le_log hr₁ hr₁₂, Real.log_le_log hr₂ hr₂₃⟩
  have hpl := Stage5StirlingPhragmen.phragmen_lindelof_convexity_subgaussian
    hab (by norm_num : (0 : ℝ) < 2) hM₁ hM₃ hdiff_g hcont_g hgrow_g hleft_g hright_g
    hσ_mem Real.pi
  have hval : g ((Real.log r₂ : ℂ) + I * (Real.pi : ℂ)) = f (s₀ - (r₂ : ℂ)) := by
    dsimp only [g]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr₂, mul_comm I (Real.pi : ℂ),
      Complex.exp_pi_mul_I]
    ring_nf
  rwa [hval] at hpl

/-- Auxiliary sublinear absorption: for `0 < lam₀ < 1`, `K ≥ 0`, `α > 0`, there is `B > 0` such that
`K * L ^ lam₀ ≤ α * L + B` for all `L ≥ 0`. -/
private lemma rpow_lt_one_le_linear_add {lam₀ K α : ℝ} (hlam0 : 0 < lam₀) (hlam1 : lam₀ < 1)
    (hK : 0 ≤ K) (hα : 0 < α) :
    ∃ B : ℝ, 0 < B ∧ ∀ L : ℝ, 0 ≤ L → K * L ^ lam₀ ≤ α * L + B := by
  have h1lam : 0 < 1 - lam₀ := sub_pos.mpr hlam1
  set L₀ : ℝ := (max (K / α) 1) ^ ((1 - lam₀)⁻¹) with hL₀_def
  have hL₀_pos : 0 < L₀ := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _
  set B : ℝ := K * L₀ ^ lam₀ + 1
  refine ⟨B, by positivity, fun L hL => ?_⟩
  by_cases hbig : L₀ ≤ L
  · have hpow : K / α ≤ L ^ (1 - lam₀) := by
      calc K / α ≤ max (K / α) 1 := le_max_left _ _
        _ = L₀ ^ (1 - lam₀) := by
            rw [hL₀_def, ← Real.rpow_mul (lt_of_lt_of_le one_pos (le_max_right _ _)).le,
              inv_mul_cancel₀ h1lam.ne', Real.rpow_one]
        _ ≤ L ^ (1 - lam₀) := Real.rpow_le_rpow hL₀_pos.le hbig h1lam.le
    have hLpos : 0 < L := lt_of_lt_of_le hL₀_pos hbig
    have hmul : K * L ^ lam₀ ≤ α * L := by
      have h1 := (div_le_iff₀ hα).mp hpow
      calc K * L ^ lam₀ ≤ (L ^ (1 - lam₀) * α) * L ^ lam₀ :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hL lam₀)
        _ = α * (L ^ (1 - lam₀) * L ^ lam₀) := by ring
        _ = α * L := by rw [← Real.rpow_add hLpos, sub_add_cancel, Real.rpow_one]
    linarith [show 0 ≤ B by positivity]
  · push Not at hbig
    have h1 : K * L ^ lam₀ ≤ K * L₀ ^ lam₀ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL hbig.le hlam0.le) hK
    have h2 : 0 ≤ α * L := mul_nonneg hα.le hL
    dsimp only [B]
    linarith

/-- **Unconditional Littlewood `1 / ζ(s) = O(|t|^α)` Bound in Any Zero-Free Half-Plane `Re(s) > θ`**:
if `0 < θ < 1`, `0 < δ`, `θ + δ < 1`, and `riemannZeta` has no zeros on `Re(s) > θ` (`s ≠ 1`),
then for EVERY `α > 0`, there exists `C > 0` such that:
1. `‖(riemannZeta s)⁻¹‖ ≤ C * (|s.im| + 2) ^ α` for all `θ + δ ≤ s.re ≤ 3` and `4 ≤ |s.im|`, and
2. `zetaReg s ≠ 0 ∧ ‖invZetaReg s‖ ≤ C` on the compact rectangle `[θ + δ, 3] × [-4, 4]`. -/
theorem inv_riemannZeta_rpow_eps_of_zeroFree_halfPlane {θ δ α : ℝ}
    (hθ0 : 0 < θ) (hδ0 : 0 < δ) (hθδ : θ + δ < 1) (hα : 0 < α)
    (hzf : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      (∀ s : ℂ, θ + δ ≤ s.re → s.re ≤ 3 → 4 ≤ |s.im| →
        ‖(riemannZeta s)⁻¹‖ ≤ C * (|s.im| + 2) ^ α) ∧
      (∀ s : ℂ, θ + δ ≤ s.re → s.re ≤ 3 → |s.im| ≤ 4 →
        Stage6EffectivePNT.zetaReg s ≠ 0 ∧ ‖invZetaReg s‖ ≤ C) := by
  -- Part A: Compact box `[θ + δ, 3] × [-4, 4]`
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
  have hK_sub : K ⊆ {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} := by
    intro z hz
    have hz_pos : 0 < z.re := by linarith [hz.1]
    refine ⟨hz_pos, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [Stage6EffectivePNT.zetaReg_one]; exact one_ne_zero
    · rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hz_pos hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (hzf z (by linarith [hz.1]) hz1)
  obtain ⟨M_box, hM_box⟩ :=
    hK_comp.exists_bound_of_continuousOn ((differentiableOn_invZetaReg.mono hK_sub).continuousOn)
  -- Part B: Tall strip via Borel–Carathéodory + Hadamard Three-Circles centered at `s₀ = 3 + i t`
  set r₁ : ℝ := 1
  set r₂_max : ℝ := 3 - θ - δ
  set r₃ : ℝ := 3 - θ - δ / 2
  set R_open : ℝ := 3 - θ - δ / 4
  have hr₂_max_gt1 : 1 < r₂_max := by dsimp only [r₂_max]; linarith
  have hr₂_max_lt : r₂_max < r₃ := by dsimp only [r₂_max, r₃]; linarith
  have hr₃_lt : r₃ < R_open := by dsimp only [r₃, R_open]; linarith
  have hR_open_lt3 : R_open < 3 := by dsimp only [R_open]; linarith
  have hR_open_pos : 0 < R_open := by linarith
  set lam₀ : ℝ := Real.log r₂_max / Real.log r₃ with hlam₀_def
  have hlog_r₂_pos : 0 < Real.log r₂_max := Real.log_pos hr₂_max_gt1
  have hlog_r₃_pos : 0 < Real.log r₃ := Real.log_pos (by linarith)
  have hlam₀_pos : 0 < lam₀ := div_pos hlog_r₂_pos hlog_r₃_pos
  have hlam₀_lt1 : lam₀ < 1 := (div_lt_one hlog_r₃_pos).mpr (Real.log_lt_log (by linarith) hr₂_max_lt)
  set M₁ : ℝ := 4 * Real.log 6 + 1
  have hM₁_gt1 : 1 < M₁ := by
    have : 0 < Real.log 6 := Real.log_pos (by norm_num)
    dsimp only [M₁]; linarith
  set A_zeta : ℝ := 2 * (3 + 12 / (θ + δ / 4))
  have hA_ge2 : 2 ≤ A_zeta := by
    dsimp only [A_zeta]
    have : 0 < 12 / (θ + δ / 4) := by positivity
    linarith
  set C_M : ℝ := Real.log A_zeta + 1
  have hCM_pos : 0 < C_M := by
    have : 0 < Real.log A_zeta := Real.log_pos (by linarith)
    linarith
  set C₃ : ℝ := (2 * r₃ / (R_open - r₃)) * C_M + M₁
  have hC₃_pos : 0 < C₃ :=
    add_pos (mul_pos (div_pos (by linarith) (sub_pos.mpr hr₃_lt)) hCM_pos) (by linarith)
  set K₄ : ℝ := M₁ * (C₃ / M₁) ^ lam₀
  have hK₄_nn : 0 ≤ K₄ := mul_nonneg (by linarith) (Real.rpow_nonneg (div_nonneg hC₃_pos.le (by linarith)) _)
  obtain ⟨B, hB_pos, hB⟩ := rpow_lt_one_le_linear_add hlam₀_pos hlam₀_lt1 hK₄_nn hα
  set C_tall : ℝ := max (2 * Real.exp B) 2
  set C : ℝ := max (max M_box 1) C_tall
  have hC_pos : 0 < C := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2) ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, hC_pos, fun s hre_lo hre_hi him => ?_, fun s hre_lo hre_hi him => ?_⟩
  · -- Tall strip `4 ≤ |s.im|`
    set t : ℝ := s.im
    by_cases hs2 : 2 ≤ s.re
    · -- Right half `2 ≤ s.re ≤ 3`: `‖1 / ζ(s)‖ ≤ 2`
      have hs_eq : s = (s.re : ℂ) + I * (t : ℂ) := Complex.ext (by simp) (by simp [t])
      have hbd := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (by linarith : 1 < s.re) t
      have h1 := hbd.2.1.trans hbd.2.2
      rw [← hs_eq, one_div] at h1
      have h2 : s.re / (s.re - 1) ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hpow_ge1 : (1 : ℝ) ≤ (|t| + 2) ^ α := Real.one_le_rpow (by linarith) hα.le
      calc ‖(riemannZeta s)⁻¹‖ ≤ 2 := h1.trans h2
        _ ≤ C_tall := le_max_right _ _
        _ ≤ C := le_max_right _ _
        _ ≤ C * (|t| + 2) ^ α := le_mul_of_one_le_right hC_pos.le hpow_ge1
    · -- Left strip `θ + δ ≤ s.re < 2`: Hadamard Three-Circles on `Log` around `s₀ = 3 + I * t`
      push Not at hs2
      set s₀ : ℂ := (3 : ℂ) + I * (t : ℂ)
      have hs₀_re : s₀.re = 3 := by simp [s₀]
      have hs₀_im : s₀.im = t := by simp [s₀]
      set r₂ : ℝ := 3 - s.re
      have hr₁₂ : r₁ < r₂ := by dsimp only [r₁, r₂]; linarith
      have hr₂_le : r₂ ≤ r₂_max := by dsimp only [r₂, r₂_max]; linarith
      have hr₂₃ : r₂ ≤ r₃ := hr₂_le.trans hr₂_max_lt.le
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
      have hinv_s₀ : ‖(riemannZeta s₀)⁻¹‖ ≤ 2 := by
        have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (σ := 3) (by norm_num) t
        have h1 := h.2.1.trans h.2.2
        have hs₀_eq' : ((3 : ℝ) : ℂ) + I * (t : ℂ) = s₀ := by simp [s₀]
        rw [hs₀_eq', one_div] at h1
        linarith
      -- Bound 1 on inner circle `‖z - s₀‖ = 1`: via `borelCaratheodory_sub_center` on `ball s₀ (3/2)`
      have hbd₁ : ∀ z : ℂ, ‖z - s₀‖ = r₁ → ‖Log z‖ ≤ M₁ := by
        intro z hz_norm
        have h32_sub : Metric.ball s₀ (3 / 2) ⊆ Metric.ball s₀ R_open :=
          Metric.ball_subset_ball (by dsimp only [R_open]; linarith)
        have hLog_diff_32 : DifferentiableOn ℂ Log (Metric.ball s₀ (3 / 2)) := fun w hw =>
          (hLog_d w (h32_sub hw)).differentiableAt.differentiableWithinAt
        have hre_32 : ∀ w ∈ Metric.ball s₀ (3 / 2), (Log w).re ≤ Real.log 6 := by
          intro w hw
          have hw_ball : w ∈ Metric.ball s₀ R_open := h32_sub hw
          have hwnz : riemannZeta w ≠ 0 := hball_nz w hw_ball
          have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
          rw [Metric.mem_ball, dist_eq_norm] at hw
          have hre_w := (abs_lt.mp ((Complex.abs_re_le_norm (w - s₀)).trans_lt hw)).1
          rw [Complex.sub_re, hs₀_re] at hre_w
          have hw_gt : 3 / 2 < w.re := by linarith
          have hzw : ‖riemannZeta w‖ ≤ 3 := by
            have hw_eq : ((w.re : ℝ) : ℂ) + I * (w.im : ℂ) = w := Complex.ext (by simp) (by simp)
            have h := Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re (by linarith : 1 < w.re) w.im
            have h1 := h.1.trans h.2.2
            rw [hw_eq] at h1
            have h2 : w.re / (w.re - 1) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
            exact h1.trans h2
          have hratio : ‖riemannZeta w / riemannZeta s₀‖ ≤ 6 := by
            rw [div_eq_mul_inv, norm_mul]
            nlinarith [norm_nonneg (riemannZeta w), norm_nonneg ((riemannZeta s₀)⁻¹)]
          have hre_eq : (Log w).re = Real.log ‖riemannZeta w / riemannZeta s₀‖ := by
            have hexp : Real.exp (Log w).re = ‖riemannZeta w / riemannZeta s₀‖ := by
              rw [← Complex.norm_exp, hLog_exp w hw_ball]
            rw [← hexp, Real.log_exp]
          rw [hre_eq]
          exact Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hwnz hs₀_nz)) hratio
        have hbc := Stage5ZetaZeroFree.borelCaratheodory_sub_center (r := 1) (R := 3 / 2)
          (by norm_num) (by norm_num) hLog_diff_32 hre_32 (by rw [hz_norm])
        rw [hLog0, sub_zero, Complex.zero_re, sub_zero] at hbc
        have h4 : (2 * (1 : ℝ) / (3 / 2 - 1)) = 4 := by norm_num
        rw [h4] at hbc
        dsimp only [M₁]; linarith
      -- Bound 2 on outer disk `closedBall s₀ r₃`: via `borelCaratheodory_sub_center` on `ball s₀ R_open`
      set L : ℝ := Real.log (|t| + 2)
      have hL_gt1 : 1 < L := by
        have h6 : Real.exp 1 < |t| + 2 := by linarith [Real.exp_one_lt_d9]
        exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h6)
      have hLog_diff_open : DifferentiableOn ℂ Log (Metric.ball s₀ R_open) := fun w hw =>
        (hLog_d w hw).differentiableAt.differentiableWithinAt
      have hre_open : ∀ w ∈ Metric.ball s₀ R_open, (Log w).re ≤ C_M * L := by
        intro w hw
        have hw1 : w ≠ 1 := hball_ne1 w hw
        have hwnz : riemannZeta w ≠ 0 := hball_nz w hw
        have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
        have hw_mem : w ∈ Metric.ball s₀ R_open := hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have hre_diff := abs_le.mp ((Complex.abs_re_le_norm (w - s₀)).trans hw.le)
        have him_diff := abs_le.mp ((Complex.abs_im_le_norm (w - s₀)).trans hw.le)
        rw [Complex.sub_re, hs₀_re] at hre_diff
        rw [Complex.sub_im, hs₀_im] at him_diff
        have hw_re_lo : θ + δ / 4 ≤ w.re := by dsimp only [R_open] at hre_diff; linarith
        have hw_re_hi : w.re ≤ 6 := by dsimp only [R_open] at hre_diff; linarith
        have hw_im_lo : 1 ≤ |w.im| := by
          have htri : |t| ≤ |w.im| + |w.im - t| := by
            have := abs_add_le w.im (t - w.im)
            rw [add_sub_cancel, abs_sub_comm] at this; exact this
          linarith [abs_le.mpr him_diff]
        have hw_im_hi : |w.im| ≤ |t| + 3 := by
          have htri : |w.im| ≤ |t| + |w.im - t| := by
            simpa [add_sub_cancel] using abs_add_le t (w.im - t)
          linarith [abs_le.mpr him_diff]
        have hw_bd : ‖riemannZeta w‖ ≤ (3 + 12 / (θ + δ / 4)) * (|t| + 2) := by
          have h1 := Stage5ZetaZeroFree.norm_riemannZeta_le_of_re_pos (by linarith : 0 < w.re) hw1
          have hsub_ge : 1 ≤ ‖w - 1‖ := by
            have := Complex.abs_im_le_norm (w - 1)
            simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
            linarith
          have hinv_le : 1 / ‖w - 1‖ ≤ 1 := div_le_one_of_le₀ hsub_ge (norm_nonneg _)
          have hnorm_w : ‖w‖ ≤ 3 * (|t| + 2) := by
            have := Complex.norm_le_abs_re_add_abs_im w
            rw [abs_of_pos (by linarith : 0 < w.re)] at this
            linarith
          have hdiv_le : ‖w‖ / w.re ≤ (3 / (θ + δ / 4)) * (|t| + 2) := by
            calc ‖w‖ / w.re ≤ (3 * (|t| + 2)) / (θ + δ / 4) :=
                  div_le_div₀ (by positivity) hnorm_w (by positivity) hw_re_lo
              _ = (3 / (θ + δ / 4)) * (|t| + 2) := by ring
          have h12 : 3 / (θ + δ / 4) ≤ 12 / (θ + δ / 4) :=
            div_le_div_of_nonneg_right (by norm_num) (by positivity)
          have ht2 : 1 ≤ |t| + 2 := by linarith
          nlinarith [norm_nonneg (riemannZeta w)]
        have hratio_le : ‖riemannZeta w / riemannZeta s₀‖ ≤ A_zeta * (|t| + 2) := by
          rw [div_eq_mul_inv, norm_mul]
          calc ‖riemannZeta w‖ * ‖(riemannZeta s₀)⁻¹‖
              ≤ ((3 + 12 / (θ + δ / 4)) * (|t| + 2)) * 2 :=
                mul_le_mul hw_bd hinv_s₀ (norm_nonneg _) (by positivity)
            _ = A_zeta * (|t| + 2) := by dsimp only [A_zeta]; ring
        have hre_eq : (Log w).re = Real.log ‖riemannZeta w / riemannZeta s₀‖ := by
          have hexp : Real.exp (Log w).re = ‖riemannZeta w / riemannZeta s₀‖ := by
            rw [← Complex.norm_exp, hLog_exp w hw_mem]
          rw [← hexp, Real.log_exp]
        rw [hre_eq]
        calc Real.log ‖riemannZeta w / riemannZeta s₀‖
            ≤ Real.log (A_zeta * (|t| + 2)) :=
              Real.log_le_log (norm_pos_iff.mpr (div_ne_zero hwnz hs₀_nz)) hratio_le
          _ = Real.log A_zeta + L := Real.log_mul (by linarith) (by linarith)
          _ ≤ C_M * L := by
              have hlogA : 0 ≤ Real.log A_zeta := Real.log_nonneg (by linarith)
              dsimp only [C_M]; nlinarith
      have hbd₃ : ∀ z ∈ Metric.closedBall s₀ r₃, ‖Log z‖ ≤ C₃ * L := by
        intro z hz
        rw [Metric.mem_closedBall, dist_eq_norm] at hz
        have hbc := Stage5ZetaZeroFree.borelCaratheodory_sub_center hR_open_pos hr₃_lt
          hLog_diff_open hre_open hz
        rw [hLog0, sub_zero, Complex.zero_re, sub_zero] at hbc
        have hM₁_le : M₁ * L ≥ 0 := by positivity
        dsimp only [C₃]
        linarith [show ((2 * r₃ / (R_open - r₃)) * C_M + M₁) * L =
            (2 * r₃ / (R_open - r₃)) * (C_M * L) + M₁ * L by ring]
      -- Apply Hadamard Three-Circles!
      have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ r₃) :=
        hLog_diff_open.mono (Metric.closedBall_subset_ball hr₃_lt)
      have htc := hadamard_three_circles_left (r₁ := r₁) (r₂ := r₂) (r₃ := r₃)
        (M₁ := M₁) (M₃ := C₃ * L)
        (by norm_num) hr₁₂.le hr₂₃ (by linarith) (by linarith) (mul_pos hC₃_pos (by linarith))
        hLog_diff_cb hbd₁ hbd₃
      have hs_eq : s₀ - (r₂ : ℂ) = s := Complex.ext (by simp [s₀, r₂]) (by simp [s₀, t])
      rw [hs_eq] at htc
      -- Simplify the three-circles exponent using `r₁ = 1`, `C₃ * L / M₁ ≥ 1`, and `log r₂ / log r₃ ≤ lam₀`
      set lam : ℝ := Real.log r₂ / Real.log r₃
      have hlam_le : lam ≤ lam₀ := div_le_div_of_nonneg_right
        (Real.log_le_log (by linarith) hr₂_le) hlog_r₃_pos.le
      have h1sub : (Real.log r₃ - Real.log r₂) / (Real.log r₃ - Real.log r₁) = 1 - lam := by
        dsimp only [r₁, lam]; rw [Real.log_one, sub_zero]; field_simp [hlog_r₃_pos.ne']
      have hlam_eq : (Real.log r₂ - Real.log r₁) / (Real.log r₃ - Real.log r₁) = lam := by
        dsimp only [r₁, lam]; rw [Real.log_one, sub_zero, sub_zero]
      rw [h1sub, hlam_eq] at htc
      have hratio_ge1 : 1 ≤ C₃ * L / M₁ := by
        rw [one_le_div (by linarith : 0 < M₁)]
        have h1 : M₁ ≤ C₃ := by
          dsimp only [C₃]
          have : 0 ≤ (2 * r₃ / (R_open - r₃)) * C_M :=
            mul_nonneg (div_nonneg (by linarith) (sub_pos.mpr hr₃_lt).le) hCM_pos.le
          linarith
        nlinarith
      have hLog_s_le : ‖Log s‖ ≤ K₄ * L ^ lam₀ := by
        have hrew : M₁ ^ (1 - lam) * (C₃ * L) ^ lam = M₁ * (C₃ * L / M₁) ^ lam := by
          rw [Real.rpow_sub (by linarith : 0 < M₁), Real.rpow_one,
            Real.div_rpow (mul_nonneg hC₃_pos.le (by linarith)) (by linarith : 0 ≤ M₁)]
          ring
        rw [hrew] at htc
        calc ‖Log s‖ ≤ M₁ * (C₃ * L / M₁) ^ lam := htc
          _ ≤ M₁ * (C₃ * L / M₁) ^ lam₀ :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hratio_ge1 hlam_le) (by linarith)
          _ = M₁ * ((C₃ / M₁) ^ lam₀ * L ^ lam₀) := by
              rw [show C₃ * L / M₁ = (C₃ / M₁) * L by ring,
                Real.mul_rpow (div_nonneg hC₃_pos.le (by linarith)) (by linarith)]
          _ = K₄ * L ^ lam₀ := by dsimp only [K₄]; ring
      -- Absorb `K₄ * L ^ lam₀ ≤ α * L + B` and exponentiate!
      have hs_ball : s ∈ Metric.ball s₀ R_open :=
        Metric.closedBall_subset_ball hr₃_lt (Metric.mem_closedBall.mpr (by
          rw [dist_eq_norm, ← hs_eq, sub_sub_cancel_left, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (by linarith)]; exact hr₂₃))
      have hinv_eq : (riemannZeta s)⁻¹ = (riemannZeta s₀)⁻¹ * cexp (-Log s) := by
        have hexp := hLog_exp s hs_ball
        have hsnz : riemannZeta s ≠ 0 := hball_nz s hs_ball
        have hs₀_nz : riemannZeta s₀ ≠ 0 := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
        rw [Complex.exp_neg, hexp, inv_div]
        field_simp [hsnz, hs₀_nz]
      have hneg_re : (-Log s).re ≤ α * L + B := by
        rw [Complex.neg_re]
        have h1 := (abs_le.mp (Complex.abs_re_le_norm (Log s))).1
        have h2 := hB L (by linarith)
        linarith
      rw [hinv_eq, norm_mul, Complex.norm_exp]
      calc ‖(riemannZeta s₀)⁻¹‖ * Real.exp (-Log s).re
          ≤ 2 * Real.exp (α * L + B) :=
            mul_le_mul hinv_s₀ (Real.exp_le_exp.mpr hneg_re) (Real.exp_pos _).le (by norm_num)
        _ = (2 * Real.exp B) * Real.exp (α * L) := by rw [Real.exp_add]; ring
        _ = (2 * Real.exp B) * (|t| + 2) ^ α := by
            rw [Real.rpow_def_of_pos (by linarith : 0 < |t| + 2), mul_comm α L]
        _ ≤ C_tall * (|t| + 2) ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
        _ ≤ C * (|t| + 2) ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
  · -- Compact box case `|s.im| ≤ 4`
    have hsK : s ∈ K := ⟨hre_lo, hre_hi, him⟩
    exact ⟨(hK_sub hsK).2, (hM_box s hsK).trans ((le_max_left M_box 1).trans (le_max_left _ _))⟩

/-! ## Section 3: Sharp Truncated Perron Formula & Unconditional Effective Mertens Bound -/

/-- Truncated sharp Perron integral for the Mertens function `M(x)`:
`(1 / (2 π)) ∫_{-T}^T (1 / ζ(c + i t)) * x^{c + i t} / (c + i t) dt`. -/
def truncatedPerronM (x c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T, invZetaReg ((c : ℂ) + I * (t : ℂ)) *
      (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))

private lemma harmonic_sum_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp : m + 1 ∉ Finset.Icc 1 m)]
    have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hstep : 1 / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
      push_cast
      rw [← Real.log_div hm1.ne' hm0.ne']
      have hlog := Real.log_le_sub_one_of_pos (div_pos hm0 hm1)
      have hneg : Real.log ((m : ℝ) / ((m : ℝ) + 1)) = -Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
        rw [Real.log_div hm0.ne' hm1.ne', Real.log_div hm1.ne' hm0.ne']; ring
      have hsub : 1 - (m : ℝ) / ((m : ℝ) + 1) = 1 / ((m : ℝ) + 1) := by
        field_simp [hm1.ne']; ring
      linarith
    linarith

/-- **Sharp Truncated Perron Formula for `mertensM x`**:
for all `x ≥ 2`, `c = 1 + 1 / Real.log x`, and `T ≥ 1`:
`‖(mertensM x : ℂ) - truncatedPerronM x c T‖ ≤ 200 * (x / T * (Real.log x + 1) + 1)`. -/
theorem norm_mertensM_sub_truncatedPerron_le {x T : ℝ} (hx : 2 ≤ x) (hT : 1 ≤ T) :
    ‖(mertensM x : ℂ) - truncatedPerronM x (1 + 1 / Real.log x) T‖ ≤
      200 * (x / T * (Real.log x + 1) + 1) := by
  have hx0 : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hT0 : 0 < T := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx_gt : (1 / 2 : ℝ) < Real.log x := hlog2.trans_le (Real.log_le_log (by norm_num) hx)
  have hlogx_pos : 0 < Real.log x := by linarith
  set c : ℝ := 1 + 1 / Real.log x with hc_def
  have hc1 : 1 < c := by rw [hc_def]; linarith [div_pos one_pos hlogx_pos]
  have hc0 : 0 < c := by linarith
  have hc3 : c ≤ 3 := by
    rw [hc_def]
    have h1 : 1 / Real.log x ≤ 2 := by rw [div_le_iff₀ hlogx_pos]; linarith
    linarith
  have hxc_le : x ^ c ≤ 3 * x := by
    have h1 : x ^ c = x * x ^ (1 / Real.log x) := by
      rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
    have h2 : x ^ (1 / Real.log x) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hlogx_pos.ne']
    rw [h1, h2]
    have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith
  -- Step 1: exact termwise series-integral swap on `[-T, T]`
  let F : ℕ → ℝ → ℂ := fun n t =>
    if n = 0 then 0
    else (ArithmeticFunction.moebius n : ℂ) *
      ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))
  have hsumR : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n : ℕ => if n = 0 then (0 : ℝ) else 1) (by simp)
      (fun n => by split_ifs <;> norm_num) (c : ℂ)).mp (by
        have hz : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) (c : ℂ) :=
          ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by simpa using hc1)
        refine hz.congr fun n => ?_
        rcases eq_or_ne n 0 with rfl | hn
        · simp [LSeries.term]
        · simp [LSeries.term, hn, ArithmeticFunction.zeta_apply])
    refine h.congr fun n => ?_
    by_cases hn : n = 0 <;> simp [hn]
  have htsumR_le : (∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-c)) ≤ 3 * Real.log x + 1 := by
    have hzeta := (Stage5ZetaZeroFree.norm_riemannZeta_and_inv_of_one_lt_re hc1 0).2.2
    have hEq : (riemannZeta (c : ℂ)).re = ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-c) := by
      rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by simpa using hc1)]
      have hterm : LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) (c : ℂ) =
          (((∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-c)) : ℝ) : ℂ) := by
        rw [LSeries, Complex.ofReal_tsum]
        refine tsum_congr fun n => ?_
        rcases eq_or_ne n 0 with rfl | hn
        · simp [LSeries.term]
        · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
          simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hn0.le, ← Complex.ofReal_one,
            ← Complex.ofReal_div, Real.rpow_neg hn0.le, one_div]
      rw [hterm, Complex.ofReal_re]
    rw [← hEq]
    have hdiv : c / (c - 1) = Real.log x + 1 := by
      rw [hc_def]; field_simp [hlogx_pos.ne']; ring
    linarith
  have hF_int : ∀ n : ℕ, IntegrableOn (F n) (Set.Ioc (-T) T) volume := fun n => by
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hxnC : ((x / (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx0 hnR).ne'
      have hcont : Continuous (fun t : ℝ =>
          (ArithmeticFunction.moebius n : ℂ) *
            ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) := by
        have hpow : Continuous (fun t : ℝ => ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) := by
          have hEq : (fun t : ℝ => ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) =
              fun t : ℝ => cexp (Complex.log ((x / (n : ℝ) : ℝ) : ℂ) * ((c : ℂ) + I * (t : ℂ))) :=
            funext fun t => Complex.cpow_def_of_ne_zero hxnC _
          rw [hEq]; fun_prop
        refine (continuous_const.mul hpow).div (by fun_prop) fun t h0 => ?_
        have := congrArg Complex.re h0; simp at this; linarith
      exact (hcont.intervalIntegrable (-T) T).1
  have hF_sum_norm : Summable (fun n : ℕ => ∫ t in Set.Ioc (-T) T, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _)
      (fun n => ?_) (hsumR.mul_left (2 * T * x ^ c / c))
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hdiv_pos : 0 < x / (n : ℝ) := div_pos hx0 hnR
      rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      have hpt : ∀ t ∈ Set.uIoc (-T) T,
          ‖(ArithmeticFunction.moebius n : ℂ) *
            ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))‖ ≤
            (x ^ c / c) * (n : ℝ) ^ (-c) := fun t _ => by
        rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hdiv_pos]
        have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
        rw [hre]
        have hden : c ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := by
          simpa [abs_of_pos hc0] using Complex.abs_re_le_norm ((c : ℂ) + I * (t : ℂ))
        have hnum : ‖(ArithmeticFunction.moebius n : ℂ)‖ * (x / (n : ℝ)) ^ c ≤ x ^ c * (n : ℝ) ^ (-c) := by
          rw [Real.div_rpow hx0.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]
          exact mul_le_of_le_one_left (by positivity) (norm_moebius_le_one n)
        calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (x / (n : ℝ)) ^ c / ‖(c : ℂ) + I * (t : ℂ)‖
            ≤ (x ^ c * (n : ℝ) ^ (-c)) / c := div_le_div₀ (by positivity) hnum hc0 hden
          _ = (x ^ c / c) * (n : ℝ) ^ (-c) := by ring
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => ‖F n t‖) (by
        intro t ht; simp only [F, hn, ↓reduceIte, norm_norm]; exact hpt t ht)
      rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _),
          show T - (-T) = 2 * T by ring, abs_of_pos (by positivity)] at h1
      have h1' : ∫ t in (-T)..T, ‖(ArithmeticFunction.moebius n : ℂ) *
            ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))‖ ≤
          (x ^ c / c) * (n : ℝ) ^ (-c) * (2 * T) := by
        simpa only [F, hn, ↓reduceIte] using h1
      linarith [show (x ^ c / c) * (n : ℝ) ^ (-c) * (2 * T) =
        2 * T * x ^ c / c * (n : ℝ) ^ (-c) by ring]
  have hswap := hasSum_integral_of_summable_integral_norm hF_int hF_sum_norm
  have htsum_t : ∀ t : ℝ, ∑' n : ℕ, F n t =
      invZetaReg ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) := by
    intro t
    have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc1]
    have hs1 : ((c : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hsnz : riemannZeta ((c : ℂ) + I * (t : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re hs.le
    rw [invZetaReg_eq_inv_riemannZeta (by linarith) hs1 hsnz,
      ← LSeries_moebius_eq_inv_riemannZeta hs]
    set W : ℂ := (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))
    have hsumL := LSeriesSummable_moebius hs
    have h1 := (hsumL.hasSum.mul_right W).tsum_eq
    rw [mul_div_assoc]
    change ∑' n : ℕ, F n t =
      (∑' n : ℕ, LSeries.term (fun m => (ArithmeticFunction.moebius m : ℂ)) ((c : ℂ) + I * (t : ℂ)) n) * W
    rw [← h1]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, LSeries.term]
    · simp only [F, LSeries.term, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hxnC : ((x / (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx0 hnR).ne'
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
      have hpow1 : ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
          (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / (n : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hxnC, Complex.cpow_def_of_ne_zero hxC,
          Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_sub,
          ← Complex.ofReal_log (div_pos hx0 hnR).le, Real.log_div hx0.ne' hnR.ne',
          ← Complex.ofReal_log hx0.le, ← Complex.ofReal_natCast, ← Complex.ofReal_log hnR.le]
        congr 1; push_cast; ring
      rw [hpow1]; dsimp only [W]; ring
  simp_rw [htsum_t] at hswap
  have hperron_hasSum : HasSum
      (fun n : ℕ => if n = 0 then (0 : ℂ) else (ArithmeticFunction.moebius n : ℂ) *
        Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T)
      (truncatedPerronM x c T) := by
    have hmul := hswap.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
    have hRHS : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in Set.Ioc (-T) T,
          invZetaReg ((c : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) =
        truncatedPerronM x c T := by
      unfold truncatedPerronM; rw [intervalIntegral.integral_of_le (by linarith)]
    rw [hRHS] at hmul
    refine hmul.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    · simp only [F, hn, ↓reduceIte, Stage5ContourExplicit.perronKernel0]
      rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
          show (fun t : ℝ => (ArithmeticFunction.moebius n : ℂ) *
            ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) =
            fun t : ℝ => (ArithmeticFunction.moebius n : ℂ) *
              (((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) by
            funext t; ring,
          intervalIntegral.integral_const_mul]
      ring
  have hM_hasSum : HasSum
      (fun n : ℕ => if n = 0 then (0 : ℂ) else (ArithmeticFunction.moebius n : ℂ) *
        (if (n : ℝ) ≤ x then 1 else 0))
      (mertensM x : ℂ) := by
    have hEq : ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (if n = 0 then (0 : ℂ) else (ArithmeticFunction.moebius n : ℂ) *
          (if (n : ℝ) ≤ x then 1 else 0)) = (mertensM x : ℂ) := by
      unfold mertensM
      rw [Complex.ofReal_sum]
      have hset : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊x⌋₊) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 ⌊x⌋₊)]
      simp only [↓reduceIte, zero_add]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp (Finset.mem_Icc.mp hn).2
      simp only [hn0, ↓reduceIte, hle, mul_one]
      norm_cast
    rw [← hEq]
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    have hge : ⌊x⌋₊ + 1 ≤ n := by simpa using hn
    have hn0 : n ≠ 0 := by omega
    have hgt : ¬ (n : ℝ) ≤ x := by
      intro hle; have := (Nat.le_floor_iff hx0.le).mpr hle; omega
    simp [hn0, hgt]
  -- Step 2: termwise difference and near/mid/far majorant
  let diff : ℕ → ℂ := fun n =>
    if n = 0 then 0
    else (ArithmeticFunction.moebius n : ℂ) *
      ((if (n : ℝ) ≤ x then (1 : ℂ) else 0) - Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T)
  have hdiff_hasSum : HasSum diff ((mertensM x : ℂ) - truncatedPerronM x c T) := by
    refine (hM_hasSum.sub hperron_hasSum).congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [diff]
    · simp only [diff, hn, ↓reduceIte]; ring
  let nearSet : Finset ℕ := {⌊x⌋₊, ⌊x⌋₊ + 1}
  let midSet : Finset ℕ := (Finset.Icc 1 (2 * ⌊x⌋₊ + 2)).filter fun n => n ∉ nearSet ∧ x ≤ 2 * (n : ℝ)
  let Maj : ℕ → ℝ := fun n =>
    if n = 0 then 0
    else if n ∈ nearSet then 61
    else if n ∈ midSet then 24 * x / (Real.pi * T * |x - (n : ℝ)|)
    else 3 * x ^ c / (Real.pi * T) * (n : ℝ) ^ (-c)
  have hMaj_summ : Summable Maj := by
    let tail : ℕ → ℝ := fun n => 3 * x ^ c / (Real.pi * T) * (if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-c))
    have htail : Summable tail := hsumR.mul_left _
    refine htail.congr_cofinite ?_
    have hfin : (({0} ∪ nearSet ∪ midSet : Finset ℕ) : Set ℕ)ᶜ ∈ Filter.cofinite :=
      Filter.mem_cofinite.mpr (by rw [compl_compl]; exact Finset.finite_toSet _)
    filter_upwards [hfin] with n hn
    simp only [Finset.coe_union, Set.mem_compl_iff, Set.mem_union, Finset.mem_coe,
      Finset.mem_singleton, not_or] at hn
    simp [Maj, tail, hn.1.1, hn.1.2, hn.2]
  have hdiff_le_Maj : ∀ n : ℕ, ‖diff n‖ ≤ Maj n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [diff, Maj]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have hy0 : 0 < x / (n : ℝ) := div_pos hx0 hnR
      simp only [diff, Maj, hn, ↓reduceIte]
      rw [norm_mul]
      have hμ1 : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := norm_moebius_le_one n
      by_cases hnear : n ∈ nearSet
      · simp only [hnear, ↓reduceIte]
        have hn_ge_half : x / 2 ≤ (n : ℝ) := by
          simp only [nearSet, Finset.mem_insert, Finset.mem_singleton] at hnear
          have hfl : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
          rcases hnear with rfl | rfl
          · linarith
          · push_cast; linarith
        have hy2 : x / (n : ℝ) ≤ 2 := by rw [div_le_iff₀ hnR]; linarith
        have hker := Stage5ContourExplicit.norm_perronKernel0_sub_ind_le_uniform hy0 hy2 hc1.le hc3 hT
        have hind_diff :
            ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) - Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T‖ ≤ 61 := by
          have h1 : (if (n : ℝ) ≤ x then (1 : ℂ) else 0) - Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T =
              -((Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T -
                (if 1 < x / (n : ℝ) then (1 : ℂ) else 0))) +
              ((if (n : ℝ) ≤ x then (1 : ℂ) else 0) - (if 1 < x / (n : ℝ) then (1 : ℂ) else 0)) := by ring
          rw [h1]
          have h2 : ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) -
              (if 1 < x / (n : ℝ) then (1 : ℂ) else 0)‖ ≤ 1 := by
            by_cases hlt : (n : ℝ) < x
            · have hlt' : 1 < x / (n : ℝ) := (one_lt_div hnR).mpr hlt
              simp [hlt.le, hlt']
            · by_cases heq : (n : ℝ) = x
              · have hdiv1 : x / (n : ℝ) = 1 := by rw [heq, div_self hx0.ne']
                rw [hdiv1, heq]; simp
              · have hgt : x < (n : ℝ) := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)
                have hlt' : ¬ 1 < x / (n : ℝ) := not_lt.mpr ((div_le_one hnR).mpr hgt.le)
                simp [not_le.mpr hgt, hlt']
          have htri := norm_add_le
            (-(Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T -
              (if 1 < x / (n : ℝ) then (1 : ℂ) else 0)))
            ((if (n : ℝ) ≤ x then (1 : ℂ) else 0) - (if 1 < x / (n : ℝ) then (1 : ℂ) else 0))
          rw [norm_neg] at htri
          linarith
        exact (mul_le_of_le_one_left (norm_nonneg _) hμ1).trans hind_diff
      · simp only [hnear, ↓reduceIte]
        have hne_x : (n : ℝ) ≠ x := by
          intro hEq
          apply hnear
          have hfl : ⌊x⌋₊ = n := by rw [← hEq, Nat.floor_natCast]
          simp [nearSet, hfl]
        have hker : ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) -
            Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T‖ ≤
            (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|) := by
          rcases lt_or_gt_of_ne hne_x with hlt | hgt
          · have h1 : 1 < x / (n : ℝ) := (one_lt_div hnR).mpr hlt
            simp only [hlt.le, ↓reduceIte]
            rw [norm_sub_rev]
            exact Stage5ContourExplicit.norm_perronKernel0_gt_one h1 hc0 hT0
          · have h1 : x / (n : ℝ) < 1 := (div_lt_one hnR).mpr hgt
            simp only [not_le.mpr hgt, ↓reduceIte, zero_sub, norm_neg]
            exact Stage5ContourExplicit.norm_perronKernel0_lt_one hy0 h1 hc0 hT0
        by_cases hmid : n ∈ midSet
        · simp only [hmid, ↓reduceIte]
          obtain ⟨hmem, -, h2n⟩ := Finset.mem_filter.mp hmid
          have hn_le : (n : ℝ) ≤ 2 * x + 2 := by
            have hle : n ≤ 2 * ⌊x⌋₊ + 2 := (Finset.mem_Icc.mp hmem).2
            have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
            have : (n : ℝ) ≤ 2 * (⌊x⌋₊ : ℝ) + 2 := by exact_mod_cast hle
            linarith
          have hlog_lb : |x - (n : ℝ)| / (2 * x + 2) ≤ |Real.log (x / (n : ℝ))| := by
            rcases lt_or_gt_of_ne hne_x with hlt | hgt
            · rw [abs_of_pos (sub_pos.mpr hlt), abs_of_pos (Real.log_pos ((one_lt_div hnR).mpr hlt))]
              have h1 := Real.log_le_sub_one_of_pos (div_pos hnR hx0)
              have hneg : Real.log ((n : ℝ) / x) = -Real.log (x / (n : ℝ)) := by
                rw [Real.log_div hnR.ne' hx0.ne', Real.log_div hx0.ne' hnR.ne']; ring
              have h2 : (x - (n : ℝ)) / x ≤ Real.log (x / (n : ℝ)) := by
                have h3 : 1 - (n : ℝ) / x = (x - (n : ℝ)) / x := by field_simp [hx0.ne']
                linarith
              exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hlt.le) hx0 (by linarith)).trans h2
            · rw [abs_of_neg (sub_neg.mpr hgt), neg_sub,
                  abs_of_neg (Real.log_neg hy0 ((div_lt_one hnR).mpr hgt))]
              have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hnR)
              have h2 : ((n : ℝ) - x) / (n : ℝ) ≤ -Real.log (x / (n : ℝ)) := by
                have h3 : 1 - x / (n : ℝ) = ((n : ℝ) - x) / (n : ℝ) := by field_simp [hnR.ne']
                linarith
              exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hgt.le) hnR hn_le).trans h2
          have hy2 : x / (n : ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr h2n
          have hyc : (x / (n : ℝ)) ^ c ≤ 8 := by
            calc (x / (n : ℝ)) ^ c ≤ 2 ^ c := Real.rpow_le_rpow hy0.le hy2 hc0.le
              _ ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
              _ = 8 := by norm_num
          have hdiff_pos : 0 < |x - (n : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hne_x.symm)
          calc ‖(ArithmeticFunction.moebius n : ℂ)‖ *
                ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) -
                  Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T‖
              ≤ (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|) :=
                (mul_le_of_le_one_left (norm_nonneg _) hμ1).trans hker
            _ ≤ 8 / (Real.pi * T * (|x - (n : ℝ)| / (2 * x + 2))) := by
                refine div_le_div₀ (by positivity) hyc (by positivity) ?_
                exact mul_le_mul_of_nonneg_left hlog_lb (by positivity)
            _ = 8 * (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) := by
                field_simp [Real.pi_ne_zero, hT0.ne', hdiff_pos.ne', (show (2 * x + 2 : ℝ) ≠ 0 by linarith)]
            _ ≤ 24 * x / (Real.pi * T * |x - (n : ℝ)|) := by
                refine div_le_div_of_nonneg_right (by linarith) (by positivity)
        · simp only [hmid, ↓reduceIte]
          have hlog_ge : (1 / 3 : ℝ) < |Real.log (x / (n : ℝ))| := by
            by_cases h2n : 2 * (n : ℝ) < x
            · have hgt2 : 2 < x / (n : ℝ) := (lt_div_iff₀ hnR).mpr h2n
              rw [abs_of_pos (Real.log_pos (by linarith))]
              linarith [hlog2.trans (Real.log_lt_log (by norm_num) hgt2)]
            · push Not at h2n
              have hn_gt : 2 * ⌊x⌋₊ + 2 < n := by
                by_contra hle; push Not at hle
                exact hmid (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hle⟩, hnear, h2n⟩)
              have hn_gt2x : 2 * x < (n : ℝ) := by
                have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
                have : (2 * ⌊x⌋₊ + 2 : ℝ) < (n : ℝ) := by exact_mod_cast hn_gt
                linarith
              have hdiv_lt : x / (n : ℝ) < 1 / 2 := by
                rw [div_lt_div_iff₀ hnR (by norm_num : (0 : ℝ) < 2)]; linarith
              rw [abs_of_neg (Real.log_neg hy0 (by linarith))]
              have h1 : Real.log (x / (n : ℝ)) < Real.log (1 / 2) := Real.log_lt_log hy0 hdiv_lt
              rw [one_div, Real.log_inv] at h1
              linarith
          calc ‖(ArithmeticFunction.moebius n : ℂ)‖ *
                ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) -
                  Stage5ContourExplicit.perronKernel0 (x / (n : ℝ)) c T‖
              ≤ (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|) :=
                (mul_le_of_le_one_left (norm_nonneg _) hμ1).trans hker
            _ ≤ (x / (n : ℝ)) ^ c / (Real.pi * T * (1 / 3)) :=
                div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le c) (by positivity)
                  (mul_le_mul_of_nonneg_left hlog_ge.le (by positivity))
            _ = 3 * x ^ c / (Real.pi * T) * (n : ℝ) ^ (-c) := by
                rw [Real.div_rpow hx0.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]
                field_simp [Real.pi_ne_zero, hT0.ne']
  -- Step 3: bound `∑' n, Maj n` via near + mid + far
  let nearF : ℕ → ℝ := fun n => if n ∈ nearSet then 61 else 0
  let midF : ℕ → ℝ := fun n => if n ∈ midSet then 24 * x / (Real.pi * T * |x - (n : ℝ)|) else 0
  let farF : ℕ → ℝ := fun n => if n = 0 then 0 else 3 * x ^ c / (Real.pi * T) * (n : ℝ) ^ (-c)
  have hnear_s : Summable nearF := summable_of_ne_finset_zero (s := nearSet) fun n hn => by simp [nearF, hn]
  have hmid_s : Summable midF := summable_of_ne_finset_zero (s := midSet) fun n hn => by simp [midF, hn]
  have hfar_s : Summable farF := (hsumR.mul_left (3 * x ^ c / (Real.pi * T))).congr fun n => by
    by_cases hn : n = 0 <;> simp [farF, hn]
  have hMaj_le : ∀ n : ℕ, Maj n ≤ nearF n + midF n + farF n := fun n => by
    by_cases hn0 : n = 0
    · subst hn0; simp [Maj, nearF, midF, farF]; positivity
    · have hnn1 : 0 ≤ nearF n := by dsimp only [nearF]; split_ifs <;> positivity
      have hnn2 : 0 ≤ midF n := by dsimp only [midF]; split_ifs <;> positivity
      have hnn3 : 0 ≤ farF n := by dsimp only [farF]; simp only [hn0, ↓reduceIte]; positivity
      simp only [Maj, hn0, ↓reduceIte]
      by_cases hnear : n ∈ nearSet
      · simp only [hnear, ↓reduceIte]; simp only [nearF, hnear, ↓reduceIte]; linarith
      · simp only [hnear, ↓reduceIte]
        by_cases hmid : n ∈ midSet
        · simp only [hmid, ↓reduceIte]; simp only [midF, hmid, ↓reduceIte]; linarith
        · simp only [hmid, ↓reduceIte]; simp only [farF, hn0, ↓reduceIte]; linarith
  have hnear_sum : ∑' n, nearF n ≤ 122 := by
    rw [tsum_eq_sum (s := nearSet) fun n hn => by simp [nearF, hn]]
    have hEq : ∑ n ∈ nearSet, nearF n = ∑ _n ∈ nearSet, (61 : ℝ) :=
      Finset.sum_congr rfl fun n hn => by simp [nearF, hn]
    rw [hEq, Finset.sum_const, nsmul_eq_mul]
    have hcard : (nearSet.card : ℝ) ≤ 2 := by
      have : nearSet.card ≤ 2 := Finset.card_le_two
      exact_mod_cast this
    linarith
  have hmid_sum : ∑' n, midF n ≤ 24 * (x / T) * (Real.log x + 2) := by
    rw [tsum_eq_sum (s := midSet) fun n hn => by simp [midF, hn]]
    have hEq : ∑ n ∈ midSet, midF n =
        (24 * x / (Real.pi * T)) * ∑ n ∈ midSet, (1 / |x - (n : ℝ)|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      simp only [midF, hn, ↓reduceIte]
      ring
    rw [hEq]
    set N : ℕ := ⌊x⌋₊
    have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
    have hN_le : (N : ℝ) ≤ x := Nat.floor_le hx0.le
    have hN_gt : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have hsum_inv : ∑ n ∈ midSet, (1 / |x - (n : ℝ)|) ≤ 3 + 2 * Real.log x := by
      let S_lo : Finset ℕ := midSet.filter (· < N)
      let S_hi : Finset ℕ := midSet.filter (fun n => ¬ n < N)
      have hpart : ∑ n ∈ midSet, (1 / |x - (n : ℝ)|) =
          (∑ n ∈ S_lo, (1 / |x - (n : ℝ)|)) + (∑ n ∈ S_hi, (1 / |x - (n : ℝ)|)) :=
        (Finset.sum_filter_add_sum_filter_not midSet (· < N) _).symm
      rw [hpart]
      have hlo : ∑ n ∈ S_lo, (1 / |x - (n : ℝ)|) ≤ 1 + Real.log x := by
        have hstep : ∑ n ∈ S_lo, (1 / |x - (n : ℝ)|) ≤ ∑ n ∈ S_lo, (1 / ((N - n : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hlt : n < N := (Finset.mem_filter.mp hn).2
          have hpos : (0 : ℝ) < ((N - n : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          refine div_le_div_of_nonneg_left zero_le_one hpos ?_
          have hsub : ((N - n : ℕ) : ℝ) = (N : ℝ) - (n : ℝ) := Nat.cast_sub hlt.le
          rw [hsub, abs_of_pos (by linarith)]
          linarith
        have hinj : ∑ n ∈ S_lo, (1 / ((N - n : ℕ) : ℝ)) ≤ ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg (s := S_lo.image (fun n => N - n))
            (t := Finset.Icc 1 N) (f := fun k : ℕ => (1 : ℝ) / (k : ℝ))
            (fun k hk => by
              rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
              have hlt : n < N := (Finset.mem_filter.mp hn).2
              exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le N n⟩)
            (fun k _ _ => by positivity)
          rw [Finset.sum_image (fun a ha b hb hab => by
            have ha' : a < N := (Finset.mem_filter.mp ha).2
            have hb' : b < N := (Finset.mem_filter.mp hb).2
            omega)] at hsub
          exact hsub
        have hlogN : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) hN_le
        linarith [harmonic_sum_le_one_add_log N (by omega)]
      have hhi : ∑ n ∈ S_hi, (1 / |x - (n : ℝ)|) ≤ 2 + Real.log x := by
        have hgt : ∀ n ∈ S_hi, N + 1 < n ∧ n ≤ 2 * N + 2 := fun n hn => by
          obtain ⟨hmid, hnot⟩ := Finset.mem_filter.mp hn
          obtain ⟨hIcc, hnotNear, _⟩ := Finset.mem_filter.mp hmid
          have hneN : n ≠ N := fun h => hnotNear (by simp [nearSet, N, h])
          have hneN1 : n ≠ N + 1 := fun h => hnotNear (by simp [nearSet, N, h])
          exact ⟨by omega, (Finset.mem_Icc.mp hIcc).2⟩
        have hstep : ∑ n ∈ S_hi, (1 / |x - (n : ℝ)|) ≤ ∑ n ∈ S_hi, (1 / ((n - (N + 1) : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have h1 := (hgt n hn).1
          have hpos : (0 : ℝ) < ((n - (N + 1) : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
          refine div_le_div_of_nonneg_left zero_le_one hpos ?_
          have hsub : ((n - (N + 1) : ℕ) : ℝ) = (n : ℝ) - ((N : ℝ) + 1) := by
            rw [Nat.cast_sub h1.le]; push_cast; ring
          rw [hsub, abs_of_neg (by linarith)]
          linarith
        have hinj : ∑ n ∈ S_hi, (1 / ((n - (N + 1) : ℕ) : ℝ)) ≤
            ∑ k ∈ Finset.Icc 1 (N + 1), (1 : ℝ) / (k : ℝ) := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg (s := S_hi.image (fun n => n - (N + 1)))
            (t := Finset.Icc 1 (N + 1)) (f := fun k : ℕ => (1 : ℝ) / (k : ℝ))
            (fun k hk => by
              rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
              have ⟨h1, h2⟩ := hgt n hn
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
            (fun k _ _ => by positivity)
          rw [Finset.sum_image (fun a ha b hb hab => by
            have ha' := (hgt a ha).1
            have hb' := (hgt b hb).1
            omega)] at hsub
          exact hsub
        have hlogN1 : Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log x + 1 := by
          have hle2x : ((N + 1 : ℕ) : ℝ) ≤ 2 * x := by push_cast; linarith
          calc Real.log ((N + 1 : ℕ) : ℝ) ≤ Real.log (2 * x) :=
                Real.log_le_log (by positivity) hle2x
            _ = Real.log 2 + Real.log x := Real.log_mul two_ne_zero hx0.ne'
            _ ≤ 1 + Real.log x := by linarith [Real.log_two_lt_d9]
            _ = Real.log x + 1 := by ring
        linarith [harmonic_sum_le_one_add_log (N + 1) (by omega)]
      linarith
    have hpi_gt3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hcoeff : 24 * x / (Real.pi * T) ≤ 8 * (x / T) := by
      rw [show 24 * x / (Real.pi * T) = (24 / Real.pi) * (x / T) by ring]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [div_le_iff₀ Real.pi_pos]; linarith
    calc (24 * x / (Real.pi * T)) * ∑ n ∈ midSet, (1 / |x - (n : ℝ)|)
        ≤ (8 * (x / T)) * (3 + 2 * Real.log x) :=
          mul_le_mul hcoeff hsum_inv (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ ≤ 24 * (x / T) * (Real.log x + 2) := by
          have hnn : 0 ≤ x / T := by positivity
          nlinarith
  have hfar_sum : ∑' n, farF n ≤ 3 * (x / T) * (3 * Real.log x + 1) := by
    have hEq : (∑' n, farF n) = (3 * x ^ c / (Real.pi * T)) *
        (∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-c)) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      by_cases hn : n = 0 <;> simp [farF, hn]
    rw [hEq]
    have hcoeff : 3 * x ^ c / (Real.pi * T) ≤ 3 * (x / T) := by
      rw [show 3 * x ^ c / (Real.pi * T) = (3 / Real.pi) * (x ^ c / T) by ring]
      have h1 : 3 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr Real.pi_gt_three.le
      have h2 : x ^ c / T ≤ 3 * (x / T) := by
        rw [show 3 * (x / T) = (3 * x) / T by ring]
        exact div_le_div_of_nonneg_right hxc_le hT0.le
      calc (3 / Real.pi) * (x ^ c / T) ≤ 1 * (3 * (x / T)) :=
            mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = 3 * (x / T) := one_mul _
    exact mul_le_mul hcoeff htsumR_le
      (tsum_nonneg fun n => by split_ifs <;> positivity) (by positivity)
  have hnorm_le : ‖(mertensM x : ℂ) - truncatedPerronM x c T‖ ≤ ∑' n, Maj n := by
    rw [← hdiff_hasSum.tsum_eq]
    have hdiff_summ : Summable (fun n => ‖diff n‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdiff_le_Maj hMaj_summ
    exact (norm_tsum_le_tsum_norm hdiff_summ).trans (hdiff_summ.tsum_le_tsum hdiff_le_Maj hMaj_summ)
  have hMaj_tot : ∑' n, Maj n ≤ (∑' n, nearF n) + (∑' n, midF n) + (∑' n, farF n) := by
    have h1 := hMaj_summ.tsum_le_tsum hMaj_le ((hnear_s.add hmid_s).add hfar_s)
    rwa [Summable.tsum_add (hnear_s.add hmid_s) hfar_s, Summable.tsum_add hnear_s hmid_s] at h1
  have hxT_nn : 0 ≤ x / T := by positivity
  nlinarith [hnorm_le, hMaj_tot, hnear_sum, hmid_sum, hfar_sum, hlogx_pos]

/-- **Exact Zero-Pole Perron Contour Shift for `truncatedPerronM`**:
whenever `0 < x`, `0 < σ < 1 < c`, `0 < T`, and `riemannZeta` has no zeros on `[σ, c] × [-T, T]`
away from `s = 1`, `invZetaReg s * x^s / s` is holomorphic on the entire closed rectangle
(with a removable zero at `s = 1`!), so Cauchy's rectangle theorem shifts the contour directly
from `Re(s) = c` to `Re(s) = σ` with zero pole residue! -/
theorem perron_contour_shift_mertensM {x σ c T : ℝ} (hx : 0 < x)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hc1 : 1 < c) (hT : 0 < T)
    (hzf : ∀ z : ℂ, σ ≤ z.re → z.re ≤ c → |z.im| ≤ T → z ≠ 1 → riemannZeta z ≠ 0) :
    let F : ℂ → ℂ := fun s => invZetaReg s * (x : ℂ) ^ s / s
    truncatedPerronM x c T =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (T : ℂ))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * ((-T : ℝ) : ℂ))) := by
  intro F
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hrect_sub : Stage5ContourExplicit.closedRect σ c (-T) T ⊆
      {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} := by
    intro z hz
    have hz_re : 0 < z.re := lt_of_lt_of_le hσ0 hz.1.1
    refine ⟨hz_re, ?_⟩
    by_cases hz1 : z = 1
    · subst hz1; rw [Stage6EffectivePNT.zetaReg_one]; exact one_ne_zero
    · rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hz_re hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (hzf z hz.1.1 hz.1.2 (abs_le.mpr hz.2) hz1)
  have hF_diff : DifferentiableOn ℂ F (Stage5ContourExplicit.closedRect σ c (-T) T) := by
    intro s hs
    have hs_re : 0 < s.re := lt_of_lt_of_le hσ0 hs.1.1
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; exact lt_irrefl 0 hs_re
    have hpow : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ w) s := by
      have hEq : (fun w : ℂ => (x : ℂ) ^ w) = fun w : ℂ => cexp (Complex.log (x : ℂ) * w) :=
        funext fun w => Complex.cpow_def_of_ne_zero hxC w
      rw [hEq]; fun_prop
    have hinv := (differentiableOn_invZetaReg.mono hrect_sub) s hs
    exact (hinv.mul hpow.differentiableWithinAt).div differentiableWithinAt_id hs0
  have hcauchy := Stage5ContourExplicit.rectBoundaryIntegral_eq_zero_of_differentiableOn
    (by linarith : σ ≤ c) (by linarith : -T ≤ T) hF_diff
  unfold Stage5ContourExplicit.rectBoundaryIntegral at hcauchy
  have hbot_eq : (∫ u in σ..c, F ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) =
      ∫ u in σ..c, F ((u : ℂ) + I * ((-T : ℝ) : ℂ)) :=
    intervalIntegral.integral_congr fun u _ => by congr 1; ring
  have htop_eq : (∫ u in σ..c, F ((u : ℂ) + (T : ℂ) * I)) =
      ∫ u in σ..c, F ((u : ℂ) + I * (T : ℂ)) :=
    intervalIntegral.integral_congr fun u _ => by congr 1; ring
  have hright_eq : (∫ t in (-T)..T, F ((c : ℂ) + (t : ℂ) * I)) =
      ∫ t in (-T)..T, F ((c : ℂ) + I * (t : ℂ)) :=
    intervalIntegral.integral_congr fun t _ => by congr 1; ring
  have hleft_eq : (∫ t in (-T)..T, F ((σ : ℂ) + (t : ℂ) * I)) =
      ∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ)) :=
    intervalIntegral.integral_congr fun t _ => by congr 1; ring
  rw [hbot_eq, htop_eq, hright_eq, hleft_eq] at hcauchy
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hdiv := congrArg (fun z : ℂ => (2 * (Real.pi : ℂ) * I)⁻¹ * z) hcauchy
  rw [mul_zero] at hdiv
  have hcoef : (2 * (Real.pi : ℂ) * I)⁻¹ * I = ((2 * Real.pi : ℝ) : ℂ)⁻¹ := by
    push_cast
    field_simp [Real.pi_ne_zero, I_ne_zero]
  unfold truncatedPerronM
  have hEq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + I * (t : ℂ))) -
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ))) +
       (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (T : ℂ))) -
       (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * ((-T : ℝ) : ℂ)))) = 0 := by
    calc _ = (2 * (Real.pi : ℂ) * I)⁻¹ *
          (((∫ u in σ..c, F ((u : ℂ) + I * ((-T : ℝ) : ℂ))) -
            (∫ u in σ..c, F ((u : ℂ) + I * (T : ℂ)))) +
           I * (∫ t in (-T)..T, F ((c : ℂ) + I * (t : ℂ))) -
           I * (∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ)))) := by
          rw [← hcoef]; ring
      _ = 0 := hdiv
  exact sub_eq_zero.mp hEq

/-- Helper: polynomial absorption into exponential decay `u ^ k * exp(-a * u) ≤ k! / a ^ k` for `u ≥ 0, a > 0`. -/
private lemma pow_mul_exp_neg_le {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) (k : ℕ) :
    u ^ k * Real.exp (-a * u) ≤ (k.factorial : ℝ) / a ^ k := by
  have hau : 0 ≤ a * u := mul_nonneg ha.le hu
  have h1 := Real.pow_div_factorial_le_exp (a * u) hau k
  have hfac : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have ha_pow : 0 < a ^ k := pow_pos ha k
  have hexp : Real.exp (-a * u) * Real.exp (a * u) = 1 := by
    rw [← Real.exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-a * u)).le
  rw [hexp] at h2
  rw [le_div_iff₀ ha_pow]
  have h3 : Real.exp (-a * u) * ((a * u) ^ k / (k.factorial : ℝ)) =
      (u ^ k * Real.exp (-a * u) * a ^ k) / (k.factorial : ℝ) := by
    rw [mul_pow]; ring
  rw [h3, div_le_one hfac] at h2
  exact h2

/-- Helper bound on `∫_{-T}^T ‖σ + I * t‖⁻¹ dt` for `0 < σ` and `1 ≤ T`. -/
private lemma integral_inv_norm_vertical_le {σ T : ℝ} (hσ : 0 < σ) (hT : 1 ≤ T) :
    ∫ t in (-T)..T, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 / σ + 2 * Real.log T := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hinv_cont : Continuous (fun t : ℝ => ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
    rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this; linarith
  have hmid : ∫ t in (-1 : ℝ)..1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 / σ := by
    have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ σ⁻¹ := fun t _ => by
      have hden : σ ≤ ‖(σ : ℂ) + I * (t : ℂ)‖ := by
        simpa [abs_of_pos hσ] using Complex.abs_re_le_norm ((σ : ℂ) + I * (t : ℂ))
      exact inv_anti₀ hσ hden
    calc ∫ t in (-1 : ℝ)..1, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹
        ≤ ∫ _t in (-1 : ℝ)..1, σ⁻¹ :=
          intervalIntegral.integral_mono_on (by norm_num) (hinv_cont.intervalIntegrable _ _)
            intervalIntegrable_const hpt
      _ = 2 / σ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hpos_tail : ∫ t in (1 : ℝ)..T, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log T := by
    have hint_t : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 : ℝ) T := by
      refine (ContinuousOn.inv₀ continuousOn_id fun t ht => ?_).intervalIntegrable
      rw [Set.uIcc_of_le hT] at ht; dsimp only [id_eq]; linarith [ht.1]
    calc ∫ t in (1 : ℝ)..T, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹
        ≤ ∫ t in (1 : ℝ)..T, t⁻¹ :=
          intervalIntegral.integral_mono_on hT (hinv_cont.intervalIntegrable _ _) hint_t fun t ht => by
            have ht0 : 0 < t := zero_lt_one.trans_le ht.1
            have hden : t ≤ ‖(σ : ℂ) + I * (t : ℂ)‖ := by
              simpa [abs_of_pos ht0] using Complex.abs_im_le_norm ((σ : ℂ) + I * (t : ℂ))
            exact inv_anti₀ ht0 hden
      _ = Real.log T := by rw [integral_inv_of_pos zero_lt_one hT0, div_one]
  have hneg_tail : ∫ t in (-T)..(-1 : ℝ), ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log T := by
    have hcomp : ∫ t in (-T)..(-1 : ℝ), ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ =
        ∫ u in (1 : ℝ)..T, ‖(σ : ℂ) + I * (u : ℂ)‖⁻¹ := by
      have h1 := intervalIntegral.integral_comp_neg
        (f := fun u : ℝ => ‖(σ : ℂ) + I * (u : ℂ)‖⁻¹) (a := -T) (b := -1)
      simp only [neg_neg] at h1
      rw [← h1]
      refine intervalIntegral.integral_congr fun t _ => ?_
      congr 1; rw [← Complex.norm_conj]; congr 1
      apply Complex.ext <;> simp
    rw [hcomp]; exact hpos_tail
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hinv_cont.intervalIntegrable (μ := volume) (-T) (-1))
    (hinv_cont.intervalIntegrable (μ := volume) (-1) 1)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hinv_cont.intervalIntegrable (μ := volume) (-T) 1)
    (hinv_cont.intervalIntegrable (μ := volume) 1 T)
  linarith

/-- **UNCONDITIONAL EFFECTIVE MERTENS FUNCTION BOUND (0 ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |mertensM x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem effective_mertens_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |mertensM x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₀, hc₀, hzf₀⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  obtain ⟨c₁, hc₁, C₁, hC₁, hbd_tall⟩ := inv_riemannZeta_zeroFree_bound
  obtain ⟨c₂, hc₂, C₂, hC₂, hbd_box⟩ := invZetaReg_bounded_near_one
  set c_star : ℝ := min c₀ (min c₁ (min c₂ (1 / 4)))
  have hc_star_pos : 0 < c_star := lt_min hc₀ (lt_min hc₁ (lt_min hc₂ (by norm_num)))
  have hc_star_le0 : c_star ≤ c₀ := min_le_left _ _
  have hc_star_le1 : c_star ≤ c₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hc_star_le2 : c_star ≤ c₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc_star_le4 : c_star ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set K_star : ℝ := max C₁ C₂
  have hK_star_pos : 0 < K_star := lt_of_lt_of_le hC₁ (le_max_left _ _)
  set a : ℝ := Real.sqrt (c_star / 2) with ha_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have ha_sq : a ^ 2 = c_star / 2 := Real.sq_sqrt (by positivity)
  set c_fin : ℝ := a / 2 with hc_fin_def
  have hc_fin_pos : 0 < c_fin := by positivity
  -- Threshold `x₀` so that `T = exp(a √(log x)) ≥ 4`, `log x ≥ 1`, `c = 1 + 1 / log x ≤ 2`
  set x₀ : ℝ := max 4 (Real.exp ((2 / c_star) * (Real.log 4) ^ 2 + 4))
  have hx₀_ge4 : 4 ≤ x₀ := le_max_left _ _
  -- Absorbed constant for `x ≥ x₀`
  have hP2 : ∀ u : ℝ, 0 ≤ u → u ^ 2 * Real.exp (-c_fin * u) ≤ (2 : ℝ) / c_fin ^ 2 := fun u hu => by
    simpa [Nat.factorial] using pow_mul_exp_neg_le hu hc_fin_pos 2
  have hP6 : ∀ u : ℝ, 0 ≤ u → u ^ 6 * Real.exp (-c_fin * u) ≤ (720 : ℝ) / c_fin ^ 6 := fun u hu => by
    simpa [Nat.factorial] using pow_mul_exp_neg_le hu hc_fin_pos 6
  set C_large : ℝ :=
    200 * (2 / c_fin ^ 2 + 1) + 200 + 6 * K_star * (2 * a) ^ 6 * (720 / c_fin ^ 6) +
    12 * K_star * (2 * a) ^ 5 * (120 / c_fin ^ 5) + 1
  have hC_large_pos : 0 < C_large := by positivity
  set C_small : ℝ := Real.exp (c_fin * Real.sqrt (Real.log x₀))
  set C_fin : ℝ := max C_large C_small
  have hC_fin_pos : 0 < C_fin := lt_of_lt_of_le hC_large_pos (le_max_left _ _)
  refine ⟨c_fin, hc_fin_pos, C_fin, hC_fin_pos, fun x hx2 => ?_⟩
  by_cases hbig : x₀ ≤ x
  · -- Main regime `x ≥ x₀`
    have hx4 : 4 ≤ x := hx₀_ge4.trans hbig
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    set Lx : ℝ := Real.log x with hLx_def
    have hLx_gt1 : 1 < Lx := by
      have h4 : Real.exp 1 < x := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) h4)
    have hLx_pos : 0 < Lx := zero_lt_one.trans hLx_gt1
    set u : ℝ := Real.sqrt Lx with hu_def
    have hu_pos : 0 < u := Real.sqrt_pos.mpr hLx_pos
    have hu_sq : u ^ 2 = Lx := Real.sq_sqrt hLx_pos.le
    set T : ℝ := Real.exp (a * u) with hT_def
    have hT_ge4 : 4 ≤ T := by
      have hlog_ge : (2 / c_star) * (Real.log 4) ^ 2 + 4 ≤ Lx := by
        have h1 : Real.exp ((2 / c_star) * (Real.log 4) ^ 2 + 4) ≤ x := (le_max_right _ _).trans hbig
        exact (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) h1)
      have hau_ge : Real.log 4 ≤ a * u := by
        have hsq : (Real.log 4) ^ 2 ≤ (a * u) ^ 2 := by
          rw [mul_pow, ha_sq, hu_sq]
          have h1 : (2 / c_star) * (Real.log 4) ^ 2 ≤ Lx := by linarith
          have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ c_star / 2)
          rw [← mul_assoc] at h2
          have hcancel : c_star / 2 * (2 / c_star) = 1 := by field_simp [hc_star_pos.ne']
          rw [hcancel, one_mul] at h2
          exact h2
        exact le_of_sq_le_sq hsq (by positivity)
      calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp (a * u) := Real.exp_le_exp.mpr hau_ge
    have hT1 : 1 ≤ T := by linarith
    have hT0 : 0 < T := by linarith
    have hlogT_eq : Real.log T = a * u := Real.log_exp _
    have hlogT_gt1 : 1 < Real.log T := by
      have h1 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) (by linarith))
    have hlogT2_le : Real.log (T + 2) ≤ 2 * (a * u) := by
      have h1 : T + 2 ≤ T ^ 2 := by nlinarith
      calc Real.log (T + 2) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h1
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
        _ = 2 * (a * u) := by rw [hlogT_eq]
    have hlogT2_gt1 : 1 < Real.log (T + 2) :=
      hlogT_gt1.trans (Real.log_lt_log hT0 (by linarith))
    set c : ℝ := 1 + 1 / Lx with hc_def
    have hc1 : 1 < c := by rw [hc_def]; linarith [div_pos one_pos hLx_pos]
    have hc2 : c ≤ 2 := by
      rw [hc_def]
      have : 1 / Lx ≤ 1 := (div_le_one hLx_pos).mpr hLx_gt1.le
      linarith
    have hxc_le : x ^ c ≤ 3 * x := by
      have h1 : x ^ c = x * x ^ (1 / Lx) := by rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
      have h2 : x ^ (1 / Lx) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hLx_pos.ne']
      rw [h1, h2]; nlinarith [Real.exp_one_lt_d9]
    set σ : ℝ := 1 - c_star / Real.log (T + 2) with hσ_def
    have hσ_lo : 1 / 2 ≤ σ := by
      have hdiv : c_star / Real.log (T + 2) ≤ 1 / 4 := by
        calc c_star / Real.log (T + 2) ≤ c_star / 1 :=
              div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hlogT2_gt1.le
          _ = c_star := div_one _
          _ ≤ 1 / 4 := hc_star_le4
      linarith
    have hσ_pos : 0 < σ := by linarith
    have hσ_lt1 : σ < 1 := by
      have : 0 < c_star / Real.log (T + 2) := div_pos hc_star_pos (by linarith)
      linarith
    -- Uniform bound on `invZetaReg` & zero-freeness on `[σ, c] × [-T, T]`
    have hrect_info : ∀ z : ℂ, σ ≤ z.re → z.re ≤ c → |z.im| ≤ T →
        (z ≠ 1 → riemannZeta z ≠ 0) ∧ ‖invZetaReg z‖ ≤ K_star * (Real.log (T + 2)) ^ 5 := by
      intro z hre1 hre2 him
      have hz_re2 : z.re ≤ 2 := hre2.trans hc2
      by_cases him4 : 4 ≤ |z.im|
      · have hlogz_le : Real.log (|z.im| + 2) ≤ Real.log (T + 2) :=
          Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
        have hlogz_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos (by linarith)
        have hdiv : c_star / Real.log (T + 2) ≤ c₁ / Real.log (|z.im| + 2) := by
          calc c_star / Real.log (T + 2) ≤ c_star / Real.log (|z.im| + 2) :=
                div_le_div_of_nonneg_left hc_star_pos.le hlogz_pos hlogz_le
            _ ≤ c₁ / Real.log (|z.im| + 2) :=
                div_le_div_of_nonneg_right hc_star_le1 hlogz_pos.le
        have hre_zf : 1 - c₁ / Real.log (|z.im| + 2) ≤ z.re := by linarith
        have hbd1 := hbd_tall z hre_zf hz_re2 him4
        have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_im, abs_zero] at him4; linarith
        have hdiv0 : c_star / Real.log (T + 2) ≤ c₀ / Real.log (|z.im| + 2) := by
          calc c_star / Real.log (T + 2) ≤ c_star / Real.log (|z.im| + 2) :=
                div_le_div_of_nonneg_left hc_star_pos.le hlogz_pos hlogz_le
            _ ≤ c₀ / Real.log (|z.im| + 2) :=
                div_le_div_of_nonneg_right hc_star_le0 hlogz_pos.le
        have hznz : riemannZeta z ≠ 0 := hzf₀ z (by linarith) hz1
        refine ⟨fun _ => hznz, ?_⟩
        rw [invZetaReg_eq_inv_riemannZeta (by linarith) hz1 hznz]
        calc ‖(riemannZeta z)⁻¹‖ ≤ C₁ * (Real.log (|z.im| + 2)) ^ 5 := hbd1
          _ ≤ K_star * (Real.log (T + 2)) ^ 5 :=
              mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hlogz_pos.le hlogz_le 5)
                (pow_nonneg hlogz_pos.le 5) hK_star_pos.le
      · push Not at him4
        have hre_box : 1 - c₂ ≤ z.re := by
          have h1 : c_star / Real.log (T + 2) ≤ c₂ := by
            calc c_star / Real.log (T + 2) ≤ c_star / 1 :=
                  div_le_div_of_nonneg_left hc_star_pos.le zero_lt_one hlogT2_gt1.le
              _ = c_star := div_one _
              _ ≤ c₂ := hc_star_le2
          linarith
        have hbox := hbd_box z hre_box hz_re2 him4.le
        have hlog5 : (1 : ℝ) ≤ (Real.log (T + 2)) ^ 5 := one_le_pow₀ hlogT2_gt1.le
        refine ⟨fun hz1 => ?_, ?_⟩
        · have hreg := hbox.1
          rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta (by linarith) hz1] at hreg
          exact (mul_ne_zero_iff.mp hreg).2
        · calc ‖invZetaReg z‖ ≤ C₂ := hbox.2
            _ ≤ K_star := le_max_right _ _
            _ ≤ K_star * (Real.log (T + 2)) ^ 5 := le_mul_of_one_le_right hK_star_pos.le hlog5
    -- Apply sharp Perron truncation & zero-pole contour shift
    have hPerron := norm_mertensM_sub_truncatedPerron_le hx2 hT1
    have hshift := perron_contour_shift_mertensM hx0 hσ_pos hσ_lt1 hc1 hT0
      (fun z h1 h2 h3 => (hrect_info z h1 h2 h3).1)
    let F : ℂ → ℂ := fun s => invZetaReg s * (x : ℂ) ^ s / s
    have hF_cont_rect : ContinuousOn F (Stage5ContourExplicit.closedRect σ c (-T) T) := by
      have hsub : Stage5ContourExplicit.closedRect σ c (-T) T ⊆
          {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} := by
        intro z hz
        have hz_re : 0 < z.re := lt_of_lt_of_le hσ_pos hz.1.1
        refine ⟨hz_re, ?_⟩
        by_cases hz1 : z = 1
        · subst hz1; rw [Stage6EffectivePNT.zetaReg_one]; exact one_ne_zero
        · rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hz_re hz1]
          exact mul_ne_zero (sub_ne_zero.mpr hz1) ((hrect_info z hz.1.1 hz.1.2 (abs_le.mpr hz.2)).1 hz1)
      have hpow : ContinuousOn (fun s : ℂ => (x : ℂ) ^ s) (Stage5ContourExplicit.closedRect σ c (-T) T) := by
        have hEq : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => cexp (Complex.log (x : ℂ) * s) :=
          funext fun s => Complex.cpow_def_of_ne_zero (by exact_mod_cast hx0.ne') s
        rw [hEq]; fun_prop
      exact ((differentiableOn_invZetaReg.mono hsub).continuousOn.mul hpow).div continuousOn_id
        fun s hs h0 => by have h0re := hs.1.1; rw [h0, Complex.zero_re] at h0re; linarith
    -- Bound left vertical integral
    have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ)))‖ ≤
        6 * K_star * x ^ σ * (Real.log (T + 2)) ^ 6 := by
      have hcont_t : ContinuousOn (fun t : ℝ => F ((σ : ℂ) + I * (t : ℂ))) (Set.uIcc (-T) T) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact hF_cont_rect.comp (by fun_prop) fun t ht => ⟨by simp; linarith, by simpa using ht⟩
      have hinv_cont : Continuous (fun t : ℝ => ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹) := by
        refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
        rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this; linarith
      have hpt : ∀ t ∈ Set.Icc (-T) T,
          ‖F ((σ : ℂ) + I * (t : ℂ))‖ ≤
            (K_star * (Real.log (T + 2)) ^ 5 * x ^ σ) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
        intro t ht
        have hiz := (hrect_info ((σ : ℂ) + I * (t : ℂ)) (by simp) (by simp; linarith)
          (by simpa using abs_le.mpr ht)).2
        dsimp only [F]
        rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
        rw [hre, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hiz (Real.rpow_nonneg hx0.le _)) (inv_nonneg.mpr (norm_nonneg _))
      have hinv_int := integral_inv_norm_vertical_le hσ_pos hT1
      have hinv_le : 2 / σ + 2 * Real.log T ≤ 6 * Real.log (T + 2) := by
        have h1 : 2 / σ ≤ 4 := by rw [div_le_iff₀ hσ_pos]; linarith
        have h2 : Real.log T ≤ Real.log (T + 2) := Real.log_le_log hT0 (by linarith)
        linarith
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ))‖
          ≤ 1 * ∫ t in (-T)..T, ‖F ((σ : ℂ) + I * (t : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
        _ ≤ ∫ t in (-T)..T, (K_star * (Real.log (T + 2)) ^ 5 * x ^ σ) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hcont_t.intervalIntegrable.norm
              ((hinv_cont.intervalIntegrable _ _).const_mul _) hpt
        _ = (K_star * (Real.log (T + 2)) ^ 5 * x ^ σ) * ∫ t in (-T)..T, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (K_star * (Real.log (T + 2)) ^ 5 * x ^ σ) * (6 * Real.log (T + 2)) :=
            mul_le_mul_of_nonneg_left (hinv_int.trans hinv_le) (by positivity)
        _ = 6 * K_star * x ^ σ * (Real.log (T + 2)) ^ 6 := by ring
    -- Bound top & bottom horizontal integrals
    have hHoriz_bd : ∀ s_im : ℝ, (s_im = T ∨ s_im = -T) →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ u in σ..c, F ((u : ℂ) + I * (s_im : ℂ)))‖ ≤
          6 * K_star * (x / T) * (Real.log (T + 2)) ^ 5 := by
      intro s_im hsim
      have habs : |s_im| = T := by rcases hsim with rfl | rfl <;> simp [abs_of_pos hT0]
      have hcont_u : ContinuousOn (fun v : ℝ => F ((v : ℂ) + I * (s_im : ℂ))) (Set.uIcc σ c) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact hF_cont_rect.comp (by fun_prop) fun v hv =>
          ⟨by simpa using hv, by simp [abs_le.mp (le_of_eq habs)]⟩
      have hpt : ∀ v ∈ Set.Icc σ c,
          ‖F ((v : ℂ) + I * (s_im : ℂ))‖ ≤ 3 * K_star * (x / T) * (Real.log (T + 2)) ^ 5 := by
        intro v hv
        have hiz := (hrect_info ((v : ℂ) + I * (s_im : ℂ)) (by simpa using hv.1)
          (by simpa using hv.2) (by simp [habs])).2
        have hx_pow : x ^ v ≤ 3 * x := (Real.rpow_le_rpow_of_exponent_le hx1 hv.2).trans hxc_le
        have hden : T ≤ ‖(v : ℂ) + I * (s_im : ℂ)‖ := by
          simpa [habs] using Complex.abs_im_le_norm ((v : ℂ) + I * (s_im : ℂ))
        dsimp only [F]
        rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((v : ℂ) + I * (s_im : ℂ)).re = v := by simp
        rw [hre]
        calc ‖invZetaReg ((v : ℂ) + I * (s_im : ℂ))‖ * x ^ v / ‖(v : ℂ) + I * (s_im : ℂ)‖
            ≤ (K_star * (Real.log (T + 2)) ^ 5 * (3 * x)) / T :=
              div_le_div₀ (by positivity)
                (mul_le_mul hiz hx_pow (Real.rpow_nonneg hx0.le _) (by positivity)) hT0 hden
          _ = 3 * K_star * (x / T) * (Real.log (T + 2)) ^ 5 := by ring
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hlen : c - σ ≤ 2 := by linarith
      calc (2 * Real.pi)⁻¹ * ‖∫ v in σ..c, F ((v : ℂ) + I * (s_im : ℂ))‖
          ≤ 1 * ∫ v in σ..c, ‖F ((v : ℂ) + I * (s_im : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
        _ ≤ ∫ _v in σ..c, (3 * K_star * (x / T) * (Real.log (T + 2)) ^ 5) := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hcont_u.intervalIntegrable.norm
              intervalIntegrable_const hpt
        _ = (c - σ) * (3 * K_star * (x / T) * (Real.log (T + 2)) ^ 5) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 2 * (3 * K_star * (x / T) * (Real.log (T + 2)) ^ 5) :=
            mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 6 * K_star * (x / T) * (Real.log (T + 2)) ^ 5 := by ring
    -- Compare `x / T` and `x ^ σ` with `x * exp(-a * u)`
    have hxT_eq : x / T = x * Real.exp (-a * u) := by
      rw [hT_def, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
    have hxσ_le : x ^ σ ≤ x * Real.exp (-a * u) := by
      have h1 : x ^ σ = x * Real.exp (-(c_star / Real.log (T + 2)) * Lx) := by
        rw [hσ_def, Real.rpow_def_of_pos hx0, ← hLx_def]
        have hsplit : Lx * (1 - c_star / Real.log (T + 2)) = Lx + -(c_star / Real.log (T + 2)) * Lx := by ring
        rw [hsplit, Real.exp_add, Real.exp_log hx0]
      rw [h1]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx0.le
      have hdiv : a * u ≤ (c_star / Real.log (T + 2)) * Lx := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : 0 < Real.log (T + 2))]
        calc a * u * Real.log (T + 2) ≤ a * u * (2 * (a * u)) :=
              mul_le_mul_of_nonneg_left hlogT2_le (by positivity)
          _ = 2 * a ^ 2 * u ^ 2 := by ring
          _ = c_star * Lx := by rw [ha_sq, hu_sq]; ring
      linarith
    have hsplit_exp : Real.exp (-a * u) = Real.exp (-c_fin * u) * Real.exp (-c_fin * u) := by
      rw [← Real.exp_add]; congr 1; dsimp only [c_fin]; ring
    have hexp_le1 : Real.exp (-c_fin * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    -- Bound each of the 4 terms by `const * x * exp(-c_fin * u)`!
    have h1_term : 200 * (x / T * (Lx + 1) + 1) ≤
        (200 * (2 / c_fin ^ 2 + 1) + 200) * x * Real.exp (-c_fin * u) := by
      have hLx_abs : (Lx + 1) * Real.exp (-c_fin * u) ≤ 2 / c_fin ^ 2 + 1 := by
        rw [← hu_sq, add_mul]
        linarith [hP2 u hu_pos.le]
      have h1_le_xexp : (1 : ℝ) ≤ x * Real.exp (-c_fin * u) := by
        have hx_ge : Real.exp (c_fin * u) ≤ x := by
          have hc_le_u : c_fin * u ≤ Lx := by
            have hcf : c_fin ≤ 1 := by
              have : a ≤ 1 := by
                rw [ha_def]; exact Real.sqrt_le_one.mpr (by linarith)
              dsimp only [c_fin]; linarith
            rw [← hu_sq]; nlinarith [show (1 : ℝ) ≤ u by
              rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hLx_gt1.le]
          exact (Real.exp_le_exp.mpr hc_le_u).trans_eq (Real.exp_log hx0)
        calc (1 : ℝ) = Real.exp (c_fin * u) * Real.exp (-c_fin * u) := by
              rw [← Real.exp_add]; simp
          _ ≤ x * Real.exp (-c_fin * u) := mul_le_mul_of_nonneg_right hx_ge (Real.exp_pos _).le
      have hterm_a : x / T * (Lx + 1) ≤ (2 / c_fin ^ 2 + 1) * x * Real.exp (-c_fin * u) := by
        rw [hxT_eq, hsplit_exp]
        calc x * (Real.exp (-c_fin * u) * Real.exp (-c_fin * u)) * (Lx + 1)
            = ((Lx + 1) * Real.exp (-c_fin * u)) * (x * Real.exp (-c_fin * u)) := by ring
          _ ≤ (2 / c_fin ^ 2 + 1) * (x * Real.exp (-c_fin * u)) :=
              mul_le_mul_of_nonneg_right hLx_abs (by positivity)
          _ = (2 / c_fin ^ 2 + 1) * x * Real.exp (-c_fin * u) := by ring
      linarith
    have h2_term : 6 * K_star * x ^ σ * (Real.log (T + 2)) ^ 6 ≤
        (6 * K_star * (2 * a) ^ 6 * (720 / c_fin ^ 6)) * x * Real.exp (-c_fin * u) := by
      have hpow6 : (Real.log (T + 2)) ^ 6 ≤ (2 * a) ^ 6 * u ^ 6 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith : Real.log (T + 2) ≤ 2 * a * u) 6
      calc 6 * K_star * x ^ σ * (Real.log (T + 2)) ^ 6
          ≤ 6 * K_star * (x * Real.exp (-a * u)) * ((2 * a) ^ 6 * u ^ 6) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hxσ_le (by positivity)) hpow6
              (pow_nonneg (by linarith) 6) (by positivity)
        _ = 6 * K_star * (2 * a) ^ 6 * (u ^ 6 * Real.exp (-c_fin * u)) * (x * Real.exp (-c_fin * u)) := by
            rw [hsplit_exp]; ring
        _ ≤ 6 * K_star * (2 * a) ^ 6 * (720 / c_fin ^ 6) * (x * Real.exp (-c_fin * u)) := by
            gcongr; exact hP6 u hu_pos.le
        _ = (6 * K_star * (2 * a) ^ 6 * (720 / c_fin ^ 6)) * x * Real.exp (-c_fin * u) := by ring
    have h3_term : 12 * K_star * (x / T) * (Real.log (T + 2)) ^ 5 ≤
        (12 * K_star * (2 * a) ^ 5 * (120 / c_fin ^ 5)) * x * Real.exp (-c_fin * u) := by
      have hP5 : u ^ 5 * Real.exp (-c_fin * u) ≤ (120 : ℝ) / c_fin ^ 5 := by
        simpa [Nat.factorial] using pow_mul_exp_neg_le hu_pos.le hc_fin_pos 5
      have hpow5 : (Real.log (T + 2)) ^ 5 ≤ (2 * a) ^ 5 * u ^ 5 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) (by linarith : Real.log (T + 2) ≤ 2 * a * u) 5
      rw [hxT_eq]
      calc 12 * K_star * (x * Real.exp (-a * u)) * (Real.log (T + 2)) ^ 5
          ≤ 12 * K_star * (x * Real.exp (-a * u)) * ((2 * a) ^ 5 * u ^ 5) :=
            mul_le_mul_of_nonneg_left hpow5 (by positivity)
        _ = 12 * K_star * (2 * a) ^ 5 * (u ^ 5 * Real.exp (-c_fin * u)) * (x * Real.exp (-c_fin * u)) := by
            rw [hsplit_exp]; ring
        _ ≤ 12 * K_star * (2 * a) ^ 5 * (120 / c_fin ^ 5) * (x * Real.exp (-c_fin * u)) := by
            gcongr
        _ = (12 * K_star * (2 * a) ^ 5 * (120 / c_fin ^ 5)) * x * Real.exp (-c_fin * u) := by ring
    -- Combine via triangle inequality!
    have hM_norm : |mertensM x| = ‖(mertensM x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    have htri1 : ‖(mertensM x : ℂ)‖ ≤
        ‖(mertensM x : ℂ) - truncatedPerronM x c T‖ + ‖truncatedPerronM x c T‖ := by
      simpa [sub_add_cancel] using norm_add_le ((mertensM x : ℂ) - truncatedPerronM x c T) (truncatedPerronM x c T)
    have htri2 : ‖truncatedPerronM x c T‖ ≤
        6 * K_star * x ^ σ * (Real.log (T + 2)) ^ 6 +
        12 * K_star * (x / T) * (Real.log (T + 2)) ^ 5 := by
      rw [hshift]
      have htop := hHoriz_bd T (Or.inl rfl)
      have hbot := hHoriz_bd (-T) (Or.inr rfl)
      have ht1 := norm_sub_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ))) +
         (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * (T : ℂ))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * ((-T : ℝ) : ℂ))))
      have ht2 := norm_add_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ : ℂ) + I * (t : ℂ))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * (T : ℂ))))
      linarith
    rw [hM_norm]
    have hCL : |mertensM x| ≤ C_large * x * Real.exp (-c_fin * u) := by
      rw [hM_norm]
      have hnn : 0 ≤ x * Real.exp (-c_fin * u) := by positivity
      dsimp only [C_large]
      linarith
    rw [← hM_norm]
    exact hCL.trans (by gcongr; exact le_max_left _ _)
  · -- Small regime `2 ≤ x < x₀`
    push Not at hbig
    have hM_le : |mertensM x| ≤ x := abs_mertensM_le (by linarith)
    have hexp_ge : Real.exp (-c_fin * Real.sqrt (Real.log x₀)) ≤ Real.exp (-c_fin * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hsqrt := Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hbig.le)
      nlinarith
    have hcancel : C_small * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) = 1 := by
      dsimp only [C_small]
      rw [← Real.exp_add]
      have : c_fin * Real.sqrt (Real.log x₀) + -c_fin * Real.sqrt (Real.log x₀) = 0 := by ring
      rw [this, Real.exp_zero]
    calc |mertensM x| ≤ x := hM_le
      _ = (C_small * Real.exp (-c_fin * Real.sqrt (Real.log x₀))) * x := by rw [hcancel, one_mul]
      _ = C_small * x * Real.exp (-c_fin * Real.sqrt (Real.log x₀)) := by ring
      _ ≤ C_small * x * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by gcongr
      _ ≤ C_fin * x * Real.exp (-c_fin * Real.sqrt (Real.log x)) := by gcongr; exact le_max_right _ _

/-- **UNCONDITIONAL MÖBIUS CANCELLATION `M(x) = o(x)` (0 ASSUMPTIONS!)**:
`Tendsto (fun x : ℝ => mertensM x / x) atTop (𝓝 0)`. -/
theorem mertensM_little_o :
    Tendsto (fun x : ℝ => mertensM x / x) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_mertens_bound
  have hexp_zero : Tendsto (fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => c * Real.sqrt (Real.log x)) atTop atTop :=
      Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp Real.tendsto_log_atTop
        |>.congr fun x => (Real.sqrt_eq_rpow (Real.log x)).symm)
    have h2 : Tendsto (fun x : ℝ => -(c * Real.sqrt (Real.log x))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h1
    have h3 : Tendsto (fun x : ℝ => Real.exp (-c * Real.sqrt (Real.log x))) atTop (𝓝 0) :=
      (Real.tendsto_exp_atBot.comp h2).congr fun x => by dsimp only [Function.comp_apply]; congr 1; ring
    simpa using h3.const_mul C
  refine squeeze_zero_norm' (a := fun x : ℝ => C * Real.exp (-c * Real.sqrt (Real.log x))) ?_ hexp_zero
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  linarith [hbd x hx]

/-- **VON MANGOLDT–LANDAU (1899) CONVERGENCE OF `∑_{n=1}^∞ μ(n) / n = 0` (0 ASSUMPTIONS!)**:
`Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)) atTop (𝓝 0)`. -/
theorem tsum_moebius_div_nat_eq_zero :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC, hbd⟩ := effective_mertens_bound
  -- Step 1: `t ↦ mertensM t / t ^ 2` is integrable on `Ioi 1`
  have hint_Ioi2 : IntegrableOn (fun t : ℝ => mertensM t / t ^ 2) (Ioi (2 : ℝ)) := by
    have hdom := (Stage8MertensTheorems.integrableOn_exp_neg_rpow_log_div_id hc
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
    refine Integrable.mono' hdom ?_ ?_
    · exact (measurable_mertensM.div (measurable_id.pow_const 2)).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht2 : 2 ≤ t := (Set.mem_Ioi.mp ht).le
      have ht0 : 0 < t := by linarith
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
      calc |mertensM t| / t ^ 2
          ≤ (C * t * Real.exp (-c * Real.sqrt (Real.log t))) / t ^ 2 :=
            div_le_div_of_nonneg_right (hbd t ht2) (sq_nonneg t)
        _ = C * (Real.exp (-c * (Real.log t) ^ ((1 : ℝ) / 2)) / t) := by
            rw [Real.sqrt_eq_rpow]; field_simp [ht0.ne']
  have hint_Ioc12 : IntegrableOn (fun t : ℝ => mertensM t / t ^ 2) (Ioc (1 : ℝ) 2) := by
    refine Integrable.mono' (integrableOn_const (C := 2) (hs := measure_Ioc_lt_top.ne))
      (measurable_mertensM.div (measurable_id.pow_const 2)).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)]
    have h1 : |mertensM t| ≤ 2 := (abs_mertensM_le ht0.le).trans ht.2
    have h2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith [ht.1]
    exact (div_le_iff₀ (sq_pos_of_pos ht0)).mpr (by linarith)
  have hint_Ioi1 : IntegrableOn (fun t : ℝ => mertensM t / t ^ 2) (Ioi (1 : ℝ)) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)]
    exact hint_Ioc12.union hint_Ioi2
  -- Step 2: Evaluate `∫_1^∞ mertensM t / t ^ 2 dt = 0` by DCT from `inv_riemannZeta_eq_mellin_mertensM` as `σ → 1⁺`!
  have hint_zero : ∫ t in Ioi (1 : ℝ), mertensM t / t ^ 2 = 0 := by
    -- Real-valued Mellin identity for `σ > 1`: `((riemannZeta σ)⁻¹).re = σ * ∫_1^∞ mertensM t * t^(-σ-1) dt`
    have hmellin_re : ∀ σ : ℝ, 1 < σ →
        ((riemannZeta (σ : ℂ))⁻¹).re = σ * ∫ t in Ioi (1 : ℝ), mertensM t * t ^ (-σ - 1) := by
      intro σ hσ
      have h1 := inv_riemannZeta_eq_mellin_mertensM (s := (σ : ℂ)) (by simpa using hσ)
      have hcongr : EqOn (fun t : ℝ => (mertensM t : ℂ) * (t : ℂ) ^ (-(σ : ℂ) - 1))
          (fun t : ℝ => (((mertensM t * t ^ (-σ - 1) : ℝ) : ℂ))) (Ioi (1 : ℝ)) := fun t ht => by
        have ht0 : 0 < t := zero_lt_one.trans ht
        dsimp only
        rw [show (-(σ : ℂ) - 1) = (((-σ - 1 : ℝ) : ℂ)) by push_cast; ring,
          ← Complex.ofReal_cpow ht0.le, ← Complex.ofReal_mul]
      rw [setIntegral_congr_fun measurableSet_Ioi hcongr] at h1
      have hre_int : (∫ t in Ioi (1 : ℝ), ((mertensM t * t ^ (-σ - 1) : ℝ) : ℂ)) =
          ((∫ t in Ioi (1 : ℝ), mertensM t * t ^ (-σ - 1) : ℝ) : ℂ) := integral_ofReal
      rw [hre_int] at h1
      have hre := congrArg Complex.re h1
      simpa using hre
    -- LHS limit: `(riemannZeta σ)⁻¹ → invZetaReg 1 = 0` as `σ → 1⁺`
    have hLHS : Tendsto (fun σ : ℝ => ((riemannZeta (σ : ℂ))⁻¹).re) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hcont : ContinuousAt invZetaReg (1 : ℂ) :=
        (differentiableOn_invZetaReg.differentiableAt
          (Stage6EffectivePNT.isOpen_re_pos_zetaReg_ne_zero.mem_nhds
            ⟨by norm_num, by rw [Stage6EffectivePNT.zetaReg_one]; exact one_ne_zero⟩)).continuousAt
      have h1 : Tendsto (fun σ : ℝ => (invZetaReg (σ : ℂ)).re) (𝓝[>] (1 : ℝ)) (𝓝 (invZetaReg 1).re) := by
        have hcomp : Tendsto (fun σ : ℝ => invZetaReg (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (invZetaReg 1)) :=
          (hcont.tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
        exact (Complex.continuous_re.continuousAt.tendsto.comp hcomp)
      rw [invZetaReg_one, Complex.zero_re] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
      have hσ1 : (σ : ℂ) ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith
      rw [invZetaReg_eq_inv_riemannZeta (by simp; linarith) hσ1
        (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))]
    -- RHS limit by DCT: `σ * ∫_1^∞ mertensM t * t^(-σ-1) dt → ∫_1^∞ mertensM t / t ^ 2 dt`
    have hRHS_int : Tendsto (fun σ : ℝ => ∫ t in Ioi (1 : ℝ), mertensM t * t ^ (-σ - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 (∫ t in Ioi (1 : ℝ), mertensM t / t ^ 2)) := by
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun t : ℝ => |mertensM t| / t ^ 2) ?_ ?_ ?_ ?_
      · exact eventually_nhdsWithin_of_forall fun σ _ =>
          (measurable_mertensM.mul (measurable_id.pow_const _)).aestronglyMeasurable
      · filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
        refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht1 : 1 < t := Set.mem_Ioi.mp ht
        have ht0 : 0 < t := zero_lt_one.trans ht1
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
        have hpow : t ^ (-σ - 1) ≤ (t ^ 2)⁻¹ := by
          rw [← Real.rpow_natCast t 2, ← Real.rpow_neg ht0.le]
          exact Real.rpow_le_rpow_of_exponent_le ht1.le (by push_cast; linarith)
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      · exact hint_Ioi1.norm.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          have ht0 : 0 < t := zero_lt_one.trans (Set.mem_Ioi.mp ht)
          dsimp only
          rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos ht0)])
      · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := zero_lt_one.trans (Set.mem_Ioi.mp ht)
        have hcont : ContinuousAt (fun σ : ℝ => mertensM t * t ^ (-σ - 1)) 1 := by
          refine continuousAt_const.mul ?_
          exact (ContinuousAt.rpow continuousAt_const (continuousAt_id.neg.sub continuousAt_const)
            (Or.inl ht0.ne'))
        have hval : mertensM t * t ^ (-(1 : ℝ) - 1) = mertensM t / t ^ 2 := by
          rw [show (-(1 : ℝ) - 1) = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le,
            show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
        rw [← hval]
        exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hRHS : Tendsto (fun σ : ℝ => σ * ∫ t in Ioi (1 : ℝ), mertensM t * t ^ (-σ - 1))
        (𝓝[>] (1 : ℝ)) (𝓝 (∫ t in Ioi (1 : ℝ), mertensM t / t ^ 2)) := by
      have hid : Tendsto (fun σ : ℝ => σ) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
        continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
      simpa using hid.mul hRHS_int
    have hRHS' : Tendsto (fun σ : ℝ => ((riemannZeta (σ : ℂ))⁻¹).re)
        (𝓝[>] (1 : ℝ)) (𝓝 (∫ t in Ioi (1 : ℝ), mertensM t / t ^ 2)) :=
      hRHS.congr' (by filter_upwards [self_mem_nhdsWithin] with σ hσ using (hmellin_re σ hσ).symm)
    exact tendsto_nhds_unique hRHS' hLHS
  -- Step 3: Real Abelian summation `∑_{n=1}^N μ(n)/n = M(N)/N + ∫_1^N M(t)/t² dt → 0 + 0 = 0`!
  have hBdry : Tendsto (fun N : ℕ => mertensM (N : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    mertensM_little_o.comp tendsto_natCast_atTop_atTop
  have hInt : Tendsto (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), mertensM t / t ^ 2)
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), mertensM t / t ^ 2)) :=
    (intervalIntegral_tendsto_integral_Ioi 1 hint_Ioi1 tendsto_id).comp tendsto_natCast_atTop_atTop
  rw [hint_zero] at hInt
  have hsum : Tendsto (fun N : ℕ => mertensM (N : ℝ) / (N : ℝ) +
      ∫ t in (1 : ℝ)..(N : ℝ), mertensM t / t ^ 2) atTop (𝓝 0) := by
    simpa using hBdry.add hInt
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  have hd : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ), HasDerivAt (fun u : ℝ => u⁻¹) (-(t ^ 2)⁻¹) t :=
    fun t ht => hasDerivAt_inv (zero_lt_one.trans_le ht.1).ne'
  have hc' : ContinuousOn (fun t : ℝ => -(t ^ 2)⁻¹) (Set.Icc (1 : ℝ) (N : ℝ)) :=
    (ContinuousOn.inv₀ (continuousOn_pow 2) fun t ht =>
      pow_ne_zero 2 (zero_lt_one.trans_le ht.1).ne').neg
  have hab := Stage8MertensTheorems.abel_summation_real (fun n => (ArithmeticFunction.moebius n : ℝ))
    hN1 hd hc'
  rw [Nat.floor_natCast] at hab
  have hLHS_eq : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) * (n : ℝ)⁻¹ =
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) :=
    Finset.sum_congr rfl fun n _ => by rw [div_eq_mul_inv]
  have hInt_eq : ∫ t in (1 : ℝ)..(N : ℝ),
      Stage8MertensTheorems.realStepSum (fun n => (ArithmeticFunction.moebius n : ℝ)) t * -(t ^ 2)⁻¹ =
      -(∫ t in (1 : ℝ)..(N : ℝ), mertensM t / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [← mertensM_eq_realStepSum, div_eq_mul_inv]; ring
  rw [hLHS_eq, ← mertensM_eq_realStepSum, hInt_eq, ← div_eq_mul_inv, sub_neg_eq_add] at hab
  exact hab.symm

/-! ## Section 4: Littlewood's 1912 Bidirectional Equivalence (`RH ↔ M(x) = O(x^{1/2 + ε})`) -/

/-- **Littlewood Forward Direction**: if `riemannZeta` has no zeros in `Re(s) > θ` (`0 < θ < 1`),
then for every `ε > 0`, `|mertensM x| ≤ C * x ^ (θ + ε)` for all `x ≥ 2`, proved directly from
`inv_riemannZeta_rpow_eps_of_zeroFree_halfPlane` + `norm_mertensM_sub_truncatedPerron_le` +
`perron_contour_shift_mertensM`. -/
theorem mertensM_rpow_eps_of_zeroFree_halfPlane {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hzf : ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |mertensM x| ≤ C * x ^ (θ + ε) := by
  intro ε hε
  set ε' : ℝ := min ε ((1 - θ) / 2) with hε'_def
  have hε'_pos : 0 < ε' := lt_min hε (by linarith)
  have hε'_le : ε' ≤ ε := min_le_left _ _
  have hε'_lt : ε' ≤ (1 - θ) / 2 := min_le_right _ _
  set σ : ℝ := θ + ε' / 3 with hσ_def
  have hσ_pos : 0 < σ := by linarith
  have hσ_lt1 : σ < 1 := by linarith
  set α : ℝ := ε' / 3 with hα_def
  have hα_pos : 0 < α := by positivity
  obtain ⟨C₀, hC₀_pos, hbd_tall, hbd_box⟩ :=
    inv_riemannZeta_rpow_eps_of_zeroFree_halfPlane hθ0 (by positivity : 0 < ε' / 3) (by linarith) hα_pos hzf
  -- Unified bound on `[σ, 3] × [-T, T]`: `‖invZetaReg s‖ ≤ C₀ * (|s.im| + 2) ^ α`
  have hbd_unif : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 3 → ‖invZetaReg s‖ ≤ C₀ * (|s.im| + 2) ^ α := by
    intro s hlo hhi
    by_cases him4 : 4 ≤ |s.im|
    · have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_im, abs_zero] at him4; linarith
      have hsnz : riemannZeta s ≠ 0 := hzf s (by linarith) hs1
      rw [invZetaReg_eq_inv_riemannZeta (by linarith) hs1 hsnz]
      exact hbd_tall s hlo hhi him4
    · push Not at him4
      have hbox := hbd_box s hlo hhi him4.le
      have hpow : (1 : ℝ) ≤ (|s.im| + 2) ^ α := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hα_pos.le
      exact hbox.2.trans (le_mul_of_one_le_right hC₀_pos.le hpow)
  -- Absorb `Real.log (x + 2)` into `x ^ (ε' / 3)`
  have hlog_abs : ∃ K_log : ℝ, 0 < K_log ∧ ∀ x : ℝ, 2 ≤ x → Real.log (x + 2) ≤ K_log * x ^ (ε' / 3) := by
    refine ⟨2 / (ε' / 3), by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have h1 : Real.log (x + 2) ≤ 2 * Real.log x := by
      have hsq : x + 2 ≤ x ^ 2 := by nlinarith
      calc Real.log (x + 2) ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) hsq
        _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
    have h2 := Real.log_le_rpow_div hx0.le (by positivity : 0 < ε' / 3)
    linarith [show (2 / (ε' / 3)) * x ^ (ε' / 3) = 2 * (x ^ (ε' / 3) / (ε' / 3)) by ring]
  obtain ⟨K_log, hK_log_pos, hK_log⟩ := hlog_abs
  set C_main : ℝ := 600 + C₀ * 2 ^ α * (2 / σ + 2) + 18 * C₀ * 2 ^ α
  set C_large : ℝ := C_main * K_log
  set C_fin : ℝ := max C_large 4
  refine ⟨C_fin, by positivity, fun x hx2 => ?_⟩
  by_cases hx4 : 4 ≤ x
  · have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
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
      have h1 : x ^ c = x * x ^ (1 / Real.log x) := by rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
      have h2 : x ^ (1 / Real.log x) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hlogx_pos.ne']
      rw [h1, h2]; nlinarith [Real.exp_one_lt_d9]
    have hPerron := norm_mertensM_sub_truncatedPerron_le hx2 (by linarith : 1 ≤ x)
    rw [div_self hx0.ne', one_mul] at hPerron
    have hshift := perron_contour_shift_mertensM hx0 hσ_pos hσ_lt1 hc1 hx0
      (fun z h1 _ _ hz1 => hzf z (by linarith) hz1)
    let F : ℂ → ℂ := fun s => invZetaReg s * (x : ℂ) ^ s / s
    have hF_cont_rect : ContinuousOn F (Stage5ContourExplicit.closedRect σ c (-x) x) := by
      have hsub : Stage5ContourExplicit.closedRect σ c (-x) x ⊆
          {z : ℂ | 0 < z.re ∧ Stage6EffectivePNT.zetaReg z ≠ 0} := by
        intro z hz
        have hz_re : 0 < z.re := lt_of_lt_of_le hσ_pos hz.1.1
        refine ⟨hz_re, ?_⟩
        by_cases hz1 : z = 1
        · subst hz1; rw [Stage6EffectivePNT.zetaReg_one]; exact one_ne_zero
        · rw [Stage6EffectivePNT.zetaReg_eq_mul_riemannZeta hz_re hz1]
          exact mul_ne_zero (sub_ne_zero.mpr hz1) (hzf z (by linarith [hz.1.1]) hz1)
      have hpow : ContinuousOn (fun s : ℂ => (x : ℂ) ^ s) (Stage5ContourExplicit.closedRect σ c (-x) x) := by
        have hEq : (fun s : ℂ => (x : ℂ) ^ s) = fun s : ℂ => cexp (Complex.log (x : ℂ) * s) :=
          funext fun s => Complex.cpow_def_of_ne_zero (by exact_mod_cast hx0.ne') s
        rw [hEq]; fun_prop
      exact ((differentiableOn_invZetaReg.mono hsub).continuousOn.mul hpow).div continuousOn_id
        fun s hs h0 => by have h0re := hs.1.1; rw [h0, Complex.zero_re] at h0re; linarith
    have hx2_pow : (x + 2) ^ α ≤ 2 ^ α * x ^ α := by
      rw [← Real.mul_rpow (by norm_num) hx0.le]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hα_pos.le
    -- Left vertical bound
    have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ)))‖ ≤
        C₀ * 2 ^ α * (2 / σ + 2) * x ^ (σ + α) * Real.log (x + 2) := by
      have hcont_t : ContinuousOn (fun t : ℝ => F ((σ : ℂ) + I * (t : ℂ))) (Set.uIcc (-x) x) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact hF_cont_rect.comp (by fun_prop) fun t ht => ⟨by simp; linarith, by simpa using ht⟩
      have hinv_cont : Continuous (fun t : ℝ => ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹) := by
        refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
        rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this; linarith
      have hpt : ∀ t ∈ Set.Icc (-x) x,
          ‖F ((σ : ℂ) + I * (t : ℂ))‖ ≤
            (C₀ * 2 ^ α * x ^ (σ + α)) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
        intro t ht
        have habs_t : |t| ≤ x := abs_le.mpr ht
        have hiz := hbd_unif ((σ : ℂ) + I * (t : ℂ)) (by simp) (by simp; linarith)
        have him_eq : ((σ : ℂ) + I * (t : ℂ)).im = t := by simp
        rw [him_eq] at hiz
        have hpow_t : (|t| + 2) ^ α ≤ 2 ^ α * x ^ α :=
          (Real.rpow_le_rpow (by linarith [abs_nonneg t]) (by linarith) hα_pos.le).trans hx2_pow
        dsimp only [F]
        rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((σ : ℂ) + I * (t : ℂ)).re = σ := by simp
        rw [hre, div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
        calc ‖invZetaReg ((σ : ℂ) + I * (t : ℂ))‖ * x ^ σ
            ≤ (C₀ * (2 ^ α * x ^ α)) * x ^ σ :=
              mul_le_mul_of_nonneg_right (hiz.trans (mul_le_mul_of_nonneg_left hpow_t hC₀_pos.le))
                (Real.rpow_nonneg hx0.le _)
          _ = C₀ * 2 ^ α * (x ^ σ * x ^ α) := by ring
          _ = C₀ * 2 ^ α * x ^ (σ + α) := by rw [← Real.rpow_add hx0]
      have hinv_int := integral_inv_norm_vertical_le hσ_pos hx1
      have hlog_ge1 : 1 ≤ Real.log (x + 2) :=
        hlogx_gt1.le.trans (Real.log_le_log hx0 (by linarith))
      have hinv_le : 2 / σ + 2 * Real.log x ≤ (2 / σ + 2) * Real.log (x + 2) := by
        have h1 : Real.log x ≤ Real.log (x + 2) := Real.log_le_log hx0 (by linarith)
        have h2 : 2 / σ ≤ (2 / σ) * Real.log (x + 2) := le_mul_of_one_le_right (by positivity) hlog_ge1
        linarith
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))‖
          ≤ 1 * ∫ t in (-x)..x, ‖F ((σ : ℂ) + I * (t : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
        _ ≤ ∫ t in (-x)..x, (C₀ * 2 ^ α * x ^ (σ + α)) * ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hcont_t.intervalIntegrable.norm
              ((hinv_cont.intervalIntegrable _ _).const_mul _) hpt
        _ = (C₀ * 2 ^ α * x ^ (σ + α)) * ∫ t in (-x)..x, ‖(σ : ℂ) + I * (t : ℂ)‖⁻¹ :=
            intervalIntegral.integral_const_mul _ _
        _ ≤ (C₀ * 2 ^ α * x ^ (σ + α)) * ((2 / σ + 2) * Real.log (x + 2)) :=
            mul_le_mul_of_nonneg_left (hinv_int.trans hinv_le) (by positivity)
        _ = C₀ * 2 ^ α * (2 / σ + 2) * x ^ (σ + α) * Real.log (x + 2) := by ring
    -- Horizontal bounds at `Im(s) = ±x`
    have hHoriz_bd : ∀ s_im : ℝ, (s_im = x ∨ s_im = -x) →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * (s_im : ℂ)))‖ ≤
          9 * C₀ * 2 ^ α * x ^ α := by
      intro s_im hsim
      have habs : |s_im| = x := by rcases hsim with rfl | rfl <;> simp [abs_of_pos hx0]
      have hcont_u : ContinuousOn (fun v : ℝ => F ((v : ℂ) + I * (s_im : ℂ))) (Set.uIcc σ c) := by
        rw [Set.uIcc_of_le (by linarith)]
        exact hF_cont_rect.comp (by fun_prop) fun v hv =>
          ⟨by simpa using hv, by simp [abs_le.mp (le_of_eq habs)]⟩
      have hpt : ∀ v ∈ Set.Icc σ c,
          ‖F ((v : ℂ) + I * (s_im : ℂ))‖ ≤ 3 * C₀ * 2 ^ α * x ^ α := by
        intro v hv
        have hiz := hbd_unif ((v : ℂ) + I * (s_im : ℂ)) (by simpa using hv.1) (by simp; linarith [hv.2])
        have him_eq : ((v : ℂ) + I * (s_im : ℂ)).im = s_im := by simp
        rw [him_eq, habs] at hiz
        have hx_pow : x ^ v ≤ 3 * x := (Real.rpow_le_rpow_of_exponent_le hx1 hv.2).trans hxc_le
        have hden : x ≤ ‖(v : ℂ) + I * (s_im : ℂ)‖ := by
          simpa [habs] using Complex.abs_im_le_norm ((v : ℂ) + I * (s_im : ℂ))
        dsimp only [F]
        rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        have hre : ((v : ℂ) + I * (s_im : ℂ)).re = v := by simp
        rw [hre]
        calc ‖invZetaReg ((v : ℂ) + I * (s_im : ℂ))‖ * x ^ v / ‖(v : ℂ) + I * (s_im : ℂ)‖
            ≤ (C₀ * (2 ^ α * x ^ α) * (3 * x)) / x :=
              div_le_div₀ (by positivity)
                (mul_le_mul (hiz.trans (mul_le_mul_of_nonneg_left hx2_pow hC₀_pos.le))
                  hx_pow (Real.rpow_nonneg hx0.le _) (by positivity)) hx0 hden
          _ = 3 * C₀ * 2 ^ α * x ^ α := by field_simp [hx0.ne']
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      have hlen : c - σ ≤ 3 := by linarith
      calc (2 * Real.pi)⁻¹ * ‖∫ v in σ..c, F ((v : ℂ) + I * (s_im : ℂ))‖
          ≤ 1 * ∫ v in σ..c, ‖F ((v : ℂ) + I * (s_im : ℂ))‖ :=
            mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
              (intervalIntegral.norm_integral_le_integral_norm (by linarith)) (norm_nonneg _) zero_le_one
        _ ≤ ∫ _v in σ..c, (3 * C₀ * 2 ^ α * x ^ α) := by
            rw [one_mul]
            exact intervalIntegral.integral_mono_on (by linarith) hcont_u.intervalIntegrable.norm
              intervalIntegrable_const hpt
        _ = (c - σ) * (3 * C₀ * 2 ^ α * x ^ α) := by rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 3 * (3 * C₀ * 2 ^ α * x ^ α) := mul_le_mul_of_nonneg_right hlen (by positivity)
        _ = 9 * C₀ * 2 ^ α * x ^ α := by ring
    -- Combine all four pieces!
    have hM_norm : |mertensM x| = ‖(mertensM x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    have htri1 : ‖(mertensM x : ℂ)‖ ≤
        ‖(mertensM x : ℂ) - truncatedPerronM x c x‖ + ‖truncatedPerronM x c x‖ := by
      simpa [sub_add_cancel] using norm_add_le ((mertensM x : ℂ) - truncatedPerronM x c x) (truncatedPerronM x c x)
    have htri2 : ‖truncatedPerronM x c x‖ ≤
        C₀ * 2 ^ α * (2 / σ + 2) * x ^ (σ + α) * Real.log (x + 2) + 18 * C₀ * 2 ^ α * x ^ α := by
      rw [hshift]
      have htop := hHoriz_bd x (Or.inl rfl)
      have hbot := hHoriz_bd (-x) (Or.inr rfl)
      have ht1 := norm_sub_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))) +
         (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * (x : ℂ))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * ((-x : ℝ) : ℂ))))
      have ht2 := norm_add_le
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-x)..x, F ((σ : ℂ) + I * (t : ℂ))))
        ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ v in σ..c, F ((v : ℂ) + I * (x : ℂ))))
      linarith
    have hlog_ge1 : 1 ≤ Real.log (x + 2) := hlogx_gt1.le.trans (Real.log_le_log hx0 (by linarith))
    have hxσα_ge1 : 1 ≤ x ^ (σ + α) := Real.one_le_rpow hx1 (by positivity)
    have hxα_le : x ^ α ≤ x ^ (σ + α) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hperr_le : 200 * (Real.log x + 1 + 1) ≤ 600 * x ^ (σ + α) * Real.log (x + 2) := by
      have hlog_le : Real.log x ≤ Real.log (x + 2) := Real.log_le_log hx0 (by linarith)
      have h1 : Real.log x + 1 + 1 ≤ 3 * Real.log (x + 2) := by linarith
      have h2 : 3 * Real.log (x + 2) ≤ 3 * x ^ (σ + α) * Real.log (x + 2) := by
        have := mul_le_mul_of_nonneg_right hxσα_ge1 (by linarith : 0 ≤ Real.log (x + 2))
        linarith
      linarith
    have hcomb : |mertensM x| ≤ C_main * x ^ (σ + α) * Real.log (x + 2) := by
      rw [hM_norm]
      have h1 : x ^ α ≤ x ^ (σ + α) * Real.log (x + 2) :=
        hxα_le.trans (le_mul_of_one_le_right (by positivity) hlog_ge1)
      have h2 : 18 * C₀ * 2 ^ α * x ^ α ≤ 18 * C₀ * 2 ^ α * x ^ (σ + α) * Real.log (x + 2) := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 18 * C₀ * 2 ^ α)
        linarith [show 18 * C₀ * 2 ^ α * (x ^ (σ + α) * Real.log (x + 2)) =
          18 * C₀ * 2 ^ α * x ^ (σ + α) * Real.log (x + 2) by ring]
      dsimp only [C_main]
      linarith
    have hpow_comb : x ^ (σ + α) * x ^ (ε' / 3) = x ^ (θ + ε') := by
      rw [← Real.rpow_add hx0, hσ_def, hα_def]; congr 1; ring
    have hpow_le : x ^ (θ + ε') ≤ x ^ (θ + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    calc |mertensM x| ≤ C_main * x ^ (σ + α) * Real.log (x + 2) := hcomb
      _ ≤ C_main * x ^ (σ + α) * (K_log * x ^ (ε' / 3)) :=
          mul_le_mul_of_nonneg_left (hK_log x hx2) (by positivity)
      _ = C_large * (x ^ (σ + α) * x ^ (ε' / 3)) := by dsimp only [C_large]; ring
      _ = C_large * x ^ (θ + ε') := by rw [hpow_comb]
      _ ≤ C_large * x ^ (θ + ε) := mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ ≤ C_fin * x ^ (θ + ε) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  · -- Small regime `2 ≤ x < 4`
    push Not at hx4
    have hM_le : |mertensM x| ≤ 4 := (abs_mertensM_le (by linarith)).trans hx4.le
    have hpow : (1 : ℝ) ≤ x ^ (θ + ε) := Real.one_le_rpow (by linarith) (by positivity)
    have h4 : (4 : ℝ) ≤ C_fin := le_max_right _ _
    nlinarith

/-- Helper: `{z : ℂ | θ < z.re} \ {(1 : ℂ)}` is preconnected for any `θ < 1`. -/
private lemma isPreconnected_re_gt_sdiff_one {θ : ℝ} (hθ : θ < 1) :
    IsPreconnected ({z : ℂ | θ < z.re} \ {(1 : ℂ)}) := by
  set U : Set ℂ := {z : ℂ | θ < z.re} \ {(1 : ℂ)}
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; linarith, fun h => by
    have := congrArg Complex.re h; norm_num at this⟩
  have hseg : ∀ a b : ℂ, a ∈ U → b ∈ U →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (t : ℂ)) * a + (t : ℂ) * b ∈ U) →
      JoinedIn U a b := fun a b _ _ hmem =>
    ⟨{ toFun := fun t => (1 - ((t : ℝ) : ℂ)) * a + ((t : ℝ) : ℂ) * b
       continuous_toFun := by fun_prop
       source' := by simp
       target' := by simp }, fun t => hmem t t.2⟩
  have hjoin2 : ∀ z ∈ U, JoinedIn U z (2 : ℂ) := by
    intro z hz
    have hz_re : θ < z.re := hz.1
    have hz_ne : z ≠ 1 := hz.2
    by_cases him : z.im = 0
    · by_cases hgt : 1 < z.re
      · refine hseg z 2 hz h2U fun t ht => ?_
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = (1 - t) * z.re + 2 * t := by
          simp [Complex.mul_re]; ring
        refine ⟨show θ < ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re by rw [hre]; nlinarith [ht.1, ht.2], ?_⟩
        intro h1; rw [Set.mem_singleton_iff] at h1
        have h1' : ((1 - (t : ℂ)) * z + (t : ℂ) * 2).re = 1 := by rw [h1, Complex.one_re]
        rw [hre] at h1'
        rcases eq_or_lt_of_le ht.1 with rfl | ht0 <;> nlinarith [ht.1, ht.2, hgt]
      · have hlt : z.re < 1 := lt_of_le_of_ne (le_of_not_gt hgt) fun heq =>
          hz_ne (Complex.ext heq (by simpa using him))
        have hzI : z + I ∈ U := ⟨by simpa using hz_re, fun h1 => by
          have := congrArg Complex.im h1; simp [him] at this⟩
        have h2I : (2 : ℂ) + I ∈ U := ⟨by simp; linarith, fun h1 => by
          have := congrArg Complex.im h1; simp at this⟩
        have h1 : JoinedIn U z (z + I) := hseg z (z + I) hz hzI fun t ht => by
          have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re = z.re := by simp [Complex.mul_re]; ring
          refine ⟨show θ < ((1 - (t : ℂ)) * z + (t : ℂ) * (z + I)).re by rw [hre]; exact hz_re, fun h1 => by
            rw [Set.mem_singleton_iff] at h1
            have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; linarith⟩
        have h2 : JoinedIn U (z + I) (2 + I) := hseg (z + I) (2 + I) hzI h2I fun t ht => by
          have hre : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re = (1 - t) * z.re + 2 * t := by
            simp [Complex.mul_re]; ring
          have him' : ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).im = 1 := by simp [Complex.mul_im, him]
          refine ⟨show θ < ((1 - (t : ℂ)) * (z + I) + (t : ℂ) * (2 + I)).re by
            rw [hre]; nlinarith [ht.1, ht.2], fun h1 => by
            rw [Set.mem_singleton_iff] at h1
            have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; norm_num at this⟩
        have h3 : JoinedIn U (2 + I) 2 := hseg (2 + I) 2 h2I h2U fun t _ => by
          have hre : ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re = 2 := by simp [Complex.mul_re]; ring
          refine ⟨show θ < ((1 - (t : ℂ)) * (2 + I) + (t : ℂ) * 2).re by rw [hre]; linarith, fun h1 => by
            rw [Set.mem_singleton_iff] at h1
            have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this⟩
        exact (h1.trans h2).trans h3
    · set w : ℂ := (2 : ℂ) + I * (z.im : ℂ)
      have hw : w ∈ U := ⟨by simp [w]; linarith, fun h1 => by
        have := congrArg Complex.re h1; simp [w] at this⟩
      have h1 : JoinedIn U z w := hseg z w hz hw fun t ht => by
        have hre : ((1 - (t : ℂ)) * z + (t : ℂ) * w).re = (1 - t) * z.re + 2 * t := by
          simp [w, Complex.mul_re]; ring
        have him' : ((1 - (t : ℂ)) * z + (t : ℂ) * w).im = z.im := by simp [w, Complex.mul_im]; ring
        refine ⟨show θ < ((1 - (t : ℂ)) * z + (t : ℂ) * w).re by
          rw [hre]; rcases eq_or_lt_of_le ht.1 with rfl | ht0 <;> nlinarith [ht.1, ht.2, hz_re, hθ], fun h1 => by
          rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.im h1; rw [him', Complex.one_im] at this; exact him this⟩
      have h2 : JoinedIn U w 2 := hseg w 2 hw h2U fun t _ => by
        have hre : ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re = 2 := by simp [w, Complex.mul_re]; ring
        refine ⟨show θ < ((1 - (t : ℂ)) * w + (t : ℂ) * 2).re by rw [hre]; linarith, fun h1 => by
          rw [Set.mem_singleton_iff] at h1
          have := congrArg Complex.re h1; rw [hre, Complex.one_re] at this; norm_num at this⟩
      exact h1.trans h2
  have hpc : IsPathConnected U := ⟨2, h2U, fun z hz => (hjoin2 z hz).symm⟩
  exact hpc.isConnected.isPreconnected

/-- **Littlewood Converse Direction**: if `|mertensM x| = O(x^{θ + ε})` for every `ε > 0`,
then `riemannZeta s ≠ 0` on the entire half-plane `Re(s) > θ` (`s ≠ 1`), proved by analytic
continuation of `F(s) = s ∫_1^∞ M(t) t^{-s-1} dt = 1 / ζ(s)` via the identity theorem! -/
theorem zeroFree_halfPlane_of_mertensM_rpow_eps {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hM : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |mertensM x| ≤ C * x ^ (θ + ε)) :
    ∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  intro s hs hs1
  rcases lt_or_ge s.re 1 with hlt1 | hge1
  · set ε : ℝ := (s.re - θ) / 2 with hε_def
    have hε0 : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨C, hC_pos, hCbd⟩ := hM ε hε0
    have hCbd1 : ∀ t : ℝ, 1 ≤ t → ‖(mertensM t : ℂ)‖ ≤ max C 2 * t ^ (θ + ε) := by
      intro t ht1
      rw [Complex.norm_real, Real.norm_eq_abs]
      by_cases ht2 : 2 ≤ t
      · exact (hCbd t ht2).trans
          (mul_le_mul_of_nonneg_right (le_max_left C 2) (Real.rpow_nonneg (by linarith) _))
      · push Not at ht2
        have h1 : |mertensM t| ≤ 2 := (abs_mertensM_le (by linarith)).trans ht2.le
        have hpow : (1 : ℝ) ≤ t ^ (θ + ε) := Real.one_le_rpow ht1 (by positivity)
        have h2 : (2 : ℝ) ≤ max C 2 := le_max_right C 2
        nlinarith
    set F : ℂ → ℂ := fun z => z * ∫ t in Ioi (1 : ℝ), (mertensM t : ℂ) * (t : ℂ) ^ (-z - 1)
    have hF_an : AnalyticOnNhd ℂ F {z : ℂ | θ + ε < z.re} := by
      have h1 := Stage3RealAnalyticLandau.analyticOnNhd_mellin_of_rpow_bound
        (Complex.measurable_ofReal.comp measurable_mertensM) (by positivity : 0 ≤ max C 2) hCbd1
      have hsub : F = fun z : ℂ =>
          (1 + z * ∫ t in Ioi (1 : ℝ), (mertensM t : ℂ) * (t : ℂ) ^ (-z - 1)) - 1 := by
        funext z; dsimp only [F]; ring
      rw [hsub]
      exact h1.sub analyticOnNhd_const
    set U : Set ℂ := {z : ℂ | θ + ε < z.re} \ {(1 : ℂ)}
    have hU_open : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
    have hprod_an : AnalyticOnNhd ℂ (fun z => riemannZeta z * F z) U := by
      have hzeta_an : AnalyticOnNhd ℂ riemannZeta U :=
        DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz.2).differentiableWithinAt)
          hU_open
      exact hzeta_an.mul (hF_an.mono fun _ hz => hz.1)
    have hEv : (fun z => riemannZeta z * F z) =ᶠ[𝓝 (2 : ℂ)] (fun _ => (1 : ℂ)) := by
      have hopen1 : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen1.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hmel := inv_riemannZeta_eq_mellin_mertensM hz
      have hznz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_le_re hz.le
      dsimp only [F]
      rw [← hmel, mul_inv_cancel₀ hznz]
    have h2U : (2 : ℂ) ∈ U := ⟨by simp; rw [hε_def]; linarith, fun h => by
      have := congrArg Complex.re h; norm_num at this⟩
    have hsU : s ∈ U := ⟨by change θ + ε < s.re; rw [hε_def]; linarith, hs1⟩
    have heq := hprod_an.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (isPreconnected_re_gt_sdiff_one (by rw [hε_def]; linarith)) h2U hEv hsU
    intro hz0
    dsimp only at heq
    rw [hz0, zero_mul] at heq
    exact zero_ne_one heq
  · exact riemannZeta_ne_zero_of_one_le_re hge1

/-- **UNCONDITIONAL SHARP BIDIRECTIONAL EQUIVALENCE: ZERO-FREE HALF-PLANE `Re(s) > θ` ↔ `M(x) = O(x^{θ + ε})`**. -/
theorem zeroFree_halfPlane_iff_mertensM_rpow_eps {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∀ s : ℂ, θ < s.re → s ≠ 1 → riemannZeta s ≠ 0) ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |mertensM x| ≤ C * x ^ (θ + ε)) :=
  ⟨mertensM_rpow_eps_of_zeroFree_halfPlane hθ0 hθ1, zeroFree_halfPlane_of_mertensM_rpow_eps hθ0 hθ1⟩

/-- **LITTLEWOOD'S 1912 BIDIRECTIONAL EQUIVALENCE (`RiemannHypothesis ↔ M(x) = O(x^{1/2 + ε})`, 0 ASSUMPTIONS!)**:
directly on Mathlib's actual `RiemannHypothesis` and `mertensM`. -/
theorem riemannHypothesis_iff_mertensM_sqrt_eps :
    RiemannHypothesis ↔
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |mertensM x| ≤ C * x ^ ((1 : ℝ) / 2 + ε)) := by
  rw [RHDirect.riemannHypothesis_iff_nonvanishingRightOfHalf]
  exact zeroFree_halfPlane_iff_mertensM_rpow_eps (by norm_num) (by norm_num)

/-! ## Section 5: Exact Classical Average Orders (`6 / π²`, `3 / π²`, `π² / 12`, Dirichlet Hyperbola) -/

/-- Exact Basel identity `∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ = Real.pi ^ 2 / 6` from Mathlib's `hasSum_zeta_two`. -/
theorem tsum_inv_sq_eq_pi_sq_div_six :
    ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ = Real.pi ^ 2 / 6 := by
  simpa [one_div] using hasSum_zeta_two.tsum_eq

/-- Exact evaluation `riemannZeta 2 = ↑Real.pi ^ 2 / 6`. -/
theorem riemannZeta_two_val :
    riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta (s := (2 : ℂ)) (by norm_num)]
  have hcast : LSeries (fun n => (ArithmeticFunction.zeta n : ℂ)) 2 =
      (((∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn, ↓reduceIte, ArithmeticFunction.zeta_apply, Nat.cast_one]
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast; rw [one_div]
  rw [hcast, tsum_inv_sq_eq_pi_sq_div_six]
  push_cast; rfl

/-- Exact Möbius reciprocal-square series `∑' n : ℕ, (μ n : ℝ) / n ^ 2 = 6 / Real.pi ^ 2`. -/
theorem tsum_moebius_div_sq_eq_six_div_pi_sq :
    ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2 = 6 / Real.pi ^ 2 := by
  have hL := LSeries_moebius_eq_inv_riemannZeta (s := (2 : ℂ)) (by norm_num)
  rw [riemannZeta_two_val] at hL
  have hcast : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) 2 =
      (((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · simp only [LSeries.term, hn, ↓reduceIte]
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
      push_cast; rfl
  rw [hcast] at hL
  have hre := congrArg Complex.re hL
  have hpi : (((Real.pi : ℂ) ^ 2 / 6)⁻¹).re = 6 / Real.pi ^ 2 := by
    rw [show ((Real.pi : ℂ) ^ 2 / 6)⁻¹ = (((6 / Real.pi ^ 2 : ℝ) : ℂ)) by
      push_cast; rw [inv_div], Complex.ofReal_re]
  rwa [Complex.ofReal_re, hpi] at hre

/-- Elementary telescoping tail bound: for any `M ≥ 1` and `f : ℕ → ℝ` with `f 0 = 0` and `|f n| ≤ 1`,
`|(∑ n ∈ Finset.Icc 1 M, f n / n ^ 2) - ∑' n : ℕ, f n / n ^ 2| ≤ 1 / M`. -/
lemma abs_partial_sum_div_sq_sub_tsum_le {f : ℕ → ℝ} (hf0 : f 0 = 0) (hf1 : ∀ n, |f n| ≤ 1)
    {M : ℕ} (hM : 1 ≤ M) :
    |(∑ n ∈ Finset.Icc 1 M, f n / (n : ℝ) ^ 2) - ∑' n : ℕ, f n / (n : ℝ) ^ 2| ≤ 1 / (M : ℝ) := by
  have hinv_summ : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr one_lt_two
  have hf_summ : Summable (fun n : ℕ => f n / (n : ℝ) ^ 2) := by
    refine Summable.of_norm_bounded hinv_summ fun n => ?_
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ)), div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _)) (hf1 n)
  have hsplit := hf_summ.sum_add_tsum_nat_add (M + 1)
  have hfin : ∑ n ∈ Finset.range (M + 1), f n / (n : ℝ) ^ 2 =
      ∑ n ∈ Finset.Icc 1 M, f n / (n : ℝ) ^ 2 := by
    have hset : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 M), hf0, zero_div, zero_add]
  rw [hfin] at hsplit
  have hdiff : (∑ n ∈ Finset.Icc 1 M, f n / (n : ℝ) ^ 2) - ∑' n : ℕ, f n / (n : ℝ) ^ 2 =
      -(∑' k : ℕ, f (k + (M + 1)) / ((k + (M + 1) : ℕ) : ℝ) ^ 2) := by
    linarith
  rw [hdiff, abs_neg]
  have hshift_inv : Summable (fun k : ℕ => (((k + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff (M + 1)).mpr hinv_summ
  have hshift_f : Summable (fun k : ℕ => f (k + (M + 1)) / ((k + (M + 1) : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (M + 1)).mpr hf_summ
  have hnorm_tsum : |∑' k : ℕ, f (k + (M + 1)) / ((k + (M + 1) : ℕ) : ℝ) ^ 2| ≤
      ∑' k : ℕ, (((k + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
    have h1 := norm_tsum_le_tsum_norm hshift_f.norm
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (hshift_f.norm.tsum_le_tsum (fun k => ?_) hshift_inv)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ((k + (M + 1) : ℕ) : ℝ)), div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _)) (hf1 _)
  -- Telescoping bound on every partial sum `∑_{k < K} 1 / (k + M + 1)^2 ≤ 1 / M - 1 / (M + K)`
  have htele : ∀ K : ℕ, ∑ k ∈ Finset.range K, (((k + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ ≤
      1 / (M : ℝ) - 1 / ((M + K : ℕ) : ℝ) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have hMK0 : (0 : ℝ) < ((M + K : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hMK1 : (0 : ℝ) < ((M + K + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hstep : (((K + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ ≤
          1 / ((M + K : ℕ) : ℝ) - 1 / ((M + K + 1 : ℕ) : ℝ) := by
        have heq1 : ((K + (M + 1) : ℕ) : ℝ) = ((M + K + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [heq1]
        have hrhs : 1 / ((M + K : ℕ) : ℝ) - 1 / ((M + K + 1 : ℕ) : ℝ) =
            1 / (((M + K : ℕ) : ℝ) * ((M + K + 1 : ℕ) : ℝ)) := by
          field_simp [hMK0.ne', hMK1.ne']
          push_cast; ring
        rw [hrhs, one_div]
        refine inv_anti₀ (mul_pos hMK0 hMK1) ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (by push_cast; linarith) hMK1.le
      have hsucc : ((M + (K + 1) : ℕ) : ℝ) = ((M + K + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hsucc]
      linarith
  have htail_le : ∑' k : ℕ, (((k + (M + 1) : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / (M : ℝ) := by
    refine le_of_tendsto hshift_inv.hasSum.tendsto_sum_nat (Eventually.of_forall fun K => ?_)
    have h1 := htele K
    have hnn : 0 ≤ 1 / ((M + K : ℕ) : ℝ) := by positivity
    linarith
  exact hnorm_tsum.trans htail_le

/-- Exact Möbius divisor-sum identity `∑_{d ∣ m} μ(d) = if m = 1 then 1 else 0` for all `m ≥ 1`. -/
lemma sum_divisors_moebius_eq_ite {m : ℕ} (hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ) = if m = 1 then 1 else 0 := by
  have h := ArithmeticFunction.ext_iff.mp ArithmeticFunction.moebius_mul_coe_zeta m
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at h
  have hEq : ∑ x ∈ m.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 *
      ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2) =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ) := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b => ArithmeticFunction.moebius a *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) b))]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdiv_pos : m / d ≠ 0 := by
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
      have hd_le : d ≤ m := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
      exact (Nat.div_pos hd_le hd_pos).ne'
    simp [ArithmeticFunction.zeta_apply, hdiv_pos]
  rw [← hEq]
  exact h

/-- Pointwise squarefree indicator identity via Möbius function: for every `n ≥ 1`,
`∑_{1 ≤ d ≤ n, d² ∣ n} μ(d) = if Squarefree n then 1 else 0`. -/
lemma sum_moebius_sq_dvd_eq_ite {n : ℕ} (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℤ) else 0) =
      if Squarefree n then 1 else 0 := by
  have hn0 : n ≠ 0 := by omega
  set m : ℕ := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)
  have hm0 : m ≠ 0 := by
    dsimp only [m]
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
  have hm_fac : ∀ p : ℕ, m.factorization p = n.factorization p / 2 := by
    intro p
    dsimp only [m]
    rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
    simp only [Finsupp.finsetSum_apply]
    have hterm : ∀ q ∈ n.primeFactors,
        (q ^ (n.factorization q / 2)).factorization p =
          if q = p then n.factorization q / 2 else 0 := fun q hq => by
      rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors hq)]
      simp [Finsupp.single_apply]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases hp : p ∈ n.primeFactors
    · simp [hp]
    · simp only [hp, ↓reduceIte]
      have h0 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by
        rwa [Nat.support_factorization])
      rw [h0]; simp
  have hd_iff : ∀ d : ℕ, 1 ≤ d → (d ^ 2 ∣ n ↔ d ∣ m) := by
    intro d hd
    have hd0 : d ≠ 0 := by omega
    rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hn0,
        ← Nat.factorization_le_iff_dvd hd0 hm0]
    constructor
    · intro h p
      have hp := h p
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hp
      rw [hm_fac p]
      omega
    · intro h p
      have hp := h p
      rw [hm_fac p] at hp
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      omega
  have hm_sq_dvd : m ^ 2 ∣ n := (hd_iff m hm_pos).mpr dvd_rfl
  have hm_le_n : m ≤ n := le_trans (by nlinarith : m ≤ m ^ 2) (Nat.le_of_dvd (by omega) hm_sq_dvd)
  have hsq_iff : Squarefree n ↔ m = 1 := by
    constructor
    · intro hsf
      by_contra hm1
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hm1
      have hp2 : p ^ 2 ∣ n := (hd_iff p hp_prime.one_le).mpr hp_dvd
      rw [sq] at hp2
      exact hp_prime.not_isUnit (hsf p hp2)
    · intro hm1 x hxx
      have hx0 : x ≠ 0 := fun h => by subst h; simp at hxx; exact hn0 hxx
      have hx_dvd : x ∣ m := (hd_iff x (Nat.pos_of_ne_zero hx0)).mp (by rwa [sq])
      rw [hm1, Nat.dvd_one] at hx_dvd
      rw [hx_dvd]; exact isUnit_one
  have hfilter : (Finset.Icc 1 n).filter (fun d => d ^ 2 ∣ n) = m.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, _⟩, hdvd⟩
      exact ⟨(hd_iff d hd1).mp hdvd, hm0⟩
    · rintro ⟨hdvd, _⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hm_pos
      exact ⟨⟨hd1, (Nat.le_of_dvd hm_pos hdvd).trans hm_le_n⟩, (hd_iff d hd1).mpr hdvd⟩
  rw [← Finset.sum_filter, hfilter, sum_divisors_moebius_eq_ite hm_pos]
  by_cases h : Squarefree n
  · simp [h, hsq_iff.mp h]
  · simp [h, mt hsq_iff.mpr h]

/-- **EXACT SQUAREFREE DENSITY `6 / π²` WITH `O(√x)` ERROR (0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 1, |#({n ∈ [1, ⌊x⌋₊] | Squarefree n}) - (6 / π²) * x| ≤ C * √x`. -/
theorem squarefree_counting_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(((Finset.Icc 1 ⌊x⌋₊).filter Squarefree).card : ℝ) - (6 / Real.pi ^ 2) * x| ≤
        C * Real.sqrt x := by
  refine ⟨4, by norm_num, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set M : ℕ := ⌊Real.sqrt x⌋₊
  have hsq1 : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx
  have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hsq1)
  have hM_le : (M : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  have hM_gt : Real.sqrt x < (M : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt x)
  have hM_le_N : M ≤ N := by
    have hsq_le : Real.sqrt x ≤ x := by
      have : x ≤ x ^ 2 := by nlinarith
      exact (Real.sqrt_le_sqrt this).trans_eq (Real.sqrt_sq hx0.le)
    exact Nat.floor_mono hsq_le
  -- Step 1: Exact integer identity `#(Squarefree ≤ N) = ∑_{d=1}^M μ(d) * (N / d^2)`
  have hcard_int : (((Finset.Icc 1 N).filter Squarefree).card : ℤ) =
      ∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
    have h1 : (((Finset.Icc 1 N).filter Squarefree).card : ℤ) =
        ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then (1 : ℤ) else 0) := by
      rw [Finset.sum_boole]
    rw [h1]
    have h2 : ∑ n ∈ Finset.Icc 1 N, (if Squarefree n then (1 : ℤ) else 0) =
        ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
          (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℤ) else 0) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      rw [← sum_moebius_sq_dvd_eq_ite hn1]
      refine Finset.sum_subset (Finset.Icc_subset_Icc_right hnN) fun d hd hnot => ?_
      have hd_gt : n < d := by
        simp only [Finset.mem_Icc] at hd hnot; omega
      have hndvd : ¬ d ^ 2 ∣ n := fun h => by
        have hle := Nat.le_of_dvd (by omega) h
        have : d ≤ d ^ 2 := by nlinarith
        omega
      simp [hndvd]
    rw [h2, Finset.sum_comm]
    have hinner : ∀ d ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N, (if d ^ 2 ∣ n then (ArithmeticFunction.moebius d : ℤ) else 0) =
          (ArithmeticFunction.moebius d : ℤ) * ((N / d ^ 2 : ℕ) : ℤ) := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd2_pos : 0 < d ^ 2 := by positivity
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      congr 1
      have hbij : ((Finset.Icc 1 N).filter (fun n => d ^ 2 ∣ n)).card = (Finset.Icc 1 (N / d ^ 2)).card := by
        refine Finset.card_bij (fun n _ => n / d ^ 2) ?_ ?_ ?_
        · intro n hn
          obtain ⟨hIcc, hdvd⟩ := Finset.mem_filter.mp hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hIcc).1
          have hnN : n ≤ N := (Finset.mem_Icc.mp hIcc).2
          exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd2_pos,
            Nat.div_le_div_right hnN⟩
        · intro a ha b hb hab
          have ha_dvd : d ^ 2 ∣ a := (Finset.mem_filter.mp ha).2
          have hb_dvd : d ^ 2 ∣ b := (Finset.mem_filter.mp hb).2
          rw [← Nat.mul_div_cancel' ha_dvd, ← Nat.mul_div_cancel' hb_dvd, hab]
        · intro k hk
          refine ⟨d ^ 2 * k, ?_, Nat.mul_div_cancel_left k hd2_pos⟩
          obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
          exact (Nat.mul_le_mul_left (d ^ 2) hk2).trans (Nat.mul_div_le N (d ^ 2))
      rw [hbij, Nat.card_Icc]; simp
    rw [Finset.sum_congr rfl hinner]
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hM_le_N) fun d hd hnot => ?_
    have hd_gt : M < d := by simp only [Finset.mem_Icc] at hd hnot; omega
    have hgt_N : N < d ^ 2 := by
      have hd_ge : (M : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast hd_gt
      have hsq : x < (d : ℝ) ^ 2 := by
        have h1 : Real.sqrt x < (d : ℝ) := lt_of_lt_of_le hM_gt hd_ge
        calc x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx0.le).symm
          _ < (d : ℝ) ^ 2 := pow_lt_pow_left₀ h1 (Real.sqrt_nonneg x) two_ne_zero
      have hN_le : (N : ℝ) ≤ x := Nat.floor_le hx0.le
      have hNd : (N : ℝ) < ((d ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hNd
    rw [Nat.div_eq_of_lt hgt_N]; simp
  -- Step 2: Cast to `ℝ` and compare with `(6 / π²) * x`
  have hcard_real : (((Finset.Icc 1 N).filter Squarefree).card : ℝ) =
      ∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ) := by
    have hc := congrArg (Int.cast (R := ℝ)) hcard_int
    simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] using hc
  rw [hcard_real]
  have hdiff_split :
      (∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ)) -
        (6 / Real.pi ^ 2) * x =
      (∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) *
        (((N / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)) +
      x * ((∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) - 6 / Real.pi ^ 2) := by
    rw [mul_sub, Finset.mul_sum]
    have h1 : ∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) *
        (((N / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2) =
        (∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) * ((N / d ^ 2 : ℕ) : ℝ)) -
        (∑ d ∈ Finset.Icc 1 M, x * ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    linarith
  rw [hdiff_split]
  -- Term 1: `|((N / d^2 : ℕ) : ℝ) - x / d^2| ≤ 2` (in fact `≤ 1` since `N / d^2 = ⌊x / d^2⌋₊`!)
  have hterm1 : |∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) *
      (((N / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| ≤ 2 * Real.sqrt x := by
    calc |∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) *
            (((N / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)|
        ≤ ∑ d ∈ Finset.Icc 1 M, |(ArithmeticFunction.moebius d : ℝ) *
            (((N / d ^ 2 : ℕ) : ℝ) - x / (d : ℝ) ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Finset.Icc 1 M, (2 : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hd2_pos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
          rw [abs_mul]
          refine (mul_le_of_le_one_left (abs_nonneg _) (abs_moebius_le_one d)).trans ?_
          have hq_le : ((N / d ^ 2 : ℕ) : ℝ) ≤ x / (d : ℝ) ^ 2 := by
            rw [le_div_iff₀ hd2_pos]
            have h1 : (N / d ^ 2 : ℕ) * d ^ 2 ≤ N := Nat.div_mul_le_self N (d ^ 2)
            have h2 : ((N / d ^ 2 : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast h1
            exact h2.trans (Nat.floor_le hx0.le)
          have hq_gt : x / (d : ℝ) ^ 2 - 2 < ((N / d ^ 2 : ℕ) : ℝ) := by
            have h1 : N < (N / d ^ 2 + 1) * d ^ 2 := by
              have := Nat.lt_div_mul_add (a := N) (b := d ^ 2) (by positivity)
              linarith [Nat.add_mul (N / d ^ 2) 1 (d ^ 2)]
            have h2 : (N : ℝ) < (((N / d ^ 2 : ℕ) : ℝ) + 1) * (d : ℝ) ^ 2 := by exact_mod_cast h1
            have h3 : x - 1 < (N : ℝ) := Nat.sub_one_lt_floor x
            have h4 : (x - 1) / (d : ℝ) ^ 2 < ((N / d ^ 2 : ℕ) : ℝ) + 1 :=
              (div_lt_iff₀ hd2_pos).mpr (by linarith)
            have h5 : 1 / (d : ℝ) ^ 2 ≤ 1 := by
              rw [div_le_one hd2_pos]
              have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
              nlinarith
            linarith [show (x - 1) / (d : ℝ) ^ 2 = x / (d : ℝ) ^ 2 - 1 / (d : ℝ) ^ 2 by ring]
          rw [abs_le]; constructor <;> linarith
      _ = 2 * (M : ℝ) := by simp [mul_comm]
      _ ≤ 2 * Real.sqrt x := by linarith
  -- Term 2: `x * |∑_{d=1}^M μ(d)/d² - 6/π²| ≤ x / M ≤ 2 √x`
  have hterm2 : |x * ((∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) -
      6 / Real.pi ^ 2)| ≤ 2 * Real.sqrt x := by
    rw [abs_mul, abs_of_pos hx0, ← tsum_moebius_div_sq_eq_six_div_pi_sq]
    have htail := abs_partial_sum_div_sq_sub_tsum_le (f := fun n => (ArithmeticFunction.moebius n : ℝ))
      (by simp) abs_moebius_le_one hM1
    have hM_half : Real.sqrt x / 2 ≤ (M : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
      linarith
    have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
    calc x * |(∑ d ∈ Finset.Icc 1 M, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) ^ 2) -
              ∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2|
        ≤ x * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left htail hx0.le
      _ ≤ x * (1 / (Real.sqrt x / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left zero_le_one (by positivity) hM_half) hx0.le
      _ = 2 * Real.sqrt x := by
          have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
          field_simp [hsq_pos.ne']
          exact (Real.sq_sqrt hx0.le).symm
  exact (abs_add_le _ _).trans (by linarith)

/-- Pointwise Möbius inversion identity for Euler's totient: for every `n ≥ 1`,
`(Nat.totient n : ℤ) = ∑ d ∈ n.divisors, μ(d) * (n / d)`. -/
lemma totient_eq_sum_moebius_div {n : ℕ} (hn : 1 ≤ n) :
    (Nat.totient n : ℤ) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * ((n / d : ℕ) : ℤ) := by
  have hn0 : n ≠ 0 := by omega
  have h1 : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * ((n / d : ℕ) : ℤ) =
      ∑ d ∈ n.divisors, ∑ k ∈ (n / d).divisors,
        (ArithmeticFunction.moebius d : ℤ) * (Nat.totient k : ℤ) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    have hnd : ((n / d : ℕ) : ℤ) = ∑ k ∈ (n / d).divisors, (Nat.totient k : ℤ) := by
      rw [← Nat.cast_sum, Nat.sum_totient]
    rw [hnd, Finset.mul_sum]
  rw [h1]
  -- Swap the divisor sum `(d ∣ n, k ∣ n / d) ↔ (k ∣ n, d ∣ n / k)` via ambient `n.divisors ×ˢ n.divisors`
  have hswap1 : ∑ d ∈ n.divisors, ∑ k ∈ (n / d).divisors,
        (ArithmeticFunction.moebius d : ℤ) * (Nat.totient k : ℤ) =
      ∑ d ∈ n.divisors, ∑ k ∈ n.divisors,
        if d * k ∣ n then (ArithmeticFunction.moebius d : ℤ) * (Nat.totient k : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp only [Nat.mem_divisors, Finset.mem_filter]
    have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hnd_ne : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hd_dvd) hd_pos).ne'
    constructor
    · rintro ⟨hk, _⟩
      have hdk : d * k ∣ n := by
        rcases hk with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        calc n = d * (n / d) := (Nat.mul_div_cancel' hd_dvd).symm
          _ = d * (k * m) := by rw [hm]
          _ = d * k * m := by ring
      exact ⟨⟨dvd_trans (dvd_mul_left k d) hdk, hn0⟩, hdk⟩
    · rintro ⟨_, hdk⟩
      refine ⟨?_, hnd_ne⟩
      rcases hdk with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left hd_pos
      calc d * (n / d) = n := Nat.mul_div_cancel' hd_dvd
        _ = d * (k * m) := by rw [hm]; ring
  have hswap2 : ∑ k ∈ n.divisors, ∑ d ∈ n.divisors,
        (if d * k ∣ n then (ArithmeticFunction.moebius d : ℤ) * (Nat.totient k : ℤ) else 0) =
      ∑ k ∈ n.divisors, (Nat.totient k : ℤ) *
        ∑ d ∈ (n / k).divisors, (ArithmeticFunction.moebius d : ℤ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => mul_comm _ _
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    have hk_dvd : k ∣ n := Nat.dvd_of_mem_divisors hk
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hnk_ne : n / k ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) hk_dvd) hk_pos).ne'
    constructor
    · rintro ⟨_, hdk⟩
      refine ⟨?_, hnk_ne⟩
      rcases hdk with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left hk_pos
      calc k * (n / k) = n := Nat.mul_div_cancel' hk_dvd
        _ = k * (d * m) := by rw [hm]; ring
    · rintro ⟨hd, _⟩
      have hdk : d * k ∣ n := by
        rcases hd with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        calc n = k * (n / k) := (Nat.mul_div_cancel' hk_dvd).symm
          _ = k * (d * m) := by rw [hm]
          _ = d * k * m := by ring
      exact ⟨⟨dvd_trans (dvd_mul_right d k) hdk, hn0⟩, hdk⟩
  rw [hswap1, Finset.sum_comm, hswap2]
  have hcollapse : ∑ k ∈ n.divisors, (Nat.totient k : ℤ) *
        ∑ d ∈ (n / k).divisors, (ArithmeticFunction.moebius d : ℤ) =
      ∑ k ∈ n.divisors, (if k = n then (Nat.totient k : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_dvd : k ∣ n := Nat.dvd_of_mem_divisors hk
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hnk_pos : 1 ≤ n / k := Nat.div_pos (Nat.le_of_dvd (by omega) hk_dvd) hk_pos
    rw [sum_divisors_moebius_eq_ite hnk_pos]
    have hiff : n / k = 1 ↔ k = n := by
      constructor
      · intro h1
        have := Nat.mul_div_cancel' hk_dvd
        rw [h1, mul_one] at this; exact this
      · rintro rfl; exact Nat.div_self (by omega)
    by_cases hkn : k = n
    · subst hkn; simp [Nat.div_self (by omega : 0 < k)]
    · simp [hkn, mt hiff.mp hkn]
  rw [hcollapse, Finset.sum_ite_eq']
  simp [Nat.mem_divisors, hn0]

/-- Elementary triangular-number sum `∑_{k=1}^q k = q * (q + 1) / 2` in `ℝ`. -/
private lemma sum_Icc_nat_real (q : ℕ) :
    ∑ k ∈ Finset.Icc 1 q, (k : ℝ) = ((q : ℝ) * ((q : ℝ) + 1)) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hIcc : Finset.Icc 1 (q + 1) = insert (q + 1) (Finset.Icc 1 q) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp : q + 1 ∉ Finset.Icc 1 q), ih]
    push_cast; ring

/-- Shared quadratic approximation lemma for `∑_{d=1}^N f(d) * (⌊N/d⌋ (⌊N/d⌋ + 1) / 2)`:
for any `f : ℕ → ℝ` with `f 0 = 0` and `|f d| ≤ 1`, and any `x ≥ 2`, `N = ⌊x⌋₊`:
`|∑_{d=1}^N f(d) * (N/d)(N/d + 1)/2 - (1/2) (∑' d, f(d)/d²) * x²| ≤ 10 * x * Real.log x`. -/
private lemma abs_sum_triangular_floor_sub_le {f : ℕ → ℝ} (hf0 : f 0 = 0) (hf1 : ∀ n, |f n| ≤ 1)
    {x : ℝ} (hx : 2 ≤ x) :
    |∑ d ∈ Finset.Icc 1 ⌊x⌋₊, f d * ((((⌊x⌋₊ / d : ℕ) : ℝ) * (((⌊x⌋₊ / d : ℕ) : ℝ) + 1)) / 2) -
      ((1 / 2 : ℝ) * (∑' n : ℕ, f n / (n : ℝ) ^ 2)) * x ^ 2| ≤ 12 * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  set N : ℕ := ⌊x⌋₊
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hN1 : 1 ≤ N := by omega
  have hN_le : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN_gt : x - 1 < (N : ℝ) := Nat.sub_one_lt_floor x
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogx : (1 / 2 : ℝ) < Real.log x := hlog2.trans_le (Real.log_le_log (by norm_num) hx)
  have hsplit :
      ∑ d ∈ Finset.Icc 1 N, f d * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2) -
        ((1 / 2 : ℝ) * (∑' n : ℕ, f n / (n : ℝ) ^ 2)) * x ^ 2 =
      (∑ d ∈ Finset.Icc 1 N, f d *
        ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2 - (x / (d : ℝ)) ^ 2 / 2)) +
      (x ^ 2 / 2) * ((∑ d ∈ Finset.Icc 1 N, f d / (d : ℝ) ^ 2) - ∑' n : ℕ, f n / (n : ℝ) ^ 2) := by
    rw [mul_sub, Finset.mul_sum]
    have h1 : ∑ d ∈ Finset.Icc 1 N, f d *
        ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2 - (x / (d : ℝ)) ^ 2 / 2) =
        (∑ d ∈ Finset.Icc 1 N, f d * ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2)) -
        (∑ d ∈ Finset.Icc 1 N, (x ^ 2 / 2) * (f d / (d : ℝ) ^ 2)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => by ring
    linarith
  rw [hsplit]
  have hterm1 : |∑ d ∈ Finset.Icc 1 N, f d *
      ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2 - (x / (d : ℝ)) ^ 2 / 2)| ≤
      (5 / 2) * x * (1 + Real.log x) := by
    calc |∑ d ∈ Finset.Icc 1 N, f d *
            ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2 - (x / (d : ℝ)) ^ 2 / 2)|
        ≤ ∑ d ∈ Finset.Icc 1 N, |f d *
            ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2 - (x / (d : ℝ)) ^ 2 / 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (5 / 2) * x * ((1 : ℝ) / (d : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd1
          rw [abs_mul]
          refine (mul_le_of_le_one_left (abs_nonneg _) (hf1 d)).trans ?_
          set q : ℝ := ((N / d : ℕ) : ℝ)
          set y : ℝ := x / (d : ℝ)
          have hq_nn : 0 ≤ q := Nat.cast_nonneg _
          have hq_le : q ≤ y := by
            dsimp only [q, y]
            rw [le_div_iff₀ hd_pos]
            have h1 : (N / d : ℕ) * d ≤ N := Nat.div_mul_le_self N d
            have h2 : ((N / d : ℕ) : ℝ) * (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
            exact h2.trans hN_le
          have hq_gt : y - 2 < q := by
            dsimp only [q, y]
            have h1 : N < (N / d + 1) * d := by
              have := Nat.lt_div_mul_add (a := N) (b := d) (by omega)
              linarith [Nat.add_mul (N / d) 1 d]
            have h2 : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h1
            have h3 : (x - 1) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 :=
              (div_lt_iff₀ hd_pos).mpr (by linarith)
            have h4 : 1 / (d : ℝ) ≤ 1 := by
              rw [div_le_one hd_pos]; exact_mod_cast hd1
            linarith [show (x - 1) / (d : ℝ) = x / (d : ℝ) - 1 / (d : ℝ) by ring]
          have hdiff_eq : q * (q + 1) / 2 - y ^ 2 / 2 = ((q - y) * (q + y) + q) / 2 := by ring
          rw [hdiff_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          have htri : |(q - y) * (q + y) + q| ≤ 5 * y := by
            have h1 : |(q - y) * (q + y)| ≤ 2 * (2 * y) := by
              rw [abs_mul, abs_of_nonpos (by linarith), abs_of_nonneg (by positivity)]
              nlinarith
            have h2 : |q| ≤ y := by rw [abs_of_nonneg hq_nn]; exact hq_le
            exact (abs_add_le _ _).trans (by linarith)
          calc |(q - y) * (q + y) + q| / 2 ≤ (5 * y) / 2 := by linarith
            _ = (5 / 2) * x * (1 / (d : ℝ)) := by dsimp only [y]; ring
      _ = (5 / 2) * x * ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / (d : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (5 / 2) * x * (1 + Real.log x) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hlogN : Real.log (N : ℝ) ≤ Real.log x :=
            Real.log_le_log (Nat.cast_pos.mpr hN1) hN_le
          linarith [harmonic_sum_le_one_add_log N hN1]
  have hterm2 : |(x ^ 2 / 2) * ((∑ d ∈ Finset.Icc 1 N, f d / (d : ℝ) ^ 2) -
      ∑' n : ℕ, f n / (n : ℝ) ^ 2)| ≤ x := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have htail := abs_partial_sum_div_sq_sub_tsum_le hf0 hf1 hN1
    have hN_half : x / 2 ≤ (N : ℝ) := by linarith
    calc (x ^ 2 / 2) * |(∑ d ∈ Finset.Icc 1 N, f d / (d : ℝ) ^ 2) - ∑' n : ℕ, f n / (n : ℝ) ^ 2|
        ≤ (x ^ 2 / 2) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ (x ^ 2 / 2) * (1 / (x / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left zero_le_one (by positivity) hN_half) (by positivity)
      _ = x := by field_simp [hx0.ne']
  have h1_le : x ≤ 2 * x * Real.log x := by nlinarith
  exact (abs_add_le _ _).trans (by nlinarith)

/-- **EXACT EULER TOTIENT AVERAGE ORDER `3 / π²` WITH `O(x log x)` ERROR (0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 2, |∑_{1 ≤ n ≤ ⌊x⌋₊} φ(n) - (3 / π²) * x²| ≤ C * x * log x`. -/
theorem sum_totient_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Nat.totient n : ℝ) - (3 / Real.pi ^ 2) * x ^ 2| ≤
        C * x * Real.log x := by
  refine ⟨12, by norm_num, fun x hx => ?_⟩
  set N : ℕ := ⌊x⌋₊
  have hsum_eq : ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        ((((N / d : ℕ) : ℝ) * (((N / d : ℕ) : ℝ) + 1)) / 2) := by
    have hint : ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℤ) =
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℤ) *
          ∑ k ∈ Finset.Icc 1 (N / d), (k : ℤ) := by
      have h1 : ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℤ) =
          ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N,
            if d ∣ n then (ArithmeticFunction.moebius d : ℤ) * ((n / d : ℕ) : ℤ) else 0 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
        rw [totient_eq_sum_moebius_div hn1, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext d
        simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hdvd, _⟩
          exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), (Nat.le_of_dvd (by omega) hdvd).trans hnN⟩, hdvd⟩
        · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨hIcc, hdvd⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hIcc).1 hdvd) hd1,
          Nat.div_le_div_right (Finset.mem_Icc.mp hIcc).2⟩
      · intro a ha b hb hab
        rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2,
            ← Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2, hab]
      · intro k hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        refine ⟨d * k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right d k⟩,
          Nat.mul_div_cancel_left k hd1⟩
        exact (Nat.mul_le_mul_left d hk2).trans (Nat.mul_div_le N d)
      · intro _ _; rfl
    have hreal : ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) =
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
          ∑ k ∈ Finset.Icc 1 (N / d), (k : ℝ) := by
      have hc := congrArg (Int.cast (R := ℝ)) hint
      simpa using hc
    rw [hreal]
    refine Finset.sum_congr rfl fun d _ => by rw [sum_Icc_nat_real]
  rw [hsum_eq]
  have hbd := abs_sum_triangular_floor_sub_le (f := fun n => (ArithmeticFunction.moebius n : ℝ))
    (by simp) abs_moebius_le_one hx
  rw [tsum_moebius_div_sq_eq_six_div_pi_sq] at hbd
  have hconst : (1 / 2 : ℝ) * (6 / Real.pi ^ 2) = 3 / Real.pi ^ 2 := by ring
  rwa [hconst] at hbd

/-- **PROBABILISTIC COPRIMALITY DENSITY (`6 / π²`, 0 ASSUMPTIONS!)**:
`#{(a, b) ∈ [1, N]² | Nat.Coprime a b} / N² → 6 / π²` as `N → ∞`. -/
theorem coprime_pairs_density :
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℝ) /
        (N : ℝ) ^ 2) atTop (𝓝 (6 / Real.pi ^ 2)) := by
  -- Exact identity for `N ≥ 1`: `#(coprime pairs in [1, N]²) = 2 * (∑_{n=1}^N φ(n)) - 1`
  have hcount : ∀ N : ℕ, 1 ≤ N →
      (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => Nat.Coprime p.1 p.2)).card : ℝ) =
        2 * (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ)) - 1 := by
    intro N hN
    set S : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => Nat.Coprime p.1 p.2)
    set S_lt : Finset (ℕ × ℕ) := S.filter (fun p => p.1 < p.2)
    set S_gt : Finset (ℕ × ℕ) := S.filter (fun p => p.2 < p.1)
    set S_eq : Finset (ℕ × ℕ) := S.filter (fun p => p.1 = p.2)
    have hdisj1 : Disjoint S_lt S_gt := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hdisj2 : Disjoint (S_lt ∪ S_gt) S_eq := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have hpeq : p.1 = p.2 := (Finset.mem_filter.mp hp2).2
      rcases Finset.mem_union.mp hp1 with hlt | hgt
      · exact (lt_irrefl p.1) (hpeq ▸ (Finset.mem_filter.mp hlt).2)
      · exact (lt_irrefl p.1) (hpeq ▸ (Finset.mem_filter.mp hgt).2)
    have hunion : (S_lt ∪ S_gt) ∪ S_eq = S := by
      ext p
      simp only [S_lt, S_gt, S_eq, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        rcases lt_trichotomy p.1 p.2 with h1 | h2 | h3
        · exact Or.inl (Or.inl ⟨h, h1⟩)
        · exact Or.inr ⟨h, h2⟩
        · exact Or.inl (Or.inr ⟨h, h3⟩)
    have hcard_eq : S_eq.card = 1 := by
      have hsing : S_eq = {(1, 1)} := by
        ext ⟨a, b⟩
        simp only [S_eq, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨_, _⟩⟩, hcop⟩, hab⟩
          subst hab
          have : a = 1 := by rw [Nat.Coprime, Nat.gcd_self] at hcop; exact hcop
          exact ⟨this, this⟩
        · rintro ⟨rfl, rfl⟩
          exact ⟨⟨⟨⟨le_rfl, hN⟩, ⟨le_rfl, hN⟩⟩, Nat.coprime_one_left 1⟩, rfl⟩
      rw [hsing, Finset.card_singleton]
    have hcard_symm : S_gt.card = S_lt.card := by
      refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
      · intro ⟨a, b⟩ hp
        simp only [S_gt, S_lt, S, Finset.mem_filter, Finset.mem_product, Prod.swap_prod_mk] at hp ⊢
        exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, hp.2⟩
      · intro _ _ _ _ h; exact Prod.swap_injective h
      · intro ⟨a, b⟩ hp
        refine ⟨(b, a), ?_, rfl⟩
        simp only [S_gt, S_lt, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
        exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.symm⟩, hp.2⟩
    have hcard_lt : S_lt.card = ∑ b ∈ Finset.Icc 2 N, Nat.totient b := by
      have hbi : S_lt = (Finset.Icc 2 N).biUnion (fun b =>
          ((Finset.Icc 1 (b - 1)).filter (fun a => Nat.Coprime a b)).image (fun a => (a, b))) := by
        ext ⟨a, b⟩
        simp only [S_lt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨_, hbN⟩⟩, hcop⟩, hab⟩
          exact ⟨b, ⟨by omega, hbN⟩, a, ⟨⟨ha1, by omega⟩, hcop⟩, rfl, rfl⟩
        · rintro ⟨b', ⟨hb2, hbN⟩, a', ⟨⟨ha1, hab⟩, hcop⟩, rfl, rfl⟩
          exact ⟨⟨⟨⟨ha1, by omega⟩, ⟨by omega, hbN⟩⟩, hcop⟩, by omega⟩
      rw [hbi, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun b hb => ?_
        have hb2 : 2 ≤ b := (Finset.mem_Icc.mp hb).1
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Nat.totient]
        congr 1
        ext a
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
        constructor
        · rintro ⟨⟨_, hab⟩, hcop⟩; exact ⟨by omega, hcop.symm⟩
        · rintro ⟨hab, hcop⟩
          have ha0 : a ≠ 0 := by
            rintro rfl
            rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
            omega
          exact ⟨⟨by omega, by omega⟩, hcop.symm⟩
      · intro b₁ _ b₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rcases Finset.mem_image.mp hp1 with ⟨a₁, _, rfl⟩
        rcases Finset.mem_image.mp hp2 with ⟨a₂, _, hEq⟩
        exact hne (Prod.mk.inj hEq).2.symm
    have hsum_split : ∑ n ∈ Finset.Icc 1 N, Nat.totient n = 1 + ∑ b ∈ Finset.Icc 2 N, Nat.totient b := by
      have hset : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hset, Finset.sum_insert (by simp : (1 : ℕ) ∉ Finset.Icc 2 N), Nat.totient_one]
    have hcard_tot : S.card + 1 = 2 * ∑ n ∈ Finset.Icc 1 N, Nat.totient n := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
        hcard_symm, hcard_eq, hcard_lt, hsum_split]
      ring
    have hreal : (S.card : ℝ) + 1 = 2 * ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) := by
      exact_mod_cast hcard_tot
    linarith
  obtain ⟨C, hC, htot⟩ := sum_totient_asymp
  rw [← tendsto_sub_nhds_zero_iff]
  have hlim : Tendsto (fun N : ℕ => (2 * C * Real.log (N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
      have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
      exact (h.comp tendsto_natCast_atTop_atTop).congr fun N => by
        simp only [Function.comp_apply, Real.rpow_one]
    have h2 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).congr fun N => by
        simp only [Function.comp_apply, one_div]
    have hcomb := (h1.const_mul (2 * C)).add h2
    rw [mul_zero, add_zero] at hcomb
    exact hcomb.congr fun N => by ring
  refine squeeze_zero_norm' (a := fun N : ℕ => (2 * C * Real.log (N : ℝ) + 1) / (N : ℝ)) ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN1 : 1 ≤ N := by omega
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [Real.norm_eq_abs, hcount N hN1]
  have hrew : (2 * ∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) - 1) / (N : ℝ) ^ 2 - 6 / Real.pi ^ 2 =
      (2 * (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) - (3 / Real.pi ^ 2) * (N : ℝ) ^ 2) - 1) /
        (N : ℝ) ^ 2 := by
    field_simp [hN0.ne', Real.pi_ne_zero]; ring
  rw [hrew, abs_div, abs_of_pos (sq_pos_of_pos hN0)]
  have htotN := htot (N : ℝ) hN2
  rw [Nat.floor_natCast] at htotN
  have hnum : |2 * (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) - (3 / Real.pi ^ 2) * (N : ℝ) ^ 2) - 1| ≤
      2 * C * (N : ℝ) * Real.log (N : ℝ) + 1 := by
    have htri := abs_sub (2 * (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) - (3 / Real.pi ^ 2) * (N : ℝ) ^ 2)) 1
    rw [abs_mul (2 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_one] at htri
    linarith
  calc |2 * (∑ n ∈ Finset.Icc 1 N, (Nat.totient n : ℝ) - (3 / Real.pi ^ 2) * (N : ℝ) ^ 2) - 1| / (N : ℝ) ^ 2
      ≤ (2 * C * (N : ℝ) * Real.log (N : ℝ) + 1) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ (2 * C * (N : ℝ) * Real.log (N : ℝ) + (N : ℝ)) / (N : ℝ) ^ 2 := by
        refine div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = (2 * C * Real.log (N : ℝ) + 1) / (N : ℝ) := by field_simp [hN0.ne']

/-- **EXACT SUM-OF-DIVISORS AVERAGE ORDER `π² / 12` WITH `O(x log x)` ERROR (0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 2, |∑_{1 ≤ n ≤ ⌊x⌋₊} σ₁(n) - (π² / 12) * x²| ≤ C * x * log x`. -/
theorem sum_sigma_one_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.sigma 1 n : ℝ) - (Real.pi ^ 2 / 12) * x ^ 2| ≤
        C * x * Real.log x := by
  refine ⟨12, by norm_num, fun x hx => ?_⟩
  set N : ℕ := ⌊x⌋₊
  have hsum_eq : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.sigma 1 n : ℝ) =
      ∑ k ∈ Finset.Icc 1 N, (if k = 0 then (0 : ℝ) else 1) *
        ((((N / k : ℕ) : ℝ) * (((N / k : ℕ) : ℝ) + 1)) / 2) := by
    have hnat : ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 1 n =
        ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / k), d := by
      have h1 : ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 1 n =
          ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, if k ∣ n then n / k else 0 := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
        rw [ArithmeticFunction.sigma_apply, ← Finset.sum_filter]
        have hflt : (Finset.Icc 1 N).filter (· ∣ n) = n.divisors := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨_, hk⟩; exact ⟨hk, by omega⟩
          · rintro ⟨hk, _⟩
            exact ⟨⟨Nat.pos_of_dvd_of_pos hk (by omega), (Nat.le_of_dvd (by omega) hk).trans hnN⟩, hk⟩
        rw [hflt]
        have hbij : ∑ d ∈ n.divisors, d ^ 1 = ∑ k ∈ n.divisors, n / k := by
          refine Finset.sum_bij (fun d _ => n / d) ?_ ?_ ?_ ?_
          · intro d hd; exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), by omega⟩
          · intro a ha b hb hab
            have ha' : a ∣ n := Nat.dvd_of_mem_divisors ha
            have hb' : b ∣ n := Nat.dvd_of_mem_divisors hb
            have h1 := Nat.div_mul_cancel ha'
            have h2 := Nat.div_mul_cancel hb'
            rw [hab] at h1
            have hpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd (by omega) hb') (Nat.pos_of_mem_divisors hb)
            exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
          · intro k hk
            refine ⟨n / k, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hk), by omega⟩,
              Nat.div_div_self (Nat.dvd_of_mem_divisors hk) (by omega)⟩
          · intro d hd
            simp [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (by omega)]
        exact hbij
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨hIcc, hdvd⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hIcc).1 hdvd) hk1,
          Nat.div_le_div_right (Finset.mem_Icc.mp hIcc).2⟩
      · intro a ha b hb hab
        rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2,
            ← Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2, hab]
      · intro d hd
        obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
        refine ⟨k * d, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right k d⟩,
          Nat.mul_div_cancel_left d hk1⟩
        exact (Nat.mul_le_mul_left k hd2).trans (Nat.mul_div_le N k)
      · intro _ _; rfl
    have hreal : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.sigma 1 n : ℝ) =
        ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / k), (d : ℝ) := by
      have hc := congrArg (Nat.cast (R := ℝ)) hnat
      simpa using hc
    rw [hreal]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    simp [hk0, sum_Icc_nat_real]
  rw [hsum_eq]
  have hbd := abs_sum_triangular_floor_sub_le (f := fun n : ℕ => if n = 0 then (0 : ℝ) else 1)
    (by simp) (fun n => by split_ifs <;> norm_num) hx
  have htsum_eq : (∑' n : ℕ, (if n = 0 then (0 : ℝ) else 1) / (n : ℝ) ^ 2) = Real.pi ^ 2 / 6 := by
    rw [← tsum_inv_sq_eq_pi_sq_div_six]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · simp [hn0, one_div]
  rw [htsum_eq] at hbd
  have hconst : (1 / 2 : ℝ) * (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 12 := by ring
  rwa [hconst] at hbd

/-- **Exact Integer Dirichlet Hyperbola Identity** for `d(n) = σ₀(n)`:
for every `N ≥ 1` and `M = Nat.sqrt N`,
`∑_{n=1}^N σ₀(n) + M² = 2 * ∑_{a=1}^M (N / a)`. -/
theorem dirichlet_hyperbola_sigma_zero {N : ℕ} (_hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 0 n) + (Nat.sqrt N) ^ 2 =
      2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (N / a) := by
  set M : ℕ := Nat.sqrt N
  have hM_sq_le : M ^ 2 ≤ N := by rw [sq]; exact Nat.sqrt_le N
  have hN_lt : N < (M + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt N
  have hM_le_N : M ≤ N := Nat.sqrt_le_self N
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N)
  set A : Finset (ℕ × ℕ) := S.filter (fun p => p.1 ≤ M)
  set B : Finset (ℕ × ℕ) := S.filter (fun p => p.2 ≤ M)
  -- 1. `S.card = ∑_{n=1}^N σ₀(n)`
  have hS_card : S.card = ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.sigma 0 n := by
    have hbi : S = (Finset.Icc 1 N).biUnion (fun n => n.divisors.image (fun d => (d, n / d))) := by
      ext ⟨a, b⟩
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_biUnion, Finset.mem_image, Nat.mem_divisors, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, hab⟩
        exact ⟨a * b, ⟨by nlinarith, hab⟩, a, ⟨dvd_mul_right a b, by nlinarith⟩, rfl,
          Nat.mul_div_cancel_left b (by omega)⟩
      · rintro ⟨n, ⟨hn1, hnN⟩, d, ⟨hdvd, _⟩, rfl, rfl⟩
        have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have hq1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd1
        have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
        exact ⟨⟨⟨hd1, (Nat.le_of_dvd (by omega) hdvd).trans hnN⟩,
          ⟨hq1, (Nat.div_le_self n d).trans hnN⟩⟩, by omega⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), ArithmeticFunction.sigma_apply]
      simp
    · intro n₁ _ n₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro ⟨a, b⟩ hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨d₁, hd₁, h1⟩
      rcases Finset.mem_image.mp hp2 with ⟨d₂, hd₂, h2⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
      obtain ⟨hd_eq, hq_eq⟩ := Prod.mk.inj h2
      have hmul1 : d₁ * (n₁ / d₁) = n₁ := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₁)
      have hmul2 : d₂ * (n₂ / d₂) = n₂ := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₂)
      rw [hq_eq, hd_eq] at hmul2
      exact hne (hmul1.symm.trans hmul2)
  -- 2. `A ∪ B = S` and `A ∩ B = Icc 1 M ×ˢ Icc 1 M`
  have hAB_union : A ∪ B = S := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      have hmul : p.1 * p.2 ≤ N := (Finset.mem_filter.mp h).2
      by_cases h1 : p.1 ≤ M
      · exact Or.inl ⟨h, h1⟩
      · right; refine ⟨h, ?_⟩
        by_contra h2
        have : (M + 1) ^ 2 ≤ p.1 * p.2 := by rw [sq]; nlinarith
        omega
  have hAB_inter : A ∩ B = Finset.Icc 1 M ×ˢ Finset.Icc 1 M := by
    ext ⟨a, b⟩
    simp only [A, B, S, Finset.mem_inter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, _⟩, haM⟩, ⟨_, hbM⟩⟩
      exact ⟨⟨ha1, haM⟩, ⟨hb1, hbM⟩⟩
    · rintro ⟨⟨ha1, haM⟩, ⟨hb1, hbM⟩⟩
      have hab : a * b ≤ N := (Nat.mul_le_mul haM hbM).trans (by simpa [sq] using hM_sq_le)
      exact ⟨⟨⟨⟨⟨ha1, haM.trans hM_le_N⟩, ⟨hb1, hbM.trans hM_le_N⟩⟩, hab⟩, haM⟩,
        ⟨⟨⟨⟨ha1, haM.trans hM_le_N⟩, ⟨hb1, hbM.trans hM_le_N⟩⟩, hab⟩, hbM⟩⟩
  -- 3. `A.card = ∑_{a=1}^M (N / a)` and `B.card = A.card`
  have hA_card : A.card = ∑ a ∈ Finset.Icc 1 M, (N / a) := by
    have hbi : A = (Finset.Icc 1 M).biUnion (fun a => (Finset.Icc 1 (N / a)).image (fun b => (a, b))) := by
      ext ⟨a, b⟩
      simp only [A, S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, hab⟩, haM⟩
        exact ⟨a, ⟨ha1, haM⟩, b, ⟨hb1, (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)⟩, rfl, rfl⟩
      · rintro ⟨a', ⟨ha1, haM⟩, b', ⟨hb1, hbq⟩, rfl, rfl⟩
        have hab : a' * b' ≤ N := (Nat.mul_le_mul_left a' hbq).trans (Nat.mul_div_le N a')
        have hbN : b' ≤ N := hbq.trans (Nat.div_le_self N a')
        exact ⟨⟨⟨⟨ha1, haM.trans hM_le_N⟩, ⟨hb1, hbN⟩⟩, hab⟩, haM⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun a _ => by
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Nat.card_Icc]; simp
    · intro a₁ _ a₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨b₁, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨b₂, _, hEq⟩
      exact hne (Prod.mk.inj hEq).1.symm
  have hB_card : B.card = A.card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro ⟨a, b⟩ hp
      simp only [A, B, S, Finset.mem_filter, Finset.mem_product, Prod.swap_prod_mk] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by rw [mul_comm]; exact hp.1.2⟩, hp.2⟩
    · intro _ _ _ _ h; exact Prod.swap_injective h
    · intro ⟨a, b⟩ hp
      refine ⟨(b, a), ?_, rfl⟩
      simp only [A, B, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by rw [mul_comm]; exact hp.1.2⟩, hp.2⟩
  have hIE := Finset.card_union_add_card_inter A B
  rw [hAB_union, hAB_inter, hS_card, hA_card, hB_card, Finset.card_product, Nat.card_Icc] at hIE
  have hsqM : (M + 1 - 1) * (M + 1 - 1) = M ^ 2 := by simp [sq]
  rw [hsqM] at hIE
  omega

/-- Sharp `O(1 / M)` Harmonic-Number Euler–Mascheroni approximation directly from Mathlib's
`Real.eulerMascheroniSeq` and `Real.eulerMascheroniSeq'`. -/
private lemma harmonic_Icc_sub_log_sub_gamma_bounds {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) - Real.log (M : ℝ) - Real.eulerMascheroniConstant ∧
    (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) - Real.log (M : ℝ) - Real.eulerMascheroniConstant ≤
      1 / (M : ℝ) := by
  have hM0 : M ≠ 0 := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hharm_eq : (harmonic M : ℝ) = ∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ) := by
    clear hM hM0 hMR
    induction M with
    | zero => simp
    | succ k ih =>
      have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [harmonic_succ, Rat.cast_add, ih, hIcc, Finset.sum_insert (by simp : k + 1 ∉ Finset.Icc 1 k),
        add_comm]
      push_cast; simp [one_div]
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant M
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' M
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq', hM0, ↓reduceIte] at hlo hhi
  rw [hharm_eq] at hlo hhi
  constructor
  · linarith
  · have hlog_step : Real.log ((M : ℝ) + 1) - Real.log (M : ℝ) ≤ 1 / (M : ℝ) := by
      rw [← Real.log_div (by linarith) hMR.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < (M : ℝ) + 1) hMR)
      have h2 : ((M : ℝ) + 1) / (M : ℝ) - 1 = 1 / (M : ℝ) := by field_simp [hMR.ne']; ring
      linarith
    linarith

/-- **DIRICHLET HYPERBOLA THEOREM FOR `d(n) = σ₀(n)` WITH `O(√x)` ERROR (0 ASSUMPTIONS!)**:
`∃ C > 0, ∀ x ≥ 1, |∑_{1 ≤ n ≤ ⌊x⌋₊} σ₀(n) - x * (log x + 2 γ - 1)| ≤ C * √x`. -/
theorem sum_sigma_zero_asymp :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.sigma 0 n : ℝ) -
        x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1)| ≤ C * Real.sqrt x := by
  refine ⟨20, by norm_num, fun x hx => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  set N : ℕ := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  set M : ℕ := Nat.sqrt N
  have hM_eq_fl : M = ⌊Real.sqrt x⌋₊ := by
    have hsq_nn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    symm
    rw [Nat.floor_eq_iff hsq_nn]
    constructor
    · have h1 : (M : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast (by rw [sq]; exact Nat.sqrt_le N)
      have h2 : (M : ℝ) ^ 2 ≤ x := h1.trans (Nat.floor_le hx0.le)
      exact Real.le_sqrt_of_sq_le h2
    · have h1 : N < (M + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt N
      have h2 : N + 1 ≤ (M + 1) ^ 2 := h1
      have h3 : (N : ℝ) + 1 ≤ ((M : ℝ) + 1) ^ 2 := by exact_mod_cast h2
      have h4 : x < ((M : ℝ) + 1) ^ 2 := lt_of_lt_of_le (Nat.lt_floor_add_one x) h3
      exact (Real.sqrt_lt' (by positivity)).mpr h4
  have hsq1 : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx
  have hM1 : 1 ≤ M := by rw [hM_eq_fl]; exact Nat.le_floor (by exact_mod_cast hsq1)
  have hM_le : (M : ℝ) ≤ Real.sqrt x := by rw [hM_eq_fl]; exact Nat.floor_le (Real.sqrt_nonneg x)
  have hM_gt : Real.sqrt x < (M : ℝ) + 1 := by rw [hM_eq_fl]; exact Nat.lt_floor_add_one (Real.sqrt x)
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM1
  have hM_half : Real.sqrt x / 2 ≤ (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hhyp : ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.sigma 0 n : ℝ) =
      2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) - (M : ℝ) ^ 2 := by
    have h1 := dirichlet_hyperbola_sigma_zero hN1
    have h2 : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.sigma 0 n : ℝ)) + (M : ℝ) ^ 2 =
        2 * ∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  rw [hhyp]
  -- Decompose into 4 explicit `O(√x)` error terms:
  -- (A) `|2 ∑_{a=1}^M (N/a - x/a)| ≤ 4 √x`
  have hA : |2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) -
      2 * x * (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ))| ≤ 4 * Real.sqrt x := by
    have hrew : 2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) -
        2 * x * (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) =
        2 * ∑ a ∈ Finset.Icc 1 M, (((N / a : ℕ) : ℝ) - x / (a : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => by ring
    rw [hrew, abs_mul, abs_of_pos two_pos]
    have hsum_bd : |∑ a ∈ Finset.Icc 1 M, (((N / a : ℕ) : ℝ) - x / (a : ℝ))| ≤ 2 * (M : ℝ) := by
      calc |∑ a ∈ Finset.Icc 1 M, (((N / a : ℕ) : ℝ) - x / (a : ℝ))|
          ≤ ∑ a ∈ Finset.Icc 1 M, |((N / a : ℕ) : ℝ) - x / (a : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ Finset.Icc 1 M, (2 : ℝ) := by
            refine Finset.sum_le_sum fun a ha => ?_
            have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
            have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha1
            have hq_le : ((N / a : ℕ) : ℝ) ≤ x / (a : ℝ) := by
              rw [le_div_iff₀ ha_pos]
              have h1 : (N / a : ℕ) * a ≤ N := Nat.div_mul_le_self N a
              have h2 : ((N / a : ℕ) : ℝ) * (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
              exact h2.trans (Nat.floor_le hx0.le)
            have hq_gt : x / (a : ℝ) - 2 < ((N / a : ℕ) : ℝ) := by
              have h1 : N < (N / a + 1) * a := by
                have := Nat.lt_div_mul_add (a := N) (b := a) (by omega)
                linarith [Nat.add_mul (N / a) 1 a]
              have h2 : (N : ℝ) < (((N / a : ℕ) : ℝ) + 1) * (a : ℝ) := by exact_mod_cast h1
              have h3 : (x - 1) / (a : ℝ) < ((N / a : ℕ) : ℝ) + 1 :=
                (div_lt_iff₀ ha_pos).mpr (by linarith [Nat.sub_one_lt_floor x])
              have h4 : 1 / (a : ℝ) ≤ 1 := by rw [div_le_one ha_pos]; exact_mod_cast ha1
              linarith [show (x - 1) / (a : ℝ) = x / (a : ℝ) - 1 / (a : ℝ) by ring]
            rw [abs_le]; constructor <;> linarith
        _ = 2 * (M : ℝ) := by simp [mul_comm]
    linarith
  -- (B) `|2 x (H_M - log M - γ)| ≤ 2 x / M ≤ 4 √x`
  have hB : |2 * x * ((∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) -
      (Real.log (M : ℝ) + Real.eulerMascheroniConstant))| ≤ 4 * Real.sqrt x := by
    have hhm := harmonic_Icc_sub_log_sub_gamma_bounds hM1
    rw [abs_mul, abs_of_pos (by positivity), abs_of_nonneg (by linarith)]
    have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    calc 2 * x * ((∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) - (Real.log (M : ℝ) + Real.eulerMascheroniConstant))
        ≤ 2 * x * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 2 * x * (1 / (Real.sqrt x / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left zero_le_one (by positivity) hM_half) (by positivity)
      _ = 4 * Real.sqrt x := by field_simp [hsq_pos.ne']; linarith [Real.sq_sqrt hx0.le]
  -- (C) `|2 x (log M - (1/2) log x)| ≤ 4 √x`
  have hC : |2 * x * (Real.log (M : ℝ) - (1 / 2) * Real.log x)| ≤ 4 * Real.sqrt x := by
    have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hlog_sq : (1 / 2) * Real.log x = Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hx0.le]; ring
    rw [hlog_sq, abs_mul, abs_of_pos (by positivity)]
    have hlog_le : Real.log (M : ℝ) ≤ Real.log (Real.sqrt x) := Real.log_le_log hM_pos hM_le
    rw [abs_of_nonpos (by linarith), neg_sub, ← Real.log_div hsq_pos.ne' hM_pos.ne']
    have hlog_ub : Real.log (Real.sqrt x / (M : ℝ)) ≤ 1 / (M : ℝ) := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hsq_pos hM_pos)
      have h2 : Real.sqrt x / (M : ℝ) - 1 ≤ 1 / (M : ℝ) := by
        rw [show Real.sqrt x / (M : ℝ) - 1 = (Real.sqrt x - (M : ℝ)) / (M : ℝ) by
          field_simp [hM_pos.ne']]
        exact div_le_div_of_nonneg_right (by linarith) hM_pos.le
      exact h1.trans h2
    calc 2 * x * Real.log (Real.sqrt x / (M : ℝ))
        ≤ 2 * x * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left hlog_ub (by positivity)
      _ ≤ 2 * x * (1 / (Real.sqrt x / 2)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left zero_le_one (by positivity) hM_half) (by positivity)
      _ = 4 * Real.sqrt x := by field_simp [hsq_pos.ne']; linarith [Real.sq_sqrt hx0.le]
  -- (D) `|M² - x| ≤ 3 √x`
  have hD : |(M : ℝ) ^ 2 - x| ≤ 3 * Real.sqrt x := by
    have hsq_eq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
    have hM2_le : (M : ℝ) ^ 2 ≤ x := by
      rw [← hsq_eq]; exact pow_le_pow_left₀ hM_pos.le hM_le 2
    rw [abs_of_nonpos (by linarith), neg_sub]
    have hfac : x - (M : ℝ) ^ 2 = (Real.sqrt x - (M : ℝ)) * (Real.sqrt x + (M : ℝ)) := by
      linear_combination -hsq_eq
    rw [hfac]
    have h1 : Real.sqrt x - (M : ℝ) ≤ 1 := by linarith
    have h2 : Real.sqrt x + (M : ℝ) ≤ 2 * Real.sqrt x := by linarith
    nlinarith [Real.sqrt_nonneg x]
  -- Combine (A) + (B) + (C) + (D) ≤ 15 √x ≤ 20 √x!
  have hcomb :
      2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) - (M : ℝ) ^ 2 -
        x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1) =
      (2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) -
        2 * x * (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ))) +
      (2 * x * ((∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) -
        (Real.log (M : ℝ) + Real.eulerMascheroniConstant))) +
      (2 * x * (Real.log (M : ℝ) - (1 / 2) * Real.log x)) -
      ((M : ℝ) ^ 2 - x) := by ring
  rw [hcomb]
  have ht1 := abs_sub
    ((2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) -
        2 * x * (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ))) +
      (2 * x * ((∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) -
        (Real.log (M : ℝ) + Real.eulerMascheroniConstant))) +
      (2 * x * (Real.log (M : ℝ) - (1 / 2) * Real.log x)))
    ((M : ℝ) ^ 2 - x)
  have ht2 := abs_add_le
    ((2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) -
        2 * x * (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ))) +
      (2 * x * ((∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) -
        (Real.log (M : ℝ) + Real.eulerMascheroniConstant))))
    (2 * x * (Real.log (M : ℝ) - (1 / 2) * Real.log x))
  have ht3 := abs_add_le
    (2 * (∑ a ∈ Finset.Icc 1 M, ((N / a : ℕ) : ℝ)) -
      2 * x * (∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)))
    (2 * x * ((∑ a ∈ Finset.Icc 1 M, (1 : ℝ) / (a : ℝ)) -
      (Real.log (M : ℝ) + Real.eulerMascheroniConstant)))
  linarith [Real.sqrt_nonneg x]

end RHDirect.Stage9MobiusAverages
