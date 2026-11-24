import RHDirect.Stage5ThetaModular
import RHDirect.Stage5ModularHecke
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# RHDirect.Stage7EisensteinSeries

Concrete Holomorphic Eisenstein Series `E₄(τ)`, `E₆(τ)`, `E₈(τ)` (`SL₂(ℤ)` Weight 4, 6, 8 Modular
Forms), Exact `q`-Expansions via Lipschitz's Formula, Low-Weight Level-1 Cusp-Form Vanishing
(`S_k(SL₂(ℤ)) = 0` for `k < 12`, `dim M_4 = dim M_6 = dim M_8 = 1`), the **UNCONDITIONAL CONCRETE
SIEGEL–WEIL IDENTITY FOR `E₈` (`Θ_{E₈}(τ) = E₄(τ) = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`)**, Exact `E₈`
Shell Representation Counts `r_{E₈}(2n) = 240 σ₃(n)` (including the 8D kissing number `240`), and
the Exact Epstein–Eisenstein Zeta Factorization `Z_{E₈}(s) = 240 · 2^{-s/2} · ζ(s/2) · ζ(s/2 - 3)`
plus its Degree-2 `GL₂` Euler Product in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero assumptions.
-/

open Complex Real Filter Module Submodule Finset
open RHDirect.ArakelovCovolume RHDirect.Stage3ThetaSiegelBridge
open RHDirect.Stage5ThetaModular RHDirect.Stage5ModularHecke
open scoped BigOperators UpperHalfPlane ModularForm Topology Manifold

namespace RHDirect.Stage7EisensteinSeries

noncomputable section

/-- Level-1 modular group `SL₂(ℤ)` embedded in `GL₂(ℝ)`. -/
abbrev SL2ZRange : Subgroup (GL (Fin 2) ℝ) :=
  (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ).range

/-! ## Section 1: Exact Bernoulli Values, Lipschitz's Formula & Holomorphic Eisenstein Series `E₄`, `E₆`, `E₈` -/

section HolomorphicEisenstein

/-- Exact Bernoulli number `B₄ = -1 / 30`. -/
theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]

/-- Exact Bernoulli number `B₅ = 0`. -/
theorem bernoulli_five : bernoulli 5 = 0 :=
  bernoulli_eq_zero_of_odd (by decide) (by decide)

/-- Exact Bernoulli number `B₆ = 1 / 42`. -/
theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by decide : 1 < 5)]
  norm_num

/-- Exact Bernoulli number `B₇ = 0`. -/
theorem bernoulli_seven : bernoulli 7 = 0 :=
  bernoulli_eq_zero_of_odd (by decide) (by decide)

/-- Exact Bernoulli number `B₈ = -1 / 30`. -/
theorem bernoulli_eight : bernoulli 8 = -1 / 30 := by
  have hb6 : bernoulli' 6 = 1 / 42 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli_six]
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    bernoulli'_zero, bernoulli'_one, bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (by decide : Odd 5) (by decide : 1 < 5), hb6,
    bernoulli'_eq_zero_of_odd (by decide : Odd 7) (by decide : 1 < 7)]
  norm_num

/-- **Lipschitz's Formula** on the upper half-plane (directly from Mathlib's
`EisensteinSeries.qExpansion_identity_pnat`): for every `k ≥ 1` and `τ : UpperHalfPlane`,
$$\sum_{n \in \mathbb{Z}} \frac{1}{(\tau + n)^{k+1}} =
  \frac{(-2\pi i)^{k+1}}{k!} \sum_{n \ge 1} n^k e^{2\pi i n \tau}.$$ -/
theorem lipschitz_formula {k : ℕ} (hk : 1 ≤ k) (τ : UpperHalfPlane) :
    (∑' n : ℤ, 1 / ((τ : ℂ) + (n : ℂ)) ^ (k + 1)) =
      (-2 * (Real.pi : ℂ) * Complex.I) ^ (k + 1) / (k.factorial : ℂ) *
        ∑' n : ℕ+, ((n : ℕ) : ℂ) ^ k *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
  rw [EisensteinSeries.qExpansion_identity_pnat hk τ]
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Normalized Weight-4 Holomorphic Eisenstein Series** on `UpperHalfPlane`:
$$E_4(\tau) = 1 + 240 \sum_{n \ge 1} \sigma_3(n) e^{2\pi i n \tau}.$$ -/
def E4 (τ : UpperHalfPlane) : ℂ :=
  1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 (n : ℕ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ))

/-- **Normalized Weight-6 Holomorphic Eisenstein Series** on `UpperHalfPlane`:
$$E_6(\tau) = 1 - 504 \sum_{n \ge 1} \sigma_5(n) e^{2\pi i n \tau}.$$ -/
def E6 (τ : UpperHalfPlane) : ℂ :=
  1 - 504 * ∑' n : ℕ+, (ArithmeticFunction.sigma 5 (n : ℕ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ))

/-- **Normalized Weight-8 Holomorphic Eisenstein Series** on `UpperHalfPlane`:
$$E_8(\tau) = 1 + 480 \sum_{n \ge 1} \sigma_7(n) e^{2\pi i n \tau}.$$ -/
def E8Eisenstein (τ : UpperHalfPlane) : ℂ :=
  1 + 480 * ∑' n : ℕ+, (ArithmeticFunction.sigma 7 (n : ℕ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ))

private lemma cexp_two_pi_I_zpow_pnat (n : ℕ+) (τ : UpperHalfPlane) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
  rw [zpow_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Exact identification of `E4` with Mathlib's `ModularForm.E₄`. -/
theorem E4_eq_modularForm_E4 (τ : UpperHalfPlane) : E4 τ = ModularForm.E₄ τ := by
  have hq := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) τ
  change ModularForm.E₄ τ = _ at hq
  rw [hq, bernoulli_four]
  unfold E4
  have htsum :
      (∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ)) =
      ∑' n : ℕ+, (ArithmeticFunction.sigma 3 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
    refine tsum_congr fun n => ?_
    rw [show (4 - 1 : ℕ) = 3 by rfl, cexp_two_pi_I_zpow_pnat]
  have hstep :
      1 - 2 * ((4 : ℕ) : ℂ) / ((-1 / 30 : ℚ) : ℂ) *
        ∑' n : ℕ+, (ArithmeticFunction.sigma (4 - 1) (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ) =
      1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
    rw [htsum]
    push_cast
    ring
  rw [← hstep]

/-- Exact identification of `E6` with Mathlib's `ModularForm.E₆`. -/
theorem E6_eq_modularForm_E6 (τ : UpperHalfPlane) : E6 τ = ModularForm.E₆ τ := by
  have hq := EisensteinSeries.q_expansion_bernoulli (k := 6) (by norm_num) (by decide) τ
  change ModularForm.E₆ τ = _ at hq
  rw [hq, bernoulli_six]
  unfold E6
  have hstep :
      1 - 2 * ((6 : ℕ) : ℂ) / ((1 / 42 : ℚ) : ℂ) *
        ∑' n : ℕ+, (ArithmeticFunction.sigma (6 - 1) (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ) =
      1 - 504 * ∑' n : ℕ+, (ArithmeticFunction.sigma 5 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
    have htsum :
        (∑' n : ℕ+, (ArithmeticFunction.sigma (6 - 1) (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ)) =
        ∑' n : ℕ+, (ArithmeticFunction.sigma 5 (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) :=
      tsum_congr fun n => by rw [show (6 - 1 : ℕ) = 5 by rfl, cexp_two_pi_I_zpow_pnat]
    rw [htsum]
    push_cast
    ring
  rw [← hstep]

/-- Exact identification of `E8Eisenstein` with Mathlib's weight-8 Eisenstein series `ModularForm.E`. -/
theorem E8Eisenstein_eq_modularForm_E8 (τ : UpperHalfPlane) :
    E8Eisenstein τ = ModularForm.E (k := 8) (by norm_num) τ := by
  have hq := EisensteinSeries.q_expansion_bernoulli (k := 8) (by norm_num) (by decide) τ
  rw [hq, bernoulli_eight]
  unfold E8Eisenstein
  have hstep :
      1 - 2 * ((8 : ℕ) : ℂ) / ((-1 / 30 : ℚ) : ℂ) *
        ∑' n : ℕ+, (ArithmeticFunction.sigma (8 - 1) (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ) =
      1 + 480 * ∑' n : ℕ+, (ArithmeticFunction.sigma 7 (n : ℕ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) := by
    have htsum :
        (∑' n : ℕ+, (ArithmeticFunction.sigma (8 - 1) (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) ^ ((n : ℕ) : ℤ)) =
        ∑' n : ℕ+, (ArithmeticFunction.sigma 7 (n : ℕ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ)) :=
      tsum_congr fun n => by rw [show (8 - 1 : ℕ) = 7 by rfl, cexp_two_pi_I_zpow_pnat]
    rw [htsum]
    push_cast
    ring
  rw [← hstep]

lemma E4_eq_coe : E4 = (ModularForm.E₄ : UpperHalfPlane → ℂ) :=
  funext E4_eq_modularForm_E4

lemma E6_eq_coe : E6 = (ModularForm.E₆ : UpperHalfPlane → ℂ) :=
  funext E6_eq_modularForm_E6

lemma E8Eisenstein_eq_coe :
    E8Eisenstein = (ModularForm.E (k := 8) (by norm_num) : UpperHalfPlane → ℂ) :=
  funext E8Eisenstein_eq_modularForm_E8

/-- Compatibility between `Stage5ThetaModular.sl2ZToGL2R` and Mathlib's `Matrix.SpecialLinearGroup.mapGL ℝ`. -/
lemma sl2ZToGL2R_eq_mapGL (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    sl2ZToGL2R γ = Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ := rfl

/-- Holomorphicity (`MDiff`) of `E4` on `UpperHalfPlane`. -/
theorem mdifferentiable_E4 : MDiff E4 := by
  rw [E4_eq_coe]
  exact ModularForm.E₄.holo'

/-- Complex differentiability of `E4 ∘ ofComplex` on `{z : ℂ | 0 < z.im}`. -/
theorem differentiableOn_E4 :
    DifferentiableOn ℂ (E4 ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_E4

/-- Holomorphicity (`MDiff`) of `E6` on `UpperHalfPlane`. -/
theorem mdifferentiable_E6 : MDiff E6 := by
  rw [E6_eq_coe]
  exact ModularForm.E₆.holo'

/-- Complex differentiability of `E6 ∘ ofComplex` on `{z : ℂ | 0 < z.im}`. -/
theorem differentiableOn_E6 :
    DifferentiableOn ℂ (E6 ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) {z : ℂ | 0 < z.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_E6

/-- Exact `q`-expansion coefficients of `E4`:
`coeff 0 = 1`, and `coeff m = 240 * σ₃(m)` for `m ≥ 1`. -/
theorem E4_qExpansion_coeff (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 E4) =
      if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℂ) := by
  rw [E4_eq_coe]
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by decide) m
  change PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 ModularForm.E₄) = _ at h
  rw [h, bernoulli_four]
  split_ifs with hm
  · rfl
  · push_cast; ring

/-- Exact `q`-expansion coefficients of `E6`:
`coeff 0 = 1`, and `coeff m = -504 * σ₅(m)` for `m ≥ 1`. -/
theorem E6_qExpansion_coeff (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 E6) =
      if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℂ) := by
  rw [E6_eq_coe]
  have h := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) (by decide) m
  change PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 ModularForm.E₆) = _ at h
  rw [h, bernoulli_six]
  split_ifs with hm
  · rfl
  · push_cast; ring

/-- Exact `q`-expansion coefficients of `E8Eisenstein`:
`coeff 0 = 1`, and `coeff m = 480 * σ₇(m)` for `m ≥ 1`. -/
theorem E8Eisenstein_qExpansion_coeff (m : ℕ) :
    PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 E8Eisenstein) =
      if m = 0 then 1 else 480 * (ArithmeticFunction.sigma 7 m : ℂ) := by
  rw [E8Eisenstein_eq_coe]
  have h := EisensteinSeries.E_qExpansion_coeff (k := 8) (by norm_num) (by decide) m
  rw [h, bernoulli_eight]
  split_ifs with hm
  · rfl
  · push_cast; ring

/-- Helper: every level-1 modular form `f` satisfies `f(τ) → coeff 0 (qExpansion 1 f)` as `Im(τ) → ∞`. -/
private lemma tendsto_levelOne_atImInfty {k : ℤ} (f : ModularForm SL2ZRange k) :
    Filter.Tendsto (f : UpperHalfPlane → ℂ) UpperHalfPlane.atImInfty
      (nhds (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)))) := by
  have hper : Function.Periodic ((f : UpperHalfPlane → ℂ) ∘ (UpperHalfPlane.ofComplex : ℂ → UpperHalfPlane)) (1 : ℝ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz1 : 0 < (z + 1).im := by simpa using hz
      have hof1 : UpperHalfPlane.ofComplex (z + 1) = ModularGroup.T • UpperHalfPlane.ofComplex z := by
        apply UpperHalfPlane.ext
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
          show ((ModularGroup.T • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) =
            (UpperHalfPlane.ofComplex z : ℂ) + 1 by
            simpa [zpow_one] using ModularGroup.coe_T_zpow_smul_eq (UpperHalfPlane.ofComplex z) (n := 1),
          UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      simp only [Function.comp_apply, Complex.ofReal_one, hof1]
      have hT := congrFun (f.slash_action_eq' _ ⟨ModularGroup.T, rfl⟩) (UpperHalfPlane.ofComplex z)
      change SlashAction.map k (sl2ZToGL2R ModularGroup.T) (f : UpperHalfPlane → ℂ)
        (UpperHalfPlane.ofComplex z) = f (UpperHalfPlane.ofComplex z) at hT
      rwa [slash_T_apply] at hT
    · have hz1 : ¬ 0 < (z + 1).im := by simpa using hz
      simp only [Function.comp_apply, Complex.ofReal_one,
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz1),
        UpperHalfPlane.ofComplex_apply_of_im_nonpos (not_lt.mp hz)]
  have hval : UpperHalfPlane.valueAtInfty (f : UpperHalfPlane → ℂ) =
      PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) :=
    (UpperHalfPlane.qExpansion_coeff_zero zero_lt_one
      (ModularFormClass.analyticAt_cuspFunction_zero f zero_lt_one one_mem_strictPeriods_SL) hper).symm
  rcases ModularFormClass.exp_decay_sub_atImInfty' f with ⟨c, hc, hO⟩
  have hneg : Filter.Tendsto (fun t : ℝ => -c * t) Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hc) Filter.tendsto_id
  have hexp0 : Filter.Tendsto (fun τ : UpperHalfPlane => Real.exp (-c * τ.im))
      UpperHalfPlane.atImInfty (nhds 0) :=
    (Real.tendsto_exp_atBot.comp hneg).comp Filter.tendsto_comap
  have hsub0 : Filter.Tendsto
      (fun τ : UpperHalfPlane => f τ - PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)))
      UpperHalfPlane.atImInfty (nhds 0) := by
    rw [← hval]
    exact hO.trans_tendsto hexp0
  simpa using hsub0.add_const (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)))

/-- Limit of `E4` at `i∞`: `E4(τ) → 1` as `Im(τ) → ∞`. -/
theorem tendsto_E4_atImInfty :
    Filter.Tendsto E4 UpperHalfPlane.atImInfty (nhds 1) := by
  rw [E4_eq_coe]
  have h := tendsto_levelOne_atImInfty ModularForm.E₄
  rwa [EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide)] at h

/-- Limit of `E6` at `i∞`: `E6(τ) → 1` as `Im(τ) → ∞`. -/
theorem tendsto_E6_atImInfty :
    Filter.Tendsto E6 UpperHalfPlane.atImInfty (nhds 1) := by
  rw [E6_eq_coe]
  have h := tendsto_levelOne_atImInfty ModularForm.E₆
  rwa [EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) (by decide)] at h

private lemma isBoundedAtImInfty_of_tendsto_one {f : UpperHalfPlane → ℂ}
    (hf : Filter.Tendsto f UpperHalfPlane.atImInfty (nhds 1)) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hev : ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty, ‖f τ‖ ≤ 2 := by
    filter_upwards [hf.eventually (Metric.ball_mem_nhds (1 : ℂ) zero_lt_one)] with τ hτ
    rw [dist_eq_norm] at hτ
    have h1 : ‖f τ‖ ≤ ‖f τ - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (f τ - 1) 1
      simpa using this
    simp only [norm_one] at h1
    linarith
  rw [UpperHalfPlane.atImInfty, Filter.eventually_comap] at hev
  rcases Filter.eventually_atTop.mp hev with ⟨A, hA⟩
  exact ⟨2, A, fun τ hτ => hA τ.im hτ τ rfl⟩

/-- Boundedness of `E4` at `i∞`. -/
theorem isBoundedAtImInfty_E4 : UpperHalfPlane.IsBoundedAtImInfty E4 :=
  isBoundedAtImInfty_of_tendsto_one tendsto_E4_atImInfty

/-- Boundedness of `E6` at `i∞`. -/
theorem isBoundedAtImInfty_E6 : UpperHalfPlane.IsBoundedAtImInfty E6 :=
  isBoundedAtImInfty_of_tendsto_one tendsto_E6_atImInfty

/-- Imaginary-axis limit `E4(i t) → 1` as `t → ∞`. -/
theorem tendsto_E4_imag_axis :
    Filter.Tendsto (fun t : ℝ => E4 (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))))
      Filter.atTop (nhds 1) := by
  refine tendsto_E4_atImInfty.comp ?_
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  refine Filter.tendsto_id.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have him : 0 < (Complex.I * (t : ℂ)).im := by simp [ht]
  have hof : UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) = ⟨Complex.I * (t : ℂ), him⟩ :=
    UpperHalfPlane.ofComplex_apply_of_im_pos him
  simp [hof]

/-- Imaginary-axis limit `E6(i t) → 1` as `t → ∞`. -/
theorem tendsto_E6_imag_axis :
    Filter.Tendsto (fun t : ℝ => E6 (UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))))
      Filter.atTop (nhds 1) := by
  refine tendsto_E6_atImInfty.comp ?_
  rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
  refine Filter.tendsto_id.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have him : 0 < (Complex.I * (t : ℂ)).im := by simp [ht]
  have hof : UpperHalfPlane.ofComplex (Complex.I * (t : ℂ)) = ⟨Complex.I * (t : ℂ), him⟩ :=
    UpperHalfPlane.ofComplex_apply_of_im_pos him
  simp [hof]

/-- Full `SL₂(ℤ)` weight-4 slash-invariance of `E4`. -/
theorem E4_slash_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (4 : ℤ) (sl2ZToGL2R γ) E4 = E4 := by
  rw [E4_eq_coe, sl2ZToGL2R_eq_mapGL]
  exact ModularForm.E₄.slash_action_eq' _ ⟨γ, rfl⟩

/-- Exact `S`-modularity of `E4`: `E4(S • τ) = τ^4 · E4(τ)`. -/
theorem E4_S_smul (τ : UpperHalfPlane) :
    E4 (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * E4 τ := by
  have h := congrFun (E4_slash_SL2Z_invariant ModularGroup.S) τ
  rw [slash_S_apply] at h
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  calc E4 (ModularGroup.S • τ)
      = (E4 (ModularGroup.S • τ) * (τ : ℂ) ^ (-(4 : ℤ))) * (τ : ℂ) ^ (4 : ℤ) := by
          rw [mul_assoc, ← zpow_add₀ hτ, neg_add_cancel, zpow_zero, mul_one]
    _ = E4 τ * (τ : ℂ) ^ (4 : ℤ) := by rw [h]
    _ = (τ : ℂ) ^ 4 * E4 τ := by norm_cast; ring

/-- Exact `T`-periodicity of `E4`: `E4(T • τ) = E4(τ)`. -/
theorem E4_T_smul (τ : UpperHalfPlane) :
    E4 (ModularGroup.T • τ) = E4 τ := by
  have h := congrFun (E4_slash_SL2Z_invariant ModularGroup.T) τ
  rwa [slash_T_apply] at h

/-- Full `SL₂(ℤ)` weight-6 slash-invariance of `E6`. -/
theorem E6_slash_SL2Z_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map (6 : ℤ) (sl2ZToGL2R γ) E6 = E6 := by
  rw [E6_eq_coe, sl2ZToGL2R_eq_mapGL]
  exact ModularForm.E₆.slash_action_eq' _ ⟨γ, rfl⟩

/-- Exact `S`-modularity of `E6`: `E6(S • τ) = τ^6 · E6(τ)`. -/
theorem E6_S_smul (τ : UpperHalfPlane) :
    E6 (ModularGroup.S • τ) = (τ : ℂ) ^ 6 * E6 τ := by
  have h := congrFun (E6_slash_SL2Z_invariant ModularGroup.S) τ
  rw [slash_S_apply] at h
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  calc E6 (ModularGroup.S • τ)
      = (E6 (ModularGroup.S • τ) * (τ : ℂ) ^ (-(6 : ℤ))) * (τ : ℂ) ^ (6 : ℤ) := by
          rw [mul_assoc, ← zpow_add₀ hτ, neg_add_cancel, zpow_zero, mul_one]
    _ = E6 τ * (τ : ℂ) ^ (6 : ℤ) := by rw [h]
    _ = (τ : ℂ) ^ 6 * E6 τ := by norm_cast; ring

/-- Exact `T`-periodicity of `E6`: `E6(T • τ) = E6(τ)`. -/
theorem E6_T_smul (τ : UpperHalfPlane) :
    E6 (ModularGroup.T • τ) = E6 τ := by
  have h := congrFun (E6_slash_SL2Z_invariant ModularGroup.T) τ
  rwa [slash_T_apply] at h

/-- Classical modular discriminant identity `Δ(τ) = (E₄(τ)³ - E₆(τ)²) / 1728`. -/
theorem discriminant_eq_E4_cube_sub_E6_sq (τ : UpperHalfPlane) :
    ModularForm.discriminant τ = (E4 τ ^ 3 - E6 τ ^ 2) / 1728 := by
  rw [E4_eq_modularForm_E4, E6_eq_modularForm_E6]
  exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ

end HolomorphicEisenstein

/-! ## Section 2: Low-Weight Level-1 Vanishing (`S_k(SL₂(ℤ)) = 0` for `k < 12`, `dim M_4 = dim M_6 = dim M_8 = 1`) -/

section LowWeightVanishing

/-- Every level-1 cusp form of weight `k < 12` vanishes identically: `S_k(SL₂(ℤ)) = 0`. -/
theorem cuspForm_SL2Z_eq_zero_of_weight_lt_twelve {k : ℤ} (hk : k < 12)
    (f : CuspForm SL2ZRange k) : f = 0 := by
  have hrank : Module.rank ℂ (CuspForm SL2ZRange k) = 0 :=
    CuspForm.rank_eq_zero_of_weight_lt_twelve hk
  have : Subsingleton (CuspForm SL2ZRange k) := rank_zero_iff.mp hrank
  exact Subsingleton.elim f 0

/-- Every level-1 modular form of weight `k < 12` whose constant term vanishes at `∞` is `0`. -/
theorem modularForm_SL2Z_eq_zero_of_coeff_zero_eq_zero {k : ℤ} (hk : k < 12)
    (f : ModularForm SL2ZRange k)
    (h0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) = 0) :
    f = 0 := by
  have hc : f.toCuspForm h0 = 0 := cuspForm_SL2Z_eq_zero_of_weight_lt_twelve hk (f.toCuspForm h0)
  ext τ
  have hτ := congrArg (fun g : CuspForm SL2ZRange k => g τ) hc
  simpa using hτ

/-- **1-Dimensionality of `M₄(SL₂(ℤ))`**: every weight-4 level-1 modular form is a scalar multiple
of `E₄` determined by its constant term at `∞`. -/
theorem modularForm_SL2Z_weight_four_eq_smul_E4 (f : ModularForm SL2ZRange 4) :
    f = (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) •
      ModularForm.E₄ := by
  set c : ℂ := PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))
  have h0 : PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 ((f - c • ModularForm.E₄ : ModularForm SL2ZRange 4) :
        UpperHalfPlane → ℂ)) = 0 := by
    have hsub : UpperHalfPlane.qExpansion 1
        ((f - c • ModularForm.E₄ : ModularForm SL2ZRange 4) : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ) -
          c • UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
      rw [FunLike.coe_sub,
        ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL f (c • ModularForm.E₄),
        FunLike.coe_smul,
        ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL c ModularForm.E₄]
    rw [hsub, map_sub, map_smul, smul_eq_mul,
      EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide)]
    simp [c]
  exact sub_eq_zero.mp (modularForm_SL2Z_eq_zero_of_coeff_zero_eq_zero (by norm_num) _ h0)

/-- **1-Dimensionality of `M₆(SL₂(ℤ))`**: every weight-6 level-1 modular form is a scalar multiple
of `E₆` determined by its constant term at `∞`. -/
theorem modularForm_SL2Z_weight_six_eq_smul_E6 (f : ModularForm SL2ZRange 6) :
    f = (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) •
      ModularForm.E₆ := by
  set c : ℂ := PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))
  have h0 : PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1 ((f - c • ModularForm.E₆ : ModularForm SL2ZRange 6) :
        UpperHalfPlane → ℂ)) = 0 := by
    have hsub : UpperHalfPlane.qExpansion 1
        ((f - c • ModularForm.E₆ : ModularForm SL2ZRange 6) : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ) -
          c • UpperHalfPlane.qExpansion 1 (ModularForm.E₆ : UpperHalfPlane → ℂ) := by
      rw [FunLike.coe_sub,
        ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL f (c • ModularForm.E₆),
        FunLike.coe_smul,
        ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL c ModularForm.E₆]
    rw [hsub, map_sub, map_smul, smul_eq_mul,
      EisensteinSeries.E_qExpansion_coeff_zero (k := 6) (by norm_num) (by decide)]
    simp [c]
  exact sub_eq_zero.mp (modularForm_SL2Z_eq_zero_of_coeff_zero_eq_zero (by norm_num) _ h0)

/-- **1-Dimensionality of `M₈(SL₂(ℤ))`**: every weight-8 level-1 modular form is a scalar multiple
of `E₈` determined by its constant term at `∞`. -/
theorem modularForm_SL2Z_weight_eight_eq_smul_E8 (f : ModularForm SL2ZRange 8) :
    f = (PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) •
      ModularForm.E (k := 8) (by norm_num) := by
  set c : ℂ := PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))
  have h0 : PowerSeries.coeff 0
      (UpperHalfPlane.qExpansion 1
        ((f - c • ModularForm.E (k := 8) (by norm_num) : ModularForm SL2ZRange 8) :
          UpperHalfPlane → ℂ)) = 0 := by
    have hsub : UpperHalfPlane.qExpansion 1
        ((f - c • ModularForm.E (k := 8) (by norm_num) : ModularForm SL2ZRange 8) :
          UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ) -
          c • UpperHalfPlane.qExpansion 1
            (ModularForm.E (k := 8) (by norm_num) : UpperHalfPlane → ℂ) := by
      rw [FunLike.coe_sub,
        ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL f
          (c • ModularForm.E (k := 8) (by norm_num)),
        FunLike.coe_smul,
        ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL c
          (ModularForm.E (k := 8) (by norm_num))]
    rw [hsub, map_sub, map_smul, smul_eq_mul,
      EisensteinSeries.E_qExpansion_coeff_zero (k := 8) (by norm_num) (by decide)]
    simp [c]
  exact sub_eq_zero.mp (modularForm_SL2Z_eq_zero_of_coeff_zero_eq_zero (by norm_num) _ h0)

/-- Explicit dimension formulas `dim S₄(SL₂(ℤ)) = 0` and `dim M₄(SL₂(ℤ)) = 1`. -/
theorem rank_cuspForm_SL2Z_weight_four :
    Module.rank ℂ (CuspForm SL2ZRange 4) = 0 :=
  CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)

theorem rank_modularForm_SL2Z_weight_four :
    Module.rank ℂ (ModularForm SL2ZRange 4) = 1 :=
  ModularForm.levelOne_weight_four_rank_one

/-- Classical identity `E₄(τ)² = E₈(τ)` (consequence of `dim M₈(SL₂(ℤ)) = 1`). -/
theorem E4_sq_eq_E8Eisenstein (τ : UpperHalfPlane) :
    E4 τ ^ 2 = E8Eisenstein τ := by
  let f8 : ModularForm SL2ZRange 8 :=
    ModularForm.mcast (by norm_num : (4 : ℤ) + 4 = 8) (ModularForm.E₄.mul ModularForm.E₄) rfl
  have hf8_apply : ∀ z : UpperHalfPlane, f8 z = ModularForm.E₄ z ^ 2 := fun z => by
    change ModularForm.E₄ z * ModularForm.E₄ z = ModularForm.E₄ z ^ 2
    ring
  have hq0 : PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (f8 : UpperHalfPlane → ℂ)) = 1 := by
    have hmul : UpperHalfPlane.qExpansion 1 (f8 : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) *
        UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
      have hcoe : (f8 : UpperHalfPlane → ℂ) =
          (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
        funext z; exact (hf8_apply z).trans (sq _)
      rw [hcoe]
      exact ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL
        ModularForm.E₄ ModularForm.E₄
    rw [hmul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff,
      EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) (by decide), mul_one]
  have heq := modularForm_SL2Z_weight_eight_eq_smul_E8 f8
  rw [hq0, one_smul] at heq
  have hτ := congrArg (fun g : ModularForm SL2ZRange 8 => g τ) heq
  rw [hf8_apply τ, ← E4_eq_modularForm_E4 τ, ← E8Eisenstein_eq_modularForm_E8 τ] at hτ
  exact hτ

/-- **Ramanujan's Divisor-Sum Convolution Identity** (from `E₄² = E₈` in `M₈(SL₂(ℤ))`):
for every `n ≥ 1`,
$$\sigma_7(n) = \sigma_3(n) + 120 \sum_{k = 1}^{n - 1} \sigma_3(k)\, \sigma_3(n - k).$$ -/
theorem ramanujan_sigma7_convolution (n : ℕ) (hn : 1 ≤ n) :
    ArithmeticFunction.sigma 7 n =
      ArithmeticFunction.sigma 3 n +
        120 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 3 k * ArithmeticFunction.sigma 3 (n - k) := by
  have hn0 : n ≠ 0 := by omega
  have hfun : (E8Eisenstein : UpperHalfPlane → ℂ) =
      (ModularForm.E₄ : UpperHalfPlane → ℂ) * (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
    funext τ
    rw [← E4_sq_eq_E8Eisenstein τ, sq, E4_eq_modularForm_E4 τ]
    rfl
  have hq : UpperHalfPlane.qExpansion 1 E8Eisenstein =
      UpperHalfPlane.qExpansion 1 E4 * UpperHalfPlane.qExpansion 1 E4 := by
    rw [hfun, ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL
      ModularForm.E₄ ModularForm.E₄, ← E4_eq_coe]
  have hanti :
      (∑ p ∈ Finset.antidiagonal n,
        PowerSeries.coeff p.1 (UpperHalfPlane.qExpansion 1 E4) *
        PowerSeries.coeff p.2 (UpperHalfPlane.qExpansion 1 E4)) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 E4) *
        PowerSeries.coeff (n - k) (UpperHalfPlane.qExpansion 1 E4) :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => PowerSeries.coeff a (UpperHalfPlane.qExpansion 1 E4) *
        PowerSeries.coeff b (UpperHalfPlane.qExpansion 1 E4)) n
  have hsub0 : n - 0 = n := Nat.sub_zero n
  have hsubn : n - n = 0 := Nat.sub_self n
  have hmid :
      (∑ k ∈ Finset.range (n - 1),
        PowerSeries.coeff (k + 1) (UpperHalfPlane.qExpansion 1 E4) *
        PowerSeries.coeff (n - (k + 1)) (UpperHalfPlane.qExpansion 1 E4)) =
      ∑ k ∈ Finset.Ioo 0 n,
        (240 * (ArithmeticFunction.sigma 3 k : ℂ)) *
        (240 * (ArithmeticFunction.sigma 3 (n - k) : ℂ)) := by
    refine Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      exact Finset.mem_Ioo.mpr ⟨Nat.succ_pos k, by omega⟩
    · intro j hj
      rcases Finset.mem_Ioo.mp hj with ⟨hj0, hjn⟩
      exact Finset.mem_range.mpr (by omega)
    · intro k _; exact Nat.add_sub_cancel k 1
    · intro j hj
      rcases Finset.mem_Ioo.mp hj with ⟨hj0, _⟩
      exact Nat.sub_add_cancel hj0
    · intro k hk
      have hk' : k < n - 1 := Finset.mem_range.mp hk
      have hne1 : k + 1 ≠ 0 := Nat.succ_ne_zero k
      have hne2 : n - (k + 1) ≠ 0 := by omega
      rw [E4_qExpansion_coeff (k + 1), if_neg hne1, E4_qExpansion_coeff (n - (k + 1)), if_neg hne2]
  have hrange : Finset.range n = Finset.range ((n - 1) + 1) := by congr 1; omega
  have hsum_Ioo :
      (∑ k ∈ Finset.range (n - 1),
        PowerSeries.coeff (k + 1) (UpperHalfPlane.qExpansion 1 E4) *
        PowerSeries.coeff (n - (k + 1)) (UpperHalfPlane.qExpansion 1 E4)) =
      (240 * 240 : ℂ) *
        ∑ k ∈ Finset.Ioo 0 n,
          (ArithmeticFunction.sigma 3 k : ℂ) * (ArithmeticFunction.sigma 3 (n - k) : ℂ) := by
    rw [hmid, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hrange' : (∑ k ∈ Finset.range n,
      PowerSeries.coeff k (UpperHalfPlane.qExpansion 1 E4) *
      PowerSeries.coeff (n - k) (UpperHalfPlane.qExpansion 1 E4)) =
      (∑ k ∈ Finset.range (n - 1),
        PowerSeries.coeff (k + 1) (UpperHalfPlane.qExpansion 1 E4) *
        PowerSeries.coeff (n - (k + 1)) (UpperHalfPlane.qExpansion 1 E4)) +
      1 * (240 * (ArithmeticFunction.sigma 3 n : ℂ)) := by
    rw [hrange, Finset.sum_range_succ', hsub0, E4_qExpansion_coeff 0, if_pos rfl,
      E4_qExpansion_coeff n, if_neg hn0]
  have hcoeff0 := congrArg (PowerSeries.coeff n) hq
  rw [E8Eisenstein_qExpansion_coeff n, if_neg hn0, PowerSeries.coeff_mul, hanti,
    Finset.sum_range_succ, hsubn, E4_qExpansion_coeff 0, if_pos rfl,
    E4_qExpansion_coeff n, if_neg hn0, hrange', hsum_Ioo] at hcoeff0
  have hC : (480 : ℂ) * (ArithmeticFunction.sigma 7 n : ℂ) =
      (480 : ℂ) * ((ArithmeticFunction.sigma 3 n +
        120 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 3 k * ArithmeticFunction.sigma 3 (n - k) : ℕ) : ℂ) := by
    rw [hcoeff0]
    push_cast
    ring
  have hC' : ((ArithmeticFunction.sigma 7 n : ℕ) : ℂ) =
      ((ArithmeticFunction.sigma 3 n +
        120 * ∑ k ∈ Finset.Ioo 0 n,
          ArithmeticFunction.sigma 3 k * ArithmeticFunction.sigma 3 (n - k) : ℕ) : ℂ) :=
    mul_left_cancel₀ (by norm_num : (480 : ℂ) ≠ 0) hC
  exact Nat.cast_injective hC'

end LowWeightVanishing

/-! ## Section 3: Exact `E₈` Shell Decomposition & UNCONDITIONAL SIEGEL–WEIL FORMULA `Θ_{E₈} = E₄` -/

section SiegelWeilE8

/-- The `n`-th norm shell of the `E₈` lattice: `{v ∈ E₈ | ‖v‖² = 2n}`. -/
abbrev E8Shell (n : ℕ) : Type :=
  {v : E8Lattice // ‖(v : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 2 * (n : ℝ)}

/-- Every `E₈` vector has squared norm `2 * n` for a unique natural number `n : ℕ`. -/
lemma exists_nat_norm_sq_eq_two_mul_E8 (v : E8Lattice) :
    ∃ n : ℕ, ‖(v : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 2 * (n : ℝ) := by
  obtain ⟨m, hm⟩ := isEvenLattice_E8Lattice (v : EuclideanSpace ℝ (Fin 8)) v.2
  have hm_nonneg : (0 : ℤ) ≤ m := by
    have hnn : (0 : ℝ) ≤ 2 * (m : ℝ) := hm ▸ sq_nonneg _
    have hmR : (0 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast hmR
  refine ⟨m.toNat, ?_⟩
  rw [hm]
  have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hm_nonneg
  rw [hcast]

/-- Every shell `E8Shell n = {v ∈ E₈ | ‖v‖² = 2n}` is finite! -/
instance finite_E8Shell (n : ℕ) : Finite (E8Shell n) := by
  let M : ℤ := 2 * (n : ℤ) + 2
  let box : Finset (Fin 8 → ℤ) := Fintype.piFinset (fun _ : Fin 8 => Finset.Icc (-M) M)
  let toBox : E8Shell n → box := fun v =>
    ⟨fun i => Classical.choose (v.1.2.1 i), by
      rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      set k : ℤ := Classical.choose (v.1.2.1 i)
      have hk : 2 * (v.1 : EuclideanSpace ℝ (Fin 8)) i = (k : ℝ) :=
        Classical.choose_spec (v.1.2.1 i)
      have hvi_sq : ((v.1 : EuclideanSpace ℝ (Fin 8)) i) ^ 2 ≤ 2 * (n : ℝ) := by
        calc ((v.1 : EuclideanSpace ℝ (Fin 8)) i) ^ 2
            = ‖(v.1 : EuclideanSpace ℝ (Fin 8)) i‖ ^ 2 := by simp [Real.norm_eq_abs]
          _ ≤ ∑ j : Fin 8, ‖(v.1 : EuclideanSpace ℝ (Fin 8)) j‖ ^ 2 :=
              Finset.single_le_sum
                (f := fun j : Fin 8 => ‖(v.1 : EuclideanSpace ℝ (Fin 8)) j‖ ^ 2)
                (fun j _ => sq_nonneg _) (Finset.mem_univ i)
          _ = ‖(v.1 : EuclideanSpace ℝ (Fin 8))‖ ^ 2 := (EuclideanSpace.norm_sq_eq _).symm
          _ = 2 * (n : ℝ) := v.2
      have hk_sq : (k : ℝ) ^ 2 ≤ 8 * (n : ℝ) := by
        have h1 : (k : ℝ) ^ 2 = 4 * ((v.1 : EuclideanSpace ℝ (Fin 8)) i) ^ 2 := by
          rw [← hk]; ring
        linarith
      have hM_ge : (8 * (n : ℝ)) ≤ (M : ℝ) ^ 2 := by
        dsimp only [M]; push_cast; nlinarith
      have hk_abs : |(k : ℝ)| ≤ (M : ℝ) := by
        have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := by dsimp only [M]; positivity
        have hsq : (k : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := hk_sq.trans hM_ge
        exact abs_le_of_sq_le_sq hsq hM_nonneg
      have ⟨hlo, hhi⟩ := abs_le.mp hk_abs
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩⟩
  have hinj : Function.Injective toBox := by
    intro u w h
    apply Subtype.ext
    apply Subtype.ext
    ext i
    have hki : Classical.choose (u.1.2.1 i) = Classical.choose (w.1.2.1 i) :=
      congrFun (congrArg Subtype.val h) i
    have hu : 2 * (u.1 : EuclideanSpace ℝ (Fin 8)) i = ((Classical.choose (u.1.2.1 i) : ℤ) : ℝ) :=
      Classical.choose_spec (u.1.2.1 i)
    have hw : 2 * (w.1 : EuclideanSpace ℝ (Fin 8)) i = ((Classical.choose (w.1.2.1 i) : ℤ) : ℝ) :=
      Classical.choose_spec (w.1.2.1 i)
    have hkiR : ((Classical.choose (u.1.2.1 i) : ℤ) : ℝ) = ((Classical.choose (w.1.2.1 i) : ℤ) : ℝ) := by
      exact_mod_cast hki
    linarith
  exact Finite.of_injective toBox hinj

/-- The 0-th shell `E8Shell 0` has cardinality `1` (consisting solely of the zero vector). -/
theorem natCard_E8Shell_zero : Nat.card (E8Shell 0) = 1 := by
  have hne : Nonempty (E8Shell 0) := ⟨⟨0, by simp⟩⟩
  have hsub : Subsingleton (E8Shell 0) := ⟨fun u v => by
    have h0 : ∀ w : E8Shell 0, w.1 = 0 := fun w => by
      apply Subtype.ext
      have hsq : ‖(w.1 : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 0 := by simpa using w.2
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    exact Subtype.ext ((h0 u).trans (h0 v).symm)⟩
  exact Nat.card_unique

/-- Canonical shell decomposition equivalence `E8Lattice ≃ Σ n : ℕ, E8Shell n`. -/
def E8LatticeEquivSigmaShell : E8Lattice ≃ Σ n : ℕ, E8Shell n where
  toFun v :=
    ⟨Classical.choose (exists_nat_norm_sq_eq_two_mul_E8 v),
     ⟨v, Classical.choose_spec (exists_nat_norm_sq_eq_two_mul_E8 v)⟩⟩
  invFun p := p.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨n, ⟨v, hv⟩⟩
    dsimp only
    have hn : Classical.choose (exists_nat_norm_sq_eq_two_mul_E8 v) = n := by
      have hspec := Classical.choose_spec (exists_nat_norm_sq_eq_two_mul_E8 v)
      have hR : ((Classical.choose (exists_nat_norm_sq_eq_two_mul_E8 v) : ℕ) : ℝ) = (n : ℝ) := by
        linarith
      exact_mod_cast hR
    cases hn
    rfl

/-- **Exact `q`-Series Expansion of `Θ_{E₈}(τ)`**:
for every `τ : UpperHalfPlane`,
`HasSum (fun n => (Nat.card (E8Shell n) : ℂ) • qParam 1 τ ^ n) (complexLatticeTheta E8Lattice τ)`. -/
theorem complexLatticeTheta_E8Lattice_hasSum_qParam (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      (Nat.card (E8Shell n) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n)
      (complexLatticeTheta E8Lattice τ) := by
  have hsum_L : HasSum (fun v : E8Lattice => complexGaussianTerm (τ : ℂ) (v : EuclideanSpace ℝ (Fin 8)))
      (complexLatticeTheta E8Lattice τ) :=
    (summable_complexGaussianTerm E8Lattice τ.im_pos).hasSum
  have hsum_sig : HasSum
      (fun p : Σ n : ℕ, E8Shell n =>
        complexGaussianTerm (τ : ℂ) (p.2.1 : EuclideanSpace ℝ (Fin 8)))
      (complexLatticeTheta E8Lattice τ) :=
    (E8LatticeEquivSigmaShell.symm.hasSum_iff).mpr hsum_L
  have hinner : ∀ n : ℕ,
      HasSum (fun v : E8Shell n => complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin 8)))
        ((Nat.card (E8Shell n) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n) := by
    intro n
    cases nonempty_fintype (E8Shell n)
    have hterm : ∀ v : E8Shell n,
        complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin 8)) =
          Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n := by
      intro v
      unfold complexGaussianTerm Function.Periodic.qParam
      rw [v.2, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hfin := hasSum_fintype (fun v : E8Shell n =>
      complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin 8)))
    have hsum_eq : (∑ v : E8Shell n, complexGaussianTerm (τ : ℂ) (v.1 : EuclideanSpace ℝ (Fin 8))) =
        (Nat.card (E8Shell n) : ℂ) • Function.Periodic.qParam (1 : ℝ) (τ : ℂ) ^ n := by
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    rwa [hsum_eq] at hfin
  exact hsum_sig.sigma hinner

/-- Boundedness of `complexLatticeTheta E8Lattice` at `i∞`. -/
theorem isBoundedAtImInfty_complexLatticeTheta_E8Lattice :
    UpperHalfPlane.IsBoundedAtImInfty (complexLatticeTheta E8Lattice) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨latticeTheta E8Lattice 1, 1, fun τ hτ => ?_⟩
  have h1 := norm_complexLatticeTheta_le E8Lattice τ
  refine h1.trans ?_
  unfold latticeTheta
  refine Summable.tsum_le_tsum (fun v => ?_) (summable_gaussianTerm E8Lattice τ.im_pos)
    (summable_gaussianTerm E8Lattice zero_lt_one)
  unfold gaussianTerm
  apply Real.exp_le_exp.mpr
  have hnn : 0 ≤ Real.pi * ‖(v : EuclideanSpace ℝ (Fin 8))‖ ^ 2 :=
    mul_nonneg Real.pi_pos.le (sq_nonneg _)
  nlinarith

/-- **The Concrete `E₈` Theta Function Packaged as a Mathlib Level-1 Weight-4 Modular Form**
`E8ThetaModularForm : ModularForm SL₂(ℤ) 4`! -/
def E8ThetaModularForm : ModularForm SL2ZRange 4 where
  toFun := complexLatticeTheta E8Lattice
  slash_action_eq' := by
    rintro _ ⟨γ, rfl⟩
    simpa [sl2ZToGL2R_eq_mapGL] using E8Lattice_slash_SL2Z_invariant γ
  holo' := mdifferentiable_complexLatticeTheta E8Lattice
  bdd_at_cusps' := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hinv : SlashAction.map (4 : ℤ) γ (complexLatticeTheta E8Lattice) =
        complexLatticeTheta E8Lattice := by
      rw [ModularForm.SL_slash]
      exact E8Lattice_slash_SL2Z_invariant γ
    rw [hinv]
    exact isBoundedAtImInfty_complexLatticeTheta_E8Lattice

@[simp]
lemma E8ThetaModularForm_apply (τ : UpperHalfPlane) :
    E8ThetaModularForm τ = complexLatticeTheta E8Lattice τ := rfl

/-- Exact `n`-th `q`-expansion coefficient of `E8ThetaModularForm` equals the shell count
`Nat.card (E8Shell n)` for EVERY `n : ℕ`. -/
theorem E8ThetaModularForm_qExpansion_coeff (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (E8ThetaModularForm : UpperHalfPlane → ℂ)) =
      (Nat.card (E8Shell n) : ℂ) :=
  (ModularFormClass.qExpansion_coeff_unique zero_lt_one one_mem_strictPeriods_SL
    (f := E8ThetaModularForm) complexLatticeTheta_E8Lattice_hasSum_qParam n).symm

/-- **UNCONDITIONAL MODULAR-FORM SIEGEL–WEIL IDENTITY FOR `E₈`**:
`E8ThetaModularForm = ModularForm.E₄` in `ModularForm (SL₂(ℤ)) 4`! -/
theorem E8ThetaModularForm_eq_E4 : E8ThetaModularForm = ModularForm.E₄ := by
  have h := modularForm_SL2Z_weight_four_eq_smul_E4 E8ThetaModularForm
  rw [E8ThetaModularForm_qExpansion_coeff 0, natCard_E8Shell_zero, Nat.cast_one, one_smul] at h
  exact h

/-- **UNCONDITIONAL CONCRETE SIEGEL–WEIL FORMULA FOR `E₈` (ZERO ASSUMPTIONS!)**:
for EVERY `τ : UpperHalfPlane`,
$$\Theta_{E_8}(\tau) = E_4(\tau) = 1 + 240 \sum_{n \ge 1} \sigma_3(n) e^{2\pi i n \tau}.$$ -/
theorem complexLatticeTheta_E8Lattice_eq_E4 (τ : UpperHalfPlane) :
    complexLatticeTheta E8Lattice τ = E4 τ := by
  rw [E4_eq_modularForm_E4 τ, ← E8ThetaModularForm_apply τ, E8ThetaModularForm_eq_E4]

/-- **Classical Jacobi–Eisenstein Identity**:
$$\frac{1}{2}\left(\theta_3(\tau)^8 + \theta_4(\tau)^8 + \theta_2(\tau)^8\right) = E_4(\tau).$$ -/
theorem E8_jacobiTheta_eq_E4 (τ : UpperHalfPlane) :
    (1 / 2 : ℂ) * (theta3 (τ : ℂ) ^ 8 + theta4 (τ : ℂ) ^ 8 + theta2 (τ : ℂ) ^ 8) = E4 τ := by
  rw [← complexLatticeTheta_E8Lattice τ]
  exact complexLatticeTheta_E8Lattice_eq_E4 τ

/-- **EXACT `E₈` LATTICE REPRESENTATION COUNT FORMULA (ZERO ASSUMPTIONS!)**:
for EVERY natural number `n ≥ 1`,
$$r_{E_8}(2n) = \#\{v \in E_8 : \|v\|^2 = 2n\} = 240 \cdot \sigma_3(n).$$ -/
theorem E8_representation_count_eq_240_sigma3 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {v : E8Lattice // ‖(v : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 2 * (n : ℝ)} =
      240 * ArithmeticFunction.sigma 3 n := by
  have hn0 : n ≠ 0 := by omega
  have hC : (Nat.card (E8Shell n) : ℂ) = ((240 * ArithmeticFunction.sigma 3 n : ℕ) : ℂ) := by
    calc (Nat.card (E8Shell n) : ℂ)
        = PowerSeries.coeff n
            (UpperHalfPlane.qExpansion 1 (E8ThetaModularForm : UpperHalfPlane → ℂ)) :=
            (E8ThetaModularForm_qExpansion_coeff n).symm
      _ = PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ)) := by
            rw [E8ThetaModularForm_eq_E4]
      _ = PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 E4) := by rw [E4_eq_coe]
      _ = 240 * (ArithmeticFunction.sigma 3 n : ℂ) := by rw [E4_qExpansion_coeff n, if_neg hn0]
      _ = ((240 * ArithmeticFunction.sigma 3 n : ℕ) : ℂ) := by push_cast; rfl
  exact Nat.cast_injective hC

/-- **8-Dimensional Kissing Number (`r_{E₈}(2) = 240`)**:
there are EXACTLY `240` minimal nonzero vectors (roots) of squared norm `2` in `E₈`! -/
theorem E8_kissing_number :
    Nat.card {v : E8Lattice // ‖(v : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 2} = 240 := by
  have h := E8_representation_count_eq_240_sigma3 1 (le_refl 1)
  simpa using h

/-- **Second Shell of `E₈` (`r_{E₈}(4) = 2160`)**:
there are EXACTLY `2160` vectors of squared norm `4` in `E₈`! -/
theorem E8_shell_two_card :
    Nat.card {v : E8Lattice // ‖(v : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 4} = 2160 := by
  have h := E8_representation_count_eq_240_sigma3 2 (by decide)
  have hsig : ArithmeticFunction.sigma 3 2 = 9 := by
    rw [ArithmeticFunction.sigma_apply]
    have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
    rw [hdiv]
    norm_num
  rw [hsig] at h
  norm_num at h
  exact h

/-- **Bonus Siegel–Weil Identity for `E₈²` (Rank 16, Weight 8)**:
`Θ_{E₈²}(τ) = E₄(τ)² = E₈(τ) = 1 + 480 ∑_{n ≥ 1} σ₇(n) qⁿ`! -/
theorem complexLatticeTheta_E8PowLattice_two_eq_E8Eisenstein (τ : UpperHalfPlane) :
    complexLatticeTheta (E8PowLattice 2) τ = E8Eisenstein τ := by
  rw [complexLatticeTheta_E8PowLattice 2 τ, complexLatticeTheta_E8Lattice_eq_E4 τ,
    E4_sq_eq_E8Eisenstein τ]

end SiegelWeilE8

/-! ## Section 4: Exact Epstein–Eisenstein Zeta Factorization & Euler Product for `E₈` -/

section EpsteinZetaFactorization

/-- Exact `LSeries` identity for the divisor power sum `σ_k`:
on `Re(w) > k + 1`, `L(σ_k, w) = ζ(w) · ζ(w - k)`. -/
theorem LSeries_sigma_eq_riemannZeta_mul (k : ℕ) {w : ℂ} (hw : (k : ℝ) + 1 < w.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.sigma k n : ℂ)) w =
      riemannZeta w * riemannZeta (w - (k : ℂ)) := by
  have hw1 : 1 < w.re := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hwk : 1 < (w - (k : ℂ)).re := by simp; linarith
  have hsum1 : LSeriesSummable (1 : ℕ → ℂ) w := LSeriesSummable_one_iff.mpr hw1
  have hsumk : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ k) w := by
    have hsum_shift : LSeriesSummable (1 : ℕ → ℂ) (w - (k : ℂ)) := LSeriesSummable_one_iff.mpr hwk
    refine hsum_shift.congr fun n => ?_
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply]
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      rw [Complex.cpow_sub _ _ hnC, Complex.cpow_natCast, div_div_eq_mul_div, one_mul]
  have hconv : LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => (n : ℂ) ^ k) =
      fun n : ℕ => (ArithmeticFunction.sigma k n : ℂ) := by
    funext n
    rw [LSeries.convolution_def, ArithmeticFunction.sigma_apply]
    dsimp only
    have hsum_anti :
        (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * (p.2 : ℂ) ^ k) =
        ∑ d ∈ n.divisors, (d : ℂ) ^ k := by
      refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
      · intro p hp
        exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
      · intro d hd
        exact Nat.mem_divisorsAntidiagonal.mpr
          ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
      · intro p hp
        rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
        have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
        ext
        · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
        · rfl
      · intro _ _; rfl
      · intro p _; simp
    rw [hsum_anti]
    push_cast
    rfl
  rw [← hconv, LSeries_convolution' hsum1 hsumk, LSeries_one_eq_riemannZeta hw1]
  congr 1
  rw [← LSeries_one_eq_riemannZeta hwk]
  unfold LSeries
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [LSeries.term, hn]
  · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply]
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [Complex.cpow_sub _ _ hnC, Complex.cpow_natCast, div_div_eq_mul_div, one_mul]

/-- `ℕ+`-indexed Dirichlet series identity for `σ_k`:
for `Re(w) > k + 1`, `∑'_{n : ℕ+} σ_k(n) · n^{-w} = ζ(w) · ζ(w - k)`. -/
theorem tsum_pnat_sigma_mul_cpow (k : ℕ) {w : ℂ} (hw : (k : ℝ) + 1 < w.re) :
    (∑' n : ℕ+, (ArithmeticFunction.sigma k (n : ℕ) : ℂ) * ((n : ℕ) : ℂ) ^ (-w)) =
      riemannZeta w * riemannZeta (w - (k : ℂ)) := by
  have hw1 : 1 < w.re := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hwk : 1 < (w - (k : ℂ)).re := by simp; linarith
  have hsum_sig : LSeriesSummable (fun m : ℕ => (ArithmeticFunction.sigma k m : ℂ)) w := by
    have hsum1 : LSeriesSummable (1 : ℕ → ℂ) w := LSeriesSummable_one_iff.mpr hw1
    have hsumk : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ k) w := by
      have hshift : LSeriesSummable (1 : ℕ → ℂ) (w - (k : ℂ)) := LSeriesSummable_one_iff.mpr hwk
      refine hshift.congr fun n => ?_
      by_cases hn : n = 0
      · simp [LSeries.term, hn]
      · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        rw [Complex.cpow_sub _ _ hnC, Complex.cpow_natCast, div_div_eq_mul_div, one_mul]
    have hconv : LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => (n : ℂ) ^ k) =
        fun n : ℕ => (ArithmeticFunction.sigma k n : ℂ) := by
      funext n
      rw [LSeries.convolution_def, ArithmeticFunction.sigma_apply]
      dsimp only
      have hsum_anti :
          (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * (p.2 : ℂ) ^ k) =
          ∑ d ∈ n.divisors, (d : ℂ) ^ k := by
        refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
        · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
        · intro d hd
          exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
        · intro p hp
          rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
          have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
          ext
          · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
          · rfl
        · intro _ _; rfl
        · intro p _; simp
      rw [hsum_anti]; push_cast; rfl
    rw [← hconv]
    exact hsum1.convolution hsumk
  rw [← LSeries_sigma_eq_riemannZeta_mul k hw]
  unfold LSeries
  rw [hsum_sig.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  let e : ℕ+ ≃ ℕ :=
    { toFun := fun n => (n : ℕ) - 1
      invFun := fun m => ⟨m + 1, Nat.succ_pos m⟩
      left_inv := fun n => Subtype.ext (Nat.sub_add_cancel n.pos)
      right_inv := fun m => Nat.add_sub_cancel m 1 }
  rw [← e.tsum_eq]
  refine tsum_congr fun n => ?_
  have hsucc : e n + 1 = (n : ℕ) := Nat.sub_add_cancel n.pos
  rw [hsucc]
  unfold LSeries.term
  rw [if_neg n.ne_zero, div_eq_mul_inv, Complex.cpow_neg]

/-- Canonical shell decomposition for nonzero `E₈` vectors:
`{v : E8Lattice // (v : ℝ⁸) ≠ 0} ≃ Σ n : ℕ+, E8Shell n`. -/
def E8NonzeroEquivSigmaShell :
    {v : E8Lattice // (v : EuclideanSpace ℝ (Fin 8)) ≠ 0} ≃ Σ n : ℕ+, E8Shell (n : ℕ) :=
  (Equiv.ofBijective
    (fun p : Σ n : ℕ+, E8Shell (n : ℕ) =>
      (⟨p.2.1, by
        intro h0
        have h2 := p.2.2
        rw [h0, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h2
        have hp : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.1.pos
        linarith⟩ : {v : E8Lattice // (v : EuclideanSpace ℝ (Fin 8)) ≠ 0}))
    (by
      constructor
      · rintro ⟨n₁, ⟨v₁, hv₁⟩⟩ ⟨n₂, ⟨v₂, hv₂⟩⟩ h
        have hv : v₁ = v₂ := congrArg Subtype.val h
        subst hv
        have hn : n₁ = n₂ := by
          have hR : ((n₁ : ℕ) : ℝ) = ((n₂ : ℕ) : ℝ) := by linarith
          exact_mod_cast hR
        subst hn
        rfl
      · rintro ⟨v, hv0⟩
        obtain ⟨m, hm⟩ := exists_nat_norm_sq_eq_two_mul_E8 v
        have hm_pos : 0 < m := by
          by_contra h0
          have hm0 : m = 0 := by omega
          rw [hm0, Nat.cast_zero, mul_zero] at hm
          exact hv0 (norm_eq_zero.mp (sq_eq_zero_iff.mp hm))
        exact ⟨⟨⟨m, hm_pos⟩, ⟨v, hm⟩⟩, Subtype.ext rfl⟩)).symm

/-- Helper: if `‖v‖² = 2n` with `n ≥ 1`, then `(‖v‖ : ℂ)^{-s} = 2^{-s/2} · n^{-s/2}`. -/
private lemma norm_cpow_neg_of_norm_sq_eq_two_mul {x : ℝ} {n : ℕ+}
    (hx : 0 ≤ x) (hsq : x ^ 2 = 2 * ((n : ℕ) : ℝ)) (s : ℂ) :
    (x : ℂ) ^ (-s) = (2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2) := by
  have hn_pos : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have hx_pos : 0 < x := by
    by_contra h
    have hx0 : x = 0 := le_antisymm (not_lt.mp h) hx
    rw [hx0] at hsq
    norm_num at hsq
  have hstep1 : (x : ℂ) ^ (-s) = ((x ^ 2 : ℝ) : ℂ) ^ (-s / 2) := by
    rw [Complex.ofReal_pow, ← Complex.cpow_natCast (x : ℂ) 2,
      ← Complex.cpow_mul (x := (x : ℂ)) (y := ((2 : ℕ) : ℂ)) (z := -s / 2)]
    · congr 1; push_cast; ring
    · rw [← Complex.ofReal_log hx_pos.le]; simp [Real.pi_pos]
    · rw [← Complex.ofReal_log hx_pos.le]; simp [Real.pi_pos.le]
  rw [hstep1, hsq, Complex.ofReal_mul]
  have h2re : 0 < ((2 : ℝ) : ℂ).re := by norm_num
  simpa using cpow_mul_ofReal_pos h2re hn_pos (-s / 2)

/-- **EXACT CONCRETE SIEGEL–WEIL / EPSTEIN–EISENSTEIN FACTORIZATION FOR `E₈` (ZERO ASSUMPTIONS!)**:
for EVERY `s : ℂ` with `Re(s) > 8`,
$$Z_{E_8}(s) = 240 \cdot 2^{-s/2} \cdot \zeta(s/2) \cdot \zeta(s/2 - 3).$$ -/
theorem epsteinZeta_E8Lattice_eq {s : ℂ} (hs : (8 : ℝ) < s.re) :
    epsteinZeta E8Lattice s =
      240 * (2 : ℂ) ^ (-s / 2) * riemannZeta (s / 2) * riemannZeta (s / 2 - 3) := by
  have hsum_ep : Summable (fun v : {v : E8Lattice // (v : EuclideanSpace ℝ (Fin 8)) ≠ 0} =>
      ((‖(v.1 : EuclideanSpace ℝ (Fin 8))‖ : ℝ) : ℂ) ^ (-s)) :=
    summable_epsteinZeta E8Lattice (by rwa [rk_E8Lattice])
  have hsum_sig : HasSum
      (fun p : Σ n : ℕ+, E8Shell (n : ℕ) =>
        ((‖(p.2.1 : EuclideanSpace ℝ (Fin 8))‖ : ℝ) : ℂ) ^ (-s))
      (epsteinZeta E8Lattice s) :=
    (E8NonzeroEquivSigmaShell.symm.hasSum_iff).mpr hsum_ep.hasSum
  have hinner : ∀ n : ℕ+,
      HasSum (fun v : E8Shell (n : ℕ) => ((‖(v.1 : EuclideanSpace ℝ (Fin 8))‖ : ℝ) : ℂ) ^ (-s))
        ((Nat.card (E8Shell (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2))) := by
    intro n
    cases nonempty_fintype (E8Shell (n : ℕ))
    have hterm : ∀ v : E8Shell (n : ℕ),
        ((‖(v.1 : EuclideanSpace ℝ (Fin 8))‖ : ℝ) : ℂ) ^ (-s) =
          (2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2) := fun v =>
      norm_cpow_neg_of_norm_sq_eq_two_mul (norm_nonneg _) v.2 s
    have hfin := hasSum_fintype (fun v : E8Shell (n : ℕ) =>
      ((‖(v.1 : EuclideanSpace ℝ (Fin 8))‖ : ℝ) : ℂ) ^ (-s))
    have hsum_eq : (∑ v : E8Shell (n : ℕ), ((‖(v.1 : EuclideanSpace ℝ (Fin 8))‖ : ℝ) : ℂ) ^ (-s)) =
        (Nat.card (E8Shell (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2)) := by
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Nat.card_eq_fintype_card]
    rwa [hsum_eq] at hfin
  have hsum_outer := hsum_sig.sigma hinner
  have houter_eq : epsteinZeta E8Lattice s =
      ∑' n : ℕ+, (Nat.card (E8Shell (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2)) :=
    hsum_outer.tsum_eq.symm
  rw [houter_eq]
  have hrew : (fun n : ℕ+ =>
      (Nat.card (E8Shell (n : ℕ)) : ℂ) * ((2 : ℂ) ^ (-s / 2) * ((n : ℕ) : ℂ) ^ (-s / 2))) =
      fun n : ℕ+ =>
        (240 * (2 : ℂ) ^ (-s / 2)) *
          ((ArithmeticFunction.sigma 3 (n : ℕ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(s / 2))) := by
    funext n
    rw [E8_representation_count_eq_240_sigma3 (n : ℕ) n.pos]
    have hneg : -s / 2 = -(s / 2) := by ring
    rw [hneg]
    push_cast
    ring
  rw [hrew, tsum_mul_left]
  have hw : ((3 : ℕ) : ℝ) + 1 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    push_cast
    linarith
  rw [tsum_pnat_sigma_mul_cpow 3 hw]
  push_cast
  ring

/-- **Exact Completed Epstein Zeta Factorization for `E₈`** on `Re(s) > 8`:
$$\Lambda_{E_8}(s) = 240 \cdot (2\pi)^{-s/2} \Gamma(s/2) \zeta(s/2) \zeta(s/2 - 3).$$ -/
theorem completedEpsteinZeta_E8Lattice_eq {s : ℂ} (hs : (8 : ℝ) < s.re) :
    completedEpsteinZeta E8Lattice s =
      240 * (2 : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
        riemannZeta (s / 2) * riemannZeta (s / 2 - 3) := by
  unfold completedEpsteinZeta
  rw [epsteinZeta_E8Lattice_eq hs]
  ring

/-- Agreement of the globally continued `completedEpsteinZetaExt E8Lattice s` with the exact
Riemann-zeta factorization on `Re(s) > 8`. -/
theorem completedEpsteinZetaExt_E8Lattice_eq_factorization {s : ℂ} (hs : (8 : ℝ) < s.re) :
    completedEpsteinZetaExt E8Lattice s =
      240 * (2 : ℂ) ^ (-s / 2) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) *
        riemannZeta (s / 2) * riemannZeta (s / 2 - 3) := by
  rw [completedEpsteinZetaExt_E8Lattice_eq_completedEpsteinZeta hs]
  exact completedEpsteinZeta_E8Lattice_eq hs

/-- Exact identification of `σ₃(n)` with the Stage 5 normalized Hecke eigenform witness
`Stage5ModularHecke.eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1)`. -/
theorem sigma_three_eq_eisensteinCoeff (n : ℕ) :
    (ArithmeticFunction.sigma 3 n : ℂ) =
      eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1) n := by
  rw [ArithmeticFunction.sigma_apply, eisensteinCoeff]
  push_cast
  refine Finset.sum_congr rfl fun d _ => ?_
  have hd1 : (d : ZMod 1) = 1 := Subsingleton.elim _ _
  simp [heckeWeight, hd1]

/-- **Exact Degree-2 `GL₂` Euler Product for the `E₈` Epstein Zeta Function** on `Re(s) > 8`
(bridging directly to `Stage5ModularHecke.eigenform_LSeries_eulerProduct` for `eisensteinCoeff 4 1`):
$$Z_{E_8}(s) = 240 \cdot 2^{-s/2} \prod_p \left(1 - \sigma_3(p) p^{-s/2} + p^{3 - s}\right)^{-1}.$$ -/
theorem epsteinZeta_E8Lattice_eulerProduct {s : ℂ} (hs : (8 : ℝ) < s.re) :
    epsteinZeta E8Lattice s =
      240 * (2 : ℂ) ^ (-s / 2) *
        ∏' p : Nat.Primes,
          degree2EulerFactor 4 (1 : DirichletCharacter ℂ 1)
            (eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1) (p : ℕ)) (p : ℕ) (s / 2) := by
  have hw : ((3 : ℕ) : ℝ) + 1 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    push_cast
    linarith
  have hw1 : 1 < (s / 2).re := by linarith
  have hw3 : 1 < (s / 2 - (3 : ℂ)).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.re_ofNat]
    linarith
  have hsum_sig : LSeriesSummable (eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1)) (s / 2) := by
    have hsum1 : LSeriesSummable (1 : ℕ → ℂ) (s / 2) := LSeriesSummable_one_iff.mpr hw1
    have hsum3 : LSeriesSummable (fun n : ℕ => (n : ℂ) ^ 3) (s / 2) := by
      have hshift : LSeriesSummable (1 : ℕ → ℂ) (s / 2 - (3 : ℂ)) :=
        LSeriesSummable_one_iff.mpr hw3
      refine hshift.congr fun n => ?_
      by_cases hn : n = 0
      · simp [LSeries.term, hn]
      · simp only [LSeries.term, hn, ↓reduceIte, Pi.one_apply]
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        rw [Complex.cpow_sub _ _ hnC,
          show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast,
          div_div_eq_mul_div, one_mul]
    have hconv : LSeries.convolution (1 : ℕ → ℂ) (fun n : ℕ => (n : ℂ) ^ 3) =
        eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1) := by
      funext n
      rw [← sigma_three_eq_eisensteinCoeff n, LSeries.convolution_def,
        ArithmeticFunction.sigma_apply]
      dsimp only
      have hsum_anti :
          (∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * (p.2 : ℂ) ^ 3) =
          ∑ d ∈ n.divisors, (d : ℂ) ^ 3 := by
        refine Finset.sum_nbij' (fun p => p.2) (fun d => (n / d, d)) ?_ ?_ ?_ ?_ ?_
        · intro p hp; exact Nat.snd_mem_divisors_of_mem_antidiagonal hp
        · intro d hd
          exact Nat.mem_divisorsAntidiagonal.mpr
            ⟨Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd), (Nat.mem_divisors.mp hd).2⟩
        · intro p hp
          rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hpmul, hn0⟩
          have hp2_pos : 0 < p.2 := Nat.pos_of_ne_zero (fun h0 => hn0 (by simp [← hpmul, h0]))
          ext
          · exact (Nat.eq_div_of_mul_eq_left hp2_pos.ne' hpmul).symm
          · rfl
        · intro _ _; rfl
        · intro p _; simp
      rw [hsum_anti]; push_cast; rfl
    rw [← hconv]
    exact hsum1.convolution hsum3
  have heuler := eigenform_LSeries_eulerProduct
    (isNormalizedHeckeEigenform_eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1)) hsum_sig
  rw [heuler]
  have hL_eq : LSeries (eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1)) (s / 2) =
      riemannZeta (s / 2) * riemannZeta (s / 2 - 3) := by
    have hfun : eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1) =
        fun n : ℕ => (ArithmeticFunction.sigma 3 n : ℂ) :=
      funext fun n => (sigma_three_eq_eisensteinCoeff n).symm
    rw [hfun]
    simpa using LSeries_sigma_eq_riemannZeta_mul 3 hw
  rw [hL_eq, epsteinZeta_E8Lattice_eq hs]
  ring

end EpsteinZetaFactorization

end
end RHDirect.Stage7EisensteinSeries
