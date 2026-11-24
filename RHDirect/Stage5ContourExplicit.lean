import RHDirect.Interfaces
import RHDirect.ElementaryEquiv
import RHDirect.MellinExplicit
import RHDirect.Stage2DirichletAP
import RHDirect.Stage3RealAnalyticLandau
import RHDirect.Stage3ZeroFreeRegion
import RHDirect.Stage4ExplicitFormula
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# RHDirect.Stage5ContourExplicit

Deep, 100%-unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings, 0 info) Stage 5 contour-shift
and explicit-formula engine in pure Mathlib `v4.33.1`, building directly on
`RHDirect.Stage4ExplicitFormula`, `RHDirect.Stage3ZeroFreeRegion`,
`RHDirect.Stage3RealAnalyticLandau`, and `RHDirect.Stage2DirichletAP`.

## Main Contents
1. **Rectangular Cauchy Integral Theorem & Exact Multi-Pole Residue Theorem**:
   - `rectBoundaryIntegral`: counterclockwise boundary integral `∮_{∂([σ₀, c] × [y₀, y₁])} f(s) ds`.
   - `rectBoundaryIntegral_eq_zero_of_differentiableOn`: direct wrapper around Mathlib's
     `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.
   - `rectBoundaryIntegral_inv_sub_eq_two_pi_I`: exact elementary evaluation
     `∮_{∂R} (s - p)⁻¹ ds = 2 π i` for any interior pole `p ∈ (σ₀, c) × (y₀, y₁)` via explicit
     `log` / `arctan` primitives and `Real.arctan_inv_of_pos`.
   - `rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues` & `vertical_contour_shift_eq_sum_residues`:
     exact multi-pole rectangular residue theorem and vertical contour-shift identity on
     `[σ₀, c] × [-T, T]`, plus multiplicative residue transfer (`vertical_contour_shift_mul_eq_sum_residues`
     and the `x^s / s` variant `vertical_contour_shift_div_id_eq_sum_residues` with `s = 0` pole).
2. **Pigeonhole Good-Horizontal-Line Selection & Quantitative Contour Estimates**:
   - `exists_good_height_pigeonhole` & `exists_good_height_pigeonhole_symm`: given at most `N`
     ordinates `{γ_j}` in `[T, T + 1]`, there exists `T_* ∈ [T, T + 1]` at distance
     `≥ 1 / (2 (N + 1))` from every `γ_j` (and symmetrically avoiding `±γ_j`).
   - `exists_good_height_avg_integral`: AM-GM 1D integral-averaging good-height selection yielding
     a horizontal line `T_* ∈ (T, T + 1)` where `∫_{σ₀}^c ∑_{ρ ∈ Z} ‖(σ ± i T_*) - ρ‖⁻¹ dσ` is
     **linear** in `Z.card` (`≤ 32 √(c - σ₀) (Z.card + 1)`).
   - Quantitative horizontal and left-vertical contour bounds for both the Cesàro-1 integrand
     `(-L'/L)(s, χ) x^{s+1} / (s (s + 1))` and the sharp Perron integrand `(-L'/L)(s, χ) x^s / s`.
3. **Smoothed Explicit Formula, Sharp Perron Formula, De-Smoothing & `TruncatedExplicitFormulaPackage`**:
   - Exact smoothed explicit formula for `ψ_1(x, χ)` combining `Stage4ExplicitFormula` with the
     contour shift and Pigeonhole good-horizontal-line estimates.
   - Sharp Perron kernel bounds (`norm_perronKernel0_lt_one`, `norm_perronKernel0_gt_one`) proved
     directly from Section 1's Rectangular Residue Theorem, and half-integer truncated Perron
     approximation for `chebyshevPsiChar χ x`.
   - De-smoothing bridges via `Stage3RealAnalyticLandau.chebyshevRamp_diff_sandwich` and `psi1Char`
     finite differences, plus full discharge of `Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage`,
     `Stage2DirichletAP.PsiCharPowerBound`, and `Stage2PrimePairs`
     (`LinnikAPDyadic ∧ LinnikAPInterval ∧ PairSupply ∧ PairEx ∧ SmallOne`) from a
     `MeromorphicLogDerivPackage`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage5ContourExplicit

/-! ## Section 1: Rectangular Cauchy Integral Theorem & Multi-Pole Residue Theorem -/

/-- Counterclockwise rectangular boundary contour integral
`∮_{∂([σ₀, c] × [y₀, y₁])} f(s) ds = ∫_{σ₀}^c f(x + i y₀) dx - ∫_{σ₀}^c f(x + i y₁) dx
  + i ∫_{y₀}^{y₁} f(c + i y) dy - i ∫_{y₀}^{y₁} f(σ₀ + i y) dy`. -/
def rectBoundaryIntegral (f : ℂ → ℂ) (σ₀ c y₀ y₁ : ℝ) : ℂ :=
  ((∫ x in σ₀..c, f ((x : ℂ) + (y₀ : ℂ) * I)) -
   (∫ x in σ₀..c, f ((x : ℂ) + (y₁ : ℂ) * I))) +
  I * (∫ y in y₀..y₁, f ((c : ℂ) + (y : ℂ) * I)) -
  I * (∫ y in y₀..y₁, f ((σ₀ : ℂ) + (y : ℂ) * I))

/-- Closed rectangle `[σ₀, c] × [y₀, y₁]` in `ℂ`. -/
def closedRect (σ₀ c y₀ y₁ : ℝ) : Set ℂ :=
  Set.Icc σ₀ c ×ℂ Set.Icc y₀ y₁

/-- Open rectangle `(σ₀, c) × (y₀, y₁)` in `ℂ`. -/
def openRect (σ₀ c y₀ y₁ : ℝ) : Set ℂ :=
  Set.Ioo σ₀ c ×ℂ Set.Ioo y₀ y₁

/-- **Rectangular Cauchy Integral Theorem**: if `f` is complex-differentiable on the closed
rectangle `[σ₀, c] × [y₀, y₁]`, then `rectBoundaryIntegral f σ₀ c y₀ y₁ = 0`. -/
theorem rectBoundaryIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hσc : σ₀ ≤ c) (hy : y₀ ≤ y₁)
    (hf : DifferentiableOn ℂ f (closedRect σ₀ c y₀ y₁)) :
    rectBoundaryIntegral f σ₀ c y₀ y₁ = 0 := by
  set z : ℂ := (σ₀ : ℂ) + (y₀ : ℂ) * I
  set w : ℂ := (c : ℂ) + (y₁ : ℂ) * I
  have hzre : z.re = σ₀ := by simp [z]
  have hzim : z.im = y₀ := by simp [z]
  have hwre : w.re = c := by simp [w]
  have hwim : w.im = y₁ := by simp [w]
  have hrect : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im = closedRect σ₀ c y₀ y₁ := by
    rw [hzre, hwre, hzim, hwim, Set.uIcc_of_le hσc, Set.uIcc_of_le hy]
    rfl
  have h0 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w (hrect.symm ▸ hf)
  simpa only [rectBoundaryIntegral, hzre, hzim, hwre, hwim, smul_eq_mul] using h0

/-- Exact primitive evaluation `∫_a^b ((x - x₀) + i d)⁻¹ dx = (1/2) log(((b-x₀)²+d²)/((a-x₀)²+d²))
  - i (arctan((b-x₀)/d) - arctan((a-x₀)/d))` for any real `d ≠ 0`. -/
theorem integral_inv_sub_add_I_mul (a b x₀ : ℝ) {d : ℝ} (hd : d ≠ 0) :
    ∫ x in a..b, (((x - x₀ : ℝ) : ℂ) + (d : ℂ) * I)⁻¹ =
      (((1 / 2 : ℝ) * (Real.log ((b - x₀) ^ 2 + d ^ 2) - Real.log ((a - x₀) ^ 2 + d ^ 2)) : ℝ) : ℂ) -
      (((Real.arctan ((b - x₀) / d) - Real.arctan ((a - x₀) / d) : ℝ) : ℂ)) * I := by
  have hd2 : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  let F : ℝ → ℂ := fun x =>
    (((1 / 2 : ℝ) * Real.log ((x - x₀) ^ 2 + d ^ 2) : ℝ) : ℂ) -
    ((Real.arctan ((x - x₀) / d) : ℝ) : ℂ) * I
  have hderiv : ∀ x : ℝ, HasDerivAt F ((((x - x₀ : ℝ) : ℂ) + (d : ℂ) * I)⁻¹) x := by
    intro x
    have hpos : 0 < (x - x₀) ^ 2 + d ^ 2 := by positivity
    have h1 : HasDerivAt (fun t : ℝ => (t - x₀) ^ 2 + d ^ 2) (2 * (x - x₀)) x := by
      have ht : HasDerivAt (fun t : ℝ => t - x₀) 1 x := (hasDerivAt_id x).sub_const x₀
      have hsq : HasDerivAt (fun t : ℝ => (t - x₀) ^ 2) (2 * (x - x₀) ^ 1 * 1) x := ht.pow 2
      simpa using hsq.add_const (d ^ 2)
    have hlog : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log ((t - x₀) ^ 2 + d ^ 2))
        ((x - x₀) / ((x - x₀) ^ 2 + d ^ 2)) x := by
      have h := (h1.log hpos.ne').const_mul (1 / 2 : ℝ)
      refine h.congr_deriv ?_
      field_simp [hpos.ne']
    have harc : HasDerivAt (fun t : ℝ => Real.arctan ((t - x₀) / d))
        (d / ((x - x₀) ^ 2 + d ^ 2)) x := by
      have hlin : HasDerivAt (fun t : ℝ => (t - x₀) / d) (1 / d) x :=
        ((hasDerivAt_id x).sub_const x₀).div_const d
      have h := (Real.hasDerivAt_arctan ((x - x₀) / d)).comp x hlin
      refine h.congr_deriv ?_
      have hden : 1 + ((x - x₀) / d) ^ 2 = ((x - x₀) ^ 2 + d ^ 2) / d ^ 2 := by
        field_simp [hd]
        ring
      rw [hden]
      field_simp [hd, hpos.ne']
    have hC : HasDerivAt F
        ((((x - x₀) / ((x - x₀) ^ 2 + d ^ 2) : ℝ) : ℂ) -
          ((d / ((x - x₀) ^ 2 + d ^ 2) : ℝ) : ℂ) * I) x :=
      (hlog.ofReal_comp).sub ((harc.ofReal_comp).mul_const I)
    refine hC.congr_deriv ?_
    have hne : ((x - x₀ : ℝ) : ℂ) + (d : ℂ) * I ≠ 0 := by
      intro h0
      have him := congrArg Complex.im h0
      simp at him
      exact hd him
    refine eq_inv_of_mul_eq_one_left (G := ℂ) ?_
    push_cast
    calc ((((x - x₀ : ℂ) / ((x - x₀ : ℂ) ^ 2 + (d : ℂ) ^ 2)) -
            ((d : ℂ) / ((x - x₀ : ℂ) ^ 2 + (d : ℂ) ^ 2)) * I) *
            ((x - x₀ : ℂ) + (d : ℂ) * I))
        = (((x - x₀ : ℂ) - (d : ℂ) * I) * ((x - x₀ : ℂ) + (d : ℂ) * I)) /
            ((x - x₀ : ℂ) ^ 2 + (d : ℂ) ^ 2) := by ring
      _ = ((x - x₀ : ℂ) ^ 2 + (d : ℂ) ^ 2) / ((x - x₀ : ℂ) ^ 2 + (d : ℂ) ^ 2) := by
            congr 1
            have : I ^ 2 = -1 := Complex.I_sq
            linear_combination -((d : ℂ) ^ 2) * this
      _ = 1 := div_self (by exact_mod_cast hpos.ne' : ((x - x₀ : ℂ) ^ 2 + (d : ℂ) ^ 2) ≠ 0)
  have hcont : Continuous (fun x : ℝ => (((x - x₀ : ℝ) : ℂ) + (d : ℂ) * I)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun x h0 => ?_
    have him := congrArg Complex.im h0
    simp at him
    exact hd him
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hcont.intervalIntegrable a b)]
  dsimp only [F]
  push_cast
  ring

private lemma arctan_add_arctan_div_eq_pi_div_two {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.arctan (u / v) + Real.arctan (v / u) = Real.pi / 2 := by
  have hpos : 0 < u / v := div_pos hu hv
  have hinv : (u / v)⁻¹ = v / u := inv_div u v
  have h := Real.arctan_inv_of_pos hpos
  rw [hinv] at h
  linarith

/-- **Exact Single-Pole Rectangular Residue Formula**:
for any interior point `p ∈ (σ₀, c) × (y₀, y₁)`,
`rectBoundaryIntegral (fun s => (s - p)⁻¹) σ₀ c y₀ y₁ = 2 * π * I`. -/
theorem rectBoundaryIntegral_inv_sub_eq_two_pi_I {σ₀ c y₀ y₁ : ℝ} {p : ℂ}
    (hσ₀ : σ₀ < p.re) (hc : p.re < c) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁) :
    rectBoundaryIntegral (fun s => (s - p)⁻¹) σ₀ c y₀ y₁ = 2 * (Real.pi : ℂ) * I := by
  set a : ℝ := p.re
  set b : ℝ := p.im
  set r : ℝ := c - a
  set l : ℝ := a - σ₀
  set u : ℝ := y₁ - b
  set d : ℝ := b - y₀
  have hr : 0 < r := sub_pos.mpr hc
  have hl : 0 < l := sub_pos.mpr hσ₀
  have hu : 0 < u := sub_pos.mpr hy₁
  have hd : 0 < d := sub_pos.mpr hy₀
  have hp_eq : p = (a : ℂ) + (b : ℂ) * I := (Complex.re_add_im p).symm
  -- Rewrite each of the four edge integrals in the standard form of `integral_inv_sub_add_I_mul`
  have hbot_eq : (fun x : ℝ => (((x : ℂ) + (y₀ : ℂ) * I) - p)⁻¹) =
      fun x : ℝ => (((x - a : ℝ) : ℂ) + ((-d : ℝ) : ℂ) * I)⁻¹ := by
    funext x; rw [hp_eq]; push_cast [d]; ring_nf
  have htop_eq : (fun x : ℝ => (((x : ℂ) + (y₁ : ℂ) * I) - p)⁻¹) =
      fun x : ℝ => (((x - a : ℝ) : ℂ) + (u : ℂ) * I)⁻¹ := by
    funext x; rw [hp_eq]; push_cast [u]; ring_nf
  have hright_eq : ∀ y : ℝ,
      I * ((((c : ℂ) + (y : ℂ) * I) - p)⁻¹) = (((y - b : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹ := by
    intro y
    have h1 : (((c : ℂ) + (y : ℂ) * I) - p) = I * (((y - b : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I) := by
      rw [hp_eq]; push_cast [r]
      have hI2 : I ^ 2 = -1 := Complex.I_sq
      linear_combination (c - a : ℂ) * hI2
    rw [h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  have hleft_eq : ∀ y : ℝ,
      I * ((((σ₀ : ℂ) + (y : ℂ) * I) - p)⁻¹) = (((y - b : ℝ) : ℂ) + (l : ℂ) * I)⁻¹ := by
    intro y
    have h1 : (((σ₀ : ℂ) + (y : ℂ) * I) - p) = I * (((y - b : ℝ) : ℂ) + (l : ℂ) * I) := by
      rw [hp_eq]; push_cast [l]
      have hI2 : I ^ 2 = -1 := Complex.I_sq
      linear_combination -(a - σ₀ : ℂ) * hI2
    rw [h1, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
  unfold rectBoundaryIntegral
  rw [hbot_eq, htop_eq, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  have hR_int : ∫ y in y₀..y₁, I * (((c : ℂ) + (y : ℂ) * I) - p)⁻¹ =
      ∫ y in y₀..y₁, (((y - b : ℝ) : ℂ) + ((-r : ℝ) : ℂ) * I)⁻¹ :=
    intervalIntegral.integral_congr fun y _ => hright_eq y
  have hL_int : ∫ y in y₀..y₁, I * (((σ₀ : ℂ) + (y : ℂ) * I) - p)⁻¹ =
      ∫ y in y₀..y₁, (((y - b : ℝ) : ℂ) + (l : ℂ) * I)⁻¹ :=
    intervalIntegral.integral_congr fun y _ => hleft_eq y
  rw [hR_int, hL_int]
  rw [integral_inv_sub_add_I_mul σ₀ c a (neg_ne_zero.mpr hd.ne'),
      integral_inv_sub_add_I_mul σ₀ c a hu.ne',
      integral_inv_sub_add_I_mul y₀ y₁ b (neg_ne_zero.mpr hr.ne'),
      integral_inv_sub_add_I_mul y₀ y₁ b hl.ne']
  have hca : c - a = r := rfl
  have hσa : σ₀ - a = -l := by dsimp only [l]; ring
  have hy1b : y₁ - b = u := rfl
  have hy0b : y₀ - b = -d := by dsimp only [d]; ring
  rw [hca, hσa, hy1b, hy0b]
  simp only [neg_sq, div_neg, neg_div, neg_neg, Real.arctan_neg]
  have h1 := arctan_add_arctan_div_eq_pi_div_two hr hd
  have h2 := arctan_add_arctan_div_eq_pi_div_two hl hd
  have h3 := arctan_add_arctan_div_eq_pi_div_two hr hu
  have h4 := arctan_add_arctan_div_eq_pi_div_two hl hu
  have hlog_ru : u ^ 2 + r ^ 2 = r ^ 2 + u ^ 2 := add_comm _ _
  have hlog_rd : d ^ 2 + r ^ 2 = r ^ 2 + d ^ 2 := add_comm _ _
  have hlog_lu : u ^ 2 + l ^ 2 = l ^ 2 + u ^ 2 := add_comm _ _
  have hlog_ld : d ^ 2 + l ^ 2 = l ^ 2 + d ^ 2 := add_comm _ _
  rw [hlog_ru, hlog_rd, hlog_lu, hlog_ld]
  have hsum_arc :
      (Real.arctan (r / d) + Real.arctan (l / d)) +
      (Real.arctan (r / u) + Real.arctan (l / u)) +
      (Real.arctan (u / r) + Real.arctan (d / r)) +
      (Real.arctan (u / l) + Real.arctan (d / l)) = 2 * Real.pi := by
    linarith
  have hsum_arcC :
      ((Real.arctan (r / d) + Real.arctan (l / d) : ℝ) : ℂ) +
      ((Real.arctan (r / u) + Real.arctan (l / u) : ℝ) : ℂ) +
      ((Real.arctan (u / r) + Real.arctan (d / r) : ℝ) : ℂ) +
      ((Real.arctan (u / l) + Real.arctan (d / l) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    exact_mod_cast hsum_arc
  push_cast at hsum_arcC ⊢
  linear_combination hsum_arcC * I

/-- Boundary integrability predicate for `rectBoundaryIntegral`: `f` is interval-integrable on all
four edges of `[σ₀, c] × [y₀, y₁]`. -/
def RectBoundaryIntegrable (f : ℂ → ℂ) (σ₀ c y₀ y₁ : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y₀ : ℂ) * I)) volume σ₀ c ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y₁ : ℂ) * I)) volume σ₀ c ∧
  IntervalIntegrable (fun y : ℝ => f ((c : ℂ) + (y : ℂ) * I)) volume y₀ y₁ ∧
  IntervalIntegrable (fun y : ℝ => f ((σ₀ : ℂ) + (y : ℂ) * I)) volume y₀ y₁

theorem rectBoundaryIntegrable_of_continuousOn {f : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hσc : σ₀ ≤ c) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (closedRect σ₀ c y₀ y₁)) :
    RectBoundaryIntegrable f σ₀ c y₀ y₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (hf.comp (by fun_prop) fun x hx => ?_).intervalIntegrable
    rw [Set.uIcc_of_le hσc] at hx
    exact ⟨by simpa using hx, by simp [hy]⟩
  · refine (hf.comp (by fun_prop) fun x hx => ?_).intervalIntegrable
    rw [Set.uIcc_of_le hσc] at hx
    exact ⟨by simpa using hx, by simp [hy]⟩
  · refine (hf.comp (by fun_prop) fun y hy' => ?_).intervalIntegrable
    rw [Set.uIcc_of_le hy] at hy'
    exact ⟨by simp [hσc], by simpa using hy'⟩
  · refine (hf.comp (by fun_prop) fun y hy' => ?_).intervalIntegrable
    rw [Set.uIcc_of_le hy] at hy'
    exact ⟨by simp [hσc], by simpa using hy'⟩

theorem rectBoundaryIntegrable_const_mul {f : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ} (a : ℂ)
    (hf : RectBoundaryIntegrable f σ₀ c y₀ y₁) :
    RectBoundaryIntegrable (fun s => a * f s) σ₀ c y₀ y₁ :=
  ⟨hf.1.const_mul a, hf.2.1.const_mul a, hf.2.2.1.const_mul a, hf.2.2.2.const_mul a⟩

theorem rectBoundaryIntegrable_add {f g : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hf : RectBoundaryIntegrable f σ₀ c y₀ y₁) (hg : RectBoundaryIntegrable g σ₀ c y₀ y₁) :
    RectBoundaryIntegrable (fun s => f s + g s) σ₀ c y₀ y₁ :=
  ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

theorem rectBoundaryIntegrable_inv_sub {σ₀ c y₀ y₁ : ℝ} {p : ℂ}
    (hσ₀ : σ₀ < p.re) (hc : p.re < c) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁) :
    RectBoundaryIntegrable (fun s => (s - p)⁻¹) σ₀ c y₀ y₁ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (Continuous.inv₀ (by fun_prop) fun x h0 => ?_).intervalIntegrable _ _
    have := congrArg Complex.im h0; simp at this; linarith
  · refine (Continuous.inv₀ (by fun_prop) fun x h0 => ?_).intervalIntegrable _ _
    have := congrArg Complex.im h0; simp at this; linarith
  · refine (Continuous.inv₀ (by fun_prop) fun y h0 => ?_).intervalIntegrable _ _
    have := congrArg Complex.re h0; simp at this; linarith
  · refine (Continuous.inv₀ (by fun_prop) fun y h0 => ?_).intervalIntegrable _ _
    have := congrArg Complex.re h0; simp at this; linarith

theorem rectBoundaryIntegral_const_mul (f : ℂ → ℂ) (a : ℂ) (σ₀ c y₀ y₁ : ℝ) :
    rectBoundaryIntegral (fun s => a * f s) σ₀ c y₀ y₁ =
      a * rectBoundaryIntegral f σ₀ c y₀ y₁ := by
  unfold rectBoundaryIntegral
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem rectBoundaryIntegral_add {f g : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hf : RectBoundaryIntegrable f σ₀ c y₀ y₁) (hg : RectBoundaryIntegrable g σ₀ c y₀ y₁) :
    rectBoundaryIntegral (fun s => f s + g s) σ₀ c y₀ y₁ =
      rectBoundaryIntegral f σ₀ c y₀ y₁ + rectBoundaryIntegral g σ₀ c y₀ y₁ := by
  unfold rectBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
      intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
      intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

private lemma intervalIntegrable_finset_sum_apply {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι → ℝ → E) {a b : ℝ}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hfun : (fun x => ∑ k ∈ insert i s, f k x) = fun x => f i x + ∑ k ∈ s, f k x := by
      funext x; exact Finset.sum_insert hi
    rw [hfun]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem rectBoundaryIntegral_finset_sum {ι : Type*} (J : Finset ι) (f : ι → ℂ → ℂ)
    {σ₀ c y₀ y₁ : ℝ} (hf : ∀ j ∈ J, RectBoundaryIntegrable (f j) σ₀ c y₀ y₁) :
    rectBoundaryIntegral (fun s => ∑ j ∈ J, f j s) σ₀ c y₀ y₁ =
      ∑ j ∈ J, rectBoundaryIntegral (f j) σ₀ c y₀ y₁ := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [rectBoundaryIntegral]
  | insert j s hj ih =>
    have hfj : RectBoundaryIntegrable (f j) σ₀ c y₀ y₁ := hf j (Finset.mem_insert_self j s)
    have hfs : ∀ k ∈ s, RectBoundaryIntegrable (f k) σ₀ c y₀ y₁ :=
      fun k hk => hf k (Finset.mem_insert_of_mem hk)
    have hsum_int : RectBoundaryIntegrable (fun z => ∑ k ∈ s, f k z) σ₀ c y₀ y₁ :=
      ⟨intervalIntegrable_finset_sum_apply s (fun k x => f k ((x : ℂ) + (y₀ : ℂ) * I))
          (fun k hk => (hfs k hk).1),
       intervalIntegrable_finset_sum_apply s (fun k x => f k ((x : ℂ) + (y₁ : ℂ) * I))
          (fun k hk => (hfs k hk).2.1),
       intervalIntegrable_finset_sum_apply s (fun k y => f k ((c : ℂ) + (y : ℂ) * I))
          (fun k hk => (hfs k hk).2.2.1),
       intervalIntegrable_finset_sum_apply s (fun k y => f k ((σ₀ : ℂ) + (y : ℂ) * I))
          (fun k hk => (hfs k hk).2.2.2)⟩
    have hfun : (fun z => ∑ k ∈ insert j s, f k z) = fun z => f j z + ∑ k ∈ s, f k z := by
      funext z; exact Finset.sum_insert hj
    rw [hfun, rectBoundaryIntegral_add hfj hsum_int, ih hfs, Finset.sum_insert hj]

theorem rectBoundaryIntegral_congr_boundary {f g : ℂ → ℂ} {σ₀ c y₀ y₁ : ℝ}
    (hbot : ∀ x ∈ Set.uIcc σ₀ c, f ((x : ℂ) + (y₀ : ℂ) * I) = g ((x : ℂ) + (y₀ : ℂ) * I))
    (htop : ∀ x ∈ Set.uIcc σ₀ c, f ((x : ℂ) + (y₁ : ℂ) * I) = g ((x : ℂ) + (y₁ : ℂ) * I))
    (hright : ∀ y ∈ Set.uIcc y₀ y₁, f ((c : ℂ) + (y : ℂ) * I) = g ((c : ℂ) + (y : ℂ) * I))
    (hleft : ∀ y ∈ Set.uIcc y₀ y₁, f ((σ₀ : ℂ) + (y : ℂ) * I) = g ((σ₀ : ℂ) + (y : ℂ) * I)) :
    rectBoundaryIntegral f σ₀ c y₀ y₁ = rectBoundaryIntegral g σ₀ c y₀ y₁ := by
  unfold rectBoundaryIntegral
  rw [intervalIntegral.integral_congr hbot, intervalIntegral.integral_congr htop,
      intervalIntegral.integral_congr hright, intervalIntegral.integral_congr hleft]

/-- Exact rectangular boundary integral of a finite principal-part sum `∑_{j ∈ J} r_j / (s - p_j)`
with all poles `p_j` in the open interior `(σ₀, c) × (y₀, y₁)`. -/
theorem rectBoundaryIntegral_principalPart_sum {ι : Type*} (J : Finset ι)
    (p r : ι → ℂ) {σ₀ c y₀ y₁ : ℝ}
    (hp : ∀ j ∈ J, p j ∈ openRect σ₀ c y₀ y₁) :
    rectBoundaryIntegral (fun s => ∑ j ∈ J, r j / (s - p j)) σ₀ c y₀ y₁ =
      2 * (Real.pi : ℂ) * I * ∑ j ∈ J, r j := by
  have hint : ∀ j ∈ J, RectBoundaryIntegrable (fun s => r j / (s - p j)) σ₀ c y₀ y₁ := by
    intro j hj
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp j hj
    simpa only [div_eq_mul_inv] using
      rectBoundaryIntegrable_const_mul (r j) (rectBoundaryIntegrable_inv_sub h1 h2 h3 h4)
  rw [rectBoundaryIntegral_finset_sum J (fun j s => r j / (s - p j)) hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp j hj
  have hdiv : (fun s => r j / (s - p j)) = fun s => r j * (s - p j)⁻¹ := by
    funext s; rw [div_eq_mul_inv]
  rw [hdiv, rectBoundaryIntegral_const_mul, rectBoundaryIntegral_inv_sub_eq_two_pi_I h1 h2 h3 h4]
  ring

/-- **Exact Rectangular Multi-Pole Residue Theorem** (boundary-agreement form):
if `G` is holomorphic on the closed rectangle `[σ₀, c] × [y₀, y₁]`, all poles `p j` (`j ∈ J`) lie
strictly in the open interior `(σ₀, c) × (y₀, y₁)`, and `F s = G s + ∑ j ∈ J, r j / (s - p j)` on
the complement of the poles (in particular, on all four boundary edges), then
`rectBoundaryIntegral F σ₀ c y₀ y₁ = 2 π i * ∑ j ∈ J, r j`. -/
theorem rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part {ι : Type*}
    (F G : ℂ → ℂ) {σ₀ c y₀ y₁ : ℝ} (hσc : σ₀ < c) (hy : y₀ < y₁)
    (J : Finset ι) (p r : ι → ℂ)
    (hp : ∀ j ∈ J, p j ∈ openRect σ₀ c y₀ y₁)
    (hG : DifferentiableOn ℂ G (closedRect σ₀ c y₀ y₁))
    (hbdry : ∀ s ∈ closedRect σ₀ c y₀ y₁, (∀ j ∈ J, s ≠ p j) →
      F s = G s + ∑ j ∈ J, r j / (s - p j)) :
    rectBoundaryIntegral F σ₀ c y₀ y₁ = 2 * (Real.pi : ℂ) * I * ∑ j ∈ J, r j := by
  have hcongr : rectBoundaryIntegral F σ₀ c y₀ y₁ =
      rectBoundaryIntegral (fun s => G s + ∑ j ∈ J, r j / (s - p j)) σ₀ c y₀ y₁ := by
    refine rectBoundaryIntegral_congr_boundary ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.uIcc_of_le hσc.le] at hx
      refine hbdry _ ⟨by simpa using hx, by simp [hy.le]⟩ fun j hj hEq => ?_
      have := congrArg Complex.im hEq; simp at this; linarith [(hp j hj).2.1]
    · intro x hx
      rw [Set.uIcc_of_le hσc.le] at hx
      refine hbdry _ ⟨by simpa using hx, by simp [hy.le]⟩ fun j hj hEq => ?_
      have := congrArg Complex.im hEq; simp at this; linarith [(hp j hj).2.2]
    · intro y hy'
      rw [Set.uIcc_of_le hy.le] at hy'
      refine hbdry _ ⟨by simp [hσc.le], by simpa using hy'⟩ fun j hj hEq => ?_
      have := congrArg Complex.re hEq; simp at this; linarith [(hp j hj).1.2]
    · intro y hy'
      rw [Set.uIcc_of_le hy.le] at hy'
      refine hbdry _ ⟨by simp [hσc.le], by simpa using hy'⟩ fun j hj hEq => ?_
      have := congrArg Complex.re hEq; simp at this; linarith [(hp j hj).1.1]
  have hG_int : RectBoundaryIntegrable G σ₀ c y₀ y₁ :=
    rectBoundaryIntegrable_of_continuousOn hσc.le hy.le hG.continuousOn
  have hP_int : RectBoundaryIntegrable (fun s => ∑ j ∈ J, r j / (s - p j)) σ₀ c y₀ y₁ := by
    have hterm : ∀ j ∈ J, RectBoundaryIntegrable (fun s => r j / (s - p j)) σ₀ c y₀ y₁ := by
      intro j hj
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp j hj
      simpa only [div_eq_mul_inv] using
        rectBoundaryIntegrable_const_mul (r j) (rectBoundaryIntegrable_inv_sub h1 h2 h3 h4)
    exact ⟨intervalIntegrable_finset_sum_apply J (fun j x => r j / (((x : ℂ) + (y₀ : ℂ) * I) - p j))
             (fun j hj => (hterm j hj).1),
           intervalIntegrable_finset_sum_apply J (fun j x => r j / (((x : ℂ) + (y₁ : ℂ) * I) - p j))
             (fun j hj => (hterm j hj).2.1),
           intervalIntegrable_finset_sum_apply J (fun j y => r j / (((c : ℂ) + (y : ℂ) * I) - p j))
             (fun j hj => (hterm j hj).2.2.1),
           intervalIntegrable_finset_sum_apply J (fun j y => r j / (((σ₀ : ℂ) + (y : ℂ) * I) - p j))
             (fun j hj => (hterm j hj).2.2.2)⟩
  rw [hcongr, rectBoundaryIntegral_add hG_int hP_int,
      rectBoundaryIntegral_eq_zero_of_differentiableOn hσc.le hy.le hG, zero_add,
      rectBoundaryIntegral_principalPart_sum J p r hp]

/-- **Exact Rectangular Multi-Pole Residue Theorem** (principal-part form):
if `F(s) - ∑_{j ∈ J} r_j / (s - p_j)` is holomorphic on `[σ₀, c] × [y₀, y₁]` and every `p_j` lies
in `(σ₀, c) × (y₀, y₁)`, then `rectBoundaryIntegral F σ₀ c y₀ y₁ = 2 π i * ∑_{j ∈ J} r_j`. -/
theorem rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues {ι : Type*}
    (F : ℂ → ℂ) {σ₀ c y₀ y₁ : ℝ} (hσc : σ₀ < c) (hy : y₀ < y₁)
    (J : Finset ι) (p r : ι → ℂ)
    (hp : ∀ j ∈ J, p j ∈ openRect σ₀ c y₀ y₁)
    (hdiff : DifferentiableOn ℂ (fun s => F s - ∑ j ∈ J, r j / (s - p j))
      (closedRect σ₀ c y₀ y₁)) :
    rectBoundaryIntegral F σ₀ c y₀ y₁ = 2 * (Real.pi : ℂ) * I * ∑ j ∈ J, r j :=
  rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part F
    (fun s => F s - ∑ j ∈ J, r j / (s - p j)) hσc hy J p r hp hdiff (fun s _ _ => by ring)

/-- Algebraic rearrangement of `rectBoundaryIntegral F σ₀ c (-T) T = 2πi * R` into the exact
vertical contour-shift identity on `[σ₀, c] × [-T, T]`. -/
theorem vertical_contour_shift_of_rectBoundaryIntegral {F : ℂ → ℂ} {σ₀ c T : ℝ} {R : ℂ}
    (hrect : rectBoundaryIntegral F σ₀ c (-T) T = 2 * (Real.pi : ℂ) * I * R) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + I * (t : ℂ))) =
      R +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ₀ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in σ₀..c, F ((σ : ℂ) + I * (T : ℂ))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in σ₀..c, F ((σ : ℂ) - I * (T : ℂ))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2piI : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero
  unfold rectBoundaryIntegral at hrect
  have hR_comm : ∫ y in (-T)..T, F ((c : ℂ) + (y : ℂ) * I) =
      ∫ t in (-T)..T, F ((c : ℂ) + I * (t : ℂ)) :=
    intervalIntegral.integral_congr fun t _ => by rw [mul_comm I (t : ℂ)]
  have hL_comm : ∫ y in (-T)..T, F ((σ₀ : ℂ) + (y : ℂ) * I) =
      ∫ t in (-T)..T, F ((σ₀ : ℂ) + I * (t : ℂ)) :=
    intervalIntegral.integral_congr fun t _ => by rw [mul_comm I (t : ℂ)]
  have hTop_comm : ∫ x in σ₀..c, F ((x : ℂ) + (T : ℂ) * I) =
      ∫ σ in σ₀..c, F ((σ : ℂ) + I * (T : ℂ)) :=
    intervalIntegral.integral_congr fun σ _ => by rw [mul_comm I (T : ℂ)]
  have hBot_comm : ∫ x in σ₀..c, F ((x : ℂ) + ((-T : ℝ) : ℂ) * I) =
      ∫ σ in σ₀..c, F ((σ : ℂ) - I * (T : ℂ)) :=
    intervalIntegral.integral_congr fun σ _ => by push_cast; ring_nf
  rw [hR_comm, hL_comm, hTop_comm, hBot_comm] at hrect
  have hmul := congrArg ((2 * (Real.pi : ℂ) * I)⁻¹ * ·) hrect
  have hcast : ((2 * Real.pi : ℝ) : ℂ)⁻¹ = (2 * (Real.pi : ℂ))⁻¹ := by push_cast; rfl
  rw [hcast]
  have hI_cancel : (2 * (Real.pi : ℂ) * I)⁻¹ * I = (2 * (Real.pi : ℂ))⁻¹ := by
    field_simp [hpi, I_ne_zero]
  have hRHS : (2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (Real.pi : ℂ) * I * R) = R := by
    rw [← mul_assoc, inv_mul_cancel₀ h2piI, one_mul]
  rw [hRHS, mul_sub, mul_add, mul_sub, ← mul_assoc, ← mul_assoc, hI_cancel] at hmul
  linear_combination hmul

/-- **Exact Vertical Contour-Shift Identity on `[σ₀, c] × [-T, T]`**:
if `F(s) - ∑_{j ∈ J} r_j / (s - p_j)` is holomorphic on `[σ₀, c] × [-T, T]` and all `p_j` lie in
`(σ₀, c) × (-T, T)`, then
`(1 / (2π)) ∫_{-T}^T F(c + i t) dt = ∑_{j ∈ J} r_j + (1 / (2π)) ∫_{-T}^T F(σ₀ + i t) dt
  + (1 / (2πi)) ∫_{σ₀}^c F(σ + i T) dσ - (1 / (2πi)) ∫_{σ₀}^c F(σ - i T) dσ`. -/
theorem vertical_contour_shift_eq_sum_residues {ι : Type*}
    (F : ℂ → ℂ) {σ₀ c T : ℝ} (hσc : σ₀ < c) (hT : 0 < T)
    (J : Finset ι) (p r : ι → ℂ)
    (hp : ∀ j ∈ J, p j ∈ openRect σ₀ c (-T) T)
    (hdiff : DifferentiableOn ℂ (fun s => F s - ∑ j ∈ J, r j / (s - p j))
      (closedRect σ₀ c (-T) T)) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((c : ℂ) + I * (t : ℂ))) =
      (∑ j ∈ J, r j) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((σ₀ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in σ₀..c, F ((σ : ℂ) + I * (T : ℂ))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in σ₀..c, F ((σ : ℂ) - I * (T : ℂ))) :=
  vertical_contour_shift_of_rectBoundaryIntegral
    (rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues F hσc (by linarith) J p r hp hdiff)

private lemma closedRect_mem_nhds_of_mem_openRect {σ₀ c y₀ y₁ : ℝ} {p : ℂ}
    (hp : p ∈ openRect σ₀ c y₀ y₁) : closedRect σ₀ c y₀ y₁ ∈ 𝓝 p := by
  have hopen : IsOpen (openRect σ₀ c y₀ y₁) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hsub : openRect σ₀ c y₀ y₁ ⊆ closedRect σ₀ c y₀ y₁ := fun _ ⟨h1, h2⟩ =>
    ⟨Set.Ioo_subset_Icc_self h1, Set.Ioo_subset_Icc_self h2⟩
  exact Filter.mem_of_superset (hopen.mem_nhds hp) hsub

/-- **Multiplicative Vertical Contour-Shift Identity (`L(s) * W(s)`)**:
if `L(s) - ∑_{j ∈ J} a_j / (s - p_j)` and the weight `W(s)` are both holomorphic on
`[σ₀, c] × [-T, T]` with all poles `p_j` in `(σ₀, c) × (-T, T)`, then the vertical contour shift of
`F(s) = L(s) * W(s)` picks up exact residues `∑_{j ∈ J} a_j * W(p_j)`. -/
theorem vertical_contour_shift_mul_eq_sum_residues {ι : Type*}
    (L W : ℂ → ℂ) {σ₀ c T : ℝ} (hσc : σ₀ < c) (hT : 0 < T)
    (J : Finset ι) (p a : ι → ℂ)
    (hp : ∀ j ∈ J, p j ∈ openRect σ₀ c (-T) T)
    (hL : DifferentiableOn ℂ (fun s => L s - ∑ j ∈ J, a j / (s - p j))
      (closedRect σ₀ c (-T) T))
    (hW : DifferentiableOn ℂ W (closedRect σ₀ c (-T) T)) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, L ((c : ℂ) + I * (t : ℂ)) * W ((c : ℂ) + I * (t : ℂ))) =
      (∑ j ∈ J, a j * W (p j)) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, L ((σ₀ : ℂ) + I * (t : ℂ)) * W ((σ₀ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in σ₀..c, L ((σ : ℂ) + I * (T : ℂ)) * W ((σ : ℂ) + I * (T : ℂ))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in σ₀..c, L ((σ : ℂ) - I * (T : ℂ)) * W ((σ : ℂ) - I * (T : ℂ))) := by
  let G : ℂ → ℂ := fun s =>
    (L s - ∑ j ∈ J, a j / (s - p j)) * W s + ∑ j ∈ J, a j * dslope W (p j) s
  have hG_diff : DifferentiableOn ℂ G (closedRect σ₀ c (-T) T) := by
    refine (hL.mul hW).add (DifferentiableOn.fun_sum fun j hj => ?_)
    have hds : DifferentiableOn ℂ (dslope W (p j)) (closedRect σ₀ c (-T) T) :=
      (Complex.differentiableOn_dslope (closedRect_mem_nhds_of_mem_openRect (hp j hj))).mpr hW
    exact (differentiableOn_const (a j)).mul hds
  have hbdry : ∀ s ∈ closedRect σ₀ c (-T) T, (∀ j ∈ J, s ≠ p j) →
      L s * W s = G s + ∑ j ∈ J, (a j * W (p j)) / (s - p j) := by
    intro s _ hs
    dsimp only [G]
    have hsum_eq : ∑ j ∈ J, a j * dslope W (p j) s + ∑ j ∈ J, (a j * W (p j)) / (s - p j) =
        (∑ j ∈ J, a j / (s - p j)) * W s := by
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : s ≠ p j := hs j hj
      have hsub : s - p j ≠ 0 := sub_ne_zero.mpr hne
      rw [dslope_of_ne W hne, slope_def_field]
      field_simp [hsub]
      ring
    linear_combination -hsum_eq
  exact vertical_contour_shift_of_rectBoundaryIntegral
    (rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part (fun s => L s * W s) G
      hσc (by linarith) J p (fun j => a j * W (p j)) hp hG_diff hbdry)

/-- **Vertical Contour-Shift Identity for `L(s) * x^s / s` with Simple Pole at `s = 0`**:
on `[σ₀, c] × [-T, T]` with `σ₀ < 0 < c`, `0 < T`, `x > 0`, if `L(s) - ∑_{j ∈ J} a_j / (s - p_j)`
is holomorphic on `[σ₀, c] × [-T, T]` with all poles `p_j ∈ (σ₀, c) × (-T, T)` and `p_j ≠ 0`, then
the contour shift of `L(s) * x^s / s` yields exact residues `L(0) + ∑_{j ∈ J} a_j * x^{p_j} / p_j`. -/
theorem vertical_contour_shift_div_id_eq_sum_residues {ι : Type*}
    (L : ℂ → ℂ) {x σ₀ c T : ℝ} (hx : 0 < x) (hσ₀ : σ₀ < 0) (hc : 0 < c) (hT : 0 < T)
    (J : Finset ι) (p a : ι → ℂ)
    (hp : ∀ j ∈ J, p j ∈ openRect σ₀ c (-T) T)
    (hp0 : ∀ j ∈ J, p j ≠ 0)
    (hL : DifferentiableOn ℂ (fun s => L s - ∑ j ∈ J, a j / (s - p j))
      (closedRect σ₀ c (-T) T)) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, L ((c : ℂ) + I * (t : ℂ)) * (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) =
      (L 0 + ∑ j ∈ J, a j * (x : ℂ) ^ (p j) / p j) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, L ((σ₀ : ℂ) + I * (t : ℂ)) * (x : ℂ) ^ ((σ₀ : ℂ) + I * (t : ℂ)) / ((σ₀ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, L ((σ : ℂ) + I * (T : ℂ)) * (x : ℂ) ^ ((σ : ℂ) + I * (T : ℂ)) / ((σ : ℂ) + I * (T : ℂ))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, L ((σ : ℂ) - I * (T : ℂ)) * (x : ℂ) ^ ((σ : ℂ) - I * (T : ℂ)) / ((σ : ℂ) - I * (T : ℂ))) := by
  classical
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  let E : ℂ → ℂ := fun s => (x : ℂ) ^ s
  have hE_diff : DifferentiableOn ℂ E (closedRect σ₀ c (-T) T) := by
    have hEq : E = fun s => cexp (Complex.log (x : ℂ) * s) :=
      funext fun s => Complex.cpow_def_of_ne_zero hxC s
    rw [hEq]
    exact ((differentiable_const _).mul differentiable_id).cexp.differentiableOn
  let H : ℂ → ℂ := fun s => L s - ∑ j ∈ J, a j / (s - p j)
  have h0_mem : (0 : ℂ) ∈ openRect σ₀ c (-T) T := ⟨by simp [hσ₀, hc], by simp [hT]⟩
  have hH_dslope : DifferentiableOn ℂ (dslope H 0) (closedRect σ₀ c (-T) T) :=
    (Complex.differentiableOn_dslope (closedRect_mem_nhds_of_mem_openRect h0_mem)).mpr hL
  have hE_dslope0 : DifferentiableOn ℂ (dslope E 0) (closedRect σ₀ c (-T) T) :=
    (Complex.differentiableOn_dslope (closedRect_mem_nhds_of_mem_openRect h0_mem)).mpr hE_diff
  let G : ℂ → ℂ := fun s =>
    H s * dslope E 0 s + dslope H 0 s +
    ∑ j ∈ J, (a j / p j) * (dslope E (p j) s - dslope E 0 s)
  have hG_diff : DifferentiableOn ℂ G (closedRect σ₀ c (-T) T) := by
    refine ((hL.mul hE_dslope0).add hH_dslope).add (DifferentiableOn.fun_sum fun j hj => ?_)
    have hEj : DifferentiableOn ℂ (dslope E (p j)) (closedRect σ₀ c (-T) T) :=
      (Complex.differentiableOn_dslope (closedRect_mem_nhds_of_mem_openRect (hp j hj))).mpr hE_diff
    exact (differentiableOn_const _).mul (hEj.sub hE_dslope0)
  -- Index set `Option ι`: `none` for `s = 0` (residue `L 0`), `some j` for `s = p j` (residue `a j * x^{p j} / p j`)
  let J' : Finset (Option ι) := insert none (J.image some)
  let p' : Option ι → ℂ := fun o => o.elim 0 p
  let r' : Option ι → ℂ := fun o => o.elim (L 0) (fun j => a j * E (p j) / p j)
  have hp' : ∀ o ∈ J', p' o ∈ openRect σ₀ c (-T) T := by
    intro o ho
    rcases Finset.mem_insert.mp ho with rfl | ho'
    · exact h0_mem
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ho'
      exact hp j hj
  have hsum_r' : ∑ o ∈ J', r' o = L 0 + ∑ j ∈ J, a j * E (p j) / p j := by
    have hnone : none ∉ J.image some := by simp
    rw [Finset.sum_insert hnone, Finset.sum_image (by intro _ _ _ _ h; exact Option.some.inj h)]
    rfl
  have hbdry : ∀ s ∈ closedRect σ₀ c (-T) T, (∀ o ∈ J', s ≠ p' o) →
      L s * E s / s = G s + ∑ o ∈ J', r' o / (s - p' o) := by
    intro s _ hs
    have hs0 : s ≠ 0 := hs none (Finset.mem_insert_self _ _)
    have hsp : ∀ j ∈ J, s ≠ p j := fun j hj =>
      hs (some j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hj))
    have hnone : none ∉ J.image some := by simp
    rw [Finset.sum_insert hnone, Finset.sum_image (by intro _ _ _ _ h; exact Option.some.inj h)]
    dsimp only [G, p', r', Option.elim]
    rw [dslope_of_ne E hs0, dslope_of_ne H hs0, slope_def_field, slope_def_field]
    simp only [sub_zero]
    have hE0 : E 0 = 1 := Complex.cpow_zero (x : ℂ)
    rw [hE0]
    have hH0 : L 0 = H 0 - ∑ j ∈ J, a j / p j := by
      dsimp only [H]
      have hneg : ∑ j ∈ J, a j / (0 - p j) = -(∑ j ∈ J, a j / p j) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by simp [div_neg]
      rw [hneg]; ring
    have hL_eq : L s = H s + ∑ j ∈ J, a j / (s - p j) := by dsimp only [H]; ring
    have hsum_part :
        ∑ j ∈ J, (a j / p j) * (dslope E (p j) s - (E s - 1) / s) +
          ∑ j ∈ J, a j * E (p j) / p j / (s - p j) - (∑ j ∈ J, a j / p j) / s =
        (∑ j ∈ J, a j / (s - p j)) * E s / s := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
          Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne : s ≠ p j := hsp j hj
      have hsub : s - p j ≠ 0 := sub_ne_zero.mpr hne
      have hpj0 : p j ≠ 0 := hp0 j hj
      rw [dslope_of_ne E hne, slope_def_field]
      field_simp [hs0, hsub, hpj0]
      ring
    rw [hL_eq, add_mul, add_div, hH0, sub_div (H 0)]
    have hH_part : H s * ((E s - 1) / s) + (H s - H 0) / s + H 0 / s = H s * E s / s := by
      field_simp [hs0]
      ring
    linear_combination -hH_part - hsum_part
  have hrect := rectBoundaryIntegral_eq_two_pi_I_mul_sum_residues_of_holo_part
    (fun s => L s * E s / s) G (by linarith) (by linarith) J' p' r' hp' hG_diff hbdry
  rw [hsum_r'] at hrect
  exact vertical_contour_shift_of_rectBoundaryIntegral hrect

/-! ## Section 2: Pigeonhole Good-Horizontal-Line Selection & Quantitative Contour Bounds -/

/-- **Classical Pigeonhole Zero-Spacing Lemma**:
given any real `T`, any finite set `S : Finset ℝ` of ordinates with `S.card ≤ N`, there exists
`T_* ∈ [T, T + 1]` whose distance to every `γ ∈ S` is at least `1 / (2 * (N + 1))`. -/
theorem exists_good_height_pigeonhole (T : ℝ) (S : Finset ℝ) {N : ℕ} (hcard : S.card ≤ N) :
    ∃ T_star ∈ Set.Icc T (T + 1), ∀ γ ∈ S, 1 / (2 * ((N : ℝ) + 1)) ≤ |T_star - γ| := by
  classical
  have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  let m : Fin (N + 1) → ℝ := fun k => T + (2 * (k : ℝ) + 1) / (2 * ((N : ℝ) + 1))
  have hm_mem : ∀ k : Fin (N + 1), m k ∈ Set.Icc T (T + 1) := by
    intro k
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k.val
    have hk_le : (k : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    constructor
    · dsimp only [m]; linarith [div_nonneg (by linarith : 0 ≤ 2 * (k : ℝ) + 1)
        (by positivity : 0 ≤ 2 * ((N : ℝ) + 1))]
    · dsimp only [m]
      have hle1 : (2 * (k : ℝ) + 1) / (2 * ((N : ℝ) + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
  by_contra hno
  push Not at hno
  have hbad : ∀ k : Fin (N + 1), ∃ γ ∈ S, |m k - γ| < 1 / (2 * ((N : ℝ) + 1)) :=
    fun k => hno (m k) (hm_mem k)
  choose f hfS hflt using hbad
  have hinj : Function.Injective (fun k : Fin (N + 1) => (⟨f k, hfS k⟩ : {x // x ∈ S})) := by
    intro k₁ k₂ hEq
    have hfEq : f k₁ = f k₂ := congrArg Subtype.val hEq
    have hdist_lt : |m k₁ - m k₂| < 1 / ((N : ℝ) + 1) := by
      calc |m k₁ - m k₂| = |(m k₁ - f k₁) - (m k₂ - f k₂)| := by rw [hfEq]; ring_nf
        _ ≤ |m k₁ - f k₁| + |m k₂ - f k₂| := abs_sub _ _
        _ < 1 / (2 * ((N : ℝ) + 1)) + 1 / (2 * ((N : ℝ) + 1)) := add_lt_add (hflt k₁) (hflt k₂)
        _ = 1 / ((N : ℝ) + 1) := by field_simp [hN1_pos.ne']; ring
    have hdiff : |m k₁ - m k₂| = |(k₁ : ℝ) - (k₂ : ℝ)| / ((N : ℝ) + 1) := by
      dsimp only [m]
      have h1 : (T + (2 * (k₁ : ℝ) + 1) / (2 * ((N : ℝ) + 1))) -
          (T + (2 * (k₂ : ℝ) + 1) / (2 * ((N : ℝ) + 1))) =
          ((k₁ : ℝ) - (k₂ : ℝ)) / ((N : ℝ) + 1) := by
        field_simp [hN1_pos.ne']; ring
      rw [h1, abs_div, abs_of_pos hN1_pos]
    rw [hdiff, div_lt_div_iff_of_pos_right hN1_pos] at hdist_lt
    have hnat : k₁.val = k₂.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1 : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        have : 1 ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
        linarith
      · have h1 : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
        have : 1 ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by rw [abs_of_nonneg (by linarith)]; linarith
        linarith
    exact Fin.ext hnat
  have hle := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hle
  omega

/-- **Symmetric Pigeonhole Zero-Spacing Lemma**:
given `T ≥ 0` and a finite zero set `Z : Finset ℂ` with `Z.card ≤ N`, there exists
`T_* ∈ [T, T + 1]` simultaneously avoiding BOTH `+ρ.im` and `-ρ.im` for every `ρ ∈ Z` by distance
at least `1 / (2 * (N + 1))` (and lying strictly in `(T, T + 1)` when `T_*` is interior, with
`|T_* - ρ.im| ≥ 1 / (2 * (N + 1))` and `|(-T_*) - ρ.im| ≥ 1 / (2 * (N + 1))`). -/
theorem exists_good_height_pigeonhole_symm {T : ℝ} (hT : 0 ≤ T) (Z : Finset ℂ) {N : ℕ}
    (hcard : Z.card ≤ N) :
    ∃ T_star ∈ Set.Icc T (T + 1),
      ∀ ρ ∈ Z,
        1 / (2 * ((N : ℝ) + 1)) ≤ |T_star - ρ.im| ∧
        1 / (2 * ((N : ℝ) + 1)) ≤ |(-T_star) - ρ.im| := by
  classical
  let S : Finset ℝ := Z.image (fun ρ => |ρ.im|)
  have hScard : S.card ≤ N := (Finset.card_image_le).trans hcard
  obtain ⟨T_star, hT_mem, hdist⟩ := exists_good_height_pigeonhole T S hScard
  refine ⟨T_star, hT_mem, fun ρ hρ => ?_⟩
  have hT_nn : 0 ≤ T_star := hT.trans hT_mem.1
  have hbase : 1 / (2 * ((N : ℝ) + 1)) ≤ abs (T_star - |ρ.im|) :=
    hdist |ρ.im| (Finset.mem_image_of_mem _ hρ)
  constructor
  · exact hbase.trans (by simpa [abs_of_nonneg hT_nn] using abs_abs_sub_abs_le_abs_sub T_star ρ.im)
  · have h2 : abs (T_star - |ρ.im|) ≤ |(-T_star) - ρ.im| := by
      have hrew : |(-T_star) - ρ.im| = |T_star - (-ρ.im)| := by
        rw [← abs_neg ((-T_star) - ρ.im)]; congr 1; ring
      rw [hrew]
      simpa [abs_of_nonneg hT_nn, abs_neg] using abs_abs_sub_abs_le_abs_sub T_star (-ρ.im)
    exact hbase.trans h2

/-- Interval integrability of `x ↦ |x - x₀| ^ (-1 / 2)` on any `[a, b]`. -/
theorem intervalIntegrable_abs_sub_rpow_neg_half (a b x₀ : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x - x₀| ^ (-(1 / 2 : ℝ))) volume a b := by
  have aux : ∀ u v : ℝ, u ≤ v →
      IntervalIntegrable (fun x : ℝ => |x - x₀| ^ (-(1 / 2 : ℝ))) volume u v := by
    intro u v huv
    have hr : ∀ p q : ℝ, x₀ ≤ p → p ≤ q →
        IntervalIntegrable (fun x : ℝ => |x - x₀| ^ (-(1 / 2 : ℝ))) volume p q := by
      intro p q hp hpq
      have hsub : IntervalIntegrable (fun x : ℝ => (x - x₀) ^ (-(1 / 2 : ℝ))) volume p q := by
        have h1 := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
          (a := p - x₀) (b := q - x₀) (by norm_num)).comp_sub_right x₀
        simpa only [sub_add_cancel] using h1
      refine ⟨hsub.1.congr_fun (fun x hx => ?_) measurableSet_Ioc,
              hsub.2.congr_fun (fun x hx => ?_) measurableSet_Ioc⟩
      · dsimp only; rw [abs_of_nonneg (by linarith [hx.1])]
      · exfalso; linarith [hx.1, hx.2]
    have hl : ∀ p q : ℝ, p ≤ q → q ≤ x₀ →
        IntervalIntegrable (fun x : ℝ => |x - x₀| ^ (-(1 / 2 : ℝ))) volume p q := by
      intro p q hpq hq
      have hsub : IntervalIntegrable (fun y : ℝ => (y - (-x₀)) ^ (-(1 / 2 : ℝ))) volume (-q) (-p) := by
        have h1 := (intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
          (a := (-q) - (-x₀)) (b := (-p) - (-x₀)) (by norm_num)).comp_sub_right (-x₀)
        simpa only [sub_add_cancel] using h1
      have hIco : IntegrableOn (fun x : ℝ => ((-x) - (-x₀)) ^ (-(1 / 2 : ℝ))) (Set.Ico p q) volume := by
        have hcomp := hsub.1.comp_neg
        have hset : -Set.Ioc (-q) (-p) = Set.Ico p q := by
          ext x; simp only [Set.mem_neg, Set.mem_Ioc, Set.mem_Ico]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
        rwa [hset] at hcomp
      have hIoc : IntegrableOn (fun x : ℝ => ((-x) - (-x₀)) ^ (-(1 / 2 : ℝ))) (Set.Ioc p q) volume :=
        hIco.congr_set_ae MeasureTheory.Ico_ae_eq_Ioc.symm
      refine ⟨hIoc.congr_fun (fun x hx => ?_) measurableSet_Ioc, ?_⟩
      · dsimp only; rw [show (-x) - (-x₀) = -(x - x₀) by ring, abs_of_nonpos (by linarith [hx.2])]
      · rw [Set.Ioc_eq_empty (not_lt.mpr hpq)]; exact integrableOn_empty
    rcases le_total x₀ u with h | h
    · exact hr u v h huv
    · rcases le_total v x₀ with h' | h'
      · exact hl u v huv h'
      · exact (hl u x₀ h le_rfl).trans (hr x₀ v le_rfl h')
  rcases le_total a b with h | h
  · exact aux a b h
  · exact (aux b a h).symm

/-- Elementary 1D singular-power integral bound: for any `a ≤ b` and any shift `x₀ : ℝ`,
`∫ x in a..b, |x - x₀| ^ (-1 / 2 : ℝ) ≤ 4 * Real.sqrt (b - a)`. -/
theorem integral_abs_sub_rpow_neg_half_le {a b : ℝ} (hab : a ≤ b) (x₀ : ℝ) :
    ∫ x in a..b, |x - x₀| ^ (-(1 / 2 : ℝ)) ≤ 4 * Real.sqrt (b - a) := by
  have hint_pos : ∀ L : ℝ, 0 ≤ L →
      ∫ u in (0 : ℝ)..L, u ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt L := by
    intro L _
    rw [integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), sub_zero,
        Real.sqrt_eq_rpow]
    have h1 : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [h1]; ring
  have hright : ∀ u v c : ℝ, c ≤ u → u ≤ v →
      ∫ x in u..v, |x - c| ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt (v - u) := by
    intro u v c hcu huv
    have hcongr : ∀ x ∈ Set.uIcc u v, |x - c| ^ (-(1 / 2 : ℝ)) = (x - c) ^ (-(1 / 2 : ℝ)) := by
      intro x hx
      rw [Set.uIcc_of_le huv] at hx
      rw [abs_of_nonneg (by linarith [hx.1])]
    rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_comp_sub_right (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) c]
    have hval : ∫ t in (u - c)..(v - c), t ^ (-(1 / 2 : ℝ)) =
        2 * Real.sqrt (v - c) - 2 * Real.sqrt (u - c) := by
      have h1 := hint_pos (u - c) (by linarith)
      have h2 := hint_pos (v - c) (by linarith)
      have hi1 := intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
        (a := 0) (b := u - c) (by norm_num)
      have hi2 := intervalIntegral.intervalIntegrable_rpow' (r := -(1 / 2 : ℝ))
        (a := u - c) (b := v - c) (by norm_num)
      have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      linarith
    rw [hval]
    have hsq : Real.sqrt (v - c) - Real.sqrt (u - c) ≤ Real.sqrt (v - u) := by
      have h1 : 0 ≤ Real.sqrt (u - c) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (v - u) := Real.sqrt_nonneg _
      have hle : Real.sqrt (v - c) ≤ Real.sqrt (u - c) + Real.sqrt (v - u) := by
        rw [← Real.sqrt_sq (add_nonneg h1 h2)]
        refine Real.sqrt_le_sqrt ?_
        have hs1 : Real.sqrt (u - c) ^ 2 = u - c := Real.sq_sqrt (by linarith)
        have hs2 : Real.sqrt (v - u) ^ 2 = v - u := Real.sq_sqrt (by linarith)
        nlinarith [mul_nonneg h1 h2]
      linarith
    linarith
  have hleft : ∀ u v c : ℝ, u ≤ v → v ≤ c →
      ∫ x in u..v, |x - c| ^ (-(1 / 2 : ℝ)) ≤ 2 * Real.sqrt (v - u) := by
    intro u v c huv hvc
    have hr := hright (-v) (-u) (-c) (by linarith) (by linarith)
    have hcomp : ∀ x : ℝ, |(-x) - (-c)| ^ (-(1 / 2 : ℝ)) = |x - c| ^ (-(1 / 2 : ℝ)) := by
      intro x; congr 1
      rw [show (-x) - (-c) = -(x - c) by ring, abs_neg]
    have hval : ∫ x in u..v, |x - c| ^ (-(1 / 2 : ℝ)) =
        ∫ y in (-v)..(-u), |y - (-c)| ^ (-(1 / 2 : ℝ)) := by
      have h1 := intervalIntegral.integral_comp_neg (f := fun y : ℝ => |y - (-c)| ^ (-(1 / 2 : ℝ)))
        (a := u) (b := v)
      simpa only [hcomp] using h1
    rw [hval]
    simpa only [show (-u) - (-v) = v - u by ring] using hr
  rcases le_total x₀ a with hxa | hax
  · exact (hright a b x₀ hxa hab).trans (by linarith [Real.sqrt_nonneg (b - a)])
  · rcases le_total b x₀ with hbx | hxb
    · exact (hleft a b x₀ hab hbx).trans (by linarith [Real.sqrt_nonneg (b - a)])
    · rw [← intervalIntegral.integral_add_adjacent_intervals
            (intervalIntegrable_abs_sub_rpow_neg_half a x₀ x₀)
            (intervalIntegrable_abs_sub_rpow_neg_half x₀ b x₀)]
      have h1 : Real.sqrt (x₀ - a) ≤ Real.sqrt (b - a) := Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt (b - x₀) ≤ Real.sqrt (b - a) := Real.sqrt_le_sqrt (by linarith)
      linarith [hleft a x₀ x₀ hax le_rfl, hright x₀ b x₀ le_rfl hxb]

/-- **AM-GM Averaged Linear-in-`N` Good-Horizontal-Line Lemma**:
for any `σ₀ < c`, `T : ℝ`, and finite set `Z : Finset ℂ`, there exists `T_* ∈ (T, T + 1)`
avoiding all `±ρ.im` (`ρ ∈ Z`) such that BOTH horizontal pole-sum integrals are **linear** in
`Z.card`:
`∫_{σ₀}^c (∑_{ρ ∈ Z} ‖(σ ± i T_*) - ρ‖⁻¹) dσ ≤ 32 * √(c - σ₀) * (Z.card + 1)`. -/
theorem exists_good_height_avg_integral {σ₀ c : ℝ} (hσc : σ₀ < c) (T : ℝ) (Z : Finset ℂ) :
    ∃ T_star ∈ Set.Ioo T (T + 1),
      (∀ ρ ∈ Z, T_star ≠ ρ.im ∧ -T_star ≠ ρ.im) ∧
      (∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) + I * (T_star : ℂ)) - ρ‖⁻¹) ≤
        32 * Real.sqrt (c - σ₀) * ((Z.card : ℝ) + 1) ∧
      (∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) - I * (T_star : ℂ)) - ρ‖⁻¹) ≤
        32 * Real.sqrt (c - σ₀) * ((Z.card : ℝ) + 1) := by
  classical
  let Φ : ℝ → ℝ := fun t =>
    ∑ ρ ∈ Z, (|t - ρ.im| ^ (-(1 / 2 : ℝ)) + |t + ρ.im| ^ (-(1 / 2 : ℝ)))
  have hΦ_int : IntervalIntegrable Φ volume T (T + 1) :=
    intervalIntegrable_finset_sum_apply Z
      (fun ρ (t : ℝ) => |t - ρ.im| ^ (-(1 / 2 : ℝ)) + |t + ρ.im| ^ (-(1 / 2 : ℝ))) fun ρ _ => by
        have h1 := intervalIntegrable_abs_sub_rpow_neg_half T (T + 1) ρ.im
        have h2 : IntervalIntegrable (fun t : ℝ => |t + ρ.im| ^ (-(1 / 2 : ℝ))) volume T (T + 1) := by
          simpa only [sub_neg_eq_add] using intervalIntegrable_abs_sub_rpow_neg_half T (T + 1) (-ρ.im)
        exact h1.add h2
  have hΦ_le : ∫ t in T..(T + 1), Φ t ≤ 8 * (Z.card : ℝ) := by
    have hsum : ∫ t in T..(T + 1), Φ t =
        ∑ ρ ∈ Z, ((∫ t in T..(T + 1), |t - ρ.im| ^ (-(1 / 2 : ℝ))) +
                  (∫ t in T..(T + 1), |t + ρ.im| ^ (-(1 / 2 : ℝ)))) := by
      dsimp only [Φ]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun ρ _ => ?_
        have h1 := intervalIntegrable_abs_sub_rpow_neg_half T (T + 1) ρ.im
        have h2 : IntervalIntegrable (fun t : ℝ => |t + ρ.im| ^ (-(1 / 2 : ℝ))) volume T (T + 1) := by
          simpa only [sub_neg_eq_add] using intervalIntegrable_abs_sub_rpow_neg_half T (T + 1) (-ρ.im)
        exact intervalIntegral.integral_add h1 h2
      · intro ρ _
        have h1 := intervalIntegrable_abs_sub_rpow_neg_half T (T + 1) ρ.im
        have h2 : IntervalIntegrable (fun t : ℝ => |t + ρ.im| ^ (-(1 / 2 : ℝ))) volume T (T + 1) := by
          simpa only [sub_neg_eq_add] using intervalIntegrable_abs_sub_rpow_neg_half T (T + 1) (-ρ.im)
        exact h1.add h2
    rw [hsum]
    calc ∑ ρ ∈ Z, ((∫ t in T..(T + 1), |t - ρ.im| ^ (-(1 / 2 : ℝ))) +
                    (∫ t in T..(T + 1), |t + ρ.im| ^ (-(1 / 2 : ℝ))))
        ≤ ∑ _ρ ∈ Z, (4 * Real.sqrt ((T + 1) - T) + 4 * Real.sqrt ((T + 1) - T)) := by
          refine Finset.sum_le_sum fun ρ _ => add_le_add ?_ ?_
          · exact integral_abs_sub_rpow_neg_half_le (by linarith) ρ.im
          · simpa only [sub_neg_eq_add] using
              integral_abs_sub_rpow_neg_half_le (by linarith : T ≤ T + 1) (-ρ.im)
      _ = 8 * (Z.card : ℝ) := by
          rw [show (T + 1) - T = 1 by ring, Real.sqrt_one, Finset.sum_const, nsmul_eq_mul]
          ring
  let bad : Set ℝ := (Z.image (fun ρ => ρ.im) : Set ℝ) ∪ (Z.image (fun ρ => -ρ.im) : Set ℝ)
  have hbad_meas : volume bad = 0 :=
    ((Z.image _).finite_toSet.union (Z.image _).finite_toSet).countable.measure_zero volume
  have hex : ∃ T_star ∈ Set.Ioo T (T + 1), T_star ∉ bad ∧ Φ T_star ≤ 8 * ((Z.card : ℝ) + 1) := by
    by_contra hno
    push Not at hno
    have hae : ∀ᵐ t ∂volume, t ∈ Set.Icc T (T + 1) → 8 * ((Z.card : ℝ) + 1) ≤ Φ t := by
      have hne_lo : ∀ᵐ t ∂volume, t ≠ T := by rw [ae_iff]; simp
      have hne_hi : ∀ᵐ t ∂volume, t ≠ T + 1 := by rw [ae_iff]; simp
      have hnot_bad : ∀ᵐ t ∂volume, t ∉ bad := by
        rw [ae_iff]
        have hEq : {t : ℝ | ¬ t ∉ bad} = bad := by ext t; simp
        rw [hEq]; exact hbad_meas
      filter_upwards [hne_lo, hne_hi, hnot_bad] with t hlo hhi hnb ht
      exact (hno t ⟨lt_of_le_of_ne ht.1 hlo.symm, lt_of_le_of_ne ht.2 hhi⟩ hnb).le
    have hge : 8 * ((Z.card : ℝ) + 1) ≤ ∫ t in T..(T + 1), Φ t := by
      have hconst : ∫ _t in T..(T + 1), (8 * ((Z.card : ℝ) + 1) : ℝ) = 8 * ((Z.card : ℝ) + 1) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [← hconst]
      refine intervalIntegral.integral_mono_ae_restrict (by linarith) intervalIntegrable_const hΦ_int ?_
      exact (ae_restrict_iff' measurableSet_Icc).mpr hae
    linarith
  obtain ⟨T_star, hT_mem, hT_not_bad, hΦ_bd⟩ := hex
  have havoid : ∀ ρ ∈ Z, T_star ≠ ρ.im ∧ -T_star ≠ ρ.im := by
    intro ρ hρ
    refine ⟨fun h => hT_not_bad (Or.inl (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, hρ, h.symm⟩))),
            fun h => hT_not_bad (Or.inr (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ρ, hρ, by linarith⟩)))⟩
  have hhoriz : ∀ (s_im : ℝ), (∀ ρ ∈ Z, s_im ≠ ρ.im) →
      (∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) ≤
        4 * Real.sqrt (c - σ₀) * ∑ ρ ∈ Z, |s_im - ρ.im| ^ (-(1 / 2 : ℝ)) := by
    intro s_im hne
    have hcont_term : ∀ ρ ∈ Z, Continuous (fun σ : ℝ => ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) := by
      intro ρ hρ
      refine Continuous.inv₀ (by fun_prop) fun σ h0 => ?_
      rw [norm_eq_zero] at h0
      have him := congrArg Complex.im h0
      simp at him
      exact hne ρ hρ (by linarith)
    rw [intervalIntegral.integral_finsetSum (fun ρ hρ => (hcont_term ρ hρ).intervalIntegrable σ₀ c),
        Finset.mul_sum]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    have hv : s_im - ρ.im ≠ 0 := sub_ne_zero.mpr (hne ρ hρ)
    have hint_rhs : IntervalIntegrable (fun σ : ℝ => |σ - ρ.re| ^ (-(1 / 2 : ℝ)) * |s_im - ρ.im| ^ (-(1 / 2 : ℝ)))
        volume σ₀ c :=
      (intervalIntegrable_abs_sub_rpow_neg_half σ₀ c ρ.re).mul_const _
    have hmono : ∫ σ in σ₀..c, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹ ≤
        ∫ σ in σ₀..c, |σ - ρ.re| ^ (-(1 / 2 : ℝ)) * |s_im - ρ.im| ^ (-(1 / 2 : ℝ)) := by
      refine intervalIntegral.integral_mono_ae_restrict hσc.le
        ((hcont_term ρ hρ).intervalIntegrable σ₀ c) hint_rhs ?_
      have hae_ne : ∀ᵐ σ ∂volume, σ ≠ ρ.re := by rw [ae_iff]; simp
      refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards [hae_ne] with σ hσ _
      have hnorm_eq : ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖ =
          Real.sqrt ((σ - ρ.re) ^ 2 + (s_im - ρ.im) ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]
        simp [sq]
      rw [hnorm_eq]
      have hu : σ - ρ.re ≠ 0 := sub_ne_zero.mpr hσ
      have hu0 : 0 < |σ - ρ.re| := abs_pos.mpr hu
      have hv0 : 0 < |s_im - ρ.im| := abs_pos.mpr hv
      have hprod : |σ - ρ.re| * |s_im - ρ.im| ≤ (σ - ρ.re) ^ 2 + (s_im - ρ.im) ^ 2 := by
        have h1 : 0 ≤ (|σ - ρ.re| - |s_im - ρ.im|) ^ 2 := sq_nonneg _
        have h2 : |σ - ρ.re| ^ 2 = (σ - ρ.re) ^ 2 := sq_abs _
        have h3 : |s_im - ρ.im| ^ 2 = (s_im - ρ.im) ^ 2 := sq_abs _
        nlinarith [mul_nonneg hu0.le hv0.le]
      have hinv := inv_anti₀ (Real.sqrt_pos.mpr (mul_pos hu0 hv0)) (Real.sqrt_le_sqrt hprod)
      have hrew : (Real.sqrt (|σ - ρ.re| * |s_im - ρ.im|))⁻¹ =
          |σ - ρ.re| ^ (-(1 / 2 : ℝ)) * |s_im - ρ.im| ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_mul hu0.le, mul_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
            Real.rpow_neg hu0.le, Real.rpow_neg hv0.le]
      rwa [hrew] at hinv
    calc ∫ σ in σ₀..c, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹
        ≤ ∫ σ in σ₀..c, |σ - ρ.re| ^ (-(1 / 2 : ℝ)) * |s_im - ρ.im| ^ (-(1 / 2 : ℝ)) := hmono
      _ = (∫ σ in σ₀..c, |σ - ρ.re| ^ (-(1 / 2 : ℝ))) * |s_im - ρ.im| ^ (-(1 / 2 : ℝ)) :=
          intervalIntegral.integral_mul_const _ _
      _ ≤ (4 * Real.sqrt (c - σ₀)) * |s_im - ρ.im| ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (integral_abs_sub_rpow_neg_half_le hσc.le ρ.re)
            (Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨T_star, hT_mem, havoid, ?_, ?_⟩
  · have h1 := hhoriz T_star (fun ρ hρ => (havoid ρ hρ).1)
    have hle_Φ : ∑ ρ ∈ Z, |T_star - ρ.im| ^ (-(1 / 2 : ℝ)) ≤ Φ T_star := by
      refine Finset.sum_le_sum fun ρ _ => ?_
      linarith [Real.rpow_nonneg (abs_nonneg (T_star + ρ.im)) (-(1 / 2 : ℝ))]
    calc ∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) + I * (T_star : ℂ)) - ρ‖⁻¹
        ≤ 4 * Real.sqrt (c - σ₀) * ∑ ρ ∈ Z, |T_star - ρ.im| ^ (-(1 / 2 : ℝ)) := h1
      _ ≤ 4 * Real.sqrt (c - σ₀) * (8 * ((Z.card : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hle_Φ.trans hΦ_bd) (by positivity)
      _ = 32 * Real.sqrt (c - σ₀) * ((Z.card : ℝ) + 1) := by ring
  · have h2 := hhoriz (-T_star) (fun ρ hρ => (havoid ρ hρ).2)
    have hcongr : ∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) - I * (T_star : ℂ)) - ρ‖⁻¹ =
        ∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) - ρ‖⁻¹ :=
      intervalIntegral.integral_congr fun σ _ => by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        congr 2; push_cast; ring
    have hle_Φ : ∑ ρ ∈ Z, |(-T_star) - ρ.im| ^ (-(1 / 2 : ℝ)) ≤ Φ T_star := by
      refine Finset.sum_le_sum fun ρ _ => ?_
      have habs : |(-T_star) - ρ.im| = |T_star + ρ.im| := by
        rw [← abs_neg ((-T_star) - ρ.im)]; congr 1; ring
      rw [habs]
      linarith [Real.rpow_nonneg (abs_nonneg (T_star - ρ.im)) (-(1 / 2 : ℝ))]
    rw [hcongr]
    calc ∫ σ in σ₀..c, ∑ ρ ∈ Z, ‖((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) - ρ‖⁻¹
        ≤ 4 * Real.sqrt (c - σ₀) * ∑ ρ ∈ Z, |(-T_star) - ρ.im| ^ (-(1 / 2 : ℝ)) := h2
      _ ≤ 4 * Real.sqrt (c - σ₀) * (8 * ((Z.card : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left (hle_Φ.trans hΦ_bd) (by positivity)
      _ = 32 * Real.sqrt (c - σ₀) * ((Z.card : ℝ) + 1) := by ring

/-! ### Quantitative Horizontal & Left-Vertical Bounds for the Cesàro-1 Integrand -/

/-- Cesàro-1 explicit-formula integrand `(-L'/L)(s, χ) · x^{s + 1} / (s (s + 1))`. -/
def cesaro1LogDerivIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  Stage3ZeroFreeRegion.negLogDerivL χ s * (x : ℂ) ^ (s + 1) / (s * (s + 1))

/-- **Horizontal Segment Estimate for the Cesàro-1 Integrand**:
for `1 ≤ x`, `σ₀ ≤ c`, `T_* > 0`, if `‖(-L'/L)(σ + i s_im, χ)‖ ≤ M_H` along `σ ∈ [σ₀, c]` with
`|s_im| = T_*`, then
`‖∫_{σ₀}^c cesaro1LogDerivIntegrand χ x (σ + i s_im) dσ‖ ≤ (c - σ₀) * M_H * x^{c + 1} / T_*^2`. -/
theorem norm_integral_horizontal_cesaro1_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ₀ c s_im T_star M_H : ℝ} (hx : 1 ≤ x) (hσc : σ₀ ≤ c) (hT : 0 < T_star)
    (hsim : |s_im| = T_star) (hMH : 0 ≤ M_H)
    (hbd : ∀ σ ∈ Set.Icc σ₀ c,
      ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ))‖ ≤ M_H) :
    ‖∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
      (c - σ₀) * M_H * x ^ (c + 1) / T_star ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hpt : ∀ σ ∈ Set.uIoc σ₀ c,
      ‖cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
        M_H * x ^ (c + 1) / T_star ^ 2 := by
    intro σ hσ
    rw [Set.uIoc_of_le hσc] at hσ
    have hmem : σ ∈ Set.Icc σ₀ c := ⟨hσ.1.le, hσ.2⟩
    unfold cesaro1LogDerivIntegrand
    rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : ((σ : ℂ) + I * (s_im : ℂ) + 1).re = σ + 1 := by simp
    rw [hre]
    have hx_le : x ^ (σ + 1) ≤ x ^ (c + 1) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith [hσ.2])
    have hden1 : T_star ≤ ‖(σ : ℂ) + I * (s_im : ℂ)‖ := by
      have h := Complex.abs_im_le_norm ((σ : ℂ) + I * (s_im : ℂ))
      simpa [hsim] using h
    have hden2 : T_star ≤ ‖(σ : ℂ) + I * (s_im : ℂ) + 1‖ := by
      have h := Complex.abs_im_le_norm ((σ : ℂ) + I * (s_im : ℂ) + 1)
      simpa [hsim] using h
    have hden : T_star ^ 2 ≤ ‖(σ : ℂ) + I * (s_im : ℂ)‖ * ‖(σ : ℂ) + I * (s_im : ℂ) + 1‖ := by
      rw [sq]; exact mul_le_mul hden1 hden2 hT.le (norm_nonneg _)
    have hnum : ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ))‖ * x ^ (σ + 1) ≤
        M_H * x ^ (c + 1) :=
      mul_le_mul (hbd σ hmem) hx_le (Real.rpow_nonneg hx0.le _) hMH
    exact div_le_div₀ (by positivity) hnum (sq_pos_of_pos hT) hden
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [abs_of_nonneg (sub_nonneg.mpr hσc)] at h1
  calc ‖∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (s_im : ℂ))‖
      ≤ M_H * x ^ (c + 1) / T_star ^ 2 * (c - σ₀) := h1
    _ = (c - σ₀) * M_H * x ^ (c + 1) / T_star ^ 2 := by ring

/-- **Left-Vertical Line Estimate for the Cesàro-1 Integrand**:
for `0 < σ₀`, `0 < x`, `0 < T_*`, if `‖(-L'/L)(σ₀ + i t, χ)‖ ≤ M_V` on `t ∈ [-T_*, T_*]` and
the integrand is interval-integrable on `[-T_*, T_*]`, then
`‖∫_{-T_*}^{T_*} cesaro1LogDerivIntegrand χ x (σ₀ + i t) dt‖ ≤ (π / σ₀) * M_V * x^{σ₀ + 1}`. -/
theorem norm_integral_left_vertical_cesaro1_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ₀ T_star M_V : ℝ} (hx : 0 < x) (hσ₀ : 0 < σ₀) (hT : 0 < T_star) (hMV : 0 ≤ M_V)
    (hint : IntervalIntegrable
      (fun t : ℝ => cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))) volume (-T_star) T_star)
    (hbd : ∀ t ∈ Set.Icc (-T_star) T_star,
      ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤ M_V) :
    ‖∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤
      (Real.pi / σ₀) * M_V * x ^ (σ₀ + 1) := by
  have hdom_int : Integrable (fun t : ℝ => M_V * x ^ (σ₀ + 1) * (σ₀ ^ 2 + t ^ 2)⁻¹) :=
    (Stage4ExplicitFormula.integrable_inv_sq_add_sq hσ₀).const_mul (M_V * x ^ (σ₀ + 1))
  have hpt : ∀ t ∈ Set.Icc (-T_star) T_star,
      ‖cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤
        M_V * x ^ (σ₀ + 1) * (σ₀ ^ 2 + t ^ 2)⁻¹ := by
    intro t ht
    unfold cesaro1LogDerivIntegrand
    rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have hre : ((σ₀ : ℂ) + I * (t : ℂ) + 1).re = σ₀ + 1 := by simp
    rw [hre]
    have hns1 : ‖(σ₀ : ℂ) + I * (t : ℂ)‖ ^ 2 = σ₀ ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
    have hns2 : ‖(σ₀ : ℂ) + I * (t : ℂ) + 1‖ ^ 2 = (σ₀ + 1) ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [sq]
    have hle : ‖(σ₀ : ℂ) + I * (t : ℂ)‖ ≤ ‖(σ₀ : ℂ) + I * (t : ℂ) + 1‖ := by
      nlinarith [norm_nonneg ((σ₀ : ℂ) + I * (t : ℂ)), norm_nonneg ((σ₀ : ℂ) + I * (t : ℂ) + 1)]
    have hprod : σ₀ ^ 2 + t ^ 2 ≤ ‖(σ₀ : ℂ) + I * (t : ℂ)‖ * ‖(σ₀ : ℂ) + I * (t : ℂ) + 1‖ := by
      calc σ₀ ^ 2 + t ^ 2 = ‖(σ₀ : ℂ) + I * (t : ℂ)‖ * ‖(σ₀ : ℂ) + I * (t : ℂ)‖ := by
            rw [← sq, hns1]
        _ ≤ ‖(σ₀ : ℂ) + I * (t : ℂ)‖ * ‖(σ₀ : ℂ) + I * (t : ℂ) + 1‖ :=
            mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    rw [← div_eq_mul_inv]
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right (hbd t ht) (Real.rpow_nonneg hx.le _))
      (by positivity) hprod
  calc ‖∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))‖
      ≤ ∫ t in (-T_star)..T_star, ‖cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ t in (-T_star)..T_star, M_V * x ^ (σ₀ + 1) * (σ₀ ^ 2 + t ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on (by linarith) hint.norm
          hdom_int.intervalIntegrable hpt
    _ = ∫ t in Set.Ioc (-T_star) T_star, M_V * x ^ (σ₀ + 1) * (σ₀ ^ 2 + t ^ 2)⁻¹ :=
        intervalIntegral.integral_of_le (by linarith)
    _ ≤ ∫ t : ℝ, M_V * x ^ (σ₀ + 1) * (σ₀ ^ 2 + t ^ 2)⁻¹ := by
        refine setIntegral_le_integral hdom_int (Eventually.of_forall fun t => ?_)
        positivity
    _ = M_V * x ^ (σ₀ + 1) * (Real.pi / σ₀) := by
        rw [integral_const_mul, Stage4ExplicitFormula.integral_inv_sq_add_sq hσ₀]
    _ = (Real.pi / σ₀) * M_V * x ^ (σ₀ + 1) := by ring

/-! ## Section 3A: Direct Smoothed Explicit Formula for `ψ_1(x, χ)` -/

open Classical in
/-- **General Contour-Shift Smoothed Explicit Formula for `ψ_1(x, χ)`**:
combining `Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le`, Section 1's multiplicative
rectangular residue shift `vertical_contour_shift_mul_eq_sum_residues`, and Section 2's horizontal
and left-vertical contour bounds! -/
theorem norm_psi1Char_sub_explicit_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x σ₀ c T_star M_H M_V : ℝ} (hx : 1 ≤ x) (hσ₀ : 0 < σ₀) (hσ1 : σ₀ < 1) (hc : 1 < c)
    (hT : 0 < T_star) (hMH : 0 ≤ M_H) (hMV : 0 ≤ M_V)
    (Z : Finset ℂ) (m : ℂ → ℂ)
    (hZ : ∀ ρ ∈ Z, σ₀ < ρ.re ∧ ρ.re < 1 ∧ -T_star < ρ.im ∧ ρ.im < T_star)
    (hL : DifferentiableOn ℂ
      (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s -
        (if χ = 1 then 1 / (s - 1) else 0) + ∑ ρ ∈ Z, m ρ / (s - ρ))
      (closedRect σ₀ c (-T_star) T_star))
    (hH_top : ∀ σ ∈ Set.Icc σ₀ c,
      ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (T_star : ℂ))‖ ≤ M_H)
    (hH_bot : ∀ σ ∈ Set.Icc σ₀ c,
      ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) - I * (T_star : ℂ))‖ ≤ M_H)
    (hV : ∀ t ∈ Set.Icc (-T_star) T_star,
      ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤ M_V) :
    ‖Stage4ExplicitFormula.psi1Char χ x -
      ((if χ = 1 then (x : ℂ) ^ 2 / 2 else 0) -
        ∑ ρ ∈ Z, m ρ * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))‖ ≤
      (6 * c / Real.pi) * x ^ (c + 1) / ((c - 1) * T_star) +
      (1 / (2 * σ₀)) * M_V * x ^ (σ₀ + 1) +
      ((c - σ₀) / Real.pi) * M_H * x ^ (c + 1) / T_star ^ 2 := by
  classical
  have hx0 : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hσc : σ₀ < c := hσ1.trans hc
  let W : ℂ → ℂ := fun s => (x : ℂ) ^ (s + 1) / (s * (s + 1))
  have hW_diff : DifferentiableOn ℂ W (closedRect σ₀ c (-T_star) T_star) := by
    have hpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ (s + 1)) := by
      have hEq : (fun s : ℂ => (x : ℂ) ^ (s + 1)) =
          fun s : ℂ => cexp (Complex.log (x : ℂ) * (s + 1)) :=
        funext fun s => Complex.cpow_def_of_ne_zero hxC (s + 1)
      rw [hEq]
      exact ((differentiable_const _).mul (differentiable_id.add (differentiable_const 1))).cexp
    refine hpow.differentiableOn.div
      (differentiableOn_id.mul (differentiableOn_id.add (differentiableOn_const 1)))
      fun s hs => mul_ne_zero ?_ ?_
    · intro h0; have := congrArg Complex.re h0; simp at this; linarith [hs.1.1]
    · intro h0; have := congrArg Complex.re h0; simp at this; linarith [hs.1.1]
  have h1_notMem : (1 : ℂ) ∉ Z := fun h1 => by
    have hre := (hZ 1 h1).2.1
    simp at hre
  let J : Finset ℂ := if χ = 1 then insert (1 : ℂ) Z else Z
  let a : ℂ → ℂ := fun p => if p = 1 then 1 else -m p
  have hp : ∀ p ∈ J, p ∈ openRect σ₀ c (-T_star) T_star := by
    intro p hp
    by_cases hχ : χ = 1
    · simp only [J, hχ, ↓reduceIte, Finset.mem_insert] at hp
      rcases hp with rfl | hpZ
      · exact ⟨by simp [hσ1, hc], by simp [hT]⟩
      · obtain ⟨h1, h2, h3, h4⟩ := hZ p hpZ
        exact ⟨⟨h1, h2.trans hc⟩, ⟨h3, h4⟩⟩
    · simp only [J, hχ, ↓reduceIte] at hp
      obtain ⟨h1, h2, h3, h4⟩ := hZ p hp
      exact ⟨⟨h1, h2.trans hc⟩, ⟨h3, h4⟩⟩
  have hL_eq : (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s - ∑ p ∈ J, a p / (s - p)) =
      fun s => Stage3ZeroFreeRegion.negLogDerivL χ s -
        (if χ = 1 then 1 / (s - 1) else 0) + ∑ ρ ∈ Z, m ρ / (s - ρ) := by
    funext s
    have hZ_sum : ∑ ρ ∈ Z, a ρ / (s - ρ) = -(∑ ρ ∈ Z, m ρ / (s - ρ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hne : ρ ≠ 1 := fun h => h1_notMem (h ▸ hρ)
      simp [a, hne, neg_div]
    by_cases hχ : χ = 1
    · simp only [J, hχ, ↓reduceIte, Finset.sum_insert h1_notMem]
      have ha1 : a 1 = 1 := by simp [a]
      rw [ha1, hZ_sum]; ring
    · simp only [J, hχ, ↓reduceIte, hZ_sum]; ring
  have hL' : DifferentiableOn ℂ
      (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s - ∑ p ∈ J, a p / (s - p))
      (closedRect σ₀ c (-T_star) T_star) := hL_eq.symm ▸ hL
  have hres_eq : ∑ p ∈ J, a p * W p =
      (if χ = 1 then (x : ℂ) ^ 2 / 2 else 0) -
        ∑ ρ ∈ Z, m ρ * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) := by
    have hZ_res : ∑ ρ ∈ Z, a ρ * W ρ = -(∑ ρ ∈ Z, m ρ * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hne : ρ ≠ 1 := fun h => h1_notMem (h ▸ hρ)
      simp only [a, hne, ↓reduceIte, W]
      ring
    have hW1 : a 1 * W 1 = (x : ℂ) ^ 2 / 2 := by
      simp only [a, ↓reduceIte, one_mul, W]
      have h2 : (1 : ℂ) + 1 = (2 : ℂ) := by norm_num
      rw [h2, Complex.cpow_ofNat]
    by_cases hχ : χ = 1
    · simp only [J, hχ, ↓reduceIte, Finset.sum_insert h1_notMem, hW1, hZ_res]; ring
    · simp only [J, hχ, ↓reduceIte, hZ_res]; ring
  have hshift := vertical_contour_shift_mul_eq_sum_residues
    (Stage3ZeroFreeRegion.negLogDerivL χ) W hσc hT J id a hp hL' hW_diff
  simp only [id_eq] at hshift
  rw [hres_eq] at hshift
  -- Identify LHS of `hshift` with `Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T_star`
  have hLHS_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T_star)..T_star,
        Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
          W ((c : ℂ) + I * (t : ℂ))) =
      Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T_star := by
    unfold Stage4ExplicitFormula.truncatedPerronPsi1
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    dsimp only [W]
    have h1 : (c : ℂ) + I * (t : ℂ) + 1 = (c : ℂ) + 1 + I * (t : ℂ) := by ring
    rw [h1, mul_div_assoc]
  rw [hLHS_eq] at hshift
  -- Continuity & integrability of the left-vertical integrand directly from `hL'`
  have hV_int : IntervalIntegrable
      (fun t : ℝ => cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))) volume (-T_star) T_star := by
    have hcont_L : ContinuousOn (Stage3ZeroFreeRegion.negLogDerivL χ)
        ((fun t : ℝ => (σ₀ : ℂ) + I * (t : ℂ)) '' Set.Icc (-T_star) T_star) := by
      have hsub : (fun t : ℝ => (σ₀ : ℂ) + I * (t : ℂ)) '' Set.Icc (-T_star) T_star ⊆
          closedRect σ₀ c (-T_star) T_star := by
        rintro _ ⟨t, ht, rfl⟩
        exact ⟨by simp [hσc.le], by simpa using ht⟩
      have hP : ContinuousOn (fun s => ∑ p ∈ J, a p / (s - p))
          ((fun t : ℝ => (σ₀ : ℂ) + I * (t : ℂ)) '' Set.Icc (-T_star) T_star) := by
        refine continuousOn_finsetSum J fun p hpJ => continuousOn_const.div
          (continuousOn_id.sub continuousOn_const) ?_
        rintro _ ⟨t, _, rfl⟩ h0
        have hre := congrArg Complex.re h0
        simp at hre
        linarith [(hp p hpJ).1.1]
      have hsum := (hL'.continuousOn.mono hsub).add hP
      refine hsum.congr fun s _ => by simp only [Pi.add_apply]; ring
    have hcont_t : ContinuousOn
        (fun t : ℝ => cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ)))
        (Set.uIcc (-T_star) T_star) := by
      rw [Set.uIcc_of_le (by linarith)]
      have hmap : ContinuousOn (fun t : ℝ => (σ₀ : ℂ) + I * (t : ℂ)) (Set.Icc (-T_star) T_star) :=
        by fun_prop
      have h1 : ContinuousOn (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ)))
          (Set.Icc (-T_star) T_star) :=
        hcont_L.comp hmap (Set.mapsTo_image _ _)
      have h2 : ContinuousOn (fun t : ℝ => W ((σ₀ : ℂ) + I * (t : ℂ))) (Set.Icc (-T_star) T_star) :=
        hW_diff.continuousOn.comp hmap fun t ht => ⟨by simp [hσc.le], by simpa using ht⟩
      refine (h1.mul h2).congr fun t _ => ?_
      unfold cesaro1LogDerivIntegrand; dsimp only [W]; rw [mul_div_assoc]; rfl
    exact hcont_t.intervalIntegrable
  have hV_eq : ∫ t in (-T_star)..T_star,
      Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ)) * W ((σ₀ : ℂ) + I * (t : ℂ)) =
      ∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ)) :=
    intervalIntegral.integral_congr fun t _ => by
      unfold cesaro1LogDerivIntegrand; dsimp only [W]; rw [mul_div_assoc]
  have hTop_eq : ∫ σ in σ₀..c,
      Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (T_star : ℂ)) * W ((σ : ℂ) + I * (T_star : ℂ)) =
      ∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ)) :=
    intervalIntegral.integral_congr fun σ _ => by
      unfold cesaro1LogDerivIntegrand; dsimp only [W]; rw [mul_div_assoc]
  have hBot_eq : ∫ σ in σ₀..c,
      Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) - I * (T_star : ℂ)) * W ((σ : ℂ) - I * (T_star : ℂ)) =
      ∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) :=
    intervalIntegral.integral_congr fun σ _ => by
      have hsub : (σ : ℂ) - I * (T_star : ℂ) = (σ : ℂ) + I * ((-T_star : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsub]; unfold cesaro1LogDerivIntegrand; dsimp only [W]; rw [mul_div_assoc]
  have hV_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤
      (1 / (2 * σ₀)) * M_V * x ^ (σ₀ + 1) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))‖
        ≤ (2 * Real.pi)⁻¹ * ((Real.pi / σ₀) * M_V * x ^ (σ₀ + 1)) :=
          mul_le_mul_of_nonneg_left
            (norm_integral_left_vertical_cesaro1_le χ hx0 hσ₀ hT hMV hV_int hV) (by positivity)
      _ = (1 / (2 * σ₀)) * M_V * x ^ (σ₀ + 1) := by field_simp [Real.pi_ne_zero, hσ₀.ne']
  have hTop_bd : ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ))‖ ≤
      ((c - σ₀) / (2 * Real.pi)) * M_H * x ^ (c + 1) / T_star ^ 2 := by
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    calc (2 * Real.pi)⁻¹ * ‖∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ))‖
        ≤ (2 * Real.pi)⁻¹ * ((c - σ₀) * M_H * x ^ (c + 1) / T_star ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_integral_horizontal_cesaro1_le χ hx hσc.le hT (abs_of_pos hT) hMH hH_top)
            (by positivity)
      _ = ((c - σ₀) / (2 * Real.pi)) * M_H * x ^ (c + 1) / T_star ^ 2 := by
          field_simp [Real.pi_ne_zero, hT.ne']
  have hBot_bd : ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ))‖ ≤
      ((c - σ₀) / (2 * Real.pi)) * M_H * x ^ (c + 1) / T_star ^ 2 := by
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hH_bot' : ∀ σ ∈ Set.Icc σ₀ c,
        ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ))‖ ≤ M_H := by
      intro σ hσ
      have hsub : (σ : ℂ) + I * ((-T_star : ℝ) : ℂ) = (σ : ℂ) - I * (T_star : ℂ) := by
        push_cast; ring
      rw [hsub]; exact hH_bot σ hσ
    calc (2 * Real.pi)⁻¹ *
          ‖∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ))‖
        ≤ (2 * Real.pi)⁻¹ * ((c - σ₀) * M_H * x ^ (c + 1) / T_star ^ 2) :=
          mul_le_mul_of_nonneg_left
            (norm_integral_horizontal_cesaro1_le χ hx hσc.le hT
              (by rw [abs_neg, abs_of_pos hT]) hMH hH_bot')
            (by positivity)
      _ = ((c - σ₀) / (2 * Real.pi)) * M_H * x ^ (c + 1) / T_star ^ 2 := by
          field_simp [Real.pi_ne_zero, hT.ne']
  have hperron := Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le χ hx0 hc hT
  have hsplit : Stage4ExplicitFormula.psi1Char χ x -
      ((if χ = 1 then (x : ℂ) ^ 2 / 2 else 0) -
        ∑ ρ ∈ Z, m ρ * (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))) =
      (Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T_star) +
      ((((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          (∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ)))) +
        ((2 * (Real.pi : ℂ) * I)⁻¹ *
          (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ)))) -
        ((2 * (Real.pi : ℂ) * I)⁻¹ *
          (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ))))) := by
    rw [hV_eq, hTop_eq, hBot_eq] at hshift
    linear_combination hshift
  rw [hsplit]
  have htri1 := norm_add_le
    (Stage4ExplicitFormula.psi1Char χ x - Stage4ExplicitFormula.truncatedPerronPsi1 χ x c T_star)
    ((((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ)))) +
      ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ)))) -
      ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)))))
  have htri2 := norm_sub_le
    ((((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ)))) +
      ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ)))))
    (((2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)))))
  have htri3 := norm_add_le
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T_star)..T_star, cesaro1LogDerivIntegrand χ x ((σ₀ : ℂ) + I * (t : ℂ))))
    ((2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ σ in σ₀..c, cesaro1LogDerivIntegrand χ x ((σ : ℂ) + I * (T_star : ℂ))))
  have hhalf : ((c - σ₀) / (2 * Real.pi)) * M_H * x ^ (c + 1) / T_star ^ 2 +
      ((c - σ₀) / (2 * Real.pi)) * M_H * x ^ (c + 1) / T_star ^ 2 =
      ((c - σ₀) / Real.pi) * M_H * x ^ (c + 1) / T_star ^ 2 := by
    field_simp [Real.pi_ne_zero, hT.ne']; ring
  linarith

/-! ## Section 3B: Sharp Perron Formula (`perronKernel0` & `truncatedPerronPsi`) -/

/-- Sharp (unsmoothed) truncated Perron kernel `(1 / (2π)) ∫_{-T}^T y^{c + i t} / (c + i t) dt`. -/
def perronKernel0 (y c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))

/-- Sharp truncated Perron integral for `ψ(x, χ)` at height `T` along `Re(s) = c > 1`. -/
def truncatedPerronPsi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T,
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))

private lemma integral_rpow_horizontal {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (a b : ℝ) :
    ∫ σ in a..b, y ^ σ = (y ^ b - y ^ a) / Real.log y := by
  have hlog : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hd : ∀ σ : ℝ, HasDerivAt (fun u : ℝ => y ^ u / Real.log y) (y ^ σ) σ := fun σ => by
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (Real.log y * u))
        (Real.exp (Real.log y * σ) * Real.log y) σ := by
      simpa using ((hasDerivAt_id σ).const_mul (Real.log y)).exp
    simp_rw [Real.rpow_def_of_pos hy]
    refine (h1.div_const (Real.log y)).congr_deriv ?_
    field_simp [hlog]
  have hcont : Continuous (fun σ : ℝ => y ^ σ) := by
    simp_rw [Real.rpow_def_of_pos hy]; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hd σ) (hcont.intervalIntegrable a b)]
  ring

/-- **Sharp Perron Kernel Bound for `0 < y < 1`** (proved directly from Section 1's Rectangular
Cauchy Integral Theorem by shifting right to `R → +∞`):
`‖perronKernel0 y c T‖ ≤ y ^ c / (π * T * |log y|)`. -/
theorem norm_perronKernel0_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy1 : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel0 y c T‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hlog_neg : Real.log y < 0 := Real.log_neg hy0 hy1
  have habs_log : |Real.log y| = -Real.log y := abs_of_neg hlog_neg
  have hbound_R : ∀ R : ℝ, c < R →
      ‖perronKernel0 y c T‖ ≤
        (T / Real.pi) * (y ^ R / R) + y ^ c / (Real.pi * T * |Real.log y|) := by
    intro R hR
    have hR0 : 0 < R := hc.trans hR
    let F : ℂ → ℂ := fun s => (y : ℂ) ^ s / s
    have hF_diff : DifferentiableOn ℂ F (closedRect c R (-T) T) := by
      have hpow : Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) := by
        have hEq : (fun s : ℂ => (y : ℂ) ^ s) = fun s => cexp (Complex.log (y : ℂ) * s) :=
          funext fun s => Complex.cpow_def_of_ne_zero hyC s
        rw [hEq]; exact ((differentiable_const _).mul differentiable_id).cexp
      refine hpow.differentiableOn.div differentiableOn_id fun s hs h0 => ?_
      have := congrArg Complex.re h0; simp at this; linarith [hs.1.1]
    have hshift := vertical_contour_shift_eq_sum_residues F hR hT (∅ : Finset Empty)
      Empty.elim Empty.elim (fun j hj => (Finset.notMem_empty j hj).elim)
      (by simpa using hF_diff)
    simp only [Finset.sum_empty, zero_add] at hshift
    -- Rearrange: `perronKernel0 y c T = Left = Right - Top + Bot`
    have hEq : perronKernel0 y c T =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((R : ℂ) + I * (t : ℂ))) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) + I * (T : ℂ))) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) - I * (T : ℂ))) := by
      unfold perronKernel0; linear_combination -hshift
    have hR_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((R : ℂ) + I * (t : ℂ)))‖ ≤
        (T / Real.pi) * (y ^ R / R) := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hpt : ∀ t ∈ Set.uIoc (-T) T, ‖F ((R : ℂ) + I * (t : ℂ))‖ ≤ y ^ R / R := by
        intro t _
        dsimp only [F]
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hre : ((R : ℂ) + I * (t : ℂ)).re = R := by simp
        rw [hre]
        have hden : R ≤ ‖(R : ℂ) + I * (t : ℂ)‖ := by
          have := Complex.abs_re_le_norm ((R : ℂ) + I * (t : ℂ))
          simpa [abs_of_pos hR0] using this
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le R) hR0 hden
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [show T - (-T) = 2 * T by ring, abs_of_pos (by positivity)] at h1
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F ((R : ℂ) + I * (t : ℂ))‖
          ≤ (2 * Real.pi)⁻¹ * (y ^ R / R * (2 * T)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (T / Real.pi) * (y ^ R / R) := by field_simp [Real.pi_ne_zero, hR0.ne']
    have hH_bd : ∀ s_im : ℝ, |s_im| = T →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) + I * (s_im : ℂ)))‖ ≤
          y ^ c / (2 * Real.pi * T * |Real.log y|) := by
      intro s_im hsim
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have hcont : Continuous (fun σ : ℝ => F ((σ : ℂ) + I * (s_im : ℂ))) := by
        dsimp only [F]
        have hpow : Continuous (fun σ : ℝ => (y : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ))) := by
          have hEq' : (fun σ : ℝ => (y : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ))) =
              fun σ : ℝ => cexp (Complex.log (y : ℂ) * ((σ : ℂ) + I * (s_im : ℂ))) :=
            funext fun σ => Complex.cpow_def_of_ne_zero hyC _
          rw [hEq']; fun_prop
        refine hpow.div (by fun_prop) fun σ h0 => ?_
        have := congrArg Complex.im h0; simp at this; rw [this, abs_zero] at hsim; linarith
      have hcont_rhs : Continuous (fun σ : ℝ => y ^ σ / T) := by
        simp_rw [Real.rpow_def_of_pos hy0]; fun_prop
      have hint_le : ‖∫ σ in c..R, F ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
          ∫ σ in c..R, y ^ σ / T := by
        calc ‖∫ σ in c..R, F ((σ : ℂ) + I * (s_im : ℂ))‖
            ≤ ∫ σ in c..R, ‖F ((σ : ℂ) + I * (s_im : ℂ))‖ :=
              intervalIntegral.norm_integral_le_integral_norm hR.le
          _ ≤ ∫ σ in c..R, y ^ σ / T := by
              refine intervalIntegral.integral_mono_on hR.le
                (hcont.intervalIntegrable c R).norm (hcont_rhs.intervalIntegrable c R) fun σ _ => ?_
              dsimp only [F]
              rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
              have hre : ((σ : ℂ) + I * (s_im : ℂ)).re = σ := by simp
              rw [hre]
              have hden : T ≤ ‖(σ : ℂ) + I * (s_im : ℂ)‖ := by
                have := Complex.abs_im_le_norm ((σ : ℂ) + I * (s_im : ℂ))
                simpa [hsim] using this
              exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le σ) hT hden
      have hval : ∫ σ in c..R, y ^ σ / T ≤ y ^ c / (T * |Real.log y|) := by
        rw [intervalIntegral.integral_div, integral_rpow_horizontal hy0 hy1.ne c R, habs_log]
        have hnum : (y ^ R - y ^ c) / Real.log y = (y ^ c - y ^ R) / (-Real.log y) := by
          field_simp [hlog_neg.ne]; ring
        have hneg_pos : 0 < -Real.log y := by linarith
        rw [hnum, div_div, mul_comm (-Real.log y) T]
        exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hy0.le R]) (by positivity)
      calc (2 * Real.pi)⁻¹ * ‖∫ σ in c..R, F ((σ : ℂ) + I * (s_im : ℂ))‖
          ≤ (2 * Real.pi)⁻¹ * (y ^ c / (T * |Real.log y|)) :=
            mul_le_mul_of_nonneg_left (hint_le.trans hval) (by positivity)
        _ = y ^ c / (2 * Real.pi * T * |Real.log y|) := by
            field_simp [Real.pi_ne_zero, hT.ne', (abs_pos.mpr hlog_neg.ne).ne']
    have hTop := hH_bd T (abs_of_pos hT)
    have hBot : ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) - I * (T : ℂ)))‖ ≤
        y ^ c / (2 * Real.pi * T * |Real.log y|) := by
      have hcongr : ∫ σ in c..R, F ((σ : ℂ) - I * (T : ℂ)) =
          ∫ σ in c..R, F ((σ : ℂ) + I * ((-T : ℝ) : ℂ)) :=
        intervalIntegral.integral_congr fun σ _ => by congr 1; push_cast; ring
      rw [hcongr]
      exact hH_bd (-T) (by rw [abs_neg, abs_of_pos hT])
    rw [hEq]
    have h1 := norm_add_le
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((R : ℂ) + I * (t : ℂ))) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) + I * (T : ℂ))))
      ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) - I * (T : ℂ))))
    have h2 := norm_sub_le
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F ((R : ℂ) + I * (t : ℂ))))
      ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c..R, F ((σ : ℂ) + I * (T : ℂ))))
    have hsum : y ^ c / (2 * Real.pi * T * |Real.log y|) +
        y ^ c / (2 * Real.pi * T * |Real.log y|) = y ^ c / (Real.pi * T * |Real.log y|) := by
      field_simp [Real.pi_ne_zero, hT.ne', (abs_pos.mpr hlog_neg.ne).ne']; ring
    linarith
  have htend : Tendsto (fun R : ℝ => (T / Real.pi) * (y ^ R / R) +
      y ^ c / (Real.pi * T * |Real.log y|)) atTop
      (𝓝 (0 + y ^ c / (Real.pi * T * |Real.log y|))) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    have hyR : Tendsto (fun R : ℝ => y ^ R) atTop (𝓝 0) := by
      have hEq : (fun R : ℝ => y ^ R) = fun R => Real.exp (Real.log y * R) :=
        funext fun R => Real.rpow_def_of_pos hy0 R
      rw [hEq]
      have hbot : Tendsto (fun R : ℝ => Real.log y * R) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg hlog_neg tendsto_id
      exact Real.tendsto_exp_atBot.comp hbot
    have hdiv : Tendsto (fun R : ℝ => y ^ R / R) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hyR.mul tendsto_inv_atTop_zero
    simpa only [mul_zero] using hdiv.const_mul (T / Real.pi)
  rw [zero_add] at htend
  refine ge_of_tendsto htend ?_
  filter_upwards [eventually_gt_atTop c] with R hR using hbound_R R hR

/-- **Sharp Perron Kernel Bound for `y > 1`** (proved directly from Section 1's Rectangular
Residue Theorem `vertical_contour_shift_div_id_eq_sum_residues` by shifting left to `-R → -∞`,
picking up exact residue `1` at `s = 0`):
`‖perronKernel0 y c T - 1‖ ≤ y ^ c / (π * T * |log y|)`. -/
theorem norm_perronKernel0_gt_one {y c T : ℝ} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel0 y c T - 1‖ ≤ y ^ c / (Real.pi * T * |Real.log y|) := by
  have hy0 : 0 < y := by linarith
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hlog_pos : 0 < Real.log y := Real.log_pos hy1
  have habs_log : |Real.log y| = Real.log y := abs_of_pos hlog_pos
  have hbound_R : ∀ R : ℝ, 0 < R →
      ‖perronKernel0 y c T - 1‖ ≤
        (T / Real.pi) * (y ^ (-R) / R) + y ^ c / (Real.pi * T * |Real.log y|) := by
    intro R hR
    have hshift := vertical_contour_shift_div_id_eq_sum_residues (fun _ => (1 : ℂ))
      hy0 (by linarith : -R < 0) hc hT (∅ : Finset Empty) Empty.elim Empty.elim
      (fun j hj => (Finset.notMem_empty j hj).elim)
      (fun j hj => (Finset.notMem_empty j hj).elim)
      (by simp)
    simp only [one_mul, Finset.sum_empty, add_zero] at hshift
    let F : ℂ → ℂ := fun s => (y : ℂ) ^ s / s
    have hEq : perronKernel0 y c T - 1 =
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F (((-R : ℝ) : ℂ) + I * (t : ℂ))) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) + I * (T : ℂ))) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) - I * (T : ℂ))) := by
      unfold perronKernel0; linear_combination hshift
    have hL_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F (((-R : ℝ) : ℂ) + I * (t : ℂ)))‖ ≤
        (T / Real.pi) * (y ^ (-R) / R) := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hpt : ∀ t ∈ Set.uIoc (-T) T, ‖F (((-R : ℝ) : ℂ) + I * (t : ℂ))‖ ≤ y ^ (-R) / R := by
        intro t _
        dsimp only [F]
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hre : (((-R : ℝ) : ℂ) + I * (t : ℂ)).re = -R := by simp
        rw [hre]
        have hden : R ≤ ‖((-R : ℝ) : ℂ) + I * (t : ℂ)‖ := by
          have := Complex.abs_re_le_norm (((-R : ℝ) : ℂ) + I * (t : ℂ))
          simpa [abs_neg, abs_of_pos hR] using this
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le (-R)) hR hden
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [show T - (-T) = 2 * T by ring, abs_of_pos (by positivity)] at h1
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, F (((-R : ℝ) : ℂ) + I * (t : ℂ))‖
          ≤ (2 * Real.pi)⁻¹ * (y ^ (-R) / R * (2 * T)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (T / Real.pi) * (y ^ (-R) / R) := by field_simp [Real.pi_ne_zero, hR.ne']
    have hH_bd : ∀ s_im : ℝ, |s_im| = T →
        ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) + I * (s_im : ℂ)))‖ ≤
          y ^ c / (2 * Real.pi * T * |Real.log y|) := by
      intro s_im hsim
      rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      have hcont : Continuous (fun σ : ℝ => F ((σ : ℂ) + I * (s_im : ℂ))) := by
        dsimp only [F]
        have hpow : Continuous (fun σ : ℝ => (y : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ))) := by
          have hEq' : (fun σ : ℝ => (y : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ))) =
              fun σ : ℝ => cexp (Complex.log (y : ℂ) * ((σ : ℂ) + I * (s_im : ℂ))) :=
            funext fun σ => Complex.cpow_def_of_ne_zero hyC _
          rw [hEq']; fun_prop
        refine hpow.div (by fun_prop) fun σ h0 => ?_
        have := congrArg Complex.im h0; simp at this; rw [this, abs_zero] at hsim; linarith
      have hcont_rhs : Continuous (fun σ : ℝ => y ^ σ / T) := by
        simp_rw [Real.rpow_def_of_pos hy0]; fun_prop
      have hint_le : ‖∫ σ in (-R)..c, F ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
          ∫ σ in (-R)..c, y ^ σ / T := by
        calc ‖∫ σ in (-R)..c, F ((σ : ℂ) + I * (s_im : ℂ))‖
            ≤ ∫ σ in (-R)..c, ‖F ((σ : ℂ) + I * (s_im : ℂ))‖ :=
              intervalIntegral.norm_integral_le_integral_norm (by linarith)
          _ ≤ ∫ σ in (-R)..c, y ^ σ / T := by
              refine intervalIntegral.integral_mono_on (by linarith)
                (hcont.intervalIntegrable (-R) c).norm (hcont_rhs.intervalIntegrable (-R) c) fun σ _ => ?_
              dsimp only [F]
              rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
              have hre : ((σ : ℂ) + I * (s_im : ℂ)).re = σ := by simp
              rw [hre]
              have hden : T ≤ ‖(σ : ℂ) + I * (s_im : ℂ)‖ := by
                have := Complex.abs_im_le_norm ((σ : ℂ) + I * (s_im : ℂ))
                simpa [hsim] using this
              exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le σ) hT hden
      have hval : ∫ σ in (-R)..c, y ^ σ / T ≤ y ^ c / (T * |Real.log y|) := by
        rw [intervalIntegral.integral_div, integral_rpow_horizontal hy0 hy1.ne' (-R) c,
            habs_log, div_div, mul_comm (Real.log y) T]
        exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hy0.le (-R)]) (by positivity)
      calc (2 * Real.pi)⁻¹ * ‖∫ σ in (-R)..c, F ((σ : ℂ) + I * (s_im : ℂ))‖
          ≤ (2 * Real.pi)⁻¹ * (y ^ c / (T * |Real.log y|)) :=
            mul_le_mul_of_nonneg_left (hint_le.trans hval) (by positivity)
        _ = y ^ c / (2 * Real.pi * T * |Real.log y|) := by
            field_simp [Real.pi_ne_zero, hT.ne', (abs_pos.mpr hlog_pos.ne').ne']
    have hTop := hH_bd T (abs_of_pos hT)
    have hBot : ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) - I * (T : ℂ)))‖ ≤
        y ^ c / (2 * Real.pi * T * |Real.log y|) := by
      have hcongr : ∫ σ in (-R)..c, F ((σ : ℂ) - I * (T : ℂ)) =
          ∫ σ in (-R)..c, F ((σ : ℂ) + I * ((-T : ℝ) : ℂ)) :=
        intervalIntegral.integral_congr fun σ _ => by congr 1; push_cast; ring
      rw [hcongr]
      exact hH_bd (-T) (by rw [abs_neg, abs_of_pos hT])
    rw [hEq]
    have h1 := norm_sub_le
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F (((-R : ℝ) : ℂ) + I * (t : ℂ))) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) + I * (T : ℂ))))
      ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) - I * (T : ℂ))))
    have h2 := norm_add_le
      (((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in (-T)..T, F (((-R : ℝ) : ℂ) + I * (t : ℂ))))
      ((2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in (-R)..c, F ((σ : ℂ) + I * (T : ℂ))))
    have hsum : y ^ c / (2 * Real.pi * T * |Real.log y|) +
        y ^ c / (2 * Real.pi * T * |Real.log y|) = y ^ c / (Real.pi * T * |Real.log y|) := by
      field_simp [Real.pi_ne_zero, hT.ne', (abs_pos.mpr hlog_pos.ne').ne']; ring
    linarith
  have htend : Tendsto (fun R : ℝ => (T / Real.pi) * (y ^ (-R) / R) +
      y ^ c / (Real.pi * T * |Real.log y|)) atTop
      (𝓝 (0 + y ^ c / (Real.pi * T * |Real.log y|))) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    have hyR : Tendsto (fun R : ℝ => y ^ (-R)) atTop (𝓝 0) := by
      have hEq : (fun R : ℝ => y ^ (-R)) = fun R => Real.exp ((-Real.log y) * R) :=
        funext fun R => by rw [Real.rpow_def_of_pos hy0]; congr 1; ring
      rw [hEq]
      have hbot : Tendsto (fun R : ℝ => (-Real.log y) * R) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
      exact Real.tendsto_exp_atBot.comp hbot
    have hdiv : Tendsto (fun R : ℝ => y ^ (-R) / R) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using hyR.mul tendsto_inv_atTop_zero
    simpa only [mul_zero] using hdiv.const_mul (T / Real.pi)
  rw [zero_add] at htend
  refine ge_of_tendsto htend ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR using hbound_R R hR

/-- Uniform singularity-free bound on `perronKernel0 y c T` near `y = 1` (for all `0 < y ≤ 2`,
`1 ≤ c ≤ 3`, `1 ≤ T`): `‖perronKernel0 y c T - (if 1 < y then 1 else 0)‖ ≤ 60`. -/
theorem norm_perronKernel0_sub_ind_le_uniform {y c T : ℝ} (hy0 : 0 < y) (hy2 : y ≤ 2)
    (hc1 : 1 ≤ c) (hc3 : c ≤ 3) (hT : 1 ≤ T) :
    ‖perronKernel0 y c T - (if 1 < y then (1 : ℂ) else 0)‖ ≤ 60 := by
  have hc0 : 0 < c := by linarith
  have hT0 : 0 < T := by linarith
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  by_cases hlog : 1 / T < |Real.log y|
  · have hy_ne : y ≠ 1 := fun h => by subst h; simp at hlog; linarith
    have hTlog : 1 ≤ T * |Real.log y| := by
      have := mul_le_mul_of_nonneg_left hlog.le hT0.le
      rwa [mul_one_div_cancel hT0.ne'] at this
    have hyc_le : y ^ c ≤ 8 := by
      calc y ^ c ≤ 2 ^ c := Real.rpow_le_rpow hy0.le hy2 hc0.le
        _ ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc3
        _ = 8 := by norm_num
    have hcore : ‖perronKernel0 y c T - (if 1 < y then (1 : ℂ) else 0)‖ ≤
        y ^ c / (Real.pi * T * |Real.log y|) := by
      rcases lt_or_gt_of_ne hy_ne with hlt | hgt
      · simp only [not_lt.mpr hlt.le, ↓reduceIte, sub_zero]
        exact norm_perronKernel0_lt_one hy0 hlt hc0 hT0
      · simp only [hgt, ↓reduceIte]
        exact norm_perronKernel0_gt_one hgt hc0 hT0
    have hden : (1 : ℝ) ≤ Real.pi * T * |Real.log y| := by
      have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      rw [mul_assoc]
      exact one_le_mul_of_one_le_of_one_le hpi hTlog
    calc ‖perronKernel0 y c T - (if 1 < y then (1 : ℂ) else 0)‖
        ≤ y ^ c / (Real.pi * T * |Real.log y|) := hcore
      _ ≤ y ^ c := div_le_self (Real.rpow_nonneg hy0.le c) hden
      _ ≤ 60 := by linarith
  · push Not at hlog
    -- `|Real.log y| ≤ 1 / T`: compare `perronKernel0 y c T` directly with `perronKernel0 1 c T`
    have hK1_le : ‖perronKernel0 1 c T‖ ≤ 1 / 2 := by
      unfold perronKernel0
      have hcongr : ∫ t in (-T)..T, ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) =
          ∫ t in (-T)..T, (((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) - ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        rw [Complex.ofReal_one, Complex.one_cpow, one_div]
        symm
        refine eq_inv_of_mul_eq_one_left (G := ℂ) ?_
        have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
        push_cast
        calc (((c : ℂ) / ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) - (t : ℂ) / ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) * I) *
              ((c : ℂ) + I * (t : ℂ)))
            = ((c : ℂ) ^ 2 - I ^ 2 * (t : ℂ) ^ 2) / ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) := by ring
          _ = ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) / ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) := by
              rw [Complex.I_sq]; ring
          _ = 1 := div_self (by exact_mod_cast hpos.ne' : ((c : ℂ) ^ 2 + (t : ℂ) ^ 2) ≠ 0)
      have hcont1 : Continuous (fun t : ℝ => (((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ))) :=
        Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop) fun t => by positivity)
      have hcont2 : Continuous (fun t : ℝ => ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I) :=
        (Complex.continuous_ofReal.comp (continuous_id.div (by fun_prop) fun t => by positivity)).mul
          continuous_const
      have hodd : ∫ t in (-T)..T, ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) * I = 0 := by
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
        have h0 : ∫ t in (-T)..T, t / (c ^ 2 + t ^ 2) = 0 := by
          have hneg := intervalIntegral.integral_comp_neg (f := fun t : ℝ => t / (c ^ 2 + t ^ 2))
            (a := -T) (b := T)
          simp only [neg_neg, neg_sq, neg_div, intervalIntegral.integral_neg] at hneg
          linarith
        rw [h0, Complex.ofReal_zero, zero_mul]
      rw [hcongr, intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _)
        (hcont2.intervalIntegrable _ _), hodd, sub_zero, intervalIntegral.integral_ofReal,
        norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity)]
      have hle_pi : ∫ t in (-T)..T, c / (c ^ 2 + t ^ 2) ≤ Real.pi := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        have hint_c : Integrable (fun t : ℝ => c * (c ^ 2 + t ^ 2)⁻¹) :=
          (Stage4ExplicitFormula.integrable_inv_sq_add_sq hc0).const_mul c
        have heq : (fun t : ℝ => c / (c ^ 2 + t ^ 2)) = fun t : ℝ => c * (c ^ 2 + t ^ 2)⁻¹ :=
          funext fun t => div_eq_mul_inv _ _
        rw [heq]
        calc ∫ t in Set.Ioc (-T) T, c * (c ^ 2 + t ^ 2)⁻¹
            ≤ ∫ t : ℝ, c * (c ^ 2 + t ^ 2)⁻¹ :=
              setIntegral_le_integral hint_c (Eventually.of_forall fun t => by positivity)
          _ = c * (Real.pi / c) := by rw [integral_const_mul, Stage4ExplicitFormula.integral_inv_sq_add_sq hc0]
          _ = Real.pi := mul_div_cancel₀ Real.pi hc0.ne'
      calc (2 * Real.pi)⁻¹ * ∫ t in (-T)..T, c / (c ^ 2 + t ^ 2)
          ≤ (2 * Real.pi)⁻¹ * Real.pi := mul_le_mul_of_nonneg_left hle_pi (by positivity)
        _ = 1 / 2 := by field_simp [Real.pi_ne_zero]
    -- Bound `‖cexp (I * θ) - 1‖ ≤ |θ|` via FTC
    have hexp_I_sub : ∀ θ : ℝ, ‖cexp (I * (θ : ℂ)) - 1‖ ≤ |θ| := fun θ => by
      have hd : ∀ u : ℝ, HasDerivAt (fun v : ℝ => cexp (I * (v : ℂ))) (I * cexp (I * (u : ℂ))) u := by
        intro u
        have h1 : HasDerivAt (fun v : ℝ => I * (v : ℂ)) I u := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul I
        exact h1.cexp.congr_deriv (by ring)
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := θ)
        (fun u _ => hd u) ((by fun_prop : Continuous fun u : ℝ => I * cexp (I * (u : ℂ))).intervalIntegrable 0 θ)
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at hftc
      rw [← hftc]
      have hpt : ∀ u ∈ Set.uIoc 0 θ, ‖I * cexp (I * (u : ℂ))‖ ≤ 1 := fun u _ => by
        rw [norm_mul, Complex.norm_I, one_mul, mul_comm I (u : ℂ), Complex.norm_exp_ofReal_mul_I]
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      simpa using h1
    -- Bound `|Real.exp a - 1| ≤ |a| * Real.exp |a|` via FTC
    have hexp_R_sub : ∀ a : ℝ, |Real.exp a - 1| ≤ |a| * Real.exp |a| := fun a => by
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := a)
        (fun u _ => Real.hasDerivAt_exp u) (Real.continuous_exp.intervalIntegrable 0 a)
      rw [Real.exp_zero] at hftc
      rw [← hftc, ← Real.norm_eq_abs]
      have hpt : ∀ u ∈ Set.uIoc 0 a, ‖Real.exp u‖ ≤ Real.exp |a| := fun u hu => by
        rw [Real.norm_of_nonneg (Real.exp_nonneg u)]
        refine Real.exp_le_exp.mpr ?_
        rcases le_total 0 a with h0a | ha0
        · rw [Set.uIoc_of_le h0a] at hu; exact hu.2.trans (le_abs_self a)
        · rw [Set.uIoc_of_ge ha0] at hu; exact hu.2.trans (abs_nonneg a)
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      simpa [mul_comm] using h1
    have hyc_sub : |y ^ c - 1| ≤ 81 / T := by
      rw [Real.rpow_def_of_pos hy0]
      have ha_le : |Real.log y * c| ≤ 3 / T := by
        rw [abs_mul, abs_of_pos hc0]
        calc |Real.log y| * c ≤ (1 / T) * 3 := mul_le_mul hlog hc3 hc0.le (by positivity)
          _ = 3 / T := by ring
      have ha3 : |Real.log y * c| ≤ 3 := ha_le.trans (div_le_self (by norm_num) hT)
      have hexp3 : Real.exp 3 ≤ 27 := by
        have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [h3]
        calc Real.exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (Real.exp_nonneg 1) he1 3
          _ = 27 := by norm_num
      calc |Real.exp (Real.log y * c) - 1|
          ≤ |Real.log y * c| * Real.exp |Real.log y * c| := hexp_R_sub _
        _ ≤ (3 / T) * Real.exp 3 :=
            mul_le_mul ha_le (Real.exp_le_exp.mpr ha3) (Real.exp_nonneg _) (by positivity)
        _ ≤ (3 / T) * 27 := mul_le_mul_of_nonneg_left hexp3 (by positivity)
        _ = 81 / T := by ring
    -- Bound `∫_{-T}^T ‖c + i t‖⁻¹ dt ≤ 2 + 2 * Real.log T`
    have hinv_int : ∫ t in (-T)..T, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 + 2 * Real.log T := by
      have hcont_n : Continuous (fun t : ℝ => ‖(c : ℂ) + I * (t : ℂ)‖⁻¹) := by
        refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
        rw [norm_eq_zero] at h0
        have := congrArg Complex.re h0; simp at this; linarith
      have hmid : ∫ t in (-1 : ℝ)..1, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 2 := by
        have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ ≤ 1 := fun t _ => by
          have hc_le : 1 ≤ ‖(c : ℂ) + I * (t : ℂ)‖ :=
            hc1.trans (by simpa [abs_of_pos hc0] using Complex.abs_re_le_norm ((c : ℂ) + I * (t : ℂ)))
          exact inv_le_one_of_one_le₀ hc_le
        calc ∫ t in (-1 : ℝ)..1, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹
            ≤ ∫ _t in (-1 : ℝ)..1, (1 : ℝ) :=
              intervalIntegral.integral_mono_on (by norm_num) (hcont_n.intervalIntegrable _ _)
                intervalIntegrable_const hpt
          _ = 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
      have hpos_tail : ∫ t in (1 : ℝ)..T, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log T := by
        have hint_inv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 : ℝ) T := by
          refine (ContinuousOn.inv₀ continuousOn_id fun t ht => ?_).intervalIntegrable
          rw [Set.uIcc_of_le hT] at ht; dsimp only [id_eq]; linarith [ht.1]
        have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ ≤ t⁻¹ := fun t ht => by
          have ht0 : 0 < t := by linarith [ht.1]
          have hle : t ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := by
            simpa [abs_of_pos ht0] using Complex.abs_im_le_norm ((c : ℂ) + I * (t : ℂ))
          exact inv_anti₀ ht0 hle
        calc ∫ t in (1 : ℝ)..T, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹
            ≤ ∫ t in (1 : ℝ)..T, t⁻¹ :=
              intervalIntegral.integral_mono_on hT (hcont_n.intervalIntegrable _ _) hint_inv hpt
          _ = Real.log T := by
              rw [integral_inv_of_pos zero_lt_one hT0, div_one]
      have hneg_tail : ∫ t in (-T)..(-1 : ℝ), ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ ≤ Real.log T := by
        have hcomp : ∫ t in (-T)..(-1 : ℝ), ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ =
            ∫ u in (1 : ℝ)..T, ‖(c : ℂ) + I * (u : ℂ)‖⁻¹ := by
          have h1 := intervalIntegral.integral_comp_neg
            (f := fun u : ℝ => ‖(c : ℂ) + I * (u : ℂ)‖⁻¹) (a := -T) (b := -1)
          simp only [neg_neg] at h1
          rw [← h1]
          refine intervalIntegral.integral_congr fun t _ => ?_
          congr 1
          rw [← Complex.norm_conj]
          congr 1
          simp [Complex.conj_ofReal]
        rw [hcomp]; exact hpos_tail
      have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
        (hcont_n.intervalIntegrable (μ := volume) (-T) (-1))
        (hcont_n.intervalIntegrable (μ := volume) (-1) 1)
      have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
        (hcont_n.intervalIntegrable (μ := volume) (-T) 1)
        (hcont_n.intervalIntegrable (μ := volume) 1 T)
      linarith
    -- Now bound `‖perronKernel0 y c T - perronKernel0 1 c T‖`
    have hdiff_le : ‖perronKernel0 y c T - perronKernel0 1 c T‖ ≤ 55 := by
      unfold perronKernel0
      rw [← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hcont_y : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) := by
        have hpow : Continuous (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) := by
          have hEq' : (fun t : ℝ => (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ))) =
              fun t : ℝ => cexp (Complex.log (y : ℂ) * ((c : ℂ) + I * (t : ℂ))) :=
            funext fun t => Complex.cpow_def_of_ne_zero hyC _
          rw [hEq']; fun_prop
        refine hpow.div (by fun_prop) fun t h0 => ?_
        have := congrArg Complex.re h0; simp at this; linarith
      have hcont_1 : Continuous (fun t : ℝ => ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) := by
        simp_rw [Complex.ofReal_one, Complex.one_cpow]
        refine continuous_const.div (by fun_prop) fun t h0 => ?_
        have := congrArg Complex.re h0; simp at this; linarith
      rw [← intervalIntegral.integral_sub (hcont_y.intervalIntegrable _ _)
        (hcont_1.intervalIntegrable _ _)]
      have hpt : ∀ t ∈ Set.Icc (-T) T,
          ‖(y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) -
            ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))‖ ≤
            (81 / T) * ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ + 1 / T := by
        intro t _
        rw [Complex.ofReal_one, Complex.one_cpow, ← sub_div, norm_div]
        have hpow_fac : (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) =
            ((y ^ c : ℝ) : ℂ) * cexp (I * ((t * Real.log y : ℝ) : ℂ)) := by
          rw [Complex.cpow_def_of_ne_zero hyC, ← Complex.ofReal_log hy0.le, mul_add, Complex.exp_add,
              Real.rpow_def_of_pos hy0, Complex.ofReal_exp]
          congr 1
          · congr 1; push_cast; ring
          · congr 1; push_cast; ring
        have hnum_split : (y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) - 1 =
            (((y ^ c - 1 : ℝ) : ℂ)) * cexp (I * ((t * Real.log y : ℝ) : ℂ)) +
            (cexp (I * ((t * Real.log y : ℝ) : ℂ)) - 1) := by
          rw [hpow_fac]; push_cast; ring
        have hexp_norm : ‖cexp (I * ((t * Real.log y : ℝ) : ℂ))‖ = 1 := by
          rw [mul_comm I, Complex.norm_exp_ofReal_mul_I]
        have hterm1 : ‖(((y ^ c - 1 : ℝ) : ℂ)) * cexp (I * ((t * Real.log y : ℝ) : ℂ))‖ /
            ‖(c : ℂ) + I * (t : ℂ)‖ ≤ (81 / T) * ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ := by
          rw [norm_mul, hexp_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hyc_sub (inv_nonneg.mpr (norm_nonneg _))
        have hterm2 : ‖cexp (I * ((t * Real.log y : ℝ) : ℂ)) - 1‖ /
            ‖(c : ℂ) + I * (t : ℂ)‖ ≤ 1 / T := by
          have h1 := hexp_I_sub (t * Real.log y)
          rw [abs_mul] at h1
          have ht_le : |t| ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := by
            simpa using Complex.abs_im_le_norm ((c : ℂ) + I * (t : ℂ))
          have hden_pos : 0 < ‖(c : ℂ) + I * (t : ℂ)‖ := by
            have := Complex.abs_re_le_norm ((c : ℂ) + I * (t : ℂ))
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
              Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, abs_of_pos hc0] at this
            linarith
          calc ‖cexp (I * ((t * Real.log y : ℝ) : ℂ)) - 1‖ / ‖(c : ℂ) + I * (t : ℂ)‖
              ≤ (|t| * |Real.log y|) / ‖(c : ℂ) + I * (t : ℂ)‖ :=
                div_le_div_of_nonneg_right h1 hden_pos.le
            _ ≤ (‖(c : ℂ) + I * (t : ℂ)‖ * |Real.log y|) / ‖(c : ℂ) + I * (t : ℂ)‖ :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht_le (abs_nonneg _)) hden_pos.le
            _ = |Real.log y| := mul_div_cancel_left₀ _ hden_pos.ne'
            _ ≤ 1 / T := hlog
        rw [hnum_split]
        calc ‖(((y ^ c - 1 : ℝ) : ℂ)) * cexp (I * ((t * Real.log y : ℝ) : ℂ)) +
              (cexp (I * ((t * Real.log y : ℝ) : ℂ)) - 1)‖ / ‖(c : ℂ) + I * (t : ℂ)‖
            ≤ (‖(((y ^ c - 1 : ℝ) : ℂ)) * cexp (I * ((t * Real.log y : ℝ) : ℂ))‖ +
                ‖cexp (I * ((t * Real.log y : ℝ) : ℂ)) - 1‖) / ‖(c : ℂ) + I * (t : ℂ)‖ :=
              div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
          _ = ‖(((y ^ c - 1 : ℝ) : ℂ)) * cexp (I * ((t * Real.log y : ℝ) : ℂ))‖ /
                ‖(c : ℂ) + I * (t : ℂ)‖ +
              ‖cexp (I * ((t * Real.log y : ℝ) : ℂ)) - 1‖ / ‖(c : ℂ) + I * (t : ℂ)‖ :=
              add_div _ _ _
          _ ≤ (81 / T) * ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ + 1 / T := add_le_add hterm1 hterm2
      have hcont_n : Continuous (fun t : ℝ => ‖(c : ℂ) + I * (t : ℂ)‖⁻¹) := by
        refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
        rw [norm_eq_zero] at h0
        have := congrArg Complex.re h0; simp at this; linarith
      have hint_rhs : IntervalIntegrable (fun t : ℝ => (81 / T) * ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ + 1 / T)
          volume (-T) T :=
        ((hcont_n.intervalIntegrable (-T) T).const_mul _).add intervalIntegrable_const
      have htot_int : ‖∫ t in (-T)..T,
          ((y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) -
            ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)))‖ ≤ 326 := by
        calc ‖∫ t in (-T)..T,
              ((y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) -
                ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)))‖
            ≤ ∫ t in (-T)..T, ‖(y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) -
                ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))‖ :=
              intervalIntegral.norm_integral_le_integral_norm (by linarith)
          _ ≤ ∫ t in (-T)..T, ((81 / T) * ‖(c : ℂ) + I * (t : ℂ)‖⁻¹ + 1 / T) :=
              intervalIntegral.integral_mono_on (by linarith)
                ((hcont_y.sub hcont_1).intervalIntegrable _ _).norm hint_rhs hpt
          _ = (81 / T) * (∫ t in (-T)..T, ‖(c : ℂ) + I * (t : ℂ)‖⁻¹) +
              (∫ _t in (-T)..T, (1 / T : ℝ)) := by
              rw [intervalIntegral.integral_add ((hcont_n.intervalIntegrable _ _).const_mul _)
                intervalIntegrable_const, intervalIntegral.integral_const_mul]
          _ ≤ (81 / T) * (2 + 2 * Real.log T) + 2 := by
              have hc2 : ∫ _t in (-T)..T, (1 / T : ℝ) = 2 := by
                rw [intervalIntegral.integral_const, smul_eq_mul]
                field_simp [hT0.ne']; ring
              rw [hc2]
              linarith [mul_le_mul_of_nonneg_left hinv_int (by positivity : 0 ≤ 81 / T)]
          _ ≤ 326 := by
              have hlogT : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hT0]
              have hdiv_le : (2 + 2 * Real.log T) / T ≤ 4 := by
                rw [div_le_iff₀ hT0]; linarith
              have heq : (81 / T) * (2 + 2 * Real.log T) = 81 * ((2 + 2 * Real.log T) / T) := by
                ring
              linarith
      have h2pi_ge : (6 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T,
              ((y : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) -
                ((1 : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)))‖
          ≤ (2 * Real.pi)⁻¹ * 326 := mul_le_mul_of_nonneg_left htot_int (by positivity)
        _ ≤ 6⁻¹ * 326 := mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num) h2pi_ge) (by norm_num)
        _ ≤ 55 := by norm_num
    have hind : ‖if 1 < y then (1 : ℂ) else 0‖ ≤ 1 := by
      split_ifs <;> simp
    have hrew : perronKernel0 y c T - (if 1 < y then (1 : ℂ) else 0) =
        (perronKernel0 y c T - perronKernel0 1 c T) +
        (perronKernel0 1 c T - (if 1 < y then (1 : ℂ) else 0)) := by ring
    rw [hrew]
    have h1 := norm_add_le (perronKernel0 y c T - perronKernel0 1 c T)
      (perronKernel0 1 c T - (if 1 < y then (1 : ℂ) else 0))
    have h2 := norm_sub_le (perronKernel0 1 c T) (if 1 < y then (1 : ℂ) else 0)
    linarith

private lemma harmonic_sum_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by simp
    rw [hIcc, Finset.sum_insert hnot]
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

/-- **Sharp Truncated Perron Formula for `chebyshevPsiChar χ x`** (exact at `x`, zero `x'` shift!):
for all `q ≥ 1`, `χ : DirichletCharacter ℂ q`, `x ≥ 2`, `c = 1 + 1 / log x`, `T ≥ 1`:
`‖chebyshevPsiChar χ x - truncatedPerronPsi χ x c T‖ ≤ 600 * (x / T * (log x + 1)² + (log x + 1))`. -/
theorem norm_chebyshevPsiChar_sub_truncatedPerron_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x T : ℝ} (hx : 2 ≤ x) (hT : 1 ≤ T) :
    ‖Stage2DirichletAP.chebyshevPsiChar χ x -
      truncatedPerronPsi χ x (1 + 1 / Real.log x) T‖ ≤
      600 * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
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
  -- Step 1: exact termwise series-integral swap on the finite interval `[-T, T]`
  let F : ℕ → ℝ → ℂ := fun n t =>
    if n = 0 then 0
    else (Λ n : ℂ) * χ n * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))
  have hsumR : Summable (fun n : ℕ => Λ n * (n : ℝ) ^ (-c)) := by
    have h := (Stage3RealAnalyticLandau.dirSeriesSummable_iff_real
      (a := fun n => Λ n) (by simp) (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (c : ℂ)).mp
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1))
    simpa using h
  have hF_int : ∀ n : ℕ, IntegrableOn (F n) (Set.Ioc (-T) T) volume := fun n => by
    by_cases hn : n = 0
    · subst hn; simp [F]
    · simp only [F, hn, ↓reduceIte]
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hxnC : ((x / (n : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (div_pos hx0 hnR).ne'
      have hcont : Continuous (fun t : ℝ =>
          (Λ n : ℂ) * χ n * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))) := by
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
          ‖(Λ n : ℂ) * χ n * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))‖ ≤
            (x ^ c / c) * (Λ n * (n : ℝ) ^ (-c)) := fun t _ => by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            Complex.norm_cpow_eq_rpow_re_of_pos hdiv_pos]
        have hre : ((c : ℂ) + I * (t : ℂ)).re = c := by simp
        rw [hre]
        have hden : c ≤ ‖(c : ℂ) + I * (t : ℂ)‖ := by
          simpa [abs_of_pos hc0] using Complex.abs_re_le_norm ((c : ℂ) + I * (t : ℂ))
        have hnum : Λ n * ‖χ n‖ * (x / (n : ℝ)) ^ c ≤ Λ n * (x ^ c * (n : ℝ) ^ (-c)) := by
          rw [Real.div_rpow hx0.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]
          calc Λ n * ‖χ n‖ * (x ^ c * ((n : ℝ) ^ c)⁻¹)
              ≤ Λ n * 1 * (x ^ c * ((n : ℝ) ^ c)⁻¹) := by gcongr; exact χ.norm_le_one _
            _ = Λ n * (x ^ c * ((n : ℝ) ^ c)⁻¹) := by ring
        calc Λ n * ‖χ n‖ * (x / (n : ℝ)) ^ c / ‖(c : ℂ) + I * (t : ℂ)‖
            ≤ (Λ n * (x ^ c * (n : ℝ) ^ (-c))) / c := div_le_div₀ (by positivity) hnum hc0 hden
          _ = (x ^ c / c) * (Λ n * (n : ℝ) ^ (-c)) := by ring
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => ‖F n t‖) (by
        intro t ht; simp only [F, hn, ↓reduceIte, norm_norm]; exact hpt t ht)
      rw [Real.norm_of_nonneg (intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _),
          show T - (-T) = 2 * T by ring, abs_of_pos (by positivity)] at h1
      have h1' : ∫ t in (-T)..T, ‖(Λ n : ℂ) * χ n * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
          ((c : ℂ) + I * (t : ℂ))‖ ≤ (x ^ c / c) * (Λ n * (n : ℝ) ^ (-c)) * (2 * T) := by
        simpa only [F, hn, ↓reduceIte] using h1
      linarith [show (x ^ c / c) * (Λ n * (n : ℝ) ^ (-c)) * (2 * T) =
        2 * T * x ^ c / c * (Λ n * (n : ℝ) ^ (-c)) by ring]
  have hswap := hasSum_integral_of_summable_integral_norm hF_int hF_sum_norm
  have htsum_t : ∀ t : ℝ, ∑' n : ℕ, F n t =
      Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
        (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) := by
    intro t
    have hs : 1 < ((c : ℂ) + I * (t : ℂ)).re := by simp [hc1]
    rw [Stage3ZeroFreeRegion.negLogDerivL_eq_LSeries χ hs]
    set W : ℂ := (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ))
    have hsumL : LSeriesSummable (fun n => χ n * (Λ n : ℂ)) ((c : ℂ) + I * (t : ℂ)) :=
      χ.LSeriesSummable_twist_vonMangoldt hs
    have h1 := (hsumL.hasSum.mul_right W).tsum_eq
    rw [mul_div_assoc]
    change ∑' n : ℕ, F n t =
      (∑' n : ℕ, LSeries.term (fun m => χ m * (Λ m : ℂ)) ((c : ℂ) + I * (t : ℂ)) n) * W
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
      (fun n : ℕ => if n = 0 then (0 : ℂ) else (Λ n : ℂ) * χ n * perronKernel0 (x / (n : ℝ)) c T)
      (truncatedPerronPsi χ x c T) := by
    have hmul := hswap.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
    have hRHS : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in Set.Ioc (-T) T,
          Stage3ZeroFreeRegion.negLogDerivL χ ((c : ℂ) + I * (t : ℂ)) *
            (x : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) / ((c : ℂ) + I * (t : ℂ)) =
        truncatedPerronPsi χ x c T := by
      unfold truncatedPerronPsi; rw [intervalIntegral.integral_of_le (by linarith)]
    rw [hRHS] at hmul
    refine hmul.congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F]
    · simp only [F, hn, ↓reduceIte, perronKernel0]
      rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
          show (fun t : ℝ => (Λ n : ℂ) * χ n * ((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
            ((c : ℂ) + I * (t : ℂ))) =
            fun t : ℝ => ((Λ n : ℂ) * χ n) * (((x / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + I * (t : ℂ)) /
            ((c : ℂ) + I * (t : ℂ))) by funext t; ring,
          intervalIntegral.integral_const_mul]
      ring
  have hpsi_hasSum : HasSum
      (fun n : ℕ => if n = 0 then (0 : ℂ) else (Λ n : ℂ) * χ n * (if (n : ℝ) ≤ x then 1 else 0))
      (Stage2DirichletAP.chebyshevPsiChar χ x) := by
    have hEq : ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        (if n = 0 then (0 : ℂ) else (Λ n : ℂ) * χ n * (if (n : ℝ) ≤ x then 1 else 0)) =
        Stage2DirichletAP.chebyshevPsiChar χ x := by
      unfold Stage2DirichletAP.chebyshevPsiChar
      refine Finset.sum_congr rfl fun n hn => ?_
      rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have hle : (n : ℝ) ≤ x :=
          (Nat.le_floor_iff hx0.le).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
        simp only [hn0, ↓reduceIte, hle, mul_one]; ring
    rw [← hEq]
    refine hasSum_sum_of_ne_finset_zero fun n hn => ?_
    have hge : ⌊x⌋₊ + 1 ≤ n := by simpa using hn
    have hn0 : n ≠ 0 := by omega
    have hgt : ¬ (n : ℝ) ≤ x := by
      intro hle; have := (Nat.le_floor_iff hx0.le).mpr hle; omega
    simp [hn0, hgt]
  -- Step 2: take termwise difference and bound via `norm_perronKernel0`
  let diff : ℕ → ℂ := fun n =>
    if n = 0 then 0
    else (Λ n : ℂ) * χ n * ((if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T)
  have hdiff_hasSum : HasSum diff
      (Stage2DirichletAP.chebyshevPsiChar χ x - truncatedPerronPsi χ x c T) := by
    refine (hpsi_hasSum.sub hperron_hasSum).congr_fun fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [diff]
    · simp only [diff, hn, ↓reduceIte]; ring
  -- Define explicit non-negative majorant `M n` split into near (`n ∈ {⌊x⌋, ⌊x⌋+1}`), mid (`x/2 ≤ n ≤ 2⌊x⌋+2`), and far
  let nearSet : Finset ℕ := {⌊x⌋₊, ⌊x⌋₊ + 1}
  let midSet : Finset ℕ := (Finset.Icc 1 (2 * ⌊x⌋₊ + 2)).filter fun n => n ∉ nearSet ∧ x ≤ 2 * (n : ℝ)
  let M : ℕ → ℝ := fun n =>
    if n = 0 then 0
    else if n ∈ nearSet then 61 * Λ n
    else if n ∈ midSet then 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|)
    else 3 * x ^ c / (Real.pi * T) * (Λ n * (n : ℝ) ^ (-c))
  have hM_summ : Summable M := by
    let tail : ℕ → ℝ := fun n => 3 * x ^ c / (Real.pi * T) * (Λ n * (n : ℝ) ^ (-c))
    have htail : Summable tail := hsumR.mul_left _
    refine htail.congr_cofinite ?_
    have hfin : (({0} ∪ nearSet ∪ midSet : Finset ℕ) : Set ℕ)ᶜ ∈ Filter.cofinite :=
      Filter.mem_cofinite.mpr (by rw [compl_compl]; exact Finset.finite_toSet _)
    filter_upwards [hfin] with n hn
    simp only [Finset.coe_union, Set.mem_compl_iff, Set.mem_union, Finset.mem_coe,
      Finset.mem_singleton, not_or] at hn
    simp [M, tail, hn.1.1, hn.1.2, hn.2]
  have hdiff_le_M : ∀ n : ℕ, ‖diff n‖ ≤ M n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [diff, M]
    · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn1
      have hy0 : 0 < x / (n : ℝ) := div_pos hx0 hnR
      simp only [diff, M, hn, ↓reduceIte]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hχ1 : Λ n * ‖χ n‖ ≤ Λ n := by
        calc Λ n * ‖χ n‖ ≤ Λ n * 1 := mul_le_mul_of_nonneg_left (χ.norm_le_one _)
              ArithmeticFunction.vonMangoldt_nonneg
          _ = Λ n := mul_one _
      by_cases hnear : n ∈ nearSet
      · simp only [hnear, ↓reduceIte]
        have hn_ge_half : x / 2 ≤ (n : ℝ) := by
          simp only [nearSet, Finset.mem_insert, Finset.mem_singleton] at hnear
          have hfl : x - 1 < (⌊x⌋₊ : ℝ) := Nat.sub_one_lt_floor x
          rcases hnear with rfl | rfl
          · linarith
          · push_cast; linarith
        have hy2 : x / (n : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hnR]; linarith
        have hker := norm_perronKernel0_sub_ind_le_uniform hy0 hy2 hc1.le hc3 hT
        have hind_diff : ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T‖ ≤ 61 := by
          have h1 : (if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T =
              -((perronKernel0 (x / (n : ℝ)) c T - (if 1 < x / (n : ℝ) then (1 : ℂ) else 0))) +
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
            (-(perronKernel0 (x / (n : ℝ)) c T - (if 1 < x / (n : ℝ) then (1 : ℂ) else 0)))
            ((if (n : ℝ) ≤ x then (1 : ℂ) else 0) - (if 1 < x / (n : ℝ) then (1 : ℂ) else 0))
          rw [norm_neg] at htri
          linarith
        calc Λ n * ‖χ n‖ * ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T‖
            ≤ Λ n * 61 := mul_le_mul hχ1 hind_diff (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
          _ = 61 * Λ n := by ring
      · simp only [hnear, ↓reduceIte]
        have hne_x : (n : ℝ) ≠ x := by
          intro hEq
          apply hnear
          have hfl : ⌊x⌋₊ = n := by rw [← hEq, Nat.floor_natCast]
          simp [nearSet, hfl]
        have hker : ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T‖ ≤
            (x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|) := by
          rcases lt_or_gt_of_ne hne_x with hlt | hgt
          · have h1 : 1 < x / (n : ℝ) := (one_lt_div hnR).mpr hlt
            simp only [hlt.le, ↓reduceIte]
            rw [norm_sub_rev]
            exact norm_perronKernel0_gt_one h1 hc0 hT0
          · have h1 : x / (n : ℝ) < 1 := (div_lt_one hnR).mpr hgt
            simp only [not_le.mpr hgt, ↓reduceIte, zero_sub, norm_neg]
            exact norm_perronKernel0_lt_one hy0 h1 hc0 hT0
        by_cases hmid : n ∈ midSet
        · simp only [hmid, ↓reduceIte]
          obtain ⟨hmem, -, h2n⟩ := Finset.mem_filter.mp hmid
          have hn_le : (n : ℝ) ≤ 2 * x + 2 := by
            have hle : n ≤ 2 * ⌊x⌋₊ + 2 := (Finset.mem_Icc.mp hmem).2
            have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
            have : (n : ℝ) ≤ 2 * (⌊x⌋₊ : ℝ) + 2 := by exact_mod_cast hle
            linarith
          have hΛ_le : Λ n ≤ Real.log (2 * x + 2) :=
            ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnR hn_le)
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
          calc Λ n * ‖χ n‖ * ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T‖
              ≤ Λ n * ((x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|)) :=
                mul_le_mul hχ1 hker (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
            _ ≤ Real.log (2 * x + 2) * (8 / (Real.pi * T * (|x - (n : ℝ)| / (2 * x + 2)))) := by
                refine mul_le_mul hΛ_le ?_ (by positivity) (Real.log_nonneg (by linarith))
                refine div_le_div₀ (by positivity) hyc (by positivity) ?_
                exact mul_le_mul_of_nonneg_left hlog_lb (by positivity)
            _ = 8 * (2 * x + 2) * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) := by
                field_simp [Real.pi_ne_zero, hT0.ne', hdiff_pos.ne', (show (2 * x + 2 : ℝ) ≠ 0 by linarith)]
            _ ≤ 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) := by
                refine div_le_div_of_nonneg_right ?_ (by positivity)
                have : 8 * (2 * x + 2) ≤ 24 * x := by linarith
                exact mul_le_mul_of_nonneg_right this (Real.log_nonneg (by linarith))
        · -- Far branch: either `2 * n < x` (so `x / n > 2`) OR `n > 2 * ⌊x⌋₊ + 2 > 2 * x` (so `x / n < 1 / 2`)
          simp only [hmid, ↓reduceIte]
          have hlog_ge : (1 / 3 : ℝ) < |Real.log (x / (n : ℝ))| := by
            by_cases h2n : 2 * (n : ℝ) < x
            · have hgt2 : 2 < x / (n : ℝ) := (lt_div_iff₀ hnR).mpr h2n
              rw [abs_of_pos (Real.log_pos (by linarith))]
              have h1 := hlog2.trans (Real.log_lt_log (by norm_num) hgt2)
              linarith
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
          calc Λ n * ‖χ n‖ * ‖(if (n : ℝ) ≤ x then (1 : ℂ) else 0) - perronKernel0 (x / (n : ℝ)) c T‖
              ≤ Λ n * ((x / (n : ℝ)) ^ c / (Real.pi * T * |Real.log (x / (n : ℝ))|)) :=
                mul_le_mul hχ1 hker (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
            _ ≤ Λ n * ((x / (n : ℝ)) ^ c / (Real.pi * T * (1 / 3))) := by
                refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
                exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le c) (by positivity)
                  (mul_le_mul_of_nonneg_left hlog_ge.le (by positivity))
            _ = 3 * x ^ c / (Real.pi * T) * (Λ n * (n : ℝ) ^ (-c)) := by
                rw [Real.div_rpow hx0.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]
                field_simp [Real.pi_ne_zero, hT0.ne']
  -- Step 3: bound `∑' n, M n` by bounding each of the three pieces (near, mid, far)
  have hM_le_split : ∀ n : ℕ, M n ≤
      (if n ∈ nearSet then 61 * Λ n else 0) +
      (if n ∈ midSet then 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) else 0) +
      3 * x ^ c / (Real.pi * T) * (Λ n * (n : ℝ) ^ (-c)) := by
    intro n
    have hnn_n : 0 ≤ 61 * Λ n := mul_nonneg (by norm_num) ArithmeticFunction.vonMangoldt_nonneg
    have hnn_m : 0 ≤ 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) :=
      div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith))) (by positivity)
    have hnn_far : 0 ≤ 3 * x ^ c / (Real.pi * T) * (Λ n * (n : ℝ) ^ (-c)) :=
      mul_nonneg (by positivity) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    dsimp only [M]
    split_ifs <;> linarith
  have hnear_summ : Summable (fun n : ℕ => if n ∈ nearSet then 61 * Λ n else 0) :=
    summable_of_ne_finset_zero (s := nearSet) fun n hn => if_neg hn
  have hmid_summ : Summable (fun n : ℕ =>
      if n ∈ midSet then 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) else 0) :=
    summable_of_ne_finset_zero (s := midSet) fun n hn => if_neg hn
  have hfar_summ : Summable (fun n : ℕ => 3 * x ^ c / (Real.pi * T) * (Λ n * (n : ℝ) ^ (-c))) :=
    hsumR.mul_left _
  have hM_tsum_le : ∑' n : ℕ, M n ≤
      (∑ n ∈ nearSet, 61 * Λ n) +
      (∑ n ∈ midSet, 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|)) +
      (3 * x ^ c / (Real.pi * T) * ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c)) := by
    have h1 := hM_summ.tsum_le_tsum hM_le_split ((hnear_summ.add hmid_summ).add hfar_summ)
    rw [(hnear_summ.add hmid_summ).tsum_add hfar_summ, hnear_summ.tsum_add hmid_summ,
        tsum_eq_sum (s := nearSet) (fun n hn => if_neg hn),
        tsum_eq_sum (s := midSet) (fun n hn => if_neg hn),
        tsum_mul_left] at h1
    refine h1.trans_eq ?_
    congr 1; congr 1
    · exact Finset.sum_congr rfl fun n hn => if_pos hn
    · exact Finset.sum_congr rfl fun n hn => if_pos hn
  -- Bound the near sum (≤ 244 * (log x + 1))
  have hlog_2x2 : Real.log (2 * x + 2) ≤ 2 * (Real.log x + 1) := by
    have hle : 2 * x + 2 ≤ 4 * x := by linarith
    have h1 : Real.log (2 * x + 2) ≤ Real.log (4 * x) := Real.log_le_log (by positivity) hle
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
    linarith
  have hnear_bd : ∑ n ∈ nearSet, 61 * Λ n ≤ 244 * (Real.log x + 1) := by
    rw [show nearSet = insert ⌊x⌋₊ {⌊x⌋₊ + 1} from rfl,
        Finset.sum_insert (by simp), Finset.sum_singleton]
    have hfl_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hfl_pos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast (Nat.floor_pos.mpr hx1)
    have h1 : Λ ⌊x⌋₊ ≤ Real.log (2 * x + 2) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hfl_pos (by linarith))
    have h2 : Λ (⌊x⌋₊ + 1) ≤ Real.log (2 * x + 2) := by
      refine ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by positivity) ?_)
      push_cast; linarith
    linarith
  -- Bound the far sum (≤ 60 * (x / T) * (log x + 1))
  have hfar_bd : 3 * x ^ c / (Real.pi * T) * (∑' n : ℕ, Λ n * (n : ℝ) ^ (-c)) ≤
      60 * (x / T) * (Real.log x + 1) := by
    have htsum := Stage4ExplicitFormula.tsum_vonMangoldt_mul_rpow_le hc1
    have hc_sub : c - 1 = 1 / Real.log x := by rw [hc_def]; ring
    have htsum' : ∑' n : ℕ, Λ n * (n : ℝ) ^ (-c) ≤ 18 * Real.log x := by
      have h1 : 6 * c / (c - 1) = 6 * c * Real.log x := by
        rw [hc_sub]; field_simp [hlogx_pos.ne']
      rw [h1] at htsum
      nlinarith
    have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    calc 3 * x ^ c / (Real.pi * T) * (∑' n : ℕ, Λ n * (n : ℝ) ^ (-c))
        ≤ 3 * (3 * x) / (3 * T) * (18 * Real.log x) := by
          refine mul_le_mul ?_ htsum'
            (tsum_nonneg fun n => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by positivity)
          refine div_le_div₀ (by positivity) (by linarith) (by positivity)
            (mul_le_mul_of_nonneg_right hpi3 hT0.le)
      _ = 54 * (x / T) * Real.log x := by field_simp [hT0.ne']; ring
      _ ≤ 60 * (x / T) * (Real.log x + 1) := by
          have : 0 ≤ x / T := by positivity
          nlinarith
  -- Bound the mid harmonic sum `∑_{n ∈ midSet} 1 / |x - n| ≤ 6 * (log x + 1)`
  have hmid_harm : ∑ n ∈ midSet, (1 : ℝ) / |x - (n : ℝ)| ≤ 6 * (Real.log x + 1) := by
    let midLo : Finset ℕ := midSet.filter fun n => n < ⌊x⌋₊
    let midHi : Finset ℕ := midSet.filter fun n => ⌊x⌋₊ + 1 < n
    have hcov : midSet ⊆ midLo ∪ midHi := by
      intro n hn
      have hnot_near : n ∉ nearSet := (Finset.mem_filter.mp hn).2.1
      have hne1 : n ≠ ⌊x⌋₊ := fun h => hnot_near (by simp [nearSet, h])
      have hne2 : n ≠ ⌊x⌋₊ + 1 := fun h => hnot_near (by simp [nearSet, h])
      rw [Finset.mem_union]
      by_cases hlt : n < ⌊x⌋₊
      · exact Or.inl (Finset.mem_filter.mpr ⟨hn, hlt⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hn, by omega⟩)
    have hM_ge1 : 1 ≤ ⌊x⌋₊ + 2 := by omega
    have hM_le : ((⌊x⌋₊ + 2 : ℕ) : ℝ) ≤ 2 * x := by
      push_cast; linarith [Nat.floor_le hx0.le]
    have hlo_bd : ∑ n ∈ midLo, (1 : ℝ) / |x - (n : ℝ)| ≤ 1 + Real.log (2 * x) := by
      have hle_k : ∑ n ∈ midLo, (1 : ℝ) / |x - (n : ℝ)| ≤
          ∑ n ∈ midLo, (1 : ℝ) / ((⌊x⌋₊ - n : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hlt : n < ⌊x⌋₊ := (Finset.mem_filter.mp hn).2
        have hk_pos : (0 : ℝ) < ((⌊x⌋₊ - n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x⌋₊ - n)
        have hle_abs : ((⌊x⌋₊ - n : ℕ) : ℝ) ≤ |x - (n : ℝ)| := by
          have hltR : (n : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hlt
          rw [Nat.cast_sub hlt.le, abs_of_pos (by linarith [Nat.floor_le hx0.le])]
          linarith [Nat.floor_le hx0.le]
        exact div_le_div_of_nonneg_left zero_le_one hk_pos hle_abs
      have hinj : ∑ n ∈ midLo, (1 : ℝ) / ((⌊x⌋₊ - n : ℕ) : ℝ) ≤
          ∑ k ∈ Finset.Icc 1 (⌊x⌋₊ + 2), (1 : ℝ) / (k : ℝ) := by
        have h1 : ∑ n ∈ midLo, (1 : ℝ) / ((⌊x⌋₊ - n : ℕ) : ℝ) =
            ∑ k ∈ midLo.image (fun n => ⌊x⌋₊ - n), (1 : ℝ) / (k : ℝ) := by
          symm
          refine Finset.sum_image fun a ha b hb hEq => ?_
          have ha' : a < ⌊x⌋₊ := (Finset.mem_filter.mp ha).2
          have hb' : b < ⌊x⌋₊ := (Finset.mem_filter.mp hb).2
          omega
        rw [h1]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
        have hlt : n < ⌊x⌋₊ := (Finset.mem_filter.mp hn).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      calc ∑ n ∈ midLo, (1 : ℝ) / |x - (n : ℝ)|
          ≤ ∑ n ∈ midLo, (1 : ℝ) / ((⌊x⌋₊ - n : ℕ) : ℝ) := hle_k
        _ ≤ ∑ k ∈ Finset.Icc 1 (⌊x⌋₊ + 2), (1 : ℝ) / (k : ℝ) := hinj
        _ ≤ 1 + Real.log ((⌊x⌋₊ + 2 : ℕ) : ℝ) := harmonic_sum_le_one_add_log _ hM_ge1
        _ ≤ 1 + Real.log (2 * x) := by
            linarith [Real.log_le_log (by positivity : (0 : ℝ) < ((⌊x⌋₊ + 2 : ℕ) : ℝ)) hM_le]
    have hhi_bd : ∑ n ∈ midHi, (1 : ℝ) / |x - (n : ℝ)| ≤ 1 + Real.log (2 * x) := by
      have hle_k : ∑ n ∈ midHi, (1 : ℝ) / |x - (n : ℝ)| ≤
          ∑ n ∈ midHi, (1 : ℝ) / ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hgt : ⌊x⌋₊ + 1 < n := (Finset.mem_filter.mp hn).2
        have hk_pos : (0 : ℝ) < ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < n - (⌊x⌋₊ + 1))
        have hle_abs : ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) ≤ |x - (n : ℝ)| := by
          have hfl : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
          have hcast : ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) = (n : ℝ) - ((⌊x⌋₊ : ℝ) + 1) := by
            rw [Nat.cast_sub hgt.le]; push_cast; rfl
          rw [hcast, abs_sub_comm, abs_of_pos (by linarith [show ((⌊x⌋₊ + 1 : ℕ) : ℝ) < (n : ℝ) by exact_mod_cast hgt])]
          linarith
        exact div_le_div_of_nonneg_left zero_le_one hk_pos hle_abs
      have hinj : ∑ n ∈ midHi, (1 : ℝ) / ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) ≤
          ∑ k ∈ Finset.Icc 1 (⌊x⌋₊ + 2), (1 : ℝ) / (k : ℝ) := by
        have h1 : ∑ n ∈ midHi, (1 : ℝ) / ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) =
            ∑ k ∈ midHi.image (fun n => n - (⌊x⌋₊ + 1)), (1 : ℝ) / (k : ℝ) := by
          symm
          refine Finset.sum_image fun a ha b hb hEq => ?_
          have ha' : ⌊x⌋₊ + 1 < a := (Finset.mem_filter.mp ha).2
          have hb' : ⌊x⌋₊ + 1 < b := (Finset.mem_filter.mp hb).2
          omega
        rw [h1]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
        have hgt : ⌊x⌋₊ + 1 < n := (Finset.mem_filter.mp hn).2
        have hle : n ≤ 2 * ⌊x⌋₊ + 2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      calc ∑ n ∈ midHi, (1 : ℝ) / |x - (n : ℝ)|
          ≤ ∑ n ∈ midHi, (1 : ℝ) / ((n - (⌊x⌋₊ + 1) : ℕ) : ℝ) := hle_k
        _ ≤ ∑ k ∈ Finset.Icc 1 (⌊x⌋₊ + 2), (1 : ℝ) / (k : ℝ) := hinj
        _ ≤ 1 + Real.log ((⌊x⌋₊ + 2 : ℕ) : ℝ) := harmonic_sum_le_one_add_log _ hM_ge1
        _ ≤ 1 + Real.log (2 * x) := by
            linarith [Real.log_le_log (by positivity : (0 : ℝ) < ((⌊x⌋₊ + 2 : ℕ) : ℝ)) hM_le]
    have hlog2x : 1 + Real.log (2 * x) ≤ 2 * (Real.log x + 1) := by
      rw [Real.log_mul (by norm_num) hx0.ne']
      linarith [Real.log_two_lt_d9]
    have hunion : ∑ n ∈ midSet, (1 : ℝ) / |x - (n : ℝ)| ≤
        (∑ n ∈ midLo, (1 : ℝ) / |x - (n : ℝ)|) + (∑ n ∈ midHi, (1 : ℝ) / |x - (n : ℝ)|) := by
      calc ∑ n ∈ midSet, (1 : ℝ) / |x - (n : ℝ)|
          ≤ ∑ n ∈ midLo ∪ midHi, (1 : ℝ) / |x - (n : ℝ)| :=
            Finset.sum_le_sum_of_subset_of_nonneg hcov fun _ _ _ => by positivity
        _ ≤ (∑ n ∈ midLo, (1 : ℝ) / |x - (n : ℝ)|) + (∑ n ∈ midHi, (1 : ℝ) / |x - (n : ℝ)|) := by
            rw [← Finset.sum_union_inter]
            linarith [Finset.sum_nonneg (s := midLo ∩ midHi)
              (f := fun n : ℕ => (1 : ℝ) / |x - (n : ℝ)|) fun _ _ => by positivity]
    linarith
  -- Bound the mid sum (≤ 96 * (x / T) * (log x + 1)^2)
  have hmid_bd :
      ∑ n ∈ midSet, 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) ≤
        96 * (x / T) * (Real.log x + 1) ^ 2 := by
    have hpull :
        ∑ n ∈ midSet, 24 * x * Real.log (2 * x + 2) / (Real.pi * T * |x - (n : ℝ)|) =
          (24 * x * Real.log (2 * x + 2) / (Real.pi * T)) *
            ∑ n ∈ midSet, (1 : ℝ) / |x - (n : ℝ)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => by ring
    rw [hpull]
    have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hcoef_le : 24 * x * Real.log (2 * x + 2) / (Real.pi * T) ≤
        16 * (x / T) * (Real.log x + 1) := by
      calc 24 * x * Real.log (2 * x + 2) / (Real.pi * T)
          ≤ 24 * x * (2 * (Real.log x + 1)) / (3 * T) := by
            refine div_le_div₀ (by positivity)
              (mul_le_mul_of_nonneg_left hlog_2x2 (by positivity))
              (by positivity) (mul_le_mul_of_nonneg_right hpi3 hT0.le)
        _ = 16 * (x / T) * (Real.log x + 1) := by field_simp [hT0.ne']; ring
    calc (24 * x * Real.log (2 * x + 2) / (Real.pi * T)) * ∑ n ∈ midSet, (1 : ℝ) / |x - (n : ℝ)|
        ≤ (16 * (x / T) * (Real.log x + 1)) * (6 * (Real.log x + 1)) :=
          mul_le_mul hcoef_le hmid_harm (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = 96 * (x / T) * (Real.log x + 1) ^ 2 := by ring
  -- Combine all three bounds
  have hdiff_summ : Summable (fun n : ℕ => ‖diff n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdiff_le_M hM_summ
  have htsum_eq : ∑' n : ℕ, diff n =
      Stage2DirichletAP.chebyshevPsiChar χ x - truncatedPerronPsi χ x c T := hdiff_hasSum.tsum_eq
  rw [← htsum_eq]
  have htot := (norm_tsum_le_tsum_norm hdiff_summ).trans
    ((hdiff_summ.tsum_le_tsum hdiff_le_M hM_summ).trans hM_tsum_le)
  have hlog_sq : Real.log x + 1 ≤ (Real.log x + 1) ^ 2 := by nlinarith
  have hfar_sq : 60 * (x / T) * (Real.log x + 1) ≤ 60 * (x / T) * (Real.log x + 1) ^ 2 := by
    have : 0 ≤ 60 * (x / T) := by positivity
    nlinarith
  have hnn1 : 0 ≤ x / T * (Real.log x + 1) ^ 2 := by positivity
  have hnn2 : 0 ≤ Real.log x + 1 := by positivity
  linarith

/-! ## Section 3C: De-Smoothing via `chebyshevRamp_diff_sandwich` and `psi1Char` Differences -/

/-- **De-Smoothing of `RHDirect.chebyshevRamp` via `Stage3RealAnalyticLandau.chebyshevRamp_diff_sandwich`**:
if `|chebyshevRamp y - y * log y + (1 + γ) * y| ≤ C * y ^ θ` for all `y ≥ 1` (`0 < θ < 1`, `C ≥ 0`),
then `Stage3RealAnalyticLandau.chebyshevRamp_diff_sandwich` unconditionally recovers
`|chebyshevPsi x - x| ≤ (4 * C + 1) * x ^ ((1 + θ) / 2)` for all `x ≥ 4`. -/
theorem abs_psi_sub_id_of_chebyshevRamp_rpow_sandwich {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 < θ)
    (hθ1 : θ < 1)
    (hramp : ∀ y : ℝ, 1 ≤ y →
      |RHDirect.chebyshevRamp y - y * Real.log y +
        (1 + Real.eulerMascheroniConstant) * y| ≤ C * y ^ θ)
    {x : ℝ} (hx : 4 ≤ x) :
    |RHDirect.chebyshevPsi x - x| ≤ (4 * C + 1) * x ^ ((1 + θ) / 2) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  set η : ℝ := x ^ (-(1 - θ) / 2) with hη_def
  have hη0 : 0 < η := Real.rpow_pos_of_pos hx0 _
  have hη_le1 : η ≤ 1 := by
    rw [hη_def]
    calc x ^ (-(1 - θ) / 2) ≤ x ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = 1 := Real.rpow_zero x
  have h1η_pos : 0 < 1 + η := by linarith
  have h1η_le2 : 1 + η ≤ 2 := by linarith
  have hE : ∀ y : ℝ, 1 ≤ y →
      |RHDirect.chebyshevRamp y / y - Real.log y + (1 + Real.eulerMascheroniConstant)| ≤
        C * y ^ (θ - 1) := by
    intro y hy
    have hy0 : 0 < y := by linarith
    have heq : RHDirect.chebyshevRamp y / y - Real.log y + (1 + Real.eulerMascheroniConstant) =
        (RHDirect.chebyshevRamp y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y) / y := by
      field_simp [hy0.ne']
    rw [heq, abs_div, abs_of_pos hy0]
    calc |RHDirect.chebyshevRamp y - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y| / y
        ≤ (C * y ^ θ) / y := div_le_div_of_nonneg_right (hramp y hy) hy0.le
      _ = C * (y ^ θ / y ^ (1 : ℝ)) := by rw [Real.rpow_one]; ring
      _ = C * y ^ (θ - 1) := by rw [← Real.rpow_sub hy0]
  have hpow_main : x * x ^ (θ - 1) / η = x ^ ((1 + θ) / 2) := by
    calc x * x ^ (θ - 1) / η
        = x ^ (1 : ℝ) * x ^ (θ - 1) / x ^ (-(1 - θ) / 2) := by rw [Real.rpow_one, hη_def]
      _ = x ^ (1 + (θ - 1)) / x ^ (-(1 - θ) / 2) := by rw [← Real.rpow_add hx0]
      _ = x ^ (1 + (θ - 1) - -(1 - θ) / 2) := by rw [← Real.rpow_sub hx0]
      _ = x ^ ((1 + θ) / 2) := by congr 1; ring
  have hpow_eta : η * x = x ^ ((1 + θ) / 2) := by
    calc η * x = x ^ (-(1 - θ) / 2) * x ^ (1 : ℝ) := by rw [Real.rpow_one, hη_def]
      _ = x ^ (-(1 - θ) / 2 + 1) := by rw [← Real.rpow_add hx0]
      _ = x ^ ((1 + θ) / 2) := by congr 1; ring
  rw [abs_le]
  constructor
  · -- Lower bound via `chebyshevRamp_diff_sandwich` on `[x / (1 + η), x]`
    set a : ℝ := x / (1 + η)
    have ha1 : 1 ≤ a := by
      change 1 ≤ x / (1 + η); rw [one_le_div h1η_pos]; linarith
    have hax : a ≤ x := div_le_self hx0.le (by linarith)
    have ha0 : 0 < a := by linarith
    have hsnd := (Stage3RealAnalyticLandau.chebyshevRamp_diff_sandwich ha1 hax).2
    have hwt : 1 / a - 1 / x = η / x := by simp only [a]; field_simp [hx0.ne', h1η_pos.ne']; ring
    rw [hwt] at hsnd
    have hlog_xa : Real.log x - Real.log a = Real.log (1 + η) := by
      rw [← Real.log_div hx0.ne' ha0.ne']
      congr 1; simp only [a]; field_simp [hx0.ne', h1η_pos.ne']
    have hlog_lb : η / (1 + η) ≤ Real.log (1 + η) := by
      have h1 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1η_pos)
      rw [Real.log_inv] at h1
      have h2 : 1 - (1 + η)⁻¹ = η / (1 + η) := by field_simp [h1η_pos.ne']; ring
      linarith
    have ha_pow : a ^ (θ - 1) ≤ 2 * x ^ (θ - 1) := by
      have h1 : x / 2 ≤ a := div_le_div_of_nonneg_left hx0.le h1η_pos h1η_le2
      have h2 : a ^ (θ - 1) ≤ (x / 2) ^ (θ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
      have h3 : (x / 2) ^ (θ - 1) = (2 : ℝ) ^ (1 - θ) * x ^ (θ - 1) := by
        rw [Real.div_rpow hx0.le (by norm_num : (0 : ℝ) ≤ 2),
          show (2 : ℝ) ^ (θ - 1) = ((2 : ℝ) ^ (1 - θ))⁻¹ by
            rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring,
          div_inv_eq_mul, mul_comm]
      have h4 : (2 : ℝ) ^ (1 - θ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 - θ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h5 : (2 : ℝ) ^ (1 - θ) * x ^ (θ - 1) ≤ 2 * x ^ (θ - 1) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hx0.le _)
      linarith
    have hEx := abs_le.mp (hE x hx1)
    have hEa := abs_le.mp (hE a ha1)
    have hdiff_lb : η / (1 + η) - 3 * C * x ^ (θ - 1) ≤
        RHDirect.chebyshevRamp x / x - RHDirect.chebyshevRamp a / a := by
      have hCa : C * a ^ (θ - 1) ≤ 2 * C * x ^ (θ - 1) := by
        have := mul_le_mul_of_nonneg_left ha_pow hC; linarith
      linarith
    have hmul := mul_le_mul_of_nonneg_left (hdiff_lb.trans hsnd) (div_nonneg hx0.le hη0.le)
    have hLHS : x / η * (η / (1 + η) - 3 * C * x ^ (θ - 1)) =
        x / (1 + η) - 3 * C * x ^ ((1 + θ) / 2) := by
      rw [mul_sub]
      have h1 : x / η * (η / (1 + η)) = x / (1 + η) := by field_simp [hη0.ne', h1η_pos.ne']
      have h2 : x / η * (3 * C * x ^ (θ - 1)) = 3 * C * (x * x ^ (θ - 1) / η) := by ring
      rw [h1, h2, hpow_main]
    have hRHS : x / η * (RHDirect.chebyshevPsi x * (η / x)) = RHDirect.chebyshevPsi x := by
      field_simp [hx0.ne', hη0.ne']
    rw [hLHS, hRHS] at hmul
    have hx_sub : x - η * x ≤ x / (1 + η) := by
      rw [le_div_iff₀ h1η_pos]
      nlinarith [mul_nonneg (sq_nonneg η) hx0.le]
    have hCpow : 0 ≤ C * x ^ ((1 + θ) / 2) := mul_nonneg hC (Real.rpow_nonneg hx0.le _)
    linarith [hpow_eta]
  · -- Upper bound via `chebyshevRamp_diff_sandwich` on `[x, x * (1 + η)]`
    set b : ℝ := x * (1 + η)
    have hxb : x ≤ b := le_mul_of_one_le_right hx0.le (by linarith)
    have hb1 : 1 ≤ b := hx1.trans hxb
    have hb0 : 0 < b := by linarith
    have hsnd := (Stage3RealAnalyticLandau.chebyshevRamp_diff_sandwich hx1 hxb).1
    have hwt : 1 / x - 1 / b = η / (x * (1 + η)) := by
      simp only [b]; field_simp [hx0.ne', h1η_pos.ne']; ring
    rw [hwt] at hsnd
    have hlog_bx : Real.log b - Real.log x = Real.log (1 + η) := by
      rw [← Real.log_div hb0.ne' hx0.ne']
      congr 1; simp only [b]; field_simp [hx0.ne']
    have hlog_ub : Real.log (1 + η) ≤ η := by
      linarith [Real.log_le_sub_one_of_pos h1η_pos]
    have hb_pow : b ^ (θ - 1) ≤ x ^ (θ - 1) :=
      Real.rpow_le_rpow_of_nonpos hx0 hxb (by linarith)
    have hEx := abs_le.mp (hE x hx1)
    have hEb := abs_le.mp (hE b hb1)
    have hdiff_ub : RHDirect.chebyshevRamp b / b - RHDirect.chebyshevRamp x / x ≤
        η + 2 * C * x ^ (θ - 1) := by
      have hCb : C * b ^ (θ - 1) ≤ C * x ^ (θ - 1) := mul_le_mul_of_nonneg_left hb_pow hC
      linarith
    have hfac_pos : 0 ≤ x * (1 + η) / η := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hsnd.trans hdiff_ub) hfac_pos
    have hLHS : x * (1 + η) / η * (RHDirect.chebyshevPsi x * (η / (x * (1 + η)))) =
        RHDirect.chebyshevPsi x := by
      field_simp [hx0.ne', hη0.ne', h1η_pos.ne']
    have hRHS : x * (1 + η) / η * (η + 2 * C * x ^ (θ - 1)) =
        x + η * x + (1 + η) * (2 * C * x ^ ((1 + θ) / 2)) := by
      have h1 : x * (1 + η) / η * η = x + η * x := by field_simp [hη0.ne']
      have h2 : x * (1 + η) / η * (2 * C * x ^ (θ - 1)) =
          (1 + η) * (2 * C * (x * x ^ (θ - 1) / η)) := by ring
      rw [mul_add, h1, h2, hpow_main]
    rw [hLHS, hRHS] at hmul
    have hCpow : 0 ≤ C * x ^ ((1 + θ) / 2) := mul_nonneg hC (Real.rpow_nonneg hx0.le _)
    have h1η_mul : (1 + η) * (2 * C * x ^ ((1 + θ) / 2)) ≤ 4 * C * x ^ ((1 + θ) / 2) := by
      nlinarith
    linarith [hpow_eta]

/-- Exact finite-difference de-smoothing identity for `Stage4ExplicitFormula.psi1Char`:
for any `χ mod q`, `0 < x`, `0 < h`:
`‖(psi1Char χ (x + h) - psi1Char χ x) / h - chebyshevPsiChar χ x‖ ≤ chebyshevPsi (x + h) - chebyshevPsi x`. -/
theorem norm_psi1Char_diff_sub_chebyshevPsiChar_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖(Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x) / (h : ℂ) -
        Stage2DirichletAP.chebyshevPsiChar χ x‖ ≤
      RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x := by
  have hx1_le : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_mono (by linarith)
  have hsub : Finset.range (⌊x⌋₊ + 1) ⊆ Finset.range (⌊x + h⌋₊ + 1) :=
    Finset.range_mono (Nat.add_le_add_right hx1_le 1)
  have hpsi1_x : Stage4ExplicitFormula.psi1Char χ x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1),
        (Λ n : ℂ) * χ n * ((max (x - (n : ℝ)) 0 : ℝ) : ℂ) := by
    unfold Stage4ExplicitFormula.psi1Char
    refine Finset.sum_subset hsub fun n _ hnot => ?_
    have hge : ⌊x⌋₊ + 1 ≤ n := by simpa using hnot
    have hgt : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hge)
    rw [max_eq_right (by linarith)]; simp
  have hpsi_x : Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1),
        if n ≤ ⌊x⌋₊ then (Λ n : ℂ) * χ n else 0 := by
    unfold Stage2DirichletAP.chebyshevPsiChar
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range (⌊x + h⌋₊ + 1)).filter (fun n => n ≤ ⌊x⌋₊) =
        Finset.range (⌊x⌋₊ + 1) := by
      ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hhhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hdiff_eq :
      (Stage4ExplicitFormula.psi1Char χ (x + h) - Stage4ExplicitFormula.psi1Char χ x) / (h : ℂ) -
        Stage2DirichletAP.chebyshevPsiChar χ x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1),
        (Λ n : ℂ) * χ n *
          ((((max (x + h - (n : ℝ)) 0 - max (x - (n : ℝ)) 0) / h -
            if n ≤ ⌊x⌋₊ then (1 : ℝ) else 0 : ℝ) : ℂ)) := by
    rw [hpsi1_x, hpsi_x]
    unfold Stage4ExplicitFormula.psi1Char
    rw [← Finset.sum_sub_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> (push_cast; field_simp [hhhC]; try ring)
  have hpsi_diff : RHDirect.chebyshevPsi (x + h) - RHDirect.chebyshevPsi x =
      ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), if n ≤ ⌊x⌋₊ then (0 : ℝ) else Λ n := by
    unfold RHDirect.chebyshevPsi
    have hsplit : ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n =
        (∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) +
        ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), if n ≤ ⌊x⌋₊ then (0 : ℝ) else Λ n := by
      have hsum_ite : ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), Λ n =
          (∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), if n ≤ ⌊x⌋₊ then Λ n else 0) +
          ∑ n ∈ Finset.range (⌊x + h⌋₊ + 1), if n ≤ ⌊x⌋₊ then (0 : ℝ) else Λ n := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
      rw [hsum_ite, ← Finset.sum_filter]
      have hfilt : (Finset.range (⌊x + h⌋₊ + 1)).filter (fun n => n ≤ ⌊x⌋₊) =
          Finset.range (⌊x⌋₊ + 1) := by
        ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt]
    linarith
  rw [hdiff_eq, hpsi_diff]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.norm_eq_abs]
  by_cases hn : n ≤ ⌊x⌋₊
  · have hle_x : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hn
    have hm1 : max (x + h - (n : ℝ)) 0 = x + h - (n : ℝ) := max_eq_left (by linarith)
    have hm2 : max (x - (n : ℝ)) 0 = x - (n : ℝ) := max_eq_left (by linarith)
    simp only [hn, ↓reduceIte, hm1, hm2]
    have h0 : (x + h - (n : ℝ) - (x - (n : ℝ))) / h - 1 = 0 := by field_simp [hh.ne']; ring
    rw [h0, abs_zero, mul_zero]
  · simp only [hn, ↓reduceIte, sub_zero]
    have hgt_x : x < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast (by omega : ⌊x⌋₊ + 1 ≤ n))
    rw [max_eq_right (by linarith : x - (n : ℝ) ≤ 0), sub_zero]
    have hle_h : max (x + h - (n : ℝ)) 0 ≤ h := max_le (by linarith) hh.le
    have habs_le : |max (x + h - (n : ℝ)) 0 / h| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg (le_max_right _ _) hh.le), div_le_one hh]
      exact hle_h
    calc Λ n * ‖χ n‖ * |max (x + h - (n : ℝ)) 0 / h|
        ≤ Λ n * 1 * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (χ.norm_le_one _)
            ArithmeticFunction.vonMangoldt_nonneg) habs_le (abs_nonneg _)
            (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg zero_le_one)
      _ = Λ n := by ring

/-! ## Section 3D: `MeromorphicLogDerivPackage` → Smoothed Explicit Formula,
`TruncatedExplicitFormulaPackage` & `Stage2PrimePairs` Discharge -/

open Classical in
/-- **Textbook Meromorphic Log-Derivative Partial-Fraction Package in a Zero-Free Strip `[1 - θ, θ]`**:
encapsulates the classical Hadamard partial-fraction representation, Riemann–von Mangoldt zero count,
and unit-strip zero density for `-L'/L(s, χ)` across all moduli `q ≥ 1` and characters `χ mod q`
(Davenport Ch. 12, 15, 16; Montgomery–Vaughan Theorem 10.13 & Lemma 12.1). -/
structure MeromorphicLogDerivPackage (θ B C_N C_1 : ℝ) : Prop where
  theta_ge_half : 1 / 2 ≤ θ
  theta_lt_one : θ < 1
  B_nonneg : 0 ≤ B
  CN_nonneg : 0 ≤ C_N
  C1_nonneg : 0 ≤ C_1
  zeros_and_partial_fraction :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ), 1 ≤ T →
      ∃ Z : Finset ℂ,
        (∀ ρ ∈ Z, 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ ∧ |ρ.im| ≤ T) ∧
        Stage3ZeroFreeRegion.ZeroCountBound C_N Z q ∧
        (∀ t : ℝ, |t| ≤ T →
          ((Z.filter fun ρ => |ρ.im - t| ≤ 1).card : ℝ) ≤
            C_1 * Real.log ((q : ℝ) * (|t| + 2))) ∧
        (∀ c T_star : ℝ, 1 < c → c ≤ 3 → 1 ≤ T_star → T_star ≤ T →
          (∀ ρ ∈ Z, |ρ.im| ≠ T_star) →
          DifferentiableOn ℂ
            (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s -
              (if χ = 1 then 1 / (s - 1) else 0) +
              ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T_star), 1 / (s - ρ))
            (closedRect (-(1 / 2)) c (-T_star) T_star)) ∧
        (∀ σ t : ℝ, -(1 / 2) ≤ σ → σ ≤ 3 → |t| ≤ T →
          (χ = 1 → ((σ : ℂ) + I * (t : ℂ)) ≠ 1) →
          (∀ ρ ∈ Z, ((σ : ℂ) + I * (t : ℂ)) ≠ ρ) →
          ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (t : ℂ)) -
            (if χ = 1 then 1 / (((σ : ℂ) + I * (t : ℂ)) - 1) else 0) +
            ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1),
              1 / (((σ : ℂ) + I * (t : ℂ)) - ρ)‖ ≤
            B * Real.log ((q : ℝ) * (|t| + 2)))

private lemma zeroCountBound_subset {C_N : ℝ} {q : ℕ} {Z₁ Z₂ : Finset ℂ}
    (hsub : Z₁ ⊆ Z₂) (hcnt : Stage3ZeroFreeRegion.ZeroCountBound C_N Z₂ q) :
    Stage3ZeroFreeRegion.ZeroCountBound C_N Z₁ q := by
  refine ⟨hcnt.1, fun t ht => ?_⟩
  have hle : (Z₁.filter fun ρ => |ρ.im| ≤ t).card ≤ (Z₂.filter fun ρ => |ρ.im| ≤ t).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  exact (by exact_mod_cast hle : ((Z₁.filter fun ρ => |ρ.im| ≤ t).card : ℝ) ≤
    ((Z₂.filter fun ρ => |ρ.im| ≤ t).card : ℝ)).trans (hcnt.2 t ht)

private lemma log_q_add_ge_half {q : ℕ} [NeZero q] {t : ℝ} (ht : 0 ≤ t) :
    (1 / 2 : ℝ) ≤ Real.log ((q : ℝ) * (t + 2)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  have h2 : (2 : ℝ) ≤ (q : ℝ) * (t + 2) := by nlinarith
  exact (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
    (Real.log_le_log (by norm_num) h2)

private lemma unit_band_card_le {C_1 : ℝ} {q : ℕ} [NeZero q] {Z : Finset ℂ} {T_lo T_hi : ℝ}
    (hlo : 1 ≤ T_lo) (hTlo_le : T_lo ≤ T_hi) (hhi : T_hi ≤ T_lo + 1) (hC1 : 0 ≤ C_1)
    (hdens : ∀ t : ℝ, |t| ≤ T_hi →
      ((Z.filter fun ρ => |ρ.im - t| ≤ 1).card : ℝ) ≤ C_1 * Real.log ((q : ℝ) * (|t| + 2))) :
    ((Z.filter fun ρ => T_lo - 1 ≤ |ρ.im| ∧ |ρ.im| ≤ T_hi + 1).card : ℝ) ≤
      4 * C_1 * Real.log ((q : ℝ) * (T_hi + 2)) := by
  classical
  set S : Finset ℂ := Z.filter fun ρ => T_lo - 1 ≤ |ρ.im| ∧ |ρ.im| ≤ T_hi + 1
  set A1 : Finset ℂ := Z.filter fun ρ => |ρ.im - T_lo| ≤ 1
  set A2 : Finset ℂ := Z.filter fun ρ => |ρ.im - T_hi| ≤ 1
  set A3 : Finset ℂ := Z.filter fun ρ => |ρ.im - (-T_lo)| ≤ 1
  set A4 : Finset ℂ := Z.filter fun ρ => |ρ.im - (-T_hi)| ≤ 1
  have hcov : S ⊆ A1 ∪ A2 ∪ A3 ∪ A4 := by
    intro ρ hρ
    obtain ⟨hρZ, h1, h2⟩ := Finset.mem_filter.mp hρ
    simp only [Finset.mem_union, A1, A2, A3, A4, Finset.mem_filter]
    by_cases him : 0 ≤ ρ.im
    · rw [abs_of_nonneg him] at h1 h2
      by_cases hmid : ρ.im ≤ T_lo + 1
      · exact Or.inl (Or.inl (Or.inl ⟨hρZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hρZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩))
    · push Not at him
      rw [abs_of_neg him] at h1 h2
      by_cases hmid : -ρ.im ≤ T_lo + 1
      · exact Or.inl (Or.inr ⟨hρZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
      · exact Or.inr ⟨hρZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hcard_le : S.card ≤ A1.card + A2.card + A3.card + A4.card := by
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le (A1 ∪ A2 ∪ A3) A4
    have h3 := Finset.card_union_le (A1 ∪ A2) A3
    have h4 := Finset.card_union_le A1 A2
    omega
  have hcardR : (S.card : ℝ) ≤ (A1.card : ℝ) + (A2.card : ℝ) + (A3.card : ℝ) + (A4.card : ℝ) := by
    exact_mod_cast hcard_le
  have hq0 : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hb1 : (A1.card : ℝ) ≤ C_1 * Real.log ((q : ℝ) * (T_hi + 2)) := by
    have h := hdens T_lo (by rw [abs_of_nonneg (by linarith)]; exact hTlo_le)
    rw [abs_of_nonneg (by linarith)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by nlinarith)) hC1)
  have hb2 : (A2.card : ℝ) ≤ C_1 * Real.log ((q : ℝ) * (T_hi + 2)) := by
    have h := hdens T_hi (by rw [abs_of_nonneg (by linarith)])
    rwa [abs_of_nonneg (by linarith)] at h
  have hb3 : (A3.card : ℝ) ≤ C_1 * Real.log ((q : ℝ) * (T_hi + 2)) := by
    have h := hdens (-T_lo) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hTlo_le)
    rw [abs_neg, abs_of_nonneg (by linarith)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by nlinarith)) hC1)
  have hb4 : (A4.card : ℝ) ≤ C_1 * Real.log ((q : ℝ) * (T_hi + 2)) := by
    have h := hdens (-T_hi) (by rw [abs_neg, abs_of_nonneg (by linarith)])
    rwa [abs_neg, abs_of_nonneg (by linarith)] at h
  linarith

open Classical in
/-- **Smoothed Explicit Formula for `ψ_1(x, χ)` from `MeromorphicLogDerivPackage`**
(combining `Stage4ExplicitFormula.norm_psi1Char_sub_truncatedPerron_le`, Section 1's Rectangular
Residue Shift, and Section 2's Pigeonhole Zero-Spacing Lemma):
for every `q ≥ 1`, `χ mod q`, `x ≥ 2`, `1 < c ≤ 3`, `T ≥ 2`, with `σ₀ = (1 - θ) / 2`, there exist
a good height `T_* ∈ [T, T + 1]` and the zero set `Z` in `[1 - θ, θ] × (-T_*, T_*)` such that
`ψ_1(x, χ) = δ_{χ=1} · x² / 2 - ∑_{ρ ∈ Z} x^{ρ + 1} / (ρ (ρ + 1))
  + O(x^{σ₀ + 1} log²(q (T + 3)) + x^{c + 1} / ((c - 1) T) + x^{c + 1} log²(q (T + 3)) / T²)`. -/
theorem psi1Char_smoothed_explicit_of_meromorphicPackage {θ B C_N C_1 : ℝ}
    (H : MeromorphicLogDerivPackage θ B C_N C_1) :
    ∃ C_S : ℝ, 0 ≤ C_S ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x c T : ℝ),
        2 ≤ x → 1 < c → c ≤ 3 → 2 ≤ T →
        let σ₀ := (1 - θ) / 2
        ∃ T_star ∈ Set.Icc T (T + 1), ∃ Z : Finset ℂ,
          (∀ ρ ∈ Z, 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ ∧ |ρ.im| < T_star) ∧
          Stage3ZeroFreeRegion.ZeroCountBound C_N Z q ∧
          ‖Stage4ExplicitFormula.psi1Char χ x -
            ((if χ = 1 then (x : ℂ) ^ 2 / 2 else 0) -
              ∑ ρ ∈ Z, (x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))‖ ≤
            C_S * (x ^ (σ₀ + 1) * (Real.log ((q : ℝ) * (T + 3))) ^ 2 +
              x ^ (c + 1) / ((c - 1) * T) +
              x ^ (c + 1) * (Real.log ((q : ℝ) * (T + 3))) ^ 2 / T ^ 2) := by
  have hθ0 : 0 < 1 - θ := by linarith [H.theta_lt_one]
  set σ₀ : ℝ := (1 - θ) / 2 with hσ₀_def
  have hσ₀_pos : 0 < σ₀ := by positivity
  have hσ₀_lt1 : σ₀ < 1 := by linarith [H.theta_ge_half, hσ₀_def]
  set K_V : ℝ := (1 / (2 * σ₀)) * (2 * B + 4 * C_1 / (1 - θ) + 8)
  set K_H : ℝ := (3 / Real.pi) * (2 * B + 4 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4))
  set C_S : ℝ := max (max K_V K_H) (18 / Real.pi)
  have hB := H.B_nonneg
  have hC1 := H.C1_nonneg
  have hCS_nn : 0 ≤ C_S := le_trans (by positivity : (0 : ℝ) ≤ 18 / Real.pi) (le_max_right _ _)
  refine ⟨C_S, hCS_nn, fun q _ χ x c T hx hc1 hc3 hT => ?_⟩
  obtain ⟨Z_all, hZ_strip, hZ_cnt, hZ_dens, hZ_holo, hZ_pf⟩ :=
    H.zeros_and_partial_fraction q χ (T + 1) (by linarith)
  set Z_band : Finset ℂ := Z_all.filter fun ρ => T - 1 ≤ |ρ.im| ∧ |ρ.im| ≤ (T + 1) + 1
  set L : ℝ := Real.log ((q : ℝ) * (T + 3))
  have hL_ge : (1 / 2 : ℝ) ≤ L := by
    have h := log_q_add_ge_half (q := q) (t := T + 1) (by linarith)
    simpa only [show T + 1 + 2 = T + 3 by ring] using h
  have hL_pos : 0 < L := by linarith
  have hband_card : (Z_band.card : ℝ) ≤ 4 * C_1 * L := by
    have h := unit_band_card_le (C_1 := C_1) (q := q) (Z := Z_all) (T_lo := T) (T_hi := T + 1)
      (by linarith) (by linarith) le_rfl hC1 hZ_dens
    simpa only [Z_band, L, show (T + 1) + 2 = T + 3 by ring] using h
  obtain ⟨T_star, hT_mem, hT_dist⟩ := exists_good_height_pigeonhole_symm (by linarith : 0 ≤ T)
    Z_band (N := Z_band.card) le_rfl
  have hT_star_ge1 : 1 ≤ T_star := by linarith [hT_mem.1]
  have hT_star_pos : 0 < T_star := by linarith
  have hT_star_le : T_star ≤ T + 1 := hT_mem.2
  -- Show `T_star` avoids every `|ρ.im|` for `ρ ∈ Z_all`
  have havoid_all : ∀ ρ ∈ Z_all, |ρ.im| ≠ T_star := by
    intro ρ hρ hEq
    have hmem : ρ ∈ Z_band := Finset.mem_filter.mpr ⟨hρ, by linarith [hT_mem.1], by linarith [hT_mem.2]⟩
    have hd := hT_dist ρ hmem
    have hpos : (0 : ℝ) < 1 / (2 * ((Z_band.card : ℝ) + 1)) := by positivity
    rcases le_or_gt 0 ρ.im with h | h
    · rw [abs_of_nonneg h] at hEq; rw [hEq, sub_self, abs_zero] at hd; linarith [hd.1]
    · rw [abs_of_neg h] at hEq
      have h0 : (-T_star) - ρ.im = 0 := by linarith
      rw [h0, abs_zero] at hd; linarith [hd.2]
  set Z : Finset ℂ := Z_all.filter fun ρ => |ρ.im| < T_star
  refine ⟨T_star, hT_mem, Z, fun ρ hρ => ?_, zeroCountBound_subset (Finset.filter_subset _ _) hZ_cnt, ?_⟩
  · obtain ⟨hρZ, hlt⟩ := Finset.mem_filter.mp hρ
    exact ⟨(hZ_strip ρ hρZ).1, (hZ_strip ρ hρZ).2.1, hlt⟩
  · -- Verify hypotheses of `norm_psi1Char_sub_explicit_le`
    have hZ_rect : ∀ ρ ∈ Z, σ₀ < ρ.re ∧ ρ.re < 1 ∧ -T_star < ρ.im ∧ ρ.im < T_star := by
      intro ρ hρ
      obtain ⟨hρZ, hlt⟩ := Finset.mem_filter.mp hρ
      obtain ⟨h1, h2, _⟩ := hZ_strip ρ hρZ
      have habs := abs_lt.mp hlt
      exact ⟨by linarith [hσ₀_def], lt_of_le_of_lt h2 H.theta_lt_one, habs.1, habs.2⟩
    have hL_holo : DifferentiableOn ℂ
        (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s -
          (if χ = 1 then 1 / (s - 1) else 0) + ∑ ρ ∈ Z, (1 : ℂ) / (s - ρ))
        (closedRect σ₀ c (-T_star) T_star) := by
      have hsub : closedRect σ₀ c (-T_star) T_star ⊆ closedRect (-(1 / 2)) c (-T_star) T_star :=
        fun s ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨by linarith, h2⟩, h3⟩
      exact (hZ_holo c T_star hc1 hc3 hT_star_ge1 hT_star_le havoid_all).mono hsub
    -- Horizontal bound `M_H = (2 * B + 4 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4)) * L ^ 2`
    set M_H : ℝ := (2 * B + 4 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4)) * L ^ 2
    have hMH_nn : 0 ≤ M_H := by positivity
    have hH_both : ∀ s_im : ℝ, (s_im = T_star ∨ s_im = -T_star) →
        ∀ σ ∈ Set.Icc σ₀ c,
          ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ))‖ ≤ M_H := by
      intro s_im hsim σ hσ
      have habs_sim : |s_im| = T_star := by
        rcases hsim with rfl | rfl <;> simp [abs_of_pos hT_star_pos]
      have hne1 : (χ = 1 → ((σ : ℂ) + I * (s_im : ℂ)) ≠ 1) := fun _ h0 => by
        have := congrArg Complex.im h0; simp at this; rw [this, abs_zero] at habs_sim; linarith
      have hneZ : ∀ ρ ∈ Z_all, ((σ : ℂ) + I * (s_im : ℂ)) ≠ ρ := fun ρ hρ h0 => by
        have := congrArg Complex.im h0; simp at this
        exact havoid_all ρ hρ (by rw [← this, habs_sim])
      have hpf := hZ_pf σ s_im (by linarith [hσ.1]) (hσ.2.trans hc3)
        (by rw [habs_sim]; exact hT_star_le) hne1 hneZ
      have hlog_le : Real.log ((q : ℝ) * (|s_im| + 2)) ≤ L := by
        have hq0 : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
        refine Real.log_le_log (by positivity) ?_
        rw [habs_sim]; nlinarith
      have hpole1 : ‖if χ = 1 then (1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - 1) else 0‖ ≤ 1 := by
        split_ifs
        · rw [norm_div, norm_one]
          have hden : 1 ≤ ‖((σ : ℂ) + I * (s_im : ℂ)) - 1‖ := by
            have h := Complex.abs_im_le_norm (((σ : ℂ) + I * (s_im : ℂ)) - 1)
            simpa [habs_sim] using hT_star_ge1.trans (by simpa [habs_sim] using h)
          exact div_le_one_of_le₀ hden (norm_nonneg _)
        · simp
      have hsum_le :
          ‖∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
            (1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)‖ ≤
            2 * (4 * C_1 + 2) * (4 * C_1 + 4) * L ^ 2 := by
        refine (norm_sum_le _ _).trans ?_
        have hsub_band : Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1) ⊆ Z_band := by
          intro ρ hρ
          obtain ⟨hρZ, hd⟩ := Finset.mem_filter.mp hρ
          have htri := abs_abs_sub_abs_le_abs_sub ρ.im s_im
          rw [habs_sim] at htri
          have habs_bd := abs_le.mp (htri.trans hd)
          exact Finset.mem_filter.mpr ⟨hρZ, by linarith [hT_mem.1], by linarith [hT_mem.2]⟩
        have hterm_bd : ∀ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
            ‖(1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)‖ ≤ 2 * ((Z_band.card : ℝ) + 1) := by
          intro ρ hρ
          have hρb := hsub_band hρ
          have hdist_ge : 1 / (2 * ((Z_band.card : ℝ) + 1)) ≤ |s_im - ρ.im| := by
            rcases hsim with rfl | rfl
            · exact (hT_dist ρ hρb).1
            · exact (hT_dist ρ hρb).2
          have hnorm_ge : 1 / (2 * ((Z_band.card : ℝ) + 1)) ≤ ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖ :=
            hdist_ge.trans (by simpa using Complex.abs_im_le_norm (((σ : ℂ) + I * (s_im : ℂ)) - ρ))
          rw [norm_div, norm_one]
          have hNb_nn : (0 : ℝ) ≤ (Z_band.card : ℝ) := Nat.cast_nonneg _
          have hNb1_pos : (0 : ℝ) < (Z_band.card : ℝ) + 1 := by linarith
          have hpos_d : (0 : ℝ) < 1 / (2 * ((Z_band.card : ℝ) + 1)) :=
            div_pos one_pos (mul_pos two_pos hNb1_pos)
          calc (1 : ℝ) / ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖
              ≤ 1 / (1 / (2 * ((Z_band.card : ℝ) + 1))) :=
                div_le_div_of_nonneg_left zero_le_one hpos_d hnorm_ge
            _ = 2 * ((Z_band.card : ℝ) + 1) := one_div_one_div _
        have hNb_nn : (0 : ℝ) ≤ (Z_band.card : ℝ) := Nat.cast_nonneg _
        calc ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
              ‖(1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)‖
            ≤ ∑ _ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1), (2 * ((Z_band.card : ℝ) + 1)) :=
              Finset.sum_le_sum hterm_bd
          _ = ((Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1)).card : ℝ) * (2 * ((Z_band.card : ℝ) + 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Z_band.card : ℝ) * (2 * ((Z_band.card : ℝ) + 1)) := by
              have hle : ((Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1)).card : ℝ) ≤ (Z_band.card : ℝ) := by
                exact_mod_cast Finset.card_le_card hsub_band
              exact mul_le_mul_of_nonneg_right hle (by linarith)
          _ ≤ ((4 * C_1 + 2) * L) * (2 * ((4 * C_1 + 4) * L)) := by
              have h1 : (Z_band.card : ℝ) ≤ (4 * C_1 + 2) * L := by nlinarith
              have h2 : (Z_band.card : ℝ) + 1 ≤ (4 * C_1 + 4) * L := by nlinarith
              exact mul_le_mul h1 (by linarith) (by linarith) (by positivity)
          _ = 2 * (4 * C_1 + 2) * (4 * C_1 + 4) * L ^ 2 := by ring
      have hrew : Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) =
          (Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) -
            (if χ = 1 then 1 / (((σ : ℂ) + I * (s_im : ℂ)) - 1) else 0) +
            ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
              1 / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)) +
          (if χ = 1 then 1 / (((σ : ℂ) + I * (s_im : ℂ)) - 1) else 0) -
          ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
            1 / (((σ : ℂ) + I * (s_im : ℂ)) - ρ) := by ring
      rw [hrew]
      refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
      have hBL : B * Real.log ((q : ℝ) * (|s_im| + 2)) ≤ 2 * B * L ^ 2 := by
        have h1 : B * Real.log ((q : ℝ) * (|s_im| + 2)) ≤ B * L := mul_le_mul_of_nonneg_left hlog_le hB
        nlinarith [mul_nonneg hB hL_pos.le]
      have h1L : (1 : ℝ) ≤ 4 * L ^ 2 := by nlinarith
      dsimp only [M_H]
      have hH_sum : (2 * B + 4 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4)) * L ^ 2 =
          2 * B * L ^ 2 + 4 * L ^ 2 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4) * L ^ 2 := by ring
      linarith
    -- Left-vertical bound `M_V = (2 * B + 4 * C_1 / (1 - θ) + 8) * L ^ 2`
    set M_V : ℝ := (2 * B + 4 * C_1 / (1 - θ) + 8) * L ^ 2
    have hMV_nn : 0 ≤ M_V := by positivity
    have hV_bd : ∀ t ∈ Set.Icc (-T_star) T_star,
        ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤ M_V := by
      intro t ht
      have habs_t : |t| ≤ T_star := abs_le.mpr ht
      have hne1 : (χ = 1 → ((σ₀ : ℂ) + I * (t : ℂ)) ≠ 1) := fun _ h0 => by
        have := congrArg Complex.re h0; simp at this; linarith
      have hneZ : ∀ ρ ∈ Z_all, ((σ₀ : ℂ) + I * (t : ℂ)) ≠ ρ := fun ρ hρ h0 => by
        have := congrArg Complex.re h0; simp at this; linarith [(hZ_strip ρ hρ).1, hσ₀_def]
      have hpf := hZ_pf σ₀ t (by linarith) (by linarith) (habs_t.trans hT_star_le) hne1 hneZ
      have hlog_le : Real.log ((q : ℝ) * (|t| + 2)) ≤ L := by
        have hq0 : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
        exact Real.log_le_log (by positivity) (by nlinarith)
      have hpole1 : ‖if χ = 1 then (1 : ℂ) / (((σ₀ : ℂ) + I * (t : ℂ)) - 1) else 0‖ ≤ 2 := by
        split_ifs
        · rw [norm_div, norm_one]
          have hden : (1 / 2 : ℝ) ≤ ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖ := by
            have h := Complex.abs_re_le_norm (((σ₀ : ℂ) + I * (t : ℂ)) - 1)
            have hre : (((σ₀ : ℂ) + I * (t : ℂ)) - 1).re = σ₀ - 1 := by simp
            rw [hre, abs_of_neg (by linarith)] at h
            linarith [H.theta_ge_half, hσ₀_def]
          calc (1 : ℝ) / ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖
              ≤ 1 / (1 / 2) := div_le_div_of_nonneg_left zero_le_one (by norm_num) hden
            _ = 2 := by norm_num
        · simp
      have hsum_le :
          ‖∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
            (1 : ℂ) / (((σ₀ : ℂ) + I * (t : ℂ)) - ρ)‖ ≤
            (4 * C_1 / (1 - θ)) * L ^ 2 := by
        refine (norm_sum_le _ _).trans ?_
        have hterm_bd : ∀ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
            ‖(1 : ℂ) / (((σ₀ : ℂ) + I * (t : ℂ)) - ρ)‖ ≤ 2 / (1 - θ) := by
          intro ρ hρ
          have hρZ := (Finset.mem_filter.mp hρ).1
          have hden : (1 - θ) / 2 ≤ ‖((σ₀ : ℂ) + I * (t : ℂ)) - ρ‖ := by
            have h := Complex.abs_re_le_norm (((σ₀ : ℂ) + I * (t : ℂ)) - ρ)
            have hre : (((σ₀ : ℂ) + I * (t : ℂ)) - ρ).re = σ₀ - ρ.re := by simp
            rw [hre, abs_of_neg (by linarith [(hZ_strip ρ hρZ).1, hσ₀_def])] at h
            linarith [(hZ_strip ρ hρZ).1, hσ₀_def]
          rw [norm_div, norm_one]
          calc (1 : ℝ) / ‖((σ₀ : ℂ) + I * (t : ℂ)) - ρ‖
              ≤ 1 / ((1 - θ) / 2) := div_le_div_of_nonneg_left zero_le_one (by positivity) hden
            _ = 2 / (1 - θ) := by field_simp [hθ0.ne']
        have hdens_t := hZ_dens t (habs_t.trans hT_star_le)
        calc ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
              ‖(1 : ℂ) / (((σ₀ : ℂ) + I * (t : ℂ)) - ρ)‖
            ≤ ∑ _ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1), (2 / (1 - θ)) :=
              Finset.sum_le_sum hterm_bd
          _ = ((Z_all.filter (fun ρ => |ρ.im - t| ≤ 1)).card : ℝ) * (2 / (1 - θ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (C_1 * Real.log ((q : ℝ) * (|t| + 2))) * (2 / (1 - θ)) :=
              mul_le_mul_of_nonneg_right hdens_t (by positivity)
          _ ≤ (C_1 * L) * (2 / (1 - θ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le hC1) (by positivity)
          _ ≤ (4 * C_1 / (1 - θ)) * L ^ 2 := by
              have h1 : (C_1 * L) * (2 / (1 - θ)) = (2 * C_1 / (1 - θ)) * L := by ring
              have h4 : (4 * C_1 / (1 - θ)) * L ^ 2 = ((2 * C_1 / (1 - θ)) * L) * (2 * L) := by ring
              rw [h1, h4]
              have hnn : 0 ≤ (2 * C_1 / (1 - θ)) * L := by positivity
              nlinarith [hL_ge]
      have hrew : Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ)) =
          (Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ)) -
            (if χ = 1 then 1 / (((σ₀ : ℂ) + I * (t : ℂ)) - 1) else 0) +
            ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
              1 / (((σ₀ : ℂ) + I * (t : ℂ)) - ρ)) +
          (if χ = 1 then 1 / (((σ₀ : ℂ) + I * (t : ℂ)) - 1) else 0) -
          ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
            1 / (((σ₀ : ℂ) + I * (t : ℂ)) - ρ) := by ring
      rw [hrew]
      refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
      have hBL : B * Real.log ((q : ℝ) * (|t| + 2)) ≤ 2 * B * L ^ 2 := by
        have h1 : B * Real.log ((q : ℝ) * (|t| + 2)) ≤ B * L := mul_le_mul_of_nonneg_left hlog_le hB
        nlinarith [mul_nonneg hB hL_pos.le]
      have h2L : (2 : ℝ) ≤ 8 * L ^ 2 := by nlinarith
      dsimp only [M_V]
      have hV_sum : (2 * B + 4 * C_1 / (1 - θ) + 8) * L ^ 2 =
          2 * B * L ^ 2 + (4 * C_1 / (1 - θ)) * L ^ 2 + 8 * L ^ 2 := by ring
      linarith
    have hH_bot : ∀ σ ∈ Set.Icc σ₀ c,
        ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) - I * (T_star : ℂ))‖ ≤ M_H := by
      intro σ hσ
      have hsub : (σ : ℂ) - I * (T_star : ℂ) = (σ : ℂ) + I * ((-T_star : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsub]
      exact hH_both (-T_star) (Or.inr rfl) σ hσ
    have hmain := norm_psi1Char_sub_explicit_le χ (by linarith : 1 ≤ x) hσ₀_pos hσ₀_lt1 hc1
      hT_star_pos hMH_nn hMV_nn Z (fun _ => (1 : ℂ)) hZ_rect hL_holo
      (hH_both T_star (Or.inl rfl)) hH_bot hV_bd
    simp only [one_mul] at hmain
    -- Compare each of the 3 RHS terms with `C_S * (...)`
    have hx0 : 0 < x := by linarith
    have hterm1 : (6 * c / Real.pi) * x ^ (c + 1) / ((c - 1) * T_star) ≤
        (18 / Real.pi) * (x ^ (c + 1) / ((c - 1) * T)) := by
      have h1 : 6 * c / Real.pi ≤ 18 / Real.pi :=
        div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
      have h2 : x ^ (c + 1) / ((c - 1) * T_star) ≤ x ^ (c + 1) / ((c - 1) * T) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) (by positivity)
          (mul_le_mul_of_nonneg_left hT_mem.1 (by linarith))
      rw [mul_div_assoc]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hterm2 : (1 / (2 * σ₀)) * M_V * x ^ (σ₀ + 1) = K_V * (x ^ (σ₀ + 1) * L ^ 2) := by
      dsimp only [M_V, K_V]; ring
    have hterm3 : ((c - σ₀) / Real.pi) * M_H * x ^ (c + 1) / T_star ^ 2 ≤
        K_H * (x ^ (c + 1) * L ^ 2 / T ^ 2) := by
      have hcs : (c - σ₀) / Real.pi ≤ 3 / Real.pi :=
        div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
      have hTsq : T ^ 2 ≤ T_star ^ 2 := pow_le_pow_left₀ (by linarith) hT_mem.1 2
      have hrew1 : ((c - σ₀) / Real.pi) * M_H * x ^ (c + 1) / T_star ^ 2 =
          ((c - σ₀) / Real.pi) * (2 * B + 4 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4)) *
            (x ^ (c + 1) * L ^ 2 / T_star ^ 2) := by dsimp only [M_H]; ring
      have hrew2 : K_H * (x ^ (c + 1) * L ^ 2 / T ^ 2) =
          (3 / Real.pi) * (2 * B + 4 + 2 * (4 * C_1 + 2) * (4 * C_1 + 4)) *
            (x ^ (c + 1) * L ^ 2 / T ^ 2) := rfl
      rw [hrew1, hrew2]
      refine mul_le_mul (mul_le_mul_of_nonneg_right hcs (by positivity))
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hTsq) (by positivity) (by positivity)
    have hKV_le : K_V ≤ C_S := (le_max_left _ _).trans (le_max_left _ _)
    have hKH_le : K_H ≤ C_S := (le_max_right _ _).trans (le_max_left _ _)
    have h18_le : 18 / Real.pi ≤ C_S := le_max_right _ _
    have hp1 : 0 ≤ x ^ (σ₀ + 1) * L ^ 2 := by positivity
    have hp2 : 0 ≤ x ^ (c + 1) / ((c - 1) * T) := by positivity
    have hp3 : 0 ≤ x ^ (c + 1) * L ^ 2 / T ^ 2 := by positivity
    have ha1 := mul_le_mul_of_nonneg_right hKV_le hp1
    have ha2 := mul_le_mul_of_nonneg_right h18_le hp2
    have ha3 := mul_le_mul_of_nonneg_right hKH_le hp3
    linarith

private lemma rpow_neg_half_mul_log_sq_le {x : ℝ} (hx : 2 ≤ x) :
    x ^ (-(1 / 2 : ℝ)) * (Real.log x + 1) ^ 2 ≤ 25 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith [show x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * x ^ (1 / 4 : ℝ) by ring]
  have h1 : (1 : ℝ) ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hlin : Real.log x + 1 ≤ 5 * x ^ (1 / 4 : ℝ) := by linarith
  have hsq : (Real.log x + 1) ^ 2 ≤ 25 * x ^ (1 / 2 : ℝ) := by
    calc (Real.log x + 1) ^ 2 ≤ (5 * x ^ (1 / 4 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by linarith [Real.log_nonneg hx1]) hlin 2
      _ = 25 * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by ring
      _ = 25 * x ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hx0]; norm_num
  have hprod : x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  calc x ^ (-(1 / 2 : ℝ)) * (Real.log x + 1) ^ 2
      ≤ x ^ (-(1 / 2 : ℝ)) * (25 * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hx0.le _)
    _ = 25 * (x ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 : ℝ)) := by ring
    _ = 25 := by rw [hprod, mul_one]

private lemma chebyshevPsiChar_modOne_eq (x : ℝ) :
    Stage2DirichletAP.chebyshevPsiChar (1 : DirichletCharacter ℂ 1) x =
      (RHDirect.chebyshevPsi x : ℂ) := by
  unfold Stage2DirichletAP.chebyshevPsiChar RHDirect.chebyshevPsi
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Stage2DirichletAP.principal_char_apply_nat, if_pos (Nat.coprime_one_right n), one_mul]

/-- **Main Bridge Theorem — Direct Discharge of `Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage`**:
combining Section 1's Rectangular Residue Shift (`vertical_contour_shift_div_id_eq_sum_residues`),
Section 2's AM-GM Linear-in-`N` Good-Horizontal-Line Lemma (`exists_good_height_avg_integral`), and
Section 3B's Sharp Truncated Perron Formula (`norm_chebyshevPsiChar_sub_truncatedPerron_le`), any
`MeromorphicLogDerivPackage θ B C_N C_1` unconditionally discharges
`Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage θ C_N C_R`! -/
theorem truncatedExplicitFormulaPackage_of_meromorphicPackage {θ B C_N C_1 : ℝ}
    (H : MeromorphicLogDerivPackage θ B C_N C_1) :
    ∃ C_R : ℝ, Stage3ZeroFreeRegion.TruncatedExplicitFormulaPackage θ C_N C_R := by
  classical
  have hθ0 : 0 < 1 - θ := by linarith [H.theta_lt_one]
  have hB := H.B_nonneg
  have hC1 := H.C1_nonneg
  -- Explicit unified constant `C_R` covering Perron + s=0 residue + left-vertical + horizontal segments
  set K_0 : ℝ := 2 * B + 2 * C_1 / (1 - θ) + 1
  set K_V : ℝ := 150 * (3 * (B + 2 * C_1) + 1)
  set K_H : ℝ := 20 * (4 * (3 * B + 1) + 64 * (12 * C_1 + 1))
  set C_R : ℝ := 1800 + K_0 + K_V + K_H
  have hCR_nn : 0 ≤ C_R := by positivity
  -- Unified character explicit formula for ALL `q ≥ 1`, `χ mod q`, `x ≥ 2`, `T ≥ 2`
  have hunified :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x T : ℝ),
        2 ≤ x → 2 ≤ T →
        ∃ Z : Finset ℂ,
          (∀ ρ ∈ Z, 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ ∧ |ρ.im| ≤ T) ∧
          Stage3ZeroFreeRegion.ZeroCountBound C_N Z q ∧
          ‖Stage2DirichletAP.chebyshevPsiChar χ x -
            (if χ = 1 then (x : ℂ) else 0) + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ‖ ≤
            C_R * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
              (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
    intro q _ χ x T hx hT
    have hx0 : 0 < x := by linarith
    have hx1 : 1 ≤ x := by linarith
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
    have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
    have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
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
      have h1 : x ^ c = x * x ^ (1 / Real.log x) := by rw [hc_def, Real.rpow_add hx0, Real.rpow_one]
      have h2 : x ^ (1 / Real.log x) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos hx0, mul_one_div_cancel hlogx_pos.ne']
      rw [h1, h2]
      have he : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      nlinarith
    -- Clamp effective truncation height `T_eff = min T (x * (log x + 1))`
    set T_eff : ℝ := min T (x * (Real.log x + 1)) with hTeff_def
    have hTeff_ge2 : 2 ≤ T_eff := le_min hT (by nlinarith)
    have hTeff_leT : T_eff ≤ T := min_le_left _ _
    have hTeff_lex : T_eff ≤ x * (Real.log x + 1) := min_le_right _ _
    -- Obtain zeros up to `T_eff + 1`
    obtain ⟨Z_all, hZ_strip, hZ_cnt, hZ_dens, hZ_holo, hZ_pf⟩ :=
      H.zeros_and_partial_fraction q χ (T_eff + 1) (by linarith)
    set Z_band : Finset ℂ := Z_all.filter fun ρ => (T_eff - 1) - 1 ≤ |ρ.im| ∧ |ρ.im| ≤ T_eff + 1
    -- Select AM-GM good height `T_star ∈ (T_eff - 1, T_eff)` avoiding all `±ρ.im` (`ρ ∈ Z_band`)
    obtain ⟨T_star, hT_mem, hT_avoid_band, hH_top_int, hH_bot_int⟩ :=
      exists_good_height_avg_integral (by linarith : -(1 / 2 : ℝ) < c) (T_eff - 1) Z_band
    rw [show T_eff - 1 + 1 = T_eff by ring] at hT_mem
    have hT_star_ge1 : 1 ≤ T_star := by linarith [hT_mem.1]
    have hT_star_pos : 0 < T_star := by linarith
    have hT_star_le : T_star ≤ T_eff := hT_mem.2.le
    have hT_star_ge_half : T_eff / 2 ≤ T_star := by linarith [hT_mem.1]
    -- `T_star` avoids every `|ρ.im|` for `ρ ∈ Z_all`
    have havoid_all : ∀ ρ ∈ Z_all, |ρ.im| ≠ T_star := by
      intro ρ hρ hEq
      have hmem : ρ ∈ Z_band :=
        Finset.mem_filter.mpr ⟨hρ, by linarith [hT_mem.1], by linarith [hT_mem.2]⟩
      have hav := hT_avoid_band ρ hmem
      rcases le_or_gt 0 ρ.im with h | h
      · rw [abs_of_nonneg h] at hEq; exact hav.1 hEq.symm
      · rw [abs_of_neg h] at hEq; exact hav.2 (by linarith)
    -- Bound `log(q * (T_eff + 2)) ≤ 3 * (log q + 1) * (log x + 1)`
    have hlog_Teff : Real.log ((q : ℝ) * (T_eff + 2)) ≤
        3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
      have hlogx_lex : Real.log x + 1 ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
      have hT_le_sq : T_eff + 2 ≤ 2 * x ^ 2 := by nlinarith
      have hlog_t : Real.log (T_eff + 2) ≤ 2 * (Real.log x + 1) := by
        calc Real.log (T_eff + 2) ≤ Real.log (2 * x ^ 2) := Real.log_le_log (by positivity) hT_le_sq
          _ = Real.log 2 + 2 * Real.log x := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
          _ ≤ 2 * (Real.log x + 1) := by linarith [Real.log_two_lt_d9]
      rw [Real.log_mul hq0.ne' (by positivity)]
      nlinarith
    have hband_card : (Z_band.card : ℝ) ≤ 12 * C_1 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
      have h1 := unit_band_card_le (C_1 := C_1) (q := q) (Z := Z_all) (T_lo := T_eff - 1)
        (T_hi := T_eff) (by linarith) (by linarith) (by linarith) hC1 (fun t ht => hZ_dens t (by linarith))
      calc (Z_band.card : ℝ) ≤ 4 * C_1 * Real.log ((q : ℝ) * (T_eff + 2)) := h1
        _ ≤ 4 * C_1 * (3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) :=
            mul_le_mul_of_nonneg_left hlog_Teff (by positivity)
        _ = 12 * C_1 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by ring
    -- Key inequality transferring `x / T_star` back to `x / T + 1 / (log x + 1)`
    have hx_div_Tstar : x / T_star * (Real.log x + 1) ^ 2 ≤
        2 * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1)) := by
      have h1 : x / T_star ≤ 2 * (x / T_eff) := by
        rw [div_le_iff₀ hT_star_pos]
        have hpos_Teff : 0 < T_eff := by linarith
        have heq : 2 * (x / T_eff) * T_star = x * (2 * T_star / T_eff) := by ring
        rw [heq]
        have hge1 : 1 ≤ 2 * T_star / T_eff := by rw [one_le_div hpos_Teff]; linarith
        nlinarith
      have h2 : x / T_eff * (Real.log x + 1) ^ 2 ≤
          x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1) := by
        rw [hTeff_def]
        rcases min_cases T (x * (Real.log x + 1)) with ⟨heq, _⟩ | ⟨heq, _⟩
        · rw [heq]; linarith
        · rw [heq]
          have hsimp : x / (x * (Real.log x + 1)) * (Real.log x + 1) ^ 2 = Real.log x + 1 := by
            field_simp [hx0.ne', (show Real.log x + 1 ≠ 0 by linarith)]
          rw [hsimp]
          linarith [show 0 ≤ x / T * (Real.log x + 1) ^ 2 by positivity]
      have h3 : x / T_star * (Real.log x + 1) ^ 2 ≤ 2 * (x / T_eff * (Real.log x + 1) ^ 2) := by
        have := mul_le_mul_of_nonneg_right h1 (sq_nonneg (Real.log x + 1))
        linarith
      linarith
    -- Define the interior zero set `Z = {ρ ∈ Z_all | |ρ.im| < T_star}`
    set Z : Finset ℂ := Z_all.filter fun ρ => |ρ.im| < T_star
    refine ⟨Z, fun ρ hρ => ?_, zeroCountBound_subset (Finset.filter_subset _ _) hZ_cnt, ?_⟩
    · obtain ⟨hρZ, hlt⟩ := Finset.mem_filter.mp hρ
      exact ⟨(hZ_strip ρ hρZ).1, (hZ_strip ρ hρZ).2.1, hlt.le.trans (hT_star_le.trans hTeff_leT)⟩
    · -- Apply `vertical_contour_shift_div_id_eq_sum_residues` on `[-1/2, c] × [-T_star, T_star]`
      have h1_notMem : (1 : ℂ) ∉ Z := fun h1 => by
        have hre := (hZ_strip 1 (Finset.mem_filter.mp h1).1).2.1
        simp at hre; linarith [H.theta_lt_one]
      let J : Finset ℂ := if χ = 1 then insert (1 : ℂ) Z else Z
      let a : ℂ → ℂ := fun p => if p = 1 then 1 else -1
      have hp : ∀ p ∈ J, p ∈ openRect (-(1 / 2)) c (-T_star) T_star := by
        intro p hpJ
        by_cases hχ : χ = 1
        · simp only [J, hχ, ↓reduceIte, Finset.mem_insert] at hpJ
          rcases hpJ with rfl | hpZ
          · exact ⟨by simp [hc1]; norm_num, by simp [hT_star_pos]⟩
          · obtain ⟨hρZ, hlt⟩ := Finset.mem_filter.mp hpZ
            obtain ⟨h1, h2, _⟩ := hZ_strip p hρZ
            exact ⟨⟨by linarith, lt_of_le_of_lt h2 (H.theta_lt_one.trans hc1)⟩, abs_lt.mp hlt⟩
        · simp only [J, hχ, ↓reduceIte] at hpJ
          obtain ⟨hρZ, hlt⟩ := Finset.mem_filter.mp hpJ
          obtain ⟨h1, h2, _⟩ := hZ_strip p hρZ
          exact ⟨⟨by linarith, lt_of_le_of_lt h2 (H.theta_lt_one.trans hc1)⟩, abs_lt.mp hlt⟩
      have hp0 : ∀ p ∈ J, p ≠ 0 := by
        intro p hpJ h0
        subst h0
        by_cases hχ : χ = 1
        · simp only [J, hχ, ↓reduceIte, Finset.mem_insert] at hpJ
          rcases hpJ with h01 | hpZ
          · norm_num at h01
          · have hre := (hZ_strip 0 (Finset.mem_filter.mp hpZ).1).1
            simp at hre; linarith
        · simp only [J, hχ, ↓reduceIte] at hpJ
          have hre := (hZ_strip 0 (Finset.mem_filter.mp hpJ).1).1
          simp at hre; linarith
      have hL_eq : (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s - ∑ p ∈ J, a p / (s - p)) =
          fun s => Stage3ZeroFreeRegion.negLogDerivL χ s -
            (if χ = 1 then 1 / (s - 1) else 0) + ∑ ρ ∈ Z, 1 / (s - ρ) := by
        funext s
        have hZ_sum : ∑ ρ ∈ Z, a ρ / (s - ρ) = -(∑ ρ ∈ Z, 1 / (s - ρ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          have hne : ρ ≠ 1 := fun h => h1_notMem (h ▸ hρ)
          simp [a, hne, neg_div]
        by_cases hχ : χ = 1
        · simp only [J, hχ, ↓reduceIte, Finset.sum_insert h1_notMem, show a 1 = 1 by simp [a], hZ_sum]
          ring
        · simp only [J, hχ, ↓reduceIte, hZ_sum]; ring
      have hL_holo : DifferentiableOn ℂ
          (fun s => Stage3ZeroFreeRegion.negLogDerivL χ s - ∑ p ∈ J, a p / (s - p))
          (closedRect (-(1 / 2)) c (-T_star) T_star) :=
        hL_eq.symm ▸ hZ_holo c T_star hc1 hc3 hT_star_ge1 (by linarith) havoid_all
      have hres_eq : ∑ p ∈ J, a p * (x : ℂ) ^ p / p =
          (if χ = 1 then (x : ℂ) else 0) - ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ := by
        have hZ_res : ∑ ρ ∈ Z, a ρ * (x : ℂ) ^ ρ / ρ = -(∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun ρ hρ => ?_
          have hne : ρ ≠ 1 := fun h => h1_notMem (h ▸ hρ)
          simp only [a, hne, ↓reduceIte]; ring
        have h1_res : a 1 * (x : ℂ) ^ (1 : ℂ) / 1 = (x : ℂ) := by
          simp [a, Complex.cpow_one]
        by_cases hχ : χ = 1
        · simp only [J, hχ, ↓reduceIte, Finset.sum_insert h1_notMem, h1_res, hZ_res]; ring
        · simp only [J, hχ, ↓reduceIte, hZ_res]; ring
      have hshift := vertical_contour_shift_div_id_eq_sum_residues
        (Stage3ZeroFreeRegion.negLogDerivL χ) hx0 (by norm_num) hc0 hT_star_pos J id a hp hp0 hL_holo
      simp only [id_eq] at hshift
      rw [hres_eq] at hshift
      change truncatedPerronPsi χ x c T_star = _ at hshift
      -- Piece 1: Sharp Perron truncation error
      have hPerron : ‖Stage2DirichletAP.chebyshevPsiChar χ x - truncatedPerronPsi χ x c T_star‖ ≤
          1800 * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
            (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
        have h1 := norm_chebyshevPsiChar_sub_truncatedPerron_le χ hx hT_star_ge1
        have h1' : 600 * (x / T_star * (Real.log x + 1) ^ 2 + (Real.log x + 1)) ≤
            1800 * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1)) := by
          have ha : 0 ≤ x / T * (Real.log x + 1) ^ 2 := by positivity
          linarith [hx_div_Tstar]
        have h2 : x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1) ≤
            x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
              (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
          have ha : 0 ≤ x / T * (Real.log x + 1) ^ 2 := by positivity
          have hb : 0 ≤ Real.log x + 1 := by positivity
          nlinarith
        linarith
      -- Piece 2: Residue at `s = 0` (`‖negLogDerivL χ 0‖ ≤ K_0 * (log q + 1)`)
      have hRes0 : ‖Stage3ZeroFreeRegion.negLogDerivL χ 0‖ ≤ K_0 * (Real.log (q : ℝ) + 1) := by
        have h0_eq : ((0 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ) = 0 := by simp
        have hne1 : χ = 1 → ((0 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ) ≠ 1 := fun _ h0 => by
          rw [h0_eq] at h0; exact zero_ne_one h0
        have hneZ : ∀ ρ ∈ Z_all, ((0 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ) ≠ ρ := fun ρ hρ h0 => by
          rw [h0_eq] at h0; have := congrArg Complex.re h0; simp at this; linarith [(hZ_strip ρ hρ).1]
        have hpf0 := hZ_pf 0 0 (by norm_num) (by norm_num) (by simp; linarith) hne1 hneZ
        rw [h0_eq] at hpf0
        have hlog2q : Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) ≤ 2 * (Real.log (q : ℝ) + 1) := by
          rw [abs_zero, zero_add, Real.log_mul hq0.ne' (by norm_num)]
          linarith [Real.log_two_lt_d9]
        have hpole1 : ‖if χ = 1 then (1 : ℂ) / ((0 : ℂ) - 1) else 0‖ ≤ 1 := by
          split_ifs <;> simp
        have hsum0 : ‖∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1), (1 : ℂ) / ((0 : ℂ) - ρ)‖ ≤
            (2 * C_1 / (1 - θ)) * (Real.log (q : ℝ) + 1) := by
          refine (norm_sum_le _ _).trans ?_
          have hterm : ∀ ρ ∈ Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1),
              ‖(1 : ℂ) / ((0 : ℂ) - ρ)‖ ≤ 1 / (1 - θ) := by
            intro ρ hρ
            have hρZ := (Finset.mem_filter.mp hρ).1
            rw [zero_sub, norm_div, norm_one, norm_neg]
            have hden : 1 - θ ≤ ‖ρ‖ := (hZ_strip ρ hρZ).1.trans (Complex.re_le_norm ρ)
            exact div_le_div_of_nonneg_left zero_le_one hθ0 hden
          calc ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1), ‖(1 : ℂ) / ((0 : ℂ) - ρ)‖
              ≤ ∑ _ρ ∈ Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1), (1 / (1 - θ)) := Finset.sum_le_sum hterm
            _ = ((Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1)).card : ℝ) * (1 / (1 - θ)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (C_1 * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2))) * (1 / (1 - θ)) :=
                mul_le_mul_of_nonneg_right (hZ_dens 0 (by simp; linarith)) (by positivity)
            _ ≤ (C_1 * (2 * (Real.log (q : ℝ) + 1))) * (1 / (1 - θ)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2q hC1) (by positivity)
            _ = (2 * C_1 / (1 - θ)) * (Real.log (q : ℝ) + 1) := by ring
        have hrew : Stage3ZeroFreeRegion.negLogDerivL χ 0 =
            (Stage3ZeroFreeRegion.negLogDerivL χ 0 - (if χ = 1 then 1 / ((0 : ℂ) - 1) else 0) +
              ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1), 1 / ((0 : ℂ) - ρ)) +
            (if χ = 1 then 1 / ((0 : ℂ) - 1) else 0) -
            ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - 0| ≤ 1), 1 / ((0 : ℂ) - ρ) := by ring
        rw [hrew]
        refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
        refine (add_le_add (add_le_add hpf0 hpole1) hsum0).trans ?_
        have hB2 : B * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) ≤ 2 * B * (Real.log (q : ℝ) + 1) := by
          have := mul_le_mul_of_nonneg_left hlog2q hB; linarith
        dsimp only [K_0]
        calc B * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) + 1 +
              (2 * C_1 / (1 - θ)) * (Real.log (q : ℝ) + 1)
            ≤ 2 * B * (Real.log (q : ℝ) + 1) + (Real.log (q : ℝ) + 1) +
              (2 * C_1 / (1 - θ)) * (Real.log (q : ℝ) + 1) :=
              add_le_add (add_le_add hB2 (by linarith)) le_rfl
          _ = (2 * B + 2 * C_1 / (1 - θ) + 1) * (Real.log (q : ℝ) + 1) := by ring
      -- Piece 3: Left-vertical integral on `Re(s) = -1/2`
      have hLeft_bd : ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ t in (-T_star)..T_star,
            Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) *
              (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) /
              (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          K_V * (Real.log (q : ℝ) + 1) := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        set M_V : ℝ := (3 * (B + 2 * C_1) + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1)
        have hMV_nn : 0 ≤ M_V := by positivity
        -- Continuity of the left-vertical integrand from `hL_holo`
        have hV_cont : ContinuousOn
            (fun t : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) *
              (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) /
              (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)))
            (Set.uIcc (-T_star) T_star) := by
          rw [Set.uIcc_of_le (by linarith)]
          have hsub : (fun t : ℝ => ((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) '' Set.Icc (-T_star) T_star ⊆
              closedRect (-(1 / 2)) c (-T_star) T_star := by
            rintro _ ⟨t, ht, rfl⟩
            exact ⟨by simp; linarith, by simpa using ht⟩
          have hP : ContinuousOn (fun s => ∑ p ∈ J, a p / (s - p))
              ((fun t : ℝ => ((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) '' Set.Icc (-T_star) T_star) := by
            refine continuousOn_finsetSum J fun p hpJ => continuousOn_const.div
              (continuousOn_id.sub continuousOn_const) ?_
            rintro _ ⟨t, _, rfl⟩ h0
            have hre := congrArg Complex.re h0; simp at hre; linarith [(hp p hpJ).1.1]
          have hcont_L : ContinuousOn (Stage3ZeroFreeRegion.negLogDerivL χ)
              ((fun t : ℝ => ((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) '' Set.Icc (-T_star) T_star) :=
            ((hL_holo.continuousOn.mono hsub).add hP).congr fun s _ => by simp only [Pi.add_apply]; ring
          have hmap : ContinuousOn (fun t : ℝ => ((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))
              (Set.Icc (-T_star) T_star) := by fun_prop
          have h1 := hcont_L.comp hmap (Set.mapsTo_image _ _)
          have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
          have hpow : Continuous (fun t : ℝ => (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))) := by
            have hEq : (fun t : ℝ => (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))) =
                fun t : ℝ => cexp (Complex.log (x : ℂ) * (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))) :=
              funext fun t => Complex.cpow_def_of_ne_zero hxC _
            rw [hEq]; fun_prop
          refine (h1.mul hpow.continuousOn).div hmap fun t _ h0 => ?_
          have hre := congrArg Complex.re h0; simp at hre
        have hV_pt : ∀ t ∈ Set.Icc (-T_star) T_star,
            ‖Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) *
              (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) /
              (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
            M_V * x ^ (-(1 / 2 : ℝ)) * ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ := by
          intro t ht
          have habs_t : |t| ≤ T_star := abs_le.mpr ht
          have hne1 : χ = 1 → (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) ≠ 1 := fun _ h0 => by
            have := congrArg Complex.re h0; simp at this; linarith
          have hneZ : ∀ ρ ∈ Z_all, (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) ≠ ρ := fun ρ hρ h0 => by
            have := congrArg Complex.re h0; simp at this; linarith [(hZ_strip ρ hρ).1]
          have hpf := hZ_pf (-(1 / 2)) t le_rfl (by norm_num) (by linarith) hne1 hneZ
          have hlog_le : Real.log ((q : ℝ) * (|t| + 2)) ≤
              3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) :=
            (Real.log_le_log (by positivity) (by nlinarith)).trans hlog_Teff
          have hpole1 : ‖if χ = 1 then (1 : ℂ) / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - 1) else 0‖ ≤ 1 := by
            split_ifs
            · rw [norm_div, norm_one]
              have hden : (1 : ℝ) ≤ ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - 1‖ := by
                have h := Complex.abs_re_le_norm ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - 1)
                have hre : ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - 1).re = -(3 / 2 : ℝ) := by
                  simp; ring
                rw [hre, abs_of_neg (by norm_num)] at h; linarith
              exact div_le_one_of_le₀ hden (norm_nonneg _)
            · simp
          have hsum_le :
              ‖∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
                (1 : ℂ) / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ)‖ ≤
                2 * C_1 * (3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
            refine (norm_sum_le _ _).trans ?_
            have hterm : ∀ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
                ‖(1 : ℂ) / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ)‖ ≤ 2 := by
              intro ρ hρ
              have hρZ := (Finset.mem_filter.mp hρ).1
              have hden : (1 / 2 : ℝ) ≤ ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ‖ := by
                have h := Complex.abs_re_le_norm ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ)
                have hre : ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ).re = -(1 / 2) - ρ.re := by simp
                rw [hre, abs_of_neg (by linarith [(hZ_strip ρ hρZ).1])] at h
                linarith [(hZ_strip ρ hρZ).1]
              rw [norm_div, norm_one]
              calc (1 : ℝ) / ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ‖
                  ≤ 1 / (1 / 2) := div_le_div_of_nonneg_left zero_le_one (by norm_num) hden
                _ = 2 := by norm_num
            calc ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
                  ‖(1 : ℂ) / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ)‖
                ≤ ∑ _ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1), (2 : ℝ) := Finset.sum_le_sum hterm
              _ = ((Z_all.filter (fun ρ => |ρ.im - t| ≤ 1)).card : ℝ) * 2 := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ (C_1 * Real.log ((q : ℝ) * (|t| + 2))) * 2 :=
                  mul_le_mul_of_nonneg_right (hZ_dens t (by linarith)) (by norm_num)
              _ ≤ (C_1 * (3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1))) * 2 :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le hC1) (by norm_num)
              _ = 2 * C_1 * (3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by ring
          have hL_bd : ‖Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤ M_V := by
            have hrew : Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) =
                (Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) -
                  (if χ = 1 then 1 / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - 1) else 0) +
                  ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
                    1 / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ)) +
                (if χ = 1 then 1 / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - 1) else 0) -
                ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - t| ≤ 1),
                  1 / ((((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) - ρ) := by ring
            rw [hrew]
            refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
            have hBL := mul_le_mul_of_nonneg_left hlog_le hB
            have h1_le : (1 : ℝ) ≤ (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by nlinarith
            dsimp only [M_V]
            linarith
          rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)).re = -(1 / 2) := by simp
          rw [hre, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hL_bd (Real.rpow_nonneg hx0.le _)) (inv_nonneg.mpr (norm_nonneg _))
        -- Bound `∫_{-T_star}^{T_star} ‖-1/2 + i t‖⁻¹ dt ≤ 4 + 2 * log T_star ≤ 6 * (log x + 1)`
        have hinv_cont : Continuous (fun t : ℝ => ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹) := by
          refine Continuous.inv₀ (by fun_prop) fun t h0 => ?_
          rw [norm_eq_zero] at h0; have := congrArg Complex.re h0; simp at this
        have hinv_int : ∫ t in (-T_star)..T_star, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ ≤
            6 * (Real.log x + 1) := by
          have hmid : ∫ t in (-1 : ℝ)..1, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ ≤ 4 := by
            have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ ≤ 2 := by
              intro t _
              have hden : (1 / 2 : ℝ) ≤ ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ := by
                have := Complex.abs_re_le_norm (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))
                simpa using this
              calc ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹
                  ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hden
                _ = 2 := by norm_num
            calc ∫ t in (-1 : ℝ)..1, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹
                ≤ ∫ _t in (-1 : ℝ)..1, (2 : ℝ) :=
                  intervalIntegral.integral_mono_on (by norm_num)
                    (hinv_cont.intervalIntegrable _ _) intervalIntegrable_const hpt
              _ = 4 := by rw [intervalIntegral.integral_const, smul_eq_mul]; norm_num
          have hpos_tail : ∫ t in (1 : ℝ)..T_star, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ ≤
              Real.log T_star := by
            have hint_inv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume (1 : ℝ) T_star := by
              refine (ContinuousOn.inv₀ continuousOn_id fun t ht => ?_).intervalIntegrable
              rw [Set.uIcc_of_le hT_star_ge1] at ht; dsimp only [id_eq]; linarith [ht.1]
            have hpt : ∀ t ∈ Set.Icc (1 : ℝ) T_star,
                ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ ≤ t⁻¹ := fun t ht => by
              have ht0 : 0 < t := by linarith [ht.1]
              have hle : t ≤ ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ := by
                simpa [abs_of_pos ht0] using Complex.abs_im_le_norm (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))
              exact inv_anti₀ ht0 hle
            calc ∫ t in (1 : ℝ)..T_star, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹
                ≤ ∫ t in (1 : ℝ)..T_star, t⁻¹ :=
                  intervalIntegral.integral_mono_on hT_star_ge1
                    (hinv_cont.intervalIntegrable _ _) hint_inv hpt
              _ = Real.log T_star := by rw [integral_inv_of_pos zero_lt_one hT_star_pos, div_one]
          have hneg_tail : ∫ t in (-T_star)..(-1 : ℝ),
              ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ ≤ Real.log T_star := by
            have hcomp : ∫ t in (-T_star)..(-1 : ℝ), ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ =
                ∫ u in (1 : ℝ)..T_star, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (u : ℂ))‖⁻¹ := by
              have h1 := intervalIntegral.integral_comp_neg
                (f := fun u : ℝ => ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (u : ℂ))‖⁻¹)
                (a := -T_star) (b := -1)
              simp only [neg_neg] at h1
              rw [← h1]
              refine intervalIntegral.integral_congr fun t _ => ?_
              congr 1; rw [← Complex.norm_conj]; congr 1
              apply Complex.ext <;> simp
            rw [hcomp]; exact hpos_tail
          have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
            (hinv_cont.intervalIntegrable (μ := volume) (-T_star) (-1))
            (hinv_cont.intervalIntegrable (μ := volume) (-1) 1)
          have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
            (hinv_cont.intervalIntegrable (μ := volume) (-T_star) 1)
            (hinv_cont.intervalIntegrable (μ := volume) 1 T_star)
          have hlog_Tstar : Real.log T_star ≤ 2 * Real.log x := by
            have hlogx_lex : Real.log x + 1 ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
            have hT_sq : T_star ≤ x ^ 2 := by nlinarith
            calc Real.log T_star ≤ Real.log (x ^ 2) := Real.log_le_log hT_star_pos hT_sq
              _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
          linarith
        have hV_int_le : ‖∫ t in (-T_star)..T_star,
            Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) *
              (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) /
              (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
            6 * (3 * (B + 2 * C_1) + 1) * (Real.log (q : ℝ) + 1) *
              (x ^ (-(1 / 2 : ℝ)) * (Real.log x + 1) ^ 2) := by
          calc ‖∫ t in (-T_star)..T_star, _‖
              ≤ ∫ t in (-T_star)..T_star, ‖Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) *
                  (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) /
                  (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖ :=
                intervalIntegral.norm_integral_le_integral_norm (by linarith)
            _ ≤ ∫ t in (-T_star)..T_star, M_V * x ^ (-(1 / 2 : ℝ)) *
                  ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ :=
                intervalIntegral.integral_mono_on (by linarith)
                  hV_cont.intervalIntegrable.norm
                  ((hinv_cont.intervalIntegrable _ _).const_mul _) hV_pt
            _ = (M_V * x ^ (-(1 / 2 : ℝ))) *
                  ∫ t in (-T_star)..T_star, ‖(((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ))‖⁻¹ :=
                intervalIntegral.integral_const_mul _ _
            _ ≤ (M_V * x ^ (-(1 / 2 : ℝ))) * (6 * (Real.log x + 1)) :=
                mul_le_mul_of_nonneg_left hinv_int (by positivity)
            _ = 6 * (3 * (B + 2 * C_1) + 1) * (Real.log (q : ℝ) + 1) *
                  (x ^ (-(1 / 2 : ℝ)) * (Real.log x + 1) ^ 2) := by dsimp only [M_V]; ring
        have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        calc (2 * Real.pi)⁻¹ * ‖∫ t in (-T_star)..T_star, _‖
            ≤ 1 * (6 * (3 * (B + 2 * C_1) + 1) * (Real.log (q : ℝ) + 1) *
                (x ^ (-(1 / 2 : ℝ)) * (Real.log x + 1) ^ 2)) :=
              mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1) hV_int_le (norm_nonneg _) zero_le_one
          _ ≤ 1 * (6 * (3 * (B + 2 * C_1) + 1) * (Real.log (q : ℝ) + 1) * 25) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (rpow_neg_half_mul_log_sq_le hx) (by positivity))
                zero_le_one
          _ = K_V * (Real.log (q : ℝ) + 1) := by dsimp only [K_V]; ring
      -- Piece 4: Top & bottom horizontal integrals on `Im(s) = ±T_star` (LINEAR in `log q` via AM-GM!)
      have hHoriz_bd : ∀ s_im : ℝ, (s_im = T_star ∨ s_im = -T_star) →
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
            ∫ σ in (-(1 / 2 : ℝ))..c,
              Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) *
                (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ)) / ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
            (K_H / 2) * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
              (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
        intro s_im hsim
        have habs_sim : |s_im| = T_star := by
          rcases hsim with rfl | rfl <;> simp [abs_of_pos hT_star_pos]
        rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        -- Continuity of the horizontal integrand from `hL_holo`
        have hH_cont : ContinuousOn
            (fun σ : ℝ => Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) *
              (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ)) / ((σ : ℂ) + I * (s_im : ℂ)))
            (Set.uIcc (-(1 / 2 : ℝ)) c) := by
          rw [Set.uIcc_of_le (by linarith)]
          have hsub : (fun σ : ℝ => (σ : ℂ) + I * (s_im : ℂ)) '' Set.Icc (-(1 / 2 : ℝ)) c ⊆
              closedRect (-(1 / 2)) c (-T_star) T_star := by
            rintro _ ⟨σ, hσ, rfl⟩
            exact ⟨by simpa using hσ, by simp [abs_le.mp (le_of_eq habs_sim)]⟩
          have hP : ContinuousOn (fun s => ∑ p ∈ J, a p / (s - p))
              ((fun σ : ℝ => (σ : ℂ) + I * (s_im : ℂ)) '' Set.Icc (-(1 / 2 : ℝ)) c) := by
            refine continuousOn_finsetSum J fun p hpJ => continuousOn_const.div
              (continuousOn_id.sub continuousOn_const) ?_
            rintro _ ⟨σ, _, rfl⟩ h0
            have him := congrArg Complex.im h0; simp at him
            rcases hsim with rfl | rfl
            · linarith [(hp p hpJ).2.2]
            · linarith [(hp p hpJ).2.1]
          have hcont_L : ContinuousOn (Stage3ZeroFreeRegion.negLogDerivL χ)
              ((fun σ : ℝ => (σ : ℂ) + I * (s_im : ℂ)) '' Set.Icc (-(1 / 2 : ℝ)) c) :=
            ((hL_holo.continuousOn.mono hsub).add hP).congr fun s _ => by simp only [Pi.add_apply]; ring
          have hmap : ContinuousOn (fun σ : ℝ => (σ : ℂ) + I * (s_im : ℂ)) (Set.Icc (-(1 / 2 : ℝ)) c) :=
            by fun_prop
          have h1 := hcont_L.comp hmap (Set.mapsTo_image _ _)
          have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
          have hpow : Continuous (fun σ : ℝ => (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ))) := by
            have hEq : (fun σ : ℝ => (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ))) =
                fun σ : ℝ => cexp (Complex.log (x : ℂ) * ((σ : ℂ) + I * (s_im : ℂ))) :=
              funext fun σ => Complex.cpow_def_of_ne_zero hxC _
            rw [hEq]; fun_prop
          refine (h1.mul hpow.continuousOn).div hmap fun σ _ h0 => ?_
          have him := congrArg Complex.im h0; simp at him; rw [him, abs_zero] at habs_sim; linarith
        have hcont_pole : Continuous (fun σ : ℝ => ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) := by
          refine continuous_finsetSum Z_band fun ρ hρ => Continuous.inv₀ (by fun_prop) fun σ h0 => ?_
          rw [norm_eq_zero] at h0
          have him := congrArg Complex.im h0; simp at him
          rcases hsim with rfl | rfl
          · exact (hT_avoid_band ρ hρ).1 (by linarith)
          · exact (hT_avoid_band ρ hρ).2 (by linarith)
        set B_lin : ℝ := (3 * B + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1)
        have hH_pt : ∀ σ ∈ Set.Icc (-(1 / 2 : ℝ)) c,
            ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) *
              (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ)) / ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
            (3 * x / T_star) * (B_lin + ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) := by
          intro σ hσ
          have hne1 : χ = 1 → ((σ : ℂ) + I * (s_im : ℂ)) ≠ 1 := fun _ h0 => by
            have := congrArg Complex.im h0; simp at this; rw [this, abs_zero] at habs_sim; linarith
          have hneZ : ∀ ρ ∈ Z_all, ((σ : ℂ) + I * (s_im : ℂ)) ≠ ρ := fun ρ hρ h0 => by
            have := congrArg Complex.im h0; simp at this; exact havoid_all ρ hρ (by rw [← this, habs_sim])
          have hpf := hZ_pf σ s_im hσ.1 (hσ.2.trans hc3) (by rw [habs_sim]; linarith) hne1 hneZ
          have hlog_le : Real.log ((q : ℝ) * (|s_im| + 2)) ≤
              3 * (Real.log (q : ℝ) + 1) * (Real.log x + 1) :=
            (Real.log_le_log (by positivity) (by rw [habs_sim]; nlinarith)).trans hlog_Teff
          have hpole1 : ‖if χ = 1 then (1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - 1) else 0‖ ≤ 1 := by
            split_ifs
            · rw [norm_div, norm_one]
              have hden : (1 : ℝ) ≤ ‖((σ : ℂ) + I * (s_im : ℂ)) - 1‖ :=
                hT_star_ge1.trans (by simpa [habs_sim] using Complex.abs_im_le_norm (((σ : ℂ) + I * (s_im : ℂ)) - 1))
              exact div_le_one_of_le₀ hden (norm_nonneg _)
            · simp
          have hsub_band : Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1) ⊆ Z_band := by
            intro ρ hρ
            obtain ⟨hρZ, hd⟩ := Finset.mem_filter.mp hρ
            have htri := abs_abs_sub_abs_le_abs_sub ρ.im s_im
            rw [habs_sim] at htri
            have habs_bd := abs_le.mp (htri.trans hd)
            exact Finset.mem_filter.mpr ⟨hρZ, by linarith [hT_mem.1], by linarith [hT_mem.2]⟩
          have hsum_le :
              ‖∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
                (1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)‖ ≤
                ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹ := by
            refine (norm_sum_le _ _).trans ?_
            have heq : ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
                ‖(1 : ℂ) / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)‖ =
                ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
                  ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹ :=
              Finset.sum_congr rfl fun ρ _ => by rw [norm_div, norm_one, one_div]
            rw [heq]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub_band fun _ _ _ => inv_nonneg.mpr (norm_nonneg _)
          have hL_bd : ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
              B_lin + ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹ := by
            have hrew : Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) =
                (Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) -
                  (if χ = 1 then 1 / (((σ : ℂ) + I * (s_im : ℂ)) - 1) else 0) +
                  ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
                    1 / (((σ : ℂ) + I * (s_im : ℂ)) - ρ)) +
                (if χ = 1 then 1 / (((σ : ℂ) + I * (s_im : ℂ)) - 1) else 0) -
                ∑ ρ ∈ Z_all.filter (fun ρ => |ρ.im - s_im| ≤ 1),
                  1 / (((σ : ℂ) + I * (s_im : ℂ)) - ρ) := by ring
            rw [hrew]
            refine (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
            have hBL := mul_le_mul_of_nonneg_left hlog_le hB
            have h1_le : (1 : ℝ) ≤ (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by nlinarith
            dsimp only [B_lin]
            linarith
          have hx_pow_le : x ^ σ ≤ 3 * x :=
            (Real.rpow_le_rpow_of_exponent_le hx1 hσ.2).trans hxc_le
          have hden_ge : T_star ≤ ‖(σ : ℂ) + I * (s_im : ℂ)‖ := by
            simpa [habs_sim] using Complex.abs_im_le_norm ((σ : ℂ) + I * (s_im : ℂ))
          rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
          have hre : ((σ : ℂ) + I * (s_im : ℂ)).re = σ := by simp
          rw [hre]
          calc ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ))‖ * x ^ σ /
                ‖(σ : ℂ) + I * (s_im : ℂ)‖
              ≤ (B_lin + ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) * (3 * x) / T_star :=
                div_le_div₀ (by positivity)
                  (mul_le_mul hL_bd hx_pow_le (Real.rpow_nonneg hx0.le _) (by
                    have : 0 ≤ B_lin := by positivity
                    exact add_nonneg this (Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (norm_nonneg _))))
                  hT_star_pos hden_ge
            _ = (3 * x / T_star) * (B_lin + ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) := by
                ring
        have hpole_int_le : ∫ σ in (-(1 / 2 : ℝ))..c,
            ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹ ≤
            64 * (12 * C_1 + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
          have hsqrt_le : Real.sqrt (c - -(1 / 2 : ℝ)) ≤ 2 :=
            calc Real.sqrt (c - -(1 / 2 : ℝ)) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by linarith)
              _ = 2 := by
                  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
                  rw [h4, Real.sqrt_sq (by norm_num)]
          have hNb_nn : (0 : ℝ) ≤ (Z_band.card : ℝ) := Nat.cast_nonneg _
          have hcard1 : (Z_band.card : ℝ) + 1 ≤ (12 * C_1 + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
            have h1_le : (1 : ℝ) ≤ (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by nlinarith
            linarith
          have hraw : ∫ σ in (-(1 / 2 : ℝ))..c,
              ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹ ≤
              32 * Real.sqrt (c - -(1 / 2 : ℝ)) * ((Z_band.card : ℝ) + 1) := by
            rcases hsim with rfl | rfl
            · exact hH_top_int
            · have hcongr : ∫ σ in (-(1 / 2 : ℝ))..c,
                  ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) - ρ‖⁻¹ =
                  ∫ σ in (-(1 / 2 : ℝ))..c,
                  ∑ ρ ∈ Z_band, ‖((σ : ℂ) - I * (T_star : ℂ)) - ρ‖⁻¹ :=
                intervalIntegral.integral_congr fun σ _ => Finset.sum_congr rfl fun ρ _ => by
                  congr 2; push_cast; ring
              rw [hcongr]; exact hH_bot_int
          calc ∫ σ in (-(1 / 2 : ℝ))..c, ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹
              ≤ 32 * Real.sqrt (c - -(1 / 2 : ℝ)) * ((Z_band.card : ℝ) + 1) := hraw
            _ ≤ (32 * 2) * ((12 * C_1 + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) :=
                mul_le_mul (by linarith) hcard1 (by linarith) (by norm_num)
            _ = 64 * (12 * C_1 + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by ring
        have hInt_bd : ‖∫ σ in (-(1 / 2 : ℝ))..c,
            Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) *
              (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ)) / ((σ : ℂ) + I * (s_im : ℂ))‖ ≤
            (3 * x / T_star) *
              ((4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
          have hint_rhs : IntervalIntegrable
              (fun σ : ℝ => (3 * x / T_star) * (B_lin + ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹))
              volume (-(1 / 2 : ℝ)) c :=
            (intervalIntegrable_const.add (hcont_pole.intervalIntegrable _ _)).const_mul _
          calc ‖∫ σ in (-(1 / 2 : ℝ))..c, _‖
              ≤ ∫ σ in (-(1 / 2 : ℝ))..c, ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (s_im : ℂ)) *
                  (x : ℂ) ^ ((σ : ℂ) + I * (s_im : ℂ)) / ((σ : ℂ) + I * (s_im : ℂ))‖ :=
                intervalIntegral.norm_integral_le_integral_norm (by linarith)
            _ ≤ ∫ σ in (-(1 / 2 : ℝ))..c,
                  (3 * x / T_star) * (B_lin + ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹) :=
                intervalIntegral.integral_mono_on (by linarith)
                  hH_cont.intervalIntegrable.norm hint_rhs hH_pt
            _ = (3 * x / T_star) *
                  ((∫ _σ in (-(1 / 2 : ℝ))..c, B_lin) +
                   (∫ σ in (-(1 / 2 : ℝ))..c, ∑ ρ ∈ Z_band, ‖((σ : ℂ) + I * (s_im : ℂ)) - ρ‖⁻¹)) := by
                rw [intervalIntegral.integral_const_mul,
                    intervalIntegral.integral_add intervalIntegrable_const
                      (hcont_pole.intervalIntegrable _ _)]
            _ ≤ (3 * x / T_star) *
                  (4 * B_lin + 64 * (12 * C_1 + 1) * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
                refine mul_le_mul_of_nonneg_left (add_le_add ?_ hpole_int_le) (by positivity)
                rw [intervalIntegral.integral_const, smul_eq_mul]
                have : 0 ≤ B_lin := by positivity
                nlinarith
            _ = (3 * x / T_star) *
                  ((4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) * (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
                dsimp only [B_lin]; ring
        have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
        have hlogx_le_sq : Real.log x + 1 ≤ (Real.log x + 1) ^ 2 := by nlinarith
        have hx_div_lin : x / T_star * (Real.log x + 1) ≤
            2 * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1)) :=
          (mul_le_mul_of_nonneg_left hlogx_le_sq (by positivity)).trans hx_div_Tstar
        calc (2 * Real.pi)⁻¹ * ‖∫ σ in (-(1 / 2 : ℝ))..c, _‖
            ≤ 1 * ((3 * x / T_star) *
                ((4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) * (Real.log (q : ℝ) + 1) * (Real.log x + 1))) :=
              mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1) hInt_bd (norm_nonneg _) zero_le_one
          _ = 3 * (4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) * (Real.log (q : ℝ) + 1) *
                (x / T_star * (Real.log x + 1)) := by ring
          _ ≤ 3 * (4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) * (Real.log (q : ℝ) + 1) *
                (2 * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1))) :=
              mul_le_mul_of_nonneg_left hx_div_lin (by positivity)
          _ ≤ (K_H / 2) * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
                (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
              have hfac : 6 * (4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) ≤ K_H / 2 := by
                dsimp only [K_H]; linarith [show 0 ≤ 4 * (3 * B + 1) + 64 * (12 * C_1 + 1) by positivity]
              have hrew : 3 * (4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) * (Real.log (q : ℝ) + 1) *
                    (2 * (x / T * (Real.log x + 1) ^ 2 + (Real.log x + 1))) =
                  6 * (4 * (3 * B + 1) + 64 * (12 * C_1 + 1)) *
                    (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
                      (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by ring
              rw [hrew]
              exact mul_le_mul_of_nonneg_right hfac (by positivity)
      -- Combine Perron + Res0 + Left + Top + Bot!
      have hBot_bd : ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
          ∫ σ in (-(1 / 2 : ℝ))..c,
            Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) - I * (T_star : ℂ)) *
              (x : ℂ) ^ ((σ : ℂ) - I * (T_star : ℂ)) / ((σ : ℂ) - I * (T_star : ℂ))‖ ≤
          (K_H / 2) * (x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
            (Real.log (q : ℝ) + 1) * (Real.log x + 1)) := by
        have hcongr : ∫ σ in (-(1 / 2 : ℝ))..c,
            Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) - I * (T_star : ℂ)) *
              (x : ℂ) ^ ((σ : ℂ) - I * (T_star : ℂ)) / ((σ : ℂ) - I * (T_star : ℂ)) =
            ∫ σ in (-(1 / 2 : ℝ))..c,
            Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) *
              (x : ℂ) ^ ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) / ((σ : ℂ) + I * ((-T_star : ℝ) : ℂ)) :=
          intervalIntegral.integral_congr fun σ _ => by
            have hsub : (σ : ℂ) - I * (T_star : ℂ) = (σ : ℂ) + I * ((-T_star : ℝ) : ℂ) := by
              push_cast; ring
            rw [hsub]
        rw [hcongr]
        exact hHoriz_bd (-T_star) (Or.inr rfl)
      have hTop_bd := hHoriz_bd T_star (Or.inl rfl)
      have hsplit : Stage2DirichletAP.chebyshevPsiChar χ x - (if χ = 1 then (x : ℂ) else 0) +
          ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ =
          (Stage2DirichletAP.chebyshevPsiChar χ x - truncatedPerronPsi χ x c T_star) +
          Stage3ZeroFreeRegion.negLogDerivL χ 0 +
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            (∫ t in (-T_star)..T_star,
              Stage3ZeroFreeRegion.negLogDerivL χ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) *
                (x : ℂ) ^ (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)) /
                (((-(1 / 2 : ℝ) : ℝ) : ℂ) + I * (t : ℂ)))) +
          ((2 * (Real.pi : ℂ) * I)⁻¹ *
            (∫ σ in (-(1 / 2 : ℝ))..c,
              Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) + I * (T_star : ℂ)) *
                (x : ℂ) ^ ((σ : ℂ) + I * (T_star : ℂ)) / ((σ : ℂ) + I * (T_star : ℂ)))) -
          ((2 * (Real.pi : ℂ) * I)⁻¹ *
            (∫ σ in (-(1 / 2 : ℝ))..c,
              Stage3ZeroFreeRegion.negLogDerivL χ ((σ : ℂ) - I * (T_star : ℂ)) *
                (x : ℂ) ^ ((σ : ℂ) - I * (T_star : ℂ)) / ((σ : ℂ) - I * (T_star : ℂ)))) := by
        linear_combination hshift
      rw [hsplit]
      refine (norm_sub_le _ _).trans ((add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl).trans ?_)
      have hlogq_le_rhs : Real.log (q : ℝ) + 1 ≤
          x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 +
            (Real.log (q : ℝ) + 1) * (Real.log x + 1) := by
        have h1 : 0 ≤ x / T * (Real.log (q : ℝ) + 1) * (Real.log x + 1) ^ 2 := by positivity
        nlinarith
      have hR0' := hRes0.trans (mul_le_mul_of_nonneg_left hlogq_le_rhs (by positivity))
      have hLV' := hLeft_bd.trans (mul_le_mul_of_nonneg_left hlogq_le_rhs (by positivity))
      dsimp only [C_R]
      linarith
  refine ⟨C_R, ⟨H.theta_ge_half, H.theta_lt_one, H.CN_nonneg, hCR_nn, ?_, ?_⟩⟩
  · -- `zeta_explicit` (`q = 1`, `χ = 1`)
    intro x T hx hT
    obtain ⟨Z, hZs, hZc, hZe⟩ := hunified 1 (1 : DirichletCharacter ℂ 1) x T hx hT
    refine ⟨Z, hZs, hZc, ?_⟩
    simp only [↓reduceIte, chebyshevPsiChar_modOne_eq, Nat.cast_one, Real.log_one, zero_add,
      mul_one, one_mul] at hZe
    have hre_eq : (RHDirect.chebyshevPsi x : ℂ) - (x : ℂ) + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ =
        (((RHDirect.chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re : ℝ) : ℂ)) +
        (((∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).im : ℝ) : ℂ)) * I := by
      apply Complex.ext <;> simp [Complex.re_sum, Complex.im_sum]
    have hre : ((RHDirect.chebyshevPsi x : ℂ) - (x : ℂ) + ∑ ρ ∈ Z, (x : ℂ) ^ ρ / ρ).re =
        RHDirect.chebyshevPsi x - x + ∑ ρ ∈ Z, ((x : ℂ) ^ ρ / ρ).re := by
      simp [Complex.re_sum]
    rw [← hre]
    exact (Complex.abs_re_le_norm _).trans hZe
  · -- `char_explicit` (`q ≥ 2`, `χ ≠ 1`)
    intro q _ hq χ hχ x T hx hT
    obtain ⟨Z, hZs, hZc, hZe⟩ := hunified q χ x T hx hT
    refine ⟨Z, hZs, hZc, ?_⟩
    simpa only [hχ, ↓reduceIte, sub_zero] using hZe

/-- **End-to-End Discharge of `PsiCharPowerBound θ'` (every `θ' ∈ (θ, 1)`) & `Stage2PrimePairs`
(`LinnikAPDyadic`, `LinnikAPInterval`, `PairSupply`, `PairEx`, `SmallOne`) from
`MeromorphicLogDerivPackage`**:
composes `truncatedExplicitFormulaPackage_of_meromorphicPackage` directly with
`Stage3ZeroFreeRegion.psiCharPowerBound_of_truncatedExplicitFormula`,
`Stage3ZeroFreeRegion.stage2PrimePairs_of_truncatedExplicitFormula`, and
`Stage4ExplicitFormula.stage4_bridge_of_truncatedExplicitFormula`! -/
theorem stage2PrimePairs_of_meromorphicPackage {θ B C_N C_1 : ℝ}
    (H : MeromorphicLogDerivPackage θ B C_N C_1) :
    (∀ θ' : ℝ, θ < θ' → θ' < 1 → Stage2DirichletAP.PsiCharPowerBound θ') ∧
      Stage2PrimePairs.LinnikAPDyadic ∧
      Stage2PrimePairs.LinnikAPInterval ∧
      HostFieldSupply.PairSupply ∧
      ThetaSlopeEngine.PairEx ∧
      HostFieldSupply.SmallOne := by
  obtain ⟨C_R, hPkg⟩ := truncatedExplicitFormulaPackage_of_meromorphicPackage H
  exact ⟨fun θ' hlo hhi => Stage3ZeroFreeRegion.psiCharPowerBound_of_truncatedExplicitFormula hPkg hlo hhi,
    Stage3ZeroFreeRegion.stage2PrimePairs_of_truncatedExplicitFormula hPkg⟩

end RHDirect.Stage5ContourExplicit

end
