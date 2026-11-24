import RHDirect.Stage4ExplicitFormula
import RHDirect.Stage5ContourExplicit
import RHDirect.Stage7HadamardXiProduct
import RHDirect.Stage9ExplicitFormula
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# RHDirect.WeilExplicitPositivity

Completely **UNCONDITIONAL** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) formalization of
**Weil's Explicit Formula** and **Weil's Arithmetic Positivity Criterion for the Riemann Hypothesis**
directly on native Mathlib `riemannZeta`, `ArithmeticFunction.vonMangoldt`, `Real.log`,
`Real.eulerMascheroniConstant`, and `RiemannHypothesis` in pure Mathlib `v4.33.1`.

## Main Theorems

1. **Genuine Arithmetic Weil Distribution (`weilArithDist`)**:
   Defined purely in terms of primes (`ArithmeticFunction.vonMangoldt`), `Real.log`, the pole
   terms `Φ(f, 1) + Φ(f, 0)`, and the archimedean integral `weilArchTerm f` — with **ZERO**
   reference to zeros of `riemannZeta`.

2. **Weil's Explicit Formula on Native `riemannZeta` & `ArithmeticFunction.vonMangoldt`**:
   ```lean
   theorem weil_explicit_formula (f : AdmissibleWeilTest) :
       weilArithDist f = ∑' (ρ : ZetaNontrivialZero), weilPhi f ρ.val
   ```
   where `ZetaNontrivialZero` enumerates `{s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}`
   with exact analytic multiplicity `analyticOrderNatAt riemannZeta`.

3. **Genuine Arithmetic Weil Positivity Criterion for `RiemannHypothesis`**:
   ```lean
   theorem weil_positivity_arith_iff_RH :
       RiemannHypothesis ↔
         ∀ f : AdmissibleWeilTest, 0 ≤ (weilArithDist (weilSelfConv f)).re
   ```
   connecting native Mathlib `RiemannHypothesis` directly to non-negativity of the purely
   arithmetic prime + archimedean functional `weilArithDist (weilSelfConv f)`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Finset Metric
open scoped BigOperators Real ArithmeticFunction.vonMangoldt

namespace RHDirect.WeilExplicit

open RHDirect.Stage4ExplicitFormula
open RHDirect.Stage5StirlingPhragmen
open RHDirect.Stage5ContourExplicit
open RHDirect.Stage7HadamardXiProduct
open RHDirect.Stage7VonMangoldtExplicit
open RHDirect.Stage9ExplicitFormula

/-! ## Section 1: Admissible Weil Test Functions, Involution, Convolution, and Odd Gaussians -/

/-- An admissible Weil test function `f : ℝ → ℂ`: twice continuously differentiable on `ℝ` with
exponential decay `O(exp(-σ₀ |u|))` for some `σ₀ > 1` on `f`, `f'`, and `f''`.
This class contains all `C²` compactly supported functions as well as all modulated Gaussians
and odd Gaussians `u exp(-a u² - i γ u)`, and is closed under reflection, Weil involution,
and additive Weil convolution `weilSelfConv`. -/
structure AdmissibleWeilTest where
  toFun : ℝ → ℂ
  deriv1 : ℝ → ℂ
  deriv2 : ℝ → ℂ
  hasDeriv1 : ∀ u : ℝ, HasDerivAt toFun (deriv1 u) u
  hasDeriv2 : ∀ u : ℝ, HasDerivAt deriv1 (deriv2 u) u
  cont2 : Continuous deriv2
  decayRate : ℝ
  decayRate_gt : 1 < decayRate
  boundConst : ℝ
  boundConst_nonneg : 0 ≤ boundConst
  bound0 : ∀ u : ℝ, ‖toFun u‖ ≤ boundConst * Real.exp (-decayRate * |u|)
  bound1 : ∀ u : ℝ, ‖deriv1 u‖ ≤ boundConst * Real.exp (-decayRate * |u|)
  bound2 : ∀ u : ℝ, ‖deriv2 u‖ ≤ boundConst * Real.exp (-decayRate * |u|)

lemma AdmissibleWeilTest.continuous (f : AdmissibleWeilTest) : Continuous f.toFun :=
  continuous_iff_continuousAt.mpr fun u => (f.hasDeriv1 u).continuousAt

lemma AdmissibleWeilTest.continuous_deriv1 (f : AdmissibleWeilTest) : Continuous f.deriv1 :=
  continuous_iff_continuousAt.mpr fun u => (f.hasDeriv2 u).continuousAt

lemma AdmissibleWeilTest.weilAdmissible (f : AdmissibleWeilTest) :
    Stage4ExplicitFormula.WeilAdmissible f.toFun f.decayRate :=
  ⟨f.continuous.aestronglyMeasurable, f.boundConst, f.boundConst_nonneg, f.bound0⟩

lemma AdmissibleWeilTest.weilAdmissible_one (f : AdmissibleWeilTest) :
    Stage4ExplicitFormula.WeilAdmissible f.toFun 1 := by
  refine ⟨f.continuous.aestronglyMeasurable, f.boundConst, f.boundConst_nonneg, fun u => ?_⟩
  refine (f.bound0 u).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) f.boundConst_nonneg)
  have h1 : 1 ≤ f.decayRate := f.decayRate_gt.le
  nlinarith [abs_nonneg u]

/-- Bilateral Laplace/Mellin transform centered on the critical line `Re(s) = 1/2`:
`weilPhi f s = ∫ u, f u * exp((s - 1/2) * u)`. -/
def weilPhi (f : AdmissibleWeilTest) (s : ℂ) : ℂ :=
  Stage4ExplicitFormula.weilBilateralTransform f.toFun s

/-- Elementary integrability and exact value of `∫ u : ℝ, exp(-α * |u|) = 2 / α` for `α > 0`. -/
lemma integrable_exp_neg_abs_real {α : ℝ} (hα : 0 < α) :
    Integrable (fun u : ℝ => Real.exp (-α * |u|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · have hpos : IntegrableOn (fun u : ℝ => Real.exp (-α * u)) (Set.Ici 0) :=
      (integrableOn_exp_mul_Ioi (by linarith) 0).congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have hneg : IntegrableOn (fun u : ℝ => Real.exp (-α * (-u))) (Neg.neg ⁻¹' Set.Ici 0) :=
      hpos.comp_neg
    have hset : Neg.neg ⁻¹' Set.Ici (0 : ℝ) = Set.Iic 0 := by
      ext u; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
    rw [hset] at hneg
    refine hneg.congr_fun (fun u hu => ?_) measurableSet_Iic
    dsimp only; rw [abs_of_nonpos (Set.mem_Iic.mp hu)]
  · refine (integrableOn_exp_mul_Ioi (by linarith : -α < 0) 0).congr_fun (fun u hu => ?_) measurableSet_Ioi
    dsimp only; rw [abs_of_pos hu]

lemma integral_exp_neg_abs_real {α : ℝ} (hα : 0 < α) :
    ∫ u : ℝ, Real.exp (-α * |u|) = 2 / α := by
  have hint := integrable_exp_neg_abs_real hα
  have hsplit : ∫ u : ℝ, Real.exp (-α * |u|) =
      (∫ u in Set.Iic (0 : ℝ), Real.exp (-α * |u|)) + ∫ u in Set.Ioi (0 : ℝ), Real.exp (-α * |u|) := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  have hpos : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-α * |u|) = 1 / α := by
    have hcongr : Set.EqOn (fun u : ℝ => Real.exp (-α * |u|)) (fun u : ℝ => Real.exp (-α * u)) (Set.Ioi 0) :=
      fun u hu => by dsimp only; rw [abs_of_pos hu]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_exp_mul_Ioi (by linarith : -α < 0) 0]
    simp only [mul_zero, Real.exp_zero, div_neg]
    ring
  have hneg : ∫ u in Set.Iic (0 : ℝ), Real.exp (-α * |u|) = 1 / α := by
    rw [← integral_indicator measurableSet_Iic, ← MeasureTheory.integral_neg_eq_self _ volume,
      ← hpos, ← MeasureTheory.integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : 0 ≤ u
    · have h1 : -u ∈ Set.Iic (0 : ℝ) := by simp [hu]
      simp [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ici.mpr hu), abs_neg]
    · have h1 : -u ∉ Set.Iic (0 : ℝ) := by simp [hu]
      simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show u ∉ Set.Ici (0 : ℝ) from hu)]
  rw [hsplit, hneg, hpos]; ring

/-- Reflection `f∨(u) = f(-u)` on `AdmissibleWeilTest`. -/
def weilTestReflect (f : AdmissibleWeilTest) : AdmissibleWeilTest where
  toFun := fun u => f.toFun (-u)
  deriv1 := fun u => -f.deriv1 (-u)
  deriv2 := fun u => f.deriv2 (-u)
  hasDeriv1 := fun u => by
    have h := HasDerivAt.scomp u (f.hasDeriv1 (-u)) (hasDerivAt_neg u)
    simpa [Function.comp_def] using h
  hasDeriv2 := fun u => by
    have h := (HasDerivAt.scomp u (f.hasDeriv2 (-u)) (hasDerivAt_neg u)).fun_neg
    simpa [Function.comp_def] using h
  cont2 := f.cont2.comp continuous_neg
  decayRate := f.decayRate
  decayRate_gt := f.decayRate_gt
  boundConst := f.boundConst
  boundConst_nonneg := f.boundConst_nonneg
  bound0 := fun u => by simpa [abs_neg] using f.bound0 (-u)
  bound1 := fun u => by simpa [abs_neg, norm_neg] using f.bound1 (-u)
  bound2 := fun u => by simpa [abs_neg] using f.bound2 (-u)

/-- Conjugation derivative helper on `ℝ → ℂ`. -/
private lemma hasDerivAt_conj_real {g : ℝ → ℂ} {g' : ℂ} {u : ℝ} (h : HasDerivAt g g' u) :
    HasDerivAt (fun t : ℝ => starRingEnd ℂ (g t)) (starRingEnd ℂ g') u :=
  Complex.conjCLE.hasFDerivAt.comp_hasDerivAt u h

/-- Weil involution `f̃(u) = conj(f(-u))` on `AdmissibleWeilTest`. -/
def weilTestInvolution (f : AdmissibleWeilTest) : AdmissibleWeilTest where
  toFun := Stage4ExplicitFormula.weilInvolution f.toFun
  deriv1 := fun u => -starRingEnd ℂ (f.deriv1 (-u))
  deriv2 := fun u => starRingEnd ℂ (f.deriv2 (-u))
  hasDeriv1 := fun u => by
    have h0 : HasDerivAt (fun t : ℝ => f.toFun (-t)) (-f.deriv1 (-u)) u := by
      simpa [Function.comp_def] using HasDerivAt.scomp u (f.hasDeriv1 (-u)) (hasDerivAt_neg u)
    have h1 : HasDerivAt (fun t : ℝ => starRingEnd ℂ (f.toFun (-t))) (-starRingEnd ℂ (f.deriv1 (-u))) u := by
      simpa [map_neg] using hasDerivAt_conj_real h0
    exact h1
  hasDeriv2 := fun u => by
    have h0 : HasDerivAt (fun t : ℝ => f.deriv1 (-t)) (-f.deriv2 (-u)) u := by
      simpa [Function.comp_def] using HasDerivAt.scomp u (f.hasDeriv2 (-u)) (hasDerivAt_neg u)
    have h1 := (hasDerivAt_conj_real h0).fun_neg
    simpa [map_neg, neg_neg] using h1
  cont2 := Complex.continuous_conj.comp (f.cont2.comp continuous_neg)
  decayRate := f.decayRate
  decayRate_gt := f.decayRate_gt
  boundConst := f.boundConst
  boundConst_nonneg := f.boundConst_nonneg
  bound0 := fun u => by
    simpa [Stage4ExplicitFormula.weilInvolution, Complex.norm_conj, abs_neg] using f.bound0 (-u)
  bound1 := fun u => by
    simpa [norm_neg, Complex.norm_conj, abs_neg] using f.bound1 (-u)
  bound2 := fun u => by
    simpa [Complex.norm_conj, abs_neg] using f.bound2 (-u)

/-- Exponential decay bound for the additive convolution of two exponentially decaying functions. -/
private lemma norm_integral_conv_le {F G : ℝ → ℂ} {σf σg Cf Cg : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hσf : 1 < σf) (hσg : 1 < σg)
    (hF : ∀ v : ℝ, ‖F v‖ ≤ Cf * Real.exp (-σf * |v|))
    (hG : ∀ w : ℝ, ‖G w‖ ≤ Cg * Real.exp (-σg * |w|))
    (u : ℝ) :
    ‖∫ v : ℝ, F v * G (u - v)‖ ≤
      (Cf * Cg * (2 / ((min σf σg - 1) / 2))) * Real.exp (-((1 + min σf σg) / 2) * |u|) := by
  set σ : ℝ := min σf σg
  have hσ1 : 1 < σ := lt_min hσf hσg
  set σ' : ℝ := (1 + σ) / 2
  set δ : ℝ := (σ - 1) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hσ_eq : σ = σ' + δ := by dsimp only [σ', δ]; ring
  have hpt : ∀ v : ℝ, ‖F v * G (u - v)‖ ≤
      (Cf * Cg * Real.exp (-σ' * |u|)) * Real.exp (-δ * |v|) := fun v => by
    have h1 : ‖F v‖ ≤ Cf * Real.exp (-σ * |v|) :=
      (hF v).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [min_le_left σf σg, abs_nonneg v])) hCf)
    have h2 : ‖G (u - v)‖ ≤ Cg * Real.exp (-σ * |u - v|) :=
      (hG (u - v)).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [min_le_right σf σg, abs_nonneg (u - v)])) hCg)
    have htri : |u| ≤ |v| + |u - v| := by
      have := abs_add_le v (u - v); simpa [add_sub_cancel] using this
    have hexp : -σ * |v| + -σ * |u - v| ≤ -σ' * |u| + -δ * |v| := by
      have hσ'_pos : 0 < σ' := by dsimp only [σ']; linarith
      have hmul1 : σ' * |u| ≤ σ' * (|v| + |u - v|) := mul_le_mul_of_nonneg_left htri hσ'_pos.le
      have hmul2 : 0 ≤ δ * |u - v| := mul_nonneg hδ.le (abs_nonneg _)
      rw [hσ_eq]; linarith
    rw [norm_mul]
    calc ‖F v‖ * ‖G (u - v)‖
        ≤ (Cf * Real.exp (-σ * |v|)) * (Cg * Real.exp (-σ * |u - v|)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = Cf * Cg * Real.exp (-σ * |v| + -σ * |u - v|) := by rw [Real.exp_add]; ring
      _ ≤ Cf * Cg * Real.exp (-σ' * |u| + -δ * |v|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (mul_nonneg hCf hCg)
      _ = (Cf * Cg * Real.exp (-σ' * |u|)) * Real.exp (-δ * |v|) := by rw [Real.exp_add]; ring
  have hint_dom : Integrable (fun v : ℝ => (Cf * Cg * Real.exp (-σ' * |u|)) * Real.exp (-δ * |v|)) :=
    (integrable_exp_neg_abs_real hδ).const_mul _
  by_cases hint : Integrable (fun v : ℝ => F v * G (u - v))
  · calc ‖∫ v : ℝ, F v * G (u - v)‖
        ≤ ∫ v : ℝ, ‖F v * G (u - v)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ v : ℝ, (Cf * Cg * Real.exp (-σ' * |u|)) * Real.exp (-δ * |v|) :=
          integral_mono hint.norm hint_dom hpt
      _ = (Cf * Cg * Real.exp (-σ' * |u|)) * (2 / δ) := by
          rw [integral_const_mul, integral_exp_neg_abs_real hδ]
      _ = (Cf * Cg * (2 / δ)) * Real.exp (-σ' * |u|) := by ring
  · rw [integral_undef hint, norm_zero]
    positivity

/-- Differentiation under the integral sign for additive convolution `u ↦ ∫ v, F v * G (u - v)`. -/
private lemma hasDerivAt_conv_integral {F G G' : ℝ → ℂ} {σf Cf Cg : ℝ}
    (hF_cont : Continuous F) (hG_cont : Continuous G) (hG'_cont : Continuous G')
    (hG_deriv : ∀ w : ℝ, HasDerivAt G (G' w) w)
    (hCf : 0 ≤ Cf) (hσf : 0 < σf)
    (hF_bd : ∀ v : ℝ, ‖F v‖ ≤ Cf * Real.exp (-σf * |v|))
    (hG_bd : ∀ w : ℝ, ‖G w‖ ≤ Cg)
    (hG'_bd : ∀ w : ℝ, ‖G' w‖ ≤ Cg)
    (u : ℝ) :
    HasDerivAt (fun x : ℝ => ∫ v : ℝ, F v * G (x - v)) (∫ v : ℝ, F v * G' (u - v)) u := by
  let bound : ℝ → ℝ := fun v => (Cf * Cg) * Real.exp (-σf * |v|)
  have hbound_int : Integrable bound := (integrable_exp_neg_abs_real hσf).const_mul (Cf * Cg)
  have hmeas : ∀ᶠ x in 𝓝 u, AEStronglyMeasurable (fun v : ℝ => F v * G (x - v)) volume :=
    Eventually.of_forall fun x =>
      (hF_cont.mul (hG_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hint_u : Integrable (fun v : ℝ => F v * G (u - v)) volume := by
    refine hbound_int.mono'
      (hF_cont.mul (hG_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    calc ‖F v‖ * ‖G (u - v)‖ ≤ (Cf * Real.exp (-σf * |v|)) * Cg :=
          mul_le_mul (hF_bd v) (hG_bd (u - v)) (norm_nonneg _) (by positivity)
      _ = bound v := by dsimp only [bound]; ring
  have hmeas' : AEStronglyMeasurable (fun v : ℝ => F v * G' (u - v)) volume :=
    (hF_cont.mul (hG'_cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  have hdom : ∀ᵐ v ∂volume, ∀ x ∈ Metric.ball u 1, ‖F v * G' (x - v)‖ ≤ bound v :=
    Eventually.of_forall fun v x _ => by
      rw [norm_mul]
      calc ‖F v‖ * ‖G' (x - v)‖ ≤ (Cf * Real.exp (-σf * |v|)) * Cg :=
            mul_le_mul (hF_bd v) (hG'_bd (x - v)) (norm_nonneg _) (by positivity)
        _ = bound v := by dsimp only [bound]; ring
  have hderiv : ∀ᵐ v ∂volume, ∀ x ∈ Metric.ball u 1,
      HasDerivAt (fun t : ℝ => F v * G (t - v)) (F v * G' (x - v)) x :=
    Eventually.of_forall fun v x _ => by
      have hsub : HasDerivAt (fun t : ℝ => t - v) 1 x := (hasDerivAt_id x).sub_const v
      have hcomp : HasDerivAt (fun t : ℝ => G (t - v)) (G' (x - v)) x := by
        simpa [Function.comp_def] using HasDerivAt.scomp x (hG_deriv (x - v)) hsub
      exact hcomp.const_mul (F v)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds u one_pos)
    hmeas hint_u hmeas' hdom hbound_int hderiv).2

/-- Additive Weil convolution `f * g` on `AdmissibleWeilTest`. -/
def weilTestConv (f g : AdmissibleWeilTest) : AdmissibleWeilTest where
  toFun := Stage4ExplicitFormula.weilConv f.toFun g.toFun
  deriv1 := fun u => ∫ v : ℝ, f.toFun v * g.deriv1 (u - v)
  deriv2 := fun u => ∫ v : ℝ, f.toFun v * g.deriv2 (u - v)
  hasDeriv1 := fun u =>
    hasDerivAt_conv_integral f.continuous g.continuous g.continuous_deriv1 g.hasDeriv1
      f.boundConst_nonneg (zero_lt_one.trans f.decayRate_gt) f.bound0
      (fun w => (g.bound0 w).trans (mul_le_of_le_one_right g.boundConst_nonneg
        (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg w]))))
      (fun w => (g.bound1 w).trans (mul_le_of_le_one_right g.boundConst_nonneg
        (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg w])))) u
  hasDeriv2 := fun u =>
    hasDerivAt_conv_integral f.continuous g.continuous_deriv1 g.cont2 g.hasDeriv2
      f.boundConst_nonneg (zero_lt_one.trans f.decayRate_gt) f.bound0
      (fun w => (g.bound1 w).trans (mul_le_of_le_one_right g.boundConst_nonneg
        (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg w]))))
      (fun w => (g.bound2 w).trans (mul_le_of_le_one_right g.boundConst_nonneg
        (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg w])))) u
  cont2 := by
    have hCf := f.boundConst_nonneg
    refine continuous_of_dominated (bound := fun v : ℝ =>
        (f.boundConst * g.boundConst) * Real.exp (-f.decayRate * |v|)) ?_ ?_
      ((integrable_exp_neg_abs_real (zero_lt_one.trans f.decayRate_gt)).const_mul _) ?_
    · intro u
      exact (f.continuous.mul (g.cont2.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · intro u
      refine Eventually.of_forall fun v => ?_
      rw [norm_mul]
      have hg2 : ‖g.deriv2 (u - v)‖ ≤ g.boundConst :=
        (g.bound2 (u - v)).trans (mul_le_of_le_one_right g.boundConst_nonneg
          (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg (u - v)])))
      calc ‖f.toFun v‖ * ‖g.deriv2 (u - v)‖
          ≤ (f.boundConst * Real.exp (-f.decayRate * |v|)) * g.boundConst :=
            mul_le_mul (f.bound0 v) hg2 (norm_nonneg _) (by positivity)
        _ = (f.boundConst * g.boundConst) * Real.exp (-f.decayRate * |v|) := by ring
    · refine Eventually.of_forall fun v => ?_
      exact continuous_const.mul (g.cont2.comp (continuous_id.sub continuous_const))
  decayRate := (1 + min f.decayRate g.decayRate) / 2
  decayRate_gt := by linarith [lt_min f.decayRate_gt g.decayRate_gt]
  boundConst := f.boundConst * g.boundConst * (2 / ((min f.decayRate g.decayRate - 1) / 2))
  boundConst_nonneg := by
    have h1 : 0 < (min f.decayRate g.decayRate - 1) / 2 := by linarith [lt_min f.decayRate_gt g.decayRate_gt]
    exact mul_nonneg (mul_nonneg f.boundConst_nonneg g.boundConst_nonneg) (div_nonneg (by norm_num) h1.le)
  bound0 := fun u => norm_integral_conv_le f.boundConst_nonneg g.boundConst_nonneg
    f.decayRate_gt g.decayRate_gt f.bound0 g.bound0 u
  bound1 := fun u => norm_integral_conv_le f.boundConst_nonneg g.boundConst_nonneg
    f.decayRate_gt g.decayRate_gt f.bound0 g.bound1 u
  bound2 := fun u => norm_integral_conv_le f.boundConst_nonneg g.boundConst_nonneg
    f.decayRate_gt g.decayRate_gt f.bound0 g.bound2 u

/-- Self-convolution `f * f̃` on `AdmissibleWeilTest`. -/
def weilSelfConv (f : AdmissibleWeilTest) : AdmissibleWeilTest :=
  weilTestConv f (weilTestInvolution f)

lemma weilSelfConv_toFun (f : AdmissibleWeilTest) :
    (weilSelfConv f).toFun = Stage4ExplicitFormula.weilConv f.toFun (Stage4ExplicitFormula.weilInvolution f.toFun) :=
  rfl

/-- Elementary Gaussian domination bound: `|u|^k * exp(-a u²) ≤ exp((k + 2)² / (4 a)) * exp(-2 |u|)`
for `a > 0` and `k ∈ ℕ`. -/
private lemma abs_pow_mul_exp_neg_sq_le {a : ℝ} (ha : 0 < a) (k : ℕ) (u : ℝ) :
    |u| ^ k * Real.exp (-a * u ^ 2) ≤
      Real.exp (((k : ℝ) + 2) ^ 2 / (4 * a)) * Real.exp (-2 * |u|) := by
  have hpow : |u| ^ k ≤ Real.exp ((k : ℝ) * |u|) := by
    calc |u| ^ k ≤ (Real.exp |u|) ^ k :=
          pow_le_pow_left₀ (abs_nonneg u) (by linarith [Real.add_one_le_exp |u|]) k
      _ = Real.exp ((k : ℝ) * |u|) := (Real.exp_nat_mul |u| k).symm
  calc |u| ^ k * Real.exp (-a * u ^ 2)
      ≤ Real.exp ((k : ℝ) * |u|) * Real.exp (-a * u ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
    _ = Real.exp ((k : ℝ) * |u| + -a * u ^ 2) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (((k : ℝ) + 2) ^ 2 / (4 * a) + -2 * |u|) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : 0 ≤ a * (|u| - ((k : ℝ) + 2) / (2 * a)) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
        have hexp : a * (|u| - ((k : ℝ) + 2) / (2 * a)) ^ 2 =
            a * u ^ 2 - ((k : ℝ) + 2) * |u| + ((k : ℝ) + 2) ^ 2 / (4 * a) := by
          rw [← sq_abs u]; field_simp [ha.ne']; ring
        linarith
    _ = Real.exp (((k : ℝ) + 2) ^ 2 / (4 * a)) * Real.exp (-2 * |u|) := Real.exp_add _ _

private lemma abs_pow_mul_exp_neg_sq_le_25 {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : k ≤ 3) (u : ℝ) :
    |u| ^ k * Real.exp (-a * u ^ 2) ≤ Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|) := by
  refine (abs_pow_mul_exp_neg_sq_le ha k u).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right ?_ (by positivity))) (Real.exp_nonneg _))
  have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

/-- Every odd-modulated Gaussian `weilOddGaussian a γ u = u * exp(-a u² - i γ u)` (`a > 0`)
is an `AdmissibleWeilTest` (with `decayRate = 2`). -/
def admissibleOddGaussian (a : ℝ) (ha : 0 < a) (γ : ℝ) : AdmissibleWeilTest where
  toFun := Stage4ExplicitFormula.weilOddGaussian a γ
  deriv1 := fun u =>
    ((1 : ℂ) - (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ))) *
      Stage4ExplicitFormula.weilGaussian a γ u
  deriv2 := fun u =>
    ((-6 * (a : ℂ) * (u : ℂ) - 2 * I * (γ : ℂ)) +
     (2 * (a : ℂ) * (u : ℂ) + I * (γ : ℂ)) *
       (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ))) *
      Stage4ExplicitFormula.weilGaussian a γ u
  hasDeriv1 := fun u => by
    have hu : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (u : ℂ)) u := by
      simpa using hu.fun_pow 2
    have hexp_arg : HasDerivAt (fun t : ℝ => -(a : ℂ) * (t : ℂ) ^ 2 - I * (γ : ℂ) * (t : ℂ))
        (-2 * (a : ℂ) * (u : ℂ) - I * (γ : ℂ)) u := by
      have h1 := hsq.const_mul (-(a : ℂ))
      have h2 := hu.const_mul (I * (γ : ℂ))
      exact (h1.sub h2).congr_deriv (by ring)
    have hG : HasDerivAt (Stage4ExplicitFormula.weilGaussian a γ)
        (Stage4ExplicitFormula.weilGaussian a γ u * (-2 * (a : ℂ) * (u : ℂ) - I * (γ : ℂ))) u :=
      hexp_arg.cexp
    exact (hu.mul hG).congr_deriv (by ring)
  hasDeriv2 := fun u => by
    have hu : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have hsq : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2) (2 * (u : ℂ)) u := by
      simpa using hu.fun_pow 2
    have hexp_arg : HasDerivAt (fun t : ℝ => -(a : ℂ) * (t : ℂ) ^ 2 - I * (γ : ℂ) * (t : ℂ))
        (-2 * (a : ℂ) * (u : ℂ) - I * (γ : ℂ)) u := by
      have h1 := hsq.const_mul (-(a : ℂ))
      have h2 := hu.const_mul (I * (γ : ℂ))
      exact (h1.sub h2).congr_deriv (by ring)
    have hG : HasDerivAt (Stage4ExplicitFormula.weilGaussian a γ)
        (Stage4ExplicitFormula.weilGaussian a γ u * (-2 * (a : ℂ) * (u : ℂ) - I * (γ : ℂ))) u :=
      hexp_arg.cexp
    have hP : HasDerivAt
        (fun t : ℝ => (1 : ℂ) - (2 * (a : ℂ) * (t : ℂ) ^ 2 + I * (γ : ℂ) * (t : ℂ)))
        (-(4 * (a : ℂ) * (u : ℂ) + I * (γ : ℂ))) u := by
      have h1 := hsq.const_mul (2 * (a : ℂ))
      have h2 := hu.const_mul (I * (γ : ℂ))
      exact ((hasDerivAt_const u (1 : ℂ)).sub (h1.add h2)).congr_deriv (by ring)
    exact (hP.mul hG).congr_deriv (by ring)
  cont2 := by
    unfold Stage4ExplicitFormula.weilGaussian; fun_prop
  decayRate := 2
  decayRate_gt := by norm_num
  boundConst := (1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2) *
    Real.exp (25 / (4 * a))
  boundConst_nonneg := by positivity
  bound0 := fun u => by
    have hG : ‖Stage4ExplicitFormula.weilGaussian a γ u‖ = Real.exp (-a * u ^ 2) := by
      unfold Stage4ExplicitFormula.weilGaussian
      rw [Complex.norm_exp]; congr 1; simp [sq]
    have h1 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 1 ≤ 3) u
    simp only [pow_one] at h1
    have hcoeff : (1 : ℝ) ≤ 1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2 := by
      have : 0 ≤ a * |γ| := mul_nonneg ha.le (abs_nonneg γ)
      nlinarith [sq_nonneg a, sq_nonneg |γ|, abs_nonneg γ]
    unfold Stage4ExplicitFormula.weilOddGaussian
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hG, mul_assoc]
    exact h1.trans (le_mul_of_one_le_left (by positivity) hcoeff)
  bound1 := fun u => by
    have hG : ‖Stage4ExplicitFormula.weilGaussian a γ u‖ = Real.exp (-a * u ^ 2) := by
      unfold Stage4ExplicitFormula.weilGaussian
      rw [Complex.norm_exp]; congr 1; simp [sq]
    have hb0 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 0 ≤ 3) u
    have hb1 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 1 ≤ 3) u
    have hb2 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 2 ≤ 3) u
    simp only [pow_zero, one_mul, pow_one] at hb0 hb1
    have hP : ‖(1 : ℂ) - (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ))‖ ≤
        1 + 2 * a * |u| ^ 2 + |γ| * |u| := by
      have h1 := norm_sub_le (1 : ℂ) (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ))
      have h2 := norm_add_le (2 * (a : ℂ) * (u : ℂ) ^ 2) (I * (γ : ℂ) * (u : ℂ))
      simp only [norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        norm_pow, Complex.norm_I, one_mul, abs_of_pos ha] at h1 h2
      linarith
    have hcoeff : 1 + 2 * a + |γ| ≤ 1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2 := by
      have : 0 ≤ a * |γ| := mul_nonneg ha.le (abs_nonneg γ)
      nlinarith [sq_nonneg a, sq_nonneg |γ|, abs_nonneg γ]
    rw [norm_mul, hG]
    calc ‖(1 : ℂ) - (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ))‖ * Real.exp (-a * u ^ 2)
        ≤ (1 + 2 * a * |u| ^ 2 + |γ| * |u|) * Real.exp (-a * u ^ 2) :=
          mul_le_mul_of_nonneg_right hP (Real.exp_nonneg _)
      _ = Real.exp (-a * u ^ 2) + 2 * a * (|u| ^ 2 * Real.exp (-a * u ^ 2)) +
            |γ| * (|u| * Real.exp (-a * u ^ 2)) := by ring
      _ ≤ (1 + 2 * a + |γ|) * (Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|)) := by
          have m1 := mul_le_mul_of_nonneg_left hb2 (by positivity : 0 ≤ 2 * a)
          have m2 := mul_le_mul_of_nonneg_left hb1 (abs_nonneg γ)
          linarith
      _ ≤ (1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2) *
            (Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|)) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2) *
            Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|) := by ring
  bound2 := fun u => by
    have hG : ‖Stage4ExplicitFormula.weilGaussian a γ u‖ = Real.exp (-a * u ^ 2) := by
      unfold Stage4ExplicitFormula.weilGaussian
      rw [Complex.norm_exp]; congr 1; simp [sq]
    have hb0 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 0 ≤ 3) u
    have hb1 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 1 ≤ 3) u
    have hb2 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 2 ≤ 3) u
    have hb3 := abs_pow_mul_exp_neg_sq_le_25 ha (by norm_num : 3 ≤ 3) u
    simp only [pow_zero, one_mul, pow_one] at hb0 hb1
    have hP : ‖(-6 * (a : ℂ) * (u : ℂ) - 2 * I * (γ : ℂ)) +
        (2 * (a : ℂ) * (u : ℂ) + I * (γ : ℂ)) *
          (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ))‖ ≤
        6 * a * |u| + 2 * |γ| + 4 * a ^ 2 * |u| ^ 3 + 4 * a * |γ| * |u| ^ 2 + |γ| ^ 2 * |u| := by
      have h1 := norm_add_le (-6 * (a : ℂ) * (u : ℂ) - 2 * I * (γ : ℂ))
        ((2 * (a : ℂ) * (u : ℂ) + I * (γ : ℂ)) * (2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ)))
      have h2 := norm_sub_le (-6 * (a : ℂ) * (u : ℂ)) (2 * I * (γ : ℂ))
      have h3 := norm_add_le (2 * (a : ℂ) * (u : ℂ)) (I * (γ : ℂ))
      have h4 := norm_add_le (2 * (a : ℂ) * (u : ℂ) ^ 2) (I * (γ : ℂ) * (u : ℂ))
      rw [norm_mul] at h1
      simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        norm_pow, Complex.norm_I, one_mul, mul_one, abs_of_pos ha] at h2 h3 h4
      have hmul : ‖2 * (a : ℂ) * (u : ℂ) + I * (γ : ℂ)‖ *
          ‖2 * (a : ℂ) * (u : ℂ) ^ 2 + I * (γ : ℂ) * (u : ℂ)‖ ≤
          (2 * a * |u| + |γ|) * (2 * a * |u| ^ 2 + |γ| * |u|) :=
        mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      nlinarith
    have hcoeff : 6 * a + 2 * |γ| + 4 * a ^ 2 + 4 * a * |γ| + |γ| ^ 2 ≤
        1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2 := by linarith
    rw [norm_mul, hG]
    calc _ ≤ (6 * a * |u| + 2 * |γ| + 4 * a ^ 2 * |u| ^ 3 + 4 * a * |γ| * |u| ^ 2 + |γ| ^ 2 * |u|) *
            Real.exp (-a * u ^ 2) := mul_le_mul_of_nonneg_right hP (Real.exp_nonneg _)
      _ = 6 * a * (|u| * Real.exp (-a * u ^ 2)) + 2 * |γ| * Real.exp (-a * u ^ 2) +
          4 * a ^ 2 * (|u| ^ 3 * Real.exp (-a * u ^ 2)) +
          4 * a * |γ| * (|u| ^ 2 * Real.exp (-a * u ^ 2)) +
          |γ| ^ 2 * (|u| * Real.exp (-a * u ^ 2)) := by ring
      _ ≤ (6 * a + 2 * |γ| + 4 * a ^ 2 + 4 * a * |γ| + |γ| ^ 2) *
            (Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|)) := by
          have m1 := mul_le_mul_of_nonneg_left hb1 (by positivity : 0 ≤ 6 * a)
          have m2 := mul_le_mul_of_nonneg_left hb0 (by positivity : 0 ≤ 2 * |γ|)
          have m3 := mul_le_mul_of_nonneg_left hb3 (by positivity : 0 ≤ 4 * a ^ 2)
          have m4 := mul_le_mul_of_nonneg_left hb2 (by positivity : 0 ≤ 4 * a * |γ|)
          have m5 := mul_le_mul_of_nonneg_left hb1 (sq_nonneg |γ|)
          linarith
      _ ≤ (1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2) *
            (Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|)) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (1 + 6 * a + 4 * a ^ 2 + 2 * |γ| + 4 * a * |γ| + |γ| ^ 2) *
            Real.exp (25 / (4 * a)) * Real.exp (-2 * |u|) := by ring

private lemma exists_exp_bound_of_compactSupport {g : ℝ → ℂ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, ‖g u‖ ≤ M * Real.exp (-2 * |u|) := by
  have hcont : Continuous (fun u : ℝ => ‖g u‖ * Real.exp (2 * |u|)) :=
    hg.norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
  have hcs : HasCompactSupport (fun u : ℝ => ‖g u‖ * Real.exp (2 * |u|)) :=
    (hgs.comp_left norm_zero).mul_right
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hcont
  refine ⟨max 0 M, le_max_left _ _, fun u => ?_⟩
  have hle : ‖g u‖ * Real.exp (2 * |u|) ≤ max 0 M := by
    have h1u := hM u
    rw [Real.norm_of_nonneg (by positivity)] at h1u
    exact h1u.trans (le_max_right _ _)
  have hexp : Real.exp (-2 * |u|) = (Real.exp (2 * |u|))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hexp, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  exact hle

/-- Every compactly supported `C²` test function `f : ℝ → ℂ` is an `AdmissibleWeilTest`
(with `toFun = f` definitionally and exponential decay rate `2 > 1`). -/
def admissibleOfCompactSupport (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f) :
    AdmissibleWeilTest where
  toFun := f
  deriv1 := deriv f
  deriv2 := deriv (deriv f)
  hasDeriv1 := fun u => (((contDiff_succ_iff_deriv (n := 1)).mp hf).1 u).hasDerivAt
  hasDeriv2 := fun u =>
    (((contDiff_succ_iff_deriv (n := 0)).mp
      ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).1 u).hasDerivAt
  cont2 :=
    ((contDiff_succ_iff_deriv (n := 0)).mp
      ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).2.2.continuous
  decayRate := 2
  decayRate_gt := by norm_num
  boundConst :=
    max (Classical.choose (exists_exp_bound_of_compactSupport
          ((contDiff_succ_iff_deriv (n := 1)).mp hf).1.continuous hsupp))
      (max (Classical.choose (exists_exp_bound_of_compactSupport
            ((contDiff_succ_iff_deriv (n := 0)).mp
              ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).1.continuous hsupp.deriv))
        (Classical.choose (exists_exp_bound_of_compactSupport
          ((contDiff_succ_iff_deriv (n := 0)).mp
            ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).2.2.continuous hsupp.deriv.deriv)))
  boundConst_nonneg :=
    le_trans
      (Classical.choose_spec (exists_exp_bound_of_compactSupport
        ((contDiff_succ_iff_deriv (n := 1)).mp hf).1.continuous hsupp)).1
      (le_max_left _ _)
  bound0 := fun u =>
    ((Classical.choose_spec (exists_exp_bound_of_compactSupport
      ((contDiff_succ_iff_deriv (n := 1)).mp hf).1.continuous hsupp)).2 u).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  bound1 := fun u =>
    ((Classical.choose_spec (exists_exp_bound_of_compactSupport
      ((contDiff_succ_iff_deriv (n := 0)).mp
        ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).1.continuous hsupp.deriv)).2 u).trans
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) (Real.exp_nonneg _))
  bound2 := fun u =>
    ((Classical.choose_spec (exists_exp_bound_of_compactSupport
      ((contDiff_succ_iff_deriv (n := 0)).mp
        ((contDiff_succ_iff_deriv (n := 1)).mp hf).2.2).2.2.continuous hsupp.deriv.deriv)).2 u).trans
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) (Real.exp_nonneg _))

@[simp] lemma admissibleOfCompactSupport_toFun (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hsupp : HasCompactSupport f) :
    (admissibleOfCompactSupport f hf hsupp).toFun = f := rfl

/-! ## Section 2: Holomorphicity & Quadratic Vertical Decay of `weilPhi`, and `ZetaNontrivialZero` -/

lemma weilPhi_one_sub (f : AdmissibleWeilTest) (s : ℂ) :
    weilPhi f (1 - s) = weilPhi (weilTestReflect f) s := by
  unfold weilPhi Stage4ExplicitFormula.weilBilateralTransform weilTestReflect
  dsimp only
  rw [← MeasureTheory.integral_neg_eq_self _ volume]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  congr 2; push_cast; ring

/-- Holomorphicity of `weilPhi f` on the open strip `|Re(s) - 1/2| < f.decayRate`
(which contains the closed strip `-1/2 ≤ Re(s) ≤ 3/2`). -/
theorem differentiableOn_weilPhi (f : AdmissibleWeilTest) :
    DifferentiableOn ℂ (weilPhi f) {s : ℂ | |s.re - 1 / 2| < f.decayRate} := by
  intro s₀ hs₀
  set ε : ℝ := (f.decayRate - |s₀.re - 1 / 2|) / 2
  have hε : 0 < ε := by change |s₀.re - 1 / 2| < f.decayRate at hs₀; dsimp only [ε]; linarith
  have hC : 0 ≤ f.boundConst := f.boundConst_nonneg
  let bound : ℝ → ℝ := fun u => (f.boundConst * (2 / ε)) * Real.exp (-(ε / 2) * |u|)
  have hbound_int : Integrable bound := (integrable_exp_neg_abs_real (by positivity)).const_mul _
  have hmeas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
      (fun u : ℝ => f.toFun u * cexp ((s - 1 / 2) * (u : ℂ))) volume :=
    Eventually.of_forall fun s =>
      (f.continuous.mul (by fun_prop)).aestronglyMeasurable
  have hint₀ : Integrable (fun u : ℝ => f.toFun u * cexp ((s₀ - 1 / 2) * (u : ℂ))) volume :=
    Stage4ExplicitFormula.integrable_weilBilateralTransform f.weilAdmissible hs₀
  have hmeas' : AEStronglyMeasurable
      (fun u : ℝ => f.toFun u * ((u : ℂ) * cexp ((s₀ - 1 / 2) * (u : ℂ)))) volume :=
    (f.continuous.mul (by fun_prop)).aestronglyMeasurable
  have hdom : ∀ᵐ u ∂volume, ∀ s ∈ Metric.ball s₀ ε,
      ‖f.toFun u * ((u : ℂ) * cexp ((s - 1 / 2) * (u : ℂ)))‖ ≤ bound u :=
    Eventually.of_forall fun u s hs => by
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have hdist : |s.re - s₀.re| ≤ ε := by
        simpa using (Complex.abs_re_le_norm (s - s₀)).trans hs.le
      have hs_re : |s.re - 1 / 2| ≤ f.decayRate - ε := by
        have htri : |s.re - 1 / 2| ≤ |s.re - s₀.re| + |s₀.re - 1 / 2| := by
          have := abs_add_le (s.re - s₀.re) (s₀.re - 1 / 2); simpa [sub_add_sub_cancel] using this
        dsimp only [ε] at hdist ⊢; linarith
      have hu_exp : |u| ≤ (2 / ε) * Real.exp ((ε / 2) * |u|) := by
        have h1 : (ε / 2) * |u| ≤ Real.exp ((ε / 2) * |u|) := by
          linarith [Real.add_one_le_exp ((ε / 2) * |u|)]
        have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 / ε by positivity)
        have h3 : (2 / ε) * ((ε / 2) * |u|) = |u| := by field_simp [hε.ne']
        linarith
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hre : ((s - 1 / 2) * (u : ℂ)).re = (s.re - 1 / 2) * u := by simp
      rw [hre]
      have hmul_le : (s.re - 1 / 2) * u ≤ (f.decayRate - ε) * |u| := by
        calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
          _ = |s.re - 1 / 2| * |u| := abs_mul _ _
          _ ≤ (f.decayRate - ε) * |u| := mul_le_mul_of_nonneg_right hs_re (abs_nonneg u)
      calc ‖f.toFun u‖ * (|u| * Real.exp ((s.re - 1 / 2) * u))
          ≤ (f.boundConst * Real.exp (-f.decayRate * |u|)) *
              (((2 / ε) * Real.exp ((ε / 2) * |u|)) * Real.exp ((f.decayRate - ε) * |u|)) :=
            mul_le_mul (f.bound0 u) (mul_le_mul hu_exp (Real.exp_le_exp.mpr hmul_le)
              (Real.exp_nonneg _) (by positivity)) (by positivity) (by positivity)
        _ = (f.boundConst * (2 / ε)) *
              (Real.exp (-f.decayRate * |u|) * Real.exp ((ε / 2) * |u|) *
               Real.exp ((f.decayRate - ε) * |u|)) := by ring
        _ = bound u := by
            rw [← Real.exp_add, ← Real.exp_add]; dsimp only [bound]; congr 2; ring
  have hderiv : ∀ᵐ u ∂volume, ∀ s ∈ Metric.ball s₀ ε,
      HasDerivAt (fun z : ℂ => f.toFun u * cexp ((z - 1 / 2) * (u : ℂ)))
        (f.toFun u * ((u : ℂ) * cexp ((s - 1 / 2) * (u : ℂ)))) s :=
    Eventually.of_forall fun u s _ => by
      have hlin : HasDerivAt (fun z : ℂ => (z - 1 / 2) * (u : ℂ)) (u : ℂ) s := by
        simpa using ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (u : ℂ)
      exact (hlin.cexp.const_mul (f.toFun u)).congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ hε)
    hmeas hint₀ hmeas' hdom hbound_int hderiv).2.differentiableAt.differentiableWithinAt

/-- Integration-by-parts step for bilateral Laplace transforms. -/
private lemma bilateral_ibp {g g' : ℝ → ℂ} {σ₀ C : ℝ} {w : ℂ}
    (hg_deriv : ∀ u : ℝ, HasDerivAt g (g' u) u)
    (hg'_cont : Continuous g')
    (hC : 0 ≤ C) (hw : |w.re| < σ₀)
    (hg_bd : ∀ u : ℝ, ‖g u‖ ≤ C * Real.exp (-σ₀ * |u|))
    (hg'_bd : ∀ u : ℝ, ‖g' u‖ ≤ C * Real.exp (-σ₀ * |u|)) :
    w * (∫ u : ℝ, g u * cexp (w * (u : ℂ))) = -(∫ u : ℝ, g' u * cexp (w * (u : ℂ))) := by
  set δ : ℝ := σ₀ - |w.re|
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hdom_fn : ∀ (h : ℝ → ℂ), Continuous h → (∀ u, ‖h u‖ ≤ C * Real.exp (-σ₀ * |u|)) →
      Integrable (fun u : ℝ => h u * cexp (w * (u : ℂ))) := fun h hc hbd => by
    refine ((integrable_exp_neg_abs_real hδ).const_mul C).mono'
      (hc.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_exp]
    have hre : (w * (u : ℂ)).re = w.re * u := by simp
    rw [hre]
    have hle : w.re * u ≤ |w.re| * |u| := (le_abs_self _).trans_eq (abs_mul _ _)
    calc ‖h u‖ * Real.exp (w.re * u)
        ≤ (C * Real.exp (-σ₀ * |u|)) * Real.exp (|w.re| * |u|) :=
          mul_le_mul (hbd u) (Real.exp_le_exp.mpr hle) (Real.exp_nonneg _) (by positivity)
      _ = C * Real.exp (-δ * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp only [δ]; ring
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg_deriv u).continuousAt
  have hi_g := hdom_fn g hg_cont hg_bd
  have hi_g' := hdom_fn g' hg'_cont hg'_bd
  let G : ℝ → ℂ := fun u => g u * cexp (w * (u : ℂ))
  let G' : ℝ → ℂ := fun u => g' u * cexp (w * (u : ℂ)) + w * (g u * cexp (w * (u : ℂ)))
  have hG_deriv : ∀ u : ℝ, HasDerivAt G (G' u) u := fun u => by
    have he : HasDerivAt (fun t : ℝ => cexp (w * (t : ℂ))) (cexp (w * (u : ℂ)) * w) u := by
      have h1 : HasDerivAt (fun t : ℝ => w * (t : ℂ)) w u := by
        simpa using Complex.ofRealCLM.hasDerivAt.const_mul w
      exact h1.cexp
    exact ((hg_deriv u).mul he).congr_deriv (by dsimp only [G']; ring)
  have hG_norm : ∀ u : ℝ, ‖G u‖ ≤ C * Real.exp (-δ * |u|) := fun u => by
    dsimp only [G]; rw [norm_mul, Complex.norm_exp]
    have hre : (w * (u : ℂ)).re = w.re * u := by simp
    rw [hre]
    have hle : w.re * u ≤ |w.re| * |u| := (le_abs_self _).trans_eq (abs_mul _ _)
    calc ‖g u‖ * Real.exp (w.re * u)
        ≤ (C * Real.exp (-σ₀ * |u|)) * Real.exp (|w.re| * |u|) :=
          mul_le_mul (hg_bd u) (Real.exp_le_exp.mpr hle) (Real.exp_nonneg _) (by positivity)
      _ = C * Real.exp (-δ * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp only [δ]; ring
  have hG_top : Tendsto G atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun u => hG_norm u) ?_
    have h1 : Tendsto (fun u : ℝ => -δ * |u|) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_abs_atTop_atTop
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  have hG_bot : Tendsto G atBot (𝓝 0) := by
    refine squeeze_zero_norm (fun u => hG_norm u) ?_
    have h1 : Tendsto (fun u : ℝ => -δ * |u|) atBot atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_abs_atBot_atTop
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  have hG'_int : Integrable G' := hi_g'.add (hi_g.const_mul w)
  have h1 := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun u _ => hG_deriv u) hG'_int.integrableOn hG_top
  have h2 := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun u _ => hG_deriv u) hG'_int.integrableOn hG_bot
  have hsplit : (∫ u in Set.Iic (0 : ℝ), G' u) + (∫ u in Set.Ioi (0 : ℝ), G' u) = ∫ u : ℝ, G' u := by
    rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      hG'_int.integrableOn hG'_int.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
  have hzero : ∫ u : ℝ, G' u = 0 := by rw [← hsplit, h1, h2]; ring
  have hadd : ∫ u : ℝ, G' u =
      (∫ u : ℝ, g' u * cexp (w * (u : ℂ))) + w * ∫ u : ℝ, g u * cexp (w * (u : ℂ)) := by
    dsimp only [G']
    rw [integral_add hi_g' (hi_g.const_mul w), integral_const_mul]
  linear_combination hzero - hadd

/-- **Uniform Quadratic Vertical Decay Bound on `weilPhi f`**:
there exists `M ≥ 0` such that for ALL `s : ℂ` in the closed vertical strip `-1/2 ≤ s.re ≤ 3/2`,
`‖weilPhi f s‖ ≤ M / (1 + s.im ^ 2)`. -/
theorem norm_weilPhi_strip_le (f : AdmissibleWeilTest) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
      ‖weilPhi f s‖ ≤ M / (1 + s.im ^ 2) := by
  set δ : ℝ := f.decayRate - 1
  have hδ : 0 < δ := by dsimp only [δ]; linarith [f.decayRate_gt]
  have hC : 0 ≤ f.boundConst := f.boundConst_nonneg
  set M₀ : ℝ := f.boundConst * (2 / δ)
  have hM₀ : 0 ≤ M₀ := mul_nonneg hC (by positivity)
  refine ⟨2 * M₀, by positivity, fun s hlo hhi => ?_⟩
  set w : ℂ := s - 1 / 2
  have hw_re : |w.re| ≤ 1 := by
    rw [abs_le]; constructor <;> simp [w] <;> linarith
  have hw_lt : |w.re| < f.decayRate := hw_re.trans_lt f.decayRate_gt
  have hbd_int : ∀ (h : ℝ → ℂ), Continuous h → (∀ u, ‖h u‖ ≤ f.boundConst * Real.exp (-f.decayRate * |u|)) →
      ‖∫ u : ℝ, h u * cexp (w * (u : ℂ))‖ ≤ M₀ := fun h hc hbd => by
    have hpt : ∀ u : ℝ, ‖h u * cexp (w * (u : ℂ))‖ ≤ f.boundConst * Real.exp (-δ * |u|) := fun u => by
      rw [norm_mul, Complex.norm_exp]
      have hre : (w * (u : ℂ)).re = w.re * u := by simp
      rw [hre]
      have hle : w.re * u ≤ 1 * |u| := by
        calc w.re * u ≤ |w.re * u| := le_abs_self _
          _ = |w.re| * |u| := abs_mul _ _
          _ ≤ 1 * |u| := mul_le_mul_of_nonneg_right hw_re (abs_nonneg u)
      calc ‖h u‖ * Real.exp (w.re * u)
          ≤ (f.boundConst * Real.exp (-f.decayRate * |u|)) * Real.exp (1 * |u|) :=
            mul_le_mul (hbd u) (Real.exp_le_exp.mpr hle) (Real.exp_nonneg _) (by positivity)
        _ = f.boundConst * Real.exp (-δ * |u|) := by
            rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp only [δ]; ring
    have hdom := (integrable_exp_neg_abs_real hδ).const_mul f.boundConst
    have hint : Integrable (fun u : ℝ => h u * cexp (w * (u : ℂ))) :=
      hdom.mono' (hc.mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall hpt)
    calc ‖∫ u : ℝ, h u * cexp (w * (u : ℂ))‖
        ≤ ∫ u : ℝ, ‖h u * cexp (w * (u : ℂ))‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ, f.boundConst * Real.exp (-δ * |u|) := integral_mono hint.norm hdom hpt
      _ = M₀ := by rw [integral_const_mul, integral_exp_neg_abs_real hδ]
  have h0 : ‖weilPhi f s‖ ≤ M₀ := hbd_int f.toFun f.continuous f.bound0
  have hibp1 := bilateral_ibp f.hasDeriv1 f.continuous_deriv1 hC hw_lt f.bound0 f.bound1
  have hibp2 := bilateral_ibp f.hasDeriv2 f.cont2 hC hw_lt f.bound1 f.bound2
  have hsq_eq : w ^ 2 * weilPhi f s = ∫ u : ℝ, f.deriv2 u * cexp (w * (u : ℂ)) := by
    unfold weilPhi Stage4ExplicitFormula.weilBilateralTransform
    calc w ^ 2 * ∫ u : ℝ, f.toFun u * cexp (w * (u : ℂ))
        = w * (w * ∫ u : ℝ, f.toFun u * cexp (w * (u : ℂ))) := by ring
      _ = w * -(∫ u : ℝ, f.deriv1 u * cexp (w * (u : ℂ))) := by rw [hibp1]
      _ = -(w * ∫ u : ℝ, f.deriv1 u * cexp (w * (u : ℂ))) := by ring
      _ = ∫ u : ℝ, f.deriv2 u * cexp (w * (u : ℂ)) := by rw [hibp2, neg_neg]
  have h2 : ‖w‖ ^ 2 * ‖weilPhi f s‖ ≤ M₀ := by
    rw [← norm_pow, ← norm_mul, hsq_eq]
    exact hbd_int f.deriv2 f.cont2 f.bound2
  have him_le : s.im ^ 2 ≤ ‖w‖ ^ 2 := by
    have h1 : |s.im| ≤ ‖w‖ := by simpa [w] using Complex.abs_im_le_norm w
    calc s.im ^ 2 = |s.im| ^ 2 := (sq_abs _).symm
      _ ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hsum : (1 + s.im ^ 2) * ‖weilPhi f s‖ ≤ 2 * M₀ := by
    have h2' : s.im ^ 2 * ‖weilPhi f s‖ ≤ M₀ :=
      (mul_le_mul_of_nonneg_right him_le (norm_nonneg _)).trans h2
    linarith
  exact (le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2)).mpr (by linarith)

lemma continuous_weilPhi_vertical (f : AdmissibleWeilTest) {σ : ℝ} (hlo : -1 / 2 ≤ σ) (hhi : σ ≤ 3 / 2) :
    Continuous (fun t : ℝ => weilPhi f ((σ : ℂ) + I * (t : ℂ))) := by
  have hdiff := differentiableOn_weilPhi f
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : (σ : ℂ) + I * (t : ℂ) ∈ {s : ℂ | |s.re - 1 / 2| < f.decayRate} := by
    change |((σ : ℂ) + I * (t : ℂ)).re - 1 / 2| < f.decayRate
    have h1 : |σ - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    simpa using h1.trans_lt f.decayRate_gt
  have hopen : IsOpen {s : ℂ | |s.re - 1 / 2| < f.decayRate} :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
  have hcat : ContinuousAt (weilPhi f) ((σ : ℂ) + I * (t : ℂ)) :=
    (hdiff.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  exact ContinuousAt.comp (f := fun y : ℝ => (σ : ℂ) + I * (y : ℂ)) hcat (by fun_prop)

lemma integrable_weilPhi_vertical (f : AdmissibleWeilTest) {σ : ℝ} (hlo : -1 / 2 ≤ σ) (hhi : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => weilPhi f ((σ : ℂ) + I * (t : ℂ))) := by
  obtain ⟨M, _, hbd⟩ := norm_weilPhi_strip_le f
  refine (integrable_inv_one_add_sq.const_mul M).mono'
    (continuous_weilPhi_vertical f hlo hhi).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 := hbd ((σ : ℂ) + I * (t : ℂ)) (by simpa using hlo) (by simpa using hhi)
  simpa [div_eq_mul_inv] using h1

/-! ### Native `ZetaNontrivialZero` Type (Multiplicity-Counted Directly on `riemannZeta`) -/

/-- Exact multiplicity equality `analyticOrderNatAt riemannZeta z = analyticOrderNatAt xi z`
for every `z` in the open critical strip `0 < z.re < 1`. -/
theorem analyticOrderNatAt_riemannZeta_eq_xi {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    analyticOrderNatAt riemannZeta z = analyticOrderNatAt xi z := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hz1 : z ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  let h : ℂ → ℂ := fun w => w * (w - 1) * w.Gammaℝ
  have hh_an : AnalyticAt ℂ h z := by
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ h {w : ℂ | 0 < w.re} := fun w hw => by
      have hw_pos : 0 < w.re := hw
      have hG_diff : DifferentiableAt ℂ Complex.Gamma (w / 2) :=
        Complex.differentiableAt_Gamma (w / 2) fun m hEq => by
          have hre := congrArg Complex.re hEq
          simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
          linarith [Nat.cast_nonneg (α := ℝ) m]
      have hpow_diff : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) w := by
        have hpiC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
        have hEq : (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) =
            fun u : ℂ => cexp (Complex.log (Real.pi : ℂ) * (-u / 2)) :=
          funext fun u => Complex.cpow_def_of_ne_zero hpiC _
        rw [hEq]; fun_prop
      have hGR : DifferentiableAt ℂ Complex.Gammaℝ w := by
        have hEq : Complex.Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2) :=
          funext Complex.Gammaℝ_def
        rw [hEq]
        exact hpow_diff.mul (hG_diff.comp w (differentiableAt_id.div_const 2))
      exact ((differentiableAt_id.mul (differentiableAt_id.sub (differentiableAt_const 1))).mul hGR).differentiableWithinAt
    exact hdiff.analyticAt (hopen.mem_nhds h0)
  have hh_ne : h z ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr hz1)) ?_
    exact Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hZ_an : AnalyticAt ℂ riemannZeta z := by
    have hdiff : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
      fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
    exact hdiff.analyticAt (isOpen_compl_singleton.mem_nhds hz1)
  have hxi_an : AnalyticAt ℂ xi z :=
    (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ z)
  have hev : xi =ᶠ[𝓝 z] fun w => h w * riemannZeta w := by
    have hU : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with w ⟨hw0, hw1⟩
    have hw0' : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw0; exact lt_irrefl 0 hw0
    have hw1' : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw1; exact lt_irrefl 1 hw1
    exact Stage5StirlingPhragmen.xi_eq_mul_Gammaℝ_mul_riemannZeta hw0' hw1'
      (Complex.Gammaℝ_ne_zero_of_re_pos hw0)
  have hxi_ntop : analyticOrderAt xi z ≠ ⊤ := by
    intro htop
    have h0' := (differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) (analyticOrderAt_eq_top.mp htop) (Set.mem_univ 0)
    simp at h0'
  obtain ⟨g, hg_an, hg_ne, hgeq⟩ := hxi_an.analyticOrderAt_ne_top.mp hxi_ntop
  have hordZ : analyticOrderAt riemannZeta z = (analyticOrderNatAt xi z : ℕ∞) := by
    refine hZ_an.analyticOrderAt_eq_natCast.mpr ⟨fun w => g w / h w, hg_an.div hh_an hh_ne,
      div_ne_zero hg_ne hh_ne, ?_⟩
    filter_upwards [hev, hgeq, hh_an.continuousAt.eventually_ne hh_ne] with w h1w h2w hhw
    simp only [smul_eq_mul] at h2w ⊢
    rw [h1w] at h2w
    have hmul : h w * riemannZeta w = h w * ((w - z) ^ analyticOrderNatAt xi z * (g w / h w)) := by
      rw [h2w]; field_simp [hhw]
    exact mul_left_cancel₀ hhw hmul
  change (analyticOrderAt riemannZeta z).toNat = analyticOrderNatAt xi z
  rw [hordZ, ENat.toNat_natCast]

/-- Native Mathlib nontrivial zeros of `riemannZeta` in the critical strip `0 < Re(s) < 1`,
counted with their exact analytic multiplicity `analyticOrderNatAt riemannZeta`. -/
abbrev ZetaNontrivialZero : Type :=
  Σ z : {s : ℂ // riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1},
    Fin (analyticOrderNatAt riemannZeta z.1)

/-- The underlying complex coordinate of a multiplicity-counted nontrivial zero. -/
def ZetaNontrivialZero.val (ρ : ZetaNontrivialZero) : ℂ := ρ.1.1

/-- Canonical bijection `ℕ ≃ ZetaNontrivialZero` matching `Stage7HadamardXiProduct.xiZeroSeq`. -/
def zetaNontrivialZeroEquiv : ℕ ≃ ZetaNontrivialZero :=
  xiZeroEquiv.trans
    { toFun := fun x =>
        ⟨⟨x.1.1,
          ((xi_eq_zero_iff_critical_strip_zeta_zero x.1.1).mp x.1.2).2.2,
          ((xi_eq_zero_iff_critical_strip_zeta_zero x.1.1).mp x.1.2).1,
          ((xi_eq_zero_iff_critical_strip_zeta_zero x.1.1).mp x.1.2).2.1⟩,
          x.2.cast (analyticOrderNatAt_riemannZeta_eq_xi
            ((xi_eq_zero_iff_critical_strip_zeta_zero x.1.1).mp x.1.2).1
            ((xi_eq_zero_iff_critical_strip_zeta_zero x.1.1).mp x.1.2).2.1).symm⟩
      invFun := fun y =>
        ⟨⟨y.1.1, (xi_eq_zero_iff_critical_strip_zeta_zero y.1.1).mpr ⟨y.1.2.2.1, y.1.2.2.2, y.1.2.1⟩⟩,
          y.2.cast (analyticOrderNatAt_riemannZeta_eq_xi y.1.2.2.1 y.1.2.2.2)⟩
      left_inv := fun ⟨⟨s, hs⟩, j⟩ => by
        refine Sigma.ext (Subtype.ext rfl) ?_
        simp
      right_inv := fun ⟨⟨s, hs⟩, j⟩ => by
        refine Sigma.ext (Subtype.ext rfl) ?_
        simp }

lemma zetaNontrivialZeroEquiv_val (n : ℕ) :
    (zetaNontrivialZeroEquiv n).val = xiZeroSeq n := rfl

/-- Absolute summability of `∑' n, weilPhi f (xiZeroSeq n)` for every `f : AdmissibleWeilTest`. -/
theorem summable_weilPhi_xiZeroSeq (f : AdmissibleWeilTest) :
    Summable (fun n : ℕ => weilPhi f (xiZeroSeq n)) := by
  obtain ⟨M, hM, hbd⟩ := norm_weilPhi_strip_le f
  refine Summable.of_norm_bounded (xiZeroSeq_summable_inv_sq.mul_left M) fun n => ?_
  have hst := xiZeroSeq_strip n
  have h1 := hbd (xiZeroSeq n) (by linarith [hst.1]) (by linarith [hst.2])
  have hnsq : ‖xiZeroSeq n‖ ^ 2 ≤ 1 + (xiZeroSeq n).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [hst.1, hst.2]
  have hρ_pos : 0 < ‖xiZeroSeq n‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (xiZeroSeq_ne_zero n))
  calc ‖weilPhi f (xiZeroSeq n)‖ ≤ M / (1 + (xiZeroSeq n).im ^ 2) := h1
    _ ≤ M / ‖xiZeroSeq n‖ ^ 2 := div_le_div_of_nonneg_left hM hρ_pos hnsq
    _ = M * (‖xiZeroSeq n‖ ^ 2)⁻¹ := div_eq_mul_inv _ _

lemma tsum_zetaNontrivialZero_eq_xiZeroSeq (f : AdmissibleWeilTest) :
    (∑' (ρ : ZetaNontrivialZero), weilPhi f ρ.val) = ∑' n : ℕ, weilPhi f (xiZeroSeq n) :=
  (Equiv.tsum_eq zetaNontrivialZeroEquiv (fun ρ : ZetaNontrivialZero => weilPhi f ρ.val)).symm

/-! ## Section 3: Fourier Inversion, Resolvent Integral, Prime Sum & Archimedean Digamma Term -/

/-- **Piece A (Exact Fourier Inversion on `Re(s) = 3/2`)**:
for every `g : AdmissibleWeilTest` and every `v : ℝ`,
`(1 / (2π)) ∫_{-∞}^∞ exp(-i t v) * Φ_g(3/2 + i t) dt = g(v) * exp(v)`. -/
theorem fourier_inversion_weilPhi_three_halves (g : AdmissibleWeilTest) (v : ℝ) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, cexp (-I * (t : ℂ) * (v : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      g.toFun v * ((Real.exp v : ℝ) : ℂ) := by
  let h : ℝ → ℂ := fun u => g.toFun u * ((Real.exp u : ℝ) : ℂ)
  have hh_cont : Continuous h := g.continuous.mul (Complex.continuous_ofReal.comp Real.continuous_exp)
  have hh_int : Integrable h := by
    set δ : ℝ := g.decayRate - 1
    have hδ : 0 < δ := by dsimp only [δ]; linarith [g.decayRate_gt]
    have hC := g.boundConst_nonneg
    refine ((integrable_exp_neg_abs_real hδ).const_mul g.boundConst).mono'
      hh_cont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    dsimp only [h]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos u).le]
    calc ‖g.toFun u‖ * Real.exp u
        ≤ (g.boundConst * Real.exp (-g.decayRate * |u|)) * Real.exp |u| :=
          mul_le_mul (g.bound0 u) (Real.exp_le_exp.mpr (le_abs_self u)) (Real.exp_pos _).le (by positivity)
      _ = g.boundConst * Real.exp (-δ * |u|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp only [δ]; ring
  have hf_eq : ∀ ξ : ℝ, FourierTransform.fourier h ξ =
      weilPhi g ((3 / 2 : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) := fun ξ => by
    rw [Real.fourier_eq']
    unfold weilPhi Stage4ExplicitFormula.weilBilateralTransform
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [h]
    rw [smul_eq_mul, Complex.ofReal_exp]
    have hinner : inner ℝ u ξ = u * ξ := by simp [mul_comm]
    rw [hinner]
    calc cexp (((-2 * Real.pi * (u * ξ) : ℝ) : ℂ) * I) * (g.toFun u * cexp (u : ℂ))
        = g.toFun u * (cexp (u : ℂ) * cexp (((-2 * Real.pi * (u * ξ) : ℝ) : ℂ) * I)) := by ring
      _ = g.toFun u * cexp (((3 / 2 : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ) - 1 / 2) * (u : ℂ)) := by
          rw [← Complex.exp_add]; congr 2; push_cast; ring
  have hfh_int : Integrable (FourierTransform.fourier h) := by
    have hfun : FourierTransform.fourier h =
        fun ξ : ℝ => (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) ((-2 * Real.pi) * ξ) :=
      funext fun ξ => by rw [hf_eq ξ]
    rw [hfun]
    have hint := integrable_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      hint.comp_mul_left' (neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  have hinv := hh_int.fourierInv_fourier_eq hfh_int (hh_cont.continuousAt (x := v))
  rw [Real.fourierInv_eq'] at hinv
  have hrew : (fun ξ : ℝ => cexp (((2 * Real.pi * inner ℝ ξ v : ℝ) : ℂ) * I) •
      FourierTransform.fourier h ξ) =
      fun ξ : ℝ => (fun t : ℝ => cexp (-I * (t : ℂ) * (v : ℂ)) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) ((-2 * Real.pi) * ξ) := by
    funext ξ
    rw [hf_eq ξ, smul_eq_mul]
    have hinner : inner ℝ ξ v = v * ξ := rfl
    rw [hinner]
    congr 1; congr 1; push_cast; ring
  have hcomp := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => cexp (-I * (t : ℂ) * (v : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)))
    (-2 * Real.pi)
  rw [hrew, hcomp] at hinv
  have h2pi : 0 < 2 * Real.pi := by positivity
  have habs : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    have hneg : (-2 : ℝ) * Real.pi = -(2 * Real.pi) := by ring
    rw [abs_inv, hneg, abs_neg, abs_of_pos h2pi]
  rw [habs, Complex.real_smul, Complex.ofReal_inv] at hinv
  exact hinv

/-- **Piece B (Exact Resolvent-Shift Integral on `Re(s) = 3/2`)**:
for every `g : AdmissibleWeilTest` and every real `c > 0`,
`(1 / (2π)) ∫_{-∞}^∞ (c + i t)⁻¹ * Φ_g(3/2 + i t) dt = ∫_{u > 0} g(u) * exp((1 - c) u) du`. -/
theorem integral_inv_add_I_mul_weilPhi (g : AdmissibleWeilTest) {c : ℝ} (hc : 0 < c) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((c : ℂ) + I * (t : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      ∫ u in Set.Ioi (0 : ℝ), g.toFun u * ((Real.exp ((1 - c) * u) : ℝ) : ℂ) := by
  have hint_phi : Integrable (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      integrable_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  have hcont_phi : Continuous (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      continuous_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  have hrep : ∀ t : ℝ, ((c : ℂ) + I * (t : ℂ))⁻¹ =
      ∫ u in Set.Ioi (0 : ℝ), cexp (-((c : ℂ) + I * (t : ℂ)) * (u : ℂ)) := fun t => by
    have hre : (-((c : ℂ) + I * (t : ℂ))).re < 0 := by simp [hc]
    have hne : (c : ℂ) + I * (t : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    rw [integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp [hne]
  have hmeas_prod : AEStronglyMeasurable
      (fun p : ℝ × ℝ => cexp (-((c : ℂ) + I * (p.1 : ℂ)) * (p.2 : ℂ)) *
        weilPhi g ((3 / 2 : ℂ) + I * (p.1 : ℂ)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    have hcont : Continuous (fun p : ℝ × ℝ =>
        cexp (-((c : ℂ) + I * (p.1 : ℂ)) * (p.2 : ℂ)) *
          weilPhi g ((3 / 2 : ℂ) + I * (p.1 : ℂ))) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-((c : ℂ) + I * (p.1 : ℂ)) * (p.2 : ℂ))).mul
        (hcont_phi.comp continuous_fst)
    exact hcont.aestronglyMeasurable
  have hint_prod : Integrable
      (fun p : ℝ × ℝ => cexp (-((c : ℂ) + I * (p.1 : ℂ)) * (p.2 : ℂ)) *
        weilPhi g ((3 / 2 : ℂ) + I * (p.1 : ℂ)))
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [MeasureTheory.integrable_prod_iff hmeas_prod]
    constructor
    · refine Eventually.of_forall fun t => ?_
      have hre : (-((c : ℂ) + I * (t : ℂ))).re < 0 := by simp [hc]
      simpa using (integrableOn_exp_mul_complex_Ioi hre 0).mul_const
        (weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)))
    · have hnorm_eq : (fun t : ℝ => ∫ u in Set.Ioi (0 : ℝ),
          ‖cexp (-((c : ℂ) + I * (t : ℂ)) * (u : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖) =
          fun t : ℝ => (1 / c) * ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖ := by
        funext t
        have hpt : (fun u : ℝ => ‖cexp (-((c : ℂ) + I * (t : ℂ)) * (u : ℂ)) *
            weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖) =
            fun u : ℝ => Real.exp (-c * u) * ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖ := by
          funext u
          rw [norm_mul, Complex.norm_exp]
          have hre : (-((c : ℂ) + I * (t : ℂ)) * (u : ℂ)).re = -c * u := by simp
          rw [hre]
        rw [hpt, integral_mul_const, integral_exp_mul_Ioi (by linarith : -c < 0) 0]
        simp only [mul_zero, Real.exp_zero, div_neg]
        ring
      rw [hnorm_eq]
      exact hint_phi.norm.const_mul (1 / c)
  have hLHS : ∫ t : ℝ, ((c : ℂ) + I * (t : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      ∫ t : ℝ, ∫ u in Set.Ioi (0 : ℝ),
        cexp (-((c : ℂ) + I * (t : ℂ)) * (u : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [hrep t, ← integral_mul_const]
  rw [hLHS, MeasureTheory.integral_integral_swap hint_prod, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  have hsplit_exp : (fun t : ℝ =>
      cexp (-((c : ℂ) + I * (t : ℂ)) * (u : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) =
      fun t : ℝ => ((Real.exp (-c * u) : ℝ) : ℂ) *
        (cexp (-I * (t : ℂ) * (u : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    funext t
    rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [hsplit_exp, integral_const_mul, mul_left_comm, fourier_inversion_weilPhi_three_halves g u]
  rw [← mul_assoc, mul_comm ((Real.exp (-c * u) : ℝ) : ℂ) (g.toFun u), mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

/-- **Piece C (Prime / von Mangoldt Sum Integral on `Re(s) = 3/2`)**:
for every `g : AdmissibleWeilTest`,
`(1 / (2π)) ∫_{-∞}^∞ (deriv riemannZeta (3/2 + i t) / riemannZeta (3/2 + i t)) * Φ_g(3/2 + i t) dt
  = -∑' n : ℕ, (Λ n / √n) * g(log n)`. -/
theorem integral_logDeriv_zeta_mul_weilPhi (g : AdmissibleWeilTest) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, (deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) /
          riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      -(∑' n : ℕ, (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * g.toFun (Real.log (n : ℝ))) := by
  have hint_phi : Integrable (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      integrable_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  have hcont_phi : Continuous (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      continuous_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  have hsumm_L : Summable (fun n : ℕ => (Λ n : ℝ) * ((n : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num))
    rw [LSeriesSummable] at h1
    refine h1.norm.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp [Real.rpow_neg hn_pos.le, div_eq_mul_inv]
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term (fun m => (Λ m : ℂ)) ((3 / 2 : ℂ) + I * (t : ℂ)) n *
      weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))
  have hF_norm : ∀ n : ℕ, ∀ t : ℝ, ‖F n t‖ =
      ((Λ n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) * ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖ := fun n t => by
    dsimp only [F]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [LSeries.term_of_ne_zero hn, norm_mul, norm_div, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hre : ((3 / 2 : ℂ) + I * (t : ℂ)).re = 3 / 2 := by simp
      rw [hre, Real.rpow_neg hn_pos.le, div_eq_mul_inv]
  have hF_int : ∀ n : ℕ, Integrable (F n) := fun n => by
    refine (hint_phi.norm.const_mul ((Λ n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)))).mono' ?_
      (Eventually.of_forall fun t => (hF_norm n t).le)
    rcases eq_or_ne n 0 with rfl | hn
    · have h0 : F 0 = 0 := funext fun t => by simp [F, LSeries.term_zero]
      rw [h0]; exact aestronglyMeasurable_zero
    · have hcont : Continuous (F n) := by
        have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have hEq : F n = fun t : ℝ =>
            ((Λ n : ℂ) * cexp (-Complex.log (n : ℂ) * ((3 / 2 : ℂ) + I * (t : ℂ)))) *
              weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) := by
          funext t
          dsimp only [F]
          congr 1
          rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC, div_eq_mul_inv,
            ← Complex.exp_neg]
          ring_nf
        rw [hEq]
        exact (by fun_prop : Continuous fun t : ℝ =>
          (Λ n : ℂ) * cexp (-Complex.log (n : ℂ) * ((3 / 2 : ℂ) + I * (t : ℂ)))).mul hcont_phi
      exact hcont.aestronglyMeasurable
  have hF_summ_int : Summable (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) := by
    have hEq : (fun n : ℕ => ∫ t : ℝ, ‖F n t‖) =
        fun n : ℕ => ((Λ n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ))) *
          ∫ t : ℝ, ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖ := by
      funext n; simp_rw [hF_norm n]; rw [integral_const_mul]
    rw [hEq]
    exact hsumm_L.mul_right _
  have hpt_eq : ∀ t : ℝ, (deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) /
        riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      -(∑' n : ℕ, F n t) := fun t => by
    have hre : 1 < ((3 / 2 : ℂ) + I * (t : ℂ)).re := by simp; norm_num
    have hL := RHDirect.LSeries_vonMangoldt_eq_neg_deriv_zeta_div hre
    have hneg : deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) /
        riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) =
        -LSeries (fun m => (Λ m : ℂ)) ((3 / 2 : ℂ) + I * (t : ℂ)) := by
      linear_combination hL
    rw [hneg, neg_mul]
    congr 1
    unfold LSeries
    rw [← tsum_mul_right]
  have hswap := MeasureTheory.integral_tsum (fun n => (hF_int n).aestronglyMeasurable)
    (by
      rw [← lt_top_iff_ne_top]
      calc ∑' n : ℕ, ∫⁻ t : ℝ, ‖F n t‖ₑ
          = ∑' n : ℕ, ENNReal.ofReal (∫ t : ℝ, ‖F n t‖) :=
            tsum_congr fun n => (ofReal_integral_norm_eq_lintegral_enorm (hF_int n)).symm
        _ = ENNReal.ofReal (∑' n : ℕ, ∫ t : ℝ, ‖F n t‖) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _)
              hF_summ_int).symm
        _ < ⊤ := ENNReal.ofReal_lt_top)
  simp_rw [hpt_eq]
  rw [integral_neg, mul_neg, hswap, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F, LSeries.term_zero]
  · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn_pos.ne'
    have hFn : (fun t : ℝ => F n t) = fun t : ℝ =>
        (((Λ n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (cexp (-I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
      funext t
      dsimp only [F]
      rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, Complex.cpow_def_of_ne_zero hnC,
        ← Complex.exp_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_log hn_pos.le]
      have hsplit : cexp (-((Real.log (n : ℝ) : ℂ) * ((3 / 2 : ℂ) + I * (t : ℂ)))) =
          (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * cexp (-I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
        rw [Real.rpow_def_of_pos hn_pos, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hsplit, Complex.ofReal_mul]; ring
    rw [hFn, integral_const_mul, mul_left_comm, fourier_inversion_weilPhi_three_halves g (Real.log (n : ℝ)),
      Real.exp_log hn_pos]
    rw [← mul_assoc, mul_comm ((((Λ n : ℝ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) _,
      mul_assoc, ← Complex.ofReal_mul, mul_comm (g.toFun _)]
    congr 1; congr 1
    have hpow : (n : ℝ) ^ (-(3 / 2 : ℝ)) * (n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn_pos.le]
      conv_lhs => rhs; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hn_pos]; norm_num
    rw [mul_assoc, hpow, div_eq_mul_inv]

/-- Digamma recurrence `Complex.digamma (w + 1) = Complex.digamma w + 1 / w` for `0 < w.re`. -/
lemma digamma_add_one {w : ℂ} (hw : 0 < w.re) :
    Complex.digamma (w + 1) = Complex.digamma w + 1 / w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; exact lt_irrefl 0 hw
  have hG_ne : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero fun m hEq => by
    have hre := congrArg Complex.re hEq
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG_diff : DifferentiableAt ℂ Complex.Gamma w :=
    Complex.differentiableAt_Gamma w fun m hEq => by
      have hre := congrArg Complex.re hEq
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hev : (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[𝓝 w] fun z : ℂ => z * Complex.Gamma z := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact Complex.Gamma_add_one z (fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz)
  have hd_lhs : deriv (fun z : ℂ => Complex.Gamma (z + 1)) w = deriv Complex.Gamma (w + 1) := by
    have hG1 : DifferentiableAt ℂ Complex.Gamma (w + 1) :=
      Complex.differentiableAt_Gamma (w + 1) fun m hEq => by
        have hre := congrArg Complex.re hEq
        simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
        linarith [Nat.cast_nonneg (α := ℝ) m]
    simpa [Function.comp_def] using (hG1.hasDerivAt.comp w ((hasDerivAt_id w).add_const 1)).deriv
  have hd_rhs : deriv (fun z : ℂ => z * Complex.Gamma z) w = Complex.Gamma w + w * deriv Complex.Gamma w := by
    simpa using ((hasDerivAt_id w).fun_mul hG_diff.hasDerivAt).deriv
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply,
    ← hd_lhs, hev.deriv_eq, hd_rhs, Complex.Gamma_add_one w hw0]
  field_simp [hw0, hG_ne]
  ring

/-- Elementary lower bound `1 - Real.exp (-2 * u) ≥ u / 2` for `u ∈ (0, 1]`. -/
private lemma one_sub_exp_neg_two_ge {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    u / 2 ≤ 1 - Real.exp (-2 * u) := by
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hexp_eq : Real.exp (-2 * u) = (Real.exp (2 * u))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hexp_eq]
  have hinv : (Real.exp (2 * u))⁻¹ ≤ (1 + 2 * u)⁻¹ := inv_anti₀ (by linarith) h1
  have hcalc : u / 2 ≤ 1 - (1 + 2 * u)⁻¹ := by
    have hden : 0 < 1 + 2 * u := by linarith
    have hEq : 1 - (1 + 2 * u)⁻¹ = 2 * u / (1 + 2 * u) := by field_simp [hden.ne']; ring
    rw [hEq, div_le_div_iff₀ two_pos hden]
    nlinarith
  linarith

/-- Integrability of the single-sided archimedean digamma integrand
`u ↦ (g(0) e^{-2u} - g(u) e^{-u/2}) / (1 - e^{-2u})` on `(0, ∞)`. -/
lemma integrableOn_weilArchHalf (g : AdmissibleWeilTest) :
    IntegrableOn
      (fun u : ℝ =>
        (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u))
      (Set.Ioi (0 : ℝ)) := by
  have hC := g.boundConst_nonneg
  let Q : ℝ → ℂ := fun u =>
    ((Real.exp (-2 * u) : ℝ) : ℂ) * g.toFun 0 - ((Real.exp (-u / 2) : ℝ) : ℂ) * g.toFun u
  have hQ_deriv : ∀ u : ℝ, HasDerivAt Q
      ((-2 : ℂ) * ((Real.exp (-2 * u) : ℝ) : ℂ) * g.toFun 0 -
       ((-1 / 2 : ℂ) * ((Real.exp (-u / 2) : ℝ) : ℂ) * g.toFun u +
        ((Real.exp (-u / 2) : ℝ) : ℂ) * g.deriv1 u)) u := fun u => by
    have he1 : HasDerivAt (fun t : ℝ => ((Real.exp (-2 * t) : ℝ) : ℂ))
        ((-2 : ℂ) * ((Real.exp (-2 * u) : ℝ) : ℂ)) u := by
      have hlin : HasDerivAt (fun t : ℝ => -2 * t) (-2) u := by
        simpa using (hasDerivAt_id u).const_mul (-2 : ℝ)
      have hr : HasDerivAt (fun t : ℝ => Real.exp (-2 * t)) (Real.exp (-2 * u) * (-2)) u :=
        hlin.exp
      simpa [mul_comm] using hr.ofReal_comp
    have he2 : HasDerivAt (fun t : ℝ => ((Real.exp (-t / 2) : ℝ) : ℂ))
        ((-1 / 2 : ℂ) * ((Real.exp (-u / 2) : ℝ) : ℂ)) u := by
      have hr : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-u / 2) * (-1 / 2)) u := by
        have hlin : HasDerivAt (fun t : ℝ => -t / 2) (-1 / 2) u := by
          simpa using (hasDerivAt_neg u).div_const (2 : ℝ)
        exact hlin.exp
      simpa [mul_comm] using hr.ofReal_comp
    exact (he1.mul_const (g.toFun 0)).sub (he2.mul (g.hasDeriv1 u))
  have hQ0 : Q 0 = 0 := by simp [Q]
  set L : ℝ := 4 * g.boundConst
  have hL_nn : 0 ≤ L := by dsimp only [L]; positivity
  have hQ_lip : ∀ u ∈ Set.Icc (0 : ℝ) 1, ‖Q u‖ ≤ L * u := fun u hu => by
    have hbd' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖(-2 : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ) * g.toFun 0 -
         ((-1 / 2 : ℂ) * ((Real.exp (-t / 2) : ℝ) : ℂ) * g.toFun t +
          ((Real.exp (-t / 2) : ℝ) : ℂ) * g.deriv1 t)‖ ≤ L := fun t ht => by
      have he1 : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
      have he2 : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
      have hg0 : ‖g.toFun 0‖ ≤ g.boundConst := by simpa using g.bound0 0
      have hgt : ‖g.toFun t‖ ≤ g.boundConst :=
        (g.bound0 t).trans (mul_le_of_le_one_right hC
          (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg t])))
      have hg1 : ‖g.deriv1 t‖ ≤ g.boundConst :=
        (g.bound1 t).trans (mul_le_of_le_one_right hC
          (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg t])))
      have h1 := norm_sub_le ((-2 : ℂ) * ((Real.exp (-2 * t) : ℝ) : ℂ) * g.toFun 0)
        ((-1 / 2 : ℂ) * ((Real.exp (-t / 2) : ℝ) : ℂ) * g.toFun t +
         ((Real.exp (-t / 2) : ℝ) : ℂ) * g.deriv1 t)
      have h2 := norm_add_le ((-1 / 2 : ℂ) * ((Real.exp (-t / 2) : ℝ) : ℂ) * g.toFun t)
        (((Real.exp (-t / 2) : ℝ) : ℂ) * g.deriv1 t)
      simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, norm_div, norm_one] at h1 h2
      dsimp only [L]
      nlinarith [Real.exp_pos (-2 * t), Real.exp_pos (-t / 2)]
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hQ_deriv t).hasDerivWithinAt) hbd' (convex_Icc 0 1)
      (Set.left_mem_Icc.mpr zero_le_one) hu
    rw [hQ0, sub_zero, sub_zero, Real.norm_of_nonneg hu.1] at hmvt
    exact hmvt
  have hcont_Ioi : ContinuousOn
      (fun u : ℝ =>
        (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u))
      (Set.Ioi (0 : ℝ)) := by
    have hden_ne : ∀ u ∈ Set.Ioi (0 : ℝ), 1 - Real.exp (-2 * u) ≠ 0 := fun u hu => by
      have : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Set.mem_Ioi.mp hu])
      linarith
    refine ((Complex.continuous_ofReal.comp_continuousOn
        ((by fun_prop : Continuous fun u : ℝ => Real.exp (-2 * u)).continuousOn.div
          (by fun_prop) hden_ne)).mul continuousOn_const).sub
      ((Complex.continuous_ofReal.comp_continuousOn
        ((by fun_prop : Continuous fun u : ℝ => Real.exp (-u / 2)).continuousOn.div
          (by fun_prop) hden_ne)).mul g.continuous.continuousOn)
  have hrew : ∀ u : ℝ,
      (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
       ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u) =
      Q u / ((1 - Real.exp (-2 * u) : ℝ) : ℂ) := fun u => by
    dsimp only [Q]
    push_cast; ring
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · refine (integrableOn_const (C := 2 * L) (hs := measure_Ioc_lt_top.ne)).mono'
      ((hcont_Ioi.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => ?_
    rw [hrew u, norm_div, Complex.norm_real]
    have hden_pos : 0 < 1 - Real.exp (-2 * u) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hu.1]))
    rw [Real.norm_of_nonneg hden_pos.le]
    have h1 := hQ_lip u ⟨hu.1.le, hu.2⟩
    have h2 := one_sub_exp_neg_two_ge hu.1 hu.2
    calc ‖Q u‖ / (1 - Real.exp (-2 * u)) ≤ (L * u) / (u / 2) :=
          div_le_div₀ (mul_nonneg hL_nn hu.1.le) h1 (by linarith [hu.1]) h2
      _ = 2 * L := by field_simp [hu.1.ne']
  · set c1 : ℝ := 1 - Real.exp (-2)
    have hc1 : 0 < c1 := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    refine ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 1).const_mul
        (2 * g.boundConst / c1)).mono'
      ((hcont_Ioi.mono (Set.Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    have hu1 : 1 < u := hu
    rw [hrew u, norm_div, Complex.norm_real]
    have hden_ge : c1 ≤ 1 - Real.exp (-2 * u) := by
      dsimp only [c1]
      have : Real.exp (-2 * u) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hden_pos : 0 < 1 - Real.exp (-2 * u) := hc1.trans_le hden_ge
    rw [Real.norm_of_nonneg hden_pos.le]
    have hQ_le : ‖Q u‖ ≤ 2 * g.boundConst * Real.exp (-(1 / 2) * u) := by
      dsimp only [Q]
      have hg0 : ‖g.toFun 0‖ ≤ g.boundConst := by simpa using g.bound0 0
      have hgu : ‖g.toFun u‖ ≤ g.boundConst :=
        (g.bound0 u).trans (mul_le_of_le_one_right hC
          (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg u])))
      have he1 : Real.exp (-2 * u) ≤ Real.exp (-(1 / 2) * u) := Real.exp_le_exp.mpr (by linarith)
      have he2 : Real.exp (-u / 2) = Real.exp (-(1 / 2) * u) := by congr 1; ring
      calc ‖((Real.exp (-2 * u) : ℝ) : ℂ) * g.toFun 0 - ((Real.exp (-u / 2) : ℝ) : ℂ) * g.toFun u‖
          ≤ ‖((Real.exp (-2 * u) : ℝ) : ℂ) * g.toFun 0‖ +
            ‖((Real.exp (-u / 2) : ℝ) : ℂ) * g.toFun u‖ := norm_sub_le _ _
        _ = Real.exp (-2 * u) * ‖g.toFun 0‖ + Real.exp (-u / 2) * ‖g.toFun u‖ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        _ ≤ Real.exp (-(1 / 2) * u) * g.boundConst + Real.exp (-(1 / 2) * u) * g.boundConst := by
            rw [he2]
            exact add_le_add (mul_le_mul he1 hg0 (norm_nonneg _) (Real.exp_pos _).le)
              (mul_le_mul_of_nonneg_left hgu (Real.exp_pos _).le)
        _ = 2 * g.boundConst * Real.exp (-(1 / 2) * u) := by ring
    calc ‖Q u‖ / (1 - Real.exp (-2 * u))
        ≤ (2 * g.boundConst * Real.exp (-(1 / 2) * u)) / c1 :=
          div_le_div₀ (by positivity) hQ_le hc1 hden_ge
      _ = (2 * g.boundConst / c1) * Real.exp (-(1 / 2) * u) := by ring

/-- **Piece D (Archimedean Digamma Integral on `Re(s) = 3/2`)**:
for every `g : AdmissibleWeilTest`,
`(1 / (2π)) ∫_{-∞}^∞ (1/2) * digamma((3/2 + i t) / 2) * Φ_g(3/2 + i t) dt
  = -(γ / 2) * g(0) + ∫_{u > 0} (e^{-2u} g(0) - e^{-u/2} g(u)) / (1 - e^{-2u}) du`. -/
theorem integral_half_digamma_mul_weilPhi (g : AdmissibleWeilTest) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((1 / 2 : ℂ) * Complex.digamma (((3 / 2 : ℂ) + I * (t : ℂ)) / 2)) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      -((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) * g.toFun 0 +
        ∫ u in Set.Ioi (0 : ℝ),
          (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
           ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u) := by
  obtain ⟨M, hM, hphi_bd⟩ := norm_weilPhi_strip_le g
  have hint_phi : Integrable (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      integrable_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  have hcont_phi : Continuous (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      continuous_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  let D : ℕ → ℝ → ℂ := fun k t =>
    ((((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ - (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))⁻¹) *
      weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))
  have hdig_expand : ∀ t : ℝ,
      ((1 / 2 : ℂ) * Complex.digamma (((3 / 2 : ℂ) + I * (t : ℂ)) / 2)) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      -((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) +
        ∑' k : ℕ, D k t := fun t => by
    have hre : 0 < (((3 / 2 : ℂ) + I * (t : ℂ)) / 2).re := by simp
    rw [Stage7VonMangoldtExplicit.digamma_eq_neg_eulerMascheroni_add_tsum hre,
      mul_add, add_mul, ← tsum_mul_left, ← tsum_mul_right]
    congr 1
    · push_cast; ring
    · refine tsum_congr fun k => ?_
      dsimp only [D]
      congr 1
      have h1 : (1 / 2 : ℂ) * (((k + 1 : ℕ) : ℂ))⁻¹ = (((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ := by
        rw [one_div, ← mul_inv]; push_cast; rw [mul_comm]
      have h2 : (1 / 2 : ℂ) * ((((3 / 2 : ℂ) + I * (t : ℂ)) / 2 + (k : ℂ))⁻¹) =
          (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))⁻¹ := by
        have hden : (2 : ℂ) * (((3 / 2 : ℂ) + I * (t : ℂ)) / 2 + (k : ℂ)) =
            ((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ) := by push_cast; ring
        rw [← hden, mul_inv]; ring
      rw [mul_sub, h1, h2]
  let K : ℝ → ℝ := fun t => if |t| ≤ 1 then 1 else |t| ^ (-(5 / 4 : ℝ))
  have hK_int : Integrable K := by
    have hpos : IntegrableOn (fun t : ℝ => t ^ (-(5 / 4 : ℝ))) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : -(5 / 4 : ℝ) < -1) zero_lt_one
    have hneg : IntegrableOn (fun t : ℝ => (-t) ^ (-(5 / 4 : ℝ))) (Set.Iic (-1 : ℝ)) := by
      have h1 : IntegrableOn (fun t : ℝ => t ^ (-(5 / 4 : ℝ))) (Set.Ici (1 : ℝ)) :=
        hpos.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
      have h2 := h1.comp_neg
      rwa [Set.neg_Ici] at h2
    have hmid : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-1 : ℝ) 1) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (1 : ℝ)), integrableOn_union]
    constructor
    · rw [← Set.Iic_union_Ioc_eq_Iic (by norm_num : (-1 : ℝ) ≤ 1), integrableOn_union]
      constructor
      · refine hneg.congr_fun (fun t ht => ?_) measurableSet_Iic
        have ht1 : t ≤ -1 := Set.mem_Iic.mp ht
        by_cases heq : t = -1
        · subst heq; simp [K]
        · have ht_lt : t < -1 := lt_of_le_of_ne ht1 heq
          have hgt : 1 < |t| := by rw [abs_of_neg (by linarith)]; linarith
          dsimp only [K]; rw [if_neg (not_le.mpr hgt), abs_of_neg (by linarith)]
      · refine (hmid.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
        have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
        simp [K, habs]
    · refine hpos.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht1 : 1 < t := Set.mem_Ioi.mp ht
      have hgt : 1 < |t| := by rw [abs_of_pos (by linarith)]; exact ht1
      dsimp only [K]; rw [if_neg (not_le.mpr hgt), abs_of_pos (by linarith)]
  have hD_bound : ∀ k : ℕ, ∀ t : ℝ,
      ‖D k t‖ ≤ (2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) * K t := fun k t => by
    set a : ℝ := ((k + 1 : ℕ) : ℝ)
    have ha1 : 1 ≤ a := by dsimp only [a]; exact_mod_cast Nat.succ_pos k
    have ha0 : 0 < a := zero_lt_one.trans_le ha1
    have h2a_ne : ((2 * (k + 1 : ℕ) : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 0 < 2 * (k + 1) by omega).ne'
    have hden_re : 0 < (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)).re := by
      simp; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hden_ne : ((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ) ≠ 0 := fun h => by
      rw [h, Complex.zero_re] at hden_re; exact lt_irrefl 0 hden_re
    have hdiff : ((((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ - (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))⁻¹) =
        (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) /
          (((2 * (k + 1 : ℕ) : ℕ) : ℂ) * (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))) := by
      rw [inv_sub_inv h2a_ne hden_ne]
      congr 1; push_cast; ring
    have hden_ge_a : a ≤ ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
      have h1 := Complex.abs_re_le_norm (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))
      have hre : (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)).re = 3 / 2 + 2 * (k : ℝ) := by simp
      rw [hre, abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) k])] at h1
      have ha_le : a ≤ 3 / 2 + 2 * (k : ℝ) := by
        dsimp only [a]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
      exact ha_le.trans h1
    have hden_ge_t : |t| ≤ ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))
    have hphi := hphi_bd ((3 / 2 : ℂ) + I * (t : ℂ)) (by simp; norm_num) (by simp)
    have him_eq : ((3 / 2 : ℂ) + I * (t : ℂ)).im = t := by simp
    rw [him_eq] at hphi
    dsimp only [D]
    rw [hdiff, norm_mul, norm_div, norm_mul, Complex.norm_natCast]
    have h2a_eq : ((2 * (k + 1 : ℕ) : ℕ) : ℝ) = 2 * a := by dsimp only [a]; push_cast; ring
    rw [h2a_eq]
    by_cases ht1 : |t| ≤ 1
    · have hKt : K t = 1 := if_pos ht1
      rw [hKt, mul_one]
      have hnum : ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ ≤ 2 := by
        calc ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖
            ≤ ‖((-1 / 2 : ℝ) : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
          _ = 1 / 2 + |t| := by simp [Complex.norm_I]
          _ ≤ 2 := by linarith
      have hphi_le : ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖ ≤ M :=
        hphi.trans (div_le_self hM (by linarith [sq_nonneg t]))
      have ha_comb : (a * a)⁻¹ ≤ a ^ (-(7 / 4 : ℝ)) := by
        rw [mul_inv, ← Real.rpow_neg_one a]
        calc a ^ (-1 : ℝ) * a ^ (-1 : ℝ) ≤ a ^ (-1 : ℝ) * a ^ (-(3 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num)) (by positivity)
          _ = a ^ (-(7 / 4 : ℝ)) := by rw [← Real.rpow_add ha0]; norm_num
      have hprod_ge : 2 * (a * a) ≤ 2 * a * ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
        nlinarith
      calc ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ /
              (2 * a * ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖) *
              ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖
          ≤ (2 / (2 * (a * a))) * M :=
            mul_le_mul (div_le_div₀ (by norm_num) hnum (by positivity) hprod_ge) hphi_le (norm_nonneg _) (by positivity)
        _ = M * (a * a)⁻¹ := by field_simp [ha0.ne']
        _ ≤ M * a ^ (-(7 / 4 : ℝ)) := mul_le_mul_of_nonneg_left ha_comb hM
        _ ≤ 2 * M * a ^ (-(7 / 4 : ℝ)) := by nlinarith [Real.rpow_nonneg ha0.le (-(7 / 4 : ℝ))]
    · push Not at ht1
      have hKt : K t = |t| ^ (-(5 / 4 : ℝ)) := if_neg (not_le.mpr ht1)
      rw [hKt]
      have ht0 : 0 < |t| := zero_lt_one.trans ht1
      have hnum : ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ ≤ 2 * |t| := by
        calc ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖
            ≤ ‖((-1 / 2 : ℝ) : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
          _ = 1 / 2 + |t| := by simp [Complex.norm_I]
          _ ≤ 2 * |t| := by linarith
      have hphi_le : ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖ ≤ M / |t| ^ 2 := by
        refine hphi.trans (div_le_div_of_nonneg_left hM (sq_pos_of_pos ht0) ?_)
        rw [sq_abs]; linarith
      have hden_ge_mix : a ^ (3 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ) ≤
          ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
        set N : ℝ := ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖
        have hN_pos : 0 < N := ha0.trans_le hden_ge_a
        have hpow4 : (a ^ (3 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ)) ^ 4 ≤ N ^ 4 := by
          have h1 : (a ^ (3 / 4 : ℝ)) ^ 4 = a ^ 3 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]; norm_num
          have h2 : (|t| ^ (1 / 4 : ℝ)) ^ 4 = |t| := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
          rw [mul_pow, h1, h2]
          calc a ^ 3 * |t| ≤ N ^ 3 * N :=
                mul_le_mul (pow_le_pow_left₀ ha0.le hden_ge_a 3) hden_ge_t ht0.le (by positivity)
            _ = N ^ 4 := by ring
        by_contra hlt
        push Not at hlt
        have hstrict : N ^ 4 < (a ^ (3 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ)) ^ 4 :=
          pow_lt_pow_left₀ hlt hN_pos.le (by norm_num)
        linarith
      have hprod_ge : 2 * a * (a ^ (3 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ)) ≤
          2 * a * ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hden_ge_mix (by positivity)
      have ha_comb : a * a ^ (3 / 4 : ℝ) = a ^ (7 / 4 : ℝ) := by
        conv_lhs => lhs; rw [← Real.rpow_one a]
        rw [← Real.rpow_add ha0]; norm_num
      have ht_comb : |t| / (|t| ^ (1 / 4 : ℝ) * |t| ^ 2) = |t| ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_two |t|, ← Real.rpow_add ht0]
        conv_lhs => lhs; rw [← Real.rpow_one |t|]
        rw [← Real.rpow_sub ht0]; norm_num
      calc ‖((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)‖ /
              (2 * a * ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖) *
              ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖
          ≤ ((2 * |t|) / (2 * a * (a ^ (3 / 4 : ℝ) * |t| ^ (1 / 4 : ℝ)))) * (M / |t| ^ 2) :=
            mul_le_mul (div_le_div₀ (by positivity) hnum (by positivity) hprod_ge) hphi_le (norm_nonneg _) (by positivity)
        _ = M * (a * a ^ (3 / 4 : ℝ))⁻¹ * (|t| / (|t| ^ (1 / 4 : ℝ) * |t| ^ 2)) := by ring
        _ = M * a ^ (-(7 / 4 : ℝ)) * |t| ^ (-(5 / 4 : ℝ)) := by
            rw [ha_comb, ← Real.rpow_neg ha0.le, ht_comb]
        _ ≤ 2 * M * a ^ (-(7 / 4 : ℝ)) * |t| ^ (-(5 / 4 : ℝ)) := by
            have : 0 ≤ M * a ^ (-(7 / 4 : ℝ)) * |t| ^ (-(5 / 4 : ℝ)) := by positivity
            linarith
  have hD_int : ∀ k : ℕ, Integrable (D k) := fun k => by
    refine (hK_int.const_mul (2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ)))).mono' ?_
      (Eventually.of_forall (hD_bound k))
    have hcont : Continuous (D k) := by
      dsimp only [D]
      refine (continuous_const.sub (Continuous.inv₀ (by fun_prop) fun t h0 => ?_)).mul hcont_phi
      have := congrArg Complex.re h0; simp at this; linarith [Nat.cast_nonneg (α := ℝ) k]
    exact hcont.aestronglyMeasurable
  have hsumm_p : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (7 / 4 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    refine ((summable_nat_add_iff 1).mpr h1).congr fun k => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg (k + 1))]
  have hD_summ_int : Summable (fun k : ℕ => ∫ t : ℝ, ‖D k t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((hsumm_p.mul_left (2 * M)).mul_right (∫ t : ℝ, K t))
    calc ∫ t : ℝ, ‖D k t‖
        ≤ ∫ t : ℝ, (2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) * K t :=
          integral_mono (hD_int k).norm (hK_int.const_mul _) (hD_bound k)
      _ = 2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ)) * ∫ t : ℝ, K t := integral_const_mul _ _
  have hD_lint : ∑' k : ℕ, ∫⁻ t : ℝ, ‖D k t‖ₑ ≠ ⊤ := by
    rw [← lt_top_iff_ne_top]
    calc ∑' k : ℕ, ∫⁻ t : ℝ, ‖D k t‖ₑ
        = ∑' k : ℕ, ENNReal.ofReal (∫ t : ℝ, ‖D k t‖) :=
          tsum_congr fun k => (ofReal_integral_norm_eq_lintegral_enorm (hD_int k)).symm
      _ = ENNReal.ofReal (∑' k : ℕ, ∫ t : ℝ, ‖D k t‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => integral_nonneg fun _ => norm_nonneg _)
            hD_summ_int).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hD_tsum_int : Integrable (fun t : ℝ => ∑' k : ℕ, D k t) := by
    refine (hK_int.const_mul (2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ)))).mono' ?_
      (Eventually.of_forall fun t => ?_)
    · refine aestronglyMeasurable_of_tendsto_ae atTop
        (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun k _ => (hD_int k).aestronglyMeasurable)
        (Eventually.of_forall fun t => ?_)
      have hsumm_t : Summable (fun k : ℕ => D k t) :=
        Summable.of_norm_bounded ((hsumm_p.mul_left (2 * M)).mul_right (K t)) (fun k => hD_bound k t)
      exact hsumm_t.hasSum.tendsto_sum_nat
    · have hsumm_t : Summable (fun k : ℕ => ‖D k t‖) :=
        ((hsumm_p.mul_left (2 * M)).mul_right (K t)).of_nonneg_of_le
          (fun _ => norm_nonneg _) (fun k => hD_bound k t)
      calc ‖∑' k : ℕ, D k t‖ ≤ ∑' k : ℕ, ‖D k t‖ := norm_tsum_le_tsum_norm hsumm_t
        _ ≤ ∑' k : ℕ, (2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) * K t :=
            hsumm_t.tsum_le_tsum (fun k => hD_bound k t) ((hsumm_p.mul_left (2 * M)).mul_right (K t))
        _ = (2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(7 / 4 : ℝ))) * K t := by
            rw [tsum_mul_right, tsum_mul_left]
  have hswap := MeasureTheory.integral_tsum (fun k => (hD_int k).aestronglyMeasurable) hD_lint
  simp_rw [hdig_expand]
  rw [integral_add (hint_phi.const_mul _) hD_tsum_int, integral_const_mul, mul_add,
    mul_left_comm ((2 * Real.pi : ℝ) : ℂ)⁻¹ (-((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ))]
  have hzero_inv : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) = g.toFun 0 := by
    have h0 := fourier_inversion_weilPhi_three_halves g 0
    simpa using h0
  rw [hzero_inv, hswap, ← tsum_mul_left]
  congr 1
  let Q : ℝ → ℂ := fun u =>
    ((Real.exp (-2 * u) : ℝ) : ℂ) * g.toFun 0 - ((Real.exp (-u / 2) : ℝ) : ℂ) * g.toFun u
  have hterm_k : ∀ k : ℕ,
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, D k t =
        ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u := fun k => by
    dsimp only [D]
    have h1_int : Integrable (fun t : ℝ =>
        (((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) :=
      hint_phi.const_mul _
    have h2_int : Integrable (fun t : ℝ =>
        (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
      refine hint_phi.norm.mono' ?_ (Eventually.of_forall fun t => ?_)
      · exact ((Continuous.inv₀ (by fun_prop) fun t h0 => by
          have := congrArg Complex.re h0; simp at this; linarith [Nat.cast_nonneg (α := ℝ) k]).mul hcont_phi).aestronglyMeasurable
      · rw [norm_mul, norm_inv]
        have hge : (1 : ℝ) ≤ ‖((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)‖ := by
          have hre := Complex.abs_re_le_norm (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))
          have hr : (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ)).re = 3 / 2 + 2 * (k : ℝ) := by simp
          rw [hr, abs_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) k])] at hre
          linarith [Nat.cast_nonneg (α := ℝ) k]
        exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hge)
    have hsub_fn : (fun t : ℝ => ((((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ -
          (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))⁻¹) *
          weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) =
        fun t : ℝ => (((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) -
          (((3 / 2 + 2 * (k : ℝ) : ℝ) : ℂ) + I * (t : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) :=
      funext fun t => sub_mul _ _ _
    rw [hsub_fn, integral_sub h1_int h2_int, mul_sub, integral_const_mul, mul_left_comm, hzero_inv,
      integral_inv_add_I_mul_weilPhi g (c := 3 / 2 + 2 * (k : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k])]
    have hneg_k : -(2 * ((k + 1 : ℕ) : ℝ)) < 0 := by
      have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hterm1 : (((2 * (k + 1 : ℕ) : ℕ) : ℂ))⁻¹ * g.toFun 0 =
        ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (-(2 * ((k + 1 : ℕ) : ℝ)) * u) : ℝ) : ℂ) * g.toFun 0 := by
      have hint_e : ∫ u in Set.Ioi (0 : ℝ), Real.exp (-(2 * ((k + 1 : ℕ) : ℝ)) * u) =
          (2 * ((k + 1 : ℕ) : ℝ))⁻¹ := by
        rw [integral_exp_mul_Ioi hneg_k 0]
        simp only [mul_zero, Real.exp_zero, div_neg]
        field_simp
      rw [integral_mul_const]
      have hcast : ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (-(2 * ((k + 1 : ℕ) : ℝ)) * u) : ℝ) : ℂ) =
          (((∫ u in Set.Ioi (0 : ℝ), Real.exp (-(2 * ((k + 1 : ℕ) : ℝ)) * u)) : ℝ) : ℂ) :=
        integral_ofReal
      rw [hcast, hint_e]; push_cast; rfl
    rw [hterm1]
    have hi1 : IntegrableOn (fun u : ℝ => ((Real.exp (-(2 * ((k + 1 : ℕ) : ℝ)) * u) : ℝ) : ℂ) * g.toFun 0)
        (Set.Ioi (0 : ℝ)) := by
      refine (integrableOn_exp_mul_Ioi hneg_k 0).const_mul ‖g.toFun 0‖
        |>.mono' ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    have hi2 : IntegrableOn (fun u : ℝ => g.toFun u * ((Real.exp ((1 - (3 / 2 + 2 * (k : ℝ))) * u) : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) := by
      have hC := g.boundConst_nonneg
      refine (integrableOn_exp_mul_Ioi (by linarith [Nat.cast_nonneg (α := ℝ) k] :
          1 - (3 / 2 + 2 * (k : ℝ)) < 0) 0).const_mul g.boundConst
        |>.mono' (g.continuous.mul (Complex.continuous_ofReal.comp (by fun_prop))).aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hgu : ‖g.toFun u‖ ≤ g.boundConst :=
        (g.bound0 u).trans (mul_le_of_le_one_right hC
          (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg u])))
      exact mul_le_mul_of_nonneg_right hgu (Real.exp_pos _).le
    rw [← integral_sub hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    dsimp only [Q]
    rw [mul_sub, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
      ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, mul_comm (g.toFun u)]
    congr 1
    · congr 2; congr 1; push_cast; ring
    · congr 2; congr 1; ring
  simp_rw [hterm_k]
  have hQ_lim_int := integrableOn_weilArchHalf g
  have hQ_eq : ∀ u : ℝ,
      (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
       ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u) =
      Q u / ((1 - Real.exp (-2 * u) : ℝ) : ℂ) := fun u => by
    dsimp only [Q]; push_cast; ring
  have hsumm_term : Summable (fun k : ℕ =>
      ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u) := by
    have h1 := hD_summ_int.mul_left ((2 * Real.pi)⁻¹)
    refine Summable.of_norm_bounded h1 fun k => ?_
    rw [← hterm_k k, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  have htend_N : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u)
      atTop
      (𝓝 (∫ u in Set.Ioi (0 : ℝ),
        (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u))) := by
    have hpart_int : ∀ k : ℕ, IntegrableOn
        (fun u : ℝ => ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u) (Set.Ioi (0 : ℝ)) := fun k => by
      have hC := g.boundConst_nonneg
      have hcont : Continuous (fun u : ℝ => ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u) :=
        (Complex.continuous_ofReal.comp (by fun_prop)).mul
          (((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const).sub
           ((Complex.continuous_ofReal.comp (by fun_prop)).mul g.continuous))
      refine ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).const_mul (2 * g.boundConst)).mono'
        hcont.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := hu
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hk_le1 : Real.exp (-(2 * (k : ℝ)) * u) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
      have hg0 : ‖g.toFun 0‖ ≤ g.boundConst := by simpa using g.bound0 0
      have hgu : ‖g.toFun u‖ ≤ g.boundConst :=
        (g.bound0 u).trans (mul_le_of_le_one_right hC
          (Real.exp_le_one_iff.mpr (by nlinarith [g.decayRate_gt, abs_nonneg u])))
      have hQ_le : ‖Q u‖ ≤ 2 * g.boundConst * Real.exp (-(1 / 2) * u) := by
        dsimp only [Q]
        have he1 : Real.exp (-2 * u) ≤ Real.exp (-(1 / 2) * u) := Real.exp_le_exp.mpr (by linarith)
        have he2 : Real.exp (-u / 2) = Real.exp (-(1 / 2) * u) := by congr 1; ring
        calc ‖((Real.exp (-2 * u) : ℝ) : ℂ) * g.toFun 0 - ((Real.exp (-u / 2) : ℝ) : ℂ) * g.toFun u‖
            ≤ Real.exp (-2 * u) * ‖g.toFun 0‖ + Real.exp (-u / 2) * ‖g.toFun u‖ := by
              refine (norm_sub_le _ _).trans_eq ?_
              simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          _ ≤ Real.exp (-(1 / 2) * u) * g.boundConst + Real.exp (-(1 / 2) * u) * g.boundConst := by
              rw [he2]
              exact add_le_add (mul_le_mul he1 hg0 (norm_nonneg _) (Real.exp_pos _).le)
                (mul_le_mul_of_nonneg_left hgu (Real.exp_pos _).le)
          _ = 2 * g.boundConst * Real.exp (-(1 / 2) * u) := by ring
      calc Real.exp (-(2 * (k : ℝ)) * u) * ‖Q u‖
          ≤ 1 * (2 * g.boundConst * Real.exp (-(1 / 2) * u)) :=
            mul_le_mul hk_le1 hQ_le (norm_nonneg _) zero_le_one
        _ = 2 * g.boundConst * Real.exp (-(1 / 2) * u) := one_mul _
    have hsum_eq : ∀ N : ℕ,
        (∑ k ∈ Finset.range N,
          ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u) =
        ∫ u in Set.Ioi (0 : ℝ),
          ∑ k ∈ Finset.range N, ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u := fun N =>
      (MeasureTheory.integral_finsetSum (Finset.range N) (fun k _ => hpart_int k)).symm
    simp_rw [hsum_eq]
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun u : ℝ =>
        ‖(((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
          ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u)‖)
      (fun N => (Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun k _ => (hpart_int k).aestronglyMeasurable))
      hQ_lim_int.norm ?_ ?_
    · intro N
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := hu
      have hr_lt1 : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hden_pos : 0 < 1 - Real.exp (-2 * u) := sub_pos.mpr hr_lt1
      have hgeom : ∑ k ∈ Finset.range N, ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u =
          (((1 - Real.exp (-2 * u) ^ N) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * Q u := by
        rw [← Finset.sum_mul]
        congr 1
        have hpow : ∀ k : ℕ, ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) =
            ((Real.exp (-2 * u) ^ k : ℝ) : ℂ) := fun k => by
          rw [← Real.exp_nat_mul]; congr 2; ring
        simp_rw [hpow, ← Complex.ofReal_sum]
        congr 1
        rw [geom_sum_eq hr_lt1.ne, ← neg_div_neg_eq, neg_sub, neg_sub]
      rw [hgeom, hQ_eq u, norm_mul, norm_div, Complex.norm_real, Complex.norm_real]
      have hnum_nn : 0 ≤ 1 - Real.exp (-2 * u) ^ N := by
        have : Real.exp (-2 * u) ^ N ≤ 1 := pow_le_one₀ (Real.exp_pos _).le hr_lt1.le
        linarith
      have hnum_le1 : 1 - Real.exp (-2 * u) ^ N ≤ 1 := by
        have : 0 ≤ Real.exp (-2 * u) ^ N := pow_nonneg (Real.exp_pos _).le N
        linarith
      rw [Real.norm_of_nonneg (div_nonneg hnum_nn hden_pos.le), Real.norm_of_nonneg hden_pos.le]
      calc (1 - Real.exp (-2 * u) ^ N) / (1 - Real.exp (-2 * u)) * ‖Q u‖
          ≤ 1 / (1 - Real.exp (-2 * u)) * ‖Q u‖ :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hnum_le1 hden_pos.le) (norm_nonneg _)
        _ = ‖Q u‖ / (1 - Real.exp (-2 * u)) := by ring
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := hu
      have hr_lt1 : Real.exp (-2 * u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hgeom : ∀ N : ℕ, ∑ k ∈ Finset.range N, ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) * Q u =
          (((1 - Real.exp (-2 * u) ^ N) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * Q u := fun N => by
        rw [← Finset.sum_mul]; congr 1
        have hpow : ∀ k : ℕ, ((Real.exp (-(2 * (k : ℝ)) * u) : ℝ) : ℂ) =
            ((Real.exp (-2 * u) ^ k : ℝ) : ℂ) := fun k => by
          rw [← Real.exp_nat_mul]; congr 2; ring
        simp_rw [hpow, ← Complex.ofReal_sum]
        congr 1; rw [geom_sum_eq hr_lt1.ne, ← neg_div_neg_eq, neg_sub, neg_sub]
      simp_rw [hgeom, hQ_eq u]
      have hpow_lim : Tendsto (fun N : ℕ => Real.exp (-2 * u) ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hr_lt1
      have hreal_lim : Tendsto (fun N : ℕ => (1 - Real.exp (-2 * u) ^ N) / (1 - Real.exp (-2 * u)))
          atTop (𝓝 ((1 - 0) / (1 - Real.exp (-2 * u)))) :=
        (tendsto_const_nhds.sub hpow_lim).div_const _
      rw [sub_zero] at hreal_lim
      have hC_lim := ((Complex.continuous_ofReal.tendsto _).comp hreal_lim).mul_const (Q u)
      have hlim_eq : ((1 / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * Q u =
          Q u / ((1 - Real.exp (-2 * u) : ℝ) : ℂ) := by
        push_cast; ring
      rwa [hlim_eq] at hC_lim
  exact tendsto_nhds_unique hsumm_term.hasSum.tendsto_sum_nat htend_N

/-- **Genuine Arithmetic Archimedean Distribution Term** (ZERO reference to zeros!):
`weilArchTerm f = -(log π + γ) f(0) + ∫₀^∞ (2 e^{-2u} f(0) - e^{-u/2}(f(u) + f(-u))) / (1 - e^{-2u}) du`. -/
def weilArchTerm (f : AdmissibleWeilTest) : ℂ :=
  -((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) * f.toFun 0 +
    ∫ u in Set.Ioi (0 : ℝ),
      (((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
       ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u)))

/-- **Genuine Arithmetic Weil Distribution** (defined purely on native Mathlib
`ArithmeticFunction.vonMangoldt`, `Real.log`, `Real.pi`, and `Real.eulerMascheroniConstant` —
ZERO reference to zeros of `riemannZeta`!):
`weilArithDist f = Φ(f, 1) + Φ(f, 0) - ∑' n, (Λ(n) / √n) * (f(log n) + f(-log n)) + weilArchTerm f`. -/
def weilArithDist (f : AdmissibleWeilTest) : ℂ :=
  weilPhi f 1 + weilPhi f 0 -
    (∑' n : ℕ, (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      (f.toFun (Real.log (n : ℝ)) + f.toFun (-Real.log (n : ℝ)))) +
    weilArchTerm f

/-- **Alternative Textbook Form of `weilArchTerm`** with `-(log(4π) + γ) f(0)` and `2 e^{-u} / (1 - e^{-2u}) = 1 / sinh u`. -/
theorem weilArchTerm_eq_log_four_pi_form (f : AdmissibleWeilTest) :
    weilArchTerm f =
      -((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) * f.toFun 0 +
        ∫ u in Set.Ioi (0 : ℝ),
          (((2 * Real.exp (-u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
           ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u))) := by
  have hcont_ker : Continuous (fun u : ℝ => 2 * Real.exp (-u) / (1 + Real.exp (-u))) :=
    (by fun_prop : Continuous fun u : ℝ => 2 * Real.exp (-u)).div
      (by fun_prop : Continuous fun u : ℝ => 1 + Real.exp (-u)) (fun u => by positivity)
  have hr_int : IntegrableOn (fun u : ℝ => 2 * Real.exp (-u) / (1 + Real.exp (-u))) (Set.Ioi (0 : ℝ)) := by
    refine ((integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0).const_mul 2).mono'
      hcont_ker.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hden : (1 : ℝ) ≤ 1 + Real.exp (-u) := by linarith [Real.exp_pos (-u)]
    simpa [neg_one_mul] using div_le_self (by positivity : 0 ≤ 2 * Real.exp (-u)) hden
  have hlog4 : ∫ u in Set.Ioi (0 : ℝ), 2 * Real.exp (-u) / (1 + Real.exp (-u)) = Real.log 4 := by
    let F : ℝ → ℝ := fun u => -2 * Real.log (1 + Real.exp (-u))
    have hF_deriv : ∀ u ∈ Set.Ioi (0 : ℝ),
        HasDerivAt F (2 * Real.exp (-u) / (1 + Real.exp (-u))) u := fun u _ => by
      have he : HasDerivAt (fun t : ℝ => 1 + Real.exp (-t)) (-Real.exp (-u)) u := by
        simpa using ((hasDerivAt_neg u).exp).const_add 1
      have hpos : 0 < 1 + Real.exp (-u) := by positivity
      have hlog := he.log hpos.ne'
      refine (hlog.const_mul (-2 : ℝ)).congr_deriv ?_
      field_simp [hpos.ne']
    have hF_top : Tendsto F atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => 1 + Real.exp (-u)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
      rw [add_zero] at h1
      have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
      simpa [F, Real.log_one] using h2.const_mul (-2 : ℝ)
    have hF_cont0 : ContinuousWithinAt F (Set.Ici (0 : ℝ)) 0 := by
      refine ContinuousAt.continuousWithinAt ?_
      have hpos : 0 < 1 + Real.exp (-(0 : ℝ)) := by positivity
      have h1 : ContinuousAt (fun t : ℝ => 1 + Real.exp (-t)) 0 :=
        continuousAt_const.add (Real.continuous_exp.comp continuous_neg).continuousAt
      exact continuousAt_const.mul (h1.log hpos.ne')
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hF_cont0 hF_deriv hr_int hF_top
    rw [hftc]
    dsimp only [F]
    have h0 : 1 + Real.exp (-(0 : ℝ)) = 2 := by norm_num
    rw [h0, zero_sub, neg_mul, neg_neg, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hdiff_int : IntegrableOn
      (fun u : ℝ => (((2 * Real.exp (-u) / (1 + Real.exp (-u)) : ℝ) : ℂ) * f.toFun 0))
      (Set.Ioi (0 : ℝ)) :=
    hr_int.ofReal.mul_const (f.toFun 0)
  have harch_int : IntegrableOn
      (fun u : ℝ =>
        (((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u))))
      (Set.Ioi (0 : ℝ)) := by
    have h1 := integrableOn_weilArchHalf f
    have h2 := integrableOn_weilArchHalf (weilTestReflect f)
    refine (h1.add h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
    dsimp only [Pi.add_apply, weilTestReflect]
    simp only [neg_zero]
    have hmul2 : ((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) =
        ((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) +
        ((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add]; congr 1; ring
    rw [hmul2]; ring
  have hpt_add : Set.EqOn
      (fun u : ℝ =>
        ((((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
          ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u))) +
         (((2 * Real.exp (-u) / (1 + Real.exp (-u)) : ℝ) : ℂ) * f.toFun 0)))
      (fun u : ℝ =>
        (((2 * Real.exp (-u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u))))
      (Set.Ioi (0 : ℝ)) := fun u hu => by
    have hu0 : 0 < u := hu
    have hden1 : 1 - Real.exp (-2 * u) ≠ 0 := (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
    have hden2 : 1 + Real.exp (-u) ≠ 0 := by positivity
    have hsq : Real.exp (-2 * u) = Real.exp (-u) ^ 2 := by rw [sq, ← Real.exp_add]; congr 1; ring
    have hreal : 2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) +
        2 * Real.exp (-u) / (1 + Real.exp (-u)) =
        2 * Real.exp (-u) / (1 - Real.exp (-2 * u)) := by
      have hden1' : 1 - Real.exp (-u) ^ 2 ≠ 0 := by rwa [← hsq]
      rw [hsq]
      field_simp [hden1', hden2]; ring
    dsimp only
    have hC : (((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) +
        ((2 * Real.exp (-u) / (1 + Real.exp (-u)) : ℝ) : ℂ)) =
        ((2 * Real.exp (-u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, hreal]
    linear_combination (f.toFun 0) * hC
  have hint_diff_val : ∫ u in Set.Ioi (0 : ℝ),
      (((2 * Real.exp (-u) / (1 + Real.exp (-u)) : ℝ) : ℂ) * f.toFun 0) =
      ((Real.log 4 : ℝ) : ℂ) * f.toFun 0 := by
    rw [integral_mul_const]
    have hcast : ∫ u in Set.Ioi (0 : ℝ), ((2 * Real.exp (-u) / (1 + Real.exp (-u)) : ℝ) : ℂ) =
        ((∫ u in Set.Ioi (0 : ℝ), 2 * Real.exp (-u) / (1 + Real.exp (-u)) : ℝ) : ℂ) :=
      integral_ofReal
    rw [hcast, hlog4]
  have hsum_int : (∫ u in Set.Ioi (0 : ℝ),
        (((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u)))) +
      ((Real.log 4 : ℝ) : ℂ) * f.toFun 0 =
      ∫ u in Set.Ioi (0 : ℝ),
        (((2 * Real.exp (-u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u))) := by
    rw [← hint_diff_val, ← integral_add harch_int hdiff_int]
    exact setIntegral_congr_fun measurableSet_Ioi hpt_add
  have hlog4pi : Real.log (4 * Real.pi) = Real.log 4 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_pos.ne'
  unfold weilArchTerm
  rw [hlog4pi, Complex.ofReal_add, Complex.ofReal_add, Complex.ofReal_add]
  linear_combination hsum_int

/-! ## Section 4: Hadamard Meromorphic Regularization & Rectangular Contour Shift of `(ξ'/ξ) Φ_f` -/

/-- Exact decomposition of `deriv xi s / xi s` on `Re(s) = 3/2`:
`deriv xi s / xi s = 1/s + 1/(s - 1) + deriv riemannZeta s / riemannZeta s - log(π)/2 + (1/2) digamma(s/2)`. -/
lemma logDeriv_xi_three_halves_decomp (t : ℝ) :
    logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) =
      1 / ((3 / 2 : ℂ) + I * (t : ℂ)) +
      1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1) +
      deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) -
      ((Real.log Real.pi / 2 : ℝ) : ℂ) +
      (1 / 2 : ℂ) * Complex.digamma (((3 / 2 : ℂ) + I * (t : ℂ)) / 2) := by
  set s : ℂ := (3 / 2 : ℂ) + I * (t : ℂ)
  have hs_re : s.re = 3 / 2 := by simp [s]
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs_re; norm_num at hs_re
  have hxi_ne : xi s ≠ 0 := xi_ne_zero_of_one_le_re (by linarith)
  have hdec := Stage9ExplicitFormula.negLogDerivZeta_eq_neg_logDeriv_xi_add (by linarith : -2 < s.re) hs1 hxi_ne
  have hdig : Complex.digamma (s / 2 + 1) = Complex.digamma (s / 2) + 1 / (s / 2) :=
    digamma_add_one (by simp [hs_re])
  have hinv_half : (1 / 2 : ℂ) * (1 / (s / 2)) = 1 / s := by
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs_re; norm_num at hs_re
    field_simp [hs0]
  unfold Stage3ZeroFreeRegion.negLogDerivZeta at hdec
  rw [hdig, mul_add, hinv_half] at hdec
  linear_combination hdec

/-- Integrability of `t ↦ logDeriv xi (3/2 + I * t) * weilPhi g (3/2 + I * t)` on `ℝ`. -/
lemma integrable_logDeriv_xi_mul_weilPhi (g : AdmissibleWeilTest) :
    Integrable (fun t : ℝ => logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) *
      weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
  obtain ⟨Cxi, hCxi, hxi_bd⟩ := Stage9ExplicitFormula.norm_logDeriv_xi_right_strip_le
  obtain ⟨M, hM, hphi_bd⟩ := norm_weilPhi_strip_le g
  have hcont_xi : Continuous (fun t : ℝ => logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    have hxi_an : AnalyticOnNhd ℂ xi Set.univ :=
      differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hnz : xi ((3 / 2 : ℂ) + I * (t : ℂ)) ≠ 0 := xi_ne_zero_of_one_le_re (by simp; norm_num)
    have hld : ContinuousAt (logDeriv xi) ((3 / 2 : ℂ) + I * (t : ℂ)) := by
      have hEq : logDeriv xi = fun s => deriv xi s / xi s := funext (logDeriv_apply xi)
      rw [hEq]
      exact (hxi_an _ (Set.mem_univ _)).deriv.continuousAt.div
        (hxi_an _ (Set.mem_univ _)).continuousAt hnz
    exact ContinuousAt.comp (f := fun y : ℝ => (3 / 2 : ℂ) + I * (y : ℂ)) hld (by fun_prop)
  have hcont_phi : Continuous (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      continuous_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  -- Bound `log(|t| + 2) / (1 + t^2) ≤ K t` via `K t = if |t| ≤ 1 then 6 else 6 * |t|^(-3/2)`
  let K : ℝ → ℝ := fun t => if |t| ≤ 1 then 6 else 6 * |t| ^ (-(3 / 2 : ℝ))
  have hK_int : Integrable K := by
    have hpos : IntegrableOn (fun t : ℝ => 6 * t ^ (-(3 / 2 : ℝ))) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3 / 2 : ℝ) < -1) zero_lt_one).const_mul 6
    have hneg : IntegrableOn (fun t : ℝ => 6 * (-t) ^ (-(3 / 2 : ℝ))) (Set.Iic (-1 : ℝ)) := by
      have h1 := hpos.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
      have h2 := h1.comp_neg
      rwa [Set.neg_Ici] at h2
    have hmid : IntegrableOn (fun _ : ℝ => (6 : ℝ)) (Set.Icc (-1 : ℝ) 1) :=
      integrableOn_const (hs := measure_Icc_lt_top.ne)
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (1 : ℝ)), integrableOn_union]
    constructor
    · rw [← Set.Iic_union_Ioc_eq_Iic (by norm_num : (-1 : ℝ) ≤ 1), integrableOn_union]
      constructor
      · refine hneg.congr_fun (fun t ht => ?_) measurableSet_Iic
        have ht1 : t ≤ -1 := Set.mem_Iic.mp ht
        by_cases heq : t = -1
        · subst heq; simp [K]
        · have ht_lt : t < -1 := lt_of_le_of_ne ht1 heq
          have hgt : 1 < |t| := by rw [abs_of_neg (by linarith)]; linarith
          dsimp only [K]; rw [if_neg (not_le.mpr hgt), abs_of_neg (by linarith)]
      · refine (hmid.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t ht => ?_) measurableSet_Ioc
        have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
        simp [K, habs]
    · refine hpos.congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht1 : 1 < t := Set.mem_Ioi.mp ht
      have hgt : 1 < |t| := by rw [abs_of_pos (by linarith)]; exact ht1
      dsimp only [K]; rw [if_neg (not_le.mpr hgt), abs_of_pos (by linarith)]
  refine (hK_int.const_mul (Cxi * M)).mono' (hcont_xi.mul hcont_phi).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have h1 : ‖logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ))‖ ≤ Cxi * Real.log (|t| + 2) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using hxi_bd (3 / 2) le_rfl (by norm_num) t
  have h2 := hphi_bd ((3 / 2 : ℂ) + I * (t : ℂ)) (by simp; norm_num) (by simp)
  have him : ((3 / 2 : ℂ) + I * (t : ℂ)).im = t := by simp
  rw [him] at h2
  have hlog_le : Real.log (|t| + 2) / (1 + t ^ 2) ≤ K t := by
    by_cases ht1 : |t| ≤ 1
    · dsimp only [K]; rw [if_pos ht1]
      have hl : Real.log (|t| + 2) ≤ 6 := by
        linarith [Real.log_le_sub_one_of_pos (by linarith [abs_nonneg t] : 0 < |t| + 2)]
      exact (div_le_self (Real.log_nonneg (by linarith [abs_nonneg t])) (by linarith [sq_nonneg t])).trans hl
    · push Not at ht1
      dsimp only [K]; rw [if_neg (not_le.mpr ht1)]
      have ht0 : 0 < |t| := zero_lt_one.trans ht1
      have hlog_nn : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
      have hlog : Real.log (|t| + 2) ≤ 6 * |t| ^ (1 / 2 : ℝ) := by
        have h1' : Real.log (|t| + 2) ≤ 2 * Real.sqrt (|t| + 2) := by
          have hs : 0 < Real.sqrt (|t| + 2) := Real.sqrt_pos.mpr (by linarith)
          have hl : Real.log (|t| + 2) = 2 * Real.log (Real.sqrt (|t| + 2)) := by
            rw [Real.log_sqrt (by linarith)]; ring
          linarith [Real.log_le_sub_one_of_pos hs]
        have h2' : Real.sqrt (|t| + 2) ≤ 3 * Real.sqrt |t| := by
          calc Real.sqrt (|t| + 2) ≤ Real.sqrt (9 * |t|) := Real.sqrt_le_sqrt (by linarith)
            _ = Real.sqrt (3 ^ 2 * |t|) := by norm_num
            _ = 3 * Real.sqrt |t| := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
        rw [← Real.sqrt_eq_rpow]; linarith
      have hden : |t| ^ 2 ≤ 1 + t ^ 2 := by rw [sq_abs]; linarith
      have hrew : (6 * |t| ^ (1 / 2 : ℝ)) / |t| ^ 2 = 6 * |t| ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_two |t|, mul_div_assoc, ← Real.rpow_sub ht0]; congr 2; norm_num
      calc Real.log (|t| + 2) / (1 + t ^ 2)
          ≤ (6 * |t| ^ (1 / 2 : ℝ)) / |t| ^ 2 :=
            div_le_div₀ (by positivity) hlog (sq_pos_of_pos ht0) hden
        _ = 6 * |t| ^ (-(3 / 2 : ℝ)) := hrew
  have hlog_nn0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  rw [norm_mul]
  calc ‖logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ))‖ * ‖weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))‖
      ≤ (Cxi * Real.log (|t| + 2)) * (M / (1 + t ^ 2)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hCxi.le hlog_nn0)
    _ = (Cxi * M) * (Real.log (|t| + 2) / (1 + t ^ 2)) := by ring
    _ ≤ (Cxi * M) * K t := mul_le_mul_of_nonneg_left hlog_le (by positivity)

/-- **Exact Single-Sided Right-Line Evaluation** on `Re(s) = 3/2` for any `g : AdmissibleWeilTest`:
`(1/(2π)) ∫_{-∞}^∞ (ξ'/ξ)(3/2 + it) Φ_g(3/2 + it) dt` equals the exact sum of the half-pole,
half-prime, constant, and half-archimedean terms! -/
theorem integral_logDeriv_xi_mul_weilPhi_eq (g : AdmissibleWeilTest) :
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      (∫ u in Set.Ioi (0 : ℝ), g.toFun u * ((Real.exp (-u / 2) : ℝ) : ℂ)) +
      (∫ u in Set.Ioi (0 : ℝ), g.toFun u * ((Real.exp (u / 2) : ℝ) : ℂ)) -
      (∑' n : ℕ, (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * g.toFun (Real.log (n : ℝ))) -
      (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) * g.toFun 0 +
      ∫ u in Set.Ioi (0 : ℝ),
        (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * g.toFun u) := by
  have hint_phi : Integrable (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      integrable_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  have hcont_phi : Continuous (fun t : ℝ => weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    simpa [Complex.ofReal_div, Complex.ofReal_ofNat] using
      continuous_weilPhi_vertical g (σ := 3 / 2) (by norm_num) le_rfl
  -- Integrability of each of the 5 pieces in `logDeriv_xi_three_halves_decomp`
  have hi_s : Integrable (fun t : ℝ => (1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    refine hint_phi.norm.mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact ((continuous_const.div (by fun_prop) fun t h0 => by
        have := congrArg Complex.re h0; simp at this).mul hcont_phi).aestronglyMeasurable
    · rw [norm_mul, norm_div, norm_one]
      have hge : (1 : ℝ) ≤ ‖(3 / 2 : ℂ) + I * (t : ℂ)‖ := by
        have h := Complex.abs_re_le_norm ((3 / 2 : ℂ) + I * (t : ℂ))
        have hr : ((3 / 2 : ℂ) + I * (t : ℂ)).re = 3 / 2 := by simp
        rw [hr, abs_of_pos (by norm_num)] at h; linarith
      exact mul_le_of_le_one_left (norm_nonneg _) (div_le_one_of_le₀ hge (by positivity))
  have hi_s1 : Integrable (fun t : ℝ => (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    refine (hint_phi.norm.const_mul 2).mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact ((continuous_const.div (by fun_prop) fun t h0 => by
        have := congrArg Complex.re h0; simp at this; norm_num at this).mul hcont_phi).aestronglyMeasurable
    · rw [norm_mul, norm_div, norm_one]
      have hge : (1 / 2 : ℝ) ≤ ‖((3 / 2 : ℂ) + I * (t : ℂ)) - 1‖ := by
        have h := Complex.abs_re_le_norm (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)
        have hr : (((3 / 2 : ℂ) + I * (t : ℂ)) - 1).re = 1 / 2 := by simp; norm_num
        rw [hr, abs_of_pos (by norm_num)] at h; exact h
      have hdiv : 1 / ‖((3 / 2 : ℂ) + I * (t : ℂ)) - 1‖ ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      exact mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
  have hi_zeta : Integrable (fun t : ℝ =>
      (deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    refine (hint_phi.norm.const_mul 3).mono' ?_ (Eventually.of_forall fun t => ?_)
    · have hZ_an : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ :=
        DifferentiableOn.analyticOnNhd
          (fun z (hz : z ≠ 1) => (differentiableAt_riemannZeta hz).differentiableWithinAt)
          isOpen_compl_singleton
      have hcont_z : Continuous (fun t : ℝ =>
          deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) := by
        refine continuous_iff_continuousAt.mpr fun t => ?_
        have hne1 : ((3 / 2 : ℂ) + I * (t : ℂ)) ≠ 1 := fun h => by
          have := congrArg Complex.re h; simp at this; norm_num at this
        have hnz : riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)
        have hc := (hZ_an _ hne1).deriv.continuousAt.div (hZ_an _ hne1).continuousAt hnz
        exact ContinuousAt.comp (f := fun y : ℝ => (3 / 2 : ℂ) + I * (y : ℂ)) hc (by fun_prop)
      exact (hcont_z.mul hcont_phi).aestronglyMeasurable
    · rw [norm_mul]
      have hbd := Stage5ZetaZeroFree.norm_negLogDerivZeta_of_one_lt_re (σ := 3 / 2) (by norm_num) t
      have hZ_le : ‖deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))‖ ≤ 3 := by
        have h1 : ‖Stage3ZeroFreeRegion.negLogDerivZeta (((3 / 2 : ℝ) : ℂ) + I * (t : ℂ))‖ ≤ 3 :=
          (hbd.1.trans hbd.2).trans (by norm_num)
        unfold Stage3ZeroFreeRegion.negLogDerivZeta at h1
        simpa [Complex.ofReal_div, Complex.ofReal_ofNat, norm_neg, neg_div] using h1
      exact mul_le_mul_of_nonneg_right hZ_le (norm_nonneg _)
  have hi_const : Integrable (fun t : ℝ =>
      ((Real.log Real.pi / 2 : ℝ) : ℂ) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) :=
    hint_phi.const_mul _
  have hi_dig : Integrable (fun t : ℝ =>
      ((1 / 2 : ℂ) * Complex.digamma (((3 / 2 : ℂ) + I * (t : ℂ)) / 2)) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) := by
    have hxi_int := integrable_logDeriv_xi_mul_weilPhi g
    refine ((((hxi_int.sub hi_s).sub hi_s1).sub hi_zeta).add hi_const).congr
      (Eventually.of_forall fun t => ?_)
    dsimp only [Pi.add_apply, Pi.sub_apply]
    rw [logDeriv_xi_three_halves_decomp t]; ring
  -- Rewrite the LHS using the 5-term decomposition
  have hi12 : Integrable (fun t : ℝ =>
      (1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) +
      (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) :=
    hi_s.add hi_s1
  have hi123 : Integrable (fun t : ℝ =>
      ((1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) +
       (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) +
      (deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) *
        weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) :=
    hi12.add hi_zeta
  have hi1234 : Integrable (fun t : ℝ =>
      (((1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) +
        (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) +
       (deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) *
         weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) -
      ((Real.log Real.pi / 2 : ℝ) : ℂ) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) :=
    hi123.sub hi_const
  have hsplit : (fun t : ℝ => logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) =
      fun t : ℝ =>
        ((((1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) +
           (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) +
          (deriv riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ)) / riemannZeta ((3 / 2 : ℂ) + I * (t : ℂ))) *
            weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) -
         ((Real.log Real.pi / 2 : ℝ) : ℂ) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) +
        ((1 / 2 : ℂ) * Complex.digamma (((3 / 2 : ℂ) + I * (t : ℂ)) / 2)) *
          weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) :=
    funext fun t => by rw [logDeriv_xi_three_halves_decomp t]; ring
  rw [hsplit, integral_add hi1234 hi_dig, integral_sub hi123 hi_const,
    integral_add hi12 hi_zeta, integral_add hi_s hi_s1,
    mul_add, mul_sub, mul_add, mul_add]
  -- Evaluate each of the 5 integrals!
  have e1 : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, (1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      ∫ u in Set.Ioi (0 : ℝ), g.toFun u * ((Real.exp (-u / 2) : ℝ) : ℂ) := by
    have h := integral_inv_add_I_mul_weilPhi g (c := 3 / 2) (by norm_num)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at h
    have hrew : (fun t : ℝ => (1 / ((3 / 2 : ℂ) + I * (t : ℂ))) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) =
        fun t : ℝ => ((3 / 2 : ℂ) + I * (t : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) :=
      funext fun t => by rw [one_div]
    rw [hrew, h]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    congr 2; congr 1; ring
  have e2 : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      ∫ u in Set.Ioi (0 : ℝ), g.toFun u * ((Real.exp (u / 2) : ℝ) : ℂ) := by
    have h := integral_inv_add_I_mul_weilPhi g (c := 1 / 2) (by norm_num)
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
    have hrew : (fun t : ℝ => (1 / (((3 / 2 : ℂ) + I * (t : ℂ)) - 1)) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ))) =
        fun t : ℝ => ((1 / 2 : ℂ) + I * (t : ℂ))⁻¹ * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) :=
      funext fun t => by rw [one_div]; congr 2; ring
    rw [hrew, h]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    congr 2; congr 1; ring
  have e3 := integral_logDeriv_zeta_mul_weilPhi g
  have e4 : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t : ℝ, ((Real.log Real.pi / 2 : ℝ) : ℂ) * weilPhi g ((3 / 2 : ℂ) + I * (t : ℂ)) =
      ((Real.log Real.pi / 2 : ℝ) : ℂ) * g.toFun 0 := by
    rw [integral_const_mul, mul_left_comm]
    have h0 := fourier_inversion_weilPhi_three_halves g 0
    simpa using congrArg (((Real.log Real.pi / 2 : ℝ) : ℂ) * ·) h0
  have e5 := integral_half_digamma_mul_weilPhi g
  rw [e1, e2, e3, e4, e5]
  have hc : (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) =
      ((Real.log Real.pi / 2 : ℝ) : ℂ) + ((Real.eulerMascheroniConstant / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add]; congr 1; ring
  rw [hc]; ring

/-- **Hadamard Meromorphic Regularization of `logDeriv xi` on `closedRect (-1/2) (3/2) (-T') T'`**:
for any `T' > 0` avoiding all zeros of `riemannZeta`, letting `F = {n | |(xiZeroSeq n).im| ≤ T'}`,
there exists `L : ℂ → ℂ` such that `L s - ∑ n ∈ F, 1 / (s - xiZeroSeq n)` is holomorphic on
`closedRect (-1/2) (3/2) (-T') T'`, every `xiZeroSeq n` (`n ∈ F`) lies in the open interior, and
`L s = logDeriv xi s` on the rectangle away from `{xiZeroSeq n | n ∈ F}`. -/
private lemma exists_meromorphic_logDeriv_xi_rect {T' : ℝ} (hT' : 0 < T')
    (havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → T' ≠ ρ.im ∧ -T' ≠ ρ.im) :
    let F : Finset ℕ := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T').toFinset
    ∃ L : ℂ → ℂ,
      (∀ n ∈ F, xiZeroSeq n ∈ Stage5ContourExplicit.openRect (-1 / 2) (3 / 2) (-T') T') ∧
      DifferentiableOn ℂ (fun s => L s - ∑ n ∈ F, (1 : ℂ) / (s - xiZeroSeq n))
        (Stage5ContourExplicit.closedRect (-1 / 2) (3 / 2) (-T') T') ∧
      (∀ s ∈ Stage5ContourExplicit.closedRect (-1 / 2) (3 / 2) (-T') T',
        (∀ n ∈ F, s ≠ xiZeroSeq n) → L s = logDeriv xi s) := by
  classical
  intro F
  -- Every `n ∈ F` has `|(xiZeroSeq n).im| < T'`
  have hF_open : ∀ n ∈ F, xiZeroSeq n ∈ Stage5ContourExplicit.openRect (-1 / 2) (3 / 2) (-T') T' := by
    intro n hn
    have hle : |(xiZeroSeq n).im| ≤ T' := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T').mem_toFinset.mp hn
    have hst := xiZeroSeq_strip n
    have hne := havoid (xiZeroSeq n) (xiZeroSeq_riemannZeta_zero n)
    have hlt : |(xiZeroSeq n).im| < T' := lt_of_le_of_ne hle fun hEq => by
      rcases (abs_eq hT'.le).mp hEq with hp | hn'
      · exact hne.1 hp.symm
      · exact hne.2 (by linarith)
    exact ⟨⟨by linarith [hst.1], by linarith [hst.2]⟩, abs_lt.mp hlt⟩
  -- Pick `δ ∈ (0, 1/2)` such that every `n ∉ F` has `T' + δ ≤ |(xiZeroSeq n).im|`
  set F_big : Finset ℕ := (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le (T' + 1)).toFinset
  set F_out : Finset ℕ := F_big.filter fun n => T' < |(xiZeroSeq n).im|
  obtain ⟨δ, hδ_pos, hδ_le, hδ_gap⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ n : ℕ, n ∉ F → T' + δ ≤ |(xiZeroSeq n).im| := by
    by_cases hemp : F_out = ∅
    · refine ⟨1 / 2, by norm_num, le_rfl, fun n hn => ?_⟩
      have hgt : T' < |(xiZeroSeq n).im| := by
        by_contra hle; exact hn ((Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T').mem_toFinset.mpr (not_lt.mp hle))
      by_contra hlt
      push Not at hlt
      have hmem : n ∈ F_out := Finset.mem_filter.mpr
        ⟨(Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le (T' + 1)).mem_toFinset.mpr
          (by change |(xiZeroSeq n).im| ≤ T' + 1; linarith), hgt⟩
      rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
    · have hne : F_out.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      set m : ℝ := F_out.inf' hne fun n => |(xiZeroSeq n).im| - T'
      have hm_pos : 0 < m := by
        rw [Finset.lt_inf'_iff]; intro n hn; exact sub_pos.mpr (Finset.mem_filter.mp hn).2
      refine ⟨min (1 / 2) m, lt_min (by norm_num) hm_pos, min_le_left _ _, fun n hn => ?_⟩
      have hgt : T' < |(xiZeroSeq n).im| := by
        by_contra hle; exact hn ((Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le T').mem_toFinset.mpr (not_lt.mp hle))
      by_cases hbig : |(xiZeroSeq n).im| ≤ T' + 1
      · have hmem : n ∈ F_out := Finset.mem_filter.mpr
          ⟨(Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le (T' + 1)).mem_toFinset.mpr hbig, hgt⟩
        have h1 : m ≤ |(xiZeroSeq n).im| - T' := Finset.inf'_le (fun k => |(xiZeroSeq k).im| - T') hmem
        have h2 : min (1 / 2) m ≤ m := min_le_right _ _
        linarith
      · push Not at hbig
        have h1 : min (1 / 2) m ≤ 1 / 2 := min_le_left _ _
        linarith
  -- Open neighborhood `U` of `closedRect (-1/2) (3/2) (-T') T'`
  set U : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < 2 ∧ |z.im| < T' + δ / 2}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hrect_sub : Stage5ContourExplicit.closedRect (-1 / 2) (3 / 2) (-T') T' ⊆ U := fun z hz =>
    ⟨by linarith [hz.1.1], by linarith [hz.1.2], by have := abs_le.mpr hz.2; linarith⟩
  have hU_norm : ∀ s ∈ U, ‖s‖ ≤ T' + 3 := fun s hs => by
    have htri := Complex.norm_le_abs_re_add_abs_im s
    have hre : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2.1.le⟩
    linarith [hs.2.2]
  have hU_sep : ∀ s ∈ U, ∀ n : ℕ, n ∉ F → δ / 2 ≤ ‖s - xiZeroSeq n‖ := fun s hs n hn => by
    have h1 := hδ_gap n hn
    have h2 : δ / 2 ≤ |s.im - (xiZeroSeq n).im| := by
      have habs := abs_abs_sub_abs_le_abs_sub (xiZeroSeq n).im s.im
      rw [abs_sub_comm (xiZeroSeq n).im s.im] at habs
      have hpos : δ / 2 ≤ |(xiZeroSeq n).im| - |s.im| := by linarith [hs.2.2]
      exact hpos.trans ((le_abs_self _).trans habs)
    exact h2.trans (by simpa using Complex.abs_im_le_norm (s - xiZeroSeq n))
  -- Define the holomorphic tail `H` via `Complex.differentiableOn_tsum_of_summable_norm`
  let term : ℕ → ℂ → ℂ := fun n s =>
    if n ∈ F then 0 else 1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n
  set C_u : ℝ := 2 * (T' + 3) + 4 * (T' + 3) ^ 2 / δ
  let u : ℕ → ℝ := fun n => C_u * (‖xiZeroSeq n‖ ^ 2)⁻¹
  have hu_summ : Summable u := xiZeroSeq_summable_inv_sq.mul_left C_u
  have hterm_diff : ∀ n : ℕ, DifferentiableOn ℂ (term n) U := fun n => by
    dsimp only [term]
    by_cases hn : n ∈ F
    · simp only [hn, ↓reduceIte]; exact differentiableOn_const 0
    · simp only [hn, ↓reduceIte]
      refine (differentiableOn_const (1 : ℂ)).div
        (differentiableOn_id.sub (differentiableOn_const _)) (fun s hs h0 => ?_) |>.add
        (differentiableOn_const _)
      have hsep := hU_sep s hs n hn
      dsimp only [Pi.sub_apply, id_eq] at h0
      rw [h0, norm_zero] at hsep; linarith
  have hterm_bd : ∀ n : ℕ, ∀ s ∈ U, ‖term n s‖ ≤ u n := fun n s hs => by
    dsimp only [term, u]
    by_cases hn : n ∈ F
    · simp only [hn, ↓reduceIte, norm_zero]
      have hCu : 0 ≤ C_u := by dsimp only [C_u]; positivity
      positivity
    · simp only [hn, ↓reduceIte]
      have hsep := hU_sep s hs n hn
      have hsub_ne : s - xiZeroSeq n ≠ 0 := fun h => by rw [h, norm_zero] at hsep; linarith
      have hρ_ne := xiZeroSeq_ne_zero n
      have hρ_pos : 0 < ‖xiZeroSeq n‖ := norm_pos_iff.mpr hρ_ne
      have hident : 1 / (s - xiZeroSeq n) + 1 / xiZeroSeq n = s / ((s - xiZeroSeq n) * xiZeroSeq n) := by
        field_simp [hsub_ne, hρ_ne]; ring
      rw [hident, norm_div, norm_mul]
      have hsn := hU_norm s hs
      by_cases hbig : 2 * (T' + 3) ≤ ‖xiZeroSeq n‖
      · have hsub_ge : ‖xiZeroSeq n‖ / 2 ≤ ‖s - xiZeroSeq n‖ := by
          have htri := norm_sub_norm_le (xiZeroSeq n) s
          rw [norm_sub_rev] at htri; linarith
        have hprod : ‖xiZeroSeq n‖ ^ 2 / 2 ≤ ‖s - xiZeroSeq n‖ * ‖xiZeroSeq n‖ := by
          have := mul_le_mul_of_nonneg_right hsub_ge hρ_pos.le
          linarith [show ‖xiZeroSeq n‖ / 2 * ‖xiZeroSeq n‖ = ‖xiZeroSeq n‖ ^ 2 / 2 by ring]
        calc ‖s‖ / (‖s - xiZeroSeq n‖ * ‖xiZeroSeq n‖)
            ≤ (T' + 3) / (‖xiZeroSeq n‖ ^ 2 / 2) :=
              div_le_div₀ (by positivity) hsn (by positivity) hprod
          _ = 2 * (T' + 3) * (‖xiZeroSeq n‖ ^ 2)⁻¹ := by field_simp [hρ_pos.ne']
          _ ≤ C_u * (‖xiZeroSeq n‖ ^ 2)⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              dsimp only [C_u]; linarith [show (0 : ℝ) ≤ 4 * (T' + 3) ^ 2 / δ by positivity]
      · push Not at hbig
        have hprod : (δ / 2) * ‖xiZeroSeq n‖ ≤ ‖s - xiZeroSeq n‖ * ‖xiZeroSeq n‖ :=
          mul_le_mul_of_nonneg_right hsep hρ_pos.le
        calc ‖s‖ / (‖s - xiZeroSeq n‖ * ‖xiZeroSeq n‖)
            ≤ (T' + 3) / ((δ / 2) * ‖xiZeroSeq n‖) :=
              div_le_div₀ (by positivity) hsn (by positivity) hprod
          _ = (2 * (T' + 3) / δ) * (‖xiZeroSeq n‖ * (‖xiZeroSeq n‖ ^ 2)⁻¹) := by
              field_simp [hδ_pos.ne', hρ_pos.ne']
          _ ≤ (2 * (T' + 3) / δ) * ((2 * (T' + 3)) * (‖xiZeroSeq n‖ ^ 2)⁻¹) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbig.le (by positivity))
                (by positivity)
          _ = (4 * (T' + 3) ^ 2 / δ) * (‖xiZeroSeq n‖ ^ 2)⁻¹ := by ring
          _ ≤ C_u * (‖xiZeroSeq n‖ ^ 2)⁻¹ := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              dsimp only [C_u]; linarith
  let H : ℂ → ℂ := fun s =>
    xiHadamardB + (∑ n ∈ F, (1 : ℂ) / xiZeroSeq n) + ∑' n : ℕ, term n s
  have hH_diff : DifferentiableOn ℂ H U :=
    (differentiableOn_const _).add
      (Complex.differentiableOn_tsum_of_summable_norm hu_summ hterm_diff hU_open hterm_bd)
  let L : ℂ → ℂ := fun s => H s + ∑ n ∈ F, (1 : ℂ) / (s - xiZeroSeq n)
  refine ⟨L, hF_open, ?_, ?_⟩
  · have hEq : (fun s => L s - ∑ n ∈ F, (1 : ℂ) / (s - xiZeroSeq n)) = H :=
      funext fun s => by dsimp only [L]; ring
    rw [hEq]
    exact hH_diff.mono hrect_sub
  · intro s hs hsF
    have hsU : s ∈ U := hrect_sub hs
    have hs_all : ∀ n : ℕ, s ≠ xiZeroSeq n := fun n => by
      by_cases hn : n ∈ F
      · exact hsF n hn
      · intro hEq; have hsep := hU_sep s hsU n hn; rw [hEq, sub_self, norm_zero] at hsep; linarith
    have hxi_ne : xi s ≠ 0 := fun h0 => by
      obtain ⟨n, hn⟩ := isMultiplicityZeroSeq_xi.exists_of_eq_zero differentiable_xi (by simp) h0
      exact hs_all n hn.symm
    rw [logDeriv_apply, xi_logDeriv_hadamard s hxi_ne]
    have hsumm := Stage5JensenHadamard.summable_hadamard_term xiZeroSeq_ne_zero xiZeroSeq_summable_inv_sq hs_all
    have hsplit := hsumm.sum_add_tsum_compl (s := F)
    have hcompl : (∑' x : ↥(F : Set ℕ)ᶜ, (1 / (s - xiZeroSeq x.1) + 1 / xiZeroSeq x.1)) =
        ∑' n : ℕ, term n s := by
      rw [← tsum_subtype_eq_of_support_subset (s := (F : Set ℕ)ᶜ) (f := fun n => term n s)]
      · refine tsum_congr fun x => ?_
        have hx : x.1 ∉ F := x.2
        simp [term, hx]
      · intro n hn
        simp only [Function.mem_support, term, ne_eq, ite_eq_left_iff, not_forall] at hn
        exact hn.1
    rw [← hsplit, hcompl, Finset.sum_add_distrib]
    dsimp only [L, H]
    ring

/-! ## Section 5: Unconditional Weil Explicit Formula on Native `riemannZeta` & `vonMangoldt` -/

/-- **MASTER CONTOUR-SHIFT IDENTITY FOR `weilPhi`**:
for every `f : AdmissibleWeilTest`,
`∑' n, weilPhi f (xiZeroSeq n)
  = (1 / (2π)) ∫_{-∞}^∞ logDeriv xi (3/2 + I * t) * (weilPhi f (3/2 + I * t) + weilPhi (weilTestReflect f) (3/2 + I * t)) dt`. -/
theorem tsum_weilPhi_xiZeroSeq_eq_vertical_integrals (f : AdmissibleWeilTest) :
    (∑' n : ℕ, weilPhi f (xiZeroSeq n)) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((3 / 2 : ℂ) + I * (t : ℂ))) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) *
          weilPhi (weilTestReflect f) ((3 / 2 : ℂ) + I * (t : ℂ))) := by
  classical
  obtain ⟨c_gap, hc_gap, C_h, hCh_pos, hgood⟩ := Stage9ExplicitFormula.exists_good_contour_height
  obtain ⟨Cd, hCd_pos, hdig_bd⟩ := Stage9ExplicitFormula.norm_digamma_strip_le
  obtain ⟨M, hM, hphi_bd⟩ := norm_weilPhi_strip_le f
  -- Pick a sequence of good heights `T' k ∈ [k + 4, k + 5]`
  have hex_k : ∀ k : ℕ, ∃ T' ∈ Set.Icc ((k : ℝ) + 4) ((k : ℝ) + 5),
      (∀ ρ : ℂ, riemannZeta ρ = 0 →
        c_gap / Real.log ((k : ℝ) + 4) ≤ |T' - ρ.im| ∧
        c_gap / Real.log ((k : ℝ) + 4) ≤ |(-T') - ρ.im|) ∧
      (∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
        ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) + I * (T' : ℂ))‖ ≤ C_h * (Real.log ((k : ℝ) + 4)) ^ 2 ∧
        ‖Stage3ZeroFreeRegion.negLogDerivZeta ((σ : ℂ) - I * (T' : ℂ))‖ ≤ C_h * (Real.log ((k : ℝ) + 4)) ^ 2) :=
    fun k => by
      have hk4 : (4 : ℝ) ≤ (k : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      simpa only [show ((k : ℝ) + 4) + 1 = (k : ℝ) + 5 by ring] using hgood ((k : ℝ) + 4) hk4
  choose T' hT'_mem hT'_gap hT'_bd using hex_k
  let Fset : ℕ → Finset ℕ := fun k => (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le (T' k)).toFinset
  let Rint : ℕ → ℂ := fun k =>
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in (-(T' k))..(T' k), logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((3 / 2 : ℂ) + I * (t : ℂ))
  let Lint : ℕ → ℂ := fun k =>
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in (-(T' k))..(T' k), logDeriv xi ((-1 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((-1 / 2 : ℂ) + I * (t : ℂ))
  let TopInt : ℕ → ℂ := fun k =>
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), logDeriv xi ((σ : ℂ) + I * (T' k : ℂ)) * weilPhi f ((σ : ℂ) + I * (T' k : ℂ))
  let BotInt : ℕ → ℂ := fun k =>
    (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), logDeriv xi ((σ : ℂ) - I * (T' k : ℂ)) * weilPhi f ((σ : ℂ) - I * (T' k : ℂ))
  -- Exact contour-shift identity at height `T' k`
  have hshift_k : ∀ k : ℕ,
      ∑ n ∈ Fset k, weilPhi f (xiZeroSeq n) = Rint k - Lint k - TopInt k + BotInt k := fun k => by
    have hTk_ge : (k : ℝ) + 4 ≤ T' k := (hT'_mem k).1
    have hTk_pos : 0 < T' k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hlogTk_pos : 0 < Real.log ((k : ℝ) + 4) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have havoid : ∀ ρ : ℂ, riemannZeta ρ = 0 → T' k ≠ ρ.im ∧ -(T' k) ≠ ρ.im := fun ρ hρ => by
      have hg := hT'_gap k ρ hρ
      have hpos : 0 < c_gap / Real.log ((k : ℝ) + 4) := div_pos hc_gap hlogTk_pos
      exact ⟨fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.1],
             fun h => by rw [h, sub_self, abs_zero] at hg; linarith [hg.2]⟩
    obtain ⟨L, hF_open, hL_diff, hL_eq⟩ := exists_meromorphic_logDeriv_xi_rect hTk_pos havoid
    have hW_diff : DifferentiableOn ℂ (weilPhi f)
        (Stage5ContourExplicit.closedRect (-1 / 2) (3 / 2) (-(T' k)) (T' k)) :=
      (differentiableOn_weilPhi f).mono fun s hs => by
        change |s.re - 1 / 2| < f.decayRate
        have h1 : |s.re - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
        exact h1.trans_lt f.decayRate_gt
    have hshift := Stage5ContourExplicit.vertical_contour_shift_mul_eq_sum_residues
      L (weilPhi f) (by norm_num : (-1 / 2 : ℝ) < 3 / 2) hTk_pos (Fset k) xiZeroSeq (fun _ => 1)
      hF_open hL_diff hW_diff
    have hR : ∫ t in (-(T' k))..(T' k), L (((3 / 2 : ℝ) : ℂ) + I * (t : ℂ)) * weilPhi f (((3 / 2 : ℝ) : ℂ) + I * (t : ℂ)) =
        ∫ t in (-(T' k))..(T' k), logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((3 / 2 : ℂ) + I * (t : ℂ)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      have hEq := hL_eq (((3 / 2 : ℝ) : ℂ) + I * (t : ℂ)) ⟨⟨by simp; norm_num, by simp⟩, by simpa using ht⟩
        fun n hn h0 => by have := (hF_open n hn).1.2; rw [← h0] at this; simp at this
      rw [hEq]; simp [Complex.ofReal_div, Complex.ofReal_ofNat]
    have hL' : ∫ t in (-(T' k))..(T' k), L (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) * weilPhi f (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) =
        ∫ t in (-(T' k))..(T' k), logDeriv xi ((-1 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((-1 / 2 : ℂ) + I * (t : ℂ)) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith)] at ht
      have hEq := hL_eq (((-1 / 2 : ℝ) : ℂ) + I * (t : ℂ)) ⟨⟨by simp, by simp; norm_num⟩, by simpa using ht⟩
        fun n hn h0 => by have := (hF_open n hn).1.1; rw [← h0] at this; simp at this
      rw [hEq]; simp [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
    have hTop : ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), L ((σ : ℂ) + I * (T' k : ℂ)) * weilPhi f ((σ : ℂ) + I * (T' k : ℂ)) =
        ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), logDeriv xi ((σ : ℂ) + I * (T' k : ℂ)) * weilPhi f ((σ : ℂ) + I * (T' k : ℂ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      have hEq := hL_eq ((σ : ℂ) + I * (T' k : ℂ)) ⟨by simpa using hσ, by simp [hTk_pos.le]⟩
        fun n hn h0 => by have := (hF_open n hn).2.2; rw [← h0] at this; simp at this
      rw [hEq]
    have hBot : ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), L ((σ : ℂ) - I * (T' k : ℂ)) * weilPhi f ((σ : ℂ) - I * (T' k : ℂ)) =
        ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), logDeriv xi ((σ : ℂ) - I * (T' k : ℂ)) * weilPhi f ((σ : ℂ) - I * (T' k : ℂ)) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le (by norm_num)] at hσ
      have hEq := hL_eq ((σ : ℂ) - I * (T' k : ℂ)) ⟨by simpa using hσ, by simp [hTk_pos.le]⟩
        fun n hn h0 => by have := (hF_open n hn).2.1; rw [← h0] at this; simp at this
      rw [hEq]
    simp only [one_mul] at hshift
    rw [hR, hL', hTop, hBot] at hshift
    dsimp only [Rint, Lint, TopInt, BotInt]
    linear_combination -hshift
  -- Limit 1: Residue sum `∑ n ∈ Fset k, weilPhi f (xiZeroSeq n) → ∑' n, weilPhi f (xiZeroSeq n)`
  have hT'_top : Tendsto T' atTop atTop :=
    tendsto_atTop_mono (fun k => (hT'_mem k).1) (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hF_top : Tendsto Fset atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro s
    refine ⟨s.sup (fun n => ⌈|(xiZeroSeq n).im|⌉₊), fun k hk n hn => ?_⟩
    refine (Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le (T' k)).mem_toFinset.mpr ?_
    change |(xiZeroSeq n).im| ≤ T' k
    have h1 : |(xiZeroSeq n).im| ≤ (⌈|(xiZeroSeq n).im|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈|(xiZeroSeq n).im|⌉₊ ≤ k := (Finset.le_sup (f := fun m => ⌈|(xiZeroSeq m).im|⌉₊) hn).trans hk
    have h3 : (⌈|(xiZeroSeq n).im|⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
    linarith [(hT'_mem k).1]
  have hlim_res : Tendsto (fun k => ∑ n ∈ Fset k, weilPhi f (xiZeroSeq n)) atTop
      (𝓝 (∑' n : ℕ, weilPhi f (xiZeroSeq n))) :=
    (summable_weilPhi_xiZeroSeq f).hasSum.comp hF_top
  -- Limit 2: Right vertical integral `Rint k → (1/(2π)) ∫ t, logDeriv xi (3/2 + I * t) * weilPhi f (3/2 + I * t)`
  have hlim_R : Tendsto Rint atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((3 / 2 : ℂ) + I * (t : ℂ)))) := by
    have hint := integrable_logDeriv_xi_mul_weilPhi f
    exact (intervalIntegral_tendsto_integral hint (tendsto_neg_atTop_atBot.comp hT'_top) hT'_top).const_mul _
  -- Limit 3: Left vertical integral `-Lint k → (1/(2π)) ∫ t, logDeriv xi (3/2 + I * t) * weilPhi (weilTestReflect f) (3/2 + I * t)`
  have hL_eq_neg : ∀ k : ℕ, -Lint k =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-(T' k))..(T' k),
          logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi (weilTestReflect f) ((3 / 2 : ℂ) + I * (t : ℂ)) := fun k => by
    dsimp only [Lint]
    rw [← mul_neg, ← intervalIntegral.integral_neg]
    congr 1
    have hcomp := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) *
        weilPhi (weilTestReflect f) ((3 / 2 : ℂ) + I * (t : ℂ)))
      (a := -(T' k)) (b := T' k)
    simp only [neg_neg] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have h1sub : (1 : ℂ) - ((-1 / 2 : ℂ) + I * (t : ℂ)) = (3 / 2 : ℂ) + I * ((-t : ℝ) : ℂ) := by
      push_cast; ring
    have hxi_sym : -(logDeriv xi ((-1 / 2 : ℂ) + I * (t : ℂ))) =
        logDeriv xi ((3 / 2 : ℂ) + I * ((-t : ℝ) : ℂ)) := by
      rw [logDeriv_apply, logDeriv_apply, ← h1sub, Stage7HadamardXiProduct.logDeriv_xi_one_sub]
    have hphi_sym : weilPhi f ((-1 / 2 : ℂ) + I * (t : ℂ)) =
        weilPhi (weilTestReflect f) ((3 / 2 : ℂ) + I * ((-t : ℝ) : ℂ)) := by
      have harg : (-1 / 2 : ℂ) + I * (t : ℂ) = 1 - ((3 / 2 : ℂ) + I * ((-t : ℝ) : ℂ)) := by
        push_cast; ring
      rw [harg, weilPhi_one_sub]
    rw [← neg_mul, hxi_sym, hphi_sym]
  have hlim_L : Tendsto (fun k => -Lint k) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) *
          weilPhi (weilTestReflect f) ((3 / 2 : ℂ) + I * (t : ℂ)))) := by
    simp_rw [hL_eq_neg]
    have hint := integrable_logDeriv_xi_mul_weilPhi (weilTestReflect f)
    exact (intervalIntegral_tendsto_integral hint (tendsto_neg_atTop_atBot.comp hT'_top) hT'_top).const_mul _
  -- Limit 4: Horizontal integrals `TopInt k → 0` and `BotInt k → 0`
  have hhoriz_zero : ∀ sg : Bool,
      Tendsto (fun k : ℕ =>
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
            logDeriv xi ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) *
              weilPhi f ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))))
        atTop (𝓝 0) := fun sg => by
    set C_tot : ℝ := 2 * M * (C_h + Cd + 2 + Real.log Real.pi)
    have hC_tot : 0 ≤ C_tot := by
      have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
      positivity
    have hlim_bd : Tendsto (fun k : ℕ => C_tot * ((Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun R : ℝ => (1 * (R + 2) * (Real.log (R + 2)) ^ 2 + 0) / R ^ 2) atTop (𝓝 0) :=
        Stage7HadamardXiProduct.tendsto_mul_log_sq_div_sq_atTop 1 0
      have hcomp := (h1.comp (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (4 : ℝ))))).const_mul C_tot
      rw [mul_zero] at hcomp
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) hcomp
      refine mul_le_mul_of_nonneg_left ?_ hC_tot
      have hk4 : (4 : ℝ) ≤ (k : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hlog_le : Real.log ((k : ℝ) + 4) ≤ Real.log (((k : ℝ) + 4) + 2) :=
        Real.log_le_log (by linarith) (by linarith)
      have hlog_nn : 0 ≤ Real.log ((k : ℝ) + 4) := Real.log_nonneg (by linarith)
      have hsq : (Real.log ((k : ℝ) + 4)) ^ 2 ≤ (Real.log (((k : ℝ) + 4) + 2)) ^ 2 :=
        pow_le_pow_left₀ hlog_nn hlog_le 2
      have hnum : (Real.log ((k : ℝ) + 4)) ^ 2 ≤
          1 * (((k : ℝ) + 4) + 2) * (Real.log (((k : ℝ) + 4) + 2)) ^ 2 + 0 := by
        nlinarith [sq_nonneg (Real.log (((k : ℝ) + 4) + 2))]
      exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
    refine squeeze_zero_norm (fun k => ?_) hlim_bd
    have hk4 : (4 : ℝ) ≤ (k : ℝ) + 4 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hTk_ge : (k : ℝ) + 4 ≤ T' k := (hT'_mem k).1
    have hTk_le : T' k ≤ (k : ℝ) + 5 := (hT'_mem k).2
    have hTk_pos : 0 < T' k := by linarith
    have hlog_gt1 : 1 < Real.log ((k : ℝ) + 4) := by
      have : Real.exp 1 < (k : ℝ) + 4 := by linarith [Real.exp_one_lt_d9]
      exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
    have hlog_sq : Real.log ((k : ℝ) + 4) ≤ (Real.log ((k : ℝ) + 4)) ^ 2 := by nlinarith
    have harg_eq : ∀ σ : ℝ,
        (σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)) =
        if sg then (σ : ℂ) + I * (T' k : ℂ) else (σ : ℂ) - I * (T' k : ℂ) := fun σ => by
      cases sg <;> simp [sub_eq_add_neg]
    have hpt : ∀ σ ∈ Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ),
        ‖logDeriv xi ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) *
          weilPhi f ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)))‖ ≤
          (C_tot / 2) * ((Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) := fun σ hσ => by
      set s : ℂ := (σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))
      have hs_re : s.re = σ := by dsimp only [s]; rw [harg_eq σ]; cases sg <;> simp
      have hs_im : s.im = if sg then T' k else -(T' k) := by dsimp only [s]; rw [harg_eq σ]; cases sg <;> simp
      have hs_im_abs : |s.im| = T' k := by rw [hs_im]; cases sg <;> simp [abs_of_pos hTk_pos]
      have hs1 : s ≠ 1 := fun h => by
        have := congrArg Complex.im h; simp at this; rw [this, abs_zero] at hs_im_abs; linarith
      have hxi_ne : xi s ≠ 0 := fun h0 => by
        have hζ : riemannZeta s = 0 := ((xi_eq_zero_iff_critical_strip_zeta_zero s).mp h0).2.2
        have hg := hT'_gap k s hζ
        have hpos : 0 < c_gap / Real.log ((k : ℝ) + 4) := div_pos hc_gap (zero_lt_one.trans hlog_gt1)
        rw [hs_im] at hg
        cases sg
        · simp only [Bool.false_eq_true, ↓reduceIte, sub_self, abs_zero] at hg; linarith [hg.2]
        · simp only [↓reduceIte, sub_self, abs_zero] at hg; linarith [hg.1]
      have hdec := Stage9ExplicitFormula.negLogDerivZeta_eq_neg_logDeriv_xi_add
        (by linarith [hσ.1] : -2 < s.re) hs1 hxi_ne
      have hld_eq : logDeriv xi s =
          -Stage3ZeroFreeRegion.negLogDerivZeta s + 1 / (s - 1) -
            ((Real.log Real.pi / 2 : ℝ) : ℂ) + (1 / 2 : ℂ) * Complex.digamma (s / 2 + 1) := by
        linear_combination hdec
      have hZ_bd : ‖Stage3ZeroFreeRegion.negLogDerivZeta s‖ ≤ C_h * (Real.log ((k : ℝ) + 4)) ^ 2 := by
        dsimp only [s]; rw [harg_eq σ]
        cases sg
        · exact (hT'_bd k σ (by linarith [hσ.1]) (by linarith [hσ.2])).2
        · exact (hT'_bd k σ (by linarith [hσ.1]) (by linarith [hσ.2])).1
      have hsub_bd : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
        rw [norm_div, norm_one]
        have hden : 1 ≤ ‖s - 1‖ := by
          have h := Complex.abs_im_le_norm (s - 1)
          have him : (s - 1).im = s.im := by simp
          rw [him, hs_im_abs] at h; linarith
        exact div_le_one_of_le₀ hden (by linarith)
      have hdig : ‖Complex.digamma (s / 2 + 1)‖ ≤ 2 * Cd * Real.log ((k : ℝ) + 4) := by
        have h1 := hdig_bd (s / 2 + 1) (by simp [hs_re]; linarith [hσ.1]) (by simp [hs_re]; linarith [hσ.2])
        have him2 : |(s / 2 + 1).im| + 2 ≤ ((k : ℝ) + 4) ^ 2 := by
          have : (s / 2 + 1).im = s.im / 2 := by simp
          rw [this, abs_div, show |(2 : ℝ)| = 2 by norm_num, hs_im_abs]; nlinarith
        have hl : Real.log (|(s / 2 + 1).im| + 2) ≤ 2 * Real.log ((k : ℝ) + 4) := by
          calc Real.log (|(s / 2 + 1).im| + 2) ≤ Real.log (((k : ℝ) + 4) ^ 2) :=
                Real.log_le_log (by positivity) him2
            _ = 2 * Real.log ((k : ℝ) + 4) := by rw [Real.log_pow]; norm_num
        exact (h1.trans (mul_le_mul_of_nonneg_left hl hCd_pos.le)).trans_eq (by ring)
      have hpi_nn : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.two_le_pi])
      have hld_bd : ‖logDeriv xi s‖ ≤ (C_h + Cd + 2 + Real.log Real.pi) * (Real.log ((k : ℝ) + 4)) ^ 2 := by
        rw [hld_eq]
        have t1 := norm_add_le (-Stage3ZeroFreeRegion.negLogDerivZeta s + 1 / (s - 1) -
            ((Real.log Real.pi / 2 : ℝ) : ℂ)) ((1 / 2 : ℂ) * Complex.digamma (s / 2 + 1))
        have t2 := norm_sub_le (-Stage3ZeroFreeRegion.negLogDerivZeta s + 1 / (s - 1))
            ((Real.log Real.pi / 2 : ℝ) : ℂ)
        have t3 := norm_add_le (-Stage3ZeroFreeRegion.negLogDerivZeta s) (1 / (s - 1))
        rw [norm_neg] at t3
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)] at t2
        rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num] at t1
        have h1_le : (1 : ℝ) ≤ (Real.log ((k : ℝ) + 4)) ^ 2 := by nlinarith
        nlinarith
      have hphi_s : ‖weilPhi f s‖ ≤ M / ((k : ℝ) + 4) ^ 2 := by
        have h1 := hphi_bd s (by linarith [hσ.1]) (by linarith [hσ.2])
        refine h1.trans (div_le_div_of_nonneg_left hM (by positivity) ?_)
        have hsq : ((k : ℝ) + 4) ^ 2 ≤ s.im ^ 2 := by
          rw [← sq_abs s.im, hs_im_abs]; exact pow_le_pow_left₀ (by linarith) hTk_ge 2
        linarith
      rw [norm_mul]
      calc ‖logDeriv xi s‖ * ‖weilPhi f s‖
          ≤ ((C_h + Cd + 2 + Real.log Real.pi) * (Real.log ((k : ℝ) + 4)) ^ 2) * (M / ((k : ℝ) + 4) ^ 2) :=
            mul_le_mul hld_bd hphi_s (norm_nonneg _) (by positivity)
        _ = (C_tot / 2) * ((Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) := by
            dsimp only [C_tot]; ring
    -- Continuity of integrand on `[-1/2, 3/2]`
    have hcont_H : ContinuousOn (fun σ : ℝ =>
        logDeriv xi ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) *
          weilPhi f ((σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))))
        (Set.Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) := by
      have hxi_an : AnalyticOnNhd ℂ xi Set.univ :=
        differentiable_xi.differentiableOn.analyticOnNhd isOpen_univ
      intro σ hσ
      set s : ℂ := (σ : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))
      have hs_im : s.im = if sg then T' k else -(T' k) := by dsimp only [s]; rw [harg_eq σ]; cases sg <;> simp
      have hxi_ne : xi s ≠ 0 := fun h0 => by
        have hζ : riemannZeta s = 0 := ((xi_eq_zero_iff_critical_strip_zeta_zero s).mp h0).2.2
        have hg := hT'_gap k s hζ
        have hpos : 0 < c_gap / Real.log ((k : ℝ) + 4) := div_pos hc_gap (zero_lt_one.trans hlog_gt1)
        rw [hs_im] at hg
        cases sg
        · simp only [Bool.false_eq_true, ↓reduceIte, sub_self, abs_zero] at hg; linarith [hg.2]
        · simp only [↓reduceIte, sub_self, abs_zero] at hg; linarith [hg.1]
      have hld : ContinuousAt (logDeriv xi) s := by
        have hEq : logDeriv xi = fun w => deriv xi w / xi w := funext (logDeriv_apply xi)
        rw [hEq]
        exact (hxi_an _ (Set.mem_univ _)).deriv.continuousAt.div
          (hxi_an _ (Set.mem_univ _)).continuousAt hxi_ne
      have hphi_at : ContinuousAt (weilPhi f) s := by
        have hopen : IsOpen {w : ℂ | |w.re - 1 / 2| < f.decayRate} :=
          isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const
        have hmem : s ∈ {w : ℂ | |w.re - 1 / 2| < f.decayRate} := by
          change |s.re - 1 / 2| < f.decayRate
          have hs_re : s.re = σ := by dsimp only [s]; rw [harg_eq σ]; cases sg <;> simp
          have h1 : |σ - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
          rw [hs_re]; exact h1.trans_lt f.decayRate_gt
        exact ((differentiableOn_weilPhi f).differentiableAt (hopen.mem_nhds hmem)).continuousAt
      have hc1 : ContinuousAt (fun x : ℝ => logDeriv xi ((x : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)))) σ :=
        ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) hld (by fun_prop)
      have hc2 : ContinuousAt (fun x : ℝ => weilPhi f ((x : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ)))) σ :=
        ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (if sg then 1 else -1 : ℂ) * (I * (T' k : ℂ))) hphi_at (by fun_prop)
      exact (hc1.mul hc2).continuousWithinAt
    have h2pi_ge1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    calc (2 * Real.pi)⁻¹ * ‖∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), _‖
        ≤ 1 * ∫ σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ), ‖_‖ :=
          mul_le_mul (inv_le_one_of_one_le₀ h2pi_ge1)
            (intervalIntegral.norm_integral_le_integral_norm (by norm_num)) (norm_nonneg _) zero_le_one
      _ ≤ ∫ _σ in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
            ((C_tot / 2) * ((Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2)) := by
          rw [one_mul]
          exact intervalIntegral.integral_mono_on (by norm_num)
            (hcont_H.mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable.norm
            intervalIntegrable_const hpt
      _ = C_tot * ((Real.log ((k : ℝ) + 4)) ^ 2 / ((k : ℝ) + 4) ^ 2) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hlim_top : Tendsto TopInt atTop (𝓝 0) := by
    simpa [TopInt] using hhoriz_zero true
  have hlim_bot : Tendsto BotInt atTop (𝓝 0) := by
    simpa [BotInt, sub_eq_add_neg] using hhoriz_zero false
  have hlim_rhs : Tendsto (fun k => Rint k + -Lint k - TopInt k + BotInt k) atTop
      (𝓝 (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) * weilPhi f ((3 / 2 : ℂ) + I * (t : ℂ))) +
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t : ℝ, logDeriv xi ((3 / 2 : ℂ) + I * (t : ℂ)) *
          weilPhi (weilTestReflect f) ((3 / 2 : ℂ) + I * (t : ℂ))) - 0 + 0)) :=
    (((hlim_R.add hlim_L).sub hlim_top).add hlim_bot)
  rw [sub_zero, add_zero] at hlim_rhs
  have hlim_eq : (fun k => ∑ n ∈ Fset k, weilPhi f (xiZeroSeq n)) =
      fun k => Rint k + -Lint k - TopInt k + BotInt k :=
    funext fun k => by rw [hshift_k k]; ring
  rw [hlim_eq] at hlim_res
  exact tendsto_nhds_unique hlim_res hlim_rhs

/-- **UNCONDITIONAL WEIL EXPLICIT FORMULA (`xiZeroSeq` form)**:
for EVERY `f : AdmissibleWeilTest`, the purely arithmetic prime + archimedean distribution
`weilArithDist f` equals the spectral zero sum `∑' n, weilPhi f (xiZeroSeq n)`. -/
theorem weil_explicit_formula_xiZeroSeq (f : AdmissibleWeilTest) :
    weilArithDist f = ∑' n : ℕ, weilPhi f (xiZeroSeq n) := by
  rw [tsum_weilPhi_xiZeroSeq_eq_vertical_integrals f,
    integral_logDeriv_xi_mul_weilPhi_eq f,
    integral_logDeriv_xi_mul_weilPhi_eq (weilTestReflect f)]
  -- Combine the two pole integrals into `weilPhi f 1 + weilPhi f 0`
  have hphi_int_1 : Integrable (fun u : ℝ => f.toFun u * cexp (((1 : ℂ) - 1 / 2) * (u : ℂ))) :=
    Stage4ExplicitFormula.integrable_weilBilateralTransform f.weilAdmissible
      (by simp; linarith [f.decayRate_gt])
  have hphi_int_0 : Integrable (fun u : ℝ => f.toFun u * cexp (((0 : ℂ) - 1 / 2) * (u : ℂ))) :=
    Stage4ExplicitFormula.integrable_weilBilateralTransform f.weilAdmissible
      (by simp; linarith [f.decayRate_gt])
  have hpole1 : (∫ u in Set.Ioi (0 : ℝ), f.toFun u * ((Real.exp (u / 2) : ℝ) : ℂ)) +
      (∫ u in Set.Ioi (0 : ℝ), (weilTestReflect f).toFun u * ((Real.exp (-u / 2) : ℝ) : ℂ)) =
      weilPhi f 1 := by
    have hneg : ∫ u in Set.Ioi (0 : ℝ), f.toFun (-u) * ((Real.exp (-u / 2) : ℝ) : ℂ) =
        ∫ u in Set.Iic (0 : ℝ), f.toFun u * cexp (((1 : ℂ) - 1 / 2) * (u : ℂ)) := by
      rw [← integral_indicator measurableSet_Iic, ← MeasureTheory.integral_neg_eq_self _ volume,
        ← MeasureTheory.integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      by_cases hu : 0 ≤ u
      · have h1 : -u ∈ Set.Iic (0 : ℝ) := by simp [hu]
        simp only [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ici.mpr hu)]
        rw [Complex.ofReal_exp]; congr 2; push_cast; ring
      · have h1 : -u ∉ Set.Iic (0 : ℝ) := by simp [hu]
        simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show u ∉ Set.Ici (0 : ℝ) from hu)]
    have hpos : ∫ u in Set.Ioi (0 : ℝ), f.toFun u * ((Real.exp (u / 2) : ℝ) : ℂ) =
        ∫ u in Set.Ioi (0 : ℝ), f.toFun u * cexp (((1 : ℂ) - 1 / 2) * (u : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [Complex.ofReal_exp]; congr 2; push_cast; ring
    dsimp only [weilTestReflect]
    rw [hpos, hneg, add_comm,
      ← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hphi_int_1.integrableOn hphi_int_1.integrableOn,
      Set.Iic_union_Ioi, setIntegral_univ]
    rfl
  have hpole0 : (∫ u in Set.Ioi (0 : ℝ), f.toFun u * ((Real.exp (-u / 2) : ℝ) : ℂ)) +
      (∫ u in Set.Ioi (0 : ℝ), (weilTestReflect f).toFun u * ((Real.exp (u / 2) : ℝ) : ℂ)) =
      weilPhi f 0 := by
    have hneg : ∫ u in Set.Ioi (0 : ℝ), f.toFun (-u) * ((Real.exp (u / 2) : ℝ) : ℂ) =
        ∫ u in Set.Iic (0 : ℝ), f.toFun u * cexp (((0 : ℂ) - 1 / 2) * (u : ℂ)) := by
      rw [← integral_indicator measurableSet_Iic, ← MeasureTheory.integral_neg_eq_self _ volume,
        ← MeasureTheory.integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      by_cases hu : 0 ≤ u
      · have h1 : -u ∈ Set.Iic (0 : ℝ) := by simp [hu]
        simp only [Set.indicator_of_mem h1, Set.indicator_of_mem (Set.mem_Ici.mpr hu)]
        rw [Complex.ofReal_exp]; congr 2; push_cast; ring
      · have h1 : -u ∉ Set.Iic (0 : ℝ) := by simp [hu]
        simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem (show u ∉ Set.Ici (0 : ℝ) from hu)]
    have hpos : ∫ u in Set.Ioi (0 : ℝ), f.toFun u * ((Real.exp (-u / 2) : ℝ) : ℂ) =
        ∫ u in Set.Ioi (0 : ℝ), f.toFun u * cexp (((0 : ℂ) - 1 / 2) * (u : ℂ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [Complex.ofReal_exp]; congr 2; push_cast; ring
    dsimp only [weilTestReflect]
    rw [hpos, hneg, add_comm,
      ← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        hphi_int_0.integrableOn hphi_int_0.integrableOn,
      Set.Iic_union_Ioi, setIntegral_univ]
    rfl
  -- Combine the two prime `tsum`s
  have hprime_summ : ∀ g : AdmissibleWeilTest,
      Summable (fun n : ℕ => (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * g.toFun (Real.log (n : ℝ))) := fun g => by
    have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((g.decayRate + 1 / 2 : ℝ) : ℂ))
      (by simp; linarith [g.decayRate_gt]))
    rw [LSeriesSummable] at hL
    have hC := g.boundConst_nonneg
    refine Summable.of_norm_bounded (hL.norm.mul_left g.boundConst) fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
      have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      rw [LSeries.term_of_ne_zero hn, norm_mul, norm_div, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.norm_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re]
      have hg_bd : ‖g.toFun (Real.log (n : ℝ))‖ ≤ g.boundConst * (n : ℝ) ^ (-g.decayRate) := by
        have h1 := g.bound0 (Real.log (n : ℝ))
        rw [abs_of_nonneg hlog_nn] at h1
        rw [Real.rpow_def_of_pos hn_pos, mul_comm (Real.log (n : ℝ))]
        exact h1
      have hpow_eq : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (-g.decayRate) =
          ((n : ℝ) ^ (g.decayRate + 1 / 2))⁻¹ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn_pos.le, ← Real.rpow_neg hn_pos.le,
          ← Real.rpow_add hn_pos]; congr 1; ring
      calc (Λ n : ℝ) / Real.sqrt (n : ℝ) * ‖g.toFun (Real.log (n : ℝ))‖
          ≤ (Λ n : ℝ) / Real.sqrt (n : ℝ) * (g.boundConst * (n : ℝ) ^ (-g.decayRate)) :=
            mul_le_mul_of_nonneg_left hg_bd (by positivity)
        _ = g.boundConst * ((Λ n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) ^ (-g.decayRate))) := by
            rw [div_eq_mul_inv]; ring
        _ = g.boundConst * ((Λ n : ℝ) / (n : ℝ) ^ (g.decayRate + 1 / 2)) := by
            rw [hpow_eq, ← div_eq_mul_inv]
  have hprime_add :
      (∑' n : ℕ, (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * f.toFun (Real.log (n : ℝ))) +
      (∑' n : ℕ, (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) * (weilTestReflect f).toFun (Real.log (n : ℝ))) =
      ∑' n : ℕ, (((Λ n : ℝ) / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
        (f.toFun (Real.log (n : ℝ)) + f.toFun (-Real.log (n : ℝ))) := by
    rw [← (hprime_summ f).tsum_add (hprime_summ (weilTestReflect f))]
    refine tsum_congr fun n => ?_
    dsimp only [weilTestReflect]; ring
  -- Combine the two archimedean integrals
  have harch_add :
      (∫ u in Set.Ioi (0 : ℝ),
        (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun u)) +
      (∫ u in Set.Ioi (0 : ℝ),
        (((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (weilTestReflect f).toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (weilTestReflect f).toFun u)) =
      ∫ u in Set.Ioi (0 : ℝ),
        (((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * f.toFun 0 -
         ((Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) * (f.toFun u + f.toFun (-u))) := by
    rw [← integral_add (integrableOn_weilArchHalf f) (integrableOn_weilArchHalf (weilTestReflect f))]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    dsimp only [weilTestReflect]
    simp only [neg_zero]
    have hmul2 : ((2 * Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) =
        ((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) +
        ((Real.exp (-2 * u) / (1 - Real.exp (-2 * u)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add]; congr 1; ring
    rw [hmul2]; ring
  have hconst_add :
      (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) * f.toFun 0 +
      (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) * (weilTestReflect f).toFun 0 =
      ((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) * f.toFun 0 := by
    dsimp only [weilTestReflect]
    simp only [neg_zero]
    have h2 : (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) +
        (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 : ℝ) : ℂ) =
        ((Real.log Real.pi + Real.eulerMascheroniConstant : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add]; congr 1; ring
    linear_combination f.toFun 0 * h2
  unfold weilArithDist weilArchTerm
  linear_combination -hpole1 - hpole0 + hprime_add + hconst_add - harch_add

/-- **UNCONDITIONAL WEIL EXPLICIT FORMULA ON NATIVE `riemannZeta` & `ArithmeticFunction.vonMangoldt`**:
for EVERY `f : AdmissibleWeilTest`, the purely arithmetic prime + archimedean distribution
`weilArithDist f` equals the multiplicity-counted nontrivial zero sum
`∑' (ρ : ZetaNontrivialZero), weilPhi f ρ.val`. -/
theorem weil_explicit_formula (f : AdmissibleWeilTest) :
    weilArithDist f = ∑' (ρ : ZetaNontrivialZero), weilPhi f ρ.val := by
  rw [tsum_zetaNontrivialZero_eq_xiZeroSeq, weil_explicit_formula_xiZeroSeq]

/-! ## Section 6: Genuine Arithmetic Weil Positivity Criterion for `RiemannHypothesis` -/

/-- Concrete `Stage4ExplicitFormula.ZeroSpectrum` instantiated directly on Mathlib's actual
multiplicity-counted nontrivial zeros `Stage7HadamardXiProduct.xiZeroSeq`. -/
def xiZeroSpectrum : Stage4ExplicitFormula.ZeroSpectrum where
  zero := xiZeroSeq
  in_strip := xiZeroSeq_strip
  locally_finite := Stage9ExplicitFormula.finite_xiZeroSeq_abs_im_le
  gaussian_summable := fun c hc => by
    set K : ℝ := max 1 (1 / c)
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_)
      (xiZeroSeq_summable_inv_sq.mul_left K)
    have hst := xiZeroSeq_strip n
    have hρ_pos : 0 < ‖xiZeroSeq n‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (xiZeroSeq_ne_zero n))
    have hnsq : ‖xiZeroSeq n‖ ^ 2 ≤ 1 + (xiZeroSeq n).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [hst.1, hst.2]
    have hexp_ge : 1 + c * (xiZeroSeq n).im ^ 2 ≤ Real.exp (c * (xiZeroSeq n).im ^ 2) := by
      linarith [Real.add_one_le_exp (c * (xiZeroSeq n).im ^ 2)]
    have hlin : ‖xiZeroSeq n‖ ^ 2 ≤ K * (1 + c * (xiZeroSeq n).im ^ 2) := by
      have hK1 : 1 ≤ K := le_max_left _ _
      have hKc : 1 ≤ K * c := by
        have h1 : 1 / c ≤ K := le_max_right _ _
        have h2 := mul_le_mul_of_nonneg_right h1 hc.le
        rwa [one_div_mul_cancel hc.ne'] at h2
      nlinarith [sq_nonneg (xiZeroSeq n).im]
    have hneg_eq : Real.exp (-c * (xiZeroSeq n).im ^ 2) = (Real.exp (c * (xiZeroSeq n).im ^ 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hneg_eq, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (Real.exp_pos _) hρ_pos]
    have hden_pos : 0 < 1 + c * (xiZeroSeq n).im ^ 2 := by positivity
    calc 1 * ‖xiZeroSeq n‖ ^ 2 = ‖xiZeroSeq n‖ ^ 2 := one_mul _
      _ ≤ K * (1 + c * (xiZeroSeq n).im ^ 2) := hlin
      _ ≤ K * Real.exp (c * (xiZeroSeq n).im ^ 2) :=
          mul_le_mul_of_nonneg_left hexp_ge (by positivity)

/-- **Exact Bridge**: for every `f : AdmissibleWeilTest`, the real part of the purely arithmetic
distribution `weilArithDist (weilSelfConv f)` equals the spectral Weil quadratic form
`Stage4ExplicitFormula.weilQuadraticForm xiZeroSpectrum f.toFun`. -/
theorem re_weilArithDist_selfConv_eq_weilQuadraticForm (f : AdmissibleWeilTest) :
    (weilArithDist (weilSelfConv f)).re =
      Stage4ExplicitFormula.weilQuadraticForm xiZeroSpectrum f.toFun := by
  rw [weil_explicit_formula_xiZeroSeq (weilSelfConv f)]
  have hre : (∑' n : ℕ, weilPhi (weilSelfConv f) (xiZeroSeq n)).re =
      ∑' n : ℕ, (weilPhi (weilSelfConv f) (xiZeroSeq n)).re := by
    simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum (summable_weilPhi_xiZeroSeq (weilSelfConv f))
  rw [hre]
  rfl

/-- **GENUINE FULL ARITHMETIC WEIL POSITIVITY CRITERION FOR THE RIEMANN HYPOTHESIS**:
Native Mathlib `RiemannHypothesis` holds IF AND ONLY IF for every `f : AdmissibleWeilTest`,
`0 ≤ (weilArithDist (weilSelfConv f)).re`,
where the RHS depends **ONLY on primes (`ArithmeticFunction.vonMangoldt`), `Real.log`, and the
archimedean integral** — with **ZERO** reference to zeros of `riemannZeta`! -/
theorem weil_positivity_arith_iff_RH :
    RiemannHypothesis ↔
      ∀ f : AdmissibleWeilTest, 0 ≤ (weilArithDist (weilSelfConv f)).re := by
  have hsurj : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → ∃ n : ℕ, xiZeroSpectrum.zero n = s := by
    intro s h0 h1 hz
    have hxi0 : xi s = 0 := (xi_eq_zero_iff_critical_strip_zeta_zero s).mpr ⟨h0, h1, hz⟩
    exact isMultiplicityZeroSeq_xi.exists_of_eq_zero differentiable_xi (by simp) hxi0
  have hiff := Stage4ExplicitFormula.riemannHypothesis_iff_weilPositivity xiZeroSpectrum hsurj
    xiZeroSeq_riemannZeta_zero
  constructor
  · intro hRH f
    rw [re_weilArithDist_selfConv_eq_weilQuadraticForm f]
    exact hiff.mp hRH f.toFun f.weilAdmissible_one
  · intro hpos
    have hon : ∀ n : ℕ, (xiZeroSpectrum.zero n).re = 1 / 2 :=
      Stage4ExplicitFormula.onLine_of_weilQuadraticForm_nonneg xiZeroSpectrum fun a ha γ => by
        have h := hpos (admissibleOddGaussian a ha γ)
        rwa [re_weilArithDist_selfConv_eq_weilQuadraticForm] at h
    exact hiff.mpr ((Stage4ExplicitFormula.weilPositivity_spectrum_iff_onLine xiZeroSpectrum).mp hon)

end RHDirect.WeilExplicit

end
