import RHDirect.Stage6HeckeSpectral
import RHDirect.Stage8ModularRing
import RHDirect.Stage8RamanujanDelta
import RHDirect.Stage9CuspFormLFunc
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# RHDirect.Stage10PeterssonHecke

**UNCONDITIONAL CONCRETE PETERSSON INNER PRODUCT ON `SL₂(ℤ) \ ℍ`, SELF-ADJOINTNESS OF HECKE
OPERATORS `⟨T_n f, g⟩ = ⟨f, T_n g⟩`, REALITY OF EIGENVALUES, ALL FIVE 1D LEVEL-1 NORMALIZED
HECKE EIGENFORMS (`k = 12, 16, 18, 20, 22`), AND EXPLICIT WEIGHT-24 (`ℚ(√144169)`) HECKE
DIAGONALIZATION** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function
open RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular RHDirect.Stage6HeckeSpectral
open RHDirect.Stage7EisensteinSeries RHDirect.Stage8ModularRing RHDirect.Stage8RamanujanDelta
open RHDirect.Stage9CuspFormLFunc
open scoped BigOperators UpperHalfPlane ModularForm Topology ENNReal Manifold ComplexConjugate
  MatrixGroups

namespace RHDirect.Stage10PeterssonHecke

noncomputable section

/-! ## Section 1: Concrete Petersson Inner Product & Hilbert Space Structure on `CuspForm SL2ZRange k` -/

section PeterssonInnerProduct

/-- The standard closed `SL₂(ℤ)` fundamental domain in Cartesian coordinates `(x, y) ∈ ℝ × ℝ`:
`stdFD = { (x, y) | |x| ≤ 1/2, y > 0, x² + y² ≥ 1 }`. -/
def stdFD : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | |p.1| ≤ 1 / 2 ∧ 0 < p.2 ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2 }

/-- The open interior of the standard `SL₂(ℤ)` fundamental domain in `ℝ × ℝ`:
`stdFDO = { (x, y) | |x| < 1/2, y > 0, x² + y² > 1 }`. -/
def stdFDO : Set (ℝ × ℝ) :=
  { p : ℝ × ℝ | |p.1| < 1 / 2 ∧ 0 < p.2 ∧ 1 < p.1 ^ 2 + p.2 ^ 2 }

theorem stdFDO_subset_stdFD : stdFDO ⊆ stdFD :=
  fun _ hp => ⟨hp.1.le, hp.2.1, hp.2.2.le⟩

theorem isOpen_stdFDO : IsOpen stdFDO := by
  unfold stdFDO
  have h1 : IsOpen { p : ℝ × ℝ | |p.1| < 1 / 2 } :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsOpen { p : ℝ × ℝ | 0 < p.2 } :=
    isOpen_lt continuous_const continuous_snd
  have h3 : IsOpen { p : ℝ × ℝ | 1 < p.1 ^ 2 + p.2 ^ 2 } :=
    isOpen_lt continuous_const ((continuous_fst.pow 2).add (continuous_snd.pow 2))
  exact h1.inter (h2.inter h3)

theorem measurableSet_stdFD : MeasurableSet stdFD := by
  unfold stdFD
  have h1 : MeasurableSet { p : ℝ × ℝ | |p.1| ≤ 1 / 2 } :=
    measurableSet_le (continuous_abs.comp continuous_fst).measurable measurable_const
  have h2 : MeasurableSet { p : ℝ × ℝ | 0 < p.2 } :=
    measurableSet_lt measurable_const continuous_snd.measurable
  have h3 : MeasurableSet { p : ℝ × ℝ | 1 ≤ p.1 ^ 2 + p.2 ^ 2 } :=
    measurableSet_le measurable_const ((continuous_fst.pow 2).add (continuous_snd.pow 2)).measurable
  exact h1.inter (h2.inter h3)

theorem stdFD_im_ge {p : ℝ × ℝ} (hp : p ∈ stdFD) : Real.sqrt 3 / 2 ≤ p.2 := by
  have hx : p.1 ^ 2 ≤ 1 / 4 := by
    have h1 : |p.1| ≤ 1 / 2 := hp.1
    have h2 : |p.1| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [abs_nonneg p.1]
    rw [sq_abs] at h2
    linarith
  have hy_sq : (Real.sqrt 3 / 2) ^ 2 ≤ p.2 ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    linarith [hp.2.2]
  nlinarith [hp.2.1, Real.sqrt_nonneg 3]

theorem stdFD_im_gt_half {p : ℝ × ℝ} (hp : p ∈ stdFD) : (1 / 2 : ℝ) < p.2 := by
  have h1 := stdFD_im_ge hp
  have hsq : (1 : ℝ) < Real.sqrt 3 := by
    have h : (1 : ℝ) ^ 2 < 3 := by norm_num
    exact Real.lt_sqrt_of_sq_lt h
  linarith

/-- Every point of `stdFD` lies in the closure of the open interior `stdFDO`. -/
theorem stdFD_subset_closure_stdFDO : stdFD ⊆ closure stdFDO := by
  intro p hp
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ : ℝ := min (1 / 2) (ε / (2 * (|p.1| + 2)))
  have hden_pos : 0 < 2 * (|p.1| + 2) := by positivity
  have hδ_pos : 0 < δ := lt_min (by norm_num) (div_pos hε hden_pos)
  have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδ_le : δ ≤ ε / (2 * (|p.1| + 2)) := min_le_right _ _
  let q : ℝ × ℝ := ((1 - δ) * p.1, p.2 + δ)
  have hq_mem : q ∈ stdFDO := by
    refine ⟨?_, by linarith [hp.2.1], ?_⟩
    · change |(1 - δ) * p.1| < 1 / 2
      rw [abs_mul, abs_of_pos (by linarith)]
      have h1 : |p.1| ≤ 1 / 2 := hp.1
      nlinarith
    · change 1 < ((1 - δ) * p.1) ^ 2 + (p.2 + δ) ^ 2
      have hx_sq : p.1 ^ 2 ≤ 1 / 4 := by
        have h1 : |p.1| ≤ 1 / 2 := hp.1
        have h2 : |p.1| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [abs_nonneg p.1]
        rw [sq_abs] at h2; linarith
      have hy_half : (1 / 2 : ℝ) < p.2 := stdFD_im_gt_half hp
      have hdiff : 0 < p.2 - p.1 ^ 2 := by linarith
      have hexp : ((1 - δ) * p.1) ^ 2 + (p.2 + δ) ^ 2 =
          (p.1 ^ 2 + p.2 ^ 2) + 2 * δ * (p.2 - p.1 ^ 2) + δ ^ 2 * (p.1 ^ 2 + 1) := by ring
      rw [hexp]
      nlinarith [hp.2.2, sq_nonneg p.1]
  refine ⟨q, hq_mem, ?_⟩
  rw [Prod.dist_eq]
  have hd1 : dist p.1 q.1 < ε := by
    change |p.1 - (1 - δ) * p.1| < ε
    have hsub : p.1 - (1 - δ) * p.1 = δ * p.1 := by ring
    rw [hsub, abs_mul, abs_of_pos hδ_pos]
    have hbound : δ * |p.1| ≤ (ε / (2 * (|p.1| + 2))) * |p.1| :=
      mul_le_mul_of_nonneg_right hδ_le (abs_nonneg _)
    have hlt : (ε / (2 * (|p.1| + 2))) * |p.1| < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden_pos]
      nlinarith [abs_nonneg p.1]
    exact lt_of_le_of_lt hbound hlt
  have hd2 : dist p.2 q.2 < ε := by
    change |p.2 - (p.2 + δ)| < ε
    have hsub : p.2 - (p.2 + δ) = -δ := by ring
    rw [hsub, abs_neg, abs_of_pos hδ_pos]
    have hlt : ε / (2 * (|p.1| + 2)) < ε := by
      rw [div_lt_iff₀ hden_pos]
      nlinarith [abs_nonneg p.1]
    exact lt_of_le_of_lt hδ_le hlt
  exact max_lt hd1 hd2

/-- Construct an `UpperHalfPlane` point from `(x, y) ∈ ℝ × ℝ` with `y > 0`. -/
def pairToUHP (p : ℝ × ℝ) (hp : 0 < p.2) : UpperHalfPlane :=
  ⟨(p.1 : ℂ) + Complex.I * (p.2 : ℂ), by simp [hp]⟩

@[simp]
theorem pairToUHP_coe (p : ℝ × ℝ) (hp : 0 < p.2) :
    (pairToUHP p hp : ℂ) = (p.1 : ℂ) + Complex.I * (p.2 : ℂ) := rfl

@[simp]
theorem pairToUHP_re (p : ℝ × ℝ) (hp : 0 < p.2) :
    (pairToUHP p hp).re = p.1 := by
  simp [pairToUHP]

@[simp]
theorem pairToUHP_im (p : ℝ × ℝ) (hp : 0 < p.2) :
    (pairToUHP p hp).im = p.2 := by
  simp [pairToUHP]

theorem pairToUHP_eq_ofComplex (p : ℝ × ℝ) (hp : 0 < p.2) :
    pairToUHP p hp = UpperHalfPlane.ofComplex ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) := by
  have him : 0 < ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)).im := by simp [hp]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  rfl

/-- Total Petersson integrand `(x, y) ↦ f(x + i y) · conj(g(x + i y)) · y^{k - 2}` on `ℝ × ℝ`
(zero for `y ≤ 0`). -/
def peterssonIntegrand {k : ℤ} (f g : CuspForm SL2ZRange k) (p : ℝ × ℝ) : ℂ :=
  if hp : 0 < p.2 then
    f (pairToUHP p hp) * star (g (pairToUHP p hp)) * (p.2 : ℂ) ^ (k - 2)
  else 0

/-- **Concrete Petersson Inner Product on `CuspForm SL2ZRange k`**:
$$\langle f, g \rangle_{\mathrm{Pet}} = \iint_{\mathcal{D}} f(x + i y)\,\overline{g(x + i y)}\,y^{k-2}\,dx\,dy.$$ -/
def peterssonInner {k : ℤ} (f g : CuspForm SL2ZRange k) : ℂ :=
  ∫ p in stdFD, peterssonIntegrand f g p

/-- Continuity of `(x, y) ↦ f(x + i y)` on the open upper half-plane `{ p : ℝ × ℝ | 0 < p.2 }`. -/
theorem continuousOn_cuspForm_pair {k : ℤ} (f : CuspForm SL2ZRange k) :
    ContinuousOn (fun p : ℝ × ℝ => if hp : 0 < p.2 then f (pairToUHP p hp) else 0)
      { p : ℝ × ℝ | 0 < p.2 } := by
  have hdiff : DifferentiableOn ℂ ((f : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex)
      { z : ℂ | 0 < z.im } :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have hmap : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))
  have hcomp : ContinuousOn
      (fun p : ℝ × ℝ => f (UpperHalfPlane.ofComplex ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))))
      { p : ℝ × ℝ | 0 < p.2 } := by
    refine hdiff.continuousOn.comp hmap.continuousOn fun p hp => ?_
    change 0 < ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)).im
    simpa using hp
  refine hcomp.congr fun p hp => ?_
  have hp' : 0 < p.2 := hp
  rw [dif_pos hp', pairToUHP_eq_ofComplex p hp']

/-- Continuity of `peterssonIntegrand f g` on `{ p : ℝ × ℝ | 0 < p.2 }`. -/
theorem continuousOn_peterssonIntegrand {k : ℤ} (f g : CuspForm SL2ZRange k) :
    ContinuousOn (peterssonIntegrand f g) { p : ℝ × ℝ | 0 < p.2 } := by
  have hf := continuousOn_cuspForm_pair f
  have hg := continuousOn_cuspForm_pair g
  have hpow : ContinuousOn (fun p : ℝ × ℝ => ((p.2 : ℂ) ^ (k - 2))) { p : ℝ × ℝ | 0 < p.2 } := by
    refine ContinuousOn.zpow₀ (Complex.continuous_ofReal.comp continuous_snd).continuousOn (k - 2) ?_
    intro p hp
    left
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  have hprod := (hf.mul (Complex.continuous_conj.comp_continuousOn hg)).mul hpow
  refine hprod.congr fun p hp => ?_
  have hp' : 0 < p.2 := hp
  simp only [peterssonIntegrand, dif_pos hp', Complex.star_def, Pi.mul_apply, Function.comp_apply]

/-- Uniform exponential decay of any level-1 cusp form on the vertical half-strip
`|x| ≤ 1/2, y ≥ √3/2`. -/
theorem cuspForm_exp_decay_strip {k : ℤ} (f : CuspForm SL2ZRange k) :
    ∃ C > 0, ∀ (p : ℝ × ℝ), |p.1| ≤ 1 / 2 → Real.sqrt 3 / 2 ≤ p.2 → ∀ (hp : 0 < p.2),
      ‖f (pairToUHP p hp)‖ ≤ C * Real.exp (-2 * Real.pi * p.2) := by
  have hbigO := CuspFormClass.exp_decay_atImInfty f zero_lt_one one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hbigO
  obtain ⟨C₀, hC₀⟩ := hbigO
  rw [UpperHalfPlane.atImInfty_basis.eventually_iff] at hC₀
  obtain ⟨A, _, hA⟩ := hC₀
  let y₀ : ℝ := Real.sqrt 3 / 2
  have hy₀_pos : 0 < y₀ := by positivity
  let B : ℝ := max y₀ A
  have hBy₀ : y₀ ≤ B := le_max_left y₀ A
  have hBA : A ≤ B := le_max_right y₀ A
  let K : Set (ℝ × ℝ) := Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Icc y₀ B
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let h : ℝ × ℝ → ℝ := fun p =>
    ‖if hp : 0 < p.2 then f (pairToUHP p hp) else 0‖ * Real.exp (2 * Real.pi * p.2)
  have hh_cont : ContinuousOn h K := by
    have hsub : K ⊆ { p : ℝ × ℝ | 0 < p.2 } := fun p hp => lt_of_lt_of_le hy₀_pos hp.2.1
    exact ((continuousOn_cuspForm_pair f).norm.mono hsub).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).continuousOn
  obtain ⟨C₁, hC₁⟩ := hK_compact.exists_bound_of_continuousOn hh_cont
  let C : ℝ := max (max C₀ C₁) 1
  have hC_pos : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC₀_le : C₀ ≤ C := le_trans (le_max_left C₀ C₁) (le_max_left _ _)
  have hC₁_le : C₁ ≤ C := le_trans (le_max_right C₀ C₁) (le_max_left _ _)
  refine ⟨C, hC_pos, fun p hx hy hp => ?_⟩
  by_cases hyB : p.2 ≤ B
  · have hpK : p ∈ K :=
      ⟨⟨by linarith [(abs_le.mp hx).1], (abs_le.mp hx).2⟩, hy, hyB⟩
    have hbound := hC₁ p hpK
    have hh_nn : 0 ≤ h p := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hh_nn] at hbound
    have hprod : ‖f (pairToUHP p hp)‖ * Real.exp (2 * Real.pi * p.2) ≤ C := by
      have heq : h p = ‖f (pairToUHP p hp)‖ * Real.exp (2 * Real.pi * p.2) := by
        simp only [h, dif_pos hp]
      rw [← heq]
      exact hbound.trans hC₁_le
    have hmul : Real.exp (2 * Real.pi * p.2) * Real.exp (-2 * Real.pi * p.2) = 1 := by
      rw [← Real.exp_add]
      have hz : 2 * Real.pi * p.2 + -2 * Real.pi * p.2 = 0 := by ring
      rw [hz, Real.exp_zero]
    calc ‖f (pairToUHP p hp)‖
        = (‖f (pairToUHP p hp)‖ * Real.exp (2 * Real.pi * p.2)) * Real.exp (-2 * Real.pi * p.2) := by
            rw [mul_assoc, hmul, mul_one]
      _ ≤ C * Real.exp (-2 * Real.pi * p.2) :=
            mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
  · have hAy : A ≤ p.2 := le_trans hBA (le_of_not_ge hyB)
    have hmem : pairToUHP p hp ∈ UpperHalfPlane.im ⁻¹' Set.Ici A := by
      change A ≤ (pairToUHP p hp).im
      simpa using hAy
    have hbound := hA hmem
    simp only [pairToUHP_im, div_one, Real.norm_of_nonneg (Real.exp_pos _).le] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right hC₀_le (Real.exp_pos _).le)

/-- Elementary domination `exp(-4π y) * y^m ≤ M * exp(-2π y)` on `[y₀, ∞)` for any integer `m : ℤ`
and any `y₀ > 0`. -/
private lemma exp_mul_zpow_bound (m : ℤ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    ∃ M > 0, ∀ y : ℝ, y₀ ≤ y →
      Real.exp (-4 * Real.pi * y) * y ^ m ≤ M * Real.exp (-2 * Real.pi * y) := by
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    let M : ℝ := (Nat.factorial m : ℝ) / (2 * Real.pi) ^ m
    have hM_pos : 0 < M := div_pos (Nat.cast_pos.mpr (Nat.factorial_pos m)) (by positivity)
    refine ⟨M, hM_pos, fun y hy => ?_⟩
    have hy_pos : 0 < y := lt_of_lt_of_le hy₀ hy
    have hpow := Real.pow_div_factorial_le_exp (2 * Real.pi * y) (by positivity) m
    have hfact_pos : (0 : ℝ) < (Nat.factorial m : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    have h2pi_pos : (0 : ℝ) < (2 * Real.pi) ^ m := by positivity
    have h1 : y ^ m ≤ M * Real.exp (2 * Real.pi * y) := by
      have hmul : (2 * Real.pi) ^ m * y ^ m ≤ (Nat.factorial m : ℝ) * Real.exp (2 * Real.pi * y) := by
        rw [← mul_pow, mul_comm (Nat.factorial m : ℝ)]
        exact (div_le_iff₀ hfact_pos).mp hpow
      have hdiv : y ^ m ≤ ((Nat.factorial m : ℝ) * Real.exp (2 * Real.pi * y)) / (2 * Real.pi) ^ m :=
        (le_div_iff₀' h2pi_pos).mpr hmul
      simpa [M, mul_div_right_comm] using hdiv
    have hexp_split : Real.exp (-4 * Real.pi * y) =
        Real.exp (-2 * Real.pi * y) * Real.exp (-2 * Real.pi * y) := by
      rw [← Real.exp_add]; congr 1; ring
    have hcancel : Real.exp (-2 * Real.pi * y) * Real.exp (2 * Real.pi * y) = 1 := by
      rw [← Real.exp_add]
      have hz : -2 * Real.pi * y + 2 * Real.pi * y = 0 := by ring
      rw [hz, Real.exp_zero]
    rw [zpow_natCast, hexp_split]
    calc Real.exp (-2 * Real.pi * y) * Real.exp (-2 * Real.pi * y) * y ^ m
        ≤ Real.exp (-2 * Real.pi * y) * Real.exp (-2 * Real.pi * y) *
            (M * Real.exp (2 * Real.pi * y)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M * (Real.exp (-2 * Real.pi * y) * Real.exp (2 * Real.pi * y)) *
            Real.exp (-2 * Real.pi * y) := by ring
      _ = M * Real.exp (-2 * Real.pi * y) := by rw [hcancel, mul_one]
  · set n : ℕ := (-m).toNat
    have hm_eq : m = -(n : ℤ) := by omega
    let M : ℝ := (y₀ ^ n)⁻¹
    have hM_pos : 0 < M := inv_pos.mpr (pow_pos hy₀ n)
    refine ⟨M, hM_pos, fun y hy => ?_⟩
    have hy_pos : 0 < y := lt_of_lt_of_le hy₀ hy
    have hpow_le : y ^ m ≤ M := by
      rw [hm_eq, _root_.zpow_neg, zpow_natCast]
      exact inv_anti₀ (pow_pos hy₀ n) (pow_le_pow_left₀ hy₀.le hy n)
    have hexp_le : Real.exp (-4 * Real.pi * y) ≤ Real.exp (-2 * Real.pi * y) :=
      Real.exp_le_exp.mpr (by have := Real.pi_pos; nlinarith)
    calc Real.exp (-4 * Real.pi * y) * y ^ m
        ≤ Real.exp (-2 * Real.pi * y) * M :=
          mul_le_mul hexp_le hpow_le (zpow_nonneg hy_pos.le m) (Real.exp_pos _).le
      _ = M * Real.exp (-2 * Real.pi * y) := mul_comm _ _

/-- **Integrability of the Concrete Petersson Integrand** on `stdFD` for every pair of level-1
cusp forms `f, g ∈ CuspForm SL2ZRange k`. -/
theorem peterssonIntegrable {k : ℤ} (f g : CuspForm SL2ZRange k) :
    IntegrableOn (peterssonIntegrand f g) stdFD volume := by
  obtain ⟨Cf, hCf_pos, hCf⟩ := cuspForm_exp_decay_strip f
  obtain ⟨Cg, hCg_pos, hCg⟩ := cuspForm_exp_decay_strip g
  let y₀ : ℝ := Real.sqrt 3 / 2
  have hy₀_pos : 0 < y₀ := by positivity
  obtain ⟨M, hM_pos, hM⟩ := exp_mul_zpow_bound (k - 2) hy₀_pos
  let S : Set (ℝ × ℝ) := Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ici y₀
  have hstd_sub : stdFD ⊆ S := fun p hp =>
    ⟨⟨by linarith [(abs_le.mp hp.1).1], (abs_le.mp hp.1).2⟩, stdFD_im_ge hp⟩
  have hdom_x : IntegrableOn (fun _ : ℝ => Cf * Cg * M) (Set.Icc (-1 / 2 : ℝ) (1 / 2)) volume :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hdom_y : IntegrableOn (fun y : ℝ => Real.exp (-2 * Real.pi * y)) (Set.Ici y₀) volume := by
    have hIoi := integrableOn_exp_mul_Ioi (a := -2 * Real.pi) (by linarith [Real.pi_pos]) y₀
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hIoi
  have hdom_prod : IntegrableOn (fun p : ℝ × ℝ => (Cf * Cg * M) * Real.exp (-2 * Real.pi * p.2))
      S volume := by
    have h := Integrable.mul_prod hdom_x hdom_y
    simpa [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict, S] using h
  have hdom_fd : IntegrableOn (fun p : ℝ × ℝ => (Cf * Cg * M) * Real.exp (-2 * Real.pi * p.2))
      stdFD volume :=
    hdom_prod.mono_set hstd_sub
  have haesm : AEStronglyMeasurable (peterssonIntegrand f g) (volume.restrict stdFD) := by
    have hcont : ContinuousOn (peterssonIntegrand f g) stdFD :=
      (continuousOn_peterssonIntegrand f g).mono fun p hp => hp.2.1
    exact hcont.aestronglyMeasurable measurableSet_stdFD
  refine hdom_fd.mono' haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_stdFD] with p hp
  have hp2 : 0 < p.2 := hp.2.1
  have hy_ge : y₀ ≤ p.2 := stdFD_im_ge hp
  simp only [peterssonIntegrand, dif_pos hp2, norm_mul, norm_star, norm_zpow,
    Complex.norm_real, Real.norm_of_nonneg hp2.le]
  have hf_b := hCf p hp.1 hy_ge hp2
  have hg_b := hCg p hp.1 hy_ge hp2
  have hprod_fg : ‖f (pairToUHP p hp2)‖ * ‖g (pairToUHP p hp2)‖ ≤
      (Cf * Cg) * Real.exp (-4 * Real.pi * p.2) := by
    calc ‖f (pairToUHP p hp2)‖ * ‖g (pairToUHP p hp2)‖
        ≤ (Cf * Real.exp (-2 * Real.pi * p.2)) * (Cg * Real.exp (-2 * Real.pi * p.2)) :=
          mul_le_mul hf_b hg_b (norm_nonneg _) (by positivity)
      _ = (Cf * Cg) * (Real.exp (-2 * Real.pi * p.2) * Real.exp (-2 * Real.pi * p.2)) := by ring
      _ = (Cf * Cg) * Real.exp (-4 * Real.pi * p.2) := by
          rw [← Real.exp_add]; congr 2; ring
  calc ‖f (pairToUHP p hp2)‖ * ‖g (pairToUHP p hp2)‖ * p.2 ^ (k - 2)
      ≤ ((Cf * Cg) * Real.exp (-4 * Real.pi * p.2)) * p.2 ^ (k - 2) :=
        mul_le_mul_of_nonneg_right hprod_fg (zpow_nonneg hp2.le _)
    _ = (Cf * Cg) * (Real.exp (-4 * Real.pi * p.2) * p.2 ^ (k - 2)) := by ring
    _ ≤ (Cf * Cg) * (M * Real.exp (-2 * Real.pi * p.2)) :=
        mul_le_mul_of_nonneg_left (hM p.2 hy_ge) (by positivity)
    _ = (Cf * Cg * M) * Real.exp (-2 * Real.pi * p.2) := by ring

/-- **Hermitian Conjugate Symmetry**: `star (peterssonInner f g) = peterssonInner g f`. -/
theorem peterssonInner_conj_symm {k : ℤ} (f g : CuspForm SL2ZRange k) :
    star (peterssonInner f g) = peterssonInner g f := by
  unfold peterssonInner
  rw [Complex.star_def, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_stdFD fun p hp => ?_
  have hp2 : 0 < p.2 := hp.2.1
  simp only [peterssonIntegrand, dif_pos hp2, Complex.star_def, map_mul, map_zpow₀,
    Complex.conj_ofReal, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

theorem peterssonInner_add_left {k : ℤ} (f₁ f₂ g : CuspForm SL2ZRange k) :
    peterssonInner (f₁ + f₂) g = peterssonInner f₁ g + peterssonInner f₂ g := by
  unfold peterssonInner
  rw [← integral_add (peterssonIntegrable f₁ g) (peterssonIntegrable f₂ g)]
  refine setIntegral_congr_fun measurableSet_stdFD fun p hp => ?_
  simp only [peterssonIntegrand, dif_pos hp.2.1, _root_.add_apply]
  ring

theorem peterssonInner_add_right {k : ℤ} (f g₁ g₂ : CuspForm SL2ZRange k) :
    peterssonInner f (g₁ + g₂) = peterssonInner f g₁ + peterssonInner f g₂ := by
  have h := congrArg star (peterssonInner_add_left g₁ g₂ f)
  simpa [peterssonInner_conj_symm] using h

theorem peterssonInner_smul_left {k : ℤ} (c : ℂ) (f g : CuspForm SL2ZRange k) :
    peterssonInner (c • f) g = c * peterssonInner f g := by
  unfold peterssonInner
  rw [← smul_eq_mul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_stdFD fun p hp => ?_
  simp only [peterssonIntegrand, dif_pos hp.2.1, _root_.smul_apply, smul_eq_mul]
  ring

theorem peterssonInner_smul_right {k : ℤ} (c : ℂ) (f g : CuspForm SL2ZRange k) :
    peterssonInner f (c • g) = star c * peterssonInner f g := by
  have h := congrArg star (peterssonInner_smul_left c g f)
  simpa [peterssonInner_conj_symm] using h

theorem peterssonInner_zero_left {k : ℤ} (g : CuspForm SL2ZRange k) :
    peterssonInner 0 g = 0 := by
  have h := peterssonInner_smul_left (0 : ℂ) (0 : CuspForm SL2ZRange k) g
  simpa using h

theorem peterssonInner_zero_right {k : ℤ} (f : CuspForm SL2ZRange k) :
    peterssonInner f 0 = 0 := by
  have h := peterssonInner_smul_right (0 : ℂ) f (0 : CuspForm SL2ZRange k)
  simpa using h

/-- Real-valued self-integrand `p ↦ ‖f(x + i y)‖² * y^{k - 2}`. -/
private def peterssonSelfReal {k : ℤ} (f : CuspForm SL2ZRange k) (p : ℝ × ℝ) : ℝ :=
  if hp : 0 < p.2 then ‖f (pairToUHP p hp)‖ ^ 2 * p.2 ^ (k - 2) else 0

private lemma peterssonIntegrand_self_eq_ofReal {k : ℤ} (f : CuspForm SL2ZRange k) (p : ℝ × ℝ) :
    peterssonIntegrand f f p = ((peterssonSelfReal f p : ℝ) : ℂ) := by
  by_cases hp : 0 < p.2
  · simp only [peterssonIntegrand, peterssonSelfReal, dif_pos hp, Complex.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_zpow]
  · simp [peterssonIntegrand, peterssonSelfReal, dif_neg hp]

private lemma peterssonInner_self_eq_ofReal {k : ℤ} (f : CuspForm SL2ZRange k) :
    peterssonInner f f = ((∫ p in stdFD, peterssonSelfReal f p : ℝ) : ℂ) := by
  unfold peterssonInner
  have hofReal : (∫ p in stdFD, ((peterssonSelfReal f p : ℝ) : ℂ)) =
      ((∫ p in stdFD, peterssonSelfReal f p : ℝ) : ℂ) := integral_ofReal
  rw [← hofReal]
  refine setIntegral_congr_fun measurableSet_stdFD fun p _ => ?_
  exact peterssonIntegrand_self_eq_ofReal f p

theorem peterssonInner_self_im_eq_zero {k : ℤ} (f : CuspForm SL2ZRange k) :
    (peterssonInner f f).im = 0 := by
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_im]

theorem peterssonInner_self_re_nonneg {k : ℤ} (f : CuspForm SL2ZRange k) :
    0 ≤ (peterssonInner f f).re := by
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_re]
  refine setIntegral_nonneg measurableSet_stdFD fun p hp => ?_
  simp only [peterssonSelfReal, dif_pos hp.2.1]
  exact mul_nonneg (sq_nonneg _) (zpow_nonneg hp.2.1.le _)

/-- Every point `τ ∈ ModularGroup.fd` maps into `stdFD` via `(τ.re, τ.im)`. -/
private lemma mem_stdFD_of_mem_modularGroup_fd {τ : UpperHalfPlane} (hτ : τ ∈ ModularGroup.fd) :
    (τ.re, τ.im) ∈ stdFD := by
  refine ⟨hτ.2, τ.im_pos, ?_⟩
  have h1 : 1 ≤ Complex.normSq (τ : ℂ) := hτ.1
  rw [Complex.normSq_apply] at h1
  simpa [sq] using h1

/-- **STRICT POSITIVE DEFINITENESS OF THE CONCRETE PETERSSON INNER PRODUCT**:
for every nonzero level-1 cusp form `f ∈ CuspForm SL2ZRange k`,
`0 < (peterssonInner f f).re`! -/
theorem peterssonInner_self_pos {k : ℤ} {f : CuspForm SL2ZRange k} (hf : f ≠ 0) :
    0 < (peterssonInner f f).re := by
  have hex : ∃ τ₀ : UpperHalfPlane, f τ₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (by ext τ; exact h τ)
  obtain ⟨τ₀, hτ₀⟩ := hex
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ₀
  have hγ_ne : f (γ • τ₀) ≠ 0 := by
    have hsl := congrFun (f.slash_action_eq'
      (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ γ) ⟨γ, rfl⟩) τ₀
    change ((f : UpperHalfPlane → ℂ) ∣[k] γ) τ₀ = f τ₀ at hsl
    rw [ModularForm.SL_slash_apply] at hsl
    intro h0
    rw [h0, zero_mul] at hsl
    exact hτ₀ hsl.symm
  let τ : UpperHalfPlane := γ • τ₀
  let p₀ : ℝ × ℝ := (τ.re, τ.im)
  have hp₀_fd : p₀ ∈ stdFD := mem_stdFD_of_mem_modularGroup_fd hγ
  have hp₀_pos : 0 < p₀.2 := τ.im_pos
  have hpair_eq : pairToUHP p₀ hp₀_pos = τ := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simp [pairToUHP, p₀]
    · simp [pairToUHP, p₀]
  have hval_pos : 0 < peterssonSelfReal f p₀ := by
    simp only [peterssonSelfReal, dif_pos hp₀_pos, hpair_eq]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hγ_ne)) (zpow_pos hp₀_pos _)
  have hcont : ContinuousOn (peterssonSelfReal f) { p : ℝ × ℝ | 0 < p.2 } := by
    have h1 := Complex.continuous_re.comp_continuousOn (continuousOn_peterssonIntegrand f f)
    refine h1.congr fun p hp => ?_
    simp only [Function.comp_apply, peterssonIntegrand_self_eq_ofReal, Complex.ofReal_re]
  have hopen_pos : IsOpen ({ p : ℝ × ℝ | 0 < p.2 }) :=
    isOpen_lt continuous_const continuous_snd
  have hcontAt : ContinuousAt (peterssonSelfReal f) p₀ :=
    hcont.continuousAt (hopen_pos.mem_nhds hp₀_pos)
  have hev : ∀ᶠ p in nhds p₀, 0 < peterssonSelfReal f p :=
    hcontAt.eventually (lt_mem_nhds hval_pos)
  obtain ⟨r, hr_pos, hr⟩ := Metric.eventually_nhds_iff.mp hev
  let U : Set (ℝ × ℝ) := Metric.ball p₀ r ∩ stdFDO
  have hU_open : IsOpen U := Metric.isOpen_ball.inter isOpen_stdFDO
  have hU_nonempty : U.Nonempty := by
    have hcl := stdFD_subset_closure_stdFDO hp₀_fd
    obtain ⟨q, hq_fdo, hq_dist⟩ := Metric.mem_closure_iff.mp hcl r hr_pos
    exact ⟨q, by simpa [Metric.mem_ball, dist_comm] using hq_dist, hq_fdo⟩
  have hU_pos : 0 < volume U := hU_open.measure_pos volume hU_nonempty
  have hU_sub : U ⊆ Function.support (peterssonSelfReal f) ∩ stdFD := by
    intro q hq
    refine ⟨?_, stdFDO_subset_stdFD hq.2⟩
    have hq_pos : 0 < peterssonSelfReal f q := hr (Metric.mem_ball.mp hq.1)
    exact hq_pos.ne'
  have hintR : IntegrableOn (peterssonSelfReal f) stdFD volume := by
    have hre := (peterssonIntegrable f f).re
    refine IntegrableOn.congr_fun hre (fun p _ => ?_) measurableSet_stdFD
    simp [peterssonIntegrand_self_eq_ofReal]
  have hnn : 0 ≤ᵐ[volume.restrict stdFD] peterssonSelfReal f := by
    filter_upwards [ae_restrict_mem measurableSet_stdFD] with p hp
    simp only [peterssonSelfReal, dif_pos hp.2.1]
    exact mul_nonneg (sq_nonneg _) (zpow_nonneg hp.2.1.le _)
  rw [peterssonInner_self_eq_ofReal, Complex.ofReal_re,
    MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnn hintR]
  exact lt_of_lt_of_le hU_pos (measure_mono hU_sub)

theorem peterssonInner_self_eq_zero_iff {k : ℤ} (f : CuspForm SL2ZRange k) :
    peterssonInner f f = 0 ↔ f = 0 := by
  constructor
  · intro h0
    by_contra hf
    have hpos := peterssonInner_self_pos hf
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  · rintro rfl
    exact peterssonInner_zero_left 0

/-- **Petersson `InnerProductSpace.Core ℂ` on `CuspForm SL2ZRange k`**.
Note Mathlib's convention: `core.inner f g = peterssonInner g f` is conjugate-linear in the first
argument `f` and `ℂ`-linear in the second argument `g`. -/
@[instance_reducible]
def peterssonInnerCore (k : ℤ) : InnerProductSpace.Core ℂ (CuspForm SL2ZRange k) where
  inner f g := peterssonInner g f
  conj_inner_symm f g := peterssonInner_conj_symm f g
  re_inner_nonneg f := peterssonInner_self_re_nonneg f
  definite f hf := (peterssonInner_self_eq_zero_iff f).mp hf
  add_left f₁ f₂ g := peterssonInner_add_right g f₁ f₂
  smul_left f g c := peterssonInner_smul_right c g f

/-- Scoped `NormedAddCommGroup` structure on `CuspForm SL2ZRange k` induced by the concrete
Petersson inner product. -/
scoped instance peterssonNormedAddCommGroup (k : ℤ) :
    NormedAddCommGroup (CuspForm SL2ZRange k) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (CuspForm SL2ZRange k) _ _ _ (peterssonInnerCore k)

/-- Scoped `InnerProductSpace ℂ` structure on `CuspForm SL2ZRange k` induced by the concrete
Petersson inner product (`⟪f, g⟫_ℂ = peterssonInner g f`). -/
scoped instance peterssonInnerProductSpace (k : ℤ) :
    InnerProductSpace ℂ (CuspForm SL2ZRange k) :=
  InnerProductSpace.ofCore (peterssonInnerCore k).toCore

theorem petersson_inner_eq {k : ℤ} (f g : CuspForm SL2ZRange k) :
    inner ℂ f g = peterssonInner g f := rfl

/-- **Finite-Dimensionality of `CuspForm SL2ZRange k` for EVERY integer weight `k : ℤ`**. -/
instance finiteDimensional_cuspForm_SL2Z (k : ℤ) :
    FiniteDimensional ℂ (CuspForm SL2ZRange k) := by
  by_cases hk : k < 0
  · have hsub : Subsingleton (CuspForm SL2ZRange k) := by
      refine ⟨fun f g => ?_⟩
      have hf : f = 0 := by
        ext τ
        exact congrFun (ModularFormClass.levelOne_neg_weight_eq_zero hk f) τ
      have hg : g = 0 := by
        ext τ
        exact congrFun (ModularFormClass.levelOne_neg_weight_eq_zero hk g) τ
      rw [hf, hg]
    infer_instance
  · lift k to ℕ using (not_lt.mp hk)
    have hfinM : FiniteDimensional ℂ (ModularForm SL2ZRange (k : ℤ)) :=
      Module.Finite.of_basis (basisModularFormSL2Z k)
    have hinj : Function.Injective
        (CuspForm.toModularFormₗ (Γ := SL2ZRange) (k := (k : ℤ))) := by
      intro f g hfg
      ext τ
      exact congrArg (fun u : ModularForm SL2ZRange (k : ℤ) => u τ) hfg
    exact Module.Finite.of_injective (CuspForm.toModularFormₗ (Γ := SL2ZRange) (k := (k : ℤ))) hinj

end PeterssonInnerProduct

/-! ## Section 2: Level-1 Hecke Algebra, Hyperbolic Measure Invariance, & Unconditional
Petersson Self-Adjointness `⟨T_n f, g⟩ = ⟨f, T_n g⟩` -/

section HeckeAlgebraAndSelfAdjointness

/-! ### Part 2A: Hecke Algebra Relations on `CuspForm SL2ZRange k` -/

/-- Uniqueness of a level-1 cusp form from its Fourier (`q`-expansion) coefficients:
if `a_m(f) = a_m(g)` for all `m : ℕ`, then `f = g`. -/
theorem cuspForm_eq_of_qExpansion_coeff_eq {k : ℤ} {f g : CuspForm SL2ZRange k}
    (h : ∀ m : ℕ, qExpansionCoeff f m = qExpansionCoeff g m) : f = g := by
  ext τ
  have hf := ModularForm.hasSum_qExpansion f zero_lt_one one_mem_strictPeriods_SL τ
  have hg := ModularForm.hasSum_qExpansion g zero_lt_one one_mem_strictPeriods_SL τ
  have hfun : (fun m : ℕ => PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) =
      fun m : ℕ => PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    funext m
    exact congrArg (· * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (h m)
  rw [hfun] at hf
  exact hf.unique hg

theorem qExpansionCoeff_add {k : ℤ} (f g : CuspForm SL2ZRange k) (m : ℕ) :
    qExpansionCoeff (f + g) m = qExpansionCoeff f m + qExpansionCoeff g m := by
  unfold qExpansionCoeff
  rw [FunLike.coe_add, ModularForm.qExpansion_add zero_lt_one one_mem_strictPeriods_SL, map_add]

theorem qExpansionCoeff_sub {k : ℤ} (f g : CuspForm SL2ZRange k) (m : ℕ) :
    qExpansionCoeff (f - g) m = qExpansionCoeff f m - qExpansionCoeff g m := by
  unfold qExpansionCoeff
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub zero_lt_one one_mem_strictPeriods_SL, map_sub]

theorem qExpansionCoeff_smul {k : ℤ} (c : ℂ) (f : CuspForm SL2ZRange k) (m : ℕ) :
    qExpansionCoeff (c • f) m = c * qExpansionCoeff f m := by
  unfold qExpansionCoeff
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL,
    map_smul, smul_eq_mul]

theorem heckeCuspForm_add (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (f g : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk n hn (f + g) = heckeCuspForm k hk n hn f + heckeCuspForm k hk n hn g := by
  apply cuspForm_eq_of_qExpansion_coeff_eq
  intro m
  rw [qExpansionCoeff_add, qExpansionCoeff, qExpansionCoeff, qExpansionCoeff,
    heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff]
  have hfun : (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 ((f + g : CuspForm SL2ZRange (k : ℤ)) : UpperHalfPlane → ℂ))) =
      (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) +
      (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ))) := by
    funext j
    exact qExpansionCoeff_add f g j
  rw [hfun, heckeOp_add]
  rfl

theorem heckeCuspForm_smul (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (c : ℂ) (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk n hn (c • f) = c • heckeCuspForm k hk n hn f := by
  apply cuspForm_eq_of_qExpansion_coeff_eq
  intro m
  rw [qExpansionCoeff_smul, qExpansionCoeff, qExpansionCoeff,
    heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff]
  have hfun : (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 ((c • f : CuspForm SL2ZRange (k : ℤ)) : UpperHalfPlane → ℂ))) =
      c • (fun j => PowerSeries.coeff j (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) := by
    funext j
    exact qExpansionCoeff_smul c f j
  rw [hfun, heckeOp_smul]
  rfl

/-- The `n`-th Hecke operator `T_n` packaged as a `ℂ`-linear endomorphism of `CuspForm SL2ZRange k`
(for `n ≥ 1`, and `0` for `n = 0`). -/
def heckeCuspFormLin (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    CuspForm SL2ZRange (k : ℤ) →ₗ[ℂ] CuspForm SL2ZRange (k : ℤ) :=
  if hn : 1 ≤ n then
    { toFun := heckeCuspForm k hk n hn
      map_add' := heckeCuspForm_add k hk n hn
      map_smul' := heckeCuspForm_smul k hk n hn }
  else 0

@[simp]
theorem heckeCuspFormLin_apply (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n)
    (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspFormLin k hk n f = heckeCuspForm k hk n hn f := by
  simp [heckeCuspFormLin, dif_pos hn]

/-- `T_1 = id` on `CuspForm SL2ZRange k`. -/
theorem heckeCuspForm_one (k : ℕ) (hk : 1 ≤ k) (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk 1 le_rfl f = f := by
  apply cuspForm_eq_of_qExpansion_coeff_eq
  intro m
  rw [qExpansionCoeff, heckeCuspForm_qExpansion_coeff, heckeOp_one]
  rfl

/-- **Unconditional Hecke Commutativity on `CuspForm SL2ZRange k`**:
for ALL `k ≥ 1`, ALL `m, n ≥ 1`, and EVERY `f ∈ S_k(SL₂(ℤ))`,
`T_m (T_n f) = T_n (T_m f)`! -/
theorem heckeCuspForm_comm (k : ℕ) (hk : 1 ≤ k) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk m hm (heckeCuspForm k hk n hn f) =
      heckeCuspForm k hk n hn (heckeCuspForm k hk m hm f) := by
  apply cuspForm_eq_of_qExpansion_coeff_eq
  intro j
  rw [qExpansionCoeff, qExpansionCoeff,
    heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff]
  have h1 : (fun i => PowerSeries.coeff i
      (UpperHalfPlane.qExpansion 1 (heckeCuspForm k hk n hn f : UpperHalfPlane → ℂ))) =
      heckeOp k (1 : DirichletCharacter ℂ 1) n (qExpansionCoeff f) := by
    funext i; exact heckeCuspForm_qExpansion_coeff k hk n hn f i
  have h2 : (fun i => PowerSeries.coeff i
      (UpperHalfPlane.qExpansion 1 (heckeCuspForm k hk m hm f : UpperHalfPlane → ℂ))) =
      heckeOp k (1 : DirichletCharacter ℂ 1) m (qExpansionCoeff f) := by
    funext i; exact heckeCuspForm_qExpansion_coeff k hk m hm f i
  rw [h1, h2]
  exact congrFun (heckeOp_comm k (1 : DirichletCharacter ℂ 1) m n hm hn (qExpansionCoeff f)) j

/-- **Unconditional Coprime Hecke Multiplicativity on `CuspForm SL2ZRange k`**:
`Nat.Coprime m n → T_m (T_n f) = T_{m * n} f`. -/
theorem heckeCuspForm_mul_of_coprime (k : ℕ) (hk : 1 ≤ k) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hcop : Nat.Coprime m n) (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk m hm (heckeCuspForm k hk n hn f) =
      heckeCuspForm k hk (m * n) (Nat.mul_pos hm hn) f := by
  apply cuspForm_eq_of_qExpansion_coeff_eq
  intro j
  rw [qExpansionCoeff, qExpansionCoeff,
    heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff]
  have h1 : (fun i => PowerSeries.coeff i
      (UpperHalfPlane.qExpansion 1 (heckeCuspForm k hk n hn f : UpperHalfPlane → ℂ))) =
      heckeOp k (1 : DirichletCharacter ℂ 1) n (qExpansionCoeff f) := by
    funext i; exact heckeCuspForm_qExpansion_coeff k hk n hn f i
  rw [h1]
  exact congrFun (heckeOp_mul_of_coprime k (1 : DirichletCharacter ℂ 1) hcop (qExpansionCoeff f)) j

/-- **Unconditional Prime-Power Hecke Recurrence on `CuspForm SL2ZRange k`**:
for every prime `p` and `r ≥ 1`,
`T_{p^{r+1}} f = T_p (T_{p^r} f) - p^{k - 1} • T_{p^{r-1}} f`. -/
theorem heckeCuspForm_prime_pow (k : ℕ) (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r)
    (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk (p ^ (r + 1)) (Nat.one_le_pow _ _ hp.pos) f =
      heckeCuspForm k hk p hp.one_lt.le (heckeCuspForm k hk (p ^ r) (Nat.one_le_pow _ _ hp.pos) f) -
        ((p : ℂ) ^ (k - 1)) • heckeCuspForm k hk (p ^ (r - 1)) (Nat.one_le_pow _ _ hp.pos) f := by
  apply cuspForm_eq_of_qExpansion_coeff_eq
  intro j
  rw [qExpansionCoeff_sub, qExpansionCoeff_smul, qExpansionCoeff, qExpansionCoeff, qExpansionCoeff,
    heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff, heckeCuspForm_qExpansion_coeff]
  have h1 : (fun i => PowerSeries.coeff i
      (UpperHalfPlane.qExpansion 1 (heckeCuspForm k hk (p ^ r) (Nat.one_le_pow _ _ hp.pos) f : UpperHalfPlane → ℂ))) =
      heckeOp k (1 : DirichletCharacter ℂ 1) (p ^ r) (qExpansionCoeff f) := by
    funext i; exact heckeCuspForm_qExpansion_coeff k hk (p ^ r) (Nat.one_le_pow _ _ hp.pos) f i
  rw [h1]
  have hrec := congrFun (heckeOp_prime_pow_recurrence k (1 : DirichletCharacter ℂ 1) hp hr
    (qExpansionCoeff f)) j
  have hchi : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime p 1).mpr (Nat.coprime_one_right p))
  rw [hchi, one_mul] at hrec
  exact hrec

/-! ### Part 2B: `GL₂⁺(ℝ)`-Invariance of the Hyperbolic Measure `y^{-2} dx dy` on `ℂ` -/

/-- The open upper half-plane as a subset of `ℂ`. -/
def uhpC : Set ℂ := { z : ℂ | 0 < z.im }

theorem isOpen_uhpC : IsOpen uhpC :=
  isOpen_lt continuous_const Complex.continuous_im

theorem measurableSet_uhpC : MeasurableSet uhpC :=
  isOpen_uhpC.measurableSet

/-- Standard closed fundamental domain as a subset of `ℂ`. -/
def stdFD_C : Set ℂ := Complex.measurableEquivRealProd ⁻¹' stdFD

/-- Standard open fundamental domain as a subset of `ℂ`. -/
def stdFDO_C : Set ℂ := Complex.measurableEquivRealProd ⁻¹' stdFDO

theorem isOpen_stdFDO_C : IsOpen stdFDO_C :=
  isOpen_stdFDO.preimage Complex.equivRealProdCLM.continuous

theorem measurableSet_stdFD_C : MeasurableSet stdFD_C :=
  measurableSet_stdFD.preimage Complex.measurableEquivRealProd.measurable

theorem measurableSet_stdFDO_C : MeasurableSet stdFDO_C :=
  isOpen_stdFDO_C.measurableSet

theorem stdFDO_C_subset_stdFD_C : stdFDO_C ⊆ stdFD_C :=
  Set.preimage_mono stdFDO_subset_stdFD

theorem stdFD_C_subset_uhpC : stdFD_C ⊆ uhpC :=
  fun _ hz => hz.2.1

theorem stdFDO_C_subset_uhpC : stdFDO_C ⊆ uhpC :=
  fun _ hz => hz.2.1

/-- The boundary `stdFD_C \ stdFDO_C` has Lebesgue measure `0` in `ℂ`. -/
theorem volume_stdFD_C_diff_stdFDO_C : volume (stdFD_C \ stdFDO_C) = 0 := by
  have hsub : stdFD_C \ stdFDO_C ⊆
      { z : ℂ | z.re = 1 / 2 } ∪ { z : ℂ | z.re = -1 / 2 } ∪ Metric.sphere (0 : ℂ) 1 := by
    intro z ⟨hfd, hnot⟩
    by_cases h1 : |z.re| = 1 / 2
    · rcases eq_or_eq_neg_of_abs_eq h1 with hpos | hneg
      · exact Or.inl (Or.inl hpos)
      · exact Or.inl (Or.inr (by change z.re = -1 / 2; rw [hneg]; ring))
    · have hre_lt : |z.re| < 1 / 2 := lt_of_le_of_ne hfd.1 h1
      have hsq_eq : z.re ^ 2 + z.im ^ 2 = 1 := by
        by_contra hne
        have hgt : 1 < z.re ^ 2 + z.im ^ 2 := lt_of_le_of_ne hfd.2.2 (Ne.symm hne)
        exact hnot ⟨hre_lt, hfd.2.1, hgt⟩
      right
      rw [Metric.mem_sphere, dist_zero_right]
      have hnsq : Complex.normSq z = 1 := by
        rw [Complex.normSq_apply]; nlinarith
      have hnorm_sq : ‖z‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq, hnsq]
      nlinarith [norm_nonneg z]
  have hline : ∀ c : ℝ, volume ({ z : ℂ | z.re = c }) = 0 := by
    intro c
    have hpre : { z : ℂ | z.re = c } =
        Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
      ext z; simp [Complex.measurableEquivRealProd_apply]
    rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (MeasurableSet.prod (measurableSet_singleton c) MeasurableSet.univ).nullMeasurableSet,
      Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hsphere : volume (Metric.sphere (0 : ℂ) 1) = 0 :=
    MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) 1
  have hunion : volume ({ z : ℂ | z.re = 1 / 2 } ∪ { z : ℂ | z.re = -1 / 2 } ∪
      Metric.sphere (0 : ℂ) 1) = 0 := by
    refine le_antisymm ?_ bot_le
    calc volume (({ z : ℂ | z.re = 1 / 2 } ∪ { z : ℂ | z.re = -1 / 2 }) ∪ Metric.sphere (0 : ℂ) 1)
        ≤ volume ({ z : ℂ | z.re = 1 / 2 } ∪ { z : ℂ | z.re = -1 / 2 }) +
            volume (Metric.sphere (0 : ℂ) 1) := measure_union_le _ _
      _ ≤ (volume { z : ℂ | z.re = 1 / 2 } + volume { z : ℂ | z.re = -1 / 2 }) +
            volume (Metric.sphere (0 : ℂ) 1) := by gcongr; exact measure_union_le _ _
      _ = 0 := by rw [hline (1 / 2), hline (-1 / 2), hsphere]; simp
  exact measure_mono_null hsub hunion

theorem stdFDO_C_ae_eq_stdFD_C : (stdFDO_C : Set ℂ) =ᵐ[volume] stdFD_C := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨measure_mono_null (Set.sdiff_eq_empty.mpr stdFDO_C_subset_stdFD_C).subset (by simp),
    volume_stdFD_C_diff_stdFDO_C⟩

/-- Möbius transformation `z ↦ (a z + b) / (c z + d)` on `ℂ` for `g : GL (Fin 2) ℝ`. -/
def mobiusC (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((g 0 0 : ℝ) * z + (g 0 1 : ℝ)) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ))

theorem mobiusC_eq_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) {z : ℂ} (hz : z ∈ uhpC) :
    mobiusC g z = ((g • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos hg (⟨z, hz⟩ : UpperHalfPlane)]
  rfl

theorem mobiusC_mem_uhpC {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) {z : ℂ} (hz : z ∈ uhpC) :
    mobiusC g z ∈ uhpC := by
  rw [mobiusC_eq_smul hg hz]
  exact (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos

theorem mobiusC_mul {g₁ g₂ : GL (Fin 2) ℝ} (hg₁ : 0 < g₁.det.val) (hg₂ : 0 < g₂.det.val)
    {z : ℂ} (hz : z ∈ uhpC) :
    mobiusC (g₁ * g₂) z = mobiusC g₁ (mobiusC g₂ z) := by
  have hg12 : 0 < (g₁ * g₂).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hg₁ hg₂
  have hz2 : mobiusC g₂ z ∈ uhpC := mobiusC_mem_uhpC hg₂ hz
  rw [mobiusC_eq_smul hg12 hz, mobiusC_eq_smul hg₁ hz2]
  have hpt : (⟨mobiusC g₂ z, hz2⟩ : UpperHalfPlane) = g₂ • (⟨z, hz⟩ : UpperHalfPlane) := by
    apply UpperHalfPlane.ext
    exact mobiusC_eq_smul hg₂ hz
  rw [hpt, ← mul_smul]

theorem mobiusC_one {z : ℂ} (hz : z ∈ uhpC) : mobiusC (1 : GL (Fin 2) ℝ) z = z := by
  rw [mobiusC_eq_smul (by simp : (0 : ℝ) < (1 : GL (Fin 2) ℝ).det.val) hz, one_smul]

theorem mobiusC_injOn {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    Set.InjOn (mobiusC g) uhpC := by
  intro z₁ hz₁ z₂ hz₂ heq
  have h1 := mobiusC_eq_smul hg hz₁
  have h2 := mobiusC_eq_smul hg hz₂
  rw [h1, h2] at heq
  have hsmul : g • (⟨z₁, hz₁⟩ : UpperHalfPlane) = g • (⟨z₂, hz₂⟩ : UpperHalfPlane) :=
    UpperHalfPlane.ext heq
  have hinv := congrArg (g⁻¹ • ·) hsmul
  simp only [inv_smul_smul] at hinv
  exact congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) hinv

/-- Real determinant of complex multiplication `z ↦ w * z` as an `ℝ`-linear endomorphism of `ℂ`
equals `Complex.normSq w`. -/
private lemma det_complex_mul_restrictScalars (w : ℂ) :
    LinearMap.det
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ).toLinearMap) =
      Complex.normSq w := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  have hmat : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ).toLinearMap) =
      !![w.re, -w.im; w.im, w.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, Complex.basisOneI, Complex.mul_re, Complex.mul_im]
  rw [hmat, Matrix.det_fin_two, Complex.normSq_apply]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Real Fréchet derivative of `mobiusC g` at any `z ∈ uhpC` (`0 < det g`). -/
private lemma hasFDerivAt_mobiusC {g : GL (Fin 2) ℝ} (_hg : 0 < g.det.val)
    {z : ℂ} (hz : z ∈ uhpC) :
    HasFDerivAt (mobiusC g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ) z := by
  have hdenom_ne : ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero g (⟨z, hz⟩ : UpperHalfPlane)
  have hnum : HasDerivAt (fun u : ℂ => (g 0 0 : ℝ) * u + (g 0 1 : ℝ)) (g 0 0 : ℝ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ)).add_const ((g 0 1 : ℝ) : ℂ)
  have hden : HasDerivAt (fun u : ℂ => (g 1 0 : ℝ) * u + (g 1 1 : ℝ)) (g 1 0 : ℝ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ)).add_const ((g 1 1 : ℝ) : ℂ)
  have hdiv : HasDerivAt (mobiusC g)
      (((g 0 0 : ℝ) * ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) -
          ((g 0 0 : ℝ) * z + (g 0 1 : ℝ)) * (g 1 0 : ℝ)) /
        ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2) z :=
    hnum.div hden hdenom_ne
  have hnum_eq :
      ((g 0 0 : ℝ) * ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) -
        ((g 0 0 : ℝ) * z + (g 0 1 : ℝ)) * (g 1 0 : ℝ)) = (g.det.val : ℂ) := by
    have hdet : (g.det.val : ℝ) = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
      change (g : Matrix (Fin 2) (Fin 2) ℝ).det = _
      exact Matrix.det_fin_two _
    rw [hdet]
    push_cast
    ring
  rw [hnum_eq] at hdiv
  exact hdiv.hasFDerivAt.restrictScalars ℝ

/-- Exact Jacobian identity: `|det(D φ_g(z))| * (Im(φ_g(z)))^{-2} = (Im z)^{-2}` for all
`g ∈ GL₂⁺(ℝ)` and `z ∈ uhpC`. -/
private lemma abs_det_mobiusC_mul_im_inv_sq {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    {z : ℂ} (hz : z ∈ uhpC) :
    |LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| *
      (mobiusC g z).im ^ (-2 : ℤ) = z.im ^ (-2 : ℤ) := by
  rw [det_complex_mul_restrictScalars, abs_of_nonneg (Complex.normSq_nonneg _)]
  have him : (mobiusC g z).im =
      g.det.val * z.im / Complex.normSq ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) := by
    rw [mobiusC_eq_smul hg hz]
    have h := UpperHalfPlane.im_smul_eq_div_normSq g (⟨z, hz⟩ : UpperHalfPlane)
    rw [abs_of_pos hg] at h
    have himz : (⟨z, hz⟩ : UpperHalfPlane).im = z.im := rfl
    rw [himz] at h
    simpa [UpperHalfPlane.denom] using h
  have hdenom_ne : ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using UpperHalfPlane.denom_ne_zero g (⟨z, hz⟩ : UpperHalfPlane)
  have hnsq_pos : 0 < Complex.normSq ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) :=
    Complex.normSq_pos.mpr hdenom_ne
  have hdet_ne : g.det.val ≠ 0 := ne_of_gt hg
  have hz_ne : z.im ≠ 0 := ne_of_gt hz
  rw [him, Complex.normSq_div, Complex.normSq_ofReal, map_pow Complex.normSq]
  have hneg2 : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by
    rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by rfl, _root_.zpow_neg, zpow_natCast]
  rw [hneg2, hneg2]
  field_simp [hdet_ne, hz_ne, ne_of_gt hnsq_pos]

/-- **Unconditional `GL₂⁺(ℝ)`-Invariance of the Hyperbolic Bochner Integral** on `ℂ`:
for every `g : GL (Fin 2) ℝ` with `0 < det g`, every measurable `s ⊆ uhpC`, and every `F : ℂ → ℂ`,
$$\int_{w \in \varphi_g '' s} F(w)\, (\mathrm{Im}\, w)^{-2}\, dw =
  \int_{z \in s} F(\varphi_g(z))\, (\mathrm{Im}\, z)^{-2}\, dz.$$ -/
theorem integral_mobiusC_hyperbolic {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    {s : Set ℂ} (hs : MeasurableSet s) (hs_sub : s ⊆ uhpC) (F : ℂ → ℂ) :
    ∫ w in mobiusC g '' s, F w * ((w.im : ℂ) ^ (-2 : ℤ)) =
      ∫ z in s, F (mobiusC g z) * ((z.im : ℂ) ^ (-2 : ℤ)) := by
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt (mobiusC g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ) s z :=
    fun z hz => (hasFDerivAt_mobiusC hg (hs_sub hz)).hasFDerivWithinAt
  have hinj : Set.InjOn (mobiusC g) s := (mobiusC_injOn hg).mono hs_sub
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv hinj]
  refine setIntegral_congr_fun hs fun z hz => ?_
  have hjac := abs_det_mobiusC_mul_im_inv_sq hg (hs_sub hz)
  rw [Complex.real_smul]
  have hjacC : ((|LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| : ℝ) : ℂ) *
      ((mobiusC g z).im : ℂ) ^ (-2 : ℤ) = (z.im : ℂ) ^ (-2 : ℤ) := by
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) hjac
    simpa [Complex.ofReal_mul, Complex.ofReal_zpow] using h1
  calc ((|LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| : ℝ) : ℂ) *
        (F (mobiusC g z) * ((mobiusC g z).im : ℂ) ^ (-2 : ℤ))
      = F (mobiusC g z) *
        (((|LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| : ℝ) : ℂ) *
          ((mobiusC g z).im : ℂ) ^ (-2 : ℤ)) := by ring
    _ = F (mobiusC g z) * (z.im : ℂ) ^ (-2 : ℤ) := by rw [hjacC]

/-- Exact `IntegrableOn` counterpart of `integral_mobiusC_hyperbolic`. -/
theorem integrableOn_mobiusC_hyperbolic_iff {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    {s : Set ℂ} (hs : MeasurableSet s) (hs_sub : s ⊆ uhpC) (F : ℂ → ℂ) :
    IntegrableOn (fun w => F w * ((w.im : ℂ) ^ (-2 : ℤ))) (mobiusC g '' s) volume ↔
      IntegrableOn (fun z => F (mobiusC g z) * ((z.im : ℂ) ^ (-2 : ℤ))) s volume := by
  have hderiv : ∀ z ∈ s, HasFDerivWithinAt (mobiusC g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ) s z :=
    fun z hz => (hasFDerivAt_mobiusC hg (hs_sub hz)).hasFDerivWithinAt
  have hinj : Set.InjOn (mobiusC g) s := (mobiusC_injOn hg).mono hs_sub
  rw [MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hderiv hinj]
  refine integrableOn_congr_fun (fun z hz => ?_) hs
  have hjac := abs_det_mobiusC_mul_im_inv_sq hg (hs_sub hz)
  have hjacC : ((|LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| : ℝ) : ℂ) *
      ((mobiusC g z).im : ℂ) ^ (-2 : ℤ) = (z.im : ℂ) ^ (-2 : ℤ) := by
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) hjac
    simpa [Complex.ofReal_mul, Complex.ofReal_zpow] using h1
  rw [Complex.real_smul]
  calc ((|LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| : ℝ) : ℂ) *
        (F (mobiusC g z) * ((mobiusC g z).im : ℂ) ^ (-2 : ℤ))
      = F (mobiusC g z) *
        (((|LinearMap.det (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
          ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ).toLinearMap)| : ℝ) : ℂ) *
          ((mobiusC g z).im : ℂ) ^ (-2 : ℤ)) := by ring
    _ = F (mobiusC g z) * (z.im : ℂ) ^ (-2 : ℤ) := by rw [hjacC]

/-- Every `g ∈ GL₂⁺(ℝ)` maps Lebesgue-null subsets of `uhpC` to Lebesgue-null subsets of `uhpC`. -/
theorem volume_mobiusC_image_zero {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    {s : Set ℂ} (hs_sub : s ⊆ uhpC) (hs0 : volume s = 0) :
    volume (mobiusC g '' s) = 0 := by
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hs0
  let t' : Set ℂ := t ∩ uhpC
  have ht'_sub : t' ⊆ uhpC := Set.inter_subset_right
  have ht'_meas : MeasurableSet t' := htm.inter measurableSet_uhpC
  have ht'_zero : volume t' = 0 := measure_mono_null Set.inter_subset_left ht0
  have hst' : s ⊆ t' := Set.subset_inter hst hs_sub
  have hderiv : ∀ z ∈ t', HasFDerivWithinAt (mobiusC g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((g.det.val : ℂ) / ((g 1 0 : ℝ) * z + (g 1 1 : ℝ)) ^ 2)).restrictScalars ℝ) t' z :=
    fun z hz => (hasFDerivAt_mobiusC hg (ht'_sub hz)).hasFDerivWithinAt
  have hinj : Set.InjOn (mobiusC g) t' := (mobiusC_injOn hg).mono ht'_sub
  have hvol : volume (mobiusC g '' t') = 0 := by
    have hlint := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume ht'_meas
      hderiv hinj (fun _ => (1 : ℝ≥0∞))
    simp only [MeasureTheory.setLIntegral_one, mul_one] at hlint
    rw [hlint, MeasureTheory.setLIntegral_measure_zero t' _ ht'_zero]
  exact measure_mono_null (Set.image_mono hst') hvol

/-- Every `g ∈ GL₂⁺(ℝ)` maps open subsets of `uhpC` to open subsets of `uhpC` (since its inverse
`mobiusC g⁻¹` is continuous on `uhpC`). -/
theorem isOpen_mobiusC_image {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    {U : Set ℂ} (hU : IsOpen U) (hU_sub : U ⊆ uhpC) :
    IsOpen (mobiusC g '' U) := by
  have hg_inv : 0 < g⁻¹.det.val := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hg
  have hcont : ContinuousOn (mobiusC g⁻¹) uhpC := by
    intro z hz
    exact (hasFDerivAt_mobiusC hg_inv hz).continuousAt.continuousWithinAt
  have heq : mobiusC g '' U = uhpC ∩ mobiusC g⁻¹ ⁻¹' U := by
    ext w
    constructor
    · rintro ⟨z, hzU, rfl⟩
      refine ⟨mobiusC_mem_uhpC hg (hU_sub hzU), ?_⟩
      change mobiusC g⁻¹ (mobiusC g z) ∈ U
      rw [← mobiusC_mul hg_inv hg (hU_sub hzU), inv_mul_cancel, mobiusC_one (hU_sub hzU)]
      exact hzU
    · rintro ⟨hw, hwinv⟩
      refine ⟨mobiusC g⁻¹ w, hwinv, ?_⟩
      rw [← mobiusC_mul hg hg_inv hw, mul_inv_cancel, mobiusC_one hw]
  rw [heq]
  exact hcont.isOpen_inter_preimage isOpen_uhpC hU

theorem measurableSet_mobiusC_image {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val)
    {s : Set ℂ} (hs : MeasurableSet s) (hs_sub : s ⊆ uhpC) :
    MeasurableSet (mobiusC g '' s) := by
  have hg_inv : 0 < g⁻¹.det.val := by
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr hg
  have hcont : ContinuousOn (mobiusC g⁻¹) uhpC := fun z hz =>
    (hasFDerivAt_mobiusC hg_inv hz).continuousAt.continuousWithinAt
  have heq : mobiusC g '' s = uhpC ∩ mobiusC g⁻¹ ⁻¹' s := by
    ext w
    constructor
    · rintro ⟨z, hzs, rfl⟩
      refine ⟨mobiusC_mem_uhpC hg (hs_sub hzs), ?_⟩
      change mobiusC g⁻¹ (mobiusC g z) ∈ s
      rw [← mobiusC_mul hg_inv hg (hs_sub hzs), inv_mul_cancel, mobiusC_one (hs_sub hzs)]
      exact hzs
    · rintro ⟨hw, hwinv⟩
      refine ⟨mobiusC g⁻¹ w, hwinv, ?_⟩
      rw [← mobiusC_mul hg hg_inv hw, mul_inv_cancel, mobiusC_one hw]
  rw [heq]
  have hmeas_on : Measurable (fun x : uhpC => mobiusC g⁻¹ x.1) :=
    (hcont.comp_continuous continuous_subtype_val fun x => x.2).measurable
  have hpre : MeasurableSet (Subtype.val '' ((fun x : uhpC => mobiusC g⁻¹ x.1) ⁻¹' s)) :=
    (MeasurableEmbedding.subtype_coe measurableSet_uhpC).measurableSet_image.mpr (hmeas_on hs)
  have hset : Subtype.val '' ((fun x : uhpC => mobiusC g⁻¹ x.1) ⁻¹' s) =
      uhpC ∩ mobiusC g⁻¹ ⁻¹' s := by
    ext w; simp [Set.mem_inter_iff, and_comm]
  rwa [← hset]

/-- Rewrite `peterssonInner f g` as a hyperbolic integral over the open fundamental domain
`stdFDO_C ⊆ ℂ` using Mathlib's `UpperHalfPlane.petersson`. -/
theorem peterssonInner_eq_integral_stdFDO_C {k : ℤ} (f g : CuspForm SL2ZRange k) :
    peterssonInner f g =
      ∫ z in stdFDO_C,
        (if hz : 0 < z.im then UpperHalfPlane.petersson k g f ⟨z, hz⟩ else 0) *
          ((z.im : ℂ) ^ (-2 : ℤ)) := by
  unfold peterssonInner
  have hmp := Complex.volume_preserving_equiv_real_prod
  have h1 : ∫ p in stdFD, peterssonIntegrand f g p =
      ∫ z in stdFD_C, peterssonIntegrand f g (Complex.measurableEquivRealProd z) := by
    exact (hmp.setIntegral_preimage_emb Complex.measurableEquivRealProd.measurableEmbedding
      (peterssonIntegrand f g) stdFD).symm
  rw [h1, ← setIntegral_congr_set stdFDO_C_ae_eq_stdFD_C]
  refine setIntegral_congr_fun measurableSet_stdFDO_C fun z hz => ?_
  have hz0 : 0 < z.im := hz.2.1
  have hpair : pairToUHP (z.re, z.im) hz0 = ⟨z, hz0⟩ := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [pairToUHP]
  have hpow : (z.im : ℂ) ^ (k - 2) = (z.im : ℂ) ^ k * (z.im : ℂ) ^ (-2 : ℤ) := by
    rw [← zpow_add₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz0)), sub_eq_add_neg]
  change (if hp : 0 < z.im then f (pairToUHP (z.re, z.im) hp) *
      star (g (pairToUHP (z.re, z.im) hp)) * (z.im : ℂ) ^ (k - 2) else 0) = _
  rw [dif_pos hz0, dif_pos hz0, hpair, hpow]
  have himz : (⟨z, hz0⟩ : UpperHalfPlane).im = z.im := rfl
  simp only [UpperHalfPlane.petersson, Complex.star_def, himz]
  ring

/-! ### Part 2C: Fricke Involution `W_p`, `Γ₀(p)` Fundamental Domain Independence, &
Unconditional Self-Adjointness of Every Hecke Operator `T_n` -/

/-- The Fricke matrix `W_p = [[0, -1], [p, 0]] ∈ GL₂⁺(ℝ)` for `p > 0` (`det W_p = p`). -/
def frickeW (p : ℕ) (hp : 0 < p) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (p : ℝ), 0] (by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hpR : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
    linarith)

theorem frickeW_det (p : ℕ) (hp : 0 < p) : (frickeW p hp).det.val = (p : ℝ) := by
  change (!![(0 : ℝ), -1; (p : ℝ), 0] : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)
  simp [Matrix.det_fin_two]

theorem frickeW_det_pos (p : ℕ) (hp : 0 < p) : 0 < (frickeW p hp).det.val := by
  rw [frickeW_det]; exact Nat.cast_pos.mpr hp

/-- Canonical right-coset representatives for `Γ₀(p) \ SL₂(ℤ)`:
`δ_b = S⁻¹ T^b` for `0 ≤ b < p`, and `δ_p = 1`. -/
def gamma0CosetRep (p : ℕ) (j : Fin (p + 1)) : SL(2, ℤ) :=
  if j.1 < p then ModularGroup.S⁻¹ * ModularGroup.T ^ (j.1 : ℤ) else 1

private lemma sl2Z_T_zpow_matrix (b : ℤ) :
    ((ModularGroup.T ^ b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, b; 0, 1] := by
  exact ModularGroup.coe_T_zpow b

private lemma sl2Z_S_inv_matrix :
    ((ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  have hmul : (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; -1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : (ModularGroup.S : SL(2, ℤ)) * ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ = 1 := by
    ext i j; exact congrFun (congrFun hmul i) j
  have h2 : (ModularGroup.S⁻¹ : SL(2, ℤ)) = ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ :=
    eq_inv_of_mul_eq_one_right h1 |>.symm
  rw [h2]

private lemma frickeW_mul_cosetRep_lt (p : ℕ) (hp : 0 < p) (b : ℕ) (_hb : b < p) :
    frickeW p hp * sl2ZToGL2R (ModularGroup.S⁻¹ * ModularGroup.T ^ (b : ℤ)) =
      heckeMat 1 b p zero_lt_one hp := by
  apply Units.ext
  have hsl : ((sl2ZToGL2R (ModularGroup.S⁻¹ * ModularGroup.T ^ (b : ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      (((ModularGroup.S⁻¹ * ModularGroup.T ^ (b : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.cast : ℤ → ℝ)) := rfl
  rw [Units.val_mul, hsl, Matrix.SpecialLinearGroup.coe_mul, sl2Z_S_inv_matrix, sl2Z_T_zpow_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeW, heckeMat, Matrix.mul_apply, Fin.sum_univ_two]

private lemma frickeW_eq_S_mul_heckeMat (p : ℕ) (hp : 0 < p) :
    frickeW p hp = sl2ZToGL2R ModularGroup.S * heckeMat p 0 1 hp zero_lt_one := by
  apply Units.ext
  have hsl : ((sl2ZToGL2R ModularGroup.S : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) := rfl
  rw [Units.val_mul, hsl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeW, heckeMat, ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]

/-- For every prime `p` and every `f ∈ CuspForm SL2ZRange k`, the Hecke operator `T_p f` decomposes
as the sum of `(f |_k W_p) |_k δ_j` over the `p + 1` coset reps `δ_j ∈ Γ₀(p) \ SL₂(ℤ)`! -/
theorem heckeCuspForm_prime_eq_sum_frickeW {k : ℕ} (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime)
    (f : CuspForm SL2ZRange (k : ℤ)) (τ : UpperHalfPlane) :
    heckeCuspForm k hk p hp.one_lt.le f τ =
      ∑ j : Fin (p + 1),
        SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j))
          (SlashAction.map (k : ℤ) (frickeW p hp.pos) (f : UpperHalfPlane → ℂ)) τ := by
  rw [heckeCuspForm_coe, slashHeckeOp_levelOne_eq_sum_cosets k p (f : UpperHalfPlane → ℂ) τ]
  have hdiv : p.divisors = {1, p} := hp.divisors
  have h1nep : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [heckeCosets, Finset.sum_sigma, hdiv, Finset.sum_pair h1nep]
  simp only [Nat.div_one, Nat.div_self hp.pos, Finset.range_one, Finset.sum_singleton]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · symm
    simp only [gamma0CosetRep, Fin.val_castSucc]
    rw [Fin.sum_univ_eq_sum_range (fun b =>
      SlashAction.map (k : ℤ) (sl2ZToGL2R (if b < p then ModularGroup.S⁻¹ * ModularGroup.T ^ (b : ℤ) else 1))
        (SlashAction.map (k : ℤ) (frickeW p hp.pos) (f : UpperHalfPlane → ℂ)) τ) p]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hblt : b < p := Finset.mem_range.mp hb
    simp only [if_pos hblt, dif_pos (And.intro zero_lt_one hp.pos)]
    have hsl := SlashAction.slash_mul (k : ℤ) (frickeW p hp.pos)
      (sl2ZToGL2R (ModularGroup.S⁻¹ * ModularGroup.T ^ (b : ℤ))) (f : UpperHalfPlane → ℂ)
    rw [← hsl, frickeW_mul_cosetRep_lt p hp.pos b hblt]
  · simp only [gamma0CosetRep, Fin.val_last, lt_self_iff_false, ↓reduceIte,
      dif_pos (And.intro hp.pos zero_lt_one)]
    have h1 : sl2ZToGL2R (1 : SL(2, ℤ)) = 1 := map_one _
    rw [h1, SlashAction.slash_one, frickeW_eq_S_mul_heckeMat p hp.pos, SlashAction.slash_mul]
    have hfS : SlashAction.map (k : ℤ) (sl2ZToGL2R ModularGroup.S) (f : UpperHalfPlane → ℂ) =
        (f : UpperHalfPlane → ℂ) := f.slash_action_eq' _ ⟨ModularGroup.S, rfl⟩
    rw [hfS]

/-- Involution identity `(f |_k W_p) |_k W_p = p^{k - 2} • f` for every even `k` and `p > 0`. -/
theorem slash_frickeW_frickeW {k : ℕ} (heven : Even k) {p : ℕ} (hp : 0 < p)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    SlashAction.map (k : ℤ) (frickeW p hp) (SlashAction.map (k : ℤ) (frickeW p hp) f) τ =
      ((p : ℂ) ^ ((k : ℤ) - 2)) * f τ := by
  rw [← SlashAction.slash_mul]
  have hW2 : (frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-(p : ℝ), 0; 0, -(p : ℝ)] := by
    change (!![(0 : ℝ), -1; (p : ℝ), 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        !![(0 : ℝ), -1; (p : ℝ), 0] = _
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdetW2 : (frickeW p hp * frickeW p hp).det.val = (p : ℝ) ^ 2 := by
    rw [map_mul, Units.val_mul, frickeW_det]; ring
  have hdet_pos : 0 < (frickeW p hp * frickeW p hp).det.val := by
    rw [hdetW2]; positivity
  have hsmul : (frickeW p hp * frickeW p hp) • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet_pos]
    change ((((frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) * (τ : ℂ) +
        ((frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ)) /
      (((frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) * (τ : ℂ) +
        ((frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ))) = (τ : ℂ)
    rw [hW2]
    have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
    simp [mul_div_cancel_left₀ _ hpC]
  have hdenom : UpperHalfPlane.denom (frickeW p hp * frickeW p hp) τ = -(p : ℂ) := by
    change (((frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) * (τ : ℂ) +
        ((frickeW p hp * frickeW p hp : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ)) = -(p : ℂ)
    rw [hW2]; simp
  rw [ModularForm.slash_def, UpperHalfPlane.σ, if_pos hdet_pos]
  change f ((frickeW p hp * frickeW p hp) • τ) *
      ((|(frickeW p hp * frickeW p hp).det.val| : ℝ) : ℂ) ^ ((k : ℤ) - 1) *
      UpperHalfPlane.denom (frickeW p hp * frickeW p hp) τ ^ (-(k : ℤ)) = _
  rw [hsmul, hdenom, abs_of_pos hdet_pos, hdetW2]
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  have hneg_pow : (-(p : ℂ)) ^ (-(k : ℤ)) = (p : ℂ) ^ (-(k : ℤ)) := by
    rcases heven with ⟨m, rfl⟩
    have hm : (-((m + m : ℕ) : ℤ)) = -((2 * m : ℕ) : ℤ) := by push_cast; ring
    rw [hm, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, pow_mul, pow_mul]
    simp [sq]
  rw [hneg_pow]
  have hdet_pow : (((p : ℝ) ^ 2 : ℝ) : ℂ) ^ ((k : ℤ) - 1) = (p : ℂ) ^ (2 * ((k : ℤ) - 1)) := by
    push_cast
    rw [← zpow_natCast (p : ℂ) 2, ← _root_.zpow_mul]
    rfl
  rw [hdet_pow, mul_assoc, ← zpow_add₀ hpC]
  have hexp : 2 * ((k : ℤ) - 1) + -(k : ℤ) = (k : ℤ) - 2 := by ring
  rw [hexp, mul_comm]

/-- **Pointwise Fricke Swap Identity**: for every even `k`, `p > 0`, and `f, g : ℍ → ℂ`,
`petersson k g (f |_k W_p) τ = petersson k (g |_k W_p) f (W_p • τ)`! -/
theorem petersson_frickeW_swap {k : ℕ} (heven : Even k) {p : ℕ} (hp : 0 < p)
    (f g : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) g (SlashAction.map (k : ℤ) (frickeW p hp) f) τ =
      UpperHalfPlane.petersson (k : ℤ) (SlashAction.map (k : ℤ) (frickeW p hp) g) f
        (frickeW p hp • τ) := by
  have h := UpperHalfPlane.petersson_slash (k : ℤ)
    (SlashAction.map (k : ℤ) (frickeW p hp) g) f (frickeW p hp) τ
  have hdet := frickeW_det p hp
  have hdet_pos := frickeW_det_pos p hp
  rw [UpperHalfPlane.σ, if_pos hdet_pos, abs_of_pos hdet_pos, hdet] at h
  change UpperHalfPlane.petersson (k : ℤ)
      (SlashAction.map (k : ℤ) (frickeW p hp) (SlashAction.map (k : ℤ) (frickeW p hp) g))
      (SlashAction.map (k : ℤ) (frickeW p hp) f) τ =
    (((p : ℝ) : ℂ) ^ ((k : ℤ) - 2)) *
      UpperHalfPlane.petersson (k : ℤ) (SlashAction.map (k : ℤ) (frickeW p hp) g) f
        (frickeW p hp • τ) at h
  have hlhs : UpperHalfPlane.petersson (k : ℤ)
      (SlashAction.map (k : ℤ) (frickeW p hp) (SlashAction.map (k : ℤ) (frickeW p hp) g))
      (SlashAction.map (k : ℤ) (frickeW p hp) f) τ =
      ((p : ℂ) ^ ((k : ℤ) - 2)) *
        UpperHalfPlane.petersson (k : ℤ) g (SlashAction.map (k : ℤ) (frickeW p hp) f) τ := by
    simp only [UpperHalfPlane.petersson, slash_frickeW_frickeW heven hp g τ,
      map_mul, map_zpow₀, map_natCast]
    ring
  rw [hlhs] at h
  have hne : ((p : ℂ) ^ ((k : ℤ) - 2)) ≠ 0 :=
    zpow_ne_zero _ (Nat.cast_ne_zero.mpr (ne_of_gt hp))
  exact mul_left_cancel₀ hne (by simpa [Complex.ofReal_natCast] using h)

/-- Conjugation by `W_p` sends every `h ∈ Γ₀(p)` to an element `frickeConj p h ∈ Γ₀(p)`. -/
def frickeConj (p : ℕ) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ h 1 0) : SL(2, ℤ) :=
  ⟨!![h 1 1, -(h 1 0 / (p : ℤ)); -(p : ℤ) * h 0 1, h 0 0], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hmul : (h 1 0 / (p : ℤ)) * (p : ℤ) = h 1 0 := Int.ediv_mul_cancel hh
    have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
      have hp' := h.prop
      rwa [Matrix.det_fin_two] at hp'
    calc h 1 1 * h 0 0 - -(h 1 0 / (p : ℤ)) * (-(p : ℤ) * h 0 1)
        = h 0 0 * h 1 1 - h 0 1 * ((h 1 0 / (p : ℤ)) * (p : ℤ)) := by ring
      _ = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by rw [hmul]
      _ = 1 := hdet⟩

theorem frickeConj_mem_gamma0 (p : ℕ) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ h 1 0) :
    (p : ℤ) ∣ (frickeConj p h hh) 1 0 :=
  ⟨-(h 0 1), by change -(p : ℤ) * h 0 1 = (p : ℤ) * -(h 0 1); ring⟩

theorem frickeW_mul_eq_frickeConj_mul_frickeW (p : ℕ) (hp : 0 < p) (h : SL(2, ℤ))
    (hh : (p : ℤ) ∣ h 1 0) :
    frickeW p hp * sl2ZToGL2R h = sl2ZToGL2R (frickeConj p h hh) * frickeW p hp := by
  apply Units.ext
  have hmul : (p : ℤ) * (h 1 0 / (p : ℤ)) = h 1 0 := Int.mul_ediv_cancel' hh
  have hmulR : (p : ℝ) * ((h 1 0 / (p : ℤ) : ℤ) : ℝ) = (h 1 0 : ℝ) := by exact_mod_cast hmul
  change (!![(0 : ℝ), -1; (p : ℝ), 0] : Matrix (Fin 2) (Fin 2) ℝ) *
      ((h : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) =
      (((frickeConj p h hh : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) *
      !![(0 : ℝ), -1; (p : ℝ), 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeConj, Matrix.mul_apply, Fin.sum_univ_two]
  · linarith
  · ring

/-- `petersson k (g |_k W_p) f` is `Γ₀(p)`-invariant! -/
theorem petersson_frickeW_gamma0_invariant {k : ℕ} {p : ℕ} (hp : 0 < p)
    (f g : CuspForm SL2ZRange (k : ℤ)) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ h 1 0)
    (τ : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) (SlashAction.map (k : ℤ) (frickeW p hp) (g : UpperHalfPlane → ℂ))
        f (h • τ) =
      UpperHalfPlane.petersson (k : ℤ) (SlashAction.map (k : ℤ) (frickeW p hp) (g : UpperHalfPlane → ℂ))
        f τ := by
  have hgW : SlashAction.map (k : ℤ) (sl2ZToGL2R h)
      (SlashAction.map (k : ℤ) (frickeW p hp) (g : UpperHalfPlane → ℂ)) =
      SlashAction.map (k : ℤ) (frickeW p hp) (g : UpperHalfPlane → ℂ) := by
    rw [← SlashAction.slash_mul, frickeW_mul_eq_frickeConj_mul_frickeW p hp h hh,
      SlashAction.slash_mul]
    have hg' := g.slash_action_eq' _ ⟨frickeConj p h hh, rfl⟩
    change SlashAction.map (k : ℤ) (sl2ZToGL2R (frickeConj p h hh)) (g : UpperHalfPlane → ℂ) =
      (g : UpperHalfPlane → ℂ) at hg'
    rw [hg']
  have hf' : SlashAction.map (k : ℤ) (sl2ZToGL2R h) (f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) := f.slash_action_eq' _ ⟨h, rfl⟩
  have hps := UpperHalfPlane.petersson_slash_SL (k : ℤ)
    (SlashAction.map (k : ℤ) (frickeW p hp) (g : UpperHalfPlane → ℂ)) f h τ
  rw [← hps]
  change UpperHalfPlane.petersson (k : ℤ)
      (SlashAction.map (k : ℤ) (sl2ZToGL2R h)
        (SlashAction.map (k : ℤ) (frickeW p hp) (g : UpperHalfPlane → ℂ)))
      (SlashAction.map (k : ℤ) (sl2ZToGL2R h) (f : UpperHalfPlane → ℂ)) τ = _
  rw [hgW, hf']

/-- Canonical positive half of `SL₂(ℤ)` (selecting one representative from each `{γ, -γ}`). -/
def SL2ZPlus : Set SL(2, ℤ) :=
  { γ : SL(2, ℤ) | 0 < γ 1 0 ∨ (γ 1 0 = 0 ∧ 0 < γ 0 0) }

private lemma sl2Z_mem_plus_or_neg (γ : SL(2, ℤ)) : γ ∈ SL2ZPlus ∨ -γ ∈ SL2ZPlus := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hp' := γ.prop
    rwa [Matrix.det_fin_two] at hp'
  rcases lt_trichotomy (γ 1 0) 0 with hlt | heq | hgt
  · right; left; change 0 < -(γ 1 0); omega
  · have ha_ne : γ 0 0 ≠ 0 := by intro h0; rw [h0, heq] at hdet; norm_num at hdet
    rcases lt_or_gt_of_ne ha_ne with ha_lt | ha_gt
    · right; right; exact ⟨by change -(γ 1 0) = 0; omega, by change 0 < -(γ 0 0); omega⟩
    · left; right; exact ⟨heq, ha_gt⟩
  · left; left; exact hgt

private lemma sl2Z_neg_not_mem_plus {γ : SL(2, ℤ)} (h : γ ∈ SL2ZPlus) : -γ ∉ SL2ZPlus := by
  intro hneg
  rcases h with h1 | ⟨h1, h2⟩
  · rcases hneg with hn1 | ⟨hn1, _⟩ <;> (change _ at hn1; simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hn1; omega)
  · rcases hneg with hn1 | ⟨_, hn2⟩
    · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hn1; omega
    · simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] at hn2; omega

private lemma mobiusC_neg_sl2Z (γ : SL(2, ℤ)) {z : ℂ} (hz : z ∈ uhpC) :
    mobiusC (sl2ZToGL2R (-γ)) z = mobiusC (sl2ZToGL2R γ) z := by
  have hz' : 0 < z.im := hz
  have hneg : sl2ZToGL2R (-γ) = -(sl2ZToGL2R γ) := by
    apply Units.ext; ext i j; simp [sl2ZToGL2R]
  have hdet1 : 0 < (sl2ZToGL2R (-γ)).det.val := by simp [sl2ZToGL2R]
  have hdet2 : 0 < (sl2ZToGL2R γ).det.val := by simp [sl2ZToGL2R]
  rw [mobiusC_eq_smul hdet1 hz', mobiusC_eq_smul hdet2 hz', hneg]
  exact congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) (UpperHalfPlane.neg_smul (sl2ZToGL2R γ) ⟨z, hz'⟩)

/-- Every `γ ∈ SL₂(ℤ)` belongs to a unique right coset `Γ₀(p) * gamma0CosetRep p j` for prime `p`. -/
private lemma exists_unique_gamma0_coset {p : ℕ} (hp : p.Prime) (γ : SL(2, ℤ)) :
    ∃ (j : Fin (p + 1)) (h : SL(2, ℤ)), (p : ℤ) ∣ h 1 0 ∧ γ = h * gamma0CosetRep p j := by
  by_cases hdiv : (p : ℤ) ∣ γ 1 0
  · refine ⟨⟨p, Nat.lt_succ_self p⟩, γ, hdiv, ?_⟩
    simp [gamma0CosetRep]
  · -- `p ∤ c`, so `c` is invertible mod `p`; pick `b ∈ {0, ..., p-1}` with `b * c ≡ d (mod p)`.
    have hpZ : (0 : ℤ) < (p : ℤ) := Int.natCast_pos.mpr hp.pos
    have hcop : IsCoprime (γ 1 0) (p : ℤ) := by
      apply Int.isCoprime_iff_gcd_eq_one.mpr
      have hdvd_or := (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hdiv (Int.natCast_dvd.mpr h))
      have h1 : Nat.Coprime (γ 1 0).natAbs p := Nat.coprime_comm.mp hdvd_or
      simpa [Int.gcd] using h1
    rcases hcop with ⟨u, v, huv⟩
    -- `(u * d) * c ≡ d (mod p)`
    let bZ : ℤ := (u * γ 1 1) % (p : ℤ)
    have hbZ_nn : 0 ≤ bZ := Int.emod_nonneg _ (ne_of_gt hpZ)
    have hbZ_lt : bZ < (p : ℤ) := Int.emod_lt_of_pos _ hpZ
    let b : ℕ := bZ.toNat
    have hb_cast : (b : ℤ) = bZ := Int.toNat_of_nonneg hbZ_nn
    have hb_lt : b < p := by
      have : (b : ℤ) < (p : ℤ) := by rw [hb_cast]; exact hbZ_lt
      exact_mod_cast this
    let j : Fin (p + 1) := ⟨b, Nat.lt_succ_of_lt hb_lt⟩
    let h : SL(2, ℤ) := γ * (gamma0CosetRep p j)⁻¹
    refine ⟨j, h, ?_, by simp [h]⟩
    have hj_eq : gamma0CosetRep p j = ModularGroup.S⁻¹ * ModularGroup.T ^ (b : ℤ) := by
      simp [gamma0CosetRep, j, hb_lt]
    have hinv_mat : (((gamma0CosetRep p j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![-(b : ℤ), -1; 1, 0] := by
      rw [hj_eq, _root_.mul_inv_rev, inv_inv, ← _root_.zpow_neg, Matrix.SpecialLinearGroup.coe_mul,
        sl2Z_T_zpow_matrix]
      ext r c; fin_cases r <;> fin_cases c <;>
        simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
    have hh10 : h 1 0 = -(b : ℤ) * γ 1 0 + γ 1 1 := by
      change ((γ * (gamma0CosetRep p j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
      rw [Matrix.SpecialLinearGroup.coe_mul, hinv_mat]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [hh10, hb_cast]
    have hmod_eq : (p : ℤ) ∣ (u * γ 1 1 - bZ) := by
      refine ⟨(u * γ 1 1) / (p : ℤ), ?_⟩
      have := Int.mul_ediv_add_emod (u * γ 1 1) (p : ℤ)
      linarith
    rcases hmod_eq with ⟨q, hq⟩
    refine ⟨q * γ 1 0 + v * γ 1 1, ?_⟩
    calc -bZ * γ 1 0 + γ 1 1
        = -(u * γ 1 1 - (p : ℤ) * q) * γ 1 0 + (u * γ 1 0 + v * (p : ℤ)) * γ 1 1 := by
            rw [← hq, huv, one_mul]; ring
      _ = (p : ℤ) * (q * γ 1 0 + v * γ 1 1) := by ring

/-- Distinct right-coset representatives `gamma0CosetRep p j₁` and `gamma0CosetRep p j₂` lie in
distinct `Γ₀(p)` right cosets for any `p > 1`. -/
private lemma gamma0_coset_eq_of_dvd {p : ℕ} (hp : 1 < p) {j₁ j₂ : Fin (p + 1)}
    {h : SL(2, ℤ)} (hh : (p : ℤ) ∣ h 1 0) (heq : gamma0CosetRep p j₁ = h * gamma0CosetRep p j₂) :
    j₁ = j₂ := by
  have hprod : (gamma0CosetRep p j₁ * (gamma0CosetRep p j₂)⁻¹) 1 0 = h 1 0 := by
    have : gamma0CosetRep p j₁ * (gamma0CosetRep p j₂)⁻¹ = h := by rw [heq, mul_inv_cancel_right]
    rw [this]
  have hdvd : (p : ℤ) ∣ (gamma0CosetRep p j₁ * (gamma0CosetRep p j₂)⁻¹) 1 0 := by
    rw [hprod]; exact hh
  have hpZ : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  by_cases h1 : j₁.1 < p <;> by_cases h2 : j₂.1 < p
  · have hmat1 : ((gamma0CosetRep p j₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![0, 1; -1, -(j₁.1 : ℤ)] := by
      simp only [gamma0CosetRep, if_pos h1]
      rw [Matrix.SpecialLinearGroup.coe_mul, sl2Z_S_inv_matrix, sl2Z_T_zpow_matrix]
      ext r c; fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hmat2 : (((gamma0CosetRep p j₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![-(j₂.1 : ℤ), -1; 1, 0] := by
      have hj2 : gamma0CosetRep p j₂ = ModularGroup.S⁻¹ * ModularGroup.T ^ (j₂.1 : ℤ) := by
        simp [gamma0CosetRep, if_pos h2]
      rw [hj2, _root_.mul_inv_rev, inv_inv, ← _root_.zpow_neg, Matrix.SpecialLinearGroup.coe_mul,
        sl2Z_T_zpow_matrix]
      ext r c; fin_cases r <;> fin_cases c <;>
        simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
    have h10 : (gamma0CosetRep p j₁ * (gamma0CosetRep p j₂)⁻¹) 1 0 = (j₂.1 : ℤ) - (j₁.1 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hmat1, hmat2]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    rw [h10] at hdvd
    rcases hdvd with ⟨q, hq⟩
    have hj1 : (j₁.1 : ℤ) < (p : ℤ) := by exact_mod_cast h1
    have hj2 : (j₂.1 : ℤ) < (p : ℤ) := by exact_mod_cast h2
    have hq0 : q = 0 := by nlinarith
    have hval : j₁.1 = j₂.1 := by
      have : (j₂.1 : ℤ) = (j₁.1 : ℤ) := by rw [hq0, mul_zero] at hq; omega
      exact_mod_cast this.symm
    exact Fin.ext hval
  · exfalso
    have hj2 : gamma0CosetRep p j₂ = 1 := by simp [gamma0CosetRep, h2]
    have hmat1 : ((gamma0CosetRep p j₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![0, 1; -1, -(j₁.1 : ℤ)] := by
      simp only [gamma0CosetRep, if_pos h1]
      rw [Matrix.SpecialLinearGroup.coe_mul, sl2Z_S_inv_matrix, sl2Z_T_zpow_matrix]
      ext r c; fin_cases r <;> fin_cases c <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hj2, inv_one, mul_one] at hdvd
    have h10 : (gamma0CosetRep p j₁) 1 0 = -1 := by
      rw [hmat1]; simp
    rw [h10] at hdvd
    rcases hdvd with ⟨q, hq⟩
    have hq0 : q = 0 := by nlinarith
    rw [hq0, mul_zero] at hq; omega
  · exfalso
    have hj1 : gamma0CosetRep p j₁ = 1 := by simp [gamma0CosetRep, h1]
    have hmat2 : (((gamma0CosetRep p j₂)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![-(j₂.1 : ℤ), -1; 1, 0] := by
      have hj2 : gamma0CosetRep p j₂ = ModularGroup.S⁻¹ * ModularGroup.T ^ (j₂.1 : ℤ) := by
        simp [gamma0CosetRep, if_pos h2]
      rw [hj2, _root_.mul_inv_rev, inv_inv, ← _root_.zpow_neg, Matrix.SpecialLinearGroup.coe_mul,
        sl2Z_T_zpow_matrix]
      ext r c; fin_cases r <;> fin_cases c <;>
        simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hj1, one_mul] at hdvd
    have h10 : ((gamma0CosetRep p j₂)⁻¹) 1 0 = 1 := by
      rw [hmat2]; simp
    rw [h10] at hdvd
    rcases hdvd with ⟨q, hq⟩
    have hq0 : q = 0 := by nlinarith
    rw [hq0, mul_zero] at hq; omega
  · have hval : j₁.1 = j₂.1 := by have := j₁.2; have := j₂.2; omega
    exact Fin.ext hval

/-- `SL(2, ℤ)` is countable (via its 4 integer matrix entries). -/
private instance instCountableSL2Z : Countable SL(2, ℤ) :=
  Function.Injective.countable
    (f := fun g : SL(2, ℤ) => ((g 0 0, g 0 1), (g 1 0, g 1 1)))
    (fun g₁ g₂ h => by
      simp only [Prod.mk.injEq] at h
      ext r c
      fin_cases r <;> fin_cases c <;> tauto)

/-- The positive half of `Γ₀(p)` inside `SL₂(ℤ)`. -/
def Gamma0Plus (p : ℕ) : Set SL(2, ℤ) :=
  { h : SL(2, ℤ) | (p : ℤ) ∣ h 1 0 ∧ h ∈ SL2ZPlus }

/-- Open fundamental domain `D_p = ⋃_{j : Fin (p + 1)} δ_j • stdFDO_C` for `Γ₀(p)`. -/
def gamma0FD (p : ℕ) : Set ℂ :=
  ⋃ j : Fin (p + 1), mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) '' stdFDO_C

private lemma sl2Z_det_pos (γ : SL(2, ℤ)) : 0 < (sl2ZToGL2R γ).det.val := by
  simp [sl2ZToGL2R]

private lemma gamma0FD_subset_uhpC (p : ℕ) : gamma0FD p ⊆ uhpC := by
  intro w hw
  rcases Set.mem_iUnion.mp hw with ⟨j, z, hz, rfl⟩
  exact mobiusC_mem_uhpC (sl2Z_det_pos _) (stdFDO_C_subset_uhpC hz)

private lemma isOpen_gamma0FD (p : ℕ) : IsOpen (gamma0FD p) := by
  refine isOpen_iUnion fun j => ?_
  exact isOpen_mobiusC_image (sl2Z_det_pos _) isOpen_stdFDO_C stdFDO_C_subset_uhpC

private lemma measurableSet_gamma0FD (p : ℕ) : MeasurableSet (gamma0FD p) :=
  (isOpen_gamma0FD p).measurableSet

/-- Two open translates `γ₁ • stdFDO_C` and `γ₂ • stdFDO_C` intersect only when `γ₁ = ± γ₂`. -/
private lemma sl2Z_eq_or_eq_neg_of_mem_inter_stdFDO_C {γ₁ γ₂ : SL(2, ℤ)} {w : ℂ}
    (h1 : w ∈ mobiusC (sl2ZToGL2R γ₁) '' stdFDO_C)
    (h2 : w ∈ mobiusC (sl2ZToGL2R γ₂) '' stdFDO_C) :
    γ₁ = γ₂ ∨ γ₁ = -γ₂ := by
  rcases h1 with ⟨z₁, hz₁, rfl⟩
  rcases h2 with ⟨z₂, hz₂, heq⟩
  let τ₁ : UpperHalfPlane := ⟨z₁, stdFDO_C_subset_uhpC hz₁⟩
  let τ₂ : UpperHalfPlane := ⟨z₂, stdFDO_C_subset_uhpC hz₂⟩
  have hτ₁ : τ₁ ∈ ModularGroup.fdo := by
    refine ⟨?_, ?_⟩
    · change 1 < Complex.normSq z₁
      rw [Complex.normSq_apply]
      have hsq : 1 < z₁.re ^ 2 + z₁.im ^ 2 := hz₁.2.2
      nlinarith [sq z₁.re, sq z₁.im]
    · exact hz₁.1
  have hτ₂ : τ₂ ∈ ModularGroup.fdo := by
    refine ⟨?_, ?_⟩
    · change 1 < Complex.normSq z₂
      rw [Complex.normSq_apply]
      have hsq : 1 < z₂.re ^ 2 + z₂.im ^ 2 := hz₂.2.2
      nlinarith [sq z₂.re, sq z₂.im]
    · exact hz₂.1
  have hsmul : γ₁ • τ₁ = γ₂ • τ₂ := by
    apply UpperHalfPlane.ext
    change ((sl2ZToGL2R γ₁ • τ₁ : UpperHalfPlane) : ℂ) = ((sl2ZToGL2R γ₂ • τ₂ : UpperHalfPlane) : ℂ)
    rw [← mobiusC_eq_smul (sl2Z_det_pos γ₁) (stdFDO_C_subset_uhpC hz₁),
      ← mobiusC_eq_smul (sl2Z_det_pos γ₂) (stdFDO_C_subset_uhpC hz₂)]
    exact heq.symm
  have hinv : (γ₂⁻¹ * γ₁) • τ₁ = τ₂ := by
    rw [mul_smul, hsmul, inv_smul_smul]
  have h1neg := ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hτ₁ (hinv ▸ hτ₂)
  rcases h1neg with h1 | hneg
  · left
    calc γ₁ = γ₂ * (γ₂⁻¹ * γ₁) := by group
      _ = γ₂ * 1 := by rw [h1]
      _ = γ₂ := mul_one _
  · right
    calc γ₁ = γ₂ * (γ₂⁻¹ * γ₁) := by group
      _ = γ₂ * (-1) := by rw [hneg]
      _ = -γ₂ := by simp

private lemma gamma0_coset_translates_pairwise_disjoint {p : ℕ} (hp : 1 < p) :
    Pairwise (Disjoint on fun j : Fin (p + 1) =>
      mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) '' stdFDO_C) := by
  intro j₁ j₂ hne
  change Disjoint _ _
  rw [Set.disjoint_left]
  intro w hw1 hw2
  rcases sl2Z_eq_or_eq_neg_of_mem_inter_stdFDO_C hw1 hw2 with h | h
  · have := gamma0_coset_eq_of_dvd hp (h := 1) (by simp) (by simpa using h)
    exact hne this
  · have := gamma0_coset_eq_of_dvd hp (h := -1) (by simp) (by simpa using h)
    exact hne this

/-- The `Gamma0Plus p`-translates of `gamma0FD p` are pairwise disjoint. -/
private lemma gamma0Plus_translates_pairwise_disjoint {p : ℕ} (hp : 1 < p) :
    Pairwise (Disjoint on fun h : Gamma0Plus p =>
      mobiusC (sl2ZToGL2R h.1) '' gamma0FD p) := by
  intro h₁ h₂ hne
  change Disjoint _ _
  rw [Set.disjoint_left]
  intro w hw1 hw2
  rcases hw1 with ⟨u₁, hu₁, rfl⟩
  rcases hu₁ with ⟨_, ⟨j₁, rfl⟩, z₁, hz₁, rfl⟩
  rcases hw2 with ⟨u₂, hu₂, heq⟩
  rcases hu₂ with ⟨_, ⟨j₂, rfl⟩, z₂, hz₂, rfl⟩
  have hm1 : mobiusC (sl2ZToGL2R h₁.1) (mobiusC (sl2ZToGL2R (gamma0CosetRep p j₁)) z₁) =
      mobiusC (sl2ZToGL2R (h₁.1 * gamma0CosetRep p j₁)) z₁ := by
    rw [map_mul, mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) (stdFDO_C_subset_uhpC hz₁)]
  have hm2 : mobiusC (sl2ZToGL2R h₂.1) (mobiusC (sl2ZToGL2R (gamma0CosetRep p j₂)) z₂) =
      mobiusC (sl2ZToGL2R (h₂.1 * gamma0CosetRep p j₂)) z₂ := by
    rw [map_mul, mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) (stdFDO_C_subset_uhpC hz₂)]
  have hin1 : mobiusC (sl2ZToGL2R (h₁.1 * gamma0CosetRep p j₁)) z₁ ∈
      mobiusC (sl2ZToGL2R (h₁.1 * gamma0CosetRep p j₁)) '' stdFDO_C := ⟨z₁, hz₁, rfl⟩
  have hin2 : mobiusC (sl2ZToGL2R (h₁.1 * gamma0CosetRep p j₁)) z₁ ∈
      mobiusC (sl2ZToGL2R (h₂.1 * gamma0CosetRep p j₂)) '' stdFDO_C :=
    ⟨z₂, hz₂, by rw [← hm2, heq, hm1]⟩
  have hdiv : ∀ (a b : SL(2, ℤ)), (p : ℤ) ∣ a 1 0 → (p : ℤ) ∣ b 1 0 → (p : ℤ) ∣ (a⁻¹ * b) 1 0 := by
    intro a b ha hb
    have ha_inv : (a⁻¹ : SL(2, ℤ)) 1 0 = -(a 1 0) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
      simp
    have hmul : (a⁻¹ * b) 1 0 = (a⁻¹) 1 0 * b 0 0 + (a⁻¹) 1 1 * b 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hmul, ha_inv]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_neg.mpr ha) _) (dvd_mul_of_dvd_right hb _)
  rcases sl2Z_eq_or_eq_neg_of_mem_inter_stdFDO_C hin1 hin2 with h | h
  · have hj : j₁ = j₂ := by
      refine gamma0_coset_eq_of_dvd hp (h := h₁.1⁻¹ * h₂.1) (hdiv h₁.1 h₂.1 h₁.2.1 h₂.2.1) ?_
      calc gamma0CosetRep p j₁ = h₁.1⁻¹ * (h₁.1 * gamma0CosetRep p j₁) := by group
        _ = h₁.1⁻¹ * (h₂.1 * gamma0CosetRep p j₂) := by rw [h]
        _ = (h₁.1⁻¹ * h₂.1) * gamma0CosetRep p j₂ := by group
    subst hj
    have heq_h : h₁.1 = h₂.1 := mul_right_cancel h
    exact hne (Subtype.ext heq_h)
  · have hj : j₁ = j₂ := by
      refine gamma0_coset_eq_of_dvd hp (h := -(h₁.1⁻¹ * h₂.1)) (dvd_neg.mpr (hdiv h₁.1 h₂.1 h₁.2.1 h₂.2.1)) ?_
      have hneg : h₁.1 * gamma0CosetRep p j₁ = (-h₂.1) * gamma0CosetRep p j₂ := by
        simpa using h
      calc gamma0CosetRep p j₁ = h₁.1⁻¹ * (h₁.1 * gamma0CosetRep p j₁) := by group
        _ = h₁.1⁻¹ * ((-h₂.1) * gamma0CosetRep p j₂) := by rw [hneg]
        _ = (-(h₁.1⁻¹ * h₂.1)) * gamma0CosetRep p j₂ := by simp [mul_assoc]
    subst hj
    have heq_h : h₁.1 = -h₂.1 := mul_right_cancel (by simpa using h)
    exact sl2Z_neg_not_mem_plus h₂.2.2 (heq_h ▸ h₁.2.2)

/-- The union of `Gamma0Plus p`-translates of `gamma0FD p` covers `uhpC` up to Lebesgue measure 0. -/
private lemma iUnion_gamma0Plus_gamma0FD_ae_eq_uhpC {p : ℕ} (hp : p.Prime) :
    (⋃ h : Gamma0Plus p, mobiusC (sl2ZToGL2R h.1) '' gamma0FD p) =ᵐ[volume] uhpC := by
  have hsub : (⋃ h : Gamma0Plus p, mobiusC (sl2ZToGL2R h.1) '' gamma0FD p) ⊆ uhpC := by
    intro w hw
    rcases Set.mem_iUnion.mp hw with ⟨h, u, hu, rfl⟩
    exact mobiusC_mem_uhpC (sl2Z_det_pos _) (gamma0FD_subset_uhpC p hu)
  have hdiff_sub : uhpC \ (⋃ h : Gamma0Plus p, mobiusC (sl2ZToGL2R h.1) '' gamma0FD p) ⊆
      ⋃ γ : SL(2, ℤ), mobiusC (sl2ZToGL2R γ) '' (stdFD_C \ stdFDO_C) := by
    intro w ⟨hw_uhp, hw_not⟩
    let τ : UpperHalfPlane := ⟨w, hw_uhp⟩
    obtain ⟨σ, hσ⟩ := ModularGroup.exists_smul_mem_fd τ
    let z : ℂ := ((σ • τ : UpperHalfPlane) : ℂ)
    have hz_fd : z ∈ stdFD_C := by
      have hm := mem_stdFD_of_mem_modularGroup_fd hσ
      simpa [stdFD_C, Complex.measurableEquivRealProd_apply, z] using hm
    have hw_eq : mobiusC (sl2ZToGL2R σ⁻¹) z = w := by
      rw [mobiusC_eq_smul (sl2Z_det_pos σ⁻¹) (stdFD_C_subset_uhpC hz_fd)]
      have hpt : (⟨z, stdFD_C_subset_uhpC hz_fd⟩ : UpperHalfPlane) = σ • τ := by
        apply UpperHalfPlane.ext; rfl
      rw [hpt, show sl2ZToGL2R σ⁻¹ • (σ • τ) = σ⁻¹ • (σ • τ) from rfl, inv_smul_smul]
    by_cases hz_fdo : z ∈ stdFDO_C
    · exfalso
      obtain ⟨j, h, hh_div, hfac⟩ := exists_unique_gamma0_coset hp σ⁻¹
      rcases sl2Z_mem_plus_or_neg h with hplus | hneg
      · apply hw_not
        refine Set.mem_iUnion.mpr ⟨⟨h, hh_div, hplus⟩,
          mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z,
          Set.mem_iUnion.mpr ⟨j, z, hz_fdo, rfl⟩, ?_⟩
        rw [← mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) (stdFDO_C_subset_uhpC hz_fdo),
          ← map_mul, ← hfac, hw_eq]
      · apply hw_not
        have hh_neg_div : (p : ℤ) ∣ (-h) 1 0 := by
          change (p : ℤ) ∣ -(h 1 0); exact dvd_neg.mpr hh_div
        refine Set.mem_iUnion.mpr ⟨⟨-h, hh_neg_div, hneg⟩,
          mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z,
          Set.mem_iUnion.mpr ⟨j, z, hz_fdo, rfl⟩, ?_⟩
        rw [mobiusC_neg_sl2Z h (mobiusC_mem_uhpC (sl2Z_det_pos _) (stdFDO_C_subset_uhpC hz_fdo)),
          ← mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) (stdFDO_C_subset_uhpC hz_fdo),
          ← map_mul, ← hfac, hw_eq]
    · exact Set.mem_iUnion.mpr ⟨σ⁻¹, z, ⟨hz_fd, hz_fdo⟩, hw_eq⟩
  have hnull : volume (⋃ γ : SL(2, ℤ), mobiusC (sl2ZToGL2R γ) '' (stdFD_C \ stdFDO_C)) = 0 := by
    refine measure_iUnion_null fun γ => ?_
    exact volume_mobiusC_image_zero (sl2Z_det_pos γ)
      (Set.sdiff_subset.trans stdFD_C_subset_uhpC) volume_stdFD_C_diff_stdFDO_C
  rw [MeasureTheory.ae_eq_set]
  exact ⟨measure_mono_null (Set.sdiff_eq_empty.mpr hsub).subset (by simp),
    measure_mono_null hdiff_sub hnull⟩

/-- Canonical `Gamma0Plus p` representative of `±h` for any `h ∈ Γ₀(p)`. -/
private def toGamma0Plus {p : ℕ} (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ h 1 0) : Gamma0Plus p := by
  classical
  exact if hp : h ∈ SL2ZPlus then ⟨h, hh, hp⟩
  else ⟨-h, by change (p : ℤ) ∣ -(h 1 0); exact dvd_neg.mpr hh,
    (sl2Z_mem_plus_or_neg h).resolve_left hp⟩

private lemma mobiusC_toGamma0Plus {p : ℕ} (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ h 1 0)
    {z : ℂ} (hz : z ∈ uhpC) :
    mobiusC (sl2ZToGL2R (toGamma0Plus h hh).1) z = mobiusC (sl2ZToGL2R h) z := by
  unfold toGamma0Plus
  split_ifs with hp
  · rfl
  · exact mobiusC_neg_sl2Z h hz

/-- **Fundamental-Domain Independence for `Γ₀(p)` under the Fricke Involution `W_p`**:
for any prime `p`, any `Γ₀(p)`-invariant function `F : ℂ → ℂ`, if `F * y^{-2}` is integrable on
both `gamma0FD p` and `W_p '' gamma0FD p`, then
$$\int_{w \in W_p '' \mathcal{D}_p} F(w)\,(\mathrm{Im}\, w)^{-2}\, dw =
  \int_{z \in \mathcal{D}_p} F(z)\,(\mathrm{Im}\, z)^{-2}\, dz.$$ -/
theorem integral_frickeW_gamma0FD_eq {p : ℕ} (hp : p.Prime) (F : ℂ → ℂ)
    (hF_inv : ∀ (h : SL(2, ℤ)), (p : ℤ) ∣ h 1 0 → ∀ z ∈ uhpC, F (mobiusC (sl2ZToGL2R h) z) = F z)
    (hInt1 : IntegrableOn (fun z => F z * ((z.im : ℂ) ^ (-2 : ℤ))) (gamma0FD p) volume)
    (hInt2 : IntegrableOn (fun z => F z * ((z.im : ℂ) ^ (-2 : ℤ)))
      (mobiusC (frickeW p hp.pos) '' gamma0FD p) volume) :
    ∫ w in mobiusC (frickeW p hp.pos) '' gamma0FD p, F w * ((w.im : ℂ) ^ (-2 : ℤ)) =
      ∫ z in gamma0FD p, F z * ((z.im : ℂ) ^ (-2 : ℤ)) := by
  let D : Set ℂ := gamma0FD p
  let DW : Set ℂ := mobiusC (frickeW p hp.pos) '' D
  let G : ℂ → ℂ := fun z => F z * ((z.im : ℂ) ^ (-2 : ℤ))
  have hD_sub : D ⊆ uhpC := gamma0FD_subset_uhpC p
  have hD_meas : MeasurableSet D := measurableSet_gamma0FD p
  have hW_pos : 0 < (frickeW p hp.pos).det.val := frickeW_det_pos p hp.pos
  have hDW_sub : DW ⊆ uhpC := by
    rintro _ ⟨z, hz, rfl⟩; exact mobiusC_mem_uhpC hW_pos (hD_sub hz)
  have hDW_meas : MeasurableSet DW := measurableSet_mobiusC_image hW_pos hD_meas hD_sub
  -- Partition 1: `DW =ᵐ[volume] ⋃ h : Gamma0Plus p, (DW ∩ h '' D)`
  let A : Gamma0Plus p → Set ℂ := fun h => DW ∩ (mobiusC (sl2ZToGL2R h.1) '' D)
  have hA_meas : ∀ h, MeasurableSet (A h) := fun h =>
    hDW_meas.inter (measurableSet_mobiusC_image (sl2Z_det_pos h.1) hD_meas hD_sub)
  have hA_disj : Pairwise (Disjoint on A) := fun h₁ h₂ hne =>
    (gamma0Plus_translates_pairwise_disjoint hp.one_lt hne).mono Set.inter_subset_right Set.inter_subset_right
  have hA_union_ae : (⋃ h : Gamma0Plus p, A h) =ᵐ[volume] DW := by
    have heq : (⋃ h : Gamma0Plus p, A h) =
        DW ∩ (⋃ h : Gamma0Plus p, mobiusC (sl2ZToGL2R h.1) '' D) :=
      (Set.inter_iUnion DW _).symm
    rw [heq]
    have h1 := MeasureTheory.ae_eq_set_inter (Filter.EventuallyEq.refl _ DW)
      (iUnion_gamma0Plus_gamma0FD_ae_eq_uhpC hp)
    have h2 : DW ∩ uhpC = DW := Set.inter_eq_left.mpr hDW_sub
    rwa [h2] at h1
  have hsum1 : HasSum (fun h : Gamma0Plus p => ∫ w in A h, G w) (∫ w in DW, G w) := by
    have hInt_union : IntegrableOn G (⋃ h : Gamma0Plus p, A h) volume :=
      hInt2.congr_set_ae hA_union_ae
    have hhs := MeasureTheory.hasSum_integral_iUnion hA_meas hA_disj hInt_union
    rwa [setIntegral_congr_set hA_union_ae] at hhs
  -- Partition 2: `D =ᵐ[volume] ⋃ h : Gamma0Plus p, (h⁻¹ '' DW ∩ D)`
  let B : Gamma0Plus p → Set ℂ := fun h => (mobiusC (sl2ZToGL2R h.1⁻¹) '' DW) ∩ D
  have hB_meas : ∀ h, MeasurableSet (B h) := fun h =>
    (measurableSet_mobiusC_image (sl2Z_det_pos h.1⁻¹) hDW_meas hDW_sub).inter hD_meas
  -- Show each `h` term matches: `∫ w in A h, G w = ∫ z in B h, G z`!
  have hterm_eq : ∀ h : Gamma0Plus p, ∫ w in A h, G w = ∫ z in B h, G z := by
    intro h
    have himage : A h = mobiusC (sl2ZToGL2R h.1) '' B h := by
      ext w
      constructor
      · rintro ⟨hw_DW, z, hzD, rfl⟩
        refine ⟨z, ⟨⟨mobiusC (sl2ZToGL2R h.1) z, hw_DW, ?_⟩, hzD⟩, rfl⟩
        rw [← mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) (hD_sub hzD),
          ← map_mul, inv_mul_cancel, map_one, mobiusC_one (hD_sub hzD)]
      · rintro ⟨z, ⟨⟨u, huDW, hzu⟩, hzD⟩, rfl⟩
        refine ⟨?_, z, hzD, rfl⟩
        have hwu : mobiusC (sl2ZToGL2R h.1) z = u := by
          rw [← hzu, ← mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) (hDW_sub huDW),
            ← map_mul, mul_inv_cancel, map_one, mobiusC_one (hDW_sub huDW)]
        rwa [hwu]
    rw [himage]
    have hB_sub : B h ⊆ uhpC := Set.inter_subset_right.trans hD_sub
    rw [integral_mobiusC_hyperbolic (sl2Z_det_pos h.1) (hB_meas h) hB_sub F]
    refine setIntegral_congr_fun (hB_meas h) fun z hz => ?_
    rw [hF_inv h.1 h.2.1 z (hB_sub hz)]
  -- Show `B` is pairwise disjoint and covers `D` up to measure 0!
  have hdiv_inv : ∀ (a : SL(2, ℤ)), (p : ℤ) ∣ a 1 0 → (p : ℤ) ∣ a⁻¹ 1 0 := by
    intro a ha
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    exact dvd_neg.mpr ha
  have hdiv_mul : ∀ (a b : SL(2, ℤ)), (p : ℤ) ∣ a 1 0 → (p : ℤ) ∣ b 1 0 → (p : ℤ) ∣ (a * b) 1 0 := by
    intro a b ha hb
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _)
  have hff : ∀ (k : SL(2, ℤ)) (hk : (p : ℤ) ∣ k 1 0),
      frickeConj p (frickeConj p k hk) (frickeConj_mem_gamma0 p k hk) = k := by
    intro k hk
    ext r s
    fin_cases r <;> fin_cases s <;> simp only [frickeConj, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    · rfl
    · have hdiv_neg : (-(p : ℤ) * k 0 1) / (p : ℤ) = -(k 0 1) := by
        have : -(p : ℤ) * k 0 1 = (p : ℤ) * (-(k 0 1)) := by ring
        rw [this, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (ne_of_gt hp.pos))]
      rw [hdiv_neg, neg_neg]
      rfl
    · have hmul : -(p : ℤ) * -(k 1 0 / (p : ℤ)) = (p : ℤ) * (k 1 0 / (p : ℤ)) := by ring
      rw [hmul, Int.mul_ediv_cancel' hk]
      rfl
    · rfl
  have hconj_right : ∀ (k : SL(2, ℤ)) (hk : (p : ℤ) ∣ k 1 0),
      sl2ZToGL2R k * frickeW p hp.pos = frickeW p hp.pos * sl2ZToGL2R (frickeConj p k hk) := by
    intro k hk
    have h1 := frickeW_mul_eq_frickeConj_mul_frickeW p hp.pos (frickeConj p k hk)
      (frickeConj_mem_gamma0 p k hk)
    rw [hff k hk] at h1
    exact h1.symm
  have h1_mem : (1 : SL(2, ℤ)) ∈ Gamma0Plus p := ⟨by simp, Or.inr ⟨by simp, by simp⟩⟩
  have hB_disj : Pairwise (Disjoint on B) := by
    intro h₁ h₂ hne
    change Disjoint _ _
    rw [Set.disjoint_left]
    intro z ⟨⟨w₁, hw₁, heq1⟩, _⟩ ⟨⟨w₂, hw₂, heq2⟩, _⟩
    rcases hw₁ with ⟨u₁, hu₁, rfl⟩
    rcases hw₂ with ⟨u₂, hu₂, rfl⟩
    have h12_div : (p : ℤ) ∣ (h₂.1 * h₁.1⁻¹) 1 0 := hdiv_mul _ _ h₂.2.1 (hdiv_inv _ h₁.2.1)
    let c : SL(2, ℤ) := frickeConj p (h₂.1 * h₁.1⁻¹) h12_div
    have hc_div : (p : ℤ) ∣ c 1 0 := frickeConj_mem_gamma0 p _ h12_div
    have hWu1 : mobiusC (frickeW p hp.pos) u₁ ∈ uhpC := mobiusC_mem_uhpC hW_pos (hD_sub hu₁)
    have hWu2 : mobiusC (frickeW p hp.pos) u₂ ∈ uhpC := mobiusC_mem_uhpC hW_pos (hD_sub hu₂)
    have hstep1 : mobiusC (sl2ZToGL2R (h₂.1 * h₁.1⁻¹)) (mobiusC (frickeW p hp.pos) u₁) =
        mobiusC (frickeW p hp.pos) u₂ := by
      rw [map_mul, mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) hWu1, heq1, ← heq2,
        ← mobiusC_mul (sl2Z_det_pos _) (sl2Z_det_pos _) hWu2, ← map_mul, mul_inv_cancel,
        map_one, mobiusC_one hWu2]
    have hstep2 : mobiusC (frickeW p hp.pos) (mobiusC (sl2ZToGL2R c) u₁) =
        mobiusC (frickeW p hp.pos) u₂ := by
      rw [← mobiusC_mul hW_pos (sl2Z_det_pos c) (hD_sub hu₁), ← hconj_right _ h12_div,
        mobiusC_mul (sl2Z_det_pos _) hW_pos (hD_sub hu₁), hstep1]
    have hcu1 : mobiusC (sl2ZToGL2R c) u₁ = u₂ :=
      mobiusC_injOn hW_pos (mobiusC_mem_uhpC (sl2Z_det_pos c) (hD_sub hu₁)) (hD_sub hu₂) hstep2
    let cplus : Gamma0Plus p := toGamma0Plus c hc_div
    have hmem1 : u₂ ∈ mobiusC (sl2ZToGL2R cplus.1) '' D :=
      ⟨u₁, hu₁, by rw [mobiusC_toGamma0Plus c hc_div (hD_sub hu₁), hcu1]⟩
    have hmem2 : u₂ ∈ mobiusC (sl2ZToGL2R (⟨1, h1_mem⟩ : Gamma0Plus p).1) '' D :=
      ⟨u₂, hu₂, by rw [map_one, mobiusC_one (hD_sub hu₂)]⟩
    have hcplus_eq : cplus = ⟨1, h1_mem⟩ := by
      by_contra hcne
      exact Set.disjoint_left.mp (gamma0Plus_translates_pairwise_disjoint hp.one_lt hcne) hmem1 hmem2
    have hc_pm : c = 1 ∨ c = -1 := by
      unfold cplus toGamma0Plus at hcplus_eq
      split_ifs at hcplus_eq with hcp
      · left; exact congrArg Subtype.val hcplus_eq
      · right
        have hneg : -c = 1 := congrArg Subtype.val hcplus_eq
        calc c = -(-c) := (neg_neg c).symm
          _ = -1 := by rw [hneg]
    have h12_pm : h₂.1 * h₁.1⁻¹ = 1 ∨ h₂.1 * h₁.1⁻¹ = -1 := by
      have hback : h₂.1 * h₁.1⁻¹ = frickeConj p c hc_div := (hff _ h12_div).symm
      rw [hback]
      rcases hc_pm with hc1 | hcn1
      · left; ext r s; fin_cases r <;> fin_cases s <;> simp [frickeConj, hc1]
      · right; ext r s; fin_cases r <;> fin_cases s <;> simp [frickeConj, hcn1]
    rcases h12_pm with h1eq | hneg_eq
    · have : h₂.1 = h₁.1 := eq_of_mul_inv_eq_one h1eq
      exact hne (Subtype.ext this.symm)
    · have : h₂.1 = -h₁.1 := by
        calc h₂.1 = (h₂.1 * h₁.1⁻¹) * h₁.1 := by group
          _ = (-1) * h₁.1 := by rw [hneg_eq]
          _ = -h₁.1 := by simp
      exact sl2Z_neg_not_mem_plus h₁.2.2 (this ▸ h₂.2.2)
  have hB_union_ae : (⋃ h : Gamma0Plus p, B h) =ᵐ[volume] D := by
    have heq : (⋃ h : Gamma0Plus p, B h) =
        (⋃ h : Gamma0Plus p, mobiusC (sl2ZToGL2R h.1⁻¹) '' DW) ∩ D := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, B]
      exact ⟨fun ⟨i, hi, hzD⟩ => ⟨⟨i, hi⟩, hzD⟩, fun ⟨⟨i, hi⟩, hzD⟩ => ⟨i, hi, hzD⟩⟩
    rw [heq]
    have hW_uhp : mobiusC (frickeW p hp.pos) '' uhpC = uhpC := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩; exact mobiusC_mem_uhpC hW_pos hz
      · intro hw
        refine ⟨mobiusC (frickeW p hp.pos) w, mobiusC_mem_uhpC hW_pos hw, ?_⟩
        rw [← mobiusC_mul hW_pos hW_pos hw]
        have hW2 : (frickeW p hp.pos * frickeW p hp.pos : Matrix (Fin 2) (Fin 2) ℝ) =
            !![-(p : ℝ), 0; 0, -(p : ℝ)] := by
          change (!![(0 : ℝ), -1; (p : ℝ), 0] : Matrix (Fin 2) (Fin 2) ℝ) *
              !![(0 : ℝ), -1; (p : ℝ), 0] = _
          ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
        have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp.pos)
        unfold mobiusC
        change ((((frickeW p hp.pos * frickeW p hp.pos : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) * w +
            ((frickeW p hp.pos * frickeW p hp.pos : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ)) /
          (((frickeW p hp.pos * frickeW p hp.pos : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) * w +
            ((frickeW p hp.pos * frickeW p hp.pos : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ))) = w
        rw [hW2]; simp [mul_div_cancel_left₀ _ hpC]
    have hBigEq : (⋃ h : Gamma0Plus p, mobiusC (sl2ZToGL2R h.1⁻¹) '' DW) =
        mobiusC (frickeW p hp.pos) '' (⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D) := by
      ext z
      constructor
      · rintro ⟨_, ⟨h, rfl⟩, _, ⟨u, hu, rfl⟩, rfl⟩
        have hinv_div : (p : ℤ) ∣ h.1⁻¹ 1 0 := hdiv_inv h.1 h.2.1
        let k : Gamma0Plus p := toGamma0Plus (frickeConj p h.1⁻¹ hinv_div)
          (frickeConj_mem_gamma0 p h.1⁻¹ hinv_div)
        refine ⟨mobiusC (sl2ZToGL2R k.1) u, Set.mem_iUnion.mpr ⟨k, u, hu, rfl⟩, ?_⟩
        rw [mobiusC_toGamma0Plus _ _ (hD_sub hu), ← mobiusC_mul hW_pos (sl2Z_det_pos _) (hD_sub hu),
          ← hconj_right h.1⁻¹ hinv_div, mobiusC_mul (sl2Z_det_pos _) hW_pos (hD_sub hu)]
      · rintro ⟨_, ⟨_, ⟨k, rfl⟩, u, hu, rfl⟩, rfl⟩
        let c : SL(2, ℤ) := (frickeConj p k.1 k.2.1)⁻¹
        have hc_div : (p : ℤ) ∣ c 1 0 := hdiv_inv _ (frickeConj_mem_gamma0 p k.1 k.2.1)
        let h : Gamma0Plus p := toGamma0Plus c hc_div
        refine Set.mem_iUnion.mpr ⟨h, mobiusC (frickeW p hp.pos) u, ⟨u, hu, rfl⟩, ?_⟩
        have hinv_pm : mobiusC (sl2ZToGL2R h.1⁻¹) (mobiusC (frickeW p hp.pos) u) =
            mobiusC (sl2ZToGL2R (frickeConj p k.1 k.2.1)) (mobiusC (frickeW p hp.pos) u) := by
          have hWu : mobiusC (frickeW p hp.pos) u ∈ uhpC := mobiusC_mem_uhpC hW_pos (hD_sub hu)
          unfold h toGamma0Plus
          split_ifs with hcp
          · simp [c]
          · simp only [inv_neg, c, inv_inv]
            exact mobiusC_neg_sl2Z _ hWu
        rw [hinv_pm, ← mobiusC_mul (sl2Z_det_pos _) hW_pos (hD_sub hu),
          ← frickeW_mul_eq_frickeConj_mul_frickeW p hp.pos k.1 k.2.1,
          mobiusC_mul hW_pos (sl2Z_det_pos _) (hD_sub hu)]
    rw [hBigEq]
    have hU_sub : (⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D) ⊆ uhpC := by
      rintro _ ⟨_, ⟨k, rfl⟩, u, hu, rfl⟩
      exact mobiusC_mem_uhpC (sl2Z_det_pos _) (hD_sub hu)
    have hU_diff0 : volume (uhpC \ ⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D) = 0 :=
      (MeasureTheory.ae_eq_set.mp (iUnion_gamma0Plus_gamma0FD_ae_eq_uhpC hp)).2
    have hWU_ae : (mobiusC (frickeW p hp.pos) ''
        (⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D)) =ᵐ[volume] uhpC := by
      rw [MeasureTheory.ae_eq_set]
      refine ⟨?_, ?_⟩
      · have hsub1 : mobiusC (frickeW p hp.pos) ''
            (⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D) ⊆ uhpC := by
          rw [← hW_uhp]; exact Set.image_mono hU_sub
        exact measure_mono_null (Set.sdiff_eq_empty.mpr hsub1).subset (by simp)
      · have hsub2 : uhpC \ (mobiusC (frickeW p hp.pos) ''
            (⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D)) ⊆
            mobiusC (frickeW p hp.pos) ''
              (uhpC \ ⋃ k : Gamma0Plus p, mobiusC (sl2ZToGL2R k.1) '' D) := by
          rintro w ⟨hw, hnot⟩
          rw [← hW_uhp] at hw
          rcases hw with ⟨z, hz, rfl⟩
          exact ⟨z, ⟨hz, fun hzU => hnot ⟨z, hzU, rfl⟩⟩, rfl⟩
        exact measure_mono_null hsub2
          (volume_mobiusC_image_zero hW_pos Set.sdiff_subset hU_diff0)
    have h1 := MeasureTheory.ae_eq_set_inter hWU_ae (Filter.EventuallyEq.refl _ D)
    have h2 : uhpC ∩ D = D := Set.inter_eq_right.mpr hD_sub
    rwa [h2] at h1
  have hsum2 : HasSum (fun h : Gamma0Plus p => ∫ z in B h, G z) (∫ z in D, G z) := by
    have hInt_union : IntegrableOn G (⋃ h : Gamma0Plus p, B h) volume :=
      hInt1.congr_set_ae hB_union_ae
    have hhs := MeasureTheory.hasSum_integral_iUnion hB_meas hB_disj hInt_union
    rwa [setIntegral_congr_set hB_union_ae] at hhs
  have hsum1' : HasSum (fun h : Gamma0Plus p => ∫ z in B h, G z) (∫ w in DW, G w) := by
    simpa [hterm_eq] using hsum1
  exact hsum1'.unique hsum2

/-- Integrability of `petersson k (g |_k heckeMat a b d) f * y^{-2}` on `stdFDO_C`. -/
private lemma integrableOn_petersson_heckeMat_stdFDO_C {k : ℕ} (hk : 1 ≤ k)
    (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (f g : CuspForm SL2ZRange (k : ℤ)) :
    IntegrableOn
      (fun z : ℂ =>
        (if hz : 0 < z.im then
          UpperHalfPlane.petersson (k : ℤ)
            (SlashAction.map (k : ℤ) (heckeMat a b d ha hd) (g : UpperHalfPlane → ℂ)) f ⟨z, hz⟩
        else 0) * ((z.im : ℂ) ^ (-2 : ℤ)))
      stdFDO_C volume := by
  let φ : ℂ → ℂ := fun z =>
    (if hz : 0 < z.im then
      UpperHalfPlane.petersson (k : ℤ)
        (SlashAction.map (k : ℤ) (heckeMat a b d ha hd) (g : UpperHalfPlane → ℂ)) f ⟨z, hz⟩
    else 0) * ((z.im : ℂ) ^ (-2 : ℤ))
  -- Exponential decay of `f` on `stdFDO_C` and boundedness of `g |_k heckeMat a b d` on `stdFDO_C`!
  obtain ⟨Cf, hCf_pos, hCf⟩ := cuspForm_exp_decay_strip f
  have hCg_bigO := CuspFormClass.exp_decay_atImInfty g zero_lt_one one_mem_strictPeriods_SL
  rw [Asymptotics.isBigO_iff] at hCg_bigO
  obtain ⟨C₀, hC₀⟩ := hCg_bigO
  rw [UpperHalfPlane.atImInfty_basis.eventually_iff] at hC₀
  obtain ⟨A, _, hA⟩ := hC₀
  let y₀ : ℝ := Real.sqrt 3 / 2
  have hy₀_pos : 0 < y₀ := by positivity
  have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  let B : ℝ := max y₀ (A * (d : ℝ) / (a : ℝ))
  let K : Set ℂ := Complex.measurableEquivRealProd ⁻¹' (Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Icc y₀ B)
  have hK_compact : IsCompact K := by
    have hcomp : IsCompact (Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Icc y₀ B) :=
      isCompact_Icc.prod isCompact_Icc
    exact Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr hcomp
  have hg_cont : ContinuousOn
      (fun z : ℂ => if hz : 0 < z.im then
        SlashAction.map (k : ℤ) (heckeMat a b d ha hd) (g : UpperHalfPlane → ℂ) ⟨z, hz⟩ else 0)
      uhpC := by
    have hmd : MDiff (fun τ : UpperHalfPlane =>
        g (heckeMat a b d ha hd • τ) * ((a : ℂ) ^ (k - 1) / (d : ℂ))) :=
      (g.holo'.comp (UpperHalfPlane.mdifferentiable_smul (heckeMat_det_pos a b d ha hd))).mul
        mdifferentiable_const
    have hdiff := UpperHalfPlane.mdifferentiable_iff.mp hmd
    refine hdiff.continuousOn.congr fun z hz => ?_
    have hz' : 0 < z.im := hz
    rw [dif_pos hz', heckeMat_slash_apply hk a b d ha hd (g : UpperHalfPlane → ℂ) ⟨z, hz'⟩]
    change _ = g (heckeMat a b d ha hd • UpperHalfPlane.ofComplex z) * ((a : ℂ) ^ (k - 1) / (d : ℂ))
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hK_sub : K ⊆ uhpC := fun z hz => lt_of_lt_of_le hy₀_pos hz.2.1
  obtain ⟨C₁, hC₁⟩ := hK_compact.exists_bound_of_continuousOn (hg_cont.norm.mono hK_sub)
  let c_scale : ℝ := ‖((a : ℂ) ^ (k - 1) / (d : ℂ))‖
  let Cg : ℝ := max (max (C₀ * c_scale) C₁) 1
  have hCg_pos : 0 < Cg := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCg_bound : ∀ z ∈ stdFDO_C, ∀ (hz : 0 < z.im),
      ‖SlashAction.map (k : ℤ) (heckeMat a b d ha hd) (g : UpperHalfPlane → ℂ) ⟨z, hz⟩‖ ≤ Cg := by
    intro z hz_fdo hz
    have hy_ge : y₀ ≤ z.im := stdFD_im_ge (stdFDO_C_subset_stdFD_C hz_fdo)
    by_cases hyB : z.im ≤ B
    · have hzK : z ∈ K := ⟨⟨by linarith [(abs_le.mp hz_fdo.1.le).1], (abs_le.mp hz_fdo.1.le).2⟩, hy_ge, hyB⟩
      have hb := hC₁ z hzK
      simp only [dif_pos hz, Real.norm_of_nonneg (norm_nonneg _)] at hb
      exact hb.trans (le_trans (le_max_right _ _) (le_max_left _ _))
    · have hB_lt : B < z.im := lt_of_not_ge hyB
      have hAd_lt : A * (d : ℝ) / (a : ℝ) < z.im := lt_of_le_of_lt (le_max_right _ _) hB_lt
      have him_eq : (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)).im =
          ((a : ℝ) / (d : ℝ)) * z.im := by
        rw [UpperHalfPlane.im_smul_eq_div_normSq, heckeMat_det,
          abs_of_pos (by positivity : (0 : ℝ) < (a : ℝ) * (d : ℝ))]
        have hden : UpperHalfPlane.denom (heckeMat a b d ha hd) (⟨z, hz⟩ : UpperHalfPlane) = (d : ℂ) := by
          simp [UpperHalfPlane.denom, heckeMat]
        rw [hden, Complex.normSq_natCast]
        change (a : ℝ) * (d : ℝ) * z.im / ((d : ℝ) * (d : ℝ)) = (a : ℝ) / (d : ℝ) * z.im
        field_simp [ne_of_gt hdR]
      have him_ge : A ≤ (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)).im := by
        rw [him_eq]
        have h1 : A * (d : ℝ) ≤ (a : ℝ) * z.im := by
          have := (div_lt_iff₀ haR).mp hAd_lt; linarith
        have h2 : A ≤ ((a : ℝ) * z.im) / (d : ℝ) := (le_div_iff₀ hdR).mpr h1
        simpa [div_mul_eq_mul_div] using h2
      have hb := hA (show heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane) ∈
        UpperHalfPlane.im ⁻¹' Set.Ici A from him_ge)
      simp only [div_one, Real.norm_of_nonneg (Real.exp_pos _).le] at hb
      have hexp_le1 : Real.exp (-2 * Real.pi * (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)).im) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have := (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
        have := Real.pi_pos
        nlinarith
      rw [heckeMat_slash_apply hk a b d ha hd (g : UpperHalfPlane → ℂ) ⟨z, hz⟩, norm_mul]
      have hC0_nn : 0 ≤ C₀ := by
        have h0 := norm_nonneg (g (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)))
        have hexp_p := Real.exp_pos (-2 * Real.pi * (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)).im)
        nlinarith
      calc ‖g (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane))‖ * c_scale
          ≤ (C₀ * Real.exp (-2 * Real.pi * (heckeMat a b d ha hd • (⟨z, hz⟩ : UpperHalfPlane)).im)) * c_scale :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ ≤ (C₀ * 1) * c_scale :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le1 hC0_nn) (norm_nonneg _)
        _ = C₀ * c_scale := by ring
        _ ≤ Cg := le_trans (le_max_left _ _) (le_max_left _ _)
  -- Now dominate `‖φ z‖ ≤ (Cf * Cg * M) * exp(-π * z.im)` on `stdFDO_C`!
  obtain ⟨M, hM_pos, hM⟩ := exp_mul_zpow_bound ((k : ℤ) - 2) (by positivity : (0 : ℝ) < y₀ / 2)
  have hM' : ∀ y : ℝ, y₀ ≤ y → Real.exp (-2 * Real.pi * y) * y ^ ((k : ℤ) - 2) ≤
      (M * 2 ^ ((k : ℤ) - 2)) * Real.exp (-Real.pi * y) := by
    intro y hy
    have h1 := hM (y / 2) (by linarith)
    have he1 : -4 * Real.pi * (y / 2) = -2 * Real.pi * y := by ring
    have he2 : -2 * Real.pi * (y / 2) = -Real.pi * y := by ring
    rw [he1, he2, div_zpow] at h1
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((k : ℤ) - 2) := zpow_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_right h1 h2pos.le
    have hcancel : y ^ ((k : ℤ) - 2) / (2 : ℝ) ^ ((k : ℤ) - 2) * (2 : ℝ) ^ ((k : ℤ) - 2) =
        y ^ ((k : ℤ) - 2) := div_mul_cancel₀ _ (ne_of_gt h2pos)
    calc Real.exp (-2 * Real.pi * y) * y ^ ((k : ℤ) - 2)
        = (Real.exp (-2 * Real.pi * y) * (y ^ ((k : ℤ) - 2) / (2 : ℝ) ^ ((k : ℤ) - 2))) *
            (2 : ℝ) ^ ((k : ℤ) - 2) := by
            field_simp [ne_of_gt h2pos]
      _ ≤ (M * Real.exp (-Real.pi * y)) * (2 : ℝ) ^ ((k : ℤ) - 2) := hmul
      _ = (M * (2 : ℝ) ^ ((k : ℤ) - 2)) * Real.exp (-Real.pi * y) := by ring
  let M' : ℝ := M * (2 : ℝ) ^ ((k : ℤ) - 2)
  let S : Set (ℝ × ℝ) := Set.Icc (-1 / 2 : ℝ) (1 / 2) ×ˢ Set.Ici y₀
  have hdom_x : IntegrableOn (fun _ : ℝ => Cf * Cg * M') (Set.Icc (-1 / 2 : ℝ) (1 / 2)) volume :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hdom_y : IntegrableOn (fun y : ℝ => Real.exp (-Real.pi * y)) (Set.Ici y₀) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_Ioi (a := -Real.pi) (by linarith [Real.pi_pos]) y₀)
  have hdom_S : IntegrableOn (fun p : ℝ × ℝ => (Cf * Cg * M') * Real.exp (-Real.pi * p.2)) S volume := by
    have h := Integrable.mul_prod hdom_x hdom_y
    simpa [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict, S] using h
  have hdom_C : IntegrableOn (fun z : ℂ => (Cf * Cg * M') * Real.exp (-Real.pi * z.im))
      (Complex.measurableEquivRealProd ⁻¹' S) volume := by
    have hmp := Complex.volume_preserving_equiv_real_prod
    exact (hmp.integrableOn_comp_preimage Complex.measurableEquivRealProd.measurableEmbedding).mpr hdom_S
  have hsub_S : stdFDO_C ⊆ Complex.measurableEquivRealProd ⁻¹' S := fun z hz =>
    ⟨⟨by linarith [(abs_le.mp hz.1.le).1], (abs_le.mp hz.1.le).2⟩, stdFD_im_ge (stdFDO_C_subset_stdFD_C hz)⟩
  have hdom_fdo : IntegrableOn (fun z : ℂ => (Cf * Cg * M') * Real.exp (-Real.pi * z.im))
      stdFDO_C volume := hdom_C.mono_set hsub_S
  have hcont_φ : ContinuousOn φ stdFDO_C := by
    have hf_cont : ContinuousOn (fun z : ℂ => if hz : 0 < z.im then f ⟨z, hz⟩ else 0) uhpC := by
      have hdiff := UpperHalfPlane.mdifferentiable_iff.mp f.holo'
      refine hdiff.continuousOn.congr fun z hz => ?_
      have hz' : 0 < z.im := hz
      rw [dif_pos hz', Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
      rfl
    have hpow : ContinuousOn (fun z : ℂ => (z.im : ℂ) ^ ((k : ℤ) - 2)) uhpC := by
      refine ContinuousOn.zpow₀ (Complex.continuous_ofReal.comp Complex.continuous_im).continuousOn _ ?_
      intro z hz; left; exact Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
    have hprod := ((Complex.continuous_conj.comp_continuousOn hg_cont).mul hf_cont).mul hpow
    refine (hprod.mono stdFDO_C_subset_uhpC).congr fun z hz => ?_
    have hz' : 0 < z.im := hz.2.1
    have himz : (⟨z, hz'⟩ : UpperHalfPlane).im = z.im := rfl
    simp only [φ, dif_pos hz', UpperHalfPlane.petersson, Pi.mul_apply, Function.comp_apply, himz]
    have hpow_eq : (z.im : ℂ) ^ (k : ℤ) * (z.im : ℂ) ^ (-2 : ℤ) = (z.im : ℂ) ^ ((k : ℤ) - 2) := by
      rw [← zpow_add₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz')), sub_eq_add_neg]
    rw [mul_assoc, hpow_eq]
  refine hdom_fdo.mono' (hcont_φ.aestronglyMeasurable measurableSet_stdFDO_C) ?_
  filter_upwards [ae_restrict_mem measurableSet_stdFDO_C] with z hz
  have hz0 : 0 < z.im := hz.2.1
  have hy_ge : y₀ ≤ z.im := stdFD_im_ge (stdFDO_C_subset_stdFD_C hz)
  have hpair : pairToUHP (z.re, z.im) hz0 = ⟨z, hz0⟩ := by
    apply UpperHalfPlane.ext; apply Complex.ext <;> simp [pairToUHP]
  have hf_b : ‖f ⟨z, hz0⟩‖ ≤ Cf * Real.exp (-2 * Real.pi * z.im) := by
    rw [← hpair]; exact hCf (z.re, z.im) hz.1.le hy_ge hz0
  have hg_b := hCg_bound z hz hz0
  have himz0 : (⟨z, hz0⟩ : UpperHalfPlane).im = z.im := rfl
  simp only [dif_pos hz0, UpperHalfPlane.petersson, himz0, norm_mul, Complex.norm_conj,
    norm_zpow, Complex.norm_real, Real.norm_of_nonneg hz0.le]
  have hzpow_comb : z.im ^ (k : ℤ) * z.im ^ (-2 : ℤ) = z.im ^ ((k : ℤ) - 2) := by
    rw [← zpow_add₀ (ne_of_gt hz0), sub_eq_add_neg]
  calc ‖SlashAction.map (k : ℤ) (heckeMat a b d ha hd) (g : UpperHalfPlane → ℂ) ⟨z, hz0⟩‖ *
        ‖f ⟨z, hz0⟩‖ * z.im ^ (k : ℤ) * z.im ^ (-2 : ℤ)
      = ‖SlashAction.map (k : ℤ) (heckeMat a b d ha hd) (g : UpperHalfPlane → ℂ) ⟨z, hz0⟩‖ *
        ‖f ⟨z, hz0⟩‖ * z.im ^ ((k : ℤ) - 2) := by rw [mul_assoc, hzpow_comb]
    _ ≤ Cg * (Cf * Real.exp (-2 * Real.pi * z.im)) * z.im ^ ((k : ℤ) - 2) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul hg_b hf_b (norm_nonneg _) hCg_pos.le) (zpow_nonneg hz0.le _)
    _ = (Cf * Cg) * (Real.exp (-2 * Real.pi * z.im) * z.im ^ ((k : ℤ) - 2)) := by ring
    _ ≤ (Cf * Cg) * (M' * Real.exp (-Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_left (hM' z.im hy_ge) (by positivity)
    _ = (Cf * Cg * M') * Real.exp (-Real.pi * z.im) := by ring

/-- **UNCONDITIONAL SELF-ADJOINTNESS OF PRIME HECKE OPERATORS `T_p`** on `CuspForm SL2ZRange k`
for EVERY weight `k ≥ 1` and EVERY prime `p`:
`peterssonInner (heckeCuspForm k hk p _ f) g = peterssonInner f (heckeCuspForm k hk p _ g)`! -/
theorem peterssonInner_heckeCuspForm_prime_eq {k : ℕ} (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime)
    (f g : CuspForm SL2ZRange (k : ℤ)) :
    peterssonInner (heckeCuspForm k hk p hp.one_lt.le f) g =
      peterssonInner f (heckeCuspForm k hk p hp.one_lt.le g) := by
  by_cases heven : Even k
  · -- Even weight `k`: exact Fricke involution + `Γ₀(p)` fundamental domain swap!
    let F₁ : ℂ → ℂ := fun z =>
      if hz : 0 < z.im then
        UpperHalfPlane.petersson (k : ℤ) g
          (SlashAction.map (k : ℤ) (frickeW p hp.pos) (f : UpperHalfPlane → ℂ)) ⟨z, hz⟩
      else 0
    let F₂ : ℂ → ℂ := fun z =>
      if hz : 0 < z.im then
        UpperHalfPlane.petersson (k : ℤ)
          (SlashAction.map (k : ℤ) (frickeW p hp.pos) (g : UpperHalfPlane → ℂ)) f ⟨z, hz⟩
      else 0
    have hW_pos : 0 < (frickeW p hp.pos).det.val := frickeW_det_pos p hp.pos
    -- Step 1: integrability of each coset piece for `F₂` and `F₁` on `stdFDO_C`.
    have hInt_piece2 : ∀ j : Fin (p + 1),
        IntegrableOn (fun z => F₂ z * ((z.im : ℂ) ^ (-2 : ℤ)))
          (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) '' stdFDO_C) volume := by
      intro j
      rw [integrableOn_mobiusC_hyperbolic_iff (sl2Z_det_pos _) measurableSet_stdFDO_C stdFDO_C_subset_uhpC]
      have hcongr : ∀ z ∈ stdFDO_C,
          F₂ (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z) * ((z.im : ℂ) ^ (-2 : ℤ)) =
          (if hz : 0 < z.im then
            UpperHalfPlane.petersson (k : ℤ)
              (SlashAction.map (k : ℤ) (frickeW p hp.pos * sl2ZToGL2R (gamma0CosetRep p j))
                (g : UpperHalfPlane → ℂ)) f ⟨z, hz⟩ else 0) * ((z.im : ℂ) ^ (-2 : ℤ)) := by
        intro z hz
        have hz0 : 0 < z.im := hz.2.1
        have hmz0 : 0 < (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z).im :=
          mobiusC_mem_uhpC (sl2Z_det_pos _) hz0
        simp only [F₂, dif_pos hmz0, dif_pos hz0]
        congr 1
        have hpt : (⟨mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z, hmz0⟩ : UpperHalfPlane) =
            gamma0CosetRep p j • (⟨z, hz0⟩ : UpperHalfPlane) := by
          apply UpperHalfPlane.ext
          exact mobiusC_eq_smul (sl2Z_det_pos _) hz0
        rw [hpt, ← UpperHalfPlane.petersson_slash_SL]
        have hf_inv : SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (f : UpperHalfPlane → ℂ) =
            (f : UpperHalfPlane → ℂ) := f.slash_action_eq' _ ⟨gamma0CosetRep p j, rfl⟩
        change UpperHalfPlane.petersson (k : ℤ)
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j))
              (SlashAction.map (k : ℤ) (frickeW p hp.pos) (g : UpperHalfPlane → ℂ)))
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (f : UpperHalfPlane → ℂ)) ⟨z, hz0⟩ = _
        rw [hf_inv, ← SlashAction.slash_mul]
      refine (IntegrableOn.congr_fun ?_ (fun z hz => (hcongr z hz).symm) measurableSet_stdFDO_C)
      by_cases hj : j.1 < p
      · have heq_mat : frickeW p hp.pos * sl2ZToGL2R (gamma0CosetRep p j) =
            heckeMat 1 j.1 p zero_lt_one hp.pos := by
          simp only [gamma0CosetRep, if_pos hj]
          exact frickeW_mul_cosetRep_lt p hp.pos j.1 hj
        simpa [heq_mat] using integrableOn_petersson_heckeMat_stdFDO_C hk 1 j.1 p zero_lt_one hp.pos f g
      · have hj1 : gamma0CosetRep p j = 1 := by simp [gamma0CosetRep, hj]
        have hgS : SlashAction.map (k : ℤ) (frickeW p hp.pos * sl2ZToGL2R (gamma0CosetRep p j))
            (g : UpperHalfPlane → ℂ) =
            SlashAction.map (k : ℤ) (heckeMat p 0 1 hp.pos zero_lt_one) (g : UpperHalfPlane → ℂ) := by
          rw [hj1, map_one, mul_one, frickeW_eq_S_mul_heckeMat p hp.pos, SlashAction.slash_mul]
          have hS := g.slash_action_eq' _ ⟨ModularGroup.S, rfl⟩
          change SlashAction.map (k : ℤ) (sl2ZToGL2R ModularGroup.S) (g : UpperHalfPlane → ℂ) =
            (g : UpperHalfPlane → ℂ) at hS
          rw [hS]
        simpa [hgS] using integrableOn_petersson_heckeMat_stdFDO_C hk p 0 1 hp.pos zero_lt_one f g
    have hInt_piece1 : ∀ j : Fin (p + 1),
        IntegrableOn (fun z => F₁ z * ((z.im : ℂ) ^ (-2 : ℤ)))
          (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) '' stdFDO_C) volume := by
      intro j
      -- Notice `F₁ z = star (F₂_swapped z)` where `F₂_swapped` swaps `f` and `g`!
      rw [integrableOn_mobiusC_hyperbolic_iff (sl2Z_det_pos _) measurableSet_stdFDO_C stdFDO_C_subset_uhpC]
      have hcongr : ∀ z ∈ stdFDO_C,
          F₁ (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z) * ((z.im : ℂ) ^ (-2 : ℤ)) =
          star ((if hz : 0 < z.im then
            UpperHalfPlane.petersson (k : ℤ)
              (SlashAction.map (k : ℤ) (frickeW p hp.pos * sl2ZToGL2R (gamma0CosetRep p j))
                (f : UpperHalfPlane → ℂ)) g ⟨z, hz⟩ else 0) * ((z.im : ℂ) ^ (-2 : ℤ))) := by
        intro z hz
        have hz0 : 0 < z.im := hz.2.1
        have hmz0 : 0 < (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z).im :=
          mobiusC_mem_uhpC (sl2Z_det_pos _) hz0
        simp only [F₁, dif_pos hmz0, dif_pos hz0, Complex.star_def, map_mul, map_zpow₀,
          Complex.conj_ofReal]
        congr 1
        have hpt : (⟨mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z, hmz0⟩ : UpperHalfPlane) =
            gamma0CosetRep p j • (⟨z, hz0⟩ : UpperHalfPlane) := by
          apply UpperHalfPlane.ext
          exact mobiusC_eq_smul (sl2Z_det_pos _) hz0
        rw [hpt, ← UpperHalfPlane.petersson_slash_SL, UpperHalfPlane.petersson_symm]
        congr 1
        have hg_inv : SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (g : UpperHalfPlane → ℂ) =
            (g : UpperHalfPlane → ℂ) := g.slash_action_eq' _ ⟨gamma0CosetRep p j, rfl⟩
        change UpperHalfPlane.petersson (k : ℤ)
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j))
              (SlashAction.map (k : ℤ) (frickeW p hp.pos) (f : UpperHalfPlane → ℂ)))
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (g : UpperHalfPlane → ℂ)) ⟨z, hz0⟩ = _
        rw [hg_inv, ← SlashAction.slash_mul]
      refine (IntegrableOn.congr_fun ?_ (fun z hz => (hcongr z hz).symm) measurableSet_stdFDO_C)
      by_cases hj : j.1 < p
      · have heq_mat : frickeW p hp.pos * sl2ZToGL2R (gamma0CosetRep p j) =
            heckeMat 1 j.1 p zero_lt_one hp.pos := by
          simp only [gamma0CosetRep, if_pos hj]
          exact frickeW_mul_cosetRep_lt p hp.pos j.1 hj
        have hbase := integrableOn_petersson_heckeMat_stdFDO_C hk 1 j.1 p zero_lt_one hp.pos g f
        have hconj : IntegrableOn (fun z => star ((if hz : 0 < z.im then
            UpperHalfPlane.petersson (k : ℤ)
              (SlashAction.map (k : ℤ) (heckeMat 1 j.1 p zero_lt_one hp.pos) (f : UpperHalfPlane → ℂ)) g ⟨z, hz⟩
            else 0) * ((z.im : ℂ) ^ (-2 : ℤ)))) stdFDO_C volume :=
          Complex.conjCLE.toContinuousLinearMap.integrable_comp hbase
        rw [heq_mat]; exact hconj
      · have hj1 : gamma0CosetRep p j = 1 := by simp [gamma0CosetRep, hj]
        have hfS : SlashAction.map (k : ℤ) (frickeW p hp.pos * sl2ZToGL2R (gamma0CosetRep p j))
            (f : UpperHalfPlane → ℂ) =
            SlashAction.map (k : ℤ) (heckeMat p 0 1 hp.pos zero_lt_one) (f : UpperHalfPlane → ℂ) := by
          rw [hj1, map_one, mul_one, frickeW_eq_S_mul_heckeMat p hp.pos, SlashAction.slash_mul]
          have hS := f.slash_action_eq' _ ⟨ModularGroup.S, rfl⟩
          change SlashAction.map (k : ℤ) (sl2ZToGL2R ModularGroup.S) (f : UpperHalfPlane → ℂ) =
            (f : UpperHalfPlane → ℂ) at hS
          rw [hS]
        have hbase := integrableOn_petersson_heckeMat_stdFDO_C hk p 0 1 hp.pos zero_lt_one g f
        have hconj : IntegrableOn (fun z => star ((if hz : 0 < z.im then
            UpperHalfPlane.petersson (k : ℤ)
              (SlashAction.map (k : ℤ) (heckeMat p 0 1 hp.pos zero_lt_one) (f : UpperHalfPlane → ℂ)) g ⟨z, hz⟩
            else 0) * ((z.im : ℂ) ^ (-2 : ℤ)))) stdFDO_C volume :=
          Complex.conjCLE.toContinuousLinearMap.integrable_comp hbase
        rw [hfS]; exact hconj
    -- Step 2: `F₁` and `F₂` are integrable on `gamma0FD p`, and `F₂` is integrable on `W_p '' gamma0FD p`.
    have hgamma0_fin : gamma0FD p =
        ⋃ j ∈ (Finset.univ : Finset (Fin (p + 1))),
          mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) '' stdFDO_C := by
      simp [gamma0FD]
    have hInt_F1_D : IntegrableOn (fun z => F₁ z * ((z.im : ℂ) ^ (-2 : ℤ))) (gamma0FD p) volume := by
      rw [hgamma0_fin, integrableOn_finset_iUnion]
      intro j _; exact hInt_piece1 j
    have hInt_F2_D : IntegrableOn (fun z => F₂ z * ((z.im : ℂ) ^ (-2 : ℤ))) (gamma0FD p) volume := by
      rw [hgamma0_fin, integrableOn_finset_iUnion]
      intro j _; exact hInt_piece2 j
    have hF1_eq_F2W : ∀ z ∈ uhpC, F₁ z = F₂ (mobiusC (frickeW p hp.pos) z) := by
      intro z hz
      have hz' : 0 < z.im := hz
      have hWz' : 0 < (mobiusC (frickeW p hp.pos) z).im := mobiusC_mem_uhpC hW_pos hz
      dsimp only [F₁, F₂]
      rw [dif_pos hz', dif_pos hWz']
      have hpt : (⟨mobiusC (frickeW p hp.pos) z, hWz'⟩ : UpperHalfPlane) =
          frickeW p hp.pos • (⟨z, hz'⟩ : UpperHalfPlane) := by
        apply UpperHalfPlane.ext; exact mobiusC_eq_smul hW_pos hz'
      rw [hpt]
      exact petersson_frickeW_swap heven hp.pos f g ⟨z, hz'⟩
    have hInt_F2_DW : IntegrableOn (fun z => F₂ z * ((z.im : ℂ) ^ (-2 : ℤ)))
        (mobiusC (frickeW p hp.pos) '' gamma0FD p) volume := by
      rw [integrableOn_mobiusC_hyperbolic_iff hW_pos (measurableSet_gamma0FD p) (gamma0FD_subset_uhpC p)]
      exact hInt_F1_D.congr_fun (fun z hz => by dsimp only; rw [hF1_eq_F2W z (gamma0FD_subset_uhpC p hz)])
        (measurableSet_gamma0FD p)
    -- Step 3: `peterssonInner (T_p f) g = ∫_{gamma0FD p} F₁ y^{-2}` and
    --         `peterssonInner f (T_p g) = ∫_{gamma0FD p} F₂ y^{-2}`!
    have hLHS : peterssonInner (heckeCuspForm k hk p hp.one_lt.le f) g =
        ∫ z in gamma0FD p, F₁ z * ((z.im : ℂ) ^ (-2 : ℤ)) := by
      rw [peterssonInner_eq_integral_stdFDO_C]
      have hsum_int :
          ∫ z in stdFDO_C,
            (if hz : 0 < z.im then
              UpperHalfPlane.petersson (k : ℤ) g (heckeCuspForm k hk p hp.one_lt.le f) ⟨z, hz⟩
            else 0) * ((z.im : ℂ) ^ (-2 : ℤ)) =
          ∑ j : Fin (p + 1),
            ∫ z in stdFDO_C, F₁ (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z) * ((z.im : ℂ) ^ (-2 : ℤ)) := by
        rw [← integral_finsetSum Finset.univ (fun j _ =>
          (integrableOn_mobiusC_hyperbolic_iff (sl2Z_det_pos _) measurableSet_stdFDO_C
            stdFDO_C_subset_uhpC F₁).mp (hInt_piece1 j))]
        refine setIntegral_congr_fun measurableSet_stdFDO_C fun z hz => ?_
        have hz0 : 0 < z.im := hz.2.1
        simp only [dif_pos hz0, UpperHalfPlane.petersson, heckeCuspForm_prime_eq_sum_frickeW hk hp f ⟨z, hz0⟩,
          Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hmz0 : 0 < (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z).im :=
          mobiusC_mem_uhpC (sl2Z_det_pos _) hz0
        simp only [F₁, dif_pos hmz0]
        congr 1
        have hpt : (⟨mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z, hmz0⟩ : UpperHalfPlane) =
            gamma0CosetRep p j • (⟨z, hz0⟩ : UpperHalfPlane) := by
          apply UpperHalfPlane.ext; exact mobiusC_eq_smul (sl2Z_det_pos _) hz0
        rw [hpt, ← UpperHalfPlane.petersson_slash_SL]
        have hg_inv : SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (g : UpperHalfPlane → ℂ) =
            (g : UpperHalfPlane → ℂ) := g.slash_action_eq' _ ⟨gamma0CosetRep p j, rfl⟩
        change _ = UpperHalfPlane.petersson (k : ℤ)
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (g : UpperHalfPlane → ℂ))
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j))
              (SlashAction.map (k : ℤ) (frickeW p hp.pos) (f : UpperHalfPlane → ℂ))) ⟨z, hz0⟩
        rw [hg_inv, UpperHalfPlane.petersson]
      rw [hsum_int, gamma0FD,
        MeasureTheory.integral_iUnion_fintype
          (fun j => measurableSet_mobiusC_image (sl2Z_det_pos _) measurableSet_stdFDO_C stdFDO_C_subset_uhpC)
          (gamma0_coset_translates_pairwise_disjoint hp.one_lt) hInt_piece1]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (integral_mobiusC_hyperbolic (sl2Z_det_pos _) measurableSet_stdFDO_C
        stdFDO_C_subset_uhpC F₁).symm
    have hRHS : peterssonInner f (heckeCuspForm k hk p hp.one_lt.le g) =
        ∫ z in gamma0FD p, F₂ z * ((z.im : ℂ) ^ (-2 : ℤ)) := by
      rw [peterssonInner_eq_integral_stdFDO_C]
      have hsum_int :
          ∫ z in stdFDO_C,
            (if hz : 0 < z.im then
              UpperHalfPlane.petersson (k : ℤ) (heckeCuspForm k hk p hp.one_lt.le g) f ⟨z, hz⟩
            else 0) * ((z.im : ℂ) ^ (-2 : ℤ)) =
          ∑ j : Fin (p + 1),
            ∫ z in stdFDO_C, F₂ (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z) * ((z.im : ℂ) ^ (-2 : ℤ)) := by
        rw [← integral_finsetSum Finset.univ (fun j _ =>
          (integrableOn_mobiusC_hyperbolic_iff (sl2Z_det_pos _) measurableSet_stdFDO_C
            stdFDO_C_subset_uhpC F₂).mp (hInt_piece2 j))]
        refine setIntegral_congr_fun measurableSet_stdFDO_C fun z hz => ?_
        have hz0 : 0 < z.im := hz.2.1
        simp only [dif_pos hz0, UpperHalfPlane.petersson, heckeCuspForm_prime_eq_sum_frickeW hk hp g ⟨z, hz0⟩,
          map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hmz0 : 0 < (mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z).im :=
          mobiusC_mem_uhpC (sl2Z_det_pos _) hz0
        simp only [F₂, dif_pos hmz0]
        congr 1
        have hpt : (⟨mobiusC (sl2ZToGL2R (gamma0CosetRep p j)) z, hmz0⟩ : UpperHalfPlane) =
            gamma0CosetRep p j • (⟨z, hz0⟩ : UpperHalfPlane) := by
          apply UpperHalfPlane.ext; exact mobiusC_eq_smul (sl2Z_det_pos _) hz0
        rw [hpt, ← UpperHalfPlane.petersson_slash_SL]
        have hf_inv : SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (f : UpperHalfPlane → ℂ) =
            (f : UpperHalfPlane → ℂ) := f.slash_action_eq' _ ⟨gamma0CosetRep p j, rfl⟩
        change _ = UpperHalfPlane.petersson (k : ℤ)
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j))
              (SlashAction.map (k : ℤ) (frickeW p hp.pos) (g : UpperHalfPlane → ℂ)))
            (SlashAction.map (k : ℤ) (sl2ZToGL2R (gamma0CosetRep p j)) (f : UpperHalfPlane → ℂ)) ⟨z, hz0⟩
        rw [hf_inv, UpperHalfPlane.petersson]
      rw [hsum_int, gamma0FD,
        MeasureTheory.integral_iUnion_fintype
          (fun j => measurableSet_mobiusC_image (sl2Z_det_pos _) measurableSet_stdFDO_C stdFDO_C_subset_uhpC)
          (gamma0_coset_translates_pairwise_disjoint hp.one_lt) hInt_piece2]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (integral_mobiusC_hyperbolic (sl2Z_det_pos _) measurableSet_stdFDO_C
        stdFDO_C_subset_uhpC F₂).symm
    -- Step 4: Swap via `W_p` and `integral_frickeW_gamma0FD_eq`!
    have hF2_inv : ∀ (h : SL(2, ℤ)), (p : ℤ) ∣ h 1 0 → ∀ z ∈ uhpC,
        F₂ (mobiusC (sl2ZToGL2R h) z) = F₂ z := by
      intro h hh z hz
      have hz' : 0 < z.im := hz
      have hhz' : 0 < (mobiusC (sl2ZToGL2R h) z).im := mobiusC_mem_uhpC (sl2Z_det_pos h) hz
      dsimp only [F₂]
      rw [dif_pos hhz', dif_pos hz']
      have hpt : (⟨mobiusC (sl2ZToGL2R h) z, hhz'⟩ : UpperHalfPlane) = h • (⟨z, hz'⟩ : UpperHalfPlane) := by
        apply UpperHalfPlane.ext; exact mobiusC_eq_smul (sl2Z_det_pos h) hz'
      rw [hpt]
      exact petersson_frickeW_gamma0_invariant hp.pos f g h hh ⟨z, hz'⟩
    rw [hLHS, hRHS]
    calc ∫ z in gamma0FD p, F₁ z * ((z.im : ℂ) ^ (-2 : ℤ))
        = ∫ z in gamma0FD p, F₂ (mobiusC (frickeW p hp.pos) z) * ((z.im : ℂ) ^ (-2 : ℤ)) :=
          setIntegral_congr_fun (measurableSet_gamma0FD p) fun z hz => by
            rw [hF1_eq_F2W z (gamma0FD_subset_uhpC p hz)]
      _ = ∫ w in mobiusC (frickeW p hp.pos) '' gamma0FD p, F₂ w * ((w.im : ℂ) ^ (-2 : ℤ)) :=
          (integral_mobiusC_hyperbolic hW_pos (measurableSet_gamma0FD p)
            (gamma0FD_subset_uhpC p) F₂).symm
      _ = ∫ z in gamma0FD p, F₂ z * ((z.im : ℂ) ^ (-2 : ℤ)) :=
          integral_frickeW_gamma0FD_eq hp F₂ hF2_inv hInt_F2_D hInt_F2_DW
  · -- Odd weight `k`: `CuspForm SL2ZRange k` is 0-dimensional, so `f = 0` and `g = 0`!
    have hodd : Odd k := Nat.not_even_iff_odd.mp heven
    have hdim0 : Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)) = 0 := by
      rw [finrank_cuspForm_SL2Z, if_pos (Or.inl hodd)]
    have hsub : Subsingleton (CuspForm SL2ZRange (k : ℤ)) :=
      Module.finrank_zero_iff.mp hdim0
    have hf0 : f = 0 := Subsingleton.elim f 0
    have hg0 : g = 0 := Subsingleton.elim g 0
    have hTf0 : heckeCuspForm k hk p hp.one_lt.le f = 0 := Subsingleton.elim _ 0
    have hTg0 : heckeCuspForm k hk p hp.one_lt.le g = 0 := Subsingleton.elim _ 0
    rw [hTf0, hTg0, hf0, hg0]

private lemma heckeCuspForm_congr_n {k : ℕ} (hk : 1 ≤ k) {m n : ℕ} (h : m = n)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (f : CuspForm SL2ZRange (k : ℤ)) :
    heckeCuspForm k hk m hm f = heckeCuspForm k hk n hn f := by
  subst h; rfl

/-- **UNCONDITIONAL SELF-ADJOINTNESS OF ALL LEVEL-1 HECKE OPERATORS `T_n` (`n ≥ 1`)**
for EVERY weight `k ≥ 1` (`0` assumptions!):
$$\langle T_n f, g \rangle_{\mathrm{Pet}} = \langle f, T_n g \rangle_{\mathrm{Pet}}.$$ -/
theorem peterssonInner_heckeCuspForm_eq (k : ℕ) (hk : 1 ≤ k) :
    ∀ (n : ℕ) (hn : 1 ≤ n) (f g : CuspForm SL2ZRange (k : ℤ)),
      peterssonInner (heckeCuspForm k hk n hn f) g =
        peterssonInner f (heckeCuspForm k hk n hn g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn f g
    by_cases hn1 : n = 1
    · rw [heckeCuspForm_congr_n hk hn1 hn le_rfl f, heckeCuspForm_congr_n hk hn1 hn le_rfl g,
        heckeCuspForm_one, heckeCuspForm_one]
    · have hgt1 : 1 < n := by omega
      set p : ℕ := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      set e : ℕ := n.factorization p
      have he_pos : 0 < e := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpdvd
      have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
      set m : ℕ := n / p ^ e
      have hpe_pos : 0 < p ^ e := pow_pos hp.pos e
      have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hpe_dvd) hpe_pos
      have hfac : p ^ e * m = n := Nat.mul_div_cancel' hpe_dvd
      have hcop : Nat.Coprime (p ^ e) m := by
        have hnotdvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (by omega)
        exact (hp.coprime_iff_not_dvd.mpr hnotdvd).pow_left e
      by_cases hm1 : m = 1
      · -- Pure prime power `n = p ^ e`
        have hn_eq : n = p ^ e := by rw [← hfac, hm1, mul_one]
        by_cases he1 : e = 1
        · have hnp : n = p := by rw [hn_eq, he1, pow_one]
          rw [heckeCuspForm_congr_n hk hnp hn hp.one_lt.le f,
            heckeCuspForm_congr_n hk hnp hn hp.one_lt.le g]
          exact peterssonInner_heckeCuspForm_prime_eq hk hp f g
        · set r : ℕ := e - 1
          have hr1 : 1 ≤ r := by omega
          have he_eq : e = r + 1 := by omega
          have hnr : n = p ^ (r + 1) := by rw [hn_eq, he_eq]
          have hpr_lt : p ^ r < n := by rw [hnr]; exact Nat.pow_lt_pow_right hp.one_lt (by omega)
          have hpr1_lt : p ^ (r - 1) < n := by rw [hnr]; exact Nat.pow_lt_pow_right hp.one_lt (by omega)
          rw [heckeCuspForm_congr_n hk hnr hn (Nat.one_le_pow _ _ hp.pos) f,
            heckeCuspForm_congr_n hk hnr hn (Nat.one_le_pow _ _ hp.pos) g]
          have hrec_f := heckeCuspForm_prime_pow k hk hp hr1 f
          have hrec_g := heckeCuspForm_prime_pow k hk hp hr1 g
          rw [hrec_f, hrec_g]
          have hsub_l : ∀ u v w : CuspForm SL2ZRange (k : ℤ),
              peterssonInner (u - v) w = peterssonInner u w - peterssonInner v w := fun u v w => by
            rw [sub_eq_add_neg, peterssonInner_add_left, ← neg_one_smul ℂ v, peterssonInner_smul_left]
            ring
          have hsub_r : ∀ u v w : CuspForm SL2ZRange (k : ℤ),
              peterssonInner u (v - w) = peterssonInner u v - peterssonInner u w := fun u v w => by
            rw [sub_eq_add_neg, peterssonInner_add_right, ← neg_one_smul ℂ w, peterssonInner_smul_right]
            simp [sub_eq_add_neg]
          rw [hsub_l, hsub_r, peterssonInner_smul_left, peterssonInner_smul_right]
          have h1 : peterssonInner
              (heckeCuspForm k hk p hp.one_lt.le (heckeCuspForm k hk (p ^ r) (Nat.one_le_pow _ _ hp.pos) f)) g =
              peterssonInner f
              (heckeCuspForm k hk p hp.one_lt.le (heckeCuspForm k hk (p ^ r) (Nat.one_le_pow _ _ hp.pos) g)) := by
            rw [peterssonInner_heckeCuspForm_prime_eq hk hp,
              ih (p ^ r) hpr_lt (Nat.one_le_pow _ _ hp.pos),
              heckeCuspForm_comm k hk (Nat.one_le_pow _ _ hp.pos) hp.one_lt.le g]
          have h2 : peterssonInner (heckeCuspForm k hk (p ^ (r - 1)) (Nat.one_le_pow _ _ hp.pos) f) g =
              peterssonInner f (heckeCuspForm k hk (p ^ (r - 1)) (Nat.one_le_pow _ _ hp.pos) g) :=
            ih (p ^ (r - 1)) hpr1_lt (Nat.one_le_pow _ _ hp.pos) f g
          have hstar : star ((p : ℂ) ^ (k - 1)) = (p : ℂ) ^ (k - 1) := by
            simp
          rw [h1, h2, hstar]
      · -- Proper coprime factorization `n = p ^ e * m` with `1 < p^e < n` and `1 < m < n`!
        have hpe_gt1 : 1 < p ^ e := one_lt_pow₀ hp.one_lt (by omega)
        have hm_gt1 : 1 < m := by omega
        have hpe_lt : p ^ e < n := by nlinarith
        have hm_lt : m < n := by nlinarith
        have hmul_f := (heckeCuspForm_mul_of_coprime k hk hpe_pos hm_pos hcop f).symm
        have hmul_g := (heckeCuspForm_mul_of_coprime k hk hpe_pos hm_pos hcop g).symm
        have heq_f : heckeCuspForm k hk n hn f =
            heckeCuspForm k hk (p ^ e) hpe_pos (heckeCuspForm k hk m hm_pos f) := by
          simpa [hfac] using hmul_f
        have heq_g : heckeCuspForm k hk n hn g =
            heckeCuspForm k hk (p ^ e) hpe_pos (heckeCuspForm k hk m hm_pos g) := by
          simpa [hfac] using hmul_g
        rw [heq_f, heq_g, ih (p ^ e) hpe_lt hpe_pos, ih m hm_lt hm_pos,
          heckeCuspForm_comm k hk hm_pos hpe_pos g]

/-- **UNCONDITIONAL REALITY OF EVERY LEVEL-1 HECKE EIGENVALUE**:
for EVERY weight `k ≥ 1`, EVERY `n ≥ 1`, and EVERY nonzero cusp form `f ∈ S_k(SL₂(ℤ))` satisfying
`T_n f = μ • f`, the eigenvalue `μ` is purely REAL (`μ.im = 0`)! -/
theorem cuspForm_hecke_eigenvalue_real {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 1 ≤ n)
    {f : CuspForm SL2ZRange (k : ℤ)} (hf : f ≠ 0) {μ : ℂ}
    (heig : heckeCuspForm k hk n hn f = μ • f) :
    μ.im = 0 := by
  have h1 : μ * peterssonInner f f = star μ * peterssonInner f f := by
    calc μ * peterssonInner f f
        = peterssonInner (μ • f) f := (peterssonInner_smul_left μ f f).symm
      _ = peterssonInner (heckeCuspForm k hk n hn f) f := by rw [heig]
      _ = peterssonInner f (heckeCuspForm k hk n hn f) :=
          peterssonInner_heckeCuspForm_eq k hk n hn f f
      _ = peterssonInner f (μ • f) := by rw [heig]
      _ = star μ * peterssonInner f f := peterssonInner_smul_right μ f f
  have hne : peterssonInner f f ≠ 0 := by
    intro h0
    exact hf ((peterssonInner_self_eq_zero_iff f).mp h0)
  have hconj : star μ = μ := (mul_right_cancel₀ hne h1).symm
  exact Complex.conj_eq_iff_im.mp hconj

/-- **GENUINE CONCRETE `PeterssonHeckeSpace 1 k 1 (CuspForm SL2ZRange k)` INSTANCE**
connecting our concrete Petersson inner product and concrete level-1 Hecke operators directly into
`Stage6HeckeSpectral` (`0` assumptions!)! -/
def cuspFormPeterssonHeckeSpace (k : ℕ) (hk : 1 ≤ k) :
    PeterssonHeckeSpace 1 k (1 : DirichletCharacter ℂ 1) (CuspForm SL2ZRange (k : ℤ)) where
  hecke := heckeCuspFormLin k hk
  hecke_one := by
    apply LinearMap.ext; intro f
    simp [heckeCuspForm_one]
  hecke_comm m n _ _ := by
    apply LinearMap.ext; intro f
    by_cases hm : 1 ≤ m <;> by_cases hn : 1 ≤ n
    · simp only [LinearMap.comp_apply, heckeCuspFormLin_apply k hk hm,
        heckeCuspFormLin_apply k hk hn]
      exact heckeCuspForm_comm k hk hm hn f
    · simp [heckeCuspFormLin, dif_neg hn]
    · simp [heckeCuspFormLin, dif_neg hm]
    · simp [heckeCuspFormLin, dif_neg hm]
  hecke_mul_of_coprime m n _ _ hcop := by
    apply LinearMap.ext; intro f
    by_cases hm : 1 ≤ m
    · by_cases hn : 1 ≤ n
      · simp only [LinearMap.comp_apply, heckeCuspFormLin_apply k hk hm,
          heckeCuspFormLin_apply k hk hn, heckeCuspFormLin_apply k hk (Nat.mul_pos hm hn)]
        exact heckeCuspForm_mul_of_coprime k hk hm hn hcop f
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [heckeCuspFormLin]
    · have hm0 : m = 0 := by omega
      subst hm0
      simp [heckeCuspFormLin]
  hecke_prime_pow p hp _ r hr := by
    apply LinearMap.ext; intro f
    have hchi : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime p 1).mpr (Nat.coprime_one_right p))
    rw [hchi, one_mul]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      heckeCuspFormLin_apply k hk (Nat.one_le_pow _ _ hp.pos),
      heckeCuspFormLin_apply k hk hp.one_lt.le]
    exact heckeCuspForm_prime_pow k hk hp hr f
  hecke_adjoint n _ := by
    have hchi : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime n 1).mpr (Nat.coprime_one_right n))
    rw [hchi, star_one, one_smul]
    apply LinearMap.ext; intro g
    refine ext_inner_left ℂ fun f => ?_
    rw [LinearMap.adjoint_inner_right, petersson_inner_eq, petersson_inner_eq]
    by_cases hn : 1 ≤ n
    · simp only [heckeCuspFormLin_apply k hk hn]
      exact (peterssonInner_heckeCuspForm_eq k hk n hn g f).symm
    · simp [heckeCuspFormLin, dif_neg hn, peterssonInner_zero_left, peterssonInner_zero_right]

/-- **MASTER SPECTRAL THEOREM FOR `S_k(SL₂(ℤ))` (`0` Assumptions!)**:
for EVERY weight `k ≥ 1`, the space `CuspForm SL2ZRange (k : ℤ)` admits a Petersson-orthonormal
basis `{f_1, ..., f_d}` of simultaneous Hecke eigenforms for ALL `T_n` (`n ≥ 1`), with purely
real eigenvalues, coprime multiplicativity, and prime-power recurrences! -/
theorem exists_orthonormalBasis_heckeEigenforms_cuspForm_SL2Z (k : ℕ) (hk : 1 ≤ k) :
    ∃ (f : OrthonormalBasis (Fin (Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)))) ℂ
        (CuspForm SL2ZRange (k : ℤ)))
      (lam : Fin (Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ))) → ℕ → ℂ),
      (∀ j n (hn : 1 ≤ n), heckeCuspForm k hk n hn (f j) = lam j n • f j) ∧
      (∀ j n, 1 ≤ n → (lam j n).im = 0) ∧
      (∀ j, lam j 1 = 1) ∧
      (∀ j m n, Nat.Coprime m n → lam j (m * n) = lam j m * lam j n) ∧
      (∀ j p, p.Prime → ∀ r, 1 ≤ r →
        lam j (p ^ (r + 1)) = lam j p * lam j (p ^ r) - (p : ℂ) ^ (k - 1) * lam j (p ^ (r - 1))) := by
  obtain ⟨f, lam, heig, hstar, h1, hmul, hpp⟩ :=
    exists_orthonormalBasis_heckeEigenforms (cuspFormPeterssonHeckeSpace k hk)
  refine ⟨f, lam, ?_, ?_, h1, ?_, ?_⟩
  · intro j n hn
    simpa [cuspFormPeterssonHeckeSpace, heckeCuspFormLin_apply k hk hn] using
      heig j n (Nat.coprime_one_right n)
  · intro j n _
    have hchi : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime n 1).mpr (Nat.coprime_one_right n))
    have hst := hstar j n (Nat.coprime_one_right n)
    rw [hchi, star_one, one_mul] at hst
    exact Complex.conj_eq_iff_im.mp hst
  · intro j m n hmn
    exact hmul j m n (Nat.coprime_one_right m) (Nat.coprime_one_right n) hmn
  · intro j p hp r hr
    have hchi : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 :=
      MulChar.one_apply ((ZMod.isUnit_iff_coprime p 1).mpr (Nat.coprime_one_right p))
    simpa [hchi] using hpp j p hp (Nat.coprime_one_right p) r hr

end HeckeAlgebraAndSelfAdjointness

/-! ## Section 3: General 1-Dimensional Eigenform Theorem & All Five 1D Level-1 Normalized
Hecke Eigenforms (`k = 12, 16, 18, 20, 22`) -/

section OneDimEigenforms

/-! ### Part 3A: General 1-Dimensional Eigenform Theorem & Universal Cusp-Form Euler Product -/

/-- **General 1-Dimensional Hecke Eigenform Theorem (`0` Assumptions!)**:
For EVERY weight `k ≥ 1` with `Module.finrank ℂ (CuspForm SL2ZRange k) = 1` and every normalized
generator `f ∈ S_k(SL₂(ℤ))` (`a₁(f) = 1`):
1. Every `g ∈ S_k(SL₂(ℤ))` equals `a₁(g) • f`, and
2. For EVERY `n ≥ 1`, `T_n f = a_n(f) • f`! -/
theorem cuspForm_eq_smul_of_finrank_eq_one {k : ℕ}
    (hdim : Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)) = 1)
    {f : CuspForm SL2ZRange (k : ℤ)} (hf1 : qExpansionCoeff f 1 = 1)
    (g : CuspForm SL2ZRange (k : ℤ)) :
    g = qExpansionCoeff g 1 • f := by
  have hf_ne : f ≠ 0 := by
    intro h0
    have hq0 : qExpansionCoeff f 1 = 0 := by
      rw [h0]; unfold qExpansionCoeff
      have hzero : ((0 : CuspForm SL2ZRange (k : ℤ)) : UpperHalfPlane → ℂ) =
          (0 : ℂ) • (f : UpperHalfPlane → ℂ) := by
        funext τ; simp
      rw [hzero, ModularForm.qExpansion_smul zero_lt_one one_mem_strictPeriods_SL]
      simp
    rw [hf1] at hq0
    exact one_ne_zero hq0
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' f hf_ne).mp hdim g
  have hc_eq : qExpansionCoeff g 1 = c := by
    rw [← hc, qExpansionCoeff_smul, hf1, mul_one]
  rw [hc_eq, hc]

theorem heckeCuspForm_eigenform_of_dim_one {k : ℕ} (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)) = 1)
    {f : CuspForm SL2ZRange (k : ℤ)} (hf1 : qExpansionCoeff f 1 = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm k hk n hn f = qExpansionCoeff f n • f := by
  have h1 := cuspForm_eq_smul_of_finrank_eq_one hdim hf1 (heckeCuspForm k hk n hn f)
  have hc1 : qExpansionCoeff (heckeCuspForm k hk n hn f) 1 = qExpansionCoeff f n := by
    rw [qExpansionCoeff, heckeCuspForm_qExpansion_coeff k hk n hn f 1,
      heckeOp_apply_one k (1 : DirichletCharacter ℂ 1) hn]
    rfl
  rw [hc1] at h1
  exact h1

/-- Any normalized level-1 cusp form `f` satisfying `∀ n ≥ 1, T_n f = a_n(f) • f` gives an
unconditional `IsNormalizedHeckeEigenform k 1 (qExpansionCoeff f) (qExpansionCoeff f)`. -/
theorem isNormalizedHeckeEigenform_of_heckeCuspForm {k : ℕ} (hk : 1 ≤ k)
    {f : CuspForm SL2ZRange (k : ℤ)} (hf1 : qExpansionCoeff f 1 = 1)
    (heig : ∀ (n : ℕ) (hn : 1 ≤ n), heckeCuspForm k hk n hn f = qExpansionCoeff f n • f) :
    IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff f) (qExpansionCoeff f) := by
  refine ⟨hf1, fun n hn => ?_⟩
  funext m
  have h1 := heckeCuspForm_qExpansion_coeff k hk n hn f m
  have h2 : qExpansionCoeff (heckeCuspForm k hk n hn f) m =
      qExpansionCoeff f n * qExpansionCoeff f m := by
    rw [heig n hn, qExpansionCoeff_smul]
  rw [qExpansionCoeff] at h2
  rw [h2] at h1
  exact h1.symm

theorem isNormalizedHeckeEigenform_of_dim_one {k : ℕ} (hk : 1 ≤ k)
    (hdim : Module.finrank ℂ (CuspForm SL2ZRange (k : ℤ)) = 1)
    {f : CuspForm SL2ZRange (k : ℤ)} (hf1 : qExpansionCoeff f 1 = 1) :
    IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff f) (qExpansionCoeff f) :=
  isNormalizedHeckeEigenform_of_heckeCuspForm hk hf1
    (fun _ hn => heckeCuspForm_eigenform_of_dim_one hk hdim hf1 hn)

/-- Universal absolute convergence of `L(f, s)` on `Re(s) > k / 2 + 1` for every level-1 cusp form
`f ∈ CuspForm SL2ZRange k`. -/
theorem cuspForm_LSeriesSummable {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ))
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (qExpansionCoeff f) s := by
  have hbigO : qExpansionCoeff f =O[Filter.atTop] fun n : ℕ => ((n : ℝ) ^ ((k : ℝ) / 2)) := by
    have h := CuspFormClass.qExpansion_isBigO f
    rw [Subgroup.strictWidthInfty_SL2Z] at h
    exact h
  refine LSeriesSummable_of_isBigO_rpow (x := (k : ℝ) / 2 + 1) hs ?_
  simpa [add_sub_cancel_right] using hbigO

/-- Universal degree-2 Euler product for `LSeries (qExpansionCoeff f) s` of ANY normalized level-1
cusp Hecke eigenform `f ∈ S_k(SL₂(ℤ))` on `Re(s) > k / 2 + 1`. -/
theorem cuspForm_eigenform_LSeries_eulerProduct {k : ℕ} (f : CuspForm SL2ZRange (k : ℤ))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff f) (qExpansionCoeff f))
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeries (qExpansionCoeff f) s =
      ∏' p : Nat.Primes,
        (1 - qExpansionCoeff f p.1 * (p.1 : ℂ) ^ (-s) +
          (p.1 : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s))⁻¹ := by
  have h := eigenform_LSeries_eulerProduct heig (cuspForm_LSeriesSummable f hs)
  rw [← h]
  refine tprod_congr fun p => ?_
  simp only [degree2EulerFactor, trivialChar_one_apply, one_mul]

/-- Universal degree-2 Euler product directly on Mathlib's `ModularForm.L` for ANY normalized
level-1 cusp Hecke eigenform `f ∈ S_k(SL₂(ℤ))` (`0 < k`) on `Re(s) > k / 2 + 1`. -/
theorem cuspForm_eigenform_modularL_eulerProduct {k : ℕ} (hk : 0 < k)
    (f : CuspForm SL2ZRange (k : ℤ))
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff f) (qExpansionCoeff f))
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ModularForm.L (Int.natCast_pos.mpr hk) f s =
      ∏' p : Nat.Primes,
        (1 - qExpansionCoeff f p.1 * (p.1 : ℂ) ^ (-s) +
          (p.1 : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s))⁻¹ := by
  have heig' : IsNormalizedHeckeEigenform (k : ℤ).toNat (1 : DirichletCharacter ℂ 1)
      (fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ)))
      (qExpansionCoeff f) := by
    have hfun : (fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (f : UpperHalfPlane → ℂ))) =
        qExpansionCoeff f := rfl
    rw [Int.toNat_natCast, hfun]
    exact heig
  have h := cuspForm_eigenform_L_eulerProduct Subgroup.strictWidthInfty_SL2Z
    (Int.natCast_pos.mpr hk) f (1 : DirichletCharacter ℂ 1) (qExpansionCoeff f)
    heig' (by simpa using hs)
  rw [← h]
  refine tprod_congr fun p => ?_
  simp only [degree2EulerFactor, trivialChar_one_apply, one_mul, Int.toNat_natCast, qExpansionCoeff]

/-! ### Part 3B: Exact Integer `q`-Expansions & Construction of All Five 1D Eigenforms -/

/-- Exact `q`-expansion identity for the weight-12 cusp-form shift `g ↦ Δ · g`:
`qExpansion 1 ((cuspFormEquivModularFormShift m).symm g) = qExpansion 1 Δ * qExpansion 1 g`. -/
theorem qExpansion_cuspFormShift_symm (m : ℤ) (g : ModularForm SL2ZRange m) :
    UpperHalfPlane.qExpansion 1
        (((cuspFormEquivModularFormShift m).symm g : CuspForm SL2ZRange (m + 12)) :
          UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 (ramanujanDelta : UpperHalfPlane → ℂ) *
        UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) := by
  have hfun :
      (((cuspFormEquivModularFormShift m).symm g : CuspForm SL2ZRange (m + 12)) :
        UpperHalfPlane → ℂ) =
      (CuspForm.toModularFormₗ ramanujanDelta : UpperHalfPlane → ℂ) * (g : UpperHalfPlane → ℂ) := by
    funext τ
    rw [cuspFormEquivModularFormShift_symm_apply]
    rfl
  rw [hfun, ModularForm.qExpansion_mul_coe zero_lt_one one_mem_strictPeriods_SL
    (CuspForm.toModularFormₗ ramanujanDelta) g]
  rfl

/-- Exact integer power series of `E₄(q) = 1 + 240 ∑_{n ≥ 1} σ₃(n) q^n ∈ ℤ⟦q⟧`. -/
def E4SeriesZ : PowerSeries ℤ :=
  1 + 240 * sigma3SeriesZ

/-- Exact integer power series of `E₆(q) = 1 - 504 ∑_{n ≥ 1} σ₅(n) q^n ∈ ℤ⟦q⟧`. -/
def E6SeriesZ : PowerSeries ℤ :=
  1 - 504 * sigma5SeriesZ

private lemma coeff_natCast_mul_Z (c : ℕ) (φ : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((c : PowerSeries ℤ) * φ) = (c : ℤ) * PowerSeries.coeff n φ := by
  rw [← map_natCast (PowerSeries.C (R := ℤ)) c, PowerSeries.coeff_C_mul]

theorem E4SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) E4SeriesZ =
      UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ) := by
  rw [← E4_eq_coe]
  ext n
  rw [PowerSeries.coeff_map, E4_qExpansion_coeff]
  unfold E4SeriesZ
  have h240 : PowerSeries.coeff n ((240 : PowerSeries ℤ) * sigma3SeriesZ) =
      240 * PowerSeries.coeff n sigma3SeriesZ := by
    simpa using coeff_natCast_mul_Z 240 sigma3SeriesZ n
  rw [map_add, h240]
  simp only [sigma3SeriesZ, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs <;> simp

theorem E6SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) E6SeriesZ =
      UpperHalfPlane.qExpansion 1 (ModularForm.E₆ : UpperHalfPlane → ℂ) := by
  rw [← E6_eq_coe]
  ext n
  rw [PowerSeries.coeff_map, E6_qExpansion_coeff]
  unfold E6SeriesZ
  have h504 : PowerSeries.coeff n ((504 : PowerSeries ℤ) * sigma5SeriesZ) =
      504 * PowerSeries.coeff n sigma5SeriesZ := by
    simpa using coeff_natCast_mul_Z 504 sigma5SeriesZ n
  rw [map_sub, h504]
  simp only [sigma5SeriesZ, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs <;> simp

private lemma E4SeriesZ_small_coeffs :
    PowerSeries.coeff 0 E4SeriesZ = 1 ∧
    PowerSeries.coeff 1 E4SeriesZ = 240 ∧
    PowerSeries.coeff 2 E4SeriesZ = 2160 ∧
    PowerSeries.coeff 3 E4SeriesZ = 6720 := by
  have hcast : ∀ n, ((PowerSeries.coeff n E4SeriesZ : ℤ) : ℂ) =
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ModularForm.E₄ : UpperHalfPlane → ℂ)) := fun n => by
    rw [← E4SeriesZ_map_eq, PowerSeries.coeff_map]; rfl
  have ⟨c0, c1, c2, c3⟩ := E4_qExpansion_coeffs_small
  rw [E4_eq_coe] at c0 c1 c2 c3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c0]; norm_num)
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c1]; norm_num)
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c2]; norm_num)
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c3]; norm_num)

private lemma E6SeriesZ_small_coeffs :
    PowerSeries.coeff 0 E6SeriesZ = 1 ∧
    PowerSeries.coeff 1 E6SeriesZ = -504 ∧
    PowerSeries.coeff 2 E6SeriesZ = -16632 ∧
    PowerSeries.coeff 3 E6SeriesZ = -122976 := by
  have hcast : ∀ n, ((PowerSeries.coeff n E6SeriesZ : ℤ) : ℂ) =
      PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (ModularForm.E₆ : UpperHalfPlane → ℂ)) := fun n => by
    rw [← E6SeriesZ_map_eq, PowerSeries.coeff_map]; rfl
  have ⟨c0, c1, c2, c3⟩ := E6_qExpansion_coeffs_small
  rw [E6_eq_coe] at c0 c1 c2 c3
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c0]; norm_num)
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c1]; norm_num)
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c2]; norm_num)
  · exact Int.cast_injective (α := ℂ) (by rw [hcast, c3]; norm_num)

private lemma coeff_mul_Z_0 (f g : PowerSeries ℤ) :
    PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g)]
  simp

private lemma coeff_mul_Z_1 (f g : PowerSeries ℤ) :
    PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g)]
  simp [Finset.sum_range_succ]

private lemma coeff_mul_Z_2 (f g : PowerSeries ℤ) :
    PowerSeries.coeff 2 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g)]
  simp [Finset.sum_range_succ]

private lemma coeff_mul_Z_3 (f g : PowerSeries ℤ) :
    PowerSeries.coeff 3 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 3 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 2 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 3 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g)]
  simp [Finset.sum_range_succ]

private lemma coeff_mul_Z_4 (f g : PowerSeries ℤ) :
    PowerSeries.coeff 4 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 4 g +
      PowerSeries.coeff 1 f * PowerSeries.coeff 3 g +
      PowerSeries.coeff 2 f * PowerSeries.coeff 2 g +
      PowerSeries.coeff 3 f * PowerSeries.coeff 1 g +
      PowerSeries.coeff 4 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g)]
  simp [Finset.sum_range_succ]

/-- The five 1-dimensional cusp form spaces `S_{12}, S_{16}, S_{18}, S_{20}, S_{22}` all have
`Module.finrank ℂ = 1`. -/
theorem finrank_cuspForm_SL2Z_five_oneDim :
    Module.finrank ℂ (CuspForm SL2ZRange 12) = 1 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 16) = 1 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 18) = 1 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 20) = 1 ∧
    Module.finrank ℂ (CuspForm SL2ZRange 22) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 12
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 16
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 18
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 20
  · simpa [Nat.odd_iff] using finrank_cuspForm_SL2Z 22

/-- **The Five Canonical Normalized Level-1 Cusp-Form Eigenforms**:
- `Δ₁₂ := Δ ∈ S₁₂`
- `Δ₁₆ := E₄ · Δ ∈ S₁₆`
- `Δ₁₈ := E₆ · Δ ∈ S₁₈`
- `Δ₂₀ := E₄² · Δ ∈ S₂₀`
- `Δ₂₂ := E₄ E₆ · Δ ∈ S₂₂` -/
def delta12 : CuspForm SL2ZRange 12 := ramanujanDelta
def delta16 : CuspForm SL2ZRange 16 := (cuspFormEquivModularFormShift 4).symm ModularForm.E₄
def delta18 : CuspForm SL2ZRange 18 := (cuspFormEquivModularFormShift 6).symm ModularForm.E₆
def delta20 : CuspForm SL2ZRange 20 := (cuspFormEquivModularFormShift 8).symm (monomialE4E6 2 0)
def delta22 : CuspForm SL2ZRange 22 := (cuspFormEquivModularFormShift 10).symm (monomialE4E6 1 1)

/-- Exact integer power series and integer Fourier coefficient sequences for `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂`. -/
def delta16SeriesZ : PowerSeries ℤ := ramanujanDeltaPowerSeriesZ * E4SeriesZ
def delta18SeriesZ : PowerSeries ℤ := ramanujanDeltaPowerSeriesZ * E6SeriesZ
def delta20SeriesZ : PowerSeries ℤ := ramanujanDeltaPowerSeriesZ * E4SeriesZ ^ 2
def delta22SeriesZ : PowerSeries ℤ := ramanujanDeltaPowerSeriesZ * (E4SeriesZ * E6SeriesZ)

def coeffDelta12Z (n : ℕ) : ℤ := ramanujanTau n
def coeffDelta16Z (n : ℕ) : ℤ := PowerSeries.coeff n delta16SeriesZ
def coeffDelta18Z (n : ℕ) : ℤ := PowerSeries.coeff n delta18SeriesZ
def coeffDelta20Z (n : ℕ) : ℤ := PowerSeries.coeff n delta20SeriesZ
def coeffDelta22Z (n : ℕ) : ℤ := PowerSeries.coeff n delta22SeriesZ

theorem delta16SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) delta16SeriesZ =
      UpperHalfPlane.qExpansion 1 (delta16 : UpperHalfPlane → ℂ) := by
  unfold delta16SeriesZ delta16
  rw [map_mul, ramanujanDeltaPowerSeriesZ_map_eq, E4SeriesZ_map_eq, qExpansion_cuspFormShift_symm]

theorem delta18SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) delta18SeriesZ =
      UpperHalfPlane.qExpansion 1 (delta18 : UpperHalfPlane → ℂ) := by
  unfold delta18SeriesZ delta18
  rw [map_mul, ramanujanDeltaPowerSeriesZ_map_eq, E6SeriesZ_map_eq, qExpansion_cuspFormShift_symm]

theorem delta20SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) delta20SeriesZ =
      UpperHalfPlane.qExpansion 1 (delta20 : UpperHalfPlane → ℂ) := by
  unfold delta20SeriesZ delta20
  rw [map_mul, map_pow, ramanujanDeltaPowerSeriesZ_map_eq, E4SeriesZ_map_eq,
    qExpansion_cuspFormShift_symm]
  congr 1
  unfold monomialE4E6
  rw [ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL]
  simp

theorem delta22SeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) delta22SeriesZ =
      UpperHalfPlane.qExpansion 1 (delta22 : UpperHalfPlane → ℂ) := by
  unfold delta22SeriesZ delta22
  rw [map_mul, map_mul, ramanujanDeltaPowerSeriesZ_map_eq, E4SeriesZ_map_eq, E6SeriesZ_map_eq,
    qExpansion_cuspFormShift_symm]
  congr 1
  unfold monomialE4E6
  rw [ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL]
  simp

theorem coeffDelta16Z_cast_eq (n : ℕ) : (coeffDelta16Z n : ℂ) = qExpansionCoeff delta16 n := by
  unfold qExpansionCoeff; rw [← delta16SeriesZ_map_eq, PowerSeries.coeff_map]; rfl

theorem coeffDelta18Z_cast_eq (n : ℕ) : (coeffDelta18Z n : ℂ) = qExpansionCoeff delta18 n := by
  unfold qExpansionCoeff; rw [← delta18SeriesZ_map_eq, PowerSeries.coeff_map]; rfl

theorem coeffDelta20Z_cast_eq (n : ℕ) : (coeffDelta20Z n : ℂ) = qExpansionCoeff delta20 n := by
  unfold qExpansionCoeff; rw [← delta20SeriesZ_map_eq, PowerSeries.coeff_map]; rfl

theorem coeffDelta22Z_cast_eq (n : ℕ) : (coeffDelta22Z n : ℂ) = qExpansionCoeff delta22 n := by
  unfold qExpansionCoeff; rw [← delta22SeriesZ_map_eq, PowerSeries.coeff_map]; rfl

/-- Verified exact small integer Fourier coefficients for `Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂`:
- `Δ₁₆`: `a₀ = 0, a₁ = 1, a₂ = 216, a₃ = -3348`
- `Δ₁₈`: `a₀ = 0, a₁ = 1, a₂ = -528, a₃ = -4284`
- `Δ₂₀`: `a₀ = 0, a₁ = 1, a₂ = 456, a₃ = 50652`
- `Δ₂₂`: `a₀ = 0, a₁ = 1, a₂ = -288, a₃ = -128844` -/
theorem coeffDelta16Z_small :
    coeffDelta16Z 0 = 0 ∧ coeffDelta16Z 1 = 1 ∧ coeffDelta16Z 2 = 216 ∧ coeffDelta16Z 3 = -3348 := by
  have ⟨e0, e1, e2, _⟩ := E4SeriesZ_small_coeffs
  have t0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  have t1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
  have t2 : PowerSeries.coeff 2 ramanujanDeltaPowerSeriesZ = -24 := ramanujanTau_two
  have t3 : PowerSeries.coeff 3 ramanujanDeltaPowerSeriesZ = 252 := ramanujanTau_three
  unfold coeffDelta16Z delta16SeriesZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff_mul_Z_0, t0, zero_mul]
  · rw [coeff_mul_Z_1, t0, t1, e0, e1]; norm_num
  · rw [coeff_mul_Z_2, t0, t1, t2, e0, e1, e2]; norm_num
  · rw [coeff_mul_Z_3, t0, t1, t2, t3, e0, e1, e2]; norm_num

theorem coeffDelta18Z_small :
    coeffDelta18Z 0 = 0 ∧ coeffDelta18Z 1 = 1 ∧ coeffDelta18Z 2 = -528 ∧ coeffDelta18Z 3 = -4284 := by
  have ⟨e0, e1, e2, _⟩ := E6SeriesZ_small_coeffs
  have t0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  have t1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
  have t2 : PowerSeries.coeff 2 ramanujanDeltaPowerSeriesZ = -24 := ramanujanTau_two
  have t3 : PowerSeries.coeff 3 ramanujanDeltaPowerSeriesZ = 252 := ramanujanTau_three
  unfold coeffDelta18Z delta18SeriesZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff_mul_Z_0, t0, zero_mul]
  · rw [coeff_mul_Z_1, t0, t1, e0, e1]; norm_num
  · rw [coeff_mul_Z_2, t0, t1, t2, e0, e1, e2]; norm_num
  · rw [coeff_mul_Z_3, t0, t1, t2, t3, e0, e1, e2]; norm_num

theorem coeffDelta20Z_small :
    coeffDelta20Z 0 = 0 ∧ coeffDelta20Z 1 = 1 ∧ coeffDelta20Z 2 = 456 ∧ coeffDelta20Z 3 = 50652 := by
  have ⟨e0, e1, e2, _⟩ := E4SeriesZ_small_coeffs
  have t0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  have t1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
  have t2 : PowerSeries.coeff 2 ramanujanDeltaPowerSeriesZ = -24 := ramanujanTau_two
  have t3 : PowerSeries.coeff 3 ramanujanDeltaPowerSeriesZ = 252 := ramanujanTau_three
  have s0 : PowerSeries.coeff 0 (E4SeriesZ ^ 2) = 1 := by
    rw [sq, coeff_mul_Z_0, e0]; norm_num
  have s1 : PowerSeries.coeff 1 (E4SeriesZ ^ 2) = 480 := by
    rw [sq, coeff_mul_Z_1, e0, e1]; norm_num
  have s2 : PowerSeries.coeff 2 (E4SeriesZ ^ 2) = 61920 := by
    rw [sq, coeff_mul_Z_2, e0, e1, e2]; norm_num
  unfold coeffDelta20Z delta20SeriesZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff_mul_Z_0, t0, zero_mul]
  · rw [coeff_mul_Z_1, t0, t1, s0, s1]; norm_num
  · rw [coeff_mul_Z_2, t0, t1, t2, s0, s1, s2]; norm_num
  · rw [coeff_mul_Z_3, t0, t1, t2, t3, s0, s1, s2]; norm_num

theorem coeffDelta22Z_small :
    coeffDelta22Z 0 = 0 ∧ coeffDelta22Z 1 = 1 ∧ coeffDelta22Z 2 = -288 ∧ coeffDelta22Z 3 = -128844 := by
  have ⟨e0, e1, e2, _⟩ := E4SeriesZ_small_coeffs
  have ⟨f0, f1, f2, _⟩ := E6SeriesZ_small_coeffs
  have t0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  have t1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
  have t2 : PowerSeries.coeff 2 ramanujanDeltaPowerSeriesZ = -24 := ramanujanTau_two
  have t3 : PowerSeries.coeff 3 ramanujanDeltaPowerSeriesZ = 252 := ramanujanTau_three
  have p0 : PowerSeries.coeff 0 (E4SeriesZ * E6SeriesZ) = 1 := by
    rw [coeff_mul_Z_0, e0, f0]; norm_num
  have p1 : PowerSeries.coeff 1 (E4SeriesZ * E6SeriesZ) = -264 := by
    rw [coeff_mul_Z_1, e0, e1, f0, f1]; norm_num
  have p2 : PowerSeries.coeff 2 (E4SeriesZ * E6SeriesZ) = -135432 := by
    rw [coeff_mul_Z_2, e0, e1, e2, f0, f1, f2]; norm_num
  unfold coeffDelta22Z delta22SeriesZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coeff_mul_Z_0, t0, zero_mul]
  · rw [coeff_mul_Z_1, t0, t1, p0, p1]; norm_num
  · rw [coeff_mul_Z_2, t0, t1, t2, p0, p1, p2]; norm_num
  · rw [coeff_mul_Z_3, t0, t1, t2, t3, p0, p1, p2]; norm_num

/-- **Unconditional Simultaneous Hecke Eigenform Theorems for All Five 1D Weights
`k ∈ {12, 16, 18, 20, 22}` (`0` Assumptions!)**. -/
theorem heckeCuspForm_delta12 {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm 12 (by norm_num) n hn delta12 = (coeffDelta12Z n : ℂ) • delta12 :=
  heckeCuspForm_ramanujanDelta hn

theorem heckeCuspForm_delta16 {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm 16 (by norm_num) n hn delta16 = (coeffDelta16Z n : ℂ) • delta16 := by
  rw [coeffDelta16Z_cast_eq]
  exact heckeCuspForm_eigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.1
    (by rw [← coeffDelta16Z_cast_eq, coeffDelta16Z_small.2.1]; simp) hn

theorem heckeCuspForm_delta18 {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm 18 (by norm_num) n hn delta18 = (coeffDelta18Z n : ℂ) • delta18 := by
  rw [coeffDelta18Z_cast_eq]
  exact heckeCuspForm_eigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.2.1
    (by rw [← coeffDelta18Z_cast_eq, coeffDelta18Z_small.2.1]; simp) hn

theorem heckeCuspForm_delta20 {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm 20 (by norm_num) n hn delta20 = (coeffDelta20Z n : ℂ) • delta20 := by
  rw [coeffDelta20Z_cast_eq]
  exact heckeCuspForm_eigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.2.2.1
    (by rw [← coeffDelta20Z_cast_eq, coeffDelta20Z_small.2.1]; simp) hn

theorem heckeCuspForm_delta22 {n : ℕ} (hn : 1 ≤ n) :
    heckeCuspForm 22 (by norm_num) n hn delta22 = (coeffDelta22Z n : ℂ) • delta22 := by
  rw [coeffDelta22Z_cast_eq]
  exact heckeCuspForm_eigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.2.2.2
    (by rw [← coeffDelta22Z_cast_eq, coeffDelta22Z_small.2.1]; simp) hn

theorem isNormalizedHeckeEigenform_delta16 :
    IsNormalizedHeckeEigenform 16 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff delta16) (qExpansionCoeff delta16) :=
  isNormalizedHeckeEigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.1
    (by rw [← coeffDelta16Z_cast_eq, coeffDelta16Z_small.2.1]; simp)

theorem isNormalizedHeckeEigenform_delta18 :
    IsNormalizedHeckeEigenform 18 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff delta18) (qExpansionCoeff delta18) :=
  isNormalizedHeckeEigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.2.1
    (by rw [← coeffDelta18Z_cast_eq, coeffDelta18Z_small.2.1]; simp)

theorem isNormalizedHeckeEigenform_delta20 :
    IsNormalizedHeckeEigenform 20 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff delta20) (qExpansionCoeff delta20) :=
  isNormalizedHeckeEigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.2.2.1
    (by rw [← coeffDelta20Z_cast_eq, coeffDelta20Z_small.2.1]; simp)

theorem isNormalizedHeckeEigenform_delta22 :
    IsNormalizedHeckeEigenform 22 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff delta22) (qExpansionCoeff delta22) :=
  isNormalizedHeckeEigenform_of_dim_one (by norm_num) finrank_cuspForm_SL2Z_five_oneDim.2.2.2.2
    (by rw [← coeffDelta22Z_cast_eq, coeffDelta22Z_small.2.1]; simp)

/-- Helper lifting `IsNormalizedHeckeEigenform` to exact integer multiplicativity & prime-power
recurrence. -/
private lemma int_mult_and_prime_pow_of_eigenform {k : ℕ} (aZ : ℕ → ℤ) (aC : ℕ → ℂ)
    (hcast : ∀ n, (aZ n : ℂ) = aC n) (h0 : aZ 0 = 0)
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1) aC aC) :
    (∀ m n, Nat.Coprime m n → aZ (m * n) = aZ m * aZ n) ∧
    (∀ p, p.Prime → ∀ r, aZ (p ^ (r + 2)) = aZ p * aZ (p ^ (r + 1)) - (p : ℤ) ^ (k - 1) * aZ (p ^ r)) := by
  constructor
  · intro m n hcop
    by_cases hm : m = 0
    · subst hm; simp [h0]
    by_cases hn : n = 0
    · subst hn; simp [h0]
    have hC := eigenform_isMultiplicative heig (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop
    exact Int.cast_injective (α := ℂ) (by simpa [hcast] using hC)
  · intro p hp r
    have hC := eigenform_prime_pow_recurrence heig hp r
    rw [trivialChar_one_apply, one_mul] at hC
    exact Int.cast_injective (α := ℂ) (by simpa [hcast] using hC)

/-- **UNCONDITIONAL INTEGER MULTIPLICATIVITY & PRIME-POWER RECURRENCE FOR ALL FIVE 1D WEIGHTS
`k = 12, 16, 18, 20, 22` (`0` Assumptions!)**. -/
theorem coeffDelta16Z_mul_and_prime_pow :
    (∀ m n, Nat.Coprime m n → coeffDelta16Z (m * n) = coeffDelta16Z m * coeffDelta16Z n) ∧
    (∀ p, p.Prime → ∀ r,
      coeffDelta16Z (p ^ (r + 2)) =
        coeffDelta16Z p * coeffDelta16Z (p ^ (r + 1)) - (p : ℤ) ^ 15 * coeffDelta16Z (p ^ r)) :=
  int_mult_and_prime_pow_of_eigenform coeffDelta16Z (qExpansionCoeff delta16)
    coeffDelta16Z_cast_eq coeffDelta16Z_small.1 isNormalizedHeckeEigenform_delta16

theorem coeffDelta18Z_mul_and_prime_pow :
    (∀ m n, Nat.Coprime m n → coeffDelta18Z (m * n) = coeffDelta18Z m * coeffDelta18Z n) ∧
    (∀ p, p.Prime → ∀ r,
      coeffDelta18Z (p ^ (r + 2)) =
        coeffDelta18Z p * coeffDelta18Z (p ^ (r + 1)) - (p : ℤ) ^ 17 * coeffDelta18Z (p ^ r)) :=
  int_mult_and_prime_pow_of_eigenform coeffDelta18Z (qExpansionCoeff delta18)
    coeffDelta18Z_cast_eq coeffDelta18Z_small.1 isNormalizedHeckeEigenform_delta18

theorem coeffDelta20Z_mul_and_prime_pow :
    (∀ m n, Nat.Coprime m n → coeffDelta20Z (m * n) = coeffDelta20Z m * coeffDelta20Z n) ∧
    (∀ p, p.Prime → ∀ r,
      coeffDelta20Z (p ^ (r + 2)) =
        coeffDelta20Z p * coeffDelta20Z (p ^ (r + 1)) - (p : ℤ) ^ 19 * coeffDelta20Z (p ^ r)) :=
  int_mult_and_prime_pow_of_eigenform coeffDelta20Z (qExpansionCoeff delta20)
    coeffDelta20Z_cast_eq coeffDelta20Z_small.1 isNormalizedHeckeEigenform_delta20

theorem coeffDelta22Z_mul_and_prime_pow :
    (∀ m n, Nat.Coprime m n → coeffDelta22Z (m * n) = coeffDelta22Z m * coeffDelta22Z n) ∧
    (∀ p, p.Prime → ∀ r,
      coeffDelta22Z (p ^ (r + 2)) =
        coeffDelta22Z p * coeffDelta22Z (p ^ (r + 1)) - (p : ℤ) ^ 21 * coeffDelta22Z (p ^ r)) :=
  int_mult_and_prime_pow_of_eigenform coeffDelta22Z (qExpansionCoeff delta22)
    coeffDelta22Z_cast_eq coeffDelta22Z_small.1 isNormalizedHeckeEigenform_delta22

/-- **UNCONDITIONAL DEGREE-2 EULER PRODUCTS FOR ALL FIVE 1D WEIGHTS (`k = 12, 16, 18, 20, 22`)**! -/
theorem delta12_LSeries_eulerProduct {s : ℂ} (hs : 7 < s.re) :
    LSeries (fun n => (coeffDelta12Z n : ℂ)) s =
      ∏' p : Nat.Primes, (1 - (coeffDelta12Z p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (11 - 2 * s))⁻¹ :=
  ramanujanDelta_LSeries_eulerProduct hs

theorem delta16_LSeries_eulerProduct {s : ℂ} (hs : 9 < s.re) :
    LSeries (fun n => (coeffDelta16Z n : ℂ)) s =
      ∏' p : Nat.Primes, (1 - (coeffDelta16Z p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (15 - 2 * s))⁻¹ := by
  have hfun : (fun n => (coeffDelta16Z n : ℂ)) = qExpansionCoeff delta16 :=
    funext coeffDelta16Z_cast_eq
  rw [hfun]
  have h := cuspForm_eigenform_LSeries_eulerProduct delta16 isNormalizedHeckeEigenform_delta16
    (by norm_num; linarith)
  rw [h]
  refine tprod_congr fun p => ?_
  rw [coeffDelta16Z_cast_eq]; norm_num

theorem delta18_LSeries_eulerProduct {s : ℂ} (hs : 10 < s.re) :
    LSeries (fun n => (coeffDelta18Z n : ℂ)) s =
      ∏' p : Nat.Primes, (1 - (coeffDelta18Z p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (17 - 2 * s))⁻¹ := by
  have hfun : (fun n => (coeffDelta18Z n : ℂ)) = qExpansionCoeff delta18 :=
    funext coeffDelta18Z_cast_eq
  rw [hfun]
  have h := cuspForm_eigenform_LSeries_eulerProduct delta18 isNormalizedHeckeEigenform_delta18
    (by norm_num; linarith)
  rw [h]
  refine tprod_congr fun p => ?_
  rw [coeffDelta18Z_cast_eq]; norm_num

theorem delta20_LSeries_eulerProduct {s : ℂ} (hs : 11 < s.re) :
    LSeries (fun n => (coeffDelta20Z n : ℂ)) s =
      ∏' p : Nat.Primes, (1 - (coeffDelta20Z p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (19 - 2 * s))⁻¹ := by
  have hfun : (fun n => (coeffDelta20Z n : ℂ)) = qExpansionCoeff delta20 :=
    funext coeffDelta20Z_cast_eq
  rw [hfun]
  have h := cuspForm_eigenform_LSeries_eulerProduct delta20 isNormalizedHeckeEigenform_delta20
    (by norm_num; linarith)
  rw [h]
  refine tprod_congr fun p => ?_
  rw [coeffDelta20Z_cast_eq]; norm_num

theorem delta22_LSeries_eulerProduct {s : ℂ} (hs : 12 < s.re) :
    LSeries (fun n => (coeffDelta22Z n : ℂ)) s =
      ∏' p : Nat.Primes, (1 - (coeffDelta22Z p.1 : ℂ) * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (21 - 2 * s))⁻¹ := by
  have hfun : (fun n => (coeffDelta22Z n : ℂ)) = qExpansionCoeff delta22 :=
    funext coeffDelta22Z_cast_eq
  rw [hfun]
  have h := cuspForm_eigenform_LSeries_eulerProduct delta22 isNormalizedHeckeEigenform_delta22
    (by norm_num; linarith)
  rw [h]
  refine tprod_congr fun p => ?_
  rw [coeffDelta22Z_cast_eq]; norm_num

end OneDimEigenforms

/-! ## Section 4: Weight-24 (`dim S₂₄ = 2`) Explicit Hecke Diagonalization & Hecke's First
Irrational Eigenvalue Field `ℚ(√144169)` -/

section Weight24HeckeDiagonalization

/-- Canonical spanning pair of `S₂₄(SL₂(ℤ))`:
- `S24_E4CubeDelta := E₄³ · Δ ∈ S₂₄`
- `S24_DeltaSq := Δ² ∈ S₂₄` -/
def S24_E4CubeDelta : CuspForm SL2ZRange 24 :=
  (cuspFormEquivModularFormShift 12).symm (monomialE4E6 3 0)

def S24_DeltaSq : CuspForm SL2ZRange 24 :=
  (cuspFormEquivModularFormShift 12).symm (CuspForm.toModularFormₗ ramanujanDelta)

/-- Exact Victor Miller basis `{S24_vm1, S24_vm2}` of `S₂₄(SL₂(ℤ))`:
- `S24_vm1 := E₄³ · Δ - 696 · Δ² = q + 0 q² + 195660 q³ + 12080128 q⁴ + ...`
- `S24_vm2 := Δ² = 0 q + q² - 48 q³ + 1080 q⁴ + ...` -/
def S24_vm1 : CuspForm SL2ZRange 24 :=
  S24_E4CubeDelta - (696 : ℂ) • S24_DeltaSq

def S24_vm2 : CuspForm SL2ZRange 24 :=
  S24_DeltaSq

private def S24_E4CubeDeltaSeriesZ : PowerSeries ℤ := ramanujanDeltaPowerSeriesZ * E4SeriesZ ^ 3
private def S24_DeltaSqSeriesZ : PowerSeries ℤ := ramanujanDeltaPowerSeriesZ * ramanujanDeltaPowerSeriesZ

private lemma S24_E4CubeDeltaSeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) S24_E4CubeDeltaSeriesZ =
      UpperHalfPlane.qExpansion 1 (S24_E4CubeDelta : UpperHalfPlane → ℂ) := by
  unfold S24_E4CubeDeltaSeriesZ S24_E4CubeDelta
  rw [map_mul, map_pow, ramanujanDeltaPowerSeriesZ_map_eq, E4SeriesZ_map_eq,
    qExpansion_cuspFormShift_symm]
  congr 1
  unfold monomialE4E6
  rw [ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_mul zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL]
  simp

private lemma S24_DeltaSqSeriesZ_map_eq :
    PowerSeries.map (Int.castRingHom ℂ) S24_DeltaSqSeriesZ =
      UpperHalfPlane.qExpansion 1 (S24_DeltaSq : UpperHalfPlane → ℂ) := by
  unfold S24_DeltaSqSeriesZ S24_DeltaSq
  rw [map_mul, ramanujanDeltaPowerSeriesZ_map_eq, qExpansion_cuspFormShift_symm]
  rfl

/-- Exact leading Fourier coefficients of `E₄³ Δ`:
`a₁ = 1, a₂ = 696, a₃ = 162252, a₄ = 12831808`. -/
theorem S24_E4CubeDelta_coeffs :
    qExpansionCoeff S24_E4CubeDelta 0 = 0 ∧
    qExpansionCoeff S24_E4CubeDelta 1 = 1 ∧
    qExpansionCoeff S24_E4CubeDelta 2 = 696 ∧
    qExpansionCoeff S24_E4CubeDelta 3 = 162252 ∧
    qExpansionCoeff S24_E4CubeDelta 4 = 12831808 := by
  have ⟨e0, e1, e2, e3⟩ := E4SeriesZ_small_coeffs
  have t0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  have t1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
  have t2 : PowerSeries.coeff 2 ramanujanDeltaPowerSeriesZ = -24 := ramanujanTau_two
  have t3 : PowerSeries.coeff 3 ramanujanDeltaPowerSeriesZ = 252 := ramanujanTau_three
  have t4 : PowerSeries.coeff 4 ramanujanDeltaPowerSeriesZ = -1472 := ramanujanTau_four
  have s0 : PowerSeries.coeff 0 (E4SeriesZ ^ 2) = 1 := by rw [sq, coeff_mul_Z_0, e0]; norm_num
  have s1 : PowerSeries.coeff 1 (E4SeriesZ ^ 2) = 480 := by rw [sq, coeff_mul_Z_1, e0, e1]; norm_num
  have s2 : PowerSeries.coeff 2 (E4SeriesZ ^ 2) = 61920 := by rw [sq, coeff_mul_Z_2, e0, e1, e2]; norm_num
  have s3 : PowerSeries.coeff 3 (E4SeriesZ ^ 2) = 1050240 := by
    rw [sq, coeff_mul_Z_3, e0, e1, e2, e3]; norm_num
  have c0 : PowerSeries.coeff 0 (E4SeriesZ ^ 3) = 1 := by
    rw [pow_succ, coeff_mul_Z_0, s0, e0]; norm_num
  have c1 : PowerSeries.coeff 1 (E4SeriesZ ^ 3) = 720 := by
    rw [pow_succ, coeff_mul_Z_1, s0, s1, e0, e1]; norm_num
  have c2 : PowerSeries.coeff 2 (E4SeriesZ ^ 3) = 179280 := by
    rw [pow_succ, coeff_mul_Z_2, s0, s1, s2, e0, e1, e2]; norm_num
  have c3 : PowerSeries.coeff 3 (E4SeriesZ ^ 3) = 16954560 := by
    rw [pow_succ, coeff_mul_Z_3, s0, s1, s2, s3, e0, e1, e2, e3]; norm_num
  have hcast : ∀ n, qExpansionCoeff S24_E4CubeDelta n =
      ((PowerSeries.coeff n S24_E4CubeDeltaSeriesZ : ℤ) : ℂ) := fun n => by
    rw [qExpansionCoeff, ← S24_E4CubeDeltaSeriesZ_map_eq, PowerSeries.coeff_map]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcast]; unfold S24_E4CubeDeltaSeriesZ; rw [coeff_mul_Z_0, t0]; simp
  · rw [hcast]; unfold S24_E4CubeDeltaSeriesZ; rw [coeff_mul_Z_1, t0, t1, c0, c1]; norm_num
  · rw [hcast]; unfold S24_E4CubeDeltaSeriesZ; rw [coeff_mul_Z_2, t0, t1, t2, c0, c1, c2]; norm_num
  · rw [hcast]; unfold S24_E4CubeDeltaSeriesZ; rw [coeff_mul_Z_3, t0, t1, t2, t3, c0, c1, c2, c3]; norm_num
  · rw [hcast]; unfold S24_E4CubeDeltaSeriesZ; rw [coeff_mul_Z_4, t0, t1, t2, t3, t4, c0, c1, c2, c3]; norm_num

/-- Exact leading Fourier coefficients of `Δ²`:
`a₀ = 0, a₁ = 0, a₂ = 1, a₃ = -48, a₄ = 1080`. -/
theorem S24_DeltaSq_coeffs :
    qExpansionCoeff S24_DeltaSq 0 = 0 ∧
    qExpansionCoeff S24_DeltaSq 1 = 0 ∧
    qExpansionCoeff S24_DeltaSq 2 = 1 ∧
    qExpansionCoeff S24_DeltaSq 3 = -48 ∧
    qExpansionCoeff S24_DeltaSq 4 = 1080 := by
  have t0 : PowerSeries.coeff 0 ramanujanDeltaPowerSeriesZ = 0 := ramanujanTau_zero
  have t1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
  have t2 : PowerSeries.coeff 2 ramanujanDeltaPowerSeriesZ = -24 := ramanujanTau_two
  have t3 : PowerSeries.coeff 3 ramanujanDeltaPowerSeriesZ = 252 := ramanujanTau_three
  have t4 : PowerSeries.coeff 4 ramanujanDeltaPowerSeriesZ = -1472 := ramanujanTau_four
  have hcast : ∀ n, qExpansionCoeff S24_DeltaSq n =
      ((PowerSeries.coeff n S24_DeltaSqSeriesZ : ℤ) : ℂ) := fun n => by
    rw [qExpansionCoeff, ← S24_DeltaSqSeriesZ_map_eq, PowerSeries.coeff_map]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcast]; unfold S24_DeltaSqSeriesZ; rw [coeff_mul_Z_0, t0]; simp
  · rw [hcast]; unfold S24_DeltaSqSeriesZ; rw [coeff_mul_Z_1, t0, t1]; norm_num
  · rw [hcast]; unfold S24_DeltaSqSeriesZ; rw [coeff_mul_Z_2, t0, t1, t2]; norm_num
  · rw [hcast]; unfold S24_DeltaSqSeriesZ; rw [coeff_mul_Z_3, t0, t1, t2, t3]; norm_num
  · rw [hcast]; unfold S24_DeltaSqSeriesZ; rw [coeff_mul_Z_4, t0, t1, t2, t3, t4]; norm_num

theorem S24_vm1_coeffs :
    qExpansionCoeff S24_vm1 1 = 1 ∧
    qExpansionCoeff S24_vm1 2 = 0 ∧
    qExpansionCoeff S24_vm1 3 = 195660 ∧
    qExpansionCoeff S24_vm1 4 = 12080128 := by
  have ⟨_, a1, a2, a3, a4⟩ := S24_E4CubeDelta_coeffs
  have ⟨_, b1, b2, b3, b4⟩ := S24_DeltaSq_coeffs
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [S24_vm1, qExpansionCoeff_sub, qExpansionCoeff_smul, a1, a2, a3, a4, b1, b2, b3, b4] <;>
    norm_num

/-- **Exact Victor Miller Decomposition of `S₂₄(SL₂(ℤ))`**:
every `f ∈ S₂₄(SL₂(ℤ))` equals `a₁(f) • S24_vm1 + a₂(f) • S24_vm2`! -/
theorem S24_eq_vm_linear_comb (f : CuspForm SL2ZRange 24) :
    f = qExpansionCoeff f 1 • S24_vm1 + qExpansionCoeff f 2 • S24_vm2 := by
  have hdim : Module.finrank ℂ (CuspForm SL2ZRange 24) = 2 :=
    finrank_cuspForm_SL2Z_small.2.2.2
  let v : Fin 2 → CuspForm SL2ZRange 24 := ![S24_vm1, S24_vm2]
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 := congrArg (fun u : CuspForm SL2ZRange 24 => qExpansionCoeff u 1) hc
    have h2 := congrArg (fun u : CuspForm SL2ZRange 24 => qExpansionCoeff u 2) hc
    have hz : ∀ m, qExpansionCoeff (0 : CuspForm SL2ZRange 24) m = 0 := fun m => by
      have h0 : (0 : CuspForm SL2ZRange 24) = (0 : ℂ) • S24_vm1 := by simp
      rw [h0, qExpansionCoeff_smul, zero_mul]
    simp only [Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.1, S24_vm1_coeffs.2.1,
      S24_vm2, S24_DeltaSq_coeffs.2.1, S24_DeltaSq_coeffs.2.2.1, hz] at h1 h2
    intro i; fin_cases i
    · simpa using h1
    · simpa using h2
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin, hdim])
  let b : Module.Basis (Fin 2) ℂ (CuspForm SL2ZRange 24) := Module.Basis.mk hli (by rw [hspan])
  have hf_sum : f = b.repr f 0 • S24_vm1 + b.repr f 1 • S24_vm2 := by
    have h := (b.sum_repr f).symm
    simpa [Fin.sum_univ_two, b, v] using h
  have hc1 : qExpansionCoeff f 1 = b.repr f 0 := by
    conv_lhs => rw [hf_sum]
    simp [qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.1, S24_vm2, S24_DeltaSq_coeffs.2.1]
  have hc2 : qExpansionCoeff f 2 = b.repr f 1 := by
    conv_lhs => rw [hf_sum]
    simp [qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.2.1, S24_vm2, S24_DeltaSq_coeffs.2.2.1]
  rw [hc1, hc2]
  exact hf_sum

private lemma heckeCuspForm_24_T2_coeff1 (f : CuspForm SL2ZRange 24) :
    qExpansionCoeff (heckeCuspForm 24 (by norm_num) 2 (by norm_num) f) 1 = qExpansionCoeff f 2 := by
  rw [qExpansionCoeff, heckeCuspForm_qExpansion_coeff, heckeOp_apply_one 24 (1 : DirichletCharacter ℂ 1) (by norm_num)]
  rfl

private lemma heckeCuspForm_24_T2_coeff2 (f : CuspForm SL2ZRange 24) :
    qExpansionCoeff (heckeCuspForm 24 (by norm_num) 2 (by norm_num) f) 2 =
      qExpansionCoeff f 4 + (8388608 : ℂ) * qExpansionCoeff f 1 := by
  rw [qExpansionCoeff, heckeCuspForm_qExpansion_coeff, heckeOp_apply]
  have hgcd : Nat.gcd 2 2 = 2 := by decide
  have hdiv : (2 : ℕ).divisors = {1, 2} := by decide
  rw [hgcd, hdiv, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
  have h1 : (1 : DirichletCharacter ℂ 1) (1 : ZMod 1) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime 1 1).mpr (by decide))
  have h2 : (1 : DirichletCharacter ℂ 1) (2 : ZMod 1) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime 2 1).mpr (by decide))
  simp only [Nat.cast_one, h1, Nat.cast_ofNat, h2, one_mul, one_pow, mul_one]
  change PowerSeries.coeff (2 * 2 / 1 ^ 2) _ + (2 : ℂ) ^ 23 * PowerSeries.coeff (2 * 2 / 2 ^ 2) _ = _
  norm_num [qExpansionCoeff]

/-- **EXACT `2 × 2` ACTION OF `T₂` ON THE VICTOR MILLER BASIS `{S24_vm1, S24_vm2}` OF `S₂₄(SL₂(ℤ))`**:
- `T₂ (S24_vm1) = 20468736 • S24_vm2`
- `T₂ (S24_vm2) = S24_vm1 + 1080 • S24_vm2` -/
theorem S24_T2_on_vm :
    heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm1 = (20468736 : ℂ) • S24_vm2 ∧
    heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm2 = S24_vm1 + (1080 : ℂ) • S24_vm2 := by
  constructor
  · rw [S24_eq_vm_linear_comb (heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm1),
      heckeCuspForm_24_T2_coeff1, heckeCuspForm_24_T2_coeff2,
      S24_vm1_coeffs.1, S24_vm1_coeffs.2.1, S24_vm1_coeffs.2.2.2]
    norm_num
  · rw [S24_eq_vm_linear_comb (heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm2),
      heckeCuspForm_24_T2_coeff1, heckeCuspForm_24_T2_coeff2,
      S24_vm2, S24_DeltaSq_coeffs.2.1, S24_DeltaSq_coeffs.2.2.1, S24_DeltaSq_coeffs.2.2.2.2]
    norm_num

/-- **EXACT `2 × 2` ACTION OF `T₂` ON THE MONOMIAL BASIS `{E₄³ Δ, Δ²}` OF `S₂₄(SL₂(ℤ))`**:
- `T₂ (E₄³ Δ) = 696 • (E₄³ Δ) + 20736000 • Δ²`
- `T₂ (Δ²) = (E₄³ Δ) + 384 • Δ²` -/
theorem S24_T2_on_monomialBasis :
    heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_E4CubeDelta =
      (696 : ℂ) • S24_E4CubeDelta + (20736000 : ℂ) • S24_DeltaSq ∧
    heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_DeltaSq =
      S24_E4CubeDelta + (384 : ℂ) • S24_DeltaSq := by
  have h1 := S24_T2_on_vm.1
  have h2 := S24_T2_on_vm.2
  have hE4_eq : S24_E4CubeDelta = S24_vm1 + (696 : ℂ) • S24_vm2 := by
    simp [S24_vm1, S24_vm2]
  constructor
  · rw [hE4_eq, heckeCuspForm_add, heckeCuspForm_smul, h1, h2]
    ext τ
    simp only [S24_vm2, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  · change heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm2 = _
    rw [h2, hE4_eq]
    ext τ
    simp only [S24_vm2, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring

/-- The exact `2 × 2` matrix of `T₂` on `S₂₄(SL₂(ℤ))` in the Victor Miller basis `{S24_vm1, S24_vm2}`:
`[[0, 1], [20468736, 1080]]`. -/
def S24_T2_matrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), 1; 20468736, 1080]

theorem S24_T2_matrix_trace_det :
    Matrix.trace S24_T2_matrix = 1080 ∧ Matrix.det S24_T2_matrix = -20468736 := by
  constructor
  · simp [S24_T2_matrix, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · rw [Matrix.det_fin_two]; norm_num [S24_T2_matrix]

/-- **HECKE'S WEIGHT-24 CHARACTERISTIC POLYNOMIAL (`X² - 1080 X - 20468736 = 0`)**:
`(T₂)² - 1080 · T₂ - 20468736 · id = 0` on ALL of `S₂₄(SL₂(ℤ))`! -/
theorem S24_T2_charpoly (f : CuspForm SL2ZRange 24) :
    heckeCuspForm 24 (by norm_num) 2 (by norm_num)
        (heckeCuspForm 24 (by norm_num) 2 (by norm_num) f) -
      (1080 : ℂ) • heckeCuspForm 24 (by norm_num) 2 (by norm_num) f -
      (20468736 : ℂ) • f = 0 := by
  let a : ℂ := qExpansionCoeff f 1
  let b : ℂ := qExpansionCoeff f 2
  have hf : f = a • S24_vm1 + b • S24_vm2 := S24_eq_vm_linear_comb f
  have h1 := S24_T2_on_vm.1
  have h2 := S24_T2_on_vm.2
  have hT2f : heckeCuspForm 24 (by norm_num) 2 (by norm_num) f =
      b • S24_vm1 + (20468736 * a + 1080 * b) • S24_vm2 := by
    rw [hf, heckeCuspForm_add, heckeCuspForm_smul, heckeCuspForm_smul, h1, h2]
    ext τ
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hT2f2 : heckeCuspForm 24 (by norm_num) 2 (by norm_num)
      (heckeCuspForm 24 (by norm_num) 2 (by norm_num) f) =
      (20468736 * a + 1080 * b) • S24_vm1 +
        (20468736 * b + 1080 * (20468736 * a + 1080 * b)) • S24_vm2 := by
    rw [hT2f, heckeCuspForm_add, heckeCuspForm_smul, heckeCuspForm_smul, h1, h2]
    ext τ
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  rw [hT2f2, hT2f, hf]
  ext τ
  simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
    _root_.zero_apply]
  ring

/-- **Hecke's Famous Weight-24 Real Eigenvalues `λ₊, λ₋ = 540 ± 12 √144169 ∈ ℚ(√144169)`**. -/
def S24_lambdaPlusR : ℝ := 540 + 12 * Real.sqrt 144169
def S24_lambdaMinusR : ℝ := 540 - 12 * Real.sqrt 144169
def S24_lambdaPlus : ℂ := (S24_lambdaPlusR : ℂ)
def S24_lambdaMinus : ℂ := (S24_lambdaMinusR : ℂ)

theorem S24_lambdaPlus_root :
    S24_lambdaPlus ^ 2 - 1080 * S24_lambdaPlus - 20468736 = 0 := by
  have hsq : Real.sqrt 144169 ^ 2 = 144169 := Real.sq_sqrt (by norm_num)
  have hR : S24_lambdaPlusR ^ 2 - 1080 * S24_lambdaPlusR - 20468736 = 0 := by
    unfold S24_lambdaPlusR
    nlinarith [hsq]
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
  simpa [S24_lambdaPlus] using hC

theorem S24_lambdaMinus_root :
    S24_lambdaMinus ^ 2 - 1080 * S24_lambdaMinus - 20468736 = 0 := by
  have hsq : Real.sqrt 144169 ^ 2 = 144169 := Real.sq_sqrt (by norm_num)
  have hR : S24_lambdaMinusR ^ 2 - 1080 * S24_lambdaMinusR - 20468736 = 0 := by
    unfold S24_lambdaMinusR
    nlinarith [hsq]
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hR
  simpa [S24_lambdaMinus] using hC

theorem S24_lambdaPlus_ne_lambdaMinus : S24_lambdaPlus ≠ S24_lambdaMinus := by
  intro h
  have hR : S24_lambdaPlusR = S24_lambdaMinusR := Complex.ofReal_injective h
  unfold S24_lambdaPlusR S24_lambdaMinusR at hR
  have hsqrt_pos : 0 < Real.sqrt 144169 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- **UNCONDITIONAL IRRATIONALITY OF `√144169`** (proving Hecke's weight-24 eigenvalues
`540 ± 12 √144169` generate the real quadratic field `ℚ(√144169) ⊋ ℚ`!). -/
theorem sqrt_144169_not_rat : ∀ q : ℚ, (q : ℝ) ≠ Real.sqrt 144169 := by
  intro q hq
  have hsqR : ((q : ℝ)) ^ 2 = 144169 := by
    rw [hq, Real.sq_sqrt (by norm_num)]
  have hsqQ : q ^ 2 = 144169 := by exact_mod_cast hsqR
  have hnum_eq : q.num ^ 2 = 144169 * (q.den : ℤ) ^ 2 := by
    have h1 : (q.num : ℚ) = q * (q.den : ℚ) := (Rat.mul_den_eq_num q).symm
    have h2 : ((q.num : ℚ)) ^ 2 = 144169 * ((q.den : ℚ)) ^ 2 := by
      rw [h1, mul_pow, hsqQ]
    exact_mod_cast h2
  have hnat : q.num.natAbs ^ 2 = 144169 * q.den ^ 2 := by
    have h1 : ((q.num.natAbs ^ 2 : ℕ) : ℤ) = ((144169 * q.den ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact hnum_eq
    exact_mod_cast h1
  have hdvd_sq : q.den ^ 2 ∣ q.num.natAbs ^ 2 := ⟨144169, by linarith⟩
  have hcop : Nat.Coprime (q.num.natAbs ^ 2) (q.den ^ 2) := (q.reduced.pow_left 2).pow_right 2
  have hden_sq_1 : q.den ^ 2 = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd_sq (dvd_refl _)
  have hm_sq : q.num.natAbs ^ 2 = 144169 := by rw [hden_sq_1, mul_one] at hnat; exact hnat
  set m : ℕ := q.num.natAbs
  by_cases hm : m ≤ 379
  · have : m ^ 2 ≤ 379 ^ 2 := Nat.pow_le_pow_left hm 2
    omega
  · have hge : 380 ≤ m := by omega
    have : 380 ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hge 2
    omega

theorem S24_lambdaPlus_not_rat : ∀ q : ℚ, (q : ℝ) ≠ S24_lambdaPlusR := by
  intro q hq
  apply sqrt_144169_not_rat ((q - 540) / 12)
  push_cast
  unfold S24_lambdaPlusR at hq
  linarith

/-- **EXPLICIT NORMALIZED SIMULTANEOUS HECKE EIGENFORMS OF WEIGHT 24 (`S₂₄(SL₂(ℤ))`)**:
- `S24_eigenPlus  := S24_vm1 + (540 + 12 √144169) • S24_vm2`
- `S24_eigenMinus := S24_vm1 + (540 - 12 √144169) • S24_vm2` -/
def S24_eigenPlus : CuspForm SL2ZRange 24 :=
  S24_vm1 + S24_lambdaPlus • S24_vm2

def S24_eigenMinus : CuspForm SL2ZRange 24 :=
  S24_vm1 + S24_lambdaMinus • S24_vm2

theorem S24_eigenPlus_normalized : qExpansionCoeff S24_eigenPlus 1 = 1 := by
  simp [S24_eigenPlus, qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.1,
    S24_vm2, S24_DeltaSq_coeffs.2.1]

theorem S24_eigenMinus_normalized : qExpansionCoeff S24_eigenMinus 1 = 1 := by
  simp [S24_eigenMinus, qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.1,
    S24_vm2, S24_DeltaSq_coeffs.2.1]

theorem S24_eigenPlus_T2 :
    heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_eigenPlus =
      S24_lambdaPlus • S24_eigenPlus := by
  unfold S24_eigenPlus
  rw [heckeCuspForm_add, heckeCuspForm_smul, S24_T2_on_vm.1, S24_T2_on_vm.2]
  have hroot : 20468736 + S24_lambdaPlus * 1080 = S24_lambdaPlus * S24_lambdaPlus := by
    linear_combination -S24_lambdaPlus_root
  ext τ
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  linear_combination hroot * S24_vm2 τ

theorem S24_eigenMinus_T2 :
    heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_eigenMinus =
      S24_lambdaMinus • S24_eigenMinus := by
  unfold S24_eigenMinus
  rw [heckeCuspForm_add, heckeCuspForm_smul, S24_T2_on_vm.1, S24_T2_on_vm.2]
  have hroot : 20468736 + S24_lambdaMinus * 1080 = S24_lambdaMinus * S24_lambdaMinus := by
    linear_combination -S24_lambdaMinus_root
  ext τ
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  linear_combination hroot * S24_vm2 τ

/-- Every `f ∈ S₂₄(SL₂(ℤ))` decomposes uniquely in the eigenbasis `{S24_eigenPlus, S24_eigenMinus}`. -/
theorem S24_eq_eigen_linear_comb (f : CuspForm SL2ZRange 24) :
    ∃ c₁ c₂ : ℂ, f = c₁ • S24_eigenPlus + c₂ • S24_eigenMinus := by
  have hne : S24_lambdaPlus - S24_lambdaMinus ≠ 0 :=
    sub_ne_zero.mpr S24_lambdaPlus_ne_lambdaMinus
  let a := qExpansionCoeff f 1
  let b := qExpansionCoeff f 2
  refine ⟨(b - S24_lambdaMinus * a) / (S24_lambdaPlus - S24_lambdaMinus),
    (S24_lambdaPlus * a - b) / (S24_lambdaPlus - S24_lambdaMinus), ?_⟩
  conv_lhs => rw [S24_eq_vm_linear_comb f]
  unfold S24_eigenPlus S24_eigenMinus
  ext τ
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, a, b]
  field_simp [hne]
  ring

/-- **EXPLICIT SIMULTANEOUS HECKE EIGENBASIS OF `S₂₄(SL₂(ℤ))` (`0` Assumptions!)**:
1. `{S24_eigenPlus, S24_eigenMinus}` is a `ℂ`-basis of `S₂₄(SL₂(ℤ))`,
2. BOTH `S24_eigenPlus` and `S24_eigenMinus` are **normalized simultaneous Hecke eigenforms** for
   EVERY `T_n` (`n ≥ 1`):
   - `T_n (S24_eigenPlus) = a_n(S24_eigenPlus) • S24_eigenPlus`
   - `T_n (S24_eigenMinus) = a_n(S24_eigenMinus) • S24_eigenMinus`
3. **`S24_eigenPlus` and `S24_eigenMinus` are PETERSSON-ORTHOGONAL**:
   `peterssonInner S24_eigenPlus S24_eigenMinus = 0`! -/
theorem S24_hecke_eigenbasis :
    LinearIndependent ℂ ![S24_eigenPlus, S24_eigenMinus] ∧
    Submodule.span ℂ (Set.range ![S24_eigenPlus, S24_eigenMinus]) = ⊤ ∧
    (∀ (n : ℕ) (hn : 1 ≤ n),
      heckeCuspForm 24 (by norm_num) n hn S24_eigenPlus =
        qExpansionCoeff S24_eigenPlus n • S24_eigenPlus) ∧
    (∀ (n : ℕ) (hn : 1 ≤ n),
      heckeCuspForm 24 (by norm_num) n hn S24_eigenMinus =
        qExpansionCoeff S24_eigenMinus n • S24_eigenMinus) ∧
    peterssonInner S24_eigenPlus S24_eigenMinus = 0 := by
  have hne : S24_lambdaPlus ≠ S24_lambdaMinus := S24_lambdaPlus_ne_lambdaMinus
  have hli : LinearIndependent ℂ ![S24_eigenPlus, S24_eigenMinus] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 := congrArg (fun u : CuspForm SL2ZRange 24 => qExpansionCoeff u 1) hc
    have h2 := congrArg (fun u : CuspForm SL2ZRange 24 => qExpansionCoeff u 2) hc
    have hz : ∀ m, qExpansionCoeff (0 : CuspForm SL2ZRange 24) m = 0 := fun m => by
      have h0 : (0 : CuspForm SL2ZRange 24) = (0 : ℂ) • S24_vm1 := by simp
      rw [h0, qExpansionCoeff_smul, zero_mul]
    have ha2p : qExpansionCoeff S24_eigenPlus 2 = S24_lambdaPlus := by
      simp [S24_eigenPlus, qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.2.1,
        S24_vm2, S24_DeltaSq_coeffs.2.2.1]
    have ha2m : qExpansionCoeff S24_eigenMinus 2 = S24_lambdaMinus := by
      simp [S24_eigenMinus, qExpansionCoeff_add, qExpansionCoeff_smul, S24_vm1_coeffs.2.1,
        S24_vm2, S24_DeltaSq_coeffs.2.2.1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      qExpansionCoeff_add, qExpansionCoeff_smul, S24_eigenPlus_normalized,
      S24_eigenMinus_normalized, ha2p, ha2m, hz, mul_one] at h1 h2
    have hc1_eq : c 1 = -c 0 := by linear_combination h1
    rw [hc1_eq] at h2
    have hprod : c 0 * (S24_lambdaPlus - S24_lambdaMinus) = 0 := by linear_combination h2
    have hc0 : c 0 = 0 := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
    intro i; fin_cases i
    · exact hc0
    · simp [hc1_eq, hc0]
  have hspan : Submodule.span ℂ (Set.range ![S24_eigenPlus, S24_eigenMinus]) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    obtain ⟨c₁, c₂, hf⟩ := S24_eq_eigen_linear_comb f
    rw [hf]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ c₁ (Submodule.subset_span ⟨0, rfl⟩)
    · exact Submodule.smul_mem _ c₂ (Submodule.subset_span ⟨1, rfl⟩)
  have heigPlus : ∀ (n : ℕ) (hn : 1 ≤ n),
      heckeCuspForm 24 (by norm_num) n hn S24_eigenPlus =
        qExpansionCoeff S24_eigenPlus n • S24_eigenPlus := by
    intro n hn
    obtain ⟨c₁, c₂, hdecomp⟩ := S24_eq_eigen_linear_comb
      (heckeCuspForm 24 (by norm_num) n hn S24_eigenPlus)
    -- Apply `T₂` and use `T₂ T_n = T_n T₂`!
    have hT2_lhs : heckeCuspForm 24 (by norm_num) 2 (by norm_num)
        (heckeCuspForm 24 (by norm_num) n hn S24_eigenPlus) =
        S24_lambdaPlus • (c₁ • S24_eigenPlus + c₂ • S24_eigenMinus) := by
      rw [heckeCuspForm_comm 24 (by norm_num) (by norm_num) hn, S24_eigenPlus_T2,
        heckeCuspForm_smul, hdecomp]
    have hT2_rhs : heckeCuspForm 24 (by norm_num) 2 (by norm_num)
        (heckeCuspForm 24 (by norm_num) n hn S24_eigenPlus) =
        (c₁ * S24_lambdaPlus) • S24_eigenPlus + (c₂ * S24_lambdaMinus) • S24_eigenMinus := by
      rw [hdecomp, heckeCuspForm_add, heckeCuspForm_smul, heckeCuspForm_smul,
        S24_eigenPlus_T2, S24_eigenMinus_T2, smul_smul, smul_smul]
    have hzero : (0 : ℂ) • S24_eigenPlus +
        (c₂ * (S24_lambdaPlus - S24_lambdaMinus)) • S24_eigenMinus = 0 := by
      have heq := hT2_lhs.symm.trans hT2_rhs
      ext τ
      have hτ := congrArg (fun u : CuspForm SL2ZRange 24 => u τ) heq
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, _root_.zero_apply] at hτ ⊢
      linear_combination hτ
    have hcomb := (Fintype.linearIndependent_iff.mp hli)
      ![0, c₂ * (S24_lambdaPlus - S24_lambdaMinus)] (by simpa [Fin.sum_univ_two] using hzero)
    have hc2_prod : c₂ * (S24_lambdaPlus - S24_lambdaMinus) = 0 := by simpa using hcomb 1
    have hc2 : c₂ = 0 := (mul_eq_zero.mp hc2_prod).resolve_right (sub_ne_zero.mpr hne)
    rw [hc2, zero_smul, add_zero] at hdecomp
    have hc1 : c₁ = qExpansionCoeff S24_eigenPlus n := by
      have hcoeff := congrArg (fun u : CuspForm SL2ZRange 24 => qExpansionCoeff u 1) hdecomp
      rw [qExpansionCoeff, heckeCuspForm_qExpansion_coeff,
        heckeOp_apply_one 24 (1 : DirichletCharacter ℂ 1) hn,
        qExpansionCoeff_smul, S24_eigenPlus_normalized, mul_one] at hcoeff
      exact hcoeff.symm
    rw [hc1] at hdecomp
    exact hdecomp
  have heigMinus : ∀ (n : ℕ) (hn : 1 ≤ n),
      heckeCuspForm 24 (by norm_num) n hn S24_eigenMinus =
        qExpansionCoeff S24_eigenMinus n • S24_eigenMinus := by
    intro n hn
    obtain ⟨c₁, c₂, hdecomp⟩ := S24_eq_eigen_linear_comb
      (heckeCuspForm 24 (by norm_num) n hn S24_eigenMinus)
    have hT2_lhs : heckeCuspForm 24 (by norm_num) 2 (by norm_num)
        (heckeCuspForm 24 (by norm_num) n hn S24_eigenMinus) =
        S24_lambdaMinus • (c₁ • S24_eigenPlus + c₂ • S24_eigenMinus) := by
      rw [heckeCuspForm_comm 24 (by norm_num) (by norm_num) hn, S24_eigenMinus_T2,
        heckeCuspForm_smul, hdecomp]
    have hT2_rhs : heckeCuspForm 24 (by norm_num) 2 (by norm_num)
        (heckeCuspForm 24 (by norm_num) n hn S24_eigenMinus) =
        (c₁ * S24_lambdaPlus) • S24_eigenPlus + (c₂ * S24_lambdaMinus) • S24_eigenMinus := by
      rw [hdecomp, heckeCuspForm_add, heckeCuspForm_smul, heckeCuspForm_smul,
        S24_eigenPlus_T2, S24_eigenMinus_T2, smul_smul, smul_smul]
    have hzero : (c₁ * (S24_lambdaMinus - S24_lambdaPlus)) • S24_eigenPlus +
        (0 : ℂ) • S24_eigenMinus = 0 := by
      have heq := hT2_lhs.symm.trans hT2_rhs
      ext τ
      have hτ := congrArg (fun u : CuspForm SL2ZRange 24 => u τ) heq
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, _root_.zero_apply] at hτ ⊢
      linear_combination hτ
    have hcomb := (Fintype.linearIndependent_iff.mp hli)
      ![c₁ * (S24_lambdaMinus - S24_lambdaPlus), 0] (by simpa [Fin.sum_univ_two] using hzero)
    have hc1_prod : c₁ * (S24_lambdaMinus - S24_lambdaPlus) = 0 := by simpa using hcomb 0
    have hc1 : c₁ = 0 := (mul_eq_zero.mp hc1_prod).resolve_right (sub_ne_zero.mpr hne.symm)
    rw [hc1, zero_smul, zero_add] at hdecomp
    have hc2 : c₂ = qExpansionCoeff S24_eigenMinus n := by
      have hcoeff := congrArg (fun u : CuspForm SL2ZRange 24 => qExpansionCoeff u 1) hdecomp
      rw [qExpansionCoeff, heckeCuspForm_qExpansion_coeff,
        heckeOp_apply_one 24 (1 : DirichletCharacter ℂ 1) hn,
        qExpansionCoeff_smul, S24_eigenMinus_normalized, mul_one] at hcoeff
      exact hcoeff.symm
    rw [hc2] at hdecomp
    exact hdecomp
  have horth : peterssonInner S24_eigenPlus S24_eigenMinus = 0 := by
    have h1 : S24_lambdaPlus * peterssonInner S24_eigenPlus S24_eigenMinus =
        S24_lambdaMinus * peterssonInner S24_eigenPlus S24_eigenMinus := by
      calc S24_lambdaPlus * peterssonInner S24_eigenPlus S24_eigenMinus
          = peterssonInner (S24_lambdaPlus • S24_eigenPlus) S24_eigenMinus :=
              (peterssonInner_smul_left _ _ _).symm
        _ = peterssonInner (heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_eigenPlus) S24_eigenMinus := by
              rw [S24_eigenPlus_T2]
        _ = peterssonInner S24_eigenPlus (heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_eigenMinus) :=
              peterssonInner_heckeCuspForm_eq 24 (by norm_num) 2 (by norm_num) _ _
        _ = peterssonInner S24_eigenPlus (S24_lambdaMinus • S24_eigenMinus) := by
              rw [S24_eigenMinus_T2]
        _ = star S24_lambdaMinus * peterssonInner S24_eigenPlus S24_eigenMinus :=
              peterssonInner_smul_right _ _ _
        _ = S24_lambdaMinus * peterssonInner S24_eigenPlus S24_eigenMinus := by
              simp [S24_lambdaMinus]
    have hdiff : (S24_lambdaPlus - S24_lambdaMinus) * peterssonInner S24_eigenPlus S24_eigenMinus = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)
  exact ⟨hli, hspan, heigPlus, heigMinus, horth⟩

/-- Unconditional `IsNormalizedHeckeEigenform` and degree-2 Euler product for BOTH weight-24
Hecke eigenforms `S24_eigenPlus` and `S24_eigenMinus` on `Re(s) > 13`! -/
theorem isNormalizedHeckeEigenform_S24_eigenPlus :
    IsNormalizedHeckeEigenform 24 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff S24_eigenPlus) (qExpansionCoeff S24_eigenPlus) :=
  isNormalizedHeckeEigenform_of_heckeCuspForm (by norm_num) S24_eigenPlus_normalized
    S24_hecke_eigenbasis.2.2.1

theorem isNormalizedHeckeEigenform_S24_eigenMinus :
    IsNormalizedHeckeEigenform 24 (1 : DirichletCharacter ℂ 1)
      (qExpansionCoeff S24_eigenMinus) (qExpansionCoeff S24_eigenMinus) :=
  isNormalizedHeckeEigenform_of_heckeCuspForm (by norm_num) S24_eigenMinus_normalized
    S24_hecke_eigenbasis.2.2.2.1

theorem S24_eigenPlus_LSeries_eulerProduct {s : ℂ} (hs : 13 < s.re) :
    LSeries (qExpansionCoeff S24_eigenPlus) s =
      ∏' p : Nat.Primes,
        (1 - qExpansionCoeff S24_eigenPlus p.1 * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (23 - 2 * s))⁻¹ := by
  have h := cuspForm_eigenform_LSeries_eulerProduct S24_eigenPlus
    isNormalizedHeckeEigenform_S24_eigenPlus (by norm_num; linarith)
  rw [h]
  refine tprod_congr fun p => by norm_num

theorem S24_eigenMinus_LSeries_eulerProduct {s : ℂ} (hs : 13 < s.re) :
    LSeries (qExpansionCoeff S24_eigenMinus) s =
      ∏' p : Nat.Primes,
        (1 - qExpansionCoeff S24_eigenMinus p.1 * (p.1 : ℂ) ^ (-s) + (p.1 : ℂ) ^ (23 - 2 * s))⁻¹ := by
  have h := cuspForm_eigenform_LSeries_eulerProduct S24_eigenMinus
    isNormalizedHeckeEigenform_S24_eigenMinus (by norm_num; linarith)
  rw [h]
  refine tprod_congr fun p => by norm_num

end Weight24HeckeDiagonalization

end

end RHDirect.Stage10PeterssonHecke
