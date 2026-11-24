import RHDirect.HermitianCurvatureCore
import RHDirect.Stage8ModularRing
import RHDirect.Stage9DeltaHadamard
import RHDirect.Stage10PeterssonHecke
import RHDirect.Stage10EisensteinSpectral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# RHDirect.Stage11HermitianCurvature

**UNCONDITIONAL CONCRETE HYPERBOLIC POINCARÉ METRIC CURVATURE `K = -1`, EXACT GAUSS–BONNET
VOLUME `vol(SL₂(ℤ) \ ℍ) = π / 3`, AUTOMORPHIC LINE-BUNDLE FIRST CHERN FORM & DEGREE
`deg(ω^{⊗ k}) = k / 12`, AND CONCRETE BOCHNER–KODAIRA–NAKANO VANISHING FOR NEGATIVE WEIGHT
(`k < 0`) ON `UpperHalfPlane`** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s,
`0` assumptions).

## Main Results

1. **Exact Hyperbolic Volume `vol(SL₂(ℤ) \ ℍ) = π / 3`**:
   - `hyperbolicVolume_stdFD_eq_pi_div_three`:
     `∫ p in Stage10PeterssonHecke.stdFD, (p.2) ^ (-2 : ℝ) = Real.pi / 3`.
   - `inv_hyperbolicVolume_stdFD_eq` & `realEisensteinExt_residue_one_eq_inv_hyperbolicVolume`:
     exact match `(vol(SL₂(ℤ) \ ℍ))⁻¹ = 3 / π = Res_{s=1} E(τ, s)` with
     `Stage10EisensteinSpectral.realEisensteinExt_residue_one`.
2. **Concrete Poincaré Kähler Metric (`K = -1`), Gauss–Bonnet Orbifold Euler Characteristic,
   & Automorphic Line Bundle `ω^{⊗ k}` First Chern Form & Degree (`deg(ω^{⊗ k}) = k / 12`)**:
   - `poincare_gaussian_curvature_eq_neg_one`:
     for `ds² = λ(x, y) (dx² + dy²)` with `λ = y⁻²`,
     `K := -(1 / (2 λ)) Δ_Eucl (log λ) = -1` identically on `UpperHalfPlane`.
   - `gauss_bonnet_sl2Z_orbifold`:
     `(1 / (2 π)) ∫_{stdFD} K · y⁻² dx dy = -1 / 6 = χ_orb(SL₂(ℤ) \ ℍ)`.
   - `chernCurvature_weight_k_eq`:
     `Θ(h_k) := -(1/4) Δ_Eucl (log h_k) = (k / 4) * y⁻²` for `h_k(τ) = τ.im ^ k`.
   - `firstChernDensity_weight_k_eq` & `firstChernIntegral_weight_k_eq`:
     `c₁(ω^{⊗ k}, h_k) = (k / (4 π)) y⁻² dx dy` integrates over `stdFD` to `k / 12`;
     at `k = 12`, `deg(ω^{⊗ 12}) = 1 = dim S₁₂(SL₂(ℤ))` (`firstChernDegree_12_matches_finrank_S12`).
3. **Direct Wiring to `RHDirect.HermitianCurvatureCore`**:
   - `leviForm_uhpLift1D`: exact bridge `leviForm (uhpLift1D φ) τ w = (Δ_Eucl φ τ / 4) * ‖w ()‖²`.
   - `isPlurisubharmonicOn_hodgePotential` & `isPlurisubharmonicOn_automorphicPotential`:
     ampleness / plurisubharmonicity of `φ_ω(τ) = -log(Im τ)` on `ℍ`.
   - `ptNormSq_hodgePotential_eq_automorphicNormSq` & `chernWeilChange_stdFD_bounds`.
4. **Concrete Bochner–Weitzenböck Positivity & Negative-Weight Vanishing (`k < 0`)**:
   - `bochner_log_laplacian_weight_k`:
     `Δ_Eucl (log (|f|² y^k)) = -k / y²` away from zeros of holomorphic `f`.
   - `bochner_identity_weight_k`:
     `Δ_Eucl (|f|² y^k) = 4 y^k |f' + (k / (2 i y)) f|² - k y^{k - 2} |f|²`.
   - `bochner_vanishing_of_isLocalMax`, `bochner_vanishing_sl2Z_of_weight_neg`,
     `modularForm_eq_zero_of_weight_neg`, and `cuspForm_eq_zero_of_weight_neg`.
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function
open RHDirect.HermitianCurvatureCore RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular
open RHDirect.Stage6HeckeSpectral RHDirect.Stage7EisensteinSeries RHDirect.Stage8ModularRing
open RHDirect.Stage9DeltaHadamard RHDirect.Stage10PeterssonHecke RHDirect.Stage10EisensteinSpectral
open scoped BigOperators UpperHalfPlane ModularForm Topology ENNReal Manifold ComplexConjugate
  MatrixGroups

namespace RHDirect.Stage11HermitianCurvature

noncomputable section

/-! ## Section 1: Exact Hyperbolic Volume `vol(SL₂(ℤ) \ ℍ) = π / 3` -/

section HyperbolicVolume

/-- Concrete hyperbolic area / volume of a measurable region `S ⊆ ℝ × ℝ` with respect to the
Poincaré area form `y⁻² dx dy`. -/
def hyperbolicVolume (S : Set (ℝ × ℝ)) : ℝ :=
  ∫ p in S, (p.2) ^ (-2 : ℝ)

/-- Exact 1D improper integral `∫_a^∞ y⁻² dy = a⁻¹` for every `a > 0`. -/
private lemma integral_Ioi_rpow_neg_two {a : ℝ} (ha : 0 < a) :
    ∫ y in Set.Ioi a, y ^ (-2 : ℝ) = a⁻¹ := by
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) ha]
  have h1 : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [h1, Real.rpow_neg_one]
  ring

/-- Exact elementary integral `∫_{-1/2}^{1/2} (√(1 - x²))⁻¹ dx = π / 3`. -/
private lemma integral_inv_sqrt_one_sub_sq_half :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), (Real.sqrt (1 - x ^ 2))⁻¹ = Real.pi / 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
      HasDerivAt Real.arcsin ((Real.sqrt (1 - x ^ 2))⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)] at hx
    have h1 : x ≠ -1 := by linarith [hx.1]
    have h2 : x ≠ 1 := by linarith [hx.2]
    simpa [one_div] using Real.hasDerivAt_arcsin h1 h2
  have hint : IntervalIntegrable (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹) volume
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
    refine ContinuousOn.inv₀
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).continuousOn ?_
    intro x hx
    have hpos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    exact (Real.sqrt_pos.mpr hpos).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have harcsin_half : Real.arcsin (1 / 2 : ℝ) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six]
    exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  rw [Real.arcsin_neg, harcsin_half]
  ring

/-- The hyperbolic area density `(x, y) ↦ y⁻²` is Lebesgue-integrable on the standard
`SL₂(ℤ)` fundamental domain `stdFD`. -/
theorem integrableOn_hyperbolicMeasure_stdFD :
    IntegrableOn (fun p : ℝ × ℝ => (p.2) ^ (-2 : ℝ)) stdFD volume := by
  let S : Set (ℝ × ℝ) := Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ˢ Set.Ioi (1 / 2 : ℝ)
  have hsub : stdFD ⊆ S := by
    intro p hp
    refine ⟨?_, stdFD_im_gt_half hp⟩
    have habs := abs_le.mp hp.1
    exact ⟨by linarith [habs.1], habs.2⟩
  have hx : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)) volume :=
    integrableOn_const (by simp [Real.volume_Icc])
  have hy : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Set.Ioi (1 / 2 : ℝ)) volume :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1 / 2)
  have hprod : IntegrableOn (fun p : ℝ × ℝ => (1 : ℝ) * (p.2) ^ (-2 : ℝ)) S volume := by
    have h := Integrable.mul_prod hx hy
    simpa [IntegrableOn, Measure.volume_eq_prod, Measure.prod_restrict, S] using h
  have hprod' : IntegrableOn (fun p : ℝ × ℝ => (p.2) ^ (-2 : ℝ)) S volume := by
    simpa only [one_mul] using hprod
  exact hprod'.mono_set hsub

/-- **Exact Hyperbolic Volume of the Modular Curve `SL₂(ℤ) \ ℍ`**:
$$\operatorname{vol}(\mathrm{SL}_2(\mathbb{Z}) \backslash \mathbb{H})
  = \iint_{\mathcal{D}} \frac{dx\,dy}{y^2} = \frac{\pi}{3}.$$ -/
theorem hyperbolicVolume_stdFD_eq_pi_div_three :
    ∫ p in Stage10PeterssonHecke.stdFD, (p.2) ^ (-2 : ℝ) = Real.pi / 3 := by
  let g : ℝ × ℝ → ℝ := stdFD.indicator (fun p : ℝ × ℝ => (p.2) ^ (-2 : ℝ))
  have hg_int : Integrable g volume :=
    (integrable_indicator_iff measurableSet_stdFD).mpr integrableOn_hyperbolicMeasure_stdFD
  have hstep1 : ∫ p in stdFD, (p.2) ^ (-2 : ℝ) = ∫ p, g p :=
    (MeasureTheory.integral_indicator measurableSet_stdFD).symm
  have hstep2 : ∫ p, g p = ∫ x : ℝ, ∫ y : ℝ, g (x, y) := by
    rw [Measure.volume_eq_prod]
    exact MeasureTheory.integral_prod g (by simpa [Measure.volume_eq_prod] using hg_int)
  have hinner : ∀ x : ℝ, ∫ y : ℝ, g (x, y) =
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)).indicator (fun t => (Real.sqrt (1 - t ^ 2))⁻¹) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
    · rw [Set.indicator_of_mem hx]
      have hx_abs : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have h1mx2_pos : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      have ha_pos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr h1mx2_pos
      have hslice : (fun y : ℝ => g (x, y)) =
          (Set.Ici (Real.sqrt (1 - x ^ 2))).indicator (fun y : ℝ => y ^ (-2 : ℝ)) := by
        funext y
        by_cases hy : Real.sqrt (1 - x ^ 2) ≤ y
        · have hmem : (x, y) ∈ stdFD := by
            refine ⟨hx_abs, lt_of_lt_of_le ha_pos hy, ?_⟩
            have hsq : 1 - x ^ 2 ≤ y ^ 2 := by
              have h1 := pow_le_pow_left₀ ha_pos.le hy 2
              rw [Real.sq_sqrt h1mx2_pos.le] at h1
              exact h1
            linarith
          simp only [g, Set.indicator_of_mem hmem, Set.indicator_of_mem (show y ∈ Set.Ici _ from hy)]
        · have hnot : (x, y) ∉ stdFD := by
            intro hmem
            apply hy
            have hsq : 1 - x ^ 2 ≤ y ^ 2 := by linarith [hmem.2.2]
            have h1 := Real.sqrt_le_sqrt hsq
            rwa [Real.sqrt_sq hmem.2.1.le] at h1
          simp only [g, Set.indicator_of_notMem hnot,
            Set.indicator_of_notMem (show y ∉ Set.Ici _ from hy)]
      rw [hslice, MeasureTheory.integral_indicator measurableSet_Ici,
        MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_neg_two ha_pos]
    · rw [Set.indicator_of_notMem hx]
      have hzero : ∀ y : ℝ, g (x, y) = 0 := by
        intro y
        have hnot : (x, y) ∉ stdFD := by
          intro hmem
          apply hx
          have habs := abs_le.mp hmem.1
          exact ⟨by linarith [habs.1], habs.2⟩
        exact Set.indicator_of_notMem hnot _
      simp [hzero]
  rw [hstep1, hstep2]
  simp_rw [hinner]
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2),
    integral_inv_sqrt_one_sub_sq_half]

/-- Named-wrapper form: `hyperbolicVolume stdFD = π / 3`. -/
theorem hyperbolicVolume_stdFD :
    hyperbolicVolume Stage10PeterssonHecke.stdFD = Real.pi / 3 :=
  hyperbolicVolume_stdFD_eq_pi_div_three

/-- Inverse hyperbolic volume `(vol(SL₂(ℤ) \ ℍ))⁻¹ = 3 / π`. -/
theorem inv_hyperbolicVolume_stdFD_eq :
    (hyperbolicVolume Stage10PeterssonHecke.stdFD)⁻¹ = 3 / Real.pi := by
  rw [hyperbolicVolume_stdFD, inv_div]

/-- **Exact Matching with the Eisenstein Residue at `s = 1`**:
the simple pole residue of `E(τ, s)` at `s = 1` proved in `Stage10EisensteinSpectral`
equals `(hyperbolicVolume stdFD)⁻¹ = 3 / π`. -/
theorem realEisensteinExt_residue_one_eq_inv_hyperbolicVolume (τ : UpperHalfPlane) :
    Tendsto (fun s : ℂ => (s - 1) * (completedEisenstein τ s / completedRiemannZeta (2 * s)))
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds ((hyperbolicVolume Stage10PeterssonHecke.stdFD : ℂ)⁻¹)) := by
  have hcast : ((hyperbolicVolume Stage10PeterssonHecke.stdFD : ℂ)⁻¹) = 3 / (Real.pi : ℂ) := by
    rw [← Complex.ofReal_inv, inv_hyperbolicVolume_stdFD_eq]
    push_cast
    rfl
  rw [hcast]
  exact realEisensteinExt_residue_one τ

end HyperbolicVolume

/-! ## Section 2: Concrete Euclidean Laplacian, Poincaré Curvature `K = -1` & Gauss–Bonnet -/

section PoincareCurvature

/-- Horizontal real slice `x ↦ φ(x + i y)` of a real-valued function on `UpperHalfPlane`. -/
def uhpSliceXR (φ : UpperHalfPlane → ℝ) (y x : ℝ) : ℝ :=
  φ (UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ)))

/-- Vertical real slice `y ↦ φ(x + i y)` of a real-valued function on `UpperHalfPlane`. -/
def uhpSliceYR (φ : UpperHalfPlane → ℝ) (x y : ℝ) : ℝ :=
  φ (UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (y : ℂ)))

/-- First partial derivative `∂φ/∂x` on `UpperHalfPlane`. -/
def partialXR (φ : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) : ℝ :=
  deriv (uhpSliceXR φ τ.im) τ.re

/-- First partial derivative `∂φ/∂y` on `UpperHalfPlane`. -/
def partialYR (φ : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) : ℝ :=
  deriv (uhpSliceYR φ τ.re) τ.im

/-- Second partial derivative `∂²φ/∂x²` on `UpperHalfPlane`. -/
def partialXXR (φ : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) : ℝ :=
  deriv (fun x : ℝ => deriv (uhpSliceXR φ τ.im) x) τ.re

/-- Second partial derivative `∂²φ/∂y²` on `UpperHalfPlane`. -/
def partialYYR (φ : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) : ℝ :=
  deriv (fun y : ℝ => deriv (uhpSliceYR φ τ.re) y) τ.im

/-- **Concrete Euclidean Laplacian on `UpperHalfPlane`**:
`Δ_Eucl φ(x + i y) = ∂²φ/∂x² + ∂²φ/∂y²`. -/
def euclLaplacianR (φ : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) : ℝ :=
  partialXXR φ τ + partialYYR φ τ

/-- Coercion `ℝ → ℂ` commutes unconditionally with `deriv`. -/
private lemma deriv_ofReal_comp (g : ℝ → ℝ) (x : ℝ) :
    deriv (fun t : ℝ => (g t : ℂ)) x = Complex.ofReal (deriv g x) := by
  by_cases hg : DifferentiableAt ℝ g x
  · have h := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hg.hasDerivAt
    exact h.deriv
  · have hnot : ¬ DifferentiableAt ℝ (fun t : ℝ => (g t : ℂ)) x := by
      intro hC
      have hre := Complex.reCLM.differentiableAt.comp x hC
      have heq : (Complex.reCLM ∘ fun t : ℝ => (g t : ℂ)) = g := by
        funext t; simp
      rw [heq] at hre
      exact hg hre
    rw [deriv_zero_of_not_differentiableAt hg, deriv_zero_of_not_differentiableAt hnot,
      Complex.ofReal_zero]

/-- Exact compatibility between `Stage10EisensteinSpectral.hypLaplacian` and `euclLaplacianR`:
`Δ_ℍ (φ : ℍ → ℂ) = -y² Δ_Eucl φ`. -/
theorem hypLaplacian_ofReal_eq (φ : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) :
    hypLaplacian (fun w => (φ w : ℂ)) τ = -((τ.im : ℂ) ^ 2) * (euclLaplacianR φ τ : ℂ) := by
  unfold hypLaplacian partialXX partialYY euclLaplacianR partialXXR partialYYR
  have hx1 : (fun x : ℝ => deriv (uhpSliceX (fun w => (φ w : ℂ)) τ.im) x) =
      fun x : ℝ => Complex.ofReal (deriv (uhpSliceXR φ τ.im) x) := by
    funext x
    exact deriv_ofReal_comp (uhpSliceXR φ τ.im) x
  have hy1 : (fun y : ℝ => deriv (uhpSliceY (fun w => (φ w : ℂ)) τ.re) y) =
      fun y : ℝ => Complex.ofReal (deriv (uhpSliceYR φ τ.re) y) := by
    funext y
    exact deriv_ofReal_comp (uhpSliceYR φ τ.re) y
  rw [hx1, hy1,
    deriv_ofReal_comp (fun x : ℝ => deriv (uhpSliceXR φ τ.im) x) τ.re,
    deriv_ofReal_comp (fun y : ℝ => deriv (uhpSliceYR φ τ.re) y) τ.im]
  push_cast
  rfl

/-- Exact Euclidean Laplacian of `τ ↦ c * log (Im τ)`:
`Δ_Eucl (c · log y) = -c · y⁻²`. -/
theorem euclLaplacianR_const_mul_log_im (c : ℝ) (τ : UpperHalfPlane) :
    euclLaplacianR (fun w => c * Real.log w.im) τ = -c * τ.im ^ (-2 : ℝ) := by
  have hy : 0 < τ.im := τ.im_pos
  have hxx : partialXXR (fun w => c * Real.log w.im) τ = 0 := by
    unfold partialXXR
    have hconst : uhpSliceXR (fun w => c * Real.log w.im) τ.im = fun _ => c * Real.log τ.im := by
      funext x
      unfold uhpSliceXR
      dsimp only
      rw [ofComplex_im_eq hy]
    rw [hconst]
    simp only [deriv_const]
  have hyy : partialYYR (fun w => c * Real.log w.im) τ = -c * τ.im ^ (-2 : ℝ) := by
    unfold partialYYR
    have hd1 : (fun y : ℝ => deriv (uhpSliceYR (fun w => c * Real.log w.im) τ.re) y) =ᶠ[𝓝 τ.im]
        fun y : ℝ => c * y⁻¹ := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with y hy0
      have hev : uhpSliceYR (fun w => c * Real.log w.im) τ.re =ᶠ[𝓝 y]
          fun u : ℝ => c * Real.log u := by
        filter_upwards [isOpen_Ioi.mem_nhds hy0] with u hu
        unfold uhpSliceYR
        dsimp only
        rw [ofComplex_im_eq hu]
      rw [hev.deriv_eq]
      exact ((Real.hasDerivAt_log hy0.ne').const_mul c).deriv
    rw [hd1.deriv_eq]
    have hd2 : HasDerivAt (fun y : ℝ => c * y⁻¹) (c * (-(τ.im ^ 2)⁻¹)) τ.im :=
      (hasDerivAt_inv hy.ne').const_mul c
    rw [hd2.deriv]
    have hrpow : τ.im ^ (-2 : ℝ) = (τ.im ^ 2)⁻¹ := by
      rw [Real.rpow_neg hy.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hrpow]
    ring
  unfold euclLaplacianR
  rw [hxx, hyy, zero_add]

/-- Conformal factor `λ(x, y) = y⁻²` of the Poincaré metric `ds² = (dx² + dy²) / y²` on `ℍ`. -/
def poincareMetricFactor (τ : UpperHalfPlane) : ℝ :=
  τ.im ^ (-2 : ℝ)

/-- Concrete Gaussian curvature of a conformal Riemannian metric `ds² = λ(x, y) (dx² + dy²)`
on `UpperHalfPlane`:
$$K_\lambda(\tau) = -\frac{1}{2 \lambda(\tau)} \Delta_{\mathrm{Eucl}} (\log \lambda)(\tau).$$ -/
def conformalGaussianCurvature (lam : UpperHalfPlane → ℝ) (τ : UpperHalfPlane) : ℝ :=
  -(1 / (2 * lam τ)) * euclLaplacianR (fun w => Real.log (lam w)) τ

/-- **Constant Negative Poincaré Gaussian Curvature (`K = -1`)**:
for `ds² = y⁻² (dx² + dy²)`, `K(τ) = -1` identically for every `τ ∈ ℍ`. -/
theorem poincare_gaussian_curvature_eq_neg_one (τ : UpperHalfPlane) :
    conformalGaussianCurvature poincareMetricFactor τ = -1 := by
  unfold conformalGaussianCurvature poincareMetricFactor
  have hlog : (fun w : UpperHalfPlane => Real.log (w.im ^ (-2 : ℝ))) =
      fun w : UpperHalfPlane => (-2 : ℝ) * Real.log w.im := by
    funext w
    rw [Real.log_rpow w.im_pos]
  rw [hlog, euclLaplacianR_const_mul_log_im (-2) τ]
  have hpos : (0 : ℝ) < τ.im ^ (-2 : ℝ) := Real.rpow_pos_of_pos τ.im_pos _
  field_simp [hpos.ne']

/-- **Gauss–Bonnet Orbifold Euler Characteristic of `SL₂(ℤ) \ ℍ`**:
$$\frac{1}{2\pi} \iint_{\mathcal{D}} K_{\mathrm{Poinc}} \, \frac{dx\,dy}{y^2}
  = -\frac{1}{6} = \chi_{\mathrm{orb}}(\mathrm{SL}_2(\mathbb{Z}) \backslash \mathbb{H}).$$ -/
theorem gauss_bonnet_sl2Z_orbifold :
    ∫ p in Stage10PeterssonHecke.stdFD,
      (if hp : 0 < p.2 then conformalGaussianCurvature poincareMetricFactor (pairToUHP p hp)
        else 0) * (p.2) ^ (-2 : ℝ) / (2 * Real.pi) = -(1 / 6 : ℝ) := by
  have hcongr : Set.EqOn
      (fun p : ℝ × ℝ =>
        (if hp : 0 < p.2 then conformalGaussianCurvature poincareMetricFactor (pairToUHP p hp)
          else 0) * (p.2) ^ (-2 : ℝ) / (2 * Real.pi))
      (fun p : ℝ × ℝ => (-(1 / (2 * Real.pi))) * (p.2) ^ (-2 : ℝ)) stdFD := by
    intro p hp
    dsimp only
    rw [dif_pos hp.2.1, poincare_gaussian_curvature_eq_neg_one]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_stdFD hcongr,
    MeasureTheory.integral_const_mul, hyperbolicVolume_stdFD_eq_pi_div_three]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]
  ring

end PoincareCurvature

/-! ## Section 3: Automorphic Line Bundle `ω^{⊗ k}` Hermitian Metric, Chern Form & Degree `k / 12` -/

section AutomorphicChernForm

/-- Concrete Petersson / automorphic Hermitian metric `h_k(τ) = Im(τ)^k` on the weight-`k`
automorphic line bundle `ω^{⊗ k}` over `UpperHalfPlane`. -/
def automorphicMetric (k : ℤ) (τ : UpperHalfPlane) : ℝ :=
  τ.im ^ k

/-- Pointwise Hermitian norm squared `‖f(τ)‖²_{h_k} = ‖f(τ)‖² · Im(τ)^k` of a weight-`k`
section `f` on `UpperHalfPlane`. -/
def automorphicNormSq (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℝ :=
  ‖f τ‖ ^ 2 * automorphicMetric k τ

/-- Canonical local Kähler / Hermitian potential `φ_ω(τ) = -log(Im τ)` of the Hodge line
bundle `ω` (`h_ω(τ) = Im(τ) = exp(-φ_ω(τ))`). -/
def hodgePotential (τ : UpperHalfPlane) : ℝ :=
  -Real.log τ.im

/-- `SL₂(ℤ)`-invariance of the pointwise Hermitian norm squared `‖f(τ)‖² Im(τ)^k` for every
level-1 modular form `f ∈ M_k(SL₂(ℤ))`. -/
theorem automorphicNormSq_modularForm_sl2Z_invariant {k : ℤ} (f : ModularForm SL2ZRange k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    automorphicNormSq k f (γ • τ) = automorphicNormSq k f τ := by
  unfold automorphicNormSq automorphicMetric
  have hslash := f.slash_action_eq' (sl2ZToGL2R γ) ⟨γ, rfl⟩
  have hval := congrFun hslash τ
  change SlashAction.map k (sl2ZToGL2R γ) (f : UpperHalfPlane → ℂ) τ = f τ at hval
  rw [slash_sl2Z_apply] at hval
  set d : ℂ := UpperHalfPlane.denom (sl2ZToGL2R γ) (τ : ℂ)
  have hd_ne : d ≠ 0 := UpperHalfPlane.denom_ne_zero (sl2ZToGL2R γ) τ
  have hd_pos : 0 < ‖d‖ := norm_pos_iff.mpr hd_ne
  have hnorm_f : ‖f (γ • τ)‖ = ‖d‖ ^ k * ‖f τ‖ := by
    have h1 := congrArg norm hval
    rw [norm_mul, norm_zpow] at h1
    have hmul : ‖d‖ ^ k * ‖d‖ ^ (-k) = 1 := by
      rw [← zpow_add₀ hd_pos.ne', add_neg_cancel, zpow_zero]
    calc ‖f (γ • τ)‖ = ‖d‖ ^ k * (‖f (γ • τ)‖ * ‖d‖ ^ (-k)) := by
          rw [mul_left_comm, hmul, mul_one]
      _ = ‖d‖ ^ k * ‖f τ‖ := by rw [h1]
  have him_smul : (γ • τ).im = τ.im / ‖d‖ ^ 2 := by
    have h1 : (γ • τ).im = (sl2ZToGL2R γ • τ).im := rfl
    rw [h1, UpperHalfPlane.im_smul_eq_div_normSq]
    have hdet : ((sl2ZToGL2R γ).det : ℝ) = 1 := by simp [sl2ZToGL2R]
    rw [hdet, abs_one, one_mul, Complex.normSq_eq_norm_sq]
  rw [hnorm_f, him_smul, div_zpow, mul_pow]
  have hpow : (‖d‖ ^ 2) ^ k = (‖d‖ ^ k) ^ 2 := by
    rw [← zpow_natCast ‖d‖ 2, ← _root_.zpow_mul, mul_comm ((2 : ℕ) : ℤ) k, _root_.zpow_mul,
      zpow_natCast]
  rw [hpow]
  have hdk_ne : (‖d‖ ^ k) ^ 2 ≠ 0 := pow_ne_zero 2 (zpow_ne_zero k hd_pos.ne')
  field_simp [hdk_ne]

/-- `SL₂(ℤ)`-invariance of the pointwise Hermitian norm squared `‖f(τ)‖² Im(τ)^k` for every
level-1 cusp form `f ∈ S_k(SL₂(ℤ))` (wired directly to `Stage9DeltaHadamard`). -/
theorem automorphicNormSq_sl2Z_invariant {k : ℤ} (f : CuspForm SL2ZRange k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    automorphicNormSq k f (γ • τ) = automorphicNormSq k f τ := by
  have h := congrArg (fun t : ℝ => t ^ 2) (cuspForm_im_pow_norm_sl2Z_invariant f γ τ)
  have hsq : ∀ w : UpperHalfPlane, (w.im ^ ((k : ℝ) / 2) * ‖f w‖) ^ 2 =
      automorphicNormSq k f w := by
    intro w
    unfold automorphicNormSq automorphicMetric
    rw [mul_pow, ← Real.rpow_natCast (w.im ^ ((k : ℝ) / 2)) 2,
      ← Real.rpow_mul w.im_pos.le]
    have hexp : (k : ℝ) / 2 * ((2 : ℕ) : ℝ) = (k : ℝ) := by push_cast; ring
    rw [hexp, Real.rpow_intCast, mul_comm]
  rw [hsq (γ • τ), hsq τ] at h
  exact h

/-- Concrete Chern curvature `(1, 1)`-coefficient of `(ω^{⊗ k}, h_k)`:
$$\Theta(h_k) = -\partial\bar\partial \log h_k
  = -\frac{1}{4}\Delta_{\mathrm{Eucl}}(\log h_k)\,dz \wedge d\bar z.$$ -/
def chernCurvatureCoeff (k : ℤ) (τ : UpperHalfPlane) : ℝ :=
  -(1 / 4 : ℝ) * euclLaplacianR (fun w => Real.log (automorphicMetric k w)) τ

/-- **Exact Chern Curvature of the Weight-`k` Automorphic Line Bundle**:
$$\Theta(h_k)(\tau) = \frac{k}{4} y^{-2}.$$ -/
theorem chernCurvature_weight_k_eq (k : ℤ) (τ : UpperHalfPlane) :
    chernCurvatureCoeff k τ = (k : ℝ) / 4 * τ.im ^ (-2 : ℝ) := by
  unfold chernCurvatureCoeff automorphicMetric
  have hlog : (fun w : UpperHalfPlane => Real.log (w.im ^ k)) =
      fun w : UpperHalfPlane => (k : ℝ) * Real.log w.im := by
    funext w
    rw [Real.log_zpow]
  rw [hlog, euclLaplacianR_const_mul_log_im (k : ℝ) τ]
  ring

/-- Concrete First Chern Form density `c₁(ω^{⊗ k}, h_k) = (i / (2 π)) Θ(h_k)` with respect
to `dx ∧ dy` (using `i dz ∧ d z̄ = 2 dx ∧ dy`):
$$c_1(\omega^{\otimes k}, h_k) = -\frac{1}{4\pi}\Delta_{\mathrm{Eucl}}(\log h_k)\,dx \wedge dy.$$ -/
def firstChernDensity (k : ℤ) (τ : UpperHalfPlane) : ℝ :=
  -(1 / (4 * Real.pi)) * euclLaplacianR (fun w => Real.log (automorphicMetric k w)) τ

/-- Relation `c₁(ω^{⊗ k}, h_k) = (1 / π) Θ(h_k) dx ∧ dy = (k / (4 π)) y⁻² dx ∧ dy`. -/
theorem firstChernDensity_weight_k_eq (k : ℤ) (τ : UpperHalfPlane) :
    firstChernDensity k τ = (k : ℝ) / (4 * Real.pi) * τ.im ^ (-2 : ℝ) := by
  have hrel : firstChernDensity k τ = (1 / Real.pi) * chernCurvatureCoeff k τ := by
    unfold firstChernDensity chernCurvatureCoeff
    ring
  rw [hrel, chernCurvature_weight_k_eq]
  ring

/-- **Exact First Chern Degree of `ω^{⊗ k}` over `SL₂(ℤ) \ ℍ`**:
$$\deg(\omega^{\otimes k})
  = \iint_{\mathcal{D}} \frac{k}{4\pi} \frac{dx\,dy}{y^2} = \frac{k}{12}.$$ -/
theorem firstChernIntegral_weight_k_eq (k : ℤ) :
    ∫ p in Stage10PeterssonHecke.stdFD, (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ) =
      (k : ℝ) / 12 := by
  rw [MeasureTheory.integral_const_mul, hyperbolicVolume_stdFD_eq_pi_div_three]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]
  ring

/-- Integral of `firstChernDensity k` directly over `stdFD` equals `k / 12`. -/
theorem firstChernIntegral_density_eq (k : ℤ) :
    ∫ p in Stage10PeterssonHecke.stdFD,
      (if hp : 0 < p.2 then firstChernDensity k (pairToUHP p hp) else 0) = (k : ℝ) / 12 := by
  have hcongr : Set.EqOn
      (fun p : ℝ × ℝ => if hp : 0 < p.2 then firstChernDensity k (pairToUHP p hp) else 0)
      (fun p : ℝ × ℝ => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) stdFD := by
    intro p hp
    dsimp only
    rw [dif_pos hp.2.1, firstChernDensity_weight_k_eq, pairToUHP_im]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_stdFD hcongr]
  exact firstChernIntegral_weight_k_eq k

/-- **Weight-12 Iconic Degree Identity**: `deg(ω^{⊗ 12}) = 12 / 12 = 1`, matching the unique
simple zero of Ramanujan's discriminant `Δ ∈ S₁₂(SL₂(ℤ))` at `i∞`. -/
theorem firstChernIntegral_weight_12_eq_one :
    ∫ p in Stage10PeterssonHecke.stdFD, (12 : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ) = 1 := by
  have h := firstChernIntegral_weight_k_eq 12
  simp only [Int.cast_ofNat] at h
  rw [h]
  norm_num

/-- Direct match between the Chern–Weil degree `deg(ω^{⊗ 12}) = 1` and the exact cusp form
dimension `dim_ℂ S₁₂(SL₂(ℤ)) = 1` from `Stage8ModularRing`. -/
theorem firstChernDegree_12_matches_finrank_S12 :
    (∫ p in Stage10PeterssonHecke.stdFD, (12 : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) =
      (Module.finrank ℂ (CuspForm SL2ZRange 12) : ℝ) := by
  rw [firstChernIntegral_weight_12_eq_one, finrank_cuspForm_SL2Z_small.1]
  norm_num

end AutomorphicChernForm

/-! ## Section 4: Direct Wiring to `RHDirect.HermitianCurvatureCore` -/

section CoreWiring

/-- Open upper half-plane embedded as a 1-dimensional complex domain `Unit → ℂ`. -/
def uhpSet1D : Set (Unit → ℂ) :=
  { z : Unit → ℂ | 0 < (z ()).im }

/-- Lift a real function on `UpperHalfPlane` to `Unit → ℂ` via `UpperHalfPlane.ofComplex`. -/
def uhpLift1D (φ : UpperHalfPlane → ℝ) (z : Unit → ℂ) : ℝ :=
  φ (UpperHalfPlane.ofComplex (z ()))

/-- `deriv` commutes unconditionally with real translation `s ↦ g (a + s)`. -/
private lemma deriv_deriv_const_add (g : ℝ → ℝ) (a : ℝ) :
    deriv (deriv fun s : ℝ => g (a + s)) 0 = deriv (deriv g) a := by
  have h1 : (deriv fun s : ℝ => g (a + s)) = fun s : ℝ => deriv g (a + s) := by
    funext s
    exact deriv_comp_const_add g a s
  rw [h1]
  simpa using deriv_comp_const_add (deriv g) a 0

/-- **Exact Bridge to `HermitianCurvatureCore.leviForm`**:
for any `C²` real function `φ` on `UpperHalfPlane`, the complex Hessian / Levi form
of `uhpLift1D φ` at `τ` in tangent direction `w : Unit → ℂ` equals `(Δ_Eucl φ(τ) / 4) * ‖w ()‖²`. -/
theorem leviForm_uhpLift1D {φ : UpperHalfPlane → ℝ} {τ : UpperHalfPlane}
    (hφ : ContDiffAt ℝ 2 (uhpLift1D φ) (fun _ => (τ : ℂ))) (w : Unit → ℂ) :
    HermitianCurvatureCore.leviForm (uhpLift1D φ) (fun _ => (τ : ℂ)) w =
      (euclLaplacianR φ τ / 4) * ‖w ()‖ ^ 2 := by
  set z₀ : Unit → ℂ := fun _ => (τ : ℂ)
  set e₁ : Unit → ℂ := fun _ => (1 : ℂ)
  set eI : Unit → ℂ := Complex.I • e₁
  set a : ℝ := (w ()).re
  set b : ℝ := (w ()).im
  have hw_eq : w = a • e₁ + b • eI := by
    funext u
    cases u
    simp only [e₁, eI, Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul, mul_one, a, b]
    exact (Complex.re_add_im (w ())).symm
  have hIw_eq : Complex.I • w = (-b) • e₁ + a • eI := by
    funext u
    cases u
    simp only [e₁, eI, Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul, mul_one, a, b]
    have hdecomp : w () = (a : ℂ) + (b : ℂ) * Complex.I := (Complex.re_add_im (w ())).symm
    rw [hdecomp]
    push_cast
    ring_nf
    simp [Complex.I_sq]
    ring
  set B := fderiv ℝ (fderiv ℝ (uhpLift1D φ)) z₀
  have hB_add_l : ∀ x y z, B (x + y) z = B x z + B y z := fun x y z => by rw [map_add]; rfl
  have hB_smul_l : ∀ (r : ℝ) x z, B (r • x) z = r * B x z := fun r x z => by rw [map_smul]; rfl
  have hB_add_r : ∀ x y z, B x (y + z) = B x y + B x z := fun x y z => map_add (B x) y z
  have hB_smul_r : ∀ (r : ℝ) x z, B x (r • z) = r * B x z := fun r x z => by
    rw [map_smul, smul_eq_mul]
  have hB_w : B w w = a * a * B e₁ e₁ + a * b * B e₁ eI + b * a * B eI e₁ + b * b * B eI eI := by
    rw [hw_eq, hB_add_l, hB_smul_l, hB_smul_l, hB_add_r, hB_add_r,
      hB_smul_r, hB_smul_r, hB_smul_r, hB_smul_r]
    ring
  have hB_Iw : B (Complex.I • w) (Complex.I • w) =
      b * b * B e₁ e₁ - b * a * B e₁ eI - a * b * B eI e₁ + a * a * B eI eI := by
    rw [hIw_eq, hB_add_l, hB_smul_l, hB_smul_l, hB_add_r, hB_add_r,
      hB_smul_r, hB_smul_r, hB_smul_r, hB_smul_r]
    ring
  have hBe1 : B e₁ e₁ = partialXXR φ τ := by
    have hline := HermitianCurvatureCore.deriv_deriv_line hφ e₁
    rw [← hline]
    have hfun : (fun s : ℝ => uhpLift1D φ (z₀ + s • e₁)) =
        fun s : ℝ => uhpSliceXR φ τ.im (τ.re + s) := by
      funext s
      simp only [uhpLift1D, uhpSliceXR, z₀, e₁, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
        mul_one]
      congr 1
      have hreim : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := (Complex.re_add_im (τ : ℂ)).symm
      rw [hreim, Complex.ofReal_add, add_right_comm, mul_comm Complex.I]
    rw [hfun]
    exact deriv_deriv_const_add (uhpSliceXR φ τ.im) τ.re
  have hBeI : B eI eI = partialYYR φ τ := by
    have hline := HermitianCurvatureCore.deriv_deriv_line hφ eI
    rw [← hline]
    have hfun : (fun s : ℝ => uhpLift1D φ (z₀ + s • eI)) =
        fun s : ℝ => uhpSliceYR φ τ.re (τ.im + s) := by
      funext s
      simp only [uhpLift1D, uhpSliceYR, z₀, eI, e₁, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
        smul_eq_mul, mul_one]
      congr 1
      have hreim : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := (Complex.re_add_im (τ : ℂ)).symm
      rw [hreim, Complex.ofReal_add, add_assoc, mul_add, mul_comm Complex.I, mul_comm Complex.I]
    rw [hfun]
    exact deriv_deriv_const_add (uhpSliceYR φ τ.re) τ.im
  have hnorm_sq : a ^ 2 + b ^ 2 = ‖w ()‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
  unfold HermitianCurvatureCore.leviForm euclLaplacianR
  change (B w w + B (Complex.I • w) (Complex.I • w)) / 4 =
    ((partialXXR φ τ + partialYYR φ τ) / 4) * ‖w ()‖ ^ 2
  rw [hB_w, hB_Iw, hBe1, hBeI, ← hnorm_sq]
  ring

/-- `C²` regularity of `z ↦ c * log (Im (z ()))` at every point of `uhpSet1D`. -/
private lemma contDiffAt_uhpLift1D_const_mul_log (c : ℝ) (τ : UpperHalfPlane) :
    ContDiffAt ℝ 2 (uhpLift1D (fun w => c * Real.log w.im)) (fun _ => (τ : ℂ)) := by
  have hopen : IsOpen uhpSet1D :=
    isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply ()))
  have hmem : (fun _ : Unit => (τ : ℂ)) ∈ uhpSet1D := τ.im_pos
  have hev : uhpLift1D (fun w => c * Real.log w.im) =ᶠ[𝓝 (fun _ : Unit => (τ : ℂ))]
      fun z : Unit → ℂ => c * Real.log (z ()).im := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    unfold uhpLift1D
    dsimp only
    have hof : (UpperHalfPlane.ofComplex (z ())).im = (z ()).im := by
      have h := UpperHalfPlane.ofComplex_apply_of_im_pos hz
      exact congrArg UpperHalfPlane.im h
    rw [hof]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have him : ContDiffAt ℝ 2 (fun z : Unit → ℂ => (z ()).im) (fun _ => (τ : ℂ)) :=
    (Complex.imCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℂ) ())).contDiff.contDiffAt
  exact contDiffAt_const.mul (him.log τ.im_pos.ne')

/-- Exact Levi curvature form of the Hodge line bundle potential `φ_ω(τ) = -log(Im τ)`:
`leviForm (uhpLift1D hodgePotential) τ w = (1 / 4) * τ.im⁻² * ‖w ()‖²`. -/
theorem leviForm_hodgePotential (τ : UpperHalfPlane) (w : Unit → ℂ) :
    HermitianCurvatureCore.leviForm (uhpLift1D hodgePotential) (fun _ => (τ : ℂ)) w =
      (1 / 4 * τ.im ^ (-2 : ℝ)) * ‖w ()‖ ^ 2 := by
  have hpot : hodgePotential = fun w : UpperHalfPlane => (-1 : ℝ) * Real.log w.im := by
    funext w; unfold hodgePotential; ring
  rw [hpot, leviForm_uhpLift1D (contDiffAt_uhpLift1D_const_mul_log (-1) τ) w,
    euclLaplacianR_const_mul_log_im (-1) τ]
  ring

/-- **Strict Plurisubharmonicity / Ampleness of the Hodge Line Bundle `ω`** (wired to
`HermitianCurvatureCore.IsPlurisubharmonicOn`). -/
theorem isPlurisubharmonicOn_hodgePotential :
    HermitianCurvatureCore.IsPlurisubharmonicOn (uhpLift1D hodgePotential) uhpSet1D := by
  intro z hz
  let τ : UpperHalfPlane := ⟨z (), hz⟩
  have hz_eq : z = fun _ => (τ : ℂ) := by
    funext u; cases u; rfl
  rw [hz_eq]
  have hpot : hodgePotential = fun w : UpperHalfPlane => (-1 : ℝ) * Real.log w.im := by
    funext w; unfold hodgePotential; ring
  refine ⟨by rw [hpot]; exact contDiffAt_uhpLift1D_const_mul_log (-1) τ, fun w => ?_⟩
  rw [leviForm_hodgePotential]
  have hpos : 0 < τ.im ^ (-2 : ℝ) := Real.rpow_pos_of_pos τ.im_pos _
  exact mul_nonneg (mul_nonneg (by norm_num) hpos.le) (sq_nonneg _)

/-- Plurisubharmonicity of the weight-`k` automorphic metric potential `-log h_k = -k log y`
for every non-negative weight `k ≥ 0`. -/
theorem isPlurisubharmonicOn_automorphicPotential {k : ℤ} (hk : 0 ≤ k) :
    HermitianCurvatureCore.IsPlurisubharmonicOn
      (uhpLift1D (fun w => -Real.log (automorphicMetric k w))) uhpSet1D := by
  intro z hz
  let τ : UpperHalfPlane := ⟨z (), hz⟩
  have hz_eq : z = fun _ => (τ : ℂ) := by
    funext u; cases u; rfl
  rw [hz_eq]
  have hfun : (fun w : UpperHalfPlane => -Real.log (automorphicMetric k w)) =
      fun w => (-(k : ℝ)) * Real.log w.im := by
    funext w
    unfold automorphicMetric
    rw [Real.log_zpow]
    ring
  rw [hfun]
  refine ⟨contDiffAt_uhpLift1D_const_mul_log (-(k : ℝ)) τ, fun w => ?_⟩
  rw [leviForm_uhpLift1D (contDiffAt_uhpLift1D_const_mul_log (-(k : ℝ)) τ) w,
    euclLaplacianR_const_mul_log_im (-(k : ℝ)) τ]
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hpos : 0 < τ.im ^ (-2 : ℝ) := Real.rpow_pos_of_pos τ.im_pos _
  have hsimp : -(-(k : ℝ)) * τ.im ^ (-2 : ℝ) / 4 * ‖w ()‖ ^ 2 =
      (k : ℝ) * τ.im ^ (-2 : ℝ) / 4 * ‖w ()‖ ^ 2 := by ring
  rw [hsimp]
  exact mul_nonneg (div_nonneg (mul_nonneg hkR hpos.le) (by norm_num)) (sq_nonneg _)

/-- Exact identity between `HermitianCurvatureCore.ptNormSq` for the Hodge potential
`φ_ω(τ) = -log(Im τ)` at tensor power `k : ℕ` and `automorphicNormSq k`. -/
theorem ptNormSq_hodgePotential_eq_automorphicNormSq (k : ℕ) (f : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) :
    HermitianCurvatureCore.ptNormSq hodgePotential k f τ = automorphicNormSq (k : ℤ) f τ := by
  unfold HermitianCurvatureCore.ptNormSq automorphicNormSq automorphicMetric hodgePotential
  congr 1
  have h1 : -(k : ℝ) * -Real.log τ.im = Real.log τ.im * (k : ℝ) := by ring
  rw [h1, ← Real.rpow_def_of_pos τ.im_pos, Real.rpow_natCast, zpow_natCast]

/-- **Chern–Weil Metric-Change Bracket on `SL₂(ℤ) \ ℍ`** (wired directly to
`HermitianCurvatureCore.chernWeilChange_bounds` with exact total degree `vol = k / 12`). -/
theorem chernWeilChange_stdFD_bounds (k : ℤ) (hk : 0 ≤ k) {u : ℝ × ℝ → ℝ} {uMin uMax : ℝ}
    (huMin : ∀ p, uMin ≤ u p) (huMax : ∀ p, u p ≤ uMax)
    (hu_int : IntegrableOn (fun p : ℝ × ℝ => u p * ((k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)))
      stdFD volume) :
    uMin * ((k : ℝ) / 12) ≤
      HermitianCurvatureCore.chernWeilChange (volume.restrict stdFD) u
        (fun _ p => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) ∧
    HermitianCurvatureCore.chernWeilChange (volume.restrict stdFD) u
      (fun _ p => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) ≤ uMax * ((k : ℝ) / 12) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hd_nn : ∀ _t ∈ Set.Icc (0 : ℝ) 1, ∀ p : ℝ × ℝ,
      0 ≤ (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ) := fun _ _ p => by
    have h1 : 0 ≤ (k : ℝ) / (4 * Real.pi) := by positivity
    have h2 : 0 ≤ (p.2) ^ (-2 : ℝ) := by
      rcases lt_trichotomy p.2 0 with hlt | h0 | hgt
      · have heq : (p.2) ^ (-2 : ℝ) = (p.2 ^ (-2 : ℤ)) := by
          rw [← Real.rpow_intCast]; norm_num
        rw [heq, _root_.zpow_neg]
        have hsq : 0 ≤ p.2 ^ (2 : ℤ) := by norm_cast; exact sq_nonneg p.2
        exact inv_nonneg.mpr hsq
      · rw [h0, Real.zero_rpow (by norm_num)]
      · exact (Real.rpow_pos_of_pos hgt _).le
    exact mul_nonneg h1 h2
  have hd_int : ∀ _t ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun p : ℝ × ℝ => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ))
        (volume.restrict stdFD) := fun _ _ =>
    integrableOn_hyperbolicMeasure_stdFD.const_mul _
  exact HermitianCurvatureCore.chernWeilChange_bounds (volume.restrict stdFD) huMin huMax hd_nn
    hd_int (fun _ _ => hu_int) (fun _ _ => firstChernIntegral_weight_k_eq k)
    intervalIntegrable_const

end CoreWiring

/-! ## Section 5: Concrete Bochner–Weitzenböck Identities & Negative-Weight Vanishing (`k < 0`) -/

section BochnerVanishing

/-- Complex derivative `f'(τ)` of a holomorphic function `f : UpperHalfPlane → ℂ`, defined via
its lift `f ∘ UpperHalfPlane.ofComplex` on `{z : ℂ | 0 < z.im}`. -/
def uhpDeriv (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  deriv (f ∘ UpperHalfPlane.ofComplex) (τ : ℂ)

/-- Real-analytic derivative of `t ↦ ‖g t‖²` for a complex-valued curve `g : ℝ → ℂ`. -/
private lemma hasDerivAt_norm_sq_curve {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s : ℝ => ‖g s‖ ^ 2) (2 * (g' * conj (g t)).re) t := by
  have heq : (fun s : ℝ => ‖g s‖ ^ 2) = fun s : ℝ => (g s * conj (g s)).re := by
    funext s
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [heq]
  have hconj : HasDerivAt (fun s : ℝ => conj (g s)) (conj g') t :=
    (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hg)
  have hmul : HasDerivAt (fun s : ℝ => g s * conj (g s))
      (g' * conj (g t) + g t * conj g') t := hg.mul hconj
  have hre : HasDerivAt (fun s : ℝ => (g s * conj (g s)).re)
      (g' * conj (g t) + g t * conj g').re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hmul
  have hval : (g' * conj (g t) + g t * conj g').re = 2 * (g' * conj (g t)).re := by
    rw [Complex.add_re]
    have hsym : (g t * conj g').re = (g' * conj (g t)).re := by
      have hc : conj (g' * conj (g t)) = g t * conj g' := by
        simp [mul_comm]
      rw [← hc, Complex.conj_re]
    linarith
  rwa [hval] at hre

/-- First and second derivatives along the horizontal slice `x ↦ F(x + i y)` of a holomorphic
function `F` on `{z : ℂ | 0 < z.im}`. -/
private lemma hasDerivAt_holo_sliceX {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun u : ℝ => F ((u : ℂ) + Complex.I * (y : ℂ)))
      (deriv F ((x : ℂ) + Complex.I * (y : ℂ))) x := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hmem : ((x : ℂ) + Complex.I * (y : ℂ)) ∈ {z : ℂ | 0 < z.im} := by simp [hy]
  have hdiff : HasDerivAt F (deriv F ((x : ℂ) + Complex.I * (y : ℂ)))
      ((x : ℂ) + Complex.I * (y : ℂ)) := (hF.differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
  have hline : HasDerivAt (fun u : ℝ => (u : ℂ) + Complex.I * (y : ℂ)) 1 x := by
    have h1 := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (Complex.I * (y : ℂ))
    exact h1.congr_deriv (by simp)
  exact ((hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hline).congr_deriv (by simp)

/-- First derivative along the vertical slice `y ↦ F(x + i y)` of a holomorphic function `F`
on `{z : ℂ | 0 < z.im}`. -/
private lemma hasDerivAt_holo_sliceY {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun v : ℝ => F ((x : ℂ) + Complex.I * (v : ℂ)))
      (Complex.I * deriv F ((x : ℂ) + Complex.I * (y : ℂ))) y := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hmem : ((x : ℂ) + Complex.I * (y : ℂ)) ∈ {z : ℂ | 0 < z.im} := by simp [hy]
  have hdiff : HasDerivAt F (deriv F ((x : ℂ) + Complex.I * (y : ℂ)))
      ((x : ℂ) + Complex.I * (y : ℂ)) := (hF.differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
  have hline : HasDerivAt (fun v : ℝ => (x : ℂ) + Complex.I * (v : ℂ)) Complex.I y := by
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul Complex.I).const_add (x : ℂ)
    exact h1.congr_deriv (by simp)
  exact ((hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt y hline).congr_deriv (by simp)

/-- Canonical Cartesian decomposition `(τ.re : ℂ) + I * (τ.im : ℂ) = τ`. -/
private lemma uhp_re_add_I_im (τ : UpperHalfPlane) :
    (τ.re : ℂ) + Complex.I * (τ.im : ℂ) = (τ : ℂ) := by
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (τ : ℂ)

/-- First partial derivative `∂/∂x (‖f‖²) = 2 Re(f' · conj f)` for holomorphic `f`. -/
private lemma hasDerivAt_uhpSliceXR_norm_sq {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (uhpSliceXR (fun w => ‖f w‖ ^ 2) y)
      (2 * (deriv (f ∘ UpperHalfPlane.ofComplex) ((x : ℂ) + Complex.I * (y : ℂ)) *
        conj ((f ∘ UpperHalfPlane.ofComplex) ((x : ℂ) + Complex.I * (y : ℂ)))).re) x := by
  have hF : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  exact hasDerivAt_norm_sq_curve (hasDerivAt_holo_sliceX hF hy)

/-- First partial derivative `∂/∂y (‖f‖²) = 2 Re(i f' · conj f)` for holomorphic `f`. -/
private lemma hasDerivAt_uhpSliceYR_norm_sq {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {x y : ℝ} (hy : 0 < y) :
    HasDerivAt (uhpSliceYR (fun w => ‖f w‖ ^ 2) x)
      (2 * (Complex.I * deriv (f ∘ UpperHalfPlane.ofComplex) ((x : ℂ) + Complex.I * (y : ℂ)) *
        conj ((f ∘ UpperHalfPlane.ofComplex) ((x : ℂ) + Complex.I * (y : ℂ)))).re) y := by
  have hF : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  exact hasDerivAt_norm_sq_curve (hasDerivAt_holo_sliceY hF hy)

/-- Second partial derivative `∂²/∂x² (‖f‖²) = 2 Re(f'' · conj f) + 2 ‖f'‖²` for holomorphic `f`. -/
private lemma partialXXR_norm_sq_holomorphic {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : UpperHalfPlane) :
    partialXXR (fun w => ‖f w‖ ^ 2) τ =
      2 * (deriv (deriv (f ∘ UpperHalfPlane.ofComplex)) (τ : ℂ) * conj (f τ)).re +
        2 * ‖uhpDeriv f τ‖ ^ 2 := by
  set F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF' : DifferentiableOn ℂ (deriv F) {z : ℂ | 0 < z.im} :=
    hF.deriv hopen
  have htau : ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) = (τ : ℂ) := uhp_re_add_I_im τ
  have hFtau : F (τ : ℂ) = f τ := by
    simp only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  unfold partialXXR
  have hd1 : (fun x : ℝ => deriv (uhpSliceXR (fun w => ‖f w‖ ^ 2) τ.im) x) =
      fun x : ℝ => 2 * (deriv F ((x : ℂ) + Complex.I * (τ.im : ℂ)) *
        conj (F ((x : ℂ) + Complex.I * (τ.im : ℂ)))).re := by
    funext x
    exact (hasDerivAt_uhpSliceXR_norm_sq hf τ.im_pos).deriv
  rw [hd1]
  have hg1 : HasDerivAt (fun x : ℝ => deriv F ((x : ℂ) + Complex.I * (τ.im : ℂ)))
      (deriv (deriv F) ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) τ.re :=
    hasDerivAt_holo_sliceX hF' τ.im_pos
  have hg2 : HasDerivAt (fun x : ℝ => conj (F ((x : ℂ) + Complex.I * (τ.im : ℂ))))
      (conj (deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))) τ.re :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ.re (hasDerivAt_holo_sliceX hF τ.im_pos)
  have hre : HasDerivAt
      (fun x : ℝ => 2 * (deriv F ((x : ℂ) + Complex.I * (τ.im : ℂ)) *
        conj (F ((x : ℂ) + Complex.I * (τ.im : ℂ)))).re)
      (2 * (deriv (deriv F) ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) *
          conj (F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) +
        deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) *
          conj (deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))).re) τ.re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ.re (hg1.mul hg2)).const_mul (2 : ℝ)
  rw [hre.deriv, htau, hFtau, Complex.add_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  unfold uhpDeriv
  ring

/-- Second partial derivative `∂²/∂y² (‖f‖²) = -2 Re(f'' · conj f) + 2 ‖f'‖²` for holomorphic `f`. -/
private lemma partialYYR_norm_sq_holomorphic {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : UpperHalfPlane) :
    partialYYR (fun w => ‖f w‖ ^ 2) τ =
      -2 * (deriv (deriv (f ∘ UpperHalfPlane.ofComplex)) (τ : ℂ) * conj (f τ)).re +
        2 * ‖uhpDeriv f τ‖ ^ 2 := by
  set F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF' : DifferentiableOn ℂ (deriv F) {z : ℂ | 0 < z.im} :=
    hF.deriv hopen
  have htau : ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) = (τ : ℂ) := uhp_re_add_I_im τ
  have hFtau : F (τ : ℂ) = f τ := by
    simp only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  unfold partialYYR
  have hd1 : (fun y : ℝ => deriv (uhpSliceYR (fun w => ‖f w‖ ^ 2) τ.re) y) =ᶠ[𝓝 τ.im]
      fun y : ℝ => 2 * (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (y : ℂ)) *
        conj (F ((τ.re : ℂ) + Complex.I * (y : ℂ)))).re := by
    filter_upwards [isOpen_Ioi.mem_nhds τ.im_pos] with y hy
    exact (hasDerivAt_uhpSliceYR_norm_sq hf hy).deriv
  rw [hd1.deriv_eq]
  have hg1 : HasDerivAt (fun y : ℝ => Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (y : ℂ)))
      (Complex.I * (Complex.I * deriv (deriv F) ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))) τ.im :=
    (hasDerivAt_holo_sliceY hF' τ.im_pos).const_mul Complex.I
  have hg2 : HasDerivAt (fun y : ℝ => conj (F ((τ.re : ℂ) + Complex.I * (y : ℂ))))
      (conj (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))) τ.im :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ.im (hasDerivAt_holo_sliceY hF τ.im_pos)
  have hre : HasDerivAt
      (fun y : ℝ => 2 * (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (y : ℂ)) *
        conj (F ((τ.re : ℂ) + Complex.I * (y : ℂ)))).re)
      (2 * (Complex.I * (Complex.I * deriv (deriv F) ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) *
          conj (F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) +
        Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) *
          conj (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))).re) τ.im :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ.im (hg1.mul hg2)).const_mul (2 : ℝ)
  rw [hre.deriv, htau, hFtau]
  have h1 : Complex.I * (Complex.I * deriv (deriv F) (τ : ℂ)) * conj (f τ) =
      -(deriv (deriv F) (τ : ℂ) * conj (f τ)) := by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  have h2 : Complex.I * deriv F (τ : ℂ) * conj (Complex.I * deriv F (τ : ℂ)) =
      ((‖deriv F (τ : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_I, one_mul]
  rw [h1, h2, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  unfold uhpDeriv
  ring

/-- **Euclidean Laplacian of `|f|²` for Holomorphic `f`**:
`Δ_Eucl (‖f‖²) = 4 ‖f'‖²` identically on `UpperHalfPlane`. -/
theorem euclLaplacianR_norm_sq_holomorphic {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : UpperHalfPlane) :
    euclLaplacianR (fun w => ‖f w‖ ^ 2) τ = 4 * ‖uhpDeriv f τ‖ ^ 2 := by
  unfold euclLaplacianR
  rw [partialXXR_norm_sq_holomorphic hf τ, partialYYR_norm_sq_holomorphic hf τ]
  ring

/-- Helper: second derivative of `log ∘ u` at a point where `u a > 0`. -/
private lemma deriv_deriv_log_comp {u : ℝ → ℝ} {a u' u'' : ℝ} (hu_pos : 0 < u a)
    (hu_ev : ∀ᶠ t in 𝓝 a, 0 < u t ∧ HasDerivAt u (deriv u t) t)
    (hu1 : HasDerivAt u u' a) (hu2 : HasDerivAt (deriv u) u'' a) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => Real.log (u s)) t) a =
      (u'' * u a - u' ^ 2) / (u a) ^ 2 := by
  have hd1 : (fun t : ℝ => deriv (fun s : ℝ => Real.log (u s)) t) =ᶠ[𝓝 a]
      fun t : ℝ => deriv u t / u t := by
    filter_upwards [hu_ev] with t ht
    exact (ht.2.log ht.1.ne').deriv
  rw [hd1.deriv_eq]
  have hd2 : HasDerivAt (fun t : ℝ => deriv u t / u t)
      ((u'' * u a - deriv u a * u') / (u a) ^ 2) a := hu2.div hu1 hu_pos.ne'
  rw [hd2.deriv, hu1.deriv]
  ring

/-- **Harmonicity of `log ‖f‖²` Away from Zeros of Holomorphic `f`**:
`Δ_Eucl (log ‖f‖²) = 0` at every `τ` where `f τ ≠ 0`. -/
theorem euclLaplacianR_log_norm_sq_holomorphic {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {τ : UpperHalfPlane} (hτ : f τ ≠ 0) :
    euclLaplacianR (fun w => Real.log (‖f w‖ ^ 2)) τ = 0 := by
  set F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF' : DifferentiableOn ℂ (deriv F) {z : ℂ | 0 < z.im} := hF.deriv hopen
  have htau : ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) = (τ : ℂ) := uhp_re_add_I_im τ
  have hFtau : F (τ : ℂ) = f τ := by
    simp only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  set u : UpperHalfPlane → ℝ := fun w => ‖f w‖ ^ 2
  have hu_pos : 0 < ‖f τ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hτ)
  have huX_tau : uhpSliceXR u τ.im τ.re = ‖f τ‖ ^ 2 := by
    simp only [uhpSliceXR, u, ofComplex_self]
  have huY_tau : uhpSliceYR u τ.re τ.im = ‖f τ‖ ^ 2 := by
    simp only [uhpSliceYR, u, ofComplex_self]
  -- Horizontal derivatives of `u`.
  have huX1 : HasDerivAt (uhpSliceXR u τ.im) (2 * (uhpDeriv f τ * conj (f τ)).re) τ.re := by
    have h := hasDerivAt_uhpSliceXR_norm_sq hf (x := τ.re) τ.im_pos
    exact h.congr_deriv (by rw [htau]; simp only [uhpDeriv, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos])
  have huX_ev : ∀ᶠ x in 𝓝 τ.re,
      0 < uhpSliceXR u τ.im x ∧ HasDerivAt (uhpSliceXR u τ.im) (deriv (uhpSliceXR u τ.im) x) x := by
    have hpos_ev : ∀ᶠ x in 𝓝 τ.re, 0 < uhpSliceXR u τ.im x :=
      huX1.continuousAt.eventually (isOpen_Ioi.mem_nhds (by rwa [huX_tau]))
    filter_upwards [hpos_ev] with x hx
    have hd := hasDerivAt_uhpSliceXR_norm_sq hf (x := x) τ.im_pos
    exact ⟨hx, by rwa [hd.deriv]⟩
  have huX2 : HasDerivAt (deriv (uhpSliceXR u τ.im))
      (2 * (deriv (deriv F) (τ : ℂ) * conj (f τ)).re + 2 * ‖uhpDeriv f τ‖ ^ 2) τ.re := by
    have hd1 : deriv (uhpSliceXR u τ.im) =
        fun x : ℝ => 2 * (deriv F ((x : ℂ) + Complex.I * (τ.im : ℂ)) *
          conj (F ((x : ℂ) + Complex.I * (τ.im : ℂ)))).re := by
      funext x
      exact (hasDerivAt_uhpSliceXR_norm_sq hf τ.im_pos).deriv
    rw [hd1]
    have hg1 := hasDerivAt_holo_sliceX hF' (x := τ.re) τ.im_pos
    have hg2 := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ.re
      (hasDerivAt_holo_sliceX hF (x := τ.re) τ.im_pos)
    have hre : HasDerivAt
        (fun x : ℝ => 2 * (deriv F ((x : ℂ) + Complex.I * (τ.im : ℂ)) *
          conj (F ((x : ℂ) + Complex.I * (τ.im : ℂ)))).re)
        (2 * (deriv (deriv F) ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) *
            conj (F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) +
          deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) *
            conj (deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))).re) τ.re :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ.re (hg1.mul hg2)).const_mul (2 : ℝ)
    refine hre.congr_deriv ?_
    rw [htau, hFtau, Complex.add_re, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    unfold uhpDeriv
    ring
  have hlogXX : partialXXR (fun w => Real.log (‖f w‖ ^ 2)) τ =
      ((2 * (deriv (deriv F) (τ : ℂ) * conj (f τ)).re + 2 * ‖uhpDeriv f τ‖ ^ 2) * ‖f τ‖ ^ 2 -
        (2 * (uhpDeriv f τ * conj (f τ)).re) ^ 2) / (‖f τ‖ ^ 2) ^ 2 := by
    unfold partialXXR
    have h := deriv_deriv_log_comp (by rwa [huX_tau]) huX_ev huX1 huX2
    rwa [huX_tau] at h
  -- Vertical derivatives of `u`.
  have huY1 : HasDerivAt (uhpSliceYR u τ.re)
      (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) τ.im := by
    have h := hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) τ.im_pos
    exact h.congr_deriv (by rw [htau]; simp only [uhpDeriv, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos])
  have huY_ev : ∀ᶠ y in 𝓝 τ.im,
      0 < uhpSliceYR u τ.re y ∧ HasDerivAt (uhpSliceYR u τ.re) (deriv (uhpSliceYR u τ.re) y) y := by
    have hpos_ev : ∀ᶠ y in 𝓝 τ.im, 0 < uhpSliceYR u τ.re y :=
      huY1.continuousAt.eventually (isOpen_Ioi.mem_nhds (by rwa [huY_tau]))
    filter_upwards [hpos_ev, isOpen_Ioi.mem_nhds τ.im_pos] with y hy_pos hy0
    have hd := hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) hy0
    exact ⟨hy_pos, by rwa [hd.deriv]⟩
  have huY2 : HasDerivAt (deriv (uhpSliceYR u τ.re))
      (-2 * (deriv (deriv F) (τ : ℂ) * conj (f τ)).re + 2 * ‖uhpDeriv f τ‖ ^ 2) τ.im := by
    have hd1 : deriv (uhpSliceYR u τ.re) =ᶠ[𝓝 τ.im]
        fun y : ℝ => 2 * (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (y : ℂ)) *
          conj (F ((τ.re : ℂ) + Complex.I * (y : ℂ)))).re := by
      filter_upwards [isOpen_Ioi.mem_nhds τ.im_pos] with y hy
      exact (hasDerivAt_uhpSliceYR_norm_sq hf hy).deriv
    refine HasDerivAt.congr_of_eventuallyEq ?_ hd1
    have hg1 := (hasDerivAt_holo_sliceY hF' (x := τ.re) τ.im_pos).const_mul Complex.I
    have hg2 := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ.im
      (hasDerivAt_holo_sliceY hF (x := τ.re) τ.im_pos)
    have hre : HasDerivAt
        (fun y : ℝ => 2 * (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (y : ℂ)) *
          conj (F ((τ.re : ℂ) + Complex.I * (y : ℂ)))).re)
        (2 * (Complex.I * (Complex.I * deriv (deriv F) ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) *
            conj (F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ))) +
          Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) *
            conj (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)))).re) τ.im :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ.im (hg1.mul hg2)).const_mul (2 : ℝ)
    refine hre.congr_deriv ?_
    rw [htau, hFtau]
    have h1 : Complex.I * (Complex.I * deriv (deriv F) (τ : ℂ)) * conj (f τ) =
        -(deriv (deriv F) (τ : ℂ) * conj (f τ)) := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    have h2 : Complex.I * deriv F (τ : ℂ) * conj (Complex.I * deriv F (τ : ℂ)) =
        ((‖deriv F (τ : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_I, one_mul]
    rw [h1, h2, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    unfold uhpDeriv
    ring
  have hlogYY : partialYYR (fun w => Real.log (‖f w‖ ^ 2)) τ =
      ((-2 * (deriv (deriv F) (τ : ℂ) * conj (f τ)).re + 2 * ‖uhpDeriv f τ‖ ^ 2) * ‖f τ‖ ^ 2 -
        (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) ^ 2) / (‖f τ‖ ^ 2) ^ 2 := by
    unfold partialYYR
    have h := deriv_deriv_log_comp (by rwa [huY_tau]) huY_ev huY1 huY2
    rwa [huY_tau] at h
  -- Combine: `4 ‖f'‖² ‖f‖² = (2 Re(f' conj f))² + (2 Re(i f' conj f))²`.
  have hpyth : (uhpDeriv f τ * conj (f τ)).re ^ 2 + (Complex.I * uhpDeriv f τ * conj (f τ)).re ^ 2 =
      ‖uhpDeriv f τ‖ ^ 2 * ‖f τ‖ ^ 2 := by
    have him : (Complex.I * uhpDeriv f τ * conj (f τ)).re = -(uhpDeriv f τ * conj (f τ)).im := by
      rw [mul_assoc, Complex.mul_re, Complex.I_re, Complex.I_im]
      ring
    rw [him, neg_sq]
    have hns := Complex.normSq_apply (uhpDeriv f τ * conj (f τ))
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj, mul_pow, ← sq, ← sq] at hns
    linarith
  unfold euclLaplacianR
  rw [hlogXX, hlogYY, ← add_div]
  have hnum :
      (2 * (deriv (deriv F) (τ : ℂ) * conj (f τ)).re + 2 * ‖uhpDeriv f τ‖ ^ 2) * ‖f τ‖ ^ 2 -
        (2 * (uhpDeriv f τ * conj (f τ)).re) ^ 2 +
      ((-2 * (deriv (deriv F) (τ : ℂ) * conj (f τ)).re + 2 * ‖uhpDeriv f τ‖ ^ 2) * ‖f τ‖ ^ 2 -
        (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) ^ 2) = 0 := by
    linarith [hpyth]
  rw [hnum, zero_div]

/-- **Logarithmic Bochner–Curvature Identity Away from Zeros**:
for any holomorphic `f` on `UpperHalfPlane`, any `k : ℝ`, and any `τ` with `f τ ≠ 0`,
$$\Delta_{\mathrm{Eucl}}\bigl(\log(|f(\tau)|^2 y^k)\bigr) = -\frac{k}{y^2}.$$ -/
theorem bochner_log_laplacian_weight_k {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℝ) {τ : UpperHalfPlane} (hτ : f τ ≠ 0) :
    euclLaplacianR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ = -k / τ.im ^ 2 := by
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hcontX : ContinuousAt (uhpSliceXR (fun w => ‖f w‖ ^ 2) τ.im) τ.re :=
    (hasDerivAt_uhpSliceXR_norm_sq hf τ.im_pos).continuousAt
  have hcontY : ContinuousAt (uhpSliceYR (fun w => ‖f w‖ ^ 2) τ.re) τ.im :=
    (hasDerivAt_uhpSliceYR_norm_sq hf τ.im_pos).continuousAt
  have hpos_tau : 0 < ‖f τ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hτ)
  have hXX : partialXXR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ =
      partialXXR (fun w => Real.log (‖f w‖ ^ 2)) τ := by
    unfold partialXXR
    have hev : uhpSliceXR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ.im =ᶠ[𝓝 τ.re]
        fun x : ℝ => uhpSliceXR (fun w => Real.log (‖f w‖ ^ 2)) τ.im x + k * Real.log τ.im := by
      have hpos_ev : ∀ᶠ x in 𝓝 τ.re, 0 < uhpSliceXR (fun w => ‖f w‖ ^ 2) τ.im x :=
        hcontX.eventually (isOpen_Ioi.mem_nhds (by simpa [uhpSliceXR, ofComplex_self] using hpos_tau))
      filter_upwards [hpos_ev] with x hx
      unfold uhpSliceXR at hx ⊢
      dsimp only at hx ⊢
      rw [ofComplex_im_eq τ.im_pos,
        Real.log_mul hx.ne' (Real.rpow_pos_of_pos τ.im_pos k).ne', Real.log_rpow τ.im_pos]
    have hd1 : deriv (uhpSliceXR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ.im) =ᶠ[𝓝 τ.re]
        deriv (uhpSliceXR (fun w => Real.log (‖f w‖ ^ 2)) τ.im) := by
      filter_upwards [hev.eventuallyEq_nhds] with x hx
      rw [hx.deriv_eq, deriv_add_const]
    exact hd1.deriv_eq
  have hYY : partialYYR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ =
      partialYYR (fun w => Real.log (‖f w‖ ^ 2)) τ + (-k / τ.im ^ 2) := by
    unfold partialYYR
    have hev : uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ.re =ᶠ[𝓝 τ.im]
        fun y : ℝ => uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re y + k * Real.log y := by
      have hpos_ev : ∀ᶠ y in 𝓝 τ.im, 0 < uhpSliceYR (fun w => ‖f w‖ ^ 2) τ.re y :=
        hcontY.eventually (isOpen_Ioi.mem_nhds (by simpa [uhpSliceYR, ofComplex_self] using hpos_tau))
      filter_upwards [hpos_ev, isOpen_Ioi.mem_nhds τ.im_pos] with y hy hy0
      unfold uhpSliceYR at hy ⊢
      dsimp only at hy ⊢
      rw [ofComplex_im_eq hy0,
        Real.log_mul hy.ne' (Real.rpow_pos_of_pos hy0 k).ne', Real.log_rpow hy0]
    have hd1 : deriv (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2 * w.im ^ k)) τ.re) =ᶠ[𝓝 τ.im]
        fun y : ℝ => deriv (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re) y + k * y⁻¹ := by
      have hpos_ev : ∀ᶠ y in 𝓝 τ.im, 0 < uhpSliceYR (fun w => ‖f w‖ ^ 2) τ.re y :=
        hcontY.eventually (isOpen_Ioi.mem_nhds (by simpa [uhpSliceYR, ofComplex_self] using hpos_tau))
      filter_upwards [hev.eventuallyEq_nhds, hpos_ev, isOpen_Ioi.mem_nhds τ.im_pos] with y hy hypos hy0
      rw [hy.deriv_eq]
      have hda : DifferentiableAt ℝ (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re) y :=
        ((hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) hy0).log hypos.ne').differentiableAt
      have hdb : HasDerivAt (fun u : ℝ => k * Real.log u) (k * y⁻¹) y :=
        (Real.hasDerivAt_log hy0.ne').const_mul k
      have hadd := hda.hasDerivAt.add hdb
      exact hadd.deriv
    rw [hd1.deriv_eq]
    have hda2 : DifferentiableAt ℝ (deriv (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re)) τ.im := by
      set u : UpperHalfPlane → ℝ := fun w => ‖f w‖ ^ 2
      have huY1 := hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) τ.im_pos
      have hpos_ev : ∀ᶠ y in 𝓝 τ.im, 0 < uhpSliceYR u τ.re y :=
        huY1.continuousAt.eventually
          (isOpen_Ioi.mem_nhds (by simpa [uhpSliceYR, u, ofComplex_self] using hpos_tau))
      have hdlog : deriv (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re) =ᶠ[𝓝 τ.im]
          fun y : ℝ => deriv (uhpSliceYR u τ.re) y / uhpSliceYR u τ.re y := by
        filter_upwards [hpos_ev, isOpen_Ioi.mem_nhds τ.im_pos] with y hypos hy0
        have hdu := hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) hy0
        have hlogd := (hdu.log hypos.ne').deriv
        rwa [← hdu.deriv] at hlogd
      rw [hdlog.differentiableAt_iff]
      have hF' : DifferentiableOn ℂ (deriv (f ∘ UpperHalfPlane.ofComplex)) {z : ℂ | 0 < z.im} :=
        hF.deriv hopen
      have hduY : DifferentiableAt ℝ (deriv (uhpSliceYR u τ.re)) τ.im := by
        have hdeq : deriv (uhpSliceYR u τ.re) =ᶠ[𝓝 τ.im]
            fun y : ℝ => 2 * (Complex.I * deriv (f ∘ UpperHalfPlane.ofComplex)
              ((τ.re : ℂ) + Complex.I * (y : ℂ)) *
              conj ((f ∘ UpperHalfPlane.ofComplex) ((τ.re : ℂ) + Complex.I * (y : ℂ)))).re := by
          filter_upwards [isOpen_Ioi.mem_nhds τ.im_pos] with y hy0
          exact (hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) hy0).deriv
        rw [hdeq.differentiableAt_iff]
        have hg1 := (hasDerivAt_holo_sliceY hF' (x := τ.re) τ.im_pos).const_mul Complex.I
        have hg2 := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ.im
          (hasDerivAt_holo_sliceY hF (x := τ.re) τ.im_pos)
        exact ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ.im (hg1.mul hg2)).const_mul 2).differentiableAt
      exact hduY.div huY1.differentiableAt (by simpa [uhpSliceYR, u, ofComplex_self] using hpos_tau.ne')
    have hdb2 : HasDerivAt (fun y : ℝ => k * y⁻¹) (k * -(τ.im ^ 2)⁻¹) τ.im :=
      (hasDerivAt_inv τ.im_pos.ne').const_mul k
    have hadd2 : HasDerivAt
        (fun y : ℝ => deriv (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re) y + k * y⁻¹)
        (deriv (deriv (uhpSliceYR (fun w => Real.log (‖f w‖ ^ 2)) τ.re)) τ.im + k * -(τ.im ^ 2)⁻¹) τ.im :=
      hda2.hasDerivAt.add hdb2
    rw [hadd2.deriv]
    ring
  unfold euclLaplacianR
  rw [hXX, hYY]
  have h0 := euclLaplacianR_log_norm_sq_holomorphic hf hτ
  unfold euclLaplacianR at h0
  linarith

/-- **Concrete Bochner–Weitzenböck Identity on `UpperHalfPlane`**:
for every holomorphic `f : UpperHalfPlane → ℂ`, every `k : ℝ`, and every `τ ∈ ℍ`:
$$\Delta_{\mathrm{Eucl}}\bigl(|f(\tau)|^2 y^k\bigr)
  = 4 y^k \left|f'(\tau) + \frac{k}{2 i y} f(\tau)\right|^2 - k y^{k - 2} |f(\tau)|^2.$$ -/
theorem bochner_identity_weight_k {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℝ) (τ : UpperHalfPlane) :
    euclLaplacianR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ =
      4 * τ.im ^ k * ‖uhpDeriv f τ + ((k : ℂ) / (2 * Complex.I * (τ.im : ℂ))) * f τ‖ ^ 2 -
        k * τ.im ^ (k - 2) * ‖f τ‖ ^ 2 := by
  set F : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex
  have hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hF' : DifferentiableOn ℂ (deriv F) {z : ℂ | 0 < z.im} := hF.deriv hopen
  have htau : ((τ.re : ℂ) + Complex.I * (τ.im : ℂ)) = (τ : ℂ) := uhp_re_add_I_im τ
  have hFtau : F (τ : ℂ) = f τ := by
    simp only [F, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos]
  set u : UpperHalfPlane → ℝ := fun w => ‖f w‖ ^ 2
  have huY_tau : uhpSliceYR u τ.re τ.im = ‖f τ‖ ^ 2 := by
    simp only [uhpSliceYR, u, ofComplex_self]
  -- Horizontal second partial: `y^k` is constant in `x`.
  have hXX : partialXXR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ =
      partialXXR u τ * τ.im ^ k := by
    unfold partialXXR
    have hslice : uhpSliceXR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ.im =
        fun x : ℝ => uhpSliceXR u τ.im x * τ.im ^ k := by
      funext x
      unfold uhpSliceXR u
      dsimp only
      rw [ofComplex_im_eq τ.im_pos]
    rw [hslice]
    have hd1 : (fun x : ℝ => deriv (fun t : ℝ => uhpSliceXR u τ.im t * τ.im ^ k) x) =
        fun x : ℝ => deriv (uhpSliceXR u τ.im) x * τ.im ^ k := by
      funext x
      exact deriv_mul_const_field (τ.im ^ k)
    rw [hd1]
    exact deriv_mul_const_field (τ.im ^ k)
  -- Vertical second partial via Leibniz rule on `u(x, y) * y^k`.
  have huY1 : HasDerivAt (uhpSliceYR u τ.re)
      (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) τ.im := by
    have h := hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) τ.im_pos
    exact h.congr_deriv (by rw [htau]; simp only [uhpDeriv, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply_of_im_pos τ.im_pos])
  have huY2 : HasDerivAt (deriv (uhpSliceYR u τ.re)) (partialYYR u τ) τ.im := by
    have hd1 : deriv (uhpSliceYR u τ.re) =ᶠ[𝓝 τ.im]
        fun y : ℝ => 2 * (Complex.I * deriv F ((τ.re : ℂ) + Complex.I * (y : ℂ)) *
          conj (F ((τ.re : ℂ) + Complex.I * (y : ℂ)))).re := by
      filter_upwards [isOpen_Ioi.mem_nhds τ.im_pos] with y hy
      exact (hasDerivAt_uhpSliceYR_norm_sq hf hy).deriv
    have hg1 := (hasDerivAt_holo_sliceY hF' (x := τ.re) τ.im_pos).const_mul Complex.I
    have hg2 := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt τ.im
      (hasDerivAt_holo_sliceY hF (x := τ.re) τ.im_pos)
    have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ.im (hg1.mul hg2)).const_mul (2 : ℝ)
    have hd := hre.congr_of_eventuallyEq hd1
    have hval : partialYYR u τ = _ := hd.deriv
    exact hd.congr_deriv hval.symm
  have hYY : partialYYR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ =
      partialYYR u τ * τ.im ^ k +
        2 * (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) * (k * τ.im ^ (k - 1)) +
        ‖f τ‖ ^ 2 * (k * (k - 1) * τ.im ^ (k - 2)) := by
    unfold partialYYR
    have hslice : uhpSliceYR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ.re =ᶠ[𝓝 τ.im]
        fun y : ℝ => uhpSliceYR u τ.re y * y ^ k := by
      filter_upwards [isOpen_Ioi.mem_nhds τ.im_pos] with y hy
      unfold uhpSliceYR u
      dsimp only
      rw [ofComplex_im_eq hy]
    have hd1 : deriv (uhpSliceYR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ.re) =ᶠ[𝓝 τ.im]
        fun y : ℝ => deriv (uhpSliceYR u τ.re) y * y ^ k +
          uhpSliceYR u τ.re y * (k * y ^ (k - 1)) := by
      filter_upwards [hslice.eventuallyEq_nhds, isOpen_Ioi.mem_nhds τ.im_pos] with y hy hy0
      rw [hy.deriv_eq]
      have hdu := hasDerivAt_uhpSliceYR_norm_sq hf (x := τ.re) hy0
      have hdp : HasDerivAt (fun v : ℝ => v ^ k) (k * y ^ (k - 1)) y :=
        Real.hasDerivAt_rpow_const (Or.inl hy0.ne')
      have hprod : HasDerivAt (fun v : ℝ => uhpSliceYR u τ.re v * v ^ k)
          (deriv (uhpSliceYR u τ.re) y * y ^ k + uhpSliceYR u τ.re y * (k * y ^ (k - 1))) y :=
        (hdu.mul hdp).congr_deriv (by rw [hdu.deriv])
      exact hprod.deriv
    rw [hd1.deriv_eq]
    have hdp1 : HasDerivAt (fun v : ℝ => v ^ k) (k * τ.im ^ (k - 1)) τ.im :=
      Real.hasDerivAt_rpow_const (Or.inl τ.im_pos.ne')
    have hdp2 : HasDerivAt (fun v : ℝ => k * v ^ (k - 1))
        (k * ((k - 1) * τ.im ^ (k - 1 - 1))) τ.im :=
      (Real.hasDerivAt_rpow_const (Or.inl τ.im_pos.ne')).const_mul k
    have htot : HasDerivAt
        (fun y : ℝ => deriv (uhpSliceYR u τ.re) y * y ^ k +
          uhpSliceYR u τ.re y * (k * y ^ (k - 1)))
        (partialYYR u τ * τ.im ^ k + deriv (uhpSliceYR u τ.re) τ.im * (k * τ.im ^ (k - 1)) +
          (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re * (k * τ.im ^ (k - 1)) +
            uhpSliceYR u τ.re τ.im * (k * ((k - 1) * τ.im ^ (k - 1 - 1))))) τ.im :=
      (huY2.mul hdp1).add (huY1.mul hdp2)
    rw [htot.deriv, huY1.deriv, huY_tau]
    have hexp : k - 1 - 1 = k - 2 := by ring
    change _ = partialYYR u τ * τ.im ^ k +
      2 * (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) * (k * τ.im ^ (k - 1)) +
      ‖f τ‖ ^ 2 * (k * (k - 1) * τ.im ^ (k - 2))
    rw [hexp]
    ring
  -- Now expand the Bochner square `‖f' + (k / (2 i y)) f‖²`.
  have hy_pos : 0 < τ.im := τ.im_pos
  have hyC : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_pos.ne'
  set α : ℂ := (k : ℂ) / (2 * Complex.I * (τ.im : ℂ))
  have hα_eq : α = -Complex.I * (((k / (2 * τ.im) : ℝ) : ℂ)) := by
    dsimp only [α]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    push_cast
    field_simp [hI, hyC]
    rw [Complex.I_sq]
    ring
  have hα_conj : conj α = Complex.I * (((k / (2 * τ.im) : ℝ) : ℂ)) := by
    rw [hα_eq]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hnorm_α : ‖α‖ ^ 2 = (k / (2 * τ.im)) ^ 2 := by
    rw [hα_eq, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hboch_sq : ‖uhpDeriv f τ + α * f τ‖ ^ 2 =
      ‖uhpDeriv f τ‖ ^ 2 + (k / τ.im) * (Complex.I * uhpDeriv f τ * conj (f τ)).re +
        (k / (2 * τ.im)) ^ 2 * ‖f τ‖ ^ 2 := by
    have h1 : ‖uhpDeriv f τ + α * f τ‖ ^ 2 =
        ((uhpDeriv f τ + α * f τ) * conj (uhpDeriv f τ + α * f τ)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [h1, map_add, map_mul]
    have hexp : (uhpDeriv f τ + α * f τ) * (conj (uhpDeriv f τ) + conj α * conj (f τ)) =
        uhpDeriv f τ * conj (uhpDeriv f τ) +
        (uhpDeriv f τ * (conj α * conj (f τ)) + (α * f τ) * conj (uhpDeriv f τ)) +
        (α * f τ) * conj (α * f τ) := by
      rw [map_mul]; ring
    rw [hexp, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
      Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq,
      norm_mul, mul_pow, hnorm_α]
    have hcross_sym : ((α * f τ) * conj (uhpDeriv f τ)).re =
        (uhpDeriv f τ * (conj α * conj (f τ))).re := by
      have hc : conj (uhpDeriv f τ * (conj α * conj (f τ))) = (α * f τ) * conj (uhpDeriv f τ) := by
        simp [mul_comm, mul_assoc]
      rw [← hc, Complex.conj_re]
    have hcross_val : (uhpDeriv f τ * (conj α * conj (f τ))).re =
        (k / (2 * τ.im)) * (Complex.I * uhpDeriv f τ * conj (f τ)).re := by
      rw [hα_conj]
      have hrearr : uhpDeriv f τ * (Complex.I * ((k / (2 * τ.im) : ℝ) : ℂ) * conj (f τ)) =
          ((k / (2 * τ.im) : ℝ) : ℂ) * (Complex.I * uhpDeriv f τ * conj (f τ)) := by ring
      rw [hrearr, Complex.re_ofReal_mul]
    rw [hcross_sym, hcross_val]
    ring
  have hrpow1 : τ.im ^ k / τ.im = τ.im ^ (k - 1) := by
    rw [Real.rpow_sub hy_pos, Real.rpow_one]
  have hrpow2 : τ.im ^ k / τ.im ^ 2 = τ.im ^ (k - 2) := by
    rw [Real.rpow_sub hy_pos, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold euclLaplacianR
  rw [hXX, hYY]
  have hsum_u : partialXXR u τ + partialYYR u τ = 4 * ‖uhpDeriv f τ‖ ^ 2 :=
    euclLaplacianR_norm_sq_holomorphic hf τ
  calc partialXXR u τ * τ.im ^ k +
        (partialYYR u τ * τ.im ^ k +
          2 * (2 * (Complex.I * uhpDeriv f τ * conj (f τ)).re) * (k * τ.im ^ (k - 1)) +
          ‖f τ‖ ^ 2 * (k * (k - 1) * τ.im ^ (k - 2)))
      = (partialXXR u τ + partialYYR u τ) * τ.im ^ k +
          4 * k * τ.im ^ (k - 1) * (Complex.I * uhpDeriv f τ * conj (f τ)).re +
          k * (k - 1) * τ.im ^ (k - 2) * ‖f τ‖ ^ 2 := by ring
    _ = 4 * τ.im ^ k * ‖uhpDeriv f τ‖ ^ 2 +
          4 * k * (τ.im ^ k / τ.im) * (Complex.I * uhpDeriv f τ * conj (f τ)).re +
          k * (k - 1) * (τ.im ^ k / τ.im ^ 2) * ‖f τ‖ ^ 2 := by
        rw [hsum_u, ← hrpow1, ← hrpow2]; ring
    _ = 4 * τ.im ^ k *
          (‖uhpDeriv f τ‖ ^ 2 + (k / τ.im) * (Complex.I * uhpDeriv f τ * conj (f τ)).re +
            (k / (2 * τ.im)) ^ 2 * ‖f τ‖ ^ 2) -
          k * (τ.im ^ k / τ.im ^ 2) * ‖f τ‖ ^ 2 := by
        field_simp [hy_pos.ne']; ring
    _ = 4 * τ.im ^ k * ‖uhpDeriv f τ + α * f τ‖ ^ 2 - k * τ.im ^ (k - 2) * ‖f τ‖ ^ 2 := by
        rw [← hboch_sq, hrpow2]

/-- Integer-weight specialization of `bochner_identity_weight_k` in terms of `automorphicNormSq`. -/
theorem bochner_identity_weight_k_int {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℤ) (τ : UpperHalfPlane) :
    euclLaplacianR (automorphicNormSq k f) τ =
      4 * τ.im ^ k * ‖uhpDeriv f τ + ((k : ℂ) / (2 * Complex.I * (τ.im : ℂ))) * f τ‖ ^ 2 -
        (k : ℝ) * τ.im ^ (k - 2) * ‖f τ‖ ^ 2 := by
  have hfun : automorphicNormSq k f = fun w : UpperHalfPlane => ‖f w‖ ^ 2 * w.im ^ (k : ℝ) := by
    funext w
    unfold automorphicNormSq automorphicMetric
    rw [Real.rpow_intCast]
  rw [hfun, bochner_identity_weight_k hf (k : ℝ) τ, Real.rpow_intCast, Complex.ofReal_intCast]
  have hsub : ((k : ℝ) - 2) = ((k - 2 : ℤ) : ℝ) := by push_cast; ring
  rw [hsub, Real.rpow_intCast]

/-- Continuity of `UpperHalfPlane.ofComplex` at any point of the open upper half-plane. -/
private lemma continuousAt_ofComplex_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    ContinuousAt UpperHalfPlane.ofComplex z :=
  UpperHalfPlane.ofComplex.continuousAt (by simpa [UpperHalfPlane.ofComplex] using hz)

/-- Second derivative test along a real slice: at a local maximum of `g`, `g''(a) ≤ 0`
(wired directly to `HermitianCurvatureCore.deriv_deriv_nonneg_of_isLocalMin`). -/
private lemma deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {a : ℝ}
    (hmax : IsLocalMax g a) (hc : ContinuousAt g a) :
    deriv (deriv g) a ≤ 0 := by
  have hmin : IsLocalMin (fun s : ℝ => -g (a + s)) 0 := by
    have hshift : IsLocalMax (fun s : ℝ => g (a + s)) 0 := by
      have hcont : ContinuousAt (fun s : ℝ => a + s) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have h0 : a + (0 : ℝ) = a := add_zero a
      exact IsLocalMax.comp_continuous (g := fun s : ℝ => a + s) (b := 0) (by rwa [h0]) hcont
    exact hshift.neg
  have hc' : ContinuousAt (fun s : ℝ => -g (a + s)) 0 := by
    have hcont : ContinuousAt (fun s : ℝ => a + s) 0 :=
      (continuous_const.add continuous_id).continuousAt
    exact (hc.comp_of_eq hcont (add_zero a)).neg
  have hnn := HermitianCurvatureCore.deriv_deriv_nonneg_of_isLocalMin hmin hc'
  have hneg : deriv (deriv fun s : ℝ => -g (a + s)) 0 = -deriv (deriv g) a := by
    have h1 : (deriv fun s : ℝ => -g (a + s)) = fun s : ℝ => -deriv g (a + s) := by
      funext s
      change deriv (-(fun t : ℝ => g (a + t))) s = -deriv g (a + s)
      rw [deriv.neg, deriv_comp_const_add]
    rw [h1]
    change deriv (-(fun s : ℝ => deriv g (a + s))) 0 = -deriv (deriv g) a
    rw [deriv.neg]
    simpa using congrArg Neg.neg (deriv_comp_const_add (deriv g) a 0)
  linarith

/-- At any local maximum `τ₀` of a continuous real function `φ` on `UpperHalfPlane`,
the Euclidean Laplacian satisfies `Δ_Eucl φ(τ₀) ≤ 0`. -/
theorem euclLaplacianR_nonpos_of_isLocalMax {φ : UpperHalfPlane → ℝ} {τ₀ : UpperHalfPlane}
    (hcont : ContinuousAt φ τ₀) (hmax : IsLocalMax φ τ₀) :
    euclLaplacianR φ τ₀ ≤ 0 := by
  have htau : ((τ₀.re : ℂ) + Complex.I * (τ₀.im : ℂ)) = (τ₀ : ℂ) := uhp_re_add_I_im τ₀
  have hmapX : ContinuousAt (fun x : ℝ => UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (τ₀.im : ℂ)))
      τ₀.re := by
    have hline : ContinuousAt (fun x : ℝ => (x : ℂ) + Complex.I * (τ₀.im : ℂ)) τ₀.re :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    exact (continuousAt_ofComplex_of_im_pos (by simpa [htau] using τ₀.im_pos)).comp hline
  have hmapY : ContinuousAt (fun y : ℝ => UpperHalfPlane.ofComplex ((τ₀.re : ℂ) + Complex.I * (y : ℂ)))
      τ₀.im := by
    have hline : ContinuousAt (fun y : ℝ => (τ₀.re : ℂ) + Complex.I * (y : ℂ)) τ₀.im :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt
    exact (continuousAt_ofComplex_of_im_pos (by simpa [htau] using τ₀.im_pos)).comp hline
  have hmaxX : IsLocalMax (uhpSliceXR φ τ₀.im) τ₀.re :=
    IsLocalMax.comp_continuous
      (g := fun x : ℝ => UpperHalfPlane.ofComplex ((x : ℂ) + Complex.I * (τ₀.im : ℂ)))
      (by rwa [ofComplex_self]) hmapX
  have hmaxY : IsLocalMax (uhpSliceYR φ τ₀.re) τ₀.im :=
    IsLocalMax.comp_continuous
      (g := fun y : ℝ => UpperHalfPlane.ofComplex ((τ₀.re : ℂ) + Complex.I * (y : ℂ)))
      (by rwa [ofComplex_self]) hmapY
  have hcX : ContinuousAt (uhpSliceXR φ τ₀.im) τ₀.re :=
    hcont.comp_of_eq hmapX (ofComplex_self τ₀)
  have hcY : ContinuousAt (uhpSliceYR φ τ₀.re) τ₀.im :=
    hcont.comp_of_eq hmapY (ofComplex_self τ₀)
  unfold euclLaplacianR partialXXR partialYYR
  linarith [deriv_deriv_nonpos_of_isLocalMax hmaxX hcX,
    deriv_deriv_nonpos_of_isLocalMax hmaxY hcY]

/-- **Local Bochner–Kodaira–Nakano Vanishing at a Maximum (`k < 0`)**:
if `f` is holomorphic on `UpperHalfPlane`, `k < 0`, and `τ ↦ |f(τ)|² y^k` attains a local
maximum at `τ₀`, then `f τ₀ = 0`. -/
theorem bochner_vanishing_of_isLocalMax {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {k : ℝ} (hk : k < 0) {τ₀ : UpperHalfPlane}
    (hmax : IsLocalMax (fun w : UpperHalfPlane => ‖f w‖ ^ 2 * w.im ^ k) τ₀) :
    f τ₀ = 0 := by
  have hf_cont : Continuous f := (hf.continuous)
  have hcont : ContinuousAt (fun w : UpperHalfPlane => ‖f w‖ ^ 2 * w.im ^ k) τ₀ := by
    have h1 : ContinuousAt (fun w : UpperHalfPlane => ‖f w‖ ^ 2) τ₀ :=
      (hf_cont.norm.pow 2).continuousAt
    have h2 : ContinuousAt (fun w : UpperHalfPlane => w.im ^ k) τ₀ :=
      UpperHalfPlane.continuous_im.continuousAt.rpow continuousAt_const (Or.inl τ₀.im_pos.ne')
    exact h1.mul h2
  have hlap_le : euclLaplacianR (fun w => ‖f w‖ ^ 2 * w.im ^ k) τ₀ ≤ 0 :=
    euclLaplacianR_nonpos_of_isLocalMax hcont hmax
  rw [bochner_identity_weight_k hf k τ₀] at hlap_le
  have hgrad_nn : 0 ≤ 4 * τ₀.im ^ k *
      ‖uhpDeriv f τ₀ + ((k : ℂ) / (2 * Complex.I * (τ₀.im : ℂ))) * f τ₀‖ ^ 2 := by
    have hpos : 0 < τ₀.im ^ k := Real.rpow_pos_of_pos τ₀.im_pos k
    positivity
  have hcurv_pos : 0 < (-k) * τ₀.im ^ (k - 2) :=
    mul_pos (neg_pos.mpr hk) (Real.rpow_pos_of_pos τ₀.im_pos (k - 2))
  have hnorm_le : (-k) * τ₀.im ^ (k - 2) * ‖f τ₀‖ ^ 2 ≤ 0 := by linarith
  have hsq_le : ‖f τ₀‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hnorm_le hcurv_pos
  have hsq_eq : ‖f τ₀‖ ^ 2 = 0 := le_antisymm hsq_le (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq_eq)

/-- **Global Bochner–Kodaira–Nakano Vanishing on `SL₂(ℤ) \ ℍ` (`k < 0`)**:
any holomorphic function `f : UpperHalfPlane → ℂ` whose weighted norm squared
`v(τ) = ‖f(τ)‖² · Im(τ)^k` is `SL₂(ℤ)`-invariant and vanishes at `i∞` must be identically zero
whenever `k < 0`. -/
theorem bochner_vanishing_sl2Z_of_weight_neg {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {k : ℝ} (hk : k < 0)
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k)
    (hvan : Tendsto (fun τ : UpperHalfPlane => ‖f τ‖ ^ 2 * τ.im ^ k)
      UpperHalfPlane.atImInfty (𝓝 0)) :
    ∀ τ : UpperHalfPlane, f τ = 0 := by
  set v : UpperHalfPlane → ℝ := fun τ => ‖f τ‖ ^ 2 * τ.im ^ k
  intro τ₁
  by_contra hne
  have hv1_pos : 0 < v τ₁ :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hne)) (Real.rpow_pos_of_pos τ₁.im_pos k)
  -- Choose `B ≥ 1` above which `v τ < v τ₁ / 2`.
  have hev := (Metric.tendsto_nhds.mp hvan) (v τ₁ / 2) (half_pos hv1_pos)
  rw [UpperHalfPlane.atImInfty_basis.eventually_iff] at hev
  obtain ⟨A, _, hA⟩ := hev
  set B : ℝ := max A 1
  have hB1 : 1 ≤ B := le_max_right A 1
  have hBA : A ≤ B := le_max_left A 1
  -- Compact box `K = [-1/2, 1/2] × [√3/2, B]` inside `{z : ℂ | 0 < z.im}`.
  let K : Set ℂ := Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) ×ℂ Set.Icc (Real.sqrt 3 / 2) B
  have hK_compact : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsqrt3_pos : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  have hsqrt3_le_one : Real.sqrt 3 / 2 ≤ 1 := by
    have h1 : Real.sqrt 3 ≤ 2 := by
      have : (3 : ℝ) ≤ 2 ^ 2 := by norm_num
      exact Real.sqrt_le_iff.mpr ⟨by norm_num, this⟩
    linarith
  have hK_nonempty : K.Nonempty :=
    ⟨Complex.I, ⟨by norm_num, by norm_num⟩, ⟨by simpa using hsqrt3_le_one, by simpa using hB1⟩⟩
  have hK_sub : K ⊆ {z : ℂ | 0 < z.im} := fun z hz => lt_of_lt_of_le hsqrt3_pos hz.2.1
  let g : ℂ → ℝ := fun z => v (UpperHalfPlane.ofComplex z)
  have hg_cont : ContinuousOn g K := by
    intro z hz
    have hzim : 0 < z.im := hK_sub hz
    have hofC : ContinuousAt UpperHalfPlane.ofComplex z := continuousAt_ofComplex_of_im_pos hzim
    have hv_cont : Continuous v := by
      have h1 : Continuous (fun w : UpperHalfPlane => ‖f w‖ ^ 2) := hf.continuous.norm.pow 2
      have h2 : Continuous (fun w : UpperHalfPlane => w.im ^ k) := by
        rw [continuous_iff_continuousAt]
        intro w
        exact UpperHalfPlane.continuous_im.continuousAt.rpow continuousAt_const
          (Or.inl w.im_pos.ne')
      exact h1.mul h2
    exact (hv_cont.continuousAt.comp hofC).continuousWithinAt
  obtain ⟨z₀, hz₀K, hz₀max⟩ := hK_compact.exists_isMaxOn hK_nonempty hg_cont
  let τ₀ : UpperHalfPlane := UpperHalfPlane.ofComplex z₀
  have hfd_im_ge : ∀ w : UpperHalfPlane, w ∈ ModularGroup.fd → Real.sqrt 3 / 2 ≤ w.im := by
    intro w hw
    have hre : |w.re| ≤ 1 / 2 := hw.2
    have hnorm : 1 ≤ Complex.normSq (w : ℂ) := hw.1
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
  have hv_tail : ∀ w : UpperHalfPlane, B ≤ w.im → v w < v τ₁ / 2 := by
    intro w hw
    have hd := hA (show w ∈ UpperHalfPlane.im ⁻¹' Set.Ici A from hBA.trans hw)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg w.im_pos.le k))] at hd
    exact hd
  -- Show `v τ₁ ≤ v τ₀` (so `v τ₀ > 0`).
  have hv1_le : v τ₁ ≤ v τ₀ := by
    obtain ⟨γ₁, hγ₁⟩ := ModularGroup.exists_smul_mem_fd τ₁
    set w₁ := γ₁ • τ₁
    have hw₁_eq : v w₁ = v τ₁ := hinv γ₁ τ₁
    have hw₁_ltB : w₁.im < B := by
      by_contra hge
      push Not at hge
      have hlt := hv_tail w₁ hge
      linarith
    have hw₁K : (w₁ : ℂ) ∈ K := ⟨abs_le.mp hγ₁.2, ⟨hfd_im_ge w₁ hγ₁, hw₁_ltB.le⟩⟩
    have hmax1 : g (w₁ : ℂ) ≤ g z₀ := hz₀max hw₁K
    have hgw1 : g (w₁ : ℂ) = v w₁ := by
      dsimp only [g]
      have hof : UpperHalfPlane.ofComplex (w₁ : ℂ) = w₁ :=
        UpperHalfPlane.ofComplex_apply_of_im_pos w₁.im_pos
      rw [hof]
    rw [hgw1, hw₁_eq] at hmax1
    exact hmax1
  -- Show `τ₀` is a global (hence local) maximum of `v` on `UpperHalfPlane`.
  have hglobal : ∀ τ : UpperHalfPlane, v τ ≤ v τ₀ := by
    intro τ
    obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd τ
    have hτ_eq : v (γ • τ) = v τ := hinv γ τ
    rw [← hτ_eq]
    set w := γ • τ
    by_cases hwB : w.im ≤ B
    · have hwK : (w : ℂ) ∈ K := ⟨abs_le.mp hγ.2, ⟨hfd_im_ge w hγ, hwB⟩⟩
      have hmaxw : g (w : ℂ) ≤ g z₀ := hz₀max hwK
      have hgw : g (w : ℂ) = v w := by
        dsimp only [g]
        have hof : UpperHalfPlane.ofComplex (w : ℂ) = w :=
          UpperHalfPlane.ofComplex_apply_of_im_pos w.im_pos
        rw [hof]
      rwa [hgw] at hmaxw
    · push Not at hwB
      have hlt := hv_tail w hwB.le
      linarith
  have hlocal : IsLocalMax v τ₀ := Filter.Eventually.of_forall hglobal
  have hf0 : f τ₀ = 0 := bochner_vanishing_of_isLocalMax hf hk hlocal
  have hv0 : v τ₀ = 0 := by simp [v, hf0]
  linarith

/-- **Bochner–Kodaira–Nakano Vanishing for Negative-Weight Modular Forms (`k < 0`)**:
every level-1 modular form `f ∈ M_k(SL₂(ℤ))` of strictly negative weight `k < 0` is
identically zero, proved directly via the Bochner–Weitzenböck identity and maximum principle. -/
theorem modularForm_eq_zero_of_weight_neg {k : ℤ} (hk : k < 0) (f : ModularForm SL2ZRange k) :
    f = 0 := by
  have hkR : (k : ℝ) < 0 := Int.cast_lt_zero.mpr hk
  have hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ (k : ℝ) = ‖f τ‖ ^ 2 * τ.im ^ (k : ℝ) := by
    intro γ τ
    have h := automorphicNormSq_modularForm_sl2Z_invariant f γ τ
    unfold automorphicNormSq automorphicMetric at h
    simpa only [Real.rpow_intCast] using h
  have hvan : Tendsto (fun τ : UpperHalfPlane => ‖f τ‖ ^ 2 * τ.im ^ (k : ℝ))
      UpperHalfPlane.atImInfty (𝓝 0) := by
    rcases ModularFormClass.exp_decay_sub_atImInfty' f with ⟨c, hc, hO⟩
    have hneg : Tendsto (fun t : ℝ => -c * t) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hc) tendsto_id
    have hexp0 : Tendsto (fun τ : UpperHalfPlane => Real.exp (-c * τ.im))
        UpperHalfPlane.atImInfty (𝓝 0) :=
      (Real.tendsto_exp_atBot.comp hneg).comp Filter.tendsto_comap
    have hsub0 : Tendsto (fun τ : UpperHalfPlane => f τ - UpperHalfPlane.valueAtInfty (f : UpperHalfPlane → ℂ))
        UpperHalfPlane.atImInfty (𝓝 0) := hO.trans_tendsto hexp0
    have hf_lim : Tendsto (fun τ : UpperHalfPlane => f τ) UpperHalfPlane.atImInfty
        (𝓝 (UpperHalfPlane.valueAtInfty (f : UpperHalfPlane → ℂ))) := by
      simpa using hsub0.add_const (UpperHalfPlane.valueAtInfty (f : UpperHalfPlane → ℂ))
    have hnorm_lim : Tendsto (fun τ : UpperHalfPlane => ‖f τ‖ ^ 2) UpperHalfPlane.atImInfty
        (𝓝 (‖UpperHalfPlane.valueAtInfty (f : UpperHalfPlane → ℂ)‖ ^ 2)) :=
      (hf_lim.norm).pow 2
    have hpow_lim : Tendsto (fun τ : UpperHalfPlane => τ.im ^ (k : ℝ))
        UpperHalfPlane.atImInfty (𝓝 0) := by
      have hr : Tendsto (fun t : ℝ => t ^ (-(-(k : ℝ)))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (neg_pos.mpr hkR)
      simp only [neg_neg] at hr
      exact hr.comp Filter.tendsto_comap
    simpa [mul_zero] using hnorm_lim.mul hpow_lim
  ext τ
  exact bochner_vanishing_sl2Z_of_weight_neg f.holo' hkR hinv hvan τ

/-- **Bochner–Kodaira–Nakano Vanishing for Negative-Weight Cusp Forms (`k < 0`)**:
every level-1 cusp form `f ∈ S_k(SL₂(ℤ))` of strictly negative weight `k < 0` is
identically zero. -/
theorem cuspForm_eq_zero_of_weight_neg {k : ℤ} (hk : k < 0) (f : CuspForm SL2ZRange k) :
    f = 0 := by
  have hmod : (f : ModularForm SL2ZRange k) = 0 :=
    modularForm_eq_zero_of_weight_neg hk (f : ModularForm SL2ZRange k)
  ext τ
  exact congrFun (congrArg DFunLike.coe hmod) τ

end BochnerVanishing

end

end RHDirect.Stage11HermitianCurvature
