import RHDirect.Stage11HermitianCurvature
import RHDirect.Stage11ArakelovFaltings
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# RHDirect.Stage14M3_HermitianLineBundles

**FIELD-2 PACKAGE M3 (WAVE 1) — UNCONDITIONAL CONCRETE HERMITIAN LINE BUNDLES, CHERN FIRST
FORMS, CURVATURE POSITIVITY / SEMINEGATIVITY, THETA & PETERSSON METRIC POSITIVITY, AND THE
DISTRIBUTIONAL POINCARÉ–LELONG EQUATION** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom
`axiom`s, `0` `opaque`, `0` `native_decide`).

Distills the genuine Hermitian differential geometry of Pillar 5
(`Formalism.HermitianCurvature.*`, `Development.AbelianVarietyTheory.Definitions.ThetaMetrics.*`,
`Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms`, and
`ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenPolar`) into a single cohesive,
unconditionally proved module directly feeding M3 Wave 2 (`HodgeBundleExtension`,
`ArakelovIntersection`, `ChowFormHeights`, `GagaAndSections`, `NefRiemannRoch`).

## Main Exported Types & Theorems

1. **Hermitian `(1, 1)`-Forms, Complex Hessian (`leviForm`), Pluriharmonicity & Griffiths
   Curvature**:
   - `HermitianCurvatureForm`: real-valued Hermitian `(1, 1)`-quadratic forms on `X ⊆ ℂ^d`,
     with `Zero`/`Add`/`Neg`/`Sub`/`SMul ℝ`, positivity predicates (`IsSemipositive`,
     `IsStrictlyPositive`, `IsUniformlyPositive`, `IsSeminegative`, `IsStrictlyNegative`),
     `ofPotential`, and `ofHermMatrix`.
   - `leviForm_smul_complex`, `leviForm_parallelogram`, `leviForm_comp_clm`.
   - `leviForm_norm_sq_holomorphic`: `leviForm (‖f ·‖²) z w = ‖fderiv ℂ f z w‖²`.
   - `leviForm_log_norm_sq_holomorphic`: exact pluriharmonicity `leviForm (log ‖f ·‖²) z w = 0`
     away from zeros of holomorphic `f` in arbitrary dimension `d`.
   - `leviForm_log_sum_norm_sq_nonneg`: Cauchy–Schwarz / Fubini–Study / Griffiths curvature
     positivity for `log (∑_k ‖f_k‖²)` and seminegativity for `-log (∑_k ‖f_k‖²)`.

2. **Concrete `MetrizedLineBundle`, `ChernFirstForm`, `SeminegativeMetric`, &
   `PosCurvatureMetric`**:
   - `MetrizedLineBundle d ι X`: holomorphic trivializing open cover with nonvanishing transition
     cocycle `g_{ij}` and `C²` local metric weights `φ_i = -log h_i` satisfying
     `φ_i - φ_j = log (‖g_{ij}‖²)`.
   - Chart-independent curvature `curvatureAt_eq_of_mem`, `curvatureForm`, and
     `ChernFirstForm L := (1 / π) • L.curvatureForm`.
   - Functorial operations `trivial`, `dual`, `tensor`, `pow`, `twistMetric`, `scaleMetric`,
     `lerpMetric`, with exact Chern–Weil formulas (`chernFirstForm_dual`, `chernFirstForm_tensor`,
     `chernFirstForm_pow`, `chernFirstForm_twistMetric`).
   - Holomorphic `Section L` with chart-independent Hermitian norm squared `ptNormSq` and
     pointwise Poincaré–Lelong away from zeros (`Section.leviForm_log_ptNormSq_eq_neg_curvature`).
   - `SemipositiveMetric`, `PosCurvatureMetric`, `SeminegativeMetric`, `NegCurvatureMetric`,
     duality & cone closure, `fubiniStudy_posCurvature`, and `subbundle_metric_seminegative`.

3. **Theta, Siegel & Petersson Hermitian Metrics (`theta_metric_positivity`)**:
   - `IsSiegelPeriodMatrix`, `thetaWeight`, `thetaMetrizedLineBundle`: canonical theta Hermitian
     metric `h_Θ(z) = exp(-2π (Im z)^T (Im Ω)⁻¹ (Im z))` on `ℂ^g` in arbitrary genus `g ≥ 1`.
   - `thetaWeight_real_coords`: exact match `2π y^T (Im Ω) y` along `z = x + Ω y`.
   - `thetaWeight_leviForm_eq`, `thetaLineBundle_chernFirstForm_eq`,
     **`theta_metric_positivity`** (`PosCurvatureMetric (thetaMetrizedLineBundle Ω)`), and
     `theta_metric_uniform_positivity`.
   - `peterssonLineBundle k` on `UpperHalfPlane` matching `Stage11HermitianCurvature` verbatim:
     `petersson_metric_positivity` (`k > 0`), `petersson_metric_semipositive` (`k ≥ 0`),
     `petersson_metric_seminegative` (`k ≤ 0`), `petersson_degree_matches_stage11`.

4. **Exact Green's Formula & Distributional `poincare_lelong_equation`**:
   - `laplacianC`, `ddcDens`, `greens_second_identity_complex` (valid for `ContDiffOn ℝ 2 φ U`
     on any open `U ⊇ tsupport u`!).
   - `green_fundamental_solution`: exact polar integration-by-parts proof of
     `∫ z : ℂ, log ‖z - a‖ * laplacianC u z = 2π u(a)`.
   - **`poincare_lelong_equation`**: for any open `U ⊆ ℂ`, smooth weight `φ` on `U`, finite
     divisor `∑_{i ∈ s} m_i [a_i]`, nonvanishing holomorphic unit `g` on `U`, and `C²` test
     function `u` with `tsupport u ⊆ U`:
     $$\int_{\mathbb{C}} \log\!\bigl(\|f(z)\|^2 e^{-\varphi(z)}\bigr) \, \mathrm{dd}^c u(z)
       = \sum_{i \in s} m_i\, u(a_i) - \int_{\mathbb{C}} c_1(\varphi)(z)\, u(z).$$
   - `poincare_lelong_metrized_bundle`, `poincare_lelong_metric_change`, and higher-dimensional
     coordinate-hyperplane `poincare_lelong_coord_hyperplane`.

5. **Direct Bridges to `Stage11HermitianCurvature`, `Stage11ArakelovFaltings`, & M3 Wave 2**.
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function Set Topology
open RHDirect.HermitianCurvatureCore RHDirect.Stage10PeterssonHecke
open RHDirect.Stage11HermitianCurvature RHDirect.Stage11ArakelovFaltings
open scoped BigOperators UpperHalfPlane ComplexConjugate ComplexOrder ENNReal Classical
open intervalIntegral

namespace RHDirect.Stage14M3_HermitianLineBundles

noncomputable section

/-! ## Section 1: Hermitian `(1, 1)`-Forms, Complex Hessian (`leviForm`), & Pluriharmonicity -/

section ComplexHessianAlgebra

/-- Local congruence of `HermitianCurvatureCore.leviForm` under eventual equality near `z`. -/
theorem leviForm_congr_of_eventuallyEq {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (h : φ =ᶠ[𝓝 z] ψ) (w : J → ℂ) :
    leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := h.eventuallyEq_nhds.mono fun _ hy => hy.fderiv_eq
  have h2 : fderiv ℝ (fderiv ℝ φ) z = fderiv ℝ (fderiv ℝ ψ) z := h1.fderiv_eq
  unfold leviForm
  rw [h2]

/-- Negation of `leviForm` for a `C²` weight. -/
theorem leviForm_neg {J : Type*} [Fintype J] {φ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (w : J → ℂ) :
    leviForm (fun y => -φ y) z w = -leviForm φ z w := by
  have heq : (fun y => -φ y) = fun y => (-1 : ℝ) * φ y + (0 : ℝ) * φ y := by
    funext y; ring
  rw [heq, leviForm_add_smul (-1) 0 hφ hφ w]
  ring

/-- Scalar multiplication of `leviForm` for a `C²` weight. -/
theorem leviForm_const_mul {J : Type*} [Fintype J] (a : ℝ) {φ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (w : J → ℂ) :
    leviForm (fun y => a * φ y) z w = a * leviForm φ z w := by
  have heq : (fun y => a * φ y) = fun y => a * φ y + (0 : ℝ) * φ y := by
    funext y; ring
  rw [heq, leviForm_add_smul a 0 hφ hφ w]
  ring

/-- Additivity of `leviForm` for `C²` weights. -/
theorem leviForm_add {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) (w : J → ℂ) :
    leviForm (fun y => φ y + ψ y) z w = leviForm φ z w + leviForm ψ z w := by
  have heq : (fun y => φ y + ψ y) = fun y => 1 * φ y + 1 * ψ y := by
    funext y; ring
  rw [heq, leviForm_add_smul 1 1 hφ hψ w]
  ring

/-- Subtraction of `leviForm` for `C²` weights. -/
theorem leviForm_sub {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) (w : J → ℂ) :
    leviForm (fun y => φ y - ψ y) z w = leviForm φ z w - leviForm ψ z w := by
  have heq : (fun y => φ y - ψ y) = fun y => 1 * φ y + (-1) * ψ y := by
    funext y; ring
  rw [heq, leviForm_add_smul 1 (-1) hφ hψ w]
  ring

/-- `leviForm` vanishes identically for the zero weight. -/
theorem leviForm_zero {J : Type*} [Fintype J] (z w : J → ℂ) :
    leviForm (fun _ : J → ℂ => (0 : ℝ)) z w = 0 :=
  leviForm_const 0 z w

/-- **Complex Quadratic Homogeneity of the Levi Form**:
for ANY function `φ : (J → ℂ) → ℝ`, any basepoint `z`, any `c : ℂ`, and any tangent `w`,
`leviForm φ z (c • w) = ‖c‖ ^ 2 * leviForm φ z w`. -/
theorem leviForm_smul_complex {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (z : J → ℂ)
    (c : ℂ) (w : J → ℂ) :
    leviForm φ z (c • w) = ‖c‖ ^ 2 * leviForm φ z w := by
  set a : ℝ := c.re
  set b : ℝ := c.im
  set B := fderiv ℝ (fderiv ℝ φ) z
  have hcw : c • w = a • w + b • (Complex.I • w) := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, Complex.real_smul, smul_eq_mul, a, b]
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_lhs => rw [hc]
    ring
  have hIcw : Complex.I • (c • w) = (-b) • w + a • (Complex.I • w) := by
    ext j
    simp only [Pi.smul_apply, Pi.add_apply, Complex.real_smul, smul_eq_mul, a, b]
    have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := (Complex.re_add_im c).symm
    conv_lhs => rw [hc]
    push_cast
    linear_combination (c.im : ℂ) * w j * Complex.I_sq
  have hBl_add : ∀ x y u, B (x + y) u = B x u + B y u := fun x y u => by rw [map_add]; rfl
  have hBl_smul : ∀ (r : ℝ) x u, B (r • x) u = r * B x u := fun r x u => by rw [map_smul]; rfl
  have hBr_add : ∀ x y u, B x (y + u) = B x y + B x u := fun x y u => map_add (B x) y u
  have hBr_smul : ∀ (r : ℝ) x u, B x (r • u) = r * B x u := fun r x u => by
    rw [map_smul, smul_eq_mul]
  have h1 : B (c • w) (c • w) =
      a * a * B w w + a * b * B w (Complex.I • w) + b * a * B (Complex.I • w) w +
        b * b * B (Complex.I • w) (Complex.I • w) := by
    rw [hcw, hBl_add, hBl_smul, hBl_smul, hBr_add, hBr_add, hBr_smul, hBr_smul, hBr_smul, hBr_smul]
    ring
  have h2 : B (Complex.I • (c • w)) (Complex.I • (c • w)) =
      b * b * B w w - b * a * B w (Complex.I • w) - a * b * B (Complex.I • w) w +
        a * a * B (Complex.I • w) (Complex.I • w) := by
    rw [hIcw, hBl_add, hBl_smul, hBl_smul, hBr_add, hBr_add, hBr_smul, hBr_smul, hBr_smul, hBr_smul]
    ring
  have hnorm : a ^ 2 + b ^ 2 = ‖c‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
  unfold leviForm
  change (B (c • w) (c • w) + B (Complex.I • (c • w)) (Complex.I • (c • w))) / 4 =
    ‖c‖ ^ 2 * ((B w w + B (Complex.I • w) (Complex.I • w)) / 4)
  rw [h1, h2, ← hnorm]
  ring

/-- **Parallelogram Identity for the Levi Form**:
`leviForm φ z (u + v) + leviForm φ z (u - v) = 2 * leviForm φ z u + 2 * leviForm φ z v`. -/
theorem leviForm_parallelogram {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (z u v : J → ℂ) :
    leviForm φ z (u + v) + leviForm φ z (u - v) = 2 * leviForm φ z u + 2 * leviForm φ z v := by
  set B := fderiv ℝ (fderiv ℝ φ) z
  have hpara : ∀ x y : J → ℂ, B (x + y) (x + y) + B (x - y) (x - y) = 2 * B x x + 2 * B y y := by
    intro x y
    have h1 : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
      simp only [map_add, _root_.add_apply]; ring
    have h2 : B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
      simp only [map_sub, _root_.sub_apply]; ring
    linarith
  unfold leviForm
  change (B (u + v) (u + v) + B (Complex.I • (u + v)) (Complex.I • (u + v))) / 4 +
      (B (u - v) (u - v) + B (Complex.I • (u - v)) (Complex.I • (u - v))) / 4 =
    2 * ((B u u + B (Complex.I • u) (Complex.I • u)) / 4) +
      2 * ((B v v + B (Complex.I • v) (Complex.I • v)) / 4)
  rw [smul_add, smul_sub]
  linarith [hpara u v, hpara (Complex.I • u) (Complex.I • v)]

/-- `leviForm φ z 0 = 0`. -/
theorem leviForm_zero_dir {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (z : J → ℂ) :
    leviForm φ z 0 = 0 := by
  have h := leviForm_smul_complex φ z 0 0
  simpa using h

/-- **Chain Rule for `leviForm` under a `ℂ`-Linear Map**:
if `T : (J₁ → ℂ) →L[ℂ] (J₂ → ℂ)` is `ℂ`-linear and `φ` is `C²` at `T z`, then
`leviForm (φ ∘ T) z w = leviForm φ (T z) (T w)`. -/
theorem leviForm_comp_clm {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (T : (J₁ → ℂ) →L[ℂ] (J₂ → ℂ)) {φ : (J₂ → ℂ) → ℝ} {z : J₁ → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (T z)) (w : J₁ → ℂ) :
    leviForm (fun y => φ (T y)) z w = leviForm φ (T z) (T w) := by
  have hT_cont : ContDiff ℝ 2 (T : (J₁ → ℂ) → (J₂ → ℂ)) :=
    (T.restrictScalars ℝ).contDiff
  have hcomp : ContDiffAt ℝ 2 (fun y => φ (T y)) z := hφ.comp z hT_cont.contDiffAt
  have hline : ∀ e : J₁ → ℂ,
      fderiv ℝ (fderiv ℝ (fun y => φ (T y))) z e e = fderiv ℝ (fderiv ℝ φ) (T z) (T e) (T e) := by
    intro e
    rw [← deriv_deriv_line hcomp e, ← deriv_deriv_line hφ (T e)]
    have hfun : (fun s : ℝ => φ (T (z + s • e))) = fun s : ℝ => φ (T z + s • T e) := by
      funext s
      have hsmul : T (s • e) = s • T e := (T.restrictScalars ℝ).map_smul s e
      rw [map_add, hsmul]
    rw [hfun]
  unfold leviForm
  rw [hline w, hline (Complex.I • w), map_smul]

/-! ### Exact Holomorphic Directional Derivatives, Pluriharmonicity & Griffiths Positivity -/

/-- Directional first derivative of a `C²` holomorphic function along a real line `s ↦ z + s • e`. -/
private lemma hasDerivAt_holo_line {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (e : J → ℂ) :
    HasDerivAt (fun s : ℝ => f (z + s • e)) (fderiv ℂ f z e) 0 := by
  have hline : HasDerivAt (fun s : ℝ => z + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hfd : HasFDerivAt f ((fderiv ℂ f z).restrictScalars ℝ) z :=
    ((hf.differentiableAt (by norm_num)).hasFDerivAt).restrictScalars ℝ
  have h0 : z + (0 : ℝ) • e = z := by simp
  exact hfd.comp_hasDerivAt_of_eq 0 hline h0.symm

/-- Directional second derivative of a `C²` holomorphic function along a real line `s ↦ z + s • e`. -/
private lemma hasDerivAt_holo_line_snd {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (e : J → ℂ) :
    HasDerivAt (fun s : ℝ => fderiv ℂ f (z + s • e) e) (fderiv ℂ (fderiv ℂ f) z e e) 0 := by
  have hline : HasDerivAt (fun s : ℝ => z + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hf1 : DifferentiableAt ℂ (fderiv ℂ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfd : HasFDerivAt (fun y => fderiv ℂ f y e)
      (((fderiv ℂ (fderiv ℂ f) z).flip e).restrictScalars ℝ) z := by
    have h := hf1.hasFDerivAt.clm_apply (hasFDerivAt_const e z)
    exact (by simpa using h : HasFDerivAt (fun y => fderiv ℂ f y e)
      ((fderiv ℂ (fderiv ℂ f) z).flip e) z).restrictScalars ℝ
  have h0 : z + (0 : ℝ) • e = z := by simp
  exact hfd.comp_hasDerivAt_of_eq 0 hline h0.symm

/-- Real-analytic first derivative of `s ↦ ‖g s‖²` along a complex curve `g : ℝ → ℂ`. -/
private lemma hasDerivAt_norm_sq_real {g : ℝ → ℂ} {g' : ℂ} {t : ℝ}
    (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s : ℝ => ‖g s‖ ^ 2) (2 * (g' * conj (g t)).re) t := by
  have heq : (fun s : ℝ => ‖g s‖ ^ 2) = fun s : ℝ => (g s * conj (g s)).re := by
    funext s
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [heq]
  have hconj : HasDerivAt (fun s : ℝ => conj (g s)) (conj g') t :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt t hg
  have hmul := hg.mul hconj
  have hre : HasDerivAt (fun s : ℝ => (g s * conj (g s)).re)
      (g' * conj (g t) + g t * conj g').re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hmul
  have hval : (g' * conj (g t) + g t * conj g').re = 2 * (g' * conj (g t)).re := by
    rw [Complex.add_re]
    have hsym : (g t * conj g').re = (g' * conj (g t)).re := by
      have hc : conj (g' * conj (g t)) = g t * conj g' := by simp [mul_comm]
      rw [← hc, Complex.conj_re]
    linarith
  rwa [hval] at hre

/-- First and second directional derivatives of `s ↦ ‖f (z + s • e)‖²` at `s = 0` for `C²`
holomorphic `f`. -/
private lemma hasDerivAt_norm_sq_holo_line {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (e : J → ℂ) :
    HasDerivAt (fun s : ℝ => ‖f (z + s • e)‖ ^ 2) (2 * (fderiv ℂ f z e * conj (f z)).re) 0 ∧
    HasDerivAt (deriv fun s : ℝ => ‖f (z + s • e)‖ ^ 2)
      (2 * (fderiv ℂ (fderiv ℂ f) z e e * conj (f z)).re + 2 * ‖fderiv ℂ f z e‖ ^ 2) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => ‖f (z + s • e)‖ ^ 2)
      (2 * (fderiv ℂ f z e * conj (f z)).re) 0 := by
    have h := hasDerivAt_norm_sq_real (hasDerivAt_holo_line hf e)
    simpa using h
  refine ⟨h1, ?_⟩
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous (fun s : ℝ => z + s • e) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℂ 2 f y := hf.eventually (by simp)
  have hd1 : deriv (fun s : ℝ => ‖f (z + s • e)‖ ^ 2) =ᶠ[𝓝 (0 : ℝ)]
      fun s : ℝ => 2 * (fderiv ℂ f (z + s • e) e * conj (f (z + s • e))).re := by
    filter_upwards [hcont.eventually hfe] with s hs
    have hline : HasDerivAt (fun t : ℝ => z + t • e) e s := by
      simpa using ((hasDerivAt_id s).smul_const e).const_add z
    have hfd : HasFDerivAt f ((fderiv ℂ f (z + s • e)).restrictScalars ℝ) (z + s • e) :=
      ((hs.differentiableAt (by norm_num)).hasFDerivAt).restrictScalars ℝ
    exact (hasDerivAt_norm_sq_real (hfd.comp_hasDerivAt s hline)).deriv
  refine HasDerivAt.congr_of_eventuallyEq ?_ hd1
  have hg1 := hasDerivAt_holo_line_snd hf e
  have hg2 : HasDerivAt (fun s : ℝ => conj (f (z + s • e))) (conj (fderiv ℂ f z e)) 0 :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_holo_line hf e)
  have hre : HasDerivAt
      (fun s : ℝ => 2 * (fderiv ℂ f (z + s • e) e * conj (f (z + s • e))).re)
      (2 * (fderiv ℂ (fderiv ℂ f) z e e * conj (f (z + (0 : ℝ) • e)) +
        fderiv ℂ f (z + (0 : ℝ) • e) e * conj (fderiv ℂ f z e)).re) 0 :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hg1.mul hg2)).const_mul (2 : ℝ)
  refine hre.congr_deriv ?_
  simp only [zero_smul, add_zero, Complex.add_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  ring

/-- `ContDiffAt ℝ 2` for `y ↦ ‖f y‖²` whenever `f` is `ContDiffAt ℂ 2`. -/
lemma contDiffAt_norm_sq_of_holo {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) :
    ContDiffAt ℝ 2 (fun y => ‖f y‖ ^ 2) z := by
  have hfR : ContDiffAt ℝ 2 f z := hf.restrict_scalars ℝ
  have heq : (fun y => ‖f y‖ ^ 2) = fun y => (f y * conj (f y)).re := by
    funext y
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [heq]
  exact Complex.reCLM.contDiff.contDiffAt.comp z
    (hfR.mul (Complex.conjCLE.contDiff.contDiffAt.comp z hfR))

/-- **Exact Complex Hessian of `‖f‖²` for Holomorphic `f` in Arbitrary Dimension `d`**:
$$\operatorname{leviForm}(\|f\|^2)(z, w) = \|df_z(w)\|^2.$$ -/
theorem leviForm_norm_sq_holomorphic {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (w : J → ℂ) :
    leviForm (fun y => ‖f y‖ ^ 2) z w = ‖fderiv ℂ f z w‖ ^ 2 := by
  have hns : ContDiffAt ℝ 2 (fun y => ‖f y‖ ^ 2) z := contDiffAt_norm_sq_of_holo hf
  have h1 := (hasDerivAt_norm_sq_holo_line hf w).2.deriv
  have h2 := (hasDerivAt_norm_sq_holo_line hf (Complex.I • w)).2.deriv
  have hI1 : fderiv ℂ f z (Complex.I • w) = Complex.I * fderiv ℂ f z w := by
    rw [map_smul, smul_eq_mul]
  have hI2 : fderiv ℂ (fderiv ℂ f) z (Complex.I • w) (Complex.I • w) =
      -fderiv ℂ (fderiv ℂ f) z w w := by
    rw [map_smul, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, Complex.I_mul_I]
    ring
  rw [hI1, hI2, norm_mul, Complex.norm_I, one_mul, neg_mul, Complex.neg_re] at h2
  unfold leviForm
  rw [← deriv_deriv_line hns w, ← deriv_deriv_line hns (Complex.I • w), h1, h2]
  ring

/-- **Pluriharmonicity of `Re f` for Holomorphic `f` in Arbitrary Dimension `d`**:
`leviForm (fun y => (f y).re) z w = 0`. -/
theorem leviForm_re_holomorphic {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (w : J → ℂ) :
    leviForm (fun y => (f y).re) z w = 0 := by
  have hre : ContDiffAt ℝ 2 (fun y => (f y).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z (hf.restrict_scalars ℝ)
  have hline : ∀ e : J → ℂ,
      deriv (deriv fun s : ℝ => (f (z + s • e)).re) 0 = (fderiv ℂ (fderiv ℂ f) z e e).re := by
    intro e
    have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 (0 : ℝ)) (𝓝 z) := by
      have hc : Continuous (fun s : ℝ => z + s • e) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℂ 2 f y := hf.eventually (by simp)
    have hd1 : deriv (fun s : ℝ => (f (z + s • e)).re) =ᶠ[𝓝 (0 : ℝ)]
        fun s : ℝ => (fderiv ℂ f (z + s • e) e).re := by
      filter_upwards [hcont.eventually hfe] with s hs
      have hl : HasDerivAt (fun t : ℝ => z + t • e) e s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_add z
      have hfd : HasFDerivAt f ((fderiv ℂ f (z + s • e)).restrictScalars ℝ) (z + s • e) :=
        ((hs.differentiableAt (by norm_num)).hasFDerivAt).restrictScalars ℝ
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (hfd.comp_hasDerivAt s hl)).deriv
    rw [hd1.deriv_eq]
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_holo_line_snd hf e)).deriv
  have hI2 : fderiv ℂ (fderiv ℂ f) z (Complex.I • w) (Complex.I • w) =
      -fderiv ℂ (fderiv ℂ f) z w w := by
    rw [map_smul, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, Complex.I_mul_I]
    ring
  unfold leviForm
  rw [← deriv_deriv_line hre w, ← deriv_deriv_line hre (Complex.I • w),
    hline w, hline (Complex.I • w), hI2, Complex.neg_re]
  ring

/-- Helper: second derivative of `s ↦ Real.log (u s)` at `0` for `u` positive and `C²` at `0`. -/
private lemma deriv_deriv_log_at_zero {u : ℝ → ℝ} {u' u'' : ℝ} (hu_pos : 0 < u 0)
    (hu_ev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < u s ∧ DifferentiableAt ℝ u s)
    (hu1 : HasDerivAt u u' 0) (hu2 : HasDerivAt (deriv u) u'' 0) :
    deriv (deriv fun s : ℝ => Real.log (u s)) 0 = (u'' * u 0 - u' ^ 2) / (u 0) ^ 2 := by
  have hd1 : deriv (fun s : ℝ => Real.log (u s)) =ᶠ[𝓝 (0 : ℝ)] fun s : ℝ => deriv u s / u s := by
    filter_upwards [hu_ev] with s hs
    exact (hs.2.hasDerivAt.log hs.1.ne').deriv
  rw [hd1.deriv_eq]
  have hd2 : HasDerivAt (fun s : ℝ => deriv u s / u s) ((u'' * u 0 - deriv u 0 * u') / (u 0) ^ 2) 0 :=
    hu2.div hu1 hu_pos.ne'
  rw [hd2.deriv, hu1.deriv]
  ring

/-- **Exact Griffiths / Fubini–Study Complex Hessian Formula for `log (∑_k ‖f_k‖²)`**:
for any finite tuple of `C²` holomorphic functions `f : Fin r → (J → ℂ) → ℂ` not all vanishing at `z`,
$$\operatorname{leviForm}\!\left(\log \sum_k \|f_k\|^2\right)(z, w)
  = \frac{\left(\sum_k \|f_k(z)\|^2\right)\left(\sum_k \|df_{k,z}(w)\|^2\right)
    - \left\|\sum_k df_{k,z}(w)\,\overline{f_k(z)}\right\|^2}{\left(\sum_k \|f_k(z)\|^2\right)^2}.$$ -/
theorem leviForm_log_sum_norm_sq_eq {J : Type*} [Fintype J] {r : ℕ}
    (f : Fin r → (J → ℂ) → ℂ) {z : J → ℂ} (hf : ∀ k, ContDiffAt ℂ 2 (f k) z)
    (hpos : 0 < ∑ k : Fin r, ‖f k z‖ ^ 2) (w : J → ℂ) :
    leviForm (fun y => Real.log (∑ k : Fin r, ‖f k y‖ ^ 2)) z w =
      ((∑ k : Fin r, ‖f k z‖ ^ 2) * (∑ k : Fin r, ‖fderiv ℂ (f k) z w‖ ^ 2) -
        ‖∑ k : Fin r, fderiv ℂ (f k) z w * conj (f k z)‖ ^ 2) /
        (∑ k : Fin r, ‖f k z‖ ^ 2) ^ 2 := by
  set S : (J → ℂ) → ℝ := fun y => ∑ k : Fin r, ‖f k y‖ ^ 2
  have hS_cd : ContDiffAt ℝ 2 S z :=
    ContDiffAt.sum fun k _ => contDiffAt_norm_sq_of_holo (hf k)
  have hlog_cd : ContDiffAt ℝ 2 (fun y => Real.log (S y)) z := hS_cd.log hpos.ne'
  have hline_log : ∀ e : J → ℂ,
      deriv (deriv fun s : ℝ => Real.log (S (z + s • e))) 0 =
        ((2 * (∑ k : Fin r, (fderiv ℂ (fderiv ℂ (f k)) z e e * conj (f k z)).re) +
            2 * ∑ k : Fin r, ‖fderiv ℂ (f k) z e‖ ^ 2) * S z -
          (2 * (∑ k : Fin r, fderiv ℂ (f k) z e * conj (f k z)).re) ^ 2) / (S z) ^ 2 := by
    intro e
    set u : ℝ → ℝ := fun s => S (z + s • e)
    have hu0 : u 0 = S z := by simp [u]
    have hu1 : HasDerivAt u (2 * (∑ k : Fin r, fderiv ℂ (f k) z e * conj (f k z)).re) 0 := by
      have hsum : HasDerivAt (fun s : ℝ => ∑ k : Fin r, ‖f k (z + s • e)‖ ^ 2)
          (∑ k : Fin r, 2 * (fderiv ℂ (f k) z e * conj (f k z)).re) 0 :=
        HasDerivAt.fun_sum fun k _ => (hasDerivAt_norm_sq_holo_line (hf k) e).1
      refine hsum.congr_deriv ?_
      rw [← Finset.mul_sum, Complex.re_sum]
    have hu2 : HasDerivAt (deriv u)
        (2 * (∑ k : Fin r, (fderiv ℂ (fderiv ℂ (f k)) z e e * conj (f k z)).re) +
          2 * ∑ k : Fin r, ‖fderiv ℂ (f k) z e‖ ^ 2) 0 := by
      have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 (0 : ℝ)) (𝓝 z) := by
        have hc : Continuous (fun s : ℝ => z + s • e) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
      have hfe : ∀ᶠ y in 𝓝 z, ∀ k : Fin r, ContDiffAt ℂ 2 (f k) y :=
        Filter.eventually_all.mpr fun k => (hf k).eventually (by simp)
      have hd_eq : deriv u =ᶠ[𝓝 (0 : ℝ)]
          fun s : ℝ => ∑ k : Fin r, deriv (fun t : ℝ => ‖f k (z + t • e)‖ ^ 2) s := by
        filter_upwards [hcont.eventually hfe] with s hs
        have hd_k : ∀ k : Fin r, DifferentiableAt ℝ (fun t : ℝ => ‖f k (z + t • e)‖ ^ 2) s := by
          intro k
          have h1 : ContDiffAt ℝ 2 (fun y => ‖f k y‖ ^ 2) (z + s • e) :=
            contDiffAt_norm_sq_of_holo (hs k)
          have hl : DifferentiableAt ℝ (fun t : ℝ => z + t • e) s :=
            (differentiableAt_const z).add (differentiableAt_id.smul_const e)
          exact (h1.differentiableAt (by norm_num)).comp s hl
        exact deriv_fun_sum fun k _ => hd_k k
      refine HasDerivAt.congr_of_eventuallyEq ?_ hd_eq
      have hsum2 : HasDerivAt
          (fun s : ℝ => ∑ k : Fin r, deriv (fun t : ℝ => ‖f k (z + t • e)‖ ^ 2) s)
          (∑ k : Fin r,
            (2 * (fderiv ℂ (fderiv ℂ (f k)) z e e * conj (f k z)).re +
              2 * ‖fderiv ℂ (f k) z e‖ ^ 2)) 0 :=
        HasDerivAt.fun_sum fun k _ => (hasDerivAt_norm_sq_holo_line (hf k) e).2
      refine hsum2.congr_deriv ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hu_ev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < u s ∧ DifferentiableAt ℝ u s := by
      have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 (0 : ℝ)) (𝓝 z) := by
        have hc : Continuous (fun s : ℝ => z + s • e) :=
          continuous_const.add (continuous_id.smul continuous_const)
        simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
      have hpos_ev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < u s :=
        hu1.continuousAt.eventually (isOpen_Ioi.mem_nhds (by rwa [hu0]))
      have hcd_ev : ∀ᶠ s in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 S (z + s • e) :=
        hcont.eventually (hS_cd.eventually (by simp))
      filter_upwards [hpos_ev, hcd_ev] with s hsp hsc
      have hl : DifferentiableAt ℝ (fun t : ℝ => z + t • e) s :=
        (differentiableAt_const z).add (differentiableAt_id.smul_const e)
      refine ⟨hsp, ?_⟩
      change DifferentiableAt ℝ (S ∘ fun t : ℝ => z + t • e) s
      exact (hsc.differentiableAt (by norm_num)).comp s hl
    have h := deriv_deriv_log_at_zero (by rwa [hu0]) hu_ev hu1 hu2
    rwa [hu0] at h
  have h1 := hline_log w
  have h2 := hline_log (Complex.I • w)
  set A : ℂ := ∑ k : Fin r, fderiv ℂ (f k) z w * conj (f k z)
  have hI_sum : (∑ k : Fin r, fderiv ℂ (f k) z (Complex.I • w) * conj (f k z)) = Complex.I * A := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_assoc]
  have hI_norm : (∑ k : Fin r, ‖fderiv ℂ (f k) z (Complex.I • w)‖ ^ 2) =
      ∑ k : Fin r, ‖fderiv ℂ (f k) z w‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, norm_mul, Complex.norm_I, one_mul]
  have hI_snd : (∑ k : Fin r, (fderiv ℂ (fderiv ℂ (f k)) z (Complex.I • w) (Complex.I • w) *
      conj (f k z)).re) =
      -(∑ k : Fin r, (fderiv ℂ (fderiv ℂ (f k)) z w w * conj (f k z)).re) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hI2 : fderiv ℂ (fderiv ℂ (f k)) z (Complex.I • w) (Complex.I • w) =
        -fderiv ℂ (fderiv ℂ (f k)) z w w := by
      rw [map_smul, map_smul, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, Complex.I_mul_I]
      ring
    rw [hI2, neg_mul, Complex.neg_re]
  have hpyth : A.re ^ 2 + (Complex.I * A).re ^ 2 = ‖A‖ ^ 2 := by
    have him : (Complex.I * A).re = -A.im := by
      rw [Complex.mul_re, Complex.I_re, Complex.I_im]; ring
    rw [him, neg_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
  rw [hI_sum, hI_norm, hI_snd] at h2
  unfold leviForm
  rw [← deriv_deriv_line hlog_cd w, ← deriv_deriv_line hlog_cd (Complex.I • w), h1, h2]
  have hS_ne : S z ≠ 0 := hpos.ne'
  dsimp only [S] at hS_ne ⊢
  field_simp [hS_ne]
  rw [← hpyth]
  ring

/-- **Griffiths / Fubini–Study Curvature Positivity**:
`leviForm (log ∑_k ‖f_k‖²) z w ≥ 0` for any finite tuple of `C²` holomorphic functions not all
vanishing at `z`. -/
theorem leviForm_log_sum_norm_sq_nonneg {J : Type*} [Fintype J] {r : ℕ}
    (f : Fin r → (J → ℂ) → ℂ) {z : J → ℂ} (hf : ∀ k, ContDiffAt ℂ 2 (f k) z)
    (hpos : 0 < ∑ k : Fin r, ‖f k z‖ ^ 2) (w : J → ℂ) :
    0 ≤ leviForm (fun y => Real.log (∑ k : Fin r, ‖f k y‖ ^ 2)) z w := by
  rw [leviForm_log_sum_norm_sq_eq f hf hpos w]
  refine div_nonneg ?_ (sq_nonneg _)
  have htri : ‖∑ k : Fin r, fderiv ℂ (f k) z w * conj (f k z)‖ ≤
      ∑ k : Fin r, ‖f k z‖ * ‖fderiv ℂ (f k) z w‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, Complex.norm_conj, mul_comm]
  have hsq : ‖∑ k : Fin r, fderiv ℂ (f k) z w * conj (f k z)‖ ^ 2 ≤
      (∑ k : Fin r, ‖f k z‖ * ‖fderiv ℂ (f k) z w‖) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (∑ k : Fin r, fderiv ℂ (f k) z w * conj (f k z))]) htri
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin r => ‖f k z‖) (fun k : Fin r => ‖fderiv ℂ (f k) z w‖)
  linarith

/-- **Pluriharmonicity of `log ‖f‖²` Away from Zeros in Arbitrary Dimension `d`**:
for any `C²` holomorphic `f : (J → ℂ) → ℂ` with `f z ≠ 0`,
`leviForm (fun y => Real.log (‖f y‖ ^ 2)) z w = 0`. -/
theorem leviForm_log_norm_sq_holomorphic {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (hne : f z ≠ 0) (w : J → ℂ) :
    leviForm (fun y => Real.log (‖f y‖ ^ 2)) z w = 0 := by
  have hpos : 0 < ∑ _k : Fin 1, ‖f z‖ ^ 2 := by
    simpa using sq_pos_of_pos (norm_pos_iff.mpr hne)
  have h := leviForm_log_sum_norm_sq_eq (fun _ : Fin 1 => f) (fun _ => hf) hpos w
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, norm_mul,
    Complex.norm_conj, mul_pow] at h
  rw [h]
  ring

/-- Corollary: `leviForm (fun y => Real.log ‖f y‖) z w = 0` away from zeros of holomorphic `f`. -/
theorem leviForm_log_norm_holomorphic {J : Type*} [Fintype J] {f : (J → ℂ) → ℂ} {z : J → ℂ}
    (hf : ContDiffAt ℂ 2 f z) (hne : f z ≠ 0) (w : J → ℂ) :
    leviForm (fun y => Real.log ‖f y‖) z w = 0 := by
  have heq : (fun y => Real.log (‖f y‖ ^ 2)) = fun y => 2 * Real.log ‖f y‖ := by
    funext y
    rw [Real.log_pow]
    push_cast
    rfl
  have hlog : ContDiffAt ℝ 2 (fun y => Real.log ‖f y‖) z := by
    have hns : ContDiffAt ℝ 2 (fun y => Real.log (‖f y‖ ^ 2)) z :=
      (contDiffAt_norm_sq_of_holo hf).log (sq_pos_of_pos (norm_pos_iff.mpr hne)).ne'
    have hhalf : (fun y => Real.log ‖f y‖) = fun y => (1 / 2 : ℝ) * Real.log (‖f y‖ ^ 2) := by
      funext y
      rw [Real.log_pow]
      push_cast
      ring
    rw [hhalf]
    exact contDiffAt_const.mul hns
  have h0 := leviForm_log_norm_sq_holomorphic hf hne w
  rw [heq, leviForm_const_mul 2 hlog w] at h0
  linarith

/-! ### Concrete `HermitianCurvatureForm` Structure & Algebra -/

/-- **Concrete Hermitian `(1, 1)`-Curvature Form** on a subset `X ⊆ ℂ^d`:
a family of real-valued Hermitian quadratic forms `z ↦ (w ↦ Θ_z(w, w))` satisfying complex
quadratic homogeneity `Θ_z(c • w) = ‖c‖² Θ_z(w)` and the parallelogram law. -/
structure HermitianCurvatureForm (d : ℕ) (X : Set (Fin d → ℂ)) where
  /-- Pointwise quadratic evaluation `Θ_z(w, w) ∈ ℝ` at `z ∈ X` in tangent direction `w ∈ ℂ^d`. -/
  eval : (Fin d → ℂ) → (Fin d → ℂ) → ℝ
  /-- Complex quadratic homogeneity `Θ_z(c • w) = ‖c‖² Θ_z(w)`. -/
  homog : ∀ z ∈ X, ∀ (c : ℂ) (w : Fin d → ℂ), eval z (c • w) = ‖c‖ ^ 2 * eval z w
  /-- Parallelogram identity (ensuring `eval z` arises from a Hermitian sesquilinear form). -/
  parallelogram : ∀ z ∈ X, ∀ (u v : Fin d → ℂ),
    eval z (u + v) + eval z (u - v) = 2 * eval z u + 2 * eval z v

namespace HermitianCurvatureForm

variable {d : ℕ} {X : Set (Fin d → ℂ)}

/-- Zero Hermitian `(1, 1)`-form. -/
instance : Zero (HermitianCurvatureForm d X) where
  zero :=
    { eval := fun _ _ => 0
      homog := fun _ _ _ _ => by ring
      parallelogram := fun _ _ _ _ => by ring }

/-- Sum of two Hermitian `(1, 1)`-forms. -/
instance : Add (HermitianCurvatureForm d X) where
  add ω₁ ω₂ :=
    { eval := fun z w => ω₁.eval z w + ω₂.eval z w
      homog := fun z hz c w => by rw [ω₁.homog z hz c w, ω₂.homog z hz c w]; ring
      parallelogram := fun z hz u v => by
        linarith [ω₁.parallelogram z hz u v, ω₂.parallelogram z hz u v] }

/-- Negation of a Hermitian `(1, 1)`-form. -/
instance : Neg (HermitianCurvatureForm d X) where
  neg ω :=
    { eval := fun z w => -ω.eval z w
      homog := fun z hz c w => by rw [ω.homog z hz c w]; ring
      parallelogram := fun z hz u v => by linarith [ω.parallelogram z hz u v] }

/-- Difference of two Hermitian `(1, 1)`-forms. -/
instance : Sub (HermitianCurvatureForm d X) where
  sub ω₁ ω₂ :=
    { eval := fun z w => ω₁.eval z w - ω₂.eval z w
      homog := fun z hz c w => by rw [ω₁.homog z hz c w, ω₂.homog z hz c w]; ring
      parallelogram := fun z hz u v => by
        linarith [ω₁.parallelogram z hz u v, ω₂.parallelogram z hz u v] }

/-- Real scalar multiple of a Hermitian `(1, 1)`-form. -/
instance : SMul ℝ (HermitianCurvatureForm d X) where
  smul a ω :=
    { eval := fun z w => a * ω.eval z w
      homog := fun z hz c w => by rw [ω.homog z hz c w]; ring
      parallelogram := fun z hz u v => by
        have h := ω.parallelogram z hz u v
        linear_combination a * h }

@[simp] lemma zero_eval (z w : Fin d → ℂ) : (0 : HermitianCurvatureForm d X).eval z w = 0 := rfl
@[simp] lemma add_eval (ω₁ ω₂ : HermitianCurvatureForm d X) (z w : Fin d → ℂ) :
    (ω₁ + ω₂).eval z w = ω₁.eval z w + ω₂.eval z w := rfl
@[simp] lemma neg_eval (ω : HermitianCurvatureForm d X) (z w : Fin d → ℂ) :
    (-ω).eval z w = -ω.eval z w := rfl
@[simp] lemma sub_eval (ω₁ ω₂ : HermitianCurvatureForm d X) (z w : Fin d → ℂ) :
    (ω₁ - ω₂).eval z w = ω₁.eval z w - ω₂.eval z w := rfl
@[simp] lemma smul_eval (a : ℝ) (ω : HermitianCurvatureForm d X) (z w : Fin d → ℂ) :
    (a • ω).eval z w = a * ω.eval z w := rfl

lemma eval_zero (ω : HermitianCurvatureForm d X) {z : Fin d → ℂ} (hz : z ∈ X) :
    ω.eval z 0 = 0 := by
  have h := ω.homog z hz 0 0
  simpa using h

/-- Construct a `HermitianCurvatureForm` directly from a local metric potential `φ` via `leviForm`. -/
def ofPotential (d : ℕ) (X : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) :
    HermitianCurvatureForm d X where
  eval := leviForm φ
  homog := fun z _ c w => leviForm_smul_complex φ z c w
  parallelogram := fun z _ u v => leviForm_parallelogram φ z u v

/-- Construct a `HermitianCurvatureForm` from a field of Hermitian matrices
`H : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ` via `w ↦ Re(wᴴ H(z) w)`. -/
def ofHermMatrix (d : ℕ) (X : Set (Fin d → ℂ))
    (H : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ) :
    HermitianCurvatureForm d X where
  eval z w := (star w ⬝ᵥ (H z).mulVec w).re
  homog z _ c w := by
    have hmul : star (c • w) ⬝ᵥ (H z).mulVec (c • w) =
        ((‖c‖ ^ 2 : ℝ) : ℂ) * (star w ⬝ᵥ (H z).mulVec w) := by
      rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, RCLike.star_def, mul_comm (conj c) c, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    rw [hmul, Complex.re_ofReal_mul]
  parallelogram z _ u v := by
    have hadd : star (u + v) ⬝ᵥ (H z).mulVec (u + v) =
        star u ⬝ᵥ (H z).mulVec u + star u ⬝ᵥ (H z).mulVec v +
          star v ⬝ᵥ (H z).mulVec u + star v ⬝ᵥ (H z).mulVec v := by
      rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
      ring
    have hsub : star (u - v) ⬝ᵥ (H z).mulVec (u - v) =
        star u ⬝ᵥ (H z).mulVec u - star u ⬝ᵥ (H z).mulVec v -
          star v ⬝ᵥ (H z).mulVec u + star v ⬝ᵥ (H z).mulVec v := by
      rw [star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
      ring
    rw [hadd, hsub]
    simp only [Complex.add_re, Complex.sub_re]
    ring

/-- Pointwise dominance order `ω₁ ≤ ω₂` on `X`. -/
def FormLe (ω₁ ω₂ : HermitianCurvatureForm d X) : Prop :=
  ∀ z ∈ X, ∀ w : Fin d → ℂ, ω₁.eval z w ≤ ω₂.eval z w

/-- Semipositivity (`ω ≥ 0` on `X`). -/
def IsSemipositive (ω : HermitianCurvatureForm d X) : Prop :=
  ∀ z ∈ X, ∀ w : Fin d → ℂ, 0 ≤ ω.eval z w

/-- Strict positivity (`ω(z, w) > 0` for all `z ∈ X` and `w ≠ 0`). -/
def IsStrictlyPositive (ω : HermitianCurvatureForm d X) : Prop :=
  ∀ z ∈ X, ∀ w : Fin d → ℂ, w ≠ 0 → 0 < ω.eval z w

/-- Uniform positivity (`c ∑ ‖w_j‖² ≤ ω(z, w)` for some `c > 0`, Kähler lower bound). -/
def IsUniformlyPositive (ω : HermitianCurvatureForm d X) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ z ∈ X, ∀ w : Fin d → ℂ, c * (∑ j : Fin d, ‖w j‖ ^ 2) ≤ ω.eval z w

/-- Seminegativity (`ω ≤ 0` on `X`). -/
def IsSeminegative (ω : HermitianCurvatureForm d X) : Prop :=
  ∀ z ∈ X, ∀ w : Fin d → ℂ, ω.eval z w ≤ 0

/-- Strict negativity (`ω(z, w) < 0` for all `z ∈ X` and `w ≠ 0`). -/
def IsStrictlyNegative (ω : HermitianCurvatureForm d X) : Prop :=
  ∀ z ∈ X, ∀ w : Fin d → ℂ, w ≠ 0 → ω.eval z w < 0

lemma isStrictlyPositive_imp_semipositive {ω : HermitianCurvatureForm d X}
    (h : ω.IsStrictlyPositive) : ω.IsSemipositive := by
  intro z hz w
  by_cases hw : w = 0
  · rw [hw, ω.eval_zero hz]
  · exact (h z hz w hw).le

lemma isUniformlyPositive_imp_strictlyPositive {ω : HermitianCurvatureForm d X}
    (h : ω.IsUniformlyPositive) : ω.IsStrictlyPositive := by
  rcases h with ⟨c, hc, hbd⟩
  intro z hz w hw
  have hsum_pos : 0 < ∑ j : Fin d, ‖w j‖ ^ 2 := by
    have hex : ∃ j : Fin d, w j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    rcases hex with ⟨j₀, hj₀⟩
    exact Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨j₀, Finset.mem_univ j₀, sq_pos_of_pos (norm_pos_iff.mpr hj₀)⟩
  exact lt_of_lt_of_le (mul_pos hc hsum_pos) (hbd z hz w)

lemma isStrictlyNegative_imp_seminegative {ω : HermitianCurvatureForm d X}
    (h : ω.IsStrictlyNegative) : ω.IsSeminegative := by
  intro z hz w
  by_cases hw : w = 0
  · rw [hw, ω.eval_zero hz]
  · exact (h z hz w hw).le

lemma isSeminegative_iff_neg_semipositive (ω : HermitianCurvatureForm d X) :
    ω.IsSeminegative ↔ (-ω).IsSemipositive := by
  constructor
  · intro h z hz w; simp only [neg_eval]; linarith [h z hz w]
  · intro h z hz w; have h1 := h z hz w; simp only [neg_eval] at h1; linarith

lemma isStrictlyNegative_iff_neg_strictlyPositive (ω : HermitianCurvatureForm d X) :
    ω.IsStrictlyNegative ↔ (-ω).IsStrictlyPositive := by
  constructor
  · intro h z hz w hw; simp only [neg_eval]; linarith [h z hz w hw]
  · intro h z hz w hw; have h1 := h z hz w hw; simp only [neg_eval] at h1; linarith

lemma isSemipositive_add {ω₁ ω₂ : HermitianCurvatureForm d X}
    (h₁ : ω₁.IsSemipositive) (h₂ : ω₂.IsSemipositive) : (ω₁ + ω₂).IsSemipositive :=
  fun z hz w => add_nonneg (h₁ z hz w) (h₂ z hz w)

lemma isStrictlyPositive_add_semipositive {ω₁ ω₂ : HermitianCurvatureForm d X}
    (h₁ : ω₁.IsStrictlyPositive) (h₂ : ω₂.IsSemipositive) : (ω₁ + ω₂).IsStrictlyPositive :=
  fun z hz w hw => add_pos_of_pos_of_nonneg (h₁ z hz w hw) (h₂ z hz w)

lemma isSemipositive_smul {a : ℝ} (ha : 0 ≤ a) {ω : HermitianCurvatureForm d X}
    (h : ω.IsSemipositive) : (a • ω).IsSemipositive :=
  fun z hz w => mul_nonneg ha (h z hz w)

lemma isStrictlyPositive_smul {a : ℝ} (ha : 0 < a) {ω : HermitianCurvatureForm d X}
    (h : ω.IsStrictlyPositive) : (a • ω).IsStrictlyPositive :=
  fun z hz w hw => mul_pos ha (h z hz w hw)

lemma isSeminegative_add {ω₁ ω₂ : HermitianCurvatureForm d X}
    (h₁ : ω₁.IsSeminegative) (h₂ : ω₂.IsSeminegative) : (ω₁ + ω₂).IsSeminegative :=
  fun z hz w => add_nonpos (h₁ z hz w) (h₂ z hz w)

/-- Positive-semidefinite Hermitian matrices induce semipositive curvature forms. -/
theorem ofHermMatrix_isSemipositive {H : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ}
    (hH : ∀ z ∈ X, (H z).PosSemidef) :
    (ofHermMatrix d X H).IsSemipositive :=
  fun z hz w => (hH z hz).re_dotProduct_nonneg w

/-- Positive-definite Hermitian matrices induce strictly positive curvature forms. -/
theorem ofHermMatrix_isStrictlyPositive {H : (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ}
    (hH : ∀ z ∈ X, (H z).PosDef) :
    (ofHermMatrix d X H).IsStrictlyPositive := by
  intro z hz w hw
  have hpd := (hH z hz).re_dotProduct_pos hw
  simpa [ofHermMatrix] using hpd

/-- Pullback of a Hermitian `(1, 1)`-form along a `ℂ`-linear map `T : (Fin d₁ → ℂ) →L[ℂ] (Fin d₂ → ℂ)`. -/
def pullbackCLM {d₁ d₂ : ℕ} {X₁ : Set (Fin d₁ → ℂ)} {X₂ : Set (Fin d₂ → ℂ)}
    (T : (Fin d₁ → ℂ) →L[ℂ] (Fin d₂ → ℂ)) (hT : ∀ z ∈ X₁, T z ∈ X₂)
    (ω : HermitianCurvatureForm d₂ X₂) : HermitianCurvatureForm d₁ X₁ where
  eval z w := ω.eval (T z) (T w)
  homog z hz c w := by rw [map_smul, ω.homog (T z) (hT z hz) c (T w)]
  parallelogram z hz u v := by
    rw [map_add, map_sub, ω.parallelogram (T z) (hT z hz) (T u) (T v)]

end HermitianCurvatureForm

end ComplexHessianAlgebra

/-! ## Section 2: Concrete `MetrizedLineBundle`, `ChernFirstForm`, `SeminegativeMetric`, & `PosCurvatureMetric` -/

section MetrizedLineBundles

/-- **Concrete Metrized Holomorphic Line Bundle `(L, h)`** over a complex domain `X ⊆ ℂ^d`:
given by an open trivializing cover `{U_i}_{i ∈ ι}`, holomorphic nonvanishing transition cocycle
`g_{ij} : U_i ∩ U_j → ℂˣ`, and `C²` local Hermitian metric weights `φ_i = -log h_i`
satisfying the exact cocycle compatibility `φ_i(z) - φ_j(z) = log(‖g_{ij}(z)‖²)` on `U_i ∩ U_j`. -/
structure MetrizedLineBundle (d : ℕ) (ι : Type*) (X : Set (Fin d → ℂ)) where
  /-- Open trivializing cover `{U_i}`. -/
  openCover : ι → Set (Fin d → ℂ)
  /-- Each chart `U_i` is open in `ℂ^d`. -/
  isOpen_cover : ∀ i, IsOpen (openCover i)
  /-- The charts cover `X`. -/
  covers : X ⊆ ⋃ i, openCover i
  /-- Holomorphic transition functions `g_{ij}` (`s_i = g_{ij} · s_j` on `U_i ∩ U_j`). -/
  transFn : ι → ι → (Fin d → ℂ) → ℂ
  /-- Each `g_{ij}` is `C²`-holomorphic on `U_i ∩ U_j`. -/
  transFn_holo : ∀ i j, ∀ z ∈ openCover i ∩ openCover j, ContDiffAt ℂ 2 (transFn i j) z
  /-- Each `g_{ij}` is nonvanishing on `U_i ∩ U_j`. -/
  transFn_ne_zero : ∀ i j, ∀ z ∈ openCover i ∩ openCover j, transFn i j z ≠ 0
  /-- Normalization `g_{ii} = 1` on `U_i`. -/
  transFn_self : ∀ i, ∀ z ∈ openCover i, transFn i i z = 1
  /-- Cocycle condition `g_{ij} · g_{jk} = g_{ik}` on `U_i ∩ U_j ∩ U_k`. -/
  transFn_cocycle : ∀ i j k, ∀ z ∈ openCover i ∩ openCover j ∩ openCover k,
    transFn i j z * transFn j k z = transFn i k z
  /-- Local Hermitian metric weights `φ_i = -log h_i` (`‖s‖²_h = ‖s_i‖² exp(-φ_i)`). -/
  weight : ι → (Fin d → ℂ) → ℝ
  /-- Each local metric weight `φ_i` is `C²` on `U_i`. -/
  weight_smooth : ∀ i, ∀ z ∈ openCover i, ContDiffAt ℝ 2 (weight i) z
  /-- Cocycle compatibility `φ_i - φ_j = log (‖g_{ij}‖²)` on `U_i ∩ U_j`. -/
  weight_compat : ∀ i j, ∀ z ∈ openCover i ∩ openCover j,
    weight i z - weight j z = Real.log (‖transFn i j z‖ ^ 2)

namespace MetrizedLineBundle

variable {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}

/-- **Chart Independence of the Local Curvature Form**:
on any overlap `z ∈ U_i ∩ U_j`, `leviForm (L.weight i) z w = leviForm (L.weight j) z w`. -/
theorem leviForm_weight_eq_of_mem (L : MetrizedLineBundle d ι X) {i j : ι} {z : Fin d → ℂ}
    (hi : z ∈ L.openCover i) (hj : z ∈ L.openCover j) (w : Fin d → ℂ) :
    leviForm (L.weight i) z w = leviForm (L.weight j) z w := by
  have hopen : IsOpen (L.openCover i ∩ L.openCover j) :=
    (L.isOpen_cover i).inter (L.isOpen_cover j)
  have hev : (fun y => L.weight i y - L.weight j y) =ᶠ[𝓝 z]
      fun y => Real.log (‖L.transFn i j y‖ ^ 2) := by
    filter_upwards [hopen.mem_nhds ⟨hi, hj⟩] with y hy
    exact L.weight_compat i j y hy
  have hsub := leviForm_congr_of_eventuallyEq hev w
  rw [leviForm_sub (L.weight_smooth i z hi) (L.weight_smooth j z hj) w,
    leviForm_log_norm_sq_holomorphic (L.transFn_holo i j z ⟨hi, hj⟩)
      (L.transFn_ne_zero i j z ⟨hi, hj⟩) w] at hsub
  linarith

/-- Globally well-defined pointwise **Hermitian Curvature Evaluation** `Θ(L, h)_z(w, w)`. -/
def curvatureAt (L : MetrizedLineBundle d ι X) (z w : Fin d → ℂ) : ℝ :=
  if h : ∃ i, z ∈ L.openCover i then leviForm (L.weight h.choose) z w else 0

/-- `L.curvatureAt z w` agrees with `leviForm (L.weight i) z w` on ANY chart `U_i ∋ z`. -/
theorem curvatureAt_eq_of_mem (L : MetrizedLineBundle d ι X) {i : ι} {z : Fin d → ℂ}
    (hi : z ∈ L.openCover i) (w : Fin d → ℂ) :
    L.curvatureAt z w = leviForm (L.weight i) z w := by
  unfold curvatureAt
  have hex : ∃ k, z ∈ L.openCover k := ⟨i, hi⟩
  rw [dif_pos hex]
  exact L.leviForm_weight_eq_of_mem hex.choose_spec hi w

/-- Intrinsic global **Hermitian Curvature `(1, 1)`-Form** `Θ(L, h)` of a `MetrizedLineBundle`. -/
def curvatureForm (L : MetrizedLineBundle d ι X) : HermitianCurvatureForm d X where
  eval := L.curvatureAt
  homog z hz c w := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
    rw [L.curvatureAt_eq_of_mem hi, L.curvatureAt_eq_of_mem hi]
    exact leviForm_smul_complex (L.weight i) z c w
  parallelogram z hz u v := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
    rw [L.curvatureAt_eq_of_mem hi, L.curvatureAt_eq_of_mem hi,
      L.curvatureAt_eq_of_mem hi, L.curvatureAt_eq_of_mem hi]
    exact leviForm_parallelogram (L.weight i) z u v

end MetrizedLineBundle

/-- **Concrete First Chern `(1, 1)`-Form** of a metrized holomorphic line bundle `(L, h)`:
$$c_1(L, h) := \frac{1}{\pi}\, \Theta(L, h) = \frac{i}{2\pi} \partial\bar\partial (-\log h).$$
Matches `Stage11HermitianCurvature.firstChernDensity` (`k / (4π) y⁻²`) verbatim! -/
def ChernFirstForm {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) : HermitianCurvatureForm d X :=
  (1 / Real.pi) • L.curvatureForm

/-- Pointwise evaluation of `ChernFirstForm L` on any chart `U_i ∋ z`. -/
theorem chernFirstForm_eval_eq_of_mem {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) {i : ι} {z : Fin d → ℂ} (hi : z ∈ L.openCover i)
    (w : Fin d → ℂ) :
    (ChernFirstForm L).eval z w = (1 / Real.pi) * leviForm (L.weight i) z w := by
  simp only [ChernFirstForm, HermitianCurvatureForm.smul_eval, MetrizedLineBundle.curvatureForm]
  rw [L.curvatureAt_eq_of_mem hi]

/-- **Semipositive Metric** (`c₁(L, h) ≥ 0` / plurisubharmonic local weights — nefness). -/
def SemipositiveMetric {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) : Prop :=
  L.curvatureForm.IsSemipositive

/-- **Strictly Positive Curvature Metric** (`c₁(L, h) > 0` — ampleness / Kähler positivity). -/
def PosCurvatureMetric {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) : Prop :=
  L.curvatureForm.IsStrictlyPositive

/-- **Seminegative Metric** (`c₁(L, h) ≤ 0` — Griffiths subbundle / semi-abelian Lie algebra
seminegativity). -/
def SeminegativeMetric {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) : Prop :=
  L.curvatureForm.IsSeminegative

/-- **Strictly Negative Curvature Metric** (`c₁(L, h) < 0`). -/
def NegCurvatureMetric {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) : Prop :=
  L.curvatureForm.IsStrictlyNegative

/-- Equivalent characterization of `SemipositiveMetric` via `ChernFirstForm`. -/
theorem semipositiveMetric_iff_chernFirstForm {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) :
    SemipositiveMetric L ↔ (ChernFirstForm L).IsSemipositive := by
  have hpi : 0 < 1 / Real.pi := by positivity
  constructor
  · exact HermitianCurvatureForm.isSemipositive_smul hpi.le
  · intro h z hz w
    exact nonneg_of_mul_nonneg_right (h z hz w) hpi

/-- Equivalent characterization of `PosCurvatureMetric` via `ChernFirstForm`. -/
theorem posCurvatureMetric_iff_chernFirstForm {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) :
    PosCurvatureMetric L ↔ (ChernFirstForm L).IsStrictlyPositive := by
  have hpi : 0 < 1 / Real.pi := by positivity
  constructor
  · exact HermitianCurvatureForm.isStrictlyPositive_smul hpi
  · intro h z hz w hw
    exact pos_of_mul_pos_right (h z hz w hw) hpi.le

/-- Equivalent characterization of `SeminegativeMetric` via `ChernFirstForm`. -/
theorem seminegativeMetric_iff_chernFirstForm {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) :
    SeminegativeMetric L ↔ (ChernFirstForm L).IsSeminegative := by
  have hpi : 0 < 1 / Real.pi := by positivity
  constructor
  · intro h z hz w
    exact mul_nonpos_of_nonneg_of_nonpos hpi.le (h z hz w)
  · intro h z hz w
    exact nonpos_of_mul_nonpos_right (h z hz w) hpi

/-- `PosCurvatureMetric` implies `SemipositiveMetric`. -/
theorem PosCurvatureMetric.semipositive {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (h : PosCurvatureMetric L) : SemipositiveMetric L :=
  HermitianCurvatureForm.isStrictlyPositive_imp_semipositive h

/-- `NegCurvatureMetric` implies `SeminegativeMetric`. -/
theorem NegCurvatureMetric.seminegative {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (h : NegCurvatureMetric L) : SeminegativeMetric L :=
  HermitianCurvatureForm.isStrictlyNegative_imp_seminegative h

namespace MetrizedLineBundle

variable {d : ℕ} {ι ι₁ ι₂ : Type*} {X : Set (Fin d → ℂ)}

/-- Single-chart **trivial holomorphic line bundle** on an open domain `X ⊆ ℂ^d` with global `C²`
Hermitian metric weight `φ`. -/
def trivial (d : ℕ) (X : Set (Fin d → ℂ)) (hX : IsOpen X) (φ : (Fin d → ℂ) → ℝ)
    (hφ : ∀ z ∈ X, ContDiffAt ℝ 2 φ z) : MetrizedLineBundle d Unit X where
  openCover _ := X
  isOpen_cover _ := hX
  covers := fun z hz => Set.mem_iUnion.mpr ⟨(), hz⟩
  transFn _ _ _ := 1
  transFn_holo _ _ _ _ := contDiffAt_const
  transFn_ne_zero _ _ _ _ := one_ne_zero
  transFn_self _ _ _ := rfl
  transFn_cocycle _ _ _ _ _ := one_mul 1
  weight _ := φ
  weight_smooth _ := hφ
  weight_compat _ _ _ _ := by simp

@[simp]
lemma trivial_curvatureAt (hX : IsOpen X) (φ : (Fin d → ℂ) → ℝ)
    (hφ : ∀ z ∈ X, ContDiffAt ℝ 2 φ z) {z : Fin d → ℂ} (hz : z ∈ X) (w : Fin d → ℂ) :
    (trivial d X hX φ hφ).curvatureAt z w = leviForm φ z w :=
  (trivial d X hX φ hφ).curvatureAt_eq_of_mem (i := ()) hz w

/-- Exact bridge between `SemipositiveMetric (trivial ...)` and
`HermitianCurvatureCore.IsPlurisubharmonicOn`. -/
theorem trivial_semipositive_iff_isPlurisubharmonicOn (hX : IsOpen X) (φ : (Fin d → ℂ) → ℝ)
    (hφ : ∀ z ∈ X, ContDiffAt ℝ 2 φ z) :
    SemipositiveMetric (trivial d X hX φ hφ) ↔ IsPlurisubharmonicOn φ X := by
  constructor
  · intro h z hz
    refine ⟨hφ z hz, fun w => ?_⟩
    have h1 : 0 ≤ (trivial d X hX φ hφ).curvatureAt z w := h z hz w
    rwa [trivial_curvatureAt hX φ hφ hz w] at h1
  · intro h z hz w
    rw [show (trivial d X hX φ hφ).curvatureForm.eval z w = leviForm φ z w from
      trivial_curvatureAt hX φ hφ hz w]
    exact (h z hz).2 w

/-- **Dual Metrized Line Bundle** `L^∨` (`g^∨_{ij} = g_{ij}⁻¹`, `φ^∨_i = -φ_i`). -/
def dual (L : MetrizedLineBundle d ι X) : MetrizedLineBundle d ι X where
  openCover := L.openCover
  isOpen_cover := L.isOpen_cover
  covers := L.covers
  transFn i j z := (L.transFn i j z)⁻¹
  transFn_holo i j z hz := (L.transFn_holo i j z hz).inv (L.transFn_ne_zero i j z hz)
  transFn_ne_zero i j z hz := inv_ne_zero (L.transFn_ne_zero i j z hz)
  transFn_self i z hz := by rw [L.transFn_self i z hz, inv_one]
  transFn_cocycle i j k z hz := by
    rw [← mul_inv, L.transFn_cocycle i j k z hz]
  weight i z := -L.weight i z
  weight_smooth i z hz := (L.weight_smooth i z hz).neg
  weight_compat i j z hz := by
    have hc := L.weight_compat i j z hz
    rw [norm_inv, inv_pow, Real.log_inv]
    linarith

/-- **Tensor Product** `L₁ ⊗ L₂` of two metrized line bundles over `X`. -/
def tensor (L₁ : MetrizedLineBundle d ι₁ X) (L₂ : MetrizedLineBundle d ι₂ X) :
    MetrizedLineBundle d (ι₁ × ι₂) X where
  openCover p := L₁.openCover p.1 ∩ L₂.openCover p.2
  isOpen_cover p := (L₁.isOpen_cover p.1).inter (L₂.isOpen_cover p.2)
  covers z hz := by
    obtain ⟨i₁, hi₁⟩ := Set.mem_iUnion.mp (L₁.covers hz)
    obtain ⟨i₂, hi₂⟩ := Set.mem_iUnion.mp (L₂.covers hz)
    exact Set.mem_iUnion.mpr ⟨(i₁, i₂), ⟨hi₁, hi₂⟩⟩
  transFn p q z := L₁.transFn p.1 q.1 z * L₂.transFn p.2 q.2 z
  transFn_holo p q z hz :=
    (L₁.transFn_holo p.1 q.1 z ⟨hz.1.1, hz.2.1⟩).mul (L₂.transFn_holo p.2 q.2 z ⟨hz.1.2, hz.2.2⟩)
  transFn_ne_zero p q z hz :=
    mul_ne_zero (L₁.transFn_ne_zero p.1 q.1 z ⟨hz.1.1, hz.2.1⟩)
      (L₂.transFn_ne_zero p.2 q.2 z ⟨hz.1.2, hz.2.2⟩)
  transFn_self p z hz := by
    rw [L₁.transFn_self p.1 z hz.1, L₂.transFn_self p.2 z hz.2, mul_one]
  transFn_cocycle p q r z hz := by
    have h1 := L₁.transFn_cocycle p.1 q.1 r.1 z ⟨⟨hz.1.1.1, hz.1.2.1⟩, hz.2.1⟩
    have h2 := L₂.transFn_cocycle p.2 q.2 r.2 z ⟨⟨hz.1.1.2, hz.1.2.2⟩, hz.2.2⟩
    calc L₁.transFn p.1 q.1 z * L₂.transFn p.2 q.2 z *
            (L₁.transFn q.1 r.1 z * L₂.transFn q.2 r.2 z)
        = (L₁.transFn p.1 q.1 z * L₁.transFn q.1 r.1 z) *
            (L₂.transFn p.2 q.2 z * L₂.transFn q.2 r.2 z) := by ring
      _ = L₁.transFn p.1 r.1 z * L₂.transFn p.2 r.2 z := by rw [h1, h2]
  weight p z := L₁.weight p.1 z + L₂.weight p.2 z
  weight_smooth p z hz := (L₁.weight_smooth p.1 z hz.1).add (L₂.weight_smooth p.2 z hz.2)
  weight_compat p q z hz := by
    have h1 := L₁.weight_compat p.1 q.1 z ⟨hz.1.1, hz.2.1⟩
    have h2 := L₂.weight_compat p.2 q.2 z ⟨hz.1.2, hz.2.2⟩
    have hn1 : ‖L₁.transFn p.1 q.1 z‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (L₁.transFn_ne_zero p.1 q.1 z ⟨hz.1.1, hz.2.1⟩))
    have hn2 : ‖L₂.transFn p.2 q.2 z‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr (L₂.transFn_ne_zero p.2 q.2 z ⟨hz.1.2, hz.2.2⟩))
    rw [norm_mul, mul_pow, Real.log_mul hn1 hn2]
    linarith

/-- Integer tensor power `L^{⊗ k}` (`k : ℤ`) of a metrized line bundle. -/
def pow (L : MetrizedLineBundle d ι X) (k : ℤ) : MetrizedLineBundle d ι X where
  openCover := L.openCover
  isOpen_cover := L.isOpen_cover
  covers := L.covers
  transFn i j z := L.transFn i j z ^ k
  transFn_holo i j z hz := by
    cases k with
    | ofNat n =>
      have hfun : (fun y : Fin d → ℂ => L.transFn i j y ^ (Int.ofNat n)) =
          fun y => L.transFn i j y ^ n := by
        funext y; exact zpow_natCast _ n
      rw [hfun]
      exact (L.transFn_holo i j z hz).pow n
    | negSucc n =>
      have hfun : (fun y : Fin d → ℂ => L.transFn i j y ^ (Int.negSucc n)) =
          fun y => (L.transFn i j y ^ (n + 1))⁻¹ := by
        funext y; exact zpow_negSucc _ n
      rw [hfun]
      exact ((L.transFn_holo i j z hz).pow (n + 1)).inv
        (pow_ne_zero (n + 1) (L.transFn_ne_zero i j z hz))
  transFn_ne_zero i j z hz := zpow_ne_zero k (L.transFn_ne_zero i j z hz)
  transFn_self i z hz := by rw [L.transFn_self i z hz, _root_.one_zpow]
  transFn_cocycle i j l z hz := by
    rw [← mul_zpow, L.transFn_cocycle i j l z hz]
  weight i z := (k : ℝ) * L.weight i z
  weight_smooth i z hz := contDiffAt_const.mul (L.weight_smooth i z hz)
  weight_compat i j z hz := by
    have hc := L.weight_compat i j z hz
    rw [norm_zpow, ← zpow_natCast (‖L.transFn i j z‖ ^ k) 2, ← _root_.zpow_mul,
      mul_comm k ((2 : ℕ) : ℤ), _root_.zpow_mul, zpow_natCast, Real.log_zpow]
    linear_combination (k : ℝ) * hc

/-- Conformal **Metric Twist** `(L, e^{-u} h)` by a global `C²` real function `u`. -/
def twistMetric (L : MetrizedLineBundle d ι X) (u : (Fin d → ℂ) → ℝ)
    (hu : ∀ i, ∀ z ∈ L.openCover i, ContDiffAt ℝ 2 u z) : MetrizedLineBundle d ι X where
  openCover := L.openCover
  isOpen_cover := L.isOpen_cover
  covers := L.covers
  transFn := L.transFn
  transFn_holo := L.transFn_holo
  transFn_ne_zero := L.transFn_ne_zero
  transFn_self := L.transFn_self
  transFn_cocycle := L.transFn_cocycle
  weight i z := L.weight i z + u z
  weight_smooth i z hz := (L.weight_smooth i z hz).add (hu i z hz)
  weight_compat i j z hz := by
    have hc := L.weight_compat i j z hz
    linarith

/-- Constant metric rescaling `φ_i ↦ φ_i + c` (`h ↦ e^{-c} h`), modeling Arakelov fiber shifts
`L + (c / 2) F_∞`. -/
def scaleMetric (L : MetrizedLineBundle d ι X) (c : ℝ) : MetrizedLineBundle d ι X :=
  L.twistMetric (fun _ => c) (fun _ _ _ => contDiffAt_const)

/-- Convex metric interpolation `(1 - t) φ₀ + t φ₁` between two metrics on the same underlying
holomorphic line bundle (`openCover` and `transFn` equal). -/
def lerpMetric (L₀ L₁ : MetrizedLineBundle d ι X) (hcov : L₀.openCover = L₁.openCover)
    (htrans : L₀.transFn = L₁.transFn) (t : ℝ) : MetrizedLineBundle d ι X where
  openCover := L₀.openCover
  isOpen_cover := L₀.isOpen_cover
  covers := L₀.covers
  transFn := L₀.transFn
  transFn_holo := L₀.transFn_holo
  transFn_ne_zero := L₀.transFn_ne_zero
  transFn_self := L₀.transFn_self
  transFn_cocycle := L₀.transFn_cocycle
  weight i z := (1 - t) * L₀.weight i z + t * L₁.weight i z
  weight_smooth i z hz :=
    (contDiffAt_const.mul (L₀.weight_smooth i z hz)).add
      (contDiffAt_const.mul (L₁.weight_smooth i z (by rwa [← hcov])))
  weight_compat i j z hz := by
    have h0 := L₀.weight_compat i j z hz
    have h1 := L₁.weight_compat i j z (by rwa [← hcov])
    rw [← htrans] at h1
    linear_combination (1 - t) * h0 + t * h1

/-! ### Exact Functoriality of `ChernFirstForm` & Curvature Positivity/Negativity Closure -/

theorem curvatureAt_dual (L : MetrizedLineBundle d ι X) {z : Fin d → ℂ} (hz : z ∈ X)
    (w : Fin d → ℂ) :
    L.dual.curvatureAt z w = -L.curvatureAt z w := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  rw [L.dual.curvatureAt_eq_of_mem hi, L.curvatureAt_eq_of_mem hi]
  exact leviForm_neg (L.weight_smooth i z hi) w

theorem chernFirstForm_dual (L : MetrizedLineBundle d ι X) {z : Fin d → ℂ} (hz : z ∈ X)
    (w : Fin d → ℂ) :
    (ChernFirstForm L.dual).eval z w = (-ChernFirstForm L).eval z w := by
  simp only [ChernFirstForm, HermitianCurvatureForm.smul_eval, HermitianCurvatureForm.neg_eval,
    curvatureForm, L.curvatureAt_dual hz w]
  ring

theorem curvatureAt_tensor (L₁ : MetrizedLineBundle d ι₁ X) (L₂ : MetrizedLineBundle d ι₂ X)
    {z : Fin d → ℂ} (hz : z ∈ X) (w : Fin d → ℂ) :
    (L₁.tensor L₂).curvatureAt z w = L₁.curvatureAt z w + L₂.curvatureAt z w := by
  obtain ⟨i₁, hi₁⟩ := Set.mem_iUnion.mp (L₁.covers hz)
  obtain ⟨i₂, hi₂⟩ := Set.mem_iUnion.mp (L₂.covers hz)
  rw [(L₁.tensor L₂).curvatureAt_eq_of_mem (i := (i₁, i₂)) ⟨hi₁, hi₂⟩,
    L₁.curvatureAt_eq_of_mem hi₁, L₂.curvatureAt_eq_of_mem hi₂]
  exact leviForm_add (L₁.weight_smooth i₁ z hi₁) (L₂.weight_smooth i₂ z hi₂) w

theorem chernFirstForm_tensor (L₁ : MetrizedLineBundle d ι₁ X) (L₂ : MetrizedLineBundle d ι₂ X)
    {z : Fin d → ℂ} (hz : z ∈ X) (w : Fin d → ℂ) :
    (ChernFirstForm (L₁.tensor L₂)).eval z w =
      (ChernFirstForm L₁ + ChernFirstForm L₂).eval z w := by
  simp only [ChernFirstForm, HermitianCurvatureForm.smul_eval, HermitianCurvatureForm.add_eval,
    curvatureForm, curvatureAt_tensor L₁ L₂ hz w]
  ring

theorem curvatureAt_pow (L : MetrizedLineBundle d ι X) (k : ℤ) {z : Fin d → ℂ} (hz : z ∈ X)
    (w : Fin d → ℂ) :
    (L.pow k).curvatureAt z w = (k : ℝ) * L.curvatureAt z w := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  rw [(L.pow k).curvatureAt_eq_of_mem hi, L.curvatureAt_eq_of_mem hi]
  exact leviForm_const_mul (k : ℝ) (L.weight_smooth i z hi) w

theorem chernFirstForm_pow (L : MetrizedLineBundle d ι X) (k : ℤ) {z : Fin d → ℂ} (hz : z ∈ X)
    (w : Fin d → ℂ) :
    (ChernFirstForm (L.pow k)).eval z w = ((k : ℝ) • ChernFirstForm L).eval z w := by
  simp only [ChernFirstForm, HermitianCurvatureForm.smul_eval, curvatureForm,
    L.curvatureAt_pow k hz w]
  ring

/-- **Exact Chern–Weil Metric-Change Formula**:
$$c_1(L, e^{-u} h) = c_1(L, h) + \frac{1}{\pi}\, \operatorname{levi}(u).$$ -/
theorem chernFirstForm_twistMetric (L : MetrizedLineBundle d ι X) (u : (Fin d → ℂ) → ℝ)
    (hu : ∀ i, ∀ z ∈ L.openCover i, ContDiffAt ℝ 2 u z) {z : Fin d → ℂ} (hz : z ∈ X)
    (w : Fin d → ℂ) :
    (ChernFirstForm (L.twistMetric u hu)).eval z w =
      (ChernFirstForm L).eval z w + (1 / Real.pi) * leviForm u z w := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  rw [chernFirstForm_eval_eq_of_mem (L.twistMetric u hu) hi,
    chernFirstForm_eval_eq_of_mem L hi]
  change (1 / Real.pi) * leviForm (fun y => L.weight i y + u y) z w = _
  rw [leviForm_add (L.weight_smooth i z hi) (hu i z hi) w]
  ring

/-- Constant metric rescaling leaves `ChernFirstForm` invariant. -/
theorem chernFirstForm_scaleMetric (L : MetrizedLineBundle d ι X) (c : ℝ) {z : Fin d → ℂ}
    (hz : z ∈ X) (w : Fin d → ℂ) :
    (ChernFirstForm (L.scaleMetric c)).eval z w = (ChernFirstForm L).eval z w := by
  rw [scaleMetric, chernFirstForm_twistMetric L (fun _ => c) _ hz w, leviForm_const, mul_zero,
    add_zero]

/-- Exact curvature interpolation along `lerpMetric`. -/
theorem curvatureAt_lerpMetric (L₀ L₁ : MetrizedLineBundle d ι X)
    (hcov : L₀.openCover = L₁.openCover) (htrans : L₀.transFn = L₁.transFn) (t : ℝ)
    {z : Fin d → ℂ} (hz : z ∈ X) (w : Fin d → ℂ) :
    (lerpMetric L₀ L₁ hcov htrans t).curvatureAt z w =
      (1 - t) * L₀.curvatureAt z w + t * L₁.curvatureAt z w := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L₀.covers hz)
  have hi1 : z ∈ L₁.openCover i := by rwa [← hcov]
  rw [(lerpMetric L₀ L₁ hcov htrans t).curvatureAt_eq_of_mem hi,
    L₀.curvatureAt_eq_of_mem hi, L₁.curvatureAt_eq_of_mem hi1]
  exact leviForm_add_smul (1 - t) t (L₀.weight_smooth i z hi) (L₁.weight_smooth i z hi1) w

/-! ### Curvature Positivity & Seminegativity Duality / Cone Theorems -/

theorem seminegativeMetric_iff_dual_semipositive (L : MetrizedLineBundle d ι X) :
    SeminegativeMetric L ↔ SemipositiveMetric L.dual := by
  constructor
  · intro h z hz w
    show 0 ≤ L.dual.curvatureAt z w
    rw [L.curvatureAt_dual hz w]
    have h1 : L.curvatureAt z w ≤ 0 := h z hz w
    linarith
  · intro h z hz w
    show L.curvatureAt z w ≤ 0
    have h1 : 0 ≤ L.dual.curvatureAt z w := h z hz w
    rw [L.curvatureAt_dual hz w] at h1
    linarith

theorem posCurvatureMetric_iff_dual_negCurvature (L : MetrizedLineBundle d ι X) :
    PosCurvatureMetric L ↔ NegCurvatureMetric L.dual := by
  constructor
  · intro h z hz w hw
    show L.dual.curvatureAt z w < 0
    rw [L.curvatureAt_dual hz w]
    have h1 : 0 < L.curvatureAt z w := h z hz w hw
    linarith
  · intro h z hz w hw
    show 0 < L.curvatureAt z w
    have h1 : L.dual.curvatureAt z w < 0 := h z hz w hw
    rw [L.curvatureAt_dual hz w] at h1
    linarith

theorem semipositiveMetric_tensor {L₁ : MetrizedLineBundle d ι₁ X}
    {L₂ : MetrizedLineBundle d ι₂ X}
    (h₁ : SemipositiveMetric L₁) (h₂ : SemipositiveMetric L₂) :
    SemipositiveMetric (L₁.tensor L₂) := by
  intro z hz w
  show 0 ≤ (L₁.tensor L₂).curvatureAt z w
  rw [curvatureAt_tensor L₁ L₂ hz w]
  exact add_nonneg (h₁ z hz w) (h₂ z hz w)

theorem posCurvatureMetric_tensor_semipositive {L₁ : MetrizedLineBundle d ι₁ X}
    {L₂ : MetrizedLineBundle d ι₂ X}
    (h₁ : PosCurvatureMetric L₁) (h₂ : SemipositiveMetric L₂) :
    PosCurvatureMetric (L₁.tensor L₂) := by
  intro z hz w hw
  show 0 < (L₁.tensor L₂).curvatureAt z w
  rw [curvatureAt_tensor L₁ L₂ hz w]
  exact add_pos_of_pos_of_nonneg (h₁ z hz w hw) (h₂ z hz w)

theorem seminegativeMetric_tensor {L₁ : MetrizedLineBundle d ι₁ X}
    {L₂ : MetrizedLineBundle d ι₂ X}
    (h₁ : SeminegativeMetric L₁) (h₂ : SeminegativeMetric L₂) :
    SeminegativeMetric (L₁.tensor L₂) := by
  intro z hz w
  show (L₁.tensor L₂).curvatureAt z w ≤ 0
  rw [curvatureAt_tensor L₁ L₂ hz w]
  exact add_nonpos (h₁ z hz w) (h₂ z hz w)

theorem semipositiveMetric_pow_of_nonneg {L : MetrizedLineBundle d ι X}
    (hL : SemipositiveMetric L) {k : ℤ} (hk : 0 ≤ k) :
    SemipositiveMetric (L.pow k) := by
  intro z hz w
  show 0 ≤ (L.pow k).curvatureAt z w
  rw [L.curvatureAt_pow k hz w]
  exact mul_nonneg (by exact_mod_cast hk) (hL z hz w)

theorem posCurvatureMetric_pow_of_pos {L : MetrizedLineBundle d ι X}
    (hL : PosCurvatureMetric L) {k : ℤ} (hk : 0 < k) :
    PosCurvatureMetric (L.pow k) := by
  intro z hz w hw
  show 0 < (L.pow k).curvatureAt z w
  rw [L.curvatureAt_pow k hz w]
  exact mul_pos (by exact_mod_cast hk) (hL z hz w hw)

theorem seminegativeMetric_pow_of_nonpos {L : MetrizedLineBundle d ι X}
    (hL : SemipositiveMetric L) {k : ℤ} (hk : k ≤ 0) :
    SeminegativeMetric (L.pow k) := by
  intro z hz w
  show (L.pow k).curvatureAt z w ≤ 0
  rw [L.curvatureAt_pow k hz w]
  exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hk) (hL z hz w)

theorem semipositiveMetric_lerp {L₀ L₁ : MetrizedLineBundle d ι X}
    (hcov : L₀.openCover = L₁.openCover) (htrans : L₀.transFn = L₁.transFn)
    (h₀ : SemipositiveMetric L₀) (h₁ : SemipositiveMetric L₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    SemipositiveMetric (lerpMetric L₀ L₁ hcov htrans t) := by
  intro z hz w
  show 0 ≤ (lerpMetric L₀ L₁ hcov htrans t).curvatureAt z w
  rw [curvatureAt_lerpMetric L₀ L₁ hcov htrans t hz w]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (h₀ z hz w)) (mul_nonneg ht0 (h₁ z hz w))

theorem posCurvatureMetric_lerp {L₀ L₁ : MetrizedLineBundle d ι X}
    (hcov : L₀.openCover = L₁.openCover) (htrans : L₀.transFn = L₁.transFn)
    (h₀ : PosCurvatureMetric L₀) (h₁ : PosCurvatureMetric L₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    PosCurvatureMetric (lerpMetric L₀ L₁ hcov htrans t) := by
  intro z hz w hw
  show 0 < (lerpMetric L₀ L₁ hcov htrans t).curvatureAt z w
  rw [curvatureAt_lerpMetric L₀ L₁ hcov htrans t hz w]
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simp only [sub_zero, one_mul, zero_mul, add_zero]; exact h₀ z hz w hw
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) (h₀ z hz w hw).le)
      (mul_pos htpos (h₁ z hz w hw))

/-! ### Global Holomorphic Sections, Chart-Independent Norm, & Pointwise Poincaré–Lelong -/

/-- A concrete **holomorphic global section** `s ∈ H⁰(X, L)` of a metrized line bundle `L`. -/
structure Section (L : MetrizedLineBundle d ι X) where
  /-- Local holomorphic representative `s_i` on chart `U_i`. -/
  sec : ι → (Fin d → ℂ) → ℂ
  /-- Holomorphicity (`C²`) of `s_i` on `U_i`. -/
  sec_holo : ∀ i, ∀ z ∈ L.openCover i, ContDiffAt ℂ 2 (sec i) z
  /-- Cocycle gluing `s_i(z) = g_{ij}(z) · s_j(z)` on `U_i ∩ U_j`. -/
  sec_compat : ∀ i j, ∀ z ∈ L.openCover i ∩ L.openCover j,
    sec i z = L.transFn i j z * sec j z

namespace Section

variable {L : MetrizedLineBundle d ι X}

/-- Chart-independence of the pointwise Hermitian norm squared `‖s_i(z)‖² exp(-φ_i(z))`. -/
theorem ptNormSq_chart_eq (s : Section L) {i j : ι} {z : Fin d → ℂ}
    (hi : z ∈ L.openCover i) (hj : z ∈ L.openCover j) :
    ‖s.sec i z‖ ^ 2 * Real.exp (-L.weight i z) =
      ‖s.sec j z‖ ^ 2 * Real.exp (-L.weight j z) := by
  rw [s.sec_compat i j z ⟨hi, hj⟩, norm_mul, mul_pow]
  have hcomp := L.weight_compat i j z ⟨hi, hj⟩
  have hwi : -L.weight i z = -Real.log (‖L.transFn i j z‖ ^ 2) + -L.weight j z := by linarith
  have hg_ne : ‖L.transFn i j z‖ ≠ 0 := norm_ne_zero_iff.mpr (L.transFn_ne_zero i j z ⟨hi, hj⟩)
  have hpos : 0 < ‖L.transFn i j z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (L.transFn_ne_zero i j z ⟨hi, hj⟩))
  rw [hwi, Real.exp_add, Real.exp_neg, Real.exp_log hpos]
  field_simp [hg_ne]

/-- Global pointwise Hermitian norm squared `‖s(z)‖²_h`. -/
def ptNormSq (s : Section L) (z : Fin d → ℂ) : ℝ :=
  if h : ∃ i, z ∈ L.openCover i then ‖s.sec h.choose z‖ ^ 2 * Real.exp (-L.weight h.choose z) else 0

/-- Global pointwise Hermitian norm `‖s(z)‖_h = √(‖s(z)‖²_h)`. -/
def ptNorm (s : Section L) (z : Fin d → ℂ) : ℝ :=
  Real.sqrt (s.ptNormSq z)

theorem ptNormSq_eq_of_mem (s : Section L) {i : ι} {z : Fin d → ℂ} (hi : z ∈ L.openCover i) :
    s.ptNormSq z = ‖s.sec i z‖ ^ 2 * Real.exp (-L.weight i z) := by
  unfold ptNormSq
  have hex : ∃ k, z ∈ L.openCover k := ⟨i, hi⟩
  rw [dif_pos hex]
  exact s.ptNormSq_chart_eq hex.choose_spec hi

theorem ptNormSq_nonneg (s : Section L) (z : Fin d → ℂ) : 0 ≤ s.ptNormSq z := by
  unfold ptNormSq
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  · exact le_rfl

/-- Nonvanishing predicate for a section `s` at `z ∈ X`. -/
def NonzeroAt (s : Section L) (z : Fin d → ℂ) : Prop :=
  ∃ i, z ∈ L.openCover i ∧ s.sec i z ≠ 0

theorem nonzeroAt_iff_ptNormSq_pos (s : Section L) {z : Fin d → ℂ} (hz : z ∈ X) :
    s.NonzeroAt z ↔ 0 < s.ptNormSq z := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  constructor
  · rintro ⟨j, hj, hne⟩
    rw [s.ptNormSq_eq_of_mem hj]
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hne)) (Real.exp_pos _)
  · intro hpos
    rw [s.ptNormSq_eq_of_mem hi] at hpos
    refine ⟨i, hi, fun h0 => ?_⟩
    simp [h0] at hpos

/-- **Pointwise Poincaré–Lelong Away from Zeros (Arbitrary Dimension `d`)**:
at every point `z ∈ X` where a holomorphic section `s` of `(L, h)` does not vanish,
$$\operatorname{leviForm}(\log \|s\|_h^2)(z, w) = -\Theta(L, h)_z(w, w), \qquad
  \frac{1}{\pi}\operatorname{leviForm}(\log \|s\|_h^2)(z, w) = -c_1(L, h)_z(w, w).$$ -/
theorem leviForm_log_ptNormSq_eq_neg_curvature (s : Section L) {z : Fin d → ℂ}
    (hsnz : s.NonzeroAt z) (w : Fin d → ℂ) :
    leviForm (fun y => Real.log (s.ptNormSq y)) z w = -L.curvatureAt z w ∧
    (1 / Real.pi) * leviForm (fun y => Real.log (s.ptNormSq y)) z w =
      -(ChernFirstForm L).eval z w := by
  rcases hsnz with ⟨i, hi, hne⟩
  have hcont : ContinuousAt (s.sec i) z := (s.sec_holo i z hi).continuousAt
  have hne_ev : ∀ᶠ y in 𝓝 z, s.sec i y ≠ 0 :=
    hcont.eventually (isOpen_ne.mem_nhds hne)
  have hev : (fun y => Real.log (s.ptNormSq y)) =ᶠ[𝓝 z]
      fun y => Real.log (‖s.sec i y‖ ^ 2) - L.weight i y := by
    filter_upwards [(L.isOpen_cover i).mem_nhds hi, hne_ev] with y hyi hyne
    rw [s.ptNormSq_eq_of_mem hyi,
      Real.log_mul (sq_pos_of_pos (norm_pos_iff.mpr hyne)).ne' (Real.exp_pos _).ne',
      Real.log_exp]
    ring
  have hlog_cd : ContDiffAt ℝ 2 (fun y => Real.log (‖s.sec i y‖ ^ 2)) z :=
    (contDiffAt_norm_sq_of_holo (s.sec_holo i z hi)).log
      (sq_pos_of_pos (norm_pos_iff.mpr hne)).ne'
  have hcurv : leviForm (fun y => Real.log (s.ptNormSq y)) z w = -L.curvatureAt z w := by
    rw [leviForm_congr_of_eventuallyEq hev w,
      leviForm_sub hlog_cd (L.weight_smooth i z hi) w,
      leviForm_log_norm_sq_holomorphic (s.sec_holo i z hi) hne w,
      L.curvatureAt_eq_of_mem hi]
    ring
  refine ⟨hcurv, ?_⟩
  rw [hcurv]
  simp only [ChernFirstForm, HermitianCurvatureForm.smul_eval, curvatureForm]
  ring

/-- Tensor product of global holomorphic sections `s₁ ⊗ s₂ ∈ H⁰(X, L₁ ⊗ L₂)`. -/
def mul {L₁ : MetrizedLineBundle d ι₁ X} {L₂ : MetrizedLineBundle d ι₂ X}
    (s₁ : Section L₁) (s₂ : Section L₂) : Section (L₁.tensor L₂) where
  sec p z := s₁.sec p.1 z * s₂.sec p.2 z
  sec_holo p z hz := (s₁.sec_holo p.1 z hz.1).mul (s₂.sec_holo p.2 z hz.2)
  sec_compat p q z hz := by
    rw [s₁.sec_compat p.1 q.1 z ⟨hz.1.1, hz.2.1⟩, s₂.sec_compat p.2 q.2 z ⟨hz.1.2, hz.2.2⟩]
    change _ = L₁.transFn p.1 q.1 z * L₂.transFn p.2 q.2 z * (s₁.sec q.1 z * s₂.sec q.2 z)
    ring

theorem ptNormSq_mul {L₁ : MetrizedLineBundle d ι₁ X} {L₂ : MetrizedLineBundle d ι₂ X}
    (s₁ : Section L₁) (s₂ : Section L₂) {z : Fin d → ℂ} (hz : z ∈ X) :
    (s₁.mul s₂).ptNormSq z = s₁.ptNormSq z * s₂.ptNormSq z := by
  obtain ⟨i₁, hi₁⟩ := Set.mem_iUnion.mp (L₁.covers hz)
  obtain ⟨i₂, hi₂⟩ := Set.mem_iUnion.mp (L₂.covers hz)
  rw [(s₁.mul s₂).ptNormSq_eq_of_mem (i := (i₁, i₂)) ⟨hi₁, hi₂⟩,
    s₁.ptNormSq_eq_of_mem hi₁, s₂.ptNormSq_eq_of_mem hi₂]
  change ‖s₁.sec i₁ z * s₂.sec i₂ z‖ ^ 2 * Real.exp (-(L₁.weight i₁ z + L₂.weight i₂ z)) = _
  rw [norm_mul, mul_pow, neg_add, Real.exp_add]
  ring

/-- Natural tensor power `s^{⊗ n} ∈ H⁰(X, L^{⊗ n})` of a section. -/
def pow (s : Section L) (n : ℕ) : Section (L.pow (n : ℤ)) where
  sec i z := s.sec i z ^ n
  sec_holo i z hz := (s.sec_holo i z hz).pow n
  sec_compat i j z hz := by
    rw [s.sec_compat i j z hz, mul_pow]
    simp [MetrizedLineBundle.pow]

theorem ptNormSq_pow (s : Section L) (n : ℕ) {z : Fin d → ℂ} (hz : z ∈ X) :
    (s.pow n).ptNormSq z = (s.ptNormSq z) ^ n := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  rw [(s.pow n).ptNormSq_eq_of_mem hi, s.ptNormSq_eq_of_mem hi]
  change ‖s.sec i z ^ n‖ ^ 2 * Real.exp (-(((n : ℤ) : ℝ) * L.weight i z)) = _
  rw [norm_pow, mul_pow, ← Real.exp_nat_mul]
  congr 1
  · ring
  · congr 1
    simp only [Int.cast_natCast]
    ring

/-- Complex scalar multiple `c • s` of a section. -/
def smul (c : ℂ) (s : Section L) : Section L where
  sec i z := c * s.sec i z
  sec_holo i z hz := contDiffAt_const.mul (s.sec_holo i z hz)
  sec_compat i j z hz := by rw [s.sec_compat i j z hz]; ring

theorem ptNormSq_smul (c : ℂ) (s : Section L) {z : Fin d → ℂ} (hz : z ∈ X) :
    (s.smul c).ptNormSq z = ‖c‖ ^ 2 * s.ptNormSq z := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  rw [(s.smul c).ptNormSq_eq_of_mem hi, s.ptNormSq_eq_of_mem hi]
  change ‖c * s.sec i z‖ ^ 2 * Real.exp (-L.weight i z) = _
  rw [norm_mul, mul_pow]
  ring

end Section

end MetrizedLineBundle

/-! ### Concrete Fubini–Study (`PosCurvatureMetric`) & Holomorphic Subbundle (`SeminegativeMetric`) -/

/-- Fubini–Study Kähler potential `φ_FS(z) = log(1 + ∑_j ‖z_j‖²)` on affine `ℂ^d ⊂ ℙ^d`. -/
def fubiniStudyWeight (d : ℕ) (z : Fin d → ℂ) : ℝ :=
  Real.log (1 + ∑ j : Fin d, ‖z j‖ ^ 2)

/-- `C²` smoothness of `fubiniStudyWeight` everywhere on `ℂ^d`. -/
lemma contDiffAt_fubiniStudyWeight (d : ℕ) (z : Fin d → ℂ) :
    ContDiffAt ℝ 2 (fubiniStudyWeight d) z := by
  have hpos : 0 < 1 + ∑ j : Fin d, ‖z j‖ ^ 2 := by
    have hnn : 0 ≤ ∑ j : Fin d, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hsum : ContDiffAt ℝ 2 (fun y : Fin d → ℂ => ∑ j : Fin d, ‖y j‖ ^ 2) z :=
    ContDiffAt.sum fun j _ =>
      contDiffAt_norm_sq_of_holo
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).contDiff.contDiffAt)
  exact (contDiffAt_const.add hsum).log hpos.ne'

/-- Concrete **Fubini–Study Metrized Line Bundle** `O(1)|_{ℂ^d}` (directly ready for
`ChowFormHeights`, `GagaAndSections`, & `NefRiemannRoch`). -/
def fubiniStudyLineBundle (d : ℕ) : MetrizedLineBundle d Unit Set.univ :=
  MetrizedLineBundle.trivial d Set.univ isOpen_univ (fubiniStudyWeight d)
    (fun z _ => contDiffAt_fubiniStudyWeight d z)

/-- **Exact Fubini–Study Curvature Formula**:
$$\operatorname{leviForm}(\varphi_{\mathrm{FS}})(z, w)
  = \frac{(1 + \|z\|^2)\|w\|^2 - |\langle w, z \rangle|^2}{(1 + \|z\|^2)^2}.$$ -/
theorem fubiniStudy_curvature_exact (d : ℕ) (z w : Fin d → ℂ) :
    (fubiniStudyLineBundle d).curvatureAt z w =
      ((1 + ∑ j : Fin d, ‖z j‖ ^ 2) * (∑ j : Fin d, ‖w j‖ ^ 2) -
        ‖∑ j : Fin d, w j * conj (z j)‖ ^ 2) /
        (1 + ∑ j : Fin d, ‖z j‖ ^ 2) ^ 2 := by
  unfold fubiniStudyLineBundle
  rw [MetrizedLineBundle.trivial_curvatureAt isOpen_univ _ _ (Set.mem_univ z) w]
  let f : Fin (d + 1) → (Fin d → ℂ) → ℂ :=
    Fin.cons (fun _ => (1 : ℂ)) (fun j y => y j)
  have hf : ∀ k : Fin (d + 1), ContDiffAt ℂ 2 (f k) z := by
    refine Fin.cases ?_ ?_
    · exact contDiffAt_const
    · intro j
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).contDiff.contDiffAt
  have hsum_eq : ∀ y : Fin d → ℂ, (∑ k : Fin (d + 1), ‖f k y‖ ^ 2) = 1 + ∑ j : Fin d, ‖y j‖ ^ 2 := by
    intro y
    rw [Fin.sum_univ_succ]
    simp [f]
  have hpos : 0 < ∑ k : Fin (d + 1), ‖f k z‖ ^ 2 := by
    rw [hsum_eq]
    have hnn : 0 ≤ ∑ j : Fin d, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hfun : fubiniStudyWeight d = fun y => Real.log (∑ k : Fin (d + 1), ‖f k y‖ ^ 2) := by
    funext y; unfold fubiniStudyWeight; rw [hsum_eq]
  rw [hfun, leviForm_log_sum_norm_sq_eq f hf hpos w, hsum_eq]
  have hderiv0 : fderiv ℂ (f 0) z w = 0 := by
    change fderiv ℂ (fun _ : Fin d → ℂ => (1 : ℂ)) z w = 0
    simp
  have hderiv_succ : ∀ j : Fin d, fderiv ℂ (f j.succ) z w = w j := by
    intro j
    change fderiv ℂ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j) z w = w j
    simp
  have hS1 : (∑ k : Fin (d + 1), ‖fderiv ℂ (f k) z w‖ ^ 2) = ∑ j : Fin d, ‖w j‖ ^ 2 := by
    rw [Fin.sum_univ_succ, hderiv0]
    simp [hderiv_succ]
  have hS2 : (∑ k : Fin (d + 1), fderiv ℂ (f k) z w * conj (f k z)) =
      ∑ j : Fin d, w j * conj (z j) := by
    rw [Fin.sum_univ_succ, hderiv0, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hderiv_succ j]
    rfl
  rw [hS1, hS2]

/-- **Strict Positivity of the Fubini–Study Metric (`PosCurvatureMetric`)** in every dimension `d`. -/
theorem fubiniStudy_posCurvature (d : ℕ) : PosCurvatureMetric (fubiniStudyLineBundle d) := by
  intro z _ w hw
  show 0 < (fubiniStudyLineBundle d).curvatureAt z w
  rw [fubiniStudy_curvature_exact]
  have hden_pos : 0 < (1 + ∑ j : Fin d, ‖z j‖ ^ 2) ^ 2 := by
    have hnn : 0 ≤ ∑ j : Fin d, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity
  refine div_pos ?_ hden_pos
  have hw_pos : 0 < ∑ j : Fin d, ‖w j‖ ^ 2 := by
    have hex : ∃ j : Fin d, w j ≠ 0 := by
      by_contra hall; push Not at hall; exact hw (funext hall)
    rcases hex with ⟨j₀, hj₀⟩
    exact Finset.sum_pos' (fun j _ => sq_nonneg _)
      ⟨j₀, Finset.mem_univ j₀, sq_pos_of_pos (norm_pos_iff.mpr hj₀)⟩
  have htri : ‖∑ j : Fin d, w j * conj (z j)‖ ≤ ∑ j : Fin d, ‖z j‖ * ‖w j‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_conj, mul_comm]
  have hsq : ‖∑ j : Fin d, w j * conj (z j)‖ ^ 2 ≤ (∑ j : Fin d, ‖z j‖ * ‖w j‖) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (∑ j : Fin d, w j * conj (z j))]) htri
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j : Fin d => ‖z j‖) (fun j : Fin d => ‖w j‖)
  nlinarith

/-- Concrete **Holomorphic Line Subbundle** of a flat trivial rank-`r` Hermitian bundle `ℂ^r`
generated by a nowhere-vanishing holomorphic frame `f : Fin r → (Fin d → ℂ) → ℂ` on open `X`,
with induced subbundle metric `h(z) = ∑_k ‖f_k(z)‖²` (`weight = -log h`). -/
def subbundleLineBundle {d r : ℕ} (X : Set (Fin d → ℂ)) (hX : IsOpen X)
    (f : Fin r → (Fin d → ℂ) → ℂ) (hf : ∀ k, ∀ z ∈ X, ContDiffAt ℂ 2 (f k) z)
    (hpos : ∀ z ∈ X, 0 < ∑ k : Fin r, ‖f k z‖ ^ 2) : MetrizedLineBundle d Unit X :=
  MetrizedLineBundle.trivial d X hX (fun y => -Real.log (∑ k : Fin r, ‖f k y‖ ^ 2))
    (fun z hz =>
      ((ContDiffAt.sum fun k _ => contDiffAt_norm_sq_of_holo (hf k z hz)).log
        (hpos z hz).ne').neg)

/-- **Griffiths Subbundle Seminegativity (`SeminegativeMetric`)**:
every holomorphic line subbundle of a flat Hermitian bundle carries a seminegative metric
(`c₁(S, h|_S) ≤ 0`), directly ready for `HodgeBundleExtension`! -/
theorem subbundle_metric_seminegative {d r : ℕ} (X : Set (Fin d → ℂ)) (hX : IsOpen X)
    (f : Fin r → (Fin d → ℂ) → ℂ) (hf : ∀ k, ∀ z ∈ X, ContDiffAt ℂ 2 (f k) z)
    (hpos : ∀ z ∈ X, 0 < ∑ k : Fin r, ‖f k z‖ ^ 2) :
    SeminegativeMetric (subbundleLineBundle X hX f hf hpos) := by
  intro z hz w
  show (subbundleLineBundle X hX f hf hpos).curvatureAt z w ≤ 0
  rw [subbundleLineBundle, MetrizedLineBundle.trivial_curvatureAt hX _ _ hz w]
  have hcd : ContDiffAt ℝ 2 (fun y => Real.log (∑ k : Fin r, ‖f k y‖ ^ 2)) z :=
    (ContDiffAt.sum fun k _ => contDiffAt_norm_sq_of_holo (hf k z hz)).log (hpos z hz).ne'
  rw [leviForm_neg hcd w]
  linarith [leviForm_log_sum_norm_sq_nonneg f (fun k => hf k z hz) (hpos z hz) w]

end MetrizedLineBundles

/-! ## Section 3: Theta, Siegel & Petersson Hermitian Metrics & `theta_metric_positivity` -/

section ThetaAndPeterssonMetrics

/-- A genus-`g` **Siegel Period Matrix** `Ω ∈ ℍ_g`: complex symmetric matrix whose imaginary part
`Y = Im Ω` is real symmetric positive-definite. -/
def IsSiegelPeriodMatrix {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) : Prop :=
  Ω.IsSymm ∧ (Ω.map Complex.im).PosDef

/-- Canonical **Theta Hermitian Metric Weight** on the complex abelian variety `ℂ^g / (ℤ^g + Ω ℤ^g)`:
$$\varphi_\Theta(z) = -\log h_\Theta(z) = 2\pi\, (\operatorname{Im} z)^T (\operatorname{Im}\Omega)^{-1} (\operatorname{Im} z).$$ -/
def thetaWeight {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℝ :=
  2 * Real.pi * ((fun j => (z j).im) ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec (fun j => (z j).im))

/-- Canonical **Theta Hermitian Metric** `h_Θ(z) = exp(-2π (Im z)^T (Im Ω)⁻¹ (Im z))`. -/
def thetaMetric {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℝ :=
  Real.exp (-thetaWeight Ω z)

/-- Exact real-coordinate evaluation of `thetaWeight` along `z = x + Ω y` (`x, y : Fin g → ℝ`):
`thetaWeight Ω (x + Ω y) = 2π (y ⬝ᵥ (Im Ω *ᵥ y))`, matching
`NormSqRiemannThetaMulExpPeriodic` verbatim! -/
theorem thetaWeight_real_coords {g : ℕ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hΩ : IsSiegelPeriodMatrix Ω) (x y : Fin g → ℝ) :
    thetaWeight Ω ((fun j => (x j : ℂ)) + Ω.mulVec (fun j => (y j : ℂ))) =
      2 * Real.pi * (y ⬝ᵥ (Ω.map Complex.im).mulVec y) := by
  set Y : Matrix (Fin g) (Fin g) ℝ := Ω.map Complex.im
  have him : (fun j : Fin g => (((fun k => (x k : ℂ)) + Ω.mulVec (fun k => (y k : ℂ))) j).im) =
      Y.mulVec y := by
    ext j
    simp only [Pi.add_apply, Complex.add_im, Complex.ofReal_im, zero_add, Matrix.mulVec, dotProduct,
      Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Y, Matrix.map_apply]
  have hYinv : Y⁻¹ * Y = 1 :=
    Matrix.nonsing_inv_mul Y (isUnit_iff_ne_zero.mpr hΩ.2.det_pos.ne')
  have hYT : Y.transpose = Y := isHermitian_real_transpose hΩ.2.isHermitian
  unfold thetaWeight
  change 2 * Real.pi * ((fun j => _) ⬝ᵥ Y⁻¹.mulVec (fun j => _)) = _
  rw [him, Matrix.mulVec_mulVec, hYinv, Matrix.one_mulVec, dotProduct_comm]

/-- `C²` smoothness of a quadratic form `z ↦ (Im z) ⬝ᵥ (A *ᵥ Im z)` on `ℂ^g`. -/
private lemma contDiff_im_quadForm {g : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) :
    ContDiff ℝ 2 (fun z : Fin g → ℂ => (fun j => (z j).im) ⬝ᵥ A.mulVec (fun j => (z j).im)) := by
  have heq : (fun z : Fin g → ℂ => (fun j => (z j).im) ⬝ᵥ A.mulVec (fun j => (z j).im)) =
      fun z => ∑ i : Fin g, ∑ j : Fin g, A i j * ((z i).im * (z j).im) := by
    funext z
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hi : ContDiff ℝ 2 (fun z : Fin g → ℂ => (z i).im) :=
    (Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) i)).contDiff
  have hj : ContDiff ℝ 2 (fun z : Fin g → ℂ => (z j).im) :=
    (Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin g => ℂ) j)).contDiff
  exact contDiff_const.mul (hi.mul hj)

/-- `C²` smoothness of `thetaWeight Ω` everywhere on `ℂ^g`. -/
lemma contDiff_thetaWeight {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) :
    ContDiff ℝ 2 (thetaWeight Ω) :=
  contDiff_const.mul (contDiff_im_quadForm (Ω.map Complex.im)⁻¹)

/-- Concrete **Theta Metrized Line Bundle** `L_Θ` on `ℂ^g` equipped with the canonical
Hermitian metric `h_Θ(z) = exp(-2π (Im z)^T (Im Ω)⁻¹ (Im z))`. -/
def thetaMetrizedLineBundle {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ) :
    MetrizedLineBundle g Unit Set.univ :=
  MetrizedLineBundle.trivial g Set.univ isOpen_univ (thetaWeight Ω)
    (fun _ _ => (contDiff_thetaWeight Ω).contDiffAt)

/-- **Exact Levi Curvature Form of the Theta Hermitian Metric in Arbitrary Genus `g`**:
$$\operatorname{leviForm}(\varphi_\Theta)(z, w)
  = \pi \Bigl((\operatorname{Re} w)^T (\operatorname{Im}\Omega)^{-1} (\operatorname{Re} w)
    + (\operatorname{Im} w)^T (\operatorname{Im}\Omega)^{-1} (\operatorname{Im} w)\Bigr).$$ -/
theorem thetaWeight_leviForm_eq {g : ℕ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hΩ : IsSiegelPeriodMatrix Ω) (z w : Fin g → ℂ) :
    leviForm (thetaWeight Ω) z w =
      Real.pi * ((fun j => (w j).re) ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec (fun j => (w j).re) +
        (fun j => (w j).im) ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec (fun j => (w j).im)) := by
  set A : Matrix (Fin g) (Fin g) ℝ := (Ω.map Complex.im)⁻¹
  have hAT : A.transpose = A := by
    rw [Matrix.transpose_nonsing_inv, isHermitian_real_transpose hΩ.2.isHermitian]
  have hsym : ∀ u v : Fin g → ℝ, u ⬝ᵥ A.mulVec v = v ⬝ᵥ A.mulVec u := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAT, dotProduct_comm]
  have hline : ∀ e : Fin g → ℂ,
      deriv (deriv fun s : ℝ => thetaWeight Ω (z + s • e)) 0 =
        4 * Real.pi * ((fun j => (e j).im) ⬝ᵥ A.mulVec (fun j => (e j).im)) := by
    intro e
    set u : Fin g → ℝ := fun j => (z j).im
    set v : Fin g → ℝ := fun j => (e j).im
    have hpoly : (fun s : ℝ => thetaWeight Ω (z + s • e)) =
        fun s : ℝ => (2 * Real.pi * (u ⬝ᵥ A.mulVec u)) +
          (4 * Real.pi * (u ⬝ᵥ A.mulVec v)) * s +
          (2 * Real.pi * (v ⬝ᵥ A.mulVec v)) * s ^ 2 := by
      funext s
      unfold thetaWeight
      have him : (fun j : Fin g => ((z + s • e) j).im) = u + s • v := by
        ext j; simp [u, v]
      change 2 * Real.pi * ((fun j => ((z + s • e) j).im) ⬝ᵥ A.mulVec (fun j => ((z + s • e) j).im)) = _
      rw [him, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
        dotProduct_add, dotProduct_smul, smul_dotProduct, smul_dotProduct, dotProduct_smul,
        hsym v u]
      ring
    rw [hpoly]
    set c₀ := 2 * Real.pi * (u ⬝ᵥ A.mulVec u)
    set c₁ := 4 * Real.pi * (u ⬝ᵥ A.mulVec v)
    set c₂ := 2 * Real.pi * (v ⬝ᵥ A.mulVec v)
    have hd1 : (deriv fun s : ℝ => c₀ + c₁ * s + c₂ * s ^ 2) = fun s : ℝ => c₁ + 2 * c₂ * s := by
      funext s
      have h1 : HasDerivAt (fun t : ℝ => c₀ + c₁ * t + c₂ * t ^ 2)
          (0 + c₁ * 1 + c₂ * (2 * s ^ 1)) s :=
        ((hasDerivAt_const s c₀).add ((hasDerivAt_id s).const_mul c₁)).add
          ((hasDerivAt_pow 2 s).const_mul c₂)
      rw [h1.deriv]; ring
    rw [hd1]
    have hd2 : HasDerivAt (fun s : ℝ => c₁ + 2 * c₂ * s) (0 + 2 * c₂ * 1) 0 :=
      (hasDerivAt_const (0 : ℝ) c₁).add ((hasDerivAt_id (0 : ℝ)).const_mul (2 * c₂))
    rw [hd2.deriv]
    dsimp only [c₂]
    ring
  have hcd := (contDiff_thetaWeight Ω).contDiffAt (x := z)
  have hIw_im : (fun j : Fin g => ((Complex.I • w) j).im) = fun j => (w j).re := by
    ext j; simp
  unfold leviForm
  rw [← deriv_deriv_line hcd w, ← deriv_deriv_line hcd (Complex.I • w),
    hline w, hline (Complex.I • w), hIw_im]
  ring

/-- **Exact First Chern Form of the Theta Line Bundle**:
equals the Riemann–Hodge polarization Kähler form `(Re w)^T Y⁻¹ (Re w) + (Im w)^T Y⁻¹ (Im w)`. -/
theorem thetaLineBundle_chernFirstForm_eq {g : ℕ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hΩ : IsSiegelPeriodMatrix Ω) (z w : Fin g → ℂ) :
    (ChernFirstForm (thetaMetrizedLineBundle Ω)).eval z w =
      (fun j => (w j).re) ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec (fun j => (w j).re) +
        (fun j => (w j).im) ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec (fun j => (w j).im) := by
  rw [chernFirstForm_eval_eq_of_mem (thetaMetrizedLineBundle Ω) (i := ()) (Set.mem_univ z) w]
  change (1 / Real.pi) * leviForm (thetaWeight Ω) z w = _
  rw [thetaWeight_leviForm_eq hΩ z w]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]

/-- **`theta_metric_positivity` (Positivity of the Curvature of the Theta Hermitian Metric)**:
for every genus `g` and every Siegel period matrix `Ω ∈ ℍ_g`, the canonical theta Hermitian line
bundle `(L_Θ, h_Θ)` has **strictly positive curvature** (`PosCurvatureMetric`). -/
theorem theta_metric_positivity {g : ℕ} {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hΩ : IsSiegelPeriodMatrix Ω) :
    PosCurvatureMetric (thetaMetrizedLineBundle Ω) := by
  have hinv_pd : (Ω.map Complex.im)⁻¹.PosDef := posDef_inv hΩ.2
  intro z _ w hw
  show 0 < (thetaMetrizedLineBundle Ω).curvatureAt z w
  rw [thetaMetrizedLineBundle, MetrizedLineBundle.trivial_curvatureAt isOpen_univ _ _ (Set.mem_univ z) w,
    thetaWeight_leviForm_eq hΩ z w]
  set wr : Fin g → ℝ := fun j => (w j).re
  set wi : Fin g → ℝ := fun j => (w j).im
  have hre_nn : 0 ≤ wr ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec wr := by
    by_cases h0 : wr = 0
    · simp [h0]
    · exact (posDef_dotProduct_mulVec_pos hinv_pd h0).le
  have him_nn : 0 ≤ wi ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec wi := by
    by_cases h0 : wi = 0
    · simp [h0]
    · exact (posDef_dotProduct_mulVec_pos hinv_pd h0).le
  have hsum_pos : 0 < wr ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec wr +
      wi ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec wi := by
    by_cases h0 : wr = 0
    · have hi0 : wi ≠ 0 := by
        intro hi0
        apply hw
        funext j
        apply Complex.ext
        · exact congrFun h0 j
        · exact congrFun hi0 j
      linarith [posDef_dotProduct_mulVec_pos hinv_pd hi0]
    · linarith [posDef_dotProduct_mulVec_pos hinv_pd h0]
  exact mul_pos Real.pi_pos hsum_pos

/-- **Uniform Kähler Positivity of the Theta Hermitian Metric**:
there exists `c > 0` (given by `π · λ_min((Im Ω)⁻¹)`) such that
`c * ∑ ‖w_j‖² ≤ Θ(L_Θ, h_Θ)(z, w)` uniformly over all `z, w ∈ ℂ^g`. -/
theorem theta_metric_uniform_positivity {g : ℕ} (hg : 0 < g) {Ω : Matrix (Fin g) (Fin g) ℂ}
    (hΩ : IsSiegelPeriodMatrix Ω) :
    (thetaMetrizedLineBundle Ω).curvatureForm.IsUniformlyPositive := by
  have hinv_pd : (Ω.map Complex.im)⁻¹.PosDef := posDef_inv hΩ.2
  let H := hinv_pd.isHermitian
  have hne : (Finset.univ : Finset (Fin g)).Nonempty :=
    ⟨⟨0, hg⟩, Finset.mem_univ _⟩
  let lamMin : ℝ := Finset.univ.inf' hne H.eigenvalues
  have hlam_pos : 0 < lamMin := by
    rw [Finset.lt_inf'_iff]
    intro k _
    exact posDef_eigenvalues_pos hinv_pd k
  have hquad_ge : ∀ x : Fin g → ℝ, lamMin * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec x := by
    intro x
    let u := H.eigenvectorBasis
    let x' : EuclideanSpace ℝ (Fin g) := WithLp.toLp 2 x
    have hx_decomp : x' = ∑ k : Fin g, inner ℝ (u k) x' • u k := (u.sum_repr' x').symm
    have hAx : WithLp.toLp 2 ((Ω.map Complex.im)⁻¹.mulVec x) =
        ∑ k : Fin g, (H.eigenvalues k * inner ℝ (u k) x') • u k := by
      have hx_fun : x = ∑ k : Fin g, inner ℝ (u k) x' • (u k : Fin g → ℝ) := by
        ext i
        have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin g) => v i) hx_decomp
        have hsum_app : ∀ (s : Finset (Fin g)) (f : Fin g → EuclideanSpace ℝ (Fin g)),
            (∑ k ∈ s, f k) i = ∑ k ∈ s, (f k) i := by
          intro s f
          induction s using Finset.induction_on with
          | empty => simp
          | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]
        rw [hsum_app] at h1
        simpa [x', Finset.sum_apply] using h1
      ext i
      have hsum_app : ∀ (s : Finset (Fin g)) (f : Fin g → EuclideanSpace ℝ (Fin g)),
          (∑ k ∈ s, f k) i = ∑ k ∈ s, (f k) i := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]
      rw [WithLp.ofLp_toLp, hx_fun, Matrix.mulVec_sum, Finset.sum_apply, hsum_app]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
      have hmul := congrFun (H.mulVec_eigenvectorBasis k) i
      simp only [Pi.smul_apply, smul_eq_mul] at hmul
      change inner ℝ (u k) x' * ((Ω.map Complex.im)⁻¹.mulVec (u k) i) = _
      rw [hmul]
      ring
    have hinner_eq : x ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec x =
        ∑ k : Fin g, H.eigenvalues k * (inner ℝ (u k) x') ^ 2 := by
      have h1 : x ⬝ᵥ (Ω.map Complex.im)⁻¹.mulVec x =
          inner ℝ x' (WithLp.toLp 2 ((Ω.map Complex.im)⁻¹.mulVec x)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        simp only [star_trivial, dotProduct, x']
        refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [h1, hAx, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, real_inner_comm x' (u k)]
      ring
    have hparseval : ∑ k : Fin g, (inner ℝ (u k) x') ^ 2 = x ⬝ᵥ x := by
      have hp := u.sum_sq_inner_right x'
      have hns : ‖x'‖ ^ 2 = x ⬝ᵥ x := by
        rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct, x']
      have hp' : ∑ k : Fin g, (inner ℝ (u k) x') ^ 2 = ‖x'‖ ^ 2 := by
        simpa [real_inner_comm] using hp
      rw [hp', hns]
    have hle : ∑ k : Fin g, lamMin * (inner ℝ (u k) x') ^ 2 ≤
        ∑ k : Fin g, H.eigenvalues k * (inner ℝ (u k) x') ^ 2 :=
      Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_right (Finset.inf'_le H.eigenvalues (Finset.mem_univ k)) (sq_nonneg _)
    rw [← Finset.mul_sum, hparseval, ← hinner_eq] at hle
    exact hle
  refine ⟨Real.pi * lamMin, mul_pos Real.pi_pos hlam_pos, fun z _ w => ?_⟩
  show Real.pi * lamMin * ∑ j : Fin g, ‖w j‖ ^ 2 ≤ (thetaMetrizedLineBundle Ω).curvatureAt z w
  rw [thetaMetrizedLineBundle, MetrizedLineBundle.trivial_curvatureAt isOpen_univ _ _ (Set.mem_univ z) w,
    thetaWeight_leviForm_eq hΩ z w]
  have hsum_norm : (∑ j : Fin g, ‖w j‖ ^ 2) =
      ((fun j => (w j).re) ⬝ᵥ (fun j => (w j).re)) + ((fun j => (w j).im) ⬝ᵥ (fun j => (w j).im)) := by
    simp only [dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hsum_norm]
  have h1 := hquad_ge (fun j => (w j).re)
  have h2 := hquad_ge (fun j => (w j).im)
  nlinarith [Real.pi_pos]

/-! ### Concrete Petersson / Hodge Automorphic Line Bundle `ω^{⊗ k}` on `UpperHalfPlane` -/

/-- Open upper half-plane as a domain in `Fin 1 → ℂ`. -/
def uhpDomain1 : Set (Fin 1 → ℂ) :=
  { z : Fin 1 → ℂ | 0 < (z 0).im }

lemma isOpen_uhpDomain1 : IsOpen uhpDomain1 :=
  isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))

/-- Local Petersson / Hodge weight `φ_k(z) = -k * log(Im (z 0))` for `ω^{⊗ k}` on `ℍ`. -/
def peterssonWeight (k : ℤ) (z : Fin 1 → ℂ) : ℝ :=
  -(k : ℝ) * Real.log (z 0).im

lemma contDiffAt_peterssonWeight (k : ℤ) {z : Fin 1 → ℂ} (hz : z ∈ uhpDomain1) :
    ContDiffAt ℝ 2 (peterssonWeight k) z := by
  have him : ContDiffAt ℝ 2 (fun y : Fin 1 → ℂ => (y 0).im) z :=
    (Complex.imCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0)).contDiff.contDiffAt
  exact contDiffAt_const.mul (him.log hz.ne')

/-- Concrete **Petersson / Automorphic Hodge Metrized Line Bundle `ω^{⊗ k}`** on `UpperHalfPlane`
with Hermitian metric `h_k(τ) = (Im τ)^k` (`φ_k(τ) = -k log(Im τ)`). -/
def peterssonLineBundle (k : ℤ) : MetrizedLineBundle 1 Unit uhpDomain1 :=
  MetrizedLineBundle.trivial 1 uhpDomain1 isOpen_uhpDomain1 (peterssonWeight k)
    (fun _ hz => contDiffAt_peterssonWeight k hz)

/-- Exact identification of `(peterssonLineBundle k).curvatureAt` with
`Stage11HermitianCurvature.chernCurvatureCoeff k τ * ‖w 0‖²`. -/
theorem peterssonLineBundle_curvature_eq (k : ℤ) (τ : UpperHalfPlane) (w : Fin 1 → ℂ) :
    (peterssonLineBundle k).curvatureAt (fun _ => (τ : ℂ)) w =
      chernCurvatureCoeff k τ * ‖w 0‖ ^ 2 := by
  have hmem : (fun _ : Fin 1 => (τ : ℂ)) ∈ uhpDomain1 := τ.im_pos
  rw [peterssonLineBundle, MetrizedLineBundle.trivial_curvatureAt isOpen_uhpDomain1 _ _ hmem w]
  let T : (Fin 1 → ℂ) →L[ℂ] (Unit → ℂ) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0
  have hφ_cd : ContDiffAt ℝ 2 (uhpLift1D (fun u => -(k : ℝ) * Real.log u.im))
      (T (fun _ => (τ : ℂ))) := by
    have hopen : IsOpen uhpSet1D :=
      isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply ()))
    have hTτ : T (fun _ => (τ : ℂ)) = fun _ => (τ : ℂ) := rfl
    rw [hTτ]
    have hev : uhpLift1D (fun u => -(k : ℝ) * Real.log u.im) =ᶠ[𝓝 (fun _ : Unit => (τ : ℂ))]
        fun z : Unit → ℂ => -(k : ℝ) * Real.log (z ()).im := by
      filter_upwards [hopen.mem_nhds τ.im_pos] with z hz
      unfold uhpLift1D
      dsimp only
      have hof : (UpperHalfPlane.ofComplex (z ())).im = (z ()).im :=
        congrArg UpperHalfPlane.im (UpperHalfPlane.ofComplex_apply_of_im_pos hz)
      rw [hof]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have him : ContDiffAt ℝ 2 (fun z : Unit → ℂ => (z ()).im) (fun _ => (τ : ℂ)) :=
      (Complex.imCLM.comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℂ) ())).contDiff.contDiffAt
    exact contDiffAt_const.mul (him.log τ.im_pos.ne')
  have hev_eq : peterssonWeight k =ᶠ[𝓝 (fun _ : Fin 1 => (τ : ℂ))]
      fun y => uhpLift1D (fun u => -(k : ℝ) * Real.log u.im) (T y) := by
    filter_upwards [isOpen_uhpDomain1.mem_nhds hmem] with y hy
    unfold peterssonWeight uhpLift1D
    have hTy : T y () = y 0 := rfl
    rw [hTy]
    dsimp only
    have hof : (UpperHalfPlane.ofComplex (y 0)).im = (y 0).im :=
      congrArg UpperHalfPlane.im (UpperHalfPlane.ofComplex_apply_of_im_pos hy)
    rw [hof]
  rw [leviForm_congr_of_eventuallyEq hev_eq w, leviForm_comp_clm T hφ_cd w]
  change leviForm (uhpLift1D (fun u => -(k : ℝ) * Real.log u.im)) (fun _ => (τ : ℂ)) (fun _ => w 0) = _
  rw [leviForm_uhpLift1D hφ_cd (fun _ => w 0), euclLaplacianR_const_mul_log_im (-(k : ℝ)) τ,
    chernCurvature_weight_k_eq]
  ring

/-- Exact identification of `(ChernFirstForm (peterssonLineBundle k)).eval` with
`Stage11HermitianCurvature.firstChernDensity k τ * ‖w 0‖²`. -/
theorem peterssonLineBundle_chernFirstForm_eq (k : ℤ) (τ : UpperHalfPlane) (w : Fin 1 → ℂ) :
    (ChernFirstForm (peterssonLineBundle k)).eval (fun _ => (τ : ℂ)) w =
      firstChernDensity k τ * ‖w 0‖ ^ 2 := by
  simp only [ChernFirstForm, HermitianCurvatureForm.smul_eval, MetrizedLineBundle.curvatureForm]
  rw [peterssonLineBundle_curvature_eq, chernCurvature_weight_k_eq, firstChernDensity_weight_k_eq]
  ring

/-- **Strict Positivity of the Petersson / Hodge Metric (`k > 0`)**:
`PosCurvatureMetric (peterssonLineBundle k)` for every positive weight `k > 0`. -/
theorem petersson_metric_positivity {k : ℤ} (hk : 0 < k) :
    PosCurvatureMetric (peterssonLineBundle k) := by
  intro z hz w hw
  let τ : UpperHalfPlane := ⟨z 0, hz⟩
  have hz_eq : z = fun _ => (τ : ℂ) := by
    funext i; fin_cases i; rfl
  have hw0 : w 0 ≠ 0 := fun h0 => hw (by funext i; fin_cases i; exact h0)
  rw [hz_eq]
  show 0 < (peterssonLineBundle k).curvatureAt (fun _ => (τ : ℂ)) w
  rw [peterssonLineBundle_curvature_eq, chernCurvature_weight_k_eq]
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have him : 0 < τ.im ^ (-2 : ℝ) := Real.rpow_pos_of_pos τ.im_pos _
  have hwn : 0 < ‖w 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  positivity

/-- Semipositivity of the Petersson / Hodge metric for `k ≥ 0`. -/
theorem petersson_metric_semipositive {k : ℤ} (hk : 0 ≤ k) :
    SemipositiveMetric (peterssonLineBundle k) := by
  intro z hz w
  let τ : UpperHalfPlane := ⟨z 0, hz⟩
  have hz_eq : z = fun _ => (τ : ℂ) := by funext i; fin_cases i; rfl
  rw [hz_eq]
  show 0 ≤ (peterssonLineBundle k).curvatureAt (fun _ => (τ : ℂ)) w
  rw [peterssonLineBundle_curvature_eq, chernCurvature_weight_k_eq]
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have him : 0 < τ.im ^ (-2 : ℝ) := Real.rpow_pos_of_pos τ.im_pos _
  exact mul_nonneg (mul_nonneg (div_nonneg hkR (by norm_num)) him.le) (sq_nonneg _)

/-- Seminegativity of the Petersson / Hodge metric for `k ≤ 0`. -/
theorem petersson_metric_seminegative {k : ℤ} (hk : k ≤ 0) :
    SeminegativeMetric (peterssonLineBundle k) := by
  intro z hz w
  let τ : UpperHalfPlane := ⟨z 0, hz⟩
  have hz_eq : z = fun _ => (τ : ℂ) := by funext i; fin_cases i; rfl
  rw [hz_eq]
  show (peterssonLineBundle k).curvatureAt (fun _ => (τ : ℂ)) w ≤ 0
  rw [peterssonLineBundle_curvature_eq, chernCurvature_weight_k_eq]
  have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
  have him : 0 < τ.im ^ (-2 : ℝ) := Real.rpow_pos_of_pos τ.im_pos _
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hkR (by norm_num)) him.le)
    (sq_nonneg _)

/-- Combined **Theta × Petersson Product Metric Positivity**:
on `uhpDomain1`, twisting the weight-`k` (`k ≥ 0`) Petersson bundle by the genus-1 theta bundle
`thetaMetrizedLineBundle Ω` (`IsSiegelPeriodMatrix Ω`) yields a strictly positively curved
`MetrizedLineBundle`. -/
theorem theta_petersson_tensor_positivity {Ω : Matrix (Fin 1) (Fin 1) ℂ}
    (hΩ : IsSiegelPeriodMatrix Ω) {k : ℤ} (hk : 0 ≤ k) :
    PosCurvatureMetric
      ((MetrizedLineBundle.trivial 1 uhpDomain1 isOpen_uhpDomain1 (thetaWeight Ω)
        (fun _ _ => (contDiff_thetaWeight Ω).contDiffAt)).tensor (peterssonLineBundle k)) := by
  refine MetrizedLineBundle.posCurvatureMetric_tensor_semipositive ?_
    (petersson_metric_semipositive hk)
  intro z hz w hw
  have h := theta_metric_positivity hΩ z (Set.mem_univ z) w hw
  simpa [thetaMetrizedLineBundle, MetrizedLineBundle.curvatureForm,
    MetrizedLineBundle.trivial_curvatureAt, hz] using h

end ThetaAndPeterssonMetrics

/-! ## Section 4: Exact Green's Formula, Green's Second Identity & Distributional `poincare_lelong_equation` -/

section PoincareLelong

/-- Concrete Euclidean Laplacian on `ℂ`:
`laplacianC u z = D²u(z)(1, 1) + D²u(z)(I, I)`. -/
def laplacianC (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I

/-- Normalized `dd^c` density on `ℂ`:
$$\mathrm{dd}^c u(z) := \frac{1}{4\pi} \Delta u(z) = \frac{1}{\pi} \operatorname{levi}(u)(z, 1).$$
Normalized so that:
- `ddcDens φ z = c₁(φ)(z)` matches `Stage11HermitianCurvature.firstChernDensity`, and
- `∫ z : ℂ, Real.log (‖z - a‖ ^ 2) * ddcDens u z = u a`! -/
def ddcDens (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / (4 * Real.pi)) * laplacianC u z

/-- Directional first and second derivatives of a `C²` function `u : ℂ → ℝ` along `t ↦ z + t • e`. -/
private lemma hasDerivAt_complex_line {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (e : ℂ) :
    HasDerivAt (fun t : ℝ => u (z + t • e)) (fderiv ℝ u z e) 0 ∧
    HasDerivAt (fun t : ℝ => fderiv ℝ u (z + t • e) e) (fderiv ℝ (fderiv ℝ u) z e e) 0 := by
  have hp : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have h0 : z + (0 : ℝ) • e = z := by simp
  have h1 := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hp h0.symm
  have hu1 : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : HasFDerivAt (fun y : ℂ => fderiv ℝ u y e) ((fderiv ℝ (fderiv ℝ u) z).flip e) z := by
    simpa using hu1.hasFDerivAt.clm_apply (hasFDerivAt_const e z)
  have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ u (z + t • e) e) (fderiv ℝ (fderiv ℝ u) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq 0 hp h0.symm
  exact ⟨h1, h2⟩

/-- Exact compatibility between `leviForm` on `Fin 1 → ℂ` and `laplacianC` on `ℂ` for `C²` `u`. -/
theorem leviForm_fin1_eq_laplacianC {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    leviForm (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) =
      laplacianC u z / 4 := by
  have hcomp_cd : ContDiffAt ℝ 2 (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) :=
    hu.comp (fun _ => z)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).contDiff.contDiffAt
  have hline : ∀ e : ℂ,
      fderiv ℝ (fderiv ℝ (fun w : Fin 1 → ℂ => u (w 0))) (fun _ => z) (fun _ => e) (fun _ => e) =
        fderiv ℝ (fderiv ℝ u) z e e := by
    intro e
    rw [← deriv_deriv_line hcomp_cd (fun _ => e)]
    have hfun : (fun s : ℝ => u (((fun _ : Fin 1 => z) + s • (fun _ : Fin 1 => e)) 0)) =
        fun s : ℝ => u (z + s • e) := rfl
    rw [hfun]
    have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 (0 : ℝ)) (𝓝 z) := by
      have hc : Continuous (fun s : ℝ => z + s • e) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    have hd1 : deriv (fun s : ℝ => u (z + s • e)) =ᶠ[𝓝 (0 : ℝ)]
        fun s : ℝ => fderiv ℝ u (z + s • e) e := by
      filter_upwards [hcont.eventually (hu.eventually (by simp))] with s hs
      have hp : HasDerivAt (fun t : ℝ => z + t • e) e s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_add z
      exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hp).deriv
    rw [hd1.deriv_eq]
    exact (hasDerivAt_complex_line hu e).2.deriv
  have he1 : (Pi.single (0 : Fin 1) (1 : ℂ)) = fun _ => (1 : ℂ) := by
    funext i; fin_cases i; simp
  have heI : (Complex.I • Pi.single (0 : Fin 1) (1 : ℂ)) = fun _ => Complex.I := by
    funext i; fin_cases i; simp
  unfold leviForm laplacianC
  rw [heI, he1, hline 1, hline Complex.I]

/-- Exact compatibility `ddcDens u z = (1 / π) * leviForm (u ∘ proj₀) z e₀` for `C²` `u`. -/
theorem ddcDens_eq_inv_pi_mul_leviForm {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    ddcDens u z = (1 / Real.pi) * leviForm (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) := by
  rw [leviForm_fin1_eq_laplacianC hu]
  unfold ddcDens
  ring

/-- Vanishing of `laplacianC (log ‖g ·‖²)` away from zeros of holomorphic `g : ℂ → ℂ`. -/
theorem laplacianC_log_norm_sq_holomorphic {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℂ 2 g z)
    (hne : g z ≠ 0) :
    laplacianC (fun w => Real.log (‖g w‖ ^ 2)) z = 0 := by
  have hcomp : ContDiffAt ℂ 2 (fun w : Fin 1 → ℂ => g (w 0)) (fun _ => z) :=
    hg.comp (fun _ => z)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).contDiff.contDiffAt
  have hlog_cd : ContDiffAt ℝ 2 (fun w : ℂ => Real.log (‖g w‖ ^ 2)) z := by
    have hgR : ContDiffAt ℝ 2 g z := hg.restrict_scalars ℝ
    have heq : (fun y => ‖g y‖ ^ 2) = fun y => (g y * conj (g y)).re := by
      funext y; rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hns : ContDiffAt ℝ 2 (fun y => ‖g y‖ ^ 2) z := by
      rw [heq]
      exact Complex.reCLM.contDiff.contDiffAt.comp z
        (hgR.mul (Complex.conjCLE.contDiff.contDiffAt.comp z hgR))
    exact hns.log (sq_pos_of_pos (norm_pos_iff.mpr hne)).ne'
  have h0 := leviForm_log_norm_sq_holomorphic hcomp hne (Pi.single 0 1)
  have h1 := leviForm_fin1_eq_laplacianC hlog_cd
  linarith

/-! ### Part A: Green's Second Identity on Any Open `U ⊇ tsupport u` -/

/-- First and second Fréchet derivatives vanish outside `tsupport u`. -/
private lemma fderiv_eq_zero_of_notMem_tsupport {u : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport u) :
    u z = 0 ∧ fderiv ℝ u z = 0 ∧ fderiv ℝ (fderiv ℝ u) z = 0 := by
  have hopen : IsOpen (tsupport u)ᶜ := isClosed_tsupport u |>.isOpen_compl
  have hu_ev : u =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hfd_ev : fderiv ℝ u =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds hz] with y hy
    have hy_ev : u =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.eventually_of_mem (hopen.mem_nhds hy) fun x hx => image_eq_zero_of_notMem_tsupport hx
    rw [hy_ev.fderiv_eq]; simp
  refine ⟨image_eq_zero_of_notMem_tsupport hz, ?_, ?_⟩
  · rw [hu_ev.fderiv_eq]; simp
  · rw [hfd_ev.fderiv_eq]; simp

/-- 1D integration by parts `∫ t, φ(t) u''(t) = ∫ t, φ''(t) u(t)` along a horizontal or vertical
slice when `φ` is `C²` on an open `U ⊇ tsupport u` and `u` is `C²` with compact support! -/
private lemma integral_ibp_line_open {U : Set ℂ} (hU : IsOpen U) {φ u : ℂ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    (hsub : tsupport u ⊆ U) (z₀ e : ℂ) (he : e ≠ 0) :
    ∫ t : ℝ, φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e =
      ∫ t : ℝ, fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e) := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  set M : ℝ := (max R 0 + ‖z₀‖ + 1) / ‖e‖ + 1
  have he_pos : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hM_pos : 0 < M := by
    have h1 : 0 ≤ max R 0 := le_max_right R 0
    have h2 : 0 ≤ ‖z₀‖ := norm_nonneg z₀
    have h3 : 0 < (max R 0 + ‖z₀‖ + 1) / ‖e‖ := div_pos (by linarith) he_pos
    linarith
  have hout : ∀ t : ℝ, M ≤ |t| → z₀ + t • e ∉ tsupport u := by
    intro t ht hmem
    have hle : ‖z₀ + t • e‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hmem
    have hnorm : |t| * ‖e‖ - ‖z₀‖ ≤ ‖z₀ + t • e‖ := by
      have h1 := norm_sub_norm_le (t • e) (-z₀)
      rw [norm_smul, Real.norm_eq_abs, norm_neg, sub_neg_eq_add, add_comm] at h1
      exact h1
    have hMt : (max R 0 + ‖z₀‖ + 1) / ‖e‖ < |t| := by linarith
    have hmul := (div_lt_iff₀ he_pos).mp hMt
    have hRle : R ≤ max R 0 := le_max_left R 0
    linarith
  let F : ℝ → ℝ := fun t =>
    φ (z₀ + t • e) * fderiv ℝ u (z₀ + t • e) e - fderiv ℝ φ (z₀ + t • e) e * u (z₀ + t • e)
  let G : ℝ → ℝ := fun t =>
    φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e -
      fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e)
  have hFG : ∀ t : ℝ, HasDerivAt F (G t) t := by
    intro t
    by_cases hmem : z₀ + t • e ∈ tsupport u
    · have hmemU : z₀ + t • e ∈ U := hsub hmem
      have hφ_at : ContDiffAt ℝ 2 φ (z₀ + t • e) := hφ.contDiffAt (hU.mem_nhds hmemU)
      have hu_at : ContDiffAt ℝ 2 u (z₀ + t • e) := hu.contDiffAt
      have hline_deriv : ∀ {f : ℂ → ℝ}, ContDiffAt ℝ 2 f (z₀ + t • e) →
          HasDerivAt (fun s : ℝ => f (z₀ + s • e)) (fderiv ℝ f (z₀ + t • e) e) t ∧
          HasDerivAt (fun s : ℝ => fderiv ℝ f (z₀ + s • e) e)
            (fderiv ℝ (fderiv ℝ f) (z₀ + t • e) e e) t := by
        intro f hf
        have hl := hasDerivAt_complex_line hf e
        have hsub_t : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
        have h1 := hl.1.comp_of_eq t hsub_t (sub_self t).symm
        have h2 := hl.2.comp_of_eq t hsub_t (sub_self t).symm
        have heq1 : (fun s : ℝ => f (z₀ + t • e + (s - t) • e)) = fun s => f (z₀ + s • e) := by
          funext s; rw [sub_smul]; congr 1; abel
        have heq2 : (fun s : ℝ => fderiv ℝ f (z₀ + t • e + (s - t) • e) e) =
            fun s => fderiv ℝ f (z₀ + s • e) e := by
          funext s; rw [sub_smul]; congr 2; abel
        refine ⟨?_, ?_⟩
        · change HasDerivAt (fun s : ℝ => f (z₀ + t • e + (s - t) • e)) _ t at h1
          rw [heq1, mul_one] at h1; exact h1
        · change HasDerivAt (fun s : ℝ => fderiv ℝ f (z₀ + t • e + (s - t) • e) e) _ t at h2
          rw [heq2, mul_one] at h2; exact h2
      obtain ⟨hφ1, hφ2⟩ := hline_deriv hφ_at
      obtain ⟨hu1, hu2⟩ := hline_deriv hu_at
      refine ((hφ1.mul hu2).sub (hφ2.mul hu1)).congr_deriv ?_
      dsimp only [G]; ring
    · have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
      have hcont : Continuous (fun s : ℝ => z₀ + s • e) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hev : F =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [(hopen.preimage hcont).mem_nhds hmem] with s hs
        obtain ⟨h0, h1, _⟩ := fderiv_eq_zero_of_notMem_tsupport hs
        dsimp only [F]
        rw [h0, h1]
        simp
      have hG0 : G t = 0 := by
        obtain ⟨h0, _, h2⟩ := fderiv_eq_zero_of_notMem_tsupport hmem
        dsimp only [G]
        rw [h0, h2]
        simp
      rw [hG0]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  have hG_cont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases hmem : z₀ + t • e ∈ tsupport u
    · have hmemU : z₀ + t • e ∈ U := hsub hmem
      have hφ_at : ContDiffAt ℝ 2 φ (z₀ + t • e) := hφ.contDiffAt (hU.mem_nhds hmemU)
      have hline_c : ContinuousAt (fun s : ℝ => z₀ + s • e) t :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      have hc1 : ContinuousAt (fun s : ℝ => φ (z₀ + s • e)) t :=
        ContinuousAt.comp (g := φ) (f := fun s : ℝ => z₀ + s • e) hφ_at.continuousAt hline_c
      have hc2 : ContinuousAt (fun s : ℝ => fderiv ℝ (fderiv ℝ u) (z₀ + s • e) e e) t := by
        have h1 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
          (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
        exact (((h1.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
          continuous_const).clm_apply continuous_const).continuousAt
      have hc3 : ContinuousAt (fun s : ℝ => fderiv ℝ (fderiv ℝ φ) (z₀ + s • e) e e) t := by
        have hφ2 : ContinuousAt (fderiv ℝ (fderiv ℝ φ)) (z₀ + t • e) :=
          ((hφ_at.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
        exact (((ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ φ)) (f := fun s : ℝ => z₀ + s • e)
          hφ2 hline_c).clm_apply continuousAt_const).clm_apply continuousAt_const)
      have hc4 : ContinuousAt (fun s : ℝ => u (z₀ + s • e)) t :=
        ContinuousAt.comp (g := u) (f := fun s : ℝ => z₀ + s • e) hu.continuous.continuousAt hline_c
      exact (hc1.mul hc2).sub (hc3.mul hc4)
    · have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
      have hcont : Continuous (fun s : ℝ => z₀ + s • e) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hev : G =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [(hopen.preimage hcont).mem_nhds hmem] with s hs
        obtain ⟨h0, _, h2⟩ := fderiv_eq_zero_of_notMem_tsupport hs
        dsimp only [G]
        rw [h0, h2]
        simp
      exact continuousAt_const.congr hev.symm
  have hG_van : ∀ t : ℝ, M ≤ |t| → G t = 0 := fun t ht => by
    obtain ⟨h0, _, h2⟩ := fderiv_eq_zero_of_notMem_tsupport (hout t ht)
    dsimp only [G]
    rw [h0, h2]
    simp
  have hF_van : ∀ t : ℝ, M ≤ |t| → F t = 0 := fun t ht => by
    obtain ⟨h0, h1, _⟩ := fderiv_eq_zero_of_notMem_tsupport (hout t ht)
    dsimp only [F]
    rw [h0, h1]
    simp
  have hG_int0 : ∫ t : ℝ, G t = 0 := by
    have hsupp : ∫ t : ℝ, G t = ∫ t in Set.Ioc (-M) M, G t := by
      rw [← setIntegral_univ]
      exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
        (Set.subset_univ (Set.Ioc (-M) M)) fun t ht => hG_van t (by
          simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_Ioc, true_and, not_and, not_le] at ht
          by_cases h1 : -M < t
          · have h2 : M < t := ht h1
            rw [abs_of_pos (by linarith)]; linarith
          · push Not at h1
            rw [abs_of_nonpos (by linarith)]; linarith)
    rw [hsupp, ← intervalIntegral.integral_of_le (by linarith : -M ≤ M),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFG t)
        (hG_cont.intervalIntegrable (-M) M),
      hF_van M (by rw [abs_of_pos hM_pos]), hF_van (-M) (by rw [abs_neg, abs_of_pos hM_pos]),
      sub_self]
  have hcont_term1 : Continuous (fun t : ℝ => φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e) := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases hmem : z₀ + t • e ∈ tsupport u
    · have hφ_at : ContDiffAt ℝ 2 φ (z₀ + t • e) := hφ.contDiffAt (hU.mem_nhds (hsub hmem))
      have hline_c : ContinuousAt (fun s : ℝ => z₀ + s • e) t :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      have h1 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
        (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
      exact (ContinuousAt.comp (g := φ) (f := fun s : ℝ => z₀ + s • e) hφ_at.continuousAt hline_c).mul
        (((h1.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
          continuous_const).clm_apply continuous_const).continuousAt
    · have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
      have hcont : Continuous (fun s : ℝ => z₀ + s • e) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hev : (fun s : ℝ => φ (z₀ + s • e) * fderiv ℝ (fderiv ℝ u) (z₀ + s • e) e e) =ᶠ[𝓝 t]
          fun _ => 0 := by
        filter_upwards [(hopen.preimage hcont).mem_nhds hmem] with s hs
        rw [(fderiv_eq_zero_of_notMem_tsupport hs).2.2]
        simp
      exact continuousAt_const.congr hev.symm
  have hcont_term2 : Continuous (fun t : ℝ => fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e)) := by
    have heq : (fun t : ℝ => fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e)) =
        fun t => (φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e) - G t := by
      funext t; dsimp only [G]; ring
    rw [heq]
    exact hcont_term1.sub hG_cont
  have hcs1 : HasCompactSupport (fun t : ℝ => φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M)) fun t ht => ?_
    by_contra hnot
    apply ht
    have hab : M ≤ |t| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with h1 | h2
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    change φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e = 0
    rw [(fderiv_eq_zero_of_notMem_tsupport (hout t hab)).2.2]
    simp
  have hcs2 : HasCompactSupport (fun t : ℝ => fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e)) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -M) (b := M)) fun t ht => ?_
    by_contra hnot
    apply ht
    have hab : M ≤ |t| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      rcases hnot with h1 | h2
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    change fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e) = 0
    rw [(fderiv_eq_zero_of_notMem_tsupport (hout t hab)).1]
    simp
  have hint1 : Integrable (fun t : ℝ => φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e) volume :=
    hcont_term1.integrable_of_hasCompactSupport hcs1
  have hint2 : Integrable (fun t : ℝ => fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e)) volume :=
    hcont_term2.integrable_of_hasCompactSupport hcs2
  have hsub_int : ∫ t : ℝ, G t =
      (∫ t : ℝ, φ (z₀ + t • e) * fderiv ℝ (fderiv ℝ u) (z₀ + t • e) e e) -
        ∫ t : ℝ, fderiv ℝ (fderiv ℝ φ) (z₀ + t • e) e e * u (z₀ + t • e) :=
    MeasureTheory.integral_sub hint1 hint2
  linarith [hG_int0, hsub_int]

/-- **Green's Second Identity on Any Open Set `U ⊆ ℂ` Containing `tsupport u`**:
if `φ` is `C²` on open `U ⊇ tsupport u` and `u : ℂ → ℝ` is `C²` with compact support, then
$$\int_{\mathbb{C}} \varphi(z)\, \Delta u(z)\, dA(z)
  = \int_{\mathbb{C}} \Delta \varphi(z)\, u(z)\, dA(z).$$ -/
theorem greens_second_identity_open {U : Set ℂ} (hU : IsOpen U) {φ u : ℂ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    (hsub : tsupport u ⊆ U) :
    Integrable (fun z : ℂ => φ z * laplacianC u z) ∧
    Integrable (fun z : ℂ => laplacianC φ z * u z) ∧
    ∫ z : ℂ, φ z * laplacianC u z = ∫ z : ℂ, laplacianC φ z * u z := by
  have hterm_cont_int : ∀ e : ℂ,
      Integrable (fun z : ℂ => φ z * fderiv ℝ (fderiv ℝ u) z e e) ∧
      Integrable (fun z : ℂ => fderiv ℝ (fderiv ℝ φ) z e e * u z) := by
    intro e
    have hc1 : Continuous (fun z : ℂ => φ z * fderiv ℝ (fderiv ℝ u) z e e) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hmem : z ∈ tsupport u
      · have hφ_at := hφ.contDiffAt (hU.mem_nhds (hsub hmem))
        have hu2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
          (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
        exact hφ_at.continuousAt.mul ((hu2.clm_apply continuous_const).clm_apply continuous_const).continuousAt
      · have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
        have hev : (fun y => φ y * fderiv ℝ (fderiv ℝ u) y e e) =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hopen.mem_nhds hmem] with y hy
          simp [(fderiv_eq_zero_of_notMem_tsupport hy).2.2]
        exact continuousAt_const.congr hev.symm
    have hc2 : Continuous (fun z : ℂ => fderiv ℝ (fderiv ℝ φ) z e e * u z) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hmem : z ∈ tsupport u
      · have hφ_at := hφ.contDiffAt (hU.mem_nhds (hsub hmem))
        have hφ2 : ContinuousAt (fderiv ℝ (fderiv ℝ φ)) z :=
          ((hφ_at.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
        exact ((hφ2.clm_apply continuousAt_const).clm_apply continuousAt_const).mul hu.continuous.continuousAt
      · have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
        have hev : (fun y => fderiv ℝ (fderiv ℝ φ) y e e * u y) =ᶠ[𝓝 z] fun _ => 0 := by
          filter_upwards [hopen.mem_nhds hmem] with y hy
          simp [(fderiv_eq_zero_of_notMem_tsupport hy).1]
        exact continuousAt_const.congr hev.symm
    have hcs1 : HasCompactSupport (fun z : ℂ => φ z * fderiv ℝ (fderiv ℝ u) z e e) :=
      HasCompactSupport.of_support_subset_isCompact hcs fun z hz => by
        by_contra hnot; apply hz; simp [(fderiv_eq_zero_of_notMem_tsupport hnot).2.2]
    have hcs2 : HasCompactSupport (fun z : ℂ => fderiv ℝ (fderiv ℝ φ) z e e * u z) :=
      HasCompactSupport.of_support_subset_isCompact hcs fun z hz => by
        by_contra hnot; apply hz; simp [(fderiv_eq_zero_of_notMem_tsupport hnot).1]
    exact ⟨hc1.integrable_of_hasCompactSupport hcs1, hc2.integrable_of_hasCompactSupport hcs2⟩
  obtain ⟨h1a, h1b⟩ := hterm_cont_int 1
  obtain ⟨hIa, hIb⟩ := hterm_cont_int Complex.I
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hEq1 : ∫ z : ℂ, φ z * fderiv ℝ (fderiv ℝ u) z 1 1 =
      ∫ z : ℂ, fderiv ℝ (fderiv ℝ φ) z 1 1 * u z := by
    have ha := hmp.integral_comp' (g := fun z : ℂ => φ z * fderiv ℝ (fderiv ℝ u) z 1 1)
    have hb := hmp.integral_comp' (g := fun z : ℂ => fderiv ℝ (fderiv ℝ φ) z 1 1 * u z)
    rw [← ha, ← hb]
    have hia : Integrable (fun p : ℝ × ℝ => φ (Complex.measurableEquivRealProd.symm p) *
        fderiv ℝ (fderiv ℝ u) (Complex.measurableEquivRealProd.symm p) 1 1) volume :=
      (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr h1a
    have hib : Integrable (fun p : ℝ × ℝ => fderiv ℝ (fderiv ℝ φ) (Complex.measurableEquivRealProd.symm p) 1 1 *
        u (Complex.measurableEquivRealProd.symm p)) volume :=
      (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr h1b
    rw [Measure.volume_eq_prod] at hia hib ⊢
    rw [MeasureTheory.integral_prod_symm _ hia, MeasureTheory.integral_prod_symm _ hib]
    refine MeasureTheory.integral_congr_ae (ae_of_all _ fun y => ?_)
    have hpt : ∀ x : ℝ, Complex.measurableEquivRealProd.symm (x, y) = (y : ℂ) * Complex.I + x • (1 : ℂ) := by
      intro x
      apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
    simp_rw [hpt]
    exact integral_ibp_line_open hU hφ hu hcs hsub ((y : ℂ) * Complex.I) 1 one_ne_zero
  have hEqI : ∫ z : ℂ, φ z * fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I =
      ∫ z : ℂ, fderiv ℝ (fderiv ℝ φ) z Complex.I Complex.I * u z := by
    have ha := hmp.integral_comp' (g := fun z : ℂ => φ z * fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I)
    have hb := hmp.integral_comp' (g := fun z : ℂ => fderiv ℝ (fderiv ℝ φ) z Complex.I Complex.I * u z)
    rw [← ha, ← hb]
    have hia : Integrable (fun p : ℝ × ℝ => φ (Complex.measurableEquivRealProd.symm p) *
        fderiv ℝ (fderiv ℝ u) (Complex.measurableEquivRealProd.symm p) Complex.I Complex.I) volume :=
      (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hIa
    have hib : Integrable (fun p : ℝ × ℝ =>
        fderiv ℝ (fderiv ℝ φ) (Complex.measurableEquivRealProd.symm p) Complex.I Complex.I *
        u (Complex.measurableEquivRealProd.symm p)) volume :=
      (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hIb
    rw [Measure.volume_eq_prod] at hia hib ⊢
    rw [MeasureTheory.integral_prod _ hia, MeasureTheory.integral_prod _ hib]
    refine MeasureTheory.integral_congr_ae (ae_of_all _ fun x => ?_)
    have hpt : ∀ y : ℝ, Complex.measurableEquivRealProd.symm (x, y) = (x : ℂ) + y • Complex.I := by
      intro y
      apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
    simp_rw [hpt]
    exact integral_ibp_line_open hU hφ hu hcs hsub (x : ℂ) Complex.I Complex.I_ne_zero
  have hsumL : (fun z : ℂ => φ z * laplacianC u z) =
      fun z => φ z * fderiv ℝ (fderiv ℝ u) z 1 1 +
        φ z * fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I := by
    funext z; unfold laplacianC; ring
  have hsumR : (fun z : ℂ => laplacianC φ z * u z) =
      fun z => fderiv ℝ (fderiv ℝ φ) z 1 1 * u z +
        fderiv ℝ (fderiv ℝ φ) z Complex.I Complex.I * u z := by
    funext z; unfold laplacianC; ring
  rw [hsumL, hsumR]
  refine ⟨h1a.add hIa, h1b.add hIb, ?_⟩
  rw [MeasureTheory.integral_add h1a hIa, MeasureTheory.integral_add h1b hIb, hEq1, hEqI]

/-- Corollary: `∫ φ * ddcDens u = ∫ ddcDens φ * u` on any open `U ⊇ tsupport u`. -/
theorem greens_second_identity_ddcDens {U : Set ℂ} (hU : IsOpen U) {φ u : ℂ → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    (hsub : tsupport u ⊆ U) :
    Integrable (fun z : ℂ => φ z * ddcDens u z) ∧
    Integrable (fun z : ℂ => ddcDens φ z * u z) ∧
    ∫ z : ℂ, φ z * ddcDens u z = ∫ z : ℂ, ddcDens φ z * u z := by
  obtain ⟨h1, h2, heq⟩ := greens_second_identity_open hU hφ hu hcs hsub
  have e1 : (fun z : ℂ => φ z * ddcDens u z) =
      fun z => (1 / (4 * Real.pi)) * (φ z * laplacianC u z) := by
    funext z; unfold ddcDens; ring
  have e2 : (fun z : ℂ => ddcDens φ z * u z) =
      fun z => (1 / (4 * Real.pi)) * (laplacianC φ z * u z) := by
    funext z; unfold ddcDens; ring
  rw [e1, e2]
  refine ⟨h1.const_mul _, h2.const_mul _, ?_⟩
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, heq]

/-- **Harmonic Annihilation for Nonvanishing Holomorphic Units**:
if `g` is `C²`-holomorphic and nonvanishing on open `U ⊇ tsupport u`, then
`∫ z : ℂ, Real.log (‖g z‖ ^ 2) * ddcDens u z = 0`. -/
theorem integral_log_norm_sq_holo_mul_ddcDens_eq_zero {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    {u : ℂ → ℝ} (hg : ∀ z ∈ U, ContDiffAt ℂ 2 g z) (hg_ne : ∀ z ∈ U, g z ≠ 0)
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) (hsub : tsupport u ⊆ U) :
    Integrable (fun z : ℂ => Real.log (‖g z‖ ^ 2) * ddcDens u z) ∧
    ∫ z : ℂ, Real.log (‖g z‖ ^ 2) * ddcDens u z = 0 := by
  have hlog_cd : ContDiffOn ℝ 2 (fun z : ℂ => Real.log (‖g z‖ ^ 2)) U := by
    intro z hz
    have h1 : ContDiffAt ℝ 2 (fun y : ℂ => ‖g y‖ ^ 2) z := by
      have hgR : ContDiffAt ℝ 2 g z := (hg z hz).restrict_scalars ℝ
      have heq : (fun y => ‖g y‖ ^ 2) = fun y => (g y * conj (g y)).re := by
        funext y; rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [heq]
      exact Complex.reCLM.contDiff.contDiffAt.comp z
        (hgR.mul (Complex.conjCLE.contDiff.contDiffAt.comp z hgR))
    exact (h1.log (sq_pos_of_pos (norm_pos_iff.mpr (hg_ne z hz))).ne').contDiffWithinAt
  obtain ⟨h1, _, heq⟩ := greens_second_identity_ddcDens hU hlog_cd hu hcs hsub
  refine ⟨h1, ?_⟩
  rw [heq]
  have hzero : ∀ z : ℂ, ddcDens (fun w => Real.log (‖g w‖ ^ 2)) z * u z = 0 := by
    intro z
    by_cases hmem : z ∈ tsupport u
    · have hzU := hsub hmem
      unfold ddcDens
      rw [laplacianC_log_norm_sq_holomorphic (hg z hzU) (hg_ne z hzU)]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hmem, mul_zero]
  simp_rw [hzero]
  simp

/-! ### Part B: Exact Polar Fundamental Solution (`∫ log ‖z - a‖ * Δ u = 2π u(a)`) -/

/-- Unit circle parametrization `θ ↦ e^{i θ} = cos θ + i sin θ`. -/
private def unitCircleE (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * Complex.I

private lemma hasDerivAt_unitCircleE (θ : ℝ) :
    HasDerivAt unitCircleE (Complex.I * unitCircleE θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I)
  have e : Complex.I * unitCircleE θ =
      ((-Real.sin θ : ℝ) : ℂ) + (Real.cos θ : ℂ) * Complex.I := by
    simp only [unitCircleE, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * Complex.I_sq
  rw [e]; exact h

private lemma continuous_unitCircleE : Continuous unitCircleE := by unfold unitCircleE; fun_prop

private lemma norm_unitCircleE (θ : ℝ) : ‖unitCircleE θ‖ = 1 := by
  have : unitCircleE θ = Complex.exp (θ * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; rfl
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma unitCircleE_pi : unitCircleE Real.pi = unitCircleE (-Real.pi) := by
  unfold unitCircleE; rw [Real.cos_neg, Real.sin_neg, Real.sin_pi]; simp

private lemma polar_symm_eq_unitCircleE (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 • unitCircleE p.2 := by
  simp [unitCircleE, Complex.real_smul]; ring

/-- Rotational invariance of `laplacianC`:
`laplacianC u z = D²u(z)(e^{iθ}, e^{iθ}) + D²u(z)(i e^{iθ}, i e^{iθ})`. -/
private lemma laplacianC_eq_rot (u : ℂ → ℝ) (z : ℂ) (θ : ℝ) :
    laplacianC u z = fderiv ℝ (fderiv ℝ u) z (unitCircleE θ) (unitCircleE θ) +
      fderiv ℝ (fderiv ℝ u) z (Complex.I * unitCircleE θ) (Complex.I * unitCircleE θ) := by
  have he : unitCircleE θ = Real.cos θ • (1 : ℂ) + Real.sin θ • Complex.I := by
    simp [unitCircleE, Complex.real_smul]
  have hie : Complex.I * unitCircleE θ = (-Real.sin θ) • (1 : ℂ) + Real.cos θ • Complex.I := by
    simp only [unitCircleE, Complex.real_smul, Complex.ofReal_neg]
    linear_combination (Real.sin θ : ℂ) * Complex.I_sq
  unfold laplacianC
  rw [hie, he]
  simp only [map_add, map_smul, _root_.add_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  have hsc := Real.sin_sq_add_cos_sq θ
  set H := fderiv ℝ (fderiv ℝ u) z
  linear_combination (-(H 1 1 + H Complex.I Complex.I)) * hsc

private def polarRad (u : ℂ → ℝ) (a : ℂ) (θ r : ℝ) : ℝ :=
  Real.log r * (r * fderiv ℝ (fderiv ℝ u) (a + r • unitCircleE θ) (unitCircleE θ) (unitCircleE θ) +
    fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ))

private def polarAng (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) : ℝ :=
  Real.log r * (r * fderiv ℝ (fderiv ℝ u) (a + r • unitCircleE θ)
      (Complex.I * unitCircleE θ) (Complex.I * unitCircleE θ) -
    fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ))

private lemma polar_decomp (u : ℂ → ℝ) (a : ℂ) (r θ : ℝ) :
    r * Real.log r * laplacianC u (a + r • unitCircleE θ) =
      polarRad u a θ r + polarAng u a r θ := by
  rw [laplacianC_eq_rot u _ θ]; simp only [polarRad, polarAng]; ring

private lemma polar_vanish {u : ℂ → ℝ} {a : ℂ} {R : ℝ} (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) {z : ℂ}
    (hz : R < ‖z - a‖) : fderiv ℝ u z = 0 ∧ fderiv ℝ (fderiv ℝ u) z = 0 := by
  have hU : IsOpen {y : ℂ | R < ‖y - a‖} := isOpen_lt continuous_const (by fun_prop)
  have h1 : ∀ y ∈ {y : ℂ | R < ‖y - a‖}, fderiv ℝ u y = 0 := by
    intro y hy
    have : u =ᶠ[𝓝 y] fun _ => 0 :=
      Filter.eventually_of_mem (hU.mem_nhds hy) fun x hx => hR x (le_of_lt hx)
    rw [this.fderiv_eq]; simp
  refine ⟨h1 z hz, ?_⟩
  have : fderiv ℝ u =ᶠ[𝓝 z] fun _ => 0 := Filter.eventually_of_mem (hU.mem_nhds hz) h1
  rw [this.fderiv_eq]; simp

private lemma integral_polarRad {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {R : ℝ} (hR0 : 0 < R)
    (hR : ∀ z, R ≤ ‖z - a‖ → u z = 0) (θ : ℝ) :
    ∫ r in Set.Ioi (0 : ℝ), polarRad u a θ r = u a := by
  have hnorm_rad : ∀ r : ℝ, 0 ≤ r → ‖a + r • unitCircleE θ - a‖ = r := fun r hr => by
    simp [norm_unitCircleE, abs_of_nonneg hr]
  have hz : ∀ r, R < r → polarRad u a θ r = 0 := fun r hr => by
    obtain ⟨h1, h2⟩ := polar_vanish hR (z := a + r • unitCircleE θ)
      (by rw [hnorm_rad r (by linarith)]; exact hr)
    simp only [polarRad, h1, h2, _root_.zero_apply, mul_zero, add_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) (R + 1) ⊆ Set.Ioi 0)
    (fun r hr => hz r (by
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at hr
      linarith [hr.2 hr.1]))]
  rw [← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ R + 1)]
  have hD1 : Continuous (fderiv ℝ u) := (hu.fderiv_right (m := 1) (by norm_num)).continuous
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hF : ∀ r ∈ Set.Ioo (0 : ℝ) (R + 1), HasDerivAt
      (fun r => r * Real.log r * fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ) -
        u (a + r • unitCircleE θ))
      (polarRad u a θ r) r := by
    intro r hr
    have hp : HasDerivAt (fun s : ℝ => a + s • unitCircleE θ) (unitCircleE θ) r := by
      simpa using ((hasDerivAt_id r).smul_const (unitCircleE θ)).const_add a
    have hr1 : HasDerivAt (fun s : ℝ => u (a + s • unitCircleE θ))
        (fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ)) r :=
      ((hu.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt r hp
    have hr2 : HasDerivAt (fun s : ℝ => fderiv ℝ u (a + s • unitCircleE θ) (unitCircleE θ))
        (fderiv ℝ (fderiv ℝ u) (a + r • unitCircleE θ) (unitCircleE θ) (unitCircleE θ)) r := by
      have h2 := (((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt r hp
      simpa using h2.clm_apply (hasDerivAt_const r (unitCircleE θ))
    refine (((Real.hasDerivAt_mul_log hr.1.ne').mul hr2).sub hr1).congr_deriv ?_
    simp only [polarRad]; ring
  have hcont : ContinuousOn
      (fun r : ℝ => r * Real.log r * fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ) -
        u (a + r • unitCircleE θ))
      (Set.Icc 0 (R + 1)) := by
    apply Continuous.continuousOn
    have h0 := hu.continuous
    have hg : Continuous fun r : ℝ => fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ) := by
      fun_prop
    exact (Real.continuous_mul_log.mul hg).sub (by fun_prop)
  have hint : IntervalIntegrable (polarRad u a θ) volume 0 (R + 1) := by
    have hP : Continuous (fun r : ℝ =>
        r * fderiv ℝ (fderiv ℝ u) (a + r • unitCircleE θ) (unitCircleE θ) (unitCircleE θ) +
          fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ)) := by fun_prop
    exact intervalIntegrable_log'.mul_continuousOn hP.continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hF hint]
  obtain ⟨h1, -⟩ := polar_vanish hR (z := a + (R + 1) • unitCircleE θ)
    (by rw [hnorm_rad (R + 1) (by linarith)]; linarith)
  have h0 : u (a + (R + 1) • unitCircleE θ) = 0 :=
    hR _ (by rw [hnorm_rad (R + 1) (by linarith)]; linarith)
  rw [h1, h0]; simp

private lemma integral_polarAng_eq_zero {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (a : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, polarAng u a r θ = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hB : ∀ θ, polarAng u a r θ = (Real.log r / r) *
      (fderiv ℝ (fderiv ℝ u) (a + r • unitCircleE θ)
          (r • (Complex.I * unitCircleE θ)) (r • (Complex.I * unitCircleE θ)) -
        r * fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ)) := by
    intro θ
    simp only [polarAng, map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [hr.ne']
  simp_rw [hB]
  have hD1 : Continuous (fderiv ℝ u) := (hu.fderiv_right (m := 1) (by norm_num)).continuous
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have he := continuous_unitCircleE
  have hang' : ∀ θ : ℝ,
      HasDerivAt (fun θ : ℝ => fderiv ℝ u (a + r • unitCircleE θ) (r • (Complex.I * unitCircleE θ)))
        (fderiv ℝ (fderiv ℝ u) (a + r • unitCircleE θ)
            (r • (Complex.I * unitCircleE θ)) (r • (Complex.I * unitCircleE θ)) -
          r * fderiv ℝ u (a + r • unitCircleE θ) (unitCircleE θ)) θ := by
    intro θ
    have hp : HasDerivAt (fun θ : ℝ => a + r • unitCircleE θ) (r • (Complex.I * unitCircleE θ)) θ :=
      ((hasDerivAt_unitCircleE θ).const_smul r).const_add a
    have hq : HasDerivAt (fun θ : ℝ => r • (Complex.I * unitCircleE θ))
        (r • (Complex.I * (Complex.I * unitCircleE θ))) θ :=
      ((hasDerivAt_unitCircleE θ).const_mul Complex.I).const_smul r
    have h2 := (((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ hp
    refine (h2.clm_apply hq).congr_deriv ?_
    rw [← mul_assoc, Complex.I_mul_I]
    simp only [neg_one_mul, smul_neg, map_neg, map_smul, smul_eq_mul, sub_eq_add_neg]
    rfl
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hang' θ)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    unitCircleE_pi]
  simp

private lemma integrableOn_polar_log_mul {P : ℝ × ℝ → ℝ} (hP : Continuous P) {R : ℝ} (hR0 : 0 < R)
    (hz : ∀ p : ℝ × ℝ, R < p.1 → P p = 0) :
    IntegrableOn (fun p : ℝ × ℝ => Real.log p.1 * P p) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  have hpi := Real.pi_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (-Real.pi) Real.pi)).exists_bound_of_continuousOn hP.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _)
    (hC (0, 0) ⟨⟨le_rfl, hR0.le⟩, ⟨by linarith, by linarith⟩⟩)
  have hg : IntegrableOn (fun p : ℝ × ℝ =>
      C * (Set.Ioc (0 : ℝ) R).indicator (fun r => ‖Real.log r‖) p.1 * (1 : ℝ))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun r : ℝ => C * (Set.Ioc (0 : ℝ) R).indicator (fun r => ‖Real.log r‖) r)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply Integrable.const_mul
      apply Integrable.mono_measure _ Measure.restrict_le_self
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR0.le).1 intervalIntegrable_log').norm
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioo (-Real.pi) Real.pi)) :=
      integrableOn_const (by simp)
    exact Integrable.mul_prod (f := fun r : ℝ => C * (Set.Ioc (0 : ℝ) R).indicator (fun r => ‖Real.log r‖) r)
      (g := fun _ : ℝ => (1 : ℝ)) h1 h2
  refine hg.mono' ((Real.measurable_log.comp measurable_fst).mul hP.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
  rcases le_or_gt p.1 R with h | h
  · have h1 : p.1 ∈ Set.Ioc (0 : ℝ) R := ⟨hp.1, h⟩
    rw [indicator_of_mem h1, mul_one, norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC p ⟨⟨le_of_lt hp.1, h⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩)
      (norm_nonneg _)
  · rw [hz p h, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 (indicator_nonneg (fun _ _ => norm_nonneg _) _)) zero_le_one

/-- Elementary `L¹` integrability of `z ↦ |log ‖z‖|` on any closed ball `closedBall 0 R ⊂ ℂ`,
proved via `|log ‖x + i y‖| ≤ |log |x|| + log (max R 1)` on `[-R, R]²` and Fubini. -/
private lemma integrable_closedBall_indicator_log_norm {R : ℝ} (hR : 0 < R) :
    Integrable (fun z : ℂ => (Metric.closedBall (0 : ℂ) R).indicator (fun ξ => |Real.log ‖ξ‖|) z)
      volume := by
  have hlog_Ioc : IntegrableOn (fun x : ℝ => |Real.log x|) (Set.Ioc 0 R) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1 intervalIntegrable_log').abs
  have hlog_pos : Integrable (fun x : ℝ => (Set.Ioc 0 R).indicator (fun t => |Real.log t|) x) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hlog_Ioc
  have hlog_neg : Integrable (fun x : ℝ => (Set.Ioc 0 R).indicator (fun t => |Real.log t|) (-x)) volume :=
    hlog_pos.comp_neg
  have hconst_x : Integrable (fun x : ℝ => (Set.Icc (-R) R).indicator (fun _ => Real.log (max R 1)) x) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp [Real.volume_Icc]))
  have hx : Integrable (fun x : ℝ =>
      (Set.Ioc 0 R).indicator (fun t => |Real.log t|) x +
        (Set.Ioc 0 R).indicator (fun t => |Real.log t|) (-x) +
        (Set.Icc (-R) R).indicator (fun _ => Real.log (max R 1)) x) volume :=
    (hlog_pos.add hlog_neg).add hconst_x
  have hy : Integrable (fun y : ℝ => (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ)) y) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp [Real.volume_Icc]))
  have hprod : Integrable (fun p : ℝ × ℝ =>
      ((Set.Ioc 0 R).indicator (fun t => |Real.log t|) p.1 +
        (Set.Ioc 0 R).indicator (fun t => |Real.log t|) (-p.1) +
        (Set.Icc (-R) R).indicator (fun _ => Real.log (max R 1)) p.1) *
      (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ)) p.2) volume := by
    rw [Measure.volume_eq_prod]
    exact hx.mul_prod hy
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hdom : Integrable (fun z : ℂ =>
      ((Set.Ioc 0 R).indicator (fun t => |Real.log t|) z.re +
        (Set.Ioc 0 R).indicator (fun t => |Real.log t|) (-z.re) +
        (Set.Icc (-R) R).indicator (fun _ => Real.log (max R 1)) z.re) *
      (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ)) z.im) volume :=
    (hmp.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  refine hdom.mono' ?_ ?_
  · exact ((continuous_abs.measurable.comp (Real.measurable_log.comp measurable_norm)).indicator
      Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable
  · have hre0_null : volume {z : ℂ | z.re = 0} = 0 := by
      have hpre : {z : ℂ | z.re = 0} =
          Complex.measurableEquivRealProd ⁻¹' (({(0 : ℝ)} : Set ℝ) ×ˢ Set.univ) := by
        ext z; simp [Complex.measurableEquivRealProd]
      rw [hpre, hmp.measure_preimage
          ((MeasurableSet.singleton (0 : ℝ)).prod MeasurableSet.univ).nullMeasurableSet,
        Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have hre_ne : ∀ᵐ z : ℂ ∂volume, z.re ≠ 0 := by
      rw [ae_iff]
      convert hre0_null using 2
      ext z; simp
    filter_upwards [hre_ne] with z hzne
    have hlogM_nn : 0 ≤ Real.log (max R 1) := Real.log_nonneg (le_max_right R 1)
    by_cases hmem : z ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_abs]
      have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hmem
      have hre_le : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have him_le : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      have hre_Icc : z.re ∈ Set.Icc (-R) R := abs_le.mp (hre_le.trans hzR)
      have him_Icc : z.im ∈ Set.Icc (-R) R := abs_le.mp (him_le.trans hzR)
      rw [Set.indicator_of_mem hre_Icc, Set.indicator_of_mem him_Icc, mul_one]
      have h1_eq : (Set.Ioc 0 R).indicator (fun t => |Real.log t|) z.re +
          (Set.Ioc 0 R).indicator (fun t => |Real.log t|) (-z.re) = |Real.log (|z.re|)| := by
        rcases lt_or_gt_of_ne hzne with hlt | hgt
        · have hm1 : z.re ∉ Set.Ioc 0 R := fun h => not_lt.mpr hlt.le h.1
          have hm2 : -z.re ∈ Set.Ioc 0 R := ⟨neg_pos.mpr hlt, by linarith [hre_Icc.1]⟩
          rw [Set.indicator_of_notMem hm1, Set.indicator_of_mem hm2, zero_add, abs_of_neg hlt]
        · have hm1 : z.re ∈ Set.Ioc 0 R := ⟨hgt, hre_Icc.2⟩
          have hm2 : -z.re ∉ Set.Ioc 0 R := fun h => by linarith [h.1]
          rw [Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2, add_zero, abs_of_pos hgt]
      rw [h1_eq]
      have hre_pos : 0 < |z.re| := abs_pos.mpr hzne
      have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hre_pos hre_le
      rcases le_or_gt ‖z‖ 1 with hle1 | hgt1
      · have hlog_le0 : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hz_pos.le hle1
        have hlog_re : Real.log |z.re| ≤ Real.log ‖z‖ := Real.log_le_log hre_pos hre_le
        rw [abs_of_nonpos hlog_le0, abs_of_nonpos (hlog_re.trans hlog_le0)]
        linarith
      · have hlog_ge0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hgt1.le
        have hlog_M : Real.log ‖z‖ ≤ Real.log (max R 1) :=
          Real.log_le_log hz_pos (hzR.trans (le_max_left R 1))
        rw [abs_of_nonneg hlog_ge0]
        linarith [abs_nonneg (Real.log |z.re|)]
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      exact mul_nonneg (add_nonneg (add_nonneg
        (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
        (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _))
        (Set.indicator_nonneg (fun _ _ => hlogM_nn) _))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- **Exact Polar Fundamental Solution of the 2D Laplacian**:
for every `u : ℂ → ℝ` with `ContDiff ℝ 2 u` and `HasCompactSupport u`, and every `a : ℂ`:
$$\int_{\mathbb{C}} \log \|z - a\|\, \Delta u(z)\, dA(z) = 2\pi\, u(a).$$ -/
theorem green_fundamental_solution {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    (a : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * laplacianC u z) ∧
      ∫ z : ℂ, Real.log ‖z - a‖ * laplacianC u z = 2 * Real.pi * u a := by
  obtain ⟨R₀, hR₀⟩ := hcs.isBounded.subset_closedBall a
  set R' : ℝ := max R₀ 1 + 1
  have hR'0 : 0 < R' := by positivity
  have hR' : ∀ z : ℂ, R' ≤ ‖z - a‖ → u z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport u := subset_tsupport u hne
    have hle : ‖z - a‖ ≤ R₀ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hR₀ hmem
    have h1 : R₀ ≤ max R₀ 1 := le_max_left R₀ 1
    linarith
  have hD1 : Continuous (fderiv ℝ u) := (hu.fderiv_right (m := 1) (by norm_num)).continuous
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have he := continuous_unitCircleE
  have hL : Continuous (laplacianC u) := by
    have h : laplacianC u = fun z =>
        fderiv ℝ (fderiv ℝ u) z 1 1 + fderiv ℝ (fderiv ℝ u) z Complex.I Complex.I := rfl
    rw [h]; fun_prop
  have hA : IntegrableOn (fun p : ℝ × ℝ => polarRad u a p.2 p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    integrableOn_polar_log_mul
      (P := fun p : ℝ × ℝ =>
        p.1 * fderiv ℝ (fderiv ℝ u) (a + p.1 • unitCircleE p.2) (unitCircleE p.2) (unitCircleE p.2) +
          fderiv ℝ u (a + p.1 • unitCircleE p.2) (unitCircleE p.2))
      (by fun_prop) hR'0 (fun p hp => by
        obtain ⟨h1, h2⟩ := polar_vanish hR' (z := a + p.1 • unitCircleE p.2)
          (by simp [norm_unitCircleE, abs_of_pos (lt_trans hR'0 hp)]; exact hp)
        simp only [h1, h2, _root_.zero_apply, mul_zero, add_zero])
  have hB : IntegrableOn (fun p : ℝ × ℝ => polarAng u a p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    integrableOn_polar_log_mul
      (P := fun p : ℝ × ℝ =>
        p.1 * fderiv ℝ (fderiv ℝ u) (a + p.1 • unitCircleE p.2)
            (Complex.I * unitCircleE p.2) (Complex.I * unitCircleE p.2) -
          fderiv ℝ u (a + p.1 • unitCircleE p.2) (unitCircleE p.2))
      (by fun_prop) hR'0 (fun p hp => by
        obtain ⟨h1, h2⟩ := polar_vanish hR' (z := a + p.1 • unitCircleE p.2)
          (by simp [norm_unitCircleE, abs_of_pos (lt_trans hR'0 hp)]; exact hp)
        simp only [h1, h2, _root_.zero_apply, mul_zero, sub_zero])
  have htarget : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  constructor
  · obtain ⟨C, hC⟩ := (isCompact_closedBall a R').exists_bound_of_continuousOn hL.continuousOn
    have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC a (Metric.mem_closedBall_self hR'0.le))
    have hdom : Integrable (fun z : ℂ =>
        C * (Metric.closedBall (0 : ℂ) R').indicator (fun ξ => |Real.log ‖ξ‖|) (z - a)) volume :=
      ((integrable_closedBall_indicator_log_norm hR'0).comp_sub_right a).const_mul C
    refine hdom.mono' ?_ (ae_of_all _ fun z => ?_)
    · exact ((Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub_const a))).mul
        hL.measurable).aestronglyMeasurable
    · rcases le_or_gt ‖z - a‖ R' with hle | hgt
      · have hm : z - a ∈ Metric.closedBall (0 : ℂ) R' := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hle
        rw [Set.indicator_of_mem hm, norm_mul, Real.norm_eq_abs, mul_comm C]
        exact mul_le_mul_of_nonneg_left
          (hC z (by rwa [Metric.mem_closedBall, dist_eq_norm])) (abs_nonneg _)
      · have hlap0 : laplacianC u z = 0 := by
          unfold laplacianC
          rw [(polar_vanish hR' hgt).2]; simp
        rw [hlap0, mul_zero, norm_zero]
        exact mul_nonneg hC0 (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
  · have ht := integral_add_left_eq_self (μ := volume)
      (fun z : ℂ => Real.log ‖z - a‖ * laplacianC u z) a
    simp only [add_sub_cancel_left] at ht
    rw [← ht, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    rw [setIntegral_congr_fun htarget
      (g := fun p : ℝ × ℝ => polarRad u a p.2 p.1 + polarAng u a p.1 p.2) (fun p hp => by
        simp only [polar_symm_eq_unitCircleE, smul_eq_mul]
        rw [norm_smul, norm_unitCircleE, mul_one, Real.norm_eq_abs, abs_of_pos hp.1, ← polar_decomp]
        ring)]
    rw [integral_add hA hB]
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hA hB
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hA,
      integral_prod _ hB]
    have eA : ∀ θ : ℝ, ∫ r in Set.Ioi (0 : ℝ), polarRad u a θ r = u a :=
      integral_polarRad hu a hR'0 hR'
    have eB : ∫ r in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi, polarAng u a r θ = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun r hr => integral_polarAng_eq_zero hu a hr)]
      simp
    simp only [eA, eB, add_zero, setIntegral_const, smul_eq_mul]
    rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    ring

/-- **Point-Divisor Poincaré–Lelong Formula**:
$$\int_{\mathbb{C}} \log(\|z - a\|^2) \, \mathrm{dd}^c u(z)\, dA(z) = u(a).$$ -/
theorem poincare_lelong_point {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u)
    (a : ℂ) :
    Integrable (fun z : ℂ => Real.log (‖z - a‖ ^ 2) * ddcDens u z) ∧
      ∫ z : ℂ, Real.log (‖z - a‖ ^ 2) * ddcDens u z = u a := by
  obtain ⟨hint, heq⟩ := green_fundamental_solution hu hcs a
  have hfun : (fun z : ℂ => Real.log (‖z - a‖ ^ 2) * ddcDens u z) =
      fun z => (1 / (2 * Real.pi)) * (Real.log ‖z - a‖ * laplacianC u z) := by
    funext z
    unfold ddcDens
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun]
  refine ⟨hint.const_mul _, ?_⟩
  rw [MeasureTheory.integral_const_mul, heq]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp [hpi]

/-! ### Part C: Full Distributional `poincare_lelong_equation` -/

/-- **THE DISTRIBUTIONAL POINCARÉ–LELONG EQUATION (`poincare_lelong_equation`)**:
Let `U ⊆ ℂ` be open, `φ : ℂ → ℝ` a `C²` Hermitian metric weight on `U` (defining the First Chern
density `c₁(φ) = ddcDens φ = (1/(4π)) Δ φ`), `g : ℂ → ℂ` a `C²`-holomorphic nonvanishing unit on
`U`, `D = ∑_{i ∈ s} m_i [a_i]` a finite divisor (`m : κ → ℤ`, `a : κ → ℂ`), and
$$f(z) = g(z) \prod_{i \in s} (z - a_i)^{m_i}.$$
Then for EVERY `C²` compactly supported test function `u : ℂ → ℝ` with `tsupport u ⊆ U`:
1. `z ↦ log(‖f(z)‖² exp(-φ(z))) * ddcDens u z` is Lebesgue-integrable on `ℂ`, and
2. $$\int_{\mathbb{C}} \log\!\bigl(\|f(z)\|^2 e^{-\varphi(z)}\bigr) \, \mathrm{dd}^c u(z)\, dA(z)
     = \sum_{i \in s} m_i\, u(a_i) - \int_{\mathbb{C}} \mathrm{dd}^c \varphi(z)\, u(z)\, dA(z).$$ -/
theorem poincare_lelong_equation {κ : Type*} (s : Finset κ) (m : κ → ℤ) (a : κ → ℂ)
    {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℝ} (hφ : ContDiffOn ℝ 2 φ U)
    {g : ℂ → ℂ} (hg : ∀ z ∈ U, ContDiffAt ℂ 2 g z) (hg_ne : ∀ z ∈ U, g z ≠ 0)
    {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) (hsub : tsupport u ⊆ U) :
    let f : ℂ → ℂ := fun z => g z * ∏ i ∈ s, (z - a i) ^ m i
    Integrable (fun z : ℂ => Real.log (‖f z‖ ^ 2 * Real.exp (-φ z)) * ddcDens u z) ∧
      ∫ z : ℂ, Real.log (‖f z‖ ^ 2 * Real.exp (-φ z)) * ddcDens u z =
        (∑ i ∈ s, (m i : ℝ) * u (a i)) - ∫ z : ℂ, ddcDens φ z * u z := by
  intro f
  obtain ⟨hg_int, hg_eq⟩ := integral_log_norm_sq_holo_mul_ddcDens_eq_zero hU hg hg_ne hu hcs hsub
  obtain ⟨hφ_int, _, hφ_eq⟩ := greens_second_identity_ddcDens hU hφ hu hcs hsub
  have hpt_int : ∀ i ∈ s, Integrable (fun z : ℂ => (m i : ℝ) * (Real.log (‖z - a i‖ ^ 2) * ddcDens u z)) :=
    fun i _ => (poincare_lelong_point hu hcs (a i)).1.const_mul (m i : ℝ)
  have hsum_int : Integrable (fun z : ℂ => ∑ i ∈ s, (m i : ℝ) * (Real.log (‖z - a i‖ ^ 2) * ddcDens u z)) :=
    integrable_finsetSum s hpt_int
  let rhsFn : ℂ → ℝ := fun z =>
    Real.log (‖g z‖ ^ 2) * ddcDens u z +
      (∑ i ∈ s, (m i : ℝ) * (Real.log (‖z - a i‖ ^ 2) * ddcDens u z)) -
      φ z * ddcDens u z
  have hrhs_int : Integrable rhsFn :=
    (hg_int.add hsum_int).sub hφ_int
  have hbad_null : volume (↑(s.image a) : Set ℂ) = 0 :=
    (Finset.finite_toSet _).measure_zero volume
  have hae : (fun z : ℂ => Real.log (‖f z‖ ^ 2 * Real.exp (-φ z)) * ddcDens u z) =ᵐ[volume] rhsFn := by
    have hmem_ae : ∀ᵐ z : ℂ ∂volume, z ∉ (↑(s.image a) : Set ℂ) := by
      rw [ae_iff]
      convert hbad_null using 2
      ext z
      simp
    filter_upwards [hmem_ae] with z hz_not
    by_cases hsupp : z ∈ tsupport u
    · have hzU : z ∈ U := hsub hsupp
      have hne_i : ∀ i ∈ s, z - a i ≠ 0 := by
        intro i hi h0
        apply hz_not
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨i, hi, (sub_eq_zero.mp h0).symm⟩
      have hprod_ne : (∏ i ∈ s, (z - a i) ^ m i) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i hi => zpow_ne_zero (m i) (hne_i i hi)
      have hf_ne : f z ≠ 0 := mul_ne_zero (hg_ne z hzU) hprod_ne
      have hf_norm_sq : ‖f z‖ ^ 2 = ‖g z‖ ^ 2 * ∏ i ∈ s, (‖z - a i‖ ^ 2) ^ m i := by
        dsimp only [f]
        rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [norm_zpow, ← zpow_natCast (‖z - a i‖ ^ m i) 2, ← _root_.zpow_mul,
          mul_comm (m i) ((2 : ℕ) : ℤ), _root_.zpow_mul, zpow_natCast]
      have hlog_prod : Real.log (∏ i ∈ s, (‖z - a i‖ ^ 2) ^ m i) =
          ∑ i ∈ s, (m i : ℝ) * Real.log (‖z - a i‖ ^ 2) := by
        rw [Real.log_prod fun i hi => zpow_ne_zero (m i) (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne_i i hi)))]
        refine Finset.sum_congr rfl fun i _ => Real.log_zpow _ _
      have hlog_f : Real.log (‖f z‖ ^ 2 * Real.exp (-φ z)) =
          Real.log (‖g z‖ ^ 2) + (∑ i ∈ s, (m i : ℝ) * Real.log (‖z - a i‖ ^ 2)) - φ z := by
        rw [Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hf_ne)) (Real.exp_pos _).ne',
          Real.log_exp, hf_norm_sq,
          Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hg_ne z hzU)))
            (Finset.prod_ne_zero_iff.mpr fun i hi =>
              zpow_ne_zero (m i) (pow_ne_zero 2 (norm_ne_zero_iff.mpr (hne_i i hi)))),
          hlog_prod]
        ring
      dsimp only [rhsFn]
      rw [hlog_f]
      simp only [sub_mul, add_mul, Finset.sum_mul, mul_assoc]
    · have hddc0 : ddcDens u z = 0 := by
        unfold ddcDens laplacianC
        rw [(fderiv_eq_zero_of_notMem_tsupport hsupp).2.2]
        simp
      simp [rhsFn, hddc0]
  refine ⟨hrhs_int.congr hae.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hae]
  have h1 : ∫ z : ℂ, rhsFn z =
      (∫ z : ℂ, (Real.log (‖g z‖ ^ 2) * ddcDens u z +
        ∑ i ∈ s, (m i : ℝ) * (Real.log (‖z - a i‖ ^ 2) * ddcDens u z))) -
      ∫ z : ℂ, φ z * ddcDens u z :=
    MeasureTheory.integral_sub (hg_int.add hsum_int) hφ_int
  have h2 : ∫ z : ℂ, (Real.log (‖g z‖ ^ 2) * ddcDens u z +
        ∑ i ∈ s, (m i : ℝ) * (Real.log (‖z - a i‖ ^ 2) * ddcDens u z)) =
      (∫ z : ℂ, Real.log (‖g z‖ ^ 2) * ddcDens u z) +
      ∫ z : ℂ, ∑ i ∈ s, (m i : ℝ) * (Real.log (‖z - a i‖ ^ 2) * ddcDens u z) :=
    MeasureTheory.integral_add hg_int hsum_int
  rw [h1, h2, MeasureTheory.integral_finsetSum s hpt_int, hg_eq, zero_add, hφ_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, (poincare_lelong_point hu hcs (a i)).2]

/-- **Packaged `MetrizedLineBundle` Poincaré–Lelong Equation**:
stated directly in terms of `L : MetrizedLineBundle 1 Unit U`, `ChernFirstForm L`, and a
factorized section `f(z) = g(z) * ∏ (z - a_i)^{m_i}`! -/
theorem poincare_lelong_metrized_bundle {κ : Type*} (s : Finset κ) (m : κ → ℤ) (a : κ → ℂ)
    {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℝ} (hφ : ContDiffOn ℝ 2 φ U)
    {g : ℂ → ℂ} (hg : ∀ z ∈ U, ContDiffAt ℂ 2 g z) (hg_ne : ∀ z ∈ U, g z ≠ 0)
    {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) (hsub : tsupport u ⊆ U) :
    let U₁ : Set (Fin 1 → ℂ) := {w | w 0 ∈ U}
    have hU₁ : IsOpen U₁ := hU.preimage (continuous_apply 0)
    have hφ₁ : ∀ w ∈ U₁, ContDiffAt ℝ 2 (fun y : Fin 1 → ℂ => φ (y 0)) w := fun w hw =>
      (hφ.contDiffAt (hU.mem_nhds hw)).comp w
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).contDiff.contDiffAt
    let L : MetrizedLineBundle 1 Unit U₁ :=
      MetrizedLineBundle.trivial 1 U₁ hU₁ (fun y => φ (y 0)) hφ₁
    let f : ℂ → ℂ := fun z => g z * ∏ i ∈ s, (z - a i) ^ m i
    ∫ z : ℂ, Real.log (‖f z‖ ^ 2 * Real.exp (-φ z)) * ddcDens u z =
      (∑ i ∈ s, (m i : ℝ) * u (a i)) -
        ∫ z : ℂ, (ChernFirstForm L).eval (fun _ => z) (Pi.single 0 1) * u z := by
  intro U₁ hU₁ hφ₁ L f
  have hpl := (poincare_lelong_equation s m a hU hφ hg hg_ne hu hcs hsub).2
  rw [hpl]
  congr 1
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun z => ?_)
  dsimp only
  by_cases hmem : z ∈ tsupport u
  · have hzU : z ∈ U := hsub hmem
    have hzU₁ : (fun _ : Fin 1 => z) ∈ U₁ := hzU
    rw [chernFirstForm_eval_eq_of_mem L (i := ()) hzU₁ (Pi.single 0 1)]
    change ddcDens φ z * u z =
      ((1 / Real.pi) * leviForm (fun y : Fin 1 → ℂ => φ (y 0)) (fun _ => z) (Pi.single 0 1)) * u z
    rw [← ddcDens_eq_inv_pi_mul_leviForm (hφ.contDiffAt (hU.mem_nhds hzU))]
  · rw [image_eq_zero_of_notMem_tsupport hmem, mul_zero, mul_zero]

/-- **Distributional Chern–Weil Metric-Change Identity** (directly ready for `ArakelovIntersection`
and `GreenCurrents`):
for any two `C²` metrics `φ₁, φ₂` on open `U ⊇ tsupport u`:
$$\int_{\mathbb{C}} (\varphi_2(z) - \varphi_1(z))\, \mathrm{dd}^c u(z)
  = \int_{\mathbb{C}} \bigl(c_1(\varphi_2)(z) - c_1(\varphi_1)(z)\bigr)\, u(z).$$ -/
theorem poincare_lelong_metric_change {U : Set ℂ} (hU : IsOpen U) {φ₁ φ₂ u : ℂ → ℝ}
    (hφ₁ : ContDiffOn ℝ 2 φ₁ U) (hφ₂ : ContDiffOn ℝ 2 φ₂ U)
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) (hsub : tsupport u ⊆ U) :
    ∫ z : ℂ, (φ₂ z - φ₁ z) * ddcDens u z =
      ∫ z : ℂ, (ddcDens φ₂ z - ddcDens φ₁ z) * u z := by
  obtain ⟨h1a, h1b, heq1⟩ := greens_second_identity_ddcDens hU hφ₁ hu hcs hsub
  obtain ⟨h2a, h2b, heq2⟩ := greens_second_identity_ddcDens hU hφ₂ hu hcs hsub
  have eL : (fun z : ℂ => (φ₂ z - φ₁ z) * ddcDens u z) =
      fun z => φ₂ z * ddcDens u z - φ₁ z * ddcDens u z := by funext z; ring
  have eR : (fun z : ℂ => (ddcDens φ₂ z - ddcDens φ₁ z) * u z) =
      fun z => ddcDens φ₂ z * u z - ddcDens φ₁ z * u z := by funext z; ring
  rw [eL, eR, MeasureTheory.integral_sub h2a h1a, MeasureTheory.integral_sub h2b h1b, heq1, heq2]

/-! ### Part D: Higher-Dimensional Coordinate-Hyperplane Poincaré–Lelong (`Fin (d + 1) → ℂ`) -/

/-- Directional `dd^c` density along coordinate `j : Fin n` on `ℂ^n`:
`ddcCoord j u z = (1 / π) * leviForm u z (Pi.single j 1)`. -/
def ddcCoord {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  (1 / Real.pi) * leviForm u z (Pi.single j 1)

/-- Fiberwise identification `ddcCoord j u (Fin.insertNth j ζ w) = ddcDens (fun ξ => u (Fin.insertNth j ξ w)) ζ`. -/
lemma ddcCoord_insertNth {d : ℕ} (j : Fin (d + 1)) {u : (Fin (d + 1) → ℂ) → ℝ}
    (hu : ContDiff ℝ 2 u) (w : Fin d → ℂ) (ζ : ℂ) :
    ddcCoord j u (Fin.insertNth j ζ w) =
      ddcDens (fun ξ : ℂ => u (Fin.insertNth j ξ w)) ζ := by
  unfold ddcCoord ddcDens
  have hline : ∀ e : ℂ,
      fderiv ℝ (fderiv ℝ u) (Fin.insertNth j ζ w) (Pi.single j e) (Pi.single j e) =
        fderiv ℝ (fderiv ℝ (fun ξ : ℂ => u (Fin.insertNth j ξ w))) ζ e e := by
    intro e
    let g : ℂ → ℝ := fun ξ => u (Fin.insertNth j ξ w)
    have hins_cd : ContDiff ℝ 2 (fun ξ : ℂ => Fin.insertNth (α := fun _ => ℂ) j ξ w) := by
      refine contDiff_pi.mpr fun k => ?_
      by_cases hkj : k = j
      · subst hkj; simp only [Fin.insertNth_apply_same]; exact contDiff_id
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hkj
        simpa using contDiff_const
    have hg_cd : ContDiff ℝ 2 g := hu.comp hins_cd
    have h1 := deriv_deriv_line (J := Fin (d + 1)) (hu.contDiffAt (x := Fin.insertNth j ζ w)) (Pi.single j e)
    have h2 : deriv (deriv fun s : ℝ => g (ζ + s • e)) 0 = fderiv ℝ (fderiv ℝ g) ζ e e := by
      have hline_g : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ζ + t • e) e s := fun s =>
        (((hasDerivAt_id s).smul_const e).const_add ζ).congr_deriv (one_smul ℝ e)
      have hev : deriv (fun s : ℝ => g (ζ + s • e)) = fun s => fderiv ℝ g (ζ + s • e) e := by
        funext s
        exact (((hg_cd.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt s (hline_g s)).deriv
      rw [hev]
      exact (hasDerivAt_complex_line (hg_cd.contDiffAt (x := ζ)) e).2.deriv
    have hfun : (fun s : ℝ => u (Fin.insertNth j ζ w + s • (Pi.single j e : Fin (d + 1) → ℂ))) =
        fun s : ℝ => g (ζ + s • e) := by
      funext s
      dsimp only [g]
      congr 1
      ext k
      by_cases hkj : k = j
      · subst hkj; simp
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hkj
        simp
    rw [← h1, hfun, h2]
  have hI_single : Complex.I • Pi.single j (1 : ℂ) = Pi.single j Complex.I := by
    ext k
    by_cases hkj : k = j
    · subst hkj; simp
    · simp [Pi.single_eq_of_ne hkj]
  unfold leviForm laplacianC
  rw [hI_single, hline 1, hline Complex.I]
  ring

/-- **Higher-Dimensional Coordinate-Hyperplane Poincaré–Lelong Formula on `ℂ^{d+1}`** (directly
ready for `Stage14M3_GreenCurrents` and `Stage14M3_ArakelovIntersection`):
for any `j : Fin (d + 1)` and any `C²` compactly supported `u : (Fin (d + 1) → ℂ) → ℝ`:
$$\int_{\mathbb{C}^{d+1}} \log(\|z_j\|^2)\, \mathrm{dd}^c_j u(z)\, dV(z)
  = \int_{\mathbb{C}^d} u\bigl(\mathrm{insertNth}_j(0, w)\bigr)\, dV(w).$$ -/
theorem poincare_lelong_coord_hyperplane {d : ℕ} (j : Fin (d + 1))
    {u : (Fin (d + 1) → ℂ) → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    Integrable (fun z : Fin (d + 1) → ℂ => Real.log (‖z j‖ ^ 2) * ddcCoord j u z) ∧
      ∫ z : Fin (d + 1) → ℂ, Real.log (‖z j‖ ^ 2) * ddcCoord j u z =
        ∫ w : Fin d → ℂ, u (Fin.insertNth j 0 w) := by
  let e : (Fin (d + 1) → ℂ) ≃ᵐ ℂ × (Fin d → ℂ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) j
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℂ) j
  have hsymm : ∀ (ζ : ℂ) (w : Fin d → ℂ), e.symm (ζ, w) = Fin.insertNth j ζ w := fun _ _ => rfl
  have hfib_cd : ∀ w : Fin d → ℂ, ContDiff ℝ 2 (fun ζ : ℂ => u (Fin.insertNth j ζ w)) := by
    intro w
    have hins : ContDiff ℝ 2 (fun ζ : ℂ => Fin.insertNth (α := fun _ => ℂ) j ζ w) := by
      refine contDiff_pi.mpr fun k => ?_
      by_cases hkj : k = j
      · subst hkj; simp only [Fin.insertNth_apply_same]; exact contDiff_id
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hkj
        simpa using contDiff_const
    exact hu.comp hins
  obtain ⟨R₀, hR₀⟩ := hcs.isBounded.subset_closedBall (0 : Fin (d + 1) → ℂ)
  set R : ℝ := max R₀ 1 + 1
  have hR_pos : 0 < R := by positivity
  have hfib_cs : ∀ w : Fin d → ℂ, HasCompactSupport (fun ζ : ℂ => u (Fin.insertNth j ζ w)) := by
    intro w
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R) fun ζ hζ => ?_
    have hmem : Fin.insertNth (α := fun _ => ℂ) j ζ w ∈ tsupport u := subset_tsupport u hζ
    have hle : ‖Fin.insertNth (α := fun _ => ℂ) j ζ w‖ ≤ R₀ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR₀ hmem
    have hζ_le : ‖ζ‖ ≤ ‖Fin.insertNth (α := fun _ => ℂ) j ζ w‖ := by
      have h := norm_le_pi_norm (Fin.insertNth (α := fun _ => ℂ) j ζ w) j
      simpa using h
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : R₀ ≤ max R₀ 1 := le_max_left R₀ 1
    linarith
  have hfib_int : ∀ w : Fin d → ℂ,
      Integrable (fun ζ : ℂ => Real.log (‖ζ‖ ^ 2) * ddcDens (fun ξ => u (Fin.insertNth j ξ w)) ζ) ∧
      ∫ ζ : ℂ, Real.log (‖ζ‖ ^ 2) * ddcDens (fun ξ => u (Fin.insertNth j ξ w)) ζ =
        u (Fin.insertNth j 0 w) := fun w => by
    simpa only [sub_zero] using poincare_lelong_point (hfib_cd w) (hfib_cs w) 0
  have hddc_cont : Continuous (ddcCoord j u) := by
    have h2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
      (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    unfold ddcCoord leviForm
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin (d + 1) → ℂ) R).exists_bound_of_continuousOn
    hddc_cont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _)
    (hC 0 (Metric.mem_closedBall_self hR_pos.le))
  have hlog_int_C : Integrable (fun ζ : ℂ => (Metric.closedBall (0 : ℂ) R).indicator
      (fun ξ => |Real.log (‖ξ‖ ^ 2)|) ζ) volume := by
    have h2 := (integrable_closedBall_indicator_log_norm hR_pos).const_mul 2
    refine h2.congr (ae_of_all _ fun ζ => ?_)
    dsimp only
    by_cases hm : ζ ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, Real.log_pow, Nat.cast_ofNat, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    · simp [Set.indicator_of_notMem hm]
  have hball_w : Integrable (fun w : Fin d → ℂ =>
      (Metric.closedBall (0 : Fin d → ℂ) R).indicator (fun _ => C) w) volume := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact integrableOn_const (isCompact_closedBall (0 : Fin d → ℂ) R).measure_lt_top.ne
  have hprod_int : Integrable (fun q : ℂ × (Fin d → ℂ) =>
      Real.log (‖q.1‖ ^ 2) * ddcCoord j u (e.symm q)) (volume.prod volume) := by
    refine (hlog_int_C.mul_prod hball_w).mono' ?_ (ae_of_all _ fun q => ?_)
    · have hmeas_e : Measurable (e.symm : ℂ × (Fin d → ℂ) → Fin (d + 1) → ℂ) := e.symm.measurable
      exact ((Real.measurable_log.comp ((measurable_norm.comp measurable_fst).pow_const 2)).mul
        (hddc_cont.measurable.comp hmeas_e)).aestronglyMeasurable
    · by_cases hmem : e.symm q ∈ tsupport u
      · have hle : ‖e.symm q‖ ≤ R := by
          have h1 : ‖e.symm q‖ ≤ R₀ := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hR₀ hmem
          have h2 : R₀ ≤ max R₀ 1 := le_max_left R₀ 1
          linarith
        have hq1 : q.1 ∈ Metric.closedBall (0 : ℂ) R := by
          rw [Metric.mem_closedBall, dist_zero_right]
          have h := norm_le_pi_norm (e.symm q) j
          simpa [hsymm] using h.trans hle
        have hq2 : q.2 ∈ Metric.closedBall (0 : Fin d → ℂ) R := by
          rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR_pos.le]
          intro i
          have h := norm_le_pi_norm (e.symm q) (j.succAbove i)
          simpa [hsymm] using h.trans hle
        rw [Set.indicator_of_mem hq1, Set.indicator_of_mem hq2, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (hC (e.symm q) (by rwa [Metric.mem_closedBall, dist_zero_right])) (abs_nonneg _)
      · have hopen : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
        have hfd2 : fderiv ℝ (fderiv ℝ u) (e.symm q) = 0 := by
          have hfd_ev : fderiv ℝ u =ᶠ[𝓝 (e.symm q)] fun _ => 0 := by
            filter_upwards [hopen.mem_nhds hmem] with y hy
            have hy_ev : u =ᶠ[𝓝 y] fun _ => 0 :=
              Filter.eventually_of_mem (hopen.mem_nhds hy) fun x hx => image_eq_zero_of_notMem_tsupport hx
            rw [hy_ev.fderiv_eq]; simp
          rw [hfd_ev.fderiv_eq]; simp
        have hddc0 : ddcCoord j u (e.symm q) = 0 := by
          unfold ddcCoord leviForm; rw [hfd2]; simp
        rw [hddc0, mul_zero, norm_zero]
        exact mul_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)
          (Set.indicator_nonneg (fun _ _ => hC0) _)
  have hint_z : Integrable (fun z : Fin (d + 1) → ℂ => Real.log (‖z j‖ ^ 2) * ddcCoord j u z) volume := by
    have h := (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding
      (g := fun z : Fin (d + 1) → ℂ => Real.log (‖z j‖ ^ 2) * ddcCoord j u z)).mp
    have heq : ((fun z : Fin (d + 1) → ℂ => Real.log (‖z j‖ ^ 2) * ddcCoord j u z) ∘ e.symm) =
        fun q : ℂ × (Fin d → ℂ) => Real.log (‖q.1‖ ^ 2) * ddcCoord j u (e.symm q) := by
      funext q; simp [hsymm]
    rw [heq] at h
    exact h hprod_int
  refine ⟨hint_z, ?_⟩
  have hch := hmp.symm.integral_comp'
    (g := fun z : Fin (d + 1) → ℂ => Real.log (‖z j‖ ^ 2) * ddcCoord j u z)
  rw [← hch]
  have heq : (fun q : ℂ × (Fin d → ℂ) => Real.log (‖(e.symm q) j‖ ^ 2) * ddcCoord j u (e.symm q)) =
      fun q => Real.log (‖q.1‖ ^ 2) * ddcCoord j u (e.symm q) := by
    funext q; simp [hsymm]
  rw [heq, MeasureTheory.integral_prod_symm _ hprod_int]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun w => ?_)
  dsimp only
  have hfib_eq : (fun ζ : ℂ => Real.log (‖ζ‖ ^ 2) * ddcCoord j u (e.symm (ζ, w))) =
      fun ζ => Real.log (‖ζ‖ ^ 2) * ddcDens (fun ξ => u (Fin.insertNth j ξ w)) ζ := by
    funext ζ
    rw [hsymm, ddcCoord_insertNth j hu w ζ]
  rw [hfib_eq]
  exact (hfib_int w).2

end PoincareLelong

/-! ## Section 5: Direct Bridges to `Stage11HermitianCurvature`, `Stage11ArakelovFaltings` & M3 Wave 2 -/

section Wave2Bridges

/-- **Bridge 1 (Exact First Chern Degree of `peterssonLineBundle k` on `SL₂(ℤ) \ ℍ`)**:
integrating `(ChernFirstForm (peterssonLineBundle k)).eval _ (Pi.single 0 1)` over the standard
fundamental domain `stdFD` yields the exact degree `k / 12` matching
`Stage11HermitianCurvature.firstChernIntegral_weight_k_eq` and
`Stage11ArakelovFaltings.ArithLineBundle.hodgeBundle`. -/
theorem petersson_degree_matches_stage11 (k : ℤ) :
    (∫ p in Stage10PeterssonHecke.stdFD,
      if hp : 0 < p.2 then
        (ChernFirstForm (peterssonLineBundle k)).eval (fun _ => (pairToUHP p hp : ℂ)) (Pi.single 0 1)
      else 0) = (k : ℝ) / 12 := by
  have hcongr : Set.EqOn
      (fun p : ℝ × ℝ => if hp : 0 < p.2 then
        (ChernFirstForm (peterssonLineBundle k)).eval (fun _ => (pairToUHP p hp : ℂ)) (Pi.single 0 1)
        else 0)
      (fun p : ℝ × ℝ => (k : ℝ) / (4 * Real.pi) * (p.2) ^ (-2 : ℝ)) stdFD := by
    intro p hp
    dsimp only
    rw [dif_pos hp.2.1, peterssonLineBundle_chernFirstForm_eq, firstChernDensity_weight_k_eq,
      pairToUHP_im]
    simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_stdFD hcongr]
  exact firstChernIntegral_weight_k_eq k

/-- **Bridge 2 (Faltings Height & Petersson Curvature Matching)**:
the Euclidean Laplacian of the concrete Faltings height `Stage11ArakelovFaltings.faltingsHeight`
at `τ ∈ ℍ` equals `2 * (peterssonLineBundle 1).curvatureAt (fun _ => τ) (Pi.single 0 1)`. -/
theorem petersson_faltingsHeight_curvature_bridge (τ : UpperHalfPlane) :
    euclLaplacianR faltingsHeight τ =
      2 * (peterssonLineBundle 1).curvatureAt (fun _ => (τ : ℂ)) (Pi.single 0 1) := by
  rw [euclLaplacianR_faltingsHeight_eq_two_chernCurvature, peterssonLineBundle_curvature_eq]
  simp

/-- **Bridge 3 (Metric Comparison / Sup-Norm Inequality for `ChowFormHeights` & `GagaAndSections`)**:
if two metrics on the same holomorphic line bundle satisfy `φ₁ ≤ φ₂ + C` everywhere on `X`, then
for every global holomorphic section `s` and every `z ∈ X`,
`‖s(z)‖²_{h₂} ≤ exp(C) * ‖s(z)‖²_{h₁}`. -/
theorem section_ptNormSq_metric_comparison {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L₁ L₂ : MetrizedLineBundle d ι X} (hcov : L₁.openCover = L₂.openCover)
    (_htrans : L₁.transFn = L₂.transFn) {C : ℝ}
    (hwt : ∀ i, ∀ z ∈ L₁.openCover i, L₁.weight i z ≤ L₂.weight i z + C)
    (s₁ : L₁.Section) (s₂ : L₂.Section)
    (hsec : ∀ i, ∀ z ∈ L₁.openCover i, s₁.sec i z = s₂.sec i z) {z : Fin d → ℂ} (hz : z ∈ X) :
    s₂.ptNormSq z ≤ Real.exp C * s₁.ptNormSq z := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L₁.covers hz)
  have hi2 : z ∈ L₂.openCover i := by rwa [← hcov]
  rw [s₁.ptNormSq_eq_of_mem hi, s₂.ptNormSq_eq_of_mem hi2, ← hsec i z hi]
  have hexp : Real.exp (-L₂.weight i z) ≤ Real.exp C * Real.exp (-L₁.weight i z) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith [hwt i z hi]
  have hmul := mul_le_mul_of_nonneg_left hexp (sq_nonneg ‖s₁.sec i z‖)
  linarith

/-- **Bridge 4 (Metric-Twist Scaling Effect on Section Norms for `ArakelovIntersection` &
`ChowFormHeights`)**:
twisting a `MetrizedLineBundle` by `u` (`φ ↦ φ + u`) multiplies every section's pointwise norm
squared by `exp (-u z)`. -/
theorem section_ptNormSq_twistMetric {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) (u : (Fin d → ℂ) → ℝ)
    (hu : ∀ i, ∀ z ∈ L.openCover i, ContDiffAt ℝ 2 u z) (s : L.Section)
    {z : Fin d → ℂ} (hz : z ∈ X) :
    let s' : (L.twistMetric u hu).Section :=
      { sec := s.sec, sec_holo := s.sec_holo, sec_compat := s.sec_compat }
    s'.ptNormSq z = Real.exp (-u z) * s.ptNormSq z := by
  intro s'
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  rw [s'.ptNormSq_eq_of_mem hi, s.ptNormSq_eq_of_mem hi]
  change ‖s.sec i z‖ ^ 2 * Real.exp (-(L.weight i z + u z)) = _
  rw [neg_add, Real.exp_add]
  ring

/-- **Bridge 5 (Bergman Extremal Bound on a `MetrizedLineBundle` for `GagaAndSections`)**:
for any finite family of sections `e : Fin r → L.Section` on a trivialized bundle `L` and linear
combination `s = ∑ c_k e_k`, the pointwise Hermitian norm squared is bounded by the finite-rank
Bergman kernel `∑_k ‖e_k(z)‖²_h` times `∑_k ‖c_k‖²` (wired directly to `HermitianCurvatureCore`). -/
theorem metrizedLineBundle_bergman_extremal {d r : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    {L : MetrizedLineBundle d ι X} (e : Fin r → L.Section) (c : Fin r → ℂ)
    {z : Fin d → ℂ} (hz : z ∈ X) :
    ∃ i, z ∈ L.openCover i ∧
      ‖∑ k : Fin r, c k * (e k).sec i z‖ ^ 2 * Real.exp (-L.weight i z) ≤
        (∑ k : Fin r, (e k).ptNormSq z) * (∑ k : Fin r, ‖c k‖ ^ 2) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (L.covers hz)
  refine ⟨i, hi, ?_⟩
  have hberg := HermitianCurvatureCore.bergman_extremal_bound (L.weight i) 1
    (fun k y => (e k).sec i y) c z
  simp only [HermitianCurvatureCore.ptNormSq, HermitianCurvatureCore.bergmanKernel,
    Nat.cast_one, neg_one_mul] at hberg
  have hsum : (∑ k : Fin r, ‖(e k).sec i z‖ ^ 2 * Real.exp (-L.weight i z)) =
      ∑ k : Fin r, (e k).ptNormSq z :=
    Finset.sum_congr rfl fun k _ => ((e k).ptNormSq_eq_of_mem hi).symm
  rwa [hsum] at hberg

/-- **Bridge 6 (Nef / Semipositive Cone Closure under Pointwise Curvature Limits for
`NefRiemannRoch`)**:
if a sequence of semipositive metrized line bundles `L_n` over `X` has curvatures converging
pointwise to the curvature of `L`, then `L` is also `SemipositiveMetric`. -/
theorem semipositiveMetric_of_tendsto {d : ℕ} {ι : Type*} {X : Set (Fin d → ℂ)}
    (L : MetrizedLineBundle d ι X) (Lseq : ℕ → MetrizedLineBundle d ι X)
    (hpos : ∀ n, SemipositiveMetric (Lseq n))
    (hlim : ∀ z ∈ X, ∀ w : Fin d → ℂ,
      Tendsto (fun n => (Lseq n).curvatureAt z w) atTop (𝓝 (L.curvatureAt z w))) :
    SemipositiveMetric L := fun z hz w =>
  ge_of_tendsto' (hlim z hz w) fun n => hpos n z hz w

/-- **Bridge 7 (Arakelov Hodge Bundle Degree & Curvature Coupling)**:
the generic-fiber degree of `Stage11ArakelovFaltings.ArithLineBundle.hodgeBundle k c` matches
the exact First Chern integral of `peterssonLineBundle k` on `stdFD`. -/
theorem petersson_hodgeBundle_deg_bridge {m : ℕ} {E_arch : Type*} [AddCommGroup E_arch]
    (k : ℤ) (c : ℝ) :
    (ArithLineBundle.hodgeBundle (m := m) (E_arch := E_arch) k c).geomDeg =
      ∫ p in Stage10PeterssonHecke.stdFD,
        if hp : 0 < p.2 then
          (ChernFirstForm (peterssonLineBundle k)).eval (fun _ => (pairToUHP p hp : ℂ)) (Pi.single 0 1)
        else 0 := by
  rw [petersson_degree_matches_stage11 k]
  rfl

end Wave2Bridges

end

end RHDirect.Stage14M3_HermitianLineBundles
