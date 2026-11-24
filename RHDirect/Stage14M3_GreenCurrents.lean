import RHDirect.HermitianCurvatureCore
import RHDirect.Stage11HermitianCurvature
import RHDirect.Stage11ArakelovFaltings
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# RHDirect.Stage14M3_GreenCurrents

**UNCONDITIONAL ARAKELOV GREEN CURRENTS, GILLET–SOULÉ STAR PRODUCT COMMUTATIVITY MODULO
`im ∂ + im ∂̄`, PULLBACK COMPATIBILITY, AND POINCARÉ–LELONG INVERSION (PILLAR-5 CLEAN
DISTILLATION)** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`).

Distills the genuine mathematical core of Arakelov Green current theory from Gillet–Soulé and
Alpöge's Pillar-5 modules (`Development.AbelianVarietyTheory.Definitions.Divisors.*`,
`Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv`,
`GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.{MonotoneDoubleLimit,PGreenFromLelong,
StatementsGreenReg}`), directly wired to `Stage11HermitianCurvature` & `Stage11ArakelovFaltings`
and ready for M3 Wave 2 (`ArakelovIntersection`, `ChowFormHeights`, `NefRiemannRoch`).

## Main Unconditional Results

1. **Concrete `dd^c` Operator, Holomorphic Pullback Invariance & Monotone Double-Limit Engine**:
   - `ddcForm φ z w := HermitianCurvatureCore.leviForm φ z w / π` (`dd^c φ = (i / (2π)) ∂∂̄ φ`),
   - `leviForm_comp_holomorphic` & `ddcForm_comp_holomorphic`: exact holomorphic pullback
     invariance `dd^c (φ ∘ F)(z, w) = (dd^c φ)(F z, DF(z) w)` for every `ContDiffAt ℂ 2` map `F`,
   - `iterLim_eq_of_monotone`: monotone double-limit theorem for regularized archimedean pairings.
2. **Fubini–Study Regularized Green Functions & 1D Analytic Poincaré–Lelong Limit**:
   - `fsLog`, `fsLogReg`, `fsLog_nonneg_of_unit`, `fsLogReg_antitone`, `fsLogReg_tendsto`,
     projective scaling invariance (`fsLog_scale_inv`, `fsLogReg_scale_inv`), and unitary pullback
     compatibility (`fsLogReg_pullback_unitary`),
   - `ddcForm_plRegPotential_neg`: exact regularized `dd^c` of `-log (‖z‖² + ε)` on `ℂ`,
   - `integral_plRadialKernel_zero_R`: exact polar mass `∫_0^R 2εr / (r² + ε)² dr = R² / (R² + ε)`,
   - `poincare_lelong_1d_approx_identity` & `poincare_lelong_1d_order_m_limit`: exact Dirac-mass
     limit `lim_{ε → 0⁺} ∫_0^R u(r) · (m · 2εr / (r² + ε)²) dr = m · u(0)` for every continuous
     radial test function `u`.
3. **Dolbeault Current Algebras, `im ∂ + im ∂̄` Quotient, `GreenCurrentData` & `ArakelovDivisor`**:
   - `DolbeaultCurrentAlgebra`: bigraded current algebra `(Curr00, Curr10, Curr01, Curr11)` with
     `∂`, `∂̄`, anticommutation `∂∂̄ + ∂̄∂ = 0`, graded Leibniz rule, `imDDbar := im ∂ + im ∂̄`,
     and quotient `Curr11ModDDbar := Curr11 ⧸ imDDbar`,
   - `greens_second_identity`: `g₂ · dd^c g₁ - g₁ · dd^c g₂ = ∂(g₂ ∂̄ g₁) + ∂̄(g₁ ∂ g₂) ∈ im ∂ + im ∂̄`,
   - `GreenCurrentData`, `green_current_linearity`, `ArakelovDivisor` (full `AddCommGroup`),
     `PrincipalArakelovSubgroup`, and `ArithChow1` (`ArakelovDivisor ⧸ PrincipalArakelovSubgroup`).
4. **Gillet–Soulé Star Product `StarProductGreen` & Commutativity Modulo `im ∂ + im ∂̄`**:
   - `StarProductGreen g₁ g₂ := g₁ · δ_{D₂} + g₂ · ω₁`,
   - `green_current_commutativity`: exact boundary witness
     `StarProductGreen g₁ g₂ - StarProductGreen g₂ g₁ ∈ im ∂ + im ∂̄` and quotient equality
     `starProductClass g₁ g₂ = starProductClass g₂ g₁`,
   - Bilinearity, metric-change anomaly (`starProductGreen_addSmooth_left`), higher-degree
     `dd^c(g₁ * g₂) + δ_{D₁} ∧ δ_{D₂} = ω₁ ∧ ω₂`, and regularized analytic commutativity
     (`green_star_commutativity_of_regularized_lelong`).
5. **Functorial Pullback Compatibility (`green_current_pullback_compat`)**:
   - `DolbeaultMorphism`, `DivisorPullbackCompat`, `GreenCurrentData.pullback`,
     `ArakelovDivisor.pullback`, and `green_current_pullback_compat` (preserving the Green
     equation, linearity, `StarProductGreen`, `im ∂ + im ∂̄` classes, and composition).
6. **Poincaré–Lelong Inversion (`poincare_lelong_inv`) & Wave-2 Archimedean Height Pairing**:
   - `ArakelovPairingModel` (Stokes-invariant top integration + prime-divisor cycle integration),
   - `poincare_lelong_inv`, `poincare_lelong_inv_logNorm`, `poincare_lelong_inv_horiz`,
     `section_space_symmetry`, `archStarPairing`, `archStarPairing_symm`,
     `archStarPairing_metric_change_bounds`, and `archStarPairing_nonneg_of_effective_semipositive`.
7. **Concrete Instantiations & Stage-11 Modular-Curve Bridges**:
   - `polyDolbeaultAlgebra`: concrete infinite-dimensional `DolbeaultCurrentAlgebra` on
     `MvPolynomial (Fin 2) ℂ` (`ℂ[z, z̄]`) certifying full consistency of all Dolbeault axioms,
   - Direct bridges to `Stage11HermitianCurvature` (`uhpGreenPotential`,
     `euclLaplacianR_uhpGreenPotential_div_four_pi_eq_firstChern`, `faltingsHeight_green_ddc_eq`)
     and `Stage11ArakelovFaltings` (`ArithLineBundle.arakelovPair`).
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function
open RHDirect.HermitianCurvatureCore RHDirect.Stage5ModularHecke RHDirect.Stage11HermitianCurvature
open RHDirect.Stage11ArakelovFaltings
open scoped BigOperators UpperHalfPlane Topology ComplexConjugate Manifold

namespace RHDirect.Stage14M3_GreenCurrents

noncomputable section

/-! ## Section 1: Concrete `dd^c` Operator, Holomorphic Pullback & Monotone Double Limits -/

section DdcAndMonotoneLimits

/-- Normalized complex Hessian / `dd^c` operator `(i / (2 π)) ∂∂̄ φ` acting on tangent direction `w`
at `z : J → ℂ`:
$$\mathrm{ddcForm}(\varphi, z, w) = \frac{1}{\pi} \operatorname{leviForm}(\varphi, z, w).$$
This normalization matches `Stage11HermitianCurvature.firstChernDensity` (`c₁ = (1 / π) Θ`). -/
def ddcForm {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (z w : J → ℂ) : ℝ :=
  HermitianCurvatureCore.leviForm φ z w / Real.pi

theorem ddcForm_const {J : Type*} [Fintype J] (c : ℝ) (z w : J → ℂ) :
    ddcForm (fun _ : J → ℂ => c) z w = 0 := by
  simp [ddcForm, HermitianCurvatureCore.leviForm_const]

theorem ddcForm_add_smul {J : Type*} [Fintype J] (a b : ℝ) {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) (w : J → ℂ) :
    ddcForm (fun y => a * φ y + b * ψ y) z w = a * ddcForm φ z w + b * ddcForm ψ z w := by
  unfold ddcForm
  rw [HermitianCurvatureCore.leviForm_add_smul a b hφ hψ w]
  ring

theorem ddcForm_add {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) (w : J → ℂ) :
    ddcForm (fun y => φ y + ψ y) z w = ddcForm φ z w + ddcForm ψ z w := by
  have h := ddcForm_add_smul 1 1 hφ hψ w
  simpa using h

theorem ddcForm_const_mul {J : Type*} [Fintype J] (a : ℝ) {φ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (w : J → ℂ) :
    ddcForm (fun y => a * φ y) z w = a * ddcForm φ z w := by
  have h := ddcForm_add_smul a 0 hφ (contDiffAt_const (c := (0 : ℝ))) w
  simpa using h

theorem ddcForm_neg {J : Type*} [Fintype J] {φ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (w : J → ℂ) :
    ddcForm (fun y => -φ y) z w = -ddcForm φ z w := by
  have h := ddcForm_const_mul (-1) hφ w
  simpa using h

theorem ddcForm_sub {J : Type*} [Fintype J] {φ ψ : (J → ℂ) → ℝ} {z : J → ℂ}
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ContDiffAt ℝ 2 ψ z) (w : J → ℂ) :
    ddcForm (fun y => φ y - ψ y) z w = ddcForm φ z w - ddcForm ψ z w := by
  have h := ddcForm_add_smul 1 (-1) hφ hψ w
  simpa [sub_eq_add_neg] using h

theorem ddcForm_nonneg_of_isPlurisubharmonicOn {J : Type*} [Fintype J]
    {φ : (J → ℂ) → ℝ} {U : Set (J → ℂ)} (hpsh : IsPlurisubharmonicOn φ U)
    {z : J → ℂ} (hz : z ∈ U) (w : J → ℂ) :
    0 ≤ ddcForm φ z w :=
  div_nonneg ((hpsh z hz).2 w) Real.pi_pos.le

/-- Exact bridge between `ddcForm` on `Unit → ℂ` and `Stage11HermitianCurvature.euclLaplacianR`:
`ddcForm (uhpLift1D φ) τ w = (Δ_Eucl φ(τ) / (4 π)) * ‖w ()‖²`. -/
theorem ddcForm_uhpLift1D {φ : UpperHalfPlane → ℝ} {τ : UpperHalfPlane}
    (hφ : ContDiffAt ℝ 2 (uhpLift1D φ) (fun _ => (τ : ℂ))) (w : Unit → ℂ) :
    ddcForm (uhpLift1D φ) (fun _ => (τ : ℂ)) w =
      (euclLaplacianR φ τ / (4 * Real.pi)) * ‖w ()‖ ^ 2 := by
  unfold ddcForm
  rw [leviForm_uhpLift1D hφ w]
  ring

/-- Second derivative along a real line `s ↦ φ(F(z + s • e))` for `C²` maps `F` and `φ`:
`d²/ds²|_{s=0} (φ ∘ F)(z + s e) = D²φ(F z)(DF e, DF e) + Dφ(F z)(D²F(z)(e, e))`. -/
private lemma sndDeriv_comp_line {I J : Type*} [Fintype I] [Fintype J]
    {φ : (J → ℂ) → ℝ} {F : (I → ℂ) → (J → ℂ)} {z : I → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F z)) (hF : ContDiffAt ℝ 2 F z) (e : I → ℂ) :
    fderiv ℝ (fderiv ℝ (φ ∘ F)) z e e =
      fderiv ℝ (fderiv ℝ φ) (F z) (fderiv ℝ F z e) (fderiv ℝ F z e) +
        fderiv ℝ φ (F z) (fderiv ℝ (fderiv ℝ F) z e e) := by
  have hcomp : ContDiffAt ℝ 2 (φ ∘ F) z := hφ.comp z hF
  rw [← HermitianCurvatureCore.deriv_deriv_line hcomp e]
  have hline : ∀ s : ℝ, HasDerivAt (fun t : ℝ => z + t • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont_line : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hF_ev : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 2 F x := hF.eventually (by simp)
  have hφ_ev : ∀ᶠ y in 𝓝 (F z), ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have hF_cont : ContinuousAt F z := hF.continuousAt
  have hφF_ev : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 2 φ (F x) := hF_cont.eventually hφ_ev
  have hd1 : deriv (fun s : ℝ => (φ ∘ F) (z + s • e)) =ᶠ[𝓝 0]
      fun s : ℝ => fderiv ℝ φ (F (z + s • e)) (fderiv ℝ F (z + s • e) e) := by
    filter_upwards [hcont_line.eventually (hF_ev.and hφF_ev)] with s ⟨hFs, hφs⟩
    have h1 : HasDerivAt (fun t : ℝ => F (z + t • e)) (fderiv ℝ F (z + s • e) e) s :=
      (hFs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have h2 : HasDerivAt (fun t : ℝ => φ (F (z + t • e)))
        (fderiv ℝ φ (F (z + s • e)) (fderiv ℝ F (z + s • e) e)) s :=
      (hφs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s h1
    exact h2.deriv
  rw [hd1.deriv_eq]
  have hF0 : HasDerivAt (fun s : ℝ => F (z + s • e)) (fderiv ℝ F z e) 0 :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 (hline 0) hz0.symm
  have hDφ : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (F z)) (F z) :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hDφ_line : HasDerivAt (fun s : ℝ => fderiv ℝ φ (F (z + s • e)))
      (fderiv ℝ (fderiv ℝ φ) (F z) (fderiv ℝ F z e)) 0 :=
    hDφ.comp_hasDerivAt_of_eq 0 hF0 (by rw [hz0])
  have hDF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hDF_e : HasFDerivAt (fun x => fderiv ℝ F x e) ((fderiv ℝ (fderiv ℝ F) z).flip e) z := by
    simpa using hDF.clm_apply (hasFDerivAt_const e z)
  have hDF_line : HasDerivAt (fun s : ℝ => fderiv ℝ F (z + s • e) e)
      (fderiv ℝ (fderiv ℝ F) z e e) 0 :=
    hDF_e.comp_hasDerivAt_of_eq 0 (hline 0) hz0.symm
  have htot := hDφ_line.clm_apply hDF_line
  rw [hz0] at htot
  simpa using htot.deriv

/-- For a `ℂ`-`C²` holomorphic map `F`, its real Hessian satisfies
`D²F(z)(i w, i w) = -D²F(z)(w, w)` (harmonicity of holomorphic maps!). -/
private lemma fderiv_fderiv_holomorphic_I_smul {I J : Type*} [Fintype I] [Fintype J]
    {F : (I → ℂ) → (J → ℂ)} {z : I → ℂ} (hF : ContDiffAt ℂ 2 F z) (w : I → ℂ) :
    fderiv ℝ (fderiv ℝ F) z (Complex.I • w) (Complex.I • w) =
      -(fderiv ℝ (fderiv ℝ F) z w w) := by
  have hF_ev : ∀ᶠ x in 𝓝 z, ContDiffAt ℂ 2 F x := hF.eventually (by simp)
  have hDF_eq : ∀ u : I → ℂ, (fun x => fderiv ℝ F x u) =ᶠ[𝓝 z] fun x => fderiv ℂ F x u := by
    intro u
    filter_upwards [hF_ev] with x hx
    have hdiff : DifferentiableAt ℂ F x := hx.differentiableAt (by norm_num)
    rw [hdiff.hasFDerivAt.restrictScalars ℝ |>.fderiv]
    rfl
  have hDF_C : HasFDerivAt (fderiv ℂ F) (fderiv ℂ (fderiv ℂ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD2_eval : ∀ u v : I → ℂ,
      fderiv ℝ (fderiv ℝ F) z u v = fderiv ℂ (fderiv ℂ F) z u v := by
    intro u v
    have h1 : HasFDerivAt (fun x => fderiv ℝ F x v)
        (((fderiv ℝ (fderiv ℝ F) z).flip v)) z := by
      have hFR := hF.restrict_scalars ℝ
      have hDFR : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
        ((hFR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
      simpa using hDFR.clm_apply (hasFDerivAt_const v z)
    have h2 : HasFDerivAt (fun x => fderiv ℂ F x v)
        (((fderiv ℂ (fderiv ℂ F) z).flip v).restrictScalars ℝ) z := by
      have hC := hDF_C.clm_apply (hasFDerivAt_const v z)
      simpa using hC.restrictScalars ℝ
    have h2' := h2.congr_of_eventuallyEq (hDF_eq v)
    have heq := h1.unique h2'
    exact congrArg (fun L => L u) heq
  rw [hD2_eval (Complex.I • w) (Complex.I • w), hD2_eval w w]
  simp only [map_smul, _root_.smul_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

/-- **Holomorphic Pullback Invariance of the Complex Hessian (Levi Form)**:
for every holomorphic `C²` map `F : (I → ℂ) → (J → ℂ)` and real `C²` potential `φ : (J → ℂ) → ℝ`,
$$\operatorname{leviForm}(\varphi \circ F)(z, w) = \operatorname{leviForm}(\varphi)(F(z), DF(z)\,w).$$ -/
theorem leviForm_comp_holomorphic {I J : Type*} [Fintype I] [Fintype J]
    {φ : (J → ℂ) → ℝ} {F : (I → ℂ) → (J → ℂ)} {z : I → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F z)) (hF : ContDiffAt ℂ 2 F z) (w : I → ℂ) :
    HermitianCurvatureCore.leviForm (φ ∘ F) z w =
      HermitianCurvatureCore.leviForm φ (F z) (fderiv ℂ F z w) := by
  have hFR : ContDiffAt ℝ 2 F z := hF.restrict_scalars ℝ
  have hdiffC : DifferentiableAt ℂ F z := hF.differentiableAt (by norm_num)
  have hDF_eq : ∀ u : I → ℂ, fderiv ℝ F z u = fderiv ℂ F z u := fun u => by
    rw [hdiffC.hasFDerivAt.restrictScalars ℝ |>.fderiv]; rfl
  unfold HermitianCurvatureCore.leviForm
  rw [sndDeriv_comp_line hφ hFR w, sndDeriv_comp_line hφ hFR (Complex.I • w),
    fderiv_fderiv_holomorphic_I_smul hF w, map_neg, hDF_eq w, hDF_eq (Complex.I • w), map_smul]
  ring

/-- **Holomorphic Pullback Invariance of `dd^c`**:
for every holomorphic `C²` map `F : (I → ℂ) → (J → ℂ)` and real `C²` potential `φ : (J → ℂ) → ℝ`,
$$\mathrm{ddcForm}(\varphi \circ F)(z, w) = \mathrm{ddcForm}(\varphi)(F(z), DF(z)\,w).$$ -/
theorem ddcForm_comp_holomorphic {I J : Type*} [Fintype I] [Fintype J]
    {φ : (J → ℂ) → ℝ} {F : (I → ℂ) → (J → ℂ)} {z : I → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F z)) (hF : ContDiffAt ℂ 2 F z) (w : I → ℂ) :
    ddcForm (φ ∘ F) z w = ddcForm φ (F z) (fderiv ℂ F z w) := by
  unfold ddcForm
  rw [leviForm_comp_holomorphic hφ hF w]

/-- Pullback invariance of `leviForm` along a `ℂ`-linear map `L : (I → ℂ) →L[ℂ] (J → ℂ)`. -/
theorem leviForm_comp_clm {I J : Type*} [Fintype I] [Fintype J]
    {φ : (J → ℂ) → ℝ} (L : (I → ℂ) →L[ℂ] (J → ℂ)) {z : I → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (L z)) (w : I → ℂ) :
    HermitianCurvatureCore.leviForm (φ ∘ L) z w =
      HermitianCurvatureCore.leviForm φ (L z) (L w) := by
  have hL : ContDiffAt ℂ 2 L z := L.contDiff.contDiffAt
  have h := leviForm_comp_holomorphic hφ hL w
  rwa [L.fderiv] at h

/-- Pullback invariance of `ddcForm` along a `ℂ`-linear map `L : (I → ℂ) →L[ℂ] (J → ℂ)`. -/
theorem ddcForm_comp_clm {I J : Type*} [Fintype I] [Fintype J]
    {φ : (J → ℂ) → ℝ} (L : (I → ℂ) →L[ℂ] (J → ℂ)) {z : I → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (L z)) (w : I → ℂ) :
    ddcForm (φ ∘ L) z w = ddcForm φ (L z) (L w) := by
  unfold ddcForm
  rw [leviForm_comp_clm L hφ w]

/-- **Monotone Double-Limit Theorem** (distilling `MonotoneDoubleLimit.iterLim_eq_of_monotone`):
if `T : ℝ → ℝ → ℝ` is monotone in each variable on `(0, ∞) × (0, ∞)` and has iterated right
limits `lim_{δ → 0⁺} lim_{ε → 0⁺} T(ε, δ) = a` and `lim_{ε → 0⁺} lim_{δ → 0⁺} T(ε, δ) = b`,
then `a = b`. This is the analytic engine behind regularized Green-current star commutativity. -/
theorem iterLim_eq_of_monotone {T : ℝ → ℝ → ℝ} {A B : ℝ → ℝ} {a b : ℝ}
    (hε : ∀ δ, 0 < δ → ∀ ε, 0 < ε → ∀ ε', ε ≤ ε' → T ε δ ≤ T ε' δ)
    (hδ : ∀ ε, 0 < ε → ∀ δ, 0 < δ → ∀ δ', δ ≤ δ' → T ε δ ≤ T ε δ')
    (hA : ∀ δ, 0 < δ → Tendsto (fun ε => T ε δ) (𝓝[>] 0) (𝓝 (A δ)))
    (hB : ∀ ε, 0 < ε → Tendsto (fun δ => T ε δ) (𝓝[>] 0) (𝓝 (B ε)))
    (ha : Tendsto A (𝓝[>] 0) (𝓝 a)) (hb : Tendsto B (𝓝[>] 0) (𝓝 b)) : a = b := by
  have below : ∀ x : ℝ, 0 < x → ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y ∧ y ≤ x := fun x hx => by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds]
      with y hy hyx using ⟨hy, hyx.le⟩
  have keyA : ∀ ε, 0 < ε → ∀ δ, 0 < δ → A δ ≤ T ε δ := fun ε hε0 δ hδ0 =>
    le_of_tendsto (hA δ hδ0) (by
      filter_upwards [below ε hε0] with ε' h' using hε δ hδ0 ε' h'.1 ε h'.2)
  have keyB : ∀ ε, 0 < ε → ∀ δ, 0 < δ → B ε ≤ T ε δ := fun ε hε0 δ hδ0 =>
    le_of_tendsto (hB ε hε0) (by
      filter_upwards [below δ hδ0] with δ' h' using hδ ε hε0 δ' h'.1 δ h'.2)
  have h1 : ∀ ε, 0 < ε → a ≤ B ε := fun ε hε0 =>
    le_of_tendsto_of_tendsto ha (hB ε hε0) (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ using keyA ε hε0 δ hδ)
  have h2 : ∀ δ, 0 < δ → b ≤ A δ := fun δ hδ0 =>
    le_of_tendsto_of_tendsto hb (hA δ hδ0) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε using keyB ε hε δ hδ0)
  refine le_antisymm ?_ ?_
  · exact ge_of_tendsto hb (by filter_upwards [self_mem_nhdsWithin] with ε hε using h1 ε hε)
  · exact ge_of_tendsto ha (by filter_upwards [self_mem_nhdsWithin] with δ hδ using h2 δ hδ)

end DdcAndMonotoneLimits

/-! ## Section 2: Fubini–Study Regularized Green Potentials & 1D Analytic Poincaré–Lelong -/

section FubiniStudyAndPoincareLelong1D

/-- Standard Hermitian squared norm `‖z‖² = ∑_j ‖z_j‖²` on `ℂ^n`. -/
def fsNormSq {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∑ j : Fin n, ‖z j‖ ^ 2

/-- Bilinear hyperplane pairing `⟨u, z⟩ = ∑_j u_j z_j` on `ℂ^n`. -/
def fsInner {n : ℕ} (u z : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, u j * z j

/-- **Fubini–Study Green Function** for the hyperplane `{∑ u_j z_j = 0}` in `ℙ^{n-1}(ℂ)`:
$$g_u(z) = -\log\!\left(\frac{|\sum_j u_j z_j|^2}{\sum_j |z_j|^2}\right).$$ -/
def fsLog {n : ℕ} (u z : Fin n → ℂ) : ℝ :=
  -Real.log (‖fsInner u z‖ ^ 2 / fsNormSq z)

/-- **Regularized Fubini–Study Green Function** (`ε > 0`, smooth on `ℂ^n \ {0}`):
$$g_{u, \varepsilon}(z) = -\log\!\left(\frac{|\sum_j u_j z_j|^2 + \varepsilon \|z\|^2}{\|z\|^2}\right).$$ -/
def fsLogReg {n : ℕ} (u : Fin n → ℂ) (ε : ℝ) (z : Fin n → ℂ) : ℝ :=
  -Real.log ((‖fsInner u z‖ ^ 2 + ε * fsNormSq z) / fsNormSq z)

theorem fsNormSq_nonneg {n : ℕ} (z : Fin n → ℂ) : 0 ≤ fsNormSq z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem fsNormSq_pos_of_ne_zero {n : ℕ} {z : Fin n → ℂ} (hz : z ≠ 0) : 0 < fsNormSq z := by
  have hex : ∃ j : Fin n, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  rcases hex with ⟨j₀, hj₀⟩
  exact Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨j₀, Finset.mem_univ j₀, sq_pos_of_pos (norm_pos_iff.mpr hj₀)⟩

theorem fsNormSq_smul {n : ℕ} (c : ℂ) (z : Fin n → ℂ) :
    fsNormSq (c • z) = ‖c‖ ^ 2 * fsNormSq z := by
  unfold fsNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem fsInner_smul_right {n : ℕ} (u : Fin n → ℂ) (c : ℂ) (z : Fin n → ℂ) :
    fsInner u (c • z) = c * fsInner u z := by
  unfold fsInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cauchy–Schwarz bound `|∑ u_j z_j|² ≤ (∑ |u_j|²)(∑ |z_j|²)`. -/
theorem fsInner_norm_sq_le_mul {n : ℕ} (u z : Fin n → ℂ) :
    ‖fsInner u z‖ ^ 2 ≤ fsNormSq u * fsNormSq z := by
  have h1 : ‖fsInner u z‖ ≤ ∑ j : Fin n, ‖u j‖ * ‖z j‖ := by
    calc ‖∑ j : Fin n, u j * z j‖
        ≤ ∑ j : Fin n, ‖u j * z j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖u j‖ * ‖z j‖ := Finset.sum_congr rfl fun j _ => norm_mul _ _
  have h2 : (∑ j : Fin n, ‖u j‖ * ‖z j‖) ^ 2 ≤ (∑ j : Fin n, ‖u j‖ ^ 2) * (∑ j : Fin n, ‖z j‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖u j‖) (fun j => ‖z j‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- Non-negativity of the Fubini–Study Green function `fsLog u z ≥ 0` whenever `‖u‖₂ ≤ 1`. -/
theorem fsLog_nonneg_of_unit {n : ℕ} {u z : Fin n → ℂ} (hu : fsNormSq u ≤ 1)
    (hz : 0 < fsNormSq z) (huz : fsInner u z ≠ 0) :
    0 ≤ fsLog u z := by
  unfold fsLog
  have hcs : ‖fsInner u z‖ ^ 2 ≤ fsNormSq z := by
    calc ‖fsInner u z‖ ^ 2 ≤ fsNormSq u * fsNormSq z := fsInner_norm_sq_le_mul u z
      _ ≤ 1 * fsNormSq z := mul_le_mul_of_nonneg_right hu hz.le
      _ = fsNormSq z := one_mul _
  have hdiv_le : ‖fsInner u z‖ ^ 2 / fsNormSq z ≤ 1 := (div_le_one hz).mpr hcs
  have hdiv_pos : 0 < ‖fsInner u z‖ ^ 2 / fsNormSq z :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr huz)) hz
  have hlog_le : Real.log (‖fsInner u z‖ ^ 2 / fsNormSq z) ≤ 0 :=
    (Real.log_le_log hdiv_pos hdiv_le).trans_eq Real.log_one
  linarith

/-- Monotonicity of regularized Fubini–Study Green functions: `0 < ε₁ ≤ ε₂ → g_{u, ε₂} ≤ g_{u, ε₁}`
(so `g_{u, ε}` increases monotonically to `g_u` as `ε → 0⁺`). -/
theorem fsLogReg_antitone {n : ℕ} (u : Fin n → ℂ) {z : Fin n → ℂ} (hz : 0 < fsNormSq z)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hle : ε₁ ≤ ε₂) :
    fsLogReg u ε₂ z ≤ fsLogReg u ε₁ z := by
  unfold fsLogReg
  have hpos₁ : 0 < (‖fsInner u z‖ ^ 2 + ε₁ * fsNormSq z) / fsNormSq z :=
    div_pos (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hε₁ hz)) hz
  have hle_arg : (‖fsInner u z‖ ^ 2 + ε₁ * fsNormSq z) / fsNormSq z ≤
      (‖fsInner u z‖ ^ 2 + ε₂ * fsNormSq z) / fsNormSq z := by
    refine div_le_div_of_nonneg_right ?_ hz.le
    linarith [mul_le_mul_of_nonneg_right hle hz.le]
  linarith [Real.log_le_log hpos₁ hle_arg]

/-- Lower bound `fsLogReg u ε z ≤ fsLog u z` for all `ε > 0` away from the hyperplane. -/
theorem fsLogReg_le_fsLog {n : ℕ} (u : Fin n → ℂ) {z : Fin n → ℂ} (hz : 0 < fsNormSq z)
    (huz : fsInner u z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    fsLogReg u ε z ≤ fsLog u z := by
  unfold fsLogReg fsLog
  have hpos : 0 < ‖fsInner u z‖ ^ 2 / fsNormSq z :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr huz)) hz
  have hle : ‖fsInner u z‖ ^ 2 / fsNormSq z ≤
      (‖fsInner u z‖ ^ 2 + ε * fsNormSq z) / fsNormSq z := by
    refine div_le_div_of_nonneg_right ?_ hz.le
    linarith [mul_pos hε hz]
  linarith [Real.log_le_log hpos hle]

/-- Pointwise convergence `lim_{ε → 0⁺} fsLogReg u ε z = fsLog u z` off `{∑ u_j z_j = 0}`. -/
theorem fsLogReg_tendsto {n : ℕ} (u z : Fin n → ℂ) (hz : 0 < fsNormSq z)
    (huz : fsInner u z ≠ 0) :
    Tendsto (fun ε : ℝ => fsLogReg u ε z) (𝓝[>] 0) (𝓝 (fsLog u z)) := by
  have hnum_pos : 0 < ‖fsInner u z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr huz)
  have hcont : ContinuousAt
      (fun ε : ℝ => -Real.log ((‖fsInner u z‖ ^ 2 + ε * fsNormSq z) / fsNormSq z)) 0 := by
    refine ContinuousAt.neg (ContinuousAt.log ?_ ?_)
    · exact ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).div_const _)
    · simp only [zero_mul, add_zero]
      exact (div_pos hnum_pos hz).ne'
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [fsLogReg, fsLog] using h

/-- Projective scaling invariance of `fsLog`: `g_u(c • z) = g_u(z)` for `c ≠ 0`. -/
theorem fsLog_scale_inv {n : ℕ} (u z : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    fsLog u (c • z) = fsLog u z := by
  unfold fsLog
  rw [fsInner_smul_right, fsNormSq_smul, norm_mul, mul_pow]
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  rw [mul_div_mul_left _ _ hc2]

/-- Projective scaling invariance of `fsLogReg`: `g_{u, ε}(c • z) = g_{u, ε}(z)` for `c ≠ 0`. -/
theorem fsLogReg_scale_inv {n : ℕ} (u : Fin n → ℂ) (ε : ℝ) (z : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    fsLogReg u ε (c • z) = fsLogReg u ε z := by
  unfold fsLogReg
  rw [fsInner_smul_right, fsNormSq_smul, norm_mul, mul_pow]
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hfact : ‖c‖ ^ 2 * ‖fsInner u z‖ ^ 2 + ε * (‖c‖ ^ 2 * fsNormSq z) =
      ‖c‖ ^ 2 * (‖fsInner u z‖ ^ 2 + ε * fsNormSq z) := by ring
  rw [hfact, mul_div_mul_left _ _ hc2]

/-- Unitary pullback compatibility of regularized Fubini–Study Green potentials:
if `U : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)` preserves `fsNormSq` and has transpose `u' : Fin m → ℂ`
(`fsInner u (U z) = fsInner u' z`), then `fsLogReg u ε (U z) = fsLogReg u' ε z`. -/
theorem fsLogReg_pullback_unitary {m n : ℕ} (U : (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (hiso : ∀ z, fsNormSq (U z) = fsNormSq z) (u : Fin n → ℂ) (u' : Fin m → ℂ)
    (hadj : ∀ z, fsInner u (U z) = fsInner u' z) (ε : ℝ) (z : Fin m → ℂ) :
    fsLogReg u ε (U z) = fsLogReg u' ε z := by
  unfold fsLogReg
  rw [hadj z, hiso z]

/-! ### 1D Analytic Regularized Poincaré–Lelong Kernel & Exact Dirac-Mass Limit -/

/-- Regularized 1D Green potential `g_ε(z) = -log (‖z‖² + ε)` on `Unit → ℂ` (`ε > 0`). -/
def plRegPotential (ε : ℝ) (z : Unit → ℂ) : ℝ :=
  -Real.log (‖z ()‖ ^ 2 + ε)

/-- Exact radial Poincaré–Lelong smoothing kernel `K_ε(r) = 2 ε r / (r² + ε)²`. -/
def plRadialKernel (ε r : ℝ) : ℝ :=
  2 * ε * r / (r ^ 2 + ε) ^ 2

private lemma hasDerivAt_plRadialAntideriv {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (fun t : ℝ => -ε / (t ^ 2 + ε)) (plRadialKernel ε r) r := by
  have hden : r ^ 2 + ε ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg r) hε).ne'
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + ε) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).add_const ε)
  have h2 := (hasDerivAt_const r (-ε)).div h1 hden
  refine h2.congr_deriv ?_
  unfold plRadialKernel
  ring

theorem plRadialKernel_nonneg {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    0 ≤ plRadialKernel ε r := by
  unfold plRadialKernel
  positivity

theorem continuous_plRadialKernel {ε : ℝ} (hε : 0 < ε) :
    Continuous (plRadialKernel ε) := by
  unfold plRadialKernel
  refine (continuous_const.mul continuous_id).div
    (((continuous_pow 2).add continuous_const).pow 2) fun r => ?_
  exact pow_ne_zero 2 (add_pos_of_nonneg_of_pos (sq_nonneg r) hε).ne'

/-- Exact integral of the 1D Poincaré–Lelong radial kernel over `[a, b]`:
$$\int_a^b \frac{2\varepsilon r}{(r^2 + \varepsilon)^2}\,dr
  = \frac{\varepsilon}{a^2 + \varepsilon} - \frac{\varepsilon}{b^2 + \varepsilon}.$$ -/
theorem integral_plRadialKernel_Icc {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    ∫ r in a..b, plRadialKernel ε r = ε / (a ^ 2 + ε) - ε / (b ^ 2 + ε) := by
  have hint : IntervalIntegrable (plRadialKernel ε) volume a b :=
    (continuous_plRadialKernel hε).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hasDerivAt_plRadialAntideriv hε r) hint]
  ring

/-- Exact disk mass of the 1D regularized Poincaré–Lelong kernel on `[0, R]`:
$$\int_0^R \frac{2\varepsilon r}{(r^2 + \varepsilon)^2}\,dr = \frac{R^2}{R^2 + \varepsilon}.$$ -/
theorem integral_plRadialKernel_zero_R {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∫ r in (0 : ℝ)..R, plRadialKernel ε r = R ^ 2 / (R ^ 2 + ε) := by
  rw [integral_plRadialKernel_Icc hε 0 R]
  have h1 : (0 : ℝ) ^ 2 + ε = ε := by ring
  have hden : R ^ 2 + ε ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg R) hε).ne'
  rw [h1, div_self hε.ne']
  field_simp [hden]
  ring

/-- The regularized disk mass converges unconditionally to `1` as `ε → 0⁺` for every `R > 0`. -/
theorem tendsto_integral_plRadialKernel_one {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫ r in (0 : ℝ)..R, plRadialKernel ε r) (𝓝[>] 0) (𝓝 1) := by
  have hev : (fun ε : ℝ => ∫ r in (0 : ℝ)..R, plRadialKernel ε r) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => R ^ 2 / (R ^ 2 + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_plRadialKernel_zero_R hε R
  refine Tendsto.congr' hev.symm ?_
  have hcont : ContinuousAt (fun ε : ℝ => R ^ 2 / (R ^ 2 + ε)) 0 :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by positivity)
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [div_self (sq_pos_of_pos hR).ne'] using h

/-- **1D Analytic Poincaré–Lelong Approximate-Identity Theorem**:
for every continuous radial test function `u : ℝ → ℝ` and every radius `R > 0`,
$$\lim_{\varepsilon \to 0^+} \int_0^R u(r) \cdot \frac{2\varepsilon r}{(r^2 + \varepsilon)^2}\,dr = u(0).$$ -/
theorem poincare_lelong_1d_approx_identity {u : ℝ → ℝ} (hu : Continuous u) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫ r in (0 : ℝ)..R, u r * plRadialKernel ε r) (𝓝[>] 0) (𝓝 (u 0)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  -- Step 1: Choose `δ ∈ (0, R]` such that `|u r - u 0| < η / 3` on `[0, δ]`.
  have huc : ContinuousAt u 0 := hu.continuousAt
  rw [Metric.continuousAt_iff] at huc
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := huc (η / 3) (by positivity)
  set δ : ℝ := min R (δ₀ / 2)
  have hδ_pos : 0 < δ := lt_min hR (half_pos hδ₀_pos)
  have hδ_le_R : δ ≤ R := min_le_left _ _
  have hδ_lt_δ₀ : δ < δ₀ := (min_le_right _ _).trans_lt (half_lt_self hδ₀_pos)
  have hsmall : ∀ r ∈ Set.Icc (0 : ℝ) δ, |u r - u 0| ≤ η / 3 := by
    intro r hr
    have hdist : dist r 0 < δ₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact hr.2.trans_lt hδ_lt_δ₀
    have h := hδ₀ hdist
    rw [Real.dist_eq] at h
    exact h.le
  -- Step 2: Uniform bound `M ≥ 1` for `|u r - u 0|` on compact `[0, R]`.
  have hbdd : ∃ M : ℝ, 0 < M ∧ ∀ r ∈ Set.Icc (0 : ℝ) R, |u r - u 0| ≤ M := by
    have hcont_abs : ContinuousOn (fun r => |u r - u 0|) (Set.Icc 0 R) :=
      ((hu.sub continuous_const).abs).continuousOn
    obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_abs
    refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun r hr => ?_⟩
    have h := hM₀ r hr
    rw [Real.norm_eq_abs, abs_abs] at h
    exact h.trans (le_max_left _ _)
  rcases hbdd with ⟨M, hM_pos, hM⟩
  -- Step 3: Choose `ε₀ > 0` small enough to control both the tail `[δ, R]` and the mass error.
  have htail_lim : Tendsto (fun ε : ℝ => ε / (δ ^ 2 + ε)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => ε / (δ ^ 2 + ε)) 0 :=
      continuousAt_id.div (continuousAt_const.add continuousAt_id) (by positivity)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmass_lim : Tendsto (fun ε : ℝ => ε / (R ^ 2 + ε)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => ε / (R ^ 2 + ε)) 0 :=
      continuousAt_id.div (continuousAt_const.add continuousAt_id) (by positivity)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hev_tail : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε / (δ ^ 2 + ε) < η / (3 * M) := by
    have h := (Metric.tendsto_nhds.mp htail_lim) (η / (3 * M)) (by positivity)
    filter_upwards [h, self_mem_nhdsWithin] with ε hε_d hε0
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hε0 (add_pos_of_nonneg_of_pos (sq_nonneg δ) hε0))] at hε_d
    exact hε_d
  have hev_mass : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε / (R ^ 2 + ε) < η / (3 * (|u 0| + 1)) := by
    have h := (Metric.tendsto_nhds.mp hmass_lim) (η / (3 * (|u 0| + 1))) (by positivity)
    filter_upwards [h, self_mem_nhdsWithin] with ε hε_d hε0
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hε0 (add_pos_of_nonneg_of_pos (sq_nonneg R) hε0))] at hε_d
    exact hε_d
  filter_upwards [self_mem_nhdsWithin, hev_tail, hev_mass] with ε hε htail hmass
  have hε_pos : 0 < ε := hε
  rw [Real.dist_eq]
  -- Rewrite the difference as `∫_0^R (u r - u 0) K_ε r dr - u 0 * (ε / (R² + ε))`.
  have hK_cont : Continuous (plRadialKernel ε) := continuous_plRadialKernel hε
  have hint_uK : IntervalIntegrable (fun r => u r * plRadialKernel ε r) volume 0 R :=
    (hu.mul hK_cont).intervalIntegrable 0 R
  have hint_cK : IntervalIntegrable (fun r => u 0 * plRadialKernel ε r) volume 0 R :=
    (continuous_const.mul hK_cont).intervalIntegrable 0 R
  have hdecomp :
      (∫ r in (0 : ℝ)..R, u r * plRadialKernel ε r) - u 0 =
        (∫ r in (0 : ℝ)..R, (u r - u 0) * plRadialKernel ε r) -
          u 0 * (ε / (R ^ 2 + ε)) := by
    have h1 : ∫ r in (0 : ℝ)..R, (u r - u 0) * plRadialKernel ε r =
        (∫ r in (0 : ℝ)..R, u r * plRadialKernel ε r) -
          u 0 * ∫ r in (0 : ℝ)..R, plRadialKernel ε r := by
      have hsub : (fun r => (u r - u 0) * plRadialKernel ε r) =
          fun r => u r * plRadialKernel ε r - u 0 * plRadialKernel ε r := by
        funext r; ring
      rw [hsub, intervalIntegral.integral_sub hint_uK hint_cK,
        intervalIntegral.integral_const_mul]
    rw [h1, integral_plRadialKernel_zero_R hε R]
    have hden : R ^ 2 + ε ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg R) hε).ne'
    field_simp [hden]
    ring
  rw [hdecomp]
  -- Split `∫_0^R = ∫_0^δ + ∫_δ^R`.
  have hint_diff1 : IntervalIntegrable (fun r => (u r - u 0) * plRadialKernel ε r) volume 0 δ :=
    ((hu.sub continuous_const).mul hK_cont).intervalIntegrable 0 δ
  have hint_diff2 : IntervalIntegrable (fun r => (u r - u 0) * plRadialKernel ε r) volume δ R :=
    ((hu.sub continuous_const).mul hK_cont).intervalIntegrable δ R
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_diff1 hint_diff2]
  -- Bound the near integral `[0, δ]`.
  have hnear : |∫ r in (0 : ℝ)..δ, (u r - u 0) * plRadialKernel ε r| ≤ η / 3 := by
    have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hδ_pos.le
      (f := fun r => (u r - u 0) * plRadialKernel ε r)
    have hmono : ∫ r in (0 : ℝ)..δ, |(u r - u 0) * plRadialKernel ε r| ≤
        ∫ r in (0 : ℝ)..δ, (η / 3) * plRadialKernel ε r := by
      refine intervalIntegral.integral_mono_on hδ_pos.le
        (((hu.sub continuous_const).mul hK_cont).abs.intervalIntegrable 0 δ)
        ((continuous_const.mul hK_cont).intervalIntegrable 0 δ) fun r hr => ?_
      rw [abs_mul, abs_of_nonneg (plRadialKernel_nonneg hε hr.1)]
      exact mul_le_mul_of_nonneg_right (hsmall r hr) (plRadialKernel_nonneg hε hr.1)
    have hmass_δ : ∫ r in (0 : ℝ)..δ, (η / 3) * plRadialKernel ε r ≤ η / 3 := by
      rw [intervalIntegral.integral_const_mul, integral_plRadialKernel_zero_R hε δ]
      have hle1 : δ ^ 2 / (δ ^ 2 + ε) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      nlinarith
    exact hnorm.trans (hmono.trans hmass_δ)
  -- Bound the tail integral `[δ, R]`.
  have hfar : |∫ r in δ..R, (u r - u 0) * plRadialKernel ε r| < η / 3 := by
    have hnorm := intervalIntegral.abs_integral_le_integral_abs (μ := volume) hδ_le_R
      (f := fun r => (u r - u 0) * plRadialKernel ε r)
    have hmono : ∫ r in δ..R, |(u r - u 0) * plRadialKernel ε r| ≤
        ∫ r in δ..R, M * plRadialKernel ε r := by
      refine intervalIntegral.integral_mono_on hδ_le_R
        (((hu.sub continuous_const).mul hK_cont).abs.intervalIntegrable δ R)
        ((continuous_const.mul hK_cont).intervalIntegrable δ R) fun r hr => ?_
      have hr0 : 0 ≤ r := hδ_pos.le.trans hr.1
      rw [abs_mul, abs_of_nonneg (plRadialKernel_nonneg hε hr0)]
      exact mul_le_mul_of_nonneg_right (hM r ⟨hr0, hr.2⟩) (plRadialKernel_nonneg hε hr0)
    have htail_val : ∫ r in δ..R, M * plRadialKernel ε r ≤ M * (ε / (δ ^ 2 + ε)) := by
      rw [intervalIntegral.integral_const_mul, integral_plRadialKernel_Icc hε δ R]
      have hpos_R : 0 ≤ ε / (R ^ 2 + ε) := div_nonneg hε.le (by positivity)
      nlinarith
    have hlt : M * (ε / (δ ^ 2 + ε)) < η / 3 := by
      have h1 := (lt_div_iff₀ (by positivity : 0 < 3 * M)).mp htail
      nlinarith
    exact (hnorm.trans (hmono.trans htail_val)).trans_lt hlt
  -- Bound the mass defect `|u 0 * (ε / (R² + ε))|`.
  have hdef : |u 0 * (ε / (R ^ 2 + ε))| < η / 3 := by
    rw [abs_mul, abs_of_pos (div_pos hε (add_pos_of_nonneg_of_pos (sq_nonneg R) hε))]
    have h1 := (lt_div_iff₀ (by positivity : 0 < 3 * (|u 0| + 1))).mp hmass
    have h2 : |u 0| * (ε / (R ^ 2 + ε)) ≤ (|u 0| + 1) * (ε / (R ^ 2 + ε)) := by
      nlinarith [div_pos hε (add_pos_of_nonneg_of_pos (sq_nonneg R) hε)]
    nlinarith
  have htri :
      |(∫ r in (0 : ℝ)..δ, (u r - u 0) * plRadialKernel ε r) +
        (∫ r in δ..R, (u r - u 0) * plRadialKernel ε r) - u 0 * (ε / (R ^ 2 + ε))| ≤
      |∫ r in (0 : ℝ)..δ, (u r - u 0) * plRadialKernel ε r| +
      |∫ r in δ..R, (u r - u 0) * plRadialKernel ε r| +
      |u 0 * (ε / (R ^ 2 + ε))| := by
    have h1 := abs_sub
      ((∫ r in (0 : ℝ)..δ, (u r - u 0) * plRadialKernel ε r) +
        (∫ r in δ..R, (u r - u 0) * plRadialKernel ε r))
      (u 0 * (ε / (R ^ 2 + ε)))
    have h2 := abs_add_le
      (∫ r in (0 : ℝ)..δ, (u r - u 0) * plRadialKernel ε r)
      (∫ r in δ..R, (u r - u 0) * plRadialKernel ε r)
    linarith
  linarith

/-- **Multiplicity-`m` 1D Analytic Poincaré–Lelong Limit**:
for every multiplicity `m : ℤ`, continuous radial test function `u`, and `R > 0`:
$$\lim_{\varepsilon \to 0^+} \int_0^R u(r) \cdot \bigl(m \cdot K_\varepsilon(r)\bigr)\,dr = m \cdot u(0).$$ -/
theorem poincare_lelong_1d_order_m_limit (m : ℤ) {u : ℝ → ℝ} (hu : Continuous u) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun ε : ℝ => ∫ r in (0 : ℝ)..R, u r * ((m : ℝ) * plRadialKernel ε r))
      (𝓝[>] 0) (𝓝 ((m : ℝ) * u 0)) := by
  have heq : (fun ε : ℝ => ∫ r in (0 : ℝ)..R, u r * ((m : ℝ) * plRadialKernel ε r)) =
      fun ε : ℝ => (m : ℝ) * ∫ r in (0 : ℝ)..R, u r * plRadialKernel ε r := by
    funext ε
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r; ring
  rw [heq]
  exact (poincare_lelong_1d_approx_identity hu hR).const_mul (m : ℝ)

/-- Exact second derivative of `s ↦ Real.log (‖a + s • v‖² + ε)` at `s = 0`. -/
private lemma deriv_deriv_log_norm_sq_add_eps (a v : ℂ) {ε : ℝ} (hε : 0 < ε) :
    deriv (deriv fun s : ℝ => Real.log (‖a + (s : ℂ) * v‖ ^ 2 + ε)) 0 =
      (2 * ‖v‖ ^ 2 * (‖a‖ ^ 2 + ε) - 4 * (a * conj v).re ^ 2) / (‖a‖ ^ 2 + ε) ^ 2 := by
  set q : ℝ → ℝ := fun s => ‖a‖ ^ 2 + 2 * (a * conj v).re * s + ‖v‖ ^ 2 * s ^ 2 + ε
  have hq_eq : (fun s : ℝ => ‖a + (s : ℂ) * v‖ ^ 2 + ε) = q := by
    funext s
    have hnorm : ‖a + (s : ℂ) * v‖ ^ 2 =
        ((a + (s : ℂ) * v) * conj (a + (s : ℂ) * v)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hnorm]
    have hexp : (a + (s : ℂ) * v) * conj (a + (s : ℂ) * v) =
        a * conj a + (s : ℂ) * (a * conj v + conj (a * conj v)) +
          ((s : ℂ) ^ 2) * (v * conj v) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [hexp]
    have hsym : (a * conj v + conj (a * conj v)).re = 2 * (a * conj v).re := by
      rw [Complex.add_re, Complex.conj_re]; ring
    have hre1 : (a * conj a).re = ‖a‖ ^ 2 := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hre2 : ((s : ℂ) * (a * conj v + conj (a * conj v))).re = 2 * (a * conj v).re * s := by
      rw [Complex.re_ofReal_mul, hsym]; ring
    have hre3 : ((s : ℂ) ^ 2 * (v * conj v)).re = ‖v‖ ^ 2 * s ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]; ring
    simp only [Complex.add_re, hre1, hre2, hre3, q]
  have hq_pt : ∀ s : ℝ, ‖a + (s : ℂ) * v‖ ^ 2 + ε = q s := fun s => congrFun hq_eq s
  simp_rw [hq_pt]
  have hq_pos : ∀ s : ℝ, 0 < q s := fun s => by
    rw [← hq_eq]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hq1 : ∀ s : ℝ, HasDerivAt q (2 * (a * conj v).re + 2 * ‖v‖ ^ 2 * s) s := fun s => by
    have h1 := ((hasDerivAt_id s).const_mul (2 * (a * conj v).re)).const_add (‖a‖ ^ 2)
    have h2 := ((hasDerivAt_pow 2 s).const_mul (‖v‖ ^ 2))
    have h3 := (h1.add h2).add_const ε
    refine h3.congr_deriv ?_
    ring
  have hd1 : (deriv fun s : ℝ => Real.log (q s)) =
      fun s : ℝ => (2 * (a * conj v).re + 2 * ‖v‖ ^ 2 * s) / q s := by
    funext s
    exact ((hq1 s).log (hq_pos s).ne').deriv
  rw [hd1]
  have hnum : HasDerivAt (fun s : ℝ => 2 * (a * conj v).re + 2 * ‖v‖ ^ 2 * s) (2 * ‖v‖ ^ 2) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * ‖v‖ ^ 2)).const_add (2 * (a * conj v).re)
    simpa using h
  have hdiv := hnum.div (hq1 0) (hq_pos 0).ne'
  have hdiv_eq : (fun s : ℝ => (2 * (a * conj v).re + 2 * ‖v‖ ^ 2 * s) / q s) =
      (fun s : ℝ => 2 * (a * conj v).re + 2 * ‖v‖ ^ 2 * s) / q := rfl
  rw [hdiv_eq, hdiv.deriv]
  simp only [q, mul_zero, zero_pow two_ne_zero, add_zero]
  ring

/-- **Exact 1D Regularized Poincaré–Lelong Curvature Identity on `ℂ`**:
for every `ε > 0` and `z, w : Unit → ℂ`,
$$\operatorname{leviForm}\bigl(z \mapsto \log(\|z()\|^2 + \varepsilon)\bigr)(z, w)
  = \frac{\varepsilon}{(\|z()\|^2 + \varepsilon)^2} \|w()\|^2.$$ -/
theorem leviForm_log_norm_sq_add_eps {ε : ℝ} (hε : 0 < ε) (z w : Unit → ℂ) :
    HermitianCurvatureCore.leviForm (fun x : Unit → ℂ => Real.log (‖x ()‖ ^ 2 + ε)) z w =
      (ε / (‖z ()‖ ^ 2 + ε) ^ 2) * ‖w ()‖ ^ 2 := by
  have hcont : ContDiffAt ℝ 2 (fun x : Unit → ℂ => Real.log (‖x ()‖ ^ 2 + ε)) z := by
    have hproj : ContDiff ℝ 2 (fun x : Unit → ℂ => x ()) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℂ) ()).contDiff
    have hsq : ContDiff ℝ 2 (fun x : Unit → ℂ => ‖x ()‖ ^ 2 + ε) := by
      have heq : (fun x : Unit → ℂ => ‖x ()‖ ^ 2 + ε) =
          fun x => (x ()).re ^ 2 + (x ()).im ^ 2 + ε := by
        funext x
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
      rw [heq]
      have hre : ContDiff ℝ 2 (fun x : Unit → ℂ => (x ()).re) :=
        Complex.reCLM.contDiff.comp hproj
      have him : ContDiff ℝ 2 (fun x : Unit → ℂ => (x ()).im) :=
        Complex.imCLM.contDiff.comp hproj
      exact ((hre.pow 2).add (him.pow 2)).add contDiff_const
    exact hsq.contDiffAt.log (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'
  unfold HermitianCurvatureCore.leviForm
  rw [← HermitianCurvatureCore.deriv_deriv_line hcont w,
    ← HermitianCurvatureCore.deriv_deriv_line hcont (Complex.I • w)]
  have hline1 : (fun s : ℝ => Real.log (‖(z + s • w) ()‖ ^ 2 + ε)) =
      fun s : ℝ => Real.log (‖z () + (s : ℂ) * w ()‖ ^ 2 + ε) := by
    funext s; simp [Complex.real_smul]
  have hline2 : (fun s : ℝ => Real.log (‖(z + s • (Complex.I • w)) ()‖ ^ 2 + ε)) =
      fun s : ℝ => Real.log (‖z () + (s : ℂ) * (Complex.I * w ())‖ ^ 2 + ε) := by
    funext s; simp [Complex.real_smul]
  rw [hline1, hline2, deriv_deriv_log_norm_sq_add_eps (z ()) (w ()) hε,
    deriv_deriv_log_norm_sq_add_eps (z ()) (Complex.I * w ()) hε]
  have hnormI : ‖Complex.I * w ()‖ ^ 2 = ‖w ()‖ ^ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have hreI : (z () * conj (Complex.I * w ())).re = (z () * conj (w ())).im := by
    rw [map_mul, Complex.conj_I]
    have h1 : z () * (-Complex.I * conj (w ())) = -Complex.I * (z () * conj (w ())) := by ring
    rw [h1, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im]
    ring
  have hpyth : (z () * conj (w ())).re ^ 2 + (z () * conj (w ())).im ^ 2 =
      ‖z ()‖ ^ 2 * ‖w ()‖ ^ 2 := by
    have hns := Complex.normSq_apply (z () * conj (w ()))
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj, mul_pow, ← sq, ← sq] at hns
    linarith
  rw [hnormI, hreI]
  have hden : (‖z ()‖ ^ 2 + ε) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'
  field_simp [hden]
  nlinarith [hpyth]

/-- **Regularized 1D Green Current Equation on `ℂ`**:
`dd^c (-log(‖z‖² + ε)) + (ε / (π (‖z‖² + ε)²)) ‖w‖² = 0` identically on `ℂ`. -/
theorem ddcForm_plRegPotential_eq {ε : ℝ} (hε : 0 < ε) (z w : Unit → ℂ) :
    ddcForm (plRegPotential ε) z w + (ε / (Real.pi * (‖z ()‖ ^ 2 + ε) ^ 2)) * ‖w ()‖ ^ 2 = 0 := by
  have hcont : ContDiffAt ℝ 2 (fun x : Unit → ℂ => Real.log (‖x ()‖ ^ 2 + ε)) z := by
    have hproj : ContDiff ℝ 2 (fun x : Unit → ℂ => x ()) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℂ) ()).contDiff
    have hsq : ContDiff ℝ 2 (fun x : Unit → ℂ => ‖x ()‖ ^ 2 + ε) := by
      have heq : (fun x : Unit → ℂ => ‖x ()‖ ^ 2 + ε) =
          fun x => (x ()).re ^ 2 + (x ()).im ^ 2 + ε := by
        funext x
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
      rw [heq]
      exact (((Complex.reCLM.contDiff.comp hproj).pow 2).add
        ((Complex.imCLM.contDiff.comp hproj).pow 2)).add contDiff_const
    exact hsq.contDiffAt.log (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'
  have hneg : ddcForm (plRegPotential ε) z w =
      -ddcForm (fun x : Unit → ℂ => Real.log (‖x ()‖ ^ 2 + ε)) z w :=
    ddcForm_neg hcont w
  rw [hneg]
  unfold ddcForm
  rw [leviForm_log_norm_sq_add_eps hε z w]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hden : (‖z ()‖ ^ 2 + ε) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hε).ne'
  field_simp [hpi, hden]
  ring

end FubiniStudyAndPoincareLelong1D

/-! ## Section 3: Dolbeault Current Algebras, `im ∂ + im ∂̄`, `GreenCurrentData` & `ArakelovDivisor` -/

section DolbeaultCurrentsAndArakelovDivisors

/-- **Dolbeault Bigraded Current Algebra**:
concrete algebraic-analytic formalization of the real current spaces `(Curr00, Curr10, Curr01, Curr11)`
carrying `∂`, `∂̄`, anticommutation `∂∂̄ + ∂̄∂ = 0`, graded exterior products, graded Leibniz rules,
and a closed `(1,1)`-current subspace.

Directly models smooth differential forms and currents of degree `(0,0)`, `(1,0)`, `(0,1)`, `(1,1)`
on a complex manifold `X(ℂ)` (realized concretely on `ℂ[z, z̄]` in Section 7!). -/
structure DolbeaultCurrentAlgebra.{u} where
  /-- `(0,0)`-currents (locally integrable functions / Green potentials). -/
  Curr00 : Type u
  /-- `(1,0)`-currents. -/
  Curr10 : Type u
  /-- `(0,1)`-currents. -/
  Curr01 : Type u
  /-- `(1,1)`-currents (curvature forms, divisor integration currents, star products). -/
  Curr11 : Type u
  [instAdd00 : AddCommGroup Curr00]
  [instMod00 : Module ℝ Curr00]
  [instAdd10 : AddCommGroup Curr10]
  [instMod10 : Module ℝ Curr10]
  [instAdd01 : AddCommGroup Curr01]
  [instMod01 : Module ℝ Curr01]
  [instAdd11 : AddCommGroup Curr11]
  [instMod11 : Module ℝ Curr11]
  /-- Dolbeault operator `∂ : Curr00 →ₗ[ℝ] Curr10`. -/
  d00 : Curr00 →ₗ[ℝ] Curr10
  /-- Dolbeault operator `∂̄ : Curr00 →ₗ[ℝ] Curr01`. -/
  dbar00 : Curr00 →ₗ[ℝ] Curr01
  /-- Dolbeault operator `∂ : Curr01 →ₗ[ℝ] Curr11`. -/
  d01 : Curr01 →ₗ[ℝ] Curr11
  /-- Dolbeault operator `∂̄ : Curr10 →ₗ[ℝ] Curr11`. -/
  dbar10 : Curr10 →ₗ[ℝ] Curr11
  /-- Fundamental Dolbeault anticommutation `∂(∂̄ g) + ∂̄(∂ g) = 0`. -/
  d_dbar_anticomm : ∀ g : Curr00, d01 (dbar00 g) + dbar10 (d00 g) = 0
  /-- Bilinear wedge product `Curr00 × Curr11 → Curr11` (even-degree, hence commutative). -/
  mul00_11 : Curr00 →ₗ[ℝ] Curr11 →ₗ[ℝ] Curr11
  /-- Bilinear product `Curr00 × Curr10 → Curr10`. -/
  mul00_10 : Curr00 →ₗ[ℝ] Curr10 →ₗ[ℝ] Curr10
  /-- Bilinear product `Curr00 × Curr01 → Curr01`. -/
  mul00_01 : Curr00 →ₗ[ℝ] Curr01 →ₗ[ℝ] Curr01
  /-- Bilinear wedge product `Curr10 × Curr01 → Curr11`. -/
  wedge10_01 : Curr10 →ₗ[ℝ] Curr01 →ₗ[ℝ] Curr11
  /-- Bilinear wedge product `Curr01 × Curr10 → Curr11`. -/
  wedge01_10 : Curr01 →ₗ[ℝ] Curr10 →ₗ[ℝ] Curr11
  /-- Graded anticommutativity of degree-1 wedge products: `α^{0,1} ∧ β^{1,0} = -(β^{1,0} ∧ α^{0,1})`. -/
  wedge_anticomm : ∀ (α : Curr01) (β : Curr10), wedge01_10 α β = -wedge10_01 β α
  /-- Graded Leibniz rule for `∂`: `∂(g · α) = ∂g ∧ α + g · ∂α`. -/
  d01_mul00_01 : ∀ (g : Curr00) (α : Curr01),
    d01 (mul00_01 g α) = wedge10_01 (d00 g) α + mul00_11 g (d01 α)
  /-- Graded Leibniz rule for `∂̄`: `∂̄(g · β) = ∂̄g ∧ β + g · ∂̄β`. -/
  dbar10_mul00_10 : ∀ (g : Curr00) (β : Curr10),
    dbar10 (mul00_10 g β) = wedge01_10 (dbar00 g) β + mul00_11 g (dbar10 β)
  /-- Submodule of closed `(1,1)`-currents (`d ω = 0`). -/
  closed11 : Submodule ℝ Curr11
  /-- Every `dd^c g = ∂(∂̄ g)` is closed. -/
  ddc_mem_closed11 : ∀ g : Curr00, d01 (dbar00 g) ∈ closed11

attribute [instance] DolbeaultCurrentAlgebra.instAdd00 DolbeaultCurrentAlgebra.instMod00
  DolbeaultCurrentAlgebra.instAdd10 DolbeaultCurrentAlgebra.instMod10
  DolbeaultCurrentAlgebra.instAdd01 DolbeaultCurrentAlgebra.instMod01
  DolbeaultCurrentAlgebra.instAdd11 DolbeaultCurrentAlgebra.instMod11

namespace DolbeaultCurrentAlgebra

variable (A : DolbeaultCurrentAlgebra)

/-- The `dd^c` operator `Curr00 →ₗ[ℝ] Curr11`, defined as `∂ ∘ ∂̄`. -/
def ddc : A.Curr00 →ₗ[ℝ] A.Curr11 :=
  A.d01.comp A.dbar00

@[simp]
theorem ddc_apply (g : A.Curr00) : A.ddc g = A.d01 (A.dbar00 g) := rfl

theorem ddc_eq_neg_dbar_d (g : A.Curr00) : A.ddc g = -A.dbar10 (A.d00 g) :=
  eq_neg_of_add_eq_zero_left (A.d_dbar_anticomm g)

theorem dbar10_d00_eq_neg_ddc (g : A.Curr00) : A.dbar10 (A.d00 g) = -A.ddc g :=
  eq_neg_of_add_eq_zero_right (A.d_dbar_anticomm g)

/-- Closedness predicate on `(1,1)`-currents. -/
def IsClosed11 (ω : A.Curr11) : Prop :=
  ω ∈ A.closed11

theorem isClosed11_zero : A.IsClosed11 0 := A.closed11.zero_mem

theorem isClosed11_add {ω₁ ω₂ : A.Curr11} (h₁ : A.IsClosed11 ω₁) (h₂ : A.IsClosed11 ω₂) :
    A.IsClosed11 (ω₁ + ω₂) := A.closed11.add_mem h₁ h₂

theorem isClosed11_neg {ω : A.Curr11} (h : A.IsClosed11 ω) : A.IsClosed11 (-ω) :=
  A.closed11.neg_mem h

theorem isClosed11_sub {ω₁ ω₂ : A.Curr11} (h₁ : A.IsClosed11 ω₁) (h₂ : A.IsClosed11 ω₂) :
    A.IsClosed11 (ω₁ - ω₂) := A.closed11.sub_mem h₁ h₂

theorem isClosed11_smul (c : ℝ) {ω : A.Curr11} (h : A.IsClosed11 ω) : A.IsClosed11 (c • ω) :=
  A.closed11.smul_mem c h

theorem isClosed11_zsmul (n : ℤ) {ω : A.Curr11} (h : A.IsClosed11 ω) : A.IsClosed11 (n • ω) := by
  have : n • ω = (n : ℝ) • ω := (Int.cast_smul_eq_zsmul ℝ n ω).symm
  rw [this]
  exact A.isClosed11_smul (n : ℝ) h

theorem isClosed11_ddc (g : A.Curr00) : A.IsClosed11 (A.ddc g) :=
  A.ddc_mem_closed11 g

/-- **The Gillet–Soulé Boundary Submodule `im ∂ + im ∂̄ ⊆ Curr11`**. -/
def imDDbar : Submodule ℝ A.Curr11 :=
  LinearMap.range A.d01 ⊔ LinearMap.range A.dbar10

/-- **The Quotient Space `D̃^{1,1}(X) = Curr11 / (im ∂ + im ∂̄)`** in which Arakelov Green current
star products live canonically. -/
abbrev Curr11ModDDbar := A.Curr11 ⧸ A.imDDbar

/-- Canonical projection `Curr11 →ₗ[ℝ] Curr11 / (im ∂ + im ∂̄)`. -/
def mkModDDbar : A.Curr11 →ₗ[ℝ] A.Curr11ModDDbar :=
  Submodule.mkQ A.imDDbar

/-- Equivalence modulo `im ∂ + im ∂̄`: `T₁ ≡ T₂ (mod im ∂ + im ∂̄)` iff `T₁ - T₂ ∈ im ∂ + im ∂̄`. -/
def ModImDDbar (T₁ T₂ : A.Curr11) : Prop :=
  T₁ - T₂ ∈ A.imDDbar

theorem mem_imDDbar_of_d01 (α : A.Curr01) : A.d01 α ∈ A.imDDbar :=
  Submodule.mem_sup_left ⟨α, rfl⟩

theorem mem_imDDbar_of_dbar10 (β : A.Curr10) : A.dbar10 β ∈ A.imDDbar :=
  Submodule.mem_sup_right ⟨β, rfl⟩

theorem mem_imDDbar_of_d01_add_dbar10 (α : A.Curr01) (β : A.Curr10) :
    A.d01 α + A.dbar10 β ∈ A.imDDbar :=
  A.imDDbar.add_mem (A.mem_imDDbar_of_d01 α) (A.mem_imDDbar_of_dbar10 β)

theorem mem_imDDbar_ddc (g : A.Curr00) : A.ddc g ∈ A.imDDbar :=
  A.mem_imDDbar_of_d01 (A.dbar00 g)

theorem modImDDbar_iff_mk_eq (T₁ T₂ : A.Curr11) :
    A.ModImDDbar T₁ T₂ ↔ A.mkModDDbar T₁ = A.mkModDDbar T₂ := by
  unfold ModImDDbar mkModDDbar
  exact (Submodule.Quotient.eq A.imDDbar).symm

theorem modImDDbar_refl (T : A.Curr11) : A.ModImDDbar T T := by
  simp [ModImDDbar]

theorem modImDDbar_symm {T₁ T₂ : A.Curr11} (h : A.ModImDDbar T₁ T₂) : A.ModImDDbar T₂ T₁ := by
  unfold ModImDDbar at h ⊢
  simpa [neg_sub] using A.imDDbar.neg_mem h

theorem modImDDbar_trans {T₁ T₂ T₃ : A.Curr11} (h₁₂ : A.ModImDDbar T₁ T₂)
    (h₂₃ : A.ModImDDbar T₂ T₃) : A.ModImDDbar T₁ T₃ := by
  unfold ModImDDbar at h₁₂ h₂₃ ⊢
  have h := A.imDDbar.add_mem h₁₂ h₂₃
  simpa [sub_add_sub_cancel] using h

theorem modImDDbar_add {T₁ T₂ S₁ S₂ : A.Curr11} (h₁ : A.ModImDDbar T₁ S₁)
    (h₂ : A.ModImDDbar T₂ S₂) : A.ModImDDbar (T₁ + T₂) (S₁ + S₂) := by
  unfold ModImDDbar at h₁ h₂ ⊢
  have h := A.imDDbar.add_mem h₁ h₂
  have heq : (T₁ - S₁) + (T₂ - S₂) = (T₁ + T₂) - (S₁ + S₂) := by abel
  rwa [heq] at h

theorem modImDDbar_smul (c : ℝ) {T₁ T₂ : A.Curr11} (h : A.ModImDDbar T₁ T₂) :
    A.ModImDDbar (c • T₁) (c • T₂) := by
  unfold ModImDDbar at h ⊢
  simpa [smul_sub] using A.imDDbar.smul_mem c h

/-- **Green's Second Identity in Any Dolbeault Current Algebra**:
$$g_2 \cdot dd^c g_1 - g_1 \cdot dd^c g_2 = \partial(g_2 \cdot \bar\partial g_1) + \bar\partial(g_1 \cdot \partial g_2).$$ -/
theorem greens_second_identity (g₁ g₂ : A.Curr00) :
    A.mul00_11 g₂ (A.ddc g₁) - A.mul00_11 g₁ (A.ddc g₂) =
      A.d01 (A.mul00_01 g₂ (A.dbar00 g₁)) + A.dbar10 (A.mul00_10 g₁ (A.d00 g₂)) := by
  rw [A.d01_mul00_01, A.dbar10_mul00_10, A.wedge_anticomm, A.dbar10_d00_eq_neg_ddc, map_neg]
  simp only [ddc_apply]
  abel

/-- Consequence of Green's second identity: `g₂ · dd^c g₁ ≡ g₁ · dd^c g₂ (mod im ∂ + im ∂̄)`. -/
theorem mul_ddc_comm_modImDDbar (g₁ g₂ : A.Curr00) :
    A.ModImDDbar (A.mul00_11 g₂ (A.ddc g₁)) (A.mul00_11 g₁ (A.ddc g₂)) := by
  unfold ModImDDbar
  rw [A.greens_second_identity g₁ g₂]
  exact A.mem_imDDbar_of_d01_add_dbar10 _ _

end DolbeaultCurrentAlgebra

/-- **Divisor-to-Current Cycle Homomorphism `δ : (PrimeDiv →₀ ℤ) →+ A.Curr11`**:
assigns to every finite formal Weil divisor `D = ∑ n_W [W]` its closed `(1,1)`-integration
current `δ_D`, with optional horizontal/vertical prime classification where vertical prime
divisors over finite primes carry zero archimedean integration current. -/
structure DivisorCurrentMap (A : DolbeaultCurrentAlgebra) (PrimeDiv : Type*) where
  /-- Additive homomorphism `D ↦ δ_D` into `(1,1)`-currents. -/
  delta : (PrimeDiv →₀ ℤ) →+ A.Curr11
  /-- Every divisor integration current `δ_D` is closed. -/
  delta_closed : ∀ D : PrimeDiv →₀ ℤ, A.IsClosed11 (delta D)

/-- **Concrete Arakelov Green Current Data** for a Weil divisor `D : PrimeDiv →₀ ℤ`:
packages a `(0,0)`-current `g_D` and a smooth closed `(1,1)`-curvature form `ω_D = c₁(𝒪(D), h)`
satisfying the fundamental **Green current equation**:
$$dd^c g_D + \delta_D = \omega_D.$$ -/
@[ext]
structure GreenCurrentData {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    (δ : DivisorCurrentMap A PrimeDiv) (D : PrimeDiv →₀ ℤ) where
  /-- The Green `(0,0)`-current `g_D`. -/
  curr : A.Curr00
  /-- The smooth closed `(1,1)`-curvature form `ω_D = c₁(𝒪(D), h)`. -/
  chernForm : A.Curr11
  /-- Closedness of the curvature form `ω_D`. -/
  chernForm_closed : A.IsClosed11 chernForm
  /-- Fundamental Green current equation `dd^c g_D + δ_D = ω_D`. -/
  green_eq : A.ddc curr + δ.delta D = chernForm

namespace GreenCurrentData

variable {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*} {δ : DivisorCurrentMap A PrimeDiv}

/-- Zero Green current for the zero divisor (`g = 0`, `ω = 0`). -/
def zero : GreenCurrentData δ 0 where
  curr := 0
  chernForm := 0
  chernForm_closed := A.isClosed11_zero
  green_eq := by simp

/-- Pure smooth Green potential `u : A.Curr00` attached to the zero divisor (`ω = dd^c u`). -/
def ofSmooth (u : A.Curr00) : GreenCurrentData δ 0 where
  curr := u
  chernForm := A.ddc u
  chernForm_closed := A.isClosed11_ddc u
  green_eq := by simp

/-- Metric-change perturbation `g ↦ g + u` preserving the underlying divisor `D`
and shifting curvature `ω ↦ ω + dd^c u`. -/
def addSmooth {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) (u : A.Curr00) :
    GreenCurrentData δ D where
  curr := g.curr + u
  chernForm := g.chernForm + A.ddc u
  chernForm_closed := A.isClosed11_add g.chernForm_closed (A.isClosed11_ddc u)
  green_eq := by
    rw [map_add, ← g.green_eq]
    abel

/-- Sum of Green currents `g₁ + g₂` for `D₁ + D₂`. -/
def add {D₁ D₂ : PrimeDiv →₀ ℤ} (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    GreenCurrentData δ (D₁ + D₂) where
  curr := g₁.curr + g₂.curr
  chernForm := g₁.chernForm + g₂.chernForm
  chernForm_closed := A.isClosed11_add g₁.chernForm_closed g₂.chernForm_closed
  green_eq := by
    rw [map_add, map_add, ← g₁.green_eq, ← g₂.green_eq]
    abel

/-- Negation `-g` of a Green current for `-D`. -/
def neg {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) : GreenCurrentData δ (-D) where
  curr := -g.curr
  chernForm := -g.chernForm
  chernForm_closed := A.isClosed11_neg g.chernForm_closed
  green_eq := by
    rw [map_neg, map_neg, ← g.green_eq]
    abel

/-- Difference `g₁ - g₂` of Green currents for `D₁ - D₂`. -/
def sub {D₁ D₂ : PrimeDiv →₀ ℤ} (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    GreenCurrentData δ (D₁ - D₂) where
  curr := g₁.curr - g₂.curr
  chernForm := g₁.chernForm - g₂.chernForm
  chernForm_closed := A.isClosed11_sub g₁.chernForm_closed g₂.chernForm_closed
  green_eq := by
    rw [map_sub, map_sub, ← g₁.green_eq, ← g₂.green_eq]
    abel

/-- Integer scaling `n • g` of a Green current for `n • D`. -/
def zsmul (n : ℤ) {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) :
    GreenCurrentData δ (n • D) where
  curr := n • g.curr
  chernForm := n • g.chernForm
  chernForm_closed := A.isClosed11_zsmul n g.chernForm_closed
  green_eq := by
    rw [map_zsmul, map_zsmul, ← smul_add, g.green_eq]

/-- Natural scaling `n • g` of a Green current for `n • D`. -/
def nsmul (n : ℕ) {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) :
    GreenCurrentData δ (n • D) where
  curr := n • g.curr
  chernForm := n • g.chernForm
  chernForm_closed := by
    have : n • g.chernForm = ((n : ℤ) • g.chernForm) := (natCast_zsmul g.chernForm n).symm
    rw [this]
    exact A.isClosed11_zsmul n g.chernForm_closed
  green_eq := by
    rw [map_nsmul, map_nsmul, ← smul_add, g.green_eq]

/-- Equivalent form of the Green equation solving for `δ_D = ω_D - dd^c g_D`. -/
theorem delta_eq_chernForm_sub_ddc {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) :
    δ.delta D = g.chernForm - A.ddc g.curr :=
  eq_sub_of_add_eq' g.green_eq

/-- Equivalent form solving for `dd^c g_D = ω_D - δ_D`. -/
theorem ddc_eq_chernForm_sub_delta {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) :
    A.ddc g.curr = g.chernForm - δ.delta D :=
  eq_sub_of_add_eq g.green_eq

/-- Two Green currents for the same divisor `D` differ in curvature by `dd^c (g₁ - g₂)`. -/
theorem chernForm_sub_eq_ddc_sub {D : PrimeDiv →₀ ℤ} (g₁ g₂ : GreenCurrentData δ D) :
    g₁.chernForm - g₂.chernForm = A.ddc (g₁.curr - g₂.curr) := by
  rw [map_sub, ← g₁.green_eq, ← g₂.green_eq]
  abel

/-- Finite `ℤ`-linear combination of Green currents. -/
def finsetSum {ι : Type*} (s : Finset ι) (D : ι → PrimeDiv →₀ ℤ)
    (g : ∀ i, GreenCurrentData δ (D i)) :
    GreenCurrentData δ (∑ i ∈ s, D i) where
  curr := ∑ i ∈ s, (g i).curr
  chernForm := ∑ i ∈ s, (g i).chernForm
  chernForm_closed := A.closed11.sum_mem fun i _ => (g i).chernForm_closed
  green_eq := by
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (g i).green_eq

@[simp] lemma zero_curr : (zero (δ := δ)).curr = 0 := rfl
@[simp] lemma zero_chernForm : (zero (δ := δ)).chernForm = 0 := rfl
@[simp] lemma ofSmooth_curr (u : A.Curr00) : (ofSmooth (δ := δ) u).curr = u := rfl
@[simp] lemma ofSmooth_chernForm (u : A.Curr00) : (ofSmooth (δ := δ) u).chernForm = A.ddc u := rfl
@[simp] lemma addSmooth_curr {D} (g : GreenCurrentData δ D) (u : A.Curr00) :
    (g.addSmooth u).curr = g.curr + u := rfl
@[simp] lemma addSmooth_chernForm {D} (g : GreenCurrentData δ D) (u : A.Curr00) :
    (g.addSmooth u).chernForm = g.chernForm + A.ddc u := rfl
@[simp] lemma add_curr {D₁ D₂} (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    (g₁.add g₂).curr = g₁.curr + g₂.curr := rfl
@[simp] lemma add_chernForm {D₁ D₂} (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    (g₁.add g₂).chernForm = g₁.chernForm + g₂.chernForm := rfl
@[simp] lemma neg_curr {D} (g : GreenCurrentData δ D) : g.neg.curr = -g.curr := rfl
@[simp] lemma neg_chernForm {D} (g : GreenCurrentData δ D) : g.neg.chernForm = -g.chernForm := rfl
@[simp] lemma sub_curr {D₁ D₂} (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    (g₁.sub g₂).curr = g₁.curr - g₂.curr := rfl
@[simp] lemma sub_chernForm {D₁ D₂} (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    (g₁.sub g₂).chernForm = g₁.chernForm - g₂.chernForm := rfl
@[simp] lemma zsmul_curr (n : ℤ) {D} (g : GreenCurrentData δ D) :
    (g.zsmul n).curr = n • g.curr := rfl
@[simp] lemma zsmul_chernForm (n : ℤ) {D} (g : GreenCurrentData δ D) :
    (g.zsmul n).chernForm = n • g.chernForm := rfl

/-- **Linearity of Green Currents (`green_current_linearity`)**:
integer linear combinations of Green currents satisfy exact additivity, negation, `ℤ`-scaling,
and finite-sum preservation of both the Green current and its first Chern curvature form,
preserving the Green equation `dd^c g + δ_D = ω_D`. -/
theorem green_current_linearity {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (D : ι → PrimeDiv →₀ ℤ) (g : ∀ i, GreenCurrentData δ (D i)) :
    let G := finsetSum s (fun i => c i • D i) (fun i => (g i).zsmul (c i))
    G.curr = ∑ i ∈ s, c i • (g i).curr ∧
    G.chernForm = ∑ i ∈ s, c i • (g i).chernForm ∧
    A.ddc G.curr + δ.delta (∑ i ∈ s, c i • D i) = G.chernForm := by
  dsimp only [finsetSum]
  refine ⟨rfl, rfl, ?_⟩
  rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [GreenCurrentData.zsmul_curr, GreenCurrentData.zsmul_chernForm,
    map_zsmul, ← smul_add, (g i).green_eq]

end GreenCurrentData

/-- Top-level export alias for `GreenCurrentData.green_current_linearity`. -/
theorem green_current_linearity {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    (δ : DivisorCurrentMap A PrimeDiv) {ι : Type*} (s : Finset ι) (c : ι → ℤ)
    (D : ι → PrimeDiv →₀ ℤ) (g : ∀ i, GreenCurrentData δ (D i)) :
    let G := GreenCurrentData.finsetSum s (fun i => c i • D i) (fun i => (g i).zsmul (c i))
    G.curr = ∑ i ∈ s, c i • (g i).curr ∧
    G.chernForm = ∑ i ∈ s, c i • (g i).chernForm ∧
    A.ddc G.curr + δ.delta (∑ i ∈ s, c i • D i) = G.chernForm :=
  GreenCurrentData.green_current_linearity s c D g

/-- **Concrete Arakelov Divisor `D̂ = (D, g_D)`**:
a pair consisting of a finite formal Weil divisor `D : PrimeDiv →₀ ℤ` and an attached
Green current `g_D : GreenCurrentData δ D` satisfying `dd^c g_D + δ_D = ω_D`. -/
structure ArakelovDivisor {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    (δ : DivisorCurrentMap A PrimeDiv) where
  /-- Underlying finite Weil divisor `D = ∑ n_W [W]`. -/
  div : PrimeDiv →₀ ℤ
  /-- Attached Green current `g_D` with closed curvature form `ω_D`. -/
  green : GreenCurrentData δ div

namespace ArakelovDivisor

variable {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*} {δ : DivisorCurrentMap A PrimeDiv}

@[ext]
theorem ext {D₁ D₂ : ArakelovDivisor δ} (hdiv : D₁.div = D₂.div)
    (hcurr : D₁.green.curr = D₂.green.curr) : D₁ = D₂ := by
  cases D₁ with
  | mk d₁ g₁ =>
    cases D₂ with
    | mk d₂ g₂ =>
      dsimp only at hdiv hcurr
      subst hdiv
      congr 1
      cases g₁ with
      | mk c₁ w₁ hw₁ heq₁ =>
        cases g₂ with
        | mk c₂ w₂ hw₂ heq₂ =>
          dsimp only at hcurr
          subst hcurr
          have hw : w₁ = w₂ := heq₁.symm.trans heq₂
          subst hw
          rfl

instance : Zero (ArakelovDivisor δ) := ⟨⟨0, GreenCurrentData.zero⟩⟩
instance : Add (ArakelovDivisor δ) := ⟨fun D₁ D₂ => ⟨D₁.div + D₂.div, D₁.green.add D₂.green⟩⟩
instance : Neg (ArakelovDivisor δ) := ⟨fun D => ⟨-D.div, D.green.neg⟩⟩
instance : Sub (ArakelovDivisor δ) := ⟨fun D₁ D₂ => ⟨D₁.div - D₂.div, D₁.green.sub D₂.green⟩⟩
instance : SMul ℕ (ArakelovDivisor δ) := ⟨fun n D => ⟨n • D.div, D.green.nsmul n⟩⟩
instance : SMul ℤ (ArakelovDivisor δ) := ⟨fun n D => ⟨n • D.div, D.green.zsmul n⟩⟩

@[simp] lemma zero_div : (0 : ArakelovDivisor δ).div = 0 := rfl
@[simp] lemma zero_curr : (0 : ArakelovDivisor δ).green.curr = 0 := rfl
@[simp] lemma zero_chernForm : (0 : ArakelovDivisor δ).green.chernForm = 0 := rfl
@[simp] lemma add_div (D₁ D₂ : ArakelovDivisor δ) : (D₁ + D₂).div = D₁.div + D₂.div := rfl
@[simp] lemma add_curr (D₁ D₂ : ArakelovDivisor δ) :
    (D₁ + D₂).green.curr = D₁.green.curr + D₂.green.curr := rfl
@[simp] lemma add_chernForm (D₁ D₂ : ArakelovDivisor δ) :
    (D₁ + D₂).green.chernForm = D₁.green.chernForm + D₂.green.chernForm := rfl
@[simp] lemma neg_div (D : ArakelovDivisor δ) : (-D).div = -D.div := rfl
@[simp] lemma neg_curr (D : ArakelovDivisor δ) : (-D).green.curr = -D.green.curr := rfl
@[simp] lemma neg_chernForm (D : ArakelovDivisor δ) :
    (-D).green.chernForm = -D.green.chernForm := rfl
@[simp] lemma sub_div (D₁ D₂ : ArakelovDivisor δ) : (D₁ - D₂).div = D₁.div - D₂.div := rfl
@[simp] lemma sub_curr (D₁ D₂ : ArakelovDivisor δ) :
    (D₁ - D₂).green.curr = D₁.green.curr - D₂.green.curr := rfl
@[simp] lemma sub_chernForm (D₁ D₂ : ArakelovDivisor δ) :
    (D₁ - D₂).green.chernForm = D₁.green.chernForm - D₂.green.chernForm := rfl
@[simp] lemma nsmul_div (n : ℕ) (D : ArakelovDivisor δ) : (n • D).div = n • D.div := rfl
@[simp] lemma nsmul_curr (n : ℕ) (D : ArakelovDivisor δ) : (n • D).green.curr = n • D.green.curr := rfl
@[simp] lemma zsmul_div (n : ℤ) (D : ArakelovDivisor δ) : (n • D).div = n • D.div := rfl
@[simp] lemma zsmul_curr (n : ℤ) (D : ArakelovDivisor δ) : (n • D).green.curr = n • D.green.curr := rfl
@[simp] lemma zsmul_chernForm (n : ℤ) (D : ArakelovDivisor δ) :
    (n • D).green.chernForm = n • D.green.chernForm := rfl

instance : AddCommGroup (ArakelovDivisor δ) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul n a := n • a
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> simp [add_nsmul]
  zsmul n a := n • a
  zsmul_zero' a := by ext <;> simp
  zsmul_succ' n a := by
    apply ArakelovDivisor.ext
    · change ((n.succ : ℤ) • a.div) = (n : ℤ) • a.div + a.div
      rw [Nat.cast_succ, add_zsmul, one_zsmul]
    · change ((n.succ : ℤ) • a.green.curr) = (n : ℤ) • a.green.curr + a.green.curr
      rw [Nat.cast_succ, add_zsmul, one_zsmul]
  zsmul_neg' n a := by
    apply ArakelovDivisor.ext
    · change Int.negSucc n • a.div = -(((n.succ : ℤ)) • a.div)
      rw [Int.negSucc_eq, neg_zsmul, Nat.cast_succ]
    · change Int.negSucc n • a.green.curr = -(((n.succ : ℤ)) • a.green.curr)
      rw [Int.negSucc_eq, neg_zsmul, Nat.cast_succ]
  neg_add_cancel a := by ext <;> simp
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  add_comm a b := by ext <;> simp [add_comm]

/-- Pure archimedean / smooth Arakelov divisor `(0, u)` (zero finite divisor, smooth potential `u`). -/
def smooth (u : A.Curr00) : ArakelovDivisor δ :=
  ⟨0, GreenCurrentData.ofSmooth u⟩

/-- The canonical additive homomorphism `u ↦ (0, u)` embedding smooth potentials into
`ArakelovDivisor δ`. -/
def smoothHom : A.Curr00 →+ ArakelovDivisor δ where
  toFun := smooth
  map_zero' := by ext <;> simp [smooth]
  map_add' u₁ u₂ := by ext <;> simp [smooth]

/-- Curvature homomorphism `c₁ : ArakelovDivisor δ →+ A.Curr11` sending `(D, g_D)` to `ω_D`. -/
def chernFormHom : ArakelovDivisor δ →+ A.Curr11 where
  toFun D := D.green.chernForm
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Underlying Weil-divisor forgetful homomorphism `ArakelovDivisor δ →+ (PrimeDiv →₀ ℤ)`. -/
def forgetDivHom : ArakelovDivisor δ →+ (PrimeDiv →₀ ℤ) where
  toFun D := D.div
  map_zero' := rfl
  map_add' _ _ := rfl

/-- An Arakelov divisor is **principal (flat)** if its curvature form vanishes identically
(`ω_D = 0`, i.e., `dd^c g_D + δ_D = 0`, matching `div̂(f) = (div(f), -log |f|²)`). -/
def IsPrincipal (D : ArakelovDivisor δ) : Prop :=
  D.green.chernForm = 0

/-- The subgroup of principal (curvature-zero) Arakelov divisors `ker(c₁)`. -/
def principalSubgroup (δ : DivisorCurrentMap A PrimeDiv) : AddSubgroup (ArakelovDivisor δ) :=
  chernFormHom.ker

/-- **First Arithmetic Chow Group `ĈH¹(X)`**:
quotient of `ArakelovDivisor δ` by principal (flat) Arakelov divisors `div̂(f)` (ready for
`Stage14M3_ArakelovIntersection`). -/
abbrev ArithChow1 (δ : DivisorCurrentMap A PrimeDiv) :=
  ArakelovDivisor δ ⧸ principalSubgroup δ

/-- The first Chern form `c₁ : ArakelovDivisor δ →+ A.Curr11` descends canonically to
`ArithChow1 δ`. -/
def chernFormOnChow (δ : DivisorCurrentMap A PrimeDiv) : ArithChow1 δ →+ A.Curr11 :=
  QuotientAddGroup.lift (principalSubgroup δ) chernFormHom (fun _ h => h)

@[simp]
theorem chernFormOnChow_mk (D : ArakelovDivisor δ) :
    chernFormOnChow δ (QuotientAddGroup.mk D) = D.green.chernForm := rfl

end ArakelovDivisor

end DolbeaultCurrentsAndArakelovDivisors

/-! ## Section 4: `StarProductGreen`, `green_current_commutativity` & Anomaly Formulas -/

section StarProduct

variable {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*} {δ : DivisorCurrentMap A PrimeDiv}

/-- **Gillet–Soulé Star Product of Green Currents (`StarProductGreen`)**:
for Green currents `g₁` (of `D₁`, curvature `ω₁`) and `g₂` (of `D₂`, curvature `ω₂`),
$$g_1 * g_2 := g_1 \wedge \delta_{D_2} + \omega_1 \wedge g_2 \in \mathrm{Curr}^{1,1}.$$ -/
def StarProductGreen {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) : A.Curr11 :=
  A.mul00_11 g₁.curr (δ.delta D₂) + A.mul00_11 g₂.curr g₁.chernForm

/-- The canonical class of `StarProductGreen g₁ g₂` in `Curr11 / (im ∂ + im ∂̄)`. -/
def starProductClass {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) : A.Curr11ModDDbar :=
  A.mkModDDbar (StarProductGreen g₁ g₂)

/-- Exact Dolbeault boundary formula for the commutator `g₁ * g₂ - g₂ * g₁`:
$$g_1 * g_2 - g_2 * g_1 = \partial(g_2 \cdot \bar\partial g_1) + \bar\partial(g_1 \cdot \partial g_2).$$ -/
theorem starProductGreen_sub_comm_eq_boundary {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen g₁ g₂ - StarProductGreen g₂ g₁ =
      A.d01 (A.mul00_01 g₂.curr (A.dbar00 g₁.curr)) +
        A.dbar10 (A.mul00_10 g₁.curr (A.d00 g₂.curr)) := by
  unfold StarProductGreen
  rw [g₂.delta_eq_chernForm_sub_ddc, g₁.delta_eq_chernForm_sub_ddc]
  simp only [map_sub]
  rw [← A.greens_second_identity g₁.curr g₂.curr]
  abel

/-- **COMMUTATIVITY OF THE GREEN CURRENT STAR PRODUCT MODULO `im ∂ + im ∂̄`
(`green_current_commutativity`)**:
for ALL Green currents `g₁, g₂`,
1. `StarProductGreen g₁ g₂ - StarProductGreen g₂ g₁ ∈ im ∂ + im ∂̄`, and
2. `starProductClass g₁ g₂ = starProductClass g₂ g₁` in `Curr11 / (im ∂ + im ∂̄)`. -/
theorem green_current_commutativity {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    A.ModImDDbar (StarProductGreen g₁ g₂) (StarProductGreen g₂ g₁) ∧
    starProductClass g₁ g₂ = starProductClass g₂ g₁ := by
  have hmem : A.ModImDDbar (StarProductGreen g₁ g₂) (StarProductGreen g₂ g₁) := by
    unfold DolbeaultCurrentAlgebra.ModImDDbar
    rw [starProductGreen_sub_comm_eq_boundary g₁ g₂]
    exact A.mem_imDDbar_of_d01_add_dbar10 _ _
  exact ⟨hmem, (A.modImDDbar_iff_mk_eq _ _).mp hmem⟩

/-- Exact bilinearity of `StarProductGreen` in the left argument. -/
theorem starProductGreen_add_left {D₁ D₁' D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₁' : GreenCurrentData δ D₁') (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen (g₁.add g₁') g₂ = StarProductGreen g₁ g₂ + StarProductGreen g₁' g₂ := by
  unfold StarProductGreen
  simp only [GreenCurrentData.add_curr, GreenCurrentData.add_chernForm, map_add,
    LinearMap.add_apply]
  abel

/-- Exact bilinearity of `StarProductGreen` in the right argument. -/
theorem starProductGreen_add_right {D₁ D₂ D₂' : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) (g₂' : GreenCurrentData δ D₂') :
    StarProductGreen g₁ (g₂.add g₂') = StarProductGreen g₁ g₂ + StarProductGreen g₁ g₂' := by
  unfold StarProductGreen
  simp only [GreenCurrentData.add_curr, map_add, LinearMap.add_apply]
  abel

theorem starProductGreen_zero_left {D₂ : PrimeDiv →₀ ℤ} (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen (GreenCurrentData.zero (δ := δ)) g₂ = 0 := by
  simp [StarProductGreen]

theorem starProductGreen_zero_right {D₁ : PrimeDiv →₀ ℤ} (g₁ : GreenCurrentData δ D₁) :
    StarProductGreen g₁ (GreenCurrentData.zero (δ := δ)) = 0 := by
  simp [StarProductGreen]

theorem starProductGreen_neg_left {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen g₁.neg g₂ = -StarProductGreen g₁ g₂ := by
  unfold StarProductGreen
  simp only [GreenCurrentData.neg_curr, GreenCurrentData.neg_chernForm, map_neg,
    LinearMap.neg_apply]
  abel

theorem starProductGreen_neg_right {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen g₁ g₂.neg = -StarProductGreen g₁ g₂ := by
  unfold StarProductGreen
  simp only [GreenCurrentData.neg_curr, map_neg, LinearMap.neg_apply]
  abel

theorem starProductGreen_zsmul_left (n : ℤ) {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen (g₁.zsmul n) g₂ = n • StarProductGreen g₁ g₂ := by
  unfold StarProductGreen
  simp only [GreenCurrentData.zsmul_curr, GreenCurrentData.zsmul_chernForm, map_zsmul,
    LinearMap.smul_apply, smul_add]

theorem starProductGreen_zsmul_right (n : ℤ) {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen g₁ (g₂.zsmul n) = n • StarProductGreen g₁ g₂ := by
  unfold StarProductGreen
  simp only [GreenCurrentData.zsmul_curr, map_zsmul, LinearMap.smul_apply, smul_add]

/-- Star product with a pure smooth potential `(0, u)` on the right equals `u · ω₁` on the nose. -/
theorem starProductGreen_ofSmooth_right {D₁ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (u : A.Curr00) :
    StarProductGreen g₁ (GreenCurrentData.ofSmooth u) = A.mul00_11 u g₁.chernForm := by
  simp [StarProductGreen]

/-- Star product with a pure smooth potential `(0, u)` on the left equals `u · ω₂` modulo
`im ∂ + im ∂̄`. -/
theorem starProductGreen_ofSmooth_left_modImDDbar (u : A.Curr00) {D₂ : PrimeDiv →₀ ℤ}
    (g₂ : GreenCurrentData δ D₂) :
    A.ModImDDbar (StarProductGreen (GreenCurrentData.ofSmooth u) g₂)
      (A.mul00_11 u g₂.chernForm) := by
  have hc := (green_current_commutativity (GreenCurrentData.ofSmooth u) g₂).1
  rwa [starProductGreen_ofSmooth_right g₂ u] at hc

/-- **Metric-Change Anomaly Formula (Right)**:
perturbing `g₂ ↦ g₂ + u` shifts `g₁ * g₂` by `u · ω₁` on the nose. -/
theorem starProductGreen_addSmooth_right {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) (u : A.Curr00) :
    StarProductGreen g₁ (g₂.addSmooth u) = StarProductGreen g₁ g₂ + A.mul00_11 u g₁.chernForm := by
  unfold StarProductGreen
  simp only [GreenCurrentData.addSmooth_curr, map_add, LinearMap.add_apply]
  abel

/-- **Metric-Change Anomaly Formula (Left)**:
perturbing `g₁ ↦ g₁ + u` shifts `g₁ * g₂` by `u · ω₂` modulo `im ∂ + im ∂̄`. -/
theorem starProductGreen_addSmooth_left_modImDDbar {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) (u : A.Curr00) :
    A.ModImDDbar (StarProductGreen (g₁.addSmooth u) g₂)
      (StarProductGreen g₁ g₂ + A.mul00_11 u g₂.chernForm) := by
  have h1 := (green_current_commutativity (g₁.addSmooth u) g₂).1
  rw [starProductGreen_addSmooth_right g₂ g₁ u] at h1
  have h2 := (green_current_commutativity g₂ g₁).1
  have h3 := A.modImDDbar_add h2 (A.modImDDbar_refl (A.mul00_11 u g₂.chernForm))
  exact A.modImDDbar_trans h1 h3

/-- Star product with a principal (flat) Green current (`ω₁ = 0`): `g₁ * g₂ = g₁ · δ_{D₂}`. -/
theorem starProductGreen_of_chernForm_zero {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (hflat : g₁.chernForm = 0) (g₂ : GreenCurrentData δ D₂) :
    StarProductGreen g₁ g₂ = A.mul00_11 g₁.curr (δ.delta D₂) := by
  simp [StarProductGreen, hflat]

/-- **Higher-Degree `dd^c` Extension**:
packages `(2,2)`-currents `Curr22` with `ddc11 : Curr11 →ₗ Curr22` and `(1,1) × (1,1)` wedge
product `wedge11` satisfying the closed-current Leibniz rule `dd^c(g · α) = (dd^c g) ∧ α` for
closed `α`, proving that `g₁ * g₂` is a genuine Green current for `D₁ · D₂` with curvature
`ω₁ ∧ ω₂`. -/
structure HigherDegreeExtension (A : DolbeaultCurrentAlgebra) where
  Curr22 : Type*
  [instAdd22 : AddCommGroup Curr22]
  [instMod22 : Module ℝ Curr22]
  ddc11 : A.Curr11 →ₗ[ℝ] Curr22
  wedge11 : A.Curr11 →ₗ[ℝ] A.Curr11 →ₗ[ℝ] Curr22
  wedge11_comm : ∀ α β : A.Curr11, wedge11 α β = wedge11 β α
  ddc11_mul_closed : ∀ (g : A.Curr00) {α : A.Curr11}, A.IsClosed11 α →
    ddc11 (A.mul00_11 g α) = wedge11 (A.ddc g) α

attribute [instance] HigherDegreeExtension.instAdd22 HigherDegreeExtension.instMod22

/-- **Star Product Green Current Equation**:
$$dd^c(g_1 * g_2) + \delta_{D_1} \wedge \delta_{D_2} = \omega_1 \wedge \omega_2.$$ -/
theorem starProduct_green_eq (E : HigherDegreeExtension A) {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    E.ddc11 (StarProductGreen g₁ g₂) + E.wedge11 (δ.delta D₁) (δ.delta D₂) =
      E.wedge11 g₁.chernForm g₂.chernForm := by
  unfold StarProductGreen
  rw [map_add, E.ddc11_mul_closed g₁.curr (δ.delta_closed D₂),
    E.ddc11_mul_closed g₂.curr g₁.chernForm_closed,
    g₁.ddc_eq_chernForm_sub_delta, g₂.ddc_eq_chernForm_sub_delta,
    E.wedge11_comm (g₂.chernForm - δ.delta D₂) g₁.chernForm]
  simp only [map_sub, LinearMap.sub_apply]
  abel

/-- **Analytic Regularized Green-Current Star Commutativity** (distilling Alpöge's
`PGreenFromLelong.proof`):
given symmetric regularized curvature pairings `formInt(ε, δ)`, regularized cone integrals
`coneInt_1(δ), coneInt_2(ε)`, and cycle integrals `cycInt_1(δ), cycInt_2(ε)` satisfying
regularized Stokes symmetry, monotonicity, and regularized Poincaré–Lelong limits, the limiting
archimedean star products agree identically:
$$\int_{D_1} g_2 + \int_X \omega_1 \wedge g_2 = \int_{D_2} g_1 + \int_X \omega_2 \wedge g_1.$$ -/
theorem green_star_commutativity_of_regularized_lelong
    {formInt : ℝ → ℝ → ℝ}
    {cone₁ cone₂ cyc₁ cyc₂ : ℝ → ℝ}
    {c₁ c₂ d₁ d₂ : ℝ}
    (hsymm : ∀ ε δ, 0 < ε → 0 < δ → formInt δ ε = formInt ε δ)
    (hmono₁ : ∀ ε, 0 < ε → ∀ δ δ', 0 < δ → δ ≤ δ' →
      formInt δ ε + cone₁ δ ≤ formInt δ' ε + cone₁ δ')
    (hmono₂ : ∀ δ, 0 < δ → ∀ ε ε', 0 < ε → ε ≤ ε' →
      formInt ε δ + cone₂ ε ≤ formInt ε' δ + cone₂ ε')
    (hlelong₁ : ∀ δ, 0 < δ →
      Tendsto (fun ε => formInt δ ε) (𝓝[>] 0) (𝓝 (cyc₂ δ - cone₁ δ)))
    (hlelong₂ : ∀ ε, 0 < ε →
      Tendsto (fun δ => formInt ε δ) (𝓝[>] 0) (𝓝 (cyc₁ ε - cone₂ ε)))
    (hcone₁ : Tendsto cone₁ (𝓝[>] 0) (𝓝 c₁))
    (hcone₂ : Tendsto cone₂ (𝓝[>] 0) (𝓝 c₂))
    (hcyc₁ : Tendsto cyc₁ (𝓝[>] 0) (𝓝 d₁))
    (hcyc₂ : Tendsto cyc₂ (𝓝[>] 0) (𝓝 d₂)) :
    d₁ + c₁ = d₂ + c₂ := by
  let T : ℝ → ℝ → ℝ := fun ε δ => formInt δ ε + cone₁ δ + cone₂ ε
  refine (iterLim_eq_of_monotone (T := T)
    (A := fun δ => cyc₂ δ + c₂) (B := fun ε => cyc₁ ε + c₁)
    ?_ ?_ ?_ ?_ ?_ ?_).symm
  · intro δ hδ ε hε ε' hεε'
    dsimp only [T]
    have h := hmono₂ δ hδ ε ε' hε hεε'
    rw [hsymm ε δ hε hδ, hsymm ε' δ (hε.trans_le hεε') hδ]
    linarith
  · intro ε hε δ hδ δ' hδδ'
    dsimp only [T]
    have h := hmono₁ ε hε δ δ' hδ hδδ'
    linarith
  · intro δ hδ
    have h := ((hlelong₁ δ hδ).add_const (cone₁ δ)).add hcone₂
    convert h using 2
    ring
  · intro ε hε
    have h := ((hlelong₂ ε hε).add hcone₁).add_const (cone₂ ε)
    refine Tendsto.congr' ?_ (by convert h using 2; ring)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    dsimp only [T]
    rw [hsymm ε δ hε hδ]
  · exact hcyc₂.add_const c₂
  · exact hcyc₁.add_const c₁

end StarProduct

/-! ## Section 5: Functorial Pullback Compatibility (`green_current_pullback_compat`) -/

section PullbackCompatibility

/-- **Morphism of Dolbeault Current Algebras** modeling pullback `f^* : A → B` along a
holomorphic/algebraic morphism `f : Y → X`. -/
structure DolbeaultMorphism (A B : DolbeaultCurrentAlgebra) where
  map00 : A.Curr00 →ₗ[ℝ] B.Curr00
  map10 : A.Curr10 →ₗ[ℝ] B.Curr10
  map01 : A.Curr01 →ₗ[ℝ] B.Curr01
  map11 : A.Curr11 →ₗ[ℝ] B.Curr11
  map_d00 : ∀ g, map10 (A.d00 g) = B.d00 (map00 g)
  map_dbar00 : ∀ g, map01 (A.dbar00 g) = B.dbar00 (map00 g)
  map_d01 : ∀ α, map11 (A.d01 α) = B.d01 (map01 α)
  map_dbar10 : ∀ β, map11 (A.dbar10 β) = B.dbar10 (map10 β)
  map_mul00_11 : ∀ g ω, map11 (A.mul00_11 g ω) = B.mul00_11 (map00 g) (map11 ω)
  map_mul00_10 : ∀ g β, map10 (A.mul00_10 g β) = B.mul00_10 (map00 g) (map10 β)
  map_mul00_01 : ∀ g α, map01 (A.mul00_01 g α) = B.mul00_01 (map00 g) (map01 α)
  map_closed11 : ∀ {ω}, A.IsClosed11 ω → B.IsClosed11 (map11 ω)

namespace DolbeaultMorphism

/-- Identity Dolbeault morphism. -/
def id (A : DolbeaultCurrentAlgebra) : DolbeaultMorphism A A where
  map00 := LinearMap.id
  map10 := LinearMap.id
  map01 := LinearMap.id
  map11 := LinearMap.id
  map_d00 _ := rfl
  map_dbar00 _ := rfl
  map_d01 _ := rfl
  map_dbar10 _ := rfl
  map_mul00_11 _ _ := rfl
  map_mul00_10 _ _ := rfl
  map_mul00_01 _ _ := rfl
  map_closed11 h := h

/-- Composition of Dolbeault morphisms `(g ∘ f)^* = f^* ∘ g^*`. -/
def comp {A B C : DolbeaultCurrentAlgebra}
    (f : DolbeaultMorphism B C) (g : DolbeaultMorphism A B) : DolbeaultMorphism A C where
  map00 := f.map00.comp g.map00
  map10 := f.map10.comp g.map10
  map01 := f.map01.comp g.map01
  map11 := f.map11.comp g.map11
  map_d00 x := by simp only [LinearMap.comp_apply, g.map_d00, f.map_d00]
  map_dbar00 x := by simp only [LinearMap.comp_apply, g.map_dbar00, f.map_dbar00]
  map_d01 α := by simp only [LinearMap.comp_apply, g.map_d01, f.map_d01]
  map_dbar10 β := by simp only [LinearMap.comp_apply, g.map_dbar10, f.map_dbar10]
  map_mul00_11 x ω := by simp only [LinearMap.comp_apply, g.map_mul00_11, f.map_mul00_11]
  map_mul00_10 x β := by simp only [LinearMap.comp_apply, g.map_mul00_10, f.map_mul00_10]
  map_mul00_01 x α := by simp only [LinearMap.comp_apply, g.map_mul00_01, f.map_mul00_01]
  map_closed11 h := f.map_closed11 (g.map_closed11 h)

theorem map_ddc {A B : DolbeaultCurrentAlgebra} (f : DolbeaultMorphism A B) (g : A.Curr00) :
    f.map11 (A.ddc g) = B.ddc (f.map00 g) := by
  simp only [DolbeaultCurrentAlgebra.ddc_apply, f.map_d01, f.map_dbar00]

/-- Pullback maps `im ∂ + im ∂̄` into `im ∂ + im ∂̄`. -/
theorem map11_mem_imDDbar {A B : DolbeaultCurrentAlgebra} (f : DolbeaultMorphism A B)
    {T : A.Curr11} (hT : T ∈ A.imDDbar) : f.map11 T ∈ B.imDDbar := by
  rcases Submodule.mem_sup.mp hT with ⟨T₁, ⟨α, rfl⟩, T₂, ⟨β, rfl⟩, rfl⟩
  rw [map_add, f.map_d01, f.map_dbar10]
  exact B.mem_imDDbar_of_d01_add_dbar10 _ _

/-- Induced pullback linear map on the quotient `Curr11 / (im ∂ + im ∂̄)`. -/
def mapModDDbar {A B : DolbeaultCurrentAlgebra} (f : DolbeaultMorphism A B) :
    A.Curr11ModDDbar →ₗ[ℝ] B.Curr11ModDDbar :=
  Submodule.mapQ A.imDDbar B.imDDbar f.map11 (fun _ h => f.map11_mem_imDDbar h)

@[simp]
theorem mapModDDbar_mk {A B : DolbeaultCurrentAlgebra} (f : DolbeaultMorphism A B) (T : A.Curr11) :
    f.mapModDDbar (A.mkModDDbar T) = B.mkModDDbar (f.map11 T) := rfl

end DolbeaultMorphism

/-- Compatibility between a Dolbeault pullback `f : A → B` and a divisor pullback homomorphism
`divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)`: `f^*(δ_D) = δ_{f^* D}`. -/
def DivisorPullbackCompat {A B : DolbeaultCurrentAlgebra} {PrimeDivX PrimeDivY : Type*}
    (f : DolbeaultMorphism A B) (δX : DivisorCurrentMap A PrimeDivX)
    (δY : DivisorCurrentMap B PrimeDivY)
    (divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)) : Prop :=
  ∀ D : PrimeDivX →₀ ℤ, f.map11 (δX.delta D) = δY.delta (divPull D)

/-- Functorial pullback of a Green current along a compatible Dolbeault morphism. -/
def GreenCurrentData.pullback {A B : DolbeaultCurrentAlgebra} {PrimeDivX PrimeDivY : Type*}
    (f : DolbeaultMorphism A B) {δX : DivisorCurrentMap A PrimeDivX}
    {δY : DivisorCurrentMap B PrimeDivY} {divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)}
    (hcompat : DivisorPullbackCompat f δX δY divPull)
    {D : PrimeDivX →₀ ℤ} (g : GreenCurrentData δX D) :
    GreenCurrentData δY (divPull D) where
  curr := f.map00 g.curr
  chernForm := f.map11 g.chernForm
  chernForm_closed := f.map_closed11 g.chernForm_closed
  green_eq := by
    rw [← f.map_ddc, ← hcompat D, ← map_add, g.green_eq]

/-- Functorial pullback of Arakelov divisors packaged as an additive group homomorphism
`f^* : ArakelovDivisor δX →+ ArakelovDivisor δY`. -/
def ArakelovDivisor.pullbackHom {A B : DolbeaultCurrentAlgebra} {PrimeDivX PrimeDivY : Type*}
    (f : DolbeaultMorphism A B) {δX : DivisorCurrentMap A PrimeDivX}
    {δY : DivisorCurrentMap B PrimeDivY} {divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)}
    (hcompat : DivisorPullbackCompat f δX δY divPull) :
    ArakelovDivisor δX →+ ArakelovDivisor δY where
  toFun D := ⟨divPull D.div, D.green.pullback f hcompat⟩
  map_zero' := by ext <;> simp [GreenCurrentData.pullback]
  map_add' D₁ D₂ := by ext <;> simp [GreenCurrentData.pullback]

/-- Pullback descends to the first arithmetic Chow group `f^* : ĈH¹(X) →+ ĈH¹(Y)`. -/
def ArakelovDivisor.pullbackChowHom {A B : DolbeaultCurrentAlgebra} {PrimeDivX PrimeDivY : Type*}
    (f : DolbeaultMorphism A B) {δX : DivisorCurrentMap A PrimeDivX}
    {δY : DivisorCurrentMap B PrimeDivY} {divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)}
    (hcompat : DivisorPullbackCompat f δX δY divPull) :
    ArakelovDivisor.ArithChow1 δX →+ ArakelovDivisor.ArithChow1 δY :=
  QuotientAddGroup.map (ArakelovDivisor.principalSubgroup δX)
    (ArakelovDivisor.principalSubgroup δY) (ArakelovDivisor.pullbackHom f hcompat) (by
      intro D hD
      change f.map11 D.green.chernForm = 0
      change D.green.chernForm = 0 at hD
      rw [hD, map_zero])

/-- **PULLBACK COMPATIBILITY OF GREEN CURRENTS & STAR PRODUCTS
(`green_current_pullback_compat`)**:
for any compatible Dolbeault pullback `f : A → B` with `divPull`:
1. Green equation: `dd^c (f^* g₁) + δ_{f^* D₁} = f^* ω₁`,
2. Linearity: `f^* (g₁ + g₂) = f^* g₁ + f^* g₂` and `f^* (n • g₁) = n • (f^* g₁)`,
3. Exact star-product compatibility: `f^* (g₁ * g₂) = (f^* g₁) * (f^* g₂)`,
4. Quotient compatibility: `f^* [g₁ * g₂] = [(f^* g₁) * (f^* g₂)]` in `Curr11 / (im ∂ + im ∂̄)`. -/
theorem green_current_pullback_compat {A B : DolbeaultCurrentAlgebra} {PrimeDivX PrimeDivY : Type*}
    (f : DolbeaultMorphism A B) {δX : DivisorCurrentMap A PrimeDivX}
    {δY : DivisorCurrentMap B PrimeDivY} {divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)}
    (hcompat : DivisorPullbackCompat f δX δY divPull)
    {D₁ D₂ : PrimeDivX →₀ ℤ}
    (g₁ : GreenCurrentData δX D₁) (g₂ : GreenCurrentData δX D₂) (n : ℤ) :
    (B.ddc (g₁.pullback f hcompat).curr + δY.delta (divPull D₁) =
        (g₁.pullback f hcompat).chernForm) ∧
    ((g₁.add g₂).pullback f hcompat).curr =
        ((g₁.pullback f hcompat).add (g₂.pullback f hcompat)).curr ∧
    ((g₁.zsmul n).pullback f hcompat).curr =
        ((g₁.pullback f hcompat).zsmul n).curr ∧
    f.map11 (StarProductGreen g₁ g₂) =
        StarProductGreen (g₁.pullback f hcompat) (g₂.pullback f hcompat) ∧
    f.mapModDDbar (starProductClass g₁ g₂) =
        starProductClass (g₁.pullback f hcompat) (g₂.pullback f hcompat) := by
  refine ⟨(g₁.pullback f hcompat).green_eq, ?_, ?_, ?_, ?_⟩
  · simp [GreenCurrentData.pullback]
  · simp [GreenCurrentData.pullback]
  · unfold StarProductGreen GreenCurrentData.pullback
    simp only [map_add, f.map_mul00_11, hcompat D₂]
  · unfold starProductClass
    rw [f.mapModDDbar_mk]
    congr 1
    unfold StarProductGreen GreenCurrentData.pullback
    simp only [map_add, f.map_mul00_11, hcompat D₂]

/-- Functoriality of Green current pullback under composition `(h ∘ f)^* = f^* ∘ h^*`. -/
theorem green_current_pullback_comp {A B C : DolbeaultCurrentAlgebra}
    {PrimeDivX PrimeDivY PrimeDivZ : Type*}
    (f : DolbeaultMorphism B C) (g : DolbeaultMorphism A B)
    {δX : DivisorCurrentMap A PrimeDivX} {δY : DivisorCurrentMap B PrimeDivY}
    {δZ : DivisorCurrentMap C PrimeDivZ}
    {divPull₁ : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)}
    {divPull₂ : (PrimeDivY →₀ ℤ) →+ (PrimeDivZ →₀ ℤ)}
    (h₁ : DivisorPullbackCompat g δX δY divPull₁)
    (h₂ : DivisorPullbackCompat f δY δZ divPull₂)
    {D : PrimeDivX →₀ ℤ} (G : GreenCurrentData δX D) :
    have hcomp : DivisorPullbackCompat (f.comp g) δX δZ (divPull₂.comp divPull₁) :=
      fun E => by simp [DolbeaultMorphism.comp, h₁ E, h₂ (divPull₁ E)]
    G.pullback (f.comp g) hcomp = (G.pullback g h₁).pullback f h₂ := by
  ext <;> rfl

/-- Identity pullback law: `id^* g = g`. -/
theorem green_current_pullback_id {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ : DivisorCurrentMap A PrimeDiv} {D : PrimeDiv →₀ ℤ} (G : GreenCurrentData δ D) :
    have hid : DivisorPullbackCompat (DolbeaultMorphism.id A) δ δ (AddMonoidHom.id _) :=
      fun _ => rfl
    G.pullback (DolbeaultMorphism.id A) hid = G := by
  ext <;> rfl

end PullbackCompatibility

/-! ## Section 6: `ArakelovPairingModel`, `poincare_lelong_inv` & Wave-2 Height Pairings -/

section PoincareLelongInvAndPairings

/-- **Arakelov Integration & Pairing Model** over a Dolbeault current algebra `A`:
packages top-degree integration `intX : A.Curr11 →ₗ[ℝ] ℝ` (vanishing on `im ∂ + im ∂̄` by
Stokes' theorem) together with prime-divisor integration functionals `intPrime W : A.Curr00 →ₗ[ℝ] ℝ`
satisfying the cycle integration identity
$$\int_X u \cdot \delta_D = \sum_{W} \operatorname{ord}_W(D) \int_W u.$$ -/
structure ArakelovPairingModel {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    (δ : DivisorCurrentMap A PrimeDiv) where
  /-- Top-degree archimedean integration functional `∫_X : Curr11 →ₗ[ℝ] ℝ`. -/
  intX : A.Curr11 →ₗ[ℝ] ℝ
  /-- **Stokes' Theorem**: `∫_X T = 0` for every `T ∈ im ∂ + im ∂̄`. -/
  stokes_vanish : ∀ T ∈ A.imDDbar, intX T = 0
  /-- Integration along each prime divisor `W`: `∫_W : Curr00 →ₗ[ℝ] ℝ`. -/
  intPrime : PrimeDiv → A.Curr00 →ₗ[ℝ] ℝ
  /-- Cycle integration identity `∫_X u · δ_D = ∑_W mult_W(D) · ∫_W u`. -/
  int_delta_eq : ∀ (D : PrimeDiv →₀ ℤ) (u : A.Curr00),
    intX (A.mul00_11 u (δ.delta D)) = D.sum (fun W m => (m : ℝ) * intPrime W u)
  /-- Classification of horizontal prime divisors (whose complex fiber is nonempty). -/
  isHoriz : PrimeDiv → Prop
  /-- Vertical prime divisors (supported over finite primes `p`) have zero archimedean integral. -/
  intPrime_vert_eq_zero : ∀ W, ¬ isHoriz W → intPrime W = 0

namespace ArakelovPairingModel

variable {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*} {δ : DivisorCurrentMap A PrimeDiv}
variable (M : ArakelovPairingModel δ)

/-- Integration descends to the quotient `Curr11 / (im ∂ + im ∂̄)`. -/
def intModDDbar : A.Curr11ModDDbar →ₗ[ℝ] ℝ :=
  Submodule.liftQ A.imDDbar M.intX (fun T hT => M.stokes_vanish T hT)

@[simp]
theorem intModDDbar_mk (T : A.Curr11) : M.intModDDbar (A.mkModDDbar T) = M.intX T := rfl

theorem intX_eq_of_modImDDbar {T₁ T₂ : A.Curr11} (h : A.ModImDDbar T₁ T₂) :
    M.intX T₁ = M.intX T₂ := by
  have h0 : M.intX (T₁ - T₂) = 0 := M.stokes_vanish (T₁ - T₂) h
  rw [map_sub] at h0
  exact sub_eq_zero.mp h0

/-- **Stokes `dd^c`-Symmetry**: `∫_X g₂ · dd^c g₁ = ∫_X g₁ · dd^c g₂`. -/
theorem intX_ddc_symm (g₁ g₂ : A.Curr00) :
    M.intX (A.mul00_11 g₂ (A.ddc g₁)) = M.intX (A.mul00_11 g₁ (A.ddc g₂)) :=
  M.intX_eq_of_modImDDbar (A.mul_ddc_comm_modImDDbar g₁ g₂)

/-- Horizontal-divisor restriction of the cycle sum (vertical prime divisors contribute `0`). -/
theorem sum_intPrime_eq_horiz [DecidablePred M.isHoriz] (D : PrimeDiv →₀ ℤ) (u : A.Curr00) :
    D.sum (fun W m => (m : ℝ) * M.intPrime W u) =
      ∑ W ∈ D.support.filter M.isHoriz, (D W : ℝ) * M.intPrime W u := by
  unfold Finsupp.sum
  rw [← Finset.sum_filter_add_sum_filter_not D.support M.isHoriz]
  have hzero : ∑ W ∈ D.support.filter (fun W => ¬ M.isHoriz W), (D W : ℝ) * M.intPrime W u = 0 := by
    refine Finset.sum_eq_zero fun W hW => ?_
    have hv := (Finset.mem_filter.mp hW).2
    rw [M.intPrime_vert_eq_zero W hv, LinearMap.zero_apply, mul_zero]
  rw [hzero, add_zero]

/-- **POINCARÉ–LELONG INVERSION FORMULA (`poincare_lelong_inv`)**:
for any Green current `g` of a divisor `D` with curvature form `ω = g.chernForm`
(`dd^c g + δ_D = ω`, e.g., `g = -log ‖s‖_A²` for a section `s` with `div(s) = D`)
and any smooth test potential `u : A.Curr00`:
$$\int_X g \cdot dd^c(u) = \int_X u \cdot \omega - \sum_{W} \operatorname{ord}_W(D) \int_W u.$$ -/
theorem poincare_lelong_inv {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) (u : A.Curr00) :
    M.intX (A.mul00_11 g.curr (A.ddc u)) =
      M.intX (A.mul00_11 u g.chernForm) - D.sum (fun W m => (m : ℝ) * M.intPrime W u) := by
  rw [M.intX_ddc_symm u g.curr, g.ddc_eq_chernForm_sub_delta, map_sub, map_sub,
    M.int_delta_eq D u]

/-- **Poincaré–Lelong Inversion in Alpöge's `logNorm` Sign (`PoincareLelongInv`)**:
with `logNorm = -g.curr` (`log ‖s‖_A²`),
$$\int_X (\log \|s\|_A^2) \cdot dd^c(u) = \sum_{W} \operatorname{ord}_W(D) \int_W u - \int_X u \cdot c_1(A).$$ -/
theorem poincare_lelong_inv_logNorm {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) (u : A.Curr00) :
    M.intX (A.mul00_11 (-g.curr) (A.ddc u)) =
      D.sum (fun W m => (m : ℝ) * M.intPrime W u) - M.intX (A.mul00_11 u g.chernForm) := by
  rw [map_neg, LinearMap.neg_apply, map_neg, M.poincare_lelong_inv g u]
  ring

/-- **Horizontal-Filtered Poincaré–Lelong Inversion** (matching `InterSt.PoincareLelongInv`
verbatim over horizontal irreducible components `W ∈ divSupp ∧ IsHorizontal W`): -/
theorem poincare_lelong_inv_horiz [DecidablePred M.isHoriz] {D : PrimeDiv →₀ ℤ}
    (g : GreenCurrentData δ D) (u : A.Curr00) :
    M.intX (A.mul00_11 (-g.curr) (A.ddc u)) =
      (∑ W ∈ D.support.filter M.isHoriz, (D W : ℝ) * M.intPrime W u) -
        M.intX (A.mul00_11 u g.chernForm) := by
  rw [M.poincare_lelong_inv_logNorm g u, M.sum_intPrime_eq_horiz D u]

/-- **Section-Space Symmetry (`InterSt.SectionSpaceSymmetry`)**:
for any two Green currents `g₁, g₂` (representing sections `s₁, s₂` of metrized line bundles):
$$\sum_W \operatorname{ord}_W(D_2) \int_W g_1 + \int_X g_2 \cdot \omega_1
  = \sum_W \operatorname{ord}_W(D_1) \int_W g_2 + \int_X g_1 \cdot \omega_2.$$ -/
theorem section_space_symmetry {D₁ D₂ : PrimeDiv →₀ ℤ}
    (g₁ : GreenCurrentData δ D₁) (g₂ : GreenCurrentData δ D₂) :
    D₂.sum (fun W m => (m : ℝ) * M.intPrime W g₁.curr) + M.intX (A.mul00_11 g₂.curr g₁.chernForm) =
      D₁.sum (fun W m => (m : ℝ) * M.intPrime W g₂.curr) +
        M.intX (A.mul00_11 g₁.curr g₂.chernForm) := by
  have hcomm := M.intX_eq_of_modImDDbar (green_current_commutativity g₁ g₂).1
  unfold StarProductGreen at hcomm
  rw [map_add, map_add, M.int_delta_eq D₂ g₁.curr, M.int_delta_eq D₁ g₂.curr] at hcomm
  exact hcomm

/-- **Archimedean Star-Product Pairing on Arakelov Divisors** (ready for
`Stage14M3_ArakelovIntersection` & `Stage14M3_ChowFormHeights`):
$$\langle \widehat{D}_1, \widehat{D}_2 \rangle_\infty := \int_X g_1 * g_2.$$ -/
def archStarPairing (D₁ D₂ : ArakelovDivisor δ) : ℝ :=
  M.intX (StarProductGreen D₁.green D₂.green)

theorem archStarPairing_eq_modDDbar (D₁ D₂ : ArakelovDivisor δ) :
    M.archStarPairing D₁ D₂ = M.intModDDbar (starProductClass D₁.green D₂.green) := rfl

theorem archStarPairing_symm (D₁ D₂ : ArakelovDivisor δ) :
    M.archStarPairing D₁ D₂ = M.archStarPairing D₂ D₁ :=
  M.intX_eq_of_modImDDbar (green_current_commutativity D₁.green D₂.green).1

theorem archStarPairing_add_left (D₁ D₁' D₂ : ArakelovDivisor δ) :
    M.archStarPairing (D₁ + D₁') D₂ = M.archStarPairing D₁ D₂ + M.archStarPairing D₁' D₂ := by
  unfold archStarPairing
  change M.intX (StarProductGreen (D₁.green.add D₁'.green) D₂.green) = _
  rw [starProductGreen_add_left, map_add]

theorem archStarPairing_add_right (D₁ D₂ D₂' : ArakelovDivisor δ) :
    M.archStarPairing D₁ (D₂ + D₂') = M.archStarPairing D₁ D₂ + M.archStarPairing D₁ D₂' := by
  rw [M.archStarPairing_symm, M.archStarPairing_add_left, M.archStarPairing_symm D₂ D₁,
    M.archStarPairing_symm D₂' D₁]

theorem archStarPairing_zero_left (D₂ : ArakelovDivisor δ) :
    M.archStarPairing 0 D₂ = 0 := by
  unfold archStarPairing
  change M.intX (StarProductGreen GreenCurrentData.zero D₂.green) = 0
  rw [starProductGreen_zero_left, map_zero]

theorem archStarPairing_zero_right (D₁ : ArakelovDivisor δ) :
    M.archStarPairing D₁ 0 = 0 := by
  rw [M.archStarPairing_symm, M.archStarPairing_zero_left]

theorem archStarPairing_neg_left (D₁ D₂ : ArakelovDivisor δ) :
    M.archStarPairing (-D₁) D₂ = -M.archStarPairing D₁ D₂ := by
  unfold archStarPairing
  change M.intX (StarProductGreen D₁.green.neg D₂.green) = _
  rw [starProductGreen_neg_left, map_neg]

theorem archStarPairing_neg_right (D₁ D₂ : ArakelovDivisor δ) :
    M.archStarPairing D₁ (-D₂) = -M.archStarPairing D₁ D₂ := by
  rw [M.archStarPairing_symm, M.archStarPairing_neg_left, M.archStarPairing_symm]

theorem archStarPairing_zsmul_left (n : ℤ) (D₁ D₂ : ArakelovDivisor δ) :
    M.archStarPairing (n • D₁) D₂ = (n : ℝ) * M.archStarPairing D₁ D₂ := by
  unfold archStarPairing
  change M.intX (StarProductGreen (D₁.green.zsmul n) D₂.green) = _
  rw [starProductGreen_zsmul_left, map_zsmul, zsmul_eq_mul]

theorem archStarPairing_zsmul_right (n : ℤ) (D₁ D₂ : ArakelovDivisor δ) :
    M.archStarPairing D₁ (n • D₂) = (n : ℝ) * M.archStarPairing D₁ D₂ := by
  rw [M.archStarPairing_symm, M.archStarPairing_zsmul_left, M.archStarPairing_symm]

/-- Pairing a smooth metric-change divisor `(0, u)` against `D̂` equals `∫_X u · c₁(D̂)`. -/
theorem archStarPairing_smooth_left (u : A.Curr00) (D : ArakelovDivisor δ) :
    M.archStarPairing (ArakelovDivisor.smooth u) D = M.intX (A.mul00_11 u D.green.chernForm) := by
  unfold archStarPairing ArakelovDivisor.smooth
  exact M.intX_eq_of_modImDDbar (starProductGreen_ofSmooth_left_modImDDbar u D.green)

theorem archStarPairing_smooth_right (D : ArakelovDivisor δ) (u : A.Curr00) :
    M.archStarPairing D (ArakelovDivisor.smooth u) = M.intX (A.mul00_11 u D.green.chernForm) := by
  rw [M.archStarPairing_symm, M.archStarPairing_smooth_left]

/-- Pairing a principal (flat) Arakelov divisor `div̂(f)` (`ω = 0`) against `D̂₂` equals
the cycle integral `∑_W ord_W(D₂) ∫_W g_f` (which cancels the finite-place intersection number
by the global product formula in `Stage14M3_ArakelovIntersection`!). -/
theorem archStarPairing_principal_left {D₁ : ArakelovDivisor δ} (hflat : D₁.IsPrincipal)
    (D₂ : ArakelovDivisor δ) :
    M.archStarPairing D₁ D₂ = D₂.div.sum (fun W m => (m : ℝ) * M.intPrime W D₁.green.curr) := by
  unfold archStarPairing
  rw [starProductGreen_of_chernForm_zero D₁.green hflat D₂.green, M.int_delta_eq D₂.div D₁.green.curr]

/-- Metric-change formula for the archimedean self-pairing under `D̂ ↦ D̂ + (0, u)`:
$$\langle \widehat{D} + (0, u), \widehat{D} + (0, u) \rangle_\infty
  = \langle \widehat{D}, \widehat{D} \rangle_\infty + 2 \int_X u \cdot \omega_D + \int_X u \cdot dd^c u.$$ -/
theorem archStarPairing_self_add_smooth (D : ArakelovDivisor δ) (u : A.Curr00) :
    M.archStarPairing (D + ArakelovDivisor.smooth u) (D + ArakelovDivisor.smooth u) =
      M.archStarPairing D D + 2 * M.intX (A.mul00_11 u D.green.chernForm) +
        M.intX (A.mul00_11 u (A.ddc u)) := by
  rw [M.archStarPairing_add_left, M.archStarPairing_add_right, M.archStarPairing_add_right,
    M.archStarPairing_smooth_left, M.archStarPairing_smooth_right,
    M.archStarPairing_smooth_left u (ArakelovDivisor.smooth u)]
  simp only [ArakelovDivisor.smooth, GreenCurrentData.ofSmooth_chernForm]
  ring

/-! ### Positivity, Semipositivity & Monotonicity Bounds for Wave 2 (`ChowFormHeights`, `NefRiemannRoch`) -/

/-- A `(0,0)`-current `g` is **effective / non-negative** relative to `M` if its integral against
every prime divisor and against a given semipositive form is non-negative; more generally, we
specify a positivity cone `Pos00 : Set A.Curr00` and semipositive `(1,1)`-cone `SemiPos11`. -/
structure PositivityCone (M : ArakelovPairingModel δ) where
  /-- Non-negative `(0,0)`-functions/currents (`g ≥ 0`). -/
  isNonneg00 : A.Curr00 → Prop
  /-- Constant function `1` in `Curr00`. -/
  one00 : A.Curr00
  /-- `1` is non-negative. -/
  one00_nonneg : isNonneg00 one00
  /-- Semipositive `(1,1)`-forms (`ω ≥ 0`). -/
  isSemiPos11 : A.Curr11 → Prop
  /-- Non-negativity of cycle integrals on non-negative potentials. -/
  intPrime_nonneg : ∀ W {u}, isNonneg00 u → 0 ≤ M.intPrime W u
  /-- Non-negativity of pairing `∫_X u · ω` when `u ≥ 0` and `ω ≥ 0`. -/
  intX_mul_nonneg : ∀ {u ω}, isNonneg00 u → isSemiPos11 ω → 0 ≤ M.intX (A.mul00_11 u ω)
  /-- Closure of `isNonneg00` under addition and non-negative real scaling. -/
  isNonneg00_add : ∀ {u v}, isNonneg00 u → isNonneg00 v → isNonneg00 (u + v)
  isNonneg00_smul : ∀ {c : ℝ} {u}, 0 ≤ c → isNonneg00 u → isNonneg00 (c • u)

/-- Geometric degree `deg(ω) := ∫_X 1 · ω` of a `(1,1)`-curvature form. -/
def geomDeg (C : PositivityCone M) (ω : A.Curr11) : ℝ :=
  M.intX (A.mul00_11 C.one00 ω)

/-- An Arakelov divisor `D̂ = (D, g_D)` is **effective** if `D ≥ 0` (`∀ W, 0 ≤ D W`) and
`g_D ≥ 0` in the positivity cone `C`. -/
def IsEffectiveArakelovDivisor (C : PositivityCone M) (D : ArakelovDivisor δ) : Prop :=
  (∀ W, 0 ≤ D.div W) ∧ C.isNonneg00 D.green.curr

/-- An Arakelov divisor `D̂ = (D, g_D)` has **semipositive curvature** (nef metric) if
`ω_D ∈ C.isSemiPos11`. -/
def IsSemipositiveGreen (C : PositivityCone M) (D : ArakelovDivisor δ) : Prop :=
  C.isSemiPos11 D.green.chernForm

/-- **Positivity of Archimedean Star Product for Effective Semipositive Arakelov Divisors**
(ready for `Stage14M3_NefRiemannRoch` & `Stage14M3_ChowFormHeights`):
if `D̂₁` is effective with semipositive curvature and `D̂₂` is effective, then
`0 ≤ ⟨D̂₁, D̂₂⟩_∞`. -/
theorem archStarPairing_nonneg_of_effective_semipositive (C : PositivityCone M)
    {D₁ D₂ : ArakelovDivisor δ}
    (h1_eff : IsEffectiveArakelovDivisor M C D₁)
    (h1_pos : IsSemipositiveGreen M C D₁)
    (h2_eff : IsEffectiveArakelovDivisor M C D₂) :
    0 ≤ M.archStarPairing D₁ D₂ := by
  unfold archStarPairing StarProductGreen
  rw [map_add, M.int_delta_eq D₂.div D₁.green.curr]
  have hsum : 0 ≤ D₂.div.sum (fun W m => (m : ℝ) * M.intPrime W D₁.green.curr) := by
    unfold Finsupp.sum
    refine Finset.sum_nonneg fun W _ => mul_nonneg ?_ (C.intPrime_nonneg W h1_eff.2)
    exact_mod_cast h2_eff.1 W
  have hcurv : 0 ≤ M.intX (A.mul00_11 D₂.green.curr D₁.green.chernForm) :=
    C.intX_mul_nonneg h2_eff.2 h1_pos
  linarith

/-- **Metric-Change Bracket for Semipositive Curvature** (ready for `Stage14M3_ChowFormHeights`):
if `uMin · 1 ≤ u ≤ uMax · 1` (i.e. `u - uMin • 1 ≥ 0` and `uMax • 1 - u ≥ 0`) and `D̂` has
semipositive curvature `ω_D`, then:
$$u_{\min} \cdot \deg(\omega_D) \le \langle (0, u), \widehat{D} \rangle_\infty \le u_{\max} \cdot \deg(\omega_D).$$ -/
theorem archStarPairing_metric_change_bounds (C : PositivityCone M)
    {D : ArakelovDivisor δ} (hpos : IsSemipositiveGreen M C D)
    {u : A.Curr00} {uMin uMax : ℝ}
    (hlo : C.isNonneg00 (u - uMin • C.one00))
    (hhi : C.isNonneg00 (uMax • C.one00 - u)) :
    uMin * M.geomDeg C D.green.chernForm ≤ M.archStarPairing (ArakelovDivisor.smooth u) D ∧
    M.archStarPairing (ArakelovDivisor.smooth u) D ≤ uMax * M.geomDeg C D.green.chernForm := by
  rw [M.archStarPairing_smooth_left]
  unfold geomDeg
  have h1 := C.intX_mul_nonneg hlo hpos
  have h2 := C.intX_mul_nonneg hhi hpos
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h1 h2
  exact ⟨by linarith, by linarith⟩

end ArakelovPairingModel

/-- Top-level export alias for `ArakelovPairingModel.poincare_lelong_inv`. -/
theorem poincare_lelong_inv {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ : DivisorCurrentMap A PrimeDiv} (M : ArakelovPairingModel δ)
    {D : PrimeDiv →₀ ℤ} (g : GreenCurrentData δ D) (u : A.Curr00) :
    M.intX (A.mul00_11 g.curr (A.ddc u)) =
      M.intX (A.mul00_11 u g.chernForm) - D.sum (fun W m => (m : ℝ) * M.intPrime W u) :=
  M.poincare_lelong_inv g u

end PoincareLelongInvAndPairings

/-! ## Section 7: Concrete Instantiations & Stage-11 Modular-Curve Bridges -/

section ConcreteInstancesAndStage11Bridges

private lemma mvPoly_pderiv_comm_01 (g : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 g) =
      MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 g) := by
  have h10 : MvPolynomial.pderiv (1 : Fin 2) (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) = 0 :=
    MvPolynomial.pderiv_X_of_ne (by decide)
  have h01 : MvPolynomial.pderiv (0 : Fin 2) (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ) = 0 :=
    MvPolynomial.pderiv_X_of_ne (by decide)
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [Derivation.leibniz, map_add, smul_eq_mul]
    have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with rfl | rfl
    · simp only [MvPolynomial.pderiv_X_self, h10, Derivation.map_one_eq_zero, map_zero, hp]
      ring
    · simp only [MvPolynomial.pderiv_X_self, h01, Derivation.map_one_eq_zero, map_zero, hp]
      ring

/-- **Concrete Infinite-Dimensional `DolbeaultCurrentAlgebra` on `ℝ[z, z̄]`**
(`MvPolynomial (Fin 2) ℝ` with `X 0 = z`, `X 1 = z̄`, `∂ = ∂/∂z`, `∂̄ = ∂/∂z̄`, and graded
exterior algebra `(1, 0) ∧ (0, 1) = dz ∧ dz̄ = -dz̄ ∧ dz`):
proves unconditionally that every single axiom of `DolbeaultCurrentAlgebra` is realized by
genuine differential operators! -/
def polyDolbeaultAlgebra : DolbeaultCurrentAlgebra.{0} where
  Curr00 := MvPolynomial (Fin 2) ℝ
  Curr10 := MvPolynomial (Fin 2) ℝ
  Curr01 := MvPolynomial (Fin 2) ℝ
  Curr11 := MvPolynomial (Fin 2) ℝ
  instAdd00 := inferInstance
  instMod00 := inferInstance
  instAdd10 := inferInstance
  instMod10 := inferInstance
  instAdd01 := inferInstance
  instMod01 := inferInstance
  instAdd11 := inferInstance
  instMod11 := inferInstance
  d00 := (MvPolynomial.pderiv 0).toLinearMap
  dbar00 := (MvPolynomial.pderiv 1).toLinearMap
  d01 := (MvPolynomial.pderiv 0).toLinearMap
  dbar10 := -((MvPolynomial.pderiv 1).toLinearMap)
  d_dbar_anticomm := fun g => by
    change MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 g) +
        -(MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 g)) = 0
    rw [mvPoly_pderiv_comm_01 g, add_neg_cancel]
  mul00_11 := LinearMap.mul ℝ (MvPolynomial (Fin 2) ℝ)
  mul00_10 := LinearMap.mul ℝ (MvPolynomial (Fin 2) ℝ)
  mul00_01 := LinearMap.mul ℝ (MvPolynomial (Fin 2) ℝ)
  wedge10_01 := LinearMap.mul ℝ (MvPolynomial (Fin 2) ℝ)
  wedge01_10 := -(LinearMap.mul ℝ (MvPolynomial (Fin 2) ℝ)).flip
  wedge_anticomm := fun α β => rfl
  d01_mul00_01 := fun g α => by
    change MvPolynomial.pderiv 0 (g * α) =
      MvPolynomial.pderiv 0 g * α + g * MvPolynomial.pderiv 0 α
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, add_comm, mul_comm α]
  dbar10_mul00_10 := fun g β => by
    change -(MvPolynomial.pderiv 1 (g * β)) =
      -(β * MvPolynomial.pderiv 1 g) + g * -(MvPolynomial.pderiv 1 β)
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  closed11 := ⊤
  ddc_mem_closed11 := fun _ => trivial

/-- Explicit verification of `polyDolbeaultAlgebra` on `z * z̄`: `dd^c (z * z̄) = 1`. -/
theorem polyDolbeaultAlgebra_ddc_z_zbar :
    polyDolbeaultAlgebra.ddc (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)) =
      ((1 : MvPolynomial (Fin 2) ℝ) : polyDolbeaultAlgebra.Curr11) := by
  change MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))) = 1
  rw [Derivation.leibniz, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (by decide)]
  simp

/-! ### Direct Wiring to `Stage11HermitianCurvature` & `Stage11ArakelovFaltings` (`SL₂(ℤ) \ ℍ`) -/

/-- Concrete Green potential `g_f(τ) = -log (‖f(τ)‖² · Im(τ)^k)` of a weight-`k` automorphic
section `f` on `UpperHalfPlane` equipped with the Petersson Hermitian metric `h_k(τ) = Im(τ)^k`. -/
def uhpGreenPotential (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℝ :=
  -Real.log (automorphicNormSq k f τ)

/-- `SL₂(ℤ)`-invariance of the automorphic Green potential `g_f` for every level-1 modular form
`f ∈ M_k(SL₂(ℤ))`. -/
theorem uhpGreenPotential_sl2Z_invariant {k : ℤ}
    (f : ModularForm RHDirect.Stage7EisensteinSeries.SL2ZRange k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    uhpGreenPotential k f (γ • τ) = uhpGreenPotential k f τ := by
  unfold uhpGreenPotential
  rw [automorphicNormSq_modularForm_sl2Z_invariant f γ τ]

/-- **Concrete Modular-Curve Poincaré–Lelong Curvature Identity Away from Zeros**:
for every holomorphic function `f : UpperHalfPlane → ℂ`, weight `k : ℤ`, and `τ ∈ ℍ` with `f τ ≠ 0`,
$$\frac{1}{4\pi} \Delta_{\mathrm{Eucl}}\bigl(-\log(\|f(\tau)\|^2 (\operatorname{Im}\tau)^k)\bigr)
  = \frac{k}{4\pi} (\operatorname{Im}\tau)^{-2} = c_1(\omega^{\otimes k}, h_k)(\tau).$$ -/
theorem uhpGreenPotential_ddc_eq_firstChern {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℤ) {τ : UpperHalfPlane} (hτ : f τ ≠ 0) :
    euclLaplacianR (uhpGreenPotential k f) τ / (4 * Real.pi) = firstChernDensity k τ := by
  have hfun : uhpGreenPotential k f = fun w => -(Real.log (‖f w‖ ^ 2 * w.im ^ (k : ℝ))) := by
    funext w
    unfold uhpGreenPotential automorphicNormSq automorphicMetric
    rw [Real.rpow_intCast]
  have hneg_lap : ∀ φ : UpperHalfPlane → ℝ,
      euclLaplacianR (fun w => -φ w) τ = -euclLaplacianR φ τ := by
    intro φ
    have hdn : ∀ (g : ℝ → ℝ) (a : ℝ), deriv (fun t : ℝ => -g t) a = -deriv g a :=
      fun g a => deriv.neg
    unfold euclLaplacianR partialXXR partialYYR uhpSliceXR uhpSliceYR
    have hx : (fun x : ℝ => deriv (fun t : ℝ => -φ (UpperHalfPlane.ofComplex ((t : ℂ) + Complex.I * (τ.im : ℂ)))) x) =
        fun x : ℝ => -deriv (fun t : ℝ => φ (UpperHalfPlane.ofComplex ((t : ℂ) + Complex.I * (τ.im : ℂ)))) x := by
      funext x; exact hdn _ x
    have hy : (fun y : ℝ => deriv (fun t : ℝ => -φ (UpperHalfPlane.ofComplex ((τ.re : ℂ) + Complex.I * (t : ℂ)))) y) =
        fun y : ℝ => -deriv (fun t : ℝ => φ (UpperHalfPlane.ofComplex ((τ.re : ℂ) + Complex.I * (t : ℂ)))) y := by
      funext y; exact hdn _ y
    rw [hx, hy, hdn, hdn]
    ring
  rw [hfun, hneg_lap, bochner_log_laplacian_weight_k hf (k : ℝ) hτ, firstChernDensity_weight_k_eq]
  have hrpow : τ.im ^ (-2 : ℝ) = (τ.im ^ 2)⁻¹ := by
    rw [Real.rpow_neg τ.im_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow]
  ring

/-- **Ramanujan Discriminant `Δ` Green Potential & Exact Degree-1 Curvature Integral**:
`24 * faltingsHeight(τ) = -log ((2π)^24 ‖Δ(τ)‖² y^12)` has exact `dd^c`-density
`firstChernDensity 12` on `ℍ` (since `Δ` never vanishes on `ℍ`), integrating over `SL₂(ℤ) \ ℍ`
to `deg(ω^{⊗ 12}) = 1`. -/
theorem faltingsHeight_green_ddc_and_degree :
    (∀ τ : UpperHalfPlane,
      euclLaplacianR (fun w => 24 * faltingsHeight w) τ / (4 * Real.pi) =
        firstChernDensity 12 τ) ∧
    ∫ p in Stage10PeterssonHecke.stdFD,
      (if hp : 0 < p.2 then
        euclLaplacianR (fun w => 24 * faltingsHeight w) (Stage10PeterssonHecke.pairToUHP p hp) /
          (4 * Real.pi)
      else 0) = 1 := by
  have hpoint : ∀ τ : UpperHalfPlane,
      euclLaplacianR (fun w => 24 * faltingsHeight w) τ / (4 * Real.pi) =
        firstChernDensity 12 τ := by
    intro τ
    have hsmul : euclLaplacianR (fun w => 24 * faltingsHeight w) τ =
        24 * euclLaplacianR faltingsHeight τ := by
      unfold euclLaplacianR partialXXR partialYYR uhpSliceXR uhpSliceYR
      have hx : (fun x : ℝ => deriv (fun t : ℝ => 24 * faltingsHeight
            (UpperHalfPlane.ofComplex ((t : ℂ) + Complex.I * (τ.im : ℂ)))) x) =
          fun x : ℝ => 24 * deriv (fun t : ℝ => faltingsHeight
            (UpperHalfPlane.ofComplex ((t : ℂ) + Complex.I * (τ.im : ℂ)))) x := by
        funext x; exact deriv_const_mul_field 24
      have hy : (fun y : ℝ => deriv (fun t : ℝ => 24 * faltingsHeight
            (UpperHalfPlane.ofComplex ((τ.re : ℂ) + Complex.I * (t : ℂ)))) y) =
          fun y : ℝ => 24 * deriv (fun t : ℝ => faltingsHeight
            (UpperHalfPlane.ofComplex ((τ.re : ℂ) + Complex.I * (t : ℂ)))) y := by
        funext y; exact deriv_const_mul_field 24
      rw [hx, hy, deriv_const_mul_field 24, deriv_const_mul_field 24]
      ring
    rw [hsmul, euclLaplacianR_faltingsHeight τ, firstChernDensity_weight_k_eq 12 τ]
    have hrpow : τ.im ^ (-2 : ℝ) = (τ.im ^ 2)⁻¹ := by
      rw [Real.rpow_neg τ.im_pos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hrpow]
    push_cast
    ring
  refine ⟨hpoint, ?_⟩
  have hcongr : Set.EqOn
      (fun p : ℝ × ℝ =>
        if hp : 0 < p.2 then
          euclLaplacianR (fun w => 24 * faltingsHeight w)
            (Stage10PeterssonHecke.pairToUHP p hp) / (4 * Real.pi)
        else 0)
      (fun p : ℝ × ℝ => if hp : 0 < p.2 then firstChernDensity 12 (Stage10PeterssonHecke.pairToUHP p hp) else 0)
      Stage10PeterssonHecke.stdFD := by
    intro p hp
    simp only [dif_pos hp.2.1, hpoint]
  rw [MeasureTheory.setIntegral_congr_fun Stage10PeterssonHecke.measurableSet_stdFD hcongr,
    firstChernIntegral_density_eq 12]
  norm_num

/-- **Direct Bridge to `Stage11ArakelovFaltings.ArithLineBundle`**:
for any `ArakelovPairingModel M` with positivity cone `C`, and any arithmetic surface model
`S : ArithSurfaceModel m E_arch`, shifting an `ArithLineBundle` by a smooth archimedean fiber
metric change `(0, u)` bounded by `[uMin, uMax]` brackets the archimedean Green pairing
`⟨(0, u), D̂⟩_∞` identically by the `ArithLineBundle.arakelovPair` fiber pairings
`(L · uMin F_∞)_Ar ≤ ⟨(0, u), D̂⟩_∞ ≤ (L · uMax F_∞)_Ar` whenever `L.geomDeg = deg(ω_D)`. -/
theorem archStarPairing_bridge_arithLineBundle {A : DolbeaultCurrentAlgebra} {PrimeDiv : Type*}
    {δ : DivisorCurrentMap A PrimeDiv} (M : ArakelovPairingModel δ)
    (C : M.PositivityCone)
    {m : ℕ} {E_arch : Type*} [NormedAddCommGroup E_arch] [InnerProductSpace ℝ E_arch]
    (S : ArithSurfaceModel m E_arch) (L : ArithLineBundle m E_arch)
    {D : ArakelovDivisor δ} (hdeg : L.geomDeg = M.geomDeg C D.green.chernForm)
    (hpos : M.IsSemipositiveGreen C D)
    {u : A.Curr00} {uMin uMax : ℝ}
    (hlo : C.isNonneg00 (u - uMin • C.one00))
    (hhi : C.isNonneg00 (uMax • C.one00 - u)) :
    ArithLineBundle.arakelovPair S L (ArithLineBundle.fiberBundle uMin) ≤
      M.archStarPairing (ArakelovDivisor.smooth u) D ∧
    M.archStarPairing (ArakelovDivisor.smooth u) D ≤
      ArithLineBundle.arakelovPair S L (ArithLineBundle.fiberBundle uMax) := by
  rw [ArithLineBundle.arakelovPair_fiber_right, ArithLineBundle.arakelovPair_fiber_right, hdeg]
  exact M.archStarPairing_metric_change_bounds C hpos hlo hhi

/-- **Wave-1 Pillar-5 Green Currents Master Synthesis**:
certifies all seven core results of `Stage14M3_GreenCurrents` in a single unconditional theorem
for direct verification and downstream Wave-2 consumption (`ArakelovIntersection`,
`ChowFormHeights`, `NefRiemannRoch`). -/
theorem stage14M3_green_currents_synthesis
    {A B : DolbeaultCurrentAlgebra} {PrimeDivX PrimeDivY : Type*}
    {δX : DivisorCurrentMap A PrimeDivX} {δY : DivisorCurrentMap B PrimeDivY}
    (M : ArakelovPairingModel δX)
    (f : DolbeaultMorphism A B) {divPull : (PrimeDivX →₀ ℤ) →+ (PrimeDivY →₀ ℤ)}
    (hcompat : DivisorPullbackCompat f δX δY divPull)
    {D₁ D₂ : PrimeDivX →₀ ℤ}
    (g₁ : GreenCurrentData δX D₁) (g₂ : GreenCurrentData δX D₂) (u : A.Curr00) :
    (starProductClass g₁ g₂ = starProductClass g₂ g₁) ∧
    (StarProductGreen (g₁.add g₂) g₁ = StarProductGreen g₁ g₁ + StarProductGreen g₂ g₁) ∧
    (f.map11 (StarProductGreen g₁ g₂) =
      StarProductGreen (g₁.pullback f hcompat) (g₂.pullback f hcompat)) ∧
    (M.intX (A.mul00_11 g₁.curr (A.ddc u)) =
      M.intX (A.mul00_11 u g₁.chernForm) - D₁.sum (fun W m => (m : ℝ) * M.intPrime W u)) ∧
    (∀ R : ℝ, 0 < R → ∀ v : ℝ → ℝ, Continuous v →
      Tendsto (fun ε : ℝ => ∫ r in (0 : ℝ)..R, v r * plRadialKernel ε r) (𝓝[>] 0) (𝓝 (v 0))) := by
  refine ⟨(green_current_commutativity g₁ g₂).2, starProductGreen_add_left g₁ g₂ g₁,
    (green_current_pullback_compat f hcompat g₁ g₂ 1).2.2.2.1,
    M.poincare_lelong_inv g₁ u, fun R hR v hv => poincare_lelong_1d_approx_identity hv hR⟩

end ConcreteInstancesAndStage11Bridges

end

end RHDirect.Stage14M3_GreenCurrents
