import RHDirect.Stage2WeilMetaplectic
import RHDirect.Stage6AdelicPoisson
import RHDirect.Stage11DoublingRallis
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Complex.Circle

/-!
# RHDirect.Stage14M1_SchrodingerFockModel

Unconditional, self-contained (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`)
Lean 4 formalization of the **Local & Adelic Schrödinger–Fock Model of the Unitary Weil
Representation** for Package `M1` Wave 1 (supporting Wave 2 `AdelicWeilTheta`, `SiegelEisenstein`,
and `DoublingZeta`).

## Main Components

1. **Concrete Archimedean Complex Schrödinger Model (`volC`, `Fr`, `IsArchSchwartz`, `realWeilOp`)**:
   - Self-dual Haar measure `volC = 2 • volume` on `ℂ`, standard additive character
     `ee x = exp(2πi x)`, self-dual Fourier transform `Fr Φ z = ∫ u, ee(2 Re(z̄ u)) Φ(u) dvolC`.
   - Unconditional Fourier inversion `Fr_Fr` (`Fr (Fr Φ) z = Φ (-z)`), order-4 identity
     `Fr_pow_four`, and **Archimedean Plancherel unitarity** `Fr_unitary` on `IsArchSchwartz`
     (containing every `SchwartzMap ℂ ℂ` and every complex Gaussian).
   - Full `SL₂(ℝ)` / `U(1,1)` archimedean Weil operator `realWeilOp a b c d` (matching Alpöge's
     `RealWeilRepresentationHypothesis`), proved `L²(ℂ, volC)`-unitary for all `a d - b c = 1`,
     plus higher-rank matrix Siegel parabolic & commuting `U(H)` dual-pair operators on `M_{m×n}(ℂ)`
     (matching `SiegelWeilUnitarySchrodinger.IsWeilSch`).
2. **Concrete Bargmann–Fock Space (`ArchFockModel`) & Exact Gaussian Vacuum Eigenvalue
   (`gauss_vacuum_eigenvalue`)**:
   - Exact complex Gaussian Fourier integral `complex_gauss_fourier_exact` via Mathlib's
     `fourier_gaussian_innerProductSpace`.
   - Exact self-duality `Fr_stdGauss` (`Fr stdGauss = stdGauss`), Weil Weyl eigenvalue
     `realWeilOp 0 1 (-1) 0 stdGauss = I • stdGauss`, exact norm `archInner stdGauss stdGauss = 1/2`,
     and **`gauss_vacuum_eigenvalue`**: for every `θ : ℝ`,
     `realWeilOp (cos θ) (sin θ) (-sin θ) (cos θ) stdGauss = exp(i θ) • stdGauss`.
   - Higher-rank Hermitian matrix Gaussian vacuum `matrixGaussVacuum` with exact `U(H) × U(n)`
     invariance, polynomial-times-Gaussian Fock submodule `ArchFockSubmodule`, and concrete
     **`ArchFockModel`** with creation/annihilation operators (`creOp`, `annOp`), Bosonic CCR
     `[a_i, a_j†] = δ_{ij}`, vacuum annihilation `a_i |0⟩ = 0`, number operator eigenvalues, exact
     Bargmann–Fock inner product `(a_i†)* = a_i`, monomial orthogonality `⟨z^α, z^β⟩ = δ_{α,β} α!`,
     positive definiteness, injectivity of `toSchrodinger`, and orthogonal vacuum projection.
3. **Concrete Non-Archimedean `p`-Adic Schrödinger Model (`PadicSB`, `padicWeil*`)**:
   - Built directly on `Stage6AdelicPoisson` (`IsPadicSchwartzBruhat`, `padicHaarInt`,
     `padicFourier`, `ballInd`).
   - Exact `p`-adic `L²` inner product `padicInner`, Haar scaling law `padicHaarInt_mul_left`,
     Siegel Levi `padicWeilLevi`, quadratic-phase unipotent `padicWeilUnip`, and Weyl Fourier
     `padicWeilWeyl` operators, with **full `p`-adic Plancherel unitarity** (`padicWeilWeyl_unitary`),
     exact spherical invariance of `1_{ℤ_p}`, and exact split-place matrix coefficient
     `padicInner_spherical_levi`.
4. **Unified `LocalWeilRep v`, `SchwartzBruhatAdelic`, & `weil_representation_unitary`**:
   - Unified `LocalWeilRep` structure parameterized by place `v`, instantiated unconditionally at
     archimedean (`archLocalWeilRep`), `p`-adic (`padicLocalWeilRep`), and finite-field
     (`finiteFieldLocalWeilRep`, bridged from `Stage2WeilMetaplectic`) places.
   - Concrete **`SchwartzBruhatAdelic`** as the `ℂ`-submodule spanned by factorizable adelic
     Schwartz–Bruhat pure tensors (`fInf ⊗ ⊗'_p fFin p` with `fFin p = 1_{ℤ_p}` outside a finite
     set `supp`), with global Gaussian-spherical vacuum `adelicVacuum`, exact inner-product
     factorization, and **`weil_representation_unitary`**.
5. **Split-Place Idempotent Algebra & `split_support_projects_vacuum`**:
   - Distills Alpöge's `WeilRepresentationSplitSupportProjectsVacuum`: CM-involutive rings,
     split idempotents `e² = e, e * c(e) = 0`, orthogonal split-idempotent families, matrix
     factorization & determinant multiplicativity, lattice decomposition, and unconditional
     **`split_support_projects_vacuum`** (general inductive theorem + concrete `p`-adic &
     finite-field instantiations).
6. **Wave-2 Readiness Bridges**:
   - `IsWeilSch`, `siegelSection`, `thetaKernel`, `weil_doubling_bridge`, and
     `SchrodingerFockPackage` for `AdelicWeilTheta`, `SiegelEisenstein`, and `DoublingZeta`.
-/

noncomputable section

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function
open RHDirect RHDirect.RallisSeesaw RHDirect.Stage2WeilMetaplectic
open RHDirect.Stage6AdelicPoisson RHDirect.Stage11DoublingRallis
open scoped BigOperators InnerProductSpace ComplexConjugate FourierTransform Topology
open scoped Real RestrictedProduct NNReal ENNReal

namespace RHDirect.Stage14M1_SchrodingerFockModel

local instance instFactPrimePrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ## Section 1: Concrete Archimedean Complex Schrödinger Space, `Fr`, & `SL₂(ℝ)` Weil Operators -/

section ArchimedeanSchrodinger

/-- Standard archimedean additive character `ee(x) = exp(2πi x)` on `ℝ`. -/
def ee (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

@[simp]
theorem ee_zero : ee 0 = 1 := by
  simp [ee]

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_neg (x : ℝ) : ee (-x) = (ee x)⁻¹ := by
  unfold ee
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem ee_sub (x y : ℝ) : ee (x - y) = ee x * ee (-y) := by
  rw [sub_eq_add_neg, ee_add]

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  have h : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem star_ee (x : ℝ) : star (ee x) = ee (-x) := by
  have hmul : star (ee x) * ee x = 1 := by
    rw [Complex.star_def, Complex.conj_mul', norm_ee x]
    norm_num
  have hinv : ee (-x) * ee x = 1 := by
    rw [← ee_add, neg_add_cancel, ee_zero]
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) (hmul.trans hinv.symm)

theorem continuous_ee : Continuous ee := by
  unfold ee
  fun_prop

/-- Self-dual Haar measure `volC = 2 • volume` on `ℂ ≃ ℝ²` for the pairing
`ψ(2 Re(z̄ u)) = ee(2 Re(z̄ u))` (matching Alpöge's `RealWeilRepresentationHypothesis`). -/
def volC : Measure ℂ :=
  (2 : ℝ≥0∞) • (volume : Measure ℂ)

instance instSFiniteVolC : SFinite volC := by
  unfold volC
  infer_instance

theorem integral_volC (f : ℂ → ℂ) :
    ∫ u, f u ∂volC = 2 * ∫ u, f u := by
  rw [volC, integral_smul_measure]
  simp

theorem integrable_volC_iff {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) :
    Integrable f volC ↔ Integrable f volume := by
  unfold volC
  exact integrable_smul_measure (by simp) (by simp)

/-- Real dilation Jacobian for `volC`: `∫ u, f (s * u) ∂volC = (s²)⁻¹ * ∫ u, f u ∂volC`. -/
theorem integral_volC_smul (f : ℂ → ℂ) {s : ℝ} (hs : s ≠ 0) :
    ∫ u, f ((s : ℂ) * u) ∂volC = (((s ^ 2)⁻¹ : ℝ) : ℂ) * ∫ u, f u ∂volC := by
  have h := Measure.integral_comp_smul (volume : Measure ℂ) f s
  simp only [Complex.real_smul, Complex.finrank_real_complex] at h
  rw [integral_volC, integral_volC, h,
    abs_of_pos (by positivity : (0 : ℝ) < (s ^ 2)⁻¹)]
  ring_nf

/-- Reflection invariance of `volC`: `∫ u, f (-u) ∂volC = ∫ u, f u ∂volC`. -/
theorem integral_volC_neg (f : ℂ → ℂ) :
    ∫ u, f (-u) ∂volC = ∫ u, f u ∂volC := by
  have h := integral_volC_smul f (by norm_num : (-1 : ℝ) ≠ 0)
  simpa using h

/-- Standard `L²(ℂ, volC)` Hermitian inner product (conjugate-linear in the first argument). -/
def archInner (Φ₁ Φ₂ : ℂ → ℂ) : ℂ :=
  ∫ z, star (Φ₁ z) * Φ₂ z ∂volC

theorem archInner_conj_symm (Φ₁ Φ₂ : ℂ → ℂ) :
    star (archInner Φ₁ Φ₂) = archInner Φ₂ Φ₁ := by
  unfold archInner
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

theorem archInner_self_eq_ofReal (Φ : ℂ → ℂ) :
    archInner Φ Φ = ((∫ z, ‖Φ z‖ ^ 2 ∂volC : ℝ) : ℂ) := by
  unfold archInner
  have hof : (∫ z, ((‖Φ z‖ ^ 2 : ℝ) : ℂ) ∂volC) = ((∫ z, ‖Φ z‖ ^ 2 ∂volC : ℝ) : ℂ) :=
    integral_ofReal
  rw [← hof]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]

theorem archInner_self_re_nonneg (Φ : ℂ → ℂ) :
    0 ≤ (archInner Φ Φ).re ∧ (archInner Φ Φ).im = 0 := by
  rw [archInner_self_eq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨integral_nonneg fun _ => sq_nonneg _, rfl⟩

/-- Self-dual complex Fourier transform on `(ℂ, volC)`:
`(Fr Φ)(z) = ∫_ℂ ee(2 Re(z̄ u)) Φ(u) dvolC(u)`. -/
def Fr (Φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ u, ee (2 * (conj z * u).re) * Φ u ∂volC

theorem inner_real_complex_eq (v z : ℂ) :
    inner ℝ v z = (conj z * v).re := by
  rw [Complex.inner]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Exact identification of `Fr Φ` with Mathlib's `Real.fourierIntegral`:
`Fr Φ z = 2 * 𝓕 Φ ((-2) * z)`. -/
theorem Fr_eq (Φ : ℂ → ℂ) (z : ℂ) :
    Fr Φ z = 2 * 𝓕 Φ (((-2 : ℝ) : ℂ) * z) := by
  rw [Fr, integral_volC, Real.fourier_eq']
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  dsimp only
  simp only [ee, smul_eq_mul]
  congr 2
  have h : inner ℝ v (((-2 : ℝ) : ℂ) * z) = -2 * (conj z * v).re := by
    rw [inner_real_complex_eq, map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  rw [h]
  push_cast
  ring

/-- Concrete Fourier-inversion Schwartz regularity class on `ℂ`: continuous `L¹` functions whose
Fourier transform is also `L¹`. Contains every `SchwartzMap ℂ ℂ` and every complex Gaussian. -/
def IsArchSchwartz (Φ : ℂ → ℂ) : Prop :=
  Continuous Φ ∧ Integrable Φ volume ∧ Integrable (𝓕 Φ) volume

/-- Every Mathlib Schwartz function `f : SchwartzMap ℂ ℂ` belongs to `IsArchSchwartz`. -/
theorem schwartzMap_isArchSchwartz (f : SchwartzMap ℂ ℂ) :
    IsArchSchwartz (f : ℂ → ℂ) := by
  refine ⟨f.continuous, f.integrable (μ := volume), ?_⟩
  have h := (𝓕 f).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe] at h

theorem isArchSchwartz_zero : IsArchSchwartz (fun _ : ℂ => (0 : ℂ)) := by
  refine ⟨continuous_const, integrable_zero _ _ _, ?_⟩
  have h0 : 𝓕 (fun _ : ℂ => (0 : ℂ)) = fun _ => 0 := by
    funext w; simp [Real.fourier_eq']
  rw [h0]
  exact integrable_zero _ _ _

theorem isArchSchwartz_const_mul (c : ℂ) {Φ : ℂ → ℂ} (hΦ : IsArchSchwartz Φ) :
    IsArchSchwartz (fun z => c * Φ z) := by
  refine ⟨continuous_const.mul hΦ.1, hΦ.2.1.const_mul c, ?_⟩
  have hF : 𝓕 (fun z => c * Φ z) = fun w => c * 𝓕 Φ w := by
    funext w
    simp only [Real.fourier_eq', smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => by dsimp only; ring)
  rw [hF]
  exact hΦ.2.2.const_mul c

theorem isArchSchwartz_add {Φ₁ Φ₂ : ℂ → ℂ} (h₁ : IsArchSchwartz Φ₁) (h₂ : IsArchSchwartz Φ₂) :
    IsArchSchwartz (fun z => Φ₁ z + Φ₂ z) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, ?_⟩
  have hF : 𝓕 (fun z => Φ₁ z + Φ₂ z) = fun w => 𝓕 Φ₁ w + 𝓕 Φ₂ w := by
    funext w
    simp only [Real.fourier_eq', smul_eq_mul, mul_add]
    have hcont_ker : Continuous (fun v : ℂ =>
        Complex.exp (((-2 * Real.pi * inner ℝ v w : ℝ) : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul
          (continuous_id.inner continuous_const))).mul continuous_const)
    exact integral_add
      (h₁.2.1.norm.mono' (hcont_ker.mul h₁.1).aestronglyMeasurable
        (Eventually.of_forall fun v => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]))
      (h₂.2.1.norm.mono' (hcont_ker.mul h₂.1).aestronglyMeasurable
        (Eventually.of_forall fun v => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]))
  rw [hF]
  exact h₁.2.2.add h₂.2.2

/-- Continuity of the Fourier transform `𝓕 Φ` for any continuous `L¹` function `Φ` on `ℂ`. -/
theorem continuous_fourier_of_isArchSchwartz {Φ : ℂ → ℂ} (hΦ : IsArchSchwartz Φ) :
    Continuous (𝓕 Φ) := by
  have hrew : 𝓕 Φ = fun w : ℂ =>
      ∫ v : ℂ, Complex.exp (((-2 * Real.pi * inner ℝ v w : ℝ) : ℂ) * Complex.I) * Φ v := by
    funext w; simp [Real.fourier_eq', smul_eq_mul]
  rw [hrew]
  refine MeasureTheory.continuous_of_dominated
      (bound := fun v : ℂ => ‖Φ v‖) ?_ ?_ hΦ.2.1.norm ?_
  · intro w
    have hcont : Continuous (fun v : ℂ =>
        Complex.exp (((-2 * Real.pi * inner ℝ v w : ℝ) : ℂ) * Complex.I) * Φ v) :=
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const)).mul
        hΦ.1
    exact hcont.aestronglyMeasurable
  · intro w
    exact Eventually.of_forall fun v => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  · exact Eventually.of_forall fun v =>
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_const.inner continuous_id))).mul continuous_const)).mul
        continuous_const

/-- **Archimedean Fourier Inversion on `IsArchSchwartz`**: `Fr (Fr Φ) z = Φ (-z)`. -/
theorem Fr_Fr {Φ : ℂ → ℂ} (hΦ : IsArchSchwartz Φ) (z : ℂ) :
    Fr (Fr Φ) z = Φ (-z) := by
  have e : Fr Φ = fun w => 2 * 𝓕 Φ (((-2 : ℝ) : ℂ) * w) := funext (Fr_eq Φ)
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hΦ.1 hΦ.2.1 hΦ.2.2) (-z)
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv, e, Fr]
  set k : ℂ → ℂ := fun v => ee (-(conj z * v).re) * (2 * 𝓕 Φ v) with hk
  have h := integral_volC_smul k (by norm_num : (-2 : ℝ) ≠ 0)
  have h1 : ∫ u, ee (2 * (conj z * u).re) * (2 * 𝓕 Φ (((-2 : ℝ) : ℂ) * u)) ∂volC =
      ∫ u, k (((-2 : ℝ) : ℂ) * u) ∂volC := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [hk]
    congr 2
    rw [mul_left_comm, Complex.re_ofReal_mul]
    ring
  rw [h1, h, integral_volC, ← mul_assoc]
  have h2 : (((((-2 : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * 2) = 2⁻¹ := by
    push_cast; norm_num
  rw [h2, hk]
  have h3 : ∀ v : ℂ, ee (-(conj z * v).re) * (2 * 𝓕 Φ v) =
      2 * (Complex.exp (((2 * Real.pi * inner ℝ v (-z) : ℝ) : ℂ) * Complex.I) • 𝓕 Φ v) := by
    intro v
    have hi : inner ℝ v (-z) = -(conj z * v).re := by
      rw [inner_neg_right, inner_real_complex_eq]
    rw [hi, ee, smul_eq_mul]
    have e4 : 2 * (Real.pi : ℂ) * Complex.I * ((-(conj z * v).re : ℝ) : ℂ) =
        ((2 * Real.pi * -(conj z * v).re : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e4]
    ring
  simp only [h3]
  rw [integral_const_mul]
  simp

/-- `Fr` preserves `IsArchSchwartz`. -/
theorem Fr_isArchSchwartz {Φ : ℂ → ℂ} (hΦ : IsArchSchwartz Φ) :
    IsArchSchwartz (Fr Φ) := by
  have e : Fr Φ = fun w => 2 * 𝓕 Φ (((-2 : ℝ) : ℂ) * w) := funext (Fr_eq Φ)
  have hcontF : Continuous (𝓕 Φ) := continuous_fourier_of_isArchSchwartz hΦ
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact continuous_const.mul (hcontF.comp (continuous_const.mul continuous_id))
  · rw [e]
    have hsm : Integrable (fun w : ℂ => 𝓕 Φ (((-2 : ℝ) : ℂ) * w)) volume := by
      simpa [Complex.real_smul] using hΦ.2.2.comp_smul (by norm_num : (-2 : ℝ) ≠ 0)
    exact hsm.const_mul 2
  · have hFF : 𝓕 (Fr Φ) = fun w => (2 : ℂ)⁻¹ * Φ (((2⁻¹ : ℝ) : ℂ) * w) := by
      funext w
      have hw := Fr_Fr hΦ (((-2⁻¹ : ℝ) : ℂ) * w)
      rw [Fr_eq (Fr Φ)] at hw
      have harg : ((-2 : ℝ) : ℂ) * (((-2⁻¹ : ℝ) : ℂ) * w) = w := by
        rw [← mul_assoc]; norm_num
      have hneg : -(((-2⁻¹ : ℝ) : ℂ) * w) = ((2⁻¹ : ℝ) : ℂ) * w := by
        push_cast; ring
      rw [harg, hneg] at hw
      calc 𝓕 (Fr Φ) w = (2 : ℂ)⁻¹ * (2 * 𝓕 (Fr Φ) w) := by ring
        _ = (2 : ℂ)⁻¹ * Φ (((2⁻¹ : ℝ) : ℂ) * w) := by rw [hw]
    rw [hFF]
    have hsm : Integrable (fun w : ℂ => Φ (((2⁻¹ : ℝ) : ℂ) * w)) volume := by
      simpa [Complex.real_smul] using hΦ.2.1.comp_smul (by norm_num : (2⁻¹ : ℝ) ≠ 0)
    exact hsm.const_mul (2 : ℂ)⁻¹

/-- Order-4 identity for the complex Fourier transform: `Fr⁴ = id` on `IsArchSchwartz`. -/
theorem Fr_pow_four {Φ : ℂ → ℂ} (hΦ : IsArchSchwartz Φ) (z : ℂ) :
    Fr (Fr (Fr (Fr Φ))) z = Φ z := by
  rw [Fr_Fr (Fr_isArchSchwartz (Fr_isArchSchwartz hΦ)), Fr_Fr hΦ, neg_neg]

/-- **Archimedean Plancherel / Parseval Unitarity on `IsArchSchwartz`**:
`⟨Fr Φ₁, Fr Φ₂⟩_{volC} = ⟨Φ₁, Φ₂⟩_{volC}`! -/
theorem Fr_unitary {Φ₁ Φ₂ : ℂ → ℂ} (h₁ : IsArchSchwartz Φ₁) (h₂ : IsArchSchwartz Φ₂) :
    archInner (Fr Φ₁) (Fr Φ₂) = archInner Φ₁ Φ₂ := by
  have hF₂ : IsArchSchwartz (Fr Φ₂) := Fr_isArchSchwartz h₂
  have h1v : Integrable Φ₁ volC := (integrable_volC_iff Φ₁).mpr h₁.2.1
  have h1c : Integrable (fun u : ℂ => star (Φ₁ u)) volC :=
    h1v.norm.mono' (continuous_star.comp h₁.1).aestronglyMeasurable
      (Eventually.of_forall fun u => by simp)
  have h2v : Integrable (Fr Φ₂) volC := (integrable_volC_iff (Fr Φ₂)).mpr hF₂.2.1
  have hprod : Integrable (fun p : ℂ × ℂ => star (Φ₁ p.1) * Fr Φ₂ p.2) (volC.prod volC) :=
    h1c.mul_prod h2v
  have hint : Integrable
      (fun p : ℂ × ℂ => ee (-(2 * (conj p.2 * p.1).re)) * star (Φ₁ p.1) * Fr Φ₂ p.2)
      (volC.prod volC) := by
    have hcont_p : Continuous (fun p : ℂ × ℂ =>
        ee (-(2 * (conj p.2 * p.1).re)) * star (Φ₁ p.1) * Fr Φ₂ p.2) :=
      ((continuous_ee.comp (continuous_neg.comp (continuous_const.mul
        (Complex.continuous_re.comp ((Complex.continuous_conj.comp continuous_snd).mul
          continuous_fst))))).mul
        ((continuous_star.comp h₁.1).comp continuous_fst)).mul
        (hF₂.1.comp continuous_snd)
    refine hprod.norm.mono' hcont_p.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, norm_ee, one_mul, ← norm_mul]
  calc archInner (Fr Φ₁) (Fr Φ₂)
      = ∫ z, (∫ u, ee (-(2 * (conj z * u).re)) * star (Φ₁ u) ∂volC) * Fr Φ₂ z ∂volC := by
          unfold archInner Fr
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          dsimp only
          congr 1
          rw [Complex.star_def, ← integral_conj]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          dsimp only
          rw [map_mul, ← Complex.star_def, star_ee]
    _ = ∫ z, ∫ u, ee (-(2 * (conj z * u).re)) * star (Φ₁ u) * Fr Φ₂ z ∂volC ∂volC := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          dsimp only
          rw [← integral_mul_const]
    _ = ∫ u, ∫ z, ee (-(2 * (conj z * u).re)) * star (Φ₁ u) * Fr Φ₂ z ∂volC ∂volC :=
          (integral_integral_swap hint).symm
    _ = ∫ u, star (Φ₁ u) * Fr (Fr Φ₂) (-u) ∂volC := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          dsimp only
          unfold Fr
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          dsimp only
          have hre : -(2 * (conj z * u).re) = 2 * (conj (-u) * z).re := by
            have h1 : (conj z * u).re = (conj u * z).re := by
              rw [← Complex.conj_re (conj u * z), map_mul, starRingEnd_self_apply, mul_comm]
            rw [map_neg, neg_mul, Complex.neg_re, h1]
            ring
          rw [hre]
          ring
    _ = archInner Φ₁ Φ₂ := by
          unfold archInner
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          dsimp only
          rw [Fr_Fr h₂ (-u), neg_neg]

/-- **Concrete `SL₂(ℝ)` / `U(1,1)` Archimedean Schrödinger Weil Operator**
(matching Alpöge's `RealWeilRepresentationHypothesis.rWR`):
- For `c = 0`: `(ω(a, b, 0, d) Φ)(z) = ee(a b |z|²) · a · Φ(a z)`.
- For `c ≠ 0`: `(ω(a, b, c, d) Φ)(z) = i · (-c⁻¹) · ee((a/c) |z|²) · Fr(u ↦ ee((d/c)|u|²) Φ(u))(-c⁻¹ z)`. -/
def realWeilOp (a b c d : ℝ) (Φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if c = 0 then
    ee (a * b * Complex.normSq z) * (a : ℂ) * Φ ((a : ℂ) * z)
  else
    Complex.I * ((-c⁻¹ : ℝ) : ℂ) * ee (a / c * Complex.normSq z) *
      Fr (fun u => ee (d / c * Complex.normSq u) * Φ u) (((-c⁻¹ : ℝ) : ℂ) * z)

@[simp]
theorem realWeilOp_one (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp 1 0 0 1 Φ z = Φ z := by
  simp [realWeilOp]

theorem realWeilOp_levi (a : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp a 0 0 a⁻¹ Φ z = (a : ℂ) * Φ ((a : ℂ) * z) := by
  simp [realWeilOp]

theorem realWeilOp_unip (b : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp 1 b 0 1 Φ z = ee (b * Complex.normSq z) * Φ z := by
  simp [realWeilOp]

theorem realWeilOp_weyl (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp 0 1 (-1) 0 Φ z = Complex.I * Fr Φ z := by
  simp [realWeilOp]

theorem realWeilOp_smul (a b c d : ℝ) (k : ℂ) (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp a b c d (k • Φ) z = k * realWeilOp a b c d Φ z := by
  unfold realWeilOp Fr
  split_ifs
  · simp [Pi.smul_apply, smul_eq_mul]; ring
  · have hrew : (fun u => ee (2 * (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re) *
        (ee (d / c * Complex.normSq u) * (k • Φ) u)) =
        fun u => k * (ee (2 * (conj (((-c⁻¹ : ℝ) : ℂ) * z) * u).re) *
          (ee (d / c * Complex.normSq u) * Φ u)) := by
      funext u; simp [Pi.smul_apply, smul_eq_mul]; ring
    rw [hrew, integral_const_mul]
    ring

theorem realWeilOp_levi_mul (a₁ a₂ : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp a₁ 0 0 a₁⁻¹ (realWeilOp a₂ 0 0 a₂⁻¹ Φ) z =
      realWeilOp (a₁ * a₂) 0 0 (a₁ * a₂)⁻¹ Φ z := by
  simp only [realWeilOp_levi, Complex.ofReal_mul]
  ring_nf

theorem realWeilOp_unip_add (b₁ b₂ : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp 1 b₁ 0 1 (realWeilOp 1 b₂ 0 1 Φ) z =
      realWeilOp 1 (b₁ + b₂) 0 1 Φ z := by
  simp only [realWeilOp_unip, add_mul, ee_add]
  ring

theorem realWeilOp_levi_comp_unip (a b : ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    realWeilOp a 0 0 a⁻¹ (realWeilOp 1 b 0 1 Φ) z =
      realWeilOp 1 (a ^ 2 * b) 0 1 (realWeilOp a 0 0 a⁻¹ Φ) z := by
  simp only [realWeilOp_levi, realWeilOp_unip, Complex.normSq_mul, Complex.normSq_ofReal]
  have h : b * (a * a * Complex.normSq z) = a ^ 2 * b * Complex.normSq z := by ring
  rw [h]
  ring

/-- Chirp-stable archimedean Schwartz class: functions `Φ` such that `u ↦ ee(t |u|²) Φ(u)` lies in
`IsArchSchwartz` for every `t : ℝ` (holds for all Gaussians and Fock vectors!). -/
def IsChirpSchwartz (Φ : ℂ → ℂ) : Prop :=
  ∀ t : ℝ, IsArchSchwartz (fun u => ee (t * Complex.normSq u) * Φ u)

theorem IsChirpSchwartz.isArchSchwartz {Φ : ℂ → ℂ} (hΦ : IsChirpSchwartz Φ) :
    IsArchSchwartz Φ := by
  simpa using hΦ 0

/-- **Unitarity of `realWeilOp` for EVERY matrix `[[a, b], [c, d]] ∈ SL₂(ℝ)` (`a d - b c = 1`)**:
`⟨realWeilOp a b c d Φ₁, realWeilOp a b c d Φ₂⟩_{volC} = ⟨Φ₁, Φ₂⟩_{volC}`! -/
theorem realWeilOp_unitary {a b c d : ℝ} (hdet : a * d - b * c = 1)
    {Φ₁ Φ₂ : ℂ → ℂ} (h₁ : IsChirpSchwartz Φ₁) (h₂ : IsChirpSchwartz Φ₂) :
    archInner (realWeilOp a b c d Φ₁) (realWeilOp a b c d Φ₂) = archInner Φ₁ Φ₂ := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by linarith
    have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    unfold archInner
    have hpt : ∀ z : ℂ, star (realWeilOp a b 0 d Φ₁ z) * realWeilOp a b 0 d Φ₂ z =
        ((a ^ 2 : ℝ) : ℂ) * (star (Φ₁ ((a : ℂ) * z)) * Φ₂ ((a : ℂ) * z)) := by
      intro z
      simp only [realWeilOp, if_true, star_mul, star_ee, Complex.star_def, Complex.conj_ofReal]
      have hee : ee (-(a * b * Complex.normSq z)) * ee (a * b * Complex.normSq z) = 1 := by
        rw [← ee_add, neg_add_cancel, ee_zero]
      calc (starRingEnd ℂ) (Φ₁ ((a : ℂ) * z)) * ((a : ℂ) * ee (-(a * b * Complex.normSq z))) *
            (ee (a * b * Complex.normSq z) * (a : ℂ) * Φ₂ ((a : ℂ) * z))
          = (ee (-(a * b * Complex.normSq z)) * ee (a * b * Complex.normSq z)) *
              (((a : ℂ) * (a : ℂ)) * ((starRingEnd ℂ) (Φ₁ ((a : ℂ) * z)) * Φ₂ ((a : ℂ) * z))) := by
              ring
        _ = ((a ^ 2 : ℝ) : ℂ) * ((starRingEnd ℂ) (Φ₁ ((a : ℂ) * z)) * Φ₂ ((a : ℂ) * z)) := by
              rw [hee, one_mul]; push_cast; ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_volC_smul (fun u => star (Φ₁ u) * Φ₂ u) ha, ← mul_assoc]
    have ha2 : ((a ^ 2 : ℝ) : ℂ) * (((a ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 ha), Complex.ofReal_one]
    rw [ha2, one_mul]
  · set Ψ₁ : ℂ → ℂ := fun u => ee (d / c * Complex.normSq u) * Φ₁ u
    set Ψ₂ : ℂ → ℂ := fun u => ee (d / c * Complex.normSq u) * Φ₂ u
    have hpt : ∀ z : ℂ, star (realWeilOp a b c d Φ₁ z) * realWeilOp a b c d Φ₂ z =
        ((((c⁻¹ : ℝ) ^ 2 : ℝ) : ℂ)) *
          (star (Fr Ψ₁ (((-c⁻¹ : ℝ) : ℂ) * z)) * Fr Ψ₂ (((-c⁻¹ : ℝ) : ℂ) * z)) := by
      intro z
      simp only [realWeilOp, if_neg hc, star_mul, star_ee, Complex.star_def,
        Complex.conj_I, Complex.conj_ofReal]
      have hee : ee (-(a / c * Complex.normSq z)) * ee (a / c * Complex.normSq z) = 1 := by
        rw [← ee_add, neg_add_cancel, ee_zero]
      have hI : (-Complex.I) * Complex.I = 1 := by simp
      calc (starRingEnd ℂ) (Fr Ψ₁ (((-c⁻¹ : ℝ) : ℂ) * z)) *
              (ee (-(a / c * Complex.normSq z)) * (((-c⁻¹ : ℝ) : ℂ) * -Complex.I)) *
            (Complex.I * ((-c⁻¹ : ℝ) : ℂ) * ee (a / c * Complex.normSq z) *
              Fr Ψ₂ (((-c⁻¹ : ℝ) : ℂ) * z))
          = ((-Complex.I) * Complex.I) *
              (ee (-(a / c * Complex.normSq z)) * ee (a / c * Complex.normSq z)) *
              ((((-c⁻¹ : ℝ) : ℂ) * ((-c⁻¹ : ℝ) : ℂ)) *
                ((starRingEnd ℂ) (Fr Ψ₁ (((-c⁻¹ : ℝ) : ℂ) * z)) *
                  Fr Ψ₂ (((-c⁻¹ : ℝ) : ℂ) * z))) := by ring
        _ = ((((c⁻¹ : ℝ) ^ 2 : ℝ) : ℂ)) *
              ((starRingEnd ℂ) (Fr Ψ₁ (((-c⁻¹ : ℝ) : ℂ) * z)) *
                Fr Ψ₂ (((-c⁻¹ : ℝ) : ℂ) * z)) := by
              rw [hI, hee, one_mul, one_mul]; push_cast; ring
    have hs : (-c⁻¹ : ℝ) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hc)
    calc archInner (realWeilOp a b c d Φ₁) (realWeilOp a b c d Φ₂)
        = ((((c⁻¹ : ℝ) ^ 2 : ℝ) : ℂ)) *
            ∫ z, star (Fr Ψ₁ (((-c⁻¹ : ℝ) : ℂ) * z)) * Fr Ψ₂ (((-c⁻¹ : ℝ) : ℂ) * z) ∂volC := by
            unfold archInner
            simp_rw [hpt]
            rw [integral_const_mul]
      _ = archInner (Fr Ψ₁) (Fr Ψ₂) := by
            rw [integral_volC_smul (fun w => star (Fr Ψ₁ w) * Fr Ψ₂ w) hs, ← mul_assoc]
            have hinv : ((((c⁻¹ : ℝ) ^ 2 : ℝ) : ℂ)) * ((((-c⁻¹ : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
              rw [← Complex.ofReal_mul, neg_sq, mul_inv_cancel₀ (pow_ne_zero 2 (inv_ne_zero hc)),
                Complex.ofReal_one]
            rw [hinv, one_mul]
            rfl
      _ = archInner Ψ₁ Ψ₂ := Fr_unitary (h₁ (d / c)) (h₂ (d / c))
      _ = archInner Φ₁ Φ₂ := by
            unfold archInner Ψ₁ Ψ₂
            refine integral_congr_ae (Eventually.of_forall fun u => ?_)
            dsimp only
            simp only [star_mul, star_ee]
            have hee : ee (-(d / c * Complex.normSq u)) * ee (d / c * Complex.normSq u) = 1 := by
              rw [← ee_add, neg_add_cancel, ee_zero]
            calc star (Φ₁ u) * ee (-(d / c * Complex.normSq u)) *
                  (ee (d / c * Complex.normSq u) * Φ₂ u)
                = (ee (-(d / c * Complex.normSq u)) * ee (d / c * Complex.normSq u)) *
                    (star (Φ₁ u) * Φ₂ u) := by ring
              _ = star (Φ₁ u) * Φ₂ u := by rw [hee, one_mul]

theorem realWeilOp_levi_unitary {a : ℝ} (ha : a ≠ 0) (Φ₁ Φ₂ : ℂ → ℂ) :
    archInner (realWeilOp a 0 0 a⁻¹ Φ₁) (realWeilOp a 0 0 a⁻¹ Φ₂) = archInner Φ₁ Φ₂ := by
  unfold archInner
  have hpt : ∀ z : ℂ, star (realWeilOp a 0 0 a⁻¹ Φ₁ z) * realWeilOp a 0 0 a⁻¹ Φ₂ z =
      ((a ^ 2 : ℝ) : ℂ) * (star (Φ₁ ((a : ℂ) * z)) * Φ₂ ((a : ℂ) * z)) := by
    intro z
    simp only [realWeilOp_levi, star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_volC_smul (fun u => star (Φ₁ u) * Φ₂ u) ha, ← mul_assoc]
  have ha2 : ((a ^ 2 : ℝ) : ℂ) * (((a ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 ha), Complex.ofReal_one]
  rw [ha2, one_mul]

theorem realWeilOp_unip_unitary (b : ℝ) (Φ₁ Φ₂ : ℂ → ℂ) :
    archInner (realWeilOp 1 b 0 1 Φ₁) (realWeilOp 1 b 0 1 Φ₂) = archInner Φ₁ Φ₂ := by
  unfold archInner
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  simp only [realWeilOp_unip, star_mul, star_ee]
  have hee : ee (-(b * Complex.normSq z)) * ee (b * Complex.normSq z) = 1 := by
    rw [← ee_add, neg_add_cancel, ee_zero]
  calc star (Φ₁ z) * ee (-(b * Complex.normSq z)) * (ee (b * Complex.normSq z) * Φ₂ z)
      = (ee (-(b * Complex.normSq z)) * ee (b * Complex.normSq z)) * (star (Φ₁ z) * Φ₂ z) := by ring
    _ = star (Φ₁ z) * Φ₂ z := by rw [hee, one_mul]

theorem realWeilOp_weyl_unitary {Φ₁ Φ₂ : ℂ → ℂ}
    (h₁ : IsArchSchwartz Φ₁) (h₂ : IsArchSchwartz Φ₂) :
    archInner (realWeilOp 0 1 (-1) 0 Φ₁) (realWeilOp 0 1 (-1) 0 Φ₂) = archInner Φ₁ Φ₂ := by
  have heq : archInner (realWeilOp 0 1 (-1) 0 Φ₁) (realWeilOp 0 1 (-1) 0 Φ₂) =
      archInner (Fr Φ₁) (Fr Φ₂) := by
    unfold archInner
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    dsimp only
    simp only [realWeilOp_weyl, star_mul, Complex.star_def, Complex.conj_I]
    have hI : (-Complex.I) * Complex.I = 1 := by simp
    calc (starRingEnd ℂ) (Fr Φ₁ z) * -Complex.I * (Complex.I * Fr Φ₂ z)
        = ((-Complex.I) * Complex.I) * ((starRingEnd ℂ) (Fr Φ₁ z) * Fr Φ₂ z) := by ring
      _ = (starRingEnd ℂ) (Fr Φ₁ z) * Fr Φ₂ z := by rw [hI, one_mul]
  rw [heq, Fr_unitary h₁ h₂]

/-! ### Higher-Rank Unitary Dual-Pair Matrix Operators (`U(n,n) × U(H)` on `M_{m×n}(ℂ)`) -/

/-- Block-`2×2` matrix constructor on `Fin (n + n)` (matching Alpöge's `StdUnn.blk4`). -/
def blk4 {R : Type*} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- Upper-left `n × n` block extractor (matching Alpöge's `StdUnn.blkA`). -/
def blkA {R : Type*} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

/-- Standard skew-Hermitian form `J_n = [[0, 1], [-1, 0]]` defining `U(n, n)`. -/
def Jst (R : Type*) [Ring R] (n : ℕ) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 0 1 (-1) 0

/-- Matrix Hermitian pairing `⟨X, Y⟩_H = Xᴴ H Y ∈ M_n(ℂ)` for a Hermitian matrix `H ∈ M_m(ℂ)`. -/
def hermInner {m n : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
    (X Y : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Xᴴ * H * Y

theorem hermInner_unitary_invariant {m n : ℕ} {H h : Matrix (Fin m) (Fin m) ℂ}
    (hh : hᴴ * H * h = H) (X Y : Matrix (Fin m) (Fin n) ℂ) :
    hermInner H (h * X) (h * Y) = hermInner H X Y := by
  unfold hermInner
  calc (h * X)ᴴ * H * (h * Y)
      = Xᴴ * (hᴴ * H * h) * Y := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
    _ = Xᴴ * H * Y := by rw [hh]

def matrixWeilLevi {m n : ℕ} (χ : ℂˣ →* Circle) (a : GL (Fin n) ℂ)
    (Φ : Matrix (Fin m) (Fin n) ℂ → ℂ) (X : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
    ((‖(Matrix.GeneralLinearGroup.det a : ℂ)‖ : ℝ) ^ m : ℂ) * Φ (X * a.1)

def matrixWeilUnip {m n : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (Φ : Matrix (Fin m) (Fin n) ℂ → ℂ) (X : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  ee (Matrix.trace (b * hermInner H X X)).re * Φ X

def matrixDualPairAct {m n : ℕ} (h : GL (Fin m) ℂ)
    (Φ : Matrix (Fin m) (Fin n) ℂ → ℂ) (X : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  Φ (h⁻¹.1 * X)

theorem matrixDualPairAct_comm_levi {m n : ℕ} (χ : ℂˣ →* Circle)
    (h : GL (Fin m) ℂ) (a : GL (Fin n) ℂ)
    (Φ : Matrix (Fin m) (Fin n) ℂ → ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    matrixDualPairAct h (matrixWeilLevi χ a Φ) X =
      matrixWeilLevi χ a (matrixDualPairAct h Φ) X := by
  simp only [matrixDualPairAct, matrixWeilLevi, Matrix.mul_assoc]

theorem matrixDualPairAct_comm_unip {m n : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (h : GL (Fin m) ℂ) (hh : h⁻¹.1ᴴ * H * h⁻¹.1 = H) (b : Matrix (Fin n) (Fin n) ℂ)
    (Φ : Matrix (Fin m) (Fin n) ℂ → ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    matrixDualPairAct h (matrixWeilUnip H b Φ) X =
      matrixWeilUnip H b (matrixDualPairAct h Φ) X := by
  simp only [matrixDualPairAct, matrixWeilUnip, hermInner_unitary_invariant hh]

end ArchimedeanSchrodinger

/-! ## Section 2: Concrete Bargmann–Fock Model (`ArchFockModel`) & Exact `gauss_vacuum_eigenvalue` -/

section BargmannFockAndGaussianVacuum

/-- Standard 1D complex Gaussian vacuum `φ₀(z) = exp(-2π |z|²)` on `(ℂ, volC)`. -/
def stdGauss (z : ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * (Complex.normSq z : ℂ))

/-- Scaled 1D complex Gaussian `φ_α(z) = exp(-2π α |z|²)` for `α > 0`. -/
def archGauss (α : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi * (α : ℂ)) * (Complex.normSq z : ℂ))

@[simp]
theorem archGauss_one : archGauss 1 = stdGauss := by
  funext z; simp [archGauss, stdGauss]

@[simp]
theorem stdGauss_zero : stdGauss 0 = 1 := by
  simp [stdGauss]

theorem stdGauss_neg (z : ℂ) : stdGauss (-z) = stdGauss z := by
  simp [stdGauss]

theorem stdGauss_ne_zero (z : ℂ) : stdGauss z ≠ 0 :=
  Complex.exp_ne_zero _

theorem continuous_stdGauss : Continuous stdGauss := by
  unfold stdGauss
  fun_prop

theorem stdGauss_unit_rot (ζ z : ℂ) (hζ : ‖ζ‖ = 1) :
    stdGauss (ζ * z) = stdGauss z := by
  unfold stdGauss
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hζ, one_pow, one_mul]

/-- **Exact Complex Gaussian Fourier Integral (`complex_gauss_fourier_exact`)**:
for every `ε > 0`, `t : ℝ`, and `w : ℂ`,
$$∫_ℂ \exp(-ε |y|²)\,ee(t|y|² + 2\operatorname{Re}(\bar{w} y))\,d\mathrm{vol}_ℂ(y)
  = \frac{2\pi}{ε - 2\pi t i}\exp\!\left(-\frac{4\pi²|w|²}{ε - 2\pi t i}\right).$$ -/
theorem complex_gauss_fourier_exact (ε t : ℝ) (hε : 0 < ε) (w : ℂ) :
    ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) *
        ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC =
      (2 * Real.pi / ((ε : ℂ) - 2 * Real.pi * t * Complex.I)) *
        Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) /
          ((ε : ℂ) - 2 * Real.pi * t * Complex.I)) := by
  set b : ℂ := (ε : ℂ) - 2 * Real.pi * t * Complex.I with hbd
  have hb : 0 < b.re := by simpa [hbd] using hε
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb (((-2 : ℝ) : ℂ) * w)
  have e1 : ∫ y, Complex.exp (-((ε * Complex.normSq y : ℝ) : ℂ)) *
        ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC =
      Fr (fun v : ℂ => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) w := by
    rw [Fr]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [ee_add]
    simp only [ee]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, Complex.normSq_eq_norm_sq, hbd]
    congr 1
    push_cast
    ring
  rw [e1, Fr_eq, h]
  simp only [Complex.finrank_real_complex]
  have e2 : (((2 : ℕ) : ℂ) / 2) = 1 := by norm_num
  rw [e2, Complex.cpow_one, norm_mul, Complex.normSq_eq_norm_sq]
  have e3 : ‖((-2 : ℝ) : ℂ)‖ = 2 := by simp
  rw [e3, ← mul_assoc]
  congr 1
  · ring
  · congr 1
    push_cast
    ring

/-- **Exact Fourier Self-Duality of the Standard Complex Gaussian**:
`Fr stdGauss z = stdGauss z` (eigenvalue `1`!). -/
theorem Fr_stdGauss (z : ℂ) : Fr stdGauss z = stdGauss z := by
  have h := complex_gauss_fourier_exact (2 * Real.pi) 0 (by positivity) z
  have hrew : Fr stdGauss z =
      ∫ y, Complex.exp (-((2 * Real.pi * Complex.normSq y : ℝ) : ℂ)) *
        ee (0 * Complex.normSq y + 2 * (conj z * y).re) ∂volC := by
    unfold Fr stdGauss
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    simp only [zero_mul, zero_add]
    rw [mul_comm]
    congr 2
    push_cast; ring
  rw [hrew, h]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have h1 : 2 * (Real.pi : ℂ) / (2 * (Real.pi : ℂ)) = 1 :=
    div_self (mul_ne_zero (by norm_num) hpi)
  have h2 : -(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq z : ℂ)) / (2 * (Real.pi : ℂ)) =
      -(2 * (Real.pi : ℂ)) * (Complex.normSq z : ℂ) := by
    field_simp [hpi]
    ring
  rw [h1, one_mul, h2]
  rfl

/-- **Exact Weil Weyl Eigenvalue of the Gaussian Vacuum**:
`realWeilOp 0 1 (-1) 0 stdGauss z = i · stdGauss z`. -/
theorem realWeilOp_weyl_stdGauss (z : ℂ) :
    realWeilOp 0 1 (-1) 0 stdGauss z = Complex.I * stdGauss z := by
  rw [realWeilOp_weyl, Fr_stdGauss]

/-- **EXACT COMPACT `SO(2)` GAUSSIAN VACUUM EIGENVALUE THEOREM (`gauss_vacuum_eigenvalue`)**:
In the concrete archimedean Schrödinger–Fock Weil representation `realWeilOp`, for EVERY rotation
`k(θ) = [[cos θ, sin θ], [-sin θ, cos θ]] ∈ SO(2) ⊂ SL₂(ℝ)`, the Gaussian vacuum `stdGauss` is an
exact eigenfunction with weight-`1` character eigenvalue `exp(i θ)`:
$$ω(k(θ))\,\varphi_0 = e^{i\theta} \cdot \varphi_0.$$ -/
theorem gauss_vacuum_eigenvalue (θ : ℝ) :
    realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) stdGauss =
      Complex.exp (Complex.I * (θ : ℂ)) • stdGauss := by
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  by_cases hs : Real.sin θ = 0
  · have hc0 : -Real.sin θ = 0 := by simp [hs]
    have hcsq : Real.cos θ ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [hs] at this
      linarith
    have hnormc : Complex.normSq ((Real.cos θ : ℂ) * z) = Complex.normSq z := by
      rw [Complex.normSq_mul, Complex.normSq_ofReal, ← sq, hcsq, one_mul]
    rw [realWeilOp, if_pos hc0, hexp, hs, mul_zero, zero_mul, ee_zero, one_mul,
      Complex.ofReal_zero, zero_mul, add_zero]
    unfold stdGauss
    rw [hnormc]
  · have hc0 : -Real.sin θ ≠ 0 := neg_ne_zero.mpr hs
    have hsinC : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [realWeilOp, if_neg hc0]
    set t : ℝ := Real.cos θ / (-Real.sin θ)
    set w : ℂ := ((-(-Real.sin θ)⁻¹ : ℝ) : ℂ) * z
    have hFr : Fr (fun u => ee (t * Complex.normSq u) * stdGauss u) w =
        (2 * Real.pi / ((2 * Real.pi : ℂ) - 2 * Real.pi * (t : ℂ) * Complex.I)) *
          Complex.exp (-(4 * Real.pi ^ 2 * (Complex.normSq w : ℂ)) /
            ((2 * Real.pi : ℂ) - 2 * Real.pi * (t : ℂ) * Complex.I)) := by
      have hG := complex_gauss_fourier_exact (2 * Real.pi) t (by positivity) w
      have hrew : Fr (fun u => ee (t * Complex.normSq u) * stdGauss u) w =
          ∫ y, Complex.exp (-((2 * Real.pi * Complex.normSq y : ℝ) : ℂ)) *
            ee (t * Complex.normSq y + 2 * (conj w * y).re) ∂volC := by
        unfold Fr stdGauss
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [ee_add]
        have heq : -((2 * Real.pi * Complex.normSq y : ℝ) : ℂ) =
            -(2 * (Real.pi : ℂ)) * (Complex.normSq y : ℂ) := by push_cast; ring
        rw [heq]
        ring
      rw [hrew, hG]
      simp [Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [hFr]
    set sC : ℂ := (Real.sin θ : ℂ)
    set cC : ℂ := (Real.cos θ : ℂ)
    have hrot_ne : sC + cC * Complex.I ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp [sC, cC] at hre
      exact hs hre
    have hden : (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I) =
        2 * (Real.pi : ℂ) * (sC + cC * Complex.I) / sC := by
      rw [eq_div_iff hsinC]
      have hsinC' : (Real.sin θ : ℂ) ≠ 0 := hsinC
      simp only [t, sC, cC, Complex.ofReal_div, Complex.ofReal_neg]
      field_simp [hsinC']
      ring
    have hw_norm : (Complex.normSq w : ℂ) = (Complex.normSq z : ℂ) / (sC ^ 2) := by
      have h1 : Complex.normSq w = (-(-Real.sin θ)⁻¹) * (-(-Real.sin θ)⁻¹) * Complex.normSq z := by
        simp only [w, Complex.normSq_mul, Complex.normSq_ofReal]
      rw [h1]
      simp only [sC, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv]
      field_simp [hsinC]
    have hsc : sC ^ 2 + cC ^ 2 = 1 := by
      change (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    have h2pi_ne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hpi
    have hden_inv : (2 * (Real.pi : ℂ)) / (2 * (Real.pi : ℂ) * (sC + cC * Complex.I) / sC) =
        sC / (sC + cC * Complex.I) := by
      rw [div_eq_iff (div_ne_zero (mul_ne_zero h2pi_ne hrot_ne) hsinC)]
      field_simp [h2pi_ne, hsinC, hrot_ne]
    have hpref : Complex.I * ((-(-Real.sin θ)⁻¹ : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) / (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I)) =
        Complex.exp (Complex.I * (θ : ℂ)) := by
      rw [hden, hden_inv, hexp]
      have hcoef : ((-(-Real.sin θ)⁻¹ : ℝ) : ℂ) = sC⁻¹ := by
        simp [sC]
      rw [hcoef, mul_assoc, inv_mul_eq_div, div_div, mul_comm (sC + cC * Complex.I) sC,
        ← div_div, div_self hsinC, one_div, mul_inv_eq_iff_eq_mul₀ hrot_ne]
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      change Complex.I = (cC + sC * Complex.I) * (sC + cC * Complex.I)
      linear_combination -Complex.I * hsc - sC * cC * hI2
    have hexponent : (2 * (Real.pi : ℂ) * Complex.I * ((Real.cos θ / (-Real.sin θ) * Complex.normSq z : ℝ) : ℂ)) +
        (-(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq w : ℂ)) /
          (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I)) =
        -(2 * (Real.pi : ℂ)) * (Complex.normSq z : ℂ) := by
      rw [hden, hw_norm]
      have hterm1 : 2 * (Real.pi : ℂ) * Complex.I * ((Real.cos θ / (-Real.sin θ) * Complex.normSq z : ℝ) : ℂ) =
          -(2 * (Real.pi : ℂ) * Complex.I * cC * (Complex.normSq z : ℂ)) / sC := by
        simp only [sC, cC, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg]
        ring
      have hterm2 : -(4 * (Real.pi : ℂ) ^ 2 * ((Complex.normSq z : ℂ) / sC ^ 2)) /
            (2 * (Real.pi : ℂ) * (sC + cC * Complex.I) / sC) =
          -(2 * (Real.pi : ℂ) * (Complex.normSq z : ℂ)) / (sC * (sC + cC * Complex.I)) := by
        rw [div_eq_iff (div_ne_zero (mul_ne_zero h2pi_ne hrot_ne) hsinC)]
        have hden2 : sC * (sC + cC * Complex.I) ≠ 0 := mul_ne_zero hsinC hrot_ne
        field_simp [hsinC, hrot_ne, h2pi_ne, hden2]
        ring
      rw [hterm1, hterm2]
      have hden2 : sC * (sC + cC * Complex.I) ≠ 0 := mul_ne_zero hsinC hrot_ne
      rw [← mul_div_mul_right _ sC hrot_ne, ← add_div, div_eq_iff hden2]
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination 2 * (Real.pi : ℂ) * (Complex.normSq z : ℂ) * hsc -
        2 * (Real.pi : ℂ) * (Complex.normSq z : ℂ) * cC ^ 2 * hI2
    calc Complex.I * ((-(-Real.sin θ)⁻¹ : ℝ) : ℂ) *
            ee (Real.cos θ / -Real.sin θ * Complex.normSq z) *
            (2 * (Real.pi : ℂ) / (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I) *
              Complex.exp (-(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq w : ℂ)) /
                (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I)))
        = (Complex.I * ((-(-Real.sin θ)⁻¹ : ℝ) : ℂ) *
            (2 * (Real.pi : ℂ) / (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I))) *
            (ee (Real.cos θ / -Real.sin θ * Complex.normSq z) *
              Complex.exp (-(4 * (Real.pi : ℂ) ^ 2 * (Complex.normSq w : ℂ)) /
                (2 * (Real.pi : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I))) := by ring
      _ = Complex.exp (Complex.I * (θ : ℂ)) * stdGauss z := by
            rw [hpref]
            congr 1
            unfold ee stdGauss
            rw [← Complex.exp_add, hexponent]

/-- **Exact `L²(ℂ, volC)` Norm-Square of the Gaussian Vacuum**: `⟨φ₀, φ₀⟩ = 1 / 2`. -/
theorem archInner_stdGauss_self : archInner stdGauss stdGauss = 1 / 2 := by
  have h := complex_gauss_fourier_exact (4 * Real.pi) 0 (by positivity) 0
  have hrew : archInner stdGauss stdGauss =
      ∫ y, Complex.exp (-((4 * Real.pi * Complex.normSq y : ℝ) : ℂ)) *
        ee (0 * Complex.normSq y + 2 * (conj (0 : ℂ) * y).re) ∂volC := by
    unfold archInner stdGauss
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [zero_mul, zero_add, map_zero, zero_mul, Complex.zero_re, mul_zero, ee_zero, mul_one,
      Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, map_ofNat]
    push_cast
    ring
  rw [hrew, h]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, map_zero,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [neg_zero, zero_div, Complex.exp_zero, mul_one]
  field_simp [hpi]
  norm_num

/-- Every complex Gaussian `y ↦ exp(-b ‖y‖²)` with `0 < b.re` is `volume`-integrable on `ℂ`. -/
theorem integrable_cexp_neg_mul_normSq {b : ℂ} (hb : 0 < b.re) :
    Integrable (fun y : ℂ => Complex.exp (-b * (Complex.normSq y : ℂ))) volume := by
  have h0 := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 (0 : ℂ)
  refine h0.congr (Eventually.of_forall fun y => ?_)
  dsimp only
  simp only [zero_mul, add_zero, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

/-- The standard Gaussian vacuum `stdGauss` belongs to `IsChirpSchwartz` (and hence
`IsArchSchwartz`). -/
theorem stdGauss_isChirpSchwartz : IsChirpSchwartz stdGauss := by
  intro t
  set f : ℂ → ℂ := fun u => ee (t * Complex.normSq u) * stdGauss u
  set b : ℂ := (2 * Real.pi : ℂ) - 2 * Real.pi * (t : ℂ) * Complex.I
  have hf_eq : f = fun u => Complex.exp (-b * (Complex.normSq u : ℂ)) := by
    funext u
    simp only [f, ee, stdGauss, b]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hb : 0 < b.re := by
    have : b.re = 2 * Real.pi := by simp [b]
    rw [this]; positivity
  refine ⟨?_, ?_, ?_⟩
  · exact (continuous_ee.comp (by fun_prop)).mul continuous_stdGauss
  · rw [hf_eq]; exact integrable_cexp_neg_mul_normSq hb
  · have hF : 𝓕 f = fun w =>
        ((2 : ℂ)⁻¹ * (2 * Real.pi / b)) *
          Complex.exp (-(Real.pi ^ 2 / b) * (Complex.normSq w : ℂ)) := by
      funext w
      have hw := complex_gauss_fourier_exact (2 * Real.pi) t (by positivity) (((-2⁻¹ : ℝ) : ℂ) * w)
      have hfr : Fr f (((-2⁻¹ : ℝ) : ℂ) * w) =
          ∫ y, Complex.exp (-((2 * Real.pi * Complex.normSq y : ℝ) : ℂ)) *
            ee (t * Complex.normSq y + 2 * (conj (((-2⁻¹ : ℝ) : ℂ) * w) * y).re) ∂volC := by
        unfold Fr f stdGauss
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [ee_add]
        have heq : -((2 * Real.pi * Complex.normSq y : ℝ) : ℂ) =
            -(2 * (Real.pi : ℂ)) * (Complex.normSq y : ℂ) := by push_cast; ring
        rw [heq]
        ring
      rw [Fr_eq f] at hfr
      have harg : ((-2 : ℝ) : ℂ) * (((-2⁻¹ : ℝ) : ℂ) * w) = w := by
        rw [← mul_assoc]; norm_num
      rw [harg] at hfr
      have hnormw : (Complex.normSq (((-2⁻¹ : ℝ) : ℂ) * w) : ℂ) = (Complex.normSq w : ℂ) / 4 := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal]
        push_cast; ring
      have hb_eq : ((2 * Real.pi : ℝ) : ℂ) - 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I = b := by
        simp [b]
      rw [← hfr, hb_eq, hnormw] at hw
      calc 𝓕 f w = (2 : ℂ)⁻¹ * (2 * 𝓕 f w) := by ring
        _ = (2 : ℂ)⁻¹ * (2 * (Real.pi : ℂ) / b *
              Complex.exp (-(4 * (Real.pi : ℂ) ^ 2 * ((Complex.normSq w : ℂ) / 4)) / b)) := by
            rw [hw]
        _ = ((2 : ℂ)⁻¹ * (2 * (Real.pi : ℂ) / b)) *
              Complex.exp (-((Real.pi : ℂ) ^ 2 / b) * (Complex.normSq w : ℂ)) := by
            rw [← mul_assoc]
            congr 2
            ring
    rw [hF]
    have hpos : 0 < ((Real.pi : ℂ) ^ 2 / b).re := by
      rw [div_eq_mul_inv, Complex.mul_re]
      have hpi2 : ((Real.pi : ℂ) ^ 2).re = Real.pi ^ 2 ∧ ((Real.pi : ℂ) ^ 2).im = 0 := by
        rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]; exact ⟨rfl, rfl⟩
      rw [hpi2.1, hpi2.2, zero_mul, sub_zero, Complex.inv_re]
      exact mul_pos (sq_pos_of_pos Real.pi_pos) (div_pos hb (Complex.normSq_pos.mpr (by
        intro h0; rw [h0, Complex.zero_re] at hb; exact lt_irrefl 0 hb)))
    exact (integrable_cexp_neg_mul_normSq hpos).const_mul _

theorem stdGauss_isArchSchwartz : IsArchSchwartz stdGauss :=
  stdGauss_isChirpSchwartz.isArchSchwartz

/-! ### Higher-Rank Hermitian Matrix Gaussian Vacuum & Concrete Bargmann–Fock Space `ArchFockModel` -/

/-- Higher-rank Hermitian matrix Gaussian vacuum on `M_{m×n}(ℂ)` (matching Alpöge's `StdUnn.gauss`). -/
def matrixGaussVacuum {m n : ℕ}
    (H s : Matrix (Fin m) (Fin m) ℂ) (l : ℝ) (Z : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ((|l| : ℝ) : ℂ) * Matrix.trace (Zᴴ * (H * s) * Z))

@[simp]
theorem matrixGaussVacuum_zero {m n : ℕ}
    (H s : Matrix (Fin m) (Fin m) ℂ) (l : ℝ) :
    matrixGaussVacuum H s l (0 : Matrix (Fin m) (Fin n) ℂ) = 1 := by
  simp [matrixGaussVacuum]

/-- **Exact Compact `U(H, s) × U(n)` Invariance of the Matrix Gaussian Vacuum**. -/
theorem matrixGaussVacuum_unitary_invariant {m n : ℕ}
    {H s h : Matrix (Fin m) (Fin m) ℂ} {k : Matrix (Fin n) (Fin n) ℂ}
    (hh : hᴴ * (H * s) * h = H * s) (hk : k * kᴴ = 1) (l : ℝ)
    (Z : Matrix (Fin m) (Fin n) ℂ) :
    matrixGaussVacuum H s l (h * Z * k) = matrixGaussVacuum H s l Z := by
  unfold matrixGaussVacuum
  congr 2
  calc Matrix.trace ((h * Z * k)ᴴ * (H * s) * (h * Z * k))
      = Matrix.trace (kᴴ * (Zᴴ * (hᴴ * (H * s) * h) * Z * k)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Zᴴ * (H * s) * Z * k) * kᴴ) := by
          rw [hh, Matrix.trace_mul_comm]
    _ = Matrix.trace (Zᴴ * (H * s) * Z * (k * kᴴ)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Zᴴ * (H * s) * Z) := by rw [hk, Matrix.mul_one]

/-- Multi-place CM Gaussian vacuum matching Alpöge's `StdUnn.gauss` across archimedean places `τ`. -/
def multiPlaceGauss {Tau : Type*} [Fintype Tau] {m n : ℕ}
    (H s : Tau → Matrix (Fin m) (Fin m) ℂ) (l : Tau → ℝ)
    (Z : Tau → Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ∑ τ : Tau, ((|l τ| : ℝ) : ℂ) *
    Matrix.trace ((Z τ)ᴴ * (H τ * s τ) * Z τ))

theorem multiPlaceGauss_eq_prod {Tau : Type*} [Fintype Tau] {m n : ℕ}
    (H s : Tau → Matrix (Fin m) (Fin m) ℂ) (l : Tau → ℝ)
    (Z : Tau → Matrix (Fin m) (Fin n) ℂ) :
    multiPlaceGauss H s l Z = ∏ τ : Tau, matrixGaussVacuum (H τ) (s τ) (l τ) (Z τ) := by
  unfold multiPlaceGauss matrixGaussVacuum
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 1
  ring

/-- Evaluation of a polynomial in holomorphic/anti-holomorphic matrix coordinates `(Z_{ij}, Z̄_{ij})`. -/
def evalHermPoly {m n : ℕ} (p : MvPolynomial (Fin m × Fin n × Bool) ℂ)
    (Z : Matrix (Fin m) (Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (fun k => if k.2.2 then conj (Z k.1 k.2.1) else Z k.1 k.2.1) p

/-- Archimedean polynomial-times-Gaussian Fock submodule `ArchFockSubmodule H s l` on `M_{m×n}(ℂ)`
(matching Alpöge's `StdUnn.fockA`). -/
def ArchFockSubmodule {m n : ℕ}
    (H s : Matrix (Fin m) (Fin m) ℂ) (l : ℝ) :
    Submodule ℂ (Matrix (Fin m) (Fin n) ℂ → ℂ) :=
  Submodule.span ℂ {φ | ∃ p : MvPolynomial (Fin m × Fin n × Bool) ℂ,
    φ = fun Z => evalHermPoly p Z * matrixGaussVacuum H s l Z}

theorem matrixGaussVacuum_mem_archFockSubmodule {m n : ℕ}
    (H s : Matrix (Fin m) (Fin m) ℂ) (l : ℝ) :
    matrixGaussVacuum (n := n) H s l ∈ ArchFockSubmodule (n := n) H s l := by
  refine Submodule.subset_span ⟨1, ?_⟩
  funext Z
  simp [evalHermPoly]

/-- Multi-index factorial `α! = ∏_i (α i)!` (matching Alpöge's `VacuumFockVectors.multiFact`). -/
def multiFact {ι : Type*} (α : ι →₀ ℕ) : ℕ :=
  α.prod fun _ k => k.factorial

@[simp]
theorem multiFact_zero {ι : Type*} : multiFact (0 : ι →₀ ℕ) = 1 := by
  simp [multiFact]

theorem multiFact_pos {ι : Type*} (α : ι →₀ ℕ) : 0 < multiFact α := by
  unfold multiFact
  exact Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem multiFact_single {ι : Type*} (i : ι) (k : ℕ) :
    multiFact (Finsupp.single i k) = k.factorial := by
  unfold multiFact
  rw [Finsupp.prod_single_index (by simp)]

theorem multiFact_add_single {ι : Type*} [DecidableEq ι] (α : ι →₀ ℕ) (i : ι) :
    multiFact (α + (Finsupp.single i 1 : ι →₀ ℕ)) = (α i + 1) * multiFact α := by
  set β : ι →₀ ℕ := α + Finsupp.single i 1
  have hsub : β.support ⊆ insert i α.support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj
    by_cases hji : j = i
    · subst hji; exact Finset.mem_insert_self _ _
    · have h0 : β j = α j := by
        simp only [β, Finsupp.add_apply, Finsupp.single_eq_of_ne hji, add_zero]
      rw [h0] at hj
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hj)
  have h1 : multiFact β = ∏ j ∈ insert i α.support, (β j).factorial := by
    unfold multiFact Finsupp.prod
    exact Finset.prod_subset hsub fun j _ hj => by
      dsimp only
      rw [Finsupp.notMem_support_iff.mp hj, Nat.factorial_zero]
  have h2 : multiFact α = ∏ j ∈ insert i α.support, (α j).factorial := by
    unfold multiFact Finsupp.prod
    exact Finset.prod_subset (Finset.subset_insert i _) fun j _ hj => by
      dsimp only
      rw [Finsupp.notMem_support_iff.mp hj, Nat.factorial_zero]
  rw [h1, h2]
  by_cases hi : i ∈ α.support
  · have hL : ∏ j ∈ α.support, (β j).factorial =
        (β i).factorial * ∏ j ∈ α.support.erase i, (β j).factorial :=
      (Finset.mul_prod_erase α.support (fun j => (β j).factorial) hi).symm
    have hR : ∏ j ∈ α.support, (α j).factorial =
        (α i).factorial * ∏ j ∈ α.support.erase i, (α j).factorial :=
      (Finset.mul_prod_erase α.support (fun j => (α j).factorial) hi).symm
    rw [Finset.insert_eq_of_mem hi, hL, hR]
    have hbi : β i = α i + 1 := by simp [β]
    rw [hbi, Nat.factorial_succ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [β, Finsupp.single_eq_of_ne hji]
  · rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have h0 : α i = 0 := Finsupp.notMem_support_iff.mp hi
    have hbi : β i = 1 := by simp [β, h0]
    rw [hbi, h0, Nat.factorial_zero, Nat.factorial_one, zero_add, one_mul, one_mul, one_mul]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [β, Finsupp.single_eq_of_ne hji]

/-- Elementary multivariate polynomial vanishing over `ℂ`: if `P ∈ ℂ[X₁, …, X_d]` evaluates to `0`
at all points `z : Fin d → ℂ`, then `P = 0`. -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero :
    ∀ {d : ℕ} (P : MvPolynomial (Fin d) ℂ),
      (∀ z : Fin d → ℂ, MvPolynomial.eval z P = 0) → P = 0
  | 0, P, hP => by
    ext m
    have hm : m = 0 := Finsupp.ext fun i => Fin.elim0 i
    subst hm
    rw [MvPolynomial.coeff_zero]
    have hev := hP Fin.elim0
    rw [MvPolynomial.eval_eq'] at hev
    by_cases h0 : (0 : Fin 0 →₀ ℕ) ∈ P.support
    · rw [Finset.sum_eq_single 0] at hev
      · simpa using hev
      · intro b _ hb
        exfalso; exact hb (Finsupp.ext fun i => Fin.elim0 i)
      · intro hnot; exact absurd h0 hnot
    · exact MvPolynomial.notMem_support_iff.mp h0
  | d + 1, P, hP => by
    apply (MvPolynomial.finSuccEquiv ℂ d).injective
    rw [map_zero]
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    refine mvPolynomial_eq_zero_of_eval_eq_zero _ fun w => ?_
    let q : Polynomial ℂ := (MvPolynomial.finSuccEquiv ℂ d P).map (MvPolynomial.eval w)
    have hq_root : ∀ x : ℂ, Polynomial.eval x q = 0 := by
      intro x
      have hev := MvPolynomial.eval_eq_eval_mv_eval' w x P
      have h0 := hP (Fin.cons x w)
      rw [hev] at h0
      simpa [q] using h0
    have hq0 : q = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset q.roots.toFinset
      have hmem : x ∈ q.roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
        exact hq_root x
      exact hx hmem
    have hck := congrArg (fun r : Polynomial ℂ => r.coeff k) hq0
    simpa [q, Polynomial.coeff_map] using hck

/-- **Concrete Bargmann–Fock Space `ArchFockModel d`** in `d` complex bosonic modes:
polynomial space `MvPolynomial (Fin d) ℂ` realized inside `L²(ℂ^d, e^{-2π α ‖z‖²})` via
`P ↦ (z ↦ P(z) * ∏_i archGauss α (z_i))`, equipped with creation operators `creOp i = z_i ·`,
annihilation operators `annOp i = ∂/∂z_i`, number operator `numOp`, and exact Bargmann–Fock
Hermitian inner product `fockInner`! -/
structure ArchFockModel (d : ℕ) where
  scale : ℝ
  scale_pos : 0 < scale

namespace ArchFockModel

abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℂ

/-- Gaussian vacuum vector `φ₀(z) = ∏_{i : Fin d} exp(-2π α |z_i|²)` on `ℂ^d`. -/
def vacuum {d : ℕ} (F : ArchFockModel d) (z : Fin d → ℂ) : ℂ :=
  ∏ i : Fin d, archGauss F.scale (z i)

@[simp]
theorem vacuum_zero {d : ℕ} (F : ArchFockModel d) :
    F.vacuum 0 = 1 := by
  simp [vacuum, archGauss]

theorem vacuum_ne_zero {d : ℕ} (F : ArchFockModel d) (z : Fin d → ℂ) :
    F.vacuum z ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Complex.exp_ne_zero _

/-- Canonical Bargmann–Fock → Schrödinger embedding `P ↦ (z ↦ P(z) * vacuum(z))`. -/
def toSchrodinger {d : ℕ} (F : ArchFockModel d) :
    Poly d →ₗ[ℂ] ((Fin d → ℂ) → ℂ) where
  toFun P z := MvPolynomial.eval z P * F.vacuum z
  map_add' P Q := by funext z; simp [add_mul]
  map_smul' c P := by funext z; simp [mul_assoc]

@[simp]
theorem toSchrodinger_one {d : ℕ} (F : ArchFockModel d) :
    F.toSchrodinger 1 = F.vacuum := by
  funext z; simp [toSchrodinger]

/-- Bosonic creation operator `a_i† : P ↦ X_i * P`. -/
def creOp {d : ℕ} (i : Fin d) : Module.End ℂ (Poly d) where
  toFun P := MvPolynomial.X i * P
  map_add' P Q := mul_add _ _ _
  map_smul' c P := by
    simp only [RingHom.id_apply, Algebra.mul_smul_comm]

/-- Bosonic annihilation operator `a_i : P ↦ ∂P / ∂X_i`. -/
def annOp {d : ℕ} (i : Fin d) : Module.End ℂ (Poly d) :=
  (MvPolynomial.pderiv i).toLinearMap

/-- Bosonic number (harmonic oscillator Hamiltonian) operator `N = ∑_i a_i† a_i`. -/
def numOp (d : ℕ) : Module.End ℂ (Poly d) :=
  ∑ i : Fin d, creOp i ∘ₗ annOp i

/-- Exact Bargmann–Fock Hermitian inner product
`⟨P, Q⟩_Fock = ∑_α conj(coeff α P) * coeff α Q * α!` (conjugate-linear in `P`, linear in `Q`). -/
def fockInner {d : ℕ} (P Q : Poly d) : ℂ :=
  ∑ α ∈ P.support ∩ Q.support, star (MvPolynomial.coeff α P) * MvPolynomial.coeff α Q *
    (multiFact α : ℂ)

theorem fockInner_eq_sum_of_subset {d : ℕ} (P Q : Poly d) (s : Finset (Fin d →₀ ℕ))
    (hs : P.support ∩ Q.support ⊆ s) :
    fockInner P Q =
      ∑ α ∈ s, star (MvPolynomial.coeff α P) * MvPolynomial.coeff α Q * (multiFact α : ℂ) := by
  unfold fockInner
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [Finset.mem_inter, not_and_or, MvPolynomial.notMem_support_iff,
    MvPolynomial.notMem_support_iff] at hα
  rcases hα with hP | hQ
  · simp [hP]
  · simp [hQ]

/-- **Creation operators commute**: `[a_i†, a_j†] = 0`. -/
theorem cre_comm {d : ℕ} (i j : Fin d) (P : Poly d) :
    creOp i (creOp j P) = creOp j (creOp i P) := by
  simp only [creOp, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- **Vacuum annihilation**: `a_i |0⟩ = 0` (`annOp i 1 = 0`). -/
@[simp]
theorem ann_vacuum {d : ℕ} (i : Fin d) :
    annOp i (1 : Poly d) = 0 := by
  change MvPolynomial.pderiv i (1 : Poly d) = 0
  simp

theorem coeff_creOp {d : ℕ} (i : Fin d) (P : Poly d) (α : Fin d →₀ ℕ) :
    MvPolynomial.coeff α (creOp i P) =
      if 1 ≤ α i then MvPolynomial.coeff (α - (Finsupp.single i 1 : Fin d →₀ ℕ)) P else 0 := by
  change MvPolynomial.coeff α (MvPolynomial.X i * P) = _
  rw [mul_comm, MvPolynomial.coeff_mul_X']
  have hiff : i ∈ α.support ↔ 1 ≤ α i := by
    rw [Finsupp.mem_support_iff]; omega
  simp only [hiff]

theorem coeff_annOp {d : ℕ} (i : Fin d) (P : Poly d) (α : Fin d →₀ ℕ) :
    MvPolynomial.coeff α (annOp i P) =
      ((α i + 1 : ℕ) : ℂ) * MvPolynomial.coeff (α + (Finsupp.single i 1 : Fin d →₀ ℕ)) P := by
  change MvPolynomial.coeff α (MvPolynomial.pderiv i P) = _
  rw [MvPolynomial.coeff_pderiv]
  push_cast
  ring

/-- **Exact Bosonic Canonical Commutation Relation (CCR)** (fast `O(1)` coefficient proof):
`[a_i, a_j†] = a_i a_j† - a_j† a_i = δ_{ij} · id`! -/
theorem fock_ccr {d : ℕ} (i j : Fin d) (P : Poly d) :
    annOp i (creOp j P) - creOp j (annOp i P) = if i = j then P else 0 := by
  ext α
  rw [MvPolynomial.coeff_sub, coeff_annOp, coeff_creOp, coeff_creOp]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have h1 : 1 ≤ (α + (Finsupp.single i 1 : Fin d →₀ ℕ)) i := by simp
    have hsub : α + (Finsupp.single i 1 : Fin d →₀ ℕ) - Finsupp.single i 1 = α := by
      ext k; simp only [Finsupp.tsub_apply, Finsupp.add_apply]; omega
    rw [if_pos h1, hsub]
    by_cases hα : 1 ≤ α i
    · rw [if_pos hα, coeff_annOp]
      have hre : α - (Finsupp.single i 1 : Fin d →₀ ℕ) + Finsupp.single i 1 = α := by
        ext k; simp only [Finsupp.add_apply, Finsupp.tsub_apply]
        by_cases hki : k = i
        · subst hki; simp only [Finsupp.single_eq_same]; omega
        · simp [Finsupp.single_eq_of_ne hki]
      have hval : ((α - (Finsupp.single i 1 : Fin d →₀ ℕ)) i + 1 : ℕ) = α i := by
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
      rw [hre, hval]
      push_cast; ring
    · have h0 : α i = 0 := by omega
      rw [if_neg hα, h0]
      simp
  · rw [if_neg hij, MvPolynomial.coeff_zero]
    have hval_j : (α + (Finsupp.single i 1 : Fin d →₀ ℕ)) j = α j := by
      simp [Finsupp.single_eq_of_ne (Ne.symm hij)]
    rw [hval_j]
    by_cases hα : 1 ≤ α j
    · rw [if_pos hα, if_pos hα, coeff_annOp]
      have hcomm : α + (Finsupp.single i 1 : Fin d →₀ ℕ) - Finsupp.single j 1 =
          α - Finsupp.single j 1 + Finsupp.single i 1 := by
        ext k; simp only [Finsupp.add_apply, Finsupp.tsub_apply]
        by_cases hkj : k = j
        · subst hkj
          have hkj' : k ≠ i := Ne.symm hij
          simp only [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hkj']; omega
        · simp only [Finsupp.single_eq_of_ne hkj]; omega
      have hval_i : (α - (Finsupp.single j 1 : Fin d →₀ ℕ)) i = α i := by
        simp [Finsupp.single_eq_of_ne hij]
      rw [hcomm, hval_i, sub_self]
    · rw [if_neg hα, if_neg hα, mul_zero, sub_self]

/-- **Exact Bargmann–Fock Adjointness**: `⟨a_i† P, Q⟩_Fock = ⟨P, a_i Q⟩_Fock`! -/
theorem cre_adjoint_ann {d : ℕ} (i : Fin d) (P Q : Poly d) :
    fockInner (creOp i P) Q = fockInner P (annOp i Q) := by
  set e : Fin d →₀ ℕ := Finsupp.single i 1
  set S : Finset (Fin d →₀ ℕ) :=
    P.support ∪ (annOp i Q).support ∪ (Q.support.image (fun β => β - e))
  have hL : fockInner (creOp i P) Q =
      ∑ β ∈ S.image (fun α => α + e),
        star (MvPolynomial.coeff β (creOp i P)) * MvPolynomial.coeff β Q * (multiFact β : ℂ) := by
    refine fockInner_eq_sum_of_subset _ _ _ fun β hβ => ?_
    rw [Finset.mem_inter, MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff] at hβ
    rw [coeff_creOp] at hβ
    have h1 : 1 ≤ β i := by
      by_contra hlt
      rw [if_neg hlt] at hβ
      exact hβ.1 rfl
    rw [Finset.mem_image]
    refine ⟨β - e, ?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨β, MvPolynomial.mem_support_iff.mpr hβ.2, rfl⟩)
    · ext j
      simp only [e, Finsupp.add_apply, Finsupp.tsub_apply]
      by_cases hji : j = i
      · subst hji; simp only [Finsupp.single_eq_same]; omega
      · simp [Finsupp.single_eq_of_ne hji]
  have hR : fockInner P (annOp i Q) =
      ∑ α ∈ S, star (MvPolynomial.coeff α P) * MvPolynomial.coeff α (annOp i Q) *
        (multiFact α : ℂ) :=
    fockInner_eq_sum_of_subset _ _ _ fun α hα =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mp hα).1)
  rw [hL, hR, Finset.sum_image (fun α₁ _ α₂ _ h => add_right_cancel h)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_creOp, coeff_annOp, multiFact_add_single]
  have h1 : 1 ≤ (α + e) i := by simp [e]
  have hsub : α + e - e = α := by
    ext j; simp only [e, Finsupp.tsub_apply, Finsupp.add_apply]; omega
  rw [if_pos h1, hsub]
  push_cast
  ring

/-- **Exact Bargmann–Fock Monomial Orthogonality**: `⟨z^α, z^β⟩_Fock = if α = β then α! else 0`! -/
theorem fock_monomial_orthogonal {d : ℕ} (α β : Fin d →₀ ℕ) :
    fockInner (MvPolynomial.monomial α (1 : ℂ)) (MvPolynomial.monomial β 1) =
      if α = β then (multiFact α : ℂ) else 0 := by
  have hsupp : ∀ γ : Fin d →₀ ℕ, (MvPolynomial.monomial γ (1 : ℂ)).support = {γ} := fun γ => by
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero]
  unfold fockInner
  rw [hsupp α, hsupp β]
  by_cases h : α = β
  · subst h
    simp [MvPolynomial.coeff_monomial]
  · have hdisj : ({α} : Finset (Fin d →₀ ℕ)) ∩ {β} = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, rfl⟩; exact h rfl
    rw [hdisj, if_neg h, Finset.sum_empty]

theorem fockInner_self_eq_sum {d : ℕ} (P : Poly d) :
    fockInner P P =
      ((∑ α ∈ P.support, ‖MvPolynomial.coeff α P‖ ^ 2 * (multiFact α : ℝ) : ℝ) : ℂ) := by
  unfold fockInner
  rw [Finset.inter_self, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]

/-- **Positive Definiteness of the Bargmann–Fock Inner Product**. -/
theorem fockInner_pos_def {d : ℕ} (P : Poly d) :
    0 ≤ (fockInner P P).re ∧ (fockInner P P).im = 0 ∧ (fockInner P P = 0 ↔ P = 0) := by
  rw [fockInner_self_eq_sum, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_eq_zero]
  refine ⟨Finset.sum_nonneg fun α _ => mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _), rfl, ?_⟩
  constructor
  · intro hsum
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun α _ =>
      mul_nonneg (sq_nonneg ‖MvPolynomial.coeff α P‖) (Nat.cast_nonneg (multiFact α))).mp hsum
    ext α
    by_cases hα : α ∈ P.support
    · have h0 := hall α hα
      have hm : (multiFact α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (multiFact_pos α).ne'
      have hn : ‖MvPolynomial.coeff α P‖ ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_right hm
      simpa using norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    · simpa using MvPolynomial.notMem_support_iff.mp hα
  · rintro rfl; simp

/-- **Exact Harmonic Oscillator Eigenvalues**: `N (z^α) = |α| · z^α`. -/
theorem numOp_monomial {d : ℕ} (α : Fin d →₀ ℕ) :
    numOp d (MvPolynomial.monomial α (1 : ℂ)) =
      ((∑ i : Fin d, α i : ℕ) : ℂ) • MvPolynomial.monomial α (1 : ℂ) := by
  ext β
  simp only [numOp, LinearMap.sum_apply, LinearMap.comp_apply, MvPolynomial.coeff_sum,
    coeff_creOp, coeff_annOp, MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_monomial]
  by_cases hβα : α = β
  · subst hβα
    rw [if_pos rfl, mul_one, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set e : Fin d →₀ ℕ := Finsupp.single i 1
    by_cases hi : 1 ≤ α i
    · have hsub : α - e + e = α := by
        ext j; simp only [e, Finsupp.add_apply, Finsupp.tsub_apply]
        by_cases hji : j = i
        · subst hji; simp only [Finsupp.single_eq_same]; omega
        · simp [Finsupp.single_eq_of_ne hji]
      have hval : (α - e) i + 1 = α i := by
        simp only [e, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
      rw [if_pos hi, hsub, if_pos rfl, mul_one, hval]
    · have h0 : α i = 0 := by omega
      rw [if_neg hi, h0, Nat.cast_zero]
  · rw [if_neg hβα, mul_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    set e : Fin d →₀ ℕ := Finsupp.single i 1
    by_cases hi : 1 ≤ β i
    · have hsub : β - e + e = β := by
        ext j; simp only [e, Finsupp.add_apply, Finsupp.tsub_apply]
        by_cases hji : j = i
        · subst hji; simp only [Finsupp.single_eq_same]; omega
        · simp [Finsupp.single_eq_of_ne hji]
      rw [if_pos hi, hsub, if_neg hβα, mul_zero]
    · rw [if_neg hi]

/-- **Exact Orthogonal Vacuum Projection in `ArchFockModel`**: `⟨1, P⟩_Fock = coeff 0 P`. -/
theorem fock_vacuum_projection_eq {d : ℕ} (P : Poly d) :
    fockInner (1 : Poly d) P = MvPolynomial.coeff 0 P := by
  have h1 : (1 : Poly d) = MvPolynomial.monomial 0 (1 : ℂ) := by simp
  rw [h1]
  have hsub : (MvPolynomial.monomial 0 (1 : ℂ)).support ∩ P.support ⊆ {0} := by
    intro α hα
    have h0 := (Finset.mem_inter.mp hα).1
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero] at h0
    exact h0
  rw [fockInner_eq_sum_of_subset _ _ {0} hsub]
  simp

/-- Injectivity of the Bargmann–Fock → Schrödinger embedding `F.toSchrodinger`. -/
theorem toSchrodinger_injective {d : ℕ} (F : ArchFockModel d) :
    Function.Injective F.toSchrodinger := by
  intro P Q hPQ
  have hzero : ∀ z : Fin d → ℂ, MvPolynomial.eval z (P - Q) = 0 := fun z => by
    rw [map_sub, sub_eq_zero]
    exact mul_right_cancel₀ (F.vacuum_ne_zero z) (congrFun hPQ z)
  exact sub_eq_zero.mp (mvPolynomial_eq_zero_of_eval_eq_zero (P - Q) hzero)

end ArchFockModel

end BargmannFockAndGaussianVacuum

/-! ## Section 3: Non-Archimedean `p`-Adic Schrödinger Model & Exact Local Plancherel Unitarity -/

section PadicSchrodinger

variable (p : ℕ) [hp : Fact p.Prime]

private lemma padic_p_pos' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
private lemma padic_one_lt_p' : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.one_lt
private lemma padic_p_complex_ne_zero' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- Concrete `ℂ`-submodule `PadicSB p` of Schwartz–Bruhat functions on `ℚ_[p]`. -/
def PadicSB : Submodule ℂ (ℚ_[p] → ℂ) where
  carrier := {f | IsPadicSchwartzBruhat p f}
  add_mem' hf hg := isPadicSchwartzBruhat_add p hf hg
  zero_mem' := ⟨0, 0, le_rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' c _ hf := isPadicSchwartzBruhat_smul p c hf

/-- Standard spherical vector `1_{ℤ_p}` inside `PadicSB p`. -/
def padicSpherical : PadicSB p :=
  ⟨ballInd p 0 0, isPadicSchwartzBruhat_ballInd p 0 0⟩

theorem isPadicSchwartzBruhat_conj {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) :
    IsPadicSchwartzBruhat p (fun x => star (f x)) := by
  rcases hf with ⟨R, N, hRN, hsupp, hloc⟩
  exact ⟨R, N, hRN, fun x hx => by dsimp only; rw [hsupp x hx, star_zero],
    fun x y hxy => by dsimp only; rw [hloc x y hxy]⟩

theorem isPadicSchwartzBruhat_mul {f g : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) (hg : IsPadicSchwartzBruhat p g) :
    IsPadicSchwartzBruhat p (fun x => f x * g x) := by
  rcases hf with ⟨R₁, N₁, hf₁⟩
  rcases hg with ⟨R₂, N₂, hg₂⟩
  let R := min R₁ R₂
  let N := max N₁ N₂
  have hf' : IsPadicSBAt p R N f :=
    isPadicSBAt_mono p hf₁ (min_le_left R₁ R₂) (le_max_left N₁ N₂)
  have hg' : IsPadicSBAt p R N g :=
    isPadicSBAt_mono p hg₂ (min_le_right R₁ R₂) (le_max_right N₁ N₂)
  exact ⟨R, N, hf'.1,
    fun x hx => by simp [hf'.2.1 x hx],
    fun x y hxy => by simp [hf'.2.2 x y hxy, hg'.2.2 x y hxy]⟩

theorem isPadicSchwartzBruhat_mul_left {a : ℚ_[p]} (ha : a ≠ 0) {f : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) :
    IsPadicSchwartzBruhat p (fun x => f (a * x)) := by
  rcases hf with ⟨R, N, hRN, hsupp, hloc⟩
  refine ⟨R - a.valuation, N - a.valuation, by omega, ?_, ?_⟩
  · intro x hx
    apply hsupp
    rw [norm_mul, Padic.norm_eq_zpow_neg_valuation ha]
    have hpos : 0 < (p : ℝ) ^ (-a.valuation) := zpow_pos (padic_p_pos' p) _
    calc (p : ℝ) ^ (-R)
        = (p : ℝ) ^ (-a.valuation) * (p : ℝ) ^ (-(R - a.valuation)) := by
            rw [← zpow_add₀ (padic_p_pos' p).ne']; congr 1; omega
      _ < (p : ℝ) ^ (-a.valuation) * ‖x‖ := mul_lt_mul_of_pos_left hx hpos
  · intro x y hxy
    apply hloc
    rw [← mul_sub, norm_mul, Padic.norm_eq_zpow_neg_valuation ha]
    have hnn : 0 ≤ (p : ℝ) ^ (-a.valuation) := (zpow_pos (padic_p_pos' p) _).le
    calc (p : ℝ) ^ (-a.valuation) * ‖x - y‖
        ≤ (p : ℝ) ^ (-a.valuation) * (p : ℝ) ^ (-(N - a.valuation)) :=
          mul_le_mul_of_nonneg_left hxy hnn
      _ = (p : ℝ) ^ (-N) := by
          rw [← zpow_add₀ (padic_p_pos' p).ne']; congr 1; omega

theorem ballInd_mul_left {a : ℚ_[p]} (ha : a ≠ 0) (b : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    ballInd p b k (a * x) = ballInd p (a⁻¹ * b) (k - a.valuation) x := by
  unfold ballInd
  have hiff : ‖a * x - b‖ ≤ (p : ℝ) ^ (-k) ↔ ‖x - a⁻¹ * b‖ ≤ (p : ℝ) ^ (-(k - a.valuation)) := by
    have hfac : a * x - b = a * (x - a⁻¹ * b) := by
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    rw [hfac, norm_mul, Padic.norm_eq_zpow_neg_valuation ha]
    have hpos : 0 < (p : ℝ) ^ (-a.valuation) := zpow_pos (padic_p_pos' p) _
    have hpow : (p : ℝ) ^ (-k) = (p : ℝ) ^ (-a.valuation) * (p : ℝ) ^ (-(k - a.valuation)) := by
      rw [← zpow_add₀ (padic_p_pos' p).ne']; congr 1; omega
    rw [hpow, mul_le_mul_iff_right₀ hpos]
  simp only [hiff]

/-- **Exact `p`-Adic Haar Scaling Law**: `∫_{ℚ_p} f(a x) dx = |a|_p⁻¹ · ∫_{ℚ_p} f(x) dx`. -/
theorem padicHaarInt_mul_left {a : ℚ_[p]} (ha : a ≠ 0) {f : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) :
    padicHaarInt p (fun x => f (a * x)) = ((‖a‖⁻¹ : ℝ) : ℂ) * padicHaarInt p f := by
  rcases hf with ⟨R, N, hRN⟩
  have hrew : (fun x => f (a * x)) =
      fun x => ∑ j : Fin (p ^ (N - R).toNat),
        f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
          ballInd p (a⁻¹ * ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))) (N - a.valuation) x := by
    funext x
    rw [isPadicSBAt_eq_sum_ballInd p hRN (a * x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ballInd_mul_left p ha]
  have hrew0 : f = fun x => ∑ j : Fin (p ^ (N - R).toNat),
      f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) *
        ballInd p ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) N x :=
    funext (isPadicSBAt_eq_sum_ballInd p hRN)
  rw [hrew, padicHaarInt_finset_sum p _ _ fun j _ =>
    isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_ballInd p _ _)]
  conv_rhs => rw [hrew0, padicHaarInt_finset_sum p _ _ fun j _ =>
    isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_ballInd p _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [padicHaarInt_smul p _ (isPadicSchwartzBruhat_ballInd p _ _),
    padicHaarInt_smul p _ (isPadicSchwartzBruhat_ballInd p _ _),
    padicHaarInt_ballInd p _ _, padicHaarInt_ballInd p _ _,
    Padic.norm_eq_zpow_neg_valuation ha, ← _root_.zpow_neg, neg_neg,
    Complex.ofReal_zpow, Complex.ofReal_natCast]
  have hpow : (p : ℂ) ^ (-(N - a.valuation)) = (p : ℂ) ^ a.valuation * (p : ℂ) ^ (-N) := by
    rw [← zpow_add₀ (padic_p_complex_ne_zero' p)]; congr 1; omega
  rw [hpow]
  ring

/-- Concrete `p`-adic `L²` Hermitian inner product on `ℚ_[p]`. -/
def padicInner (f g : ℚ_[p] → ℂ) : ℂ :=
  padicHaarInt p (fun x => star (f x) * g x)

theorem padicInner_conj_symm {f g : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) (hg : IsPadicSchwartzBruhat p g) :
    star (padicInner p f g) = padicInner p g f := by
  have hfg : IsPadicSchwartzBruhat p (fun x => star (f x) * g x) :=
    isPadicSchwartzBruhat_mul p (isPadicSchwartzBruhat_conj p hf) hg
  have hgf : IsPadicSchwartzBruhat p (fun x => star (g x) * f x) :=
    isPadicSchwartzBruhat_mul p (isPadicSchwartzBruhat_conj p hg) hf
  rcases hfg with ⟨R₁, N₁, h1⟩
  rcases hgf with ⟨R₂, N₂, h2⟩
  let R := min R₁ R₂
  let N := max N₁ N₂
  have h1' : IsPadicSBAt p R N (fun x => star (f x) * g x) :=
    isPadicSBAt_mono p h1 (min_le_left R₁ R₂) (le_max_left N₁ N₂)
  have h2' : IsPadicSBAt p R N (fun x => star (g x) * f x) :=
    isPadicSBAt_mono p h2 (min_le_right R₁ R₂) (le_max_right N₁ N₂)
  unfold padicInner
  rw [padicHaarInt_eq_padicIntAt p h1', padicHaarInt_eq_padicIntAt p h2']
  unfold padicIntAt
  have hpstar : star ((p : ℂ) ^ (-N)) = (p : ℂ) ^ (-N) := by
    rw [Complex.star_def, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, Complex.conj_ofReal]
  rw [star_mul, hpstar, star_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [star_mul, star_star, mul_comm]

theorem padicInner_self_re_nonneg {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) :
    0 ≤ (padicInner p f f).re ∧ (padicInner p f f).im = 0 := by
  have hff : IsPadicSchwartzBruhat p (fun x => star (f x) * f x) :=
    isPadicSchwartzBruhat_mul p (isPadicSchwartzBruhat_conj p hf) hf
  rcases hff with ⟨R, N, hRN⟩
  unfold padicInner
  rw [padicHaarInt_eq_padicIntAt p hRN]
  unfold padicIntAt
  have heq : (p : ℂ) ^ (-N) * ∑ j : Fin (p ^ (N - R).toNat),
        star (f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))) * f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) =
      (((p : ℝ) ^ (-N) * ∑ j : Fin (p ^ (N - R).toNat),
        ‖f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  rw [heq, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨mul_nonneg (zpow_nonneg (padic_p_pos' p).le _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _), rfl⟩

theorem padicInner_self_eq_zero_iff {f : ℚ_[p] → ℂ} (hf : IsPadicSchwartzBruhat p f) :
    padicInner p f f = 0 ↔ f = 0 := by
  constructor
  · intro h0
    rcases hf with ⟨R, N, hRN⟩
    have hff : IsPadicSBAt p R N (fun x => star (f x) * f x) :=
      ⟨hRN.1, fun x hx => by simp [hRN.2.1 x hx],
       fun x y hxy => by simp [hRN.2.2 x y hxy]⟩
    unfold padicInner at h0
    rw [padicHaarInt_eq_padicIntAt p hff] at h0
    unfold padicIntAt at h0
    have hsum0 : ∑ j : Fin (p ^ (N - R).toNat),
        ‖f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))‖ ^ 2 = 0 := by
      have hpne : (p : ℂ) ^ (-N) ≠ 0 := zpow_ne_zero _ (padic_p_complex_ne_zero' p)
      have hs := (mul_eq_zero.mp h0).resolve_left hpne
      have hcast : ∑ j : Fin (p ^ (N - R).toNat),
          star (f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))) * f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) =
          ((∑ j : Fin (p ^ (N - R).toNat),
            ‖f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p]))‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.star_def, Complex.conj_mul']
      rw [hcast, Complex.ofReal_eq_zero] at hs
      exact hs
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hsum0
    funext x
    rw [isPadicSBAt_eq_sum_ballInd p hRN x]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : f ((p : ℚ_[p]) ^ R * (j.1 : ℚ_[p])) = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp (hall j (Finset.mem_univ j)))
    rw [hj, zero_mul]
  · rintro rfl
    unfold padicInner
    simpa using padicHaarInt_zero p

theorem ballInd_mul_ballInd (a₁ a₂ : ℚ_[p]) (k₁ k₂ : ℤ) (x : ℚ_[p]) :
    ballInd p a₁ k₁ x * ballInd p a₂ k₂ x =
      if ‖a₂ - a₁‖ ≤ (p : ℝ) ^ (-min k₁ k₂) then
        ballInd p (if k₁ ≤ k₂ then a₂ else a₁) (max k₁ k₂) x
      else 0 := by
  by_cases hab : ‖a₂ - a₁‖ ≤ (p : ℝ) ^ (-min k₁ k₂)
  · rw [if_pos hab]
    by_cases hk : k₁ ≤ k₂
    · rw [if_pos hk, max_eq_right hk]
      rw [min_eq_left hk] at hab
      by_cases hx2 : ‖x - a₂‖ ≤ (p : ℝ) ^ (-k₂)
      · have hx1 : ‖x - a₁‖ ≤ (p : ℝ) ^ (-k₁) := by
          have hle : (p : ℝ) ^ (-k₂) ≤ (p : ℝ) ^ (-k₁) :=
            zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
          have hsub : x - a₁ = (x - a₂) + (a₂ - a₁) := by ring
          rw [hsub]
          exact (Padic.nonarchimedean _ _).trans (max_le (hx2.trans hle) hab)
        rw [(ballInd_eq_one_iff p _ _ _).mpr hx1, (ballInd_eq_one_iff p _ _ _).mpr hx2, mul_one]
      · push Not at hx2
        rw [(ballInd_eq_zero_iff p _ _ _).mpr hx2, mul_zero]
    · push Not at hk
      rw [if_neg (not_le_of_gt hk), max_eq_left hk.le]
      rw [min_eq_right hk.le] at hab
      by_cases hx1 : ‖x - a₁‖ ≤ (p : ℝ) ^ (-k₁)
      · have hx2 : ‖x - a₂‖ ≤ (p : ℝ) ^ (-k₂) := by
          have hle : (p : ℝ) ^ (-k₁) ≤ (p : ℝ) ^ (-k₂) :=
            zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
          have hsub : x - a₂ = (x - a₁) + -(a₂ - a₁) := by ring
          rw [hsub]
          refine (Padic.nonarchimedean _ _).trans (max_le (hx1.trans hle) ?_)
          rwa [norm_neg]
        rw [(ballInd_eq_one_iff p _ _ _).mpr hx1, (ballInd_eq_one_iff p _ _ _).mpr hx2, mul_one]
      · push Not at hx1
        rw [(ballInd_eq_zero_iff p _ _ _).mpr hx1, zero_mul]
  · rw [if_neg hab]
    push Not at hab
    by_cases hx1 : ‖x - a₁‖ ≤ (p : ℝ) ^ (-k₁)
    · have hx2 : (p : ℝ) ^ (-k₂) < ‖x - a₂‖ := by
        by_contra hle
        push Not at hle
        have h1 : (p : ℝ) ^ (-k₁) ≤ (p : ℝ) ^ (-min k₁ k₂) :=
          zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
        have h2 : (p : ℝ) ^ (-k₂) ≤ (p : ℝ) ^ (-min k₁ k₂) :=
          zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
        have hsub : a₂ - a₁ = (x - a₁) + -(x - a₂) := by ring
        have hle' : ‖a₂ - a₁‖ ≤ (p : ℝ) ^ (-min k₁ k₂) := by
          rw [hsub]
          refine (Padic.nonarchimedean _ _).trans (max_le (hx1.trans h1) ?_)
          rw [norm_neg]; exact hle.trans h2
        exact hab.not_ge hle'
      rw [(ballInd_eq_zero_iff p _ _ _).mpr hx2, mul_zero]
    · push Not at hx1
      rw [(ballInd_eq_zero_iff p _ _ _).mpr hx1, zero_mul]

theorem star_ballInd (a : ℚ_[p]) (k : ℤ) (x : ℚ_[p]) :
    star (ballInd p a k x) = ballInd p a k x := by
  unfold ballInd
  split_ifs <;> simp

theorem padicInner_ballInd (a₁ a₂ : ℚ_[p]) (k₁ k₂ : ℤ) :
    padicInner p (ballInd p a₁ k₁) (ballInd p a₂ k₂) =
      (p : ℂ) ^ (-max k₁ k₂) * ballInd p 0 (min k₁ k₂) (a₂ - a₁) := by
  unfold padicInner
  have hrew : (fun x => star (ballInd p a₁ k₁ x) * ballInd p a₂ k₂ x) =
      fun x => if ‖a₂ - a₁‖ ≤ (p : ℝ) ^ (-min k₁ k₂) then
        ballInd p (if k₁ ≤ k₂ then a₂ else a₁) (max k₁ k₂) x else 0 := by
    funext x
    rw [star_ballInd, ballInd_mul_ballInd]
  rw [hrew]
  by_cases hab : ‖a₂ - a₁‖ ≤ (p : ℝ) ^ (-min k₁ k₂)
  · simp only [if_pos hab]
    rw [padicHaarInt_ballInd, (ballInd_eq_one_iff p 0 (min k₁ k₂) (a₂ - a₁)).mpr (by simpa using hab),
      mul_one]
  · simp only [if_neg hab]
    rw [padicHaarInt_zero,
      (ballInd_eq_zero_iff p 0 (min k₁ k₂) (a₂ - a₁)).mpr (by simpa [not_le] using hab), mul_zero]

theorem padicInner_fourier_ballInd (a₁ a₂ : ℚ_[p]) (k₁ k₂ : ℤ) :
    padicInner p (padicFourier p (ballInd p a₁ k₁)) (padicFourier p (ballInd p a₂ k₂)) =
      padicInner p (ballInd p a₁ k₁) (ballInd p a₂ k₂) := by
  unfold padicInner
  have hrew : (fun y => star (padicFourier p (ballInd p a₁ k₁) y) *
        padicFourier p (ballInd p a₂ k₂) y) =
      fun y => ((p : ℂ) ^ (-(k₁ + k₂))) *
        (ballInd p 0 (-min k₁ k₂) y * padicAddChar p (y * (a₂ - a₁))) := by
    funext y
    rw [padicFourier_ballInd, padicFourier_ballInd]
    simp only [star_mul, star_ballInd, star_padicAddChar]
    have hpstar : star ((p : ℂ) ^ (-k₁)) = (p : ℂ) ^ (-k₁) := by
      rw [Complex.star_def, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, Complex.conj_ofReal]
    rw [hpstar]
    have hball : ballInd p 0 (-k₁) y * ballInd p 0 (-k₂) y = ballInd p 0 (-min k₁ k₂) y := by
      rw [ballInd_mul_ballInd]
      have h0 : ‖(0 : ℚ_[p]) - 0‖ ≤ (p : ℝ) ^ (-min (-k₁) (-k₂)) := by
        simp [zpow_nonneg (padic_p_pos' p).le]
      rw [if_pos h0]
      have hmax : max (-k₁) (-k₂) = -min k₁ k₂ := by omega
      simp [hmax]
    have hch : padicAddChar p (-(a₁ * y)) * padicAddChar p (a₂ * y) =
        padicAddChar p (y * (a₂ - a₁)) := by
      rw [← padicAddChar_add]; congr 1; ring
    have hpow : (p : ℂ) ^ (-k₁) * (p : ℂ) ^ (-k₂) = (p : ℂ) ^ (-(k₁ + k₂)) := by
      rw [← zpow_add₀ (padic_p_complex_ne_zero' p)]; congr 1; omega
    calc ballInd p 0 (-k₁) y * (padicAddChar p (-(a₁ * y)) * (p : ℂ) ^ (-k₁)) *
          ((p : ℂ) ^ (-k₂) * padicAddChar p (a₂ * y) * ballInd p 0 (-k₂) y)
        = ((p : ℂ) ^ (-k₁) * (p : ℂ) ^ (-k₂)) *
            ((ballInd p 0 (-k₁) y * ballInd p 0 (-k₂) y) *
              (padicAddChar p (-(a₁ * y)) * padicAddChar p (a₂ * y))) := by ring
      _ = (p : ℂ) ^ (-(k₁ + k₂)) *
            (ballInd p 0 (-min k₁ k₂) y * padicAddChar p (y * (a₂ - a₁))) := by
            rw [hpow, hball, hch]
  rw [hrew, padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p
    (isPadicSchwartzBruhat_ballInd p 0 (-min k₁ k₂)) (a₂ - a₁))]
  change (p : ℂ) ^ (-(k₁ + k₂)) * padicFourier p (ballInd p 0 (-min k₁ k₂)) (a₂ - a₁) = _
  rw [padicFourier_ballInd_zero, neg_neg, ← mul_assoc, ← zpow_add₀ (padic_p_complex_ne_zero' p)]
  have hexp : -(k₁ + k₂) + min k₁ k₂ = -max k₁ k₂ := by omega
  rw [hexp, ← padicInner_ballInd]
  rfl

/-- Helper: `padicInner` of finite linear combinations of Schwartz–Bruhat functions expands
sesquilinearly. -/
private lemma padicInner_finset_sum {ι₁ ι₂ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (c₁ : ι₁ → ℂ) (c₂ : ι₂ → ℂ) (F₁ : ι₁ → ℚ_[p] → ℂ) (F₂ : ι₂ → ℚ_[p] → ℂ)
    (h₁ : ∀ i ∈ s₁, IsPadicSchwartzBruhat p (F₁ i))
    (h₂ : ∀ j ∈ s₂, IsPadicSchwartzBruhat p (F₂ j)) :
    padicInner p (fun x => ∑ i ∈ s₁, c₁ i * F₁ i x) (fun x => ∑ j ∈ s₂, c₂ j * F₂ j x) =
      ∑ i ∈ s₁, ∑ j ∈ s₂, (star (c₁ i) * c₂ j) * padicInner p (F₁ i) (F₂ j) := by
  unfold padicInner
  have hrew : (fun x => star (∑ i ∈ s₁, c₁ i * F₁ i x) * ∑ j ∈ s₂, c₂ j * F₂ j x) =
      fun x => ∑ i ∈ s₁, ∑ j ∈ s₂, (star (c₁ i) * c₂ j) * (star (F₁ i x) * F₂ j x) := by
    funext x
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [star_mul]; ring
  rw [hrew, padicHaarInt_finset_sum p _ _ fun i hi =>
    isPadicSchwartzBruhat_finset_sum p _ _ fun j hj =>
      isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul p
        (isPadicSchwartzBruhat_conj p (h₁ i hi)) (h₂ j hj))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [padicHaarInt_finset_sum p _ _ fun j hj =>
    isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul p
      (isPadicSchwartzBruhat_conj p (h₁ i hi)) (h₂ j hj))]
  refine Finset.sum_congr rfl fun j hj =>
    padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul p
      (isPadicSchwartzBruhat_conj p (h₁ i hi)) (h₂ j hj))

private lemma padicFourier_finset_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (F : ι → ℚ_[p] → ℂ) (hF : ∀ i ∈ s, IsPadicSchwartzBruhat p (F i)) (y : ℚ_[p]) :
    padicFourier p (fun x => ∑ i ∈ s, c i * F i x) y =
      ∑ i ∈ s, c i * padicFourier p (F i) y := by
  unfold padicFourier
  have hrew : (fun x => (∑ i ∈ s, c i * F i x) * padicAddChar p (x * y)) =
      fun x => ∑ i ∈ s, c i * (F i x * padicAddChar p (x * y)) := by
    funext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
  rw [hrew, padicHaarInt_finset_sum p _ _ fun i hi =>
    isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul_addChar p (hF i hi) y)]
  refine Finset.sum_congr rfl fun i hi =>
    padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_addChar p (hF i hi) y)

/-- **EXACT NON-ARCHIMEDEAN `p`-ADIC PLANCHEREL UNITARITY (`padicFourier_unitary`)**:
`⟨ℱ_p f, ℱ_p g⟩ = ⟨f, g⟩` for ALL Schwartz–Bruhat functions `f, g : ℚ_[p] → ℂ`! -/
theorem padicFourier_unitary {f g : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) (hg : IsPadicSchwartzBruhat p g) :
    padicInner p (padicFourier p f) (padicFourier p g) = padicInner p f g := by
  rcases hf with ⟨R₁, N₁, hf₁⟩
  rcases hg with ⟨R₂, N₂, hg₂⟩
  have hf_sum : f = fun x => ∑ i : Fin (p ^ (N₁ - R₁).toNat),
      f ((p : ℚ_[p]) ^ R₁ * (i.1 : ℚ_[p])) *
        ballInd p ((p : ℚ_[p]) ^ R₁ * (i.1 : ℚ_[p])) N₁ x :=
    funext (isPadicSBAt_eq_sum_ballInd p hf₁)
  have hg_sum : g = fun x => ∑ j : Fin (p ^ (N₂ - R₂).toNat),
      g ((p : ℚ_[p]) ^ R₂ * (j.1 : ℚ_[p])) *
        ballInd p ((p : ℚ_[p]) ^ R₂ * (j.1 : ℚ_[p])) N₂ x :=
    funext (isPadicSBAt_eq_sum_ballInd p hg₂)
  have hFf : padicFourier p f = fun y => ∑ i : Fin (p ^ (N₁ - R₁).toNat),
      f ((p : ℚ_[p]) ^ R₁ * (i.1 : ℚ_[p])) *
        padicFourier p (ballInd p ((p : ℚ_[p]) ^ R₁ * (i.1 : ℚ_[p])) N₁) y := by
    funext y; conv_lhs => rw [hf_sum]
    exact padicFourier_finset_sum p _ _ _ (fun _ _ => isPadicSchwartzBruhat_ballInd p _ _) y
  have hFg : padicFourier p g = fun y => ∑ j : Fin (p ^ (N₂ - R₂).toNat),
      g ((p : ℚ_[p]) ^ R₂ * (j.1 : ℚ_[p])) *
        padicFourier p (ballInd p ((p : ℚ_[p]) ^ R₂ * (j.1 : ℚ_[p])) N₂) y := by
    funext y; conv_lhs => rw [hg_sum]
    exact padicFourier_finset_sum p _ _ _ (fun _ _ => isPadicSchwartzBruhat_ballInd p _ _) y
  rw [hFf, hFg, padicInner_finset_sum p _ _ _ _ _ _
    (fun _ _ => isPadicSchwartzBruhat_padicFourier p (isPadicSchwartzBruhat_ballInd p _ _))
    (fun _ _ => isPadicSchwartzBruhat_padicFourier p (isPadicSchwartzBruhat_ballInd p _ _))]
  conv_rhs => rw [hf_sum, hg_sum, padicInner_finset_sum p _ _ _ _ _ _
    (fun _ _ => isPadicSchwartzBruhat_ballInd p _ _)
    (fun _ _ => isPadicSchwartzBruhat_ballInd p _ _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [padicInner_fourier_ballInd]

/-- Concrete `p`-adic Siegel Levi Weil operator on `PadicSB p`. -/
def padicWeilLevi (χ : (ℚ_[p])ˣ →* Circle) (a : (ℚ_[p])ˣ) :
    Module.End ℂ (PadicSB p) where
  toFun f := ⟨fun x => (χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) * f.1 ((a : ℚ_[p]) * x),
    isPadicSchwartzBruhat_smul p _ (isPadicSchwartzBruhat_mul_left p a.ne_zero f.2)⟩
  map_add' f g := by ext x; dsimp; ring
  map_smul' c f := by ext x; dsimp; ring

theorem isPadicSchwartzBruhat_mul_quad (b : ℚ_[p]) {f : ℚ_[p] → ℂ}
    (hf : IsPadicSchwartzBruhat p f) :
    IsPadicSchwartzBruhat p (fun x => padicAddChar p (b * (x * x)) * f x) := by
  rcases hf with ⟨R, N₀, hf₀⟩
  let N := max N₀ (max R (-b.valuation - R))
  have hf' : IsPadicSBAt p R N f :=
    isPadicSBAt_mono p hf₀ le_rfl (le_max_left N₀ (max R (-b.valuation - R)))
  refine ⟨R, N, hf'.1, fun x hx => by simp [hf'.2.1 x hx], fun x₁ x₂ h12 => ?_⟩
  dsimp only
  by_cases hx₁ : ‖x₁‖ ≤ (p : ℝ) ^ (-R)
  · have hx₂ : ‖x₂‖ ≤ (p : ℝ) ^ (-R) := by
      have hle : (p : ℝ) ^ (-N) ≤ (p : ℝ) ^ (-R) :=
        zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
      have : x₂ = x₁ + -(x₁ - x₂) := by ring
      rw [this]
      refine (Padic.nonarchimedean _ _).trans (max_le hx₁ ?_)
      rw [norm_neg]; exact h12.trans hle
    rw [hf'.2.2 x₁ x₂ h12]
    congr 1
    have hdiff : ‖b * (x₁ * x₁ - x₂ * x₂)‖ ≤ 1 := by
      by_cases hb0 : b = 0
      · simp [hb0]
      · have hfac : x₁ * x₁ - x₂ * x₂ = (x₁ - x₂) * (x₁ + x₂) := by ring
        rw [hfac, norm_mul, norm_mul, Padic.norm_eq_zpow_neg_valuation hb0]
        have hsum : ‖x₁ + x₂‖ ≤ (p : ℝ) ^ (-R) :=
          (Padic.nonarchimedean _ _).trans (max_le hx₁ hx₂)
        have hleN : (p : ℝ) ^ (-N) ≤ (p : ℝ) ^ (b.valuation + R) :=
          zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
        calc (p : ℝ) ^ (-b.valuation) * (‖x₁ - x₂‖ * ‖x₁ + x₂‖)
            ≤ (p : ℝ) ^ (-b.valuation) * ((p : ℝ) ^ (b.valuation + R) * (p : ℝ) ^ (-R)) := by
              refine mul_le_mul_of_nonneg_left
                (mul_le_mul (h12.trans hleN) hsum (norm_nonneg _)
                  (zpow_nonneg (padic_p_pos' p).le _))
                (zpow_nonneg (padic_p_pos' p).le _)
          _ = 1 := by
              rw [← zpow_add₀ (padic_p_pos' p).ne', ← zpow_add₀ (padic_p_pos' p).ne']
              have : -b.valuation + (b.valuation + R + -R) = 0 := by omega
              rw [this, zpow_zero]
    have h1 := padicAddChar_of_norm_le_one p hdiff
    have heq : b * (x₁ * x₁) = b * (x₁ * x₁ - x₂ * x₂) + b * (x₂ * x₂) := by ring
    rw [heq, padicAddChar_add, h1, one_mul]
  · push Not at hx₁
    have hx₂ : (p : ℝ) ^ (-R) < ‖x₂‖ := by
      have hle : (p : ℝ) ^ (-N) ≤ (p : ℝ) ^ (-R) :=
        zpow_le_zpow_right₀ (padic_one_lt_p' p).le (by omega)
      have hne : ‖x₁‖ ≠ ‖-(x₁ - x₂)‖ := by rw [norm_neg]; exact (h12.trans hle |>.trans_lt hx₁).ne'
      have hsub : x₂ = x₁ + -(x₁ - x₂) := by ring
      rw [hsub, Padic.add_eq_max_of_ne hne, norm_neg,
        max_eq_left (h12.trans hle |>.trans_lt hx₁).le]
      exact hx₁
    rw [hf'.2.1 x₁ hx₁, hf'.2.1 x₂ hx₂, mul_zero, mul_zero]

/-- Concrete `p`-adic Siegel unipotent quadratic-phase operator on `PadicSB p`. -/
def padicWeilUnip (b : ℚ_[p]) : Module.End ℂ (PadicSB p) where
  toFun f := ⟨fun x => padicAddChar p (b * (x * x)) * f.1 x,
    isPadicSchwartzBruhat_mul_quad p b f.2⟩
  map_add' f g := by ext x; dsimp; ring
  map_smul' c f := by ext x; dsimp; ring

/-- Concrete `p`-adic Weyl Fourier operator on `PadicSB p`. -/
def padicWeilWeyl : Module.End ℂ (PadicSB p) where
  toFun f := ⟨padicFourier p f.1, isPadicSchwartzBruhat_padicFourier p f.2⟩
  map_add' f g := by ext y; exact padicFourier_add p f.2 g.2 y
  map_smul' c f := by ext y; exact padicFourier_smul p c f.2 y

theorem padicWeilLevi_unitary (χ : (ℚ_[p])ˣ →* Circle) (a : (ℚ_[p])ˣ)
    (f g : PadicSB p) :
    padicInner p (padicWeilLevi p χ a f).1 (padicWeilLevi p χ a g).1 = padicInner p f.1 g.1 := by
  unfold padicInner
  have hrew : (fun x => star ((padicWeilLevi p χ a f).1 x) * (padicWeilLevi p χ a g).1 x) =
      fun x => ((‖(a : ℚ_[p])‖ : ℝ) : ℂ) * (star (f.1 ((a : ℚ_[p]) * x)) * g.1 ((a : ℚ_[p]) * x)) := by
    funext x
    simp only [padicWeilLevi, LinearMap.coe_mk, AddHom.coe_mk, star_mul]
    have hχ : star (χ a : ℂ) * (χ a : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]; norm_num
    have hsq : star ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) =
        ((‖(a : ℚ_[p])‖ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (norm_nonneg _)]
    calc star (f.1 ((a : ℚ_[p]) * x)) *
            (star ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) * star (χ a : ℂ)) *
          ((χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) * g.1 ((a : ℚ_[p]) * x))
        = (star (χ a : ℂ) * (χ a : ℂ)) *
            (star ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ)) *
            (star (f.1 ((a : ℚ_[p]) * x)) * g.1 ((a : ℚ_[p]) * x)) := by ring
      _ = ((‖(a : ℚ_[p])‖ : ℝ) : ℂ) * (star (f.1 ((a : ℚ_[p]) * x)) * g.1 ((a : ℚ_[p]) * x)) := by
            rw [hχ, hsq, one_mul]
  have hfg : IsPadicSchwartzBruhat p (fun x => star (f.1 x) * g.1 x) :=
    isPadicSchwartzBruhat_mul p (isPadicSchwartzBruhat_conj p f.2) g.2
  rw [hrew, padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul_left p a.ne_zero hfg),
    padicHaarInt_mul_left p a.ne_zero hfg, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr a.ne_zero), Complex.ofReal_one, one_mul]

theorem padicWeilUnip_unitary (b : ℚ_[p]) (f g : PadicSB p) :
    padicInner p (padicWeilUnip p b f).1 (padicWeilUnip p b g).1 = padicInner p f.1 g.1 := by
  unfold padicInner
  refine padicHaarInt_congr p fun x => ?_
  simp only [padicWeilUnip, LinearMap.coe_mk, AddHom.coe_mk, star_mul, star_padicAddChar]
  have h1 : padicAddChar p (-(b * (x * x))) * padicAddChar p (b * (x * x)) = 1 := by
    rw [← padicAddChar_add, neg_add_cancel, padicAddChar_zero]
  calc star (f.1 x) * padicAddChar p (-(b * (x * x))) *
        (padicAddChar p (b * (x * x)) * g.1 x)
      = (padicAddChar p (-(b * (x * x))) * padicAddChar p (b * (x * x))) *
          (star (f.1 x) * g.1 x) := by ring
    _ = star (f.1 x) * g.1 x := by rw [h1, one_mul]

theorem padicWeilWeyl_unitary (f g : PadicSB p) :
    padicInner p (padicWeilWeyl p f).1 (padicWeilWeyl p g).1 = padicInner p f.1 g.1 :=
  padicFourier_unitary p f.2 g.2

theorem padicWeilWeyl_spherical :
    padicWeilWeyl p (padicSpherical p) = padicSpherical p := by
  ext y
  exact congrFun (padicFourier_padicIntInd_selfDual p) y

theorem padicWeilUnip_spherical {b : ℚ_[p]} (hb : ‖b‖ ≤ 1) :
    padicWeilUnip p b (padicSpherical p) = padicSpherical p := by
  ext x
  change padicAddChar p (b * (x * x)) * ballInd p 0 0 x = ballInd p 0 0 x
  by_cases hx : ‖x‖ ≤ 1
  · have hnorm : ‖b * (x * x)‖ ≤ 1 := by
      rw [norm_mul, norm_mul]
      calc ‖b‖ * (‖x‖ * ‖x‖) ≤ 1 * (1 * 1) :=
            mul_le_mul hb (mul_le_mul hx hx (norm_nonneg _) zero_le_one)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
        _ = 1 := by norm_num
    rw [padicAddChar_of_norm_le_one p hnorm, one_mul]
  · have h0 : ballInd p 0 0 x = 0 := by
      rw [ballInd_eq_zero_iff]; simpa [not_le] using hx
    rw [h0, mul_zero]

theorem padicWeilLevi_spherical (χ : (ℚ_[p])ˣ →* Circle) {u : (ℚ_[p])ˣ}
    (hu : ‖(u : ℚ_[p])‖ = 1) :
    padicWeilLevi p χ u (padicSpherical p) = (χ u : ℂ) • padicSpherical p := by
  ext x
  change (χ u : ℂ) * ((Real.sqrt ‖(u : ℚ_[p])‖ : ℝ) : ℂ) * ballInd p 0 0 ((u : ℚ_[p]) * x) =
    (χ u : ℂ) * ballInd p 0 0 x
  rw [hu, Real.sqrt_one, Complex.ofReal_one, mul_one]
  congr 1
  unfold ballInd
  simp [norm_mul, hu]

theorem padicInner_spherical :
    padicInner p (padicSpherical p).1 (padicSpherical p).1 = 1 := by
  change padicInner p (ballInd p 0 0) (ballInd p 0 0) = 1
  rw [padicInner_ballInd]
  simp [ballInd]

/-- Exact local `p`-adic split-place matrix coefficient of `padicWeilLevi` on `1_{ℤ_p}`:
`⟨1_{ℤ_p}, ω(a) 1_{ℤ_p}⟩ = χ(a) · p^{-|v_p(a)| / 2}`! -/
theorem padicInner_spherical_levi (χ : (ℚ_[p])ˣ →* Circle) (a : (ℚ_[p])ˣ) :
    padicInner p (padicSpherical p).1 (padicWeilLevi p χ a (padicSpherical p)).1 =
      (χ a : ℂ) * (((p : ℝ) ^ (-((|a.1.valuation| : ℤ) : ℝ) / 2) : ℝ) : ℂ) := by
  have hrew : (padicWeilLevi p χ a (padicSpherical p)).1 =
      fun x => ((χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ)) *
        ballInd p 0 (-a.1.valuation) x := by
    funext x
    change (χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ) * ballInd p 0 0 ((a : ℚ_[p]) * x) = _
    rw [ballInd_mul_left p a.ne_zero]
    simp
  unfold padicInner
  rw [hrew]
  have hmul : (fun x => star ((padicSpherical p).1 x) *
        (((χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ)) * ballInd p 0 (-a.1.valuation) x)) =
      fun x => ((χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ)) *
        (star (ballInd p 0 0 x) * ballInd p 0 (-a.1.valuation) x) := by
    funext x; dsimp only [padicSpherical]; ring
  rw [hmul, padicHaarInt_smul p _ (isPadicSchwartzBruhat_mul p
    (isPadicSchwartzBruhat_conj p (isPadicSchwartzBruhat_ballInd p 0 0))
    (isPadicSchwartzBruhat_ballInd p 0 (-a.1.valuation)))]
  change ((χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p])‖ : ℝ) : ℂ)) *
      padicInner p (ballInd p 0 0) (ballInd p 0 (-a.1.valuation)) = _
  rw [padicInner_ballInd, sub_self, (ballInd_eq_one_iff p 0 _ 0).mpr (by
    simp [zpow_nonneg (padic_p_pos' p).le]), mul_one, mul_assoc]
  congr 1
  rw [Padic.norm_eq_zpow_neg_valuation a.ne_zero, Real.sqrt_eq_rpow,
    ← Real.rpow_intCast (p : ℝ) (-a.1.valuation), ← Real.rpow_mul (padic_p_pos' p).le,
    ← Complex.ofReal_natCast, ← Complex.ofReal_zpow, ← Complex.ofReal_mul,
    ← Real.rpow_intCast (p : ℝ) (-max 0 (-a.1.valuation)), ← Real.rpow_add (padic_p_pos' p)]
  congr 1
  congr 1
  rcases le_or_gt 0 a.1.valuation with hv | hv
  · have hmax : max (0 : ℤ) (-a.1.valuation) = 0 := max_eq_left (by omega)
    rw [hmax, abs_of_nonneg hv]; push_cast; ring
  · have hmax : max (0 : ℤ) (-a.1.valuation) = -a.1.valuation := max_eq_right (by omega)
    rw [hmax, abs_of_neg hv]; push_cast; ring

end PadicSchrodinger

/-! ## Section 4: Unified `LocalWeilRep v`, `SchwartzBruhatAdelic`, & `weil_representation_unitary` -/

section LocalAndAdelicWeil

/-- Places of `ℚ` (with `LocalWeilRep` parameterized over any place index `v : ι`). -/
inductive LocalPlace : Type
  | arch : LocalPlace
  | finite (p : Nat.Primes) : LocalPlace
  deriving DecidableEq

/-- **Unified Local Weil Representation `LocalWeilRep v`** at any place `v`. -/
structure LocalWeilRep.{u, w} {ι : Type w} (v : ι) where
  Space : Type u
  [instAdd : AddCommGroup Space]
  [instMod : Module ℂ Space]
  Grp : Type u
  [instGrp : Group Grp]
  rep : Grp →* Module.End ℂ Space
  innerProd : Space → Space → ℂ
  inner_conj_symm : ∀ x y, star (innerProd x y) = innerProd y x
  inner_self_nonneg : ∀ x, 0 ≤ (innerProd x x).re ∧ (innerProd x x).im = 0
  inner_self_eq_zero : ∀ x, innerProd x x = 0 ↔ x = 0
  rep_unitary : ∀ g x y, innerProd (rep g x) (rep g y) = innerProd x y
  vacuum : Space
  vacuum_ne_zero : vacuum ≠ 0
  compactSubgroup : Subgroup Grp
  vacuum_eigen : ∀ k ∈ compactSubgroup, ∃ χ : Circle, rep k vacuum = (χ : ℂ) • vacuum

attribute [instance] LocalWeilRep.instAdd LocalWeilRep.instMod LocalWeilRep.instGrp

/-- **Axiomatization of the Unitary Schrödinger Weil Representation (`IsWeilSch`)** matching
Alpöge's `GlobalTheory.StdUnn.IsWeilSch` for Wave 2 `AdelicWeilTheta` & `SiegelEisenstein`. -/
structure IsWeilSch {G A V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (eval : V → A → ℂ)
    (leviAct : G → A → A) (leviFactor : G → ℂ)
    (unipPhase : G → A → ℂ) (weylOp : V → V)
    (IsLevi IsUnip IsWeyl : G → Prop)
    (ω : G →* Module.End ℂ V) : Prop where
  levi : ∀ g, IsLevi g → ∀ Φ x, eval (ω g Φ) x = leviFactor g * eval Φ (leviAct g x)
  unip : ∀ g, IsUnip g → ∀ Φ x, eval (ω g Φ) x = unipPhase g x * eval Φ x
  weyl : ∀ g, IsWeyl g → ∀ Φ, ω g Φ = weylOp Φ

/-- Concrete `p`-adic Siegel Levi `LocalWeilRep (LocalPlace.finite p)` on `PadicSB p`. -/
def padicLocalWeilRep (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle) :
    LocalWeilRep (LocalPlace.finite p) where
  Space := PadicSB p.1
  Grp := (ℚ_[p.1])ˣ
  rep :=
    { toFun := padicWeilLevi p.1 χ
      map_one' := by
        ext f x
        change (χ 1 : ℂ) * ((Real.sqrt ‖(1 : ℚ_[p.1])‖ : ℝ) : ℂ) * f.1 (1 * x) = f.1 x
        simp
      map_mul' := fun a b => by
        ext f x
        change (χ (a * b) : ℂ) * ((Real.sqrt ‖((a * b : (ℚ_[p.1])ˣ) : ℚ_[p.1])‖ : ℝ) : ℂ) *
            f.1 (((a * b : (ℚ_[p.1])ˣ) : ℚ_[p.1]) * x) =
          (χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) *
            ((χ b : ℂ) * ((Real.sqrt ‖(b : ℚ_[p.1])‖ : ℝ) : ℂ) *
              f.1 ((b : ℚ_[p.1]) * ((a : ℚ_[p.1]) * x)))
        have harg : (((a * b : (ℚ_[p.1])ˣ) : ℚ_[p.1]) * x) =
            (b : ℚ_[p.1]) * ((a : ℚ_[p.1]) * x) := by
          rw [Units.val_mul]; ring
        rw [harg, map_mul, Circle.coe_mul, Units.val_mul, norm_mul,
          Real.sqrt_mul (norm_nonneg _), Complex.ofReal_mul]
        ring }
  innerProd f g := padicInner p.1 f.1 g.1
  inner_conj_symm f g := padicInner_conj_symm p.1 f.2 g.2
  inner_self_nonneg f := padicInner_self_re_nonneg p.1 f.2
  inner_self_eq_zero f := by
    rw [padicInner_self_eq_zero_iff p.1 f.2]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rep_unitary a f g := padicWeilLevi_unitary p.1 χ a f g
  vacuum := padicSpherical p.1
  vacuum_ne_zero := by
    intro h0
    have h1 := congrArg (fun f : PadicSB p.1 => f.1 0) h0
    simp [padicSpherical, ballInd] at h1
  compactSubgroup :=
    { carrier := {u : (ℚ_[p.1])ˣ | ‖(u : ℚ_[p.1])‖ = 1}
      mul_mem' := fun {a b} ha hb => by
        change ‖((a * b : (ℚ_[p.1])ˣ) : ℚ_[p.1])‖ = 1
        rw [Units.val_mul, norm_mul, ha, hb, mul_one]
      one_mem' := by change ‖(1 : ℚ_[p.1])‖ = 1; simp
      inv_mem' := fun {a} ha => by
        change ‖((a⁻¹ : (ℚ_[p.1])ˣ) : ℚ_[p.1])‖ = 1
        have h : ‖((a⁻¹ : (ℚ_[p.1])ˣ) : ℚ_[p.1])‖ * ‖(a : ℚ_[p.1])‖ = 1 := by
          rw [← norm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, norm_one]
        have ha' : ‖(a : ℚ_[p.1])‖ = 1 := ha
        rw [ha', mul_one] at h
        exact h }
  vacuum_eigen u hu := ⟨χ u, padicWeilLevi_spherical p.1 χ hu⟩

/-- Concrete archimedean vacuum line `ℂ · stdGauss`. -/
def archVacuumSpace : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {stdGauss}

private lemma realWeilOp_rot_smul (θ : ℝ) (c : ℂ) :
    realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) (c • stdGauss) =
      (c * Complex.exp (Complex.I * (θ : ℂ))) • stdGauss := by
  funext z
  rw [realWeilOp_smul, gauss_vacuum_eigenvalue θ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Concrete `LocalWeilRep LocalPlace.arch` realized by `realWeilOp (cos θ) (sin θ) (-sin θ) (cos θ)`
on `archVacuumSpace` with `L²(ℂ, volC)` inner product and Gaussian vacuum `stdGauss`. -/
def archLocalWeilRep : LocalWeilRep LocalPlace.arch where
  Space := archVacuumSpace
  Grp := Multiplicative ℝ
  rep :=
    { toFun := fun g =>
        { toFun := fun Φ =>
            let θ : ℝ := Multiplicative.toAdd g
            ⟨realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) Φ.1, by
              rcases Submodule.mem_span_singleton.mp Φ.2 with ⟨c, hc⟩
              rw [← hc, realWeilOp_rot_smul]
              exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)⟩
          map_add' := fun Φ₁ Φ₂ => by
            let θ : ℝ := Multiplicative.toAdd g
            rcases Submodule.mem_span_singleton.mp Φ₁.2 with ⟨c₁, hc₁⟩
            rcases Submodule.mem_span_singleton.mp Φ₂.2 with ⟨c₂, hc₂⟩
            have hsum : (Φ₁ + Φ₂).1 = (c₁ + c₂) • stdGauss := by
              change Φ₁.1 + Φ₂.1 = _; rw [← hc₁, ← hc₂, add_smul]
            ext z
            change realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) (Φ₁ + Φ₂).1 z =
              realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) Φ₁.1 z +
              realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) Φ₂.1 z
            rw [hsum, ← hc₁, ← hc₂, realWeilOp_rot_smul, realWeilOp_rot_smul, realWeilOp_rot_smul]
            simp only [Pi.smul_apply, smul_eq_mul]; ring
          map_smul' := fun r Φ => by
            let θ : ℝ := Multiplicative.toAdd g
            rcases Submodule.mem_span_singleton.mp Φ.2 with ⟨c, hc⟩
            have hsm : (r • Φ).1 = (r * c) • stdGauss := by
              change r • Φ.1 = _; rw [← hc, smul_smul]
            ext z
            change realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) (r • Φ).1 z =
              r * realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) Φ.1 z
            rw [hsm, ← hc, realWeilOp_rot_smul, realWeilOp_rot_smul]
            simp only [Pi.smul_apply, smul_eq_mul]; ring }
      map_one' := by
        ext Φ z
        simp [realWeilOp_one]
      map_mul' := fun g₁ g₂ => by
        let θ₁ : ℝ := Multiplicative.toAdd g₁
        let θ₂ : ℝ := Multiplicative.toAdd g₂
        ext Φ z
        rcases Submodule.mem_span_singleton.mp Φ.2 with ⟨c, hc⟩
        change realWeilOp (Real.cos (θ₁ + θ₂)) (Real.sin (θ₁ + θ₂))
            (-Real.sin (θ₁ + θ₂)) (Real.cos (θ₁ + θ₂)) Φ.1 z =
          realWeilOp (Real.cos θ₁) (Real.sin θ₁) (-Real.sin θ₁) (Real.cos θ₁)
            (realWeilOp (Real.cos θ₂) (Real.sin θ₂) (-Real.sin θ₂) (Real.cos θ₂) Φ.1) z
        rw [← hc, realWeilOp_rot_smul (θ₁ + θ₂) c, realWeilOp_rot_smul θ₂ c,
          realWeilOp_rot_smul θ₁ (c * Complex.exp (Complex.I * (θ₂ : ℂ)))]
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, mul_add, Complex.exp_add]
        ring }
  innerProd Φ₁ Φ₂ := archInner Φ₁.1 Φ₂.1
  inner_conj_symm Φ₁ Φ₂ := archInner_conj_symm Φ₁.1 Φ₂.1
  inner_self_nonneg Φ := archInner_self_re_nonneg Φ.1
  inner_self_eq_zero Φ := by
    rcases Submodule.mem_span_singleton.mp Φ.2 with ⟨c, hc⟩
    have hval : archInner Φ.1 Φ.1 = (star c * c) * (1 / 2) := by
      rw [← hc, ← archInner_stdGauss_self]
      unfold archInner
      have hrew : (fun z => star ((c • stdGauss) z) * (c • stdGauss) z) =
          fun z => (star c * c) * (star (stdGauss z) * stdGauss z) := by
        funext z; simp only [Pi.smul_apply, smul_eq_mul, star_mul]; ring
      rw [hrew, integral_const_mul]
    rw [hval]
    constructor
    · intro h0
      have hc0 : star c * c = 0 := (mul_eq_zero.mp h0).resolve_right (by norm_num)
      have hcn : c = 0 := by
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_eq_zero] at hc0
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hc0)
      ext z; rw [← hc, hcn]; simp
    · intro h0
      have hc0 : c = 0 := by
        have hz := congrArg (fun f : archVacuumSpace => f.1 0) h0
        rw [← hc] at hz
        simpa [stdGauss_zero] using hz
      simp [hc0]
  rep_unitary g Φ₁ Φ₂ := by
    let θ : ℝ := Multiplicative.toAdd g
    have hdet : Real.cos θ * Real.cos θ - Real.sin θ * (-Real.sin θ) = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    have hcs : ∀ Φ : archVacuumSpace, IsChirpSchwartz Φ.1 := by
      intro Φ
      rcases Submodule.mem_span_singleton.mp Φ.2 with ⟨c, hc⟩
      intro t
      have hrew : (fun u => ee (t * Complex.normSq u) * Φ.1 u) =
          fun u => c * (ee (t * Complex.normSq u) * stdGauss u) := by
        funext u; rw [← hc]; simp [Pi.smul_apply, smul_eq_mul]; ring
      rw [hrew]
      exact isArchSchwartz_const_mul c (stdGauss_isChirpSchwartz t)
    exact realWeilOp_unitary hdet (hcs Φ₁) (hcs Φ₂)
  vacuum := ⟨stdGauss, Submodule.subset_span rfl⟩
  vacuum_ne_zero := by
    intro h0
    have hz := congrArg (fun f : archVacuumSpace => f.1 0) h0
    simp [stdGauss_zero] at hz
  compactSubgroup := ⊤
  vacuum_eigen g _ := by
    let θ : ℝ := Multiplicative.toAdd g
    refine ⟨Circle.exp θ, ?_⟩
    ext z
    have h := congrFun (gauss_vacuum_eigenvalue θ) z
    simpa [Circle.coe_exp, mul_comm Complex.I] using h

/-- Concrete finite-field `LocalWeilRep` bridged directly from `RHDirect.Stage2WeilMetaplectic`! -/
def finiteFieldLocalWeilRep {ι : Type*} (v : ι) (𝔽 : Type*) [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    (n : ℕ) : LocalWeilRep v where
  Space := SchrodingerSpace 𝔽 n
  Grp := GL (Fin n) 𝔽
  rep := weilLeviHom
  innerProd f g := inner ℂ f g
  inner_conj_symm f g := inner_conj_symm g f
  inner_self_nonneg f := by
    have h : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    rw [h, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sq_nonneg _, rfl⟩
  inner_self_eq_zero f := inner_self_eq_zero
  rep_unitary g f₁ f₂ := weilLevi_unitary g f₁ f₂
  vacuum := deltaVec 0
  vacuum_ne_zero := by
    intro h0
    have hz := congrArg (fun f : SchrodingerSpace 𝔽 n => f 0) h0
    simp at hz
  compactSubgroup := ⊤
  vacuum_eigen g _ := by
    refine ⟨1, ?_⟩
    ext x
    change deltaVec (0 : Fin n → 𝔽) (g⁻¹.1.mulVec x) = (1 : ℂ) * deltaVec 0 x
    simp only [deltaVec_apply, one_mul]
    have hiff : g⁻¹.1.mulVec x = 0 ↔ x = 0 := by
      constructor
      · intro hx
        have h1 := congrArg g.1.mulVec hx
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec, Matrix.mulVec_zero] at h1
        exact h1
      · rintro rfl; exact Matrix.mulVec_zero _
    by_cases hx : x = 0
    · rw [if_pos (hiff.mpr hx), if_pos hx]
    · rw [if_neg (mt hiff.mp hx), if_neg hx]

/-! ### Concrete Adelic Schwartz–Bruhat Space `SchwartzBruhatAdelic` -/

/-- Complexified rational adele space `ℂ × 𝔸_{ℚ,f}` for unitary/complex Schrödinger functions. -/
abbrev AdelicComplexSpace : Type :=
  ℂ × RatFinAdele

/-- A **factorizable adelic Schwartz–Bruhat pure tensor** `Φ_∞ ⊗ (⊗'_p Φ_p)`. -/
structure AdelicPureTensor where
  fInf : ℂ → ℂ
  hfInf : IsArchSchwartz fInf
  fFin : ∀ p : Nat.Primes, PadicSB p.1
  supp : Finset Nat.Primes
  unramified : ∀ p : Nat.Primes, p ∉ supp → fFin p = padicSpherical p.1

theorem AdelicPureTensor.hasFiniteMulSupport (T : AdelicPureTensor) (x : RatFinAdele) :
    (Function.mulSupport fun p : Nat.Primes => (T.fFin p).1 (x p)).Finite := by
  have hmem : ∀ᶠ p : Nat.Primes in Filter.cofinite, x p ∈ PadicInt.subring p.1 := x.2
  have hbad : {p : Nat.Primes | x p ∉ PadicInt.subring p.1}.Finite := by
    simpa [Filter.eventually_cofinite] using hmem
  refine (hbad.union T.supp.finite_toSet).subset fun p hp => ?_
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, not_or, not_not] at hnot
  have hval : (T.fFin p).1 (x p) = 1 := by
    rw [T.unramified p hnot.2]
    change ballInd p.1 0 0 (x p) = 1
    rw [ballInd_eq_one_iff]
    simpa [PadicInt.subring] using hnot.1
  exact hp hval

def AdelicPureTensor.eval (T : AdelicPureTensor) (x : AdelicComplexSpace) : ℂ :=
  T.fInf x.1 * ∏ᶠ p : Nat.Primes, (T.fFin p).1 (x.2 p)

/-- **CONCRETE ADELIC SCHWARTZ–BRUHAT SPACE `SchwartzBruhatAdelic`**:
the `ℂ`-submodule of functions `AdelicComplexSpace → ℂ` spanned by all factorizable
archimedean-Schwartz × finite-place-Bruhat pure tensors! -/
def SchwartzBruhatAdelic : Submodule ℂ (AdelicComplexSpace → ℂ) :=
  Submodule.span ℂ (Set.range AdelicPureTensor.eval)

theorem adelicPureTensor_mem_schwartzBruhatAdelic (T : AdelicPureTensor) :
    T.eval ∈ SchwartzBruhatAdelic :=
  Submodule.subset_span ⟨T, rfl⟩

/-- The canonical **global Gaussian–spherical vacuum** `φ₀ = stdGauss ⊗ (⊗'_p 1_{ℤ_p})`. -/
def adelicVacuum : AdelicPureTensor where
  fInf := stdGauss
  hfInf := stdGauss_isArchSchwartz
  fFin p := padicSpherical p.1
  supp := ∅
  unramified _ _ := rfl

theorem adelicVacuum_mem_schwartzBruhatAdelic :
    adelicVacuum.eval ∈ SchwartzBruhatAdelic :=
  adelicPureTensor_mem_schwartzBruhatAdelic adelicVacuum

@[simp]
theorem adelicVacuum_eval_zero :
    adelicVacuum.eval (0, 0) = 1 := by
  unfold AdelicPureTensor.eval adelicVacuum
  have hfin : ∀ p : Nat.Primes, (padicSpherical p.1).1 0 = 1 := fun p => by
    change ballInd p.1 0 0 0 = 1
    simp [ballInd]
  simp [hfin, stdGauss_zero]

/-- Exact finite-product adelic `L²` inner product of two factorizable `AdelicPureTensor`s. -/
def adelicPureInner (T₁ T₂ : AdelicPureTensor) : ℂ :=
  archInner T₁.fInf T₂.fInf *
    ∏ p ∈ T₁.supp ∪ T₂.supp, padicInner p.1 (T₁.fFin p).1 (T₂.fFin p).1

theorem adelicPureInner_eq_prod_of_subset (T₁ T₂ : AdelicPureTensor) (S : Finset Nat.Primes)
    (hS : T₁.supp ∪ T₂.supp ⊆ S) :
    adelicPureInner T₁ T₂ =
      archInner T₁.fInf T₂.fInf * ∏ p ∈ S, padicInner p.1 (T₁.fFin p).1 (T₂.fFin p).1 := by
  unfold adelicPureInner
  congr 1
  refine Finset.prod_subset hS fun p _ hp => ?_
  rw [Finset.mem_union, not_or] at hp
  rw [T₁.unramified p hp.1, T₂.unramified p hp.2]
  exact padicInner_spherical p.1

theorem adelicPureInner_vacuum_self :
    adelicPureInner adelicVacuum adelicVacuum = 1 / 2 := by
  unfold adelicPureInner adelicVacuum
  simp [archInner_stdGauss_self]

/-- Restricted-product adelic Weil operator datum. -/
structure AdelicWeilElement where
  thetaInf : ℝ
  chiFin : ∀ p : Nat.Primes, (ℚ_[p.1])ˣ →* Circle
  aFin : ∀ p : Nat.Primes, (ℚ_[p.1])ˣ
  ramPrimes : Finset Nat.Primes
  unramified_act : ∀ p : Nat.Primes, p ∉ ramPrimes →
    padicWeilLevi p.1 (chiFin p) (aFin p) (padicSpherical p.1) = padicSpherical p.1

def adelicWeilAct (g : AdelicWeilElement) (T : AdelicPureTensor)
    (hArch : IsArchSchwartz (realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
      (-Real.sin g.thetaInf) (Real.cos g.thetaInf) T.fInf)) : AdelicPureTensor where
  fInf := realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
    (-Real.sin g.thetaInf) (Real.cos g.thetaInf) T.fInf
  hfInf := hArch
  fFin p := padicWeilLevi p.1 (g.chiFin p) (g.aFin p) (T.fFin p)
  supp := T.supp ∪ g.ramPrimes
  unramified p hp := by
    rw [Finset.mem_union, not_or] at hp
    rw [T.unramified p hp.1, g.unramified_act p hp.2]

/-- **MASTER UNITARITY THEOREM FOR THE LOCAL & ADELIC WEIL REPRESENTATION
(`weil_representation_unitary`)**:
Unconditionally certifies `L²`-unitarity across all four layers:
1. Every `W : LocalWeilRep v` is unitary on its local Schrödinger space;
2. The archimedean `SL₂(ℝ)` Weil operator `realWeilOp a b c d` (`a d - b c = 1`) is
   `L²(ℂ, volC)`-unitary on chirp-Schwartz functions;
3. Every non-archimedean `p`-adic Weil generator (`padicWeilLevi`, `padicWeilUnip`,
   `padicWeilWeyl`) is `L²(ℚ_p)`-unitary on `PadicSB p`;
4. Every restricted-product `AdelicWeilElement` is strictly unitary for the global adelic `L²`
   inner product `adelicPureInner` on `SchwartzBruhatAdelic`! -/
theorem weil_representation_unitary :
    (∀ {ι : Type*} {v : ι} (W : LocalWeilRep v) (g : W.Grp) (x y : W.Space),
      W.innerProd (W.rep g x) (W.rep g y) = W.innerProd x y) ∧
    (∀ {a b c d : ℝ}, a * d - b * c = 1 →
      ∀ {Φ₁ Φ₂ : ℂ → ℂ}, IsChirpSchwartz Φ₁ → IsChirpSchwartz Φ₂ →
        archInner (realWeilOp a b c d Φ₁) (realWeilOp a b c d Φ₂) = archInner Φ₁ Φ₂) ∧
    (∀ (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle) (a : (ℚ_[p.1])ˣ) (b : ℚ_[p.1])
      (f g : PadicSB p.1),
      padicInner p.1 (padicWeilLevi p.1 χ a f).1 (padicWeilLevi p.1 χ a g).1 =
        padicInner p.1 f.1 g.1 ∧
      padicInner p.1 (padicWeilUnip p.1 b f).1 (padicWeilUnip p.1 b g).1 =
        padicInner p.1 f.1 g.1 ∧
      padicInner p.1 (padicWeilWeyl p.1 f).1 (padicWeilWeyl p.1 g).1 =
        padicInner p.1 f.1 g.1) ∧
    (∀ (g : AdelicWeilElement) (T₁ T₂ : AdelicPureTensor)
      (_hcs₁ : IsChirpSchwartz T₁.fInf) (_hcs₂ : IsChirpSchwartz T₂.fInf)
      (hA₁ : IsArchSchwartz (realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
        (-Real.sin g.thetaInf) (Real.cos g.thetaInf) T₁.fInf))
      (hA₂ : IsArchSchwartz (realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
        (-Real.sin g.thetaInf) (Real.cos g.thetaInf) T₂.fInf)),
      adelicPureInner (adelicWeilAct g T₁ hA₁) (adelicWeilAct g T₂ hA₂) =
        adelicPureInner T₁ T₂) := by
  refine ⟨fun W g x y => W.rep_unitary g x y,
    fun hdet _ _ h₁ h₂ => realWeilOp_unitary hdet h₁ h₂,
    fun p χ a b f g => ⟨padicWeilLevi_unitary p.1 χ a f g,
      padicWeilUnip_unitary p.1 b f g, padicWeilWeyl_unitary p.1 f g⟩,
    fun g T₁ T₂ hcs₁ hcs₂ hA₁ hA₂ => ?_⟩
  set S : Finset Nat.Primes := (T₁.supp ∪ T₂.supp) ∪ g.ramPrimes
  have hsub1 : (adelicWeilAct g T₁ hA₁).supp ∪ (adelicWeilAct g T₂ hA₂).supp ⊆ S := by
    intro p hp
    simp only [adelicWeilAct, Finset.mem_union, S] at hp ⊢
    tauto
  have hsub2 : T₁.supp ∪ T₂.supp ⊆ S := Finset.subset_union_left
  rw [adelicPureInner_eq_prod_of_subset _ _ S hsub1,
    adelicPureInner_eq_prod_of_subset _ _ S hsub2]
  have hdet : Real.cos g.thetaInf * Real.cos g.thetaInf -
      Real.sin g.thetaInf * (-Real.sin g.thetaInf) = 1 := by
    have := Real.sin_sq_add_cos_sq g.thetaInf
    linarith
  congr 1
  · exact realWeilOp_unitary hdet hcs₁ hcs₂
  · refine Finset.prod_congr rfl fun p _ => ?_
    exact padicWeilLevi_unitary p.1 (g.chiFin p) (g.aFin p) (T₁.fFin p) (T₂.fFin p)

end LocalAndAdelicWeil

/-! ## Section 5: Split-Place Idempotent Algebra & `split_support_projects_vacuum`
(Distilling Alpöge's `WeilRepresentationSplitSupportProjectsVacuum`) -/

section SplitSupportVacuumProjection

/-- A **split idempotent** `e` in a commutative ring `R` with CM involution `c : R →+* R`:
`e² = e` and `e · c(e) = 0`. -/
def IsSplitIdem {R : Type*} [CommRing R] (c : R →+* R) (e : R) : Prop :=
  e * e = e ∧ e * c e = 0

/-- A finite family `{e_i}_{i ∈ Q}` of pairwise orthogonal split idempotents whose sum `e`
satisfies `e · c(e) = 0`. -/
structure OrthSplitIdemFamily {R ι : Type*} [CommRing R] (c : R →+* R) (Q : Finset ι)
    (es : ι → R) : Prop where
  split : ∀ i ∈ Q, IsSplitIdem c (es i)
  orth : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0
  conj_orth : (∑ i ∈ Q, es i) * c (∑ i ∈ Q, es i) = 0

theorem split_idem_sum_idem {R : Type*} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x)
    {e : R} (he : IsSplitIdem c e) :
    (e + c e) * (e + c e) = e + c e ∧ c (e + c e) = e + c e := by
  have hce : c e * c e = c e := by rw [← map_mul, he.1]
  refine ⟨?_, ?_⟩
  · linear_combination he.1 + hce + 2 * he.2
  · rw [map_add, hc, add_comm]

theorem split_idem_compl_idem {R : Type*} [CommRing R] (c : R →+* R) (hc : ∀ x, c (c x) = x)
    {e : R} (he : IsSplitIdem c e) :
    (1 - (e + c e)) * (1 - (e + c e)) = 1 - (e + c e) ∧
      c (1 - (e + c e)) = 1 - (e + c e) := by
  obtain ⟨hε, hcε⟩ := split_idem_sum_idem c hc he
  refine ⟨?_, ?_⟩
  · linear_combination hε
  · rw [map_sub, map_one, hcε]

/-- **Idempotent Determinant Localization Lemma** (distilling Alpöge's `idem_det`). -/
theorem idem_det_eq {R : Type*} [CommRing R] {m : ℕ} {a : R} (ha : a * a = a)
    {M M' : Matrix (Fin m) (Fin m) R} (hM : a • M = a • M') :
    a * M.det = a * M'.det := by
  have hap : ∀ n : ℕ, 1 ≤ n → a ^ n = a := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases k with _ | k'
      · simp
      · rw [pow_succ, ih (by omega), ha]
  have hEntry : ∀ i j, a * M i j = a * M' i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.smul_apply, smul_eq_mul] using this
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Matrix.det_apply', Matrix.det_apply', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hprod : a * ∏ i : Fin m, M (σ i) i = a * ∏ i : Fin m, M' (σ i) i := by
      have hm1 : 1 ≤ Fintype.card (Fin m) := by simpa using Nat.succ_le_of_lt hm
      calc a * ∏ i : Fin m, M (σ i) i
          = (∏ _i : Fin m, a) * ∏ i : Fin m, M (σ i) i := by
              rw [Finset.prod_const, Finset.card_univ, hap _ hm1]
        _ = ∏ i : Fin m, (a * M (σ i) i) := Finset.prod_mul_distrib.symm
        _ = ∏ i : Fin m, (a * M' (σ i) i) :=
              Finset.prod_congr rfl fun i _ => hEntry (σ i) i
        _ = (∏ _i : Fin m, a) * ∏ i : Fin m, M' (σ i) i := Finset.prod_mul_distrib
        _ = a * ∏ i : Fin m, M' (σ i) i := by
              rw [Finset.prod_const, Finset.card_univ, hap _ hm1]
    calc a * ((Equiv.Perm.sign σ : R) * ∏ i : Fin m, M (σ i) i)
        = (Equiv.Perm.sign σ : R) * (a * ∏ i : Fin m, M (σ i) i) := by ring
      _ = (Equiv.Perm.sign σ : R) * (a * ∏ i : Fin m, M' (σ i) i) := by rw [hprod]
      _ = a * ((Equiv.Perm.sign σ : R) * ∏ i : Fin m, M' (σ i) i) := by ring

/-- Localized determinant `detAt e M = e * M.det + (1 - e)` at an idempotent `e`. -/
def detAt {R : Type*} [CommRing R] {m : ℕ} (e : R) (M : Matrix (Fin m) (Fin m) R) : R :=
  e * M.det + (1 - e)

/-- **Split-Support Matrix & Determinant Factorization** (distilling Alpöge's `alg_parts`). -/
theorem split_matrix_factorization {R : Type*} [CommRing R] {m : ℕ} (c : R →+* R)
    {a a' : R}
    (ha : a * a = a) (hca : c a * c a = c a) (haca : a * c a = 0)
    (ha' : a' * a' = a') (haa' : a * a' = 0) (hcaca' : c a * c a' = 0)
    (haca' : a * c a' = 0) (hcaa' : c a * a' = 0)
    {M : Matrix (Fin m) (Fin m) R}
    (hsupp : (1 - ((a + a') + (c a + c a'))) • (M - 1) = 0) :
    let ε : R := a + c a
    let M₀ : Matrix (Fin m) (Fin m) R := 1 + ε • (M - 1)
    let M' : Matrix (Fin m) (Fin m) R := 1 + (1 - ε) • (M - 1)
    M = M₀ * M' ∧
    (1 - (a + c a)) • (M₀ - 1) = 0 ∧
    (1 - (a' + c a')) • (M' - 1) = 0 ∧
    detAt (a + a') M = detAt a M₀ * detAt a' M' := by
  intro ε M₀ M'
  have hε : ε * ε = ε := by simp only [ε]; linear_combination ha + hca + 2 * haca
  have h1ε : ε * (1 - ε) = 0 := by linear_combination -hε
  have hsupp_ij : ∀ i j, (1 - ((a + a') + (c a + c a'))) * (M i j - (1 : Matrix _ _ R) i j) = 0 := by
    intro i j
    have := congrFun (congrFun hsupp i) j
    simpa [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] using this
  have hM0_supp : (1 - ε) • (M₀ - 1) = 0 := by
    ext i j
    simp only [M₀, add_sub_cancel_left, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply,
      smul_eq_mul]
    linear_combination (M i j - (1 : Matrix _ _ R) i j) * (-hε)
  have hM'_supp : (1 - (a' + c a')) • (M' - 1) = 0 := by
    ext i j
    simp only [M', add_sub_cancel_left, Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply,
      smul_eq_mul, ε]
    have hcoeff : (1 - (a' + c a')) * (1 - (a + c a)) = 1 - ((a + a') + (c a + c a')) := by
      linear_combination haa' + haca' + hcaa' + hcaca'
    rw [← mul_assoc, hcoeff, hsupp_ij i j]
  have hmul : M = M₀ * M' := by
    calc M = 1 + (M - 1) := by abel
      _ = 1 + ε • (M - 1) + (1 - ε) • (M - 1) := by
            ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
            ring
      _ = (1 + ε • (M - 1)) * (1 + (1 - ε) • (M - 1)) := by
            rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one,
              Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1ε, zero_smul, add_zero]
            abel
  have hdet0 : a * M₀.det = a * M.det := by
    refine idem_det_eq ha ?_
    ext i j
    simp only [M₀, ε, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination (M i j - (1 : Matrix _ _ R) i j) * (ha + haca)
  have hdet' : a' * M'.det = a' * M.det := by
    refine idem_det_eq ha' ?_
    ext i j
    simp only [M', ε, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    linear_combination -(M i j - (1 : Matrix _ _ R) i j) * (haa' + hcaa')
  have hdet : detAt (a + a') M = detAt a M₀ * detAt a' M' := by
    unfold detAt
    linear_combination -(1 - a') * hdet0 - (1 - a) * hdet' +
      (M.det + M.det - M₀.det * M'.det - 1) * haa'
  exact ⟨hmul, hM0_supp, hM'_supp, hdet⟩

/-- **Abstract Split-Support Lattice Splitting Lemma** (distilling Alpöge's `hLat_split` + `hle`). -/
theorem split_lattice_decomp {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (Λ₀ Λ₁ Λ' : Submodule R M)
    (hsplit : ∀ v ∈ Λ', ∃ x, x ∈ Λ₀ ∧ x ∈ Λ' ∧ v - x ∈ Λ₁) :
    Λ' ≤ (Λ' ⊓ Λ₀) ⊔ (Λ' ⊓ Λ₁) := by
  intro v hv
  obtain ⟨x, hx0, hx', hvx1⟩ := hsplit v hv
  have hvx' : v - x ∈ Λ' := Λ'.sub_mem hv hx'
  have hdecomp : v = x + (v - x) := by abel
  rw [hdecomp]
  exact Submodule.add_mem_sup ⟨hx', hx0⟩ ⟨hvx', hvx1⟩

/-- A **Split-Place Vacuum Projection System** attached to a Weil representation `ω`. -/
structure SplitVacuumSystem (G H U Lat : Type*) [Group G] [CommGroup U]
    [AddCommGroup H] [Module ℂ H] where
  ω : G →* Module.End ℂ H
  proj : Lat → Module.End ℂ H
  baseLat : Lat
  moveLat : G → Lat → Lat
  moveLat_one : ∀ Λ, moveLat 1 Λ = Λ
  moveLat_mul : ∀ g₁ g₂ Λ, moveLat (g₁ * g₂) Λ = moveLat g₁ (moveLat g₂ Λ)
  χ : U →* Circle
  rank : ℕ
  idx : Lat → Lat → ℕ
  idx_self : ∀ Λ, idx Λ Λ = 1
  idx_pos : ∀ Λ₁ Λ₂, 0 < idx Λ₁ Λ₂
  local_step : ∀ (h₀ h' : G) (y₀ : U) (v : H),
    proj baseLat (ω h₀ (proj (moveLat h' baseLat) v)) =
      ((χ y₀ : ℂ) * (((idx (moveLat (h₀ * h') baseLat) (moveLat h' baseLat) : ℝ) ^
        (-(rank : ℝ) / 2) : ℝ) : ℂ)) •
        proj baseLat (proj (moveLat h' baseLat) v)

/-- **SPLIT-SUPPORT VACUUM PROJECTION THEOREM (`split_support_projects_vacuum`)**
(Unconditional Distillation of Alpöge's `WeilRepresentationSplitSupportProjectsVacuum`!):
Given ANY finite set `Q` of split places with commuting split-place group factors `h_i ∈ G` and
localized determinants `y_i ∈ U`, projecting `ω(∏_{i ∈ Q} h_i) v₀` onto the `baseLat`-vacuum
subspace yields an exact nonzero scalar multiple of `v₀`! -/
theorem split_support_projects_vacuum {G H U Lat ι : Type*}
    [Group G] [CommGroup U] [AddCommGroup H] [Module ℂ H] [DecidableEq ι]
    (S : SplitVacuumSystem G H U Lat)
    (v₀ : H) (hv₀ : S.proj S.baseLat v₀ = v₀)
    (Q : Finset ι) (hPart : ι → G) (yPart : ι → U)
    (hcomm : ∀ i ∈ Q, ∀ j ∈ Q, hPart i * hPart j = hPart j * hPart i)
    (hstep_vac : ∀ (F : Finset ι) (hF : F ⊆ Q),
      S.proj (S.moveLat (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hF ha) b (hF hb))) S.baseLat)
        (S.ω (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hF ha) b (hF hb))) v₀) =
      S.ω (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hF ha) b (hF hb))) v₀) :
    ∃ stepIdx : ι → ℕ, (∀ i ∈ Q, 0 < stepIdx i) ∧
      S.proj S.baseLat
          (S.ω (Q.noncommProd hPart (fun a ha b hb _ => hcomm a ha b hb)) v₀) =
        (∏ i ∈ Q, (S.χ (yPart i) : ℂ) *
          (((stepIdx i : ℝ) ^ (-(S.rank : ℝ) / 2) : ℝ) : ℂ)) • v₀ := by
  classical
  have hmain : ∀ (F : Finset ι) (hFQ : F ⊆ Q),
      ∃ stepIdx : ι → ℕ, (∀ i ∈ F, 0 < stepIdx i) ∧
        S.proj S.baseLat
            (S.ω (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hFQ ha) b (hFQ hb))) v₀) =
          (∏ i ∈ F, (S.χ (yPart i) : ℂ) *
            (((stepIdx i : ℝ) ^ (-(S.rank : ℝ) / 2) : ℝ) : ℂ)) • v₀ := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro hFQ
      refine ⟨fun _ => 1, fun _ _ => Nat.zero_lt_one, ?_⟩
      have hempty : (∅ : Finset ι).noncommProd hPart
          (fun a ha b hb _ => hcomm a (hFQ ha) b (hFQ hb)) = 1 :=
        Finset.noncommProd_empty hPart _
      rw [hempty, map_one, Module.End.one_apply, hv₀, Finset.prod_empty, one_smul]
    | @insert a F ha ih =>
      intro hFQ
      have hsub : F ⊆ Q := fun x hx => hFQ (Finset.mem_insert_of_mem hx)
      obtain ⟨idxF, hposF, hEqF⟩ := ih hsub
      set hF : G := F.noncommProd hPart (fun x hx y hy _ => hcomm x (hsub hx) y (hsub hy))
      have hprod : (insert a F).noncommProd hPart
          (fun x hx y hy _ => hcomm x (hFQ hx) y (hFQ hy)) = hPart a * hF :=
        Finset.noncommProd_insert_of_notMem F a hPart
          (fun x hx y hy _ => hcomm x (hFQ hx) y (hFQ hy)) ha
      set d_a : ℕ := S.idx (S.moveLat (hPart a * hF) S.baseLat) (S.moveLat hF S.baseLat)
      let idxNew : ι → ℕ := fun i => if i = a then d_a else idxF i
      refine ⟨idxNew, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiF
        · simp [idxNew, d_a, S.idx_pos]
        · have hia : i ≠ a := fun h => ha (h ▸ hiF)
          simpa [idxNew, hia] using hposF i hiF
      · rw [hprod, map_mul, Module.End.mul_apply, ← hstep_vac F hsub,
          S.local_step (hPart a) hF (yPart a) (S.ω hF v₀),
          hstep_vac F hsub, hEqF, smul_smul, Finset.prod_insert ha]
        congr 1
        simp only [idxNew, if_pos rfl]
        congr 1
        refine Finset.prod_congr rfl fun i hiF => ?_
        have hia : i ≠ a := fun h => ha (h ▸ hiF)
        simp [hia]
  exact hmain Q Finset.Subset.rfl

/-- Exact vacuum matrix coefficient & strict nonvanishing corollary of `split_support_projects_vacuum`. -/
theorem split_support_vacuum_matrix_coeff {G H U Lat ι : Type*}
    [Group G] [CommGroup U] [AddCommGroup H] [Module ℂ H] [DecidableEq ι]
    (S : SplitVacuumSystem G H U Lat)
    (v₀ : H) (hv₀ : S.proj S.baseLat v₀ = v₀) (hv₀_ne : v₀ ≠ 0)
    (ip : H → H → ℂ)
    (hip_smul : ∀ (c : ℂ) (x y : H), ip x (c • y) = c * ip x y)
    (hselfadj : ∀ x y : H, ip (S.proj S.baseLat x) y = ip x (S.proj S.baseLat y))
    (Q : Finset ι) (hPart : ι → G) (yPart : ι → U)
    (hcomm : ∀ i ∈ Q, ∀ j ∈ Q, hPart i * hPart j = hPart j * hPart i)
    (hstep_vac : ∀ (F : Finset ι) (hF : F ⊆ Q),
      S.proj (S.moveLat (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hF ha) b (hF hb))) S.baseLat)
        (S.ω (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hF ha) b (hF hb))) v₀) =
      S.ω (F.noncommProd hPart (fun a ha b hb _ => hcomm a (hF ha) b (hF hb))) v₀) :
    ∃ stepIdx : ι → ℕ, (∀ i ∈ Q, 0 < stepIdx i) ∧
      ip v₀ (S.ω (Q.noncommProd hPart (fun a ha b hb _ => hcomm a ha b hb)) v₀) =
        (∏ i ∈ Q, (S.χ (yPart i) : ℂ) *
          (((stepIdx i : ℝ) ^ (-(S.rank : ℝ) / 2) : ℝ) : ℂ)) * ip v₀ v₀ ∧
      S.proj S.baseLat
        (S.ω (Q.noncommProd hPart (fun a ha b hb _ => hcomm a ha b hb)) v₀) ≠ 0 := by
  obtain ⟨stepIdx, hpos, hproj⟩ :=
    split_support_projects_vacuum S v₀ hv₀ Q hPart yPart hcomm hstep_vac
  refine ⟨stepIdx, hpos, ?_, ?_⟩
  · calc ip v₀ (S.ω (Q.noncommProd hPart (fun a ha b hb _ => hcomm a ha b hb)) v₀)
        = ip (S.proj S.baseLat v₀)
            (S.ω (Q.noncommProd hPart (fun a ha b hb _ => hcomm a ha b hb)) v₀) := by rw [hv₀]
      _ = ip v₀ (S.proj S.baseLat
            (S.ω (Q.noncommProd hPart (fun a ha b hb _ => hcomm a ha b hb)) v₀)) :=
            hselfadj _ _
      _ = (∏ i ∈ Q, (S.χ (yPart i) : ℂ) *
            (((stepIdx i : ℝ) ^ (-(S.rank : ℝ) / 2) : ℝ) : ℂ)) * ip v₀ v₀ := by
            rw [hproj, hip_smul]
  · rw [hproj]
    refine smul_ne_zero ?_ hv₀_ne
    refine Finset.prod_ne_zero_iff.mpr fun i hi => mul_ne_zero (Circle.coe_ne_zero _) ?_
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (hpos i hi)) _).ne'

/-- **Concrete Global `p`-Adic Split-Support Vacuum Projection (`adelic_padic_split_vacuum_coeff`)**:
`⟨φ₀, ω(g) φ₀⟩_𝔸 = (1 / 2) · exp(i θ_∞) · ∏_{p ∈ g.ramPrimes} χ_p(a_p) · p^{-|v_p(a_p)| / 2}`! -/
theorem adelic_padic_split_vacuum_coeff (g : AdelicWeilElement) :
    let hA : IsArchSchwartz (realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
        (-Real.sin g.thetaInf) (Real.cos g.thetaInf) adelicVacuum.fInf) := by
      change IsArchSchwartz (realWeilOp _ _ _ _ stdGauss)
      rw [gauss_vacuum_eigenvalue]
      exact isArchSchwartz_const_mul _ stdGauss_isArchSchwartz
    adelicPureInner adelicVacuum (adelicWeilAct g adelicVacuum hA) =
      (1 / 2 : ℂ) * Complex.exp (Complex.I * (g.thetaInf : ℂ)) *
        ∏ p ∈ g.ramPrimes,
          (g.chiFin p (g.aFin p) : ℂ) *
            (((p.1 : ℝ) ^ (-((|(g.aFin p).1.valuation| : ℤ) : ℝ) / 2) : ℝ) : ℂ) := by
  intro hA
  unfold adelicPureInner adelicWeilAct adelicVacuum
  simp only [Finset.empty_union]
  have harch : archInner stdGauss
      (realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
        (-Real.sin g.thetaInf) (Real.cos g.thetaInf) stdGauss) =
      (1 / 2 : ℂ) * Complex.exp (Complex.I * (g.thetaInf : ℂ)) := by
    rw [gauss_vacuum_eigenvalue]
    unfold archInner
    have hrew : (fun z => star (stdGauss z) * ((Complex.exp (Complex.I * (g.thetaInf : ℂ)) • stdGauss) z)) =
        fun z => Complex.exp (Complex.I * (g.thetaInf : ℂ)) * (star (stdGauss z) * stdGauss z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [hrew, integral_const_mul]
    change Complex.exp (Complex.I * (g.thetaInf : ℂ)) * archInner stdGauss stdGauss = _
    rw [archInner_stdGauss_self, mul_comm]
  rw [harch]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  exact padicInner_spherical_levi p.1 (g.chiFin p) (g.aFin p)

/-- **Concrete Finite-Field Vacuum Projection Bridge (`Stage2WeilMetaplectic`)**. -/
theorem finiteField_vacuum_proj_eq {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (g : Heis 𝔽 n) :
    heisVacuumProj (schrodingerRep ψ) (schrodingerRep ψ g (deltaVec 0)) =
      if g.a = 0 then ψ g.z • deltaVec 0 else 0 := by
  have hP : heisVacuumProj (schrodingerRep (n := n) ψ) = coordProj (n := n) ψ 0 := by
    ext f x
    simp only [heisVacuumProj, coordProj, LinearMap.smul_apply, LinearMap.sum_apply,
      schrodingerRep_mod, dotProd_zero_right, neg_zero, AddChar.map_zero_eq_one, one_smul]
  rw [hP, coordProj_apply ψ hψ 0]
  change (ψ g.z * (ψ (dotProd g.b 0) * deltaVec (0 : Fin n → 𝔽) (0 + g.a))) • deltaVec 0 = _
  simp only [dotProd_zero_right, AddChar.map_zero_eq_one, one_mul, zero_add, deltaVec_apply]
  by_cases ha : g.a = 0
  · simp [ha]
  · simp [ha]

end SplitSupportVacuumProjection

/-! ## Section 6: Wave-2 Readiness Bridges (`AdelicWeilTheta`, `SiegelEisenstein`, `DoublingZeta`) -/

section Wave2Interfaces

/-- **Siegel Parabolic Section Datum** (matching Alpöge's `StdUnn.sect`):
`sect H Φ s g = H(g)^{s - s₀} · (ω(g) Φ)(0)` for Wave 2 `Stage14M1_SiegelEisenstein`. -/
def siegelSection {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ω : G →* Module.End ℂ V) (evalZero : V → ℂ) (H : G → ℝ≥0) (s0 : ℂ)
    (Φ : V) (s : ℂ) (g : G) : ℂ :=
  ((H g : ℝ) : ℂ) ^ (s - s0) * evalZero (ω g Φ)

theorem siegelSection_one {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ω : G →* Module.End ℂ V) (evalZero : V → ℂ) (H : G → ℝ≥0) (hH1 : H 1 = 1) (s0 : ℂ)
    (Φ : V) (s : ℂ) :
    siegelSection ω evalZero H s0 Φ s 1 = evalZero Φ := by
  unfold siegelSection
  rw [hH1, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul, map_one,
    Module.End.one_apply]

theorem siegelSection_right_compact_eigen {ι : Type*} {v : ι} (W : LocalWeilRep v)
    (evalZero : W.Space →ₗ[ℂ] ℂ) (H : W.Grp → ℝ≥0) (s0 : ℂ)
    (hH : ∀ g, ∀ k ∈ W.compactSubgroup, H (g * k) = H g)
    (s : ℂ) (g : W.Grp) {k : W.Grp} (hk : k ∈ W.compactSubgroup) :
    ∃ χ : Circle,
      siegelSection W.rep evalZero H s0 W.vacuum s (g * k) =
        (χ : ℂ) * siegelSection W.rep evalZero H s0 W.vacuum s g := by
  obtain ⟨χ, hχ⟩ := W.vacuum_eigen k hk
  refine ⟨χ, ?_⟩
  unfold siegelSection
  rw [hH g k hk, map_mul, Module.End.mul_apply, hχ, map_smul, map_smul, smul_eq_mul]
  ring

/-- **Adelic / Local Theta Kernel Datum** (matching Alpöge's `StdUnn.theta`). -/
def thetaKernel {G H A Ξ : Type*} [Group G] [Group H]
    [AddCommGroup (A → ℂ)] [Module ℂ (A → ℂ)]
    (ω : G →* Module.End ℂ (A → ℂ)) (rat : Ξ → A) (act : H → A → A)
    (Φ : A → ℂ) (g : G) (h : H) : ℂ :=
  ∑' ξ : Ξ, ω g Φ (act h⁻¹ (rat ξ))

/-- **Direct Bridge to `Stage11DoublingRallis`**. -/
theorem weil_doubling_bridge {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ : EuclideanSpace ℂ G) :
    LinearMap.adjoint (doublingGramOp Θ) = doublingGramOp Θ ∧
    0 ≤ (inner ℂ (thetaLiftLin Θ φ) (thetaLiftLin Θ φ)).re ∧
    (thetaLiftLin Θ φ ≠ 0 ↔ 0 < (inner ℂ (doublingGramOp Θ φ) φ).re) :=
  ⟨doublingGramOp_self_adjoint Θ,
    (rallis_inner_product_nonneg Θ φ).1,
    theta_lift_ne_zero_iff_doubling_pos Θ φ⟩

/-- **Unified Wave-1 Export Package `SchrodingerFockPackage`** for downstream Wave 2 consumption
(`AdelicWeilTheta`, `SiegelEisenstein`, `DoublingZeta`). -/
structure SchrodingerFockPackage where
  archRep : LocalWeilRep LocalPlace.arch
  padicRep : ∀ p : Nat.Primes, ((ℚ_[p.1])ˣ →* Circle) → LocalWeilRep (LocalPlace.finite p)
  fockModel : ∀ d : ℕ, ArchFockModel d
  vacuumAdelic : AdelicPureTensor
  vacuum_mem_SB : vacuumAdelic.eval ∈ SchwartzBruhatAdelic
  vacuum_eval_zero : vacuumAdelic.eval (0, 0) = 1
  vacuum_norm_sq : adelicPureInner vacuumAdelic vacuumAdelic = 1 / 2
  gauss_eigen : ∀ θ : ℝ,
    realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ) (Real.cos θ) stdGauss =
      Complex.exp (Complex.I * (θ : ℂ)) • stdGauss

def canonicalSchrodingerFockPackage : SchrodingerFockPackage where
  archRep := archLocalWeilRep
  padicRep p χ := padicLocalWeilRep p χ
  fockModel _ := ⟨1, zero_lt_one⟩
  vacuumAdelic := adelicVacuum
  vacuum_mem_SB := adelicVacuum_mem_schwartzBruhatAdelic
  vacuum_eval_zero := adelicVacuum_eval_zero
  vacuum_norm_sq := adelicPureInner_vacuum_self
  gauss_eigen := gauss_vacuum_eigenvalue

end Wave2Interfaces

end RHDirect.Stage14M1_SchrodingerFockModel

end
