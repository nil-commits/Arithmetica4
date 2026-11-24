import RHDirect.Stage3ExplicitSpectral
import RHDirect.Stage3ThetaSiegelBridge
import RHDirect.Stage3AutomorphicDescent
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Fintype.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# RHDirect.Stage4SelbergTrace

Stage 4 deep mathematical formalization of the **Finite & Compact-Quotient Selberg–Arthur Trace
Formula, Orbital Integral Expansion, Jacquet–Langlands & Cyclic Base-Change Spectral Transfer,
and Multi-Dimensional Lattice Poisson Summation / Theta Functional Equation / Flat-Torus Weyl Law**
in pure Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Contents

1. **Exact Finite-Quotient Selberg–Arthur Trace Formula (`Γ \ G`)**:
   - Automorphic Hilbert space `AutomorphicL2 G Γ := EuclideanSpace ℂ (RightCosetSpace G Γ)` on the
     right-coset quotient `Γ \ G = Quotient (QuotientGroup.rightRel Γ)`, with canonical orthonormal
     delta basis `cosetOrthonormalBasis` and unitary right-regular representation `rightRegRep G Γ`.
   - Right-regular automorphic convolution operator `(rightConvOp G Γ f φ)(x) = ∑_{g ∈ G} f(g) φ(x g)`,
     convolution algebra homomorphism (`rightConvOp_comp`), Hilbert adjoint (`rightConvOp_adjoint`),
     Hermiticity for self-adjoint kernels (`rightConvOp_isSymmetric_of_selfAdj`), and exact
     automorphic kernel matrix entries (`automorphicKernel`, `rightConvOp_apply_eq_sum_kernel`).
   - Exact **Geometric Side** & **Orbital Integral Expansion**:
     * Coset diagonal form: `Tr(R(f)) = ∑_{x ∈ Γ \ G} ∑_{γ ∈ Γ} f(x⁻¹ γ x)`.
     * Group-averaged form: `Tr(R(f)) = |Γ|⁻¹ ∑_{γ ∈ Γ} ∑_{x ∈ G} f(x⁻¹ γ x)`.
     * Centralizer-weighted conjugacy-class form:
       `Tr(R(f)) = ∑_{[γ] ∈ Conj(Γ)} |Z_Γ(γ)|⁻¹ · ∑_{x ∈ G} f(x⁻¹ γ x)`.
     * Canonical **Arthur–Selberg Volume × Orbital Integral Formula**:
       `Tr(R(f)) = ∑_{[γ] ∈ Conj(Γ)} (|Z_G(γ)| / |Z_Γ(γ)|) · O_γ(f)` where
       `O_γ(f) = ∑_{x ∈ Z_G(γ) \ G} f(x⁻¹ γ x) = |Z_G(γ)|⁻¹ ∑_{x ∈ G} f(x⁻¹ γ x)`.
     * `|Γ| / |Z_Γ(γ)|`-weighted conjugacy-class form and exact identity-term extraction
       (`O_1(f) = f(1)`, `Tr(R(δ_1)) = |G| / |Γ|`).
   - Exact **Spectral Side** & **Full Selberg–Arthur Trace Formula**:
     * For any Peter–Weyl / isotypic `SpectralDecomposition G Γ ι` with representations `π_i` and
       multiplicities `m_i`, `Tr(R(f)) = ∑_i m_i · Tr(π_i(f)) = geomSide G Γ f`.
     * For any self-adjoint test kernel `f`, unconditional spectral-theorem eigenbasis identity
       `∑_k λ_k = geomSide G Γ f` with real eigenvalues `λ_k ∈ ℝ`, plus Bochner curvature spectral
       gap transfer on `L²(Γ \ G)` via `Stage3ExplicitSpectral.bochner_spectral_gap_symmetric`.

2. **Simple Jacquet–Langlands & Cyclic Base-Change Spectral Transfer Principle**:
   - Group `L²`-character inner product `charInner`, orthogonal/orthonormal character families
     (`IsOrthogonalChars`, `IsOrthonormalChars`), Schur Fourier coefficient extraction
     (`charInner_linearComb`), and unconditional linear independence
     (`eq_of_forall_test_orthogonalChars`).
   - Concrete orthonormal character families bridging `Stage2WeilMetaplectic` (`sum_psi_dotProd`)
     and `Stage3AutomorphicDescent` (`zmodChar_sum_dual`), plus arbitrary finite-group 1D characters
     (`homChar_orthonormal`).
   - Unconditional **Jacquet–Langlands Spectral Transfer** (both same-group conjugacy-matching and
     general cross-group test-function correspondence `f ↦ f'` with matching geometric sides and
     local character transfer): matching orbital integrals imply matching spectral traces AND
     identical automorphic multiplicities `m₁(π) = m₂(π')`!
   - **Cyclic Base-Change Twisted Trace Identity**: for prime-order `η : G →* ℂˣ`,
     `∑_{j : Fin p} Tr(R(η^j · f)) = p · Tr(R(1_{ker η} · f))`.

3. **1D & `n`-D Lattice Poisson Summation, Theta Functional Equation & Flat-Torus Weyl Law**:
   - 1D scaled Gaussian Poisson summation (`theta1D_functional_eq`) directly from Mathlib's
     `Real.tsum_exp_neg_mul_int_sq`, and rank-1 lattice identity (`latticeTheta_span_singleton_functional_eq`).
   - Canonical dual lattice `dualLattice L`, orthogonal-basis dualization (`dualBasis`), biduality
     `(L*)* = L`, and exact covolume product & duality formulas
     (`covol_of_orthogonalBasis`, `covol_dualLattice_of_orthogonalBasis`).
   - Exact **Multi-Dimensional Orthogonal-Lattice Theta Functional Equation** (`latticeTheta_functional_eq_orthogonal`):
     `Θ_L(t) = t^{-r/2} · covol(L)⁻¹ · Θ_{L*}(t⁻¹)` for every discrete orthogonal lattice `L ⊂ E`
     and every `t > 0`, directly on `Stage3ThetaSiegelBridge.latticeTheta` and `ArakelovCovolume.covol`.
   - Direct bridge to `Stage3ExplicitSpectral.DiscreteSpectrum` (`torusSpectrum`, `torusLaplacianSpectrum`):
     * Exact `t^{-r/2}` heat-kernel asymptotics as `t → 0⁺` (`torusSpectrum_heatTrace_asymptotic`,
       `torusLaplacian_heatTrace_asymptotic`).
     * Non-asymptotic and sharp asymptotic **Flat-Torus Weyl Laws** via
       `Stage3ExplicitSpectral.DiscreteSpectrum.weyl_upper_bound` and `weyl_upper_bound_optimal`:
       `N(Λ) ≤ e · covol(L)⁻¹ · Θ_{L*}(Λ) · Λ^{r/2}` for all `Λ > 0`,
       `N(Λ) ≤ (e + ε) · covol(L)⁻¹ · Λ^{r/2}` eventually for every `ε > 0`,
       and sharp `N_{-Δ}(Λ) ≤ e · covol(L) · Λ^{r/2}` (resp. `e · covol(L)⁻¹ · Λ^{r/2}` on the
       dual torus) for all sufficiently large `Λ`, plus short-interval Gaussian wave-kernel
       window bounds (`torusSpectrum_windowCount_bound`).
-/

open Finset Real Filter MeasureTheory Module Submodule
open RHDirect RHDirect.ArakelovCovolume RHDirect.Stage3ExplicitSpectral
open RHDirect.Stage3ThetaSiegelBridge
open scoped BigOperators InnerProductSpace Matrix ComplexConjugate Topology

namespace RHDirect.Stage4SelbergTrace

noncomputable section

/-! ## Section 1: Exact Finite-Quotient Selberg–Arthur Trace Formula (`Γ \ G`) -/

section FiniteSelbergTrace

variable {G : Type*} [Group G]

/-- Right-coset quotient `Γ \ G = { Γ x | x ∈ G }`, realized via `QuotientGroup.rightRel Γ`
where `x ~ y ↔ y * x⁻¹ ∈ Γ`. -/
abbrev RightCosetSpace (G : Type*) [Group G] (Γ : Subgroup G) : Type _ :=
  Quotient (QuotientGroup.rightRel Γ)

/-- Canonical projection `G → Γ \ G`. -/
def rightCosetMk (Γ : Subgroup G) (x : G) : RightCosetSpace G Γ :=
  Quotient.mk (QuotientGroup.rightRel Γ) x

@[simp]
lemma rightCosetMk_eq_iff (Γ : Subgroup G) {x y : G} :
    rightCosetMk Γ x = rightCosetMk Γ y ↔ y * x⁻¹ ∈ Γ := by
  change Quotient.mk (QuotientGroup.rightRel Γ) x = Quotient.mk (QuotientGroup.rightRel Γ) y ↔ _
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

lemma rightCosetMk_mul_left (Γ : Subgroup G) {γ : G} (hγ : γ ∈ Γ) (x : G) :
    rightCosetMk Γ (γ * x) = rightCosetMk Γ x := by
  rw [rightCosetMk_eq_iff]
  have h : x * (γ * x)⁻¹ = γ⁻¹ := by group
  rw [h]
  exact Γ.inv_mem hγ

/-- Well-defined right multiplication `(Γ x) · g = Γ (x g)` on `Γ \ G`. -/
def rightCosetMul {Γ : Subgroup G} (q : RightCosetSpace G Γ) (g : G) : RightCosetSpace G Γ :=
  Quotient.liftOn q (fun x => rightCosetMk Γ (x * g)) fun x y hxy => by
    have hmem : y * x⁻¹ ∈ Γ := (QuotientGroup.rightRel_apply).mp hxy
    rw [rightCosetMk_eq_iff]
    have heq : (y * g) * (x * g)⁻¹ = y * x⁻¹ := by group
    rwa [heq]

@[simp]
lemma rightCosetMul_mk (Γ : Subgroup G) (x g : G) :
    rightCosetMul (rightCosetMk Γ x) g = rightCosetMk Γ (x * g) := rfl

@[simp]
lemma rightCosetMul_one {Γ : Subgroup G} (q : RightCosetSpace G Γ) :
    rightCosetMul q 1 = q := by
  refine Quotient.inductionOn q fun x => ?_
  change rightCosetMul (rightCosetMk Γ x) 1 = rightCosetMk Γ x
  rw [rightCosetMul_mk, mul_one]

lemma rightCosetMul_mul {Γ : Subgroup G} (q : RightCosetSpace G Γ) (g₁ g₂ : G) :
    rightCosetMul (rightCosetMul q g₁) g₂ = rightCosetMul q (g₁ * g₂) := by
  refine Quotient.inductionOn q fun x => ?_
  change rightCosetMul (rightCosetMul (rightCosetMk Γ x) g₁) g₂ =
    rightCosetMul (rightCosetMk Γ x) (g₁ * g₂)
  rw [rightCosetMul_mk, rightCosetMul_mk, rightCosetMul_mk, mul_assoc]

/-- Right multiplication by `g : G` is a bijection on `Γ \ G`. -/
def rightCosetMulEquiv (Γ : Subgroup G) (g : G) :
    RightCosetSpace G Γ ≃ RightCosetSpace G Γ where
  toFun q := rightCosetMul q g
  invFun q := rightCosetMul q g⁻¹
  left_inv q := by dsimp only; rw [rightCosetMul_mul, mul_inv_cancel, rightCosetMul_one]
  right_inv q := by dsimp only; rw [rightCosetMul_mul, inv_mul_cancel, rightCosetMul_one]

lemma rightCosetMul_bijective (Γ : Subgroup G) (g : G) :
    Function.Bijective (fun q : RightCosetSpace G Γ => rightCosetMul q g) :=
  (rightCosetMulEquiv Γ g).bijective

/-- Representative `rep q ∈ G` of a right coset `q ∈ Γ \ G` satisfying `rightCosetMk Γ (rep q) = q`. -/
def cosetRep {Γ : Subgroup G} (q : RightCosetSpace G Γ) : G :=
  Quotient.out q

@[simp]
lemma rightCosetMk_cosetRep {Γ : Subgroup G} (q : RightCosetSpace G Γ) :
    rightCosetMk Γ (cosetRep q) = q :=
  Quotient.out_eq q

/-- Every `x : G` splits uniquely as `x = γ * cosetRep (Γ x)` with `γ ∈ Γ`. -/
def groupEquivSubgroupProdRightCoset (Γ : Subgroup G) :
    G ≃ (Γ × RightCosetSpace G Γ) where
  toFun x :=
    (⟨x * (cosetRep (rightCosetMk Γ x))⁻¹, by
      have h : rightCosetMk Γ (cosetRep (rightCosetMk Γ x)) = rightCosetMk Γ x :=
        rightCosetMk_cosetRep _
      exact (rightCosetMk_eq_iff Γ).mp h⟩,
     rightCosetMk Γ x)
  invFun p := (p.1 : G) * cosetRep p.2
  left_inv x := by
    dsimp only
    group
  right_inv p := by
    rcases p with ⟨⟨γ, hγ⟩, q⟩
    have hmk : rightCosetMk Γ (γ * cosetRep q) = q := by
      rw [rightCosetMk_mul_left Γ hγ, rightCosetMk_cosetRep]
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      rw [hmk]
      group
    · exact hmk

/-- **Lagrange's Cardinality Identity for `Γ \ G`**: `|Γ| * |Γ \ G| = |G|`. -/
theorem card_subgroup_mul_card_rightCosetSpace [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] :
    Fintype.card Γ * Fintype.card (RightCosetSpace G Γ) = Fintype.card G := by
  have h := Fintype.card_congr (groupEquivSubgroupProdRightCoset Γ)
  rw [Fintype.card_prod] at h
  exact h.symm

/-- **Master Fiberwise Group Summation over `Γ \ G`**:
for any `ψ : G → ℂ`, `∑ x : G, ψ x = ∑ q : Γ \ G, ∑ γ : Γ, ψ (γ * cosetRep q)`. -/
theorem sum_group_eq_sum_rightCoset_sum_subgroup [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] (ψ : G → ℂ) :
    ∑ x : G, ψ x = ∑ q : RightCosetSpace G Γ, ∑ γ : Γ, ψ ((γ : G) * cosetRep q) := by
  calc ∑ x : G, ψ x
      = ∑ p : Γ × RightCosetSpace G Γ, ψ ((p.1 : G) * cosetRep p.2) := by
          refine Fintype.sum_equiv (groupEquivSubgroupProdRightCoset Γ) _ _ fun x => ?_
          congr 1
          exact ((groupEquivSubgroupProdRightCoset Γ).left_inv x).symm
    _ = ∑ γ : Γ, ∑ q : RightCosetSpace G Γ, ψ ((γ : G) * cosetRep q) :=
          Fintype.sum_prod_type _
    _ = ∑ q : RightCosetSpace G Γ, ∑ γ : Γ, ψ ((γ : G) * cosetRep q) :=
          Finset.sum_comm

/-- **Left-Invariant Group Summation Reduction**:
if `ψ (γ * x) = ψ x` for all `γ ∈ Γ` and `x ∈ G`, then
`∑ x : G, ψ x = |Γ| * ∑ q : Γ \ G, ψ (cosetRep q)`. -/
theorem sum_group_eq_card_subgroup_mul_sum_rightCoset [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] (ψ : G → ℂ)
    (hinv : ∀ γ ∈ Γ, ∀ x : G, ψ (γ * x) = ψ x) :
    ∑ x : G, ψ x = (Fintype.card Γ : ℂ) * ∑ q : RightCosetSpace G Γ, ψ (cosetRep q) := by
  rw [sum_group_eq_sum_rightCoset_sum_subgroup Γ ψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  calc ∑ γ : Γ, ψ ((γ : G) * cosetRep q)
      = ∑ _γ : Γ, ψ (cosetRep q) := Finset.sum_congr rfl fun γ _ => hinv γ γ.2 (cosetRep q)
    _ = (Fintype.card Γ : ℂ) * ψ (cosetRep q) := by simp [nsmul_eq_mul]

/-- The finite-dimensional automorphic Hilbert space `L²(Γ \ G) = EuclideanSpace ℂ (Γ \ G)`. -/
abbrev AutomorphicL2 (G : Type*) [Group G] (Γ : Subgroup G) : Type _ :=
  EuclideanSpace ℂ (RightCosetSpace G Γ)

/-- Standard orthonormal delta basis of `L²(Γ \ G)`. -/
def cosetOrthonormalBasis [Fintype G] (Γ : Subgroup G) [Fintype (RightCosetSpace G Γ)] :
    OrthonormalBasis (RightCosetSpace G Γ) ℂ (AutomorphicL2 G Γ) :=
  EuclideanSpace.basisFun (RightCosetSpace G Γ) ℂ

/-- Coordinate inner product on `L²(Γ \ G)`. -/
theorem automorphicL2_inner_eq [Fintype G] (Γ : Subgroup G) [Fintype (RightCosetSpace G Γ)]
    (φ ψ : AutomorphicL2 G Γ) :
    inner ℂ φ ψ = ∑ q : RightCosetSpace G Γ, star (φ q) * ψ q := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [RCLike.inner_apply, mul_comm, Complex.star_def]

/-- Dimension of `L²(Γ \ G)` equals `|Γ \ G|`. -/
theorem finrank_automorphicL2 [Fintype G] (Γ : Subgroup G) [Fintype (RightCosetSpace G Γ)] :
    Module.finrank ℂ (AutomorphicL2 G Γ) = Fintype.card (RightCosetSpace G Γ) :=
  finrank_euclideanSpace

/-- Right-translation unitary operator `(R(g) φ)(q) = φ(q · g)` on `L²(Γ \ G)`. -/
def rightRegOp (Γ : Subgroup G) (g : G) :
    AutomorphicL2 G Γ →ₗ[ℂ] AutomorphicL2 G Γ where
  toFun φ := WithLp.toLp 2 (fun q => φ (rightCosetMul q g))
  map_add' _ _ := by ext q; rfl
  map_smul' _ _ := by ext q; rfl

@[simp]
lemma rightRegOp_apply (Γ : Subgroup G) (g : G) (φ : AutomorphicL2 G Γ)
    (q : RightCosetSpace G Γ) :
    rightRegOp Γ g φ q = φ (rightCosetMul q g) := rfl

/-- The right-regular representation `R : G →* End ℂ (L²(Γ \ G))`. -/
def rightRegRep (Γ : Subgroup G) :
    G →* Module.End ℂ (AutomorphicL2 G Γ) where
  toFun g := rightRegOp Γ g
  map_one' := by
    apply LinearMap.ext; intro φ; ext q
    simp [rightRegOp_apply]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext; intro φ; ext q
    change φ (rightCosetMul q (g₁ * g₂)) = φ (rightCosetMul (rightCosetMul q g₁) g₂)
    rw [rightCosetMul_mul]

/-- Right translation `R(g)` is unitary on `L²(Γ \ G)`. -/
theorem rightRegOp_unitary [Fintype G] (Γ : Subgroup G) [Fintype (RightCosetSpace G Γ)]
    (g : G) (φ ψ : AutomorphicL2 G Γ) :
    inner ℂ (rightRegOp Γ g φ) (rightRegOp Γ g ψ) = inner ℂ φ ψ := by
  rw [automorphicL2_inner_eq, automorphicL2_inner_eq]
  exact Fintype.sum_equiv (rightCosetMulEquiv Γ g) _ _ fun _ => rfl

/-- Group convolution `(f₁ * f₂)(g) = ∑ h : G, f₁ h * f₂ (h⁻¹ * g)`. -/
def groupConv [Fintype G] (f₁ f₂ : G → ℂ) (g : G) : ℂ :=
  ∑ h : G, f₁ h * f₂ (h⁻¹ * g)

/-- Involution `f*(g) = star (f g⁻¹)` on the group convolution algebra `ℂ[G]`. -/
def conjInv (f : G → ℂ) (g : G) : ℂ :=
  star (f g⁻¹)

/-- **Right-Regular Automorphic Convolution Operator `R(f)` on `L²(Γ \ G)`**:
`(R(f) φ)(q) = ∑_{g ∈ G} f(g) · φ(q · g)`. -/
def rightConvOp [Fintype G] (Γ : Subgroup G) (f : G → ℂ) :
    AutomorphicL2 G Γ →ₗ[ℂ] AutomorphicL2 G Γ :=
  ∑ g : G, f g • rightRegOp Γ g

theorem rightConvOp_apply [Fintype G] (Γ : Subgroup G) (f : G → ℂ)
    (φ : AutomorphicL2 G Γ) (q : RightCosetSpace G Γ) :
    rightConvOp Γ f φ q = ∑ g : G, f g * φ (rightCosetMul q g) := by
  unfold rightConvOp
  rw [LinearMap.sum_apply]
  have hsum : ∀ (s : Finset G) (F : G → AutomorphicL2 G Γ),
      (∑ g ∈ s, F g) q = ∑ g ∈ s, F g q := by
    classical
    intro s F
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]
  rw [hsum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rfl

theorem rightConvOp_add [Fintype G] (Γ : Subgroup G) (f₁ f₂ : G → ℂ) :
    rightConvOp Γ (f₁ + f₂) = rightConvOp Γ f₁ + rightConvOp Γ f₂ := by
  unfold rightConvOp
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem rightConvOp_smul [Fintype G] (Γ : Subgroup G) (c : ℂ) (f : G → ℂ) :
    rightConvOp Γ (c • f) = c • rightConvOp Γ f := by
  unfold rightConvOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [smul_smul]

/-- **Convolution Algebra Homomorphism**: `R(f₁) ∘ R(f₂) = R(f₁ * f₂)`. -/
theorem rightConvOp_comp [Fintype G] (Γ : Subgroup G) (f₁ f₂ : G → ℂ) :
    rightConvOp Γ f₁ ∘ₗ rightConvOp Γ f₂ = rightConvOp Γ (groupConv f₁ f₂) := by
  apply LinearMap.ext; intro φ; ext q
  rw [LinearMap.comp_apply, rightConvOp_apply, rightConvOp_apply]
  simp_rw [rightConvOp_apply, Finset.mul_sum]
  calc ∑ h : G, ∑ k : G, f₁ h * (f₂ k * φ (rightCosetMul (rightCosetMul q h) k))
      = ∑ h : G, ∑ g : G, f₁ h * f₂ (h⁻¹ * g) * φ (rightCosetMul q g) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun k => ?_
          change f₁ h * (f₂ k * φ (rightCosetMul (rightCosetMul q h) k)) =
            f₁ h * f₂ (h⁻¹ * (h * k)) * φ (rightCosetMul q (h * k))
          rw [inv_mul_cancel_left, rightCosetMul_mul, mul_assoc]
    _ = ∑ g : G, ∑ h : G, f₁ h * f₂ (h⁻¹ * g) * φ (rightCosetMul q g) := Finset.sum_comm
    _ = ∑ g : G, groupConv f₁ f₂ g * φ (rightCosetMul q g) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [← Finset.sum_mul]; rfl

/-- **Hilbert Adjoint of `R(f)`**: `R(f)* = R(f*)`, where `f*(g) = star (f g⁻¹)`. -/
theorem rightConvOp_adjoint [Fintype G] (Γ : Subgroup G) [Fintype (RightCosetSpace G Γ)]
    (f : G → ℂ) :
    LinearMap.adjoint (rightConvOp Γ f) = rightConvOp Γ (conjInv f) := by
  apply LinearMap.ext; intro ψ
  refine ext_inner_left ℂ fun φ => ?_
  rw [LinearMap.adjoint_inner_right, automorphicL2_inner_eq, automorphicL2_inner_eq]
  simp_rw [rightConvOp_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc ∑ g : G, ∑ q : RightCosetSpace G Γ, star (φ (rightCosetMul q g)) * star (f g) * ψ q
      = ∑ g : G, ∑ q' : RightCosetSpace G Γ,
          star (φ q') * (star (f g) * ψ (rightCosetMul q' g⁻¹)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          refine Fintype.sum_equiv (rightCosetMulEquiv Γ g) _ _ fun q => ?_
          dsimp only [rightCosetMulEquiv, Equiv.coe_fn_mk]
          rw [rightCosetMul_mul, mul_inv_cancel, rightCosetMul_one]
          ring
    _ = ∑ g' : G, ∑ q' : RightCosetSpace G Γ,
          star (φ q') * (conjInv f g' * ψ (rightCosetMul q' g')) := by
          refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
          refine Finset.sum_congr rfl fun q' _ => ?_
          simp [conjInv]
    _ = ∑ q' : RightCosetSpace G Γ, ∑ g' : G,
          star (φ q') * (conjInv f g' * ψ (rightCosetMul q' g')) := Finset.sum_comm

/-- If `f` is self-adjoint (`∀ g, f g⁻¹ = star (f g)`), then `R(f)` is Hermitian (`IsSymmetric`). -/
theorem rightConvOp_isSymmetric_of_selfAdj [Fintype G] (Γ : Subgroup G)
    [Fintype (RightCosetSpace G Γ)] (f : G → ℂ) (hf : ∀ g : G, f g⁻¹ = star (f g)) :
    (rightConvOp Γ f).IsSymmetric := by
  have hconj : conjInv f = f := by
    funext g
    simp only [conjInv, hf g, star_star]
  intro φ ψ
  rw [← LinearMap.adjoint_inner_right, rightConvOp_adjoint, hconj]

/-- **Automorphic Kernel `K_f(q₁, q₂) = ∑_{γ ∈ Γ} f(rep(q₁)⁻¹ γ rep(q₂))`** on `(Γ \ G) × (Γ \ G)`. -/
def automorphicKernel [Fintype G] (Γ : Subgroup G) [Fintype Γ]
    (f : G → ℂ) (q₁ q₂ : RightCosetSpace G Γ) : ℂ :=
  ∑ γ : Γ, f ((cosetRep q₁)⁻¹ * (γ : G) * cosetRep q₂)

/-- `automorphicKernel` is **independent of the choice of coset representatives**:
`K_f(Γ x₁, Γ x₂) = ∑_{γ ∈ Γ} f(x₁⁻¹ γ x₂)`. -/
theorem automorphicKernel_mk [Fintype G] (Γ : Subgroup G) [Fintype Γ]
    (f : G → ℂ) (x₁ x₂ : G) :
    automorphicKernel Γ f (rightCosetMk Γ x₁) (rightCosetMk Γ x₂) =
      ∑ γ : Γ, f (x₁⁻¹ * (γ : G) * x₂) := by
  unfold automorphicKernel
  have h1 : cosetRep (rightCosetMk Γ x₁) * x₁⁻¹ ∈ Γ :=
    (rightCosetMk_eq_iff Γ).mp (rightCosetMk_cosetRep (rightCosetMk Γ x₁)).symm
  have h2 : cosetRep (rightCosetMk Γ x₂) * x₂⁻¹ ∈ Γ :=
    (rightCosetMk_eq_iff Γ).mp (rightCosetMk_cosetRep (rightCosetMk Γ x₂)).symm
  let γ₁ : Γ := ⟨cosetRep (rightCosetMk Γ x₁) * x₁⁻¹, h1⟩
  let γ₂ : Γ := ⟨cosetRep (rightCosetMk Γ x₂) * x₂⁻¹, h2⟩
  let e : Γ ≃ Γ := (Equiv.mulLeft γ₁⁻¹).trans (Equiv.mulRight γ₂)
  refine Fintype.sum_equiv e _ _ fun γ => ?_
  change f ((cosetRep (rightCosetMk Γ x₁))⁻¹ * (γ : G) * cosetRep (rightCosetMk Γ x₂)) =
    f (x₁⁻¹ * (((γ₁⁻¹ * γ) * γ₂ : Γ) : G) * x₂)
  congr 1
  change (cosetRep (rightCosetMk Γ x₁))⁻¹ * (γ : G) * cosetRep (rightCosetMk Γ x₂) =
    x₁⁻¹ * (((cosetRep (rightCosetMk Γ x₁) * x₁⁻¹)⁻¹ * (γ : G)) *
      (cosetRep (rightCosetMk Γ x₂) * x₂⁻¹)) * x₂
  group

/-- **Integral/Kernel Operator Representation of `R(f)`**:
`(R(f) φ)(q₁) = ∑_{q₂ ∈ Γ \ G} K_f(q₁, q₂) * φ(q₂)`. -/
theorem rightConvOp_apply_eq_sum_kernel [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    (f : G → ℂ) (φ : AutomorphicL2 G Γ) (q₁ : RightCosetSpace G Γ) :
    rightConvOp Γ f φ q₁ =
      ∑ q₂ : RightCosetSpace G Γ, automorphicKernel Γ f q₁ q₂ * φ q₂ := by
  refine Quotient.inductionOn q₁ fun x₁ => ?_
  change rightConvOp Γ f φ (rightCosetMk Γ x₁) = _
  rw [rightConvOp_apply]
  calc ∑ g : G, f g * φ (rightCosetMk Γ (x₁ * g))
      = ∑ h : G, f (x₁⁻¹ * h) * φ (rightCosetMk Γ h) := by
          refine Fintype.sum_equiv (Equiv.mulLeft x₁) _ _ fun g => ?_
          simp
    _ = ∑ q₂ : RightCosetSpace G Γ, ∑ γ : Γ,
          f (x₁⁻¹ * ((γ : G) * cosetRep q₂)) * φ (rightCosetMk Γ ((γ : G) * cosetRep q₂)) :=
          sum_group_eq_sum_rightCoset_sum_subgroup Γ _
    _ = ∑ q₂ : RightCosetSpace G Γ, automorphicKernel Γ f (rightCosetMk Γ x₁) q₂ * φ q₂ := by
          refine Finset.sum_congr rfl fun q₂ _ => ?_
          have hker : automorphicKernel Γ f (rightCosetMk Γ x₁) q₂ =
              ∑ γ : Γ, f (x₁⁻¹ * (γ : G) * cosetRep q₂) := by
            conv_lhs => rw [← rightCosetMk_cosetRep q₂]
            exact automorphicKernel_mk Γ f x₁ (cosetRep q₂)
          rw [hker, Finset.sum_mul]
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [rightCosetMk_mul_left Γ γ.2, rightCosetMk_cosetRep, mul_assoc]

/-- Exact matrix entry of `R(f)` in the orthonormal delta basis of `L²(Γ \ G)`:
`⟨δ_{q₁}, R(f) δ_{q₂}⟩ = K_f(q₁, q₂)`. -/
theorem inner_cosetBasis_rightConvOp [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] [DecidableEq (RightCosetSpace G Γ)]
    (f : G → ℂ) (q₁ q₂ : RightCosetSpace G Γ) :
    inner ℂ (cosetOrthonormalBasis Γ q₁) (rightConvOp Γ f (cosetOrthonormalBasis Γ q₂)) =
      automorphicKernel Γ f q₁ q₂ := by
  have hdelta : ∀ q r : RightCosetSpace G Γ,
      cosetOrthonormalBasis Γ q r = if r = q then 1 else 0 := by
    intro q r
    simp [cosetOrthonormalBasis, EuclideanSpace.basisFun_apply]
  rw [automorphicL2_inner_eq, Finset.sum_eq_single q₁]
  · rw [hdelta q₁ q₁, if_pos rfl, star_one, one_mul, rightConvOp_apply_eq_sum_kernel,
      Finset.sum_eq_single q₂]
    · rw [hdelta q₂ q₂, if_pos rfl, mul_one]
    · intro q _ hq
      rw [hdelta q₂ q, if_neg hq, mul_zero]
    · intro h; exact absurd (Finset.mem_univ q₂) h
  · intro q _ hq
    rw [hdelta q₁ q, if_neg hq, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ q₁) h

/-- Trace of any linear endomorphism on a finite-dimensional inner product space in an
orthonormal basis: `Tr(T) = ∑ i, ⟨e_i, T e_i⟩`. -/
theorem trace_eq_sum_inner_orthonormalBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (e : OrthonormalBasis ι ℂ V) (T : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V T = ∑ i : ι, inner ℂ (e i) (T (e i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ e.toBasis T, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis]

/-- **Pre-Trace Exact Geometric Side (Coset Diagonal Sum)**:
`Tr(R(f) | L²(Γ \ G)) = ∑_{q ∈ Γ \ G} ∑_{γ ∈ Γ} f(rep(q)⁻¹ γ rep(q))`. -/
theorem trace_rightConvOp_eq_sum_coset [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] (f : G → ℂ) :
    LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) =
      ∑ q : RightCosetSpace G Γ, ∑ γ : Γ, f ((cosetRep q)⁻¹ * (γ : G) * cosetRep q) := by
  classical
  rw [trace_eq_sum_inner_orthonormalBasis (cosetOrthonormalBasis Γ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact inner_cosetBasis_rightConvOp Γ f q q

/-- **Pre-Trace Exact Geometric Side (Group-Averaged Double Sum)**:
`Tr(R(f) | L²(Γ \ G)) = |Γ|⁻¹ ∑_{γ ∈ Γ} ∑_{x ∈ G} f(x⁻¹ γ x)`. -/
theorem trace_rightConvOp_eq_inv_card_mul_sum_group [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] (f : G → ℂ) :
    LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) =
      (Fintype.card Γ : ℂ)⁻¹ * ∑ γ : Γ, ∑ x : G, f (x⁻¹ * (γ : G) * x) := by
  rw [trace_rightConvOp_eq_sum_coset]
  have hinv : ∀ γ₀ ∈ Γ, ∀ x : G,
      (∑ γ : Γ, f ((γ₀ * x)⁻¹ * (γ : G) * (γ₀ * x))) = ∑ γ : Γ, f (x⁻¹ * (γ : G) * x) := by
    intro γ₀ hγ₀ x
    let g₀ : Γ := ⟨γ₀, hγ₀⟩
    let e : Γ ≃ Γ := (Equiv.mulLeft g₀⁻¹).trans (Equiv.mulRight g₀)
    refine Fintype.sum_equiv e _ _ fun γ => ?_
    change f ((γ₀ * x)⁻¹ * (γ : G) * (γ₀ * x)) = f (x⁻¹ * (((g₀⁻¹ * γ) * g₀ : Γ) : G) * x)
    congr 1
    change (γ₀ * x)⁻¹ * (γ : G) * (γ₀ * x) = x⁻¹ * ((γ₀⁻¹ * (γ : G)) * γ₀) * x
    group
  have havg := sum_group_eq_card_subgroup_mul_sum_rightCoset Γ
    (fun x => ∑ γ : Γ, f (x⁻¹ * (γ : G) * x)) hinv
  have hne : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  conv_rhs => rw [Finset.sum_comm]
  rw [havg, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ### Orbital Integrals, Conjugacy-Class Orbit–Stabilizer & Exact Geometric Expansion -/

/-- Unnormalized `G`-conjugacy orbit sum `∑_{x ∈ G} f(x⁻¹ γ x)`. -/
def orbitSum [Fintype G] (f : G → ℂ) (γ : G) : ℂ :=
  ∑ x : G, f (x⁻¹ * γ * x)

/-- `orbitSum` depends only on the `G`-conjugacy class of `γ`. -/
theorem orbitSum_eq_of_isConj [Fintype G] (f : G → ℂ) {γ₁ γ₂ : G} (h : IsConj γ₁ γ₂) :
    orbitSum f γ₁ = orbitSum f γ₂ := by
  rcases h with ⟨u, hu⟩
  unfold orbitSum
  refine Fintype.sum_equiv (Equiv.mulLeft (u : G)) _ _ fun x => ?_
  change f (x⁻¹ * γ₁ * x) = f (((u : G) * x)⁻¹ * γ₂ * ((u : G) * x))
  have hγ₂ : γ₂ = (u : G) * γ₁ * (u : G)⁻¹ := by
    have h1 : (u : G) * γ₁ = γ₂ * (u : G) := hu
    calc γ₂ = (γ₂ * (u : G)) * (u : G)⁻¹ := by group
      _ = (u : G) * γ₁ * (u : G)⁻¹ := by rw [← h1]
  rw [hγ₂]
  congr 1
  group

/-- **Arthur–Selberg Orbital Integral** of `f : G → ℂ` at `γ ∈ G`:
`O_γ(f) = ∑_{x ∈ Z_G(γ) \ G} f(x⁻¹ γ x)`. -/
def orbitalIntegral [Fintype G] (f : G → ℂ) (γ : G)
    [Fintype (RightCosetSpace G (Subgroup.centralizer ({γ} : Set G)))] : ℂ :=
  ∑ q : RightCosetSpace G (Subgroup.centralizer ({γ} : Set G)),
    f ((cosetRep q)⁻¹ * γ * cosetRep q)

/-- Exact relation `orbitSum f γ = |Z_G(γ)| * O_γ(f)`. -/
theorem orbitSum_eq_card_centralizer_mul_orbitalIntegral [Fintype G] (f : G → ℂ) (γ : G)
    [Fintype (Subgroup.centralizer ({γ} : Set G))]
    [Fintype (RightCosetSpace G (Subgroup.centralizer ({γ} : Set G)))] :
    orbitSum f γ =
      (Fintype.card (Subgroup.centralizer ({γ} : Set G)) : ℂ) * orbitalIntegral f γ := by
  unfold orbitSum orbitalIntegral
  refine sum_group_eq_card_subgroup_mul_sum_rightCoset (Subgroup.centralizer ({γ} : Set G))
    (fun x => f (x⁻¹ * γ * x)) ?_
  intro z hz x
  have hcomm : γ * z = z * γ := hz γ (Set.mem_singleton γ)
  congr 1
  calc (z * x)⁻¹ * γ * (z * x)
      = x⁻¹ * (z⁻¹ * (γ * z)) * x := by group
    _ = x⁻¹ * (z⁻¹ * (z * γ)) * x := by rw [hcomm]
    _ = x⁻¹ * γ * x := by group

/-- Normalized orbital integral formula `O_γ(f) = |Z_G(γ)|⁻¹ * ∑_{x ∈ G} f(x⁻¹ γ x)`. -/
theorem orbitalIntegral_eq_inv_card_mul_orbitSum [Fintype G] (f : G → ℂ) (γ : G)
    [Fintype (Subgroup.centralizer ({γ} : Set G))]
    [Fintype (RightCosetSpace G (Subgroup.centralizer ({γ} : Set G)))] :
    orbitalIntegral f γ =
      (Fintype.card (Subgroup.centralizer ({γ} : Set G)) : ℂ)⁻¹ * orbitSum f γ := by
  rw [orbitSum_eq_card_centralizer_mul_orbitalIntegral]
  have hne : (Fintype.card (Subgroup.centralizer ({γ} : Set G)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- At the identity `γ = 1`, `O_1(f) = f(1)`! -/
theorem orbitalIntegral_one [Fintype G] (f : G → ℂ)
    [Fintype (Subgroup.centralizer ({(1 : G)} : Set G))]
    [Fintype (RightCosetSpace G (Subgroup.centralizer ({(1 : G)} : Set G)))] :
    orbitalIntegral f 1 = f 1 := by
  rw [orbitalIntegral_eq_inv_card_mul_orbitSum]
  have hcent : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  have hcard : Fintype.card (Subgroup.centralizer ({(1 : G)} : Set G)) = Fintype.card G := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun x => (x : G)
        invFun := fun x => ⟨x, by rw [hcent]; trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsum : orbitSum f 1 = (Fintype.card G : ℂ) * f 1 := by
    unfold orbitSum
    simp [nsmul_eq_mul]
  have hne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hcard, hsum, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Elementary **Conjugacy-Class Orbit–Stabilizer Theorem** for any finite group `H`:
`|{h' : H | ConjClasses.mk h' = ConjClasses.mk h}| * |Z_H(h)| = |H|`. -/
theorem card_conjClass_mul_card_centralizer {H : Type*} [Group H] [Fintype H]
    [DecidableEq (ConjClasses H)] (h : H) [Fintype (Subgroup.centralizer ({h} : Set H))] :
    (Finset.univ.filter (fun h' : H => ConjClasses.mk h' = ConjClasses.mk h)).card *
      Fintype.card (Subgroup.centralizer ({h} : Set H)) = Fintype.card H := by
  classical
  let φ : H → H := fun x => x * h * x⁻¹
  let C : Finset H := Finset.univ.filter (fun h' : H => ConjClasses.mk h' = ConjClasses.mk h)
  have hmaps : ∀ x ∈ (Finset.univ : Finset H), φ x ∈ C := by
    intro x _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj]
    exact ⟨Units.mk x⁻¹ x (inv_mul_cancel x) (mul_inv_cancel x), by
      change x⁻¹ * (x * h * x⁻¹) = h * x⁻¹
      group⟩
  have hfiber : ∀ h' ∈ C,
      (Finset.univ.filter (fun x : H => φ x = h')).card =
        Fintype.card (Subgroup.centralizer ({h} : Set H)) := by
    intro h' hh'
    have hconj : IsConj h h' := by
      have hmk := (Finset.mem_filter.mp hh').2
      exact (ConjClasses.mk_eq_mk_iff_isConj.mp hmk).symm
    rcases hconj with ⟨u, hu⟩
    let x₀ : H := (u : H)
    have hx₀ : φ x₀ = h' := by
      have h1 : x₀ * h = h' * x₀ := hu
      dsimp only [φ]
      calc x₀ * h * x₀⁻¹ = (h' * x₀) * x₀⁻¹ := by rw [h1]
        _ = h' := by group
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun x =>
          ⟨x₀⁻¹ * x.1, by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            have hx : x.1 * h * x.1⁻¹ = x₀ * h * x₀⁻¹ :=
              ((Finset.mem_filter.mp x.2).2).trans hx₀.symm
            calc h * (x₀⁻¹ * x.1)
                = x₀⁻¹ * (x₀ * h * x₀⁻¹) * x.1 := by group
              _ = x₀⁻¹ * (x.1 * h * x.1⁻¹) * x.1 := by rw [← hx]
              _ = x₀⁻¹ * x.1 * h := by group⟩
        invFun := fun z =>
          ⟨x₀ * z.1, by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_⟩
            have hcomm : h * z.1 = z.1 * h := z.2 h (Set.mem_singleton h)
            dsimp only [φ]
            rw [← hx₀]
            dsimp only [φ]
            calc (x₀ * z.1) * h * (x₀ * z.1)⁻¹
                = x₀ * (z.1 * h) * z.1⁻¹ * x₀⁻¹ := by group
              _ = x₀ * (h * z.1) * z.1⁻¹ * x₀⁻¹ := by rw [← hcomm]
              _ = x₀ * h * x₀⁻¹ := by group⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun z => Subtype.ext (by group) }
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ] at hsum
  calc C.card * Fintype.card (Subgroup.centralizer ({h} : Set H))
      = ∑ _h' ∈ C, Fintype.card (Subgroup.centralizer ({h} : Set H)) := by simp
    _ = ∑ h' ∈ C, (Finset.univ.filter (fun x : H => φ x = h')).card :=
          Finset.sum_congr rfl fun h' hh' => (hfiber h' hh').symm
    _ = Fintype.card H := hsum.symm

/-- Canonical representative `γ ∈ H` of a conjugacy class `c : ConjClasses H`. -/
def conjRep {H : Type*} [Group H] (c : ConjClasses H) : H :=
  Classical.choose (ConjClasses.exists_rep c)

@[simp]
lemma conjClasses_mk_conjRep {H : Type*} [Group H] (c : ConjClasses H) :
    ConjClasses.mk (conjRep c) = c :=
  Classical.choose_spec (ConjClasses.exists_rep c)

/-- **Exact Geometric Side of the Finite-Quotient Selberg–Arthur Trace Formula**
(Arthur–Selberg volume × orbital integral expansion over `ConjClasses Γ`):
`GeomSide(Γ, f) = ∑_{[γ] ∈ Conj(Γ)} (|Z_G(γ)| / |Z_Γ(γ)|) · O_γ(f)`. -/
def geomSide [Fintype G] (Γ : Subgroup G) (f : G → ℂ) : ℂ := by
  classical
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : Fintype (ConjClasses Γ) := Quotient.fintype (IsConj.setoid Γ)
  exact ∑ c : ConjClasses Γ,
    let γ : Γ := conjRep c
    letI : Fintype (Subgroup.centralizer ({γ} : Set Γ)) := Fintype.ofFinite _
    letI : Fintype (Subgroup.centralizer ({(γ : G)} : Set G)) := Fintype.ofFinite _
    letI : Fintype (RightCosetSpace G (Subgroup.centralizer ({(γ : G)} : Set G))) :=
      Fintype.ofFinite _
    ((Fintype.card (Subgroup.centralizer ({(γ : G)} : Set G)) : ℂ) /
      (Fintype.card (Subgroup.centralizer ({γ} : Set Γ)) : ℂ)) *
      orbitalIntegral f (γ : G)

/-- **Exact Conjugacy-Class Centralizer Expansion** of `Tr(R(f) | L²(Γ \ G))`:
`Tr(R(f)) = ∑_{[γ] ∈ Conj(Γ)} |Z_Γ(γ)|⁻¹ · ∑_{x ∈ G} f(x⁻¹ γ x)`. -/
theorem trace_rightConvOp_eq_sum_conjClasses_centralizer [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    [DecidableEq (ConjClasses Γ)] [Fintype (ConjClasses Γ)]
    (f : G → ℂ) :
    LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) =
      ∑ c : ConjClasses Γ,
        let γ : Γ := conjRep c
        let _ : Fintype (Subgroup.centralizer ({γ} : Set Γ)) := Fintype.ofFinite _
        (Fintype.card (Subgroup.centralizer ({γ} : Set Γ)) : ℂ)⁻¹ *
          orbitSum f (γ : G) := by
  classical
  rw [trace_rightConvOp_eq_inv_card_mul_sum_group]
  have hfiber :
      ∑ γ : Γ, orbitSum f (γ : G) =
        ∑ c : ConjClasses Γ,
          ∑ γ ∈ Finset.univ.filter (fun γ : Γ => ConjClasses.mk γ = c),
            orbitSum f (γ : G) := by
    simpa only [Finset.mem_univ, forall_const] using
      (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset Γ))
        (t := (Finset.univ : Finset (ConjClasses Γ)))
        (g := ConjClasses.mk) (fun _ _ => Finset.mem_univ _)
        (fun γ : Γ => orbitSum f (γ : G))).symm
  change (Fintype.card Γ : ℂ)⁻¹ * ∑ γ : Γ, orbitSum f (γ : G) = _
  rw [hfiber, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  let γ₀ : Γ := conjRep c
  let _ : Fintype (Subgroup.centralizer ({γ₀} : Set Γ)) := Fintype.ofFinite _
  have hconst : ∀ γ ∈ Finset.univ.filter (fun γ : Γ => ConjClasses.mk γ = c),
      orbitSum f (γ : G) = orbitSum f (γ₀ : G) := by
    intro γ hγ
    have hmk : ConjClasses.mk γ = ConjClasses.mk γ₀ := by
      rw [(Finset.mem_filter.mp hγ).2, conjClasses_mk_conjRep]
    have hconjΓ : IsConj γ γ₀ := ConjClasses.mk_eq_mk_iff_isConj.mp hmk
    have hconjG : IsConj (γ : G) (γ₀ : G) := by
      rcases hconjΓ with ⟨u, hu⟩
      refine ⟨Units.map Γ.subtype u, ?_⟩
      change ((u : Γ) : G) * (γ : G) = (γ₀ : G) * ((u : Γ) : G)
      simpa using congrArg Γ.subtype hu
    exact orbitSum_eq_of_isConj f hconjG
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have horb := card_conjClass_mul_card_centralizer γ₀
  have hfilter_eq :
      Finset.univ.filter (fun γ : Γ => ConjClasses.mk γ = c) =
        Finset.univ.filter (fun γ : Γ => ConjClasses.mk γ = ConjClasses.mk γ₀) := by
    simp [γ₀, conjClasses_mk_conjRep]
  rw [hfilter_eq]
  have horbC :
      ((Finset.univ.filter (fun γ : Γ => ConjClasses.mk γ = ConjClasses.mk γ₀)).card : ℂ) *
        (Fintype.card (Subgroup.centralizer ({γ₀} : Set Γ)) : ℂ) =
      (Fintype.card Γ : ℂ) := by
    exact_mod_cast horb
  have hΓne : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZne : (Fintype.card (Subgroup.centralizer ({γ₀} : Set Γ)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcardC :
      ((Finset.univ.filter (fun γ : Γ => ConjClasses.mk γ = ConjClasses.mk γ₀)).card : ℂ) =
      (Fintype.card Γ : ℂ) * (Fintype.card (Subgroup.centralizer ({γ₀} : Set Γ)) : ℂ)⁻¹ := by
    rw [← horbC, mul_assoc, mul_inv_cancel₀ hZne, mul_one]
  rw [hcardC, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hΓne, one_mul]

/-- **Exact Arthur–Selberg Volume × Orbital Integral Geometric Side**:
`Tr(R(f) | L²(Γ \ G)) = ∑_{[γ] ∈ Conj(Γ)} (|Z_G(γ)| / |Z_Γ(γ)|) · O_γ(f) = geomSide Γ f`. -/
theorem trace_rightConvOp_eq_geomSide [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] (f : G → ℂ) :
    LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) = geomSide Γ f := by
  classical
  unfold geomSide
  let _ : Fintype (ConjClasses Γ) := Quotient.fintype (IsConj.setoid Γ)
  rw [trace_rightConvOp_eq_sum_conjClasses_centralizer Γ f]
  refine Finset.sum_congr (by congr 1; exact Subsingleton.elim _ _) fun c _ => ?_
  dsimp only
  let γ : Γ := conjRep c
  let _ : Fintype (Subgroup.centralizer ({γ} : Set Γ)) := Fintype.ofFinite _
  let _ : Fintype (Subgroup.centralizer ({(γ : G)} : Set G)) := Fintype.ofFinite _
  let _ : Fintype (RightCosetSpace G (Subgroup.centralizer ({(γ : G)} : Set G))) :=
    Fintype.ofFinite _
  change (Fintype.card (Subgroup.centralizer ({γ} : Set Γ)) : ℂ)⁻¹ * orbitSum f (γ : G) =
    ((Fintype.card (Subgroup.centralizer ({(γ : G)} : Set G)) : ℂ) /
      (Fintype.card (Subgroup.centralizer ({γ} : Set Γ)) : ℂ)) * orbitalIntegral f (γ : G)
  rw [orbitSum_eq_card_centralizer_mul_orbitalIntegral f (γ : G)]
  ring

/-- **`(|Γ| / |Z_Γ(γ)|)`-Weighted Orbital Expansion** of `Tr(R(f) | L²(Γ \ G))`:
`Tr(R(f)) = ∑_{[γ] ∈ Conj(Γ)} (|Γ| / |Z_Γ(γ)|) · (|Γ|⁻¹ ∑_{x ∈ G} f(x⁻¹ γ x))`. -/
theorem trace_rightConvOp_eq_sum_conjClasses_gamma_weight [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    [DecidableEq (ConjClasses Γ)] [Fintype (ConjClasses Γ)] (f : G → ℂ) :
    LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) =
      ∑ c : ConjClasses Γ,
        let γ : Γ := conjRep c
        let _ : Fintype (Subgroup.centralizer ({γ} : Set Γ)) := Fintype.ofFinite _
        ((Fintype.card Γ : ℂ) / (Fintype.card (Subgroup.centralizer ({γ} : Set Γ)) : ℂ)) *
          ((Fintype.card Γ : ℂ)⁻¹ * orbitSum f (γ : G)) := by
  rw [trace_rightConvOp_eq_sum_conjClasses_centralizer Γ f]
  have hΓne : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine Finset.sum_congr rfl fun c _ => ?_
  dsimp only
  field_simp [hΓne]

/-- Evaluating the trace at the identity delta kernel `δ_1` recovers `dim L²(Γ \ G) = |G| / |Γ|`. -/
theorem trace_rightConvOp_delta_one [Fintype G] [DecidableEq G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)] :
    LinearMap.trace ℂ (AutomorphicL2 G Γ)
      (rightConvOp Γ (fun g => if g = 1 then (1 : ℂ) else 0)) =
      (Fintype.card G : ℂ) / (Fintype.card Γ : ℂ) := by
  rw [trace_rightConvOp_eq_sum_coset]
  have hinner : ∀ q : RightCosetSpace G Γ,
      (∑ γ : Γ, if (cosetRep q)⁻¹ * (γ : G) * cosetRep q = 1 then (1 : ℂ) else 0) = 1 := by
    intro q
    rw [Finset.sum_eq_single (1 : Γ)]
    · simp
    · intro γ _ hγ
      have hne : (cosetRep q)⁻¹ * (γ : G) * cosetRep q ≠ 1 := by
        intro h1
        have hγ1 : (γ : G) = 1 := by
          calc (γ : G)
              = cosetRep q * ((cosetRep q)⁻¹ * (γ : G) * cosetRep q) * (cosetRep q)⁻¹ := by group
            _ = cosetRep q * 1 * (cosetRep q)⁻¹ := by rw [h1]
            _ = 1 := by group
        exact hγ (Subtype.ext hγ1)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ (1 : Γ)) h
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hlag : (Fintype.card Γ : ℂ) * (Fintype.card (RightCosetSpace G Γ) : ℂ) =
      (Fintype.card G : ℂ) := by
    exact_mod_cast card_subgroup_mul_card_rightCosetSpace Γ
  have hΓne : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hΓne]
  rw [mul_comm]
  exact hlag

/-! ### Exact Spectral Side & Full Finite-Quotient Selberg–Arthur Trace Formula -/

/-- Integrated operator `ρ(f) = ∑_{g ∈ G} f(g) • ρ(g)` for any representation `ρ : G →* End ℂ V`. -/
def repConvOp [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (f : G → ℂ) : Module.End ℂ V :=
  ∑ g : G, f g • ρ g

/-- Character `χ_ρ(g) = Tr(ρ(g))` of a finite-dimensional representation `ρ`. -/
def repChar {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (g : G) : ℂ :=
  LinearMap.trace ℂ V (ρ g)

/-- **Trace of an Integrated Representation Operator**:
`Tr(ρ(f)) = ∑_{g ∈ G} f(g) · χ_ρ(g)`. -/
theorem trace_repConvOp [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (f : G → ℂ) :
    LinearMap.trace ℂ V (repConvOp ρ f) = ∑ g : G, f g * repChar ρ g := by
  unfold repConvOp repChar
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul]

/-- Trace of a block-diagonal operator on a finite product `∀ i : ι, W i` equals the sum of the
component traces. -/
theorem trace_pi_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, FiniteDimensional ℂ (W i)]
    (T : ∀ i : ι, Module.End ℂ (W i)) :
    LinearMap.trace ℂ (∀ i : ι, W i)
      { toFun := fun v i => T i (v i)
        map_add' := fun u v => by funext i; exact map_add (T i) (u i) (v i)
        map_smul' := fun c v => by funext i; exact map_smul (T i) c (v i) } =
      ∑ i : ι, LinearMap.trace ℂ (W i) (T i) := by
  classical
  let b : ∀ i : ι, Module.Basis (Fin (Module.finrank ℂ (W i))) ℂ (W i) :=
    fun i => Module.finBasis ℂ (W i)
  let B : Module.Basis (Σ i : ι, Fin (Module.finrank ℂ (W i))) ℂ (∀ i : ι, W i) :=
    Pi.basis b
  let L : Module.End ℂ (∀ i : ι, W i) :=
    { toFun := fun v i => T i (v i)
      map_add' := fun u v => by funext i; exact map_add (T i) (u i) (v i)
      map_smul' := fun c v => by funext i; exact map_smul (T i) c (v i) }
  change LinearMap.trace ℂ (∀ i : ι, W i) L = _
  rw [LinearMap.trace_eq_matrix_trace ℂ B L, Matrix.trace]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.trace_eq_matrix_trace ℂ (b i) (T i), Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, B, Pi.basis_apply, Pi.basis_repr, L]
  change (b i).repr (T i (Pi.single i (b i j) i)) j = (b i).repr (T i (b i j)) j
  rw [Pi.single_eq_same]

/-- **Peter–Weyl / Isotypic Spectral Decomposition of `L²(Γ \ G)`**:
a `G`-equivariant linear isomorphism `L²(Γ \ G) ≃ₗ[ℂ] ∀ i : ι, Fin (m i) → V i` decomposing the
right-regular representation into finite-dimensional representations `ρ_i` with multiplicities `m_i`. -/
structure SpectralDecomposition (G : Type*) [Group G] (Γ : Subgroup G) (ι : Type*) [Fintype ι] where
  V : ι → Type*
  [instAdd : ∀ i, AddCommGroup (V i)]
  [instMod : ∀ i, Module ℂ (V i)]
  [instFin : ∀ i, FiniteDimensional ℂ (V i)]
  rep : ∀ i : ι, G →* Module.End ℂ (V i)
  mult : ι → ℕ
  equiv : AutomorphicL2 G Γ ≃ₗ[ℂ] (∀ i : ι, Fin (mult i) → V i)
  intertwines : ∀ (g : G) (φ : AutomorphicL2 G Γ) (i : ι) (k : Fin (mult i)),
    equiv (rightRegRep Γ g φ) i k = rep i g (equiv φ i k)

attribute [instance] SpectralDecomposition.instAdd SpectralDecomposition.instMod
  SpectralDecomposition.instFin

/-- Spectral side `∑_i m_i · Tr(ρ_i(f))` of a `SpectralDecomposition`. -/
def SpectralDecomposition.specSide [Fintype G] {Γ : Subgroup G} {ι : Type*} [Fintype ι]
    (D : SpectralDecomposition G Γ ι) (f : G → ℂ) : ℂ :=
  ∑ i : ι, (D.mult i : ℂ) * LinearMap.trace ℂ (D.V i) (repConvOp (D.rep i) f)

/-- **Exact Spectral Side Identity**:
for any Peter–Weyl decomposition `D` of `L²(Γ \ G)`,
`Tr(R(f) | L²(Γ \ G)) = ∑_i m_i · Tr(ρ_i(f))`. -/
theorem SpectralDecomposition.trace_rightConvOp_eq_specSide [Fintype G] {Γ : Subgroup G}
    {ι : Type*} [Fintype ι] (D : SpectralDecomposition G Γ ι) (f : G → ℂ) :
    LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) = D.specSide f := by
  classical
  let blockOp : Module.End ℂ (∀ i : ι, Fin (D.mult i) → D.V i) :=
    { toFun := fun v i k => repConvOp (D.rep i) f (v i k)
      map_add' := fun u v => by funext i k; exact map_add _ _ _
      map_smul' := fun c v => by funext i k; exact map_smul _ _ _ }
  have hconj : D.equiv.conj (rightConvOp Γ f) = blockOp := by
    apply LinearMap.ext; intro v; funext i k
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hint : ∀ (g : G) (φ : AutomorphicL2 G Γ),
        D.equiv (rightRegOp Γ g φ) i k = D.rep i g (D.equiv φ i k) :=
      fun g φ => D.intertwines g φ i k
    have hsum_eval : ∀ (s : Finset G) (F : G → AutomorphicL2 G Γ),
        D.equiv (∑ g ∈ s, F g) i k = ∑ g ∈ s, D.equiv (F g) i k := by
      intro s F
      rw [map_sum]
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha _ =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          simp
    change D.equiv (rightConvOp Γ f (D.equiv.symm v)) i k = repConvOp (D.rep i) f (v i k)
    unfold rightConvOp repConvOp
    rw [LinearMap.sum_apply, hsum_eval, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [LinearMap.smul_apply]
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hint g (D.equiv.symm v),
      D.equiv.apply_symm_apply]
  have htr : LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ f) =
      LinearMap.trace ℂ (∀ i : ι, Fin (D.mult i) → D.V i) blockOp := by
    rw [← hconj, LinearMap.trace_conj']
  rw [htr]
  have houter := trace_pi_diag (W := fun i : ι => Fin (D.mult i) → D.V i)
    (T := fun i =>
      { toFun := fun u k => repConvOp (D.rep i) f (u k)
        map_add' := fun u₁ u₂ => by funext k; exact map_add _ _ _
        map_smul' := fun c u => by funext k; exact map_smul _ _ _ })
  change LinearMap.trace ℂ (∀ i : ι, Fin (D.mult i) → D.V i) blockOp = D.specSide f
  have hblock_eq : LinearMap.trace ℂ (∀ i : ι, Fin (D.mult i) → D.V i) blockOp =
      ∑ i : ι, LinearMap.trace ℂ (Fin (D.mult i) → D.V i)
        { toFun := fun u k => repConvOp (D.rep i) f (u k)
          map_add' := fun u₁ u₂ => by funext k; exact map_add _ _ _
          map_smul' := fun c u => by funext k; exact map_smul _ _ _ } := houter
  rw [hblock_eq]
  unfold SpectralDecomposition.specSide
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinner := trace_pi_diag (W := fun _ : Fin (D.mult i) => D.V i)
    (T := fun _ => repConvOp (D.rep i) f)
  rw [hinner]
  simp [nsmul_eq_mul]

/-- Character-sum form of the spectral side:
`D.specSide f = ∑ i : ι, m_i · ∑ g : G, f g * χ_{ρ_i}(g)`. -/
theorem SpectralDecomposition.specSide_eq_sum_char [Fintype G] {Γ : Subgroup G}
    {ι : Type*} [Fintype ι] (D : SpectralDecomposition G Γ ι) (f : G → ℂ) :
    D.specSide f = ∑ i : ι, (D.mult i : ℂ) * ∑ g : G, f g * repChar (D.rep i) g := by
  unfold SpectralDecomposition.specSide
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_repConvOp]

/-- **EXACT FINITE-QUOTIENT SELBERG–ARTHUR TRACE FORMULA**:
for any finite group `G`, subgroup `Γ ≤ G`, Peter–Weyl spectral decomposition `D` of `L²(Γ \ G)`,
and convolution test function `f : G → ℂ`:
$$\sum_{i} m_i \cdot \operatorname{Tr}(\rho_i(f)) =
  \sum_{[\gamma] \in \operatorname{Conj}(\Gamma)}
    \frac{|Z_G(\gamma)|}{|Z_\Gamma(\gamma)|} \cdot O_\gamma(f).$$ -/
theorem selberg_arthur_trace_formula [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    {ι : Type*} [Fintype ι] (D : SpectralDecomposition G Γ ι) (f : G → ℂ) :
    D.specSide f = geomSide Γ f := by
  rw [← D.trace_rightConvOp_eq_specSide f, trace_rightConvOp_eq_geomSide Γ f]

/-- **Selberg–Arthur Trace Formula (Explicit Centralizer-Weighted Orbital Form)**:
`∑_i m_i · ∑_g f(g) χ_{ρ_i}(g) = ∑_{[γ] ∈ Conj(Γ)} |Z_Γ(γ)|⁻¹ ∑_{x ∈ G} f(x⁻¹ γ x)`. -/
theorem selberg_arthur_trace_formula_explicit [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    [DecidableEq (ConjClasses Γ)] [Fintype (ConjClasses Γ)]
    {ι : Type*} [Fintype ι] (D : SpectralDecomposition G Γ ι) (f : G → ℂ) :
    ∑ i : ι, (D.mult i : ℂ) * ∑ g : G, f g * repChar (D.rep i) g =
      ∑ c : ConjClasses Γ,
        let γ : Γ := conjRep c
        letI : Fintype (Subgroup.centralizer ({γ} : Set Γ)) := Fintype.ofFinite _
        (Fintype.card (Subgroup.centralizer ({γ} : Set Γ)) : ℂ)⁻¹ *
          orbitSum f (γ : G) := by
  rw [← D.specSide_eq_sum_char, ← D.trace_rightConvOp_eq_specSide,
    trace_rightConvOp_eq_sum_conjClasses_centralizer Γ f]

/-- **Dimension / Frobenius Reciprocity Corollary (`f = δ_1`)**:
`∑_i m_i · dim(V_i) = |G| / |Γ|`. -/
theorem selberg_arthur_dimension_formula [Fintype G] [DecidableEq G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    {ι : Type*} [Fintype ι] (D : SpectralDecomposition G Γ ι) :
    ∑ i : ι, (D.mult i : ℂ) * (Module.finrank ℂ (D.V i) : ℂ) =
      (Fintype.card G : ℂ) / (Fintype.card Γ : ℂ) := by
  let δ : G → ℂ := fun g => if g = 1 then 1 else 0
  have h1 := D.trace_rightConvOp_eq_specSide δ
  have h2 := trace_rightConvOp_delta_one Γ
  rw [h2] at h1
  rw [h1, D.specSide_eq_sum_char]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.sum_eq_single (1 : G)]
  · simp [δ, repChar, map_one]
  · intro g _ hg; simp [δ, hg]
  · intro h; exact absurd (Finset.mem_univ (1 : G)) h

/-- **Self-Adjoint Spectral-Theorem Selberg Trace Formula**:
for ANY self-adjoint kernel `f` (`∀ g, f g⁻¹ = star (f g)`), `R(f)` admits an orthonormal
eigenbasis of `L²(Γ \ G)` with real eigenvalues `λ_k ∈ ℝ` whose sum equals `geomSide Γ f`! -/
theorem selberg_arthur_selfAdjoint_eigenvalues [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    (f : G → ℂ) (hf : ∀ g : G, f g⁻¹ = star (f g)) :
    let hS := rightConvOp_isSymmetric_of_selfAdj Γ f hf
    let n := Fintype.card (RightCosetSpace G Γ)
    let hn : Module.finrank ℂ (AutomorphicL2 G Γ) = n := finrank_automorphicL2 Γ
    (∑ k : Fin n, (hS.eigenvalues hn k : ℂ)) = geomSide Γ f := by
  intro hS n hn
  rw [← trace_rightConvOp_eq_geomSide Γ f]
  rw [trace_eq_sum_inner_orthonormalBasis (hS.eigenvectorBasis hn)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hS.apply_eigenvectorBasis hn k, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (hS.eigenvectorBasis hn).orthonormal.1 k]
  simp

/-- **Bochner Curvature Spectral Gap on `L²(Γ \ G)`**:
connects directly to `Stage3ExplicitSpectral.bochner_spectral_gap_symmetric` — any Bochner-type
symmetric automorphic operator `Δ = D* ∘ D + R` on `L²(Γ \ G)` with curvature lower bound
`Re ⟨R φ, φ⟩ ≥ κ ‖φ‖²` has every eigenvalue `μ ∈ ℂ` purely real and satisfying `κ ≤ μ.re`! -/
theorem automorphic_bochner_spectral_gap [Fintype G] (Γ : Subgroup G)
    [Fintype (RightCosetSpace G Γ)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (D : AutomorphicL2 G Γ →ₗ[ℂ] H) (R : AutomorphicL2 G Γ →ₗ[ℂ] AutomorphicL2 G Γ)
    (hR_sym : R.IsSymmetric) {κ : ℝ} (hcurv : ∀ φ, κ * ‖φ‖ ^ 2 ≤ (inner ℂ (R φ) φ).re)
    {φ : AutomorphicL2 G Γ} (hφ : φ ≠ 0) {μ : ℂ}
    (heig : (LinearMap.adjoint D ∘ₗ D + R) φ = μ • φ) :
    μ.im = 0 ∧ κ ≤ μ.re :=
  Stage3ExplicitSpectral.bochner_spectral_gap_symmetric D (LinearMap.adjoint D) R
    (fun v u => LinearMap.adjoint_inner_left D u v) hR_sym hcurv hφ heig

end FiniteSelbergTrace

/-! ## Section 2: Simple Jacquet–Langlands & Cyclic Base-Change Spectral Transfer Principle -/

section JacquetLanglandsTransfer

/-- Normalized group `L²`-inner product `⟨φ, ψ⟩_G = |G|⁻¹ ∑_{g ∈ G} star (φ g) * ψ g`. -/
def charInner {G : Type*} [Fintype G] (φ ψ : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g : G, star (φ g) * ψ g

/-- A family of functions `χ : ι → G → ℂ` is **orthogonal** with nonzero `L²`-norms. -/
def IsOrthogonalChars {G : Type*} [Fintype G] {ι : Type*} (χ : ι → G → ℂ) : Prop :=
  (∀ i j : ι, i ≠ j → ∑ g : G, star (χ i g) * χ j g = 0) ∧
    (∀ i : ι, ∑ g : G, star (χ i g) * χ i g ≠ 0)

/-- A family of functions `χ : ι → G → ℂ` is **orthonormal** for `charInner`
(standard Schur orthogonality of irreducible characters). -/
def IsOrthonormalChars {G : Type*} [Fintype G] {ι : Type*} [DecidableEq ι]
    (χ : ι → G → ℂ) : Prop :=
  ∀ i j : ι, charInner (χ i) (χ j) = if i = j then 1 else 0

theorem IsOrthonormalChars.toOrthogonal {G : Type*} [Fintype G] [Nonempty G]
    {ι : Type*} [DecidableEq ι] {χ : ι → G → ℂ}
    (h : IsOrthonormalChars χ) : IsOrthogonalChars χ := by
  have hGne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · intro i j hij
    have h0 := h i j
    rw [if_neg hij] at h0
    unfold charInner at h0
    exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hGne)
  · intro i hi
    have h1 := h i i
    rw [if_pos rfl] at h1
    unfold charInner at h1
    rw [hi, mul_zero] at h1
    exact zero_ne_one h1

/-- **Schur Fourier Coefficient Extraction**:
for any orthonormal character system `χ`, `⟨χ_j, ∑_i c_i χ_i⟩_G = c_j`. -/
theorem charInner_linearComb {G : Type*} [Fintype G] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {χ : ι → G → ℂ} (hχ : IsOrthonormalChars χ) (c : ι → ℂ) (j : ι) :
    charInner (χ j) (fun g => ∑ i : ι, c i * χ i g) = c j := by
  unfold charInner
  calc (Fintype.card G : ℂ)⁻¹ * ∑ g : G, star (χ j g) * ∑ i : ι, c i * χ i g
      = (Fintype.card G : ℂ)⁻¹ * ∑ i : ι, c i * ∑ g : G, star (χ j g) * χ i g := by
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => by ring
    _ = ∑ i : ι, c i * charInner (χ j) (χ i) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold charInner; ring
    _ = ∑ i : ι, c i * (if j = i then 1 else 0) := by
          refine Finset.sum_congr rfl fun i _ => by rw [hχ j i]
    _ = c j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro i _ hi; simp [Ne.symm hi]
          · intro h; exact absurd (Finset.mem_univ j) h

/-- **Linear Independence of Orthogonal Characters (Pointwise Form)**:
if `∑_i c₁ i * χ i g = ∑_i c₂ i * χ i g` for all `g ∈ G`, then `∀ i, c₁ i = c₂ i`. -/
theorem eq_of_sum_mul_orthogonalChars {G : Type*} [Fintype G] {ι : Type*} [Fintype ι]
    {χ : ι → G → ℂ} (hχ : IsOrthogonalChars χ) {c₁ c₂ : ι → ℂ}
    (heq : ∀ g : G, ∑ i : ι, c₁ i * χ i g = ∑ i : ι, c₂ i * χ i g) :
    ∀ j : ι, c₁ j = c₂ j := by
  classical
  intro j
  have hproj : ∀ c : ι → ℂ,
      (∑ g : G, star (χ j g) * ∑ i : ι, c i * χ i g) =
        c j * ∑ g : G, star (χ j g) * χ j g := by
    intro c
    calc ∑ g : G, star (χ j g) * ∑ i : ι, c i * χ i g
        = ∑ i : ι, c i * ∑ g : G, star (χ j g) * χ i g := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => by ring
      _ = c j * ∑ g : G, star (χ j g) * χ j g := by
            rw [Finset.sum_eq_single j]
            · intro i _ hi
              rw [hχ.1 j i (Ne.symm hi), mul_zero]
            · intro h; exact absurd (Finset.mem_univ j) h
  have hsum :
      (∑ g : G, star (χ j g) * ∑ i : ι, c₁ i * χ i g) =
        ∑ g : G, star (χ j g) * ∑ i : ι, c₂ i * χ i g :=
    Finset.sum_congr rfl fun g _ => by rw [heq g]
  rw [hproj c₁, hproj c₂] at hsum
  exact mul_right_cancel₀ (hχ.2 j) hsum

/-- **Linear Independence of Orthogonal Characters (Test-Function / Distribution Form)**:
if `∑_i c₁ i * ∑_g f g * χ i g = ∑_i c₂ i * ∑_g f g * χ i g` for every test function `f : G → ℂ`,
then `∀ g, ∑_i c₁ i * χ i g = ∑_i c₂ i * χ i g` AND `∀ i, c₁ i = c₂ i`! -/
theorem eq_of_forall_test_orthogonalChars {G : Type*} [Fintype G] {ι : Type*} [Fintype ι]
    {χ : ι → G → ℂ} (hχ : IsOrthogonalChars χ) {c₁ c₂ : ι → ℂ}
    (htest : ∀ f : G → ℂ,
      (∑ i : ι, c₁ i * ∑ g : G, f g * χ i g) =
        ∑ i : ι, c₂ i * ∑ g : G, f g * χ i g) :
    (∀ g : G, ∑ i : ι, c₁ i * χ i g = ∑ i : ι, c₂ i * χ i g) ∧ (∀ j : ι, c₁ j = c₂ j) := by
  classical
  have hpt : ∀ g₀ : G, ∑ i : ι, c₁ i * χ i g₀ = ∑ i : ι, c₂ i * χ i g₀ := by
    intro g₀
    have h := htest (fun g => if g = g₀ then 1 else 0)
    have hsimp : ∀ c : ι → ℂ,
        (∑ i : ι, c i * ∑ g : G, (if g = g₀ then (1 : ℂ) else 0) * χ i g) =
          ∑ i : ι, c i * χ i g₀ := by
      intro c
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [Finset.sum_eq_single g₀]
      · simp
      · intro g _ hg; simp [hg]
      · intro hmem; exact absurd (Finset.mem_univ g₀) hmem
    rwa [hsimp c₁, hsimp c₂] at h
  exact ⟨hpt, eq_of_sum_mul_orthogonalChars hχ hpt⟩

/-! ### Concrete Orthonormal Character Systems (1D Characters, `Stage2WeilMetaplectic`, `Stage3AutomorphicDescent`) -/

/-- Every 1D character `η : G →* ℂˣ` on a finite group `G` takes unit-circle values. -/
lemma homChar_norm_eq_one {G : Type*} [Group G] [Fintype G] (η : G →* ℂˣ) (g : G) :
    ‖(η g : ℂ)‖ = 1 := by
  have hpow : (η g : ℂ) ^ Fintype.card G = 1 := by
    have hord : g ^ Fintype.card G = 1 := pow_card_eq_one
    have h1 : (η (g ^ Fintype.card G) : ℂ) = (η 1 : ℂ) := congrArg (fun x => (η x : ℂ)) hord
    rw [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] at h1
    exact h1
  have hnorm : ‖(η g : ℂ)‖ ^ Fintype.card G = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  rcases lt_trichotomy ‖(η g : ℂ)‖ 1 with hlt | heq | hgt
  · exact absurd (pow_lt_one₀ (norm_nonneg _) hlt hpos.ne') (by linarith)
  · exact heq
  · exact absurd (one_lt_pow₀ hgt hpos.ne') (by linarith)

lemma homChar_star_eq_inv {G : Type*} [Group G] [Fintype G] (η : G →* ℂˣ) (g : G) :
    star (η g : ℂ) = (η g⁻¹ : ℂ) := by
  have h1 : star (η g : ℂ) * (η g : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul', homChar_norm_eq_one η g]
    norm_num
  have h2 : (η g⁻¹ : ℂ) * (η g : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  exact mul_right_cancel₀ (Units.ne_zero (η g)) (h1.trans h2.symm)

/-- **Schur Orthogonality for Any Family of Distinct 1D Group Characters**:
any injective family `η : ι → (G →* ℂˣ)` on a finite group `G` is `IsOrthonormalChars`. -/
theorem homChar_orthonormal {G : Type*} [Group G] [Fintype G]
    {ι : Type*} [DecidableEq ι] (η : ι → (G →* ℂˣ))
    (hinj : Function.Injective η) :
    IsOrthonormalChars (fun i g => (η i g : ℂ)) := by
  intro i j
  unfold charInner
  have hGne : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hsum : ∑ g : G, star (η i g : ℂ) * (η i g : ℂ) = (Fintype.card G : ℂ) := by
      calc ∑ g : G, star (η i g : ℂ) * (η i g : ℂ)
          = ∑ _g : G, (1 : ℂ) := Finset.sum_congr rfl fun g _ => by
              rw [homChar_star_eq_inv, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
                Units.val_one]
        _ = (Fintype.card G : ℂ) := by simp
    rw [hsum, inv_mul_cancel₀ hGne]
  · rw [if_neg hij]
    have hne : η i ≠ η j := fun h => hij (hinj h)
    have hex : ∃ h : G, (η i h : ℂ) ≠ (η j h : ℂ) := by
      by_contra hAll
      push Not at hAll
      apply hne
      ext g
      exact hAll g
    obtain ⟨h, hh⟩ := hex
    let c : ℂ := star (η i h : ℂ) * (η j h : ℂ)
    have hc_ne : c ≠ 1 := by
      intro hc1
      apply hh
      have hmul : (η i h : ℂ) * c = (η i h : ℂ) := by rw [hc1, mul_one]
      have hmul2 : (η i h : ℂ) * c = (η j h : ℂ) := by
        dsimp only [c]
        rw [← mul_assoc, homChar_star_eq_inv, ← Units.val_mul, ← map_mul, mul_inv_cancel,
          map_one, Units.val_one, one_mul]
      exact hmul.symm.trans hmul2
    let S : ℂ := ∑ g : G, star (η i g : ℂ) * (η j g : ℂ)
    have hshift : c * S = S := by
      dsimp only [c, S]
      rw [Finset.mul_sum]
      calc ∑ g : G, star (η i h : ℂ) * (η j h : ℂ) * (star (η i g : ℂ) * (η j g : ℂ))
          = ∑ g : G, star (η i (h * g) : ℂ) * (η j (h * g) : ℂ) := by
              refine Finset.sum_congr rfl fun g _ => ?_
              simp only [map_mul, Units.val_mul, star_mul]
              ring
        _ = ∑ g : G, star (η i g : ℂ) * (η j g : ℂ) :=
              Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun _ => rfl
    have hS0 : S = 0 := by
      have h0 : (c - 1) * S = 0 := by rw [sub_mul, one_mul, hshift, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc_ne)
    change (Fintype.card G : ℂ)⁻¹ * S = 0
    rw [hS0, mul_zero]

/-- **Bridge to `Stage2WeilMetaplectic`**: additive characters `x ↦ ψ(⟨b, x⟩)` on `𝔽^n` form an
orthonormal character system (via `Stage2WeilMetaplectic.sum_psi_dotProd`)! -/
theorem weilAdditiveChar_orthonormal {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    IsOrthonormalChars
      (fun (b : Fin n → 𝔽) (x : Fin n → 𝔽) => ψ (Stage2WeilMetaplectic.dotProd b x)) := by
  intro b₁ b₂
  unfold charInner
  have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum :
      ∑ x : Fin n → 𝔽, star (ψ (Stage2WeilMetaplectic.dotProd b₁ x)) *
          ψ (Stage2WeilMetaplectic.dotProd b₂ x) =
        ∑ x : Fin n → 𝔽, ψ (Stage2WeilMetaplectic.dotProd (b₂ - b₁) x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Stage2WeilMetaplectic.addChar_star_eq_neg, ← AddChar.map_add_eq_mul,
      Stage2WeilMetaplectic.dotProd_sub_left, sub_eq_add_neg, add_comm]
  rw [hsum, Stage2WeilMetaplectic.sum_psi_dotProd ψ hψ (b₂ - b₁)]
  by_cases h : b₁ = b₂
  · subst h
    rw [sub_self, if_pos rfl, if_pos rfl, inv_mul_cancel₀ hcard]
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm h)), if_neg h, mul_zero]

/-- **Finite-Field Plancherel / Weil-Fourier Trace Invariance**
(directly bridging `Stage2WeilMetaplectic.fourierOp_unitary` & `fourierOp_parseval`):
the normalized finite Fourier transform `ℱ` preserves inner products, `L²`-norms, and operator
traces (`Tr(ℱ⁻¹ ∘ T ∘ ℱ) = Tr(T)`). -/
theorem weilFourier_plancherel_trace_invariance {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
    {n : ℕ} (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1)
    (T : Module.End ℂ (Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n)) :
    (∀ f g : Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n,
      inner ℂ (Stage2WeilMetaplectic.fourierOp ψ f) (Stage2WeilMetaplectic.fourierOp ψ g) =
        inner ℂ f g) ∧
    (∀ f : Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n,
      ‖Stage2WeilMetaplectic.fourierOp ψ f‖ ^ 2 = ‖f‖ ^ 2) ∧
    LinearMap.trace ℂ (Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n)
      ((Stage2WeilMetaplectic.fourierOp ψ ∘ₗ Stage2WeilMetaplectic.reflectOp) ∘ₗ
        T ∘ₗ Stage2WeilMetaplectic.fourierOp ψ) =
      LinearMap.trace ℂ (Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n) T := by
  refine ⟨Stage2WeilMetaplectic.fourierOp_unitary ψ hψ,
    Stage2WeilMetaplectic.fourierOp_parseval ψ hψ, ?_⟩
  have hsq := Stage2WeilMetaplectic.fourierOp_sq_eq_reflect n ψ hψ
  have href := Stage2WeilMetaplectic.reflectOp_sq (𝔽 := 𝔽) (n := n)
  let F : Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n ≃ₗ[ℂ]
      Stage2WeilMetaplectic.SchrodingerSpace 𝔽 n :=
    LinearEquiv.ofLinearMap (Stage2WeilMetaplectic.fourierOp ψ)
      (Stage2WeilMetaplectic.fourierOp ψ ∘ₗ Stage2WeilMetaplectic.reflectOp)
      (by
        rw [← LinearMap.comp_assoc, hsq, href])
      (by
        rw [LinearMap.comp_assoc, ← Stage2WeilMetaplectic.fourierOp_comm_reflect n ψ hψ,
          ← LinearMap.comp_assoc, hsq, href])
  have hconj :
      (Stage2WeilMetaplectic.fourierOp ψ ∘ₗ Stage2WeilMetaplectic.reflectOp) ∘ₗ
        T ∘ₗ Stage2WeilMetaplectic.fourierOp ψ = F.symm.conj T := by
    apply LinearMap.ext; intro f
    simp [F, LinearEquiv.conj_apply]
  rw [hconj, LinearMap.trace_conj']

/-- **Bridge to `Stage3AutomorphicDescent`**: cyclic characters `zmodChar ζ k` on `ZMod p`
form an orthonormal character system (via `Stage3AutomorphicDescent.zmodChar_sum_dual`)! -/
theorem zmodChar_orthonormal {p : ℕ} [Fact p.Prime] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) :
    IsOrthonormalChars (G := ZMod p) (Stage3AutomorphicDescent.zmodChar (p := p) ζ) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : NeZero p := ⟨hp.ne'⟩
  have hcard : (Fintype.card (ZMod p) : ℂ) = (p : ℂ) := by simp [ZMod.card]
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hstar : ∀ k g : ZMod p,
      star (Stage3AutomorphicDescent.zmodChar ζ k g) =
        Stage3AutomorphicDescent.zmodChar ζ (-k) g := by
    intro k g
    have hmul : Stage3AutomorphicDescent.zmodChar ζ (-k) g *
        Stage3AutomorphicDescent.zmodChar ζ k g = 1 := by
      rw [← Stage3AutomorphicDescent.zmodChar_add_left hζ.pow_eq_one, neg_add_cancel,
        Stage3AutomorphicDescent.zmodChar_zero_left]
    have hnorm : ‖Stage3AutomorphicDescent.zmodChar ζ k g‖ = 1 := by
      unfold Stage3AutomorphicDescent.zmodChar
      rw [norm_pow, hζ.norm'_eq_one hp.ne', one_pow]
    have hcmul : star (Stage3AutomorphicDescent.zmodChar ζ k g) *
        Stage3AutomorphicDescent.zmodChar ζ k g = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hnorm]
      norm_num
    have hne : Stage3AutomorphicDescent.zmodChar ζ k g ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnorm
      norm_num at hnorm
    exact mul_right_cancel₀ hne (hcmul.trans hmul.symm)
  intro k₁ k₂
  unfold charInner
  have hsum :
      ∑ g : ZMod p, star (Stage3AutomorphicDescent.zmodChar ζ k₁ g) *
          Stage3AutomorphicDescent.zmodChar ζ k₂ g =
        ∑ g : ZMod p, Stage3AutomorphicDescent.zmodChar ζ g (k₂ - k₁) := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hstar, ← Stage3AutomorphicDescent.zmodChar_add_left hζ.pow_eq_one, neg_add_eq_sub]
    unfold Stage3AutomorphicDescent.zmodChar
    rw [mul_comm]
  rw [hcard, hsum, Stage3AutomorphicDescent.zmodChar_sum_dual hζ (k₂ - k₁)]
  by_cases h : k₁ = k₂
  · subst h
    rw [sub_self, if_pos rfl, if_pos rfl, inv_mul_cancel₀ hpne]
  · rw [if_neg (sub_ne_zero.mpr (Ne.symm h)), if_neg h, mul_zero]

/-! ### Jacquet–Langlands Spectral Transfer & Cyclic Base-Change Twisted Trace -/

/-- **Jacquet–Langlands Multiplicity Transfer (Same-Group Conjugacy-Matching Form)**:
if two finite quotients `(G, Γ₁)` and `(G, Γ₂)` have matching geometric sides
(`∀ f, geomSide Γ₁ f = geomSide Γ₂ f`) and decompose over a common family of representations
with orthogonal characters `χ_i = repChar (rep i)`, then:
1. Their spectral traces match identically for every test function `f : G → ℂ`,
2. Their automorphic character sums match pointwise on `G`,
3. **Every spectral multiplicity matches identically: `∀ i, m₁ i = m₂ i`**! -/
theorem jacquet_langlands_same_group_transfer {G : Type*} [Group G] [Fintype G]
    (Γ₁ Γ₂ : Subgroup G)
    [Fintype Γ₁] [Fintype (RightCosetSpace G Γ₁)]
    [Fintype Γ₂] [Fintype (RightCosetSpace G Γ₂)]
    {ι : Type*} [Fintype ι]
    (D₁ : SpectralDecomposition G Γ₁ ι)
    (D₂ : SpectralDecomposition G Γ₂ ι)
    (hchar_eq : ∀ i : ι, ∀ g : G, repChar (D₁.rep i) g = repChar (D₂.rep i) g)
    (horth : IsOrthogonalChars (fun i => repChar (D₁.rep i)))
    (hgeom : ∀ f : G → ℂ, geomSide Γ₁ f = geomSide Γ₂ f) :
    (∀ f : G → ℂ, D₁.specSide f = D₂.specSide f) ∧
    (∀ g : G, ∑ i : ι, (D₁.mult i : ℂ) * repChar (D₁.rep i) g =
      ∑ i : ι, (D₂.mult i : ℂ) * repChar (D₂.rep i) g) ∧
    (∀ i : ι, D₁.mult i = D₂.mult i) := by
  have hspec : ∀ f : G → ℂ, D₁.specSide f = D₂.specSide f := fun f => by
    rw [selberg_arthur_trace_formula Γ₁ D₁ f, hgeom f, ← selberg_arthur_trace_formula Γ₂ D₂ f]
  have htest : ∀ f : G → ℂ,
      (∑ i : ι, (D₁.mult i : ℂ) * ∑ g : G, f g * repChar (D₁.rep i) g) =
        ∑ i : ι, (D₂.mult i : ℂ) * ∑ g : G, f g * repChar (D₁.rep i) g := by
    intro f
    have h := hspec f
    rw [D₁.specSide_eq_sum_char, D₂.specSide_eq_sum_char] at h
    simpa only [← hchar_eq] using h
  obtain ⟨hpt, hmultC⟩ := eq_of_forall_test_orthogonalChars horth htest
  refine ⟨hspec, ?_, fun i => Nat.cast_injective (hmultC i)⟩
  intro g
  simpa only [← hchar_eq] using hpt g

/-- **General Cross-Group Jacquet–Langlands Spectral Transfer Theorem**:
suppose `(G₁, Γ₁)` and `(G₂, Γ₂)` are two finite quotients with spectral decompositions `D₁, D₂`
indexed by `ι`, linked by a **test-function transfer `T : (G₁ → ℂ) → (G₂ → ℂ)`** satisfying:
- **Matching Geometric Sides / Orbital Integrals**: `∀ f, geomSide Γ₁ f = geomSide Γ₂ (T f)`,
- **Local Jacquet–Langlands Character Identity**: `∀ i f, Tr(ρ₂ i (T f)) = Tr(ρ₁ i f)`,
- **Orthogonality of Characters on `G₁`**: `IsOrthogonalChars (fun i => repChar (D₁.rep i))`.
Then unconditionally:
1. Spectral traces match identically: `∀ f, D₁.specSide f = D₂.specSide (T f)`,
2. Pointwise spectral character traces match identically,
3. **Every automorphic spectral multiplicity transfers identically: `∀ i, D₁.mult i = D₂.mult i`**! -/
theorem jacquet_langlands_transfer_of_matching_orbital
    {G₁ G₂ : Type*} [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂]
    (Γ₁ : Subgroup G₁) [Fintype Γ₁] [Fintype (RightCosetSpace G₁ Γ₁)]
    (Γ₂ : Subgroup G₂) [Fintype Γ₂] [Fintype (RightCosetSpace G₂ Γ₂)]
    {ι : Type*} [Fintype ι]
    (D₁ : SpectralDecomposition G₁ Γ₁ ι)
    (D₂ : SpectralDecomposition G₂ Γ₂ ι)
    (T : (G₁ → ℂ) → (G₂ → ℂ))
    (hgeom : ∀ f : G₁ → ℂ, geomSide Γ₁ f = geomSide Γ₂ (T f))
    (hchar_transfer : ∀ (i : ι) (f : G₁ → ℂ),
      LinearMap.trace ℂ (D₂.V i) (repConvOp (D₂.rep i) (T f)) =
        LinearMap.trace ℂ (D₁.V i) (repConvOp (D₁.rep i) f))
    (horth : IsOrthogonalChars (fun i => repChar (D₁.rep i))) :
    (∀ f : G₁ → ℂ, D₁.specSide f = D₂.specSide (T f)) ∧
    (∀ g : G₁, ∑ i : ι, (D₁.mult i : ℂ) * repChar (D₁.rep i) g =
      ∑ i : ι, (D₂.mult i : ℂ) * repChar (D₁.rep i) g) ∧
    (∀ i : ι, D₁.mult i = D₂.mult i) := by
  have hspec : ∀ f : G₁ → ℂ, D₁.specSide f = D₂.specSide (T f) := fun f => by
    rw [selberg_arthur_trace_formula Γ₁ D₁ f, hgeom f, ← selberg_arthur_trace_formula Γ₂ D₂ (T f)]
  have htest : ∀ f : G₁ → ℂ,
      (∑ i : ι, (D₁.mult i : ℂ) * ∑ g : G₁, f g * repChar (D₁.rep i) g) =
        ∑ i : ι, (D₂.mult i : ℂ) * ∑ g : G₁, f g * repChar (D₁.rep i) g := by
    intro f
    have h := hspec f
    unfold SpectralDecomposition.specSide at h
    simp_rw [hchar_transfer, trace_repConvOp] at h
    exact h
  obtain ⟨hpt, hmultC⟩ := eq_of_forall_test_orthogonalChars horth htest
  exact ⟨hspec, hpt, fun i => Nat.cast_injective (hmultC i)⟩

/-- **Cyclic Base-Change Twisted Trace Projection** (bridging `Stage3AutomorphicDescent`):
for any prime-order character `η : G →* ℂˣ` (`∀ g, η g ^ p = 1`) and any test function `f : G → ℂ`,
summing the `η^j`-twisted traces over `j : Fin p` projects cleanly onto `ker η`:
`∑_{j : Fin p} Tr(R(η^j · f) | L²(Γ \ G)) = p · Tr(R(1_{ker η} · f) | L²(Γ \ G))`! -/
theorem cyclic_baseChange_twisted_trace {G : Type*} [Group G] [Fintype G] (Γ : Subgroup G)
    [Fintype Γ] [Fintype (RightCosetSpace G Γ)]
    {p : ℕ} (η : G →* ℂˣ) (hη : ∀ g : G, (η g : ℂ) ^ p = 1) (f : G → ℂ)
    [DecidablePred (· ∈ η.ker)] :
    (∑ j : Fin p,
      LinearMap.trace ℂ (AutomorphicL2 G Γ)
        (rightConvOp Γ (fun g => (η g : ℂ) ^ (j : ℕ) * f g))) =
      (p : ℂ) * LinearMap.trace ℂ (AutomorphicL2 G Γ)
        (rightConvOp Γ (fun g => if g ∈ η.ker then f g else 0)) := by
  have hlin : ∀ h : G → ℂ,
      LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightConvOp Γ h) =
        ∑ g : G, h g * LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightRegOp Γ g) := by
    intro h
    unfold rightConvOp
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, smul_eq_mul]
  simp_rw [hlin]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hsum : (∑ j : Fin p, (η g : ℂ) ^ (j : ℕ)) = if g ∈ η.ker then (p : ℂ) else 0 := by
    rw [Stage3AutomorphicDescent.sum_fin_pow_eq_ite (hη g)]
    by_cases hker : g ∈ η.ker
    · have h1 : (η g : ℂ) = 1 := by
        have : η g = 1 := hker
        rw [this, Units.val_one]
      rw [if_pos h1, if_pos hker]
    · have h1 : (η g : ℂ) ≠ 1 := by
        intro hc
        apply hker
        change η g = 1
        exact Units.ext hc
      rw [if_neg h1, if_neg hker]
  calc ∑ j : Fin p, (η g : ℂ) ^ (j : ℕ) * f g *
          LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightRegOp Γ g)
      = (∑ j : Fin p, (η g : ℂ) ^ (j : ℕ)) *
          (f g * LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightRegOp Γ g)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
    _ = (if g ∈ η.ker then (p : ℂ) else 0) *
          (f g * LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightRegOp Γ g)) := by rw [hsum]
    _ = (p : ℂ) * ((if g ∈ η.ker then f g else 0) *
          LinearMap.trace ℂ (AutomorphicL2 G Γ) (rightRegOp Γ g)) := by
          split_ifs <;> ring

end JacquetLanglandsTransfer

/-! ## Section 3: 1D & `n`-D Lattice Poisson Summation, Theta Functional Equation & Flat-Torus Weyl Law -/

section LatticePoissonAndWeyl

/-! ### 1D Scaled Gaussian Poisson Summation -/

/-- One-dimensional scaled Gaussian theta series `θ_a(t) = ∑'_{n ∈ ℤ} exp(-π t (a n)²)`. -/
def theta1D (a t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * t * (a * (n : ℝ)) ^ 2)

/-- Unconditional summability of the 1D scaled Gaussian theta series for `a > 0, t > 0`. -/
theorem summable_theta1D {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * (a * (n : ℝ)) ^ 2)) := by
  have hta : 0 < t * a ^ 2 := by positivity
  refine summable_of_sum_le (c := 6 + 4 / Real.sqrt (t * a ^ 2))
    (fun _ => (Real.exp_pos _).le) fun s => ?_
  have h := Stage3ThetaSiegelBridge.sum_int_exp_shifted_le hta 0 s
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1; ring

/-- **Exact 1D Scaled Lattice Poisson Summation / Theta Functional Equation**
(direct from Mathlib's `Real.tsum_exp_neg_mul_int_sq`):
for every `a > 0` and `t > 0`, `θ_a(t) = t^{-1/2} · a⁻¹ · θ_{a⁻¹}(t⁻¹)`. -/
theorem theta1D_functional_eq {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    theta1D a t = t ^ (-(1 / 2 : ℝ)) * a⁻¹ * theta1D a⁻¹ t⁻¹ := by
  unfold theta1D
  have hta : 0 < t * a ^ 2 := by positivity
  have hlhs : (fun n : ℤ => Real.exp (-Real.pi * t * (a * (n : ℝ)) ^ 2)) =
      fun n : ℤ => Real.exp (-Real.pi * (t * a ^ 2) * (n : ℝ) ^ 2) := by
    funext n; congr 1; ring
  have hrhs : (fun n : ℤ => Real.exp (-Real.pi / (t * a ^ 2) * (n : ℝ) ^ 2)) =
      fun n : ℤ => Real.exp (-Real.pi * t⁻¹ * (a⁻¹ * (n : ℝ)) ^ 2) := by
    funext n; congr 1
    field_simp [ha.ne', ht.ne']
  rw [hlhs, Real.tsum_exp_neg_mul_int_sq hta, hrhs]
  congr 1
  have hpow : (t * a ^ 2) ^ ((1 : ℝ) / 2) = t ^ ((1 : ℝ) / 2) * a := by
    rw [Real.mul_rpow ht.le (sq_nonneg a), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
    norm_num
  rw [hpow, one_div, mul_inv, Real.rpow_neg ht.le]

/-- **Multi-Dimensional Product Factorization for `tsum` over `Fin r → ℤ`**:
if each coordinate factor `f i : ℤ → ℝ` is nonnegative and summable, then
`∑' c : Fin r → ℤ, ∏ i, f i (c i) = ∏ i, ∑' n : ℤ, f i n`. -/
theorem summable_and_tsum_pi_fin_prod :
    ∀ {r : ℕ} (f : Fin r → ℤ → ℝ),
      (∀ i n, 0 ≤ f i n) →
      (∀ i, Summable (f i)) →
      Summable (fun c : Fin r → ℤ => ∏ i : Fin r, f i (c i)) ∧
        (∑' c : Fin r → ℤ, ∏ i : Fin r, f i (c i)) = ∏ i : Fin r, ∑' n : ℤ, f i n
  | 0, f, _, _ => by
      refine ⟨(hasSum_fintype _).summable, ?_⟩
      rw [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
      simp
  | r + 1, f, hnn, hsum => by
      let f' : Fin r → ℤ → ℝ := fun i => f i.succ
      have ⟨hsum', htsum'⟩ := summable_and_tsum_pi_fin_prod f'
        (fun i n => hnn i.succ n) (fun i => hsum i.succ)
      let e : (ℤ × (Fin r → ℤ)) ≃ (Fin (r + 1) → ℤ) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun c => (c 0, fun i => c i.succ)
          left_inv := fun p => by ext <;> simp
          right_inv := fun c => by
            funext i
            refine Fin.cases rfl (fun _ => rfl) i }
      have hprod_sum : Summable (fun p : ℤ × (Fin r → ℤ) =>
          f 0 p.1 * ∏ i : Fin r, f' i (p.2 i)) :=
        Summable.mul_of_nonneg (hsum 0) hsum'
          (fun n => hnn 0 n)
          (fun c' => Finset.prod_nonneg fun i _ => hnn i.succ (c' i))
      have hcomp : (fun c : Fin (r + 1) → ℤ => ∏ i : Fin (r + 1), f i (c i)) ∘ e =
          fun p : ℤ × (Fin r → ℤ) => f 0 p.1 * ∏ i : Fin r, f' i (p.2 i) := by
        funext p
        dsimp only [Function.comp_apply, e, f']
        rw [Fin.prod_univ_succ]
        simp
      have hsum_full : Summable (fun c : Fin (r + 1) → ℤ => ∏ i : Fin (r + 1), f i (c i)) := by
        rw [← Equiv.summable_iff e, hcomp]
        exact hprod_sum
      refine ⟨hsum_full, ?_⟩
      rw [Fin.prod_univ_succ, ← htsum', (hsum 0).tsum_mul_tsum hsum' hprod_sum]
      rw [← hcomp]
      exact (e.tsum_eq (fun c : Fin (r + 1) → ℤ => ∏ i : Fin (r + 1), f i (c i))).symm

/-! ### Canonical Dual Lattice `dualLattice L`, Orthogonal Lattices & Exact `n`-D Functional Equation -/

section OrthogonalLatticeTheta

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Canonical Dual Lattice `L*`** inside `span ℝ L ⊆ E`:
`L* = { w ∈ span ℝ L | ∀ v ∈ L, ⟨w, v⟩ ∈ ℤ }`. -/
def dualLattice (L : Submodule ℤ E) : Submodule ℤ E where
  carrier := { w : E | w ∈ Submodule.span ℝ (L : Set E) ∧
    ∀ v ∈ L, ∃ m : ℤ, inner ℝ w v = (m : ℝ) }
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro w₁ w₂ ⟨hw₁S, hw₁⟩ ⟨hw₂S, hw₂⟩
    refine ⟨Submodule.add_mem _ hw₁S hw₂S, fun v hv => ?_⟩
    obtain ⟨m₁, hm₁⟩ := hw₁ v hv
    obtain ⟨m₂, hm₂⟩ := hw₂ v hv
    exact ⟨m₁ + m₂, by rw [inner_add_left, hm₁, hm₂]; push_cast; rfl⟩
  smul_mem' := by
    rintro k w ⟨hwS, hw⟩
    refine ⟨?_, fun v hv => ?_⟩
    · rw [← Int.cast_smul_eq_zsmul ℝ]
      exact Submodule.smul_mem _ (k : ℝ) hwS
    · obtain ⟨m, hm⟩ := hw v hv
      exact ⟨k * m, by
        rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hm]
        push_cast; rfl⟩

/-- Orthogonality predicate for a `ℤ`-basis `b : Basis (Fin r) ℤ L` of a lattice `L ⊂ E`. -/
def IsOrthogonalBasis {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L) : Prop :=
  ∀ i j : Fin r, i ≠ j → inner ℝ (b i : E) (b j : E) = 0

/-- Dual basis vector `b*_i = ‖b_i‖⁻² • b_i` attached to an orthogonal `ℤ`-basis `b`. -/
def dualVec {L : Submodule ℤ E} {r : ℕ} (b : Basis (Fin r) ℤ L) (i : Fin r) : E :=
  (‖(b i : E)‖ ^ 2)⁻¹ • (b i : E)

lemma norm_basis_pos {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (i : Fin r) :
    0 < ‖(b i : E)‖ := by
  have hli := linearIndependent_coe_basis L b
  exact norm_pos_iff.mpr (hli.ne_zero i)

lemma inner_dualVec_basis {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (i j : Fin r) :
    inner ℝ (dualVec b i) (b j : E) = if i = j then 1 else 0 := by
  unfold dualVec
  rw [real_inner_smul_left]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, real_inner_self_eq_norm_sq,
      inv_mul_cancel₀ (pow_ne_zero 2 (norm_basis_pos b i).ne')]
  · rw [if_neg hij, hb i j hij, mul_zero]

lemma norm_dualVec {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (i : Fin r) :
    ‖dualVec b i‖ = ‖(b i : E)‖⁻¹ := by
  unfold dualVec
  have hpos := norm_basis_pos b i
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  field_simp [hpos.ne']

omit [FiniteDimensional ℝ E] in
lemma inner_dualVec_dualVec {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {i j : Fin r} (hij : i ≠ j) :
    inner ℝ (dualVec b i) (dualVec b j) = 0 := by
  unfold dualVec
  rw [real_inner_smul_left, real_inner_smul_right, hb i j hij, mul_zero, mul_zero]

lemma dualVec_mem_dualLattice {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (i : Fin r) :
    dualVec b i ∈ dualLattice L := by
  constructor
  · unfold dualVec
    exact Submodule.smul_mem _ _ (Submodule.subset_span (b i).2)
  · intro v hv
    let x : L := ⟨v, hv⟩
    refine ⟨b.repr x i, ?_⟩
    have hx : v = ∑ j : Fin r, (b.repr x j : ℝ) • (b j : E) := by
      have h1 : x = ∑ j : Fin r, b.repr x j • b j := (b.sum_repr x).symm
      have h2 := congrArg (fun y : L => (y : E)) h1
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul] using h2
    rw [hx, inner_sum]
    rw [Finset.sum_eq_single i]
    · rw [real_inner_smul_right, inner_dualVec_basis b hb i i, if_pos rfl, mul_one]
    · intro j _ hj
      rw [real_inner_smul_right, inner_dualVec_basis b hb i j, if_neg (Ne.symm hj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

/-- Every `w ∈ span ℝ L` expands along the orthogonal basis `b` as `w = ∑ i, ⟨w, b_i⟩ • b*_i`. -/
lemma mem_span_real_orthogonal_expansion {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {w : E}
    (hw : w ∈ Submodule.span ℝ (L : Set E)) :
    w = ∑ i : Fin r, (inner ℝ w (b i : E)) • dualVec b i := by
  have hspanZ : Submodule.span ℤ (Set.range fun i => (b i : E)) = L := by
    have : Set.range (fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp _ _
    rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have hspanR : Submodule.span ℝ (Set.range fun i => (b i : E)) = Submodule.span ℝ (L : Set E) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range fun i => (b i : E)), hspanZ]
  rw [← hspanR, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, rfl⟩ := hw
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_inner, Finset.sum_eq_single i]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    unfold dualVec
    rw [smul_smul, mul_inv_cancel_right₀ (pow_ne_zero 2 (norm_basis_pos b i).ne')]
  · intro j _ hj
    rw [real_inner_smul_left, hb j i hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- For an orthogonal lattice `L`, `dualLattice L` is the `ℤ`-span of `dualVec b`. -/
theorem dualLattice_eq_span_dualVec {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    dualLattice L = Submodule.span ℤ (Set.range (dualVec b)) := by
  apply le_antisymm
  · intro w hw
    have hexp := mem_span_real_orthogonal_expansion b hb hw.1
    rw [hexp]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := hw.2 (b i : E) (b i).2
    rw [hm, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ m (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact dualVec_mem_dualLattice b hb i

/-- Explicit orthogonal `ℤ`-basis `dualBasis b : Basis (Fin r) ℤ (dualLattice L)` of `L*`. -/
def dualBasis {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    Basis (Fin r) ℤ (dualLattice L) :=
  Basis.mk
    (v := fun i => ⟨dualVec b i, dualVec_mem_dualLattice b hb i⟩)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hval : ∑ j : Fin r, (c j : ℝ) • dualVec b j = 0 := by
        have h := congrArg (fun y : dualLattice L => (y : E)) hc
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul,
          ZeroMemClass.coe_zero] using h
      have hinner : inner ℝ (∑ j : Fin r, (c j : ℝ) • dualVec b j) (b i : E) = 0 := by
        rw [hval, inner_zero_left]
      rw [sum_inner, Finset.sum_eq_single i] at hinner
      · rw [real_inner_smul_left, inner_dualVec_basis b hb i i, if_pos rfl, mul_one] at hinner
        exact_mod_cast hinner
      · intro j _ hj
        rw [real_inner_smul_left, inner_dualVec_basis b hb j i, if_neg hj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h)
    (by
      intro w _
      have hw : (w : E) ∈ Submodule.span ℤ (Set.range (dualVec b)) := by
        rw [← dualLattice_eq_span_dualVec b hb]
        exact w.2
      rw [Submodule.mem_span_range_iff_exists_fun] at hw
      obtain ⟨c, hc⟩ := hw
      have hsum : w = ∑ i : Fin r, c i • (⟨dualVec b i, dualVec_mem_dualLattice b hb i⟩ : dualLattice L) := by
        apply Subtype.ext
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using hc.symm
      rw [hsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp]
lemma dualBasis_coe {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (i : Fin r) :
    ((dualBasis b hb i : dualLattice L) : E) = dualVec b i := by
  simp [dualBasis]

lemma dualBasis_isOrthogonal {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    IsOrthogonalBasis (dualBasis b hb) := by
  intro i j hij
  rw [dualBasis_coe, dualBasis_coe]
  exact inner_dualVec_dualVec b hb hij

/-- The dual lattice `L*` of any discrete orthogonal lattice `L` is automatically discrete! -/
theorem discreteTopology_dualLattice_of_orthogonal {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    DiscreteTopology (dualLattice L) := by
  let f : dualLattice L → (Fin r → ℤ) := fun w i => (dualBasis b hb).repr w i
  have hf_inj : Function.Injective f := fun w₁ w₂ h =>
    (dualBasis b hb).repr.injective (Finsupp.ext (congrFun h))
  have hf_cont : Continuous f := by
    refine continuous_pi fun i => ?_
    have heq : (fun w : dualLattice L => ((f w i : ℤ) : ℝ)) =
        fun w : dualLattice L => inner ℝ (w : E) (b i : E) := by
      funext w
      have hw : (w : E) = ∑ j : Fin r, ((f w j : ℤ) : ℝ) • dualVec b j := by
        have h := congrArg (fun y : dualLattice L => (y : E)) ((dualBasis b hb).sum_repr w).symm
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul,
          dualBasis_coe, f] using h
      rw [hw, sum_inner, Finset.sum_eq_single i]
      · rw [real_inner_smul_left, inner_dualVec_basis b hb i i, if_pos rfl, mul_one]
      · intro j _ hj
        rw [real_inner_smul_left, inner_dualVec_basis b hb j i, if_neg hj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hcontR : Continuous (fun w : dualLattice L => ((f w i : ℤ) : ℝ)) := by
      rw [heq]
      exact continuous_subtype_val.inner continuous_const
    exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hcontR
  exact DiscreteTopology.of_continuous_injective hf_cont hf_inj

/-- **Biduality `(L*)* = L`** for any discrete orthogonal lattice `L`. -/
theorem dualLattice_dualLattice_of_orthogonal {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    dualLattice (dualLattice L) = L := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  rw [dualLattice_eq_span_dualVec (dualBasis b hb) (dualBasis_isOrthogonal b hb)]
  have hvec : dualVec (dualBasis b hb) = fun i => (b i : E) := by
    funext i
    unfold dualVec
    rw [dualBasis_coe, norm_dualVec, inv_pow, inv_inv]
    unfold dualVec
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 2 (norm_basis_pos b i).ne'), one_smul]
  rw [hvec]
  have : Set.range (fun i => (b i : E)) = L.subtype '' Set.range b := Set.range_comp _ _
  rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

/-- **Exact Covolume Product Formula for Orthogonal Lattices**:
`covol L = ∏ i : Fin r, ‖b_i‖`. -/
theorem covol_of_orthogonalBasis {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    covol L = ∏ i : Fin r, ‖(b i : E)‖ := by
  rw [covol_eq_sqrt_det_gram L b]
  have hdiag : Matrix.gram ℝ (fun i => (b i : E)) =
      Matrix.diagonal (fun i => ‖(b i : E)‖ ^ 2) := by
    ext i j
    rw [Matrix.gram_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, real_inner_self_eq_norm_sq]
    · rw [if_neg hij, hb i j hij]
  have hsq : (∏ i : Fin r, ‖(b i : E)‖ ^ 2) = (∏ i : Fin r, ‖(b i : E)‖) ^ 2 :=
    Finset.prod_pow (Finset.univ : Finset (Fin r)) 2 (fun i => ‖(b i : E)‖)
  rw [hdiag, Matrix.det_diagonal, hsq,
    Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg _)]

/-- **Exact Dual-Lattice Covolume Identity**:
`covol (L*) = (covol L)⁻¹`. -/
theorem covol_dualLattice_of_orthogonalBasis {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    covol (dualLattice L) = (covol L)⁻¹ := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  rw [covol_of_orthogonalBasis (dualBasis b hb) (dualBasis_isOrthogonal b hb),
    covol_of_orthogonalBasis b hb, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [dualBasis_coe, norm_dualVec]

omit [FiniteDimensional ℝ E] in
/-- Pythagorean squared-norm expansion for an orthogonal `ℤ`-basis:
`‖∑ i, c i • b_i‖² = ∑ i, (c i * ‖b_i‖)²`. -/
lemma norm_sq_sum_orthogonalBasis {L : Submodule ℤ E} {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (c : Fin r → ℤ) :
    ‖∑ i : Fin r, c i • (b i : E)‖ ^ 2 = ∑ i : Fin r, (‖(b i : E)‖ * (c i : ℝ)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · simp_rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  · intro j _ hj
    simp_rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [real_inner_smul_left, real_inner_smul_right, hb i j (Ne.symm hj), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Exact Product Factorization of `Stage3ThetaSiegelBridge.latticeTheta`** on an orthogonal lattice:
`Θ_L(t) = ∏ i : Fin r, θ_{‖b_i‖}(t)`. -/
theorem latticeTheta_eq_prod_theta1D {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {t : ℝ} (ht : 0 < t) :
    latticeTheta L t = ∏ i : Fin r, theta1D ‖(b i : E)‖ t := by
  let e : (Fin r → ℤ) ≃ L :=
    { toFun := fun c => ∑ i : Fin r, c i • b i
      invFun := fun v i => b.repr v i
      left_inv := fun c => by
        funext i
        simp only [map_sum, map_zsmul, Basis.repr_self, Finsupp.finsetSum_apply,
          Finsupp.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [Finsupp.single_eq_of_ne (Ne.symm hj)]
        · intro h; exact absurd (Finset.mem_univ i) h
      right_inv := fun v => b.sum_repr v }
  unfold latticeTheta
  rw [← e.tsum_eq]
  have hterm : ∀ c : Fin r → ℤ,
      gaussianTerm t ((e c : L) : E) =
        ∏ i : Fin r, Real.exp (-Real.pi * t * (‖(b i : E)‖ * (c i : ℝ)) ^ 2) := by
    intro c
    unfold gaussianTerm
    have hcoe : ((e c : L) : E) = ∑ i : Fin r, c i • (b i : E) := by
      simp [e]
    rw [hcoe, norm_sq_sum_orthogonalBasis b hb c, Finset.mul_sum, Real.exp_sum]
  simp_rw [hterm]
  exact (summable_and_tsum_pi_fin_prod
    (fun i n => Real.exp (-Real.pi * t * (‖(b i : E)‖ * (n : ℝ)) ^ 2))
    (fun _ _ => (Real.exp_pos _).le)
    (fun i => summable_theta1D (norm_basis_pos b i) ht)).2

/-- **EXACT MULTI-DIMENSIONAL ORTHOGONAL-LATTICE THETA FUNCTIONAL EQUATION (POISSON SUMMATION)**:
for every discrete orthogonal `ℤ`-lattice `L ⊂ E` of rank `r` and every `t > 0`,
$$\Theta_L(t) = t^{-r/2} \cdot \operatorname{covol}(L)^{-1} \cdot \Theta_{L^*}(t^{-1}).$$ -/
theorem latticeTheta_functional_eq_orthogonal {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {t : ℝ} (ht : 0 < t) :
    latticeTheta L t =
      t ^ (-((r : ℝ) / 2)) * (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹ := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  rw [latticeTheta_eq_prod_theta1D b hb ht,
    latticeTheta_eq_prod_theta1D (dualBasis b hb) (dualBasis_isOrthogonal b hb) (inv_pos.mpr ht),
    covol_of_orthogonalBasis b hb]
  have hfac : ∀ i : Fin r,
      theta1D ‖(b i : E)‖ t =
        t ^ (-(1 / 2 : ℝ)) * ‖(b i : E)‖⁻¹ * theta1D ‖((dualBasis b hb i : dualLattice L) : E)‖ t⁻¹ := by
    intro i
    rw [dualBasis_coe, norm_dualVec]
    exact theta1D_functional_eq (norm_basis_pos b i) ht
  simp_rw [hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_inv_distrib]
  have hpow : (t ^ (-(1 / 2 : ℝ))) ^ r = t ^ (-((r : ℝ) / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1; ring
  rw [hpow]

/-- **Dual Form of the Orthogonal-Lattice Theta Functional Equation**:
$$\Theta_{L^*}(t) = t^{-r/2} \cdot \operatorname{covol}(L) \cdot \Theta_L(t^{-1}).$$ -/
theorem latticeTheta_dual_functional_eq_orthogonal {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {t : ℝ} (ht : 0 < t) :
    latticeTheta (dualLattice L) t =
      t ^ (-((r : ℝ) / 2)) * covol L * latticeTheta L t⁻¹ := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  have h := latticeTheta_functional_eq_orthogonal (dualBasis b hb) (dualBasis_isOrthogonal b hb) ht
  rwa [covol_dualLattice_of_orthogonalBasis b hb, inv_inv,
    dualLattice_dualLattice_of_orthogonal b hb] at h

/-- **1D Lattice Functional Equation Special Case (`L = ℤ · v`, `v ≠ 0`)**:
`Θ_{ℤ·v}(t) = t^{-1/2} · covol(ℤ·v)⁻¹ · Θ_{(ℤ·v)*}(t⁻¹)`. -/
theorem latticeTheta_span_singleton_functional_eq {v : E} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    let L : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
    latticeTheta L t =
      t ^ (-(1 / 2 : ℝ)) * (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹ := by
  intro L
  let e : ℤ ≃ₗ[ℤ] L :=
    { toFun := fun n => ⟨n • v, Submodule.smul_mem _ n (Submodule.subset_span rfl)⟩
      invFun := fun x => Classical.choose (Submodule.mem_span_singleton.mp x.2)
      map_add' := fun m n => Subtype.ext (add_zsmul v m n)
      map_smul' := fun m n => Subtype.ext (by simp [mul_zsmul])
      left_inv := fun n => by
        have hc := Classical.choose_spec
          (Submodule.mem_span_singleton.mp (Submodule.smul_mem L n (Submodule.subset_span rfl)))
        have hsub : ((Classical.choose
          (Submodule.mem_span_singleton.mp (Submodule.smul_mem L n (Submodule.subset_span rfl)))
            - n : ℤ) : ℝ) • v = 0 := by
          rw [Int.cast_sub, sub_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, hc, sub_self]
        rcases smul_eq_zero.mp hsub with h0 | h0
        · exact sub_eq_zero.mp (by exact_mod_cast h0)
        · exact absurd h0 hv
      right_inv := fun x => Subtype.ext
        (Classical.choose_spec (Submodule.mem_span_singleton.mp x.2)) }
  have : DiscreteTopology L := by
    have hcont : Continuous (fun x : L => (inner ℝ v (x : E)) / ‖v‖ ^ 2) :=
      (continuous_const.inner continuous_subtype_val).div_const _
    have hinv : ∀ x : L, (e.symm x : ℝ) = inner ℝ v (x : E) / ‖v‖ ^ 2 := by
      intro x
      have hx : (x : E) = (e.symm x : ℤ) • v := (congrArg Subtype.val (e.apply_symm_apply x)).symm
      rw [hx, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_self_eq_norm_sq]
      have hvn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
      field_simp [hvn]
    refine DiscreteTopology.of_continuous_injective (f := fun x : L => (e.symm x : ℤ)) ?_
      e.symm.injective
    have hcast : Continuous (fun x : L => ((e.symm x : ℤ) : ℝ)) := by
      simpa only [funext hinv] using hcont
    exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hcast
  let b : Basis (Fin 1) ℤ L := (Basis.singleton (Fin 1) ℤ).map e
  have hb : IsOrthogonalBasis b := fun i j hij => absurd (Subsingleton.elim i j) hij
  simpa using latticeTheta_functional_eq_orthogonal b hb ht

/-! ### Direct Bridge to `Stage3ExplicitSpectral`: Flat-Torus Heat-Kernel Asymptotics & Weyl Law -/

/-- Normalized flat-torus spectrum `D_L` indexed by `v ∈ L` with eigenvalues `λ_v = π ‖v‖²` and
unit multiplicities (spectrum of `-(1 / (4 π)) Δ` on the dual flat torus `ℝ^r / L*`). -/
def torusSpectrum (L : Submodule ℤ E) : DiscreteSpectrum L where
  eig v := Real.pi * ‖(v : E)‖ ^ 2
  mult _ := 1
  eig_nonneg _ := mul_nonneg Real.pi_pos.le (sq_nonneg _)
  mult_nonneg _ := zero_le_one

/-- Standard Euclidean Laplacian `-Δ` spectrum on the flat torus `ℝ^r / L`, indexed by dual
lattice frequencies `w ∈ L*` with eigenvalues `λ_w = 4 π² ‖w‖²` and unit multiplicities. -/
def torusLaplacianSpectrum (L : Submodule ℤ E) : DiscreteSpectrum (dualLattice L) where
  eig w := 4 * Real.pi ^ 2 * ‖(w : E)‖ ^ 2
  mult _ := 1
  eig_nonneg _ := by positivity
  mult_nonneg _ := zero_le_one

theorem torusSpectrum_heatSummable (L : Submodule ℤ E) [DiscreteTopology L] {t : ℝ} (ht : 0 < t) :
    (torusSpectrum L).HeatSummable t := by
  unfold DiscreteSpectrum.HeatSummable torusSpectrum
  refine (summable_gaussianTerm L ht).congr fun v => ?_
  unfold gaussianTerm
  simp only [one_mul]
  congr 1; ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem torusSpectrum_heatTrace_eq_latticeTheta (L : Submodule ℤ E) (t : ℝ) :
    (torusSpectrum L).heatTrace t = latticeTheta L t := by
  unfold DiscreteSpectrum.heatTrace torusSpectrum latticeTheta gaussianTerm
  congr 1; funext v
  simp only [one_mul]
  congr 1; ring

theorem torusLaplacian_heatSummable {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {t : ℝ} (ht : 0 < t) :
    (torusLaplacianSpectrum L).HeatSummable t := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  unfold DiscreteSpectrum.HeatSummable torusLaplacianSpectrum
  have h4πt : 0 < 4 * Real.pi * t := by positivity
  refine (summable_gaussianTerm (dualLattice L) h4πt).congr fun w => ?_
  unfold gaussianTerm
  simp only [one_mul]
  congr 1; ring

omit [FiniteDimensional ℝ E] in
theorem torusLaplacian_heatTrace_eq_latticeTheta (L : Submodule ℤ E) (t : ℝ) :
    (torusLaplacianSpectrum L).heatTrace t = latticeTheta (dualLattice L) (4 * Real.pi * t) := by
  unfold DiscreteSpectrum.heatTrace torusLaplacianSpectrum latticeTheta gaussianTerm
  congr 1; funext w
  simp only [one_mul]
  congr 1; ring

/-- **Exact `t^{-r/2}` Flat-Torus Heat-Kernel Asymptotic Limit (`t → 0⁺`)**:
`t^{r/2} · Z_L(t) → covol(L)⁻¹` as `t → 0⁺`! -/
theorem torusSpectrum_heatTrace_asymptotic {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    Tendsto (fun t : ℝ => t ^ ((r : ℝ) / 2) * (torusSpectrum L).heatTrace t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (covol L)⁻¹) := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  have hinv_top : Tendsto (fun t : ℝ => t⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have htheta : Tendsto (fun t : ℝ => (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((covol L)⁻¹ * 1)) :=
    (Stage3ThetaSiegelBridge.latticeTheta_tendsto_one (dualLattice L) |>.comp hinv_top).const_mul _
  rw [mul_one] at htheta
  refine htheta.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_pos : 0 < t := ht
  rw [torusSpectrum_heatTrace_eq_latticeTheta, latticeTheta_functional_eq_orthogonal b hb ht_pos]
  have hcancel : t ^ ((r : ℝ) / 2) * t ^ (-((r : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add ht_pos, add_neg_cancel, Real.rpow_zero]
  calc (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹
      = 1 * ((covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹) := (one_mul _).symm
    _ = (t ^ ((r : ℝ) / 2) * t ^ (-((r : ℝ) / 2))) *
          ((covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹) := by rw [hcancel]
    _ = t ^ ((r : ℝ) / 2) * (t ^ (-((r : ℝ) / 2)) * (covol L)⁻¹ *
          latticeTheta (dualLattice L) t⁻¹) := by ring

/-- **Exact Minakshisundaram–Pleijel Heat-Kernel Asymptotic for `-Δ` on `ℝ^r / L`**:
`t^{r/2} · Tr(e^{t Δ}) → (4 π)^{-r/2} · covol(L)` as `t → 0⁺`! -/
theorem torusLaplacian_heatTrace_asymptotic {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    Tendsto (fun t : ℝ => t ^ ((r : ℝ) / 2) * (torusLaplacianSpectrum L).heatTrace t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L)) := by
  have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
  have hinv_top : Tendsto (fun t : ℝ => (4 * Real.pi * t)⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have hmul : Tendsto (fun t : ℝ => 4 * Real.pi * t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun t : ℝ => 4 * Real.pi * t) (nhds 0) (nhds (4 * Real.pi * 0)) :=
          (continuous_const_mul (4 * Real.pi)).continuousAt.tendsto
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos h4π ht
    exact tendsto_inv_nhdsGT_zero.comp hmul
  have htheta : Tendsto
      (fun t : ℝ => ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L) *
        latticeTheta L (4 * Real.pi * t)⁻¹)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L) * 1)) :=
    (Stage3ThetaSiegelBridge.latticeTheta_tendsto_one L |>.comp hinv_top).const_mul _
  rw [mul_one] at htheta
  refine htheta.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht_pos : 0 < t := ht
  have h4πt : 0 < 4 * Real.pi * t := mul_pos h4π ht_pos
  rw [torusLaplacian_heatTrace_eq_latticeTheta,
    latticeTheta_dual_functional_eq_orthogonal b hb h4πt,
    Real.mul_rpow h4π.le ht_pos.le]
  have hcancel : t ^ ((r : ℝ) / 2) * t ^ (-((r : ℝ) / 2)) = 1 := by
    rw [← Real.rpow_add ht_pos, add_neg_cancel, Real.rpow_zero]
  calc (4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L * latticeTheta L (4 * Real.pi * t)⁻¹
      = 1 * ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L * latticeTheta L (4 * Real.pi * t)⁻¹) :=
          (one_mul _).symm
    _ = (t ^ ((r : ℝ) / 2) * t ^ (-((r : ℝ) / 2))) *
          ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L * latticeTheta L (4 * Real.pi * t)⁻¹) := by
          rw [hcancel]
    _ = t ^ ((r : ℝ) / 2) * ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * t ^ (-((r : ℝ) / 2)) *
          covol L * latticeTheta L (4 * Real.pi * t)⁻¹) := by ring

/-- **Non-Asymptotic Flat-Torus Weyl-Law Upper Bound (ALL `Λ > 0`)** via
`Stage3ExplicitSpectral.DiscreteSpectrum.weyl_upper_bound`:
`N_L(Λ) ≤ e · covol(L)⁻¹ · Θ_{L*}(Λ) · Λ^{r/2}`. -/
theorem torusSpectrum_weyl_upper_bound {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {Λ : ℝ} (hΛ : 0 < Λ) :
    (torusSpectrum L).specCount Λ ≤
      Real.exp 1 * ((covol L)⁻¹ * latticeTheta (dualLattice L) Λ) * Λ ^ ((r : ℝ) / 2) := by
  have hinv_pos : 0 < 1 / Λ := one_div_pos.mpr hΛ
  refine (torusSpectrum L).weyl_upper_bound (C := (covol L)⁻¹ * latticeTheta (dualLattice L) Λ)
    (d := (r : ℝ)) hΛ (torusSpectrum_heatSummable L hinv_pos) ?_
  rw [torusSpectrum_heatTrace_eq_latticeTheta,
    latticeTheta_functional_eq_orthogonal b hb hinv_pos, one_div, inv_inv]
  ring_nf
  exact le_rfl

/-- **Sharp Asymptotic Flat-Torus Weyl-Law Upper Bound (ALL ranks `r`)**:
for every `ε > 0`, eventually as `Λ → ∞`:
`N_L(Λ) ≤ (e + ε) · covol(L)⁻¹ · Λ^{r/2}`. -/
theorem torusSpectrum_weyl_upper_bound_eventually_eps {L : Submodule ℤ E} [DiscreteTopology L]
    {r : ℕ} (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Λ : ℝ in atTop,
      (torusSpectrum L).specCount Λ ≤
        (Real.exp 1 + ε) * (covol L)⁻¹ * Λ ^ ((r : ℝ) / 2) := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  have hlim := Stage3ThetaSiegelBridge.latticeTheta_tendsto_one (dualLattice L)
  have htarget : 1 < 1 + ε / Real.exp 1 := by
    have : 0 < ε / Real.exp 1 := div_pos hε (Real.exp_pos 1)
    linarith
  have hev_th : ∀ᶠ Λ : ℝ in atTop, latticeTheta (dualLattice L) Λ < 1 + ε / Real.exp 1 :=
    hlim.eventually (Iio_mem_nhds htarget)
  filter_upwards [hev_th, Filter.eventually_gt_atTop (0 : ℝ)] with Λ hth hΛ
  have hcov_nn : 0 ≤ (covol L)⁻¹ := inv_nonneg.mpr (covol_pos L).le
  have hpow_nn : 0 ≤ Λ ^ ((r : ℝ) / 2) := Real.rpow_nonneg hΛ.le _
  have hcoef : Real.exp 1 * latticeTheta (dualLattice L) Λ ≤ Real.exp 1 + ε := by
    have h1 := mul_le_mul_of_nonneg_left hth.le (Real.exp_pos 1).le
    have h2 : Real.exp 1 * (1 + ε / Real.exp 1) = Real.exp 1 + ε := by
      field_simp [(Real.exp_pos 1).ne']
    linarith
  calc (torusSpectrum L).specCount Λ
      ≤ Real.exp 1 * ((covol L)⁻¹ * latticeTheta (dualLattice L) Λ) * Λ ^ ((r : ℝ) / 2) :=
          torusSpectrum_weyl_upper_bound b hb hΛ
    _ = (Real.exp 1 * latticeTheta (dualLattice L) Λ) * ((covol L)⁻¹ * Λ ^ ((r : ℝ) / 2)) := by
          ring
    _ ≤ (Real.exp 1 + ε) * ((covol L)⁻¹ * Λ ^ ((r : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hcov_nn hpow_nn)
    _ = (Real.exp 1 + ε) * (covol L)⁻¹ * Λ ^ ((r : ℝ) / 2) := by ring

/-- **Non-Asymptotic Standard-Laplacian Flat-Torus Weyl Bound (ALL `Λ > 0`)**:
on the flat torus `ℝ^r / L` with standard Laplacian `-Δ`,
`N_{-Δ}(Λ) ≤ e · (4 π)^{-r/2} · covol(L) · Θ_L(Λ / (4 π)) · Λ^{r/2}`. -/
theorem torusLaplacian_weyl_upper_bound {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) {Λ : ℝ} (hΛ : 0 < Λ) :
    (torusLaplacianSpectrum L).specCount Λ ≤
      Real.exp 1 * ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L *
        latticeTheta L (Λ / (4 * Real.pi))) * Λ ^ ((r : ℝ) / 2) := by
  have hinv_pos : 0 < 1 / Λ := one_div_pos.mpr hΛ
  have h4π : (0 : ℝ) < 4 * Real.pi := by positivity
  have h4πinv : 0 < 4 * Real.pi * (1 / Λ) := mul_pos h4π hinv_pos
  refine (torusLaplacianSpectrum L).weyl_upper_bound
    (C := (4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L * latticeTheta L (Λ / (4 * Real.pi)))
    (d := (r : ℝ)) hΛ (torusLaplacian_heatSummable b hb hinv_pos) ?_
  rw [torusLaplacian_heatTrace_eq_latticeTheta,
    latticeTheta_dual_functional_eq_orthogonal b hb h4πinv,
    Real.mul_rpow h4π.le hinv_pos.le]
  have harg : (4 * Real.pi * (1 / Λ))⁻¹ = Λ / (4 * Real.pi) := by
    field_simp [h4π.ne', hΛ.ne']
  rw [harg]
  ring_nf
  exact le_rfl

/-- **Sharp Flat-Torus Weyl Law `N_{-Δ}(Λ) ≤ e · covol(L) · Λ^{r/2}` (ALL ranks `r ≥ 1`)**:
for every discrete orthogonal lattice `L ⊂ E` of rank `r ≥ 1`, eventually as `Λ → ∞`,
`N_{-Δ}(ℝ^r / L, Λ) ≤ e · covol(L) · Λ^{r/2}` (and applied to `L*`, `N_{-Δ}(ℝ^r / L*, Λ) ≤ e · covol(L)⁻¹ · Λ^{r/2}`)! -/
theorem torusLaplacian_weyl_upper_bound_sharp {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (hr : 1 ≤ r) (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    ∀ᶠ Λ : ℝ in atTop,
      (torusLaplacianSpectrum L).specCount Λ ≤ Real.exp 1 * covol L * Λ ^ ((r : ℝ) / 2) := by
  have h4π : (1 : ℝ) < 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hr2 : (0 : ℝ) < (r : ℝ) / 2 := by positivity
  have hpow_gt : (1 : ℝ) < (4 * Real.pi) ^ ((r : ℝ) / 2) :=
    Real.one_lt_rpow h4π hr2
  have hdiv_top : Tendsto (fun Λ : ℝ => Λ / (4 * Real.pi)) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by positivity) tendsto_id
  have hlim := (Stage3ThetaSiegelBridge.latticeTheta_tendsto_one L).comp hdiv_top
  have hev_th : ∀ᶠ Λ : ℝ in atTop,
      latticeTheta L (Λ / (4 * Real.pi)) < (4 * Real.pi) ^ ((r : ℝ) / 2) :=
    hlim.eventually (Iio_mem_nhds hpow_gt)
  filter_upwards [hev_th, Filter.eventually_gt_atTop (0 : ℝ)] with Λ hth hΛ
  have hprod_le : (4 * Real.pi) ^ (-((r : ℝ) / 2)) * latticeTheta L (Λ / (4 * Real.pi)) ≤ 1 := by
    have h4π_pos : (0 : ℝ) < 4 * Real.pi := by positivity
    calc (4 * Real.pi) ^ (-((r : ℝ) / 2)) * latticeTheta L (Λ / (4 * Real.pi))
        ≤ (4 * Real.pi) ^ (-((r : ℝ) / 2)) * (4 * Real.pi) ^ ((r : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hth.le (Real.rpow_nonneg h4π_pos.le _)
      _ = 1 := by rw [← Real.rpow_add h4π_pos, neg_add_cancel, Real.rpow_zero]
  have hcov_nn : 0 ≤ covol L := (covol_pos L).le
  have hpow_nn : 0 ≤ Λ ^ ((r : ℝ) / 2) := Real.rpow_nonneg hΛ.le _
  calc (torusLaplacianSpectrum L).specCount Λ
      ≤ Real.exp 1 * ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * covol L *
          latticeTheta L (Λ / (4 * Real.pi))) * Λ ^ ((r : ℝ) / 2) :=
            torusLaplacian_weyl_upper_bound b hb hΛ
    _ = ((4 * Real.pi) ^ (-((r : ℝ) / 2)) * latticeTheta L (Λ / (4 * Real.pi))) *
          (Real.exp 1 * covol L * Λ ^ ((r : ℝ) / 2)) := by ring
    _ ≤ 1 * (Real.exp 1 * covol L * Λ ^ ((r : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hprod_le
            (mul_nonneg (mul_nonneg (Real.exp_pos 1).le hcov_nn) hpow_nn)
    _ = Real.exp 1 * covol L * Λ ^ ((r : ℝ) / 2) := one_mul _

/-- **Dual-Torus Sharp Weyl Law `N_{-Δ}(ℝ^r / L*, Λ) ≤ e · covol(L)⁻¹ · Λ^{r/2}` (ALL `r ≥ 1`)**:
obtained directly by applying `torusLaplacian_weyl_upper_bound_sharp` to `L*`! -/
theorem dualTorusLaplacian_weyl_upper_bound_sharp {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (hr : 1 ≤ r) (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    ∀ᶠ Λ : ℝ in atTop,
      (torusLaplacianSpectrum (dualLattice L)).specCount Λ ≤
        Real.exp 1 * (covol L)⁻¹ * Λ ^ ((r : ℝ) / 2) := by
  have : DiscreteTopology (dualLattice L) := discreteTopology_dualLattice_of_orthogonal b hb
  have h := torusLaplacian_weyl_upper_bound_sharp hr (dualBasis b hb) (dualBasis_isOrthogonal b hb)
  rwa [covol_dualLattice_of_orthogonalBasis b hb] at h

/-- **Short-Interval Gaussian Wave-Kernel Multiplicity Bound on Flat Tori**
(connecting `Stage3ExplicitSpectral.DiscreteSpectrum.windowCount_le_heatTrace` directly to the
exact orthogonal-lattice theta functional equation):
for all `Λ, t, σ` with `t > 0, σ > 0`:
`W_L(Λ, σ) ≤ exp(1/2 + t Λ + t² σ² / 2) · t^{-r/2} · covol(L)⁻¹ · Θ_{L*}(t⁻¹)`. -/
theorem torusSpectrum_windowCount_bound {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ}
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) (Λ : ℝ) {t σ : ℝ}
    (ht : 0 < t) (hσ : 0 < σ) :
    (torusSpectrum L).windowCount Λ σ ≤
      Real.exp (1 / 2 + t * Λ + t ^ 2 * σ ^ 2 / 2) *
        (t ^ (-((r : ℝ) / 2)) * (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹) := by
  have h := (torusSpectrum L).windowCount_le_heatTrace Λ t hσ (torusSpectrum_heatSummable L ht)
  rwa [torusSpectrum_heatTrace_eq_latticeTheta,
    latticeTheta_functional_eq_orthogonal b hb ht] at h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- **General Non-Negative Wave-Kernel Localization on Flat Tori**
(directly applying `Stage3ExplicitSpectral.DiscreteSpectrum.waveKernel_localization`):
for any non-negative wave kernel `K : ℝ → ℝ` with `c ≤ K(u)` (`0 < c`) on `|u| ≤ 1`,
`c · W_L(Λ, σ) ≤ ∑'_{v ∈ L} K((π ‖v‖² - Λ) / σ)`. -/
theorem torusSpectrum_waveKernel_localization (L : Submodule ℤ E)
    {K : ℝ → ℝ} {c Λ σ : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hKnn : ∀ u, 0 ≤ K u) (hKwin : ∀ u, |u| ≤ 1 → c ≤ K u)
    (hsum : Summable fun v : L => K ((Real.pi * ‖(v : E)‖ ^ 2 - Λ) / σ)) :
    c * (torusSpectrum L).windowCount Λ σ ≤
      ∑' v : L, K ((Real.pi * ‖(v : E)‖ ^ 2 - Λ) / σ) := by
  have h := (torusSpectrum L).waveKernel_localization hc hσ hKnn hKwin
    (by simpa [torusSpectrum] using hsum)
  simpa [torusSpectrum] using h

end OrthogonalLatticeTheta

end LatticePoissonAndWeyl

/-! ## Section 4: Unified Stage-4 Selberg–Arthur & Poisson–Weyl Master Discharge -/

/-- **Unified Stage-4 Selberg Trace, Jacquet–Langlands & Flat-Torus Poisson–Weyl Discharge**:
combines all three pillars in a single zero-`sorry`, zero-axiom headline certificate. -/
theorem stage4_selberg_trace_master_discharge
    {G : Type*} [Group G] [Fintype G]
    (Γ₁ Γ₂ : Subgroup G)
    [Fintype Γ₁] [Fintype (RightCosetSpace G Γ₁)]
    [Fintype Γ₂] [Fintype (RightCosetSpace G Γ₂)]
    {ι : Type*} [Fintype ι]
    (D₁ : SpectralDecomposition G Γ₁ ι)
    (D₂ : SpectralDecomposition G Γ₂ ι)
    (hchar_eq : ∀ i : ι, ∀ g : G, repChar (D₁.rep i) g = repChar (D₂.rep i) g)
    (horth : IsOrthogonalChars (fun i => repChar (D₁.rep i)))
    (hgeom : ∀ f : G → ℂ, geomSide Γ₁ f = geomSide Γ₂ f)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] {r : ℕ} (hr : 1 ≤ r)
    (b : Basis (Fin r) ℤ L) (hb : IsOrthogonalBasis b) :
    (∀ f : G → ℂ, D₁.specSide f = geomSide Γ₁ f) ∧
    (∀ i : ι, D₁.mult i = D₂.mult i) ∧
    (∀ t > 0, latticeTheta L t =
      t ^ (-((r : ℝ) / 2)) * (covol L)⁻¹ * latticeTheta (dualLattice L) t⁻¹) ∧
    (∀ᶠ Λ : ℝ in atTop,
      (torusLaplacianSpectrum (dualLattice L)).specCount Λ ≤
        Real.exp 1 * (covol L)⁻¹ * Λ ^ ((r : ℝ) / 2)) :=
  ⟨fun f => selberg_arthur_trace_formula Γ₁ D₁ f,
   (jacquet_langlands_same_group_transfer Γ₁ Γ₂ D₁ D₂ hchar_eq horth hgeom).2.2,
   fun _ ht => latticeTheta_functional_eq_orthogonal b hb ht,
   dualTorusLaplacian_weyl_upper_bound_sharp hr b hb⟩

end

end RHDirect.Stage4SelbergTrace
