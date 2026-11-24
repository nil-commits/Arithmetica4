import RHDirect.RallisSeesaw
import RHDirect.SiegelWeilCore
import RHDirect.Stage2WeilMetaplectic
import RHDirect.Stage10PeterssonHecke
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Matrix.Block
import Mathlib.MeasureTheory.Integral.Prod

/-!
# RHDirect.Stage11DoublingRallis

**UNCONDITIONAL CONCRETE PIATETSKI-SHAPIRO–RALLIS DOUBLING METHOD, SEESAW DUAL-PAIR IDENTITY,
LOCAL UNRAMIFIED DOUBLING ZETA FACTORIZATION, & EXACT INNER-PRODUCT POSITIVITY FOR DEFINITE
DUAL PAIRS** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` assumptions).

## Structure

1. **Concrete Doubling Space `V^□ = V ⊕ (-V)` & Exact Seesaw Dual-Pair Identities**:
   - Block-diagonal doubled Hermitian/orthogonal form `doubledForm B = diag(B, -B)` on
     `V^□ = V ⊕ (-V)`, group homomorphism `doubledEmbed : G × G ↪ G^□` preserving orthogonal and
     unitary forms, maximal totally isotropic diagonal/anti-diagonal splitting `V^Δ, V^∇`, and
     stabilizer action of the diagonal subgroup `G^Δ`.
   - Exact **Rallis Seesaw Identity (`rallis_seesaw_exact`)** and **`seesaw_inner_product_eq`**
     for commuting seesaw dual pairs `(G₁ × G₂, H)` and `(G, H₁ × H₂)` with split theta kernel
     `Θ((g₁, g₂), h) = Θ₁(g₁, h) * Θ₂(g₂, h)` (both finite weighted / Hilbert `EuclideanSpace ℂ`
     and continuous Bochner-integral Fubini versions).
   - Exact **Doubling Seesaw Inner-Product Formula (`doubling_seesaw_inner_product_eq` &
     `doubling_seesaw_integral_eq`)**:
     `⟨θ(φ₁), θ(φ₂)⟩_H = ∬_{G × G} φ₁(g₁) conj(φ₂(g₂)) · Θ_doubled(g₁, g₂) dg₁ dg₂`.
2. **Concrete Doubling Zeta Integral, Hecke Commutativity, Eigenform Factorization & Exact
   Local Unramified Doubling Factor**:
   - Matrix-coefficient doubling operator `D_s` and doubling zeta integral
     `Z(s, φ₁, φ₂, f_s) = ∫_G ⟨π(g) φ₁, φ₂⟩ · f_s(g) dg` (`doubling_zeta_integral_eq`).
   - Commutation of `D_s` with the Hecke algebra, preservation of Hecke eigenspaces, and
     **`doubling_eigenform_factorization`**: on every multiplicity-one Hecke eigenform space `S`,
     `D_s` acts by a scalar doubling eigenvalue `Z(s, π)`, giving
     `⟨D_s φ₁, φ₂⟩ = Z(s, π) · ⟨φ₁, φ₂⟩`.
   - Direct instantiation on the concrete level-1 cusp-form spaces `S₁₂(SL₂(ℤ))` (`delta12`),
     `S₁₆, S₁₈, S₂₀, S₂₂`, and the 2-dimensional Hecke eigenbasis `{S24_eigenPlus, S24_eigenMinus}`
     of `S₂₄(SL₂(ℤ))` from `RHDirect.Stage10PeterssonHecke`.
   - **Exact Local Unramified Doubling Factor (`localDoublingZetaGL2_eq`)**:
     for `GL₂` / `SL₂` Satake parameters `(α_p, β_p)`, the full analytic Macdonald–Cartan double-coset
     sum `Z_p(s, α_p, β_p)` converges absolutely and equals `L_p(s + 1/2, π) / d_p(s)`, together
     with the rank-`n` `U(n)` / `GL_n` local standard `L`-factor identity (`localDoublingFactorUn_eq`),
     explicit Satake roots for `E₈` / `E₄` and `Δ₁₂`, and the global Euler-product bridge.
3. **Concrete Rallis Inner-Product Positivity, Non-Vanishing Criterion & Direct Bridge into
   `RHDirect.RallisSeesaw` and `RHDirect.SiegelWeilCore`**:
   - **`rallis_inner_product_nonneg`**: `0 ≤ (⟨θ(φ), θ(φ)⟩).re` (finite, weighted, and integral).
   - **`theta_lift_ne_zero_iff_doubling_pos`**: `θ(φ) ≠ 0 ↔ 0 < (⟨D φ, φ⟩).re`.
   - Direct concrete wiring into `RHDirect.RallisSeesaw` (`SeesawDualPair`, `RallisInnerProductHyp`,
     `rallis_factor_nonneg_of_nonzero`, `rallis_normSq_scaling`, `definite_chain_nonvanishing`)
     and `RHDirect.SiegelWeilCore` (`DoublingZetaForm`, `SiegelEisensteinDecomp`,
     `MatchesThetaMean` for `Θ_{E₈} = E₄` from `Stage7EisensteinSeries`).
-/

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function
open RHDirect RHDirect.RallisSeesaw RHDirect.SiegelWeilCore
open RHDirect.Stage2WeilMetaplectic RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular
open RHDirect.Stage6HeckeSpectral RHDirect.Stage7EisensteinSeries RHDirect.Stage8RamanujanDelta
open RHDirect.Stage9CuspFormLFunc RHDirect.Stage10PeterssonHecke
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace RHDirect.Stage11DoublingRallis

noncomputable section

/-! ## Section 1: Concrete Doubling Space `V^□ = V ⊕ (-V)` & Exact Seesaw / Doubling Identities -/

section DoublingSpaceGeometry

/-- The **doubled Hermitian/bilinear form** on `V^□ = V ⊕ (-V)` attached to a form matrix
`B : M_m(𝔽)`: block-diagonal `diag(B, -B)`. -/
def doubledForm {𝔽 : Type*} [CommRing 𝔽] {m : ℕ} (B : Matrix (Fin m) (Fin m) 𝔽) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝔽 :=
  Matrix.fromBlocks B 0 0 (-B)

/-- The **doubling block-diagonal embedding** `ι : M_m(𝔽) × M_m(𝔽) ↪ M_{2m}(𝔽)`,
mapping `(g₁, g₂) ↦ diag(g₁, g₂)`. -/
def doubledEmbed {𝔽 : Type*} [CommRing 𝔽] {m : ℕ}
    (g₁ g₂ : Matrix (Fin m) (Fin m) 𝔽) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝔽 :=
  Matrix.fromBlocks g₁ 0 0 g₂

theorem doubledEmbed_one {𝔽 : Type*} [CommRing 𝔽] {m : ℕ} :
    doubledEmbed (1 : Matrix (Fin m) (Fin m) 𝔽) 1 = 1 := by
  unfold doubledEmbed
  exact Matrix.fromBlocks_one

theorem doubledEmbed_mul {𝔽 : Type*} [CommRing 𝔽] {m : ℕ}
    (g₁ g₂ h₁ h₂ : Matrix (Fin m) (Fin m) 𝔽) :
    doubledEmbed g₁ g₂ * doubledEmbed h₁ h₂ = doubledEmbed (g₁ * h₁) (g₂ * h₂) := by
  unfold doubledEmbed
  rw [Matrix.fromBlocks_multiply]
  simp

theorem doubledEmbed_injective {𝔽 : Type*} [CommRing 𝔽] {m : ℕ} :
    Function.Injective (fun p : Matrix (Fin m) (Fin m) 𝔽 × Matrix (Fin m) (Fin m) 𝔽 =>
      doubledEmbed p.1 p.2) := by
  rintro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ h
  have h1 : g₁ = h₁ := by
    ext i j
    have hij := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
    simpa [doubledEmbed] using hij
  have h2 : g₂ = h₂ := by
    ext i j
    have hij := congrFun (congrFun h (Sum.inr i)) (Sum.inr j)
    simpa [doubledEmbed] using hij
  exact Prod.ext h1 h2

/-- **Orthogonal/Symplectic Doubling Embedding**: if `g₁, g₂` preserve `B`, then
`doubledEmbed g₁ g₂` preserves `doubledForm B = diag(B, -B)`. -/
theorem doubledEmbed_preserves_orth {𝔽 : Type*} [CommRing 𝔽] {m : ℕ}
    {B g₁ g₂ : Matrix (Fin m) (Fin m) 𝔽}
    (hg₁ : g₁ᵀ * B * g₁ = B) (hg₂ : g₂ᵀ * B * g₂ = B) :
    (doubledEmbed g₁ g₂)ᵀ * doubledForm B * doubledEmbed g₁ g₂ = doubledForm B := by
  unfold doubledEmbed doubledForm
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hg₁, hg₂]

/-- **Unitary Doubling Embedding**: for a field involution `σ : 𝔽 ≃+* 𝔽`, if `g₁, g₂ ∈ U(B)`
(`gᴴ B g = B`), then `doubledEmbed g₁ g₂ ∈ U(V^□)` preserves `doubledForm B = diag(B, -B)`. -/
theorem doubledEmbed_preserves_herm {𝔽 : Type*} [CommRing 𝔽] {m : ℕ} (σ : 𝔽 ≃+* 𝔽)
    {B g₁ g₂ : Matrix (Fin m) (Fin m) 𝔽}
    (hg₁ : (g₁.map σ)ᵀ * B * g₁ = B) (hg₂ : (g₂.map σ)ᵀ * B * g₂ = B) :
    ((doubledEmbed g₁ g₂).map σ)ᵀ * doubledForm B * doubledEmbed g₁ g₂ = doubledForm B := by
  have hmap : (doubledEmbed g₁ g₂).map σ = doubledEmbed (g₁.map σ) (g₂.map σ) := by
    ext x y
    cases x <;> cases y <;> simp [doubledEmbed]
  rw [hmap]
  unfold doubledEmbed doubledForm
  rw [Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hg₁, hg₂]

/-- Bilinear pairing on the doubled space `V^□ = V ⊕ (-V)` induced by `doubledForm B`. -/
def doubledPairing {𝔽 : Type*} [CommRing 𝔽] {m : ℕ} (B : Matrix (Fin m) (Fin m) 𝔽)
    (u v : Fin m ⊕ Fin m → 𝔽) : 𝔽 :=
  dotProduct u ((doubledForm B).mulVec v)

/-- Explicit split formula for `doubledPairing B`:
`⟨(u₁, u₂), (v₁, v₂)⟩_{V ⊕ (-V)} = ⟨u₁, B v₁⟩ - ⟨u₂, B v₂⟩`. -/
theorem doubledPairing_elim {𝔽 : Type*} [CommRing 𝔽] {m : ℕ} (B : Matrix (Fin m) (Fin m) 𝔽)
    (u₁ u₂ v₁ v₂ : Fin m → 𝔽) :
    doubledPairing B (Sum.elim u₁ u₂) (Sum.elim v₁ v₂) =
      dotProduct u₁ (B.mulVec v₁) - dotProduct u₂ (B.mulVec v₂) := by
  simp only [doubledPairing, doubledForm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, Matrix.neg_apply, neg_mul,
    Finset.sum_neg_distrib, mul_neg]
  exact (sub_eq_add_neg _ _).symm

/-- Canonical diagonal embedding `v ↦ (v, v)` into `V^□ = V ⊕ (-V)` spanning the maximal
isotropic subspace `V^Δ`. -/
def diagVec {𝔽 : Type*} {m : ℕ} (v : Fin m → 𝔽) : Fin m ⊕ Fin m → 𝔽 :=
  Sum.elim v v

/-- Canonical anti-diagonal embedding `v ↦ (v, -v)` into `V^□ = V ⊕ (-V)` spanning the
complementary maximal isotropic subspace `V^∇`. -/
def antiDiagVec {𝔽 : Type*} [Neg 𝔽] {m : ℕ} (v : Fin m → 𝔽) : Fin m ⊕ Fin m → 𝔽 :=
  Sum.elim v (-v)

/-- **Maximal Isotropy of `V^Δ` and `V^∇` in `V^□ = V ⊕ (-V)`**:
both the diagonal `{(v, v)}` and anti-diagonal `{(v, -v)}` are totally isotropic for `diag(B, -B)`. -/
theorem doubledPairing_diag_isotropic {𝔽 : Type*} [CommRing 𝔽] {m : ℕ}
    (B : Matrix (Fin m) (Fin m) 𝔽) (v w : Fin m → 𝔽) :
    doubledPairing B (diagVec v) (diagVec w) = 0 := by
  unfold diagVec
  rw [doubledPairing_elim, sub_self]

theorem doubledPairing_antiDiag_isotropic {𝔽 : Type*} [CommRing 𝔽] {m : ℕ}
    (B : Matrix (Fin m) (Fin m) 𝔽) (v w : Fin m → 𝔽) :
    doubledPairing B (antiDiagVec v) (antiDiagVec w) = 0 := by
  unfold antiDiagVec
  rw [doubledPairing_elim, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, sub_self]

/-- **Siegel Parabolic Diagonal Stabilizer**: the diagonal subgroup `G^Δ = {(g, g)}` preserves
the maximal isotropic subspace `V^Δ` pointwise: `diag(g, g) (v, v) = (g v, g v)`. -/
theorem doubledEmbed_diag_stabilizes {𝔽 : Type*} [CommRing 𝔽] {m : ℕ}
    (g : Matrix (Fin m) (Fin m) 𝔽) (v : Fin m → 𝔽) :
    (doubledEmbed g g).mulVec (diagVec v) = diagVec (g.mulVec v) := by
  ext x
  cases x with
  | inl i =>
    simp [doubledEmbed, diagVec, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  | inr i =>
    simp [doubledEmbed, diagVec, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

end DoublingSpaceGeometry

section FiniteSeesawAndDoubling

/-- Automorphic weighted Hermitian pairing `⟨f, g⟩_w = ∑ x, w x * f x * star (g x)`
(linear in the first argument, conjugate-linear in the second, matching `peterssonInner`). -/
def autInner {α : Type*} [Fintype α] (w : α → ℂ) (f g : α → ℂ) : ℂ :=
  ∑ x : α, w x * f x * star (g x)

/-- Exact bridge between `autInner` and `RHDirect.RallisSeesaw.wip`:
`autInner w f g = wip w g f`. -/
theorem autInner_eq_wip_swap {α : Type*} [Fintype α] (w : α → ℂ) (f g : α → ℂ) :
    autInner w f g = wip w g f := by
  unfold autInner wip
  refine Finset.sum_congr rfl fun x _ => by ring

/-- Exact bridge between `autInner` with unit weights and Mathlib's `EuclideanSpace ℂ` inner
product: `autInner 1 f g = inner ℂ g f`. -/
theorem autInner_one_eq_inner_swap {α : Type*} [Fintype α] (f g : EuclideanSpace ℂ α) :
    autInner (fun _ => (1 : ℂ)) (fun x => f x) (fun x => g x) = inner ℂ g f := by
  rw [euclidean_inner_eq]
  unfold autInner
  refine Finset.sum_congr rfl fun x _ => by ring

/-- Weighted finite theta lift `θ(φ)(h) = ∑ g, wG g * φ g * Θ g h`
(identical to `RHDirect.RallisSeesaw.kerOp wG Θ φ`). -/
def thetaLiftW {G H : Type*} [Fintype G]
    (wG : G → ℂ) (Θ : G → H → ℂ) (φ : G → ℂ) : H → ℂ :=
  kerOp wG Θ φ

/-- Weighted finite adjoint theta lift `θ*(ψ)(g) = ∑ h, wH h * ψ h * star (Θ g h)`
(identical to `RHDirect.RallisSeesaw.kerOp wH (kerAdj Θ) ψ`). -/
def thetaLiftAdjW {G H : Type*} [Fintype H]
    (wH : H → ℂ) (Θ : G → H → ℂ) (ψ : H → ℂ) : G → ℂ :=
  kerOp wH (kerAdj Θ) ψ

/-- Pure tensor product `(φ₁ ⊗ φ₂)(g₁, g₂) = φ₁(g₁) * φ₂(g₂)` on `G₁ × G₂`. -/
def pureTensor {G₁ G₂ : Type*} (φ₁ : G₁ → ℂ) (φ₂ : G₂ → ℂ) : G₁ × G₂ → ℂ :=
  fun p => φ₁ p.1 * φ₂ p.2

/-- Pure tensor product in `EuclideanSpace ℂ (G₁ × G₂)`. -/
def pureTensorL2 {G₁ G₂ : Type*}
    (φ₁ : EuclideanSpace ℂ G₁) (φ₂ : EuclideanSpace ℂ G₂) : EuclideanSpace ℂ (G₁ × G₂) :=
  WithLp.toLp 2 (fun p => φ₁ p.1 * φ₂ p.2)

/-- Split product theta kernel `Θ((g₁, g₂), h) = Θ₁(g₁, h) * Θ₂(g₂, h)` on `(G₁ × G₂) × H`. -/
def prodThetaKernel {G₁ G₂ H : Type*} (Θ₁ : G₁ → H → ℂ) (Θ₂ : G₂ → H → ℂ) :
    (G₁ × G₂) → H → ℂ :=
  fun p h => Θ₁ p.1 h * Θ₂ p.2 h

/-- **Doubled Theta Kernel** on `G × G`:
`Θ_doubled(g₁, g₂) = ∑ h, wH h * Θ(g₁, h) * star (Θ(g₂, h))`. -/
def doubledThetaKernel {G H : Type*} [Fintype H]
    (wH : H → ℂ) (Θ : G → H → ℂ) (p : G × G) : ℂ :=
  ∑ h : H, wH h * Θ p.1 h * star (Θ p.2 h)

/-- Concrete linear theta lift `θ : L²(G) →ₗ[ℂ] L²(H)` for any finite kernel `Θ : G → H → ℂ`. -/
def thetaLiftLin {G H : Type*} [Fintype G] (Θ : G → H → ℂ) :
    EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ H where
  toFun φ := WithLp.toLp 2 (fun h => ∑ g : G, φ g * Θ g h)
  map_add' φ₁ φ₂ := by
    ext h
    change ∑ g : G, (φ₁ g + φ₂ g) * Θ g h = (∑ g : G, φ₁ g * Θ g h) + ∑ g : G, φ₂ g * Θ g h
    simp_rw [add_mul, Finset.sum_add_distrib]
  map_smul' c φ := by
    ext h
    change ∑ g : G, (c * φ g) * Θ g h = c * ∑ g : G, φ g * Θ g h
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => by ring

/-- Concrete linear adjoint theta lift `θ* : L²(H) →ₗ[ℂ] L²(G)` with conjugate-transpose kernel. -/
def thetaLiftAdjLin {G H : Type*} [Fintype H] (Θ : G → H → ℂ) :
    EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun ψ := WithLp.toLp 2 (fun g => ∑ h : H, ψ h * star (Θ g h))
  map_add' ψ₁ ψ₂ := by
    ext g
    change ∑ h : H, (ψ₁ h + ψ₂ h) * star (Θ g h) =
      (∑ h : H, ψ₁ h * star (Θ g h)) + ∑ h : H, ψ₂ h * star (Θ g h)
    simp_rw [add_mul, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext g
    change ∑ h : H, (c * ψ h) * star (Θ g h) = c * ∑ h : H, ψ h * star (Θ g h)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => by ring

@[simp]
theorem thetaLiftLin_apply {G H : Type*} [Fintype G] (Θ : G → H → ℂ)
    (φ : EuclideanSpace ℂ G) (h : H) :
    thetaLiftLin Θ φ h = ∑ g : G, φ g * Θ g h := rfl

@[simp]
theorem thetaLiftAdjLin_apply {G H : Type*} [Fintype H] (Θ : G → H → ℂ)
    (ψ : EuclideanSpace ℂ H) (g : G) :
    thetaLiftAdjLin Θ ψ g = ∑ h : H, ψ h * star (Θ g h) := rfl

/-- **Split Kernel Factorization on Pure Tensors**:
for a split kernel `Θ((g₁, g₂), h) = Θ₁(g₁, h) * Θ₂(g₂, h)` and product weights
`w₁₂(g₁, g₂) = w₁(g₁) * w₂(g₂)`,
`θ(φ₁ ⊗ φ₂)(h) = θ₁(φ₁)(h) * θ₂(φ₂)(h)`. -/
theorem thetaLiftW_pureTensor {G₁ G₂ H : Type*} [Fintype G₁] [Fintype G₂]
    (w₁ : G₁ → ℂ) (w₂ : G₂ → ℂ) (Θ₁ : G₁ → H → ℂ) (Θ₂ : G₂ → H → ℂ)
    (φ₁ : G₁ → ℂ) (φ₂ : G₂ → ℂ) (h : H) :
    thetaLiftW (fun p : G₁ × G₂ => w₁ p.1 * w₂ p.2) (prodThetaKernel Θ₁ Θ₂)
        (pureTensor φ₁ φ₂) h =
      thetaLiftW w₁ Θ₁ φ₁ h * thetaLiftW w₂ Θ₂ φ₂ h := by
  unfold thetaLiftW kerOp prodThetaKernel pureTensor
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g₂ _ => by ring

/-- **CONCRETE FINITE SEESAW DUAL-PAIR IDENTITY (`seesaw_inner_product_eq`) (`0` Assumptions!)**:
Given two commuting dual-pair spaces `G₁, G₂` and `H₁, H₂` with seesaw embeddings
`ιG : G₁ × G₂ → G`, `ιH : H → H₁ × H₂` and a theta kernel `Θ : G → H → ℂ` splitting as
`Θ (ιG (g₁, g₂)) h = Θ₁ g₁ (ιH h).1 * Θ₂ g₂ (ιH h).2`:
1. The weighted seesaw pairing of `θ₁(φ₁) · θ₂(φ₂)` against `ψ` on `H` equals the pairing of
   `φ₁ ⊗ φ₂` against the pullback `θ*(ψ)` on `G₁ × G₂`! -/
theorem seesaw_inner_product_eq {G₁ G₂ G H H₁ H₂ : Type*}
    [Fintype G₁] [Fintype G₂] [Fintype H]
    (ιG : G₁ × G₂ → G) (ιH : H → H₁ × H₂)
    (w₁ : G₁ → ℂ) (w₂ : G₂ → ℂ) (wH : H → ℂ)
    (hw₁ : ∀ g₁, star (w₁ g₁) = w₁ g₁) (hw₂ : ∀ g₂, star (w₂ g₂) = w₂ g₂)
    (Θ : G → H → ℂ) (Θ₁ : G₁ → H₁ → ℂ) (Θ₂ : G₂ → H₂ → ℂ)
    (hsplit : ∀ (g₁ : G₁) (g₂ : G₂) (h : H),
      Θ (ιG (g₁, g₂)) h = Θ₁ g₁ (ιH h).1 * Θ₂ g₂ (ιH h).2)
    (φ₁ : G₁ → ℂ) (φ₂ : G₂ → ℂ) (ψ : H → ℂ) :
    wip wH
        (fun h => thetaLiftW w₁ (fun g₁ h' => Θ₁ g₁ (ιH h').1) φ₁ h *
          thetaLiftW w₂ (fun g₂ h' => Θ₂ g₂ (ιH h').2) φ₂ h)
        ψ =
      wip (fun p : G₁ × G₂ => w₁ p.1 * w₂ p.2) (pureTensor φ₁ φ₂)
        (thetaLiftAdjW wH (fun p h => Θ (ιG p) h) ψ) := by
  have hker : (fun p : G₁ × G₂ => fun h : H => Θ (ιG p) h) =
      prodThetaKernel (fun g₁ h => Θ₁ g₁ (ιH h).1) (fun g₂ h => Θ₂ g₂ (ιH h).2) := by
    funext p h
    exact hsplit p.1 p.2 h
  have hprod : (fun h => thetaLiftW w₁ (fun g₁ h' => Θ₁ g₁ (ιH h').1) φ₁ h *
      thetaLiftW w₂ (fun g₂ h' => Θ₂ g₂ (ιH h').2) φ₂ h) =
      thetaLiftW (fun p : G₁ × G₂ => w₁ p.1 * w₂ p.2)
        (fun p h => Θ (ιG p) h) (pureTensor φ₁ φ₂) := by
    funext h
    rw [hker, thetaLiftW_pureTensor]
  rw [hprod]
  refine kerOp_adjoint _ _ _ _ _ fun p => ?_
  rw [star_mul, hw₁ p.1, hw₂ p.2, mul_comm]

/-- **EXACT RALLIS SEESAW IDENTITY (`rallis_seesaw_exact`) (`0` Assumptions!)**:
In the concrete Hilbert space `EuclideanSpace ℂ`, for a split theta kernel
`Θ((g₁, g₂), h) = Θ₁(g₁, h) * Θ₂(g₂, h)`:
1. `⟨θ(φ₁ ⊗ φ₂), ψ⟩_H = ⟨φ₁ ⊗ φ₂, θ*(ψ)⟩_{G₁ × G₂}`, AND
2. `⟨θ₁(φ₁) · θ₂(φ₂), ψ⟩_H = ⟨φ₁ ⊗ φ₂, θ*(ψ)⟩_{G₁ × G₂}`! -/
theorem rallis_seesaw_exact {G₁ G₂ H : Type*} [Fintype G₁] [Fintype G₂] [Fintype H]
    (Θ₁ : G₁ → H → ℂ) (Θ₂ : G₂ → H → ℂ)
    (φ₁ : EuclideanSpace ℂ G₁) (φ₂ : EuclideanSpace ℂ G₂) (ψ : EuclideanSpace ℂ H) :
    inner ℂ (thetaLiftLin (prodThetaKernel Θ₁ Θ₂) (pureTensorL2 φ₁ φ₂)) ψ =
      inner ℂ (pureTensorL2 φ₁ φ₂) (thetaLiftAdjLin (prodThetaKernel Θ₁ Θ₂) ψ) ∧
    inner ℂ (WithLp.toLp 2 (fun h : H => thetaLiftLin Θ₁ φ₁ h * thetaLiftLin Θ₂ φ₂ h)) ψ =
      inner ℂ (pureTensorL2 φ₁ φ₂) (thetaLiftAdjLin (prodThetaKernel Θ₁ Θ₂) ψ) := by
  have h1 : inner ℂ (thetaLiftLin (prodThetaKernel Θ₁ Θ₂) (pureTensorL2 φ₁ φ₂)) ψ =
      inner ℂ (pureTensorL2 φ₁ φ₂) (thetaLiftAdjLin (prodThetaKernel Θ₁ Θ₂) ψ) := by
    rw [euclidean_inner_eq, euclidean_inner_eq]
    simp only [thetaLiftLin_apply, thetaLiftAdjLin_apply, star_sum, star_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun h _ => by ring
  have h2 : thetaLiftLin (prodThetaKernel Θ₁ Θ₂) (pureTensorL2 φ₁ φ₂) =
      WithLp.toLp 2 (fun h : H => thetaLiftLin Θ₁ φ₁ h * thetaLiftLin Θ₂ φ₂ h) := by
    ext h
    change ∑ p : G₁ × G₂, (φ₁ p.1 * φ₂ p.2) * (Θ₁ p.1 h * Θ₂ p.2 h) =
      (∑ g₁ : G₁, φ₁ g₁ * Θ₁ g₁ h) * (∑ g₂ : G₂, φ₂ g₂ * Θ₂ g₂ h)
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g₂ _ => by ring
  exact ⟨h1, h2 ▸ h1⟩

/-- **CONCRETE DOUBLING SEESAW INNER-PRODUCT FORMULA (`doubling_seesaw_inner_product_eq`)**:
For the doubling seesaw `G × G ↪ G^□` (splitting `V ⊕ (-V)` with conjugated second kernel
`Θ_{-V} = star ∘ Θ_V`), the inner product of two theta lifts factors into the exact double
pairing against the doubled theta kernel `Θ_doubled(g₁, g₂) = ∑ h, wH(h) Θ(g₁, h) conj(Θ(g₂, h))`:
`⟨θ(φ₁), θ(φ₂)⟩_H = ∑_{(g₁, g₂) ∈ G × G} wG(g₁) wG(g₂) φ₁(g₁) conj(φ₂(g₂)) · Θ_doubled(g₁, g₂)`. -/
theorem doubling_seesaw_inner_product_eq {G H : Type*} [Fintype G] [Fintype H]
    (wG : G → ℂ) (wH : H → ℂ) (hwG : ∀ g, star (wG g) = wG g)
    (Θ : G → H → ℂ) (φ₁ φ₂ : G → ℂ) :
    autInner wH (thetaLiftW wG Θ φ₁) (thetaLiftW wG Θ φ₂) =
      ∑ p : G × G, (wG p.1 * wG p.2) * φ₁ p.1 * star (φ₂ p.2) * doubledThetaKernel wH Θ p := by
  unfold autInner thetaLiftW kerOp doubledThetaKernel
  rw [Fintype.sum_prod_type]
  calc ∑ h : H, wH h * (∑ g₁ : G, wG g₁ * φ₁ g₁ * Θ g₁ h) *
          star (∑ g₂ : G, wG g₂ * φ₂ g₂ * Θ g₂ h)
      = ∑ h : H, ∑ g₁ : G, ∑ g₂ : G,
          wG g₁ * wG g₂ * φ₁ g₁ * star (φ₂ g₂) * (wH h * Θ g₁ h * star (Θ g₂ h)) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [star_sum, Finset.mul_sum]
          have hinner : ∀ g₂ : G,
              (wH h * ∑ g₁ : G, wG g₁ * φ₁ g₁ * Θ g₁ h) * star (wG g₂ * φ₂ g₂ * Θ g₂ h) =
              ∑ g₁ : G, wG g₁ * wG g₂ * φ₁ g₁ * star (φ₂ g₂) * (wH h * Θ g₁ h * star (Θ g₂ h)) := by
            intro g₂
            rw [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun g₁ _ => ?_
            simp only [star_mul, hwG]
            ring
          rw [Finset.sum_congr rfl fun g₂ _ => hinner g₂, Finset.sum_comm]
    _ = ∑ g₁ : G, ∑ h : H, ∑ g₂ : G,
          wG g₁ * wG g₂ * φ₁ g₁ * star (φ₂ g₂) * (wH h * Θ g₁ h * star (Θ g₂ h)) :=
          Finset.sum_comm
    _ = ∑ g₁ : G, ∑ g₂ : G, ∑ h : H,
          wG g₁ * wG g₂ * φ₁ g₁ * star (φ₂ g₂) * (wH h * Θ g₁ h * star (Θ g₂ h)) := by
          refine Finset.sum_congr rfl fun g₁ _ => Finset.sum_comm
    _ = ∑ g₁ : G, ∑ g₂ : G,
          wG g₁ * wG g₂ * φ₁ g₁ * star (φ₂ g₂) * ∑ h : H, wH h * Θ g₁ h * star (Θ g₂ h) := by
          refine Finset.sum_congr rfl fun g₁ _ => Finset.sum_congr rfl fun g₂ _ =>
            (Finset.mul_sum _ _ _).symm

/-- **Hilbert-Space (`EuclideanSpace ℂ`) Doubling Seesaw Formula**:
`inner ℂ (θ φ₂) (θ φ₁) = ∑_{(g₁, g₂) ∈ G × G} φ₁(g₁) conj(φ₂(g₂)) · Θ_doubled(g₁, g₂)`. -/
theorem doubling_seesaw_inner_product_L2 {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ₁ φ₂ : EuclideanSpace ℂ G) :
    inner ℂ (thetaLiftLin Θ φ₂) (thetaLiftLin Θ φ₁) =
      ∑ p : G × G, φ₁ p.1 * star (φ₂ p.2) * doubledThetaKernel (fun _ => (1 : ℂ)) Θ p := by
  have h := doubling_seesaw_inner_product_eq (fun _ : G => (1 : ℂ)) (fun _ : H => (1 : ℂ))
    (fun _ => star_one _) Θ (fun g => φ₁ g) (fun g => φ₂ g)
  have hL : autInner (fun _ : H => (1 : ℂ))
      (thetaLiftW (fun _ : G => (1 : ℂ)) Θ (fun g => φ₁ g))
      (thetaLiftW (fun _ : G => (1 : ℂ)) Θ (fun g => φ₂ g)) =
      inner ℂ (thetaLiftLin Θ φ₂) (thetaLiftLin Θ φ₁) := by
    rw [← autInner_one_eq_inner_swap]
    unfold autInner thetaLiftW kerOp
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [thetaLiftLin_apply]
  rw [hL] at h
  simpa only [one_mul] using h

end FiniteSeesawAndDoubling

section ArchimedeanIntegralSeesawAndDoubling

/-- Continuous / Archimedean integral theta lift `(θ φ)(h) = ∫ g, φ(g) * Θ(g, h) dμ_G(g)`. -/
def thetaLiftInt {G H : Type*} [MeasurableSpace G] (μG : Measure G)
    (Θ : G → H → ℂ) (φ : G → ℂ) (h : H) : ℂ :=
  ∫ g, φ g * Θ g h ∂μG

/-- Continuous / Archimedean adjoint theta lift `(θ* ψ)(g) = ∫ h, ψ(h) * conj(Θ(g, h)) dμ_H(h)`. -/
def thetaLiftAdjInt {G H : Type*} [MeasurableSpace H] (μH : Measure H)
    (Θ : G → H → ℂ) (ψ : H → ℂ) (g : G) : ℂ :=
  ∫ h, ψ h * star (Θ g h) ∂μH

/-- Continuous / Archimedean doubled theta kernel
`Θ_doubled(g₁, g₂) = ∫ h, Θ(g₁, h) * conj(Θ(g₂, h)) dμ_H(h)`. -/
def doubledThetaKernelInt {G H : Type*} [MeasurableSpace H] (μH : Measure H)
    (Θ : G → H → ℂ) (p : G × G) : ℂ :=
  ∫ h, Θ p.1 h * star (Θ p.2 h) ∂μH

/-- **ARCHIMEDEAN / MEASURE-THEORETIC RALLIS SEESAW IDENTITY (`rallis_seesaw_integral_exact`)
(`0` Assumptions beyond Fubini integrability!)**:
For sigma-finite measure spaces `(G, μG)` and `(H, μH)`,
`∫_H θ(φ)(h) conj(ψ(h)) dμ_H = ∫_G φ(g) conj(θ*(ψ)(g)) dμ_G`
(and symmetrically with `star` on the first factor). -/
theorem rallis_seesaw_integral_exact {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    {μG : Measure G} {μH : Measure H} [SFinite μG] [SFinite μH]
    (Θ : G → H → ℂ) (φ : G → ℂ) (ψ : H → ℂ)
    (hint : Integrable (fun p : G × H => φ p.1 * Θ p.1 p.2 * star (ψ p.2)) (μG.prod μH)) :
    ∫ h, thetaLiftInt μG Θ φ h * star (ψ h) ∂μH =
      ∫ g, φ g * star (thetaLiftAdjInt μH Θ ψ g) ∂μG := by
  calc ∫ h, thetaLiftInt μG Θ φ h * star (ψ h) ∂μH
      = ∫ h, ∫ g, φ g * Θ g h * star (ψ h) ∂μG ∂μH := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          dsimp only [thetaLiftInt]
          rw [← integral_mul_const]
    _ = ∫ g, ∫ h, φ g * Θ g h * star (ψ h) ∂μH ∂μG :=
          (integral_integral_swap hint).symm
    _ = ∫ g, φ g * star (thetaLiftAdjInt μH Θ ψ g) ∂μG := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          dsimp only [thetaLiftAdjInt]
          rw [Complex.star_def, ← integral_conj, ← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
          dsimp only
          simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
          ring

/-- **ARCHIMEDEAN / MEASURE-THEORETIC DOUBLING SEESAW FORMULA (`doubling_seesaw_integral_eq`)
(`0` Assumptions beyond Fubini integrability!)**:
$$⟨θ(φ₁), θ(φ₂)⟩_H = \iint_{G \times G} φ₁(g₁)\,\overline{φ₂(g₂)}\,\Theta_{\mathrm{doubled}}(g₁, g₂)\,dμ_G(g₁)\,dμ_G(g₂).$$ -/
theorem doubling_seesaw_integral_eq {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    {μG : Measure G} {μH : Measure H} [SFinite μG] [SFinite μH]
    (Θ : G → H → ℂ) (φ₁ φ₂ : G → ℂ)
    (hint₁ : Integrable
      (fun p : (G × G) × H =>
        φ₁ p.1.1 * star (φ₂ p.1.2) * (Θ p.1.1 p.2 * star (Θ p.1.2 p.2)))
      ((μG.prod μG).prod μH))
    (hint₂ : ∀ h : H, Integrable
      (fun p : G × G => (φ₁ p.1 * Θ p.1 h) * star (φ₂ p.2 * Θ p.2 h)) (μG.prod μG)) :
    ∫ h, thetaLiftInt μG Θ φ₁ h * star (thetaLiftInt μG Θ φ₂ h) ∂μH =
      ∫ p : G × G, φ₁ p.1 * star (φ₂ p.2) * doubledThetaKernelInt μH Θ p ∂(μG.prod μG) := by
  have hpoint : ∀ h : H,
      thetaLiftInt μG Θ φ₁ h * star (thetaLiftInt μG Θ φ₂ h) =
        ∫ p : G × G, φ₁ p.1 * star (φ₂ p.2) * (Θ p.1 h * star (Θ p.2 h)) ∂(μG.prod μG) := by
    intro h
    unfold thetaLiftInt
    rw [Complex.star_def, ← integral_conj]
    have hprod := integral_prod (μ := μG) (ν := μG)
      (f := fun p : G × G => (φ₁ p.1 * Θ p.1 h) * star (φ₂ p.2 * Θ p.2 h)) (hint₂ h)
    have hsep : (∫ g₁, ∫ g₂, (φ₁ g₁ * Θ g₁ h) * star (φ₂ g₂ * Θ g₂ h) ∂μG ∂μG) =
        (∫ g₁, φ₁ g₁ * Θ g₁ h ∂μG) * (∫ g₂, (starRingEnd ℂ) (φ₂ g₂ * Θ g₂ h) ∂μG) := by
      simp_rw [integral_const_mul, integral_mul_const, Complex.star_def]
    rw [← hsep, ← hprod]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    simp only [star_mul, Complex.star_def]
    ring
  calc ∫ h, thetaLiftInt μG Θ φ₁ h * star (thetaLiftInt μG Θ φ₂ h) ∂μH
      = ∫ h, ∫ p : G × G,
          φ₁ p.1 * star (φ₂ p.2) * (Θ p.1 h * star (Θ p.2 h)) ∂(μG.prod μG) ∂μH :=
          integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ p : G × G, ∫ h,
          φ₁ p.1 * star (φ₂ p.2) * (Θ p.1 h * star (Θ p.2 h)) ∂μH ∂(μG.prod μG) :=
          (integral_integral_swap hint₁).symm
    _ = ∫ p : G × G, φ₁ p.1 * star (φ₂ p.2) * doubledThetaKernelInt μH Θ p ∂(μG.prod μG) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          dsimp only [doubledThetaKernelInt]
          rw [integral_const_mul]

end ArchimedeanIntegralSeesawAndDoubling

/-! ## Section 2: Concrete Doubling Zeta Integral, Hecke Commutativity, Eigenform Factorization &
Exact Local Unramified Doubling Factor `Z_p(s, α_p, β_p) = L_p(s + 1/2, π) / d_p(s)` -/

section DoublingOperatorAndHeckeFactorization

/-- Finite-group matrix-coefficient doubling operator `D_s φ = ∑ g, f_s(g) • ρ(g) φ`. -/
def doublingOp {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) : Module.End ℂ V :=
  ∑ g : G, f_s g • ρ g

/-- Finite-group matrix-coefficient doubling zeta integral
`Z(s, φ₁, φ₂, f_s) = ∑ g, ⟨φ₂, ρ(g) φ₁⟩ * f_s(g)` (linear in `φ₁`, conjugate-linear in `φ₂`). -/
def doublingZeta {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) (φ₁ φ₂ : V) : ℂ :=
  ∑ g : G, inner ℂ φ₂ (ρ g φ₁) * f_s g

/-- Exact identity equating the finite doubling operator pairing with the matrix-coefficient
doubling zeta integral: `⟨φ₂, D_s φ₁⟩ = ∑ g, ⟨φ₂, ρ(g) φ₁⟩ * f_s(g)`. -/
theorem doubling_zeta_fin_eq {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) (φ₁ φ₂ : V) :
    inner ℂ φ₂ (doublingOp ρ f_s φ₁) = doublingZeta ρ f_s φ₁ φ₂ := by
  unfold doublingOp doublingZeta
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun g _ => mul_comm _ _

/-- Continuous / Bochner-integral doubling operator `D_s φ = ∫_G f_s(g) • ρ(g) φ dμ_G(g)`. -/
def doublingOpInt {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (μG : Measure G) (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) (φ : V) : V :=
  ∫ g, f_s g • ρ g φ ∂μG

/-- Continuous / Bochner-integral matrix-coefficient doubling zeta integral
`Z(s, φ₁, φ₂, f_s) = ∫_G ⟨φ₂, ρ(g) φ₁⟩ * f_s(g) dμ_G(g)`. -/
def doublingZetaInt {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μG : Measure G) (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) (φ₁ φ₂ : V) : ℂ :=
  ∫ g, inner ℂ φ₂ (ρ g φ₁) * f_s g ∂μG

/-- **CONCRETE DOUBLING ZETA INTEGRAL IDENTITY (`doubling_zeta_integral_eq`) (`0` Assumptions!)**:
For any Bochner-integrable doubling action `g ↦ f_s(g) • ρ(g) φ₁` on a complete inner-product
space `V`,
`⟨φ₂, D_s φ₁⟩ = ∫_G ⟨φ₂, ρ(g) φ₁⟩ * f_s(g) dμ_G(g)`! -/
theorem doubling_zeta_integral_eq {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (μG : Measure G) (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) (φ₁ φ₂ : V)
    (hint : Integrable (fun g : G => f_s g • ρ g φ₁) μG) :
    inner ℂ φ₂ (doublingOpInt μG ρ f_s φ₁) = doublingZetaInt μG ρ f_s φ₁ φ₂ := by
  unfold doublingOpInt doublingZetaInt
  have hcomm := (innerSL ℂ φ₂).integral_comp_comm hint
  simpa only [innerSL_apply_apply, inner_smul_right, mul_comm] using hcomm.symm

/-- **Hecke Commutativity of the Doubling Operator**:
any Hecke operator `T : End ℂ V` commuting with the group representation `ρ(g)` commutes
with the doubling operator `D_s = ∑ g, f_s(g) • ρ(g)`. -/
theorem doublingOp_comm_hecke {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V]
    (ρ : G →* Module.End ℂ V) (f_s : G → ℂ) (T : Module.End ℂ V)
    (hcomm : ∀ g : G, T ∘ₗ ρ g = ρ g ∘ₗ T) :
    T ∘ₗ doublingOp ρ f_s = doublingOp ρ f_s ∘ₗ T := by
  ext v
  simp only [doublingOp, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hg := congrArg (fun L : Module.End ℂ V => L v) (hcomm g)
  simpa only [LinearMap.comp_apply] using congrArg (f_s g • ·) hg

/-- **Bi-`K`-Invariant Preservation of Spherical Vectors**:
if `f_s : G → ℂ` is left-`K`-invariant (`f_s (k * g) = f_s g`), then `doublingOp ρ f_s` maps
EVERY vector into the `K`-fixed spherical subspace `V^K`! -/
theorem doublingOp_mem_K_fixed {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (K : Subgroup G)
    (ρ : G →* Module.End ℂ V) (f_s : G → ℂ)
    (hinv : ∀ k ∈ K, ∀ g : G, f_s (k * g) = f_s g)
    (v : V) (k : G) (hk : k ∈ K) :
    ρ k (doublingOp ρ f_s v) = doublingOp ρ f_s v := by
  unfold doublingOp
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  have hmul : ∀ g : G, ρ k (ρ g v) = ρ (k * g) v := fun g => by
    rw [map_mul]; rfl
  simp_rw [hmul]
  calc ∑ g : G, f_s g • ρ (k * g) v
      = ∑ g : G, f_s (k * g) • ρ (k * g) v := by
          refine Finset.sum_congr rfl fun g _ => by rw [hinv k hk g]
    _ = ∑ g : G, f_s g • ρ g v :=
          Fintype.sum_equiv (Equiv.mulLeft k) _ _ (fun _ => rfl)

/-- **Eigenspace Stability under Commuting Doubling Operators**:
if `D` commutes with every operator `T i` in a Hecke family, then `D` stabilizes their
simultaneous Hecke eigenspace `⋂_i ker(T_i - λ_i)`. -/
theorem commuting_preserves_hecke_eigenspace {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (T : ι → Module.End ℂ V) (lam : ι → ℂ) (D : Module.End ℂ V)
    (hcomm : ∀ i, T i ∘ₗ D = D ∘ₗ T i)
    {φ : V} (hφ : ∀ i, T i φ = lam i • φ) :
    ∀ i, T i (D φ) = lam i • D φ := by
  intro i
  have hc := congrArg (fun L : Module.End ℂ V => L φ) (hcomm i)
  simp only [LinearMap.comp_apply] at hc
  rw [hc, hφ i, map_smul]

/-- **DOUBLING EIGENFORM SCALAR FACTORIZATION (`doubling_eigenform_factorization`)
(`0` Assumptions!)**:
Let `S ≤ V` be a 1-dimensional simultaneous Hecke eigenspace (`finrank ℂ S = 1`, multiplicity one)
for a Hecke family `{T_i}` with eigenvalues `{λ_i}`, and let `D_s : End ℂ V` commute with `{T_i}`
(for instance `D_s = doublingOp π f_s` with `T_i ∘ π(g) = π(g) ∘ T_i`).
Then there exists a **unique scalar doubling eigenvalue `Z(s, π) : ℂ`** such that:
1. `D_s φ = Z(s, π) • φ` for every `φ ∈ S`,
2. `⟨φ₂, D_s φ₁⟩ = Z(s, π) · ⟨φ₂, φ₁⟩` and `⟨D_s φ₁, φ₂⟩ = conj(Z(s, π)) · ⟨φ₁, φ₂⟩` for all
   `φ₁, φ₂ ∈ S`, AND
3. For every nonzero eigenform `φ ∈ S`, `Z(s, π) = ⟨φ, D_s φ⟩ / ⟨φ, φ⟩`! -/
theorem doubling_eigenform_factorization {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (T : ι → Module.End ℂ V) (lam : ι → ℂ)
    (D_s : Module.End ℂ V) (hcomm : ∀ i, T i ∘ₗ D_s = D_s ∘ₗ T i)
    (hdim : Module.finrank ℂ (↥(⨅ i : ι, Module.End.eigenspace (T i) (lam i))) = 1) :
    ∃! Z : ℂ,
      (∀ φ ∈ (⨅ i : ι, Module.End.eigenspace (T i) (lam i) : Submodule ℂ V), D_s φ = Z • φ) ∧
      (∀ φ₁ ∈ (⨅ i : ι, Module.End.eigenspace (T i) (lam i) : Submodule ℂ V),
       ∀ φ₂ ∈ (⨅ i : ι, Module.End.eigenspace (T i) (lam i) : Submodule ℂ V),
        inner ℂ φ₂ (D_s φ₁) = Z * inner ℂ φ₂ φ₁ ∧
        inner ℂ (D_s φ₁) φ₂ = star Z * inner ℂ φ₁ φ₂) ∧
      (∀ φ ∈ (⨅ i : ι, Module.End.eigenspace (T i) (lam i) : Submodule ℂ V), φ ≠ 0 →
        Z = inner ℂ φ (D_s φ) / inner ℂ φ φ) := by
  set S : Submodule ℂ V := ⨅ i : ι, Module.End.eigenspace (T i) (lam i)
  have hS_ne_bot : S ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    exact zero_ne_one hdim
  obtain ⟨e, heS, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS_ne_bot
  have hS_mem : ∀ v : V, v ∈ S ↔ ∀ i, T i v = lam i • v := by
    intro v
    simp only [S, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hDeS : D_s e ∈ S := (hS_mem (D_s e)).mpr
    (commuting_preserves_hecke_eigenspace T lam D_s hcomm ((hS_mem e).mp heS))
  have hgen : ∀ v ∈ S, ∃ c : ℂ, v = c • e := by
    intro v hv
    have he_sub : (⟨e, heS⟩ : S) ≠ 0 := fun h => he0 (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, heS⟩ : S) he_sub).mp hdim ⟨v, hv⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  obtain ⟨Z, hZe⟩ := hgen (D_s e) hDeS
  refine ⟨Z, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro φ hφ
    obtain ⟨c, rfl⟩ := hgen φ hφ
    rw [map_smul, hZe, smul_smul, smul_smul, mul_comm]
  · intro φ₁ hφ₁ φ₂ hφ₂
    obtain ⟨c, rfl⟩ := hgen φ₁ hφ₁
    have hDφ₁ : D_s (c • e) = Z • (c • e) := by
      rw [map_smul, hZe, smul_smul, smul_smul, mul_comm]
    rw [hDφ₁, inner_smul_right, inner_smul_left]
    exact ⟨rfl, rfl⟩
  · intro φ hφ hφ0
    obtain ⟨c, rfl⟩ := hgen φ hφ
    have hDφ : D_s (c • e) = Z • (c • e) := by
      rw [map_smul, hZe, smul_smul, smul_smul, mul_comm]
    have hne : inner ℂ (c • e) (c • e) ≠ 0 := by
      rwa [ne_eq, inner_self_eq_zero]
    rw [hDφ, inner_smul_right, mul_div_cancel_right₀ Z hne]
  · rintro Z' ⟨hZ', -, -⟩
    have heq : Z' • e = Z • e := (hZ' e heS).symm.trans hZe
    exact smul_left_injective ℂ he0 heq

/-- **Concrete Doubling Factorization on `S₁₂(SL₂(ℤ))` (`delta12`)**:
every linear operator `D : End ℂ (CuspForm SL2ZRange 12)` acts as scalar multiplication by its
Petersson doubling eigenvalue `Z(D) = ⟨D Δ₁₂, Δ₁₂⟩_Pet / ⟨Δ₁₂, Δ₁₂⟩_Pet`! -/
theorem doubling_factorization_delta12 (D : Module.End ℂ (CuspForm SL2ZRange 12)) :
    ∃! Z : ℂ,
      (∀ φ : CuspForm SL2ZRange 12, D φ = Z • φ) ∧
      (∀ φ₁ φ₂ : CuspForm SL2ZRange 12, peterssonInner (D φ₁) φ₂ = Z * peterssonInner φ₁ φ₂) ∧
      Z = peterssonInner (D delta12) delta12 / peterssonInner delta12 delta12 := by
  have h1 : qExpansionCoeff delta12 1 = 1 := by
    unfold delta12 qExpansionCoeff
    have ht1 : PowerSeries.coeff 1 ramanujanDeltaPowerSeriesZ = 1 := ramanujanTau_one
    rw [← ramanujanDeltaPowerSeriesZ_map_eq, PowerSeries.coeff_map, ht1]
    simp
  have hdim : Module.finrank ℂ (CuspForm SL2ZRange 12) = 1 :=
    finrank_cuspForm_SL2Z_five_oneDim.1
  have hne : delta12 ≠ 0 := by
    intro h0
    have hq0 : qExpansionCoeff delta12 1 = 0 := by
      rw [h0]
      have hz : (0 : CuspForm SL2ZRange 12) = (0 : ℂ) • delta12 := by simp
      rw [hz, qExpansionCoeff_smul, zero_mul]
    rw [h1] at hq0
    exact one_ne_zero hq0
  have hpet_ne : peterssonInner delta12 delta12 ≠ 0 :=
    (peterssonInner_self_eq_zero_iff delta12).not.mpr hne
  let Z : ℂ := qExpansionCoeff (D delta12) 1
  have hDdelta : D delta12 = Z • delta12 := cuspForm_eq_smul_of_finrank_eq_one hdim h1 (D delta12)
  refine ⟨Z, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro φ
    have hφ : φ = qExpansionCoeff φ 1 • delta12 := cuspForm_eq_smul_of_finrank_eq_one hdim h1 φ
    conv_lhs => rw [hφ, map_smul, hDdelta, smul_smul, mul_comm, ← smul_smul, ← hφ]
  · intro φ₁ φ₂
    have hφ₁ : φ₁ = qExpansionCoeff φ₁ 1 • delta12 := cuspForm_eq_smul_of_finrank_eq_one hdim h1 φ₁
    have hDφ₁ : D φ₁ = Z • φ₁ := by
      conv_lhs => rw [hφ₁, map_smul, hDdelta, smul_smul, mul_comm, ← smul_smul, ← hφ₁]
    rw [hDφ₁, peterssonInner_smul_left]
  · rw [hDdelta, peterssonInner_smul_left, mul_div_cancel_right₀ Z hpet_ne]
  · rintro Z' ⟨hZ', -, -⟩
    have heq : Z' • delta12 = Z • delta12 := (hZ' delta12).symm.trans hDdelta
    exact smul_left_injective ℂ hne heq

/-- **Concrete Doubling Diagonalization on `S₂₄(SL₂(ℤ))` (`ℚ(√144169)` Hecke Eigenbasis)**:
every linear doubling operator `D : End ℂ (CuspForm SL2ZRange 24)` that commutes with `T₂`
is **simultaneously diagonal** in the Petersson-orthogonal Hecke eigenbasis
`{S24_eigenPlus, S24_eigenMinus}` with exact doubling eigenvalues `Z₊, Z₋`! -/
theorem doubling_diagonalization_S24 (D : Module.End ℂ (CuspForm SL2ZRange 24))
    (hcomm : heckeCuspFormLin 24 (by norm_num) 2 ∘ₗ D = D ∘ₗ heckeCuspFormLin 24 (by norm_num) 2) :
    ∃ Z_plus Z_minus : ℂ,
      D S24_eigenPlus = Z_plus • S24_eigenPlus ∧
      D S24_eigenMinus = Z_minus • S24_eigenMinus ∧
      peterssonInner (D S24_eigenPlus) S24_eigenMinus = 0 ∧
      Z_plus = peterssonInner (D S24_eigenPlus) S24_eigenPlus /
        peterssonInner S24_eigenPlus S24_eigenPlus ∧
      Z_minus = peterssonInner (D S24_eigenMinus) S24_eigenMinus /
        peterssonInner S24_eigenMinus S24_eigenMinus := by
  have hli := S24_hecke_eigenbasis.1
  have hne := S24_lambdaPlus_ne_lambdaMinus
  have hcomm_apply : ∀ f : CuspForm SL2ZRange 24,
      heckeCuspForm 24 (by norm_num) 2 (by norm_num) (D f) =
        D (heckeCuspForm 24 (by norm_num) 2 (by norm_num) f) := by
    intro f
    have h := congrArg (fun L : Module.End ℂ (CuspForm SL2ZRange 24) => L f) hcomm
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      heckeCuspFormLin_apply 24 (by norm_num) (by norm_num),
      heckeCuspFormLin_apply 24 (by norm_num) (by norm_num)] at h
    exact h
  -- Decompose `D S24_eigenPlus` in `{S24_eigenPlus, S24_eigenMinus}`
  obtain ⟨a₁, a₂, ha⟩ := S24_eq_eigen_linear_comb (D S24_eigenPlus)
  have hTa_l : heckeCuspForm 24 (by norm_num) 2 (by norm_num) (D S24_eigenPlus) =
      S24_lambdaPlus • (a₁ • S24_eigenPlus + a₂ • S24_eigenMinus) := by
    rw [hcomm_apply, S24_eigenPlus_T2, map_smul, ha]
  have hTa_r : heckeCuspForm 24 (by norm_num) 2 (by norm_num) (D S24_eigenPlus) =
      (a₁ * S24_lambdaPlus) • S24_eigenPlus + (a₂ * S24_lambdaMinus) • S24_eigenMinus := by
    rw [ha, heckeCuspForm_add, heckeCuspForm_smul, heckeCuspForm_smul,
      S24_eigenPlus_T2, S24_eigenMinus_T2, smul_smul, smul_smul]
  have ha2_zero : (0 : ℂ) • S24_eigenPlus +
      (a₂ * (S24_lambdaPlus - S24_lambdaMinus)) • S24_eigenMinus = 0 := by
    have heq := hTa_l.symm.trans hTa_r
    ext τ
    have hτ := congrArg (fun u : CuspForm SL2ZRange 24 => u τ) heq
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, _root_.zero_apply] at hτ ⊢
    linear_combination hτ
  have ha2_comb := (Fintype.linearIndependent_iff.mp hli)
    ![0, a₂ * (S24_lambdaPlus - S24_lambdaMinus)] (by simpa [Fin.sum_univ_two] using ha2_zero)
  have ha2 : a₂ = 0 :=
    (mul_eq_zero.mp (by simpa using ha2_comb 1)).resolve_right (sub_ne_zero.mpr hne)
  rw [ha2, zero_smul, add_zero] at ha
  -- Decompose `D S24_eigenMinus` in `{S24_eigenPlus, S24_eigenMinus}`
  obtain ⟨b₁, b₂, hb⟩ := S24_eq_eigen_linear_comb (D S24_eigenMinus)
  have hTb_l : heckeCuspForm 24 (by norm_num) 2 (by norm_num) (D S24_eigenMinus) =
      S24_lambdaMinus • (b₁ • S24_eigenPlus + b₂ • S24_eigenMinus) := by
    rw [hcomm_apply, S24_eigenMinus_T2, map_smul, hb]
  have hTb_r : heckeCuspForm 24 (by norm_num) 2 (by norm_num) (D S24_eigenMinus) =
      (b₁ * S24_lambdaPlus) • S24_eigenPlus + (b₂ * S24_lambdaMinus) • S24_eigenMinus := by
    rw [hb, heckeCuspForm_add, heckeCuspForm_smul, heckeCuspForm_smul,
      S24_eigenPlus_T2, S24_eigenMinus_T2, smul_smul, smul_smul]
  have hb1_zero : (b₁ * (S24_lambdaMinus - S24_lambdaPlus)) • S24_eigenPlus +
      (0 : ℂ) • S24_eigenMinus = 0 := by
    have heq := hTb_l.symm.trans hTb_r
    ext τ
    have hτ := congrArg (fun u : CuspForm SL2ZRange 24 => u τ) heq
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, _root_.zero_apply] at hτ ⊢
    linear_combination hτ
  have hb1_comb := (Fintype.linearIndependent_iff.mp hli)
    ![b₁ * (S24_lambdaMinus - S24_lambdaPlus), 0] (by simpa [Fin.sum_univ_two] using hb1_zero)
  have hb1 : b₁ = 0 :=
    (mul_eq_zero.mp (by simpa using hb1_comb 0)).resolve_right (sub_ne_zero.mpr hne.symm)
  rw [hb1, zero_smul, zero_add] at hb
  have hp_ne : S24_eigenPlus ≠ 0 := by
    intro h0
    have hq := S24_eigenPlus_normalized
    rw [h0] at hq
    have hz : (0 : CuspForm SL2ZRange 24) = (0 : ℂ) • S24_vm1 := by simp
    rw [hz, qExpansionCoeff_smul, zero_mul] at hq
    exact zero_ne_one hq
  have hm_ne : S24_eigenMinus ≠ 0 := by
    intro h0
    have hq := S24_eigenMinus_normalized
    rw [h0] at hq
    have hz : (0 : CuspForm SL2ZRange 24) = (0 : ℂ) • S24_vm1 := by simp
    rw [hz, qExpansionCoeff_smul, zero_mul] at hq
    exact zero_ne_one hq
  have hpet_p : peterssonInner S24_eigenPlus S24_eigenPlus ≠ 0 :=
    (peterssonInner_self_eq_zero_iff S24_eigenPlus).not.mpr hp_ne
  have hpet_m : peterssonInner S24_eigenMinus S24_eigenMinus ≠ 0 :=
    (peterssonInner_self_eq_zero_iff S24_eigenMinus).not.mpr hm_ne
  refine ⟨a₁, b₂, ha, hb, ?_, ?_, ?_⟩
  · rw [ha, peterssonInner_smul_left, S24_hecke_eigenbasis.2.2.2.2, mul_zero]
  · rw [ha, peterssonInner_smul_left, mul_div_cancel_right₀ a₁ hpet_p]
  · rw [hb, peterssonInner_smul_left, mul_div_cancel_right₀ b₂ hpet_m]

end DoublingOperatorAndHeckeFactorization

/-! ### Part 2B: Exact Local Unramified Doubling Factor `Z_p(s, α_p, β_p) = L_p(s + 1/2, π) / d_p(s)` -/

section LocalUnramifiedDoublingFactor

/-- Complete homogeneous symmetric polynomial of degree `r` in two Satake parameters `(α, β)`:
`homogSym2 α β r = ∑ j = 0..r, α^j β^{r - j}` (equals `(α^{r+1} - β^{r+1}) / (α - β)` when
`α ≠ β`, and `(r + 1) α^r` when `α = β`). -/
def homogSym2 (α β : ℂ) (r : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j)

@[simp]
theorem homogSym2_zero (α β : ℂ) : homogSym2 α β 0 = 1 := by
  simp [homogSym2]

@[simp]
theorem homogSym2_one (α β : ℂ) : homogSym2 α β 1 = α + β := by
  simp [homogSym2, Finset.sum_range_succ, add_comm]

theorem homogSym2_eq_sum_antidiagonal (α β : ℂ) (r : ℕ) :
    homogSym2 α β r = ∑ kl ∈ Finset.antidiagonal r, α ^ kl.1 * β ^ kl.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => α ^ a * β ^ b)]
  rfl

theorem homogSym2_succ (α β : ℂ) (r : ℕ) :
    homogSym2 α β (r + 1) = α * homogSym2 α β r + β ^ (r + 1) := by
  unfold homogSym2
  rw [Finset.sum_range_succ' (f := fun j : ℕ => α ^ j * β ^ (r + 1 - j)) (r + 1),
    Nat.sub_zero, pow_zero, one_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ', Nat.succ_sub_succ_eq_sub]
  ring

/-- **Analytic Generating Function for `homogSym2`**:
for all `α, β, X : ℂ` with `‖α * X‖ < 1` and `‖β * X‖ < 1`,
`∑' r : ℕ, homogSym2 α β r * X ^ r = ((1 - α * X) * (1 - β * X))⁻¹`. -/
theorem hasSum_homogSym2_mul_pow {α β X : ℂ} (hα : ‖α * X‖ < 1) (hβ : ‖β * X‖ < 1) :
    HasSum (fun r : ℕ => homogSym2 α β r * X ^ r) (((1 - α * X) * (1 - β * X))⁻¹) := by
  set M : ℝ := max ‖α * X‖ ‖β * X‖
  have hM_nn : 0 ≤ M := le_trans (norm_nonneg _) (le_max_left _ _)
  have hM_lt : M < 1 := max_lt hα hβ
  have hterm_le : ∀ r : ℕ, ‖homogSym2 α β r * X ^ r‖ ≤ ((r : ℝ) + 1) * M ^ r := by
    intro r
    unfold homogSym2
    rw [Finset.sum_mul]
    calc ‖∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j) * X ^ r‖
        ≤ ∑ j ∈ Finset.range (r + 1), ‖α ^ j * β ^ (r - j) * X ^ r‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (r + 1), M ^ r := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hXsplit : X ^ r = X ^ j * X ^ (r - j) := by
              rw [← pow_add, Nat.add_sub_of_le hjr]
            rw [hXsplit]
            have hrearr : α ^ j * β ^ (r - j) * (X ^ j * X ^ (r - j)) =
                (α * X) ^ j * (β * X) ^ (r - j) := by
              rw [mul_pow, mul_pow]; ring
            rw [hrearr, norm_mul, norm_pow, norm_pow]
            calc ‖α * X‖ ^ j * ‖β * X‖ ^ (r - j)
                ≤ M ^ j * M ^ (r - j) :=
                  mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) j)
                    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) (r - j))
                    (pow_nonneg (norm_nonneg _) _) (pow_nonneg hM_nn _)
              _ = M ^ r := by rw [← pow_add, Nat.add_sub_of_le hjr]
      _ = ((r : ℝ) + 1) * M ^ r := by
            simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Geometric domination `((r : ℝ) + 1) * M^r ≤ C * r₀^r` with `r₀ = (M + 1)/2 < 1` via Bernoulli
  set r₀ : ℝ := (M + 1) / 2
  have hr₀_pos : 0 < r₀ := by dsimp only [r₀]; linarith
  have hr₀_lt : r₀ < 1 := by dsimp only [r₀]; linarith
  have hdom : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, ((r : ℝ) + 1) * M ^ r ≤ C * r₀ ^ r := by
    by_cases hM0 : M = 0
    · refine ⟨1, zero_le_one, fun r => ?_⟩
      cases r with
      | zero => simp [hM0]
      | succ k => simp [hM0]; positivity
    · have hM_pos : 0 < M := lt_of_le_of_ne hM_nn (Ne.symm hM0)
      set δ : ℝ := (1 - M) / (2 * M)
      have hδ_pos : 0 < δ := div_pos (sub_pos.mpr hM_lt) (by positivity)
      have hr₀_eq : r₀ = M * (1 + δ) := by
        dsimp only [r₀, δ]; field_simp [hM_pos.ne']; ring
      refine ⟨1 + δ⁻¹, by positivity, fun r => ?_⟩
      have hbern : 1 + (r : ℝ) * δ ≤ (1 + δ) ^ r := one_add_mul_le_pow (by linarith) r
      have hlin : (r : ℝ) + 1 ≤ (1 + δ⁻¹) * (1 + (r : ℝ) * δ) := by
        have h1 : (1 + δ⁻¹) * (1 + (r : ℝ) * δ) = (r : ℝ) + 1 + δ⁻¹ + (r : ℝ) * δ := by
          field_simp [hδ_pos.ne']; ring
        rw [h1]
        have hr_nn : (0 : ℝ) ≤ (r : ℝ) * δ := by positivity
        linarith [inv_pos.mpr hδ_pos]
      rw [hr₀_eq, mul_pow]
      calc ((r : ℝ) + 1) * M ^ r
          ≤ ((1 + δ⁻¹) * (1 + (r : ℝ) * δ)) * M ^ r :=
            mul_le_mul_of_nonneg_right hlin (pow_nonneg hM_nn r)
        _ ≤ ((1 + δ⁻¹) * (1 + δ) ^ r) * M ^ r :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbern (by positivity)) (pow_nonneg hM_nn r)
        _ = (1 + δ⁻¹) * (M ^ r * (1 + δ) ^ r) := by ring
  obtain ⟨C, hC_nn, hC⟩ := hdom
  have hsumm : Summable (fun r : ℕ => homogSym2 α β r * X ^ r) := by
    refine Summable.of_norm_bounded (g := fun r : ℕ => C * r₀ ^ r)
      ((summable_geometric_of_lt_one hr₀_pos.le hr₀_lt).mul_left C) fun r =>
      (hterm_le r).trans (hC r)
  -- Exact telescoping partial-sum identity:
  -- `(1 - α X) * ∑ r ∈ range (N + 1), h_r * X^r = (∑ r ∈ range (N + 1), (β X)^r) - (α X) * h_N * X^N`
  have htelescope : ∀ N : ℕ,
      (1 - α * X) * (∑ r ∈ Finset.range (N + 1), homogSym2 α β r * X ^ r) =
        (∑ r ∈ Finset.range (N + 1), (β * X) ^ r) - (α * X) * (homogSym2 α β N * X ^ N) := by
    intro N
    induction N with
    | zero =>
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        homogSym2_zero, pow_zero, mul_one]
    | succ N ih =>
      conv_lhs => rw [Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [mul_add, ih, homogSym2_succ, pow_succ', mul_pow]
      ring
  have hterm_tendsto : Filter.Tendsto (fun N : ℕ => homogSym2 α β N * X ^ N)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm (fun N => (hterm_le N).trans (hC N)) ?_
    have hpow0 : Filter.Tendsto (fun N : ℕ => r₀ ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr₀_pos.le hr₀_lt
    simpa only [mul_zero] using hpow0.const_mul C
  have hB : Filter.Tendsto (fun N : ℕ => ∑ r ∈ Finset.range (N + 1), (β * X) ^ r)
      Filter.atTop (nhds (1 - β * X)⁻¹) :=
    ((hasSum_geometric_of_norm_lt_one hβ).tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hS : Filter.Tendsto (fun N : ℕ => ∑ r ∈ Finset.range (N + 1), homogSym2 α β r * X ^ r)
      Filter.atTop (nhds (∑' r : ℕ, homogSym2 α β r * X ^ r)) :=
    (hsumm.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hL : Filter.Tendsto
      (fun N : ℕ => (1 - α * X) * ∑ r ∈ Finset.range (N + 1), homogSym2 α β r * X ^ r)
      Filter.atTop (nhds ((1 - α * X) * ∑' r : ℕ, homogSym2 α β r * X ^ r)) :=
    hS.const_mul (1 - α * X)
  have hR : Filter.Tendsto
      (fun N : ℕ => (∑ r ∈ Finset.range (N + 1), (β * X) ^ r) -
        (α * X) * (homogSym2 α β N * X ^ N))
      Filter.atTop (nhds ((1 - β * X)⁻¹)) := by
    simpa only [mul_zero, sub_zero] using hB.sub (hterm_tendsto.const_mul (α * X))
  have hL' : Filter.Tendsto
      (fun N : ℕ => (∑ r ∈ Finset.range (N + 1), (β * X) ^ r) -
        (α * X) * (homogSym2 α β N * X ^ N))
      Filter.atTop (nhds ((1 - α * X) * ∑' r : ℕ, homogSym2 α β r * X ^ r)) := by
    refine hL.congr fun N => htelescope N
  have heq : (1 - α * X) * ∑' r : ℕ, homogSym2 α β r * X ^ r = (1 - β * X)⁻¹ :=
    tendsto_nhds_unique hL' hR
  have h1α_ne : 1 - α * X ≠ 0 := by
    intro h0
    have h1 : α * X = 1 := sub_eq_zero.mp h0 |>.symm
    rw [h1, norm_one] at hα
    exact lt_irrefl 1 hα
  have htsum_eq : ∑' r : ℕ, homogSym2 α β r * X ^ r = ((1 - α * X) * (1 - β * X))⁻¹ := by
    rw [mul_inv, mul_comm (1 - α * X)⁻¹]
    calc ∑' r : ℕ, homogSym2 α β r * X ^ r
        = (1 - α * X)⁻¹ * ((1 - α * X) * ∑' r : ℕ, homogSym2 α β r * X ^ r) := by
            rw [← mul_assoc, inv_mul_cancel₀ h1α_ne, one_mul]
      _ = (1 - α * X)⁻¹ * (1 - β * X)⁻¹ := by rw [heq]
      _ = (1 - β * X)⁻¹ * (1 - α * X)⁻¹ := mul_comm _ _
  rw [← htsum_eq]
  exact hsumm.hasSum

/-- **Cartan Double-Coset Volume `vol(K diag(p^r, 1) K)`** in `GL₂(ℚ_p) / Z`:
`1` for `r = 0`, and `p^r * (1 + p⁻¹)` for `r ≥ 1`. -/
def cartanCosetVol (p : ℕ) (r : ℕ) : ℂ :=
  if r = 0 then 1 else (p : ℂ) ^ r * (1 + (p : ℂ)⁻¹)

/-- **Macdonald Unramified Spherical Matrix Coefficient `Φ_π(diag(p^r, 1))`** on `GL₂(ℚ_p)`
for Satake parameters `(α_p, β_p)`:
- `r = 0`: `1`,
- `r = 1`: `(1 + p⁻¹)⁻¹ * p^{-1/2} * (α_p + β_p)`,
- `r ≥ 2`: `(1 + p⁻¹)⁻¹ * p^{-r/2} * (h_r(α_p, β_p) - p⁻¹ α_p β_p h_{r-2}(α_p, β_p))`. -/
def macdonaldSphericalGL2 (p : ℕ) (α β : ℂ) (r : ℕ) : ℂ :=
  match r with
  | 0 => 1
  | 1 => (1 + (p : ℂ)⁻¹)⁻¹ * (p : ℂ) ^ (-(1 : ℂ) / 2) * homogSym2 α β 1
  | m + 2 =>
      (1 + (p : ℂ)⁻¹)⁻¹ * (p : ℂ) ^ (-((m + 2 : ℕ) : ℂ) / 2) *
        (homogSym2 α β (m + 2) - (p : ℂ)⁻¹ * (α * β) * homogSym2 α β m)

/-- **Unramified Siegel–Eisenstein Doubling Section** on the Cartan torus `diag(p^r, 1)`:
`f_s(diag(p^r, 1)) = p^{-r(s + 1)}`. -/
def unramifiedDoublingSection (p : ℕ) (s : ℂ) (r : ℕ) : ℂ :=
  (p : ℂ) ^ (-(r : ℂ) * (s + 1))

/-- **Concrete Local Unramified Doubling Zeta Integral `Z_p(s, α_p, β_p)`** for `GL₂(ℚ_p)`:
summing the Cartan double-coset matrix-coefficient integral over all `r : ℕ`,
$$Z_p(s, \alpha_p, \beta_p) = \sum_{r=0}^{\infty} \operatorname{vol}(K a_r K)\,\Phi_\pi(a_r)\,f_s(a_r).$$ -/
def localDoublingZetaGL2 (p : ℕ) (α β s : ℂ) : ℂ :=
  ∑' r : ℕ, cartanCosetVol p r * macdonaldSphericalGL2 p α β r * unramifiedDoublingSection p s r

/-- **Local Standard Degree-2 `L`-Factor** for `GL₂` Satake parameters `(α_p, β_p)`:
`L_p(w, π) = ((1 - α_p p^{-w}) (1 - β_p p^{-w}))⁻¹`. -/
def localStdLFactorGL2 (p : ℕ) (α β w : ℂ) : ℂ :=
  ((1 - α * (p : ℂ) ^ (-w)) * (1 - β * (p : ℂ) ^ (-w)))⁻¹

/-- **Local Piatetski-Shapiro–Rallis Normalizing Factor `d_p(s, ω_p)`**:
`d_p(s, ω_p) = (1 - ω_p * p^{-(2s + 2)})⁻¹` (where `ω_p = α_p β_p`; for trivial central
character `ω_p = 1`, `d_p(s) = ζ_p(2s + 2) = (1 - p^{-(2s + 2)})⁻¹`). -/
def localDoublingNormFactor (p : ℕ) (ω s : ℂ) : ℂ :=
  (1 - ω * (p : ℂ) ^ (-(2 * s + 2)))⁻¹

/-- Exact Cartan-term simplification: for any prime `p` (`p ≥ 2`, hence `1 + p⁻¹ ≠ 0`),
`vol(K a_r K) * Φ_π(a_r) * f_s(a_r) = c_r(α, β) * (p^{-(s + 1/2)})^r`. -/
private lemma cartan_term_simplify {p : ℕ} (hp : p.Prime) (α β s : ℂ) (r : ℕ) :
    cartanCosetVol p r * macdonaldSphericalGL2 p α β r * unramifiedDoublingSection p s r =
      (match r with
       | 0 => homogSym2 α β 0
       | 1 => homogSym2 α β 1
       | m + 2 => homogSym2 α β (m + 2) - (p : ℂ)⁻¹ * (α * β) * homogSym2 α β m) *
        ((p : ℂ) ^ (-(s + 1 / 2))) ^ r := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hpC_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h1p_ne : (1 : ℂ) + (p : ℂ)⁻¹ ≠ 0 := by
    have hR : (0 : ℝ) < 1 + (p : ℝ)⁻¹ := by positivity
    have hC : ((1 + (p : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_natCast] using hC
  have hpow : ∀ n : ℕ,
      (p : ℂ) ^ n * (p : ℂ) ^ (-(n : ℂ) / 2) * (p : ℂ) ^ (-(n : ℂ) * (s + 1)) =
        ((p : ℂ) ^ (-(s + 1 / 2))) ^ n := by
    intro n
    rw [← Complex.cpow_natCast (p : ℂ) n, ← Complex.cpow_add _ _ hpC_ne,
      ← Complex.cpow_add _ _ hpC_ne, ← Complex.cpow_nat_mul]
    congr 1
    ring
  cases r with
  | zero =>
    simp [cartanCosetVol, macdonaldSphericalGL2, unramifiedDoublingSection]
  | succ k =>
    cases k with
    | zero =>
      simp only [cartanCosetVol, Nat.zero_add, one_ne_zero, ↓reduceIte,
        macdonaldSphericalGL2, unramifiedDoublingSection, pow_one, Nat.cast_one]
      have h1 := hpow 1
      simp only [pow_one, Nat.cast_one] at h1
      calc (p : ℂ) * (1 + (p : ℂ)⁻¹) *
              ((1 + (p : ℂ)⁻¹)⁻¹ * (p : ℂ) ^ (-(1 : ℂ) / 2) * homogSym2 α β 1) *
              (p : ℂ) ^ (-(1 : ℂ) * (s + 1))
          = homogSym2 α β 1 * ((1 + (p : ℂ)⁻¹) * (1 + (p : ℂ)⁻¹)⁻¹) *
              ((p : ℂ) * (p : ℂ) ^ (-(1 : ℂ) / 2) * (p : ℂ) ^ (-(1 : ℂ) * (s + 1))) := by ring
        _ = homogSym2 α β 1 * (p : ℂ) ^ (-(s + 1 / 2)) := by
              rw [mul_inv_cancel₀ h1p_ne, mul_one, h1]
    | succ m =>
      simp only [cartanCosetVol, Nat.succ_ne_zero, ↓reduceIte, macdonaldSphericalGL2,
        unramifiedDoublingSection]
      have hm := hpow (m + 2)
      calc (p : ℂ) ^ (m + 2) * (1 + (p : ℂ)⁻¹) *
              ((1 + (p : ℂ)⁻¹)⁻¹ * (p : ℂ) ^ (-((m + 2 : ℕ) : ℂ) / 2) *
                (homogSym2 α β (m + 2) - (p : ℂ)⁻¹ * (α * β) * homogSym2 α β m)) *
              (p : ℂ) ^ (-((m + 2 : ℕ) : ℂ) * (s + 1))
          = (homogSym2 α β (m + 2) - (p : ℂ)⁻¹ * (α * β) * homogSym2 α β m) *
              ((1 + (p : ℂ)⁻¹) * (1 + (p : ℂ)⁻¹)⁻¹) *
              ((p : ℂ) ^ (m + 2) * (p : ℂ) ^ (-((m + 2 : ℕ) : ℂ) / 2) *
                (p : ℂ) ^ (-((m + 2 : ℕ) : ℂ) * (s + 1))) := by ring
        _ = (homogSym2 α β (m + 2) - (p : ℂ)⁻¹ * (α * β) * homogSym2 α β m) *
              ((p : ℂ) ^ (-(s + 1 / 2))) ^ (m + 2) := by
              rw [mul_inv_cancel₀ h1p_ne, mul_one, hm]

/-- **EXACT LOCAL UNRAMIFIED DOUBLING FACTOR FOR `GL₂` (`localDoublingZetaGL2_eq`)
(`0` Assumptions!)**:
For EVERY prime `p`, Satake parameters `(α_p, β_p)`, and complex parameter `s` in the domain
of absolute convergence (`‖α_p * p^{-(s + 1/2)}‖ < 1` and `‖β_p * p^{-(s + 1/2)}‖ < 1`),
the Macdonald–Cartan doubling zeta integral evaluates EXACTLY to the local standard `L`-factor
divided by the Piatetski-Shapiro–Rallis normalizing factor:
$$Z_p(s, \alpha_p, \beta_p) = \frac{L_p(s + 1/2, \pi)}{d_p(s, \alpha_p \beta_p)}
  = \frac{1 - \alpha_p \beta_p p^{-(2s + 2)}}{(1 - \alpha_p p^{-(s + 1/2)})(1 - \beta_p p^{-(s + 1/2)})}!$$ -/
theorem localDoublingZetaGL2_eq {p : ℕ} (hp : p.Prime) {α β s : ℂ}
    (hα : ‖α * (p : ℂ) ^ (-(s + 1 / 2))‖ < 1)
    (hβ : ‖β * (p : ℂ) ^ (-(s + 1 / 2))‖ < 1) :
    localDoublingZetaGL2 p α β s =
      localStdLFactorGL2 p α β (s + 1 / 2) / localDoublingNormFactor p (α * β) s := by
  have hpC_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  set X : ℂ := (p : ℂ) ^ (-(s + 1 / 2))
  have hMain : HasSum (fun r : ℕ => homogSym2 α β r * X ^ r)
      (((1 - α * X) * (1 - β * X))⁻¹) := hasSum_homogSym2_mul_pow hα hβ
  let cShift : ℂ := (p : ℂ)⁻¹ * (α * β) * X ^ 2
  have hSubBase : HasSum (fun m : ℕ => cShift * (homogSym2 α β m * X ^ m))
      (cShift * ((1 - α * X) * (1 - β * X))⁻¹) := hMain.mul_left cShift
  let gShift : ℕ → ℂ := fun r =>
    match r with
    | 0 => 0
    | 1 => 0
    | m + 2 => (p : ℂ)⁻¹ * (α * β) * homogSym2 α β m * X ^ (m + 2)
  have hShift : HasSum gShift (cShift * ((1 - α * X) * (1 - β * X))⁻¹) := by
    have h2 : HasSum (fun m : ℕ => gShift (m + 2)) (cShift * ((1 - α * X) * (1 - β * X))⁻¹) := by
      refine hSubBase.congr_fun fun m => ?_
      dsimp only [gShift, cShift]
      rw [pow_add]
      ring
    have h2' : HasSum (fun m : ℕ => gShift (m + 2))
        (cShift * ((1 - α * X) * (1 - β * X))⁻¹ - ∑ i ∈ Finset.range 2, gShift i) := by
      simpa [Finset.sum_range_succ, gShift] using h2
    exact (hasSum_nat_add_iff' 2 (f := gShift)).mp h2'
  have hDiff : HasSum (fun r : ℕ => homogSym2 α β r * X ^ r - gShift r)
      (((1 - α * X) * (1 - β * X))⁻¹ - cShift * ((1 - α * X) * (1 - β * X))⁻¹) :=
    hMain.sub hShift
  have hTerms : (fun r : ℕ =>
      cartanCosetVol p r * macdonaldSphericalGL2 p α β r * unramifiedDoublingSection p s r) =
      fun r : ℕ => homogSym2 α β r * X ^ r - gShift r := by
    funext r
    rw [cartan_term_simplify hp α β s r]
    cases r with
    | zero =>
      dsimp only [gShift, X]
      ring
    | succ k =>
      cases k with
      | zero =>
        dsimp only [gShift, X]
        ring
      | succ m =>
        dsimp only [gShift, X]
        ring
  unfold localDoublingZetaGL2
  rw [hTerms, hDiff.tsum_eq]
  have hX2 : (p : ℂ)⁻¹ * X ^ 2 = (p : ℂ) ^ (-(2 * s + 2)) := by
    dsimp only [X]
    rw [← Complex.cpow_neg_one (p : ℂ), ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hpC_ne]
    congr 1
    push_cast
    ring
  have hcShift : cShift = (α * β) * (p : ℂ) ^ (-(2 * s + 2)) := by
    dsimp only [cShift]
    rw [← hX2]
    ring
  unfold localStdLFactorGL2 localDoublingNormFactor
  rw [hcShift, div_inv_eq_mul]
  change ((1 - α * X) * (1 - β * X))⁻¹ -
      α * β * (p : ℂ) ^ (-(2 * s + 2)) * ((1 - α * X) * (1 - β * X))⁻¹ =
    ((1 - α * X) * (1 - β * X))⁻¹ * (1 - α * β * (p : ℂ) ^ (-(2 * s + 2)))
  ring

/-- **Specialization to Trivial Central Character (`α_p * β_p = 1`)**:
`Z_p(s, α_p, β_p) = L_p(s + 1/2, π) / ζ_p(2s + 2)`! -/
theorem localDoublingZetaGL2_trivial_central {p : ℕ} (hp : p.Prime) {α β s : ℂ}
    (hω : α * β = 1)
    (hα : ‖α * (p : ℂ) ^ (-(s + 1 / 2))‖ < 1)
    (hβ : ‖β * (p : ℂ) ^ (-(s + 1 / 2))‖ < 1) :
    localDoublingZetaGL2 p α β s =
      localStdLFactorGL2 p α β (s + 1 / 2) / (1 - (p : ℂ) ^ (-(2 * s + 2)))⁻¹ := by
  rw [localDoublingZetaGL2_eq hp hα hβ, hω, localDoublingNormFactor, one_mul]

/-- **Exact Match between `localStdLFactorGL2` and `Stage5ModularHecke.degree2EulerFactor`**:
whenever Satake parameters satisfy `α + β = a_p` and `α * β = p^{k - 1}`,
`localStdLFactorGL2 p α β w = degree2EulerFactor k 1 a_p p w`! -/
theorem localStdLFactorGL2_eq_degree2EulerFactor {k p : ℕ} (hp : p.Prime) {α β a_p w : ℂ}
    (hsum : α + β = a_p) (hprod : α * β = (p : ℂ) ^ (k - 1)) :
    localStdLFactorGL2 p α β w =
      degree2EulerFactor k (1 : DirichletCharacter ℂ 1) a_p p w := by
  have hpC_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  unfold localStdLFactorGL2 degree2EulerFactor
  have hchi : (1 : DirichletCharacter ℂ 1) (p : ZMod 1) = 1 :=
    MulChar.one_apply ((ZMod.isUnit_iff_coprime p 1).mpr (Nat.coprime_one_right p))
  rw [hchi, one_mul]
  congr 1
  have hpow : (p : ℂ) ^ (k - 1) * ((p : ℂ) ^ (-w) * (p : ℂ) ^ (-w)) =
      (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * w) := by
    rw [← Complex.cpow_natCast (p : ℂ) (k - 1), ← Complex.cpow_add _ _ hpC_ne,
      ← Complex.cpow_add _ _ hpC_ne]
    congr 1
    ring
  calc (1 - α * (p : ℂ) ^ (-w)) * (1 - β * (p : ℂ) ^ (-w))
      = 1 - (α + β) * (p : ℂ) ^ (-w) + (α * β) * ((p : ℂ) ^ (-w) * (p : ℂ) ^ (-w)) := by ring
    _ = 1 - a_p * (p : ℂ) ^ (-w) + (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * w) := by
          rw [hsum, hprod, hpow]

/-- Complex square root `z^(1/2)` satisfying `(csqrt z)^2 = z` for every `z : ℂ`. -/
def csqrt (z : ℂ) : ℂ :=
  z ^ ((1 : ℂ) / 2)

theorem csqrt_sq (z : ℂ) : csqrt z ^ 2 = z := by
  unfold csqrt
  by_cases hz : z = 0
  · subst hz
    rw [Complex.zero_cpow (by norm_num), zero_pow (by decide : 2 ≠ 0)]
  · rw [← Complex.cpow_nat_mul]
    have h2 : ((2 : ℕ) : ℂ) * ((1 : ℂ) / 2) = 1 := by push_cast; ring
    rw [h2, Complex.cpow_one]

/-- **Explicit Satake Parameter Pair for Any Hecke Eigenvalue `(a_p, p^{k - 1})`** (`0` Assumptions!):
using `csqrt` on the discriminant `a_p² - 4 p^{k - 1}`, we construct explicit
`α_p, β_p : ℂ` with `α_p + β_p = a_p` and `α_p * β_p = p^{k - 1}`. -/
def satakeAlpha (k p : ℕ) (a_p : ℂ) : ℂ :=
  (a_p + csqrt (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1))) / 2

def satakeBeta (k p : ℕ) (a_p : ℂ) : ℂ :=
  (a_p - csqrt (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1))) / 2

theorem satakeAlpha_add_beta (k p : ℕ) (a_p : ℂ) :
    satakeAlpha k p a_p + satakeBeta k p a_p = a_p := by
  unfold satakeAlpha satakeBeta
  ring

theorem satakeAlpha_mul_beta (k p : ℕ) (a_p : ℂ) :
    satakeAlpha k p a_p * satakeBeta k p a_p = (p : ℂ) ^ (k - 1) := by
  unfold satakeAlpha satakeBeta
  have hsq : csqrt (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1)) ^ 2 =
      a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1) :=
    csqrt_sq _
  calc (a_p + csqrt (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1))) / 2 *
        ((a_p - csqrt (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1))) / 2)
      = (a_p ^ 2 - csqrt (a_p ^ 2 - 4 * (p : ℂ) ^ (k - 1)) ^ 2) / 4 := by ring
    _ = (p : ℂ) ^ (k - 1) := by rw [hsq]; ring

/-- **GLOBAL EULER PRODUCT OF NORMALIZED LOCAL DOUBLING FACTORS FOR `E₈` / `E₄` (`0` Assumptions!)**:
At every prime `p`, the weight-4 Eisenstein series `E₄ = Θ_{E₈}` has explicit Satake parameters
`α_p = 1, β_p = p³` (`α_p + β_p = σ₃(p)`, `α_p β_p = p³`), so for `Re(s) > 7/2`, the global
Euler product of normalized local doubling integrals equals the `E₈` Epstein–Eisenstein zeta
function `ζ(s + 1/2) ζ(s - 5/2)`! -/
theorem E8_global_doubling_euler_product {s : ℂ} (hs : (7 : ℝ) / 2 < s.re) :
    (∏' p : Nat.Primes,
      localDoublingNormFactor p.1 ((p.1 : ℂ) ^ 3) s *
        localDoublingZetaGL2 p.1 1 ((p.1 : ℂ) ^ 3) s) =
      riemannZeta (s + 1 / 2) * riemannZeta (s + 1 / 2 - 3) := by
  have hre : (8 : ℝ) < (2 * (s + 1 / 2)).re := by
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.add_re,
      Complex.div_ofNat_re, Complex.one_re, zero_mul, sub_zero]
    linarith
  have hfactor : ∀ p : Nat.Primes,
      localDoublingNormFactor p.1 ((p.1 : ℂ) ^ 3) s *
        localDoublingZetaGL2 p.1 1 ((p.1 : ℂ) ^ 3) s =
      degree2EulerFactor 4 (1 : DirichletCharacter ℂ 1)
        (eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1) (p : ℕ)) (p : ℕ) (s + 1 / 2) := by
    intro p
    have hp_ge2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
    have hp_pos : (0 : ℝ) < (p.1 : ℝ) := by linarith
    have hp_gt1 : (1 : ℝ) < (p.1 : ℝ) := by linarith
    have hnormX : ‖(p.1 : ℂ) ^ (-(s + 1 / 2))‖ = (p.1 : ℝ) ^ (-(s.re + 1 / 2)) := by
      rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
      simp only [Complex.neg_re, Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    have hα : ‖(1 : ℂ) * (p.1 : ℂ) ^ (-(s + 1 / 2))‖ < 1 := by
      rw [one_mul, hnormX]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
    have hβ : ‖(p.1 : ℂ) ^ 3 * (p.1 : ℂ) ^ (-(s + 1 / 2))‖ < 1 := by
      rw [norm_mul, norm_pow, Complex.norm_natCast, hnormX, ← Real.rpow_natCast (p.1 : ℝ) 3,
        ← Real.rpow_add hp_pos]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by push_cast; linarith)
    have hnorm_ne : localDoublingNormFactor p.1 ((p.1 : ℂ) ^ 3) s ≠ 0 := by
      unfold localDoublingNormFactor
      refine inv_ne_zero (sub_ne_zero.mpr fun h1 => ?_)
      have hlt : ‖(p.1 : ℂ) ^ 3 * (p.1 : ℂ) ^ (-(2 * s + 2))‖ < 1 := by
        rw [norm_mul, norm_pow, Complex.norm_natCast,
          Complex.norm_natCast_cpow_of_pos p.2.pos, ← Real.rpow_natCast (p.1 : ℝ) 3,
          ← Real.rpow_add hp_pos]
        apply Real.rpow_lt_one_of_one_lt_of_neg hp_gt1
        simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
          Complex.im_ofNat, zero_mul, sub_zero]
        push_cast
        linarith
      rw [← h1, norm_one] at hlt
      exact lt_irrefl 1 hlt
    rw [localDoublingZetaGL2_eq p.2 hα hβ, one_mul, mul_div_cancel₀ _ hnorm_ne]
    refine localStdLFactorGL2_eq_degree2EulerFactor p.2 ?_ (by simp)
    rw [← sigma_three_eq_eisensteinCoeff p.1, ArithmeticFunction.sigma_apply, p.2.divisors]
    rw [Finset.sum_pair p.2.ne_one.symm]
    push_cast
    ring
  rw [tprod_congr hfactor]
  have hep1 := epsteinZeta_E8Lattice_eq (s := 2 * (s + 1 / 2)) hre
  have hep2 := epsteinZeta_E8Lattice_eulerProduct (s := 2 * (s + 1 / 2)) hre
  have hdiv2 : 2 * (s + 1 / 2) / 2 = s + 1 / 2 := by ring
  rw [hdiv2] at hep1 hep2
  have hpre_ne : (240 : ℂ) * (2 : ℂ) ^ (-(2 * (s + 1 / 2)) / 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  have heq : (240 : ℂ) * (2 : ℂ) ^ (-(2 * (s + 1 / 2)) / 2) *
        (∏' p : Nat.Primes, degree2EulerFactor 4 (1 : DirichletCharacter ℂ 1)
          (eisensteinCoeff 4 (1 : DirichletCharacter ℂ 1) (p : ℕ)) (p : ℕ) (s + 1 / 2)) =
      (240 : ℂ) * (2 : ℂ) ^ (-(2 * (s + 1 / 2)) / 2) *
        (riemannZeta (s + 1 / 2) * riemannZeta (s + 1 / 2 - 3)) := by
    rw [← hep2, hep1]
    ring
  exact mul_left_cancel₀ hpre_ne heq

/-- **Rank-`n` `U(n)` / `GL_n` Local Standard `L`-Factor** for Satake parameters
`α : Fin n → ℂ`: `L_p(w, π) = ∏_{i=1}^n (1 - α_i p^{-w})⁻¹`. -/
def localStdLFactorUn (n p : ℕ) (α : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∏ i : Fin n, (1 - α i * (p : ℂ) ^ (-w))⁻¹

/-- **Rank-`n` `U(n)` Local Doubling Normalizing Factor** `d_p(s) = ∏_{j=0}^{n-1} (1 - p^{-(2s + n - j)})⁻¹`. -/
def localDoublingNormFactorUn (n p : ℕ) (s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 - (p : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ))))⁻¹

/-- **Rank-`n` `U(n)` Local Unramified Doubling Factor**:
`Z_p^{(n)}(s, α) = ∏_{i : Fin n} (1 - p^{-(2s + n - i)}) / (1 - α_i p^{-(s + 1/2)})`. -/
def localDoublingFactorUn (n p : ℕ) (α : Fin n → ℂ) (s : ℂ) : ℂ :=
  ∏ i : Fin n, (1 - (p : ℂ) ^ (-(2 * s + (n : ℂ) - (i.1 : ℂ)))) *
    (1 - α i * (p : ℂ) ^ (-(s + 1 / 2)))⁻¹

/-- **Exact Rank-`n` `U(n)` Local Unramified Doubling Factorization (`localDoublingFactorUn_eq`)**:
$$Z_p^{(n)}(s, \alpha) = \frac{L_p^{(n)}(s + 1/2, \alpha)}{d_p^{(n)}(s)}!$$ -/
theorem localDoublingFactorUn_eq (n p : ℕ) (α : Fin n → ℂ) (s : ℂ) :
    localDoublingFactorUn n p α s =
      localStdLFactorUn n p α (s + 1 / 2) / localDoublingNormFactorUn n p s := by
  unfold localDoublingFactorUn localStdLFactorUn localDoublingNormFactorUn
  rw [Finset.prod_mul_distrib,
    Finset.prod_inv_distrib (s := Finset.range n)
      (f := fun j : ℕ => 1 - (p : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ)))),
    div_inv_eq_mul, mul_comm]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => 1 - (p : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ)))) n]

end LocalUnramifiedDoublingFactor

/-! ## Section 3: Concrete Rallis Inner-Product Positivity, Non-Vanishing Criterion & Direct
Bridge into `RHDirect.RallisSeesaw` and `RHDirect.SiegelWeilCore` -/

section RallisPositivityAndBridge

/-- Concrete **Doubling Gram Operator** `D = θ* ∘ₗ θ : L²(G) →ₗ[ℂ] L²(G)` whose kernel is the
doubled theta kernel `Θ_doubled(g₁, g₂) = ∑ h, Θ(g₁, h) conj(Θ(g₂, h))`. -/
def doublingGramOp {G H : Type*} [Fintype G] [Fintype H] (Θ : G → H → ℂ) :
    Module.End ℂ (EuclideanSpace ℂ G) :=
  thetaLiftAdjLin Θ ∘ₗ thetaLiftLin Θ

/-- Explicit kernel formula for the doubling Gram operator `D = θ* ∘ₗ θ`:
`(D φ)(g₂) = ∑ g₁, φ(g₁) * Θ_doubled(g₁, g₂)`. -/
theorem doublingGramOp_apply {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ : EuclideanSpace ℂ G) (g₂ : G) :
    doublingGramOp Θ φ g₂ =
      ∑ g₁ : G, φ g₁ * doubledThetaKernel (fun _ => (1 : ℂ)) Θ (g₁, g₂) := by
  unfold doublingGramOp doubledThetaKernel
  simp only [LinearMap.comp_apply, thetaLiftAdjLin_apply, thetaLiftLin_apply, one_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => by ring

/-- Exact Hilbert-adjoint identification: `thetaLiftAdjLin Θ = LinearMap.adjoint (thetaLiftLin Θ)`. -/
theorem thetaLiftAdjLin_eq_adjoint {G H : Type*} [Fintype G] [Fintype H] (Θ : G → H → ℂ) :
    thetaLiftAdjLin Θ = LinearMap.adjoint (thetaLiftLin Θ) := by
  apply LinearMap.ext
  intro ψ
  refine ext_inner_left ℂ fun φ => ?_
  rw [LinearMap.adjoint_inner_right, euclidean_inner_eq, euclidean_inner_eq]
  simp only [thetaLiftLin_apply, thetaLiftAdjLin_apply, star_sum, star_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => by ring

/-- **Self-Adjointness of the Doubling Gram Operator `D = θ* ∘ θ`**. -/
theorem doublingGramOp_self_adjoint {G H : Type*} [Fintype G] [Fintype H] (Θ : G → H → ℂ) :
    LinearMap.adjoint (doublingGramOp Θ) = doublingGramOp Θ := by
  unfold doublingGramOp
  rw [thetaLiftAdjLin_eq_adjoint, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]

/-- **Direct Instantiation of `RHDirect.RallisSeesaw.SeesawDualPair`** for any concrete finite
theta kernel `Θ : G → H → ℂ`. -/
def concreteThetaSeesawPair {G H : Type*} [Fintype G] [Fintype H] (Θ : G → H → ℂ) :
    SeesawDualPair ℂ (EuclideanSpace ℂ G) (EuclideanSpace ℂ H) where
  θ := thetaLiftLin Θ
  θAdj := thetaLiftAdjLin Θ
  adjoint_eq φ ψ := by
    rw [thetaLiftAdjLin_eq_adjoint, LinearMap.adjoint_inner_right]

/-- **Direct Instantiation of `RHDirect.RallisSeesaw.SeesawDualPair`** for the doubled space
`G × G → H` with split kernel `Θ₁(g₁, h) * Θ₂(g₂, h)`. -/
def doubledSeesawPair {G₁ G₂ H : Type*} [Fintype G₁] [Fintype G₂] [Fintype H]
    (Θ₁ : G₁ → H → ℂ) (Θ₂ : G₂ → H → ℂ) :
    SeesawDualPair ℂ (EuclideanSpace ℂ (G₁ × G₂)) (EuclideanSpace ℂ H) :=
  concreteThetaSeesawPair (prodThetaKernel Θ₁ Θ₂)

/-- **Exact Doubling Inner-Product Identity**:
`⟨D φ, φ⟩ = ⟨φ, D φ⟩ = ⟨θ(φ), θ(φ)⟩ = ‖θ(φ)‖²`. -/
theorem doublingGramOp_inner_eq_normSq {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ : EuclideanSpace ℂ G) :
    inner ℂ (doublingGramOp Θ φ) φ = ((‖thetaLiftLin Θ φ‖ ^ 2 : ℝ) : ℂ) ∧
    inner ℂ φ (doublingGramOp Θ φ) = ((‖thetaLiftLin Θ φ‖ ^ 2 : ℝ) : ℂ) := by
  have hR : inner ℂ φ (doublingGramOp Θ φ) = ((‖thetaLiftLin Θ φ‖ ^ 2 : ℝ) : ℂ) :=
    (concreteThetaSeesawPair Θ).rallis_pairing_eq_normSq φ
  have hL : inner ℂ (doublingGramOp Θ φ) φ = ((‖thetaLiftLin Θ φ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hR, Complex.conj_ofReal]
  exact ⟨hL, hR⟩

/-- **CONCRETE RALLIS INNER-PRODUCT POSITIVITY (`rallis_inner_product_nonneg`) (`0` Assumptions!)**:
1. For every finite theta lift `θ(φ) ∈ L²(H)`, `0 ≤ (⟨θ(φ), θ(φ)⟩).re` and `(⟨θ(φ), θ(φ)⟩).im = 0`.
2. For every weighted genus theta lift with `0 ≤ wH`, `0 ≤ (autInner wH (θ φ) (θ φ)).re`. -/
theorem rallis_inner_product_nonneg {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ : EuclideanSpace ℂ G) :
    0 ≤ (inner ℂ (thetaLiftLin Θ φ) (thetaLiftLin Θ φ)).re ∧
    (inner ℂ (thetaLiftLin Θ φ) (thetaLiftLin Θ φ)).im = 0 := by
  have h := (concreteThetaSeesawPair Θ).rallis_pairing_re_nonneg φ
  have heq : inner ℂ (thetaLiftLin Θ φ) (thetaLiftLin Θ φ) =
      inner ℂ φ ((concreteThetaSeesawPair Θ).θAdj ((concreteThetaSeesawPair Θ).θ φ)) :=
    (concreteThetaSeesawPair Θ).adjoint_eq φ (thetaLiftLin Θ φ)
  rw [heq]
  exact h

theorem rallis_weighted_inner_product_nonneg {G H : Type*} [Fintype G] [Fintype H]
    (wG : G → ℂ) {wH : H → ℝ} (hwH : ∀ h, 0 ≤ wH h) (Θ : G → H → ℂ) (φ : G → ℂ) :
    0 ≤ (autInner (fun h => (wH h : ℂ)) (thetaLiftW wG Θ φ) (thetaLiftW wG Θ φ)).re ∧
    (autInner (fun h => (wH h : ℂ)) (thetaLiftW wG Θ φ) (thetaLiftW wG Θ φ)).im = 0 := by
  rw [autInner_eq_wip_swap]
  exact wip_self_re_nonneg hwH _

/-- **Continuous / Archimedean Rallis Inner-Product Positivity (`rallis_integral_inner_product_nonneg`)**:
for any measure space `(H, μH)` and theta lift `θ(φ)`, `0 ≤ (∫_H θ(φ)(h) conj(θ(φ)(h)) dμ_H).re`! -/
theorem rallis_integral_inner_product_nonneg {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    (μG : Measure G) (μH : Measure H) (Θ : G → H → ℂ) (φ : G → ℂ) :
    0 ≤ (∫ h, thetaLiftInt μG Θ φ h * star (thetaLiftInt μG Θ φ h) ∂μH).re ∧
    (∫ h, thetaLiftInt μG Θ φ h * star (thetaLiftInt μG Θ φ h) ∂μH).im = 0 := by
  have hof : (∫ h, ((‖thetaLiftInt μG Θ φ h‖ ^ 2 : ℝ) : ℂ) ∂μH) =
      ((∫ h, ‖thetaLiftInt μG Θ φ h‖ ^ 2 ∂μH : ℝ) : ℂ) := integral_ofReal
  have heq : (∫ h, thetaLiftInt μG Θ φ h * star (thetaLiftInt μG Θ φ h) ∂μH) =
      ((∫ h, ‖thetaLiftInt μG Θ φ h‖ ^ 2 ∂μH : ℝ) : ℂ) := by
    rw [← hof]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    dsimp only
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [heq, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨integral_nonneg fun h => sq_nonneg _, rfl⟩

/-- **CONCRETE RALLIS NON-VANISHING CRITERION (`theta_lift_ne_zero_iff_doubling_pos`)
(`0` Assumptions!)**:
For any concrete finite dual-pair theta lift `θ = thetaLiftLin Θ` and its doubling Gram operator
`D = doublingGramOp Θ`:
$$\theta(\varphi) \ne 0 \iff 0 < \operatorname{Re}\langle D \varphi, \varphi \rangle
  \iff 0 < \operatorname{Re}\langle \varphi, D \varphi \rangle!$$ -/
theorem theta_lift_ne_zero_iff_doubling_pos {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ : EuclideanSpace ℂ G) :
    thetaLiftLin Θ φ ≠ 0 ↔ 0 < (inner ℂ (doublingGramOp Θ φ) φ).re := by
  rw [(doublingGramOp_inner_eq_normSq Θ φ).1, Complex.ofReal_re]
  constructor
  · intro hne
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  · intro hpos h0
    rw [h0, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hpos
    exact lt_irrefl 0 hpos

/-- **Weighted Genus Non-Vanishing Criterion**:
for strictly positive weights `wH > 0`, `θ(φ) ≠ 0` iff the doubled genus pairing is strictly positive! -/
theorem weighted_theta_lift_ne_zero_iff_doubling_pos {G H : Type*} [Fintype G] [Fintype H]
    (wG : G → ℝ) {wH : H → ℝ} (hwH : ∀ h, 0 < wH h) (Θ : G → H → ℂ) (φ : G → ℂ) :
    thetaLiftW (fun g => (wG g : ℂ)) Θ φ ≠ 0 ↔
      0 < (∑ p : G × G, ((wG p.1 : ℂ) * (wG p.2 : ℂ)) * φ p.1 * star (φ p.2) *
        doubledThetaKernel (fun h => (wH h : ℂ)) Θ p).re := by
  have hwG_star : ∀ g, star (wG g : ℂ) = (wG g : ℂ) := fun g => Complex.conj_ofReal _
  rw [← doubling_seesaw_inner_product_eq (fun g => (wG g : ℂ)) (fun h => (wH h : ℂ)) hwG_star Θ φ φ,
    autInner_eq_wip_swap, wip_self_eq_sum_normSq, Complex.ofReal_re]
  constructor
  · intro hne
    have hneq0 : wip (fun h => (wH h : ℂ)) (thetaLiftW (fun g => (wG g : ℂ)) Θ φ)
        (thetaLiftW (fun g => (wG g : ℂ)) Θ φ) ≠ 0 :=
      (wip_self_eq_zero_iff hwH _).not.mpr hne
    rw [wip_self_eq_sum_normSq, Complex.ofReal_ne_zero] at hneq0
    have hnn : 0 ≤ ∑ h : H, wH h * ‖thetaLiftW (fun g => (wG g : ℂ)) Θ φ h‖ ^ 2 :=
      Finset.sum_nonneg fun h _ => mul_nonneg (hwH h).le (sq_nonneg _)
    exact lt_of_le_of_ne hnn (Ne.symm hneq0)
  · intro hpos h0
    rw [h0] at hpos
    simp at hpos

/-- **Direct Wiring into `RHDirect.RallisSeesaw.RallisInnerProductHyp`**:
whenever the doubling Gram operator `D = doublingGramOp Θ` acts on a submodule `S ≤ L²(G)` as
scalar multiplication by a doubling eigenvalue `Z = c * L * ∏ v ∈ Pset, Z_v`, then
`RallisInnerProductHyp (thetaLiftLin Θ) S Pset c L Z_loc` holds unconditionally — immediately
supplying `rallis_factor_nonneg_of_nonzero`, `rallis_normSq_scaling`, and
`rallis_lift_ne_zero_of_factor_ne_zero` from `RHDirect.RallisSeesaw`! -/
theorem rallisInnerProductHyp_of_doubling_eigen {G H P : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (S : Submodule ℂ (EuclideanSpace ℂ G))
    (Pset : Finset P) (c L : ℂ) (Z_loc : P → ℂ)
    (hD : ∀ φ ∈ S, doublingGramOp Θ φ = (c * L * ∏ v ∈ Pset, Z_loc v) • φ) :
    RallisInnerProductHyp (thetaLiftLin Θ) S Pset c L Z_loc := by
  intro x hx y hy
  calc inner ℂ (thetaLiftLin Θ x) (thetaLiftLin Θ y)
      = inner ℂ x (doublingGramOp Θ y) := (concreteThetaSeesawPair Θ).adjoint_eq x (thetaLiftLin Θ y)
    _ = inner ℂ x ((c * L * ∏ v ∈ Pset, Z_loc v) • y) := by rw [hD y hy]
    _ = (c * L * ∏ v ∈ Pset, Z_loc v) * inner ℂ x y := inner_smul_right _ _ _

/-- **Consequence via `RHDirect.RallisSeesaw`**:
under a doubling eigenform identity `D φ = (c * L * ∏ Z_v) • φ` on `S`, for every nonzero `φ ∈ S`:
1. The doubling eigenvalue `α = c * L * ∏ Z_v` is real and non-negative (`0 ≤ Re α`, `Im α = 0`),
2. `‖θ(φ)‖² = Re(α) · ‖φ‖²`, and
3. `α ≠ 0 → θ(φ) ≠ 0`! -/
theorem doubling_eigen_rallis_positivity_and_nonvanishing {G H P : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (S : Submodule ℂ (EuclideanSpace ℂ G))
    (Pset : Finset P) (c L : ℂ) (Z_loc : P → ℂ)
    (hD : ∀ φ ∈ S, doublingGramOp Θ φ = (c * L * ∏ v ∈ Pset, Z_loc v) • φ)
    {φ : EuclideanSpace ℂ G} (hφ : φ ∈ S) (hφ0 : φ ≠ 0) :
    (0 ≤ (c * L * ∏ v ∈ Pset, Z_loc v).re ∧ (c * L * ∏ v ∈ Pset, Z_loc v).im = 0) ∧
    ‖thetaLiftLin Θ φ‖ ^ 2 = (c * L * ∏ v ∈ Pset, Z_loc v).re * ‖φ‖ ^ 2 ∧
    (c * L * ∏ v ∈ Pset, Z_loc v ≠ 0 → thetaLiftLin Θ φ ≠ 0) := by
  have hHyp := rallisInnerProductHyp_of_doubling_eigen Θ S Pset c L Z_loc hD
  exact ⟨rallis_factor_nonneg_of_nonzero hHyp hφ hφ0,
    rallis_normSq_scaling hHyp hφ,
    rallis_lift_ne_zero_of_factor_ne_zero hHyp hφ hφ0⟩

/-- **Concrete Definite Dual-Pair Tower Bridge into `RHDirect.RallisSeesaw.downChain`**:
for a chain of finite theta-lift kernels `Θ j : G j → G (j + 1) → ℂ` whose downward adjoints
`T j := thetaLiftAdjLin (Θ j)` satisfy the step-wise doubling eigenvalue identity
`doublingGramOp (Θ j) φ = Z j • φ` on `S j` with `thetaLiftLin (Θ j) (S j) ⊆ S (j + 1)`,
the `m`-step upward lift `(downChain T m)*` satisfies:
1. Exact multiplicative Petersson norm-square recursion `‖lift_m φ‖² = (∏ j < m, Re(Z j)) * ‖φ‖²`,
2. Exact inductive nonvanishing along every stage `0 ≤ j ≤ m` whenever `Z j ≠ 0`! -/
theorem concrete_doubling_tower_nonvanishing
    {G : ℕ → Type*} [∀ j, Fintype (G j)]
    (Θ : ∀ j, G j → G (j + 1) → ℂ)
    (S : ∀ j, Submodule ℂ (EuclideanSpace ℂ (G j)))
    (Z : ℕ → ℂ)
    (hstep : ∀ j, ∀ φ ∈ S j, doublingGramOp (Θ j) φ = Z j • φ)
    (hS : ∀ j, ∀ φ ∈ S j, thetaLiftLin (Θ j) φ ∈ S (j + 1))
    (m : ℕ) (hZ : ∀ j < m, Z j ≠ 0)
    {φ : EuclideanSpace ℂ (G 0)} (hφ : φ ∈ S 0) (hφ0 : φ ≠ 0) :
    ‖LinearMap.adjoint (downChain (E := fun i => EuclideanSpace ℂ (G i))
        (fun i => thetaLiftAdjLin (Θ i)) m) φ‖ ^ 2 =
      (∏ j ∈ Finset.range m, (Z j).re) * ‖φ‖ ^ 2 ∧
    (∀ k ≤ m,
      LinearMap.adjoint (downChain (E := fun i => EuclideanSpace ℂ (G i))
        (fun i => thetaLiftAdjLin (Θ i)) k) φ ∈ S k ∧
      LinearMap.adjoint (downChain (E := fun i => EuclideanSpace ℂ (G i))
        (fun i => thetaLiftAdjLin (Θ i)) k) φ ≠ 0) := by
  have hadj : ∀ j, LinearMap.adjoint (thetaLiftAdjLin (Θ j)) = thetaLiftLin (Θ j) := fun j => by
    rw [thetaLiftAdjLin_eq_adjoint, LinearMap.adjoint_adjoint]
  have hstep' : ∀ j, ∀ x ∈ S j,
      thetaLiftAdjLin (Θ j) (LinearMap.adjoint (thetaLiftAdjLin (Θ j)) x) = Z j • x := by
    intro j x hx
    rw [hadj j]
    exact hstep j x hx
  have hS' : ∀ j, ∀ x ∈ S j, LinearMap.adjoint (thetaLiftAdjLin (Θ j)) x ∈ S (j + 1) := by
    intro j x hx
    rw [hadj j]
    exact hS j x hx
  exact ⟨chain_normSq_recursion (E := fun i => EuclideanSpace ℂ (G i))
      (fun i => thetaLiftAdjLin (Θ i)) S Z hstep' hS' m hφ,
    definite_chain_nonvanishing (E := fun i => EuclideanSpace ℂ (G i))
      (fun i => thetaLiftAdjLin (Θ i)) S Z hstep' hS' m hZ hφ hφ0⟩

/-- **Direct Wiring of Concrete Finite Doubling Spaces into `RHDirect.SiegelWeilCore.DoublingZetaForm`**:
any finite family of self-dual lattices/test vectors whose doubling Gram values `⟨φ, D φ⟩` are
related by nonzero transfer units packages directly into `SiegelWeilCore.DoublingZetaForm`,
transferring nonvanishing from a single nonzero theta lift `θ(φ₀) ≠ 0` to every self-dual
member of the genus! -/
def concreteDoublingZetaForm {G H Lat : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (IsSelfDual : Lat → Prop) (vec : Lat → EuclideanSpace ℂ G)
    (htransfer : ∀ L₁ L₂, IsSelfDual L₁ → IsSelfDual L₂ →
      ∃ u : ℂ, u ≠ 0 ∧
        inner ℂ (vec L₂) (doublingGramOp Θ (vec L₂)) =
          u * inner ℂ (vec L₁) (doublingGramOp Θ (vec L₁))) :
    DoublingZetaForm Lat where
  IsSelfDual := IsSelfDual
  zetaVal L := inner ℂ (vec L) (doublingGramOp Θ (vec L))
  transfer_factor := htransfer

theorem concreteDoublingZetaForm_theta_ne_zero {G H Lat : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (IsSelfDual : Lat → Prop) (vec : Lat → EuclideanSpace ℂ G)
    (htransfer : ∀ L₁ L₂, IsSelfDual L₁ → IsSelfDual L₂ →
      ∃ u : ℂ, u ≠ 0 ∧
        inner ℂ (vec L₂) (doublingGramOp Θ (vec L₂)) =
          u * inner ℂ (vec L₁) (doublingGramOp Θ (vec L₁)))
    (L₀ : Lat) (hL₀ : IsSelfDual L₀) (hLift₀ : thetaLiftLin Θ (vec L₀) ≠ 0) :
    ∀ L : Lat, IsSelfDual L → thetaLiftLin Θ (vec L) ≠ 0 := by
  let Z : DoublingZetaForm Lat := concreteDoublingZetaForm Θ IsSelfDual vec htransfer
  have hZ₀ : Z.zetaVal L₀ ≠ 0 :=
    ((concreteThetaSeesawPair Θ).lift_ne_zero_iff (vec L₀)).mp hLift₀
  intro L hL
  have hZL : Z.zetaVal L ≠ 0 := Z.ne_zero_of_frameLat L₀ hL₀ hZ₀ L hL
  exact ((concreteThetaSeesawPair Θ).lift_ne_zero_iff (vec L)).mpr hZL

/-- **Direct Wiring of the Unconditional `E₈` Siegel–Weil Identity (`Θ_{E₈} = E₄`) into
`RHDirect.SiegelWeilCore.SiegelEisensteinDecomp` (`0` Assumptions!)**:
decomposes `E₄(τ) = 1 + 0 + 240 ∑_{n ≥ 1} σ₃(n) q^n` into its constant term `c₀ = 1` and
Fourier tail, proving `SiegelEisensteinDecomp.MatchesThetaMean` against the `E₈` theta series
on the singleton genus `Unit` (`O(E₈)` class number `1`)! -/
def E8SiegelEisensteinDecomp : SiegelEisensteinDecomp UpperHalfPlane where
  c0 _ := 1
  c1 _ := 0
  tail τ := 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 (n : ℕ) : ℂ) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℕ) : ℂ) * (τ : ℂ))

theorem E8SiegelEisensteinDecomp_matches_thetaMean :
    E8SiegelEisensteinDecomp.MatchesThetaMean
      (Measure.dirac ()) (1 : ℝ) (fun τ _ => complexLatticeTheta E8Lattice τ) := by
  intro τ
  unfold SiegelEisensteinDecomp.eval E8SiegelEisensteinDecomp thetaMean
  rw [inv_one, one_smul, integral_dirac, add_zero]
  dsimp only
  rw [complexLatticeTheta_E8Lattice_eq_E4 τ]
  rfl

end RallisPositivityAndBridge

end

end RHDirect.Stage11DoublingRallis
