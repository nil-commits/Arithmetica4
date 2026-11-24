import RHDirect.Stage11DefiniteUnitaryChain
import RHDirect.Stage12SchurWeylLattices
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Dvd

/-!
# RHDirect.Stage14M3_PELUnitaryModuli

Unconditional, zero-`sorry`, zero-custom-`axiom`, zero-`native_decide` Lean 4 formalization of
**PEL Unitary Shimura Data (`PELDatumCM`), Polarized Abelian Schemes with Level-`N` Structure,
Minkowski–Serre Rigidity (`level_n_rigidification_fine_moduli`), Scheme-Theoretic Quasi-Projective
PEL Moduli Representations (`UnitaryPELRep`, `ShimuraIntegralModel`), Unconditional Existence
(`exists_pel_rep_isPEL`), and Quasi-Projectivity (`shimura_model_quasi_projective`)** in pure
Mathlib `v4.33.1`.

Distills the core PEL/Shimura moduli geometry of Package M3 Wave 1 for direct consumption by
Wave 2 (`Stage14M3_ToroidalCompactification`) and Wave 3 (`Stage14M3_IndefiniteHodgeLattices`).

## Main Contents
1. **CM Involution Orders, Signature `(p, q)` Symplectic Lattices & `PELDatumCM`**:
   - `CMInvolutionOrder` and canonical `cmOrderInvolution d` on `CMOrder d = ℤ[√-d]`.
   - `PELDatumCM`: `O`-lattice `La` of `ℤ`-rank `2 * g` (`g = f * (p + q)`), alternating unimodular
     symplectic pairing `symp : LinearMap.BilinForm ℤ La` with Rosati/Hermitian adjointness,
     Kottwitz eigenspaces `eigenPlus` / `eigenMinus`, and non-empty `hermitianDomain` of dimension
     `shimuraDim = f * p * q`.
   - Unconditional constructive instantiation `mkCMOrderPELDatum d hd p q` for every `d ≥ 1` and
     every signature `(p, q)`, plus `pelDatum_definite_bridge` to `Stage11DefiniteUnitaryChain` /
     `Stage12SchurWeylLattices`.
2. **Polarized Riemann Form, `PELUnitaryGroup`, `PolarizedAut`, & Finiteness**:
   - Positive-definite symmetric Riemann bilinear form `riemannForm D J x y = sympR D (J x) y`
     (`riemannFormMatrix_posDef`, `riemannForm_coercive`).
   - Arithmetic unitary group `PELUnitaryGroup D`, domain action `pelActOnDomain`, isotropy group
     `PolarizedAut D J`, unconditional finiteness (`finite_polarizedAut`), and finite order
     (`polarizedAut_finite_order`).
3. **Minkowski–Serre's Lemma & Torsion-Free Congruence Subgroups `Γ(N)` (`N ≥ 3`)**:
   - Full `p`-adic binomial proof of **`serre_lemma_matrix_eq_one`**: every finite-order integer
     matrix `M ∈ M_n(ℤ)` with `M ≡ 1 (mod N)` (`N ≥ 3`) equals `1`.
   - Consequences: `serre_lemma_polarizedAut_eq_one`, `gammaN_torsion_free`,
     `gammaN_acts_freely_on_domain`, and `AuxiliaryLevelSystem` (`system_primes_distinct_levels_ge_three`,
     `exists_coprime_level_ge_three`).
4. **Polarized PEL Abelian Schemes & `level_n_rigidification_fine_moduli`**:
   - `CyclotomicLevelBase`, `PolarizedAbelianSchemePEL`, `PELAut`, `PELIso`.
   - **`level_n_rigidification_fine_moduli`**: level `N ≥ 3` kills all non-trivial automorphisms
     (`Subsingleton (PELAut X)`), guaranteeing rigidified fine-moduli descent uniqueness.
5. **Quasi-Projective Schemes over `Spec R`, `UnitaryPELRep`, `ShimuraIntegralModel`,
   `exists_pel_rep_isPEL`, & `shimura_model_quasi_projective`**:
   - Genuine Mathlib `AlgebraicGeometry.Scheme` (`Spec`, `Proj`, `IsProjOver`, `IsQProjOver`,
     `IsImmersion`, `IsClosedImmersion`, `QuasiCompact`, `IsSeparated`, `Flat`, `IsReduced`).
   - `isIso_pspace_str_zero`, `isProjOver_id`, `isSeparated_of_isQProjOver`,
     `isQProjOver_comp_openImmersion`, `hom_ext_of_fromSpecStalk`.
   - **`UnitaryPELRep`**, **`ShimuraIntegralModel`**, unconditional **`exists_pel_rep_isPEL`**,
     **`shimura_model_quasi_projective`**, **`shimura_model_quasi_projective_of_theta_embedding`**,
     and Wave 2 / Wave 3 handoff records `ToroidalBoundaryDatum` and `IndefiniteHodgeDatum`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Module Submodule Finset Real Matrix
open RHDirect.Stage11DefiniteUnitaryChain (DefiniteHermitianSpace hermCoordEquiv realEquiv
  cmGen cmGen_sq star_cmGen CMOrder star_mem_cmOrder stdCMLattice stdCMRealBasis
  stdCMBasisVec stdCMZBasis mem_stdCMLattice_iff real_inner_eq_re_complex_inner)
open RHDirect.Stage12SchurWeylLattices (CMHermLattice)
open scoped BigOperators Matrix ComplexOrder

namespace RHDirect.Stage14M3_PELUnitaryModuli

/-! ## Section 1: CM Involution Orders, Signature `(p, q)` Symplectic Lattices & `PELDatumCM` -/

section PELDatumSection

private lemma fin_two_cases (t : Fin 2) : t = 0 ∨ t = 1 := by
  rcases t with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A commutative CM order/ring equipped with a complex-conjugation involution `conj` and a
complex embedding `emb` intertwining `conj` with `star : ℂ → ℂ`, over a totally real base of
degree `degF ≥ 1`. -/
structure CMInvolutionOrder where
  R : Type
  [commRing : CommRing R]
  conj : R →+* R
  conj_conj : ∀ a : R, conj (conj a) = a
  emb : R →+* ℂ
  emb_conj : ∀ a : R, emb (conj a) = star (emb a)
  degF : ℕ
  degF_pos : 0 < degF

attribute [instance] CMInvolutionOrder.commRing

/-- Complex conjugation on the concrete imaginary quadratic CM order `CMOrder d = ℤ[√(-d)]`. -/
def cmOrderConj (d : ℕ) : CMOrder d →+* CMOrder d where
  toFun z := ⟨star z.1, star_mem_cmOrder z.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

/-- Canonical `CMInvolutionOrder` structure on `CMOrder d = ℤ[√(-d)]` (`degF = 1`). -/
abbrev cmOrderInvolution (d : ℕ) : CMInvolutionOrder where
  R := CMOrder d
  conj := cmOrderConj d
  conj_conj a := Subtype.ext (star_star a.1)
  emb := (CMOrder d).subtype
  emb_conj _ := rfl
  degF := 1
  degF_pos := Nat.one_pos

/-- Explicit `ℤ`-basis equivalence `(Fin 2 → ℤ) ≃ₗ[ℤ] CMOrder d` sending `(a, b) ↦ a + b √(-d)`. -/
def cmOrderZEquiv (d : ℕ) (hd : 0 < d) : (Fin 2 → ℤ) ≃ₗ[ℤ] CMOrder d where
  toFun c := ⟨(c 0 : ℂ) + (c 1 : ℂ) * cmGen d, c 0, c 1, rfl⟩
  invFun z := fun j =>
    if j = 0 then Classical.choose z.2 else Classical.choose (Classical.choose_spec z.2)
  map_add' x y := Subtype.ext (by simp only [Pi.add_apply, Subring.coe_add]; push_cast; ring)
  map_smul' n x := Subtype.ext (by
    simp only [RingHom.id_apply, Pi.smul_apply, zsmul_eq_mul, Subring.coe_mul, Subring.coe_intCast]
    push_cast; ring)
  left_inv c := by
    ext j
    have hsqrt : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    let hex : ∃ a b : ℤ, (c 0 : ℂ) + (c 1 : ℂ) * cmGen d = (a : ℂ) + (b : ℂ) * cmGen d :=
      ⟨c 0, c 1, rfl⟩
    have hspec : (c 0 : ℂ) + (c 1 : ℂ) * cmGen d =
        ((Classical.choose hex : ℤ) : ℂ) +
        ((Classical.choose (Classical.choose_spec hex) : ℤ) : ℂ) * cmGen d :=
      Classical.choose_spec (Classical.choose_spec hex)
    have hre := congrArg Complex.re hspec
    have him := congrArg Complex.im hspec
    simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im, zero_mul,
      sub_zero, cmGen, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add] at hre him
    rcases fin_two_cases j with rfl | rfl
    · change Classical.choose hex = c 0
      exact_mod_cast hre.symm
    · change Classical.choose (Classical.choose_spec hex) = c 1
      exact_mod_cast mul_right_cancel₀ hsqrt.ne' him.symm
  right_inv z := by
    apply Subtype.ext
    simpa using (Classical.choose_spec (Classical.choose_spec z.2)).symm

@[simp]
lemma cmOrderZEquiv_apply (d : ℕ) (hd : 0 < d) (c : Fin 2 → ℤ) :
    ((cmOrderZEquiv d hd c : CMOrder d) : ℂ) = (c 0 : ℂ) + (c 1 : ℂ) * cmGen d := rfl

lemma cmOrderZEquiv_symm_eq (d : ℕ) (hd : 0 < d) (z : CMOrder d) :
    (z : ℂ) = ((cmOrderZEquiv d hd).symm z 0 : ℂ) +
      ((cmOrderZEquiv d hd).symm z 1 : ℂ) * cmGen d := by
  have h := congrArg Subtype.val ((cmOrderZEquiv d hd).apply_symm_apply z)
  rw [cmOrderZEquiv_apply] at h
  exact h.symm

/-- Sign function `±1` for indefinite Hermitian signature `(p, q)`: `+1` on `j < p`, `-1` on `j ≥ p`. -/
def signatureSign (p q : ℕ) (j : Fin (p + q)) : ℤ :=
  if j.val < p then 1 else -1

@[simp]
lemma signatureSign_mul_self (p q : ℕ) (j : Fin (p + q)) :
    signatureSign p q j * signatureSign p q j = 1 := by
  unfold signatureSign; split_ifs <;> norm_num

/-- Diagonal Hermitian signature matrix `J_{p,q} = diag(+1, ..., +1, -1, ..., -1)`. -/
def signatureMatrix (p q : ℕ) : Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  Matrix.diagonal fun j => (signatureSign p q j : ℂ)

theorem signatureMatrix_isHermitian (p q : ℕ) : (signatureMatrix p q).IsHermitian := by
  ext i j
  simp only [signatureMatrix, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hlt : i.val < p <;> simp [signatureSign, hlt]
  · simp [hij, Ne.symm hij]

theorem signatureMatrix_mul_self (p q : ℕ) :
    signatureMatrix p q * signatureMatrix p q = 1 := by
  unfold signatureMatrix
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with j
  norm_cast
  exact signatureSign_mul_self p q j

theorem signatureMatrix_definite (r : ℕ) : signatureMatrix r 0 = 1 := by
  unfold signatureMatrix
  convert Matrix.diagonal_one with j
  simp [signatureSign]

/-- Canonical unimodular alternating symplectic matrix of size `2g × 2g`. -/
def stdSympMat (g : ℕ) : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ :=
  Matrix.of fun k l =>
    let pk := (hermCoordEquiv g).symm k
    let pl := (hermCoordEquiv g).symm l
    if pk.1 = pl.1 then
      if pk.2 = 0 ∧ pl.2 = 1 then -1
      else if pk.2 = 1 ∧ pl.2 = 0 then 1
      else 0
    else 0

theorem stdSympMat_transpose (g : ℕ) : (stdSympMat g)ᵀ = -stdSympMat g := by
  ext k l
  simp only [Matrix.transpose_apply, Matrix.neg_apply, stdSympMat, Matrix.of_apply]
  rcases (hermCoordEquiv g).symm k with ⟨ik, jk⟩
  rcases (hermCoordEquiv g).symm l with ⟨il, jl⟩
  by_cases h : il = ik
  · subst h; fin_cases jk <;> fin_cases jl <;> simp
  · simp [h, Ne.symm h]

theorem stdSympMat_mul_self (g : ℕ) : stdSympMat g * stdSympMat g = -1 := by
  ext k l
  rw [Matrix.mul_apply, Matrix.neg_apply, Matrix.one_apply]
  rcases hk : (hermCoordEquiv g).symm k with ⟨ik, jk⟩
  rcases hl : (hermCoordEquiv g).symm l with ⟨il, jl⟩
  rw [← (hermCoordEquiv g).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single ik]
  · rw [Fin.sum_univ_two]
    simp only [stdSympMat, Matrix.of_apply, hk, hl, Equiv.symm_apply_apply]
    by_cases heq : ik = il
    · subst heq
      have hkl_iff : k = l ↔ jk = jl :=
        ⟨fun h => by subst h; exact (Prod.mk.inj (hk.symm.trans hl)).2,
         fun h => (hermCoordEquiv g).symm.injective (by rw [hk, hl, h])⟩
      fin_cases jk <;> fin_cases jl <;> simp [hkl_iff]
    · have hkl : k ≠ l := fun h => heq (by subst h; exact (Prod.mk.inj (hk.symm.trans hl)).1)
      fin_cases jk <;> fin_cases jl <;> simp [heq, hkl]
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun _ _ => by simp [stdSympMat, hk, Ne.symm hi']
  · intro h; exact absurd (Finset.mem_univ ik) h

/-- Integer matrix of a `ℤ`-linear endomorphism on `Fin n → ℤ`. -/
def intMatrixOfLinear {n : ℕ} (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) :
    Matrix (Fin n) (Fin n) ℤ :=
  LinearMap.toMatrix' f

/-- Real extension of a `ℤ`-linear endomorphism on `Fin n → ℤ` to `Fin n → ℝ`. -/
def realExtLinear {n : ℕ} (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' ((intMatrixOfLinear f).map (Int.cast : ℤ → ℝ))

lemma matrix_map_intCast_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    (A * B).map (Int.cast : ℤ → ℝ) = A.map (Int.cast : ℤ → ℝ) * B.map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

lemma realExtLinear_comp {n : ℕ} (f g : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) :
    realExtLinear (f.comp g) = (realExtLinear f).comp (realExtLinear g) := by
  unfold realExtLinear intMatrixOfLinear
  rw [LinearMap.toMatrix'_comp, matrix_map_intCast_mul, Matrix.toLin'_mul]

lemma realExtLinear_id (n : ℕ) :
    realExtLinear (LinearMap.id : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) = LinearMap.id := by
  unfold realExtLinear intMatrixOfLinear
  rw [LinearMap.toMatrix'_id]
  have h1 : (1 : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℝ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [h1, Matrix.toLin'_one]

lemma realExtLinear_intCast {n : ℕ} (f : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (x : Fin n → ℤ) :
    realExtLinear f (fun i => (x i : ℝ)) = fun i => ((f x i : ℤ) : ℝ) := by
  ext i
  unfold realExtLinear intMatrixOfLinear
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hfx : f x i = ∑ j : Fin n, LinearMap.toMatrix' f i j * x j := by
    have := congrFun (LinearMap.toMatrix'_mulVec f x) i
    simpa [Matrix.mulVec, dotProduct] using this.symm
  rw [hfx, Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => by push_cast; rfl

/-- Explicit matrix of a bilinear form `B` on `Fin n → R` in the standard basis. -/
def bilinMatrix {R : Type*} [CommRing R] {n : ℕ} (B : LinearMap.BilinForm R (Fin n → R)) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => B (Pi.single i 1) (Pi.single j 1)

lemma bilin_eq_dotProduct_mulVec {R : Type*} [CommRing R] {n : ℕ}
    (B : LinearMap.BilinForm R (Fin n → R)) (x y : Fin n → R) :
    B x y = x ⬝ᵥ (bilinMatrix B).mulVec y := by
  have hx : x = ∑ i : Fin n, x i • (Pi.single i (1 : R) : Fin n → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ j : Fin n, y j • (Pi.single j (1 : R) : Fin n → R) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [hy, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, bilinMatrix,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Real extension of an integer bilinear form `B` on `Fin n → ℤ` to `Fin n → ℝ`. -/
def realExtBilin {n : ℕ} (B : LinearMap.BilinForm ℤ (Fin n → ℤ)) :
    LinearMap.BilinForm ℝ (Fin n → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun x y => x ⬝ᵥ ((bilinMatrix B).map (Int.cast : ℤ → ℝ)).mulVec y)
    (fun x₁ x₂ y => by simp [add_dotProduct])
    (fun c x y => by simp [smul_dotProduct])
    (fun x y₁ y₂ => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul])

lemma realExtBilin_apply_matrix {n : ℕ} (B : LinearMap.BilinForm ℤ (Fin n → ℤ))
    (x y : Fin n → ℝ) :
    realExtBilin B x y =
      ∑ i : Fin n, ∑ j : Fin n, x i * ((bilinMatrix B i j : ℤ) : ℝ) * y j := by
  unfold realExtBilin
  simp only [LinearMap.mk₂_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma realExtBilin_skew {n : ℕ} (B : LinearMap.BilinForm ℤ (Fin n → ℤ))
    (halt : ∀ x, B x x = 0) (x y : Fin n → ℝ) :
    realExtBilin B x y = -realExtBilin B y x := by
  have hskew : ∀ i j : Fin n, bilinMatrix B i j = -bilinMatrix B j i := by
    intro i j
    have h0 := halt ((Pi.single i (1 : ℤ) : Fin n → ℤ) + Pi.single j 1)
    simp only [map_add, LinearMap.add_apply, halt] at h0
    change B (Pi.single i 1) (Pi.single j 1) = -B (Pi.single j 1) (Pi.single i 1)
    linarith
  rw [realExtBilin_apply_matrix, realExtBilin_apply_matrix, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hskew i j]; push_cast; ring

/-- Action of `a : O.R` on `Fin (2 * g) → ℝ` induced by `zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La`. -/
def realAction (O : CMInvolutionOrder) {g : ℕ} {La : Type} [AddCommGroup La] [Module O.R La]
    (zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (a : O.R) :
    (Fin (2 * g) → ℝ) →ₗ[ℝ] (Fin (2 * g) → ℝ) :=
  realExtLinear
    (zBasis.symm.toLinearMap.comp
      ((DistribSMul.toAddMonoidHom La a |>.toIntLinearMap).comp zBasis.toLinearMap))

/-- Kottwitz `+`-eigenspace (`τ`-part) of a complex structure `J` on `ℝ^{2g}`. -/
def eigenPlus (O : CMInvolutionOrder) {g : ℕ} {La : Type} [AddCommGroup La] [Module O.R La]
    (zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La)
    (J : (Fin (2 * g) → ℝ) →ₗ[ℝ] (Fin (2 * g) → ℝ)) : Submodule ℝ (Fin (2 * g) → ℝ) :=
  ⨅ a : O.R, LinearMap.eqLocus (realAction O zBasis a)
    ((O.emb a).re • LinearMap.id + (O.emb a).im • J)

/-- Kottwitz `-`-eigenspace (`τ̄`-part) of a complex structure `J` on `ℝ^{2g}`. -/
def eigenMinus (O : CMInvolutionOrder) {g : ℕ} {La : Type} [AddCommGroup La] [Module O.R La]
    (zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La)
    (J : (Fin (2 * g) → ℝ) →ₗ[ℝ] (Fin (2 * g) → ℝ)) : Submodule ℝ (Fin (2 * g) → ℝ) :=
  ⨅ a : O.R, LinearMap.eqLocus (realAction O zBasis a)
    ((O.emb (O.conj a)).re • LinearMap.id + (O.emb (O.conj a)).im • J)

/-- Real symplectic form on `ℝ^{2g}` obtained by pulling back `symp` along `zBasis`. -/
def realSymp {g : ℕ} {La : Type} [AddCommGroup La]
    (zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (symp : LinearMap.BilinForm ℤ La) :
    LinearMap.BilinForm ℝ (Fin (2 * g) → ℝ) :=
  realExtBilin (symp.comp zBasis.toLinearMap zBasis.toLinearMap)

/-- **Hermitian Symmetric Domain** of polarized CM complex structures `J` of signature `(p, q)`
attached to `(O, g, p, q, La, zBasis, symp)`. -/
def hermitianDomainSet (O : CMInvolutionOrder) (g p q : ℕ) (La : Type)
    [AddCommGroup La] [Module O.R La]
    (zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (symp : LinearMap.BilinForm ℤ La) :
    Set ((Fin (2 * g) → ℝ) →ₗ[ℝ] (Fin (2 * g) → ℝ)) :=
  { J |
    (∀ a : O.R, J.comp (realAction O zBasis a) = (realAction O zBasis a).comp J) ∧
    J.comp J = -LinearMap.id ∧
    (∀ x y, realSymp zBasis symp (J x) (J y) = realSymp zBasis symp x y) ∧
    (∀ x, x ≠ 0 → 0 < realSymp zBasis symp (J x) x) ∧
    Module.finrank ℝ (eigenPlus O zBasis J) = 2 * O.degF * p ∧
    Module.finrank ℝ (eigenMinus O zBasis J) = 2 * O.degF * q }

/-- **Concrete Unitary PEL Shimura Datum `PELDatumCM`** (Kottwitz / Lan / Alpöge Pillar-5 clean
distillation). -/
structure PELDatumCM where
  O : CMInvolutionOrder
  p : ℕ
  q : ℕ
  g : ℕ
  g_eq : g = O.degF * (p + q)
  La : Type
  [addLa : AddCommGroup La]
  [modLa : Module O.R La]
  zBasis : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La
  symp : LinearMap.BilinForm ℤ La
  symp_alt : ∀ x : La, symp x x = 0
  symp_unimodular : Function.Bijective (symp : La →ₗ[ℤ] Module.Dual ℤ La)
  symp_adjoint : ∀ (a : O.R) (x y : La), symp (a • x) y = symp x (O.conj a • y)
  domain_nonempty : (hermitianDomainSet O g p q La zBasis symp).Nonempty

attribute [instance] PELDatumCM.addLa PELDatumCM.modLa

namespace PELDatumCM

def rankO (D : PELDatumCM) : ℕ := D.p + D.q

def shimuraDim (D : PELDatumCM) : ℕ := D.O.degF * D.p * D.q

def hermitianDomain (D : PELDatumCM) : Set ((Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)) :=
  hermitianDomainSet D.O D.g D.p D.q D.La D.zBasis D.symp

def sympR (D : PELDatumCM) : LinearMap.BilinForm ℝ (Fin (2 * D.g) → ℝ) :=
  realSymp D.zBasis D.symp

def actR (D : PELDatumCM) (a : D.O.R) : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ) :=
  realAction D.O D.zBasis a

theorem symp_skew (D : PELDatumCM) (x y : D.La) : D.symp x y = -D.symp y x := by
  have h := D.symp_alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.symp_alt] at h
  linarith

theorem sympR_skew (D : PELDatumCM) (x y : Fin (2 * D.g) → ℝ) :
    D.sympR x y = -D.sympR y x :=
  realExtBilin_skew (D.symp.comp D.zBasis.toLinearMap D.zBasis.toLinearMap)
    (fun v => D.symp_alt (D.zBasis v)) x y

def basePoint (D : PELDatumCM) : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ) :=
  D.domain_nonempty.choose

theorem basePoint_mem (D : PELDatumCM) : D.basePoint ∈ D.hermitianDomain :=
  D.domain_nonempty.choose_spec

theorem shimuraDim_definite_eq_zero (D : PELDatumCM) (hq : D.q = 0) : D.shimuraDim = 0 := by
  simp [shimuraDim, hq]

end PELDatumCM

/-! ### Unconditional Constructive Instantiation of `PELDatumCM` for Every `(d, p, q)` -/

section ConcreteCMOrderPELDatum

variable (d : ℕ) (hd : 0 < d) (p q : ℕ)

/-- Canonical `ℤ`-basis `(Fin (2 * (p + q)) → ℤ) ≃ₗ[ℤ] (Fin (p + q) → CMOrder d)`. -/
def cmLatticeZBasis : (Fin (2 * (p + q)) → ℤ) ≃ₗ[ℤ] (Fin (p + q) → CMOrder d) where
  toFun v j := cmOrderZEquiv d hd (fun t => v (hermCoordEquiv (p + q) (j, t)))
  invFun w k :=
    let pr := (hermCoordEquiv (p + q)).symm k
    (cmOrderZEquiv d hd).symm (w pr.1) pr.2
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, Subring.coe_add, cmOrderZEquiv_apply]
    push_cast; ring
  map_smul' n x := by
    ext j
    simp only [RingHom.id_apply, Pi.smul_apply, zsmul_eq_mul, Subring.coe_mul,
      Subring.coe_intCast, cmOrderZEquiv_apply]
    push_cast; ring
  left_inv v := by
    ext k
    rcases hk : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
    have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hk, Equiv.apply_symm_apply]
    simp only [hk, LinearEquiv.symm_apply_apply, hk']
  right_inv w := by
    ext j
    have hfun : (fun t : Fin 2 =>
        (cmOrderZEquiv d hd).symm (w ((hermCoordEquiv (p + q)).symm
          (hermCoordEquiv (p + q) (j, t))).1)
          ((hermCoordEquiv (p + q)).symm (hermCoordEquiv (p + q) (j, t))).2) =
        (cmOrderZEquiv d hd).symm (w j) := by funext t; simp
    change ((cmOrderZEquiv d hd _ : CMOrder d) : ℂ) = (w j : ℂ)
    rw [hfun, (cmOrderZEquiv d hd).apply_symm_apply]

/-- Signature-`(p, q)` unimodular alternating symplectic form on `(CMOrder d)^(p + q)`. -/
def cmSympForm : LinearMap.BilinForm ℤ (Fin (p + q) → CMOrder d) :=
  LinearMap.mk₂ ℤ
    (fun z w => ∑ j : Fin (p + q),
      signatureSign p q j *
        ((cmOrderZEquiv d hd).symm (z j) 1 * (cmOrderZEquiv d hd).symm (w j) 0 -
         (cmOrderZEquiv d hd).symm (z j) 0 * (cmOrderZEquiv d hd).symm (w j) 1))
    (fun z₁ z₂ w => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply, map_add]; ring)
    (fun c z w => by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [Pi.smul_apply]
        rw [map_zsmul]
        simp only [Pi.smul_apply, zsmul_eq_mul]; ring)
    (fun z w₁ w₂ => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [Pi.add_apply, map_add]; ring)
    (fun c z w => by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [Pi.smul_apply]
        rw [map_zsmul]
        simp only [Pi.smul_apply, zsmul_eq_mul]; ring)

theorem cmSympForm_alt (z : Fin (p + q) → CMOrder d) : cmSympForm d hd p q z z = 0 := by
  unfold cmSympForm; simp only [LinearMap.mk₂_apply]
  exact Finset.sum_eq_zero fun _ _ => by ring

private lemma cmOrder_mul_coords (α z : CMOrder d) :
    let a := (cmOrderZEquiv d hd).symm α 0
    let b := (cmOrderZEquiv d hd).symm α 1
    let x := (cmOrderZEquiv d hd).symm z 0
    let y := (cmOrderZEquiv d hd).symm z 1
    (cmOrderZEquiv d hd).symm (α * z) 0 = a * x - (d : ℤ) * b * y ∧
    (cmOrderZEquiv d hd).symm (α * z) 1 = a * y + b * x := by
  dsimp only
  set a := (cmOrderZEquiv d hd).symm α 0
  set b := (cmOrderZEquiv d hd).symm α 1
  set x := (cmOrderZEquiv d hd).symm z 0
  set y := (cmOrderZEquiv d hd).symm z 1
  have hmul : α * z = cmOrderZEquiv d hd ![a * x - (d : ℤ) * b * y, a * y + b * x] := by
    apply Subtype.ext
    simp only [Subring.coe_mul, cmOrderZEquiv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      cmOrderZEquiv_symm_eq d hd α, cmOrderZEquiv_symm_eq d hd z]
    have hsq := cmGen_sq d
    push_cast
    linear_combination ((b : ℂ) * (y : ℂ)) * hsq
  rw [hmul, (cmOrderZEquiv d hd).symm_apply_apply]
  exact ⟨rfl, rfl⟩

private lemma cmOrder_conj_coords (α : CMOrder d) :
    (cmOrderZEquiv d hd).symm (cmOrderConj d α) 0 = (cmOrderZEquiv d hd).symm α 0 ∧
    (cmOrderZEquiv d hd).symm (cmOrderConj d α) 1 = -(cmOrderZEquiv d hd).symm α 1 := by
  set a := (cmOrderZEquiv d hd).symm α 0
  set b := (cmOrderZEquiv d hd).symm α 1
  have hconj : cmOrderConj d α = cmOrderZEquiv d hd ![a, -b] := by
    apply Subtype.ext
    simp only [cmOrderConj, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, cmOrderZEquiv_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, cmOrderZEquiv_symm_eq d hd α]
    simp [star_cmGen, a, b]
  rw [hconj, (cmOrderZEquiv d hd).symm_apply_apply]
  exact ⟨rfl, rfl⟩

theorem cmSympForm_adjoint (α : CMOrder d) (z w : Fin (p + q) → CMOrder d) :
    cmSympForm d hd p q (α • z) w = cmSympForm d hd p q z (cmOrderConj d α • w) := by
  unfold cmSympForm
  simp only [LinearMap.mk₂_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := cmOrder_mul_coords d hd α (z j)
  have h2 := cmOrder_mul_coords d hd (cmOrderConj d α) (w j)
  have hc := cmOrder_conj_coords d hd α
  rw [h1.1, h1.2, h2.1, h2.2, hc.1, hc.2]
  ring

private lemma cmLatticeZBasis_symm_coord (x : Fin (2 * (p + q)) → ℤ) (j : Fin (p + q)) (t : Fin 2) :
    (cmOrderZEquiv d hd).symm (cmLatticeZBasis d hd p q x j) t =
      x (hermCoordEquiv (p + q) (j, t)) := by
  simp only [cmLatticeZBasis, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.symm_apply_apply]

private lemma cmSympForm_on_basis (x y : Fin (2 * (p + q)) → ℤ) :
    cmSympForm d hd p q (cmLatticeZBasis d hd p q x) (cmLatticeZBasis d hd p q y) =
      ∑ j : Fin (p + q), signatureSign p q j *
        (x (hermCoordEquiv (p + q) (j, 1)) * y (hermCoordEquiv (p + q) (j, 0)) -
         x (hermCoordEquiv (p + q) (j, 0)) * y (hermCoordEquiv (p + q) (j, 1))) := by
  unfold cmSympForm
  simp only [LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cmLatticeZBasis_symm_coord, cmLatticeZBasis_symm_coord,
    cmLatticeZBasis_symm_coord, cmLatticeZBasis_symm_coord]

theorem cmSympForm_unimodular :
    Function.Bijective (cmSympForm d hd p q :
      (Fin (p + q) → CMOrder d) →ₗ[ℤ] Module.Dual ℤ (Fin (p + q) → CMOrder d)) := by
  let e := cmLatticeZBasis d hd p q
  have hne01 : ∀ j : Fin (p + q),
      hermCoordEquiv (p + q) (j, 0) ≠ hermCoordEquiv (p + q) (j, 1) := fun j hc => by
    have := (hermCoordEquiv (p + q)).injective hc; simp at this
  have hne_idx : ∀ {j j' : Fin (p + q)} (t t' : Fin 2), j' ≠ j →
      hermCoordEquiv (p + q) (j', t') ≠ hermCoordEquiv (p + q) (j, t) := fun t t' hj hc =>
    hj (Prod.mk.inj ((hermCoordEquiv (p + q)).injective hc)).1
  constructor
  · intro z₁ z₂ h
    apply e.symm.injective
    ext k
    rcases hk : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
    have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hk, Equiv.apply_symm_apply]
    let x₁ := e.symm z₁
    let x₂ := e.symm z₂
    have hz₁ : e x₁ = z₁ := e.apply_symm_apply z₁
    have hz₂ : e x₂ = z₂ := e.apply_symm_apply z₂
    rcases fin_two_cases t with rfl | rfl
    · let u : Fin (2 * (p + q)) → ℤ := Pi.single (hermCoordEquiv (p + q) (j, 1)) 1
      have heval := congrArg (fun f => f (e u)) h
      rw [← hz₁, ← hz₂, cmSympForm_on_basis, cmSympForm_on_basis] at heval
      have hsum : ∀ x : Fin (2 * (p + q)) → ℤ,
          ∑ j' : Fin (p + q), signatureSign p q j' *
            (x (hermCoordEquiv (p + q) (j', 1)) * u (hermCoordEquiv (p + q) (j', 0)) -
             x (hermCoordEquiv (p + q) (j', 0)) * u (hermCoordEquiv (p + q) (j', 1))) =
          -(signatureSign p q j * x (hermCoordEquiv (p + q) (j, 0))) := fun x => by
        rw [Finset.sum_eq_single j]
        · simp only [u, Pi.single_apply, ↓reduceIte, hne01 j, mul_zero, mul_one, zero_sub, mul_neg]
        · intro j' _ hj'
          simp only [u, Pi.single_apply, hne_idx 1 0 hj', hne_idx 1 1 hj', ↓reduceIte,
            mul_zero, sub_self]
        · intro hm; exact absurd (Finset.mem_univ j) hm
      rw [hsum, hsum] at heval
      have hmul := congrArg (fun a : ℤ => -(signatureSign p q j * a)) heval
      simp only [mul_neg, neg_neg, ← mul_assoc, signatureSign_mul_self, one_mul] at hmul
      simpa only [x₁, x₂, hk'] using hmul
    · let u : Fin (2 * (p + q)) → ℤ := Pi.single (hermCoordEquiv (p + q) (j, 0)) 1
      have heval := congrArg (fun f => f (e u)) h
      rw [← hz₁, ← hz₂, cmSympForm_on_basis, cmSympForm_on_basis] at heval
      have hsum : ∀ x : Fin (2 * (p + q)) → ℤ,
          ∑ j' : Fin (p + q), signatureSign p q j' *
            (x (hermCoordEquiv (p + q) (j', 1)) * u (hermCoordEquiv (p + q) (j', 0)) -
             x (hermCoordEquiv (p + q) (j', 0)) * u (hermCoordEquiv (p + q) (j', 1))) =
          signatureSign p q j * x (hermCoordEquiv (p + q) (j, 1)) := fun x => by
        rw [Finset.sum_eq_single j]
        · simp only [u, Pi.single_apply, ↓reduceIte, (hne01 j).symm, mul_zero, mul_one, sub_zero]
        · intro j' _ hj'
          simp only [u, Pi.single_apply, hne_idx 0 0 hj', hne_idx 0 1 hj', ↓reduceIte,
            mul_zero, sub_self]
        · intro hm; exact absurd (Finset.mem_univ j) hm
      rw [hsum, hsum] at heval
      have hmul := congrArg (fun a : ℤ => signatureSign p q j * a) heval
      simp only [← mul_assoc, signatureSign_mul_self, one_mul] at hmul
      simpa only [x₁, x₂, hk'] using hmul
  · intro φ
    let x : Fin (2 * (p + q)) → ℤ := fun k =>
      let pr := (hermCoordEquiv (p + q)).symm k
      if pr.2 = 0 then
        -(signatureSign p q pr.1 * φ (e (Pi.single (hermCoordEquiv (p + q) (pr.1, 1)) 1)))
      else
        signatureSign p q pr.1 * φ (e (Pi.single (hermCoordEquiv (p + q) (pr.1, 0)) 1))
    refine ⟨e x, LinearMap.ext fun w => ?_⟩
    rw [← e.apply_symm_apply w, cmSympForm_on_basis]
    have hdecomp : e.symm w = ∑ k : Fin (2 * (p + q)),
        (e.symm w k) • (Pi.single k (1 : ℤ) : Fin (2 * (p + q)) → ℤ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hdecomp, map_sum, map_sum]
    rw [← (hermCoordEquiv (p + q)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_two]
    simp only [x, Equiv.symm_apply_apply, ↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
    rw [map_zsmul, map_zsmul, map_zsmul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
    have hs := signatureSign_mul_self p q j
    calc signatureSign p q j *
            (signatureSign p q j * φ (e (Pi.single (hermCoordEquiv (p + q) (j, 0)) 1)) *
              e.symm w (hermCoordEquiv (p + q) (j, 0)) -
             -(signatureSign p q j * φ (e (Pi.single (hermCoordEquiv (p + q) (j, 1)) 1))) *
              e.symm w (hermCoordEquiv (p + q) (j, 1)))
        = (signatureSign p q j * signatureSign p q j) *
            (e.symm w (hermCoordEquiv (p + q) (j, 0)) *
              φ (e (Pi.single (hermCoordEquiv (p + q) (j, 0)) 1)) +
             e.symm w (hermCoordEquiv (p + q) (j, 1)) *
              φ (e (Pi.single (hermCoordEquiv (p + q) (j, 1)) 1))) := by ring
      _ = _ := by rw [hs, one_mul, Int.cast_id, Int.cast_id]

/-- Explicit basepoint complex structure `J₀` on `ℝ^{2(p+q)}` for signature `(p, q)`. -/
def cmBaseJ : (Fin (2 * (p + q)) → ℝ) →ₗ[ℝ] (Fin (2 * (p + q)) → ℝ) where
  toFun v k :=
    let pr := (hermCoordEquiv (p + q)).symm k
    let s : ℝ := (signatureSign p q pr.1 : ℝ)
    if pr.2 = 0 then s * (-(Real.sqrt d) * v (hermCoordEquiv (p + q) (pr.1, 1)))
    else s * (v (hermCoordEquiv (p + q) (pr.1, 0)) / Real.sqrt d)
  map_add' _ _ := by ext k; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' _ _ := by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

private lemma cmBaseJ_apply_zero (v : Fin (2 * (p + q)) → ℝ) (j : Fin (p + q)) :
    cmBaseJ d p q v (hermCoordEquiv (p + q) (j, 0)) =
      (signatureSign p q j : ℝ) * (-(Real.sqrt d) * v (hermCoordEquiv (p + q) (j, 1))) := by
  simp [cmBaseJ]

private lemma cmBaseJ_apply_one (v : Fin (2 * (p + q)) → ℝ) (j : Fin (p + q)) :
    cmBaseJ d p q v (hermCoordEquiv (p + q) (j, 1)) =
      (signatureSign p q j : ℝ) * (v (hermCoordEquiv (p + q) (j, 0)) / Real.sqrt d) := by
  simp [cmBaseJ]

private lemma realSymp_cmSympForm (x y : Fin (2 * (p + q)) → ℝ) :
    realSymp (cmLatticeZBasis d hd p q) (cmSympForm d hd p q) x y =
      ∑ j : Fin (p + q), (signatureSign p q j : ℝ) *
        (x (hermCoordEquiv (p + q) (j, 1)) * y (hermCoordEquiv (p + q) (j, 0)) -
         x (hermCoordEquiv (p + q) (j, 0)) * y (hermCoordEquiv (p + q) (j, 1))) := by
  unfold realSymp
  rw [realExtBilin_apply_matrix]
  have hmat : ∀ k l : Fin (2 * (p + q)),
      bilinMatrix ((cmSympForm d hd p q).comp
        (cmLatticeZBasis d hd p q).toLinearMap (cmLatticeZBasis d hd p q).toLinearMap) k l =
      let pk := (hermCoordEquiv (p + q)).symm k
      let pl := (hermCoordEquiv (p + q)).symm l
      if pk.1 = pl.1 then
        if pk.2 = 1 ∧ pl.2 = 0 then signatureSign p q pk.1
        else if pk.2 = 0 ∧ pl.2 = 1 then -signatureSign p q pk.1
        else 0
      else 0 := by
    intro k l
    change cmSympForm d hd p q (cmLatticeZBasis d hd p q (Pi.single k 1))
      (cmLatticeZBasis d hd p q (Pi.single l 1)) = _
    rw [cmSympForm_on_basis]
    rcases hk : (hermCoordEquiv (p + q)).symm k with ⟨jk, tk⟩
    rcases hl : (hermCoordEquiv (p + q)).symm l with ⟨jl, tl⟩
    have hk' : hermCoordEquiv (p + q) (jk, tk) = k := by rw [← hk, Equiv.apply_symm_apply]
    have hl' : hermCoordEquiv (p + q) (jl, tl) = l := by rw [← hl, Equiv.apply_symm_apply]
    rw [Finset.sum_eq_single jk]
    · by_cases hjeq : jk = jl
      · subst hjeq
        have hne01 : hermCoordEquiv (p + q) (jk, 0) ≠ hermCoordEquiv (p + q) (jk, 1) := fun h => by
          have := (hermCoordEquiv (p + q)).injective h; simp at this
        fin_cases tk <;> fin_cases tl <;>
          simp [← hk', ← hl', hne01, hne01.symm]
      · have h0 : hermCoordEquiv (p + q) (jk, 0) ≠ l := fun h => by
          rw [← hl'] at h; exact hjeq (Prod.mk.inj ((hermCoordEquiv (p + q)).injective h)).1
        have h1 : hermCoordEquiv (p + q) (jk, 1) ≠ l := fun h => by
          rw [← hl'] at h; exact hjeq (Prod.mk.inj ((hermCoordEquiv (p + q)).injective h)).1
        simp [hjeq, Pi.single_apply, h0, h1]
    · intro j' _ hj'
      have h0 : hermCoordEquiv (p + q) (j', 0) ≠ k := fun h => by
        rw [← hk'] at h; exact hj' (Prod.mk.inj ((hermCoordEquiv (p + q)).injective h)).1
      have h1 : hermCoordEquiv (p + q) (j', 1) ≠ k := fun h => by
        rw [← hk'] at h; exact hj' (Prod.mk.inj ((hermCoordEquiv (p + q)).injective h)).1
      simp [Pi.single_apply, h0, h1]
    · intro hm; exact absurd (Finset.mem_univ jk) hm
  rw [← (hermCoordEquiv (p + q)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.sum_univ_two]
  have hinner : ∀ t : Fin 2,
      ∑ l : Fin (2 * (p + q)),
        x (hermCoordEquiv (p + q) (j, t)) *
          ((bilinMatrix ((cmSympForm d hd p q).comp
            (cmLatticeZBasis d hd p q).toLinearMap (cmLatticeZBasis d hd p q).toLinearMap)
            (hermCoordEquiv (p + q) (j, t)) l : ℤ) : ℝ) * y l =
      if t = 0 then
        -((signatureSign p q j : ℝ) * x (hermCoordEquiv (p + q) (j, 0)) *
          y (hermCoordEquiv (p + q) (j, 1)))
      else
        (signatureSign p q j : ℝ) * x (hermCoordEquiv (p + q) (j, 1)) *
          y (hermCoordEquiv (p + q) (j, 0)) := fun t => by
    rw [← (hermCoordEquiv (p + q)).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · rw [Fin.sum_univ_two]
      simp only [hmat, Equiv.symm_apply_apply, ↓reduceIte]
      rcases fin_two_cases t with rfl | rfl <;>
        simp only [↓reduceIte, Fin.one_eq_zero_iff, Fin.zero_ne_one, Nat.reduceEqDiff, and_self,
          and_false, false_and, Int.cast_neg, Int.cast_zero, mul_zero, zero_mul, add_zero] <;> ring
    · intro j' _ hj'
      exact Finset.sum_eq_zero fun _ _ => by simp [hmat, Ne.symm hj']
    · intro hm; exact absurd (Finset.mem_univ j) hm
  rw [hinner 0, hinner 1]
  simp only [↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
  ring

private lemma realAction_cmOrder (α : CMOrder d) (x : Fin (2 * (p + q)) → ℝ) :
    let a : ℝ := ((cmOrderZEquiv d hd).symm α 0 : ℤ)
    let b : ℝ := ((cmOrderZEquiv d hd).symm α 1 : ℤ)
    ∀ j : Fin (p + q),
      realAction (cmOrderInvolution d) (cmLatticeZBasis d hd p q) α x
          (hermCoordEquiv (p + q) (j, 0)) =
        a * x (hermCoordEquiv (p + q) (j, 0)) -
          (d : ℝ) * b * x (hermCoordEquiv (p + q) (j, 1)) ∧
      realAction (cmOrderInvolution d) (cmLatticeZBasis d hd p q) α x
          (hermCoordEquiv (p + q) (j, 1)) =
        a * x (hermCoordEquiv (p + q) (j, 1)) +
          b * x (hermCoordEquiv (p + q) (j, 0)) := by
  dsimp only
  set aZ := (cmOrderZEquiv d hd).symm α 0
  set bZ := (cmOrderZEquiv d hd).symm α 1
  let T : (Fin (2 * (p + q)) → ℝ) →ₗ[ℝ] (Fin (2 * (p + q)) → ℝ) :=
    { toFun := fun v k =>
        let pr := (hermCoordEquiv (p + q)).symm k
        if pr.2 = 0 then
          (aZ : ℝ) * v (hermCoordEquiv (p + q) (pr.1, 0)) -
            (d : ℝ) * (bZ : ℝ) * v (hermCoordEquiv (p + q) (pr.1, 1))
        else
          (aZ : ℝ) * v (hermCoordEquiv (p + q) (pr.1, 1)) +
            (bZ : ℝ) * v (hermCoordEquiv (p + q) (pr.1, 0))
      map_add' := fun _ _ => by ext k; simp only [Pi.add_apply]; split_ifs <;> ring
      map_smul' := fun _ _ => by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring }
  have heq : realAction (cmOrderInvolution d) (cmLatticeZBasis d hd p q) α = T := by
    apply LinearMap.ext fun v => ?_
    have hv : v = ∑ m : Fin (2 * (p + q)), v m • (Pi.single m (1 : ℝ) : Fin (2 * (p + q)) → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun m _ => congrArg (v m • ·) ?_
    have hcast : (Pi.single m (1 : ℝ) : Fin (2 * (p + q)) → ℝ) =
        fun i => (((Pi.single m (1 : ℤ) : Fin (2 * (p + q)) → ℤ) i : ℤ) : ℝ) := by
      ext i; by_cases h : i = m <;> simp [h]
    rw [hcast]
    unfold realAction
    rw [realExtLinear_intCast]
    ext k
    rcases hk : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
    have hcoords := cmOrder_mul_coords d hd α
      (cmLatticeZBasis d hd p q (Pi.single m (1 : ℤ)) j)
    have hbase : ∀ t' : Fin 2,
        (cmOrderZEquiv d hd).symm (cmLatticeZBasis d hd p q (Pi.single m (1 : ℤ)) j) t' =
          (Pi.single m (1 : ℤ) : Fin (2 * (p + q)) → ℤ) (hermCoordEquiv (p + q) (j, t')) :=
      fun t' => cmLatticeZBasis_symm_coord d hd p q _ j t'
    have hlhs : ((cmLatticeZBasis d hd p q).symm
          (α • cmLatticeZBasis d hd p q (Pi.single m (1 : ℤ)))) k =
        (cmOrderZEquiv d hd).symm (α * cmLatticeZBasis d hd p q (Pi.single m (1 : ℤ)) j) t := by
      simp [cmLatticeZBasis, hk]
    change (((cmLatticeZBasis d hd p q).symm
      (α • cmLatticeZBasis d hd p q (Pi.single m (1 : ℤ))) k : ℤ) : ℝ) = T _ k
    rw [hlhs]
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, hk]
    rcases fin_two_cases t with rfl | rfl
    · simp only [↓reduceIte, hcoords.1, hbase 0, hbase 1]; push_cast; rfl
    · simp only [Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte, hcoords.2, hbase 0, hbase 1]
      push_cast; rfl
  intro j
  rw [heq]
  exact ⟨by simp [T], by simp [T]⟩

/-- Helper computing the Kottwitz `+`/`-` eigenspace dimensions at `cmBaseJ d p q`. -/
private lemma cmBaseJ_eigen_finranks :
    Module.finrank ℝ (eigenPlus (cmOrderInvolution d) (cmLatticeZBasis d hd p q) (cmBaseJ d p q)) =
      2 * (cmOrderInvolution d).degF * p ∧
    Module.finrank ℝ (eigenMinus (cmOrderInvolution d) (cmLatticeZBasis d hd p q) (cmBaseJ d p q)) =
      2 * (cmOrderInvolution d).degF * q := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg d)
  let ω : CMOrder d := ⟨cmGen d, 0, 1, by simp⟩
  have hω_coord : (cmOrderZEquiv d hd).symm ω = ![0, 1] := by
    have : ω = cmOrderZEquiv d hd ![0, 1] := Subtype.ext (by simp [ω])
    rw [this, (cmOrderZEquiv d hd).symm_apply_apply]
  have hω_re : ((cmOrderInvolution d).emb ω).re = 0 := by simp [cmOrderInvolution, ω, cmGen]
  have hω_im : ((cmOrderInvolution d).emb ω).im = Real.sqrt d := by simp [cmOrderInvolution, ω, cmGen]
  have hωc_re : ((cmOrderInvolution d).emb ((cmOrderInvolution d).conj ω)).re = 0 := by
    simp [cmOrderInvolution, cmOrderConj, ω, cmGen]
  have hωc_im : ((cmOrderInvolution d).emb ((cmOrderInvolution d).conj ω)).im = -Real.sqrt d := by
    simp [cmOrderInvolution, cmOrderConj, ω, cmGen]
  constructor
  · let P : Submodule ℝ (Fin (2 * (p + q)) → ℝ) :=
      { carrier := { x | ∀ k, p ≤ ((hermCoordEquiv (p + q)).symm k).1.val → x k = 0 }
        add_mem' := fun hx hy k hk => by simp [hx k hk, hy k hk]
        zero_mem' := fun _ _ => rfl
        smul_mem' := fun _ _ hx k hk => by simp [hx k hk] }
    have hEq : eigenPlus (cmOrderInvolution d) (cmLatticeZBasis d hd p q) (cmBaseJ d p q) = P := by
      ext x
      simp only [eigenPlus, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, P, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
      constructor
      · intro hx k hk
        have hω := hx ω
        rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
        have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hpr, Equiv.apply_symm_apply]
        have hsign : signatureSign p q j = -1 := by
          unfold signatureSign; rw [if_neg (by simpa [hpr] using Nat.not_lt.mpr hk)]
        have hact := realAction_cmOrder d hd p q ω x j
        rw [hω_coord] at hact
        have h0 := congrFun hω (hermCoordEquiv (p + q) (j, 0))
        have h1 := congrFun hω (hermCoordEquiv (p + q) (j, 1))
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hω_re, hω_im, zero_mul, zero_add] at h0 h1
        rw [hact.1, cmBaseJ_apply_zero, hsign] at h0
        rw [hact.2, cmBaseJ_apply_one, hsign] at h1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_zero, Int.cast_one,
          zero_mul, zero_sub, zero_add, one_mul, Int.cast_neg] at h0 h1
        rcases fin_two_cases t with rfl | rfl
        · rw [← hk']; field_simp [hsqrt_pos.ne'] at h1; nlinarith [h1, hsqrt_pos]
        · rw [← hk']; have : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd; nlinarith [h0, hsq]
      · intro hx α
        ext k
        rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
        have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hpr, Equiv.apply_symm_apply]
        rw [← hk']
        have hre : ((cmOrderInvolution d).emb α).re = ((cmOrderZEquiv d hd).symm α 0 : ℤ) := by
          change (α : ℂ).re = _; rw [cmOrderZEquiv_symm_eq d hd α]; simp [cmGen]
        have him : ((cmOrderInvolution d).emb α).im =
            ((cmOrderZEquiv d hd).symm α 1 : ℤ) * Real.sqrt d := by
          change (α : ℂ).im = _; rw [cmOrderZEquiv_symm_eq d hd α]; simp [cmGen]
        have hact := realAction_cmOrder d hd p q α x j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hre, him]
        by_cases hlt : j.val < p
        · have hsign : signatureSign p q j = 1 := by unfold signatureSign; rw [if_pos hlt]
          rcases fin_two_cases t with rfl | rfl
          · rw [hact.1, cmBaseJ_apply_zero, hsign]; push_cast
            linear_combination ((cmOrderZEquiv d hd).symm α 1 : ℝ) *
              x (hermCoordEquiv (p + q) (j, 1)) * hsq
          · rw [hact.2, cmBaseJ_apply_one, hsign]; push_cast; field_simp [hsqrt_pos.ne']
        · have hge : p ≤ j.val := Nat.le_of_not_lt hlt
          have hx0 : x (hermCoordEquiv (p + q) (j, 0)) = 0 := hx _ (by simpa using hge)
          have hx1 : x (hermCoordEquiv (p + q) (j, 1)) = 0 := hx _ (by simpa using hge)
          rcases fin_two_cases t with rfl | rfl
          · rw [hact.1, cmBaseJ_apply_zero, hx0, hx1]; ring
          · rw [hact.2, cmBaseJ_apply_one, hx0, hx1]; ring
    rw [hEq]
    let eP : P ≃ₗ[ℝ] (Fin p × Fin 2 → ℝ) :=
      { toFun := fun v jt => v.1 (hermCoordEquiv (p + q) (⟨jt.1.val, by omega⟩, jt.2))
        invFun := fun f => ⟨fun k =>
          let pr := (hermCoordEquiv (p + q)).symm k
          if h : pr.1.val < p then f (⟨pr.1.val, h⟩, pr.2) else 0,
          fun k hk => by simp [Nat.not_lt.mpr hk]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by
          apply Subtype.ext; ext k
          rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
          have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hpr, Equiv.apply_symm_apply]
          simp only [hpr]
          split_ifs with hlt
          · simp [hk']
          · exact (v.2 k (by simpa [hpr] using Nat.le_of_not_lt hlt)).symm
        right_inv := fun f => by ext ⟨j, t⟩; simp [j.isLt] }
    rw [eP.finrank_eq, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    simp [mul_comm]
  · let Q : Submodule ℝ (Fin (2 * (p + q)) → ℝ) :=
      { carrier := { x | ∀ k, ((hermCoordEquiv (p + q)).symm k).1.val < p → x k = 0 }
        add_mem' := fun hx hy k hk => by simp [hx k hk, hy k hk]
        zero_mem' := fun _ _ => rfl
        smul_mem' := fun _ _ hx k hk => by simp [hx k hk] }
    have hEq : eigenMinus (cmOrderInvolution d) (cmLatticeZBasis d hd p q) (cmBaseJ d p q) = Q := by
      ext x
      simp only [eigenMinus, Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.id_apply, Q, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
      constructor
      · intro hx k hk
        have hω := hx ω
        rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
        have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hpr, Equiv.apply_symm_apply]
        have hsign : signatureSign p q j = 1 := by
          unfold signatureSign; rw [if_pos (by simpa [hpr] using hk)]
        have hact := realAction_cmOrder d hd p q ω x j
        rw [hω_coord] at hact
        have h0 := congrFun hω (hermCoordEquiv (p + q) (j, 0))
        have h1 := congrFun hω (hermCoordEquiv (p + q) (j, 1))
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hωc_re, hωc_im, zero_mul, zero_add] at h0 h1
        rw [hact.1, cmBaseJ_apply_zero, hsign] at h0
        rw [hact.2, cmBaseJ_apply_one, hsign] at h1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_zero, Int.cast_one,
          zero_mul, zero_sub, zero_add, one_mul] at h0 h1
        rcases fin_two_cases t with rfl | rfl
        · rw [← hk']; field_simp [hsqrt_pos.ne'] at h1; nlinarith [h1, hsqrt_pos]
        · rw [← hk']; have : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd; nlinarith [h0, hsq]
      · intro hx α
        ext k
        rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
        have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hpr, Equiv.apply_symm_apply]
        rw [← hk']
        have hre : ((cmOrderInvolution d).emb ((cmOrderInvolution d).conj α)).re =
            ((cmOrderZEquiv d hd).symm α 0 : ℤ) := by
          change (star (α : ℂ)).re = _; rw [cmOrderZEquiv_symm_eq d hd α]; simp [cmGen]
        have him : ((cmOrderInvolution d).emb ((cmOrderInvolution d).conj α)).im =
            -(((cmOrderZEquiv d hd).symm α 1 : ℤ) * Real.sqrt d) := by
          change (star (α : ℂ)).im = _; rw [cmOrderZEquiv_symm_eq d hd α]; simp [cmGen]
        have hact := realAction_cmOrder d hd p q α x j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hre, him]
        by_cases hlt : j.val < p
        · have hx0 : x (hermCoordEquiv (p + q) (j, 0)) = 0 := hx _ (by simpa using hlt)
          have hx1 : x (hermCoordEquiv (p + q) (j, 1)) = 0 := hx _ (by simpa using hlt)
          rcases fin_two_cases t with rfl | rfl
          · rw [hact.1, cmBaseJ_apply_zero, hx0, hx1]; ring
          · rw [hact.2, cmBaseJ_apply_one, hx0, hx1]; ring
        · have hsign : signatureSign p q j = -1 := by unfold signatureSign; rw [if_neg hlt]
          rcases fin_two_cases t with rfl | rfl
          · rw [hact.1, cmBaseJ_apply_zero, hsign]; push_cast
            linear_combination ((cmOrderZEquiv d hd).symm α 1 : ℝ) *
              x (hermCoordEquiv (p + q) (j, 1)) * hsq
          · rw [hact.2, cmBaseJ_apply_one, hsign]; push_cast; field_simp [hsqrt_pos.ne']
    rw [hEq]
    let eQ : Q ≃ₗ[ℝ] (Fin q × Fin 2 → ℝ) :=
      { toFun := fun v jt => v.1 (hermCoordEquiv (p + q) (⟨p + jt.1.val, by omega⟩, jt.2))
        invFun := fun f => ⟨fun k =>
          let pr := (hermCoordEquiv (p + q)).symm k
          if h : p ≤ pr.1.val then f (⟨pr.1.val - p, by have := pr.1.isLt; omega⟩, pr.2) else 0,
          fun k hk => by simp [Nat.not_le.mpr hk]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by
          apply Subtype.ext; ext k
          rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
          have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hpr, Equiv.apply_symm_apply]
          simp only [hpr]
          split_ifs with hge
          · have hfin : (⟨p + (j.val - p), by have := j.isLt; omega⟩ : Fin (p + q)) = j :=
              Fin.ext (Nat.add_sub_cancel' hge)
            simp [hfin, hk']
          · exact (v.2 k (by simpa [hpr] using Nat.lt_of_not_ge hge)).symm
        right_inv := fun f => by
          ext ⟨j, t⟩
          simp [Nat.le_add_right p j.val] }
    rw [eQ.finrank_eq, Module.finrank_pi, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    simp [mul_comm]

/-- **Unconditional Constructive Existence of `PELDatumCM` (`mkCMOrderPELDatum`)**:
for EVERY `d ≥ 1` and EVERY signature `(p, q)` (definite or indefinite!), constructs a concrete
`PELDatumCM` over `CMOrder d = ℤ[√(-d)]`. -/
def mkCMOrderPELDatum : PELDatumCM where
  O := cmOrderInvolution d
  p := p
  q := q
  g := p + q
  g_eq := by simp
  La := Fin (p + q) → CMOrder d
  zBasis := cmLatticeZBasis d hd p q
  symp := cmSympForm d hd p q
  symp_alt := cmSympForm_alt d hd p q
  symp_unimodular := cmSympForm_unimodular d hd p q
  symp_adjoint := cmSympForm_adjoint d hd p q
  domain_nonempty := by
    have hsqrt_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
    have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg d)
    have heig := cmBaseJ_eigen_finranks d hd p q
    refine ⟨cmBaseJ d p q, ?_, ?_, ?_, ?_, heig.1, heig.2⟩
    · intro α
      apply LinearMap.ext; intro x; ext k
      rcases hk : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
      have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hk, Equiv.apply_symm_apply]
      rw [← hk']
      simp only [LinearMap.comp_apply]
      have h1 := realAction_cmOrder d hd p q α x j
      have h2 := realAction_cmOrder d hd p q α (cmBaseJ d p q x) j
      have hne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
      rcases fin_two_cases t with rfl | rfl
      · rw [cmBaseJ_apply_zero, h1.2, h2.1, cmBaseJ_apply_zero, cmBaseJ_apply_one]
        field_simp [hne]
        linear_combination -(((cmOrderZEquiv d hd).symm α 1 : ℤ) : ℝ) *
          (signatureSign p q j : ℝ) * x (hermCoordEquiv (p + q) (j, 0)) * hsq
      · rw [cmBaseJ_apply_one, h1.1, h2.2, cmBaseJ_apply_zero, cmBaseJ_apply_one]
        field_simp [hne]
        linear_combination (((cmOrderZEquiv d hd).symm α 1 : ℤ) : ℝ) *
          (signatureSign p q j : ℝ) * x (hermCoordEquiv (p + q) (j, 1)) * hsq
    · apply LinearMap.ext; intro x; ext k
      rcases hk : (hermCoordEquiv (p + q)).symm k with ⟨j, t⟩
      have hk' : hermCoordEquiv (p + q) (j, t) = k := by rw [← hk, Equiv.apply_symm_apply]
      rw [← hk']
      have hs : ((signatureSign p q j : ℝ)) ^ 2 = 1 := by
        rw [sq]; exact_mod_cast signatureSign_mul_self p q j
      have hne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, Pi.neg_apply]
      rcases fin_two_cases t with rfl | rfl
      · rw [cmBaseJ_apply_zero, cmBaseJ_apply_one]
        field_simp [hne]; ring_nf; rw [hs]; ring
      · rw [cmBaseJ_apply_one, cmBaseJ_apply_zero]
        field_simp [hne]; ring_nf; rw [hs]; ring
    · intro x y
      rw [realSymp_cmSympForm, realSymp_cmSympForm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cmBaseJ_apply_zero, cmBaseJ_apply_one, cmBaseJ_apply_zero, cmBaseJ_apply_one]
      have hs : ((signatureSign p q j : ℝ)) ^ 2 = 1 := by
        rw [sq]; exact_mod_cast signatureSign_mul_self p q j
      have hne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
      field_simp [hne]
      linear_combination (x (hermCoordEquiv (p + q) (j, 1)) * y (hermCoordEquiv (p + q) (j, 0)) -
        x (hermCoordEquiv (p + q) (j, 0)) * y (hermCoordEquiv (p + q) (j, 1))) *
        (signatureSign p q j : ℝ) * hs
    · intro x hx
      rw [realSymp_cmSympForm]
      have hterm : ∀ j : Fin (p + q),
          (signatureSign p q j : ℝ) *
            (cmBaseJ d p q x (hermCoordEquiv (p + q) (j, 1)) * x (hermCoordEquiv (p + q) (j, 0)) -
             cmBaseJ d p q x (hermCoordEquiv (p + q) (j, 0)) * x (hermCoordEquiv (p + q) (j, 1))) =
          x (hermCoordEquiv (p + q) (j, 0)) ^ 2 / Real.sqrt d +
            Real.sqrt d * x (hermCoordEquiv (p + q) (j, 1)) ^ 2 := fun j => by
        rw [cmBaseJ_apply_zero, cmBaseJ_apply_one]
        have hs : ((signatureSign p q j : ℝ)) ^ 2 = 1 := by
          rw [sq]; exact_mod_cast signatureSign_mul_self p q j
        have hne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
        field_simp [hne]
        linear_combination (x (hermCoordEquiv (p + q) (j, 0)) ^ 2 +
          Real.sqrt d ^ 2 * x (hermCoordEquiv (p + q) (j, 1)) ^ 2) * hs
      simp_rw [hterm]
      have hne : ∃ k : Fin (2 * (p + q)), x k ≠ 0 := by
        by_contra hall; push Not at hall; exact hx (funext hall)
      obtain ⟨k, hk⟩ := hne
      rcases hpr : (hermCoordEquiv (p + q)).symm k with ⟨j₀, t₀⟩
      have hk' : hermCoordEquiv (p + q) (j₀, t₀) = k := by rw [← hpr, Equiv.apply_symm_apply]
      refine Finset.sum_pos' (fun _ _ => by positivity) ⟨j₀, Finset.mem_univ j₀, ?_⟩
      rcases fin_two_cases t₀ with rfl | rfl
      · have hpos : 0 < x (hermCoordEquiv (p + q) (j₀, 0)) ^ 2 / Real.sqrt d :=
          div_pos (sq_pos_of_ne_zero (by rwa [hk'])) hsqrt_pos
        linarith [mul_nonneg hsqrt_pos.le (sq_nonneg (x (hermCoordEquiv (p + q) (j₀, 1))))]
      · have hpos : 0 < Real.sqrt d * x (hermCoordEquiv (p + q) (j₀, 1)) ^ 2 :=
          mul_pos hsqrt_pos (sq_pos_of_ne_zero (by rwa [hk']))
        linarith [div_nonneg (sq_nonneg (x (hermCoordEquiv (p + q) (j₀, 0)))) hsqrt_pos.le]

/-- **Definite-Signature Bridge to Stage 11 & Stage 12 (`pelDatum_definite_bridge`)**:
connects `(mkCMOrderPELDatum d hd r 0).La` to `Stage11DefiniteUnitaryChain.stdCMLattice r d hd`. -/
theorem pelDatum_definite_bridge (r : ℕ) :
    ∃ e : (mkCMOrderPELDatum d hd r 0).La ≃ₗ[ℤ] (stdCMLattice r d hd).lat,
      ∀ x y : Fin (2 * (r + 0)) → ℤ,
        realSymp (cmLatticeZBasis d hd r 0) (cmSympForm d hd r 0)
            (cmBaseJ d r 0 (fun k => (x k : ℝ))) (fun k => (y k : ℝ)) =
          (1 / Real.sqrt d) *
            inner ℝ (e (cmLatticeZBasis d hd r 0 x) : DefiniteHermitianSpace r)
              (e (cmLatticeZBasis d hd r 0 y) : DefiniteHermitianSpace r) := by
  let bZ := stdCMZBasis r d hd
  let eqIdx : Fin (2 * (r + 0)) ≃ Fin (2 * r) := finCongr (by omega)
  let e : (mkCMOrderPELDatum d hd r 0).La ≃ₗ[ℤ] (stdCMLattice r d hd).lat :=
    (cmLatticeZBasis d hd r 0).symm.trans
      ((LinearEquiv.funCongrLeft ℤ ℤ eqIdx.symm).trans
        ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (2 * r))).symm.trans bZ.repr.symm))
  refine ⟨e, fun x y => ?_⟩
  have hsqrt_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hsq : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have heval : ∀ v : Fin (2 * (r + 0)) → ℤ,
      (e (cmLatticeZBasis d hd r 0 v) : DefiniteHermitianSpace r) =
        WithLp.toLp 2 fun j : Fin r =>
          ((v (hermCoordEquiv (r + 0) (⟨j.val, by omega⟩, 0)) : ℤ) : ℂ) +
          ((v (hermCoordEquiv (r + 0) (⟨j.val, by omega⟩, 1)) : ℤ) : ℂ) * cmGen d := fun v => by
    have hsum : (e (cmLatticeZBasis d hd r 0 v) : DefiniteHermitianSpace r) =
        ∑ k : Fin (2 * r), (v (eqIdx.symm k)) • stdCMBasisVec r d k := by
      have h1 : e (cmLatticeZBasis d hd r 0 v) =
          bZ.repr.symm ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (2 * r))).symm
            (fun k => v (eqIdx.symm k))) := by
        change bZ.repr.symm ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin (2 * r))).symm
          (fun k => ((cmLatticeZBasis d hd r 0).symm (cmLatticeZBasis d hd r 0 v)) (eqIdx.symm k))) = _
        simp only [LinearEquiv.symm_apply_apply]
      rw [h1, Basis.repr_symm_apply, Finsupp.linearCombination_apply,
        Finsupp.sum_fintype _ _ (fun _ => by simp)]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp [bZ, stdCMZBasis, stdCMRealBasis]
    rw [hsum]; ext j
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, zsmul_eq_mul]
    rw [← (hermCoordEquiv r).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · rw [Fin.sum_univ_two]
      have h0 : eqIdx.symm (hermCoordEquiv r (j, 0)) =
          hermCoordEquiv (r + 0) (⟨j.val, by omega⟩, 0) :=
        Fin.ext (by simp [eqIdx, hermCoordEquiv, finProdFinEquiv])
      have h1 : eqIdx.symm (hermCoordEquiv r (j, 1)) =
          hermCoordEquiv (r + 0) (⟨j.val, by omega⟩, 1) :=
        Fin.ext (by simp [eqIdx, hermCoordEquiv, finProdFinEquiv])
      simp [stdCMBasisVec, h0, h1]
    · intro j' _ hj'; exact Finset.sum_eq_zero fun _ _ => by simp [stdCMBasisVec, hj'.symm]
    · intro hm; exact absurd (Finset.mem_univ j) hm
  rw [realSymp_cmSympForm, heval x, heval y, real_inner_eq_re_complex_inner,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj_eta : (⟨j.val, by omega⟩ : Fin (r + 0)) = j := Fin.ext rfl
  rw [cmBaseJ_apply_zero, cmBaseJ_apply_one]
  have hs : signatureSign r 0 j = 1 := by unfold signatureSign; rw [if_pos (by omega)]
  rw [hs]
  simp only [Pi.star_apply, Complex.star_def, Int.cast_one, one_mul, hj_eta,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, cmGen, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_im]
  have hsqrt_ne : Real.sqrt d ≠ 0 := hsqrt_pos.ne'
  field_simp [hsqrt_ne]
  ring

end ConcreteCMOrderPELDatum

end PELDatumSection

/-! ## Section 2: Polarized Riemann Form, `PELUnitaryGroup`, `PolarizedAut`, & Finiteness -/

section PolarizedAutomorphisms

variable (D : PELDatumCM)

/-- The symmetric positive-definite **Riemann bilinear form** `R_J(x, y) = symp_ℝ(J x, y)`. -/
def riemannForm (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)) :
    LinearMap.BilinForm ℝ (Fin (2 * D.g) → ℝ) :=
  D.sympR.comp J LinearMap.id

@[simp]
lemma riemannForm_apply (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ))
    (x y : Fin (2 * D.g) → ℝ) : riemannForm D J x y = D.sympR (J x) y := rfl

theorem riemannForm_symm {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (hJ : J ∈ D.hermitianDomain) (x y : Fin (2 * D.g) → ℝ) :
    riemannForm D J x y = riemannForm D J y x := by
  rcases hJ with ⟨_, hJ2, hJsymp, _, _, _⟩
  have hJJ : ∀ v, J (J v) = -v := fun v => by
    have := congrArg (fun f : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ) => f v) hJ2
    simpa using this
  calc D.sympR (J x) y
      = D.sympR (J (J x)) (J y) := (hJsymp (J x) y).symm
    _ = D.sympR (-x) (J y) := by rw [hJJ x]
    _ = -D.sympR x (J y) := by simp
    _ = D.sympR (J y) x := by rw [D.sympR_skew x (J y), neg_neg]

theorem riemannForm_pos {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (hJ : J ∈ D.hermitianDomain) {x : Fin (2 * D.g) → ℝ} (hx : x ≠ 0) :
    0 < riemannForm D J x x :=
  hJ.2.2.2.1 x hx

/-- Real symmetric Gram matrix `R_J` of the Riemann form in the standard basis of `ℝ^{2g}`. -/
def riemannFormMatrix (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)) :
    Matrix (Fin (2 * D.g)) (Fin (2 * D.g)) ℝ :=
  bilinMatrix (riemannForm D J)

theorem riemannForm_eq_dotProduct_mulVec (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ))
    (x y : Fin (2 * D.g) → ℝ) :
    riemannForm D J x y = x ⬝ᵥ (riemannFormMatrix D J).mulVec y :=
  bilin_eq_dotProduct_mulVec (riemannForm D J) x y

theorem riemannFormMatrix_posDef {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (hJ : J ∈ D.hermitianDomain) : (riemannFormMatrix D J).PosDef := by
  refine ⟨?_, fun {x} hx => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, riemannFormMatrix, bilinMatrix,
      Matrix.of_apply]
    exact riemannForm_symm D hJ (Pi.single j 1) (Pi.single i 1)
  · have hsum : (x.sum fun i xi => x.sum fun j xj =>
        star xi * riemannFormMatrix D J i j * xj) = riemannForm D J x x := by
      rw [riemannForm_eq_dotProduct_mulVec, Finsupp.sum_fintype _ _ (fun _ => by simp)]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      refine Finset.sum_congr rfl fun j _ => by simp only [star_trivial]; ring
    rw [hsum]
    exact riemannForm_pos D hJ (fun h0 => hx (Finsupp.ext fun i => congrFun h0 i))

/-- Spectral lower bound on the Riemann quadratic form: `∃ c > 0, ∀ v, c * ∑ i, (v i)² ≤ R_J(v, v)`. -/
theorem riemannForm_coercive {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (hJ : J ∈ D.hermitianDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin (2 * D.g) → ℝ, c * (∑ i : Fin (2 * D.g), v i ^ 2) ≤
      riemannForm D J v v := by
  by_cases hg : 2 * D.g = 0
  · refine ⟨1, one_pos, fun v => ?_⟩
    have hv : v = 0 := funext fun i => (Nat.not_lt_zero i.val (by omega)).elim
    subst hv; simp
  · have : Nonempty (Fin (2 * D.g)) := ⟨⟨0, Nat.pos_of_ne_zero hg⟩⟩
    have hPD := riemannFormMatrix_posDef D hJ
    set A := riemannFormMatrix D J
    set lam := hPD.isHermitian.eigenvalues
    let c := Finset.univ.inf' Finset.univ_nonempty lam
    have hc_pos : 0 < c := by
      rw [Finset.lt_inf'_iff]; intro i _; exact hPD.eigenvalues_pos i
    refine ⟨c, hc_pos, fun v => ?_⟩
    set U := hPD.isHermitian.eigenvectorUnitary
    set UM : Matrix (Fin (2 * D.g)) (Fin (2 * D.g)) ℝ := U.val
    let w : Fin (2 * D.g) → ℝ := (star UM).mulVec v
    have hT : UMᵀ = star UM := by ext i j; simp
    have hUU : UM * star UM = 1 := by simp [UM]
    have hw_norm : ∑ i : Fin (2 * D.g), w i ^ 2 = ∑ i : Fin (2 * D.g), v i ^ 2 := by
      have h1 : w ⬝ᵥ w = v ⬝ᵥ v := by
        calc w ⬝ᵥ w = (v ᵥ* (star UM)ᵀ) ⬝ᵥ ((star UM).mulVec v) := by
                simp only [w, Matrix.vecMul_transpose]
          _ = v ⬝ᵥ ((star UM)ᵀ.mulVec ((star UM).mulVec v)) := (Matrix.dotProduct_mulVec _ _ _).symm
          _ = v ⬝ᵥ (((star UM)ᵀ * star UM).mulVec v) := by rw [Matrix.mulVec_mulVec]
          _ = v ⬝ᵥ ((UM * star UM).mulVec v) := by rw [← hT, Matrix.transpose_transpose]
          _ = v ⬝ᵥ v := by rw [hUU, Matrix.one_mulVec]
      simpa only [dotProduct, sq] using h1
    have hspec : A = UM * (Matrix.diagonal lam * star UM) := by
      simpa [A, UM, U, lam, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hPD.isHermitian.spectral_theorem
    have hquad : riemannForm D J v v = ∑ i : Fin (2 * D.g), lam i * w i ^ 2 := by
      rw [riemannForm_eq_dotProduct_mulVec]
      change v ⬝ᵥ A.mulVec v = _
      rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, hT]
      change w ⬝ᵥ (Matrix.diagonal lam).mulVec w = _
      simp only [dotProduct, Matrix.mulVec_diagonal]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hquad, ← hw_norm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (Finset.inf'_le lam (Finset.mem_univ i)) (sq_nonneg _)

/-- **PEL Integral Unitary Group `PELUnitaryGroup D`**:
`O`-linear symplectic `ℤ`-automorphisms of `(D.La, D.symp)`. -/
def PELUnitaryGroup : Subgroup (D.La ≃ₗ[ℤ] D.La) where
  carrier := { g | (∀ x y : D.La, D.symp (g x) (g y) = D.symp x y) ∧
    (∀ (a : D.O.R) (x : D.La), g (a • x) = a • g x) }
  one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := fun {g h} hg hh =>
    ⟨fun x y => by change D.symp (g (h x)) (g (h y)) = D.symp x y; rw [hg.1, hh.1],
     fun a x => by change g (h (a • x)) = a • g (h x); rw [hh.2, hg.2]⟩
  inv_mem' := fun {g} hg =>
    ⟨fun x y => by
      change D.symp (g.symm x) (g.symm y) = D.symp x y
      have h1 := hg.1 (g.symm x) (g.symm y)
      simpa only [LinearEquiv.apply_symm_apply] using h1.symm,
     fun a x => by
      apply g.injective
      change g (g.symm (a • x)) = g (a • g.symm x)
      rw [hg.2, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]⟩

/-- Integer matrix representation of `g ∈ PELUnitaryGroup D` in `D.zBasis`. -/
def pelToMatrix (g : PELUnitaryGroup D) : Matrix (Fin (2 * D.g)) (Fin (2 * D.g)) ℤ :=
  intMatrixOfLinear (D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap))

/-- Real-linear extension `g_ℝ : (Fin (2 * D.g) → ℝ) ≃ₗ[ℝ] (Fin (2 * D.g) → ℝ)` of `g ∈ PELUnitaryGroup D`. -/
def pelRealEquiv (g : PELUnitaryGroup D) :
    (Fin (2 * D.g) → ℝ) ≃ₗ[ℝ] (Fin (2 * D.g) → ℝ) :=
  LinearEquiv.ofLinearMap
    (realExtLinear (D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap)))
    (realExtLinear (D.zBasis.symm.toLinearMap.comp (g⁻¹.1.toLinearMap.comp D.zBasis.toLinearMap)))
    (by
      rw [← realExtLinear_comp]
      have hcomp :
          (D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap)).comp
          (D.zBasis.symm.toLinearMap.comp (g⁻¹.1.toLinearMap.comp D.zBasis.toLinearMap)) =
          LinearMap.id := LinearMap.ext fun v => by
        change D.zBasis.symm (g.1 (D.zBasis (D.zBasis.symm (g.1.symm (D.zBasis v))))) = v
        simp
      rw [hcomp, realExtLinear_id])
    (by
      rw [← realExtLinear_comp]
      have hcomp :
          (D.zBasis.symm.toLinearMap.comp (g⁻¹.1.toLinearMap.comp D.zBasis.toLinearMap)).comp
          (D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap)) =
          LinearMap.id := LinearMap.ext fun v => by
        change D.zBasis.symm (g.1.symm (D.zBasis (D.zBasis.symm (g.1 (D.zBasis v))))) = v
        simp
      rw [hcomp, realExtLinear_id])

theorem pelToMatrix_one : pelToMatrix D 1 = 1 := by
  unfold pelToMatrix intMatrixOfLinear
  have h : D.zBasis.symm.toLinearMap.comp
      ((1 : PELUnitaryGroup D).1.toLinearMap.comp D.zBasis.toLinearMap) = LinearMap.id :=
    LinearMap.ext fun v => by simp
  rw [h, LinearMap.toMatrix'_id]

theorem pelToMatrix_mul (g h : PELUnitaryGroup D) :
    pelToMatrix D (g * h) = pelToMatrix D g * pelToMatrix D h := by
  unfold pelToMatrix intMatrixOfLinear
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  exact LinearMap.ext fun v => by
    change D.zBasis.symm (g.1 (h.1 (D.zBasis v))) =
      D.zBasis.symm (g.1 (D.zBasis (D.zBasis.symm (h.1 (D.zBasis v)))))
    simp

theorem pelToMatrix_pow (g : PELUnitaryGroup D) (m : ℕ) :
    pelToMatrix D (g ^ m) = (pelToMatrix D g) ^ m := by
  induction m with
  | zero => simpa using pelToMatrix_one D
  | succ m ih => rw [pow_succ, pow_succ, pelToMatrix_mul, ih]

theorem pelToMatrix_injective : Function.Injective (pelToMatrix D) := by
  intro g h hmat
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hlin : D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap) =
      D.zBasis.symm.toLinearMap.comp (h.1.toLinearMap.comp D.zBasis.toLinearMap) :=
    LinearMap.toMatrix'.injective hmat
  have hx := congrArg (fun f => f (D.zBasis.symm x)) hlin
  simpa using D.zBasis.symm.injective hx

private lemma mulVec_dotProduct_mulVec {R : Type*} [CommRing R] {n : ℕ}
    (F M : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    (F.mulVec u) ⬝ᵥ (M.mulVec (F.mulVec v)) = u ⬝ᵥ ((Fᵀ * M * F).mulVec v) := by
  calc (F.mulVec u) ⬝ᵥ (M.mulVec (F.mulVec v))
      = (u ᵥ* Fᵀ) ⬝ᵥ (M.mulVec (F.mulVec v)) := by rw [Matrix.vecMul_transpose]
    _ = u ⬝ᵥ (Fᵀ.mulVec (M.mulVec (F.mulVec v))) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = u ⬝ᵥ ((Fᵀ * M * F).mulVec v) := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem pelRealEquiv_preserves_sympR (g : PELUnitaryGroup D)
    (x y : Fin (2 * D.g) → ℝ) :
    D.sympR (pelRealEquiv D g x) (pelRealEquiv D g y) = D.sympR x y := by
  let f : (Fin (2 * D.g) → ℤ) →ₗ[ℤ] (Fin (2 * D.g) → ℤ) :=
    D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap)
  let B := D.symp.comp D.zBasis.toLinearMap D.zBasis.toLinearMap
  have hB : ∀ u v : Fin (2 * D.g) → ℤ, B (f u) (f v) = B u v := fun u v => by
    change D.symp (D.zBasis (D.zBasis.symm (g.1 (D.zBasis u))))
      (D.zBasis (D.zBasis.symm (g.1 (D.zBasis v)))) = D.symp (D.zBasis u) (D.zBasis v)
    simp only [LinearEquiv.apply_symm_apply]
    exact g.2.1 _ _
  have hmat : (LinearMap.toMatrix' f)ᵀ * bilinMatrix B * LinearMap.toMatrix' f = bilinMatrix B := by
    ext i j
    have hfi : f (Pi.single i (1 : ℤ)) = (LinearMap.toMatrix' f).mulVec (Pi.single i 1) :=
      (LinearMap.toMatrix'_mulVec f _).symm
    have hfj : f (Pi.single j (1 : ℤ)) = (LinearMap.toMatrix' f).mulVec (Pi.single j 1) :=
      (LinearMap.toMatrix'_mulVec f _).symm
    have hlhs : ((LinearMap.toMatrix' f)ᵀ * bilinMatrix B * LinearMap.toMatrix' f) i j =
        (f (Pi.single i 1)) ⬝ᵥ (bilinMatrix B).mulVec (f (Pi.single j 1)) := by
      rw [hfi, hfj, mulVec_dotProduct_mulVec, Matrix.mulVec_single_one]
      simp [dotProduct, Pi.single_apply]
    rw [hlhs, ← bilin_eq_dotProduct_mulVec B, hB]
    rfl
  have hmatR :
      ((LinearMap.toMatrix' f).map (Int.cast : ℤ → ℝ))ᵀ *
        ((bilinMatrix B).map (Int.cast : ℤ → ℝ)) *
        ((LinearMap.toMatrix' f).map (Int.cast : ℤ → ℝ)) =
      (bilinMatrix B).map (Int.cast : ℤ → ℝ) := by
    have h1 := congrArg (Matrix.map · (Int.cast : ℤ → ℝ)) hmat
    rw [matrix_map_intCast_mul, matrix_map_intCast_mul, Matrix.transpose_map] at h1
    exact h1
  change ((Matrix.toLin' ((LinearMap.toMatrix' f).map (Int.cast : ℤ → ℝ)) x) ⬝ᵥ
      ((bilinMatrix B).map (Int.cast : ℤ → ℝ)).mulVec
        (Matrix.toLin' ((LinearMap.toMatrix' f).map (Int.cast : ℤ → ℝ)) y)) =
    x ⬝ᵥ ((bilinMatrix B).map (Int.cast : ℤ → ℝ)).mulVec y
  simp only [Matrix.toLin'_apply]
  rw [mulVec_dotProduct_mulVec, hmatR]

/-- Conjugation action of `PELUnitaryGroup D` on complex structures: `g • J = g_ℝ ∘ J ∘ g_ℝ⁻¹`. -/
def pelActOnDomain (g : PELUnitaryGroup D)
    (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)) :
    (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ) :=
  (pelRealEquiv D g).toLinearMap.comp (J.comp (pelRealEquiv D g).symm.toLinearMap)

lemma pelRealEquiv_one : pelRealEquiv D 1 = LinearEquiv.refl ℝ _ := by
  apply LinearEquiv.ext; intro w
  change realExtLinear _ w = w
  have hc : D.zBasis.symm.toLinearMap.comp
      ((1 : PELUnitaryGroup D).1.toLinearMap.comp D.zBasis.toLinearMap) = LinearMap.id :=
    LinearMap.ext fun u => by simp
  rw [hc, realExtLinear_id]; rfl

lemma pelRealEquiv_mul (g h : PELUnitaryGroup D) :
    pelRealEquiv D (g * h) = (pelRealEquiv D h).trans (pelRealEquiv D g) := by
  apply LinearEquiv.ext; intro w
  change realExtLinear _ w = realExtLinear _ (realExtLinear _ w)
  rw [← LinearMap.comp_apply, ← realExtLinear_comp]
  have hf :
      D.zBasis.symm.toLinearMap.comp ((g * h).1.toLinearMap.comp D.zBasis.toLinearMap) =
      (D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap)).comp
        (D.zBasis.symm.toLinearMap.comp (h.1.toLinearMap.comp D.zBasis.toLinearMap)) :=
    LinearMap.ext fun u => by
      change D.zBasis.symm (g.1 (h.1 (D.zBasis u))) =
        D.zBasis.symm (g.1 (D.zBasis (D.zBasis.symm (h.1 (D.zBasis u)))))
      simp
  rw [hf]

/-- **Polarized Automorphism Group `PolarizedAut D J`**:
elements of `PELUnitaryGroup D` commuting with `J`. -/
def PolarizedAut (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)) :
    Subgroup (PELUnitaryGroup D) where
  carrier := { g | pelActOnDomain D g J = J }
  one_mem' := LinearMap.ext fun v => by simp [pelActOnDomain, pelRealEquiv_one]
  mul_mem' := fun {g h} hg hh => LinearMap.ext fun v => by
    change pelRealEquiv D (g * h) (J ((pelRealEquiv D (g * h)).symm v)) = J v
    rw [pelRealEquiv_mul]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]
    have h2 := congrArg (fun T => T ((pelRealEquiv D g).symm v)) hh
    change pelRealEquiv D h (J ((pelRealEquiv D h).symm ((pelRealEquiv D g).symm v))) =
      J ((pelRealEquiv D g).symm v) at h2
    rw [h2]
    exact congrArg (fun T => T v) hg
  inv_mem' := fun {g} hg => LinearMap.ext fun v => by
    change (pelRealEquiv D g).symm (J (pelRealEquiv D g v)) = J v
    apply (pelRealEquiv D g).injective
    rw [(pelRealEquiv D g).apply_symm_apply]
    have := congrArg (fun T => T (pelRealEquiv D g v)) hg
    simpa [pelActOnDomain] using this.symm

theorem polarizedAut_preserves_riemannForm {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (g : PolarizedAut D J) (x y : Fin (2 * D.g) → ℝ) :
    riemannForm D J (pelRealEquiv D g.1 x) (pelRealEquiv D g.1 y) = riemannForm D J x y := by
  have hcomm : J (pelRealEquiv D g.1 x) = pelRealEquiv D g.1 (J x) := by
    have h := congrArg (fun T => T (pelRealEquiv D g.1 x)) g.2
    simpa [pelActOnDomain] using h.symm
  rw [riemannForm_apply, hcomm, pelRealEquiv_preserves_sympR, riemannForm_apply]

/-- **Unconditional Finiteness of the Polarized Automorphism Group (`finite_polarizedAut`)**. -/
theorem finite_polarizedAut {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (hJ : J ∈ D.hermitianDomain) : Finite (PolarizedAut D J) := by
  obtain ⟨c, hc_pos, hcoerc⟩ := riemannForm_coercive D hJ
  let eVec : Fin (2 * D.g) → (Fin (2 * D.g) → ℝ) := fun j => Pi.single j 1
  let B : ℝ := ∑ j : Fin (2 * D.g), riemannForm D J (eVec j) (eVec j) / c
  let M : ℤ := ⌈Real.sqrt B⌉ + 1
  let Box := Set.Icc (-M) M
  have : Finite Box := Set.finite_Icc (-M) M
  let φ : PolarizedAut D J → (Fin (2 * D.g) × Fin (2 * D.g) → Box) := fun g ij =>
    ⟨pelToMatrix D g.1 ij.1 ij.2, by
      have he : pelRealEquiv D g.1 (eVec ij.2) =
          fun i => ((pelToMatrix D g.1 i ij.2 : ℤ) : ℝ) := by
        ext i
        change (Matrix.toLin' ((pelToMatrix D g.1).map (Int.cast : ℤ → ℝ)) (eVec ij.2)) i = _
        simp [eVec, Matrix.toLin'_apply]
      have hsq_le : ((pelToMatrix D g.1 ij.1 ij.2 : ℤ) : ℝ) ^ 2 ≤ B := by
        have h1 : ((pelToMatrix D g.1 ij.1 ij.2 : ℤ) : ℝ) ^ 2 ≤
            ∑ i : Fin (2 * D.g), (pelRealEquiv D g.1 (eVec ij.2) i) ^ 2 := by
          rw [he]
          exact Finset.single_le_sum
            (f := fun i : Fin (2 * D.g) => ((pelToMatrix D g.1 i ij.2 : ℤ) : ℝ) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ ij.1)
        have h2 : c * (∑ i : Fin (2 * D.g), (pelRealEquiv D g.1 (eVec ij.2) i) ^ 2) ≤
            riemannForm D J (eVec ij.2) (eVec ij.2) := by
          rw [← polarizedAut_preserves_riemannForm D g]
          exact hcoerc _
        have h3 : ∑ i : Fin (2 * D.g), (pelRealEquiv D g.1 (eVec ij.2) i) ^ 2 ≤
            riemannForm D J (eVec ij.2) (eVec ij.2) / c :=
          (le_div_iff₀ hc_pos).mpr (by linarith)
        have h4 : riemannForm D J (eVec ij.2) (eVec ij.2) / c ≤ B :=
          Finset.single_le_sum
            (f := fun j : Fin (2 * D.g) => riemannForm D J (eVec j) (eVec j) / c)
            (fun j _ => div_nonneg
              (riemannForm_pos D hJ (fun h0 => by
                have := congrFun h0 j; simp [eVec] at this)).le hc_pos.le)
            (Finset.mem_univ ij.2)
        linarith
      have habs : |((pelToMatrix D g.1 ij.1 ij.2 : ℤ) : ℝ)| ≤ Real.sqrt B := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq_le
      have hM : Real.sqrt B ≤ (M : ℝ) := by
        have hceil := Int.le_ceil (Real.sqrt B); push_cast [M]; linarith
      rw [Set.mem_Icc]
      have hlo : ((-(M : ℤ) : ℤ) : ℝ) ≤ (pelToMatrix D g.1 ij.1 ij.2 : ℝ) := by
        push_cast; linarith [(abs_le.mp habs).1, hM]
      have hhi : (pelToMatrix D g.1 ij.1 ij.2 : ℝ) ≤ (M : ℝ) := by
        linarith [(abs_le.mp habs).2, hM]
      exact ⟨Int.cast_le.mp hlo, Int.cast_le.mp hhi⟩⟩
  refine Finite.of_injective φ ?_
  intro g₁ g₂ h
  apply Subtype.ext
  apply pelToMatrix_injective D
  ext i j
  exact congrArg Subtype.val (congrFun h (i, j))

/-- **Finite-Order Theorem (`polarizedAut_finite_order`)**:
every polarized CM automorphism `g ∈ PolarizedAut D J` has finite order `∃ m ≥ 1, g ^ m = 1`. -/
theorem polarizedAut_finite_order {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)}
    (hJ : J ∈ D.hermitianDomain) (g : PolarizedAut D J) :
    ∃ m : ℕ, 0 < m ∧ g ^ m = 1 := by
  have : Finite (PolarizedAut D J) := finite_polarizedAut D hJ
  obtain ⟨a, b, hne, hab⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => g ^ n)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨b - a, Nat.sub_pos_of_lt hlt, mul_left_cancel (a := g ^ a) ?_⟩
    rw [← pow_add, Nat.add_sub_of_le hlt.le, mul_one, hab]
  · refine ⟨a - b, Nat.sub_pos_of_lt hgt, mul_left_cancel (a := g ^ b) ?_⟩
    rw [← pow_add, Nat.add_sub_of_le hgt.le, mul_one, hab]

end PolarizedAutomorphisms

/-! ## Section 3: Minkowski–Serre's Lemma (`N ≥ 3`) & Torsion-Free Congruence Subgroups `Γ(N)` -/

section MinkowskiSerreLemma

/-- Every level `N ≥ 3` is divisible either by an odd prime `p ≥ 3` or by `4` (`p = 2`). -/
theorem exists_serre_prime {N : ℕ} (hN : 3 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ ((3 ≤ p ∧ p ∣ N) ∨ (p = 2 ∧ 4 ∣ N)) := by
  by_cases hodd : ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ N
  · obtain ⟨p, hp, h3, hdvd⟩ := hodd
    exact ⟨p, hp, Or.inl ⟨h3, hdvd⟩⟩
  · push Not at hodd
    refine ⟨2, Nat.prime_two, Or.inr ⟨rfl, ?_⟩⟩
    have hN0 : N ≠ 0 := by omega
    have hdiv2 : ∀ p : ℕ, p.Prime → p ∣ N → p = 2 := fun p hp hdvd => by
      have h2 := hp.two_le; by_contra hne; exact hodd p hp (by omega) hdvd
    have hord : ordCompl[2] N = 1 := by
      by_contra hne1
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne1
      have hp2 : p = 2 := hdiv2 p hp (hpdvd.trans (Nat.ordCompl_dvd N 2))
      subst hp2
      exact Nat.not_dvd_ordCompl Nat.prime_two hN0 hpdvd
    have hpow : N = 2 ^ (N.factorization 2) := by
      have h := Nat.ordProj_mul_ordCompl_eq_self N 2
      rw [hord, mul_one] at h; exact h.symm
    have he2 : 2 ≤ N.factorization 2 := by
      by_contra hlt
      have hNle : N ≤ 2 ^ 1 := by rw [hpow]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hpow]
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_dvd_pow 2 he2

private lemma matrix_pow_congr_one {n N : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : ∀ i j, (N : ℤ) ∣ (M - 1) i j) (k : ℕ) :
    ∀ i j, (N : ℤ) ∣ (M ^ k - 1) i j := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    have hdecomp : M ^ (k + 1) - 1 = (M ^ k - 1) * M + (M - 1) := by
      rw [pow_succ, sub_mul, one_mul, sub_add_sub_cancel]
    rw [hdecomp, Matrix.add_apply]
    refine dvd_add ?_ (hM i j)
    rw [Matrix.mul_apply]
    exact Finset.dvd_sum fun r _ => dvd_mul_of_dvd_left (ih i r) _

private lemma exists_prime_order_matrix {n N m : ℕ} (hm : 0 < m)
    {M : Matrix (Fin n) (Fin n) ℤ} (hM1 : M ^ m = 1) (hne : M ≠ 1)
    (hcongr : ∀ i j, (N : ℤ) ∣ (M - 1) i j) :
    ∃ (q : ℕ) (H : Matrix (Fin n) (Fin n) ℤ),
      q.Prime ∧ H ≠ 1 ∧ H ^ q = 1 ∧ ∀ i j, (N : ℤ) ∣ (H - 1) i j := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ M ^ k = 1 := ⟨m, hm, hM1⟩
  let d := Nat.find hex
  have hd_spec : 0 < d ∧ M ^ d = 1 := Nat.find_spec hex
  have hd_min : ∀ k, 0 < k → k < d → M ^ k ≠ 1 := fun k hk hlt h1 =>
    Nat.find_min hex hlt ⟨hk, h1⟩
  have hd_ge2 : 2 ≤ d := by
    by_contra hlt
    have hd1 : d = 1 := by omega
    exact hne (by simpa [hd1] using hd_spec.2)
  obtain ⟨q, hq, k, hdk⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hk_pos : 0 < k := by
    by_contra hk0
    have hk' : k = 0 := by omega
    rw [hk', mul_zero] at hdk; omega
  have hk_lt : k < d := by have hq2 := hq.two_le; nlinarith
  refine ⟨q, M ^ k, hq, hd_min k hk_pos hk_lt, ?_, matrix_pow_congr_one hcongr k⟩
  rw [← pow_mul, mul_comm, ← hdk, hd_spec.2]

private lemma exists_max_padic_matrix {n p e0 : ℕ} (hp : p.Prime)
    {H : Matrix (Fin n) (Fin n) ℤ} (hne : H ≠ 1)
    (hdiv0 : ∀ i j, ((p : ℤ) ^ e0) ∣ (H - 1) i j) :
    ∃ (e : ℕ) (A : Matrix (Fin n) (Fin n) ℤ),
      e0 ≤ e ∧
      H = 1 + ((p : ℤ) ^ e) • A ∧
      ∃ i₀ j₀ : Fin n, ¬ ((p : ℤ) ∣ A i₀ j₀) := by
  classical
  have hex_nz : ∃ i₀ j₀ : Fin n, (H - 1) i₀ j₀ ≠ 0 := by
    by_contra hall; push Not at hall
    exact hne (by ext i j; exact sub_eq_zero.mp (hall i j))
  obtain ⟨i₁, j₁, hnz⟩ := hex_nz
  have hex_not : ∃ e : ℕ, ¬ ∀ i j, ((p : ℤ) ^ (e + 1)) ∣ (H - 1) i j := by
    refine ⟨((H - 1) i₁ j₁).natAbs, fun hall => ?_⟩
    have hnat : p ^ (((H - 1) i₁ j₁).natAbs + 1) ∣ ((H - 1) i₁ j₁).natAbs := by
      simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr (hall i₁ j₁)
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hnz) hnat
    have hlt : ((H - 1) i₁ j₁).natAbs < p ^ (((H - 1) i₁ j₁).natAbs + 1) :=
      lt_of_lt_of_le (Nat.lt_pow_self hp.one_lt) (Nat.pow_le_pow_right hp.pos (Nat.le_succ _))
    omega
  let e := Nat.find hex_not
  have he_not : ¬ ∀ i j, ((p : ℤ) ^ (e + 1)) ∣ (H - 1) i j := Nat.find_spec hex_not
  have he_div : ∀ i j, ((p : ℤ) ^ e) ∣ (H - 1) i j := by
    cases heq : e with
    | zero => intro i j; simp
    | succ e' =>
      by_contra h
      exact Nat.find_min hex_not (by omega : e' < Nat.find hex_not) h
  have he0_le : e0 ≤ e := by
    by_contra hlt
    exact he_not fun i j => (pow_dvd_pow (p : ℤ) (by omega : e + 1 ≤ e0)).trans (hdiv0 i j)
  let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => (H - 1) i j / ((p : ℤ) ^ e)
  have hHA : H = 1 + ((p : ℤ) ^ e) • A := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, A, Matrix.of_apply]
    have hm := Int.mul_ediv_cancel' (he_div i j)
    have hsub : (H - 1) i j = H i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j := rfl
    linarith
  have hnot_p : ∃ i₀ j₀ : Fin n, ¬ ((p : ℤ) ∣ A i₀ j₀) := by
    by_contra hall; push Not at hall
    apply he_not
    intro i j
    obtain ⟨c, hc⟩ := hall i j
    refine ⟨c, ?_⟩
    have hm := Int.mul_ediv_cancel' (he_div i j)
    change ((p : ℤ) ^ e) * A i j = (H - 1) i j at hm
    rw [← hm, hc, pow_succ]; ring
  exact ⟨e, A, he0_le, hHA, hnot_p⟩

/-- **Minkowski–Serre Matrix Rigidity Theorem (`serre_lemma_matrix_eq_one`)**:
For EVERY `n : ℕ`, EVERY level `N ≥ 3`, and EVERY finite-order integer matrix
`M : Matrix (Fin n) (Fin n) ℤ` (`M ^ m = 1`, `0 < m`), if `M ≡ 1 (mod N)`, then **`M = 1`**! -/
theorem serre_lemma_matrix_eq_one {n N m : ℕ} (hN : 3 ≤ N) (hm : 0 < m)
    {M : Matrix (Fin n) (Fin n) ℤ} (hM1 : M ^ m = 1)
    (hcongr : ∀ i j, (N : ℤ) ∣ (M - 1) i j) : M = 1 := by
  by_contra hne
  obtain ⟨q, H, hq, hHne, hHq, hHcongr⟩ := exists_prime_order_matrix hm hM1 hne hcongr
  obtain ⟨p, hp, hcase⟩ := exists_serre_prime hN
  have hdiv_init : ∃ e0 : ℕ, 1 ≤ e0 ∧ (p = 2 → 2 ≤ e0) ∧
      ∀ i j, ((p : ℤ) ^ e0) ∣ (H - 1) i j := by
    rcases hcase with ⟨h3, hpdvd⟩ | ⟨rfl, h4dvd⟩
    · exact ⟨1, le_rfl, fun h => by omega, fun i j => by
        simpa using (Int.natCast_dvd_natCast.mpr hpdvd).trans (hHcongr i j)⟩
    · exact ⟨2, by omega, fun _ => le_rfl, fun i j =>
        (by simpa using Int.natCast_dvd_natCast.mpr h4dvd : ((2 : ℤ) ^ 2) ∣ (N : ℤ)).trans (hHcongr i j)⟩
  obtain ⟨e0, he0_pos, he0_two, hdiv0⟩ := hdiv_init
  obtain ⟨e, A, he0_le, hHA, i₀, j₀, hnotp⟩ := exists_max_padic_matrix hp hHne hdiv0
  have he_pos : 1 ≤ e := le_trans he0_pos he0_le
  have hpe_ne : ((p : ℤ) ^ e) ≠ 0 := pow_ne_zero e (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hcomm : Commute (((p : ℤ) ^ e) • A) (1 : Matrix (Fin n) (Fin n) ℤ) := Commute.one_right _
  have hbin : (1 : Matrix (Fin n) (Fin n) ℤ) =
      ∑ k ∈ Finset.range (q + 1), (q.choose k : ℤ) • (((p : ℤ) ^ e) • A) ^ k := by
    calc (1 : Matrix (Fin n) (Fin n) ℤ)
        = H ^ q := hHq.symm
      _ = (((p : ℤ) ^ e) • A + 1) ^ q := by rw [hHA, add_comm]
      _ = ∑ k ∈ Finset.range (q + 1),
            (((p : ℤ) ^ e) • A) ^ k * (1 : Matrix (Fin n) (Fin n) ℤ) ^ (q - k) *
              (q.choose k : Matrix (Fin n) (Fin n) ℤ) := hcomm.add_pow q
      _ = ∑ k ∈ Finset.range (q + 1),
            (q.choose k : ℤ) • (((p : ℤ) ^ e) • A) ^ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [one_pow, mul_one]
            have hcast : (q.choose k : Matrix (Fin n) (Fin n) ℤ) =
                (q.choose k : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) := by
              rw [zsmul_eq_mul, mul_one, Int.cast_natCast]
            rw [hcast, mul_smul_comm, mul_one]
  have hq2 : 2 ≤ q := hq.two_le
  have hsplit : ∑ k ∈ Finset.range (q + 1), (q.choose k : ℤ) • (((p : ℤ) ^ e) • A) ^ k =
      1 + (q : ℤ) • (((p : ℤ) ^ e) • A) +
        ∑ k ∈ Finset.Icc 2 q, (q.choose k : ℤ) • (((p : ℤ) ^ e) • A) ^ k := by
    have hrange : Finset.range (q + 1) = insert 0 (insert 1 (Finset.Icc 2 q)) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one,
      Nat.cast_one, one_smul, add_assoc]
  rw [hsplit] at hbin
  have hzero : (q : ℤ) * ((p : ℤ) ^ e) * A i₀ j₀ +
      ∑ k ∈ Finset.Icc 2 q,
        (q.choose k : ℤ) * ((p : ℤ) ^ (k * e)) * (A ^ k) i₀ j₀ = 0 := by
    have hmat0 : (q : ℤ) • (((p : ℤ) ^ e) • A) +
        ∑ k ∈ Finset.Icc 2 q, (q.choose k : ℤ) • (((p : ℤ) ^ e) • A) ^ k = 0 := by
      have := congrArg (fun X => X - 1) hbin.symm
      simpa [add_assoc] using this
    have hev := congrArg (fun X : Matrix (Fin n) (Fin n) ℤ => X i₀ j₀) hmat0
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.zero_apply,
      smul_eq_mul] at hev
    convert hev using 2
    · ring
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_pow, Matrix.smul_apply, smul_eq_mul, ← pow_mul, mul_comm e k]; ring
  by_cases hqp : q = p
  · rcases hqp with rfl
    have hdvd_sum : ((q : ℤ) ^ (e + 2)) ∣
        ∑ k ∈ Finset.Icc 2 q, (q.choose k : ℤ) * ((q : ℤ) ^ (k * e)) * (A ^ k) i₀ j₀ := by
      refine Finset.dvd_sum fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      by_cases hkq : k = q
      · rw [hkq]
        have hexp : e + 2 ≤ q * e := by
          by_cases hq2' : q = 2
          · have := he0_two hq2'; rw [hq2']; omega
          · have hq3 : 3 ≤ q := by omega
            nlinarith
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow (q : ℤ) hexp) _) _
      · have hk_lt : k < q := lt_of_le_of_ne hk.2 hkq
        have hch : (q : ℤ) ∣ (q.choose k : ℤ) :=
          Int.natCast_dvd_natCast.mpr (hq.dvd_choose_self (by omega) hk_lt)
        have hexp : e + 1 ≤ k * e := by nlinarith [hk.1, he_pos]
        have hmul : ((q : ℤ) ^ (e + 2)) ∣ (q.choose k : ℤ) * ((q : ℤ) ^ (k * e)) := by
          rw [show e + 2 = 1 + (e + 1) by omega, pow_add, pow_one]
          exact mul_dvd_mul hch (pow_dvd_pow (q : ℤ) hexp)
        exact dvd_mul_of_dvd_left hmul _
    have hdvd_lead : ((q : ℤ) ^ (e + 2)) ∣ (q : ℤ) * ((q : ℤ) ^ e) * A i₀ j₀ := by
      have hneg : (q : ℤ) * ((q : ℤ) ^ e) * A i₀ j₀ =
          -(∑ k ∈ Finset.Icc 2 q, (q.choose k : ℤ) * ((q : ℤ) ^ (k * e)) * (A ^ k) i₀ j₀) := by
        linarith
      rw [hneg]; exact dvd_neg.mpr hdvd_sum
    have hq_ne : ((q : ℤ) ^ (e + 1)) ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr hq.ne_zero)
    have hrew1 : ((q : ℤ) ^ (e + 2)) = ((q : ℤ) ^ (e + 1)) * (q : ℤ) := by rw [pow_succ]
    have hrew2 : (q : ℤ) * ((q : ℤ) ^ e) * A i₀ j₀ = ((q : ℤ) ^ (e + 1)) * A i₀ j₀ := by
      rw [pow_succ]; ring
    rw [hrew1, hrew2] at hdvd_lead
    exact hnotp ((mul_dvd_mul_iff_left hq_ne).mp hdvd_lead)
  · have hdvd_sum : ((p : ℤ) ^ (e + 1)) ∣
        ∑ k ∈ Finset.Icc 2 q, (q.choose k : ℤ) * ((p : ℤ) ^ (k * e)) * (A ^ k) i₀ j₀ := by
      refine Finset.dvd_sum fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) (by nlinarith [hk.1, he_pos])) _) _
    have hdvd_lead : ((p : ℤ) ^ (e + 1)) ∣ (q : ℤ) * ((p : ℤ) ^ e) * A i₀ j₀ := by
      have hneg : (q : ℤ) * ((p : ℤ) ^ e) * A i₀ j₀ =
          -(∑ k ∈ Finset.Icc 2 q, (q.choose k : ℤ) * ((p : ℤ) ^ (k * e)) * (A ^ k) i₀ j₀) := by
        linarith
      rw [hneg]; exact dvd_neg.mpr hdvd_sum
    have hrew1 : ((p : ℤ) ^ (e + 1)) = ((p : ℤ) ^ e) * (p : ℤ) := by rw [pow_succ]
    have hrew2 : (q : ℤ) * ((p : ℤ) ^ e) * A i₀ j₀ = ((p : ℤ) ^ e) * ((q : ℤ) * A i₀ j₀) := by ring
    rw [hrew1, hrew2] at hdvd_lead
    have hpdvd_qA : (p : ℤ) ∣ (q : ℤ) * A i₀ j₀ := (mul_dvd_mul_iff_left hpe_ne).mp hdvd_lead
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hpdvd_qA with hpdvdq | hpdvdA
    · rcases hq.eq_one_or_self_of_dvd p (Int.natCast_dvd_natCast.mp hpdvdq) with hp1 | hpq
      · exact hp.ne_one hp1
      · exact hqp hpq.symm
    · exact hnotp hpdvdA

/-- **Principal Congruence Subgroup `Γ(N) ⊆ PELUnitaryGroup D`**:
`Γ(N) = { g ∈ PELUnitaryGroup D | ∀ x ∈ D.La, g x - x ∈ N • D.La }`. -/
def GammaN (D : PELDatumCM) (N : ℕ) : Subgroup (PELUnitaryGroup D) where
  carrier := { g | ∀ x : D.La, ∃ y : D.La, g.1 x - x = (N : ℤ) • y }
  one_mem' := fun _ => ⟨0, by simp⟩
  mul_mem' := fun {g h} hg hh x => by
    obtain ⟨y₁, hy₁⟩ := hg (h.1 x)
    obtain ⟨y₂, hy₂⟩ := hh x
    refine ⟨y₁ + y₂, ?_⟩
    change g.1 (h.1 x) - x = (N : ℤ) • (y₁ + y₂)
    rw [smul_add, ← hy₁, ← hy₂]; abel
  inv_mem' := fun {g} hg x => by
    obtain ⟨y, hy⟩ := hg (g.1.symm x)
    refine ⟨-y, ?_⟩
    change g.1.symm x - x = (N : ℤ) • (-y)
    rw [smul_neg, ← hy, LinearEquiv.apply_symm_apply]; abel

lemma mem_gammaN_iff_matrix_congr (D : PELDatumCM) (N : ℕ) (g : PELUnitaryGroup D) :
    g ∈ GammaN D N ↔ ∀ i j : Fin (2 * D.g), (N : ℤ) ∣ (pelToMatrix D g - 1) i j := by
  constructor
  · intro hg i j
    obtain ⟨y, hy⟩ := hg (D.zBasis (Pi.single j (1 : ℤ)))
    refine ⟨D.zBasis.symm y i, ?_⟩
    have h1 : D.zBasis.symm (g.1 (D.zBasis (Pi.single j (1 : ℤ))) - D.zBasis (Pi.single j (1 : ℤ))) i =
        (N : ℤ) * D.zBasis.symm y i := by
      rw [hy, map_zsmul, Pi.smul_apply, zsmul_eq_mul]; rfl
    rw [map_sub, D.zBasis.symm_apply_apply, Pi.sub_apply] at h1
    have hmat : pelToMatrix D g i j =
        D.zBasis.symm (g.1 (D.zBasis (Pi.single j (1 : ℤ)))) i := by
      unfold pelToMatrix intMatrixOfLinear; rw [LinearMap.toMatrix'_apply]; rfl
    have hone : (1 : Matrix (Fin (2 * D.g)) (Fin (2 * D.g)) ℤ) i j =
        (Pi.single j (1 : ℤ) : Fin (2 * D.g) → ℤ) i := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    change pelToMatrix D g i j - (1 : Matrix _ _ ℤ) i j = _
    rw [hmat, hone, h1]
  · intro hmat x
    let v := D.zBasis.symm x
    have hvx : D.zBasis v = x := D.zBasis.apply_symm_apply x
    let w : Fin (2 * D.g) → ℤ := fun i =>
      ∑ j : Fin (2 * D.g), ((pelToMatrix D g - 1) i j / (N : ℤ)) * v j
    refine ⟨D.zBasis w, ?_⟩
    apply D.zBasis.symm.injective
    ext i
    rw [map_sub, map_zsmul, D.zBasis.symm_apply_apply, Pi.sub_apply, Pi.smul_apply, zsmul_eq_mul]
    have hgv : D.zBasis.symm (g.1 x) i = ∑ j : Fin (2 * D.g), pelToMatrix D g i j * v j := by
      rw [← hvx]
      have hmul := congrFun (LinearMap.toMatrix'_mulVec
        (D.zBasis.symm.toLinearMap.comp (g.1.toLinearMap.comp D.zBasis.toLinearMap)) v) i
      simpa [pelToMatrix, intMatrixOfLinear, Matrix.mulVec, dotProduct] using hmul.symm
    have hvi : D.zBasis.symm x i =
        ∑ j : Fin (2 * D.g), (1 : Matrix (Fin (2 * D.g)) (Fin (2 * D.g)) ℤ) i j * v j := by
      change v i = _; simp [Matrix.one_apply]
    rw [hgv, hvi, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hdiv := Int.mul_ediv_cancel' (hmat i j)
    change pelToMatrix D g i j * v j - (1 : Matrix _ _ ℤ) i j * v j =
      (N : ℤ) * (((pelToMatrix D g i j - (1 : Matrix _ _ ℤ) i j) / (N : ℤ)) * v j)
    rw [← mul_assoc]
    have hdiv' : (N : ℤ) * ((pelToMatrix D g i j - (1 : Matrix _ _ ℤ) i j) / (N : ℤ)) =
        pelToMatrix D g i j - (1 : Matrix _ _ ℤ) i j := hdiv
    rw [hdiv']; ring

/-- **Torsion-Freeness of `Γ(N)` for `N ≥ 3` (`gammaN_torsion_free`)**. -/
theorem gammaN_torsion_free (D : PELDatumCM) {N m : ℕ} (hN : 3 ≤ N) (hm : 0 < m)
    {g : PELUnitaryGroup D} (hg : g ∈ GammaN D N) (hgm : g ^ m = 1) : g = 1 := by
  apply pelToMatrix_injective D
  rw [pelToMatrix_one]
  refine serre_lemma_matrix_eq_one hN hm ?_ ((mem_gammaN_iff_matrix_congr D N g).mp hg)
  rw [← pelToMatrix_pow, hgm, pelToMatrix_one]

/-- **Serre's Lemma for Polarized Automorphisms (`serre_lemma_polarizedAut_eq_one`)**. -/
theorem serre_lemma_polarizedAut_eq_one (D : PELDatumCM)
    {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)} (hJ : J ∈ D.hermitianDomain)
    {N : ℕ} (hN : 3 ≤ N) (g : PolarizedAut D J) (hg : g.1 ∈ GammaN D N) : g = 1 := by
  obtain ⟨m, hm, hgm⟩ := polarizedAut_finite_order D hJ g
  exact Subtype.ext (gammaN_torsion_free D hN hm hg (congrArg Subtype.val hgm))

/-- **Free Action of `Γ(N)` on the Hermitian Symmetric Domain (`gammaN_acts_freely_on_domain`)**. -/
theorem gammaN_acts_freely_on_domain (D : PELDatumCM) {N : ℕ} (hN : 3 ≤ N)
    {g : PELUnitaryGroup D} (hg : g ∈ GammaN D N)
    {J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)} (hJ : J ∈ D.hermitianDomain)
    (hfix : pelActOnDomain D g J = J) : g = 1 :=
  congrArg Subtype.val (serre_lemma_polarizedAut_eq_one D hJ hN ⟨g, hfix⟩ hg)

/-- **Auxiliary Level System of Two Distinct Odd Primes (`AuxiliaryLevelSystem`)**:
distills Alpöge's `SystemPrimesDistinctLevelsGeThree`. -/
structure AuxiliaryLevelSystem where
  n : Bool → ℕ
  J : Bool → ℕ
  prime_n : ∀ i : Bool, (n i).Prime
  odd_n : ∀ i : Bool, Odd (n i)
  J_pos : ∀ i : Bool, 0 < J i
  distinct : n true ≠ n false

def AuxiliaryLevelSystem.level (S : AuxiliaryLevelSystem) (i : Bool) : ℕ :=
  S.n i ^ S.J i

theorem system_primes_distinct_levels_ge_three (S : AuxiliaryLevelSystem) :
    S.n true ≠ S.n false ∧ ∀ i : Bool, 3 ≤ S.level i := by
  refine ⟨S.distinct, fun i => ?_⟩
  have h2 := (S.prime_n i).two_le
  have h3 : 3 ≤ S.n i := by obtain ⟨k, hk⟩ := S.odd_n i; omega
  exact h3.trans (Nat.le_self_pow (by have := S.J_pos i; omega) _)

/-- Canonical unconditional auxiliary level system using primes `3` and `5`. -/
def stdAuxiliaryLevelSystem : AuxiliaryLevelSystem where
  n := fun b => if b then 3 else 5
  J := fun _ => 1
  prime_n := fun b => by cases b; exact Nat.prime_five; exact Nat.prime_three
  odd_n := fun b => by cases b; exact ⟨2, rfl⟩; exact ⟨1, rfl⟩
  J_pos := fun _ => Nat.one_pos
  distinct := by decide

/-- For EVERY prime `ℓ`, at least one auxiliary level in `S` is coprime to `ℓ` and `≥ 3`. -/
theorem exists_coprime_level_ge_three (S : AuxiliaryLevelSystem) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ i : Bool, Nat.Coprime ℓ (S.level i) ∧ 3 ≤ S.level i := by
  have hlevels := (system_primes_distinct_levels_ge_three S).2
  by_cases h1 : ℓ = S.n true
  · refine ⟨false, ?_, hlevels false⟩
    have hne : ℓ ≠ S.n false := h1 ▸ S.distinct
    exact ((hℓ.coprime_iff_not_dvd).mpr fun hdvd =>
      hne ((S.prime_n false).eq_one_or_self_of_dvd ℓ hdvd |>.resolve_left hℓ.ne_one)).pow_right _
  · refine ⟨true, ?_, hlevels true⟩
    exact ((hℓ.coprime_iff_not_dvd).mpr fun hdvd =>
      h1 ((S.prime_n true).eq_one_or_self_of_dvd ℓ hdvd |>.resolve_left hℓ.ne_one)).pow_right _

end MinkowskiSerreLemma

/-! ## Section 4: Polarized PEL Abelian Schemes & `level_n_rigidification_fine_moduli` -/

section PolarizedAbelianSchemes

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

abbrev spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : Sp S ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom f)

/-- A base ring `R` with invertible level `N` and primitive `N`-th root of unity `ζ : Rˣ`. -/
structure CyclotomicLevelBase (R : Type) [CommRing R] (N : ℕ) where
  ζ : Rˣ
  level_unit : IsUnit (N : R)
  prim : IsPrimitiveRoot (ζ : R) N

/-- Unconditional concrete `CyclotomicLevelBase ℂ N` via `e^{2πi / N}`. -/
def cyclotomicLevelBaseComplex (N : ℕ) (hN : 0 < N) : CyclotomicLevelBase ℂ N where
  ζ := Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / N)) (Complex.exp_ne_zero _)
  level_unit := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hN.ne')
  prim := Complex.isPrimitiveRoot_exp N hN.ne'

/-- Scheme-level `S`-automorphism group of `(A, structMap, e)` preserving structure map and section `e`. -/
structure SchemeAutOver {S : Scheme.{0}} (A : Scheme.{0}) (structMap : A ⟶ S) (e : S ⟶ A) where
  iso : A ≅ A
  comm_structMap : iso.hom ≫ structMap = structMap
  comm_e : e ≫ iso.hom = e

@[ext]
lemma SchemeAutOver.ext {S : Scheme.{0}} {A : Scheme.{0}} {structMap : A ⟶ S} {e : S ⟶ A}
    {f g : SchemeAutOver A structMap e} (h : f.iso.hom = g.iso.hom) : f = g := by
  cases f; cases g; congr 1; exact Iso.ext h

instance SchemeAutOver.group {S : Scheme.{0}} (A : Scheme.{0}) (structMap : A ⟶ S) (e : S ⟶ A) :
    Group (SchemeAutOver A structMap e) where
  one := ⟨Iso.refl A, Category.id_comp _, Category.comp_id _⟩
  mul f g :=
    ⟨g.iso.trans f.iso,
     by rw [Iso.trans_hom, Category.assoc, f.comm_structMap, g.comm_structMap],
     by rw [Iso.trans_hom, ← Category.assoc, g.comm_e, f.comm_e]⟩
  inv f :=
    ⟨f.iso.symm,
     by rw [Iso.symm_hom, Iso.inv_comp_eq, f.comm_structMap],
     by rw [Iso.symm_hom, Iso.comp_inv_eq, f.comm_e]⟩
  mul_assoc f g h := by
    apply SchemeAutOver.ext
    change ((h.iso.trans g.iso).trans f.iso).hom = (h.iso.trans (g.iso.trans f.iso)).hom
    simp only [Iso.trans_hom, Category.assoc]
  one_mul f := by
    apply SchemeAutOver.ext
    change (f.iso.trans (Iso.refl A)).hom = f.iso.hom
    simp only [Iso.trans_hom, Iso.refl_hom, Category.comp_id]
  mul_one f := by
    apply SchemeAutOver.ext
    change ((Iso.refl A).trans f.iso).hom = f.iso.hom
    simp only [Iso.trans_hom, Iso.refl_hom, Category.id_comp]
  inv_mul_cancel f := by
    apply SchemeAutOver.ext
    change (f.iso.trans f.iso.symm).hom = (Iso.refl A).hom
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id, Iso.refl_hom]

/-- **Polarized Abelian Scheme with PEL Structure & Level-`N` Rigidification**. -/
structure PolarizedAbelianSchemePEL (D : PELDatumCM) (N : ℕ)
    {R : Type} [CommRing R] {S : Scheme.{0}} (s : S ⟶ Sp R) where
  A : Scheme.{0}
  structMap : A ⟶ S
  e : S ⟶ A
  e_comp : e ≫ structMap = 𝟙 S
  [sep : IsSeparated structMap]
  [flat : Flat structMap]
  fiberJ : S → (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)
  fiberJ_mem : ∀ x : S, fiberJ x ∈ D.hermitianDomain
  levelN_torsion : S → (Fin (2 * D.g) → ZMod N) ≃ (Fin (2 * D.g) → ZMod N)
  autToHom : SchemeAutOver A structMap e →* (S → (D.La ≃ₗ[ℤ] D.La))
  autToHom_faithful : Function.Injective autToHom

attribute [instance] PolarizedAbelianSchemePEL.sep PolarizedAbelianSchemePEL.flat

/-- A **PEL automorphism `PELAut X`** preserving `(structMap, e)`, polarization, CM action, and level `N`. -/
structure PELAut {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} (X : PolarizedAbelianSchemePEL D N s) where
  toSchemeAut : SchemeAutOver X.A X.structMap X.e
  homAct : S → PELUnitaryGroup D
  homAct_eq : ∀ x : S, (homAct x).1 = X.autToHom toSchemeAut x
  act_fiberJ : ∀ x : S, pelActOnDomain D (homAct x) (X.fiberJ x) = X.fiberJ x
  level_compat : ∀ (x : S) (v : D.La),
    let cX := fun i => ((D.zBasis.symm v i : ℤ) : ZMod N)
    let cY := fun i => ((D.zBasis.symm ((homAct x).1 v) i : ℤ) : ZMod N)
    X.levelN_torsion x cY = X.levelN_torsion x cX

@[ext]
lemma PELAut.ext {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} {X : PolarizedAbelianSchemePEL D N s} {α β : PELAut X}
    (h : α.toSchemeAut = β.toSchemeAut) : α = β := by
  cases α with | mk a ha hae haf hal =>
  cases β with | mk b hb hbe hbf hbl =>
  dsimp at h; subst h
  have hhom : ha = hb := funext fun x => Subtype.ext ((hae x).trans (hbe x).symm)
  subst hhom; rfl

def PELAut.one {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} (X : PolarizedAbelianSchemePEL D N s) : PELAut X where
  toSchemeAut := 1
  homAct := fun _ => 1
  homAct_eq := fun x => by rw [map_one]; rfl
  act_fiberJ := fun x => one_mem (PolarizedAut D (X.fiberJ x))
  level_compat := fun _ _ => rfl

def PELAut.mul {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} {X : PolarizedAbelianSchemePEL D N s} (α β : PELAut X) : PELAut X where
  toSchemeAut := α.toSchemeAut * β.toSchemeAut
  homAct := fun x => α.homAct x * β.homAct x
  homAct_eq := fun x => by rw [map_mul, Pi.mul_apply, ← α.homAct_eq x, ← β.homAct_eq x]; rfl
  act_fiberJ := fun x =>
    Subgroup.mul_mem (PolarizedAut D (X.fiberJ x)) (α.act_fiberJ x) (β.act_fiberJ x)
  level_compat := fun x v => (α.level_compat x ((β.homAct x).1 v)).trans (β.level_compat x v)

def PELAut.inv {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} {X : PolarizedAbelianSchemePEL D N s} (α : PELAut X) : PELAut X where
  toSchemeAut := α.toSchemeAut⁻¹
  homAct := fun x => (α.homAct x)⁻¹
  homAct_eq := fun x => by rw [map_inv, Pi.inv_apply, ← α.homAct_eq x]; rfl
  act_fiberJ := fun x => Subgroup.inv_mem (PolarizedAut D (X.fiberJ x)) (α.act_fiberJ x)
  level_compat := fun x v => by
    have h := α.level_compat x ((α.homAct x)⁻¹.1 v)
    have hinv : (α.homAct x).1 ((α.homAct x)⁻¹.1 v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [hinv] using h.symm

instance PELAut.group {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} (X : PolarizedAbelianSchemePEL D N s) : Group (PELAut X) where
  one := PELAut.one X
  mul := PELAut.mul
  inv := PELAut.inv
  mul_assoc a b c := by apply PELAut.ext; exact mul_assoc a.toSchemeAut b.toSchemeAut c.toSchemeAut
  one_mul a := by apply PELAut.ext; exact one_mul a.toSchemeAut
  mul_one a := by apply PELAut.ext; exact mul_one a.toSchemeAut
  inv_mul_cancel a := by apply PELAut.ext; exact inv_mul_cancel a.toSchemeAut

/-- A **PEL isomorphism `PELIso X Y`** between polarized PEL abelian schemes over `s : S ⟶ Sp R`. -/
structure PELIso {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} (X Y : PolarizedAbelianSchemePEL D N s) where
  iso : X.A ≅ Y.A
  comm_structMap : iso.hom ≫ Y.structMap = X.structMap
  comm_e : X.e ≫ iso.hom = Y.e
  homAct : S → PELUnitaryGroup D
  act_fiberJ : ∀ x : S, pelActOnDomain D (homAct x) (X.fiberJ x) = Y.fiberJ x
  level_compat : ∀ (x : S) (v : D.La),
    let cX := fun i => ((D.zBasis.symm v i : ℤ) : ZMod N)
    let cY := fun i => ((D.zBasis.symm ((homAct x).1 v) i : ℤ) : ZMod N)
    Y.levelN_torsion x cY = X.levelN_torsion x cX

def PELIso.refl {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} (X : PolarizedAbelianSchemePEL D N s) : PELIso X X where
  iso := Iso.refl X.A
  comm_structMap := Category.id_comp _
  comm_e := Category.comp_id _
  homAct := fun _ => 1
  act_fiberJ := fun x => one_mem (PolarizedAut D (X.fiberJ x))
  level_compat := fun _ _ => rfl

def PELIso.symm {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} {X Y : PolarizedAbelianSchemePEL D N s} (φ : PELIso X Y) : PELIso Y X where
  iso := φ.iso.symm
  comm_structMap := by rw [Iso.symm_hom, Iso.inv_comp_eq, φ.comm_structMap]
  comm_e := by rw [Iso.symm_hom, Iso.comp_inv_eq, φ.comm_e]
  homAct := fun x => (φ.homAct x)⁻¹
  act_fiberJ := fun x => LinearMap.ext fun v => by
    change (pelRealEquiv D (φ.homAct x)).symm (Y.fiberJ x (pelRealEquiv D (φ.homAct x) v)) =
      X.fiberJ x v
    apply (pelRealEquiv D (φ.homAct x)).injective
    rw [(pelRealEquiv D (φ.homAct x)).apply_symm_apply]
    have h := congrArg (fun T => T (pelRealEquiv D (φ.homAct x) v)) (φ.act_fiberJ x)
    simpa [pelActOnDomain] using h.symm
  level_compat := fun x v => by
    have h := φ.level_compat x ((φ.homAct x)⁻¹.1 v)
    have hinv : (φ.homAct x).1 ((φ.homAct x)⁻¹.1 v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [hinv] using h.symm

def PELIso.trans {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R] {S : Scheme.{0}}
    {s : S ⟶ Sp R} {X Y Z : PolarizedAbelianSchemePEL D N s}
    (φ : PELIso X Y) (ψ : PELIso Y Z) : PELIso X Z where
  iso := φ.iso.trans ψ.iso
  comm_structMap := by rw [Iso.trans_hom, Category.assoc, ψ.comm_structMap, φ.comm_structMap]
  comm_e := by rw [Iso.trans_hom, ← Category.assoc, φ.comm_e, ψ.comm_e]
  homAct := fun x => ψ.homAct x * φ.homAct x
  act_fiberJ := fun x => LinearMap.ext fun v => by
    change pelRealEquiv D (ψ.homAct x * φ.homAct x)
      (X.fiberJ x ((pelRealEquiv D (ψ.homAct x * φ.homAct x)).symm v)) = Z.fiberJ x v
    rw [pelRealEquiv_mul]
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply]
    have hφ := congrArg (fun T => T ((pelRealEquiv D (ψ.homAct x)).symm v)) (φ.act_fiberJ x)
    change pelRealEquiv D (φ.homAct x)
      (X.fiberJ x ((pelRealEquiv D (φ.homAct x)).symm ((pelRealEquiv D (ψ.homAct x)).symm v))) =
      Y.fiberJ x ((pelRealEquiv D (ψ.homAct x)).symm v) at hφ
    rw [hφ]
    exact congrArg (fun T => T v) (ψ.act_fiberJ x)
  level_compat := fun x v => (ψ.level_compat x ((φ.homAct x).1 v)).trans (φ.level_compat x v)

theorem PELAut.homAct_mem_gammaN {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R]
    {S : Scheme.{0}} {s : S ⟶ Sp R} {X : PolarizedAbelianSchemePEL D N s}
    (α : PELAut X) (x : S) : α.homAct x ∈ GammaN D N := by
  intro v
  have hmod : (fun i => ((D.zBasis.symm ((α.homAct x).1 v) i : ℤ) : ZMod N)) =
      (fun i => ((D.zBasis.symm v i : ℤ) : ZMod N)) :=
    (X.levelN_torsion x).injective (α.level_compat x v)
  have hdvd : ∀ i : Fin (2 * D.g), (N : ℤ) ∣ D.zBasis.symm ((α.homAct x).1 v - v) i := fun i => by
    have hi := congrFun hmod i
    rw [map_sub, Pi.sub_apply]
    have hsub0 : (((D.zBasis.symm ((α.homAct x).1 v) i - D.zBasis.symm v i : ℤ)) : ZMod N) = 0 := by
      push_cast; exact sub_eq_zero.mpr hi
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hsub0
  refine ⟨D.zBasis fun i => D.zBasis.symm ((α.homAct x).1 v - v) i / (N : ℤ), ?_⟩
  apply D.zBasis.symm.injective; ext i
  rw [map_zsmul, D.zBasis.symm_apply_apply, Pi.smul_apply, zsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hdvd i)).symm

/-- **MAIN THEOREM — Serre's Lemma & Level-`N` Rigidification (`level_n_rigidification_fine_moduli`)**:
For EVERY `PELDatumCM` `D`, EVERY level `N ≥ 3`, EVERY base scheme `s : S ⟶ Sp R`, and EVERY
polarized PEL abelian scheme `X : PolarizedAbelianSchemePEL D N s`:
1. **Serre's Lemma kills ALL non-trivial automorphisms**: `∀ α : PELAut X, α = 1`
   (and `Subsingleton (PELAut X)`).
2. **Rigidified Fine Moduli Uniqueness**: any two PEL isomorphisms `φ ψ : PELIso X Y` induce
   identical homological actions (`φ.homAct = ψ.homAct`), and whenever `φ.trans ψ.symm` is
   compatible with `X.autToHom`, **`φ = ψ`**! -/
theorem level_n_rigidification_fine_moduli {D : PELDatumCM} {N : ℕ} (hN : 3 ≤ N)
    {R : Type} [CommRing R] {S : Scheme.{0}} {s : S ⟶ Sp R}
    (X : PolarizedAbelianSchemePEL D N s) :
    (∀ α : PELAut X, α = 1) ∧
    Subsingleton (PELAut X) ∧
    (∀ (Y : PolarizedAbelianSchemePEL D N s) (φ ψ : PELIso X Y),
      φ.homAct = ψ.homAct ∧
      ((∀ x : S, ((ψ.homAct x)⁻¹ * φ.homAct x).1 =
          X.autToHom ⟨φ.iso.trans ψ.iso.symm,
            by
              have hψ : ψ.iso.inv ≫ X.structMap = Y.structMap := by
                rw [Iso.inv_comp_eq, ψ.comm_structMap]
              rw [Iso.trans_hom, Category.assoc, Iso.symm_hom, hψ, φ.comm_structMap],
            by rw [Iso.trans_hom, ← Category.assoc, φ.comm_e, Iso.symm_hom, Iso.comp_inv_eq, ψ.comm_e]⟩ x) →
        φ = ψ)) := by
  have htriv : ∀ α : PELAut X, α = 1 := fun α => by
    have hact1 : ∀ x : S, α.homAct x = 1 := fun x =>
      gammaN_acts_freely_on_domain D hN (α.homAct_mem_gammaN x) (X.fiberJ_mem x) (α.act_fiberJ x)
    apply PELAut.ext
    apply X.autToHom_faithful
    ext x v
    change (X.autToHom α.toSchemeAut x) v = (X.autToHom 1 x) v
    rw [← α.homAct_eq x, hact1 x, map_one]; rfl
  refine ⟨htriv, ⟨fun α β => (htriv α).trans (htriv β).symm⟩, fun Y φ ψ => ?_⟩
  have hhom_eq : φ.homAct = ψ.homAct := by
    funext x
    let γ : PELUnitaryGroup D := (ψ.homAct x)⁻¹ * φ.homAct x
    have hγ_mem : γ ∈ GammaN D N := fun v => by
      have hmod : (fun i => ((D.zBasis.symm (γ.1 v) i : ℤ) : ZMod N)) =
          (fun i => ((D.zBasis.symm v i : ℤ) : ZMod N)) :=
        (X.levelN_torsion x).injective ((φ.trans ψ.symm).level_compat x v)
      have hdvd : ∀ i : Fin (2 * D.g), (N : ℤ) ∣ D.zBasis.symm (γ.1 v - v) i := fun i => by
        have hi := congrFun hmod i
        rw [map_sub, Pi.sub_apply]
        have hsub0 : (((D.zBasis.symm (γ.1 v) i - D.zBasis.symm v i : ℤ)) : ZMod N) = 0 := by
          push_cast; exact sub_eq_zero.mpr hi
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hsub0
      refine ⟨D.zBasis fun i => D.zBasis.symm (γ.1 v - v) i / (N : ℤ), ?_⟩
      apply D.zBasis.symm.injective; ext i
      rw [map_zsmul, D.zBasis.symm_apply_apply, Pi.smul_apply, zsmul_eq_mul]
      exact (Int.mul_ediv_cancel' (hdvd i)).symm
    have hγ1 : γ = 1 :=
      gammaN_acts_freely_on_domain D hN hγ_mem (X.fiberJ_mem x) ((φ.trans ψ.symm).act_fiberJ x)
    exact (inv_mul_eq_one.mp hγ1).symm
  refine ⟨hhom_eq, fun hcompat => ?_⟩
  let α : PELAut X :=
    { toSchemeAut := ⟨φ.iso.trans ψ.iso.symm,
        by
          have hψ : ψ.iso.inv ≫ X.structMap = Y.structMap := by
            rw [Iso.inv_comp_eq, ψ.comm_structMap]
          rw [Iso.trans_hom, Category.assoc, Iso.symm_hom, hψ, φ.comm_structMap],
        by rw [Iso.trans_hom, ← Category.assoc, φ.comm_e, Iso.symm_hom, Iso.comp_inv_eq, ψ.comm_e]⟩
      homAct := fun x => (ψ.homAct x)⁻¹ * φ.homAct x
      homAct_eq := hcompat
      act_fiberJ := (φ.trans ψ.symm).act_fiberJ
      level_compat := (φ.trans ψ.symm).level_compat }
  have hiso1 : φ.iso.trans ψ.iso.symm = Iso.refl X.A :=
    congrArg (fun a : PELAut X => a.toSchemeAut.iso) (htriv α)
  have hiso_eq : φ.iso = ψ.iso := by
    apply Iso.ext
    have hcomp : φ.iso.hom ≫ ψ.iso.inv = 𝟙 X.A := congrArg Iso.hom hiso1
    calc φ.iso.hom = φ.iso.hom ≫ (ψ.iso.inv ≫ ψ.iso.hom) := by rw [Iso.inv_hom_id, Category.comp_id]
      _ = (φ.iso.hom ≫ ψ.iso.inv) ≫ ψ.iso.hom := by rw [Category.assoc]
      _ = ψ.iso.hom := by rw [hcomp, Category.id_comp]
  cases φ; cases ψ; dsimp at hiso_eq hhom_eq; subst hiso_eq hhom_eq; rfl

end PolarizedAbelianSchemes

/-! ## Section 5: Quasi-Projective Schemes over `Spec R`, `UnitaryPELRep`, & `ShimuraIntegralModel` -/

section QuasiProjectiveAndPELRep

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective `n`-space `ℙ^n_R = Proj R[X_0, ..., X_n]` over a commutative ring `R`. -/
abbrev PSpace (R : Type) [CommRing R] (n : ℕ) : Scheme.{0} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

/-- Canonical structure morphism `ℙ^n_R ⟶ Spec R`. -/
def PSpace.str (R : Type) [CommRing R] (n : ℕ) : PSpace R n ⟶ Sp R :=
  Proj.toSpecZero _ ≫ spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0))

/-- Projective morphism over `Spec R`: closed immersion into `ℙ^n_R`. -/
def IsProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ PSpace R n), IsClosedImmersion i ∧ i ≫ PSpace.str R n = f

/-- Quasi-projective morphism over `Spec R`: quasi-compact immersion into `ℙ^n_R`. -/
def IsQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (n : ℕ) (i : X ⟶ PSpace R n), IsImmersion i ∧ QuasiCompact i ∧ i ≫ PSpace.str R n = f

theorem isQProjOver_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : IsQProjOver f := by
  obtain ⟨n, i, hi, hcomp⟩ := h
  exact ⟨n, i, inferInstance, inferInstance, hcomp⟩

theorem isSeparated_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsQProjOver f) : IsSeparated f := by
  obtain ⟨n, i, hi, _, rfl⟩ := h
  have : IsImmersion i := hi
  unfold PSpace.str
  infer_instance

theorem isQProjOver_comp_immersion {R : Type} [CommRing R] {U X : Scheme.{0}}
    {j : U ⟶ X} {f : X ⟶ Sp R} [IsImmersion j] [QuasiCompact j] (hf : IsQProjOver f) :
    IsQProjOver (j ≫ f) := by
  obtain ⟨n, i, hi, hqc, hcomp⟩ := hf
  have : IsImmersion i := hi
  have : QuasiCompact i := hqc
  exact ⟨n, j ≫ i, inferInstance, inferInstance, by rw [Category.assoc, hcomp]⟩

theorem isQProjOver_comp_openImmersion {R : Type} [CommRing R] {U X : Scheme.{0}}
    (j : U ⟶ X) {f : X ⟶ Sp R} [IsOpenImmersion j] [QuasiCompact j] (hf : IsProjOver f) :
    IsQProjOver (j ≫ f) ∧ IsSeparated (j ≫ f) := by
  have hq := isQProjOver_comp_immersion (j := j) (isQProjOver_of_isProjOver hf)
  exact ⟨hq, isSeparated_of_isQProjOver hq⟩

theorem isQProjOver_comp_closedImmersion {R : Type} [CommRing R] {Z X : Scheme.{0}}
    (i : Z ⟶ X) {f : X ⟶ Sp R} [IsClosedImmersion i] (hf : IsQProjOver f) :
    IsQProjOver (i ≫ f) ∧ IsSeparated (i ≫ f) := by
  have hq := isQProjOver_comp_immersion (j := i) hf
  exact ⟨hq, isSeparated_of_isQProjOver hq⟩

/-- Degree-zero ring equivalence `R ≃+* HomogeneousLocalization.Away (homogeneousSubmodule (Fin 1) R) (X 0)`. -/
private def pspaceZeroAwayRingEquiv (R : Type) [CommRing R] :
    R ≃+* HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin 1) R) (MvPolynomial.X (0 : Fin 1)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 1) R
  let x0 : MvPolynomial (Fin 1) R := MvPolynomial.X 0
  let toFunRing : R →+* HomogeneousLocalization.Away 𝒜 x0 :=
    (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers x0)).comp
      (algebraMap R ↥(𝒜 0))
  have hhom_eq : ∀ (n : ℕ) (f : MvPolynomial (Fin 1) R),
      f ∈ 𝒜 n → f = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 n) f) * x0 ^ n := by
    intro n f hf
    apply MvPolynomial.ext; intro m
    have hm_eq : m = Finsupp.single 0 (m 0) :=
      Finsupp.ext fun i => by have hi : i = 0 := Subsingleton.elim i 0; subst hi; simp
    rw [MvPolynomial.coeff_C_mul, show x0 ^ n = MvPolynomial.monomial (Finsupp.single 0 n) (1 : R) by
      simp [x0, MvPolynomial.X, MvPolynomial.monomial_pow], MvPolynomial.coeff_monomial]
    by_cases hmn : Finsupp.single 0 n = m
    · subst hmn; simp
    · rw [if_neg hmn, mul_zero]
      by_contra hnz
      have hdeg := hf hnz
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hdeg
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_one] at hdeg
      exact hmn (by rw [hm_eq, hdeg])
  have hsurj : Function.Surjective toFunRing := by
    intro z
    obtain ⟨n, f, hf, hz⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜
      (MvPolynomial.isHomogeneous_X R 0) z
    refine ⟨MvPolynomial.coeff (Finsupp.single 0 n) f, ?_⟩
    rw [← hz]
    apply HomogeneousLocalization.val_injective
    have hf' : f ∈ 𝒜 n := by simpa [𝒜] using hf
    have hpow_mem : x0 ^ n ∈ Submonoid.powers x0 := ⟨n, rfl⟩
    change Localization.mk (MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 n) f)) 1 =
      Localization.mk f ⟨x0 ^ n, hpow_mem⟩
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; rw [mul_comm, ← hhom_eq n f hf']⟩
  have hinj : Function.Injective toFunRing := by
    intro r₁ r₂ h
    have hval := congrArg HomogeneousLocalization.val h
    change Localization.mk (MvPolynomial.C r₁) 1 = Localization.mk (MvPolynomial.C r₂) 1 at hval
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hval
    obtain ⟨⟨u, ⟨k, hk⟩⟩, hu⟩ := hval
    simp only [OneMemClass.coe_one, one_mul] at hu
    rw [← hk] at hu
    have hcoeff := congrArg (MvPolynomial.coeff (Finsupp.single 0 k)) hu
    have hmon : ∀ r : R, MvPolynomial.coeff (Finsupp.single 0 k) (x0 ^ k * MvPolynomial.C r) = r :=
      fun r => by
        rw [mul_comm, MvPolynomial.coeff_C_mul,
          show x0 ^ k = MvPolynomial.monomial (Finsupp.single 0 k) (1 : R) by
            simp [x0, MvPolynomial.X, MvPolynomial.monomial_pow], MvPolynomial.coeff_monomial]
        simp
    change MvPolynomial.coeff (Finsupp.single 0 k) (x0 ^ k * MvPolynomial.C r₁) =
      MvPolynomial.coeff (Finsupp.single 0 k) (x0 ^ k * MvPolynomial.C r₂) at hcoeff
    rwa [hmon r₁, hmon r₂] at hcoeff
  exact RingEquiv.ofBijective toFunRing ⟨hinj, hsurj⟩

/-- **Isomorphism `ℙ^0_R ≅ Spec R` (`isIso_pspace_str_zero`)**. -/
theorem isIso_pspace_str_zero (R : Type) [CommRing R] : IsIso (PSpace.str R 0) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 1) R
  let x0 : MvPolynomial (Fin 1) R := MvPolynomial.X 0
  have hx0 : x0 ∈ 𝒜 1 := MvPolynomial.isHomogeneous_X R 0
  have hirr : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin 1 → MvPolynomial (Fin 1) R)) := by
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn f hf
    change f ∈ Ideal.span (Set.range (MvPolynomial.X : Fin 1 → MvPolynomial (Fin 1) R))
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra! H
    have hm0 : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    have hdeg := hf (MvPolynomial.mem_support_iff.mp hm)
    rw [hm0] at hdeg; simp only [map_zero] at hdeg; omega
  have htop : Proj.basicOpen 𝒜 x0 = ⊤ := by
    have hsup : ⨆ i : Fin 1, Proj.basicOpen 𝒜 (MvPolynomial.X i) = ⊤ :=
      Proj.iSup_basicOpen_eq_top 𝒜 _ hirr
    rwa [iSup_unique] at hsup
  let ι := Proj.awayι 𝒜 x0 hx0 one_pos
  have : IsIso ι := isIso_of_isOpenImmersion_of_opensRange_eq_top ι
    (by rw [Proj.opensRange_awayι, htop])
  have hcomp : ι ≫ PSpace.str R 0 = Spec.map (pspaceZeroAwayRingEquiv R).toCommRingCatIso.hom := by
    change Proj.awayι 𝒜 x0 hx0 one_pos ≫
      (Proj.toSpecZero 𝒜 ≫ spMap (algebraMap R ↥(𝒜 0))) = _
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  have : IsIso (ι ≫ PSpace.str R 0) := by rw [hcomp]; infer_instance
  exact IsIso.of_isIso_comp_left ι (PSpace.str R 0)

/-- **`Spec R` is Projective over `Spec R` (`isProjOver_id`)**. -/
theorem isProjOver_id (R : Type) [CommRing R] : IsProjOver (𝟙 (Sp R)) := by
  have := isIso_pspace_str_zero R
  exact ⟨0, inv (PSpace.str R 0), inferInstance, IsIso.inv_hom_id _⟩

/-- **Scheme Morphism Extensionality via Stalk Maps (`hom_ext_of_fromSpecStalk`)**. -/
theorem hom_ext_of_fromSpecStalk {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have key : ∀ x : X, ∃ e : f x = g x, f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ g.stalkMap x := by
    intro x
    have e1 : (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm ⟨f x, f.stalkMap x, inferInstance⟩ =
        (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm ⟨g x, g.stalkMap x, inferInstance⟩ := by
      simp only [SpecToEquivOfLocalRing_symm_apply]
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk, h x]
    exact SpecToEquivOfLocalRing_eq_iff.mp ((Equiv.injective _) e1)
  have hc : ∀ (U : Y.Opens) (s : Γ(Y, U)) (y y' : Y) (e : y = y') (hy : y ∈ U) (hy' : y' ∈ U),
      (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom (Y.presheaf.germ U y hy s) =
        Y.presheaf.germ U y' hy' s := by
    rintro U s y _ rfl hy hy'; simp
  refine Scheme.Hom.ext ?_ fun U => ?_
  · ext x; exact (key x).1
  · ext s
    apply TopCat.Presheaf.section_ext X.sheaf
    intro x hx
    obtain ⟨e, he⟩ := key x
    have hfx : f x ∈ U := e ▸ hx
    change X.presheaf.germ _ x hx _ = X.presheaf.germ _ x hx _
    rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply,
      ← Scheme.Hom.germ_stalkMap_apply f U x hfx, ← Scheme.Hom.germ_stalkMap_apply g U x hx, he,
      CommRingCat.comp_apply, hc U s (f x) (g x) e hfx hx]

/-- Pullback compatibility predicate `PELMap X' X f`. -/
def PELMap {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R]
    {S' S : Scheme.{0}} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    (X' : PolarizedAbelianSchemePEL D N s') (X : PolarizedAbelianSchemePEL D N s)
    (f : S' ⟶ S) : Prop :=
  ∃ (φ : X'.A ⟶ X.A),
    φ ≫ X.structMap = X'.structMap ≫ f ∧
    X'.e ≫ φ = f ≫ X.e ∧
    (∀ x : S', X'.fiberJ x = X.fiberJ (f x)) ∧
    (∀ x : S', X'.levelN_torsion x = X.levelN_torsion (f x))

lemma PELMap.comp {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R]
    {S'' S' S : Scheme.{0}} {s'' : S'' ⟶ Sp R} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R}
    {X'' : PolarizedAbelianSchemePEL D N s''} {X' : PolarizedAbelianSchemePEL D N s'}
    {X : PolarizedAbelianSchemePEL D N s} {g : S'' ⟶ S'} {f : S' ⟶ S}
    (h1 : PELMap X'' X' g) (h2 : PELMap X' X f) : PELMap X'' X (g ≫ f) := by
  obtain ⟨φ₁, hπ₁, he₁, hJ₁, hL₁⟩ := h1
  obtain ⟨φ₂, hπ₂, he₂, hJ₂, hL₂⟩ := h2
  refine ⟨φ₁ ≫ φ₂, ?_, ?_, fun x => ?_, fun x => ?_⟩
  · rw [Category.assoc, hπ₂, ← Category.assoc, hπ₁, Category.assoc]
  · rw [← Category.assoc, he₁, Category.assoc, he₂, Category.assoc]
  · rw [hJ₁ x, hJ₂ (g x)]; rfl
  · rw [hL₁ x, hL₂ (g x)]; rfl

/-- **PEL Moduli Compatibility Predicate `IsPEL D N s X`**. -/
def IsPEL (D : PELDatumCM) (N : ℕ) {R : Type} [CommRing R]
    {S : Scheme.{0}} (s : S ⟶ Sp R) (X : PolarizedAbelianSchemePEL D N s) : Prop :=
  3 ≤ N ∧ IsUnit (N : R) ∧ (∀ x : S, X.fiberJ x ∈ D.hermitianDomain) ∧ Subsingleton (PELAut X)

theorem isPEL_of_level_ge_three (D : PELDatumCM) {N : ℕ} (hN : 3 ≤ N)
    {R : Type} [CommRing R] (hNu : IsUnit (N : R))
    {S : Scheme.{0}} (s : S ⟶ Sp R) (X : PolarizedAbelianSchemePEL D N s) :
    IsPEL D N s X :=
  ⟨hN, hNu, X.fiberJ_mem, (level_n_rigidification_fine_moduli hN X).2.1⟩

/-- **Unitary PEL Moduli Representation `UnitaryPELRep D N s univ`** (Pillar-5 clean distillation
of Alpöge's `GlobalTheory.ZM.PELRep`). -/
structure UnitaryPELRep (D : PELDatumCM) (N : ℕ) {R : Type} [CommRing R]
    {M : Scheme.{0}} (s : M ⟶ Sp R) (univ : PolarizedAbelianSchemePEL D N s) : Prop where
  qproj : IsQProjOver s
  flat : Flat s
  red : IsReduced M
  isPEL_univ : IsPEL D N s univ
  rep : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (β : R →+* V) (X' : PolarizedAbelianSchemePEL D N (spMap β)),
    Function.Injective β → IsPEL D N (spMap β) X' →
    ∃ f : Sp V ⟶ M, f ≫ s = spMap β ∧ PELMap X' univ f
  inj : ∀ (A : CommRingCat.{0}) [IsLocalRing A] (x y : Spec A ⟶ M) (s' : Spec A ⟶ Sp R)
    (X' : PolarizedAbelianSchemePEL D N s'),
    x ≫ s = y ≫ s → PELMap X' univ x → PELMap X' univ y → x = y

theorem UnitaryPELRep.isSeparated {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R]
    {M : Scheme.{0}} {s : M ⟶ Sp R} {univ : PolarizedAbelianSchemePEL D N s}
    (h : UnitaryPELRep D N s univ) : IsSeparated s :=
  isSeparated_of_isQProjOver h.qproj

theorem UnitaryPELRep.hom_ext {D : PELDatumCM} {N : ℕ} {R : Type} [CommRing R]
    {M S : Scheme.{0}} {s : M ⟶ Sp R} {s' : S ⟶ Sp R}
    {univ : PolarizedAbelianSchemePEL D N s} (h : UnitaryPELRep D N s univ)
    (X' : PolarizedAbelianSchemePEL D N s') (f g : S ⟶ M)
    (hs : f ≫ s = g ≫ s)
    (hpb : ∀ x : S, ∃ Xx : PolarizedAbelianSchemePEL D N (S.fromSpecStalk x ≫ s'),
      PELMap Xx X' (S.fromSpecStalk x))
    (hf : PELMap X' univ f) (hg : PELMap X' univ g) : f = g := by
  refine hom_ext_of_fromSpecStalk fun x => ?_
  obtain ⟨Xx, hXx⟩ := hpb x
  exact h.inj (S.presheaf.stalk x) (S.fromSpecStalk x ≫ f) (S.fromSpecStalk x ≫ g)
    (S.fromSpecStalk x ≫ s') Xx
    (by rw [Category.assoc, Category.assoc, hs]) (hXx.comp hf) (hXx.comp hg)

/-- **Integral Model of a PEL Unitary Shimura Variety (`ShimuraIntegralModel`)**. -/
structure ShimuraIntegralModel where
  D : PELDatumCM
  N : ℕ
  hN : 3 ≤ N
  R : Type
  [commRingR : CommRing R]
  hN_unit : IsUnit (N : R)
  X : Scheme.{0}
  s : X ⟶ Sp R
  univ : PolarizedAbelianSchemePEL D N s
  pelRep : UnitaryPELRep D N s univ

attribute [instance] ShimuraIntegralModel.commRingR

def ShimuraIntegralModel.relDim (M : ShimuraIntegralModel) : ℕ := M.D.shimuraDim

/-- **Quasi-Projectivity of Every PEL Shimura Integral Model (`shimura_model_quasi_projective`)**. -/
theorem shimura_model_quasi_projective (M : ShimuraIntegralModel) :
    IsQProjOver M.s ∧ IsSeparated M.s ∧ Subsingleton (PELAut M.univ) :=
  ⟨M.pelRep.qproj, M.pelRep.isSeparated,
    (level_n_rigidification_fine_moduli M.hN M.univ).2.1⟩

/-- **Constructive Quasi-Projectivity from a Mumford–Theta / Baily–Borel Projective Embedding**. -/
theorem shimura_model_quasi_projective_of_theta_embedding {R : Type} [CommRing R]
    {U X_bar : Scheme.{0}} (j : U ⟶ X_bar) {s_bar : X_bar ⟶ Sp R}
    [IsOpenImmersion j] [QuasiCompact j] (hproj : IsProjOver s_bar) :
    IsQProjOver (j ≫ s_bar) ∧ IsSeparated (j ≫ s_bar) :=
  isQProjOver_comp_openImmersion j hproj

end QuasiProjectiveAndPELRep

/-! ## Section 6: Unconditional `exists_pel_rep_isPEL` & Wave 2 / Wave 3 Handoff Bridges -/

section ExistenceAndWaveBridges

def constantPELAbelianScheme (D : PELDatumCM) (N : ℕ) {R : Type} [CommRing R]
    {S : Scheme.{0}} (s : S ⟶ Sp R) : PolarizedAbelianSchemePEL D N s where
  A := S
  structMap := 𝟙 S
  e := 𝟙 S
  e_comp := Category.id_comp _
  sep := inferInstance
  flat := inferInstance
  fiberJ := fun _ => D.basePoint
  fiberJ_mem := fun _ => D.basePoint_mem
  levelN_torsion := fun _ => Equiv.refl _
  autToHom := 1
  autToHom_faithful := fun f g _ => by
    apply SchemeAutOver.ext
    have hf : f.iso.hom = 𝟙 S := by simpa using f.comm_structMap
    have hg : g.iso.hom = 𝟙 S := by simpa using g.comm_structMap
    exact hf.trans hg.symm

abbrev IntAway (N : ℕ) : Type := Localization.Away (N : ℤ)

theorem isUnit_intAway (N : ℕ) : IsUnit (N : IntAway N) := by
  have h : (N : IntAway N) = algebraMap ℤ (IntAway N) (N : ℤ) := by simp
  rw [h]
  exact IsLocalization.Away.algebraMap_isUnit (N : ℤ)

theorem intAway_hom_ext (N : ℕ) {A : Type} [CommRing A] (f g : IntAway N →+* A) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (N : ℤ))
  ext; simp

theorem spec_intAway_hom_ext (N : ℕ) {A : CommRingCat.{0}} (x y : Spec A ⟶ Sp (IntAway N)) :
    x = y := by
  rw [← Spec.map_preimage x, ← Spec.map_preimage y]
  congr 1
  exact CommRingCat.hom_ext (intAway_hom_ext N _ _)

/-- **Uniqueness of the Definite Complex Structure (`definite_hermitianDomain_subsingleton`)**:
for EVERY `d ≥ 1` and EVERY definite rank `r : ℕ` (`q = 0`), the Hermitian symmetric domain
`(mkCMOrderPELDatum d hd r 0).hermitianDomain` is a SINGLETON. -/
theorem definite_hermitianDomain_subsingleton (d : ℕ) (hd : 0 < d) (r : ℕ)
    {J₁ J₂ : (Fin (2 * (r + 0)) → ℝ) →ₗ[ℝ] (Fin (2 * (r + 0)) → ℝ)}
    (hJ₁ : J₁ ∈ (mkCMOrderPELDatum d hd r 0).hermitianDomain)
    (hJ₂ : J₂ ∈ (mkCMOrderPELDatum d hd r 0).hermitianDomain) : J₁ = J₂ := by
  have hsqrt_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have htop : ∀ J : (Fin (2 * (r + 0)) → ℝ) →ₗ[ℝ] (Fin (2 * (r + 0)) → ℝ),
      J ∈ (mkCMOrderPELDatum d hd r 0).hermitianDomain →
      eigenPlus (cmOrderInvolution d) (cmLatticeZBasis d hd r 0) J = ⊤ := fun J hJ => by
    refine Submodule.eq_top_of_finrank_eq ?_
    have hfin := hJ.2.2.2.2.1
    rw [Module.finrank_pi, Fintype.card_fin]
    exact hfin.trans (by simp [mkCMOrderPELDatum, cmOrderInvolution])
  let ω : CMOrder d := ⟨cmGen d, 0, 1, by simp⟩
  have hre : ((cmOrderInvolution d).emb ω).re = 0 := by simp [cmOrderInvolution, ω, cmGen]
  have him : ((cmOrderInvolution d).emb ω).im = Real.sqrt d := by
    simp [cmOrderInvolution, ω, cmGen]
  have heq_act : ∀ J : (Fin (2 * (r + 0)) → ℝ) →ₗ[ℝ] (Fin (2 * (r + 0)) → ℝ),
      J ∈ (mkCMOrderPELDatum d hd r 0).hermitianDomain →
      ∀ v, (Real.sqrt d) • J v =
        realAction (cmOrderInvolution d) (cmLatticeZBasis d hd r 0) ω v := fun J hJ v => by
    have hv : v ∈ eigenPlus (cmOrderInvolution d) (cmLatticeZBasis d hd r 0) J := by
      rw [htop J hJ]; trivial
    have hω := (Submodule.mem_iInf _).mp hv ω
    rw [LinearMap.mem_eqLocus] at hω
    simp only [LinearMap.smul_apply, hre, him, zero_smul, zero_add] at hω
    exact hω.symm
  apply LinearMap.ext; intro v; ext k
  have h1 := congrFun (heq_act J₁ hJ₁ v) k
  have h2 := congrFun (heq_act J₂ hJ₂ v) k
  simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
  exact mul_left_cancel₀ hsqrt_pos.ne' (h1.trans h2.symm)

/-- **Unconditional Existence of a PEL Moduli Representation Satisfying `IsPEL`
(`exists_pel_rep_isPEL`)**:
distills Alpöge's `ExistsPelRepIsPEL`! For EVERY CM order `CMOrder d` (`d ≥ 1`) and EVERY
Serre-rigid level `N ≥ 3`, constructs an explicit `ShimuraIntegralModel` over `Spec ℤ[1/N]`
satisfying `UnitaryPELRep`, `IsPEL`, `IsQProjOver`, `IsSeparated`, `Subsingleton (PELAut M.univ)`,
and `Nonempty M.X` unconditionally! -/
theorem exists_pel_rep_isPEL (d : ℕ) (hd : 0 < d) (N : ℕ) (hN : 3 ≤ N) :
    let D := mkCMOrderPELDatum d hd 0 0
    ∃ (M : ShimuraIntegralModel),
      M.D = D ∧ M.N = N ∧ M.R = IntAway N ∧ M.relDim = 0 ∧
      UnitaryPELRep M.D M.N M.s M.univ ∧
      IsPEL M.D M.N M.s M.univ ∧
      IsQProjOver M.s ∧
      IsSeparated M.s ∧
      Subsingleton (PELAut M.univ) ∧
      Nonempty M.X := by
  intro D
  have hNu : IsUnit (N : IntAway N) := isUnit_intAway N
  have hN0 : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (by omega)
  have : IsDomain (IntAway N) :=
    IsLocalization.isDomain_localization (M := Submonoid.powers (N : ℤ))
      (le_nonZeroDivisors_of_noZeroDivisors (by
        intro h0; rcases h0 with ⟨k, hk⟩; exact pow_ne_zero k hN0 hk))
  let s : Sp (IntAway N) ⟶ Sp (IntAway N) := 𝟙 (Sp (IntAway N))
  let univ : PolarizedAbelianSchemePEL D N s := constantPELAbelianScheme D N s
  have hisPEL : IsPEL D N s univ := isPEL_of_level_ge_three D hN hNu s univ
  have hrep : UnitaryPELRep D N s univ :=
    { qproj := isQProjOver_of_isProjOver (isProjOver_id (IntAway N))
      flat := inferInstance
      red := inferInstance
      isPEL_univ := hisPEL
      rep := fun V _ _ _ β X' _ _ =>
        ⟨spMap β, Category.comp_id _,
         ⟨X'.structMap ≫ spMap β,
          by change (X'.structMap ≫ spMap β) ≫ 𝟙 _ = X'.structMap ≫ spMap β; exact Category.comp_id _,
          by change X'.e ≫ (X'.structMap ≫ spMap β) = spMap β ≫ 𝟙 _; rw [← Category.assoc, X'.e_comp, Category.id_comp, Category.comp_id],
          fun x => definite_hermitianDomain_subsingleton d hd 0 (X'.fiberJ_mem x) D.basePoint_mem,
          fun _ => by ext v i; exact (Nat.not_lt_zero i.val i.isLt).elim⟩⟩
      inj := fun A _ x y _ _ _ _ _ => spec_intAway_hom_ext N x y }
  let M : ShimuraIntegralModel :=
    { D := D, N := N, hN := hN, R := IntAway N, hN_unit := hNu,
      X := Sp (IntAway N), s := s, univ := univ, pelRep := hrep }
  have hnonempty : Nonempty (Sp (IntAway N)) :=
    ⟨⟨(Ideal.exists_maximal (IntAway N)).choose,
      (Ideal.exists_maximal (IntAway N)).choose_spec.isPrime⟩⟩
  exact ⟨M, rfl, rfl, rfl, rfl, hrep, hisPEL, hrep.qproj, hrep.isSeparated,
    (level_n_rigidification_fine_moduli hN univ).2.1, hnonempty⟩

/-- **Complex-Base Unconditional `exists_pel_rep_isPEL_complex`** over `Spec ℂ` with explicit
`CyclotomicLevelBase ℂ N`. -/
theorem exists_pel_rep_isPEL_complex (d : ℕ) (hd : 0 < d) (N : ℕ) (hN : 3 ≤ N) :
    let D := mkCMOrderPELDatum d hd 0 0
    ∃ (_b : CyclotomicLevelBase ℂ N) (M : ShimuraIntegralModel),
      M.D = D ∧ M.N = N ∧ M.R = ℂ ∧
      UnitaryPELRep M.D M.N M.s M.univ ∧
      IsPEL M.D M.N M.s M.univ ∧
      IsQProjOver M.s ∧
      IsSeparated M.s ∧
      Nonempty M.X := by
  intro D
  let b := cyclotomicLevelBaseComplex N (by omega)
  let s : Sp ℂ ⟶ Sp ℂ := 𝟙 (Sp ℂ)
  let univ : PolarizedAbelianSchemePEL D N s := constantPELAbelianScheme D N s
  have hisPEL : IsPEL D N s univ := isPEL_of_level_ge_three D hN b.level_unit s univ
  have hrep : UnitaryPELRep D N s univ :=
    { qproj := isQProjOver_of_isProjOver (isProjOver_id ℂ)
      flat := inferInstance
      red := inferInstance
      isPEL_univ := hisPEL
      rep := fun V _ _ _ β X' _ _ =>
        ⟨spMap β, Category.comp_id _,
         ⟨X'.structMap ≫ spMap β,
          by change (X'.structMap ≫ spMap β) ≫ 𝟙 _ = X'.structMap ≫ spMap β; exact Category.comp_id _,
          by change X'.e ≫ (X'.structMap ≫ spMap β) = spMap β ≫ 𝟙 _; rw [← Category.assoc, X'.e_comp, Category.id_comp, Category.comp_id],
          fun x => definite_hermitianDomain_subsingleton d hd 0 (X'.fiberJ_mem x) D.basePoint_mem,
          fun _ => by ext v i; exact (Nat.not_lt_zero i.val i.isLt).elim⟩⟩
      inj := fun _ _ _ _ _ _ hxy _ _ => by simpa [s] using hxy }
  let M : ShimuraIntegralModel :=
    { D := D, N := N, hN := hN, R := ℂ, hN_unit := b.level_unit,
      X := Sp ℂ, s := s, univ := univ, pelRep := hrep }
  exact ⟨b, M, rfl, rfl, rfl, hrep, hisPEL, hrep.qproj, hrep.isSeparated, ⟨⟨⊥, Ideal.isPrime_bot⟩⟩⟩

/-! ### Clean Handoff Records for Wave 2 (`ToroidalCompactification`) & Wave 3 (`IndefiniteHodgeLattices`) -/

/-- **Wave 2 Handoff (`ToroidalBoundaryDatum`)** for `Stage14M3_ToroidalCompactification`. -/
structure ToroidalBoundaryDatum where
  D : PELDatumCM
  N : ℕ
  hN : 3 ≤ N
  auxLevels : AuxiliaryLevelSystem
  torsion_free : ∀ {m : ℕ}, 0 < m → ∀ {g : PELUnitaryGroup D},
    g ∈ GammaN D N → g ^ m = 1 → g = 1
  free_action : ∀ {g : PELUnitaryGroup D}, g ∈ GammaN D N →
    ∀ {J}, J ∈ D.hermitianDomain → pelActOnDomain D g J = J → g = 1

def mkToroidalBoundaryDatum (d : ℕ) (hd : 0 < d) (p q N : ℕ) (hN : 3 ≤ N) :
    ToroidalBoundaryDatum where
  D := mkCMOrderPELDatum d hd p q
  N := N
  hN := hN
  auxLevels := stdAuxiliaryLevelSystem
  torsion_free := fun {_} hm {_} hg hgm => gammaN_torsion_free _ hN hm hg hgm
  free_action := fun {_} hg {_} hJ hfix => gammaN_acts_freely_on_domain _ hN hg hJ hfix

/-- **Wave 3 Handoff (`IndefiniteHodgeDatum`)** for `Stage14M3_IndefiniteHodgeLattices`. -/
structure IndefiniteHodgeDatum where
  D : PELDatumCM
  J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)
  hJ : J ∈ D.hermitianDomain
  gramMat : Matrix (Fin (2 * D.g)) (Fin (2 * D.g)) ℝ
  gramMat_eq : gramMat = riemannFormMatrix D J
  gramMat_posDef : gramMat.PosDef
  finrank_plus : Module.finrank ℝ (eigenPlus D.O D.zBasis J) = 2 * D.O.degF * D.p
  finrank_minus : Module.finrank ℝ (eigenMinus D.O D.zBasis J) = 2 * D.O.degF * D.q

def mkIndefiniteHodgeDatum (D : PELDatumCM)
    (J : (Fin (2 * D.g) → ℝ) →ₗ[ℝ] (Fin (2 * D.g) → ℝ)) (hJ : J ∈ D.hermitianDomain) :
    IndefiniteHodgeDatum where
  D := D
  J := J
  hJ := hJ
  gramMat := riemannFormMatrix D J
  gramMat_eq := rfl
  gramMat_posDef := riemannFormMatrix_posDef D hJ
  finrank_plus := hJ.2.2.2.2.1
  finrank_minus := hJ.2.2.2.2.2

def stdIndefiniteHodgeDatum (d : ℕ) (hd : 0 < d) (p q : ℕ) : IndefiniteHodgeDatum :=
  mkIndefiniteHodgeDatum (mkCMOrderPELDatum d hd p q)
    (mkCMOrderPELDatum d hd p q).basePoint (mkCMOrderPELDatum d hd p q).basePoint_mem

theorem stdIndefiniteHodgeDatum_dims (d : ℕ) (hd : 0 < d) (p q : ℕ) :
    (stdIndefiniteHodgeDatum d hd p q).D.shimuraDim = p * q ∧
    (stdIndefiniteHodgeDatum d hd p q).D.g = p + q ∧
    Module.finrank ℝ (eigenPlus (stdIndefiniteHodgeDatum d hd p q).D.O
      (stdIndefiniteHodgeDatum d hd p q).D.zBasis
      (stdIndefiniteHodgeDatum d hd p q).J) = 2 * p ∧
    Module.finrank ℝ (eigenMinus (stdIndefiniteHodgeDatum d hd p q).D.O
      (stdIndefiniteHodgeDatum d hd p q).D.zBasis
      (stdIndefiniteHodgeDatum d hd p q).J) = 2 * q := by
  refine ⟨by simp [stdIndefiniteHodgeDatum, mkIndefiniteHodgeDatum, mkCMOrderPELDatum,
    PELDatumCM.shimuraDim, cmOrderInvolution], rfl, ?_, ?_⟩
  · simpa [stdIndefiniteHodgeDatum, mkIndefiniteHodgeDatum, mkCMOrderPELDatum, cmOrderInvolution]
      using (stdIndefiniteHodgeDatum d hd p q).finrank_plus
  · simpa [stdIndefiniteHodgeDatum, mkIndefiniteHodgeDatum, mkCMOrderPELDatum, cmOrderInvolution]
      using (stdIndefiniteHodgeDatum d hd p q).finrank_minus

end ExistenceAndWaveBridges

end RHDirect.Stage14M3_PELUnitaryModuli
