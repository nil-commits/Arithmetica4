import RHDirect.Stage11DefiniteUnitaryChain
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Group.Basic

/-!
# RHDirect.Stage14M1_UnitaryGroupDef

Field-2 Package M1 Wave 1 (Module 2 of 6): **Unitary Groups of CM Hermitian Spaces,
Signature `(p, q)` & Sylvester Inertia, Adelic Unitary Groups, Compact Open Levels,
and Unconditional Finiteness of Definite Arithmetic Stabilizers** in pure Mathlib `v4.33.1`
(`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`).

## Contents

1. **CM Field Pairs `CMFieldPair F E`**:
   - Totally real base field `F`, totally complex quadratic CM extension `E/F` (`[E : F] = 2`)
     equipped with complex conjugation `star : E → E` fixing `F` and commuting with all
     archimedean embeddings `τ : E →+* ℂ`.
   - Construction of `conjAlgHom : E →ₐ[F] E`, `conjAlgEquiv : E ≃ₐ[F] E`, real restriction
     `realPlaceOfEmbedding`, and lifting of any real place `ι : F →+* ℝ` to `τ : E →+* ℂ`.

2. **Hermitian Spaces over CM Fields (`HermSpaceCM E F V`) & Unitary Groups (`UnitaryGrp`)**:
   - Concrete Hermitian spaces `HermSpaceCM E F V` carrying a nondegenerate Hermitian form
     `form : V →ₗ⋆[E] V →ₗ[E] E`, dimension `dim`, and explicit `E`-basis `frame`.
   - Gram matrix `gram`, Hermitian symmetry `gram_isHerm`, nonsingularity `gram_det_isUnit`,
     and constructors `HermSpaceCM.ofMatrix`, `HermSpaceCM.neg` (`-V`),
     `HermSpaceCM.directSum` (`V₁ ⊕ V₂`), and `HermSpaceCM.doubled` (`V^□ = V ⊕ (-V)` with
     totally isotropic diagonal `V^Δ` for M1 Wave 2 `DoublingZeta`).
   - Coordinate-free unitary group `UnitaryGrp H : Subgroup (V ≃ₗ[E] V)`, matrix unitary
     group `UnitaryMatGrp σ J : Subgroup (GL n A)`, explicit isomorphism
     `unitaryGrpEquivMat : UnitaryGrp H ≃* UnitaryMatGrp ... H.gram`, functorial `R`-points
     `UnitaryPts σ J R`, and doubling embeddings `directSumEmbed`, `doubledEmbed`, `diagDoubledEmbed`.

3. **Hermitian Signature `(p, q)`, Sylvester's Law of Inertia, `DefiniteHermSpace` & `IndefiniteHermSpace`**:
   - Concrete `HasSignature J p q`, invariance/additivity (`hasSignature_card`, `hasSignature_neg`,
     `hasSignature_directSum`), exact characterizations `hasSignature_posDef_iff` and
     `hasSignature_negDef_iff`, **Sylvester's Law of Inertia (`hasSignature_unique`)**, and
     spectral existence `exists_hasSignature_of_isHermitian_isUnit`.
   - **`DefiniteHermSpace E F V`** (definite at every archimedean place, with positive-definite
     predicate `IsPosDef` and `PosDefHermSpace`), **`IndefiniteHermSpace E F V`** (arbitrary
     signature `(p τ, q τ)` with indefinite witness), total definiteness `isTotDef`, and
     Cauchy–Schwarz matrix-entry bound `definite_cauchy_schwarz_entry_bound`.

4. **Adelic Unitary Groups `UnitaryAdelicGrp`, Compactness at `∞` & `CompactOpenLevel`**:
   - Local finite groups `UnitaryLocalGrp H v`, local archimedean groups `UnitaryArchGrp H ι`
     (with compactness `isCompact_unitaryMat_of_posDef` for positive-definite forms),
     finite-adelic group `UnitaryFiniteAdelicGrp H`, full adelic group `UnitaryAdelicGrp H`,
     and injective rational embeddings `ratToFiniteAdelic` and `ratToAdelic`.
   - Adelic integral subring `adelicIntRing F E ⊆ E ⊗[F] 𝔸_{F,f}`, standard maximal compact
     open level `stdMaximalLevel H`, principal congruence levels `principalCongruenceLevel H I hI`,
     and general **`CompactOpenLevel H`** closed under finite-index subgroups, intersections,
     and conjugation by `UnitaryFiniteAdelicGrp H`.

5. **Unconditional Finiteness Theorem (`stabilizer_finite_of_definite`)**:
   - Number-field denominator clearing (`exists_int_denom_of_numberField`), trace-form dual
     basis integrality over `𝓞 F`, and adelic lattice pullback `adelicPullbackLattice`
     (`Module.Finite (𝓞 E)` and full `E`-span).
   - Lattice stabilizer finiteness `stabilizer_lattice_finite_of_definite`, adelic level
     finiteness **`stabilizer_finite_of_definite`** (`U(V)(F) ∩ K_f` is `Finite`), and
     arbitrary double-coset stabilizer finiteness **`stabilizer_coset_finite_of_definite`**
     (`U(V)(F) ∩ g K_f g⁻¹` is `Finite` for every `g ∈ U(V)(𝔸_{F,f})`), ready for M1 Wave 2
     `AdelicWeilTheta`, `DoublingZeta`, and `FormalDegreeDiscrete`.
-/

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Module Submodule Matrix TensorProduct NumberField IsDedekindDomain
open scoped BigOperators TensorProduct ComplexOrder

namespace RHDirect.Stage14M1_UnitaryGroupDef

/-! ## Section 1: CM Field Extensions `CMFieldPair F E` & Archimedean Conjugation -/

section CMFields

/-- A CM field pair `(F, E)`: `F` is a totally real number field, `E` is a totally complex
quadratic extension of `F` (`[E : F] = 2`) with involution `star : E → E` whose fixed subfield
is `F` and which commutes with every archimedean embedding `τ : E →+* ℂ`. -/
structure CMFieldPair (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] : Prop where
  totallyReal : NumberField.IsTotallyReal F
  totallyComplex : NumberField.IsTotallyComplex E
  degTwo : Module.finrank F E = 2
  star_fixed_iff : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range
  star_embedding_compat : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = star (τ a)

namespace CMFieldPair

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
  [StarRing E] [Algebra F E]

/-- CM conjugation `starRingEnd E` as an `F`-algebra homomorphism `E →ₐ[F] E`. -/
def conjAlgHom (cm : CMFieldPair F E) : E →ₐ[F] E :=
  { starRingEnd E with
    commutes' := fun a => (cm.star_fixed_iff (algebraMap F E a)).2 ⟨a, rfl⟩ }

/-- CM conjugation as an `F`-algebra automorphism `E ≃ₐ[F] E`. -/
def conjAlgEquiv (cm : CMFieldPair F E) : E ≃ₐ[F] E :=
  { cm.conjAlgHom with
    invFun := cm.conjAlgHom
    left_inv := fun a => star_star a
    right_inv := fun a => star_star a }

/-- Underlying ring endomorphism of CM conjugation. -/
abbrev conjRingHom (_cm : CMFieldPair F E) : E →+* E := starRingEnd E

@[simp]
lemma conjAlgHom_apply (cm : CMFieldPair F E) (a : E) :
    cm.conjAlgHom a = star a := rfl

@[simp]
lemma conjAlgEquiv_apply (cm : CMFieldPair F E) (a : E) :
    cm.conjAlgEquiv a = star a := rfl

@[simp]
lemma conjRingHom_apply (cm : CMFieldPair F E) (a : E) :
    cm.conjRingHom a = star a := rfl

lemma conjAlgHom_involutive (cm : CMFieldPair F E) (a : E) :
    cm.conjAlgHom (cm.conjAlgHom a) = a := star_star a

lemma star_embedding_eq_comp (cm : CMFieldPair F E) (τ : E →+* ℂ) :
    τ.comp cm.conjRingHom = (starRingEnd ℂ).comp τ := by
  ext a
  exact cm.star_embedding_compat τ a

/-- Every embedding `τ : E →+* ℂ` takes real values on the totally real base field `F`. -/
lemma embedding_base_im_eq_zero (cm : CMFieldPair F E) (τ : E →+* ℂ) (a : F) :
    (τ (algebraMap F E a)).im = 0 := by
  have hfix : star (algebraMap F E a) = algebraMap F E a :=
    (cm.star_fixed_iff (algebraMap F E a)).2 ⟨a, rfl⟩
  have h1 : star (τ (algebraMap F E a)) = τ (algebraMap F E a) := by
    rw [← cm.star_embedding_compat τ (algebraMap F E a), hfix]
  exact Complex.conj_eq_iff_im.1 h1

/-- Restriction of a complex embedding `τ : E →+* ℂ` to a real embedding `F →+* ℝ`. -/
def realPlaceOfEmbedding (cm : CMFieldPair F E) (τ : E →+* ℂ) : F →+* ℝ where
  toFun a := (τ (algebraMap F E a)).re
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Complex.mul_re, cm.embedding_base_im_eq_zero τ a,
      cm.embedding_base_im_eq_zero τ b, mul_zero, sub_zero]
  map_zero' := by simp
  map_add' a b := by simp

lemma embedding_base_eq_ofReal (cm : CMFieldPair F E) (τ : E →+* ℂ) (a : F) :
    τ (algebraMap F E a) = ((cm.realPlaceOfEmbedding τ a : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · exact cm.embedding_base_im_eq_zero τ a

/-- Every real embedding `ι : F →+* ℝ` extends to at least one complex embedding `τ : E →+* ℂ`. -/
theorem exists_embedding_above (cm : CMFieldPair F E) (ι : F →+* ℝ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι := by
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [cm.degTwo]; norm_num)
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  let φ : E →ₐ[F] ℂ := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_⟩
  ext a
  exact φ.commutes a

/-- Every real embedding `ι : F →+* ℝ` appears as `realPlaceOfEmbedding τ` for some `τ`. -/
theorem exists_embedding_with_realPlace (cm : CMFieldPair F E) (ι : F →+* ℝ) :
    ∃ τ : E →+* ℂ, cm.realPlaceOfEmbedding τ = ι := by
  obtain ⟨τ, hτ⟩ := cm.exists_embedding_above ι
  refine ⟨τ, ?_⟩
  ext a
  have h := RingHom.congr_fun hτ a
  simp only [RingHom.comp_apply, Complex.coe_algebraMap] at h
  change (τ (algebraMap F E a)).re = ι a
  rw [h, Complex.ofReal_re]

end CMFieldPair

end CMFields

/-! ## Section 2: Matrix & Coordinate-Free Hermitian Forms (`HermSpaceCM E F V`) -/

section HermitianForms

section MatrixHermitian

variable {A : Type*} [CommRing A] {m p q n : Type*}

/-- `σ`-twisted conjugate transpose `(M.map σ)ᵀ` of a matrix over `A`. -/
def conjTransposeMap (σ : A →+* A) (M : Matrix m p A) : Matrix p m A :=
  (M.map σ)ᵀ

/-- Predicate that a square matrix `J` is `σ`-Hermitian (`(J.map σ)ᵀ = J`). -/
def IsHermMatrix (σ : A →+* A) (J : Matrix n n A) : Prop :=
  conjTransposeMap σ J = J

/-- Explicit Hermitian sesquilinear pairing `∑_{i,j} σ(x_i) * J_{ij} * y_j`. -/
def hermFormMatrix [Fintype n] (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A :=
  ∑ i : n, ∑ j : n, σ (x i) * J i j * y j

lemma conjTransposeMap_apply (σ : A →+* A) (M : Matrix m p A) (i : p) (j : m) :
    conjTransposeMap σ M i j = σ (M j i) := rfl

lemma conjTransposeMap_mul [Fintype p] (σ : A →+* A) (M : Matrix m p A) (N : Matrix p q A) :
    conjTransposeMap σ (M * N) = conjTransposeMap σ N * conjTransposeMap σ M := by
  simp [conjTransposeMap, Matrix.map_mul, Matrix.transpose_mul]

lemma conjTransposeMap_one [DecidableEq n] (σ : A →+* A) :
    conjTransposeMap σ (1 : Matrix n n A) = 1 := by
  unfold conjTransposeMap
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

lemma conjTransposeMap_add (σ : A →+* A) (M N : Matrix m p A) :
    conjTransposeMap σ (M + N) = conjTransposeMap σ M + conjTransposeMap σ N := by
  ext i j
  simp [conjTransposeMap]

lemma conjTransposeMap_neg (σ : A →+* A) (M : Matrix m p A) :
    conjTransposeMap σ (-M) = -conjTransposeMap σ M := by
  ext i j
  simp [conjTransposeMap]

lemma conjTransposeMap_star_eq_conjTranspose [StarRing A] (M : Matrix m p A) :
    conjTransposeMap (starRingEnd A) M = Mᴴ := by
  ext i j
  rfl

lemma conjTransposeMap_fromBlocks (σ : A →+* A)
    (M₁₁ : Matrix m p A) (M₁₂ : Matrix m q A) (M₂₁ : Matrix n p A) (M₂₂ : Matrix n q A) :
    conjTransposeMap σ (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (conjTransposeMap σ M₁₁) (conjTransposeMap σ M₂₁)
        (conjTransposeMap σ M₁₂) (conjTransposeMap σ M₂₂) := by
  ext i j
  cases i <;> cases j <;> simp [conjTransposeMap]

lemma isHermMatrix_neg {σ : A →+* A} {J : Matrix n n A} (hJ : IsHermMatrix σ J) :
    IsHermMatrix σ (-J) := by
  unfold IsHermMatrix at hJ ⊢
  rw [conjTransposeMap_neg, hJ]

lemma isHermMatrix_fromBlocks {σ : A →+* A}
    {J₁ : Matrix m m A} {J₂ : Matrix n n A}
    (hJ₁ : IsHermMatrix σ J₁) (hJ₂ : IsHermMatrix σ J₂) :
    IsHermMatrix σ (Matrix.fromBlocks J₁ 0 0 J₂) := by
  unfold IsHermMatrix at hJ₁ hJ₂ ⊢
  rw [conjTransposeMap_fromBlocks]
  have h0₁ : conjTransposeMap σ (0 : Matrix m n A) = 0 := by ext i j; simp [conjTransposeMap]
  have h0₂ : conjTransposeMap σ (0 : Matrix n m A) = 0 := by ext i j; simp [conjTransposeMap]
  rw [hJ₁, hJ₂, h0₁, h0₂]

lemma isHermMatrix_reindex {σ : A →+* A} {J : Matrix m m A} (hJ : IsHermMatrix σ J)
    (e : m ≃ n) : IsHermMatrix σ (J.reindex e e) := by
  ext i j
  exact congrFun (congrFun hJ (e.symm i)) (e.symm j)

lemma hermFormMatrix_add_left [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x₁ x₂ y : n → A) :
    hermFormMatrix σ J (x₁ + x₂) y = hermFormMatrix σ J x₁ y + hermFormMatrix σ J x₂ y := by
  unfold hermFormMatrix
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

lemma hermFormMatrix_add_right [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y₁ y₂ : n → A) :
    hermFormMatrix σ J x (y₁ + y₂) = hermFormMatrix σ J x y₁ + hermFormMatrix σ J x y₂ := by
  unfold hermFormMatrix
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma hermFormMatrix_smul_left [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (c : A) (x y : n → A) :
    hermFormMatrix σ J (c • x) y = σ c * hermFormMatrix σ J x y := by
  unfold hermFormMatrix
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma hermFormMatrix_smul_right [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (c : A) (x y : n → A) :
    hermFormMatrix σ J x (c • y) = c * hermFormMatrix σ J x y := by
  unfold hermFormMatrix
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma hermFormMatrix_single_left [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) (i : n) (y : n → A) :
    hermFormMatrix σ J (Pi.single i 1) y = (J *ᵥ y) i := by
  unfold hermFormMatrix
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma hermFormMatrix_single_right [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) (x : n → A) (j : n) :
    hermFormMatrix σ J x (Pi.single j 1) = ∑ i : n, σ (x i) * J i j := by
  unfold hermFormMatrix
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma hermFormMatrix_gram [Fintype n] (σ : A →+* A) (J M : Matrix n n A) (a b : n) :
    (conjTransposeMap σ M * J * M) a b =
      hermFormMatrix σ J (fun k => M k a) (fun k => M k b) := by
  unfold hermFormMatrix conjTransposeMap
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma hermFormMatrix_map [Fintype n] {B : Type*} [CommRing B]
    (σA : A →+* A) (σB : B →+* B) (τ : A →+* B) (hτ : τ.comp σA = σB.comp τ)
    (J : Matrix n n A) (x y : n → A) :
    τ (hermFormMatrix σA J x y) =
      hermFormMatrix σB (J.map τ) (fun k => τ (x k)) (fun k => τ (y k)) := by
  unfold hermFormMatrix
  simp only [map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 := RingHom.congr_fun hτ (x i)
  simp only [RingHom.comp_apply] at h1
  rw [h1]

lemma hermFormMatrix_conj_mulVec [Fintype n] (σ : A →+* A) (J M : Matrix n n A)
    (x y : n → A) :
    hermFormMatrix σ J (M *ᵥ x) (M *ᵥ y) =
      hermFormMatrix σ (conjTransposeMap σ M * J * M) x y := by
  unfold hermFormMatrix
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have step1 : ∀ i j : n,
      (∑ a : n, σ (M i a) * σ (x a)) * J i j * (∑ b : n, M j b * y b) =
        ∑ a : n, ∑ b : n, σ (M i a) * σ (x a) * J i j * (M j b * y b) := by
    intro i j
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
  simp_rw [step1]
  calc ∑ i : n, ∑ j : n, ∑ a : n, ∑ b : n, σ (M i a) * σ (x a) * J i j * (M j b * y b)
      = ∑ i : n, ∑ a : n, ∑ j : n, ∑ b : n, σ (M i a) * σ (x a) * J i j * (M j b * y b) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a : n, ∑ i : n, ∑ j : n, ∑ b : n, σ (M i a) * σ (x a) * J i j * (M j b * y b) :=
        Finset.sum_comm
    _ = ∑ a : n, ∑ i : n, ∑ b : n, ∑ j : n, σ (M i a) * σ (x a) * J i j * (M j b * y b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ a : n, ∑ b : n, ∑ i : n, ∑ j : n, σ (M i a) * σ (x a) * J i j * (M j b * y b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a : n, ∑ b : n, σ (x a) * (conjTransposeMap σ M * J * M) a b * y b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hermFormMatrix_gram]
        unfold hermFormMatrix
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end MatrixHermitian

/-- **Concrete Hermitian Space `HermSpaceCM E F V`** over a CM field pair `(F, E)`:
an `E`-vector space `V` of finite dimension `dim` equipped with a nondegenerate
`E`-Hermitian sesquilinear form `form : V →ₗ⋆[E] V →ₗ[E] E` and a reference basis `frame`. -/
structure HermSpaceCM (E F V : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  cm : CMFieldPair F E
  form : V →ₗ⋆[E] V →ₗ[E] E
  herm : ∀ x y : V, form y x = star (form x y)
  nondeg : ∀ x : V, (∀ y : V, form x y = 0) → x = 0
  dim : ℕ
  dim_eq : Module.finrank E V = dim
  frame : Module.Basis (Fin dim) E V

namespace HermSpaceCM

variable {E F V : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Gram matrix of `H.form` with respect to the reference frame `H.frame`. -/
def gram (H : HermSpaceCM E F V) : Matrix (Fin H.dim) (Fin H.dim) E :=
  Matrix.of fun i j => H.form (H.frame i) (H.frame j)

@[simp]
lemma gram_apply (H : HermSpaceCM E F V) (i j : Fin H.dim) :
    H.gram i j = H.form (H.frame i) (H.frame j) := rfl

/-- The Gram matrix `H.gram` is `starRingEnd E`-Hermitian. -/
theorem gram_isHerm (H : HermSpaceCM E F V) :
    IsHermMatrix H.cm.conjRingHom H.gram := by
  ext i j
  simp only [conjTransposeMap_apply, gram_apply, CMFieldPair.conjRingHom_apply]
  exact (H.herm (H.frame j) (H.frame i)).symm

/-- Nondegeneracy of `H.form` implies `H.gram.det` is invertible in `E`. -/
theorem gram_det_isUnit (H : HermSpaceCM E F V) : IsUnit H.gram.det := by
  classical
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrow : ∀ i : Fin H.dim, H.form (H.frame i) (∑ j : Fin H.dim, v j • H.frame j) = 0 := by
    intro i
    have h1 : ∑ j : Fin H.dim, H.gram i j * v j = 0 := by
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct] using this
    rw [map_sum]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans h1
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  have hzero : ∑ j : Fin H.dim, v j • H.frame j = 0 := by
    apply H.nondeg
    intro y
    rw [← H.frame.sum_repr y, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    have hcomm : H.form (∑ j : Fin H.dim, v j • H.frame j) (H.frame i) =
        star (H.form (H.frame i) (∑ j : Fin H.dim, v j • H.frame j)) :=
      H.herm _ _
    rw [hrow i, star_zero] at hcomm
    rw [hcomm, mul_zero]
  have hv' := (Fintype.linearIndependent_iff.mp H.frame.linearIndependent) v hzero
  exact hv0 (funext hv')

/-- Coordinate expansion of `H.form x y` via `H.gram` and `H.frame.repr`. -/
theorem form_eq_hermFormMatrix (H : HermSpaceCM E F V) (x y : V) :
    H.form x y = hermFormMatrix H.cm.conjRingHom H.gram (H.frame.repr x) (H.frame.repr y) := by
  conv_lhs => rw [← H.frame.sum_repr x, ← H.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  unfold hermFormMatrix
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [CMFieldPair.conjRingHom_apply, gram_apply]
  ring

/-- Every diagonal value `H.form x x` is fixed by CM conjugation and hence lies in `F`. -/
theorem form_self_mem_base (H : HermSpaceCM E F V) (x : V) :
    ∃ a : F, algebraMap F E a = H.form x x := by
  have hfix : star (H.form x x) = H.form x x := (H.herm x x).symm
  exact RingHom.mem_range.mp ((H.cm.star_fixed_iff _).1 hfix)

/-- Concrete `HermSpaceCM E F (Fin n → E)` built from any invertible Hermitian matrix `J`. -/
def ofMatrix {n : ℕ} (cm : CMFieldPair F E) (J : Matrix (Fin n) (Fin n) E)
    (hHerm : IsHermMatrix cm.conjRingHom J) (hdet : IsUnit J.det) :
    HermSpaceCM E F (Fin n → E) where
  cm := cm
  form :=
    { toFun := fun x =>
        { toFun := fun y => hermFormMatrix cm.conjRingHom J x y
          map_add' := fun y₁ y₂ => hermFormMatrix_add_right cm.conjRingHom J x y₁ y₂
          map_smul' := fun c y => by
            simpa [smul_eq_mul] using hermFormMatrix_smul_right cm.conjRingHom J c x y }
      map_add' := fun x₁ x₂ =>
        LinearMap.ext fun y => hermFormMatrix_add_left cm.conjRingHom J x₁ x₂ y
      map_smul' := fun c x =>
        LinearMap.ext fun y => by
          simpa [RingHom.id_apply, smul_eq_mul, CMFieldPair.conjRingHom_apply,
            starRingEnd_apply] using
            hermFormMatrix_smul_left cm.conjRingHom J c x y }
  herm := fun x y => by
    change hermFormMatrix cm.conjRingHom J y x = star (hermFormMatrix cm.conjRingHom J x y)
    unfold hermFormMatrix
    rw [star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [star_mul', star_star, CMFieldPair.conjRingHom_apply]
    have hJji : star (J j i) = J i j := by
      have h := congrFun (congrFun hHerm i) j
      simpa [conjTransposeMap, CMFieldPair.conjRingHom_apply] using h
    rw [hJji]
    ring
  nondeg := fun x hx => by
    have hmul : (fun i => star (x i)) ᵥ* J = 0 := by
      ext j
      have hj := hx (Pi.single j 1)
      change hermFormMatrix cm.conjRingHom J x (Pi.single j 1) = 0 at hj
      rw [hermFormMatrix_single_right] at hj
      simpa [Matrix.vecMul, dotProduct] using hj
    have hxstar : (fun i => star (x i)) = 0 := by
      have := congrArg (fun v => v ᵥ* J⁻¹) hmul
      simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet] using this
    ext i
    have hi := congrFun hxstar i
    simpa using congrArg star hi
  dim := n
  dim_eq := Module.finrank_fin_fun E
  frame := Pi.basisFun E (Fin n)

@[simp]
lemma gram_ofMatrix {n : ℕ} (cm : CMFieldPair F E) (J : Matrix (Fin n) (Fin n) E)
    (hHerm : IsHermMatrix cm.conjRingHom J) (hdet : IsUnit J.det) :
    (ofMatrix cm J hHerm hdet).gram = J := by
  have h : ∀ a b : Fin n,
      hermFormMatrix cm.conjRingHom J (Pi.basisFun E (Fin n) a) (Pi.basisFun E (Fin n) b) = J a b := by
    intro a b
    rw [Pi.basisFun_apply, Pi.basisFun_apply, hermFormMatrix_single_left]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  ext i j
  exact h i j

/-- Negated Hermitian space `-V` (`form` replaced by `-form`), used in Rallis doubling `V ⊕ (-V)`. -/
def neg (H : HermSpaceCM E F V) : HermSpaceCM E F V where
  cm := H.cm
  form := -H.form
  herm := fun x y => by
    simp only [LinearMap.neg_apply, star_neg]
    exact congrArg Neg.neg (H.herm x y)
  nondeg := fun x hx => H.nondeg x fun y => by
    have := hx y
    simp only [LinearMap.neg_apply, neg_eq_zero] at this
    exact this
  dim := H.dim
  dim_eq := H.dim_eq
  frame := H.frame

@[simp]
lemma neg_form (H : HermSpaceCM E F V) (x y : V) :
    H.neg.form x y = -H.form x y := rfl

@[simp]
lemma neg_gram (H : HermSpaceCM E F V) :
    H.neg.gram = -H.gram := by
  ext i j; rfl

/-- Orthogonal direct sum `V₁ ⊕ V₂` of two Hermitian spaces over the same CM field pair `(F, E)`. -/
def directSum {V₁ V₂ : Type*} [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁]
    [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (H₁ : HermSpaceCM E F V₁) (H₂ : HermSpaceCM E F V₂) :
    HermSpaceCM E F (V₁ × V₂) where
  cm := H₁.cm
  form :=
    { toFun := fun x =>
        { toFun := fun y => H₁.form x.1 y.1 + H₂.form x.2 y.2
          map_add' := fun y₁ y₂ => by simp [map_add]; ring
          map_smul' := fun c y => by simp [smul_eq_mul, mul_add] }
      map_add' := fun x₁ x₂ =>
        LinearMap.ext fun y => by simp [map_add]; ring
      map_smul' := fun c x =>
        LinearMap.ext fun y => by
          change H₁.form (c • x.1) y.1 + H₂.form (c • x.2) y.2 =
            starRingEnd E c • (H₁.form x.1 y.1 + H₂.form x.2 y.2)
          simp [smul_eq_mul, mul_add] }
  herm := fun x y => by
    change H₁.form y.1 x.1 + H₂.form y.2 x.2 = star (H₁.form x.1 y.1 + H₂.form x.2 y.2)
    rw [star_add, H₁.herm, H₂.herm]
  nondeg := fun x hx => by
    have hx₁ : x.1 = 0 := H₁.nondeg x.1 fun y₁ => by
      simpa using hx (y₁, 0)
    have hx₂ : x.2 = 0 := H₂.nondeg x.2 fun y₂ => by
      simpa using hx (0, y₂)
    exact Prod.ext hx₁ hx₂
  dim := H₁.dim + H₂.dim
  dim_eq := by
    rw [Module.finrank_prod, H₁.dim_eq, H₂.dim_eq]
  frame := (H₁.frame.prod H₂.frame).reindex finSumFinEquiv

@[simp]
lemma directSum_form {V₁ V₂ : Type*} [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁]
    [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (H₁ : HermSpaceCM E F V₁) (H₂ : HermSpaceCM E F V₂) (x y : V₁ × V₂) :
    (H₁.directSum H₂).form x y = H₁.form x.1 y.1 + H₂.form x.2 y.2 := rfl

lemma directSum_gram {V₁ V₂ : Type*} [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁]
    [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (H₁ : HermSpaceCM E F V₁) (H₂ : HermSpaceCM E F V₂) :
    (H₁.directSum H₂).gram =
      (Matrix.fromBlocks H₁.gram 0 0 H₂.gram).reindex finSumFinEquiv finSumFinEquiv := by
  have h : ∀ i j : Fin (H₁.dim + H₂.dim),
      H₁.form ((H₁.frame.prod H₂.frame).reindex finSumFinEquiv i).1
          ((H₁.frame.prod H₂.frame).reindex finSumFinEquiv j).1 +
        H₂.form ((H₁.frame.prod H₂.frame).reindex finSumFinEquiv i).2
          ((H₁.frame.prod H₂.frame).reindex finSumFinEquiv j).2 =
        (Matrix.fromBlocks H₁.gram 0 0 H₂.gram) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := by
    intro i j
    simp only [Basis.coe_reindex, Function.comp_apply]
    rcases hi : finSumFinEquiv.symm i with a | a <;>
      rcases hj : finSumFinEquiv.symm j with b | b <;>
      simp [Basis.prod_apply, gram_apply]
  ext i j
  exact h i j

/-- The doubled Hermitian space `V^□ = V ⊕ (-V)` used in Piatetski-Shapiro–Rallis doubling. -/
def doubled (H : HermSpaceCM E F V) : HermSpaceCM E F (V × V) :=
  H.directSum H.neg

@[simp]
lemma doubled_form (H : HermSpaceCM E F V) (x y : V × V) :
    H.doubled.form x y = H.form x.1 y.1 - H.form x.2 y.2 := by
  simp [doubled, sub_eq_add_neg]

/-- The diagonal Lagrangian subspace `V^Δ = {(v, v) | v ∈ V} ⊆ V^□` is totally isotropic. -/
def diagonalSubspace (_H : HermSpaceCM E F V) : Submodule E (V × V) where
  carrier := { p | p.1 = p.2 }
  zero_mem' := rfl
  add_mem' := fun ha hb => by simp_all
  smul_mem' := fun c x (h : x.1 = x.2) => by
    change c • x.1 = c • x.2
    rw [h]

theorem doubled_form_diagonal_eq_zero (H : HermSpaceCM E F V) {x y : V × V}
    (hx : x ∈ H.diagonalSubspace) (hy : y ∈ H.diagonalSubspace) :
    H.doubled.form x y = 0 := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  change x₁ = x₂ at hx
  change y₁ = y₂ at hy
  subst hx; subst hy
  simp [doubled_form]

end HermSpaceCM

/-- Isometric `E`-linear equivalence between two CM Hermitian spaces. -/
structure HermIsom {E F V₁ V₂ : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁]
    [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (H₁ : HermSpaceCM E F V₁) (H₂ : HermSpaceCM E F V₂) where
  toLinearEquiv : V₁ ≃ₗ[E] V₂
  map_form : ∀ x y : V₁, H₂.form (toLinearEquiv x) (toLinearEquiv y) = H₁.form x y

end HermitianForms

/-! ## Section 3: Unitary Groups (`UnitaryGrp`, `UnitaryMatGrp`, `UnitaryPts`) & Doubling Maps -/

section UnitaryGroups

/-- Coordinate-free unitary group `U(V)(E) ≤ GL_E(V)` of a CM Hermitian space `H : HermSpaceCM E F V`. -/
def UnitaryGrp {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) : Subgroup (V ≃ₗ[E] V) where
  carrier := { g | ∀ x y : V, H.form (g x) (g y) = H.form x y }
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change H.form (a (b x)) (a (b y)) = H.form x y
    rw [ha, hb]
  inv_mem' := by
    intro g hg x y
    have h := hg (g.symm x) (g.symm y)
    change H.form (g (g.symm x)) (g (g.symm y)) = H.form (g.symm x) (g.symm y) at h
    simpa using h.symm

/-- Matrix unitary group `U(J)(A) = { g ∈ GL_n(A) | cT σ g * J * g = J }`. -/
def UnitaryMatGrp {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := { g | conjTransposeMap σ (g : Matrix n n A) * J * (g : Matrix n n A) = J }
  one_mem' := by simp [conjTransposeMap_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc conjTransposeMap σ ((a : Matrix n n A) * (b : Matrix n n A)) * J *
            ((a : Matrix n n A) * (b : Matrix n n A))
        = conjTransposeMap σ (b : Matrix n n A) *
            (conjTransposeMap σ (a : Matrix n n A) * J * (a : Matrix n n A)) *
            (b : Matrix n n A) := by
          rw [conjTransposeMap_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc conjTransposeMap σ ((g⁻¹ : GL n A) : Matrix n n A) * J *
            ((g⁻¹ : GL n A) : Matrix n n A)
        = conjTransposeMap σ ((g⁻¹ : GL n A) : Matrix n n A) *
            (conjTransposeMap σ (g : Matrix n n A) * J * (g : Matrix n n A)) *
            ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = conjTransposeMap σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J *
            ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [conjTransposeMap_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, conjTransposeMap_one, Matrix.one_mul, Matrix.mul_one]

/-- Functorial base-change map `GL_n(A) →* GL_n(B)` induced by a ring homomorphism `φ : A →+* B`. -/
def baseChangeGL {A B : Type*} [CommRing A] [CommRing B] {n : Type*} [Fintype n] [DecidableEq n]
    (φ : A →+* B) : GL n A →* GL n B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

lemma baseChangeGL_apply_matrix {A B : Type*} [CommRing A] [CommRing B]
    {n : Type*} [Fintype n] [DecidableEq n] (φ : A →+* B) (g : GL n A) :
    ((baseChangeGL φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ := rfl

theorem baseChangeGL_injective {A B : Type*} [CommRing A] [CommRing B]
    {n : Type*} [Fintype n] [DecidableEq n] {φ : A →+* B} (hφ : Function.Injective φ) :
    Function.Injective (baseChangeGL (n := n) φ) := by
  intro g₁ g₂ h
  apply Units.ext
  ext i j
  apply hφ
  have hij := congrFun (congrFun (congrArg (fun u : GL n B => (u : Matrix n n B)) h) i) j
  simpa [baseChangeGL_apply_matrix] using hij

theorem baseChangeGL_mem_unitaryMatGrp {A B : Type*} [CommRing A] [CommRing B]
    {n : Type*} [Fintype n] [DecidableEq n] (σA : A →+* A) (σB : B →+* B)
    (φ : A →+* B) (hφ : φ.comp σA = σB.comp φ) (J : Matrix n n A)
    {g : GL n A} (hg : g ∈ UnitaryMatGrp σA J) :
    baseChangeGL φ g ∈ UnitaryMatGrp σB (J.map φ) := by
  change conjTransposeMap σB ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ =
    J.map φ
  have hc : conjTransposeMap σB ((g : Matrix n n A).map φ) =
      (conjTransposeMap σA (g : Matrix n n A)).map φ := by
    ext i j
    simp only [conjTransposeMap_apply, Matrix.map_apply]
    exact (RingHom.congr_fun hφ _).symm
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]

/-- Exact group isomorphism `UnitaryGrp H ≃* UnitaryMatGrp H.cm.conjRingHom H.gram`
via the reference frame `H.frame`. -/
def unitaryGrpEquivMat {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) :
    UnitaryGrp H ≃* UnitaryMatGrp H.cm.conjRingHom H.gram where
  toFun g :=
    ⟨⟨LinearMap.toMatrix H.frame H.frame (g.1 : V →ₗ[E] V),
      LinearMap.toMatrix H.frame H.frame (g.1.symm : V →ₗ[E] V),
      by rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id],
      by rw [← LinearMap.toMatrix_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
          LinearEquiv.refl_toLinearMap, LinearMap.toMatrix_id]⟩,
      by
        change conjTransposeMap H.cm.conjRingHom
            (LinearMap.toMatrix H.frame H.frame (g.1 : V →ₗ[E] V)) *
            H.gram * LinearMap.toMatrix H.frame H.frame (g.1 : V →ₗ[E] V) = H.gram
        ext a b
        rw [hermFormMatrix_gram]
        have hrepr : ∀ k : Fin H.dim,
            (H.frame.repr (g.1 (H.frame k)) : Fin H.dim → E) =
              fun i => LinearMap.toMatrix H.frame H.frame (g.1 : V →ₗ[E] V) i k := by
          intro k; ext i; exact (LinearMap.toMatrix_apply H.frame H.frame _ i k).symm
        have h1 := H.form_eq_hermFormMatrix (g.1 (H.frame a)) (g.1 (H.frame b))
        rw [hrepr a, hrepr b] at h1
        rw [← h1, g.2 (H.frame a) (H.frame b)]
        rfl⟩
  invFun M :=
    ⟨LinearEquiv.ofLinearMap
        (Matrix.toLin H.frame H.frame (M.1 : Matrix (Fin H.dim) (Fin H.dim) E))
        (Matrix.toLin H.frame H.frame ((M.1⁻¹ : GL (Fin H.dim) E) : Matrix _ _ E))
        (by rw [← Matrix.toLin_mul, Units.mul_inv, Matrix.toLin_one])
        (by rw [← Matrix.toLin_mul, Units.inv_mul, Matrix.toLin_one]),
      by
        intro x y
        rw [H.form_eq_hermFormMatrix, H.form_eq_hermFormMatrix]
        have hrep : ∀ z : V,
            (H.frame.repr ((Matrix.toLin H.frame H.frame (M.1 : Matrix _ _ E)) z) : Fin H.dim → E) =
              (M.1 : Matrix _ _ E) *ᵥ H.frame.repr z := by
          intro z
          ext i
          have h := congrFun (LinearMap.toMatrix_mulVec_repr H.frame H.frame
            (Matrix.toLin H.frame H.frame (M.1 : Matrix (Fin H.dim) (Fin H.dim) E)) z) i
          rw [LinearMap.toMatrix_toLin] at h
          exact h.symm
        change hermFormMatrix H.cm.conjRingHom H.gram
            (H.frame.repr ((Matrix.toLin H.frame H.frame (M.1 : Matrix _ _ E)) x))
            (H.frame.repr ((Matrix.toLin H.frame H.frame (M.1 : Matrix _ _ E)) y)) = _
        rw [hrep x, hrep y, hermFormMatrix_conj_mulVec, M.2]⟩
  map_mul' g₁ g₂ := by
    apply Subtype.ext
    apply Units.ext
    change LinearMap.toMatrix H.frame H.frame ((g₁.1 * g₂.1 : V ≃ₗ[E] V) : V →ₗ[E] V) =
      LinearMap.toMatrix H.frame H.frame (g₁.1 : V →ₗ[E] V) *
        LinearMap.toMatrix H.frame H.frame (g₂.1 : V →ₗ[E] V)
    rw [← LinearMap.toMatrix_comp]
    rfl
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change (Matrix.toLin H.frame H.frame (LinearMap.toMatrix H.frame H.frame (g.1 : V →ₗ[E] V))) x = g.1 x
    rw [Matrix.toLin_toMatrix]
    rfl
  right_inv M := by
    apply Subtype.ext
    apply Units.ext
    change LinearMap.toMatrix H.frame H.frame
      (Matrix.toLin H.frame H.frame (M.1 : Matrix (Fin H.dim) (Fin H.dim) E)) = M.1
    exact LinearMap.toMatrix_toLin H.frame H.frame M.1

section TensorPoints

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Tensor-extended involution `σ ⊗ id_R` on `E ⊗[F] R`. -/
def sigTensor (σ : E →ₐ[F] E) (R : Type*) [CommRing R] [Algebra F R] :
    E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

/-- Canonical inclusion `E →+* E ⊗[F] R`, `e ↦ e ⊗ 1`. -/
def inclE (R : Type*) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

lemma inclE_comp_sig (σ : E →ₐ[F] E) (R : Type*) [CommRing R] [Algebra F R] :
    (inclE (E := E) R).comp (σ : E →+* E) = (sigTensor σ R).comp (inclE (E := E) R) := by
  ext e
  simp [inclE, sigTensor]

/-- `R`-points `U(J)(R) ≤ GL_n(E ⊗_F R)` of the unitary group attached to `(σ, J)`. -/
def UnitaryPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type*) [CommRing R] [Algebra F R] :
    Subgroup (GL n (E ⊗[F] R)) :=
  UnitaryMatGrp (sigTensor σ R) (J.map (inclE (E := E) R))

/-- Rational embedding `U(J)(E) →* U(J)(R)` via `e ↦ e ⊗ 1`. -/
def ratPtsHom (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type*) [CommRing R] [Algebra F R] :
    UnitaryMatGrp (σ : E →+* E) J →* UnitaryPts σ J R where
  toFun g := ⟨baseChangeGL (inclE R) g.1,
    baseChangeGL_mem_unitaryMatGrp (σ : E →+* E) (sigTensor σ R) (inclE R)
      (inclE_comp_sig σ R) J g.2⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' a b := by apply Subtype.ext; exact map_mul _ a.1 b.1

end TensorPoints

section TensorPointsField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  {n : Type*} [Fintype n] [DecidableEq n]

lemma inclE_injective_of_nontrivial (R : Type*) [CommRing R] [Nontrivial R] [Algebra F R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  haveI : Module.Free F R := Module.Free.of_divisionRing F R
  let b := Module.Free.chooseBasis F R
  have h1 : (1 : R) ≠ 0 := one_ne_zero
  have hi : b.repr 1 ≠ 0 := fun h => h1 (b.repr.injective (by simp [h]))
  obtain ⟨i₀, hi₀⟩ := Finsupp.support_nonempty_iff.mpr hi
  have hi₀' : b.repr 1 i₀ ≠ 0 := Finsupp.mem_support_iff.mp hi₀
  let φ : R →ₗ[F] F := (b.repr 1 i₀)⁻¹ • b.coord i₀
  have hφ1 : φ 1 = 1 := by
    simp [φ, inv_mul_cancel₀ hi₀']
  let retract : E ⊗[F] R →ₗ[F] E := (TensorProduct.rid F E).toLinearMap ∘ₗ φ.lTensor E
  have hleft : ∀ e : E, retract (inclE (F := F) (E := E) R e) = e := fun e => by
    simp [retract, inclE, hφ1]
  intro x y hxy
  have hret := congrArg retract hxy
  simpa [hleft] using hret

theorem ratPtsHom_injective (σ : E →ₐ[F] E) (J : Matrix n n E)
    (R : Type*) [CommRing R] [Nontrivial R] [Algebra F R] :
    Function.Injective (ratPtsHom σ J R) := by
  intro g₁ g₂ h
  apply Subtype.ext
  exact baseChangeGL_injective (inclE_injective_of_nontrivial (F := F) (E := E) R)
    (congrArg Subtype.val h)

end TensorPointsField

section DoublingMaps

variable {E F V V₁ V₂ : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁]
  [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]

/-- Direct-sum embedding `U(V₁) × U(V₂) →* U(V₁ ⊕ V₂)`. -/
def UnitaryGrp.directSumEmbed (H₁ : HermSpaceCM E F V₁) (H₂ : HermSpaceCM E F V₂) :
    UnitaryGrp H₁ × UnitaryGrp H₂ →* UnitaryGrp (H₁.directSum H₂) where
  toFun p :=
    ⟨LinearEquiv.prodCongr p.1.1 p.2.1, fun x y => by
      simp only [HermSpaceCM.directSum_form, LinearEquiv.prodCongr_apply]
      rw [p.1.2 x.1 y.1, p.2.2 x.2 y.2]⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro ⟨x₁, x₂⟩; rfl
  map_mul' a b := by
    apply Subtype.ext; apply LinearEquiv.ext; intro ⟨x₁, x₂⟩; rfl

/-- Doubling embedding `U(V) × U(V) →* U(V ⊕ (-V))` for Piatetski-Shapiro–Rallis doubling. -/
def UnitaryGrp.doubledEmbed (H : HermSpaceCM E F V) :
    UnitaryGrp H × UnitaryGrp H →* UnitaryGrp H.doubled where
  toFun p :=
    ⟨LinearEquiv.prodCongr p.1.1 p.2.1, fun x y => by
      simp only [HermSpaceCM.doubled_form, LinearEquiv.prodCongr_apply]
      rw [p.1.2 x.1 y.1, p.2.2 x.2 y.2]⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro ⟨x₁, x₂⟩; rfl
  map_mul' a b := by
    apply Subtype.ext; apply LinearEquiv.ext; intro ⟨x₁, x₂⟩; rfl

/-- Diagonal subgroup embedding `U(V) →* U(V ⊕ (-V))`, `g ↦ (g, g)`, stabilizing `V^Δ`. -/
def UnitaryGrp.diagDoubledEmbed (H : HermSpaceCM E F V) :
    UnitaryGrp H →* UnitaryGrp H.doubled :=
  (UnitaryGrp.doubledEmbed H).comp ((MonoidHom.id (UnitaryGrp H)).prod (MonoidHom.id (UnitaryGrp H)))

theorem UnitaryGrp.diagDoubledEmbed_stabilizes_diagonal (H : HermSpaceCM E F V)
    (g : UnitaryGrp H) {x : V × V} (hx : x ∈ H.diagonalSubspace) :
    (UnitaryGrp.diagDoubledEmbed H g).1 x ∈ H.diagonalSubspace := by
  change (g.1 x.1, g.1 x.2).1 = (g.1 x.1, g.1 x.2).2
  exact congrArg g.1 hx

end DoublingMaps

end UnitaryGroups

/-! ## Section 4: Hermitian Signature `(p, q)`, Sylvester's Law of Inertia, `DefiniteHermSpace` & `IndefiniteHermSpace` -/

section SignatureAndDefiniteness

/-- Standard diagonal signature `(p, q)` matrix `diag(I_p, -I_q)` over `ℂ`. -/
def Jpq (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

lemma Jpq_isHermitian (p q : ℕ) : (Jpq p q).IsHermitian := by
  ext i j
  cases i <;> cases j <;> simp [Jpq, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]

private lemma reindex_mul_self {m n R : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [NonUnitalNonAssocSemiring R] (e : m ≃ n) (A B : Matrix m m R) :
    A.reindex e e * B.reindex e e = (A * B).reindex e e := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact Equiv.sum_comp e.symm (fun k => A (e.symm i) k * B k (e.symm j))

private lemma reindex_one_self {m n R : Type*} [DecidableEq m] [DecidableEq n]
    [Zero R] [One R] (e : m ≃ n) :
    (1 : Matrix m m R).reindex e e = 1 := by
  ext i j
  simp [Matrix.one_apply]

/-- Concrete predicate that a complex matrix `J` has Hermitian signature `(p, q)`. -/
def HasSignature {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (p q : ℕ) : Prop :=
  ∃ (e : n ≃ Fin p ⊕ Fin q) (P : GL (Fin p ⊕ Fin q) ℂ),
    (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * J.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Jpq p q

lemma hasSignature_card {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℂ} {p q : ℕ} (h : HasSignature J p q) :
    p + q = Fintype.card n := by
  obtain ⟨e, -, -⟩ := h
  have hcard := Fintype.card_congr e
  simpa [Fintype.card_sum, Fintype.card_fin] using hcard.symm

lemma hasSignature_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℂ} {p q : ℕ} (h : HasSignature J p q) :
    J.IsHermitian := by
  obtain ⟨e, P, hP⟩ := h
  have hJre : (J.reindex e e).IsHermitian := by
    have h1 : J.reindex e e =
        ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)ᴴ * Jpq p q *
          ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ) := by
      have hPin : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *
          ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ) = 1 := Units.mul_inv P
      have hPinH : ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)ᴴ *
          (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, hPin, Matrix.conjTranspose_one]
      calc J.reindex e e
          = 1 * J.reindex e e * 1 := by simp
        _ = (((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᴴ * (P : Matrix _ _ ℂ)ᴴ) * J.reindex e e *
              ((P : Matrix _ _ ℂ) * ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) := by
            rw [hPinH, hPin]
        _ = ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᴴ *
              ((P : Matrix _ _ ℂ)ᴴ * J.reindex e e * (P : Matrix _ _ ℂ)) *
              ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP]
    unfold Matrix.IsHermitian
    rw [h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (Jpq_isHermitian p q).eq, Matrix.mul_assoc]
  ext i j
  have hij := congrFun (congrFun hJre (e i)) (e j)
  simpa [Matrix.conjTranspose_apply] using hij

lemma hasSignature_isUnit_det {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℂ} {p q : ℕ} (h : HasSignature J p q) :
    IsUnit J.det := by
  obtain ⟨e, P, hP⟩ := h
  have hJpq : IsUnit (Jpq p q).det := by
    unfold Jpq
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one,
      Fintype.card_fin, one_mul, mul_one]
    exact (pow_ne_zero q (by norm_num : (-1 : ℂ) ≠ 0)).isUnit
  have hdetP : IsUnit (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 := congrArg Matrix.det (congrArg Units.val (mul_inv_cancel P))
    rw [Units.val_mul, Units.val_one, Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  have hdetPH : IsUnit ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ).det := by
    rw [Matrix.det_conjTranspose, isUnit_iff_ne_zero]
    exact star_ne_zero.mpr hdetP.ne_zero
  have hPdet := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self] at hPdet
  have hre : IsUnit ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ.det * J.det *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det) := by
    rw [hPdet]; exact hJpq
  rw [IsUnit.mul_iff, IsUnit.mul_iff] at hre
  exact hre.1.2

lemma hasSignature_neg {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℂ} {p q : ℕ} (h : HasSignature J p q) :
    HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let sw : Fin p ⊕ Fin q ≃ Fin q ⊕ Fin p := Equiv.sumComm (Fin p) (Fin q)
  refine ⟨e.trans sw,
    ⟨((P : Matrix _ _ ℂ).reindex sw sw), (((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).reindex sw sw), ?_, ?_⟩, ?_⟩
  · rw [reindex_mul_self, Units.mul_inv, reindex_one_self]
  · rw [reindex_mul_self, Units.inv_mul, reindex_one_self]
  · change ((P : Matrix _ _ ℂ).reindex sw sw)ᴴ * (-J).reindex (e.trans sw) (e.trans sw) *
        ((P : Matrix _ _ ℂ).reindex sw sw) = Jpq q p
    have hre1 : (-J).reindex (e.trans sw) (e.trans sw) = -(J.reindex e e).reindex sw sw := by
      ext i j; simp
    have hre2 : ((P : Matrix _ _ ℂ).reindex sw sw)ᴴ =
        ((P : Matrix _ _ ℂ)ᴴ).reindex sw sw := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [hre1, hre2, Matrix.mul_neg, Matrix.neg_mul, reindex_mul_self, reindex_mul_self, hP]
    ext i j
    cases i <;> cases j <;> simp [Jpq, sw, Matrix.one_apply]

lemma hasSignature_directSum {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂]
    {J₁ : Matrix n₁ n₁ ℂ} {J₂ : Matrix n₂ n₂ ℂ} {p₁ q₁ p₂ q₂ : ℕ}
    (h₁ : HasSignature J₁ p₁ q₁) (h₂ : HasSignature J₂ p₂ q₂) :
    HasSignature (Matrix.fromBlocks J₁ 0 0 J₂) (p₁ + p₂) (q₁ + q₂) := by
  obtain ⟨e₁, P₁, hP₁⟩ := h₁
  obtain ⟨e₂, P₂, hP₂⟩ := h₂
  let s₁ : (Fin p₁ ⊕ Fin q₁) ⊕ (Fin p₂ ⊕ Fin q₂) ≃ Fin (p₁ + p₂) ⊕ Fin (q₁ + q₂) :=
    (Equiv.sumAssoc _ _ _).trans <|
      (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumAssoc _ _ _).symm.trans
        (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _)) |>.trans (Equiv.sumAssoc _ _ _))).trans <|
      (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)
  let e : n₁ ⊕ n₂ ≃ Fin (p₁ + p₂) ⊕ Fin (q₁ + q₂) := (Equiv.sumCongr e₁ e₂).trans s₁
  let P0 : GL ((Fin p₁ ⊕ Fin q₁) ⊕ (Fin p₂ ⊕ Fin q₂)) ℂ :=
    ⟨Matrix.fromBlocks (P₁ : Matrix _ _ ℂ) 0 0 (P₂ : Matrix _ _ ℂ),
     Matrix.fromBlocks ((P₁⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) 0 0 ((P₂⁻¹ : GL _ ℂ) : Matrix _ _ ℂ),
     by rw [Matrix.fromBlocks_multiply]; simp,
     by rw [Matrix.fromBlocks_multiply]; simp⟩
  let P : GL (Fin (p₁ + p₂) ⊕ Fin (q₁ + q₂)) ℂ :=
    ⟨(P0 : Matrix _ _ ℂ).reindex s₁ s₁, ((P0⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).reindex s₁ s₁,
      by rw [reindex_mul_self, Units.mul_inv, reindex_one_self],
      by rw [reindex_mul_self, Units.inv_mul, reindex_one_self]⟩
  refine ⟨e, P, ?_⟩
  have hmid : (P0 : Matrix _ _ ℂ)ᴴ *
      ((Matrix.fromBlocks J₁ 0 0 J₂).reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂)) *
      (P0 : Matrix _ _ ℂ) = Matrix.fromBlocks (Jpq p₁ q₁) 0 0 (Jpq p₂ q₂) := by
    have hreJ : (Matrix.fromBlocks J₁ 0 0 J₂).reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂) =
        Matrix.fromBlocks (J₁.reindex e₁ e₁) 0 0 (J₂.reindex e₂ e₂) := by
      ext i j; cases i <;> cases j <;> simp
    rw [hreJ]
    simp only [P0, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hP₁, hP₂]
  have hfull : (P : Matrix _ _ ℂ)ᴴ * (Matrix.fromBlocks J₁ 0 0 J₂).reindex e e * (P : Matrix _ _ ℂ) =
      (Matrix.fromBlocks (Jpq p₁ q₁) 0 0 (Jpq p₂ q₂)).reindex s₁ s₁ := by
    have h1 : (P : Matrix _ _ ℂ)ᴴ = ((P0 : Matrix _ _ ℂ)ᴴ).reindex s₁ s₁ := by
      ext i j; simp [P, Matrix.conjTranspose_apply]
    have h2 : (Matrix.fromBlocks J₁ 0 0 J₂).reindex e e =
        ((Matrix.fromBlocks J₁ 0 0 J₂).reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂)).reindex s₁ s₁ := by
      ext i j; simp [e]
    rw [h1, h2]
    change (((P0 : Matrix _ _ ℂ)ᴴ).reindex s₁ s₁) *
        (((Matrix.fromBlocks J₁ 0 0 J₂).reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂)).reindex s₁ s₁) *
        ((P0 : Matrix _ _ ℂ).reindex s₁ s₁) = _
    rw [reindex_mul_self, reindex_mul_self, hmid]
  rw [hfull]
  ext i j
  rcases hi : s₁.symm i with (a | a) | (a | a) <;>
    rcases hj : s₁.symm j with (b | b) | (b | b)
  all_goals
    have hi' : i = s₁ _ := (Equiv.symm_apply_eq s₁).1 hi
    have hj' : j = s₁ _ := (Equiv.symm_apply_eq s₁).1 hj
    subst hi'; subst hj'
    simp [Jpq, s₁, finSumFinEquiv, Matrix.one_apply, Fin.ext_iff] <;> try omega

private lemma star_dotProduct_Jpq_mulVec (p q : ℕ) (z : Fin p ⊕ Fin q → ℂ) :
    star z ⬝ᵥ (Jpq p q *ᵥ z) =
      (∑ i : Fin p, star (z (Sum.inl i)) * z (Sum.inl i)) -
        (∑ j : Fin q, star (z (Sum.inr j)) * z (Sum.inr j)) := by
  rw [Jpq, Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec, add_zero, zero_add,
    Pi.neg_apply, Pi.star_apply, mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg,
    Function.comp_apply]

private lemma sum_star_mul_self_eq_normSq {m : ℕ} (u : Fin m → ℂ) :
    (∑ i : Fin m, star (u i) * u i) = ((∑ i : Fin m, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/-- **Sylvester's Law of Inertia (`hasSignature_unique`)**:
the Hermitian signature `(p, q)` of a complex matrix `J` is uniquely determined. -/
theorem hasSignature_unique {n : Type*} [Fintype n] [DecidableEq n]
    {J : Matrix n n ℂ} {p₁ q₁ p₂ q₂ : ℕ}
    (h₁ : HasSignature J p₁ q₁) (h₂ : HasSignature J p₂ q₂) :
    p₁ = p₂ ∧ q₁ = q₂ := by
  have hc₁ := hasSignature_card h₁
  have hc₂ := hasSignature_card h₂
  suffices hp : p₁ = p₂ from ⟨hp, by omega⟩
  have hcontra : ∀ {a b c d : ℕ}, HasSignature J a b → HasSignature J c d → a < c → False := by
    intro a b c d ha hc hlt
    have hca := hasSignature_card ha
    have hcc := hasSignature_card hc
    obtain ⟨e₁, P₁, hP₁⟩ := ha
    obtain ⟨e₂, P₂, hP₂⟩ := hc
    let P₂M : Matrix (Fin c ⊕ Fin d) (Fin c ⊕ Fin d) ℂ := P₂
    let P₁M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := P₁
    let Tpos : (Fin c → ℂ) →ₗ[ℂ] (n → ℂ) :=
      { toFun := fun u k => (P₂M *ᵥ Sum.elim u (0 : Fin d → ℂ)) (e₂ k)
        map_add' := fun u₁ u₂ => by
          ext k
          have hsum : Sum.elim (u₁ + u₂) (0 : Fin d → ℂ) =
              Sum.elim u₁ (0 : Fin d → ℂ) + Sum.elim u₂ (0 : Fin d → ℂ) := by
            ext x; cases x <;> simp
          rw [hsum, Matrix.mulVec_add]; rfl
        map_smul' := fun r u => by
          ext k
          have hsm : Sum.elim (r • u) (0 : Fin d → ℂ) = r • Sum.elim u (0 : Fin d → ℂ) := by
            ext x; cases x <;> simp
          rw [hsm, Matrix.mulVec_smul]; rfl }
    let Tneg : (Fin b → ℂ) →ₗ[ℂ] (n → ℂ) :=
      { toFun := fun w k => (P₁M *ᵥ Sum.elim (0 : Fin a → ℂ) w) (e₁ k)
        map_add' := fun w₁ w₂ => by
          ext k
          have hsum : Sum.elim (0 : Fin a → ℂ) (w₁ + w₂) =
              Sum.elim (0 : Fin a → ℂ) w₁ + Sum.elim (0 : Fin a → ℂ) w₂ := by
            ext x; cases x <;> simp
          rw [hsum, Matrix.mulVec_add]; rfl
        map_smul' := fun r w => by
          ext k
          have hsm : Sum.elim (0 : Fin a → ℂ) (r • w) = r • Sum.elim (0 : Fin a → ℂ) w := by
            ext x; cases x <;> simp
          rw [hsm, Matrix.mulVec_smul]; rfl }
    have hTpos_inj : Function.Injective Tpos := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have h0 : P₂M *ᵥ Sum.elim u (0 : Fin d → ℂ) = 0 := by
        ext x
        have hk := congrFun hu (e₂.symm x)
        simpa [Tpos] using hk
      let P₂inv : Matrix (Fin c ⊕ Fin d) (Fin c ⊕ Fin d) ℂ := (P₂⁻¹ : GL (Fin c ⊕ Fin d) ℂ)
      have hP2inv : P₂inv * P₂M = 1 :=
        congrArg Units.val (inv_mul_cancel P₂)
      have h1 : Sum.elim u (0 : Fin d → ℂ) = 0 := by
        have := congrArg (P₂inv *ᵥ ·) h0
        simpa [Matrix.mulVec_mulVec, hP2inv] using this
      ext i
      exact congrFun h1 (Sum.inl i)
    have hTneg_inj : Function.Injective Tneg := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      have h0 : P₁M *ᵥ Sum.elim (0 : Fin a → ℂ) w = 0 := by
        ext x
        have hk := congrFun hw (e₁.symm x)
        simpa [Tneg] using hk
      let P₁inv : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := (P₁⁻¹ : GL (Fin a ⊕ Fin b) ℂ)
      have hP1inv : P₁inv * P₁M = 1 :=
        congrArg Units.val (inv_mul_cancel P₁)
      have h1 : Sum.elim (0 : Fin a → ℂ) w = 0 := by
        have := congrArg (P₁inv *ᵥ ·) h0
        simpa [Matrix.mulVec_mulVec, hP1inv] using this
      ext j
      exact congrFun h1 (Sum.inr j)
    let Wpos : Submodule ℂ (n → ℂ) := LinearMap.range Tpos
    let Wneg : Submodule ℂ (n → ℂ) := LinearMap.range Tneg
    have hdim_pos : Module.finrank ℂ ↥Wpos = c := by
      rw [LinearMap.finrank_range_of_inj hTpos_inj, Module.finrank_fin_fun]
    have hdim_neg : Module.finrank ℂ ↥Wneg = b := by
      rw [LinearMap.finrank_range_of_inj hTneg_inj, Module.finrank_fin_fun]
    have hsum_le : Module.finrank ℂ ↥(Wpos ⊔ Wneg) ≤ Fintype.card n := by
      calc Module.finrank ℂ ↥(Wpos ⊔ Wneg)
          ≤ Module.finrank ℂ (n → ℂ) := Submodule.finrank_le (Wpos ⊔ Wneg)
        _ = Fintype.card n := Module.finrank_fintype_fun_eq_card ℂ
    have hinf_pos : 0 < Module.finrank ℂ ↥(Wpos ⊓ Wneg) := by
      have hmod := Submodule.finrank_sup_add_finrank_inf_eq Wpos Wneg
      rw [hdim_pos, hdim_neg] at hmod
      omega
    have hne_bot : (Wpos ⊓ Wneg) ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hinf_pos
      exact lt_irrefl 0 hinf_pos
    obtain ⟨v, hv_mem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    obtain ⟨⟨u, hu_eq⟩, ⟨w, hw_eq⟩⟩ := hv_mem
    have hu_ne : u ≠ 0 := by
      intro hu0; apply hv0; rw [← hu_eq, hu0, map_zero]
    have hpos_re : 0 < (star v ⬝ᵥ (J *ᵥ v)).re := by
      have hv_reidx : (v ∘ e₂.symm) = P₂M *ᵥ Sum.elim u (0 : Fin d → ℂ) := by
        ext x; simpa [Tpos] using (congrFun hu_eq (e₂.symm x)).symm
      have hdot : star v ⬝ᵥ (J *ᵥ v) = star (v ∘ e₂.symm) ⬝ᵥ (J.reindex e₂ e₂ *ᵥ (v ∘ e₂.symm)) := by
        simp only [dotProduct, Matrix.mulVec]
        rw [← e₂.sum_comp]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.star_apply]
        congr 1
        rw [← e₂.sum_comp]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp
      have hmid : star (Sum.elim u (0 : Fin d → ℂ)) ⬝ᵥ
          (Jpq c d *ᵥ Sum.elim u (0 : Fin d → ℂ)) =
          ((∑ i : Fin c, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
        rw [star_dotProduct_Jpq_mulVec]
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, star_zero, zero_mul,
          Finset.sum_const_zero, sub_zero]
        exact sum_star_mul_self_eq_normSq u
      have hval : star v ⬝ᵥ (J *ᵥ v) = ((∑ i : Fin c, ‖u i‖ ^ 2 : ℝ) : ℂ) := by
        rw [hdot, hv_reidx, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
          ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
        change star (Sum.elim u (0 : Fin d → ℂ)) ⬝ᵥ
            ((P₂Mᴴ * J.reindex e₂ e₂ * P₂M) *ᵥ Sum.elim u (0 : Fin d → ℂ)) = _
        rw [hP₂, hmid]
      rw [hval, Complex.ofReal_re]
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu_ne
      exact Finset.sum_pos' (fun i _ => sq_nonneg _)
        ⟨i₀, Finset.mem_univ _, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi₀)⟩
    have hneg_re : (star v ⬝ᵥ (J *ᵥ v)).re ≤ 0 := by
      have hv_reidx : (v ∘ e₁.symm) = P₁M *ᵥ Sum.elim (0 : Fin a → ℂ) w := by
        ext x; simpa [Tneg] using (congrFun hw_eq (e₁.symm x)).symm
      have hdot : star v ⬝ᵥ (J *ᵥ v) = star (v ∘ e₁.symm) ⬝ᵥ (J.reindex e₁ e₁ *ᵥ (v ∘ e₁.symm)) := by
        simp only [dotProduct, Matrix.mulVec]
        rw [← e₁.sum_comp]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Function.comp_apply, Equiv.symm_apply_apply, Pi.star_apply]
        congr 1
        rw [← e₁.sum_comp]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp
      have hmid : star (Sum.elim (0 : Fin a → ℂ) w) ⬝ᵥ
          (Jpq a b *ᵥ Sum.elim (0 : Fin a → ℂ) w) =
          ((-∑ j : Fin b, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [star_dotProduct_Jpq_mulVec]
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, star_zero, zero_mul,
          Finset.sum_const_zero, zero_sub]
        rw [sum_star_mul_self_eq_normSq w]
        simp
      have hval : star v ⬝ᵥ (J *ᵥ v) = ((-∑ j : Fin b, ‖w j‖ ^ 2 : ℝ) : ℂ) := by
        rw [hdot, hv_reidx, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
          ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
        change star (Sum.elim (0 : Fin a → ℂ) w) ⬝ᵥ
            ((P₁Mᴴ * J.reindex e₁ e₁ * P₁M) *ᵥ Sum.elim (0 : Fin a → ℂ) w) = _
        rw [hP₁, hmid]
      rw [hval, Complex.ofReal_re]
      exact neg_nonpos.mpr (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hcontra h₁ h₂ hlt
  · exact hcontra h₂ h₁ hgt

/-- A matrix `J : Matrix n n ℂ` has signature `(|n|, 0)` if and only if `J.PosDef`. -/
theorem hasSignature_posDef_iff {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) :
    HasSignature J (Fintype.card n) 0 ↔ J.PosDef := by
  constructor
  · intro h
    have hHerm := hasSignature_isHermitian h
    obtain ⟨e, P, hP⟩ := h
    refine ⟨hHerm, fun {x} hx => ?_⟩
    let PM : Matrix (Fin (Fintype.card n) ⊕ Fin 0) (Fin (Fintype.card n) ⊕ Fin 0) ℂ := P
    let PinvM : Matrix (Fin (Fintype.card n) ⊕ Fin 0) (Fin (Fintype.card n) ⊕ Fin 0) ℂ :=
      (P⁻¹ : GL (Fin (Fintype.card n) ⊕ Fin 0) ℂ)
    have hPin : PM * PinvM = 1 := congrArg Units.val (mul_inv_cancel P)
    have hJ : J.reindex e e = PinvMᴴ * 1 * PinvM := by
      have hJpq : Jpq (Fintype.card n) 0 = 1 := by
        ext i j
        rcases i with i | i <;> rcases j with j | j
        · simp [Jpq, Matrix.one_apply]
        · exact j.elim0
        · exact i.elim0
        · exact i.elim0
      have hPinH : PinvMᴴ * PMᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, hPin, Matrix.conjTranspose_one]
      calc J.reindex e e
          = (PinvMᴴ * PMᴴ) * J.reindex e e * (PM * PinvM) := by
            rw [hPinH, hPin]; simp
        _ = PinvMᴴ * (PMᴴ * J.reindex e e * PM) * PinvM := by
            simp only [Matrix.mul_assoc]
        _ = PinvMᴴ * 1 * PinvM := by
            rw [hP, hJpq]
    let y : Fin (Fintype.card n) ⊕ Fin 0 → ℂ := PinvM *ᵥ (fun k => x (e.symm k))
    have hyne : y ≠ 0 := by
      intro hy0
      apply hx
      ext i
      have h2 := congrArg (PM *ᵥ ·) hy0
      simp only [y, Matrix.mulVec_mulVec, hPin, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h2
      have h3 := congrFun h2 (e i)
      simpa using h3
    have hform : (x.sum fun i xi => x.sum fun j xj => star xi * J i j * xj) =
        star (fun k => x (e.symm k)) ⬝ᵥ (J.reindex e e *ᵥ (fun k => x (e.symm k))) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      have hR : ∀ i, (x.sum fun j xj => star (x i) * J i j * xj) =
          ∑ j, star (x i) * J i j * x j := fun i => Finsupp.sum_fintype _ _ (fun _ => by simp)
      simp_rw [hR]
      rw [← e.symm.sum_comp]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← e.symm.sum_comp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp [mul_assoc]
    rw [hform, hJ, Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec]
    change star y ⬝ᵥ y > 0
    have hsum : star y ⬝ᵥ y = ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    rw [hsum, gt_iff_lt, Complex.lt_def]
    simp only [Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im, and_true]
    obtain ⟨k₀, hk₀⟩ := Function.ne_iff.mp hyne
    exact Finset.sum_pos' (fun k _ => sq_nonneg _)
      ⟨k₀, Finset.mem_univ _, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hk₀)⟩
  · intro hPos
    let e0 : n ≃ Fin (Fintype.card n) := Fintype.equivFin n
    let e : n ≃ Fin (Fintype.card n) ⊕ Fin 0 := e0.trans (Equiv.sumEmpty _ _).symm
    let U : Matrix n n ℂ := hPos.isHermitian.eigenvectorUnitary
    let Dinv : Matrix n n ℂ := Matrix.diagonal fun i =>
      (((Real.sqrt (hPos.isHermitian.eigenvalues i))⁻¹ : ℝ) : ℂ)
    let D : Matrix n n ℂ := Matrix.diagonal fun i =>
      ((Real.sqrt (hPos.isHermitian.eigenvalues i) : ℝ) : ℂ)
    let Q : Matrix n n ℂ := U * Dinv
    let Qinv : Matrix n n ℂ := D * star U
    have hDD : D * Dinv = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        have hpos : 0 < Real.sqrt (hPos.isHermitian.eigenvalues i) :=
          Real.sqrt_pos.mpr (hPos.eigenvalues_pos i)
        simp only [Matrix.diagonal_apply_eq]
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, Matrix.one_apply_eq]
      · simp [hij]
    have hDinvD : Dinv * D = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        have hpos : 0 < Real.sqrt (hPos.isHermitian.eigenvalues i) :=
          Real.sqrt_pos.mpr (hPos.eigenvalues_pos i)
        simp only [Matrix.diagonal_apply_eq]
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, Matrix.one_apply_eq]
      · simp [hij]
    have hQQinv : Q * Qinv = 1 := by
      calc U * Dinv * (D * star U) = U * (Dinv * D) * star U := by simp only [Matrix.mul_assoc]
        _ = U * star U := by rw [hDinvD, Matrix.mul_one]
        _ = 1 := hPos.isHermitian.eigenvectorUnitary.2.2
    have hQinvQ : Qinv * Q = 1 := by
      calc D * star U * (U * Dinv) = D * (star U * U) * Dinv := by simp only [Matrix.mul_assoc]
        _ = D * Dinv := by rw [hPos.isHermitian.eigenvectorUnitary.2.1, Matrix.mul_one]
        _ = 1 := hDD
    let P : GL (Fin (Fintype.card n) ⊕ Fin 0) ℂ :=
      ⟨Q.reindex e e, Qinv.reindex e e,
        by rw [reindex_mul_self, hQQinv, reindex_one_self],
        by rw [reindex_mul_self, hQinvQ, reindex_one_self]⟩
    refine ⟨e, P, ?_⟩
    have hQHJQ : Qᴴ * J * Q = 1 := by
      have hspec : J = U * Matrix.diagonal (RCLike.ofReal ∘ hPos.isHermitian.eigenvalues) * star U := by
        simpa [U, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
          hPos.isHermitian.spectral_theorem
      have hDinvH : Dinvᴴ = Dinv := by
        rw [Matrix.diagonal_conjTranspose]
        congr 1; funext i; simp
      have hQH : Qᴴ = Dinv * star U := by
        simp only [Q, Matrix.conjTranspose_mul, hDinvH]; rfl
      calc Qᴴ * J * Q
          = (Dinv * star U) *
              (U * Matrix.diagonal (RCLike.ofReal ∘ hPos.isHermitian.eigenvalues) * star U) *
              (U * Dinv) := by
            rw [hQH]; conv_lhs => rw [hspec]
        _ = Dinv * (star U * U) * Matrix.diagonal (RCLike.ofReal ∘ hPos.isHermitian.eigenvalues) *
              (star U * U) * Dinv := by simp only [Matrix.mul_assoc]
        _ = Dinv * Matrix.diagonal (RCLike.ofReal ∘ hPos.isHermitian.eigenvalues) * Dinv := by
            rw [hPos.isHermitian.eigenvectorUnitary.2.1, Matrix.mul_one, Matrix.mul_one]
        _ = 1 := by
            rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
            ext i j
            by_cases hij : i = j
            · subst hij
              have hpos : 0 < hPos.isHermitian.eigenvalues i := hPos.eigenvalues_pos i
              have hsq : Real.sqrt (hPos.isHermitian.eigenvalues i) ≠ 0 :=
                (Real.sqrt_pos.mpr hpos).ne'
              rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
              simp only [Function.comp_apply]
              rw [show (RCLike.ofReal (hPos.isHermitian.eigenvalues i) : ℂ) =
                (hPos.isHermitian.eigenvalues i : ℂ) from rfl,
                ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
              congr 1
              have hmul : Real.sqrt (hPos.isHermitian.eigenvalues i) ^ 2 =
                  hPos.isHermitian.eigenvalues i := Real.sq_sqrt hpos.le
              field_simp [hsq]
              exact hmul.symm
            · simp [hij]
    have hP1 : (P : Matrix _ _ ℂ)ᴴ * J.reindex e e * (P : Matrix _ _ ℂ) = 1 := by
      have hreH : (P : Matrix _ _ ℂ)ᴴ = Qᴴ.reindex e e := by
        ext i j; simp [P, Matrix.conjTranspose_apply]
      rw [hreH]
      change (Qᴴ.reindex e e) * (J.reindex e e) * (Q.reindex e e) = 1
      rw [reindex_mul_self, reindex_mul_self, hQHJQ, reindex_one_self]
    rw [hP1]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Jpq, Matrix.one_apply]
    · exact j.elim0
    · exact i.elim0
    · exact i.elim0

/-- A matrix `J : Matrix n n ℂ` has signature `(0, |n|)` if and only if `(-J).PosDef`. -/
theorem hasSignature_negDef_iff {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) :
    HasSignature J 0 (Fintype.card n) ↔ (-J).PosDef := by
  constructor
  · intro h
    exact (hasSignature_posDef_iff (-J)).1 (hasSignature_neg h)
  · intro h
    have h1 := (hasSignature_posDef_iff (-J)).2 h
    simpa using hasSignature_neg h1

/-- Every invertible Hermitian matrix `J : Matrix n n ℂ` admits a signature `(p, q)` with
`p + q = Fintype.card n`. -/
theorem exists_hasSignature_of_isHermitian_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hH : J.IsHermitian) (hdet : IsUnit J.det) :
    ∃ p q : ℕ, HasSignature J p q := by
  classical
  let ev := hH.eigenvalues
  let U : Matrix n n ℂ := hH.eigenvectorUnitary
  have hev_ne : ∀ i : n, ev i ≠ 0 := by
    intro i hi
    have hspec : J = U * Matrix.diagonal (RCLike.ofReal ∘ ev) * star U := by
      simpa [U, ev, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using hH.spectral_theorem
    have hdet0 : J.det = 0 := by
      have hzi : ((RCLike.ofReal ∘ ev : n → ℂ) i) = 0 := by simp [hi]
      have hprod0 : (∏ j : n, (RCLike.ofReal ∘ ev : n → ℂ) j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzi
      conv_lhs => rw [hspec]
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hprod0, mul_zero, zero_mul]
    exact hdet.ne_zero hdet0
  let sPos : Finset n := Finset.univ.filter (fun i => 0 < ev i)
  let sNeg : Finset n := Finset.univ.filter (fun i => ev i < 0)
  have hdisj : Disjoint sPos sNeg := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [sPos, sNeg, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    linarith
  have hunion : sPos ∪ sNeg = Finset.univ := by
    ext i
    simp only [Finset.mem_union, sPos, sNeg, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    exact lt_or_gt_of_ne (hev_ne i).symm
  let p := sPos.card
  let q := sNeg.card
  let ePos : sPos ≃ Fin p := sPos.equivFin
  let eNeg : sNeg ≃ Fin q := sNeg.equivFin
  let eSum : n ≃ sPos ⊕ sNeg :=
    { toFun := fun i => if hi : i ∈ sPos then Sum.inl ⟨i, hi⟩ else Sum.inr ⟨i, by
        have := hunion ▸ Finset.mem_univ i
        rcases Finset.mem_union.1 this with h1 | h2
        · exact absurd h1 hi
        · exact h2⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := fun i => by by_cases hi : i ∈ sPos <;> simp [hi]
      right_inv := fun x => by
        rcases x with ⟨i, hi⟩ | ⟨i, hi⟩
        · simp [hi]
        · have hnot : i ∉ sPos := Finset.disjoint_right.1 hdisj hi
          simp [hnot] }
  let e : n ≃ Fin p ⊕ Fin q := eSum.trans (Equiv.sumCongr ePos eNeg)
  let Dinv : Matrix n n ℂ := Matrix.diagonal fun i =>
    (((Real.sqrt |ev i|)⁻¹ : ℝ) : ℂ)
  let D : Matrix n n ℂ := Matrix.diagonal fun i =>
    ((Real.sqrt |ev i| : ℝ) : ℂ)
  let Q : Matrix n n ℂ := U * Dinv
  let Qinv : Matrix n n ℂ := D * star U
  have hDinvD : Dinv * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hpos : 0 < Real.sqrt |ev i| := Real.sqrt_pos.mpr (abs_pos.mpr (hev_ne i))
      simp only [Matrix.diagonal_apply_eq]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one, Matrix.one_apply_eq]
    · simp [hij]
  have hDDinv : D * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hpos : 0 < Real.sqrt |ev i| := Real.sqrt_pos.mpr (abs_pos.mpr (hev_ne i))
      simp only [Matrix.diagonal_apply_eq]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, Matrix.one_apply_eq]
    · simp [hij]
  have hQQinv : Q * Qinv = 1 := by
    calc U * Dinv * (D * star U) = U * (Dinv * D) * star U := by simp only [Matrix.mul_assoc]
      _ = U * star U := by rw [hDinvD, Matrix.mul_one]
      _ = 1 := hH.eigenvectorUnitary.2.2
  have hQinvQ : Qinv * Q = 1 := by
    calc D * star U * (U * Dinv) = D * (star U * U) * Dinv := by simp only [Matrix.mul_assoc]
      _ = D * Dinv := by rw [hH.eigenvectorUnitary.2.1, Matrix.mul_one]
      _ = 1 := hDDinv
  let P : GL (Fin p ⊕ Fin q) ℂ :=
    ⟨Q.reindex e e, Qinv.reindex e e,
      by rw [reindex_mul_self, hQQinv, reindex_one_self],
      by rw [reindex_mul_self, hQinvQ, reindex_one_self]⟩
  refine ⟨p, q, e, P, ?_⟩
  have hQHJQ : Qᴴ * J * Q = Matrix.diagonal fun i => if 0 < ev i then (1 : ℂ) else -1 := by
    have hspec : J = U * Matrix.diagonal (RCLike.ofReal ∘ ev) * star U := by
      simpa [U, ev, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using hH.spectral_theorem
    have hDinvH : Dinvᴴ = Dinv := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1; funext i; simp
    have hQH : Qᴴ = Dinv * star U := by
      simp only [Q, Matrix.conjTranspose_mul, hDinvH]; rfl
    calc Qᴴ * J * Q
        = (Dinv * star U) * (U * Matrix.diagonal (RCLike.ofReal ∘ ev) * star U) * (U * Dinv) := by
          rw [hQH]; conv_lhs => rw [hspec]
      _ = Dinv * (star U * U) * Matrix.diagonal (RCLike.ofReal ∘ ev) * (star U * U) * Dinv := by
          simp only [Matrix.mul_assoc]
      _ = Dinv * Matrix.diagonal (RCLike.ofReal ∘ ev) * Dinv := by
          rw [hH.eigenvectorUnitary.2.1, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by
          rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
          ext i j
          by_cases hij : i = j
          · subst hij
            simp only [Matrix.diagonal_apply_eq, Function.comp_apply]
            rw [show (RCLike.ofReal (ev i) : ℂ) = (ev i : ℂ) from rfl,
              ← Complex.ofReal_mul, ← Complex.ofReal_mul]
            have hsq : Real.sqrt |ev i| ≠ 0 := (Real.sqrt_pos.mpr (abs_pos.mpr (hev_ne i))).ne'
            by_cases hpos : 0 < ev i
            · rw [if_pos hpos, ← Complex.ofReal_one]
              congr 1
              have hmul : Real.sqrt (ev i) ^ 2 = ev i := Real.sq_sqrt hpos.le
              rw [abs_of_pos hpos]
              field_simp [hsq]
              exact hmul.symm
            · rw [if_neg hpos]
              have hneg : ev i < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hev_ne i)
              have hreal : (Real.sqrt |ev i|)⁻¹ * ev i * (Real.sqrt |ev i|)⁻¹ = -1 := by
                rw [abs_of_neg hneg]
                have hmul : Real.sqrt (-ev i) ^ 2 = -ev i := Real.sq_sqrt (neg_nonneg.mpr hneg.le)
                field_simp [hsq]
                rw [hmul, div_neg, div_self hneg.ne]
              rw [hreal]; simp
          · simp [hij]
  have hreH : (P : Matrix _ _ ℂ)ᴴ = Qᴴ.reindex e e := by
    ext i j; simp [P, Matrix.conjTranspose_apply]
  rw [hreH]
  change (Qᴴ.reindex e e) * (J.reindex e e) * (Q.reindex e e) = Jpq p q
  rw [reindex_mul_self, reindex_mul_self, hQHJQ]
  ext a b
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq]
    rcases a with a | a
    · have ha : e.symm (Sum.inl a) ∈ sPos := by
        have := (ePos.symm a).2
        simp [e, eSum]
      have hpos : 0 < ev (e.symm (Sum.inl a)) := (Finset.mem_filter.mp ha).2
      simp [Jpq, hpos]
    · have ha : e.symm (Sum.inr a) ∈ sNeg := by
        have := (eNeg.symm a).2
        simp [e, eSum]
      have hneg : ev (e.symm (Sum.inr a)) < 0 := (Finset.mem_filter.mp ha).2
      simp [Jpq, not_lt.2 hneg.le]
  · have hne : e.symm a ≠ e.symm b := fun h => hab (e.symm.injective h)
    rw [Matrix.diagonal_apply_ne _ hne]
    rcases a with a | a <;> rcases b with b | b <;> simp [Jpq, Matrix.one_apply] <;>
      intro h <;> exact hab (by subst h; rfl)

/-- **Definite Hermitian Space `DefiniteHermSpace E F V`** over a CM field pair `(F, E)`:
at every archimedean embedding `τ : E →+* ℂ`, the Hermitian form is either positive-definite
`(dim, 0)` or negative-definite `(0, dim)`. -/
structure DefiniteHermSpace (E F V : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  toHerm : HermSpaceCM E F V
  definite : ∀ τ : E →+* ℂ,
    HasSignature (toHerm.gram.map τ) toHerm.dim 0 ∨
      HasSignature (toHerm.gram.map τ) 0 toHerm.dim

/-- Predicate asserting that a CM Hermitian space is **positive-definite** at every
archimedean place (`HasSignature (gram.map τ) dim 0`, equivalently `(gram.map τ).PosDef`). -/
def HermSpaceCM.IsPosDef {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) : Prop :=
  ∀ τ : E →+* ℂ, (H.gram.map τ).PosDef

/-- Constructor from a positive-definite CM Hermitian space. -/
def DefiniteHermSpace.ofPosDef {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) (hpos : H.IsPosDef) : DefiniteHermSpace E F V where
  toHerm := H
  definite := fun τ => Or.inl (by simpa using (hasSignature_posDef_iff (H.gram.map τ)).2 (hpos τ))

/-- **Indefinite Hermitian Space `IndefiniteHermSpace E F V`** with explicit signature
`(p τ, q τ)` at every complex embedding `τ : E →+* ℂ` and at least one indefinite place
`0 < p τ ∧ 0 < q τ`. -/
structure IndefiniteHermSpace (E F V : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  toHerm : HermSpaceCM E F V
  p : (E →+* ℂ) → ℕ
  q : (E →+* ℂ) → ℕ
  sig_ok : ∀ τ : E →+* ℂ, HasSignature (toHerm.gram.map τ) (p τ) (q τ)
  indefinite_witness : ∃ τ : E →+* ℂ, 0 < p τ ∧ 0 < q τ

theorem IndefiniteHermSpace.p_add_q {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : IndefiniteHermSpace E F V) (τ : E →+* ℂ) :
    H.p τ + H.q τ = H.toHerm.dim := by
  simpa using hasSignature_card (H.sig_ok τ)

/-- The doubled space `H.doubled = V ⊕ (-V)` of any positive-definite space of dimension `≥ 1`
is an `IndefiniteHermSpace` of signature `(dim, dim)`. -/
def IndefiniteHermSpace.ofDoubledPosDef {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) (hpos : H.IsPosDef) (hdim : 0 < H.dim) :
    IndefiniteHermSpace E F (V × V) where
  toHerm := H.doubled
  p := fun _ => H.dim
  q := fun _ => H.dim
  sig_ok := fun τ => by
    have h1 : HasSignature (H.gram.map τ) H.dim 0 := by
      simpa using (hasSignature_posDef_iff (H.gram.map τ)).2 (hpos τ)
    have h2 : HasSignature ((-H.gram).map τ) 0 H.dim := by
      have hneg : (-H.gram).map τ = -(H.gram.map τ) := by
        ext i j; simp [Matrix.map_apply]
      rw [hneg]
      exact hasSignature_neg h1
    have hds := hasSignature_directSum h1 h2
    obtain ⟨e, P, hP⟩ := hds
    let s2 : Fin (H.dim + 0) ⊕ Fin (0 + H.dim) ≃ Fin H.dim ⊕ Fin H.dim :=
      Equiv.sumCongr (finCongr (Nat.add_zero H.dim)) (finCongr (Nat.zero_add H.dim))
    let e0 : Fin H.doubled.dim ≃ Fin (H.dim + H.dim) := finCongr rfl
    let e'' : Fin H.doubled.dim ≃ Fin H.dim ⊕ Fin H.dim :=
      e0.trans (finSumFinEquiv.symm.trans (e.trans s2))
    have hre : ∀ a b : Fin (H.dim + H.dim),
        (H.doubled.gram.map τ) (e0.symm a) (e0.symm b) =
          (Matrix.fromBlocks (H.gram.map τ) 0 0 ((-H.gram).map τ))
            (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
      intro a b
      simp only [Matrix.map_apply]
      have hdg : H.doubled.gram (e0.symm a) (e0.symm b) =
          (Matrix.fromBlocks H.gram 0 0 (-H.gram))
            (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
        change (H.directSum H.neg).gram a b = _
        rw [H.directSum_gram H.neg]
        simp only [Matrix.reindex_apply, HermSpaceCM.neg_gram]
        rfl
      rw [hdg]
      rcases finSumFinEquiv.symm a with x | x <;>
        rcases finSumFinEquiv.symm b with y | y <;>
        simp
    let P' : GL (Fin H.dim ⊕ Fin H.dim) ℂ :=
      ⟨(P : Matrix _ _ ℂ).reindex s2 s2, ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).reindex s2 s2,
        by rw [reindex_mul_self, Units.mul_inv, reindex_one_self],
        by rw [reindex_mul_self, Units.inv_mul, reindex_one_self]⟩
    refine ⟨e'', P', ?_⟩
    have hre'' : (H.doubled.gram.map τ).reindex e'' e'' =
        ((Matrix.fromBlocks (H.gram.map τ) 0 0 ((-H.gram).map τ)).reindex e e).reindex s2 s2 := by
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      have hi : e''.symm i = e0.symm (finSumFinEquiv (e.symm (s2.symm i))) := rfl
      have hj : e''.symm j = e0.symm (finSumFinEquiv (e.symm (s2.symm j))) := rfl
      rw [hi, hj, hre, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hP'H : (P' : Matrix _ _ ℂ)ᴴ = ((P : Matrix _ _ ℂ)ᴴ).reindex s2 s2 := by
      ext i j; simp [P', Matrix.conjTranspose_apply]
    rw [hre'', hP'H]
    change (((P : Matrix _ _ ℂ)ᴴ).reindex s2 s2) *
        (((Matrix.fromBlocks (H.gram.map τ) 0 0 ((-H.gram).map τ)).reindex e e).reindex s2 s2) *
        ((P : Matrix _ _ ℂ).reindex s2 s2) = Jpq H.dim H.dim
    rw [reindex_mul_self, reindex_mul_self, hP]
    ext i j
    cases i <;> cases j <;> simp [Jpq, s2, Matrix.one_apply]
  indefinite_witness := by
    letI : Algebra ℚ E := RingHom.toAlgebra (algebraMap ℚ E)
    haveI : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    exact ⟨τ, hdim, hdim⟩

/-! ### Total Definiteness & Cauchy–Schwarz Bound for Definite Unitary Matrices -/

/-- Definiteness at a real embedding `ι : F →+* ℝ`: the Hermitian quadratic form `x ↦ hform σ J x x`
is either strictly positive on `E^n \ {0}` or strictly negative on `E^n \ {0}`. -/
def IsDefiniteAt {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : Type*} [Fintype n] (σ : E →ₐ[F] E) (J : Matrix n n E) (ι : F →+* ℝ) : Prop :=
  (∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hermFormMatrix (σ : E →+* E) J x x ∧ 0 < ι a) ∨
  (∀ x : n → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hermFormMatrix (σ : E →+* E) J x x ∧ ι a < 0)

/-- Total definiteness of `(σ, J)`: `F` is totally real and `(σ, J)` is definite at all `ι : F →+* ℝ`. -/
def IsTotDef {F E : Type*} [Field F] [NumberField F] [Field E] [Algebra F E]
    {n : Type*} [Fintype n] (σ : E →ₐ[F] E) (J : Matrix n n E) : Prop :=
  NumberField.IsTotallyReal F ∧ ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι

/-- Every `DefiniteHermSpace` induces a totally definite Hermitian Gram matrix `H.toHerm.gram`. -/
theorem DefiniteHermSpace.isTotDef {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : DefiniteHermSpace E F V) :
    IsTotDef H.toHerm.cm.conjAlgHom H.toHerm.gram := by
  refine ⟨H.toHerm.cm.totallyReal, fun ι => ?_⟩
  obtain ⟨τ, hτ⟩ := H.toHerm.cm.exists_embedding_with_realPlace ι
  have hfix : ∀ x : Fin H.toHerm.dim → E,
      star (hermFormMatrix H.toHerm.cm.conjRingHom H.toHerm.gram x x) =
        hermFormMatrix H.toHerm.cm.conjRingHom H.toHerm.gram x x := by
    intro x
    unfold hermFormMatrix
    simp_rw [star_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hJ : star (H.toHerm.gram j i) = H.toHerm.gram i j :=
      congrFun (congrFun H.toHerm.gram_isHerm i) j
    simp only [star_mul', star_star, CMFieldPair.conjRingHom_apply, hJ]
    ring
  have hval : ∀ x : Fin H.toHerm.dim → E,
      ∃ a : F, algebraMap F E a = hermFormMatrix H.toHerm.cm.conjRingHom H.toHerm.gram x x ∧
        ((ι a : ℝ) : ℂ) =
          star (fun i => τ (x i)) ⬝ᵥ
            ((H.toHerm.gram.map τ) *ᵥ (fun i => τ (x i))) := by
    intro x
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp ((H.toHerm.cm.star_fixed_iff _).1 (hfix x))
    refine ⟨a, ha, ?_⟩
    rw [← hτ, ← H.toHerm.cm.embedding_base_eq_ofReal τ a, ha]
    rw [hermFormMatrix_map H.toHerm.cm.conjRingHom (starRingEnd ℂ) τ
      (H.toHerm.cm.star_embedding_eq_comp τ)]
    simp only [hermFormMatrix, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp [mul_assoc]
  have hyne : ∀ x : Fin H.toHerm.dim → E, x ≠ 0 → (fun i => τ (x i)) ≠ 0 := by
    intro x hx hy
    apply hx
    funext i
    exact (map_eq_zero τ).mp (congrFun hy i)
  rcases H.definite τ with hpos | hneg
  · left
    intro x hx
    obtain ⟨a, ha, hι⟩ := hval x
    refine ⟨a, ha, ?_⟩
    have hPosDef : (H.toHerm.gram.map τ).PosDef :=
      (hasSignature_posDef_iff _).1 (by simpa using hpos)
    let y : Fin H.toHerm.dim →₀ ℂ := Finsupp.equivFunOnFinite.symm (fun i => τ (x i))
    have hy0 : y ≠ 0 := by
      intro h0
      apply hyne x hx
      ext i
      exact congrArg (fun f : Fin H.toHerm.dim →₀ ℂ => f i) h0
    have hypos := hPosDef.2 hy0
    have hyeq : (y.sum fun i yi => y.sum fun j yj => star yi * (H.toHerm.gram.map τ) i j * yj) =
        star (fun i => τ (x i)) ⬝ᵥ ((H.toHerm.gram.map τ) *ᵥ (fun i => τ (x i))) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      have hR : ∀ i, (y.sum fun j yj => star (y i) * (H.toHerm.gram.map τ) i j * yj) =
          ∑ j, star (τ (x i)) * (H.toHerm.gram.map τ) i j * τ (x j) := fun i =>
        Finsupp.sum_fintype _ _ (fun _ => by simp)
      simp_rw [hR]
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hyeq, ← hι, Complex.lt_def] at hypos
    simpa using hypos.1
  · right
    intro x hx
    obtain ⟨a, ha, hι⟩ := hval x
    refine ⟨a, ha, ?_⟩
    have hNegDef : (-(H.toHerm.gram.map τ)).PosDef :=
      (hasSignature_negDef_iff _).1 (by simpa using hneg)
    let y : Fin H.toHerm.dim →₀ ℂ := Finsupp.equivFunOnFinite.symm (fun i => τ (x i))
    have hy0 : y ≠ 0 := by
      intro h0
      apply hyne x hx
      ext i
      exact congrArg (fun f : Fin H.toHerm.dim →₀ ℂ => f i) h0
    have hypos := hNegDef.2 hy0
    have hyeq : (y.sum fun i yi => y.sum fun j yj => star yi * (-(H.toHerm.gram.map τ)) i j * yj) =
        -(star (fun i => τ (x i)) ⬝ᵥ ((H.toHerm.gram.map τ) *ᵥ (fun i => τ (x i)))) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
      have hR : ∀ i, (y.sum fun j yj => star (y i) * (-(H.toHerm.gram.map τ)) i j * yj) =
          ∑ j, -(star (τ (x i)) * (H.toHerm.gram.map τ) i j * τ (x j)) := fun i => by
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
        refine Finset.sum_congr rfl fun j _ => by simp [y]
      simp_rw [hR]
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Finset.sum_neg_distrib]
    rw [hyeq, ← hι, ← Complex.ofReal_neg, Complex.lt_def] at hypos
    simp only [Complex.zero_re, Complex.ofReal_re] at hypos
    linarith [hypos.1]

private lemma hermFormMatrix_complex_expand {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (a b : ℂ) (u v : n → ℂ) :
    hermFormMatrix (starRingEnd ℂ) A (a • v + b • u) (a • v + b • u) =
      star a * a * hermFormMatrix (starRingEnd ℂ) A v v +
        star a * b * hermFormMatrix (starRingEnd ℂ) A v u +
        star b * a * hermFormMatrix (starRingEnd ℂ) A u v +
        star b * b * hermFormMatrix (starRingEnd ℂ) A u u := by
  unfold hermFormMatrix
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    map_add, map_mul, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermFormMatrix_complex_conj {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (hA : ∀ i j, star (A j i) = A i j) (u v : n → ℂ) :
    star (hermFormMatrix (starRingEnd ℂ) A u v) = hermFormMatrix (starRingEnd ℂ) A v u := by
  unfold hermFormMatrix
  simp_rw [star_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [star_mul', starRingEnd_apply, star_star, hA]
  ring

private lemma hermFormMatrix_complex_cs {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (hA : ∀ i j, star (A j i) = A i j) (u v : n → ℂ) :
    hermFormMatrix (starRingEnd ℂ) A
        (hermFormMatrix (starRingEnd ℂ) A u u • v + (-hermFormMatrix (starRingEnd ℂ) A u v) • u)
        (hermFormMatrix (starRingEnd ℂ) A u u • v + (-hermFormMatrix (starRingEnd ℂ) A u v) • u) =
      hermFormMatrix (starRingEnd ℂ) A u u *
        (hermFormMatrix (starRingEnd ℂ) A u u * hermFormMatrix (starRingEnd ℂ) A v v -
          star (hermFormMatrix (starRingEnd ℂ) A u v) * hermFormMatrix (starRingEnd ℂ) A u v) := by
  rw [hermFormMatrix_complex_expand]
  have h1 : star (hermFormMatrix (starRingEnd ℂ) A u u) = hermFormMatrix (starRingEnd ℂ) A u u :=
    hermFormMatrix_complex_conj A hA u u
  have h2 : hermFormMatrix (starRingEnd ℂ) A v u = star (hermFormMatrix (starRingEnd ℂ) A u v) :=
    (hermFormMatrix_complex_conj A hA u v).symm
  rw [h2, star_neg, h1]
  ring

private lemma definite_sign_at {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : Type*} [Fintype n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) :
    ∃ s : ℝ, 0 < s * s ∧ ∀ x : n → E, ∃ t : ℝ,
      τ (hermFormMatrix (σ : E →+* E) J x x) = (t : ℂ) ∧
        (x ≠ 0 → 0 < s * t) ∧ 0 ≤ s * t := by
  classical
  have hreal : ∀ a : F, star (τ (algebraMap F E a)) = τ (algebraMap F E a) := by
    intro a
    have h1 : τ ((σ : E →+* E) (algebraMap F E a)) = star (τ (algebraMap F E a)) :=
      RingHom.congr_fun hτ (algebraMap F E a)
    have h2 : (σ : E →+* E) (algebraMap F E a) = algebraMap F E a := σ.commutes a
    rw [h2] at h1
    exact h1.symm
  have him : ∀ a : F, (τ (algebraMap F E a)).im = 0 := fun a =>
    Complex.conj_eq_iff_im.1 (hreal a)
  let ι : F →+* ℝ :=
    { toFun := fun a => (τ (algebraMap F E a)).re
      map_one' := by simp
      map_mul' := fun a b => by simp [map_mul, Complex.mul_re, him a, him b]
      map_zero' := by simp
      map_add' := fun a b => by simp [map_add] }
  have hval : ∀ a : F, τ (algebraMap F E a) = ((ι a : ℝ) : ℂ) := fun a =>
    (Complex.conj_eq_iff_re.1 (hreal a)).symm
  have h00 : τ (hermFormMatrix (σ : E →+* E) J 0 0) = ((0 : ℝ) : ℂ) := by
    unfold hermFormMatrix; simp
  rcases hdef ι with hpos | hneg
  · refine ⟨1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx; exact h00
    · obtain ⟨a, ha, hpa⟩ := hpos x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]; exact hval a
  · refine ⟨-1, by norm_num, fun x => ?_⟩
    by_cases hx : x = 0
    · refine ⟨0, ?_, fun h => absurd hx h, by norm_num⟩
      subst hx; exact h00
    · obtain ⟨a, ha, hpa⟩ := hneg x hx
      refine ⟨ι a, ?_, fun _ => by linarith, by linarith⟩
      rw [← ha]; exact hval a

/-- **Cauchy–Schwarz Matrix Entry Bound (`definite_cauchy_schwarz_entry_bound`)**:
for any definite Hermitian matrix `J` over `E` and any `g ∈ U(J)(E)`, every archimedean
embedding satisfies `‖τ ((J * g) i j)‖ ≤ ‖τ (J i i)‖ + ‖τ (J j j)‖`. -/
theorem definite_cauchy_schwarz_entry_bound {F E : Type*} [Field F] [Field E] [Algebra F E]
    {n : Type*} [Fintype n] [DecidableEq n]
    (σ : E →ₐ[F] E) (J : Matrix n n E) (τ : E →+* ℂ)
    (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHermMatrix (σ : E →+* E) J)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι)
    (g : Matrix n n E) (hg : conjTransposeMap (σ : E →+* E) g * J * g = J) (i j : n) :
    ‖τ ((J * g) i j)‖ ≤ ‖τ (J i i)‖ + ‖τ (J j j)‖ := by
  classical
  obtain ⟨s, -, hsign⟩ := definite_sign_at σ J τ hτ hdef
  have hA : ∀ a b, star ((J.map τ) b a) = (J.map τ) a b := by
    intro a b
    have h3 : τ ((σ : E →+* E) (J b a)) = star (τ (J b a)) := RingHom.congr_fun hτ _
    have h4 : (σ : E →+* E) (J b a) = J a b := congrFun (congrFun hH a) b
    simp only [Matrix.map_apply]
    rw [← h3, h4]
  have hc : (J * g) i j = hermFormMatrix (σ : E →+* E) J (Pi.single i 1) (fun k => g k j) := by
    rw [hermFormMatrix_single_left]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hb : hermFormMatrix (σ : E →+* E) J (fun k => g k j) (fun k => g k j) = J j j := by
    rw [← hermFormMatrix_gram, hg]
  have ha : hermFormMatrix (σ : E →+* E) J (Pi.single i 1) (Pi.single i 1) = J i i := by
    rw [hermFormMatrix_single_left]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hau : τ (J i i) = hermFormMatrix (starRingEnd ℂ) (J.map τ)
      (fun k => τ ((Pi.single i 1 : n → E) k)) (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    rw [← hermFormMatrix_map _ _ τ hτ, ha]
  have hcu : τ ((J * g) i j) = hermFormMatrix (starRingEnd ℂ) (J.map τ)
      (fun k => τ ((Pi.single i 1 : n → E) k)) (fun k => τ (g k j)) := by
    rw [← hermFormMatrix_map _ _ τ hτ, hc]
  have hbv : τ (J j j) = hermFormMatrix (starRingEnd ℂ) (J.map τ)
      (fun k => τ (g k j)) (fun k => τ (g k j)) := by
    rw [← hermFormMatrix_map _ _ τ hτ, hb]
  obtain ⟨tw, htw, -, htw0⟩ := hsign
    ((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E))
  obtain ⟨ta, hta, hta1, -⟩ := hsign (Pi.single i 1 : n → E)
  obtain ⟨tb, htb, -, htb0⟩ := hsign (fun k => g k j)
  have hei : (Pi.single i 1 : n → E) ≠ 0 := by
    intro h
    have h5 := congrFun h i
    simp at h5
  have hta' := hta1 hei
  rw [ha] at hta
  rw [hb] at htb
  rw [hermFormMatrix_map _ _ τ hτ] at htw
  have hw : (fun k => τ (((J i i) • (fun k => g k j) + (-((J * g) i j)) • (Pi.single i 1 : n → E)) k)) =
      τ (J i i) • (fun k => τ (g k j)) + (-τ ((J * g) i j)) • (fun k => τ ((Pi.single i 1 : n → E) k)) := by
    funext k
    simp [map_add, map_mul, map_neg]
  rw [hw, hau, hcu, hermFormMatrix_complex_cs _ hA, ← hau, ← hcu, ← hbv, hta, htb] at htw
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, ← Complex.ofReal_mul] at htw
  have key : ta * (ta * tb - ‖τ ((J * g) i j)‖ ^ 2) = tw := Complex.ofReal_injective htw
  have h1 : ‖τ ((J * g) i j)‖ ^ 2 ≤ ta * tb := by
    by_contra hneg
    push Not at hneg
    have h6 : s * tw < 0 := by
      rw [← key]
      nlinarith
    linarith
  have h3 : ta * tb ≤ |ta| * |tb| := by
    rw [← abs_mul]; exact le_abs_self _
  rw [hta, htb, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [abs_nonneg ta, abs_nonneg tb, norm_nonneg (τ ((J * g) i j))]

end SignatureAndDefiniteness

/-! ## Section 5: Adelic Unitary Groups `UnitaryAdelicGrp`, Compactness at `∞` & `CompactOpenLevel` -/

section AdelicUnitaryGroups

section LocalAndArchimedean

variable {E F V : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Local unitary group `U(V)(F_v)` at a finite place `v : HeightOneSpectrum (𝓞 F)`. -/
def UnitaryLocalGrp (H : HermSpaceCM E F V) (v : HeightOneSpectrum (𝓞 F)) :
    Type _ :=
  UnitaryPts H.cm.conjAlgHom H.gram (v.adicCompletion F)

instance (H : HermSpaceCM E F V) (v : HeightOneSpectrum (𝓞 F)) :
    Group (UnitaryLocalGrp H v) :=
  inferInstanceAs (Group (UnitaryPts H.cm.conjAlgHom H.gram (v.adicCompletion F)))

/-- Archimedean real completion `F_ι` equipped with its canonical `F`-algebra structure via `ι : F →+* ℝ`. -/
def ArchReal (F : Type*) [Field F] (_ι : F →+* ℝ) : Type := ℝ

instance (F : Type*) [Field F] (ι : F →+* ℝ) : Field (ArchReal F ι) := inferInstanceAs (Field ℝ)
instance (F : Type*) [Field F] (ι : F →+* ℝ) : CommRing (ArchReal F ι) := inferInstanceAs (CommRing ℝ)
instance (F : Type*) [Field F] (ι : F →+* ℝ) : Nontrivial (ArchReal F ι) := inferInstanceAs (Nontrivial ℝ)
instance (F : Type*) [Field F] (ι : F →+* ℝ) : Algebra F (ArchReal F ι) := ι.toAlgebra

/-- Local archimedean unitary group `U(V)(F_ι)` at a real embedding `ι : F →+* ℝ`. -/
def UnitaryArchGrp (H : HermSpaceCM E F V) (ι : F →+* ℝ) : Type _ :=
  UnitaryPts H.cm.conjAlgHom H.gram (ArchReal F ι)

instance (H : HermSpaceCM E F V) (ι : F →+* ℝ) : Group (UnitaryArchGrp H ι) :=
  inferInstanceAs (Group (UnitaryPts H.cm.conjAlgHom H.gram (ArchReal F ι)))

instance instNontrivialFiniteAdeleRing (F : Type*) [Field F] [NumberField F] :
    Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have h2 : ¬ IsUnit (2 : 𝓞 F) := by
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hyF : (2 : F) * (y : F) = 1 := by
      simpa [map_ofNat] using congrArg (algebraMap (𝓞 F) F) hy
    have hyhalf : (y : F) = algebraMap ℚ F (1 / 2 : ℚ) := by
      have : (algebraMap ℚ F (2 : ℚ)) * (y : F) = 1 := by simpa using hyF
      calc (y : F) = (algebraMap ℚ F (2 : ℚ))⁻¹ * 1 := by
            rw [← this, ← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
        _ = algebraMap ℚ F (1 / 2 : ℚ) := by simp [one_div]
    have hint : IsIntegral ℤ (1 / 2 : ℚ) := by
      rw [← isIntegral_algebraMap_iff (algebraMap ℚ F).injective, ← hyhalf]
      exact RingOfIntegers.isIntegral_coe y
    have hq : (1 / 2 : ℚ) ∈ (algebraMap ℤ ℚ).range :=
      IsIntegrallyClosed.isIntegral_iff.mp hint
    obtain ⟨n, hn⟩ := hq
    have h2n : (2 : ℚ) * (n : ℚ) = 1 := by
      simpa using congrArg (fun z : ℚ => (2 : ℚ) * z) hn
    have : (2 * n : ℤ) = 1 := by exact_mod_cast h2n
    omega
  have hne_top : Ideal.span ({(2 : 𝓞 F)} : Set (𝓞 F)) ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton] at htop
    exact h2 (isUnit_of_dvd_one htop)
  obtain ⟨m, hm_max, hm_le⟩ := Ideal.exists_le_maximal _ hne_top
  have hm0 : m ≠ ⊥ := by
    intro hbot
    rw [hbot] at hm_le
    have h0 : (2 : 𝓞 F) = 0 := by
      simpa using hm_le (Ideal.subset_span (Set.mem_singleton (2 : 𝓞 F)))
    have h0F : (2 : F) = 0 := by simpa using congrArg (algebraMap (𝓞 F) F) h0
    norm_num at h0F
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm_max.isPrime, hm0⟩
  have hv : (1 : v.adicCompletion F) = (0 : v.adicCompletion F) :=
    congrArg (fun a : FiniteAdeleRing (𝓞 F) F => a v) h
  exact one_ne_zero hv

/-- Finite-adelic unitary group `U(V)(𝔸_{F,f})`. -/
def UnitaryFiniteAdelicGrp (H : HermSpaceCM E F V) : Type _ :=
  UnitaryPts H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)

instance (H : HermSpaceCM E F V) : Group (UnitaryFiniteAdelicGrp H) :=
  inferInstanceAs (Group (UnitaryPts H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)))

/-- Full adelic unitary group `U(V)(𝔸_F) = (∏_{ι : F →+* ℝ} U(V)(F_ι)) × U(V)(𝔸_{F,f})`. -/
def UnitaryAdelicGrp (H : HermSpaceCM E F V) : Type _ :=
  (Π ι : (F →+* ℝ), UnitaryArchGrp H ι) × UnitaryFiniteAdelicGrp H

instance (H : HermSpaceCM E F V) : Group (UnitaryAdelicGrp H) :=
  inferInstanceAs (Group ((Π ι : (F →+* ℝ), UnitaryArchGrp H ι) × UnitaryFiniteAdelicGrp H))

/-- Projection from `UnitaryAdelicGrp H` to its finite-adelic component `U(V)(𝔸_{F,f})`. -/
def UnitaryAdelicGrp.finProj (H : HermSpaceCM E F V) :
    UnitaryAdelicGrp H →* UnitaryFiniteAdelicGrp H :=
  MonoidHom.snd _ _

/-- Projection from `UnitaryAdelicGrp H` to its archimedean component at `ι : F →+* ℝ`. -/
def UnitaryAdelicGrp.archAt (H : HermSpaceCM E F V) (ι : F →+* ℝ) :
    UnitaryAdelicGrp H →* UnitaryArchGrp H ι :=
  (Pi.evalMonoidHom (fun j => UnitaryArchGrp H j) ι).comp (MonoidHom.fst _ _)

/-- Rational embedding `U(V)(E) →* U(V)(𝔸_{F,f})` into the finite-adelic unitary group. -/
def HermSpaceCM.ratToFiniteAdelic (H : HermSpaceCM E F V) :
    UnitaryGrp H →* UnitaryFiniteAdelicGrp H :=
  (ratPtsHom H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)).comp
    (unitaryGrpEquivMat H).toMonoidHom

theorem HermSpaceCM.ratToFiniteAdelic_injective (H : HermSpaceCM E F V) :
    Function.Injective H.ratToFiniteAdelic :=
  (ratPtsHom_injective H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)).comp
    (unitaryGrpEquivMat H).injective

/-- Rational embedding `U(V)(E) →* U(V)(F_ι)` at an archimedean place `ι : F →+* ℝ`. -/
def HermSpaceCM.ratToArch (H : HermSpaceCM E F V) (ι : F →+* ℝ) :
    UnitaryGrp H →* UnitaryArchGrp H ι :=
  (ratPtsHom H.cm.conjAlgHom H.gram (ArchReal F ι)).comp (unitaryGrpEquivMat H).toMonoidHom

/-- Diagonal rational embedding `U(V)(E) →* U(V)(𝔸_F)` into the full adelic unitary group. -/
def HermSpaceCM.ratToAdelic (H : HermSpaceCM E F V) :
    UnitaryGrp H →* UnitaryAdelicGrp H :=
  MonoidHom.prod (MonoidHom.pi fun ι => H.ratToArch ι) H.ratToFiniteAdelic

theorem HermSpaceCM.ratToAdelic_injective (H : HermSpaceCM E F V) :
    Function.Injective H.ratToAdelic := by
  intro g₁ g₂ h
  exact H.ratToFiniteAdelic_injective (congrArg Prod.snd h)

/-- Compactness of the complex unitary group `{ g : GL_n(ℂ) | gᴴ * J * g = J }` when `J.PosDef`. -/
theorem isCompact_complexUnitary_of_posDef {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hJ : J.PosDef) :
    IsCompact { g : Matrix n n ℂ | gᴴ * J * g = J } := by
  let U : Matrix n n ℂ := hJ.isHermitian.eigenvectorUnitary
  let Dsqrt : Matrix n n ℂ := Matrix.diagonal fun i =>
    ((Real.sqrt (hJ.isHermitian.eigenvalues i) : ℝ) : ℂ)
  let Dinv : Matrix n n ℂ := Matrix.diagonal fun i =>
    (((Real.sqrt (hJ.isHermitian.eigenvalues i))⁻¹ : ℝ) : ℂ)
  let P : Matrix n n ℂ := U * Dsqrt * star U
  let Pinv : Matrix n n ℂ := U * Dinv * star U
  have hDD : Dsqrt * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hpos : 0 < Real.sqrt (hJ.isHermitian.eigenvalues i) :=
        Real.sqrt_pos.mpr (hJ.eigenvalues_pos i)
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      rw [Complex.ofReal_inv]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne')
    · simp [hij]
  have hPPinv : P * Pinv = 1 := by
    calc (U * Dsqrt * star U) * (U * Dinv * star U)
        = U * Dsqrt * (star U * U) * Dinv * star U := by simp only [Matrix.mul_assoc]
      _ = U * (Dsqrt * Dinv) * star U := by
          rw [hJ.isHermitian.eigenvectorUnitary.2.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * star U := by rw [hDD, Matrix.mul_one]
      _ = 1 := hJ.isHermitian.eigenvectorUnitary.2.2
  have hPinvP : Pinv * P = 1 := by
    calc (U * Dinv * star U) * (U * Dsqrt * star U)
        = U * Dinv * (star U * U) * Dsqrt * star U := by simp only [Matrix.mul_assoc]
      _ = U * (Dinv * Dsqrt) * star U := by
          rw [hJ.isHermitian.eigenvectorUnitary.2.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * star U := by
          have hDD' : Dinv * Dsqrt = 1 := by
            rw [Matrix.diagonal_mul_diagonal]
            ext i j
            by_cases hij : i = j
            · subst hij
              have hpos : 0 < Real.sqrt (hJ.isHermitian.eigenvalues i) :=
                Real.sqrt_pos.mpr (hJ.eigenvalues_pos i)
              rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
              rw [Complex.ofReal_inv]
              exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne')
            · simp [hij]
          rw [hDD', Matrix.mul_one]
      _ = 1 := hJ.isHermitian.eigenvectorUnitary.2.2
  have hPH : Pᴴ = P := by
    have hDsqrtH : Dsqrtᴴ = Dsqrt := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1; funext i; simp
    simp only [P, Matrix.conjTranspose_mul, hDsqrtH]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hPJ : Pᴴ * P = J := by
    rw [hPH]
    calc (U * Dsqrt * star U) * (U * Dsqrt * star U)
        = U * Dsqrt * (star U * U) * Dsqrt * star U := by simp only [Matrix.mul_assoc]
      _ = U * (Dsqrt * Dsqrt) * star U := by
          rw [hJ.isHermitian.eigenvectorUnitary.2.1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (RCLike.ofReal ∘ hJ.isHermitian.eigenvalues) * star U := by
          congr 2
          rw [Matrix.diagonal_mul_diagonal]
          congr 1; funext i
          have hpos := (hJ.eigenvalues_pos i).le
          change ((Real.sqrt (hJ.isHermitian.eigenvalues i) : ℝ) : ℂ) *
            ((Real.sqrt (hJ.isHermitian.eigenvalues i) : ℝ) : ℂ) =
            ((hJ.isHermitian.eigenvalues i : ℝ) : ℂ)
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]
      _ = J := by
          simpa [U, Matrix.mul_assoc, Unitary.conjStarAlgAut_apply] using
            hJ.isHermitian.spectral_theorem.symm
  have hPinvH : Pinvᴴ = Pinv := by
    have hDinvH : Dinvᴴ = Dinv := by
      rw [Matrix.diagonal_conjTranspose]
      congr 1; funext i; simp
    simp only [Pinv, Matrix.conjTranspose_mul, hDinvH]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hPP : P * P = J := by simpa [hPH] using hPJ
  have himg : { g : Matrix n n ℂ | gᴴ * J * g = J } =
      (fun u : Matrix n n ℂ => Pinv * u * P) '' (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
    ext g
    constructor
    · intro hg
      refine ⟨P * g * Pinv, ?_, ?_⟩
      · rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff']
        have h1 : (P * g * Pinv)ᴴ = Pinv * gᴴ * P := by
          simp only [Matrix.conjTranspose_mul, hPH, hPinvH, Matrix.mul_assoc]
        calc (P * g * Pinv)ᴴ * (P * g * Pinv)
            = Pinv * gᴴ * (P * P) * g * Pinv := by rw [h1]; simp only [Matrix.mul_assoc]
          _ = Pinv * (gᴴ * J * g) * Pinv := by
              rw [hPP]; simp only [Matrix.mul_assoc]
          _ = Pinv * J * Pinv := by rw [hg]
          _ = Pinv * (P * P) * Pinv := by rw [hPP]
          _ = (Pinv * P) * (P * Pinv) := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hPinvP, hPPinv, Matrix.mul_one]
      · calc Pinv * (P * g * Pinv) * P
            = (Pinv * P) * g * (Pinv * P) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [hPinvP, Matrix.one_mul, Matrix.mul_one]
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff'] at hu
      have h1 : (Pinv * u * P)ᴴ = P * uᴴ * Pinv := by
        simp only [Matrix.conjTranspose_mul, hPH, hPinvH, Matrix.mul_assoc]
      calc (Pinv * u * P)ᴴ * J * (Pinv * u * P)
          = P * uᴴ * Pinv * (P * P) * Pinv * u * P := by
            rw [h1, hPP]; simp only [Matrix.mul_assoc]
        _ = P * (uᴴ * u) * P := by
            have hmid1 : Pinv * (P * P) * Pinv = 1 := by
              calc Pinv * (P * P) * Pinv = (Pinv * P) * (P * Pinv) := by simp only [Matrix.mul_assoc]
                _ = 1 := by rw [hPinvP, hPPinv, Matrix.mul_one]
            calc P * uᴴ * Pinv * (P * P) * Pinv * u * P
                = P * uᴴ * (Pinv * (P * P) * Pinv) * u * P := by simp only [Matrix.mul_assoc]
              _ = P * (uᴴ * u) * P := by rw [hmid1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = J := by
            rw [← Matrix.star_eq_conjTranspose, hu, Matrix.mul_one, hPP]
  rw [himg]
  have hunit_comp : IsCompact (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
    have hsub : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) ⊆
        Set.pi Set.univ (fun _ : n => Set.pi Set.univ (fun _ : n => Metric.closedBall (0 : ℂ) 1)) := by
      intro u hu i _ j _
      rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff'] at hu
      have hdiag : (uᴴ * u) j j = 1 := by
        rw [← Matrix.star_eq_conjTranspose, hu, Matrix.one_apply_eq]
      rw [Matrix.mul_apply] at hdiag
      have hre := congrArg Complex.re hdiag
      simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul',
        ← Complex.ofReal_pow, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.one_re] at hre
      have hle : ‖u i j‖ ^ 2 ≤ 1 := by
        rw [← hre]
        exact Finset.single_le_sum (fun k _ => sq_nonneg ‖u k j‖) (Finset.mem_univ i)
      rw [Metric.mem_closedBall, dist_zero_right]
      nlinarith [norm_nonneg (u i j)]
    have hclosed : IsClosed (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
      have heq : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) =
          { u : Matrix n n ℂ | uᴴ * u = 1 } := by
        ext u; exact Matrix.mem_unitaryGroup_iff'
      rw [heq]
      refine isClosed_eq ?_ continuous_const
      exact Continuous.matrix_mul
        ((continuous_id.matrix_map Complex.continuous_conj).matrix_transpose) continuous_id
    have hbox : IsCompact
        (Set.pi Set.univ (fun _ : n => Set.pi Set.univ (fun _ : n => Metric.closedBall (0 : ℂ) 1))) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    exact hbox.of_isClosed_subset hclosed hsub
  exact hunit_comp.image
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

end LocalAndArchimedean

section IntegralRingsAndLevels

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- Integral finite adeles `∏_v 𝒪_{F,v} ⊆ 𝔸_{F,f}`. -/
def intAd : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := { a | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F }
  mul_mem' := fun ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (v.adicCompletionIntegers F)
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  neg_mem' := fun ha v => neg_mem (ha v)

/-- Subring `𝒪_E ⊆ E` embedded in `E`. -/
def intOE : Subring E := (algebraMap (𝓞 E) E).range

/-- Subring `S₁ ⊗ S₂` generated inside `E ⊗_F R`. -/
def tensInt (R : Type*) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure
    (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
      Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

/-- Adelic integral structure subring `𝒪_{E,f} = 𝒪_E ⊗_{𝒪_F} 𝒪_{F,f} ⊆ E ⊗_F 𝔸_{F,f}`. -/
abbrev adelicIntRing : Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  tensInt F E (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

/-- Canonical embedding of `d : 𝓞 F` as a central scalar `(1 : E) ⊗ d ∈ E ⊗_F 𝔸_{F,f}`. -/
def levelC (d : 𝓞 F) : E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d

variable {F E}

lemma levelC_one : levelC F E 1 = 1 := by
  simp [levelC, Algebra.TensorProduct.one_def]

lemma levelC_mul (a b : 𝓞 F) : levelC F E (a * b) = levelC F E a * levelC F E b := by
  simp [levelC, Algebra.TensorProduct.tmul_mul_tmul]

lemma intAd_mem_of_int (r : 𝓞 F) :
    algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r ∈ intAd F := by
  intro v
  change Valued.v ((r : F) : v.adicCompletion F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one v r

lemma tmul_mem_adelicIntRing (e : 𝓞 E) {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intAd F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] y ∈ adelicIntRing F E := by
  have heq : algebraMap (𝓞 E) E e ⊗ₜ[F] y =
      (algebraMap (𝓞 E) E e ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * ((1 : E) ⊗ₜ[F] y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [heq]
  exact mul_mem
    (Subring.subset_closure (Or.inl ⟨⟨_, ⟨e, rfl⟩⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩))

lemma levelC_mem_adelicIntRing (d : 𝓞 F) : levelC F E d ∈ adelicIntRing F E := by
  simpa [levelC] using tmul_mem_adelicIntRing (1 : 𝓞 E) (intAd_mem_of_int d)

/-- Stabilizer in `GL_n(A)` of an `R`-submodule `Λ ⊆ A^n`. -/
def stabGL {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [Algebra R A] (Λ : Submodule R (n → A)) : Subgroup (GL n A) where
  carrier := { g | ∀ x : n → A, x ∈ Λ ↔ (g : Matrix n n A) *ᵥ x ∈ Λ }
  one_mem' := fun x => by simp
  mul_mem' := fun ha hb x => by
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb x).trans (ha _)
  inv_mem' := fun {g} hg x => by
    have h := hg (((g⁻¹ : GL n A) : Matrix n n A) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h
    exact h.symm

/-- Standard integral `R`-lattice `R^n ⊆ A^n`. -/
def stdLat (n : Type*) [Fintype n] (R : Type*) {A : Type*} [CommRing A] [CommRing R] [Algebra R A] :
    Submodule R (n → A) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap R A)

lemma mem_stdLat_iff {n A : Type*} [Fintype n] [CommRing A] (S : Subring A) (v : n → A) :
    v ∈ stdLat n S ↔ ∀ i : n, v i ∈ S := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨v i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

/-- Lattice-stabilizer level subgroup `level σ J Λ = U(J) ∩ stabGL Λ`. -/
def latticeLevel {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [Algebra R A]
    (σ : A →+* A) (J : Matrix n n A) (Λ : Submodule R (n → A)) : Subgroup (GL n A) :=
  UnitaryMatGrp σ J ⊓ stabGL Λ

section LevelStructures

variable {E F V : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Canonical ring homomorphism `𝓞 F →+* adelicIntRing F E` sending `d ↦ (1 : E) ⊗ d`. -/
def levelCHom (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    𝓞 F →+* adelicIntRing F E where
  toFun d := ⟨levelC F E d, levelC_mem_adelicIntRing d⟩
  map_one' := Subtype.ext levelC_one
  map_mul' a b := Subtype.ext (levelC_mul a b)
  map_zero' := Subtype.ext (by simp [levelC])
  map_add' a b := Subtype.ext (by simp [levelC, map_add, TensorProduct.tmul_add])

/-- Ideal `I · 𝒪_{E,f} ⊆ 𝒪_{E,f}` induced by an ideal `I ≤ 𝓞 F`. -/
def levelIdeal (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (I : Ideal (𝓞 F)) : Ideal (adelicIntRing F E) :=
  I.map (levelCHom F E)

/-- Congruence subgroup of `GL_n(E ⊗_F 𝔸_{F,f})` congruent to `1` modulo `I · 𝒪_{E,f}`. -/
def congruenceSubgroup (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : Type*) [Fintype n] [DecidableEq n] (I : Ideal (𝓞 F)) :
    Subgroup (GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  ((baseChangeGL (n := n) (Ideal.Quotient.mk (levelIdeal F E I))).ker).map
    (baseChangeGL (n := n) (adelicIntRing F E).subtype)

lemma congruenceSubgroup_le_stabGL (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : Type*) [Fintype n] [DecidableEq n] (I : Ideal (𝓞 F)) :
    congruenceSubgroup F E n I ≤ stabGL (stdLat n (adelicIntRing F E)) := by
  rintro g ⟨g₀, -, rfl⟩ x
  have hmul : ∀ (M : Matrix n n (adelicIntRing F E)) (v : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      (∀ i, v i ∈ adelicIntRing F E) →
      ∀ i, (M.map (adelicIntRing F E).subtype *ᵥ v) i ∈ adelicIntRing F E := by
    intro M v hv i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact sum_mem fun j _ => mul_mem (M i j).2 (hv j)
  rw [mem_stdLat_iff, mem_stdLat_iff]
  constructor
  · intro hx
    exact hmul (g₀ : Matrix n n (adelicIntRing F E)) x hx
  · intro hx
    have hx' : x = ((g₀⁻¹ : GL n (adelicIntRing F E)) : Matrix n n (adelicIntRing F E)).map
        (adelicIntRing F E).subtype *ᵥ
        (((baseChangeGL (adelicIntRing F E).subtype g₀ : GL n _) : Matrix n n _) *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, baseChangeGL_apply_matrix, ← Matrix.map_mul,
        Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    rw [hx']
    exact hmul ((g₀⁻¹ : GL n (adelicIntRing F E)) : Matrix n n (adelicIntRing F E)) _ hx

/-- Standard maximal compact open level `K_{f,0} = U(V)(𝔸_{F,f}) ∩ GL_n(𝒪_{E,f})`. -/
def stdMaximalLevel (H : HermSpaceCM E F V) : Subgroup (UnitaryFiniteAdelicGrp H) :=
  (stabGL (stdLat (Fin H.dim) (adelicIntRing F E))).comap
    (UnitaryPts H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)).subtype

/-- Principal congruence subgroup `K_f(I) ≤ U(V)(𝔸_{F,f})` at level `I ≤ 𝓞 F`. -/
def principalCongruenceSubgroup (H : HermSpaceCM E F V) (I : Ideal (𝓞 F)) :
    Subgroup (UnitaryFiniteAdelicGrp H) :=
  (congruenceSubgroup F E (Fin H.dim) I).comap
    (UnitaryPts H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)).subtype

/-- **Compact Open Level Subgroup `CompactOpenLevel H`** of `U(V)(𝔸_{F,f})`:
a subgroup `toSubgroup ≤ U(V)(𝔸_{F,f})` stabilizing an adelic `𝒪_{E,f}`-lattice `lat`
sandwiched between `c₁ · 𝒪_{E,f}^n` and `c₂⁻¹ · 𝒪_{E,f}^n` for nonzero `c₁, c₂ ∈ 𝓞 F`. -/
structure CompactOpenLevel (H : HermSpaceCM E F V) where
  toSubgroup : Subgroup (UnitaryFiniteAdelicGrp H)
  c₁ : 𝓞 F
  c₂ : 𝓞 F
  hc₁ : c₁ ≠ 0
  hc₂ : c₂ ≠ 0
  lat : Submodule (adelicIntRing F E) (Fin H.dim → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
  stabilizes_lat : ∀ g ∈ toSubgroup,
    (g.1 : GL (Fin H.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ stabGL lat
  lower_bound : ∀ v : Fin H.dim → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    (∀ i, v i ∈ adelicIntRing F E) → (fun i => levelC F E c₁ * v i) ∈ lat
  upper_bound : ∀ v ∈ lat, ∀ i : Fin H.dim, levelC F E c₂ * v i ∈ adelicIntRing F E

namespace CompactOpenLevel

/-- Standard maximal compact open level `K_{f,0}` packaged as a `CompactOpenLevel H`. -/
def stdMaximal (H : HermSpaceCM E F V) : CompactOpenLevel H where
  toSubgroup := stdMaximalLevel H
  c₁ := 1
  c₂ := 1
  hc₁ := one_ne_zero
  hc₂ := one_ne_zero
  lat := stdLat (Fin H.dim) (adelicIntRing F E)
  stabilizes_lat := fun _ hg => hg
  lower_bound := fun v hv => by
    rw [mem_stdLat_iff]
    intro i; rw [levelC_one, one_mul]; exact hv i
  upper_bound := fun v hv i => by
    rw [mem_stdLat_iff] at hv
    rw [levelC_one, one_mul]
    exact hv i

/-- Principal congruence subgroup `K_f(I)` packaged as a `CompactOpenLevel H`. -/
def principalCongruence (H : HermSpaceCM E F V) (I : Ideal (𝓞 F)) : CompactOpenLevel H where
  toSubgroup := principalCongruenceSubgroup H I
  c₁ := 1
  c₂ := 1
  hc₁ := one_ne_zero
  hc₂ := one_ne_zero
  lat := stdLat (Fin H.dim) (adelicIntRing F E)
  stabilizes_lat := fun _ hg => congruenceSubgroup_le_stabGL F E (Fin H.dim) I hg
  lower_bound := fun v hv => by
    rw [mem_stdLat_iff]
    intro i; rw [levelC_one, one_mul]; exact hv i
  upper_bound := fun v hv i => by
    rw [mem_stdLat_iff] at hv
    rw [levelC_one, one_mul]
    exact hv i

/-- Any subgroup of a `CompactOpenLevel H` is again a `CompactOpenLevel H`. -/
def ofSubgroup {H : HermSpaceCM E F V} (K : CompactOpenLevel H)
    (K' : Subgroup (UnitaryFiniteAdelicGrp H))
    (hK' : K' ≤ K.toSubgroup) : CompactOpenLevel H where
  toSubgroup := K'
  c₁ := K.c₁
  c₂ := K.c₂
  hc₁ := K.hc₁
  hc₂ := K.hc₂
  lat := K.lat
  stabilizes_lat := fun g hg => K.stabilizes_lat g (hK' hg)
  lower_bound := K.lower_bound
  upper_bound := K.upper_bound

/-- Intersection of two `CompactOpenLevel` subgroups is a `CompactOpenLevel`. -/
def inf {H : HermSpaceCM E F V} (K K' : CompactOpenLevel H) : CompactOpenLevel H :=
  K.ofSubgroup (K.toSubgroup ⊓ K'.toSubgroup) inf_le_left

end CompactOpenLevel

end LevelStructures

end IntegralRingsAndLevels

end AdelicUnitaryGroups

/-! ## Section 6: Denominator Clearing, Trace-Form Pullback & `stabilizer_finite_of_definite` -/

section StabilizerFiniteness

section DenominatorAndTrace

/-- Every finite family of elements in a number field `E` has a nonzero integral common denominator. -/
theorem exists_int_denom_of_numberField {E ι : Type*} [Field E] [NumberField E] [Finite ι]
    (f : ι → E) :
    ∃ d : E, d ≠ 0 ∧ IsIntegral ℤ d ∧ ∀ i, IsIntegral ℤ (d * f i) := by
  classical
  have hZ : ∀ x : ℤ, IsIntegral ℤ (x : E) := fun x => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := x))
  have hQ : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using hQ
  haveI := Fintype.ofFinite ι
  refine ⟨((∏ i, m i : ℤ) : E), ?_, hZ _, ?_⟩
  · exact_mod_cast Finset.prod_ne_zero_iff.2 fun i _ => hm0 i
  · intro i
    rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i)]
    push_cast
    rw [mul_comm ((m i : ℤ) : E), mul_assoc]
    refine IsIntegral.mul ?_ (hmi i)
    exact_mod_cast hZ (∏ j ∈ Finset.univ.erase i, m j)

lemma local_adele_denom {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (v.adicCompletion F) d * x ∈ v.adicCompletionIntegers F := by
  have hs : { y : v.adicCompletion F | Valued.v (y - x) < 1 } ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at ha
  obtain ⟨⟨num, den⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 F)) a
  refine ⟨(den : 𝓞 F), nonZeroDivisors.ne_zero den.2, ?_⟩
  have h1 : algebraMap (𝓞 F) (v.adicCompletion F) num =
      algebraMap F (v.adicCompletion F) a * algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F) num, ← hnd, map_mul,
      ← IsScalarTower.algebraMap_apply]
  have heq : algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * x =
      algebraMap (𝓞 F) (v.adicCompletion F) num -
        algebraMap (𝓞 F) (v.adicCompletion F) (den : 𝓞 F) * (algebraMap F _ a - x) := by
    rw [h1]; ring
  rw [heq]
  refine sub_mem ?_ (mul_mem ?_ ?_)
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap (𝓞 F) F num : F) : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one v num
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap (𝓞 F) F (den : 𝓞 F) : F) : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one v (den : 𝓞 F)
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact ha.le

theorem exists_adele_denom {F : Type*} [Field F] [NumberField F] (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d * a ∈ intAd F := by
  classical
  have hP : { v : HeightOneSpectrum (𝓞 F) | a v ∉ v.adicCompletionIntegers F }.Finite :=
    Filter.eventually_cofinite.1 a.2
  choose d hd0 hd using fun v : HeightOneSpectrum (𝓞 F) => local_adele_denom v (a v)
  refine ⟨∏ v ∈ hP.toFinset, d v, Finset.prod_ne_zero_iff.2 fun v _ => hd0 v, fun w => ?_⟩
  show algebraMap (𝓞 F) (w.adicCompletion F) (∏ v ∈ hP.toFinset, d v) * a w ∈ _
  by_cases hw : w ∈ hP.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, map_mul, mul_comm (algebraMap _ _ (d w)), mul_assoc]
    refine mul_mem ?_ (hd w)
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap (𝓞 F) F _ : F) : w.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one w _
  · have hmem : a w ∈ w.adicCompletionIntegers F := by simpa using hw
    refine mul_mem ?_ hmem
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap (𝓞 F) F _ : F) : w.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one w _

theorem exists_adelicCM_denom {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ levelC F E d * x ∈ adelicIntRing F E := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    have halg : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
    obtain ⟨m, hm0, hm⟩ := (halg.1 e).exists_integral_multiple
    obtain ⟨d, hd0, hd⟩ := exists_adele_denom a
    refine ⟨(m : 𝓞 F) * d, mul_ne_zero (Int.cast_ne_zero.2 hm0) hd0, ?_⟩
    have heq : levelC F E ((m : 𝓞 F) * d) * (e ⊗ₜ a) =
        algebraMap (𝓞 E) E ⟨m • e, hm⟩ ⊗ₜ[F] (algebraMap (𝓞 F) _ d * a) := by
      simp only [levelC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, map_intCast]
      rw [show algebraMap (𝓞 E) E ⟨m • e, hm⟩ = m • e from rfl, TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_assoc]
    rw [heq]
    exact tmul_mem_adelicIntRing _ hd
  | add x y hx hy =>
    obtain ⟨dx, hdx, hx'⟩ := hx
    obtain ⟨dy, hdy, hy'⟩ := hy
    refine ⟨dx * dy, mul_ne_zero hdx hdy, ?_⟩
    rw [mul_add]
    have hx1 : levelC F E (dx * dy) * x = levelC F E dy * (levelC F E dx * x) := by
      rw [levelC_mul, mul_comm (levelC F E dx), mul_assoc]
    have hy1 : levelC F E (dx * dy) * y = levelC F E dx * (levelC F E dy * y) := by
      rw [levelC_mul, mul_assoc]
    rw [hx1, hy1]
    exact add_mem (mul_mem (levelC_mem_adelicIntRing dy) hx')
      (mul_mem (levelC_mem_adelicIntRing dx) hy')

theorem exists_adelicGL_denom {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : Type*} [Fintype n] [DecidableEq n]
    (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      (∀ i j : n, levelC F E d * (G : Matrix n n _) i j ∈ adelicIntRing F E) ∧
      (∀ i j : n, levelC F E d * ((G⁻¹ : GL n _) : Matrix n n _) i j ∈ adelicIntRing F E) := by
  classical
  let f : n × n ⊕ n × n → E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    Sum.elim (fun p => (G : Matrix n n _) p.1 p.2) (fun p => ((G⁻¹ : GL n _) : Matrix n n _) p.1 p.2)
  have hf : ∀ k, ∃ d : 𝓞 F, d ≠ 0 ∧ levelC F E d * f k ∈ adelicIntRing F E :=
    fun k => exists_adelicCM_denom (f k)
  choose df hdf0 hdf using hf
  refine ⟨∏ k, df k, Finset.prod_ne_zero_iff.2 fun k _ => hdf0 k, ?_, ?_⟩
  · intro i j
    have hk := hdf (Sum.inl (i, j))
    rw [← Finset.mul_prod_erase Finset.univ df (Finset.mem_univ (Sum.inl (i, j))),
      mul_comm (df (Sum.inl (i, j))), levelC_mul, mul_assoc]
    exact mul_mem (levelC_mem_adelicIntRing _) hk
  · intro i j
    have hk := hdf (Sum.inr (i, j))
    rw [← Finset.mul_prod_erase Finset.univ df (Finset.mem_univ (Sum.inr (i, j))),
      mul_comm (df (Sum.inr (i, j))), levelC_mul, mul_assoc]
    exact mul_mem (levelC_mem_adelicIntRing _) hk

/-- Trace map `tr_{E/F} ⊗ id : E ⊗_F 𝔸_{F,f} →ₗ[F] 𝔸_{F,f}`. -/
def adelicTrace (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →ₗ[F] FiniteAdeleRing (𝓞 F) F :=
  (TensorProduct.lid F _).toLinearMap ∘ₗ (Algebra.trace F E).rTensor _

lemma adelicTrace_tmul {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (e : E) (a : FiniteAdeleRing (𝓞 F) F) :
    adelicTrace F E (e ⊗ₜ[F] a) = algebraMap F _ (Algebra.trace F E e) * a := by
  simp [adelicTrace, Algebra.smul_def]

lemma adelicTrace_mem_intAd {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {s : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (hs : s ∈ adelicIntRing F E) :
    adelicTrace F E s ∈ intAd F := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b : Module.Basis ι ℤ (𝓞 E) := Module.Free.chooseBasis ℤ (𝓞 E)
  have hz_tmul : ∀ (z : ℤ) (e : E) (a : FiniteAdeleRing (𝓞 F) F),
      (z • e) ⊗ₜ[F] a = e ⊗ₜ[F] (z • a) := fun z e a => by
    rw [zsmul_eq_mul, zsmul_eq_mul,
      ← map_intCast (algebraMap F E) z,
      ← map_intCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) z,
      ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
  let S_span : Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
    { carrier := { x | ∃ a : ι → intAd F,
        x = ∑ i : ι, algebraMap (𝓞 E) E (b i) ⊗ₜ[F] (a i : FiniteAdeleRing (𝓞 F) F) }
      zero_mem' := ⟨0, by simp⟩
      one_mem' := by
        refine ⟨fun i => ⟨(b.repr 1 i : ℤ) • (1 : FiniteAdeleRing (𝓞 F) F),
          zsmul_mem (one_mem (intAd F)) _⟩, ?_⟩
        have h1 : (1 : 𝓞 E) = ∑ i : ι, b.repr 1 i • b i := (b.sum_repr 1).symm
        have h1E : (1 : E) = ∑ i : ι, (b.repr 1 i : ℤ) • algebraMap (𝓞 E) E (b i) := by
          have := congrArg (algebraMap (𝓞 E) E) h1
          simpa only [map_one, map_sum, map_zsmul] using this
        rw [Algebra.TensorProduct.one_def, h1E, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => hz_tmul _ _ _
      add_mem' := by
        rintro _ _ ⟨a₁, rfl⟩ ⟨a₂, rfl⟩
        refine ⟨fun i => a₁ i + a₂ i, ?_⟩
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [TensorProduct.tmul_add]
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        refine ⟨fun i => -a i, ?_⟩
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [TensorProduct.tmul_neg]
      mul_mem' := by
        rintro _ _ ⟨a₁, rfl⟩ ⟨a₂, rfl⟩
        rw [Finset.sum_mul]
        have hterm : ∀ i j : ι,
            (algebraMap (𝓞 E) E (b i) ⊗ₜ[F] (a₁ i : FiniteAdeleRing (𝓞 F) F)) *
              (algebraMap (𝓞 E) E (b j) ⊗ₜ[F] (a₂ j : FiniteAdeleRing (𝓞 F) F)) =
            ∑ k : ι, algebraMap (𝓞 E) E (b k) ⊗ₜ[F]
              ((b.repr (b i * b j) k : ℤ) •
                ((a₁ i : FiniteAdeleRing (𝓞 F) F) * (a₂ j : FiniteAdeleRing (𝓞 F) F))) := by
          intro i j
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          have hbij : algebraMap (𝓞 E) E (b i) * algebraMap (𝓞 E) E (b j) =
              ∑ k : ι, (b.repr (b i * b j) k : ℤ) • algebraMap (𝓞 E) E (b k) := by
            have h0 := congrArg (algebraMap (𝓞 E) E) (b.sum_repr (b i * b j)).symm
            simpa only [map_mul, map_sum, map_zsmul] using h0
          rw [hbij, TensorProduct.sum_tmul]
          refine Finset.sum_congr rfl fun k _ => hz_tmul _ _ _
        simp_rw [Finset.mul_sum, hterm]
        have hswap : ∀ i : ι,
            (∑ j : ι, ∑ k : ι, algebraMap (𝓞 E) E (b k) ⊗ₜ[F]
              ((b.repr (b i * b j) k : ℤ) •
                ((a₁ i : FiniteAdeleRing (𝓞 F) F) * (a₂ j : FiniteAdeleRing (𝓞 F) F)))) =
            ∑ k : ι, ∑ j : ι, algebraMap (𝓞 E) E (b k) ⊗ₜ[F]
              ((b.repr (b i * b j) k : ℤ) •
                ((a₁ i : FiniteAdeleRing (𝓞 F) F) * (a₂ j : FiniteAdeleRing (𝓞 F) F))) :=
          fun i => Finset.sum_comm
        simp_rw [hswap]
        rw [Finset.sum_comm]
        refine ⟨fun k => ∑ i : ι, ∑ j : ι,
          ⟨(b.repr (b i * b j) k : ℤ) •
            ((a₁ i : FiniteAdeleRing (𝓞 F) F) * (a₂ j : FiniteAdeleRing (𝓞 F) F)),
            zsmul_mem (mul_mem (a₁ i).2 (a₂ j).2) _⟩, ?_⟩
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [AddSubmonoidClass.coe_finsetSum, TensorProduct.tmul_sum] }
  have hle : adelicIntRing F E ≤ S_span := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, ⟨e₀, rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · refine ⟨fun i => ⟨(b.repr e₀ i : ℤ) • (1 : FiniteAdeleRing (𝓞 F) F),
        zsmul_mem (one_mem _) _⟩, ?_⟩
      dsimp only
      have h0 : algebraMap (𝓞 E) E e₀ =
          ∑ i : ι, (b.repr e₀ i : ℤ) • algebraMap (𝓞 E) E (b i) := by
        have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr e₀).symm
        simpa only [map_sum, map_zsmul] using this
      rw [h0, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => hz_tmul _ _ _
    · refine ⟨fun i => ⟨(b.repr 1 i : ℤ) • y, zsmul_mem hy _⟩, ?_⟩
      dsimp only
      have h1E : (1 : E) = ∑ i : ι, (b.repr 1 i : ℤ) • algebraMap (𝓞 E) E (b i) := by
        have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr 1).symm
        simpa only [map_one, map_sum, map_zsmul] using this
      rw [h1E, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => hz_tmul _ _ _
  obtain ⟨a, rfl⟩ := hle hs
  rw [map_sum]
  refine sum_mem fun i _ => ?_
  rw [adelicTrace_tmul]
  obtain ⟨t, ht⟩ : ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = Algebra.trace F E (algebraMap (𝓞 E) E (b i)) :=
    ⟨⟨_, Algebra.isIntegral_trace (R := ℤ) (RingOfIntegers.isIntegral_coe (b i))⟩, rfl⟩
  rw [← ht, ← IsScalarTower.algebraMap_apply]
  exact mul_mem (intAd_mem_of_int t) (a i).2

lemma mem_base_integers_of_adele {F : Type*} [Field F] [NumberField F] (k : F)
    (hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAd F) :
    k ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => ?_
  have hv : (k : v.adicCompletion F) ∈ v.adicCompletionIntegers F := hk v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  exact hv

lemma trace_mem_base_of_inclE {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (e : E) (he : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e ∈ adelicIntRing F E)
    (b : 𝓞 E) :
    Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range := by
  apply mem_base_integers_of_adele
  have hb : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E b) ∈ adelicIntRing F E :=
    tmul_mem_adelicIntRing b (one_mem (intAd F))
  have hmul : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (e * algebraMap (𝓞 E) E b) ∈
      adelicIntRing F E := by
    rw [map_mul]; exact mul_mem he hb
  have ht := adelicTrace_mem_intAd hmul
  simpa [inclE, adelicTrace_tmul] using ht

lemma mem_dual_span_of_trace {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Module.Basis ι F E) (d : E) (hd : ∀ i, IsIntegral ℤ (d * β i)) (e : E)
    (he : ∀ b : 𝓞 E, Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) :
    d * e ∈ Submodule.span (𝓞 F)
      (Set.range ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β)) := by
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  rw [← β'.sum_repr (d * e)]
  refine sum_mem fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  obtain ⟨t, ht⟩ := he ⟨d * β i, hd i⟩
  have htr : Algebra.trace F E (d * e * β i) = algebraMap (𝓞 F) F t := by
    rw [ht]; congr 1; show d * e * β i = e * (d * β i); ring
  rw [htr, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end DenominatorAndTrace

section AdelicPullbackLattice

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- Pullback of an adelic lattice `L ⊆ (E ⊗_F 𝔸_{F,f})^n` along `G : GL_n(E ⊗_F 𝔸_{F,f})`
to an `𝓞_E`-submodule `Λ_G(L) = E^n ∩ G(L)`. -/
def adelicPullbackLattice (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (L : Submodule (adelicIntRing F E) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
    Submodule (𝓞 E) (n → E) where
  carrier := { x | ((G⁻¹ : GL n _) : Matrix n n _) *ᵥ
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ L }
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at *
    rw [show (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i) +
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i)) =
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) +
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i)) from rfl, Matrix.mulVec_add]
    exact L.add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
    rw [show (fun _ : n => (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 0 from rfl, Matrix.mulVec_zero]
    exact L.zero_mem
  smul_mem' := by
    intro a x hx
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *
    have heq : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (a • x i)) =
        (⟨inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a),
          tmul_mem_adelicIntRing a (one_mem (intAd F))⟩ : adelicIntRing F E) •
          (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
      ext i
      change inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (a • x i) =
        inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 E) E a) *
          inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)
      rw [Algebra.smul_def, map_mul]
    rw [heq, Matrix.mulVec_smul]
    exact L.smul_mem _ hx

lemma algebraMap_base_ne_zero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (d : 𝓞 F) (hd : d ≠ 0) :
    algebraMap (𝓞 F) E d ≠ 0 := by
  intro h
  apply hd
  have h1 : algebraMap F E (algebraMap (𝓞 F) F d) = 0 := by
    rwa [← IsScalarTower.algebraMap_apply (𝓞 F) F E]
  have h2 := (map_eq_zero_iff _ (algebraMap F E).injective).1 h1
  exact Subtype.coe_injective (h2.trans (map_zero (algebraMap (𝓞 F) F)).symm)

lemma inclE_algebraMap_base_eq_levelC (d : 𝓞 F) :
    inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) E d) = levelC F E d := by
  simp only [inclE, levelC, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F E,
    IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F),
    Algebra.algebraMap_eq_smul_one (A := E),
    Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F),
    TensorProduct.smul_tmul]

theorem adelicPullbackLattice_stab (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (L : Submodule (adelicIntRing F E) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (γ₀ : GL n E)
    (hM : G⁻¹ * baseChangeGL (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * G ∈ stabGL L) :
    γ₀ ∈ stabGL (adelicPullbackLattice G L) := by
  intro x
  change ((G⁻¹ : GL n _) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ L ↔
    ((G⁻¹ : GL n _) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ₀ : Matrix n n E) *ᵥ x) i)) ∈ L
  have hkey : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ₀ : Matrix n n E) *ᵥ x) i)) =
      ((baseChangeGL (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ : GL n _) : Matrix n n _) *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) := by
    ext i
    rw [baseChangeGL_apply_matrix, RingHom.map_mulVec]
    rfl
  rw [hkey]
  have h1 := hM (((G⁻¹ : GL n _) : Matrix n n _) *ᵥ
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)))
  rw [Matrix.mulVec_mulVec] at h1
  simp only [Units.val_mul, Matrix.mul_assoc] at h1
  rw [← Units.val_mul G G⁻¹, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h1
  rw [Matrix.mulVec_mulVec]
  exact h1

theorem adelicPullbackLattice_span_top (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (L : Submodule (adelicIntRing F E) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (c₁ d : 𝓞 F) (hc₁ : c₁ ≠ 0) (hd : d ≠ 0)
    (hL₁ : ∀ v : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
      (∀ i, v i ∈ adelicIntRing F E) → (fun i => levelC F E c₁ * v i) ∈ L)
    (hGi : ∀ i j : n, levelC F E d * ((G⁻¹ : GL n _) : Matrix n n _) i j ∈ adelicIntRing F E) :
    Submodule.span E (adelicPullbackLattice G L : Set (n → E)) = ⊤ := by
  set u : E := algebraMap (𝓞 F) E (c₁ * d)
  have hu : u ≠ 0 := algebraMap_base_ne_zero (c₁ * d) (mul_ne_zero hc₁ hd)
  have hk : ∀ k : n, Pi.single k u ∈ adelicPullbackLattice G L := by
    intro k
    change ((G⁻¹ : GL n _) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single k u : n → E) i)) ∈ L
    have hs : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single k u : n → E) i)) =
        Pi.single k (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) u) := by
      ext i
      by_cases h : i = k <;> simp [h]
    rw [hs, Matrix.mulVec_single]
    convert hL₁ (fun i => levelC F E d * ((G⁻¹ : GL n _) : Matrix n n _) i k) (fun i => hGi i k)
      using 1
    ext i
    simp only [u, map_mul, inclE_algebraMap_base_eq_levelC, Pi.smul_apply,
      Matrix.col_apply, op_smul_eq_smul, smul_eq_mul, mul_assoc]
  rw [eq_top_iff, ← (Pi.basisFun E n).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  have hsingle : Pi.basisFun E n k = u⁻¹ • Pi.single k u := by
    rw [Pi.basisFun_apply, ← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hu]
  rw [hsingle]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hk k))

theorem adelicPullbackLattice_finite (G : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (L : Submodule (adelicIntRing F E) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (c₂ d : 𝓞 F) (hc₂ : c₂ ≠ 0) (hd : d ≠ 0)
    (hL₂ : ∀ v ∈ L, ∀ i : n, levelC F E c₂ * v i ∈ adelicIntRing F E)
    (hG : ∀ i j : n, levelC F E d * (G : Matrix n n _) i j ∈ adelicIntRing F E) :
    Module.Finite (𝓞 E) (adelicPullbackLattice G L) := by
  classical
  set β := Module.finBasis F E
  obtain ⟨d₀, hd₀, -, hd₀i⟩ := exists_int_denom_of_numberField (fun i => β i)
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  set u : E := algebraMap (𝓞 F) E (d * c₂)
  have hu : u ≠ 0 := algebraMap_base_ne_zero (d * c₂) (mul_ne_zero hd hc₂)
  set q : E := (d₀ * u)⁻¹
  set W : Submodule (𝓞 F) (n → E) := Submodule.span (𝓞 F)
    (Set.range fun p : n × Fin (Module.finrank F E) => (Pi.single p.1 (q * β' p.2) : n → E))
  have hle : (adelicPullbackLattice G L).restrictScalars (𝓞 F) ≤ W := by
    intro x hx
    have hw := hL₂ _ hx
    set w := ((G⁻¹ : GL n _) : Matrix n n _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))
    have hx' : (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) =
        (G : Matrix n n _) *ᵥ w := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hj : ∀ j : n, inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (u * x j) ∈ adelicIntRing F E := by
      intro j
      rw [map_mul, inclE_algebraMap_base_eq_levelC, levelC_mul, congrFun hx' j]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine sum_mem fun k _ => ?_
      have heq : levelC F E d * levelC F E c₂ * ((G : Matrix n n _) j k * w k) =
          (levelC F E d * (G : Matrix n n _) j k) * (levelC F E c₂ * w k) := by ring
      rw [heq]
      exact mul_mem (hG j k) (hw k)
    have hmem : ∀ j : n, d₀ * (u * x j) ∈ Submodule.span (𝓞 F) (Set.range β') := fun j =>
      mem_dual_span_of_trace β d₀ hd₀i _ (trace_mem_base_of_inclE _ (hj j))
    rw [← Finset.univ_sum_single x]
    refine sum_mem fun j _ => ?_
    let Lj : E →ₗ[𝓞 F] (n → E) :=
      (LinearMap.single (𝓞 F) (fun _ => E) j) ∘ₗ ((LinearMap.mulLeft F q).restrictScalars (𝓞 F))
    have h1 : Lj (d₀ * (u * x j)) = Pi.single j (x j) := by
      have hd0 : d₀ * u ≠ 0 := mul_ne_zero hd₀ hu
      simp only [Lj, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        LinearMap.mulLeft_apply, LinearMap.coe_single, q]
      congr 1
      rw [← mul_assoc, ← mul_assoc, mul_assoc _ d₀ u, inv_mul_cancel₀ hd0, one_mul]
    rw [← h1]
    have h2 := Submodule.mem_map_of_mem (f := Lj) (hmem j)
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨(j, i), by simp [Lj]⟩
  let ιF := Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let bF : Module.Basis ιF ℤ (𝓞 F) := Module.Free.chooseBasis ℤ (𝓞 F)
  set WZ : Submodule ℤ (n → E) := Submodule.span ℤ
    (Set.range fun r : (n × Fin (Module.finrank F E)) × ιF =>
      (bF r.2 • (Pi.single r.1.1 (q * β' r.1.2) : n → E)))
  have hleZ : (adelicPullbackLattice G L).restrictScalars ℤ ≤ WZ := by
    intro w hw
    have hwW : w ∈ W := hle hw
    rw [Submodule.mem_span_range_iff_exists_fun] at hwW
    obtain ⟨c, rfl⟩ := hwW
    refine sum_mem fun p _ => ?_
    have hc : c p = ∑ i : ιF, bF.repr (c p) i • bF i := (bF.sum_repr (c p)).symm
    rw [hc, Finset.sum_smul]
    refine sum_mem fun i _ => ?_
    have hsm : (bF.repr (c p) i • bF i) • (Pi.single p.1 (q * β' p.2) : n → E) =
        bF.repr (c p) i • (bF i • (Pi.single p.1 (q * β' p.2) : n → E)) := by
      ext j
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc,
        ← IsScalarTower.algebraMap_apply ℤ (𝓞 F) E]
    rw [hsm]
    exact Submodule.smul_mem WZ _ (Submodule.subset_span ⟨(p, i), rfl⟩)
  haveI : IsNoetherian ℤ WZ := isNoetherian_span_of_finite ℤ (Set.finite_range _)
  let f : ((adelicPullbackLattice G L).restrictScalars ℤ) →ₗ[ℤ] WZ :=
    Submodule.inclusion hleZ
  haveI : Module.Finite ℤ (LinearMap.range f) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian (LinearMap.range f))
  have hfinZ : Module.Finite ℤ (adelicPullbackLattice G L) :=
    Module.Finite.equiv (LinearEquiv.ofInjective f (Submodule.inclusion_injective hleZ)).symm
  haveI := hfinZ
  exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) (adelicPullbackLattice G L)

end AdelicPullbackLattice

section MainFinitenessTheorems

/-- **Unconditional Lattice Stabilizer Finiteness (`stabilizer_lattice_finite_of_definite`)**:
for any totally definite Hermitian matrix `(σ, J)` over a CM field `E/F` and any finitely
generated full-rank `𝓞_E`-lattice `Λ ⊆ E^n`, `U(J)(E) ∩ Stab(Λ)` is `Finite`. -/
theorem stabilizer_lattice_finite_of_definite {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n : Type*} [Fintype n] [DecidableEq n]
    (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHermMatrix (σ : E →+* E) J) (hdet : IsUnit J.det)
    (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    Finite (latticeLevel (σ : E →+* E) J Λ) := by
  classical
  obtain ⟨dJ, hdJ0, -, hdJ⟩ := exists_int_denom_of_numberField (fun p : n × n => J p.1 p.2)
  obtain ⟨S, hS⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨dL, hdL0, -, hdL⟩ := exists_int_denom_of_numberField (fun p : S × n => (p.1 : n → E) p.2)
  have hΛint : ∀ v ∈ Λ, ∀ k : n, IsIntegral ℤ (dL * v k) := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem x hx => intro k; exact hdL (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have heq : (r • x) k = algebraMap (𝓞 E) E r * x k := by
        rw [Pi.smul_apply, Algebra.smul_def]
      rw [heq, mul_left_comm]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hcol : ∀ j : n, ∃ c : E, c ≠ 0 ∧ c • (Pi.single j 1 : n → E) ∈ Λ := by
    intro j
    have hm : (Pi.single j 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; trivial
    obtain ⟨m, f, gg, hsum⟩ := Submodule.mem_span_set'.mp hm
    obtain ⟨d, hd0, -, hd⟩ := exists_int_denom_of_numberField f
    refine ⟨d, hd0, ?_⟩
    rw [← hsum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hd l)
    have heq : d • (f l • (gg l : n → E)) = r • (gg l : n → E) := by
      rw [smul_smul, ← hr, algebraMap_smul]
    rw [heq]
    exact Λ.smul_mem r (gg l).2
  choose c hc0 hcΛ using hcol
  let β : (E →+* ℂ) × n × n → ℝ := fun z =>
    ‖z.1 (dJ * dL * c z.2.2)‖ * (‖z.1 (J z.2.1 z.2.1)‖ + ‖z.1 (J z.2.2 z.2.2)‖)
  obtain ⟨B, hB⟩ := (Set.finite_range β).bddAbove
  set T : Set E := { x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B }
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  have hmem : ∀ g ∈ latticeLevel (σ : E →+* E) J Λ, ∀ i j : n,
      dJ * dL * c j * ((J * (g : Matrix n n E)) i j) ∈ T := by
    intro g hg i j
    have hU : conjTransposeMap (σ : E →+* E) (g : Matrix n n E) * J * (g : Matrix n n E) = J := hg.1
    have hstab : ∀ x : n → E, x ∈ Λ ↔ (g : Matrix n n E) *ᵥ x ∈ Λ := hg.2
    have hgc : (g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E)) ∈ Λ := (hstab _).mp (hcΛ j)
    have hcoord : ∀ k, ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k =
        c j * (g : Matrix n n E) k j := by
      intro k; simp [Matrix.mulVec_smul]
    refine ⟨?_, fun φ => ?_⟩
    · have heq : dJ * dL * c j * ((J * (g : Matrix n n E)) i j) =
          ∑ k : n, (dJ * J i k) * (dL * ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k) := by
        simp only [hcoord, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [heq]
      exact IsIntegral.sum _ fun k _ => (hdJ (i, k)).mul (hΛint _ hgc k)
    · rw [map_mul, norm_mul]
      calc ‖φ (dJ * dL * c j)‖ * ‖φ ((J * (g : Matrix n n E)) i j)‖
          ≤ ‖φ (dJ * dL * c j)‖ * (‖φ (J i i)‖ + ‖φ (J j j)‖) :=
            mul_le_mul_of_nonneg_left
              (definite_cauchy_schwarz_entry_bound σ J φ (hτ φ) hH hdef.2 _ hU i j)
              (norm_nonneg _)
        _ = β (φ, i, j) := rfl
        _ ≤ B := hB ⟨(φ, i, j), rfl⟩
  haveI : Finite T := hTfin.to_subtype
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr hdet
  refine Finite.of_injective
    (fun g : latticeLevel (σ : E →+* E) J Λ => fun i j => (⟨_, hmem g.1 g.2 i j⟩ : T)) ?_
  intro g g' hgg
  have h1 : J * (g.1 : Matrix n n E) = J * (g'.1 : Matrix n n E) := by
    ext i j
    have hij := congrArg Subtype.val (congrFun (congrFun hgg i) j)
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hdJ0 hdL0) (hc0 j)) hij
  exact Subtype.ext (Units.ext (hJu.mul_left_cancel h1))

/-- **Main Coset Stabilizer Finiteness Theorem (`stabilizer_coset_finite_of_definite`)**:
for ANY definite CM Hermitian space `H : DefiniteHermSpace E F V`, ANY compact open level
`K : CompactOpenLevel H.toHerm`, and ANY `g ∈ U(V)(𝔸_{F,f})`, the arithmetic stabilizer
`{ γ ∈ U(V)(E) | g⁻¹ * finRat(γ) * g ∈ K }` is **FINITE**. -/
theorem stabilizer_coset_finite_of_definite {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : DefiniteHermSpace E F V) (K : CompactOpenLevel H.toHerm)
    (g : UnitaryFiniteAdelicGrp H.toHerm) :
    Finite { γ : UnitaryGrp H.toHerm // g⁻¹ * H.toHerm.ratToFiniteAdelic γ * g ∈ K.toSubgroup } := by
  classical
  set G : GL (Fin H.toHerm.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := g.1
  obtain ⟨d, hd0, hG, hGi⟩ := exists_adelicGL_denom G
  let Λ := adelicPullbackLattice G K.lat
  have hfinΛ : Module.Finite (𝓞 E) Λ :=
    adelicPullbackLattice_finite G K.lat K.c₂ d K.hc₂ hd0 K.upper_bound hG
  have hspanΛ : Submodule.span E (Λ : Set (Fin H.toHerm.dim → E)) = ⊤ :=
    adelicPullbackLattice_span_top G K.lat K.c₁ d K.hc₁ hd0 K.lower_bound hGi
  have hF : Finite (latticeLevel H.toHerm.cm.conjRingHom H.toHerm.gram Λ) :=
    stabilizer_lattice_finite_of_definite H.toHerm.cm.conjAlgHom H.toHerm.gram
      H.toHerm.cm.star_embedding_eq_comp H.toHerm.gram_isHerm H.toHerm.gram_det_isUnit
      H.isTotDef Λ hfinΛ hspanΛ
  let toMat : { γ : UnitaryGrp H.toHerm // g⁻¹ * H.toHerm.ratToFiniteAdelic γ * g ∈ K.toSubgroup } →
      latticeLevel H.toHerm.cm.conjRingHom H.toHerm.gram Λ := fun γ =>
    ⟨(unitaryGrpEquivMat H.toHerm γ.1).1,
      (unitaryGrpEquivMat H.toHerm γ.1).2,
      by
        refine adelicPullbackLattice_stab G K.lat (unitaryGrpEquivMat H.toHerm γ.1).1 ?_
        have hstab : G⁻¹ * (baseChangeGL (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
            ((unitaryGrpEquivMat H.toHerm γ.1).1)) * G ∈ stabGL K.lat :=
          K.stabilizes_lat (g⁻¹ * H.toHerm.ratToFiniteAdelic γ.1 * g) γ.2
        exact hstab⟩
  refine Finite.of_injective toMat ?_
  intro γ₁ γ₂ h
  apply Subtype.ext
  apply (unitaryGrpEquivMat H.toHerm).injective
  exact Subtype.ext (congrArg (fun z : latticeLevel _ _ _ => z.1) h)

/-- **Main Stabilizer Finiteness Theorem (`stabilizer_finite_of_definite`)**:
for ANY definite CM Hermitian space `H : DefiniteHermSpace E F V` (in particular, every
positive-definite Hermitian space over a CM field) and ANY compact open level
`K_f : CompactOpenLevel H.toHerm`, the discrete arithmetic subgroup `U(V)(F) ∩ K_f` is **FINITE**. -/
theorem stabilizer_finite_of_definite {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : DefiniteHermSpace E F V) (K : CompactOpenLevel H.toHerm) :
    Finite { γ : UnitaryGrp H.toHerm // H.toHerm.ratToFiniteAdelic γ ∈ K.toSubgroup } := by
  have h := stabilizer_coset_finite_of_definite H K 1
  let e : { γ : UnitaryGrp H.toHerm // H.toHerm.ratToFiniteAdelic γ ∈ K.toSubgroup } ≃
      { γ : UnitaryGrp H.toHerm // (1 : UnitaryFiniteAdelicGrp H.toHerm)⁻¹ *
        H.toHerm.ratToFiniteAdelic γ * 1 ∈ K.toSubgroup } :=
    { toFun := fun γ => ⟨γ.1, by simpa using γ.2⟩
      invFun := fun γ => ⟨γ.1, by simpa using γ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Finite.of_equiv _ e.symm

/-- Positive-definite specialization of `stabilizer_finite_of_definite`. -/
theorem stabilizer_finite_of_posDef {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) (hpos : H.IsPosDef) (K : CompactOpenLevel H) :
    Finite { γ : UnitaryGrp H // H.ratToFiniteAdelic γ ∈ K.toSubgroup } :=
  stabilizer_finite_of_definite (DefiniteHermSpace.ofPosDef H hpos) K

/-- Bridge to `Stage11DefiniteUnitaryChain`: every complex positive-definite Hermitian lattice `L`
in `DefiniteHermitianSpace N` has finite definite unitary automorphism group. -/
theorem definiteUnitaryGroup_finite_bridge {N : ℕ}
    (L : RHDirect.Stage11DefiniteUnitaryChain.HermitianLattice N) :
    Finite (RHDirect.Stage11DefiniteUnitaryChain.DefiniteUnitaryGroup L) :=
  RHDirect.Stage11DefiniteUnitaryChain.finite_definiteUnitaryGroup L

end MainFinitenessTheorems

end StabilizerFiniteness

end RHDirect.Stage14M1_UnitaryGroupDef
