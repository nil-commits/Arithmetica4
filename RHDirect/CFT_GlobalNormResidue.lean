import RHDirect.CFT_GlobalInequalities
import RHDirect.CFT_CyclotomicCharacters
import RHDirect.CFT_LocalArtinReciprocity

/-!
# RHDirect.CFT_GlobalNormResidue

Global Class Field Theory Pillar — Global Norm Residue Symbol & Idele Class Group Theory:
1. Local-to-global norm residue symbols at finite and infinite places (`RangeFiniteLocalNormLeKerLocalSymbol`,
   `Infinite`, `RangeIdeleNormLeKerIdeleSymbol`, `RestrictNormalInfiniteLocalSymbol`, `Surjective`).
2. Functoriality of local and global norm residue symbols in towers (`FunctorialLocal`,
   `FunctorialFinite`, `FunctorialInfinite`, `Functorial`).
3. Rational and cyclotomic norm residue symbols, reciprocity on `ℚ`, continuity, and surjectivity
   onto cyclotomic Galois groups (`RationalLocal`, `RationalCyclotomic`, `RationalDiagonal`,
   `Rational`, `RationalContinuous`, `CyclotomicBase`, `CyclotomicCompositum`, `CyclotomicImage`,
   `Cyclotomic`).
4. Idele class group direct limit, Galois invariants, Tate cohomology via Herbrand & Second Inequality,
   and abstract class field theory `ClassFieldData` on `IdeleClassLimit` (`ConjugateNorm`,
   `IdeleClassMapIdeleClassMap`, `IdeleClassEquivIdeleClassMapOfComm`, `Invariants`,
   `InvariantsGalois`, `NatCardTateOfIsCyclic`, `Theory`).
-/

noncomputable section

namespace RHDirect.CFT.Global

open RHDirect.Stage13CFT_IdeleNormResidue
open RHDirect.CFT_ProfiniteSemilocal

/-! ### 01_IdeleClassGroup.ConjugateNorm -/
section Sec3_01_IdeleClassGroup_ConjugateNorm

open IsDedekindDomain NumberField AdeleBaseChange
open scoped NumberField.AdeleRing

noncomputable section

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  {ι : Type*} [Fintype ι]

omit [NumberField K] [NumberField L] [NumberField M] in

theorem det_conjugates_ne_zero [DecidableEq ι] (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (b : Module.Basis ι K L) :
    (Matrix.of fun i j ↦ τ i (algebraMap L M (b j))).det ≠ 0 := by
  classical
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv0
  let χ : ι → (L →* M) := fun i ↦
    ((τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M) : L →+* M).toMonoidHom
  have hχ : Function.Injective χ := by
    intro i j hij
    apply hτ
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom L M).comp χ hχ
  let f : L →ₗ[K] M := ∑ i, LinearMap.mulLeft K (v i) ∘ₗ
    ((τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M)).toLinearMap
  have hf : f = 0 := by
    refine b.ext fun j ↦ ?_
    have hj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hj
    simpa [f] using hj
  have hsum : ∑ i, v i • ((χ i : L →* M) : L → M) = 0 := by
    funext x
    have hx := LinearMap.congr_fun hf x
    simpa [f, χ] using hx
  funext i
  exact (Fintype.linearIndependent_iff.1 hli) v hsum i

theorem adeleMap_norm_eq_prod (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (hcard : Fintype.card ι = Module.finrank K L) (y : 𝔸[L]) :
    adeleMap K M (Algebra.norm 𝔸[K] y) = ∏ i, τ i • adeleMap L M y := by
  classical
  let b : Module.Basis ι K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hcard).symm
  let B := adeleBasis b
  let A := Algebra.leftMulMatrix B y
  let D : Matrix ι ι M := Matrix.of fun i j ↦ τ i (algebraMap L M (b j))
  have hA : ∀ k j, A k j = B.repr (y * B j) k := fun k j ↦
    Algebra.leftMulMatrix_eq_repr_mul B y k j
  have hy : ∀ j, y * algebraMap L 𝔸[L] (b j) =
      ∑ k, adeleMap K L (A k j) * algebraMap L 𝔸[L] (b k) := by
    intro j
    conv_lhs => rw [← B.sum_repr (y * algebraMap L 𝔸[L] (b j))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply, hA, adeleBasis_apply]
  have key : Matrix.diagonal (fun i ↦ τ i • adeleMap L M y) * D.map (algebraMap M 𝔸[M]) =
      D.map (algebraMap M 𝔸[M]) * A.map (adeleMap K M) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    have h := congrArg (fun z ↦ τ i • adeleMap L M z) (hy j)
    simp only [map_mul, map_sum, smul_mul', Finset.smul_sum, adeleMap_algebraMap,
      adeleMap_adeleMap, AdeleBaseChange.smul_algebraMap, smul_adeleMap] at h
    simp only [Matrix.map_apply, Matrix.of_apply, D, h]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at hdet
  rw [Algebra.norm_eq_matrix_det B]
  rw [mul_comm] at hdet
  have hu : IsUnit (algebraMap M 𝔸[M] D.det) :=
    (isUnit_iff_ne_zero.2 (det_conjugates_ne_zero τ hτ b)).map _
  exact (hu.mul_left_cancel hdet).symm

theorem ideleEmbedding_ideleNorm_eq_prod (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (hcard : Fintype.card ι = Module.finrank K L) (x : IdeleGroup L) :
    ideleEmbedding K M (ideleNorm K L x) = ∏ i, τ i • ideleEmbedding L M x :=
  Units.ext (by
    rw [coe_ideleEmbedding, coe_ideleNorm, adeleMap_norm_eq_prod τ hτ hcard, Units.coe_prod]
    rfl)

theorem ideleClassMap_ideleClassNorm_eq_prod (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (hcard : Fintype.card ι = Module.finrank K L) (c : IdeleClassGroup L) :
    ideleClassMap K M (ideleClassNorm K L c) = ∏ i, τ i • ideleClassMap L M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  simp only [ideleClassNorm_mk, ideleClassMap_mk, ideleEmbedding_ideleNorm_eq_prod τ hτ hcard,
    smul_mk, map_prod]

end

end Sec3_01_IdeleClassGroup_ConjugateNorm

/-! ### 02_IdeleClassGroup.IdeleClassMapIdeleClassMap -/
section Sec3_02_IdeleClassGroup_IdeleClassMapIdeleClassMap

open NumberField IntermediateField

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

abbrev FiniteSubfield : Type := {F : IntermediateField ℚ ℚ̄ // FiniteDimensional ℚ F}

namespace FiniteSubfield

instance (F : FiniteSubfield) : FiniteDimensional ℚ F.1 := F.2

instance (F : FiniteSubfield) : NumberField F.1 where
  to_finiteDimensional := by convert F.2

instance : IsDirectedOrder FiniteSubfield where
  directed F E := ⟨⟨F.1 ⊔ E.1, inferInstance⟩, le_sup_left (a := F.1), le_sup_right (a := F.1)⟩

instance : Nonempty FiniteSubfield := ⟨⟨⊥, inferInstance⟩⟩

abbrev algebraOfLE {F E : FiniteSubfield} (h : F ≤ E) : Algebra F.1 E.1 :=
  (IntermediateField.inclusion (show F.1 ≤ E.1 from h)).toRingHom.toAlgebra

theorem algebraOfLE_algebraMap {F E : FiniteSubfield} (h : F ≤ E) (x : F.1) :
    ((@algebraMap F.1 E.1 _ _ (algebraOfLE h) x : E.1) : ℚ̄) = x :=
  rfl

def ideleClassMap {F E : FiniteSubfield} (h : F ≤ E) :
    IdeleClassGroup F.1 →* IdeleClassGroup E.1 :=
  letI := algebraOfLE h
  RHDirect.CFT_ProfiniteSemilocal.ideleClassMap F.1 E.1

theorem ideleClassMap_mk {F E : FiniteSubfield} (h : F ≤ E) (x : IdeleGroup F.1) :
    ideleClassMap h (IdeleClassGroup.mk F.1 x) =
      IdeleClassGroup.mk E.1 (@ideleEmbedding F.1 E.1 _ _ _ _ (algebraOfLE h) x) :=
  rfl

theorem ideleClassMap_injective {F E : FiniteSubfield} (h : F ≤ E) :
    Function.Injective (ideleClassMap h) :=
  letI := algebraOfLE h
  RHDirect.CFT_ProfiniteSemilocal.ideleClassMap_injective

theorem ideleClassMap_ideleClassMap {F E M : FiniteSubfield} (hFE : F ≤ E) (hEM : E ≤ M)
    (c : IdeleClassGroup F.1) :
    ideleClassMap hEM (ideleClassMap hFE c) = ideleClassMap (hFE.trans hEM) c := by
  let := algebraOfLE hFE
  let := algebraOfLE hEM
  let := algebraOfLE (hFE.trans hEM)
  have : IsScalarTower F.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact RHDirect.CFT_ProfiniteSemilocal.ideleClassMap_ideleClassMap c

@[simp]
theorem ideleClassMap_self {F : FiniteSubfield} (h : F ≤ F) (c : IdeleClassGroup F.1) :
    ideleClassMap h c = c :=
  ideleClassMap_injective h (ideleClassMap_ideleClassMap h h c)

instance directedSystem : DirectedSystem (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ ideleClassMap h) where
  map_self _ c := ideleClassMap_self _ c
  map_map _ _ _ hFE hEM c := ideleClassMap_ideleClassMap hFE hEM c

end FiniteSubfield

def IdeleClassLimit : Type :=
  DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)

namespace IdeleClassLimit

instance : CommGroup IdeleClassLimit :=
  inferInstanceAs (CommGroup (DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)))

def of (F : FiniteSubfield) : IdeleClassGroup F.1 →* IdeleClassLimit where
  toFun c := (⟦⟨F, c⟩⟧ : DirectLimit (fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap h))
  map_one' := (DirectLimit.one_def (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F).symm
  map_mul' x y := (DirectLimit.mul_def (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F x y).symm

@[simp]
theorem of_ideleClassMap {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup F.1) :
    of E (FiniteSubfield.ideleClassMap h c) = of F c :=
  show (⟦⟨E, FiniteSubfield.ideleClassMap h c⟩⟧ : DirectLimit
    (fun F : FiniteSubfield ↦ IdeleClassGroup F.1) (fun _ _ h ↦ FiniteSubfield.ideleClassMap h)) =
      ⟦⟨F, c⟩⟧ from DirectLimit.mk_apply (F := fun F : FiniteSubfield ↦ IdeleClassGroup F.1)
        (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) F E c h

theorem of_injective (F : FiniteSubfield) : Function.Injective (of F) :=
  DirectLimit.mk_injective (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h)
    (fun _ _ h ↦ FiniteSubfield.ideleClassMap_injective h) F

theorem exists_of (z : IdeleClassLimit) : ∃ (F : FiniteSubfield) (c : IdeleClassGroup F.1),
    of F c = z := by
  obtain ⟨F, c, rfl⟩ := DirectLimit.exists_eq_mk
    (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) z
  exact ⟨F, c, rfl⟩

theorem exists_of₂ (z w : IdeleClassLimit) : ∃ (F : FiniteSubfield) (c d : IdeleClassGroup F.1),
    of F c = z ∧ of F d = w := by
  obtain ⟨F, c, d, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂
    (f := fun _ _ h ↦ FiniteSubfield.ideleClassMap h) z w
  exact ⟨F, c, d, rfl, rfl⟩

theorem of_eq_of_iff {F E M : FiniteSubfield} (hF : F ≤ M) (hE : E ≤ M) (x : IdeleClassGroup F.1)
    (y : IdeleClassGroup E.1) : of F x = of E y ↔ FiniteSubfield.ideleClassMap hF x = FiniteSubfield.ideleClassMap hE y := by
  rw [← of_ideleClassMap hF x, ← of_ideleClassMap hE y, (of_injective M).eq_iff]

section lift

variable {G : Type*} [CommGroup G] (g : ∀ F : FiniteSubfield, IdeleClassGroup F.1 →* G)
  (compat : ∀ (F E : FiniteSubfield) (h : F ≤ E) (c : IdeleClassGroup F.1),
    g E (FiniteSubfield.ideleClassMap h c) = g F c)

def lift : IdeleClassLimit →* G where
  toFun := DirectLimit.lift (fun _ _ h ↦ FiniteSubfield.ideleClassMap h) (fun F c ↦ g F c)
    fun F E h c ↦ (compat F E h c).symm
  map_one' := by
    obtain ⟨F⟩ := (inferInstance : Nonempty FiniteSubfield)
    have h1 : (1 : IdeleClassLimit) = of F 1 := (map_one _).symm
    rw [h1]
    exact map_one (g F)
  map_mul' z w := by
    obtain ⟨F, c, d, rfl, rfl⟩ := exists_of₂ z w
    rw [← map_mul]
    exact map_mul (g F) c d

@[simp]
theorem lift_of (F : FiniteSubfield) (c : IdeleClassGroup F.1) : lift g compat (of F c) = g F c :=
  rfl

theorem lift_comp_of (F : FiniteSubfield) : (lift g compat).comp (of F) = g F :=
  MonoidHom.ext fun _ ↦ rfl

theorem lift_unique (φ : IdeleClassLimit →* G) (hφ : ∀ F, φ.comp (of F) = g F) :
    φ = lift g compat := by
  ext z
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [lift_of, ← hφ F, MonoidHom.comp_apply]

end lift

@[ext]
theorem hom_ext {G : Type*} [Monoid G] {φ ψ : IdeleClassLimit →* G}
    (h : ∀ F : FiniteSubfield, φ.comp (of F) = ψ.comp (of F)) : φ = ψ := by
  ext z
  obtain ⟨F, c, rfl⟩ := exists_of z
  exact DFunLike.congr_fun (h F) c

end IdeleClassLimit

end

end Sec3_02_IdeleClassGroup_IdeleClassMapIdeleClassMap

/-! ### 03_NormResidueSymbol.RangeFiniteLocalNormLeKerLocalSymbol -/
section Sec3_03_NormResidueSymbol_RangeFiniteLocalNormLeKerLocalSymbol

open IsDedekindDomain NumberField SemiLocal
open scoped Pointwise

noncomputable section

section Range

variable {F E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω]

def equivFieldRange (i : E →ₐ[F] Ω) : E ≃ₐ[F] i.fieldRange :=
  AlgEquiv.ofInjectiveField i

@[simp]
theorem coe_equivFieldRange (i : E →ₐ[F] Ω) (y : E) :
    ((equivFieldRange i y : i.fieldRange) : Ω) = i y :=
  rfl

end Range

section NormResidue

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] (M : Type*) [Field M] [Algebra k M] [FiniteDimensional k M]

def residueEmbedding : M →ₐ[k] AlgebraicClosure k :=
  IsAlgClosed.lift

def residueImage : IntermediateField k (AlgebraicClosure k) :=
  (residueEmbedding k M).fieldRange

def residueImageEquiv : M ≃ₐ[k] residueImage k M :=
  AlgEquiv.ofInjectiveField (residueEmbedding k M)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
@[simp]
theorem coe_residueImageEquiv (y : M) :
    ((residueImageEquiv k M y : residueImage k M) : AlgebraicClosure k) = residueEmbedding k M y :=
  rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem residueEmbedding_residueImageEquiv_symm (z : residueImage k M) :
    residueEmbedding k M ((residueImageEquiv k M).symm z) = z := by
  rw [← coe_residueImageEquiv, AlgEquiv.apply_symm_apply]

instance : FiniteDimensional k (residueImage k M) :=
  LinearEquiv.finiteDimensional (residueImageEquiv k M).toLinearEquiv

instance [IsGalois k M] : IsGalois k (residueImage k M) :=
  IsGalois.of_algEquiv (residueImageEquiv k M)

instance [IsMulCommutative (M ≃ₐ[k] M)] :
    IsMulCommutative (residueImage k M ≃ₐ[k] residueImage k M) :=
  ⟨⟨fun a b ↦ (AlgEquiv.autCongr (residueImageEquiv k M)).symm.injective (by
    rw [map_mul, map_mul]
    exact mul_comm' _ _)⟩⟩

variable [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)]

def normResidueSymbol : kˣ →* (M ≃ₐ[k] M) :=
  (AlgEquiv.autCongr (residueImageEquiv k M).symm).toMonoidHom.comp
    ((RHDirect.CFT.LocalField.abelianRestrict (residueImage k M)).comp
      (RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k)))

variable {k M}

theorem normResidueSymbol_apply (x : kˣ) (y : M) :
    normResidueSymbol k M x y = (residueImageEquiv k M).symm
      (RHDirect.CFT.LocalField.abelianRestrict (residueImage k M)
        (RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k) x) (residueImageEquiv k M y)) :=
  rfl

theorem exists_mk_eq_localReciprocityLimit (x : kˣ) :
    ∃ τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      (τ : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
        RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k) x :=
  QuotientGroup.mk_surjective _

theorem residueEmbedding_normResidueSymbol {x : kˣ}
    {τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
      RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k) x) (y : M) :
    residueEmbedding k M (normResidueSymbol k M x y) = τ (residueEmbedding k M y) := by
  rw [normResidueSymbol_apply, ← hτ, RHDirect.CFT.LocalField.abelianRestrict_mk,
    residueEmbedding_residueImageEquiv_symm]
  exact AlgEquiv.restrictNormal_commutes τ (residueImage k M) (residueImageEquiv k M y)

theorem normResidueSymbol_spec (i : M →ₐ[k] AlgebraicClosure k) {x : kˣ}
    {τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
      RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k) x) (y : M) :
    i (normResidueSymbol k M x y) = τ (i y) := by
  set χ : residueImage k M ≃ₐ[k] i.fieldRange :=
    (residueImageEquiv k M).symm.trans
      (equivFieldRange i) with hχ
  set ρ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k := χ.liftNormal (AlgebraicClosure k) with hρ
  have hρi : ∀ z : M, ρ (residueEmbedding k M z) = i z := fun z ↦
    (χ.liftNormal_commutes (AlgebraicClosure k) (residueImageEquiv k M z)).trans (by
      rw [hχ, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
      rfl)
  have hτ' : ((ρ⁻¹ * τ * ρ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) :
      TopologicalAbelianization (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)) =
        RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k) x := by
    rw [← hτ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, mul_comm, ← mul_assoc,
      QuotientGroup.mk_inv, mul_inv_cancel, one_mul]
  have h := residueEmbedding_normResidueSymbol hτ' y
  rw [← hρi, ← hρi, h]
  simp [AlgEquiv.mul_apply]

theorem ker_normResidueSymbol :
    (normResidueSymbol k M).ker = (RHDirect.CFT.LocalField.normUnits k M).range := by
  have hN : (RHDirect.CFT.LocalField.normUnits k (residueImage k M)).range =
      (RHDirect.CFT.LocalField.normUnits k M).range := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨Units.map (residueImageEquiv k M).symm.toRingEquiv.toMonoidHom z, Units.ext ?_⟩
      simp only [RHDirect.CFT.LocalField.coe_normUnits, Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv (residueImageEquiv k M).symm (z : residueImage k M)
    · rintro ⟨z, rfl⟩
      refine ⟨Units.map (residueImageEquiv k M).toRingEquiv.toMonoidHom z, Units.ext ?_⟩
      simp only [RHDirect.CFT.LocalField.coe_normUnits, Units.coe_map]
      exact Algebra.norm_eq_of_algEquiv (residueImageEquiv k M) (z : M)
  ext x
  rw [MonoidHom.mem_ker, ← hN]
  change (AlgEquiv.autCongr (residueImageEquiv k M).symm)
    (RHDirect.CFT.LocalField.abelianRestrict (residueImage k M)
      (RHDirect.CFT.LocalField.localReciprocityLimit k (AlgebraicClosure k) x)) = 1 ↔ _
  rw [RHDirect.CFT.LocalField.abelianRestrict_localReciprocityLimit, map_eq_one_iff _ (MulEquiv.injective _),
    map_eq_one_iff _ (MulEquiv.injective _), QuotientGroup.eq_one_iff]

end NormResidue

theorem continuous_monoidHom_of_isOpen_ker {G D : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one, nhds_discrete D, Filter.tendsto_pure]
  exact Filter.mem_of_superset (hf.mem_nhds f.ker.one_mem) fun x hx ↦ hx

section Finite

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

instance isMulCommutative_gal_adicCompletion [IsMulCommutative (L ≃ₐ[K] L)] (w : PlacesOver L v) :
    IsMulCommutative (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) :=
  ⟨⟨fun a b ↦ (decompositionMulEquiv v w.1).symm.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact mul_comm' _ _))⟩⟩

variable [IsMulCommutative (L ≃ₐ[K] L)]

def symbolAt (w : PlacesOver L v) : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  (MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal).subtype.comp
    ((decompositionMulEquiv v w.1).symm.toMonoidHom.comp
      (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L)))

theorem symbolAt_mem_stabilizer (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) :
    symbolAt L v w x ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal :=
  ((decompositionMulEquiv v w.1).symm _).2

theorem algebraMap_symbolAt_apply (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) (l : L) :
    algebraMap L (w.1.adicCompletion L) (symbolAt L v w x l) =
      normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x
        (algebraMap L (w.1.adicCompletion L) l) := by
  have h : decompositionToLocal v w.1 ((decompositionMulEquiv v w.1).symm
      (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x)) =
        normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x :=
    (decompositionMulEquiv v w.1).apply_symm_apply _
  conv_rhs => rw [← h]
  rw [decompositionToLocal_algebraMap]
  rfl

theorem symbolAt_eq (w w' : PlacesOver L v) : symbolAt L v w = symbolAt L v w' := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  have h' : w'.1 = σ • w.1 := by rw [← hσ]; rfl
  set s := galEquiv v σ w.1 w'.1 h' with hs_def
  ext x l
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion K) x
  set a := normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x with ha
  set a' := normResidueSymbol (v.adicCompletion K) (w'.1.adicCompletion L) x with ha'
  have hs : ∀ y, a' (s y) = s (a y) := fun y ↦ by
    apply (residueEmbedding (v.adicCompletion K) (w'.1.adicCompletion L)).toRingHom.injective
    have h2 : residueEmbedding _ _ (s (a y)) = τ (residueEmbedding _ _ (s y)) :=
      normResidueSymbol_spec
        ((residueEmbedding (v.adicCompletion K) (w'.1.adicCompletion L)).comp s.toAlgHom) hτ y
    change residueEmbedding _ _ (a' (s y)) = residueEmbedding _ _ (s (a y))
    rw [ha', residueEmbedding_normResidueSymbol hτ, h2]
  set d := symbolAt L v w x with hd_def
  have hd : σ (d (σ⁻¹ l)) = d l := by
    have := congrArg (fun g : L ≃ₐ[K] L ↦ g l)
      (show σ * d * σ⁻¹ = d by rw [mul_comm' σ d, mul_inv_cancel_right])
    simpa only [AlgEquiv.mul_apply] using this
  apply (algebraMap L (w'.1.adicCompletion L)).injective
  calc algebraMap L (w'.1.adicCompletion L) (d l)
      = algebraMap L (w'.1.adicCompletion L) (σ (d (σ⁻¹ l))) := by rw [hd]
    _ = s (algebraMap L (w.1.adicCompletion L) (d (σ⁻¹ l))) :=
        (galEquiv_algebraMap v σ w.1 w'.1 h' _).symm
    _ = s (a (algebraMap L (w.1.adicCompletion L) (σ⁻¹ l))) := by
        rw [hd_def, algebraMap_symbolAt_apply]
    _ = a' (s (algebraMap L (w.1.adicCompletion L) (σ⁻¹ l))) := (hs _).symm
    _ = a' (algebraMap L (w'.1.adicCompletion L) (σ (σ⁻¹ l))) := by
        rw [hs_def, galEquiv_algebraMap]
    _ = a' (algebraMap L (w'.1.adicCompletion L) l) := by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    _ = algebraMap L (w'.1.adicCompletion L) (symbolAt L v w' x l) :=
        (algebraMap_symbolAt_apply L v w' x l).symm

def localSymbol : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  symbolAt L v (nonempty_placesOver L v).some

theorem localSymbol_eq_symbolAt (w : PlacesOver L v) : localSymbol L v = symbolAt L v w :=
  symbolAt_eq L v _ w

theorem localSymbol_mem_stabilizer (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) :
    localSymbol L v x ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal := by
  rw [localSymbol_eq_symbolAt L v w]
  exact symbolAt_mem_stabilizer L v w x

theorem algebraMap_localSymbol_apply (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) (l : L) :
    algebraMap L (w.1.adicCompletion L) (localSymbol L v x l) =
      normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x
        (algebraMap L (w.1.adicCompletion L) l) := by
  rw [localSymbol_eq_symbolAt L v w]
  exact algebraMap_symbolAt_apply L v w x l

theorem ker_localSymbol (w : PlacesOver L v) :
    (localSymbol L v).ker =
      (RHDirect.CFT.LocalField.normUnits (v.adicCompletion K) (w.1.adicCompletion L)).range := by
  rw [localSymbol_eq_symbolAt L v w, ← ker_normResidueSymbol]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (((decompositionMulEquiv v w.1).symm
    (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x)) : L ≃ₐ[K] L) = 1 ↔ _
  rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

theorem units_le_ker_localSymbol (w : PlacesOver L v)
    (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker := by
  intro u hu
  rw [ker_localSymbol L v w]
  obtain ⟨y, -, hyu⟩ := IdeleNorm.exists_norm_eq_of_ramificationIdx_eq_one v w.1 he hu
  exact ⟨y, Units.ext hyu⟩

theorem eventually_units_le_ker_localSymbol :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker := by
  filter_upwards [IdeleNorm.eventually_forall_placesOver K
    (IdeleNorm.eventually_ramificationIdx_eq_one K L)] with v hv
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact units_le_ker_localSymbol L v w (hv w)

theorem continuous_localSymbol : Continuous (localSymbol L v) := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  refine continuous_monoidHom_of_isOpen_ker _ ?_
  rw [ker_localSymbol L v w]
  exact RHDirect.CFT.LocalField.isOpen_range_normUnits _ _

theorem range_finiteLocalNorm_le_ker_localSymbol :
    (IdeleNorm.finiteLocalNorm L v).range ≤ (localSymbol L v).ker := by
  rintro _ ⟨y, rfl⟩
  change ∏ w, Units.map (Algebra.norm (v.adicCompletion K) :
    w.1.adicCompletion L →* v.adicCompletion K) (y w) ∈ _
  exact Subgroup.prod_mem _ fun w _ ↦ by
    rw [ker_localSymbol L v w]
    exact ⟨y w, rfl⟩

end Finite

end

end Sec3_03_NormResidueSymbol_RangeFiniteLocalNormLeKerLocalSymbol

/-! ### 04_NormResidueSymbol.RationalCyclotomic -/
section Sec3_04_NormResidueSymbol_RationalCyclotomic

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped RHDirect.CFT_AbstractLocalReciprocity

noncomputable section

namespace RationalSymbol

open RHDirect.CFT_CyclotomicCharacters.Cyclotomic RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

instance isGalois_maxCyclotomic : IsGalois ℚ maxCyclotomic := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ maxCyclotomic _ (IntermediateField.algebra' maxCyclotomic) := by
    rw [← InfiniteGalois.normal_iff_isGalois, ← ker_character]
    infer_instance
  convert h
  exact Subsingleton.elim _ _

abbrev cycRestrict : Gal(ℚ̄/ℚ) →* Gal(maxCyclotomic/ℚ) :=
  AlgEquiv.restrictNormalHom maxCyclotomic

theorem cycRestrict_surjective : Function.Surjective cycRestrict := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  exact AlgEquiv.restrictNormalHom_surjective ℚ̄

theorem coe_cycRestrict_apply (σ : Gal(ℚ̄/ℚ)) (x : maxCyclotomic) :
    ((cycRestrict σ x : maxCyclotomic) : ℚ̄) = σ x :=
  AlgEquiv.restrictNormal_commutes σ maxCyclotomic x

theorem ker_cycRestrict : cycRestrict.ker = character.ker := by
  rw [ker_character]
  ext σ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := coe_cycRestrict_apply σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at this
    exact this.symm
  · intro h
    ext x
    rw [coe_cycRestrict_apply, AlgEquiv.one_apply]
    exact h x x.2

def cycCharacter : Gal(maxCyclotomic/ℚ) ≃* ℤ̂ˣ :=
  (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq ker_cycRestrict).trans
      (QuotientGroup.quotientKerEquivOfSurjective character character_surjective))

theorem cycCharacter_cycRestrict (σ : Gal(ℚ̄/ℚ)) : cycCharacter (cycRestrict σ) = character σ := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective cycRestrict cycRestrict_surjective).symm
      (cycRestrict σ) = (σ : Gal(ℚ̄/ℚ) ⧸ cycRestrict.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [cycCharacter, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

theorem cycCharacter_spec (τ : Gal(maxCyclotomic/ℚ)) (n : ℕ+) {ζ : maxCyclotomic}
    (hζ : ζ ^ (n : ℕ) = 1) :
    τ ζ = ζ ^ (ProfiniteInteger.proj n (cycCharacter τ : ℤ̂)).val := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  apply Subtype.ext
  rw [cycCharacter_cycRestrict, SubmonoidClass.coe_pow]
  rw [coe_cycRestrict_apply]
  exact character_spec σ n (by rw [← SubmonoidClass.coe_pow, hζ, OneMemClass.coe_one])

def unitPart : IdeleClassGroup ℚ →* ℤ̂ˣ :=
  (Units.map padicEquiv.symm.toRingHom.toMonoidHom).comp
    ((MonoidHom.snd _ _).comp RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom)

theorem unitPart_surjective : Function.Surjective unitPart := by
  intro w
  obtain ⟨x, hx⟩ := RationalIdeles.ideleClassGroupEquiv.surjective
    (1, Units.map padicEquiv.toRingHom.toMonoidHom w)
  refine ⟨x, Units.ext ?_⟩
  simp only [unitPart, MonoidHom.comp_apply, MonoidHom.coe_snd, Units.coe_map]
  change padicEquiv.symm ((RationalIdeles.ideleClassGroupEquiv x).2 : _) = _
  rw [hx]
  simp [ofPadics_toPadics]

theorem toPadicInt_unitPart (x : IdeleClassGroup ℚ) (q : Nat.Primes) :
    toPadicInt q (unitPart x : ℤ̂) =
      ((RationalIdeles.ideleClassGroupEquiv x).2 : Π p : Nat.Primes, ℤ_[p]) q := by
  change toPadics (padicEquiv.symm _) q = _
  rw [← padicEquiv_apply, RingEquiv.apply_symm_apply]
  rfl

def reciprocityMap : IdeleClassGroup ℚ →* Gal(maxCyclotomic/ℚ) :=
  cycCharacter.symm.toMonoidHom.comp unitPart⁻¹

theorem cycCharacter_reciprocityMap (x : IdeleClassGroup ℚ) :
    cycCharacter (reciprocityMap x) = (unitPart x)⁻¹ := by
  simp [reciprocityMap]

theorem reciprocityMap_surjective : Function.Surjective reciprocityMap := by
  intro τ
  obtain ⟨x, hx⟩ := unitPart_surjective (cycCharacter τ)⁻¹
  refine ⟨x, cycCharacter.injective ?_⟩
  rw [cycCharacter_reciprocityMap, hx, inv_inv]

theorem reciprocityMap_eq_one_iff (x : IdeleClassGroup ℚ) :
    reciprocityMap x = 1 ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 := by
  rw [← cycCharacter.injective.eq_iff, map_one, cycCharacter_reciprocityMap, inv_eq_one]
  have h : unitPart x =
      Units.map padicEquiv.symm.toRingHom.toMonoidHom (RationalIdeles.ideleClassGroupEquiv x).2 :=
    rfl
  rw [h, ← map_one (Units.map padicEquiv.symm.toRingHom.toMonoidHom)]
  exact (Units.map_injective (f := padicEquiv.symm.toRingHom.toMonoidHom)
    padicEquiv.symm.injective).eq_iff

end RationalSymbol

end

end Sec3_04_NormResidueSymbol_RationalCyclotomic

/-! ### 05_IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm -/
section Sec3_05_IdeleClassGroup_IdeleClassEquivIdeleClassMapOfComm

open NumberField IntermediateField AdeleBaseChange
open scoped NumberField.AdeleRing

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Naturality

variable {L L' M M' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field M]
  [NumberField M] [Field M'] [NumberField M'] [Algebra L M] [Algebra L' M']

theorem adeleRingEquiv_adeleMap_of_comm (τ : L ≃+* L') (ρ : M ≃+* M')
    (h : ∀ l : L, ρ (algebraMap L M l) = algebraMap L' M' (τ l)) (a : 𝔸[L]) :
    adeleRingEquiv ρ (adeleMap L M a) = adeleMap L' M' (adeleRingEquiv τ a) := by
  have : IsScalarTower ℚ L M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsScalarTower ℚ L' M' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have key : ((adeleRingEquiv ρ : 𝔸[M] →+* 𝔸[M']).comp (adeleMap L M) : 𝔸[L] →+* 𝔸[M']) =
      (adeleMap L' M').comp (adeleRingEquiv τ : 𝔸[L] →+* 𝔸[L']) := by
    refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, adeleMap_algebraMap,
        adeleRingEquiv_algebraMap, h]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, adeleMap_adeleMap,
        adeleRingEquiv_adeleMap_rat]
  exact congrArg (fun f : 𝔸[L] →+* 𝔸[M'] ↦ f a) key

theorem ideleEquiv_ideleEmbedding_of_comm (τ : L ≃+* L') (ρ : M ≃+* M')
    (h : ∀ l : L, ρ (algebraMap L M l) = algebraMap L' M' (τ l)) (x : IdeleGroup L) :
    ideleEquiv ρ (ideleEmbedding L M x) = ideleEmbedding L' M' (ideleEquiv τ x) :=
  Units.ext (adeleRingEquiv_adeleMap_of_comm τ ρ h (x : 𝔸[L]))

theorem ideleClassEquiv_ideleClassMap_of_comm (τ : L ≃+* L') (ρ : M ≃+* M')
    (h : ∀ l : L, ρ (algebraMap L M l) = algebraMap L' M' (τ l)) (c : IdeleClassGroup L) :
    ideleClassEquiv ρ (ideleClassMap L M c) = ideleClassMap L' M' (ideleClassEquiv τ c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassMap_mk, ideleClassEquiv_mk, ideleClassEquiv_mk, ideleClassMap_mk,
    ideleEquiv_ideleEmbedding_of_comm τ ρ h]

end Naturality

namespace FiniteSubfield

def map (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : FiniteSubfield :=
  ⟨F.1.map (σ : ℚ̄ →ₐ[ℚ] ℚ̄),
    LinearEquiv.finiteDimensional (IntermediateField.equivMap F.1 (σ : ℚ̄ →ₐ[ℚ] ℚ̄)).toLinearEquiv⟩

def mapEquiv (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : F.1 ≃+* (map σ F).1 :=
  (IntermediateField.equivMap F.1 (σ : ℚ̄ →ₐ[ℚ] ℚ̄)).toRingEquiv

@[simp]
theorem coe_mapEquiv (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (x : F.1) :
    ((mapEquiv σ F x : (map σ F).1) : ℚ̄) = σ x :=
  rfl

theorem map_mono (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) {F E : FiniteSubfield} (h : F ≤ E) : map σ F ≤ map σ E :=
  IntermediateField.map_mono _ (show F.1 ≤ E.1 from h)

theorem of_ideleClassEquiv_congr {F E E' : FiniteSubfield} (τ : F.1 ≃+* E.1) (τ' : F.1 ≃+* E'.1)
    (h : ∀ x : F.1, (τ x : ℚ̄) = τ' x) (c : IdeleClassGroup F.1) :
    IdeleClassLimit.of E (ideleClassEquiv τ c) = IdeleClassLimit.of E' (ideleClassEquiv τ' c) := by
  have hE : E = E' := by
    refine Subtype.ext (SetLike.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩)
    · obtain ⟨x, hx⟩ := τ.surjective ⟨y, hy⟩
      have hy' : y = ((τ' x : E'.1) : ℚ̄) := by rw [← h x, hx]
      rw [hy']
      exact (τ' x).2
    · obtain ⟨x, hx⟩ := τ'.surjective ⟨y, hy⟩
      have hy' : y = ((τ x : E.1) : ℚ̄) := by rw [h x, hx]
      rw [hy']
      exact (τ x).2
  subst hE
  have : τ = τ' := RingEquiv.ext fun x ↦ Subtype.ext (h x)
  rw [this]

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield

def conjOf (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) : IdeleClassGroup F.1 →* IdeleClassLimit :=
  (of (map σ F)).comp (ideleClassEquiv (mapEquiv σ F)).toMulEquiv.toMonoidHom

theorem conjOf_apply (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    conjOf σ F c = of (map σ F) (ideleClassEquiv (mapEquiv σ F) c) :=
  rfl

theorem conjOf_compat (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F E : FiniteSubfield) (h : F ≤ E)
    (c : IdeleClassGroup F.1) : conjOf σ E (FiniteSubfield.ideleClassMap h c) = conjOf σ F c := by
  rw [conjOf_apply, conjOf_apply, FiniteSubfield.ideleClassMap]
  let := algebraOfLE h
  let := algebraOfLE (map_mono σ h)
  rw [ideleClassEquiv_ideleClassMap_of_comm (mapEquiv σ F) (mapEquiv σ E) (fun x ↦ rfl)]
  exact of_ideleClassMap (map_mono σ h) _

def galoisHom (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : IdeleClassLimit →* IdeleClassLimit :=
  lift (conjOf σ) (conjOf_compat σ)

theorem galoisHom_of (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    galoisHom σ (of F c) = of (map σ F) (ideleClassEquiv (mapEquiv σ F) c) :=
  rfl

theorem galoisHom_one (z : IdeleClassLimit) : galoisHom 1 z = z := by
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [galoisHom_of]
  refine (of_ideleClassEquiv_congr (mapEquiv 1 F) (RingEquiv.refl F.1) (fun x ↦ rfl) c).trans ?_
  rw [ideleClassEquiv_refl]

theorem galoisHom_mul (σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleClassLimit) :
    galoisHom (σ * τ) z = galoisHom σ (galoisHom τ z) := by
  obtain ⟨F, c, rfl⟩ := exists_of z
  rw [galoisHom_of, galoisHom_of, galoisHom_of, ← ideleClassEquiv_trans]
  exact of_ideleClassEquiv_congr (mapEquiv (σ * τ) F)
    ((mapEquiv τ F).trans (mapEquiv σ (map τ F))) (fun x ↦ rfl) c

instance : MulDistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit where
  smul σ z := galoisHom σ z
  one_smul := galoisHom_one
  mul_smul := galoisHom_mul
  smul_one σ := map_one (galoisHom σ)
  smul_mul σ := map_mul (galoisHom σ)

theorem smul_def (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (z : IdeleClassLimit) : σ • z = galoisHom σ z :=
  rfl

theorem smul_of (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    σ • of F c = of (map σ F) (ideleClassEquiv (mapEquiv σ F) c) :=
  rfl

theorem smul_of_eq_of_mem_fixingSubgroup {F : FiniteSubfield} {σ : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hσ : σ ∈ F.1.fixingSubgroup) (c : IdeleClassGroup F.1) : σ • of F c = of F c := by
  rw [smul_of]
  refine (of_ideleClassEquiv_congr (mapEquiv σ F) (RingEquiv.refl F.1)
    (fun x ↦ (IntermediateField.mem_fixingSubgroup_iff F.1 σ).1 hσ x x.2) c).trans ?_
  rw [ideleClassEquiv_refl]

instance : RHDirect.CFT_AbstractLocalReciprocity.IsDiscreteModule (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit where
  isOpen_stabilizer z := by
    obtain ⟨F, c, rfl⟩ := exists_of z
    have : FiniteDimensional ℚ F.1 := F.2
    exact Subgroup.isOpen_mono (H₁ := F.1.fixingSubgroup)
      (fun σ hσ ↦ smul_of_eq_of_mem_fixingSubgroup hσ c) F.1.fixingSubgroup_isOpen

end IdeleClassLimit

end

end Sec3_05_IdeleClassGroup_IdeleClassEquivIdeleClassMapOfComm

/-! ### 06_NormResidueSymbol.FunctorialLocal -/
section Sec3_06_NormResidueSymbol_FunctorialLocal

open RHDirect.CFT.LocalField

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
  [IsMulCommutative (M ≃ₐ[k] M)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in

theorem isAbelianGalois_of_isGalois : IsAbelianGalois k M :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  [FiniteDimensional k M] in

theorem apply_mem_maximalAbelianExtension {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (z : M) : ι z ∈ maximalAbelianExtension k Ω :=
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  have := isAbelianGalois_fieldRange ι
  le_maximalAbelianExtension ι.fieldRange ⟨z, rfl⟩

theorem normResidueSymbol_eq_localArtinMapOfField :
    have := isAbelianGalois_of_isGalois (k := k) (M := M)
    normResidueSymbol k M = localArtinMapOfField k M := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  ext x z
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := k) x
  apply (residueEmbedding k M).injective
  change residueEmbedding k M _ = residueEmbedding k M _
  rw [residueEmbedding_normResidueSymbol hτ,
    localArtinMapOfField_eq_artinOfEmbedding (residueEmbedding k M), apply_artinOfEmbedding,
    localArtinMap_apply, ← hτ, topologicalAbelianizationEquiv_mk_apply]

theorem normResidueSymbol_apply_eq_localArtinMap {Ω : Type*} [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] (ι : M →ₐ[k] Ω) (x : kˣ) (z : M) :
    ι (normResidueSymbol k M x z) =
      ((localArtinMap k Ω x ⟨ι z, apply_mem_maximalAbelianExtension ι z⟩ :
        maximalAbelianExtension k Ω) : Ω) := by
  have := isAbelianGalois_of_isGalois (k := k) (M := M)
  rw [normResidueSymbol_eq_localArtinMapOfField, localArtinMapOfField_eq_artinOfEmbedding ι,
    apply_artinOfEmbedding]

variable {k' : Type*} [Field k'] [ValuativeRel k'] [TopologicalSpace k']
  [IsNonarchimedeanLocalField k'] [CharZero k'] [Algebra k k'] [ValuativeExtension k k']
  [FiniteDimensional k k']
  {M' : Type*} [Field M'] [Algebra k' M'] [Algebra k M'] [IsScalarTower k k' M']
  [FiniteDimensional k' M'] [IsGalois k' M'] [IsMulCommutative (M' ≃ₐ[k'] M')]

theorem normResidueSymbol_norm (j : M →ₐ[k] M') (x : k'ˣ) (z : M) :
    normResidueSymbol k' M' x (j z) = j (normResidueSymbol k M (normUnits k k' x) z) := by
  have : IsSepClosure k (AlgebraicClosure k') :=
    isSepClosure_of_isSeparable k k' (AlgebraicClosure k')
  set ι' : M' →ₐ[k'] AlgebraicClosure k' := IsAlgClosed.lift
  set ι : M →ₐ[k] AlgebraicClosure k' := (ι'.restrictScalars k).comp j
  apply ι'.injective
  have h1 := normResidueSymbol_apply_eq_localArtinMap ι' x (j z)
  have h2 := normResidueSymbol_apply_eq_localArtinMap ι (normUnits k k' x) z
  have h3 := localArtinMap_apply_of_algebra (Ω := AlgebraicClosure k') x
    (apply_mem_maximalAbelianExtension ι z)
  exact h1.trans (h3.trans h2.symm)

end Local

end

end Sec3_06_NormResidueSymbol_FunctorialLocal

/-! ### 07_NormResidueSymbol.Infinite -/
section Sec3_07_NormResidueSymbol_Infinite

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding
open scoped NumberField.LiesOver ComplexConjugate

noncomputable section

section Conj

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isConj_iff_forall {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} :
    IsConj φ σ ↔ ∀ x, φ (σ x) = star (φ x) :=
  ⟨fun h ↦ h.eq, fun h ↦ RingHom.ext fun x ↦ by
    rw [RingHom.comp_apply, conjugate_coe_eq, starRingEnd_apply]
    exact (h x).symm⟩

theorem isConj_conjugate_iff {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} :
    IsConj (conjugate φ) σ ↔ IsConj φ σ := by
  simp only [isConj_iff_forall, conjugate_coe_eq, starRingEnd_apply]
  constructor
  · intro h x
    simpa using congrArg star (h x)
  · intro h x
    rw [h x]

theorem isConj_iff_of_mk_eq {φ ψ : L →+* ℂ} (h : mk φ = mk ψ) (σ : L ≃ₐ[K] L) :
    IsConj φ σ ↔ IsConj ψ σ := by
  rcases mk_eq_iff.1 h with rfl | rfl
  · rfl
  · exact isConj_conjugate_iff.symm

theorem isConj_comp_iff [IsMulCommutative (L ≃ₐ[K] L)] {φ : L →+* ℂ} {σ ν : L ≃ₐ[K] L} :
    IsConj (φ.comp (ν : L →+* L)) σ ↔ IsConj φ σ := by
  have hc : ∀ y, ν (σ y) = σ (ν y) := fun y ↦ by
    rw [← AlgEquiv.mul_apply, mul_comm' ν σ, AlgEquiv.mul_apply]
  have hν : ∀ y, (ν : L →+* L) y = ν y := fun _ ↦ rfl
  simp only [isConj_iff_forall, RingHom.comp_apply, hν]
  constructor
  · intro h y
    have := h (ν.symm y)
    rwa [hc, AlgEquiv.apply_symm_apply] at this
  · intro h y
    rw [hc]
    exact h (ν y)

open scoped Classical in

def conjOfEmbedding (φ : L →+* ℂ) : L ≃ₐ[K] L :=
  if h : ∃ σ : L ≃ₐ[K] L, IsConj φ σ then h.choose else 1

theorem conjOfEmbedding_eq {φ : L →+* ℂ} {σ : L ≃ₐ[K] L} (hσ : IsConj φ σ) :
    conjOfEmbedding φ = σ := by
  have h : ∃ σ : L ≃ₐ[K] L, IsConj φ σ := ⟨σ, hσ⟩
  rw [conjOfEmbedding, dif_pos h]
  exact h.choose_spec.ext hσ

theorem conjOfEmbedding_of_not {φ : L →+* ℂ} (h : ¬ ∃ σ : L ≃ₐ[K] L, IsConj φ σ) :
    conjOfEmbedding (K := K) φ = 1 := by
  rw [conjOfEmbedding, dif_neg h]

theorem conjOfEmbedding_congr {φ ψ : L →+* ℂ}
    (h : ∀ σ : L ≃ₐ[K] L, IsConj φ σ ↔ IsConj ψ σ) :
    conjOfEmbedding (K := K) φ = conjOfEmbedding ψ := by
  by_cases hφ : ∃ σ : L ≃ₐ[K] L, IsConj φ σ
  · obtain ⟨σ, hσ⟩ := hφ
    rw [conjOfEmbedding_eq hσ, conjOfEmbedding_eq ((h σ).1 hσ)]
  · rw [conjOfEmbedding_of_not hφ,
      conjOfEmbedding_of_not fun ⟨σ, hσ⟩ ↦ hφ ⟨σ, (h σ).2 hσ⟩]

theorem conjOfEmbedding_mul_self (φ : L →+* ℂ) :
    conjOfEmbedding (K := K) φ * conjOfEmbedding φ = 1 := by
  by_cases hφ : ∃ σ : L ≃ₐ[K] L, IsConj φ σ
  · obtain ⟨σ, hσ⟩ := hφ
    rw [conjOfEmbedding_eq hσ]
    exact AlgEquiv.ext fun x ↦ isConj_apply_apply hσ x
  · rw [conjOfEmbedding_of_not hφ, mul_one]

variable (K) in

def conjAt (w : InfinitePlace L) : L ≃ₐ[K] L :=
  conjOfEmbedding w.embedding

theorem conjAt_mul_self (w : InfinitePlace L) : conjAt K w * conjAt K w = 1 :=
  conjOfEmbedding_mul_self _

theorem conjAt_of_isReal {w : InfinitePlace L} (hw : w.IsReal) : conjAt K w = 1 :=
  conjOfEmbedding_eq (isConj_one_iff.2 (isReal_iff.1 hw))

theorem isConj_conjAt [IsGalois K L] {w : InfinitePlace L} (hw : w.IsRamified K) :
    IsConj w.embedding (conjAt K w) := by
  obtain ⟨σ, hσ⟩ := exists_isConj_of_isRamified (k := K) (φ := w.embedding) (by rwa [mk_embedding])
  rw [conjAt, conjOfEmbedding_eq hσ]
  exact hσ

theorem conjAt_ne_one [IsGalois K L] {w : InfinitePlace L} (hw : w.IsRamified K) :
    conjAt K w ≠ 1 :=
  (isConj_ne_one_iff (isConj_conjAt hw)).2 fun h ↦
    not_isReal_iff_isComplex.2 (isRamified_iff.1 hw).1 (isReal_iff.2 h)

theorem conjAt_smul [IsMulCommutative (L ≃ₐ[K] L)] (τ : L ≃ₐ[K] L) (w : InfinitePlace L) :
    conjAt K (τ • w) = conjAt K w := by
  refine conjOfEmbedding_congr fun σ ↦ ?_
  have h : mk (τ • w).embedding = mk (w.embedding.comp (τ.symm : L →+* L)) := by
    rw [mk_embedding, ← InfinitePlace.smul_mk, mk_embedding]
  rw [isConj_iff_of_mk_eq h]
  exact isConj_comp_iff

theorem conjAt_eq [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] {v : InfinitePlace K}
    (w w' : v.placesOver L) : conjAt K (w : InfinitePlace L) = conjAt K (w' : InfinitePlace L) := by
  obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (L ≃ₐ[K] L) w w'
  rw [InfinitePlace.coe_smul_placesOver, conjAt_smul]

end Conj

section Completion

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]

theorem extensionEmbedding_algebraMap_self (l : L) :
    extensionEmbedding w (algebraMap L w.Completion l) = w.embedding l :=
  extensionEmbedding_coe w _

theorem completionConj_algebraMap (hv : v.IsReal) (l : L) :
    InfinitePlace.completionConj (w := w) hv (algebraMap L w.Completion l) =
      algebraMap L w.Completion (conjAt K w l) := by
  by_cases hw : w.IsComplex
  · have hram : w.IsRamified K :=
      isRamified_iff.2 ⟨hw, by rw [InfinitePlace.LiesOver.comap_eq w v]; exact hv⟩
    apply (extensionEmbedding w).injective
    rw [InfinitePlace.extensionEmbedding_completionConj, extensionEmbedding_algebraMap_self,
      extensionEmbedding_algebraMap_self, (isConj_conjAt hram).eq, starRingEnd_apply]
  · have hw' : w.IsReal := not_isComplex_iff_isReal.1 hw
    rw [InfinitePlace.completionConj, dif_neg hw, conjAt_of_isReal hw']
    rfl

end Completion

section Symbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : InfinitePlace K)

open scoped Classical in

def infiniteLocalSymbol : v.Completionˣ →* (L ≃ₐ[K] L) :=
  if hv : v.IsReal then
    (InfinitePlace.realSignHom (conjAt K ((IdeleNorm.nonempty_infinitePlacesOver L v).some :
        InfinitePlace L)) (conjAt_mul_self _)).comp
      (Units.map (extensionEmbeddingOfIsReal hv).toMonoidHom)
  else 1

theorem infiniteLocalSymbol_apply (hv : v.IsReal) (w : v.placesOver L) (x : v.Completionˣ) :
    infiniteLocalSymbol L v x =
      if extensionEmbeddingOfIsReal hv x < 0 then conjAt K (w : InfinitePlace L) else 1 := by
  rw [infiniteLocalSymbol, dif_pos hv, MonoidHom.comp_apply, InfinitePlace.realSignHom_apply,
    conjAt_eq _ w]
  rfl

omit [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] in

theorem infiniteLocalSymbol_of_not_isReal (hv : ¬ v.IsReal) : infiniteLocalSymbol L v = 1 := by
  rw [infiniteLocalSymbol, dif_neg hv]

theorem algebraMap_infiniteLocalSymbol_apply (w : v.placesOver L) (x : v.Completionˣ) (l : L) :
    algebraMap L (w : InfinitePlace L).Completion (infiniteLocalSymbol L v x l) =
      InfinitePlace.localSymbol v (w : InfinitePlace L) x
        (algebraMap L (w : InfinitePlace L).Completion l) := by
  by_cases hv : v.IsReal
  · rw [infiniteLocalSymbol_apply L v hv w, InfinitePlace.localSymbol_apply v _ hv]
    split_ifs
    · exact (completionConj_algebraMap (w : InfinitePlace L) hv l).symm
    · rfl
  · rw [infiniteLocalSymbol_of_not_isReal L v hv, InfinitePlace.localSymbol_of_not_isReal v _ hv]
    rfl

theorem ker_infiniteLocalSymbol (w : v.placesOver L) :
    (infiniteLocalSymbol L v).ker = InfinitePlace.normSubgroup v (w : InfinitePlace L) := by
  by_cases h2 : v.IsReal ∧ (w : InfinitePlace L).IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hram : (w : InfinitePlace L).IsRamified K :=
      isRamified_iff.2 ⟨hw, by rw [InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v]; exact hv⟩
    ext x
    rw [MonoidHom.mem_ker, infiniteLocalSymbol_apply L v hv w,
      InfinitePlace.mem_normSubgroup_iff hv hw]
    have hx0 : extensionEmbeddingOfIsReal hv x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    constructor
    · intro h
      by_contra hneg
      rw [if_pos (lt_of_le_of_ne (not_lt.1 hneg) hx0)] at h
      exact conjAt_ne_one hram h
    · intro h
      rw [if_neg (not_lt.2 h.le)]
  · rw [InfinitePlace.normSubgroup_eq_top (w : InfinitePlace L) h2, eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    by_cases hv : v.IsReal
    · have hw : (w : InfinitePlace L).IsReal := not_isComplex_iff_isReal.1 fun hw ↦ h2 ⟨hv, hw⟩
      rw [infiniteLocalSymbol_apply L v hv w, conjAt_of_isReal hw, ite_self]
    · rw [infiniteLocalSymbol_of_not_isReal L v hv, MonoidHom.one_apply]

open scoped Classical in

theorem range_infiniteLocalNorm_le_ker_infiniteLocalSymbol :
    (IdeleNorm.infiniteLocalNorm L v).range ≤ (infiniteLocalSymbol L v).ker := by
  rintro _ ⟨y, rfl⟩
  change ∏ w : v.placesOver L, Units.map (Algebra.norm v.Completion :
    (w : InfinitePlace L).Completion →* v.Completion) (y w) ∈ _
  exact Subgroup.prod_mem _ fun w _ ↦ by
    rw [ker_infiniteLocalSymbol L v w]
    exact ⟨y w, rfl⟩

theorem continuous_infiniteLocalSymbol : Continuous (infiniteLocalSymbol L v) :=
  continuous_monoidHom_of_isOpen_ker _ (Subgroup.isOpen_mono
    (range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L v)
    (IdeleNorm.isOpen_range_infiniteLocalNorm v))

end Symbol

end

end Sec3_07_NormResidueSymbol_Infinite

/-! ### 08_NormResidueSymbol.RationalLocal -/
section Sec3_08_NormResidueSymbol_RationalLocal

open IsDedekindDomain NumberField

noncomputable section

namespace RationalSymbol

abbrev prime (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ := Rat.HeightOneSpectrum.primesEquiv v

instance (v : HeightOneSpectrum (𝓞 ℚ)) : Fact (prime v).Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev padicRingEquiv : v.adicCompletion ℚ ≃+* ℚ_[prime v] :=
  RingEquivClass.toRingEquiv (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

theorem continuous_padicRingEquiv : Continuous (padicRingEquiv v) :=
  map_continuous (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

theorem continuous_padicRingEquiv_symm : Continuous (padicRingEquiv v).symm :=
  HomeomorphClass.inv_continuous (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v)

def closureEquiv :
    AlgebraicClosure (v.adicCompletion ℚ) ≃+* AlgebraicClosure ℚ_[prime v] :=
  IsAlgClosure.equivOfEquiv _ _ (padicRingEquiv v)

theorem closureEquiv_algebraMap (x : v.adicCompletion ℚ) :
    closureEquiv v (algebraMap _ (AlgebraicClosure (v.adicCompletion ℚ)) x) =
      algebraMap ℚ_[prime v] (AlgebraicClosure ℚ_[prime v]) (padicRingEquiv v x) :=
  IsAlgClosure.equivOfEquiv_algebraMap _ _ _ x

theorem mem_maximalAbelianExtension_of_pow_eq_one {y : AlgebraicClosure (v.adicCompletion ℚ)}
    {n : ℕ} (hn : 0 < n) (hy : y ^ n = 1) :
    y ∈ RHDirect.CFT.LocalField.maximalAbelianExtension (v.adicCompletion ℚ)
      (AlgebraicClosure (v.adicCompletion ℚ)) := by
  rw [← RHDirect.CFT.LocalField.mem_maximalAbelianExtension_transport_iff (padicRingEquiv v) (closureEquiv v)
    (closureEquiv_algebraMap v), RHDirect.CFT.LocalField.Padic.maximalAbelianExtension_eq_adjoin_rootsOfUnity]
  exact IntermediateField.subset_adjoin _ _ ⟨n, hn, by rw [← map_pow, hy, map_one]⟩

theorem closureEquiv_apply_of_localReciprocityLimit (x : (v.adicCompletion ℚ)ˣ)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        RHDirect.CFT.LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    {τ' : AlgebraicClosure ℚ_[prime v] ≃ₐ[ℚ_[prime v]] AlgebraicClosure ℚ_[prime v]}
    (hτ' : (τ' : TopologicalAbelianization (AlgebraicClosure ℚ_[prime v] ≃ₐ[ℚ_[prime v]]
      AlgebraicClosure ℚ_[prime v])) =
        RHDirect.CFT.LocalField.localReciprocityLimit ℚ_[prime v] (AlgebraicClosure ℚ_[prime v])
          (Units.map (padicRingEquiv v).toRingHom.toMonoidHom x))
    {y : AlgebraicClosure (v.adicCompletion ℚ)}
    (hy : y ∈ RHDirect.CFT.LocalField.maximalAbelianExtension (v.adicCompletion ℚ)
      (AlgebraicClosure (v.adicCompletion ℚ))) :
    closureEquiv v (τ y) = τ' (closureEquiv v y) := by
  have h := RHDirect.CFT.LocalField.transport_localArtinMap_apply_of_continuous (padicRingEquiv v)
    (continuous_padicRingEquiv v) (continuous_padicRingEquiv_symm v) (closureEquiv v)
    (closureEquiv_algebraMap v) x hy
  rw [RHDirect.CFT.LocalField.localArtinMap_apply, RHDirect.CFT.LocalField.localArtinMap_apply, ← hτ, ← hτ',
    RHDirect.CFT.LocalField.topologicalAbelianizationEquiv_mk_apply,
    RHDirect.CFT.LocalField.topologicalAbelianizationEquiv_mk_apply] at h
  exact h

theorem pos_of_coprime {m : ℕ} (hm : m.Coprime (prime v)) : 0 < m :=
  Nat.pos_of_ne_zero fun h ↦ by
    subst h
    exact (Fact.out : (prime v).Prime).one_lt.ne' ((Nat.coprime_zero_left _).1 hm)

theorem apply_of_pow_eq_one_of_prime_pow (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ) (r : ℤ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        RHDirect.CFT.LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    {n : ℕ} {y : AlgebraicClosure (v.adicCompletion ℚ)} (hy : y ^ (prime v ^ n) = 1) :
    τ y = y ^ (PadicInt.toZModPow n ((u⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v])).val := by
  obtain ⟨τ', hτ'⟩ := QuotientGroup.mk_surjective (RHDirect.CFT.LocalField.localReciprocityLimit ℚ_[prime v]
    (AlgebraicClosure ℚ_[prime v]) (Units.map (padicRingEquiv v).toRingHom.toMonoidHom x))
  have hmem := mem_maximalAbelianExtension_of_pow_eq_one v
    (pow_pos (Fact.out : (prime v).Prime).pos n) hy
  apply (closureEquiv v).injective
  rw [closureEquiv_apply_of_localReciprocityLimit v x hτ hτ' hmem, map_pow]
  exact RHDirect.CFT.LocalField.Padic.apply_of_pow_eq_one_of_prime_pow (prime v) _ u r
    (by rw [Units.coe_map]; exact hx) hτ' (by rw [← map_pow, hy, map_one])

theorem apply_of_pow_eq_one_of_coprime (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ) (r : ℕ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        RHDirect.CFT.LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    {m : ℕ} (hm : m.Coprime (prime v)) {y : AlgebraicClosure (v.adicCompletion ℚ)} (hy : y ^ m = 1) :
    τ y = y ^ (prime v ^ r) := by
  obtain ⟨τ', hτ'⟩ := QuotientGroup.mk_surjective (RHDirect.CFT.LocalField.localReciprocityLimit ℚ_[prime v]
    (AlgebraicClosure ℚ_[prime v]) (Units.map (padicRingEquiv v).toRingHom.toMonoidHom x))
  have hmem := mem_maximalAbelianExtension_of_pow_eq_one v (pos_of_coprime v hm) hy
  apply (closureEquiv v).injective
  rw [closureEquiv_apply_of_localReciprocityLimit v x hτ hτ' hmem, map_pow]
  exact RHDirect.CFT.LocalField.Padic.apply_of_pow_eq_one_of_coprime_of_nat (prime v) _ u r
    (by rw [Units.coe_map]; exact hx) hτ' hm (by rw [← map_pow, hy, map_one])

section Symbol

open SemiLocal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem residueEmbedding_localSymbol_apply (w : PlacesOver L v) (x : (v.adicCompletion ℚ)ˣ)
    {τ : AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ)}
    (hτ : (τ : TopologicalAbelianization (AlgebraicClosure (v.adicCompletion ℚ) ≃ₐ[v.adicCompletion ℚ]
      AlgebraicClosure (v.adicCompletion ℚ))) =
        RHDirect.CFT.LocalField.localReciprocityLimit (v.adicCompletion ℚ) (AlgebraicClosure (v.adicCompletion ℚ)) x)
    (l : L) :
    residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) (localSymbol L v x l)) =
      τ (residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) l)) := by
  rw [algebraMap_localSymbol_apply L v w x l]
  exact normResidueSymbol_spec _ hτ _

theorem localSymbol_apply_of_pow_eq_one_of_prime_pow (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ)
    (r : ℤ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v ^ n) = 1) :
    localSymbol L v x ζ = ζ ^ (PadicInt.toZModPow n ((u⁻¹ : ℤ_[prime v]ˣ) : ℤ_[prime v])).val := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion ℚ) x
  set i := residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
  have hj : Function.Injective fun l : L ↦ i (algebraMap L (w.1.adicCompletion L) l) :=
    i.toRingHom.injective.comp (algebraMap L (w.1.adicCompletion L)).injective
  apply hj
  simp only
  rw [residueEmbedding_localSymbol_apply v L w x hτ, map_pow, map_pow]
  exact apply_of_pow_eq_one_of_prime_pow v x u r hx hτ
    (by rw [← map_pow, ← map_pow, hζ, map_one, map_one])

theorem localSymbol_apply_of_pow_eq_one_of_coprime (x : (v.adicCompletion ℚ)ˣ) (u : ℤ_[prime v]ˣ)
    (r : ℕ)
    (hx : padicRingEquiv v x = ((u : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ r)
    {m : ℕ} (hm : m.Coprime (prime v)) {ζ : L} (hζ : ζ ^ m = 1) :
    localSymbol L v x ζ = ζ ^ (prime v ^ r) := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion ℚ) x
  set i := residueEmbedding (v.adicCompletion ℚ) (w.1.adicCompletion L)
  have hj : Function.Injective fun l : L ↦ i (algebraMap L (w.1.adicCompletion L) l) :=
    i.toRingHom.injective.comp (algebraMap L (w.1.adicCompletion L)).injective
  apply hj
  simp only
  rw [residueEmbedding_localSymbol_apply v L w x hτ, map_pow, map_pow]
  exact apply_of_pow_eq_one_of_coprime v x u r hx hτ hm
    (by rw [← map_pow, ← map_pow, hζ, map_one, map_one])

end Symbol

end RationalSymbol

end

end Sec3_08_NormResidueSymbol_RationalLocal

/-! ### 09_IdeleClassGroup.Invariants -/
section Sec3_09_IdeleClassGroup_Invariants

open NumberField IntermediateField RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

def ideleClassNorm {F E : FiniteSubfield} (h : F ≤ E) :
    IdeleClassGroup E.1 →* IdeleClassGroup F.1 :=
  letI := algebraOfLE h
  RHDirect.CFT_ProfiniteSemilocal.ideleClassNorm F.1 E.1

def galoisClosure (F : FiniteSubfield) : FiniteSubfield :=
  ⟨normalClosure ℚ F.1 ℚ̄, inferInstance⟩

theorem le_galoisClosure (F : FiniteSubfield) : F ≤ galoisClosure F :=
  show F.1 ≤ normalClosure ℚ F.1 ℚ̄ from IntermediateField.le_normalClosure F.1

instance (F : FiniteSubfield) : IsGalois ℚ (galoisClosure F).1 :=
  IsGalois.normalClosure ℚ F.1 ℚ̄

theorem index_fixingSubgroup (F : FiniteSubfield) :
    F.1.fixingSubgroup.index = Module.finrank ℚ F.1 :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (E' := ℚ̄) F.1).symm

instance (F : FiniteSubfield) : F.1.fixingSubgroup.FiniteIndex :=
  ⟨by rw [index_fixingSubgroup]; exact Module.finrank_pos.ne'⟩

theorem relIndex_fixingSubgroup {F E : FiniteSubfield} (h : F ≤ E) :
    letI := algebraOfLE h
    E.1.fixingSubgroup.relIndex F.1.fixingSubgroup = Module.finrank F.1 E.1 := by
  let := algebraOfLE h
  have : IsScalarTower ℚ F.1 E.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Module.Free F.1 E.1 := Module.Free.of_divisionRing _ _
  have : FiniteDimensional F.1 E.1 := FiniteDimensional.right ℚ F.1 E.1
  have h1 := Subgroup.relIndex_mul_index
    (IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h))
  rw [index_fixingSubgroup, index_fixingSubgroup, ← Module.finrank_mul_finrank ℚ F.1 E.1,
    mul_comm (Module.finrank ℚ F.1)] at h1
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

theorem fixingSubgroup_fixedField_openSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    (fixedField (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))).fixingSubgroup = U :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩

def ofOpenSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) : FiniteSubfield :=
  ⟨fixedField (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)), (InfiniteGalois.isOpen_iff_finite _).1 (by
    rw [fixingSubgroup_fixedField_openSubgroup]
    exact U.isOpen)⟩

theorem fixingSubgroup_ofOpenSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    (ofOpenSubgroup U).1.fixingSubgroup = U :=
  fixingSubgroup_fixedField_openSubgroup U

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield

theorem smul_of_eq_of_ideleClassEquiv {M : FiniteSubfield} (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ : M.1 ≃+* M.1)
    (h : ∀ x : M.1, σ x = τ x) (c : IdeleClassGroup M.1) :
    σ • of M c = of M (ideleClassEquiv τ c) :=
  (smul_of σ M c).trans (of_ideleClassEquiv_congr _ _ h c)

theorem fixedModule_fixingSubgroup (F : FiniteSubfield) :
    fixedModule IdeleClassLimit F.1.fixingSubgroup = (of F).range := by
  apply le_antisymm
  · intro z hz
    obtain ⟨E, c, rfl⟩ := exists_of z
    let S : FiniteSubfield := ⟨F.1 ⊔ E.1, inferInstance⟩
    let M := galoisClosure S
    have hFM : F ≤ M := le_trans (show F.1 ≤ F.1 ⊔ E.1 from le_sup_left) (le_galoisClosure S)
    have hEM : E ≤ M := le_trans (show E.1 ≤ F.1 ⊔ E.1 from le_sup_right) (le_galoisClosure S)
    rw [← of_ideleClassMap hEM c] at hz ⊢
    let := algebraOfLE hFM
    have : IsScalarTower ℚ F.1 M.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : IsGalois F.1 M.1 := IsGalois.tower_top_of_isGalois ℚ F.1 M.1
    have hfix : ∀ σ : M.1 ≃ₐ[F.1] M.1, σ • FiniteSubfield.ideleClassMap hEM c =
        FiniteSubfield.ideleClassMap hEM c := by
      intro σ
      let σ' : ℚ̄ ≃ₐ[ℚ] ℚ̄ := (σ.restrictScalars ℚ).liftNormal ℚ̄
      have hσ' : ∀ x : M.1, σ' x = σ x := fun x ↦ (σ.restrictScalars ℚ).liftNormal_commutes ℚ̄ x
      have hmem : σ' ∈ F.1.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        have h1 := hσ' (algebraMap F.1 M.1 ⟨x, hx⟩)
        rw [σ.commutes] at h1
        exact h1
      have h1 := hz σ' hmem
      rw [smul_of_eq_of_ideleClassEquiv σ' (σ : M.1 ≃+* M.1) hσ'] at h1
      exact of_injective M h1
    obtain ⟨d, hd⟩ :=
      (forall_smul_eq_iff_mem_range_ideleClassMap (K := F.1) (FiniteSubfield.ideleClassMap hEM c)).1
        hfix
    exact ⟨d, by rw [← hd]; exact (of_ideleClassMap hFM d).symm⟩
  · rintro _ ⟨c, rfl⟩ σ hσ
    exact smul_of_eq_of_mem_fixingSubgroup hσ c

theorem fixedModule_openSubgroup (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = (of (ofOpenSubgroup U)).range := by
  have h := fixedModule_fixingSubgroup (ofOpenSubgroup U)
  rwa [fixingSubgroup_ofOpenSubgroup] at h

def fixedEquiv (F : FiniteSubfield) :
    IdeleClassGroup F.1 ≃* fixedModule IdeleClassLimit F.1.fixingSubgroup :=
  (MonoidHom.ofInjective (of_injective F)).trans
    (MulEquiv.subgroupCongr (fixedModule_fixingSubgroup F).symm)

@[simp]
theorem coe_fixedEquiv (F : FiniteSubfield) (c : IdeleClassGroup F.1) :
    (fixedEquiv F c : IdeleClassLimit) = of F c :=
  rfl

theorem norm_fixedEquiv {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup E.1) :
    norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup (fixedEquiv E c) =
      fixedEquiv F (FiniteSubfield.ideleClassNorm h c) := by
  classical
  set K := F.1.fixingSubgroup
  set L := E.1.fixingSubgroup
  let M := galoisClosure E
  have hEM : E ≤ M := le_galoisClosure E
  have hFM : F ≤ M := le_trans h hEM
  let iFE := algebraOfLE h
  let iEM := algebraOfLE hEM
  let iFM := algebraOfLE hFM
  have : IsScalarTower F.1 E.1 M.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ι := K ⧸ L.subgroupOf K
  let _ : Fintype ι := Fintype.ofFinite ι
  let ρ : ι → (M.1 ≃ₐ[F.1] M.1) := fun q ↦
    AlgEquiv.ofRingEquiv (f := ((((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal M.1 : M.1 ≃ₐ[ℚ] M.1) :
      M.1 ≃+* M.1)) (fun x ↦ by
        apply Subtype.ext
        have h1 := AlgEquiv.restrictNormal_commutes ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) M.1
          (algebraMap F.1 M.1 x)
        refine h1.trans ?_
        exact (IntermediateField.mem_fixingSubgroup_iff F.1 _).1 (q.out : K).2 x x.2)
  have hρ : ∀ (q : ι) (x : M.1), ((ρ q x : M.1) : ℚ̄) = ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x :=
    fun q x ↦ AlgEquiv.restrictNormal_commutes ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) M.1 x
  have hinj : Function.Injective fun q ↦
      (ρ q : M.1 →ₐ[F.1] M.1).comp (IsScalarTower.toAlgHom F.1 E.1 M.1) := by
    intro q q' hqq'
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 := congrArg (fun f : E.1 →ₐ[F.1] M.1 ↦ ((f ⟨x, hx⟩ : M.1) : ℚ̄)) hqq'
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom'] at h1
    rw [hρ, hρ] at h1
    change ((q.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x = ((q'.out : K) : ℚ̄ ≃ₐ[ℚ] ℚ̄) x at h1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, ← h1, ← AlgEquiv.mul_apply,
      inv_mul_cancel, AlgEquiv.one_apply]
  have hcard : Fintype.card ι = Module.finrank F.1 E.1 := by
    rw [← relIndex_fixingSubgroup h, ← Nat.card_eq_fintype_card]
    rfl
  have hq : ∀ q : ι, cosetSMul IdeleClassLimit K L (fixedEquiv E c) q =
      of M (ρ q • FiniteSubfield.ideleClassMap hEM c) := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rw [cosetSMul_mk, coe_fixedEquiv, ← of_ideleClassMap hEM c,
      smul_of_eq_of_ideleClassEquiv _ (ρ q : M.1 ≃+* M.1) (fun x ↦ (hρ q x).symm)]
    rfl
  apply Subtype.ext
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun q _ ↦ hq q, ← map_prod,
    coe_fixedEquiv]
  have h2 := ideleClassMap_ideleClassNorm_eq_prod ρ hinj hcard c
  change _ = of F (RHDirect.CFT_ProfiniteSemilocal.ideleClassNorm F.1 E.1 c)
  rw [← of_ideleClassMap hFM]
  exact congrArg (of M) h2.symm

instance normal_range_ideleClassNorm {F E : FiniteSubfield} (h : F ≤ E) :
    (FiniteSubfield.ideleClassNorm h).range.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def tateZeroEquiv {F E : FiniteSubfield} (h : F ≤ E) :
    tateZero IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup ≃*
      IdeleClassGroup F.1 ⧸ (FiniteSubfield.ideleClassNorm h).range :=
  QuotientGroup.congr (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).range
    (FiniteSubfield.ideleClassNorm h).range (fixedEquiv F).symm (by
    ext c
    simp only [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      obtain ⟨d, rfl⟩ := (fixedEquiv E).surjective a
      refine ⟨d, ?_⟩
      rw [norm_fixedEquiv h]
      exact ((fixedEquiv F).symm_apply_apply _).symm
    · rintro ⟨d, rfl⟩
      refine ⟨_, ⟨fixedEquiv E d, rfl⟩, ?_⟩
      rw [norm_fixedEquiv h]
      exact (fixedEquiv F).symm_apply_apply _)

theorem tateZeroEquiv_mk {F E : FiniteSubfield} (h : F ≤ E) (c : IdeleClassGroup F.1) :
    tateZeroEquiv h (fixedEquiv F c : tateZero IdeleClassLimit F.1.fixingSubgroup
      E.1.fixingSubgroup) = (c : IdeleClassGroup F.1 ⧸ (FiniteSubfield.ideleClassNorm h).range) := by
  rw [tateZeroEquiv, QuotientGroup.congr_mk]
  exact congrArg _ ((fixedEquiv F).symm_apply_apply c)

end IdeleClassLimit

end

end Sec3_09_IdeleClassGroup_Invariants

/-! ### 10_NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol -/
section Sec3_10_NormResidueSymbol_RangeIdeleNormLeKerIdeleSymbol

open IsDedekindDomain NumberField IdeleGroup

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

abbrev galCommGroup : CommGroup (L ≃ₐ[K] L) :=
  { toGroup := (inferInstance : Group (L ≃ₐ[K] L)), mul_comm := mul_comm' }

attribute [local instance] galCommGroup

def ideleSymbol : IdeleGroup K →* (L ≃ₐ[K] L) :=
  IdeleMap.ideleMap (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)

variable {K}

theorem ideleSymbol_apply (x : IdeleGroup K) :
    ideleSymbol K L x = (∏ᶠ v, localSymbol L v (finiteProj v x)) *
      ∏ w, infiniteLocalSymbol L w (infiniteProj w x) :=
  IdeleMap.ideleMap_apply (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) x

theorem hasFiniteMulSupport_localSymbol (x : IdeleGroup K) :
    Function.HasFiniteMulSupport fun v ↦ localSymbol L v (finiteProj v x) :=
  IdeleMap.hasFiniteMulSupport (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v)
    (eventually_units_le_ker_localSymbol L) x

@[simp]
theorem ideleSymbol_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ideleSymbol K L (finiteEmbedding v a) = localSymbol L v a :=
  IdeleMap.ideleMap_finiteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) v a

@[simp]
theorem ideleSymbol_infiniteEmbedding (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ideleSymbol K L (infiniteEmbedding w a) = infiniteLocalSymbol L w a :=
  IdeleMap.ideleMap_infiniteEmbedding (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) w a

theorem continuous_ideleSymbol : Continuous (ideleSymbol K L) :=
  IdeleMap.continuous_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w)

theorem isOpen_ker_ideleSymbol : IsOpen ((ideleSymbol K L).ker : Set (IdeleGroup K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete _).preimage (continuous_ideleSymbol L)

theorem eq_ideleSymbol {ψ : IdeleGroup K →* (L ≃ₐ[K] L)} (hψ : Continuous ψ)
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = localSymbol L v a)
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = infiniteLocalSymbol L w a) :
    ψ = ideleSymbol K L :=
  IdeleMap.eq_ideleMap (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L) (fun v ↦ continuous_localSymbol L v)
    (fun w ↦ continuous_infiniteLocalSymbol L w) hψ
    (fun v ↦ MonoidHom.ext (hfin v)) (fun w ↦ MonoidHom.ext (hinf w))

theorem range_ideleNorm_le_ker_ideleSymbol : (ideleNorm K L).range ≤ (ideleSymbol K L).ker := by
  intro x hx
  obtain ⟨hf, hi⟩ := (IdeleNorm.mem_range_ideleNorm_iff_forall L x).1 hx
  exact IdeleMap.ideleMap_eq_one_of_forall_mem (G := L ≃ₐ[K] L) (fun v ↦ localSymbol L v) (fun w ↦ infiniteLocalSymbol L w)
    (eventually_units_le_ker_localSymbol L)
    (fun v ↦ (IdeleNorm.finiteLocalNorm L v).range)
    (fun w ↦ (IdeleNorm.infiniteLocalNorm L w).range)
    (fun v ↦ range_finiteLocalNorm_le_ker_localSymbol L v)
    (fun w ↦ range_infiniteLocalNorm_le_ker_infiniteLocalSymbol L w) hf hi

@[simp]
theorem ideleSymbol_ideleNorm (y : IdeleGroup L) : ideleSymbol K L (ideleNorm K L y) = 1 :=
  range_ideleNorm_le_ker_ideleSymbol L ⟨y, rfl⟩

end

end Sec3_10_NormResidueSymbol_RangeIdeleNormLeKerIdeleSymbol

/-! ### 11_IdeleClassGroup.InvariantsGalois -/
section Sec3_11_IdeleClassGroup_InvariantsGalois

open NumberField IntermediateField RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace FiniteSubfield

theorem ofOpenSubgroup_le {U U' : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} (h : U' ≤ U) :
    ofOpenSubgroup U ≤ ofOpenSubgroup U' :=
  show fixedField (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ≤ fixedField (U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) from
    fun x hx ↦ (mem_fixedField_iff _ x).2 fun g hg ↦ (mem_fixedField_iff _ x).1 hx g (h hg)

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield

theorem coe_norm_of_eq {K L : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} [(L.subgroupOf K).FiniteIndex]
    {F E : FiniteSubfield} (h : F ≤ E) (hK : K = F.1.fixingSubgroup) (hL : L = E.1.fixingSubgroup)
    (c : IdeleClassGroup E.1) (hc : of E c ∈ fixedModule IdeleClassLimit L) :
    (norm IdeleClassLimit K L ⟨of E c, hc⟩ : IdeleClassLimit) =
      of F (FiniteSubfield.ideleClassNorm h c) := by
  subst hK hL
  exact congrArg Subtype.val (norm_fixedEquiv h c)

theorem coe_norm_openSubgroup {U U' : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} (hUU' : U' ≤ U)
    (c : IdeleClassGroup (ofOpenSubgroup U').1)
    (hc : of (ofOpenSubgroup U') c ∈ fixedModule IdeleClassLimit (U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) :
    (norm IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (U' : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
      ⟨of (ofOpenSubgroup U') c, hc⟩ : IdeleClassLimit) =
      of (ofOpenSubgroup U) (FiniteSubfield.ideleClassNorm (ofOpenSubgroup_le hUU') c) :=
  coe_norm_of_eq (ofOpenSubgroup_le hUU') (fixingSubgroup_ofOpenSubgroup U).symm
    (fixingSubgroup_ofOpenSubgroup U').symm c hc

end IdeleClassLimit

namespace FiniteSubfield

instance algebraOfFact {F E : FiniteSubfield} [h : Fact (F ≤ E)] : Algebra F.1 E.1 :=
  algebraOfLE h.out

instance {F E : FiniteSubfield} [Fact (F ≤ E)] : IsScalarTower ℚ F.1 E.1 :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

instance {F E : FiniteSubfield} [Fact (F ≤ E)] : FiniteDimensional F.1 E.1 :=
  FiniteDimensional.right ℚ F.1 E.1

theorem apply_mem_of_normal {F E : FiniteSubfield} (h : F ≤ E)
    [hN : (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal] {g : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (hg : g ∈ F.1.fixingSubgroup) {x : ℚ̄} (hx : x ∈ E.1) : g x ∈ E.1 := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup E.1, mem_fixedField_iff]
  intro l hl
  have hc : g⁻¹ * l * g ∈ E.1.fixingSubgroup := by
    have h1 := hN.conj_mem ⟨l, IntermediateField.fixingSubgroup_le (show F.1 ≤ E.1 from h) hl⟩
      (by rwa [Subgroup.mem_subgroupOf]) (⟨g, hg⟩ : F.1.fixingSubgroup)⁻¹
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hc x hx
  calc l (g x) = g ((g⁻¹ * l * g) x) := by
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g, mul_inv_cancel,
          AlgEquiv.one_apply]
    _ = g x := by rw [h2]

variable {F E : FiniteSubfield} [hFE : Fact (F ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]

def restrictHom : F.1.fixingSubgroup →* (E.1 ≃ₐ[F.1] E.1) where
  toFun g := AlgEquiv.ofRingEquiv (f :=
      { toFun := fun x ↦ ⟨(g : ℚ̄ ≃ₐ[ℚ] ℚ̄) x, apply_mem_of_normal hFE.out g.2 x.2⟩
        invFun := fun x ↦ ⟨(g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ x, apply_mem_of_normal hFE.out (inv_mem g.2) x.2⟩
        left_inv := fun x ↦ Subtype.ext (by
          change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) x) = x
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply])
        right_inv := fun x ↦ Subtype.ext (by
          change (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ x) = x
          rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])
        map_mul' := fun x y ↦ Subtype.ext (map_mul (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄) y)
        map_add' := fun x y ↦ Subtype.ext (map_add (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄) y) })
      (fun x ↦ Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff F.1 _).1 g.2 x x.2))
  map_one' := AlgEquiv.ext fun _ ↦ Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ Subtype.ext rfl

@[simp]
theorem coe_restrictHom_apply (g : F.1.fixingSubgroup) (x : E.1) :
    ((restrictHom g x : E.1) : ℚ̄) = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) x :=
  rfl

theorem restrictHom_surjective :
    Function.Surjective (restrictHom : F.1.fixingSubgroup →* (E.1 ≃ₐ[F.1] E.1)) := by
  intro σ
  let σ' : ℚ̄ ≃ₐ[ℚ] ℚ̄ := (σ.restrictScalars ℚ).liftNormal ℚ̄
  have hσ' : ∀ x : E.1, σ' x = σ x := fun x ↦ (σ.restrictScalars ℚ).liftNormal_commutes ℚ̄ x
  have hmem : σ' ∈ F.1.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 := hσ' (algebraMap F.1 E.1 ⟨x, hx⟩)
    rw [σ.commutes] at h1
    exact h1
  exact ⟨⟨σ', hmem⟩, AlgEquiv.ext fun x ↦ Subtype.ext (hσ' x)⟩

theorem ker_restrictHom :
    (restrictHom : F.1.fixingSubgroup →* (E.1 ≃ₐ[F.1] E.1)).ker =
      E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    exact congrArg (fun σ : E.1 ≃ₐ[F.1] E.1 ↦ ((σ ⟨x, hx⟩ : E.1) : ℚ̄)) hg
  · intro hg
    exact AlgEquiv.ext fun x ↦ Subtype.ext (hg x x.2)

theorem isGalois_of_normal : IsGalois F.1 E.1 := by
  apply IsGalois.of_card_aut_eq_finrank
  have h1 : E.1.fixingSubgroup.relIndex F.1.fixingSubgroup = Module.finrank F.1 E.1 :=
    relIndex_fixingSubgroup hFE.out
  rw [← h1, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (restrictHom_surjective (F := F) (E := E))).toEquiv, ker_restrictHom]
  rfl

end FiniteSubfield

namespace IdeleClassLimit

open FiniteSubfield RHDirect.CFT.LocalField

variable {F E : FiniteSubfield} [hFE : Fact (F ≤ E)]
  [(E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup).Normal]

theorem smul_of_of_normal (g : F.1.fixingSubgroup) (c : IdeleClassGroup E.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • of E c = of E (restrictHom (E := E) g • c) :=
  smul_of_eq_of_ideleClassEquiv _ ((restrictHom (E := E) g : E.1 ≃ₐ[F.1] E.1) : E.1 ≃+* E.1)
    (fun _ ↦ rfl) c

theorem mem_invariants_iff (c : IdeleClassGroup E.1) :
    c ∈ invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) ↔
      of E c ∈ fixedModule IdeleClassLimit F.1.fixingSubgroup := by
  constructor
  · intro hc g hg
    exact (smul_of_of_normal ⟨g, hg⟩ c).trans (congrArg _ (hc _))
  · intro hc σ
    obtain ⟨g, rfl⟩ := restrictHom_surjective σ
    apply of_injective E
    rw [← smul_of_of_normal g]
    exact hc g g.2

def invariantsEquiv :
    invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) ≃*
      fixedModule IdeleClassLimit F.1.fixingSubgroup :=
  (MonoidHom.ofInjective (f := (of E).comp (invariants (E.1 ≃ₐ[F.1] E.1) _).subtype)
    ((of_injective E).comp Subtype.val_injective)).trans (MulEquiv.subgroupCongr (by
      ext a
      constructor
      · rintro ⟨c, rfl⟩
        exact (mem_invariants_iff (c : IdeleClassGroup E.1)).1 c.2
      · intro ha
        have ha' := fixedModule_anti (IntermediateField.fixingSubgroup_le
          (show F.1 ≤ E.1 from hFE.out)) ha
        rw [fixedModule_fixingSubgroup] at ha'
        obtain ⟨c, rfl⟩ := ha'
        exact ⟨⟨c, (mem_invariants_iff c).2 ha⟩, rfl⟩))

@[simp]
theorem coe_invariantsEquiv (c : invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)) :
    (invariantsEquiv c : IdeleClassLimit) = of E c :=
  rfl

theorem of_tateNorm (c : IdeleClassGroup E.1) :
    of E (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) c) =
      of F (FiniteSubfield.ideleClassNorm hFE.out c) := by
  have := isGalois_of_normal (F := F) (E := E)
  rw [tateNorm_apply, ← ideleClassMap_ideleClassNorm]
  exact of_ideleClassMap hFE.out _

theorem tateNorm_eq_one_iff (c : IdeleClassGroup E.1) :
    tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) c = 1 ↔
      norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup (fixedEquiv E c) = 1 := by
  constructor
  · intro h1
    apply Subtype.ext
    rw [norm_fixedEquiv hFE.out, coe_fixedEquiv, ← of_tateNorm, h1, map_one]
    rfl
  · intro h1
    apply of_injective E
    rw [of_tateNorm, map_one, ← coe_fixedEquiv, ← norm_fixedEquiv hFE.out, h1]
    rfl

theorem map_augmentation :
    (RHDirect.CFT.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).map (of E) =
      RHDirect.CFT_AbstractLocalReciprocity.augmentation IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup := by
  rw [RHDirect.CFT.LocalField.augmentation, MonoidHom.map_closure, RHDirect.CFT_AbstractLocalReciprocity.augmentation]
  congr 1
  ext a
  constructor
  · rintro ⟨_, ⟨σ, c, rfl⟩, rfl⟩
    obtain ⟨g, rfl⟩ := restrictHom_surjective σ
    refine ⟨g, g.2, of E c, ?_, ?_⟩
    · rw [fixedModule_fixingSubgroup]
      exact ⟨c, rfl⟩
    · rw [map_div, smul_of_of_normal g c]
  · rintro ⟨g, hg, a, ha, rfl⟩
    rw [fixedModule_fixingSubgroup] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨restrictHom ⟨g, hg⟩ • c / c, ⟨_, c, rfl⟩, by
      rw [map_div, ← smul_of_of_normal ⟨g, hg⟩ c]⟩

theorem coe_invariantsEquiv_tateNorm (c : IdeleClassGroup E.1) :
    (invariantsEquiv ⟨tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) c,
      tateNorm_mem_invariants c⟩ : IdeleClassLimit) =
      norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup (fixedEquiv E c) := by
  rw [coe_invariantsEquiv, norm_fixedEquiv hFE.out, coe_fixedEquiv]
  exact of_tateNorm c

theorem map_range_tateNorm :
    ((tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).range.subgroupOf
      (invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1))).map
        (invariantsEquiv (F := F) (E := E) : invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) →*
          fixedModule IdeleClassLimit F.1.fixingSubgroup) =
      (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).range := by
  apply le_antisymm
  · rintro _ ⟨⟨y, hy⟩, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨fixedEquiv E c, Subtype.ext (coe_invariantsEquiv_tateNorm c).symm⟩
  · rintro _ ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (fixedEquiv E).surjective b
    exact ⟨⟨tateNorm _ _ c, tateNorm_mem_invariants c⟩, ⟨c, rfl⟩,
      Subtype.ext (coe_invariantsEquiv_tateNorm c)⟩

def tateZeroEquivGalois :
    tateZero IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup ≃*
      TateZero (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) :=
  haveI : ((tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).range.subgroupOf
      (invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1))).Normal :=
    ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  (QuotientGroup.congr ((tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).range.subgroupOf
      (invariants (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)))
    (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).range invariantsEquiv
    map_range_tateNorm).symm

def kerEquiv :
    (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker ≃*
      (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker :=
  ((fixedEquiv E).subgroupMap _).trans (MulEquiv.subgroupCongr (by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      exact (tateNorm_eq_one_iff c).1 hc
    · intro a ha
      obtain ⟨c, rfl⟩ := (fixedEquiv E).surjective a
      exact ⟨c, (tateNorm_eq_one_iff c).2 ha, rfl⟩))

@[simp]
theorem coe_coe_kerEquiv (c : (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker) :
    ((kerEquiv c : fixedModule IdeleClassLimit E.1.fixingSubgroup) : IdeleClassLimit) = of E c :=
  rfl

theorem map_augmentation_subgroupOf :
    ((RHDirect.CFT.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).subgroupOf
      (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker).map
        (kerEquiv (F := F) (E := E) : (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker →*
          (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker) =
      (RHDirect.CFT_AbstractLocalReciprocity.augmentation IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).comap
        ((fixedModule IdeleClassLimit E.1.fixingSubgroup).subtype.comp
          (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker.subtype) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap]
    change of E (x : IdeleClassGroup E.1) ∈ _
    rw [← map_augmentation]
    exact Subgroup.mem_map_of_mem _ hx
  · intro y hy
    obtain ⟨x, rfl⟩ := kerEquiv.surjective y
    rw [Subgroup.mem_comap] at hy
    change of E (x : IdeleClassGroup E.1) ∈ _ at hy
    rw [← map_augmentation, Subgroup.mem_map_iff_mem (of_injective E)] at hy
    exact ⟨x, Subgroup.mem_subgroupOf.2 hy, rfl⟩

def tateNegOneEquivGalois :
    tateNegOne IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup ≃*
      TateNegOne (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1) :=
  haveI : ((RHDirect.CFT.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).subgroupOf
      (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker).Normal :=
    ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  (QuotientGroup.congr ((RHDirect.CFT.LocalField.augmentation (E.1 ≃ₐ[F.1] E.1)
      (IdeleClassGroup E.1)).subgroupOf (tateNorm (E.1 ≃ₐ[F.1] E.1) (IdeleClassGroup E.1)).ker)
    ((RHDirect.CFT_AbstractLocalReciprocity.augmentation IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).comap
      ((fixedModule IdeleClassLimit E.1.fixingSubgroup).subtype.comp
        (norm IdeleClassLimit F.1.fixingSubgroup E.1.fixingSubgroup).ker.subtype))
    kerEquiv map_augmentation_subgroupOf).symm

end IdeleClassLimit

end

end Sec3_11_IdeleClassGroup_InvariantsGalois

/-! ### 12_NormResidueSymbol.FunctorialFinite -/
section Sec3_12_NormResidueSymbol_FunctorialFinite

open IsDedekindDomain NumberField SemiLocal AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_finiteEmbedding (v' : HeightOneSpectrum (𝓞 K')) (a : (v'.adicCompletion K')ˣ) :
    ideleNorm K K' (finiteEmbedding v' a) =
      finiteEmbedding (below K v')
        (RHDirect.CFT.LocalField.normUnits ((below K v').adicCompletion K) (v'.adicCompletion K') a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_finiteEmbedding]
    exact (Finset.prod_eq_one fun _ _ ↦ map_one _)
  · rw [ideleNorm_snd]
    simp only [coe_finiteEmbedding]
    by_cases hv : v = below K v'
    · subst hv
      rw [Finset.prod_eq_single (⟨v', inferInstance⟩ : PlacesOver K' (below K v')),
        finiteAdeleSingle_apply_self, finiteAdeleSingle_apply_self, RHDirect.CFT.LocalField.coe_normUnits]
      · intro w _ hw
        rw [finiteAdeleSingle_apply_of_ne (fun h ↦ hw (Subtype.ext h)), map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [finiteAdeleSingle_apply_of_ne hv]
      refine Finset.prod_eq_one fun w _ ↦ ?_
      have hw : w.1 ≠ v' := by
        rintro h
        apply hv
        rw [← h]
        exact ((below_eq_iff w.1 v).2 w.2).symm
      rw [finiteAdeleSingle_apply_of_ne hw, map_one]

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

omit [NumberField K] [NumberField K'] [NumberField L'] in

theorem liesOver_trans_of_liesOver (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 K'))
    (u' : HeightOneSpectrum (𝓞 L')) [v'.asIdeal.LiesOver v.asIdeal]
    [u'.asIdeal.LiesOver v'.asIdeal] : u'.asIdeal.LiesOver v.asIdeal :=
  (below_eq_iff u' v).1 (by
    rw [← below_below (L := K'), (below_eq_iff u' v').2 inferInstance,
      (below_eq_iff v' v).2 inferInstance])

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_localSymbol_norm (v : HeightOneSpectrum (𝓞 K))
    (v' : HeightOneSpectrum (𝓞 K')) [v'.asIdeal.LiesOver v.asIdeal] (a : (v'.adicCompletion K')ˣ) :
    ((localSymbol L' v' a).restrictScalars K).restrictNormal L =
      localSymbol L v (RHDirect.CFT.LocalField.normUnits (v.adicCompletion K) (v'.adicCompletion K') a) := by
  obtain ⟨u'⟩ := nonempty_placesOver L' v'
  have : u'.1.asIdeal.LiesOver v.asIdeal := liesOver_trans_of_liesOver v v' u'.1
  have hu : (below L u'.1).asIdeal.LiesOver v.asIdeal :=
    (below_eq_iff _ v).1 (by rw [below_below, (below_eq_iff u'.1 v).2 inferInstance])
  let u : PlacesOver L v := ⟨below L u'.1, hu⟩
  have : u'.1.asIdeal.LiesOver u.1.asIdeal := liesOver_below (K := L) u'.1
  have : IsScalarTower (v.adicCompletion K) (v'.adicCompletion K') (u'.1.adicCompletion L') :=
    .of_algebraMap_eq fun r ↦ (completionMap_completionMap v v' u'.1 r).symm
  have := isMulCommutative_gal_adicCompletion L' v' u'
  have := isMulCommutative_gal_adicCompletion L v u
  let j : u.1.adicCompletion L →ₐ[v.adicCompletion K] u'.1.adicCompletion L' :=
    { completionMap u.1 u'.1 with
      commutes' := fun r ↦ completionMap_completionMap v u.1 u'.1 r }
  have hj : ∀ m : L, j (algebraMap L (u.1.adicCompletion L) m) =
      algebraMap L' (u'.1.adicCompletion L') (algebraMap L L' m) := fun m ↦ by
    change completionMap u.1 u'.1 _ = _
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply L L' (u'.1.adicCompletion L')]
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply]
  apply (algebraMap L' (u'.1.adicCompletion L')).injective
  rw [algebraMap_localSymbol_apply L' v' u', ← hj, ← hj, algebraMap_localSymbol_apply L v u,
    normResidueSymbol_norm j]

end

end Sec3_12_NormResidueSymbol_FunctorialFinite

/-! ### 13_NormResidueSymbol.RationalDiagonal -/
section Sec3_13_NormResidueSymbol_RationalDiagonal

open IsDedekindDomain NumberField IdeleGroup

noncomputable section

namespace RationalSymbol

attribute [local instance] galCommGroup

section Infinite

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

theorem conjAt_apply_of_pow_eq_one (w : InfinitePlace L) {ζ : L} {n : ℕ} (hn : n ≠ 0)
    (hζ : ζ ^ n = 1) : conjAt ℚ w ζ = ζ⁻¹ := by
  have hc : ComplexEmbedding.IsConj w.embedding (conjAt ℚ w) := by
    by_cases hw : w.IsReal
    · rw [conjAt_of_isReal hw]
      exact ComplexEmbedding.isConj_one_iff.2 (InfinitePlace.isReal_iff.1 hw)
    · exact isConj_conjAt (InfinitePlace.isRamified_iff.2
        ⟨InfinitePlace.not_isReal_iff_isComplex.1 hw, RationalIdeles.isReal_infinitePlace _⟩)
  apply w.embedding.injective
  rw [hc.eq, map_inv₀, ← starRingEnd_apply, ← Complex.inv_eq_conj]
  exact Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) hn

variable (L) [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem infiniteLocalSymbol_apply_of_pow_eq_one (w : InfinitePlace ℚ) (x : w.Completionˣ) {ζ : L}
    {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    infiniteLocalSymbol L w x ζ =
      if InfinitePlace.Completion.extensionEmbeddingOfIsReal
        (RationalIdeles.isReal_infinitePlace w) x < 0 then ζ⁻¹ else ζ := by
  obtain ⟨w'⟩ := IdeleNorm.nonempty_infinitePlacesOver L w
  rw [infiniteLocalSymbol_apply L w (RationalIdeles.isReal_infinitePlace w) w' x]
  split_ifs
  · exact conjAt_apply_of_pow_eq_one _ hn hζ
  · rfl

theorem extensionEmbeddingOfIsReal_infiniteProj (w : InfinitePlace ℚ) (y : IdeleGroup ℚ) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal (RationalIdeles.isReal_infinitePlace w)
      (infiniteProj w y : w.Completion) = (RationalIdeles.realPart y : ℝ) := by
  obtain rfl : w = default := Subsingleton.elim _ _
  rw [RationalIdeles.coe_realPart, RationalIdeles.realEquiv_apply]
  rfl

end Infinite

theorem exists_finprod_eq_prod_mul {ι G : Type*} [CommGroup G] (H : Subgroup G) {f : ι → G}
    (hf : (Function.mulSupport f).Finite) (T : Finset ι) (hT : ∀ i ∉ T, f i ∈ H) :
    ∃ h ∈ H, ∏ᶠ i, f i = (∏ i ∈ T, f i) * h := by
  refine ⟨∏ᶠ i ∈ Set.univ \ (T : Set ι), f i, finprod_mem_induction (· ∈ H) H.one_mem
    (fun _ _ ↦ H.mul_mem) (fun i hi ↦ hT i hi.2), ?_⟩
  rw [← finprod_mem_coe_finset, finprod_mem_mul_sdiff' (Set.subset_univ _) (by simpa using hf),
    finprod_mem_univ]

section Symbol

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem ideleSymbol_apply_eq_of_forall_notMem (y : IdeleGroup ℚ) (ζ : L)
    (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hT : ∀ v ∉ T, localSymbol L v (finiteProj v y) ζ = ζ) :
    ideleSymbol ℚ L y ζ = (∏ v ∈ T, localSymbol L v (finiteProj v y))
      (infiniteLocalSymbol L default (infiniteProj default y) ζ) := by
  obtain ⟨h, hh, heq⟩ := exists_finprod_eq_prod_mul (MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ)
    (hasFiniteMulSupport_localSymbol L y) T fun v hv ↦ by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact hT v hv
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hh
  rw [ideleSymbol_apply, heq, Fintype.prod_subsingleton _ default, mul_right_comm,
    AlgEquiv.mul_apply, hh, AlgEquiv.mul_apply]

end Symbol

section Generators

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem padicRingEquiv_finiteProj_diagonal (v : HeightOneSpectrum (𝓞 ℚ)) (a : ℚˣ) :
    padicRingEquiv v (finiteProj v (diagonal ℚ a) : v.adicCompletion ℚ) = ((a : ℚ) : ℚ_[prime v]) := by
  let f : ℚ →+* ℚ_[prime v] := (padicRingEquiv v).toRingHom.comp
    (@algebraMap ℚ (v.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v))
  exact eq_ratCast f (a : ℚ)

theorem prime_injective : Function.Injective prime := fun _ _ h ↦
  Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

theorem coprime_prime {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ v') :
    (prime v).Coprime (prime v') :=
  (Nat.coprime_primes Fact.out Fact.out).2 fun e ↦ h (prime_injective e)

def primeUnit {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ v') : ℤ_[prime v]ˣ :=
  (PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 (coprime_prime h))).unit

theorem coe_primeUnit {v v' : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ v') :
    ((primeUnit h : ℤ_[prime v]ˣ) : ℤ_[prime v]) = (prime v' : ℤ_[prime v]) := by
  simp [primeUnit]

def primeRat (v : HeightOneSpectrum (𝓞 ℚ)) : ℚˣ :=
  Units.mk0 (prime v : ℚ) (Nat.cast_ne_zero.2 (Fact.out : (prime v).Prime).ne_zero)

def placeOf (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm p

theorem prime_placeOf (p : Nat.Primes) : prime (placeOf p) = p :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)

@[simp]
theorem coe_primeRat (v : HeightOneSpectrum (𝓞 ℚ)) : ((primeRat v : ℚˣ) : ℚ) = (prime v : ℚ) :=
  rfl

variable {L}

theorem localSymbol_neg_one_of_ne {v v₀ : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ v₀) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v (finiteProj v (diagonal ℚ (-1))) ζ = ζ := by
  rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (-1) 0
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp) (Nat.Coprime.pow_left n (coprime_prime hv.symm)) hζ,
    pow_zero, pow_one]

theorem localSymbol_neg_one_self (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v₀ (finiteProj v₀ (diagonal ℚ (-1))) ζ = ζ⁻¹ := by
  rw [localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (-1) 0
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp) hζ]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, RHDirect.CFT.LocalField.pow_eq_pow_of_natCast_eq hζ (b := 0) (by simp [ZMod.natCast_val]),
    pow_zero]

theorem localSymbol_prime_of_ne {v v₀ v' : HeightOneSpectrum (𝓞 ℚ)} (hv₀ : v ≠ v₀) (hv' : v ≠ v')
    {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v (finiteProj v (diagonal ℚ (primeRat v'))) ζ = ζ := by
  rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (primeUnit hv') 0
    (by rw [padicRingEquiv_finiteProj_diagonal, coe_primeUnit]; simp)
    (Nat.Coprime.pow_left n (coprime_prime hv₀.symm)) hζ, pow_zero, pow_one]

theorem localSymbol_prime_self (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v₀ (finiteProj v₀ (diagonal ℚ (primeRat v₀))) ζ = ζ := by
  rw [localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ 1 1
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp) hζ]
  conv_rhs => rw [← pow_one ζ]
  exact RHDirect.CFT.LocalField.pow_eq_pow_of_natCast_eq hζ (by simp [ZMod.natCast_val])

theorem localSymbol_prime_at_other {v₀ v' : HeightOneSpectrum (𝓞 ℚ)} (h : v₀ ≠ v') {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v₀ (finiteProj v₀ (diagonal ℚ (primeRat v'))) ζ =
      ζ ^ (PadicInt.toZModPow n (((primeUnit h)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val :=
  localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (primeUnit h) 0
    (by rw [padicRingEquiv_finiteProj_diagonal, coe_primeUnit]; simp) hζ

theorem localSymbol_prime_at_self {v₀ v' : HeightOneSpectrum (𝓞 ℚ)} (h : v₀ ≠ v') {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    localSymbol L v' (finiteProj v' (diagonal ℚ (primeRat v'))) ζ = ζ ^ prime v' := by
  rw [localSymbol_apply_of_pow_eq_one_of_coprime v' L _ 1 1
    (by rw [padicRingEquiv_finiteProj_diagonal]; simp)
    (Nat.Coprime.pow_left n (coprime_prime h)) hζ, pow_one]

variable (L)

theorem ideleSymbol_diagonal_neg_one (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) : ideleSymbol ℚ L (diagonal ℚ (-1)) ζ = ζ := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀}
      (fun v hv ↦ localSymbol_neg_one_of_ne (by simpa using hv) hζ),
    Finset.prod_singleton, infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ,
    extensionEmbeddingOfIsReal_infiniteProj, if_pos (by rw [RationalIdeles.realPart_diagonal]; simp),
    map_inv₀, localSymbol_neg_one_self v₀ hζ, inv_inv]

theorem ideleSymbol_diagonal_prime (v₀ v' : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L}
    (hζ : ζ ^ (prime v₀ ^ n) = 1) : ideleSymbol ℚ L (diagonal ℚ (primeRat v')) ζ = ζ := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  have hinf : infiniteLocalSymbol L default (infiniteProj default (diagonal ℚ (primeRat v'))) ζ =
      ζ := by
    rw [infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ, extensionEmbeddingOfIsReal_infiniteProj,
      if_neg (by rw [RationalIdeles.realPart_diagonal]; simp)]
  by_cases h : v₀ = v'
  · subst h
    rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀}
        (fun v hv ↦ localSymbol_prime_of_ne (by simpa using hv) (by simpa using hv) hζ),
      Finset.prod_singleton, hinf, localSymbol_prime_self v₀ hζ]
  · classical
    have : NeZero (prime v₀ ^ n) := ⟨hn⟩
    rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀, v'}
        (fun v hv ↦ by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
          exact localSymbol_prime_of_ne hv.1 hv.2 hζ),
      Finset.prod_pair h, hinf, AlgEquiv.mul_apply, localSymbol_prime_at_self h hζ, map_pow,
      localSymbol_prime_at_other h hζ, ← pow_mul]
    conv_rhs => rw [← pow_one ζ]
    refine RHDirect.CFT.LocalField.pow_eq_pow_of_natCast_eq hζ ?_
    have hu : ((prime v' : ℕ) : ℤ_[prime v₀]) = ((primeUnit h : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀]) :=
      (coe_primeUnit h).symm
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← map_natCast (PadicInt.toZModPow (p := prime v₀) n),
      hu, ← map_mul, Units.inv_mul, map_one, Nat.cast_one]

end Generators

theorem mem_of_neg_one_mem_of_primeRat_mem (H : Subgroup ℚˣ) (hneg : -1 ∈ H)
    (hp : ∀ v, primeRat v ∈ H) (a : ℚˣ) : a ∈ H := by
  have hnat : ∀ n : ℕ, ∀ h : (n : ℚ) ≠ 0, Units.mk0 (n : ℚ) h ∈ H := by
    intro n
    induction n using Nat.recOnMul with
    | zero => intro h; exact absurd Nat.cast_zero h
    | one =>
      intro h
      convert H.one_mem
      ext
      simp
    | prime p hp' =>
      intro h
      convert hp (placeOf ⟨p, hp'⟩) using 1
      ext
      rw [Units.val_mk0, coe_primeRat, prime_placeOf ⟨p, hp'⟩]
    | mul a b ha hb =>
      intro h
      have ha0 : (a : ℚ) ≠ 0 := fun h0 ↦ h (by rw [Nat.cast_mul, h0, zero_mul])
      have hb0 : (b : ℚ) ≠ 0 := fun h0 ↦ h (by rw [Nat.cast_mul, h0, mul_zero])
      convert H.mul_mem (ha ha0) (hb hb0) using 1
      ext
      simp
  have hint : ∀ z : ℤ, ∀ h : (z : ℚ) ≠ 0, Units.mk0 (z : ℚ) h ∈ H := by
    intro z h
    have h' : ((z.natAbs : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Int.natAbs_ne_zero.2 (Int.cast_ne_zero.1 h))
    rcases Int.natAbs_eq z with hz | hz
    · convert hnat _ h' using 1
      ext
      rw [Units.val_mk0, Units.val_mk0, ← Int.cast_natCast, ← hz]
    · convert H.mul_mem hneg (hnat _ h') using 1
      ext
      rw [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, Units.val_mk0, neg_one_mul,
        ← Int.cast_natCast, ← Int.cast_neg, ← hz]
  have h1 := hint a.1.num (Int.cast_ne_zero.2 (Rat.num_ne_zero.2 a.ne_zero))
  have h2 := hint (a.1.den : ℤ) (by exact_mod_cast a.1.den_nz)
  convert H.mul_mem h1 (H.inv_mem h2) using 1
  ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, Int.cast_natCast,
    ← div_eq_mul_inv, Rat.num_div_den]

theorem apply_eq_of_pow_eq_one_of_forall_prime_pow {L : Type*} [Field L] [CharZero L] (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ p k : ℕ, p.Prime → ∀ ζ : L, ζ ^ (p ^ k) = 1 → σ ζ = ζ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  induction n using Nat.recOnPosPrimePosCoprime generalizing ζ with
  | prime_pow p k hp _ => exact hσ p k hp ζ hζ
  | zero => exact absurd rfl hn
  | one => rw [pow_one] at hζ; rw [hζ, map_one]
  | coprime a b ha hb hab iha ihb =>
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hζ
      exact zero_ne_one hζ
    have hA : σ (ζ ^ a) = ζ ^ a :=
      ihb (by omega) (by rw [← pow_mul, hζ])
    have hB : σ (ζ ^ b) = ζ ^ b :=
      iha (by omega) (by rw [← pow_mul, mul_comm b a, hζ])
    have e : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
      rw [← Nat.gcd_eq_gcd_ab, hab.gcd_eq_one, Nat.cast_one]
    have hz : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b := by
      rw [← zpow_natCast, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← e,
        zpow_one]
    rw [hz, map_mul, map_zpow₀, map_zpow₀, hA, hB]

section Main

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem ideleSymbol_diagonal_apply_of_pow_eq_one_of_prime_pow (a : ℚˣ)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    ideleSymbol ℚ L (diagonal ℚ a) ζ = ζ := by
  let H : Subgroup ℚˣ :=
    (MulAction.stabilizer (L ≃ₐ[ℚ] L) ζ).comap ((ideleSymbol ℚ L).comp (diagonal ℚ))
  have key : ∀ b, b ∈ H ↔ ideleSymbol ℚ L (diagonal ℚ b) ζ = ζ := fun b ↦ by
    simp only [H, Subgroup.mem_comap, MonoidHom.comp_apply, MulAction.mem_stabilizer_iff,
      AlgEquiv.smul_def]
  exact (key a).1 (mem_of_neg_one_mem_of_primeRat_mem H
    ((key _).2 (ideleSymbol_diagonal_neg_one L v₀ hζ))
    (fun v' ↦ (key _).2 (ideleSymbol_diagonal_prime L v₀ v' hζ)) a)

theorem ideleSymbol_diagonal_apply_of_pow_eq_one (a : ℚˣ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : ideleSymbol ℚ L (diagonal ℚ a) ζ = ζ :=
  apply_eq_of_pow_eq_one_of_forall_prime_pow _ (fun p k hp ξ hξ ↦ by
    exact ideleSymbol_diagonal_apply_of_pow_eq_one_of_prime_pow L a (placeOf ⟨p, hp⟩) (n := k)
      (by rw [prime_placeOf ⟨p, hp⟩]; exact hξ)) hn hζ

theorem ideleSymbol_diagonal_eq_one (S : Set ℕ) [IsCyclotomicExtension S ℚ L] (a : ℚˣ) :
    ideleSymbol ℚ L (diagonal ℚ a) = 1 :=
  IsCyclotomicExtension.algEquiv_eq_of_apply_eq S ℚ L fun m hm hm0 ↦ by
    obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L hm hm0
    exact ⟨r, hr, ideleSymbol_diagonal_apply_of_pow_eq_one L a hm0 hr.pow_eq_one⟩

end Main

end RationalSymbol

end

end Sec3_13_NormResidueSymbol_RationalDiagonal

/-! ### 14_NormResidueSymbol.RestrictNormalInfiniteLocalSymbol -/
section Sec3_14_NormResidueSymbol_RestrictNormalInfiniteLocalSymbol

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
  SemiLocal AdeleBaseChange IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

section Finite

variable (v : HeightOneSpectrum (𝓞 K))

omit [NumberField K] [NumberField L] [NumberField M] in

theorem liesOver_below_of_placesOver (u : PlacesOver M v) :
    (below L u.1).asIdeal.LiesOver v.asIdeal :=
  (below_eq_iff _ v).1 (by rw [below_below, (below_eq_iff u.1 v).2 inferInstance])

def belowPlace (u : PlacesOver M v) : PlacesOver L v :=
  ⟨below L u.1, liesOver_below_of_placesOver L M v u⟩

omit [NumberField K] [NumberField L] [NumberField M] in
theorem belowPlace_val (u : PlacesOver M v) : (belowPlace L M v u).1 = below L u.1 :=
  rfl

omit [NumberField K] [NumberField L] [NumberField M] in

instance liesOver_belowPlace (u : PlacesOver M v) :
    u.1.asIdeal.LiesOver (belowPlace L M v u).1.asIdeal :=
  liesOver_below (K := L) u.1

def completionAlgHom (u : PlacesOver M v) :
    (belowPlace L M v u).1.adicCompletion L →ₐ[v.adicCompletion K] u.1.adicCompletion M :=
  { completionMap (belowPlace L M v u).1 u.1 with
    commutes' := fun a ↦ completionMap_completionMap v (belowPlace L M v u).1 u.1 a }

theorem completionAlgHom_algebraMap (u : PlacesOver M v) (l : L) :
    completionAlgHom L M v u (algebraMap L ((belowPlace L M v u).1.adicCompletion L) l) =
      algebraMap M (u.1.adicCompletion M) (algebraMap L M l) := by
  change completionMap _ u.1 _ = _
  rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply L M (u.1.adicCompletion M)]

variable [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)]
  [IsMulCommutative (M ≃ₐ[K] M)]

theorem restrictNormal_localSymbol (x : (v.adicCompletion K)ˣ) :
    (localSymbol M v x).restrictNormal L = localSymbol L v x := by
  obtain ⟨u⟩ := nonempty_placesOver M v
  obtain ⟨τ, hτ⟩ := exists_mk_eq_localReciprocityLimit (k := v.adicCompletion K) x
  have key : ∀ l : L,
      localSymbol M v x (algebraMap L M l) = algebraMap L M (localSymbol L v x l) := by
    intro l
    apply (algebraMap M (u.1.adicCompletion M)).injective
    apply (residueEmbedding (v.adicCompletion K) (u.1.adicCompletion M)).toRingHom.injective
    change residueEmbedding _ _ (algebraMap M _ (localSymbol M v x (algebraMap L M l))) =
      residueEmbedding _ _ (algebraMap M _ (algebraMap L M (localSymbol L v x l)))
    rw [algebraMap_localSymbol_apply M v u, residueEmbedding_normResidueSymbol hτ,
      ← completionAlgHom_algebraMap, ← completionAlgHom_algebraMap,
      algebraMap_localSymbol_apply L v (belowPlace L M v u)]
    exact (normResidueSymbol_spec
      ((residueEmbedding (v.adicCompletion K) (u.1.adicCompletion M)).comp
        (completionAlgHom L M v u)) hτ _).symm
  ext l
  apply (algebraMap L M).injective
  rw [AlgEquiv.restrictNormal_commutes, key]

end Finite

section Infinite

omit [NumberField K] [NumberField L] in

theorem isConj_conjAt_of_isReal [IsGalois K L] {w : InfinitePlace L}
    (hv : (w.comap (algebraMap K L)).IsReal) : IsConj w.embedding (conjAt K w) := by
  by_cases hw : w.IsReal
  · rw [conjAt_of_isReal hw]
    exact isConj_one_iff.2 (isReal_iff.1 hw)
  · exact isConj_conjAt (isRamified_iff.2 ⟨not_isReal_iff_isComplex.1 hw, hv⟩)

omit [NumberField K] [NumberField L] [NumberField M] in

theorem restrictNormal_conjAt [IsGalois K L] [IsGalois K M] (w : InfinitePlace M)
    (hv : (w.comap (algebraMap K M)).IsReal) :
    (conjAt K w).restrictNormal L = conjAt K (w.comap (algebraMap L M)) := by
  have h := isConj_conjAt_of_isReal M hv
  have hr : IsConj (w.embedding.comp (algebraMap L M)) ((conjAt K w).restrictNormal L) := by
    rw [isConj_iff_forall]
    intro l
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes]
    exact h.eq _
  have hmk : mk (w.embedding.comp (algebraMap L M)) = mk (w.comap (algebraMap L M)).embedding := by
    rw [mk_embedding, ← comap_mk, mk_embedding]
  exact (conjOfEmbedding_eq ((isConj_iff_of_mk_eq hmk _).1 hr)).symm

variable [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)]
  [IsMulCommutative (M ≃ₐ[K] M)]

theorem restrictNormal_infiniteLocalSymbol (v : InfinitePlace K) (x : v.Completionˣ) :
    (infiniteLocalSymbol M v x).restrictNormal L = infiniteLocalSymbol L v x := by
  have h1 : (1 : M ≃ₐ[K] M).restrictNormal L = 1 :=
    map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)
  by_cases hv : v.IsReal
  · obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver M v
    have hwv : (w : InfinitePlace M).comap (algebraMap K M) = v :=
      (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v _).1 w.2
    have hw' : ((w : InfinitePlace M).comap (algebraMap L M)).LiesOver v :=
      (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v _).2 (by
        rw [← comap_comp, ← IsScalarTower.algebraMap_eq, hwv])
    rw [infiniteLocalSymbol_apply M v hv w, infiniteLocalSymbol_apply L v hv ⟨_, hw'⟩]
    split_ifs
    · exact restrictNormal_conjAt L M (w : InfinitePlace M) (by rw [hwv]; exact hv)
    · exact h1
  · rw [infiniteLocalSymbol_of_not_isReal M v hv, infiniteLocalSymbol_of_not_isReal L v hv]
    exact h1

end Infinite

variable [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)]
  [IsMulCommutative (M ≃ₐ[K] M)]

theorem restrictNormal_ideleSymbol (x : IdeleGroup K) :
    (ideleSymbol K M x).restrictNormal L = ideleSymbol K L x := by
  have h := eq_ideleSymbol L (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp
      (ideleSymbol K M)) ((continuous_of_discreteTopology :
      Continuous (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)).comp (continuous_ideleSymbol M))
    (fun v a ↦ by
      rw [MonoidHom.comp_apply, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol L M v a)
    (fun w a ↦ by
      rw [MonoidHom.comp_apply, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol L M w a)
  exact congrArg (fun f : IdeleGroup K →* (L ≃ₐ[K] L) ↦ f x) h

end

end Sec3_14_NormResidueSymbol_RestrictNormalInfiniteLocalSymbol

/-! ### 15_IdeleClassGroup.NatCardTateOfIsCyclic -/
section Sec3_15_IdeleClassGroup_NatCardTateOfIsCyclic

open NumberField IntermediateField RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield

theorem natCard_tate_of_isCyclic (K L : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) [(L.subgroupOf K).Normal]
    [(L.subgroupOf K).FiniteIndex] {F E : FiniteSubfield} (hFE : F ≤ E)
    (hK : K = F.1.fixingSubgroup) (hL : L = E.1.fixingSubgroup)
    (hcyc : IsCyclic (K ⧸ L.subgroupOf K)) :
    Nat.card (tateZero IdeleClassLimit K L) = L.relIndex K ∧
      Nat.card (tateNegOne IdeleClassLimit K L) = 1 := by
  subst hK hL
  have : Fact (F ≤ E) := ⟨hFE⟩
  have : IsGalois F.1 E.1 := isGalois_of_normal (F := F) (E := E)

  have hcycE : IsCyclic (E.1 ≃ₐ[F.1] E.1) := by
    let φ := QuotientGroup.lift (E.1.fixingSubgroup.subgroupOf F.1.fixingSubgroup)
      (restrictHom (F := F) (E := E)) (ker_restrictHom (F := F) (E := E)).ge
    refine isCyclic_of_surjective φ fun x ↦ ?_
    obtain ⟨g, rfl⟩ := restrictHom_surjective (F := F) (E := E) x
    exact ⟨g, rfl⟩
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E.1 ≃ₐ[F.1] E.1)
  have hax := classFieldAxiom_ideleClassGroup (K := F.1) (L := E.1) σ hσ
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr (tateZeroEquivGalois (F := F) (E := E)).toEquiv,
      RHDirect.CFT.LocalField.natCard_tateZero_eq hσ, hax.1]
    exact (relIndex_fixingSubgroup hFE).symm
  · rw [Nat.card_congr (tateNegOneEquivGalois (F := F) (E := E)).toEquiv,
      RHDirect.CFT.LocalField.natCard_tateNegOne_eq hσ, hax.2]

theorem classFieldAxiom : ClassFieldAxiom (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (V : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
    (ofOpenSubgroup_le hVU) (fixingSubgroup_ofOpenSubgroup U).symm
    (fixingSubgroup_ofOpenSubgroup V).symm hcyc

end IdeleClassLimit

end

end Sec3_15_IdeleClassGroup_NatCardTateOfIsCyclic

/-! ### 16_NormResidueSymbol.Rational -/
section Sec3_16_NormResidueSymbol_Rational

open IsDedekindDomain NumberField IdeleGroup IntermediateField
open scoped RHDirect.CFT_AbstractLocalReciprocity

noncomputable section

namespace RationalSymbol

open RHDirect.CFT_CyclotomicCharacters.Cyclotomic RHDirect.CFT_AbstractLocalReciprocity

attribute [local instance] galCommGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

section Unit

def unitAt (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ℤ_[prime v]ˣ :=
  Units.map ((Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv :
    v.adicCompletionIntegers ℚ →* ℤ_[prime v]) ((RationalIdeles.positiveSubgroupEquiv y).2 v)

theorem padicRingEquiv_finiteProj (y : RationalIdeles.positiveSubgroup)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    padicRingEquiv v (finiteProj v (y : IdeleGroup ℚ) : v.adicCompletion ℚ) =
      ((unitAt y v : ℤ_[prime v]) : ℚ_[prime v]) * (prime v : ℚ_[prime v]) ^ (0 : ℕ) := by
  rw [pow_zero, mul_one]
  rfl

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] [IsMulCommutative (L ≃ₐ[ℚ] L)]

theorem ideleSymbol_apply_of_mem_positiveSubgroup (y : RationalIdeles.positiveSubgroup)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : L} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    ideleSymbol ℚ L y ζ =
      ζ ^ (PadicInt.toZModPow n (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val := by
  have hn : prime v₀ ^ n ≠ 0 := pow_ne_zero _ (Fact.out : (prime v₀).Prime).ne_zero
  rw [ideleSymbol_apply_eq_of_forall_notMem L _ ζ {v₀} fun v hv ↦ by
      rw [localSymbol_apply_of_pow_eq_one_of_coprime v L _ (unitAt y v) 0
        (padicRingEquiv_finiteProj y v)
        (Nat.Coprime.pow_left n (coprime_prime (by simpa using hv : v ≠ v₀).symm)) hζ,
        pow_zero, pow_one],
    Finset.prod_singleton, infiniteLocalSymbol_apply_of_pow_eq_one L _ _ hn hζ,
    extensionEmbeddingOfIsReal_infiniteProj,
    if_neg (not_lt.2 (RationalIdeles.mem_positiveSubgroup.1 y.2).2.le)]
  exact localSymbol_apply_of_pow_eq_one_of_prime_pow v₀ L _ (unitAt y v₀) 0
    (by rw [padicRingEquiv_finiteProj y v₀, pow_zero, zpow_zero]) hζ

end Unit

theorem toPadicInt_unitPart_mk (y : RationalIdeles.positiveSubgroup) (v : HeightOneSpectrum (𝓞 ℚ)) :
    toPadicInt (prime v) (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℤ̂) =
      ((unitAt y v : ℤ_[prime v]ˣ) : ℤ_[prime v]) := by
  have h := toPadicInt_unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))
    (Rat.HeightOneSpectrum.primesEquiv v)
  rw [RationalIdeles.ideleClassGroupEquiv_mk] at h
  refine h.trans ?_
  change RationalIdeles.integersRingEquiv (fun v ↦ (((RationalIdeles.positiveSubgroupEquiv y).2 v :
    (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ))
      (Rat.HeightOneSpectrum.primesEquiv v) = _
  exact Equiv.piCongrLeft_apply_apply (P := fun p : Nat.Primes ↦ ℤ_[p])
    (e := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))
    (fun v' ↦ (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v').toAlgEquiv.toRingEquiv
      (((RationalIdeles.positiveSubgroupEquiv y).2 v' : (v'.adicCompletionIntegers ℚ)ˣ) :
        v'.adicCompletionIntegers ℚ)) v

theorem reciprocityMap_apply_of_mem_positiveSubgroup (y : RationalIdeles.positiveSubgroup)
    (v₀ : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} {ζ : maxCyclotomic} (hζ : ζ ^ (prime v₀ ^ n) = 1) :
    reciprocityMap (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) ζ =
      ζ ^ (PadicInt.toZModPow n (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀])).val := by
  rw [cycCharacter_spec _ (primePowPNat (prime v₀) n) hζ, cycCharacter_reciprocityMap,
    ← toZModPow_toPadicInt]
  have h' : Units.map (toPadicInt (prime v₀)).toMonoidHom
      (unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))) = unitAt y v₀ :=
    Units.ext (toPadicInt_unitPart_mk y v₀)
  have h'' : toPadicInt (prime v₀)
      (((unitPart (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)))⁻¹ : ℤ̂ˣ) : ℤ̂) =
        (((unitAt y v₀)⁻¹ : ℤ_[prime v₀]ˣ) : ℤ_[prime v₀]) := by
    rw [← h', Units.coe_map_inv]
    rfl
  rw [h'']
  rfl

instance (m : ℕ) [NeZero m] :
    IsMulCommutative (rootsOfUnityField m ≃ₐ[ℚ] rootsOfUnityField m) :=
  IsCyclotomicExtension.isMulCommutative {m} ℚ _

theorem rootsOfUnityField_le_maxCyclotomic (m : ℕ) [NeZero m] :
    rootsOfUnityField m ≤ maxCyclotomic :=
  adjoin_le_iff.2 fun _ hx ↦ subset_adjoin ℚ _ ⟨m, Nat.pos_of_neZero m, hx⟩

theorem restrictNormal_eq_ideleSymbol (m : ℕ) [NeZero m] (x : IdeleGroup ℚ) (σ : Gal(ℚ̄/ℚ))
    (hσ : cycRestrict σ = reciprocityMap (IdeleClassGroup.mk ℚ x)) :
    σ.restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) x := by
  obtain ⟨⟨a, y⟩, rfl⟩ := RationalIdeles.mulMap_bijective.2 x
  simp only [RationalIdeles.mulMap_apply] at hσ ⊢
  have e : IdeleClassGroup.mk ℚ (diagonal ℚ a * (y : IdeleGroup ℚ)) =
      IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ) := by
    rw [map_mul, IdeleClassGroup.mk_diagonal]
    exact one_mul (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ))
  rw [e] at hσ
  rw [map_mul, ideleSymbol_diagonal_eq_one _ {m} a, one_mul]
  set L := rootsOfUnityField m
  set σ₁ := ideleSymbol ℚ L (y : IdeleGroup ℚ)
  set σ₂ := σ.restrictNormal L

  have key : ∀ (p k : ℕ) (hp : p.Prime) (ζ : L), ζ ^ (p ^ k) = 1 → σ₂ ζ = σ₁ ζ := by
    intro p k hp ζ hζ
    have hp' : ζ ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1 := by rw [prime_placeOf ⟨p, hp⟩]; exact hζ
    rw [ideleSymbol_apply_of_mem_positiveSubgroup L y _ hp']
    apply Subtype.ext
    have h1 : ((σ₂ ζ : L) : ℚ̄) = σ ζ := AlgEquiv.restrictNormal_commutes σ L ζ
    have hmem : (ζ : ℚ̄) ∈ maxCyclotomic := rootsOfUnityField_le_maxCyclotomic m ζ.2
    have hζ' : (⟨ζ, hmem⟩ : maxCyclotomic) ^ (prime (placeOf ⟨p, hp⟩) ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hp')
    have h2 := reciprocityMap_apply_of_mem_positiveSubgroup y (placeOf ⟨p, hp⟩) hζ'
    rw [← hσ] at h2
    have h3 := congrArg Subtype.val h2
    rw [coe_cycRestrict_apply] at h3
    rw [h1, h3, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow]
  refine IsCyclotomicExtension.algEquiv_eq_of_apply_eq {m} ℚ L fun n hn hn0 ↦ ?_
  obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L hn hn0
  refine ⟨r, hr, ?_⟩
  have := apply_eq_of_pow_eq_one_of_forall_prime_pow (σ₁⁻¹ * σ₂) (fun p k hp ζ hζ ↦ by
    rw [AlgEquiv.mul_apply, key p k hp ζ hζ, ← AlgEquiv.mul_apply, inv_mul_cancel,
      AlgEquiv.one_apply]) hn0 hr.pow_eq_one
  rw [AlgEquiv.mul_apply] at this
  calc σ₂ r = σ₁ (σ₁⁻¹ (σ₂ r)) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    _ = σ₁ r := by rw [this]

theorem coe_ideleSymbol_apply (m : ℕ) [NeZero m] (x : IdeleGroup ℚ) (z : rootsOfUnityField m) :
    ((ideleSymbol ℚ (rootsOfUnityField m) x z : rootsOfUnityField m) : ℚ̄) =
      ((reciprocityMap (IdeleClassGroup.mk ℚ x)
        ⟨z, rootsOfUnityField_le_maxCyclotomic m z.2⟩ : maxCyclotomic) : ℚ̄) := by
  obtain ⟨σ, hσ⟩ := cycRestrict_surjective (reciprocityMap (IdeleClassGroup.mk ℚ x))
  rw [← restrictNormal_eq_ideleSymbol m x σ hσ, ← hσ, coe_cycRestrict_apply]
  exact AlgEquiv.restrictNormal_commutes σ (rootsOfUnityField m) z

end RationalSymbol

end

end Sec3_16_NormResidueSymbol_Rational

/-! ### 17_NormResidueSymbol.FunctorialInfinite -/
section Sec3_17_NormResidueSymbol_FunctorialInfinite

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
  NumberField.ComplexEmbedding IdeleGroup
open scoped NumberField.LiesOver

noncomputable section

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

theorem ideleNorm_infiniteEmbedding (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ideleNorm K K' (infiniteEmbedding v' a) =
      infiniteEmbedding (v'.comap (algebraMap K K'))
        (RHDirect.CFT.LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  classical
  apply Units.ext
  refine Prod.ext (funext fun w ↦ ?_) (FiniteAdeleRing.ext (K := K) fun v ↦ ?_)
  · rw [ideleNorm_fst]
    simp only [coe_infiniteEmbedding]
    by_cases hw : w = v'.comap (algebraMap K K')
    · subst hw
      rw [Finset.prod_eq_single (⟨v', (inferInstance : v'.LiesOver (v'.comap (algebraMap K K')))⟩ :
          (v'.comap (algebraMap K K')).placesOver K'),
        infiniteAdeleSingle_apply, infiniteAdeleSingle_apply, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_same, RHDirect.CFT.LocalField.coe_normUnits]
      · intro u _ hu
        rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)),
          map_one]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw]
      refine Finset.prod_eq_one fun u _ ↦ ?_
      have hu : (u : InfinitePlace K') ≠ v' := by
        rintro h
        apply hw
        rw [← h]
        exact ((RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq w _).1 u.2).symm
      rw [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu, map_one]
  · rw [ideleNorm_snd]
    exact Finset.prod_eq_one fun _ _ ↦ map_one _

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra K L]
  [Algebra K L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] in

theorem restrictNormal_restrictScalars_conjAt [IsGalois K L] [IsGalois K' L']
    (u' : InfinitePlace L') (hv : (u'.comap (algebraMap K' L')).IsReal) :
    ((conjAt K' u').restrictScalars K).restrictNormal L = conjAt K (u'.comap (algebraMap L L')) := by
  have h := isConj_conjAt_of_isReal L' hv
  have hr : IsConj (u'.embedding.comp (algebraMap L L'))
      (((conjAt K' u').restrictScalars K).restrictNormal L) := by
    rw [isConj_iff_forall]
    intro l
    rw [RingHom.comp_apply, RingHom.comp_apply, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.restrictScalars_apply]
    exact h.eq _
  have hmk : mk (u'.embedding.comp (algebraMap L L')) =
      mk (u'.comap (algebraMap L L')).embedding := by
    rw [mk_embedding, ← comap_mk, mk_embedding]
  exact (conjOfEmbedding_eq ((isConj_iff_of_mk_eq hmk _).1 hr)).symm

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

omit [NumberField K] [NumberField K'] [NumberField L] [NumberField L'] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')] in

theorem restrictNormal_restrictScalars_one [Normal K L] :
    ((1 : L' ≃ₐ[K'] L').restrictScalars K).restrictNormal L = 1 := by
  ext l
  apply (algebraMap L L').injective
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.restrictScalars_apply, AlgEquiv.one_apply,
    AlgEquiv.one_apply]

omit [NumberField K] [NumberField K'] in

theorem extensionEmbeddingOfIsReal_normUnits (v' : InfinitePlace K') (hv' : v'.IsReal)
    (a : v'.Completionˣ) :
    extensionEmbeddingOfIsReal (hv'.comap (algebraMap K K'))
        (RHDirect.CFT.LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a : _) =
      extensionEmbeddingOfIsReal hv' a := by
  have hv := hv'.comap (algebraMap K K')
  have hfin : Module.finrank (v'.comap (algebraMap K K')).Completion v'.Completion = 1 :=
    (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.finrank_completion_eq_one_iff v').2
      fun h ↦ not_isComplex_iff_isReal.2 hv' h.2
  obtain ⟨c, hc⟩ := ((Algebra.finrank_eq_one_iff_bijective_algebraMap).1 hfin).2
    (a : v'.Completion)
  have e1 : (extensionEmbeddingOfIsReal hv'
      (algebraMap (v'.comap (algebraMap K K')).Completion v'.Completion c) : ℂ) =
        extensionEmbeddingOfIsReal hv c := by
    rw [extensionEmbeddingOfIsReal_apply]
    exact RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.extensionEmbedding_algebraMap hv c
  rw [RHDirect.CFT.LocalField.coe_normUnits, ← hc, Algebra.norm_algebraMap, hfin, pow_one]
  exact (Complex.ofReal_injective e1).symm

theorem restrictNormal_infiniteLocalSymbol_norm (v' : InfinitePlace K') (a : v'.Completionˣ) :
    ((infiniteLocalSymbol L' v' a).restrictScalars K).restrictNormal L =
      infiniteLocalSymbol L (v'.comap (algebraMap K K'))
        (RHDirect.CFT.LocalField.normUnits (v'.comap (algebraMap K K')).Completion v'.Completion a) := by
  by_cases hv' : v'.IsReal
  · have hv := hv'.comap (algebraMap K K')
    obtain ⟨u'⟩ := IdeleNorm.nonempty_infinitePlacesOver L' v'
    have hu'v' : (u' : InfinitePlace L').comap (algebraMap K' L') = v' :=
      (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq v' _).1 u'.2
    have hu : ((u' : InfinitePlace L').comap (algebraMap L L')).LiesOver
        (v'.comap (algebraMap K K')) :=
      (RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.liesOver_iff_comap_eq _ _).2 (by
        rw [← comap_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq K K' L',
          comap_comp, hu'v'])
    rw [infiniteLocalSymbol_apply L' v' hv' u', infiniteLocalSymbol_apply L _ hv ⟨_, hu⟩,
      extensionEmbeddingOfIsReal_normUnits v' hv' a]
    split_ifs
    · exact restrictNormal_restrictScalars_conjAt (u' : InfinitePlace L') (by rw [hu'v']; exact hv')
    · exact restrictNormal_restrictScalars_one
  · rw [infiniteLocalSymbol_of_not_isReal L' v' hv', MonoidHom.one_apply,
      restrictNormal_restrictScalars_one]
    by_cases hv : (v'.comap (algebraMap K K')).IsReal
    · obtain ⟨u⟩ := IdeleNorm.nonempty_infinitePlacesOver L (v'.comap (algebraMap K K'))
      rw [infiniteLocalSymbol_apply L _ hv u, if_neg]
      rw [not_lt, RHDirect.CFT.LocalField.coe_normUnits, RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.extensionEmbeddingOfIsReal_norm
        hv (not_isReal_iff_isComplex.1 hv')]
      exact Complex.normSq_nonneg _
    · rw [infiniteLocalSymbol_of_not_isReal L _ hv, MonoidHom.one_apply]

end

end Sec3_17_NormResidueSymbol_FunctorialInfinite

/-! ### 18_NormResidueSymbol.Surjective -/
section Sec3_18_NormResidueSymbol_Surjective

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

section Trivial

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem range_ideleNorm_eq_top_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    (ideleNorm K L).range = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ ↦ (IdeleNorm.mem_range_ideleNorm_iff_forall L x).2
    ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨w⟩ := nonempty_placesOver L v
    have h1 : finiteProj v x ∈ (localSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_finiteEmbedding]
      exact h _
    rw [ker_localSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.finiteLocalNorm_mulSingle]; exact hy⟩
  · obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L v
    have h1 : infiniteProj v x ∈ (infiniteLocalSymbol L v).ker := by
      rw [MonoidHom.mem_ker, ← ideleSymbol_infiniteEmbedding]
      exact h _
    rw [ker_infiniteLocalSymbol L v w] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨Pi.mulSingle w y, by rw [IdeleNorm.infiniteLocalNorm_mulSingle]; exact hy⟩

end Trivial

universe u

section Cyclic

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]

theorem finrank_eq_one_of_ideleSymbol_eq_one (h : ∀ x, ideleSymbol K L x = 1) :
    Module.finrank K L = 1 :=
  firstInequality.finrank_eq_one_of_sup_eq_top
    (top_le_iff.1 (range_ideleNorm_eq_top_of_ideleSymbol_eq_one L h ▸ le_sup_left))

end Cyclic

section Surjective

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

attribute [local instance] galCommGroup

omit [NumberField K] [NumberField L] [IsMulCommutative (L ≃ₐ[K] L)] in

theorem restrictNormal_fixedField_eq_one {N : Subgroup (L ≃ₐ[K] L)} [N.Normal] {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ N) : σ.restrictNormal (fixedField N) = 1 := by
  ext y
  change ((σ.restrictNormal (fixedField N) y : fixedField N) : L) = y
  exact (AlgEquiv.restrictNormal_commutes σ (fixedField N) y).trans
    ((mem_fixedField_iff N y).1 y.2 σ hσ)

theorem ideleSymbol_surjective : Function.Surjective (ideleSymbol K L) := by
  classical
  by_contra hs
  obtain ⟨σ, hσ⟩ := not_forall.1 hs
  set H := (ideleSymbol K L).range with hH
  have hσH : σ ∉ H := fun ⟨x, hx⟩ ↦ hσ ⟨x, hx⟩
  obtain ⟨ι, _, n, _, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite
    ((L ≃ₐ[K] L) ⧸ H)
  have hne : (QuotientGroup.mk' H σ) ≠ 1 := by
    rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨i, hi⟩ : ∃ i, e (QuotientGroup.mk' H σ) i ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne ((MulEquiv.map_eq_one_iff e).1 (funext hall))
  set χ : (L ≃ₐ[K] L) →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun j ↦ Multiplicative (ZMod (n j))) i).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' H)) with hχ
  set N := χ.ker with hN
  have hHN : ∀ x, ideleSymbol K L x ∈ N := fun x ↦ by
    have hq : QuotientGroup.mk' H (ideleSymbol K L x) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
    rw [hN, MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, hq, map_one, map_one]
  have hσN : σ ∉ N := hi
  set F := fixedField N with hF
  have : IsCyclic (F ≃ₐ[K] F) := by
    have e1 : (F ≃ₐ[K] F) ≃* χ.range :=
      (IsGalois.normalAutEquivQuotient N).symm.trans (QuotientGroup.quotientKerEquivRange χ)
    exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  have hF1 : ∀ x, ideleSymbol K F x = 1 := fun x ↦ by
    rw [← restrictNormal_ideleSymbol F L x]
    exact restrictNormal_fixedField_eq_one (hHN x)
  have hbot : F = ⊥ := finrank_eq_one_iff.1 (finrank_eq_one_of_ideleSymbol_eq_one hF1)
  have htop : N = ⊤ := by
    rw [← fixingSubgroup_fixedField N, ← hF, hbot, fixingSubgroup_bot]
  exact hσN (htop ▸ Subgroup.mem_top σ)

end Surjective

end

end Sec3_18_NormResidueSymbol_Surjective

/-! ### 19_NormResidueSymbol.RationalContinuous -/
section Sec3_19_NormResidueSymbol_RationalContinuous

open IsDedekindDomain NumberField IdeleGroup IntermediateField Topology
open scoped RHDirect.CFT_AbstractLocalReciprocity

noncomputable section

namespace RationalSymbol

open RHDirect.CFT_CyclotomicCharacters.Cyclotomic RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem continuous_cycRestrict : Continuous cycRestrict := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @Normal ℚ maxCyclotomic _ _ (IntermediateField.algebra' maxCyclotomic) := by
    convert isGalois_maxCyclotomic.to_normal
    exact Subsingleton.elim _ _
  have hc := @InfiniteGalois.restrictNormalHom_continuous ℚ ℚ̄ _ _ _ maxCyclotomic h
  exact hc

theorem continuous_cycCharacter : Continuous cycCharacter := by
  have : T2Space Gal(maxCyclotomic/ℚ) := krullTopology_t2
  have hq : IsQuotientMap cycRestrict :=
    continuous_cycRestrict.isClosedMap.isQuotientMap continuous_cycRestrict cycRestrict_surjective
  rw [hq.continuous_iff]
  exact continuous_character.congr fun σ ↦ (cycCharacter_cycRestrict σ).symm

def cycCharacterHomeomorph : Gal(maxCyclotomic/ℚ) ≃ₜ* ℤ̂ˣ where
  toMulEquiv := cycCharacter
  continuous_toFun := continuous_cycCharacter
  continuous_invFun :=
    (continuous_cycCharacter.homeoOfEquivCompactToT2 (f := cycCharacter.toEquiv)).symm.continuous

@[simp] theorem cycCharacterHomeomorph_apply (τ : Gal(maxCyclotomic/ℚ)) :
    cycCharacterHomeomorph τ = cycCharacter τ :=
  rfl

def unitsPadicHomeomorph : (Π q : Nat.Primes, ℤ_[q])ˣ ≃ₜ* ℤ̂ˣ :=
  unitsContinuousMulEquiv padicEquiv.symm.toMulEquiv continuous_ofPadics continuous_toPadics

theorem unitPart_eq (x : IdeleClassGroup ℚ) :
    unitPart x = unitsPadicHomeomorph (RationalIdeles.ideleClassGroupEquiv x).2 :=
  Units.ext rfl

theorem continuous_unitPart : Continuous unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.continuous.comp
    (continuous_snd.comp RationalIdeles.ideleClassGroupEquiv.continuous)

theorem isOpenMap_unitPart : IsOpenMap unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.toHomeomorph.isOpenMap.comp
    (isOpenMap_snd.comp RationalIdeles.ideleClassGroupEquiv.toHomeomorph.isOpenMap)

theorem reciprocityMap_eq_comp :
    (reciprocityMap : IdeleClassGroup ℚ → Gal(maxCyclotomic/ℚ)) =
      cycCharacterHomeomorph.symm ∘ (·⁻¹) ∘ unitPart :=
  rfl

theorem continuous_reciprocityMap : Continuous reciprocityMap := by
  rw [reciprocityMap_eq_comp]
  exact cycCharacterHomeomorph.symm.continuous.comp (continuous_unitPart.inv)

theorem isOpenMap_reciprocityMap : IsOpenMap reciprocityMap := by
  rw [reciprocityMap_eq_comp]
  exact cycCharacterHomeomorph.symm.toHomeomorph.isOpenMap.comp (IsOpenMap.comp (isOpenMap_inv _) isOpenMap_unitPart)

def positiveRealFactor : Subgroup (IdeleClassGroup ℚ) :=
  (MonoidHom.snd (Units.posSubgroup ℝ) (Π p : Nat.Primes, ℤ_[p])ˣ).ker.comap
    RationalIdeles.ideleClassGroupEquiv.toMulEquiv.toMonoidHom

theorem mem_positiveRealFactor_iff (x : IdeleClassGroup ℚ) :
    x ∈ positiveRealFactor ↔ (RationalIdeles.ideleClassGroupEquiv x).2 = 1 :=
  Iff.rfl

theorem mem_positiveRealFactor_iff_exists (x : IdeleClassGroup ℚ) :
    x ∈ positiveRealFactor ↔
      ∃ r : Units.posSubgroup ℝ, RationalIdeles.ideleClassGroupEquiv.symm (r, 1) = x := by
  rw [mem_positiveRealFactor_iff]
  constructor
  · intro h
    refine ⟨(RationalIdeles.ideleClassGroupEquiv x).1, ?_⟩
    rw [ContinuousMulEquiv.symm_apply_eq]
    exact Prod.ext rfl h.symm
  · rintro ⟨r, rfl⟩
    rw [ContinuousMulEquiv.apply_symm_apply]

theorem ker_reciprocityMap : reciprocityMap.ker = positiveRealFactor := by
  ext x
  rw [MonoidHom.mem_ker, reciprocityMap_eq_one_iff, mem_positiveRealFactor_iff]

instance : positiveRealFactor.Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def quotientPositiveRealFactorMulEquiv :
    IdeleClassGroup ℚ ⧸ positiveRealFactor ≃* Gal(maxCyclotomic/ℚ) :=
  (QuotientGroup.quotientMulEquivOfEq ker_reciprocityMap.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ reciprocityMap_surjective)

theorem quotientPositiveRealFactorMulEquiv_mk (x : IdeleClassGroup ℚ) :
    quotientPositiveRealFactorMulEquiv (x : IdeleClassGroup ℚ ⧸ positiveRealFactor) =
      reciprocityMap x :=
  rfl

theorem continuous_quotientPositiveRealFactorMulEquiv :
    Continuous quotientPositiveRealFactorMulEquiv :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    (continuous_reciprocityMap.congr fun x ↦ (quotientPositiveRealFactorMulEquiv_mk x).symm)

theorem isOpenMap_quotientPositiveRealFactorMulEquiv :
    IsOpenMap quotientPositiveRealFactorMulEquiv := by
  intro U hU
  rw [← Set.image_preimage_eq U QuotientGroup.mk_surjective, Set.image_image]
  simp only [quotientPositiveRealFactorMulEquiv_mk]
  exact isOpenMap_reciprocityMap _ (hU.preimage QuotientGroup.continuous_mk)

def quotientPositiveRealFactorEquiv :
    IdeleClassGroup ℚ ⧸ positiveRealFactor ≃ₜ* Gal(maxCyclotomic/ℚ) where
  toMulEquiv := quotientPositiveRealFactorMulEquiv
  continuous_toFun := continuous_quotientPositiveRealFactorMulEquiv
  continuous_invFun := quotientPositiveRealFactorMulEquiv.toEquiv.continuous_symm_iff.2
    isOpenMap_quotientPositiveRealFactorMulEquiv

@[simp] theorem quotientPositiveRealFactorEquiv_mk (x : IdeleClassGroup ℚ) :
    quotientPositiveRealFactorEquiv (x : IdeleClassGroup ℚ ⧸ positiveRealFactor) =
      reciprocityMap x :=
  rfl

theorem compactSpace_gal_maxCyclotomic : CompactSpace Gal(maxCyclotomic/ℚ) :=
  inferInstance

instance compactSpace_quotientPositiveRealFactor :
    CompactSpace (IdeleClassGroup ℚ ⧸ positiveRealFactor) :=
  quotientPositiveRealFactorEquiv.toHomeomorph.symm.compactSpace

end RationalSymbol

end

end Sec3_19_NormResidueSymbol_RationalContinuous

/-! ### 20_NormResidueSymbol.Functorial -/
section Sec3_20_NormResidueSymbol_Functorial

open IsDedekindDomain NumberField AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']

variable (K) in

def restrictScalarsHom : (L' ≃ₐ[K'] L') →* (L' ≃ₐ[K] L') where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField K'] [NumberField L'] in
@[simp]
theorem restrictScalarsHom_apply (σ : L' ≃ₐ[K'] L') : restrictScalarsHom K σ = σ.restrictScalars K :=
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_restrictScalars_ideleSymbol (x : IdeleGroup K') :
    ((ideleSymbol K' L' x).restrictScalars K).restrictNormal L =
      ideleSymbol K L (ideleNorm K K' x) := by
  have h := IdeleGroup.continuous_monoidHom_ext
    (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp
      ((restrictScalarsHom K).comp (ideleSymbol K' L')))
    (ψ' := (ideleSymbol K L).comp (ideleNorm K K'))
    ((continuous_of_discreteTopology : Continuous ((AlgEquiv.restrictNormalHom (F := K)
      (K₁ := L') L).comp (restrictScalarsHom (L' := L') K))).comp (continuous_ideleSymbol L'))
    ((continuous_ideleSymbol L).comp (continuous_ideleNorm (K := K) (L := K')))
    (fun v' a ↦ by
      change ((ideleSymbol K' L' (finiteEmbedding v' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (finiteEmbedding v' a))
      rw [ideleSymbol_finiteEmbedding, ideleNorm_finiteEmbedding, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol_norm (below K v') v' a)
    (fun w' a ↦ by
      change ((ideleSymbol K' L' (infiniteEmbedding w' a)).restrictScalars K).restrictNormal L =
        ideleSymbol K L (ideleNorm K K' (infiniteEmbedding w' a))
      rw [ideleSymbol_infiniteEmbedding, ideleNorm_infiniteEmbedding, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol_norm w' a)
  exact congrArg (fun f : IdeleGroup K' →* (L ≃ₐ[K] L) ↦ f x) h

end

end Sec3_20_NormResidueSymbol_Functorial

/-! ### 21_NormResidueSymbol.CyclotomicBase -/
section Sec3_21_NormResidueSymbol_CyclotomicBase

open IsDedekindDomain NumberField IdeleGroup IntermediateField

noncomputable section

namespace CyclotomicSymbol

section Roots

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem ideleSymbol_diagonal_apply_of_pow_eq_one (a : Kˣ) {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : ζ ^ n = 1) : ideleSymbol K L (diagonal K a) ζ = ζ := by
  have hk : orderOf ζ ≠ 0 := (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨n, Nat.pos_of_ne_zero hn, hζ⟩)).ne'
  have : NeZero (orderOf ζ) := ⟨hk⟩
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  set L₀ : IntermediateField ℚ L := ℚ⟮ζ⟯ with hL₀
  have : IsCyclotomicExtension {orderOf ζ} ℚ L₀ :=
    hprim.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ L₀ := IsCyclotomicExtension.isGalois {orderOf ζ} ℚ L₀
  have : IsMulCommutative (L₀ ≃ₐ[ℚ] L₀) := IsCyclotomicExtension.isMulCommutative {orderOf ζ} ℚ L₀
  have h := restrictNormal_restrictScalars_ideleSymbol (K := ℚ) (L := L₀) (L' := L) (diagonal K a)
  rw [ideleNorm_diagonal, RationalSymbol.ideleSymbol_diagonal_eq_one L₀ {orderOf ζ}] at h
  have h' := congrArg (fun σ : L₀ ≃ₐ[ℚ] L₀ ↦ ((σ ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩ : L₀) : L)) h
  simp only [AlgEquiv.one_apply] at h'
  exact (AlgEquiv.restrictNormal_commutes ((ideleSymbol K L (diagonal K a)).restrictScalars ℚ) L₀
    ⟨ζ, mem_adjoin_simple_self ℚ ζ⟩).symm.trans h'

theorem ideleSymbol_diagonal_eq_one (S : Set ℕ) [IsCyclotomicExtension S K L] (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 :=
  IsCyclotomicExtension.algEquiv_eq_of_apply_eq S K L fun m hm hm0 ↦ by
    obtain ⟨r, hr⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L hm hm0
    exact ⟨r, hr, ideleSymbol_diagonal_apply_of_pow_eq_one a hm0 hr.pow_eq_one⟩

theorem ideleSymbol_diagonal_eq_one_of_isCyclotomicExtension_singleton (m : ℕ)
    [IsCyclotomicExtension {m} K L] (a : Kˣ) : ideleSymbol K L (diagonal K a) = 1 :=
  ideleSymbol_diagonal_eq_one {m} a

end Roots

section Sub

variable {K : Type*} [Field K] [NumberField K] (L M : Type*) [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M] [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (M ≃ₐ[K] M)]

theorem ideleSymbol_diagonal_eq_one_of_le (S : Set ℕ) [IsCyclotomicExtension S K M] (a : Kˣ) :
    ideleSymbol K L (diagonal K a) = 1 := by
  rw [← restrictNormal_ideleSymbol L M, ideleSymbol_diagonal_eq_one S a]
  exact map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L)

theorem range_diagonal_le_ker_ideleSymbol (S : Set ℕ) [IsCyclotomicExtension S K M] :
    (diagonal K).range ≤ (ideleSymbol K L).ker := by
  rintro _ ⟨a, rfl⟩
  exact ideleSymbol_diagonal_eq_one_of_le L M S a

end Sub

section ClassSymbol

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

def ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (ideleSymbol K L) h

variable {L}

@[simp]
theorem ideleClassSymbol_mk (h : (diagonal K).range ≤ (ideleSymbol K L).ker) (x : IdeleGroup K) :
    ideleClassSymbol L h (IdeleClassGroup.mk K x) = ideleSymbol K L x :=
  rfl

theorem continuous_ideleClassSymbol (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Continuous (ideleClassSymbol L h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_ideleSymbol L)

end ClassSymbol

universe u

theorem ideleClassSymbol_surjective {K L : Type u} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (h : (diagonal K).range ≤ (ideleSymbol K L).ker) :
    Function.Surjective (ideleClassSymbol L h) := fun σ ↦
  let ⟨x, hx⟩ := ideleSymbol_surjective (K := K) (L := L) σ
  ⟨IdeleClassGroup.mk K x, hx⟩

end CyclotomicSymbol

end

end Sec3_21_NormResidueSymbol_CyclotomicBase

/-! ### 22_NormResidueSymbol.CyclotomicCompositum -/
section Sec3_22_NormResidueSymbol_CyclotomicCompositum

open NumberField IntermediateField IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield

def compositum (K F : FiniteSubfield) : FiniteSubfield :=
  ⟨K.1 ⊔ F.1, inferInstance⟩

variable (K F : FiniteSubfield)

instance fact_le_compositum_left : Fact (K ≤ compositum K F) :=
  ⟨show K.1 ≤ K.1 ⊔ F.1 from le_sup_left⟩

instance fact_le_compositum_right : Fact (F ≤ compositum K F) :=
  ⟨show F.1 ≤ K.1 ⊔ F.1 from le_sup_right⟩

theorem fixingSubgroup_compositum :
    (compositum K F).1.fixingSubgroup = K.1.fixingSubgroup ⊓ F.1.fixingSubgroup :=
  fixingSubgroup_sup

variable [IsGalois ℚ F.1]

theorem fixingSubgroup_normal : F.1.fixingSubgroup.Normal := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ F.1 _ (IntermediateField.algebra' F.1) := by
    convert (inferInstance : IsGalois ℚ F.1)
    exact Subsingleton.elim _ _
  rw [InfiniteGalois.normal_iff_isGalois]
  exact h

instance normal_subgroupOf_compositum :
    ((compositum K F).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := by
  rw [fixingSubgroup_compositum, Subgroup.inf_subgroupOf_left]
  have := fixingSubgroup_normal F
  exact Subgroup.Normal.subgroupOf this _

instance isGalois_compositum : IsGalois K.1 (compositum K F).1 :=
  isGalois_of_normal

theorem mem_fixingSubgroup_iff_restrictNormal_eq_one (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    g ∈ F.1.fixingSubgroup ↔ g.restrictNormal F.1 = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg
    ext y
    exact (AlgEquiv.restrictNormal_commutes g F.1 y).trans (hg y y.2)
  · intro hg y hy
    have h1 := AlgEquiv.restrictNormal_commutes g F.1 ⟨y, hy⟩
    rw [hg] at h1
    exact h1.symm

variable [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] in

theorem commutator_mem_fixingSubgroup (a b : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    (a * b)⁻¹ * (b * a) ∈ F.1.fixingSubgroup := by
  rw [mem_fixingSubgroup_iff_restrictNormal_eq_one]
  change AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 ((a * b)⁻¹ * (b * a)) = 1
  rw [map_mul, map_inv, map_mul, map_mul,
    mul_comm' (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 b), inv_mul_cancel]

variable [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)]

instance isMulCommutative_compositum :
    IsMulCommutative ((compositum K F).1 ≃ₐ[K.1] (compositum K F).1) := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := compositum K F) a
  obtain ⟨h, rfl⟩ := restrictHom_surjective (F := K) (E := compositum K F) b
  rw [← map_mul, ← map_mul, MonoidHom.eq_iff, ker_restrictHom, Subgroup.mem_subgroupOf,
    fixingSubgroup_compositum]
  exact ⟨Subtype.property _, commutator_mem_fixingSubgroup F _ _⟩

omit [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] in

theorem restrictNormal_restrictHom (g : K.1.fixingSubgroup) :
    ((restrictHom (E := compositum K F) g).restrictScalars ℚ).restrictNormal F.1 =
      (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 := by
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes
    ((restrictHom (E := compositum K F) g).restrictScalars ℚ) F.1 y
  have h2 := AlgEquiv.restrictNormal_commutes (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) F.1 y
  exact (congrArg Subtype.val h1).trans h2.symm

theorem ideleSymbol_ideleNorm (x : IdeleGroup K.1) :
    ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) =
      ((ideleSymbol K.1 (compositum K F).1 x).restrictScalars ℚ).restrictNormal F.1 :=
  (restrictNormal_restrictScalars_ideleSymbol x).symm

theorem exists_restrictNormal_eq_ideleSymbol (x : IdeleGroup K.1) :
    ∃ g ∈ K.1.fixingSubgroup,
      g.restrictNormal F.1 = ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) := by
  obtain ⟨g, hg⟩ := restrictHom_surjective (F := K) (E := compositum K F)
    (ideleSymbol K.1 (compositum K F).1 x)
  refine ⟨g, g.2, ?_⟩
  rw [ideleSymbol_ideleNorm, ← hg, restrictNormal_restrictHom]

theorem exists_ideleSymbol_eq_restrictNormal {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ K.1.fixingSubgroup) :
    ∃ x : IdeleGroup K.1, ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) = g.restrictNormal F.1 := by
  obtain ⟨x, hx⟩ := ideleSymbol_surjective (K := K.1) (L := (compositum K F).1)
    (restrictHom (E := compositum K F) ⟨g, hg⟩)
  refine ⟨x, ?_⟩
  rw [ideleSymbol_ideleNorm, hx, restrictNormal_restrictHom]

theorem restrictHom_eq_ideleSymbol (g : K.1.fixingSubgroup) (x : IdeleGroup K.1)
    (h : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x)) :
    restrictHom (E := compositum K F) g = ideleSymbol K.1 (compositum K F).1 x := by
  obtain ⟨g', hg'⟩ := restrictHom_surjective (F := K) (E := compositum K F)
    (ideleSymbol K.1 (compositum K F).1 x)
  have h' : (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 := by
    rw [h, ideleSymbol_ideleNorm, ← hg', restrictNormal_restrictHom]
  rw [← hg', eq_comm, MonoidHom.eq_iff, ker_restrictHom, Subgroup.mem_subgroupOf,
    fixingSubgroup_compositum]
  refine ⟨(g⁻¹ * g' : K.1.fixingSubgroup).2, (mem_fixingSubgroup_iff_restrictNormal_eq_one F _).2 ?_⟩
  change AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1
    ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ * (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄)) = 1
  rw [map_mul, map_inv]
  change ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1)⁻¹ * (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = 1
  rw [h', inv_mul_cancel]

end CyclotomicSymbol

end

end Sec3_22_NormResidueSymbol_CyclotomicCompositum

/-! ### 23_NormResidueSymbol.CyclotomicImage -/
section Sec3_23_NormResidueSymbol_CyclotomicImage

open NumberField IntermediateField IdeleGroup
open scoped RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield RationalSymbol RHDirect.CFT_CyclotomicCharacters.Cyclotomic

abbrev layer (m : ℕ+) : FiniteSubfield :=
  ⟨rootsOfUnityField m, inferInstance⟩

theorem rootsOfUnityField_le_mul (m n : ℕ+) :
    rootsOfUnityField m ≤ rootsOfUnityField (m * n : ℕ+) :=
  adjoin.mono ℚ _ _ fun x (hx : x ^ (m : ℕ) = 1) ↦ by
    change x ^ ((m * n : ℕ+) : ℕ) = 1
    rw [PNat.mul_coe, pow_mul, hx, one_pow]

def AgreesOn (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (τ : maxCyclotomic ≃ₐ[ℚ] maxCyclotomic) : Prop :=
  ∀ z (hz : z ∈ rootsOfUnityField m), g z = (τ ⟨z, rootsOfUnityField_le_maxCyclotomic m hz⟩ : ℚ̄)

theorem AgreesOn.of_mul {m n : ℕ+} {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} {τ : maxCyclotomic ≃ₐ[ℚ] maxCyclotomic}
    (h : AgreesOn (m * n) g τ) : AgreesOn m g τ :=
  fun z hz ↦ h z (rootsOfUnityField_le_mul m n hz)

theorem agreesOn_iff (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : IdeleGroup ℚ) :
    AgreesOn m g (reciprocityMap (IdeleClassGroup.mk ℚ x)) ↔
      g.restrictNormal (rootsOfUnityField m) = ideleSymbol ℚ (rootsOfUnityField m) x := by
  constructor
  · intro h
    refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
    rw [coe_ideleSymbol_apply]
    exact (AlgEquiv.restrictNormal_commutes g (rootsOfUnityField m) y).trans (h y y.2)
  · intro h z hz
    have h1 := AlgEquiv.restrictNormal_commutes g (rootsOfUnityField m) ⟨z, hz⟩
    rw [h] at h1
    exact h1.symm.trans (coe_ideleSymbol_apply m x ⟨z, hz⟩)

theorem cycRestrict_eq_of_forall_agreesOn {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} {τ : maxCyclotomic ≃ₐ[ℚ] maxCyclotomic}
    (h : ∀ m, AgreesOn m g τ) : cycRestrict g = τ := by
  obtain ⟨σ, rfl⟩ := cycRestrict_surjective τ
  have hfix : σ⁻¹ * g ∈ maxCyclotomic.fixingSubgroup := by
    rw [maxCyclotomic, mem_fixingSubgroup_adjoin_iff]
    rintro ζ ⟨n, hn, hζ⟩
    have h1 := h ⟨n, hn⟩ ζ (subset_adjoin ℚ _ hζ)
    rw [coe_cycRestrict_apply] at h1
    rw [AlgEquiv.mul_apply, h1, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  rw [coe_cycRestrict_apply, coe_cycRestrict_apply]
  have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix y y.2
  calc g y = σ ((σ⁻¹ * g) y) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
    _ = σ y := by rw [h2]

theorem isClosed_setOf_restrictNormal_eq (F : FiniteSubfield) [IsGalois ℚ F.1]
    (t : F.1 ≃ₐ[ℚ] F.1) : IsClosed {g : ℚ̄ ≃ₐ[ℚ] ℚ̄ | g.restrictNormal F.1 = t} := by
  by_cases h : ∃ g₀ : ℚ̄ ≃ₐ[ℚ] ℚ̄, g₀.restrictNormal F.1 = t
  · obtain ⟨g₀, hg₀⟩ := h
    have e : {g : ℚ̄ ≃ₐ[ℚ] ℚ̄ | g.restrictNormal F.1 = t} =
        (fun g ↦ g₀⁻¹ * g) ⁻¹' (F.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      ext g
      change g.restrictNormal F.1 = t ↔ g₀⁻¹ * g ∈ F.1.fixingSubgroup
      rw [mem_fixingSubgroup_iff_restrictNormal_eq_one]
      change _ ↔ AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 (g₀⁻¹ * g) = 1
      rw [map_mul, map_inv]
      change _ ↔ (g₀.restrictNormal F.1)⁻¹ * g.restrictNormal F.1 = 1
      rw [hg₀, inv_mul_eq_one, eq_comm]
    rw [e]
    exact F.1.fixingSubgroup_isClosed.preimage (continuous_const.mul continuous_id)
  · push Not at h
    have e : {g : ℚ̄ ≃ₐ[ℚ] ℚ̄ | g.restrictNormal F.1 = t} = ∅ :=
      Set.eq_empty_of_forall_notMem fun g hg ↦ h g hg
    rw [e]
    exact isClosed_empty

variable (K : FiniteSubfield)

def cycSymbol : IdeleClassGroup K.1 →* (maxCyclotomic ≃ₐ[ℚ] maxCyclotomic) :=
  reciprocityMap.comp (ideleClassNorm ℚ K.1)

theorem cycSymbol_mk (x : IdeleGroup K.1) :
    cycSymbol K (IdeleClassGroup.mk K.1 x) =
      reciprocityMap (IdeleClassGroup.mk ℚ (ideleNorm ℚ K.1 x)) := by
  rw [cycSymbol, MonoidHom.comp_apply, ideleClassNorm_mk]

theorem continuous_cycSymbol : Continuous (cycSymbol K) :=
  continuous_reciprocityMap.comp (continuous_ideleClassNorm (K := ℚ) (L := K.1))

theorem range_diagonal_le_ker_layer (m : ℕ+) :
    (diagonal ℚ).range ≤ (ideleSymbol ℚ (rootsOfUnityField m)).ker := by
  rintro _ ⟨a, rfl⟩
  exact RationalSymbol.ideleSymbol_diagonal_eq_one _ {(m : ℕ)} a

def layerSymbol (m : ℕ+) :
    IdeleClassGroup K.1 →* (rootsOfUnityField m ≃ₐ[ℚ] rootsOfUnityField m) :=
  (ideleClassSymbol (K := ℚ) (rootsOfUnityField m) (range_diagonal_le_ker_layer m)).comp
    (ideleClassNorm ℚ K.1)

theorem layerSymbol_mk (m : ℕ+) (x : IdeleGroup K.1) :
    layerSymbol K m (IdeleClassGroup.mk K.1 x) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 x) := by
  rw [layerSymbol, MonoidHom.comp_apply, ideleClassNorm_mk, ideleClassSymbol_mk]

theorem continuous_layerSymbol (m : ℕ+) : Continuous (layerSymbol K m) :=
  (continuous_ideleClassSymbol (range_diagonal_le_ker_layer m)).comp
    (continuous_ideleClassNorm (K := ℚ) (L := K.1))

theorem agreesOn_cycSymbol_iff (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (c : IdeleClassGroup K.1) :
    AgreesOn m g (cycSymbol K c) ↔ g.restrictNormal (rootsOfUnityField m) = layerSymbol K m c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
  rw [cycSymbol_mk, layerSymbol_mk, agreesOn_iff]

section Positive

variable {F : Type*} [Field F] [NumberField F]

theorem exists_infiniteEmbedding_ideleModule_eq (t : {r : ℝ // 0 < r}) :
    ∃ (w : InfinitePlace F) (z : (w.Completion)ˣ),
      IdeleGroup.ideleModule F (infiniteEmbedding w z) = t ∧
        ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (z : w.Completion) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨t, ht⟩ := t
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    have hz0 : e.symm t ≠ 0 := (map_ne_zero_iff _ e.symm.injective).2 ht.ne'
    have he : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm t) = t := by
      rw [← InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
      exact e.apply_symm_apply t
    refine ⟨w, Units.mk0 (e.symm t) hz0, Subtype.ext ?_, fun _ ↦ ?_⟩
    · rw [ideleModule_infiniteEmbedding, Units.val_mk0]
      have hn : ‖e.symm t‖ = ‖e (e.symm t)‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
      rw [hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg ht.le]
      simp [InfinitePlace.mult, hw]
    · rw [Units.val_mk0, he]
      exact ht
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have hz0 : e.symm (Real.sqrt t : ℂ) ≠ 0 :=
      (map_ne_zero_iff _ e.symm.injective).2 (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ht))
    have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    refine ⟨w, Units.mk0 _ hz0, Subtype.ext ?_, fun h ↦ absurd h hw'⟩
    rw [ideleModule_infiniteEmbedding, Units.val_mk0]
    have hn : ‖e.symm (Real.sqrt t : ℂ)‖ = ‖e (e.symm (Real.sqrt t : ℂ))‖ := by
      rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
      exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) _).symm
    rw [hn, RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
    simp [InfinitePlace.mult, hw', Real.sq_sqrt ht.le]

theorem ideleSymbol_infiniteEmbedding_eq_one (L : Type*) [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] [IsMulCommutative (L ≃ₐ[F] L)] (w : InfinitePlace F) (z : (w.Completion)ˣ)
    (hz : ∀ hw : w.IsReal, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (z : w.Completion)) :
    ideleSymbol F L (infiniteEmbedding w z) = 1 := by
  rw [ideleSymbol_infiniteEmbedding]
  by_cases hw : w.IsReal
  · obtain ⟨w'⟩ := IdeleNorm.nonempty_infinitePlacesOver L w
    rw [infiniteLocalSymbol_apply L w hw w' z, if_neg (not_lt.2 (hz hw).le)]
  · rw [infiniteLocalSymbol_of_not_isReal L w hw, MonoidHom.one_apply]

end Positive

theorem ideleSymbol_ideleNorm_eq_one (F : FiniteSubfield) [IsGalois ℚ F.1]
    [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] {x : IdeleGroup K.1}
    (h : ideleSymbol K.1 (compositum K F).1 x = 1) : ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) = 1 := by
  rw [ideleSymbol_ideleNorm, h]
  exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := (compositum K F).1) F.1)

theorem exists_mem_fixingSubgroup_cycRestrict_eq (c : IdeleClassGroup K.1) :
    ∃ g ∈ K.1.fixingSubgroup, cycRestrict g = cycSymbol K c := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  let t : ℕ+ → Set (ℚ̄ ≃ₐ[ℚ] ℚ̄) := fun m ↦ (K.1.fixingSubgroup : Set (ℚ̄ ≃ₐ[ℚ] ℚ̄)) ∩
    {g | g.restrictNormal (rootsOfUnityField m) = layerSymbol K m c}
  have hcl : ∀ m, IsClosed (t m) := fun m ↦ K.1.fixingSubgroup_isClosed.inter
    (isClosed_setOf_restrictNormal_eq (layer m) _)
  have hne : ∀ m, (t m).Nonempty := fun m ↦ by
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K.1 c
    obtain ⟨g, hg, h⟩ := exists_restrictNormal_eq_ideleSymbol K (layer m) x
    refine ⟨g, hg, ?_⟩
    change g.restrictNormal (rootsOfUnityField m) = _
    rw [layerSymbol_mk]
    exact h
  have hdir : Directed (· ⊇ ·) t := fun m n ↦ by
    refine ⟨m * n, fun g hg ↦ ⟨hg.1, ?_⟩, fun g hg ↦ ⟨hg.1, ?_⟩⟩
    · exact (agreesOn_cycSymbol_iff K m g c).1 ((agreesOn_cycSymbol_iff K _ g c).2 hg.2).of_mul
    · have h := (agreesOn_cycSymbol_iff K _ g c).2 hg.2
      rw [mul_comm] at h
      exact (agreesOn_cycSymbol_iff K n g c).1 h.of_mul
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun m ↦ (hcl m).isCompact) hcl
  rw [Set.mem_iInter] at hg
  exact ⟨g, (hg 1).1,
    cycRestrict_eq_of_forall_agreesOn fun m ↦ (agreesOn_cycSymbol_iff K m g c).2 (hg m).2⟩

theorem exists_cycSymbol_eq {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ K.1.fixingSubgroup) :
    ∃ c : IdeleClassGroup K.1, cycSymbol K c = cycRestrict g := by
  let s : ℕ+ → Set (IdeleClassGroup K.1) := fun m ↦
    (IdeleClassGroup.normOneSubgroup K.1 : Set (IdeleClassGroup K.1)) ∩
      layerSymbol K m ⁻¹' {g.restrictNormal (rootsOfUnityField m)}
  have hone : IsClosed (IdeleClassGroup.normOneSubgroup K.1 : Set (IdeleClassGroup K.1)) :=
    isClosed_singleton.preimage (IdeleClassGroup.continuous_ideleModule K.1)
  have hcl : ∀ m, IsClosed (s m) := fun m ↦
    hone.inter (isClosed_singleton.preimage (continuous_layerSymbol K m))
  have hco : ∀ m, IsCompact (s m) := fun m ↦
    (IdeleClassGroup.isCompact_normOneSubgroup K.1).inter_right
      (isClosed_singleton.preimage (continuous_layerSymbol K m))
  have hne : ∀ m, (s m).Nonempty := fun m ↦ by
    obtain ⟨x, hx⟩ := exists_ideleSymbol_eq_restrictNormal K (layer m) hg
    obtain ⟨w, z, hmod, hpos⟩ := exists_infiniteEmbedding_ideleModule_eq (F := K.1)
      (IdeleGroup.ideleModule K.1 x)
    have he : ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 (infiniteEmbedding w z)) = 1 :=
      ideleSymbol_ideleNorm_eq_one K (layer m) (ideleSymbol_infiniteEmbedding_eq_one _ w z hpos)
    refine ⟨IdeleClassGroup.mk K.1 (x * (infiniteEmbedding w z)⁻¹), ?_, ?_⟩
    · change IdeleClassGroup.ideleModule K.1 (IdeleClassGroup.mk K.1 _) = 1
      rw [IdeleClassGroup.ideleModule_mk, map_mul, map_inv, hmod, mul_inv_cancel]
    · change layerSymbol K m _ = _
      rw [layerSymbol_mk, map_mul, map_inv, map_mul, map_inv, he, inv_one, mul_one]
      exact hx
  have hdir : Directed (· ⊇ ·) s := fun m n ↦ by
    refine ⟨m * n, fun c hc ↦ ⟨hc.1, ?_⟩, fun c hc ↦ ⟨hc.1, ?_⟩⟩
    · have h := (agreesOn_cycSymbol_iff K _ g c).2 (Set.mem_singleton_iff.1 hc.2).symm
      exact Set.mem_singleton_iff.2 ((agreesOn_cycSymbol_iff K m g c).1 h.of_mul).symm
    · have h := (agreesOn_cycSymbol_iff K _ g c).2 (Set.mem_singleton_iff.1 hc.2).symm
      rw [mul_comm] at h
      exact Set.mem_singleton_iff.2 ((agreesOn_cycSymbol_iff K n g c).1 h.of_mul).symm
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed s hdir hne
    hco hcl
  rw [Set.mem_iInter] at hc
  exact ⟨c, (cycRestrict_eq_of_forall_agreesOn fun m ↦
    (agreesOn_cycSymbol_iff K m g c).2 (Set.mem_singleton_iff.1 (hc m).2).symm).symm⟩

theorem range_cycSymbol : (cycSymbol K).range = K.1.fixingSubgroup.map cycRestrict := by
  ext τ
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, hg, h⟩ := exists_mem_fixingSubgroup_cycRestrict_eq K c
    exact ⟨g, hg, h⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨c, hc⟩ := exists_cycSymbol_eq K hg
    exact ⟨c, hc⟩

def cycDegree : (maxCyclotomic ≃ₐ[ℚ] maxCyclotomic) →* Multiplicative ℤ̂ :=
  unitsDegree.comp cycCharacter.toMonoidHom

theorem cycDegree_comp_cycRestrict : cycDegree.comp cycRestrict = degree := by
  refine MonoidHom.ext fun σ ↦ ?_
  change unitsDegree (cycCharacter (cycRestrict σ)) = degree σ
  rw [degree_apply, cycCharacter_cycRestrict]

theorem map_cycDegree_range_cycSymbol :
    (cycSymbol K).range.map cycDegree = K.1.fixingSubgroup.map degree := by
  rw [range_cycSymbol, Subgroup.map_map, cycDegree_comp_cycRestrict]

end CyclotomicSymbol

end

end Sec3_23_NormResidueSymbol_CyclotomicImage

/-! ### 24_NormResidueSymbol.Cyclotomic -/
section Sec3_24_NormResidueSymbol_Cyclotomic

open NumberField IntermediateField IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield RationalSymbol RHDirect.CFT_CyclotomicCharacters.Cyclotomic

theorem exists_le_sup_rootsOfUnityField (K L : FiniteSubfield) (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) :
    ∃ m : ℕ+, L.1 ≤ K.1 ⊔ rootsOfUnityField m := by
  obtain ⟨α, hα⟩ : ∃ α : L.1,
      @IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α} = ⊤ := by
    have e : IntermediateField.algebra' L.1 = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    rw [e]
    exact Field.exists_primitive_element ℚ L.1
  have hdir : Directed (· ≤ ·) fun m : ℕ+ ↦ K.1 ⊔ rootsOfUnityField m := fun m n ↦
    ⟨m * n, sup_le_sup_left (rootsOfUnityField_le_mul m n) _,
      sup_le_sup_left (by rw [mul_comm]; exact rootsOfUnityField_le_mul n m) _⟩
  have hmem : (α : ℚ̄) ∈ ⨆ m : ℕ+, K.1 ⊔ rootsOfUnityField m := by
    rw [← sup_iSup, ← maxCyclotomic_eq_iSup]
    exact hL α.2
  rw [← SetLike.mem_coe, coe_iSup_of_directed hdir, Set.mem_iUnion] at hmem
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, fun y hy ↦ ?_⟩
  have hy' : y ∈ (@IntermediateField.adjoin ℚ _ (↥L.1) _ (IntermediateField.algebra' L.1) {α}).map
      L.1.val :=
    ⟨⟨y, hy⟩, by rw [hα]; trivial, rfl⟩
  rw [adjoin_map, Set.image_singleton] at hy'
  exact adjoin_simple_le_iff.2 hm hy'

theorem agreesOn_cycRestrict (m : ℕ+) (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) : AgreesOn m g (cycRestrict g) :=
  fun z hz ↦ (coe_cycRestrict_apply g ⟨z, rootsOfUnityField_le_maxCyclotomic m hz⟩).symm

variable (K L : FiniteSubfield) [Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

instance isGalois_of_fact : IsGalois K.1 L.1 :=
  isGalois_of_normal

omit [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] in

theorem isScalarTower_of_le (E : FiniteSubfield) [Fact (K ≤ E)] [Fact (L ≤ E)] :
    IsScalarTower K.1 L.1 E.1 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [IsMulCommutative (L.1 ≃ₐ[K.1] L.1)]

theorem ideleSymbol_diagonal_eq_one_of_le_sup (hL : L.1 ≤ K.1 ⊔ maxCyclotomic) (a : K.1ˣ) :
    ideleSymbol K.1 L.1 (diagonal K.1 a) = 1 := by
  obtain ⟨m, hm⟩ := exists_le_sup_rootsOfUnityField K L hL
  have : Fact (L ≤ compositum K (layer m)) := ⟨hm⟩
  have := isScalarTower_of_le K L (compositum K (layer m))
  have h1 : ((1 : K.1.fixingSubgroup) : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal (rootsOfUnityField m) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 (diagonal K.1 a)) := by
    rw [ideleNorm_diagonal, range_diagonal_le_ker_layer m ⟨_, rfl⟩]
    exact map_one (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) (rootsOfUnityField m))
  have hE := restrictHom_eq_ideleSymbol K (layer m) 1 (diagonal K.1 a) h1
  rw [map_one] at hE
  rw [← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]
  exact map_one (AlgEquiv.restrictNormalHom (F := K.1) (K₁ := (compositum K (layer m)).1) L.1)

theorem restrictHom_eq_ideleSymbol_of_le_sup (hL : L.1 ≤ K.1 ⊔ maxCyclotomic)
    (g : K.1.fixingSubgroup) (x : IdeleGroup K.1)
    (hg : cycRestrict (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) = cycSymbol K (IdeleClassGroup.mk K.1 x)) :
    restrictHom (E := L) g = ideleSymbol K.1 L.1 x := by
  obtain ⟨m, hm⟩ := exists_le_sup_rootsOfUnityField K L hL
  have : Fact (L ≤ compositum K (layer m)) := ⟨hm⟩
  have := isScalarTower_of_le K L (compositum K (layer m))
  have h1 : ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)).restrictNormal (rootsOfUnityField m) =
      ideleSymbol ℚ (rootsOfUnityField m) (ideleNorm ℚ K.1 x) := by
    have h := agreesOn_cycRestrict m (g : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    rw [hg, agreesOn_cycSymbol_iff, layerSymbol_mk] at h
    exact h
  have hE := restrictHom_eq_ideleSymbol K (layer m) g x h1
  rw [← restrictNormal_ideleSymbol L.1 (compositum K (layer m)).1, ← hE]
  refine AlgEquiv.ext fun y ↦ Subtype.ext ?_
  exact (congrArg Subtype.val
    (AlgEquiv.restrictNormal_commutes (restrictHom (E := compositum K (layer m)) g) L.1 y)).symm

end CyclotomicSymbol

end

end Sec3_24_NormResidueSymbol_Cyclotomic

/-! ### 25_IdeleClassGroup.Theory -/
section Sec3_25_IdeleClassGroup_Theory

open NumberField IntermediateField RHDirect.CFT_AbstractLocalReciprocity
open scoped RHDirect.CFT_AbstractLocalReciprocity

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace IdeleClassLimit

open FiniteSubfield RationalSymbol CyclotomicSymbol RHDirect.CFT_CyclotomicCharacters.Cyclotomic

def rationals : FiniteSubfield :=
  ⟨⊥, inferInstance⟩

theorem rationals_le (F : FiniteSubfield) : rationals ≤ F :=
  show (⊥ : IntermediateField ℚ ℚ̄) ≤ F.1 from bot_le

theorem fixingSubgroup_rationals :
    rationals.1.fixingSubgroup = (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  IntermediateField.fixingSubgroup_bot

def baseEquiv :
    IdeleClassGroup rationals.1 ≃* fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  (fixedEquiv rationals).trans (MulEquiv.subgroupCongr (by rw [fixingSubgroup_rationals]))

@[simp]
theorem coe_baseEquiv (c : IdeleClassGroup rationals.1) :
    (baseEquiv c : IdeleClassLimit) = of rationals c :=
  rfl

theorem ideleClassMap_self_eq (K : Type*) [Field K] [NumberField K] (c : IdeleClassGroup K) :
    ideleClassMap K K c = c :=
  ideleClassMap_injective (ideleClassMap_ideleClassMap (K := K) (L := K) (M := K) c)

def ratRingEquiv : ℚ ≃+* rationals.1 :=
  ((IntermediateField.botEquiv ℚ ℚ̄).symm : ℚ ≃ₐ[ℚ] (⊥ : IntermediateField ℚ ℚ̄)).toRingEquiv

theorem ideleClassEquiv_ratRingEquiv (c : IdeleClassGroup ℚ) :
    ideleClassEquiv ratRingEquiv c = ideleClassMap ℚ rationals.1 c := by
  have h := ideleClassEquiv_ideleClassMap_of_comm (L := ℚ) (L' := ℚ) (M := ℚ) (M' := rationals.1)
    (RingEquiv.refl ℚ) ratRingEquiv (fun l ↦ by
      rw [RingEquiv.refl_apply]
      exact (eq_ratCast (ratRingEquiv.toRingHom.comp (algebraMap ℚ ℚ)) l).trans
        (eq_ratCast (algebraMap ℚ rationals.1) l).symm) c
  rwa [ideleClassMap_self_eq, ideleClassEquiv_refl] at h

theorem ideleClassNorm_ideleClassEquiv_ratRingEquiv (c : IdeleClassGroup ℚ) :
    ideleClassNorm ℚ rationals.1 (ideleClassEquiv ratRingEquiv c) = c := by
  rw [ideleClassEquiv_ratRingEquiv, ideleClassNorm_ideleClassMap,
    show Module.finrank ℚ rationals.1 = 1 from IntermediateField.finrank_bot, pow_one]

def ratEquiv :
    IdeleClassGroup ℚ ≃* fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  (ideleClassEquiv ratRingEquiv).toMulEquiv.trans baseEquiv

theorem coe_ratEquiv (c : IdeleClassGroup ℚ) :
    (ratEquiv c : IdeleClassLimit) = of rationals (ideleClassMap ℚ rationals.1 c) := by
  rw [← ideleClassEquiv_ratRingEquiv]
  rfl

def val : fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) →* Multiplicative ℤ̂ :=
  (cycDegree.comp (cycSymbol rationals)).comp baseEquiv.symm.toMonoidHom

theorem val_baseEquiv (c : IdeleClassGroup rationals.1) :
    val (baseEquiv c) = cycDegree (cycSymbol rationals c) := by
  simp [val]

theorem val_ratEquiv (c : IdeleClassGroup ℚ) :
    val (ratEquiv c) = cycDegree (reciprocityMap c) := by
  have h : ratEquiv c = baseEquiv (ideleClassEquiv ratRingEquiv c) := MulEquiv.trans_apply _ _ c
  rw [h, val_baseEquiv, cycSymbol, MonoidHom.comp_apply,
    ideleClassNorm_ideleClassEquiv_ratRingEquiv]

theorem cycSymbol_ideleClassNorm {F : FiniteSubfield} (h : rationals ≤ F)
    (c : IdeleClassGroup F.1) :
    cycSymbol rationals (FiniteSubfield.ideleClassNorm h c) = cycSymbol F c := by
  let := algebraOfLE h
  have : IsScalarTower ℚ rationals.1 F.1 := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  rw [cycSymbol, cycSymbol, MonoidHom.comp_apply, MonoidHom.comp_apply]
  congr 1
  exact ideleClassNorm_ideleClassNorm (K := ℚ) (L := rationals.1) (M := F.1) c

theorem val_norm_of {U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)} [(U.subgroupOf ⊤).FiniteIndex] {F : FiniteSubfield}
    (hU : U = F.1.fixingSubgroup) (c : IdeleClassGroup F.1)
    (hc : of F c ∈ fixedModule IdeleClassLimit U) :
    val (norm IdeleClassLimit ⊤ U ⟨of F c, hc⟩) = cycDegree (cycSymbol F c) := by
  have h := coe_norm_of_eq (K := ⊤) (rationals_le F) fixingSubgroup_rationals.symm hU c hc
  have he : norm IdeleClassLimit ⊤ U ⟨of F c, hc⟩ =
      baseEquiv (FiniteSubfield.ideleClassNorm (rationals_le F) c) :=
    Subtype.ext h
  rw [he, val_baseEquiv, cycSymbol_ideleClassNorm]

theorem range_cycDegree_comp_cycSymbol_rationals :
    (cycDegree.comp (cycSymbol rationals)).range = ⊤ := by
  rw [MonoidHom.range_comp, map_cycDegree_range_cycSymbol, fixingSubgroup_rationals,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact degree_surjective

theorem val_surjective : Function.Surjective val := by
  intro z
  obtain ⟨c, hc⟩ := MonoidHom.range_eq_top.1 range_cycDegree_comp_cycSymbol_rationals z
  exact ⟨baseEquiv c, by rw [val_baseEquiv]; exact hc⟩

theorem range_val : val.range = ⊤ :=
  MonoidHom.range_eq_top.2 val_surjective

theorem inertiaDegree_ne_zero (F : FiniteSubfield) : inertiaDegree degree F.1.fixingSubgroup ≠ 0 :=
  Nat.pos_iff_ne_zero.1 (Nat.pos_of_dvd_of_pos (Subgroup.index_map_dvd _ degree_surjective)
    (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero)))

theorem range_cycDegree_comp_cycSymbol (F : FiniteSubfield) :
    (cycDegree.comp (cycSymbol F)).range =
      (powMonoidHom (inertiaDegree degree F.1.fixingSubgroup) :
        Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
  rw [MonoidHom.range_comp, map_cycDegree_range_cycSymbol]
  ext x
  rw [ProfiniteInteger.mem_of_index_ne_zero (inertiaDegree_ne_zero F)]
  rfl

theorem range_val_comp_norm (U : OpenSubgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :
    (val.comp (norm IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))
      (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)))).range =
      val.range.map (powMonoidHom (inertiaDegree degree (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)))) := by
  set F := ofOpenSubgroup U
  have hU : (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) = F.1.fixingSubgroup := (fixingSubgroup_ofOpenSubgroup U).symm
  have hR := range_cycDegree_comp_cycSymbol F
  rw [← hU] at hR
  rw [range_val, ← MonoidHom.range_eq_map, ← hR]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨c, hc⟩ : (a : IdeleClassLimit) ∈ (of F).range := by
      rw [← fixedModule_openSubgroup U]
      exact a.2
    refine ⟨c, ?_⟩
    have hc' : of F c ∈ fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [hc]; exact a.2
    have ha' : a = ⟨of F c, hc'⟩ := Subtype.ext hc.symm
    rw [ha']
    exact (val_norm_of hU c hc').symm
  · rintro ⟨c, rfl⟩
    have hc' : of F c ∈ fixedModule IdeleClassLimit (U : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) := by
      rw [fixedModule_openSubgroup]; exact ⟨c, rfl⟩
    exact ⟨⟨of F c, hc'⟩, val_norm_of hU c hc'⟩

theorem exists_eq_intCast_add_nsmul (n : ℕ) (hn : 0 < n)
    (a : fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))) :
    ∃ (m : ℤ) (b : fixedModule IdeleClassLimit (⊤ : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄))),
      Multiplicative.toAdd (val a) = (m : ℤ̂) + n • Multiplicative.toAdd (val b) := by
  set N : ℕ+ := ⟨n, hn⟩
  set x := Multiplicative.toAdd (val a)
  set k : ℕ := (ProfiniteInteger.proj N x).val
  have h0 : ProfiniteInteger.proj N (x - (k : ℤ̂)) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨y, hy⟩ := ProfiniteInteger.exists_eq_nsmul_of_proj_eq_zero h0
  obtain ⟨b, hb⟩ := val_surjective (Multiplicative.ofAdd y)
  refine ⟨k, b, ?_⟩
  rw [hb, toAdd_ofAdd, Int.cast_natCast]
  change x = (k : ℤ̂) + (N : ℕ) • y
  rw [← hy]
  abel

def classFieldTheory : ClassFieldTheory (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit where
  deg := degree
  continuous_deg := continuous_degree
  surjective_deg := degree_surjective
  val := val
  intCast_mem_range_val _ := val_surjective _
  exists_eq_intCast_add_nsmul := exists_eq_intCast_add_nsmul
  range_val_comp_norm := range_val_comp_norm
  isDiscreteModule := inferInstance
  classFieldAxiom := classFieldAxiom

@[simp]
theorem classFieldTheory_deg : classFieldTheory.deg = degree :=
  rfl

theorem classFieldTheory_val (c : IdeleClassGroup ℚ) :
    classFieldTheory.val (ratEquiv c) = cycDegree (reciprocityMap c) :=
  val_ratEquiv c

theorem classFieldTheory_val_surjective : Function.Surjective classFieldTheory.val :=
  val_surjective

end IdeleClassLimit

end

end Sec3_25_IdeleClassGroup_Theory

end RHDirect.CFT.Global
