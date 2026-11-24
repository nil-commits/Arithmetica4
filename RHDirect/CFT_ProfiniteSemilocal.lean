import RHDirect.Stage13CFT_IdeleNormResidue
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Algebra.Equiv
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.NormTrace
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# RHDirect.CFT_ProfiniteSemilocal

Global Class Field Theory Pillar:
1. Profinite Galois Modules, Finite & Profinite Kummer Correspondence, and Restricted Ramification
   (`ProfCoh`).
2. Semilocal Algebras for Finite & Infinite Places (`SemiLocal`, `InfinitePlace`):
   `K_v ⊗_K L ≃ ∏_{w|v} L_w`, local-global trace & norm decomposition
   `N_{L/K}(x) = ∏_{w|v} N_{L_w/K_v}(x)`, and Galois action on completions.
3. Archimedean Local Norm Index, Local Symbol, and Herbrand Quotient (`InfinitePlace`):
   `[K_vˣ : N(L_wˣ)] = 1` or `2` and `h(L_wˣ) = [L_w : K_v]`.
4. Adele Ring Topology, Weak Approximation, Base Change `L ⊗_K 𝔸_K ≃ₜ 𝔸_L`, Idele Norms,
   and Galois Action on `𝔸_L`, `IdeleGroup L`, and `IdeleClassGroup L` (`AdeleBaseChange`,
   `IdeleGalois`), built directly on `RHDirect.Stage13CFT_IdeleNormResidue`.
-/

noncomputable section

namespace RHDirect.CFT_ProfiniteSemilocal

open RHDirect.Stage13CFT_IdeleNormResidue

/-! ## Part 1: Profinite Galois Modules, Kummer Correspondence & Restricted Ramification -/

namespace ProfCoh

section DiscreteModules

open CategoryTheory

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]

@[simp]
theorem mem_stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

variable [TopologicalSpace G]

class IsDiscreteRep (A : Rep.{w} k G) : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (stabilizer A.ρ a : Set G)

theorem isOpen_stabilizer (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) :=
  IsDiscreteRep.isOpen_stabilizer a

theorem isDiscreteRep_iff (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) :=
  ⟨fun h => h.isOpen_stabilizer, fun h => ⟨h⟩⟩

variable (k G) in
def isDiscreteRep : ObjectProperty (Rep.{w} k G) := fun A => IsDiscreteRep A

@[simp]
theorem isDiscreteRep_apply (A : Rep.{w} k G) : isDiscreteRep k G A ↔ IsDiscreteRep A :=
  Iff.rfl

variable (k G) in
abbrev DiscreteRep := (isDiscreteRep.{w} k G).FullSubcategory

instance (A : DiscreteRep.{w} k G) : IsDiscreteRep A.obj := A.property

end DiscreteModules

section GaloisModules

universe w u v

section IntRep

variable {G : Type v} [Monoid G]

def intRep {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) :
    Representation (ULift.{w} ℤ) G V where
  toFun g :=
    { toFun := φ g
      map_add' := map_add (φ g)
      map_smul' := fun r x => by
        change φ g (r.down • x) = r.down • φ g x
        exact map_zsmul (φ g) r.down x }
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp]
theorem intRep_apply {V : Type u} [AddCommGroup V] (φ : G →* AddMonoid.End V) (g : G) (x : V) :
    intRep.{w} φ g x = φ g x :=
  rfl

def intRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation (ULift.{w} ℤ) G (Additive M) :=
  intRep.{w} ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

@[simp]
theorem intRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    intRepOfMonoidEnd.{w} φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl

def zRepOfMonoidEnd {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) :
    Representation ℤ G (Additive M) :=
  (addMonoidEndRingEquivInt (Additive M) : AddMonoid.End (Additive M) →* _).comp
    ((monoidEndToAdditive M : Monoid.End M →* AddMonoid.End (Additive M)).comp φ)

@[simp]
theorem zRepOfMonoidEnd_apply {M : Type u} [CommGroup M] (φ : G →* Monoid.End M) (g : G)
    (x : Additive M) :
    zRepOfMonoidEnd φ g x = Additive.ofMul (φ g x.toMul) :=
  rfl

end IntRep

section GaloisDefs

variable (K : Type*) (L : Type u) [Field K] [Field L] [Algebra K L]

def galUnitsHom : Gal(L/K) →* Monoid.End Lˣ where
  toFun σ := Units.map (σ : L →* L)
  map_one' := by ext u; rfl
  map_mul' σ τ := by ext u; rfl

@[simp]
theorem coe_galUnitsHom_apply (σ : Gal(L/K)) (u : Lˣ) :
    ((galUnitsHom K L σ u : Lˣ) : L) = σ u :=
  rfl

def galRootsOfUnityHom (n : ℕ) : Gal(L/K) →* Monoid.End (rootsOfUnity n L) where
  toFun σ := restrictRootsOfUnity σ n
  map_one' := by ext ζ; rfl
  map_mul' σ τ := by ext ζ; rfl

@[simp]
theorem coe_galRootsOfUnityHom_apply (n : ℕ) (σ : Gal(L/K)) (ζ : rootsOfUnity n L) :
    (((galRootsOfUnityHom K L n σ ζ : Lˣ)) : L) = σ (ζ : Lˣ) :=
  rfl

abbrev galAdd : Rep.{u} K Gal(L/K) := Rep.ofDistribMulAction K Gal(L/K) L

abbrev galAddInt : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRep.{w} (DistribMulAction.toAddMonoidEnd Gal(L/K) L))

abbrev galUnits : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galUnitsHom K L))

abbrev galRootsOfUnity (n : ℕ) : Rep.{u} (ULift.{w} ℤ) Gal(L/K) :=
  Rep.of (intRepOfMonoidEnd.{w} (galRootsOfUnityHom K L n))

abbrev galAddZ : Rep.{u} ℤ Gal(L/K) := Rep.ofDistribMulAction ℤ Gal(L/K) L

abbrev galUnitsZ : Rep.{u} ℤ Gal(L/K) := Rep.of (zRepOfMonoidEnd (galUnitsHom K L))

abbrev galRootsOfUnityZ (n : ℕ) : Rep.{u} ℤ Gal(L/K) :=
  Rep.of (zRepOfMonoidEnd (galRootsOfUnityHom K L n))

variable {K L}

@[simp] theorem galAdd_ρ_apply (σ : Gal(L/K)) (x : L) : (galAdd K L).ρ σ x = σ x := rfl
@[simp] theorem galAddInt_ρ_apply (σ : Gal(L/K)) (x : L) : (galAddInt.{w} K L).ρ σ x = σ x := rfl
@[simp] theorem galAddZ_ρ_apply (σ : Gal(L/K)) (x : L) : (galAddZ K L).ρ σ x = σ x := rfl

@[simp]
theorem galUnits_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnits.{w} K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) := rfl

@[simp]
theorem galUnitsZ_ρ_apply (σ : Gal(L/K)) (x : Additive Lˣ) :
    (galUnitsZ K L).ρ σ x = Additive.ofMul (galUnitsHom K L σ x.toMul) := rfl

@[simp]
theorem galRootsOfUnity_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnity.{w} K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) := rfl

@[simp]
theorem galRootsOfUnityZ_ρ_apply (n : ℕ) (σ : Gal(L/K)) (x : Additive (rootsOfUnity n L)) :
    (galRootsOfUnityZ K L n).ρ σ x = Additive.ofMul (galRootsOfUnityHom K L n σ x.toMul) := rfl

end GaloisDefs

section GaloisDiscrete

open IntermediateField

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

theorem galois_compactSpace (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    CompactSpace Gal(L/K) := inferInstance

theorem galois_t2Space (K L : Type*) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] :
    T2Space Gal(L/K) := inferInstance

theorem galois_isProfinite (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    CompactSpace Gal(L/K) ∧ T2Space Gal(L/K) ∧ TotallyDisconnectedSpace Gal(L/K) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem apply_eq_of_mem_fixingSubgroup_adjoin {x : L} {σ : Gal(L/K)}
    (hσ : σ ∈ (K⟮x⟯).fixingSubgroup) : σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (mem_adjoin_simple_self K x)

theorem isOpen_of_forall_apply_eq_mem [Algebra.IsIntegral K L] (H : Subgroup Gal(L/K)) (x : L)
    (h : ∀ σ : Gal(L/K), σ x = x → σ ∈ H) : IsOpen (H : Set Gal(L/K)) := by
  have : FiniteDimensional K K⟮x⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact Subgroup.isOpen_mono (fun σ hσ => h σ (apply_eq_of_mem_fixingSubgroup_adjoin hσ))
    (fixingSubgroup_isOpen K⟮x⟯)

variable [Algebra.IsIntegral K L]

instance isDiscreteRep_galAdd : IsDiscreteRep (galAdd K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galAddInt : IsDiscreteRep (galAddInt.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galAddZ : IsDiscreteRep (galAddZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ (x : L) fun _ h => h⟩

instance isDiscreteRep_galUnits : IsDiscreteRep (galUnits.{w} K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnits_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩

instance isDiscreteRep_galUnitsZ : IsDiscreteRep (galUnitsZ K L) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _ ((Additive.toMul x : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galUnitsZ_ρ_apply]
    change Additive.ofMul (galUnitsHom K L σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Units.ext h⟩

instance isDiscreteRep_galRootsOfUnity (n : ℕ) : IsDiscreteRep (galRootsOfUnity.{w} K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnity_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩

instance isDiscreteRep_galRootsOfUnityZ (n : ℕ) : IsDiscreteRep (galRootsOfUnityZ K L n) :=
  ⟨fun x => isOpen_of_forall_apply_eq_mem _
    (((Additive.toMul x : rootsOfUnity n L) : Lˣ) : L) fun σ h => by
    rw [mem_stabilizer, galRootsOfUnityZ_ρ_apply]
    change Additive.ofMul (galRootsOfUnityHom K L n σ (Additive.toMul x)) = x
    rw [← ofMul_toMul x]
    congr 1
    exact Subtype.ext (Units.ext h)⟩

end GaloisDiscrete

section GaloisFixedField

open IntermediateField InfiniteGalois

variable {K : Type*} {L : Type u} [Field K] [Field L] [Algebra K L]

theorem isOpen_fixingSubgroup_finiteGalois (E : FiniteGaloisIntermediateField K L) :
    IsOpen (E.fixingSubgroup : Set Gal(L/K)) :=
  fixingSubgroup_isOpen E.toIntermediateField

theorem normal_fixingSubgroup_finiteGalois [IsGalois K L] (E : FiniteGaloisIntermediateField K L) :
    E.fixingSubgroup.Normal :=
  (normal_iff_isGalois E.toIntermediateField).2 E.isGalois

section OpenNormal

variable [IsGalois K L]

def fixingOpenNormalSubgroup (E : FiniteGaloisIntermediateField K L) :
    OpenNormalSubgroup Gal(L/K) where
  toSubgroup := E.fixingSubgroup
  isOpen' := isOpen_fixingSubgroup_finiteGalois E
  isNormal' := normal_fixingSubgroup_finiteGalois E

@[simp]
theorem coe_fixingOpenNormalSubgroup (E : FiniteGaloisIntermediateField K L) :
    (fixingOpenNormalSubgroup E : Subgroup Gal(L/K)) = E.fixingSubgroup :=
  rfl

variable (U : OpenNormalSubgroup Gal(L/K))

def openNormalToClosed : ClosedSubgroup Gal(L/K) :=
  ⟨U.toSubgroup, U.toOpenSubgroup.isClosed⟩

instance : (openNormalToClosed U).Normal :=
  U.isNormal'

@[simp]
theorem fixingSubgroup_fixedField_openNormalSubgroup :
    (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup = U :=
  fixingSubgroup_fixedField (openNormalToClosed U)

instance finiteDimensional_fixedField_openNormalSubgroup :
    FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (isOpen_iff_finite _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isOpen

instance isGalois_fixedField_openNormalSubgroup :
    IsGalois K (fixedField (U : Subgroup Gal(L/K))) := by
  refine (normal_iff_isGalois _).1 ?_
  rw [fixingSubgroup_fixedField_openNormalSubgroup]
  exact U.isNormal'

def fixedFiniteGalois : FiniteGaloisIntermediateField K L where
  toIntermediateField := fixedField (U : Subgroup Gal(L/K))

@[simp]
theorem fixedFiniteGalois_toIntermediateField :
    (fixedFiniteGalois U).toIntermediateField = fixedField (U : Subgroup Gal(L/K)) :=
  rfl

def quotientEquivGal :
    Gal(L/K) ⧸ (U : Subgroup Gal(L/K)) ≃* Gal(fixedField (U : Subgroup Gal(L/K))/K) :=
  normalAutEquivQuotient (openNormalToClosed U)

@[simp]
theorem quotientEquivGal_mk_apply (σ : Gal(L/K)) (x : fixedField (U : Subgroup Gal(L/K))) :
    ((quotientEquivGal U (σ : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) x : _) : L) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x

omit [IsGalois K L] in
theorem mem_invariants_galAdd_iff (x : L) :
    x ∈ Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ↔
      x ∈ fixedField (U : Subgroup Gal(L/K)) :=
  ⟨fun h σ => h σ, fun h σ => h σ⟩

omit [IsGalois K L] in
def invariantsGalAddEquiv :
    Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype) ≃ₗ[K]
      fixedField (U : Subgroup Gal(L/K)) where
  toFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).1 x.2⟩
  invFun x := ⟨x.1, (mem_invariants_galAdd_iff U x.1).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem invariantsGalAddEquiv_quotientToInvariants (q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
    (x : Representation.invariants ((galAdd K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    invariantsGalAddEquiv U (((galAdd K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q x) =
      quotientEquivGal U q (invariantsGalAddEquiv U x) := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply Subtype.ext
    rw [quotientEquivGal_mk_apply]
    rfl

@[simp]
theorem fixingOpenNormalSubgroup_fixedFiniteGalois :
    fixingOpenNormalSubgroup (fixedFiniteGalois U) = U := by
  ext σ
  change σ ∈ (fixedField (U : Subgroup Gal(L/K))).fixingSubgroup ↔ σ ∈ (U : Subgroup Gal(L/K))
  rw [fixingSubgroup_fixedField_openNormalSubgroup]

@[simp]
theorem fixedFiniteGalois_fixingOpenNormalSubgroup (E : FiniteGaloisIntermediateField K L) :
    fixedFiniteGalois (fixingOpenNormalSubgroup E) = E :=
  FiniteGaloisIntermediateField.val_injective (fixedField_fixingSubgroup E.toIntermediateField)

def openNormalSubgroupEquiv :
    OpenNormalSubgroup Gal(L/K) ≃o (FiniteGaloisIntermediateField K L)ᵒᵈ where
  toFun U := OrderDual.toDual (fixedFiniteGalois U)
  invFun E := fixingOpenNormalSubgroup (OrderDual.ofDual E)
  left_inv U := fixingOpenNormalSubgroup_fixedFiniteGalois U
  right_inv E := fixedFiniteGalois_fixingOpenNormalSubgroup (OrderDual.ofDual E)
  map_rel_iff' {U V} := by
    change fixedField (V : Subgroup Gal(L/K)) ≤ fixedField (U : Subgroup Gal(L/K)) ↔ U ≤ V
    rw [le_iff_le, fixingSubgroup_fixedField_openNormalSubgroup]
    exact Iff.rfl

@[simp]
theorem openNormalSubgroupEquiv_apply (U : OpenNormalSubgroup Gal(L/K)) :
    (OrderDual.ofDual (openNormalSubgroupEquiv U)).toIntermediateField =
      fixedField (U : Subgroup Gal(L/K)) :=
  rfl

@[simp]
theorem coe_openNormalSubgroupEquiv_symm_apply (E : FiniteGaloisIntermediateField K L) :
    ((openNormalSubgroupEquiv.symm (OrderDual.toDual E) : OpenNormalSubgroup Gal(L/K)) :
      Subgroup Gal(L/K)) = E.fixingSubgroup :=
  rfl

theorem exists_finiteGalois_le (E : IntermediateField K L) [FiniteDimensional K E] :
    ∃ F : FiniteGaloisIntermediateField K L, E ≤ F.toIntermediateField :=
  ⟨{ toIntermediateField := normalClosure K E L
     finiteDimensional := normalClosure.is_finiteDimensional K E L
     isGalois := IsGalois.normalClosure K E L }, le_normalClosure E⟩

theorem exists_finiteGalois_mem (x : L) :
    ∃ F : FiniteGaloisIntermediateField K L, x ∈ F.toIntermediateField :=
  ⟨FiniteGaloisIntermediateField.adjoin K {x},
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)⟩

end OpenNormal

end GaloisFixedField

end GaloisModules

/-! ### Kummer Basic, Finite & Correspondence -/

section KummerBasic

open Polynomial

section Defs

variable (K : Type*) [Field K] (n : ℕ)

def unitsPow : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range

abbrev UnitsModPow : Type _ := Kˣ ⧸ unitsPow K n

variable {K n} in
lemma mem_unitsPow {a : Kˣ} : a ∈ unitsPow K n ↔ ∃ b : Kˣ, b ^ n = a := by
  simp [unitsPow]

lemma UnitsModPow.pow_eq_one (x : UnitsModPow K n) : x ^ n = 1 := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact mem_unitsPow.mpr ⟨a, rfl⟩

variable (L : Type*) [Field L] [Algebra K L]

def unitsPowIn : Subgroup Kˣ := (unitsPow L n).comap (Units.map (algebraMap K L : K →* L))

variable {K n L} in
lemma mem_unitsPowIn {a : Kˣ} : a ∈ unitsPowIn K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  simp only [unitsPowIn, Subgroup.mem_comap, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa [Units.ext_iff] using congrArg Units.val hb⟩
  · rintro ⟨α, hα⟩
    by_cases h0 : α = 0
    · have hn : n = 0 := by
        by_contra hn
        rw [h0, zero_pow hn] at hα
        exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
      subst hn
      refine ⟨1, ?_⟩
      ext
      simpa using hα
    · exact ⟨Units.mk0 α h0, by ext; simpa using hα⟩

lemma unitsPow_le_unitsPowIn : unitsPow K n ≤ unitsPowIn K n L := by
  intro a ha
  obtain ⟨b, rfl⟩ := mem_unitsPow.mp ha
  exact mem_unitsPowIn.mpr ⟨algebraMap K L b, by simp⟩

def kummerGroup : Subgroup (UnitsModPow K n) :=
  (unitsPowIn K n L).map (QuotientGroup.mk' (unitsPow K n))

variable {K n L} in
lemma mk_mem_kummerGroup {a : Kˣ} :
    (a : UnitsModPow K n) ∈ kummerGroup K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by
  rw [← mem_unitsPowIn]
  constructor
  · rintro ⟨b, hb, hba⟩
    obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp hba)
    have : a = b * c ^ n := by rw [hc]; group
    rw [this]
    exact mul_mem hb (unitsPow_le_unitsPowIn K n L (mem_unitsPow.mpr ⟨c, rfl⟩))
  · intro ha
    exact ⟨a, ha, rfl⟩

def toKummerGroup : unitsPowIn K n L →* kummerGroup K n L :=
  ((QuotientGroup.mk' (unitsPow K n)).comp (unitsPowIn K n L).subtype).codRestrict _
    (fun a => Subgroup.mem_map_of_mem _ a.2)

lemma toKummerGroup_surjective : Function.Surjective (toKummerGroup K n L) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

lemma ker_toKummerGroup :
    (toKummerGroup K n L).ker = (unitsPow K n).subgroupOf (unitsPowIn K n L) := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (N := unitsPow K n)]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def kummerGroupEquiv :
    (unitsPowIn K n L ⧸ (unitsPow K n).subgroupOf (unitsPowIn K n L)) ≃* kummerGroup K n L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toKummerGroup K n L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toKummerGroup_surjective K n L))

end Defs

section RootsOfUnity

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {L : Type*} [Field L] [Algebra K L]

lemma exists_algebraMap_eq_of_pow_eq_one {x : L} (hx : x ^ n = 1) :
    ∃ ζ : rootsOfUnity n K, algebraMap K L ((ζ : Kˣ) : K) = x := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, hi⟩ := (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hx
  refine ⟨⟨(hζ.isUnit (NeZero.ne n)).unit ^ i, ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity', Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← pow_mul, mul_comm,
      pow_mul, hζ.pow_eq_one, one_pow]
  · simpa using hi

lemma algHom_apply_eq_self_of_pow_eq_one {x : L} (hx : x ^ n = 1) (σ : L →ₐ[K] L) :
    σ x = x := by
  obtain ⟨ζ, rfl⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hx
  exact σ.commutes _

omit [HasEnoughRootsOfUnity K n] in
lemma ne_zero_of_pow_eq_algebraMap {a : Kˣ} {α : L} (hα : α ^ n = algebraMap K L a) : α ≠ 0 := by
  rintro rfl
  rw [zero_pow (NeZero.ne n)] at hα
  exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm

end RootsOfUnity

section Pairing

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]

lemma exists_kummer_value (σ : Gal(L/K)) (x : kummerGroup K n L) :
    ∃ ζ : rootsOfUnity n K, ∀ a : Kˣ, (a : UnitsModPow K n) = x →
      ∀ α : L, α ^ n = algebraMap K L a → σ α = algebraMap K L ((ζ : Kˣ) : K) * α := by
  obtain ⟨x, a₀, ha₀, rfl⟩ := x
  obtain ⟨α₀, hα₀⟩ := mem_unitsPowIn.mp ha₀
  have hα₀0 : α₀ ≠ 0 := ne_zero_of_pow_eq_algebraMap hα₀
  have hσ : (σ α₀ / α₀) ^ n = 1 := by
    rw [div_pow, ← map_pow, hα₀, AlgEquiv.commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).mpr a₀.ne_zero
  obtain ⟨ζ, hζ⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hσ
  refine ⟨ζ, fun a ha α hα => ?_⟩
  obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp ha)
  set γ := algebraMap K L (c : K) with hγ
  have hγ0 : γ ≠ 0 := (map_ne_zero (algebraMap K L)).mpr c.ne_zero
  have ha0 : algebraMap K L (a : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr a.ne_zero
  have ha' : algebraMap K L (a₀ : K) = algebraMap K L (a : K) * γ ^ n := by
    have h1 : (c : K) ^ n = (a : K)⁻¹ * (a₀ : K) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
        using congrArg Units.val hc
    have h2 : (a₀ : K) = (a : K) * (c : K) ^ n := by
      rw [h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
    rw [h2, map_mul, map_pow]
  have hη : (α * γ / α₀) ^ n = 1 := by
    rw [div_pow, mul_pow, hα, hα₀, ha']
    exact div_self (mul_ne_zero ha0 (pow_ne_zero _ hγ0))
  have hfix : σ (α * γ / α₀) = α * γ / α₀ :=
    algHom_apply_eq_self_of_pow_eq_one (K := K) hη (σ : L →ₐ[K] L)
  have hσγ : σ γ = γ := σ.commutes _
  have hσα₀ : σ α₀ = algebraMap K L ((ζ : Kˣ) : K) * α₀ := by
    rw [hζ, div_mul_cancel₀ _ hα₀0]
  have hσα₀0 : σ α₀ ≠ 0 := (map_ne_zero σ).mpr hα₀0
  have key : σ α * γ / σ α₀ = α * γ / α₀ := by
    rw [← hfix, map_div₀, map_mul, hσγ]
  calc σ α = (σ α * γ / σ α₀) * (σ α₀ / γ) := by field_simp
    _ = (α * γ / α₀) * (algebraMap K L ((ζ : Kˣ) : K) * α₀ / γ) := by rw [key, hσα₀]
    _ = algebraMap K L ((ζ : Kˣ) : K) * α := by field_simp

def kummerPairing (σ : Gal(L/K)) (x : kummerGroup K n L) : rootsOfUnity n K :=
  (exists_kummer_value K n L σ x).choose

variable {K n L}

lemma kummerPairing_spec (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    σ α = algebraMap K L ((kummerPairing K n L σ x : Kˣ) : K) * α :=
  (exists_kummer_value K n L σ x).choose_spec a ha α hα

lemma kummerPairing_eq_of_apply (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a)
    (ζ : rootsOfUnity n K) (h : σ α = algebraMap K L ((ζ : Kˣ) : K) * α) :
    kummerPairing K n L σ x = ζ := by
  have h' := kummerPairing_spec σ x ha hα
  rw [h] at h'
  have := mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hα) h'
  ext
  exact ((algebraMap K L).injective this).symm

lemma kummerPairing_eq_one_iff (σ : Gal(L/K)) (x : kummerGroup K n L) {a : Kˣ}
    (ha : (a : UnitsModPow K n) = x) {α : L} (hα : α ^ n = algebraMap K L a) :
    kummerPairing K n L σ x = 1 ↔ σ α = α := by
  constructor
  · intro h
    rw [kummerPairing_spec σ x ha hα, h]
    simp
  · intro h
    exact kummerPairing_eq_of_apply σ x ha hα 1 (by rw [h]; simp)

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_rep (x : kummerGroup K n L) :
    ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ ∃ α : L, α ^ n = algebraMap K L a := by
  obtain ⟨x, a, ha, rfl⟩ := x
  exact ⟨a, rfl, mem_unitsPowIn.mp ha⟩

lemma kummerPairing_mul_left (σ τ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairing K n L (σ * τ) x = kummerPairing K n L σ x * kummerPairing K n L τ x := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  apply kummerPairing_eq_of_apply (σ * τ) x ha hα
  rw [AlgEquiv.mul_apply, kummerPairing_spec τ x ha hα, map_mul, AlgEquiv.commutes,
    kummerPairing_spec σ x ha hα]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

lemma kummerPairing_mul_right (σ : Gal(L/K)) (x y : kummerGroup K n L) :
    kummerPairing K n L σ (x * y) = kummerPairing K n L σ x * kummerPairing K n L σ y := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  obtain ⟨b, hb, β, hβ⟩ := exists_rep y
  have hab : ((a * b : Kˣ) : UnitsModPow K n) =
      ((x * y : kummerGroup K n L) : UnitsModPow K n) := by
    rw [QuotientGroup.mk_mul, ha, hb]
    rfl
  have hαβ : (α * β) ^ n = algebraMap K L ((a * b : Kˣ) : K) := by
    rw [mul_pow, hα, hβ, Units.val_mul, map_mul]
  apply kummerPairing_eq_of_apply σ (x * y) hab hαβ
  rw [map_mul, kummerPairing_spec σ x ha hα, kummerPairing_spec σ y hb hβ]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

lemma kummerPairing_one_left (x : kummerGroup K n L) : kummerPairing K n L 1 x = 1 := by
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  exact (kummerPairing_eq_one_iff 1 x ha hα).mpr rfl

lemma kummerPairing_one_right (σ : Gal(L/K)) : kummerPairing K n L σ 1 = 1 := by
  have h := kummerPairing_mul_right σ (1 : kummerGroup K n L) 1
  rw [mul_one] at h
  exact (mul_eq_left.mp h.symm)

variable (K n L)

def kummerPairingLeft : Gal(L/K) →* (kummerGroup K n L →* rootsOfUnity n K) where
  toFun σ :=
    { toFun := kummerPairing K n L σ
      map_one' := kummerPairing_one_right σ
      map_mul' := kummerPairing_mul_right σ }
  map_one' := by ext x : 1; exact kummerPairing_one_left x
  map_mul' σ τ := by ext x : 1; exact kummerPairing_mul_left σ τ x

def kummerPairingRight : kummerGroup K n L →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun x :=
    { toFun := fun σ => kummerPairing K n L σ x
      map_one' := kummerPairing_one_left x
      map_mul' := fun σ τ => kummerPairing_mul_left σ τ x }
  map_one' := by ext σ : 1; exact kummerPairing_one_right σ
  map_mul' x y := by ext σ : 1; exact kummerPairing_mul_right σ x y

@[simp] lemma kummerPairingLeft_apply (σ : Gal(L/K)) (x : kummerGroup K n L) :
    kummerPairingLeft K n L σ x = kummerPairing K n L σ x := rfl

@[simp] lemma kummerPairingRight_apply (x : kummerGroup K n L) (σ : Gal(L/K)) :
    kummerPairingRight K n L x σ = kummerPairing K n L σ x := rfl

end Pairing

section Field

variable (K : Type*) [Field K] (n : ℕ)

def kummerField (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup (UnitsModPow K n)) :
    IntermediateField K Ω :=
  IntermediateField.adjoin K
    {α : Ω | ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K Ω a}

end Field

end KummerBasic

section KummerFinite

open Polynomial

section Characters

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

def monoidHomRootsOfUnityEquiv (G : Type*) [Group G] (hG : ∀ g : G, g ^ n = 1) :
    (G →* rootsOfUnity n K) ≃ (G →* Kˣ) where
  toFun φ := (rootsOfUnity n K).subtype.comp φ
  invFun ψ := ψ.codRestrict (rootsOfUnity n K) fun g => by
    rw [mem_rootsOfUnity, ← map_pow, hG g, map_one]
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

lemma card_monoidHom_rootsOfUnity (G : Type*) [CommGroup G] [Finite G]
    (hG : ∀ g : G, g ^ n = 1) : Nat.card (G →* rootsOfUnity n K) = Nat.card G := by
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  rw [Nat.card_congr (monoidHomRootsOfUnityEquiv G hG),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]

lemma finite_monoidHom_rootsOfUnity (G : Type*) [Group G] [Finite G] :
    Finite (G →* rootsOfUnity n K) :=
  .of_injective _ DFunLike.coe_injective

end Characters

section FiniteKummer

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma kummerGroup_pow_eq_one (x : kummerGroup K n L) : x ^ n = 1 :=
  Subtype.ext (UnitsModPow.pow_eq_one K n x.1)

variable {K n L}

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_eigenvector_of_character [FiniteDimensional K L] (χ : Gal(L/K) →* Kˣ) :
    ∃ β : Lˣ, ∀ σ : Gal(L/K), σ (β : L) = algebraMap K L (χ σ : K) * β := by
  let f : Gal(L/K) → Lˣ := fun σ => Units.map (algebraMap K L : K →* L) (χ σ)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    ext
    simp only [f, map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def,
      AlgEquiv.commutes]
    ring
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, fun σ => ?_⟩
  have := congrArg Units.val (hβ σ)
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
    f] at this
  rw [← this, div_mul_cancel₀ _ β.ne_zero]

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_kummer_eigenvector [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (χ : Gal(L/K) →* Kˣ) :
    ∃ a : Kˣ, ∃ β : L, β ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ β = algebraMap K L (χ σ : K) * β := by
  obtain ⟨β, hβ⟩ := exists_eigenvector_of_character χ
  have hfix : ∀ σ : Gal(L/K), σ ((β : L) ^ n) = (β : L) ^ n := by
    intro σ
    rw [map_pow, hβ σ, mul_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ, map_one, Units.val_one, map_one, one_mul]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) _).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact pow_ne_zero n β.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, β, hb.symm, hβ⟩

variable (K n L)

theorem kummerPairingRight_injective [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (kummerPairingRight K n L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  have hfix : ∀ σ : Gal(L/K), σ α = α := fun σ =>
    (kummerPairing_eq_one_iff σ x ha hα).mp (DFunLike.congr_fun hx σ)
  obtain ⟨b, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) α).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (NeZero.ne n)] at hα
    exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
  have hba : (Units.mk0 b hb0) ^ n = a := by
    ext
    simpa using (algebraMap K L).injective (by simpa using hα)
  apply Subtype.ext
  rw [← ha, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
  exact mem_unitsPow.mpr ⟨_, hba⟩

theorem kummerPairingLeft_injective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Injective (kummerPairingLeft K n L) := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) := HasEnoughRootsOfUnity.of_dvd K hexp
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) K hne
  obtain ⟨a, β, hβ, hχβ⟩ := exists_kummer_eigenvector hexp χ
  have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨β, hβ⟩
  have h1 : σ β = β :=
    (kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl hβ).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)
  rw [hχβ σ] at h1
  have h2 : algebraMap K L (χ σ : K) = 1 :=
    mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hβ) (h1.trans (one_mul β).symm)
  apply hχ
  ext
  simpa using (algebraMap K L).injective (h2.trans (map_one _).symm)

theorem kummerGroup_finite [FiniteDimensional K L] [IsGalois K L] :
    Finite (kummerGroup K n L) :=
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  Finite.of_injective _ (kummerPairingRight_injective K n L)

theorem card_kummerGroup [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Nat.card (kummerGroup K n L) = Module.finrank K L := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [← IsGalois.card_aut_eq_finrank]
  apply le_antisymm
  · calc Nat.card (kummerGroup K n L) ≤ Nat.card (Gal(L/K) →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingRight_injective K n L)
      _ = Nat.card Gal(L/K) :=
          card_monoidHom_rootsOfUnity Gal(L/K) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp)
  · calc Nat.card Gal(L/K) ≤ Nat.card (kummerGroup K n L →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingLeft_injective K n L hexp)
      _ = Nat.card (kummerGroup K n L) :=
          card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)

theorem kummerPairingLeft_bijective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Bijective (kummerPairingLeft K n L) := by
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨kummerPairingLeft_injective K n L hexp, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, ← card_kummerGroup K n L hexp]
  exact (card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)).symm

theorem kummerPairingRight_bijective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Bijective (kummerPairingRight K n L) := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨kummerPairingRight_injective K n L, ?_⟩
  rw [card_kummerGroup K n L hexp, ← IsGalois.card_aut_eq_finrank]
  exact (card_monoidHom_rootsOfUnity Gal(L/K) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp)).symm

def galEquivDual [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Gal(L/K) ≃* (kummerGroup K n L →* rootsOfUnity n K) :=
  MulEquiv.ofBijective _ (kummerPairingLeft_bijective K n L hexp)

def kummerGroupEquivDual [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    kummerGroup K n L ≃* (Gal(L/K) →* rootsOfUnity n K) :=
  MulEquiv.ofBijective _ (kummerPairingRight_bijective K n L hexp)

@[simp] lemma galEquivDual_apply [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) (σ : Gal(L/K))
    (x : kummerGroup K n L) : galEquivDual K n L hexp σ x = kummerPairing K n L σ x := rfl

@[simp] lemma kummerGroupEquivDual_apply [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) (x : kummerGroup K n L)
    (σ : Gal(L/K)) : kummerGroupEquivDual K n L hexp x σ = kummerPairing K n L σ x := rfl

theorem kummerField_kummerGroup [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    kummerField K n L (kummerGroup K n L) = ⊤ := by
  set E := kummerField K n L (kummerGroup K n L)
  have hbot : E.fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply kummerPairingLeft_injective K n L hexp
    rw [map_one]
    ext x : 1
    obtain ⟨a, ha, α, hα⟩ := exists_rep x
    have hαE : α ∈ E := IntermediateField.subset_adjoin _ _ ⟨a, ha ▸ x.2, hα⟩
    rw [kummerPairingLeft_apply, MonoidHom.one_apply]
    exact (kummerPairing_eq_one_iff σ x ha hα).mpr (hσ ⟨α, hαE⟩)
  rw [← IsGalois.fixedField_fixingSubgroup E, hbot, IntermediateField.fixedField_bot]

theorem adjoin_nthRoots_eq_top [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    IntermediateField.adjoin K {α : L | α ≠ 0 ∧ α ^ n ∈ Set.range (algebraMap K L)} = ⊤ := by
  rw [eq_top_iff, ← kummerField_kummerGroup K n L hexp]
  apply IntermediateField.adjoin.mono
  rintro α ⟨a, -, hα⟩
  exact ⟨ne_zero_of_pow_eq_algebraMap hα, a, hα.symm⟩

end FiniteKummer

end KummerFinite

section KummerCorrespondence

open Polynomial IntermediateField

section Generated

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {L : Type*} [Field L] [Algebra K L]

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma eq_one_of_forall_mem_fixed {T : Set L} (hT : adjoin K T = ⊤) {σ : Gal(L/K)}
    (h : ∀ α ∈ T, σ α = α) : σ = 1 := by
  have hle : adjoin K T ≤ fixedField (Subgroup.zpowers σ) := by
    rw [adjoin_le_iff]
    intro α hα
    rw [SetLike.mem_coe, mem_fixedField_iff]
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer Gal(L/K) α := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h α hα
    have hf' := (Subgroup.zpowers_le.mpr hσ) hf
    rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hf'
    exact hf'
  rw [hT] at hle
  ext x
  have hx := hle (IntermediateField.mem_top (x := x))
  rw [mem_fixedField_iff] at hx
  rw [AlgEquiv.one_apply]
  exact hx σ (Subgroup.mem_zpowers σ)

lemma exists_eq_algebraMap_mul {a b : Kˣ} (h : (a : UnitsModPow K n) = b) {α β : L}
    (hα : α ^ n = algebraMap K L a) (hβ : β ^ n = algebraMap K L b) :
    ∃ c : K, α = algebraMap K L c * β := by
  obtain ⟨d, hd⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp h)
  have hβ0 : β ≠ 0 := ne_zero_of_pow_eq_algebraMap hβ
  have hd0 : algebraMap K L (d : K) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr d.ne_zero
  have hb : (b : K) = (a : K) * (d : K) ^ n := by
    have h1 : (d : K) ^ n = (a : K)⁻¹ * (b : K) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
        using congrArg Units.val hd
    rw [h1, ← mul_assoc, mul_inv_cancel₀ a.ne_zero, one_mul]
  have hq : (α * algebraMap K L (d : K) / β) ^ n = 1 := by
    rw [div_pow, mul_pow, hα, hβ, hb, map_mul, map_pow]
    exact div_self (mul_ne_zero ((map_ne_zero (algebraMap K L)).mpr a.ne_zero) (pow_ne_zero _ hd0))
  obtain ⟨η, hη⟩ := exists_algebraMap_eq_of_pow_eq_one (K := K) hq
  refine ⟨((η : Kˣ) : K) / d, ?_⟩
  rw [map_div₀, hη]
  field_simp

variable (K n L)

theorem kummerPairingLeft_injective_of_adjoin_eq_top {T : Set L} (hT : adjoin K T = ⊤)
    (hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a) :
    Function.Injective (kummerPairingLeft K n L) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply eq_one_of_forall_mem_fixed hT
  intro α hα
  obtain ⟨a, ha⟩ := hTn α hα
  have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨α, ha⟩
  exact (kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl ha).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)

theorem isMulCommutative_of_adjoin_eq_top {T : Set L} (hT : adjoin K T = ⊤)
    (hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a) :
    IsMulCommutative Gal(L/K) :=
  ⟨⟨fun σ τ => kummerPairingLeft_injective_of_adjoin_eq_top K n L hT hTn (by
    rw [map_mul, map_mul, mul_comm])⟩⟩

theorem exponent_dvd_of_adjoin_eq_top {T : Set L} (hT : adjoin K T = ⊤)
    (hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a) :
    Monoid.exponent Gal(L/K) ∣ n := by
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ =>
    kummerPairingLeft_injective_of_adjoin_eq_top K n L hT hTn ?_
  rw [map_pow, map_one]
  ext x
  have := (mem_rootsOfUnity n _).mp (kummerPairingLeft K n L σ x).2
  simp only [MonoidHom.pow_apply, MonoidHom.one_apply]
  exact congrArg Units.val (by rw [SubmonoidClass.coe_pow, this, OneMemClass.coe_one])

theorem kummerGroup_le_of_adjoin_eq_top [FiniteDimensional K L] [IsGalois K L] {T : Set L}
    (hT : adjoin K T = ⊤) (Δ : Subgroup (UnitsModPow K n))
    (hTΔ : ∀ α ∈ T, ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ α ^ n = algebraMap K L a) :
    kummerGroup K n L ≤ Δ := by
  have hTn : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K L a := fun α hα =>
    let ⟨a, _, h⟩ := hTΔ α hα; ⟨a, h⟩
  have : IsMulCommutative Gal(L/K) := isMulCommutative_of_adjoin_eq_top K n L hT hTn
  have hexp := exponent_dvd_of_adjoin_eq_top K n L hT hTn
  have := kummerGroup_finite K n L
  let H : Subgroup (kummerGroup K n L) := Δ.comap (kummerGroup K n L).subtype
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) H
  let res : Gal(L/K) → (H →* rootsOfUnity n K) := fun σ => (kummerPairingLeft K n L σ).comp H.subtype
  have hres : Function.Injective res := by
    intro σ τ hστ
    have hfix : ∀ α ∈ T, (τ⁻¹ * σ) α = α := by
      intro α hα
      obtain ⟨a, haΔ, ha⟩ := hTΔ α hα
      have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨α, ha⟩
      have hxH : (⟨_, hx⟩ : kummerGroup K n L) ∈ H := haΔ
      have h1 := DFunLike.congr_fun hστ ⟨_, hxH⟩
      simp only [res, MonoidHom.comp_apply, Subgroup.coe_subtype, kummerPairingLeft_apply] at h1
      rw [AlgEquiv.mul_apply, kummerPairing_spec σ ⟨_, hx⟩ rfl ha, h1,
        ← kummerPairing_spec τ ⟨_, hx⟩ rfl ha, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    exact (inv_mul_eq_one.mp (eq_one_of_forall_mem_fixed hT hfix)).symm
  have hH : Nat.card H = Nat.card (kummerGroup K n L) := by
    apply le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective)
    calc Nat.card (kummerGroup K n L) = Nat.card Gal(L/K) := by
          rw [card_kummerGroup K n L hexp, IsGalois.card_aut_eq_finrank]
      _ ≤ Nat.card (H →* rootsOfUnity n K) := Nat.card_le_card_of_injective _ hres
      _ = Nat.card H := card_monoidHom_rootsOfUnity H fun x =>
          Subtype.ext (kummerGroup_pow_eq_one K n L x.1)
  have htop := Subgroup.eq_top_of_card_eq H hH
  intro x hx
  have : (⟨x, hx⟩ : kummerGroup K n L) ∈ H := htop ▸ Subgroup.mem_top _
  exact this

end Generated

section GaloisKummer

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem isGalois_adjoin_nthRoots {T : Set Ω} (hT : ∀ α ∈ T, ∃ a : Kˣ, α ^ n = algebraMap K Ω a) :
    IsGalois K (adjoin K T) := by
  classical
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hnK : (n : K) ≠ 0 := (hζ.neZero').out
  let a : T → Kˣ := fun α => (hT α α.2).choose
  have ha : ∀ α : T, (α : Ω) ^ n = algebraMap K Ω (a α) := fun α => (hT α α.2).choose_spec
  let p : T → K[X] := fun α => X ^ n - C (a α : K)
  have hp0 : ∀ α, p α ≠ 0 := fun α => X_pow_sub_C_ne_zero (NeZero.pos n) _
  have hsep : ∀ α, (p α).Separable := fun α => separable_X_pow_sub_C _ hnK (a α).ne_zero
  have hsplit : ∀ α : T, ((p α).map (algebraMap K Ω)).Splits := by
    intro α
    simp only [p, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap K Ω).injective) (ha α)
  have hgal : ∀ α : T, IsGalois K (adjoin K ((p α).rootSet Ω)) := fun α =>
    haveI := adjoin_rootSet_isSplittingField (hsplit α)
    IsGalois.of_separable_splitting_field (hsep α)
  have heq : adjoin K T = ⨆ α : T, adjoin K ((p α).rootSet Ω) := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      intro α hα
      apply le_iSup (fun β : T => adjoin K ((p β).rootSet Ω)) ⟨α, hα⟩
      apply subset_adjoin
      rw [mem_rootSet]
      refine ⟨hp0 _, ?_⟩
      simp [p, ha ⟨α, hα⟩]
    · refine iSup_le fun α => ?_
      rw [adjoin_le_iff]
      intro γ hγ
      rw [mem_rootSet] at hγ
      have hγn : γ ^ n = algebraMap K Ω (a α) := by
        have := hγ.2
        simp only [p, map_sub, map_pow, aeval_X, aeval_C] at this
        exact sub_eq_zero.mp this
      obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K) rfl hγn (ha α)
      rw [SetLike.mem_coe, hc]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ α.2)
  have : ∀ α : T, Normal K (adjoin K ((p α).rootSet Ω)) := fun α => (hgal α).to_normal
  have : ∀ α : T, Algebra.IsSeparable K (adjoin K ((p α).rootSet Ω)) :=
    fun α => (hgal α).to_isSeparable
  rw [heq]
  constructor

end GaloisKummer

section Correspondence

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma pow_eq_algebraMap_iff (E : IntermediateField K Ω) (x : E) (a : K) :
    x ^ n = algebraMap K E a ↔ (x : Ω) ^ n = algebraMap K Ω a := by
  rw [← Subtype.val_inj, IntermediateField.coe_pow]
  rfl

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma adjoin_preimage_eq_top (S : Set Ω) :
    adjoin K (((↑) : adjoin K S → Ω) ⁻¹' S) = ⊤ := by
  apply IntermediateField.map_injective (adjoin K S).val
  rw [adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  congr 1
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨⟨x, subset_adjoin K S hx⟩, hx, rfl⟩⟩

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma kummerField_mono {Δ Δ' : Subgroup (UnitsModPow K n)} (h : Δ ≤ Δ') :
    kummerField K n Ω Δ ≤ kummerField K n Ω Δ' :=
  adjoin.mono _ _ _ fun _ ⟨a, ha, hα⟩ => ⟨a, h ha, hα⟩

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma kummerGroup_mono {E E' : IntermediateField K Ω} (h : E ≤ E') :
    kummerGroup K n E ≤ kummerGroup K n E' := by
  intro y hy
  induction y using QuotientGroup.induction_on with
  | H b =>
    obtain ⟨β, hβ⟩ := mk_mem_kummerGroup.mp hy
    refine mk_mem_kummerGroup.mpr ⟨⟨β, h β.2⟩, ?_⟩
    rw [pow_eq_algebraMap_iff] at hβ ⊢
    exact hβ

omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma kummerField_generators (Δ : Subgroup (UnitsModPow K n)) :
    adjoin K {x : kummerField K n Ω Δ |
      ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧ x ^ n = algebraMap K _ a} = ⊤ := by
  unfold kummerField
  rw [← adjoin_preimage_eq_top K Ω]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, pow_eq_algebraMap_iff]

theorem kummerField_isGalois (Δ : Subgroup (UnitsModPow K n)) :
    IsGalois K (kummerField K n Ω Δ) :=
  isGalois_adjoin_nthRoots fun _ ⟨a, _, h⟩ => ⟨a, h⟩

theorem kummerField_isMulCommutative (Δ : Subgroup (UnitsModPow K n)) :
    IsMulCommutative Gal(kummerField K n Ω Δ/K) :=
  isMulCommutative_of_adjoin_eq_top K n _ (kummerField_generators K n Ω Δ)
    fun _ ⟨a, _, h⟩ => ⟨a, h⟩

theorem kummerField_exponent_dvd (Δ : Subgroup (UnitsModPow K n)) :
    Monoid.exponent Gal(kummerField K n Ω Δ/K) ∣ n :=
  exponent_dvd_of_adjoin_eq_top K n _ (kummerField_generators K n Ω Δ)
    fun _ ⟨a, _, h⟩ => ⟨a, h⟩

omit [HasEnoughRootsOfUnity K n] in
lemma isIntegral_of_pow_eq_algebraMap {α : Ω} {a : K} (hα : α ^ n = algebraMap K Ω a) :
    IsIntegral K α :=
  ⟨X ^ n - C a, monic_X_pow_sub_C _ (NeZero.ne n), by simp [hα]⟩

lemma exists_pow_eq_algebraMap [IsSepClosed Ω] (a : Kˣ) : ∃ α : Ω, α ^ n = algebraMap K Ω a := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hnΩ : ((n : ℕ) : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero (algebraMap K Ω)).mpr (hζ.neZero').out
  obtain ⟨α, hα⟩ := IsSepClosed.exists_root (X ^ n - C (algebraMap K Ω a))
    (by rw [degree_X_pow_sub_C (NeZero.pos n)]; exact_mod_cast NeZero.ne n)
    (separable_X_pow_sub_C _ hnΩ ((map_ne_zero (algebraMap K Ω)).mpr a.ne_zero))
  exact ⟨α, by simpa [sub_eq_zero] using hα⟩

theorem kummerGroup_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    kummerGroup K n (kummerField K n Ω Δ) = Δ := by
  apply le_antisymm
  · intro y hy
    induction y using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨β, hβ⟩ := mk_mem_kummerGroup.mp hy
      rw [pow_eq_algebraMap_iff] at hβ
      obtain ⟨T, hTS, hβT⟩ := exists_finset_of_mem_adjoin β.2
      have hTn : ∀ α ∈ (T : Set Ω), ∃ a : Kˣ, (a : UnitsModPow K n) ∈ Δ ∧
          α ^ n = algebraMap K Ω a := fun α hα => hTS hα
      have : FiniteDimensional K (adjoin K (T : Set Ω)) :=
        finiteDimensional_adjoin fun α hα =>
          let ⟨_, _, h⟩ := hTn α hα; isIntegral_of_pow_eq_algebraMap K n Ω h
      have : IsGalois K (adjoin K (T : Set Ω)) :=
        isGalois_adjoin_nthRoots fun α hα => let ⟨a, _, h⟩ := hTn α hα; ⟨a, h⟩
      have hle := kummerGroup_le_of_adjoin_eq_top K n (adjoin K (T : Set Ω))
        (adjoin_preimage_eq_top K Ω _) Δ (fun α hα => by
          obtain ⟨a, haΔ, ha⟩ := hTn α hα
          exact ⟨a, haΔ, (pow_eq_algebraMap_iff K n Ω _ α a).mpr ha⟩)
      apply hle
      exact mk_mem_kummerGroup.mpr ⟨⟨β, hβT⟩, (pow_eq_algebraMap_iff K n Ω _ _ _).mpr hβ⟩
  · intro y hy
    induction y using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨α, hα⟩ := exists_pow_eq_algebraMap K n Ω b
      exact mk_mem_kummerGroup.mpr ⟨⟨α, subset_adjoin _ _ ⟨b, hy, hα⟩⟩,
        (pow_eq_algebraMap_iff K n Ω _ _ _).mpr hα⟩

theorem kummerField_kummerGroup_eq (E : IntermediateField K Ω) [IsGalois K E]
    [IsMulCommutative Gal(E/K)] (hexp : Monoid.exponent Gal(E/K) ∣ n) :
    kummerField K n Ω (kummerGroup K n E) = E := by
  apply le_antisymm
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    obtain ⟨β, hβ⟩ := mk_mem_kummerGroup.mp ha
    rw [pow_eq_algebraMap_iff] at hβ
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K) rfl hα hβ
    rw [SetLike.mem_coe, hc]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) β.2
  · intro x hx
    set x' : E := ⟨x, hx⟩
    set p := minpoly K x'
    let F : IntermediateField K E := adjoin K (p.rootSet E)
    have : p.IsSplittingField K F := adjoin_rootSet_isSplittingField (Normal.splits inferInstance x')
    have : IsGalois K F :=
      IsGalois.of_separable_splitting_field (Algebra.IsSeparable.isSeparable K x')
    have : FiniteDimensional K F := IsSplittingField.finiteDimensional F p
    have hxF : x' ∈ F := subset_adjoin _ _ (by
      rw [mem_rootSet]
      exact ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x'), minpoly.aeval K x'⟩)
    have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := F) (E := E)
    have : IsMulCommutative Gal(F/K) := ⟨⟨fun σ τ => by
      obtain ⟨σ', rfl⟩ := hsurj σ
      obtain ⟨τ', rfl⟩ := hsurj τ
      rw [← map_mul, ← map_mul, (IsMulCommutative.is_comm (M := Gal(E/K))).comm σ' τ']⟩⟩
    have hexpF : Monoid.exponent Gal(F/K) ∣ n := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
      obtain ⟨σ', rfl⟩ := hsurj σ
      rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ', map_one]
    have htop := adjoin_nthRoots_eq_top K n F hexpF
    let φ : F →ₐ[K] Ω := E.val.comp F.val
    have hmap : (⊤ : IntermediateField K F).map φ ≤ kummerField K n Ω (kummerGroup K n E) := by
      rw [← htop, adjoin_map, kummerField, adjoin_le_iff]
      rintro _ ⟨γ, ⟨hγ0, b, hb⟩, rfl⟩
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [map_zero] at hb
        exact pow_ne_zero n hγ0 hb.symm
      refine subset_adjoin _ _ ⟨Units.mk0 b hb0, ?_, ?_⟩
      · refine mk_mem_kummerGroup.mpr ⟨F.val γ, ?_⟩
        rw [← map_pow, ← hb, AlgHom.commutes]
        rfl
      · change (φ γ) ^ n = algebraMap K Ω b
        rw [← map_pow, ← hb, AlgHom.commutes]
    exact hmap ((IntermediateField.map_mem_map _ φ).mpr (IntermediateField.mem_top (x := ⟨x', hxF⟩)))

lemma exists_finite_generators_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    ∃ r : Δ → Ω, (∀ x : Δ, ∃ a : Kˣ, (a : UnitsModPow K n) = x ∧ r x ^ n = algebraMap K Ω a) ∧
      kummerField K n Ω Δ = adjoin K (Set.range r) := by
  choose r hr using fun x : Δ => exists_pow_eq_algebraMap K n Ω (x : UnitsModPow K n).out
  refine ⟨r, fun x => ⟨_, QuotientGroup.out_eq' _, hr x⟩, le_antisymm ?_ ?_⟩
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_mul (K := K)
      (QuotientGroup.out_eq' (a : UnitsModPow K n)).symm hα (hr ⟨_, ha⟩)
    rw [SetLike.mem_coe, hc]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (subset_adjoin _ _ ⟨_, rfl⟩)
  · rw [kummerField, adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    refine subset_adjoin _ _ ⟨(x : UnitsModPow K n).out, ?_, hr x⟩
    rw [QuotientGroup.out_eq']
    exact x.2

theorem finiteDimensional_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n))
    [Finite Δ] : FiniteDimensional K (kummerField K n Ω Δ) := by
  obtain ⟨r, hr, heq⟩ := exists_finite_generators_kummerField K n Ω Δ
  rw [heq]
  exact finiteDimensional_adjoin fun α ⟨x, hx⟩ => by
    obtain ⟨a, -, ha⟩ := hr x
    exact isIntegral_of_pow_eq_algebraMap K n Ω (hx ▸ ha)

theorem finrank_kummerField [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) [Finite Δ] :
    Module.finrank K (kummerField K n Ω Δ) = Nat.card Δ := by
  have := finiteDimensional_kummerField K n Ω Δ
  have := kummerField_isGalois K n Ω Δ
  have := kummerField_isMulCommutative K n Ω Δ
  rw [← card_kummerGroup K n _ (kummerField_exponent_dvd K n Ω Δ), kummerGroup_kummerField]

def kummerCorrespondence [IsSepClosed Ω] :
    Subgroup (UnitsModPow K n) ≃o {E : IntermediateField K Ω //
      IsGalois K E ∧ IsMulCommutative Gal(E/K) ∧ Monoid.exponent Gal(E/K) ∣ n} where
  toFun Δ := ⟨kummerField K n Ω Δ, kummerField_isGalois K n Ω Δ,
    kummerField_isMulCommutative K n Ω Δ, kummerField_exponent_dvd K n Ω Δ⟩
  invFun E := kummerGroup K n E.1
  left_inv Δ := kummerGroup_kummerField K n Ω Δ
  right_inv := by
    rintro ⟨E, h1, h2, h3⟩
    exact Subtype.ext (kummerField_kummerGroup_eq K n Ω E h3)
  map_rel_iff' {Δ Δ'} := by
    constructor
    · intro h
      have h' : kummerField K n Ω Δ ≤ kummerField K n Ω Δ' := h
      rw [← kummerGroup_kummerField K n Ω Δ, ← kummerGroup_kummerField K n Ω Δ']
      exact kummerGroup_mono K n Ω h'
    · intro h
      exact kummerField_mono K n Ω h

@[simp] lemma kummerCorrespondence_apply [IsSepClosed Ω] (Δ : Subgroup (UnitsModPow K n)) :
    (kummerCorrespondence K n Ω Δ : IntermediateField K Ω) = kummerField K n Ω Δ := rfl

@[simp] lemma kummerCorrespondence_symm_apply [IsSepClosed Ω]
    (E : {E : IntermediateField K Ω //
      IsGalois K E ∧ IsMulCommutative Gal(E/K) ∧ Monoid.exponent Gal(E/K) ∣ n}) :
    (kummerCorrespondence K n Ω).symm E = kummerGroup K n E.1 := rfl

end Correspondence

end KummerCorrespondence

/-! ### Restricted Ramification & Unramified Extensions -/

section RestrictedRamification

open NumberField IsDedekindDomain
open scoped Pointwise

section MaxUnramifiedOutside

variable {F : Type*} [Field F]

def placesOver {L : Type*} [Field L] [Algebra F L]
    (S : Set (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 L)) :=
  {w | ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal}

theorem mem_placesOver {L : Type*} [Field L] [Algebra F L]
    {S : Set (HeightOneSpectrum (𝓞 F))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ ∃ v ∈ S, w.asIdeal.LiesOver v.asIdeal :=
  Iff.rfl

variable {Ω : Type*} [Field Ω] [Algebra F Ω]

def IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F Ω) : Prop :=
  ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal

variable (F Ω) in
def maxUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) : IntermediateField F Ω :=
  ⨆ (E : IntermediateField F Ω) (_ : FiniteDimensional F E) (_ : IsUnramifiedOutside S E), E

variable (F Ω) in
abbrev galUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) :=
  Gal(maxUnramifiedOutside F Ω S / F)

end MaxUnramifiedOutside

section Ramification

theorem isUnramifiedAt_tower_iff {F L M : Type*} [Field F] [Field L] [Field M]
    [NumberField F] [NumberField L] [NumberField M]
    [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) Q ↔
      Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 L)) ∧ Algebra.IsUnramifiedAt (𝓞 L) Q := by
  rw [← Ideal.ramificationIdx_eq_one_iff, ← Ideal.ramificationIdx_eq_one_iff,
    ← Ideal.ramificationIdx_eq_one_iff, Ideal.ramificationIdx_tower (q := Q.under (𝓞 L))]
  exact mul_eq_one

section Inertia

variable {F E M : Type*} [Field F] [Field E] [Field M] [Algebra F E] [Algebra E M] [Algebra F M]
  [IsScalarTower F E M]

theorem restrictScalars_mem_inertia_iff (Q : Ideal (𝓞 M)) (σ : Gal(M/E)) :
    AlgEquiv.restrictScalarsHom F σ ∈ Q.inertia Gal(M/F) ↔ σ ∈ Q.inertia Gal(M/E) :=
  Iff.rfl

theorem mem_range_restrictScalarsHom_iff (σ : Gal(M/F)) :
    σ ∈ (AlgEquiv.restrictScalarsHom F : Gal(M/E) →* Gal(M/F)).range ↔
      ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

variable [NumberField F] [NumberField E] [NumberField M] [IsGalois F M]

theorem isUnramifiedAt_under_iff_inertia (Q : Ideal (𝓞 M)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 F) (Q.under (𝓞 E)) ↔
      ∀ σ ∈ Q.inertia Gal(M/F), ∀ x : E, σ (algebraMap E M x) = algebraMap E M x := by
  have : IsGaloisGroup Gal(M/F) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  have : IsGalois E M := IsGalois.tower_top_of_isGalois F E M
  have : IsGaloisGroup Gal(M/E) (𝓞 E) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ E M
  have cF : Nat.card (Q.inertia Gal(M/F)) = Q.ramificationIdx (𝓞 F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 F)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q Gal(M/F)]
  have cE : Nat.card (Q.inertia Gal(M/E)) = Q.ramificationIdx (𝓞 E) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (Q.under (𝓞 E)) Q,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 E)) Q Gal(M/E)]
  have htow : Q.ramificationIdx (𝓞 F) =
      (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (q := Q.under (𝓞 E)) (r := Q)
  set φ : Gal(M/E) →* Gal(M/F) := AlgEquiv.restrictScalarsHom F with hφ
  have hinj : Function.Injective φ := AlgEquiv.restrictScalarsHom_injective F
  have hmap : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) ⊓ φ.range := by
    ext σ
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨(restrictScalars_mem_inertia_iff Q τ).2 hτ, τ, rfl⟩
    · rintro ⟨hσ, τ, rfl⟩
      exact ⟨τ, (restrictScalars_mem_inertia_iff Q τ).1 hσ, rfl⟩
  have hcardmap : Nat.card ((Q.inertia Gal(M/E)).map φ) = Nat.card (Q.inertia Gal(M/E)) :=
    Subgroup.card_map_of_injective hinj
  have hpos : 0 < Nat.card (Q.inertia Gal(M/E)) := Nat.card_pos
  rw [← Ideal.ramificationIdx_eq_one_iff]
  constructor
  · intro h1 σ hσ
    have hc : Nat.card (Q.inertia Gal(M/F) ⊓ φ.range : Subgroup Gal(M/F)) ≥
        Nat.card (Q.inertia Gal(M/F)) := by
      rw [← hmap, hcardmap, cF, cE, htow, h1, one_mul]
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : Q.inertia Gal(M/F) ⊓ φ.range ≤ _) hc
    have hσ' : σ ∈ Q.inertia Gal(M/F) ⊓ φ.range := by rw [heq]; exact hσ
    exact (mem_range_restrictScalarsHom_iff σ).1 hσ'.2
  · intro h
    have hle : Q.inertia Gal(M/F) ≤ φ.range := fun σ hσ =>
      (mem_range_restrictScalarsHom_iff σ).2 (h σ hσ)
    have hmap' : (Q.inertia Gal(M/E)).map φ = Q.inertia Gal(M/F) := by
      rw [hmap, inf_eq_left.2 hle]
    have hc : (Q.under (𝓞 E)).ramificationIdx (𝓞 F) * Q.ramificationIdx (𝓞 E) =
        1 * Q.ramificationIdx (𝓞 E) := by
      rw [← htow, ← cF, ← cE, ← hmap', hcardmap, one_mul]
    exact Nat.eq_of_mul_eq_mul_right (cE ▸ hpos) hc

end Inertia

end Ramification

section Unramified

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem finiteDimensional_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M] :
    FiniteDimensional F E :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

theorem isUnramifiedIn_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M]
    (v : HeightOneSpectrum (𝓞 F)) (hM : Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  intro P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have hu := ((isUnramifiedAt_tower_iff (F := F) (L := E) Q).1 (hM Q hQ this)).1
  have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
  subst e
  exact hu

theorem isUnramifiedIn_iff_inertia {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        ∀ σ ∈ Q.inertia Gal(M/F), ∀ x (hx : x ∈ E), σ ⟨x, h hx⟩ = ⟨x, h hx⟩ := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  constructor
  · intro hE Q hQ hQv σ hσ x hx
    have : (Q.under (𝓞 E)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact hQv.over⟩
    have hu := hE (Q.under (𝓞 E)) inferInstance this
    exact (isUnramifiedAt_under_iff_inertia Q).1 hu σ hσ ⟨x, hx⟩
  · intro hI P hP hPv
    obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hu := (isUnramifiedAt_under_iff_inertia (F := F) (E := E) Q).2
      (fun σ hσ y => hI Q hQ hQv σ hσ y.1 y.2)
    have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
    subst e
    exact hu

omit [NumberField F] in
theorem mem_map_fixedField_iff {M : IntermediateField F Ω} (H : Subgroup Gal(M/F)) (x : Ω) :
    x ∈ (IntermediateField.fixedField H).map M.val ↔ ∃ hx : x ∈ M, ∀ σ ∈ H, σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, (IntermediateField.mem_fixedField_iff H _).2 hfix, rfl⟩

theorem isUnramifiedIn_iff_le_fixedField {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        E ≤ (IntermediateField.fixedField (Q.inertia Gal(M/F))).map M.val := by
  rw [isUnramifiedIn_iff_inertia h]
  refine forall_congr' fun Q => forall_congr' fun _ => forall_congr' fun _ => ?_
  constructor
  · intro hI x hx
    exact (mem_map_fixedField_iff _ x).2 ⟨h hx, fun σ hσ => hI σ hσ x hx⟩
  · intro hle σ hσ x hx
    obtain ⟨_, hfix⟩ := (mem_map_fixedField_iff _ x).1 (hle hx)
    exact hfix σ hσ

variable [IsGalois F Ω]

theorem isUnramifiedIn_sup {E₁ E₂ : IntermediateField F Ω} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] (v : HeightOneSpectrum (𝓞 F))
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) v.asIdeal) (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (E₁ ⊔ E₂)
  rw [isUnramifiedIn_iff_le_fixedField hM]
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_left.trans hM)] at h₁
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_right.trans hM)] at h₂
  exact fun Q hQ hQv => sup_le (h₁ Q hQ hQv) (h₂ Q hQ hQv)

theorem IsUnramifiedOutside.sup {S : Set (HeightOneSpectrum (𝓞 F))} {E₁ E₂ : IntermediateField F Ω}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂] (h₁ : IsUnramifiedOutside S E₁)
    (h₂ : IsUnramifiedOutside S E₂) : IsUnramifiedOutside S (E₁ ⊔ E₂) :=
  fun v hv => isUnramifiedIn_sup v (h₁ v hv) (h₂ v hv)

theorem isUnramifiedIn_bot (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⊥ : IntermediateField F Ω)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (⊥ : IntermediateField F Ω)
  rw [isUnramifiedIn_iff_inertia hM]
  intro Q _ _ σ _ x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes a

theorem isUnramifiedOutside_bot (S : Set (HeightOneSpectrum (𝓞 F))) :
    IsUnramifiedOutside S (⊥ : IntermediateField F Ω) :=
  fun v _ => isUnramifiedIn_bot v

theorem isUnramifiedIn_map {E : IntermediateField F Ω} [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) (hE : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) (τ : Gal(Ω/F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (τ : Ω →ₐ[F] Ω))) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le E
  set M' : IntermediateField F Ω := M.toIntermediateField with hM'
  set ρ : Gal(M'/F) := τ.restrictNormal M' with hρ
  have hρapp : ∀ y (hy : y ∈ M'), ((ρ ⟨y, hy⟩ : M') : Ω) = τ y := fun y hy =>
    AlgEquiv.restrictNormal_commutes τ M' ⟨y, hy⟩
  have hτM : E.map (τ : Ω →ₐ[F] Ω) ≤ M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    have := (ρ ⟨y, hM hy⟩).2
    rwa [hρapp] at this
  rw [isUnramifiedIn_iff_inertia hM] at hE
  rw [isUnramifiedIn_iff_inertia hτM]
  intro Q hQ hQv σ hσ x hx
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  have hconj : ρ⁻¹ * σ * ρ ∈ (ρ⁻¹ • Q).inertia Gal(M'/F) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro z
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
      smul_sub, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    exact (AddSubgroup.mem_inertia.1 hσ) (ρ • z)
  have := NumberField.of_module_finite F M'
  have : IsGaloisGroup Gal(M'/F) (𝓞 F) (𝓞 M') := IsGaloisGroup.of_isFractionRing _ _ _ F M'
  have hfix := hE (ρ⁻¹ • Q) inferInstance inferInstance _ hconj y hy
  have hρy : ρ ⟨y, hM hy⟩ = ⟨(τ : Ω →ₐ[F] Ω) y, hτM hx⟩ := Subtype.ext (hρapp y (hM hy))
  rw [← hρy]
  calc σ (ρ ⟨y, hM hy⟩) = ρ ((ρ⁻¹ * σ * ρ) ⟨y, hM hy⟩) := by
        simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ρ ⟨y, hM hy⟩ := by rw [hfix]

theorem IsUnramifiedOutside.map {S : Set (HeightOneSpectrum (𝓞 F))} {E : IntermediateField F Ω}
    [FiniteDimensional F E] (hE : IsUnramifiedOutside S E) (τ : Gal(Ω/F)) :
    IsUnramifiedOutside S (E.map (τ : Ω →ₐ[F] Ω)) :=
  fun v hv => isUnramifiedIn_map v (hE v hv) τ

end Unramified

end RestrictedRamification

end ProfCoh

/-! ## Part 2: Semilocal Algebras (Finite & Infinite Places) & Norm/Trace Decomposition -/

section BlockNormTrace

theorem det_blockDiagonal' {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (M : ∀ i, Matrix (κ i) (κ i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  rw [(Matrix.blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have : (Matrix.blockDiagonal' M).toSquareBlock Sigma.fst k =
      (M k).submatrix (Equiv.sigmaSubtype k) (Equiv.sigmaSubtype k) := by
    ext ⟨⟨i, a⟩, hi⟩ ⟨⟨j, b⟩, hj⟩
    dsimp only at hi hj
    subst hi hj
    simp [Matrix.toSquareBlock_def, Equiv.sigmaSubtype]
  rw [this, Matrix.det_submatrix_equiv_self]

theorem leftMulMatrix_pi {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) R (A i)) (x : ∀ i, A i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (b i) (x i) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr, Matrix.blockDiagonal'_apply]
  by_cases h : i = j
  · subst h
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  · simp [h]

theorem norm_pi {R ι : Type*} [CommRing R] [Fintype ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (x : ∀ i, A i) :
    Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => (Algebra.norm_eq_matrix_det (b i) (x i)).symm

theorem trace_pi {R ι : Type*} [CommRing R] [Fintype ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
    [∀ i, Module.Finite R (A i)] (x : ∀ i, A i) :
    Algebra.trace R _ x = ∑ i, Algebra.trace R (A i) (x i) := by
  classical
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi, Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ => (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

end BlockNormTrace

namespace SemiLocal

open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter TensorProduct Module
open RHDirect.Stage13CFT_IdeleNormResidue.SemiLocal

/-! ### Semilocal Approximation -/

section Approximation

variable {L : Type*} [Field L] [NumberField L]

theorem exists_sub_mem_pow_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum (𝓞 L)) (hw : Function.Injective w) (i : ι) (n : ℕ) :
    ∃ a : 𝓞 L, ∀ j, a - (if j = i then 1 else 0) ∈ (w j).asIdeal ^ n := by
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Finset.univ)
    (fun j ↦ (w j).asIdeal) (fun _ ↦ n) (fun j _ ↦ (w j).prime)
    (fun j _ k _ hjk h ↦ hjk (hw (HeightOneSpectrum.ext h)))
    (fun j ↦ if j.1 = i then 1 else 0)
  exact ⟨y, fun j ↦ hy j (Finset.mem_univ j)⟩

theorem norm_algebraMap_le_of_mem_pow (w : HeightOneSpectrum (𝓞 L)) (a : 𝓞 L) (n : ℕ)
    (ha : a ∈ w.asIdeal ^ n) :
    ‖algebraMap (𝓞 L) (w.adicCompletion L) a‖ ≤
      ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) ^ n := by
  rw [IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, ← FinitePlace.embedding_apply,
    FinitePlace.norm_embedding_int, ← NNReal.coe_pow, NNReal.coe_le_coe, ← map_pow]
  apply (toNNReal_strictMono (HeightOneSpectrum.one_lt_absNorm_nnreal w)).monotone
  rw [← exp_nsmul, smul_neg, nsmul_one]
  exact (w.intValuation_le_pow_iff_mem a n).2 ha

theorem toNNReal_exp_neg_one_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    ((toNNReal (HeightOneSpectrum.absNorm_ne_zero w) (exp (-1 : ℤ)) : ℝ)) < 1 := by
  rw [← NNReal.coe_one, NNReal.coe_lt_coe,
    toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  rw [← exp_zero, exp_lt_exp]
  norm_num

theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  have := Fintype.ofFinite ι
  let f : L →+* ((i : ι) → (w i).adicCompletion L) := RingHom.pi fun i ↦ algebraMap L _
  let S : Subring ((i : ι) → (w i).adicCompletion L) := f.range.topologicalClosure
  have hδ : ∀ i, Pi.single i 1 ∈ S := by
    intro i
    choose a ha using fun n ↦ exists_sub_mem_pow_of_injective w hw i n
    refine mem_closure_of_tendsto (b := atTop) (f := fun n ↦ f (algebraMap (𝓞 L) L (a n))) ?_
      (Eventually.of_forall fun n ↦ ⟨_, rfl⟩)
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg _)
        (toNNReal_exp_neg_one_lt_one (w j)))
    have h := norm_algebraMap_le_of_mem_pow (w j) _ n (ha n j)
    refine le_of_eq_of_le ?_ h
    congr 1
    by_cases hji : j = i
    · subst hji; simp [f, ← IsScalarTower.algebraMap_apply]
    · simp [f, hji, ← IsScalarTower.algebraMap_apply]
  have hE : ∀ y : ι → L, (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ∈ S := by
    intro y
    have : (fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) =
        ∑ i, Pi.single i 1 * f (y i) := by
      funext j
      simp only [Finset.sum_apply, Pi.mul_apply, f, RingHom.pi_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne hb.symm]
      · simp
    rw [this]
    exact S.sum_mem fun i _ ↦ S.mul_mem (hδ i) (f.range.le_topologicalClosure ⟨y i, rfl⟩)
  have hdense : DenseRange (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) :=
    DenseRange.piMap fun i ↦ HeightOneSpectrum.denseRange_algebraMap L (w i)
  have hsub : Set.range (fun y : ι → L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) (y i)) ⊆
      closure (Set.range f) := by
    rintro _ ⟨y, rfl⟩
    exact hE y
  exact dense_closure.1 (hdense.mono hsub)

end Approximation

/-! ### Continuous Completion Map -/

section CompletionMap

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

theorem continuous_completionMap : Continuous (completionMap v w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)

theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map _
      ((algebraMap K (WithVal (v.valuation K)) x : WithVal _) :
        UniformSpace.Completion (WithVal (v.valuation K))) =
    ((algebraMap K (WithVal (w.valuation L)) x : WithVal _) :
        UniformSpace.Completion (WithVal (w.valuation L)))
  rw [UniformSpace.Completion.map_coe
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w)]
  rfl

theorem valued_completionMap (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  have hK : ∀ k : K, Valued.v (completionMap v w (algebraMap K _ k)) =
      Valued.v (algebraMap K (v.adicCompletion K) k) ^ e := by
    intro k
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [he, ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
      HeightOneSpectrum.valuation_liesOver L v w]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hclosed : IsClosed
      {x : v.adicCompletion K | Valued.v (completionMap v w x) = Valued.v x ^ e} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x0 hx0
    have h0 : x0 ≠ 0 := by
      rintro rfl
      simp [zero_pow he0] at hx0
    have h1 : Valued.v x0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (completionMap v w x0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (completionMap v w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_completionMap v w).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with x hx hx'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hx hx' hx0 ⊢
    rwa [hx, hx']
  exact (HeightOneSpectrum.denseRange_algebraMap K v).induction_on x hclosed hK

scoped instance algebraCompletion : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra

theorem algebraMap_completion_eq :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionMap v w := rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ (completionMap_algebraMap v w x).symm

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := ((continuous_completionMap v w).comp continuous_fst).mul continuous_snd

end CompletionMap

/-! ### Local Degree Lower Bound `e * f ≤ [L_w : K_v]` -/

section LocalDegree

section Integers

variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem valued_algebraMap_int (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) = u.intValuation b := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F),
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]

theorem valued_algebraMap_int_le_one (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) ≤ 1 := by
  rw [valued_algebraMap_int]
  exact u.intValuation_le_one b

theorem valued_algebraMap_int_lt_one_iff (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) < 1 ↔ b ∈ u.asIdeal := by
  rw [valued_algebraMap_int]
  exact u.intValuation_lt_one_iff_mem b

theorem valued_algebraMap_field (x : F) :
    Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem exists_int_valued_sub_lt_one (d : u.adicCompletion F) (hd : Valued.v d ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r) < 1 := by
  obtain ⟨x, hx⟩ : ∃ x : F, Valued.v (d - algebraMap F (u.adicCompletion F) x) < 1 := by
    have ho : IsOpen {y : u.adicCompletion F | Valued.v (d - y) < 1} := by
      have : {y : u.adicCompletion F | Valued.v (d - y) < 1} = Metric.ball d 1 := by
        ext y
        rw [Set.mem_ofPred_eq, Metric.mem_ball, dist_comm, dist_eq_norm,
          Valued.toNormedField.norm_lt_one_iff]
      rw [this]
      exact Metric.isOpen_ball
    exact (HeightOneSpectrum.denseRange_algebraMap F u).exists_mem_open ho ⟨d, by simp⟩
  have hx1 : u.valuation F x ≤ 1 := by
    rw [← valued_algebraMap_field]
    calc Valued.v (algebraMap F (u.adicCompletion F) x)
        = Valued.v (d - (d - algebraMap F (u.adicCompletion F) x)) := by rw [sub_sub_cancel]
      _ ≤ max (Valued.v d) (Valued.v (d - algebraMap F (u.adicCompletion F) x)) :=
          Valuation.map_sub _ _ _
      _ ≤ 1 := max_le hd hx.le
  obtain ⟨r, hr⟩ := u.exists_valuation_sub_lt_of_integer hx1 1
  refine ⟨r, ?_⟩
  have hr' : Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) r -
      algebraMap F (u.adicCompletion F) x) < 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (u.adicCompletion F), ← map_sub,
      valued_algebraMap_field]
    simpa using hr
  calc Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r)
      = Valued.v ((d - algebraMap F (u.adicCompletion F) x) -
          (algebraMap (𝓞 F) (u.adicCompletion F) r - algebraMap F (u.adicCompletion F) x)) := by
        congr 1; ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ < 1 := max_lt hx hr'

end Integers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

theorem algebraMap_completion_algebraMap_int (r : 𝓞 K) :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) (algebraMap (𝓞 K) _ r) =
      algebraMap (𝓞 L) (w.adicCompletion L) (algebraMap (𝓞 K) (𝓞 L) r) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K), algebraMap_completion_eq,
    completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
    IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L),
    ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, ← IsScalarTower.algebraMap_apply (𝓞 K) K L]

theorem valued_algebraMap_completion (x : v.adicCompletion K) :
    Valued.v (algebraMap (v.adicCompletion K) (w.adicCompletion L) x) =
      Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) :=
  valued_completionMap v w x

variable {ι : Type*} [Fintype ι]

theorem valued_sum_le (ω : ι → 𝓞 L) (c : ι → v.adicCompletion K) (M : ℤᵐ⁰)
    (hM : ∀ j, Valued.v (c j) ≤ M) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) ≤ M ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul, valued_algebraMap_completion]
  calc _ ≤ Valued.v (c j) ^ w.asIdeal.ramificationIdx (𝓞 K) * 1 :=
        mul_le_mul' le_rfl (valued_algebraMap_int_le_one w (ω j))
    _ ≤ _ := by rw [mul_one]; exact pow_le_pow_left' (hM j) _

theorem valued_sum_eq_one (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (d : ι → v.adicCompletion K) (hd : ∀ j, Valued.v (d j) ≤ 1) (j0 : ι)
    (hj0 : Valued.v (d j0) = 1) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) = 1 := by
  refine le_antisymm (by simpa using valued_sum_le v w ω d 1 hd) ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  choose r hr using fun j ↦ exists_int_valued_sub_lt_one v (d j) (hd j)
  have h1 : Valued.v (algebraMap (𝓞 L) (w.adicCompletion L)
      (∑ j, algebraMap (𝓞 K) (𝓞 L) (r j) * ω j)) < 1 := by
    have heq : algebraMap (𝓞 L) (w.adicCompletion L) (∑ j, algebraMap (𝓞 K) (𝓞 L) (r j) * ω j) =
        (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) -
        ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L)
          (d j - algebraMap (𝓞 K) (v.adicCompletion K) (r j)) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω j) := by
      rw [← Finset.sum_sub_distrib, map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, map_sub, algebraMap_completion_algebraMap_int]
      ring
    rw [heq]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hlt ?_)
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, valued_algebraMap_completion]
    calc _ ≤ Valued.v (d j - algebraMap (𝓞 K) (v.adicCompletion K) (r j)) ^
          w.asIdeal.ramificationIdx (𝓞 K) * 1 :=
          mul_le_mul' le_rfl (valued_algebraMap_int_le_one w (ω j))
      _ < 1 := by rw [mul_one]; exact pow_lt_one' (hr j) he0
  rw [valued_algebraMap_int_lt_one_iff, ← Ideal.Quotient.eq_zero_iff_mem, map_sum] at h1
  have hsum : ∑ j, Ideal.Quotient.mk v.asIdeal (r j) • Ideal.Quotient.mk w.asIdeal (ω j) = 0 := by
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def, map_mul, Ideal.Quotient.algebraMap_mk_of_liesOver]
  have hr0 := Fintype.linearIndependent_iff.1 hω _ hsum j0
  rw [Ideal.Quotient.eq_zero_iff_mem, ← valued_algebraMap_int_lt_one_iff v] at hr0
  have : Valued.v (d j0) < 1 := by
    calc Valued.v (d j0) = Valued.v ((d j0 - algebraMap (𝓞 K) (v.adicCompletion K) (r j0)) +
          algebraMap (𝓞 K) (v.adicCompletion K) (r j0)) := by rw [sub_add_cancel]
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ < 1 := max_lt (hr j0) hr0
  exact absurd hj0 this.ne

omit [Fintype ι] in
theorem valued_sum_eq [Fintype ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (c : ι → v.adicCompletion K) (j0 : ι) (hj0 : ∀ j, Valued.v (c j) ≤ Valued.v (c j0)) :
    Valued.v (∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j)) =
      Valued.v (c j0) ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  by_cases h0 : c j0 = 0
  · have hc : ∀ j, c j = 0 := fun j ↦ by
      have := hj0 j
      rw [h0, map_zero] at this
      exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)
    simp [hc, zero_pow he0]
  · have hv0 : Valued.v (c j0) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    set d : ι → v.adicCompletion K := fun j ↦ c j * (c j0)⁻¹ with hd_def
    have hcd : ∀ j, c j = c j0 * d j := fun j ↦ by
      simp only [hd_def]
      rw [mul_comm (c j), ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    have hd : ∀ j, Valued.v (d j) ≤ 1 := fun j ↦ by
      simp only [hd_def, map_mul, map_inv₀]
      rw [← mul_inv_cancel₀ hv0]
      exact mul_le_mul_left (hj0 j) _
    have hdj0 : Valued.v (d j0) = 1 := by simp [hd_def, mul_inv_cancel₀ h0]
    have : ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j) *
        algebraMap (𝓞 L) (w.adicCompletion L) (ω j) =
        algebraMap (v.adicCompletion K) (w.adicCompletion L) (c j0) *
          ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (d j) *
            algebraMap (𝓞 L) (w.adicCompletion L) (ω j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hcd j, map_mul, mul_assoc]
    rw [this, map_mul, valued_algebraMap_completion, valued_sum_eq_one v w ω hω d hd j0 hdj0,
      mul_one]

theorem eq_of_exp_mul_pow_eq {e i i' : ℕ} (hi : i < e) (hi' : i' < e) {a b : ℤᵐ⁰} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : exp (-(i : ℤ)) * a ^ e = exp (-(i' : ℤ)) * b ^ e) : i = i' := by
  rw [← exp_log ha, ← exp_log hb, ← exp_nsmul, ← exp_nsmul, ← exp_add, ← exp_add, exp_inj] at h
  simp only [nsmul_eq_mul] at h
  have hdvd : (e : ℤ) ∣ (i : ℤ) - i' := ⟨log a - log b, by rw [mul_sub]; linarith⟩
  have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> omega)
  omega

omit [Fintype ι] in
theorem linearIndependent_uniformizer_pow_mul [Finite ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (π : L) (hπ : w.valuation L π = exp (-1 : ℤ)) :
    LinearIndependent (v.adicCompletion K)
      (fun p : Fin (w.asIdeal.ramificationIdx (𝓞 K)) × ι ↦
        algebraMap L (w.adicCompletion L) π ^ (p.1 : ℕ) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω p.2)) := by
  classical
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact linearIndependent_empty_type
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  set P := algebraMap L (w.adicCompletion L) π with hP
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set s : Fin e → w.adicCompletion L := fun i ↦
    ∑ j, algebraMap (v.adicCompletion K) (w.adicCompletion L) (g (i, j)) *
      algebraMap (𝓞 L) (w.adicCompletion L) (ω j) with hs_def
  have hsum : ∑ i : Fin e, P ^ (i : ℕ) * s i = 0 := by
    rw [← hg, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hs_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Algebra.smul_def]
    ring
  have hvP : ∀ n : ℕ, Valued.v (P ^ n) = exp (-(n : ℤ)) := by
    intro n
    rw [map_pow, hP, valued_algebraMap_field, hπ, ← exp_nsmul]
    simp
  choose J hJ using fun i : Fin e ↦ Finite.exists_max (fun j ↦ Valued.v (g (i, j)))
  set M : Fin e → ℤᵐ⁰ := fun i ↦ Valued.v (g (i, J i)) with hM_def
  have hterm : ∀ i : Fin e, Valued.v (P ^ (i : ℕ) * s i) = exp (-((i : ℕ) : ℤ)) * M i ^ e := by
    intro i
    rw [map_mul, hvP, hs_def, valued_sum_eq v w ω hω _ (J i) (hJ i)]
  have hM : ∀ i, M i = 0 := by
    by_contra hne
    obtain ⟨i1, hi1⟩ := not_forall.1 hne
    have : Nonempty (Fin e) := ⟨i1⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max (fun i : Fin e ↦ Valued.v (P ^ (i : ℕ) * s i))
    have hnz : ∀ i : Fin e, Valued.v (P ^ (i : ℕ) * s i) ≠ 0 → M i ≠ 0 := by
      intro i hi hMi
      rw [hterm, hMi, zero_pow he0, mul_zero] at hi
      exact hi rfl
    have htop : Valued.v (P ^ (i0 : ℕ) * s i0) ≠ 0 := by
      intro h
      have := hi0 i1
      rw [h, hterm] at this
      have h' : exp (-((i1 : ℕ) : ℤ)) * M i1 ^ e = 0 := le_antisymm this zero_le
      rw [mul_eq_zero] at h'
      rcases h' with h' | h'
      · exact exp_ne_zero h'
      · exact hi1 (pow_eq_zero_iff he0 |>.1 h')
    have hlt : ∀ i ∈ Finset.univ \ {i0},
        Valued.v (P ^ (i : ℕ) * s i) < Valued.v (P ^ (i0 : ℕ) * s i0) := by
      intro i hi
      have hne : i ≠ i0 := by simpa using hi
      refine lt_of_le_of_ne (hi0 i) fun heq ↦ hne (Fin.ext ?_)
      have hi_nz : Valued.v (P ^ (i : ℕ) * s i) ≠ 0 := heq ▸ htop
      rw [hterm, hterm] at heq
      exact eq_of_exp_mul_pow_eq i.2 i0.2 (hnz i hi_nz) (hnz i0 htop) heq
    have := Valuation.map_sum_eq_of_lt _ (Finset.mem_univ i0) hlt
    rw [hsum, map_zero] at this
    exact htop this.symm
  rintro ⟨i, j⟩
  have := hJ i j
  rw [show Valued.v (g (i, J i)) = M i from rfl, hM i] at this
  exact (Valuation.zero_iff _).1 (le_antisymm this zero_le)

theorem ramificationIdx_mul_inertiaDeg_le_finrank :
    w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) ≤
      Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have := v.isMaximal
  have := w.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  let b := Module.finBasis (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)
  choose ω hω using fun j ↦ Ideal.Quotient.mk_surjective (b j)
  have hli : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)) := by
    convert b.linearIndependent with j
    exact hω j
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer L
  have := (linearIndependent_uniformizer_pow_mul v w ω hli π hπ).fintype_card_le_finrank
  simpa using this

end LocalDegree

/-! ### Finite Semilocal Tensor Equivalence `K_v ⊗_K L ≃ ∏_{w|v} L_w` -/

section FiniteTensor

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (L) (v : HeightOneSpectrum (𝓞 K))

abbrev CompletionsOver : Type _ := (w : PlacesOver L v) → w.1.adicCompletion L

def tensorMap : v.adicCompletion K ⊗[K] L →ₐ[v.adicCompletion K] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom K L _)
    (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap_tmul (a : v.adicCompletion K) (x : L) :
    tensorMap L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x := by
  simp [tensorMap]

theorem denseRange_algebraMap_completionsOver :
    DenseRange (algebraMap L (CompletionsOver L v)) :=
  denseRange_algebraMap_pi (fun w : PlacesOver L v ↦ w.1) Subtype.val_injective

open scoped Valued in
theorem tensorMap_surjective : Function.Surjective (tensorMap L v) := by
  have hclosed : IsClosed (LinearMap.range (tensorMap L v).toLinearMap :
      Set (CompletionsOver L v)) :=
    Submodule.closed_of_finiteDimensional _
  have hdense : Dense (Set.range (tensorMap L v)) := by
    refine (denseRange_algebraMap_completionsOver L v).mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by simp⟩
  rw [LinearMap.coe_range] at hclosed
  have h2 : closure (Set.range (tensorMap L v)) = Set.range (tensorMap L v) := hclosed.closure_eq
  rw [← Set.range_eq_univ, ← h2, hdense.closure_eq]

theorem sum_finrank_le :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) ≤ finrank K L := by
  rw [← Module.finrank_pi_fintype]
  calc _ ≤ finrank (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) :=
        LinearMap.finrank_le_finrank_of_surjective (f := (tensorMap L v).toLinearMap)
          (tensorMap_surjective L v)
    _ = finrank K L := Module.finrank_baseChange

theorem sum_ramificationIdx_mul_inertiaDeg :
    ∑ w : PlacesOver L v, w.1.asIdeal.ramificationIdx (𝓞 K) * w.1.asIdeal.inertiaDeg (𝓞 K) =
      finrank K L := by
  have := v.isPrime
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)]
  exact Fintype.sum_equiv (placesOverEquiv L v) _ _ (fun _ ↦ rfl)

theorem sum_finrank_eq :
    ∑ w : PlacesOver L v, finrank (v.adicCompletion K) (w.1.adicCompletion L) = finrank K L := by
  refine le_antisymm (sum_finrank_le L v) ?_
  rw [← sum_ramificationIdx_mul_inertiaDeg L v]
  exact Finset.sum_le_sum fun w _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1

theorem finrank_eq_ramificationIdx_mul_inertiaDeg (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  have h := (Finset.sum_eq_sum_iff_of_le
    (fun (w : PlacesOver L v) _ ↦ ramificationIdx_mul_inertiaDeg_le_finrank v w.1)).1
    (by rw [sum_ramificationIdx_mul_inertiaDeg, sum_finrank_eq])
  exact (h ⟨w, inferInstance⟩ (Finset.mem_univ _)).symm

scoped instance finiteDimensional_adicCompletion (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := by
  refine Module.finite_of_finrank_pos ?_
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w]
  have := v.isMaximal
  have := w.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
  exact Nat.mul_pos (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)) Module.finrank_pos

theorem tensorMap_injective : Function.Injective (tensorMap L v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (tensorMap L v).toLinearMap)
    (by rw [Module.finrank_baseChange, Module.finrank_pi_fintype, sum_finrank_eq])).2
    (tensorMap_surjective L v)

def tensorEquiv : v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap L v) ⟨tensorMap_injective L v, tensorMap_surjective L v⟩

@[simp] theorem tensorEquiv_tmul (a : v.adicCompletion K) (x : L) :
    tensorEquiv L v (a ⊗ₜ x) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * algebraMap L _ x :=
  tensorMap_tmul L v a x

@[simp] theorem tensorEquiv_one_tmul (x : L) :
    tensorEquiv L v (1 ⊗ₜ x) = algebraMap L (CompletionsOver L v) x := by
  simp

def tensorMap' : L ⊗[K] v.adicCompletion K →ₐ[L] CompletionsOver L v :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (IsScalarTower.toAlgHom K (v.adicCompletion K) _) (fun _ _ ↦ Commute.all _ _)

@[simp] theorem tensorMap'_tmul (x : L) (a : v.adicCompletion K) :
    tensorMap' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a := by
  simp [tensorMap']

theorem tensorMap'_eq_comp :
    ⇑(tensorMap' L v) = tensorEquiv L v ∘ Algebra.TensorProduct.comm K L (v.adicCompletion K) := by
  have : (tensorMap' L v).restrictScalars K =
      ((tensorEquiv L v).toAlgHom.restrictScalars K).comp
        (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toAlgHom :=
    Algebra.TensorProduct.ext' fun x a ↦ by simp [mul_comm]
  exact congrArg DFunLike.coe this

def tensorEquiv' : L ⊗[K] v.adicCompletion K ≃ₐ[L] CompletionsOver L v :=
  AlgEquiv.ofBijective (tensorMap' L v) (by
    rw [tensorMap'_eq_comp]
    exact (tensorEquiv L v).bijective.comp (AlgEquiv.bijective _))

@[simp] theorem tensorEquiv'_tmul (x : L) (a : v.adicCompletion K) :
    tensorEquiv' L v (x ⊗ₜ a) =
      algebraMap L (CompletionsOver L v) x * algebraMap (v.adicCompletion K) _ a :=
  tensorMap'_tmul L v x a

theorem tensorEquiv'_tmul_mul (a : v.adicCompletion K) (y : L ⊗[K] v.adicCompletion K) :
    tensorEquiv' L v ((1 ⊗ₜ a) * y) =
      algebraMap (v.adicCompletion K) (CompletionsOver L v) a * tensorEquiv' L v y := by
  rw [map_mul, tensorEquiv'_tmul, map_one, one_mul]

open scoped Valued in
instance isModuleTopology_completionsOver :
    IsModuleTopology (v.adicCompletion K) (CompletionsOver L v) :=
  isModuleTopologyOfFiniteDimensional

def tensorHomeomorph [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)] :
    v.adicCompletion K ⊗[K] L ≃ₜ CompletionsOver L v where
  toEquiv := (tensorEquiv L v).toEquiv
  continuous_toFun :=
    IsModuleTopology.continuous_of_linearMap (tensorEquiv L v).toLinearEquiv.toLinearMap
  continuous_invFun := by
    have := IsModuleTopology.toContinuousAdd (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
    exact IsModuleTopology.continuous_of_linearMap (tensorEquiv L v).symm.toLinearEquiv.toLinearMap

@[simp] theorem tensorHomeomorph_apply [TopologicalSpace (v.adicCompletion K ⊗[K] L)]
    [IsModuleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)]
    (y : v.adicCompletion K ⊗[K] L) : tensorHomeomorph L v y = tensorEquiv L v y := rfl

end FiniteTensor

/-! ### Galois Action on Finite Completions -/

section GaloisCompletions

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L]

def galoisCompletionMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) :
    WithVal (w.valuation L) →+* w'.adicCompletion L :=
  (algebraMap L (w'.adicCompletion L)).comp
    (σ.toRingEquiv.toRingHom.comp (WithVal.equiv (w.valuation L)).toRingHom)

theorem isUniformInducing_algebraMap_withVal (w : HeightOneSpectrum (𝓞 L)) :
    IsUniformInducing (fun x : WithVal (w.valuation L) ↦
      algebraMap L (w.adicCompletion L) (WithVal.equiv _ x)) :=
  (HeightOneSpectrum.adicCompletion.uniformEquiv L w).symm.isUniformEmbedding.isUniformInducing.comp
    (UniformSpace.Completion.isUniformInducing_coe _)

theorem uniformContinuous_galoisCompletionMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • w) : UniformContinuous (galoisCompletionMap σ w w') := by
  subst h
  rw [UniformContinuous, ← (isUniformInducing_algebraMap_withVal w).comap_uniformity,
    ((Metric.uniformity_basis_dist).comap _).tendsto_iff Metric.uniformity_basis_dist]
  intro ε hε
  refine ⟨ε, hε, fun p hp ↦ ?_⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, dist_eq_norm] at hp ⊢
  rw [← map_sub, ← map_sub] at hp
  rw [← map_sub]
  simp only [galoisCompletionMap, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
  rwa [norm_algebraMap_smul]

def galHom (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w' = σ • w) :
    w.adicCompletion L →+* w'.adicCompletion L :=
  (UniformSpace.Completion.extensionHom (galoisCompletionMap σ w w')
      (uniformContinuous_galoisCompletionMap σ w w' h).continuous).comp
    (HeightOneSpectrum.adicCompletion.equiv L w).toRingHom

theorem continuous_galHom (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w' = σ • w) :
    Continuous (galHom σ w w' h) :=
  UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion L w)

theorem galHom_algebraMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w' = σ • w)
    (x : L) : galHom σ w w' h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) := by
  change UniformSpace.Completion.extensionHom (galoisCompletionMap σ w w')
    (uniformContinuous_galoisCompletionMap σ w w' h).continuous
    ((WithVal.equiv (w.valuation L)).symm x : UniformSpace.Completion _) = _
  rw [UniformSpace.Completion.extensionHom_coe]
  rfl

theorem galHom_comp_galHom (σ τ : L ≃ₐ[K] L) (hστ : τ * σ = 1) (w w' : HeightOneSpectrum (𝓞 L))
    (h : w' = σ • w) (h' : w = τ • w') :
    (galHom τ w' w h').comp (galHom σ w w' h) = RingHom.id _ := by
  have := (HeightOneSpectrum.denseRange_algebraMap L w).equalizer
    ((continuous_galHom τ w' w h').comp (continuous_galHom σ w w' h)) continuous_id
    (funext fun x ↦ by
      simp only [Function.comp_apply, galHom_algebraMap, id_eq]
      rw [← AlgEquiv.mul_apply, hστ, AlgEquiv.one_apply])
  exact RingHom.ext (congrFun this)

variable [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem galHom_completionMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w)
    (a : v.adicCompletion K) : galHom σ w w' h (completionMap v w a) = completionMap v w' a := by
  have := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((continuous_galHom σ w w' h).comp (continuous_completionMap v w))
    (continuous_completionMap v w')
    (funext fun x ↦ by
      simp only [Function.comp_apply, completionMap_algebraMap,
        IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
        IsScalarTower.algebraMap_apply K L (w'.adicCompletion L), galHom_algebraMap,
        AlgEquiv.commutes])
  exact congrFun this a

def galEquiv (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w'.adicCompletion L :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (galHom σ w w' h) (galHom σ⁻¹ w' w (by rw [h, inv_smul_smul]))
      (galHom_comp_galHom σ⁻¹ σ (mul_inv_cancel σ) w' w _ h)
      (galHom_comp_galHom σ σ⁻¹ (inv_mul_cancel σ) w w' h _))
    (fun a ↦ galHom_completionMap v σ w w' h a)

theorem galEquiv_apply (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w)
    (y : w.adicCompletion L) : galEquiv v σ w w' h y = galHom σ w w' h y := rfl

theorem galEquiv_algebraMap (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) (x : L) :
    galEquiv v σ w w' h (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w'.adicCompletion L) (σ x) :=
  galHom_algebraMap σ w w' h x

theorem continuous_galEquiv (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    Continuous (galEquiv v σ w w' h) :=
  continuous_galHom σ w w' h

theorem continuous_galEquiv_symm (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    Continuous (galEquiv v σ w w' h).symm :=
  continuous_galHom σ⁻¹ w' w (by rw [h, inv_smul_smul])

def galContinuousEquiv (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal] (h : w' = σ • w) :
    ContinuousAlgEquiv (v.adicCompletion K) (w.adicCompletion L) (w'.adicCompletion L) where
  toAlgEquiv := galEquiv v σ w w' h
  continuous_toFun := continuous_galEquiv v σ w w' h
  continuous_invFun := continuous_galEquiv_symm v σ w w' h

omit [NumberField K] [NumberField L] in
theorem eq_smul_inv_smul (σ : L ≃ₐ[K] L) (u : PlacesOver L v) : u.1 = σ • (σ⁻¹ • u).1 := by
  rw [← coe_smul_placesOver, smul_inv_smul]

def piGal (σ : L ≃ₐ[K] L) : CompletionsOver L v →ₐ[v.adicCompletion K] CompletionsOver L v :=
  AlgHom.pi fun u ↦
    (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toAlgHom.comp
      (Pi.evalAlgHom _ _ (σ⁻¹ • u))

theorem piGal_apply (σ : L ≃ₐ[K] L) (y : CompletionsOver L v) (u : PlacesOver L v) :
    piGal v σ y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := rfl

theorem tensorEquiv_map_gal (σ : L ≃ₐ[K] L) (x : v.adicCompletion K ⊗[K] L) :
    tensorEquiv L v (Algebra.TensorProduct.map
      (AlgHom.id (v.adicCompletion K) (v.adicCompletion K)) σ.toAlgHom x) =
      piGal v σ (tensorEquiv L v x) := by
  have : (tensorEquiv L v).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion K) (v.adicCompletion K))
        σ.toAlgHom) = (piGal v σ).comp (tensorEquiv L v).toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro a l
    funext u
    simp [piGal_apply, Pi.mul_apply, galEquiv_algebraMap]
  exact DFunLike.congr_fun this x

end GaloisCompletions

/-! ### Local-Global Norm & Trace Decomposition (Finite Places) -/

section FiniteNormTrace

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

theorem norm_one_tmul (x : L) :
    Algebra.norm (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.norm K x) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem trace_one_tmul (x : L) :
    Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
        ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.trace K L x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

theorem algebraMap_norm_eq_prod (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : PlacesOver L v,
        Algebra.norm (v.adicCompletion K) (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← norm_one_tmul, ← Algebra.norm_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul,
    norm_pi]
  rfl

theorem algebraMap_trace_eq_sum (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L x) =
      ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L)
        (algebraMap L (w.1.adicCompletion L) x) := by
  rw [← trace_one_tmul, ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), tensorEquiv_one_tmul,
    trace_pi]
  rfl

end FiniteNormTrace

end SemiLocal

/-! ### Infinite Semilocal Algebras, Infinite Adele Base Change & Archimedean Norm Index -/

namespace InfinitePlace

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct ComplexConjugate

section NontriviallyNormed

variable {K : Type*} [Field K] (v : InfinitePlace K)

theorem norm_two_completion : ‖(2 : v.Completion)‖ = 2 := by
  have h := (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) 2
  rw [← h, map_ofNat]
  simp

instance instNontriviallyNormedFieldCompletion : NontriviallyNormedField v.Completion where
  non_trivial := ⟨2, by rw [norm_two_completion]; norm_num⟩

end NontriviallyNormed

section InfiniteTensor

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)

instance (w : v.placesOver L) : (w : InfinitePlace L).LiesOver v := w.2

instance (w : InfinitePlace L) : IsScalarTower K L w.Completion := .of_algebraMap_eq fun _ => rfl

abbrev PiPlacesOver : Type _ := (w : v.placesOver L) → (w : InfinitePlace L).Completion

def tensorPiHom : v.Completion ⊗[K] L →ₐ[v.Completion] PiPlacesOver (L := L) v :=
  Algebra.TensorProduct.lift (Algebra.ofId v.Completion _)
    ((Algebra.ofId L (PiPlacesOver (L := L) v)).restrictScalars K) (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorPiHom_tmul (x : v.Completion) (l : L) (w : v.placesOver L) :
    tensorPiHom v (x ⊗ₜ l) w =
      algebraMap v.Completion _ x * (l : (w : InfinitePlace L).Completion) := by
  simp [tensorPiHom]

variable {v} in
theorem finrank_completion_pos (w : InfinitePlace L) [w.LiesOver v] :
    0 < Module.finrank v.Completion w.Completion := by
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]; norm_num
  · rw [h.finrank_eq_two v]; norm_num

instance finiteDimensional_completion (w : InfinitePlace L) [w.LiesOver v] :
    FiniteDimensional v.Completion w.Completion :=
  Module.finite_of_finrank_pos (finrank_completion_pos w)

variable [NumberField K] [NumberField L]

open scoped Classical in
theorem sum_finrank_completion :
    ∑ w : v.placesOver L, Module.finrank v.Completion (w : InfinitePlace L).Completion =
      Module.finrank K L := by
  classical
  rw [← sum_inertiaDeg_eq_finrank K L v]
  refine Finset.sum_bij (fun w _ => w.1) (fun w _ => by simp)
    (fun a _ b _ h => Subtype.ext h) (fun b hb => ⟨⟨b, by simpa using hb⟩, Finset.mem_univ _, rfl⟩)
    (fun w _ => (inertiaDeg_eq_finrank v w.1).symm)

theorem finrank_piPlacesOver :
    Module.finrank v.Completion (PiPlacesOver (L := L) v) = Module.finrank K L := by
  classical
  rw [Module.finrank_pi_fintype, sum_finrank_completion]

theorem finrank_tensor :
    Module.finrank v.Completion (v.Completion ⊗[K] L) = Module.finrank K L :=
  Module.finrank_baseChange

omit [NumberField K] in
theorem denseRange_algebraMap_piPlacesOver :
    DenseRange (algebraMap L (PiPlacesOver (L := L) v)) := by
  classical
  let π : InfiniteAdeleRing L → PiPlacesOver (L := L) v := fun x w => x w
  have hπ : Continuous π := continuous_pi fun w => continuous_apply (w : InfinitePlace L)
  have hs : Function.Surjective π := fun y =>
    ⟨fun w => if h : w ∈ v.placesOver L then y ⟨w, h⟩ else 0, by ext w; simp [π]⟩
  exact hs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap L) hπ

theorem tensorPiHom_surjective : Function.Surjective (tensorPiHom (L := L) v) := by
  let f := (tensorPiHom (L := L) v).toLinearMap
  have hclosed : IsClosed (LinearMap.range f : Set (PiPlacesOver (L := L) v)) :=
    (LinearMap.range f).closed_of_finiteDimensional
  have hsub : Set.range (algebraMap L (PiPlacesOver (L := L) v)) ⊆ LinearMap.range f := by
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by ext w; simp [f]⟩
  have huniv : (LinearMap.range f : Set (PiPlacesOver (L := L) v)) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (denseRange_algebraMap_piPlacesOver v).closure_range]
    exact closure_minimal hsub hclosed
  intro y
  have hy : y ∈ (LinearMap.range f : Set (PiPlacesOver (L := L) v)) := huniv ▸ Set.mem_univ y
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, hx⟩

theorem tensorPiHom_bijective : Function.Bijective (tensorPiHom (L := L) v) := by
  refine ⟨?_, tensorPiHom_surjective v⟩
  have h : Module.finrank v.Completion (v.Completion ⊗[K] L) =
      Module.finrank v.Completion (PiPlacesOver (L := L) v) := by
    rw [finrank_tensor, finrank_piPlacesOver]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h
    (f := (tensorPiHom (L := L) v).toLinearMap)).mpr (tensorPiHom_surjective v)

def tensorPiEquiv : v.Completion ⊗[K] L ≃ₐ[v.Completion] PiPlacesOver (L := L) v :=
  AlgEquiv.ofBijective (tensorPiHom v) (tensorPiHom_bijective v)

@[simp]
theorem tensorPiEquiv_apply (x : v.Completion ⊗[K] L) :
    tensorPiEquiv (L := L) v x = tensorPiHom v x := rfl

omit [NumberField K] in
theorem isModuleTopology_piPlacesOver : IsModuleTopology v.Completion (PiPlacesOver (L := L) v) :=
  isModuleTopologyOfFiniteDimensional

def tensorPiHomeomorph :
    letI := moduleTopology v.Completion (v.Completion ⊗[K] L)
    v.Completion ⊗[K] L ≃ₜ PiPlacesOver (L := L) v :=
  letI := moduleTopology v.Completion (v.Completion ⊗[K] L)
  haveI : IsModuleTopology v.Completion (v.Completion ⊗[K] L) := ⟨rfl⟩
  haveI := isModuleTopology_piPlacesOver (L := L) v
  haveI := IsModuleTopology.toContinuousAdd v.Completion (v.Completion ⊗[K] L)
  { toEquiv := (tensorPiEquiv (L := L) v).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquiv (L := L) v).toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquiv (L := L) v).symm.toLinearMap }

@[simp]
theorem tensorPiHomeomorph_apply (x : v.Completion ⊗[K] L) :
    tensorPiHomeomorph (L := L) v x = tensorPiHom v x := rfl

def tensorPiEquivLeft : L ⊗[K] v.Completion ≃ₐ[L] PiPlacesOver (L := L) v :=
  AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.comm K L v.Completion).trans
      ((tensorPiEquiv (L := L) v).restrictScalars K)).toRingEquiv)
    (fun l => by ext w; simp [Algebra.TensorProduct.algebraMap_apply])

@[simp]
theorem tensorPiEquivLeft_tmul (l : L) (x : v.Completion) (w : v.placesOver L) :
    tensorPiEquivLeft (L := L) v (l ⊗ₜ x) w =
      (l : (w : InfinitePlace L).Completion) * algebraMap v.Completion _ x := by
  simp [tensorPiEquivLeft, mul_comm]

def tensorPiEquivRight :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
    L ⊗[K] v.Completion ≃ₐ[v.Completion] PiPlacesOver (L := L) v :=
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
  AlgEquiv.ofRingEquiv (f := (tensorPiEquivLeft (L := L) v).toRingEquiv)
    (fun x => by
      funext w
      change tensorPiEquivLeft (L := L) v (1 ⊗ₜ x) w = _
      rw [tensorPiEquivLeft_tmul, Completion.coe_one, one_mul]
      rfl)

def tensorPiHomeomorphRight :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
    letI := moduleTopology v.Completion (L ⊗[K] v.Completion)
    L ⊗[K] v.Completion ≃ₜ PiPlacesOver (L := L) v :=
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := v.Completion)
  letI := moduleTopology v.Completion (L ⊗[K] v.Completion)
  haveI : IsModuleTopology v.Completion (L ⊗[K] v.Completion) := ⟨rfl⟩
  haveI := isModuleTopology_piPlacesOver (L := L) v
  haveI := IsModuleTopology.toContinuousAdd v.Completion (L ⊗[K] v.Completion)
  { toEquiv := (tensorPiEquivRight (L := L) v).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquivRight (L := L) v).toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (tensorPiEquivRight (L := L) v).symm.toLinearMap }

@[simp]
theorem tensorPiHomeomorphRight_tmul (l : L) (x : v.Completion) (w : v.placesOver L) :
    tensorPiHomeomorphRight (L := L) v (l ⊗ₜ x) w =
      (l : (w : InfinitePlace L).Completion) * algebraMap v.Completion _ x :=
  tensorPiEquivLeft_tmul v l x w

theorem algebraMap_norm_eq_norm_tmul (l : L) :
    algebraMap K v.Completion (Algebra.norm K l) =
      Algebra.norm v.Completion ((1 : v.Completion) ⊗ₜ[K] l) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem algebraMap_trace_eq_trace_tmul (l : L) :
    algebraMap K v.Completion (Algebra.trace K L l) =
      Algebra.trace v.Completion _ ((1 : v.Completion) ⊗ₜ[K] l) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

open scoped Classical in
theorem norm_tensor_eq_prod (x : v.Completion ⊗[K] L) :
    Algebra.norm v.Completion x =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (tensorPiHom v x w) := by
  rw [← Algebra.norm_eq_of_algEquiv (tensorPiEquiv (L := L) v) x, tensorPiEquiv_apply, norm_pi]

open scoped Classical in
theorem trace_tensor_eq_sum (x : v.Completion ⊗[K] L) :
    Algebra.trace v.Completion _ x =
      ∑ w : v.placesOver L, Algebra.trace v.Completion _ (tensorPiHom v x w) := by
  rw [← Algebra.trace_eq_of_algEquiv (tensorPiEquiv (L := L) v) x, tensorPiEquiv_apply, trace_pi]

open scoped Classical in
theorem algebraMap_norm_eq_prod (l : L) :
    algebraMap K v.Completion (Algebra.norm K l) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (l : (w : InfinitePlace L).Completion) := by
  rw [algebraMap_norm_eq_norm_tmul, norm_tensor_eq_prod]
  simp

open scoped Classical in
theorem algebraMap_trace_eq_sum (l : L) :
    algebraMap K v.Completion (Algebra.trace K L l) =
      ∑ w : v.placesOver L,
        Algebra.trace v.Completion _ (l : (w : InfinitePlace L).Completion) := by
  rw [algebraMap_trace_eq_trace_tmul, trace_tensor_eq_sum]
  simp

end InfiniteTensor

section InfiniteAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)

theorem liesOver_iff_comap_eq (w : InfinitePlace L) :
    w.LiesOver v ↔ w.comap (algebraMap K L) = v :=
  ⟨fun _ => NumberField.InfinitePlace.LiesOver.comap_eq w v, fun h => ⟨congrArg Subtype.val h⟩⟩

theorem comap_smul_algebraMap (σ : Gal(L/K)) (w : InfinitePlace L) :
    (σ • w).comap (algebraMap K L) = w.comap (algebraMap K L) := by
  rw [comap_smul]
  congr 1
  ext x
  simp

instance : MulAction Gal(L/K) (v.placesOver L) where
  smul σ w := ⟨σ • (w : InfinitePlace L), (liesOver_iff_comap_eq v _).2 <| by
    rw [comap_smul_algebraMap, (liesOver_iff_comap_eq v _).1 w.2]⟩
  one_smul w := Subtype.ext (one_smul _ (w : InfinitePlace L))
  mul_smul σ τ w := Subtype.ext (mul_smul σ τ (w : InfinitePlace L))

@[simp]
theorem coe_smul_placesOver (σ : Gal(L/K)) (w : v.placesOver L) :
    ((σ • w : v.placesOver L) : InfinitePlace L) = σ • (w : InfinitePlace L) := rfl

theorem exists_smul_eq_of_liesOver [IsGalois K L] (w w' : InfinitePlace L) [w.LiesOver v]
    [w'.LiesOver v] : ∃ σ : Gal(L/K), σ • w = w' :=
  exists_smul_eq_of_comap_eq <| by
    rw [(liesOver_iff_comap_eq v w).1 ‹_›, (liesOver_iff_comap_eq v w').1 ‹_›]

instance [IsGalois K L] : MulAction.IsPretransitive Gal(L/K) (v.placesOver L) where
  exists_smul_eq w w' := by
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_liesOver v (w : InfinitePlace L) (w' : InfinitePlace L)
    exact ⟨σ, Subtype.ext hσ⟩

end InfiniteAction

section InfiniteAdeleBaseChange

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance liesOver_comap (w : InfinitePlace L) : w.LiesOver (w.comap (algebraMap K L)) :=
  (liesOver_iff_comap_eq _ w).2 rfl

def piPlacesOverEquiv :
    ((v : InfinitePlace K) → PiPlacesOver (L := L) v) ≃ₐ[L] InfiniteAdeleRing L where
  toFun x w := x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩
  invFun y v w := y w
  left_inv x := by
    funext v w
    obtain ⟨w, hw⟩ := w
    have h : w.comap (algebraMap K L) = v := (liesOver_iff_comap_eq v w).1 hw
    subst h
    rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem piPlacesOverEquiv_apply (x : (v : InfinitePlace K) → PiPlacesOver (L := L) v)
    (w : InfinitePlace L) :
    piPlacesOverEquiv x w = x (w.comap (algebraMap K L)) ⟨w, liesOver_comap w⟩ := rfl

def infiniteAdeleRingMap : InfiniteAdeleRing K →+* InfiniteAdeleRing L :=
  RingHom.pi fun w : InfinitePlace L =>
    (algebraMap (w.comap (algebraMap K L)).Completion w.Completion).comp
      (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) (w.comap (algebraMap K L)))

@[simp]
theorem infiniteAdeleRingMap_apply (x : InfiniteAdeleRing K) (w : InfinitePlace L) :
    infiniteAdeleRingMap x w =
      algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := rfl

theorem continuous_infiniteAdeleRingMap :
    Continuous (infiniteAdeleRingMap (K := K) (L := L)) :=
  continuous_pi fun w =>
    (NumberField.LiesOver.continuous_completionMap (v := w.comap (algebraMap K L)) (w := w)).comp
      (continuous_apply (w.comap (algebraMap K L)))

theorem infiniteAdeleRingMap_algebraMap (k : K) :
    infiniteAdeleRingMap (algebraMap K (InfiniteAdeleRing K) k) =
      algebraMap L (InfiniteAdeleRing L) (algebraMap K L k) := by
  funext w
  rw [infiniteAdeleRingMap_apply, InfiniteAdeleRing.algebraMap_apply,
    InfiniteAdeleRing.algebraMap_apply, ← Completion.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L]
  rfl

variable [NumberField K] [NumberField L]

open scoped Classical in
def tensorInfiniteAdeleRingEquiv :
    L ⊗[K] InfiniteAdeleRing K ≃ₐ[L] InfiniteAdeleRing L :=
  (Algebra.TensorProduct.piRight K L L (fun v : InfinitePlace K => v.Completion)).trans <|
    (AlgEquiv.piCongrRight fun v => tensorPiEquivLeft (L := L) v).trans piPlacesOverEquiv

theorem tensorInfiniteAdeleRingEquiv_tmul (l : L) (x : InfiniteAdeleRing K)
    (w : InfinitePlace L) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) w =
      (l : w.Completion) * algebraMap (w.comap (algebraMap K L)).Completion w.Completion
        (x (w.comap (algebraMap K L))) := by
  change tensorPiEquivLeft (L := L) (w.comap (algebraMap K L))
    (l ⊗ₜ x (w.comap (algebraMap K L))) ⟨w, liesOver_comap w⟩ = _
  rw [tensorPiEquivLeft_tmul]

theorem tensorInfiniteAdeleRingEquiv_tmul' (l : L) (x : InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingEquiv (l ⊗ₜ x) =
      algebraMap L (InfiniteAdeleRing L) l * infiniteAdeleRingMap x := by
  funext w
  rw [tensorInfiniteAdeleRingEquiv_tmul]
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (i : ι) : PiPlacesOver (L := L) v →ₗ[v.Completion] v.Completion :=
  ((Algebra.TensorProduct.basis v.Completion b).coord i).comp
    (tensorPiEquiv (L := L) v).symm.toLinearMap

theorem continuous_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (v : InfinitePlace K) (i : ι) :
    Continuous (piPlacesOverCoord b v i) :=
  LinearMap.continuous_of_finiteDimensional _

theorem sum_piPlacesOverCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (v : InfinitePlace K) (y : PiPlacesOver (L := L) v) (w : v.placesOver L) :
    ∑ i, algebraMap v.Completion _ (piPlacesOverCoord b v i y) *
      (b i : (w : InfinitePlace L).Completion) = y w := by
  have h := (Algebra.TensorProduct.basis v.Completion b).sum_repr
    ((tensorPiEquiv (L := L) v).symm y)
  have h2 := congrArg (fun z => tensorPiEquiv (L := L) v z w) h
  simp only [AlgEquiv.apply_symm_apply] at h2
  rw [← h2, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, Pi.smul_apply, tensorPiEquiv_apply,
    tensorPiHom_tmul, map_one, one_mul, Algebra.smul_def]
  rfl

def adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L) (i : ι)
    (y : InfiniteAdeleRing L) : InfiniteAdeleRing K :=
  fun v => piPlacesOverCoord b v i (fun w => y w)

theorem continuous_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)
    (i : ι) : Continuous (adeleCoord b i) :=
  continuous_pi fun v => (continuous_piPlacesOverCoord b v i).comp
    (continuous_pi fun w => continuous_apply (w : InfinitePlace L))

theorem tensorInfiniteAdeleRingEquiv_sum_adeleCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (y : InfiniteAdeleRing L) :
    tensorInfiniteAdeleRingEquiv (∑ i, b i ⊗ₜ[K] adeleCoord b i y) = y := by
  funext w
  have ev : ∀ f : ι → InfiniteAdeleRing L, (∑ i, f i) w = ∑ i, f i w := fun f =>
    map_sum (Pi.evalAddMonoidHom (fun w : InfinitePlace L => w.Completion) w) f Finset.univ
  rw [map_sum, ev]
  simp_rw [tensorInfiniteAdeleRingEquiv_tmul]
  have := sum_piPlacesOverCoord b (w.comap (algebraMap K L)) (fun w' => y w') ⟨w, liesOver_comap w⟩
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

def tmulLeft (l : L) : InfiniteAdeleRing K →ₗ[InfiniteAdeleRing K] L ⊗[K] InfiniteAdeleRing K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def tensorInfiniteAdeleRingHomeomorph :
    letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
    L ⊗[K] InfiniteAdeleRing K ≃ₜ InfiniteAdeleRing L :=
  letI := moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  haveI : IsModuleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  let b := Module.finBasis K L
  { toEquiv := (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] InfiniteAdeleRing K →ₛₗ[infiniteAdeleRingMap (K := K) (L := L)]
          InfiniteAdeleRing L :=
        { toFun := tensorInfiniteAdeleRingEquiv
          map_add' := map_add _
          map_smul' := fun c t => by
            change tensorInfiniteAdeleRingEquiv ((1 ⊗ₜ c) * t) = infiniteAdeleRingMap c * _
            rw [map_mul, tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_infiniteAdeleRingMap φ
    continuous_invFun := by
      have h : ∀ y, (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y =
          ∑ i, tmulLeft (b i) (adeleCoord b i y) := fun y => by
        rw [AlgEquiv.symm_apply_eq]
        exact (tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y).symm
      change Continuous fun y => (tensorInfiniteAdeleRingEquiv (K := K) (L := L)).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ =>
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (b i))).comp
          (continuous_adeleCoord b i) }

@[simp]
theorem tensorInfiniteAdeleRingHomeomorph_apply (x : L ⊗[K] InfiniteAdeleRing K) :
    tensorInfiniteAdeleRingHomeomorph x = tensorInfiniteAdeleRingEquiv x := rfl

end InfiniteAdeleBaseChange

/-! ## Part 3: Global Infinite Norm Index, Archimedean Local Symbol & Herbrand Quotient -/

section InfiniteNormIndex

open ProfCoh

theorem natCard_kerModRange_eq_one {A : Type*} [AddCommGroup A] {f g : A →+ A}
    (h : ∀ x ∈ f.ker, x ∈ g.range) : Nat.card (KerModRange f g) = 1 := by
  have : Subsingleton (KerModRange f g) := ⟨fun p q => by
    induction p using QuotientAddGroup.induction_on with | H x =>
    induction q using QuotientAddGroup.induction_on with | H y =>
    rw [KerModRange.mk_eq_mk_iff]
    exact h _ (sub_mem x.2 y.2)⟩
  exact Nat.card_of_subsingleton (0 : KerModRange f g)

def realSignHom {G : Type*} [Group G] (c : G) (hc : c * c = 1) : ℝˣ →* G where
  toFun x := if (x : ℝ) < 0 then c else 1
  map_one' := by simp
  map_mul' x y := by
    simp only [Units.val_mul]
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;>
      rcases lt_or_gt_of_ne y.ne_zero with hy | hy
    · simp [hx, hy, not_lt.2 (mul_pos_of_neg_of_neg hx hy).le, hc]
    · simp [hx, not_lt.2 hy.le, mul_neg_of_neg_of_pos hx hy]
    · simp [not_lt.2 hx.le, hy, mul_neg_of_pos_of_neg hx hy]
    · simp [not_lt.2 hx.le, not_lt.2 hy.le, not_lt.2 (mul_pos hx hy).le]

theorem realSignHom_apply {G : Type*} [Group G] (c : G) (hc : c * c = 1) (x : ℝˣ) :
    realSignHom c hc x = if (x : ℝ) < 0 then c else 1 :=
  rfl

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]

theorem finrank_completion_eq_two_iff :
    Module.finrank v.Completion w.Completion = 2 ↔ v.IsReal ∧ w.IsComplex := by
  have hc : w.comap (algebraMap K L) = v := NumberField.InfinitePlace.LiesOver.comap_eq w v
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]
    refine ⟨fun h' => absurd h' (by norm_num), fun ⟨hv, hw⟩ => absurd h ?_⟩
    exact isRamified_iff.2 ⟨hw, hc ▸ hv⟩
  · rw [h.finrank_eq_two v]
    exact ⟨fun _ => ⟨hc ▸ h.isReal, h.isComplex⟩, fun _ => rfl⟩

theorem finrank_completion_eq_one_iff :
    Module.finrank v.Completion w.Completion = 1 ↔ ¬ (v.IsReal ∧ w.IsComplex) := by
  rw [← finrank_completion_eq_two_iff w]
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v]; norm_num
  · rw [h.finrank_eq_two v]; norm_num

section Conj

variable {w}

theorem extensionEmbedding_algebraMap (hv : v.IsReal) (x : v.Completion) :
    extensionEmbedding w (algebraMap v.Completion w.Completion x) =
      (extensionEmbeddingOfIsReal hv x : ℂ) := by
  have := NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal w hv
  rw [extensionEmbeddingOfIsReal_apply]
  exact Completion.liesOver_extensionEmbedding_apply w v

open scoped Classical in
def completionConj (hv : v.IsReal) : Gal(w.Completion/v.Completion) :=
  if hw : w.IsComplex then
    AlgEquiv.ofRingEquiv (f := ((ringEquivComplexOfIsComplex hw).trans
      (starRingAut : RingAut ℂ)).trans (ringEquivComplexOfIsComplex hw).symm) (fun x => by
        apply (ringEquivComplexOfIsComplex hw).injective
        simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, ringEquivComplexOfIsComplex_apply,
          extensionEmbedding_algebraMap hv, starRingAut_apply]
        exact Complex.conj_ofReal _)
  else 1

theorem extensionEmbedding_completionConj (hv : v.IsReal) (x : w.Completion) :
    extensionEmbedding w (completionConj hv x) = conj (extensionEmbedding w x) := by
  by_cases hw : w.IsComplex
  · rw [← ringEquivComplexOfIsComplex_apply hw]
    simp [completionConj, dif_pos hw]
  · rw [completionConj, dif_neg hw, AlgEquiv.one_apply,
      ← extensionEmbeddingOfIsReal_apply (not_isComplex_iff_isReal.1 hw), Complex.conj_ofReal]

theorem completionConj_mul_self (hv : v.IsReal) :
    completionConj (w := w) hv * completionConj hv = 1 := by
  refine AlgEquiv.ext fun x => ?_
  apply (extensionEmbedding w).injective
  simp [AlgEquiv.mul_apply, extensionEmbedding_completionConj]

theorem completionConj_ne_one (hv : v.IsReal) (hw : w.IsComplex) :
    completionConj (w := w) hv ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := surjective_extensionEmbedding_of_isComplex hw Complex.I
  have := extensionEmbedding_completionConj (w := w) hv z
  rw [h, AlgEquiv.one_apply, hz, Complex.conj_I] at this
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination this
  simp at h2

open scoped Classical in
theorem eq_one_or_eq_completionConj (hv : v.IsReal) (hw : w.IsComplex)
    (σ : Gal(w.Completion/v.Completion)) : σ = 1 ∨ σ = completionConj hv := by
  by_contra h
  push Not at h
  have hcard := AlgEquiv.card_le (F := v.Completion) (K := w.Completion)
  rw [(finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩] at hcard
  have h3 : ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion)).card = 3 :=
    Finset.card_eq_three.2 ⟨1, completionConj hv, σ, (completionConj_ne_one hv hw).symm,
      h.1.symm, h.2.symm, rfl⟩
  have := Finset.card_le_univ ({1, completionConj hv, σ} : Finset Gal(w.Completion/v.Completion))
  omega

open scoped Classical in
theorem univ_eq_one_completionConj (hv : v.IsReal) (hw : w.IsComplex) :
    (Finset.univ : Finset Gal(w.Completion/v.Completion)) = {1, completionConj hv} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_one_or_eq_completionConj hv hw σ

theorem card_gal_eq_two (hv : v.IsReal) (hw : w.IsComplex) :
    Fintype.card Gal(w.Completion/v.Completion) = 2 := by
  classical
  rw [← Finset.card_univ, univ_eq_one_completionConj hv hw]
  exact Finset.card_pair (completionConj_ne_one hv hw).symm

variable (w) in
theorem subsingleton_gal (h : ¬ (v.IsReal ∧ w.IsComplex)) :
    Subsingleton Gal(w.Completion/v.Completion) := by
  have hcard := AlgEquiv.card_le (F := v.Completion) (K := w.Completion)
  rw [(finrank_completion_eq_one_iff w).2 h] at hcard
  exact Fintype.card_le_one_iff_subsingleton.1 hcard

variable (w) in
theorem natCard_gal_completion :
    Nat.card Gal(w.Completion/v.Completion) = Module.finrank v.Completion w.Completion := by
  rw [Nat.card_eq_fintype_card]
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · rw [card_gal_eq_two h2.1 h2.2, (finrank_completion_eq_two_iff w).2 h2]
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    exact Fintype.card_eq_one_iff.2 ⟨1, fun _ => Subsingleton.elim _ _⟩

instance isGalois_completion : IsGalois v.Completion w.Completion :=
  IsGalois.of_card_aut_eq_finrank (h := natCard_gal_completion w)

end Conj

section Norm

variable {w}

theorem algebraMap_norm_completion (hv : v.IsReal) (hw : w.IsComplex) (y : w.Completion) :
    algebraMap v.Completion w.Completion (Algebra.norm v.Completion y) =
      y * completionConj (w := w) hv y := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, univ_eq_one_completionConj hv hw,
    Finset.prod_pair (completionConj_ne_one hv hw).symm, AlgEquiv.one_apply]

theorem extensionEmbeddingOfIsReal_norm (hv : v.IsReal) (hw : w.IsComplex) (y : w.Completion) :
    extensionEmbeddingOfIsReal hv (Algebra.norm v.Completion y) =
      Complex.normSq (extensionEmbedding w y) := by
  apply Complex.ofReal_injective
  rw [← extensionEmbedding_algebraMap (w := w) hv, algebraMap_norm_completion hv hw, map_mul,
    extensionEmbedding_completionConj, Complex.mul_conj]

variable (v w) in
def normSubgroup : Subgroup v.Completionˣ :=
  (Units.map (Algebra.norm v.Completion : w.Completion →* v.Completion)).range

theorem mem_normSubgroup_iff (hv : v.IsReal) (hw : w.IsComplex) (x : v.Completionˣ) :
    x ∈ normSubgroup v w ↔ 0 < extensionEmbeddingOfIsReal hv x := by
  rw [normSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Units.coe_map, extensionEmbeddingOfIsReal_norm hv hw]
    exact Complex.normSq_pos.2 ((map_ne_zero _).2 y.ne_zero)
  · intro hx
    obtain ⟨a, ha⟩ := surjective_extensionEmbeddingOfIsReal hv
      (Real.sqrt (extensionEmbeddingOfIsReal hv x))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm, Real.sqrt_eq_zero hx.le] at ha
      exact hx.ne' ha
    refine ⟨Units.mk0 (algebraMap v.Completion w.Completion a) ((map_ne_zero _).2 ha0), ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0, Algebra.norm_algebraMap,
      (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    apply (extensionEmbeddingOfIsReal hv).injective
    rw [map_pow, ha, Real.sq_sqrt hx.le]

variable (w) in
theorem normSubgroup_eq_top (h : ¬ (v.IsReal ∧ w.IsComplex)) : normSubgroup v w = ⊤ := by
  rw [eq_top_iff]
  intro x _
  refine ⟨Units.map (algebraMap v.Completion w.Completion : v.Completion →* w.Completion) x, ?_⟩
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, MonoidHom.coe_coe, Algebra.norm_algebraMap,
    (finrank_completion_eq_one_iff w).2 h, pow_one]

end Norm

section LocalSymbol

variable (v)

open scoped Classical in
def localSymbol : v.Completionˣ →* Gal(w.Completion/v.Completion) :=
  if hv : v.IsReal then
    (realSignHom (completionConj (w := w) hv) (completionConj_mul_self hv)).comp
      (Units.map (extensionEmbeddingOfIsReal hv).toMonoidHom)
  else 1

theorem localSymbol_apply (hv : v.IsReal) (x : v.Completionˣ) :
    localSymbol v w x =
      if extensionEmbeddingOfIsReal hv x < 0 then completionConj hv else 1 := by
  simp only [localSymbol, dif_pos hv, MonoidHom.comp_apply, realSignHom_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact if_congr Iff.rfl rfl rfl

theorem localSymbol_of_not_isReal (hv : ¬ v.IsReal) : localSymbol v w = 1 := by
  rw [localSymbol, dif_neg hv]

theorem ker_localSymbol : (localSymbol v w).ker = normSubgroup v w := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    ext x
    rw [MonoidHom.mem_ker, localSymbol_apply v w hv, mem_normSubgroup_iff hv hw]
    have hx0 : extensionEmbeddingOfIsReal hv x ≠ 0 := (map_ne_zero _).2 x.ne_zero
    constructor
    · intro h
      by_contra hneg
      have hlt : extensionEmbeddingOfIsReal hv x < 0 := lt_of_le_of_ne (not_lt.1 hneg) hx0
      rw [if_pos hlt] at h
      exact completionConj_ne_one hv hw h
    · intro h
      rw [if_neg (not_lt.2 h.le)]
  · rw [normSubgroup_eq_top w h2, eq_top_iff]
    intro x _
    rw [MonoidHom.mem_ker]
    by_cases hv : v.IsReal
    · have hw : ¬ w.IsComplex := fun hw => h2 ⟨hv, hw⟩
      rw [localSymbol_apply v w hv, completionConj, dif_neg hw, ite_self]
    · rw [localSymbol_of_not_isReal v w hv, MonoidHom.one_apply]

theorem localSymbol_surjective : Function.Surjective (localSymbol v w) := by
  intro σ
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    rcases eq_one_or_eq_completionConj hv hw σ with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨-1, ?_⟩
      rw [localSymbol_apply v w hv, if_pos]
      simp
  · have := subsingleton_gal w h2
    exact ⟨1, Subsingleton.elim _ _⟩

def normQuotientEquivGal : v.Completionˣ ⧸ normSubgroup v w ≃* Gal(w.Completion/v.Completion) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_localSymbol v w).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (localSymbol_surjective v w))

theorem natCard_quotient_normSubgroup :
    Nat.card (v.Completionˣ ⧸ normSubgroup v w) = Module.finrank v.Completion w.Completion := by
  rw [Nat.card_congr (normQuotientEquivGal v w).toEquiv, natCard_gal_completion w]

end LocalSymbol

section Herbrand

variable (v)

abbrev unitsRep : Representation ℤ Gal(w.Completion/v.Completion) (Additive w.Completionˣ) :=
  zRepOfMonoidEnd (galUnitsHom v.Completion w.Completion)

theorem unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((unitsRep v w σ x).toMul : w.Completion) = σ (x.toMul : w.Completion) :=
  rfl

theorem cycSub_unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((cycSub (unitsRep v w) σ x).toMul : w.Completion) =
      σ (x.toMul : w.Completion) / (x.toMul : w.Completion) := by
  rw [cycSub_apply, toMul_sub, Units.val_div_eq_div_val, unitsRep_toMul]

variable {v w}

theorem normHom_unitsRep_toMul (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ) :
    ((normHom (unitsRep v w) x).toMul : w.Completion) =
      (x.toMul : w.Completion) * completionConj (w := w) hv (x.toMul : w.Completion) := by
  classical
  rw [Stage13CFT_IdeleNormResidue.normHom_apply, univ_eq_one_completionConj hv hw,
    Finset.sum_pair (completionConj_ne_one hv hw).symm, toMul_add, Units.val_mul, unitsRep_toMul,
    unitsRep_toMul, AlgEquiv.one_apply]

theorem re_pos_of_mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex)
    {x : Additive w.Completionˣ} (hx : x ∈ (normHom (unitsRep v w)).range) :
    0 < (extensionEmbedding w (x.toMul : w.Completion)).re := by
  obtain ⟨y, rfl⟩ := hx
  rw [normHom_unitsRep_toMul hv hw, map_mul, extensionEmbedding_completionConj, Complex.mul_conj,
    Complex.ofReal_re]
  exact Complex.normSq_pos.2 ((map_ne_zero _).2 (Units.ne_zero _))

theorem mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ)
    (hx : completionConj (w := w) hv (x.toMul : w.Completion) = x.toMul)
    (hpos : 0 < (extensionEmbedding w (x.toMul : w.Completion)).re) :
    x ∈ (normHom (unitsRep v w)).range := by
  have hreal : extensionEmbedding w (x.toMul : w.Completion) =
      ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
    have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
    rw [hx] at h
    exact (Complex.conj_eq_iff_re.1 h.symm).symm
  set r := (extensionEmbedding w (x.toMul : w.Completion)).re
  obtain ⟨a, ha⟩ := surjective_extensionEmbedding_of_isComplex hw (Real.sqrt r : ℂ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Complex.ofReal_eq_zero, Real.sqrt_eq_zero hpos.le] at ha
    exact hpos.ne' ha
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  apply (extensionEmbedding w).injective
  rw [normHom_unitsRep_toMul hv hw, toMul_ofMul, Units.val_mk0, map_mul,
    extensionEmbedding_completionConj, ha, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt hpos.le, ← hreal]

theorem exists_conj_eq_mul {z : ℂ} (hz : z * conj z = 1) : ∃ u : ℂ, u ≠ 0 ∧ conj u = z * u := by
  by_cases h : 1 + conj z = 0
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    have h1 : conj z = -1 := by linear_combination h
    have h2 : z = -1 := by simpa using congrArg conj h1
    rw [h2, Complex.conj_I]
    ring
  · refine ⟨1 + conj z, h, ?_⟩
    rw [map_add, map_one, Complex.conj_conj]
    linear_combination -hz

variable (v w)

theorem natCard_kerModRange_cycSub_normHom (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (cycSub (unitsRep v w) (completionConj hv))
      (normHom (unitsRep v w))) = 2 := by
  set c := completionConj (w := w) hv
  have hker : ∀ x : Additive w.Completionˣ,
      x ∈ (cycSub (unitsRep v w) c).ker ↔ c (x.toMul : w.Completion) = x.toMul := by
    intro x
    rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, cycSub_unitsRep_toMul,
      div_eq_one_iff_eq (Units.ne_zero _)]
  set m : Additive w.Completionˣ := Additive.ofMul (-1)
  have hm : m ∈ (cycSub (unitsRep v w) c).ker := by
    rw [hker]
    simp [m]
  have hme : extensionEmbedding w (m.toMul : w.Completion) = -1 := by simp [m]
  rw [Nat.card_eq_two_iff]
  refine ⟨QuotientAddGroup.mk ⟨0, zero_mem _⟩, QuotientAddGroup.mk ⟨m, hm⟩, ?_, ?_⟩
  · rw [Ne, KerModRange.mk_eq_mk_iff]
    intro h
    have := re_pos_of_mem_range_normHom hv hw h
    rw [AddSubgroup.coe_mk, zero_sub, toMul_neg, Units.val_inv_eq_inv_val, map_inv₀, hme] at this
    norm_num at this
  · rw [Set.eq_univ_iff_forall]
    intro q
    induction q using QuotientAddGroup.induction_on with | H z =>
    obtain ⟨x, hx⟩ := z
    have hc := (hker x).1 hx
    have hreal : extensionEmbedding w (x.toMul : w.Completion) =
        ((extensionEmbedding w (x.toMul : w.Completion)).re : ℂ) := by
      have h := extensionEmbedding_completionConj (w := w) hv (x.toMul : w.Completion)
      rw [hc] at h
      exact (Complex.conj_eq_iff_re.1 h.symm).symm
    have hne : (extensionEmbedding w (x.toMul : w.Completion)).re ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, map_eq_zero] at hreal
      exact Units.ne_zero _ hreal
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · right
      rw [KerModRange.mk_eq_mk_iff]
      apply mem_range_normHom hv hw
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀, hc,
          (hker m).1 hm]
      · rw [AddSubgroup.coe_mk, AddSubgroup.coe_mk, toMul_sub, Units.val_div_eq_div_val, map_div₀,
          hme, div_neg, div_one, Complex.neg_re]
        linarith
    · left
      rw [KerModRange.mk_eq_mk_iff, AddSubgroup.coe_mk, AddSubgroup.coe_mk, sub_zero]
      exact mem_range_normHom hv hw x hc hpos

theorem natCard_kerModRange_normHom_cycSub (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (normHom (unitsRep v w))
      (cycSub (unitsRep v w) (completionConj hv))) = 1 := by
  apply natCard_kerModRange_eq_one
  intro x hx
  rw [AddMonoidHom.mem_ker, ← toMul_eq_one, ← Units.val_eq_one, normHom_unitsRep_toMul hv hw] at hx
  have hz : extensionEmbedding w (x.toMul : w.Completion) *
      conj (extensionEmbedding w (x.toMul : w.Completion)) = 1 := by
    rw [← extensionEmbedding_completionConj hv, ← map_mul, hx, map_one]
  obtain ⟨u, hu0, hu⟩ := exists_conj_eq_mul hz
  obtain ⟨y, rfl⟩ := surjective_extensionEmbedding_of_isComplex hw u
  have hy0 : y ≠ 0 := by rintro rfl; exact hu0 (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [cycSub_unitsRep_toMul, toMul_ofMul, Units.val_mk0, div_eq_iff hy0]
  apply (extensionEmbedding w).injective
  rw [extensionEmbedding_completionConj, hu, map_mul]

theorem cyclicHerbrand_unitsRep_eq_two (hv : v.IsReal) (hw : w.IsComplex) :
    cyclicHerbrand (unitsRep v w) (completionConj hv) = 2 := by
  rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_cycSub_normHom v w hv hw,
    natCard_kerModRange_normHom_cycSub v w hv hw]
  norm_num

theorem hasCyclicHerbrand_unitsRep (hv : v.IsReal) (hw : w.IsComplex) :
    HasCyclicHerbrand (unitsRep v w) (completionConj hv) :=
  ⟨Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_cycSub_normHom v w hv hw]; norm_num),
    Nat.finite_of_card_ne_zero (by rw [natCard_kerModRange_normHom_cycSub v w hv hw]; norm_num)⟩

theorem cyclicHerbrand_unitsRep_eq_finrank (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (unitsRep v w) σ = Module.finrank v.Completion w.Completion := by
  by_cases h2 : v.IsReal ∧ w.IsComplex
  · obtain ⟨hv, hw⟩ := h2
    have hσc : σ = completionConj hv := by
      rcases eq_one_or_eq_completionConj hv hw σ with h | h
      · exfalso
        have := hσ (completionConj hv)
        rw [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
        exact completionConj_ne_one hv hw this
      · exact h
    rw [hσc, cyclicHerbrand_unitsRep_eq_two v w hv hw, (finrank_completion_eq_two_iff w).2 ⟨hv, hw⟩]
    norm_num
  · rw [(finrank_completion_eq_one_iff w).2 h2]
    have := subsingleton_gal w h2
    have hsub : ∀ x, cycSub (unitsRep v w) σ x = 0 := fun x => by
      rw [Subsingleton.elim σ 1, cycSub_apply, map_one, Module.End.one_apply, sub_self]
    have hnorm : ∀ x, normHom (unitsRep v w) x = x := fun x => by
      rw [Stage13CFT_IdeleNormResidue.normHom_apply, Fintype.sum_subsingleton _ 1, map_one, Module.End.one_apply]
    rw [cyclicHerbrand, herbrandQuotient, natCard_kerModRange_eq_one (fun x _ => ⟨x, hnorm x⟩),
      natCard_kerModRange_eq_one (fun x hx => ⟨0, by
        rw [map_zero]; rw [AddMonoidHom.mem_ker, hnorm] at hx; exact hx.symm⟩)]
    norm_num

end Herbrand

end InfiniteNormIndex

end InfinitePlace

/-! ## Part 4: Adele Ring Topology, Weak Approximation, Base Change, Idele Norms & Galois Action -/

section LocalFieldBridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero

section ValuativeRelInstances

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

instance : ValuativeRel (v.adicCompletion K) := .ofValuation Valued.v

instance : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible := .ofValuation _

instance : IsValuativeTopology (v.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_iff_vle Valued.v Valued.mem_nhds

instance : ValuativeRel.IsNontrivial (v.adicCompletion K) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial Valued.v).2 inferInstance

theorem mem_valuationInteger_iff (x : v.adicCompletion K) :
    x ∈ 𝒪[v.adicCompletion K] ↔ x ∈ v.adicCompletionIntegers K := by
  rw [Valuation.mem_integer_iff, mem_adicCompletionIntegers,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one]

end ValuativeRelInstances

section NonarchimedeanLocalField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : IsNonarchimedeanLocalField (v.adicCompletion K) where

end NonarchimedeanLocalField

section IntegralClosureBridge_Density

open SemiLocal

variable {L : Type*} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

theorem adicCompletionIntegers_subset_closure_ringOfIntegers :
    (w.adicCompletionIntegers L : Set (w.adicCompletion L)) ⊆
      closure (Set.range fun r : 𝓞 L ↦ algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 hs
  have h1 : {y : w.adicCompletion L | Valued.v.restrict (y - x) < γ.1} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨γ, subset_rfl⟩
  have h2 : {y : w.adicCompletion L | Valued.v.restrict (y - x) <
      ((1 : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
        Valuation (w.adicCompletion L) ℤᵐ⁰)))ˣ) : _)} ∈ nhds x :=
    Valued.mem_nhds.2 ⟨1, subset_rfl⟩
  obtain ⟨k, hk1, hk2⟩ := (denseRange_algebraMap (R := 𝓞 L) (K := L) w).mem_nhds
    (Filter.inter_mem h1 h2)
  simp only [Set.mem_ofPred_eq, Units.val_one, Valuation.restrict_lt_iff_lt_embedding] at hk1 hk2
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := by simp [hc]
  have hx1 : Valued.v x ≤ 1 := hx
  have hkv : w.valuation L k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation' w k]
    have : (k : w.adicCompletion L) = (algebraMap L (w.adicCompletion L) k - x) + x := by
      rw [sub_add_cancel]; rfl
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le hk2.le hx1)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_of_integer w hkv (Units.mk0 c hc0)
  refine ⟨_, hγ ?_, r, rfl⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  have hr' : Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) -
      algebraMap L (w.adicCompletion L) k) < c := by
    rw [← map_sub]
    exact (valuedAdicCompletion_eq_valuation' w _).trans_lt hr
  have : algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) - x =
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r) -
        algebraMap L (w.adicCompletion L) k) + (algebraMap L (w.adicCompletion L) k - x) := by
    ring
  rw [this]
  exact Valuation.map_add_lt _ hr' hk1

end IntegralClosureBridge_Density

section IntegralClosureBridge

open SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

instance valuativeExtension_adicCompletion :
    ValuativeExtension (v.adicCompletion K) (w.adicCompletion L) where
  vle_iff_vle a b := by
    have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 :=
      (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
    rw [Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰)),
      Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)),
      valued_algebraMap_completion, valued_algebraMap_completion]
    exact pow_le_pow_iff_left₀ zero_le zero_le he

theorem mem_integer_of_isIntegral {x : w.adicCompletion L}
    (hx : IsIntegral 𝒪[v.adicCompletion K] x) : x ∈ 𝒪[w.adicCompletion L] := by
  let f : 𝒪[v.adicCompletion K] →+* 𝒪[w.adicCompletion L] :=
    RingHom.codRestrict ((algebraMap (v.adicCompletion K) (w.adicCompletion L)).comp
      (Subring.subtype _)) _ fun a ↦ (mem_valuationInteger_iff w _).2 <| by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, RingHom.comp_apply,
          Subring.coe_subtype, valued_algebraMap_completion]
        exact pow_le_one' ((mem_valuationInteger_iff v a.1).1 a.2) _
  obtain ⟨p, hp, hpx⟩ := hx
  have h : IsIntegral 𝒪[w.adicCompletion L] x := ⟨p.map f, hp.map f, by
    rw [Polynomial.eval₂_map]
    exact hpx⟩
  exact (Valuation.integer.integers (valuation (w.adicCompletion L))).mem_of_integral h

theorem isIntegral_algebraMap_ringOfIntegers (r : 𝓞 L) :
    IsIntegral 𝒪[v.adicCompletion K]
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) := by
  obtain ⟨p, hp, hroot⟩ := RingOfIntegers.isIntegral_coe r
  refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map, show (algebraMap 𝒪[v.adicCompletion K] (w.adicCompletion L)).comp
      (Int.castRingHom _) = (algebraMap L (w.adicCompletion L)).comp (algebraMap ℤ L) from
      RingHom.ext_int _ _, ← Polynomial.hom_eval₂]
  exact (congrArg (algebraMap L (w.adicCompletion L)) hroot).trans (map_zero _)

theorem continuousSMul_integer :
    ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) := by
  refine continuousSMul_of_algebraMap _ _ ?_
  rw [IsScalarTower.algebraMap_eq 𝒪[v.adicCompletion K] (v.adicCompletion K)]
  exact (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)).comp
    continuous_subtype_val

theorem isClosed_integralClosure :
    IsClosed ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) := by
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  have : ContinuousSMul 𝒪[v.adicCompletion K] (w.adicCompletion L) :=
    continuousSMul_integer v w
  have hfin : Module.Finite 𝒪[v.adicCompletion K]
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)) :=
    IsIntegralClosure.finite 𝒪[v.adicCompletion K] (v.adicCompletion K) (w.adicCompletion L) _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' 𝒪[v.adicCompletion K]
    (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L))
  let g := (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L)).val.toLinearMap ∘ₗ f
  have hg : Continuous g := LinearMap.continuous_on_pi g
  have : ((integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) :
      Set (w.adicCompletion L))) = Set.range g := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := hf ⟨y, hy⟩
      exact ⟨c, by simp [g, hc]⟩
    · rintro ⟨c, rfl⟩
      exact (f c).2
  rw [this]
  exact (isCompact_range hg).isClosed

theorem isIntegral_of_mem_integer {x : w.adicCompletion L} (hx : x ∈ 𝒪[w.adicCompletion L]) :
    IsIntegral 𝒪[v.adicCompletion K] x := by
  have hx' : x ∈ w.adicCompletionIntegers L := (mem_valuationInteger_iff w x).1 hx
  have hsub : (Set.range fun r : 𝓞 L ↦
      algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L r)) ⊆
      (integralClosure 𝒪[v.adicCompletion K] (w.adicCompletion L) : Set (w.adicCompletion L)) := by
    rintro _ ⟨r, rfl⟩
    exact isIntegral_algebraMap_ringOfIntegers v w r
  exact closure_minimal hsub (isClosed_integralClosure v w)
    (adicCompletionIntegers_subset_closure_ringOfIntegers w hx')

instance isIntegralClosure_integer :
    IsIntegralClosure 𝒪[w.adicCompletion L] 𝒪[v.adicCompletion K] (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx ↦ ⟨⟨x, mem_integer_of_isIntegral v w hx⟩, rfl⟩,
    fun ⟨y, hy⟩ ↦ hy ▸ isIntegral_of_mem_integer v w y.2⟩

end IntegralClosureBridge

end LocalFieldBridge

/-! ### Adele Approximation, Lattice, Discreteness, Compactness & Topology -/

section AdeleTopologyAndCompactness

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
  NumberField.InfinitePlace.Completion Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

section StrongApproxFinite

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_valuation_sub_le_one (S : Finset (HeightOneSpectrum R))
    (x : HeightOneSpectrum R → K) :
    ∃ k : K, (∀ v ∈ S, v.valuation K (k - x v) ≤ 1) ∧ (∀ v ∉ S, v.valuation K k ≤ 1) := by
  classical
  obtain ⟨⟨d, hdm⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x
  simp only at hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdm
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm
  have hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hd v hv
      exact ⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hr
  have hI : Ideal.span {d} ≠ (0 : Ideal R) := by simpa using hd0
  let T : Finset (HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have he : ∀ v : HeightOneSpectrum R, v.intValuation d = WithZero.exp (-(e v : ℤ)) :=
    fun v => v.intValuation_if_neg hd0
  have he0 : ∀ v, v ∉ T → e v = 0 := by
    intro v hv
    have hmem : d ∉ v.asIdeal := by
      intro h
      apply hv
      simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact Or.inr (Ideal.dvd_span_singleton.2 h)
    have h1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hmem
    rw [he, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum R => v.asIdeal) e
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then r v.1 else 0)
  have key : ∀ (v : HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v →
      v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1 := by
    intro v a ha
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, he]
    exact div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le
  refine ⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := hy v hvT
    simp only [hv, if_true] at h1
    have h2 := key v _ h1
    have h3 : algebraMap R K (y - r v) / algebraMap R K d =
        algebraMap R K y / algebraMap R K d - x v := by
      rw [map_sub, hr v hv]
      field_simp
    rwa [h3] at h2
  · apply key
    by_cases hvT : v ∈ T
    · have h1 := hy v hvT
      simpa [hv] using h1
    · simp [he0 v hvT]

theorem isOpen_integralFiniteAdeles :
    IsOpen (integralFiniteAdeles R K : Set (FiniteAdeleRing R K)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem exists_sub_mem_integralFiniteAdeles (a : FiniteAdeleRing R K) :
    ∃ k : K, a - algebraMap K (FiniteAdeleRing R K) k ∈ integralFiniteAdeles R K := by
  classical
  have hS : {v : HeightOneSpectrum R | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  have hx : ∀ v : HeightOneSpectrum R, ∃ z : K,
      a v - (z : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    intro v
    have hU : IsOpen {w : v.adicCompletion K | a v - w ∈ v.adicCompletionIntegers K} :=
      (Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage
        (continuous_const.sub continuous_id)
    obtain ⟨z, hz⟩ := (denseRange_algebraMap (K := K) v).exists_mem_open hU ⟨a v, by simp⟩
    exact ⟨z, hz⟩
  choose x hx using hx
  obtain ⟨k, hkS, hkn⟩ := exists_valuation_sub_le_one hS.toFinset x
  refine ⟨k, fun v => ?_⟩
  change a v - (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  by_cases hv : v ∈ hS.toFinset
  · have h1 := (coe_mem_adicCompletionIntegers_iff v (k - x v)).mpr (hkS v hv)
    have h2 : a v - (k : v.adicCompletion K) =
        (a v - (x v : v.adicCompletion K)) - ((k - x v : K) : v.adicCompletion K) := by
      have hc : ∀ z : K, (z : v.adicCompletion K) = algebraMap K (v.adicCompletion K) z :=
        fun z => by simp [algebraMap_adicCompletion]
      rw [hc, hc, hc, map_sub]
      ring
    rw [h2]
    exact Subring.sub_mem _ (hx v) h1
  · have hav : a v ∈ v.adicCompletionIntegers K := by simpa using hv
    exact Subring.sub_mem _ hav ((coe_mem_adicCompletionIntegers_iff v k).mpr (hkn v hv))

theorem range_algebraMap_sup_integralFiniteAdeles :
    (algebraMap K (FiniteAdeleRing R K)).range.toAddSubgroup ⊔
      (integralFiniteAdeles R K).toAddSubgroup = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles a
  have : a = algebraMap K (FiniteAdeleRing R K) k + (a - algebraMap K (FiniteAdeleRing R K) k) := by
    abel
  rw [this]
  exact AddSubgroup.add_mem_sup ⟨k, rfl⟩ hk

instance : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance (F : Type*) [Field F] : T2Space (NumberField.InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))

instance : T2Space (NumberField.AdeleRing R K) :=
  inferInstanceAs (T2Space (NumberField.InfiniteAdeleRing K × FiniteAdeleRing R K))

end StrongApproxFinite

section IntegersLatticeAndCompact

theorem discreteTopology_of_isOpen_of_forall_mem {G : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U)
    (hH : ∀ x ∈ H, x ∈ U → x = 0) : DiscreteTopology H := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert hU.preimage continuous_subtype_val
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have hx0 : x = 0 := by simpa using congrArg Subtype.val h
    rw [hx0]
    exact h0
  · intro h
    exact Subtype.ext (hH x hx h)

variable (K : Type*) [Field K]

open scoped Classical in
def homeomorphMixedSpace : K∞ ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K => IsReal v)
      (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
          (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))

theorem homeomorphMixedSpace_apply (x : K∞) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

theorem homeomorphMixedSpace_algebraMap (k : K) :
    homeomorphMixedSpace K (algebraMap K K∞ k) = mixedEmbedding K k := by
  rw [homeomorphMixedSpace_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]

theorem homeomorphMixedSpace_sub (x y : K∞) :
    homeomorphMixedSpace K (x - y) = homeomorphMixedSpace K x - homeomorphMixedSpace K y := by
  simp only [homeomorphMixedSpace_apply, map_sub]

theorem norm_algebraMap_apply (k : K) (w : InfinitePlace K) :
    ‖algebraMap K K∞ k w‖ = w k := by
  simp [InfiniteAdeleRing.algebraMap_apply, WithAbs.norm_toAbs_eq]
  rfl

variable [NumberField K]

theorem eq_zero_of_forall_infinitePlace_lt_one (z : 𝓞 K) (h : ∀ w : InfinitePlace K, w z < 1) :
    z = 0 := by
  by_contra hz
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (one_le_of_lt_one hz fun w' _ => h w').not_gt (h w)

def integersInfinite : AddSubgroup K∞ :=
  (algebraMap (𝓞 K) K∞).range.toAddSubgroup

open scoped Classical

def fundamentalSetInfinite : Set K∞ :=
  homeomorphMixedSpace K ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)

theorem isCompact_closure_fundamentalSetInfinite :
    IsCompact (closure (fundamentalSetInfinite K)) := by
  rw [fundamentalSetInfinite, ← Homeomorph.preimage_closure, Homeomorph.isCompact_preimage]
  exact (ZSpan.fundamentalDomain_isBounded _).isCompact_closure

theorem existsUnique_sub_mem_fundamentalSetInfinite (x : K∞) :
    ∃! z : 𝓞 K, x - algebraMap (𝓞 K) K∞ z ∈ fundamentalSetInfinite K := by
  set b := mixedEmbedding.latticeBasis K
  have hmem : ∀ z : 𝓞 K, mixedEmbedding K (z : K) ∈ Submodule.span ℤ (Set.range b) := by
    intro z
    rw [mixedEmbedding.mem_span_latticeBasis]
    exact ⟨z, rfl⟩
  have himg : ∀ z : 𝓞 K, homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) =
      homeomorphMixedSpace K x - mixedEmbedding K (z : K) := by
    intro z
    rw [homeomorphMixedSpace_sub, IsScalarTower.algebraMap_apply (𝓞 K) K K∞,
      homeomorphMixedSpace_algebraMap]
  have hinj : Function.Injective fun z : 𝓞 K => mixedEmbedding K (z : K) :=
    (mixedEmbedding K).injective.comp RingOfIntegers.coe_injective
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 K, mixedEmbedding K (z : K) =
      (ZSpan.floor b (homeomorphMixedSpace K x) : mixedEmbedding.mixedSpace K) := by
    have := (ZSpan.floor b (homeomorphMixedSpace K x)).2
    rw [mixedEmbedding.mem_span_latticeBasis] at this
    exact this
  refine ⟨z, ?_, fun z' hz' => ?_⟩
  · change homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z) ∈ ZSpan.fundamentalDomain b
    rw [himg, hz]
    exact ZSpan.fract_mem_fundamentalDomain b _
  · replace hz' : homeomorphMixedSpace K (x - algebraMap (𝓞 K) K∞ z') ∈
        ZSpan.fundamentalDomain b := hz'
    rw [himg] at hz'
    have h1 : homeomorphMixedSpace K x - mixedEmbedding K (z : K) ∈ ZSpan.fundamentalDomain b := by
      rw [hz]
      exact ZSpan.fract_mem_fundamentalDomain b _
    rw [← ZSpan.fract_eq_self] at h1 hz'
    have heq : ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) =
        ZSpan.fract b (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) := by
      rw [ZSpan.fract_eq_fract]
      have : -(homeomorphMixedSpace K x - mixedEmbedding K (z' : K)) +
          (homeomorphMixedSpace K x - mixedEmbedding K (z : K)) =
          mixedEmbedding K (z' : K) - mixedEmbedding K (z : K) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hmem z') (hmem z)
    rw [hz', h1] at heq
    exact hinj (sub_right_injective heq)

theorem exists_eq_of_forall_mem_adicCompletionIntegers (k : K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : 𝓞 K, (z : K) = k := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1 := fun v =>
    (coe_mem_adicCompletionIntegers_iff v k).mp (h v)
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv
  exact ⟨z, hz⟩

theorem algebraMap_integers_mem_integralFiniteAdeles (z : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (z : K) ∈ integralFiniteAdeles (𝓞 K) K := fun v =>
  (coe_mem_adicCompletionIntegers_iff v (z : K)).mpr (HeightOneSpectrum.valuation_le_one v z)

theorem discreteTopology_principalSubgroup :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  refine discreteTopology_of_isOpen_of_forall_mem _
    ({x : K∞ | ∀ w, ‖x w‖ < 1} ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))
    ?_ ⟨fun w => by
      show ‖(0 : K∞) w‖ < 1
      rw [show (0 : K∞) w = 0 from rfl, norm_zero]; exact one_pos,
      Subring.zero_mem _⟩ ?_
  · refine IsOpen.prod ?_ isOpen_integralFiniteAdeles
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_apply (A := fun w : InfinitePlace K => w.Completion) w).norm
        continuous_const
  · rintro _ ⟨k, rfl⟩ ⟨hinf, hf⟩
    obtain ⟨z, rfl⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K k hf
    have hz : ∀ w : InfinitePlace K, w z < 1 := fun w => by
      have := hinf w
      rwa [show (algebraMap K 𝔸[K] (z : K)).1 = algebraMap K K∞ (z : K) from rfl,
        norm_algebraMap_apply] at this
    rw [eq_zero_of_forall_infinitePlace_lt_one K z hz]
    simp

theorem isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  haveI := discreteTopology_principalSubgroup K
  AddSubgroup.isClosed_of_discrete

def fundamentalSet : Set 𝔸[K] :=
  fundamentalSetInfinite K ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))

theorem existsUnique_sub_mem_fundamentalSet (x : 𝔸[K]) :
    ∃! k : K, x - algebraMap K 𝔸[K] k ∈ fundamentalSet K := by
  obtain ⟨k₁, hk₁⟩ := exists_sub_mem_integralFiniteAdeles x.2
  obtain ⟨z, hz, -⟩ := existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)
  refine ⟨k₁ + z, ⟨?_, ?_⟩, fun k hk => ?_⟩
  · change x.1 - algebraMap K K∞ (k₁ + z) ∈ _
    rw [map_add, ← sub_sub, ← IsScalarTower.algebraMap_apply]
    exact hz
  · change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) (k₁ + z) ∈ _
    rw [map_add, ← sub_sub]
    exact Subring.sub_mem _ hk₁ (algebraMap_integers_mem_integralFiniteAdeles K z)
  · obtain ⟨hkinf, hkf⟩ := hk
    change x.1 - algebraMap K K∞ k ∈ fundamentalSetInfinite K at hkinf
    change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ integralFiniteAdeles (𝓞 K) K at hkf
    have hdiff : algebraMap K (FiniteAdeleRing (𝓞 K) K) (k - (k₁ + z)) ∈
        integralFiniteAdeles (𝓞 K) K := by
      have h2 := Subring.sub_mem _ (Subring.sub_mem _ hk₁ hkf)
        (algebraMap_integers_mem_integralFiniteAdeles K z)
      convert h2 using 1
      simp only [map_sub, map_add]
      abel
    obtain ⟨u, hu⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K _ hdiff
    have h1 : z + u = z := by
      refine (existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)).unique
        ?_ hz
      convert hkinf using 1
      have hu' : algebraMap (𝓞 K) K u = k - (k₁ + algebraMap (𝓞 K) K z) := hu
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K K∞, map_add, hu']
      simp only [map_sub, map_add]
      abel
    have hu0 : u = 0 := by simpa using h1
    rw [hu0] at hu
    have : k - (k₁ + z) = 0 := by rw [← hu]; simp
    exact sub_eq_zero.mp this

theorem exists_isCompact_forall_exists_sub_mem :
    ∃ C : Set K∞, IsCompact C ∧ ∀ x : 𝔸[K], ∃ k : K, x - algebraMap K 𝔸[K] k ∈
      C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine ⟨closure (fundamentalSetInfinite K), isCompact_closure_fundamentalSetInfinite K,
    fun x => ?_⟩
  obtain ⟨k, ⟨hinf, hf⟩, -⟩ := existsUnique_sub_mem_fundamentalSet K x
  exact ⟨k, subset_closure hinf, hf⟩

abbrev AdeleQuotient : Type _ := 𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K

instance : IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  isClosed_principalSubgroup K

instance compactSpace_adeleQuotient : CompactSpace (AdeleQuotient K) := by
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  have hD : IsCompact (C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) :
      Set 𝔸[K]) := hC.prod (isCompact_integralFiniteAdeles K)
  refine ⟨?_⟩
  convert hD.image (QuotientAddGroup.continuous_mk (N := AdeleRing.principalSubgroup (𝓞 K) K))
  refine (Set.eq_univ_of_forall fun q => ?_).symm
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := hx x
    refine ⟨x - algebraMap K 𝔸[K] k, hk, ?_⟩
    rw [QuotientAddGroup.eq]
    exact ⟨k, by simp⟩

instance t2Space_adeleQuotient : T2Space (AdeleQuotient K) := inferInstance

theorem compactSpace_and_t2Space_adeleQuotient :
    CompactSpace (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) ∧
      T2Space (𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K) :=
  ⟨compactSpace_adeleQuotient K, t2Space_adeleQuotient K⟩

instance locallyCompactSpace_adeleRing : LocallyCompactSpace 𝔸[K] :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

theorem t2Space_adeleRing : T2Space 𝔸[K] := inferInstance

instance ideleGroup_locallyCompactSpace : LocallyCompactSpace (IdeleGroup K) := inferInstance

theorem ideleGroup_t2Space : T2Space (IdeleGroup K) := inferInstance

theorem isCompact_units_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ) := by
  have h : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K)) ×ˢ
      (MulOpposite.unop ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) :=
    (isCompact_adicCompletionIntegers v).prod
      (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 (isCompact_adicCompletionIntegers v))
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext u
  simp only [SetLike.mem_coe, Submonoid.mem_units_iff, Set.mem_preimage, Set.mem_prod,
    Units.embedProduct_apply, MulOpposite.unop_op]
  exact Iff.rfl

instance locallyCompactSpace_restrictedProduct_units :
    LocallyCompactSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
        Set (v.adicCompletion K)ˣ)) :=
    ⟨fun v ↦ isOpen_units_adicCompletionIntegers K v⟩
  RestrictedProduct.locallyCompactSpace_of_group
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (B := fun v ↦ (Submonoid.ofClass (v.adicCompletionIntegers K)).units)
    (.of_forall fun v ↦ isCompact_units_adicCompletionIntegers K v)

end IntegersLatticeAndCompact

/-! ### Weak Approximation (Additive & Multiplicative Units) -/

section WeakApproximation

variable {K : Type*} [Field K] [NumberField K]

theorem adicAbv_lt_one_iff_mem (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.asIdeal := by
  rw [← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem K v x

theorem adicAbv_isNontrivial (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.HeightOneSpectrum.adicAbv K v).IsNontrivial := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
  · simpa using hx0
  · exact ((adicAbv_lt_one_iff_mem v x).2 hxv).ne

theorem not_isEquiv_adicAbv {v v' : HeightOneSpectrum (𝓞 K)} (h : v ≠ v') :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv
        (NumberField.HeightOneSpectrum.adicAbv K v') := by
  intro he
  have hle : ¬ v.asIdeal ≤ v'.asIdeal := fun hle ↦
    h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle))
  obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hle
  have h1 := (adicAbv_lt_one_iff_mem v x).2 hxv
  rw [he.lt_one_iff] at h1
  exact hxv' ((adicAbv_lt_one_iff_mem v' x).1 h1)

theorem not_isEquiv_adicAbv_infinitePlace (v : HeightOneSpectrum (𝓞 K)) (w : InfinitePlace K) :
    ¬ (NumberField.HeightOneSpectrum.adicAbv K v).IsEquiv w.1 := by
  intro he
  have h1 : NumberField.HeightOneSpectrum.adicAbv K v (2 : K) ≤ 1 := by
    simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one K v 2
  rw [he.le_one_iff] at h1
  have h2 : w.1 (2 : K) = 2 := by
    have h := w.map_natCast 2
    rw [Nat.cast_ofNat, Nat.cast_ofNat] at h
    exact h
  linarith

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))

def placeAbv : S ⊕ T → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ NumberField.HeightOneSpectrum.adicAbv K v.1) (fun w ↦ w.1.1)

theorem placeAbv_isNontrivial : ∀ i, (placeAbv S T i).IsNontrivial
  | .inl v => adicAbv_isNontrivial v.1
  | .inr w => w.1.isNontrivial

theorem placeAbv_pairwise_not_isEquiv :
    Pairwise fun i j ↦ ¬ (placeAbv S T i).IsEquiv (placeAbv S T j) := by
  rintro (⟨v, hv⟩ | ⟨w, hw⟩) (⟨v', hv'⟩ | ⟨w', hw'⟩) hij he
  · exact not_isEquiv_adicAbv (fun h ↦ hij (by subst h; rfl)) he
  · exact not_isEquiv_adicAbv_infinitePlace v w' he
  · exact not_isEquiv_adicAbv_infinitePlace v' w he.symm
  · exact hij (by
      have : w = w' := InfinitePlace.eq_iff_isEquiv.2 he
      subst this; rfl)

theorem isometry_algebraMap_adicCompletion (v : HeightOneSpectrum (𝓞 K)) :
    Isometry ((algebraMap K (v.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v)).toRingHom) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun x ↦ ?_
  rw [WithAbs.norm_eq_apply_ofAbs, ← FinitePlace.norm_embedding]
  rfl

theorem denseRange_algebraMap_prod_pi :
    DenseRange (fun x : K ↦ ((fun v : S ↦ algebraMap K (v.1.adicCompletion K) x),
      (fun w : T ↦ algebraMap K w.1.Completion x))) := by
  classical
  let φ : ∀ v : S, WithAbs (placeAbv S T (.inl v)) → v.1.adicCompletion K := fun v ↦
    (algebraMap K (v.1.adicCompletion K)).comp
      (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).toRingHom
  let ψ : ∀ w : T, WithAbs (placeAbv S T (.inr w)) → w.1.Completion := fun w y ↦
    ((show WithAbs w.1.1 from y) : w.1.Completion)
  have hφc : ∀ v, Continuous (φ v) := fun v ↦ (isometry_algebraMap_adicCompletion v.1).continuous
  have hφd : ∀ v, DenseRange (φ v) := by
    intro v
    have h := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v.1
    unfold DenseRange at h ⊢
    convert h using 1
    show Set.range (⇑(algebraMap K (v.1.adicCompletion K)) ∘
      ⇑(WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1))) = _
    exact (WithAbs.equiv (NumberField.HeightOneSpectrum.adicAbv K v.1)).surjective.range_comp _
  have hψc : ∀ w, Continuous (ψ w) := fun w ↦ InfinitePlace.Completion.continuous_coe w.1
  have hψd : ∀ w, DenseRange (ψ w) := fun w ↦ InfinitePlace.Completion.denseRange_coe w.1
  let e := Homeomorph.sumPiEquivProdPi S T (fun i ↦ WithAbs (placeAbv S T i))
  have hc : Continuous (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
      (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w))).comp e.continuous
  have hg : DenseRange (Prod.map (Pi.map φ) (Pi.map ψ) ∘ e) :=
    ((DenseRange.piMap hφd).prodMap (DenseRange.piMap hψd)).comp e.surjective.denseRange
      ((continuous_pi fun v ↦ (hφc v).comp (continuous_apply v)).prodMap
        (continuous_pi fun w ↦ (hψc w).comp (continuous_apply w)))
  have hd := AbsoluteValue.denseRange_algebraMap_pi (placeAbv_isNontrivial S T)
    (placeAbv_pairwise_not_isEquiv S T)
  convert hg.comp hd hc using 1
  funext x
  rfl

theorem denseRange_units_prod_pi :
    DenseRange (fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a))) := by
  classical
  set f := fun a : Kˣ ↦
      ((fun v : S ↦ Units.map (algebraMap K (v.1.adicCompletion K)).toMonoidHom a),
        (fun w : T ↦ Units.map (algebraMap K w.1.Completion).toMonoidHom a)) with hf
  set E : ((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ) →
      ((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion) :=
    Prod.map (Pi.map fun _ ↦ Units.val) (Pi.map fun _ ↦ Units.val) with hE
  have hEi : IsInducing E :=
    (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing).prodMap
      (IsInducing.piMap fun _ ↦ Units.isEmbedding_val₀.isInducing)
  let W : Set (((v : S) → v.1.adicCompletion K) × ((w : T) → w.1.Completion)) :=
    {z | (∀ v, z.1 v ≠ 0) ∧ ∀ w, z.2 w ≠ 0}
  have hW : IsOpen W := by
    have : W = (⋂ v, {z | z.1 v ≠ 0}) ∩ ⋂ w, {z | z.2 w ≠ 0} := by ext z; simp [W]
    rw [this]
    exact (isOpen_iInter_of_finite fun v ↦
      isOpen_ne_fun ((continuous_apply v).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun w ↦
        isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const)
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ ↦ ?_
  obtain ⟨V, hV, rfl⟩ := hEi.isOpen_iff.1 hU
  have hEu : E u ∈ W := ⟨fun v ↦ (u.1 v).ne_zero, fun w ↦ (u.2 w).ne_zero⟩
  obtain ⟨x, hxV, hxW⟩ := (denseRange_algebraMap_prod_pi S T).exists_mem_open (hV.inter hW)
    ⟨E u, hu, hEu⟩
  by_cases hx : x = 0
  · have hS : IsEmpty S := ⟨fun v ↦ hxW.1 v (by rw [hx]; exact map_zero _)⟩
    have hT : IsEmpty T := ⟨fun w ↦ hxW.2 w (by rw [hx]; exact map_zero _)⟩
    refine ⟨f 1, ?_, 1, rfl⟩
    show E (f 1) ∈ V
    convert hxV using 1
    exact Prod.ext (funext fun v ↦ isEmptyElim v) (funext fun w ↦ isEmptyElim w)
  · refine ⟨f (Units.mk0 x hx), ?_, _, rfl⟩
    exact hxV

end WeakApproximation

end AdeleTopologyAndCompactness

/-! ### Adele Base Change `L ⊗_K 𝔸[K] ≃ₜ 𝔸[L]` -/

namespace AdeleBaseChange

open IsDedekindDomain NumberField TensorProduct Module Filter Topology SemiLocal
open RHDirect.Stage13CFT_IdeleNormResidue.SemiLocal
open scoped NumberField.AdeleRing RestrictedProduct

section FiniteMap

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K) in
def below (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.under (𝓞 K)
  isPrime := Ideal.IsPrime.under (𝓞 K) w.asIdeal
  ne_bot := Ideal.under_ne_bot (𝓞 K) w.ne_bot

instance liesOver_below (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (below K w).asIdeal :=
  ⟨rfl⟩

omit [NumberField K] [NumberField L] in
theorem below_eq_iff (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K)) :
    below K w = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  constructor
  · rintro rfl; infer_instance
  · intro h; exact HeightOneSpectrum.ext h.over.symm

theorem tendsto_below : Tendsto (below K (L := L)) cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    ((Set.finite_range (Subtype.val : PlacesOver L v → HeightOneSpectrum (𝓞 L))).subset
      fun w hw ↦ ⟨⟨w, (below_eq_iff w v).1 hw⟩, rfl⟩).to_subtype

theorem completionMap_congr {v v' : HeightOneSpectrum (𝓞 K)} (h : v = v')
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v'.asIdeal]
    (a : FiniteAdeleRing (𝓞 K) K) :
    completionMap v w (a v) = completionMap v' w (a v') := by
  subst h; rfl

theorem mapsTo_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    Set.MapsTo (completionMap v w) (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  intro x hx
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [valued_completionMap]
  exact pow_le_one' hx _

variable (K L) in
def finiteAdeleMap : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 K) ↦ v.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (B₁ := fun v ↦ v.adicCompletionIntegers K) (B₂ := fun w ↦ w.adicCompletionIntegers L)
    (below K) tendsto_below (fun w ↦ completionMap (below K w) w)
    (hφ := .of_forall fun w ↦ mapsTo_completionMap (below K w) w)

@[simp]
theorem finiteAdeleMap_apply (x : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleMap K L x w = completionMap (below K w) w (x (below K w)) :=
  rfl

theorem continuous_finiteAdeleMap : Continuous (finiteAdeleMap K L) :=
  RestrictedProduct.mapAlong_continuous _ _ (below K) tendsto_below _
    (.of_forall fun w ↦ mapsTo_completionMap (below K w) w)
    fun w ↦ continuous_completionMap (below K w) w

theorem finiteAdeleMap_algebraMap (k : K) :
    finiteAdeleMap K L (algebraMap K _ k) = algebraMap L _ (algebraMap K L k) := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  exact (completionMap_algebraMap (below K w) w k).trans
    (IsScalarTower.algebraMap_apply K L (w.adicCompletion L) k)

end FiniteMap

section FiniteCoord

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem trace_mem_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {y : w.adicCompletion L}
    (hy : y ∈ w.adicCompletionIntegers L) :
    Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y ∈ v.adicCompletionIntegers K := by
  open ValuativeRel in
  have hint : IsIntegral 𝒪[v.adicCompletion K] y :=
    isIntegral_of_mem_integer v w ((mem_valuationInteger_iff w y).2 hy)
  have htr : IsIntegral 𝒪[v.adicCompletion K]
      (Algebra.trace (v.adicCompletion K) (w.adicCompletion L) y) :=
    Algebra.isIntegral_trace hint
  exact (mem_valuationInteger_iff v _).1 ((Valuation.integer.integers
    (ValuativeRel.valuation (v.adicCompletion K))).mem_of_integral htr)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

abbrev traceDual : Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

theorem trace_mul_traceDual (i j : ι) :
    Algebra.trace K L (b j * traceDual b i) = if j = i then 1 else 0 := by
  rw [mul_comm, ← Algebra.traceForm_apply]
  exact LinearMap.BilinForm.apply_dualBasis_left _ _ i j

def localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    CompletionsOver L v →ₗ[v.adicCompletion K] v.adicCompletion K :=
  ((Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i).comp
    (tensorEquiv L v).symm.toLinearEquiv.toLinearMap

omit [DecidableEq ι] in
theorem sum_localCoord (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v) :
    ∑ i, algebraMap (v.adicCompletion K) (CompletionsOver L v) (localCoord b v i z) *
      algebraMap L (CompletionsOver L v) (b i) = z := by
  have h := (Algebra.TensorProduct.basis (v.adicCompletion K) b).sum_repr
    ((tensorEquiv L v).symm z)
  have h2 := congrArg (tensorEquiv L v) h
  rw [AlgEquiv.apply_symm_apply, map_sum] at h2
  conv_rhs => rw [← h2]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.TensorProduct.basis_apply, map_smul, tensorEquiv_one_tmul, Algebra.smul_def]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem localCoord_algebraMap (v : HeightOneSpectrum (𝓞 K)) (i : ι) (l : L) :
    localCoord b v i (algebraMap L (CompletionsOver L v) l) =
      algebraMap K (v.adicCompletion K) (b.repr l i) := by
  have : (tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l) = 1 ⊗ₜ l := by
    rw [AlgEquiv.symm_apply_eq, tensorEquiv_one_tmul]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm (algebraMap L (CompletionsOver L v) l)) = _
  rw [this, Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, one_smul,
    Finsupp.mapRange_apply]

theorem localCoord_eq_sum_trace (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v) :
    localCoord b v i z = ∑ w : PlacesOver L v, Algebra.trace (v.adicCompletion K)
      (w.1.adicCompletion L) (z w * algebraMap L (w.1.adicCompletion L) (traceDual b i)) := by
  have key : (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i =
      (Algebra.trace (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).comp
        (LinearMap.mulRight (v.adicCompletion K) (1 ⊗ₜ traceDual b i)) := by
    refine (Algebra.TensorProduct.basis (v.adicCompletion K) b).ext fun j ↦ ?_
    rw [Basis.coord_apply, Basis.repr_self, LinearMap.comp_apply, LinearMap.mulRight_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      trace_one_tmul, trace_mul_traceDual, Finsupp.single_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  change (Algebra.TensorProduct.basis (v.adicCompletion K) b).coord i
    ((tensorEquiv L v).symm z) = _
  rw [key, LinearMap.comp_apply, LinearMap.mulRight_apply,
    ← Algebra.trace_eq_of_algEquiv (tensorEquiv L v), map_mul, AlgEquiv.apply_symm_apply,
    tensorEquiv_one_tmul, trace_pi]
  rfl

theorem localCoord_mem (v : HeightOneSpectrum (𝓞 K)) (i : ι) (z : CompletionsOver L v)
    (hz : ∀ w : PlacesOver L v,
      z w * algebraMap L (w.1.adicCompletion L) (traceDual b i) ∈ w.1.adicCompletionIntegers L) :
    localCoord b v i z ∈ v.adicCompletionIntegers K := by
  rw [localCoord_eq_sum_trace]
  exact sum_mem fun w _ ↦ trace_mem_adicCompletionIntegers v w.1 (hz w)

omit [Fintype ι] [DecidableEq ι] in
theorem continuous_localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    Continuous (localCoord b v i) :=
  IsModuleTopology.continuous_of_linearMap (localCoord b v i)

end FiniteCoord

section FiniteTensor

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def evalAddHom (w : HeightOneSpectrum (𝓞 L)) : FiniteAdeleRing (𝓞 L) L →+ w.adicCompletion L where
  toFun y := y w
  map_zero' := rfl
  map_add' _ _ := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

theorem eventually_localCoord_mem (i : ι) (y : FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ v in cofinite, localCoord b v i (fun w ↦ y w.1) ∈ v.adicCompletionIntegers K := by
  have hfin : {w : HeightOneSpectrum (𝓞 L) |
      ¬ (y * algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)) w ∈
        w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.1 (y * algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)).2
  refine Filter.eventually_cofinite.2 ((hfin.image (below K)).subset fun v hv ↦ ?_)
  by_contra hv'
  refine hv (localCoord_mem b v i _ fun w ↦ ?_)
  by_contra hw
  exact hv' ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩

def finiteCoord (i : ι) : FiniteAdeleRing (𝓞 L) L →+ FiniteAdeleRing (𝓞 K) K where
  toFun y := ⟨fun v ↦ localCoord b v i (fun w ↦ y w.1), eventually_localCoord_mem b i y⟩
  map_zero' := FiniteAdeleRing.ext (K := K) fun v ↦ map_zero (localCoord b v i)
  map_add' y y' := FiniteAdeleRing.ext (K := K) fun v ↦
    map_add (localCoord b v i) (fun w : PlacesOver L v ↦ y w.1) (fun w : PlacesOver L v ↦ y' w.1)

theorem finiteCoord_apply (i : ι) (y : FiniteAdeleRing (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K)) :
    finiteCoord b i y v = localCoord b v i (fun w ↦ y w.1) :=
  rfl

theorem continuous_finiteCoord (i : ι) : Continuous (finiteCoord b i) := by
  refine (RestrictedProduct.continuous_dom
    (R := fun w : HeightOneSpectrum (𝓞 L) ↦ w.adicCompletion L)
    (A := fun w ↦ (w.adicCompletionIntegers L : Set (w.adicCompletion L)))).2 fun S hS ↦ ?_
  set T : Set (HeightOneSpectrum (𝓞 L)) := Sᶜ ∪ {w | algebraMap L (w.adicCompletion L)
    (traceDual b i) ∉ w.adicCompletionIntegers L} with hTdef
  have hT : T.Finite := by
    refine Set.Finite.union ?_ ?_
    · exact le_principal_iff.1 hS
    · exact Filter.eventually_cofinite.1
        (algebraMap L (FiniteAdeleRing (𝓞 L) L) (traceDual b i)).2
  have hS' : cofinite ≤ 𝓟 (below K '' T)ᶜ := by
    rw [le_principal_iff, mem_cofinite, compl_compl]
    exact hT.image _
  let g : Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]_[𝓟 S] →
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [v.adicCompletion K, v.adicCompletionIntegers K]_[𝓟 (below K '' T)ᶜ] :=
    fun y ↦ ⟨fun v ↦ localCoord b v i (fun w ↦ y w.1), by
      rw [eventually_principal]
      intro v hv
      refine localCoord_mem b v i _ fun w ↦ ?_
      have hw : w.1 ∉ T := fun hw ↦ hv ⟨w.1, hw, (below_eq_iff w.1 v).2 w.2⟩
      simp only [hTdef, Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq] at hw
      exact mul_mem (eventually_principal.1 y.2 _ hw.1) hw.2⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal_iff_forall.2 fun v ↦
    (continuous_localCoord b v i).comp
      (continuous_pi fun w ↦ RestrictedProduct.continuous_eval w.1)
  exact (RestrictedProduct.continuous_inclusion hS').comp hg

local instance : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra

local instance : IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  .of_algebraMap_eq fun _ ↦ rfl

variable (K L) in
def finiteTensorMap : L ⊗[K] FiniteAdeleRing (𝓞 K) K →ₐ[L] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    { finiteAdeleMap K L with commutes' := finiteAdeleMap_algebraMap } fun _ _ ↦ Commute.all _ _

theorem finiteTensorMap_tmul (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteTensorMap K L (l ⊗ₜ a) = algebraMap L _ l * finiteAdeleMap K L a := by
  rw [finiteTensorMap, Algebra.TensorProduct.lift_tmul]
  rfl

theorem finiteCoord_algebraMap_mul (i : ι) (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteCoord b i (algebraMap L _ l * finiteAdeleMap K L a) =
      algebraMap K _ (b.repr l i) * a := by
  refine FiniteAdeleRing.ext (K := K) fun v ↦ ?_
  rw [finiteCoord_apply]
  have : (fun w : PlacesOver L v ↦
      (algebraMap L (FiniteAdeleRing (𝓞 L) L) l * finiteAdeleMap K L a) w.1) =
      a v • algebraMap L (CompletionsOver L v) l := by
    funext w
    change algebraMap L (w.1.adicCompletion L) l *
        completionMap (below K w.1) w.1 (a (below K w.1)) =
      completionMap v w.1 (a v) * algebraMap L (w.1.adicCompletion L) l
    rw [completionMap_congr ((below_eq_iff w.1 v).2 w.2), mul_comm]
  rw [this, map_smul, localCoord_algebraMap, smul_eq_mul, mul_comm]
  rfl

theorem finiteTensorMap_sum_finiteCoord (y : FiniteAdeleRing (𝓞 L) L) :
    finiteTensorMap K L (∑ i, b i ⊗ₜ finiteCoord b i y) = y := by
  refine FiniteAdeleRing.ext (K := L) fun w ↦ ?_
  rw [map_sum]
  change evalAddHom w (∑ i, finiteTensorMap K L (b i ⊗ₜ finiteCoord b i y)) = y w
  rw [map_sum]
  have h := congrFun (sum_localCoord b (below K w) (fun w' ↦ y w'.1)) ⟨w, liesOver_below w⟩
  rw [Finset.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [finiteTensorMap_tmul]
  exact mul_comm _ _

theorem sum_finiteCoord_finiteTensorMap (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    ∑ i, b i ⊗ₜ finiteCoord b i (finiteTensorMap K L t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
    simp_rw [finiteTensorMap_tmul, finiteCoord_algebraMap_mul, ← Algebra.smul_def,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← TensorProduct.sum_tmul, b.sum_repr]
  | add s t hs ht =>
    simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hs, ht]

variable (K L) in
def finiteTensorEquiv : L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃ₐ[L] FiniteAdeleRing (𝓞 L) L :=
  AlgEquiv.ofBijective (finiteTensorMap K L)
    ⟨Function.LeftInverse.injective
      (g := fun y : FiniteAdeleRing (𝓞 L) L ↦
        ∑ i, Module.finBasis K L i ⊗ₜ finiteCoord (Module.finBasis K L) i y)
      (sum_finiteCoord_finiteTensorMap (Module.finBasis K L)),
    Function.RightInverse.surjective (finiteTensorMap_sum_finiteCoord (Module.finBasis K L))⟩

theorem finiteTensorEquiv_tmul (l : L) (a : FiniteAdeleRing (𝓞 K) K) :
    finiteTensorEquiv K L (l ⊗ₜ a) = algebraMap L _ l * finiteAdeleMap K L a :=
  finiteTensorMap_tmul l a

theorem finiteTensorEquiv_symm_apply (y : FiniteAdeleRing (𝓞 L) L) :
    (finiteTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ finiteCoord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (finiteTensorMap_sum_finiteCoord b y).symm

theorem finiteTensorEquiv_tmul_apply (l : L) (a : FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 L)) :
    finiteTensorEquiv K L (l ⊗ₜ a) w =
      tensorEquiv' L (below K w) (l ⊗ₜ a (below K w)) ⟨w, liesOver_below w⟩ := by
  rw [finiteTensorEquiv_tmul, tensorEquiv'_tmul]
  rfl

end FiniteTensor

section AdeleEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in
def adeleMap : 𝔸[K] →+* 𝔸[L] :=
  RingHom.prodMap (InfinitePlace.infiniteAdeleRingMap (K := K) (L := L)) (finiteAdeleMap K L)

theorem adeleMap_apply (x : 𝔸[K]) :
    adeleMap K L x = (InfinitePlace.infiniteAdeleRingMap x.1, finiteAdeleMap K L x.2) :=
  rfl

theorem continuous_adeleMap : Continuous (adeleMap K L) :=
  InfinitePlace.continuous_infiniteAdeleRingMap.prodMap continuous_finiteAdeleMap

theorem adeleMap_algebraMap (k : K) :
    adeleMap K L (algebraMap K 𝔸[K] k) = algebraMap L 𝔸[L] (algebraMap K L k) :=
  Prod.ext (InfinitePlace.infiniteAdeleRingMap_algebraMap k) (finiteAdeleMap_algebraMap k)

variable (K L) in
def adeleTensorEquiv : L ⊗[K] 𝔸[K] ≃ₐ[L] 𝔸[L] :=
  (Algebra.TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).trans
    (AlgEquiv.prodCongr InfinitePlace.tensorInfiniteAdeleRingEquiv (finiteTensorEquiv K L))

theorem adeleTensorEquiv_tmul (l : L) (a : 𝔸[K]) :
    adeleTensorEquiv K L (l ⊗ₜ a) = algebraMap L 𝔸[L] l * adeleMap K L a :=
  Prod.ext (InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul' l a.1) (finiteTensorEquiv_tmul l a.2)

theorem adeleTensorEquiv_tmul_snd (l : L) (a : 𝔸[K]) (w : HeightOneSpectrum (𝓞 L)) :
    (adeleTensorEquiv K L (l ⊗ₜ a)).2 w =
      SemiLocal.tensorEquiv' L (below K w) (l ⊗ₜ a.2 (below K w)) ⟨w, liesOver_below w⟩ :=
  finiteTensorEquiv_tmul_apply l a.2 w

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def coord (i : ι) (y : 𝔸[L]) : 𝔸[K] :=
  (InfinitePlace.adeleCoord b i y.1, finiteCoord b i y.2)

theorem continuous_coord (i : ι) : Continuous (coord b i) :=
  ((InfinitePlace.continuous_adeleCoord b i).comp continuous_fst).prodMk
    ((continuous_finiteCoord b i).comp continuous_snd)

def fstAddHom : 𝔸[L] →+ InfiniteAdeleRing L where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

def sndAddHom : 𝔸[L] →+ FiniteAdeleRing (𝓞 L) L where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl

theorem adeleTensorEquiv_sum_coord (y : 𝔸[L]) :
    adeleTensorEquiv K L (∑ i, b i ⊗ₜ coord b i y) = y := by
  rw [map_sum]
  simp_rw [adeleTensorEquiv_tmul]
  refine Prod.ext ?_ ?_
  · change fstAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.1
    rw [map_sum]
    conv_rhs => rw [← InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y.1]
    rw [map_sum]
    simp_rw [InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
    rfl
  · change sndAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.2
    rw [map_sum]
    conv_rhs => rw [← finiteTensorMap_sum_finiteCoord b y.2]
    rw [map_sum]
    simp_rw [finiteTensorMap_tmul]
    rfl

theorem adeleTensorEquiv_symm_apply (y : 𝔸[L]) :
    (adeleTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ coord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (adeleTensorEquiv_sum_coord b y).symm

end AdeleEquiv

section AdeleHomeomorph

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def tmulLeft (l : L) : 𝔸[K] →ₗ[𝔸[K]] L ⊗[K] 𝔸[K] where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem adeleTensorEquiv_one_tmul_mul (a : 𝔸[K]) (t : L ⊗[K] 𝔸[K]) :
    adeleTensorEquiv K L ((1 ⊗ₜ a) * t) = adeleMap K L a * adeleTensorEquiv K L t := by
  rw [map_mul, adeleTensorEquiv_tmul, map_one, one_mul]

variable (K L) in
def adeleTensorSemilinear : L ⊗[K] 𝔸[K] →ₛₗ[adeleMap K L] 𝔸[L] where
  toFun := adeleTensorEquiv K L
  map_add' := map_add _
  map_smul' c t := adeleTensorEquiv_one_tmul_mul c t

variable (K L) in
def adeleTensorHomeomorph :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃ₜ 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  haveI : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd 𝔸[K] (L ⊗[K] 𝔸[K])
  { toEquiv := (adeleTensorEquiv K L).toEquiv
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMapₛₗ continuous_adeleMap (adeleTensorSemilinear K L)
    continuous_invFun := by
      have h : ∀ y, (adeleTensorEquiv K L).symm y =
          ∑ i, tmulLeft (Module.finBasis K L i) (coord (Module.finBasis K L) i y) :=
        adeleTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (adeleTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (tmulLeft (Module.finBasis K L i))).comp
          (continuous_coord _ i) }

@[simp]
theorem adeleTensorHomeomorph_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorHomeomorph K L t = adeleTensorEquiv K L t :=
  rfl

variable (K L) in
def adeleTensorContinuousAlgEquiv :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃A[L] 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  { adeleTensorEquiv K L with
    continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
    continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }

@[simp]
theorem adeleTensorContinuousAlgEquiv_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorContinuousAlgEquiv K L t = adeleTensorEquiv K L t :=
  rfl

scoped instance algebraAdeleRing : Algebra 𝔸[K] 𝔸[L] :=
  (adeleMap K L).toAlgebra

theorem algebraMap_adeleRing : algebraMap 𝔸[K] 𝔸[L] = adeleMap K L :=
  rfl

scoped instance continuousSMul_adeleRing : ContinuousSMul 𝔸[K] 𝔸[L] :=
  continuousSMul_of_algebraMap _ _ continuous_adeleMap

variable (K L) in
def adeleTensorAlgEquivAdele : L ⊗[K] 𝔸[K] ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv (f := (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (1 ⊗ₜ a) = adeleMap K L a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]

@[simp]
theorem adeleTensorAlgEquivAdele_apply (t : L ⊗[K] 𝔸[K]) :
    adeleTensorAlgEquivAdele K L t = adeleTensorEquiv K L t :=
  rfl

variable (K L) in
def adeleTensorContinuousAlgEquivAdele :
    letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
    L ⊗[K] 𝔸[K] ≃A[𝔸[K]] 𝔸[L] :=
  letI := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  { adeleTensorAlgEquivAdele K L with
    continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
    continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }

theorem isModuleTopology_adeleRing : IsModuleTopology 𝔸[K] 𝔸[L] := by
  let := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  have : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  exact IsModuleTopology.iso
    { (adeleTensorAlgEquivAdele K L).toLinearEquiv with
      continuous_toFun := (adeleTensorHomeomorph K L).continuous_toFun
      continuous_invFun := (adeleTensorHomeomorph K L).continuous_invFun }

variable (K L) in
def normalizedTrace : L →ₗ[K] K :=
  (finrank K L : K)⁻¹ • Algebra.trace K L

theorem normalizedTrace_one : normalizedTrace K L 1 = 1 := by
  rw [normalizedTrace, LinearMap.smul_apply, ← map_one (algebraMap K L), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one, smul_eq_mul, inv_mul_cancel₀]
  exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'

variable (K L) in
def traceRetraction : L ⊗[K] 𝔸[K] →ₗ[𝔸[K]] 𝔸[K] where
  toFun t := TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) t)
  map_add' s t := by simp only [map_add]
  map_smul' c t := by
    change _ = c * _
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L)
        ((1 ⊗ₜ c) * (l ⊗ₜ a))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul, mul_smul_comm]
    | add s t hs ht => simp only [smul_add, map_add, hs, ht, mul_add]

theorem traceRetraction_one_tmul (a : 𝔸[K]) : traceRetraction K L (1 ⊗ₜ a) = a := by
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (1 ⊗ₜ a)) = a
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, normalizedTrace_one, one_smul]

variable (K L) in
def adeleRetraction (y : 𝔸[L]) : 𝔸[K] :=
  traceRetraction K L ((adeleTensorEquiv K L).symm y)

theorem adeleRetraction_adeleMap (a : 𝔸[K]) : adeleRetraction K L (adeleMap K L a) = a := by
  have : (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]
  rw [adeleRetraction, this, traceRetraction_one_tmul]

theorem continuous_adeleRetraction : Continuous (adeleRetraction K L) := by
  let := moduleTopology 𝔸[K] (L ⊗[K] 𝔸[K])
  have : IsModuleTopology 𝔸[K] (L ⊗[K] 𝔸[K]) := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap (traceRetraction K L)).comp
    (adeleTensorHomeomorph K L).symm.continuous

theorem adeleMap_injective : Function.Injective (adeleMap K L) :=
  Function.LeftInverse.injective (g := adeleRetraction K L) adeleRetraction_adeleMap

theorem isClosedEmbedding_adeleMap : IsClosedEmbedding (adeleMap K L) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 L) L) := inferInstanceAs (T2Space
    (Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]))
  haveI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : NumberField.InfinitePlace L) → w.Completion))
  haveI : T2Space 𝔸[L] := inferInstanceAs (T2Space (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
  Function.LeftInverse.isClosedEmbedding (f := adeleRetraction K L) adeleRetraction_adeleMap
    continuous_adeleRetraction continuous_adeleMap

def finiteTmulLeft (l : L) :
    FiniteAdeleRing (𝓞 K) K →ₗ[FiniteAdeleRing (𝓞 K) K] L ⊗[K] FiniteAdeleRing (𝓞 K) K where
  toFun x := l ⊗ₜ x
  map_add' x y := TensorProduct.tmul_add _ _ _
  map_smul' c x := by
    change l ⊗ₜ (c * x) = (1 ⊗ₜ c) * (l ⊗ₜ x)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (K L) in
def finiteTensorHomeomorph :
    letI := moduleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
    L ⊗[K] FiniteAdeleRing (𝓞 K) K ≃ₜ FiniteAdeleRing (𝓞 L) L :=
  letI := moduleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 K) K) (L ⊗[K] FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 K) K)
    (L ⊗[K] FiniteAdeleRing (𝓞 K) K)
  { toEquiv := (finiteTensorEquiv K L).toEquiv
    continuous_toFun := by
      let φ : L ⊗[K] FiniteAdeleRing (𝓞 K) K →ₛₗ[finiteAdeleMap K L] FiniteAdeleRing (𝓞 L) L :=
        { toFun := finiteTensorEquiv K L
          map_add' := map_add _
          map_smul' := fun c t ↦ by
            change finiteTensorEquiv K L ((1 ⊗ₜ c) * t) = finiteAdeleMap K L c * _
            rw [map_mul, finiteTensorEquiv_tmul, map_one, one_mul] }
      exact IsModuleTopology.continuous_of_linearMapₛₗ continuous_finiteAdeleMap φ
    continuous_invFun := by
      have h : ∀ y, (finiteTensorEquiv K L).symm y = ∑ i, finiteTmulLeft (Module.finBasis K L i)
          (finiteCoord (Module.finBasis K L) i y) :=
        finiteTensorEquiv_symm_apply (Module.finBasis K L)
      change Continuous fun y ↦ (finiteTensorEquiv K L).symm y
      simp_rw [h]
      exact continuous_finsetSum _ fun i _ ↦
        (IsModuleTopology.continuous_of_linearMap (finiteTmulLeft (Module.finBasis K L i))).comp
          (continuous_finiteCoord _ i) }

@[simp]
theorem finiteTensorHomeomorph_apply (t : L ⊗[K] FiniteAdeleRing (𝓞 K) K) :
    finiteTensorHomeomorph K L t = finiteTensorEquiv K L t :=
  rfl

end AdeleHomeomorph

/-! ### Adele Basis, Norms, Local Component Norms & Tower Compatibility -/

section AdeleNorms

open scoped NumberField.LiesOver

theorem norm_map_of_repr {A B A' B' ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [CommRing B'] [Algebra A' B'] [Fintype ι] [DecidableEq ι]
    (φ : A →+* A') (ψ : B →+* B') (b : Basis ι A B) (b' : Basis ι A' B')
    (h : ∀ y i, b'.repr (ψ y) i = φ (b.repr y i)) (y : B) :
    Algebra.norm A' (ψ y) = φ (Algebra.norm A y) := by
  have hb : ∀ j, ψ (b j) = b' j := fun j ↦ b'.repr.injective <| Finsupp.ext fun i ↦ by
    rw [h, b.repr_self, b'.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, h]

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in
def adeleTensorAlgEquivLeft : 𝔸[K] ⊗[K] L ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm K 𝔸[K] L).toRingEquiv.trans
      (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (Algebra.TensorProduct.comm K 𝔸[K] L (a ⊗ₜ 1)) = adeleMap K L a
    rw [Algebra.TensorProduct.comm_tmul, adeleTensorEquiv_tmul, map_one, one_mul]

theorem adeleTensorAlgEquivLeft_tmul (a : 𝔸[K]) (l : L) :
    adeleTensorAlgEquivLeft K L (a ⊗ₜ l) = algebraMap L 𝔸[L] l * adeleMap K L a := by
  change adeleTensorEquiv K L (Algebra.TensorProduct.comm K 𝔸[K] L (a ⊗ₜ l)) = _
  rw [Algebra.TensorProduct.comm_tmul, adeleTensorEquiv_tmul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def adeleBasis : Basis ι 𝔸[K] 𝔸[L] :=
  (Algebra.TensorProduct.basis 𝔸[K] b).map (adeleTensorAlgEquivLeft K L).toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem adeleBasis_apply (i : ι) : adeleBasis b i = algebraMap L 𝔸[L] (b i) := by
  rw [adeleBasis, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change adeleTensorAlgEquivLeft K L (1 ⊗ₜ b i) = _
  rw [adeleTensorAlgEquivLeft_tmul, map_one, mul_one]

theorem adeleBasis_repr (y : 𝔸[L]) (i : ι) : (adeleBasis b).repr y i = coord b i y := by
  have hy : ∑ j, coord b j y • adeleBasis b j = y := by
    conv_rhs => rw [← adeleTensorEquiv_sum_coord b y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [adeleTensorEquiv_tmul, adeleBasis_apply, Algebra.smul_def, algebraMap_adeleRing, mul_comm]
  conv_lhs => rw [← hy]
  rw [Basis.repr_sum_self]

omit [DecidableEq ι] in
theorem adeleBasis_repr_algebraMap (l : L) (i : ι) :
    (adeleBasis b).repr (algebraMap L 𝔸[L] l) i = algebraMap K 𝔸[K] (b.repr l i) := by
  classical
  have hl : algebraMap L 𝔸[L] l = ∑ j, algebraMap K 𝔸[K] (b.repr l j) • adeleBasis b j := by
    conv_lhs => rw [← b.sum_repr l]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [adeleBasis_apply, Algebra.smul_def, map_mul, Algebra.smul_def, algebraMap_adeleRing,
      adeleMap_algebraMap]
  rw [hl, Basis.repr_sum_self]

variable (K) in
scoped instance nontrivial_adeleRing : Nontrivial 𝔸[K] :=
  (AdeleRing.algebraMap_injective (𝓞 K) K).nontrivial

variable (K L) in
scoped instance : Module.Free 𝔸[K] 𝔸[L] := .of_basis (adeleBasis (Module.finBasis K L))

variable (K L) in
scoped instance : Module.Finite 𝔸[K] 𝔸[L] := .of_basis (adeleBasis (Module.finBasis K L))

variable (K L) in
theorem finrank_adeleRing : Module.finrank 𝔸[K] 𝔸[L] = Module.finrank K L := by
  rw [Module.finrank_eq_card_basis (adeleBasis (Module.finBasis K L)), Fintype.card_fin]

theorem continuous_norm_adeleRing : Continuous (Algebra.norm 𝔸[K] : 𝔸[L] → 𝔸[K]) := by
  let b := Module.finBasis K L
  have h : (Algebra.norm 𝔸[K] : 𝔸[L] → 𝔸[K]) =
      fun y ↦ (Algebra.leftMulMatrix (adeleBasis b) y).det :=
    funext fun y ↦ Algebra.norm_eq_matrix_det (adeleBasis b) y
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j ↦ ?_)
  simp_rw [Algebra.leftMulMatrix_eq_repr_mul, adeleBasis_repr]
  exact (continuous_coord b i).comp (continuous_id.mul continuous_const)

theorem norm_adeleRing_algebraMap (l : L) :
    Algebra.norm 𝔸[K] (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (Algebra.norm K l) := by
  classical
  exact norm_map_of_repr (algebraMap K 𝔸[K]) (algebraMap L 𝔸[L]) (Module.finBasis K L)
    (adeleBasis (Module.finBasis K L)) (fun y i ↦ adeleBasis_repr_algebraMap _ y i) l

theorem norm_adeleRing_adeleMap (x : 𝔸[K]) :
    Algebra.norm 𝔸[K] (adeleMap K L x) = x ^ Module.finrank K L := by
  rw [← finrank_adeleRing K L]
  exact Algebra.norm_algebraMap x

theorem adeleRetraction_algebraMap (l : L) :
    adeleRetraction K L (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (normalizedTrace K L l) := by
  have h : (adeleTensorEquiv K L).symm (algebraMap L 𝔸[L] l) = l ⊗ₜ 1 := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]
  rw [adeleRetraction, h]
  change TensorProduct.lid K 𝔸[K] (LinearMap.rTensor 𝔸[K] (normalizedTrace K L) (l ⊗ₜ 1)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.algebraMap_eq_smul_one]

variable (K) in
def finiteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (L) in
def finiteRestrict (v : HeightOneSpectrum (𝓞 K)) : 𝔸[L] →+* CompletionsOver L v where
  toFun y w := y.2 w.1
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def completionsOverBasis (v : HeightOneSpectrum (𝓞 K)) :
    Basis ι (v.adicCompletion K) (CompletionsOver L v) :=
  (Algebra.TensorProduct.basis (v.adicCompletion K) b).map (tensorEquiv L v).toLinearEquiv

omit [Fintype ι] [DecidableEq ι] in
theorem completionsOverBasis_repr (v : HeightOneSpectrum (𝓞 K)) (z : CompletionsOver L v)
    (i : ι) : (completionsOverBasis b v).repr z i = localCoord b v i z :=
  rfl

theorem finiteEval_norm (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    finiteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm (v.adicCompletion K) (finiteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (finiteEval K v) (finiteRestrict L v) (adeleBasis (Module.finBasis K L))
    (completionsOverBasis (Module.finBasis K L) v) (fun y i ↦ ?_) y).symm
  rw [completionsOverBasis_repr, adeleBasis_repr]
  rfl

theorem norm_adeleRing_snd (v : HeightOneSpectrum (𝓞 K)) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) (y.2 w.1) :=
  (finiteEval_norm v y).trans (norm_pi _)

variable (K) in
def infiniteEval (v : InfinitePlace K) : 𝔸[K] →+* v.Completion where
  toFun a := a.1 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (L) in
def infiniteRestrict (v : InfinitePlace K) :
    𝔸[L] →+* InfinitePlace.PiPlacesOver (L := L) v where
  toFun y w := y.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def piPlacesOverBasis (v : InfinitePlace K) :
    Basis ι v.Completion (InfinitePlace.PiPlacesOver (L := L) v) :=
  (Algebra.TensorProduct.basis v.Completion b).map
    (InfinitePlace.tensorPiEquiv (L := L) v).toLinearEquiv

theorem piPlacesOverBasis_repr (v : InfinitePlace K)
    (z : InfinitePlace.PiPlacesOver (L := L) v) (i : ι) :
    (piPlacesOverBasis b v).repr z i = InfinitePlace.piPlacesOverCoord b v i z :=
  rfl

theorem infiniteEval_norm (v : InfinitePlace K) (y : 𝔸[L]) :
    infiniteEval K v (Algebra.norm 𝔸[K] y) =
      Algebra.norm v.Completion (infiniteRestrict L v y) := by
  classical
  refine (norm_map_of_repr (infiniteEval K v) (infiniteRestrict L v)
    (adeleBasis (Module.finBasis K L)) (piPlacesOverBasis (Module.finBasis K L) v)
    (fun y i ↦ ?_) y).symm
  rw [piPlacesOverBasis_repr, adeleBasis_repr]
  rfl

open scoped Classical in
theorem norm_adeleRing_fst (v : InfinitePlace K) (y : 𝔸[L]) :
    (Algebra.norm 𝔸[K] y).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (y.1 w) :=
  (infiniteEval_norm v y).trans (norm_pi _)

end AdeleNorms

section Tower

open scoped NumberField.LiesOver

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem completionMap_completionMap (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (u : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (a : v.adicCompletion K) :
    completionMap w u (completionMap v w a) = completionMap v u a := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    ((continuous_completionMap w u).comp (continuous_completionMap v w))
    (continuous_completionMap v u) (funext fun k ↦ ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [completionMap_algebraMap, completionMap_algebraMap,
      IsScalarTower.algebraMap_apply K L (w.adicCompletion L), completionMap_algebraMap,
      IsScalarTower.algebraMap_apply L M (u.adicCompletion M),
      IsScalarTower.algebraMap_apply K M (u.adicCompletion M), ← IsScalarTower.algebraMap_apply K L M]

omit [NumberField K] [NumberField L] [NumberField M] in
theorem below_below (u : HeightOneSpectrum (𝓞 M)) : below K (below L u) = below K u :=
  HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) u.asIdeal)

theorem finiteAdeleMap_finiteAdeleMap (x : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleMap L M (finiteAdeleMap K L x) = finiteAdeleMap K M x := by
  refine FiniteAdeleRing.ext (K := M) fun u ↦ ?_
  have hb := below_below (K := K) (L := L) u
  have : u.asIdeal.LiesOver (below K (below L u)).asIdeal := by rw [hb]; infer_instance
  rw [finiteAdeleMap_apply, finiteAdeleMap_apply, finiteAdeleMap_apply,
    completionMap_completionMap (below K (below L u)) (below L u) u]
  exact completionMap_congr hb u x

omit [NumberField K] [NumberField L] [NumberField M] in
theorem algebraMap_completion_algebraMap (v : InfinitePlace K) (w : InfinitePlace L)
    (u : InfinitePlace M) [w.LiesOver v] [u.LiesOver w] [u.LiesOver v] (a : v.Completion) :
    algebraMap w.Completion u.Completion (algebraMap v.Completion w.Completion a) =
      algebraMap v.Completion u.Completion a := by
  have h := (InfinitePlace.Completion.denseRange_coe v).equalizer
    ((continuous_algebraMap w.Completion u.Completion).comp
      (continuous_algebraMap v.Completion w.Completion))
    (continuous_algebraMap v.Completion u.Completion) (funext fun y ↦ ?_)
  · exact congrFun h a
  · change algebraMap w.Completion u.Completion
        (algebraMap v.Completion w.Completion (algebraMap K v.Completion y.ofAbs)) =
      algebraMap v.Completion u.Completion (algebraMap K v.Completion y.ofAbs)
    rw [← IsScalarTower.algebraMap_apply K v.Completion w.Completion,
      ← IsScalarTower.algebraMap_apply K v.Completion u.Completion,
      IsScalarTower.algebraMap_apply K L w.Completion,
      ← IsScalarTower.algebraMap_apply L w.Completion u.Completion,
      IsScalarTower.algebraMap_apply L M u.Completion,
      IsScalarTower.algebraMap_apply K M u.Completion, ← IsScalarTower.algebraMap_apply K L M]

omit [NumberField K] [NumberField L] [NumberField M] [Algebra L M] [IsScalarTower K L M] in
theorem algebraMap_completion_congr {v v' : InfinitePlace K} (h : v = v') (u : InfinitePlace M)
    [u.LiesOver v] [u.LiesOver v'] (x : InfiniteAdeleRing K) :
    algebraMap v.Completion u.Completion (x v) = algebraMap v'.Completion u.Completion (x v') := by
  subst h; rfl

omit [NumberField K] [NumberField L] [NumberField M] in
theorem infiniteAdeleRingMap_infiniteAdeleRingMap (x : InfiniteAdeleRing K) :
    InfinitePlace.infiniteAdeleRingMap (K := L) (L := M)
        (InfinitePlace.infiniteAdeleRingMap (K := K) (L := L) x) =
      InfinitePlace.infiniteAdeleRingMap (K := K) (L := M) x := by
  funext u
  have hv : (u.comap (algebraMap L M)).comap (algebraMap K L) = u.comap (algebraMap K M) := by
    rw [IsScalarTower.algebraMap_eq K L M]; rfl
  have : u.LiesOver ((u.comap (algebraMap L M)).comap (algebraMap K L)) := by
    rw [hv]; infer_instance
  rw [InfinitePlace.infiniteAdeleRingMap_apply, InfinitePlace.infiniteAdeleRingMap_apply,
    InfinitePlace.infiniteAdeleRingMap_apply,
    algebraMap_completion_algebraMap _ (u.comap (algebraMap L M)) u]
  exact algebraMap_completion_congr hv u x

theorem adeleMap_adeleMap (x : 𝔸[K]) : adeleMap L M (adeleMap K L x) = adeleMap K M x :=
  Prod.ext (infiniteAdeleRingMap_infiniteAdeleRingMap x.1) (finiteAdeleMap_finiteAdeleMap x.2)

scoped instance isScalarTower_adeleRing : IsScalarTower 𝔸[K] 𝔸[L] 𝔸[M] :=
  .of_algebraMap_eq fun x ↦ (adeleMap_adeleMap x).symm

theorem norm_adeleRing_norm (y : 𝔸[M]) :
    Algebra.norm 𝔸[K] (Algebra.norm 𝔸[L] y) = Algebra.norm 𝔸[K] y :=
  Algebra.norm_norm

end Tower

/-! ### Galois Action on Adeles, Ring Equiv Transport & Place Components -/

section GaloisOnAdelesRing

section Ext

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem adeleRingHom_ext {R : Type*} [Semiring R] {f g : 𝔸[L] →+* R}
    (hL : ∀ l : L, f (algebraMap L 𝔸[L] l) = g (algebraMap L 𝔸[L] l))
    (hK : ∀ a : 𝔸[K], f (adeleMap K L a) = g (adeleMap K L a)) : f = g := by
  ext y
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv K L).surjective y
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [adeleTensorEquiv_tmul, map_mul, map_mul, hL, hK]
  | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]

theorem adeleTensorEquiv_symm_algebraMap (l : L) :
    (adeleTensorEquiv K L).symm (algebraMap L 𝔸[L] l) = l ⊗ₜ 1 := by
  rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]

theorem adeleTensorEquiv_symm_adeleMap (a : 𝔸[K]) :
    (adeleTensorEquiv K L).symm (adeleMap K L a) = 1 ⊗ₜ a := by
  rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, one_mul]

end Ext

section Transport

variable {L L' L'' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field L'']
  [NumberField L'']

def adeleRingEquiv (τ : L ≃+* L') : 𝔸[L] ≃+* 𝔸[L'] :=
  ((adeleTensorEquiv ℚ L).symm.toRingEquiv.trans
    (Algebra.TensorProduct.congr τ.toRatAlgEquiv (AlgEquiv.refl : 𝔸[ℚ] ≃ₐ[ℚ] 𝔸[ℚ])).toRingEquiv).trans
    (adeleTensorEquiv ℚ L').toRingEquiv

@[simp]
theorem adeleRingEquiv_algebraMap (τ : L ≃+* L') (l : L) :
    adeleRingEquiv τ (algebraMap L 𝔸[L] l) = algebraMap L' 𝔸[L'] (τ l) := by
  change adeleTensorEquiv ℚ L' (Algebra.TensorProduct.congr τ.toRatAlgEquiv AlgEquiv.refl
    ((adeleTensorEquiv ℚ L).symm (algebraMap L 𝔸[L] l))) = _
  rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul]
  simp

@[simp]
theorem adeleRingEquiv_adeleMap_rat (τ : L ≃+* L') (a : 𝔸[ℚ]) :
    adeleRingEquiv τ (adeleMap ℚ L a) = adeleMap ℚ L' a := by
  change adeleTensorEquiv ℚ L' (Algebra.TensorProduct.congr τ.toRatAlgEquiv AlgEquiv.refl
    ((adeleTensorEquiv ℚ L).symm (adeleMap ℚ L a))) = _
  rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul]
  simp

theorem adeleRingHom_ext_rat {R : Type*} [Semiring R] {f g : 𝔸[L] →+* R}
    (hL : ∀ l : L, f (algebraMap L 𝔸[L] l) = g (algebraMap L 𝔸[L] l))
    (hQ : ∀ a : 𝔸[ℚ], f (adeleMap ℚ L a) = g (adeleMap ℚ L a)) : f = g :=
  adeleRingHom_ext hL hQ

@[simp]
theorem adeleRingEquiv_refl : adeleRingEquiv (RingEquiv.refl L) = RingEquiv.refl 𝔸[L] := by
  apply RingEquiv.toRingHom_injective
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · exact adeleRingEquiv_algebraMap _ l
  · exact adeleRingEquiv_adeleMap_rat _ a

theorem adeleRingEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') :
    adeleRingEquiv (τ.trans τ') = (adeleRingEquiv τ).trans (adeleRingEquiv τ') := by
  apply RingEquiv.toRingHom_injective
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · change adeleRingEquiv (τ.trans τ') _ = adeleRingEquiv τ' (adeleRingEquiv τ _)
    rw [adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap, adeleRingEquiv_algebraMap]
    rfl
  · change adeleRingEquiv (τ.trans τ') _ = adeleRingEquiv τ' (adeleRingEquiv τ _)
    rw [adeleRingEquiv_adeleMap_rat, adeleRingEquiv_adeleMap_rat, adeleRingEquiv_adeleMap_rat]

theorem adeleRingEquiv_symm (τ : L ≃+* L') :
    adeleRingEquiv τ.symm = (adeleRingEquiv τ).symm := by
  ext x
  apply (adeleRingEquiv τ).injective
  rw [RingEquiv.apply_symm_apply, ← RingEquiv.trans_apply, ← adeleRingEquiv_trans,
    RingEquiv.symm_trans_self, adeleRingEquiv_refl, RingEquiv.refl_apply]

theorem continuous_adeleRingEquiv (τ : L ≃+* L') : Continuous (adeleRingEquiv τ) := by
  have : IsModuleTopology 𝔸[ℚ] 𝔸[L] := isModuleTopology_adeleRing
  let f : 𝔸[L] →ₗ[𝔸[ℚ]] 𝔸[L'] :=
    { toFun := adeleRingEquiv τ
      map_add' := map_add _
      map_smul' := fun c x ↦ by
        simp only [Algebra.smul_def, algebraMap_adeleRing, map_mul, adeleRingEquiv_adeleMap_rat,
          RingHom.id_apply] }
  exact IsModuleTopology.continuous_of_linearMap f

def adeleHomeomorph (τ : L ≃+* L') : 𝔸[L] ≃ₜ 𝔸[L'] where
  toEquiv := (adeleRingEquiv τ).toEquiv
  continuous_toFun := continuous_adeleRingEquiv τ
  continuous_invFun := by
    change Continuous (adeleRingEquiv τ).symm
    rw [← adeleRingEquiv_symm]
    exact continuous_adeleRingEquiv τ.symm

@[simp]
theorem adeleHomeomorph_apply (τ : L ≃+* L') (x : 𝔸[L]) :
    adeleHomeomorph τ x = adeleRingEquiv τ x :=
  rfl

end Transport

section Relative

variable {K L L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L']

@[simp]
theorem adeleRingEquiv_adeleMap (τ : L ≃ₐ[K] L') (a : 𝔸[K]) :
    adeleRingEquiv (τ : L ≃+* L') (adeleMap K L a) = adeleMap K L' a := by
  have h : ((adeleRingEquiv (τ : L ≃+* L')).toRingHom.comp (adeleMap K L) : 𝔸[K] →+* 𝔸[L']) =
      adeleMap K L' := by
    refine adeleRingHom_ext_rat (fun k ↦ ?_) (fun a ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adeleMap_algebraMap, adeleRingEquiv_algebraMap]
      simp
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, adeleMap_adeleMap, adeleRingEquiv_adeleMap_rat]
  exact congrArg (fun f : 𝔸[K] →+* 𝔸[L'] ↦ f a) h

variable (K) in
def adeleAlgEquiv (τ : L ≃ₐ[K] L') : 𝔸[L] ≃ₐ[𝔸[K]] 𝔸[L'] :=
  AlgEquiv.ofRingEquiv (f := adeleRingEquiv (τ : L ≃+* L')) fun a ↦ adeleRingEquiv_adeleMap τ a

@[simp]
theorem adeleAlgEquiv_apply (τ : L ≃ₐ[K] L') (x : 𝔸[L]) :
    adeleAlgEquiv K τ x = adeleRingEquiv (τ : L ≃+* L') x :=
  rfl

theorem norm_adeleRingEquiv (τ : L ≃ₐ[K] L') (x : 𝔸[L]) :
    Algebra.norm 𝔸[K] (adeleRingEquiv (τ : L ≃+* L') x) = Algebra.norm 𝔸[K] x :=
  Algebra.norm_eq_of_algEquiv (adeleAlgEquiv K τ) x

end Relative

section RingAction

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in
def adeleRingAut : (L ≃ₐ[K] L) →* RingAut 𝔸[L] where
  toFun σ := adeleRingEquiv (σ : L ≃+* L)
  map_one' := adeleRingEquiv_refl
  map_mul' σ τ := by
    rw [show ((σ * τ : L ≃ₐ[K] L) : L ≃+* L) = (τ : L ≃+* L).trans (σ : L ≃+* L) from rfl,
      adeleRingEquiv_trans]
    rfl

instance : MulSemiringAction (L ≃ₐ[K] L) 𝔸[L] :=
  MulSemiringAction.compHom _ (adeleRingAut K L)

omit [NumberField K] in
@[simp]
theorem smul_algebraMap (σ : L ≃ₐ[K] L) (l : L) :
    σ • algebraMap L 𝔸[L] l = algebraMap L 𝔸[L] (σ l) :=
  adeleRingEquiv_algebraMap _ l

@[simp]
theorem smul_adeleMap (σ : L ≃ₐ[K] L) (a : 𝔸[K]) : σ • adeleMap K L a = adeleMap K L a :=
  adeleRingEquiv_adeleMap σ a

instance : ContinuousConstSMul (L ≃ₐ[K] L) 𝔸[L] where
  continuous_const_smul σ := continuous_adeleRingEquiv (σ : L ≃+* L)

instance : ContinuousSMul (L ≃ₐ[K] L) 𝔸[L] where
  continuous_smul := continuous_prod_of_discrete_left.2 fun σ ↦ continuous_const_smul σ

@[simp]
theorem norm_smul (σ : L ≃ₐ[K] L) (y : 𝔸[L]) : Algebra.norm 𝔸[K] (σ • y) = Algebra.norm 𝔸[K] y :=
  norm_adeleRingEquiv σ y

section GaloisNormTrace

variable [IsGalois K L]

open Classical in
theorem isUnit_det_conjugates (b : Module.Basis (L ≃ₐ[K] L) K L) :
    IsUnit (Matrix.of fun σ τ : L ≃ₐ[K] L ↦ σ (b τ)).det := by
  classical
  set D := Matrix.of fun σ τ : L ≃ₐ[K] L ↦ σ (b τ)
  have hT : D.transpose * D = (Algebra.traceMatrix K b).map (algebraMap K L) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, D]
    rw [trace_eq_sum_automorphisms]
    exact Finset.sum_congr rfl fun σ _ ↦ (map_mul σ _ _).symm
  have hdet : D.det * D.det = algebraMap K L (Algebra.discr K b) := by
    rw [Algebra.discr_def, RingHom.map_det, RingHom.mapMatrix_apply, ← hT, Matrix.det_mul,
      Matrix.det_transpose]
  refine isUnit_iff_ne_zero.2 fun h ↦ Algebra.discr_not_zero_of_basis K b ?_
  rw [h, zero_mul] at hdet
  exact (FaithfulSMul.algebraMap_injective K L) (hdet.symm.trans (map_zero _).symm)

theorem adeleMap_norm (y : 𝔸[L]) :
    adeleMap K L (Algebra.norm 𝔸[K] y) = ∏ σ : L ≃ₐ[K] L, σ • y := by
  classical
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rw [Fintype.card_eq_nat_card]; exact IsGalois.card_aut_eq_finrank K L
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hcard).symm
  let B := adeleBasis b
  let M := Algebra.leftMulMatrix B y
  let D : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ τ ↦ σ (b τ)
  have hM : ∀ ρ τ, M ρ τ = B.repr (y * B τ) ρ := fun ρ τ ↦
    Algebra.leftMulMatrix_eq_repr_mul B y ρ τ
  have hy : ∀ τ, y * algebraMap L 𝔸[L] (b τ) =
      ∑ ρ, adeleMap K L (M ρ τ) * algebraMap L 𝔸[L] (b ρ) := by
    intro τ
    conv_lhs => rw [← B.sum_repr (y * algebraMap L 𝔸[L] (b τ))]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply, hM, adeleBasis_apply]
  have key : Matrix.diagonal (fun σ : L ≃ₐ[K] L ↦ σ • y) * D.map (algebraMap L 𝔸[L]) =
      D.map (algebraMap L 𝔸[L]) * M.map (adeleMap K L) := by
    ext σ τ
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    have h := congrArg (σ • ·) (hy τ)
    simp only [smul_mul', Finset.smul_sum, smul_algebraMap, smul_adeleMap] at h
    simp only [Matrix.map_apply, Matrix.of_apply, D, h]
    exact Finset.sum_congr rfl fun ρ _ ↦ mul_comm _ _
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at hdet
  rw [Algebra.norm_eq_matrix_det B]
  rw [mul_comm] at hdet
  exact (((isUnit_det_conjugates b).map (algebraMap L 𝔸[L])).mul_left_cancel hdet).symm

theorem exists_adeleMap_eq_sum_smul (y : 𝔸[L]) :
    ∃ a : 𝔸[K], adeleMap K L a = ∑ σ : L ≃ₐ[K] L, σ • y := by
  classical
  let b := Module.finBasis K L
  let B := adeleBasis b
  refine ⟨∑ i, B.repr y i * algebraMap K 𝔸[K] (Algebra.trace K L (b i)), ?_⟩
  have hy : y = ∑ i, adeleMap K L (B.repr y i) * algebraMap L 𝔸[L] (b i) := by
    conv_lhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply]
  conv_rhs => rw [hy]
  simp only [Finset.smul_sum, smul_mul', smul_adeleMap, smul_algebraMap]
  rw [Finset.sum_comm, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_sum, ← map_sum, ← trace_eq_sum_automorphisms, map_mul, adeleMap_algebraMap]

theorem forall_smul_eq_iff_mem_range (y : 𝔸[L]) :
    (∀ σ : L ≃ₐ[K] L, σ • y = y) ↔ y ∈ (adeleMap K L).range := by
  constructor
  · intro hy
    obtain ⟨a, ha⟩ := exists_adeleMap_eq_sum_smul (K := K) y
    simp only [hy, Finset.sum_const, Finset.card_univ] at ha
    set n := Fintype.card (L ≃ₐ[K] L)
    have hn : (n : K) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨algebraMap K 𝔸[K] (n : K)⁻¹ * a, ?_⟩
    rw [map_mul, ha, adeleMap_algebraMap, nsmul_eq_mul, ← mul_assoc,
      show (n : 𝔸[L]) = algebraMap L 𝔸[L] (algebraMap K L (n : K)) by simp, ← map_mul, ← map_mul,
      inv_mul_cancel₀ hn, map_one, map_one, one_mul]
  · rintro ⟨a, rfl⟩ σ
    exact smul_adeleMap σ a

end GaloisNormTrace

end RingAction

section PlacesAction

open scoped NumberField.LiesOver

variable {L L' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

theorem adeleRingEquiv_eq_adeleMap (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) :
    (adeleRingEquiv τ : 𝔸[L] →+* 𝔸[L']) = adeleMap L L' := by
  refine adeleRingHom_ext_rat (fun l ↦ ?_) (fun a ↦ ?_)
  · rw [RingHom.coe_coe, adeleRingEquiv_algebraMap, adeleMap_algebraMap, hτ]
  · rw [RingHom.coe_coe, adeleRingEquiv_adeleMap_rat, adeleMap_adeleMap]

theorem adeleRingEquiv_snd (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) (x : 𝔸[L])
    (w' : HeightOneSpectrum (𝓞 L')) :
    (adeleRingEquiv τ x).2 w' = SemiLocal.completionMap (below L w') w' (x.2 (below L w')) := by
  rw [← RingHom.coe_coe, adeleRingEquiv_eq_adeleMap τ hτ]
  rfl

theorem adeleRingEquiv_fst (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l) (x : 𝔸[L])
    (w' : InfinitePlace L') :
    (adeleRingEquiv τ x).1 w' =
      algebraMap (w'.comap (algebraMap L L')).Completion w'.Completion
        (x.1 (w'.comap (algebraMap L L'))) := by
  rw [← RingHom.coe_coe, adeleRingEquiv_eq_adeleMap τ hτ]
  rfl

theorem completionMap_below_algebraMap (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l)
    (w' : HeightOneSpectrum (𝓞 L')) (l : L) :
    SemiLocal.completionMap (below L w') w' (algebraMap L ((below L w').adicCompletion L) l) =
      algebraMap L' (w'.adicCompletion L') (τ l) := by
  rw [SemiLocal.completionMap_algebraMap, hτ, IsScalarTower.algebraMap_apply L L']

omit [NumberField L] [NumberField L'] in
theorem completion_algebraMap_comap_apply (τ : L ≃+* L') (hτ : ∀ l, τ l = algebraMap L L' l)
    (w' : InfinitePlace L') (l : L) :
    algebraMap (w'.comap (algebraMap L L')).Completion w'.Completion
        (algebraMap L (w'.comap (algebraMap L L')).Completion l) =
      algebraMap L' w'.Completion (τ l) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply L L', hτ]

variable {M M' : Type*} [Field M] [NumberField M] [Field M'] [NumberField M']

def comapPrime (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) : HeightOneSpectrum (𝓞 M) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  below M w'

omit [NumberField M] [NumberField M'] in
theorem comapPrime_asIdeal (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    (comapPrime τ w').asIdeal = w'.asIdeal.comap (RingOfIntegers.mapRingHom (τ : M →+* M')) :=
  rfl

def finiteCompletionMap (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) :
    (comapPrime τ w').adicCompletion M →+* w'.adicCompletion M' :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  SemiLocal.completionMap (below M w') w'

theorem finiteCompletionMap_algebraMap (τ : M ≃+* M') (w' : HeightOneSpectrum (𝓞 M')) (l : M) :
    finiteCompletionMap τ w' (algebraMap M _ l) = algebraMap M' (w'.adicCompletion M') (τ l) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  completionMap_below_algebraMap τ (fun _ ↦ rfl) w' l

def infiniteCompletionMap (τ : M ≃+* M') (w' : InfinitePlace M') :
    (w'.comap (τ : M →+* M')).Completion →+* w'.Completion :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  algebraMap (w'.comap (algebraMap M M')).Completion w'.Completion

omit [NumberField M] [NumberField M'] in
theorem infiniteCompletionMap_algebraMap (τ : M ≃+* M') (w' : InfinitePlace M') (l : M) :
    infiniteCompletionMap τ w' (algebraMap M _ l) = algebraMap M' w'.Completion (τ l) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  completion_algebraMap_comap_apply τ (fun _ ↦ rfl) w' l

theorem adeleRingEquiv_snd_eq (τ : M ≃+* M') (x : 𝔸[M]) (w' : HeightOneSpectrum (𝓞 M')) :
    (adeleRingEquiv τ x).2 w' = finiteCompletionMap τ w' (x.2 (comapPrime τ w')) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  adeleRingEquiv_snd τ (fun _ ↦ rfl) x w'

theorem adeleRingEquiv_fst_eq (τ : M ≃+* M') (x : 𝔸[M]) (w' : InfinitePlace M') :
    (adeleRingEquiv τ x).1 w' = infiniteCompletionMap τ w' (x.1 (w'.comap (τ : M →+* M'))) :=
  letI : Algebra M M' := (τ : M →+* M').toAlgebra
  adeleRingEquiv_fst τ (fun _ ↦ rfl) x w'

variable {K : Type*} [Field K] [NumberField K] [Algebra K M]

omit [NumberField K] [NumberField M] in
theorem comapPrime_eq_inv_smul (σ : M ≃ₐ[K] M) (w' : HeightOneSpectrum (𝓞 M)) :
    comapPrime (σ : M ≃+* M) w' = σ⁻¹ • w' := by
  ext1
  rw [comapPrime_asIdeal, smul_asIdeal, Ideal.pointwise_smul_eq_comap]
  ext y
  simp only [Ideal.mem_comap]
  constructor <;> intro h <;> convert h using 2 <;> ext <;> rfl

omit [NumberField K] [NumberField M] in
theorem comap_eq_inv_smul (σ : M ≃ₐ[K] M) (w' : InfinitePlace M) :
    w'.comap ((σ : M ≃+* M) : M →+* M) = σ⁻¹ • w' := by
  ext y
  rw [InfinitePlace.comap_apply, InfinitePlace.smul_apply]
  rfl

omit [NumberField K] in
theorem smul_snd (σ : M ≃ₐ[K] M) (x : 𝔸[M]) (w' : HeightOneSpectrum (𝓞 M)) :
    (σ • x).2 w' = finiteCompletionMap (σ : M ≃+* M) w' (x.2 (comapPrime (σ : M ≃+* M) w')) :=
  adeleRingEquiv_snd_eq _ x w'

omit [NumberField K] in
theorem smul_fst (σ : M ≃ₐ[K] M) (x : 𝔸[M]) (w' : InfinitePlace M) :
    (σ • x).1 w' = infiniteCompletionMap (σ : M ≃+* M) w' (x.1 (w'.comap ((σ : M ≃+* M) : M →+* M))) :=
  adeleRingEquiv_fst_eq _ x w'

end PlacesAction

end GaloisOnAdelesRing

end AdeleBaseChange

/-! ### Idele & Idele Class Group Field-Extension Embeddings, Norms & Galois Action -/

section IdeleExtensionAndGalois

open IsDedekindDomain NumberField Topology AdeleBaseChange SemiLocal
open RHDirect.Stage13CFT_IdeleNormResidue.SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver RestrictedProduct

section IdeleMaps

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def ideleEmbedding : IdeleGroup K →* IdeleGroup L :=
  Units.map (adeleMap K L).toMonoidHom

def ideleNorm : IdeleGroup L →* IdeleGroup K :=
  Units.map (Algebra.norm 𝔸[K] : 𝔸[L] →* 𝔸[K])

variable {K L}

@[simp]
theorem coe_ideleEmbedding (x : IdeleGroup K) :
    ((ideleEmbedding K L x : IdeleGroup L) : 𝔸[L]) = adeleMap K L x :=
  rfl

theorem ideleEmbedding_injective : Function.Injective (ideleEmbedding K L) := fun _ _ h ↦
  Units.ext (adeleMap_injective (congrArg Units.val h))

theorem continuous_ideleEmbedding : Continuous (ideleEmbedding K L) :=
  Continuous.units_map (adeleMap K L).toMonoidHom continuous_adeleMap

theorem isClosedEmbedding_ideleEmbedding : IsClosedEmbedding (ideleEmbedding K L) :=
  haveI : T2Space (FiniteAdeleRing (𝓞 L) L) := inferInstanceAs (T2Space
    (Πʳ w : HeightOneSpectrum (𝓞 L), [w.adicCompletion L, w.adicCompletionIntegers L]))
  haveI : T2Space (InfiniteAdeleRing L) :=
    inferInstanceAs (T2Space ((w : NumberField.InfinitePlace L) → w.Completion))
  haveI : T2Space 𝔸[L] := inferInstanceAs (T2Space (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L))
  haveI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs (T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  haveI : T2Space (InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace K) → v.Completion))
  haveI : T2Space 𝔸[K] := inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
  Topology.IsClosedEmbedding.units_map (f := (adeleMap K L).toMonoidHom) isClosedEmbedding_adeleMap

theorem ideleEmbedding_diagonal (k : Kˣ) :
    ideleEmbedding K L (IdeleGroup.diagonal K k) =
      IdeleGroup.diagonal L (Units.map (algebraMap K L).toMonoidHom k) :=
  Units.ext (adeleMap_algebraMap (k : K))

@[simp]
theorem coe_ideleNorm (x : IdeleGroup L) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]) = Algebra.norm 𝔸[K] (x : 𝔸[L]) :=
  rfl

theorem continuous_ideleNorm : Continuous (ideleNorm K L) :=
  Continuous.units_map _ continuous_norm_adeleRing

theorem ideleNorm_diagonal (l : Lˣ) :
    ideleNorm K L (IdeleGroup.diagonal L l) =
      IdeleGroup.diagonal K (Units.map (Algebra.norm K : L →* K) l) :=
  Units.ext (norm_adeleRing_algebraMap (l : L))

theorem ideleNorm_ideleEmbedding (x : IdeleGroup K) :
    ideleNorm K L (ideleEmbedding K L x) = x ^ Module.finrank K L :=
  Units.ext (by rw [Units.val_pow_eq_pow_val]; exact norm_adeleRing_adeleMap (x : 𝔸[K]))

theorem ideleNorm_snd (x : IdeleGroup L) (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).2 v =
      ∏ w : PlacesOver L v, Algebra.norm (v.adicCompletion K) ((x : 𝔸[L]).2 w.1) :=
  norm_adeleRing_snd (K := K) v (x : 𝔸[L])

open scoped Classical in
theorem ideleNorm_fst (x : IdeleGroup L) (v : InfinitePlace K) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]).1 v =
      ∏ w : v.placesOver L, Algebra.norm v.Completion ((x : 𝔸[L]).1 w) :=
  norm_adeleRing_fst (K := K) v (x : 𝔸[L])

theorem diagonal_range_le_comap_ideleEmbedding :
    (IdeleGroup.diagonal K).range ≤ (IdeleGroup.diagonal L).range.comap (ideleEmbedding K L) := by
  rintro _ ⟨k, rfl⟩
  exact ⟨Units.map (algebraMap K L).toMonoidHom k, (ideleEmbedding_diagonal k).symm⟩

theorem diagonal_range_le_comap_ideleNorm :
    (IdeleGroup.diagonal L).range ≤ (IdeleGroup.diagonal K).range.comap (ideleNorm K L) := by
  rintro _ ⟨l, rfl⟩
  exact ⟨Units.map (Algebra.norm K : L →* K) l, (ideleNorm_diagonal l).symm⟩

variable (K L) in
def ideleClassMap : IdeleClassGroup K →* IdeleClassGroup L :=
  QuotientGroup.map _ _ (ideleEmbedding K L) diagonal_range_le_comap_ideleEmbedding

variable (K L) in
def ideleClassNorm : IdeleClassGroup L →* IdeleClassGroup K :=
  QuotientGroup.map _ _ (ideleNorm K L) diagonal_range_le_comap_ideleNorm

@[simp]
theorem ideleClassMap_mk (x : IdeleGroup K) :
    ideleClassMap K L (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (ideleEmbedding K L x) :=
  rfl

@[simp]
theorem ideleClassNorm_mk (x : IdeleGroup L) :
    ideleClassNorm K L (IdeleClassGroup.mk L x) = IdeleClassGroup.mk K (ideleNorm K L x) :=
  rfl

theorem continuous_ideleClassMap : Continuous (ideleClassMap K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    ((IdeleClassGroup.continuous_mk L).comp continuous_ideleEmbedding)

theorem continuous_ideleClassNorm : Continuous (ideleClassNorm K L) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    ((IdeleClassGroup.continuous_mk K).comp continuous_ideleNorm)

theorem ideleClassNorm_ideleClassMap (c : IdeleClassGroup K) :
    ideleClassNorm K L (ideleClassMap K L c) = c ^ Module.finrank K L := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ideleClassNorm_mk, ideleNorm_ideleEmbedding, map_pow]

theorem mem_range_diagonal_of_ideleEmbedding {x : IdeleGroup K}
    (hx : ideleEmbedding K L x ∈ (IdeleGroup.diagonal L).range) :
    x ∈ (IdeleGroup.diagonal K).range := by
  obtain ⟨l, hl⟩ := hx
  have hxk : (x : 𝔸[K]) = algebraMap K 𝔸[K] (normalizedTrace K L (l : L)) := by
    rw [← adeleRetraction_adeleMap (L := L) (x : 𝔸[K]), ← coe_ideleEmbedding, ← hl,
      IdeleGroup.coe_diagonal, adeleRetraction_algebraMap]
  have hk : normalizedTrace K L (l : L) ≠ 0 := by
    intro h
    rw [h, map_zero] at hxk
    exact x.ne_zero hxk
  exact ⟨Units.mk0 _ hk, Units.ext hxk.symm⟩

theorem ideleClassMap_injective : Function.Injective (ideleClassMap K L) := by
  refine (injective_iff_map_eq_one _).2 fun c hc ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ← MonoidHom.mem_ker, IdeleClassGroup.ker_mk] at hc
  rw [← MonoidHom.mem_ker, IdeleClassGroup.ker_mk]
  exact mem_range_diagonal_of_ideleEmbedding hc

end IdeleMaps

section IdeleTower

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

theorem ideleEmbedding_ideleEmbedding (x : IdeleGroup K) :
    ideleEmbedding L M (ideleEmbedding K L x) = ideleEmbedding K M x :=
  Units.ext (adeleMap_adeleMap (x : 𝔸[K]))

theorem ideleNorm_ideleNorm (x : IdeleGroup M) :
    ideleNorm K L (ideleNorm L M x) = ideleNorm K M x :=
  Units.ext (norm_adeleRing_norm (K := K) (L := L) (x : 𝔸[M]))

theorem ideleClassMap_ideleClassMap (c : IdeleClassGroup K) :
    ideleClassMap L M (ideleClassMap K L c) = ideleClassMap K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ideleClassMap_mk, ideleClassMap_mk, ideleEmbedding_ideleEmbedding]

theorem ideleClassNorm_ideleClassNorm (c : IdeleClassGroup M) :
    ideleClassNorm K L (ideleClassNorm L M c) = ideleClassNorm K M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective M c
  rw [ideleClassNorm_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleNorm]

end IdeleTower

section IdeleEquivAndAction

variable {L L' L'' : Type*} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field L'']
  [NumberField L'']

def ideleEquiv (τ : L ≃+* L') : IdeleGroup L ≃ₜ* IdeleGroup L' where
  toMulEquiv := Units.mapEquiv (adeleRingEquiv τ).toMulEquiv
  continuous_toFun := Continuous.units_map (adeleRingEquiv τ).toMonoidHom (continuous_adeleRingEquiv τ)
  continuous_invFun := by
    have h := Continuous.units_map (adeleRingEquiv τ.symm).toMonoidHom
      (continuous_adeleRingEquiv τ.symm)
    rw [adeleRingEquiv_symm] at h
    exact h

@[simp]
theorem coe_ideleEquiv (τ : L ≃+* L') (x : IdeleGroup L) :
    ((ideleEquiv τ x : IdeleGroup L') : 𝔸[L']) = adeleRingEquiv τ (x : 𝔸[L]) :=
  rfl

@[simp]
theorem ideleEquiv_refl (x : IdeleGroup L) : ideleEquiv (RingEquiv.refl L) x = x :=
  Units.ext (by rw [coe_ideleEquiv, adeleRingEquiv_refl, RingEquiv.refl_apply])

theorem ideleEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') (x : IdeleGroup L) :
    ideleEquiv (τ.trans τ') x = ideleEquiv τ' (ideleEquiv τ x) :=
  Units.ext (by rw [coe_ideleEquiv, coe_ideleEquiv, coe_ideleEquiv, adeleRingEquiv_trans,
    RingEquiv.trans_apply])

@[simp]
theorem ideleEquiv_diagonal (τ : L ≃+* L') (l : Lˣ) :
    ideleEquiv τ (IdeleGroup.diagonal L l) =
      IdeleGroup.diagonal L' (Units.map (τ : L →* L') l) :=
  Units.ext (adeleRingEquiv_algebraMap τ (l : L))

theorem map_range_diagonal (τ : L ≃+* L') :
    (IdeleGroup.diagonal L).range.map (ideleEquiv τ).toMulEquiv.toMonoidHom =
      (IdeleGroup.diagonal L').range := by
  ext y
  constructor
  · rintro ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨_, (ideleEquiv_diagonal τ l).symm⟩
  · rintro ⟨l', rfl⟩
    refine ⟨IdeleGroup.diagonal L (Units.map (τ.symm : L' →* L) l'), ⟨_, rfl⟩, ?_⟩
    change ideleEquiv τ _ = _
    rw [ideleEquiv_diagonal]
    congr 1
    ext
    simp

def ideleClassEquiv (τ : L ≃+* L') : IdeleClassGroup L ≃ₜ* IdeleClassGroup L' where
  toMulEquiv := QuotientGroup.congr _ _ (ideleEquiv τ).toMulEquiv (map_range_diagonal τ)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      ((IdeleClassGroup.continuous_mk L').comp (ideleEquiv τ).continuous)
  continuous_invFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
      ((IdeleClassGroup.continuous_mk L).comp (ideleEquiv τ).symm.continuous)

@[simp]
theorem ideleClassEquiv_mk (τ : L ≃+* L') (x : IdeleGroup L) :
    ideleClassEquiv τ (IdeleClassGroup.mk L x) = IdeleClassGroup.mk L' (ideleEquiv τ x) :=
  rfl

@[simp]
theorem ideleClassEquiv_refl (c : IdeleClassGroup L) : ideleClassEquiv (RingEquiv.refl L) c = c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleEquiv_refl]

theorem ideleClassEquiv_trans (τ : L ≃+* L') (τ' : L' ≃+* L'') (c : IdeleClassGroup L) :
    ideleClassEquiv (τ.trans τ') c = ideleClassEquiv τ' (ideleClassEquiv τ c) := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleClassEquiv_mk, ideleClassEquiv_mk, ideleEquiv_trans]

section RelativeEquiv

variable {K : Type*} [Field K] [NumberField K] [Algebra K L] [Algebra K L']

@[simp]
theorem ideleEquiv_ideleEmbedding (τ : L ≃ₐ[K] L') (x : IdeleGroup K) :
    ideleEquiv (τ : L ≃+* L') (ideleEmbedding K L x) = ideleEmbedding K L' x :=
  Units.ext (adeleRingEquiv_adeleMap τ (x : 𝔸[K]))

@[simp]
theorem ideleNorm_ideleEquiv (τ : L ≃ₐ[K] L') (x : IdeleGroup L) :
    ideleNorm K L' (ideleEquiv (τ : L ≃+* L') x) = ideleNorm K L x :=
  Units.ext (norm_adeleRingEquiv τ (x : 𝔸[L]))

@[simp]
theorem ideleClassEquiv_ideleClassMap (τ : L ≃ₐ[K] L') (c : IdeleClassGroup K) :
    ideleClassEquiv (τ : L ≃+* L') (ideleClassMap K L c) = ideleClassMap K L' c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, ideleClassEquiv_mk, ideleEquiv_ideleEmbedding, ideleClassMap_mk]

@[simp]
theorem ideleClassNorm_ideleClassEquiv (τ : L ≃ₐ[K] L') (c : IdeleClassGroup L) :
    ideleClassNorm K L' (ideleClassEquiv (τ : L ≃+* L') c) = ideleClassNorm K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [ideleClassEquiv_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_ideleEquiv]

end RelativeEquiv

end IdeleEquivAndAction

section GaloisIdeleAction

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

instance : MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup L) :=
  Units.mulDistribMulActionRight

omit [NumberField K] in
@[simp]
theorem coe_smul_idele (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    ((σ • x : IdeleGroup L) : 𝔸[L]) = σ • (x : 𝔸[L]) :=
  rfl

omit [NumberField K] in
theorem smul_idele_eq_ideleEquiv (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    σ • x = ideleEquiv (σ : L ≃+* L) x :=
  Units.ext rfl

instance : ContinuousConstSMul (L ≃ₐ[K] L) (IdeleGroup L) where
  continuous_const_smul σ := by
    have h : (fun x : IdeleGroup L ↦ σ • x) = ideleEquiv (σ : L ≃+* L) :=
      funext (smul_idele_eq_ideleEquiv σ)
    rw [h]
    exact (ideleEquiv (σ : L ≃+* L)).continuous

instance : ContinuousSMul (L ≃ₐ[K] L) (IdeleGroup L) where
  continuous_smul := continuous_prod_of_discrete_left.2 fun σ ↦ continuous_const_smul σ

omit [NumberField K] in
@[simp]
theorem smul_diagonal (σ : L ≃ₐ[K] L) (l : Lˣ) :
    σ • IdeleGroup.diagonal L l = IdeleGroup.diagonal L (σ • l) :=
  Units.ext (smul_algebraMap σ (l : L))

@[simp]
theorem smul_ideleEmbedding (σ : L ≃ₐ[K] L) (x : IdeleGroup K) :
    σ • ideleEmbedding K L x = ideleEmbedding K L x :=
  Units.ext (smul_adeleMap σ (x : 𝔸[K]))

@[simp]
theorem ideleNorm_smul (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    ideleNorm K L (σ • x) = ideleNorm K L x :=
  Units.ext (norm_smul σ (x : 𝔸[L]))

section GaloisFixedIdeles

variable [IsGalois K L]

theorem ideleEmbedding_ideleNorm (x : IdeleGroup L) :
    ideleEmbedding K L (ideleNorm K L x) = ∏ σ : L ≃ₐ[K] L, σ • x :=
  Units.ext (by rw [coe_ideleEmbedding, coe_ideleNorm, adeleMap_norm, Units.coe_prod]; rfl)

theorem forall_smul_eq_iff_mem_range_ideleEmbedding (x : IdeleGroup L) :
    (∀ σ : L ≃ₐ[K] L, σ • x = x) ↔ x ∈ (ideleEmbedding K L).range := by
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (forall_smul_eq_iff_mem_range (K := K) (x : 𝔸[L])).1 fun σ ↦
      congrArg Units.val (hx σ)
    obtain ⟨a', ha'⟩ := (forall_smul_eq_iff_mem_range (K := K) ((x⁻¹ : IdeleGroup L) : 𝔸[L])).1
      fun σ ↦ congrArg Units.val (show σ • x⁻¹ = x⁻¹ by rw [smul_inv', hx σ])
    have h1 : a * a' = 1 := adeleMap_injective (K := K) (L := L) (by
      rw [map_mul, ha, ha', Units.mul_inv, map_one])
    refine ⟨⟨a, a', h1, by rw [mul_comm, h1]⟩, Units.ext ?_⟩
    exact ha
  · rintro ⟨y, rfl⟩ σ
    exact smul_ideleEmbedding σ y

theorem fixedPoints_subgroup_idele :
    FixedPoints.subgroup (L ≃ₐ[K] L) (IdeleGroup L) = (ideleEmbedding K L).range := by
  ext x
  exact forall_smul_eq_iff_mem_range_ideleEmbedding x

variable (K L) in
def ideleFixedEquiv : IdeleGroup K ≃ₜ* FixedPoints.subgroup (L ≃ₐ[K] L) (IdeleGroup L) where
  toMulEquiv := (MonoidHom.ofInjective (f := ideleEmbedding K L)
      (ideleEmbedding_injective (K := K) (L := L))).trans
    (MulEquiv.subgroupCongr fixedPoints_subgroup_idele.symm)
  continuous_toFun := continuous_ideleEmbedding.subtype_mk _
  continuous_invFun := by
    rw [(isClosedEmbedding_ideleEmbedding (K := K) (L := L)).isInducing.continuous_iff]
    convert continuous_subtype_val using 1
    funext y
    simp only [Function.comp_apply]
    exact MonoidHom.apply_ofInjective_symm _ _

end GaloisFixedIdeles

variable (K L) in
def ideleClassAut : (L ≃ₐ[K] L) →* MulAut (IdeleClassGroup L) where
  toFun σ := (ideleClassEquiv (σ : L ≃+* L)).toMulEquiv
  map_one' := MulEquiv.ext fun c ↦ ideleClassEquiv_refl c
  map_mul' σ τ := MulEquiv.ext fun c ↦ ideleClassEquiv_trans (τ : L ≃+* L) (σ : L ≃+* L) c

instance : MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L) :=
  MulDistribMulAction.compHom _ (ideleClassAut K L)

omit [NumberField K] in
@[simp]
theorem smul_mk (σ : L ≃ₐ[K] L) (x : IdeleGroup L) :
    σ • IdeleClassGroup.mk L x = IdeleClassGroup.mk L (σ • x) := by
  rw [smul_idele_eq_ideleEquiv]
  rfl

instance : ContinuousConstSMul (L ≃ₐ[K] L) (IdeleClassGroup L) where
  continuous_const_smul σ := (ideleClassEquiv (σ : L ≃+* L)).continuous

instance : ContinuousSMul (L ≃ₐ[K] L) (IdeleClassGroup L) where
  continuous_smul := continuous_prod_of_discrete_left.2 fun σ ↦ continuous_const_smul σ

@[simp]
theorem smul_ideleClassMap (σ : L ≃ₐ[K] L) (c : IdeleClassGroup K) :
    σ • ideleClassMap K L c = ideleClassMap K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [ideleClassMap_mk, smul_mk, smul_ideleEmbedding]

@[simp]
theorem ideleClassNorm_smul (σ : L ≃ₐ[K] L) (c : IdeleClassGroup L) :
    ideleClassNorm K L (σ • c) = ideleClassNorm K L c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  rw [smul_mk, ideleClassNorm_mk, ideleClassNorm_mk, ideleNorm_smul]

section GaloisIdeleClass

variable [IsGalois K L]

theorem ideleClassMap_ideleClassNorm (c : IdeleClassGroup L) :
    ideleClassMap K L (ideleClassNorm K L c) = ∏ σ : L ≃ₐ[K] L, σ • c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  simp only [ideleClassNorm_mk, ideleClassMap_mk, ideleEmbedding_ideleNorm, smul_mk, map_prod]

theorem forall_smul_eq_iff_mem_range_ideleClassMap (c : IdeleClassGroup L) :
    (∀ σ : L ≃ₐ[K] L, σ • c = c) ↔ c ∈ (ideleClassMap K L).range := by
  constructor
  · intro hc
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
    have h1 : ∀ σ : L ≃ₐ[K] L, ∃ a : Lˣ, σ • x = x * IdeleGroup.diagonal L a := by
      intro σ
      have h := hc σ
      rw [smul_mk] at h
      obtain ⟨a, ha⟩ := QuotientGroup.eq.1 h.symm
      exact ⟨a, by rw [ha, mul_inv_cancel_left]⟩
    choose a ha using h1
    have hcoc : groupCohomology.IsMulCocycle₁ a := by
      intro σ τ
      apply IdeleGroup.diagonal_injective L
      apply mul_left_cancel (a := x)
      rw [← ha, mul_smul, ha τ, smul_mul', ha σ, smul_diagonal, map_mul, mul_assoc,
        mul_comm (IdeleGroup.diagonal L (a σ))]
    obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units a hcoc
    have hfix : ∀ σ : L ≃ₐ[K] L, σ • (x * (IdeleGroup.diagonal L β)⁻¹) =
        x * (IdeleGroup.diagonal L β)⁻¹ := by
      intro σ
      rw [smul_mul', smul_inv', ha σ, smul_diagonal, ← hβ σ, map_div, div_eq_mul_inv, mul_assoc x,
        mul_inv_cancel_comm]
    obtain ⟨z, hz⟩ := (forall_smul_eq_iff_mem_range_ideleEmbedding _).1 hfix
    refine ⟨IdeleClassGroup.mk K z, ?_⟩
    rw [ideleClassMap_mk, hz, map_mul, map_inv, IdeleClassGroup.mk_diagonal, inv_one]
    exact mul_one (IdeleClassGroup.mk L x)
  · rintro ⟨d, rfl⟩ σ
    exact smul_ideleClassMap σ d

end GaloisIdeleClass

end GaloisIdeleAction

end IdeleExtensionAndGalois

end RHDirect.CFT_ProfiniteSemilocal
