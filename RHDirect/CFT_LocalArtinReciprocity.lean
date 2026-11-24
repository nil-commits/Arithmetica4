import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import RHDirect.CFT_FormalGroups
import RHDirect.CFT_AbstractLocalReciprocity
import RHDirect.CFT_LocalStructure
import RHDirect.CFT_LocalRamification
import RHDirect.CFT_LubinTateTower

/-!
# RHDirect.CFT_LocalArtinReciprocity

Complete Local Class Field Theory (`namespace RHDirect.CFT.LocalField`):
- Maximal Abelian Extension `maximalAbelianExtension`, `restrictAb`, `le_maximalAbelianExtension`
- Profinite Open Completion `openCompletion`
- Local Reciprocity Isomorphism `Kˣ ⧸ N(Lˣ) ≃* Gal(L / K)` (finite, universal, and limit)
- Local Existence Theorem (`localExistence`) & Norm Group Correspondence (`OrderIso`)
- Local Artin Map (`localArtinMap`), Uniqueness, Base Change, Transport, Functoriality, and Intrinsic Abstract Field API
- Local Kronecker–Weber Theorem (`localKroneckerWeber`)
- Explicit Local Artin Map on `ℚ_p` (`ExplicitQp`)
-/

noncomputable section


/-! ### MaximalAbelianExtension -/
section Sec_MaximalAbelianExtension

namespace RHDirect.CFT.LocalField

open _root_.IntermediateField

open scoped commutatorElement

section MaximalAbelian

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]

def commutatorClosure : ClosedSubgroup (Ω ≃ₐ[F] Ω) where
  toSubgroup := (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

instance normal_commutatorClosure : (commutatorClosure F Ω).Normal :=
  inferInstanceAs (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure.Normal

def maximalAbelianExtension : IntermediateField F Ω :=
  fixedField (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure

variable [IsGalois F Ω]

instance isGalois_maximalAbelianExtension : IsGalois F (maximalAbelianExtension F Ω) :=
  IsGalois.of_fixedField_normal_subgroup _

theorem fixingSubgroup_maximalAbelianExtension :
    (maximalAbelianExtension F Ω).fixingSubgroup = (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure :=
  InfiniteGalois.fixingSubgroup_fixedField (commutatorClosure F Ω)

noncomputable def topologicalAbelianizationEquiv :
    TopologicalAbelianization (Ω ≃ₐ[F] Ω) ≃ₜ*
      (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  have : T2Space (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
    krullTopology_t2
  let e := InfiniteGalois.normalAutEquivQuotient (commutatorClosure F Ω)
  have hc : Continuous e := by
    apply Continuous.quotient_lift
    exact InfiniteGalois.restrictNormalHom_continuous _
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

theorem topologicalAbelianizationEquiv_mk (σ : Ω ≃ₐ[F] Ω) :
    topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension F Ω) σ :=
  rfl

theorem topologicalAbelianizationEquiv_mk_apply (σ : Ω ≃ₐ[F] Ω) (x : maximalAbelianExtension F Ω) :
    ((topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) x : _) : Ω) =
      σ x := by
  rw [topologicalAbelianizationEquiv_mk, AlgEquiv.restrictNormalHom_apply]

end MaximalAbelian

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem commutator_le_ker_of_comm {G M : Type*} [Group G] [Group M] [IsMulCommutative M]
    (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

theorem le_maximalAbelianExtension (L : IntermediateField F Ω) [IsAbelianGalois F L] :
    L ≤ maximalAbelianExtension F Ω := by
  have : T2Space (L ≃ₐ[F] L) := krullTopology_t2
  rw [maximalAbelianExtension, le_iff_le, ← L.restrictNormalHom_ker]
  refine Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_comm _) ?_
  exact isClosed_singleton.preimage (InfiniteGalois.restrictNormalHom_continuous L)

variable (E : IntermediateField F Ω) [Normal F E]

theorem closure_commutator_le_ker_restrictNormalHom (h : E ≤ maximalAbelianExtension F Ω) :
    (commutator (Ω ≃ₐ[F] Ω)).topologicalClosure ≤ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E).ker := by
  rw [E.restrictNormalHom_ker, ← fixingSubgroup_maximalAbelianExtension]
  exact fixingSubgroup_le h

noncomputable def restrictAb (h : E ≤ maximalAbelianExtension F Ω) :
    (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) →* (E ≃ₐ[F] E) :=
  (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
    (closure_commutator_le_ker_restrictNormalHom E h)).comp
      (topologicalAbelianizationEquiv F Ω).symm.toMulEquiv.toMonoidHom

theorem restrictAb_topologicalAbelianizationEquiv (h : E ≤ maximalAbelianExtension F Ω) (σ : Ω ≃ₐ[F] Ω) :
    restrictAb E h (topologicalAbelianizationEquiv F Ω (σ : TopologicalAbelianization (Ω ≃ₐ[F] Ω))) =
      AlgEquiv.restrictNormalHom E σ := by
  change QuotientGroup.lift _ _ (closure_commutator_le_ker_restrictNormalHom E h)
    ((topologicalAbelianizationEquiv F Ω).symm (topologicalAbelianizationEquiv F Ω _)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

theorem restrictAb_apply (h : E ≤ maximalAbelianExtension F Ω) (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) (x : E) :
    ((restrictAb E h σ x : E) : Ω) = ((σ ⟨x, h x.2⟩ : maximalAbelianExtension F Ω) : Ω) := by
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm σ)
  have hσ : σ = topologicalAbelianizationEquiv F Ω (τ : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hτ, ContinuousMulEquiv.apply_symm_apply]
  rw [hσ, restrictAb_topologicalAbelianizationEquiv, AlgEquiv.restrictNormalHom_apply,
    topologicalAbelianizationEquiv_mk_apply]

theorem continuous_restrictAb (h : E ≤ maximalAbelianExtension F Ω) : Continuous (restrictAb E h) := by
  have h1 : Continuous (QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) E)
      (closure_commutator_le_ker_restrictNormalHom E h)) :=
    Continuous.quotient_lift (InfiniteGalois.restrictNormalHom_continuous E) _
  exact h1.comp (topologicalAbelianizationEquiv F Ω).symm.continuous

end Restrict

section Finite

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem exists_finite_abelian_mem {y : Ω} (hy : y ∈ maximalAbelianExtension F Ω) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsAbelianGalois F L ∧ y ∈ L := by
  have : FiniteDimensional F F⟮y⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  set M : IntermediateField F Ω := normalClosure F F⟮y⟯ Ω
  have : FiniteDimensional F M := normalClosure.is_finiteDimensional F F⟮y⟯ Ω
  have : IsGalois F M := IsGalois.normalClosure F F⟮y⟯ Ω
  have hyM : y ∈ M := IntermediateField.le_normalClosure F⟮y⟯ (mem_adjoin_simple_self F y)
  have hMn : M.fixingSubgroup.Normal := by
    rw [← M.restrictNormalHom_ker]; exact MonoidHom.normal_ker _
  set H : Subgroup (Ω ≃ₐ[F] Ω) := M.fixingSubgroup ⊔ commutator (Ω ≃ₐ[F] Ω)
  have : H.Normal := Subgroup.sup_normal _ _
  set A : IntermediateField F Ω := fixedField H
  have hAM : A ≤ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M]
    exact fixedField_le le_sup_left
  have : FiniteDimensional F A :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hAM).toLinearMap
      (IntermediateField.inclusion hAM).injective
  have hfix : ∀ g ∈ H, AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) A g = 1 := by
    intro g hg
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    exact (mem_fixedField_iff H (x : Ω)).1 x.2 g hg
  refine ⟨A, inferInstance, { toIsMulCommutative := ⟨⟨fun σ τ => ?_⟩⟩ }, ?_⟩
  · obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := A) (E := Ω) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := A) (E := Ω) τ
    have hc := hfix ⁅σ', τ'⁆ (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ') (Subgroup.mem_top τ')))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · rw [mem_fixedField_iff]
    intro g hg
    have hle : H ≤ MulAction.stabilizer (Ω ≃ₐ[F] Ω) y := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact (IntermediateField.mem_fixingSubgroup_iff M g).1 hg y hyM
      · exact (mem_fixedField_iff _ y).1 hy g (Subgroup.le_topologicalClosure _ hg)
    exact hle hg

theorem maximalAbelianExtension_eq_iSup :
    maximalAbelianExtension F Ω =
      ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun L => iSup_le fun _ => iSup_le fun _ =>
    le_maximalAbelianExtension L)
  obtain ⟨L, hL1, hL2, hyL⟩ := exists_finite_abelian_mem hy
  have hle : L ≤ ⨆ (L : IntermediateField F Ω) (_ : FiniteDimensional F L) (_ : IsAbelianGalois F L), L :=
    le_iSup_of_le L (le_iSup_of_le hL1 (le_iSup_of_le hL2 le_rfl))
  exact hle hyL

theorem ext_restrictAb {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      restrictAb L (le_maximalAbelianExtension L) σ = restrictAb L (le_maximalAbelianExtension L) τ) :
    σ = τ := by
  ext x
  obtain ⟨L, hL1, hL2, hxL⟩ := exists_finite_abelian_mem x.2
  have := congrArg (fun ρ : L ≃ₐ[F] L => ((ρ ⟨x, hxL⟩ : L) : Ω)) (h L)
  simpa only [restrictAb_apply] using this

end Finite

section Continuity

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_surjective (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) : Function.Surjective (restrictAb E h) := by
  intro ρ
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := E) (E := Ω) ρ
  exact ⟨_, restrictAb_topologicalAbelianizationEquiv E h τ⟩

variable (F Ω) in

def finiteAbelianExtensions : Set (IntermediateField F Ω) :=
  {L | FiniteDimensional F L ∧ IsAbelianGalois F L}

omit [IsGalois F Ω] in
theorem mem_finiteAbelianExtensions {L : IntermediateField F Ω} :
    L ∈ finiteAbelianExtensions F Ω ↔ FiniteDimensional F L ∧ IsAbelianGalois F L :=
  Iff.rfl

variable (F Ω) in

noncomputable def restrictAbPi (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω)
    (L : finiteAbelianExtensions F Ω) : (L : IntermediateField F Ω) ≃ₐ[F] (L : IntermediateField F Ω) :=
  have := L.2.2
  restrictAb (L : IntermediateField F Ω) (le_maximalAbelianExtension (L : IntermediateField F Ω)) σ

theorem continuous_restrictAbPi : Continuous (restrictAbPi F Ω) :=
  continuous_pi fun L => by
    have := L.2.2
    exact continuous_restrictAb _ _

theorem injective_restrictAbPi : Function.Injective (restrictAbPi F Ω) := by
  intro σ τ hστ
  refine ext_restrictAb fun L _ _ => ?_
  exact congrFun hστ ⟨L, inferInstance, inferInstance⟩

theorem isClosedEmbedding_restrictAbPi : Topology.IsClosedEmbedding (restrictAbPi F Ω) := by
  have : ∀ L : finiteAbelianExtensions F Ω,
      T2Space ((L : IntermediateField F Ω) ≃ₐ[F] (L : IntermediateField F Ω)) := fun L => by
    have := L.2.2
    exact krullTopology_t2
  exact continuous_restrictAbPi.isClosedEmbedding injective_restrictAbPi

theorem continuous_iff_restrictAb {X : Type*} [TopologicalSpace X]
    {f : X → maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω} :
    Continuous f ↔ ∀ (L : IntermediateField F Ω) [FiniteDimensional F L] [IsAbelianGalois F L],
      Continuous fun x => restrictAb L (le_maximalAbelianExtension L) (f x) := by
  constructor
  · intro hf L _ _
    exact (continuous_restrictAb _ _).comp hf
  · intro h
    rw [isClosedEmbedding_restrictAbPi.isInducing.continuous_iff, continuous_pi_iff]
    intro L
    have := L.2.1
    have := L.2.2
    exact h (L : IntermediateField F Ω)

end Continuity

section Commutative

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

instance isMulCommutative_maximalAbelianExtension :
    IsMulCommutative (maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) :=
  ⟨⟨fun σ τ => (topologicalAbelianizationEquiv F Ω).symm.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩

theorem isAbelianGalois_of_le_maximalAbelianExtension (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) : IsAbelianGalois F E := by
  have : IsGalois F E :=
    have := Algebra.isSeparable_tower_bot_of_isSeparable F E Ω
    IsGalois.mk
  refine { toIsMulCommutative := ⟨⟨fun σ τ => ?_⟩⟩ }
  obtain ⟨σ', rfl⟩ := restrictAb_surjective E h σ
  obtain ⟨τ', rfl⟩ := restrictAb_surjective E h τ
  rw [← map_mul, ← map_mul, mul_comm' σ' τ']

theorem isAbelianGalois_iff_le_maximalAbelianExtension (E : IntermediateField F Ω) [Normal F E] :
    IsAbelianGalois F E ↔ E ≤ maximalAbelianExtension F Ω :=
  ⟨fun _ => le_maximalAbelianExtension E, isAbelianGalois_of_le_maximalAbelianExtension E⟩

end Commutative

end RHDirect.CFT.LocalField
end Sec_MaximalAbelianExtension


/-! ### OpenCompletion -/
section Sec_OpenCompletion

namespace RHDirect.CFT.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}

variable {G} in

def quotientMapOfLE {H H' : Subgroup G} (h : H ≤ H') : G ⧸ H →* G ⧸ H' :=
  QuotientGroup.map H H' (MonoidHom.id G) h

omit [TopologicalSpace G] [IsTopologicalGroup G] in
variable {G} in
@[simp]
theorem quotientMapOfLE_mk {H H' : Subgroup G} (h : H ≤ H') (x : G) :
    quotientMapOfLE h (x : G ⧸ H) = (x : G ⧸ H') :=
  rfl

def openCompletion : Subgroup (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) where
  carrier := {a | ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H'}
  one_mem' := fun H H' h => by simp
  mul_mem' := fun ha hb H H' h => by simp [map_mul, ha H H' h, hb H H' h]
  inv_mem' := fun ha H H' h => by simp [map_inv, ha H H' h]

namespace openCompletion

variable {G}

omit [IsTopologicalGroup G] in
theorem mem_iff {a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)} :
    a ∈ openCompletion G ↔
      ∀ (H H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'), quotientMapOfLE h (a H) = a H' :=
  Iff.rfl

omit [IsTopologicalGroup G] in
theorem apply_eq (a : openCompletion G) {H H' : openFiniteIndex G} (h : (H : Subgroup G) ≤ H') :
    quotientMapOfLE h ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) =
      (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H' :=
  a.2 H H' h

omit [IsTopologicalGroup G] in

theorem ext {a b : openCompletion G}
    (h : ∀ H : openFiniteIndex G, (a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H =
      (b : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H) : a = b :=
  Subtype.ext (funext h)

variable (G) in

def of : G →* openCompletion G :=
  MonoidHom.codRestrict (MonoidHom.pi fun H : openFiniteIndex G => QuotientGroup.mk' (H : Subgroup G))
    (openCompletion G) fun _ _ _ _ => rfl

omit [IsTopologicalGroup G] in
@[simp]
theorem of_apply (x : G) (H : openFiniteIndex G) :
    ((of G x : openCompletion G) : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) H =
      (x : G ⧸ (H : Subgroup G)) :=
  rfl

theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

theorem isClosed : IsClosed (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) := by
  have hset : (openCompletion G : Set (∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G))) =
      ⋂ (H : openFiniteIndex G) (H' : openFiniteIndex G) (h : (H : Subgroup G) ≤ H'),
        {a | quotientMapOfLE h (a H) = a H'} := by
    ext a
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    rfl
  rw [hset]
  refine isClosed_iInter fun H => isClosed_iInter fun H' => isClosed_iInter fun h => ?_
  have := discreteTopology_quotient H
  have := discreteTopology_quotient H'
  exact isClosed_eq ((continuous_of_discreteTopology (f := quotientMapOfLE h)).comp (continuous_apply H))
    (continuous_apply H')

instance : IsTopologicalGroup (openCompletion G) := inferInstance

instance : CompactSpace (openCompletion G) := by
  have : ∀ H : openFiniteIndex G, CompactSpace (G ⧸ (H : Subgroup G)) := fun H => by
    have := H.2.2
    infer_instance
  exact isCompact_iff_compactSpace.1 isClosed.isCompact

instance : T2Space (openCompletion G) := by
  have : ∀ H : openFiniteIndex G, T2Space (G ⧸ (H : Subgroup G)) := fun H => by
    have := discreteTopology_quotient H
    infer_instance
  infer_instance

theorem denseRange_of : DenseRange (of G) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro a
  rw [mem_closure_iff]
  intro U hU haU
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨I, u, hu, hIV⟩ := isOpen_pi_iff.1 hV _ haU
  let H₀ : Subgroup G := ⨅ H ∈ I, (H : Subgroup G)
  have hH₀ : H₀ ∈ openFiniteIndex G := by
    refine ⟨?_, Subgroup.finiteIndex_iInf' _ fun H _ => H.2.2⟩
    have : (H₀ : Set G) = ⋂ H ∈ I, ((H : Subgroup G) : Set G) := by
      simp [H₀, Subgroup.coe_iInf]
    rw [this]
    exact isOpen_biInter_finset fun H _ => H.2.1
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
    ((a : ∀ H : openFiniteIndex G, G ⧸ (H : Subgroup G)) ⟨H₀, hH₀⟩)
  refine ⟨of G x, hIV fun H hH => ?_, x, rfl⟩
  have hle : H₀ ≤ (H : Subgroup G) := iInf₂_le H hH
  have := apply_eq a (H := ⟨H₀, hH₀⟩) (H' := H) hle
  rw [← hx, quotientMapOfLE_mk] at this
  change (x : G ⧸ (H : Subgroup G)) ∈ u H
  rw [this]
  exact (hu H hH).2

end openCompletion

end Completion

end RHDirect.CFT.LocalField
end Sec_OpenCompletion


/-! ### LocalReciprocityLimitAbstract -/
section Sec_LocalReciprocityLimitAbstract

namespace RHDirect.CFT_AbstractLocalReciprocity

section TopologicalAbelianization

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
  [TopologicalSpace H] [IsTopologicalGroup H]

theorem topologicalClosure_commutator_le_comap (f : G →* H) (hf : Continuous f) :
    (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap f := by
  refine Subgroup.topologicalClosure_minimal _ ?_
    ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_comap, map_commutatorElement]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

def topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    TopologicalAbelianization G →* TopologicalAbelianization H :=
  QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)

@[simp]
theorem topologicalAbelianizationMap_mk (f : G →* H) (hf : Continuous f) (g : G) :
    topologicalAbelianizationMap f hf (g : TopologicalAbelianization G) =
      (f g : TopologicalAbelianization H) :=
  rfl

theorem continuous_topologicalAbelianizationMap (f : G →* H) (hf : Continuous f) :
    Continuous (topologicalAbelianizationMap f hf) := by
  rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
  exact (QuotientGroup.isQuotientMap_mk _).continuous.comp hf

end TopologicalAbelianization

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem continuous_inclusion {K K' : Subgroup G} (hK : K' ≤ K) :
    Continuous (Subgroup.inclusion hK) :=
  continuous_subtype_val.subtype_mk _

def limitRestrict {K K' : OpenSubgroup G} (hK : K' ≤ K) :
    TopologicalAbelianization (K' : Subgroup G) →* TopologicalAbelianization (K : Subgroup G) :=
  topologicalAbelianizationMap (Subgroup.inclusion hK) (continuous_inclusion hK)

@[simp]
theorem limitRestrict_mk {K K' : OpenSubgroup G} (hK : K' ≤ K) (g : (K' : Subgroup G)) :
    limitRestrict hK (g : TopologicalAbelianization (K' : Subgroup G)) =
      ((⟨g, hK g.2⟩ : (K : Subgroup G)) : TopologicalAbelianization (K : Subgroup G)) :=
  rfl

def conjHom (σ : G) (K : OpenSubgroup G) :
    (K : Subgroup G) →* ((conjOpen σ K : OpenSubgroup G) : Subgroup G) where
  toFun τ := ⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩
  map_one' := Subtype.ext (by simp)
  map_mul' τ τ' := Subtype.ext (by simp [mul_assoc])

@[simp]
theorem coe_conjHom (σ : G) (K : OpenSubgroup G) (τ : (K : Subgroup G)) :
    ((conjHom σ K τ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : G) = σ * τ * σ⁻¹ :=
  rfl

theorem continuous_conjHom (σ : G) (K : OpenSubgroup G) : Continuous (conjHom σ K) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

def limitConj (σ : G) (K : OpenSubgroup G) :
    TopologicalAbelianization (K : Subgroup G) →*
      TopologicalAbelianization ((conjOpen σ K : OpenSubgroup G) : Subgroup G) :=
  topologicalAbelianizationMap (conjHom σ K) (continuous_conjHom σ K)

@[simp]
theorem limitConj_mk (σ : G) (K : OpenSubgroup G) (g : (K : Subgroup G)) :
    limitConj σ K (g : TopologicalAbelianization (K : Subgroup G)) =
      (conjHom σ K g : TopologicalAbelianization ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem limitRestrict_reciprocityLimit {K K' : OpenSubgroup G} (hK : K' ≤ K)
    (a : fixedModule A (K' : Subgroup G)) :
    limitRestrict hK (D.reciprocityLimit hax K' a) =
      D.reciprocityLimit hax K (norm A (K : Subgroup G) (K' : Subgroup G) a) := by
  refine D.eq_reciprocityLimit hax fun L hL _ => ?_
  have hmap : (commutator (K' : Subgroup G)).map (Subgroup.inclusion hK) ≤
      commutator (K : Subgroup G) := by
    rw [commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hL' : IsAbelianExtension K' (L ⊓ K') := by
    refine ⟨inf_le_right, fun x hx => ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, x.2⟩
    have h1 := hL.commutator_le (hmap ⟨x, hx, rfl⟩)
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  have := hL'.normal
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (D.reciprocityLimit hax K' a)
  have e := D.reciprocity_abelianizationRestrict_reciprocityLimit hax hL' a
  rw [← hg, abelianizationRestrict_mk] at e
  rw [← hg, limitRestrict_mk, abelianizationRestrict_mk]
  have h := D.reciprocity_galRestrict hax hL.le hL'.le hK inf_le_left
    (g : (K' : Subgroup G) ⧸ ((L ⊓ K' : OpenSubgroup G) : Subgroup G).subgroupOf K')
  rw [galRestrict_mk, e, normTateZero_mk] at h
  exact h

end ClassFieldData

end RHDirect.CFT_AbstractLocalReciprocity
end Sec_LocalReciprocityLimitAbstract


/-! ### LocalReciprocityFinite -/
section Sec_LocalReciprocityFinite

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def transportReciprocity {K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)} (hLK : L' ≤ K')
    [((L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K').Normal] {Γ M : Type*} [Group Γ] [CommGroup M]
    (e : (K' : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K' ≃* Γ)
    (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) ≃* M) (N : Subgroup M)
    (hN : (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* M) = N) :
    Abelianization Γ ≃* M ⧸ N :=
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  e.abelianizationCongr.symm.trans
    (((localClassFieldData K Ω).reciprocityAbEquiv hLK (classFieldAxiom_units K Ω)).trans
      (QuotientGroup.congr _ _ u hN))

theorem transportReciprocity_symm_mk {K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)} (hLK : L' ≤ K')
    [((L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K').Normal] {Γ M : Type*} [Group Γ] [CommGroup M]
    (e : (K' : Subgroup (Ω ≃ₐ[K] Ω)) ⧸ (L' : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf K' ≃* Γ)
    (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) ≃* M) (N : Subgroup M)
    (hN : (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (u : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* M) = N) (a : fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    (transportReciprocity hLK e u N hN).symm (u a : M ⧸ N) =
      e.abelianizationCongr (((localClassFieldData K Ω).reciprocityAbEquiv hLK
        (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω))
          (L' : Subgroup (Ω ≃ₐ[K] Ω)))) := by
  simp only [transportReciprocity, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  congr 2
  rw [QuotientGroup.congr_symm, QuotientGroup.congr_mk, MulEquiv.symm_apply_apply]

end Transport

section Base

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

noncomputable def restrictTop :
    ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →* (L ≃ₐ[K] L) :=
  (AlgEquiv.restrictNormalHom L).comp (⊤ : Subgroup (Ω ≃ₐ[K] Ω)).subtype

@[simp]
theorem restrictTop_apply (σ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    restrictTop L σ = (σ : Ω ≃ₐ[K] Ω).restrictNormal L :=
  rfl

theorem restrictTop_surjective : Function.Surjective (restrictTop L) := fun τ => by
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  exact ⟨⟨σ, Subgroup.mem_top σ⟩, hσ⟩

theorem ker_restrictTop :
    (restrictTop L).ker = (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
  ext σ
  have hc : ∀ y : L, ((((σ : Ω ≃ₐ[K] Ω).restrictNormal L) y : L) : Ω) = (σ : Ω ≃ₐ[K] Ω) y :=
    fun y => AlgEquiv.restrictNormal_commutes _ _ y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, coe_fixingOpenSubgroup,
    IntermediateField.mem_fixingSubgroup_iff, restrictTop_apply]
  constructor
  · intro h x hx
    have := congrArg (fun τ : L ≃ₐ[K] L => ((τ ⟨x, hx⟩ : L) : Ω)) h
    simp only [hc, AlgEquiv.one_apply] at this
    exact this
  · intro h
    ext x
    rw [hc, AlgEquiv.one_apply]
    exact h x x.2

instance normal_fixingOpenSubgroup_top :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal := by
  rw [← ker_restrictTop]
  exact MonoidHom.normal_ker _

noncomputable def baseQuotientEquiv :
    ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_restrictTop L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (restrictTop_surjective L))

@[simp]
theorem baseQuotientEquiv_mk (σ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    baseQuotientEquiv L (σ : _ ⧸ _) = (σ : Ω ≃ₐ[K] Ω).restrictNormal L :=
  rfl

theorem map_baseUnitsEquiv_range_norm :
    (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  haveI : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩
    change baseUnitsEquiv (RHDirect.CFT_AbstractLocalReciprocity.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]

noncomputable def localReciprocity : Abelianization (L ≃ₐ[K] L) ≃* Kˣ ⧸ (normUnits K L).range :=
  transportReciprocity (K' := ⊤) (L' := fixingOpenSubgroup L) le_top (baseQuotientEquiv L)
    baseUnitsEquiv (normUnits K L).range (map_baseUnitsEquiv_range_norm L)

theorem localReciprocity_symm_mk_baseUnitsEquiv
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    (localReciprocity L).symm (baseUnitsEquiv a : Kˣ ⧸ (normUnits K L).range) =
      (baseQuotientEquiv L).abelianizationCongr
        (((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
          (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _)) :=
  transportReciprocity_symm_mk _ _ _ _ _ a

end Base

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem inertiaDegree_top_unramifiedDegree :
    inertiaDegree (unramifiedDegree K Ω)
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
  rw [inertiaDegree]
  change ((⊤ : Subgroup (Ω ≃ₐ[K] Ω)).map (unramifiedDegree K Ω)).index = 1
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective _ unramifiedDegree_surjective,
    Subgroup.index_top]

theorem valuation_top_localClassFieldData
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).valuation ⊤ a =
      Multiplicative.ofAdd ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) := by
  have h := (localClassFieldData K Ω).valuation_pow ⊤ a
  rw [localClassFieldData_deg, inertiaDegree_top_unramifiedDegree, pow_one] at h
  rw [h]
  erw [norm_self]
  rfl

variable (K Ω) in

noncomputable def unramifiedFrobenius (L : IntermediateField K Ω) [Normal K L] : L ≃ₐ[K] L :=
  ((maximalUnramifiedExtensionFrobenius K Ω).liftNormal Ω).restrictNormal L

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

theorem localReciprocity_symm_mk_of_le_maximalUnramifiedExtension
    (hL : L ≤ maximalUnramifiedExtension K Ω) (x : Kˣ) :
    (localReciprocity L).symm (x : Kˣ ⧸ (normUnits K L).range) =
      Abelianization.of (unramifiedFrobenius K Ω L) ^ ord (x : K) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  set σ := (maximalUnramifiedExtensionFrobenius K Ω).liftNormal Ω with hσdef
  have hσ : σ.restrictNormal (maximalUnramifiedExtension K Ω) =
      maximalUnramifiedExtensionFrobenius K Ω := AlgEquiv.restrict_liftNormal _ _
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  rw [localReciprocity_symm_mk_baseUnitsEquiv]
  have hu : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⊓
      (localClassFieldData K Ω).deg.ker ≤ (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rw [localClassFieldData_deg, ker_unramifiedDegree, coe_fixingOpenSubgroup]
    exact inf_le_right.trans (IntermediateField.fixingSubgroup_antitone hL)
  have hφ : (localClassFieldData K Ω).relDeg ⊤ ⟨σ, Subgroup.mem_top σ⟩ = Multiplicative.ofAdd 1 := by
    rw [ClassFieldData.relDeg_eq_iff, localClassFieldData_deg, inertiaDegree_top_unramifiedDegree,
      pow_one]
    exact (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff σ).1 hσ
  rw [(localClassFieldData K Ω).reciprocityAbEquiv_symm_of_unramified_of_valuation le_top
    (classFieldAxiom_units K Ω) hu hφ a _ (valuation_top_localClassFieldData a), map_zpow]
  rfl

end Frobenius

section Relative

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in

theorem finiteDimensional_of_le' {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F] :
    FiniteDimensional K E :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    fun x y hxy => Subtype.ext (congrArg (fun z : F => (z : Ω)) hxy)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in

theorem fixingOpenSubgroup_anti {L F : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K F] (h : L ≤ F) : fixingOpenSubgroup F ≤ fixingOpenSubgroup L :=
  fun _ hx => IntermediateField.fixingSubgroup_antitone h hx

variable {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)]

theorem map_unitsEquivOfForall_range_norm (K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω))
    (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L') :
    (norm Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) (L' : Subgroup (Ω ≃ₐ[K] Ω))).range.map
      (unitsEquivOfForall (K' : Subgroup (Ω ≃ₐ[K] Ω)) E (mem_iff_forall_of_fixingSubgroup_eq _ hK) :
        fixedModule Ωˣ (K' : Subgroup (Ω ≃ₐ[K] Ω)) →* Eˣ) =
      (normUnits E (IntermediateField.extendScalars h)).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (unitsEquivOfForall_norm (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(unitsEquivOfForall (L' : Subgroup (Ω ≃ₐ[K] Ω)) (IntermediateField.extendScalars h)
      (mem_extendScalars_iff_forall _ h hL)).symm b, rfl⟩, ?_⟩
    change unitsEquivOfForall _ E _ (norm Ωˣ _ _ _) = _
    rw [unitsEquivOfForall_norm (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL, MulEquiv.apply_symm_apply]

noncomputable def relReciprocityOfFixingSubgroups (K' L' : OpenSubgroup (Ω ≃ₐ[K] Ω)) (hK : E.fixingSubgroup = K')
    (hL : F.fixingSubgroup = L') :
    Abelianization (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) ≃*
      Eˣ ⧸ (normUnits E (IntermediateField.extendScalars h)).range :=
  haveI := (galoisTateModel (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL).normal
  transportReciprocity (K' := K') (L' := L')
    (fun _ hx => (galoisTateModel (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL).le hx)
    (galoisTateModel (K' : Subgroup (Ω ≃ₐ[K] Ω)) L' h hK hL).quotientEquiv
    (unitsEquivOfForall (K' : Subgroup (Ω ≃ₐ[K] Ω)) E (mem_iff_forall_of_fixingSubgroup_eq _ hK))
    _ (map_unitsEquivOfForall_range_norm h K' L' hK hL)

noncomputable def relLocalReciprocity :
    Abelianization (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) ≃*
      Eˣ ⧸ (normUnits E (IntermediateField.extendScalars h)).range :=
  haveI := finiteDimensional_of_le' h
  relReciprocityOfFixingSubgroups h (fixingOpenSubgroup E) (fixingOpenSubgroup F) rfl rfl

end Relative

section NormSquare

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

noncomputable def galRestrictField (hLF : L ≤ F) :
    (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) →* (L ≃ₐ[K] L) :=
  haveI := finiteDimensional_of_le' h
  haveI := (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
    h rfl rfl).normal
  (baseQuotientEquiv L).toMonoidHom.comp
    ((galRestrict (le_top : fixingOpenSubgroup E ≤ ⊤)
      (fixingOpenSubgroup_anti hLF)).comp
      (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
        h rfl rfl).quotientEquiv.symm.toMonoidHom)

end NormSquare

section ConjSquare

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in

theorem fixingSubgroup_map_conj (σ : Ω ≃ₐ[K] Ω) (E : IntermediateField K Ω) :
    (E.map (σ : Ω →ₐ[K] Ω)).fixingSubgroup = E.fixingSubgroup.map (MulAut.conj σ).toMonoidHom := by
  ext τ
  rw [mem_map_conj, IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hτ y hy
    have := hτ (σ y) ⟨y, hy, rfl⟩
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact this
  · rintro hτ _ ⟨y, hy, rfl⟩
    have := hτ y hy
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at this
    exact this

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem fixingSubgroup_eq_conjOpen (σ : Ω ≃ₐ[K] Ω) {E E₂ : IntermediateField K Ω}
    [FiniteDimensional K E] (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) :
    E₂.fixingSubgroup = (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω)) := by
  rw [← hE, fixingSubgroup_map_conj]
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem apply_mem_of_map_eq (σ : Ω ≃ₐ[K] Ω) {E E₂ : IntermediateField K Ω}
    (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) {y : Ω} (hy : y ∈ E) : σ y ∈ E₂ := by
  rw [← hE]
  exact ⟨y, hy, rfl⟩

variable {E F : IntermediateField K Ω} (h : E ≤ F) [FiniteDimensional K F]
  [IsGalois E (IntermediateField.extendScalars h)] (σ : Ω ≃ₐ[K] Ω)
  {E₂ F₂ : IntermediateField K Ω} (h₂ : E₂ ≤ F₂) [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)]
  (hE : E.map (σ : Ω →ₐ[K] Ω) = E₂) (hF : F.map (σ : Ω →ₐ[K] Ω) = F₂)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω]
  [FiniteDimensional K F] [IsGalois E (IntermediateField.extendScalars h)] [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)] in
include hE in

noncomputable def conjUnits : Eˣ →* E₂ˣ :=
  Units.map (((σ : Ω →+* Ω).comp (algebraMap E Ω)).codRestrict E₂ fun y =>
    apply_mem_of_map_eq σ hE y.2)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω]
  [FiniteDimensional K F] [IsGalois E (IntermediateField.extendScalars h)] [FiniteDimensional K F₂]
  [IsGalois E₂ (IntermediateField.extendScalars h₂)] in
@[simp]
theorem coe_conjUnits (x : Eˣ) : (((conjUnits σ hE x : E₂ˣ) : E₂) : Ω) = σ (x : Ω) :=
  rfl

omit [IsGalois E₂ (IntermediateField.extendScalars h₂)] in
include hE hF in
theorem conj_mem_extendScalars (x : IntermediateField.extendScalars h) :
    σ (x : Ω) ∈ IntermediateField.extendScalars h₂ :=
  (IntermediateField.mem_extendScalars h₂).2
    (apply_mem_of_map_eq σ hF ((IntermediateField.mem_extendScalars h).1 x.2))

noncomputable def conjGal :
    (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) →*
      (IntermediateField.extendScalars h₂ ≃ₐ[E₂] IntermediateField.extendScalars h₂) :=
  haveI := finiteDimensional_of_le' h
  haveI := (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
    h rfl rfl).normal
  (galoisTateModel (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω))
    (conjOpen σ (fixingOpenSubgroup F)) h₂ (fixingSubgroup_eq_conjOpen σ hE)
    (fixingSubgroup_eq_conjOpen σ hF)).quotientEquiv.toMonoidHom.comp
    ((galConj σ (fixingOpenSubgroup E) (fixingOpenSubgroup F)).comp
      (galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
        h rfl rfl).quotientEquiv.symm.toMonoidHom)

theorem conjGal_apply (τ : IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h)
    (x : IntermediateField.extendScalars h) :
    ((conjGal h σ h₂ hE hF τ ⟨σ x, conj_mem_extendScalars h σ h₂ hE hF x⟩ :
      IntermediateField.extendScalars h₂) : Ω) = σ ((τ x : IntermediateField.extendScalars h) : Ω) := by
  haveI := finiteDimensional_of_le' h
  set T := galoisTateModel (fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)) (fixingOpenSubgroup F)
    h rfl rfl
  set T₂ := galoisTateModel (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω))
    (conjOpen σ (fixingOpenSubgroup F)) h₂ (fixingSubgroup_eq_conjOpen σ hE)
    (fixingSubgroup_eq_conjOpen σ hF)
  haveI := T.normal
  obtain ⟨ρ, rfl⟩ := T.surjective_hom τ
  have e : T.quotientEquiv.symm (T.hom ρ) = (ρ : _ ⧸ _) := by
    rw [MulEquiv.symm_apply_eq, TateModel.quotientEquiv_mk]
  have hρ : ∀ y : IntermediateField.extendScalars h,
      ((T.hom ρ y : IntermediateField.extendScalars h) : Ω) = (ρ : Ω ≃ₐ[K] Ω) y :=
    fun y => coe_restrictHom_apply _ h rfl ρ y
  have hρ₂ : ∀ (ρ₂ : (conjOpen σ (fixingOpenSubgroup E) : Subgroup (Ω ≃ₐ[K] Ω)))
      (y : IntermediateField.extendScalars h₂),
      ((T₂.hom ρ₂ y : IntermediateField.extendScalars h₂) : Ω) = (ρ₂ : Ω ≃ₐ[K] Ω) y :=
    fun ρ₂ y => coe_restrictHom_apply _ h₂ (fixingSubgroup_eq_conjOpen σ hE) ρ₂ y
  rw [hρ]
  change ((T₂.quotientEquiv (galConj σ (fixingOpenSubgroup E) (fixingOpenSubgroup F)
    (T.quotientEquiv.symm (T.hom ρ))) ⟨σ x, _⟩ : IntermediateField.extendScalars h₂) : Ω) = _
  rw [e, galConj_mk, TateModel.quotientEquiv_mk, hρ₂]
  simp [AlgEquiv.mul_apply]

end ConjSquare

end RHDirect.CFT.LocalField
end Sec_LocalReciprocityFinite


/-! ### LocalReciprocityUniversal -/
section Sec_LocalReciprocityUniversal

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

section Group

variable {G : Type*} [Group G] {M : Type*} [Group M] [IsMulCommutative M]

theorem commutator_le_ker_of_isMulCommutative (f : G →* M) : commutator G ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm' _ _

end Group

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Top

variable (K Ω) in

def topSubtype : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →* (Ω ≃ₐ[K] Ω) :=
  Subgroup.subtype _

theorem continuous_topSubtype : Continuous (topSubtype K Ω) :=
  continuous_subtype_val

variable (K Ω) in

def topSubtypeInv : (Ω ≃ₐ[K] Ω) →* ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) where
  toFun g := ⟨g, Subgroup.mem_top g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_topSubtypeInv : Continuous (topSubtypeInv K Ω) :=
  continuous_id.subtype_mk _

variable (K Ω) in

noncomputable def topAbelianizationEquiv :
    TopologicalAbelianization ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃*
      TopologicalAbelianization (Ω ≃ₐ[K] Ω) where
  toFun := topologicalAbelianizationMap (topSubtype K Ω) continuous_topSubtype
  invFun := topologicalAbelianizationMap (topSubtypeInv K Ω) continuous_topSubtypeInv
  left_inv y := by
    induction y using QuotientGroup.induction_on with
    | H g => rfl
  right_inv y := by
    induction y using QuotientGroup.induction_on with
    | H g => rfl
  map_mul' := map_mul _

@[simp]
theorem topAbelianizationEquiv_mk (g : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    topAbelianizationEquiv K Ω (g : TopologicalAbelianization _) =
      ((g : Ω ≃ₐ[K] Ω) : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :=
  rfl

theorem continuous_topAbelianizationEquiv : Continuous (topAbelianizationEquiv K Ω) :=
  continuous_topologicalAbelianizationMap (topSubtype K Ω) continuous_topSubtype

end Top

section Restrict

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem ker_restrictNormalHom :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker = L.fixingSubgroup := by
  ext σ
  have hc : ∀ y : L, (((σ.restrictNormal L) y : L) : Ω) = σ y :=
    fun y => AlgEquiv.restrictNormal_commutes _ _ y
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := congrArg (fun τ : L ≃ₐ[K] L => ((τ ⟨x, hx⟩ : L) : Ω)) h
    simp only [AlgEquiv.restrictNormalHom_apply, hc, AlgEquiv.one_apply] at this
    exact this
  · intro h
    ext x
    simp only [AlgEquiv.restrictNormalHom_apply, hc, AlgEquiv.one_apply]
    exact h x x.2

variable [IsMulCommutative (L ≃ₐ[K] L)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem topologicalClosure_commutator_le_ker_restrictNormalHom :
    (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure ≤
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker := by
  refine Subgroup.topologicalClosure_minimal _ (commutator_le_ker_of_isMulCommutative _) ?_
  rw [ker_restrictNormalHom]
  exact Subgroup.isClosed_of_isOpen _ (L.fixingSubgroup_isOpen)

noncomputable def abelianRestrict : TopologicalAbelianization (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) :=
  QuotientGroup.lift _ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L)
    (topologicalClosure_commutator_le_ker_restrictNormalHom L)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
@[simp]
theorem abelianRestrict_mk (σ : Ω ≃ₐ[K] Ω) :
    abelianRestrict L (σ : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = σ.restrictNormal L :=
  rfl

theorem isAbelianExtension_fixingOpenSubgroup : IsAbelianExtension ⊤ (fixingOpenSubgroup L) := by
  refine ⟨le_top, ?_⟩
  rw [← ker_restrictTop]
  exact commutator_le_ker_of_isMulCommutative _

theorem abelianRestrict_topAbelianizationEquiv
    (y : TopologicalAbelianization ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    abelianRestrict L (topAbelianizationEquiv K Ω y) =
      baseQuotientEquiv L (abelianizationRestrict (isAbelianExtension_fixingOpenSubgroup L) y) := by
  induction y using QuotientGroup.induction_on with
  | H g => rfl

end Restrict

section Universal

variable (K Ω) in

noncomputable def localReciprocityLimit : Kˣ →* TopologicalAbelianization (Ω ≃ₐ[K] Ω) :=
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  (topAbelianizationEquiv K Ω).toMonoidHom.comp
    (((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤).comp
      (baseUnitsEquiv (K := K) (Ω := Ω)).symm.toMonoidHom)

theorem localReciprocityLimit_baseUnitsEquiv
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    haveI := isDiscreteModule_units (K := K) (Ω := Ω)
    localReciprocityLimit K Ω (baseUnitsEquiv a) = topAbelianizationEquiv K Ω
      ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤ a) := by
  simp only [localReciprocityLimit, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.symm_apply_apply]

theorem of_abelianRestrict_localReciprocityLimit (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (x : Kˣ) :
    Abelianization.of (abelianRestrict L (localReciprocityLimit K Ω x)) =
      (localReciprocity L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  have hM := isAbelianExtension_fixingOpenSubgroup L
  rw [localReciprocityLimit_baseUnitsEquiv, abelianRestrict_topAbelianizationEquiv,
    (localClassFieldData K Ω).abelianizationRestrict_reciprocityLimit _ hM,
    localReciprocity_symm_mk_baseUnitsEquiv]
  set q := ((localClassFieldData K Ω).reciprocityAbelianEquiv (classFieldAxiom_units K Ω) hM).symm
    (a : tateZero Ωˣ _ _) with hq
  have e : ((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
      (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _) = Abelianization.of q := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of, hq,
      ← (localClassFieldData K Ω).reciprocityAbelianEquiv_apply (classFieldAxiom_units K Ω) hM,
      MulEquiv.apply_symm_apply]
  rw [e]
  rfl

omit [IsSepClosure K Ω] in
theorem mem_range_norm_top_iff (L : IntermediateField K Ω) [IsGalois K Ω] [FiniteDimensional K L]
    (a : fixedModule Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    a ∈ (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω))).range ↔
      baseUnitsEquiv a ∈ (normUnits K L).range := by
  haveI : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L b).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨(fixedModuleUnitsEquiv L).symm b, baseUnitsEquiv.injective ?_⟩
    change baseUnitsEquiv (RHDirect.CFT_AbstractLocalReciprocity.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply, hb]

theorem ker_localReciprocityLimit :
    (localReciprocityLimit K Ω).ker =
      ⨅ L : {L : IntermediateField K Ω // FiniteDimensional K L},
        haveI := L.2
        (normUnits K L.1).range := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  ext x
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  rw [MonoidHom.mem_ker, localReciprocityLimit_baseUnitsEquiv, map_eq_one_iff _
    (topAbelianizationEquiv K Ω).injective, ← MonoidHom.mem_ker,
    ClassFieldData.ker_reciprocityLimit_eq_iInf, Subgroup.mem_iInf, Subgroup.mem_iInf]
  constructor
  · intro h L
    haveI := L.2
    have := h ⟨fixingOpenSubgroup L.1, le_top⟩
    exact (mem_range_norm_top_iff L.1 a).1 this
  · intro h M
    have hM := fixingOpenSubgroup_fixedField M.1
    have h' := (mem_range_norm_top_iff _ a).2
      (h ⟨IntermediateField.fixedField (M.1 : Subgroup (Ω ≃ₐ[K] Ω)), inferInstance⟩)
    rw [hM] at h'
    exact h'

theorem denseRange_localReciprocityLimit : DenseRange (localReciprocityLimit K Ω) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  have hd := (localClassFieldData K Ω).denseRange_reciprocityLimit (classFieldAxiom_units K Ω)
    (K := (⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)))
  have hd' : DenseRange (((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤) ∘
      (baseUnitsEquiv (K := K) (Ω := Ω)).symm) := by
    unfold DenseRange
    rw [Function.Surjective.range_comp (MulEquiv.surjective _)]
    exact hd
  have := DenseRange.comp (topAbelianizationEquiv K Ω).surjective.denseRange hd'
    continuous_topAbelianizationEquiv
  exact this

end Universal

section Degree

open ProfiniteInteger

variable (K Ω) in

noncomputable def unramifiedOpenSubgroup (n : ℕ+) : OpenSubgroup (Ω ≃ₐ[K] Ω) where
  toSubgroup := (AddSubgroup.toSubgroup (multiples n)).comap (unramifiedDegree K Ω)
  isOpen' := (isOpen_multiples n).preimage (continuous_toAdd.comp continuous_unramifiedDegree)

theorem mem_unramifiedOpenSubgroup {n : ℕ+} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ (unramifiedOpenSubgroup K Ω n : Subgroup (Ω ≃ₐ[K] Ω)) ↔
      Multiplicative.toAdd (unramifiedDegree K Ω σ) ∈ multiples n :=
  Iff.rfl

theorem unramifiedDegree_of_mk_eq_localReciprocityLimit {x : Kˣ} {g : Ω ≃ₐ[K] Ω}
    (hg : (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = localReciprocityLimit K Ω x) :
    unramifiedDegree K Ω g = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ℤ̂) := by
  haveI := isDiscreteModule_units (K := K) (Ω := Ω)
  obtain ⟨a, rfl⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective x
  rw [localReciprocityLimit_baseUnitsEquiv] at hg
  have hg' : ((⟨g, Subgroup.mem_top g⟩ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
      TopologicalAbelianization _) =
      (localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) ⊤ a :=
    (topAbelianizationEquiv K Ω).injective (by rw [← hg]; rfl)
  obtain ⟨φ, hφ⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) (Multiplicative.ofAdd 1)
  set φ' : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := ⟨φ, Subgroup.mem_top φ⟩
  have hφ' : (localClassFieldData K Ω).relDeg ⊤ φ' = Multiplicative.ofAdd 1 := by
    rw [ClassFieldData.relDeg_eq_iff, localClassFieldData_deg, inertiaDegree_top_unramifiedDegree,
      pow_one]
    exact hφ
  have hv := valuation_top_localClassFieldData a
  refine multiplicative_ext fun n => ?_
  have hu : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⊓
      (localClassFieldData K Ω).deg.ker ≤ (unramifiedOpenSubgroup K Ω n : Subgroup (Ω ≃ₐ[K] Ω)) := by
    intro σ hσ
    rw [mem_unramifiedOpenSubgroup, (MonoidHom.mem_ker.1 hσ.2 : unramifiedDegree K Ω σ = 1),
      toAdd_one]
    exact (multiples n).zero_mem
  have hL : IsAbelianExtension ⊤ (unramifiedOpenSubgroup K Ω n) := by
    refine ⟨le_top, fun y hy => ?_⟩
    have h := commutator_le_ker_of_isMulCommutative
      ((unramifiedDegree K Ω).comp (Subgroup.subtype _)) hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    rw [Subgroup.mem_subgroupOf, mem_unramifiedOpenSubgroup, h, toAdd_one]
    exact (multiples n).zero_mem
  haveI := hL.normal
  have h1 := (localClassFieldData K Ω).reciprocity_abelianizationRestrict_reciprocityLimit
    (classFieldAxiom_units K Ω) hL a
  rw [← hg', abelianizationRestrict_mk] at h1
  have h2 := (localClassFieldData K Ω).reciprocityAbEquiv_symm_of_unramified_of_valuation hL.le
    (classFieldAxiom_units K Ω) hu hφ' a _ hv
  rw [MulEquiv.symm_apply_eq, ← map_zpow, ClassFieldData.reciprocityAbEquiv_of,
    ← QuotientGroup.mk_zpow] at h2
  have h3 := (localClassFieldData K Ω).reciprocity_injective (classFieldAxiom_units K Ω) hL
    (h1.trans h2)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_unramifiedOpenSubgroup] at h3
  rw [← proj_eq_zero_iff] at h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow, map_mul, map_inv, map_zpow,
    toAdd_mul, toAdd_inv, toAdd_zpow, map_add, map_neg, map_zsmul] at h3
  rw [show (φ' : Ω ≃ₐ[K] Ω) = φ from rfl, hφ, toAdd_ofAdd, map_one, zsmul_one,
    neg_add_eq_zero] at h3
  rw [toAdd_ofAdd, map_intCast]
  exact h3

theorem restrictNormal_eq_frobenius_of_mk_eq_localReciprocityLimit {π : Kˣ}
    (hπ : ord (π : K) = 1) {g : Ω ≃ₐ[K] Ω}
    (hg : (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = localReciprocityLimit K Ω π) :
    g.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω := by
  rw [restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff,
    unramifiedDegree_of_mk_eq_localReciprocityLimit hg, hπ, Int.cast_one]

end Degree

section Abelian

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
  [IsMulCommutative (L ≃ₐ[K] L)]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω]
  [FiniteDimensional K L] [IsGalois K L] in
theorem bijective_abelianizationOf :
    Function.Bijective (Abelianization.of : (L ≃ₐ[K] L) →* Abelianization (L ≃ₐ[K] L)) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun σ hσ => ?_, QuotientGroup.mk_surjective⟩
  rw [← MonoidHom.mem_ker, Abelianization.ker_of, commutator,
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at hσ
  exact hσ

noncomputable def localReciprocityAbelian : (L ≃ₐ[K] L) ≃* Kˣ ⧸ (normUnits K L).range :=
  (MulEquiv.ofBijective _ (bijective_abelianizationOf L)).trans (localReciprocity L)

theorem of_localReciprocityAbelian_symm (x : Kˣ ⧸ (normUnits K L).range) :
    Abelianization.of ((localReciprocityAbelian L).symm x) = (localReciprocity L).symm x := by
  rw [MulEquiv.eq_symm_apply]
  exact (localReciprocityAbelian L).apply_symm_apply x

theorem abelianRestrict_localReciprocityLimit (x : Kˣ) :
    abelianRestrict L (localReciprocityLimit K Ω x) =
      (localReciprocityAbelian L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  apply (bijective_abelianizationOf L).1
  rw [of_abelianRestrict_localReciprocityLimit, of_localReciprocityAbelian_symm]

end Abelian

section Absolute

noncomputable def localReciprocityAbsolute [CharZero K] :
    Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  localReciprocityLimit K (AlgebraicClosure K)

end Absolute

end RHDirect.CFT.LocalField
end Sec_LocalReciprocityUniversal


/-! ### ExistenceDictionary -/
section Sec_ExistenceDictionary

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity

section Dictionary

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem normal_subgroupOf_top_fixingOpenSubgroup_iff (L : IntermediateField K Ω)
    [FiniteDimensional K L] :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal ↔ IsGalois K L := by
  rw [← InfiniteGalois.normal_iff_isGalois, coe_fixingOpenSubgroup]
  constructor
  · intro h
    refine ⟨fun n hn g => ?_⟩
    have := h.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, Subgroup.mem_top g⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro h
    exact h.subgroupOf _

theorem isAbelianExtension_fixingOpenSubgroup_iff (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsAbelianExtension ⊤ (fixingOpenSubgroup L) ↔
      IsGalois K L ∧ ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
  constructor
  · intro h
    have hn := h.normal
    have hG : IsGalois K L := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).1 hn
    refine ⟨hG, fun σ τ => ?_⟩
    have hc := h.isMulCommutative
    obtain ⟨p, rfl⟩ := (baseQuotientEquiv L).surjective σ
    obtain ⟨q, rfl⟩ := (baseQuotientEquiv L).surjective τ
    rw [← map_mul, ← map_mul, hc.is_comm.comm]
  · rintro ⟨hG, hc⟩
    have hn := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).2 hG
    have : IsMulCommutative (((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :=
      ⟨⟨fun p q => (baseQuotientEquiv L).injective (by rw [map_mul, map_mul, hc])⟩⟩
    exact isAbelianExtension_of_isMulCommutative le_top

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem map_baseUnitsEquiv_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (normGroup Ωˣ ⊤ (fixingOpenSubgroup L)).map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  have : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩
    change baseUnitsEquiv (RHDirect.CFT_AbstractLocalReciprocity.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem mem_normGroup_iff_mem_range_normUnits (L : IntermediateField K Ω) [FiniteDimensional K L]
    (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    a ∈ normGroup Ωˣ ⊤ (fixingOpenSubgroup L) ↔ baseUnitsEquiv a ∈ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup L]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, hba⟩
    rwa [← baseUnitsEquiv.injective hba]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem normGroup_eq_comap (L : IntermediateField K Ω) [FiniteDimensional K L] :
    normGroup Ωˣ ⊤ (fixingOpenSubgroup L) =
      (normUnits K L).range.comap
        (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) := by
  ext a
  exact mem_normGroup_iff_mem_range_normUnits L a

variable (L : IntermediateField K Ω) [FiniteDimensional K L]

noncomputable def maximalAbelianSubextension : IntermediateField K Ω :=
  IntermediateField.fixedField (maxAbelian (le_top : fixingOpenSubgroup L ≤ ⊤) : Subgroup (Ω ≃ₐ[K] Ω))

instance finiteDimensional_maximalAbelianSubextension :
    FiniteDimensional K (maximalAbelianSubextension L) :=
  finiteDimensional_fixedField_openSubgroup _

theorem fixingOpenSubgroup_maximalAbelianSubextension :
    fixingOpenSubgroup (maximalAbelianSubextension L) = maxAbelian (le_top : fixingOpenSubgroup L ≤ ⊤) :=
  fixingOpenSubgroup_fixedField _

theorem isAbelianExtension_fixingOpenSubgroup_maximalAbelianSubextension :
    IsAbelianExtension ⊤ (fixingOpenSubgroup (maximalAbelianSubextension L)) := by
  rw [fixingOpenSubgroup_maximalAbelianSubextension]
  exact isAbelianExtension_maxAbelian _

instance isGalois_maximalAbelianSubextension : IsGalois K (maximalAbelianSubextension L) :=
  ((isAbelianExtension_fixingOpenSubgroup_iff _).1
    (isAbelianExtension_fixingOpenSubgroup_maximalAbelianSubextension L)).1

end Dictionary

section Correspondence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

theorem range_normUnits_le_range_normUnits_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsGalois K L] [IsGalois K L']
    (hL : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hL' : ∀ σ τ : L' ≃ₐ[K] L', σ * τ = τ * σ) :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup,
    Subgroup.map_le_map_iff_of_injective baseUnitsEquiv.injective,
    (localClassFieldTheory K Ω).normGroup_le_normGroup_iff (localClassFieldTheory K Ω).classFieldAxiom
      ((isAbelianExtension_fixingOpenSubgroup_iff L).2 ⟨inferInstance, hL⟩)
      ((isAbelianExtension_fixingOpenSubgroup_iff L').2 ⟨inferInstance, hL'⟩)]
  exact fixingSubgroup_le_fixingSubgroup_iff

end Correspondence

end RHDirect.CFT.LocalField
end Sec_ExistenceDictionary


/-! ### Existence -/
section Sec_Existence


open ValuativeRel RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

theorem lubinTateField_mul_comm (n : ℕ)
    (σ τ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) : σ * τ = τ * σ := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  apply (lubinTateGalEquiv hπ hf n).injective
  rw [map_mul, map_mul]
  exact mul_comm (G := (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ) _ _

include hf in

theorem mem_unitFiltration_of_mem_range_normUnits {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    (h : unitUniformizerPow hπ u k ∈ (normUnits K (lubinTateField Ω hπ hf n)).range) :
    u ∈ unitFiltration K n := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set T := lubinTateField Ω hπ hf n
  have hab : IsAbelianExtension ⊤ (fixingOpenSubgroup T) :=
    (isAbelianExtension_fixingOpenSubgroup_iff T).2 ⟨inferInstance, lubinTateField_mul_comm hπ hf n⟩
  have := hab.normal
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u k
  have hr := reciprocity_lubinTate hπ hf hn (fixingOpenSubgroup T)
    (by rw [coe_fixingOpenSubgroup]) (by rw [coe_fixingOpenSubgroup]; exact inf_le_left) u k τ hτd hτ
  have hmem : τ ∈ (fixingOpenSubgroup T : Subgroup (Ω ≃ₐ[K] Ω)) := by
    refine ((localClassFieldTheory K Ω).mem_normGroup_iff_of_reciprocity
      (localClassFieldTheory K Ω).classFieldAxiom hab hr).1 ?_
    rw [mem_normGroup_iff_mem_range_normUnits, MulEquiv.apply_symm_apply]
    exact h
  rw [coe_fixingOpenSubgroup] at hmem

  have hchar := lubinTateChar_eq_of_apply hπ hf (le_refl T) 1 ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) fun x hx => by
    have e := congrArg IdealPoint.val (hτ x hx)
    rw [lubinTateGalPointMap_val] at e
    rw [← e, AlgEquiv.one_apply]
    exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _
      (val_mem_lubinTateField hπ hf hx)).symm
  rw [map_one, Units.val_one] at hchar
  have h1 : unitsMk π n u⁻¹ = 1 := Units.ext (by rw [coe_unitsMk, Units.val_one, hchar])
  exact inv_mem_iff.1 ((unitsMk_eq_one_iff hπ).1 h1)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem range_normUnits_anti {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] (h : L ≤ L') : (normUnits K L').range ≤ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup]
  exact Subgroup.map_mono (normGroup_mono (fixingOpenSubgroup_anti h) le_top)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem unitUniformizerPow_eq (u : 𝒪[K]ˣ) (k : ℤ) :
    unitUniformizerPow hπ u k = uniformizerUnit hπ ^ k * unitsIncl K u := by
  rw [unitUniformizerPow, mul_comm]
  rfl

include hf in

theorem range_normUnits_sup_le {n m : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) (hmE : m ∣ Module.finrank K E) {H : Subgroup Kˣ}
    (hnH : unitFiltrationUnits K n ≤ H) (hmH : (powMonoidHom m : Kˣ →* Kˣ).range ≤ H) :
    (normUnits K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)).range ≤ H := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have := hE.1
  set T := lubinTateField Ω hπ hf n
  set L : IntermediateField K Ω := T ⊔ E
  rintro _ ⟨y, rfl⟩

  have hdvd : m ∣ residueDegree K L := by
    have h1 := residueDegree_dvd_of_le (le_sup_right : E ≤ L)
    rw [residueDegree_eq_finrank_of_unramified K E hE.ramificationIndex_eq_one] at h1
    exact hmE.trans h1
  obtain ⟨j, hj⟩ := hdvd
  obtain ⟨⟨k, u⟩, hx⟩ := (unitsOfIntProd_bijective hπ).2 (normUnits K L y)
  have hk : k.toAdd = (m : ℤ) * ((j : ℤ) * ord ((y : L) : L)) := by
    rw [← ord_unitsOfIntProd hπ k u, hx, coe_normUnits, ord_norm, hj]
    push_cast
    ring
  have hxu : unitUniformizerPow hπ u k.toAdd = normUnits K L y := by
    rw [← hx, unitsOfIntProd_eq, unitUniformizerPow_eq]

  have hT : unitUniformizerPow hπ u k.toAdd ∈ (normUnits K T).range := by
    rw [hxu]
    exact range_normUnits_anti le_sup_left ⟨y, rfl⟩
  have hu := mem_unitFiltration_of_mem_range_normUnits hπ hf hn u k.toAdd hT
  rw [← hxu, unitUniformizerPow_eq]
  refine H.mul_mem (hmH ⟨uniformizerUnit hπ ^ ((j : ℤ) * ord ((y : L) : L)), ?_⟩)
    (hnH ⟨u, hu, rfl⟩)
  rw [powMonoidHom_apply, ← zpow_natCast, ← zpow_mul, hk, mul_comm]

end LubinTate

section Existence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

theorem exists_range_normUnits_le (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), (normUnits K L).range ≤ H := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨⟨n, hnH⟩, m, hm, hmH⟩ := exists_unitFiltrationUnits_le_and_range_pow_le hH
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
  have := hE.1
  have hmE : m ∣ Module.finrank K (unramifiedTower K Ω m) := by
    rw [finrank_unramifiedTower]
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hm) m.le_succ
  exact ⟨_, inferInstance, range_normUnits_sup_le hπ (isLubinTateSeries_ltPoly π) n.succ_pos hE hmE
    ((unitFiltrationUnits_antitone n.le_succ).trans hnH) hmH⟩

theorem isOpen_range_normUnits_and_finiteIndex (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsOpen ((normUnits K L).range : Set Kˣ) ∧ (normUnits K L).range.FiniteIndex := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  exact ⟨isOpen_range_normUnits K L, finiteIndex_range_normUnits K L⟩

theorem exists_range_normUnits_eq (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧ (normUnits K L).range = H := by
  obtain ⟨L₀, _, hL₀⟩ := exists_range_normUnits_le (Ω := Ω) H hH
  set B := H.comap (baseUnitsEquiv (K := K) (Ω := Ω) :
    fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ)
  have hB : normGroup Ωˣ ⊤ (fixingOpenSubgroup L₀) ≤ B := by
    rw [normGroup_eq_comap]
    exact Subgroup.comap_mono hL₀
  obtain ⟨U, hU, -, hUB⟩ := (localClassFieldTheory K Ω).exists_normGroup_eq_of_le
    (localClassFieldTheory K Ω).classFieldAxiom le_top hB
  set M := IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
  have hMU : fixingOpenSubgroup M = U := fixingOpenSubgroup_fixedField U
  rw [← hMU] at hU hUB
  obtain ⟨hG, hc⟩ := (isAbelianExtension_fixingOpenSubgroup_iff M).1 hU
  refine ⟨M, inferInstance, hG, hc, ?_⟩
  rw [← map_baseUnitsEquiv_normGroup, hUB]
  exact Subgroup.map_comap_eq_self_of_surjective baseUnitsEquiv.surjective H

end Existence

end RHDirect.CFT.LocalField
end Sec_Existence


/-! ### LocalArtinMap -/
section Sec_LocalArtinMap


namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup

theorem continuous_of_isOpen_ker {G D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group D] [TopologicalSpace D] [DiscreteTopology D] (f : G →* D)
    (hf : IsOpen (f.ker : Set G)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one, nhds_discrete D, Filter.tendsto_pure]
  exact Filter.mem_of_superset (hf.mem_nhds f.ker.one_mem) fun x hx => hx

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Def

variable (K Ω) in

def localArtinMap :
    Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom.comp (localReciprocityLimit K Ω)

theorem localArtinMap_apply (x : Kˣ) :
    localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x) :=
  rfl

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    restrictAb L (le_maximalAbelianExtension L) (topologicalAbelianizationEquiv K Ω g) =
      abelianRestrict L g := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [restrictAb_topologicalAbelianizationEquiv]
  rfl

theorem restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (x : Kˣ) :
    restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) =
      (localReciprocityAbelian L).symm (x : Kˣ ⧸ (normUnits K L).range) := by
  rw [localArtinMap_apply, restrictAb_topologicalAbelianizationEquiv_eq_abelianRestrict,
    abelianRestrict_localReciprocityLimit]

theorem ker_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)).ker =
      (normUnits K L).range := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, restrictAb_localArtinMap, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff]

theorem surjective_restrictAb_localArtinMap (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    Function.Surjective ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) := by
  intro σ
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (localReciprocityAbelian L σ)
  refine ⟨x, ?_⟩
  rw [MonoidHom.comp_apply, restrictAb_localArtinMap, hx, MulEquiv.symm_apply_apply]

end Def

section Unramified

instance isAbelianGalois_maximalUnramifiedExtension :
    IsAbelianGalois K (maximalUnramifiedExtension K Ω) :=
  { toIsMulCommutative := ⟨⟨fun σ τ => (maximalUnramifiedExtensionGaloisEquiv K Ω).injective (by
      rw [map_mul, map_mul, mul_comm])⟩⟩ }

theorem maximalUnramifiedExtension_le_maximalAbelianExtension :
    maximalUnramifiedExtension K Ω ≤ maximalAbelianExtension K Ω :=
  le_maximalAbelianExtension _

theorem restrictAb_localArtinMap_uniformizer {π : Kˣ} (hπ : ord (π : K) = 1) :
    restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
      (localArtinMap K Ω π) = maximalUnramifiedExtensionFrobenius K Ω := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (localReciprocityLimit K Ω π)
  rw [localArtinMap_apply, ← hg, restrictAb_topologicalAbelianizationEquiv]
  exact restrictNormal_eq_frobenius_of_mk_eq_localReciprocityLimit hπ hg

theorem restrictAb_localArtinMap_of_le_maximalUnramifiedExtension (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] (hL : L ≤ maximalUnramifiedExtension K Ω) (x : Kˣ) :
    restrictAb L (hL.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω x) =
      unramifiedFrobenius K Ω L ^ ord (x : K) := by
  have := isAbelianGalois_of_le_maximalAbelianExtension L
    (hL.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
  apply (bijective_abelianizationOf L).1
  rw [restrictAb_localArtinMap, of_localReciprocityAbelian_symm,
    localReciprocity_symm_mk_of_le_maximalUnramifiedExtension L hL, map_zpow]

theorem localArtinMap_uniformizer_apply {π : Kˣ} (hπ : ord (π : K) = 1) {y : Ω}
    (hy : y ∈ maximalUnramifiedExtension K Ω) :
    ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
      maximalAbelianExtension K Ω) : Ω) =
      (maximalUnramifiedExtensionFrobenius K Ω ⟨y, hy⟩ : Ω) := by
  rw [← restrictAb_localArtinMap_uniformizer hπ, restrictAb_apply]

end Unramified

section Topology

theorem continuous_localArtinMap : Continuous (localArtinMap K Ω) := by
  rw [continuous_iff_restrictAb]
  intro L _ _
  refine continuous_of_isOpen_ker ((restrictAb L (le_maximalAbelianExtension L)).comp
    (localArtinMap K Ω)) ?_
  rw [ker_restrictAb_localArtinMap]
  exact (isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L).1

end Topology

section Injective

theorem eq_one_of_forall_mem_unitFiltration {u : 𝒪[K]ˣ}
    (h : ∀ n, 1 ≤ n → u ∈ unitFiltration K n) : u = 1 := by
  have hmem : (u : 𝒪[K]) - 1 ∈ ⨅ n : ℕ, 𝓂[K] ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact h n hn
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top', Ideal.mem_bot, sub_eq_zero] at hmem
  exact Units.ext hmem

theorem injective_localArtinMap : Function.Injective (localArtinMap K Ω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hker : x ∈ (localReciprocityLimit K Ω).ker := by
    rw [MonoidHom.mem_ker]
    exact (topologicalAbelianizationEquiv K Ω).injective (by rw [map_one]; exact hx)
  rw [ker_localReciprocityLimit, Subgroup.mem_iInf] at hker
  have hnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L], x ∈ (normUnits K L).range :=
    fun L _ => hker ⟨L, inferInstance⟩
  have hopen : ∀ (H : Subgroup Kˣ) [H.FiniteIndex], IsOpen (H : Set Kˣ) → x ∈ H := by
    intro H _ hH
    obtain ⟨L, hL, -, -, hLH⟩ := exists_range_normUnits_eq (Ω := Ω) H hH
    rw [← hLH]
    exact hnorm L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set e := unitsEquivIntProd hπ
  have hk : (e x).1 = 1 := by
    set k := Multiplicative.toAdd (e x).1 with hk
    let f : Kˣ →* Multiplicative (ZMod (k.natAbs + 1)) :=
      (AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod (k.natAbs + 1)))).comp
        ((MonoidHom.fst _ _).comp e.toMonoidHom)
    have hfo : IsOpen (f.ker : Set Kˣ) := by
      refine Subgroup.isOpen_mono (H₁ := unitFiltrationUnits K 0) ?_ (isOpen_unitFiltrationUnits 0)
      rintro _ ⟨u, -, rfl⟩
      simp [f, e, unitsEquivIntProd_unitsIncl]
    have hfx := hopen f.ker hfo
    rw [MonoidHom.mem_ker] at hfx
    have h0 : ((k : ℤ) : ZMod (k.natAbs + 1)) = 0 := by
      simpa [f, k] using hfx
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    have : k = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h0 (by simp only [Int.natAbs_natCast]; omega)
    rw [← ofAdd_toAdd (e x).1, ← hk, this, ofAdd_zero]
  set u := (e x).2
  have hxu : x = unitsIncl K u := by
    apply e.injective
    rw [unitsEquivIntProd_unitsIncl, ← hk]
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf := isLubinTateSeries_ltPoly π
  have hu : u = 1 := by
    refine eq_one_of_forall_mem_unitFiltration fun n hn => ?_
    refine mem_unitFiltration_of_mem_range_normUnits (Ω := Ω) hπ hf hn u 0 ?_
    rw [unitUniformizerPow_eq, zpow_zero, one_mul, ← hxu]
    exact hnorm _
  rw [hxu, hu, map_one]

end Injective

end RHDirect.CFT.LocalField
end Sec_LocalArtinMap


/-! ### NormCorrespondence -/
section Sec_NormCorrespondence


namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Index

theorem index_range_normUnits_of_isAbelianGalois (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] : (normUnits K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, ← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (localReciprocityAbelian L).toEquiv).symm

end Index

section Lattice

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem isAbelianGalois_sup (L L' : IntermediateField K Ω) [IsAbelianGalois K L]
    [IsAbelianGalois K L'] : IsAbelianGalois K (L ⊔ L' : IntermediateField K Ω) :=
  isAbelianGalois_of_le_maximalAbelianExtension _
    (sup_le (le_maximalAbelianExtension L) (le_maximalAbelianExtension L'))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem mul_comm_of_isAbelianGalois' (L : IntermediateField K Ω) [IsAbelianGalois K L]
    (σ τ : L ≃ₐ[K] L) : σ * τ = τ * σ :=
  mul_comm' σ τ

theorem range_normUnits_le_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsAbelianGalois K L] [IsAbelianGalois K L'] :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L :=
  range_normUnits_le_range_normUnits_iff (mul_comm_of_isAbelianGalois' L)
    (mul_comm_of_isAbelianGalois' L')

theorem exists_isAbelianGalois_range_normUnits_eq (H : Subgroup Kˣ) [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      (normUnits K L).range = H := by
  obtain ⟨L, hL, hG, hc, hLH⟩ := exists_range_normUnits_eq (Ω := Ω) H hH
  exact ⟨L, hL, { toIsGalois := hG, toIsMulCommutative := ⟨⟨hc⟩⟩ }, hLH⟩

end Lattice

section OrderIso

variable (K) in

def openFiniteIndexSubgroups : Set (Subgroup Kˣ) :=
  {H | IsOpen (H : Set Kˣ) ∧ H.FiniteIndex}

variable (K Ω) in

def normGroupMap (L : finiteAbelianExtensions K Ω) : openFiniteIndexSubgroups K :=
  have := L.2.1
  ⟨(normUnits K (L : IntermediateField K Ω)).range,
    isOpen_range_normUnits_and_finiteIndex (Ω := Ω) _⟩

theorem normGroupMap_injective : Function.Injective (normGroupMap K Ω) := by
  intro L L' h
  have := L.2.1
  have := L.2.2
  have := L'.2.1
  have := L'.2.2
  have h' : (normUnits K (L : IntermediateField K Ω)).range =
      (normUnits K (L' : IntermediateField K Ω)).range := congrArg Subtype.val h
  exact Subtype.ext (le_antisymm (range_normUnits_le_iff.1 h'.ge) (range_normUnits_le_iff.1 h'.le))

theorem normGroupMap_surjective : Function.Surjective (normGroupMap K Ω) := by
  intro H
  have := H.2.2
  obtain ⟨L, h1, h2, hL⟩ := exists_isAbelianGalois_range_normUnits_eq (Ω := Ω) H.1 H.2.1
  exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩

theorem normGroupMap_le_iff {L L' : finiteAbelianExtensions K Ω} :
    normGroupMap K Ω L ≤ normGroupMap K Ω L' ↔ L' ≤ L := by
  have := L.2.1
  have := L.2.2
  have := L'.2.1
  have := L'.2.2
  exact range_normUnits_le_iff

variable (K Ω) in

def normGroupOrderIso : finiteAbelianExtensions K Ω ≃o (openFiniteIndexSubgroups K)ᵒᵈ where
  toEquiv := (Equiv.ofBijective _ ⟨normGroupMap_injective, normGroupMap_surjective⟩).trans
    OrderDual.toDual
  map_rel_iff' := normGroupMap_le_iff

theorem normGroupOrderIso_apply (L : finiteAbelianExtensions K Ω) :
    (OrderDual.ofDual (normGroupOrderIso K Ω L)).1 =
      (have := L.2.1; (normUnits K (L : IntermediateField K Ω)).range) :=
  rfl

end OrderIso

end RHDirect.CFT.LocalField
end Sec_NormCorrespondence


/-! ### LocalArtinCompletion -/
section Sec_LocalArtinCompletion


namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_eq_of_le {E E' : IntermediateField F Ω} [Normal F E] [Normal F E']
    (hE' : E' ≤ maximalAbelianExtension F Ω) (hEE' : E ≤ E')
    {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : restrictAb E' hE' σ = restrictAb E' hE' τ) :
    restrictAb E (hEE'.trans hE') σ = restrictAb E (hEE'.trans hE') τ := by
  ext y
  have := congrArg (fun ρ : E' ≃ₐ[F] E' => ((ρ ⟨y, hEE' y.2⟩ : E') : Ω)) h
  simp only [restrictAb_apply] at this ⊢
  exact this

end Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section ClassField

variable (K Ω) in

def classField (H : openFiniteIndex Kˣ) : finiteAbelianExtensions K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual ⟨H.1, H.2⟩)

theorem range_normUnits_classField (H : openFiniteIndex Kˣ) :
    (normUnits K (classField K Ω H : IntermediateField K Ω)).range = H.1 :=
  congrArg (fun y => (OrderDual.ofDual y).1)
    ((normGroupOrderIso K Ω).apply_symm_apply (OrderDual.toDual ⟨H.1, H.2⟩))

theorem classField_anti {H H' : openFiniteIndex Kˣ} (h : H.1 ≤ H'.1) :
    (classField K Ω H' : IntermediateField K Ω) ≤ classField K Ω H := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  have := (classField K Ω H').2.1
  have := (classField K Ω H').2.2
  rw [← range_normUnits_le_iff, range_normUnits_classField, range_normUnits_classField]
  exact h

theorem le_classField (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L] :
    L ≤ classField K Ω ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩ := by
  have := (classField K Ω ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩).2.1
  have := (classField K Ω ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩).2.2
  rw [← range_normUnits_le_iff, range_normUnits_classField]

end ClassField

section Coord

variable (K Ω) in

def artinCoord (H : openFiniteIndex Kˣ) :
    (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* Kˣ ⧸ H.1 :=
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField H)).toMonoidHom.comp
    ((localReciprocityAbelian (classField K Ω H : IntermediateField K Ω)).toMonoidHom.comp
      (restrictAb _ (le_maximalAbelianExtension _)))

theorem artinCoord_eq_of (H : openFiniteIndex Kˣ)
    (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) (x : Kˣ)
    (h : have := (classField K Ω H).2.1; have := (classField K Ω H).2.2
      restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) σ =
        restrictAb _ (le_maximalAbelianExtension _) (localArtinMap K Ω x)) :
    artinCoord K Ω H σ = (x : Kˣ ⧸ H.1) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  simp only [artinCoord, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, restrictAb_localArtinMap, MulEquiv.apply_symm_apply, QuotientGroup.quotientMulEquivOfEq_mk]

theorem artinCoord_localArtinMap (H : openFiniteIndex Kˣ) (x : Kˣ) :
    artinCoord K Ω H (localArtinMap K Ω x) = (x : Kˣ ⧸ H.1) :=
  artinCoord_eq_of H _ x rfl

theorem exists_artinCoord_eq (H H' : openFiniteIndex Kˣ) (h : H.1 ≤ H'.1)
    (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :
    ∃ x : Kˣ, artinCoord K Ω H σ = (x : Kˣ ⧸ H.1) ∧ artinCoord K Ω H' σ = (x : Kˣ ⧸ H'.1) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  have := (classField K Ω H').2.1
  have := (classField K Ω H').2.2
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := Ω) (classField K Ω H : IntermediateField K Ω)
    (restrictAb _ (le_maximalAbelianExtension _) σ)
  refine ⟨x, artinCoord_eq_of H σ x hx.symm, artinCoord_eq_of H' σ x ?_⟩
  exact restrictAb_eq_of_le (le_maximalAbelianExtension _) (classField_anti h) hx.symm

theorem continuous_artinCoord (H : openFiniteIndex Kˣ) : Continuous (artinCoord K Ω H) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  change Continuous ((fun ρ => (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField H))
    (localReciprocityAbelian (classField K Ω H : IntermediateField K Ω) ρ)) ∘
      restrictAb _ (le_maximalAbelianExtension _))
  exact continuous_of_discreteTopology.comp (continuous_restrictAb _ _)

end Coord

section Completion

variable (K Ω) in

def galToOpenCompletion :
    (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* openCompletion Kˣ :=
  MonoidHom.codRestrict (MonoidHom.pi fun H => artinCoord K Ω H) (openCompletion Kˣ) fun σ H H' h => by
    obtain ⟨x, hx, hx'⟩ := exists_artinCoord_eq H H' h σ
    change quotientMapOfLE h (artinCoord K Ω H σ) = artinCoord K Ω H' σ
    rw [hx, hx', quotientMapOfLE_mk]

theorem galToOpenCompletion_apply (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)
    (H : openFiniteIndex Kˣ) :
    ((galToOpenCompletion K Ω σ : openCompletion Kˣ) : ∀ H : openFiniteIndex Kˣ, Kˣ ⧸ H.1) H =
      artinCoord K Ω H σ :=
  rfl

theorem galToOpenCompletion_localArtinMap (x : Kˣ) :
    galToOpenCompletion K Ω (localArtinMap K Ω x) = openCompletion.of Kˣ x :=
  openCompletion.ext fun H => artinCoord_localArtinMap H x

theorem continuous_galToOpenCompletion : Continuous (galToOpenCompletion K Ω) :=
  Continuous.subtype_mk (continuous_pi fun H => continuous_artinCoord H) _

theorem injective_galToOpenCompletion : Function.Injective (galToOpenCompletion K Ω) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine ext_restrictAb fun L _ _ => ?_
  set H : openFiniteIndex Kˣ := ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  have hH : artinCoord K Ω H σ = 1 := by
    rw [← galToOpenCompletion_apply, hσ]
    rfl
  have h1 : restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) σ =
      restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) 1 := by
    rw [map_one]
    simpa [artinCoord] using hH
  exact restrictAb_eq_of_le (le_maximalAbelianExtension _) (le_classField L) h1

theorem surjective_galToOpenCompletion : Function.Surjective (galToOpenCompletion K Ω) := by
  have hc : IsClosed (Set.range (galToOpenCompletion K Ω)) :=
    (isCompact_range continuous_galToOpenCompletion).isClosed
  have hsub : Set.range (openCompletion.of Kˣ) ⊆ Set.range (galToOpenCompletion K Ω) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, galToOpenCompletion_localArtinMap x⟩
  have := (openCompletion.denseRange_of (G := Kˣ)).closure_range
  intro a
  have ha : a ∈ closure (Set.range (openCompletion.of Kˣ)) := by rw [this]; trivial
  exact hc.closure_subset_iff.2 hsub ha

variable (K Ω) in

def localArtinCompletion :
    openCompletion Kˣ ≃ₜ* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  let e := MulEquiv.ofBijective (galToOpenCompletion K Ω)
    ⟨injective_galToOpenCompletion, surjective_galToOpenCompletion⟩
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := continuous_galToOpenCompletion
      continuous_invFun :=
        (continuous_galToOpenCompletion.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end Completion

end RHDirect.CFT.LocalField
end Sec_LocalArtinCompletion


/-! ### KroneckerWeber -/
section Sec_KroneckerWeber


open _root_.IntermediateField ValuativeRel

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup

section Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem mul_comm_of_isAbelianGalois (L : IntermediateField K Ω) [IsAbelianGalois K L]
    (σ τ : L ≃ₐ[K] L) : σ * τ = τ * σ :=
  (IsMulCommutative.is_comm (M := L ≃ₐ[K] L)).comm σ τ

theorem isAbelianGalois_of_mul_comm (L : IntermediateField K Ω) [IsGalois K L]
    (h : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) : IsAbelianGalois K L where
  is_comm := ⟨h⟩

end Abelian

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosed Ω] [Algebra.IsSeparable K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hf in

theorem isAbelianGalois_lubinTateField_sup {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) :
    IsAbelianGalois K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) := by
  have := hE.1
  have := hE.isGalois
  exact isAbelianGalois_of_mul_comm _ (lubinTateUnramified_mul_comm hπ hf hn hE)

include hf in

theorem exists_le_lubinTateField_sup_unramifiedTower (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ n m : ℕ, L ≤ lubinTateField Ω hπ hf (n + 1) ⊔ unramifiedTower K Ω m := by
  have : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨hO, hF⟩ := isOpen_range_normUnits_and_finiteIndex L
  obtain ⟨⟨n, hnH⟩, m, hm, hmH⟩ := exists_unitFiltrationUnits_le_and_range_pow_le hO
  have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
  have := hE.1
  have hmE : m ∣ Module.finrank K (unramifiedTower K Ω m) := by
    rw [finrank_unramifiedTower]
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hm) m.le_succ
  have hle := range_normUnits_sup_le hπ hf n.succ_pos hE hmE
    ((unitFiltrationUnits_antitone n.le_succ).trans hnH) hmH
  have hM := isAbelianGalois_lubinTateField_sup hπ hf n.succ_pos hE
  exact ⟨n, m, (range_normUnits_le_range_normUnits_iff (mul_comm_of_isAbelianGalois _)
    (mul_comm_of_isAbelianGalois L)).1 hle⟩

theorem maximalAbelianExtension_eq_lubinTateMaxUnramified :
    maximalAbelianExtension K Ω = lubinTateMaxUnramified Ω hπ := by
  have : IsSepClosure K Ω := ⟨inferInstance, inferInstance⟩
  have hf := isLubinTateSeries_ltPoly π
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
    obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower hπ hf L
    exact sup_le_sup (lubinTateField_le_lubinTateLimit hπ hf _)
      (unramifiedTower_le_maximalUnramifiedExtension m) (h hyL)
  · refine @le_maximalAbelianExtension K Ω _ _ _ _ _ (isAbelianGalois_of_mul_comm _ fun σ τ =>
      (lubinTateMaxUnramifiedGalEquiv hπ hf).injective (by rw [map_mul, map_mul, mul_comm]))

end LubinTate

section Padic

namespace Padic

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

theorem irreducible_natCast_integer : Irreducible (p : 𝒪[ℚ_[p]]) := by
  have h := (MulEquiv.irreducible_iff (f := (PadicRank.padicIntEquivInteger p).toMulEquiv)
    (x := (p : ℤ_[p]))).2 PadicInt.irreducible_p
  simpa using h

theorem card_residueField : Nat.card 𝓀[ℚ_[p]] = p := by
  rw [← Nat.card_congr (IsLocalRing.ResidueField.mapEquiv
      (PadicRank.padicIntEquivInteger p)).toEquiv,
    Nat.card_congr PadicInt.residueField.toEquiv, Nat.card_zmod]

def multiplicativeLTPoly : 𝒪[ℚ_[p]][X] := (1 + X) ^ p - 1

theorem isLubinTateSeries_multiplicativeLTPoly :
    IsLubinTateSeries (p : 𝒪[ℚ_[p]]) (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) where
  constantCoeff_eq_zero := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      multiplicativeLTPoly, coeff_sub, coeff_one_add_X_pow]
    simp
  coeff_one := by
    rw [Polynomial.coeff_coe, multiplicativeLTPoly, coeff_sub, coeff_one_add_X_pow]
    simp [Polynomial.coeff_one]
  dvd_coeff_sub n := by
    rw [card_residueField, ← Polynomial.coe_X, ← Polynomial.coe_pow, ← Polynomial.coe_sub,
      Polynomial.coeff_coe, multiplicativeLTPoly, coeff_sub, coeff_sub, coeff_one_add_X_pow,
      coeff_one, coeff_X_pow]
    have hp0 := hp.out.ne_zero
    by_cases h0 : n = 0
    · subst h0
      simp [Ne.symm hp0]
    by_cases hpn : n = p
    · subst hpn
      simp [h0]
    rw [if_neg h0, if_neg hpn, sub_zero, sub_zero]
    rcases lt_or_gt_of_ne hpn with h | h
    · exact Nat.cast_dvd_cast (hp.out.dvd_choose_self h0 h)
    · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero]
      exact dvd_zero _

section Torsion

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra ℚ_[p] Ω] [ValuativeExtension ℚ_[p] Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

theorem val_pow_smul (n : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (((p : 𝒪[ℚ_[p]]) ^ n) • x).val = (1 + x.val) ^ (p ^ n) - 1 := by
  have := t2Space_of_isValuativeTopology Ω
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_smul, ih, lubinTate_uniformizer_smul_val, psEval_polynomial]
    simp only [multiplicativeLTPoly, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_X, map_sub, map_pow, map_add, map_one, aeval_X]
    rw [add_sub_cancel, ← pow_mul, ← pow_succ']

theorem lubinTateField_le_adjoin_rootsOfUnity (n : ℕ) :
    lubinTateField Ω (irreducible_natCast_integer p) (isLubinTateSeries_multiplicativeLTPoly p) n ≤
      adjoin ℚ_[p] {ζ : Ω | ζ ^ (p ^ n) = 1} := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have h := congrArg IdealPoint.val ((mem_lubinTateTorsion _ n x).1 hx)
  rw [val_pow_smul, IdealPoint.val_zero, sub_eq_zero] at h
  have hx' : x.val = (1 + x.val) - 1 := by ring
  rw [hx']
  exact sub_mem (subset_adjoin _ _ h) (one_mem _)

end Torsion

variable {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosed Ω] [Algebra.IsSeparable ℚ_[p] Ω]

omit [Algebra.IsSeparable ℚ_[p] Ω] in

theorem unramifiedTower_le_adjoin_rootsOfUnity (m : ℕ) :
    unramifiedTower ℚ_[p] Ω m ≤
      adjoin ℚ_[p] {ζ : Ω | ζ ^ (p ^ (m + 1).factorial - 1) = 1} := by
  rw [unramifiedTower, adjoin_simple_le_iff]
  refine subset_adjoin _ _ ?_
  have h := (isPrimitiveRoot_unramifiedTowerRoot (K := ℚ_[p]) (Ω := Ω) m).pow_eq_one
  rwa [card_residueField] at h

theorem exists_le_adjoin_rootsOfUnity (L : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] L]
    [IsAbelianGalois ℚ_[p] L] :
    ∃ N : ℕ, 0 < N ∧ L ≤ adjoin ℚ_[p] {ζ : Ω | ζ ^ N = 1} := by
  let := algebraicValuativeRel ℚ_[p] Ω
  let := algebraicTopology ℚ_[p] Ω
  have := algebraicValuativeRel_valuativeExtension ℚ_[p] Ω
  have := algebraicTopology_isValuativeTopology ℚ_[p] Ω
  obtain ⟨n, m, h⟩ := exists_le_lubinTateField_sup_unramifiedTower (irreducible_natCast_integer p)
    (isLubinTateSeries_multiplicativeLTPoly p) L
  have hM : 0 < p ^ (m + 1).factorial - 1 := Nat.sub_pos_of_lt
    (Nat.one_lt_pow (Nat.factorial_ne_zero _) hp.out.one_lt)
  refine ⟨p ^ (n + 1) * (p ^ (m + 1).factorial - 1),
    Nat.mul_pos (pow_pos hp.out.pos _) hM, h.trans (sup_le ?_ ?_)⟩
  · refine (lubinTateField_le_adjoin_rootsOfUnity p (n + 1)).trans (adjoin.mono _ _ _ ?_)
    intro ζ (hζ : ζ ^ _ = 1)
    change ζ ^ _ = 1
    rw [pow_mul, hζ, one_pow]
  · refine (unramifiedTower_le_adjoin_rootsOfUnity p m).trans (adjoin.mono _ _ _ ?_)
    intro ζ (hζ : ζ ^ _ = 1)
    change ζ ^ _ = 1
    rw [mul_comm, pow_mul, hζ, one_pow]

theorem coprime_pow_sub_one {k : ℕ} (hk : k ≠ 0) : (p ^ k - 1).Coprime p := by
  rw [Nat.coprime_comm, hp.out.coprime_iff_not_dvd]
  intro h
  have h1 : p ∣ p ^ k := dvd_pow_self p hk
  have h2 := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.out.pos)] at h2
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h2)

omit [Algebra.IsSeparable ℚ_[p] Ω] in

theorem maximalUnramifiedExtension_eq_adjoin_rootsOfUnity :
    maximalUnramifiedExtension ℚ_[p] Ω =
      adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, 0 < n ∧ n.Coprime p ∧ ζ ^ n = 1} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨m, hm⟩ := exists_mem_unramifiedTower hx
    have h1 := unramifiedTower_le_adjoin_rootsOfUnity p m hm
    refine adjoin.mono ℚ_[p] _ _ ?_ h1
    intro ζ hζ
    have hζ' : ζ ^ (p ^ (m + 1).factorial - 1) = 1 := hζ
    have hpos : 0 < p ^ (m + 1).factorial - 1 :=
      Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.factorial_ne_zero (m + 1)) hp.out.one_lt)
    exact ⟨p ^ (m + 1).factorial - 1, hpos,
      coprime_pow_sub_one p (Nat.factorial_ne_zero (m + 1)), hζ'⟩
  · rw [adjoin_le_iff]
    rintro ζ ⟨n, hn, hcop, hζn⟩
    have hφ : n.totient ≠ 0 := (Nat.totient_pos.2 hn).ne'
    obtain ⟨ξ, hξ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := ℚ_[p]) (Ksep := Ω) hφ
    have hdvd : n ∣ p ^ n.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.out.pos)).1
        (Nat.ModEq.pow_totient hcop.symm).symm
    have hU := (isUnramifiedSubextension_adjoin hφ hξ).1
    rw [card_residueField] at hξ
    have : NeZero (p ^ n.totient - 1) := ⟨(Nat.sub_pos_of_lt
      (Nat.one_lt_pow hφ hp.out.one_lt)).ne'⟩
    obtain ⟨i, -, hi⟩ := hξ.eq_pow_of_pow_eq_one (ξ := ζ) (by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc, pow_mul, hζn, one_pow])
    rw [← hi]
    exact hU.le_maximalUnramifiedExtension (pow_mem (mem_adjoin_simple_self ℚ_[p] ξ) i)

theorem lubinTateLimit_le_adjoin_rootsOfUnity [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension ℚ_[p] Ω] :
    lubinTateLimit Ω (irreducible_natCast_integer p) ≤
      adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, ζ ^ (p ^ n) = 1} := by
  rw [lubinTateLimit_eq _ (isLubinTateSeries_multiplicativeLTPoly p)]
  exact iSup_le fun n => (lubinTateField_le_adjoin_rootsOfUnity p n).trans
    (adjoin.mono _ _ _ fun ζ (hζ : ζ ^ (p ^ n) = 1) =>
      show ∃ n : ℕ, ζ ^ (p ^ n) = 1 from ⟨n, hζ⟩)

variable (Ω) in

theorem maximalAbelianExtension_eq_adjoin_rootsOfUnity :
    maximalAbelianExtension ℚ_[p] Ω = adjoin ℚ_[p] {ζ : Ω | ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1} := by
  have : IsSepClosure ℚ_[p] Ω := ⟨inferInstance, inferInstance⟩
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
    obtain ⟨N, hN, h⟩ := exists_le_adjoin_rootsOfUnity p L
    refine (h.trans (adjoin.mono _ _ _ ?_)) hyL
    intro ζ hζ
    exact ⟨N, hN, hζ⟩
  · rw [adjoin_le_iff]
    rintro ζ ⟨n, hn, hζn⟩
    have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
    have : NeZero (orderOf ζ) := ⟨(orderOf_pos_iff.2 hfin).ne'⟩
    have hζ : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
    have := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
    have := IsCyclotomicExtension.isAbelianGalois {orderOf ζ} ℚ_[p] ℚ_[p]⟮ζ⟯
    have : FiniteDimensional ℚ_[p] ℚ_[p]⟮ζ⟯ := adjoin.finiteDimensional
      (IsIntegral.of_pow hn (by rw [hζn]; exact isIntegral_one))
    exact le_maximalAbelianExtension ℚ_[p]⟮ζ⟯ (mem_adjoin_simple_self ℚ_[p] ζ)

end Padic

end Padic

end RHDirect.CFT.LocalField
end Sec_KroneckerWeber


/-! ### LocalArtinUniqueness -/
section Sec_LocalArtinUniqueness


namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup

section Galois

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem apply_eq_self_of_mem_sup {τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    {E₁ E₂ : IntermediateField F Ω} (h₁ : E₁ ≤ maximalAbelianExtension F Ω)
    (h₂ : E₂ ≤ maximalAbelianExtension F Ω)
    (hτ₁ : ∀ (y : Ω) (hy : y ∈ E₁), ((τ ⟨y, h₁ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y)
    (hτ₂ : ∀ (y : Ω) (hy : y ∈ E₂), ((τ ⟨y, h₂ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y)
    (y : Ω) (hy : y ∈ E₁ ⊔ E₂) :
    ((τ ⟨y, sup_le h₁ h₂ hy⟩ : maximalAbelianExtension F Ω) : Ω) = y := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective ((topologicalAbelianizationEquiv F Ω).symm τ)
  have hτ : τ = topologicalAbelianizationEquiv F Ω (g : TopologicalAbelianization (Ω ≃ₐ[F] Ω)) := by
    rw [hg, ContinuousMulEquiv.apply_symm_apply]
  subst hτ
  have hg : g ∈ (E₁ ⊔ E₂).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_,
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun z hz => ?_⟩
    · have := hτ₁ z hz
      rwa [topologicalAbelianizationEquiv_mk_apply] at this
    · have := hτ₂ z hz
      rwa [topologicalAbelianizationEquiv_mk_apply] at this
  rw [topologicalAbelianizationEquiv_mk_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y hy

end Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Uniqueness

theorem monoidHom_ext_uniformizer {M : Type*} [Group M] {f g : Kˣ →* M}
    (h : ∀ {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ), f (uniformizerUnit hϖ) = g (uniformizerUnit hϖ)) :
    f = g := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hunit : ∀ u : 𝒪[K]ˣ, f (unitsIncl K u) = g (unitsIncl K u) := by
    intro u
    have huϖ : Irreducible ((u : 𝒪[K]) * ϖ) := (irreducible_units_mul u).2 hϖ
    have he : unitsIncl K u = uniformizerUnit huϖ * (uniformizerUnit hϖ)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      ext
      simp [coe_uniformizerUnit]
    rw [he, map_mul, map_mul, map_inv, map_inv, h huϖ, h hϖ]
  ext x
  set e := unitsEquivIntProd hϖ
  have hx : x = uniformizerUnit hϖ ^ Multiplicative.toAdd (e x).1 * unitsIncl K (e x).2 := by
    apply e.injective
    rw [map_mul, map_zpow, unitsEquivIntProd_uniformizer, unitsEquivIntProd_unitsIncl]
    ext
    · simp [← ofAdd_zsmul]
    · simp
  rw [hx, map_mul, map_mul, map_zpow, map_zpow, h hϖ, hunit]

theorem eq_localArtinMap_of
    {ψ : Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)}
    (hFrob : ∀ π : Kˣ, ord (π : K) = 1 →
      restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
        (ψ π) = maximalUnramifiedExtensionFrobenius K Ω)
    (hnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      ∀ x ∈ (normUnits K L).range, restrictAb L (le_maximalAbelianExtension L) (ψ x) = 1) :
    ψ = localArtinMap K Ω := by
  refine monoidHom_ext_uniformizer fun {ϖ} hϖ => ?_
  set π := uniformizerUnit hϖ
  have hπ : ord (π : K) = 1 := ord_uniformizer hϖ
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf := isLubinTateSeries_ltPoly ϖ

  have hLT : ∀ (χ : Kˣ →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω))
      (hχ : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        ∀ x ∈ (normUnits K L).range, restrictAb L (le_maximalAbelianExtension L) (χ x) = 1)
      (n : ℕ) (y : Ω) (hy : y ∈ lubinTateField Ω hϖ hf (n + 1)),
      ∃ hy' : y ∈ maximalAbelianExtension K Ω, ((χ π ⟨y, hy'⟩ : maximalAbelianExtension K Ω) : Ω) = y := by
    intro χ hχ n y hy
    have : IsAbelianGalois K (lubinTateField Ω hϖ hf (n + 1)) :=
      isAbelianGalois_of_mul_comm _ (lubinTateField_mul_comm hϖ hf (n + 1))
    refine ⟨le_maximalAbelianExtension _ hy, ?_⟩
    obtain ⟨z, hz⟩ := exists_norm_eq_uniformizer (Ω := Ω) hϖ hf n.succ_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hz
      exact coe_ne_zero_of_irreducible hϖ hz.symm
    have hmem : π ∈ (normUnits K (lubinTateField Ω hϖ hf (n + 1))).range :=
      ⟨Units.mk0 z hz0, Units.ext (by simpa [π, coe_uniformizerUnit] using hz)⟩
    have := congrArg (fun ρ : lubinTateField Ω hϖ hf (n + 1) ≃ₐ[K] lubinTateField Ω hϖ hf (n + 1) =>
      ((ρ ⟨y, hy⟩ : lubinTateField Ω hϖ hf (n + 1)) : Ω)) (hχ _ π hmem)
    simpa only [restrictAb_apply, AlgEquiv.one_apply] using this
  have hφnorm : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      ∀ x ∈ (normUnits K L).range,
        restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) = 1 := by
    intro L _ _ x hx
    rw [← MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_restrictAb_localArtinMap]
    exact hx
  have hur : ∀ (y : Ω) (hy : y ∈ maximalUnramifiedExtension K Ω),
      ((ψ π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
        maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K Ω π ⟨y, maximalUnramifiedExtension_le_maximalAbelianExtension hy⟩ :
        maximalAbelianExtension K Ω) : Ω) := by
    intro y hy
    have h1 := congrArg (fun ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω =>
      ((ρ ⟨y, hy⟩ : maximalUnramifiedExtension K Ω) : Ω)) (hFrob π hπ)
    have h2 := congrArg (fun ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω =>
      ((ρ ⟨y, hy⟩ : maximalUnramifiedExtension K Ω) : Ω)) (restrictAb_localArtinMap_uniformizer (Ω := Ω) hπ)
    simp only [restrictAb_apply] at h1 h2
    rw [h1, h2]

  set τ := (ψ π)⁻¹ * localArtinMap K Ω π
  have hτ1 : τ = 1 := by
    refine ext_restrictAb fun L _ _ => ?_
    obtain ⟨n, m, hLM⟩ := exists_le_lubinTateField_sup_unramifiedTower hϖ hf L
    have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
    have hM := isAbelianGalois_lubinTateField_sup hϖ hf n.succ_pos hE
    have h₁ : lubinTateField Ω hϖ hf (n + 1) ≤ maximalAbelianExtension K Ω :=
      (le_sup_left : lubinTateField Ω hϖ hf (n + 1) ≤
        lubinTateField Ω hϖ hf (n + 1) ⊔ unramifiedTower K Ω m).trans (le_maximalAbelianExtension _)
    have h₂ : unramifiedTower K Ω m ≤ maximalAbelianExtension K Ω :=
      (le_sup_right : unramifiedTower K Ω m ≤ lubinTateField Ω hϖ hf (n + 1) ⊔ _).trans
        (le_maximalAbelianExtension _)
    have hfix := apply_eq_self_of_mem_sup (τ := τ) h₁ h₂ (fun y hy => ?_) (fun y hy => ?_)
    · ext y
      rw [restrictAb_apply, map_one, AlgEquiv.one_apply]
      exact hfix y (hLM y.2)
    · obtain ⟨hy₁, hψ⟩ := hLT ψ hnorm n y hy
      obtain ⟨hy₂, hφ⟩ := hLT (localArtinMap K Ω) hφnorm n y hy
      simp only [τ, AlgEquiv.mul_apply]
      have : (localArtinMap K Ω π ⟨y, h₁ hy⟩) = ⟨y, h₁ hy⟩ := Subtype.ext hφ
      have h1 : (ψ π).symm ⟨y, h₁ hy⟩ = ⟨y, h₁ hy⟩ :=
        (AlgEquiv.symm_apply_eq _).2 (Subtype.ext hψ).symm
      rw [this, AlgEquiv.aut_inv, h1]
    · have hyur : y ∈ maximalUnramifiedExtension K Ω := unramifiedTower_le_maximalUnramifiedExtension m hy
      have h := hur y hyur
      simp only [τ, AlgEquiv.mul_apply]
      have h1 : (ψ π).symm (localArtinMap K Ω π ⟨y, h₂ hy⟩) = ⟨y, h₂ hy⟩ :=
        (AlgEquiv.symm_apply_eq _).2 (Subtype.ext h).symm
      rw [AlgEquiv.aut_inv, h1]
  rw [← inv_mul_eq_one]
  exact hτ1

end Uniqueness

end RHDirect.CFT.LocalField
end Sec_LocalArtinUniqueness


/-! ### LocalArtinBaseChange -/
section Sec_LocalArtinBaseChange


namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

section Galois

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (E : IntermediateField K Ω)

def restrictScalarsHom : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[K] Ω) :=
  (E.fixingSubgroup.subtype).comp (IntermediateField.fixingSubgroupEquiv E).symm.toMonoidHom

@[simp]
theorem restrictScalarsHom_apply (σ : Ω ≃ₐ[E] Ω) (x : Ω) : restrictScalarsHom E σ x = σ x :=
  rfl

variable [FiniteDimensional K E]

theorem continuous_restrictScalarsHom : Continuous (restrictScalarsHom (K := K) (Ω := Ω) E) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
  have : FiniteDimensional K (M ⊔ E : IntermediateField K Ω) := inferInstance
  have : FiniteDimensional E (IntermediateField.extendScalars (le_sup_right : E ≤ M ⊔ E)) :=
    finiteDimensional_extendScalars _
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.extendScalars (le_sup_right : E ≤ M ⊔ E), inferInstance, fun σ hσ => ?_⟩
  apply hMs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x
    ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := M) (b := E) hx))

variable [IsGalois K Ω]

def fixingSubgroupHomeomorph :
    ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃ₜ* (Ω ≃ₐ[E] Ω) :=
  have : T2Space (Ω ≃ₐ[K] Ω) := krullTopology_t2
  let e := (IntermediateField.fixingSubgroupEquiv E).symm.trans
    (MulEquiv.subgroupCongr (coe_fixingOpenSubgroup E).symm)
  have hc : Continuous e :=
    Continuous.subtype_mk (continuous_restrictScalarsHom E) fun σ => (e σ).2
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := hc
      continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

@[simp]
theorem fixingSubgroupHomeomorph_apply
    (σ : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) (x : Ω) :
    fixingSubgroupHomeomorph E σ x = (σ : Ω ≃ₐ[K] Ω) x :=
  rfl

omit [IsGalois K Ω] in

theorem maximalAbelianExtension_le_restrictScalars :
    maximalAbelianExtension K Ω ≤ (maximalAbelianExtension E Ω).restrictScalars K := by
  intro y hy
  rw [IntermediateField.mem_restrictScalars]
  change y ∈ IntermediateField.fixedField _
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  have hle : (commutator (Ω ≃ₐ[E] Ω)).topologicalClosure ≤
      (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure.comap (restrictScalarsHom E) := by
    refine Subgroup.topologicalClosure_minimal _ ?_
      ((Subgroup.isClosed_topologicalClosure _).preimage (continuous_restrictScalarsHom E))
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.le_topologicalClosure _
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact (IntermediateField.mem_fixedField_iff _ _).1 hy _ (hle hg)

end Galois

section Data

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]

instance isSepClosure_intermediateField (E : IntermediateField K Ω) : IsSepClosure E Ω :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ω⟩

variable (E : IntermediateField K Ω) [FiniteDimensional K E]

variable (K) in

def unitsEquivFixingOpen :
    fixedModule Ωˣ ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ≃* Eˣ :=
  unitsEquivOfForall _ E
    (mem_iff_forall_of_fixingSubgroup_eq ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
      Subgroup (Ω ≃ₐ[K] Ω)) rfl)

theorem relDeg_fixingOpenSubgroup
    (σ : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) σ =
      unramifiedDegree E Ω (fixingSubgroupHomeomorph E σ) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hi : inertiaDegree (unramifiedDegree K Ω)
      ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = residueDegree K E :=
    inertiaDegree_unramifiedDegree_fixingSubgroup E
  rw [ClassFieldData.relDeg_eq_iff, localClassFieldData_deg, hi]
  exact unramifiedDegree_fixingSubgroup E σ

theorem valuation_fixingOpenSubgroup
    (a : fixedModule Ωˣ ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :
    (localClassFieldData K Ω).valuation (fixingOpenSubgroup E) a =
      Multiplicative.ofAdd ((ord ((unitsEquivFixingOpen K E a : Eˣ) : E) : ℤ) : ℤ̂) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hf : residueDegree K E ≠ 0 := (residueDegree_pos K E).ne'
  have h := (localClassFieldData K Ω).valuation_pow (fixingOpenSubgroup E) a
  have hi : inertiaDegree (unramifiedDegree K Ω)
      ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = residueDegree K E :=
    inertiaDegree_unramifiedDegree_fixingSubgroup E
  rw [localClassFieldData_deg, hi, localClassFieldData_val, localValuation_apply] at h
  have : (E.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  erw [baseUnitsEquiv_norm E a] at h
  rw [← RHDirect.CFT_AbstractLocalReciprocity.ProfiniteInteger.pow_left_inj hf, h]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ordUnitsHom, coe_normUnits, ord_norm, toAdd_pow, toAdd_ofAdd, Int.cast_mul,
    Int.cast_natCast, nsmul_eq_mul]
  rfl

end Data

section Limit

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  [FiniteDimensional K E] in
theorem le_restrictScalars (L : IntermediateField E Ω) : E ≤ L.restrictScalars K := fun x hx => by
  rw [IntermediateField.mem_restrictScalars]
  exact L.algebraMap_mem ⟨x, hx⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  [FiniteDimensional K E] in
theorem extendScalars_restrictScalars' (L : IntermediateField E Ω) :
    IntermediateField.extendScalars (le_restrictScalars E L) = L := by
  ext x
  rw [IntermediateField.mem_extendScalars, IntermediateField.mem_restrictScalars]

variable (K) in

def baseChangeArtinMap : Eˣ →* (maximalAbelianExtension E Ω ≃ₐ[E] maximalAbelianExtension E Ω) :=
  (topologicalAbelianizationEquiv E Ω).toMulEquiv.toMonoidHom.comp
    ((topologicalAbelianizationMap (fixingSubgroupHomeomorph E).toMulEquiv.toMonoidHom
      (fixingSubgroupHomeomorph E).continuous).comp
      (((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E)).comp
        (unitsEquivFixingOpen K E).symm.toMonoidHom))

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem baseChangeArtinMap_apply (x : Eˣ)
    (g : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)))
    (hg : (QuotientGroup.mk g : TopologicalAbelianization _) =
      (localClassFieldData K Ω).reciprocityLimit
      (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) ((unitsEquivFixingOpen K E).symm x))
    (y : maximalAbelianExtension E Ω) :
    ((baseChangeArtinMap K E x y : maximalAbelianExtension E Ω) : Ω) = (g : Ω ≃ₐ[K] Ω) y := by
  have h : baseChangeArtinMap K E x = topologicalAbelianizationEquiv E Ω
      (topologicalAbelianizationMap (fixingSubgroupHomeomorph E).toMulEquiv.toMonoidHom
        (fixingSubgroupHomeomorph E).continuous ((localClassFieldData K Ω).reciprocityLimit
          (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) ((unitsEquivFixingOpen K E).symm x))) :=
    rfl
  rw [h, ← hg]
  change ((topologicalAbelianizationEquiv E Ω
    (QuotientGroup.mk (fixingSubgroupHomeomorph E g) : TopologicalAbelianization (Ω ≃ₐ[E] Ω)) y :
      maximalAbelianExtension E Ω) : Ω) = _
  rw [topologicalAbelianizationEquiv_mk_apply]
  rfl

end Limit

section Properties

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in
variable {E} in

theorem isAbelianExtension_fixingOpenSubgroup_of_le {F : IntermediateField K Ω} (h : E ≤ F)
    [FiniteDimensional K F] [IsAbelianGalois E (IntermediateField.extendScalars h)] :
    IsAbelianExtension (fixingOpenSubgroup E) (fixingOpenSubgroup F) := by
  refine ⟨fixingOpenSubgroup_anti h, ?_⟩
  let r : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) →*
      (IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h) :=
    (AlgEquiv.restrictNormalHom (IntermediateField.extendScalars h)).comp
      (fixingSubgroupHomeomorph E).toMulEquiv.toMonoidHom
  refine (commutator_le_ker_of_comm r).trans fun σ hσ => ?_
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_subgroupOf, coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have := congrArg (fun ρ : IntermediateField.extendScalars h ≃ₐ[E] IntermediateField.extendScalars h =>
    ((ρ ⟨y, (IntermediateField.mem_extendScalars h).2 hy⟩ : IntermediateField.extendScalars h) : Ω)) hσ
  simp only [r] at this
  rw [MonoidHom.comp_apply, AlgEquiv.restrictNormalHom_apply] at this
  exact this

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in
variable {E} in

theorem restrictAb_baseChangeArtinMap_eq_one {F : IntermediateField K Ω} (h : E ≤ F)
    [FiniteDimensional K F] [IsAbelianGalois E (IntermediateField.extendScalars h)] (x : Eˣ)
    (hx : x ∈ (normUnits E (IntermediateField.extendScalars h)).range) :
    restrictAb (IntermediateField.extendScalars h) (le_maximalAbelianExtension _)
      (baseChangeArtinMap K E x) = 1 := by
  have hUV := isAbelianExtension_fixingOpenSubgroup_of_le h
  have := hUV.normal
  set a := (unitsEquivFixingOpen K E).symm x with ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)
  have hna : a ∈ (norm Ωˣ ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))
      ((fixingOpenSubgroup F : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).range := by
    rw [← map_unitsEquivOfForall_range_norm h (fixingOpenSubgroup E) (fixingOpenSubgroup F) rfl rfl]
      at hx
    obtain ⟨c, hc, hcx⟩ := hx
    have : c = a := by
      rw [ha, MulEquiv.eq_symm_apply]
      exact hcx
    rwa [← this]
  have h1 : abelianizationRestrict hUV
      ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a) = 1 := by
    rw [ClassFieldData.abelianizationRestrict_reciprocityLimit, MulEquiv.map_eq_one_iff,
      QuotientGroup.eq_one_iff]
    exact hna
  rw [← hg, abelianizationRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff] at h1
  ext y
  rw [restrictAb_apply, baseChangeArtinMap_apply E x g hg, AlgEquiv.one_apply]
  exact h1 y ((IntermediateField.mem_extendScalars h).1 y.2)

end Properties

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  [FiniteDimensional K E] in
theorem abelianization_of_injective_of_comm {G : Type*} [Group G] [IsMulCommutative G] :
    Function.Injective (Abelianization.of : G →* Abelianization G) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  rw [← MonoidHom.mem_ker, Abelianization.ker_of, commutator,
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at hσ
  exact hσ

theorem restrictAb_baseChangeArtinMap_uniformizer {ϖ : Eˣ} (hϖ : ord (ϖ : E) = 1) :
    restrictAb (maximalUnramifiedExtension E Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
      (baseChangeArtinMap K E ϖ) = maximalUnramifiedExtensionFrobenius E Ω := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  ext ⟨y, hy⟩
  obtain ⟨E', hE', hyE'⟩ := (mem_maximalUnramifiedExtension_iff (K := E)).1 hy
  obtain ⟨F, h, rfl⟩ : ∃ (F : IntermediateField K Ω) (h : E ≤ F),
      E' = IntermediateField.extendScalars h :=
    ⟨_, _, (extendScalars_restrictScalars' E E').symm⟩
  have := hE'.1
  have := hE'.isGalois
  have hEur := hE'.le_maximalUnramifiedExtension
  have : IsAbelianGalois E (IntermediateField.extendScalars h) :=
    isAbelianGalois_of_le_maximalAbelianExtension _
      (hEur.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
  have : FiniteDimensional K F :=
    (FiniteDimensional.trans K E (IntermediateField.extendScalars h) :)
  have hUV := isAbelianExtension_fixingOpenSubgroup_of_le h
  have := hUV.normal
  have hmc := hUV.isMulCommutative

  set σ₀ : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) :=
    (fixingSubgroupHomeomorph E).symm ((maximalUnramifiedExtensionFrobenius E Ω).liftNormal Ω) with hσ₀
  have hφ : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) σ₀ = Multiplicative.ofAdd 1 := by
    rw [relDeg_fixingOpenSubgroup, hσ₀, ContinuousMulEquiv.apply_symm_apply]
    exact (restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff _).1
      (AlgEquiv.restrict_liftNormal _ _)
  have hu : ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⊓
      (localClassFieldData K Ω).deg.ker ≤ (fixingOpenSubgroup F : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rintro τ ⟨hτU, hτ⟩
    replace hτ : (localClassFieldData K Ω).deg τ = 1 := hτ
    have h1 : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) ⟨τ, hτU⟩ = 1 := by
      rw [ClassFieldData.relDeg_eq_iff, one_pow]
      exact hτ
    rw [relDeg_fixingOpenSubgroup, unramifiedDegree_eq_one_iff] at h1
    rw [coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hz' : z ∈ maximalUnramifiedExtension E Ω := hEur ((IntermediateField.mem_extendScalars h).2 hz)
    have := (ker_unramifiedDegree (K := E) (Ω := Ω)) ▸ (MonoidHom.mem_ker.2
      ((unramifiedDegree_eq_one_iff _).2 h1))
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this z hz'
  set a := (unitsEquivFixingOpen K E).symm ϖ with ha
  have hval : (localClassFieldData K Ω).valuation (fixingOpenSubgroup E) a =
      Multiplicative.ofAdd ((1 : ℤ) : ℤ̂) := by
    rw [valuation_fixingOpenSubgroup, ha, MulEquiv.apply_symm_apply, hϖ]
  have key := (localClassFieldData K Ω).reciprocityAbEquiv_symm_of_unramified_of_valuation hUV.le
    (classFieldAxiom_units K Ω) hu hφ a 1 hval
  have hq : Abelianization.of (abelianizationRestrict hUV
      ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)) =
      ((localClassFieldData K Ω).reciprocityAbEquiv hUV.le (classFieldAxiom_units K Ω)).symm
        (a : tateZero Ωˣ _ _) := by
    rw [MulEquiv.eq_symm_apply, ClassFieldData.reciprocityAbEquiv_of,
      (localClassFieldData K Ω).abelianizationRestrict_reciprocityLimit (classFieldAxiom_units K Ω) hUV,
      ← (localClassFieldData K Ω).reciprocityAbelianEquiv_apply (classFieldAxiom_units K Ω) hUV,
      MulEquiv.apply_symm_apply]
  rw [key, zpow_one] at hq
  have hq' := abelianization_of_injective_of_comm hq
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)
  rw [← hg, abelianizationRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    coe_fixingOpenSubgroup, IntermediateField.mem_fixingSubgroup_iff] at hq'
  have hyF : y ∈ F := (IntermediateField.mem_extendScalars h).1 hyE'
  have e1 := hq' y hyF
  rw [restrictAb_apply, baseChangeArtinMap_apply E ϖ g hg]
  change (g : Ω ≃ₐ[K] Ω) y = _
  have e2 : ((σ₀ : Ω ≃ₐ[K] Ω) y) = ((maximalUnramifiedExtensionFrobenius E Ω
      (⟨y, hy⟩ : maximalUnramifiedExtension E Ω) : maximalUnramifiedExtension E Ω) : Ω) := by
    rw [← fixingSubgroupHomeomorph_apply, hσ₀, ContinuousMulEquiv.apply_symm_apply]
    exact AlgEquiv.liftNormal_commutes _ Ω (⟨y, hy⟩ : maximalUnramifiedExtension E Ω)
  have e3 : (g : Ω ≃ₐ[K] Ω) y = (σ₀ : Ω ≃ₐ[K] Ω) y := by
    have := congrArg (g : Ω ≃ₐ[K] Ω) e1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
      AlgEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e3, e2]

end Frobenius

section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

theorem baseChangeArtinMap_eq : baseChangeArtinMap K E = localArtinMap E Ω := by
  refine eq_localArtinMap_of (fun π hπ => restrictAb_baseChangeArtinMap_uniformizer E hπ) ?_
  intro L _ _ x hx
  obtain ⟨F, h, rfl⟩ : ∃ (F : IntermediateField K Ω) (h : E ≤ F),
      L = IntermediateField.extendScalars h :=
    ⟨_, _, (extendScalars_restrictScalars' E L).symm⟩
  have : FiniteDimensional K F :=
    (FiniteDimensional.trans K E (IntermediateField.extendScalars h) :)
  exact restrictAb_baseChangeArtinMap_eq_one h x hx

theorem localArtinMap_apply_of_mem (x : Eˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap E Ω x ⟨y, maximalAbelianExtension_le_restrictScalars E hy⟩ :
      maximalAbelianExtension E Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K E x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  rw [← baseChangeArtinMap_eq]
  set a := (unitsEquivFixingOpen K E).symm x with ha
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective
    ((localClassFieldData K Ω).reciprocityLimit (classFieldAxiom_units K Ω) (fixingOpenSubgroup E) a)
  rw [baseChangeArtinMap_apply E x g hg]
  have hE : (E.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup E : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  have hN : normUnits K E x = baseUnitsEquiv (norm Ωˣ ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
      Subgroup (Ω ≃ₐ[K] Ω)) ((fixingOpenSubgroup E : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
        Subgroup (Ω ≃ₐ[K] Ω)) a) := by
    erw [baseUnitsEquiv_norm E a]
    congr 1
  have hlim := (localClassFieldData K Ω).limitRestrict_reciprocityLimit (classFieldAxiom_units K Ω)
    (le_top : fixingOpenSubgroup E ≤ ⊤) a
  rw [← hg, limitRestrict_mk] at hlim
  rw [hN, localArtinMap_apply, localReciprocityLimit_baseUnitsEquiv, ← hlim, topAbelianizationEquiv_mk,
    topologicalAbelianizationEquiv_mk_apply]

end Functoriality

section Relative

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {E : IntermediateField K Ω} [FiniteDimensional K E]

attribute [local instance] isDiscreteModule_units

end Relative

end RHDirect.CFT.LocalField
end Sec_LocalArtinBaseChange


/-! ### LocalArtinTransport -/
section Sec_LocalArtinTransport


namespace RHDirect.CFT.LocalField

open ValuativeRel

section Semilinear

variable {K K' A B : Type*} [Field K] [Field K'] [Field A] [Field B] [Algebra K A] [Algebra K' B]
  (e : K ≃+* K') (f : A ≃+* B) (hf : ∀ x : K, f (algebraMap K A x) = algebraMap K' B (e x))

include hf in
theorem symm_algebraMap_transport (x : K') : f.symm (algebraMap K' B x) = algebraMap K A (e.symm x) := by
  rw [RingEquiv.symm_apply_eq, hf, RingEquiv.apply_symm_apply]

include hf in
theorem comp_algebraMap_transport :
    (algebraMap K' B).comp e.toRingHom = (f : A →+* B).comp (algebraMap K A) := by
  ext x
  exact (hf x).symm

def galTransport : (A ≃ₐ[K] A) ≃* (B ≃ₐ[K'] B) where
  toFun σ :=
    { (f.symm.trans σ.toRingEquiv).trans f with
      commutes' := fun c => by
        simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingEquiv.coe_trans, Function.comp_apply, symm_algebraMap_transport e f hf,
          AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, hf, RingEquiv.apply_symm_apply] }
  invFun τ :=
    { (f.trans τ.toRingEquiv).trans f.symm with
      commutes' := fun c => by
        simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
          RingEquiv.coe_trans, Function.comp_apply, hf, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
          symm_algebraMap_transport e f hf, RingEquiv.symm_apply_apply] }
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' _ _ := by ext; simp

theorem galTransport_apply (σ : A ≃ₐ[K] A) (a : A) : galTransport e f hf σ (f a) = f (σ a) := by
  simp [galTransport]

include e f hf in
theorem isMulCommutative_transport [IsMulCommutative (A ≃ₐ[K] A)] :
    IsMulCommutative (B ≃ₐ[K'] B) :=
  ⟨⟨fun σ τ => by
    obtain ⟨σ', rfl⟩ := (galTransport e f hf).surjective σ
    obtain ⟨τ', rfl⟩ := (galTransport e f hf).surjective τ
    rw [← map_mul, ← map_mul, mul_comm' σ' τ']⟩⟩

include e f hf in
theorem finiteDimensional_transport [FiniteDimensional K A] : FiniteDimensional K' B :=
  Module.Finite.of_equiv_equiv e f (comp_algebraMap_transport e f hf)

include e f hf in
theorem isGalois_transport [IsGalois K A] : IsGalois K' B :=
  IsGalois.of_equiv_equiv (comp_algebraMap_transport e f hf)

include e f hf in
theorem isAbelianGalois_transport [IsAbelianGalois K A] : IsAbelianGalois K' B :=
  have := isGalois_transport e f hf
  { toIsMulCommutative := isMulCommutative_transport e f hf }

include hf in
theorem norm_transport (a : A) : e (Algebra.norm K a) = Algebra.norm K' (f a) := by
  rw [Algebra.norm_eq_of_equiv_equiv e f (comp_algebraMap_transport e f hf), RingEquiv.apply_symm_apply]

end Semilinear

section IntermediateFieldTransport

variable {K K' Ω Ω' : Type*} [Field K] [Field K'] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω']
  (e : K ≃+* K') (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x))

def transportField (M : IntermediateField K Ω) : IntermediateField K' Ω' :=
  (M.toSubfield.map (ε : Ω →+* Ω')).toIntermediateField fun x =>
    ⟨algebraMap K Ω (e.symm x), M.algebraMap_mem _, by
      change ε (algebraMap K Ω (e.symm x)) = _
      rw [hε, e.apply_symm_apply]⟩

theorem mem_transportField {M : IntermediateField K Ω} {y : Ω'} :
    y ∈ transportField e ε hε M ↔ ε.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ε.symm (ε x) ∈ M
    rw [RingEquiv.symm_apply_apply]
    exact hx
  · intro h
    exact ⟨_, h, ε.apply_symm_apply y⟩

theorem apply_mem_transportField {M : IntermediateField K Ω} {x : Ω} :
    ε x ∈ transportField e ε hε M ↔ x ∈ M := by
  rw [mem_transportField, RingEquiv.symm_apply_apply]

def transportFieldEquiv (M : IntermediateField K Ω) : M ≃+* transportField e ε hε M where
  toFun x := ⟨ε x, (apply_mem_transportField e ε hε).2 x.2⟩
  invFun y := ⟨ε.symm y, (mem_transportField e ε hε).1 y.2⟩
  left_inv _ := Subtype.ext (ε.symm_apply_apply _)
  right_inv _ := Subtype.ext (ε.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul ε _ _)
  map_add' _ _ := Subtype.ext (map_add ε _ _)

@[simp]
theorem coe_transportFieldEquiv (M : IntermediateField K Ω) (x : M) :
    (transportFieldEquiv e ε hε M x : Ω') = ε x :=
  rfl

theorem transportFieldEquiv_algebraMap (M : IntermediateField K Ω) (x : K) :
    transportFieldEquiv e ε hε M (algebraMap K M x) = algebraMap K' (transportField e ε hε M) (e x) :=
  Subtype.ext (hε x)

theorem isAbelianGalois_transportField (M : IntermediateField K Ω) [IsAbelianGalois K M] :
    IsAbelianGalois K' (transportField e ε hε M) :=
  isAbelianGalois_transport e (transportFieldEquiv e ε hε M) (transportFieldEquiv_algebraMap e ε hε M)

theorem finiteDimensional_transportField (M : IntermediateField K Ω) [FiniteDimensional K M] :
    FiniteDimensional K' (transportField e ε hε M) :=
  finiteDimensional_transport e (transportFieldEquiv e ε hε M) (transportFieldEquiv_algebraMap e ε hε M)

theorem norm_transportField (M : IntermediateField K Ω) (z : M) :
    e (Algebra.norm K z) = Algebra.norm K' (transportFieldEquiv e ε hε M z) :=
  norm_transport e (transportFieldEquiv e ε hε M) (transportFieldEquiv_algebraMap e ε hε M) z

variable [IsGalois K Ω] [IsGalois K' Ω']

include hε in
theorem apply_mem_maximalAbelianExtension {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ε y ∈ maximalAbelianExtension K' Ω' := by
  obtain ⟨L, _, _, hyL⟩ := exists_finite_abelian_mem hy
  have := isAbelianGalois_transportField e ε hε L
  exact le_maximalAbelianExtension _ ((apply_mem_transportField e ε hε).2 hyL)

include hε in

theorem mem_maximalAbelianExtension_transport_iff {y : Ω} :
    ε y ∈ maximalAbelianExtension K' Ω' ↔ y ∈ maximalAbelianExtension K Ω := by
  refine ⟨fun h => ?_, apply_mem_maximalAbelianExtension e ε hε⟩
  have := apply_mem_maximalAbelianExtension e.symm ε.symm (symm_algebraMap_transport e ε hε) h
  rwa [RingEquiv.symm_apply_apply] at this

theorem transportField_maximalAbelianExtension :
    transportField e ε hε (maximalAbelianExtension K Ω) = maximalAbelianExtension K' Ω' := by
  ext y
  rw [mem_transportField, ← mem_maximalAbelianExtension_transport_iff e ε hε, RingEquiv.apply_symm_apply]

def maximalAbelianExtensionTransport :
    maximalAbelianExtension K Ω ≃+* maximalAbelianExtension K' Ω' :=
  (transportFieldEquiv e ε hε _).trans
    (IntermediateField.equivOfEq (transportField_maximalAbelianExtension e ε hε)).toRingEquiv

@[simp]
theorem coe_maximalAbelianExtensionTransport (y : maximalAbelianExtension K Ω) :
    (maximalAbelianExtensionTransport e ε hε y : Ω') = ε y :=
  rfl

theorem maximalAbelianExtensionTransport_algebraMap (x : K) :
    maximalAbelianExtensionTransport e ε hε (algebraMap K _ x) = algebraMap K' _ (e x) :=
  Subtype.ext (hε x)

end IntermediateFieldTransport

section Valuation

variable {K K' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] in
include he in
theorem symm_vle_iff (x y : K') : e.symm x ≤ᵥ e.symm y ↔ x ≤ᵥ y := by
  rw [← he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] in
include he in
theorem apply_mem_integer_iff (x : K) : e x ∈ 𝒪[K'] ↔ x ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← (valuation K').vle_one_iff,
    ← (valuation K).vle_one_iff, ← map_one e, he]

def integerEquivOfVle : 𝒪[K] ≃+* 𝒪[K'] where
  toFun x := ⟨e x, (apply_mem_integer_iff e he x).2 x.2⟩
  invFun y := ⟨e.symm y, by rw [← apply_mem_integer_iff e he, RingEquiv.apply_symm_apply]; exact y.2⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  map_add' _ _ := Subtype.ext (map_add e _ _)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] in
@[simp]
theorem coe_integerEquivOfVle (x : 𝒪[K]) : (integerEquivOfVle e he x : K') = e x :=
  rfl

def residueFieldEquivOfVle : 𝓀[K] ≃+* 𝓀[K'] :=
  IsLocalRing.ResidueField.mapEquiv (integerEquivOfVle e he)

include he in

theorem card_residueField_eq_of_vle : Nat.card 𝓀[K'] = Nat.card 𝓀[K] :=
  (Nat.card_congr (residueFieldEquivOfVle e he).toEquiv).symm

include he in
theorem natCast_residueField_ne_zero_iff (m : ℕ) : (m : 𝓀[K']) ≠ 0 ↔ (m : 𝓀[K]) ≠ 0 := by
  rw [← map_natCast (residueFieldEquivOfVle e he), Ne, map_eq_zero_iff _ (residueFieldEquivOfVle e he).injective]

include he in

theorem ord_apply_of_vle (x : Kˣ) : ord (e (x : K)) = ord (x : K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ' : Irreducible (integerEquivOfVle e he ϖ) :=
    (MulEquiv.irreducible_iff (f := (integerEquivOfVle e he).toMulEquiv) (x := ϖ)).2 hϖ
  set p := unitsEquivIntProd hϖ x
  have hx : (x : K) = (ϖ : K) ^ Multiplicative.toAdd p.1 * ((p.2 : 𝒪[K]) : K) := by
    rw [← coe_unitsOfIntProd hϖ, ← unitsEquivIntProd_symm_apply, MulEquiv.symm_apply_apply]
  set y : K'ˣ := unitsOfIntProd hϖ' (p.1, Units.map (integerEquivOfVle e he).toMonoidHom p.2)
  have hy : e (x : K) = (y : K') := by
    rw [coe_unitsOfIntProd, hx, map_mul, map_zpow₀]
    rfl
  have h2 : (unitsEquivIntProd hϖ' y).1 = p.1 := by
    change ((unitsEquivIntProd hϖ') ((unitsEquivIntProd hϖ').symm _)).1 = _
    rw [MulEquiv.apply_symm_apply]
  rw [unitsEquivIntProd_fst] at h2
  rw [hy]
  exact Multiplicative.ofAdd.injective (h2.trans (unitsEquivIntProd_fst hϖ x))

end Valuation

section Main

variable {K K' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω'] [IsSepClosure K Ω]
  [IsSepClosure K' Ω']
  (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)
  (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x))

include he hε in
theorem apply_mem_maximalUnramifiedExtension_of_vle {y : Ω}
    (hy : y ∈ maximalUnramifiedExtension K Ω) : ε y ∈ maximalUnramifiedExtension K' Ω' := by
  rw [maximalUnramifiedExtension_eq_adjoin] at hy ⊢
  have hS : unramifiedRoots K Ω ⊆ (transportField e.symm ε.symm (symm_algebraMap_transport e ε hε)
      (IntermediateField.adjoin K' (unramifiedRoots K' Ω')) : Set Ω) := by
    intro ξ hξ
    rw [SetLike.mem_coe, mem_transportField, RingEquiv.symm_symm]
    apply IntermediateField.subset_adjoin
    obtain ⟨m, hm, hξm⟩ := mem_unramifiedRoots_iff.1 hξ
    exact mem_unramifiedRoots_iff.2 ⟨m, (natCast_residueField_ne_zero_iff e he m).2 hm, by
      rw [← map_pow, hξm, map_one]⟩
  have := (IntermediateField.adjoin_le_iff.2 hS) hy
  rwa [mem_transportField, RingEquiv.symm_symm] at this

variable (K Ω) in

def transportedArtinMap :
    K'ˣ →* (maximalAbelianExtension K' Ω' ≃ₐ[K'] maximalAbelianExtension K' Ω') :=
  (galTransport e (maximalAbelianExtensionTransport e ε hε)
    (maximalAbelianExtensionTransport_algebraMap e ε hε)).toMonoidHom.comp
      ((localArtinMap K Ω).comp (Units.map e.symm.toRingHom.toMonoidHom))

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] in
theorem transportedArtinMap_apply (x' : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((transportedArtinMap K Ω e ε hε x'
      ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
        maximalAbelianExtension K' Ω') : Ω') =
      ε ((localArtinMap K Ω (Units.map e.symm.toRingHom.toMonoidHom x') ⟨y, hy⟩ :
        maximalAbelianExtension K Ω) : Ω) := by
  have h := galTransport_apply e (maximalAbelianExtensionTransport e ε hε)
    (maximalAbelianExtensionTransport_algebraMap e ε hε)
    (localArtinMap K Ω (Units.map e.symm.toRingHom.toMonoidHom x')) ⟨y, hy⟩
  exact congrArg Subtype.val h

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] in
theorem transportedArtinMap_apply' (x' : K'ˣ) {y' : Ω'}
    (hy' : y' ∈ maximalAbelianExtension K' Ω') :
    ((transportedArtinMap K Ω e ε hε x' ⟨y', hy'⟩ : maximalAbelianExtension K' Ω') : Ω') =
      ε ((localArtinMap K Ω (Units.map e.symm.toRingHom.toMonoidHom x')
        ⟨ε.symm y', (mem_maximalAbelianExtension_transport_iff e ε hε).1
          (by rwa [RingEquiv.apply_symm_apply])⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have h := transportedArtinMap_apply e ε hε x'
    ((mem_maximalAbelianExtension_transport_iff e ε hε).1 (by rwa [RingEquiv.apply_symm_apply] :
      ε (ε.symm y') ∈ maximalAbelianExtension K' Ω'))
  simp only [RingEquiv.apply_symm_apply] at h
  exact h

include he in

theorem transportedArtinMap_eq : transportedArtinMap K Ω e ε hε = localArtinMap K' Ω' := by
  have he' := symm_vle_iff e he
  have hε' := symm_algebraMap_transport e ε hε
  refine eq_localArtinMap_of (fun π' hπ' => ?_) (fun L' _ _ x' hx' => ?_)
  ·
    set π : Kˣ := Units.map e.symm.toRingHom.toMonoidHom π'
    have hπ : ord (π : K) = 1 := by
      rw [← hπ', ← ord_apply_of_vle e.symm he' π']
      rfl
    rw [eq_maximalUnramifiedExtensionFrobenius_iff]
    intro ξ hξ
    obtain ⟨m, hm, hξm⟩ := mem_unramifiedRoots_iff.1 hξ
    apply Subtype.ext
    rw [restrictAb_apply, transportedArtinMap_apply']
    have hur : ε.symm (ξ : Ω') ∈ maximalUnramifiedExtension K Ω := by
      have := apply_mem_maximalUnramifiedExtension_of_vle e.symm he' ε.symm hε' ξ.2
      exact this
    have h1 := localArtinMap_uniformizer_apply (Ω := Ω) hπ hur
    have hm' : (m : 𝓀[K]) ≠ 0 := (natCast_residueField_ne_zero_iff e he m).1 hm
    have hpow : (⟨ε.symm (ξ : Ω'), hur⟩ : maximalUnramifiedExtension K Ω) ^ m = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hξm
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this ⊢
      rw [← map_pow, this, map_one]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm' hpow] at h1
    rw [show (⟨ε.symm (ξ : Ω'), _⟩ : maximalAbelianExtension K Ω) =
      ⟨ε.symm (ξ : Ω'), maximalUnramifiedExtension_le_maximalAbelianExtension hur⟩ from rfl, h1]
    simp only [SubmonoidClass.coe_pow, map_pow, RingEquiv.apply_symm_apply,
      card_residueField_eq_of_vle e he]
  ·
    set L := transportField e.symm ε.symm hε' L'
    have : FiniteDimensional K L := finiteDimensional_transportField e.symm ε.symm hε' L'
    have : IsAbelianGalois K L := isAbelianGalois_transportField e.symm ε.symm hε' L'
    obtain ⟨z', rfl⟩ := hx'
    set x : Kˣ := Units.map e.symm.toRingHom.toMonoidHom (normUnits K' L' z')
    have hx : x ∈ (normUnits K L).range := by
      refine ⟨Units.map (transportFieldEquiv e.symm ε.symm hε' L').toRingHom.toMonoidHom z', ?_⟩
      apply Units.ext
      change Algebra.norm K (transportFieldEquiv e.symm ε.symm hε' L' (z' : L')) =
        e.symm (Algebra.norm K' (z' : L'))
      exact (norm_transportField e.symm ε.symm hε' L' (z' : L')).symm
    have hker : restrictAb L (le_maximalAbelianExtension L) (localArtinMap K Ω x) = 1 := by
      rw [← MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_restrictAb_localArtinMap]
      exact hx
    ext y'
    rw [restrictAb_apply, transportedArtinMap_apply', AlgEquiv.one_apply]
    have hyL : ε.symm (y' : Ω') ∈ L := by
      rw [mem_transportField, RingEquiv.symm_symm, RingEquiv.apply_symm_apply]
      exact y'.2
    have h2 := congrArg (fun ρ : L ≃ₐ[K] L => ((ρ ⟨ε.symm (y' : Ω'), hyL⟩ : L) : Ω)) hker
    simp only [restrictAb_apply, AlgEquiv.one_apply] at h2
    rw [h2, RingEquiv.apply_symm_apply]

include he in

theorem transport_localArtinMap_apply (x : Kˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') := by
  have hx : Units.map e.symm.toRingHom.toMonoidHom (Units.map e.toRingHom.toMonoidHom x) = x := by
    ext
    simp
  rw [← transportedArtinMap_eq e he ε hε, transportedArtinMap_apply, hx]

end Main

section Corollaries

variable {K K' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

open Filter Topology in

theorem vle_apply_iff_of_continuous (e : K ≃+* K') (hc : Continuous e) (hc' : Continuous e.symm)
    (x y : K) : e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  refine vle_map_iff_of_valuation_lt_one_iff e.toRingHom (fun z => ?_) x y
  rw [← tendsto_pow_atTop_nhds_zero_iff, ← tendsto_pow_atTop_nhds_zero_iff]
  constructor
  · intro h
    have := (hc'.tendsto 0).comp h
    simpa [Function.comp_def] using this
  · intro h
    have := (hc.tendsto 0).comp h
    simpa [Function.comp_def] using this

variable {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω'] [IsSepClosure K Ω]
  [IsSepClosure K' Ω']

theorem transport_localArtinMap_apply_of_continuous (e : K ≃+* K') (hc : Continuous e)
    (hc' : Continuous e.symm) (ε : Ω ≃+* Ω')
    (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x)) (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') :=
  transport_localArtinMap_apply e (vle_apply_iff_of_continuous e hc hc') ε hε x hy

variable [Algebra K Ω'] [IsSepClosure K Ω']

theorem localArtinMap_algEquiv_apply (ε : Ω ≃ₐ[K] Ω') (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K Ω' x ⟨ε y, (mem_maximalAbelianExtension_transport_iff (RingEquiv.refl K)
        ε.toRingEquiv (fun c => ε.commutes c)).2 hy⟩ : maximalAbelianExtension K Ω') : Ω') := by
  have h := transport_localArtinMap_apply (RingEquiv.refl K) (fun _ _ => Iff.rfl) ε.toRingEquiv
    (fun c => ε.commutes c) x hy
  have hx : Units.map (RingEquiv.refl K).toRingHom.toMonoidHom x = x := by
    ext
    rfl
  rw [hx] at h
  exact h

end Corollaries

end RHDirect.CFT.LocalField
end Sec_LocalArtinTransport


/-! ### LocalArtinFunctoriality -/
section Sec_LocalArtinFunctoriality


namespace RHDirect.CFT.LocalField

open ValuativeRel

section Valuation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem vle_algEquiv_apply_iff {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L'] [ValuativeRel L] [ValuativeRel L']
    [ValuativeExtension K L] [ValuativeExtension K L'] (e : L ≃ₐ[K] L') (x y : L) :
    e x ≤ᵥ e y ↔ x ≤ᵥ y := by
  rw [vle_iff_spectralNorm_le (K := K), vle_iff_spectralNorm_le (K := K)]
  simp only [spectralNorm, minpoly.algEquiv_eq]

end Valuation

section Conjugation

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] (σ : Ω ≃ₐ[K] Ω)

instance finiteDimensional_map_algEquiv :
    FiniteDimensional K (E.map (σ : Ω →ₐ[K] Ω)) :=
  LinearEquiv.finiteDimensional (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toLinearEquiv

theorem localArtinMap_conj_apply (x : Eˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension E Ω) :
    σ ((localArtinMap E Ω x ⟨y, hy⟩ : maximalAbelianExtension E Ω) : Ω) =
      ((localArtinMap (E.map (σ : Ω →ₐ[K] Ω)) Ω
        (Units.map (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv.toRingHom.toMonoidHom x)
          ⟨σ y, (mem_maximalAbelianExtension_transport_iff
            (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv σ.toRingEquiv
            (fun _ => rfl)).2 hy⟩ : maximalAbelianExtension (E.map (σ : Ω →ₐ[K] Ω)) Ω) : Ω) :=
  transport_localArtinMap_apply (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)).toRingEquiv
    (fun a b => vle_algEquiv_apply_iff (IntermediateField.equivMap E (σ : Ω →ₐ[K] Ω)) a b)
    σ.toRingEquiv (fun _ => rfl) x hy

end Conjugation

section Finite

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']
  [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
  {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [IsSepClosure K Ω] [IsSepClosure K' Ω]

omit [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [ValuativeExtension K K'] in

theorem maximalAbelianExtension_le_of_algebra {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    y ∈ maximalAbelianExtension K' Ω := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  exact (mem_maximalAbelianExtension_transport_iff (AlgHom.equivFieldRange ι).toRingEquiv
    (RingEquiv.refl Ω) (fun _ => rfl)).1 (maximalAbelianExtension_le_restrictScalars ι.fieldRange hy)

theorem localArtinMap_apply_of_algebra (x : K'ˣ) {y : Ω} (hy : y ∈ maximalAbelianExtension K Ω) :
    ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
      maximalAbelianExtension K' Ω) : Ω) =
      ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  set ι := IsScalarTower.toAlgHom K K' Ω
  have : FiniteDimensional K ι.fieldRange :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ι).toLinearEquiv
  set e := AlgHom.equivFieldRange ι
  have he : ∀ a b : K', e a ≤ᵥ e b ↔ a ≤ᵥ b := vle_algEquiv_apply_iff e
  have h1 := transport_localArtinMap_apply e.toRingEquiv he (RingEquiv.refl Ω) (fun _ => rfl) x
    (maximalAbelianExtension_le_of_algebra hy)
  simp only [RingEquiv.refl_apply] at h1
  rw [h1, localArtinMap_apply_of_mem ι.fieldRange _ hy]
  congr 3
  ext
  rw [coe_normUnits, coe_normUnits]
  exact Algebra.norm_eq_of_algEquiv e x

end Finite

end RHDirect.CFT.LocalField
end Sec_LocalArtinFunctoriality


/-! ### LocalArtinAbstractField -/
section Sec_LocalArtinAbstractField


namespace RHDirect.CFT.LocalField

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

section Embedding

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsSepClosure K Ω] in
theorem isAbelianGalois_fieldRange (ι : L →ₐ[K] Ω) : IsAbelianGalois K ι.fieldRange :=
  have := IsGalois.of_algEquiv ι.equivFieldRange
  { toIsMulCommutative := ⟨⟨fun σ τ => (AlgEquiv.autCongr ι.equivFieldRange).symm.injective
      ((map_mul _ σ τ).trans ((mul_comm' _ _).trans (map_mul _ τ σ).symm))⟩⟩ }

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsAbelianGalois K L]
  [IsSepClosure K Ω] in
theorem finiteDimensional_fieldRange (ι : L →ₐ[K] Ω) : FiniteDimensional K ι.fieldRange :=
  LinearEquiv.finiteDimensional ι.equivFieldRange.toLinearEquiv

def artinOfEmbedding (ι : L →ₐ[K] Ω) : Kˣ →* (L ≃ₐ[K] L) :=
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  (AlgEquiv.autCongr ι.equivFieldRange).symm.toMonoidHom.comp
    ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω))

theorem apply_artinOfEmbedding (ι : L →ₐ[K] Ω) (x : Kˣ) (z : L) :
    ι (artinOfEmbedding ι x z) =
      ((localArtinMap K Ω x ⟨ι z, (have := isAbelianGalois_fieldRange ι;
        le_maximalAbelianExtension ι.fieldRange) ⟨z, rfl⟩⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have h : ι (artinOfEmbedding ι x z) =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _) (localArtinMap K Ω x)
        (ι.equivFieldRange z) : ι.fieldRange) : Ω) := by
    simp only [artinOfEmbedding, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
    rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]
    rfl
  rw [h, restrictAb_apply]
  rfl

theorem artinOfEmbedding_eq (ι₁ ι₂ : L →ₐ[K] Ω) : artinOfEmbedding ι₁ = artinOfEmbedding ι₂ := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable ι₁.fieldRange Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K ι₁.fieldRange Ω
  obtain ⟨φ, hφ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι₁.fieldRange
    (M := Ω) (E := Ω) (ι₂.comp ι₁.equivFieldRange.symm.toAlgHom)
  have hφι : ∀ z : L, φ (ι₁ z) = ι₂ z := by
    intro z
    have := congrArg (fun f : ι₁.fieldRange →ₐ[K] Ω => f (ι₁.equivFieldRange z)) hφ
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  set τ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  set t := topologicalAbelianizationEquiv K Ω (τ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))
  have ht : ∀ w : maximalAbelianExtension K Ω, ((t w : maximalAbelianExtension K Ω) : Ω) = τ w :=
    fun w => topologicalAbelianizationEquiv_mk_apply K Ω τ w
  ext x z
  have key : ι₂ (artinOfEmbedding ι₁ x z) = ι₂ (artinOfEmbedding ι₂ x z) := by
    rw [← hφι (artinOfEmbedding ι₁ x z), apply_artinOfEmbedding ι₂]
    change τ (ι₁ (artinOfEmbedding ι₁ x z)) = _
    rw [apply_artinOfEmbedding ι₁]
    set w : maximalAbelianExtension K Ω := ⟨ι₁ z, (have := isAbelianGalois_fieldRange ι₁;
      le_maximalAbelianExtension ι₁.fieldRange) ⟨z, rfl⟩⟩
    have htw : t w = ⟨ι₂ z, (have := isAbelianGalois_fieldRange ι₂;
        le_maximalAbelianExtension ι₂.fieldRange) ⟨z, rfl⟩⟩ :=
      Subtype.ext ((ht w).trans (hφι z))
    have hc : (localArtinMap K Ω x) (t w) = t ((localArtinMap K Ω x) w) := by
      rw [← AlgEquiv.mul_apply, mul_comm' (localArtinMap K Ω x) t, AlgEquiv.mul_apply]
    rw [← ht, ← hc, htw]
  exact ι₂.injective key

variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [IsSepClosure K Ω']

theorem artinOfEmbedding_algEquiv_comp (ε : Ω ≃ₐ[K] Ω') (ι : L →ₐ[K] Ω) :
    artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) = artinOfEmbedding ι := by
  ext x z
  have key : ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) x z) =
      ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ι x z) := by
    rw [apply_artinOfEmbedding]
    change _ = ε (ι (artinOfEmbedding ι x z))
    rw [apply_artinOfEmbedding, localArtinMap_algEquiv_apply]
    rfl
  exact ((ε : Ω →ₐ[K] Ω').comp ι).injective key

end Embedding

section Intrinsic

variable (K L) in

def localArtinMapOfField : Kˣ →* (L ≃ₐ[K] L) :=
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  artinOfEmbedding (IsSepClosed.lift : L →ₐ[K] SeparableClosure K)

theorem localArtinMapOfField_eq_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (ι : L →ₐ[K] Ω) : localArtinMapOfField K L = artinOfEmbedding ι := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  let ε : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  rw [localArtinMapOfField, ← artinOfEmbedding_algEquiv_comp ε]
  exact artinOfEmbedding_eq _ _

theorem ker_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ι : L →ₐ[K] Ω) : (artinOfEmbedding ι).ker = (normUnits K L).range := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have hker : (artinOfEmbedding ι).ker =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω)).ker := by
    ext x
    simp [artinOfEmbedding, MonoidHom.mem_ker]
  rw [hker, ker_restrictAb_localArtinMap]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨Units.map ι.equivFieldRange.symm.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩
    simp [coe_normUnits, Algebra.norm_eq_of_algEquiv]
  · rintro ⟨w, rfl⟩
    refine ⟨Units.map ι.equivFieldRange.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩
    simp [coe_normUnits, Algebra.norm_eq_of_algEquiv]

theorem ker_localArtinMapOfField : (localArtinMapOfField K L).ker = (normUnits K L).range := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  exact ker_artinOfEmbedding _

theorem surjective_localArtinMapOfField : Function.Surjective (localArtinMapOfField K L) := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  set ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  intro σ
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := SeparableClosure K) ι.fieldRange
    (AlgEquiv.autCongr ι.equivFieldRange σ)
  refine ⟨x, ?_⟩
  change (AlgEquiv.autCongr ι.equivFieldRange).symm _ = σ
  rw [hx, MulEquiv.symm_apply_apply]

def localReciprocityOfField : Kˣ ⧸ (normUnits K L).range ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq ker_localArtinMapOfField.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ surjective_localArtinMapOfField)

theorem localReciprocityOfField_mk (x : Kˣ) :
    localReciprocityOfField (K := K) (L := L) (x : Kˣ ⧸ (normUnits K L).range) =
      localArtinMapOfField K L x :=
  rfl

end Intrinsic

end RHDirect.CFT.LocalField
end Sec_LocalArtinAbstractField


/-! ### MainTheorem -/
section Sec_MainTheorem


namespace RHDirect.CFT.LocalField

open ValuativeRel

section Main

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem localArtinMap_spec :
    Continuous (localArtinMap K Ω) ∧
      (∀ π : Kˣ, ord (π : K) = 1 →
        restrictAb (maximalUnramifiedExtension K Ω) maximalUnramifiedExtension_le_maximalAbelianExtension
          (localArtinMap K Ω π) = maximalUnramifiedExtensionFrobenius K Ω) ∧
      ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)).ker =
            (normUnits K L).range ∧
          Function.Surjective ((restrictAb L (le_maximalAbelianExtension L)).comp (localArtinMap K Ω)) :=
  ⟨continuous_localArtinMap, fun _ hπ => restrictAb_localArtinMap_uniformizer hπ,
    fun L _ _ => ⟨ker_restrictAb_localArtinMap L, surjective_restrictAb_localArtinMap L⟩⟩

theorem localArtinMap_unramified (L : IntermediateField K Ω) (hL : IsUnramifiedSubextension L)
    (x : Kˣ) :
    have := hL.1
    have := hL.isGalois
    restrictAb L (hL.le_maximalUnramifiedExtension.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
      (localArtinMap K Ω x) = unramifiedFrobenius K Ω L ^ ord (x : K) :=
  have := hL.1
  have := hL.isGalois
  restrictAb_localArtinMap_of_le_maximalUnramifiedExtension L hL.le_maximalUnramifiedExtension x

end Main

section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem isSepClosure_of_isSeparable (K K' Ω : Type*) [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω] [Algebra.IsSeparable K K'] [IsSepClosure K' Ω] :
    IsSepClosure K Ω :=
  ⟨IsSepClosure.sep_closed K', Algebra.IsSeparable.trans K K' Ω⟩

theorem localArtinMap_norm [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
    [Algebra.IsSeparable K K'] {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower K K' Ω] [IsSepClosure K' Ω] (x : K'ˣ) {y : Ω} :
    have := isSepClosure_of_isSeparable K K' Ω
    ∀ hy : y ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
        maximalAbelianExtension K' Ω) : Ω) =
        ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  intro _ hy
  exact localArtinMap_apply_of_algebra x hy

theorem localArtinMap_transport {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω']
    [IsSepClosure K Ω] [IsSepClosure K' Ω'] (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x)) (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') :=
  transport_localArtinMap_apply e he ε hε x hy

end Functoriality

end RHDirect.CFT.LocalField
end Sec_MainTheorem


/-! ### ExplicitQp -/
section Sec_ExplicitQp


open _root_.IntermediateField ValuativeRel

namespace RHDirect.CFT.LocalField

open RHDirect.CFT_AbstractLocalReciprocity RHDirect.CFT.FormalGroups RHDirect.CFT.LocalField.FormalGroup

section Bridge

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hf in

theorem localReciprocity_symm_lubinTateField {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    {τ : Ω ≃ₐ[K] Ω} (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    (localReciprocity (lubinTateField Ω hπ hf n)).symm
        (unitUniformizerPow hπ u k : Kˣ ⧸ (normUnits K (lubinTateField Ω hπ hf n)).range) =
      Abelianization.of (τ.restrictNormal (lubinTateField Ω hπ hf n)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set L := lubinTateField Ω hπ hf n
  have hr := reciprocity_lubinTate hπ hf hn (fixingOpenSubgroup L)
    (by rw [coe_fixingOpenSubgroup]) (by rw [coe_fixingOpenSubgroup]; exact inf_le_left) u k τ hτd hτ
  obtain ⟨a, ha⟩ := (baseUnitsEquiv (K := K) (Ω := Ω)).surjective (unitUniformizerPow hπ u k)
  rw [← ha, MulEquiv.symm_apply_apply] at hr
  rw [← ha, localReciprocity_symm_mk_baseUnitsEquiv]
  have e : ((localClassFieldData K Ω).reciprocityAbEquiv (le_top : fixingOpenSubgroup L ≤ ⊤)
      (classFieldAxiom_units K Ω)).symm (a : tateZero Ωˣ _ _) =
      Abelianization.of (QuotientGroup.mk ⟨τ, Subgroup.mem_top τ⟩) := by
    rw [MulEquiv.symm_apply_eq, ClassFieldData.reciprocityAbEquiv_of]
    exact hr.symm
  rw [e]
  rfl

include hf in

theorem apply_val_of_mk_eq_localReciprocityLimit {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    {g : Ω ≃ₐ[K] Ω}
    (hg : (g : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
      localReciprocityLimit K Ω (unitUniformizerPow hπ u k))
    {x : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hx : x ∈ lubinTateTorsion Ω hf n) :
    g x.val = (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x).val := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set L := lubinTateField Ω hπ hf n
  have : IsMulCommutative (L ≃ₐ[K] L) := ⟨⟨lubinTateField_mul_comm hπ hf n⟩⟩
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u k
  have h2 := of_abelianRestrict_localReciprocityLimit L (unitUniformizerPow hπ u k)
  rw [← hg, abelianRestrict_mk, localReciprocity_symm_lubinTateField hπ hf hn u k hτd hτ] at h2
  have h3 := (bijective_abelianizationOf L).1 h2
  have hxL := val_mem_lubinTateField hπ hf hx
  have e := congrArg IdealPoint.val (hτ x hx)
  rw [lubinTateGalPointMap_val] at e
  rw [← e]
  have c1 := AlgEquiv.restrictNormal_commutes g L ⟨x.val, hxL⟩
  have c2 := AlgEquiv.restrictNormal_commutes τ L ⟨x.val, hxL⟩
  rw [h3] at c1
  exact c1.symm.trans c2

end Bridge

section Multiplicative

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]

theorem subst_multiplicativeLTPoly {τ : Type*} {a : MvPowerSeries τ 𝒪[ℚ_[p]]}
    (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst a (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) = (1 + a) ^ p - 1 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [multiplicativeLTPoly, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_add,
    Polynomial.coe_one, Polynomial.coe_X, ← PowerSeries.coe_substAlgHom hs, map_sub, map_pow,
    map_add, map_one, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs]

theorem lubinTateFormalGroup_multiplicative :
    (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p)).toPowerSeries =
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1 :
        MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) := by
  rw [lubinTateFormalGroup_toPowerSeries]
  symm
  apply eq_lubinTateLift
  · rw [linearForm_fin_two, map_one, one_mul, one_mul, add_sub_cancel_left]
    have h1 : ∀ i : Fin 2, (1 : ℕ∞) ≤ MvPowerSeries.order (MvPowerSeries.X i :
        MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) :=
      fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.2 (by simp)
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := add_le_add (h1 0) (h1 1)
      _ ≤ _ := MvPowerSeries.le_order_mul
  · have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 +
        MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) = 0 := by simp
    have hs : MvPowerSeries.HasSubst (substEach (multiplicativeLTPoly p : PowerSeries 𝒪[ℚ_[p]]) :
        Fin 2 → MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) :=
      hasSubst_substEach (isLubinTateSeries_multiplicativeLTPoly p).constantCoeff_eq_zero
    rw [subst_multiplicativeLTPoly p h0, ← MvPowerSeries.coe_substAlgHom hs, map_add, map_add,
      map_mul, MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_X hs,
      MvPowerSeries.subst_X hs, substEach_apply, substEach_apply,
      subst_multiplicativeLTPoly p (by simp), subst_multiplicativeLTPoly p (by simp)]
    rw [show (1 + (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) :
        MvPowerSeries (Fin 2) 𝒪[ℚ_[p]]) = (1 + MvPowerSeries.X 0) * (1 + MvPowerSeries.X 1) by ring,
      mul_pow]
    ring

end Padic

end Multiplicative

section Points

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in
theorem psTerm_add {σ : Type*} (f g : MvPowerSeries σ 𝒪[K]) (x : σ → Ω) :
    psTerm (f + g) x = psTerm f x + psTerm g x := by
  funext d
  simp only [psTerm, map_add, Subring.coe_add, Pi.add_apply, add_mul]

theorem psEval_add {σ : Type*} [Finite σ] (f g : MvPowerSeries σ 𝒪[K]) {x : σ → Ω}
    (hx : ∀ i, valuation Ω (x i) < 1) :
    psEval (f + g) x = psEval f x + psEval g x := by
  have := t2Space_of_isValuativeTopology Ω
  have h := (hasSum_psEval' f x hx).add (hasSum_psEval' g x hx)
  exact (hasSum_psEval' (f + g) x hx).unique (by rw [psTerm_add]; exact h)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

theorem psEval_X_mul_X [TopologicalSpace Ω] (x : Fin 2 → Ω) :
    psEval (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) 𝒪[K]) x = x 0 * x 1 := by
  classical
  have hX : (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin 2) 𝒪[K]) =
      MvPowerSeries.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [hX, psEval, tsum_eq_single (Finsupp.single 0 1 + Finsupp.single 1 1)]
  · rw [psTerm, MvPowerSeries.coeff_monomial_same, Finsupp.prod_add_index (by simp) (by simp [pow_add])]
    simp
  · intro d hd
    simp [psTerm, MvPowerSeries.coeff_monomial, hd]

end Points

section PadicPoints

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra ℚ_[p] Ω] [ValuativeExtension ℚ_[p] Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

theorem val_add_multiplicative
    (x y : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (x + y).val = x.val + y.val + x.val * y.val := by
  have hxy : ∀ i, valuation Ω ((![x.val, y.val] : Fin 2 → Ω) i) < 1 := fun i => by
    fin_cases i
    · exact x.valuation_lt_one
    · exact y.valuation_lt_one
  rw [IdealPoint.val_add, lubinTateFormalGroup_multiplicative, psEval_add _ _ hxy,
    psEval_add _ _ hxy, psEval_X, psEval_X, psEval_X_mul_X]
  rfl

theorem val_natCast_smul (k : ℕ)
    (x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))) :
    (((k : 𝒪[ℚ_[p]])) • x).val = (1 + x.val) ^ k - 1 := by
  rw [Nat.cast_smul_eq_nsmul]
  induction k with
  | zero => simp [IdealPoint.val_zero]
  | succ k ih =>
    rw [succ_nsmul, val_add_multiplicative, ih, pow_succ]
    ring

theorem val_smul_of_mem_torsion {n : ℕ}
    {x : IdealPoint Ω (lubinTateFormalGroup (irreducible_natCast_integer p)
      (isLubinTateSeries_multiplicativeLTPoly p))}
    (hx : x ∈ lubinTateTorsion Ω (isLubinTateSeries_multiplicativeLTPoly p) n) {a : 𝒪[ℚ_[p]]} {k : ℕ}
    (hak : (p : 𝒪[ℚ_[p]]) ^ n ∣ a - k) :
    (a • x).val = (1 + x.val) ^ k - 1 := by
  obtain ⟨c, hc⟩ := hak
  have h0 : ((p : 𝒪[ℚ_[p]]) ^ n) • x = 0 := (mem_lubinTateTorsion _ n x).1 hx
  have : a • x = (k : 𝒪[ℚ_[p]]) • x := by
    rw [← sub_eq_zero, ← sub_smul, hc, mul_comm, mul_smul, h0, smul_zero]
  rw [this, val_natCast_smul]

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra.IsAlgebraic ℚ_[p] Ω] in

theorem valuation_sub_one_lt_one {n : ℕ} {ζ : Ω} (hζ : ζ ^ (p ^ n) = 1) :
    valuation Ω (ζ - 1) < 1 := by
  have hp1 : valuation Ω (p : Ω) < 1 := by
    have h := valuation_algebraMap_lt_one_of_irreducible (L := Ω) (irreducible_natCast_integer p)
    simpa using h
  induction n generalizing ζ with
  | zero =>
    rw [pow_zero, pow_one] at hζ
    simp [hζ]
  | succ n ih =>
    have h1 : (ζ ^ p) ^ (p ^ n) = 1 := by rw [← pow_mul, ← pow_succ']; exact hζ
    have ih' := ih h1
    by_contra hge
    replace hge := not_lt.1 hge
    have hv1 : valuation Ω ζ = 1 := by
      have hN : valuation Ω ζ ^ (p ^ (n + 1)) = 1 := by rw [← map_pow, hζ, map_one]
      have hN0 : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
      rcases lt_trichotomy (valuation Ω ζ) 1 with h | h | h
      · exact absurd hN (pow_lt_one₀ zero_le h hN0).ne
      · exact h
      · exact absurd hN (one_lt_pow₀ h hN0).ne'
    have hle : valuation Ω (ζ - 1) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (by simp [hv1])
    have heq : valuation Ω (ζ - 1) = 1 := le_antisymm hle hge
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out
      (⟨ζ - 1, (Valuation.mem_integer_iff _ _).2 hle⟩ : 𝒪[Ω]) 1
    have e : ζ ^ p - 1 = (ζ - 1) ^ p + (p : Ω) * (ζ - 1) * (r : Ω) := by
      have := congrArg Subtype.val hr
      simp only [Subring.coe_pow, Subring.coe_add, Subring.coe_mul, Subring.coe_one,
        Subring.coe_natCast, one_pow, mul_one, sub_add_cancel] at this
      rw [this]
      ring
    have hr1 : valuation Ω (r : Ω) ≤ 1 := (Valuation.mem_integer_iff _ _).1 r.2
    have hlt : valuation Ω ((p : Ω) * (ζ - 1) * (r : Ω)) < valuation Ω ((ζ - 1) ^ p) := by
      rw [map_pow, heq, one_pow, map_mul, map_mul, heq, mul_one]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hr1) hp1
    have : valuation Ω (ζ ^ p - 1) = 1 := by
      rw [e, (valuation Ω).map_add_eq_of_lt_left hlt, map_pow, heq, one_pow]
    exact absurd ih' (by rw [this]; exact lt_irrefl 1)

end Padic

end PadicPoints

section Explicit

theorem pow_eq_pow_of_natCast_eq {M : Type*} [Monoid M] {ξ : M} {m a b : ℕ} (hξ : ξ ^ m = 1)
    (h : (a : ZMod m) = b) : ξ ^ a = ξ ^ b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  have key : ∀ c, ξ ^ c = ξ ^ (c % m) := fun c => by
    conv_lhs => rw [← Nat.div_add_mod c m, pow_add, pow_mul, hξ, one_pow, one_mul]
  rw [key a, key b, h]

namespace Padic

variable (p : ℕ) [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

theorem natCast_residueField_ne_zero {m : ℕ} (hm : m.Coprime p) : (m : 𝓀[ℚ_[p]]) ≠ 0 := by
  intro h0
  have hcard : ((Nat.card 𝓀[ℚ_[p]] : ℕ) : 𝓀[ℚ_[p]]) = 0 := by
    have := Fintype.ofFinite 𝓀[ℚ_[p]]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero 𝓀[ℚ_[p]]
  rw [card_residueField] at hcard
  have hc : ringChar 𝓀[ℚ_[p]] ∣ p :=
    (CharP.cast_eq_zero_iff 𝓀[ℚ_[p]] (ringChar 𝓀[ℚ_[p]]) p).1 hcard
  have hcp : ringChar 𝓀[ℚ_[p]] = p :=
    ((Nat.dvd_prime hp.out).1 hc).resolve_left CharP.ringChar_ne_one
  have hdvd : p ∣ m := by
    rw [← hcp, ← CharP.cast_eq_zero_iff 𝓀[ℚ_[p]] (ringChar 𝓀[ℚ_[p]])]
    exact h0
  have h := Nat.Coprime.coprime_dvd_left hdvd hm
  rw [Nat.coprime_self] at h
  exact hp.out.one_lt.ne' h

theorem frobenius_zpow_apply_of_pow_eq_one {m : ℕ} (hm : m.Coprime p) (r : ℤ)
    {ξ : maximalUnramifiedExtension ℚ_[p] Ω} (hξ : ξ ^ m = 1) :
    (maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ r) ξ =
      ξ ^ (((ZMod.unitOfCoprime p hm.symm ^ r : (ZMod m)ˣ) : ZMod m)).val := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).1 hm)
  have : NeZero m := ⟨hm0⟩
  set F := maximalUnramifiedExtensionFrobenius ℚ_[p] Ω
  set e := ZMod.unitOfCoprime p hm.symm
  have he : ((e : (ZMod m)ˣ) : ZMod m) = p := ZMod.coe_unitOfCoprime p hm.symm
  have hF : ∀ η : maximalUnramifiedExtension ℚ_[p] Ω, η ^ m = 1 → F η = η ^ p := fun η hη => by
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one
      (natCast_residueField_ne_zero p hm) hη, card_residueField]
  have hnat : ∀ (k : ℕ) (η : maximalUnramifiedExtension ℚ_[p] Ω), η ^ m = 1 →
      (F ^ k) η = η ^ (((e ^ k : (ZMod m)ˣ) : ZMod m)).val := by
    intro k
    induction k with
    | zero =>
      intro η hη
      rw [pow_zero, pow_zero, Units.val_one, AlgEquiv.one_apply]
      conv_lhs => rw [← pow_one η]
      exact pow_eq_pow_of_natCast_eq hη (by rw [ZMod.natCast_zmod_val, Nat.cast_one])
    | succ k ih =>
      intro η hη
      have hk : ((F ^ k) η) ^ m = 1 := by rw [← map_pow, hη, map_one]
      rw [pow_succ', AlgEquiv.mul_apply, hF _ hk, ih η hη, ← pow_mul]
      refine pow_eq_pow_of_natCast_eq hη ?_
      rw [ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val, pow_succ, Units.val_mul, he]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg r
  · rw [zpow_natCast, zpow_natCast]
    exact hnat k ξ hξ
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    set η := (F ^ k)⁻¹ ξ
    have hη : η ^ m = 1 := by rw [← map_pow, hξ, map_one]
    have hFη : (F ^ k) η = ξ := by
      change (F ^ k) ((F ^ k).symm ξ) = ξ
      exact AlgEquiv.apply_symm_apply _ ξ
    rw [← hFη, hnat k η hη, ← pow_mul]
    conv_lhs => rw [← pow_one η]
    refine pow_eq_pow_of_natCast_eq hη ?_
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Nat.cast_one]

def integerUnit (u : ℤ_[p]ˣ) : 𝒪[ℚ_[p]]ˣ :=
  Units.map (PadicRank.padicIntEquivInteger p : ℤ_[p] →* 𝒪[ℚ_[p]]) u

theorem coe_integerUnit (u : ℤ_[p]ˣ) :
    (((integerUnit p u : 𝒪[ℚ_[p]]ˣ) : 𝒪[ℚ_[p]]) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) :=
  rfl

theorem unitUniformizerPow_integerUnit (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) :
    unitUniformizerPow (irreducible_natCast_integer p) (integerUnit p u) r = x := by
  apply Units.ext
  rw [hx, unitUniformizerPow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val,
    Units.val_mk0]
  rfl

theorem ord_eq_of_eq_mul_zpow (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) :
    ord (x : ℚ_[p]) = r := by
  have hπ := irreducible_natCast_integer p
  have hp0 : (((p : 𝒪[ℚ_[p]]) : ℚ_[p])) ≠ 0 := coe_ne_zero_of_irreducible hπ
  have e : (x : ℚ_[p]) = (((integerUnit p u : 𝒪[ℚ_[p]]ˣ) : 𝒪[ℚ_[p]]) : ℚ_[p]) *
      ((p : 𝒪[ℚ_[p]]) : ℚ_[p]) ^ r := by
    rw [← unitUniformizerPow_integerUnit p x u r hx, unitUniformizerPow, Units.val_mul,
      Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rfl
  rw [e, ord_mul (by simp) (zpow_ne_zero _ hp0), ord_unit, ord_zpow hp0, ord_uniformizer hπ,
    mul_one, zero_add]

theorem apply_of_pow_eq_one_of_prime_pow (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) {σ : Ω ≃ₐ[ℚ_[p]] Ω}
    (hσ : (σ : TopologicalAbelianization (Ω ≃ₐ[ℚ_[p]] Ω)) = localReciprocityLimit ℚ_[p] Ω x)
    {n : ℕ} {ζ : Ω} (hζ : ζ ^ (p ^ n) = 1) :
    σ ζ = ζ ^ (PadicInt.toZModPow n ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val := by
  let := algebraicValuativeRel ℚ_[p] Ω
  let := algebraicTopology ℚ_[p] Ω
  have := algebraicValuativeRel_valuativeExtension ℚ_[p] Ω
  have := algebraicTopology_isValuativeTopology ℚ_[p] Ω
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, pow_one] at hζ
    subst hζ
    simp
  have hπ := irreducible_natCast_integer p
  have hf := isLubinTateSeries_multiplicativeLTPoly p
  set k := (PadicInt.toZModPow n ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])).val
  let y : IdealPoint Ω (lubinTateFormalGroup hπ hf) :=
    IdealPoint.mk (ζ - 1) (valuation_sub_one_lt_one p hζ)
  have hy : y ∈ lubinTateTorsion Ω hf n := by
    rw [mem_lubinTateTorsion]
    apply IdealPoint.ext
    rw [val_pow_smul, IdealPoint.val_zero, IdealPoint.val_mk, add_sub_cancel, hζ, sub_self]
  have h1 := apply_val_of_mk_eq_localReciprocityLimit hπ hf hn (integerUnit p u) r
    (hσ.trans (by rw [unitUniformizerPow_integerUnit p x u r hx])) hy
  have hdvd : (p : 𝒪[ℚ_[p]]) ^ n ∣ (((integerUnit p u)⁻¹ : 𝒪[ℚ_[p]]ˣ) : 𝒪[ℚ_[p]]) - k := by
    have hker : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - k ∈ RingHom.ker (PadicInt.toZModPow (p := p) n) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    have h := map_dvd (PadicRank.padicIntEquivInteger p) hker
    rw [map_pow, map_natCast, map_sub, map_natCast] at h
    convert h using 2
    simp [integerUnit]
  rw [val_smul_of_mem_torsion p hy hdvd] at h1
  simp only [y, IdealPoint.val_mk, add_sub_cancel, map_sub, map_one] at h1
  exact sub_left_injective h1

theorem apply_of_pow_eq_one_of_coprime (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℤ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) {σ : Ω ≃ₐ[ℚ_[p]] Ω}
    (hσ : (σ : TopologicalAbelianization (Ω ≃ₐ[ℚ_[p]] Ω)) = localReciprocityLimit ℚ_[p] Ω x)
    {m : ℕ} (hm : m.Coprime p) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ (((ZMod.unitOfCoprime p hm.symm ^ r : (ZMod m)ˣ) : ZMod m)).val := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed ℚ_[p]
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    subst h
    exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).1 hm)
  have hζur : ζ ∈ maximalUnramifiedExtension ℚ_[p] Ω := by
    rw [maximalUnramifiedExtension_eq_adjoin_rootsOfUnity]
    exact subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩
  have hdeg := unramifiedDegree_of_mk_eq_localReciprocityLimit hσ
  rw [ord_eq_of_eq_mul_zpow p x u r hx] at hdeg
  have hres : σ.restrictNormal (maximalUnramifiedExtension ℚ_[p] Ω) =
      maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ r := by
    apply unramifiedDegree_maximalUnramifiedExtension_injective
    rw [unramifiedDegree_restrictNormal, hdeg, map_zpow,
      unramifiedDegree_maximalUnramifiedExtensionFrobenius, ← ofAdd_zsmul, zsmul_one]
  have hξ : (⟨ζ, hζur⟩ : maximalUnramifiedExtension ℚ_[p] Ω) ^ m = 1 :=
    Subtype.ext (by simpa using hζ)
  have c := AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension ℚ_[p] Ω) ⟨ζ, hζur⟩
  rw [hres] at c
  rw [frobenius_zpow_apply_of_pow_eq_one p hm r hξ] at c
  change ((⟨ζ, hζur⟩ ^ _ : maximalUnramifiedExtension ℚ_[p] Ω) : Ω) = σ ζ at c
  rw [← c, SubmonoidClass.coe_pow]

theorem apply_of_pow_eq_one_of_coprime_of_nat (x : ℚ_[p]ˣ) (u : ℤ_[p]ˣ) (r : ℕ)
    (hx : (x : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ r) {σ : Ω ≃ₐ[ℚ_[p]] Ω}
    (hσ : (σ : TopologicalAbelianization (Ω ≃ₐ[ℚ_[p]] Ω)) = localReciprocityLimit ℚ_[p] Ω x)
    {m : ℕ} (hm : m.Coprime p) {ζ : Ω} (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ (p ^ r) := by
  have hm0 : m ≠ 0 := fun h => by
    subst h
    exact hp.out.one_lt.ne' ((Nat.coprime_zero_left p).1 hm)
  have : NeZero m := ⟨hm0⟩
  rw [apply_of_pow_eq_one_of_coprime p x u r (by rw [hx, zpow_natCast]) hσ hm hζ]
  refine pow_eq_pow_of_natCast_eq hζ ?_
  rw [ZMod.natCast_zmod_val, zpow_natCast, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    Nat.cast_pow]

end Padic

end Explicit

end RHDirect.CFT.LocalField
end Sec_ExplicitQp

end
