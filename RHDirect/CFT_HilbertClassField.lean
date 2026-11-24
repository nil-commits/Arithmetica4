import RHDirect.CFT_GlobalExistence

/-!
# RHDirect.CFT_HilbertClassField

Global Class Field Theory Pillar — Ray Class Fields, the Hilbert Class Field, and the
Unconditional Bridge to `RHDirect.Stage13GL_KummerDuality.HilbertArtinData`:
1. Ray class groups `Modulus.RayClassGroup` & ideal-theoretic `Modulus.IdealRayClassGroup`,
   finiteness and weak-approximation isomorphism `Modulus.rayClassGroupEquiv`.
2. Local unramifiedness and splitting criteria (`RayClassFieldLocal`).
3. Ray class fields `Modulus.rayClassField`, Artin isomorphism `Modulus.rayClassArtinEquiv`,
   Frobenius law `Modulus.rayClassArtinEquiv_primeClass`, and cofinality `exists_le_rayClassField`.
4. Everywhere-unramified extensions and trivial modulus `Modulus.one` (`TrivialModulus`).
5. **Hilbert Class Field** (`HilbertClassField`): `hilbertClassField K Ω`, its finiteness,
   abelian Galois property, norm group `range_ideleClassNorm_hilbertClassField`, everywhere
   unramifiedness `isUnramifiedEverywhere_hilbertClassField`, universal property
   `le_hilbertClassField_iff`, Artin isomorphism
   `hilbertClassFieldArtinEquiv : ClassGroup (𝓞 K) ≃* (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω)`,
   and Frobenius law `hilbertClassFieldArtinEquiv_mk0`.
6. **Crown Jewel Bridge (`hilbertArtinData_unconditional`)**: unconditional, zero-parameter
   construction of `RHDirect.Stage13GL_KummerDuality.HilbertArtinData K Ω` together with
   unconditional corollaries for `shaLen_le_of_cl`, `plusLen_le_of_cl`, and `minusLen_le_of_cl`.
-/

noncomputable section

namespace RHDirect.CFT.Global

open RHDirect.Stage13CFT_IdeleNormResidue
open RHDirect.CFT_ProfiniteSemilocal

/-! ### 01_ClassFieldConsequences.RayClass -/
section Sec6_01_ClassFieldConsequences_RayClass

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def rayGroup : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ 𝔪.congruenceSubgroup

abbrev RayClassGroup : Type _ :=
  IdeleGroup K ⧸ 𝔪.rayGroup

theorem diagonal_range_le_rayGroup : (diagonal K).range ≤ 𝔪.rayGroup :=
  le_sup_left

theorem congruenceSubgroup_le_rayGroup : 𝔪.congruenceSubgroup ≤ 𝔪.rayGroup :=
  le_sup_right

theorem map_rayGroup :
    𝔪.rayGroup.map (QuotientGroup.mk' (diagonal K).range) =
      𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  rw [rayGroup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  rfl

instance : (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def quotientMapCongruenceEquiv :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.RayClassGroup :=
  (QuotientGroup.quotientMulEquivOfEq 𝔪.map_rayGroup.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ 𝔪.diagonal_range_le_rayGroup)

@[simp]
theorem quotientMapCongruenceEquiv_mk (x : IdeleGroup K) :
    𝔪.quotientMapCongruenceEquiv (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      (QuotientGroup.mk x : 𝔪.RayClassGroup) :=
  rfl

theorem map_idealLevel_sup_le :
    (idealLevel 𝔪.ideal).map ofFinite ⊔ (infinitePositive K).map ofInfinite ≤
      𝔪.congruenceSubgroup := by
  refine sup_le ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
    · rw [← finiteComponent_toFinite, toFinite_ofFinite]
      exact mem_finiteLevel.1 hy v
    · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((toInfinite K (ofFinite y) : InfiniteAdeleRing K) w.1)
      rw [toInfinite_ofFinite]
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
      rw [map_one]
      exact one_pos
  · rintro _ ⟨z, hz, rfl⟩
    refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
    · rw [← finiteComponent_toFinite, toFinite_ofInfinite, map_one]
      exact one_mem _
    · have h : ((infiniteProj w.1 (ofInfinite z) : (w.1.Completion)ˣ) : w.1.Completion) =
          (toInfinite K (ofInfinite z) : InfiniteAdeleRing K) w.1 := rfl
      rw [h, toInfinite_ofInfinite]
      exact hz w.1 w.2

theorem congruenceSubgroup_eq_sup (h : 𝔪.real = Set.univ) :
    𝔪.congruenceSubgroup =
      (idealLevel 𝔪.ideal).map ofFinite ⊔ (infinitePositive K).map ofInfinite := by
  refine le_antisymm (fun x hx ↦ ?_) 𝔪.map_idealLevel_sup_le
  obtain ⟨hf, hi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
  rw [← ofFinite_mul_ofInfinite x]
  refine mul_mem (Subgroup.mem_sup_left ⟨_, mem_finiteLevel.2 fun v ↦ ?_, rfl⟩)
    (Subgroup.mem_sup_right ⟨_, fun w hw ↦ hi ⟨w, hw⟩ (h ▸ Set.mem_univ _), rfl⟩)
  rw [finiteComponent_toFinite]
  exact hf v

theorem rayGroup_ideal_le : IdeleGroup.rayGroup K 𝔪.ideal ≤ 𝔪.rayGroup := by
  rw [IdeleGroup.rayGroup, sup_assoc]
  exact sup_le_sup_left 𝔪.map_idealLevel_sup_le _

theorem rayGroup_eq (h : 𝔪.real = Set.univ) : 𝔪.rayGroup = IdeleGroup.rayGroup K 𝔪.ideal := by
  rw [IdeleGroup.rayGroup, sup_assoc, rayGroup, 𝔪.congruenceSubgroup_eq_sup h]

def rayClassGroupEquiv_of_real_eq_univ (h : 𝔪.real = Set.univ) :
    𝔪.RayClassGroup ≃* RHDirect.CFT.Global.RayClassGroup K 𝔪.ideal :=
  QuotientGroup.quotientMulEquivOfEq (𝔪.rayGroup_eq h)

@[simp]
theorem rayClassGroupEquiv_of_real_eq_univ_mk (h : 𝔪.real = Set.univ) (x : IdeleGroup K) :
    𝔪.rayClassGroupEquiv_of_real_eq_univ h (QuotientGroup.mk x) =
      (QuotientGroup.mk x : RHDirect.CFT.Global.RayClassGroup K 𝔪.ideal) :=
  rfl

theorem RayClassGroup.finite : Finite 𝔪.RayClassGroup := by
  have : Finite (RHDirect.CFT.Global.RayClassGroup K 𝔪.ideal) :=
    RHDirect.CFT.Global.RayClassGroup.finite 𝔪.ideal_ne_bot
  have : (IdeleGroup.rayGroup K 𝔪.ideal).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : 𝔪.rayGroup.FiniteIndex := Subgroup.finiteIndex_of_le 𝔪.rayGroup_ideal_le
  exact Subgroup.finite_quotient_of_finiteIndex

instance : Finite 𝔪.RayClassGroup :=
  RayClassGroup.finite 𝔪

theorem finiteIndex_map_congruenceSubgroup :
    (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)).FiniteIndex := by
  have : Finite (IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K)) :=
    Finite.of_equiv _ 𝔪.quotientMapCongruenceEquiv.symm.toEquiv
  exact Subgroup.finiteIndex_of_finite_quotient

end Modulus

end

end Sec6_01_ClassFieldConsequences_RayClass

/-! ### 02_ClassFieldConsequences.IdealRayClass -/
section Sec6_02_ClassFieldConsequences_IdealRayClass

open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

namespace Modulus

variable (𝔪 : Modulus K)

def coprimeIdeals : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  carrier := {I | ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
    count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0}
  one_mem' v _ := by rw [Units.val_one, count_one]
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul, count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, count_inv, hI v hv, neg_zero]

theorem mem_coprimeIdeals {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I ∈ 𝔪.coprimeIdeals ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.ideal →
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
  Iff.rfl

theorem ord_eq_zero_of_mem_idelesOneMod {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.ideal) : ord v x = 0 := by
  have h := ((𝔪.mem_idelesOneMod.1 hx).1 v hv).1
  rw [coe_finiteProj] at h
  rw [ord, h, log_one, neg_zero]

theorem toFractionalIdeal_mem_coprimeIdeals {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    toFractionalIdeal x ∈ 𝔪.coprimeIdeals := fun v hv ↦ by
  rw [count_toFractionalIdeal, 𝔪.ord_eq_zero_of_mem_idelesOneMod hx hv]

theorem toPrincipalIdeal_mem_coprimeIdeals {a : Kˣ} (ha : a ∈ 𝔪.rayUnits) :
    toPrincipalIdeal (𝓞 K) K a ∈ 𝔪.coprimeIdeals := by
  rw [← toFractionalIdeal_diagonal]
  exact 𝔪.toFractionalIdeal_mem_coprimeIdeals ha

def principalRay : Subgroup 𝔪.coprimeIdeals :=
  (𝔪.rayUnits.map (toPrincipalIdeal (𝓞 K) K)).subgroupOf 𝔪.coprimeIdeals

theorem mem_principalRay {I : 𝔪.coprimeIdeals} :
    I ∈ 𝔪.principalRay ↔
      ∃ a ∈ 𝔪.rayUnits, toPrincipalIdeal (𝓞 K) K a = (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  rw [principalRay, Subgroup.mem_subgroupOf, Subgroup.mem_map]

abbrev IdealRayClassGroup : Type _ :=
  𝔪.coprimeIdeals ⧸ 𝔪.principalRay

theorem exists_diagonal_mul_mem_idelesOneMod (x : IdeleGroup K) :
    ∃ a : Kˣ, diagonal K a * x ∈ 𝔪.idelesOneMod := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) := 𝔪.finite_support_exponent.toFinset
  let T : Finset (InfinitePlace K) := Finset.univ
  let O : Set (((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ)) :=
    (Set.univ.pi fun v : S ↦ {z | z * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)}) ×ˢ
      (Set.univ.pi fun w : T ↦ {z | ∀ hw : w.1.IsReal,
        (⟨w.1, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.real →
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
            ((z * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)})
  have hO : IsOpen O := by
    refine (isOpen_set_pi Set.finite_univ fun v _ ↦ ?_).prod
      (isOpen_set_pi Set.finite_univ fun w _ ↦ ?_)
    · exact (isOpen_unitsLevel v.1 _).preimage (continuous_mul_const _)
    · simp only [Set.ofPred_forall]
      refine isOpen_iInter_of_finite fun hw ↦ isOpen_iInter_of_finite fun _ ↦ ?_
      exact isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp
          (Units.continuous_val.comp (continuous_mul_const _)))
  have hne : O.Nonempty := by
    refine ⟨(fun v ↦ (finiteProj v.1 x)⁻¹, fun w ↦ (infiniteProj w.1 x)⁻¹),
      Set.mem_univ_pi.2 fun v ↦ ?_, Set.mem_univ_pi.2 fun w ↦ ?_⟩
    · show (finiteProj v.1 x)⁻¹ * finiteProj v.1 x ∈ unitsLevel v.1 (𝔪.exponent v.1)
      rw [inv_mul_cancel]
      exact one_mem _
    · intro hw _
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((infiniteProj w.1 x)⁻¹ * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)
      rw [inv_mul_cancel, Units.val_one, map_one]
      exact one_pos
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S T).exists_mem_open hO hne
  refine ⟨a, 𝔪.mem_idelesOneMod.2 ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩⟩
  · have hvS : v ∈ S := by
      rw [Set.Finite.mem_toFinset, mem_support, ← Nat.one_le_iff_ne_zero]
      exact (𝔪.one_le_exponent_iff v).2 hv
    have h := Set.mem_univ_pi.1 ha.1 ⟨v, hvS⟩
    have he : finiteProj v (diagonal K a) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
      refine Units.ext ?_
      change ((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [map_mul, he]
    exact h
  · have h := Set.mem_univ_pi.1 ha.2 ⟨w.1, Finset.mem_univ _⟩ w.2 hw
    have he : infiniteProj w.1 (diagonal K a) =
        Units.map (algebraMap K w.1.Completion).toMonoidHom a :=
      Units.ext rfl
    rw [map_mul, he]
    exact h

def idelesOneModToCoprimeIdeals : 𝔪.idelesOneMod →* 𝔪.coprimeIdeals :=
  ((toFractionalIdeal (K := K)).comp 𝔪.idelesOneMod.subtype).codRestrict _
    fun x ↦ 𝔪.toFractionalIdeal_mem_coprimeIdeals x.2

@[simp]
theorem coe_idelesOneModToCoprimeIdeals (x : 𝔪.idelesOneMod) :
    ((𝔪.idelesOneModToCoprimeIdeals x : 𝔪.coprimeIdeals) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      toFractionalIdeal (x : IdeleGroup K) :=
  rfl

def toIdealRayClassGroup : 𝔪.idelesOneMod →* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneModToCoprimeIdeals

def toRayClassGroup : 𝔪.idelesOneMod →* 𝔪.RayClassGroup :=
  (QuotientGroup.mk' _).comp 𝔪.idelesOneMod.subtype

theorem exists_mem_idelesOneMod_toFractionalIdeal_eq {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ x ∈ 𝔪.idelesOneMod, toFractionalIdeal x = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
        neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

theorem idelesOneModToCoprimeIdeals_surjective : Surjective 𝔪.idelesOneModToCoprimeIdeals := by
  rintro ⟨I, hI⟩
  have h : I ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K)) := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    refine finprod_induction (· ∈ 𝔪.idelesOneMod.map (toFractionalIdeal (K := K))) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ ?_
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · rw [hI v hv, zpow_zero]
      exact one_mem _
    · obtain ⟨x, hx, hxI⟩ := 𝔪.exists_mem_idelesOneMod_toFractionalIdeal_eq hv
      exact zpow_mem (Subgroup.mem_map.2 ⟨x, hx, hxI⟩) _
  obtain ⟨x, hx, hxI⟩ := h
  exact ⟨⟨x, hx⟩, Subtype.ext hxI⟩

theorem toIdealRayClassGroup_surjective : Surjective 𝔪.toIdealRayClassGroup :=
  (QuotientGroup.mk'_surjective _).comp 𝔪.idelesOneModToCoprimeIdeals_surjective

theorem toRayClassGroup_surjective : Surjective 𝔪.toRayClassGroup := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨a, ha⟩ := 𝔪.exists_diagonal_mul_mem_idelesOneMod x
  refine ⟨⟨_, ha⟩, ?_⟩
  change (QuotientGroup.mk (diagonal K a * x) : 𝔪.RayClassGroup) = QuotientGroup.mk x
  rw [QuotientGroup.eq, show (diagonal K a * x)⁻¹ * x = (diagonal K a)⁻¹ by
    rw [mul_inv_rev, mul_comm x⁻¹, mul_assoc, inv_mul_cancel, mul_one]]
  exact inv_mem (𝔪.diagonal_range_le_rayGroup ⟨a, rfl⟩)

theorem ker_toRayClassGroup :
    𝔪.toRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext x
  rw [MonoidHom.mem_ker, toRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem ker_toIdealRayClassGroup :
    𝔪.toIdealRayClassGroup.ker = 𝔪.rayGroup.subgroupOf 𝔪.idelesOneMod := by
  ext ⟨x, hx⟩
  rw [MonoidHom.mem_ker, toIdealRayClassGroup, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_principalRay, Subgroup.mem_subgroupOf, rayGroup, Subgroup.mem_sup]
  constructor
  · rintro ⟨a, ha, hax⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal x at hax
    refine ⟨diagonal K a, ⟨a, rfl⟩, (diagonal K a)⁻¹ * x, ?_, mul_inv_cancel_left _ _⟩
    rw [congruenceSubgroup_eq_inf, Subgroup.mem_inf, ← ker_toFractionalIdeal, MonoidHom.mem_ker,
      map_mul, map_inv, toFractionalIdeal_diagonal, hax]
    exact ⟨mul_mem (inv_mem ha) hx, inv_mul_cancel _⟩
  · rintro ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩
    have hu' := 𝔪.congruenceSubgroup_le_idelesOneMod hu
    have ha : a ∈ 𝔪.rayUnits := by
      change diagonal K a ∈ 𝔪.idelesOneMod
      rw [← mul_inv_cancel_right (diagonal K a) u]
      exact mul_mem hx (inv_mem hu')
    refine ⟨a, ha, ?_⟩
    change toPrincipalIdeal (𝓞 K) K a = toFractionalIdeal (diagonal K a * u)
    have hu0 : toFractionalIdeal u = 1 := by
      rw [← MonoidHom.mem_ker, ker_toFractionalIdeal]
      exact 𝔪.congruenceSubgroup_le_standardOpenSubgroup hu
    rw [map_mul, hu0, mul_one, toFractionalIdeal_diagonal]

def rayClassGroupEquiv : 𝔪.RayClassGroup ≃* 𝔪.IdealRayClassGroup :=
  (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (𝔪.ker_toRayClassGroup.trans 𝔪.ker_toIdealRayClassGroup.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toIdealRayClassGroup_surjective))

theorem rayClassGroupEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassGroupEquiv (QuotientGroup.mk x : 𝔪.RayClassGroup) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective _ 𝔪.toRayClassGroup_surjective).symm
      (QuotientGroup.mk x : 𝔪.RayClassGroup) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [rayClassGroupEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, h]
  rfl

def quotientEquivIdealRayClassGroup :
    IdeleClassGroup K ⧸ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≃* 𝔪.IdealRayClassGroup :=
  𝔪.quotientMapCongruenceEquiv.trans 𝔪.rayClassGroupEquiv

theorem quotientEquivIdealRayClassGroup_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.quotientEquivIdealRayClassGroup (QuotientGroup.mk (IdeleClassGroup.mk K x)) =
      QuotientGroup.mk (⟨toFractionalIdeal x, 𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ :
        𝔪.coprimeIdeals) := by
  rw [quotientEquivIdealRayClassGroup, MulEquiv.trans_apply, quotientMapCongruenceEquiv_mk,
    rayClassGroupEquiv_mk _ hx]

def idealRayClassGroupEquiv_of_real_eq_univ (h : 𝔪.real = Set.univ) :
    RHDirect.CFT.Global.RayClassGroup K 𝔪.ideal ≃* 𝔪.IdealRayClassGroup :=
  (𝔪.rayClassGroupEquiv_of_real_eq_univ h).symm.trans 𝔪.rayClassGroupEquiv

instance : Finite 𝔪.IdealRayClassGroup :=
  Finite.of_equiv _ 𝔪.rayClassGroupEquiv.toEquiv

end Modulus

end

end Sec6_02_ClassFieldConsequences_IdealRayClass

/-! ### 03_ClassFieldConsequences.RayClassFieldLocal -/
section Sec6_03_ClassFieldConsequences_RayClassFieldLocal

open IsDedekindDomain NumberField ValuativeRel RHDirect.CFT.LocalField SemiLocal WithZero
open scoped Pointwise

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M]
  [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)]

omit [CharZero k] [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [ValuativeExtension k M] [FiniteDimensional k M] in
variable (k) in
theorem exists_ord_eq_one_units : ∃ π : kˣ, ord (π : k) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, ord_uniformizer hϖ⟩

omit [CharZero k] [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [ValuativeExtension k M] [FiniteDimensional k M] in
theorem ord_zpow_units {π : kˣ} (hπ : ord (π : k) = 1) (n : ℤ) : ord ((π ^ n : kˣ) : k) = n := by
  rw [Units.val_zpow_eq_zpow_val, ord_zpow π.ne_zero, hπ, mul_one]

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [ValuativeExtension k M] in
theorem natCard_quotient_range_normUnits :
    Nat.card (kˣ ⧸ (normUnits k M).range) = Module.finrank k M := by
  have e : kˣ ⧸ (normUnits k M).range ≃* (M ≃ₐ[k] M) :=
    (QuotientGroup.quotientMulEquivOfEq ker_normResidueSymbol.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ normResidueSymbol_surjective)
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]

theorem ramificationIndex_eq_one_of_units_le
    (h : unitFiltrationUnits k 0 ≤ (normUnits k M).range) : ramificationIndex k M = 1 := by
  set N := (normUnits k M).range
  set f := residueDegree k M
  obtain ⟨π, hπ⟩ := exists_ord_eq_one_units k
  obtain ⟨ϖ, hϖ⟩ := exists_ord_eq_one_units M
  have hπf : π ^ (f : ℤ) ∈ N := by
    have hu : (π ^ (f : ℤ))⁻¹ * normUnits k M ϖ ∈ unitFiltrationUnits k 0 := by
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _),
        coe_normUnits, ord_norm, hϖ, ← zpow_neg, ord_zpow_units hπ]
      ring
    have h2 := N.mul_mem (h hu) (N.inv_mem (⟨ϖ, rfl⟩ : normUnits k M ϖ ∈ N))
    rwa [mul_inv_cancel_right, inv_mem_iff] at h2
  have htop : Subgroup.zpowers (π : kˣ ⧸ N) = ⊤ := by
    refine eq_top_iff.2 fun c _ ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨ord (x : k), ?_⟩
    change ((π : kˣ ⧸ N)) ^ ord (x : k) = (x : kˣ ⧸ N)
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    apply h
    rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _),
      ← zpow_neg, ord_zpow_units hπ]
    ring
  have hf0 : 0 < f := by
    have h1 := ramificationIndex_mul_residueDegree k M
    have h2 : 0 < Module.finrank k M := Module.finrank_pos
    rw [← h1] at h2
    exact Nat.pos_of_mul_pos_left h2
  have hle : Module.finrank k M ≤ f := by
    rw [← natCard_quotient_range_normUnits, ← Subgroup.card_top (G := kˣ ⧸ N), ← htop,
      Nat.card_zpowers]
    refine orderOf_le_of_pow_eq_one hf0 ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact_mod_cast hπf
  have h1 : ramificationIndex k M * f = Module.finrank k M := ramificationIndex_mul_residueDegree k M
  have he : ramificationIndex k M ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 2 * f ≤ ramificationIndex k M * f := Nat.mul_le_mul_right f hc
    omega
  have he0 : ramificationIndex k M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (Module.finrank_pos (R := k) (M := M)).ne' h1.symm
  omega

end Local

section Completion

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isEquiv_valuation_valued :
    (ValuativeRel.valuation (v.adicCompletion K)).IsEquiv
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) :=
  ValuativeRel.isEquiv _ _

variable {v} in
theorem mem_unitFiltrationUnits_zero_iff_valued {x : (v.adicCompletion K)ˣ} :
    x ∈ unitFiltrationUnits (v.adicCompletion K) 0 ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  rw [mem_unitFiltrationUnits_zero_iff]
  exact (isEquiv_valuation_valued v).eq_one_iff_eq_one

theorem valued_irreducible_valuationInteger {ϖ : 𝒪[v.adicCompletion K]} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
  have he := isEquiv_valuation_valued v
  have hne : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hlt : Valued.v (ϖ : v.adicCompletion K) < 1 :=
    he.lt_one_iff_lt_one.1 (valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ))
  obtain ⟨y, hy⟩ := valued_adicCompletion_surjective (K := K) v (exp (-1 : ℤ))
  have hexp : exp (-1 : ℤ) < 1 := by
    rw [← exp_zero, exp_lt_exp]
    norm_num
  have hy1 : valuation (v.adicCompletion K) y < 1 := he.lt_one_iff_lt_one.2 (hy ▸ hexp)
  have hymem : (⟨y, hy1.le⟩ : 𝒪[v.adicCompletion K]) ∈ 𝓂[v.adicCompletion K] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation (v.adicCompletion K))).isUnit_iff_valuation_eq_one]
    exact hy1.ne
  have hyϖ : valuation (v.adicCompletion K) y ≤ valuation (v.adicCompletion K) ϖ := by
    have hs := hϖ.maximalIdeal_eq_setOfPred_le_v_coe (v := valuation (v.adicCompletion K))
    have h2 : (⟨y, hy1.le⟩ : 𝒪[v.adicCompletion K]) ∈ (𝓂[v.adicCompletion K] : Set _) := hymem
    rw [hs] at h2
    exact h2
  have hyϖ' := (he y ϖ).1 hyϖ
  rw [hy] at hyϖ'
  rw [← exp_log hne] at hyϖ' hlt ⊢
  rw [← exp_zero, exp_lt_exp] at hlt
  rw [exp_le_exp] at hyϖ'
  congr 1
  omega

theorem exists_ord_eq_one_valued :
    ∃ π : (v.adicCompletion K)ˣ, ord (π : v.adicCompletion K) = 1 ∧
      Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, ord_uniformizer hϖ, valued_irreducible_valuationInteger v hϖ⟩

end Completion

section Global

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : HeightOneSpectrum (𝓞 K))

theorem ramificationIdx_eq_one_of_units_le_ker_localSymbol
    (h : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (localSymbol L v).ker)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let w' : PlacesOver L v := ⟨w, inferInstance⟩
  have := isMulCommutative_gal_adicCompletion L v w'
  have hM : ramificationIndex (v.adicCompletion K) (w.adicCompletion L) = 1 :=
    ramificationIndex_eq_one_of_units_le (by rw [← ker_localSymbol L v w']; exact h)
  exact (ramificationIdx_integer v w).symm.trans hM

theorem localSymbol_eq_one_iff_normResidueSymbol (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) :
    localSymbol L v x = 1 ↔
      normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x = 1 := by
  have := isMulCommutative_gal_adicCompletion L v w
  rw [localSymbol_eq_symbolAt L v w]
  change (((decompositionMulEquiv v w.1).symm
    (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x) :
      MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal) : L ≃ₐ[K] L) = 1 ↔ _
  rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

theorem splitsCompletely_iff_localSymbol_eq_one :
    SplitsCompletely L v ↔ ∀ x : (v.adicCompletion K)ˣ, localSymbol L v x = 1 := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  have := isMulCommutative_gal_adicCompletion L v w
  rw [splitsCompletely_iff_forall_finrank]
  constructor
  · intro h x
    rw [localSymbol_eq_one_iff_normResidueSymbol v w]
    have hc : Nat.card (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) = 1 := by
      rw [IsGalois.card_aut_eq_finrank, h w]
    exact (Nat.card_eq_one_iff_unique.1 hc).1.elim _ _
  · intro h w'
    rw [← finrank_eq_of_isGalois v w w', ← IsGalois.card_aut_eq_finrank,
      Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun σ τ ↦ ?_⟩, inferInstance⟩
    obtain ⟨x, rfl⟩ := normResidueSymbol_surjective σ
    obtain ⟨y, rfl⟩ := normResidueSymbol_surjective τ
    rw [(localSymbol_eq_one_iff_normResidueSymbol v w x).1 (h x),
      (localSymbol_eq_one_iff_normResidueSymbol v w y).1 (h y)]

theorem splitsCompletely_iff_arithFrobAt_eq_one
    (h : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (localSymbol L v).ker)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    SplitsCompletely L v ↔ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = 1 := by
  have he := ramificationIdx_eq_one_of_units_le_ker_localSymbol v h w
  obtain ⟨π, hπ⟩ := exists_ord_eq_one_units (v.adicCompletion K)
  have hF := localSymbol_eq_arithFrobAt v w he hπ
  rw [splitsCompletely_iff_localSymbol_eq_one]
  constructor
  · intro h1
    rw [← hF]
    exact h1 π
  · intro h1 x
    have hu : (π ^ ord (x : v.adicCompletion K))⁻¹ * x ∈ unitFiltrationUnits (v.adicCompletion K) 0 := by
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _),
        ← zpow_neg, ord_zpow_units hπ]
      ring
    have hx : x = π ^ ord (x : v.adicCompletion K) * ((π ^ ord (x : v.adicCompletion K))⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    rw [hx, map_mul, h hu, mul_one, map_zpow, hF, h1, one_zpow]

end Global

end

end Sec6_03_ClassFieldConsequences_RayClassFieldLocal

/-! ### 04_ClassFieldConsequences.RayClassField -/
section Sec6_04_ClassFieldConsequences_RayClassField

open IsDedekindDomain NumberField IntermediateField IdeleGroup
  RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup SemiLocal WithZero
open RHDirect.CFT.LocalField (restrictAb le_maximalAbelianExtension)
open scoped Pointwise

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

namespace Modulus

variable (𝔪 : Modulus K)

def normSubgroup : OpenFiniteIndexSubgroup K :=
  ⟨𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K), 𝔪.isOpen_map_congruenceSubgroup,
    𝔪.finiteIndex_map_congruenceSubgroup⟩

theorem finiteEmbedding_mem_congruenceSubgroup {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    finiteEmbedding v u ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun w ↦ ?_, fun w _ ↦ ?_⟩
  · by_cases hwv : w = v
    · subst hwv
      rw [finiteProj_finiteEmbedding, (𝔪.exponent_eq_zero_iff w).2 hv]
      refine mem_unitsLevel.2 ⟨hu, ?_⟩
      rw [Nat.cast_zero, neg_zero, exp_zero]
      exact Valuation.map_sub_le _ hu.le (by simp)
    · rw [finiteProj_finiteEmbedding_of_ne hwv]
      exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos

theorem exists_uniformizer_finiteEmbedding_mem_idelesOneMod {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    ∃ π : (v.adicCompletion K)ˣ, RHDirect.CFT.LocalField.ord (π : v.adicCompletion K) = 1 ∧
      ∃ _ : finiteEmbedding v π ∈ 𝔪.idelesOneMod,
        toFractionalIdeal (finiteEmbedding v π) = primeIdealUnit v := by
  classical
  obtain ⟨π, hπ, hval⟩ := exists_ord_eq_one_valued v
  refine ⟨π, hπ, 𝔪.mem_idelesOneMod.2 ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩,
    toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  · have hwv : w ≠ v := fun h ↦ hv (h ▸ hw)
    rw [finiteProj_finiteEmbedding_of_ne hwv]
    exact one_mem _
  · change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (1 : w.1.Completion)
    rw [map_one]
    exact one_pos
  · rw [count_primeIdealUnit]
    split_ifs with h
    · subst h
      rw [ord_finiteEmbedding_self, hval, log_exp, neg_neg]
    · exact ord_finiteEmbedding_of_ne h _

theorem primeIdealUnit_mem_coprimeIdeals {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    primeIdealUnit v ∈ 𝔪.coprimeIdeals := fun w hw ↦ by
  rw [count_primeIdealUnit, if_neg]
  rintro rfl
  exact hv hw

def primeClass {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) : 𝔪.IdealRayClassGroup :=
  QuotientGroup.mk ⟨primeIdealUnit v, 𝔪.primeIdealUnit_mem_coprimeIdeals hv⟩

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

def rayClassFieldSubfield : FiniteAbelianSubfield K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual 𝔪.normSubgroup)

def rayClassField : IntermediateField K Ω :=
  (𝔪.rayClassFieldSubfield Ω).1

instance finiteDimensional_rayClassField : FiniteDimensional K (𝔪.rayClassField Ω) :=
  (𝔪.rayClassFieldSubfield Ω).2.1

instance isAbelianGalois_rayClassField : IsAbelianGalois K (𝔪.rayClassField Ω) :=
  (𝔪.rayClassFieldSubfield Ω).2.2

theorem range_ideleClassNorm_rayClassField :
    (ideleClassNorm K (𝔪.rayClassField Ω)).range = 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) := by
  have h : normGroup (𝔪.rayClassFieldSubfield Ω) = 𝔪.normSubgroup := by
    rw [← normGroupOrderIso_apply, rayClassFieldSubfield, OrderIso.apply_symm_apply]
    rfl
  exact congrArg Subtype.val h

def rayClassGroupGalEquiv : 𝔪.RayClassGroup ≃* (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) :=
  𝔪.quotientMapCongruenceEquiv.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (𝔪.range_ideleClassNorm_rayClassField Ω).symm).trans
      (reciprocityMapEquiv K (𝔪.rayClassField Ω)))

theorem rayClassGroupGalEquiv_mk (x : IdeleGroup K) :
    𝔪.rayClassGroupGalEquiv Ω (QuotientGroup.mk x) =
      reciprocityMap K (𝔪.rayClassField Ω) (IdeleClassGroup.mk K x) := by
  rw [rayClassGroupGalEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply,
    ← quotientMapCongruenceEquiv_mk, MulEquiv.symm_apply_apply]
  rfl

def rayClassArtinEquiv : 𝔪.IdealRayClassGroup ≃* (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) :=
  𝔪.rayClassGroupEquiv.symm.trans (𝔪.rayClassGroupGalEquiv Ω)

theorem rayClassArtinEquiv_mk {x : IdeleGroup K} (hx : x ∈ 𝔪.idelesOneMod) :
    𝔪.rayClassArtinEquiv Ω (QuotientGroup.mk ⟨toFractionalIdeal x,
      𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩) =
      reciprocityMap K (𝔪.rayClassField Ω) (IdeleClassGroup.mk K x) := by
  rw [rayClassArtinEquiv, MulEquiv.trans_apply, ← 𝔪.rayClassGroupEquiv_mk hx,
    MulEquiv.symm_apply_apply, rayClassGroupGalEquiv_mk]

theorem unitFiltrationUnits_le_ker_localSymbol {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    RHDirect.CFT.LocalField.unitFiltrationUnits (v.adicCompletion K) 0 ≤
      (localSymbol (𝔪.rayClassField Ω) v).ker := by
  intro u hu
  have hx : IdeleClassGroup.mk K (finiteEmbedding v u) ∈
      (ideleClassNorm K (𝔪.rayClassField Ω)).range := by
    rw [𝔪.range_ideleClassNorm_rayClassField Ω]
    exact ⟨_, 𝔪.finiteEmbedding_mem_congruenceSubgroup hv
      (mem_unitFiltrationUnits_zero_iff_valued.1 hu), rfl⟩
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk, ideleSymbol_finiteEmbedding] at hx
  exact hx

theorem ramificationIdx_rayClassField_eq_one {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal)
    (w : HeightOneSpectrum (𝓞 (𝔪.rayClassField Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
  ramificationIdx_eq_one_of_units_le_ker_localSymbol v (𝔪.unitFiltrationUnits_le_ker_localSymbol Ω hv) w

theorem rayClassArtinEquiv_primeClass {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal)
    (w : HeightOneSpectrum (𝓞 (𝔪.rayClassField Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    𝔪.rayClassArtinEquiv Ω (𝔪.primeClass hv) =
      arithFrobAt (𝓞 K) (𝔪.rayClassField Ω ≃ₐ[K] 𝔪.rayClassField Ω) w.asIdeal := by
  obtain ⟨π, hπ, hx, hxp⟩ := 𝔪.exists_uniformizer_finiteEmbedding_mem_idelesOneMod hv
  have hc : 𝔪.primeClass hv = QuotientGroup.mk ⟨toFractionalIdeal (finiteEmbedding v π),
      𝔪.toFractionalIdeal_mem_coprimeIdeals hx⟩ := by
    rw [primeClass]
    congr 2
    exact hxp.symm
  rw [hc, 𝔪.rayClassArtinEquiv_mk Ω hx, reciprocityMap_mk,
    ideleSymbol_finiteEmbedding_eq_arithFrobAt v w (𝔪.ramificationIdx_rayClassField_eq_one Ω hv w) hπ]

theorem splitsCompletely_rayClassField_iff {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔪.ideal) :
    SplitsCompletely (𝔪.rayClassField Ω) v ↔ 𝔪.primeClass hv = 1 := by
  obtain ⟨w, hw⟩ := nonempty_placesOver (𝔪.rayClassField Ω) v
  rw [splitsCompletely_iff_arithFrobAt_eq_one v (𝔪.unitFiltrationUnits_le_ker_localSymbol Ω hv) w,
    ← 𝔪.rayClassArtinEquiv_primeClass Ω hv w, MulEquiv.map_eq_one_iff]

end Modulus

theorem exists_le_rayClassField (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L] :
    ∃ 𝔪 : Modulus K, L ≤ 𝔪.rayClassField Ω := by
  obtain ⟨𝔪, -, hle⟩ := IdeleClassGroup.exists_map_congruenceSubgroup_le _
    (isOpen_range_ideleClassNorm (K := K) (L := L))
  refine ⟨𝔪, (range_ideleClassNorm_le_range_iff L (𝔪.rayClassField Ω)).1 ?_⟩
  rw [𝔪.range_ideleClassNorm_rayClassField Ω]
  exact hle

end

end Sec6_04_ClassFieldConsequences_RayClassField

/-! ### 05_ClassFieldConsequences.TrivialModulus -/
section Sec6_05_ClassFieldConsequences_TrivialModulus

open IsDedekindDomain NumberField IntermediateField IdeleGroup
  RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup SemiLocal
open RHDirect.CFT.LocalField (restrictAb le_maximalAbelianExtension)
open scoped nonZeroDivisors

noncomputable section

universe u

section Unramified

variable (K : Type*) [Field K] [NumberField K] (L : Type*) [Field L] [Algebra K L]

def IsUnramifiedEverywhere : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) ∧
    ∀ v : InfinitePlace K, v.IsUnramifiedIn L

variable [NumberField L]

theorem isUnramifiedIn_iff_ramificationIdx (v : HeightOneSpectrum (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
        w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  constructor
  · intro h w hw
    exact Ideal.ramificationIdx_eq_one_iff.2 (h w.asIdeal w.isPrime hw)
  · intro h P hP hPv
    have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    exact Ideal.ramificationIdx_eq_one_iff.1 (h ⟨P, hP, hne⟩ hPv)

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]

theorem infiniteLocalSymbol_eq_one_iff (v : InfinitePlace K) :
    infiniteLocalSymbol L v = 1 ↔ v.IsUnramifiedIn L := by
  by_cases hv : v.IsReal
  · constructor
    · intro h w hw
      have : w.LiesOver v := by
        subst hw
        exact ⟨rfl⟩
      by_contra hram
      have hneg : InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          ((-1 : (v.Completion)ˣ) : v.Completion) < 0 := by
        simp
      have h1 := infiniteLocalSymbol_apply L v hv ⟨w, this⟩ (-1)
      rw [h, if_pos hneg, MonoidHom.one_apply] at h1
      exact conjAt_ne_one hram h1.symm
    · intro h
      ext1 x
      obtain ⟨w⟩ := IdeleNorm.nonempty_infinitePlacesOver L v
      have := w.2
      have hc := NumberField.InfinitePlace.LiesOver.comap_eq (w : InfinitePlace L) v
      have hw : (w : InfinitePlace L).IsReal :=
        (NumberField.InfinitePlace.isUnramified_iff.1 (h _ hc)).resolve_right
          (by rw [hc]; exact NumberField.InfinitePlace.not_isComplex_iff_isReal.2 hv)
      rw [infiniteLocalSymbol_apply L v hv w, MonoidHom.one_apply, conjAt_of_isReal hw, ite_self]
  · rw [infiniteLocalSymbol_of_not_isReal L v hv]
    simp only [true_iff]
    intro w hw
    exact NumberField.InfinitePlace.isUnramified_iff.2
      (Or.inr (hw ▸ NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hv))

theorem units_le_ker_localSymbol_of_isUnramifiedIn (v : HeightOneSpectrum (𝓞 K))
    (h : Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  exact units_le_ker_localSymbol L v w ((isUnramifiedIn_iff_ramificationIdx K L v).1 h w.1 w.2)

theorem ideleSymbol_eq_one_of_isUnramifiedEverywhere (h : IsUnramifiedEverywhere K L)
    {x : IdeleGroup K} (hx : ∀ v, finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units) :
    ideleSymbol K L x = 1 := by
  have hN : ∀ v, (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤ (localSymbol L v).ker :=
    fun v ↦ units_le_ker_localSymbol_of_isUnramifiedIn K L v (h.1 v)
  have hNinf : ∀ w : InfinitePlace K, (⊤ : Subgroup (w.Completion)ˣ) ≤ (infiniteLocalSymbol L w).ker := by
    intro w
    rw [(infiniteLocalSymbol_eq_one_iff K L w).2 (h.2 w), MonoidHom.ker_one]
  have h1 : ∀ v, localSymbol L v (finiteProj v x) = 1 := fun v ↦ hN v (hx v)
  have h2 : ∀ w, infiniteLocalSymbol L w (infiniteProj w x) = 1 := fun w ↦ hNinf w (Subgroup.mem_top _)
  rw [ideleSymbol_apply]
  simp only [h1, h2, finprod_one, Finset.prod_const_one, mul_one]

end Unramified

section Descent

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem IsUnramifiedEverywhere.of_le {E M : IntermediateField K Ω} (hEM : E ≤ M) [FiniteDimensional K M]
    (hM : IsUnramifiedEverywhere K M) : IsUnramifiedEverywhere K E := by
  refine ⟨fun v ↦ ProfCoh.isUnramifiedIn_of_le hEM v (hM.1 v), fun v w hw ↦ ?_⟩
  have : FiniteDimensional K E := ProfCoh.finiteDimensional_of_le hEM
  let _ : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  have : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite E M := Module.Finite.of_restrictScalars_finite K E M
  obtain ⟨w', rfl⟩ := NumberField.InfinitePlace.comap_surjective (K := M) w
  rw [NumberField.InfinitePlace.isUnramified_iff]
  by_cases hv : v.IsReal
  · left
    have hc : w'.comap (algebraMap K M) = v := by
      rw [IsScalarTower.algebraMap_eq K E M, NumberField.InfinitePlace.comap_comp, hw]
    have hw'r : w'.IsReal := (NumberField.InfinitePlace.isUnramified_iff.1 (hM.2 v w' hc)).resolve_right
      (by rw [hc]; exact NumberField.InfinitePlace.not_isComplex_iff_isReal.2 hv)
    exact hw'r.comap _
  · right
    rw [hw]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.1 hv

end Descent

variable {K : Type u} [Field K] [NumberField K]

namespace Modulus

def one : Modulus K :=
  ⟨⊤, top_ne_bot, ∅⟩

theorem not_dvd_one_ideal (v : HeightOneSpectrum (𝓞 K)) : ¬ v.asIdeal ∣ (one : Modulus K).ideal := by
  change ¬ v.asIdeal ∣ ⊤
  rw [Ideal.dvd_iff_le]
  exact fun h ↦ v.isPrime.ne_top (top_le_iff.1 h)

theorem idelesOneMod_one : (one : Modulus K).idelesOneMod = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ one.mem_idelesOneMod.2
    ⟨fun v hv ↦ (not_dvd_one_ideal v hv).elim, fun _ hw ↦ hw.elim⟩

theorem congruenceSubgroup_one : (one : Modulus K).congruenceSubgroup = standardOpenSubgroup K := by
  rw [congruenceSubgroup_eq_inf, idelesOneMod_one, top_inf_eq]

theorem coprimeIdeals_one : (one : Modulus K).coprimeIdeals = ⊤ :=
  eq_top_iff.2 fun _ _ v hv ↦ (not_dvd_one_ideal v hv).elim

theorem rayUnits_one : (one : Modulus K).rayUnits = ⊤ := by
  rw [rayUnits, idelesOneMod_one, Subgroup.comap_top]

theorem classGroup_mk_eq_one_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  rw [← (ClassGroup.equiv K).injective.eq_iff, ClassGroup.equiv_mk, map_one,
    FractionalIdeal.canonicalEquiv_self, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Iff.rfl

def toClassGroup : (one : Modulus K).coprimeIdeals →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (one : Modulus K).coprimeIdeals.subtype

theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) := by
  intro c
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  refine ⟨⟨FractionalIdeal.mk0 K I, by rw [coprimeIdeals_one]; trivial⟩, ?_⟩
  exact ClassGroup.mk_mk0 (K := K) I

theorem ker_toClassGroup : (toClassGroup (K := K)).ker = (one : Modulus K).principalRay := by
  ext I
  rw [MonoidHom.mem_ker, toClassGroup, MonoidHom.comp_apply, Subgroup.coe_subtype,
    classGroup_mk_eq_one_iff, mem_principalRay, rayUnits_one, MonoidHom.mem_range]
  simp only [Subgroup.mem_top, true_and]

def classGroupEquiv : (one : Modulus K).IdealRayClassGroup ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_toClassGroup.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)

theorem classGroupEquiv_mk (I : (one : Modulus K).coprimeIdeals) :
    classGroupEquiv (QuotientGroup.mk I) = ClassGroup.mk K (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
  rfl

theorem classGroupEquiv_primeClass (v : HeightOneSpectrum (𝓞 K)) :
    classGroupEquiv (one.primeClass (not_dvd_one_ideal v)) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  rw [primeClass, classGroupEquiv_mk, ← ClassGroup.mk_mk0 (K := K)]
  congr 1

end Modulus

end

end Sec6_05_ClassFieldConsequences_TrivialModulus

/-! ### 06_ClassFieldConsequences.HilbertClassField -/
section Sec6_06_ClassFieldConsequences_HilbertClassField

open IsDedekindDomain NumberField IntermediateField IdeleGroup
  RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup SemiLocal
open RHDirect.CFT.LocalField (restrictAb le_maximalAbelianExtension)
open scoped nonZeroDivisors

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

abbrev hilbertClassField : IntermediateField K Ω :=
  (Modulus.one : Modulus K).rayClassField Ω

instance finiteDimensional_hilbertClassField : FiniteDimensional K (hilbertClassField K Ω) :=
  inferInstanceAs (FiniteDimensional K ((Modulus.one : Modulus K).rayClassField Ω))

instance isAbelianGalois_hilbertClassField : IsAbelianGalois K (hilbertClassField K Ω) :=
  inferInstanceAs (IsAbelianGalois K ((Modulus.one : Modulus K).rayClassField Ω))

theorem range_ideleClassNorm_hilbertClassField :
    (ideleClassNorm K (hilbertClassField K Ω)).range =
      (standardOpenSubgroup K).map (IdeleClassGroup.mk K) := by
  rw [← Modulus.congruenceSubgroup_one]
  exact (Modulus.one : Modulus K).range_ideleClassNorm_rayClassField Ω

theorem isUnramifiedEverywhere_hilbertClassField :
    IsUnramifiedEverywhere K (hilbertClassField K Ω) := by
  refine ⟨fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [isUnramifiedIn_iff_ramificationIdx]
    intro w hw
    have := hw
    exact (Modulus.one : Modulus K).ramificationIdx_rayClassField_eq_one Ω
      (Modulus.not_dvd_one_ideal v) w
  · rw [← infiniteLocalSymbol_eq_one_iff]
    ext1 x
    have hx : IdeleClassGroup.mk K (infiniteEmbedding v x) ∈
        (ideleClassNorm K (hilbertClassField K Ω)).range := by
      rw [range_ideleClassNorm_hilbertClassField]
      exact ⟨_, infiniteEmbedding_mem_standardOpenSubgroup v x, rfl⟩
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk,
      ideleSymbol_infiniteEmbedding] at hx
    rw [hx, MonoidHom.one_apply]

theorem le_hilbertClassField_iff (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    L ≤ hilbertClassField K Ω ↔ IsUnramifiedEverywhere K L := by
  constructor
  · intro hle
    exact (isUnramifiedEverywhere_hilbertClassField K Ω).of_le hle
  · intro h
    refine (range_ideleClassNorm_le_range_iff L (hilbertClassField K Ω)).1 ?_
    rw [range_ideleClassNorm_hilbertClassField]
    rintro _ ⟨x, hx, rfl⟩
    rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_mk]
    refine ideleSymbol_eq_one_of_isUnramifiedEverywhere K L h fun v ↦ ?_
    have hx' : x ∈ (Modulus.one : Modulus K).congruenceSubgroup := by
      rw [Modulus.congruenceSubgroup_one]
      exact hx
    have hv := ((Modulus.one : Modulus K).mem_congruenceSubgroup.1 hx').1 v
    rw [(Modulus.exponent_eq_zero_iff _ v).2 (Modulus.not_dvd_one_ideal v), unitsLevel_zero] at hv
    exact hv

def hilbertClassFieldArtinEquiv :
    ClassGroup (𝓞 K) ≃* (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) :=
  Modulus.classGroupEquiv.symm.trans ((Modulus.one : Modulus K).rayClassArtinEquiv Ω)

theorem hilbertClassFieldArtinEquiv_mk0 (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 (hilbertClassField K Ω))) [w.asIdeal.LiesOver v.asIdeal] :
    hilbertClassFieldArtinEquiv K Ω
        (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) =
      arithFrobAt (𝓞 K) (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) w.asIdeal := by
  change (Modulus.one : Modulus K).rayClassArtinEquiv Ω (Modulus.classGroupEquiv.symm
    (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)) = _
  rw [← Modulus.classGroupEquiv_primeClass v, MulEquiv.symm_apply_apply]
  exact (Modulus.one : Modulus K).rayClassArtinEquiv_primeClass Ω (Modulus.not_dvd_one_ideal v) w

end

end Sec6_06_ClassFieldConsequences_HilbertClassField

end RHDirect.CFT.Global
