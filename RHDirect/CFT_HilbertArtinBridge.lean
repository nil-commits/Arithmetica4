import RHDirect.CFT_HilbertClassField
import RHDirect.Stage13GL_KummerDuality

/-!
# RHDirect.CFT_HilbertArtinBridge

Unconditional zero-parameter bridge from our standalone Global Class Field Theory &
Hilbert Class Field formalization (`RHDirect.CFT_HilbertClassField`) to
`RHDirect.Stage13GL_KummerDuality.HilbertArtinData K Ω`, discharging the sole remaining
assumption of `Stage13GL_KummerDuality` (`hilbertArtinData_unconditional`,
`shaLen_le_of_cl_unconditional`, `plusLen_le_of_cl_unconditional`,
`minusLen_le_of_cl_unconditional`).

Note: All 15 core Global CFT modules (`Stage13CFT_IdeleNormResidue` through
`CFT_HilbertClassField`) compile 100% standalone on pure Mathlib `v4.33.1`.
This optional bridge module additionally imports `RHDirect.Stage13GL_KummerDuality`.
-/

noncomputable section

namespace RHDirect.CFT.Global

open RHDirect.Stage13CFT_IdeleNormResidue
open RHDirect.CFT_ProfiniteSemilocal

/-! ### 07_HilbertArtinDataBridge (Crown Jewel Bridge to `Stage13GL_KummerDuality`) -/
section Sec6_07_HilbertArtinDataBridge

open NumberField IsDedekindDomain IntermediateField
open RHDirect.Stage12GaloisShaLen RHDirect.Stage13GL_GaloisCohomLength
  RHDirect.Stage13GL_SelmerTransport RHDirect.Stage13GL_KummerDuality
open scoped nonZeroDivisors

noncomputable section

private theorem hilbertClassField_locConst
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω] :
    IsLocallyConstant
      ((hilbertClassFieldArtinEquiv K Ω).symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω))) := by
  have hcont : Continuous (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω)) :=
    InfiniteGalois.restrictNormalHom_continuous (hilbertClassField K Ω)
  have hlc : IsLocallyConstant
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω)) :=
    (IsLocallyConstant.iff_continuous _).2 hcont
  exact hlc.comp (hilbertClassFieldArtinEquiv K Ω).symm

private theorem hilbertClassField_ine_eq_one
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (hg : g ∈ Ine (F := K) A) :
    (hilbertClassFieldArtinEquiv K Ω).symm
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω) g) = 1 := by
  set H : IntermediateField K Ω := hilbertClassField K Ω
  have : FiniteDimensional K H := inferInstance
  have : IsAbelianGalois K H := inferInstance
  have : NumberField H := NumberField.of_module_finite K H
  have hUnramH : IsUnramifiedEverywhere K H := isUnramifiedEverywhere_hilbertClassField K Ω
  rw [MulEquiv.map_eq_one_iff]
  by_cases hA : A = ⊤
  · subst hA
    have hg1 : g = 1 := by
      have hbot : Ine (F := K) (⊤ : ValuationSubring Ω) = ⊥ := (placeDict K Ω).1
      rw [hbot, Subgroup.mem_bot] at hg
      exact hg
    rw [hg1, map_one]
  · obtain ⟨v, hAv⟩ := (placeDict K Ω).2.1 A hA
    obtain ⟨w, hwA, hwv⟩ := place_between (L := H) hAv
    have : w.asIdeal.LiesOver v.asIdeal := hwv
    have hmem : AlgEquiv.restrictNormalHom H g ∈ w.asIdeal.inertia (H ≃ₐ[K] H) := by
      intro x
      refine (hwA _).mp ?_
      have hcoe : algebraMap H Ω ((AlgEquiv.restrictNormalHom H g • x : 𝓞 H) : H) =
          g (algebraMap H Ω (x : H)) :=
        AlgEquiv.restrictNormal_commutes g H (x : H)
      have hxle : A.valuation (algebraMap H Ω (x : H)) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr
          (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)
      have hsub : algebraMap H Ω ((AlgEquiv.restrictNormalHom H g • x - x : 𝓞 H) : H) =
          g (algebraMap H Ω (x : H)) - algebraMap H Ω (x : H) := by
        change algebraMap H Ω (((AlgEquiv.restrictNormalHom H g • x : 𝓞 H) : H) - (x : H)) = _
        rw [map_sub, hcoe]
      rw [hsub]
      exact hg.2 _ hxle
    have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
      (isUnramifiedIn_iff_ramificationIdx K H v).1 (hUnramH.1 v) w hwv
    have hbot : w.asIdeal.inertia (H ≃ₐ[K] H) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ ((natCard_inertia v w).trans he)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem

private theorem hilbertClassField_conj_eq_one
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (c : G K Ω) (hc : IsConjOm c.toRingEquiv) :
    (hilbertClassFieldArtinEquiv K Ω).symm
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω) c) = 1 := by
  set H : IntermediateField K Ω := hilbertClassField K Ω
  have : FiniteDimensional K H := inferInstance
  have : IsAbelianGalois K H := inferInstance
  have : NumberField H := NumberField.of_module_finite K H
  have hUnramH : IsUnramifiedEverywhere K H := isUnramifiedEverywhere_hilbertClassField K Ω
  obtain ⟨j, hj⟩ := hc
  rw [MulEquiv.map_eq_one_iff]
  let jH : H →+* ℂ := j.comp (algebraMap H Ω)
  let jK : K →+* ℂ := jH.comp (algebraMap K H)
  have hjK_eq : jK = j.comp (algebraMap K Ω) := by
    ext x
    change j (algebraMap H Ω (algebraMap K H x)) = j (algebraMap K Ω x)
    rw [← IsScalarTower.algebraMap_apply K H Ω]
  have hKreal : ComplexEmbedding.IsReal jK := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [RingHom.comp_apply, hjK_eq, RingHom.comp_apply]
    have hcx := hj (algebraMap K Ω x)
    rw [show c.toRingEquiv (algebraMap K Ω x) = algebraMap K Ω x from c.commutes x] at hcx
    exact hcx.symm
  let w : InfinitePlace H := InfinitePlace.mk jH
  let v : InfinitePlace K := InfinitePlace.mk jK
  have hwv : w.comap (algebraMap K H) = v := rfl
  have hvreal : v.IsReal := (InfinitePlace.isReal_mk_iff).2 hKreal
  have hwreal : w.IsReal :=
    (InfinitePlace.isUnramified_iff.1 (hUnramH.2 v w hwv)).resolve_right
      (by rw [hwv]; exact InfinitePlace.not_isComplex_iff_isReal.2 hvreal)
  have hjHreal : ComplexEmbedding.IsReal jH := (InfinitePlace.isReal_mk_iff).1 hwreal
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have hcoe : ((AlgEquiv.restrictNormalHom H c x : H) : Ω) = c (x : Ω) :=
    AlgEquiv.restrictNormal_commutes c H x
  rw [hcoe, AlgEquiv.one_apply]
  apply j.injective
  exact (hj (x : Ω)).trans (DFunLike.congr_fun (ComplexEmbedding.isReal_iff.1 hjHreal) x)

private theorem hilbertClassField_frob
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω)
    (hAv : IsPlaceOver A v) (hFrob : IsFrob (F := K) A (normV v) σ) :
    (hilbertClassFieldArtinEquiv K Ω).symm
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω) σ) = primeCl v := by
  set H : IntermediateField K Ω := hilbertClassField K Ω
  have : FiniteDimensional K H := inferInstance
  have : IsAbelianGalois K H := inferInstance
  have : NumberField H := NumberField.of_module_finite K H
  have hUnramH : IsUnramifiedEverywhere K H := isUnramifiedEverywhere_hilbertClassField K Ω
  obtain ⟨w, hwA, hwv⟩ := place_between (L := H) hAv
  have : w.asIdeal.LiesOver v.asIdeal := hwv
  have hAf : IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom H σ) w.asIdeal := res_frob hwA hFrob
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    (isUnramifiedIn_iff_ramificationIdx K H v).1 (hUnramH.1 v) w hwv
  have hbot : w.asIdeal.inertia (H ≃ₐ[K] H) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ ((natCard_inertia v w).trans he)
  have hmem := hAf.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) (H ≃ₐ[K] H) w.asIdeal)
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  change (hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom H σ) = primeCl v
  rw [hmem, MulEquiv.symm_apply_eq]
  exact (hilbertClassFieldArtinEquiv_mk0 K Ω v w).symm

private theorem hilbertClassField_ker_le
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (C : Type) [CommGroup C] (χ : G K Ω →* C)
    (hOpen : IsOpen (χ.ker : Set (G K Ω)))
    (hIne : ∀ A : ValuationSubring Ω, Ine (F := K) A ≤ χ.ker)
    (hConj : ∀ c : G K Ω, IsConjOm c.toRingEquiv → χ c = 1) :
    ((hilbertClassFieldArtinEquiv K Ω).symm.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω))).ker ≤ χ.ker := by
  set H : IntermediateField K Ω := hilbertClassField K Ω
  have : FiniteDimensional K H := inferInstance
  have : IsAbelianGalois K H := inferInstance
  have : NumberField H := NumberField.of_module_finite K H
  let Ucl : ClosedSubgroup (G K Ω) := ⟨χ.ker, χ.ker.isClosed_of_isOpen hOpen⟩
  let L : IntermediateField K Ω := IntermediateField.fixedField χ.ker
  have hfix : L.fixingSubgroup = χ.ker := InfiniteGalois.fixingSubgroup_fixedField Ucl
  have : FiniteDimensional K L :=
    (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hOpen)
  have : IsGalois K L := IsGalois.of_fixedField_normal_subgroup χ.ker
  have : NumberField L := NumberField.of_module_finite K L
  have : IsMulCommutative (L ≃ₐ[K] L) := by
    refine ⟨⟨fun σ τ ↦ ?_⟩⟩
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
    have hcomm : (σ' * τ') * (τ' * σ')⁻¹ ∈ χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, mul_comm (χ τ') (χ σ'),
        mul_inv_cancel]
    rw [← hfix] at hcomm
    have h1 : AlgEquiv.restrictNormalHom L ((σ' * τ') * (τ' * σ')⁻¹) = 1 := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      have hcoe : ((AlgEquiv.restrictNormalHom L ((σ' * τ') * (τ' * σ')⁻¹) x : L) : Ω) =
          ((σ' * τ') * (τ' * σ')⁻¹) (x : Ω) :=
        AlgEquiv.restrictNormal_commutes ((σ' * τ') * (τ' * σ')⁻¹) L x
      rw [hcoe, AlgEquiv.one_apply]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hcomm x x.2
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    simpa only [map_mul] using h1
  have : IsAbelianGalois K L := {}
  have hUnramL : IsUnramifiedEverywhere K L := by
    refine ⟨fun v ↦ ?_, fun v w hw ↦ ?_⟩
    · rw [isUnramifiedIn_iff_ramificationIdx]
      intro w hwv
      have : w.asIdeal.LiesOver v.asIdeal := hwv
      rw [← natCard_inertia v w]
      have hbot : w.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ := by
        rw [eq_bot_iff]
        intro τ hτ
        obtain ⟨A, φ, hφL, hφI⟩ := lift_ine_over L w τ hτ
        have hφK : φ ∈ L.fixingSubgroup := hfix.symm ▸ hIne A hφI
        rw [Subgroup.mem_bot, ← hφL]
        apply AlgEquiv.ext
        intro x
        apply Subtype.ext
        have hcoe : ((AlgEquiv.restrictNormalHom L φ x : L) : Ω) = φ (x : Ω) :=
          AlgEquiv.restrictNormal_commutes φ L x
        rw [hcoe, AlgEquiv.one_apply]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hφK x x.2
      rw [hbot]
      exact Nat.card_unique
    · rw [InfinitePlace.isUnramified_iff]
      by_cases hv : v.IsReal
      · left
        have hKreal : ComplexEmbedding.IsReal (w.embedding.comp (algebraMap K L)) := by
          rw [← InfinitePlace.isReal_mk_iff]
          have hmk : InfinitePlace.mk (w.embedding.comp (algebraMap K L)) = v := by
            rw [← hw]
            conv_rhs => rw [← InfinitePlace.mk_embedding w]
            rfl
          rwa [hmk]
        obtain ⟨c, hcConj, hcFix⟩ := exists_conj_lift L w.embedding hKreal
        have hcMem : c ∈ L.fixingSubgroup := by
          rw [hfix, MonoidHom.mem_ker]
          exact hConj c hcConj
        have hLreal : ComplexEmbedding.IsReal w.embedding := by
          rw [ComplexEmbedding.isReal_iff]
          ext x
          exact hcFix x ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hcMem x x.2)
        rw [← InfinitePlace.mk_embedding w, InfinitePlace.isReal_mk_iff]
        exact hLreal
      · right
        rw [hw]
        exact InfinitePlace.not_isReal_iff_isComplex.1 hv
  have hLH : L ≤ H := (le_hilbertClassField_iff K Ω L).2 hUnramL
  intro g hg
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff] at hg
  have hgH : g ∈ H.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hcoe : ((AlgEquiv.restrictNormalHom H g ⟨x, hx⟩ : H) : Ω) = g x :=
      AlgEquiv.restrictNormal_commutes g H ⟨x, hx⟩
    rw [← hcoe, hg, AlgEquiv.one_apply]
  rw [← hfix]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hgH x (hLH hx)

/-- **CROWN JEWEL BRIDGE**: Unconditional, zero-parameter construction of
`RHDirect.Stage13GL_KummerDuality.HilbertArtinData K Ω` from Global Class Field Theory and the
Hilbert Class Field (`hilbertClassField K Ω` & `hilbertClassFieldArtinEquiv K Ω`). -/
def hilbertArtinData_unconditional
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    RHDirect.Stage13GL_KummerDuality.HilbertArtinData K Ω :=
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsGalois K Ω := ⟨⟩
  { artCl := (hilbertClassFieldArtinEquiv K Ω).symm.toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (hilbertClassField K Ω))
    surj := (hilbertClassFieldArtinEquiv K Ω).symm.surjective.comp
      (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := hilbertClassField K Ω) (E := Ω))
    locConst := hilbertClassField_locConst K Ω
    ine_eq_one := hilbertClassField_ine_eq_one K Ω
    conj_eq_one := hilbertClassField_conj_eq_one K Ω
    frob := hilbertClassField_frob K Ω
    ker_le := hilbertClassField_ker_le K Ω }

/-! #### Unconditional downstream corollaries for `Stage13GL_KummerDuality` -/

theorem shaLen_le_of_cl_unconditional
    {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (D : LData F Ω l) {e : ℤ} (he : e ≠ 0) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEq (Fn F Ω l n) l (qzG F Ω l e)) ≤ Bd) :
    shaLen D e ≤ Bd + errTwo l :=
  shaLen_le_of_cl (fun n ↦ hilbertArtinData_unconditional (Fn F Ω l n) Ω) D he Bd hB

theorem plusLen_le_of_cl_unconditional
    {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ)
    (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEig (Fn F Ω l n) l (qzG F Ω l e) σ 1) ≤ Bd) :
    plusLen D e ≤ Bd + errTwo l :=
  plusLen_le_of_cl (fun n ↦ hilbertArtinData_unconditional (Fn F Ω l n) Ω) D he hσ Bd hB

theorem minusLen_le_of_cl_unconditional
    {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ)
    (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEig (Fn F Ω l n) l (qzG F Ω l e) σ (-1)) ≤ Bd) :
    minusLen D e ≤ Bd + errTwo l :=
  minusLen_le_of_cl (fun n ↦ hilbertArtinData_unconditional (Fn F Ω l n) Ω) D he hσ Bd hB

end

end Sec6_07_HilbertArtinDataBridge

end RHDirect.CFT.Global
