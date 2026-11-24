import RHDirect.CFT_GlobalCompletion
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# RHDirect.CFT_GlobalInequalities

Global Class Field Theory Pillar — Global Kummer Theory, Local/Global Power Subgroup Indices,
Global Second Inequality, and Exact Cyclic Norm Index Equality:
1. Global Kummer theory (`KummerTheory.Degree`, `Unramified`, `SplittingInfinite`,
   `SplittingKummer`, `LocalIndex`, `LocalIndexAtPlace`).
2. Global power subgroup indices (`ExistenceTheorem.PowerIndex`, `LocalPowers`,
   `IndexRangePowMonoidHomAdicCompletionMulNorm`, `KummerIndexLemma.*`,
   `PowerSubgroupIndex.Existence`).
3. **Global Second Inequality** (`SecondInequality.*`: `SecondInequalityRoots`,
   `SecondInequality`, `secondInequality`): `[I_K : Kˣ N_{L/K}(I_L)] ≤ [L : K]` for every
   finite cyclic extension `L / K` of number fields.
4. **Exact Cyclic Norm Index Equality & Class Field Axioms**
   (`index_range_ideleClassNorm_eq_finrank`, `natCard_cycTateNegOne_ideleClassGroup`,
   `natCard_cycTateZero_ideleClassGroup_eq_finrank`, `classFieldAxiom_ideleClassGroup`):
   `[I_K : Kˣ N_{L/K}(I_L)] = [L : K]`, `|H⁰(G, C_L)| = [L : K]`, and `|H⁻¹(G, C_L)| = 1`.
-/

noncomputable section

namespace RHDirect.CFT.Global

open RHDirect.Stage13CFT_IdeleNormResidue
open RHDirect.CFT_ProfiniteSemilocal

/-! ### 01_KummerTheory.Degree -/
section Sec2_01_KummerTheory_Degree

open RHDirect.CFT_ProfiniteSemilocal.ProfCoh IntermediateField

section Radicals

variable (K : Type*) [Field K] (n : ℕ)

def radicalClasses (Δ : Subgroup Kˣ) : Subgroup (UnitsModPow K n) :=
  Δ.map (QuotientGroup.mk' (unitsPow K n))

noncomputable def toRadicalClasses (Δ : Subgroup Kˣ) : Δ →* radicalClasses K n Δ :=
  ((QuotientGroup.mk' (unitsPow K n)).comp Δ.subtype).codRestrict _
    (fun a => Subgroup.mem_map_of_mem _ a.2)

lemma toRadicalClasses_surjective (Δ : Subgroup Kˣ) :
    Function.Surjective (toRadicalClasses K n Δ) := by
  rintro ⟨x, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

lemma ker_toRadicalClasses (Δ : Subgroup Kˣ) :
    (toRadicalClasses K n Δ).ker = (unitsPow K n).subgroupOf Δ := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff (N := unitsPow K n)]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

noncomputable def radicalQuotientEquiv (Δ : Subgroup Kˣ) :
    (Δ ⧸ (unitsPow K n).subgroupOf Δ) ≃* radicalClasses K n Δ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toRadicalClasses K n Δ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toRadicalClasses_surjective K n Δ))

@[simp] lemma radicalQuotientEquiv_mk (Δ : Subgroup Kˣ) (a : Δ) :
    (radicalQuotientEquiv K n Δ (a : Δ ⧸ (unitsPow K n).subgroupOf Δ) : UnitsModPow K n) =
      ((a : Kˣ) : UnitsModPow K n) :=
  rfl

def kummerExtension (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ) :
    IntermediateField K Ω :=
  adjoin K {α : Ω | ∃ a ∈ Δ, α ^ n = algebraMap K Ω a}

theorem kummerExtension_eq_kummerField (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ) :
    kummerExtension K n Ω Δ = kummerField K n Ω (radicalClasses K n Δ) := by
  apply le_antisymm
  · rw [kummerExtension, adjoin_le_iff]
    rintro α ⟨a, ha, hα⟩
    exact subset_adjoin _ _ ⟨a, Subgroup.mem_map_of_mem _ ha, hα⟩
  · rw [kummerField, adjoin_le_iff]
    rintro α ⟨a, ⟨b, hb, hab⟩, hα⟩

    obtain ⟨c, hc⟩ := mem_unitsPow.mp (QuotientGroup.eq.mp hab)
    have hc0 : algebraMap K Ω (c : K) ≠ 0 := (map_ne_zero (algebraMap K Ω)).mpr c.ne_zero
    have ha : (a : K) = (b : K) * (c : K) ^ n := by
      have h1 : (c : K) ^ n = (b : K)⁻¹ * (a : K) := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
          using congrArg Units.val hc
      rw [h1, ← mul_assoc, mul_inv_cancel₀ b.ne_zero, one_mul]
    have hβ : (α / algebraMap K Ω (c : K)) ^ n = algebraMap K Ω (b : K) := by
      rw [div_pow, hα, ha, map_mul, map_pow]
      field_simp
    have hmem : α / algebraMap K Ω (c : K) ∈ kummerExtension K n Ω Δ :=
      subset_adjoin _ _ ⟨b, hb, hβ⟩
    have : α = α / algebraMap K Ω (c : K) * algebraMap K Ω (c : K) := by field_simp
    rw [SetLike.mem_coe, this]
    exact mul_mem hmem (IntermediateField.algebraMap_mem _ _)

end Radicals

section Main

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ)

instance kummerExtension_isGalois : IsGalois K (kummerExtension K n Ω Δ) := by
  rw [kummerExtension_eq_kummerField]
  exact kummerField_isGalois K n Ω _

instance kummerExtension_isMulCommutative : IsMulCommutative Gal(kummerExtension K n Ω Δ/K) := by
  rw [kummerExtension_eq_kummerField]
  exact kummerField_isMulCommutative K n Ω _

theorem kummerExtension_exponent_dvd : Monoid.exponent Gal(kummerExtension K n Ω Δ/K) ∣ n := by
  rw [kummerExtension_eq_kummerField]
  exact kummerField_exponent_dvd K n Ω _

instance finite_radicalClasses [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)] :
    Finite (radicalClasses K n Δ) :=
  Finite.of_equiv _ (radicalQuotientEquiv K n Δ).toEquiv

variable [IsSepClosed Ω]

theorem kummerGroup_kummerExtension :
    kummerGroup K n (kummerExtension K n Ω Δ) = radicalClasses K n Δ := by
  rw [kummerExtension_eq_kummerField]
  exact kummerGroup_kummerField K n Ω _

theorem unitsPowIn_kummerExtension (hΔ : unitsPow K n ≤ Δ) :
    unitsPowIn K n (kummerExtension K n Ω Δ) = Δ := by
  have h1 : (QuotientGroup.mk' (unitsPow K n)).ker ≤ unitsPowIn K n (kummerExtension K n Ω Δ) := by
    rw [QuotientGroup.ker_mk']
    exact unitsPow_le_unitsPowIn K n _
  have h2 : (QuotientGroup.mk' (unitsPow K n)).ker ≤ Δ := by
    rw [QuotientGroup.ker_mk']
    exact hΔ
  calc unitsPowIn K n (kummerExtension K n Ω Δ)
      = (kummerGroup K n (kummerExtension K n Ω Δ)).comap (QuotientGroup.mk' (unitsPow K n)) :=
        (Subgroup.comap_map_eq_self h1).symm
    _ = (radicalClasses K n Δ).comap (QuotientGroup.mk' (unitsPow K n)) := by
        rw [kummerGroup_kummerExtension]
    _ = Δ := Subgroup.comap_map_eq_self h2

variable [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]

instance kummerExtension_finiteDimensional : FiniteDimensional K (kummerExtension K n Ω Δ) := by
  rw [kummerExtension_eq_kummerField]
  exact finiteDimensional_kummerField K n Ω _

theorem finrank_kummerExtension :
    Module.finrank K (kummerExtension K n Ω Δ) = Nat.card (Δ ⧸ (unitsPow K n).subgroupOf Δ) := by
  rw [kummerExtension_eq_kummerField, finrank_kummerField,
    Nat.card_congr (radicalQuotientEquiv K n Δ).toEquiv]

noncomputable def radicalQuotientEquivKummerGroup :
    (Δ ⧸ (unitsPow K n).subgroupOf Δ) ≃* kummerGroup K n (kummerExtension K n Ω Δ) :=
  (radicalQuotientEquiv K n Δ).trans
    (MulEquiv.subgroupCongr (kummerGroup_kummerExtension K n Ω Δ).symm)

noncomputable def kummerExtensionGalEquiv :
    Gal(kummerExtension K n Ω Δ/K) ≃* ((Δ ⧸ (unitsPow K n).subgroupOf Δ) →* rootsOfUnity n K) :=
  (galEquivDual K n (kummerExtension K n Ω Δ) (kummerExtension_exponent_dvd K n Ω Δ)).trans
    (MulEquiv.monoidHomCongrLeft (radicalQuotientEquivKummerGroup K n Ω Δ).symm)

end Main

section Converse

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω]

end Converse

end Sec2_01_KummerTheory_Degree

/-! ### 02_KummerTheory.Unramified -/
section Sec2_02_KummerTheory_Unramified

open NumberField IsDedekindDomain Polynomial

namespace Kummer

variable {K : Type*} [Field K] [NumberField K]

theorem exists_mul_pow_integral_notMem (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (a : Kˣ) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    ∃ c : K, c ≠ 0 ∧ ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = a * c ^ n ∧ b ∉ v.asIdeal := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have ha0 : v.valuation K (a : K) ≠ 0 := by simp
  set a' : K := a * (π ^ m) ^ n with ha'
  have hva' : v.valuation K a' = 1 := by
    rw [ha', map_mul, map_pow, map_zpow₀, hπ, ← WithZero.exp_log ha0, hm]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    simp
  obtain ⟨r, d, hrd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) a' hva'.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.prop
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h
    apply hd
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h]
    exact zero_mem _
  refine ⟨π ^ m * algebraMap (𝓞 K) K d, mul_ne_zero (zpow_ne_zero _ hπ0) hdK,
    r * d ^ (n - 1), ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, ha']
    ring
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v]
    have h1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v).mpr hd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, map_mul, map_mul, map_pow, hva', h1]
    simp

variable {M : Type*} [Field M] [NumberField M] [Algebra K M]

theorem isUnramifiedAt_of_pow_eq {n : ℕ} (a : Kˣ) {α : M} (hα : α ^ n = algebraMap K M a)
    (hgen : IntermediateField.adjoin K {α} = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnv (by simp)
  obtain ⟨c, hc, b, hb, hbv⟩ := exists_mul_pow_integral_notMem v hn a hav
  set x : M := algebraMap K M c * α with hx
  have hxn : x ^ n = algebraMap K M (algebraMap (𝓞 K) K b) := by
    rw [hx, mul_pow, hα, hb, map_mul, map_pow]
    ring
  have hxint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hxn]
    exact b.isIntegral_coe.algebraMap
  let y : 𝓞 M := ⟨x, hxint⟩
  have hyx : algebraMap (𝓞 M) M y = x := rfl
  have hyb : y ^ n = algebraMap (𝓞 K) (𝓞 M) b := by
    apply FaithfulSMul.algebraMap_injective (𝓞 M) M
    rw [map_pow, hyx, hxn, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]
  have hKx : IntermediateField.adjoin K {x} = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    have : α = algebraMap K M c⁻¹ * x := by
      rw [hx, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self K x)
  have hgen' : Algebra.adjoin K {algebraMap (𝓞 M) M y} = ⊤ := by
    rw [hyx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), hKx, IntermediateField.top_toSubalgebra]
  have hyint : IsIntegral (𝓞 K) y := Algebra.IsIntegral.isIntegral y
  obtain ⟨g, hg⟩ : minpoly (𝓞 K) y ∣ X ^ n - C b :=
    minpoly.isIntegrallyClosed_dvd hyint (by simp [hyb])
  have hder : aeval y (derivative (minpoly (𝓞 K) y)) * aeval y g = (n : 𝓞 M) * y ^ (n - 1) := by
    have := congrArg (fun p => aeval y (derivative p)) hg
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add,
      map_mul, minpoly.aeval, zero_mul, add_zero] at this
    rw [← this]
    simp
  have hnP : (n : 𝓞 M) ∉ P := by
    intro h
    apply hnv
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    simpa using h
  have hyP : y ∉ P := by
    intro h
    apply hbv
    have : algebraMap (𝓞 K) (𝓞 M) b ∈ P :=
      hyb ▸ Ideal.pow_mem_of_mem P h n (Nat.pos_of_ne_zero hn)
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    exact this
  have hfP : aeval y (derivative (minpoly (𝓞 K) y)) ∉ P := by
    intro h
    have : (n : 𝓞 M) * y ^ (n - 1) ∈ P := hder ▸ Ideal.mul_mem_right _ P h
    rcases Ideal.IsPrime.mem_or_mem ‹_› this with h1 | h1
    · exact hnP h1
    · exact hyP (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h1)
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M y hgen'
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact hfP (Ideal.le_of_dvd hdvd hmem)

theorem ramificationIdx_eq_one_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    P.ramificationIdx (𝓞 K) = 1 := by
  have := isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

theorem isUnramifiedIn_of_pow_eq {n : ℕ} (a : Kˣ) {α : M}
    (hα : α ^ n = algebraMap K M a) (hgen : IntermediateField.adjoin K {α} = ⊤)
    (v : HeightOneSpectrum (𝓞 K)) (hnv : (n : 𝓞 K) ∉ v.asIdeal)
    (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal := fun P _ _ =>
  isUnramifiedAt_of_pow_eq a hα hgen v hnv hav P

end Kummer

end Sec2_02_KummerTheory_Unramified

/-! ### 03_KummerTheory.SplittingInfinite -/
section Sec2_03_KummerTheory_SplittingInfinite

open NumberField Module
open scoped NumberField.LiesOver TensorProduct

namespace InfinitePlace
open RHDirect.CFT_ProfiniteSemilocal.InfinitePlace

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

def SplitsCompletely (v : NumberField.InfinitePlace K) : Prop :=
  ∀ w : NumberField.InfinitePlace L, w.LiesOver v → w.IsUnramified K

variable {L} (v : NumberField.InfinitePlace K)

theorem isUnramified_iff_finrank_eq_one (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    w.IsUnramified K ↔ finrank v.Completion w.Completion = 1 := by
  refine ⟨fun h ↦ h.finrank_eq_one v, fun h ↦ ?_⟩
  rcases w.isUnramified_or_isRamified K with hu | hr
  · exact hu
  · exact absurd (h.symm.trans (hr.finrank_eq_two v)) (by norm_num)

theorem splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : v.placesOver L, finrank v.Completion (w : NumberField.InfinitePlace L).Completion = 1 :=
  ⟨fun h w ↦ (isUnramified_iff_finrank_eq_one v w.1).1 (h w.1 w.2),
    fun h w hw ↦ have := hw; (isUnramified_iff_finrank_eq_one v w).2 (h ⟨w, hw⟩)⟩

variable [NumberField K] [NumberField L]

theorem splitsCompletely_iff_isFiniteSplit :
    SplitsCompletely L v ↔ Algebra.IsFiniteSplit v.Completion (v.Completion ⊗[K] L) := by
  rw [splitsCompletely_iff_forall_finrank, ← isFiniteSplit_pi_iff]
  exact ⟨fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v).symm,
    fun h ↦ .of_algEquiv (tensorPiEquiv (L := L) v)⟩

variable (L) in

theorem nonempty_placesOver : Nonempty (v.placesOver L) := by
  classical
  by_contra h
  rw [not_nonempty_iff] at h
  have := sum_finrank_completion (L := L) v
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  exact (Module.finrank_pos (R := K) (M := L)).ne this

end InfinitePlace

end Sec2_03_KummerTheory_SplittingInfinite

/-! ### 04_KummerTheory.SplittingKummer -/
section Sec2_04_KummerTheory_SplittingKummer

open IsDedekindDomain NumberField Module IntermediateField RHDirect.CFT_ProfiniteSemilocal.ProfCoh
open scoped TensorProduct

section Local

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]

omit [NeZero n] [HasEnoughRootsOfUnity K n] [IsScalarTower K F E] in

theorem kummerExtension_pow_eq {y : kummerExtension K n Ω Δ} {a : K}
    (hy : (y : Ω) ^ n = algebraMap K Ω a) :
    y ^ n = algebraMap K (kummerExtension K n Ω Δ) a :=
  Subtype.ext (by rw [IntermediateField.coe_pow, hy]; rfl)

theorem algHom_kummerExtension_mem_fieldRange (ι : kummerExtension K n Ω Δ →ₐ[K] E)
    (h : ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K)) (m : kummerExtension K n Ω Δ) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have key : ∀ (y : kummerExtension K n Ω Δ), ∀ a ∈ Δ, (y : Ω) ^ n = algebraMap K Ω (a : K) →
      ι y ∈ (algebraMap F E).fieldRange := by
    intro y a ha hy
    obtain ⟨x, hx⟩ := h a ha
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0 : algebraMap F E x ≠ 0 := by
      refine (map_ne_zero _).2 fun hx0 ↦ ?_
      rw [hx0, zero_pow (NeZero.ne n)] at hx
      exact a.ne_zero ((algebraMap K F).injective (by rw [← hx, map_zero]))
    have hpow : ι y ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, kummerExtension_pow_eq hy, ι.commutes, ← map_pow, hx,
        ← IsScalarTower.algebraMap_apply]
    have hroot : (ι y / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0)]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0]
  obtain ⟨m, hm⟩ := m
  induction hm using IntermediateField.adjoin_induction with
  | mem α hα =>
    obtain ⟨a, ha, hαa⟩ := id hα
    exact key _ a ha hαa
  | algebraMap x =>
    refine ⟨algebraMap K F x, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact (ι.commutes x).symm
  | add x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
    rw [map_add]
    exact add_mem ihx ihy
  | inv x hx ih =>
    show ι (⟨x, hx⟩⁻¹) ∈ _
    rw [map_inv₀]
    exact inv_mem ih
  | mul x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
    rw [map_mul]
    exact mul_mem ihx ihy

omit [Algebra K E] [IsScalarTower K F E] in

theorem finrank_eq_one_of_tensor_surjective {A : Type*} [CommRing A] [Algebra K A]
    (g : F ⊗[K] A →ₐ[F] E) (hg : Function.Surjective g)
    (hA : ∀ m : A, g (1 ⊗ₜ m) ∈ (algebraMap F E).fieldRange) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  refine eq_top_iff.2 fun e he ↦ ?_
  clear he
  obtain ⟨t, rfl⟩ := hg e
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c m =>
    have : c ⊗ₜ[K] m = c • ((1 : F) ⊗ₜ[K] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Subalgebra.smul_mem _ (Algebra.mem_bot.2 (hA m)) c
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem finrank_eq_one_iff_of_kummerExtension [IsSepClosed Ω]
    (g : F ⊗[K] kummerExtension K n Ω Δ →ₐ[F] E) (hg : Function.Surjective g) :
    finrank F E = 1 ↔ ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K) := by
  let ι : kummerExtension K n Ω Δ →ₐ[K] E :=
    (g.restrictScalars K).comp Algebra.TensorProduct.includeRight
  constructor
  · intro h1 a ha
    have hsurj : Function.Surjective (algebraMap F E) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hnK : NeZero ((n : ℕ) : K) := hζ.neZero'
    have hnΩ : NeZero ((n : ℕ) : Ω) :=
      ⟨by rw [← map_natCast (algebraMap K Ω)]; exact (map_ne_zero _).2 hnK.out⟩
    obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) n
    let y : kummerExtension K n Ω Δ := ⟨α, subset_adjoin _ _ ⟨a, ha, hα⟩⟩
    obtain ⟨x, hx⟩ := hsurj (ι y)
    refine ⟨x, (algebraMap F E).injective ?_⟩
    rw [map_pow, hx, ← map_pow, kummerExtension_pow_eq (y := y) hα, ι.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro h
    exact finrank_eq_one_of_tensor_surjective g hg fun m ↦
      algHom_kummerExtension_mem_fieldRange ι h m

end Local

section Global

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω] {Δ : Subgroup Kˣ}
  [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]

instance numberField_kummerExtension : NumberField (kummerExtension K n Ω Δ) :=
  NumberField.of_module_finite K _

open SemiLocal in

theorem splitsCompletely_kummerExtension_iff (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) (a : K) := by
  have key (w : PlacesOver (kummerExtension K n Ω Δ) v) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom (v.adicCompletion K) _ w).comp
        (tensorEquiv (kummerExtension K n Ω Δ) v).toAlgHom)
      ((Function.surjective_eval w).comp (tensorEquiv (kummerExtension K n Ω Δ) v).surjective)
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)

open scoped NumberField.LiesOver in

theorem InfinitePlace.splitsCompletely_kummerExtension_iff (v : NumberField.InfinitePlace K) :
    InfinitePlace.SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.Completion, x ^ n = algebraMap K v.Completion (a : K) := by
  have key (w : v.placesOver (kummerExtension K n Ω Δ)) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom v.Completion _ w).comp
        (InfinitePlace.tensorPiHom (L := kummerExtension K n Ω Δ) v))
      ((Function.surjective_eval w).comp
        (InfinitePlace.tensorPiHom_surjective (L := kummerExtension K n Ω Δ) v))
  rw [InfinitePlace.splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := InfinitePlace.nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)

end Global

end Sec2_04_KummerTheory_SplittingKummer

/-! ### 05_KummerTheory.LocalIndex -/
section Sec2_05_KummerTheory_LocalIndex

open ValuativeRel IsLocalRing RHDirect.CFT.LocalField
open scoped WithZero

theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ c : R, (1 + x) ^ n = 1 + n * x + x ^ 2 * c := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨n + c + x * c, ?_⟩
    rw [pow_succ, hc]
    push_cast
    ring

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Filtration

theorem div_mem_unitFiltration_iff {k : ℕ} {x y : 𝒪[K]ˣ} :
    x / y ∈ unitFiltration K k ↔ (x : 𝒪[K]) - y ∈ 𝓂[K] ^ k := by
  rw [mem_unitFiltration]
  have h1 : ((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ((x : 𝒪[K]) - y) * ((y⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (Units.mul_inv y)
  have h2 : (x : 𝒪[K]) - y = (y : 𝒪[K]) * (((x / y : 𝒪[K]ˣ) : 𝒪[K]) - 1) := by
    rw [div_eq_mul_inv, Units.val_mul]
    linear_combination (-(x : 𝒪[K])) * (Units.mul_inv y)
  constructor
  · intro h; rw [h2]; exact Ideal.mul_mem_left _ _ h
  · intro h; rw [h1]; exact Ideal.mul_mem_right _ _ h

theorem eq_zero_of_forall_mem_maximalIdeal_pow {x : 𝒪[K]} (hx : ∀ k, x ∈ 𝓂[K] ^ k) : x = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  by_contra h0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h := (RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ).mp (hx (m + 1))
  rw [pow_succ, mul_comm (u : 𝒪[K]), mul_dvd_mul_iff_left (pow_ne_zero m hϖ.ne_zero)] at h
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h u.isUnit)

theorem filtrationSeparated_unitFiltration : FiltrationSeparated (unitFiltration K) := by
  intro u hu
  have : (u : 𝒪[K]) - 1 = 0 := eq_zero_of_forall_mem_maximalIdeal_pow fun k ↦ hu k
  ext
  simpa [sub_eq_zero] using this

theorem isAdicComplete_integer : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let _ : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  have : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  infer_instance

theorem filtrationComplete_unitFiltration : FiltrationComplete (unitFiltration K) := by
  have hc := (isAdicComplete_integer (K := K)).toIsPrecomplete
  intro x hx
  choose M hM using hx

  let M' : ℕ → ℕ := fun N ↦ (Finset.range (N + 1)).sup M
  have hM'ge : ∀ N, M N ≤ M' N := fun N ↦ Finset.le_sup (Finset.self_mem_range_succ N)
  have hM'mono : Monotone M' := fun a b hab ↦
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  have hy : ∀ {a b : ℕ}, a ≤ b →
      ((x (M' a) : 𝒪[K]) ≡ x (M' b) [SMOD (𝓂[K] ^ a • ⊤ : Submodule 𝒪[K] 𝒪[K])]) := by
    intro a b hab
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact div_mem_unitFiltration_iff.mp
      (hM a (M' b) ((hM'ge a).trans (hM'mono hab)) (M' a) (hM'ge a))
  obtain ⟨L, hL⟩ := hc.prec' (fun N ↦ (x (M' N) : 𝒪[K])) hy
  have hL' : ∀ N, (x (M' N) : 𝒪[K]) - L ∈ 𝓂[K] ^ N := fun N ↦ by
    have := hL N
    rwa [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at this
  have hLu : IsUnit L := by
    by_contra hL0
    have h1 : L ∈ 𝓂[K] := (IsLocalRing.mem_maximalIdeal L).mpr hL0
    have h2 := hL' 1
    rw [pow_one] at h2
    have : (x (M' 1) : 𝒪[K]) ∈ 𝓂[K] := by
      simpa using Ideal.add_mem _ h2 h1
    exact (IsLocalRing.mem_maximalIdeal _).mp this (x (M' 1)).isUnit
  refine ⟨hLu.unit, fun N ↦ ⟨M' N, fun n hn ↦ ?_⟩⟩
  rw [div_mem_unitFiltration_iff, IsUnit.unit_spec]
  have h1 : (x n : 𝒪[K]) - x (M' N) ∈ 𝓂[K] ^ N :=
    div_mem_unitFiltration_iff.mp (hM N (M' N) (hM'ge N) n ((hM'ge N).trans hn))
  have := Ideal.add_mem _ h1 (hL' N)
  rwa [sub_add_sub_cancel] at this

end Filtration

section PowerMap

variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ in

theorem exists_one_add_uniformizer_pow_mul_pow_eq {j : ℕ} (hj : d + 1 ≤ j) (a : 𝒪[K]) :
    ∃ c : 𝒪[K], (1 + ϖ ^ j * a) ^ n = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by
  obtain ⟨c₀, hc₀⟩ := exists_one_add_pow_eq (ϖ ^ j * a) n
  obtain ⟨t, rfl⟩ : ∃ t, j = d + 1 + t := ⟨j - (d + 1), by omega⟩
  refine ⟨ϖ ^ t * a ^ 2 * c₀, ?_⟩
  rw [hc₀, hnd]
  ring

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ in

theorem exists_units_pow_eq {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ} {a : 𝒪[K]}
    (hu : (u : 𝒪[K]) - 1 = ϖ ^ j * a) :
    ∃ c : 𝒪[K], ((u ^ n : 𝒪[K]ˣ) : 𝒪[K]) = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by
  obtain ⟨c, hc⟩ := exists_one_add_uniformizer_pow_mul_pow_eq hnd hj a
  refine ⟨c, ?_⟩
  rw [Units.val_pow_eq_pow_val, ← hc, ← hu, add_sub_cancel]

theorem pow_mem_unitFiltration {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ n ∈ unitFiltration K (j + d) := by
  obtain ⟨a, ha⟩ := (RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ).mp hu
  obtain ⟨c, hc⟩ := exists_units_pow_eq hnd hj ha
  rw [mem_unitFiltration, hc, add_sub_cancel_left, RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ]
  exact dvd_mul_right _ _

theorem exists_pow_div_mem_unitFiltration {j : ℕ} (hj : d + 1 ≤ j) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K (j + d)) :
    ∃ g ∈ unitFiltration K j, h / g ^ n ∈ unitFiltration K (j + 1 + d) := by
  obtain ⟨b, hb⟩ := (RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ).mp hh
  have hg := isUnit_one_add_mul hϖ (n := j) (by omega) ((ε⁻¹ : 𝒪[K]ˣ) * b)
  have hg1 : ((hg.unit : 𝒪[K]ˣ) : 𝒪[K]) - 1 = ϖ ^ j * ((ε⁻¹ : 𝒪[K]ˣ) * b) := by
    rw [IsUnit.unit_spec, add_sub_cancel_left]
  refine ⟨hg.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, hg1, RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ]
    exact dvd_mul_right _ _
  · obtain ⟨c, hc⟩ := exists_units_pow_eq hnd hj hg1
    rw [div_mem_unitFiltration_iff, RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ]
    exact ⟨-c, by linear_combination hb - hc - ϖ ^ (j + d) * b * (Units.mul_inv ε)⟩

theorem eq_one_of_pow_eq_one {u : 𝒪[K]ˣ} (hu : u ∈ unitFiltration K (d + 1)) (hun : u ^ n = 1) :
    u = 1 := by
  classical
  by_contra hu1
  have hex : ∃ k, u ∉ unitFiltration K k := by
    by_contra h
    push Not at h
    exact hu1 (filtrationSeparated_unitFiltration u h)
  have hJ := Nat.find_spec hex
  have hJmin : ∀ k < Nat.find hex, u ∈ unitFiltration K k := fun k hk ↦ by
    have := Nat.find_min hex hk
    simpa using this
  have hJd : d + 1 < Nat.find hex := by
    by_contra hle
    exact hJ (unitFiltration_antitone K (not_lt.mp hle) hu)
  obtain ⟨j, hjJ⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have huj : u ∈ unitFiltration K j := hJmin j (by omega)
  obtain ⟨a, ha⟩ := (RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ).mp huj
  have hnot : ¬ ϖ ∣ a := by
    rintro ⟨b, rfl⟩
    apply hJ
    rw [hjJ, mem_unitFiltration, RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ, ha, pow_succ]
    exact mul_dvd_mul_left _ (dvd_mul_right _ _)
  obtain ⟨c, hc⟩ := exists_units_pow_eq hnd (j := j) (by omega) ha
  rw [hun, Units.val_one, left_eq_add, mul_eq_zero] at hc
  rcases hc with hc | hc
  · exact pow_ne_zero _ hϖ.ne_zero hc
  · apply hnot
    refine ⟨-((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c, ?_⟩
    linear_combination ((ε⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * hc - a * (Units.inv_mul ε)

theorem map_powMonoidHom_unitFiltration :
    (unitFiltration K (d + 1)).map (powMonoidHom n) = unitFiltration K (d + 1 + d) :=
  map_eq_of_graded_surjective (unitFiltration_antitone K) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration (powMonoidHom n)
    (φ := fun j ↦ j + d) (Filter.tendsto_add_atTop_nat d) (d + 1)
    (fun _ hj _ hg ↦ pow_mem_unitFiltration hϖ hnd hj hg)
    (fun _ hj _ hh ↦ exists_pow_div_mem_unitFiltration hϖ hnd hj hh)

theorem index_range_powMonoidHom_integerUnits_of_eq :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker * Nat.card 𝓀[K] ^ d := by
  set f : 𝒪[K]ˣ →* 𝒪[K]ˣ := powMonoidHom n
  set V := unitFiltration K (d + 1)
  have hdisj : Disjoint V f.ker := by
    rw [Subgroup.disjoint_def]
    intro u hu hk
    exact eq_one_of_pow_eq_one hϖ hnd hu hk
  have h1 : V.relIndex f.ker = Nat.card f.ker := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.2 hdisj, Subgroup.index_bot]
  have h2 : V.relIndex (V ⊔ f.ker) * (V ⊔ f.ker).index = V.index :=
    Subgroup.relIndex_mul_index le_sup_left
  have h3 : V.relIndex (V ⊔ f.ker) = V.relIndex f.ker := Subgroup.relIndex_sup_left f.ker V
  have h4 : (V.map f).index = (V ⊔ f.ker).index * f.range.index := V.index_map f
  rw [map_powMonoidHom_unitFiltration hϖ hnd, index_unitFiltration K (by omega)] at h4
  rw [h3, h1, index_unitFiltration K (by omega)] at h2
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hc : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d :=
    Nat.mul_pos (by omega) (pow_pos (by omega) d)
  refine Nat.eq_of_mul_eq_mul_left hc ?_
  have e1 : d + 1 - 1 = d := by omega
  have e2 : d + 1 + d - 1 = d + d := by omega
  rw [e1] at h2
  rw [e2, pow_add] at h4
  calc (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ d * f.range.index
      = Nat.card f.ker * ((V ⊔ f.ker).index * f.range.index) := by rw [← h2]; ring
    _ = _ := by rw [← h4]; ring

end PowerMap

section Units

variable {n : ℕ}

theorem ord_uniformizer_pow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (d : ℕ) : ord ((ϖ : K) ^ d) = d := by
  have h0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  induction d with
  | zero => simp [ord]
  | succ d ih =>
    rw [pow_succ, ord_mul (pow_ne_zero _ h0) h0, ih, ord_uniformizer hϖ]
    push_cast
    ring

theorem exists_natCast_eq_unit_mul_pow (hn : (n : K) ≠ 0) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ∃ (d : ℕ) (ε : 𝒪[K]ˣ), (n : 𝒪[K]) = ε * ϖ ^ d ∧ ord (n : K) = d := by
  have h0 : (n : 𝒪[K]) ≠ 0 := by
    intro h
    apply hn
    simpa using congrArg (fun x : 𝒪[K] ↦ (x : K)) h
  obtain ⟨d, ε, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  refine ⟨d, ε, h, ?_⟩
  have hK : (n : K) = ((ε : 𝒪[K]) : K) * (ϖ : K) ^ d := by
    simpa using congrArg (fun x : 𝒪[K] ↦ (x : K)) h
  have hε : ((ε : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hϖd : (ϖ : K) ^ d ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  rw [hK, ord_mul hε hϖd, ord_unit, ord_uniformizer_pow hϖ, zero_add]

theorem map_unitsIncl_ker_powMonoidHom (hn : n ≠ 0) :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker.map (unitsIncl K) = rootsOfUnity n K := by
  ext x
  rw [Subgroup.mem_map, mem_rootsOfUnity]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hu
    rw [← map_pow, hu, map_one]
  · intro hx
    have hv : normalizedValuation K (x : K) ^ n = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx, Units.val_one, map_one]
    have hv1 : normalizedValuation K (x : K) = 1 := by
      have hne : normalizedValuation K (x : K) ≠ 0 := by simp
      have hlog := congrArg WithZero.log hv
      rw [WithZero.log_pow, WithZero.log_one, smul_eq_zero] at hlog
      rcases hlog with h | h
      · exact absurd h hn
      · rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
    obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr hv1
    refine ⟨u, ?_, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    apply unitsIncl_injective
    rw [map_pow, hx, map_one]

theorem natCard_rootsOfUnity_eq (hn : n ≠ 0) :
    Nat.card (rootsOfUnity n K) = Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker := by
  rw [← map_unitsIncl_ker_powMonoidHom hn, Subgroup.card_map_of_injective unitsIncl_injective]

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem index_range_powMonoidHom_multiplicativeInt (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  have h : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range =
      (AddSubgroup.zmultiples (n : ℤ)).toSubgroup := by
    ext x
    rw [MonoidHom.mem_range, Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.toAdd y, by simp⟩
    · rintro ⟨k, hk⟩
      refine ⟨Multiplicative.ofAdd k, ?_⟩
      apply Multiplicative.toAdd.injective
      simp [hk]
  rw [h, AddSubgroup.index_toSubgroup, Int.index_zmultiples]
  simp

omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem range_powMonoidHom_prod {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range =
      (powMonoidHom n : G →* G).range.prod (powMonoidHom n : H →* H).range := by
  ext ⟨a, b⟩
  rw [Subgroup.mem_prod, MonoidHom.mem_range, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨x, y⟩, h⟩
    rw [powMonoidHom_apply, Prod.pow_mk, Prod.mk.injEq] at h
    exact ⟨⟨x, h.1⟩, ⟨y, h.2⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨(x, y), ?_⟩
    rw [powMonoidHom_apply] at hx hy ⊢
    rw [Prod.pow_mk, hx, hy]

theorem index_range_powMonoidHom_units_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index := by
  set e := unitsEquivIntProd hϖ
  have hmap : (powMonoidHom n : Kˣ →* Kˣ).range.map (e : Kˣ →* Multiplicative ℤ × 𝒪[K]ˣ) =
      (powMonoidHom n : Multiplicative ℤ × 𝒪[K]ˣ →* _).range := by
    ext p
    rw [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q ^ n, ⟨e.symm q, rfl⟩, by simp⟩
  rw [← Subgroup.index_map_equiv _ e, hmap, range_powMonoidHom_prod, Subgroup.index_prod,
    index_range_powMonoidHom_multiplicativeInt]

theorem index_range_powMonoidHom_eq_mul (hn : (n : K) ≠ 0) :
    ∃ d : ℕ, ord (n : K) = d ∧ (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * Nat.card (rootsOfUnity n K) * Nat.card 𝓀[K] ^ d := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨d, ε, hnd, hord⟩ := exists_natCast_eq_unit_mul_pow hn hϖ
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨d, hord, ?_⟩
  rw [index_range_powMonoidHom_units_eq hϖ, index_range_powMonoidHom_integerUnits_of_eq hϖ hnd,
    natCard_rootsOfUnity_eq hn0, mul_assoc]

theorem index_range_powMonoidHom (hn : (n : K) ≠ 0) :
    ((powMonoidHom n : Kˣ →* Kˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n K) * (Nat.card 𝓀[K] : ℝ) ^ ord (n : K) := by
  obtain ⟨d, hd, h⟩ := index_range_powMonoidHom_eq_mul hn
  rw [h, hd, zpow_natCast]
  push_cast
  ring

end Units

section Open

theorem uniformizer_pow_succ_dvd_of_valuation_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    {z : 𝒪[K]} (h : valuation K (z : K) < valuation K ((ϖ : K) ^ k)) : ϖ ^ (k + 1) ∣ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact dvd_zero _
  obtain ⟨m, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖ
  have hzK : (((w : 𝒪[K]) * ϖ ^ m : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast hz
  have hϖk : (ϖ : K) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  rw [← normalizedValuation_lt_iff, normalizedValuation_eq_exp_ord hzK,
    normalizedValuation_eq_exp_ord hϖk, WithZero.exp_lt_exp, neg_lt_neg_iff,
    ord_uniformizer_pow hϖ] at h
  have hord : ord ((((w : 𝒪[K]) * ϖ ^ m : 𝒪[K])) : K) = m := by
    have hw : ((w : 𝒪[K]) : K) ≠ 0 := by exact_mod_cast w.ne_zero
    have hϖm : (ϖ : K) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
    push_cast
    rw [ord_mul hw hϖm, ord_unit, ord_uniformizer_pow hϖ, zero_add]
  rw [hord] at h
  exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _

theorem isOpen_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨d, ε, hnd, -⟩ := exists_natCast_eq_unit_mul_pow hn hϖ
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  set B : Set K := {y | valuation K (y - 1) < valuation K ((ϖ : K) ^ (d + d))}
  have hB : B ∈ nhds (1 : K) := by
    refine (IsValuativeTopology.hasBasis_nhds' (1 : K)).mem_of_mem ?_
    rw [Ne, Valuation.zero_iff]
    exact pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have hB' : Units.val ⁻¹' B ∈ nhds (1 : Kˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (by simpa using hB)
  refine Filter.mem_of_superset hB' fun x hx ↦ ?_
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, B] at hx
  have hlt1 : valuation K ((x : K) - 1) < 1 := by
    refine hx.trans_le ?_
    rw [map_pow]
    exact pow_le_one' ϖ.2 _
  have hy : (x : K) - 1 ∈ 𝒪[K] := hlt1.le
  have hv1 : valuation K (x : K) = 1 := by
    have := Valuation.map_add_eq_of_lt_right (valuation K) (x := (x : K) - 1) (y := 1)
      (by rwa [map_one])
    rwa [sub_add_cancel, map_one] at this
  have hnv : normalizedValuation K (x : K) = 1 := by
    rw [← map_one (normalizedValuation K), normalizedValuation_eq_iff, map_one, hv1]
  obtain ⟨u, rfl⟩ := mem_range_unitsIncl_iff.mpr hnv
  have hu : u ∈ unitFiltration K (d + 1 + d) := by
    rw [mem_unitFiltration, RHDirect.CFT.LocalField.mem_maximalIdeal_pow_iff hϖ]
    have e1 : d + 1 + d = d + d + 1 := by omega
    rw [e1]
    apply uniformizer_pow_succ_dvd_of_valuation_lt hϖ
    simpa using hx
  rw [← map_powMonoidHom_unitFiltration hϖ hnd] at hu
  obtain ⟨w, -, rfl⟩ := hu
  exact ⟨unitsIncl K w, by simp⟩

end Open

end Sec2_05_KummerTheory_LocalIndex

/-! ### 06_KummerTheory.LocalIndexAtPlace -/
section Sec2_06_KummerTheory_LocalIndexAtPlace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  RHDirect.CFT.LocalField

section FinitePlace

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem coe_mem_adicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).1 x.2

theorem coe_mem_valuationInteger (x : v.adicCompletionIntegers K) :
    (x : v.adicCompletion K) ∈ 𝒪[v.adicCompletion K] :=
  (mem_valuationInteger_iff v (x : v.adicCompletion K)).2 x.2

def integerEquivAdicCompletionIntegers :
    𝒪[v.adicCompletion K] ≃+* v.adicCompletionIntegers K where
  toFun x := ⟨x, coe_mem_adicCompletionIntegers v x⟩
  invFun x := ⟨x, coe_mem_valuationInteger v x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_integerEquivAdicCompletionIntegers (x : 𝒪[v.adicCompletion K]) :
    ((integerEquivAdicCompletionIntegers v x : v.adicCompletionIntegers K) :
      v.adicCompletion K) = x :=
  rfl

theorem natCard_residueField_adicCompletion :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by
  rw [← natCard_residueField_adicCompletionIntegers v]
  exact Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv (integerEquivAdicCompletionIntegers v)).toEquiv

theorem norm_eq_absNorm_zpow_neg_ord {x : v.adicCompletion K} (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ord x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  set p := unitsEquivIntProd hϖ (Units.mk0 x hx)
  have hxp : x = ((ϖ : v.adicCompletion K)) ^ (Multiplicative.toAdd p.1) *
      ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) := by
    rw [← coe_unitsOfIntProd hϖ, ← unitsEquivIntProd_symm_apply hϖ, MulEquiv.symm_apply_apply]
    rfl
  have hord : Multiplicative.toAdd p.1 = ord x := by
    rw [unitsEquivIntProd_fst hϖ]
    rfl
  have hϖ' : Irreducible (integerEquivAdicCompletionIntegers v ϖ) :=
    hϖ.map (integerEquivAdicCompletionIntegers v)
  have hnϖ : ‖(ϖ : v.adicCompletion K)‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    have h := normalizedAbv_of_irreducible v hϖ'
    rw [normalizedAbv_apply, coe_integerEquivAdicCompletionIntegers] at h
    exact h
  have hu : ‖((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K)‖ = 1 := by
    have hunit : IsUnit (integerEquivAdicCompletionIntegers v p.2) :=
      p.2.isUnit.map (integerEquivAdicCompletionIntegers v)
    have h1 := (adicCompletionIntegers.isUnit_iff_valued_eq_one).1 hunit
    have h0 : ((p.2 : 𝒪[v.adicCompletion K]) : v.adicCompletion K) ≠ 0 := by
      exact_mod_cast p.2.ne_zero
    rw [← normalizedAbv_apply, normalizedAbv_eq_zpow v h0]
    rw [coe_integerEquivAdicCompletionIntegers] at h1
    rw [h1]
    simp
  conv_lhs => rw [hxp]
  rw [norm_mul, norm_zpow, hnϖ, hu, mul_one, hord, inv_zpow']

variable {v}

theorem natCast_ne_zero_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    (n : v.adicCompletion K) ≠ 0 := by
  rw [← map_natCast (algebraMap K (v.adicCompletion K)), ne_eq,
    map_eq_zero_iff _ (algebraMap K (v.adicCompletion K)).injective]
  exact_mod_cast hn

variable (v)

theorem index_range_powMonoidHom_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n (v.adicCompletion K)) / ‖(n : v.adicCompletion K)‖ := by
  have hn' := natCast_ne_zero_adicCompletion (v := v) hn
  rw [index_range_powMonoidHom hn', natCard_residueField_adicCompletion,
    norm_eq_absNorm_zpow_neg_ord v hn', zpow_neg, div_inv_eq_mul]

theorem index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity (v.adicCompletion K) n] :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) =
      n ^ 2 / ‖(n : v.adicCompletion K)‖ := by
  rw [index_range_powMonoidHom_adicCompletion v (NeZero.ne n),
    HasEnoughRootsOfUnity.natCard_rootsOfUnity, sq]

theorem isOpen_range_powMonoidHom_adicCompletion {n : ℕ} (hn : n ≠ 0) :
    IsOpen ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range :
      Set (v.adicCompletion K)ˣ) :=
  isOpen_range_powMonoidHom (natCast_ne_zero_adicCompletion hn)

end FinitePlace

end Sec2_06_KummerTheory_LocalIndexAtPlace

/-! ### 07_ExistenceTheorem.PowerIndex -/
section Sec2_07_ExistenceTheorem_PowerIndex

open NumberField IsDedekindDomain Module


section PowerIndex

variable {G : Type*} [CommGroup G]

theorem mem_torsion_of_pow_mem_torsion {n : ℕ} (hn : n ≠ 0) {x : G}
    (hx : x ^ n ∈ CommGroup.torsion G) : x ∈ CommGroup.torsion G := by
  rw [CommGroup.mem_torsion] at hx ⊢
  exact (isOfFinOrder_pow.1 hx).resolve_right hn

theorem range_powMonoidHom_subgroupOf_torsion {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.subgroupOf (CommGroup.torsion G) =
      (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range := by
  ext ⟨t, ht⟩
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    rw [powMonoidHom_apply] at hx
    refine ⟨⟨x, mem_torsion_of_pow_mem_torsion hn ?_⟩, Subtype.ext ?_⟩
    · rw [hx]
      exact ht
    · exact hx
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem range_powMonoidHom_sup_torsion (n : ℕ) :
    (powMonoidHom n : G →* G).range ⊔ CommGroup.torsion G =
      (powMonoidHom n : G ⧸ CommGroup.torsion G →* G ⧸ CommGroup.torsion G).range.comap
        (QuotientGroup.mk' (CommGroup.torsion G)) := by
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · intro hx
    obtain ⟨_, ⟨b, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.1 hx
    refine ⟨QuotientGroup.mk' _ b, ?_⟩
    have h1 : QuotientGroup.mk' (CommGroup.torsion G) t = 1 := (QuotientGroup.eq_one_iff t).2 ht
    rw [map_mul, h1, mul_one, powMonoidHom_apply, map_pow]
  · rintro ⟨q, hq⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion G) q
    have ht : (b ^ n)⁻¹ * x ∈ CommGroup.torsion G := by
      rw [← QuotientGroup.eq]
      rw [← map_pow] at hq
      exact hq
    have h := Subgroup.mul_mem_sup (S := (powMonoidHom n : G →* G).range)
      (T := CommGroup.torsion G) ⟨b, rfl⟩ ht
    rwa [powMonoidHom_apply, mul_inv_cancel_left] at h

instance finite_additive_quotient_torsion [Group.FG G] :
    Module.Finite ℤ (Additive (G ⧸ CommGroup.torsion G)) := by
  rw [Module.Finite.iff_addGroup_fg, AddGroup.fg_iff_addMonoid_fg, ← Monoid.fg_iff_add_fg,
    ← Group.fg_iff_monoid_fg]
  infer_instance

theorem index_range_powMonoidHom_eq_pow_mul [Group.FG G] {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ finrank ℤ (Additive (G ⧸ CommGroup.torsion G)) *
        (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range.index := by
  set T := CommGroup.torsion G
  set N := (powMonoidHom n : G →* G).range
  have hQ : (powMonoidHom n : G ⧸ T →* G ⧸ T).range.index =
      n ^ finrank ℤ (Additive (G ⧸ T)) :=
    AddSubgroup.index_range_nsmul (Additive (G ⧸ T)) n
  have hsup : (N ⊔ T).index = n ^ finrank ℤ (Additive (G ⧸ T)) := by
    rw [range_powMonoidHom_sup_torsion, Subgroup.index_comap_of_surjective _
      (QuotientGroup.mk'_surjective T), hQ]
  have hrel : N.relIndex T = (powMonoidHom n : T →* T).range.index := by
    rw [Subgroup.relIndex, range_powMonoidHom_subgroupOf_torsion hn]
  rw [← Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T), Subgroup.relIndex_sup_left, hrel,
    hsup, mul_comm]

end PowerIndex

section SUnit

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

namespace SUnit
open RHDirect.Stage13CFT_IdeleNormResidue.SUnit

theorem finrank_quotient_torsion [Finite S] :
    finrank ℤ (Additive (S.unit K ⧸ CommGroup.torsion (S.unit K))) = Units.rank K + Nat.card S := by
  rw [← finrank_eq S]
  exact finrank_quotient_torsion_eq (M := Additive (S.unit K))

theorem dvd_natCard_torsion (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    n ∣ Nat.card (CommGroup.torsion (S.unit K)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  set u : Kˣ := (hζ.isUnit (NeZero.ne n)).unit
  have hu : IsPrimitiveRoot u n := IsPrimitiveRoot.coe_units_iff.1 hζ
  have hfin : IsOfFinOrder u := by
    rw [← orderOf_pos_iff, ← hu.eq_orderOf]
    exact NeZero.pos n
  let u' : S.unit K := ⟨u, fun v _ ↦ valuation_eq_one_of_isOfFinOrder hfin v⟩
  have hfin' : IsOfFinOrder u' := by
    rw [← orderOf_pos_iff, ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact orderOf_pos_iff.mpr hfin
  let t : CommGroup.torsion (S.unit K) := ⟨u', hfin'⟩
  have ht : orderOf t = n := by
    rw [← orderOf_injective (CommGroup.torsion (S.unit K)).subtype Subtype.val_injective,
      ← orderOf_injective (S.unit K).subtype Subtype.val_injective]
    exact hu.eq_orderOf.symm
  rw [← ht]
  exact orderOf_dvd_natCard t

theorem index_range_powMonoidHom (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] [Finite S] :
    (powMonoidHom n : S.unit K →* S.unit K).range.index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  have hpos : 0 < InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  rw [index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), finrank_quotient_torsion,
    IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right (dvd_natCard_torsion S n), ← pow_succ,
    Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  congr 1
  omega

end SUnit

end SUnit

end Sec2_07_ExistenceTheorem_PowerIndex

/-! ### 08_ExistenceTheorem.LocalPowers -/
section Sec2_08_ExistenceTheorem_LocalPowers

open NumberField IsDedekindDomain IntermediateField RHDirect.CFT_ProfiniteSemilocal.ProfCoh
open IdeleNorm SemiLocal
open scoped NumberField.LiesOver


section InfiniteSplit

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem range_infiniteLocalNorm_eq_top_of_splitsCompletely (v : InfinitePlace K)
    (h : InfinitePlace.SplitsCompletely L v) : (infiniteLocalNorm L v).range = ⊤ := by
  classical
  obtain ⟨w⟩ := nonempty_infinitePlacesOver L v
  have hw := (InfinitePlace.splitsCompletely_iff_forall_finrank v).1 h w
  refine eq_top_iff.2 fun a _ ↦ ⟨Pi.mulSingle w (Units.map (algebraMap v.Completion
    (w : InfinitePlace L).Completion : v.Completion →* (w : InfinitePlace L).Completion) a), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  rw [RHDirect.CFT.LocalField.coe_normUnits, Units.coe_map]
  exact (Algebra.norm_algebraMap (a : v.Completion)).trans (by rw [hw, pow_one])

end InfiniteSplit

section Kummer

variable {K : Type*} [Field K] {n : ℕ} [NeZero n]

omit [NeZero n] in

theorem forall_mem_zpowers_exists_pow_eq {F : Type*} [Field F] [Algebra K F] {y : Kˣ}
    (h : ∃ x : F, x ^ n = algebraMap K F (y : K)) :
    ∀ a ∈ Subgroup.zpowers y, ∃ x : F, x ^ n = algebraMap K F (a : K) := by
  obtain ⟨x, hx⟩ := h
  rintro _ ⟨k, rfl⟩
  refine ⟨x ^ k, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, Units.val_zpow_eq_zpow_val,
    map_zpow₀]

instance finite_zpowers_quotient_unitsPow (y : Kˣ) :
    Finite (Subgroup.zpowers y ⧸ (unitsPow K n).subgroupOf (Subgroup.zpowers y)) := by
  have hle : (powMonoidHom n : Subgroup.zpowers y →* Subgroup.zpowers y).range ≤
      (unitsPow K n).subgroupOf (Subgroup.zpowers y) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(x : Kˣ), rfl⟩
  have : Group.FG (Subgroup.zpowers y) := (Group.fg_iff_subgroup_fg _).2
    ⟨{y}, by rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]⟩
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (Subgroup.zpowers y) (NeZero.ne n)
  have := Subgroup.finiteIndex_of_le hle
  exact Subgroup.finite_quotient_of_finiteIndex

variable [HasEnoughRootsOfUnity K n] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in

theorem adjoin_eq_top_of_pow_eq {y : Kˣ} (α : kummerExtension K n Ω (Subgroup.zpowers y))
    (hα : α ^ n = algebraMap K _ (y : K)) : adjoin K {α} = ⊤ := by
  refine eq_top_iff.2 fun m _ ↦ ?_
  have hg : AdjoinSimple.gen K α ^ n = algebraMap K (adjoin K {α}) (y : K) := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, AdjoinSimple.coe_gen, hα]
    rfl
  obtain ⟨f, hf⟩ := algHom_kummerExtension_mem_fieldRange (F := adjoin K {α})
    (AlgHom.id K (kummerExtension K n Ω (Subgroup.zpowers y)))
    (forall_mem_zpowers_exists_pow_eq ⟨_, hg⟩) m
  have hfm : (f : kummerExtension K n Ω (Subgroup.zpowers y)) = m := hf
  rw [← hfm]
  exact f.2

theorem isCyclic_gal_kummerExtension_zpowers (y : Kˣ) :
    IsCyclic Gal(kummerExtension K n Ω (Subgroup.zpowers y)/K) := by
  set Δ := Subgroup.zpowers y
  let q : Δ ⧸ (unitsPow K n).subgroupOf Δ := ((⟨y, Subgroup.mem_zpowers y⟩ : Δ) : _)
  let ev : ((Δ ⧸ (unitsPow K n).subgroupOf Δ) →* rootsOfUnity n K) →* rootsOfUnity n K :=
    { toFun := fun φ ↦ φ q
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hev : Function.Injective ev := by
    intro φ ψ h
    refine MonoidHom.ext fun c ↦ ?_
    induction c using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨_, k, rfl⟩ := a
      have ha : ((⟨y ^ k, k, rfl⟩ : Δ) : Δ ⧸ (unitsPow K n).subgroupOf Δ) = q ^ k := by
        rw [← QuotientGroup.mk_zpow]
        rfl
      rw [ha, map_zpow, map_zpow]
      exact congrArg (· ^ k) h
  exact isCyclic_of_injective (ev.comp (kummerExtensionGalEquiv K n Ω Δ).toMonoidHom)
    (hev.comp (kummerExtensionGalEquiv K n Ω Δ).injective)

end Kummer

universe u

variable {K : Type u} [Field K] [NumberField K]

theorem FirstInequality.exists_pow_eq_of_forall_pow_eq (hFI : FirstInequality.{u}) {n : ℕ}
    [NeZero n] [HasEnoughRootsOfUnity K n] (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (IdeleGroup.diagonal K).range ⊔ IdeleGroup.sIdeles S = ⊤) {y : Kˣ} (hy : y ∈ S.unit K)
    (hfin : ∀ v ∈ S, ∃ x : v.adicCompletion K, x ^ n = algebraMap K _ (y : K))
    (hinf : ∀ w : InfinitePlace K, ∃ x : w.Completion, x ^ n = algebraMap K _ (y : K)) :
    ∃ z : K, z ^ n = y := by
  set Δ := Subgroup.zpowers y
  set M := kummerExtension K n (AlgebraicClosure K) Δ
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (y : K))
    (NeZero.pos n)
  let α' : M := ⟨α, subset_adjoin _ _ ⟨y, Subgroup.mem_zpowers y, hα⟩⟩
  have hα' : α' ^ n = algebraMap K M (y : K) := kummerExtension_pow_eq hα
  have hgen : adjoin K {α'} = ⊤ := adjoin_eq_top_of_pow_eq α' hα'

  have hnorm : IdeleGroup.sIdeles S ≤ (ideleNorm K M).range := by
    intro x hx
    refine mem_range_ideleNorm_of_forall x (fun v ↦ ?_) (fun w ↦ ?_)
    · by_cases hv : v ∈ S
      · rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
          ((splitsCompletely_kummerExtension_iff v).2
            (forall_mem_zpowers_exists_pow_eq (hfin v hv))))]
        exact Subgroup.mem_top _
      · obtain ⟨w⟩ := nonempty_placesOver M v
        have he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
          Kummer.ramificationIdx_eq_one_of_pow_eq y hα' hgen v (fun h ↦ hv (hS v h))
            (by rw [hy v hv, WithZero.log_one]; exact dvd_zero _) w.1.asIdeal
        have hu : IdeleGroup.finiteProj v x ∈
            (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
          have h := (IdeleGroup.mem_sIdeles_iff S).1 hx v hv
          rw [Submonoid.mem_units_iff, ← map_inv, IdeleGroup.coe_finiteProj,
            IdeleGroup.coe_finiteProj]
          exact ⟨h.1, h.2⟩
        rw [← map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w he] at hu
        obtain ⟨z, -, hz⟩ := hu
        exact ⟨z, hz⟩
    · rw [range_infiniteLocalNorm_eq_top_of_splitsCompletely w
        ((InfinitePlace.splitsCompletely_kummerExtension_iff w).2
          (forall_mem_zpowers_exists_pow_eq (hinf w)))]
      exact Subgroup.mem_top _
  have htop : (ideleNorm K M).range ⊔ (IdeleGroup.diagonal K).range = ⊤ := by
    rw [eq_top_iff, ← hJ]
    exact sup_le le_sup_right (hnorm.trans le_sup_left)
  have := isCyclic_gal_kummerExtension_zpowers (n := n) (Ω := AlgebraicClosure K) y
  have h1 := hFI.finrank_eq_one_of_sup_eq_top htop
  rw [finrank_kummerExtension] at h1
  have hsub : Subsingleton (Δ ⧸ (unitsPow K n).subgroupOf Δ) :=
    (Nat.card_eq_one_iff_unique.1 h1).1
  have hyΔ : (⟨y, Subgroup.mem_zpowers y⟩ : Δ) ∈ (unitsPow K n).subgroupOf Δ := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  obtain ⟨z, hz⟩ := mem_unitsPow.1 (Subgroup.mem_subgroupOf.1 hyΔ)
  exact ⟨z, by rw [← Units.val_pow_eq_pow_val, hz]⟩

end Sec2_08_ExistenceTheorem_LocalPowers

/-! ### 09_ExistenceTheorem.IndexRangePowMonoidHomAdicCompletionMulNorm -/
section Sec2_09_ExistenceTheorem_IndexRangePowMonoidHomAdicCompletionMulNorm

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup


section LocalIndex

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem index_range_powMonoidHom_adicCompletion_mul_norm (v : HeightOneSpectrum (𝓞 K)) :
    ((powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range.index : ℝ) *
      ‖(n : v.adicCompletion K)‖ = (n : ℝ) ^ 2 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have hζv := hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective
  have hn : ‖(n : v.adicCompletion K)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (natCast_ne_zero_adicCompletion (v := v) (NeZero.ne n))
  rw [index_range_powMonoidHom_adicCompletion v (NeZero.ne n), hζv.card_rootsOfUnity,
    div_mul_cancel₀ _ hn, sq]

omit [NumberField K] in

theorem eq_one_or_eq_two_of_isReal {w : InfinitePlace K} (hw : w.IsReal) : n = 1 ∨ n = 2 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  have h := hζ.map_of_injective (InfinitePlace.embedding_of_isReal hw).injective
  set x := InfinitePlace.embedding_of_isReal hw ζ
  have habs : |x| = 1 := by
    have h1 : |x| ^ n = 1 := by rw [← abs_pow, h.pow_eq_one, abs_one]
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg x) (NeZero.ne n)).1 h1
  have hx2 : x ^ 2 = 1 := by rw [← sq_abs, habs, one_pow]
  exact (Nat.dvd_prime Nat.prime_two).1 (h.dvd_of_pow_eq_one 2 hx2)

omit [NumberField K] in

theorem index_range_powMonoidHom_infinitePlaceCompletion_mul_norm (w : InfinitePlace K) :
    ((powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range.index : ℝ) *
      ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ 2 := by
  have hnorm : ‖(n : w.Completion)‖ = n := by
    have h : ‖(n : w.Completion)‖ = w (n : K) := by
      rw [← map_natCast (algebraMap K w.Completion) n]
      exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
    rw [h, InfinitePlace.map_natCast]
  rw [index_range_powMonoidHom_infinitePlaceCompletion w (NeZero.ne n), hnorm]
  rcases w.isReal_or_isComplex with hw | hw
  · rw [hw.mult_eq_one, pow_one]
    rcases eq_one_or_eq_two_of_isReal (n := n) hw with h | h <;> subst h <;> norm_num [hw]
  · have hw' : ¬w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
    rw [hw.mult_eq_two]
    simp [hw']

theorem relIndex_powerSubgroup_empty_eq_pow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).relIndex
        (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) =
      n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  have hpf := prod_norm_natCast_mul_prod_infinitePlace (K := K) (NeZero.ne n) S hS
  apply Nat.cast_injective (R := ℝ)
  rw [relIndex_powerSubgroup_empty]
  push_cast
  have key : ((∏ v ∈ S, ((powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index : ℝ)) *
      ∏ w : InfinitePlace K, ((powMonoidHom n : (w.Completion)ˣ →* _).range.index : ℝ)) *
      ((∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
        ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult) =
      (n : ℝ) ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
    rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    simp_rw [index_range_powMonoidHom_adicCompletion_mul_norm,
      index_range_powMonoidHom_infinitePlaceCompletion_mul_norm]
    rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, ← pow_mul, ← pow_mul, ← pow_add,
      mul_add]
  rwa [hpf, mul_one] at key

end LocalIndex

universe u

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem FirstInequality.comap_sUnitsToSIdeles_powerSubgroup (hFI : FirstInequality.{u})
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles S = ⊤) :
    ((powerSubgroup n S ∅).subgroupOf (sIdeles S)).comap (sUnitsToSIdeles S) =
      (powMonoidHom n : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_sUnitsToSIdeles, powerSubgroup,
    mem_localSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨hf, hi, -⟩
    obtain ⟨z, hz⟩ := hFI.exists_pow_eq_of_forall_pow_eq S hS hJ e.2
      (fun v hv ↦ by
        obtain ⟨u, hu⟩ := hf v hv
        refine ⟨(u : v.adicCompletion K), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, finiteProj_diagonal]
        rfl)
      (fun w ↦ by
        obtain ⟨u, hu⟩ := hi w
        refine ⟨(u : w.Completion), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, infiniteProj_diagonal]
        rfl)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at hz
      exact ((e : Kˣ)).ne_zero hz.symm
    set zu : Kˣ := Units.mk0 z hz0
    have hzun : zu ^ n = (e : Kˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])
    have hzu : zu ∈ S.unit K := by
      intro v hv
      have he : v.valuationOfNeZero (e : Kˣ) = 1 := by
        have h := e.2 v hv
        rw [← valuationOfNeZero_eq] at h
        exact_mod_cast h
      have h1 : v.valuationOfNeZero zu ^ n = 1 := by rw [← map_pow, hzun, he]
      rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne n),
        WithZero.coe_one]
    exact ⟨⟨zu, hzu⟩, Subtype.ext hzun⟩
  · rintro ⟨f, rfl⟩
    refine ⟨fun v _ ↦ ⟨finiteProj v (diagonal K f), ?_⟩,
      fun w ↦ ⟨infiniteProj w (diagonal K f), ?_⟩, fun v hv ↦ ?_⟩
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · exact (diagonal_mem_sIdeles_iff S _).2 (powMonoidHom n f).2 v (by simpa using hv)

theorem FirstInequality.index_map_powerSubgroup (hFI : FirstInequality.{u})
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K)).index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) := by
  set T : Set (HeightOneSpectrum (𝓞 K)) := (S : Set (HeightOneSpectrum (𝓞 K))) with hT
  set W := (powerSubgroup n T ∅).subgroupOf (sIdeles T)
  have hle : powerSubgroup n T ∅ ≤ sIdeles T := by
    simpa using powerSubgroup_le_sIdeles T ∅ n
  have hmap : W.map (sIdelesToIdeleClassGroup T) =
      (powerSubgroup n T ∅).map (IdeleClassGroup.mk K) := by
    rw [sIdelesToIdeleClassGroup, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle]
  have hW : W.index = n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) :=
    relIndex_powerSubgroup_empty_eq_pow S hS
  have hE : (W.comap (sUnitsToSIdeles T)).index = n ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [hFI.comap_sUnitsToSIdeles_powerSubgroup T (fun v hv ↦ Finset.mem_coe.2 (hS v hv)) hJ,
      SUnit.index_range_powMonoidHom, add_comm]
    simp [T]
  have h := index_map_mul_index_comap T hJ W
  rw [hmap, hE, hW, two_mul,
    pow_add n (S.card + Fintype.card (InfinitePlace K)) (S.card + Fintype.card (InfinitePlace K))] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) h

end Sec2_09_ExistenceTheorem_IndexRangePowMonoidHomAdicCompletionMulNorm

/-! ### 10_KummerTheory.KummerIndexLemma.HasEnoughRootsOfUnityOfRingHom -/
section Sec2_10_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RHDirect.CFT_ProfiniteSemilocal.ProfCoh WithZero

namespace KummerIndex

theorem hasEnoughRootsOfUnity_of_ringHom {F E : Type*} [Field F] [Field E] (f : F →+* E)
    (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity F n] : HasEnoughRootsOfUnity E n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
  exact ⟨⟨f ζ, hζ.map_of_injective f.injective⟩, rootsOfUnity.isCyclic E n⟩

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev localUnits : Subgroup (v.adicCompletion K)ˣ :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

variable {v} in

theorem mem_localUnits_iff {x : (v.adicCompletion K)ˣ} :
    x ∈ localUnits v ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  change (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ _
  rw [mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hx)).1 h2)
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩

theorem units_map_mem_localUnits {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) a ∈ localUnits v := by
  rw [mem_localUnits_iff, Units.coe_map]
  change Valued.v ((a : K) : v.adicCompletion K) = 1
  rw [valuedAdicCompletion_eq_valuation', ha]

def localClass (p : ℕ) : Kˣ →* UnitsModPow (v.adicCompletion K) p :=
  (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p)).comp
    (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K))

theorem ker_localClass (p : ℕ) :
    (localClass v p).ker = unitsPowIn K p (v.adicCompletion K) := by
  rw [localClass, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rfl

def localUnitClasses (p : ℕ) : Subgroup (UnitsModPow (v.adicCompletion K) p) :=
  (localUnits v).map (QuotientGroup.mk' (unitsPow (v.adicCompletion K) p))

theorem localClass_mem_localUnitClasses (p : ℕ) {a : Kˣ} (ha : v.valuation K (a : K) = 1) :
    localClass v p a ∈ localUnitClasses v p :=
  Subgroup.mem_map_of_mem _ (units_map_mem_localUnits v ha)

def ordMod (p : ℕ) : (v.adicCompletion K)ˣ →* Multiplicative (ZMod p) where
  toFun x := Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p))
  map_one' := by simp
  map_mul' x y := by
    have hx : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
    rw [Units.val_mul, map_mul, log_mul hx hy, ← ofAdd_add]
    push_cast
    ring_nf

theorem exists_uniformizer_unit :
    ∃ π : (v.adicCompletion K)ˣ, Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨x, hx⟩ := valued_adicCompletion_surjective (v := v) (K := K) (exp (-1 : ℤ))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact exp_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordMod_surjective (p : ℕ) [NeZero p] : Function.Surjective (ordMod v p) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
  intro z
  refine ⟨π ^ (Multiplicative.toAdd z).val, ?_⟩
  change Multiplicative.ofAdd (((-log (Valued.v ((π ^ (Multiplicative.toAdd z).val :
    (v.adicCompletion K)ˣ) : v.adicCompletion K)) : ℤ) : ZMod p)) = z
  rw [Units.val_pow_eq_pow_val, map_pow, hπ, ← exp_nsmul, log_exp]
  simp only [smul_neg, nsmul_eq_mul, mul_one, neg_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
  rfl

theorem ker_ordMod (p : ℕ) [NeZero p] :
    (ordMod v p).ker = localUnits v ⊔ unitsPow (v.adicCompletion K) p := by
  apply le_antisymm
  · intro x hx
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
    rw [MonoidHom.mem_ker] at hx
    change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      at hx
    rw [ofAdd_eq_one, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    obtain ⟨k, hk⟩ := hx
    obtain ⟨π, hπ⟩ := exists_uniformizer_unit v
    have hu : x * ((π ^ k) ^ p)⁻¹ ∈ localUnits v := by
      rw [mem_localUnits_iff, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
        Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_pow, map_zpow₀, hπ,
        ← exp_zsmul, ← exp_nsmul, ← exp_log hx0]
      rw [← exp_neg, ← exp_add]
      have : -(-log (Valued.v (x : v.adicCompletion K))) = (p : ℤ) * (-k) := by
        rw [hk]; ring
      rw [exp_eq_one]
      rw [neg_neg] at this
      rw [this]
      simp only [smul_eq_mul, nsmul_eq_mul]
      ring
    have hx' : x = (x * ((π ^ k) ^ p)⁻¹) * (π ^ k) ^ p := by group
    rw [hx']
    exact Subgroup.mul_mem_sup hu ⟨π ^ k, rfl⟩
  · rw [sup_le_iff]
    constructor
    · intro x hx
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (x : v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [(mem_localUnits_iff).1 hx, log_one]
      simp
    · rintro _ ⟨b, rfl⟩
      have hb : Valued.v (b : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 b.ne_zero
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd (((-log (Valued.v (((b ^ p : (v.adicCompletion K)ˣ)) :
        v.adicCompletion K)) : ℤ) : ZMod p)) = 1
      rw [Units.val_pow_eq_pow_val, map_pow, log_pow]
      simp

theorem index_localUnits_sup_unitsPow (p : ℕ) [NeZero p] :
    (localUnits v ⊔ unitsPow (v.adicCompletion K) p).index = p := by
  rw [← ker_ordMod, Subgroup.index_ker, (ordMod v p).range_eq_top_of_surjective
    (ordMod_surjective v p), Subgroup.card_top, Nat.card_eq_fintype_card]
  simp

theorem index_unitsPow (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) :
    (unitsPow (v.adicCompletion K) p).index = p ^ 2 := by
  have := hasEnoughRootsOfUnity_of_ringHom (algebraMap K (v.adicCompletion K)) p
  have h := index_range_powMonoidHom_adicCompletion_of_hasEnoughRootsOfUnity v (n := p)
  rw [norm_natCast_adicCompletion_eq_one hv, div_one] at h
  exact_mod_cast h

theorem natCard_localUnitClasses (p : ℕ) [NeZero p] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) : Nat.card (localUnitClasses v p) = p := by
  have hidx : (localUnitClasses v p).index = p := by
    rw [localUnitClasses, Subgroup.index_map, QuotientGroup.ker_mk',
      (QuotientGroup.mk' _).range_eq_top_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.index_top, mul_one, index_localUnits_sup_unitsPow]
  have hcard : Nat.card (UnitsModPow (v.adicCompletion K) p) = p ^ 2 :=
    index_unitsPow v p hv
  have h := Subgroup.card_mul_index (localUnitClasses v p)
  rw [hidx, hcard, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right (NeZero.pos p) h

theorem exists_mul_zpow_inv_mem_unitsPow (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity K p]
    (hv : (p : 𝓞 K) ∉ v.asIdeal) {a x : (v.adicCompletion K)ˣ} (ha : a ∈ localUnits v)
    (hx : x ∈ localUnits v) (hap : a ∉ unitsPow (v.adicCompletion K) p) :
    ∃ k : ℤ, x * (a ^ k)⁻¹ ∈ unitsPow (v.adicCompletion K) p := by
  let g : localUnitClasses v p := ⟨QuotientGroup.mk' _ a, Subgroup.mem_map_of_mem _ ha⟩
  let g' : localUnitClasses v p := ⟨QuotientGroup.mk' _ x, Subgroup.mem_map_of_mem _ hx⟩
  have hg : g ≠ 1 := by
    intro h
    apply hap
    have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a = 1 := congrArg Subtype.val h
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_prime_card (natCard_localUnitClasses v p hv) hg (g' := g'))
  refine ⟨k, ?_⟩
  have h' : QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) a ^ k =
      QuotientGroup.mk' (unitsPow (v.adicCompletion K) p) x := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_zpow] at this
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow]
  change QuotientGroup.mk' _ x * (QuotientGroup.mk' _ a ^ k)⁻¹ = 1
  rw [h']
  exact mul_inv_cancel _

end KummerIndex

end Sec2_10_KummerTheory_KummerIndexLemma_HasEnoughRootsOfUnityOfRingHom

/-! ### 11_KummerTheory.KummerIndexLemma.PowerPlaces -/
section Sec2_11_KummerTheory_KummerIndexLemma_PowerPlaces

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RHDirect.CFT_ProfiniteSemilocal.ProfCoh Module
  Filter IntermediateField AdeleBaseChange

namespace KummerIndex

section Radical

variable (K : Type*) [Field K] (p : ℕ)

def radicalGroup (y : Kˣ) : Subgroup Kˣ :=
  Subgroup.zpowers y ⊔ unitsPow K p

variable {K p}

theorem unitsPow_le_radicalGroup (y : Kˣ) : unitsPow K p ≤ radicalGroup K p y :=
  le_sup_right

theorem mem_radicalGroup_self (y : Kˣ) : y ∈ radicalGroup K p y :=
  le_sup_left (a := Subgroup.zpowers y) (Subgroup.mem_zpowers y)

theorem radicalGroup_le {y : Kˣ} {H : Subgroup Kˣ} (hy : y ∈ H) (hH : unitsPow K p ≤ H) :
    radicalGroup K p y ≤ H :=
  sup_le ((Subgroup.zpowers_le).2 hy) hH

theorem radicalClasses_radicalGroup (y : Kˣ) :
    radicalClasses K p (radicalGroup K p y) =
      Subgroup.zpowers (QuotientGroup.mk' (unitsPow K p) y) := by
  rw [radicalClasses, radicalGroup, Subgroup.map_sup, MonoidHom.map_zpowers,
    QuotientGroup.map_mk'_self, sup_bot_eq]

theorem natCard_radicalQuotient (y : Kˣ) :
    Nat.card (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) =
      orderOf (QuotientGroup.mk' (unitsPow K p) y) := by
  rw [Nat.card_congr (radicalQuotientEquiv K p _).toEquiv, radicalClasses_radicalGroup,
    Nat.card_zpowers]

instance finite_radicalQuotient [NeZero p] (y : Kˣ) :
    Finite (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_radicalQuotient]
  exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨p, NeZero.pos p, UnitsModPow.pow_eq_one _ _ _⟩)).ne'

theorem natCard_radicalQuotient_of_not_mem [Fact p.Prime] {y : Kˣ} (hy : y ∉ unitsPow K p) :
    Nat.card (radicalGroup K p y ⧸ (unitsPow K p).subgroupOf (radicalGroup K p y)) = p := by
  rw [natCard_radicalQuotient]
  refine orderOf_eq_prime (UnitsModPow.pow_eq_one _ _ _) ?_
  rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

variable [Fact p.Prime] [HasEnoughRootsOfUnity K p] (Ω : Type*) [Field Ω] [Algebra K Ω]
  [IsSepClosed Ω]

theorem finrank_kummerExtension_radicalGroup {y : Kˣ} (hy : y ∉ unitsPow K p) :
    finrank K (kummerExtension K p Ω (radicalGroup K p y)) = p := by
  rw [finrank_kummerExtension, natCard_radicalQuotient_of_not_mem hy]

theorem isCyclic_kummerExtension_radicalGroup {y : Kˣ} (hy : y ∉ unitsPow K p) :
    IsCyclic Gal(kummerExtension K p Ω (radicalGroup K p y)/K) :=
  isCyclic_of_prime_card (p := p) (by
    rw [IsGalois.card_aut_eq_finrank, finrank_kummerExtension_radicalGroup Ω hy])

theorem unitsPowIn_kummerExtension_radicalGroup (y : Kˣ) :
    unitsPowIn K p (kummerExtension K p Ω (radicalGroup K p y)) = radicalGroup K p y :=
  unitsPowIn_kummerExtension K p Ω _ (unitsPow_le_radicalGroup y)

theorem exists_pow_eq_kummerExtension_radicalGroup (y : Kˣ) :
    ∃ α : kummerExtension K p Ω (radicalGroup K p y), α ^ p = algebraMap K _ (y : K) := by
  have h := mem_radicalGroup_self (p := p) y
  rw [← unitsPowIn_kummerExtension_radicalGroup Ω y] at h
  exact mem_unitsPowIn.1 h

end Radical

section Place

open SemiLocal

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.RHDirect.CFT.Global.FirstInequality.exists_place_mem_unitsPowIn_not_mem
    (hFI : FirstInequality.{u}) {a x : Kˣ} (hx : x ∉ radicalGroup K p a)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (haS : ∀ v ∉ S, v.valuation K (a : K) = 1) (hxS : ∀ v ∉ S, v.valuation K (x : K) = 1) :
    ∃ v ∉ S, a ∈ unitsPowIn K p (v.adicCompletion K) ∧
      x ∉ unitsPowIn K p (v.adicCompletion K) := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  let Ω := AlgebraicClosure K
  let L := kummerExtension K p Ω (radicalGroup K p a)
  have hL : unitsPowIn K p L = radicalGroup K p a :=
    unitsPowIn_kummerExtension_radicalGroup Ω a
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω a
  have : HasEnoughRootsOfUnity L p := hasEnoughRootsOfUnity_of_ringHom (algebraMap K L) p
  let xL : Lˣ := Units.map (algebraMap K L : K →* L) x
  have hxL : xL ∉ unitsPow L p := by
    intro h
    apply hx
    rw [← hL]
    exact Subgroup.mem_comap.2 h
  let L' := kummerExtension L p (AlgebraicClosure L) (radicalGroup L p xL)
  have hfin : finrank L L' = p := finrank_kummerExtension_radicalGroup _ hxL
  have : IsCyclic Gal(L'/L) := isCyclic_kummerExtension_radicalGroup _ hxL
  suffices h : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, SplitsCompletely L' w by
    have h1 := hFI.finrank_eq_one_of_eventually_splitsCompletely h
    rw [hfin] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, below K w ∉ S :=
    tendsto_below.eventually hS.eventually_cofinite_notMem
  filter_upwards [hev] with w hw
  rw [splitsCompletely_kummerExtension_iff]
  suffices key : xL ∈ unitsPowIn L p (w.adicCompletion L) by
    intro c hc
    exact mem_unitsPowIn.1 (radicalGroup_le key (unitsPow_le_unitsPowIn L p _) hc)
  set v := below K w
  have hpv : (p : 𝓞 K) ∉ v.asIdeal := fun h ↦ hw (hpS v h)
  let ιK : Kˣ →* (w.adicCompletion L)ˣ := Units.map (algebraMap K (w.adicCompletion L) : K →* _)
  let ιv : (v.adicCompletion K)ˣ →* (w.adicCompletion L)ˣ :=
    Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L) : _ →* _)
  let κ : Kˣ →* (v.adicCompletion K)ˣ := Units.map (algebraMap K (v.adicCompletion K) : K →* _)
  have hικ (z : Kˣ) : ιv (κ z) = ιK z := by
    apply Units.ext
    simp only [ιv, ιK, κ, Units.coe_map, MonoidHom.coe_coe]
    exact (IsScalarTower.algebraMap_apply K (v.adicCompletion K) (w.adicCompletion L) _).symm
  have hxLw : ((ιK x : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      algebraMap L (w.adicCompletion L) (xL : L) := by
    simp only [ιK, xL, Units.coe_map, MonoidHom.coe_coe]
    exact IsScalarTower.algebraMap_apply K L (w.adicCompletion L) _
  suffices h : ιK x ∈ unitsPow (w.adicCompletion L) p by
    obtain ⟨b, hb⟩ := mem_unitsPow.1 h
    refine mem_unitsPowIn.2 ⟨b, ?_⟩
    rw [← hxLw, ← hb, Units.val_pow_eq_pow_val]
  by_cases ha : a ∈ unitsPowIn K p (v.adicCompletion K)
  · obtain ⟨b, hb⟩ := mem_unitsPow.1 (Subgroup.mem_comap.1 (hcon v hw ha))
    refine mem_unitsPow.2 ⟨ιv b, ?_⟩
    rw [← map_pow, hb]
    exact hικ x
  · have ha' : κ a ∉ unitsPow (v.adicCompletion K) p := fun h ↦ ha (Subgroup.mem_comap.2 h)
    obtain ⟨k, hk⟩ := exists_mul_zpow_inv_mem_unitsPow v p hpv
      (units_map_mem_localUnits v (haS v hw)) (units_map_mem_localUnits v (hxS v hw)) ha'
    obtain ⟨b, hb⟩ := mem_unitsPow.1 hk
    have hα0 : algebraMap L (w.adicCompletion L) (α : L) ≠ 0 := by
      rw [ne_eq, map_eq_zero]
      intro h0
      have h1 : (α : kummerExtension K p Ω (radicalGroup K p a)) = 0 := h0
      rw [h1, zero_pow (Fact.out : p.Prime).ne_zero, eq_comm, map_eq_zero] at hα
      exact a.ne_zero hα
    let αw : (w.adicCompletion L)ˣ := Units.mk0 _ hα0
    have hαw : αw ^ p = ιK a := by
      apply Units.ext
      simp only [αw, ιK, Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, MonoidHom.coe_coe]
      rw [← map_pow]
      change algebraMap L (w.adicCompletion L) ((α ^ p : kummerExtension K p Ω _) : L) = _
      rw [hα, IsScalarTower.algebraMap_apply K L (w.adicCompletion L)]
    refine mem_unitsPow.2 ⟨ιv b * αw ^ k, ?_⟩
    have hb' : ιv b ^ p = ιK x * (ιK a ^ k)⁻¹ := by
      rw [← map_pow, hb, map_mul, map_inv, map_zpow, hικ, hικ]
    have hαk : (αw ^ k) ^ p = ιK a ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hαw]
    rw [mul_pow, hb', hαk, inv_mul_cancel_right]

end Place

end KummerIndex

end Sec2_11_KummerTheory_KummerIndexLemma_PowerPlaces

/-! ### 12_KummerTheory.KummerIndexLemma.Places -/
section Sec2_12_KummerTheory_KummerIndexLemma_Places

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RHDirect.CFT_ProfiniteSemilocal.ProfCoh

namespace KummerIndex

variable {K : Type*} [Field K] [NumberField K]

def unitsPowAt (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  ⨅ v ∈ T, unitsPowIn K p (v.adicCompletion K)

theorem mem_unitsPowAt {p : ℕ} {T : Finset (HeightOneSpectrum (𝓞 K))} {x : Kˣ} :
    x ∈ unitsPowAt p T ↔ ∀ v ∈ T, x ∈ unitsPowIn K p (v.adicCompletion K) := by
  simp only [unitsPowAt, Subgroup.mem_iInf]

theorem unitsPowAt_empty (p : ℕ) : unitsPowAt (K := K) p ∅ = ⊤ := by
  ext x
  simp [mem_unitsPowAt]

theorem unitsPowAt_insert [DecidableEq (HeightOneSpectrum (𝓞 K))] (p : ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsPowAt p (insert v T) = unitsPowIn K p (v.adicCompletion K) ⊓ unitsPowAt p T := by
  ext x
  simp only [mem_unitsPowAt, Finset.mem_insert, forall_eq_or_imp, Subgroup.mem_inf]

theorem unitsPow_le_unitsPowAt (p : ℕ) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    unitsPow K p ≤ unitsPowAt p T := fun _ hx ↦
  mem_unitsPowAt.2 fun _ _ ↦ unitsPow_le_unitsPowIn K p _ hx

variable {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem exists_localClass_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpT : ∀ v ∈ T, (p : 𝓞 K) ∉ v.asIdeal)
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      p ^ T.card)
    (z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ)
    (hz : ∀ v ∈ T, z v ∈ localUnits v) :
    ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, ∀ v ∈ T,
      localClass v p δ = QuotientGroup.mk (z v) := by
  classical
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hvS : ∀ v ∈ T, v ∉ (S : Set (HeightOneSpectrum (𝓞 K))) := fun v hv hvS ↦
    Finset.disjoint_left.1 hST (Finset.mem_coe.1 hvS) hv
  let _ : ∀ v : T, Group (UnitsModPow (v.1.adicCompletion K) p) := fun _ ↦ inferInstance
  let ψ : Δ →* ((v : T) → UnitsModPow (v.1.adicCompletion K) p) :=
    MonoidHom.pi fun v ↦ (localClass v.1 p).comp Δ.subtype
  have hker : ψ.ker = (unitsPowAt p T).subgroupOf Δ := by
    ext δ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitsPowAt, funext_iff]
    constructor
    · intro h v hv
      rw [← ker_localClass]
      exact h ⟨v, hv⟩
    · intro h v
      have := h v.1 v.2
      rw [← ker_localClass] at this
      exact this
  let U : Subgroup ((v : T) → UnitsModPow (v.1.adicCompletion K) p) :=
    Subgroup.pi Set.univ fun v ↦ localUnitClasses v.1 p
  have hU : Nat.card U = p ^ T.card := by
    have e : U ≃ ∀ v : T, localUnitClasses v.1 p :=
      (Equiv.subtypeEquivRight fun f ↦ by simp [U, Subgroup.mem_pi]).trans
        (Equiv.subtypePiEquivPi)
    rw [Nat.card_congr e, Nat.card_pi,
      Finset.prod_congr rfl fun v _ ↦ natCard_localUnitClasses v.1 p (hpT v.1 v.2),
      Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hrange : Nat.card ψ.range = p ^ T.card := by
    rw [← Subgroup.index_ker, hker, ← Subgroup.relIndex, hidx]
  have hle : ψ.range ≤ U := by
    rintro _ ⟨δ, rfl⟩
    rw [Subgroup.mem_pi]
    intro v _
    exact localClass_mem_localUnitClasses v.1 p (Set.unit_valuation_eq_one (S := (S : Set (HeightOneSpectrum (𝓞 K)))) (K := K) δ (hvS v.1 v.2))
  have : Finite U := Nat.finite_of_card_ne_zero (by
    rw [hU]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have heq : ψ.range = U := Subgroup.eq_of_le_of_card_ge hle (by rw [hU, hrange])
  have hf : (fun v : T ↦ (QuotientGroup.mk (z v.1) : UnitsModPow (v.1.adicCompletion K) p)) ∈
      ψ.range := by
    rw [heq, Subgroup.mem_pi]
    intro v _
    exact Subgroup.mem_map_of_mem _ (hz v.1 v.2)
  obtain ⟨δ, hδ⟩ := hf
  refine ⟨δ, δ.2, fun v hv ↦ ?_⟩
  exact congrFun hδ ⟨v, hv⟩

universe u

variable {K : Type u} [Field K] [NumberField K] [HasEnoughRootsOfUnity K p]

omit [Fact p.Prime] [HasEnoughRootsOfUnity K p] in

theorem valuation_eq_one_of_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} {x : Kˣ}
    (hx : x ∈ S.unit K) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    v.valuation K (x : K) = 1 :=
  Set.unit_valuation_eq_one (S := S) (K := K) ⟨x, hx⟩ hv

omit [HasEnoughRootsOfUnity K p] in

theorem relIndex_unitsPow_sUnit_ne_zero (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K p).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) ≠ 0 := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hfi := Subgroup.finiteIndex_range_powMonoidHom_of_fg Δ (Fact.out : p.Prime).ne_zero
  have hle : (powMonoidHom p : Δ →* Δ).range ≤ (unitsPow K p).subgroupOf Δ := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(y : Kˣ), rfl⟩
  exact fun h ↦ hfi.index_ne_zero (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

theorem _root_.RHDirect.CFT.Global.FirstInequality.exists_place_relIndex_unitsPowAt_insert
    (hFI : FirstInequality.{u}) [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) {T : Finset (HeightOneSpectrum (𝓞 K))}
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
      p ^ T.card)
    {x : Kˣ} (hxΔ : x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hxT : x ∈ unitsPowAt p T)
    (hxa : x ∉ radicalGroup K p a) :
    ∃ v, v ∉ S ∧ v ∉ T ∧ a ∈ unitsPowIn K p (v.adicCompletion K) ∧
      (unitsPowAt p (insert v T)).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) =
        p ^ (T.card + 1) := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hfin : ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).Finite :=
    (S.finite_toSet).union T.finite_toSet
  obtain ⟨v, hv, hav, hxv⟩ := hFI.exists_place_mem_unitsPowIn_not_mem hxa hfin
    (fun v hv ↦ Or.inl (hpS v hv))
    (fun v hv ↦ valuation_eq_one_of_mem_unit ha (fun h ↦ hv (Or.inl h)))
    (fun v hv ↦ valuation_eq_one_of_mem_unit hxΔ (fun h ↦ hv (Or.inl h)))
  have hvS : v ∉ S := fun h ↦ hv (Or.inl h)
  have hvT : v ∉ T := fun h ↦ hv (Or.inr h)
  refine ⟨v, hvS, hvT, hav, ?_⟩
  have hpv : (p : 𝓞 K) ∉ v.asIdeal := fun h ↦ hvS (hpS v h)
  rw [unitsPowAt_insert, ← Subgroup.relIndex_inf_mul_relIndex, hidx, pow_succ, mul_comm]
  congr 1
  rw [← ker_localClass, Subgroup.relIndex_ker]
  set H := (unitsPowAt p T ⊓ Δ).map (localClass v p)
  have hle : H ≤ localUnitClasses v p := by
    rintro _ ⟨y, hy, rfl⟩
    exact localClass_mem_localUnitClasses v p (valuation_eq_one_of_mem_unit hy.2 hvS)
  have hdvd : Nat.card H ∣ p := by
    have := Subgroup.card_dvd_of_le hle
    rwa [natCard_localUnitClasses v p hpv] at this
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
  · exfalso
    have hbot := Subgroup.card_eq_one.1 h1
    have hmem : localClass v p x ∈ H := Subgroup.mem_map_of_mem _ ⟨hxT, hxΔ⟩
    rw [hbot, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_localClass] at hmem
    exact hxv hmem
  · exact hp

theorem _root_.RHDirect.CFT.Global.FirstInequality.exists_places_unitsPowAt
    (hFI : FirstInequality.{u}) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
      (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = p ^ T.card ∧
      ∀ x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, x ∈ unitsPowAt p T →
        x ∈ radicalGroup K p a := by
  classical
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  let Good : Finset (HeightOneSpectrum (𝓞 K)) → Prop := fun T ↦ Disjoint S T ∧
    (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
    (unitsPowAt p T).relIndex Δ = p ^ T.card
  have key : ∀ n : ℕ, ∃ T, Good T ∧
      (n ≤ T.card ∨ ∀ x ∈ Δ, x ∈ unitsPowAt p T → x ∈ radicalGroup K p a) := by
    intro n
    induction n with
    | zero =>
      refine ⟨∅, ⟨Finset.disjoint_empty_right S, by simp, ?_⟩, Or.inl le_rfl⟩
      rw [unitsPowAt_empty, Subgroup.relIndex_top_left, Finset.card_empty, pow_zero]
    | succ n ih =>
      obtain ⟨T, hT, h | h⟩ := ih
      · by_cases hfin : ∀ x ∈ Δ, x ∈ unitsPowAt p T → x ∈ radicalGroup K p a
        · exact ⟨T, hT, Or.inr hfin⟩
        · simp only [not_forall, exists_prop] at hfin
          obtain ⟨x, hxΔ, hxT, hxa⟩ := hfin
          obtain ⟨v, hvS, hvT, hav, hidx⟩ :=
            hFI.exists_place_relIndex_unitsPowAt_insert S hpS ha hT.2.2 hxΔ hxT hxa
          refine ⟨insert v T, ⟨?_, ?_, ?_⟩, Or.inl ?_⟩
          · exact Finset.disjoint_insert_right.2 ⟨hvS, hT.1⟩
          · intro w hw
            rcases Finset.mem_insert.1 hw with rfl | hw
            · exact hav
            · exact hT.2.1 w hw
          · rw [Finset.card_insert_of_notMem hvT, hidx]
          · rw [Finset.card_insert_of_notMem hvT]
            omega
      · exact ⟨T, hT, Or.inr h⟩
  set B := (unitsPow K p).relIndex Δ
  have hB : B ≠ 0 := relIndex_unitsPow_sUnit_ne_zero S
  obtain ⟨T, hT, h | h⟩ := key B
  · exfalso
    have hdvd : p ^ T.card ∣ B :=
      hT.2.2 ▸ Subgroup.relIndex_dvd_of_le_left Δ (unitsPow_le_unitsPowAt p T)
    have h1 : p ^ T.card ≤ B := Nat.le_of_dvd (Nat.pos_of_ne_zero hB) hdvd
    have h2 : T.card < p ^ T.card := Nat.lt_pow_self (Fact.out : p.Prime).one_lt
    omega
  · exact ⟨T, hT.1, hT.2.1, hT.2.2, h⟩

end KummerIndex

end Sec2_12_KummerTheory_KummerIndexLemma_Places

/-! ### 13_KummerTheory.KummerIndexLemma.PowerKernel -/
section Sec2_13_KummerTheory_KummerIndexLemma_PowerKernel

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RHDirect.CFT_ProfiniteSemilocal.ProfCoh Module
  Filter IntermediateField AdeleBaseChange SemiLocal IdeleNorm

open scoped NumberField.LiesOver

namespace KummerIndex

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem finiteProj_mem_localUnits {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K}
    (h : IdeleGroup.ord v x = 0) : IdeleGroup.finiteProj v x ∈ localUnits v := by
  have hx := (IdeleGroup.ord_eq_zero_iff v x).1 h
  rw [localUnits, Submonoid.mem_units_iff]
  have h2 : ((IdeleGroup.finiteProj v x)⁻¹ : (v.adicCompletion K)ˣ) =
      IdeleGroup.finiteProj v x⁻¹ := (map_inv _ _).symm
  rw [h2, IdeleGroup.coe_finiteProj, IdeleGroup.coe_finiteProj]
  exact hx

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (b : (v.adicCompletion K)ˣ) : b ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  classical
  let y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ := fun w ↦
    Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
      v.adicCompletion K →* w.1.adicCompletion L) b
  refine ⟨y, ?_⟩
  rw [← Finset.univ_prod_mulSingle y, map_prod]
  simp_rw [y, finiteLocalNorm_mulSingle_algebraMap]
  rw [Finset.prod_pow_eq_pow_sum, sum_finrank_eq]

theorem range_infiniteLocalNorm_eq_top_of_splitsCompletely (w : InfinitePlace K)
    (h : InfinitePlace.SplitsCompletely L w) : (infiniteLocalNorm L w).range = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨w'⟩ := nonempty_infinitePlacesOver L w
  have hd := (InfinitePlace.splitsCompletely_iff_forall_finrank w).1 h w'
  refine ⟨Pi.mulSingle w' (Units.map (algebraMap w.Completion
    (w' : InfinitePlace L).Completion : w.Completion →* (w' : InfinitePlace L).Completion) u), ?_⟩
  rw [infiniteLocalNorm_mulSingle]
  apply Units.ext
  simp [RHDirect.CFT.LocalField.normUnits, Algebra.norm_algebraMap, hd]

end LocalNorms

universe u

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.RHDirect.CFT.Global.FirstInequality.mem_unitsPow_of_forall_mem_unitsPowIn
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hS : (IdeleGroup.diagonal K).range ⊔
      IdeleGroup.sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v))
    {y : Kˣ}
    (hyE : y ∈ ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ (T : Set (HeightOneSpectrum (𝓞 K)))).unit K)
    (hyS : ∀ v ∈ S, y ∈ unitsPowIn K p (v.adicCompletion K))
    (hyinf : ∀ w : InfinitePlace K, y ∈ unitsPowIn K p w.Completion) :
    y ∈ unitsPow K p := by
  classical
  by_contra hy
  let Ω := AlgebraicClosure K
  let F := kummerExtension K p Ω (radicalGroup K p y)
  have hfinF : finrank K F = p := finrank_kummerExtension_radicalGroup Ω hy
  have : IsCyclic Gal(F/K) := isCyclic_kummerExtension_radicalGroup Ω hy
  obtain ⟨α, hα⟩ := exists_pow_eq_kummerExtension_radicalGroup (p := p) Ω y
  have hgen : IntermediateField.adjoin K {α} = ⊤ := by
    have hdvd : finrank K (IntermediateField.adjoin K {α}) ∣ p := by
      have := IntermediateField.finrank_dvd_of_le_right (K := K)
        (le_top : IntermediateField.adjoin K {α} ≤ ⊤)
      rwa [IntermediateField.finrank_top', hfinF] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hpp
    · exfalso
      rw [IntermediateField.finrank_eq_one_iff] at h1
      have hmem : α ∈ (⊥ : IntermediateField K F) :=
        h1 ▸ IntermediateField.mem_adjoin_simple_self K α
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hmem
      have hcp : c ^ p = (y : K) := by
        apply (algebraMap K F).injective
        rw [map_pow, hc, hα]
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_pow (Fact.out : p.Prime).ne_zero] at hcp
        exact y.ne_zero hcp.symm
      exact hy (mem_unitsPow.2 ⟨Units.mk0 c hc0, Units.ext (by simp [hcp])⟩)
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hpp, IntermediateField.finrank_top', hfinF])
  suffices h : (ideleNorm K F).range ⊔ (IdeleGroup.diagonal K).range = ⊤ by
    have h1 := hFI.finrank_eq_one_of_sup_eq_top h
    rw [hfinF] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hsplit : ∀ v ∈ S, (finiteLocalNorm F v).range = ⊤ := fun v hv ↦
    range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
      ((splitsCompletely_kummerExtension_iff v).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyS v hv) (unitsPow_le_unitsPowIn K p _) hc)))
  have hinf : ∀ w, (infiniteLocalNorm F w).range = ⊤ := fun w ↦
    range_infiniteLocalNorm_eq_top_of_splitsCompletely w
      ((InfinitePlace.splitsCompletely_kummerExtension_iff w).2 fun c hc ↦
        mem_unitsPowIn.1 (radicalGroup_le (hyinf w) (unitsPow_le_unitsPowIn K p _) hc))
  have hunr : ∀ v, v ∉ S → v ∉ T →
      (integerUnitsOver F v).map (finiteLocalNorm F v) = localUnits v := by
    intro v hvS hvT
    obtain ⟨w⟩ := nonempty_placesOver F v
    have := w.1.isPrime
    refine map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w ?_
    refine Kummer.ramificationIdx_eq_one_of_pow_eq y hα hgen v (fun h ↦ hvS (hpS v h)) ?_
      w.1.asIdeal
    rw [valuation_eq_one_of_mem_unit hyE (by simp [hvS, hvT]), WithZero.log_one]
    exact dvd_zero _
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, s, hs, rfl⟩ := IdeleGroup.exists_diagonal_mul_of_sup_eq_top _ hS x
  have hsv : ∀ v ∉ S, IdeleGroup.finiteProj v s ∈ localUnits v := fun v hv ↦
    finiteProj_mem_localUnits ((IdeleGroup.mem_sIdeles _).1 hs v (by simpa using hv))
  obtain ⟨δ, hδ, hδT⟩ := hsurj (fun v ↦ IdeleGroup.finiteProj v s)
    (fun v hv ↦ hsv v (Finset.disjoint_right.1 hST hv))
  set t := IdeleGroup.diagonal K δ⁻¹ * s with ht_def
  have hloc : ∀ v, v ∉ S → IdeleGroup.finiteProj v t ∈ localUnits v := by
    intro v hvS
    rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal]
    exact mul_mem (units_map_mem_localUnits v (valuation_eq_one_of_mem_unit (inv_mem hδ)
      (by simpa using hvS))) (hsv v hvS)
  have ht : t ∈ (ideleNorm K F).range := by
    rw [mem_range_ideleNorm_iff]
    refine ⟨fun v ↦ ?_, fun w ↦ by rw [hinf w]; exact Subgroup.mem_top _, ?_⟩
    · by_cases hvS : v ∈ S
      · rw [hsplit v hvS]
        exact Subgroup.mem_top _
      by_cases hvT : v ∈ T
      · have hpow : IdeleGroup.finiteProj v t ∈ unitsPow (v.adicCompletion K) p := by
          rw [ht_def, map_mul, IdeleGroup.finiteProj_diagonal, map_inv]
          exact QuotientGroup.eq.1 (hδT v hvT)
        obtain ⟨b, hb⟩ := mem_unitsPow.1 hpow
        have hnorm := pow_finrank_mem_range_finiteLocalNorm (L := F) v b
        rw [hfinF, hb] at hnorm
        exact hnorm
      · exact Subgroup.map_le_range _ _ (hunr v hvS hvT ▸ hloc v hvS)
    · filter_upwards [(S.finite_toSet.union T.finite_toSet).eventually_cofinite_notMem] with v hv
      simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
      rw [hunr v hv.1 hv.2]
      exact hloc v hv.1
  have hs_eq : s = t * IdeleGroup.diagonal K δ := by
    rw [ht_def, map_inv, mul_comm, mul_inv_cancel_left]
  rw [hs_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a, rfl⟩)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right ⟨δ, rfl⟩))

end KummerIndex

end Sec2_13_KummerTheory_KummerIndexLemma_PowerKernel

/-! ### 14_KummerTheory.KummerIndexLemma -/
section Sec2_14_KummerTheory_KummerIndexLemma

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RHDirect.CFT_ProfiniteSemilocal.ProfCoh IdeleGroup

namespace KummerIndex

variable {K : Type*} [Field K] [NumberField K] {p : ℕ}

theorem mem_unit_of_pow_mem_unit {S : Set (HeightOneSpectrum (𝓞 K))} (hp : p ≠ 0) {b : Kˣ}
    (hb : b ^ p ∈ S.unit K) : b ∈ S.unit K := by
  intro v hv
  have he : v.valuationOfNeZero (b ^ p) = 1 := by
    have h := hb v hv
    rw [← valuationOfNeZero_eq] at h
    exact_mod_cast h
  rw [map_pow] at he
  rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 he).resolve_right hp, WithZero.coe_one]

theorem unitsPow_subgroupOf_unit (S : Set (HeightOneSpectrum (𝓞 K))) (hp : p ≠ 0) :
    (unitsPow K p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, mem_unitsPow]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨⟨b, mem_unit_of_pow_mem_unit hp (hb ▸ e.2)⟩, Subtype.ext ?_⟩
    rw [powMonoidHom_apply, Subgroup.coe_pow]
    exact hb
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem relIndex_powerSubgroup_eq_pow [NeZero p] [HasEnoughRootsOfUnity K p]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) T).relIndex
        (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  rw [relIndex_powerSubgroup, ← relIndex_powerSubgroup_empty, relIndex_powerSubgroup_empty_eq_pow S hpS]

universe u

variable {K : Type u} [Field K] [NumberField K] [Fact p.Prime] [HasEnoughRootsOfUnity K p]

theorem _root_.RHDirect.CFT.Global.FirstInequality.comap_sUnitsToSIdeles_powerSubgroup_union
    (hFI : FirstInequality.{u}) (S T : Finset (HeightOneSpectrum (𝓞 K))) (hST : Disjoint S T)
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    (hsurj : ∀ z : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ,
      (∀ v ∈ T, z v ∈ localUnits v) → ∃ δ ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K,
        ∀ v ∈ T, localClass v p δ = QuotientGroup.mk (z v)) :
    ((powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).subgroupOf
        (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T))).comap
          (sUnitsToSIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (powMonoidHom p : ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T).unit K →* _).range := by
  ext e
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_sUnitsToSIdeles, powerSubgroup,
    mem_localSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨hf, hi, -⟩
    have hy := hFI.mem_unitsPow_of_forall_mem_unitsPowIn S T hST hpS hJ hsurj e.2
      (fun v hv ↦ by
        obtain ⟨u, hu⟩ := hf v hv
        refine mem_unitsPowIn.2 ⟨(u : v.adicCompletion K), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, finiteProj_diagonal]
        rfl)
      (fun w ↦ by
        obtain ⟨u, hu⟩ := hi w
        refine mem_unitsPowIn.2 ⟨(u : w.Completion), ?_⟩
        rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hu, infiniteProj_diagonal]
        rfl)
    obtain ⟨b, hb⟩ := mem_unitsPow.1 hy
    refine ⟨⟨b, mem_unit_of_pow_mem_unit (Fact.out : p.Prime).ne_zero (hb ▸ e.2)⟩,
      Subtype.ext ?_⟩
    rw [powMonoidHom_apply, Subgroup.coe_pow]
    exact hb
  · rintro ⟨f, rfl⟩
    refine ⟨fun v _ ↦ ⟨finiteProj v (diagonal K f), ?_⟩,
      fun w ↦ ⟨infiniteProj w (diagonal K f), ?_⟩, fun v hv ↦ ?_⟩
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · rw [powMonoidHom_apply, ← map_pow, ← map_pow]
      rfl
    · exact (diagonal_mem_sIdeles_iff _ _).2 (powMonoidHom p f).2 v hv

theorem card_add_one_eq (S T : Finset (HeightOneSpectrum (𝓞 K))) {a : Kˣ}
    (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hap : a ∉ unitsPow K p)
    (haT : ∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K))
    (hidx : (unitsPowAt p T).relIndex ((S : Set (HeightOneSpectrum (𝓞 K))).unit K) = p ^ T.card)
    (hker : ∀ x ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K, x ∈ unitsPowAt p T →
      x ∈ radicalGroup K p a) :
    T.card + 1 = S.card + Fintype.card (InfinitePlace K) := by
  set Δ := (S : Set (HeightOneSpectrum (𝓞 K))).unit K
  have hΔp : (unitsPow K p).relIndex Δ = p ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [Subgroup.relIndex, unitsPow_subgroupOf_unit _ (Fact.out : p.Prime).ne_zero,
      SUnit.index_range_powMonoidHom]
    simp
  have heq : radicalGroup K p a ⊓ Δ = unitsPowAt p T ⊓ Δ := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨radicalGroup_le (mem_unitsPowAt.2 haT) (unitsPow_le_unitsPowAt p T) h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hker x h2 h1, h2⟩
  have hrad : (radicalGroup K p a).relIndex Δ = p ^ T.card := by
    rw [← Subgroup.inf_relIndex_right, heq, Subgroup.inf_relIndex_right, hidx]
  have hstep : (unitsPow K p).relIndex (radicalGroup K p a ⊓ Δ) = p := by
    rw [← QuotientGroup.ker_mk' (unitsPow K p), Subgroup.relIndex_ker]
    set H := (radicalGroup K p a ⊓ Δ).map (QuotientGroup.mk' (unitsPow K p))
    have hle : H ≤ Subgroup.zpowers (QuotientGroup.mk' (unitsPow K p) a) := by
      rw [← radicalClasses_radicalGroup]
      exact Subgroup.map_mono inf_le_left
    have hord : orderOf (QuotientGroup.mk' (unitsPow K p) a) = p := by
      refine orderOf_eq_prime (UnitsModPow.pow_eq_one _ _ _) ?_
      rwa [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hdvd : Nat.card H ∣ p := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hord] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
    · exfalso
      have hbot := Subgroup.card_eq_one.1 h1
      have hmem : QuotientGroup.mk' (unitsPow K p) a ∈ H :=
        Subgroup.mem_map_of_mem _ ⟨mem_radicalGroup_self a, ha⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact hap hmem
    · exact hp
  have h := Subgroup.relIndex_inf_mul_relIndex (unitsPow K p) (radicalGroup K p a) Δ
  rw [inf_of_le_left (unitsPow_le_radicalGroup a), hstep, hrad, hΔp, ← pow_succ'] at h
  have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h
  omega

theorem _root_.RHDirect.CFT.Global.FirstInequality.exists_places_index_map_powerSubgroup
    (hFI : FirstInequality.{u}) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤)
    {a : Kˣ} (ha : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K) (hap : a ∉ unitsPow K p) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), Disjoint S T ∧
      T.card + 1 = S.card + Fintype.card (InfinitePlace K) ∧
      (∀ v ∈ T, a ∈ unitsPowIn K p (v.adicCompletion K)) ∧
      ((powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).map
        (IdeleClassGroup.mk K)).index = p := by
  classical
  obtain ⟨T, hST, haT, hidx, hker⟩ := hFI.exists_places_unitsPowAt S hpS ha
  have hcard := card_add_one_eq S T ha hap haT hidx hker
  refine ⟨T, hST, hcard, haT, ?_⟩
  have hpT : ∀ v ∈ T, (p : 𝓞 K) ∉ v.asIdeal := fun v hv h ↦
    Finset.disjoint_right.1 hST hv (hpS v h)
  have hsurj := exists_localClass_eq S T hST hpT hidx
  set S' : Set (HeightOneSpectrum (𝓞 K)) := (S : Set (HeightOneSpectrum (𝓞 K))) ∪ T with hS'
  have hJ' : (diagonal K).range ⊔ sIdeles S' = ⊤ :=
    sup_sIdeles_eq_top_of_subset Set.subset_union_left hJ
  set W := (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).subgroupOf
    (sIdeles S')
  have hle : powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))) ≤
      sIdeles S' :=
    powerSubgroup_le_sIdeles _ _ p
  have hmap : W.map (sIdelesToIdeleClassGroup S') =
      (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K)))).map
        (IdeleClassGroup.mk K) := by
    rw [sIdelesToIdeleClassGroup, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hle]
  have hW : W.index = p ^ (2 * (S.card + Fintype.card (InfinitePlace K))) :=
    relIndex_powerSubgroup_eq_pow S T hpS
  have hcardS' : Nat.card S' = S.card + T.card := by
    rw [hS', ← Finset.coe_union, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      Finset.card_union_of_disjoint hST]
  have hE : (W.comap (sUnitsToSIdeles S')).index =
      p ^ (Fintype.card (InfinitePlace K) + (S.card + T.card)) := by
    rw [hFI.comap_sUnitsToSIdeles_powerSubgroup_union S T hST hpS hJ hsurj,
      SUnit.index_range_powMonoidHom, hcardS']
  have h := index_map_mul_index_comap S' hJ' W
  rw [hmap, hE, hW] at h
  have h2 : 2 * (S.card + Fintype.card (InfinitePlace K)) =
      1 + (Fintype.card (InfinitePlace K) + (S.card + T.card)) := by omega
  rw [h2, pow_add p 1, pow_one] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos _) h

end KummerIndex

end Sec2_14_KummerTheory_KummerIndexLemma

/-! ### 15_PowerSubgroupIndex.Existence -/
section Sec2_15_PowerSubgroupIndex_Existence

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RHDirect.CFT_ProfiniteSemilocal.ProfCoh IdeleGroup
  KummerIndex

universe u

section Power

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem index_map_powerSubgroup (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K)).index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) :=
  firstInequality.index_map_powerSubgroup S hS hJ

end Power

section Prime

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] [HasEnoughRootsOfUnity K p]

end Prime

end Sec2_15_PowerSubgroupIndex_Existence

/-! ### 16_SecondInequality.Statement -/
section Sec2_16_SecondInequality_Statement

open NumberField Module Polynomial IntermediateField

section GroupTheory

variable {G G' : Type*} [Group G] [Group G']

theorem enatCard_quotient_le_iff (H : Subgroup G) (n : ℕ) :
    ENat.card (G ⧸ H) ≤ n ↔ H.index ≠ 0 ∧ H.index ≤ n := by
  by_cases hf : Finite (G ⧸ H)
  · rw [ENat.card_eq_coe_natCard, Nat.cast_le]
    exact ⟨fun h ↦ ⟨Subgroup.index_ne_zero_of_finite, h⟩, fun h ↦ h.2⟩
  · have : Infinite (G ⧸ H) := not_finite_iff_infinite.1 hf
    rw [ENat.card_eq_top_of_infinite]
    refine ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd h.1 ?_⟩
    rw [not_not, Subgroup.index, Nat.card_eq_zero_of_infinite]

theorem index_le_of_comap_le (f : G →* G') {H : Subgroup G} {H' : Subgroup G'}
    (hle : H'.comap f ≤ H) (hH' : H'.index ≠ 0) : H.index ≠ 0 ∧ H.index ≤ H'.index := by
  have h1 : (H'.comap f).index ≤ H'.index := by
    rw [Subgroup.index_comap, ← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top (by rwa [Subgroup.relIndex_top_right])
  have h2 : (H'.comap f).index ≠ 0 := by
    rw [Subgroup.index_comap]
    exact mt (Subgroup.relIndex_eq_zero_of_le_right le_top) (by rwa [Subgroup.relIndex_top_right])
  have h3 : H.index ∣ (H'.comap f).index := Subgroup.index_dvd_of_le hle
  exact ⟨fun h ↦ h2 (Nat.eq_zero_of_zero_dvd (h ▸ h3)), (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h3).trans h1⟩

theorem index_map_le (f : G →* G') {H : Subgroup G} (hH : H.index ≠ 0) (hf : f.range.index ≠ 0) :
    (H.map f).index ≠ 0 ∧ (H.map f).index ≤ f.range.index * H.index := by
  have h3 : (H ⊔ f.ker).index ∣ H.index := Subgroup.index_dvd_of_le le_sup_left
  have h4 : (H ⊔ f.ker).index ≠ 0 := fun h ↦ hH (Nat.eq_zero_of_zero_dvd (h ▸ h3))
  rw [Subgroup.index_map]
  refine ⟨mul_ne_zero h4 hf, ?_⟩
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (Nat.pos_of_ne_zero hH) h3)

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {x : G} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ H) (hb : x ^ b ∈ H) : x ∈ H := by
  have hg : ((a.gcd b : ℕ) : ℤ) = a * a.gcdA b + b * a.gcdB b := Nat.gcd_eq_gcd_ab a b
  rw [hab, Nat.cast_one] at hg
  have : x = (x ^ a) ^ a.gcdA b * (x ^ b) ^ a.gcdB b := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hg, zpow_one]
  rw [this]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem mul_comm_of_isCyclic [IsCyclic G] (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
  exact zpow_mul_comm g i j

end GroupTheory

def SecondInequalityRoots.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] (p : ℕ), p.Prime → HasEnoughRootsOfUnity K p →
    Module.finrank K L = p → ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ p

section Norms

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem pow_finrank_mem_range_ideleClassNorm (c : IdeleClassGroup K) :
    c ^ finrank K L ∈ (ideleClassNorm K L).range :=
  ⟨ideleClassMap K L c, ideleClassNorm_ideleClassMap c⟩

end Norms

end Sec2_16_SecondInequality_Statement

/-! ### 17_SecondInequality.PrimeDegree -/
section Sec2_17_SecondInequality_PrimeDegree

open NumberField Module Polynomial IntermediateField

universe u

section PrimeDegree

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem SecondInequalityRoots.index_le_of_prime (hR : SecondInequalityRoots.{u}) [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hL : finrank K L = p) :
    (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let E := CyclotomicField p L
  let ζ : E := IsCyclotomicExtension.zeta p L E
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p L E
  let K' : IntermediateField K E := K⟮ζ⟯

  have hroot : aeval ζ (cyclotomic p K) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hp.pos
  have hd_lt : finrank K K' < p := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral ζ)]
    have h1 := minpoly.degree_le_of_ne_zero K ζ (cyclotomic_ne_zero p K) hroot
    have h2 : (minpoly K ζ).natDegree ≤ (cyclotomic p K).natDegree := natDegree_le_natDegree h1
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    have := hp.two_le
    omega
  have hd_pos : 0 < finrank K K' := finrank_pos
  have hcop : (finrank K K').Coprime p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hd_pos hd_lt)).symm

  let ζ' : K' := ⟨ζ, mem_adjoin_simple_self K ζ⟩
  have hζ' : IsPrimitiveRoot ζ' p :=
    (IsPrimitiveRoot.map_iff_of_injective (f := algebraMap K' E) (algebraMap K' E).injective).1 hζ
  have hroots : HasEnoughRootsOfUnity K' p := ⟨⟨ζ', hζ'⟩, rootsOfUnity.isCyclic K' p⟩

  obtain ⟨f, hfsep, hf⟩ := IsGalois.is_separable_splitting_field (F := K) (E := L)
  have := hf
  have : IsSplittingField L E ((cyclotomic p K).map (algebraMap K L)) := by
    rw [map_cyclotomic]
    exact IsCyclotomicExtension.splitting_field_cyclotomic p L E
  have : IsSplittingField K E (f * cyclotomic p K) :=
    IsSplittingField.mul (F := K) (K := L) (L := E) f (cyclotomic p K) hfsep.ne_zero (cyclotomic_ne_zero p K)
  have : IsGalois K E :=
    { to_isSeparable := inferInstance, to_normal := Normal.of_isSplittingField (f * cyclotomic p K) }
  have : IsGalois K' E := IsGalois.tower_top_of_isGalois K K' E

  let L' : IntermediateField K E := (IsScalarTower.toAlgHom K L E).fieldRange
  have hsup : K' ⊔ L' = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : x ∈ Algebra.adjoin L ({ζ} : Set E) := by
      rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.1 hy]
      exact le_sup_left (a := K') (mem_adjoin_simple_self K ζ)
    | algebraMap l => exact le_sup_right (b := L') ⟨l, rfl⟩
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hL' : finrank K L' = p := by
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L E)).toLinearEquiv.finrank_eq.symm.trans hL

  have htow1 : finrank K K' * finrank K' E = finrank K E := finrank_mul_finrank K K' E
  have htow2 : finrank K L * finrank L E = finrank K E := finrank_mul_finrank K L E
  have hle : finrank K E ≤ finrank K K' * p := by
    have := finrank_sup_le K' L'
    rwa [hsup, finrank_top', hL'] at this
  have hdeg : finrank K' E = p := by
    have h1 : finrank K' E ≤ p := by
      rw [← htow1] at hle
      exact Nat.le_of_mul_le_mul_left hle hd_pos
    have h2 : p ∣ finrank K K' * finrank K' E := by
      rw [htow1, ← htow2, hL]
      exact dvd_mul_right p _
    have h3 : p ∣ finrank K' E := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h2)
    exact le_antisymm h1 (Nat.le_of_dvd finrank_pos h3)
  have : IsCyclic (E ≃ₐ[K'] E) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, hdeg])

  have hE := (enatCard_quotient_le_iff _ p).1 (hR K' E p hp hroots hdeg)

  have hcomap : (ideleClassNorm K' E).range.comap (ideleClassMap K K') ≤
      (ideleClassNorm K L).range := by
    intro c hc
    obtain ⟨y, hy⟩ := hc
    refine mem_of_pow_mem_of_coprime hcop ?_ (hL ▸ pow_finrank_mem_range_ideleClassNorm c)
    refine ⟨ideleClassNorm L E y, ?_⟩
    rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := K'), hy,
      ideleClassNorm_ideleClassMap]
  have := index_le_of_comap_le (ideleClassMap K K') hcomap hE.1
  exact ⟨this.1, this.2.trans hE.2⟩

end PrimeDegree

end Sec2_17_SecondInequality_PrimeDegree

/-! ### 18_SecondInequality.Reduction -/
section Sec2_18_SecondInequality_Reduction

open NumberField Module IntermediateField

universe u

def SecondInequality.{v} : Prop :=
  ∀ (K L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)],
    ENat.card (IdeleClassGroup K ⧸ (ideleClassNorm K L).range) ≤ Module.finrank K L

theorem SecondInequalityRoots.index_le_of_finrank_eq (hR : SecondInequalityRoots.{u}) (n : ℕ) :
    ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)], finrank K L = n →
      (ideleClassNorm K L).range.index ≠ 0 ∧ (ideleClassNorm K L).range.index ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ _ hn
  have hn0 : 0 < n := hn ▸ finrank_pos
  by_cases h1 : n = 1
  ·
    have htop : (ideleClassNorm K L).range = ⊤ := by
      rw [eq_top_iff]
      intro c _
      have := pow_finrank_mem_range_ideleClassNorm (L := L) c
      rwa [hn, h1, pow_one] at this
    rw [htop, Subgroup.index_top]
    omega
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (L ≃ₐ[K] L) = n := by rw [IsGalois.card_aut_eq_finrank, hn]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hcard ▸ hqn)

  let H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers g
  have : H.Normal := ⟨fun a ha b ↦ by rwa [mul_comm_of_isCyclic b a, mul_inv_cancel_right]⟩
  let M : IntermediateField K L := fixedField H
  have hML : finrank M L = q := by
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, hg]
  have hKM : finrank K M * q = n := by rw [← hML, finrank_mul_finrank, hn]
  have hm_lt : finrank K M < n := by
    have : 0 < finrank K M := finrank_pos
    calc finrank K M < finrank K M * 2 := by omega
      _ ≤ finrank K M * q := Nat.mul_le_mul_left _ hq.two_le
      _ = n := hKM

  have : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
  have : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (p := q) (by rw [IsGalois.card_aut_eq_finrank, hML])
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup H
  have : IsCyclic (M ≃ₐ[K] M) :=
    isCyclic_of_surjective _ (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L))
  have hM := ih (finrank K M) hm_lt K M rfl
  have hL := hR.index_le_of_prime (K := M) (L := L) hq hML

  have hcomp : (ideleClassNorm K M).comp (ideleClassNorm M L) = ideleClassNorm K L :=
    MonoidHom.ext fun c ↦ ideleClassNorm_ideleClassNorm c
  have hrange : (ideleClassNorm K L).range =
      (ideleClassNorm M L).range.map (ideleClassNorm K M) := by
    rw [MonoidHom.map_range, hcomp]
  have := index_map_le (ideleClassNorm K M) hL.1 hM.1
  rw [hrange]
  refine ⟨this.1, this.2.trans ?_⟩
  rw [← hKM]
  exact Nat.mul_le_mul hM.2 hL.2

theorem SecondInequalityRoots.secondInequality (hR : SecondInequalityRoots.{u}) :
    SecondInequality.{u} := by
  intro K L _ _ _ _ _ _ _
  exact (enatCard_quotient_le_iff _ _).2 (hR.index_le_of_finrank_eq _ K L rfl)

end Sec2_18_SecondInequality_Reduction

/-! ### 19_SecondInequality.PowFinrankMemRangeInfiniteLocalNorm -/
section Sec2_19_SecondInequality_PowFinrankMemRangeInfiniteLocalNorm

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Module IntermediateField
open RHDirect.CFT_ProfiniteSemilocal.ProfCoh IdeleGroup IdeleNorm SemiLocal
open scoped TensorProduct NumberField.LiesOver

section Splitting

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem algHom_mem_fieldRange_of_pow_eq {L F E : Type*} [Field L] [Field F] [Field E]
    [Algebra K L] [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    {a : K} {α : L} (hα : α ^ n = algebraMap K L a) (hgen : K⟮α⟯ = ⊤) (ι : L →ₐ[K] E)
    {x : F} (hx : x ^ n = algebraMap K F a) (m : L) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have hαr : ι α ∈ (algebraMap F E).fieldRange := by
    by_cases hx0 : x = 0
    · have ha : a = 0 := by
        rw [hx0, zero_pow (NeZero.ne n)] at hx
        exact (algebraMap K F).injective (by rw [← hx, map_zero])
      rw [ha, map_zero, pow_eq_zero_iff (NeZero.ne n)] at hα
      rw [hα, map_zero]
      exact zero_mem _
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0' : algebraMap F E x ≠ 0 := (map_ne_zero _).2 hx0
    have hpow : ι α ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, hα, ι.commutes, ← map_pow, hx, ← IsScalarTower.algebraMap_apply]
    have hroot : (ι α / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0')]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0']
  let J : IntermediateField K E := Subfield.toIntermediateField (algebraMap F E).fieldRange
    fun c ↦ ⟨algebraMap K F c, (IsScalarTower.algebraMap_apply K F E c).symm⟩
  have hle : K⟮α⟯ ≤ J.comap ι := adjoin_simple_le_iff.2 hαr
  rw [hgen] at hle
  exact hle (Set.mem_univ m)

variable [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem splitsCompletely_of_pow_eq {a : K} {α : L} (hα : α ^ n = algebraMap K L a)
    (hgen : K⟮α⟯ = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (h : ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) a) :
    SplitsCompletely L v := by
  obtain ⟨x, hx⟩ := h
  rw [splitsCompletely_iff_forall_finrank]
  intro w
  let g := (Pi.evalAlgHom (v.adicCompletion K) _ w).comp (tensorEquiv L v).toAlgHom
  exact finrank_eq_one_of_tensor_surjective g
    ((Function.surjective_eval w).comp (tensorEquiv L v).surjective)
    fun m ↦ algHom_mem_fieldRange_of_pow_eq hα hgen
      ((g.restrictScalars K).comp Algebra.TensorProduct.includeRight) hx m

end Splitting

section LocalNorms

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]

theorem pow_finrank_mem_range_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K)ˣ) : y ^ finrank K L ∈ (finiteLocalNorm L v).range := by
  refine ⟨fun w ↦ Units.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) :
    v.adicCompletion K →* w.1.adicCompletion L) y, ?_⟩
  apply Units.ext
  rw [coe_finiteLocalNorm, Units.val_pow_eq_pow_val, ← sum_finrank_eq L v,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.coe_map]
  exact Algebra.norm_algebraMap (S := w.1.adicCompletion L) (y : v.adicCompletion K)

theorem pow_finrank_mem_range_infiniteLocalNorm (v : InfinitePlace K) (y : (v.Completion)ˣ) :
    y ^ finrank K L ∈ (infiniteLocalNorm L v).range := by
  classical
  refine ⟨fun w ↦ Units.map (algebraMap v.Completion (w : InfinitePlace L).Completion :
    v.Completion →* (w : InfinitePlace L).Completion) y, ?_⟩
  apply Units.ext
  rw [coe_infiniteLocalNorm, Units.val_pow_eq_pow_val,
    ← RHDirect.CFT_ProfiniteSemilocal.InfinitePlace.sum_finrank_completion (L := L) v, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.coe_map]
  exact Algebra.norm_algebraMap (S := (w : InfinitePlace L).Completion) (y : v.Completion)

end LocalNorms

section Main

universe u

theorem not_mem_bot_of_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L] {α : L}
    (hgen : K⟮α⟯ = ⊤) (h1 : finrank K L ≠ 1) : α ∉ (⊥ : IntermediateField K L) := by
  intro hα
  have hbot : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← hgen]
    exact adjoin_simple_eq_bot_iff.2 hα
  have := IntermediateField.finrank_eq_one_iff.2 hbot
  rw [IntermediateField.finrank_top'] at this
  exact h1 this

theorem FirstInequality.secondInequalityRoots (hFI : FirstInequality.{u}) :
    SecondInequalityRoots.{u} := by
  intro K L _ _ _ _ _ _ _ p hp hroots hdeg
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  have hK : (primitiveRoots (finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots finrank_pos).2 (hdeg ▸ hζ)⟩
  obtain ⟨α, ⟨a₀, ha₀⟩, hgen⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  rw [hdeg] at ha₀
  have h1 : finrank K L ≠ 1 := by rw [hdeg]; exact hp.ne_one
  have hαK := not_mem_bot_of_adjoin_eq_top hgen h1
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, pow_eq_zero_iff hp.ne_zero] at ha₀
    exact hαK (ha₀ ▸ zero_mem _)
  set a : Kˣ := Units.mk0 a₀ ha₀0 with ha_def
  have hα : α ^ p = algebraMap K L (a : K) := by rw [Units.val_mk0, ha₀]

  have hap : a ∉ unitsPow K p := by
    intro h
    obtain ⟨b, hb⟩ := mem_unitsPow.1 h
    have hb0 : algebraMap K L (b : K) ≠ 0 := (map_ne_zero _).2 b.ne_zero
    have hroot : (α / algebraMap K L (b : K)) ^ p = 1 := by
      rw [div_pow, hα, ← map_pow, ← Units.val_pow_eq_pow_val, hb,
        div_self ((map_ne_zero _).2 a.ne_zero)]
    have hζ' : IsPrimitiveRoot (algebraMap K L ζ) p :=
      hζ.map_of_injective (algebraMap K L).injective
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine hαK ⟨ζ ^ k * b, ?_⟩
    show algebraMap K L (ζ ^ k * (b : K)) = α
    rw [map_mul, map_pow, hk, div_mul_cancel₀ _ hb0]

  obtain ⟨S₀, hS₀⟩ := exists_finset_sup_sIdeles_eq_top (K := K)
  have hfp : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(p : 𝓞 K)}) ?_).subset fun v hv ↦ ?_
    · rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.ne_zero
    · exact Ideal.dvd_span_singleton.2 hv
  have hfa : {v : HeightOneSpectrum (𝓞 K) | ord v (diagonal K a) ≠ 0}.Finite :=
    eventually_ord_eq_zero (diagonal K a)
  set S : Finset (HeightOneSpectrum (𝓞 K)) := S₀ ∪ hfp.toFinset ∪ hfa.toFinset with hS
  have hpS : ∀ v, (p : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv ↦ by
    simp [S, hv]
  have hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ :=
    sup_sIdeles_eq_top_of_subset (fun v hv ↦ by simp [S, Finset.mem_coe.1 hv]) hS₀
  have haS : a ∈ (S : Set (HeightOneSpectrum (𝓞 K))).unit K := by
    refine (diagonal_mem_sIdeles_iff _ a).1 fun v hv ↦ ?_
    by_contra h
    exact hv (by simp [S, h])

  obtain ⟨T, hST, -, haT, hidx⟩ := hFI.exists_places_index_map_powerSubgroup S hpS hJ haS hap

  have hnorm : powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 K))) ≤
      (ideleNorm K L).range := by
    intro x hx
    have hxST := powerSubgroup_le_sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))
      (T : Set (HeightOneSpectrum (𝓞 K))) p hx
    obtain ⟨hxS, hxinf, -⟩ := (mem_localSubgroup _ _ _ _).1 hx
    refine mem_range_ideleNorm_of_forall x (fun v ↦ ?_) (fun w ↦ ?_)
    · by_cases hvS : v ∈ S
      · obtain ⟨y, hy⟩ := hxS v hvS
        rw [← hy, powMonoidHom_apply, ← hdeg]
        exact pow_finrank_mem_range_finiteLocalNorm v y
      by_cases hvT : v ∈ T
      · rw [range_finiteLocalNorm_eq_top_of_isFiniteSplit v ((splitsCompletely_iff_isFiniteSplit v).1
          (splitsCompletely_of_pow_eq hα hgen v (mem_unitsPowIn.1 (haT v hvT))))]
        exact Subgroup.mem_top _
      · obtain ⟨w⟩ := nonempty_placesOver L v
        have he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1 :=
          Kummer.ramificationIdx_eq_one_of_pow_eq a hα hgen v (fun h ↦ hvS (hpS v h))
            (by rw [haS v hvS, WithZero.log_one]; exact dvd_zero _) w.1.asIdeal
        have hu : finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
          have h := (mem_sIdeles_iff _).1 hxST v (by simp [hvS, hvT])
          rw [Submonoid.mem_units_iff, ← map_inv, coe_finiteProj, coe_finiteProj]
          exact ⟨h.1, h.2⟩
        rw [← map_integerUnitsOver_eq_of_ramificationIdx_eq_one v w he] at hu
        obtain ⟨z, -, hz⟩ := hu
        exact ⟨z, hz⟩
    · obtain ⟨y, hy⟩ := hxinf w
      rw [← hy, powMonoidHom_apply, ← hdeg]
      exact pow_finrank_mem_range_infiniteLocalNorm w y

  have hle : (powerSubgroup p (S : Set (HeightOneSpectrum (𝓞 K)))
      (T : Set (HeightOneSpectrum (𝓞 K)))).map (IdeleClassGroup.mk K) ≤
        (ideleClassNorm K L).range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hnorm hx
    exact ⟨IdeleClassGroup.mk L y, by rw [ideleClassNorm_mk, hy]⟩
  have hdvd := Subgroup.index_dvd_of_le hle
  rw [hidx] at hdvd
  refine (enatCard_quotient_le_iff _ p).2 ⟨fun h ↦ ?_, Nat.le_of_dvd hp.pos hdvd⟩
  rw [h] at hdvd
  exact hp.ne_zero (Nat.eq_zero_of_zero_dvd hdvd)

end Main

end Sec2_19_SecondInequality_PowFinrankMemRangeInfiniteLocalNorm

/-! ### 20_SecondInequality.Cyclic -/
section Sec2_20_SecondInequality_Cyclic

open NumberField RHDirect.Stage13CFT_IdeleNormResidue Module

universe u

theorem secondInequality : SecondInequality.{u} :=
  (firstInequality.{u}.secondInequalityRoots).secondInequality

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem index_range_ideleClassNorm_eq_finrank [IsCyclic Gal(L/K)] :
    (ideleClassNorm K L).range.index = finrank K L := by
  obtain ⟨hge, hne⟩ := finrank_le_index_range_ideleClassNorm (K := K) (L := L)
  have hle := ((enatCard_quotient_le_iff _ _).1 (secondInequality.{u} K L)).2
  exact le_antisymm hle hge

theorem natCard_cycTateNegOne_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = 1 := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  obtain ⟨h, hpos⟩ := index_range_ideleClassNorm σ hσ
  rw [index_range_ideleClassNorm_eq_finrank] at h
  have hn : 0 < finrank K L := finrank_pos
  have h' : finrank K L * 1 = finrank K L * _ := (mul_one _).trans h
  exact (Nat.eq_of_mul_eq_mul_left hn h').symm

theorem natCard_cycTateZero_ideleClassGroup_eq_finrank (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
      = finrank K L := by
  have : IsCyclic Gal(L/K) := ⟨⟨σ, fun g ↦ Subgroup.mem_zpowers_iff.1 (hσ g)⟩⟩
  rw [natCard_cycTateZero_ideleClassGroup σ hσ, index_range_ideleClassNorm_eq_finrank]

theorem classFieldAxiom_ideleClassGroup (σ : Gal(L/K)) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (CycTateZero (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = finrank K L ∧
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)) σ)
        = 1 :=
  ⟨natCard_cycTateZero_ideleClassGroup_eq_finrank σ hσ, natCard_cycTateNegOne_ideleClassGroup σ hσ⟩

end

end Sec2_20_SecondInequality_Cyclic

end RHDirect.CFT.Global
