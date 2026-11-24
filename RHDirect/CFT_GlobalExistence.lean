import RHDirect.CFT_GlobalReciprocity
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Data.Sign.Defs
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# RHDirect.CFT_GlobalExistence

Global Class Field Theory Pillar — Global Existence Theorem & Continuous Global Artin Map:
1. Local & finite-adelic congruence filtrations (`unitsLevel`, `finiteLevel`, `idealLevel`,
   `Modulus`, `congruenceSubgroup`, `idelesOneMod`, `rayUnits`) and open-subgroup containment
   (`Modulus.exists_congruenceSubgroup_le`, `IdeleClassGroup.exists_map_congruenceSubgroup_le`).
2. Kummer norm groups for `S`-units (`KummerNorm`) and existence of abelian extensions for
   open finite-exponent subgroups when base field has enough roots of unity (`Kummer`).
3. Norm Limitation Theorem (`NormLimitation`): `(ideleClassNorm K (maxAbelian K M)).range =
   (ideleClassNorm K M).range` and index `= |Gal(M/K)^ab|`.
4. **Global Existence Theorem** (`ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini`):
   order-reversing bijection `normGroupOrderIso : FiniteAbelianSubfield K Ω ≃o (OpenFiniteIndexSubgroup K)ᵒᵈ`
   between finite abelian extensions `L / K` inside `Ω` and open finite-index subgroups of `IdeleClassGroup K`.
5. **Continuous Global Artin Map** (`GlobalArtinMap.ArtinMap` & `GlobalArtinMap.Kernel`):
   `artinMap : IdeleClassGroup K →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)`,
   its continuity, surjectivity, kernel `ker(artinMap) = connectedComponentOfOne (IdeleClassGroup K)`,
   and topological isomorphism `artinQuotientEquiv`.
-/

noncomputable section

namespace RHDirect.CFT.Global

open RHDirect.Stage13CFT_IdeleNormResidue
open RHDirect.CFT_ProfiniteSemilocal

/-! ### 01_CongruenceAndModulus -/
section Sec5_01_CongruenceAndModulus

open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

section LocalUnitsLevel

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def unitsLevel (n : ℕ) : Subgroup (v.adicCompletion K)ˣ where
  carrier := {x | Valued.v (x : v.adicCompletion K) = 1 ∧
    Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ))}
  one_mem' := by simp
  mul_mem' {x y} hx hy := by
    refine ⟨by simp [hx.1, hy.1], ?_⟩
    have : ((x * y : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K) * ((y : v.adicCompletion K) - 1) +
          ((x : v.adicCompletion K) - 1) := by
      push_cast; ring
    rw [this]
    refine Valuation.map_add_le _ ?_ hx.2
    rw [map_mul, hx.1, one_mul]
    exact hy.2
  inv_mem' {x} hx := by
    have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
    refine ⟨by simp [hx.1], ?_⟩
    have : ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) - 1 =
        (x : v.adicCompletion K)⁻¹ * (1 - (x : v.adicCompletion K)) := by
      rw [Units.val_inv_eq_inv_val, mul_sub, mul_one, inv_mul_cancel₀ hx0]
    rw [this, map_mul, map_inv₀, hx.1, inv_one, one_mul, Valuation.map_sub_swap]
    exact hx.2

variable {v} in
theorem mem_unitsLevel {n : ℕ} {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v (x : v.adicCompletion K) = 1 ∧
      Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) :=
  Iff.rfl

variable {v} in
theorem mem_unitsLevel_of_one_le {n : ℕ} (hn : 1 ≤ n) {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) := by
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  have hlt : Valued.v ((x : v.adicCompletion K) - 1) < Valued.v (1 : v.adicCompletion K) := by
    rw [map_one]
    refine h.trans_lt ?_
    rw [← exp_zero, exp_lt_exp]
    omega
  simpa using Valuation.map_eq_of_sub_lt _ hlt

theorem unitsLevel_zero :
    unitsLevel (K := K) v 0 = (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  ext x
  rw [Submonoid.mem_units_iff, mem_unitsLevel]
  change _ ↔ (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
    ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · rintro ⟨h1, -⟩
    simp [h1]
  · rintro ⟨h1, h2⟩
    have hx0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simp
    have h3 : 1 ≤ Valued.v (x : v.adicCompletion K) :=
      (inv_le_one₀ (zero_lt_iff.2 hx0)).1 h2
    refine ⟨le_antisymm h1 h3, ?_⟩
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact Valuation.map_sub_le _ h1 (by simp)

theorem unitsLevel_antitone : Antitone (unitsLevel (K := K) v) := by
  intro m n hmn x hx
  refine ⟨hx.1, hx.2.trans ?_⟩
  rw [exp_le_exp]
  omega

theorem isOpen_unitsLevel (n : ℕ) : IsOpen (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) := by
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  obtain ⟨a, ha⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective (K := K) (v := v)
    (exp (-(n : ℤ)))
  have ha0 : Valued.v a ≠ 0 := by simp [ha]
  have h1 : {y : v.adicCompletion K | Valued.v y = 1} ∈ 𝓝 (1 : v.adicCompletion K) := by
    simpa using Valued.locally_const (x := (1 : v.adicCompletion K)) (by simp)
  have h2 : {y : v.adicCompletion K | Valued.v (y - 1) ≤ exp (-(n : ℤ))} ∈
      𝓝 (1 : v.adicCompletion K) := by
    have hc : Continuous fun y : v.adicCompletion K ↦ y - 1 + a :=
      (continuous_id.sub continuous_const).add continuous_const
    have h := hc.continuousAt.preimage_mem_nhds (x := (1 : v.adicCompletion K))
      (by simpa using Valued.locally_const (x := a) ha0)
    refine Filter.mem_of_superset h fun y hy ↦ ?_
    have hy' : Valued.v (y - 1 + a) = exp (-(n : ℤ)) := by rw [← ha]; exact hy
    have : y - 1 = (y - 1 + a) - a := by ring
    change Valued.v (y - 1) ≤ exp (-(n : ℤ))
    rw [this]
    exact Valuation.map_sub_le _ hy'.le ha.le
  have h3 := Units.continuous_val.continuousAt.preimage_mem_nhds (x := (1 : (v.adicCompletion K)ˣ))
    (by rw [Units.val_one]; exact Filter.inter_mem h1 h2)
  exact Filter.mem_of_superset h3 fun x hx ↦ hx

theorem exists_unitsLevel_subset {t : Set (v.adicCompletion K)ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) ⊆ t := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Units.val_one, mem_comap] at ht
  obtain ⟨t', ht', hsub⟩ := ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 ht'
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := fun h ↦ γ.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
  refine ⟨(-(log c)).toNat + 1, by omega, fun x hx ↦ hsub (hγ ?_)⟩
  change Valued.v.restrict ((x : v.adicCompletion K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc]
  refine hx.2.trans_lt (lt_of_lt_of_eq ?_ (exp_log hc0))
  rw [exp_lt_exp]
  omega

end LocalUnitsLevel

section Ideals

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

omit [IsDedekindDomain R] in
theorem asIdeal_pow_eq_one_iff (v : HeightOneSpectrum R) {k : ℕ} : v.asIdeal ^ k = 1 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hk
    have hle : v.asIdeal ^ k ≤ v.asIdeal := Ideal.pow_le_self hk
    rw [h, Ideal.one_eq_top, top_le_iff] at hle
    exact v.isPrime.ne_top hle
  · rintro rfl
    exact pow_zero _

omit [IsDedekindDomain R] in
theorem mulSupport_asIdeal_pow (a : HeightOneSpectrum R → ℕ) :
    mulSupport (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v) = support a := by
  ext v
  simp only [mem_mulSupport, mem_support, ne_eq, asIdeal_pow_eq_one_iff]

theorem finprod_asIdeal_pow_ne_bot (a : HeightOneSpectrum R → ℕ) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ≠ ⊥ :=
  finprod_induction (fun I : Ideal R ↦ I ≠ ⊥) one_ne_zero (fun _ _ hx hy ↦ mul_ne_zero hx hy)
    fun v ↦ pow_ne_zero _ v.ne_bot

theorem finprod_asIdeal_pow_dvd_iff {a : HeightOneSpectrum R → ℕ} (ha : (support a).Finite)
    {I : Ideal R} (hI : I ≠ ⊥) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ∣ I ↔
      ∀ v : HeightOneSpectrum R, a v ≤ multiplicity v.asIdeal I := by
  have hfa : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v := by
    rw [HasFiniteMulSupport, mulSupport_asIdeal_pow]
    exact ha
  constructor
  · intro h v
    have h1 : v.asIdeal ^ a v ∣ I := (finprod_mem_dvd v hfa).trans h
    have h2 := HeightOneSpectrum.multiplicity_le_of_ideal_ge v (Ideal.le_of_dvd h1) hI
    rwa [multiplicity_pow_self_of_prime (HeightOneSpectrum.prime v)] at h2
  · intro h
    have hm : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ multiplicity v.asIdeal I := by
      simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI] using
        Ideal.hasFiniteMulSupport hI
    have hmb : HasFiniteMulSupport fun v : HeightOneSpectrum R ↦
        v.asIdeal ^ (multiplicity v.asIdeal I - a v) := by
      rw [HasFiniteMulSupport, mulSupport_asIdeal_pow] at hm ⊢
      refine hm.subset fun v hv ↦ ?_
      simp only [mem_support, ne_eq] at hv ⊢
      omega
    have hsplit : (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ multiplicity v.asIdeal I) =
        fun v ↦ v.asIdeal ^ a v * v.asIdeal ^ (multiplicity v.asIdeal I - a v) :=
      funext fun v ↦ by rw [← pow_add, Nat.add_sub_cancel' (h v)]
    conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
    rw [hsplit, finprod_mul_distrib hfa hmb]
    exact dvd_mul_right _ _

end Ideals

section Completions

variable {K : Type*} [Field K] [NumberField K]

open NumberField.InfinitePlace.Completion

def realUnitsHom {w : InfinitePlace K} (hw : w.IsReal) : ℝˣ →ₜ* (w.Completion)ˣ where
  toMonoidHom := Units.map ((ringEquivRealOfIsReal hw).symm : ℝ →+* w.Completion).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivRealOfIsReal hw).symm.continuous

def complexUnitsHom {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →ₜ* (w.Completion)ˣ where
  toMonoidHom := Units.map ((ringEquivComplexOfIsComplex hw).symm : ℂ →+* w.Completion).toMonoidHom
  continuous_toFun := Units.continuous_map (isometryEquivComplexOfIsComplex hw).symm.continuous

omit [NumberField K] in
theorem realUnitsHom_surjective {w : InfinitePlace K} (hw : w.IsReal) (a : (w.Completion)ˣ) :
    realUnitsHom hw (Units.map (ringEquivRealOfIsReal hw : w.Completion →+* ℝ).toMonoidHom a) = a :=
  Units.ext ((ringEquivRealOfIsReal hw).symm_apply_apply _)

omit [NumberField K] in
theorem complexUnitsHom_surjective {w : InfinitePlace K} (hw : w.IsComplex) (a : (w.Completion)ˣ) :
    complexUnitsHom hw
      (Units.map (ringEquivComplexOfIsComplex hw : w.Completion →+* ℂ).toMonoidHom a) = a :=
  Units.ext ((ringEquivComplexOfIsComplex hw).symm_apply_apply _)

end Completions

namespace IdeleGroup

open RHDirect.Stage13CFT_IdeleNormResidue.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (_root_.RestrictedProduct.evalMonoidHom
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)

@[simp]
theorem coe_finiteComponent (v : HeightOneSpectrum (𝓞 K)) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((finiteComponent v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

theorem continuous_finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteComponent (K := K) v) :=
  Units.continuous_map (_root_.RestrictedProduct.continuous_eval v)

theorem finiteComponent_toFinite (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    finiteComponent v (toFinite K x) = finiteProj v x :=
  Units.ext rfl

def finiteLevel (n : HeightOneSpectrum (𝓞 K) → ℕ) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ⨅ v, (unitsLevel v (n v)).comap (finiteComponent v)

theorem mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteLevel n ↔ ∀ v, finiteComponent v x ∈ unitsLevel v (n v) := by
  simp only [finiteLevel, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem finiteLevel_antitone {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := fun _ hx ↦
  mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)

theorem finiteLevel_le_finiteLevel_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ finiteLevel 0 :=
  finiteLevel_antitone fun v ↦ Nat.zero_le (n v)

theorem finiteUnitsEquiv_apply_eq (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteUnitsEquiv K x v = finiteComponent v x :=
  Units.ext rfl

theorem isOpen_finiteLevel_zero :
    IsOpen (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have h := (_root_.RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ))
    (fun v ↦ IdeleGroup.isOpen_units_adicCompletionIntegers K v)).preimage (finiteUnitsEquiv K).continuous
  convert h using 1
  ext x
  simp only [SetLike.mem_coe, mem_finiteLevel, Pi.zero_apply, unitsLevel_zero, Set.mem_preimage,
    Set.mem_ofPred_eq]
  exact forall_congr' fun v ↦ by rw [← finiteUnitsEquiv_apply_eq]; rfl

theorem isOpen_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : (support n).Finite) :
    IsOpen (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have : (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) =
      (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩
      ⋂ v ∈ hn.toFinset, finiteComponent v ⁻¹'
        (unitsLevel (K := K) v (n v) : Set (v.adicCompletion K)ˣ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨fun hx ↦ ⟨finiteLevel_le_finiteLevel_zero n hx, fun v _ ↦ mem_finiteLevel.1 hx v⟩,
      fun ⟨h0, h⟩ ↦ mem_finiteLevel.2 fun v ↦ ?_⟩
    by_cases hv : n v = 0
    · rw [hv]
      exact mem_finiteLevel.1 h0 v
    · exact h v (by simpa using hv)
  rw [this]
  exact isOpen_finiteLevel_zero.inter (isOpen_biInter_finset fun v _ ↦
    (isOpen_unitsLevel v (n v)).preimage (continuous_finiteComponent v))

theorem exists_finiteLevel_subset {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧
        (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ⊆ W := by
  classical
  let e := finiteUnitsEquiv K
  let es := ContinuousMulEquiv.symm e
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ := by simp
  have hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])
  have hW2 := (_root_.RestrictedProduct.continuous_inclusion
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1
  rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hW2
  obtain ⟨t, ht, htW⟩ := hW2
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, u, hu, hIu⟩ := ht
  choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)
  refine ⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v],
    fun v hv ↦ by simp [hv], ?_⟩
  intro x hx
  rw [SetLike.mem_coe, mem_finiteLevel] at hx
  have hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun v ↦ by
    rw [finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]
    exact unitsLevel_antitone v (Nat.zero_le _) (hx v)
  let z : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩
  have hz := htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from
    hIu fun v hv ↦ by
      have := hx v
      simp only [Finset.mem_coe.1 hv, if_true] at this
      exact hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))
  have hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x := rfl
  rw [Set.mem_preimage, Set.mem_preimage, hzx] at hz
  rwa [show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x] at hz

def idealLevel (𝔪 : Ideal (𝓞 K)) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  finiteLevel fun v ↦ multiplicity v.asIdeal 𝔪

def ofFinite : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _)

theorem continuous_ofFinite : Continuous (ofFinite (K := K)) := by
  have : Continuous fun x : (FiniteAdeleRing (𝓞 K) K)ˣ ↦
      ContinuousMulEquiv.symm (prodEquiv K) ((1 : (InfiniteAdeleRing K)ˣ), x) :=
    (ContinuousMulEquiv.symm (prodEquiv K)).continuous.comp (continuous_const.prodMk continuous_id)
  exact this

@[simp]
theorem toFinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toFinite K (ofFinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).2 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem toInfinite_ofFinite (x : (FiniteAdeleRing (𝓞 K) K)ˣ) : toInfinite K (ofFinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (1, x))).1 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem mem_standardOpenSubgroup_iff_toFinite_mem (x : IdeleGroup K) :
    x ∈ standardOpenSubgroup K ↔ toFinite K x ∈ finiteLevel 0 := by
  rw [mem_standardOpenSubgroup, mem_finiteLevel]
  refine forall_congr' fun v ↦ ?_
  rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
  rfl

def ofInfinite : (InfiniteAdeleRing K)ˣ →* IdeleGroup K :=
  (ContinuousMulEquiv.symm (prodEquiv K)).toMulEquiv.toMonoidHom.comp (MonoidHom.inl _ _)

@[simp]
theorem toInfinite_ofInfinite (x : (InfiniteAdeleRing K)ˣ) : toInfinite K (ofInfinite x) = x := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (x, 1))).1 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

@[simp]
theorem toFinite_ofInfinite (x : (InfiniteAdeleRing K)ˣ) : toFinite K (ofInfinite x) = 1 := by
  change ((prodEquiv K) ((ContinuousMulEquiv.symm (prodEquiv K)) (x, 1))).2 = 1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem ofFinite_mul_ofInfinite (x : IdeleGroup K) :
    ofFinite (toFinite K x) * ofInfinite (toInfinite K x) = x := by
  apply (prodEquiv K).injective
  refine Prod.ext ?_ ?_
  · change toInfinite K (ofFinite (toFinite K x) * ofInfinite (toInfinite K x)) = toInfinite K x
    rw [map_mul, toInfinite_ofFinite, toInfinite_ofInfinite, one_mul]
  · change toFinite K (ofFinite (toFinite K x) * ofInfinite (toInfinite K x)) = toFinite K x
    rw [map_mul, toFinite_ofFinite, toFinite_ofInfinite, mul_one]

def infiniteComponent (w : InfinitePlace K) : (InfiniteAdeleRing K)ˣ →* (w.Completion)ˣ :=
  Units.map (Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w)

omit [NumberField K] in
@[simp]
theorem coe_infiniteComponent (w : InfinitePlace K) (x : (InfiniteAdeleRing K)ˣ) :
    ((infiniteComponent w x : (w.Completion)ˣ) : w.Completion) = (x : InfiniteAdeleRing K) w :=
  rfl

theorem ofInfinite_map_infiniteAdeleSingle (w : InfinitePlace K) (a : (w.Completion)ˣ) :
    ofInfinite (Units.map (infiniteAdeleSingle w) a) = infiniteEmbedding w a :=
  Units.ext rfl

theorem prod_map_infiniteAdeleSingle (x : (InfiniteAdeleRing K)ˣ) :
    ∏ w, Units.map (infiniteAdeleSingle w) (infiniteComponent w x) = x := by
  classical
  apply Units.ext
  rw [Units.coe_prod]
  exact Finset.univ_prod_mulSingle (fun w : InfinitePlace K ↦ (x : InfiniteAdeleRing K) w)

theorem ofInfinite_eq_prod (x : (InfiniteAdeleRing K)ˣ) :
    ofInfinite x = ∏ w, infiniteEmbedding w (infiniteComponent w x) := by
  conv_lhs => rw [← prod_map_infiniteAdeleSingle x]
  rw [map_prod]
  simp only [ofInfinite_map_infiniteAdeleSingle]

variable (K) in
def infinitePositive : Subgroup (InfiniteAdeleRing K)ˣ where
  carrier := {x | ∀ (w : InfinitePlace K) (hw : w.IsReal),
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : InfiniteAdeleRing K) w)}
  one_mem' w hw := by
    show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (1 : w.Completion)
    rw [map_one]
    exact one_pos
  mul_mem' {a b} ha hb w hw := by
    show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      ((a : InfiniteAdeleRing K) w * (b : InfiniteAdeleRing K) w)
    rw [map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    have h0 : ((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w *
        (a : InfiniteAdeleRing K) w = 1 :=
      congrFun a.inv_mul w
    have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((a⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w) *
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((a : InfiniteAdeleRing K) w) = 1 := by
      rw [← map_mul, h0, map_one]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_pos.2 (ha w hw)

omit [NumberField K] in
theorem mem_infinitePositive {x : (InfiniteAdeleRing K)ˣ} :
    x ∈ infinitePositive K ↔ ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((x : InfiniteAdeleRing K) w) :=
  Iff.rfl

variable (K) in
def infiniteSign : (InfiniteAdeleRing K)ˣ →* ({w : InfinitePlace K // w.IsReal} → SignTypeˣ) :=
  MonoidHom.pi fun w ↦ (Units.map (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    ((Units.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 :
      w.1.Completion →+* ℝ).toMonoidHom).comp (infiniteComponent w.1))

omit [NumberField K] in
theorem infiniteSign_apply_val (x : (InfiniteAdeleRing K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    ((infiniteSign K x w : SignTypeˣ) : SignType) =
      SignType.sign (InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((x : InfiniteAdeleRing K) w.1)) :=
  rfl

omit [NumberField K] in
theorem infinitePositive_eq_ker : infinitePositive K = (infiniteSign K).ker := by
  ext x
  rw [mem_infinitePositive, MonoidHom.mem_ker]
  constructor
  · intro h
    funext w
    apply Units.ext
    rw [infiniteSign_apply_val, Pi.one_apply, Units.val_one, sign_eq_one_iff]
    exact h w.1 w.2
  · intro h w hw
    have h' := congrArg Units.val (congrFun h ⟨w, hw⟩)
    rwa [infiniteSign_apply_val, Pi.one_apply, Units.val_one, sign_eq_one_iff] at h'

instance : (infinitePositive K).FiniteIndex := by
  rw [infinitePositive_eq_ker]
  exact Subgroup.finiteIndex_ker _

variable (K) in
def rayGroup (𝔪 : Ideal (𝓞 K)) : Subgroup (IdeleGroup K) :=
  (diagonal K).range ⊔ (idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite

theorem map_idealLevel_le_standardOpenSubgroup (𝔪 : Ideal (𝓞 K)) :
    (idealLevel 𝔪).map ofFinite ≤ standardOpenSubgroup K := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_standardOpenSubgroup_iff_toFinite_mem, toFinite_ofFinite]
  exact finiteLevel_le_finiteLevel_zero _ hx

theorem map_infinitePositive_le_standardOpenSubgroup :
    (infinitePositive K).map ofInfinite ≤ standardOpenSubgroup K := by
  rintro _ ⟨x, -, rfl⟩
  rw [mem_standardOpenSubgroup_iff_toFinite_mem, toFinite_ofInfinite]
  exact one_mem _

theorem rayGroup_le (𝔪 : Ideal (𝓞 K)) :
    rayGroup K 𝔪 ≤ (diagonal K).range ⊔ standardOpenSubgroup K :=
  sup_le (sup_le le_sup_left ((map_idealLevel_le_standardOpenSubgroup 𝔪).trans le_sup_right))
    (map_infinitePositive_le_standardOpenSubgroup.trans le_sup_right)

theorem finite_quotient_idealLevel {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    Finite (finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0)) := by
  have hc : IsCompact (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    convert isCompact_finite_units_integral K using 1
    ext x
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, mem_finiteLevel]
    refine forall_congr' fun v ↦ ?_
    rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff]
    rfl
  have : CompactSpace (finiteLevel (K := K) 0) := isCompact_iff_compactSpace.1 hc
  have hm : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.asIdeal ^ multiplicity v.asIdeal 𝔪 := by
    simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity h𝔪] using
      Ideal.hasFiniteMulSupport h𝔪
  have hs : (support fun v : HeightOneSpectrum (𝓞 K) ↦ multiplicity v.asIdeal 𝔪).Finite := by
    rw [← mulSupport_asIdeal_pow]
    exact hm
  exact Subgroup.quotient_finite_of_isOpen _
    ((isOpen_finiteLevel hs).preimage continuous_subtype_val)

def standardOpenInfiniteHom : standardOpenSubgroup K →* (InfiniteAdeleRing K)ˣ ⧸ infinitePositive K :=
  (QuotientGroup.mk' _).comp ((toInfinite K).comp (standardOpenSubgroup K).subtype)

def standardOpenFiniteHom (𝔪 : Ideal (𝓞 K)) :
    standardOpenSubgroup K →* finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0) :=
  (QuotientGroup.mk' _).comp (((toFinite K).comp (standardOpenSubgroup K).subtype).codRestrict _
    fun u ↦ (mem_standardOpenSubgroup_iff_toFinite_mem _).1 u.2)

theorem ker_inf_ker_le (𝔪 : Ideal (𝓞 K)) :
    (standardOpenInfiniteHom (K := K)).ker ⊓ (standardOpenFiniteHom 𝔪).ker ≤
      ((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
        (standardOpenSubgroup K) := by
  intro u hu
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
  rw [MonoidHom.mem_ker, standardOpenInfiniteHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [MonoidHom.mem_ker, standardOpenFiniteHom, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
  rw [Subgroup.mem_subgroupOf, ← ofFinite_mul_ofInfinite (u : IdeleGroup K)]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, h2, rfl⟩) (Subgroup.mem_sup_right ⟨_, h1, rfl⟩)

def positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) : Subgroup (IdeleGroup K) where
  carrier := {x | ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
    ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)}
  one_mem' w _ := by simp
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul, Units.val_mul, map_mul]
    exact mul_pos (ha w hw) (hb w hw)
  inv_mem' {a} ha w hw := by
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.2 (ha w hw)

theorem mem_positiveAt {S : Set {w : InfinitePlace K // w.IsReal}} {x : IdeleGroup K} :
    x ∈ positiveAt S ↔ ∀ w ∈ S, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) :=
  Iff.rfl

theorem isOpen_positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) :
    IsOpen (positiveAt S : Set (IdeleGroup K)) := by
  have : (positiveAt S : Set (IdeleGroup K)) = ⋂ w ∈ S, (fun x : IdeleGroup K ↦
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
        ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)) ⁻¹' Set.Ioi 0 := by
    ext x
    simp [mem_positiveAt]
  rw [this]
  refine S.toFinite.isOpen_biInter fun w _ ↦ isOpen_Ioi.preimage ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    (Units.continuous_val.comp (continuous_infiniteProj w.1))

end IdeleGroup

open IdeleGroup

variable (K : Type*) [Field K] [NumberField K] in
abbrev RayClassGroup (𝔪 : Ideal (𝓞 K)) : Type _ := IdeleGroup K ⧸ IdeleGroup.rayGroup K 𝔪

theorem RayClassGroup.finite {K : Type*} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}
    (h𝔪 : 𝔪 ≠ ⊥) : Finite (RayClassGroup K 𝔪) := by
  set R := IdeleGroup.rayGroup K 𝔪
  set U := standardOpenSubgroup K
  set M := (diagonal K).range ⊔ U
  have hM : M.FiniteIndex := by
    rw [show M = (IdeleGroup.toClassGroup (K := K)).ker from IdeleGroup.ker_toClassGroup.symm]
    exact Subgroup.finiteIndex_ker _
  have : Finite ((InfiniteAdeleRing K)ˣ ⧸ infinitePositive K) :=
    Subgroup.finite_quotient_of_finiteIndex
  have : Finite (finiteLevel (K := K) 0 ⧸ (idealLevel 𝔪).subgroupOf (finiteLevel 0)) :=
    finite_quotient_idealLevel h𝔪
  have : Finite (standardOpenInfiniteHom (K := K)).range :=
    Finite.of_injective _ Subtype.val_injective
  have : Finite (standardOpenFiniteHom (K := K) 𝔪).range :=
    Finite.of_injective _ Subtype.val_injective
  have : (standardOpenInfiniteHom (K := K)).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have : (standardOpenFiniteHom (K := K) 𝔪).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  have h2 : (((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
      U).FiniteIndex := Subgroup.finiteIndex_of_le (ker_inf_ker_le 𝔪)
  have hWP : (idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite ≤ R :=
    sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have h3 : (R.subgroupOf U).FiniteIndex :=
    Subgroup.finiteIndex_of_le fun x hx ↦ Subgroup.mem_subgroupOf.2 (hWP (Subgroup.mem_subgroupOf.1 hx))
  have hUR : U ⊔ R = M :=
    le_antisymm (sup_le le_sup_right (rayGroup_le 𝔪))
      (sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) le_sup_left)
  have hRM : R.relIndex M ≠ 0 := by
    rw [← hUR, Subgroup.relIndex_sup_right]
    exact h3.index_ne_zero
  have hR : R.index ≠ 0 := by
    rw [← Subgroup.relIndex_mul_index (rayGroup_le 𝔪)]
    exact mul_ne_zero hRM hM.index_ne_zero
  exact Subgroup.index_ne_zero_iff_finite.1 hR

variable (K : Type*) [Field K] [NumberField K] in
structure Modulus where
  ideal : Ideal (𝓞 K)
  ideal_ne_bot : ideal ≠ ⊥
  real : Set {w : InfinitePlace K // w.IsReal}

namespace Modulus

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

def exponent (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  multiplicity v.asIdeal 𝔪.ideal

omit [NumberField K] in
theorem exponent_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) :
    𝔪.exponent v = 0 ↔ ¬ v.asIdeal ∣ 𝔪.ideal :=
  multiplicity_eq_zero

omit [NumberField K] in
theorem one_le_exponent_iff (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ 𝔪.exponent v ↔ v.asIdeal ∣ 𝔪.ideal := by
  rw [Nat.one_le_iff_ne_zero, Ne, exponent_eq_zero_iff, not_not]

omit [NumberField K] in
theorem asIdeal_pow_exponent_dvd (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ^ 𝔪.exponent v ∣ 𝔪.ideal :=
  pow_multiplicity_dvd _ _

theorem finite_support_exponent : (support 𝔪.exponent).Finite := by
  have hm : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      v.asIdeal ^ multiplicity v.asIdeal 𝔪.ideal := by
    simpa only [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity 𝔪.ideal_ne_bot] using
      Ideal.hasFiniteMulSupport 𝔪.ideal_ne_bot
  rw [← mulSupport_asIdeal_pow]
  exact hm

def congruenceSubgroup : Subgroup (IdeleGroup K) :=
  (idealLevel 𝔪.ideal).comap (toFinite K) ⊓ positiveAt 𝔪.real

theorem mem_congruenceSubgroup {x : IdeleGroup K} :
    x ∈ 𝔪.congruenceSubgroup ↔
      (∀ v, finiteProj v x ∈ unitsLevel v (𝔪.exponent v)) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  rw [congruenceSubgroup, Subgroup.mem_inf, Subgroup.mem_comap, idealLevel, mem_finiteLevel,
    mem_positiveAt]
  simp only [finiteComponent_toFinite]
  rfl

theorem mem_congruenceSubgroup_iff {x : IdeleGroup K} :
    x ∈ 𝔪.congruenceSubgroup ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal →
          Valued.v ((x : 𝔸[K]).2 v - 1) ≤ exp (-(𝔪.exponent v : ℤ))) ∧
        (∀ v, ¬ v.asIdeal ∣ 𝔪.ideal → Valued.v ((x : 𝔸[K]).2 v) = 1) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((x : 𝔸[K]).1 w.1) := by
  rw [mem_congruenceSubgroup]
  constructor
  · rintro ⟨hf, hi⟩
    refine ⟨fun v hv ↦ (hf v).2, fun v hv ↦ (hf v).1, hi⟩
  · rintro ⟨hd, hn, hi⟩
    refine ⟨fun v ↦ ?_, hi⟩
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · exact (mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv)).2 (hd v hv)
    · rw [(𝔪.exponent_eq_zero_iff v).2 hv, mem_unitsLevel]
      refine ⟨hn v hv, ?_⟩
      rw [Nat.cast_zero, neg_zero, exp_zero]
      exact Valuation.map_sub_le _ (hn v hv).le (by simp)

theorem isOpen_congruenceSubgroup : IsOpen (𝔪.congruenceSubgroup : Set (IdeleGroup K)) := by
  rw [congruenceSubgroup, Subgroup.coe_inf, Subgroup.coe_comap]
  refine IsOpen.inter ?_ (isOpen_positiveAt _)
  exact (isOpen_finiteLevel 𝔪.finite_support_exponent).preimage (continuous_toFinite K)

theorem congruenceSubgroup_le_standardOpenSubgroup :
    𝔪.congruenceSubgroup ≤ standardOpenSubgroup K := fun x hx ↦ by
  rw [mem_standardOpenSubgroup_iff_toFinite_mem]
  exact finiteLevel_le_finiteLevel_zero _ (Subgroup.mem_inf.1 hx).1

def idelesOneMod : Subgroup (IdeleGroup K) :=
  (⨅ (v : HeightOneSpectrum (𝓞 K)) (_ : v.asIdeal ∣ 𝔪.ideal),
    (unitsLevel v (𝔪.exponent v)).comap (finiteProj v)) ⊓ positiveAt 𝔪.real

theorem mem_idelesOneMod {x : IdeleGroup K} :
    x ∈ 𝔪.idelesOneMod ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal → finiteProj v x ∈ unitsLevel v (𝔪.exponent v)) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
          ((infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion) := by
  simp only [idelesOneMod, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_positiveAt]

theorem congruenceSubgroup_eq_inf :
    𝔪.congruenceSubgroup = 𝔪.idelesOneMod ⊓ standardOpenSubgroup K := by
  ext x
  rw [Subgroup.mem_inf, mem_congruenceSubgroup, mem_idelesOneMod,
    mem_standardOpenSubgroup_iff_toFinite_mem, mem_finiteLevel]
  simp only [finiteComponent_toFinite, Pi.zero_apply]
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨⟨fun v _ ↦ hf v, hi⟩, fun v ↦ unitsLevel_antitone v (Nat.zero_le _) (hf v)⟩
  · rintro ⟨⟨hf, hi⟩, h0⟩
    refine ⟨fun v ↦ ?_, hi⟩
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · exact hf v hv
    · rw [(𝔪.exponent_eq_zero_iff v).2 hv]
      exact h0 v

theorem congruenceSubgroup_le_idelesOneMod : 𝔪.congruenceSubgroup ≤ 𝔪.idelesOneMod := by
  rw [congruenceSubgroup_eq_inf]
  exact inf_le_left

def rayUnits : Subgroup Kˣ :=
  𝔪.idelesOneMod.comap (diagonal K)

theorem mem_rayUnits {a : Kˣ} :
    a ∈ 𝔪.rayUnits ↔
      (∀ v, v.asIdeal ∣ 𝔪.ideal → v.valuation K ((a : K) - 1) ≤ exp (-(𝔪.exponent v : ℤ))) ∧
        ∀ w ∈ 𝔪.real, 0 < InfinitePlace.embedding_of_isReal w.2 (a : K) := by
  rw [rayUnits, Subgroup.mem_comap, mem_idelesOneMod]
  refine and_congr (forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_)
    (forall_congr' fun w ↦ forall_congr' fun _ ↦ ?_)
  · have hc : ∀ k : K, (k : v.adicCompletion K) = algebraMap K (v.adicCompletion K) k := fun k ↦ by
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [mem_unitsLevel_of_one_le ((𝔪.one_le_exponent_iff v).2 hv), coe_finiteProj_diagonal,
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hc, hc,
      (algebraMap K (v.adicCompletion K)).map_sub, (algebraMap K (v.adicCompletion K)).map_one]
  · rw [coe_infiniteProj_diagonal]
    exact Iff.of_eq (congrArg (0 < ·) (InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe _ _))

end Modulus

end

end Sec5_01_CongruenceAndModulus

/-! ### 02_ClassFieldConsequences.OpenSubgroup -/
section Sec5_02_ClassFieldConsequences_OpenSubgroup

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

noncomputable section

theorem Subgroup.subset_of_isPreconnected {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {s : Set G}
    (hs : IsPreconnected s) (h1 : (1 : G) ∈ s) : s ⊆ H :=
  hs.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, h1, H.one_mem⟩

theorem Subgroup.mem_of_isOpen_of_pos (H : Subgroup ℝˣ) (hH : IsOpen (H : Set ℝˣ)) {r : ℝˣ}
    (hr : 0 < (r : ℝ)) : r ∈ H := by
  let f : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)
  have hf : Continuous f := Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp
  have hsub := Subgroup.subset_of_isPreconnected H hH (isPreconnected_range hf)
    ⟨0, Units.ext (by simp [f])⟩
  exact hsub ⟨Real.log r, Units.ext (Real.exp_log hr)⟩

theorem Subgroup.mem_of_isOpen_complexUnits (H : Subgroup ℂˣ) (hH : IsOpen (H : Set ℂˣ)) (z : ℂˣ) :
    z ∈ H :=
  Subgroup.subset_of_isPreconnected H hH isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z)

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

theorem infiniteEmbedding_mem_of_isOpen_of_isReal (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsReal)
    {a : (w.Completion)ˣ}
    (ha : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion)) :
    infiniteEmbedding w a ∈ H := by
  let Hr : Subgroup ℝˣ := (H.comap (infiniteEmbedding w)).comap (realUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hr : Set ℝˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (realUnitsHom hw).continuous
  let r : ℝˣ := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).toMonoidHom a
  have hr : 0 < (r : ℝ) := by
    change 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (a : w.Completion)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ha
  have hmem : r ∈ Hr := Subgroup.mem_of_isOpen_of_pos Hr hopen hr
  rw [← realUnitsHom_surjective hw a]
  exact hmem

theorem infiniteEmbedding_mem_of_isOpen_of_isComplex (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsComplex)
    (a : (w.Completion)ˣ) : infiniteEmbedding w a ∈ H := by
  let Hc : Subgroup ℂˣ := (H.comap (infiniteEmbedding w)).comap (complexUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hc : Set ℂˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (complexUnitsHom hw).continuous
  have hmem := Subgroup.mem_of_isOpen_complexUnits Hc hopen
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw :
      w.Completion →+* ℂ).toMonoidHom a)
  rw [← complexUnitsHom_surjective hw a]
  exact hmem

theorem Modulus.exists_congruenceSubgroup_le (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup ≤ H := by
  classical
  have hWf : (H.comap ofFinite : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ 𝓝 1 :=
    (hH.preimage continuous_ofFinite).mem_nhds (by simp [H.one_mem])
  obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hWf
  have hsupp : (support n).Finite :=
    S.finite_toSet.subset fun v hv ↦ by
      by_contra h
      exact hv (hn0 v h)
  let 𝔪 : Modulus K := ⟨∏ᶠ v, v.asIdeal ^ n v, finprod_asIdeal_pow_ne_bot n, Set.univ⟩
  have hle : ∀ v, n v ≤ 𝔪.exponent v :=
    (finprod_asIdeal_pow_dvd_iff hsupp (finprod_asIdeal_pow_ne_bot n)).1 dvd_rfl
  refine ⟨𝔪, rfl, fun x hx ↦ ?_⟩
  obtain ⟨hf, hi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
  rw [← ofFinite_mul_ofInfinite x]
  refine H.mul_mem ?_ ?_
  · have : toFinite K x ∈ finiteLevel n := mem_finiteLevel.2 fun v ↦ by
      rw [finiteComponent_toFinite]
      exact unitsLevel_antitone v (hle v) (hf v)
    exact hsub this
  · rw [ofInfinite_eq_prod]
    refine Subgroup.prod_mem H fun w _ ↦ ?_
    rcases w.isReal_or_isComplex with hw | hw
    · exact infiniteEmbedding_mem_of_isOpen_of_isReal H hH hw (hi ⟨w, hw⟩ (Set.mem_univ _))
    · exact infiniteEmbedding_mem_of_isOpen_of_isComplex H hH hw _

theorem IdeleClassGroup.exists_map_congruenceSubgroup_le (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Modulus.exists_congruenceSubgroup_le (H.comap (IdeleClassGroup.mk K))
    (hH.preimage (IdeleClassGroup.continuous_mk K))
  exact ⟨𝔪, h𝔪, Subgroup.map_le_iff_le_comap.2 hle⟩

theorem IdeleClassGroup.exists_map_congruenceSubgroup_le_of_finiteIndex
    (H : Subgroup (IdeleClassGroup K)) (hH : IsOpen (H : Set (IdeleClassGroup K)))
    (_ : H.FiniteIndex) :
    ∃ 𝔪 : Modulus K, 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H :=
  (IdeleClassGroup.exists_map_congruenceSubgroup_le H hH).imp fun _ h ↦ h.2

theorem Modulus.isOpen_map_congruenceSubgroup (𝔪 : Modulus K) :
    IsOpen (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) : Set (IdeleClassGroup K)) := by
  rw [Subgroup.coe_map]
  exact IdeleClassGroup.isOpenMap_mk K _ 𝔪.isOpen_congruenceSubgroup

end

end Sec5_02_ClassFieldConsequences_OpenSubgroup

/-! ### 03_ExistenceTheorem.KummerNorm -/
section Sec5_03_ExistenceTheorem_KummerNorm

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
  SemiLocal ProfCoh

noncomputable section

universe u

theorem IdeleGroup.finiteProj_mem_units_of_ord_eq_zero {K : Type*} [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} (h : ord v x = 0) :
    finiteProj v x ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  rw [ord_eq_zero_iff] at h
  refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
  · rw [coe_finiteProj]
    exact h.1
  · rw [← map_inv, coe_finiteProj]
    exact h.2

section SUnits

variable {K : Type u} [Field K] [NumberField K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

omit [HasEnoughRootsOfUnity K n] in
theorem unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) :
    (unitsPow K n).subgroupOf (S.unit K) = (powMonoidHom n : S.unit K →* S.unit K).range := by
  ext e
  rw [Subgroup.mem_subgroupOf, mem_unitsPow, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    have hzu : z ∈ S.unit K := by
      intro v hv
      have he : v.valuationOfNeZero (e : Kˣ) = 1 := by
        have h := e.2 v hv
        rw [← valuationOfNeZero_eq] at h
        exact_mod_cast h
      have h1 : v.valuationOfNeZero z ^ n = 1 := by rw [← map_pow, hz, he]
      rw [← valuationOfNeZero_eq, (pow_eq_one_iff.1 h1).resolve_right (NeZero.ne n),
        WithZero.coe_one]
    exact ⟨⟨z, hzu⟩, Subtype.ext hz⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem index_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).index =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [unitsPow_subgroupOf_sUnit, SUnit.index_range_powMonoidHom]

instance finiteIndex_unitsPow_subgroupOf_sUnit (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    ((unitsPow K n).subgroupOf (S.unit K)).FiniteIndex :=
  ⟨by rw [index_unitsPow_subgroupOf_sUnit]; exact pow_ne_zero _ (NeZero.ne n)⟩

variable (K) in
abbrev sUnitKummerField (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K (AlgebraicClosure K) :=
  kummerExtension K n (AlgebraicClosure K) (S.unit K)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

instance sUnitKummerField.numberField : NumberField (sUnitKummerField K n S) :=
  NumberField.of_module_finite K _

instance sUnitKummerField.isAbelianGalois : IsAbelianGalois K (sUnitKummerField K n S) :=
  { toIsGalois := inferInstance, toIsMulCommutative := inferInstance }

theorem finrank_sUnitKummerField :
    Module.finrank K (sUnitKummerField K n S) =
      n ^ (Fintype.card (InfinitePlace K) + Nat.card S) := by
  rw [finrank_kummerExtension, ← Subgroup.index, index_unitsPow_subgroupOf_sUnit]

end SUnits

section Symbol

attribute [local instance] galCommGroup

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S]

theorem ideleSymbol_adjoin_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {a : Kˣ} (ha : a ∈ S.unit K) (β : sUnitKummerField K n S)
    (hβ : β ^ n = algebraMap K _ (a : K)) {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (K⟮β⟯ : IntermediateField K (sUnitKummerField K n S)) x = 1 := by
  have hexpM : ∀ τ : Gal(sUnitKummerField K n S/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  have hexp : ∀ τ : Gal(K⟮β⟯/K), τ ^ n = 1 := by
    intro τ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := K⟮β⟯)
      (E := sUnitKummerField K n S) τ
    rw [← map_pow, hexpM, map_one]
  have hβ' : (⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯) ^ n = algebraMap K K⟮β⟯ (a : K) :=
    Subtype.ext (by exact hβ)
  have hgen : adjoin K {(⟨β, mem_adjoin_simple_self K β⟩ : K⟮β⟯)} = ⊤ :=
    lift_injective _ (by rw [lift_adjoin_simple, lift_top])
  have hinf : ∀ w, infiniteLocalSymbol K⟮β⟯ w (infiniteProj w x) = 1 := by
    intro w
    obtain ⟨t, ht⟩ := hx.2.1 w
    rw [← ht, powMonoidHom_apply, map_pow, hexp]
  have hfin : ∀ v, localSymbol K⟮β⟯ v (finiteProj v x) = 1 := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨t, ht⟩ := hx.1 v hv
      rw [← ht, powMonoidHom_apply, map_pow, hexp]
    · have hord : ord v x = 0 := hx.2.2 v (by simpa using hv)
      obtain ⟨w⟩ := nonempty_placesOver K⟮β⟯ v
      have hnv : (n : 𝓞 K) ∉ v.asIdeal := fun h ↦ hv (hS v h)
      have hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)) := by
        have h := ha v hv
        rw [← valuationOfNeZero_eq] at h
        rw [← valuationOfNeZero_eq, show v.valuationOfNeZero a = 1 by exact_mod_cast h]
        simp
      have he := Kummer.ramificationIdx_eq_one_of_pow_eq (M := K⟮β⟯) a hβ' hgen v hnv hav
        w.1.asIdeal
      exact units_le_ker_localSymbol K⟮β⟯ v w he (finiteProj_mem_units_of_ord_eq_zero hord)
  rw [ideleSymbol_apply, finprod_eq_one_of_forall_eq_one hfin,
    Finset.prod_eq_one fun w _ ↦ hinf w, mul_one]

theorem ideleSymbol_sUnitKummerField_eq_one
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {x : IdeleGroup K} (hx : x ∈ powerSubgroup n S ∅) :
    ideleSymbol K (sUnitKummerField K n S) x = 1 := by
  set M := sUnitKummerField K n S
  have hfix : ∀ (β : M) (a : Kˣ), a ∈ S.unit K →
      (β : AlgebraicClosure K) ^ n = algebraMap K _ (a : K) → ideleSymbol K M x β = β := by
    intro β a ha hβ
    have hβ' : β ^ n = algebraMap K M (a : K) := Subtype.ext hβ
    have h1 := restrictNormal_ideleSymbol (K⟮β⟯ : IntermediateField K M) M x
    rw [ideleSymbol_adjoin_eq_one hS ha β hβ' hx, AlgEquiv.restrictNormal_eq_one_iff] at h1
    exact h1 β (mem_adjoin_simple_self K β)
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin K (S := M)
    (s := {α : AlgebraicClosure K | ∃ a ∈ S.unit K, α ^ n = algebraMap K _ (a : K)}) rfl ?_
  rintro y ⟨a, ha, hy⟩
  exact hfix _ a ha hy

theorem map_powerSubgroup_le_range_ideleClassNorm
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (powerSubgroup n S ∅).map (IdeleClassGroup.mk K) ≤
      (ideleClassNorm K (sUnitKummerField K n S)).range := by
  rw [← ker_reciprocityMap, Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, reciprocityMap_mk]
  exact ideleSymbol_sUnitKummerField_eq_one hS hx

theorem range_ideleClassNorm_sUnitKummerField (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤) :
    (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range =
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) := by
  have hle := map_powerSubgroup_le_range_ideleClassNorm (n := n)
    (S := (S : Set (HeightOneSpectrum (𝓞 K)))) fun v hv ↦ Finset.mem_coe.2 (hS v hv)
  have h1 : (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range.index =
      n ^ (S.card + Fintype.card (InfinitePlace K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_sUnitKummerField,
      Nat.card_coe_set_eq, Set.ncard_coe_finset, add_comm]
  have h2 := index_map_powerSubgroup (n := n) S hS hJ
  have hrel := Subgroup.relIndex_mul_index hle
  rw [h1, h2] at hrel
  have hone : ((powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map
      (IdeleClassGroup.mk K)).relIndex
      (ideleClassNorm K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K))))).range = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) (by rw [hrel, one_mul])
  exact le_antisymm (Subgroup.relIndex_eq_one.1 hone) hle

end Symbol

end

end Sec5_03_ExistenceTheorem_KummerNorm

/-! ### 04_ExistenceTheorem.Kummer -/
section Sec5_04_ExistenceTheorem_Kummer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IdeleGroup IntermediateField
open scoped NumberField.AdeleRing

noncomputable section

universe u

section Galois

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [Field M] [NumberField M] [Algebra K M]
  [IsAbelianGalois K M]

theorem reciprocityMap_intermediateField (L : IntermediateField K M) (c : IdeleClassGroup K) :
    reciprocityMap K L c = (reciprocityMap K M c).restrictNormal L := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [reciprocityMap_mk, reciprocityMap_mk, restrictNormal_ideleSymbol]

theorem range_ideleClassNorm_fixedField (N : Subgroup (IdeleClassGroup K))
    (hN : (ideleClassNorm K M).range ≤ N) :
    (ideleClassNorm K (fixedField (N.map (reciprocityMap K M)))).range = N := by
  ext c
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField,
    AlgEquiv.restrictNormal_eq_one_iff]
  rw [← IntermediateField.mem_fixingSubgroup_iff, IntermediateField.fixingSubgroup_fixedField]
  constructor
  · rintro ⟨d, hd, hdc⟩
    have hk : d⁻¹ * c ∈ (reciprocityMap K M).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
    rw [ker_reciprocityMap] at hk
    simpa using N.mul_mem hd (hN hk)
  · intro hc
    exact ⟨c, hc, rfl⟩

theorem exists_intermediateField_range_ideleClassNorm_eq_of_le (N : Subgroup (IdeleClassGroup K))
    (hN : (ideleClassNorm K M).range ≤ N) :
    ∃ L : IntermediateField K M, (ideleClassNorm K L).range = N :=
  ⟨_, range_ideleClassNorm_fixedField N hN⟩

end Galois

section Open

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n]

theorem IdeleGroup.valued_finiteProj_eq_one_of_ord_eq_zero {v : HeightOneSpectrum (𝓞 K)}
    {x : IdeleGroup K} (h : ord v x = 0) :
    Valued.v ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  rw [coe_finiteProj, ← WithZero.exp_log (valued_ne_zero v x)]
  have h' : WithZero.log (Valued.v ((x : 𝔸[K]).2 v)) = 0 := by
    rw [ord] at h
    omega
  rw [h', WithZero.exp_zero]

theorem mem_congruenceSubgroup_of_eq_one (𝔪 : Modulus K) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : ∀ v, 𝔪.exponent v ≠ 0 → v ∈ S) {z : IdeleGroup K} (hzS : ∀ v ∈ S, finiteProj v z = 1)
    (hzo : ∀ v ∉ S, ord v z = 0) (hzi : ∀ w, infiniteProj w z = 1) :
    z ∈ 𝔪.congruenceSubgroup := by
  refine 𝔪.mem_congruenceSubgroup.2 ⟨fun v ↦ ?_, fun w _ ↦ ?_⟩
  · by_cases hv : v ∈ S
    · rw [hzS v hv]
      exact one_mem _
    · have he : 𝔪.exponent v = 0 := by
        by_contra h
        exact hv (hS v h)
      have h1 := valued_finiteProj_eq_one_of_ord_eq_zero (hzo v hv)
      rw [he, mem_unitsLevel]
      refine ⟨h1, ?_⟩
      rw [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact Valuation.map_sub_le _ h1.le (by simp)
  · rw [hzi w.1]
    simp

theorem exists_map_powerSubgroup_le (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ ∧
      (powerSubgroup n (S : Set (HeightOneSpectrum (𝓞 K))) ∅).map (IdeleClassGroup.mk K) ≤ N := by
  classical
  obtain ⟨𝔪, -, h𝔪⟩ := Modulus.exists_congruenceSubgroup_le (N.comap (IdeleClassGroup.mk K))
    (hN.preimage (IdeleClassGroup.continuous_mk K))
  obtain ⟨S₀, hS₀⟩ := exists_finset_sup_sIdeles_eq_top (K := K)
  have hn0 : Ideal.span {(n : 𝓞 K)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast NeZero.ne n
  set P := (Ideal.finite_factors hn0).toFinset
  set T := 𝔪.finite_support_exponent.toFinset
  set S := S₀ ∪ T ∪ P with hSdef
  have hsub : (S₀ : Set (HeightOneSpectrum (𝓞 K))) ⊆ S := by
    intro v hv
    simp [hSdef, Finset.mem_coe.1 hv]
  refine ⟨S, fun v hv ↦ ?_, sup_sIdeles_eq_top_of_subset hsub hS₀, ?_⟩
  · have : v ∈ P := by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.2 hv
    simp [hSdef, this]
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  choose α hα using fun v : S ↦ hx.1 v.1 (Finset.mem_coe.2 v.2)
  choose β hβ using fun w ↦ hx.2.1 w
  let y : IdeleGroup K := (∏ v : S, finiteEmbedding v.1 (α v)) * ∏ w, infiniteEmbedding w (β w)
  have hyS : ∀ v : S, finiteProj v.1 y = α v := by
    intro v
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    rw [Finset.prod_eq_single v (fun u _ hu ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hu (Subtype.ext h.symm)) _) (by simp),
      finiteProj_finiteEmbedding]
  have hyo : ∀ v ∉ S, finiteProj v y = 1 := by
    intro v hv
    simp only [y, map_mul, map_prod, finiteProj_infiniteEmbedding, Finset.prod_const_one, mul_one]
    exact Finset.prod_eq_one fun u _ ↦
      finiteProj_finiteEmbedding_of_ne (fun h ↦ hv (by rw [h]; exact u.2)) _
  have hyi : ∀ w, infiniteProj w y = β w := by
    intro w
    simp only [y, map_mul, map_prod, infiniteProj_finiteEmbedding, Finset.prod_const_one, one_mul]
    rw [Finset.prod_eq_single w (fun u _ hu ↦
      infiniteProj_infiniteEmbedding_of_ne (fun h ↦ hu h.symm) _) (by simp),
      infiniteProj_infiniteEmbedding]
  set z := (y ^ n)⁻¹ * x with hz
  have hzS : ∀ v ∈ (S : Set (HeightOneSpectrum (𝓞 K))), finiteProj v z = 1 := by
    intro v hv
    rw [hz, map_mul, map_inv, map_pow, hyS ⟨v, hv⟩, ← hα ⟨v, hv⟩, powMonoidHom_apply,
      inv_mul_cancel]
  have hzo : ∀ v ∉ (S : Set (HeightOneSpectrum (𝓞 K))), ord v z = 0 := by
    intro v hv
    have hyv : ord v y = 0 := by
      rw [ord, ← coe_finiteProj, hyo v hv, Units.val_one, map_one, WithZero.log_one, neg_zero]
    have hxv : ord v x = 0 := hx.2.2 v (by simpa using hv)
    rw [hz, ord_mul, ord_inv]
    have hpow' : ∀ k : ℕ, ord v (y ^ k) = 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ord_mul, ih, hyv, add_zero]
    rw [hpow' n, hxv]
    simp
  have hzi : ∀ w, infiniteProj w z = 1 := by
    intro w
    rw [hz, map_mul, map_inv, map_pow, hyi w, ← hβ w, powMonoidHom_apply, inv_mul_cancel]
  have hzU : z ∈ 𝔪.congruenceSubgroup :=
    mem_congruenceSubgroup_of_eq_one 𝔪 (S := (S : Set (HeightOneSpectrum (𝓞 K))))
      (fun v hv ↦ by
        have : v ∈ T := by
          rw [Set.Finite.mem_toFinset]
          exact hv
        simp [hSdef, this]) hzS hzo hzi
  have hxyz : x = y ^ n * z := by rw [hz, mul_inv_cancel_left]
  rw [hxyz]
  refine Subgroup.mul_mem _ ?_ (h𝔪 hzU)
  rw [Subgroup.mem_comap, map_pow]
  exact hpow _

end Open

section Existence

variable {K : Type u} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

theorem exists_intermediateField_range_ideleClassNorm_eq (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) ∧
      (diagonal K).range ⊔ sIdeles (S : Set (HeightOneSpectrum (𝓞 K))) = ⊤ ∧
      ∃ L : IntermediateField K (sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))),
        (ideleClassNorm K L).range = N := by
  obtain ⟨S, hS, hJ, hle⟩ := exists_map_powerSubgroup_le N hN hpow
  refine ⟨S, hS, hJ, exists_intermediateField_range_ideleClassNorm_eq_of_le N ?_⟩
  rw [range_ideleClassNorm_sUnitKummerField S hS hJ]
  exact hle

theorem exists_isAbelianGalois_range_ideleClassNorm_eq (N : Subgroup (IdeleClassGroup K))
    (hN : IsOpen (N : Set (IdeleClassGroup K))) (hpow : ∀ c, c ^ n ∈ N) :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsAbelianGalois K L ∧ Monoid.exponent Gal(L/K) ∣ n ∧ (ideleClassNorm K L).range = N := by
  obtain ⟨S, -, -, L, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq N hN hpow
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, ?_, hL⟩
  have hexpM : ∀ τ : Gal(sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))/K), τ ^ n = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (kummerExtension_exponent_dvd K n _ _)
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun τ ↦ ?_
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L)
    (E := sUnitKummerField K n (S : Set (HeightOneSpectrum (𝓞 K)))) τ
  rw [← map_pow, hexpM, map_one]

end Existence

end

end Sec5_04_ExistenceTheorem_Kummer

/-! ### 05_ExistenceTheorem.NormLimitation -/
section Sec5_05_ExistenceTheorem_NormLimitation

open IsDedekindDomain NumberField IntermediateField IdeleGroup AdeleBaseChange

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section MaxAbelian

variable (K M : Type*) [Field K] [Field M] [Algebra K M]

def maxAbelian : IntermediateField K M := fixedField (commutator Gal(M/K))

variable [FiniteDimensional K M] [IsGalois K M]

instance isGalois_maxAbelian : IsGalois K (maxAbelian K M) :=
  IsGalois.of_fixedField_normal_subgroup _

instance isMulCommutative_maxAbelian : IsMulCommutative Gal(maxAbelian K M/K) := by
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  let e : Gal(M/K) ⧸ commutator Gal(M/K) ≃* Gal(maxAbelian K M/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  obtain ⟨a, rfl⟩ := e.surjective σ
  obtain ⟨b, rfl⟩ := e.surjective τ
  rw [← map_mul, ← map_mul]
  exact congrArg e (mul_comm (G := Abelianization Gal(M/K)) a b)

instance isAbelianGalois_maxAbelian : IsAbelianGalois K (maxAbelian K M) where

theorem finrank_maxAbelian :
    Module.finrank K (maxAbelian K M) = Nat.card (Abelianization Gal(M/K)) := by
  have h1 := Module.finrank_mul_finrank K (maxAbelian K M) M
  rw [maxAbelian, finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M,
    ← (commutator Gal(M/K)).card_mul_index] at h1
  have hpos : 0 < Nat.card (commutator Gal(M/K)) := Nat.card_pos
  rw [mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

end MaxAbelian

namespace IdeleClassLimit

open FiniteSubfield

variable (K L : FiniteSubfield) [hKL : Fact (K ≤ L)]
  [(L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal]

theorem ker_abstractSymbol_le :
    (abstractSymbol K L).ker ≤ (FiniteSubfield.ideleClassNorm hKL.out).range :=
  (ker_abstractSymbol K L).le

theorem index_range_ideleClassNorm_dvd :
    (FiniteSubfield.ideleClassNorm hKL.out).range.index ∣
      Nat.card (Abelianization (L.1 ≃ₐ[K.1] L.1)) := by
  refine (Subgroup.index_dvd_of_le (ker_abstractSymbol_le K L)).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card (abstractSymbol K L).range

end IdeleClassLimit

section Transport

theorem index_range_ideleClassNorm_dvd_card_abelianization {K M : Type*} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] [IsGalois K M] :
    (ideleClassNorm K M).range.index ∣ Nat.card (Abelianization Gal(M/K)) := by
  let K' := baseField K M
  let M' := topField M
  let _ : Algebra K K'.1 := (rangeMap (baseEmbedding K M)).toAlgebra
  let _ : Algebra M M'.1 := (rangeMap (embedding M)).toAlgebra
  let _ : Algebra K M'.1 := ((rangeMap (embedding M)).comp (algebraMap K M)).toAlgebra
  have : IsScalarTower K K'.1 M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K M M'.1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hK : Function.Bijective (algebraMap K K'.1) := rangeMap_bijective _
  have hM : Function.Bijective (algebraMap M M'.1) := rangeMap_bijective _
  have : IsGalois K M'.1 :=
    IsGalois.of_algEquiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K M M'.1) hM)
  have : IsGalois K'.1 M'.1 := IsGalois.tower_top_of_isGalois K K'.1 M'.1
  have := FiniteSubfield.normal_subgroupOf_of_isGalois (F := K') (E := M')
  have h1 := IdeleClassLimit.index_range_ideleClassNorm_dvd K' M'
  have hrange : (ideleClassNorm K M).range =
      (ideleClassNorm K'.1 M'.1).range.map (ideleClassNorm K K'.1) := by
    ext c
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨ideleClassNorm K'.1 M'.1 (ideleClassMap M M'.1 d), ⟨_, rfl⟩, ?_⟩
      rw [ideleClassNorm_ideleClassNorm, ← ideleClassNorm_ideleClassNorm (L := M),
        ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hM, pow_one]
    · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
      exact ⟨ideleClassNorm M M'.1 d, by
        rw [ideleClassNorm_ideleClassNorm, ideleClassNorm_ideleClassNorm]⟩
  have hsurj : Function.Surjective (ideleClassNorm K K'.1) := fun c ↦
    ⟨ideleClassMap K K'.1 c, by
      rw [ideleClassNorm_ideleClassMap, finrank_eq_one_of_bijective hK, pow_one]⟩
  have hcard : Nat.card (Abelianization Gal(M'.1/K'.1)) = Nat.card (Abelianization Gal(M/K)) := by
    let f : Gal(M'.1/K'.1) →* Gal(M/K) :=
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M'.1) M).comp (restrictScalarsHom K)
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro σ hσ
      exact restrictNormal_restrictScalars_eq_one (K := K) hM hσ
    have hc : Nat.card Gal(M'.1/K'.1) = Nat.card Gal(M/K) := by
      rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
      have e1 := Module.finrank_mul_finrank K K'.1 M'.1
      have e2 := Module.finrank_mul_finrank K M M'.1
      rw [finrank_eq_one_of_bijective hK, one_mul] at e1
      rw [finrank_eq_one_of_bijective hM, mul_one] at e2
      rw [e1, e2]
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le hc.ge
    exact Nat.card_congr (MulEquiv.ofBijective f hbij).abelianizationCongr.toEquiv
  rw [hrange, ← hcard]
  exact (Subgroup.index_map_dvd _ hsurj).trans h1

universe u

variable {K M : Type u} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

theorem range_ideleClassNorm_maxAbelian :
    (ideleClassNorm K (maxAbelian K M)).range = (ideleClassNorm K M).range := by
  have hle : (ideleClassNorm K M).range ≤ (ideleClassNorm K (maxAbelian K M)).range := by
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm (maxAbelian K M) M c, ideleClassNorm_ideleClassNorm c⟩
  have hE : (ideleClassNorm K (maxAbelian K M)).range.index =
      Nat.card (Abelianization Gal(M/K)) := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative, finrank_maxAbelian]
  have hne : (ideleClassNorm K (maxAbelian K M)).range.index ≠ 0 := by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'
  have heq : (ideleClassNorm K M).range.index = (ideleClassNorm K (maxAbelian K M)).range.index :=
    Nat.dvd_antisymm (hE ▸ index_range_ideleClassNorm_dvd_card_abelianization)
      (Subgroup.index_dvd_of_le hle)
  have hrel := Subgroup.relIndex_mul_index hle
  rw [heq] at hrel
  have h1 : (ideleClassNorm K M).range.relIndex (ideleClassNorm K (maxAbelian K M)).range = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (hrel.trans (one_mul _).symm)
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) hle

theorem index_range_ideleClassNorm_eq_card_abelianization :
    (ideleClassNorm K M).range.index = Nat.card (Abelianization Gal(M/K)) := by
  rw [← range_ideleClassNorm_maxAbelian, index_range_ideleClassNorm_eq_finrank_of_isMulCommutative,
    finrank_maxAbelian]

omit [IsGalois K M] in
theorem exists_isAbelianGalois_range_ideleClassNorm_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range ≤ (ideleClassNorm K L).range := by
  let Ω := AlgebraicClosure L
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.trans K L Ω
  have : IsAlgClosure K Ω := ⟨AlgebraicClosure.isAlgClosed L, inferInstance⟩
  let N := normalClosure K L Ω
  have : IsGalois K N := ⟨⟩
  have : NumberField N := NumberField.of_module_finite K N
  refine ⟨maxAbelian K N, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [range_ideleClassNorm_maxAbelian]
  rintro _ ⟨c, rfl⟩
  exact ⟨ideleClassNorm L N c, ideleClassNorm_ideleClassNorm c⟩

end Transport

end

end Sec5_05_ExistenceTheorem_NormLimitation

/-! ### 06_ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini -/
section Sec5_06_ExistenceTheorem_Main

open IsDedekindDomain NumberField IntermediateField IdeleGroup

noncomputable section

universe u

instance numberField_of_finiteDimensional {K Ω : Type*} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L] : NumberField L :=
  NumberField.of_module_finite K L

section NormGroup

variable {K : Type*} [Field K] [NumberField K]

theorem range_ideleClassNorm_congr {L L' : Type*} [Field L] [NumberField L] [Field L']
    [NumberField L'] [Algebra K L] [Algebra K L'] (τ : L ≃ₐ[K] L') :
    (ideleClassNorm K L').range = (ideleClassNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨e, rfl⟩ := (ideleClassEquiv (τ : L ≃+* L')).surjective d
    exact ⟨e, (ideleClassNorm_ideleClassEquiv τ e).symm⟩
  · rintro ⟨d, rfl⟩
    exact ⟨_, ideleClassNorm_ideleClassEquiv τ d⟩

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M]

theorem range_ideleClassNorm_eq_comap (F : IntermediateField K M) :
    (ideleClassNorm K F).range = F.fixingSubgroup.comap (reciprocityMap K M) := by
  ext c
  rw [← ker_reciprocityMap, MonoidHom.mem_ker, reciprocityMap_intermediateField,
    AlgEquiv.restrictNormal_eq_one_iff, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]

end NormGroup

section Compositum

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem isMulCommutative_sup (L₁ L₂ : IntermediateField K Ω) [IsAbelianGalois K L₁]
    [IsAbelianGalois K L₂] [Normal K ↥(L₁ ⊔ L₂)] : IsMulCommutative Gal(↥(L₁ ⊔ L₂)/K) := by
  have h₁ : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
  have h₂ : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
  have key : ∀ (L : IntermediateField K Ω) [IsAbelianGalois K L] (h : L ≤ L₁ ⊔ L₂)
      (σ τ : Gal(↥(L₁ ⊔ L₂)/K)), (τ * σ)⁻¹ * (σ * τ) ∈ (restrict h).fixingSubgroup := by
    intro L _ h σ τ
    let _ : Algebra L ↥(L₁ ⊔ L₂) := (IntermediateField.inclusion h).toAlgebra
    have : IsScalarTower K L ↥(L₁ ⊔ L₂) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    obtain ⟨x, rfl⟩ : ∃ x : L, algebraMap L ↥(L₁ ⊔ L₂) x = y := ⟨⟨y, (mem_restrict h y).1 hy⟩, rfl⟩
    have hm : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L ((τ * σ)⁻¹ * (σ * τ)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm' (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L τ), inv_mul_cancel]
    have hc := AlgEquiv.restrictNormal_commutes ((τ * σ)⁻¹ * (σ * τ)) L x
    change algebraMap L _ (AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥(L₁ ⊔ L₂)) L
      ((τ * σ)⁻¹ * (σ * τ)) x) = _ at hc
    rw [hm, AlgEquiv.one_apply] at hc
    exact hc.symm
  refine ⟨⟨fun σ τ ↦ ?_⟩⟩
  have htop : restrict h₁ ⊔ restrict h₂ = (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)) := by
    refine top_unique fun y _ ↦ ?_
    have hy : (y : Ω) ∈ lift (restrict h₁) ⊔ lift (restrict h₂) := by
      rw [lift_restrict, lift_restrict]
      exact y.2
    rw [← lift_sup] at hy
    exact (mem_lift y).1 hy
  have hρ : (τ * σ)⁻¹ * (σ * τ) ∈ (⊤ : IntermediateField K ↥(L₁ ⊔ L₂)).fixingSubgroup := by
    rw [← htop, fixingSubgroup_sup]
    exact ⟨key L₁ h₁ σ τ, key L₂ h₂ σ τ⟩
  have h1 : (τ * σ)⁻¹ * (σ * τ) = 1 :=
    AlgEquiv.ext fun y ↦ (IntermediateField.mem_fixingSubgroup_iff _ _).1 hρ y mem_top
  rw [inv_mul_eq_one] at h1
  exact h1.symm

instance isAbelianGalois_sup [CharZero K] (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    IsAbelianGalois K ↥(L₁ ⊔ L₂) :=
  have : IsGalois K ↥(L₁ ⊔ L₂) := ⟨⟩
  { toIsMulCommutative := isMulCommutative_sup L₁ L₂ }

end Compositum

section Existence

variable {K : Type u} [Field K] [NumberField K]

theorem exists_isAbelianGalois_range_ideleClassNorm_eq_of_le (L : Type u) [Field L] [NumberField L]
    [Algebra K L] (N : Subgroup (IdeleClassGroup K)) (hN : (ideleClassNorm K L).range ≤ N) :
    ∃ (E : Type u) (_ : Field E) (_ : NumberField E) (_ : Algebra K E),
      IsAbelianGalois K E ∧ (ideleClassNorm K E).range = N := by
  obtain ⟨E, _, _, _, _, hE⟩ := exists_isAbelianGalois_range_ideleClassNorm_le (K := K) L
  exact ⟨fixedField (N.map (reciprocityMap K E)), inferInstance, inferInstance, inferInstance,
    inferInstance, range_ideleClassNorm_fixedField N (hE.trans hN)⟩

theorem exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex
    (N : Subgroup (IdeleClassGroup K)) (hN : IsOpen (N : Set (IdeleClassGroup K))) [N.FiniteIndex] :
    ∃ (L : Type u) (_ : Field L) (_ : NumberField L) (_ : Algebra K L),
      IsAbelianGalois K L ∧ (ideleClassNorm K L).range = N := by
  have : NeZero N.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  let K' := CyclotomicField N.index K
  have : HasEnoughRootsOfUnity K' N.index :=
    ⟨⟨_, IsCyclotomicExtension.zeta_spec N.index K K'⟩, rootsOfUnity.isCyclic _ _⟩
  let N' := N.comap (ideleClassNorm K K')
  have hN' : IsOpen (N' : Set (IdeleClassGroup K')) := hN.preimage continuous_ideleClassNorm
  have : N.Normal := ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  have hpow : ∀ c, c ^ N.index ∈ N' := fun c ↦ by
    rw [Subgroup.mem_comap, map_pow]
    exact N.pow_index_mem _
  obtain ⟨L', _, _, _, -, -, hL'⟩ := exists_isAbelianGalois_range_ideleClassNorm_eq N' hN' hpow
  let _ : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine exists_isAbelianGalois_range_ideleClassNorm_eq_of_le L' N ?_
  rintro _ ⟨c, rfl⟩
  rw [← ideleClassNorm_ideleClassNorm (L := K')]
  have hc : ideleClassNorm K' L' c ∈ N' := hL' ▸ ⟨c, rfl⟩
  exact hc

end Existence

section Open

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L]

theorem isOpen_range_ideleClassNorm :
    IsOpen ((ideleClassNorm K L).range : Set (IdeleClassGroup K)) := by
  rw [← ker_reciprocityMap, MonoidHom.coe_ker]
  exact (isOpen_discrete {1}).preimage continuous_reciprocityMap

instance finiteIndex_range_ideleClassNorm : (ideleClassNorm K L).range.FiniteIndex :=
  ⟨by
    rw [index_range_ideleClassNorm_eq_finrank_of_isMulCommutative]
    exact Module.finrank_pos.ne'⟩

end Open

section Correspondence

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]

theorem range_ideleClassNorm_le_range_iff (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    (ideleClassNorm K L₂).range ≤ (ideleClassNorm K L₁).range ↔ L₁ ≤ L₂ := by
  constructor
  · intro h
    have h₁ : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
    have h₂ : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
    have e₁ : (ideleClassNorm K (restrict h₁)).range = (ideleClassNorm K L₁).range :=
      range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₁))
    have e₂ : (ideleClassNorm K (restrict h₂)).range = (ideleClassNorm K L₂).range :=
      range_ideleClassNorm_congr (AlgEquiv.ofInjectiveField (IntermediateField.inclusion h₂))
    rw [← e₁, ← e₂, range_ideleClassNorm_eq_comap, range_ideleClassNorm_eq_comap,
      Subgroup.comap_le_comap_of_surjective reciprocityMap_surjective] at h
    have hF : restrict h₁ ≤ restrict h₂ := by
      rw [← IsGalois.intermediateFieldEquivSubgroup.le_iff_le]
      exact h
    intro x hx
    exact (mem_restrict h₂ ⟨x, h₁ hx⟩).1 (hF ((mem_restrict h₁ ⟨x, h₁ hx⟩).2 hx))
  · intro h
    let _ : Algebra L₁ L₂ := (IntermediateField.inclusion h).toAlgebra
    have : IsScalarTower K L₁ L₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    rintro _ ⟨c, rfl⟩
    exact ⟨ideleClassNorm L₁ L₂ c, ideleClassNorm_ideleClassNorm c⟩

variable [IsAlgClosed Ω]

theorem exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex
    (N : Subgroup (IdeleClassGroup K)) (hN : IsOpen (N : Set (IdeleClassGroup K))) [N.FiniteIndex] :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      (ideleClassNorm K L).range = N := by
  obtain ⟨L, _, _, _, _, hL⟩ := exists_isAbelianGalois_range_ideleClassNorm_eq_of_finiteIndex N hN
  let f : L →ₐ[K] Ω := IsAlgClosed.lift
  let τ := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := LinearEquiv.finiteDimensional τ.toLinearEquiv
  have : IsAbelianGalois K f.fieldRange := IsAbelianGalois.of_algHom τ.symm.toAlgHom
  exact ⟨f.fieldRange, inferInstance, inferInstance, (range_ideleClassNorm_congr τ).trans hL⟩

variable (K Ω) in
abbrev FiniteAbelianSubfield : Type u :=
  {L : IntermediateField K Ω // FiniteDimensional K L ∧ IsAbelianGalois K L}

variable (K) in
abbrev OpenFiniteIndexSubgroup : Type u :=
  {N : Subgroup (IdeleClassGroup K) // IsOpen (N : Set (IdeleClassGroup K)) ∧ N.FiniteIndex}

def normGroup (L : FiniteAbelianSubfield K Ω) : OpenFiniteIndexSubgroup K :=
  haveI := L.2.1
  haveI := L.2.2
  ⟨(ideleClassNorm K L.1).range, isOpen_range_ideleClassNorm, inferInstance⟩

omit [IsAlgClosed Ω] in
theorem normGroup_le_normGroup_iff (L₁ L₂ : FiniteAbelianSubfield K Ω) :
    normGroup L₂ ≤ normGroup L₁ ↔ L₁ ≤ L₂ := by
  have := L₁.2.1
  have := L₁.2.2
  have := L₂.2.1
  have := L₂.2.2
  exact range_ideleClassNorm_le_range_iff L₁.1 L₂.1

omit [IsAlgClosed Ω] in
theorem normGroup_injective : Function.Injective (normGroup (K := K) (Ω := Ω)) := fun L₁ L₂ h ↦
  le_antisymm ((normGroup_le_normGroup_iff L₁ L₂).1 h.ge) ((normGroup_le_normGroup_iff L₂ L₁).1 h.le)

theorem normGroup_surjective : Function.Surjective (normGroup (K := K) (Ω := Ω)) := fun N ↦ by
  have := N.2.2
  obtain ⟨L, h1, h2, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω)
    N.1 N.2.1
  exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩

variable (K Ω) in
def normGroupOrderIso : FiniteAbelianSubfield K Ω ≃o (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := (Equiv.ofBijective normGroup ⟨normGroup_injective, normGroup_surjective⟩).trans
    OrderDual.toDual
  map_rel_iff' {L₁ L₂} := normGroup_le_normGroup_iff L₁ L₂

theorem normGroupOrderIso_apply (L : FiniteAbelianSubfield K Ω) :
    OrderDual.ofDual (normGroupOrderIso K Ω L) = normGroup L :=
  rfl

end Correspondence

end

end Sec5_06_ExistenceTheorem_Main

/-! ### 07_GlobalArtinMap.ArtinMap -/
section Sec5_07_GlobalArtinMap_ArtinMap

open IsDedekindDomain NumberField IntermediateField IdeleGroup RHDirect.CFT.LocalField SemiLocal

noncomputable section

universe u

section Restrict

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem reciprocityMap_apply_of_le {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [IsAbelianGalois K L] [FiniteDimensional K L'] [IsAbelianGalois K L'] (h : L ≤ L')
    (c : IdeleClassGroup K) (l : L) :
    ((reciprocityMap K L' c ⟨l, h l.2⟩ : L') : Ω) = ((reciprocityMap K L c l : L) : Ω) := by
  let _ : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  rw [reciprocityMap_mk, reciprocityMap_mk, ← restrictNormal_ideleSymbol (L := L) (M := L')]
  exact congrArg Subtype.val (AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l).symm

variable [IsGalois K Ω]

omit [NumberField K] in
theorem restrictAb_eq_of_le {L L' : IntermediateField K Ω} [Normal K L] [Normal K L']
    (hL' : L' ≤ maximalAbelianExtension K Ω) (h : L ≤ L')
    {σ τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (hστ : restrictAb L' hL' σ = restrictAb L' hL' τ) :
    restrictAb L (h.trans hL') σ = restrictAb L (h.trans hL') τ := by
  ext l
  have e := congrArg (fun ρ : L' ≃ₐ[K] L' ↦ ((ρ ⟨l, h l.2⟩ : L') : Ω)) hστ
  simp only [restrictAb_apply] at e ⊢
  exact e

theorem restrictAb_eq_reciprocityMap_of_le {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [IsAbelianGalois K L] [FiniteDimensional K L'] [IsAbelianGalois K L'] (h : L ≤ L')
    {c : IdeleClassGroup K} {τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω}
    (hτ : restrictAb L' (le_maximalAbelianExtension L') τ = reciprocityMap K L' c) :
    restrictAb L (le_maximalAbelianExtension L) τ = reciprocityMap K L c := by
  ext l
  have e := congrArg (fun ρ : L' ≃ₐ[K] L' ↦ ((ρ ⟨l, h l.2⟩ : L') : Ω)) hτ
  simp only [restrictAb_apply] at e ⊢
  rw [e, reciprocityMap_apply_of_le h]

end Restrict

section ArtinMap

variable (K : Type*) [Field K] [NumberField K] (Ω : Type*) [Field Ω] [Algebra K Ω] [IsGalois K Ω]

instance nonempty_finiteAbelianExtensions : Nonempty (finiteAbelianExtensions K Ω) :=
  ⟨⟨⊥, inferInstance, inferInstance⟩⟩

variable {K Ω} in
def fiberOver (c : IdeleClassGroup K) (L : finiteAbelianExtensions K Ω) :
    Set (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  haveI := L.2.1
  haveI := L.2.2
  {τ | restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ =
    reciprocityMap K (L : IntermediateField K Ω) c}

theorem exists_restrictAb_eq_reciprocityMap (c : IdeleClassGroup K) :
    ∃ τ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω,
      ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
        restrictAb L (le_maximalAbelianExtension L) τ = reciprocityMap K L c := by
  have hcl : ∀ L : finiteAbelianExtensions K Ω, IsClosed (fiberOver c L) := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact isClosed_eq (continuous_restrictAb _ _) continuous_const
  have hne : ∀ L : finiteAbelianExtensions K Ω, (fiberOver c L).Nonempty := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact restrictAb_surjective (L : IntermediateField K Ω) _ _
  have hdir : Directed (· ⊇ ·) (fiberOver (Ω := Ω) c) := by
    intro L₁ L₂
    have := L₁.2.1
    have := L₁.2.2
    have := L₂.2.1
    have := L₂.2.2
    refine ⟨⟨(L₁ : IntermediateField K Ω) ⊔ L₂, inferInstance, inferInstance⟩, fun τ hτ ↦ ?_,
      fun τ hτ ↦ ?_⟩
    · exact restrictAb_eq_reciprocityMap_of_le le_sup_left hτ
    · exact restrictAb_eq_reciprocityMap_of_le le_sup_right hτ
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fiberOver c) hdir hne (fun L ↦ (hcl L).isCompact) hcl
  refine ⟨τ, fun L _ _ ↦ ?_⟩
  exact Set.mem_iInter.1 hτ ⟨L, inferInstance, inferInstance⟩

def artinMap : IdeleClassGroup K →* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) where
  toFun c := (exists_restrictAb_eq_reciprocityMap K Ω c).choose
  map_one' := ext_restrictAb fun L _ _ ↦ by
    rw [(exists_restrictAb_eq_reciprocityMap K Ω 1).choose_spec L, map_one, map_one]
  map_mul' c d := ext_restrictAb fun L _ _ ↦ by
    rw [(exists_restrictAb_eq_reciprocityMap K Ω (c * d)).choose_spec L, map_mul, map_mul,
      (exists_restrictAb_eq_reciprocityMap K Ω c).choose_spec L,
      (exists_restrictAb_eq_reciprocityMap K Ω d).choose_spec L]

variable {K Ω}

@[simp]
theorem restrictAb_artinMap (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
    (c : IdeleClassGroup K) :
    restrictAb L (le_maximalAbelianExtension L) (artinMap K Ω c) = reciprocityMap K L c :=
  (exists_restrictAb_eq_reciprocityMap K Ω c).choose_spec L

theorem artinMap_apply (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
    (c : IdeleClassGroup K) (l : L) :
    ((artinMap K Ω c ⟨l, le_maximalAbelianExtension L l.2⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((reciprocityMap K L c l : L) : Ω) := by
  rw [← restrictAb_artinMap L c, restrictAb_apply]

theorem continuous_artinMap : Continuous (artinMap K Ω) :=
  continuous_iff_restrictAb.2 fun L _ _ ↦ by
    simp only [restrictAb_artinMap]
    exact continuous_reciprocityMap

end ArtinMap

section Local

variable {K : Type*} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

theorem restrictAb_artinMap_finiteEmbedding (v : HeightOneSpectrum (𝓞 K))
    (a : (v.adicCompletion K)ˣ) :
    restrictAb L (le_maximalAbelianExtension L)
        (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v a))) = localSymbol L v a := by
  rw [restrictAb_artinMap, reciprocityMap_mk, ideleSymbol_finiteEmbedding]

theorem artinMap_finiteEmbedding_apply (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v)
    {Ωv : Type*} [Field Ωv] [Algebra (v.adicCompletion K) Ωv] [IsSepClosure (v.adicCompletion K) Ωv]
    (ι : w.1.adicCompletion L →ₐ[v.adicCompletion K] Ωv) (a : (v.adicCompletion K)ˣ) (l : L) :
    ι (algebraMap L (w.1.adicCompletion L)
        (restrictAb L (le_maximalAbelianExtension L)
          (artinMap K Ω (IdeleClassGroup.mk K (finiteEmbedding v a))) l)) =
      ((localArtinMap (v.adicCompletion K) Ωv a
        ⟨ι (algebraMap L (w.1.adicCompletion L) l), apply_mem_maximalAbelianExtension ι _⟩ :
          maximalAbelianExtension (v.adicCompletion K) Ωv) : Ωv) := by
  rw [restrictAb_artinMap_finiteEmbedding, algebraMap_localSymbol_apply,
    normResidueSymbol_apply_eq_localArtinMap]

end Local

end

end Sec5_07_GlobalArtinMap_ArtinMap

/-! ### 08_GlobalArtinMap.Kernel -/
section Sec5_08_GlobalArtinMap_Kernel

open IsDedekindDomain NumberField IntermediateField IdeleGroup RHDirect.CFT.LocalField

noncomputable section

universe u

instance IdeleClassGroup.normal_connectedComponentOfOne (K : Type*) [Field K] [NumberField K] :
    (Subgroup.connectedComponentOfOne (IdeleClassGroup K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

section Path

variable {K : Type*} [Field K] [NumberField K]

theorem IdeleGroup.exists_continuous_ideleModule_eq_exp (w : InfinitePlace K) :
    ∃ γ : ℝ → IdeleGroup K, Continuous γ ∧ γ 0 = 1 ∧
      ∀ t, (IdeleGroup.ideleModule K (γ t) : ℝ) = Real.exp t := by
  rcases w.isReal_or_isComplex with hw | hw
  · let u : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)
    have hu : Continuous u := Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp
    have hu0 : u 0 = 1 := Units.ext (by simp [u])
    refine ⟨fun t ↦ infiniteEmbedding w (realUnitsHom hw (u t)),
      (continuous_infiniteEmbedding w).comp ((realUnitsHom hw).continuous.comp hu), ?_, fun t ↦ ?_⟩
    · simp only [hu0, map_one]
    · rw [ideleModule_infiniteEmbedding]
      let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      have hval : ((realUnitsHom hw (u t) : (w.Completion)ˣ) : w.Completion) = e.symm (Real.exp t) :=
        rfl
      have hn : ‖e.symm (Real.exp t)‖ = ‖e (e.symm (Real.exp t))‖ := by
        rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) _).symm
      rw [hval, hn, RingEquiv.apply_symm_apply, Real.norm_of_nonneg (Real.exp_pos t).le]
      simp [InfinitePlace.mult, hw]
  · let u : ℝ → ℂˣ := fun t ↦ Units.mk0 ((Real.exp (t / 2) : ℝ) : ℂ)
      (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _))
    have hu : Continuous u := Units.isEmbedding_val₀.isInducing.continuous_iff.2
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2)))
    have hu0 : u 0 = 1 := Units.ext (by simp [u])
    refine ⟨fun t ↦ infiniteEmbedding w (complexUnitsHom hw (u t)),
      (continuous_infiniteEmbedding w).comp ((complexUnitsHom hw).continuous.comp hu), ?_, fun t ↦ ?_⟩
    · simp only [hu0, map_one]
    · rw [ideleModule_infiniteEmbedding]
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      have hval : ((complexUnitsHom hw (u t) : (w.Completion)ˣ) : w.Completion) =
          e.symm ((Real.exp (t / 2) : ℝ) : ℂ) :=
        rfl
      have hn : ‖e.symm ((Real.exp (t / 2) : ℝ) : ℂ)‖ = ‖e (e.symm ((Real.exp (t / 2) : ℝ) : ℂ))‖ := by
        rw [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]
        exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) _).symm
      have hw' : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hw
      rw [hval, hn, RingEquiv.apply_symm_apply, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [InfinitePlace.mult, hw', if_false]
      rw [sq, ← Real.exp_add, add_halves]

theorem IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq (c : IdeleClassGroup K) :
    ∃ d ∈ IdeleClassGroup.normOneSubgroup K, ∃ e ∈ connectedComponent (1 : IdeleClassGroup K),
      c = d * e := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  obtain ⟨γ, hγc, hγ0, hγm⟩ := IdeleGroup.exists_continuous_ideleModule_eq_exp w
  set t := Real.log (IdeleClassGroup.ideleModule K c : ℝ)
  set e := IdeleClassGroup.mk K (γ t)
  have he : IdeleClassGroup.ideleModule K e = IdeleClassGroup.ideleModule K c := by
    apply Subtype.ext
    change (IdeleGroup.ideleModule K (γ t) : ℝ) = _
    rw [hγm, Real.exp_log (IdeleClassGroup.ideleModule K c).2]
  refine ⟨c * e⁻¹, ?_, e, ?_, (inv_mul_cancel_right c e).symm⟩
  · change IdeleClassGroup.ideleModule K (c * e⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  · refine (isPreconnected_range ((IdeleClassGroup.continuous_mk K).comp hγc)).subset_connectedComponent
      ⟨0, ?_⟩ ⟨t, rfl⟩
    simp only [Function.comp_apply, hγ0, map_one]

end Path

section Surjective

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]

theorem connectedComponent_subset_ker_artinMap :
    connectedComponent (1 : IdeleClassGroup K) ⊆ (artinMap K Ω).ker := fun c hc ↦
  ext_restrictAb fun L _ _ ↦ by
    rw [restrictAb_artinMap, map_one]
    have hopen : IsOpen ((reciprocityMap K L).ker : Set (IdeleClassGroup K)) := by
      rw [MonoidHom.coe_ker]
      exact (isOpen_discrete _).preimage continuous_reciprocityMap
    exact Subgroup.subset_of_isPreconnected _ hopen isPreconnected_connectedComponent
      mem_connectedComponent hc

theorem exists_mem_normOneSubgroup_artinMap_eq (c : IdeleClassGroup K) :
    ∃ d ∈ IdeleClassGroup.normOneSubgroup K, artinMap K Ω d = artinMap K Ω c := by
  obtain ⟨d, hd, e, he, rfl⟩ := IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c
  refine ⟨d, hd, ?_⟩
  have h := connectedComponent_subset_ker_artinMap (Ω := Ω) he
  rw [SetLike.mem_coe, MonoidHom.mem_ker] at h
  rw [map_mul, h, mul_one]

theorem artinMap_surjective : Function.Surjective (artinMap K Ω) := by
  intro τ
  let N := IdeleClassGroup.normOneSubgroup K
  let f : N → (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
    fun d ↦ artinMap K Ω d
  have hf : Continuous f := continuous_artinMap.comp continuous_subtype_val
  let t : finiteAbelianExtensions K Ω → Set N := fun L ↦
    have := L.2.1
    have := L.2.2
    {d | restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) (f d) =
      restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ}
  have hcl : ∀ L, IsClosed (t L) := fun L ↦ by
    have := L.2.1
    have := L.2.2
    exact isClosed_eq ((continuous_restrictAb _ _).comp hf) continuous_const
  have hne : ∀ L, (t L).Nonempty := fun L ↦ by
    have := L.2.1
    have := L.2.2
    obtain ⟨c, hc⟩ := reciprocityMap_surjective (K := K) (L := (L : IntermediateField K Ω))
      (restrictAb (L : IntermediateField K Ω) (le_maximalAbelianExtension _) τ)
    obtain ⟨d, hd, hdc⟩ := exists_mem_normOneSubgroup_artinMap_eq (Ω := Ω) c
    refine ⟨⟨d, hd⟩, ?_⟩
    change restrictAb _ _ (artinMap K Ω d) = _
    rw [hdc, restrictAb_artinMap, hc]
  have hdir : Directed (· ⊇ ·) t := by
    intro L₁ L₂
    have := L₁.2.1
    have := L₁.2.2
    have := L₂.2.1
    have := L₂.2.2
    refine ⟨⟨(L₁ : IntermediateField K Ω) ⊔ L₂, inferInstance, inferInstance⟩, fun d hd ↦ ?_,
      fun d hd ↦ ?_⟩
    · exact restrictAb_eq_of_le (le_maximalAbelianExtension _) le_sup_left hd
    · exact restrictAb_eq_of_le (le_maximalAbelianExtension _) le_sup_right hd
  obtain ⟨d, hd⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hne
    (fun L ↦ (hcl L).isCompact) hcl
  refine ⟨d, ext_restrictAb fun L _ _ ↦ ?_⟩
  exact Set.mem_iInter.1 hd ⟨L, inferInstance, inferInstance⟩

end Surjective

section Kernel

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]

theorem IdeleClassGroup.isConnected_preimage_mk_connectedComponent
    (y : IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) :
    IsConnected ((QuotientGroup.mk : IdeleClassGroup K →
      IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ⁻¹' {y}) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have h : (QuotientGroup.mk : IdeleClassGroup K →
      IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ⁻¹'
        {(a : IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K))} =
      (fun x ↦ a * x) '' connectedComponent (1 : IdeleClassGroup K) := by
    ext x
    rw [Set.image_mul_left, Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, eq_comm,
      QuotientGroup.eq]
    rfl
  rw [h]
  exact isConnected_connectedComponent.image _ (continuous_const_mul a).continuousOn

theorem ker_artinMap :
    (artinMap K Ω).ker = Subgroup.connectedComponentOfOne (IdeleClassGroup K) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  refine le_antisymm (fun c hc ↦ ?_) fun c hc ↦ connectedComponent_subset_ker_artinMap hc
  by_contra hcD
  set D := Subgroup.connectedComponentOfOne (IdeleClassGroup K)
  have hDcl : IsClosed (D : Set (IdeleClassGroup K)) := isClosed_connectedComponent
  let π : IdeleClassGroup K → IdeleClassGroup K ⧸ D := QuotientGroup.mk
  have hπc : Continuous π := continuous_quotient_mk'
  have himage : π '' (IdeleClassGroup.normOneSubgroup K : Set (IdeleClassGroup K)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨d, hd, e, he, rfl⟩ := IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c'
    refine ⟨d, hd, QuotientGroup.eq.2 ?_⟩
    exact (inv_mul_cancel_left d e).symm ▸ he
  have : CompactSpace (IdeleClassGroup K ⧸ D) :=
    ⟨himage ▸ (IdeleClassGroup.isCompact_normOneSubgroup K).image hπc⟩
  have hpre := (QuotientGroup.isQuotientMap_mk D).isCoinducing.preimage_connectedComponent
    IdeleClassGroup.isConnected_preimage_mk_connectedComponent 1
  have hnot : π c ∉ connectedComponent (π 1) := by
    intro h
    have h' : c ∈ π ⁻¹' connectedComponent (π 1) := h
    rw [hpre] at h'
    exact hcD h'
  rw [connectedComponent_eq_iInter_isClopen, Set.mem_iInter] at hnot
  push Not at hnot
  obtain ⟨⟨W, hWc, hW1⟩, hcW⟩ := hnot
  replace hW1 : (1 : IdeleClassGroup K ⧸ D) ∈ W := hW1
  obtain ⟨H, hHW⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hWc hW1
  let N : Subgroup (IdeleClassGroup K) := (H : Subgroup (IdeleClassGroup K ⧸ D)).comap (QuotientGroup.mk' D)
  have hNopen : IsOpen (N : Set (IdeleClassGroup K)) := H.isOpen.preimage hπc
  have : (H : Subgroup (IdeleClassGroup K ⧸ D)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have : N.FiniteIndex := ⟨by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective D)]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  have hcN : c ∉ N := fun h ↦ hcW (hHW h)
  obtain ⟨L, _, _, hL⟩ := exists_intermediateField_range_ideleClassNorm_eq_of_finiteIndex (Ω := Ω) N
    hNopen
  apply hcN
  rw [← hL, ← ker_reciprocityMap, MonoidHom.mem_ker, ← restrictAb_artinMap L c,
    MonoidHom.mem_ker.1 hc, map_one]

def artinQuotientEquiv :
    IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K) ≃ₜ*
      (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  have : T2Space (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) := krullTopology_t2
  have hDcl : IsClosed ((Subgroup.connectedComponentOfOne (IdeleClassGroup K)) :
    Set (IdeleClassGroup K)) := isClosed_connectedComponent
  let e := (QuotientGroup.quotientMulEquivOfEq (ker_artinMap (K := K) (Ω := Ω)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ artinMap_surjective)
  have hc : Continuous e := by
    refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    have h : (e ∘ QuotientGroup.mk) = artinMap K Ω := funext fun _ ↦ rfl
    rw [h]
    exact continuous_artinMap
  have : CompactSpace (IdeleClassGroup K ⧸ Subgroup.connectedComponentOfOne (IdeleClassGroup K)) := by
    refine ⟨?_⟩
    have himage : (QuotientGroup.mk : IdeleClassGroup K → IdeleClassGroup K ⧸
        Subgroup.connectedComponentOfOne (IdeleClassGroup K)) ''
          (IdeleClassGroup.normOneSubgroup K : Set (IdeleClassGroup K)) = Set.univ := by
      refine Set.eq_univ_of_forall fun q ↦ ?_
      obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨d, hd, e, he, rfl⟩ := IdeleClassGroup.exists_mem_normOneSubgroup_mul_eq c'
      refine ⟨d, hd, QuotientGroup.eq.2 ?_⟩
      exact (inv_mul_cancel_left d e).symm ▸ he
    exact himage ▸ (IdeleClassGroup.isCompact_normOneSubgroup K).image continuous_quotient_mk'
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end Kernel

end

end Sec5_08_GlobalArtinMap_Kernel

end RHDirect.CFT.Global
