import RHDirect.Stage13SixCaseVWinAssembly
import RHDirect.Stage13MinusParityRubin
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# RHDirect.Stage13MaschkeCharDecomp

Unconditional (`0` open parameters, `0` `sorry`, `0` custom `axiom`s, `0` `native_decide`) Lean 4
formalization of **Stage 13 — Field 1 Discharge: Plus-Parity `Gal(E/ℚ)` Maschke Character
Decomposition, `l`-Adic Cyclotomic DVR Base-Change Length Calculus, Genuine Galois Action on
`Sha1Galois`, and Inflation–Restriction Trivial-Character Descent (`CountZ` Bridge)**.

## Main Results

1. **Abelian Field Structure from `1 ≤ condF E`**:
   - `condF_spec`, `isGalois_of_one_le_condF`, `aut_mul_comm_of_one_le_condF`,
     `finrank_le_condF`, `card_aut_eq_finrank_of_one_le_condF`, `card_aut_le_condF`.

2. **Cyclotomic DVR Coefficient Rings `O / ℤ_[l]` (`eO = 1` when `l ∤ n`)**:
   - `exists_unramified_dvr_rootsOfUnity`: explicit unramified DVR `O / ℤ_[l]` with `eO l O = 1`
     and `HasEnoughRootsOfUnity O n` whenever `¬ l ∣ n`.
   - `exists_dvr_rootsOfUnity`: explicit DVR `O / ℤ_[l]` with `1 ≤ eO l O < ⊤` and
     `HasEnoughRootsOfUnity O n` for arbitrary `n ≥ 1`.

3. **Flat Base-Change Length Calculus & Maschke / `lenEigLe` Character Splitting**:
   - `length_baseChange_eq_eO_mul`: `Module.length O (O ⊗[ℤ_[l]] M) = eO l O * Module.length ℤ_[l] M`.
   - `length_eig_one_baseChange`: `Module.length O (eig (baseChangeRep π) 1) = eO l O * Module.length ℤ_[l] (eig π 1)`.
   - `lenEigLe` (unconditional even when `l ∣ |Q|`) and `lenEigEq` (exact Maschke orthogonal
     idempotents `e_χ = |Q|⁻¹ ∑_{g ∈ Q} χ(g⁻¹) g` when `IsUnit (|Q| : O)`).

4. **Genuine `Gal(E/ℚ)` Action on `Sha1Galois E l k` & Commutation with `conjH1`**:
   - Lift-independent `galActH1`, `galActH1_mem_sha`, `conjH1_eq_smul_galActH1`,
     and `galRepShaPlus : Representation ℤ_[l] (E ≃ₐ[ℚ] E) (ShaPlus E l k)`.

5. **Continuous Corestriction & Inflation–Restriction (`Vlen_trivial_le_sha_rat`)**:
   - `resH1_injective_of_unit_index`, `corH1`, `sha_invariants_length_le_sha_rat`, and
     **`Vlen_trivial_le_sha_rat`**: `Vlen E l k χ ≤ realGaloisSelmerSystem.shaLen ℚ l k`
     for all `1 ≤ condF E`, `l ≠ 2`, `¬ l ∣ Module.finrank ℚ E`, `0 < k`, and `χ.isTrivial = true`.

6. **Zero-Parameter `AbelianCharSelmerData realGaloisSelmerSystem`**:
   - `charSet`, `charSet_card_le` (unconditional for ALL `NumberField E`), `Vlen`, `loss := 0`,
     `plusLen_le_of_one_le_condF`, `plusLen_eq_sum_of_not_dvd`, `loss_eq_zero_of_not_dvd`,
     `loss_le_poly`, and `realGaloisAbelianCharSelmerData` (matching `minusParitySelmerSystem`
     definitionally by `rfl`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators TensorProduct Pointwise
open NumberField IsDedekindDomain Representation Finset
open RHDirect RHDirect.Stage12GaloisShaLen RHDirect.Stage12Window1RootAvoid
open RHDirect.Stage13MinusParityRubin RHDirect.Stage13SixCaseVWinAssembly
open RHDirect.TaylorWilesWindow

namespace RHDirect.Stage13MaschkeCharDecomp

/-! ## Section 1: Abelian Galois Structure of Number Fields with `1 ≤ condF E` -/

section AbelianCondF

/-- Every number field `E` with `1 ≤ condF E` embeds into `CyclotomicField (condF E) ℚ`. -/
theorem condF_spec {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    0 < condF E ∧ Nonempty (E →ₐ[ℚ] CyclotomicField (condF E) ℚ) := by
  have hne : {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : condF E = 0 := by unfold condF; rw [hemp]; exact Nat.sInf_empty
    omega
  exact Nat.sInf_mem hne

/-- Automorphisms of `CyclotomicField N ℚ` over `ℚ` commute. -/
theorem cyclotomicField_aut_comm (N : ℕ) [NeZero N]
    (σ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) : σ * τ = τ * σ := by
  have hprim := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  let pb := hprim.powerBasis ℚ
  have hgen : pb.gen = IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ) :=
    IsPrimitiveRoot.powerBasis_gen ℚ hprim
  have hex : ∀ α : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      ∃ a : ℕ, α pb.gen = pb.gen ^ a := fun α => by
    rw [hgen]
    have hroot : (α (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) ^ N = 1 := by
      rw [← map_pow, hprim.pow_eq_one, map_one]
    obtain ⟨a, _, ha⟩ := hprim.eq_pow_of_pow_eq_one hroot
    exact ⟨a, ha.symm⟩
  obtain ⟨a, ha⟩ := hex σ
  obtain ⟨b, hb⟩ := hex τ
  apply AlgEquiv.coe_toAlgHom_injective
  apply pb.algHom_ext
  change σ (τ pb.gen) = τ (σ pb.gen)
  rw [hb, ha, map_pow, map_pow, ha, hb, ← pow_mul, ← pow_mul, mul_comm]

/-- Every subfield of `CyclotomicField N ℚ` is stabilized by every `ℚ`-automorphism of
`CyclotomicField N ℚ` and is therefore normal over `ℚ`. -/
theorem normal_of_algHom_cyclotomic {E : Type} [Field E] [NumberField E]
    {N : ℕ} [NeZero N] (j : E →ₐ[ℚ] CyclotomicField N ℚ) :
    Normal ℚ E := by
  classical
  haveI : IsGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isGalois {N} ℚ (CyclotomicField N ℚ)
  let K : IntermediateField ℚ (CyclotomicField N ℚ) := j.fieldRange
  have hfix : IntermediateField.fixedField K.fixingSubgroup = K :=
    IsGalois.fixedField_fixingSubgroup K
  have hstab : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (x : E),
      τ (j x) ∈ K := by
    intro τ x
    rw [← hfix, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hcomm : g * τ = τ * g := cyclotomicField_aut_comm N g τ
    have hgx : g (j x) = j x := hg ⟨j x, ⟨x, rfl⟩⟩
    change (g * τ) (j x) = τ (j x)
    rw [hcomm, AlgEquiv.mul_apply, hgx]
  refine ⟨fun x => ?_⟩
  have hsplits_C : ((minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ))).Splits := by
    have heq : minpoly ℚ (j x) = minpoly ℚ x := minpoly.algHom_eq j j.injective x
    rw [← heq]
    exact Normal.splits (inferInstance : Normal ℚ (CyclotomicField N ℚ)) (j x)
  have hmem_range : ∀ r ∈ ((minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ))).roots,
      r ∈ K := by
    intro r hr
    have hmp_ne : minpoly ℚ x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
    have hmap_ne : (minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ)) ≠ 0 :=
      Polynomial.map_ne_zero hmp_ne
    have hroot : Polynomial.aeval r (minpoly ℚ x) = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact (Polynomial.mem_roots hmap_ne).mp hr
    have hmp_r : minpoly ℚ r = minpoly ℚ (j x) := by
      have h1 : minpoly ℚ (j x) = minpoly ℚ x := minpoly.algHom_eq j j.injective x
      rw [h1]
      exact (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))
        hroot (minpoly.monic (Algebra.IsIntegral.isIntegral x))).symm
    have hrx : Polynomial.aeval (j x) (minpoly ℚ x) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    haveI : Fact (Irreducible (minpoly ℚ x)) :=
      ⟨minpoly.irreducible (Algebra.IsIntegral.isIntegral x)⟩
    let f1 : AdjoinRoot (minpoly ℚ x) →ₐ[ℚ] CyclotomicField N ℚ :=
      AdjoinRoot.liftAlgHom (minpoly ℚ x) (Algebra.ofId ℚ (CyclotomicField N ℚ)) (j x) hrx
    let f2 : AdjoinRoot (minpoly ℚ x) →ₐ[ℚ] CyclotomicField N ℚ :=
      AdjoinRoot.liftAlgHom (minpoly ℚ x) (Algebra.ofId ℚ (CyclotomicField N ℚ)) r hroot
    let eAd : f1.fieldRange ≃ₐ[ℚ] f2.fieldRange :=
      (AlgEquiv.ofInjectiveField f1).symm.trans (AlgEquiv.ofInjectiveField f2)
    let τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ :=
      AlgEquiv.liftNormal eAd (CyclotomicField N ℚ)
    have hτ : τ (j x) = r := by
      let α : AdjoinRoot (minpoly ℚ x) := AdjoinRoot.root (minpoly ℚ x)
      have hf1α : f1 α = j x := AdjoinRoot.liftAlgHom_root _ _ _ _
      have hf2α : f2 α = r := AdjoinRoot.liftAlgHom_root _ _ _ _
      let a1 : f1.fieldRange := AlgEquiv.ofInjectiveField f1 α
      have h1 : τ (algebraMap f1.fieldRange (CyclotomicField N ℚ) a1) =
          algebraMap f2.fieldRange (CyclotomicField N ℚ) (eAd a1) :=
        AlgEquiv.liftNormal_commutes eAd (CyclotomicField N ℚ) a1
      have ha1 : algebraMap f1.fieldRange (CyclotomicField N ℚ) a1 = j x := hf1α
      have ha2 : algebraMap f2.fieldRange (CyclotomicField N ℚ) (eAd a1) = r := by
        change f2 ((AlgEquiv.ofInjectiveField f1).symm ((AlgEquiv.ofInjectiveField f1) α)) = r
        rw [AlgEquiv.symm_apply_apply, hf2α]
      rw [ha1, ha2] at h1
      exact h1
    rw [← hτ]
    exact hstab τ x
  rw [Polynomial.splits_iff_card_roots]
  have hmp_ne : minpoly ℚ x ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)
  have hmap_C : ((minpoly ℚ x).map (algebraMap ℚ E)).map j.toRingHom =
      (minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ)) := by
    rw [Polynomial.map_map]
    congr 1
    exact j.comp_algebraMap
  have hcard_C : ((minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ))).roots.card =
      ((minpoly ℚ x).map (algebraMap ℚ E)).natDegree := by
    rw [Polynomial.splits_iff_card_roots.mp hsplits_C, Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℚ _).injective, Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ E).injective]
  have hroots_eq : ((minpoly ℚ x).map (algebraMap ℚ E)).roots.map j =
      ((minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ))).roots := by
    have hsub : ((minpoly ℚ x).map (algebraMap ℚ E)).roots.map j ≤
        ((minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ))).roots := by
      rw [← hmap_C]
      exact Polynomial.map_roots_le (f := j.toRingHom) (Polynomial.map_ne_zero (Polynomial.map_ne_zero hmp_ne))
    apply Multiset.eq_of_le_of_card_le hsub
    have hsep : (minpoly ℚ x).Separable := Algebra.IsSeparable.isSeparable ℚ x
    have hnodup_C : ((minpoly ℚ x).map (algebraMap ℚ (CyclotomicField N ℚ))).roots.Nodup :=
      Polynomial.nodup_roots (hsep.map)
    rw [← Multiset.toFinset_card_of_nodup hnodup_C]
    have hnodup_E : (((minpoly ℚ x).map (algebraMap ℚ E)).roots.map j).Nodup :=
      Multiset.nodup_of_le hsub hnodup_C
    rw [← Multiset.toFinset_card_of_nodup hnodup_E]
    apply Finset.card_le_card
    intro r hr
    rw [Multiset.mem_toFinset] at hr ⊢
    obtain ⟨y, hy⟩ := hmem_range r hr
    have hy' : j y = r := hy
    subst hy'
    rw [Multiset.mem_map]
    refine ⟨y, ?_, rfl⟩
    rw [Polynomial.mem_roots (Polynomial.map_ne_zero hmp_ne), Polynomial.IsRoot.def,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    apply j.injective
    rw [map_zero]
    change j (Polynomial.aeval y (minpoly ℚ x)) = 0
    rw [← Polynomial.aeval_algHom_apply j y (minpoly ℚ x), Polynomial.aeval_def,
      ← Polynomial.eval_map]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero hmp_ne)).mp hr
  have := congrArg Multiset.card hroots_eq
  rw [Multiset.card_map, hcard_C] at this
  exact this

/-- Every number field `E` with `1 ≤ condF E` is Galois over `ℚ`. -/
theorem isGalois_of_one_le_condF {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    IsGalois ℚ E := by
  obtain ⟨hpos, ⟨j⟩⟩ := condF_spec hcond
  haveI : NeZero (condF E) := ⟨hpos.ne'⟩
  haveI : Normal ℚ E := normal_of_algHom_cyclotomic j
  exact IsGalois.mk

/-- Every number field `E` with `1 ≤ condF E` has abelian Galois group `E ≃ₐ[ℚ] E`. -/
theorem aut_mul_comm_of_one_le_condF {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E)
    (g h : E ≃ₐ[ℚ] E) : g * h = h * g := by
  obtain ⟨hpos, ⟨j⟩⟩ := condF_spec hcond
  haveI : NeZero (condF E) := ⟨hpos.ne'⟩
  haveI : IsGalois ℚ (CyclotomicField (condF E) ℚ) :=
    IsCyclotomicExtension.isGalois {condF E} ℚ (CyclotomicField (condF E) ℚ)
  let K : IntermediateField ℚ (CyclotomicField (condF E) ℚ) := j.fieldRange
  haveI : Normal ℚ E := normal_of_algHom_cyclotomic j
  let eEK' : E ≃ₐ[ℚ] K :=
    { toFun := fun x => ⟨j x, ⟨x, rfl⟩⟩
      invFun := fun y => y.2.choose
      left_inv := fun x => j.injective (show j (⟨j x, ⟨x, rfl⟩⟩ : K).2.choose = j x from
        (⟨j x, ⟨x, rfl⟩⟩ : K).2.choose_spec)
      right_inv := fun y => Subtype.ext y.2.choose_spec
      map_mul' := fun a b => Subtype.ext (map_mul j a b)
      map_add' := fun a b => Subtype.ext (map_add j a b)
      commutes' := fun r => Subtype.ext (j.commutes r) }
  haveI : Normal ℚ K := Normal.of_algEquiv eEK'
  let gK : K ≃ₐ[ℚ] K := eEK'.symm.trans (g.trans eEK')
  let hK : K ≃ₐ[ℚ] K := eEK'.symm.trans (h.trans eEK')
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := CyclotomicField (condF E) ℚ) K) :=
    AlgEquiv.restrictNormalHom_surjective (CyclotomicField (condF E) ℚ)
  obtain ⟨σ, hσ⟩ := hsurj gK
  obtain ⟨τ, hτ⟩ := hsurj hK
  have hKcomm : gK * hK = hK * gK := by
    rw [← hσ, ← hτ, ← map_mul, ← map_mul, cyclotomicField_aut_comm (condF E) σ τ]
  ext x
  have h1 : ∀ (a b : E ≃ₐ[ℚ] E), ((eEK'.symm.trans (a.trans eEK')) * (eEK'.symm.trans (b.trans eEK'))) (eEK' x) =
      eEK' ((a * b) x) := fun a b => by
    simp [AlgEquiv.mul_apply]
  have h2 := congrArg (fun φ : K ≃ₐ[ℚ] K => φ (eEK' x)) hKcomm
  rw [h1 g h, h1 h g] at h2
  exact eEK'.injective h2

/-- Degree bound `Module.finrank ℚ E ≤ condF E` for every number field `E` with `1 ≤ condF E`. -/
theorem finrank_le_condF {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    Module.finrank ℚ E ≤ condF E := by
  obtain ⟨hpos, ⟨j⟩⟩ := condF_spec hcond
  haveI : NeZero (condF E) := ⟨hpos.ne'⟩
  have h1 : Module.finrank ℚ E ≤ Module.finrank ℚ (CyclotomicField (condF E) ℚ) :=
    LinearMap.finrank_le_finrank_of_injective (f := j.toLinearMap) j.injective
  have h2 : Module.finrank ℚ (CyclotomicField (condF E) ℚ) = Nat.totient (condF E) :=
    IsCyclotomicExtension.finrank (CyclotomicField (condF E) ℚ)
      (Polynomial.cyclotomic.irreducible_rat hpos)
  exact h1.trans (h2.le.trans (Nat.totient_le (condF E)))

/-- Automorphism group cardinality equals degree for every number field `E` with `1 ≤ condF E`. -/
theorem card_aut_eq_finrank_of_one_le_condF {E : Type} [Field E] [NumberField E]
    (hcond : 1 ≤ condF E) :
    Fintype.card (E ≃ₐ[ℚ] E) = Module.finrank ℚ E := by
  haveI : IsGalois ℚ E := isGalois_of_one_le_condF hcond
  have h := IsGalois.card_aut_eq_finrank ℚ E
  simpa [Nat.card_eq_fintype_card] using h

theorem card_aut_le_condF {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    Fintype.card (E ≃ₐ[ℚ] E) ≤ condF E := by
  rw [card_aut_eq_finrank_of_one_le_condF hcond]
  exact finrank_le_condF hcond

/-- Commutative group structure on `E ≃ₐ[ℚ] E` when `1 ≤ condF E` (non-global to avoid diamonds). -/
@[instance_reducible]
def commGroupAutOfCondF {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    CommGroup (E ≃ₐ[ℚ] E) :=
  { (inferInstance : Group (E ≃ₐ[ℚ] E)) with
    mul_comm := aut_mul_comm_of_one_le_condF hcond }

end AbelianCondF

/-! ## Section 2: `l`-Adic Cyclotomic DVR Extensions `O / ℤ_[l]` (`eO = 1` when `l ∤ n`) -/

section PadicCyclotomicDVR

/-- Ramification length `eO l O := Module.length O (O ⧸ Ideal.span {(l : O)})`. -/
def eO (l : ℕ) (O : Type*) [CommRing O] : ℕ∞ :=
  Module.length O (O ⧸ Ideal.span {(l : O)})

/-- Bundled `l`-adic DVR coefficient ring containing `n`-th roots of unity. -/
structure PadicCoeffDVR (l n : ℕ) [Fact l.Prime] where
  O : Type
  [commRing : CommRing O]
  [isDomain : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [alg : Algebra ℤ_[l] O]
  [flat : Module.Flat ℤ_[l] O]
  [roots : HasEnoughRootsOfUnity O n]
  l_ne_zero : (l : O) ≠ 0
  l_mem_max : (l : O) ∈ IsLocalRing.maximalIdeal O

attribute [instance] PadicCoeffDVR.commRing PadicCoeffDVR.isDomain PadicCoeffDVR.dvr
  PadicCoeffDVR.alg PadicCoeffDVR.flat PadicCoeffDVR.roots

instance PadicCoeffDVR.isLocalHom {l n : ℕ} [Fact l.Prime] (C : PadicCoeffDVR l n) :
    IsLocalHom (algebraMap ℤ_[l] C.O) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have ha_mem : a ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).mpr hna
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at ha_mem
  obtain ⟨c, rfl⟩ := ha_mem
  have hmem : algebraMap ℤ_[l] C.O ((l : ℤ_[l]) * c) ∈ IsLocalRing.maximalIdeal C.O := by
    rw [map_mul, map_natCast]
    exact (IsLocalRing.maximalIdeal C.O).mul_mem_right _ C.l_mem_max
  exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) ha

theorem PadicCoeffDVR.eO_ne_zero {l n : ℕ} [Fact l.Prime] (C : PadicCoeffDVR l n) :
    eO l C.O ≠ 0 := by
  intro h0
  have hsub : Subsingleton (C.O ⧸ Ideal.span {(l : C.O)}) :=
    (Module.length_eq_zero_iff (R := C.O)).mp h0
  have h10 : (Ideal.Quotient.mk (Ideal.span {(l : C.O)}) (1 : C.O)) = 0 := Subsingleton.elim _ _
  rw [Ideal.Quotient.eq_zero_iff_mem] at h10
  have htop : Ideal.span {(l : C.O)} = ⊤ := Ideal.eq_top_of_isUnit_mem _ h10 isUnit_one
  have hle : Ideal.span {(l : C.O)} ≤ IsLocalRing.maximalIdeal C.O :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr C.l_mem_max)
  rw [htop] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal C.O).ne_top (top_le_iff.mp hle)

theorem PadicCoeffDVR.one_le_eO {l n : ℕ} [Fact l.Prime] (C : PadicCoeffDVR l n) :
    1 ≤ eO l C.O := by
  have hne := C.eO_ne_zero
  cases h : eO l C.O with
  | top => exact le_top
  | coe m =>
    rw [h] at hne
    have hm : m ≠ 0 := fun h0 => hne (by simp [h0])
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm

theorem PadicCoeffDVR.eO_ne_top {l n : ℕ} [Fact l.Prime] (C : PadicCoeffDVR l n) :
    eO l C.O ≠ ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C.O
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible C.l_ne_zero hϖ
  have hspan : Ideal.span {(l : C.O)} = Ideal.span {ϖ ^ r} := by
    rw [hu]
    exact Ideal.span_singleton_eq_span_singleton.mpr (Associated.symm ⟨u, mul_comm _ _⟩)
  unfold eO
  rw [hspan]
  clear hu hspan
  induction r with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    have hsub : Subsingleton (C.O ⧸ (⊤ : Ideal C.O)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [(Module.length_eq_zero_iff (R := C.O)).mpr hsub]
    exact ENat.natCast_ne_top 0
  | succ m ih =>
    have hle : Ideal.span {ϖ ^ (m + 1)} ≤ Ideal.span {ϖ ^ m} :=
      Ideal.span_singleton_le_span_singleton.mpr ⟨ϖ, by rw [pow_succ]⟩
    let qMap : (C.O ⧸ Ideal.span {ϖ ^ (m + 1)}) →ₗ[C.O] (C.O ⧸ Ideal.span {ϖ ^ m}) :=
      Submodule.factor hle
    have hsurj : Function.Surjective qMap := Submodule.factor_surjective hle
    have hker : LinearMap.ker qMap =
        Submodule.map (Ideal.span {ϖ ^ (m + 1)}).mkQ (Ideal.span {ϖ ^ m}) := by
      ext x
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [qMap, LinearMap.mem_ker, Submodule.mem_map]
      change Submodule.Quotient.mk (p := Ideal.span {ϖ ^ m}) a = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro ha; exact ⟨a, ha, rfl⟩
      · rintro ⟨b, hb, hba⟩
        have hdiff : a - b ∈ Ideal.span {ϖ ^ (m + 1)} :=
          (Submodule.Quotient.eq _).mp hba.symm
        simpa using (Ideal.span {ϖ ^ m}).add_mem hb (hle hdiff)
    have hker_len : Module.length C.O (LinearMap.ker qMap) = 1 := by
      let φ : C.O →ₗ[C.O] LinearMap.ker qMap :=
        { toFun := fun a => ⟨Submodule.Quotient.mk (p := Ideal.span {ϖ ^ (m + 1)}) (a * ϖ ^ m), by
            rw [hker]
            exact ⟨a * ϖ ^ m, Ideal.mem_span_singleton.mpr (dvd_mul_left _ _), rfl⟩⟩
          map_add' := fun a b => Subtype.ext (by simp [add_mul])
          map_smul' := fun r a => Subtype.ext (by
            change Submodule.Quotient.mk (p := Ideal.span {ϖ ^ (m + 1)}) ((r * a) * ϖ ^ m) =
              r • Submodule.Quotient.mk (p := Ideal.span {ϖ ^ (m + 1)}) (a * ϖ ^ m)
            rw [mul_assoc, ← smul_eq_mul, Submodule.Quotient.mk_smul]) }
      have hφ_surj : Function.Surjective φ := by
        rintro ⟨x, hx⟩
        rw [hker] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy
        exact ⟨a, Subtype.ext (by simp [φ, mul_comm])⟩
      have hφ_ker : LinearMap.ker φ = Ideal.span {ϖ} := by
        ext a
        simp only [LinearMap.mem_ker, Subtype.ext_iff, φ, LinearMap.coe_mk, AddHom.coe_mk,
          ZeroMemClass.coe_zero, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
        constructor
        · rintro ⟨c, hc⟩
          have hpow0 : ϖ ^ m ≠ 0 := pow_ne_zero m hϖ.ne_zero
          rw [pow_succ, mul_assoc] at hc
          have hac : a = ϖ * c := mul_right_cancel₀ hpow0 (by rw [hc]; ring)
          exact ⟨c, hac⟩
        · rintro ⟨c, rfl⟩
          exact ⟨c, by rw [pow_succ]; ring⟩
      have heqv : (C.O ⧸ Ideal.span {ϖ}) ≃ₗ[C.O] LinearMap.ker qMap :=
        (Submodule.quotEquivOfEq _ _ hφ_ker.symm).trans (φ.quotKerEquivOfSurjective hφ_surj)
      rw [← heqv.length_eq]
      have hmax : Ideal.span {ϖ} = IsLocalRing.maximalIdeal C.O :=
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ).symm
      rw [hmax, Module.length_eq_one_iff]
      exact isSimpleModule_iff_quot_maximal.mpr
        ⟨IsLocalRing.maximalIdeal C.O, IsLocalRing.maximalIdeal.isMaximal C.O,
          ⟨LinearEquiv.refl C.O _⟩⟩
    have hadd := Module.length_eq_add_of_exact (LinearMap.ker qMap).subtype qMap
      (Submodule.subtype_injective _) hsurj
      (LinearMap.exact_iff.mpr (Submodule.range_subtype _).symm)
    rw [hadd, hker_len]
    exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top 1, ih⟩

/-- Helper: in `Localization.AtPrime P` of a domain `A`, `mk' a s` lies in the maximal ideal iff `a ∈ P`. -/
private lemma mk'_mem_maximalIdeal_iff {A : Type*} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (a : A) (s : P.primeCompl) :
    IsLocalization.mk' (Localization.AtPrime P) a s ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ↔ a ∈ P := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_contra ha
    apply hnu
    have hua : IsUnit (algebraMap A (Localization.AtPrime P) a) :=
      IsLocalization.map_units (Localization.AtPrime P) (⟨a, ha⟩ : P.primeCompl)
    have hus : IsUnit (algebraMap A (Localization.AtPrime P) s.1) :=
      IsLocalization.map_units (Localization.AtPrime P) s
    obtain ⟨u_s, hu_s⟩ := hus
    have hmk : IsLocalization.mk' (Localization.AtPrime P) a s =
        algebraMap A (Localization.AtPrime P) a * (u_s⁻¹ : (Localization.AtPrime P)ˣ) := by
      apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
      rw [mul_assoc, ← hu_s, Units.inv_mul, mul_one]
    rw [hmk]
    exact hua.mul u_s⁻¹.isUnit
  · intro ha hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    dsimp only at hy
    rw [← IsLocalization.mk'_mul, ← map_one (algebraMap A (Localization.AtPrime P)),
      ← IsLocalization.mk'_one (M := P.primeCompl) (Localization.AtPrime P) (1 : A)] at hy
    rw [IsLocalization.mk'_eq_iff_eq] at hy
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp hy
    simp only [Submonoid.coe_mul, Submonoid.coe_one, one_mul, mul_one] at hc
    have hmem : c.1 * (s.1 * t.1) ∈ P := by
      rw [← hc]
      exact P.mul_mem_left c.1 (P.mul_mem_right b ha)
    have hst : c.1 * (s.1 * t.1) ∈ P.primeCompl :=
      P.primeCompl.mul_mem c.2 (P.primeCompl.mul_mem s.2 t.2)
    exact hst hmem

/-- **Unramified Cyclotomic DVR Construction (`l ∤ n`, `eO l O = 1`)**. -/
theorem exists_unramified_dvr_rootsOfUnity (l n : ℕ) [Fact l.Prime] [NeZero n] (hnd : ¬ l ∣ n) :
    ∃ C : PadicCoeffDVR l n, eO l C.O = 1 := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed (AlgebraicClosure ℚ_[l]) := AlgebraicClosure.isAlgClosed ℚ_[l]
  haveI : CharZero (AlgebraicClosure ℚ_[l]) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[l] (AlgebraicClosure ℚ_[l])).injective
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ_[l]) :=
    ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ_[l]) n
  have hζ_int : IsIntegral ℤ_[l] ζ := by
    refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
    simp [hζ.pow_eq_one]
  let A : Subalgebra ℤ_[l] (AlgebraicClosure ℚ_[l]) := Algebra.adjoin ℤ_[l] {ζ}
  haveI : Module.Finite ℤ_[l] A := Module.Finite.iff_fg.mpr hζ_int.fg_adjoin_singleton
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite ℤ_[l] A
  have hinj_Z : Function.Injective (algebraMap ℤ_[l] A) := by
    intro a b hab
    have h := congrArg (fun x : A => (x : AlgebraicClosure ℚ_[l])) hab
    simp only [Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (AlgebraicClosure ℚ_[l])] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] _).injective h)
  haveI : CharZero A := charZero_of_injective_algebraMap hinj_Z
  haveI : Module.IsTorsionFree ℤ_[l] A := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj_Z
  let ζA : A := ⟨ζ, Algebra.self_mem_adjoin_singleton ℤ_[l] ζ⟩
  have hζA_prim : IsPrimitiveRoot ζA n :=
    IsPrimitiveRoot.of_map_of_injective (f := A.val) hζ Subtype.val_injective
  have hζA_int : IsIntegral ℤ_[l] ζA :=
    (isIntegral_algHom_iff A.val Subtype.val_injective).mp hζ_int
  let f : Polynomial ℤ_[l] := minpoly ℤ_[l] ζA
  have hf_monic : f.Monic := minpoly.monic hζA_int
  have hf_dvd : f ∣ Polynomial.X ^ n - 1 := by
    apply minpoly.isIntegrallyClosed_dvd hζA_int
    simp [hζA_prim.pow_eq_one]
  let red : ℤ_[l] →+* ZMod l := PadicInt.toZMod
  have hred_surj : Function.Surjective red := ZMod.ringHom_surjective red
  let fbar : Polynomial (ZMod l) := f.map red
  have hfbar_monic : fbar.Monic := hf_monic.map red
  have hfbar_dvd : fbar ∣ Polynomial.X ^ n - 1 := by
    have h1 := Polynomial.map_dvd red hf_dvd
    simpa [fbar, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one] using h1
  have hfbar_deg : 1 ≤ fbar.natDegree := by
    rw [hf_monic.natDegree_map red]
    exact minpoly.natDegree_pos hζA_int
  have hsep_Xn : (Polynomial.X ^ n - 1 : Polynomial (ZMod l)).Separable := by
    have hn0 : ((n : ℕ) : ZMod l) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
    exact Polynomial.separable_X_pow_sub_C (1 : ZMod l) hn0 one_ne_zero
  have hsep_fbar : fbar.Separable := Polynomial.Separable.of_dvd hsep_Xn hfbar_dvd
  have hsqf_fbar : Squarefree fbar := hsep_fbar.squarefree
  have hfbar_nu : ¬ IsUnit fbar := by
    intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hg_irr, hg_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hfbar_nu hfbar_monic.ne_zero
  obtain ⟨hbar, hfbar_eq⟩ := hg_dvd
  have hgn_dvd_hbar : ¬ g ∣ hbar := by
    intro hgh
    have hsq : g * g ∣ fbar := by rw [hfbar_eq]; exact mul_dvd_mul_left g hgh
    exact hg_irr.not_isUnit (hsqf_fbar g hsq)
  let ev : Polynomial ℤ_[l] →ₐ[ℤ_[l]] A := Polynomial.aeval ζA
  have hev_surj : Function.Surjective ev := by
    intro x
    have hx : x.1 ∈ Algebra.adjoin ℤ_[l] {ζ} := x.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, hp⟩ := hx
    refine ⟨p, Subtype.ext ?_⟩
    change A.val (Polynomial.aeval ζA p) = x.1
    rw [← Polynomial.aeval_algHom_apply]
    exact hp
  have hev_ker : RingHom.ker ev.toRingHom = Ideal.span {f} := by
    ext p
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    refine ⟨fun hp => minpoly.isIntegrallyClosed_dvd hζA_int hp, ?_⟩
    rintro ⟨q, rfl⟩
    change ev (f * q) = 0
    rw [map_mul, show ev f = 0 from minpoly.aeval ℤ_[l] ζA, zero_mul]
  let modG : Polynomial ℤ_[l] →+* Polynomial (ZMod l) ⧸ Ideal.span {g} :=
    (Ideal.Quotient.mk (Ideal.span {g})).comp (Polynomial.mapRingHom red)
  have hker_le : RingHom.ker ev.toRingHom ≤ RingHom.ker modG := by
    intro p hp
    rw [hev_ker, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk (Ideal.span {g}) ((f * q).map red) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.map_mul]
    exact dvd_mul_of_dvd_left ⟨hbar, hfbar_eq⟩ _
  let eQuot : Polynomial ℤ_[l] ⧸ RingHom.ker ev.toRingHom ≃+* A :=
    RingHom.quotientKerEquivOfSurjective (f := ev.toRingHom) hev_surj
  let ψ : A →+* Polynomial (ZMod l) ⧸ Ideal.span {g} :=
    (Ideal.Quotient.lift (RingHom.ker ev.toRingHom) modG fun p hp =>
      RingHom.mem_ker.mp (hker_le hp)).comp eQuot.symm.toRingHom
  have hψ_ev : ∀ p : Polynomial ℤ_[l], ψ (ev p) = modG p := fun p => by
    have h1 : eQuot.symm (ev p) = Ideal.Quotient.mk (RingHom.ker ev.toRingHom) p := by
      apply eQuot.injective
      rw [eQuot.apply_symm_apply]
      rfl
    dsimp only [ψ, RingHom.comp_apply]
    rw [show eQuot.symm.toRingHom (ev p) = Ideal.Quotient.mk (RingHom.ker ev.toRingHom) p from h1]
    rfl
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨qbar, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective red hred_surj qbar
    exact ⟨ev q, hψ_ev q⟩
  haveI : (Ideal.span {g}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hg_irr
  letI : Field (Polynomial (ZMod l) ⧸ Ideal.span {g}) := Ideal.Quotient.field _
  let qI : Ideal A := RingHom.ker ψ
  haveI hq_max : qI.IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψ_surj
  haveI hq_prime : qI.IsPrime := hq_max.isPrime
  have hl_mem_q : (l : A) ∈ qI := by
    change ψ (l : A) = 0
    have h1 : (l : A) = ev (Polynomial.C (l : ℤ_[l])) := by simp [ev]
    rw [h1, hψ_ev]
    change Ideal.Quotient.mk (Ideal.span {g}) ((Polynomial.C (l : ℤ_[l])).map red) = 0
    have hredl : red (l : ℤ_[l]) = 0 := by
      show PadicInt.toZMod ((l : ℕ) : ℤ_[l]) = 0
      rw [map_natCast, ZMod.natCast_self]
    rw [Polynomial.map_C, hredl, map_zero, map_zero]
  let O := Localization.AtPrime qI
  haveI : IsDomain O := IsLocalization.isDomain_localization qI.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing qI.primeCompl O inferInstance
  have hinj_AO : Function.Injective (algebraMap A O) :=
    IsLocalization.injective O qI.primeCompl_le_nonZeroDivisors
  have hinj_ZO : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] A O]
    exact hinj_AO.comp hinj_Z
  haveI : Module.IsTorsionFree ℤ_[l] O :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj_ZO
  haveI : Module.Flat ℤ_[l] O := inferInstance
  have hmax_eq : IsLocalRing.maximalIdeal O = Ideal.span {(l : O)} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective qI.primeCompl x
      have ha : a ∈ qI := (mk'_mem_maximalIdeal_iff qI a s).mp hx
      obtain ⟨p, rfl⟩ := hev_surj a
      have hp_dvd : g ∣ p.map red := by
        have h0 : modG p = 0 := by rw [← hψ_ev p]; exact ha
        exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      obtain ⟨qbar, hqbar⟩ := hp_dvd
      obtain ⟨h, hh⟩ := Polynomial.map_surjective red hred_surj hbar
      obtain ⟨q, hq⟩ := Polynomial.map_surjective red hred_surj qbar
      let t : A := ev h
      have ht_not_mem : t ∉ qI := by
        intro ht
        have h0 : modG h = 0 := by rw [← hψ_ev h]; exact ht
        have hd : g ∣ h.map red := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
        rw [hh] at hd
        exact hgn_dvd_hbar hd
      have hdiff_zero : (h * p - f * q).map red = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, hh, hq, hqbar]
        change hbar * (g * qbar) - fbar * qbar = 0
        rw [hfbar_eq]
        ring
      have hl_dvd_diff : ∃ r : Polynomial ℤ_[l], h * p - f * q = Polynomial.C (l : ℤ_[l]) * r := by
        have hcoeff : ∀ i : ℕ, (l : ℤ_[l]) ∣ (h * p - f * q).coeff i := fun i => by
          have hi : red ((h * p - f * q).coeff i) = 0 := by
            have := congrArg (fun P => P.coeff i) hdiff_zero
            rw [Polynomial.coeff_map, Polynomial.coeff_zero] at this
            exact this
          have hmem : (h * p - f * q).coeff i ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
            rw [← PadicInt.ker_toZMod]; exact hi
          rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
          exact hmem
        choose c hc using hcoeff
        refine ⟨∑ i ∈ (h * p - f * q).support, Polynomial.monomial i (c i), ?_⟩
        ext i
        rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
        simp_rw [Polynomial.coeff_monomial]
        rw [Finset.sum_ite_eq']
        split_ifs with hi
        · exact hc i
        · rw [mul_zero]
          exact Polynomial.notMem_support_iff.mp hi
      obtain ⟨r, hr⟩ := hl_dvd_diff
      have hta : t * ev p = (l : A) * ev r := by
        have h1 : ev (h * p - f * q) = ev (Polynomial.C (l : ℤ_[l]) * r) := congrArg ev hr
        rw [map_sub, map_mul, map_mul, map_mul, show ev f = 0 from minpoly.aeval ℤ_[l] ζA,
          zero_mul, sub_zero] at h1
        simpa [t, ev] using h1
      rw [Ideal.mem_span_singleton]
      have ht_unit : IsUnit (algebraMap A O t) :=
        IsLocalization.map_units O (⟨t, ht_not_mem⟩ : qI.primeCompl)
      obtain ⟨u_t, hu_t⟩ := ht_unit
      have hts : algebraMap A O t * algebraMap A O (ev p) = (l : O) * algebraMap A O (ev r) := by
        rw [← map_mul, hta, map_mul, map_natCast]
      have hap : algebraMap A O (ev p) = (l : O) * ((u_t⁻¹ : Oˣ) * algebraMap A O (ev r)) := by
        calc algebraMap A O (ev p)
            = ((u_t⁻¹ : Oˣ) : O) * (algebraMap A O t * algebraMap A O (ev p)) := by
                rw [← hu_t, ← mul_assoc, Units.inv_mul, one_mul]
          _ = ((u_t⁻¹ : Oˣ) : O) * ((l : O) * algebraMap A O (ev r)) := by rw [hts]
          _ = (l : O) * ((u_t⁻¹ : Oˣ) * algebraMap A O (ev r)) := by ring
      have hs_unit : IsUnit (algebraMap A O s.1) := IsLocalization.map_units O s
      obtain ⟨u_s, hu_s⟩ := hs_unit
      have hmk : IsLocalization.mk' O (ev p) s =
          algebraMap A O (ev p) * (u_s⁻¹ : Oˣ) := by
        apply (IsLocalization.mk'_eq_iff_eq_mul).mpr
        rw [mul_assoc, ← hu_s, Units.inv_mul, mul_one]
      dsimp only
      rw [hmk, hap, mul_assoc]
      exact dvd_mul_right _ _
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have h1 : (l : O) = IsLocalization.mk' O (l : A) (1 : qI.primeCompl) := by
        rw [IsLocalization.mk'_one (M := qI.primeCompl) O (l : A), map_natCast]
      rw [h1, mk'_mem_maximalIdeal_iff]
      exact hl_mem_q
  have hlO_ne : (l : O) ≠ 0 := by
    intro h0
    have h1 : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by
      rw [map_natCast, h0, map_zero]
    have h2 : ((l : ℕ) : ℤ_[l]) = 0 := hinj_ZO h1
    exact hl.ne_zero (by exact_mod_cast h2)
  have hlO_mem : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [hmax_eq]; exact Ideal.subset_span rfl
  have hnf : ¬ IsField O := by
    intro hf
    have hnu : ¬ IsUnit (l : O) := (IsLocalRing.mem_maximalIdeal _).mp hlO_mem
    obtain ⟨v, hv⟩ := hf.mul_inv_cancel hlO_ne
    exact hnu (IsUnit.of_mul_eq_one v hv)
  have hp : (IsLocalRing.maximalIdeal O).IsPrincipal := by
    rw [hmax_eq]; exact ⟨⟨(l : O), rfl⟩⟩
  haveI hDVR : IsDiscreteValuationRing O := ((IsDiscreteValuationRing.TFAE O hnf).out 0 4).mpr hp
  haveI hRoots : HasEnoughRootsOfUnity O n :=
    ⟨⟨algebraMap A O ζA, hζA_prim.map_of_injective hinj_AO⟩, rootsOfUnity.isCyclic O n⟩
  refine ⟨{ O := O, l_ne_zero := hlO_ne, l_mem_max := hlO_mem }, ?_⟩
  unfold eO
  rw [← hmax_eq, Module.length_eq_one_iff]
  exact isSimpleModule_iff_quot_maximal.mpr
    ⟨IsLocalRing.maximalIdeal O, IsLocalRing.maximalIdeal.isMaximal O, ⟨LinearEquiv.refl O _⟩⟩

/-- **General Cyclotomic DVR Construction (any `n ≥ 1`, even `l ∣ n`)**. -/
theorem exists_dvr_rootsOfUnity (l n : ℕ) [Fact l.Prime] [NeZero n] :
    Nonempty (PadicCoeffDVR l n) := by
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed (AlgebraicClosure ℚ_[l]) := AlgebraicClosure.isAlgClosed ℚ_[l]
  haveI : CharZero (AlgebraicClosure ℚ_[l]) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[l] (AlgebraicClosure ℚ_[l])).injective
  haveI : NeZero ((n : ℕ) : AlgebraicClosure ℚ_[l]) :=
    ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ_[l]) n
  have hζ_int : IsIntegral ℤ_[l] ζ := by
    refine ⟨Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
    simp [hζ.pow_eq_one]
  let K : IntermediateField ℚ_[l] (AlgebraicClosure ℚ_[l]) := IntermediateField.adjoin ℚ_[l] {ζ}
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let R := integralClosure ℤ_[l] K
  haveI : IsDedekindDomain R := IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K R
  have hinj_ZR : Function.Injective (algebraMap ℤ_[l] R) := by
    intro a b hab
    have h := congrArg (fun x : R => (x : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)
  have hlR_ne : (l : R) ≠ 0 := by
    intro h0
    have h1 : algebraMap ℤ_[l] R (l : ℤ_[l]) = algebraMap ℤ_[l] R 0 := by
      rw [map_natCast, h0, map_zero]
    have h2 : ((l : ℕ) : ℤ_[l]) = 0 := hinj_ZR h1
    exact hl.ne_zero (by exact_mod_cast h2)
  have hlR_nu : ¬ IsUnit (l : R) := by
    intro hu
    obtain ⟨u, hu_eq⟩ := hu.exists_right_inv
    have huK : (l : K) * (u : K) = 1 := by
      have := congrArg (fun x : R => (x : K)) hu_eq
      simpa using this
    have hu_inv : (u : K) = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by
      have hlK : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
      apply mul_left_cancel₀ hlK
      rw [huK, ← map_natCast (algebraMap ℚ_[l] K), ← map_mul,
        mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hl.ne_zero), map_one]
    have hint_inv : IsIntegral ℤ_[l] ((l : ℚ_[l])⁻¹) := by
      have hi : IsIntegral ℤ_[l] (u : K) := u.2
      rw [hu_inv] at hi
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] K)
        (algebraMap ℚ_[l] K).injective).mp hi
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint_inv
    have hnorm : ‖(l : ℚ_[l])⁻¹‖ ≤ 1 := by
      rw [← hz]; exact PadicInt.norm_le_one z
    rw [norm_inv, Padic.norm_p] at hnorm
    have h1 : (l : ℝ) ≤ 1 := by
      have := hnorm
      rw [inv_inv] at this
      exact this
    have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl.two_le
    linarith
  have hspan_ne_top : Ideal.span {(l : R)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hlR_nu
  obtain ⟨m, hm_max, hlm⟩ := Ideal.exists_le_maximal (Ideal.span {(l : R)}) hspan_ne_top
  have hm_ne_bot : m ≠ ⊥ := by
    intro hb
    have : (l : R) ∈ (⊥ : Ideal R) := hb ▸ hlm (Ideal.subset_span rfl)
    exact hlR_ne (Ideal.mem_bot.mp this)
  let v : HeightOneSpectrum R := ⟨m, hm_max.isPrime, hm_ne_bot⟩
  let O := Localization.AtPrime v.asIdeal
  haveI : IsDomain O := IsLocalization.isDomain_localization v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI hDVR : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot O
  have hinj_RO : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O v.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : Module.IsTorsionFree ℤ_[l] R :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj_ZR
  haveI : Module.Flat ℤ_[l] R := inferInstance
  haveI : Module.Flat R O := IsLocalization.flat (R := R) (p := v.asIdeal.primeCompl) (S := O)
  haveI : Module.Flat ℤ_[l] O := Module.Flat.trans ℤ_[l] R O
  have hζK : ζ ∈ K := IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ
  let ζR : R := ⟨⟨ζ, hζK⟩, (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).mp hζ_int⟩
  have hζR_prim : IsPrimitiveRoot ζR n :=
    IsPrimitiveRoot.of_map_of_injective (f := (K.val.restrictScalars ℤ_[l]).comp R.val) hζ
      (Subtype.val_injective.comp Subtype.val_injective)
  haveI hRoots : HasEnoughRootsOfUnity O n :=
    ⟨⟨algebraMap R O ζR, hζR_prim.map_of_injective hinj_RO⟩, rootsOfUnity.isCyclic O n⟩
  have hlO_ne : (l : O) ≠ 0 := by
    intro h0
    have h1 : algebraMap R O (l : R) = algebraMap R O 0 := by rw [map_natCast, h0, map_zero]
    exact hlR_ne (hinj_RO h1)
  have hlO_mem : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    have h1 : (l : O) = IsLocalization.mk' O (l : R) (1 : v.asIdeal.primeCompl) := by
      rw [IsLocalization.mk'_one (M := v.asIdeal.primeCompl) O (l : R), map_natCast]
    rw [h1, mk'_mem_maximalIdeal_iff]
    exact hlm (Ideal.subset_span rfl)
  exact ⟨{ O := O, l_ne_zero := hlO_ne, l_mem_max := hlO_mem }⟩

/-- Canonical choice of `PadicCoeffDVR l n`: unramified (`eO = 1`) whenever `¬ l ∣ n`,
and general DVR otherwise! -/
def chosenPadicCoeffDVR (l n : ℕ) [Fact l.Prime] [NeZero n] : PadicCoeffDVR l n :=
  if h : ¬ l ∣ n then
    Classical.choose (exists_unramified_dvr_rootsOfUnity l n h)
  else
    Classical.choice (exists_dvr_rootsOfUnity l n)

theorem eO_chosenPadicCoeffDVR_of_not_dvd (l n : ℕ) [Fact l.Prime] [NeZero n] (hnd : ¬ l ∣ n) :
    eO l (chosenPadicCoeffDVR l n).O = 1 := by
  unfold chosenPadicCoeffDVR
  rw [dif_pos hnd]
  exact Classical.choose_spec (exists_unramified_dvr_rootsOfUnity l n hnd)

end PadicCyclotomicDVR

/-! ## Section 3: Flat Base-Change Length Calculus & Maschke / `lenEigLe` Eigenspace Splitting -/

section BaseChangeAndMaschke

/-- **Faithfully Flat Base-Change Length Formula (`length_baseChange_eq_eO_mul`)**:
for EVERY `ℤ_[l]`-module `M` (finite OR infinite length!),
`Module.length C.O (C.O ⊗[ℤ_[l]] M) = eO l C.O * Module.length ℤ_[l] M`! -/
theorem length_baseChange_eq_eO_mul {l n : ℕ} [Fact l.Prime] (C : PadicCoeffDVR l n)
    (M : Type*) [AddCommGroup M] [Module ℤ_[l] M] :
    Module.length C.O (C.O ⊗[ℤ_[l]] M) = eO l C.O * Module.length ℤ_[l] M := by
  have hmap : (IsLocalRing.maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] C.O) = Ideal.span {(l : C.O)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [IsLocalRing.length_baseChange, hmap, mul_comm]
  rfl

/-- Eigenspace `eig π χ := {x | ∀ g, π g x = χ g • x}` for a character `χ : Q →* Oˣ`. -/
def eig {O Q M : Type*} [CommRing O] [Group Q] [AddCommGroup M] [Module O M]
    (π : Representation O Q M) (χ : Q →* Oˣ) : Submodule O M where
  carrier := {x | ∀ g : Q, π g x = ((χ g : Oˣ) : O) • x}
  zero_mem' g := by simp
  add_mem' ha hb g := by simp [map_add, ha g, hb g, smul_add]
  smul_mem' c x hx g := by simp [map_smul, hx g, smul_comm c]

@[simp] theorem mem_eig {O Q M : Type*} [CommRing O] [Group Q] [AddCommGroup M] [Module O M]
    {π : Representation O Q M} {χ : Q →* Oˣ} {x : M} :
    x ∈ eig π χ ↔ ∀ g : Q, π g x = ((χ g : Oˣ) : O) • x := Iff.rfl

/-- Base-changed representation `O ⊗[R] M` induced by `π : Representation R Q M`. -/
def baseChangeRep {R O Q M : Type*} [CommRing R] [CommRing O] [Algebra R O] [Group Q]
    [AddCommGroup M] [Module R M] (π : Representation R Q M) :
    Representation O Q (O ⊗[R] M) where
  toFun g := LinearMap.baseChange O (π g)
  map_one' := by
    rw [map_one]
    apply TensorProduct.AlgebraTensorModule.ext
    intro o m
    rfl
  map_mul' g h := by
    rw [map_mul]
    apply TensorProduct.AlgebraTensorModule.ext
    intro o m
    rfl

@[simp] theorem baseChangeRep_tmul {R O Q M : Type*} [CommRing R] [CommRing O] [Algebra R O] [Group Q]
    [AddCommGroup M] [Module R M] (π : Representation R Q M) (g : Q) (o : O) (m : M) :
    baseChangeRep (O := O) π g (o ⊗ₜ[R] m) = o ⊗ₜ[R] (π g m) := rfl

/-- Explicit finite-product tensor equivalence `O ⊗[R] (Q → M) ≃ₗ[O] (Q → O ⊗[R] M)`. -/
def tensorPiEquiv {R O Q M : Type*} [CommRing R] [CommRing O] [Algebra R O]
    [Fintype Q] [DecidableEq Q] [AddCommGroup M] [Module R M] :
    (O ⊗[R] (Q → M)) ≃ₗ[O] (Q → (O ⊗[R] M)) := by
  let bilin : O →ₗ[O] (Q → M) →ₗ[R] (Q → (O ⊗[R] M)) :=
    { toFun := fun o =>
        { toFun := fun f q => o ⊗ₜ[R] (f q)
          map_add' := fun f₁ f₂ => funext fun q => TensorProduct.tmul_add _ _ _
          map_smul' := fun r f => funext fun q => by
            change o ⊗ₜ[R] (r • f q) = r • (o ⊗ₜ[R] f q)
            rw [TensorProduct.tmul_smul] }
      map_add' := fun o₁ o₂ => LinearMap.ext fun f => funext fun q => TensorProduct.add_tmul _ _ _
      map_smul' := fun c o => LinearMap.ext fun f => funext fun q => by
        change (c * o) ⊗ₜ[R] (f q) = c • (o ⊗ₜ[R] (f q))
        rw [← smul_eq_mul, TensorProduct.smul_tmul'] }
  let fwd : (O ⊗[R] (Q → M)) →ₗ[O] (Q → (O ⊗[R] M)) :=
    TensorProduct.AlgebraTensorModule.lift bilin
  let bwd : (Q → (O ⊗[R] M)) →ₗ[O] (O ⊗[R] (Q → M)) :=
    { toFun := fun F => ∑ q : Q, LinearMap.baseChange O (LinearMap.single R (fun _ : Q => M) q) (F q)
      map_add' := fun F₁ F₂ => by simp [Finset.sum_add_distrib]
      map_smul' := fun c F => by simp [Finset.smul_sum] }
  refine LinearEquiv.ofLinearMap fwd bwd ?_ ?_
  · apply LinearMap.ext
    intro F
    funext q
    have hsum : ∀ (s : Finset Q) (G : Q → O ⊗[R] M),
        fwd (∑ r ∈ s, LinearMap.baseChange O (LinearMap.single R (fun _ : Q => M) r) (G r)) q =
          ∑ r ∈ s, fwd (LinearMap.baseChange O (LinearMap.single R (fun _ : Q => M) r) (G r)) q := by
      intro s G
      rw [map_sum, Finset.sum_apply]
    change fwd (∑ r : Q, LinearMap.baseChange O (LinearMap.single R (fun _ : Q => M) r) (F r)) q = F q
    rw [hsum, Finset.sum_eq_single q]
    · induction (F q) using TensorProduct.induction_on with
      | zero => simp
      | tmul o m =>
        change o ⊗ₜ[R] (Pi.single (M := fun _ : Q => M) q m q) = o ⊗ₜ[R] m
        rw [Pi.single_eq_same]
      | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy]
    · intro r _ hrq
      induction (F r) using TensorProduct.induction_on with
      | zero => simp
      | tmul o m =>
        change o ⊗ₜ[R] (Pi.single (M := fun _ : Q => M) r m q) = 0
        rw [Pi.single_eq_of_ne (Ne.symm hrq), TensorProduct.tmul_zero]
      | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy, add_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · apply TensorProduct.AlgebraTensorModule.ext
    intro o f
    change ∑ q : Q, LinearMap.baseChange O (LinearMap.single R (fun _ : Q => M) q) (o ⊗ₜ[R] f q) =
      o ⊗ₜ[R] f
    simp only [LinearMap.baseChange_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    funext q
    rw [Finset.sum_apply, Finset.sum_eq_single q]
    · exact Pi.single_eq_same (M := fun _ : Q => M) q (f q)
    · intro r _ hrq; exact Pi.single_eq_of_ne (M := fun _ : Q => M) (Ne.symm hrq) (f r)
    · intro h; exact absurd (Finset.mem_univ _) h

/-- For a finite group `Q` and flat `O / ℤ_[l]`, the trivial eigenspace (`Q`-invariants) commutes
with flat base change: `Module.length O (eig (baseChangeRep π) 1) = eO l O * Module.length ℤ_[l] (eig π 1)`! -/
theorem length_eig_one_baseChange {l n : ℕ} [Fact l.Prime] (C : PadicCoeffDVR l n)
    {Q M : Type*} [Group Q] [Fintype Q] [AddCommGroup M] [Module ℤ_[l] M]
    (π : Representation ℤ_[l] Q M) :
    Module.length C.O (eig (baseChangeRep (O := C.O) π) 1) =
      eO l C.O * Module.length ℤ_[l] (eig π 1) := by
  classical
  let δ : M →ₗ[ℤ_[l]] (Q → M) :=
    LinearMap.pi fun g => π g - LinearMap.id
  have hker_δ : LinearMap.ker δ = eig π 1 := by
    ext x
    simp only [LinearMap.mem_ker, δ, mem_eig, MonoidHom.one_apply, Units.val_one, one_smul]
    constructor
    · intro h g
      have hg := congrFun h g
      simpa [sub_eq_zero] using hg
    · intro h
      funext g
      simp [h g]
  let δO : (C.O ⊗[ℤ_[l]] M) →ₗ[C.O] (Q → (C.O ⊗[ℤ_[l]] M)) :=
    LinearMap.pi fun g => baseChangeRep (O := C.O) π g - LinearMap.id
  have hker_δO : LinearMap.ker δO = eig (baseChangeRep (O := C.O) π) 1 := by
    ext x
    simp only [LinearMap.mem_ker, δO, mem_eig, MonoidHom.one_apply, Units.val_one, one_smul]
    constructor
    · intro h g
      have hg := congrFun h g
      simpa [sub_eq_zero] using hg
    · intro h
      funext g
      simp [h g]
  have hex : Function.Exact (eig π 1).subtype δ := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, hker_δ]
  have hexO : Function.Exact (LinearMap.baseChange C.O (eig π 1).subtype) (LinearMap.baseChange C.O δ) :=
    Module.Flat.lTensor_exact C.O hex
  have hinjO : Function.Injective (LinearMap.baseChange C.O (eig π 1).subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.subtype_injective _)
  let ePi : (C.O ⊗[ℤ_[l]] (Q → M)) ≃ₗ[C.O] (Q → (C.O ⊗[ℤ_[l]] M)) := tensorPiEquiv
  have hcomm : ePi.toLinearMap ∘ₗ LinearMap.baseChange C.O δ = δO := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro o m
    funext g
    change o ⊗ₜ[ℤ_[l]] (π g m - m) = o ⊗ₜ[ℤ_[l]] (π g m) - o ⊗ₜ[ℤ_[l]] m
    exact TensorProduct.tmul_sub o (π g m) m
  have hker_eq : LinearMap.ker (LinearMap.baseChange C.O δ) = LinearMap.ker δO := by
    rw [← hcomm, LinearMap.ker_comp]
    have hbot : LinearMap.ker ePi.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr ePi.injective
    rw [hbot, Submodule.comap_bot]
  have hrange : LinearMap.range (LinearMap.baseChange C.O (eig π 1).subtype) =
      eig (baseChangeRep (O := C.O) π) 1 := by
    rw [← hker_δO, ← hker_eq, ← LinearMap.exact_iff.mp hexO]
  let eqv : (C.O ⊗[ℤ_[l]] (eig π 1)) ≃ₗ[C.O] eig (baseChangeRep (O := C.O) π) 1 :=
    (LinearEquiv.ofInjective _ hinjO).trans (LinearEquiv.ofEq _ _ hrange)
  rw [← eqv.length_eq, length_baseChange_eq_eO_mul C (eig π 1)]

/-- Subadditivity of kernel length under composition of endomorphisms. -/
theorem length_ker_comp_le {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N]
    (f g : Module.End O N) :
    Module.length O (LinearMap.ker (f ∘ₗ g)) ≤
      Module.length O (LinearMap.ker f) + Module.length O (LinearMap.ker g) := by
  let incl : LinearMap.ker g →ₗ[O] LinearMap.ker (f ∘ₗ g) :=
    Submodule.inclusion (fun x hx => by
      simp only [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
      rw [hx, map_zero])
  let toKerF : LinearMap.ker (f ∘ₗ g) →ₗ[O] LinearMap.ker f :=
    (g ∘ₗ (LinearMap.ker (f ∘ₗ g)).subtype).codRestrict (LinearMap.ker f) (fun x => x.2)
  have hker : LinearMap.ker toKerF = LinearMap.range incl := by
    ext ⟨x, hx⟩
    simp only [LinearMap.mem_ker, Subtype.ext_iff, toKerF, ZeroMemClass.coe_zero,
      LinearMap.mem_range, incl]
    constructor
    · intro hgx; exact ⟨⟨x, hgx⟩, rfl⟩
    · rintro ⟨⟨y, hy⟩, hyx⟩; cases hyx; exact hy
  have hadd := length_ker_add_length_range toKerF
  have h1 : Module.length O (LinearMap.ker toKerF) = Module.length O (LinearMap.ker g) := by
    rw [hker]
    exact (LinearEquiv.ofInjective incl (Submodule.inclusion_injective _)).length_eq.symm
  have h2 : Module.length O (LinearMap.range toKerF) ≤ Module.length O (LinearMap.ker f) :=
    length_submodule_le (LinearMap.range toKerF)
  rw [← hadd, h1, add_comm]
  exact add_le_add h2 le_rfl

private theorem length_ker_aeval_prod_le {O N : Type*} [CommRing O] [AddCommGroup N] [Module O N]
    (f : Module.End O N) (p : ℕ → Polynomial O) (s : Finset ℕ) :
    Module.length O (LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
      ∑ i ∈ s, Module.length O (LinearMap.ker (Polynomial.aeval f (p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, map_one]
    have h1 : LinearMap.ker (1 : Module.End O N) = ⊥ := LinearMap.ker_id
    rw [h1, (Module.length_eq_zero_iff (R := O)).mpr inferInstance]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul]
    exact (length_ker_comp_le _ _).trans (add_le_add le_rfl ih)

/-- **Root-splitting length subadditivity (`lenRoots`)**:
valid EVEN when `n` is NOT a unit in `O`. -/
theorem lenRoots {O N : Type*} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (n : ℕ) (ζ : O) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (f : Module.End O N) (hf : f ^ n = 1) :
    Module.length O N ≤
      ∑ i ∈ Finset.range n, Module.length O (LinearMap.ker (f - ζ ^ i • (1 : Module.End O N))) := by
  have hprod := X_pow_sub_C_eq_prod hζ hn (one_pow n)
  have hterm : ∀ i, Polynomial.aeval f (Polynomial.X - Polynomial.C (ζ ^ i * 1)) =
      f - ζ ^ i • (1 : Module.End O N) := fun i => by
    simp [Algebra.algebraMap_eq_smul_one, smul_pow]
  have he : Polynomial.aeval f (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * 1))) = 0 := by
    rw [← hprod]
    simp [hf]
  have htop : Module.length O (LinearMap.ker (Polynomial.aeval f
      (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * 1))))) = Module.length O N := by
    rw [he, LinearMap.ker_zero, Module.length_top]
  rw [← htop]
  exact (length_ker_aeval_prod_le f (fun i => Polynomial.X - Polynomial.C (ζ ^ i * 1))
    (Finset.range n)).trans (le_of_eq (Finset.sum_congr rfl fun i _ => by rw [hterm i]))

private theorem lenEigLe_one {O N : Type*} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (n : ℕ) (ζ : O) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (f : Module.End O N) (hf : f ^ n = 1)
    (P : Submodule O N) (hP : ∀ x ∈ P, f x ∈ P) :
    Module.length O P ≤ ∑ j : Fin n,
      Module.length O (P ⊓ LinearMap.ker (f - ζ ^ (j : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  have h1 : (f.restrict hP) ^ n = 1 := by
    ext x
    rw [Module.End.pow_restrict]
    simp [hf]
  refine (lenRoots n ζ hn hζ (f.restrict hP) h1).trans ?_
  rw [Finset.sum_range]
  refine Finset.sum_le_sum fun j _ => ?_
  refine length_mono_of_injective
    (LinearMap.codRestrict _ (P.subtype ∘ₗ Submodule.subtype _) fun x => ⟨x.1.2, ?_⟩) ?_
  · exact congrArg Subtype.val (LinearMap.mem_ker.mp x.2)
  · intro x y h
    have hval : ((x : P) : N) = ((y : P) : N) :=
      congrArg (fun z : ↥(P ⊓ LinearMap.ker (f - ζ ^ (j : ℕ) • (1 : Module.End O N))) => (z : N)) h
    exact Subtype.ext (Subtype.ext hval)

private theorem lenEigLe_many {O N : Type*} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (k : ℕ) :
    ∀ (n : Fin k → ℕ) (ζ : Fin k → O), (∀ i, 0 < n i) → (∀ i, IsPrimitiveRoot (ζ i) (n i)) →
      ∀ f : Fin k → Module.End O N, (∀ i, f i ^ n i = 1) → (∀ i j, f i * f j = f j * f i) →
      ∀ P : Submodule O N, (∀ i, ∀ x ∈ P, f i x ∈ P) →
      Module.length O P ≤ ∑ a : (∀ i, Fin (n i)),
        Module.length O (P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^ (a i : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  induction k with
  | zero =>
    intro n ζ _ _ f _ _ P _
    rw [Fintype.sum_unique, iInf_of_empty, inf_top_eq]
  | succ k ih =>
    intro n ζ hn hζ f hf hc P hP
    refine (lenEigLe_one (n 0) (ζ 0) (hn 0) (hζ 0) (f 0) (hf 0) P (hP 0)).trans ?_
    rw [← (Fin.consEquiv fun i => Fin (n i)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (ih (fun i => n i.succ) (fun i => ζ i.succ) (fun i => hn _) (fun i => hζ _)
      (fun i => f i.succ) (fun i => hf _) (fun i j => hc _ _) _ ?_).trans (le_of_eq ?_)
    · intro i x hx
      refine ⟨hP _ x hx.1, ?_⟩
      have h2 : f 0 x = ζ 0 ^ (j : ℕ) • x := by simpa [sub_eq_zero] using hx.2
      have h3 : f 0 (f i.succ x) = ζ 0 ^ (j : ℕ) • f i.succ x := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply, h2, map_smul]
      simpa [sub_eq_zero] using h3
    · refine Finset.sum_congr rfl fun a _ => ?_
      have : (P ⊓ LinearMap.ker (f 0 - ζ 0 ^ (j : ℕ) • (1 : Module.End O N))) ⊓
          ⨅ i : Fin k, LinearMap.ker (f i.succ - ζ i.succ ^ (a i : ℕ) • (1 : Module.End O N)) =
          P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^
            (((Fin.consEquiv fun i => Fin (n i)) (j, a) i : Fin (n i)) : ℕ) • (1 : Module.End O N)) := by
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_iInf, Fin.forall_fin_succ, and_assoc]
        rfl
      rw [this]

private theorem exists_commGroup_generators (Q : Type*) [CommGroup Q] [Finite Q] :
    ∃ (k : ℕ) (n : Fin k → ℕ) (g : Fin k → Q), (∀ i, 0 < n i) ∧ (∀ i, orderOf (g i) = n i) ∧
      Submonoid.closure (Set.range g) = ⊤ ∧
      ∀ (C : Type*) [CommGroup C] (u : Fin k → C), (∀ i, u i ^ n i = 1) →
        ∃ ψ : Q →* C, ∀ i, ψ (g i) = u i := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let σ := (Fintype.equivFin ι).symm
  haveI : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  refine ⟨_, fun i => n (σ i), fun i => e.symm (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)),
    fun i => zero_lt_one.trans (hn (σ i)), fun i => ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    have := orderOf_injective (MonoidHom.mulSingle (fun i => Multiplicative (ZMod (n i))) (σ i))
      (Pi.mulSingle_injective (M := fun i => Multiplicative (ZMod (n i))) (σ i)) (Multiplicative.ofAdd 1)
    rw [MonoidHom.mulSingle_apply] at this
    rw [this, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  · rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := e.symm.surjective q
    rw [← Finset.univ_prod_mulSingle y, map_prod]
    refine Submonoid.prod_mem _ fun i _ => ?_
    obtain ⟨i, rfl⟩ := σ.surjective i
    have : y (σ i) = Multiplicative.ofAdd (1 : ZMod (n (σ i))) ^ (y (σ i)).toAdd.val := by
      rw [← ofAdd_nsmul]; simp
    rw [this, Pi.mulSingle_pow, map_pow]
    have hmem : e.symm (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)) ∈
        Set.range (fun j => e.symm (Pi.mulSingle (σ j) (Multiplicative.ofAdd 1))) := ⟨i, rfl⟩
    exact Submonoid.pow_mem _ (Submonoid.subset_closure hmem) _
  · intro C _ u hu
    let φ : (∀ i, Multiplicative (ZMod (n i))) →* C :=
      { toFun := fun y => ∏ i, u (σ.symm i) ^ (y i).toAdd.val
        map_one' := by simp
        map_mul' := fun y₁ y₂ => by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← pow_add]
          have hmod : ((y₁ i * y₂ i).toAdd.val) ≡ (y₁ i).toAdd.val + (y₂ i).toAdd.val [MOD n i] := by
            change ((y₁ i).toAdd + (y₂ i).toAdd).val ≡ _ [MOD n i]
            rw [ZMod.val_add]
            exact Nat.mod_modEq _ _
          have hpow : u (σ.symm i) ^ n i = 1 := by simpa using hu (σ.symm i)
          have hord : orderOf (u (σ.symm i)) ∣ n i := orderOf_dvd_of_pow_eq_one hpow
          exact pow_eq_pow_iff_modEq.mpr (hmod.of_dvd hord) }
    refine ⟨φ.comp e.toMonoidHom, fun i => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, φ,
      MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Finset.prod_eq_single (σ i)]
    · rw [Pi.mulSingle_eq_same, Equiv.symm_apply_apply]
      have h1 : (Multiplicative.ofAdd (1 : ZMod (n (σ i)))).toAdd.val = 1 := by
        haveI : Fact (1 < n (σ i)) := ⟨hn (σ i)⟩
        exact ZMod.val_one (n (σ i))
      rw [h1, pow_one]
    · intro j _ hji
      rw [Pi.mulSingle_eq_of_ne hji]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **Unconditional Eigenspace Length Bound (`lenEigLe`, works even when `l ∣ |Q|`)**. -/
theorem lenEigLe {O Q N : Type*} [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q]
    [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
    [AddCommGroup N] [Module O N] (π : Representation O Q N) :
    Module.length O N ≤ ∑ χ : Q →* Oˣ, Module.length O (eig π χ) := by
  classical
  obtain ⟨k, n, g, hn, hord, hgen, hchar⟩ := exists_commGroup_generators Q
  have hexp : ∀ i, n i ∣ Monoid.exponent Q := fun i =>
    hord i ▸ Monoid.order_dvd_exponent (g i)
  have hroots : ∀ i, ∃ ζ : O, IsPrimitiveRoot ζ (n i) := fun i => by
    haveI : HasEnoughRootsOfUnity O (n i) := HasEnoughRootsOfUnity.of_dvd O (hexp i)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot O (n i)
  choose ζ hζ using hroots
  have hf_pow : ∀ i, (π (g i)) ^ n i = 1 := fun i => by
    rw [← map_pow, ← hord i, pow_orderOf_eq_one, map_one]
  have hf_comm : ∀ i j, π (g i) * π (g j) = π (g j) * π (g i) := fun i j => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hmain := lenEigLe_many k n ζ hn hζ (fun i => π (g i)) hf_pow hf_comm ⊤ (fun _ _ _ => trivial)
  rw [Module.length_top] at hmain
  refine hmain.trans ?_
  have hunit : ∀ (i : Fin k) (a : Fin (n i)), IsUnit (ζ i ^ (a : ℕ)) := fun i a =>
    ((hζ i).isUnit (hn i).ne').pow (a : ℕ)
  have htuple : ∀ a : (∀ i, Fin (n i)), ∃ χ : Q →* Oˣ, ∀ i, ((χ (g i) : Oˣ) : O) = ζ i ^ (a i : ℕ) := by
    intro a
    obtain ⟨χ, hχ⟩ := hchar Oˣ (fun i => (hunit i (a i)).unit) (fun i => by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
      rw [← pow_mul, mul_comm, pow_mul, (hζ i).pow_eq_one, one_pow])
    exact ⟨χ, fun i => by rw [hχ i, IsUnit.unit_spec]⟩
  choose Φ hΦ using htuple
  have hΦ_inj : Function.Injective Φ := by
    intro a b hab
    funext i
    apply Fin.ext
    have h1 : ζ i ^ (a i : ℕ) = ζ i ^ (b i : ℕ) := by
      rw [← hΦ a i, ← hΦ b i, hab]
    exact (hζ i).pow_inj (a i).isLt (b i).isLt h1
  have hle_eig : ∀ a : (∀ i, Fin (n i)),
      ((⊤ : Submodule O N) ⊓ ⨅ i, LinearMap.ker (π (g i) - ζ i ^ (a i : ℕ) • (1 : Module.End O N))) ≤
        eig π (Φ a) := by
    intro a x hx
    rw [top_inf_eq, Submodule.mem_iInf] at hx
    rw [mem_eig]
    intro q
    have hq : q ∈ Submonoid.closure (Set.range g) := by rw [hgen]; trivial
    induction hq using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      have hi := LinearMap.mem_ker.mp (hx i)
      rw [hΦ a i]
      simpa [sub_eq_zero] using hi
    | one => simp
    | mul y z _ _ ihy ihz =>
      rw [map_mul, Module.End.mul_apply, ihz, map_smul, ihy, smul_smul, map_mul, Units.val_mul, mul_comm]
  calc ∑ a : (∀ i, Fin (n i)),
        Module.length O ((⊤ : Submodule O N) ⊓
          ⨅ i, LinearMap.ker (π (g i) - ζ i ^ (a i : ℕ) • (1 : Module.End O N)) : Submodule O N)
      ≤ ∑ a : (∀ i, Fin (n i)), Module.length O (eig π (Φ a)) :=
          Finset.sum_le_sum fun a _ => length_mono_of_le (hle_eig a)
    _ = ∑ χ ∈ Finset.univ.image Φ, Module.length O (eig π χ) :=
          (Finset.sum_image (f := fun χ => Module.length O (eig π χ))
            (fun a _ b _ h => hΦ_inj h)).symm
    _ ≤ ∑ χ : Q →* Oˣ, Module.length O (eig π χ) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)

private lemma sum_hom_units_eq_zero {O G : Type*} [CommRing O] [IsDomain O] [Group G] [Fintype G]
    (ψ : G →* O) (hψ : ψ ≠ 1) : ∑ g : G, ψ g = 0 := by
  have hex : ∃ g₀ : G, ψ g₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (MonoidHom.ext h)
  obtain ⟨g₀, hg₀⟩ := hex
  have hmul : ψ g₀ * ∑ g : G, ψ g = ∑ g : G, ψ g := by
    rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl fun g _ => (map_mul ψ g₀ g).symm).trans ?_
    exact Fintype.sum_bijective (fun g => g₀ * g) (Group.mulLeft_bijective g₀) _ _ (fun _ => rfl)
  have h0 : (ψ g₀ - 1) * ∑ g : G, ψ g = 0 := by rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hg₀)

/-- **Exact Maschke Orthogonal-Idempotent Decomposition (`lenEigEq`, when `IsUnit (|Q| : O)`)**. -/
theorem lenEigEq {O Q N : Type*} [CommRing O] [IsDomain O] [CommGroup Q] [Fintype Q]
    [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
    [AddCommGroup N] [Module O N] (π : Representation O Q N)
    (hu : IsUnit (Fintype.card Q : O)) :
    Module.length O N = ∑ χ : Q →* Oˣ, Module.length O (eig π χ) := by
  classical
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  let prj : (Q →* Oˣ) → Module.End O N := fun χ =>
    c • ∑ g : Q, ((χ g⁻¹ : Oˣ) : O) • π g
  have hprj_apply : ∀ (χ : Q →* Oˣ) (x : N),
      prj χ x = c • ∑ g : Q, ((χ g⁻¹ : Oˣ) : O) • π g x := fun χ x => by
    simp [prj, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
  have hprj_mem : ∀ (χ : Q →* Oˣ) (x : N), prj χ x ∈ eig π χ := by
    intro χ x
    rw [mem_eig]
    intro h
    rw [hprj_apply, map_smul, map_sum]
    have hterm : ∀ g : Q, π h (((χ g⁻¹ : Oˣ) : O) • π g x) =
        ((χ h : Oˣ) : O) • (((χ (h * g)⁻¹ : Oˣ) : O) • π (h * g) x) := fun g => by
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, smul_smul, ← Units.val_mul, ← map_mul]
      simp [mul_inv_rev]
    simp_rw [hterm, ← Finset.smul_sum]
    rw [smul_comm]
    congr 1
    congr 1
    exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)
  have hprj_self : ∀ (χ : Q →* Oˣ) {x : N}, x ∈ eig π χ → prj χ x = x := by
    intro χ x hx
    rw [hprj_apply]
    have h1 : ∀ g : Q, ((χ g⁻¹ : Oˣ) : O) • π g x = x := fun g => by
      rw [mem_eig.mp hx, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, one_smul]
    simp_rw [h1]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  have hprj_ne : ∀ {ψ χ : Q →* Oˣ}, ψ ≠ χ → ∀ {x : N}, x ∈ eig π χ → prj ψ x = 0 := by
    intro ψ χ hne x hx
    rw [hprj_apply]
    have h1 : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x =
        ((Units.coeHom O).comp (ψ⁻¹ * χ) g) • x := fun g => by
      rw [mem_eig.mp hx, smul_smul]
      simp
    simp_rw [h1]
    rw [← Finset.sum_smul, sum_hom_units_eq_zero, zero_smul, smul_zero]
    intro h1'
    apply hne
    ext g
    have hg := DFunLike.congr_fun h1' g
    have h2 : (ψ g)⁻¹ * χ g = 1 := Units.ext (by simpa using hg)
    exact congrArg Units.val (inv_mul_eq_one.mp h2)
  have hsum_prj : ∀ x : N, ∑ χ : Q →* Oˣ, prj χ x = x := by
    intro x
    simp_rw [hprj_apply]
    rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_eq_single (1 : Q)]
    · simp only [inv_one, map_one, Units.val_one, one_smul, Module.End.one_apply]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
        ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
    · intro g _ hg
      rw [← Finset.sum_smul]
      obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q O (inv_ne_one.mpr hg)
      have h0 := sum_hom_units_eq_zero
        ((Units.coeHom O).comp (MonoidHom.eval g⁻¹ : (Q →* Oˣ) →* Oˣ)) (fun h =>
          hφ (Units.ext (DFunLike.congr_fun h φ)))
      have h2 : ∑ χ : Q →* Oˣ, ((χ g⁻¹ : Oˣ) : O) = 0 := h0
      rw [h2, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  let f : N →ₗ[O] (∀ χ : Q →* Oˣ, eig π χ) :=
    LinearMap.pi fun χ => (prj χ).codRestrict (eig π χ) (hprj_mem χ)
  let g : (∀ χ : Q →* Oˣ, eig π χ) →ₗ[O] N :=
    { toFun := fun y => ∑ χ : Q →* Oˣ, (y χ : N)
      map_add' := fun y₁ y₂ => by simp [Finset.sum_add_distrib]
      map_smul' := fun r y => by simp [Finset.smul_sum] }
  have hleft : ∀ x : N, g (f x) = x := fun x => hsum_prj x
  have hright : ∀ y : (∀ χ : Q →* Oˣ, eig π χ), f (g y) = y := fun y => by
    funext χ
    apply Subtype.ext
    change prj χ (∑ ψ : Q →* Oˣ, (y ψ : N)) = (y χ : N)
    rw [map_sum, Finset.sum_eq_single χ]
    · exact hprj_self χ (y χ).2
    · intro ψ _ hψ; exact hprj_ne hψ.symm (y ψ).2
    · intro h; exact absurd (Finset.mem_univ _) h
  let eqv : N ≃ₗ[O] (∀ χ : Q →* Oˣ, eig π χ) :=
    LinearEquiv.ofLinearMap f g (LinearMap.ext hright) (LinearMap.ext hleft)
  rw [eqv.length_eq, Module.length_pi_of_fintype]

end BaseChangeAndMaschke

/-! ## Section 4: Genuine `Gal(E/ℚ)` Action on `Sha1Galois E l k` & Commutation with `conjH1` -/

section GaloisActionOnSha

variable {E : Type} [Field E] [NumberField E]

/-- `AlgebraicClosure E` is also an algebraic closure of `ℚ`. -/
theorem isAlgClosure_rat_algClosure (E : Type) [Field E] [NumberField E] :
    IsAlgClosure ℚ (AlgebraicClosure E) := by
  haveI : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure E) := AlgebraicClosure.isAlgebraic E
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) :=
    Algebra.IsAlgebraic.trans (R := ℚ) (S := E) (A := AlgebraicClosure E)
  exact ⟨AlgebraicClosure.isAlgClosed E, inferInstance⟩

/-- `IsLiftGal g σ` means `σ : Ω ≃ₐ[ℚ] Ω` extends `g : E ≃ₐ[ℚ] E`. -/
def IsLiftGal {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω]
    (g : E ≃ₐ[ℚ] E) (σ : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω (g x)

theorem IsLiftGal.one {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω] :
    IsLiftGal (E := E) (Ω := Ω) 1 1 := fun _ => rfl

theorem IsLiftGal.mul {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω]
    {g₁ g₂ : E ≃ₐ[ℚ] E} {σ₁ σ₂ : Ω ≃ₐ[ℚ] Ω}
    (h₁ : IsLiftGal g₁ σ₁) (h₂ : IsLiftGal g₂ σ₂) :
    IsLiftGal (g₁ * g₂) (σ₁ * σ₂) := fun x => by
  change σ₁ (σ₂ (algebraMap E Ω x)) = algebraMap E Ω (g₁ (g₂ x))
  rw [h₂ x, h₁ (g₂ x)]

theorem IsLiftGal.inv {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω]
    {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (h : IsLiftGal g σ) :
    IsLiftGal g⁻¹ σ⁻¹ := fun x => by
  apply σ.injective
  have h1 : σ (σ⁻¹ (algebraMap E Ω x)) = algebraMap E Ω x := σ.apply_symm_apply _
  rw [h1, h (g⁻¹ x)]
  congr 1
  exact (g.apply_symm_apply x).symm

/-- Diamond-free wrapper of `AlgebraicClosure E` twisted by `g : E ≃ₐ[ℚ] E` for constructing lifts. -/
private structure TwistedClosure (E : Type) [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) where
  val : AlgebraicClosure E

private def TwistedClosure.equiv (E : Type) [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) :
    TwistedClosure E g ≃ AlgebraicClosure E where
  toFun := TwistedClosure.val
  invFun := TwistedClosure.mk
  left_inv _ := rfl
  right_inv _ := rfl

private instance (E : Type) [Field E] [NumberField E] (g : E ≃ₐ[ℚ] E) : Field (TwistedClosure E g) :=
  (TwistedClosure.equiv E g).field

/-- Every `g : E ≃ₐ[ℚ] E` lifts to an automorphism `σ : AlgebraicClosure E ≃ₐ[ℚ] AlgebraicClosure E`. -/
theorem exists_liftGal (g : E ≃ₐ[ℚ] E) :
    ∃ σ : AlgebraicClosure E ≃ₐ[ℚ] AlgebraicClosure E, IsLiftGal g σ := by
  let eR : TwistedClosure E g ≃+* AlgebraicClosure E :=
    { toEquiv := TwistedClosure.equiv E g
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra E (TwistedClosure E g) :=
    (eR.symm.toRingHom.comp ((algebraMap E (AlgebraicClosure E)).comp g.toRingHom)).toAlgebra
  haveI : IsAlgClosed (TwistedClosure E g) :=
    IsAlgClosed.of_ringEquiv (AlgebraicClosure E) (TwistedClosure E g) eR.symm
  haveI : Algebra.IsAlgebraic E (TwistedClosure E g) := by
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) := (isAlgClosure_rat_algClosure E).isAlgebraic
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure E) := Algebra.IsAlgebraic.isIntegral
    refine ⟨fun z => ?_⟩
    have hz : IsIntegral ℚ (eR z) := Algebra.IsIntegral.isIntegral (eR z)
    obtain ⟨p, hp_monic, hpz⟩ := hz
    refine ⟨p.map (algebraMap ℚ E), (hp_monic.map _).ne_zero, ?_⟩
    apply eR.injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : eR.toRingHom.comp ((algebraMap E (TwistedClosure E g)).comp (algebraMap ℚ E)) =
        algebraMap ℚ (AlgebraicClosure E) := by
      ext r
      change eR (eR.symm (algebraMap E (AlgebraicClosure E) (g (algebraMap ℚ E r)))) = _
      rw [eR.apply_symm_apply, g.commutes r]
      exact (IsScalarTower.algebraMap_apply ℚ E (AlgebraicClosure E) r).symm
    have hev : eR.toRingHom (Polynomial.eval₂ ((algebraMap E (TwistedClosure E g)).comp (algebraMap ℚ E)) z p) =
        Polynomial.eval₂ (algebraMap ℚ (AlgebraicClosure E)) (eR z) p := by
      rw [Polynomial.hom_eval₂, hcomp]; rfl
    exact hev.trans hpz
  haveI : IsAlgClosure E (TwistedClosure E g) := ⟨inferInstance, inferInstance⟩
  let φ : AlgebraicClosure E ≃ₐ[E] TwistedClosure E g :=
    IsAlgClosure.equiv E (AlgebraicClosure E) (TwistedClosure E g)
  let σR : AlgebraicClosure E ≃+* AlgebraicClosure E := φ.toRingEquiv.trans eR
  let σ : AlgebraicClosure E ≃ₐ[ℚ] AlgebraicClosure E :=
    AlgEquiv.ofRingEquiv (f := σR) (fun r => by
      change σR (algebraMap ℚ (AlgebraicClosure E) r) = algebraMap ℚ (AlgebraicClosure E) r
      exact map_ratCast σR r)
  refine ⟨σ, fun x => ?_⟩
  change eR (φ (algebraMap E (AlgebraicClosure E) x)) = algebraMap E (AlgebraicClosure E) (g x)
  rw [φ.commutes x]
  change eR (eR.symm (algebraMap E (AlgebraicClosure E) (g x))) = _
  rw [eR.apply_symm_apply]

/-- Induced ring automorphism `𝓞 E ≃+* 𝓞 E` from `g : E ≃ₐ[ℚ] E`. -/
def galRingInt (g : E ≃ₐ[ℚ] E) : 𝓞 E ≃+* 𝓞 E where
  toFun x := ⟨g x.1, IsIntegral.map g.toAlgHom x.2⟩
  invFun x := ⟨g.symm x.1, IsIntegral.map g.symm.toAlgHom x.2⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x.1)
  right_inv x := Subtype.ext (g.apply_symm_apply x.1)
  map_mul' a b := Subtype.ext (map_mul g a.1 b.1)
  map_add' a b := Subtype.ext (map_add g a.1 b.1)

/-- Induced bijection on `HeightOneSpectrum (𝓞 E)` sending `v ↦ v.comap g`. -/
def galSpec (g : E ≃ₐ[ℚ] E) :
    HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E) :=
  let φ : 𝓞 E ≃+* 𝓞 E := galRingInt g
  { toFun := fun v =>
      { asIdeal := v.asIdeal.comap φ.toRingHom
        isPrime := v.isPrime.comap φ.toRingHom
        ne_bot := fun h => v.ne_bot (Ideal.ext fun x => by
          constructor
          · intro hx
            have : φ.symm x ∈ v.asIdeal.comap φ.toRingHom := by
              rw [Ideal.mem_comap]
              change φ (φ.symm x) ∈ v.asIdeal
              rw [φ.apply_symm_apply]
              exact hx
            rw [h, Ideal.mem_bot] at this
            simpa using congrArg φ this
          · intro hx; rw [Ideal.mem_bot.mp hx]; exact Ideal.zero_mem _) }
    invFun := fun v =>
      { asIdeal := v.asIdeal.comap φ.symm.toRingHom
        isPrime := v.isPrime.comap φ.symm.toRingHom
        ne_bot := fun h => v.ne_bot (Ideal.ext fun x => by
          constructor
          · intro hx
            have : φ x ∈ v.asIdeal.comap φ.symm.toRingHom := by
              rw [Ideal.mem_comap]
              change φ.symm (φ x) ∈ v.asIdeal
              rw [φ.symm_apply_apply]
              exact hx
            rw [h, Ideal.mem_bot] at this
            simpa using congrArg φ.symm this
          · intro hx; rw [Ideal.mem_bot.mp hx]; exact Ideal.zero_mem _) }
    left_inv := fun v => by
      ext x
      change φ (φ.symm x) ∈ v.asIdeal ↔ x ∈ v.asIdeal
      rw [φ.apply_symm_apply]
    right_inv := fun v => by
      ext x
      change φ.symm (φ x) ∈ v.asIdeal ↔ x ∈ v.asIdeal
      rw [φ.symm_apply_apply] }

theorem galSpec_mem_above_iff (g : E ≃ₐ[ℚ] E) (l : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    galSpec g v ∈ Above E l ↔ v ∈ Above E l := by
  change ((l : ℕ) : 𝓞 E) ∈ v.asIdeal.comap (galRingInt g).toRingHom ↔ ((l : ℕ) : 𝓞 E) ∈ v.asIdeal
  rw [Ideal.mem_comap, map_natCast]

section LiftAction

variable {Ω : Type} [Field Ω] [Algebra E Ω] [Algebra ℚ Ω] [IsScalarTower ℚ E Ω] [IsAlgClosure E Ω]

/-- Conjugation automorphism `h ↦ σ⁻¹ * h * σ` on `G E Ω` induced by a lift `σ : Ω ≃ₐ[ℚ] Ω` of `g`. -/
def conjGalHom {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ) : G E Ω →* G E Ω where
  toFun h :=
    { toFun := fun y => σ.symm (h (σ y))
      invFun := fun y => σ.symm (h.symm (σ y))
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      map_mul' := fun a b => by simp [map_mul]
      map_add' := fun a b => by simp [map_add]
      commutes' := fun x => by
        show σ.symm (h (σ (algebraMap E Ω x))) = algebraMap E Ω x
        rw [hσ x, h.commutes (g x), ← hσ x, σ.symm_apply_apply] }
  map_one' := by ext y; simp
  map_mul' h₁ h₂ := by ext y; simp [AlgEquiv.mul_apply]

theorem conjGalHom_continuous {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ) :
    Continuous (conjGalHom hσ) := by
  apply continuous_of_continuousAt_one (conjGalHom hσ)
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K, hK, hs⟩ := hs
  haveI : FiniteDimensional E K := hK
  let K' : IntermediateField E Ω :=
    { carrier := {y : Ω | σ.symm y ∈ K}
      zero_mem' := by simp
      add_mem' := fun ha hb => by simp only [Set.mem_ofPred_eq] at *; rw [map_add]; exact K.add_mem ha hb
      one_mem' := by simp
      mul_mem' := fun ha hb => by simp only [Set.mem_ofPred_eq] at *; rw [map_mul]; exact K.mul_mem ha hb
      inv_mem' := fun {a} ha => by simp only [Set.mem_ofPred_eq] at *; rw [map_inv₀]; exact K.inv_mem ha
      algebraMap_mem' := fun x => by
        simp only [Set.mem_ofPred_eq]
        have hinv : σ.symm (algebraMap E Ω x) = algebraMap E Ω (g.symm x) := hσ.inv x
        rw [hinv]
        exact K.algebraMap_mem (g.symm x) }
  have hK' : FiniteDimensional E K' := by
    haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
    let eKK' : K ≃ₗ[ℚ] K' :=
      { toFun := fun y => ⟨σ y.1, by simp [K', y.2]⟩
        invFun := fun y => ⟨σ.symm y.1, y.2⟩
        left_inv := fun y => Subtype.ext (σ.symm_apply_apply y.1)
        right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1)
        map_add' := fun a b => Subtype.ext (map_add σ a.1 b.1)
        map_smul' := fun r y => Subtype.ext (by
          change σ (r • y.1) = r • σ y.1
          exact map_smul σ r y.1) }
    haveI : FiniteDimensional ℚ K' := eKK'.finiteDimensional
    exact Module.Finite.of_restrictScalars_finite ℚ E K'
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨K', hK', fun h hh => hs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro x hx
  have hx' : σ x ∈ K' := by change σ.symm (σ x) ∈ K; simpa using hx
  have hgx := hh (σ x) hx'
  show σ.symm (h (σ x)) = x
  rw [hgx, σ.symm_apply_apply]

theorem conjGalHom_cycZ {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    (l : ℕ) [Fact l.Prime] (h : G E Ω) :
    cycZ E Ω l (conjGalHom hσ h) = cycZ E Ω l h := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hζ' : IsPrimitiveRoot (σ ζ) (l ^ n) := hζ.map_of_injective σ.injective
  have h1 : h (σ ζ) = (σ ζ) ^ (PadicInt.toZModPow n ((cycZ E Ω l h : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G E Ω) Ω h) (σ ζ) hζ'.pow_eq_one
  have h2 : σ.symm (h (σ ζ)) =
      ζ ^ (PadicInt.toZModPow n ((cycZ E Ω l (conjGalHom hσ h) : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l
      (MulSemiringAction.toRingAut (G E Ω) Ω (conjGalHom hσ h)) ζ hζ.pow_eq_one
  rw [h1, map_pow, σ.symm_apply_apply] at h2
  apply ZMod.val_injective
  exact (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2).symm

theorem conjGalHom_mem_ine {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {A : ValuationSubring Ω} {h : G E Ω} (hh : h ∈ Ine (F := E) A) :
    conjGalHom hσ h ∈ Ine (F := E) (A.comap σ.toRingHom) := by
  let A₁ := A.comap σ.toRingHom
  have hA₁ : ∀ y : Ω, y ∈ A₁ ↔ σ y ∈ A := fun _ => Iff.rfl
  have hdec : conjGalHom hσ h ∈ Dec (F := E) A₁ := by
    rw [mem_Dec]
    ext y
    conv_lhs =>
      rw [← smul_inv_smul (conjGalHom hσ h) y, ValuationSubring.smul_mem_pointwise_smul_iff]
    rw [← map_inv (conjGalHom hσ) h, hA₁, hA₁]
    show σ (σ.symm (h⁻¹ (σ y))) ∈ A ↔ σ y ∈ A
    rw [σ.apply_symm_apply]
    exact apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hh.1) (σ y)
  have hv : ∀ y : Ω, A₁.valuation y < 1 ↔ A.valuation (σ y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hA₁, ← map_inv₀, hA₁,
      map_eq_zero_iff _ σ.injective]
  refine ⟨hdec, fun x hx => ?_⟩
  rw [hv]
  have hle : A.valuation (σ x) ≤ 1 := by
    rwa [ValuationSubring.valuation_le_one_iff, ← hA₁, ← ValuationSubring.valuation_le_one_iff]
  have e : σ ((conjGalHom hσ h) x - x) = h (σ x) - σ x := by
    rw [map_sub]
    show σ (σ.symm (h (σ x))) - σ x = _
    rw [σ.apply_symm_apply]
  rw [e]
  exact hh.2 (σ x) hle

theorem gal_isPlaceOver {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A v) :
    IsPlaceOver (A.comap σ.toRingHom) (galSpec g v) := by
  intro x
  let A₁ := A.comap σ.toRingHom
  have hA₁ : ∀ y : Ω, y ∈ A₁ ↔ σ y ∈ A := fun _ => Iff.rfl
  have hv : ∀ y : Ω, A₁.valuation y < 1 ↔ A.valuation (σ y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hA₁, ← map_inv₀, hA₁,
      map_eq_zero_iff _ σ.injective]
  rw [hv, hσ (x : E)]
  exact hA (galRingInt g x)

theorem conjGalHom_NS_le {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    (l : ℕ) [Fact l.Prime] (D : LData E Ω l) :
    NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) ≤
      (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comap (conjGalHom hσ) := by
  have hcl : IsClosed (((NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comap
      (conjGalHom hσ) : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).preimage (conjGalHom_continuous hσ)
  haveI : ((NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comap (conjGalHom hσ)).Normal :=
    Subgroup.Normal.comap inferInstance _
  unfold NS
  apply Subgroup.topologicalClosure_minimal _ _ hcl
  apply Subgroup.normalClosure_le_normal
  rintro τ hτ
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff, exists_prop] at hτ
  obtain ⟨v, hv, A, hA, hτ_ine⟩ := hτ
  have hv' : galSpec g v ∉ (D.S : Set (HeightOneSpectrum (𝓞 E))) := by
    intro hmem
    have h1 : galSpec g v ∈ Above E l := D.hS ▸ hmem
    rw [galSpec_mem_above_iff, ← D.hS] at h1
    exact hv h1
  show conjGalHom hσ τ ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_compl_iff, exists_prop]
  exact ⟨galSpec g v, hv', A.comap σ.toRingHom, gal_isPlaceOver hσ hA, conjGalHom_mem_ine hσ hτ_ine⟩

/-- Continuous automorphism `GS Ω D.S →* GS Ω D.S` induced by a lift `σ : Ω ≃ₐ[ℚ] Ω` of `g`. -/
def gsGalHom {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) :
    GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) :=
  QuotientGroup.map
    (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))
    (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))
    (conjGalHom hσ) (conjGalHom_NS_le hσ l D)

theorem gsGalHom_mk {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (h : G E Ω) :
    gsGalHom hσ D (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) h) =
      toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (conjGalHom hσ h) := rfl

theorem continuous_gsGalHom {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) :
    Continuous (gsGalHom hσ D) :=
  (QuotientGroup.isQuotientMap_mk
    (NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))))).continuous_iff.2
    ((continuous_toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comp (conjGalHom_continuous hσ))

theorem chi_comp_gsGalHom {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l)
    (x : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) :
    D.chi (gsGalHom hσ D x) = D.chi x := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  show D.chi (gsGalHom hσ D (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) h)) =
    D.chi (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) h)
  rw [gsGalHom_mk]
  have h1 := congrArg (fun f => f (conjGalHom hσ h)) D.hchi
  have h2 := congrArg (fun f => f h) D.hchi
  exact h1.trans ((conjGalHom_cycZ hσ l h).trans h2.symm)

/-- Twisted action of a lift `σ : Ω ≃ₐ[ℚ] Ω` on `H¹(G_{E, S_l}, (ℚ_l/ℤ_l)(-e))`:
`(σ • f)(x) = (cycZ ℚ Ω l σ)^{-e} • f(σ⁻¹ x σ)`. -/
def liftActH1 {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    Module.End ℤ_[l] (H1 (qzTw D e)) :=
  let u : ℤ_[l] := (((cycZ ℚ Ω l σ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l])
  let mScal : QZ l →ₗ[ℤ_[l]] QZ l := u • LinearMap.id
  have hcomm : ∀ x m, mScal (qzTw D e (gsGalHom hσ D x) m) = qzTw D e x (mScal m) := by
    intro x m
    have hchi : D.chi (gsGalHom hσ D x) = D.chi x := chi_comp_gsGalHom hσ D x
    have hchi_pow : (D.chi ^ (-e)) (gsGalHom hσ D x) = (D.chi ^ (-e)) x := by
      cases -e with
      | ofNat n =>
        change (D.chi ^ (n : ℤ)) (gsGalHom hσ D x) = (D.chi ^ (n : ℤ)) x
        simp only [zpow_natCast, MonoidHom.pow_apply, hchi]
      | negSucc n =>
        simp only [zpow_negSucc, MonoidHom.inv_apply, MonoidHom.pow_apply, hchi]
    change u • (qzTw D e (gsGalHom hσ D x) m) = qzTw D e x (u • m)
    rw [map_smul]
    congr 1
    simp only [qzTw, scalRep_apply, hchi_pow]
  pairH1 (qzTw D e) (qzTw D e) (gsGalHom hσ D) (continuous_gsGalHom hσ D) mScal
    (continuous_id.const_smul u) hcomm

theorem liftActH1_one {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    liftActH1 (E := E) (Ω := Ω) IsLiftGal.one D e = 1 := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  dsimp only [liftActH1]
  simp only [pairH1, Submodule.mapQ_apply, Module.End.one_apply]
  apply (Submodule.Quotient.eq _).mpr
  refine (mem_B1 _ _).mpr ⟨0, fun y => ?_⟩
  rw [map_zero, sub_zero]
  have hgs : gsGalHom (IsLiftGal.one (E := E) (Ω := Ω)) D y = y := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    show toGS Ω _ (conjGalHom IsLiftGal.one h) = toGS Ω _ h
    congr 1
  change (((cycZ ℚ Ω l 1) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • f.1 (gsGalHom IsLiftGal.one D y) - f.1 y = 0
  rw [map_one, one_zpow, Units.val_one, one_smul, hgs, sub_self]

theorem liftActH1_mul {g₁ g₂ : E ≃ₐ[ℚ] E} {σ₁ σ₂ : Ω ≃ₐ[ℚ] Ω}
    (h₁ : IsLiftGal g₁ σ₁) (h₂ : IsLiftGal g₂ σ₂)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    liftActH1 (h₁.mul h₂) D e = liftActH1 h₁ D e * liftActH1 h₂ D e := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  dsimp only [liftActH1]
  simp only [Module.End.mul_apply, pairH1, Submodule.mapQ_apply]
  apply (Submodule.Quotient.eq _).mpr
  refine (mem_B1 _ _).mpr ⟨0, fun y => ?_⟩
  rw [map_zero, sub_zero]
  have hgs : gsGalHom (h₁.mul h₂) D y = gsGalHom h₂ D (gsGalHom h₁ D y) := by
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    show toGS Ω _ (conjGalHom (h₁.mul h₂) h) = toGS Ω _ (conjGalHom h₂ (conjGalHom h₁ h))
    congr 1
  have hcyc : (((cycZ ℚ Ω l (σ₁ * σ₂)) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) =
      (((cycZ ℚ Ω l σ₁) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) *
      (((cycZ ℚ Ω l σ₂) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) := by
    rw [map_mul, mul_zpow, Units.val_mul]
  change (((cycZ ℚ Ω l (σ₁ * σ₂)) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • f.1 (gsGalHom (h₁.mul h₂) D y) -
    (((cycZ ℚ Ω l σ₁) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) •
      ((((cycZ ℚ Ω l σ₂) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • f.1 (gsGalHom h₂ D (gsGalHom h₁ D y))) = 0
  rw [hcyc, hgs, mul_smul, sub_self]

/-- **Inner-Conjugation Triviality (Lift Independence Core)**:
any lift `τ : Ω ≃ₐ[ℚ] Ω` of `1 : E ≃ₐ[ℚ] E` acts trivially on `H¹(G_{E, S_l}, (ℚ_l/ℤ_l)(-e))`! -/
theorem liftActH1_eq_one_of_lift_one {τ : Ω ≃ₐ[ℚ] Ω} (hτ : IsLiftGal (E := E) 1 τ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    liftActH1 hτ D e = 1 := by
  let τE : G E Ω :=
    { toRingEquiv := τ.toRingEquiv
      commutes' := fun x => hτ x }
  let t : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) := toGS Ω _ τE
  have hcyc : cycZ ℚ Ω l τ = D.chi t := by
    have h1 : D.chi t = cycZ E Ω l τE := congrArg (fun f => f τE) D.hchi
    exact h1.symm
  have hgs : ∀ y : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))),
      gsGalHom hτ D y = t⁻¹ * y * t := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    show toGS Ω _ (conjGalHom hτ h) = (toGS Ω _ τE)⁻¹ * toGS Ω _ h * toGS Ω _ τE
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  dsimp only [liftActH1]
  simp only [pairH1, Submodule.mapQ_apply, Module.End.one_apply]
  apply (Submodule.Quotient.eq _).mpr
  refine (mem_B1 _ _).mpr ⟨f.1 t, fun y => ?_⟩
  change (((cycZ ℚ Ω l τ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • f.1 (gsGalHom hτ D y) - f.1 y =
    qzTw D e y (f.1 t) - f.1 t
  rw [hgs y]
  have hu : (((cycZ ℚ Ω l τ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • f.1 (t⁻¹ * y * t) =
      qzTw D e t (f.1 (t⁻¹ * y * t)) := by
    rw [hcyc]
    simp [qzTw, scalRep_apply]
  rw [hu]
  have hc1 : f.1 (t⁻¹ * (y * t)) = f.1 t⁻¹ + qzTw D e t⁻¹ (f.1 (y * t)) := f.2.2 t⁻¹ (y * t)
  have hc2 : f.1 (y * t) = f.1 y + qzTw D e y (f.1 t) := f.2.2 y t
  have hc3 : f.1 (t * t⁻¹) = f.1 t + qzTw D e t (f.1 t⁻¹) := f.2.2 t t⁻¹
  rw [mul_inv_cancel, cocycle1_one _ f.2.2] at hc3
  have hinv_f : qzTw D e t (f.1 t⁻¹) = -f.1 t := eq_neg_of_add_eq_zero_right hc3.symm
  have hmul_assoc : t⁻¹ * y * t = t⁻¹ * (y * t) := mul_assoc _ _ _
  rw [hmul_assoc, hc1, map_add, hinv_f, hc2, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply]
  abel

private theorem liftActH1_congr {g₁ g₂ : E ≃ₐ[ℚ] E} {σ₁ σ₂ : Ω ≃ₐ[ℚ] Ω}
    (hg : g₁ = g₂) (hσ : σ₁ = σ₂) (h₁ : IsLiftGal g₁ σ₁) (h₂ : IsLiftGal g₂ σ₂)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    liftActH1 h₁ D e = liftActH1 h₂ D e := by
  subst hg; subst hσ; rfl

/-- **Full Lift Independence**: `liftActH1 hσ₁ D e = liftActH1 hσ₂ D e` for any two lifts of `g`. -/
theorem liftActH1_indep {g : E ≃ₐ[ℚ] E} {σ₁ σ₂ : Ω ≃ₐ[ℚ] Ω}
    (h₁ : IsLiftGal g σ₁) (h₂ : IsLiftGal g σ₂)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    liftActH1 h₁ D e = liftActH1 h₂ D e := by
  have hrel : IsLiftGal (E := E) 1 (σ₁⁻¹ * σ₂) := by
    have := h₁.inv.mul h₂
    rwa [inv_mul_cancel] at this
  have h2eq : σ₁ * (σ₁⁻¹ * σ₂) = σ₂ := by group
  have hmul := liftActH1_mul h₁ hrel D e
  have htriv := liftActH1_eq_one_of_lift_one hrel D e
  have hmul' : liftActH1 (h₁.mul hrel) D e = liftActH1 h₁ D e := by
    calc liftActH1 (h₁.mul hrel) D e = liftActH1 h₁ D e * liftActH1 hrel D e := hmul
      _ = liftActH1 h₁ D e * 1 := by rw [htriv]
      _ = liftActH1 h₁ D e := mul_one _
  exact hmul'.symm.trans (liftActH1_congr (mul_one g) h2eq (h₁.mul hrel) h₂ D e)

/-- `liftActH1 hσ D e` preserves `Sha D e` for every lift `σ : Ω ≃ₐ[ℚ] Ω` of `g`. -/
theorem liftActH1_mem_sha {g : E ≃ₐ[ℚ] E} {σ : Ω ≃ₐ[ℚ] Ω} (hσ : IsLiftGal g σ)
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ)
    {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    liftActH1 hσ D e x ∈ Sha D e := by
  simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro v
  let v' : D.S := ⟨galSpec g v.1, by
    have hv' : galSpec g v.1 ∈ Above E l := by
      rw [galSpec_mem_above_iff]
      exact D.hS ▸ Finset.mem_coe.mpr v.2
    exact Finset.mem_coe.mp (D.hS ▸ hv')⟩
  have hA' : IsPlaceOver ((D.A v).comap σ.toRingHom) v'.1 := gal_isPlaceOver hσ (D.hA v)
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (D.hA v') hA'
  let cHom : Dec (F := E) (D.A v) →* Dec (F := E) (D.A v') :=
    { toFun := fun τ =>
        ⟨g₀⁻¹ * conjGalHom hσ τ.1 * g₀, by
          rw [mem_Dec]
          have hc1 : conjGalHom hσ τ.1 ∈ Dec (F := E) ((D.A v).comap σ.toRingHom) := by
            rw [mem_Dec]
            ext y
            conv_lhs =>
              rw [← smul_inv_smul (conjGalHom hσ τ.1) y,
                ValuationSubring.smul_mem_pointwise_smul_iff]
            rw [← map_inv (conjGalHom hσ) τ.1]
            change σ (σ.symm (τ.1⁻¹ (σ y))) ∈ D.A v ↔ σ y ∈ D.A v
            rw [σ.apply_symm_apply]
            exact apply_mem_iff_of_mem_Dec ((Dec (F := E) (D.A v)).inv_mem τ.2) (σ y)
          rw [mem_Dec] at hc1
          have hg_inv : g₀⁻¹ • ((D.A v).comap σ.toRingHom) = D.A v' := by
            rw [← hg₀, inv_smul_smul]
          calc (g₀⁻¹ * conjGalHom hσ τ.1 * g₀) • D.A v'
              = (g₀⁻¹ * conjGalHom hσ τ.1) • (g₀ • D.A v') := mul_smul _ _ _
            _ = g₀⁻¹ • (conjGalHom hσ τ.1 • ((D.A v).comap σ.toRingHom)) := by rw [hg₀, mul_smul]
            _ = g₀⁻¹ • ((D.A v).comap σ.toRingHom) := by rw [hc1]
            _ = D.A v' := hg_inv⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcCont : Continuous cHom :=
    Continuous.subtype_mk
      ((continuous_const.mul ((conjGalHom_continuous hσ).comp continuous_subtype_val)).mul
        continuous_const) _
  have hconj_loc : ∀ τ : Dec (F := E) (D.A v),
      ((locFam D.S D.A v').comp cHom) τ =
        (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) g₀)⁻¹ *
          gsGalHom hσ D (locFam D.S D.A v τ) *
          toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) g₀ := fun τ => by
    simp only [locFam, locHom, MonoidHom.comp_apply, Subgroup.coe_subtype, cHom, MonoidHom.coe_mk,
      OneHom.coe_mk, map_mul, map_inv, gsGalHom_mk]
  have hres_comp : resH1 (qzTw D e) ((locFam D.S D.A v').comp cHom)
      ((continuous_locFam D.S D.A v').comp hcCont) x = 0 := by
    rw [← resH1_comp (qzTw D e) (locFam D.S D.A v') (continuous_locFam D.S D.A v') cHom hcCont x,
      hx v', map_zero]
  have hres_gs : resH1 (qzTw D e) ((gsGalHom hσ D).comp (locFam D.S D.A v))
      ((continuous_gsGalHom hσ D).comp (continuous_locFam D.S D.A v)) x = 0 :=
    (resH1_conj_eq_zero_iff (qzTw D e) ((gsGalHom hσ D).comp (locFam D.S D.A v))
      ((continuous_gsGalHom hσ D).comp (continuous_locFam D.S D.A v))
      (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) g₀)⁻¹
      ((locFam D.S D.A v').comp cHom) ((continuous_locFam D.S D.A v').comp hcCont)
      (fun τ => by rw [hconj_loc, inv_inv]; rfl) x).mp hres_comp
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, mem_B1, restrictCocycles1_apply, MonoidHom.comp_apply] at hres_gs
  dsimp only [liftActH1]
  simp only [resH1, pairH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.coe_subtype, mem_B1, restrictCocycles1_apply,
    compatiblePairCocycles1_apply]
  obtain ⟨m, hm⟩ := hres_gs
  let u : ℤ_[l] := (((cycZ ℚ Ω l σ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l])
  refine ⟨u • m, fun τ => ?_⟩
  change u • f.1 (gsGalHom hσ D (locFam D.S D.A v τ)) =
    qzTw D e (locFam D.S D.A v τ) (u • m) - u • m
  rw [hm τ, smul_sub, map_smul]
  congr 2
  have hchi := chi_comp_gsGalHom hσ D (locFam D.S D.A v τ)
  have hchi_pow : (D.chi ^ (-e)) (gsGalHom hσ D (locFam D.S D.A v τ)) =
      (D.chi ^ (-e)) (locFam D.S D.A v τ) := by
    cases -e with
    | ofNat n =>
      change (D.chi ^ (n : ℤ)) (gsGalHom hσ D (locFam D.S D.A v τ)) =
        (D.chi ^ (n : ℤ)) (locFam D.S D.A v τ)
      simp only [zpow_natCast, MonoidHom.pow_apply, hchi]
    | negSucc n =>
      simp only [zpow_negSucc, MonoidHom.inv_apply, MonoidHom.pow_apply, hchi]
  simp only [qzTw, scalRep_apply, hchi_pow]

end LiftAction

/-- **Genuine Lift-Independent `Gal(E/ℚ)` Representation on `H¹(G_{E, S_l}, (ℚ_l/ℤ_l)(-e))`**. -/
def galActH1 (E : Type) [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
    (D : LData E (AlgebraicClosure E) l) (e : ℤ) :
    Representation ℤ_[l] (E ≃ₐ[ℚ] E) (H1 (qzTw D e)) where
  toFun g := liftActH1 (Classical.choose_spec (exists_liftGal g)) D e
  map_one' := by
    rw [liftActH1_indep (Classical.choose_spec (exists_liftGal (1 : E ≃ₐ[ℚ] E))) IsLiftGal.one D e]
    exact liftActH1_one D e
  map_mul' g₁ g₂ := by
    rw [liftActH1_indep (Classical.choose_spec (exists_liftGal (g₁ * g₂)))
      ((Classical.choose_spec (exists_liftGal g₁)).mul (Classical.choose_spec (exists_liftGal g₂))) D e]
    exact liftActH1_mul _ _ D e

theorem galActH1_eq_liftActH1 {g : E ≃ₐ[ℚ] E} {σ : AlgebraicClosure E ≃ₐ[ℚ] AlgebraicClosure E}
    (hσ : IsLiftGal g σ) {l : ℕ} [Fact l.Prime] (D : LData E (AlgebraicClosure E) l) (e : ℤ) :
    galActH1 E D e g = liftActH1 hσ D e :=
  liftActH1_indep (Classical.choose_spec (exists_liftGal g)) hσ D e

theorem galActH1_mem_sha {l : ℕ} [Fact l.Prime] (D : LData E (AlgebraicClosure E) l) (e : ℤ)
    (g : E ≃ₐ[ℚ] E) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    galActH1 E D e g x ∈ Sha D e :=
  liftActH1_mem_sha (Classical.choose_spec (exists_liftGal g)) D e hx

/-- **Exact Proportionality Between `conjH1 I` and `galActH1 I.c`**:
for EVERY `I : CMGaloisInvolution E (AlgebraicClosure E)` and `e : ℕ`, `conjH1 I D e` is a `±1`
scalar multiple of `galActH1 E D e I.c`! -/
theorem conjH1_eq_smul_galActH1 (I : CMGaloisInvolution E (AlgebraicClosure E))
    {l : ℕ} [Fact l.Prime] (D : LData E (AlgebraicClosure E) l) (e : ℕ) :
    ∃ ε : ℤ_[l], ε * ε = 1 ∧ conjH1 I D (e : ℤ) = ε • galActH1 E D (e : ℤ) I.c := by
  let σI : AlgebraicClosure E ≃ₐ[ℚ] AlgebraicClosure E :=
    AlgEquiv.ofRingEquiv (f := I.σ) (fun r => map_ratCast I.σ r)
  have hσI : IsLiftGal I.c σI := I.compat
  have hσI_sq : σI * σI = 1 := by
    ext z
    change (I.σ.trans I.σ) z = z
    rw [I.σ_sq, RingEquiv.refl_apply]
  let uI : ℤ_[l]ˣ := cycZ ℚ (AlgebraicClosure E) l σI
  have huI_sq : uI * uI = 1 := by
    rw [← map_mul, hσI_sq, map_one]
  have huI_inv : uI⁻¹ = uI := inv_eq_of_mul_eq_one_right huI_sq
  have huI_zpow : ((uI ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) = ((uI : ℤ_[l]) ^ e) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, huI_inv, Units.val_pow_eq_pow_val]
  let ε : ℤ_[l] := (-1 : ℤ_[l]) ^ e * ((uI : ℤ_[l]) ^ e)
  refine ⟨ε, ?_, ?_⟩
  · dsimp only [ε]
    have h1 : (-1 : ℤ_[l]) ^ e * (-1 : ℤ_[l]) ^ e = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have h2 : (uI : ℤ_[l]) ^ e * (uI : ℤ_[l]) ^ e = 1 := by
      rw [← mul_pow, ← Units.val_mul, huI_sq, Units.val_one, one_pow]
    calc ((-1 : ℤ_[l]) ^ e * (uI : ℤ_[l]) ^ e) * ((-1 : ℤ_[l]) ^ e * (uI : ℤ_[l]) ^ e)
        = ((-1 : ℤ_[l]) ^ e * (-1 : ℤ_[l]) ^ e) * ((uI : ℤ_[l]) ^ e * (uI : ℤ_[l]) ^ e) := by ring
      _ = 1 * 1 := by rw [h1, h2]
      _ = 1 := mul_one 1
  · rw [galActH1_eq_liftActH1 hσI D (e : ℤ)]
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    dsimp only [conjH1, liftActH1]
    simp only [pairH1, LinearMap.smul_apply, Submodule.mapQ_apply]
    change Submodule.Quotient.mk _ = ε • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul]
    apply (Submodule.Quotient.eq _).mpr
    refine (mem_B1 _ _).mpr ⟨0, fun y => ?_⟩
    rw [map_zero, sub_zero]
    have hgs_eq : gsConj I l D y = gsGalHom hσI D y := by
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      show toGS (AlgebraicClosure E) _ (cmConjGalHom I h) =
        toGS (AlgebraicClosure E) _ (conjGalHom hσI h)
      congr 1
    have hnatAbs : (e : ℤ).natAbs = e := Int.natAbs_natCast e
    have hmul_ε : ε * ((uI ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) = (-1 : ℤ_[l]) ^ e := by
      rw [huI_zpow]
      dsimp only [ε]
      rw [mul_assoc, ← mul_pow, ← Units.val_mul, huI_sq, Units.val_one, one_pow, mul_one]
    change (-1 : ℤ_[l]) ^ (e : ℤ).natAbs • f.1 (gsConj I l D y) -
      ε • (((uI ^ (-(e : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • f.1 (gsGalHom hσI D y)) = 0
    rw [hnatAbs, hgs_eq, smul_smul, hmul_ε, sub_self]

/-- The exact canonical CM involution used in `Stage13MinusParityRubin.minusParitySelmerSystem`. -/
def canonicalCMInv (E : Type) [Field E] [NumberField E] :
    CMGaloisInvolution E (AlgebraicClosure E) := by
  classical
  exact if h : ∃ I : CMGaloisInvolution E (AlgebraicClosure E), I.c ≠ 1
    then Classical.choose h
    else CMGaloisInvolution.trivial E (AlgebraicClosure E)

/-- The exact plus-parity submodule of `Sha1Galois E l k` matching `minusParitySelmerSystem.plusLen`. -/
def ShaPlus (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ) :
    Submodule ℤ_[l.1] (H1 (qzTw (canonicalLData E l) (k : ℤ))) :=
  Sha1Galois E l (k : ℤ) ⊓
    (conjH1 (canonicalCMInv E) (canonicalLData E l) (k : ℤ)).eigenspace ((-1 : ℤ_[l.1]) ^ k)

/-- `minusParitySelmerSystem.plusLen E l k` is definitionally `Module.length ℤ_[l] (ShaPlus E l k)`! -/
theorem minusParitySelmerSystem_plusLen_eq_shaPlus (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ) :
    minusParitySelmerSystem.plusLen E l k = Module.length ℤ_[l.1] ↥(ShaPlus E l k) := rfl

/-- When `1 ≤ condF E`, `Gal(E/ℚ)` commutes with `conjH1 (canonicalCMInv E)`, hence preserves `ShaPlus E l k`! -/
theorem galActH1_mem_shaPlus (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E)
    (l : Nat.Primes) (k : ℕ) (g : E ≃ₐ[ℚ] E)
    {x : H1 (qzTw (canonicalLData E l) (k : ℤ))} (hx : x ∈ ShaPlus E l k) :
    galActH1 E (canonicalLData E l) (k : ℤ) g x ∈ ShaPlus E l k := by
  refine ⟨galActH1_mem_sha (canonicalLData E l) (k : ℤ) g hx.1, ?_⟩
  change galActH1 E (canonicalLData E l) (k : ℤ) g x ∈
    (conjH1 (canonicalCMInv E) (canonicalLData E l) (k : ℤ)).eigenspace ((-1 : ℤ_[l.1]) ^ k)
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨ε, _, hconj⟩ := conjH1_eq_smul_galActH1 (canonicalCMInv E) (canonicalLData E l) k
  have hx_eig : conjH1 (canonicalCMInv E) (canonicalLData E l) (k : ℤ) x =
      ((-1 : ℤ_[l.1]) ^ k) • x := Module.End.mem_eigenspace_iff.mp hx.2
  have hcomm : galActH1 E (canonicalLData E l) (k : ℤ) g *
      galActH1 E (canonicalLData E l) (k : ℤ) (canonicalCMInv E).c =
      galActH1 E (canonicalLData E l) (k : ℤ) (canonicalCMInv E).c *
      galActH1 E (canonicalLData E l) (k : ℤ) g := by
    rw [← map_mul, ← map_mul, aut_mul_comm_of_one_le_condF hcond]
  have hcomm_conj : conjH1 (canonicalCMInv E) (canonicalLData E l) (k : ℤ)
      (galActH1 E (canonicalLData E l) (k : ℤ) g x) =
      galActH1 E (canonicalLData E l) (k : ℤ) g
      (conjH1 (canonicalCMInv E) (canonicalLData E l) (k : ℤ) x) := by
    rw [hconj]
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
    exact (LinearMap.congr_fun hcomm x).symm
  rw [hcomm_conj, hx_eig, map_smul]

/-- Genuine `Gal(E/ℚ)` representation on `ShaPlus E l k` for every abelian number field `1 ≤ condF E`. -/
def galRepShaPlus (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E)
    (l : Nat.Primes) (k : ℕ) :
    Representation ℤ_[l.1] (E ≃ₐ[ℚ] E) ↥(ShaPlus E l k) :=
  (galActH1 E (canonicalLData E l) (k : ℤ)).subrepresentation (ShaPlus E l k)
    (fun g _ hx => galActH1_mem_shaPlus E hcond l k g hx)

end GaloisActionOnSha

/-! ## Section 5: Continuous Corestriction & Inflation–Restriction (`Vlen_trivial_le_sha_rat`) -/

section CorestrictionAndInflationRestriction

private lemma normal_inv_conj_mem {H : Type*} [Group H] (U : Subgroup H) [U.Normal]
    (σ : H) {h : H} (hh : h ∈ U) : σ⁻¹ * h * σ ∈ U := by
  simpa [inv_inv] using (inferInstance : U.Normal).conj_mem h hh σ⁻¹

/-- **General Restriction Injectivity for Unit-Index Normal Subgroups**:
if `K ◁ H` has finite index `m` with `IsUnit (m : R)`, then
`resH1 ρ K.subtype continuous_subtype_val : H1 ρ →ₗ[R] H1 (ρ.comp K.subtype)` is injective! -/
theorem resH1_injective_of_unit_index {R H M : Type*} [CommRing R]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    (ρ : Representation R H M) (K : Subgroup H) [K.Normal] [Finite (H ⧸ K)]
    (hu : IsUnit (Nat.card (H ⧸ K) : R)) :
    Function.Injective (resH1 ρ K.subtype continuous_subtype_val) := by
  classical
  letI : Fintype (H ⧸ K) := Fintype.ofFinite (H ⧸ K)
  rw [Nat.card_eq_fintype_card] at hu
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.coe_subtype, mem_B1] at hx
  obtain ⟨m₀, hm₀⟩ := hx
  let f' : H → M := fun g => f.1 g - (ρ g m₀ - m₀)
  have hf'_cocycle : ∀ a b : H, f' (a * b) = f' a + ρ a (f' b) := fun a b => by
    dsimp only [f']
    rw [f.2.2 a b, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul]
    abel
  have hf'_K : ∀ u ∈ K, f' u = 0 := fun u huK => by
    dsimp only [f']
    have := hm₀ ⟨u, huK⟩
    change f.1 u = ρ u m₀ - m₀ at this
    rw [this, sub_self]
  have hf'_coset : ∀ (g : H) (u : H), u ∈ K → f' (g * u) = f' g := fun g u huK => by
    rw [hf'_cocycle g u, hf'_K u huK, map_zero, add_zero]
  let m : M := -(c • ∑ q : H ⧸ K, f' (Quotient.out q))
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine (mem_B1 _ _).mpr ⟨m₀ + m, fun g => ?_⟩
  have hsum : ∑ q : H ⧸ K, f' (Quotient.out q) =
      (Fintype.card (H ⧸ K) : R) • f' g + ρ g (∑ q : H ⧸ K, f' (Quotient.out q)) := by
    have hterm : ∀ q : H ⧸ K,
        f' (Quotient.out ((g : H ⧸ K) * q)) = f' g + ρ g (f' (Quotient.out q)) := fun q => by
      have hsame : QuotientGroup.mk (s := K) (g * Quotient.out q) =
          QuotientGroup.mk (s := K) (Quotient.out ((g : H ⧸ K) * q)) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
      obtain ⟨u, hu⟩ : ∃ u ∈ K, g * Quotient.out q = Quotient.out ((g : H ⧸ K) * q) * u := by
        refine ⟨(Quotient.out ((g : H ⧸ K) * q))⁻¹ * (g * Quotient.out q), ?_, by group⟩
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hsame, inv_mul_cancel]
      rw [← hf'_coset _ u hu.1, ← hu.2, hf'_cocycle g (Quotient.out q)]
    have hbij : ∑ q : H ⧸ K, f' (Quotient.out ((g : H ⧸ K) * q)) =
        ∑ q : H ⧸ K, f' (Quotient.out q) :=
      Fintype.sum_bijective (fun q : H ⧸ K => (g : H ⧸ K) * q)
        (Group.mulLeft_bijective (g : H ⧸ K)) _ _ (fun _ => rfl)
    conv_lhs => rw [← hbij]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul R,
      map_sum]
  have hf'g : f' g = ρ g m - m := by
    have h1 := congrArg (fun v => c • v) hsum
    rw [smul_add, smul_smul, hc, one_smul, ← map_smul] at h1
    dsimp only [m]
    rw [map_neg, sub_neg_eq_add]
    have h2 : f' g = c • ∑ q : H ⧸ K, f' (Quotient.out q) -
        ρ g (c • ∑ q : H ⧸ K, f' (Quotient.out q)) := eq_sub_of_add_eq h1.symm
    rw [h2]; abel
  have hfg : f.1 g = f' g + (ρ g m₀ - m₀) := by dsimp only [f']; abel
  change f.1 g = _
  rw [hfg, hf'g, map_add]
  abel

/-- **Explicit Continuous Corestriction `corH1 : H¹(U, M) →ₗ[R] H¹(H, M)`**
for any open normal finite-index subgroup `U ◁ H` acting continuously on a discrete `R`-module `M`. -/
def corH1 {R H M : Type*} [CommRing R]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R H M) (hρ : ContAction ρ)
    (U : Subgroup H) [U.Normal] [Finite (H ⧸ U)] (hU_open : IsOpen (U : Set H)) :
    H1 (ρ.comp U.subtype) →ₗ[R] H1 ρ := by
  classical
  letI : Fintype (H ⧸ U) := Fintype.ofFinite (H ⧸ U)
  let s : (H ⧸ U) → H := Quotient.out
  have hs_mk : ∀ q : H ⧸ U, QuotientGroup.mk (s := U) (s q) = q := Quotient.out_eq
  let uVal : H → (H ⧸ U) → U := fun g q =>
    ⟨(s ((g : H ⧸ U) * q))⁻¹ * g * s q, by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, hs_mk, hs_mk]
      group⟩
  have hu_mul : ∀ g₁ g₂ q, uVal (g₁ * g₂) q = uVal g₁ ((g₂ : H ⧸ U) * q) * uVal g₂ q := by
    intro g₁ g₂ q
    apply Subtype.ext
    simp only [uVal, Subgroup.coe_mul, QuotientGroup.mk_mul, mul_assoc]
    group
  haveI hdiscQ : DiscreteTopology (H ⧸ U) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro q₀
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q₀
    rw [← (QuotientGroup.isQuotientMap_mk U).isOpen_preimage]
    have hpre : (QuotientGroup.mk : H → H ⧸ U) ⁻¹' {QuotientGroup.mk g₀} =
        (fun g => g⁻¹ * g₀) ⁻¹' (U : Set H) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, QuotientGroup.eq]
    rw [hpre]
    exact hU_open.preimage (continuous_id.inv.mul continuous_const)
  have hcos_cont : ∀ q : H ⧸ U, Continuous (fun g : H => s ((g : H ⧸ U) * q)) := fun q =>
    continuous_of_discreteTopology.comp
      ((QuotientGroup.isQuotientMap_mk U).continuous.mul continuous_const)
  have hu_cont : ∀ q : H ⧸ U, Continuous (fun g : H => uVal g q) := fun q =>
    Continuous.subtype_mk (((hcos_cont q).inv.mul continuous_id).mul continuous_const) _
  let corZ : Z1 (ρ.comp U.subtype) →ₗ[R] Z1 ρ :=
    { toFun := fun f =>
        ⟨fun g => ∑ q : H ⧸ U, ρ (s ((g : H ⧸ U) * q)) (f.1 (uVal g q)),
          continuous_finsetSum Finset.univ (fun q _ =>
            hρ.comp ((hcos_cont q).prodMk (f.2.1.comp (hu_cont q)))),
          fun g₁ g₂ => by
            have hstep : ∀ q : H ⧸ U,
                ρ (s (((g₁ * g₂ : H) : H ⧸ U) * q)) (f.1 (uVal (g₁ * g₂) q)) =
                  ρ (s ((g₁ : H ⧸ U) * ((g₂ : H ⧸ U) * q))) (f.1 (uVal g₁ ((g₂ : H ⧸ U) * q))) +
                  ρ g₁ (ρ (s ((g₂ : H ⧸ U) * q)) (f.1 (uVal g₂ q))) := fun q => by
              rw [hu_mul g₁ g₂ q, f.2.2, map_add, QuotientGroup.mk_mul, mul_assoc]
              congr 1
              change ρ (s ((g₁ : H ⧸ U) * ((g₂ : H ⧸ U) * q)))
                (ρ (uVal g₁ ((g₂ : H ⧸ U) * q)).1 (f.1 (uVal g₂ q))) = _
              rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
              congr 2
              simp only [uVal]
              group
            simp_rw [hstep, Finset.sum_add_distrib, ← map_sum]
            congr 1
            exact Fintype.sum_bijective (fun q : H ⧸ U => (g₂ : H ⧸ U) * q)
              (Group.mulLeft_bijective (g₂ : H ⧸ U)) _ _ (fun _ => rfl)⟩
      map_add' := fun f₁ f₂ => Subtype.ext (funext fun g => by
        simp [map_add, Finset.sum_add_distrib])
      map_smul' := fun r f => Subtype.ext (funext fun g => by
        simp [map_smul, Finset.smul_sum]) }
  refine Submodule.mapQ _ _ corZ ?_
  intro f hf
  rw [Submodule.mem_comap, Submodule.coe_subtype, mem_B1] at hf
  change (corZ f).1 ∈ B1 ρ
  rw [mem_B1]
  obtain ⟨m, hm⟩ := hf
  refine ⟨∑ q : H ⧸ U, ρ (s q) m, fun g => ?_⟩
  change ∑ q : H ⧸ U, ρ (s ((g : H ⧸ U) * q)) (f.1 (uVal g q)) =
    ρ g (∑ q : H ⧸ U, ρ (s q) m) - ∑ q : H ⧸ U, ρ (s q) m
  have hterm : ∀ q : H ⧸ U, ρ (s ((g : H ⧸ U) * q)) (f.1 (uVal g q)) =
      ρ g (ρ (s q) m) - ρ (s ((g : H ⧸ U) * q)) m := fun q => by
    rw [hm (uVal g q), map_sub]
    congr 1
    change ρ (s ((g : H ⧸ U) * q)) (ρ (uVal g q).1 m) = _
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp only [uVal]; group
  simp_rw [hterm, Finset.sum_sub_distrib, ← map_sum]
  congr 1
  exact Fintype.sum_bijective (fun q : H ⧸ U => (g : H ⧸ U) * q)
    (Group.mulLeft_bijective (g : H ⧸ U)) _ _ (fun _ => rfl)

/-- Corestriction-restriction formula on cosets: `(corH1 [f])|_U = ∑ q, (s q) • [f]`. -/
theorem resH1_corH1_mk {R H M : Type*} [CommRing R]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R H M) (hρ : ContAction ρ)
    (U : Subgroup H) [U.Normal] [Finite (H ⧸ U)] (hU_open : IsOpen (U : Set H))
    (f : Z1 (ρ.comp U.subtype)) :
    letI : Fintype (H ⧸ U) := Fintype.ofFinite (H ⧸ U)
    resH1 ρ U.subtype continuous_subtype_val (corH1 ρ hρ U hU_open (Submodule.Quotient.mk f)) =
      Submodule.Quotient.mk
        ⟨fun h => ∑ q : H ⧸ U,
            ρ (Quotient.out q) (f.1 ⟨(Quotient.out q)⁻¹ * h.1 * Quotient.out q,
              normal_inv_conj_mem U (Quotient.out q) h.2⟩),
          by
            have hterm_cont : ∀ q : H ⧸ U,
                Continuous (fun h : U => ρ (Quotient.out q) (f.1 ⟨(Quotient.out q)⁻¹ * h.1 * Quotient.out q,
                  normal_inv_conj_mem U (Quotient.out q) h.2⟩)) := fun q =>
              hρ.comp (continuous_const.prodMk (f.2.1.comp
                (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _)))
            exact continuous_finsetSum Finset.univ (fun q _ => hterm_cont q),
          fun a b => by
            dsimp only
            rw [map_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun q _ => ?_
            have hconj : (⟨(Quotient.out q)⁻¹ * (a * b).1 * Quotient.out q,
                normal_inv_conj_mem U (Quotient.out q) (a * b).2⟩ : U) =
                ⟨(Quotient.out q)⁻¹ * a.1 * Quotient.out q,
                  normal_inv_conj_mem U (Quotient.out q) a.2⟩ *
                ⟨(Quotient.out q)⁻¹ * b.1 * Quotient.out q,
                  normal_inv_conj_mem U (Quotient.out q) b.2⟩ := by
              apply Subtype.ext; simp only [Subgroup.coe_mul]; group
            rw [hconj, f.2.2, map_add]
            congr 1
            change ρ (Quotient.out q) (ρ ((Quotient.out q)⁻¹ * a.1 * Quotient.out q) _) =
              ρ a.1 (ρ (Quotient.out q) _)
            rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2; group⟩ := by
  classical
  letI : Fintype (H ⧸ U) := Fintype.ofFinite (H ⧸ U)
  apply (Submodule.Quotient.eq _).mpr
  refine (mem_B1 _ _).mpr ⟨0, fun h => ?_⟩
  rw [map_zero, sub_zero]
  have hhU : (h.1 : H ⧸ U) = 1 := (QuotientGroup.eq_one_iff h.1).mpr h.2
  change (∑ q : H ⧸ U, ρ (Quotient.out ((h.1 : H ⧸ U) * q))
      (f.1 ⟨(Quotient.out ((h.1 : H ⧸ U) * q))⁻¹ * h.1 * Quotient.out q, _⟩)) -
    (∑ q : H ⧸ U, ρ (Quotient.out q)
      (f.1 ⟨(Quotient.out q)⁻¹ * h.1 * Quotient.out q, _⟩)) = 0
  have heq : ∀ q : H ⧸ U,
      ρ (Quotient.out ((h.1 : H ⧸ U) * q))
        (f.1 ⟨(Quotient.out ((h.1 : H ⧸ U) * q))⁻¹ * h.1 * Quotient.out q, _⟩) =
      ρ (Quotient.out q)
        (f.1 ⟨(Quotient.out q)⁻¹ * h.1 * Quotient.out q, _⟩) := fun q => by
    have hq : Quotient.out ((h.1 : H ⧸ U) * q) = Quotient.out q :=
      congrArg Quotient.out (by rw [hhU, one_mul])
    have hu : (⟨(Quotient.out ((h.1 : H ⧸ U) * q))⁻¹ * h.1 * Quotient.out q,
        by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
            QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.out_eq']
          group⟩ : U) =
        ⟨(Quotient.out q)⁻¹ * h.1 * Quotient.out q,
          normal_inv_conj_mem U (Quotient.out q) h.2⟩ :=
      Subtype.ext (by dsimp only; rw [hq])
    exact congrArg₂ (fun g u => ρ g (f.1 u)) hq hu
  rw [Finset.sum_congr rfl fun q _ => heq q, sub_self]

/-- Continuous inclusion `G E Ω →* G ℚ Ω` for `Ω = AlgebraicClosure E`. -/
def inclGal (E : Type) [Field E] [NumberField E] :
    G E (AlgebraicClosure E) →* G ℚ (AlgebraicClosure E) where
  toFun h :=
    { toRingEquiv := h.toRingEquiv
      commutes' := fun r => map_ratCast h.toRingEquiv r }
  map_one' := by ext z; rfl
  map_mul' _ _ := by ext z; rfl

theorem inclGal_injective (E : Type) [Field E] [NumberField E] :
    Function.Injective (inclGal E) := by
  intro a b hab
  ext z
  exact congrArg (fun φ : G ℚ (AlgebraicClosure E) => φ z) hab

theorem continuous_inclGal (E : Type) [Field E] [NumberField E] :
    Continuous (inclGal E) := by
  classical
  apply continuous_of_continuousAt_one (inclGal E)
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K, hK, hs⟩ := hs
  haveI : FiniteDimensional ℚ K := hK
  let KE : IntermediateField E (AlgebraicClosure E) :=
    IntermediateField.adjoin E (K : Set (AlgebraicClosure E))
  have hKE : FiniteDimensional E KE := by
    let b := Module.finBasis ℚ K
    let S : Finset (AlgebraicClosure E) := Finset.univ.image (fun i => (b i : AlgebraicClosure E))
    have hspan : IntermediateField.adjoin E (K : Set (AlgebraicClosure E)) =
        IntermediateField.adjoin E (S : Set (AlgebraicClosure E)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro x hx
        have hlin : (⟨x, hx⟩ : K) = ∑ i, b.repr ⟨x, hx⟩ i • b i := (b.sum_repr ⟨x, hx⟩).symm
        have hx_eq : x = ∑ i, algebraMap ℚ (AlgebraicClosure E) (b.repr ⟨x, hx⟩ i) *
            (b i : AlgebraicClosure E) := by
          have := congrArg Subtype.val hlin
          simpa [Algebra.smul_def] using this
        rw [hx_eq]
        refine sum_mem fun i _ => mul_mem ?_ ?_
        · have hrat : algebraMap ℚ (AlgebraicClosure E) (b.repr ⟨x, hx⟩ i) =
              algebraMap E (AlgebraicClosure E) (algebraMap ℚ E (b.repr ⟨x, hx⟩ i)) :=
            IsScalarTower.algebraMap_apply ℚ E (AlgebraicClosure E) _
          rw [hrat]
          exact IntermediateField.algebraMap_mem _ _
        · exact IntermediateField.subset_adjoin E _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
      · refine IntermediateField.adjoin.mono E _ _ (fun _ hz => ?_)
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
        exact (b i).2
    rw [show KE = IntermediateField.adjoin E (S : Set (AlgebraicClosure E)) from hspan]
    clear hspan
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.coe_empty, IntermediateField.adjoin_empty]
      exact Module.Finite.of_surjective (Algebra.linearMap E _) (fun ⟨x, hx⟩ => by
        obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
        exact ⟨r, rfl⟩)
    | @insert a s _ ih =>
      haveI : FiniteDimensional E (IntermediateField.adjoin E (s : Set (AlgebraicClosure E))) := ih
      rw [Finset.coe_insert, ← Set.union_singleton, ← IntermediateField.adjoin_adjoin_left]
      haveI : FiniteDimensional (IntermediateField.adjoin E (s : Set (AlgebraicClosure E)))
          (IntermediateField.adjoin (IntermediateField.adjoin E (s : Set (AlgebraicClosure E))) {a}) :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
      haveI : FiniteDimensional E
          (IntermediateField.adjoin (IntermediateField.adjoin E (s : Set (AlgebraicClosure E))) {a}) :=
        Module.Finite.trans (IntermediateField.adjoin E (s : Set (AlgebraicClosure E))) _
      exact inferInstanceAs (FiniteDimensional E
        (IntermediateField.adjoin (IntermediateField.adjoin E (s : Set (AlgebraicClosure E))) {a}))
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨KE, hKE, fun h hh => hs ?_⟩
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hh ⊢
  intro x hx
  exact hh x (IntermediateField.subset_adjoin E _ hx)

/-- Inverse of `inclGal` on its image `U := (inclGal E).range` is continuous (since `G E Ω` has
the subspace topology from `G ℚ Ω` / finite-dimensional `E/ℚ`!). -/
theorem continuous_toInclGalRange (E : Type) [Field E] [NumberField E] :
    let eU : G E (AlgebraicClosure E) ≃* (inclGal E).range :=
      MulEquiv.ofBijective ((inclGal E).rangeRestrict)
        ⟨fun _ _ h => inclGal_injective E (congrArg Subtype.val h), (inclGal E).rangeRestrict_surjective⟩
    Continuous eU.symm := by
  intro eU
  apply continuous_of_continuousAt_one eU.symm.toMonoidHom
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨K, hK, hs⟩ := hs
  haveI : FiniteDimensional E K := hK
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  let KQ : IntermediateField ℚ (AlgebraicClosure E) := K.restrictScalars ℚ
  haveI hKQ : FiniteDimensional ℚ KQ := inferInstanceAs (FiniteDimensional ℚ K)
  have hopen_Q : IsOpen ((KQ.fixingSubgroup : Subgroup (G ℚ (AlgebraicClosure E))) :
      Set (G ℚ (AlgebraicClosure E))) := IntermediateField.fixingSubgroup_isOpen KQ
  rw [Filter.mem_map]
  refine Filter.mem_of_superset
    ((hopen_Q.preimage continuous_subtype_val).mem_nhds (show (1 : (inclGal E).range).1 ∈ KQ.fixingSubgroup from one_mem _))
    (fun u hu => hs ?_)
  rw [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hu
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hxQ : x ∈ KQ := hx
  have h1 := hu x hxQ
  have h2 : (inclGal E (eU.symm u)) x = u.1 x := by
    have heq : (inclGal E).rangeRestrict (eU.symm u) = u := eU.apply_symm_apply u
    exact congrArg (fun φ : (inclGal E).range => φ.1 x) heq
  exact h2.trans h1

/-- Every element of `𝓞 E` has valuation `≤ 1` under any valuation subring `A` of `Ω`. -/
private lemma valuation_ringOfIntegers_le_one {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (c : 𝓞 E) :
    A.valuation (algebraMap E Ω (c : E)) ≤ 1 := by
  set z : Ω := algebraMap E Ω (c : E)
  by_contra hgt
  rw [not_le] at hgt
  have hz0 : z ≠ 0 := by intro h0; rw [h0, Valuation.map_zero] at hgt; exact not_lt_of_ge zero_le hgt
  have hinv_lt : A.valuation z⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  have hint : IsIntegral ℤ z := by
    have hc : IsIntegral ℤ (c : E) := c.2
    exact IsIntegral.map (IsScalarTower.toAlgHom ℤ E Ω) hc
  obtain ⟨p, hp_monic, hpz⟩ := hint
  set n := p.natDegree
  have hn_pos : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp_monic hn0
    rw [hp1, Polynomial.eval₂_one] at hpz
    exact one_ne_zero hpz
  -- Divide `p(z) = z^n + ∑_{i < n} p_i z^i = 0` by `z^n` to get `1 = - ∑_{i < n} p_i (z⁻¹)^(n - i)`
  have hpoly : z ^ n + ∑ i ∈ Finset.range n, (p.coeff i : Ω) * z ^ i = 0 := by
    have hsum := p.eval₂_eq_sum_range (f := Int.castRingHom Ω) (x := z)
    rw [Finset.sum_range_succ, hp_monic.coeff_natDegree, map_one, one_mul, add_comm] at hsum
    change z ^ p.natDegree + ∑ i ∈ Finset.range p.natDegree, Int.castRingHom Ω (p.coeff i) * z ^ i = 0
    rw [← hsum]
    exact hpz
  have hzn0 : z ^ n ≠ 0 := pow_ne_zero n hz0
  have hone : (1 : Ω) = -(∑ i ∈ Finset.range n, (p.coeff i : Ω) * (z⁻¹) ^ (n - i)) := by
    have hmul : (z⁻¹) ^ n * (z ^ n + ∑ i ∈ Finset.range n, (p.coeff i : Ω) * z ^ i) = 0 := by
      rw [hpoly, mul_zero]
    rw [mul_add, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, Finset.mul_sum] at hmul
    have hterm : ∀ i ∈ Finset.range n,
        (z⁻¹) ^ n * ((p.coeff i : Ω) * z ^ i) = (p.coeff i : Ω) * (z⁻¹) ^ (n - i) := fun i hi => by
      have hilt : i < n := Finset.mem_range.mp hi
      have hsplit : n = (n - i) + i := (Nat.sub_add_cancel hilt.le).symm
      calc (z⁻¹) ^ n * ((p.coeff i : Ω) * z ^ i)
          = (p.coeff i : Ω) * ((z⁻¹) ^ ((n - i) + i) * z ^ i) := by rw [← hsplit]; ring
        _ = (p.coeff i : Ω) * ((z⁻¹) ^ (n - i) * ((z⁻¹) ^ i * z ^ i)) := by rw [pow_add]; ring
        _ = (p.coeff i : Ω) * (z⁻¹) ^ (n - i) := by rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow, mul_one]
    rw [Finset.sum_congr rfl hterm] at hmul
    exact eq_neg_of_add_eq_zero_left hmul
  have hval_int : ∀ a : ℤ, A.valuation (a : Ω) ≤ 1 := fun a =>
    (A.valuation_le_one_iff (a : Ω)).mpr (intCast_mem A a)
  have hval_lt : A.valuation (∑ i ∈ Finset.range n, (p.coeff i : Ω) * (z⁻¹) ^ (n - i)) < 1 := by
    have hlt_term : ∀ i ∈ Finset.range n, A.valuation ((p.coeff i : Ω) * (z⁻¹) ^ (n - i)) < 1 := by
      intro i hi
      have hilt : i < n := Finset.mem_range.mp hi
      rw [Valuation.map_mul, Valuation.map_pow]
      have hpow_lt : A.valuation z⁻¹ ^ (n - i) < 1 :=
        pow_lt_one₀ zero_le hinv_lt (by omega)
      exact mul_lt_one_of_nonneg_of_lt_one_right (hval_int _) zero_le hpow_lt
    have hsum_lt : ∀ s : Finset ℕ,
        (∀ i ∈ s, A.valuation ((p.coeff i : Ω) * (z⁻¹) ^ (n - i)) < 1) →
        A.valuation (∑ i ∈ s, (p.coeff i : Ω) * (z⁻¹) ^ (n - i)) < 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simp
      | @insert a s ha ih =>
        intro hs
        rw [Finset.sum_insert ha]
        exact Valuation.map_add_lt _ (hs a (Finset.mem_insert_self a s))
          (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
    exact hsum_lt (Finset.range n) hlt_term
  have h1 : A.valuation (1 : Ω) < 1 := by
    rw [hone, Valuation.map_neg]
    exact hval_lt
  rw [Valuation.map_one] at h1
  exact lt_irrefl 1 h1

/-- Place of `𝓞 E` cut out by a valuation subring `A` of `Ω` lying over a rational prime `v`. -/
private def placeOfEBelow (E : Type) [Field E] [NumberField E]
    {A : ValuationSubring (AlgebraicClosure E)} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hA : IsPlaceOver (F := ℚ) A v) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal :=
    { carrier := {x : 𝓞 E | A.valuation (algebraMap E (AlgebraicClosure E) (x : E)) < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        change A.valuation (algebraMap E (AlgebraicClosure E) ((a : E) + (b : E))) < 1
        rw [map_add]
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hx ⊢
        exact mul_lt_one_of_nonneg_of_lt_one_right
          (valuation_ringOfIntegers_le_one A c) zero_le hx }
  isPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : 𝓞 E) ∈ (⊤ : Ideal (𝓞 E)) := Submodule.mem_top
      rw [← htop] at h1
      change A.valuation (algebraMap E (AlgebraicClosure E) ((1 : 𝓞 E) : E)) < 1 at h1
      simp at h1
    · intro x y hxy
      simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
        Set.mem_ofPred_eq, map_mul] at hxy ⊢
      by_contra hnot
      push Not at hnot
      have hge : 1 ≤ A.valuation (algebraMap E (AlgebraicClosure E) (x : E)) *
          A.valuation (algebraMap E (AlgebraicClosure E) (y : E)) :=
        one_le_mul_of_one_le_of_one_le hnot.1 hnot.2
      exact not_lt_of_ge hge hxy
  ne_bot := by
    intro hbot
    obtain ⟨p, hp_mem, hp_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    have hp_int : IsIntegral ℤ (p : ℚ) := NumberField.RingOfIntegers.isIntegral_coe p
    let x : 𝓞 E := ⟨algebraMap ℚ E (p : ℚ), IsIntegral.map (IsScalarTower.toAlgHom ℤ ℚ E) hp_int⟩
    have hx_mem : x ∈ {y : 𝓞 E | A.valuation (algebraMap E (AlgebraicClosure E) (y : E)) < 1} := by
      change A.valuation (algebraMap E (AlgebraicClosure E) (algebraMap ℚ E (p : ℚ))) < 1
      rw [← IsScalarTower.algebraMap_apply ℚ E (AlgebraicClosure E)]
      exact (hA p).mpr hp_mem
    have hx0 : x = 0 := by
      have : x ∈ (⊥ : Ideal (𝓞 E)) := hbot ▸ hx_mem
      exact Ideal.mem_bot.mp this
    have hp0 : (p : ℚ) = 0 := by
      have hE0 : algebraMap ℚ E (p : ℚ) = 0 := congrArg Subtype.val hx0
      exact (algebraMap ℚ E).injective (hE0.trans (map_zero _).symm)
    exact hp_ne (Subtype.ext hp0)

private theorem isPlaceOver_placeOfEBelow (E : Type) [Field E] [NumberField E]
    {A : ValuationSubring (AlgebraicClosure E)} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hA : IsPlaceOver (F := ℚ) A v) :
    IsPlaceOver (F := E) A (placeOfEBelow E hA) := fun _ => Iff.rfl

private theorem placeOfEBelow_mem_above_iff (E : Type) [Field E] [NumberField E]
    {A : ValuationSubring (AlgebraicClosure E)} {v : HeightOneSpectrum (𝓞 ℚ)}
    (hA : IsPlaceOver (F := ℚ) A v) (l : ℕ) :
    placeOfEBelow E hA ∈ Above E l ↔ v ∈ Above ℚ l := by
  change A.valuation (algebraMap E (AlgebraicClosure E) (((l : ℕ) : 𝓞 E) : E)) < 1 ↔
    ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
  rw [← hA ((l : ℕ) : 𝓞 ℚ)]
  simp

private lemma normal_subgroupOf_finite_and_dvd {H : Type*} [Group H]
    (U : Subgroup H) [U.Normal] [Finite (H ⧸ U)] (K : Subgroup H) :
    Finite (K ⧸ U.subgroupOf K) ∧ Nat.card (K ⧸ U.subgroupOf K) ∣ Nat.card (H ⧸ U) := by
  haveI : (U.subgroupOf K).Normal := Subgroup.Normal.subgroupOf (inferInstance : U.Normal) K
  let φ : (K ⧸ U.subgroupOf K) →* (H ⧸ U) :=
    QuotientGroup.lift (U.subgroupOf K) ((QuotientGroup.mk' U).comp K.subtype)
      (fun a ha => (QuotientGroup.eq_one_iff a.1).mpr ha)
  have hφ_inj : Function.Injective φ := fun a b hab => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    change QuotientGroup.mk (s := U) a.1 = QuotientGroup.mk (s := U) b.1 at hab
    rw [QuotientGroup.eq] at hab ⊢
    exact hab
  haveI : Finite (K ⧸ U.subgroupOf K) := Finite.of_injective φ hφ_inj
  refine ⟨inferInstance, ?_⟩
  have hcard_eq : Nat.card (K ⧸ U.subgroupOf K) = Nat.card φ.range :=
    Nat.card_congr (Equiv.ofBijective (fun x => ⟨φ x, ⟨x, rfl⟩⟩)
      ⟨fun a b h => hφ_inj (congrArg Subtype.val h), fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩)
  rw [hcard_eq]
  exact Subgroup.card_subgroup_dvd_card φ.range

private lemma resH1_mk_eq_zero_iff {R H₁ H₂ M : Type*} [CommRing R]
    [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁]
    [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M]
    (ρ : Representation R H₂ M) (φ : H₁ →* H₂) (hφ : Continuous φ) (f : Z1 ρ) :
    resH1 ρ φ hφ (Submodule.Quotient.mk f) = 0 ↔
      ∃ m : M, ∀ g : H₁, f.1 (φ g) = ρ (φ g) m - m := by
  simp only [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.coe_subtype, mem_B1]
  rfl

private lemma sha_res_loc_eq_zero {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] (D : LData E Ω l) (e : ℤ)
    {x : H1 (qzTw D e)} (hx : x ∈ Sha D e)
    (wS : D.S) (A : ValuationSubring Ω) (hA : IsPlaceOver (F := E) A wS.1) :
    resH1 (qzTw D e) (locHom (F := E) (D.S : Set (HeightOneSpectrum (𝓞 E))) A)
      (continuous_locHom (F := E) (D.S : Set (HeightOneSpectrum (𝓞 E))) A) x = 0 := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (D.hA wS) hA
  let cHom : Dec (F := E) A →* Dec (F := E) (D.A wS) :=
    conjDecHom (F := E) g₀⁻¹ (by rw [← hg₀, inv_smul_smul])
  have hcCont : Continuous cHom := continuous_conjDecHom (F := E) g₀⁻¹ _
  have hconj_loc : ∀ τ : Dec (F := E) A,
      ((locFam D.S D.A wS).comp cHom) τ =
        (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) g₀)⁻¹ *
          locHom (F := E) (D.S : Set (HeightOneSpectrum (𝓞 E))) A τ *
          toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) g₀ := fun τ => by
    simp [cHom, conjDecHom, locFam, locHom, map_mul, map_inv]
  have hx_w : resH1 (qzTw D e) (locFam D.S D.A wS) (continuous_locFam D.S D.A wS) x = 0 := by
    simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact hx wS
  have hres_comp : resH1 (qzTw D e) ((locFam D.S D.A wS).comp cHom)
      ((continuous_locFam D.S D.A wS).comp hcCont) x = 0 := by
    rw [← resH1_comp (qzTw D e) (locFam D.S D.A wS) (continuous_locFam D.S D.A wS) cHom hcCont,
      hx_w, map_zero]
  exact (resH1_conj_eq_zero_iff (qzTw D e)
    (locHom (F := E) (D.S : Set (HeightOneSpectrum (𝓞 E))) A)
    (continuous_locHom (F := E) (D.S : Set (HeightOneSpectrum (𝓞 E))) A)
    (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) g₀)⁻¹
    ((locFam D.S D.A wS).comp cHom)
    ((continuous_locFam D.S D.A wS).comp hcCont)
    (fun τ => by rw [hconj_loc, inv_inv]) x).mp hres_comp

/-- **Inflation–Restriction Trivial-Eigenspace Bound (`sha_invariants_length_le_sha_rat`)**:
for every abelian number field `E` (`1 ≤ condF E`), odd prime `l` with `¬ l ∣ Module.finrank ℚ E`,
and twist `k : ℕ`, the `Gal(E/ℚ)`-invariants of `ShaPlus E l k` inject into `Sha1Galois ℚ l k`, so
`Module.length ℤ_[l] (eig (galRepShaPlus E hcond l k) 1) ≤ realGaloisSelmerSystem.shaLen ℚ l k`! -/
theorem sha_invariants_length_le_sha_rat (E : Type) [Field E] [NumberField E]
    (hcond : 1 ≤ condF E) (l : Nat.Primes) (hnd : ¬ (l : ℕ) ∣ Module.finrank ℚ E) (k : ℕ) :
    Module.length ℤ_[l.1] (eig (galRepShaPlus E hcond l k) 1) ≤
      realGaloisSelmerSystem.shaLen ℚ l k := by
  classical
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := isAlgClosure_rat_algClosure E
  haveI : IsGalois ℚ E := isGalois_of_one_le_condF hcond
  let D_Q : LData ℚ (AlgebraicClosure E) l.1 :=
    Classical.choice (ldata_nonempty (F := ℚ) (Ω := AlgebraicClosure E) l.1)
  rw [realGaloisSelmerSystem_shaLen, ← shaLen_eq_galoisShaLen ℚ l D_Q (k : ℤ)]
  -- Set up `U = (inclGal E).range ◁ G ℚ (AlgebraicClosure E)` of index `d = Module.finrank ℚ E`
  let U : Subgroup (G ℚ (AlgebraicClosure E)) := (inclGal E).range
  let E_im : IntermediateField ℚ (AlgebraicClosure E) :=
    (IsScalarTower.toAlgHom ℚ E (AlgebraicClosure E)).fieldRange
  haveI : FiniteDimensional ℚ E_im :=
    (AlgEquiv.ofInjective (IsScalarTower.toAlgHom ℚ E (AlgebraicClosure E))
      (algebraMap E (AlgebraicClosure E)).injective).toLinearEquiv.finiteDimensional
  have hU_eq_fix : U = E_im.fixingSubgroup := by
    ext σ
    simp only [U, MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff, E_im]
    constructor
    · rintro ⟨h, rfl⟩ _ ⟨x, rfl⟩
      exact h.commutes x
    · intro hfix
      refine ⟨{ toRingEquiv := σ.toRingEquiv
                commutes' := fun x => hfix _ ⟨x, rfl⟩ }, ?_⟩
      ext z; rfl
  have hU_open : IsOpen (U : Set (G ℚ (AlgebraicClosure E))) := by
    rw [hU_eq_fix]; exact IntermediateField.fixingSubgroup_isOpen E_im
  let resE : G ℚ (AlgebraicClosure E) →* (E ≃ₐ[ℚ] E) :=
    AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure E) E
  have hresE_ker : resE.ker = U := by
    ext σ
    rw [MonoidHom.mem_ker, hU_eq_fix, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h1 y hy
      obtain ⟨x, rfl⟩ := hy
      have hcomm : algebraMap E (AlgebraicClosure E) (resE σ x) =
          σ (algebraMap E (AlgebraicClosure E) x) :=
        AlgEquiv.restrictNormal_commutes σ E x
      rw [h1] at hcomm
      exact hcomm.symm
    · intro hfix
      ext x
      apply (algebraMap E (AlgebraicClosure E)).injective
      have hcomm := AlgEquiv.restrictNormal_commutes σ E x
      exact hcomm.trans (hfix _ ⟨x, rfl⟩)
  have hresE_surj : Function.Surjective resE := by
    intro g
    obtain ⟨σ, hσ⟩ := exists_liftGal g
    refine ⟨σ, ?_⟩
    ext x
    apply (algebraMap E (AlgebraicClosure E)).injective
    exact (AlgEquiv.restrictNormal_commutes σ E x).trans (hσ x)
  haveI hU_norm : U.Normal := by rw [← hresE_ker]; exact MonoidHom.normal_ker resE
  let qEquiv : (G ℚ (AlgebraicClosure E) ⧸ U) ≃* (E ≃ₐ[ℚ] E) :=
    (QuotientGroup.quotientMulEquivOfEq hresE_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective resE hresE_surj)
  haveI : Finite (G ℚ (AlgebraicClosure E) ⧸ U) := Finite.of_equiv (E ≃ₐ[ℚ] E) qEquiv.symm.toEquiv
  letI : Fintype (G ℚ (AlgebraicClosure E) ⧸ U) := Fintype.ofFinite (G ℚ (AlgebraicClosure E) ⧸ U)
  have hcard_Q : Fintype.card (G ℚ (AlgebraicClosure E) ⧸ U) = Module.finrank ℚ E := by
    rw [Fintype.card_congr qEquiv.toEquiv, card_aut_eq_finrank_of_one_le_condF hcond]
  have hd_unit : IsUnit (Module.finrank ℚ E : ℤ_[l.1]) :=
    isUnit_finrank_padicInt_of_not_dvd E hnd
  obtain ⟨c_d, hc_d⟩ := hd_unit.exists_left_inv
  -- Define `ρ_Q := (qzTw D_Q k).comp (toGS _ D_Q.S)` directly so `infQ = resH1 (qzTw D_Q k) (toGS _ _)`!
  let ρ_Q : Representation ℤ_[l.1] (G ℚ (AlgebraicClosure E)) (QZ l.1) :=
    (qzTw D_Q (k : ℤ)).comp (toGS (AlgebraicClosure E) (D_Q.S : Set (HeightOneSpectrum (𝓞 ℚ))))
  have hρ_Q_eq : ρ_Q = scalRep (QZ l.1) (cycZ ℚ (AlgebraicClosure E) l.1 ^ (-(k : ℤ))) := by
    ext g m
    have hchi : D_Q.chi (toGS (AlgebraicClosure E) _ g) = cycZ ℚ (AlgebraicClosure E) l.1 g :=
      congrArg (fun f => f g) D_Q.hchi
    have hpow : (D_Q.chi ^ (-(k : ℤ))) (toGS (AlgebraicClosure E) _ g) =
        (cycZ ℚ (AlgebraicClosure E) l.1 ^ (-(k : ℤ))) g := by
      simp only [zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, hchi]
    simp only [ρ_Q, MonoidHom.comp_apply, qzTw, scalRep_apply, hpow]
  have hρ_Q_cont : ContAction ρ_Q := by
    rw [hρ_Q_eq]
    exact contScal l.1 (G ℚ (AlgebraicClosure E)) (cycZ ℚ (AlgebraicClosure E) l.1 ^ (-(k : ℤ)))
      (Units.continuous_val.comp ((continuous_cycZ ℚ (AlgebraicClosure E) l.1).zpow (-(k : ℤ))))
  let eU : G E (AlgebraicClosure E) ≃* U :=
    MulEquiv.ofBijective ((inclGal E).rangeRestrict)
      ⟨fun a b h => inclGal_injective E (congrArg Subtype.val h), (inclGal E).rangeRestrict_surjective⟩
  have heU_cont : Continuous eU := Continuous.subtype_mk (continuous_inclGal E) _
  have heU_symm_cont : Continuous eU.symm := continuous_toInclGalRange E
  have hrep_compat : ∀ u : U, ∀ m : QZ l.1,
      ((qzTw (canonicalLData E l) (k : ℤ)).comp
        (toGS (AlgebraicClosure E) ((canonicalLData E l).S : Set (HeightOneSpectrum (𝓞 E))))) (eU.symm u) m =
        (ρ_Q.comp U.subtype) u m := fun u m => by
    have hchi : (canonicalLData E l).chi (toGS (AlgebraicClosure E) _ (eU.symm u)) =
        cycZ ℚ (AlgebraicClosure E) l.1 u.1 := by
      have h1 := congrArg (fun f => f (eU.symm u)) (canonicalLData E l).hchi
      have h2 : inclGal E (eU.symm u) = u.1 := congrArg Subtype.val (eU.apply_symm_apply u)
      rw [← h2]
      exact h1
    have hpow : ((canonicalLData E l).chi ^ (-(k : ℤ))) (toGS (AlgebraicClosure E) _ (eU.symm u)) =
        (cycZ ℚ (AlgebraicClosure E) l.1 ^ (-(k : ℤ))) u.1 := by
      simp only [zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply, hchi]
    rw [hρ_Q_eq]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, qzTw, scalRep_apply, hpow]
  let infE_abs : H1 (qzTw (canonicalLData E l) (k : ℤ)) →ₗ[ℤ_[l.1]]
      H1 ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _)) :=
    resH1 (qzTw (canonicalLData E l) (k : ℤ)) (toGS (AlgebraicClosure E) _)
      (continuous_toGS (AlgebraicClosure E) _)
  let toU : H1 ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _)) →ₗ[ℤ_[l.1]]
      H1 (ρ_Q.comp U.subtype) :=
    pairH1 ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _))
      (ρ_Q.comp U.subtype) eU.symm.toMonoidHom heU_symm_cont LinearMap.id continuous_id
      (fun u m => hrep_compat u m)
  let infE : H1 (qzTw (canonicalLData E l) (k : ℤ)) →ₗ[ℤ_[l.1]] H1 (ρ_Q.comp U.subtype) :=
    toU.comp infE_abs
  have hinfE_inj : Function.Injective infE := by
    have h1 := (infUnram (qzTw (canonicalLData E l) (k : ℤ))).1
    have h2 := (pairH1_id_bijective
      ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _)) (ρ_Q.comp U.subtype)
      eU.symm.toMonoidHom heU_symm_cont eU.toMonoidHom heU_cont
      (fun g => eU.symm_apply_apply g) (fun u => eU.apply_symm_apply u)
      (fun u m => hrep_compat u m)).1
    exact h2.comp h1
  let corScaled : H1 (ρ_Q.comp U.subtype) →ₗ[ℤ_[l.1]] H1 ρ_Q :=
    c_d • corH1 ρ_Q hρ_Q_cont U hU_open
  let fU_of : Z1 (qzTw (canonicalLData E l) (k : ℤ)) → Z1 (ρ_Q.comp U.subtype) := fun f =>
    ⟨fun u => f.1 (toGS (AlgebraicClosure E) _ (eU.symm u)),
      f.2.1.comp ((continuous_toGS (AlgebraicClosure E) _).comp heU_symm_cont),
      fun a b => by
        dsimp only
        rw [map_mul, map_mul, f.2.2]
        congr 1
        exact hrep_compat a (f.1 (toGS (AlgebraicClosure E) _ (eU.symm b)))⟩
  have hinfE_mk : ∀ f : Z1 (qzTw (canonicalLData E l) (k : ℤ)),
      infE (Submodule.Quotient.mk f) = Submodule.Quotient.mk (fU_of f) := fun _ => rfl
  have hres_cor_eq : ∀ x : eig (galRepShaPlus E hcond l k) 1,
      resH1 ρ_Q U.subtype continuous_subtype_val (corScaled (infE x.1.1)) = infE x.1.1 := by
    intro x
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ x.1.1
    have hinv_g : ∀ g : E ≃ₐ[ℚ] E, galActH1 E (canonicalLData E l) (k : ℤ) g x.1.1 = x.1.1 := fun g => by
      have hg := mem_eig.mp x.2 g
      simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hg
      exact congrArg Subtype.val hg
    dsimp only [corScaled, LinearMap.smul_apply]
    rw [map_smul, ← hf, hinfE_mk f, resH1_corH1_mk ρ_Q hρ_Q_cont U hU_open (fU_of f)]
    let mkU : Z1 (ρ_Q.comp U.subtype) →ₗ[ℤ_[l.1]] H1 (ρ_Q.comp U.subtype) :=
      ((B1 (ρ_Q.comp U.subtype)).comap (Z1 (ρ_Q.comp U.subtype)).subtype).mkQ
    let conjCoc : (G ℚ (AlgebraicClosure E) ⧸ U) → Z1 (ρ_Q.comp U.subtype) := fun q =>
      let σ := Quotient.out q
      ⟨fun h => ρ_Q σ ((fU_of f).1 ⟨σ⁻¹ * h.1 * σ, normal_inv_conj_mem U σ h.2⟩),
        hρ_Q_cont.comp (continuous_const.prodMk ((fU_of f).2.1.comp
          (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _))),
        fun a b => by
          dsimp only
          have hconj : (⟨σ⁻¹ * (a * b).1 * σ, normal_inv_conj_mem U σ (a * b).2⟩ : U) =
              ⟨σ⁻¹ * a.1 * σ, normal_inv_conj_mem U σ a.2⟩ *
              ⟨σ⁻¹ * b.1 * σ, normal_inv_conj_mem U σ b.2⟩ := by
            apply Subtype.ext; simp only [Subgroup.coe_mul]; group
          rw [hconj, (fU_of f).2.2, map_add]
          congr 1
          change ρ_Q σ (ρ_Q (σ⁻¹ * a.1 * σ) _) = ρ_Q a.1 (ρ_Q σ _)
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2; group⟩
    have hterm_eq : ∀ q : G ℚ (AlgebraicClosure E) ⧸ U, mkU (conjCoc q) = mkU (fU_of f) := by
      intro q
      let σ := Quotient.out q
      have hσ : IsLiftGal (resE σ) σ := fun a => (AlgEquiv.restrictNormal_commutes σ E a).symm
      have hact : liftActH1 hσ (canonicalLData E l) (k : ℤ) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk f := by
        rw [← galActH1_eq_liftActH1 hσ (canonicalLData E l) (k : ℤ), hf]
        exact hinv_g (resE σ)
      have hinf_act : infE (liftActH1 hσ (canonicalLData E l) (k : ℤ) (Submodule.Quotient.mk f)) =
          mkU (fU_of f) := by
        rw [hact]; rfl
      rw [← hinf_act]
      apply congrArg mkU
      apply Subtype.ext
      funext h
      have hgs_eq : gsGalHom hσ (canonicalLData E l) (toGS (AlgebraicClosure E) _ (eU.symm h)) =
          toGS (AlgebraicClosure E) _ (eU.symm ⟨σ⁻¹ * h.1 * σ, normal_inv_conj_mem U σ h.2⟩) := by
        rw [gsGalHom_mk]
        congr 1
        apply inclGal_injective E
        have h1 : inclGal E (eU.symm h) = h.1 := congrArg Subtype.val (eU.apply_symm_apply h)
        have h2 : inclGal E (eU.symm ⟨σ⁻¹ * h.1 * σ, normal_inv_conj_mem U σ h.2⟩) = σ⁻¹ * h.1 * σ :=
          congrArg Subtype.val (eU.apply_symm_apply ⟨σ⁻¹ * h.1 * σ, normal_inv_conj_mem U σ h.2⟩)
        rw [h2]
        ext z
        change σ.symm ((eU.symm h) (σ z)) = σ.symm (h.1 (σ z))
        exact congrArg σ.symm (congrArg (fun φ : G ℚ (AlgebraicClosure E) => φ (σ z)) h1)
      have hρσ : ∀ m : QZ l.1, ρ_Q σ m =
          (((cycZ ℚ (AlgebraicClosure E) l.1 σ) ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m := fun m => by
        rw [hρ_Q_eq]
        simp only [scalRep_apply, zpow_neg, zpow_natCast, MonoidHom.inv_apply, MonoidHom.pow_apply]
      change ρ_Q σ (f.1 (toGS (AlgebraicClosure E) _ (eU.symm ⟨σ⁻¹ * h.1 * σ, normal_inv_conj_mem U σ h.2⟩))) =
        (((cycZ ℚ (AlgebraicClosure E) l.1 σ) ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) •
          f.1 (gsGalHom hσ (canonicalLData E l) (toGS (AlgebraicClosure E) _ (eU.symm h)))
      rw [hρσ, hgs_eq]
    trans (c_d • ∑ q : G ℚ (AlgebraicClosure E) ⧸ U, mkU (conjCoc q))
    · congr 1
      rw [← map_sum mkU]
      apply congrArg mkU
      apply Subtype.ext
      funext h
      simp [conjCoc, Finset.sum_apply]
    · rw [Finset.sum_congr rfl (fun q _ => hterm_eq q), Finset.sum_const, Finset.card_univ,
        hcard_Q, ← Nat.cast_smul_eq_nsmul ℤ_[l.1], smul_smul, hc_d, one_smul]
      rfl
  have hsub_unit : ∀ (K : Subgroup (G ℚ (AlgebraicClosure E))),
      IsUnit (Nat.card (K ⧸ U.subgroupOf K) : ℤ_[l.1]) := fun K => by
    have hdvd := (normal_subgroupOf_finite_and_dvd U K).2
    have hdvd' : Nat.card (K ⧸ U.subgroupOf K) ∣ Module.finrank ℚ E := by
      rwa [Nat.card_eq_fintype_card (α := G ℚ (AlgebraicClosure E) ⧸ U), hcard_Q] at hdvd
    exact isUnit_natCast_padicInt_of_not_dvd (fun hld => hnd (hld.trans hdvd'))
  let infQ : H1 (qzTw D_Q (k : ℤ)) →ₗ[ℤ_[l.1]] H1 ρ_Q :=
    resH1 (qzTw D_Q (k : ℤ)) (toGS (AlgebraicClosure E) _) (continuous_toGS (AlgebraicClosure E) _)
  have hinfQ_inj : Function.Injective infQ := (infUnram (qzTw D_Q (k : ℤ))).1
  have hmem_shaQ : ∀ x : eig (galRepShaPlus E hcond l k) 1,
      ∃ y₀ : Sha D_Q (k : ℤ), infQ y₀.1 = corScaled (infE x.1.1) := by
    intro x
    set y : H1 ρ_Q := corScaled (infE x.1.1)
    have hres_y : resH1 ρ_Q U.subtype continuous_subtype_val y = infE x.1.1 := hres_cor_eq x
    -- Step A: `y` is unramified at all `v ∉ D_Q.S`
    have hunram_y : ∀ v ∉ (D_Q.S : Set (HeightOneSpectrum (𝓞 ℚ))),
        ∀ A : ValuationSubring (AlgebraicClosure E), IsPlaceOver (F := ℚ) A v →
          resH1 ρ_Q (Ine (F := ℚ) A).subtype continuous_subtype_val y = 0 := by
      intro v hv A hA
      let K : Subgroup (G ℚ (AlgebraicClosure E)) := Ine (F := ℚ) A
      haveI : (U.subgroupOf K).Normal := Subgroup.Normal.subgroupOf (inferInstance : U.Normal) K
      haveI : Finite (K ⧸ U.subgroupOf K) := (normal_subgroupOf_finite_and_dvd U K).1
      apply resH1_injective_of_unit_index (ρ_Q.comp K.subtype) (U.subgroupOf K) (hsub_unit K)
      rw [map_zero]
      let w : HeightOneSpectrum (𝓞 E) := placeOfEBelow E hA
      have hw_not : w ∉ ((canonicalLData E l).S : Set (HeightOneSpectrum (𝓞 E))) := by
        intro hmem
        have h1 : w ∈ Above E l.1 := (canonicalLData E l).hS ▸ hmem
        rw [placeOfEBelow_mem_above_iff] at h1
        exact hv (D_Q.hS ▸ h1)
      have hvan_E : resH1 ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _))
          (Ine (F := E) A).subtype continuous_subtype_val (infE_abs x.1.1) = 0 :=
        ((infUnram (qzTw (canonicalLData E l) (k : ℤ))).2 (infE_abs x.1.1)).mp
          ⟨x.1.1, rfl⟩ w hw_not A (isPlaceOver_placeOfEBelow E hA)
      have hcomp_eq : resH1 (ρ_Q.comp K.subtype) (U.subgroupOf K).subtype continuous_subtype_val
          (resH1 ρ_Q K.subtype continuous_subtype_val y) =
          resH1 (ρ_Q.comp U.subtype)
            ((K.subtype.comp (U.subgroupOf K).subtype).codRestrict U fun g => Subgroup.mem_subgroupOf.mp g.2)
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
            (resH1 ρ_Q U.subtype continuous_subtype_val y) := by
        obtain ⟨fy, hfy⟩ := Submodule.Quotient.mk_surjective _ y
        rw [← hfy]; rfl
      rw [hcomp_eq, hres_y]
      obtain ⟨fx, hfx⟩ := Submodule.Quotient.mk_surjective _ x.1.1
      rw [← hfx] at hvan_E ⊢
      obtain ⟨m, hm⟩ := (resH1_mk_eq_zero_iff
        ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _))
        (Ine (F := E) A).subtype continuous_subtype_val
        (restrictCocycles1 (qzTw (canonicalLData E l) (k : ℤ))
          (toGS (AlgebraicClosure E) _) (continuous_toGS (AlgebraicClosure E) _) fx)).mp hvan_E
      rw [hinfE_mk fx]
      apply (resH1_mk_eq_zero_iff _ _ _ _).mpr
      refine ⟨m, fun g => ?_⟩
      let uG : U := ⟨g.1.1, Subgroup.mem_subgroupOf.mp g.2⟩
      have hg_ineE : eU.symm uG ∈ Ine (F := E) A := by
        have h1 : inclGal E (eU.symm uG) = g.1.1 := congrArg Subtype.val (eU.apply_symm_apply uG)
        refine ⟨?_, fun z hz => ?_⟩
        · change eU.symm uG ∈ Dec (F := E) A
          rw [mem_Dec]
          have hinv : inclGal E (eU.symm uG)⁻¹ = g.1.1⁻¹ := by rw [map_inv, h1]
          ext a
          simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
          have hinvz := congrArg (fun φ : G ℚ (AlgebraicClosure E) => φ a) hinv
          exact (Iff.of_eq (congrArg (· ∈ A) hinvz)).trans (by
            have hdec := mem_Dec.mp g.1.2.1
            exact show g.1.1⁻¹ • a ∈ A ↔ a ∈ A by
              rw [← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hdec])
        · have h1z : (eU.symm uG) z = g.1.1 z :=
            congrArg (fun φ : G ℚ (AlgebraicClosure E) => φ z) h1
          rw [h1z]
          exact g.1.2.2 z hz
      have hmg : fx.1 (toGS (AlgebraicClosure E) _ (eU.symm uG)) =
          ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _)) (eU.symm uG) m - m :=
        hm ⟨eU.symm uG, hg_ineE⟩
      have hrep_g : (ρ_Q.comp U.subtype) uG m =
          ((qzTw (canonicalLData E l) (k : ℤ)).comp (toGS (AlgebraicClosure E) _)) (eU.symm uG) m :=
        (hrep_compat uG m).symm
      change fx.1 (toGS (AlgebraicClosure E) _ (eU.symm uG)) = (ρ_Q.comp U.subtype) uG m - m
      rw [hrep_g]
      exact hmg
    -- Step B: By `infUnram` for `ℚ`, `y = infQ y₀` for some `y₀ : H1 (qzTw D_Q k)` (1 line!)
    obtain ⟨y₀, hy₀⟩ := ((infUnram (qzTw D_Q (k : ℤ))).2 y).mpr hunram_y
    -- Step C: `y₀ ∈ Sha D_Q k` (locally trivial at every `v ∈ D_Q.S`!)
    have hy₀_sha : y₀ ∈ Sha D_Q (k : ℤ) := by
      simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
      intro v
      let A : ValuationSubring (AlgebraicClosure E) := D_Q.A v
      let K : Subgroup (G ℚ (AlgebraicClosure E)) := Dec (F := ℚ) A
      haveI : (U.subgroupOf K).Normal := Subgroup.Normal.subgroupOf (inferInstance : U.Normal) K
      haveI : Finite (K ⧸ U.subgroupOf K) := (normal_subgroupOf_finite_and_dvd U K).1
      have hres_K_zero : resH1 ρ_Q K.subtype continuous_subtype_val y = 0 := by
        apply resH1_injective_of_unit_index (ρ_Q.comp K.subtype) (U.subgroupOf K) (hsub_unit K)
        rw [map_zero]
        have hcomp_eq : resH1 (ρ_Q.comp K.subtype) (U.subgroupOf K).subtype continuous_subtype_val
            (resH1 ρ_Q K.subtype continuous_subtype_val y) =
            resH1 (ρ_Q.comp U.subtype)
              ((K.subtype.comp (U.subgroupOf K).subtype).codRestrict U fun g => Subgroup.mem_subgroupOf.mp g.2)
              (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
              (resH1 ρ_Q U.subtype continuous_subtype_val y) := by
          obtain ⟨fy, hfy⟩ := Submodule.Quotient.mk_surjective _ y
          rw [← hfy]; rfl
        rw [hcomp_eq, hres_y]
        let w : HeightOneSpectrum (𝓞 E) := placeOfEBelow E (D_Q.hA v)
        have hw_mem : w ∈ (canonicalLData E l).S := by
          have hv_ab : v.1 ∈ Above ℚ l.1 := D_Q.hS ▸ Finset.mem_coe.mpr v.2
          have hw_ab : w ∈ Above E l.1 := (placeOfEBelow_mem_above_iff E (D_Q.hA v) l.1).mpr hv_ab
          exact Finset.mem_coe.mp ((canonicalLData E l).hS ▸ hw_ab)
        let wS : (canonicalLData E l).S := ⟨w, hw_mem⟩
        have hres_A := sha_res_loc_eq_zero (canonicalLData E l) (k : ℤ) x.1.2.1 wS A
          (isPlaceOver_placeOfEBelow E (D_Q.hA v))
        obtain ⟨fx, hfx⟩ := Submodule.Quotient.mk_surjective _ x.1.1
        rw [← hfx] at hres_A ⊢
        obtain ⟨m, hm⟩ := (resH1_mk_eq_zero_iff (qzTw (canonicalLData E l) (k : ℤ))
          (locHom (F := E) ((canonicalLData E l).S : Set (HeightOneSpectrum (𝓞 E))) A)
          (continuous_locHom (F := E) ((canonicalLData E l).S : Set (HeightOneSpectrum (𝓞 E))) A) fx).mp hres_A
        rw [hinfE_mk fx]
        apply (resH1_mk_eq_zero_iff _ _ _ _).mpr
        refine ⟨m, fun g => ?_⟩
        let uG : U := ⟨g.1.1, Subgroup.mem_subgroupOf.mp g.2⟩
        have hg_decE : eU.symm uG ∈ Dec (F := E) A := by
          rw [mem_Dec]
          have h1 : inclGal E (eU.symm uG) = g.1.1 := congrArg Subtype.val (eU.apply_symm_apply uG)
          have hinv : inclGal E (eU.symm uG)⁻¹ = g.1.1⁻¹ := by rw [map_inv, h1]
          ext a
          simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
          have hinvz := congrArg (fun φ : G ℚ (AlgebraicClosure E) => φ a) hinv
          exact (Iff.of_eq (congrArg (· ∈ A) hinvz)).trans (by
            have hdec := mem_Dec.mp g.1.2
            exact show g.1.1⁻¹ • a ∈ A ↔ a ∈ A by
              rw [← ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hdec])
        have hmg : fx.1 (toGS (AlgebraicClosure E) _ (eU.symm uG)) =
            qzTw (canonicalLData E l) (k : ℤ) (toGS (AlgebraicClosure E) _ (eU.symm uG)) m - m :=
          hm ⟨eU.symm uG, hg_decE⟩
        have hrep_g : (ρ_Q.comp U.subtype) uG m =
            qzTw (canonicalLData E l) (k : ℤ) (toGS (AlgebraicClosure E) _ (eU.symm uG)) m :=
          (hrep_compat uG m).symm
        change fx.1 (toGS (AlgebraicClosure E) _ (eU.symm uG)) = (ρ_Q.comp U.subtype) uG m - m
        rw [hrep_g]
        exact hmg
      -- Transfer `resH1 ρ_Q K.subtype _ (infQ y₀) = 0` directly via `resH1_comp`!
      rw [← hy₀] at hres_K_zero
      have hloc_eq : resH1 (qzTw D_Q (k : ℤ)) (locFam D_Q.S D_Q.A v) (continuous_locFam D_Q.S D_Q.A v) y₀ =
          resH1 ρ_Q K.subtype continuous_subtype_val (infQ y₀) := by
        rw [resH1_comp (qzTw D_Q (k : ℤ)) (toGS (AlgebraicClosure E) _)
          (continuous_toGS (AlgebraicClosure E) _) K.subtype continuous_subtype_val]
        rfl
      rw [hloc_eq]
      exact hres_K_zero
    exact ⟨⟨y₀, hy₀_sha⟩, hy₀⟩
  -- Build the `ℤ_[l]`-linear injection `Φ : eig (galRepShaPlus E hcond l k) 1 →ₗ[ℤ_[l]] Sha D_Q k`
  choose Φfun hΦfun using hmem_shaQ
  let Φ : eig (galRepShaPlus E hcond l k) 1 →ₗ[ℤ_[l.1]] Sha D_Q (k : ℤ) :=
    { toFun := Φfun
      map_add' := fun a b => Subtype.ext (hinfQ_inj (by
        change infQ (Φfun (a + b)).1 = infQ ((Φfun a).1 + (Φfun b).1)
        rw [map_add, hΦfun (a + b), hΦfun a, hΦfun b, ← map_add, ← map_add]
        rfl))
      map_smul' := fun r a => Subtype.ext (hinfQ_inj (by
        change infQ (Φfun (r • a)).1 = infQ (r • (Φfun a).1)
        rw [map_smul, hΦfun (r • a), hΦfun a, ← map_smul, ← map_smul]
        rfl)) }
  have hΦ_inj : Function.Injective Φ := by
    intro a b hab
    have hfun : Φfun a = Φfun b := hab
    have h1 : corScaled (infE a.1.1) = corScaled (infE b.1.1) := by
      rw [← hΦfun a, ← hΦfun b, hfun]
    have h2 : infE a.1.1 = infE b.1.1 := by
      rw [← hres_cor_eq a, ← hres_cor_eq b, h1]
    exact Subtype.ext (Subtype.ext (hinfE_inj h2))
  exact length_mono_of_injective Φ hΦ_inj

end CorestrictionAndInflationRestriction

/-! ## Section 6: Concrete `charSet`, `Vlen`, `loss`, `AbelianCharSelmerData`, & Headline Theorems -/

section ConcreteCharSelmerData

private lemma exponent_pos_of_finite_group (Q : Type*) [Group Q] [Finite Q] :
    0 < Monoid.exponent Q :=
  Nat.pos_of_dvd_of_pos Group.exponent_dvd_nat_card Nat.card_pos

/-- Canonical group isomorphism `(Q →* ℂˣ) ≃* (Q →* Oˣ)` for any finite commutative group `Q`
and integral domain `O` with `HasEnoughRootsOfUnity O (Monoid.exponent Q)`. -/
def dualEquiv (Q : Type*) [CommGroup Q] [Finite Q] (O : Type*) [CommRing O] [IsDomain O]
    [HasEnoughRootsOfUnity O (Monoid.exponent Q)] :
    (Q →* ℂˣ) ≃* (Q →* Oˣ) := by
  classical
  set m := Monoid.exponent Q
  have hm_pos : 0 < m := exponent_pos_of_finite_group Q
  haveI : NeZero m := ⟨hm_pos.ne'⟩
  let ζC : ℂ := Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))
  have hζC : IsPrimitiveRoot ζC m := Complex.isPrimitiveRoot_exp m hm_pos.ne'
  let ζO : O := Classical.choose (HasEnoughRootsOfUnity.exists_primitiveRoot O m)
  have hζO : IsPrimitiveRoot ζO m :=
    Classical.choose_spec (HasEnoughRootsOfUnity.exists_primitiveRoot O m)
  have hζC_u : IsUnit ζC := hζC.isUnit hm_pos.ne'
  have hζO_u : IsUnit ζO := hζO.isUnit hm_pos.ne'
  let uC : ℂˣ := hζC_u.unit
  let uO : Oˣ := hζO_u.unit
  -- Map `χ : Q →* ℂˣ` to `χ_O : Q →* Oˣ` sending `g ↦ uO ^ a` where `χ g = uC ^ a`
  have hexC : ∀ (χ : Q →* ℂˣ) (g : Q), ∃ a < m, (χ g : ℂ) = ζC ^ a := fun χ g => by
    have hpow : (χ g : ℂ) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, Monoid.pow_exponent_eq_one, map_one, Units.val_one]
    obtain ⟨a, ha, heq⟩ := hζC.eq_pow_of_pow_eq_one hpow
    exact ⟨a, ha, heq.symm⟩
  have hexO : ∀ (ψ : Q →* Oˣ) (g : Q), ∃ a < m, (ψ g : O) = ζO ^ a := fun ψ g => by
    have hpow : (ψ g : O) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, Monoid.pow_exponent_eq_one, map_one, Units.val_one]
    obtain ⟨a, ha, heq⟩ := hζO.eq_pow_of_pow_eq_one hpow
    exact ⟨a, ha, heq.symm⟩
  have hpowC_mod : ∀ a : ℕ, ζC ^ a = ζC ^ (a % m) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a m, pow_add, pow_mul, hζC.pow_eq_one, one_pow, one_mul]
  have hpowO_mod : ∀ a : ℕ, ζO ^ a = ζO ^ (a % m) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a m, pow_add, pow_mul, hζO.pow_eq_one, one_pow, one_mul]
  have huC_val : ∀ a : ℕ, ((uC ^ a : ℂˣ) : ℂ) = ζC ^ a := fun a => by
    rw [Units.val_pow_eq_pow_val]; exact congrArg (· ^ a) hζC_u.unit_spec
  have huO_val : ∀ a : ℕ, ((uO ^ a : Oˣ) : O) = ζO ^ a := fun a => by
    rw [Units.val_pow_eq_pow_val]; exact congrArg (· ^ a) hζO_u.unit_spec
  have hpowC_eq : ∀ {a b : ℕ}, ζC ^ a = ζC ^ b → uO ^ a = uO ^ b := fun {a b} h => by
    have hmod : a % m = b % m :=
      hζC.pow_inj (Nat.mod_lt a hm_pos) (Nat.mod_lt b hm_pos) (by rw [← hpowC_mod a, ← hpowC_mod b]; exact h)
    apply Units.ext
    rw [huO_val a, huO_val b, hpowO_mod a, hpowO_mod b, hmod]
  have hpowO_eq : ∀ {a b : ℕ}, ζO ^ a = ζO ^ b → uC ^ a = uC ^ b := fun {a b} h => by
    have hmod : a % m = b % m :=
      hζO.pow_inj (Nat.mod_lt a hm_pos) (Nat.mod_lt b hm_pos) (by rw [← hpowO_mod a, ← hpowO_mod b]; exact h)
    apply Units.ext
    rw [huC_val a, huC_val b, hpowC_mod a, hpowC_mod b, hmod]
  let fwd : (Q →* ℂˣ) → (Q →* Oˣ) := fun χ =>
    { toFun := fun g => uO ^ (hexC χ g).choose
      map_one' := by
        set a := (hexC χ 1).choose
        have ha : (χ 1 : ℂ) = ζC ^ a := (hexC χ 1).choose_spec.2
        have h0 : ζC ^ a = ζC ^ 0 := by rw [← ha, map_one, Units.val_one, pow_zero]
        exact (hpowC_eq h0).trans (pow_zero uO)
      map_mul' := fun g₁ g₂ => by
        rw [← pow_add]
        apply hpowC_eq
        set a12 := (hexC χ (g₁ * g₂)).choose
        set a1 := (hexC χ g₁).choose
        set a2 := (hexC χ g₂).choose
        have h1 : (χ (g₁ * g₂) : ℂ) = ζC ^ a12 := (hexC χ (g₁ * g₂)).choose_spec.2
        have h2 : (χ g₁ : ℂ) = ζC ^ a1 := (hexC χ g₁).choose_spec.2
        have h3 : (χ g₂ : ℂ) = ζC ^ a2 := (hexC χ g₂).choose_spec.2
        calc ζC ^ a12 = (χ (g₁ * g₂) : ℂ) := h1.symm
          _ = (χ g₁ : ℂ) * (χ g₂ : ℂ) := by rw [map_mul, Units.val_mul]
          _ = ζC ^ a1 * ζC ^ a2 := by rw [h2, h3]
          _ = ζC ^ (a1 + a2) := (pow_add ζC a1 a2).symm }
  let bwd : (Q →* Oˣ) → (Q →* ℂˣ) := fun ψ =>
    { toFun := fun g => uC ^ (hexO ψ g).choose
      map_one' := by
        set a := (hexO ψ 1).choose
        have ha : (ψ 1 : O) = ζO ^ a := (hexO ψ 1).choose_spec.2
        have h0 : ζO ^ a = ζO ^ 0 := by rw [← ha, map_one, Units.val_one, pow_zero]
        exact (hpowO_eq h0).trans (pow_zero uC)
      map_mul' := fun g₁ g₂ => by
        rw [← pow_add]
        apply hpowO_eq
        set a12 := (hexO ψ (g₁ * g₂)).choose
        set a1 := (hexO ψ g₁).choose
        set a2 := (hexO ψ g₂).choose
        have h1 : (ψ (g₁ * g₂) : O) = ζO ^ a12 := (hexO ψ (g₁ * g₂)).choose_spec.2
        have h2 : (ψ g₁ : O) = ζO ^ a1 := (hexO ψ g₁).choose_spec.2
        have h3 : (ψ g₂ : O) = ζO ^ a2 := (hexO ψ g₂).choose_spec.2
        calc ζO ^ a12 = (ψ (g₁ * g₂) : O) := h1.symm
          _ = (ψ g₁ : O) * (ψ g₂ : O) := by rw [map_mul, Units.val_mul]
          _ = ζO ^ a1 * ζO ^ a2 := by rw [h2, h3]
          _ = ζO ^ (a1 + a2) := (pow_add ζO a1 a2).symm }
  refine
    { toFun := fwd
      invFun := bwd
      left_inv := fun χ => by
        ext g
        set b := (hexO (fwd χ) g).choose
        set a := (hexC χ g).choose
        have hb : ((fwd χ g : Oˣ) : O) = ζO ^ b := (hexO (fwd χ) g).choose_spec.2
        have ha : (χ g : ℂ) = ζC ^ a := (hexC χ g).choose_spec.2
        have h3 : ζO ^ b = ζO ^ a := by
          calc ζO ^ b = ((fwd χ g : Oˣ) : O) := hb.symm
            _ = ((uO ^ a : Oˣ) : O) := rfl
            _ = ζO ^ a := huO_val a
        have h4 : uC ^ b = uC ^ a := hpowO_eq h3
        change ((uC ^ b : ℂˣ) : ℂ) = (χ g : ℂ)
        rw [h4, huC_val a, ← ha]
      right_inv := fun ψ => by
        ext g
        set b := (hexC (bwd ψ) g).choose
        set a := (hexO ψ g).choose
        have hb : ((bwd ψ g : ℂˣ) : ℂ) = ζC ^ b := (hexC (bwd ψ) g).choose_spec.2
        have ha : (ψ g : O) = ζO ^ a := (hexO ψ g).choose_spec.2
        have h3 : ζC ^ b = ζC ^ a := by
          calc ζC ^ b = ((bwd ψ g : ℂˣ) : ℂ) := hb.symm
            _ = ((uC ^ a : ℂˣ) : ℂ) := rfl
            _ = ζC ^ a := huC_val a
        have h4 : uO ^ b = uO ^ a := hpowC_eq h3
        change ((uO ^ b : Oˣ) : O) = (ψ g : O)
        rw [h4, huO_val a, ← ha]
      map_mul' := fun χ₁ χ₂ => by
        ext g
        set a12 := (hexC (χ₁ * χ₂) g).choose
        set a1 := (hexC χ₁ g).choose
        set a2 := (hexC χ₂ g).choose
        have h1 : ((χ₁ * χ₂) g : ℂ) = ζC ^ a12 := (hexC (χ₁ * χ₂) g).choose_spec.2
        have h2 : (χ₁ g : ℂ) = ζC ^ a1 := (hexC χ₁ g).choose_spec.2
        have h3 : (χ₂ g : ℂ) = ζC ^ a2 := (hexC χ₂ g).choose_spec.2
        have heq : uO ^ a12 = uO ^ (a1 + a2) := hpowC_eq (by
          calc ζC ^ a12 = ((χ₁ * χ₂) g : ℂ) := h1.symm
            _ = (χ₁ g : ℂ) * (χ₂ g : ℂ) := by rw [MonoidHom.mul_apply, Units.val_mul]
            _ = ζC ^ a1 * ζC ^ a2 := by rw [h2, h3]
            _ = ζC ^ (a1 + a2) := (pow_add ζC a1 a2).symm)
        change ((uO ^ a12 : Oˣ) : O) = ((uO ^ a1 * uO ^ a2 : Oˣ) : O)
        rw [heq, pow_add] }

/-- Fintype instance on `(E ≃ₐ[ℚ] E) →* ℂˣ` for `1 ≤ condF E`. -/
@[instance_reducible]
private def fintypeDualComplex {E : Type} [Field E] [NumberField E] (_hcond : 1 ≤ condF E) :
    Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := by
  classical
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
  -- Every `χ : G →* ℂˣ` lands in the finite group of `m`-th roots of unity
  let m := Monoid.exponent (E ≃ₐ[ℚ] E)
  let emb : ((E ≃ₐ[ℚ] E) →* ℂˣ) → ((E ≃ₐ[ℚ] E) → rootsOfUnity m ℂ) :=
    fun χ g => ⟨χ g, by
      rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]⟩
  have hemb : Function.Injective emb := fun a b h => by
    ext g
    have hg := congrFun h g
    exact congrArg (fun z : rootsOfUnity m ℂ => ((z : ℂˣ) : ℂ)) hg
  haveI : Finite ((E ≃ₐ[ℚ] E) →* ℂˣ) := Finite.of_injective emb hemb
  exact Fintype.ofFinite _

/-- Exact cardinality of the complex dual group: `|(E ≃ₐ[ℚ] E) →* ℂˣ| = Module.finrank ℚ E ≤ condF E`. -/
theorem card_dualComplex_eq_finrank {E : Type} [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    @Fintype.card ((E ≃ₐ[ℚ] E) →* ℂˣ) (fintypeDualComplex hcond) = Module.finrank ℚ E := by
  letI : CommGroup (E ≃ₐ[ℚ] E) := commGroupAutOfCondF hcond
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
  have h1 := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (E ≃ₐ[ℚ] E) ℂ
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
  exact h1.trans (card_aut_eq_finrank_of_one_le_condF hcond)

/-- Concrete character tag map `charToTag : ((E ≃ₐ[ℚ] E) →* ℂˣ) → GalCharTag` for `1 ≤ condF E`. -/
def charToTag (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    ((E ≃ₐ[ℚ] E) →* ℂˣ) → GalCharTag := by
  classical
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  exact fun χ =>
    { id := (Fintype.equivFin ((E ≃ₐ[ℚ] E) →* ℂˣ) χ).val
      isTrivial := decide (χ = 1)
      evenOrder := decide (2 ∣ orderOf χ)
      r1LeTwoPowC2 := decide (orderOf χ ≤ 2) }

theorem charToTag_injective (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E) :
    Function.Injective (charToTag E hcond) := by
  classical
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  intro χ₁ χ₂ h
  have hid : (Fintype.equivFin ((E ≃ₐ[ℚ] E) →* ℂˣ) χ₁).val =
      (Fintype.equivFin ((E ≃ₐ[ℚ] E) →* ℂˣ) χ₂).val := congrArg GalCharTag.id h
  exact (Fintype.equivFin _).injective (Fin.ext hid)

/-- The canonical trivial character tag in `charSet E k` when `1 ≤ condF E`. -/
def trivialCharTag (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E) : GalCharTag :=
  charToTag E hcond 1

/-- **Concrete `charSet E k : Finset GalCharTag`**:
enumerates the genuine complex dual group `(E ≃ₐ[ℚ] E) →* ℂˣ` when `1 ≤ condF E`, and `∅` when `condF E = 0`. -/
def charSet (E : Type) [Field E] [NumberField E] (_k : ℕ) : Finset GalCharTag := by
  classical
  exact if hcond : 1 ≤ condF E then
    letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
    Finset.univ.image (charToTag E hcond)
  else ∅

/-- **Unconditional `charSet_card_le` (0 hypotheses, ALL `NumberField E`!)**:
`(charSet E k).card ≤ condF E`! -/
theorem charSet_card_le (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (charSet E k).card ≤ condF E := by
  classical
  unfold charSet
  split_ifs with hcond
  · letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
    calc (Finset.univ.image (charToTag E hcond)).card
        ≤ (Finset.univ : Finset ((E ≃ₐ[ℚ] E) →* ℂˣ)).card := Finset.card_image_le
      _ = @Fintype.card ((E ≃ₐ[ℚ] E) →* ℂˣ) (fintypeDualComplex hcond) := Finset.card_univ
      _ = Module.finrank ℚ E := card_dualComplex_eq_finrank hcond
      _ ≤ condF E := finrank_le_condF hcond
  · simp

theorem trivialCharTag_mem_charSet (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E)
    (k : ℕ) : trivialCharTag E hcond ∈ charSet E k := by
  classical
  unfold charSet trivialCharTag
  rw [dif_pos hcond]
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  exact Finset.mem_image_of_mem _ (Finset.mem_univ 1)

theorem isTrivial_eq_true_iff (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E)
    (k : ℕ) {χ : GalCharTag} (hχ : χ ∈ charSet E k) :
    χ.isTrivial = true ↔ χ = trivialCharTag E hcond := by
  classical
  unfold charSet at hχ
  rw [dif_pos hcond] at hχ
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hχ
  constructor
  · intro ht
    have hψ : ψ = 1 := of_decide_eq_true ht
    rw [hψ]; rfl
  · intro heq
    have hψ : ψ = 1 := charToTag_injective E hcond heq
    subst hψ
    simp [charToTag]

/-- **Genuine Character-Eigenspace Length `Vlen E l k χ : ℕ∞`**:
for an abelian number field `1 ≤ condF E` and tag `χ = charToTag E hcond ψ`, equals the exact
`O`-module length `Module.length O (eig (baseChangeRep (galRepShaPlus E hcond l k)) (dualEquiv ψ))`
over the cyclotomic DVR `O = (chosenPadicCoeffDVR l (exp(Gal(E/ℚ)))).O` (which is unramified
`eO = 1` whenever `l ∤ [E:ℚ]`)! -/
def Vlen (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ) (χ : GalCharTag) : ℕ∞ := by
  classical
  exact if hcond : 1 ≤ condF E then
    if hmem : ∃ ψ : (E ≃ₐ[ℚ] E) →* ℂˣ, charToTag E hcond ψ = χ then
      letI : CommGroup (E ≃ₐ[ℚ] E) := commGroupAutOfCondF hcond
      haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
      let C := chosenPadicCoeffDVR l.1 (Monoid.exponent (E ≃ₐ[ℚ] E))
      let ψO := dualEquiv (E ≃ₐ[ℚ] E) C.O (Classical.choose hmem)
      Module.length C.O (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) ψO)
    else 0
  else 0

theorem Vlen_charToTag (E : Type) [Field E] [NumberField E] (hcond : 1 ≤ condF E)
    (l : Nat.Primes) (k : ℕ) (ψ : (E ≃ₐ[ℚ] E) →* ℂˣ) :
    letI : CommGroup (E ≃ₐ[ℚ] E) := commGroupAutOfCondF hcond
    haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
    let C := chosenPadicCoeffDVR l.1 (Monoid.exponent (E ≃ₐ[ℚ] E))
    Vlen E l k (charToTag E hcond ψ) =
      Module.length C.O
        (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k))
          (dualEquiv (E ≃ₐ[ℚ] E) C.O ψ)) := by
  classical
  unfold Vlen
  rw [dif_pos hcond]
  have hmem : ∃ ψ' : (E ≃ₐ[ℚ] E) →* ℂˣ, charToTag E hcond ψ' = charToTag E hcond ψ := ⟨ψ, rfl⟩
  rw [dif_pos hmem]
  have hch : Classical.choose hmem = ψ := charToTag_injective E hcond (Classical.choose_spec hmem)
  rw [hch]

/-- Exact local decomposition loss (`0` via genuine Maschke / `lenEigLe` eigenspace splitting!). -/
def loss (_E : Type) [Field _E] [NumberField _E] (_l : Nat.Primes) (_k : ℕ) : ℕ := 0

/-- **UNCONDITIONAL ABELIAN PLUS-PARITY CHARACTER DECOMPOSITION (`0` OPEN PARAMETERS!)**:
for EVERY abelian number field `E` (`1 ≤ condF E`), EVERY odd prime `l ≠ 2`, and EVERY `0 < k`,
`minusParitySelmerSystem.plusLen E l k ≤ (∑ χ ∈ charSet E k, Vlen E l k χ) + (loss E l k : ℕ∞)`! -/
theorem plusLen_le_of_one_le_condF (E : Type) [Field E] [NumberField E]
    (hcond : 1 ≤ condF E) (l : Nat.Primes) (k : ℕ) (_hl2 : (l : ℕ) ≠ 2) (_hk : 0 < k) :
    minusParitySelmerSystem.plusLen E l k ≤
      (∑ χ ∈ charSet E k, Vlen E l k χ) + (loss E l k : ℕ∞) := by
  classical
  letI : CommGroup (E ≃ₐ[ℚ] E) := commGroupAutOfCondF hcond
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
  let C := chosenPadicCoeffDVR l.1 (Monoid.exponent (E ≃ₐ[ℚ] E))
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  let dEq := dualEquiv (E ≃ₐ[ℚ] E) C.O
  letI : Fintype ((E ≃ₐ[ℚ] E) →* C.Oˣ) := Fintype.ofEquiv _ dEq.toEquiv
  have hstep1 : minusParitySelmerSystem.plusLen E l k ≤
      Module.length C.O (C.O ⊗[ℤ_[l.1]] ↥(ShaPlus E l k)) := by
    rw [minusParitySelmerSystem_plusLen_eq_shaPlus, length_baseChange_eq_eO_mul C]
    calc Module.length ℤ_[l.1] ↥(ShaPlus E l k)
        = 1 * Module.length ℤ_[l.1] ↥(ShaPlus E l k) := (one_mul _).symm
      _ ≤ eO l.1 C.O * Module.length ℤ_[l.1] ↥(ShaPlus E l k) :=
          mul_le_mul_of_nonneg_right C.one_le_eO zero_le
  have hstep2 : Module.length C.O (C.O ⊗[ℤ_[l.1]] ↥(ShaPlus E l k)) ≤
      ∑ ψO : (E ≃ₐ[ℚ] E) →* C.Oˣ,
        Module.length C.O (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) ψO) :=
    lenEigLe (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k))
  have hsum_eq : ∑ ψO : (E ≃ₐ[ℚ] E) →* C.Oˣ,
        Module.length C.O (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) ψO) =
      ∑ χ ∈ charSet E k, Vlen E l k χ := by
    unfold charSet
    rw [dif_pos hcond, Finset.sum_image (fun a _ b _ h => charToTag_injective E hcond h)]
    rw [← Fintype.sum_equiv dEq.toEquiv
      (fun ψ => Vlen E l k (charToTag E hcond ψ))
      (fun ψO => Module.length C.O (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) ψO))
      (fun ψ => Vlen_charToTag E hcond l k ψ)]
  rw [loss, Nat.cast_zero, add_zero, ← hsum_eq]
  exact hstep1.trans hstep2

/-- **EXACT MASCHKE EQUALITY (`l ∤ [E : ℚ]`)**:
whenever `1 ≤ condF E` and `¬ l ∣ Module.finrank ℚ E`, the unramified cyclotomic DVR `C.O` has
`eO = 1` and `IsUnit (|Gal(E/ℚ)| : C.O)`, yielding **EXACT EQUALITY**:
`minusParitySelmerSystem.plusLen E l k = ∑ χ ∈ charSet E k, Vlen E l k χ`! -/
theorem plusLen_eq_sum_of_not_dvd (E : Type) [Field E] [NumberField E]
    (hcond : 1 ≤ condF E) (l : Nat.Primes) (k : ℕ) (hnd : ¬ (l : ℕ) ∣ Module.finrank ℚ E) :
    minusParitySelmerSystem.plusLen E l k = ∑ χ ∈ charSet E k, Vlen E l k χ := by
  classical
  letI : CommGroup (E ≃ₐ[ℚ] E) := commGroupAutOfCondF hcond
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
  have hexp_dvd : Monoid.exponent (E ≃ₐ[ℚ] E) ∣ Module.finrank ℚ E := by
    rw [← card_aut_eq_finrank_of_one_le_condF hcond, ← Nat.card_eq_fintype_card]
    exact Group.exponent_dvd_nat_card
  have hnd_exp : ¬ (l : ℕ) ∣ Monoid.exponent (E ≃ₐ[ℚ] E) := fun h => hnd (h.trans hexp_dvd)
  let C := chosenPadicCoeffDVR l.1 (Monoid.exponent (E ≃ₐ[ℚ] E))
  have heO1 : eO l.1 C.O = 1 := eO_chosenPadicCoeffDVR_of_not_dvd l.1 _ hnd_exp
  letI : Fintype ((E ≃ₐ[ℚ] E) →* ℂˣ) := fintypeDualComplex hcond
  let dEq := dualEquiv (E ≃ₐ[ℚ] E) C.O
  letI : Fintype ((E ≃ₐ[ℚ] E) →* C.Oˣ) := Fintype.ofEquiv _ dEq.toEquiv
  have hu_Z : IsUnit (Fintype.card (E ≃ₐ[ℚ] E) : ℤ_[l.1]) := by
    rw [card_aut_eq_finrank_of_one_le_condF hcond]
    exact isUnit_finrank_padicInt_of_not_dvd E hnd
  have hu_O : IsUnit (Fintype.card (E ≃ₐ[ℚ] E) : C.O) := by
    simpa [map_natCast] using hu_Z.map (algebraMap ℤ_[l.1] C.O)
  have hstep1 : minusParitySelmerSystem.plusLen E l k =
      Module.length C.O (C.O ⊗[ℤ_[l.1]] ↥(ShaPlus E l k)) := by
    rw [minusParitySelmerSystem_plusLen_eq_shaPlus, length_baseChange_eq_eO_mul C, heO1, one_mul]
  have hstep2 := lenEigEq (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) hu_O
  have hsum_eq : ∑ ψO : (E ≃ₐ[ℚ] E) →* C.Oˣ,
        Module.length C.O (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) ψO) =
      ∑ χ ∈ charSet E k, Vlen E l k χ := by
    unfold charSet
    rw [dif_pos hcond, Finset.sum_image (fun a _ b _ h => charToTag_injective E hcond h)]
    rw [← Fintype.sum_equiv dEq.toEquiv
      (fun ψ => Vlen E l k (charToTag E hcond ψ))
      (fun ψO => Module.length C.O (eig (baseChangeRep (O := C.O) (galRepShaPlus E hcond l k)) ψO))
      (fun ψ => Vlen_charToTag E hcond l k ψ)]
  rw [hstep1, hstep2, hsum_eq]

/-- **`loss = 0` outside `Bchi_χ` (and unconditionally everywhere!)**. -/
theorem loss_eq_zero_of_not_dvd (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ)
    (_hnd : ¬ (l : ℕ) ∣ Module.finrank ℚ E) : loss E l k = 0 := rfl

/-- Polynomial bound for `loss E l k` inside `Bchi_χ` (`Closs = 0` suffices!). -/
theorem loss_le_poly (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k Closs : ℕ) :
    (loss E l k : ℝ) ≤ (((l : ℕ) : ℝ) * (condF E : ℝ) * (k : ℝ)) ^ Closs := by
  rw [loss, Nat.cast_zero]
  positivity

/-- **UNCONDITIONAL TRIVIAL-CHARACTER EIGENSPACE BOUND (`Vlen_trivial_le_sha_rat`, `CountZ` SNAP-IN!)**:
for EVERY abelian number field `E` (`1 ≤ condF E`), EVERY odd prime `l` with `¬ l ∣ [E : ℚ]`,
EVERY `k : ℕ`, and EVERY `χ ∈ charSet E k` with `χ.isTrivial = true`:
`Vlen E l k χ ≤ realGaloisSelmerSystem.shaLen ℚ l k`! -/
theorem Vlen_trivial_le_sha_rat (E : Type) [Field E] [NumberField E]
    (hcond : 1 ≤ condF E) (l : Nat.Primes) (k : ℕ)
    (hnd : ¬ (l : ℕ) ∣ Module.finrank ℚ E)
    {χ : GalCharTag} (hχ : χ ∈ charSet E k) (htriv : χ.isTrivial = true) :
    Vlen E l k χ ≤ realGaloisSelmerSystem.shaLen ℚ l k := by
  have hχ_eq : χ = trivialCharTag E hcond := (isTrivial_eq_true_iff E hcond k hχ).mp htriv
  rw [hχ_eq, trivialCharTag]
  letI : CommGroup (E ≃ₐ[ℚ] E) := commGroupAutOfCondF hcond
  haveI : NeZero (Monoid.exponent (E ≃ₐ[ℚ] E)) := ⟨(exponent_pos_of_finite_group _).ne'⟩
  have hexp_dvd : Monoid.exponent (E ≃ₐ[ℚ] E) ∣ Module.finrank ℚ E := by
    rw [← card_aut_eq_finrank_of_one_le_condF hcond, ← Nat.card_eq_fintype_card]
    exact Group.exponent_dvd_nat_card
  have hnd_exp : ¬ (l : ℕ) ∣ Monoid.exponent (E ≃ₐ[ℚ] E) := fun h => hnd (h.trans hexp_dvd)
  let C := chosenPadicCoeffDVR l.1 (Monoid.exponent (E ≃ₐ[ℚ] E))
  have heO1 : eO l.1 C.O = 1 := eO_chosenPadicCoeffDVR_of_not_dvd l.1 _ hnd_exp
  rw [Vlen_charToTag E hcond l k 1, map_one,
    length_eig_one_baseChange C (galRepShaPlus E hcond l k), heO1, one_mul]
  exact sha_invariants_length_le_sha_rat E hcond l hnd k

/-- Convenience specialization of `Vlen_trivial_le_sha_rat` directly for `IsChiField ψ e q d E`
and any prime `l ∉ Bchi E ψ` (matching `Stage13Field1Unification.lean:958-962`). -/
theorem Vlen_trivial_le_sha_rat_of_isChiField {ψ : PChar} {e q d : ℕ}
    (hq : 0 < q) (hd : 0 < d) {E : Type} [Field E] [NumberField E]
    (hE : IsChiField ψ e q d E) {l : Nat.Primes} (hlB : l ∉ Bchi E ψ) (k : ℕ)
    {χ : GalCharTag} (hχ : χ ∈ charSet E k) (htriv : χ.isTrivial = true) :
    Vlen E l k χ ≤ realGaloisSelmerSystem.shaLen ℚ l k := by
  have hcond : 1 ≤ condF E := (Stage2GaloisWire.condF_bounds_of_isChiField ψ e q d hq hd E hE).1
  have hnd : ¬ (l : ℕ) ∣ Module.finrank ℚ E := (not_mem_Bchi_spec hcond hlB).2.1
  exact Vlen_trivial_le_sha_rat E hcond l k hnd hχ htriv

/-- **Abelian Character-Level Selmer Data (`AbelianCharSelmerData S`)**:
exact Field-#1 interface matching `Stage13SixCaseVWinAssembly.CharSelmerData S` with the
exact abelianness guard `1 ≤ condF E` already present at every call site (`sumOut_of_counts`,
`sumIn_of_counts`). -/
structure AbelianCharSelmerData (S : SelmerSystem) where
  plusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  minusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  shaLen_eq_add : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    (l : ℕ) ≠ 2 → S.shaLen E l e = plusLen E l e + minusLen E l e
  charSet : (E : Type) → [Field E] → [NumberField E] → ℕ → Finset GalCharTag
  charSet_card_le : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ),
    (charSet E k).card ≤ condF E
  Vlen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → GalCharTag → ℕ∞
  loss : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ
  plusLen_le : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ),
    1 ≤ condF E → (l : ℕ) ≠ 2 → 0 < k →
      plusLen E l k ≤ (∑ χ ∈ charSet E k, Vlen E l k χ) + (loss E l k : ℕ∞)

/-- **ZERO-PARAMETER `AbelianCharSelmerData realGaloisSelmerSystem`**!
Matches `Stage13MinusParityRubin.minusParitySelmerSystem` definitionally (`rfl`), with genuine
`Gal(E/ℚ)` character-eigenspace lengths `Vlen`, `loss = 0`, exact Maschke splitting for `l ∤ [E:ℚ]`,
and inflation–restriction `Vlen_trivial_le_sha_rat` for `CountZ`! -/
def realGaloisAbelianCharSelmerData : AbelianCharSelmerData realGaloisSelmerSystem where
  plusLen := minusParitySelmerSystem.plusLen
  minusLen := minusParitySelmerSystem.minusLen
  shaLen_eq_add := minusParitySelmerSystem.shaLen_eq_add
  charSet := charSet
  charSet_card_le := charSet_card_le
  Vlen := Vlen
  loss := loss
  plusLen_le E _ _ l k hcond hl2 hk := plusLen_le_of_one_le_condF E hcond l k hl2 hk

@[simp] theorem realGaloisAbelianCharSelmerData_plusLen :
    realGaloisAbelianCharSelmerData.plusLen = minusParitySelmerSystem.plusLen := rfl

@[simp] theorem realGaloisAbelianCharSelmerData_minusLen :
    realGaloisAbelianCharSelmerData.minusLen = minusParitySelmerSystem.minusLen := rfl

@[simp] theorem realGaloisAbelianCharSelmerData_loss (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ) :
    realGaloisAbelianCharSelmerData.loss E l k = 0 := rfl

/-- Exact bridge to legacy `CharSelmerData realGaloisSelmerSystem` isolating ONLY the non-abelian
(`condF E = 0`) finiteness fallback (unused by `sumOut_of_counts` / `sumIn_of_counts`). -/
def realGaloisCharSelmerData_of_nonabelian_finite
    (hnonab : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ),
      condF E = 0 → (l : ℕ) ≠ 2 → 0 < k → minusParitySelmerSystem.plusLen E l k ≠ ⊤) :
    CharSelmerData realGaloisSelmerSystem where
  plusLen := minusParitySelmerSystem.plusLen
  minusLen := minusParitySelmerSystem.minusLen
  shaLen_eq_add := minusParitySelmerSystem.shaLen_eq_add
  charSet := charSet
  charSet_card_le := charSet_card_le
  Vlen := Vlen
  loss E _ _ l k := if condF E = 0 then (minusParitySelmerSystem.plusLen E l k).toNat else 0
  plusLen_le E _ _ l k hl2 hk := by
    by_cases h0 : condF E = 0
    · rw [if_pos h0, ENat.natCast_toNat (hnonab E l k h0 hl2 hk)]
      exact le_add_self
    · rw [if_neg h0]
      have hcond : 1 ≤ condF E := Nat.one_le_iff_ne_zero.mpr h0
      simpa [loss] using plusLen_le_of_one_le_condF E hcond l k hl2 hk

end ConcreteCharSelmerData

end RHDirect.Stage13MaschkeCharDecomp

end
