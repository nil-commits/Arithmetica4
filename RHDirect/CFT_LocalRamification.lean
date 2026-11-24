import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import RHDirect.CFT_LocalStructure
import RHDirect.CFT_AbstractLocalReciprocity
import RHDirect.Stage13CFT_IdeleNormResidue

/-!
# RHDirect.CFT_LocalRamification

Local Field Unramified Extensions, Ramification, Tame Extensions & Local Herbrand Quotient
(`namespace RHDirect.CFT.LocalField`):
- Intermediate fields, separable closures & valuation extensions
- Unramified extensions, Hensel lifting, existence, Galois group (Frobenius), roots of unity & norm surjectivity
- Maximal unramified extension `K^nr`, its integers & completion `𝔹` with completed Frobenius
- Eisenstein polynomials, existence of extensions of given degree, ramification groups & structure
- Tame ramification & tame extensions
- Normal lattices, local Tate-trivial open subgroups & Local Herbrand Quotient (`[Kˣ : N(Lˣ)] = [L : K]` for cyclic `L/K`)
-/

noncomputable section

namespace RHDirect.CFT.LocalField


/-! ### IntermediateField -/
section Sec_IntermediateField

open ValuativeRel Topology Filter

section Algebraic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]
  (E : IntermediateField K L)

instance intermediateField_valuativeRel : ValuativeRel E :=
  ValuativeRel.ofValuation ((valuation L).comap (algebraMap E L))

variable {E} in

@[simp]
theorem IntermediateField.coe_vle_coe_iff (x y : E) : (x : L) ≤ᵥ (y : L) ↔ x ≤ᵥ y :=
  by exact (valuation L).vle_iff_le

instance intermediateField_valuativeExtension_right : ValuativeExtension E L :=
  ⟨IntermediateField.coe_vle_coe_iff⟩

instance intermediateField_valuativeExtension_left [ValuativeRel K] [ValuativeExtension K L] :
    ValuativeExtension K E :=
  ⟨fun a b ↦ by
    rw [← IntermediateField.coe_vle_coe_iff, IntermediateField.coe_algebraMap_apply,
      IntermediateField.coe_algebraMap_apply, ValuativeExtension.vle_iff_vle]⟩

variable {E} in

theorem IntermediateField.valuation_coe (x : E) :
    valuation L (x : L) = ValuativeExtension.mapValueGroupWithZero E L (valuation E x) :=
  (ValuativeExtension.mapValueGroupWithZero_valuation (A := E) (B := L) x).symm

end Algebraic

section Topological

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (E : IntermediateField K L)

theorem IntermediateField.isClosed_of_isNonarchimedeanLocalField : IsClosed (E : Set L) := by
  let := nontriviallyNormedField K
  have := completeSpace_nontriviallyNormedField K
  have := t2Space_of_isNonarchimedeanLocalField L
  have : FiniteDimensional K (Subalgebra.toSubmodule E.toSubalgebra) :=
    (inferInstance : FiniteDimensional K E)
  exact (Subalgebra.toSubmodule E.toSubalgebra).closed_of_finiteDimensional

instance intermediateField_isNonarchimedeanLocalField : IsNonarchimedeanLocalField E := by

  have small : ∀ γ : (ValueGroupWithZero L)ˣ, ∃ b : E, b ≠ 0 ∧ valuation L (b : L) < γ := by
    intro γ
    obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
    obtain ⟨a, rfl⟩ := valuation_surjective δ
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hδ0
    have hb : valuation L (algebraMap K L a) < 1 :=
      (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hb γ
    refine ⟨algebraMap K E (a ^ n), by simp [ha0], ?_⟩
    rw [IntermediateField.coe_algebraMap_apply, map_pow, map_pow]
    exact hn
  have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := E) (B := L)
  have hval := IntermediateField.valuation_coe (E := E)
  have : ContinuousConstVAdd E E :=
    ⟨fun c ↦ continuous_induced_rng.2 (continuous_const.add continuous_subtype_val)⟩
  have hvt : IsValuativeTopology E := by
    refine IsValuativeTopology.of_zero fun s ↦ ?_
    have hb := (IsValuativeTopology.hasBasis_nhds_zero L).comap ((↑) : E → L)
    rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero]
    refine hb.mem_iff.trans ?_
    constructor
    · rintro ⟨γ, -, hγ⟩
      obtain ⟨b, hb0, hb⟩ := small γ
      refine ⟨Units.mk0 (valuation E b) (by simpa using hb0), fun z hz ↦ hγ ?_⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
      rw [hval] at hb ⊢
      exact (hmono hz).trans hb
    · rintro ⟨γ, hγ⟩
      have hγ0 : ValuativeExtension.mapValueGroupWithZero E L γ ≠ 0 := by
        rw [← map_zero (ValuativeExtension.mapValueGroupWithZero E L)]
        exact (hmono (zero_lt_iff.mpr γ.ne_zero)).ne'
      refine ⟨Units.mk0 _ hγ0, trivial, fun z hz ↦ hγ ?_⟩
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
      rw [hval] at hz
      exact hmono.lt_iff_lt.mp hz
  have hlc : LocallyCompactSpace E :=
    (IntermediateField.isClosed_of_isNonarchimedeanLocalField E).isClosedEmbedding_subtypeVal
      |>.locallyCompactSpace
  have hnt : IsNontrivial E := by
    obtain ⟨b, hb0, hb⟩ := small 1
    refine ⟨⟨valuation E b, by simpa using hb0, fun h ↦ ?_⟩⟩
    rw [hval, h, map_one] at hb
    exact hb.false
  exact { hvt, hlc, hnt with }

example : IsNonarchimedeanLocalField E := inferInstance
example : ValuativeExtension E L := inferInstance
example : Algebra 𝒪[E] 𝒪[L] := inferInstance
example : Algebra 𝓀[E] 𝓀[L] := inferInstance
example (σ : L ≃ₐ[E] L) (x : L) : valuation L (σ x) = valuation L x :=
  valuation_algEquiv_apply E L σ x
example (F : IntermediateField K L) (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension E F :=
  valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)

end Topological

end Sec_IntermediateField


/-! ### SeparableClosure -/
section Sec_SeparableClosure

open ValuativeRel Topology Filter Polynomial

section Integral

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [ValuativeExtension K L]

theorem valuation_le_one_of_aeval_eq_zero {p : K[X]} (hp : p.Monic)
    (hc : ∀ n, valuation K (p.coeff n) ≤ 1) {y : L} (hy : aeval y p = 0) : valuation L y ≤ 1 := by
  by_contra h
  push Not at h
  set d := p.natDegree
  have hsum : aeval y p = y ^ d + ∑ i ∈ Finset.range d, algebraMap K L (p.coeff i) * y ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul, add_comm]
    simp only [Algebra.smul_def]
    rfl
  rw [hsum, add_eq_zero_iff_eq_neg] at hy
  have hy0 : valuation L y ^ d ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one h))
  have hlt : valuation L (∑ i ∈ Finset.range d, algebraMap K L (p.coeff i) * y ^ i) <
      valuation L y ^ d := by
    refine Valuation.map_sum_lt _ hy0 fun i hi ↦ ?_
    rw [map_mul, map_pow]
    have hci : valuation L (algebraMap K L (p.coeff i)) ≤ 1 :=
      (Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) _).mpr (hc i)
    calc valuation L (algebraMap K L (p.coeff i)) * valuation L y ^ i
        ≤ 1 * valuation L y ^ i := mul_le_mul_left hci _
      _ = valuation L y ^ i := one_mul _
      _ < valuation L y ^ d := pow_lt_pow_right₀ h (Finset.mem_range.mp hi)
  rw [← map_pow, hy, Valuation.map_neg] at hlt
  exact lt_irrefl _ hlt

end Integral

section Spectral

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

@[instance_reducible]
def algebraicNormedField : NontriviallyNormedField L :=
  letI := normedField K
  haveI := normedField_isUltrametricDist K
  haveI := normedField_completeSpace K
  spectralNorm.nontriviallyNormedField K L

theorem algebraicNormedField_isUltrametricDist :
    letI := algebraicNormedField K L
    IsUltrametricDist L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  let := algebraicNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))

theorem algebraicNormedField_norm_algebraMap (a : K) :
    letI := normedField K
    letI := algebraicNormedField K L
    ‖algebraMap K L a‖ = ‖a‖ := by
  let := normedField K
  exact spectralNorm_extends a

variable {K L}

theorem valuation_le_one_of_spectralNorm_le_one [ValuativeRel L] [ValuativeExtension K L] {y : L}
    (h : letI := normedField K; spectralNorm K L y ≤ 1) : valuation L y ≤ 1 := by
  let := normedField K
  have hint : IsIntegral K y := Algebra.IsIntegral.isIntegral y
  have hc := (spectralValue_le_one_iff (minpoly.monic hint)).mp h
  refine valuation_le_one_of_aeval_eq_zero (minpoly.monic hint) (fun n ↦ ?_) (minpoly.aeval K y)
  have h1 : ‖(minpoly K y).coeff n‖ ≤ ‖(1 : K)‖ := by rw [norm_one]; exact hc n
  rw [normedField_norm_le_norm_iff, (valuation K).vle_iff_le, map_one] at h1
  exact h1

theorem valuation_lt_one_iff_spectralNorm_lt_one [ValuativeRel L] [ValuativeExtension K L] (x : L) :
    valuation L x < 1 ↔ (letI := normedField K; spectralNorm K L x < 1) := by
  let := normedField K
  let := algebraicNormedField K L
  change valuation L x < 1 ↔ ‖x‖ < 1
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hn
      exact absurd hn (by norm_num)
    have hinv : valuation L x⁻¹ ≤ 1 := by
      refine valuation_le_one_of_spectralNorm_le_one (K := K) ?_
      change ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hn
    rw [map_inv₀] at hinv
    have hv0 : valuation L x ≠ 0 := by simpa using hx0
    have := mul_le_mul_right hinv (valuation L x)
    rw [mul_inv_cancel₀ hv0, mul_one] at this
    exact absurd hx this.not_gt
  · intro hx
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one K
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha0 hx
    have ha : a ≠ 0 := norm_pos_iff.mp ha0
    have hna : algebraMap K L a ≠ 0 := (_root_.map_ne_zero _).mpr ha
    have hnorm : ‖algebraMap K L a‖ = ‖a‖ := algebraicNormedField_norm_algebraMap K L a

    set u := x ^ n * (algebraMap K L a)⁻¹ with hu
    have hu1 : valuation L u ≤ 1 := by
      refine valuation_le_one_of_spectralNorm_le_one (K := K) ?_
      change ‖u‖ ≤ 1
      rw [hu, norm_mul, norm_inv, norm_pow, hnorm]
      exact mul_inv_le_one_of_le₀ hn.le (norm_nonneg _)
    have hva : valuation L (algebraMap K L a) < 1 := by
      refine (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr ?_
      have : ¬ ‖(1 : K)‖ ≤ ‖a‖ := by rw [norm_one]; exact not_le.mpr ha1
      rw [normedField_norm_le_norm_iff, (valuation K).vle_iff_le, map_one] at this
      exact not_le.mp this
    have hxn : x ^ n = u * algebraMap K L a := by
      rw [hu, mul_assoc, inv_mul_cancel₀ hna, mul_one]
    have hpow : valuation L x ^ n < 1 := by
      rw [← map_pow, hxn, map_mul]
      calc valuation L u * valuation L (algebraMap K L a)
          ≤ 1 * valuation L (algebraMap K L a) := mul_le_mul_left hu1 _
        _ < 1 := by rw [one_mul]; exact hva
    by_contra h
    exact (one_le_pow₀ (not_lt.mp h)).not_gt hpow

theorem vle_iff_spectralNorm_le [ValuativeRel L] [ValuativeExtension K L] (x y : L) :
    x ≤ᵥ y ↔ (letI := normedField K; spectralNorm K L x ≤ spectralNorm K L y) := by
  let := normedField K
  let := algebraicNormedField K L
  change x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, norm_nonneg, iff_true]
    exact ValuativeRel.zero_vle y
  · rw [vle_iff_not_valuation_div_lt_one hx, valuation_lt_one_iff_spectralNorm_lt_one (K := K)]
    change ¬ ‖y / x‖ < 1 ↔ _
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hx), not_lt]

variable (K) in

theorem valuativeRel_eq_of_isAlgebraic {v₁ v₂ : ValuativeRel L}
    (e₁ : @ValuativeExtension K L _ _ _ v₁ _) (e₂ : @ValuativeExtension K L _ _ _ v₂ _) :
    v₁ = v₂ := by
  ext x y
  exact (@vle_iff_spectralNorm_le K _ _ _ _ L _ _ _ v₁ e₁ x y).trans
    (@vle_iff_spectralNorm_le K _ _ _ _ L _ _ _ v₂ e₂ x y).symm

theorem valuation_algEquiv_apply_of_isAlgebraic [ValuativeRel L] [ValuativeExtension K L]
    (σ : L ≃ₐ[K] L) (x : L) : valuation L (σ x) = valuation L x := by
  let := normedField K
  have h : spectralNorm K L (σ x) = spectralNorm K L x := (spectralNorm_eq_of_equiv σ x).symm
  refine le_antisymm ?_ ?_
  · rw [← (valuation L).vle_iff_le, vle_iff_spectralNorm_le (K := K), h]
  · rw [← (valuation L).vle_iff_le, vle_iff_spectralNorm_le (K := K), h]

end Spectral

section Existence

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

@[instance_reducible]
def algebraicValuativeRel : ValuativeRel L :=
  letI := algebraicNormedField K L
  haveI := algebraicNormedField_isUltrametricDist K L
  ValuativeRel.ofValuation (NormedField.valuation (K := L))

@[instance_reducible]
def algebraicTopology : TopologicalSpace L :=
  (algebraicNormedField K L).toUniformSpace.toTopologicalSpace

theorem algebraicValuativeRel_vle_iff (x y : L) :
    letI := normedField K
    letI := algebraicValuativeRel K L
    x ≤ᵥ y ↔ spectralNorm K L x ≤ spectralNorm K L y := Iff.rfl

theorem algebraicValuativeRel_valuativeExtension :
    letI := algebraicValuativeRel K L
    ValuativeExtension K L := by
  let := algebraicValuativeRel K L
  constructor
  intro a b
  rw [algebraicValuativeRel_vle_iff]
  let := normedField K
  rw [← normedField_norm_le_norm_iff]
  rw [← algebraicNormedField_norm_algebraMap K L a, ← algebraicNormedField_norm_algebraMap K L b]
  rfl

theorem algebraicValuativeRel_isNontrivial :
    letI := algebraicValuativeRel K L
    IsNontrivial L := by
  let := algebraicNormedField K L
  have := algebraicNormedField_isUltrametricDist K L
  let := algebraicValuativeRel K L
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  rw [isNontrivial_iff_isNontrivial (NormedField.valuation (K := L))]
  infer_instance

theorem algebraicTopology_isValuativeTopology :
    letI := algebraicValuativeRel K L
    letI := algebraicTopology K L
    IsValuativeTopology L := by
  let := algebraicNormedField K L
  have := algebraicNormedField_isUltrametricDist K L
  let := algebraicValuativeRel K L
  have hc : (NormedField.valuation (K := L)).Compatible := Valuation.Compatible.ofValuation _
  exact IsValuativeTopology.of_mem_nhds_zero_iff_vle (NormedField.valuation (K := L))
    (fun {s} ↦ (NormedField.toValued (K := L)).is_topological_valuation s)

end Existence

section SeparableClosure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance separableClosure_valuativeRel : ValuativeRel (SeparableClosure K) :=
  algebraicValuativeRel K (SeparableClosure K)

instance separableClosure_topologicalSpace : TopologicalSpace (SeparableClosure K) :=
  algebraicTopology K (SeparableClosure K)

instance separableClosure_valuativeExtension : ValuativeExtension K (SeparableClosure K) :=
  algebraicValuativeRel_valuativeExtension K (SeparableClosure K)

instance separableClosure_isValuativeTopology : IsValuativeTopology (SeparableClosure K) :=
  algebraicTopology_isValuativeTopology K (SeparableClosure K)

instance separableClosure_isNontrivial : IsNontrivial (SeparableClosure K) :=
  algebraicValuativeRel_isNontrivial K (SeparableClosure K)

end SeparableClosure

section Topology

theorem topologicalSpace_eq_of_isValuativeTopology {R : Type*} [CommRing R] [ValuativeRel R]
    {t₁ t₂ : TopologicalSpace R} (h₁ : @IsValuativeTopology R _ _ t₁)
    (h₂ : @IsValuativeTopology R _ _ t₂) : t₁ = t₂ :=
  TopologicalSpace.ext_nhds fun x ↦ Filter.ext fun s ↦
    (@IsValuativeTopology.mem_nhds_iff R _ _ t₁ h₁ s x).trans
      (@IsValuativeTopology.mem_nhds_iff R _ _ t₂ h₂ s x).symm

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] in

theorem exists_algebraMap_valuation_lt (γ : (ValueGroupWithZero Ω)ˣ) :
    ∃ a : K, a ≠ 0 ∧ valuation Ω (algebraMap K Ω a) < γ := by
  let := normedField K
  let := algebraicNormedField K Ω
  obtain ⟨z, hz⟩ := valuation_surjective (γ : ValueGroupWithZero Ω)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact γ.ne_zero hz.symm
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one K
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hz0) ha1
  have ha : a ≠ 0 := norm_pos_iff.mp ha0
  refine ⟨a ^ n, pow_ne_zero _ ha, ?_⟩
  rw [← hz, ← (valuation Ω).vlt_iff_lt, ← not_vle, vle_iff_spectralNorm_le (K := K), not_le]
  change ‖algebraMap K Ω (a ^ n)‖ < ‖z‖
  rw [algebraicNormedField_norm_algebraMap K Ω, norm_pow]
  exact hn

instance intermediateField_isValuativeTopology (E : IntermediateField K Ω) :
    IsValuativeTopology E := by
  have hmono := ValuativeExtension.mapValueGroupWithZero_strictMono (A := E) (B := Ω)
  have hval := IntermediateField.valuation_coe (E := E)
  have : ContinuousConstVAdd E E :=
    ⟨fun c ↦ continuous_induced_rng.2 (continuous_const.add continuous_subtype_val)⟩
  refine IsValuativeTopology.of_zero fun s ↦ ?_
  have hb := (IsValuativeTopology.hasBasis_nhds_zero Ω).comap ((↑) : E → Ω)
  rw [IsInducing.subtypeVal.nhds_eq_comap, ZeroMemClass.coe_zero]
  refine hb.mem_iff.trans ?_
  constructor
  · rintro ⟨γ, -, hγ⟩
    obtain ⟨a, ha0, ha⟩ := exists_algebraMap_valuation_lt (K := K) γ
    set b : E := algebraMap K E a
    have hb0 : b ≠ 0 := (_root_.map_ne_zero _).mpr ha0
    have hbv : valuation Ω (b : Ω) < γ := by
      rw [IntermediateField.coe_algebraMap_apply]
      exact ha
    refine ⟨Units.mk0 (valuation E b) (by simpa using hb0), fun z hz ↦ hγ ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
    rw [hval] at hbv ⊢
    exact (hmono hz).trans hbv
  · rintro ⟨γ, hγ⟩
    have hγ0 : ValuativeExtension.mapValueGroupWithZero E Ω γ ≠ 0 := by
      rw [← map_zero (ValuativeExtension.mapValueGroupWithZero E Ω)]
      exact (hmono (zero_lt_iff.mpr γ.ne_zero)).ne'
    refine ⟨Units.mk0 _ hγ0, trivial, fun z hz ↦ hγ ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Units.val_mk0] at hz ⊢
    rw [hval] at hz
    exact hmono.lt_iff_lt.mp hz

end Topology

section Inclusion

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [ValuativeRel Ω]

theorem IntermediateField.valuativeExtension_inclusion {E F : IntermediateField K Ω} (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension E F :=
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  ⟨fun a b ↦ by
    rw [← IntermediateField.coe_vle_coe_iff (L := Ω) a b,
      ← IntermediateField.coe_vle_coe_iff (L := Ω)]
    rfl⟩

end Inclusion

section Finite

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

variable (K) in

theorem valuativeRel_eq_finiteExtensionStructure {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [v : ValuativeRel L] [ValuativeExtension K L] :
    v = (finiteExtensionStructure K L).rel :=
  valuativeRel_eq_of_isAlgebraic K inferInstance (finiteExtensionStructure_valuativeExtension K L)

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω]

variable [Algebra.IsAlgebraic K Ω]

instance intermediateField_isNonarchimedeanLocalField_of_finiteDimensional
    (L : IntermediateField K Ω) [FiniteDimensional K L] : IsNonarchimedeanLocalField L := by
  have hrel := valuativeRel_eq_finiteExtensionStructure K (L := L)
  have h1 : @IsNonarchimedeanLocalField L _ (finiteExtensionStructure K L).rel
      (finiteExtensionStructure K L).top :=
    finiteExtensionStructure_isNonarchimedeanLocalField K L
  rw [← hrel] at h1
  have hvt : IsValuativeTopology L := inferInstance
  have ht := topologicalSpace_eq_of_isValuativeTopology hvt h1.toIsValuativeTopology
  rw [← ht] at h1
  exact h1

theorem continuous_algEquiv_of_isAlgebraic (σ : Ω ≃ₐ[K] Ω) : Continuous σ := by
  refine continuous_of_continuousAt_zero σ.toRingEquiv.toAddEquiv.toAddMonoidHom ?_
  change Tendsto σ (𝓝 0) (𝓝 (σ 0))
  rw [map_zero, (IsValuativeTopology.hasBasis_nhds_zero Ω).tendsto_iff
      (IsValuativeTopology.hasBasis_nhds_zero Ω)]
  intro γ _
  refine ⟨γ, trivial, fun x hx ↦ ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rw [valuation_algEquiv_apply_of_isAlgebraic]
  exact hx

def homeomorphOfIsAlgebraic (σ : Ω ≃ₐ[K] Ω) : Ω ≃ₜ Ω where
  toEquiv := σ.toEquiv
  continuous_toFun := continuous_algEquiv_of_isAlgebraic σ
  continuous_invFun := continuous_algEquiv_of_isAlgebraic σ.symm

@[simp]
theorem coe_homeomorphOfIsAlgebraic (σ : Ω ≃ₐ[K] Ω) : ⇑(homeomorphOfIsAlgebraic σ) = σ :=
  rfl

end Finite

section Check

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]

example : IsNonarchimedeanLocalField L := inferInstance
example : ValuativeExtension K L := inferInstance
example : ValuativeExtension L (SeparableClosure K) := inferInstance
example (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : SeparableClosure K) :
    valuation (SeparableClosure K) (σ x) = valuation (SeparableClosure K) x :=
  valuation_algEquiv_apply_of_isAlgebraic σ x

end Check

end Sec_SeparableClosure


/-! ### SeparableClosureValuation -/
section Sec_SeparableClosureValuation

open ValuativeRel IsLocalRing
open scoped WithZero

section Valuation

variable {F G : Type*} [Field F] [ValuativeRel F] [Field G] [ValuativeRel G] [Algebra F G]
  [ValuativeExtension F G]

theorem valuation_algebraMap_eq_iff (x y : F) :
    valuation G (algebraMap F G x) = valuation G (algebraMap F G y) ↔
      valuation F x = valuation F y := by
  rw [le_antisymm_iff, le_antisymm_iff, ← (valuation G).vle_iff_le, ← (valuation G).vle_iff_le,
    ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle, (valuation F).vle_iff_le,
    (valuation F).vle_iff_le]

theorem valuation_algebraMap_le_iff (x y : F) :
    valuation G (algebraMap F G x) ≤ valuation G (algebraMap F G y) ↔
      valuation F x ≤ valuation F y := by
  rw [← (valuation G).vle_iff_le, ValuativeExtension.vle_iff_vle, (valuation F).vle_iff_le]

end Valuation

section Ord

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private theorem ord_zero_alt : ord (0 : K) = 0 := by
  simp [ord]

@[simp]
theorem ord_one : ord (1 : K) = 0 := by
  simp [ord]

private theorem ord_pow_alt (x : K) (n : ℕ) : ord (x ^ n) = n * ord x := by
  simp [ord, WithZero.log_pow]

private theorem ord_zpow_alt (x : K) (n : ℤ) : ord (x ^ n) = n * ord x := by
  simp [ord, map_zpow₀, WithZero.log_zpow]

theorem ord_eq_ord_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord x = ord y ↔ valuation K x = valuation K y := by
  rw [← normalizedValuation_eq_iff, normalizedValuation_eq_exp_ord hx,
    normalizedValuation_eq_exp_ord hy, WithZero.exp_inj, neg_inj]

theorem ord_le_ord_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord x ≤ ord y ↔ valuation K y ≤ valuation K x := by
  rw [← normalizedValuation_le_iff, normalizedValuation_eq_exp_ord hx,
    normalizedValuation_eq_exp_ord hy, WithZero.exp_le_exp, neg_le_neg_iff]

variable (K) in

theorem exists_ord_eq (n : ℤ) : ∃ x : K, x ≠ 0 ∧ ord x = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨(ϖ : K) ^ n, zpow_ne_zero _ hϖ0, by rw [ord_zpow_alt, ord_uniformizer hϖ, mul_one]⟩

end Ord

section Extension

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

private theorem ord_algebraMap_eq_ramificationIndex_mul (a : K) : ord (algebraMap K L a) = ramificationIndex K L * ord a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero

  have hspan : Ideal.span {algebraMap 𝒪[K] 𝒪[L] ϖ} =
      Ideal.span {ϖL ^ ramificationIndex K L} := by
    rw [← Ideal.span_singleton_pow, ← hϖL.maximalIdeal_eq, ← map_maximalIdeal K L,
      hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hu' : algebraMap K L ϖ * ((u : 𝒪[L]) : L) = (ϖL : L) ^ ramificationIndex K L := by
    have := congrArg (fun z : 𝒪[L] ↦ (z : L)) hu
    simpa using this
  have hιϖ : algebraMap K L ϖ ≠ 0 := (_root_.map_ne_zero _).mpr hϖ0
  have hu0 : ((u : 𝒪[L]) : L) ≠ 0 := by
    have : (u : 𝒪[L]) ≠ 0 := u.ne_zero
    exact_mod_cast this
  have hkey : ord (algebraMap K L ϖ) = ramificationIndex K L := by
    have h := congrArg ord hu'
    rw [ord_mul hιϖ hu0, ord_unit, add_zero, ord_pow_alt, ord_uniformizer hϖL, mul_one] at h
    exact h

  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hk : (ϖ : K) ^ ord a ≠ 0 := zpow_ne_zero _ hϖ0
  have hv : valuation K a = valuation K ((ϖ : K) ^ ord a) := by
    rw [← ord_eq_ord_iff ha hk, ord_zpow_alt, ord_uniformizer hϖ, mul_one]
  have hvL : valuation L (algebraMap K L a) = valuation L (algebraMap K L ((ϖ : K) ^ ord a)) :=
    (valuation_algebraMap_eq_iff a _).mpr hv
  rw [← ord_eq_ord_iff ((_root_.map_ne_zero _).mpr ha) ((_root_.map_ne_zero _).mpr hk)] at hvL
  rw [hvL, map_zpow₀, ord_zpow_alt, hkey, mul_comm]

theorem valuation_pow_ramificationIndex_eq {y : L} {a : K} (hy : y ≠ 0) (ha : a ≠ 0)
    (h : ord a = ord y) :
    valuation L y ^ ramificationIndex K L = valuation L (algebraMap K L a) := by
  rw [← map_pow, ← ord_eq_ord_iff (pow_ne_zero _ hy) ((_root_.map_ne_zero _).mpr ha), ord_pow_alt,
    ord_algebraMap_eq_ramificationIndex_mul, h]

end Extension

section Structure

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem isNonarchimedeanLocalField_finiteExtensionStructure_top {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [v : ValuativeRel L] [ValuativeExtension K L] :
    @IsNonarchimedeanLocalField L _ v (finiteExtensionStructure K L).top := by
  have h1 : @IsNonarchimedeanLocalField L _ (finiteExtensionStructure K L).rel
      (finiteExtensionStructure K L).top :=
    finiteExtensionStructure_isNonarchimedeanLocalField K L
  rw [← valuativeRel_eq_finiteExtensionStructure K (L := L)] at h1
  exact h1

end Structure

section Rat

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [Algebra K Ω] [ValuativeExtension K Ω]

open Classical in

def ordRat (x : Ω) : ℚ :=
  if h : ∃ p : ℕ × K, 0 < p.1 ∧ p.2 ≠ 0 ∧ valuation Ω x ^ p.1 = valuation Ω (algebraMap K Ω p.2)
  then (ord h.choose.2 : ℚ) / h.choose.1 else 0

variable {K}

omit [ValuativeExtension K Ω] in

theorem ordRat_congr {x y : Ω} (h : valuation Ω x = valuation Ω y) : ordRat K x = ordRat K y := by
  unfold ordRat
  rw [h]

theorem ordRat_eq_of_pow {x : Ω} {m : ℕ} {a : K} (hm : 0 < m) (ha : a ≠ 0)
    (h : valuation Ω x ^ m = valuation Ω (algebraMap K Ω a)) : ordRat K x = ord a / m := by
  have hex : ∃ p : ℕ × K, 0 < p.1 ∧ p.2 ≠ 0 ∧
      valuation Ω x ^ p.1 = valuation Ω (algebraMap K Ω p.2) := ⟨(m, a), hm, ha, h⟩
  rw [ordRat, dif_pos hex]
  obtain ⟨hp1, hp2, hp3⟩ := hex.choose_spec
  set p := hex.choose

  have hv : valuation Ω (algebraMap K Ω (p.2 ^ m)) = valuation Ω (algebraMap K Ω (a ^ p.1)) := by
    rw [map_pow, map_pow, map_pow, map_pow, ← hp3, ← h, ← pow_mul, ← pow_mul, mul_comm]
  rw [valuation_algebraMap_eq_iff, ← ord_eq_ord_iff (pow_ne_zero _ hp2) (pow_ne_zero _ ha),
    ord_pow_alt, ord_pow_alt] at hv
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hp1' : (p.1 : ℚ) ≠ 0 := by exact_mod_cast hp1.ne'
  rw [div_eq_div_iff hp1' hm']
  have hv' : ((m : ℤ) : ℚ) * (ord p.2 : ℚ) = ((p.1 : ℤ) : ℚ) * (ord a : ℚ) := by exact_mod_cast hv
  push_cast at hv'
  linarith

omit [ValuativeExtension K Ω] in

@[simp]
theorem ordRat_zero : ordRat K (0 : Ω) = 0 := by
  rw [ordRat, dif_neg]
  rintro ⟨p, hp1, hp2, hp3⟩
  rw [map_zero, zero_pow hp1.ne'] at hp3
  exact ((_root_.map_ne_zero _).mpr hp2) ((Valuation.zero_iff _).mp hp3.symm)

@[simp]
theorem ordRat_algebraMap (a : K) : ordRat K (algebraMap K Ω a) = ord a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [ordRat_eq_of_pow one_pos ha (pow_one _), Nat.cast_one, div_one]

@[simp]
theorem ordRat_one : ordRat K (1 : Ω) = 0 := by
  rw [← map_one (algebraMap K Ω), ordRat_algebraMap, ord_one, Int.cast_zero]

theorem ordRat_algebraMap_of_finite {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [Algebra L Ω] [IsScalarTower K L Ω] [ValuativeExtension L Ω] (y : L) :
    ordRat K (algebraMap L Ω y) = ord y / ramificationIndex K L := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  have h := valuation_pow_ramificationIndex_eq K hy ha hay
  rw [← map_pow, ← valuation_algebraMap_eq_iff (G := Ω), map_pow, map_pow,
    ← IsScalarTower.algebraMap_apply] at h
  rw [ordRat_eq_of_pow (ramificationIndex_pos K L) ha h, hay]

variable [Algebra.IsAlgebraic K Ω]

theorem exists_valuation_pow_eq {x : Ω} (hx : x ≠ 0) :
    ∃ (m : ℕ) (a : K), 0 < m ∧ a ≠ 0 ∧ valuation Ω x ^ m = valuation Ω (algebraMap K Ω a) := by
  let L := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let : TopologicalSpace L := (finiteExtensionStructure K L).top
  have : IsNonarchimedeanLocalField L := isNonarchimedeanLocalField_finiteExtensionStructure_top K
  set y := IntermediateField.AdjoinSimple.gen K x
  have hyx : algebraMap L Ω y = x := IntermediateField.AdjoinSimple.algebraMap_gen K x
  have hy : y ≠ 0 := by
    rintro h
    rw [h, map_zero] at hyx
    exact hx hyx.symm
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  have h := valuation_pow_ramificationIndex_eq K hy ha hay
  rw [← map_pow, ← valuation_algebraMap_eq_iff (G := Ω), map_pow, map_pow,
    ← IsScalarTower.algebraMap_apply, hyx] at h
  exact ⟨ramificationIndex K L, a, ramificationIndex_pos K L, ha, h⟩

theorem ordRat_mul {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K (x * y) = ordRat K x + ordRat K y := by
  obtain ⟨m, a, hm, ha, h⟩ := exists_valuation_pow_eq (K := K) hx
  obtain ⟨n, b, hn, hb, h'⟩ := exists_valuation_pow_eq (K := K) hy
  have hab : a ^ n * b ^ m ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)
  have hxy : valuation Ω (x * y) ^ (m * n) = valuation Ω (algebraMap K Ω (a ^ n * b ^ m)) := by
    rw [map_mul, mul_pow, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, ← h, ← h',
      ← pow_mul, ← pow_mul, mul_comm n m]
  rw [ordRat_eq_of_pow (Nat.mul_pos hm hn) hab hxy, ordRat_eq_of_pow hm ha h,
    ordRat_eq_of_pow hn hb h', ord_mul (pow_ne_zero _ ha) (pow_ne_zero _ hb), ord_pow_alt, ord_pow_alt]
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

theorem ordRat_inv {x : Ω} (hx : x ≠ 0) : ordRat K x⁻¹ = -ordRat K x := by
  have h := ordRat_mul (K := K) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordRat_one] at h
  linarith

theorem ordRat_le_ordRat_iff {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x ≤ ordRat K y ↔ valuation Ω y ≤ valuation Ω x := by
  obtain ⟨m, a, hm, ha, h⟩ := exists_valuation_pow_eq (K := K) hx
  obtain ⟨n, b, hn, hb, h'⟩ := exists_valuation_pow_eq (K := K) hy
  have hmn : m * n ≠ 0 := (Nat.mul_pos hm hn).ne'
  have hp : valuation Ω y ^ (m * n) ≤ valuation Ω x ^ (m * n) ↔
      valuation Ω y ≤ valuation Ω x := pow_le_pow_iff_left₀ zero_le zero_le hmn
  rw [← hp]
  have e1 : valuation Ω x ^ (m * n) = valuation Ω (algebraMap K Ω (a ^ n)) := by
    rw [pow_mul, h, map_pow, map_pow]
  have e2 : valuation Ω y ^ (m * n) = valuation Ω (algebraMap K Ω (b ^ m)) := by
    rw [mul_comm, pow_mul, h', map_pow, map_pow]
  rw [e1, e2, valuation_algebraMap_le_iff, ← ord_le_ord_iff (pow_ne_zero _ ha) (pow_ne_zero _ hb),
    ordRat_eq_of_pow hm ha h, ordRat_eq_of_pow hn hb h', ord_pow_alt, ord_pow_alt]
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ hm' hn']
  constructor
  · intro hle
    have h2 : (((n : ℤ) * ord a : ℤ) : ℚ) ≤ (((m : ℤ) * ord b : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h2
  · intro hle
    have : ((n : ℤ) : ℚ) * ord a ≤ ((m : ℤ) : ℚ) * ord b := by exact_mod_cast hle
    push_cast at this
    linarith

theorem ordRat_eq_ordRat_iff {x y : Ω} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordRat K x = ordRat K y ↔ valuation Ω x = valuation Ω y := by
  rw [le_antisymm_iff, le_antisymm_iff, ordRat_le_ordRat_iff hx hy, ordRat_le_ordRat_iff hy hx,
    and_comm]

theorem ordRat_algEquiv (σ : Ω ≃ₐ[K] Ω) (x : Ω) : ordRat K (σ x) = ordRat K x :=
  ordRat_congr (valuation_algEquiv_apply_of_isAlgebraic σ x)

variable (K Ω) in

def ordRatHom : Ωˣ →* Multiplicative ℚ where
  toFun x := Multiplicative.ofAdd (ordRat K (x : Ω))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, ordRat_mul x.ne_zero y.ne_zero, ofAdd_add]

@[simp]
theorem toAdd_ordRatHom (x : Ωˣ) : (ordRatHom K Ω x).toAdd = ordRat K (x : Ω) := rfl

variable (K Ω) in

def valueGroupRat (L : Type*) [Field L] [Algebra L Ω] : AddSubgroup ℚ where
  carrier := Set.range fun y : Lˣ ↦ ordRat K (algebraMap L Ω y)
  zero_mem' := ⟨1, by simp⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨z, rfl⟩
    refine ⟨y * z, ?_⟩
    simp only [Units.val_mul, map_mul]
    exact ordRat_mul ((_root_.map_ne_zero _).mpr y.ne_zero) ((_root_.map_ne_zero _).mpr z.ne_zero)
  neg_mem' := by
    rintro _ ⟨y, rfl⟩
    refine ⟨y⁻¹, ?_⟩
    simp only [Units.val_inv_eq_inv_val, map_inv₀]
    exact ordRat_inv ((_root_.map_ne_zero _).mpr y.ne_zero)

theorem mem_valueGroupRat {L : Type*} [Field L] [Algebra L Ω] {q : ℚ} :
    q ∈ valueGroupRat K Ω L ↔ ∃ y : L, y ≠ 0 ∧ ordRat K (algebraMap L Ω y) = q := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.ne_zero, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Units.mk0 y hy, rfl⟩

variable (K Ω) in

theorem valueGroupRat_base : valueGroupRat K Ω K = AddSubgroup.zmultiples (1 : ℚ) := by
  ext q
  rw [mem_valueGroupRat, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨a, -, rfl⟩
    exact ⟨ord a, by simp⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨a, ha, han⟩ := exists_ord_eq K n
    exact ⟨a, ha, by simp [han]⟩

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [Algebra L Ω] [IsScalarTower K L Ω] [ValuativeExtension L Ω]

variable (K Ω) in

theorem valueGroupRat_eq :
    valueGroupRat K Ω L = AddSubgroup.zmultiples ((ramificationIndex K L : ℚ)⁻¹) := by
  ext q
  rw [mem_valueGroupRat, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨ord y, by rw [ordRat_algebraMap_of_finite, zsmul_eq_mul, div_eq_mul_inv]⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨y, hy, hyn⟩ := exists_ord_eq L n
    exact ⟨y, hy, by rw [ordRat_algebraMap_of_finite, hyn, zsmul_eq_mul, div_eq_mul_inv]⟩

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] [ValuativeExtension L Ω] in
variable (K Ω) in

theorem valueGroupRat_base_le : valueGroupRat K Ω K ≤ valueGroupRat K Ω L := by
  rintro _ ⟨a, rfl⟩
  refine ⟨Units.map (algebraMap K L).toMonoidHom a, ?_⟩
  simp [← IsScalarTower.algebraMap_apply]

variable (K Ω) in

theorem relIndex_valueGroupRat :
    (valueGroupRat K Ω K).relIndex (valueGroupRat K Ω L) = ramificationIndex K L := by
  have he : (ramificationIndex K L : ℚ) ≠ 0 := by exact_mod_cast (ramificationIndex_pos K L).ne'
  set f : ℤ →+ ℚ := zmultiplesHom ℚ (ramificationIndex K L : ℚ)⁻¹
  have hrange : (⊤ : AddSubgroup ℤ).map f = valueGroupRat K Ω L := by
    rw [← AddMonoidHom.range_eq_map, AddSubgroup.range_zmultiplesHom, valueGroupRat_eq]
  have hcomap : (valueGroupRat K Ω K).comap f =
      AddSubgroup.zmultiples ((ramificationIndex K L : ℕ) : ℤ) := by
    ext n
    rw [AddSubgroup.mem_comap, valueGroupRat_base, AddSubgroup.mem_zmultiples_iff,
      AddSubgroup.mem_zmultiples_iff]
    simp only [f, zmultiplesHom_apply, zsmul_eq_mul, mul_one]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have : (k : ℚ) * ramificationIndex K L = n := by
        rw [hk]
        field_simp
      exact_mod_cast this
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      push_cast
      field_simp
  rw [← hrange, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, hcomap,
    Int.index_zmultiples, Int.natAbs_natCast]

end Rat

section Check

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : IntermediateField K (SeparableClosure K)) [FiniteDimensional K L]

example : (valueGroupRat K (SeparableClosure K) K).relIndex (valueGroupRat K (SeparableClosure K) L) =
    ramificationIndex K L :=
  relIndex_valueGroupRat K (SeparableClosure K) L

example : valueGroupRat K (SeparableClosure K) K = AddSubgroup.zmultiples 1 :=
  valueGroupRat_base K (SeparableClosure K)

example (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : SeparableClosure K) :
    ordRat K (σ x) = ordRat K x :=
  ordRat_algEquiv σ x

end Check

end Sec_SeparableClosureValuation


/-! ### UnramifiedDefs -/
section Sec_UnramifiedDefs

open ValuativeRel

class IsUnramified (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] : Prop where

  ramificationIndex_eq_one : ramificationIndex K L = 1

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem isUnramified_iff : IsUnramified K L ↔ ramificationIndex K L = 1 :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ residueDegree K L = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : ramificationIndex K L * residueDegree K L = 1 * residueDegree K L := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this

theorem isUnramified_iff_finrank_residueField :
    IsUnramified K L ↔ Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by
  rw [isUnramified_iff_residueDegree_eq_finrank, residueDegree_eq_finrank]

theorem IsUnramified.residueDegree_eq_finrank [IsUnramified K L] :
    residueDegree K L = Module.finrank K L :=
  (isUnramified_iff_residueDegree_eq_finrank K L).1 inferInstance

theorem IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
  (isUnramified_iff_finrank_residueField K L).1 inferInstance

end Topological

section Tower

variable (K L M : Type*) [Field K] [ValuativeRel K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional L M]

theorem isUnramified_tower_iff :
    IsUnramified K M ↔ IsUnramified K L ∧ IsUnramified L M := by
  simp only [isUnramified_iff, ramificationIndex_tower K L M, mul_eq_one]

theorem IsUnramified.trans [IsUnramified K L] [IsUnramified L M] : IsUnramified K M :=
  (isUnramified_tower_iff K L M).2 ⟨inferInstance, inferInstance⟩

theorem IsUnramified.of_tower_left [IsUnramified K M] : IsUnramified K L :=
  ((isUnramified_tower_iff K L M).1 inferInstance).1

theorem IsUnramified.of_tower_right [IsUnramified K M] : IsUnramified L M :=
  ((isUnramified_tower_iff K L M).1 inferInstance).2

end Tower

end Sec_UnramifiedDefs


/-! ### UnramifiedHensel -/
section Sec_UnramifiedHensel

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField

section Base

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

instance henselianLocalRing_integer : HenselianLocalRing 𝒪[K] where
  toIsLocalRing := inferInstance
  is_henselian f hf a₀ h₁ h₂ := by
    have := isAdicComplete_integer K
    exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

end Base

section Residue

variable (K M : Type*) [Field K] [ValuativeRel K] [Field M] [ValuativeRel M]
  [Algebra K M] [ValuativeExtension K M]

theorem residue_aeval [Algebra 𝓀[K] 𝓀[M]]
    (h : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[M] (residue 𝒪[K] x) =
      residue 𝒪[M] (algebraMap 𝒪[K] 𝒪[M] x))
    (P : 𝒪[K][X]) (x : 𝒪[M]) :
    residue 𝒪[M] (aeval x P) = aeval (residue 𝒪[M] x) (P.map (residue 𝒪[K])) := by
  have hc : (algebraMap 𝓀[K] 𝓀[M]).comp (residue 𝒪[K]) =
      (residue 𝒪[M]).comp (algebraMap 𝒪[K] 𝒪[M]) := RingHom.ext h
  rw [aeval_def, aeval_def, eval₂_map, hc, hom_eval₂]

end Residue

theorem isScalarTower_residueField (K E L : Type*) [Field K] [ValuativeRel K] [Field E]
    [ValuativeRel E] [Field L] [ValuativeRel L] [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] [ValuativeExtension K E] [ValuativeExtension E L]
    [ValuativeExtension K L] [Algebra 𝓀[K] 𝓀[E]] [Algebra 𝓀[E] 𝓀[L]] [Algebra 𝓀[K] 𝓀[L]]
    (h₁ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[E] (residue 𝒪[K] x) =
      residue 𝒪[E] (algebraMap 𝒪[K] 𝒪[E] x))
    (h₂ : ∀ x : 𝒪[E], algebraMap 𝓀[E] 𝓀[L] (residue 𝒪[E] x) =
      residue 𝒪[L] (algebraMap 𝒪[E] 𝒪[L] x))
    (h₃ : ∀ x : 𝒪[K], algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] x) =
      residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)) :
    IsScalarTower 𝓀[K] 𝓀[E] 𝓀[L] := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [h₁, h₂, h₃, IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[E] 𝒪[L]]

section Extension

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_lift_primitive :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧
      P.natDegree = residueDegree K L ∧ (P.map (residue 𝒪[K])).Separable ∧
      IntermediateField.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
  obtain ⟨b, hb⟩ := Field.exists_primitive_element 𝓀[K] 𝓀[L]
  have hbi : IsIntegral 𝓀[K] b := .of_finite _ _
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := lifts_and_natDegree_eq_and_monic
    (f := residue 𝒪[K]) (p := minpoly 𝓀[K] b)
    ((lifts_iff_coeff_lifts _).2 fun n ↦ residue_surjective _) (minpoly.monic hbi)
  have hsep : (minpoly 𝓀[K] b).Separable := Algebra.IsSeparable.isSeparable 𝓀[K] b
  obtain ⟨b0, rfl⟩ := residue_surjective (R := 𝒪[L]) b
  let Q := P.map (algebraMap 𝒪[K] 𝒪[L])
  have hQ : Q.Monic := hPmon.map _
  have h1 : Q.eval b0 ∈ 𝓂[L] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl), hPmap, minpoly.aeval]
  have h2 : IsUnit (Q.derivative.eval b0) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap, residue_aeval K L (fun _ ↦ rfl),
      ← derivative_map, hPmap]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨β, hβ, hβb⟩ := HenselianLocalRing.is_henselian Q hQ b0 h1 h2
  have hres : residue 𝒪[L] β = residue 𝒪[L] b0 := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hβb
  refine ⟨β, P, hPmon, ?_, ?_, ?_, ?_⟩
  · rw [← eval_map_algebraMap]
    exact hβ
  · rw [hPdeg, residueDegree_eq_finrank, ← IntermediateField.adjoin.finrank hbi, hb,
      IntermediateField.finrank_top']
  · rw [hPmap]
    exact hsep
  · rw [hres]
    exact hb

theorem residueDegree_eq_one_iff_surjective (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F L] [ValuativeExtension F L]
    [FiniteDimensional F L] :
    residueDegree F L = 1 ↔ Function.Surjective (algebraMap 𝓀[F] 𝓀[L]) := by
  rw [residueDegree_eq_finrank, ← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  constructor
  · intro h y
    have : y ∈ (⊥ : Subalgebra 𝓀[F] 𝓀[L]) := h ▸ Algebra.mem_top
    exact Algebra.mem_bot.1 this
  · intro h
    refine eq_top_iff.2 fun y _ ↦ Algebra.mem_bot.2 (h y)

theorem exists_unramified_adjoin :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnramified K K⟮(β : L)⟯ ∧ Module.finrank K K⟮(β : L)⟯ = residueDegree K L ∧
      residueDegree K⟮(β : L)⟯ L = 1 := by
  obtain ⟨β, P, hPm, hβ, hdeg, hsep, hgen⟩ := exists_lift_primitive K L
  set T := K⟮(β : L)⟯ with hT
  have hβL : aeval (β : L) P = 0 := by
    have := aeval_algHom_apply (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) β P
    rw [hβ, map_zero] at this
    exact this
  have hle : Module.finrank K T ≤ residueDegree K L := by
    have hi : IsIntegral K (β : L) := .of_finite K _
    rw [hT, IntermediateField.adjoin.finrank hi, ← hdeg]
    have hne : P.map (algebraMap 𝒪[K] K) ≠ 0 := (hPm.map _).ne_zero
    have hd := minpoly.dvd K (β : L) (p := P.map (algebraMap 𝒪[K] K))
      (by rw [aeval_map_algebraMap]; exact hβL)
    calc (minpoly K (β : L)).natDegree ≤ (P.map (algebraMap 𝒪[K] K)).natDegree :=
          natDegree_le_of_dvd hd hne
      _ = P.natDegree := hPm.natDegree_map _
  have hβT : (β : L) ∈ T := IntermediateField.mem_adjoin_simple_self K _
  let βT : 𝒪[T] := ⟨⟨β, hβT⟩, (algebraMap_mem_integer_iff T L _).1 β.2⟩
  have hsurj : Function.Surjective (algebraMap 𝓀[T] 𝓀[L]) := by
    have := isScalarTower_residueField K T L (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    have hb : residue 𝒪[L] β ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range :=
      ⟨residue 𝒪[T] βT, rfl⟩
    have htop : Algebra.adjoin 𝓀[K] {residue 𝒪[L] β} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite _ _), hgen, IntermediateField.top_toSubalgebra]
    have hr : (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range = ⊤ :=
      eq_top_iff.2 (htop ▸ Algebra.adjoin_le (Set.singleton_subset_iff.2 hb))
    intro y
    obtain ⟨z, hz⟩ := (hr ▸ Algebra.mem_top : y ∈ (IsScalarTower.toAlgHom 𝓀[K] 𝓀[T] 𝓀[L]).range)
    exact ⟨z, hz⟩
  have h1 : residueDegree T L = 1 := (residueDegree_eq_one_iff_surjective L T).2 hsurj
  have htower := residueDegree_tower K T L
  rw [h1, mul_one] at htower
  have hfe : residueDegree K T ≤ Module.finrank K T := by
    rw [← ramificationIndex_mul_residueDegree K T]
    exact Nat.le_mul_of_pos_left _ (ramificationIndex_pos K T)
  have heq : Module.finrank K T = residueDegree K T := by omega
  exact ⟨β, P, hPm, hβ, hsep, (isUnramified_iff_residueDegree_eq_finrank K T).2 heq.symm,
    heq.trans htower.symm, h1⟩

theorem mem_of_residueDegree_eq_one (F : IntermediateField K L) (hF : residueDegree F L = 1)
    (P : 𝒪[K][X]) (hP : P.Monic) (γ : 𝒪[L]) (hγ : aeval γ P = 0)
    (hd : IsUnit (aeval γ (derivative P))) : (γ : L) ∈ F := by
  have hsurj := (residueDegree_eq_one_iff_surjective L F).1 hF
  have hinj : Function.Injective (algebraMap 𝓀[F] 𝓀[L]) := (algebraMap 𝓀[F] 𝓀[L]).injective
  obtain ⟨c₀', hc₀'⟩ := hsurj (residue 𝒪[L] γ)
  obtain ⟨c₀, rfl⟩ := residue_surjective (R := 𝒪[F]) c₀'
  have hc₀ : residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] c₀) = residue 𝒪[L] γ := hc₀'

  have key : ∀ Q : 𝒪[K][X], algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
      residue 𝒪[L] (aeval γ Q) := by
    intro Q
    rw [show algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] (aeval c₀ Q)) =
        residue 𝒪[L] (algebraMap 𝒪[F] 𝒪[L] (aeval c₀ Q)) from rfl, ← aeval_algebraMap_apply,
      residue_aeval K L (fun _ ↦ rfl), hc₀, ← residue_aeval K L (fun _ ↦ rfl)]
  let Q := P.map (algebraMap 𝒪[K] 𝒪[F])
  have h1 : Q.eval c₀ ∈ 𝓂[F] := by
    rw [← residue_eq_zero_iff, eval_map_algebraMap]
    apply hinj
    rw [key, hγ, map_zero, map_zero]
  have h2 : IsUnit (Q.derivative.eval c₀) := by
    rw [← residue_ne_zero_iff_isUnit, derivative_map, eval_map_algebraMap]
    intro h0
    have := key (derivative P)
    rw [h0, map_zero] at this
    exact (residue_ne_zero_iff_isUnit _).2 hd this.symm
  obtain ⟨c, hc, hcc₀⟩ := HenselianLocalRing.is_henselian Q (hP.map _) c₀ h1 h2
  have hcF : aeval c P = 0 := by
    rw [← eval_map_algebraMap]
    exact hc
  set c' := algebraMap 𝒪[F] 𝒪[L] c
  have hc' : aeval c' P = 0 := by
    rw [aeval_algebraMap_apply, hcF, map_zero]
  have hres : residue 𝒪[L] c' = residue 𝒪[L] γ := by
    rw [← hc₀]
    have : residue 𝒪[F] c = residue 𝒪[F] c₀ := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hcc₀
    change algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c) = algebraMap 𝓀[F] 𝓀[L] (residue 𝒪[F] c₀)
    rw [this]
  have heq : γ = c' := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact hc') ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [heq]
  exact (c : F).2

end Extension

end Sec_UnramifiedHensel


/-! ### Unramified -/
section Sec_Unramified

open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField


section Generator

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem isUnit_aeval_derivative_of_separable (P : 𝒪[K][X])
    (hP : (P.map (residue 𝒪[K])).Separable) (x : 𝒪[L]) (hx : aeval x P = 0) :
    IsUnit (aeval x (derivative P)) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval K L (fun _ ↦ rfl), ← derivative_map]
  refine hP.aeval_derivative_ne_zero ?_
  rw [← residue_aeval K L (fun _ ↦ rfl), hx, map_zero]

theorem IsUnramified.exists_generator [IsUnramified K L] :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ (P.map (residue 𝒪[K])).Separable ∧
      IsUnit (aeval β (derivative P)) ∧ K⟮(β : L)⟯ = ⊤ := by
  obtain ⟨β, P, hPm, hβ, hsep, -, hdeg, -⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, hsep, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_⟩
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [hdeg, IntermediateField.finrank_top', IsUnramified.residueDegree_eq_finrank K L]

end Generator

section Etale

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem map_maximalIdeal_eq_iff :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) = maximalIdeal 𝒪[L] ↔ IsUnramified K L := by
  rw [map_maximalIdeal K L, isUnramified_iff]
  constructor
  · intro h
    have hpos := ramificationIndex_pos K L
    by_contra hne
    have h2 : 2 ≤ ramificationIndex K L := by omega
    have hL : maximalIdeal 𝒪[L] ≠ ⊥ := maximalIdeal_ne_bot L
    have hlt := Ideal.pow_succ_lt_pow hL 1
    have hle : maximalIdeal 𝒪[L] ^ 1 ≤ maximalIdeal 𝒪[L] ^ (1 + 1) :=
      calc maximalIdeal 𝒪[L] ^ 1 = maximalIdeal 𝒪[L] ^ ramificationIndex K L := by
            rw [pow_one, h]
        _ ≤ maximalIdeal 𝒪[L] ^ (1 + 1) := Ideal.pow_le_pow_right h2
    exact absurd hle (not_le_of_gt hlt)
  · intro h
    rw [h, pow_one]

end Etale

section Maximal

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

def maximalUnramified : IntermediateField K L :=
  sSup {E : IntermediateField K L | IsUnramified K E}

theorem le_maximalUnramified (E : IntermediateField K L) [IsUnramified K E] :
    E ≤ maximalUnramified K L :=
  le_sSup (show IsUnramified K E from inferInstance)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]

variable {K L} in

theorem IsUnramified.of_le {E F : IntermediateField K L} (h : E ≤ F) [IsUnramified K F] :
    IsUnramified K E := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension E F := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  have : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite K E F
  exact IsUnramified.of_tower_left K E F

theorem exists_generator_of_isUnramified (E : IntermediateField K L) [IsUnramified K E] :
    ∃ (γ : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval γ P = 0 ∧ IsUnit (aeval γ (derivative P)) ∧
      E = K⟮(γ : L)⟯ := by
  obtain ⟨β, P, hPm, hβ, -, hd, htop⟩ := IsUnramified.exists_generator K E
  refine ⟨algebraMap 𝒪[E] 𝒪[L] β, P, hPm, ?_, ?_, ?_⟩
  · rw [aeval_algebraMap_apply, hβ, map_zero]
  · rw [aeval_algebraMap_apply]
    exact hd.map _
  · have := congrArg (IntermediateField.map E.val) htop
    rw [IntermediateField.adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val] at this
    exact this.symm

theorem exists_maximalUnramified_eq :
    ∃ (β : 𝒪[L]) (P : 𝒪[K][X]), P.Monic ∧ aeval β P = 0 ∧ IsUnit (aeval β (derivative P)) ∧
      maximalUnramified K L = K⟮(β : L)⟯ ∧ IsUnramified K K⟮(β : L)⟯ ∧
      Module.finrank K K⟮(β : L)⟯ = residueDegree K L ∧ residueDegree K⟮(β : L)⟯ L = 1 := by
  obtain ⟨β, P, hPm, hβ, hsep, hunr, hdeg, h1⟩ := exists_unramified_adjoin K L
  refine ⟨β, P, hPm, hβ, isUnit_aeval_derivative_of_separable K L P hsep β hβ, ?_, hunr, hdeg, h1⟩
  refine le_antisymm (sSup_le fun E hE ↦ ?_) (le_sSup hunr)
  have : IsUnramified K E := hE
  obtain ⟨γ, Q, hQ, hγ, hd, hE'⟩ := exists_generator_of_isUnramified K L E
  rw [hE']
  exact IntermediateField.adjoin_simple_le_iff.2 (mem_of_residueDegree_eq_one K L _ h1 Q hQ γ hγ hd)

instance isUnramified_maximalUnramified : IsUnramified K (maximalUnramified K L) := by
  obtain ⟨β, P, -, -, -, heq, hunr, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hunr

theorem finrank_maximalUnramified :
    Module.finrank K (maximalUnramified K L) = residueDegree K L := by
  obtain ⟨β, P, -, -, -, heq, -, hdeg, -⟩ := exists_maximalUnramified_eq K L
  rw [heq]
  exact hdeg

theorem IsUnramified.sup (E F : IntermediateField K L) [IsUnramified K E] [IsUnramified K F] :
    IsUnramified K (E ⊔ F : IntermediateField K L) :=
  IsUnramified.of_le (sup_le (le_maximalUnramified K L E) (le_maximalUnramified K L F))

theorem IsUnramified.iSup {ι : Type*} (E : ι → IntermediateField K L)
    [∀ i, IsUnramified K (E i)] : IsUnramified K (⨆ i, E i : IntermediateField K L) :=
  IsUnramified.of_le (iSup_le fun i ↦ le_maximalUnramified K L (E i))

end Maximal

section BaseChange

variable (K K' L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K K'] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
  [ValuativeExtension K K'] [ValuativeExtension K' L] [ValuativeExtension K L]
  [FiniteDimensional K L]

end BaseChange

section Galois

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def inertiaSubgroup : Subgroup (L ≃ₐ[K] L) := (residueAlgEquiv K L).ker

theorem inertiaSubgroup_apply_eq (σ : L ≃ₐ[K] L) (hσ : σ ∈ inertiaSubgroup K L) (P : 𝒪[K][X])
    (γ : 𝒪[L]) (hγ : aeval γ P = 0) (hd : IsUnit (aeval γ (derivative P))) : σ γ = γ := by
  set γσ := integerAlgEquiv K L σ γ
  have h0 : aeval γσ P = 0 := by
    have := aeval_algHom_apply (integerAlgEquiv K L σ : 𝒪[L] →ₐ[𝒪[K]] 𝒪[L]) γ P
    rw [hγ, map_zero] at this
    exact this
  have hres : residue 𝒪[L] γσ = residue 𝒪[L] γ := by
    have h1 : residueAlgEquiv K L σ = 1 := hσ
    rw [← residueAlgEquiv_residue, h1]
    rfl
  have heq : γ = γσ := by
    refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := P.map (algebraMap 𝒪[K] 𝒪[L]))
      (by rw [eval_map_algebraMap]; exact hγ) (by rw [eval_map_algebraMap]; exact h0) ?_ ?_
    · rw [← mem_nonunits_iff, ← mem_maximalIdeal, ← residue_eq_zero_iff, map_sub, hres, sub_self]
    · rw [derivative_map, eval_map_algebraMap]
      exact hd
  rw [← coe_integerAlgEquiv_apply]
  exact congrArg Subtype.val heq.symm

theorem maximalUnramified_le_fixedField :
    maximalUnramified K L ≤ IntermediateField.fixedField (inertiaSubgroup K L) := by
  obtain ⟨β, P, -, hβ, hd, heq, -, -, -⟩ := exists_maximalUnramified_eq K L
  rw [heq, IntermediateField.adjoin_simple_le_iff]
  exact fun σ ↦ inertiaSubgroup_apply_eq K L σ σ.2 P β hβ hd

variable [IsGalois K L]

theorem inertiaSubgroup_counting :
    Nat.card (inertiaSubgroup K L) = ramificationIndex K L ∧
      Nat.card (residueAlgEquiv K L).range = residueDegree K L ∧
      Module.finrank K (IntermediateField.fixedField (inertiaSubgroup K L)) = residueDegree K L := by
  set I := inertiaSubgroup K L
  set F := IntermediateField.fixedField I
  have hn := ramificationIndex_mul_residueDegree K L
  have hf := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hFL : Module.finrank F L = Nat.card I := IntermediateField.finrank_fixedField_eq_card I
  have hG : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hIdx : Nat.card I * I.index = Nat.card (L ≃ₐ[K] L) := Subgroup.card_mul_index I
  have hind : I.index = Nat.card (residueAlgEquiv K L).range := Subgroup.index_ker _
  have hrange : Nat.card (residueAlgEquiv K L).range ≤ residueDegree K L := by
    calc Nat.card (residueAlgEquiv K L).range ≤ Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
          Subgroup.card_le_card_group _
      _ = Module.finrank 𝓀[K] 𝓀[L] := IsGalois.card_aut_eq_finrank _ _
      _ = residueDegree K L := (residueDegree_eq_finrank K L).symm
  have hFK : Module.finrank K F * Module.finrank F L = Module.finrank K L :=
    Module.finrank_mul_finrank K F L
  have hTF : residueDegree K L ≤ Module.finrank K F := by
    rw [← finrank_maximalUnramified K L]
    exact IntermediateField.finrank_le_of_le_right (maximalUnramified_le_fixedField K L)
  set a := Nat.card I
  set r := Nat.card (residueAlgEquiv K L).range
  set e := ramificationIndex K L
  set f := residueDegree K L
  set d := Module.finrank K F
  rw [hind, hG, ← hn] at hIdx
  rw [hFL, ← hn] at hFK
  have h1 : a ≤ e := by
    refine Nat.le_of_mul_le_mul_left ?_ hf
    calc f * a ≤ d * a := Nat.mul_le_mul_right _ hTF
      _ = e * f := hFK
      _ = f * e := mul_comm _ _
  have h2 : e ≤ a := by
    refine Nat.le_of_mul_le_mul_right ?_ hf
    calc e * f = a * r := hIdx.symm
      _ ≤ a * f := Nat.mul_le_mul_left _ hrange
  have hae : a = e := le_antisymm h1 h2
  refine ⟨hae, ?_, ?_⟩
  · rw [hae] at hIdx
    exact (Nat.eq_of_mul_eq_mul_left he hIdx)
  · rw [hae, mul_comm e f] at hFK
    exact Nat.eq_of_mul_eq_mul_right he hFK

theorem card_inertiaSubgroup : Nat.card (inertiaSubgroup K L) = ramificationIndex K L :=
  (inertiaSubgroup_counting K L).1

end Galois

end Sec_Unramified


/-! ### UnramifiedRootsOfUnity -/
section Sec_UnramifiedRootsOfUnity

open ValuativeRel Polynomial

section RootsOfUnity

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem exists_pow_eq_one_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {a : 𝓀[L]} (ha : a ^ m = 1) :
    ∃ x : 𝒪[L], x ^ m = 1 ∧ IsLocalRing.residue 𝒪[L] x = a := by
  obtain ⟨a₀, rfl⟩ := IsLocalRing.residue_surjective a
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hmon : (X ^ m - C (1 : 𝒪[L])).Monic := monic_X_pow_sub_C 1 hm0
  have hev : (X ^ m - C (1 : 𝒪[L])).eval a₀ ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp [ha]
  have hder : IsUnit (Ideal.Quotient.mk 𝓂[L] ((X ^ m - C (1 : 𝒪[L])).derivative.eval a₀)) := by
    have ha0 : IsLocalRing.residue 𝒪[L] a₀ ≠ 0 := by
      rintro h
      rw [h, zero_pow hm0] at ha
      exact zero_ne_one ha
    change IsUnit (IsLocalRing.residue 𝒪[L] _)
    rw [isUnit_iff_ne_zero]
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_pow,
      eval_X, eval_natCast, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hm (pow_ne_zero _ ha0)
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  obtain ⟨x, hx, hxa⟩ := HenselianRing.is_henselian _ hmon a₀ hev hder
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hxa

theorem eq_of_pow_eq_one_of_residue_eq {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {x y : 𝒪[L]}
    (hx : x ^ m = 1) (hy : y ^ m = 1)
    (h : IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] y) : x = y := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hxu : IsUnit x := (isUnit_pow_iff hm0).mp (hx ▸ isUnit_one)
  refine IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ m - C 1)
    (by simp [hx]) (by simp [hy]) ?_ ?_
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff,
      map_sub, h, sub_self]
  · simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_pow, eval_X]
    refine IsUnit.mul ?_ (hxu.pow _)
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simpa using hm

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in

theorem mem_integer_of_pow_eq_one {m : ℕ} (hm : m ≠ 0) {x : L} (hx : x ^ m = 1) : x ∈ 𝒪[L] := by
  rw [Valuation.mem_integer_iff]
  have h : valuation L x ^ m = 1 := by rw [← map_pow, hx, map_one]
  refine le_of_not_gt fun h1 ↦ ?_
  have := one_lt_pow₀ h1 hm
  rw [h] at this
  exact this.false

theorem exists_isPrimitiveRoot_card_residueField_sub_one :
    ∃ ζ : 𝒪[L], IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := 𝓀[L]ˣ)
  have hpg : IsPrimitiveRoot (g : 𝓀[L]) (Nat.card 𝓀[L] - 1) := by
    rw [← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg, ← orderOf_units]
    exact IsPrimitiveRoot.orderOf _
  obtain ⟨x, hx, hxg⟩ :=
    exists_pow_eq_one_residue_eq (natCast_card_residueField_sub_one_ne_zero L) hpg.pow_eq_one
  refine ⟨x, hx, fun l hl ↦ hpg.dvd_of_pow_eq_one l ?_⟩
  rw [← hxg, ← map_pow, hl, map_one]

end RootsOfUnity

section Degree

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_minpoly_residue_le (x : 𝒪[L]) :
    (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] x)).natDegree ≤ (minpoly K (x : L)).natDegree := by
  have hx : IsIntegral 𝒪[K] (x : L) := (isIntegral_iff K L x).mpr x.2
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, (minpoly.monic hx).natDegree_map]
  set g := minpoly 𝒪[K] (x : L)
  have hg0 : aeval x g = 0 := by
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← minpoly.aeval 𝒪[K] (x : L)]
    exact (aeval_algebraMap_apply L x g).symm
  have hmon : (g.map (algebraMap 𝒪[K] 𝓀[K])).Monic := (minpoly.monic hx).map _
  refine (natDegree_le_natDegree (minpoly.min 𝓀[K] _ hmon ?_)).trans
    ((minpoly.monic hx).natDegree_map _).le
  rw [aeval_map_algebraMap, ← IsLocalRing.ResidueField.algebraMap_eq, aeval_algebraMap_apply, hg0,
    map_zero]

end Degree

end Sec_UnramifiedRootsOfUnity


/-! ### UnramifiedGalois -/
section Sec_UnramifiedGalois

open ValuativeRel Polynomial _root_.IntermediateField

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ} {ζ : L}

theorem algebra_adjoin_eq_top_of_adjoin_eq_top (htop : K⟮ζ⟯ = ⊤) : Algebra.adjoin K {ζ} = ⊤ :=
  (IntermediateField.adjoin_eq_top_iff (F := K) (E := L)).mp htop

theorem algEquiv_eq_one_of_apply_eq (htop : K⟮ζ⟯ = ⊤) {σ : L ≃ₐ[K] L} (hσ : σ ζ = ζ) : σ = 1 := by
  have h := AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop)
    (φ₁ := σ.toAlgHom) (φ₂ := AlgHom.id K L) (by simpa using hσ)
  ext x
  exact DFunLike.congr_fun h x

theorem isGalois_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m)
    (hm : (m : K) ≠ 0) (htop : K⟮ζ⟯ = ⊤) : IsGalois K L := by
  have : NeZero m := ⟨by rintro rfl; simp at hm⟩
  have : IsCyclotomicExtension {m} K L := by
    rw [IsCyclotomicExtension.iff_singleton]
    refine ⟨⟨ζ, hζ⟩, fun x ↦ ?_⟩
    have hle : Algebra.adjoin K {ζ} ≤ Algebra.adjoin K {b : L | b ^ m = 1} :=
      Algebra.adjoin_mono (by simpa using hζ.pow_eq_one)
    exact hle (by rw [algebra_adjoin_eq_top_of_adjoin_eq_top htop]; trivial)
  exact IsCyclotomicExtension.isGalois {m} K L

end Generic

section PrimitiveResidue

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem isPrimitiveRoot_residue {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) {ζ : 𝒪[L]}
    (hζ : IsPrimitiveRoot ζ m) : IsPrimitiveRoot (IsLocalRing.residue 𝒪[L] ζ) m := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl ↦ hζ.dvd_of_pow_eq_one l ?_⟩
  refine eq_of_pow_eq_one_of_residue_eq hm ?_ (one_pow m) (by rw [map_pow, hl, map_one])
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem natCast_ne_zero_of_residueField {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0) : (m : L) ≠ 0 := by
  intro h
  apply hm
  have : (m : 𝒪[L]) = 0 := Subtype.ext (by simpa using h)
  rw [← map_natCast (IsLocalRing.residue 𝒪[L]), this, map_zero]

end PrimitiveResidue

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Residue

variable (L) in

theorem natCast_residueField_ne_zero {m : ℕ} (hm : (m : 𝓀[K]) ≠ 0) : (m : 𝓀[L]) ≠ 0 := by
  rw [← map_natCast (algebraMap 𝓀[K] 𝓀[L])]
  exact (map_ne_zero_iff _ (algebraMap 𝓀[K] 𝓀[L]).injective).mpr hm

end Residue

section Cyclotomic

variable {m : ℕ} {ζ : L}

private def rootInteger (hm : m ≠ 0) (hζ : ζ ^ m = 1) : 𝒪[L] :=
  ⟨ζ, mem_integer_of_pow_eq_one hm hζ⟩

variable (K L) in

theorem residueAlgEquiv_injective_of_adjoin_eq_top (hm : (m : 𝓀[K]) ≠ 0) (hζ : ζ ^ m = 1)
    (htop : K⟮ζ⟯ = ⊤) : Function.Injective (residueAlgEquiv K L) := by
  have hmL := natCast_residueField_ne_zero L hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply algEquiv_eq_one_of_apply_eq htop
  set z := rootInteger hm0 hζ
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z, rootInteger] using hζ)
  have key : integerAlgEquiv K L σ z = z := by
    refine eq_of_pow_eq_one_of_residue_eq hmL (by rw [← map_pow, hz, map_one]) hz ?_
    rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]
  simpa [z, rootInteger] using congrArg Subtype.val key

theorem ramificationIndex_eq_one_of_adjoin_eq_top (hζ : IsPrimitiveRoot ζ m) (hm : (m : 𝓀[K]) ≠ 0)
    (htop : K⟮ζ⟯ = ⊤) : ramificationIndex K L = 1 := by
  have := isGalois_of_adjoin_eq_top hζ (natCast_ne_zero_of_residueField (L := K) hm) htop
  have hinj := residueAlgEquiv_injective_of_adjoin_eq_top K L hm hζ.pow_eq_one htop
  have hcard : Module.finrank K L ≤ residueDegree K L := by
    rw [← IsGalois.card_aut_eq_finrank, residueDegree_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_le_card_of_injective _ hinj
  have hf := residueDegree_pos K L
  rw [← ramificationIndex_mul_residueDegree K L] at hcard
  have he := ramificationIndex_pos K L
  nlinarith

end Cyclotomic

section Unramified

variable (K L)

theorem residueDegree_eq_finrank_of_unramified (h : ramificationIndex K L = 1) :
    residueDegree K L = Module.finrank K L := by
  rw [← ramificationIndex_mul_residueDegree K L, h, one_mul]

theorem exists_isPrimitiveRoot_adjoin_eq_top_of_unramified (h : ramificationIndex K L = 1) :
    ∃ ζ : L, IsPrimitiveRoot ζ (Nat.card 𝓀[L] - 1) ∧ K⟮ζ⟯ = ⊤ := by
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot_card_residueField_sub_one (L := L)
  refine ⟨z, hz.map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective, ?_⟩
  have hres := isPrimitiveRoot_residue (natCast_card_residueField_sub_one_ne_zero L) hz
  have htop' : 𝓀[K]⟮IsLocalRing.residue 𝒪[L] z⟯ = ⊤ := by
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]
      exact zero_mem _
    · have := Fintype.ofFinite 𝓀[L]
      have : NeZero (Nat.card 𝓀[L] - 1) := ⟨fun h0 ↦
        natCast_card_residueField_sub_one_ne_zero L (by rw [h0, Nat.cast_zero])⟩
      have hy1 : y ^ (Nat.card 𝓀[L] - 1) = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_sub_one_eq_one y hy
      obtain ⟨i, -, rfl⟩ := hres.eq_pow_of_pow_eq_one hy1
      exact pow_mem (mem_adjoin_simple_self _ _) _
  refine eq_of_le_of_finrank_le le_top ?_
  rw [finrank_top', adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank]
  calc Module.finrank 𝓀[K] 𝓀[L] = Module.finrank 𝓀[K] 𝓀[K]⟮IsLocalRing.residue 𝒪[L] z⟯ := by
        rw [htop', finrank_top']
    _ = (minpoly 𝓀[K] (IsLocalRing.residue 𝒪[L] z)).natDegree :=
        adjoin.finrank (Algebra.IsIntegral.isIntegral _)
    _ ≤ _ := natDegree_minpoly_residue_le z

theorem isGalois_of_unramified (h : ramificationIndex K L = 1) : IsGalois K L := by
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hm := natCast_ne_zero_of_residueField (natCast_card_residueField_sub_one_ne_zero L)
  refine isGalois_of_adjoin_eq_top hζ (fun h0 ↦ hm ?_) htop
  rw [← map_natCast (algebraMap K L), h0, map_zero]

theorem residueAlgEquiv_injective_of_unramified (h : ramificationIndex K L = 1) :
    Function.Injective (residueAlgEquiv K L) := by
  obtain ⟨ζ, hζ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hm := natCast_card_residueField_sub_one_ne_zero L
  refine residueAlgEquiv_injective_of_adjoin_eq_top K L (m := Nat.card 𝓀[L] - 1) (fun h0 ↦ hm ?_)
    hζ.pow_eq_one htop
  rw [← map_natCast (algebraMap 𝓀[K] 𝓀[L]), h0, map_zero]

theorem card_algEquiv_of_unramified (h : ramificationIndex K L = 1) :
    Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
  have := isGalois_of_unramified K L h
  exact IsGalois.card_aut_eq_finrank K L

theorem residueAlgEquiv_bijective_of_unramified (h : ramificationIndex K L = 1) :
    Function.Bijective (residueAlgEquiv K L) := by
  refine (residueAlgEquiv_injective_of_unramified K L h).bijective_of_nat_card_le ?_
  rw [card_algEquiv_of_unramified K L h, IsGalois.card_aut_eq_finrank, ← residueDegree_eq_finrank,
    residueDegree_eq_finrank_of_unramified K L h]

def galoisEquivResidue (h : ramificationIndex K L = 1) :
    (L ≃ₐ[K] L) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (residueAlgEquiv K L) (residueAlgEquiv_bijective_of_unramified K L h)

@[simp]
theorem galoisEquivResidue_apply (h : ramificationIndex K L = 1) (σ : L ≃ₐ[K] L) :
    galoisEquivResidue K L h σ = residueAlgEquiv K L σ :=
  rfl

theorem isCyclic_of_unramified (h : ramificationIndex K L = 1) : IsCyclic (L ≃ₐ[K] L) :=
  isCyclic_of_surjective (galoisEquivResidue K L h).symm.toMonoidHom
    (galoisEquivResidue K L h).symm.surjective

def frobenius (h : ramificationIndex K L = 1) : L ≃ₐ[K] L :=
  letI := Fintype.ofFinite 𝓀[K]
  (galoisEquivResidue K L h).symm (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L])

theorem residueAlgEquiv_frobenius_apply (h : ramificationIndex K L = 1) (y : 𝓀[L]) :
    residueAlgEquiv K L (frobenius K L h) y = y ^ Nat.card 𝓀[K] := by
  let := Fintype.ofFinite 𝓀[K]
  have : residueAlgEquiv K L (frobenius K L h) =
      FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] :=
    (galoisEquivResidue K L h).apply_symm_apply _
  rw [this, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card]

theorem residue_frobenius_apply (h : ramificationIndex K L = 1) (x : 𝒪[L]) :
    IsLocalRing.residue 𝒪[L] (integerAlgEquiv K L (frobenius K L h) x) =
      IsLocalRing.residue 𝒪[L] x ^ Nat.card 𝓀[K] := by
  rw [← residueAlgEquiv_residue, residueAlgEquiv_frobenius_apply]

theorem frobenius_sub_pow_mem_maximalIdeal (h : ramificationIndex K L = 1) (x : 𝒪[L]) :
    integerAlgEquiv K L (frobenius K L h) x - x ^ Nat.card 𝓀[K] ∈ 𝓂[L] := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, residue_frobenius_apply, sub_self]

theorem orderOf_frobenius (h : ramificationIndex K L = 1) :
    orderOf (frobenius K L h) = Module.finrank K L := by
  let := Fintype.ofFinite 𝓀[K]
  rw [frobenius, MulEquiv.orderOf_eq, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
    ← residueDegree_eq_finrank, residueDegree_eq_finrank_of_unramified K L h]

theorem zpowers_frobenius (h : ramificationIndex K L = 1) :
    Subgroup.zpowers (frobenius K L h) = ⊤ := by
  let := Fintype.ofFinite 𝓀[K]
  rw [eq_top_iff]
  intro σ _
  obtain ⟨k, hk⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K] 𝓀[L]).2
    (galoisEquivResidue K L h σ)
  refine ⟨(k : ℕ), ?_⟩
  apply (galoisEquivResidue K L h).injective
  simp only [zpow_natCast, map_pow]
  rw [← hk, frobenius, MulEquiv.apply_symm_apply]

variable {K L}

theorem frobenius_apply_of_pow_eq_one (h : ramificationIndex K L = 1) {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) {ξ : L} (hξ : ξ ^ m = 1) :
    frobenius K L h ξ = ξ ^ Nat.card 𝓀[K] := by
  have hmL := natCast_residueField_ne_zero L hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  set z : 𝒪[L] := ⟨ξ, mem_integer_of_pow_eq_one hm0 hξ⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hξ)
  have key : integerAlgEquiv K L (frobenius K L h) z = z ^ Nat.card 𝓀[K] := by
    refine eq_of_pow_eq_one_of_residue_eq hmL (by rw [← map_pow, hz, map_one]) ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]
    · rw [residue_frobenius_apply, map_pow]
  simpa [z] using congrArg Subtype.val key

theorem natCast_card_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
  have := Fintype.ofFinite 𝓀[K]
  rw [Nat.cast_sub (Nat.one_le_pow _ _ Nat.card_pos), Nat.cast_pow, Nat.card_eq_fintype_card,
    FiniteField.cast_card_eq_zero, zero_pow hn, Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

theorem finrank_eq_of_adjoin_eq_top {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (htop : K⟮ζ⟯ = ⊤) :
    Module.finrank K L = n := by
  set q := Nat.card 𝓀[K] with hq_def
  have hq : 1 < q := one_lt_card_residueField K
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have h := ramificationIndex_eq_one_of_adjoin_eq_top hζ hm htop
  set F := frobenius K L h
  have hF : F ζ = ζ ^ q := frobenius_apply_of_pow_eq_one h hm hζ.pow_eq_one
  have hFk : ∀ k : ℕ, (F ^ k) ζ = ζ ^ (q ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hF, ← pow_mul, ← pow_succ']
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by
    have : 1 < q ^ n := Nat.one_lt_pow hn hq
    omega)
  have hpow : ∀ k : ℕ, ζ ^ (q ^ k) = ζ ↔ ζ ^ (q ^ k - 1) = 1 := by
    intro k
    have h1 : q ^ k = q ^ k - 1 + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    conv_lhs => rw [h1, pow_succ]
    constructor
    · intro h2
      exact mul_left_cancel₀ hζ0 (by rw [mul_one, mul_comm]; exact h2)
    · intro h2
      rw [h2, one_mul]
  have hd := orderOf_frobenius K L h
  have hfin := Module.finrank_pos (R := K) (M := L)
  apply le_antisymm
  ·
    have hFn : F ^ n = 1 := by
      apply algEquiv_eq_one_of_apply_eq htop
      rw [hFk, hpow]
      exact hζ.pow_eq_one
    rw [← hd]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (orderOf_dvd_of_pow_eq_one hFn)
  ·
    have h1 : ζ ^ (q ^ Module.finrank K L - 1) = 1 := by
      rw [← hpow, ← hFk, ← hd, pow_orderOf_eq_one, AlgEquiv.one_apply]
    have hdvd := hζ.dvd_of_pow_eq_one _ h1
    have hlt : 1 < q ^ Module.finrank K L := Nat.one_lt_pow hfin.ne' hq
    have hle := Nat.le_of_dvd (by omega) hdvd
    have : q ^ n ≤ q ^ Module.finrank K L := by
      have := Nat.one_le_pow n q (by omega)
      omega
    exact (Nat.pow_le_pow_iff_right hq).mp this

end Unramified

end Sec_UnramifiedGalois


/-! ### UnramifiedExistence -/
section Sec_UnramifiedExistence

open ValuativeRel _root_.IntermediateField

section Card

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem card_residueField_of_unramified (h : ramificationIndex K L = 1) :
    Nat.card 𝓀[L] = Nat.card 𝓀[K] ^ Module.finrank K L := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[L]
  rw [← residueDegree_eq_finrank_of_unramified K L h, residueDegree_eq_finrank,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])]

end Card

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem adjoin_gen_eq_top (α : Ksep) : K⟮AdjoinSimple.gen K α⟯ = ⊤ := by
  apply map_injective K⟮α⟯.val
  rw [adjoin_map, Set.image_singleton, ← AlgHom.fieldRange_eq_map, fieldRange_val]
  exact congrArg (fun x ↦ K⟮x⟯) (AdjoinSimple.coe_gen K α)

def IsUnramifiedSubextension (E : IntermediateField K Ksep) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), ramificationIndex K E = 1

theorem isUnramifiedSubextension_iff_exists (E : IntermediateField K Ksep) :
    IsUnramifiedSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), ramificationIndex K E = 1 := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem IsUnramifiedSubextension.ramificationIndex_eq_one {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] : ramificationIndex K E = 1 :=
  hE.2 inferInstance inferInstance inferInstance inferInstance

theorem IsUnramifiedSubextension.isGalois {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsGalois K E := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isGalois_of_unramified K E hE.ramificationIndex_eq_one

theorem IsUnramifiedSubextension.isCyclic {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : IsCyclic (E ≃ₐ[K] E) := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  exact isCyclic_of_unramified K E hE.ramificationIndex_eq_one

theorem IsUnramifiedSubextension.card_algEquiv {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
  have := hE.1
  have := hE.isGalois
  exact IsGalois.card_aut_eq_finrank K E

theorem exists_isPrimitiveRoot_card_pow_sub_one [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : Ksep, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  classical
  set m := Nat.card 𝓀[K] ^ n - 1
  have hm0 : m ≠ 0 := by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega
  have hK := natCast_ne_zero_of_residueField (natCast_card_pow_sub_one_ne_zero (K := K) hn)
  have hmKsep : (m : Ksep) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ksep)]
    exact (map_ne_zero_iff _ (algebraMap K Ksep).injective).mpr hK
  have hsep : (Polynomial.X ^ m - 1 : Polynomial Ksep).Separable := by
    simpa only [map_one] using Polynomial.separable_X_pow_sub_C (1 : Ksep) hmKsep one_ne_zero
  have hspl : (Polynomial.X ^ m - 1 : Polynomial Ksep).Splits :=
    IsSepClosed.splits_of_separable _ hsep
  have hne0 : (Polynomial.X ^ m - 1 : Polynomial Ksep) ≠ 0 := hsep.ne_zero
  have hcard_roots : (Polynomial.X ^ m - 1 : Polynomial Ksep).roots.toFinset.card = m := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      ← hspl.natDegree_eq_card_roots]
    simpa only [map_one] using Polynomial.natDegree_X_pow_sub_C (n := m) (r := (1 : Ksep))
  have hmem_iff : ∀ x : Ksep,
      x ∈ (Polynomial.X ^ m - 1 : Polynomial Ksep).roots.toFinset ↔ x ^ m = 1 := by
    intro x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne0, Polynomial.IsRoot,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, sub_eq_zero]
  let e : (Polynomial.X ^ m - 1 : Polynomial Ksep).roots.toFinset ≃ rootsOfUnity m Ksep :=
    { toFun := fun x ↦
        have hx1 : x.1 ^ m = 1 := (hmem_iff x.1).mp x.2
        have hx0 : x.1 ≠ 0 := fun h0 ↦ by rw [h0, zero_pow hm0] at hx1; exact zero_ne_one hx1
        ⟨Units.mk0 x.1 hx0, by
          rw [mem_rootsOfUnity]
          ext
          simpa [Units.val_pow_eq_pow_val] using hx1⟩
      invFun := fun u ↦
        ⟨(u.1 : Ksep), (hmem_iff _).mpr (by
          have hu := (mem_rootsOfUnity m u.1).mp u.2
          simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hu)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ by ext; rfl }
  let _ : Fintype (rootsOfUnity m Ksep) := Fintype.ofEquiv _ e
  have hcard : Fintype.card (rootsOfUnity m Ksep) = m := by
    rw [Fintype.card_congr e.symm, Fintype.card_coe, hcard_roots]
  have _ : NeZero m := ⟨hm0⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity m Ksep)
  have hord_g : orderOf g = m :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans (Nat.card_eq_fintype_card.trans hcard)
  have hord_val : orderOf ((g.1 : Ksepˣ) : Ksep) = m := by
    rw [← Units.coeHom_apply, orderOf_injective (Units.coeHom Ksep) Units.val_injective,
      Subgroup.orderOf_coe, hord_g]
  refine ⟨(g.1 : Ksep), ?_, fun l hl ↦ ?_⟩
  · have h := pow_orderOf_eq_one ((g.1 : Ksepˣ) : Ksep)
    rwa [hord_val] at h
  · have h := orderOf_dvd_of_pow_eq_one hl
    rwa [hord_val] at h

theorem isUnramifiedSubextension_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n := by
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hpos : 0 < Nat.card 𝓀[K] ^ n - 1 := by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega
  have hint : IsIntegral K ζ := (hζ.isIntegral hpos).tower_top
  have hfin : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional hint
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  have htop := adjoin_gen_eq_top (K := K) ζ
  refine ⟨⟨hfin, fun _ _ _ _ ↦ ramificationIndex_eq_one_of_adjoin_eq_top hζ' hm htop⟩, ?_⟩
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  exact finrank_eq_of_adjoin_eq_top hn hζ' htop

theorem IsUnramifiedSubextension.eq_adjoin {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hEn : Module.finrank K E = n) (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E = K⟮ζ⟯ := by
  have := hE.1
  let := (finiteExtensionStructure K E).rel
  let := (finiteExtensionStructure K E).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K E
  have := finiteExtensionStructure_valuativeExtension K E
  have h := hE.ramificationIndex_eq_one
  obtain ⟨ξ, hξ, -⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K E h
  rw [card_residueField_of_unramified K E h, hEn] at hξ
  have hξ' : IsPrimitiveRoot (ξ : Ksep) (Nat.card 𝓀[K] ^ n - 1) :=
    hξ.map_of_injective (f := E.val) Subtype.val_injective
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by
    have := Nat.one_lt_pow hn (one_lt_card_residueField K)
    omega⟩
  obtain ⟨i, -, hi⟩ := hξ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hζE : ζ ∈ E := hi ▸ pow_mem ξ.2 i
  have hle : K⟮ζ⟯ ≤ E := adjoin_simple_le_iff.mpr hζE
  refine (eq_of_le_of_finrank_eq hle ?_).symm
  rw [(isUnramifiedSubextension_adjoin hn hζ).2, hEn]

theorem existsUnique_isUnramifiedSubextension [IsSepClosed Ksep] {n : ℕ} (hn : n ≠ 0) :
    ∃! E : IntermediateField K Ksep, IsUnramifiedSubextension E ∧ Module.finrank K E = n := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ksep) hn
  exact ⟨K⟮ζ⟯, isUnramifiedSubextension_adjoin hn hζ,
    fun E ⟨hE, hEn⟩ ↦ hE.eq_adjoin hEn hn hζ⟩

theorem isUnramifiedSubextension_adjoin_spec {n : ℕ} (hn : n ≠ 0) {ζ : Ksep}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    IsUnramifiedSubextension K⟮ζ⟯ ∧ Module.finrank K K⟮ζ⟯ = n ∧ IsGalois K K⟮ζ⟯ ∧
      IsCyclic (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) ∧ Nat.card (K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯) = n ∧
      ∀ E : IntermediateField K Ksep, IsUnramifiedSubextension E → Module.finrank K E = n →
        E = K⟮ζ⟯ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  exact ⟨hE, hEn, hE.isGalois, hE.isCyclic, hE.card_algEquiv.trans hEn,
    fun E hE' hE'n ↦ hE'.eq_adjoin hE'n hn hζ⟩

variable {E : IntermediateField K Ksep} (hE : IsUnramifiedSubextension E)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E]
include hE

end SeparableClosure

end Sec_UnramifiedExistence


/-! ### UnramifiedNormSurj -/
section Sec_UnramifiedNormSurj

open ValuativeRel IsLocalRing Filter Polynomial

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in

theorem coe_normIntegerUnits_eq (u : 𝒪[L]ˣ) :
    ((normIntegerUnits K L u : 𝒪[K]ˣ) : 𝒪[K]) = Algebra.norm 𝒪[K] (u : 𝒪[L]) :=
  rfl

theorem exists_norm_one_add_smul (r : 𝒪[K]) (a : 𝒪[L]) :
    ∃ c : 𝒪[K], Algebra.norm 𝒪[K] (1 + r • a) =
      1 + r * Algebra.trace 𝒪[K] 𝒪[L] a + r ^ 2 * c := by
  classical
  let b := Module.Free.chooseBasis 𝒪[K] 𝒪[L]
  refine ⟨(Matrix.det (1 + (X : 𝒪[K][X]) • (Algebra.leftMulMatrix b a).map C)).divX.divX.eval r,
    ?_⟩
  rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul,
    Algebra.trace_eq_matrix_trace b]
  ring

theorem residue_eq_sum_repr (y : 𝒪[L]) :
    residue 𝒪[L] y = ∑ i, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) •
      residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  conv_lhs => rw [← (Module.Free.chooseBasis 𝒪[K] 𝒪[L]).sum_repr y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  rfl

section Residue

variable [IsUnramified K L]

variable (K L) in

def residueBasis : Module.Basis (Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) 𝓀[K] 𝓀[L] :=
  basisOfTopLeSpanOfCardEqFinrank (fun i ↦ residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i))
    (by
      rintro z -
      obtain ⟨y, rfl⟩ := residue_surjective z
      rw [residue_eq_sum_repr (K := K)]
      exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_integer K L,
        IsUnramified.finrank_residueField K L])

theorem residueBasis_apply (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    residueBasis K L i = residue 𝒪[L] (Module.Free.chooseBasis 𝒪[K] 𝒪[L] i) := by
  simp [residueBasis]

theorem residueBasis_repr (y : 𝒪[L]) (i : Module.Free.ChooseBasisIndex 𝒪[K] 𝒪[L]) :
    (residueBasis K L).repr (residue 𝒪[L] y) i =
      residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y i) := by
  have h : residue 𝒪[L] y = ∑ j, residue 𝒪[K] ((Module.Free.chooseBasis 𝒪[K] 𝒪[L]).repr y j) •
      residueBasis K L j := by
    simp only [residueBasis_apply]
    exact residue_eq_sum_repr y
  rw [h, (residueBasis K L).repr_sum_self]

theorem leftMulMatrix_residueBasis (y : 𝒪[L]) :
    Algebra.leftMulMatrix (residueBasis K L) (residue 𝒪[L] y) =
      (Algebra.leftMulMatrix (Module.Free.chooseBasis 𝒪[K] 𝒪[L]) y).map (residue 𝒪[K]) := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    residueBasis_apply, ← map_mul, residueBasis_repr]

theorem residue_norm (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.norm 𝒪[K] y) = Algebra.norm 𝓀[K] (residue 𝒪[L] y) := by
  classical
  rw [Algebra.norm_eq_matrix_det (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.norm_eq_matrix_det (residueBasis K L), leftMulMatrix_residueBasis, RingHom.map_det]
  rfl

theorem residue_trace (y : 𝒪[L]) :
    residue 𝒪[K] (Algebra.trace 𝒪[K] 𝒪[L] y) = Algebra.trace 𝓀[K] 𝓀[L] (residue 𝒪[L] y) := by
  rw [Algebra.trace_eq_matrix_trace (Module.Free.chooseBasis 𝒪[K] 𝒪[L]),
    Algebra.trace_eq_matrix_trace (residueBasis K L), leftMulMatrix_residueBasis]
  exact AddMonoidHom.map_trace (residue 𝒪[K]).toAddMonoidHom _

theorem irreducible_algebraMap_of_isUnramified {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  have h := map_maximalIdeal K L
  rw [IsUnramified.ramificationIndex_eq_one, pow_one, hϖ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton] at h
  exact h.symm

theorem trace_integer_surjective : Function.Surjective (Algebra.trace 𝒪[K] 𝒪[L]) := by
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] 1
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu : IsUnit (Algebra.trace 𝒪[K] 𝒪[L] a) := by
    rw [← residue_ne_zero_iff_isUnit, residue_trace, ht]
    exact one_ne_zero
  intro c
  refine ⟨(((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) • a, ?_⟩
  rw [map_smul, smul_eq_mul]
  linear_combination c * Units.inv_mul hu.unit - (((hu.unit⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * c) * hu.unit_spec

theorem normIntegerUnits_mem_unitFiltration {n : ℕ} {u : 𝒪[L]ˣ} (hu : u ∈ unitFiltration L n) :
    normIntegerUnits K L u ∈ unitFiltration K n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖL).mp (mem_unitFiltration.mp hu)
  have hu' : (u : 𝒪[L]) = 1 + ϖ ^ n • a := by
    rw [Algebra.smul_def, map_pow, ← ha]
    ring
  obtain ⟨c, hc⟩ := exists_norm_one_add_smul (ϖ ^ n) a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ]
  refine ⟨Algebra.trace 𝒪[K] 𝒪[L] a + ϖ ^ n * c, ?_⟩
  rw [coe_normIntegerUnits_eq, hu', hc]
  ring

theorem exists_normIntegerUnits_div_mem_one (h : 𝒪[K]ˣ) :
    ∃ g : 𝒪[L]ˣ, h / normIntegerUnits K L g ∈ unitFiltration K 1 := by
  obtain ⟨ζ, hζ⟩ := FiniteField.unitsMap_norm_surjective 𝓀[K] 𝓀[L] (unitsToResidue K h)
  obtain ⟨g, rfl⟩ := unitsToResidue_surjective L ζ
  refine ⟨g, ?_⟩
  rw [← ker_unitsToResidue, MonoidHom.mem_ker, _root_.map_div, div_eq_one, ← hζ]
  ext
  simp [coe_normIntegerUnits_eq, residue_norm]

theorem exists_normIntegerUnits_div_mem_succ {n : ℕ} (hn : 1 ≤ n) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K n) :
    ∃ g ∈ unitFiltration L n, h / normIntegerUnits K L g ∈ unitFiltration K (n + 1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨c, hc⟩ := (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp hh)
  obtain ⟨t, ht⟩ := Algebra.trace_surjective 𝓀[K] 𝓀[L] (residue 𝒪[K] c)
  obtain ⟨a, rfl⟩ := residue_surjective t
  have hu := isUnit_one_add_mul hϖL hn a
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [mem_unitFiltration, IsUnit.unit_spec, add_sub_cancel_left, mem_maximalIdeal_pow_iff hϖL]
    exact dvd_mul_right _ _
  · rw [div_mem_unitFiltration_iff]
    obtain ⟨d, hd⟩ := exists_norm_one_add_smul (ϖ ^ n) a
    have e1 : ((normIntegerUnits K L hu.unit : 𝒪[K]ˣ) : 𝒪[K]) =
        1 + ϖ ^ n * Algebra.trace 𝒪[K] 𝒪[L] a + (ϖ ^ n) ^ 2 * d := by
      rw [coe_normIntegerUnits_eq, IsUnit.unit_spec, ← hd, Algebra.smul_def, map_pow]
    have e2 : c - Algebra.trace 𝒪[K] 𝒪[L] a ∈ 𝓂[K] := by
      rw [← residue_eq_zero_iff, map_sub, residue_trace, ht, sub_self]
    obtain ⟨e, he⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp e2
    have hh' : (h : 𝒪[K]) = 1 + ϖ ^ n * c := by
      rw [← hc]
      ring
    rw [mem_maximalIdeal_pow_iff hϖ]
    refine ⟨e - ϖ ^ (n - 1) * d, ?_⟩
    rw [e1, hh']
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    linear_combination (ϖ ^ (m + 1)) * he

theorem map_normIntegerUnits_unitFiltration (n : ℕ) :
    (unitFiltration L n).map (normIntegerUnits K L) = unitFiltration K n :=
  map_eq_of_graded_surjective (unitFiltration_antitone L) (unitFiltration_antitone K)
    filtrationComplete_unitFiltration filtrationSeparated_unitFiltration
    (normIntegerUnits K L) (φ := id) tendsto_id n
    (fun _ _ _ hg ↦ normIntegerUnits_mem_unitFiltration hg)
    (fun m _ h hh ↦ by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨g, hg⟩ := exists_normIntegerUnits_div_mem_one (L := L) h
        exact ⟨g, by simp, hg⟩
      · exact exists_normIntegerUnits_div_mem_succ hm hh)

theorem normIntegerUnits_surjective : Function.Surjective (normIntegerUnits K L) := by
  intro h
  have e := map_normIntegerUnits_unitFiltration (K := K) (L := L) 0
  rw [unitFiltration_zero, unitFiltration_zero] at e
  have hh : h ∈ (⊤ : Subgroup 𝒪[L]ˣ).map (normIntegerUnits K L) := by
    rw [e]
    exact Subgroup.mem_top h
  obtain ⟨g, -, rfl⟩ := hh
  exact ⟨g, rfl⟩

theorem map_normUnits_unitFiltrationUnits (n : ℕ) :
    (unitFiltrationUnits L n).map (normUnits K L) = unitFiltrationUnits K n := by
  have h : (normUnits K L).comp (unitsIncl L) = (unitsIncl K).comp (normIntegerUnits K L) := by
    ext u
    simp [normUnits_unitsIncl]
  rw [unitFiltrationUnits, unitFiltrationUnits, Subgroup.map_map, h, ← Subgroup.map_map,
    map_normIntegerUnits_unitFiltration]

theorem unitFiltrationUnits_zero_le_range_normUnits :
    unitFiltrationUnits K 0 ≤ (normUnits K L).range := by
  rw [← map_normUnits_unitFiltrationUnits (L := L) 0]
  exact Subgroup.map_le_range _ _

end Residue

section NormGroup

variable (K L) in

def ordModFinrank : Kˣ →* Multiplicative (ZMod (Module.finrank K L)) where
  toFun x := Multiplicative.ofAdd ((ord (x : K) : ℤ) : ZMod (Module.finrank K L))
  map_one' := by simp [ord]
  map_mul' x y := by
    rw [Units.val_mul, ord_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
theorem ordModFinrank_apply (x : Kˣ) :
    ordModFinrank K L x = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ZMod (Module.finrank K L)) :=
  rfl

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L] in
theorem ordModFinrank_surjective : Function.Surjective (ordModFinrank K L) := by
  intro z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
  refine ⟨uniformizerUnit hϖ ^ k, ?_⟩
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  rw [ordModFinrank_apply, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, ord_zpow hϖ0,
    ord_uniformizer hϖ, mul_one, hk]
  rfl

variable [IsUnramified K L]

theorem mem_range_normUnits_iff (x : Kˣ) :
    x ∈ (normUnits K L).range ↔ (Module.finrank K L : ℤ) ∣ ord (x : K) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [coe_normUnits, ord_norm, IsUnramified.residueDegree_eq_finrank K L]
    exact dvd_mul_right _ _
  · rintro ⟨k, hk⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    obtain ⟨⟨m, u⟩, hx⟩ := (unitsOfIntProd_bijective hϖ).2 x
    have hm : m.toAdd = Module.finrank K L * k := by
      rw [← hk, ← hx, ord_unitsOfIntProd]
    obtain ⟨v, hv⟩ := normIntegerUnits_surjective (K := K) (L := L) u
    refine ⟨Units.map (algebraMap K L : K →* L) (uniformizerUnit hϖ) ^ k * unitsIncl L v, ?_⟩
    rw [← hx, unitsOfIntProd_eq, map_mul, map_zpow, normUnits_unitsIncl, hv, hm, zpow_mul]
    congr 2
    ext
    simp [Algebra.norm_algebraMap]

theorem ker_ordModFinrank : (ordModFinrank K L).ker = (normUnits K L).range := by
  ext x
  rw [MonoidHom.mem_ker, mem_range_normUnits_iff, ordModFinrank_apply, ofAdd_eq_one,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

variable (K L) in

def quotientRangeNormUnitsEquiv :
    Kˣ ⧸ (normUnits K L).range ≃* Multiplicative (ZMod (Module.finrank K L)) :=
  (QuotientGroup.quotientMulEquivOfEq ker_ordModFinrank.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ordModFinrank_surjective)

theorem quotientRangeNormUnitsEquiv_mk (x : Kˣ) :
    quotientRangeNormUnitsEquiv K L (QuotientGroup.mk x) = ordModFinrank K L x :=
  rfl

theorem index_range_normUnits : (normUnits K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, Nat.card_congr (quotientRangeNormUnitsEquiv K L).toEquiv]
  exact Nat.card_zmod _

theorem zpowers_mk_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Subgroup.zpowers (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  induction q using QuotientGroup.induction_on with
  | H x =>
    refine ⟨ord (x : K), ?_⟩
    have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
    simp only
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_range_normUnits_iff, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, coe_uniformizerUnit,
      ord_mul (inv_ne_zero (zpow_ne_zero _ hϖ0)) x.ne_zero, ← zpow_neg, ord_zpow hϖ0,
      ord_uniformizer hϖ]
    simp

theorem orderOf_mk_uniformizerUnit {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    orderOf (QuotientGroup.mk (uniformizerUnit hϖ) : Kˣ ⧸ (normUnits K L).range) =
      Module.finrank K L := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (fun q ↦ by
    rw [zpowers_mk_uniformizerUnit hϖ]; exact Subgroup.mem_top q)]
  exact index_range_normUnits

theorem isCyclic_quotient_range_normUnits : IsCyclic (Kˣ ⧸ (normUnits K L).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, zpowers_mk_uniformizerUnit hϖ⟩

end NormGroup

end Sec_UnramifiedNormSurj


/-! ### UnramifiedNorms -/
section Sec_UnramifiedNorms

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem coe_tateNorm_integerUnits [IsGalois K L] (u : 𝒪[L]ˣ) :
    (((tateNorm (L ≃ₐ[K] L) 𝒪[L]ˣ u : 𝒪[L]ˣ) : 𝒪[L]) : L) =
      algebraMap K L (Algebra.norm K ((u : 𝒪[L]) : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, tateNorm_apply, Units.coe_prod]
  push_cast
  rfl

theorem exists_eq_of_forall_smul_eq [IsGalois K L] {x : 𝒪[L]ˣ}
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) :
    ∃ w : 𝒪[K]ˣ, algebraMap K L ((w : 𝒪[K]) : K) = ((x : 𝒪[L]) : L) := by
  have hfix : ((x : 𝒪[L]) : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed _).2 fun σ ↦ by
      have := congrArg (fun u : 𝒪[L]ˣ ↦ ((u : 𝒪[L]) : L)) (hx σ)
      simpa using this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (Units.ne_zero x) (by exact_mod_cast hc.symm)
  have h1 : c ∈ 𝒪[K] := (algebraMap_mem_integer_iff K L c).1 (hc ▸ (x : 𝒪[L]).2)
  have h2 : c⁻¹ ∈ 𝒪[K] := by
    refine (algebraMap_mem_integer_iff K L c⁻¹).1 ?_
    have e : algebraMap K L c⁻¹ = (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
      rw [map_inv₀, hc, eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (Units.ne_zero x))]
      exact_mod_cast congrArg (fun u : 𝒪[L] ↦ (u : L)) x.inv_mul
    rw [e]
    exact (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L])).2
  refine ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, ?_, ?_⟩, hc⟩
  · ext
    simp [hc0]
  · ext
    simp [hc0]

theorem subsingleton_tateZero_integerUnits [IsGalois K L] [IsUnramified K L] :
    Subsingleton (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  obtain ⟨w, hw⟩ := exists_eq_of_forall_smul_eq hx
  obtain ⟨v, rfl⟩ := normIntegerUnits_surjective (K := K) (L := L) w
  refine ⟨v, Units.ext (Subtype.ext ?_)⟩
  rw [coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]

theorem subsingleton_tateNegOne_integerUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramified K L] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hxL : tateNorm (L ≃ₐ[K] L) Lˣ (unitsIncl L x) = 1 := by
    rw [tateNorm_apply]
    simp_rw [← unitsIncl_smul]
    rw [← map_prod, ← tateNorm_apply, hx, map_one]
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hg hxL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨⟨m, v⟩, rfl⟩ := (unitsOfIntProd_bijective hϖL).2 y
  have hπ : g • uniformizerUnit hϖL = uniformizerUnit hϖL := by
    ext
    change g ((uniformizerUnit hϖL : Lˣ) : L) = _
    rw [coe_uniformizerUnit, coe_algebraMap_integer, AlgEquiv.commutes]
  have hx' : x = g • v / v := by
    apply unitsIncl_injective (K := L)
    rw [← hy, unitsOfIntProd_eq, _root_.map_div, unitsIncl_smul, smul_mul', smul_zpow', hπ,
      mul_div_mul_left_eq_div]
  rw [hx']
  exact Subgroup.subset_closure ⟨g, v, rfl⟩

end Sec_UnramifiedNorms


/-! ### MaximalUnramified -/
section Sec_MaximalUnramified

open ValuativeRel _root_.IntermediateField RHDirect.CFT_AbstractLocalReciprocity RHDirect.CFT_AbstractLocalReciprocity.ProfiniteInteger

section Roots

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem algEquiv_pow_apply_of_apply_eq_pow {L : Type*} [Field L] [Algebra K L] {τ : L ≃ₐ[K] L}
    {x : L} {q : ℕ} (h : τ x = x ^ q) (k : ℕ) : (τ ^ k) x = x ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, ← pow_succ']

theorem one_lt_card_residueField_pow {n : ℕ} (hn : n ≠ 0) : 1 < Nat.card 𝓀[K] ^ n :=
  Nat.one_lt_pow hn (one_lt_card_residueField K)

theorem exists_frobenius_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    ∃ τ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯, τ (AdjoinSimple.gen K ζ) = AdjoinSimple.gen K ζ ^ Nat.card 𝓀[K] ∧
      orderOf τ = n ∧ Subgroup.zpowers τ = ⊤ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  have h := hE.ramificationIndex_eq_one
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  refine ⟨frobenius K K⟮ζ⟯ h, frobenius_apply_of_pow_eq_one h
    (natCast_card_pow_sub_one_ne_zero hn) hζ'.pow_eq_one, ?_, zpowers_frobenius K _ h⟩
  rw [orderOf_frobenius, hEn]

theorem exists_apply_eq_pow_pow {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (σ : Ω ≃ₐ[K] Ω) :
    ∃ a : ℕ, σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  have := hE.isGalois
  obtain ⟨τ, hτ, -, htop⟩ := exists_frobenius_adjoin hn hζ
  have hmem : σ.restrictNormal K⟮ζ⟯ ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := mem_powers_iff_mem_zpowers.2 hmem
  refine ⟨a, ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ K⟮ζ⟯ (AdjoinSimple.gen K ζ)
  rw [← ha, algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  simpa using h1.symm

theorem pow_pow_eq_pow_pow_iff {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (a b : ℕ) :
    ζ ^ Nat.card 𝓀[K] ^ a = ζ ^ Nat.card 𝓀[K] ^ b ↔ a ≡ b [MOD n] := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  obtain ⟨τ, hτ, hord, -⟩ := exists_frobenius_adjoin hn hζ
  rw [← hord, ← pow_eq_pow_iff_modEq]
  constructor
  · intro h
    have h' : (τ ^ a) (AdjoinSimple.gen K ζ) = (τ ^ b) (AdjoinSimple.gen K ζ) := by
      rw [algEquiv_pow_apply_of_apply_eq_pow hτ, algEquiv_pow_apply_of_apply_eq_pow hτ]
      exact Subtype.ext (by simpa using h)
    have h1 : (τ ^ b)⁻¹ * τ ^ a = 1 := by
      refine algEquiv_eq_one_of_apply_eq (adjoin_gen_eq_top ζ) ?_
      rw [AlgEquiv.mul_apply, h', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact (inv_mul_eq_one.mp h1).symm
  · intro h
    have := congrArg (fun ρ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯ ↦ ((ρ (AdjoinSimple.gen K ζ) : K⟮ζ⟯) : Ω)) h
    simpa [algEquiv_pow_apply_of_apply_eq_pow hτ] using this

theorem apply_eq_pow_pow_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) {σ : Ω ≃ₐ[K] Ω} {a : ℕ}
    (ha : σ ζ = ζ ^ Nat.card 𝓀[K] ^ a) {ξ : Ω} (hξ : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1) :
    σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]

variable (K Ω) in

class HasUnramifiedRoots : Prop where
  exists_isPrimitiveRoot : ∀ n : ℕ, n ≠ 0 → ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)

instance hasUnramifiedRoots_of_isSepClosed [IsSepClosed Ω] : HasUnramifiedRoots K Ω :=
  ⟨fun _ hn ↦ exists_isPrimitiveRoot_card_pow_sub_one (K := K) hn⟩

variable (K Ω) in

def unramifiedRoots : Set Ω :=
  {ξ | ∃ n : ℕ, n ≠ 0 ∧ ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1}

omit [Algebra K Ω] in

theorem mem_unramifiedRoots_iff {ξ : Ω} :
    ξ ∈ unramifiedRoots K Ω ↔ ∃ m : ℕ, (m : 𝓀[K]) ≠ 0 ∧ ξ ^ m = 1 := by
  constructor
  · rintro ⟨n, hn, hξ⟩
    exact ⟨_, natCast_card_pow_sub_one_ne_zero hn, hξ⟩
  · rintro ⟨m, hm, hξ⟩
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have := Fintype.ofFinite 𝓀[K]
    obtain ⟨p, hp⟩ := CharP.exists 𝓀[K]
    obtain ⟨k, hprime, hcard⟩ := FiniteField.card 𝓀[K] p
    have hpm : ¬ p ∣ m := fun h ↦ hm ((CharP.cast_eq_zero_iff 𝓀[K] p m).2 h)
    have hcop : Nat.Coprime (Nat.card 𝓀[K]) m := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hprime).2 hpm)
    have hdvd : m ∣ Nat.card 𝓀[K] ^ m.totient - 1 :=
      (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ Nat.card_pos)).1 (Nat.ModEq.pow_totient hcop).symm
    refine ⟨m.totient, (Nat.totient_pos.2 (Nat.pos_of_ne_zero hm0)).ne', ?_⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ, one_pow]

variable (K) in
open Classical in

def unramifiedCoord (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) : ZMod n :=
  if h : ∃ a : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ a.val then h.choose else 0

theorem natCast_eq_unramifiedCoord_iff {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔ σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  obtain ⟨a₀, ha₀⟩ := exists_apply_eq_pow_pow hn hζ σ
  have hex : ∃ c : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ c.val := by
    refine ⟨a₀, fun ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one hn hζ ?_ hξ⟩
    rw [ha₀, pow_pow_eq_pow_pow_iff hn hζ, ZMod.val_natCast]
    exact (Nat.mod_modEq a₀ n).symm
  have hc : unramifiedCoord K σ n = hex.choose := dif_pos hex
  rw [hc, hex.choose_spec ζ hζ.pow_eq_one, pow_pow_eq_pow_pow_iff hn hζ,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact eq_comm

theorem apply_eq_pow_pow_unramifiedCoord {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) :
    σ ζ = ζ ^ Nat.card 𝓀[K] ^ (unramifiedCoord K σ n).val :=
  (natCast_eq_unramifiedCoord_iff hζ σ _).1 (ZMod.natCast_zmod_val _)

variable [HasUnramifiedRoots K Ω]

theorem natCast_eq_unramifiedCoord_iff_forall (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔
      ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 → σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  rw [natCast_eq_unramifiedCoord_iff hζ]
  exact ⟨fun h ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ h hξ, fun h ↦ h ζ hζ.pow_eq_one⟩

theorem unramifiedCoord_one (n : ℕ+) : unramifiedCoord K (1 : Ω ≃ₐ[K] Ω) n = 0 := by
  rw [← (natCast_eq_unramifiedCoord_iff_forall 1 n 0).2 (fun ξ _ ↦ by simp), Nat.cast_zero]

theorem unramifiedCoord_mul (σ τ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n + unramifiedCoord K τ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have h := (natCast_eq_unramifiedCoord_iff hζ (σ * τ)
    ((unramifiedCoord K σ n).val + (unramifiedCoord K τ n).val)).2 (by
      rw [AlgEquiv.mul_apply, apply_eq_pow_pow_unramifiedCoord hζ τ, map_pow,
        apply_eq_pow_pow_unramifiedCoord hζ σ, ← pow_mul, ← pow_add])
  rw [← h, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem castHom_unramifiedCoord (σ : Ω ≃ₐ[K] Ω) {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    ZMod.castHom h (ZMod m) (unramifiedCoord K σ n) = unramifiedCoord K σ m := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) m m.ne_zero
  have hdvd : Nat.card 𝓀[K] ^ (m : ℕ) - 1 ∣ Nat.card 𝓀[K] ^ (n : ℕ) - 1 := by
    obtain ⟨k, hk⟩ := h
    rw [hk, pow_mul]
    simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card 𝓀[K] ^ (m : ℕ)) 1 k
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have key := apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ
    (apply_eq_pow_pow_unramifiedCoord hζ σ) hξn
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (natCast_eq_unramifiedCoord_iff hξ σ _).2 key

end Roots

section Degree

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω]

variable (K Ω) in

def unramifiedDegree : (Ω ≃ₐ[K] Ω) →* Multiplicative ℤ̂ where
  toFun σ := Multiplicative.ofAdd ⟨fun n ↦ unramifiedCoord K σ n,
    mem_profiniteIntegers.2 fun _ _ h ↦ castHom_unramifiedCoord σ h⟩
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    ext n
    show unramifiedCoord K 1 n = proj n 0
    rw [map_zero, unramifiedCoord_one]
  map_mul' σ τ := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
    congr 1
    ext n
    show unramifiedCoord K (σ * τ) n = proj n (_ + _)
    rw [map_add, unramifiedCoord_mul]
    rfl

theorem proj_toAdd_unramifiedDegree (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    proj n (Multiplicative.toAdd (unramifiedDegree K Ω σ)) = unramifiedCoord K σ n :=
  rfl

theorem multiplicative_ext {x y : Multiplicative ℤ̂}
    (h : ∀ n, proj n (Multiplicative.toAdd x) = proj n (Multiplicative.toAdd y)) : x = y :=
  Multiplicative.toAdd.injective (ProfiniteInteger.ext h)

theorem unramifiedCoord_mul_of_apply_eq (σ : Ω ≃ₐ[K] Ω) {τ : Ω ≃ₐ[K] Ω} {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (hτ : τ ζ = ζ) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n := by
  have h0 : unramifiedCoord K τ n = 0 := by
    rw [← (natCast_eq_unramifiedCoord_iff hζ τ 0).2 (by simpa using hτ), Nat.cast_zero]
  rw [unramifiedCoord_mul, h0, add_zero]

theorem continuous_unramifiedCoord (n : ℕ+) :
    Continuous fun σ : Ω ≃ₐ[K] Ω ↦ unramifiedCoord K σ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hfin : FiniteDimensional K K⟮ζ⟯ := (isUnramifiedSubextension_adjoin n.ne_zero hζ).1.1
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun σ ↦ ?_).continuous
  open scoped Pointwise in
  have hU : σ • (K⟮ζ⟯.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) ∈ nhds σ :=
    (K⟮ζ⟯.fixingSubgroup_isOpen.smul σ).mem_nhds ⟨1, one_mem _, by simp⟩
  filter_upwards [hU] with ρ hρ
  obtain ⟨τ, hτ, rfl⟩ := hρ
  exact unramifiedCoord_mul_of_apply_eq σ hζ
    ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (mem_adjoin_simple_self K ζ))

theorem continuous_unramifiedDegree : Continuous (unramifiedDegree K Ω) :=
  continuous_ofAdd.comp (Continuous.subtype_mk (continuous_pi fun n ↦ continuous_unramifiedCoord n) _)

theorem exists_unramifiedCoord_eq [Normal K Ω] (n : ℕ+) (c : ZMod n) :
    ∃ σ : Ω ≃ₐ[K] Ω, unramifiedCoord K σ n = c := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin n.ne_zero hζ
  have := hE.1
  obtain ⟨τ, hτ, -, -⟩ := exists_frobenius_adjoin n.ne_zero hζ
  refine ⟨(τ ^ c.val).liftNormal Ω, ?_⟩
  have h1 := AlgEquiv.liftNormal_commutes (τ ^ c.val) Ω (AdjoinSimple.gen K ζ)
  rw [algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  have h2 := (natCast_eq_unramifiedCoord_iff hζ ((τ ^ c.val).liftNormal Ω) c.val).2
    (by simpa using h1)
  rw [← h2, ZMod.natCast_zmod_val]

theorem unramifiedDegree_surjective [IsGalois K Ω] : Function.Surjective (unramifiedDegree K Ω) := by
  intro x
  let N : ℕ → ℕ+ := fun k ↦ ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  let S : ℕ → Set (Ω ≃ₐ[K] Ω) := fun k ↦
    {σ | unramifiedCoord K σ (N k) = proj (N k) (Multiplicative.toAdd x)}
  have hS : ∀ k, IsClosed (S k) := fun k ↦
    isClosed_eq (continuous_unramifiedCoord _) continuous_const
  have hdvd : ∀ k, (N k : ℕ) ∣ N (k + 1) := fun k ↦ Nat.factorial_dvd_factorial (by omega)
  have hmono : ∀ k, S (k + 1) ⊆ S k := by
    intro k σ hσ
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← castHom_unramifiedCoord σ (hdvd k), hσ, castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k ↦ exists_unramifiedCoord_eq _ _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hS 0).isCompact hS
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, multiplicative_ext fun n ↦ ?_⟩
  have hn : (n : ℕ) ∣ N ((n : ℕ) - 1) := by
    show (n : ℕ) ∣ ((n : ℕ) - 1 + 1).factorial
    rw [Nat.sub_add_cancel n.pos]
    exact Nat.dvd_factorial n.pos le_rfl
  rw [proj_toAdd_unramifiedDegree, ← castHom_unramifiedCoord σ hn, hσ _, castHom_proj]

theorem unramifiedDegree_eq_ofAdd_natCast_iff (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd (a : ℤ̂) ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  constructor
  · rintro h ξ ⟨n, hn, hξ⟩
    have hc : unramifiedCoord K σ ⟨n, Nat.pos_of_ne_zero hn⟩ = a := by
      have := congrArg (fun y ↦ proj ⟨n, Nat.pos_of_ne_zero hn⟩ (Multiplicative.toAdd y)) h
      refine this.trans ?_
      rw [toAdd_ofAdd, map_natCast]
    exact (natCast_eq_unramifiedCoord_iff_forall σ ⟨n, Nat.pos_of_ne_zero hn⟩ a).1 hc.symm ξ hξ
  · intro h
    refine multiplicative_ext fun n ↦ ?_
    rw [proj_toAdd_unramifiedDegree, toAdd_ofAdd, map_natCast]
    exact ((natCast_eq_unramifiedCoord_iff_forall σ n a).2
      fun ξ hξ ↦ h ξ ⟨n, n.ne_zero, hξ⟩).symm

theorem unramifiedDegree_eq_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = 1 ↔ ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 0
  simp only [Nat.cast_zero, ofAdd_zero, pow_zero, pow_one] at this
  exact this

theorem unramifiedDegree_eq_ofAdd_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 1
  simp only [Nat.cast_one, pow_one] at this
  exact this

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω] in

theorem mem_fixingSubgroup_adjoin_iff {S : Set Ω} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ (adjoin K S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [← Subgroup.zpowers_le, ← le_iff_le, adjoin_le_iff]
  refine ⟨fun h x hx ↦ (mem_fixedField_iff _ _).1 (h hx) σ (Subgroup.mem_zpowers σ), fun h x hx ↦ ?_⟩
  refine (mem_fixedField_iff _ _).2 fun τ hτ ↦ ?_
  have hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := h x hx
  exact (Subgroup.zpowers_le.2 hσ) hτ

end Degree

section MaximalUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem pow_sub_one_dvd_pow_sub_one (q : ℕ) {m n : ℕ} (h : m ∣ n) : q ^ m - 1 ∣ q ^ n - 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul]
  simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (q ^ m) 1 k

variable (K Ω) in

def maximalUnramifiedExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, E.1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem IsUnramifiedSubextension.le_maximalUnramifiedExtension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : E ≤ maximalUnramifiedExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) ⟨E, hE⟩

theorem adjoin_le_maximalUnramifiedExtension {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : K⟮ζ⟯ ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_adjoin hn hζ).1.le_maximalUnramifiedExtension

instance normal_maximalUnramifiedExtension : Normal K (maximalUnramifiedExtension K Ω) := by
  have : ∀ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, Normal K E.1 :=
    fun E ↦ E.2.isGalois.to_normal
  unfold maximalUnramifiedExtension
  infer_instance

instance isGalois_maximalUnramifiedExtension [Algebra.IsSeparable K Ω] :
    IsGalois K (maximalUnramifiedExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (maximalUnramifiedExtension K Ω) Ω
  isGalois_iff.2 ⟨this, inferInstance⟩

variable [HasUnramifiedRoots K Ω]

theorem IsUnramifiedSubextension.le_adjoin {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {n : ℕ} (hn : n ≠ 0) (hdvd : Module.finrank K E ∣ n) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : E ≤ K⟮ζ⟯ := by
  have := hE.1
  have hm : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hm
  rw [hE.eq_adjoin rfl hm hξ, adjoin_simple_le_iff]
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξn
  exact pow_mem (mem_adjoin_simple_self K ζ) i

theorem directed_isUnramifiedSubextension :
    Directed (· ≤ ·) (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) := by
  rintro ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
  have := h₁.1
  have := h₂.1
  have hn : Module.finrank K E₁ * Module.finrank K E₂ ≠ 0 :=
    mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
  exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin hn hζ).1⟩,
    h₁.le_adjoin hn (dvd_mul_right _ _) hζ, h₂.le_adjoin hn (dvd_mul_left _ _) hζ⟩

theorem coe_maximalUnramifiedExtension : (maximalUnramifiedExtension K Ω : Set Ω) =
    ⋃ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, (E.1 : Set Ω) := by
  have : Nonempty {E : IntermediateField K Ω // IsUnramifiedSubextension E} := by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) 1 one_ne_zero
    exact ⟨⟨K⟮ζ⟯, (isUnramifiedSubextension_adjoin one_ne_zero hζ).1⟩⟩
  exact coe_iSup_of_directed directed_isUnramifiedSubextension

theorem mem_maximalUnramifiedExtension_iff {x : Ω} :
    x ∈ maximalUnramifiedExtension K Ω ↔ ∃ E : IntermediateField K Ω, IsUnramifiedSubextension E ∧ x ∈ E := by
  rw [← SetLike.mem_coe, coe_maximalUnramifiedExtension, Set.mem_iUnion]
  exact ⟨fun ⟨E, h⟩ ↦ ⟨E.1, E.2, h⟩, fun ⟨E, hE, h⟩ ↦ ⟨⟨E, hE⟩, h⟩⟩

theorem maximalUnramifiedExtension_eq_adjoin :
    maximalUnramifiedExtension K Ω = adjoin K (unramifiedRoots K Ω) := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    have := E.2.1
    have hn : Module.finrank K E.1 ≠ 0 := Module.finrank_pos.ne'
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
    rw [E.2.eq_adjoin rfl hn hζ, adjoin_simple_le_iff]
    exact subset_adjoin K _ ⟨_, hn, hζ.pow_eq_one⟩
  · rw [adjoin_le_iff]
    rintro ξ ⟨n, hn, hξ⟩
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
      ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact adjoin_le_maximalUnramifiedExtension hn hζ (pow_mem (mem_adjoin_simple_self K ζ) i)

theorem unramifiedRoots_subset_maximalUnramifiedExtension :
    unramifiedRoots K Ω ⊆ maximalUnramifiedExtension K Ω := by
  rw [maximalUnramifiedExtension_eq_adjoin]
  exact subset_adjoin K _

instance hasUnramifiedRoots_maximalUnramifiedExtension : HasUnramifiedRoots K (maximalUnramifiedExtension K Ω) :=
  ⟨fun n hn ↦ by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    exact ⟨⟨ζ, unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, hn, hζ.pow_eq_one⟩⟩,
      hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective⟩⟩

theorem ker_unramifiedDegree :
    (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, unramifiedDegree_eq_one_iff, maximalUnramifiedExtension_eq_adjoin,
    mem_fixingSubgroup_adjoin_iff]

theorem unramifiedDegree_restrictNormal (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (σ.restrictNormal (maximalUnramifiedExtension K Ω)) =
      unramifiedDegree K Ω σ := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, proj_toAdd_unramifiedDegree]
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hζE : ζ ∈ maximalUnramifiedExtension K Ω :=
    unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, n.ne_zero, hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : maximalUnramifiedExtension K Ω) (Nat.card 𝓀[K] ^ (n : ℕ) - 1) :=
    hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective
  rw [← (natCast_eq_unramifiedCoord_iff hζ' _ (unramifiedCoord K σ n).val).2 ?_,
    ZMod.natCast_zmod_val]
  apply Subtype.ext
  have h1 := AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω) ⟨ζ, hζE⟩
  simp only [IntermediateField.algebraMap_apply] at h1
  rw [h1]
  simpa using apply_eq_pow_pow_unramifiedCoord hζ σ

variable [IsGalois K Ω]

theorem unramifiedDegree_maximalUnramifiedExtension_surjective :
    Function.Surjective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  intro x
  obtain ⟨σ, rfl⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) x
  exact ⟨_, unramifiedDegree_restrictNormal σ⟩

theorem unramifiedDegree_maximalUnramifiedExtension_injective :
    Function.Injective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  rw [injective_iff_map_eq_one]
  intro ρ hρ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) ρ
  have hσ : σ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, ← unramifiedDegree_restrictNormal]
    exact hρ
  rw [ker_unramifiedDegree, ← IntermediateField.restrictNormalHom_ker] at hσ
  exact MonoidHom.mem_ker.1 hσ

variable (K Ω) in

def maximalUnramifiedExtensionGaloisEquiv :
    (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃ₜ* Multiplicative ℤ̂ :=
  let e : (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃* Multiplicative ℤ̂ :=
    MulEquiv.ofBijective (unramifiedDegree K (maximalUnramifiedExtension K Ω))
      ⟨unramifiedDegree_maximalUnramifiedExtension_injective, unramifiedDegree_maximalUnramifiedExtension_surjective⟩
  { e with
    continuous_toFun := continuous_unramifiedDegree
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) continuous_unramifiedDegree).symm.continuous }

@[simp]
theorem maximalUnramifiedExtensionGaloisEquiv_apply (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    maximalUnramifiedExtensionGaloisEquiv K Ω ρ = unramifiedDegree K (maximalUnramifiedExtension K Ω) ρ :=
  rfl

variable (K Ω) in

def maximalUnramifiedExtensionFrobenius : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).symm (Multiplicative.ofAdd 1)

theorem unramifiedDegree_maximalUnramifiedExtensionFrobenius :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (maximalUnramifiedExtensionFrobenius K Ω) =
      Multiplicative.ofAdd 1 :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).apply_symm_apply _

theorem eq_maximalUnramifiedExtensionFrobenius_iff (ρ : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :
    ρ = maximalUnramifiedExtensionFrobenius K Ω ↔
      ∀ ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω), ρ ξ = ξ ^ Nat.card 𝓀[K] := by
  rw [← unramifiedDegree_eq_ofAdd_one_iff,
    ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

theorem maximalUnramifiedExtensionFrobenius_apply {ξ : maximalUnramifiedExtension K Ω}
    (hξ : ξ ∈ unramifiedRoots K (maximalUnramifiedExtension K Ω)) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] :=
  (eq_maximalUnramifiedExtensionFrobenius_iff _).1 rfl ξ hξ

theorem maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one {ξ : maximalUnramifiedExtension K Ω} {m : ℕ}
    (hm : (m : 𝓀[K]) ≠ 0) (hξ : ξ ^ m = 1) :
    maximalUnramifiedExtensionFrobenius K Ω ξ = ξ ^ Nat.card 𝓀[K] :=
  maximalUnramifiedExtensionFrobenius_apply (mem_unramifiedRoots_iff.2 ⟨m, hm, hξ⟩)

theorem restrictNormal_eq_maximalUnramifiedExtensionFrobenius_iff (σ : Ω ≃ₐ[K] Ω) :
    σ.restrictNormal (maximalUnramifiedExtension K Ω) = maximalUnramifiedExtensionFrobenius K Ω ↔
      unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 := by
  rw [← unramifiedDegree_restrictNormal, ← unramifiedDegree_maximalUnramifiedExtensionFrobenius (K := K) (Ω := Ω)]
  exact unramifiedDegree_maximalUnramifiedExtension_injective.eq_iff.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω] in

theorem dense_zpowers_ofAdd_one :
    Dense (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
  have h : (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) =
      Multiplicative.ofAdd '' Set.range (Int.cast : ℤ → ℤ̂) := by
    ext y
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, ⟨k, rfl⟩, by rw [← ofAdd_zsmul, zsmul_one]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [← ofAdd_zsmul, zsmul_one]⟩
  rw [h]
  exact Multiplicative.ofAdd.surjective.denseRange.dense_image continuous_ofAdd denseRange_intCast

theorem dense_zpowers_maximalUnramifiedExtensionFrobenius :
    Dense (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) := by
  have h : (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω) :
      Set (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω)) =
      (maximalUnramifiedExtensionGaloisEquiv K Ω).symm ''
        (Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ̂)) : Set (Multiplicative ℤ̂)) := by
    ext ρ
    simp only [SetLike.mem_coe, Subgroup.mem_zpowers_iff, Set.mem_image]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, by rw [map_zpow]; rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, by rw [map_zpow]; rfl⟩
  rw [h]
  exact (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.surjective.denseRange.dense_image
    (maximalUnramifiedExtensionGaloisEquiv K Ω).symm.continuous dense_zpowers_ofAdd_one

theorem topologicalClosure_zpowers_maximalUnramifiedExtensionFrobenius :
    (Subgroup.zpowers (maximalUnramifiedExtensionFrobenius K Ω)).topologicalClosure = ⊤ :=
  SetLike.coe_injective (by
    rw [Subgroup.topologicalClosure_coe, dense_zpowers_maximalUnramifiedExtensionFrobenius.closure_eq,
      Subgroup.coe_top])

end MaximalUnramified

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

instance hasUnramifiedRoots_of_isSepClosure [IsSepClosure K Ω] : HasUnramifiedRoots K Ω :=
  have := IsSepClosure.sep_closed K (K := Ω)
  inferInstance

theorem unramifiedDegree_spec [IsSepClosure K Ω] :
    Continuous (unramifiedDegree K Ω) ∧ Function.Surjective (unramifiedDegree K Ω) ∧
      (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup :=
  ⟨continuous_unramifiedDegree, unramifiedDegree_surjective, ker_unramifiedDegree⟩

end SeparableClosure

section Finite

section Card

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]

theorem card_residueField_eq_pow_residueDegree :
    Nat.card 𝓀[M] = Nat.card 𝓀[K] ^ residueDegree K M := by
  have := Fintype.ofFinite 𝓀[K]
  have := Fintype.ofFinite 𝓀[M]
  rw [residueDegree_eq_finrank, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[M])]

end Card

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

theorem unramifiedCoord_fixingSubgroup (σ : L.fixingSubgroup) (n : ℕ+) :
    unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n =
      (residueDegree K L : ZMod n) * unramifiedCoord L (fixingSubgroupEquiv L σ) n := by
  have hQ := card_residueField_eq_pow_residueDegree K L
  have key : ((residueDegree K L * (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val : ℕ) :
      ZMod n) = unramifiedCoord K (σ : Ω ≃ₐ[K] Ω) n := by
    rw [natCast_eq_unramifiedCoord_iff_forall]
    intro ξ hξ
    have hξ' : ξ ^ (Nat.card 𝓀[L] ^ (n : ℕ) - 1) = 1 := by
      rw [hQ, ← pow_mul]
      obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K])
        (dvd_mul_left (n : ℕ) (residueDegree K L))
      rw [hc, pow_mul, hξ, one_pow]
    have h := (natCast_eq_unramifiedCoord_iff_forall (K := L) (fixingSubgroupEquiv L σ) n
      (unramifiedCoord L (fixingSubgroupEquiv L σ) n).val).1 (ZMod.natCast_zmod_val _) ξ hξ'
    rw [hQ, ← pow_mul] at h
    exact h
  rw [← key, Nat.cast_mul, ZMod.natCast_zmod_val]

theorem unramifiedDegree_fixingSubgroup (σ : L.fixingSubgroup) :
    unramifiedDegree K Ω σ = unramifiedDegree L Ω (fixingSubgroupEquiv L σ) ^ residueDegree K L := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, toAdd_pow, map_nsmul, proj_toAdd_unramifiedDegree, nsmul_eq_mul,
    unramifiedCoord_fixingSubgroup]

variable [IsGalois K Ω]

theorem map_unramifiedDegree_fixingSubgroup :
    L.fixingSubgroup.map (unramifiedDegree K Ω) =
      (powMonoidHom (residueDegree K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
  have := IsGalois.tower_top_of_isGalois K L Ω
  ext x
  simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (unramifiedDegree_fixingSubgroup L ⟨σ, hσ⟩).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨τ, rfl⟩ := unramifiedDegree_surjective (K := L) (Ω := Ω) y
    obtain ⟨σ, rfl⟩ := (fixingSubgroupEquiv L).surjective τ
    exact ⟨σ, σ.2, (unramifiedDegree_fixingSubgroup L σ)⟩

theorem inertiaDegree_unramifiedDegree_fixingSubgroup :
    inertiaDegree (unramifiedDegree K Ω) L.fixingSubgroup = residueDegree K L := by
  rw [inertiaDegree, map_unramifiedDegree_fixingSubgroup,
    ProfiniteInteger.index_range_powMonoidHom (residueDegree_pos K L).ne']

end Finite

end Sec_MaximalUnramified


/-! ### MaximalUnramifiedIntegers -/
section Sec_MaximalUnramifiedIntegers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000



open ValuativeRel IsLocalRing

section Ambient

variable {K Ω : Type*} [Field K] [Field Ω] [ValuativeRel Ω] [Algebra K Ω]

theorem valuation_le_valuation_iff_coe (E : IntermediateField K Ω) (x y : E) :
    valuation E x ≤ valuation E y ↔ valuation Ω (x : Ω) ≤ valuation Ω (y : Ω) := by
  rw [← Valuation.vle_iff_le, ← Valuation.vle_iff_le, IntermediateField.coe_vle_coe_iff]

theorem valuation_eq_valuation_iff_coe (E : IntermediateField K Ω) (x y : E) :
    valuation E x = valuation E y ↔ valuation Ω (x : Ω) = valuation Ω (y : Ω) := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff_coe,
    valuation_le_valuation_iff_coe]

theorem mem_integer_intermediateField_iff (E : IntermediateField K Ω) (x : E) :
    x ∈ 𝒪[E] ↔ valuation Ω (x : Ω) ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation E), valuation_le_valuation_iff_coe]
  simp

theorem isUnit_integer_intermediateField_iff (E : IntermediateField K Ω) (x : 𝒪[E]) :
    IsUnit x ↔ valuation Ω ((x : E) : Ω) = 1 := by
  rw [(Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one, ← map_one (valuation E)]
  exact (valuation_eq_valuation_iff_coe E _ _).trans (by simp; rfl)

theorem mem_maximalIdeal_intermediateField_iff (E : IntermediateField K Ω) (x : 𝒪[E]) :
    x ∈ 𝓂[E] ↔ valuation Ω ((x : E) : Ω) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_intermediateField_iff]
  have : valuation Ω ((x : E) : Ω) ≤ 1 := (mem_integer_intermediateField_iff E x).mp x.2
  exact ⟨fun h ↦ lt_of_le_of_ne this h, fun h ↦ h.ne⟩

theorem dvd_integer_intermediateField_iff (E : IntermediateField K Ω) (x y : 𝒪[E]) :
    x ∣ y ↔ valuation Ω ((y : E) : Ω) ≤ valuation Ω ((x : E) : Ω) := by
  rw [(Valuation.integer.integers (valuation E)).dvd_iff_le]
  exact valuation_le_valuation_iff_coe E _ _

def integerInclusion [ValuativeRel K] [ValuativeExtension K Ω] {E F : IntermediateField K Ω}
    (h : E ≤ F) : 𝒪[E] →ₐ[𝒪[K]] 𝒪[F] where
  toFun x := ⟨IntermediateField.inclusion h x, by
    rw [mem_integer_intermediateField_iff]
    exact (mem_integer_intermediateField_iff E x).mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_integerInclusion [ValuativeRel K] [ValuativeExtension K Ω] {E F : IntermediateField K Ω}
    (h : E ≤ F) (x : 𝒪[E]) : (((integerInclusion h x : 𝒪[F]) : F) : Ω) = ((x : E) : Ω) :=
  rfl

theorem integerInclusion_injective [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : Function.Injective (integerInclusion h) := by
  intro x y hxy
  have := congrArg (fun z : 𝒪[F] ↦ ((z : F) : Ω)) hxy
  exact Subtype.ext (Subtype.ext this)

instance isLocalHom_integerInclusion [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : IsLocalHom (integerInclusion h) :=
  ⟨fun x hx ↦ by
    rw [isUnit_integer_intermediateField_iff] at hx ⊢
    exact hx⟩

end Ambient

section Discrete

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

theorem exists_valuation_eq_algebraMap {x : Ω} (hx : x ∈ 𝔼) (hx0 : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ valuation Ω x = valuation Ω (algebraMap K Ω a) := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  have := hL.1
  have he : ramificationIndex K L = 1 := hL.ramificationIndex_eq_one
  set y : L := ⟨x, hxL⟩
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  refine ⟨a, ha, ?_⟩
  have h1 := ordRat_algebraMap_of_finite (K := K) (Ω := Ω) y
  rw [he, Nat.cast_one, div_one] at h1
  rw [← ordRat_eq_ordRat_iff (K := K) hx0 ((_root_.map_ne_zero _).mpr ha), ordRat_algebraMap,
    hay]
  exact h1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

@[simp]
theorem coe_algebraMap_integer_intermediateField (E : IntermediateField K Ω) (a : 𝒪[K]) :
    (((algebraMap 𝒪[K] 𝒪[E] a : 𝒪[E]) : E) : Ω) = algebraMap K Ω (a : K) :=
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

theorem valuation_algebraMap_eq_one_iff (x : K) :
    valuation Ω (algebraMap K Ω x) = 1 ↔ valuation K x = 1 := by
  simpa using valuation_algebraMap_eq_iff (G := Ω) x 1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

theorem not_isUnit_algebraMap_uniformizer (E : IntermediateField K Ω) {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) : ¬ IsUnit (algebraMap 𝒪[K] 𝒪[E] ϖ) := by
  rw [isUnit_integer_intermediateField_iff, coe_algebraMap_integer_intermediateField,
    valuation_algebraMap_eq_one_iff]
  exact ((Valuation.integer.integers (valuation K)).valuation_irreducible_lt_one hϖ).ne

theorem exists_associated_pow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {r : 𝒪[𝔼]} (hr : r ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n) r := by
  have hx0 : ((r : 𝔼) : Ω) ≠ 0 := by
    intro h
    exact hr (Subtype.ext (Subtype.ext h))
  obtain ⟨a, ha, hva⟩ := exists_valuation_eq_algebraMap (r : 𝔼).2 hx0
  have haK : a ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, ← map_one (valuation K), ← valuation_algebraMap_le_iff (G := Ω),
      map_one, ← hva]
    exact (mem_integer_intermediateField_iff _ _).mp r.2
  set a' : 𝒪[K] := ⟨a, haK⟩
  have ha' : a' ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha' hϖ
  have hu1 : valuation Ω (algebraMap K Ω ((u : 𝒪[K]) : K)) = 1 := by
    rw [valuation_algebraMap_eq_one_iff]
    exact (Valuation.integer.integers (valuation K)).valuation_unit u
  have hv : valuation Ω ((r : 𝔼) : Ω) = valuation Ω (algebraMap K Ω (ϖ : K)) ^ n := by
    have h2 : a = ((u : 𝒪[K]) : K) * (ϖ : K) ^ n := by
      have := congrArg Subtype.val hu
      simpa [a'] using this
    rw [hva, h2, map_mul, map_mul, hu1, one_mul, map_pow, map_pow]
  have hv' : valuation Ω (((algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n : 𝒪[𝔼]) : 𝔼) : Ω) =
      valuation Ω (algebraMap K Ω (ϖ : K)) ^ n := by
    rw [← map_pow]
    simp
  refine ⟨n, associated_of_dvd_dvd ?_ ?_⟩ <;> rw [dvd_integer_intermediateField_iff, hv, hv']

theorem irreducible_algebraMap_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[𝔼] ϖ) := by
  set p := algebraMap 𝒪[K] 𝒪[𝔼] ϖ
  have hp := not_isUnit_algebraMap_uniformizer 𝔼 hϖ
  have hp0 : p ≠ 0 := by
    intro h
    have h' := congrArg (fun z : 𝒪[𝔼] ↦ ((z : 𝔼) : Ω)) h
    simp only [p, coe_algebraMap_integer_intermediateField] at h'
    rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_eq_zero_iff _ (algebraMap K Ω).injective] at h'
    exact hϖ.ne_zero (Subtype.ext h')
  have hdvd : ∀ x : 𝒪[𝔼], ¬ IsUnit x → p ∣ x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨n, hn⟩ := exists_associated_pow hϖ hx0
    rcases n with _ | n
    · exact absurd (hn.isUnit (by simp)) hx
    · exact (dvd_pow_self p n.succ_ne_zero).trans hn.dvd
  refine irreducible_iff.mpr ⟨hp, fun a b hab ↦ ?_⟩
  by_contra h
  push Not at h
  obtain ⟨c, rfl⟩ := hdvd a h.1
  obtain ⟨d, rfl⟩ := hdvd b h.2
  have : p * (c * d) = 1 := by
    apply mul_left_cancel₀ hp0
    linear_combination hab.symm
  exact hp (isUnit_iff_exists_inv.mpr ⟨_, this⟩)

instance isDiscreteValuationRing_integer : IsDiscreteValuationRing 𝒪[𝔼] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_algebraMap_uniformizer hϖ, fun hx ↦ exists_associated_pow hϖ hx⟩

theorem map_maximalIdeal_integer : (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[𝔼]) = 𝓂[𝔼] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    (irreducible_algebraMap_uniformizer hϖ).maximalIdeal_eq]

end Discrete

section Automorphism

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsAlgebraic K L]

variable (K L) in

def integerAlgEquivOfIsAlgebraic : (L ≃ₐ[K] L) →* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) where
  toFun ρ :=
    { toFun x := ⟨ρ x, by
        rw [Valuation.mem_integer_iff, valuation_algEquiv_apply_of_isAlgebraic]
        exact x.2⟩
      invFun x := ⟨ρ.symm x, by
        rw [Valuation.mem_integer_iff, valuation_algEquiv_apply_of_isAlgebraic]
        exact x.2⟩
      left_inv x := Subtype.ext (ρ.symm_apply_apply _)
      right_inv x := Subtype.ext (ρ.apply_symm_apply _)
      map_mul' x y := Subtype.ext (map_mul ρ _ _)
      map_add' x y := Subtype.ext (map_add ρ _ _)
      commutes' a := Subtype.ext (ρ.commutes _) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem coe_integerAlgEquivOfIsAlgebraic_apply (ρ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    (integerAlgEquivOfIsAlgebraic K L ρ x : L) = ρ x :=
  rfl

end Automorphism

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] in

instance isAlgebraic_maximalUnramifiedExtension : Algebra.IsAlgebraic K 𝔼 :=
  inferInstance

theorem exists_pow_card_pow_sub_mem_maximalIdeal (x : 𝒪[𝔼]) :
    ∃ n : ℕ, n ≠ 0 ∧ x ^ (Nat.card 𝓀[K] ^ n) - x ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hxz : integerInclusion hle z = x := rfl
  refine ⟨Module.finrank K L, Module.finrank_pos.ne', ?_⟩
  have := Fintype.ofFinite 𝓀[L]
  have hz : z ^ (Nat.card 𝓀[K] ^ Module.finrank K L) - z ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← card_residueField_of_unramified K L h,
      Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  rw [← hxz]
  simpa using hz

theorem exists_isPrimitiveRoot_residue {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : ResidueField 𝒪[𝔼], IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  set L := IntermediateField.adjoin K {ζ}
  have := hL.1
  have hle := hL.le_maximalUnramifiedExtension
  have hmK := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hm : ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[L]) ≠ 0 := natCast_residueField_ne_zero L hmK
  have hm0 : Nat.card 𝓀[K] ^ n - 1 ≠ 0 := by
    rintro h0
    rw [h0, Nat.cast_zero] at hmK
    exact hmK rfl
  set ζL : L := IntermediateField.AdjoinSimple.gen K ζ
  have hζL : IsPrimitiveRoot ζL (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := L.val) Subtype.val_injective
  set ζO : 𝒪[L] := ⟨ζL, mem_integer_of_pow_eq_one hm0 hζL.pow_eq_one⟩
  have hζO : IsPrimitiveRoot ζO (Nat.card 𝓀[K] ^ n - 1) :=
    hζL.of_map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective
  have hres := isPrimitiveRoot_residue hm hζO
  refine ⟨residue 𝒪[𝔼] (integerInclusion hle ζO), ?_⟩
  refine ⟨by rw [← map_pow, ← map_pow, hζO.pow_eq_one, map_one, map_one], fun l hl ↦ ?_⟩
  refine hres.dvd_of_pow_eq_one l ?_
  rw [← map_pow, ← map_pow] at hl
  rw [← map_pow, ← map_one (residue 𝒪[L]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_intermediateField_iff]
  rw [← map_one (residue 𝒪[𝔼]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_intermediateField_iff] at hl
  simpa using hl

variable [IsGalois K Ω]

theorem frobenius_integer_sub_pow_mem_maximalIdeal (x : 𝒪[𝔼]) :
    integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x -
      x ^ Nat.card 𝓀[K] ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  obtain ⟨ξ, hξ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  rw [card_residueField_of_unramified K L h] at hξ
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have key : (maximalUnramifiedExtension K Ω).val.comp
      ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) =
      L.val.comp (frobenius K L h).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hz := frobenius_sub_pow_mem_maximalIdeal K L h z
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f ⟨(x : 𝔼), hxL⟩) key
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at hk
  convert hz using 2
  change ((maximalUnramifiedExtensionFrobenius K Ω (IntermediateField.inclusion hle ⟨(x : 𝔼), hxL⟩) :
      𝔼) : Ω) - _ = ((frobenius K L h ⟨(x : 𝔼), hxL⟩ : L) : Ω) - _
  rw [hk]
  rfl

end Frobenius

section FiniteFieldClosure

open Polynomial

variable {k k' : Type*} [Field k] [Finite k] [Field k'] [Algebra k k']

theorem isAlgebraic_of_pow_card_pow_eq_self {y : k'} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ (Nat.card k ^ n) = y) : IsAlgebraic k y :=
  ⟨X ^ (Nat.card k ^ n) - X, FiniteField.X_pow_card_pow_sub_X_ne_zero k hn Finite.one_lt_card,
    by simp [hy]⟩

omit [Algebra k k'] in

theorem splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot {m : ℕ} {ζ : k'}
    (hζ : IsPrimitiveRoot ζ (Nat.card k ^ m - 1)) :
    Splits (X ^ (Nat.card k ^ m) - X : k'[X]) := by
  have h1 : 1 ≤ Nat.card k ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : (X ^ (Nat.card k ^ m) - X : k'[X]) = X * (X ^ (Nat.card k ^ m - 1) - C 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ]
    rw [map_one]
    ring
  rw [this]
  exact Splits.X.mul (X_pow_sub_one_splits hζ)

theorem isAlgClosed_of_isPrimitiveRoot [Algebra.IsAlgebraic k k']
    (h : ∀ m : ℕ, m ≠ 0 → ∃ ζ : k', IsPrimitiveRoot ζ (Nat.card k ^ m - 1)) : IsAlgClosed k' := by
  refine IsAlgClosed.of_exists_root _ fun p _ hirr ↦ ?_
  have := Fact.mk hirr
  let A := AdjoinRoot p
  let α : A := AdjoinRoot.root p
  have : Module.Finite k' A := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Algebra.IsAlgebraic k' A := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic k A := Algebra.IsAlgebraic.trans k k' A
  have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let F := IntermediateField.adjoin k {α}
  have : FiniteDimensional k F := IntermediateField.adjoin.finiteDimensional hint
  have : Fintype k := Fintype.ofFinite k
  have : Finite F := Module.finite_of_finite k
  have : Fintype F := Fintype.ofFinite F
  set m := Module.finrank k F
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Fintype.card F = Nat.card k ^ m := by
    rw [Module.card_eq_pow_finrank (K := k) (V := F), Nat.card_eq_fintype_card]
  have hα : α ^ (Nat.card k ^ m) = α := by
    have := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen k α)
    rw [hcard] at this
    exact congrArg Subtype.val this
  obtain ⟨ζ, hζ⟩ := h m hm
  have hroot : ((X ^ (Nat.card k ^ m) - X : k'[X]).map (algebraMap k' A)).IsRoot α := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow,
      eval_X, hα, sub_self]
  obtain ⟨β, hβ⟩ := (splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot hζ).mem_range_of_isRoot
    (FiniteField.X_pow_card_pow_sub_X_ne_zero k' hm Finite.one_lt_card) hroot
  refine ⟨β, ?_⟩
  have h0 : aeval α p = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← hβ, aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  exact (map_eq_zero_iff _ (algebraMap k' A).injective).mp h0

end FiniteFieldClosure

section Residue

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

theorem exists_pow_card_pow_eq_self (y : 𝓀[𝔼]) :
    ∃ n : ℕ, n ≠ 0 ∧ y ^ (Nat.card 𝓀[K] ^ n) = y := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨n, hn, hx⟩ := exists_pow_card_pow_sub_mem_maximalIdeal x
  refine ⟨n, hn, ?_⟩
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

instance isAlgebraic_residueField : Algebra.IsAlgebraic 𝓀[K] 𝓀[𝔼] := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨n, hn, hy⟩ := exists_pow_card_pow_eq_self y
  exact isAlgebraic_of_pow_card_pow_eq_self hn hy

instance isAlgClosed_residueField : IsAlgClosed 𝓀[𝔼] :=
  isAlgClosed_of_isPrimitiveRoot (k := 𝓀[K]) fun _ hm ↦ exists_isPrimitiveRoot_residue hm

instance isAlgClosure_residueField :
    letI : Module.IsTorsionFree 𝓀[K] 𝓀[𝔼] := DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure 𝓀[K] 𝓀[𝔼] :=
  letI : Module.IsTorsionFree 𝓀[K] 𝓀[𝔼] := DivisionSemiring.to_moduleIsTorsionFree
  ⟨isAlgClosed_residueField, isAlgebraic_residueField⟩

end Residue

end Sec_MaximalUnramifiedIntegers


/-! ### CompletedUnramified -/
section Sec_CompletedUnramified

open IsLocalRing ValuativeRel

section Lift

variable {R : Type*} [CommRing R] {I : Ideal R}

variable (I) in

theorem factorPow_evalₐ {k n : ℕ} (hle : k ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq]
  have h := x.2 hle
  rw [SModEq.sub_mem] at h
  have hI : (I ^ k • ⊤ : Submodule R R) = I ^ k := by ext; simp
  rw [← neg_sub]
  exact neg_mem (hI ▸ h)

theorem pow_le_comap_pow {θ : R →+* R} (hθ : I ≤ I.comap θ) (n : ℕ) : I ^ n ≤ (I ^ n).comap θ :=
  Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hθ) n)

def adicCompletionQuotientMap (θ : R →+* R) (hθ : I ≤ I.comap θ) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) θ (pow_le_comap_pow hθ n)).comp
    (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)

theorem factorPow_comp_adicCompletionQuotientMap (θ : R →+* R) (hθ : I ≤ I.comap θ) {k n : ℕ}
    (hle : k ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (adicCompletionQuotientMap θ hθ n) =
      adicCompletionQuotientMap θ hθ k := by
  ext x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hk : AdicCompletion.evalₐ I k x = Ideal.Quotient.mk (I ^ k) r := by
    rw [← factorPow_evalₐ I hle, ← hr]
    rfl
  simp only [adicCompletionQuotientMap, RingHom.comp_apply, RingHom.coe_coe]
  rw [← hr, hk, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  rfl

def adicCompletionMap (θ : R →+* R) (hθ : I ≤ I.comap θ) :
    AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (adicCompletionQuotientMap θ hθ)
    (factorPow_comp_adicCompletionQuotientMap θ hθ)

theorem evalₐ_adicCompletionMap (θ : R →+* R) (hθ : I ≤ I.comap θ) (n : ℕ)
    (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionMap θ hθ x) =
      Ideal.quotientMap (I ^ n) θ (pow_le_comap_pow hθ n) (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom I _ (factorPow_comp_adicCompletionQuotientMap θ hθ) n x

@[simp]
theorem adicCompletionMap_of (θ : R →+* R) (hθ : I ≤ I.comap θ) (r : R) :
    adicCompletionMap θ hθ (AdicCompletion.of I R r) = AdicCompletion.of I R (θ r) := by
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of,
    Ideal.quotientMap_mk]

theorem adicCompletionMap_id :
    adicCompletionMap (RingHom.id R) (Ideal.comap_id I).ge = RingHom.id (AdicCompletion I R) := by
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [evalₐ_adicCompletionMap, RingHom.id_apply]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk, RingHom.id_apply]

theorem adicCompletionMap_comp (θ₁ θ₂ : R →+* R) (h₁ : I ≤ I.comap θ₁) (h₂ : I ≤ I.comap θ₂) :
    (adicCompletionMap θ₁ h₁).comp (adicCompletionMap θ₂ h₂) =
      adicCompletionMap (θ₁.comp θ₂)
        (by rw [← Ideal.comap_comap]; exact h₂.trans (Ideal.comap_mono h₁)) := by
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [RingHom.comp_apply, evalₐ_adicCompletionMap, evalₐ_adicCompletionMap,
    evalₐ_adicCompletionMap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

end Lift

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔅" => AdicCompletion (maximalIdeal R) R

variable (R) in

theorem algebraMap_adicCompletion_injective : Function.Injective (algebraMap R 𝔅) :=
  AdicCompletion.of_injective _ _

theorem maximalIdeal_adicCompletion_eq_span {ϖ : R} (hϖ : Irreducible ϖ) :
    maximalIdeal 𝔅 = Ideal.span {algebraMap R 𝔅 ϖ} := by
  rw [AdicCompletion.maximalIdeal_eq_map, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

theorem eq_zero_of_forall_mem_maximalIdeal_pow_adic {x : 𝔅} (h : ∀ n, x ∈ maximalIdeal 𝔅 ^ n) :
    x = 0 :=
  IsHausdorff.haus' (I := maximalIdeal 𝔅) x fun n ↦ by
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using h n

theorem exists_eq_unit_mul_pow_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) {x : 𝔅} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : 𝔅ˣ), x = u * algebraMap R 𝔅 ϖ ^ n :=
  _root_.RHDirect.CFT_AbstractLocalReciprocity.PowerSubgroups.exists_eq_unit_mul_pow_adicCompletion hϖ hx

theorem algebraMap_pow_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    algebraMap R 𝔅 ϖ ^ n ≠ 0 := by
  rw [← map_pow, Ne, ← map_zero (algebraMap R 𝔅), (algebraMap_adicCompletion_injective R).eq_iff]
  exact pow_ne_zero n hϖ.ne_zero

instance isDomain_adicCompletion : IsDomain 𝔅 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : NoZeroDivisors 𝔅 := ⟨fun {x y} hxy ↦ by
    by_contra h
    push Not at h
    obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ h.1
    obtain ⟨n, v, rfl⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ h.2
    apply algebraMap_pow_ne_zero hϖ (m + n)
    have : ((u * v : 𝔅ˣ) : 𝔅) * algebraMap R 𝔅 ϖ ^ (m + n) = 0 := by
      rw [← hxy, Units.val_mul, pow_add]
      ring
    exact (Units.mul_right_eq_zero _).mp this⟩
  exact NoZeroDivisors.to_isDomain _

theorem irreducible_algebraMap_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap R 𝔅 ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (by simpa using algebraMap_pow_ne_zero hϖ 1) (maximalIdeal_adicCompletion_eq_span hϖ)

instance isDiscreteValuationRing_adicCompletion : IsDiscreteValuationRing 𝔅 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_algebraMap_adicCompletion hϖ, fun hx ↦ by
      obtain ⟨n, u, hu⟩ := exists_eq_unit_mul_pow_adicCompletion hϖ hx
      exact ⟨n, u, by rw [hu, mul_comm]⟩⟩

theorem exists_sub_algebraMap_mem_pow (x : 𝔅) (n : ℕ) :
    ∃ r : R, x - algebraMap R 𝔅 r ∈ maximalIdeal 𝔅 ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm := maximalIdeal_adicCompletion_eq_span hϖ
  have hres : ∀ y : 𝔅, ∃ s : R, y - algebraMap R 𝔅 s ∈ maximalIdeal 𝔅 := by
    intro y
    obtain ⟨t, ht⟩ := (AdicCompletion.residueField_map_bijective R).2 (residue 𝔅 y)
    obtain ⟨s, rfl⟩ := residue_surjective t
    refine ⟨s, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, ← ht, ResidueField.map_residue, sub_self]
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
    obtain ⟨c, hc⟩ := hr
    obtain ⟨s, hs⟩ := hres c
    rw [hm, Ideal.mem_span_singleton'] at hs
    obtain ⟨d, hd⟩ := hs
    refine ⟨r + ϖ ^ n * s, ?_⟩
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨d, ?_⟩
    rw [map_add, map_mul, map_pow]
    linear_combination (algebraMap R 𝔅 ϖ) ^ n * hd + hc

theorem ringHom_ext_adicCompletion {ϖ : R} (hϖ : Irreducible ϖ) {τ₁ τ₂ : 𝔅 →+* 𝔅}
    (h : ∀ r, τ₁ (algebraMap R 𝔅 r) = τ₂ (algebraMap R 𝔅 r))
    (hmem : τ₁ (algebraMap R 𝔅 ϖ) ∈ maximalIdeal 𝔅) : τ₁ = τ₂ := by
  have hm := maximalIdeal_adicCompletion_eq_span hϖ
  refine RingHom.ext fun x ↦ ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_maximalIdeal_pow_adic fun n ↦ ?_
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow x n
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hr
  obtain ⟨c, hc⟩ := hr
  have hx : x = algebraMap R 𝔅 r + c * algebraMap R 𝔅 ϖ ^ n := by rw [hc]; ring
  rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, h r, ← h ϖ]
  have : τ₁ (algebraMap R 𝔅 ϖ) ^ n ∈ maximalIdeal 𝔅 ^ n := Ideal.pow_mem_pow hmem n
  convert Ideal.mul_mem_left _ (τ₁ c - τ₂ c) this using 1
  ring

end DVR

section Automorphism

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "𝔅" => AdicCompletion (maximalIdeal R) R

theorem maximalIdeal_le_comap_ringEquiv (θ : R ≃+* R) :
    maximalIdeal R ≤ (maximalIdeal R).comap (θ : R →+* R) := by
  intro x hx
  rw [Ideal.mem_comap]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  simpa using hu.map θ.symm

theorem adicCompletionMap_congr {θ₁ θ₂ : R →+* R} (h : θ₁ = θ₂)
    (h₁ : maximalIdeal R ≤ (maximalIdeal R).comap θ₁) (h₂ : maximalIdeal R ≤ (maximalIdeal R).comap θ₂) :
    adicCompletionMap θ₁ h₁ = adicCompletionMap θ₂ h₂ := by
  subst h
  rfl

theorem adicCompletionMap_eq_id {θ : R →+* R} (hθ : maximalIdeal R ≤ (maximalIdeal R).comap θ)
    (h : θ = RingHom.id R) : adicCompletionMap θ hθ = RingHom.id 𝔅 := by
  subst h
  exact adicCompletionMap_id

def adicCompletionRingEquiv (θ : R ≃+* R) : 𝔅 ≃+* 𝔅 :=
  RingEquiv.ofRingHom
    (adicCompletionMap (θ : R →+* R) (maximalIdeal_le_comap_ringEquiv θ))
    (adicCompletionMap (θ.symm : R →+* R) (maximalIdeal_le_comap_ringEquiv θ.symm))
    (by
      rw [adicCompletionMap_comp]
      exact adicCompletionMap_eq_id _ (by ext; simp))
    (by
      rw [adicCompletionMap_comp]
      exact adicCompletionMap_eq_id _ (by ext; simp))

theorem adicCompletionRingEquiv_apply (θ : R ≃+* R) (x : 𝔅) :
    adicCompletionRingEquiv θ x =
      adicCompletionMap (θ : R →+* R) (maximalIdeal_le_comap_ringEquiv θ) x :=
  rfl

variable {S : Type*} [CommRing S] [Algebra S R]

def adicCompletionAlgEquiv : (R ≃ₐ[S] R) →* (𝔅 ≃ₐ[S] 𝔅) where
  toFun θ :=
    AlgEquiv.ofRingEquiv (f := adicCompletionRingEquiv θ.toRingEquiv) (fun s ↦ by
      change adicCompletionMap _ _ (AdicCompletion.of _ R (algebraMap S R s)) =
        AdicCompletion.of _ R (algebraMap S R s)
      rw [adicCompletionMap_of]
      simp)
  map_one' := by
    ext1 x
    change adicCompletionMap _ _ x = x
    rw [adicCompletionMap_eq_id _ (by ext; simp)]
    rfl
  map_mul' θ₁ θ₂ := by
    ext1 x
    change adicCompletionMap _ _ x = adicCompletionMap _ _ (adicCompletionMap _ _ x)
    rw [← RingHom.comp_apply (adicCompletionMap _ _), adicCompletionMap_comp]
    exact congrArg (fun f : 𝔅 →+* 𝔅 ↦ f x) (adicCompletionMap_congr (by ext; simp) _ _)

@[simp]
theorem adicCompletionAlgEquiv_algebraMap (θ : R ≃ₐ[S] R) (r : R) :
    adicCompletionAlgEquiv θ (algebraMap R 𝔅 r) = algebraMap R 𝔅 (θ r) :=
  show adicCompletionMap _ _ (AdicCompletion.of _ R r) = _ from adicCompletionMap_of _ _ r

theorem eq_adicCompletionAlgEquiv (θ : R ≃ₐ[S] R) {τ : 𝔅 →+* 𝔅}
    (hτ : ∀ r, τ (algebraMap R 𝔅 r) = algebraMap R 𝔅 (θ r)) :
    τ = (adicCompletionAlgEquiv θ : 𝔅 →+* 𝔅) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ringHom_ext_adicCompletion hϖ (fun r ↦ ?_) ?_
  · rw [hτ]
    exact (adicCompletionAlgEquiv_algebraMap θ r).symm
  · rw [hτ, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.mem_map_of_mem _ ?_
    exact maximalIdeal_le_comap_ringEquiv θ.toRingEquiv (hϖ.maximalIdeal_eq ▸
      Ideal.mem_span_singleton_self ϖ)

end Automorphism

section FixedRing

open Polynomial

theorem mem_range_of_pow_card_eq_self {F k : Type*} [Field F] [Finite F] [Field k] [Algebra F k]
    {y : k} (hy : y ^ Nat.card F = y) : y ∈ (algebraMap F k).range := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at hy
  have hs : Splits (X ^ Fintype.card F - X : F[X]) := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      FiniteField.X_pow_card_sub_X_natDegree_eq F hq]
    exact Finset.card_univ
  refine hs.mem_range_of_isRoot (FiniteField.X_pow_card_sub_X_ne_zero F hq) ?_
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow,
    eval_X, hy, sub_self]

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]

theorem isLocalHom_algebraMap_of_map_maximalIdeal
    (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsLocalHom (algebraMap A B) := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 h
  have := Ideal.mem_map_of_mem (algebraMap A B) hm
  rw [hunr] at this
  exact (mem_maximalIdeal _).1 this ha

variable [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
  (hunr : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (σ : B →ₐ[A] B)
  (hσ : ∀ x : B, residue B (σ x) = residue B x ^ Nat.card (ResidueField A))
include hunr hσ

omit [IsAdicComplete (maximalIdeal A) A] in

theorem exists_sub_algebraMap_mem_of_fixed {c : B} (hc : σ c = c) :
    ∃ d : A, c - algebraMap A B d ∈ maximalIdeal B := by
  have := isLocalHom_algebraMap_of_map_maximalIdeal hunr
  have hy : residue B c ^ Nat.card (ResidueField A) = residue B c := by rw [← hσ, hc]
  obtain ⟨t, ht⟩ := mem_range_of_pow_card_eq_self hy
  obtain ⟨d, rfl⟩ := residue_surjective t
  refine ⟨d, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, ← ht, ResidueField.algebraMap_residue, sub_self]

theorem mem_range_algebraMap_iff_fixed (b : B) : b ∈ (algebraMap A B).range ↔ σ b = b := by
  refine ⟨fun ⟨a, ha⟩ ↦ by rw [← ha, σ.commutes], fun hb ↦ ?_⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set ϖ := algebraMap A B π with hϖdef
  have hmB : maximalIdeal B = Ideal.span {ϖ} := by
    rw [← hunr, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field B
    rw [hmB, h0, Ideal.span_singleton_eq_bot]
  have hϖm : ϖ ∈ maximalIdeal B := hmB ▸ Ideal.mem_span_singleton_self ϖ
  have hπm : π ∈ maximalIdeal A := hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hσϖ : σ ϖ = ϖ := σ.commutes π
  have step : ∀ c : B, σ c = c → ∃ d : A, ∃ c' : B, σ c' = c' ∧ c = algebraMap A B d + ϖ * c' := by
    intro c hc
    obtain ⟨d, hd⟩ := exists_sub_algebraMap_mem_of_fixed hunr σ hσ hc
    rw [hmB, Ideal.mem_span_singleton'] at hd
    obtain ⟨c', hc'⟩ := hd
    refine ⟨d, c', ?_, by rw [mul_comm, hc']; ring⟩
    have h1 := congrArg σ hc'
    rw [map_mul, hσϖ, map_sub, hc, σ.commutes, ← hc'] at h1
    exact mul_right_cancel₀ hϖ0 h1
  choose D N hN hDN using step
  let c : ℕ → {x : B // σ x = x} := fun n ↦
    Nat.rec ⟨b, hb⟩ (fun _ x ↦ ⟨N x.1 x.2, hN x.1 x.2⟩) n
  have hc_succ : ∀ n, (c (n + 1)).1 = N (c n).1 (c n).2 := fun _ ↦ rfl
  let d : ℕ → A := fun n ↦ D (c n).1 (c n).2
  let s : ℕ → A := fun n ↦ ∑ i ∈ Finset.range n, π ^ i * d i
  have hs : ∀ n, b = algebraMap A B (s n) + ϖ ^ n * (c n).1 := by
    intro n
    induction n with
    | zero => simp [s, c]
    | succ n ih =>
      have h := hDN (c n).1 (c n).2
      rw [← hc_succ] at h
      rw [ih, h]
      simp only [s, d, Finset.sum_range_succ, map_add, map_mul, map_pow]
      ring
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → s m ≡ s n [SMOD (maximalIdeal A ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff]
    simp only [s]
    rw [← Finset.sum_Ico_eq_sub _ hmn]
    refine Ideal.sum_mem _ fun i hi ↦ ?_
    refine Ideal.mul_mem_right _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.mp hi).1 (Ideal.pow_mem_pow hπm i)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) s hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal B) _ fun n ↦ ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have hLn := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hLn
  have h1 : algebraMap A B (s n - L) ∈ maximalIdeal B ^ n := by
    rw [← hunr, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hLn
  have h2 : ϖ ^ n * (c n).1 ∈ maximalIdeal B ^ n :=
    Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hϖm n)
  have : algebraMap A B L - b = -(algebraMap A B (s n - L) + ϖ ^ n * (c n).1) := by
    rw [hs n, map_sub]
    ring
  rw [this, neg_mem_iff]
  exact add_mem h1 h2

end FixedRing

section Completed

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

abbrev CompletedUnramifiedIntegers : Type _ :=
  AdicCompletion (maximalIdeal 𝒪[maximalUnramifiedExtension K Ω]) 𝒪[maximalUnramifiedExtension K Ω]

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

example : IsDiscreteValuationRing 𝔹 := inferInstance

theorem isAdicComplete_completedUnramifiedIntegers : IsAdicComplete (maximalIdeal 𝔹) 𝔹 :=
  inferInstance

instance isScalarTower_completedUnramifiedIntegers : IsScalarTower 𝒪[K] 𝒪[𝔼] 𝔹 :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

theorem algebraMap_integer_completedUnramifiedIntegers_injective :
    Function.Injective (algebraMap 𝒪[𝔼] 𝔹) :=
  algebraMap_adicCompletion_injective _

theorem algebraMap_completedUnramifiedIntegers_injective :
    Function.Injective (algebraMap 𝒪[K] 𝔹) := by
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[𝔼] 𝔹]
  exact (algebraMap_integer_completedUnramifiedIntegers_injective K Ω).comp
    (algebraMap_integer_injective K 𝔼)

theorem map_maximalIdeal_completedUnramifiedIntegers :
    (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝔹) = maximalIdeal 𝔹 := by
  rw [IsScalarTower.algebraMap_eq 𝒪[K] 𝒪[𝔼] 𝔹, ← Ideal.map_map, map_maximalIdeal_integer,
    AdicCompletion.maximalIdeal_eq_map]

instance isLocalHom_algebraMap_completedUnramifiedIntegers : IsLocalHom (algebraMap 𝒪[K] 𝔹) :=
  isLocalHom_algebraMap_of_map_maximalIdeal (map_maximalIdeal_completedUnramifiedIntegers K Ω)

theorem irreducible_algebraMap_completedUnramifiedIntegers_iff (π : 𝒪[K]) :
    Irreducible (algebraMap 𝒪[K] 𝔹 π) ↔ Irreducible π := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine irreducible_iff.mpr ⟨fun hu ↦ h.not_isUnit (hu.map _), fun a b hab ↦ ?_⟩
    rw [hab, map_mul] at h
    exact (h.isUnit_or_isUnit rfl).imp (isUnit_of_map_unit _ _) (isUnit_of_map_unit _ _)
  · rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[𝔼] 𝔹]
    exact irreducible_algebraMap_adicCompletion (irreducible_algebraMap_uniformizer h)

def residueFieldCompletedUnramifiedIntegersEquiv :
    ResidueField 𝒪[𝔼] ≃+* ResidueField 𝔹 :=
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective 𝒪[𝔼])

instance isAlgClosed_residueField_completedUnramifiedIntegers : IsAlgClosed (ResidueField 𝔹) :=
  IsAlgClosed.of_ringEquiv _ _ (residueFieldCompletedUnramifiedIntegersEquiv K Ω)

instance isAlgebraic_residueField_completedUnramifiedIntegers :
    Algebra.IsAlgebraic 𝓀[K] (ResidueField 𝔹) :=
  AlgEquiv.isAlgebraic (R := 𝓀[K]) (A := ResidueField 𝒪[𝔼])
    (AlgEquiv.ofRingEquiv (f := residueFieldCompletedUnramifiedIntegersEquiv K Ω) fun t ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective t
      change ResidueField.map (algebraMap 𝒪[𝔼] 𝔹)
        (algebraMap 𝓀[K] (ResidueField 𝒪[𝔼]) (residue 𝒪[K] a)) = _
      rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue,
        ResidueField.map_residue]
      rfl)

instance isAlgClosure_residueField_completedUnramifiedIntegers :
    letI : Module.IsTorsionFree 𝓀[K] (ResidueField 𝔹) := DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure 𝓀[K] (ResidueField 𝔹) :=
  letI : Module.IsTorsionFree 𝓀[K] (ResidueField 𝔹) := DivisionSemiring.to_moduleIsTorsionFree
  ⟨isAlgClosed_residueField_completedUnramifiedIntegers K Ω,
    isAlgebraic_residueField_completedUnramifiedIntegers K Ω⟩

end Completed

section Frobenius

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

def completedUnramifiedAlgEquiv : (𝔼 ≃ₐ[K] 𝔼) →* (𝔹 ≃ₐ[𝒪[K]] 𝔹) :=
  adicCompletionAlgEquiv.comp (integerAlgEquivOfIsAlgebraic K 𝔼)

variable {K Ω}

@[simp]
theorem completedUnramifiedAlgEquiv_algebraMap (ρ : 𝔼 ≃ₐ[K] 𝔼) (x : 𝒪[𝔼]) :
    completedUnramifiedAlgEquiv K Ω ρ (algebraMap 𝒪[𝔼] 𝔹 x) =
      algebraMap 𝒪[𝔼] 𝔹 (integerAlgEquivOfIsAlgebraic K 𝔼 ρ x) :=
  adicCompletionAlgEquiv_algebraMap _ x

theorem eq_completedUnramifiedAlgEquiv (ρ : 𝔼 ≃ₐ[K] 𝔼) {τ : 𝔹 →+* 𝔹}
    (hτ : ∀ x : 𝒪[𝔼], τ (algebraMap 𝒪[𝔼] 𝔹 x) =
      algebraMap 𝒪[𝔼] 𝔹 (integerAlgEquivOfIsAlgebraic K 𝔼 ρ x)) :
    τ = (completedUnramifiedAlgEquiv K Ω ρ : 𝔹 →+* 𝔹) :=
  eq_adicCompletionAlgEquiv _ hτ

variable [IsGalois K Ω]

variable (K Ω) in

def completedFrobenius : 𝔹 ≃ₐ[𝒪[K]] 𝔹 :=
  completedUnramifiedAlgEquiv K Ω (maximalUnramifiedExtensionFrobenius K Ω)

theorem completedFrobenius_algebraMap (x : 𝒪[𝔼]) :
    completedFrobenius K Ω (algebraMap 𝒪[𝔼] 𝔹 x) = algebraMap 𝒪[𝔼] 𝔹
      (integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x) :=
  completedUnramifiedAlgEquiv_algebraMap _ x

theorem eq_completedFrobenius {τ : 𝔹 →+* 𝔹}
    (hτ : ∀ x : 𝒪[𝔼], τ (algebraMap 𝒪[𝔼] 𝔹 x) = algebraMap 𝒪[𝔼] 𝔹
      (integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x)) :
    τ = (completedFrobenius K Ω : 𝔹 →+* 𝔹) :=
  eq_completedUnramifiedAlgEquiv _ hτ

theorem residue_completedFrobenius (x : 𝔹) :
    residue 𝔹 (completedFrobenius K Ω x) = residue 𝔹 x ^ Nat.card 𝓀[K] := by
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow x 1
  rw [pow_one] at hr
  set σ := completedFrobenius K Ω
  have h1 : residue 𝔹 x = residue 𝔹 (algebraMap 𝒪[𝔼] 𝔹 r) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hr
  have h2 : residue 𝔹 (σ x) = residue 𝔹 (σ (algebraMap 𝒪[𝔼] 𝔹 r)) := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    exact fun hu ↦ hr (by simpa using hu.map σ.symm)
  rw [h2, h1, completedFrobenius_algebraMap, ← map_pow, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff, ← map_pow, ← map_sub, AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.mem_map_of_mem _ (frobenius_integer_sub_pow_mem_maximalIdeal r)

theorem mem_range_algebraMap_iff_completedFrobenius (b : 𝔹) :
    b ∈ (algebraMap 𝒪[K] 𝔹).range ↔ completedFrobenius K Ω b = b :=
  have := isAdicComplete_integer K
  mem_range_algebraMap_iff_fixed (map_maximalIdeal_completedUnramifiedIntegers K Ω)
    (completedFrobenius K Ω).toAlgHom (residue_completedFrobenius) b

variable (K Ω) in

theorem completedUnramifiedIntegers_spec :
    IsDiscreteValuationRing 𝔹 ∧ IsAdicComplete (maximalIdeal 𝔹) 𝔹 ∧
      Function.Injective (algebraMap 𝒪[K] 𝔹) ∧
      (maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝔹) = maximalIdeal 𝔹 ∧
      (∀ π : 𝒪[K], Irreducible (algebraMap 𝒪[K] 𝔹 π) ↔ Irreducible π) ∧
      IsAlgClosed (ResidueField 𝔹) ∧ Algebra.IsAlgebraic 𝓀[K] (ResidueField 𝔹) ∧
      (∀ x : 𝔹, residue 𝔹 (completedFrobenius K Ω x) = residue 𝔹 x ^ Nat.card 𝓀[K]) ∧
      (∀ b : 𝔹, completedFrobenius K Ω b = b ↔ b ∈ (algebraMap 𝒪[K] 𝔹).range) :=
  ⟨inferInstance, inferInstance, algebraMap_completedUnramifiedIntegers_injective K Ω,
    map_maximalIdeal_completedUnramifiedIntegers K Ω,
    irreducible_algebraMap_completedUnramifiedIntegers_iff K Ω, inferInstance, inferInstance,
    residue_completedFrobenius, fun b ↦ (mem_range_algebraMap_iff_completedFrobenius b).symm⟩

end Frobenius

section Finite

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

def integerToCompleted {L : IntermediateField K Ω} (h : L ≤ 𝔼) : 𝒪[L] →ₐ[𝒪[K]] 𝔹 :=
  (IsScalarTower.toAlgHom 𝒪[K] 𝒪[𝔼] 𝔹).comp (integerInclusion h)

variable {K Ω}

@[simp]
theorem integerToCompleted_apply {L : IntermediateField K Ω} (h : L ≤ 𝔼) (x : 𝒪[L]) :
    integerToCompleted K Ω h x = algebraMap 𝒪[𝔼] 𝔹 (integerInclusion h x) :=
  rfl

theorem integerToCompleted_injective {L : IntermediateField K Ω} (h : L ≤ 𝔼) :
    Function.Injective (integerToCompleted K Ω h) :=
  (algebraMap_integer_completedUnramifiedIntegers_injective K Ω).comp (integerInclusion_injective h)

theorem integerToCompleted_comp_integerInclusion {L L' : IntermediateField K Ω} (h : L ≤ L')
    (h' : L' ≤ 𝔼) :
    (integerToCompleted K Ω h').comp (integerInclusion h) = integerToCompleted K Ω (h.trans h') :=
  AlgHom.ext fun _ ↦ rfl

theorem IsUnramifiedSubextension.injective_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) :
    Function.Injective (integerToCompleted K Ω hL.le_maximalUnramifiedExtension) :=
  integerToCompleted_injective _

end Finite

section FiniteFrobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

local notation "𝔹" => CompletedUnramifiedIntegers K Ω

theorem maximalUnramifiedExtensionFrobenius_inclusion {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    ((maximalUnramifiedExtensionFrobenius K Ω
      (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y) : 𝔼) : Ω) =
      ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  obtain ⟨ξ, hξ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  rw [card_residueField_of_unramified K L h] at hξ
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have key : (maximalUnramifiedExtension K Ω).val.comp
      ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) =
      L.val.comp (frobenius K L h).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f y) key
  simpa only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] using hk

theorem completedFrobenius_integerToCompleted {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (x : 𝒪[L]) :
    letI := hL.1
    completedFrobenius K Ω (integerToCompleted K Ω hL.le_maximalUnramifiedExtension x) =
      integerToCompleted K Ω hL.le_maximalUnramifiedExtension
        (integerAlgEquiv K L (frobenius K L hL.ramificationIndex_eq_one) x) := by
  have := hL.1
  rw [integerToCompleted_apply, integerToCompleted_apply, completedFrobenius_algebraMap]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  exact maximalUnramifiedExtensionFrobenius_inclusion hL (x : L)

end FiniteFrobenius

section Check

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

example : IsAdicComplete (maximalIdeal (CompletedUnramifiedIntegers K (SeparableClosure K)))
    (CompletedUnramifiedIntegers K (SeparableClosure K)) :=
  inferInstance

example (b : CompletedUnramifiedIntegers K (SeparableClosure K)) :
    completedFrobenius K (SeparableClosure K) b = b ↔
      b ∈ (algebraMap 𝒪[K] (CompletedUnramifiedIntegers K (SeparableClosure K))).range :=
  (completedUnramifiedIntegers_spec K (SeparableClosure K)).2.2.2.2.2.2.2.2 b

example (π : 𝒪[K]) (hπ : Irreducible π) :
    IsDomain (CompletedUnramifiedIntegers K (SeparableClosure K)) ∧
      IsDiscreteValuationRing (CompletedUnramifiedIntegers K (SeparableClosure K)) ∧
      Irreducible (algebraMap 𝒪[K] (CompletedUnramifiedIntegers K (SeparableClosure K)) π) ∧
      IsAlgClosed (ResidueField (CompletedUnramifiedIntegers K (SeparableClosure K))) ∧
      ∀ x : CompletedUnramifiedIntegers K (SeparableClosure K),
        residue _ ((completedFrobenius K (SeparableClosure K)).toAlgHom x) =
          residue _ x ^ Nat.card (ResidueField 𝒪[K]) :=
  ⟨inferInstance, inferInstance,
    (irreducible_algebraMap_completedUnramifiedIntegers_iff K (SeparableClosure K) π).mpr hπ,
    inferInstance, residue_completedFrobenius⟩

end Check

end Sec_CompletedUnramified


/-! ### Eisenstein -/
section Sec_Eisenstein

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem eq_zero_of_addVal_lt_of_sum_eq_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : ι → R}
    (hs : ∑ i ∈ s, t i = 0) {j : ι} (hj : j ∈ s)
    (hlt : ∀ i ∈ s, i ≠ j → addVal R (t j) < addVal R (t i)) : t j = 0 := by
  by_contra h0
  have htop : addVal R (t j) ≠ ⊤ := fun h => h0 (addVal_eq_top_iff.mp h)
  have hrest : addVal R (t j) < addVal R (∑ i ∈ s.erase j, t i) :=
    (addVal R).map_lt_sum htop fun i hi => hlt i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi)
  have := (addVal R).map_add_eq_of_lt_left hrest
  rw [Finset.add_sum_erase s t hj, hs, AddValuation.map_zero] at this
  exact htop this.symm

theorem exists_addVal_eq_coe {x : R} (hx : x ≠ 0) : ∃ k : ℕ, addVal R x = k := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  exact ⟨k, addVal_def' u hϖ k⟩

end DVR

section Local

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem addVal_algebraMap_integer (x : 𝒪[K]) :
    addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) = ramificationIndex K L * addVal 𝒪[K] x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]
  have key : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] ϖ) = ramificationIndex K L := by
    have h := map_maximalIdeal K L
    rw [hϖ.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    rw [(addVal_eq_iff_associated _ _).mpr h, hϖL.addVal_pow]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.mul_top]
    exact_mod_cast (ramificationIndex_pos K L).ne'
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [map_mul, map_pow, addVal_mul, addVal_pow, key, addVal_def' u hϖ k]
  have hu : IsUnit (algebraMap 𝒪[K] 𝒪[L] u) := u.isUnit.map _
  rw [addVal_eq_zero_iff.mpr hu, zero_add, nsmul_eq_mul, mul_comm]

end Local

section DVR2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem mem_maximalIdeal_pow_iff_le_addVal (k : ℕ) (x : R) :
    x ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hϖ.addVal_pow]

theorem addVal_eq_one_of_mem_of_notMem_sq {x : R} (h1 : x ∈ IsLocalRing.maximalIdeal R)
    (h2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) : addVal R x = 1 := by
  rw [← pow_one (IsLocalRing.maximalIdeal R), mem_maximalIdeal_pow_iff_le_addVal] at h1
  rw [mem_maximalIdeal_pow_iff_le_addVal, not_le] at h2
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk] at h1 h2 ⊢
  norm_cast at h1 h2 ⊢
  omega

end DVR2

section Forward

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natDegree_mul_addVal_eq_ramificationIndex {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
    {α : 𝒪[L]} (hα : aeval α f = 0) :
    (f.natDegree : ℕ∞) * addVal 𝒪[L] α = ramificationIndex K L := by
  set n := f.natDegree with hn_def
  set e := ramificationIndex K L with he_def
  have he : 0 < e := ramificationIndex_pos K L
  have hinj := algebraMap_integer_injective K L
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [aeval_def, eval₂_at_zero] at hα
    have : f.coeff 0 = 0 := hinj (by rw [hα, map_zero])
    exact hf.notMem (by rw [this]; exact zero_mem _)
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (f.coeff i) * α ^ i with ht
  have hsum : ∑ i ∈ Finset.range (n + 1), t i = 0 := by
    rw [← hα, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, n]
  have hval : ∀ i, addVal 𝒪[L] (t i) = e * addVal 𝒪[K] (f.coeff i) + i * m := by
    intro i
    simp only [t, addVal_mul, addVal_pow, addVal_algebraMap_integer, hm, nsmul_eq_mul, e]

  have hlow : ∀ i < n, ((e + i * m : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi
    have h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i) := by
      have := hf.mem hi
      rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[K]), mem_maximalIdeal_pow_iff_le_addVal] at this
      exact_mod_cast this
    rw [hval]
    push_cast
    gcongr
    calc (e : ℕ∞) = e * 1 := (mul_one _).symm
      _ ≤ e * addVal 𝒪[K] (f.coeff i) := by gcongr

  have htop : addVal 𝒪[L] (t n) = ((n * m : ℕ) : ℕ∞) := by
    have hu : IsUnit (f.coeff n) := by
      have := hf.leading
      rw [leadingCoeff] at this
      exact (IsLocalRing.notMem_maximalIdeal.mp this)
    rw [hval, addVal_eq_zero_iff.mpr hu]
    push_cast
    ring

  have hbot : addVal 𝒪[L] (t 0) = (e : ℕ∞) := by
    have h1 : f.coeff 0 ∈ IsLocalRing.maximalIdeal 𝒪[K] := hf.mem hn
    rw [hval, addVal_eq_one_of_mem_of_notMem_sq h1 hf.notMem]
    simp
  have hne_n : t n ≠ 0 := by
    intro h
    rw [h, addVal_zero] at htop
    exact ENat.top_ne_natCast _ htop
  have hne_0 : t 0 ≠ 0 := by
    intro h
    rw [h, addVal_zero] at hbot
    exact ENat.top_ne_natCast _ hbot

  have hA : e ≤ n * m := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_n (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ n) ?_)
    intro i hi hin
    have hi' : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    refine lt_of_lt_of_le ?_ (hlow i hi')
    rw [htop]
    exact_mod_cast (by omega : n * m < e + i * m)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hA
      omega
    · exact h

  have hB : n * m ≤ e := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_0 (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (by simp) ?_)
    intro i hi hi0
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hbot]
    rcases lt_or_eq_of_le hi' with hlt' | rfl
    · refine lt_of_lt_of_le ?_ (hlow i hlt')
      have : 1 ≤ i * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hi0 (by omega))
      exact_mod_cast (by omega : e < e + i * m)
    · rw [htop]
      exact_mod_cast hlt
  rw [hm]
  exact_mod_cast le_antisymm hB hA

end Forward

section TotallyRamified

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem residueDegree_eq_one_of_ramificationIndex_eq_finrank
    (h : ramificationIndex K L = Module.finrank K L) : residueDegree K L = 1 := by
  have h1 := ramificationIndex_mul_residueDegree K L
  have h2 := ramificationIndex_pos K L
  rw [h] at h1 h2
  exact (Nat.mul_eq_left h2.ne').mp h1

theorem exists_sub_algebraMap_mem_maximalIdeal (h : residueDegree K L = 1) (w : 𝒪[L]) :
    ∃ c : 𝒪[K], w - algebraMap 𝒪[K] 𝒪[L] c ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
  rw [residueDegree_eq_finrank, finrank_eq_one_iff_of_nonzero' (1 : 𝓀[L]) one_ne_zero] at h
  obtain ⟨c, hc⟩ := h (IsLocalRing.residue 𝒪[L] w)
  obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
  refine ⟨c', ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, Algebra.smul_def, mul_one,
    IsLocalRing.ResidueField.algebraMap_residue, sub_self]

end TotallyRamified

section Eisenstein

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem isUnit_leadingCoeff_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : IsUnit f.leadingCoeff :=
  IsLocalRing.notMem_maximalIdeal.mp hf.leading

theorem isPrimitive_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : f.IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  exact isUnit_of_dvd_unit (hr _) (isUnit_leadingCoeff_of_isEisensteinAt hf)

theorem irreducible_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible f :=
  hf.irreducible (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime
    (isPrimitive_of_isEisensteinAt hf) hn

theorem irreducible_map_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap 𝒪[K] K)) :=
  (isPrimitive_of_isEisensteinAt hf).irreducible_iff_irreducible_map_fraction_map.mp
    (irreducible_of_isEisensteinAt hf hn)

variable [Field L] [Algebra K L]

theorem isIntegral_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    IsIntegral 𝒪[K] α := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_of_isEisensteinAt hf
  refine ⟨C (↑u⁻¹ : 𝒪[K]) * f, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp), ?_⟩
  rw [← aeval_def, map_mul, hα, mul_zero]

theorem finrank_adjoin_le_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    Module.finrank K K⟮α⟯ ≤ f.natDegree := by
  have hint : IsIntegral K α := (isIntegral_of_isEisensteinAt hf hα).tower_top
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hne : f.map (algebraMap 𝒪[K] K) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hinj]
    rintro rfl
    exact hf.leading (by simp)
  rw [IntermediateField.adjoin.finrank hint, ← natDegree_map_eq_of_injective hinj f]
  exact natDegree_le_of_dvd (minpoly.dvd K α (by rw [aeval_map_algebraMap, hα])) hne

theorem minpoly_eq_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) {α : L}
    (hα : aeval α f = 0) :
    minpoly K α = C (algebraMap 𝒪[K] K f.leadingCoeff)⁻¹ * f.map (algebraMap 𝒪[K] K) := by
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hc : algebraMap 𝒪[K] K f.leadingCoeff ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    rintro h
    exact hf.leading (by rw [h]; exact zero_mem _)
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · rw [irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hc)))]
    exact irreducible_map_of_isEisensteinAt hf hn
  · rw [map_mul, aeval_map_algebraMap, hα, mul_zero]
  · refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [leadingCoeff_map_of_injective hinj, inv_mul_cancel₀ hc]

end Eisenstein

section Root

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}

theorem mem_integer_of_isEisensteinAt (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    {α : L} (hα : aeval α f = 0) : α ∈ 𝒪[L] :=
  (isIntegral_iff K L α).mp (isIntegral_of_isEisensteinAt hf hα)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [FiniteDimensional K L] in
theorem aeval_integer_eq_zero {α : L} (h : α ∈ 𝒪[L]) (hα : aeval α f = 0) :
    aeval (⟨α, h⟩ : 𝒪[L]) f = 0 := by
  refine Subtype.val_injective ?_
  have h2 : (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) (aeval (⟨α, h⟩ : 𝒪[L]) f) = aeval α f :=
    (aeval_algHom_apply _ _ _).symm
  rw [hα] at h2
  simpa using h2

theorem isEisensteinAt_root_of_finrank_le (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < f.natDegree) {α : 𝒪[L]} (hα : aeval α f = 0)
    (hdeg : Module.finrank K L ≤ f.natDegree) :
    ramificationIndex K L = f.natDegree ∧ Module.finrank K L = f.natDegree ∧ Irreducible α := by
  have key := natDegree_mul_addVal_eq_ramificationIndex hf hn hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [addVal_zero, ENat.mul_top (by exact_mod_cast hn.ne')] at key
    exact ENat.top_ne_natCast _ key
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  rw [hm] at key
  have key' : f.natDegree * m = ramificationIndex K L := by exact_mod_cast key
  have hef := ramificationIndex_mul_residueDegree K L
  have hf1 := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hle : ramificationIndex K L ≤ Module.finrank K L := by
    rw [← hef]
    exact Nat.le_mul_of_pos_right _ hf1
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 1 with h | h
    · have : m = 0 := by omega
      rw [this, mul_zero] at key'
      omega
    · have : f.natDegree * m ≤ f.natDegree * 1 := by omega
      have := Nat.le_of_mul_le_mul_left this hn
      omega
  subst hm1
  rw [mul_one] at key'
  refine ⟨key'.symm, by omega, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
  have : Associated ϖ α := by
    rw [← addVal_eq_iff_associated, addVal_uniformizer hϖ, hm, Nat.cast_one]
  exact this.irreducible hϖ

variable (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hn hα

section Generated

variable (hgen : K⟮α⟯ = ⊤)
include hgen

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L] hn in

theorem finrank_le_of_isEisensteinAt : Module.finrank K L ≤ f.natDegree := by
  rw [← IntermediateField.finrank_top', ← hgen]
  exact finrank_adjoin_le_of_isEisensteinAt hf hα

theorem finrank_eq_natDegree_of_isEisensteinAt : Module.finrank K L = f.natDegree :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.1

theorem ramificationIndex_eq_natDegree_of_isEisensteinAt : ramificationIndex K L = f.natDegree :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).1

theorem irreducible_of_isEisensteinAt_root :
    Irreducible (⟨α, mem_integer_of_isEisensteinAt hf hα⟩ : 𝒪[L]) :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.2

end Generated

end Root

section AdjoinRoot

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]} (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)

include hf hα

include hn

end AdjoinRoot

section Converse

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ

theorem addVal_term_of_totallyRamified (g : 𝒪[K][X]) (i : ℕ) :
    (∀ k, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ k →
      ((Module.finrank K L * k + i : ℕ) : ℕ∞) ≤
        addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i)) ∧
    (IsUnit (g.coeff i) → addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) = i) := by
  have hval : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) =
      Module.finrank K L * addVal 𝒪[K] (g.coeff i) + i := by
    rw [addVal_mul, addVal_algebraMap_integer, h, hϖ.addVal_pow]
  refine ⟨fun k hk => ?_, fun hu => ?_⟩
  · rw [mem_maximalIdeal_pow_iff_le_addVal] at hk
    rw [hval]
    push_cast
    gcongr
  · rw [hval, addVal_eq_zero_iff.mpr hu, mul_zero, zero_add]

theorem minpoly_isEisensteinAt_of_irreducible :
    (minpoly 𝒪[K] (ϖ : L)).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      (minpoly 𝒪[K] (ϖ : L)).natDegree = Module.finrank K L := by
  set g := minpoly 𝒪[K] (ϖ : L) with hg_def
  set n := Module.finrank K L with hn_def
  have hint : IsIntegral 𝒪[K] (ϖ : L) := (isIntegral_iff K L _).mpr ϖ.2
  have hmon : g.Monic := minpoly.monic hint
  set d := g.natDegree with hd_def
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hmap : minpoly K (ϖ : L) = g.map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hint
  have hdn : d ≤ n := by
    have := minpoly.natDegree_le (A := K) (ϖ : L)
    rwa [hmap, hmon.natDegree_map] at this
  have hn0 : 0 < n := Module.finrank_pos
  have hroot : aeval ϖ g = 0 := by
    have := aeval_integer_eq_zero (f := g) ϖ.2 (minpoly.aeval 𝒪[K] (ϖ : L))
    simpa using this
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i with ht
  have hsum : ∑ i ∈ Finset.range (d + 1), t i = 0 := by
    rw [← hroot, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, d]
  have hterm := addVal_term_of_totallyRamified h hϖ g
  have hne : ∀ i, IsUnit (g.coeff i) → t i ≠ 0 := by
    intro i hu h0
    have := (hterm i).2 hu
    simp only [t] at h0
    rw [h0, addVal_zero] at this
    exact ENat.top_ne_natCast _ this
  have hlow : ∀ i, ((i : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i
    have := (hterm i).1 0 (by simp)
    rw [mul_zero, zero_add] at this
    exact this

  have hmem : ∀ i < d, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    by_contra hcon
    push Not at hcon
    have hex : ∃ j, j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := hcon
    classical
    let j := Nat.find hex
    have hj : j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := Nat.find_spec hex
    have hu : IsUnit (g.coeff j) := IsLocalRing.notMem_maximalIdeal.mp hj.2
    refine hne j hu (eq_zero_of_addVal_lt_of_sum_eq_zero hsum
      (Finset.mem_range.mpr (by omega)) fun i hi hij => ?_)
    rw [(hterm j).2 hu]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi' : g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
        by_contra hc
        exact Nat.find_min hex hlt ⟨by omega, hc⟩
      have := (hterm i).1 1 (by rwa [pow_one])
      refine lt_of_lt_of_le ?_ this
      exact_mod_cast (by omega : j < n * 1 + i)
    · exact lt_of_lt_of_le (by exact_mod_cast hgt) (hlow i)
  have htop : t d = ϖ ^ d := by
    simp only [t]
    rw [show g.coeff d = 1 from hmon]
    simp
  have htop_val : addVal 𝒪[L] (t d) = d := by rw [htop, hϖ.addVal_pow]
  have htop_ne : t d ≠ 0 := by
    rw [htop]
    exact pow_ne_zero _ hϖ.ne_zero

  have hmid : ∀ i, 0 < i → i < d → ((n + 1 : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi0 hid
    have := (hterm i).1 1 (by rw [pow_one]; exact hmem i hid)
    refine le_trans ?_ this
    exact_mod_cast (by omega : n + 1 ≤ n * 1 + i)

  have hsq : g.coeff 0 ∉ IsLocalRing.maximalIdeal 𝒪[K] ^ 2 := by
    intro hc
    refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
      fun i hi hid => ?_)
    have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
    rw [htop_val]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine lt_of_lt_of_le ?_ ((hterm 0).1 2 hc)
      exact_mod_cast (by omega : d < n * 2 + 0)
    · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')
  have Heisenberg₂ : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) :=
    { leading := by
        rw [hmon.leadingCoeff]
        exact fun h1 => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
      mem := fun hi => hmem _ hi
      notMem := hsq }
  refine ⟨Heisenberg₂, le_antisymm hdn ?_⟩

  by_contra hlt
  rw [not_le] at hlt
  have h0val : addVal 𝒪[L] (t 0) = n := by
    simp only [t]
    rw [addVal_mul, addVal_algebraMap_integer, h,
      addVal_eq_one_of_mem_of_notMem_sq (hmem 0 hd0) hsq]
    simp
  refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
    fun i hi hid => ?_)
  have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
  rw [htop_val]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [h0val]
    exact_mod_cast hlt
  · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')

omit h hϖ in
theorem minpoly_eq_map_of_irreducible :
    minpoly K (ϖ : L) = (minpoly 𝒪[K] (ϖ : L)).map (algebraMap 𝒪[K] K) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' K ((isIntegral_iff K L _).mpr ϖ.2)

theorem adjoin_eq_top_of_irreducible : K⟮(ϖ : L)⟯ = ⊤ := by
  have hint : IsIntegral K (ϖ : L) := ((isIntegral_iff K L _).mpr ϖ.2).tower_top
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, minpoly_eq_map_of_irreducible,
    (minpoly.monic ((isIntegral_iff K L _).mpr ϖ.2)).natDegree_map]
  exact (minpoly_isEisensteinAt_of_irreducible h hϖ).2

end Converse

end Sec_Eisenstein


/-! ### ExtensionsOfDegree -/
section Sec_ExtensionsOfDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000


open Polynomial _root_.IntermediateField ValuativeRel


section Normed

variable {L : Type*} [NontriviallyNormedField L]

theorem norm_le_one_of_aeval_eq_zero {C : Type*} [NormedField C] [IsUltrametricDist C]
    [NormedAlgebra L C] {g : L[X]} (hg : g.Monic) (hc : ∀ i, ‖g.coeff i‖ ≤ 1) {x : C}
    (hx : aeval x g = 0) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  set e := g.natDegree
  have hsum : aeval x g = x ^ e + ∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hg.coeff_natDegree, one_smul, add_comm]
    simp only [Algebra.smul_def]
    rfl
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h
    linarith
  have h1 : ‖∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i‖ < ‖x ^ e‖ := by
    rcases (Finset.range e).eq_empty_or_nonempty with he | he
    · rw [he, Finset.sum_empty, norm_zero, norm_pow]
      exact pow_pos (norm_pos_iff.2 hx0) _
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty he
        (fun i ↦ algebraMap L C (g.coeff i) * x ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_algebraMap', norm_pow, norm_pow]
      calc ‖g.coeff i‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr
            exact hc i
        _ < ‖x‖ ^ e := by
            rw [one_mul]
            exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have h2 : x ^ e = -∑ i ∈ Finset.range e, algebraMap L C (g.coeff i) * x ^ i := by
    rw [hsum] at hx
    exact eq_neg_of_add_eq_zero_left hx
  rw [h2, norm_neg] at h1
  exact lt_irrefl _ h1

variable [CompleteSpace L] [IsUltrametricDist L]

theorem exists_adjoin_eq_of_norm_coeff_sub_lt (f : L[X]) (hm : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) (Ω' : Type*) [Field Ω'] [Algebra L Ω'] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : L[X], g.Monic → g.natDegree = f.natDegree → (∀ i, ‖g.coeff i‖ ≤ 1) →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → ∀ β : Ω', aeval β g = 0 →
        ∃ α : Ω', aeval α f = 0 ∧ L⟮α⟯ = L⟮β⟯ := by
  classical
  let C := AlgebraicClosure L
  let : NontriviallyNormedField C := spectralNorm.nontriviallyNormedField L C
  let : NormedAlgebra L C := spectralNorm.normedAlgebra L C
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra L
  set R : Finset C := (f.map (algebraMap L C)).roots.toFinset with hR
  set D : Finset ℝ := ((R ×ˢ R).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ ‖p.1 - p.2‖) with hD
  set r : ℝ := if h : D.Nonempty then D.min' h else 1 with hr_def
  have hDpos : ∀ d ∈ D, 0 < d := by
    intro d hd
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hd
    exact norm_pos_iff.2 (sub_ne_zero.2 (Finset.mem_filter.1 hab).2)
  have hr : 0 < r := by
    rw [hr_def]
    split_ifs with h
    · exact hDpos _ (D.min'_mem h)
    · exact one_pos
  have hrle : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → r ≤ ‖a - b‖ := by
    intro a ha b hb hab
    have hmem : ‖a - b‖ ∈ D :=
      Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩
    rw [hr_def, dif_pos ⟨_, hmem⟩]
    exact D.min'_le _ hmem
  refine ⟨r ^ f.natDegree, pow_pos hr _, ?_⟩
  intro g hgm hdeg hgc hclose β hβ
  have hβint : IsIntegral L β := ⟨g, hgm, by rwa [← aeval_def]⟩
  have : FiniteDimensional L L⟮β⟯ := adjoin.finiteDimensional hβint
  let ψ : L⟮β⟯ →ₐ[L] C := IsAlgClosed.lift
  set β' : C := ψ (AdjoinSimple.gen L β) with hβ'_def
  have hgen : aeval (AdjoinSimple.gen L β) g = 0 := by
    apply (algebraMap L⟮β⟯ Ω').injective
    rw [← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, hβ,
      map_zero]
  have hβ' : aeval β' g = 0 := by
    rw [hβ'_def, aeval_algHom_apply, hgen, map_zero]
  have hnorm : ‖β'‖ ≤ 1 := norm_le_one_of_aeval_eq_zero hgm hgc hβ'

  have hsmall : ‖aeval β' f‖ < r ^ f.natDegree := by
    have hfg : aeval β' f = aeval β' (f - g) := by rw [map_sub, hβ', sub_zero]
    have hdeg' : (f - g).natDegree < f.natDegree + 1 :=
      Nat.lt_succ_of_le ((natDegree_sub_le f g).trans (by rw [hdeg, max_self]))
    rw [hfg, aeval_eq_sum_range' hdeg']
    obtain ⟨i, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun i ↦ (f - g).coeff i • β' ^ i)
    refine hle.trans_lt ?_
    rw [Algebra.smul_def, norm_mul, norm_algebraMap', norm_pow, coeff_sub, norm_sub_rev]
    calc ‖g.coeff i - f.coeff i‖ * ‖β'‖ ^ i ≤ ‖g.coeff i - f.coeff i‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hnorm
      _ < r ^ f.natDegree := by rw [mul_one]; exact hclose i

  have hsplit : (f.map (algebraMap L C)).Splits := IsAlgClosed.splits _
  have hnodup : (f.map (algebraMap L C)).roots.Nodup := nodup_roots (hsep.map)
  have hcard : R.card = f.natDegree := by
    rw [hR, Multiset.toFinset_card_of_nodup hnodup, ← hsplit.natDegree_eq_card_roots,
      natDegree_map]
  have heval : aeval β' f = ∏ a ∈ R, (β' - a) := by
    rw [aeval_def, eval₂_eq_eval_map, hsplit.eval_eq_prod_roots_of_monic (hm.map _), hR,
      Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnodup.dedup]
  obtain ⟨a, haR, ha⟩ : ∃ a ∈ R, ‖β' - a‖ < r := by
    by_contra hcon
    push Not at hcon
    have : r ^ f.natDegree ≤ ‖aeval β' f‖ := by
      rw [heval, norm_prod, ← hcard, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ ↦ hr.le) hcon
    exact absurd hsmall (not_lt.2 this)
  have hfC : f.map (algebraMap L C) ≠ 0 := (hm.map _).ne_zero
  have haroot : aeval a f = 0 := by
    have := (mem_roots hfC).1 (Multiset.mem_toFinset.1 haR)
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : minpoly L a = f := (minpoly.eq_of_irreducible_of_monic hirr haroot hm).symm

  have hkr : a ∈ L⟮β'⟯ := by
    refine IsKrasner.krasner (by rw [hmin]; exact hsep) (by rw [hmin]; exact IsAlgClosed.splits _)
      (Algebra.IsIntegral.isIntegral β') (fun x' hx' hne ↦ ?_)
    have hx'root : aeval x' f = 0 := by
      rw [← hmin, isConjRoot_def.1 hx']
      exact minpoly.aeval L x'
    have hx'R : x' ∈ R := by
      rw [hR, Multiset.mem_toFinset, mem_roots hfC, IsRoot, eval_map_algebraMap]
      exact hx'root
    rw [norm_sub_rev]
    exact ha.trans_le (hrle a haR x' hx'R hne)

  have hrange : L⟮β'⟯ ≤ ψ.fieldRange := adjoin_simple_le_iff.2 (AlgHom.mem_fieldRange.2 ⟨_, rfl⟩)
  obtain ⟨y, hy⟩ := AlgHom.mem_fieldRange.1 (hrange hkr)
  have hy0 : aeval y f = 0 := by
    have h' : ψ (aeval y f) = 0 := by rw [← aeval_algHom_apply, hy, haroot]
    simpa using h'
  have hα : aeval (y : Ω') f = 0 := by
    have := aeval_algebraMap_apply Ω' y f
    rw [hy0, map_zero] at this
    exact this
  refine ⟨(y : Ω'), hα, ?_⟩
  have hαint : IsIntegral L (y : Ω') := ⟨f, hm, by rwa [← aeval_def]⟩
  refine eq_of_le_of_finrank_le (adjoin_simple_le_iff.2 y.2) ?_
  rw [adjoin.finrank hβint, adjoin.finrank hαint,
    ← minpoly.eq_of_irreducible_of_monic hirr hα hm, ← hdeg]
  exact natDegree_le_natDegree (minpoly.degree_le_of_ne_zero L β hgm.ne_zero hβ)

end Normed

section MonicOfCoeffs

variable {R : Type*} [CommRing R]

def monicOfCoeffs {n : ℕ} (c : Fin n → R) : R[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

theorem coeff_sum_fin_C_mul_X_pow {n : ℕ} (c : Fin n → R) (k : ℕ) :
    (∑ i : Fin n, C (c i) * X ^ (i : ℕ)).coeff k = if h : k < n then c ⟨k, h⟩ else 0 := by
  classical
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k, h⟩ (fun j _ hj ↦ if_neg fun hk ↦ hj (Fin.ext hk.symm))
      (fun h' ↦ absurd (Finset.mem_univ _) h'), if_pos rfl]
  · exact Finset.sum_eq_zero fun j _ ↦ if_neg fun (hk : k = (j : ℕ)) ↦ h (hk ▸ j.2)

theorem monic_monicOfCoeffs {n : ℕ} (c : Fin n → R) : (monicOfCoeffs c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

theorem natDegree_monicOfCoeffs [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (monicOfCoeffs c).natDegree = n := by
  rw [monicOfCoeffs, natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt c),
    natDegree_X_pow]

theorem eq_monicOfCoeffs {g : R[X]} (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n) :
    g = monicOfCoeffs (fun i : Fin n ↦ g.coeff i) := by
  conv_lhs => rw [hg.as_sum, hn]
  rw [monicOfCoeffs, Fin.sum_univ_eq_sum_range (fun i ↦ C (g.coeff i) * X ^ i) n]

theorem monicOfCoeffs_sub_monicOfCoeffs {n : ℕ} (c d : Fin n → R) :
    monicOfCoeffs c - monicOfCoeffs d = ∑ i : Fin n, C (c i - d i) * X ^ (i : ℕ) := by
  rw [monicOfCoeffs, monicOfCoeffs, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  simp only [C_sub, sub_mul]

end MonicOfCoeffs

section Eisenstein

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

end Eisenstein

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Valued

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

end Valued

variable (Ω : Type*) [Field Ω] [Algebra K Ω]

end Main

end Sec_ExtensionsOfDegree


/-! ### Ramification -/
section Sec_Ramification

open ValuativeRel IsLocalRing

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Action

variable {K L}

theorem integerAlgEquiv_mem_maximalIdeal_pow_iff (σ : L ≃ₐ[K] L) (n : ℕ) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x ∈ 𝓂[L] ^ n ↔ x ∈ 𝓂[L] ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hσϖ : Irreducible (integerAlgEquiv K L σ ϖ) :=
    (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ
  rw [mem_maximalIdeal_pow_iff hσϖ, mem_maximalIdeal_pow_iff hϖ, ← map_pow,
    map_dvd_iff (integerAlgEquiv K L σ)]

theorem algEquiv_eq_one_of_forall_integer {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝒪[L], integerAlgEquiv K L σ x = x) : σ = 1 := by
  ext y
  rw [AlgEquiv.one_apply]
  by_cases hy : valuation L y ≤ 1
  · exact congrArg Subtype.val (h ⟨y, hy⟩)
  · have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have hinv : valuation L y⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hy))
    have := congrArg Subtype.val (h ⟨y⁻¹, hinv⟩)
    simp only [coe_integerAlgEquiv_apply, map_inv₀] at this
    exact inv_injective this

end Action

def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {σ | ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat}
  one_mem' x := by simp
  mul_mem' {σ τ} hσ hτ x := by
    have h : integerAlgEquiv K L (σ * τ) x - x =
        (integerAlgEquiv K L σ (integerAlgEquiv K L τ x) - integerAlgEquiv K L τ x) +
          (integerAlgEquiv K L τ x - x) := by
      rw [map_mul, AlgEquiv.mul_apply]; ring
    rw [h]
    exact add_mem (hσ _) (hτ x)
  inv_mem' {σ} hσ x := by
    have h := hσ (integerAlgEquiv K L σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply] at h
    rw [← neg_sub]
    exact neg_mem h

variable {K L}

theorem mem_lowerRamificationGroup_iff {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (i + 1).toNat :=
  Iff.rfl

theorem mem_lowerRamificationGroup_natCast_iff {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L n ↔
      ∀ x : 𝒪[L], integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ (n + 1) := by
  rw [mem_lowerRamificationGroup_iff]
  have : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [this]

variable (K L)

theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) := by
  intro i j hij σ hσ x
  exact Ideal.pow_le_pow_right (by omega) (hσ x)

theorem lowerRamificationGroup_eq_top {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by
  refine eq_top_iff.mpr fun σ _ x ↦ ?_
  have : (i + 1).toNat = 0 := by omega
  rw [this, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

instance lowerRamificationGroup_normal (i : ℤ) : (lowerRamificationGroup K L i).Normal where
  conj_mem σ hσ τ x := by
    set y := integerAlgEquiv K L τ⁻¹ x
    have hx : x = integerAlgEquiv K L τ y := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    have h : integerAlgEquiv K L (τ * σ * τ⁻¹) x - x =
        integerAlgEquiv K L τ (integerAlgEquiv K L σ y - y) := by
      rw [map_sub, map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hx]
    rw [h, integerAlgEquiv_mem_maximalIdeal_pow_iff]
    exact hσ y

variable {K L}

theorem mem_maximalIdeal_pow_iff_normalizedValuation (n : ℕ) (y : 𝒪[L]) :
    y ∈ 𝓂[L] ^ n ↔ normalizedValuation L (y : L) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hv : normalizedValuation L ((ϖ ^ n : 𝒪[L]) : L) = WithZero.exp (-(n : ℤ)) := by
    rw [SubmonoidClass.coe_pow, map_pow, normalizedValuation_uniformizer hϖ, ← WithZero.exp_nsmul]
    simp
  rw [mem_maximalIdeal_pow_iff hϖ, (Valuation.integer.integers (valuation L)).dvd_iff_le, ← hv,
    normalizedValuation_le_iff]
  rfl

theorem mem_lowerRamificationGroup_iff_valuation {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x ∈ 𝒪[L], normalizedValuation L (σ x - x) ≤ WithZero.exp (-(i + 1)) := by
  rw [mem_lowerRamificationGroup_iff]
  refine ⟨fun h x hx ↦ ?_, fun h x ↦ ?_⟩
  · have := (mem_maximalIdeal_pow_iff_normalizedValuation _ _).mp (h ⟨x, hx⟩)
    have hc : ((integerAlgEquiv K L σ ⟨x, hx⟩ - ⟨x, hx⟩ : 𝒪[L]) : L) = σ x - x := rfl
    rw [hc] at this
    refine this.trans ?_
    rw [WithZero.exp_le_exp]
    omega
  · rcases le_or_gt (i + 1) 0 with hi | hi
    · have : (i + 1).toNat = 0 := by omega
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · rw [mem_maximalIdeal_pow_iff_normalizedValuation]
      have h' := h x x.2
      have he : ((i + 1).toNat : ℤ) = i + 1 := by omega
      rw [he]
      simpa using h'

variable (K L)

theorem lowerRamificationGroup_zero : lowerRamificationGroup K L 0 = (residueAlgEquiv K L).ker := by
  ext σ
  rw [MonoidHom.mem_ker, AlgEquiv.ext_iff]
  have : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [mem_lowerRamificationGroup_iff, this, pow_one]
  refine ⟨fun h r ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := residue_surjective r
    rw [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff]
    exact h x
  · have := h (residue 𝒪[L] x)
    rwa [residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff] at this

theorem residue_integerAlgEquiv_of_mem_zero {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (x : 𝒪[L]) : residue 𝒪[L] (integerAlgEquiv K L σ x) = residue 𝒪[L] x := by
  rw [lowerRamificationGroup_zero, MonoidHom.mem_ker] at hσ
  rw [← residueAlgEquiv_residue, hσ, AlgEquiv.one_apply]

theorem exists_lowerRamificationGroup_eq_bot :
    ∃ n : ℕ, ∀ i : ℤ, n ≤ i → lowerRamificationGroup K L i = ⊥ := by
  have key : ∀ σ : L ≃ₐ[K] L, ∃ m : ℕ, σ ≠ 1 → σ ∉ lowerRamificationGroup K L m := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h ↦ (h hσ).elim⟩
    obtain ⟨x, hx⟩ : ∃ x : 𝒪[L], integerAlgEquiv K L σ x ≠ x := by
      by_contra! h
      exact hσ (algEquiv_eq_one_of_forall_integer h)
    have hd : integerAlgEquiv K L σ x - x ≠ 0 := sub_ne_zero.mpr hx
    have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (𝓂[L]) (Ideal.IsPrime.ne_top')
    obtain ⟨m, hm⟩ : ∃ m : ℕ, integerAlgEquiv K L σ x - x ∉ 𝓂[L] ^ m := by
      by_contra! h
      exact hd (by
        have : integerAlgEquiv K L σ x - x ∈ ⨅ m : ℕ, 𝓂[L] ^ m := Submodule.mem_iInf _ |>.mpr h
        rwa [hinf, Ideal.mem_bot] at this)
    refine ⟨m, fun _ hmem ↦ hm ?_⟩
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (mem_lowerRamificationGroup_natCast_iff.mp hmem x)
  choose f hf using key
  obtain ⟨N, hN⟩ := Finite.exists_le f
  refine ⟨N, fun i hi ↦ eq_bot_iff.mpr fun σ hσ ↦ ?_⟩
  by_contra h
  exact hf σ h (lowerRamificationGroup_antitone K L (by have := hN σ; omega) hσ)

end Sec_Ramification


/-! ### RamificationUnits -/
section Sec_RamificationUnits

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Inertia

theorem integerAlgEquiv_teichmuller {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    (ζ : 𝓀[L]ˣ) :
    integerAlgEquiv K L σ (teichmuller L ζ : 𝒪[L]) = teichmuller L ζ := by
  have hres : unitsToResidue L (Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L])
      (teichmuller L ζ)) = unitsToResidue L (teichmuller L ζ) := by
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L hσ _
  have hpow : Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (teichmuller L ζ) ^
      (Nat.card 𝓀[L] - 1) = 1 := by
    rw [← map_pow, teichmuller_pow_card_sub_one, map_one]
  exact congrArg Units.val (eq_of_pow_card_sub_one hpow (teichmuller_pow_card_sub_one ζ) hres)

theorem sub_mem_of_uniformizer {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) {n : ℕ}
    (h : integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ n) (x : 𝒪[L]) :
    integerAlgEquiv K L σ x - x ∈ 𝓂[L] ^ n := by
  set e := integerAlgEquiv K L σ
  let P : 𝒪[L] → Prop := fun y ↦ e y - y ∈ 𝓂[L] ^ n
  have hadd : ∀ a b, P a → P b → P (a + b) := fun a b ha hb ↦ by
    have : e (a + b) - (a + b) = (e a - a) + (e b - b) := by rw [map_add]; ring
    simp only [P, this]
    exact add_mem ha hb
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb ↦ by
    have : e (a * b) - a * b = e a * (e b - b) + (e a - a) * b := by rw [map_mul]; ring
    simp only [P, this]
    exact add_mem (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
  have hpow : ∀ a (k : ℕ), P a → P (a ^ k) := by
    intro a k ha
    induction k with
    | zero => simp [P]
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih ha
  have hfix : ∀ a, e a = a → P a := fun a ha ↦ by simp [P, ha]
  have hideal : ∀ y ∈ 𝓂[L] ^ n, P y := fun y hy ↦
    sub_mem ((integerAlgEquiv_mem_maximalIdeal_pow_iff σ n y).mpr hy) hy
  have happrox : ∀ y : 𝒪[L], ∃ t, e t = t ∧ y - t ∈ 𝓂[L] := by
    intro y
    by_cases hy : residue 𝒪[L] y = 0
    · exact ⟨0, map_zero e, by simpa using (residue_eq_zero_iff y).mp hy⟩
    · refine ⟨teichmuller L (Units.mk0 _ hy), integerAlgEquiv_teichmuller hσ _, ?_⟩
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrArg Units.val (unitsToResidue_teichmuller (K := L) (Units.mk0 _ hy))).symm
  have hstep : ∀ m : ℕ, ∃ r, P r ∧ x - r ∈ 𝓂[L] ^ m := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp [P], by simp⟩
    | succ m ih =>
      obtain ⟨r, hr, hxr⟩ := ih
      obtain ⟨y, hy⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hxr
      obtain ⟨t, ht, hyt⟩ := happrox y
      obtain ⟨z, hz⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hyt
      refine ⟨r + ϖ ^ m * t, hadd _ _ hr (hmul _ _ (hpow _ _ h) (hfix _ ht)), ?_⟩
      rw [mem_maximalIdeal_pow_iff hϖ]
      exact ⟨z, by rw [pow_succ]; linear_combination hy + ϖ ^ m * hz⟩
  obtain ⟨r, hr, hxr⟩ := hstep n
  have : x = r + (x - r) := by ring
  rw [this]
  exact hadd _ _ hr (hideal _ hxr)

theorem mem_lowerRamificationGroup_iff_uniformizer {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ integerAlgEquiv K L σ ϖ - ϖ ∈ 𝓂[L] ^ (n + 1) :=
  ⟨fun h ↦ mem_lowerRamificationGroup_natCast_iff.mp h ϖ,
    fun h ↦ mem_lowerRamificationGroup_natCast_iff.mpr (sub_mem_of_uniformizer hσ hϖ h)⟩

end Inertia

section Ratio

theorem irreducible_integerAlgEquiv (σ : L ≃ₐ[K] L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Irreducible (integerAlgEquiv K L σ ϖ) :=
  (MulEquiv.irreducible_iff (f := (integerAlgEquiv K L σ : 𝒪[L] ≃* 𝒪[L]))).mpr hϖ

def uniformizerRatio {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (σ : L ≃ₐ[K] L) : 𝒪[L]ˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

theorem mul_uniformizerRatio (σ : L ≃ₐ[K] L) :
    ϖ * uniformizerRatio hϖ σ = integerAlgEquiv K L σ ϖ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[L] hϖ
    (irreducible_integerAlgEquiv σ hϖ)).choose_spec

theorem uniformizerRatio_eq_iff (σ : L ≃ₐ[K] L) (u : 𝒪[L]ˣ) :
    uniformizerRatio hϖ σ = u ↔ ϖ * u = integerAlgEquiv K L σ ϖ := by
  refine ⟨fun h ↦ h ▸ mul_uniformizerRatio hϖ σ, fun h ↦ Units.ext ?_⟩
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans h.symm)

@[simp]
theorem uniformizerRatio_one : uniformizerRatio hϖ (1 : L ≃ₐ[K] L) = 1 := by
  rw [uniformizerRatio_eq_iff, map_one, AlgEquiv.one_apply, Units.val_one, mul_one]

theorem uniformizerRatio_mul (σ τ : L ≃ₐ[K] L) :
    uniformizerRatio hϖ (σ * τ) = uniformizerRatio hϖ σ *
      Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) (uniformizerRatio hϖ τ) := by
  rw [uniformizerRatio_eq_iff, map_mul, AlgEquiv.mul_apply, ← mul_uniformizerRatio hϖ τ, map_mul,
    ← mul_uniformizerRatio hϖ σ, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, mul_assoc]

theorem mem_lowerRamificationGroup_iff_uniformizerRatio {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L 0) (n : ℕ) :
    σ ∈ lowerRamificationGroup K L n ↔ uniformizerRatio hϖ σ ∈ unitFiltration L n := by
  rw [mem_lowerRamificationGroup_iff_uniformizer hσ hϖ, mem_unitFiltration,
    ← mul_uniformizerRatio hϖ σ, mem_maximalIdeal_pow_iff hϖ, mem_maximalIdeal_pow_iff hϖ,
    show ϖ * (uniformizerRatio hϖ σ : 𝒪[L]) - ϖ = ϖ * ((uniformizerRatio hϖ σ : 𝒪[L]) - 1) by ring,
    pow_succ', mul_dvd_mul_iff_left hϖ.ne_zero]

theorem uniformizerRatio_mem {n : ℕ} (σ : lowerRamificationGroup K L n) :
    uniformizerRatio hϖ (σ : L ≃ₐ[K] L) ∈ unitFiltration L n :=
  (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ
    (lowerRamificationGroup_antitone K L (by omega) σ.2) n).mp σ.2

omit hϖ in

theorem map_mul_inv_mem {n : ℕ} {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L n)
    (u : 𝒪[L]ˣ) :
    Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ ∈ unitFiltration L (n + 1) := by
  rw [mem_unitFiltration]
  have h : ((Units.map (integerAlgEquiv K L σ : 𝒪[L] →* 𝒪[L]) u * u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 =
      (integerAlgEquiv K L σ u - u) * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) := by
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, sub_mul, Units.mul_inv]
  rw [h]
  exact Ideal.mul_mem_right _ _ (mem_lowerRamificationGroup_natCast_iff.mp hσ (u : 𝒪[L]))

omit hϖ in

abbrev unitFiltrationSucc (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (n : ℕ) : Subgroup (unitFiltration L n) :=
  (unitFiltration L (n + 1)).subgroupOf (unitFiltration L n)

def ramificationToUnits (n : ℕ) :
    lowerRamificationGroup K L n →* unitFiltration L n ⧸ unitFiltrationSucc L n where
  toFun σ := QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩
  map_one' := by
    have : (⟨uniformizerRatio hϖ ((1 : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
      uniformizerRatio_mem hϖ 1⟩ : unitFiltration L n) = 1 := Subtype.ext (uniformizerRatio_one hϖ)
    rw [this, QuotientGroup.mk_one]
  map_mul' σ τ := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := map_mul_inv_mem σ.2 (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))
    have key : (((⟨uniformizerRatio hϖ ((σ * τ : lowerRamificationGroup K L n) : L ≃ₐ[K] L),
        uniformizerRatio_mem hϖ (σ * τ)⟩ : unitFiltration L n)⁻¹ *
        (⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ *
          ⟨uniformizerRatio hϖ (τ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ τ⟩) : unitFiltration L n) : 𝒪[L]ˣ) =
        (Units.map (integerAlgEquiv K L (σ : L ≃ₐ[K] L) : 𝒪[L] →* 𝒪[L])
          (uniformizerRatio hϖ (τ : L ≃ₐ[K] L)) * (uniformizerRatio hϖ (τ : L ≃ₐ[K] L))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, uniformizerRatio_mul]
      group
      exact mul_comm _ _
    rw [key]
    exact inv_mem h

theorem ramificationToUnits_apply (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationToUnits hϖ n σ =
      QuotientGroup.mk ⟨uniformizerRatio hϖ (σ : L ≃ₐ[K] L), uniformizerRatio_mem hϖ σ⟩ :=
  rfl

theorem ker_ramificationToUnits (n : ℕ) :
    (ramificationToUnits hϖ n).ker =
      (lowerRamificationGroup K L (n + 1 : ℕ)).subgroupOf (lowerRamificationGroup K L n) := by
  ext σ
  have hσ0 : (σ : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 :=
    lowerRamificationGroup_antitone K L (by omega) σ.2
  rw [MonoidHom.mem_ker, ramificationToUnits_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_lowerRamificationGroup_iff_uniformizerRatio hϖ hσ0]

def ramificationQuotientToUnits (n : ℕ) :
    lowerRamificationGroup K L n ⧸
        (lowerRamificationGroup K L (n + 1 : ℕ)).subgroupOf (lowerRamificationGroup K L n) →*
      unitFiltration L n ⧸ unitFiltrationSucc L n :=
  (QuotientGroup.kerLift (ramificationToUnits hϖ n)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_ramificationToUnits hϖ n).symm).toMonoidHom

@[simp]
theorem ramificationQuotientToUnits_mk (n : ℕ) (σ : lowerRamificationGroup K L n) :
    ramificationQuotientToUnits hϖ n (QuotientGroup.mk σ) = ramificationToUnits hϖ n σ :=
  rfl

end Ratio

end Sec_RamificationUnits


/-! ### RamificationStructure -/
section Sec_RamificationStructure

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

section Tame

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

def inertiaToResidueUnits : lowerRamificationGroup K L 0 →* 𝓀[L]ˣ where
  toFun σ := unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L))
  map_one' := by simp
  map_mul' σ τ := by
    rw [Subgroup.coe_mul, uniformizerRatio_mul, map_mul]
    congr 1
    ext
    exact residue_integerAlgEquiv_of_mem_zero K L σ.2 _

theorem inertiaToResidueUnits_apply (σ : lowerRamificationGroup K L 0) :
    inertiaToResidueUnits hϖ σ = unitsToResidue L (uniformizerRatio hϖ (σ : L ≃ₐ[K] L)) :=
  rfl

theorem ker_inertiaToResidueUnits :
    (inertiaToResidueUnits hϖ).ker =
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, inertiaToResidueUnits_apply,
    ← MonoidHom.mem_ker, ker_unitsToResidue]
  exact (mem_lowerRamificationGroup_iff_uniformizerRatio hϖ σ.2 1).symm

def inertiaQuotientToResidueUnits :
    lowerRamificationGroup K L 0 ⧸
        (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0) →* 𝓀[L]ˣ :=
  (QuotientGroup.kerLift (inertiaToResidueUnits hϖ)).comp
    (QuotientGroup.quotientMulEquivOfEq (ker_inertiaToResidueUnits hϖ).symm).toMonoidHom

theorem inertiaQuotientToResidueUnits_injective :
    Function.Injective (inertiaQuotientToResidueUnits (K := K) hϖ) :=
  fun _ _ hab ↦ (MulEquiv.injective _) (QuotientGroup.kerLift_injective (inertiaToResidueUnits hϖ) hab)

omit hϖ

variable (K L)

theorem isCyclic_lowerRamificationGroup_zero_quotient :
    IsCyclic (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  exact isCyclic_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

theorem card_lowerRamificationGroup_zero_quotient_dvd :
    Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0)) ∣
        Nat.card 𝓀[L] - 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rw [← Nat.card_units 𝓀[L]]
  exact Subgroup.card_dvd_of_injective _ (inertiaQuotientToResidueUnits_injective hϖ)

variable {K L}

theorem coprime_card_residueField_sub_one : Nat.Coprime (Nat.card 𝓀[L] - 1) (ringChar 𝓀[L]) := by
  let := Fintype.ofFinite 𝓀[L]
  have hq : ringChar 𝓀[L] ∣ Nat.card 𝓀[L] := by
    rw [← CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have h1 : 1 ≤ Nat.card 𝓀[L] := Nat.card_pos
  refine Nat.Coprime.symm (Nat.dvd_one.mp ?_)
  have ha := Nat.gcd_dvd_left (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have hb := Nat.gcd_dvd_right (ringChar 𝓀[L]) (Nat.card 𝓀[L] - 1)
  have := Nat.dvd_sub (ha.trans hq) hb
  rwa [Nat.sub_sub_self h1] at this

variable (K L)

theorem coprime_card_lowerRamificationGroup_zero_quotient :
    Nat.Coprime (Nat.card (lowerRamificationGroup K L 0 ⧸
      (lowerRamificationGroup K L 1).subgroupOf (lowerRamificationGroup K L 0))) (ringChar 𝓀[K]) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  exact Nat.Coprime.coprime_dvd_left (card_lowerRamificationGroup_zero_quotient_dvd K L)
    coprime_card_residueField_sub_one

end Tame

section Wild

theorem pow_ringChar_eq_one_unitFiltration {n : ℕ} (hn : 1 ≤ n)
    (y : unitFiltration L n ⧸ unitFiltrationSucc L n) : y ^ ringChar 𝓀[L] = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  apply (unitFiltrationGradedEquiv hϖ hn).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]

theorem pow_ringChar_mem_lowerRamificationGroup {n : ℕ} (hn : 1 ≤ n) {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ lowerRamificationGroup K L n) :
    σ ^ ringChar 𝓀[L] ∈ lowerRamificationGroup K L (n + 1 : ℕ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have h : ((⟨σ, hσ⟩ : lowerRamificationGroup K L n) ^ ringChar 𝓀[L]) ∈
      (ramificationToUnits hϖ n).ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_ringChar_eq_one_unitFiltration hn]
  rw [ker_ramificationToUnits, Subgroup.mem_subgroupOf] at h
  simpa using h

variable (K L)

theorem isPGroup_lowerRamificationGroup_one :
    IsPGroup (ringChar 𝓀[K]) (lowerRamificationGroup K L 1) := by
  rw [Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot K L
  have key : ∀ k : ℕ, ∀ σ ∈ lowerRamificationGroup K L 1,
      σ ^ (ringChar 𝓀[L] ^ k) ∈ lowerRamificationGroup K L ((1 + k : ℕ) : ℤ) := by
    intro k σ hσ
    induction k with
    | zero => simpa using hσ
    | succ k ih =>
      rw [pow_succ, pow_mul, show 1 + (k + 1) = 1 + k + 1 by omega]
      exact pow_ringChar_mem_lowerRamificationGroup (by omega) ih
  intro σ
  refine ⟨N, Subtype.ext ?_⟩
  have := key N σ σ.2
  rw [hN _ (by omega), Subgroup.mem_bot] at this
  simpa using this

theorem isSolvable_lowerRamificationGroup_one : Group.IsSolvable (lowerRamificationGroup K L 1) := by
  have : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] _⟩
  have := (isPGroup_lowerRamificationGroup_one K L).isNilpotent
  infer_instance

theorem isSolvable_lowerRamificationGroup_zero : Group.IsSolvable (lowerRamificationGroup K L 0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have := isSolvable_lowerRamificationGroup_one K L
  refine Group.isSolvable_of_ker_le_range
    (Subgroup.inclusion (lowerRamificationGroup_antitone K L zero_le_one))
    (inertiaToResidueUnits hϖ) ?_
  intro σ hσ
  rw [ker_inertiaToResidueUnits, Subgroup.mem_subgroupOf] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

theorem isSolvable_algEquiv : Group.IsSolvable (L ≃ₐ[K] L) := by
  have := isSolvable_lowerRamificationGroup_zero K L
  have : Group.IsSolvable (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
    Group.isSolvable_of_comm fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  refine Group.isSolvable_of_ker_le_range (lowerRamificationGroup K L 0).subtype (residueAlgEquiv K L) ?_
  intro σ hσ
  rw [← lowerRamificationGroup_zero] at hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

end Wild

end Sec_RamificationStructure


/-! ### RamificationTame -/
section Sec_RamificationTame

open scoped _root_.IntermediateField


open ValuativeRel IsLocalRing IsDiscreteValuationRing

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem natCast_ramificationIndex_ne_zero
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    (ramificationIndex K L : 𝓀[L]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[L] (ringChar 𝓀[L]), ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro hdvd
  have h1 := Nat.Coprime.eq_one_of_dvd he.symm hdvd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))

theorem exists_pow_eq_uniformizer_of_residueDegree_eq_one (hf : residueDegree K L = 1)
    (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ π : 𝒪[K], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
      α ^ ramificationIndex K L = algebraMap 𝒪[K] 𝒪[L] π ∧ K⟮(α : L)⟯ = ⊤ := by
  set e := ramificationIndex K L with he_def
  obtain ⟨ϖK, hϖK⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]

  obtain ⟨u, hu⟩ : Associated (algebraMap 𝒪[K] 𝒪[L] ϖK) (ϖL ^ e) := by
    have h := map_maximalIdeal K L
    rw [hϖK.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    exact h

  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_maximalIdeal K L hf (u : 𝒪[L])
  have hcu : IsUnit c := by
    by_contra hn
    have hnL : ¬ IsUnit (algebraMap 𝒪[K] 𝒪[L] c) := fun h ↦ hn (isUnit_of_map_unit _ _ h)
    have hmem : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := (mem_maximalIdeal _).mpr hnL
    have : (u : 𝒪[L]) ∈ 𝓂[L] := by
      have := add_mem hc hmem
      rwa [sub_add_cancel] at this
    exact (mem_maximalIdeal _).mp this u.isUnit
  set c' := hcu.unit
  set cL : 𝒪[L]ˣ := Units.map (algebraMap 𝒪[K] 𝒪[L] : 𝒪[K] →* 𝒪[L]) c' with hcL
  have hcLval : (cL : 𝒪[L]) = algebraMap 𝒪[K] 𝒪[L] c := rfl

  have hv : u * cL⁻¹ ∈ unitFiltration L 1 := by
    rw [mem_unitFiltration, pow_one, Units.val_mul,
      show (u : 𝒪[L]) * ((cL⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 = ((u : 𝒪[L]) - cL) * ((cL⁻¹ : 𝒪[L]ˣ) : 𝒪[L])
        by rw [sub_mul, Units.mul_inv], hcLval]
    exact Ideal.mul_mem_right _ _ hc
  obtain ⟨w, hw⟩ := unitFiltration_one_le_range_pow (natCast_ramificationIndex_ne_zero K L he) hv
  have hw' : w ^ e = u * cL⁻¹ := hw
  have hinv : (w⁻¹) ^ e = cL * u⁻¹ := by rw [inv_pow, hw', mul_inv_rev, inv_inv]

  have htot : ramificationIndex K L = Module.finrank K L := by
    have := ramificationIndex_mul_residueDegree K L
    rwa [hf, mul_one] at this
  refine ⟨ϖK * (c' : 𝒪[K]), (irreducible_mul_isUnit c'.isUnit).mpr hϖK,
    ϖL * ((w⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (irreducible_mul_isUnit (w⁻¹).isUnit).mpr hϖL, ?_, ?_⟩
  · have hui := Units.mul_inv u
    calc (ϖL * ((w⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) ^ e = ϖL ^ e * (((w⁻¹) ^ e : 𝒪[L]ˣ) : 𝒪[L]) := by
          rw [mul_pow, Units.val_pow_eq_pow_val]
      _ = algebraMap 𝒪[K] 𝒪[L] ϖK * u * (cL * ((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L])) := by
          rw [← hu, hinv, Units.val_mul]
      _ = algebraMap 𝒪[K] 𝒪[L] (ϖK * (c' : 𝒪[K])) := by
          rw [map_mul, show algebraMap 𝒪[K] 𝒪[L] (c' : 𝒪[K]) = cL from rfl]
          linear_combination (algebraMap 𝒪[K] 𝒪[L] ϖK * cL) * hui
  · exact adjoin_eq_top_of_irreducible htot ((irreducible_mul_isUnit (w⁻¹).isUnit).mpr hϖL)

variable {K L}

theorem exists_pow_eq_uniformizer_of_isUnramified (T : IntermediateField K L) [IsUnramified K T]
    (hf : residueDegree T L = 1) (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ramificationIndex T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  have htow : ramificationIndex T L = ramificationIndex K L := by
    rw [ramificationIndex_tower K T L, IsUnramified.ramificationIndex_eq_one (K := K) (L := T), one_mul]
  have he' : Nat.Coprime (ramificationIndex T L) (ringChar 𝓀[T]) := by
    rw [htow, ← Algebra.ringChar_eq 𝓀[K] 𝓀[T]]
    exact he
  refine ⟨htow, ?_⟩
  rw [← htow]
  exact exists_pow_eq_uniformizer_of_residueDegree_eq_one T L hf he'

end Sec_RamificationTame


/-! ### RamificationTameStructure -/
section Sec_RamificationTameStructure

open scoped _root_.IntermediateField


open ValuativeRel

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_tame_structure (he : Nat.Coprime (ramificationIndex K L) (ringChar 𝓀[K])) :
    ∃ T : IntermediateField K L, IsUnramified K T ∧
      Module.finrank K T = residueDegree K L ∧ residueDegree T L = 1 ∧
      ramificationIndex T L = ramificationIndex K L ∧
      Module.finrank T L = ramificationIndex K L ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ ramificationIndex K L = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  obtain ⟨β, -, -, -, -, hun, hdeg, hres⟩ := exists_unramified_adjoin K L
  set T := K⟮(β : L)⟯
  obtain ⟨htow, hrest⟩ := exists_pow_eq_uniformizer_of_isUnramified T hres he
  have hfin : Module.finrank T L = ramificationIndex K L := by
    have := ramificationIndex_mul_residueDegree T L
    rw [hres, mul_one, htow] at this
    exact this.symm
  exact ⟨T, hun, hdeg, hres, htow, hfin, hrest⟩

end Sec_RamificationTameStructure


/-! ### TameExtension -/
section Sec_TameExtension

open Polynomial _root_.IntermediateField ValuativeRel


section Definition

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]

def IsTameSubextension (E : IntermediateField K Ω) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K])

theorem isTameSubextension_iff_exists (E : IntermediateField K Ω) :
    IsTameSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h

theorem IsTameSubextension.coprime {E : IntermediateField K Ω} (hE : IsTameSubextension E)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E] :
    Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) :=
  hE.2 inferInstance inferInstance inferInstance inferInstance

theorem IsUnramifiedSubextension.isTameSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : IsTameSubextension E :=
  ⟨hE.1, fun _ _ _ _ ↦ by rw [hE.ramificationIndex_eq_one]; exact Nat.coprime_one_left _⟩

variable (K Ω) in

def tameExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsTameSubextension E}, E.1

theorem IsTameSubextension.le_tameExtension {E : IntermediateField K Ω}
    (hE : IsTameSubextension E) : E ≤ tameExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsTameSubextension E} ↦ E.1) ⟨E, hE⟩

variable (K Ω) in

theorem maximalUnramifiedExtension_le_tameExtension :
    maximalUnramifiedExtension K Ω ≤ tameExtension K Ω :=
  iSup_le fun E ↦ E.2.isTameSubextension.le_tameExtension

end Definition

theorem finiteDimensional_of_le {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {E F : IntermediateField K Ω} [FiniteDimensional K F] (h : E ≤ F) : FiniteDimensional K E :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

section Valued

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem isTameSubextension_iff (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsTameSubextension E ↔ Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) :=
  ⟨fun h ↦ h.coprime, fun h ↦ (isTameSubextension_iff_exists E).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩

theorem isUnramifiedSubextension_iff' (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsUnramifiedSubextension E ↔ ramificationIndex K E = 1 :=
  ⟨fun h ↦ h.ramificationIndex_eq_one, fun h ↦ (isUnramifiedSubextension_iff_exists E).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩

theorem residueDegree_restrictScalars (T : IntermediateField K Ω) [FiniteDimensional K T]
    (F : IntermediateField T Ω) [FiniteDimensional T F] :
    residueDegree K (F.restrictScalars K) = residueDegree K T * residueDegree T F := by
  have : FiniteDimensional K F := Module.Finite.trans T F
  have : FiniteDimensional K (F.restrictScalars K) := this
  have h1 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[K] ^ residueDegree K (F.restrictScalars K) :=
    card_residueField_eq_pow_residueDegree K _
  have h2 : Nat.card 𝓀[F] = Nat.card 𝓀[T] ^ residueDegree T F :=
    card_residueField_eq_pow_residueDegree T F
  have h3 : Nat.card 𝓀[T] = Nat.card 𝓀[K] ^ residueDegree K T :=
    card_residueField_eq_pow_residueDegree K T
  have h4 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[F] := rfl
  rw [h4, h2, h3, ← pow_mul] at h1
  exact (Nat.pow_right_injective (one_lt_card_residueField K) h1).symm

theorem ramificationIndex_restrictScalars (T : IntermediateField K Ω) [FiniteDimensional K T]
    (F : IntermediateField T Ω) [FiniteDimensional T F] :
    ramificationIndex K (F.restrictScalars K) = ramificationIndex K T * ramificationIndex T F := by
  have : FiniteDimensional K F := Module.Finite.trans T F
  have : FiniteDimensional K (F.restrictScalars K) := this
  have hf := residueDegree_restrictScalars T F
  have h1 := ramificationIndex_mul_residueDegree K (F.restrictScalars K)
  have h2 := ramificationIndex_mul_residueDegree K T
  have h3 := ramificationIndex_mul_residueDegree T F
  have h4 : Module.finrank K (F.restrictScalars K) = Module.finrank K T * Module.finrank T F :=
    (Module.finrank_mul_finrank K T F).symm
  rw [h4, ← h2, ← h3, hf] at h1
  have hpos : 0 < residueDegree K T * residueDegree T F :=
    Nat.mul_pos (residueDegree_pos K T) (residueDegree_pos T F)
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)

theorem IsTameSubextension.of_le {E F : IntermediateField K Ω} (hF : IsTameSubextension F)
    (h : E ≤ F) : IsTameSubextension E := by
  have := hF.1
  have : FiniteDimensional K E := finiteDimensional_of_le h
  set F' := extendScalars h
  have : FiniteDimensional K F' := (inferInstance : FiniteDimensional K F)
  have : FiniteDimensional E F' := Module.Finite.of_restrictScalars_finite K E F'
  rw [isTameSubextension_iff]
  have he : ramificationIndex K F = ramificationIndex K E * ramificationIndex E F' :=
    ramificationIndex_restrictScalars E F'
  exact Nat.Coprime.coprime_dvd_left (Dvd.intro _ he.symm) hF.coprime

end Valued

section SlopeTestRemainingChoices

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem natCast_residueField_ne_zero_of_coprime {m : ℕ} (hm : Nat.Coprime m (ringChar 𝓀[K])) :
    (m : 𝓀[K]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K])]
  intro hd
  have h1 := Nat.Coprime.eq_one_of_dvd hm.symm hd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))

theorem ne_zero_of_coprime_ringChar {m : ℕ} (hm : Nat.Coprime m (ringChar 𝓀[K])) : m ≠ 0 := by
  rintro rfl
  exact natCast_residueField_ne_zero_of_coprime (K := K) hm Nat.cast_zero

theorem irreducible_algebraMap_of_ramificationIndex_eq_one {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [FiniteDimensional K L] (h : ramificationIndex K L = 1) {π : 𝒪[K]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] π) := by
  have hu : IsUnramified K L := (isUnramified_iff K L).2 h
  have hmap := (map_maximalIdeal_eq_iff K L).2 hu
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hmap, hπ, Ideal.map_span, Set.image_singleton]

theorem isEisensteinAt_X_pow_sub_C {R : Type*} [CommRing R] {P : Ideal R} (hP : P ≠ ⊤) {m : ℕ}
    (hm : 0 < m) {a : R} (ha : a ∈ P) (ha2 : a ∉ P ^ 2) : (X ^ m - C a).IsEisensteinAt P := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact absurd (Subsingleton.elim P ⊤) hP
  refine ⟨?_, fun {n} hn ↦ ?_, ?_⟩
  · rw [(monic_X_pow_sub_C a hm.ne').leadingCoeff]
    exact fun h ↦ hP ((Ideal.eq_top_iff_one _).2 h)
  · rw [natDegree_X_pow_sub_C] at hn
    rw [coeff_sub, coeff_X_pow, if_neg hn.ne, coeff_C, zero_sub]
    split_ifs
    · exact P.neg_mem ha
    · rw [neg_zero]
      exact P.zero_mem
  · rw [coeff_sub, coeff_X_pow, if_neg hm.ne, coeff_C, if_pos rfl, zero_sub]
    exact fun h ↦ ha2 ((P ^ 2).neg_mem_iff.1 h)

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

theorem exists_isPrimitiveRoot_forall_mem_adjoin [HasUnramifiedRoots K Ω] (S : Finset Ω)
    (hS : ∀ x ∈ S, x ∈ unramifiedRoots K Ω) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1) ∧ ∀ x ∈ S, x ∈ K⟮ζ⟯ := by
  classical
  choose n hn0 hn using hS
  set k := ∏ x ∈ S.attach, n x.1 x.2 with hk_def
  have hk : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ ↦ hn0 x.1 x.2
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) k hk
  refine ⟨k, hk, ζ, hζ, fun x hx ↦ ?_⟩
  have hdvd : n x hx ∣ k := Finset.dvd_prod_of_mem (fun y : S ↦ n y.1 y.2) (Finset.mem_attach S ⟨x, hx⟩)
  have hx1 : x ^ (Nat.card 𝓀[K] ^ k - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hn x hx, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ k - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hk; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx1
  exact pow_mem (mem_adjoin_simple_self K ζ) i

end SlopeTestRemainingChoices

section Valued

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem finiteDimensional_adjoin_pair_and_ramificationIndex {k : ℕ} (hk : k ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1)) {π : 𝒪[K]} (hπ : Irreducible π) {m : ℕ}
    (hm : Nat.Coprime m (ringChar 𝓀[K])) {γ : Ω} (hγ : γ ^ m = algebraMap K Ω π) :
    ∃ _ : FiniteDimensional K (adjoin K {ζ, γ}), ramificationIndex K (adjoin K {ζ, γ}) = m := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hm)
  obtain ⟨hT, -⟩ := isUnramifiedSubextension_adjoin hk hζ
  set T := K⟮ζ⟯ with hT_def
  have := hT.1
  have heT : ramificationIndex K T = 1 := hT.ramificationIndex_eq_one
  set πT : 𝒪[T] := algebraMap 𝒪[K] 𝒪[T] π with hπT_def
  have hπT : Irreducible πT := irreducible_algebraMap_of_ramificationIndex_eq_one heT hπ
  set g : 𝒪[T][X] := X ^ m - C πT with hg_def
  have hgE : g.IsEisensteinAt 𝓂[T] := by
    refine isEisensteinAt_X_pow_sub_C (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm0
      (uniformizer_mem_maximalIdeal hπT) ?_
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπT, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro hd
    have := (_root_.pow_dvd_pow_iff hπT.ne_zero hπT.not_isUnit).1 (by rwa [pow_one] : πT ^ 2 ∣ πT ^ 1)
    omega
  have hgdeg : g.natDegree = m := natDegree_X_pow_sub_C
  have hπΩ : algebraMap T Ω ((πT : 𝒪[T]) : T) = algebraMap K Ω π := by
    rw [hπT_def, coe_algebraMap_integer, ← IsScalarTower.algebraMap_apply]
  have hγT : aeval γ (g.map (algebraMap 𝒪[T] T)) = 0 := by
    rw [hg_def, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_sub, map_pow, aeval_X,
      aeval_C, sub_eq_zero, hγ]
    exact hπΩ.symm
  have hγint : IsIntegral T γ :=
    ⟨g.map (algebraMap 𝒪[T] T), (monic_X_pow_sub_C _ hm0.ne').map _, by rwa [← aeval_def]⟩
  have : FiniteDimensional T T⟮γ⟯ := adjoin.finiteDimensional hγint
  set α := AdjoinSimple.gen T γ
  have hα : aeval α g = 0 := by
    apply (algebraMap T⟮γ⟯ Ω).injective
    rw [← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, map_zero,
      ← aeval_map_algebraMap T]
    exact hγT
  have he : ramificationIndex T T⟮γ⟯ = m := by
    rw [← hgdeg]
    exact ramificationIndex_eq_natDegree_of_isEisensteinAt hgE (by rw [hgdeg]; exact hm0) hα
      (adjoin_gen_eq_top γ)
  have hadj : T⟮γ⟯.restrictScalars K = adjoin K {ζ, γ} := adjoin_simple_adjoin_simple K ζ γ
  have : FiniteDimensional K T⟮γ⟯ := Module.Finite.trans T T⟮γ⟯
  have hfin : FiniteDimensional K (T⟮γ⟯.restrictScalars K) := this
  rw [hadj] at hfin
  refine ⟨hfin, ?_⟩
  have := ramificationIndex_restrictScalars T T⟮γ⟯
  rw [heT, one_mul, he] at this
  rw [← hadj]
  exact this

end Valued

section Structure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem apply_mem_adjoin_of_adjoin_eq_top {A Ω : Type*} [Field A] [Algebra K A] [Field Ω]
    [Algebra K Ω] (ι : A →ₐ[K] Ω) {z : A} (hgen : K⟮z⟯ = ⊤) (t : A) : ι t ∈ K⟮ι z⟯ := by
  have ht : t ∈ K⟮z⟯ := by rw [hgen]; trivial
  have : ι t ∈ (K⟮z⟯).map ι := (IntermediateField.mem_map _).2 ⟨t, ht, rfl⟩
  rwa [adjoin_map, Set.image_singleton] at this

variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem IsTameSubextension.exists_le_adjoin_pair [IsSepClosed Ω] {E : IntermediateField K Ω}
    (hE : IsTameSubextension E) {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1) ∧
      ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ ∃ γ : Ω, γ ^ m = algebraMap K Ω π ∧
        E ≤ adjoin K {ζ, γ} := by
  have := hE.1
  set e := ramificationIndex K E with he_def
  have he : Nat.Coprime e (ringChar 𝓀[K]) := hE.coprime
  obtain ⟨T₀, hT₀un, -, -, -, -, π₀, hπ₀, α, -, hαpow, hαgen⟩ := exists_tame_structure K E he
  have heT₀ : ramificationIndex K T₀ = 1 := (isUnramified_iff K T₀).1 hT₀un
  obtain ⟨ζ₀, hζ₀, hζ₀gen⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K T₀ heT₀
  have hπT₀ : Irreducible (algebraMap 𝒪[K] 𝒪[T₀] π) :=
    irreducible_algebraMap_of_ramificationIndex_eq_one heT₀ hπ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[T₀] hπT₀ hπ₀
  set t : 𝒪[T₀]ˣ := teichmuller T₀ (unitsToResidue T₀ u) with ht_def
  have ht : t ^ (Nat.card 𝓀[T₀] - 1) = 1 := teichmuller_pow_card_sub_one _
  have hw : u * t⁻¹ ∈ unitFiltration T₀ 1 := unitsMulInvTeichmuller_mem u
  have heK : (e : 𝓀[K]) ≠ 0 := natCast_residueField_ne_zero_of_coprime he
  have heT₀' : (e : 𝓀[T₀]) ≠ 0 := natCast_residueField_ne_zero T₀ heK
  obtain ⟨w₀, hw₀⟩ := unitFiltration_one_le_range_pow heT₀' hw
  have hw₀' : w₀ ^ e * t = u := by
    have : w₀ ^ e = u * t⁻¹ := hw₀
    rw [this, inv_mul_cancel_right]

  let ι : T₀ →ₐ[K] Ω := E.val.comp T₀.val
  have hιT₀ : ∀ x : T₀, ι x = ((x : E) : Ω) := fun x ↦ rfl
  obtain ⟨t', ht'_def⟩ : ∃ x : Ω, x = ι ((t : 𝒪[T₀]) : T₀) := ⟨_, rfl⟩
  obtain ⟨w', hw'_def⟩ : ∃ x : Ω, x = ι ((w₀ : 𝒪[T₀]) : T₀) := ⟨_, rfl⟩
  obtain ⟨α', hα'_def⟩ : ∃ x : Ω, x = (((α : 𝒪[E]) : E) : Ω) := ⟨_, rfl⟩
  have he0 : (e : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2
      (natCast_ne_zero_of_residueField heK)
  have : NeZero (e : Ω) := ⟨he0⟩
  obtain ⟨ξ, hξ⟩ := IsSepClosed.exists_pow_nat_eq t' e
  have ht'0 : t' ≠ 0 := by
    rw [ht'_def]
    exact (map_ne_zero_iff _ ι.injective).2 (by simp)
  have hw'0 : w' ≠ 0 := by
    rw [hw'_def]
    exact (map_ne_zero_iff _ ι.injective).2 (by simp)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow (ne_zero_of_coprime_ringChar he)] at hξ
    exact ht'0 hξ.symm

  have hα'pow : α' ^ e = algebraMap K Ω π * w' ^ e * t' := by
    have h1 : α' ^ e = ι ((π₀ : 𝒪[T₀]) : T₀) := by
      calc α' ^ e = (((α ^ e : 𝒪[E]) : E) : Ω) := by rw [hα'_def]; simp
        _ = ι ((π₀ : 𝒪[T₀]) : T₀) := by rw [hαpow, coe_algebraMap_integer]; rfl
    have h2 : ((π₀ : 𝒪[T₀]) : T₀) =
        algebraMap K T₀ π * ((w₀ : 𝒪[T₀]) : T₀) ^ e * ((t : 𝒪[T₀]) : T₀) := by
      rw [← hu, ← hw₀']
      push_cast [coe_algebraMap_integer]
      ring
    rw [h1, h2, map_mul, map_mul, map_pow, AlgHom.commutes, ht'_def, hw'_def]
  obtain ⟨γ, hγ_def⟩ : ∃ x : Ω, x = α' / (ξ * w') := ⟨_, rfl⟩
  have hγ : γ ^ e = algebraMap K Ω π := by
    rw [hγ_def, div_pow, mul_pow, hξ, hα'pow]
    field_simp

  have hf₀ : residueDegree K T₀ ≠ 0 := (residueDegree_pos K T₀).ne'
  have hcard : Nat.card 𝓀[T₀] = Nat.card 𝓀[K] ^ residueDegree K T₀ :=
    card_residueField_eq_pow_residueDegree K T₀
  have htT : ((t : 𝒪[T₀]) : T₀) ^ (Nat.card 𝓀[T₀] - 1) = 1 := by
    have := congrArg (fun x : 𝒪[T₀]ˣ ↦ (((x : 𝒪[T₀]) : T₀))) ht
    simpa using this
  have hξroot : ξ ^ (e * (Nat.card 𝓀[T₀] - 1)) = 1 := by
    rw [pow_mul, hξ, ht'_def, ← map_pow, htT, map_one]
  have hζ₀root : ι ζ₀ ^ (Nat.card 𝓀[T₀] - 1) = 1 := by
    rw [← map_pow, hζ₀.pow_eq_one, map_one]
  have hcK : ((Nat.card 𝓀[T₀] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
    rw [hcard]
    exact natCast_card_pow_sub_one_ne_zero hf₀
  classical
  obtain ⟨k, hk, ζ, hζ, hmem⟩ := exists_isPrimitiveRoot_forall_mem_adjoin (K := K) {ξ, ι ζ₀} (by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_unramifiedRoots_iff.2 ⟨_, by rw [Nat.cast_mul]; exact mul_ne_zero heK hcK, hξroot⟩
    · exact mem_unramifiedRoots_iff.2 ⟨_, hcK, hζ₀root⟩)
  refine ⟨k, hk, ζ, hζ, e, he, γ, hγ, ?_⟩

  have hζA : K⟮ζ⟯ ≤ adjoin K {ζ, γ} := adjoin_simple_le_iff.2 (subset_adjoin K _ (by simp))
  have hγA : γ ∈ adjoin K {ζ, γ} := subset_adjoin K _ (by simp)
  have hT₀A : ∀ x : T₀, ι x ∈ adjoin K {ζ, γ} := fun x ↦
    hζA (adjoin_simple_le_iff.2 (hmem (ι ζ₀) (by simp))
      (apply_mem_adjoin_of_adjoin_eq_top ι hζ₀gen x))
  have hξA : ξ ∈ adjoin K {ζ, γ} := hζA (hmem ξ (by simp))
  have hα'A : α' ∈ adjoin K {ζ, γ} := by
    have : α' = γ * (ξ * w') := by
      rw [hγ_def, div_mul_cancel₀ _ (mul_ne_zero hξ0 hw'0)]
    rw [this]
    exact mul_mem hγA (mul_mem hξA (hw'_def ▸ hT₀A _))
  have htop : (⊤ : IntermediateField K E) = adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)}) := by
    rw [← restrictScalars_adjoin, hαgen, restrictScalars_top]
  intro x hx
  have hx' : (⟨x, hx⟩ : E) ∈ adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)}) := by
    rw [← htop]
    trivial
  have hxm : E.val ⟨x, hx⟩ ∈ (adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)})).map E.val :=
    (IntermediateField.mem_map _).2 ⟨_, hx', rfl⟩
  rw [adjoin_map] at hxm
  refine (adjoin_le_iff.2 ?_) hxm
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with hy | hy
  · exact hT₀A ⟨y, hy⟩
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hα'_def] at hα'A
    exact hα'A

end Structure

section Union

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem isTameSubextension_adjoin_pair {k : ℕ} (hk : k ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1)) {π : 𝒪[K]} (hπ : Irreducible π) {m : ℕ}
    (hm : Nat.Coprime m (ringChar 𝓀[K])) {γ : Ω} (hγ : γ ^ m = algebraMap K Ω π) :
    IsTameSubextension (adjoin K {ζ, γ}) := by
  obtain ⟨hfin, he⟩ := finiteDimensional_adjoin_pair_and_ramificationIndex hk hζ hπ hm hγ
  rw [isTameSubextension_iff, he]
  exact hm

variable [IsSepClosed Ω]

theorem tameExtension_eq_sup {π : 𝒪[K]} (hπ : Irreducible π) :
    tameExtension K Ω = maximalUnramifiedExtension K Ω ⊔
      adjoin K {γ : Ω | ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ γ ^ m = algebraMap K Ω π} := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    obtain ⟨k, hk, ζ, hζ, m, hm, γ, hγ, hE⟩ := E.2.exists_le_adjoin_pair hπ
    refine hE.trans ((adjoin_le_iff).2 ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact le_sup_left (a := maximalUnramifiedExtension K Ω)
        (unramifiedRoots_subset_maximalUnramifiedExtension ⟨k, hk, hζ.pow_eq_one⟩)
    · exact le_sup_right (a := maximalUnramifiedExtension K Ω) (subset_adjoin K _ ⟨m, hm, hγ⟩)
  · refine sup_le (maximalUnramifiedExtension_le_tameExtension K Ω) ((adjoin_le_iff).2 ?_)
    rintro γ ⟨m, hm, hγ⟩
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω) one_ne_zero
    exact (isTameSubextension_adjoin_pair one_ne_zero hζ hπ hm hγ).le_tameExtension
      (subset_adjoin K _ (by simp))

theorem tameExtension_eq_adjoin {π : 𝒪[K]} (hπ : Irreducible π) :
    tameExtension K Ω = adjoin K (unramifiedRoots K Ω ∪
      {γ : Ω | ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ γ ^ m = algebraMap K Ω π}) := by
  rw [tameExtension_eq_sup hπ, maximalUnramifiedExtension_eq_adjoin, adjoin_union]

end Union

section Galois

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]

omit [Algebra.IsAlgebraic K Ω] in

theorem normal_tameExtension [Normal K Ω] : Normal K (tameExtension K Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [normal_iff_forall_map_le']
  intro σ
  rw [tameExtension_eq_adjoin hπ, adjoin_map]
  refine adjoin_le_iff.2 fun y hy ↦ subset_adjoin K _ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  rcases hx with ⟨n, hn, hx⟩ | ⟨m, hm, hx⟩
  · exact Or.inl ⟨n, hn, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, map_one]⟩
  · exact Or.inr ⟨m, hm, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, AlgEquiv.commutes]⟩

omit [Algebra.IsAlgebraic K Ω] in

theorem isGalois_tameExtension_of_valued [IsGalois K Ω] : IsGalois K (tameExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (tameExtension K Ω) Ω
  have := normal_tameExtension (K := K) (Ω := Ω)
  isGalois_iff.2 ⟨inferInstance, inferInstance⟩

end Galois

section SeparableClosure

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

instance isGalois_tameExtension : IsGalois K (tameExtension K Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact isGalois_tameExtension_of_valued

end SeparableClosure

end Sec_TameExtension


/-! ### NormalLattice -/
section Sec_NormalLattice

open ValuativeRel Finset

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]

theorem integer_smul_eq (c : 𝒪[K]) (y : L) : c • y = algebraMap K L (c : K) * y := by
  rw [← Algebra.smul_def]
  rfl

theorem integer_smul_cancel {c : 𝒪[K]} (hc : c ≠ 0) {y z : L} (h : c • y = c • z) : y = z := by
  rw [integer_smul_eq, integer_smul_eq] at h
  refine mul_left_cancel₀ ?_ h
  rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
  exact fun h0 => hc (Subtype.ext h0)

variable [FiniteDimensional K L]

section Lattice

def normalLattice (π : 𝒪[K]) (θ : L) (s : ℕ) : Submodule 𝒪[K] L :=
  Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => π ^ s • σ θ)

variable (π : 𝒪[K]) (θ : L)

theorem mem_normalLattice_iff {s : ℕ} {x : L} :
    x ∈ normalLattice π θ s ↔ ∃ c : Gal(L/K) → 𝒪[K], π ^ s • ∑ σ, c σ • σ θ = x := by
  rw [normalLattice, Submodule.mem_span_range_iff_exists_fun]
  simp_rw [smul_sum, smul_comm (π ^ s)]

theorem smul_sum_mem_normalLattice (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ s :=
  (mem_normalLattice_iff π θ).mpr ⟨c, rfl⟩

theorem coeff_injective (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    {c d : Gal(L/K) → 𝒪[K]} (h : ∑ σ, c σ • σ θ = ∑ σ, d σ • σ θ) : c = d := by
  have h0 : ∑ σ, ((c σ : K) - d σ) • σ θ = 0 := by
    simp_rw [sub_smul, sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext σ
  exact Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hθ _ h0 σ))

theorem smul_sum_mem_normalLattice_add_iff (hπ : π ≠ 0)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (s N : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ (s + N) ↔ ∀ σ, π ^ N ∣ c σ := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (mem_normalLattice_iff π θ).mp h
    have e : π ^ s • ∑ σ, (π ^ N * d σ) • σ θ = π ^ s • ∑ σ, c σ • σ θ := by
      rw [← hd, pow_add, mul_smul]
      simp_rw [smul_sum, mul_smul]
    have := coeff_injective θ hθ (integer_smul_cancel (pow_ne_zero s hπ) e)
    intro σ
    exact ⟨d σ, (congrFun this σ).symm⟩
  · intro h
    choose d hd using h
    refine (mem_normalLattice_iff π θ).mpr ⟨d, ?_⟩
    rw [pow_add, mul_smul]
    simp_rw [smul_sum, ← mul_smul, hd]

omit [FiniteDimensional K L] in

theorem normalLattice_antitone : Antitone (normalLattice π θ) := by
  refine antitone_nat_of_succ_le fun s => Submodule.span_le.mpr ?_
  rintro _ ⟨σ, rfl⟩
  simp only [SetLike.mem_coe, pow_succ', mul_smul]
  exact Submodule.smul_mem _ π (Submodule.subset_span ⟨σ, rfl⟩)

theorem pow_smul_mem_normalLattice {t u : ℕ} {x : L} (hx : x ∈ normalLattice π θ t) :
    π ^ u • x ∈ normalLattice π θ (t + u) := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [← mul_smul, ← pow_add, add_comm u t]
  exact smul_sum_mem_normalLattice π θ _ c

theorem algEquiv_smul_sum (τ : Gal(L/K)) (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    τ (π ^ s • ∑ σ, c σ • σ θ) = π ^ s • ∑ σ, c (τ⁻¹ * σ) • σ θ := by
  have h : ∀ (a : 𝒪[K]) (y : L), τ (a • y) = a • τ y := fun a y => by
    rw [integer_smul_eq, integer_smul_eq, map_mul, AlgEquiv.commutes]
  rw [h, map_sum]
  congr 1
  simp_rw [h, ← AlgEquiv.mul_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp)

theorem algEquiv_mem_normalLattice (τ : Gal(L/K)) {s : ℕ} {x : L} (hx : x ∈ normalLattice π θ s) :
    τ x ∈ normalLattice π θ s := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [algEquiv_smul_sum]
  exact smul_sum_mem_normalLattice π θ s _

end Lattice

section Integral

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]

variable (π : 𝒪[K]) (θ : L)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem mem_integer_of_mem_normalLattice (hθO : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) {s : ℕ} {x : L}
    (hx : x ∈ normalLattice π θ s) : x ∈ 𝒪[L] := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [integer_smul_eq]
  refine mul_mem ((algebraMap_mem_integer_iff K L _).mpr (π ^ s).2) (sum_mem fun σ _ => ?_)
  rw [integer_smul_eq]
  exact mul_mem ((algebraMap_mem_integer_iff K L _).mpr (c σ).2) (hθO σ)

omit [ValuativeRel L] [ValuativeExtension K L] [FiniteDimensional K L] in

theorem exists_pow_mul_mem_integer_of_lt_one {F : Type*} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {t : F}
    (ht : valuation F t < 1) (a : F) : ∃ n, ∀ m ≥ n, t ^ m * a ∈ 𝒪[F] := by
  have ht1 : t ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr ht.le
  have key : ∃ n, t ^ n * a ∈ 𝒪[F] := by
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    have hva : valuation F a ≠ 0 := by simpa using ha
    obtain ⟨n, hn⟩ := exists_pow_lt₀ ht (Units.mk0 (valuation F a)⁻¹ (inv_ne_zero hva))
    refine ⟨n, (Valuation.mem_integer_iff _ _).mpr (le_of_lt ?_)⟩
    calc valuation F (t ^ n * a) = valuation F t ^ n * valuation F a := by simp
      _ < (valuation F a)⁻¹ * valuation F a :=
          mul_lt_mul_of_pos_right (by simpa using hn) (zero_lt_iff.mpr hva)
      _ = 1 := inv_mul_cancel₀ hva
  obtain ⟨n, hn⟩ := key
  refine ⟨n, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, mul_comm (t ^ n), mul_assoc]
  exact mul_mem (pow_mem ht1 d) hn

omit [ValuativeRel L] [ValuativeExtension K L] [FiniteDimensional K L] in

theorem exists_pow_mul_mem_integer (hπ : Irreducible π) (a : K) :
    ∃ n, ∀ m ≥ n, (π : K) ^ m * a ∈ 𝒪[K] :=
  exists_pow_mul_mem_integer_of_lt_one
    (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)) a

variable [IsGalois K L]

omit [ValuativeRel L] [ValuativeExtension K L] in

theorem exists_pow_smul_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (y : L) :
    ∃ n, ∀ m ≥ n, π ^ m • y ∈ normalLattice π θ 0 := by
  let b : Module.Basis Gal(L/K) K L := basisOfLinearIndependentOfCardEqFinrank hθ
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))
  have hb : ∀ σ, b σ = σ θ := fun σ => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  choose n hn using fun σ => exists_pow_mul_mem_integer π hπ (b.repr y σ)
  refine ⟨univ.sup n, fun m hm => (mem_normalLattice_iff π θ).mpr
    ⟨fun σ => ⟨_, hn σ m ((le_sup (mem_univ σ)).trans hm)⟩, ?_⟩⟩
  conv_rhs => rw [← b.sum_repr y]
  rw [pow_zero, one_smul, smul_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [hb, integer_smul_eq, integer_smul_eq, Algebra.smul_def, ← mul_assoc, ← map_mul]
  simp

omit [ValuativeRel L] [ValuativeExtension K L] in

theorem exists_pow_smul_mul_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    ∃ r, ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0 := by
  choose n hn using fun p : Gal(L/K) × Gal(L/K) =>
    exists_pow_smul_mem_normalLattice π θ hπ hθ (p.1 θ * p.2 θ)
  exact ⟨univ.sup n, fun σ τ => hn (σ, τ) _ (le_sup (mem_univ (σ, τ)))⟩

end Integral

section Product

variable (π : 𝒪[K]) (θ : L)

theorem mul_mem_normalLattice {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {a b : ℕ} {x y : L}
    (hx : x ∈ normalLattice π θ (a + r)) (hy : y ∈ normalLattice π θ b) :
    x * y ∈ normalLattice π θ (a + b) := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  obtain ⟨d, rfl⟩ := (mem_normalLattice_iff π θ).mp hy
  have h0 : π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ) ∈ normalLattice π θ 0 := by
    rw [smul_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [smul_sum]
    refine Submodule.sum_mem _ fun τ _ => ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (hr σ τ)
  have e : (π ^ (a + r) • ∑ σ, c σ • σ θ) * (π ^ b • ∑ τ, d τ • τ θ) =
      π ^ (a + b) • (π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ)) := by
    rw [smul_smul, ← pow_add, smul_mul_smul_comm, ← pow_add, Finset.sum_mul_sum,
      add_right_comm]
    simp_rw [smul_mul_smul_comm]
  rw [e]
  simpa using pow_smul_mem_normalLattice π θ (u := a + b) h0

theorem mul_mem_normalLattice_succ {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s t : ℕ} (hs : r < s)
    {x y : L} (hx : x ∈ normalLattice π θ s) (hy : y ∈ normalLattice π θ t) :
    x * y ∈ normalLattice π θ (t + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hs
  have h := mul_mem_normalLattice π θ hr (a := d + 1) (b := t)
    (by rwa [show d + 1 + r = r + d + 1 by omega]) hy
  exact normalLattice_antitone π θ (show t + 1 ≤ d + 1 + t by omega) h

end Product

section Complete

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] in

private theorem isAdicComplete_maximalIdeal : IsAdicComplete 𝓂[K] 𝒪[K] := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

omit [FiniteDimensional K L] in

theorem smodEq_iff_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x y : 𝒪[K]} :
    x ≡ y [SMOD (𝓂[K] ^ n • ⊤ : Submodule 𝒪[K] 𝒪[K])] ↔ π ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_iff hπ]

omit [FiniteDimensional K L] in

theorem exists_limit_of_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) (c : ℕ → 𝒪[K])
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n - c m) :
    ∃ a, ∀ N, ∃ M, ∀ n ≥ M, π ^ N ∣ c n - a := by
  choose M hM using hc
  let M' : ℕ → ℕ := fun N => (range (N + 1)).sup M
  have hM' : ∀ N, M N ≤ M' N := fun N => le_sup (mem_range.mpr (Nat.lt_succ_self N))
  have hmono : Monotone M' := fun i j hij =>
    sup_mono (range_subset_range.mpr (Nat.succ_le_succ hij))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (isAdicComplete_maximalIdeal (K := K)).toIsPrecomplete
    (f := fun N => c (M' N)) (fun {m n} hmn => by
      rw [smodEq_iff_pow_dvd hπ]
      exact hM m (M' n) ((hM' m).trans (hmono hmn)) (M' m) (hM' m))
  refine ⟨a, fun N => ⟨M' N, fun n hn => ?_⟩⟩
  have h1 : π ^ N ∣ c n - c (M' N) := hM N _ (hM' N) n ((hM' N).trans hn)
  have h2 : π ^ N ∣ c (M' N) - a := (smodEq_iff_pow_dvd hπ).mp (ha N)
  have := dvd_add h1 h2
  rwa [sub_add_sub_cancel] at this

omit [FiniteDimensional K L] in

theorem eq_zero_of_forall_pow_dvd {π : 𝒪[K]} (hπ : Irreducible π) {x : 𝒪[K]}
    (h : ∀ N, π ^ N ∣ x) : x = 0 :=
  IsHausdorff.haus (isAdicComplete_maximalIdeal (K := K)).toIsHausdorff x fun N => by
    rw [smodEq_iff_pow_dvd hπ, sub_zero]
    exact h N

variable (π : 𝒪[K]) (θ : L)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem smul_sum_sub_smul_sum (s : ℕ) (c d : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ - π ^ s • ∑ σ, d σ • σ θ = π ^ s • ∑ σ, (c σ - d σ) • σ θ := by
  simp only [sub_smul, sum_sub_distrib, smul_sub]

theorem eq_zero_of_forall_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} {x : L}
    (h : ∀ N, x ∈ normalLattice π θ (s + N)) : x = 0 := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp (h 0)
  have hc : ∀ σ, c σ = 0 := fun σ => eq_zero_of_forall_pow_dvd hπ fun N =>
    (smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ s N c).mp (h N) σ
  simp [hc]

theorem exists_limit_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} (y : ℕ → L)
    (hy : ∀ n, y n ∈ normalLattice π θ s)
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, y n - y m ∈ normalLattice π θ (s + N)) :
    ∃ z ∈ normalLattice π θ s, ∀ N, ∃ M, ∀ n ≥ M, y n - z ∈ normalLattice π θ (s + N) := by
  choose c hcy using fun n => (mem_normalLattice_iff π θ).mp (hy n)
  have hcc : ∀ σ, ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, π ^ N ∣ c n σ - c m σ := by
    intro σ N
    obtain ⟨M, hM⟩ := hc N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := hM m hm n hn
    rw [← hcy n, ← hcy m, smul_sum_sub_smul_sum,
      smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ] at this
    exact this σ
  choose a ha using fun σ => exists_limit_of_pow_dvd hπ (fun n => c n σ) (hcc σ)
  refine ⟨π ^ s • ∑ σ, a σ • σ θ, smul_sum_mem_normalLattice π θ s a, fun N => ?_⟩
  choose M hM using fun σ => ha σ N
  refine ⟨univ.sup M, fun n hn => ?_⟩
  rw [← hcy n, smul_sum_sub_smul_sum, smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ]
  exact fun σ => hM σ n ((le_sup (mem_univ σ)).trans hn)

variable {π θ}

theorem exists_inv_one_add (hπ : Irreducible π) (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    {r : ℕ} (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s : ℕ}
    (hs : r < s) {x : L} (hx : x ∈ normalLattice π θ s) :
    ∃ z ∈ normalLattice π θ s, (1 + x) * (1 + z) = 1 := by
  have hnx : -x ∈ normalLattice π θ s := neg_mem hx
  have hpow : ∀ i, (-x) ^ (i + 1) ∈ normalLattice π θ (s + i) := by
    intro i
    induction i with
    | zero => simpa using hnx
    | succ i ih =>
      rw [pow_succ', ← add_assoc]
      exact mul_mem_normalLattice_succ π θ hr hs hnx ih
  let z : ℕ → L := fun n => ∑ i ∈ range n, (-x) ^ (i + 1)
  have htail : ∀ m d, z (m + d) - z m ∈ normalLattice π θ (s + m) := by
    intro m d
    simp only [z, sum_range_add, add_sub_cancel_left]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact normalLattice_antitone π θ (show s + m ≤ s + (m + i) by omega) (hpow (m + i))
  have hzs : ∀ n, z n ∈ normalLattice π θ s := fun n => by
    simpa [z] using htail 0 n
  obtain ⟨w, hw, hlim⟩ := exists_limit_normalLattice π θ hπ hθ z hzs (fun N => ⟨N, fun m hm n hn => by
    rcases le_total m n with hmn | hnm
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact normalLattice_antitone π θ (by omega) (htail m d)
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
      have := neg_mem (htail n d)
      rw [neg_sub] at this
      exact normalLattice_antitone π θ (by omega) this⟩)
  refine ⟨w, hw, ?_⟩
  have hgeom : ∀ n, (1 + x) * (1 + z n) = 1 - (-x) ^ (n + 1) := by
    intro n
    have h1 : 1 + z n = ∑ i ∈ range (n + 1), (-x) ^ i := by
      simp only [z, sum_range_succ', pow_zero]
      ring
    rw [h1, ← mul_neg_geom_sum, sub_neg_eq_add]
  have hmul : ∀ {t : ℕ} {v : L}, v ∈ normalLattice π θ t → (1 + x) * v ∈ normalLattice π θ t :=
    fun {t v} hv => by
      rw [add_mul, one_mul]
      exact add_mem hv (normalLattice_antitone π θ (Nat.le_succ t)
        (mul_mem_normalLattice_succ π θ hr hs hx hv))
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_normalLattice π θ hπ hθ (s := s) fun N => ?_
  obtain ⟨M, hM⟩ := hlim N
  have e : (1 + x) * (1 + w) - 1 = (1 + x) * (w - z (max M N)) - (-x) ^ (max M N + 1) := by
    have := hgeom (max M N)
    linear_combination this
  rw [e]
  refine sub_mem (hmul ?_) (normalLattice_antitone π θ (by omega) (hpow (max M N)))
  have := neg_mem (hM (max M N) (le_max_left M N))
  rwa [neg_sub] at this

theorem exists_unit_one_add [ValuativeRel L] [ValuativeExtension K L] (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (hθO : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L])
    {r : ℕ} (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s : ℕ}
    (hs : r < s) {x : L} (hx : x ∈ normalLattice π θ s) :
    ∃ u : 𝒪[L]ˣ, ((u : 𝒪[L]) : L) = 1 + x ∧
      (((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1 ∈ normalLattice π θ s := by
  obtain ⟨z, hz, hxz⟩ := exists_inv_one_add hπ hθ hr hs hx
  have hxO : 1 + x ∈ 𝒪[L] := add_mem (one_mem _) (mem_integer_of_mem_normalLattice π θ hθO hx)
  have hzO : 1 + z ∈ 𝒪[L] := add_mem (one_mem _) (mem_integer_of_mem_normalLattice π θ hθO hz)
  refine ⟨⟨⟨1 + x, hxO⟩, ⟨1 + z, hzO⟩, Subtype.ext hxz, Subtype.ext (by rw [mul_comm]; exact hxz)⟩,
    rfl, ?_⟩
  simpa using hz

end Complete

section Existence

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

omit [FiniteDimensional K L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in

theorem valuation_algebraMap_lt_one {π : 𝒪[K]} (hπ : Irreducible π) :
    valuation L (algebraMap K L (π : K)) < 1 :=
  (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) _).mpr
    (valuation_lt_one_of_mem_maximalIdeal ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit))

variable [IsGalois K L]

theorem exists_normalBasis_integer {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ θ : L, (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧ ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L] := by
  let θ₀ : L := IsGalois.normalBasis K L 1
  have hθ₀ : LinearIndependent K fun σ : Gal(L/K) => σ θ₀ := by
    have := (IsGalois.normalBasis K L).linearIndependent
    convert this using 1
    funext σ
    rw [IsGalois.normalBasis_apply]
  choose n hn using fun σ : Gal(L/K) =>
    exists_pow_mul_mem_integer_of_lt_one (valuation_algebraMap_lt_one (L := L) hπ) (σ θ₀)
  let c : K := (π : K) ^ univ.sup n
  have hc : c ≠ 0 := pow_ne_zero _ fun h => hπ.ne_zero (Subtype.ext h)
  refine ⟨c • θ₀, ?_, fun σ => ?_⟩
  · rw [Fintype.linearIndependent_iff] at hθ₀ ⊢
    intro g hg σ
    have := hθ₀ (fun τ => g τ * c) (by simpa [map_smul, smul_smul] using hg) σ
    exact (mul_eq_zero.mp this).resolve_right hc
  · rw [map_smul, Algebra.smul_def, map_pow]
    exact hn σ _ (le_sup (mem_univ σ))

end Existence

section Open

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L] [IsGalois K L]
  [ValuativeExtension K L] in
private theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space L := by
  let := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  infer_instance

variable (π : 𝒪[K]) (θ : L)

theorem isOpen_normalLattice (hπ : Irreducible π) (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    (s : ℕ) : IsOpen (normalLattice π θ s : Set L) := by
  have := t2Space_isNonarchimedeanLocalField_singleBlock (L := L)
  have hπ0 : algebraMap K L (π : K) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap K L).injective]
    exact fun h => hπ.ne_zero (Subtype.ext h)
  have hcont : Continuous fun c : Gal(L/K) → 𝒪[K] => π ^ s • ∑ σ, c σ • σ θ := by
    simp_rw [integer_smul_eq, Finset.mul_sum]
    refine continuous_finsetSum _ fun σ _ => ?_
    simp_rw [← Algebra.smul_def, smul_smul]
    refine Continuous.smul ?_ continuous_const
    exact continuous_const.mul (continuous_subtype_val.comp (continuous_apply σ))
  have hcpt : IsCompact (normalLattice π θ s : Set L) := by
    have : (normalLattice π θ s : Set L) = Set.range fun c : Gal(L/K) → 𝒪[K] =>
        π ^ s • ∑ σ, c σ • σ θ := by
      ext x
      exact (mem_normalLattice_iff π θ).trans (by simp)
    rw [this]
    exact isCompact_range hcont
  let A : ℕ → Set L := fun n => (fun y => algebraMap K L (π : K) ^ n * y) ⁻¹' normalLattice π θ s
  have hA : ∀ n, IsClosed (A n) := fun n =>
    hcpt.isClosed.preimage (continuous_const.mul continuous_id)
  have hU : ⋃ n, A n = Set.univ := by
    refine Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ?_
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_normalLattice π θ hπ hθ y
    have h := pow_smul_mem_normalLattice π θ (u := s) (hn n le_rfl)
    rw [zero_add, ← mul_smul, ← pow_add, add_comm, integer_smul_eq] at h
    exact ⟨n + s, by simpa [A] using h⟩
  obtain ⟨n, y₀, hy₀⟩ := nonempty_interior_of_iUnion_of_closed hA hU
  let h : L ≃ₜ L := Homeomorph.mulLeft₀ (algebraMap K L (π : K) ^ n) (pow_ne_zero n hπ0)
  have hsub : h '' interior (A n) ⊆ normalLattice π θ s := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy : y ∈ A n)
  exact AddSubgroup.isOpen_of_mem_nhds (normalLattice π θ s).toAddSubgroup
    (Filter.mem_of_superset ((h.isOpenMap _ isOpen_interior).mem_nhds ⟨y₀, hy₀, rfl⟩) hsub)

end Open

end Sec_NormalLattice


/-! ### CompleteTrivialLocal -/
section Sec_CompleteTrivialLocal

open ValuativeRel Finset

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [ValuativeRel L]

abbrev unitVal (u : 𝒪[L]ˣ) : L := ((u : 𝒪[L]) : L)

theorem unitVal_injective : Function.Injective (unitVal (L := L)) :=
  fun _ _ h => Units.ext (Subtype.ext h)

variable (V : Subgroup 𝒪[L]ˣ)
  (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, unitVal w = σ (unitVal u))

def stableSMul (σ : Gal(L/K)) (u : V) : V :=
  ⟨(hV σ u u.2).choose, (hV σ u u.2).choose_spec.1⟩

theorem unitVal_stableSMul (σ : Gal(L/K)) (u : V) :
    unitVal (stableSMul V hV σ u : 𝒪[L]ˣ) = σ (unitVal u) :=
  (hV σ u u.2).choose_spec.2

@[instance_reducible]
def stableUnitsAction : MulDistribMulAction Gal(L/K) V where
  smul := stableSMul V hV
  one_smul u := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV 1 u : 𝒪[L]ˣ) = unitVal u
    rw [unitVal_stableSMul, AlgEquiv.one_apply]))
  mul_smul σ τ u := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV (σ * τ) u : 𝒪[L]ˣ) =
      unitVal (stableSMul V hV σ (stableSMul V hV τ u) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul, unitVal_stableSMul, unitVal_stableSMul, AlgEquiv.mul_apply]))
  smul_mul σ u w := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV σ (u * w) : 𝒪[L]ˣ) =
      unitVal ((stableSMul V hV σ u * stableSMul V hV σ w : V) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul]
    simp only [unitVal, Subgroup.coe_mul, Units.val_mul, Subring.coe_mul] at *
    rw [map_mul]
    exact congrArg₂ (· * ·) ((hV σ u u.2).choose_spec.2).symm ((hV σ w w.2).choose_spec.2).symm))
  smul_one σ := Subtype.ext (unitVal_injective (by
    show unitVal (stableSMul V hV σ 1 : 𝒪[L]ˣ) = unitVal ((1 : V) : 𝒪[L]ˣ)
    rw [unitVal_stableSMul]
    simp [unitVal]))

theorem unitVal_smul (σ : Gal(L/K)) (u : V) :
    letI := stableUnitsAction V hV
    unitVal ((σ • u : V) : 𝒪[L]ˣ) = σ (unitVal u) :=
  (hV σ u u.2).choose_spec.2

end Action

section Data

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
  [FiniteDimensional K L]

structure NormalLatticeData where

  π : 𝒪[K]
  irreducible : Irreducible π

  θ : L
  linearIndependent : LinearIndependent K fun σ : Gal(L/K) => σ θ
  integer : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]

  r : ℕ
  mul_mem : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0

namespace NormalLatticeData

variable {K L} (D : NormalLatticeData K L)

abbrev lat (s : ℕ) : Submodule 𝒪[K] L := normalLattice D.π D.θ s

abbrev k : ℕ := D.r + 1

omit [FiniteDimensional K L] in
theorem lat_antitone {s t : ℕ} (h : s ≤ t) : D.lat t ≤ D.lat s := normalLattice_antitone _ _ h

theorem mul_mem_lat {s t : ℕ} (hs : D.k ≤ s) {x y : L} (hx : x ∈ D.lat s) (hy : y ∈ D.lat t) :
    x * y ∈ D.lat (t + 1) :=
  mul_mem_normalLattice_succ D.π D.θ D.mul_mem (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hs) hx hy

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]

theorem exists_unit {s : ℕ} (hs : D.k ≤ s) {x : L} (hx : x ∈ D.lat s) :
    ∃ u : 𝒪[L]ˣ, unitVal u = 1 + x ∧ unitVal u⁻¹ - 1 ∈ D.lat s :=
  exists_unit_one_add D.irreducible D.linearIndependent D.integer D.mul_mem
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hs) hx

def units (j : ℕ) : Subgroup 𝒪[L]ˣ where
  carrier := {u | unitVal u - 1 ∈ D.lat (D.k + j)}
  one_mem' := by
    show unitVal (1 : 𝒪[L]ˣ) - 1 ∈ D.lat (D.k + j)
    simp [unitVal]
  mul_mem' {u w} hu hw := by
    have e : unitVal (u * w) - 1 = (unitVal u - 1) + (unitVal w - 1) +
        (unitVal u - 1) * (unitVal w - 1) := by
      simp only [unitVal, Units.val_mul, Subring.coe_mul]
      ring
    show unitVal (u * w) - 1 ∈ D.lat (D.k + j)
    rw [e]
    exact add_mem (add_mem hu hw)
      (D.lat_antitone (Nat.le_succ _) (D.mul_mem_lat (Nat.le_add_right _ _) hu hw))
  inv_mem' {u} hu := by
    obtain ⟨v, hv, hvi⟩ := D.exists_unit (Nat.le_add_right _ j) hu
    have : v = u := unitVal_injective (by rw [hv]; ring)
    rw [← this]
    exact hvi

theorem mem_units {j : ℕ} {u : 𝒪[L]ˣ} : u ∈ D.units j ↔ unitVal u - 1 ∈ D.lat (D.k + j) := Iff.rfl

theorem units_antitone : Antitone D.units := fun _ _ h _ hu =>
  D.lat_antitone (by omega) hu

theorem exists_mem_units_eq (j : ℕ) (σ : Gal(L/K)) {u : 𝒪[L]ˣ} (hu : u ∈ D.units j) :
    ∃ w ∈ D.units j, unitVal w = σ (unitVal u) := by
  have hx : σ (unitVal u - 1) ∈ D.lat (D.k + j) := algEquiv_mem_normalLattice _ _ σ hu
  obtain ⟨w, hw, -⟩ := D.exists_unit (Nat.le_add_right _ j) hx
  refine ⟨w, ?_, ?_⟩
  · rw [mem_units, hw, add_sub_cancel_left]
    exact hx
  · rw [hw, map_sub, map_one]
    ring

end NormalLatticeData

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]

theorem NormalLatticeData.nonempty : Nonempty (NormalLatticeData K L) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨θ, hθ, hθO⟩ := exists_normalBasis_integer (L := L) hπ
  obtain ⟨r, hr⟩ := exists_pow_smul_mul_mem_normalLattice π θ hπ hθ
  exact ⟨⟨π, hπ, θ, hθ, hθO, r, hr⟩⟩

end Data

section Units

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

namespace NormalLatticeData

variable (D : NormalLatticeData K L)

theorem units_zero_stable :
    ∀ σ : Gal(L/K), ∀ u ∈ D.units 0, ∃ w ∈ D.units 0, unitVal w = σ (unitVal u) :=
  fun σ _ hu => D.exists_mem_units_eq 0 σ hu

@[instance_reducible]
def action : MulDistribMulAction Gal(L/K) (D.units 0) :=
  stableUnitsAction (D.units 0) D.units_zero_stable

attribute [local instance] action

abbrev val (x : D.units 0) : L := unitVal (x : 𝒪[L]ˣ)

theorem val_injective : Function.Injective D.val :=
  fun _ _ h => Subtype.ext (unitVal_injective h)

theorem val_one : D.val 1 = 1 := by simp [val, unitVal]

theorem val_mul (x y : D.units 0) : D.val (x * y) = D.val x * D.val y := by
  simp [val, unitVal]

theorem val_mul_val_inv (x : D.units 0) : D.val x * D.val x⁻¹ = 1 := by
  rw [← val_mul, mul_inv_cancel, val_one]

theorem val_smul (σ : Gal(L/K)) (x : D.units 0) : D.val (σ • x) = σ (D.val x) :=
  unitVal_smul (D.units 0) D.units_zero_stable σ x

theorem val_sub_one_mem (x : D.units 0) : D.val x - 1 ∈ D.lat D.k := x.2

theorem val_mul_mem (x : D.units 0) {t : ℕ} {z : L} (hz : z ∈ D.lat t) : D.val x * z ∈ D.lat t := by
  have e : D.val x * z = z + (D.val x - 1) * z := by ring
  rw [e]
  exact add_mem hz (D.lat_antitone (Nat.le_succ t) (D.mul_mem_lat le_rfl (D.val_sub_one_mem x) hz))

def filt : StableFiltration Gal(L/K) (D.units 0) where
  F j := (D.units j).subgroupOf (D.units 0)
  antitone := fun _ _ h _ hx => D.units_antitone h hx
  smul_mem j σ {x} hx := by
    show D.val (σ • x) - 1 ∈ D.lat (D.k + j)
    rw [val_smul, ← map_one σ, ← map_sub]
    exact algEquiv_mem_normalLattice _ _ σ hx

theorem mem_filt {j : ℕ} {x : D.units 0} : x ∈ D.filt.F j ↔ D.val x - 1 ∈ D.lat (D.k + j) :=
  Iff.rfl

theorem filt_zero : D.filt.F 0 = ⊤ := Subgroup.subgroupOf_self _

theorem div_mem_filt_iff {j : ℕ} {x y : D.units 0} :
    x / y ∈ D.filt.F j ↔ D.val x - D.val y ∈ D.lat (D.k + j) := by
  rw [mem_filt]
  have e1 : D.val (x / y) - 1 = D.val y⁻¹ * (D.val x - D.val y) := by
    rw [div_eq_mul_inv, val_mul]
    linear_combination D.val_mul_val_inv y
  have e2 : D.val x - D.val y = D.val y * (D.val (x / y) - 1) := by
    rw [div_eq_mul_inv, val_mul]
    linear_combination (-D.val x) * D.val_mul_val_inv y
  constructor
  · intro h
    rw [e2]
    exact D.val_mul_mem y h
  · intro h
    rw [e1]
    exact D.val_mul_mem y⁻¹ h

theorem filt_complete : FiltrationComplete D.filt.F := by
  intro x hx
  obtain ⟨z, hz, hlim⟩ := exists_limit_normalLattice D.π D.θ D.irreducible D.linearIndependent
    (s := D.k) (fun n => D.val (x n) - 1) (fun n => D.val_sub_one_mem (x n)) (fun N => by
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have := D.div_mem_filt_iff.mp (hM m hm n hn)
      rwa [sub_sub_sub_cancel_right])
  obtain ⟨w, hw, -⟩ := D.exists_unit le_rfl hz
  have hw0 : w ∈ D.units 0 := by
    rw [mem_units, hw, add_sub_cancel_left]
    exact hz
  refine ⟨⟨w, hw0⟩, fun N => ?_⟩
  obtain ⟨M, hM⟩ := hlim N
  refine ⟨M, fun n hn => D.div_mem_filt_iff.mpr ?_⟩
  have e : D.val (x n) - D.val ⟨w, hw0⟩ = (D.val (x n) - 1) - z := by
    simp only [val, hw]
    ring
  rw [e]
  exact hM n hn

theorem filt_separated : FiltrationSeparated D.filt.F := by
  intro x hx
  have h0 : D.val x - 1 = 0 := eq_zero_of_forall_mem_normalLattice D.π D.θ D.irreducible
    D.linearIndependent (s := D.k) fun N => hx N
  exact D.val_injective (by rw [val_one]; exact sub_eq_zero.mp h0)

end NormalLatticeData

end Units

section Graded

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
theorem algEquiv_algebraMap_integer (τ : Gal(L/K)) (c : 𝒪[K]) :
    τ (algebraMap 𝒪[K] L c) = algebraMap 𝒪[K] L c := by
  rw [IsScalarTower.algebraMap_apply 𝒪[K] K L, AlgEquiv.commutes]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [ValuativeExtension K L]
  [FiniteDimensional K L] in
theorem quotient_mk_sum {N : AddSubgroup L} {ι : Type*} [Fintype ι] (g : ι → L) :
    ∑ i, (g i : L ⧸ N) = ((∑ i, g i : L) : L ⧸ N) :=
  (map_sum (QuotientAddGroup.mk' N) g univ).symm

namespace NormalLatticeData

variable (D : NormalLatticeData K L)

attribute [local instance] action

abbrev Q (j : ℕ) : AddSubgroup L := (D.lat (D.k + j + 1)).toAddSubgroup

def grHom (j : ℕ) : D.filt.F j →* Multiplicative (L ⧸ D.Q j) where
  toFun x := Multiplicative.ofAdd ((D.val x - 1 : L) : L ⧸ D.Q j)
  map_one' := by simp [val_one]
  map_mul' x y := by
    rw [← ofAdd_add, ← QuotientAddGroup.mk_add]
    congr 1
    rw [QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
    have e : D.val ((x * y : D.filt.F j) : D.units 0) - 1 - ((D.val x - 1) + (D.val y - 1)) =
        (D.val x - 1) * (D.val y - 1) := by
      rw [Subgroup.coe_mul, val_mul]
      ring
    rw [e]
    exact D.mul_mem_lat (Nat.le_add_right _ _) (D.mem_filt.mp x.2) (D.mem_filt.mp y.2)

theorem grHom_toAdd {j : ℕ} (x : D.filt.F j) :
    (D.grHom j x).toAdd = ((D.val x - 1 : L) : L ⧸ D.Q j) := rfl

theorem grHom_eq_one_iff {j : ℕ} (x : D.filt.F j) :
    D.grHom j x = 1 ↔ (x : D.units 0) ∈ D.filt.F (j + 1) := by
  rw [← toAdd_eq_zero, grHom_toAdd, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup,
    mem_filt]
  rfl

theorem val_coe_smul_F {j : ℕ} (σ : Gal(L/K)) (y : D.filt.F j) :
    D.val ((σ • y : D.filt.F j) : D.units 0) = σ (D.val y) := by
  rw [StableFiltration.coe_smul_F, val_smul]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]
  [FiniteDimensional K L] in

theorem smul_theta_mem (j : ℕ) (c : 𝒪[K]) : c • D.π ^ (D.k + j) • D.θ ∈ D.lat (D.k + j) := by
  have : D.π ^ (D.k + j) • (1 : Gal(L/K)) D.θ ∈ D.lat (D.k + j) := Submodule.subset_span ⟨1, rfl⟩
  simpa using Submodule.smul_mem _ c this

theorem exists_mem_filt (j : ℕ) (c : 𝒪[K]) :
    ∃ y : D.units 0, y ∈ D.filt.F j ∧ D.val y = 1 + c • D.π ^ (D.k + j) • D.θ := by
  obtain ⟨w, hw, -⟩ := D.exists_unit (Nat.le_add_right _ _) (D.smul_theta_mem j c)
  have hw0 : w ∈ D.units 0 := by
    rw [mem_units, hw, add_sub_cancel_left]
    exact D.lat_antitone (Nat.le_add_right _ _) (D.smul_theta_mem j c)
  refine ⟨⟨w, hw0⟩, ?_, hw⟩
  rw [mem_filt]
  show unitVal w - 1 ∈ _
  rw [hw, add_sub_cancel_left]
  exact D.smul_theta_mem j c

theorem subsingleton_tateZero_gr (j : ℕ) : Subsingleton (TateZero Gal(L/K) (D.filt.gr j)) := by
  rw [D.filt.subsingleton_tateZero_gr_iff]
  intro x hx hinv
  obtain ⟨c, hc⟩ := (mem_normalLattice_iff D.π D.θ).mp (D.mem_filt.mp hx)
  have hdiv : ∀ σ : Gal(L/K), D.π ^ 1 ∣ c σ - c 1 := by
    intro σ
    have h1 := D.div_mem_filt_iff.mp (hinv σ)
    rw [← add_assoc] at h1
    have e : D.val (σ • x) - D.val x = D.π ^ (D.k + j) • ∑ τ, (c (σ⁻¹ * τ) - c τ) • τ D.θ := by
      rw [← smul_sum_sub_smul_sum, ← algEquiv_smul_sum, hc, val_smul, map_sub, map_one]
      ring
    rw [e] at h1
    have h2 := (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero
      D.linearIndependent (D.k + j) 1 _).mp h1 σ
    rw [inv_mul_cancel] at h2
    have := dvd_neg.mpr h2
    rwa [neg_sub] at this
  obtain ⟨y, hy, hyv⟩ := D.exists_mem_filt j (c 1)
  refine ⟨y, hy, ?_⟩
  let x' : D.filt.F j := ⟨x, hx⟩
  let y' : D.filt.F j := ⟨y, hy⟩
  have e1 : x / tateNorm Gal(L/K) (D.units 0) y =
      ((x' / tateNorm Gal(L/K) (D.filt.F j) y' : D.filt.F j) : D.units 0) := by
    rw [Subgroup.coe_div, D.filt.coe_tateNorm_F]
  rw [e1, ← grHom_eq_one_iff, map_div, div_eq_one]
  apply Multiplicative.toAdd.injective
  rw [grHom_toAdd, tateNorm_apply, map_prod, toAdd_prod]
  simp_rw [grHom_toAdd, val_coe_smul_F]
  rw [quotient_mk_sum, QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
  have e2 : D.val x' - 1 - ∑ σ : Gal(L/K), (σ (D.val y') - 1) =
      D.π ^ (D.k + j) • ∑ σ, (c σ - c 1) • σ D.θ := by
    show D.val x - 1 - ∑ σ : Gal(L/K), (σ (D.val y) - 1) = _
    rw [← hc, hyv]
    simp only [Algebra.smul_def, map_add, map_one, map_mul, map_pow, map_sub,
      algEquiv_algebraMap_integer, add_sub_cancel_left, Finset.mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun σ _ => ?_
    ring
  rw [e2]
  exact (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero D.linearIndependent
    (D.k + j) 1 _).mpr hdiv

theorem subsingleton_tateNegOne_gr (j : ℕ) : Subsingleton (TateNegOne Gal(L/K) (D.filt.gr j)) := by
  rw [D.filt.subsingleton_tateNegOne_gr_iff]
  intro x hx hN
  obtain ⟨c, hc⟩ := (mem_normalLattice_iff D.π D.θ).mp (D.mem_filt.mp hx)
  let x' : D.filt.F j := ⟨x, hx⟩
  have hN' : ((tateNorm Gal(L/K) (D.filt.F j) x' : D.filt.F j) : D.units 0) ∈ D.filt.F (j + 1) := by
    rwa [D.filt.coe_tateNorm_F]
  rw [← grHom_eq_one_iff, ← toAdd_eq_zero, tateNorm_apply, map_prod, toAdd_prod] at hN'
  simp_rw [grHom_toAdd, val_coe_smul_F] at hN'
  rw [quotient_mk_sum, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup] at hN'
  have e : ∑ σ : Gal(L/K), (σ (D.val x') - 1) =
      D.π ^ (D.k + j) • ∑ τ, (∑ σ : Gal(L/K), c (σ⁻¹ * τ)) • τ D.θ := by
    have h1 : ∀ σ : Gal(L/K), σ (D.val x') - 1 = σ (D.val x' - 1) := fun σ => by
      rw [map_sub, map_one]
    simp_rw [h1]
    show ∑ σ : Gal(L/K), σ (D.val x - 1) = _
    simp_rw [← hc, algEquiv_smul_sum, ← smul_sum]
    rw [sum_comm]
    simp_rw [sum_smul]
  rw [e] at hN'
  have hdiv := (smul_sum_mem_normalLattice_add_iff D.π D.θ D.irreducible.ne_zero
    D.linearIndependent (D.k + j) 1 _).mp hN' 1
  have hsumc : ∑ σ : Gal(L/K), c (σ⁻¹ * 1) = ∑ σ, c σ := by
    simp_rw [mul_one]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun _ => rfl)
  rw [hsumc, pow_one] at hdiv
  obtain ⟨e0, he0⟩ := hdiv
  choose m hm hmv using fun τ => D.exists_mem_filt j (c τ)
  refine ⟨m, hm, ?_⟩
  let m' : Gal(L/K) → D.filt.F j := fun τ => ⟨m τ, hm τ⟩
  have e1 : x / augMap Gal(L/K) (D.units 0) m =
      ((x' / augMap Gal(L/K) (D.filt.F j) m' : D.filt.F j) : D.units 0) := by
    rw [Subgroup.coe_div, D.filt.coe_augMap_F]
  rw [e1, ← grHom_eq_one_iff, map_div, div_eq_one]
  apply Multiplicative.toAdd.injective
  rw [grHom_toAdd, augMap_apply, map_prod, toAdd_prod]
  simp_rw [map_div, toAdd_div, grHom_toAdd, val_coe_smul_F, ← QuotientAddGroup.mk_sub]
  rw [quotient_mk_sum, QuotientAddGroup.eq_iff_sub_mem, Submodule.mem_toAddSubgroup]
  have e2 : D.val x' - 1 - ∑ τ : Gal(L/K), (τ (D.val (m' τ)) - 1 - (D.val (m' τ) - 1)) =
      e0 • D.π ^ (D.k + j + 1) • D.θ := by
    show D.val x - 1 - ∑ τ : Gal(L/K), (τ (D.val (m τ)) - 1 - (D.val (m τ) - 1)) = _
    rw [← hc]
    simp_rw [hmv]
    have he0' : ∑ τ, algebraMap 𝒪[K] L (c τ) = algebraMap 𝒪[K] L D.π * algebraMap 𝒪[K] L e0 := by
      rw [← map_sum, he0, map_mul]
    simp only [Algebra.smul_def, map_add, map_one, map_mul, map_pow,
      algEquiv_algebraMap_integer, add_sub_cancel_left, Finset.mul_sum, sum_sub_distrib]
    have h3 : ∑ τ : Gal(L/K), algebraMap 𝒪[K] L (c τ) * (algebraMap 𝒪[K] L D.π ^ (D.k + j) * D.θ) =
        (∑ τ, algebraMap 𝒪[K] L (c τ)) * (algebraMap 𝒪[K] L D.π ^ (D.k + j) * D.θ) := by
      rw [Finset.sum_mul]
    rw [h3, he0']
    ring_nf
  rw [e2]
  have : D.π ^ (D.k + j + 1) • (1 : Gal(L/K)) D.θ ∈ D.lat (D.k + j + 1) :=
    Submodule.subset_span ⟨1, rfl⟩
  simpa using Submodule.smul_mem _ e0 this

end NormalLatticeData

end Graded

section Main

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] in
open scoped Pointwise in

theorem normalLattice_eq_smul_span (π : 𝒪[K]) (θ : L) (s : ℕ) :
    normalLattice π θ s = π ^ s • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ) := by
  rw [normalLattice, ← Set.smul_set_range, Submodule.span_smul]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] in

theorem span_conjugates_eq_top {θ : L} (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ := by
  have := (basisOfLinearIndependentOfCardEqFinrank hθ
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))).span_eq
  simpa [coe_basisOfLinearIndependentOfCardEqFinrank] using this

namespace NormalLatticeData

variable (D : NormalLatticeData K L)

theorem isOpen_units (j : ℕ) : IsOpen (D.units j : Set 𝒪[L]ˣ) := by
  have h : (D.units j : Set 𝒪[L]ˣ) =
      (fun u : 𝒪[L]ˣ => unitVal u - 1) ⁻¹' (D.lat (D.k + j) : Set L) := rfl
  rw [h]
  exact (isOpen_normalLattice D.π D.θ D.irreducible D.linearIndependent _).preimage
    ((continuous_subtype_val.comp Units.continuous_val).sub continuous_const)

attribute [local instance] action

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L] in

theorem subsingleton_tate :
    Subsingleton (TateZero Gal(L/K) (D.units 0)) ∧ Subsingleton (TateNegOne Gal(L/K) (D.units 0)) :=
  subsingleton_tate_of_complete D.filt D.filt_zero D.filt_complete D.filt_separated
    D.subsingleton_tateZero_gr D.subsingleton_tateNegOne_gr

end NormalLatticeData

open scoped Pointwise in

theorem exists_openSubgroup_units_tateTrivial :
    ∃ (π : 𝒪[K]) (θ : L) (k : ℕ), Irreducible π ∧ (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧
      Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ ∧
      (∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) ∧
      ∃ (V : Subgroup 𝒪[L]ˣ)
        (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, ((w : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L)),
        (∀ u : 𝒪[L]ˣ, u ∈ V ↔
          ((u : 𝒪[L]) : L) - 1 ∈ π ^ k • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ)) ∧
        IsOpen (V : Set 𝒪[L]ˣ) ∧
        (letI := stableUnitsAction V hV;
          Subsingleton (TateZero Gal(L/K) V) ∧ Subsingleton (TateNegOne Gal(L/K) V)) := by
  obtain ⟨D⟩ := NormalLatticeData.nonempty K L
  refine ⟨D.π, D.θ, D.k, D.irreducible, D.linearIndependent,
    span_conjugates_eq_top D.linearIndependent, D.integer, D.units 0, D.units_zero_stable,
    fun u => ?_, D.isOpen_units 0, D.subsingleton_tate⟩
  rw [← normalLattice_eq_smul_span]
  exact Iff.rfl

end Main

end Sec_CompleteTrivialLocal


/-! ### HerbrandCyclic -/
section Sec_HerbrandCyclic

open RHDirect.Stage13CFT_IdeleNormResidue

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

theorem toMul_cycNorm (x : Additive M) :
    (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = tateNorm G M x.toMul := by
  rw [cycNorm_apply, toMul_sum, tateNorm_apply]
  rfl

omit [Fintype G] in

theorem toMul_cycSubOne (σ : G) (x : Additive M) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ x).toMul = σ • x.toMul / x.toMul := by
  rw [cycSubOne_apply]
  rfl

theorem ker_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).ker = (tateNorm G M).ker.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, MonoidHom.mem_ker, ← toMul_cycNorm]
  exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← toMul_zero] at h; exact Additive.toMul.injective h⟩

theorem range_cycNorm_ofMulDistribMulAction :
    (cycNorm (Representation.ofMulDistribMulAction G M)).range =
      (tateNorm G M).range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMul, (toMul_cycNorm x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨Additive.ofMul x, Additive.toMul.injective ?_⟩
    rw [toMul_cycNorm]
    exact hx

variable {σ : G}

omit [Fintype G] in

theorem ker_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker =
      (invariants G M).toAddSubgroup := by
  ext x
  rw [mem_ker_cycSubOne_iff _ hσ, Additive.mem_toAddSubgroup, mem_invariants]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  exact ⟨fun h g => congrArg Additive.toMul (h g), fun h g => by rw [h g]; rfl⟩

omit [Fintype G] in

theorem range_cycSubOne_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range =
      (augmentation G M).toAddSubgroup := by
  rw [range_cycSubOne_eq_closure _ hσ, augmentation, Subgroup.toAddSubgroup_closure]
  congr 1

theorem natCard_tateZero_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateZero G M) =
      Nat.card (CycTateZero (Representation.ofMulDistribMulAction G M) σ) := by
  change (tateNorm G M).range.relIndex (invariants G M) =
    (cycNorm (Representation.ofMulDistribMulAction G M)).range.relIndex
      (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker
  rw [ker_cycSubOne_ofMulDistribMulAction hσ, range_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]

theorem natCard_tateNegOne_eq (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateNegOne G M) =
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction G M) σ) := by
  change (augmentation G M).relIndex (tateNorm G M).ker =
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range.relIndex
      (cycNorm (Representation.ofMulDistribMulAction G M)).ker
  rw [range_cycSubOne_ofMulDistribMulAction hσ, ker_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]

theorem cycHerbrand_ofMulDistribMulAction (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (Representation.ofMulDistribMulAction G M) σ =
      (Nat.card (TateZero G M) : ℚ) / Nat.card (TateNegOne G M) := by
  rw [cycHerbrand_eq, natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]

private theorem finite_iff_natCard_ne_zero {X : Type*} [Nonempty X] :
    Finite X ↔ Nat.card X ≠ 0 := by
  rw [Nat.card_ne_zero]
  exact ⟨fun h => ⟨inferInstance, h⟩, fun h => h.2⟩

theorem hasHerbrandQuotient_iff (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      Finite (TateZero G M) ∧ Finite (TateNegOne G M) := by
  rw [HasHerbrandQuotient, finite_iff_natCard_ne_zero, finite_iff_natCard_ne_zero,
    finite_iff_natCard_ne_zero (X := TateZero G M), finite_iff_natCard_ne_zero (X := TateNegOne G M),
    natCard_tateZero_eq hσ, natCard_tateNegOne_eq hσ]

theorem cycHerbrand_eq_one_of_subsingleton (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    [Subsingleton (TateZero G M)] [Subsingleton (TateNegOne G M)] :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) σ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ = 1 := by
  refine ⟨(hasHerbrandQuotient_iff hσ).mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hσ, Nat.card_unique, Nat.card_unique]
  norm_num

section Injective

variable {N : Type*} [CommGroup N] [MulDistribMulAction G N]

omit [Fintype G] in

theorem toAdditive_cycSubOne (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) (τ : G)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x) =
      cycSubOne (Representation.ofMulDistribMulAction G N) τ (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycSubOne]
  change i (cycSubOne (Representation.ofMulDistribMulAction G M) τ x).toMul = _
  rw [toMul_cycSubOne, map_div, hi]
  rfl

theorem toAdditive_cycNorm (i : M →* N) (hi : ∀ (g : G) (x : M), i (g • x) = g • i x)
    (x : Additive M) :
    MonoidHom.toAdditive i (cycNorm (Representation.ofMulDistribMulAction G M) x) =
      cycNorm (Representation.ofMulDistribMulAction G N) (MonoidHom.toAdditive i x) := by
  apply Additive.toMul.injective
  rw [toMul_cycNorm]
  change i (cycNorm (Representation.ofMulDistribMulAction G M) x).toMul = _
  rw [toMul_cycNorm, tateNorm_apply, tateNorm_apply, map_prod]
  simp_rw [hi]
  rfl

private theorem range_toAdditive (i : M →* N) :
    (MonoidHom.toAdditive i).range = i.range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨x.toMul, by rw [← hx]; rfl⟩,
    fun ⟨x, hx⟩ => ⟨Additive.ofMul x, Additive.toMul.injective hx⟩⟩

theorem cycHerbrand_eq_of_injective (i : M →* N) (hinj : Function.Injective i)
    (hi : ∀ (g : G) (x : M), i (g • x) = g • i x) [i.range.FiniteIndex] (τ : G) :
    (HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G M) τ)
        (cycNorm (Representation.ofMulDistribMulAction G M)) ↔
      HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction G N) τ)
        (cycNorm (Representation.ofMulDistribMulAction G N))) ∧
    cycHerbrand (Representation.ofMulDistribMulAction G M) τ =
      cycHerbrand (Representation.ofMulDistribMulAction G N) τ := by
  have hfi : (MonoidHom.toAdditive i).range.FiniteIndex := by
    constructor
    rw [range_toAdditive, Subgroup.index_toAddSubgroup]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : Finite (Additive N ⧸ (MonoidHom.toAdditive i).range) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  have hinj' : Function.Injective (MonoidHom.toAdditive i) := hinj
  exact ⟨hasHerbrandQuotient_iff_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ),
    herbrandQuotient_eq_of_injective_of_finite hinj' (toAdditive_cycSubOne i hi τ)
      (toAdditive_cycNorm i hi) (cycSubOne_cycNorm _ τ) (cycNorm_cycSubOne _ τ)⟩

end Injective

end Sec_HerbrandCyclic


/-! ### HerbrandLocalBase -/
section Sec_HerbrandLocalBase

open ValuativeRel RHDirect.Stage13CFT_IdeleNormResidue

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def unitsToTateZero : Kˣ →* TateZero (L ≃ₐ[K] L) Lˣ :=
  (QuotientGroup.mk' _).comp
    ((Units.map (algebraMap K L : K →* L)).codRestrict (invariants (L ≃ₐ[K] L) Lˣ) fun a g => by
      ext
      simp [AlgEquiv.smul_units_def])

theorem coe_tateNorm_units (x : Lˣ) :
    ((tateNorm (L ≃ₐ[K] L) Lˣ x : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L)) := by
  rw [algebraMap_norm_eq_prod, tateNorm_apply, Units.coe_prod]
  rfl

theorem unitsToTateZero_surjective : Function.Surjective (unitsToTateZero (K := K) (L := L)) := by
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hfix : ∀ y : L, (∀ g : L ≃ₐ[K] L, g y = y) → ∃ a : K, algebraMap K L a = y := fun y hy =>
    (IsGalois.mem_range_algebraMap_iff_fixed y).mpr hy
  obtain ⟨a, ha⟩ := hfix (x : L) fun g => congrArg Units.val (hx g)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact x.ne_zero ha.symm
  exact ⟨Units.mk0 a ha0, congrArg (QuotientGroup.mk' _) (Subtype.ext (Units.ext ha))⟩

theorem ker_unitsToTateZero : (unitsToTateZero (K := K) (L := L)).ker = (normUnits K L).range := by
  ext a
  rw [MonoidHom.mem_ker, unitsToTateZero, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Units.ext ((algebraMap K L).injective ?_)⟩
    rw [coe_normUnits, ← coe_tateNorm_units, hy]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨y, Units.ext ?_⟩
    rw [coe_tateNorm_units]
    rfl

theorem natCard_tateZero_units_eq :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Nat.card (Kˣ ⧸ (normUnits K L).range) := by
  rw [← ker_unitsToTateZero]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ unitsToTateZero_surjective).toEquiv.symm

end Galois

section Ord

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

variable (L) in

def unitsOrd : Additive Lˣ →+ ℤ where
  toFun x := ord ((x.toMul : Lˣ) : L)
  map_zero' := by
    exact ord_unit (K := L) 1
  map_add' x y := by
    change ord (((x.toMul * y.toMul : Lˣ)) : L) = _
    rw [Units.val_mul, ord_mul x.toMul.ne_zero y.toMul.ne_zero]

theorem unitsOrd_ofMul (x : Lˣ) : unitsOrd L (Additive.ofMul x) = ord (x : L) :=
  rfl

theorem unitsOrd_surjective : Function.Surjective (unitsOrd L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  intro n
  refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
  rw [map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]

theorem ord_eq_zero_iff_mem_range_unitsIncl (x : Lˣ) :
    ord (x : L) = 0 ↔ x ∈ (unitsIncl L).range := by
  rw [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero, ← MonoidHom.range_eq_map]

theorem exact_unitsIncl_unitsOrd :
    Function.Exact (MonoidHom.toAdditive (unitsIncl L)) (unitsOrd L) := by
  intro y
  change ord ((y.toMul : Lˣ) : L) = 0 ↔ _
  rw [ord_eq_zero_iff_mem_range_unitsIncl]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.toMul, rfl⟩

end Ord

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem ord_algEquiv (σ : L ≃ₐ[K] L) (x : L) : ord (σ x) = ord x := by
  rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
    valuation_algEquiv_apply K L σ x]

theorem unitsOrd_smul (σ : L ≃ₐ[K] L) (x : Lˣ) :
    unitsOrd L (Additive.ofMul (σ • x)) = unitsOrd L (Additive.ofMul x) := by
  rw [unitsOrd_ofMul, unitsOrd_ofMul, AlgEquiv.smul_units_def, Units.coe_map]
  exact ord_algEquiv σ x

theorem unitsOrd_cycSubOne (τ : L ≃ₐ[K] L) (x : Additive Lˣ) :
    unitsOrd L (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) τ x) =
      cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) τ (unitsOrd L x) := by
  rw [cycSubOne_apply, cycSubOne_apply, map_sub, Representation.ofMulDistribMulAction_apply_apply,
    unitsOrd_smul, Representation.trivial_apply]
  rfl

theorem unitsOrd_cycNorm (x : Additive Lˣ) :
    unitsOrd L (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) x) =
      cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) (unitsOrd L x) := by
  rw [cycNorm_apply, cycNorm_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Representation.ofMulDistribMulAction_apply_apply, unitsOrd_smul, Representation.trivial_apply]
  rfl

variable {σ : L ≃ₐ[K] L}

theorem cycHerbrand_units_eq_mul (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hA : HasHerbrandQuotient
      (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
      (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ))) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ *
          Fintype.card (L ≃ₐ[K] L) := by
  have hi : Function.Injective (MonoidHom.toAdditive (unitsIncl L)) := unitsIncl_injective
  have hC : HasHerbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) :=
    hasCyclicHerbrand_of_finite (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) hσ
  have hCv : herbrandQuotient (cycSubOne (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ) σ)
      (cycNorm (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) = Fintype.card (L ≃ₐ[K] L) :=
    cyclicHerbrand_trivial_int σ
  refine ⟨HasHerbrandQuotient.of_shortExact_left_right hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, ?_⟩
  rw [cycHerbrand, herbrandQuotient_eq_mul_of_shortExact hi unitsOrd_surjective
    exact_unitsIncl_unitsOrd (toAdditive_cycSubOne _ unitsIncl_smul σ)
    (toAdditive_cycNorm _ unitsIncl_smul) (unitsOrd_cycSubOne σ) unitsOrd_cycNorm
    (cycSubOne_cycNorm _ σ) (cycNorm_cycSubOne _ σ) hA hC, hCv]
  rfl

theorem cycHerbrand_integerUnits_eq_one_of_subgroup (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (V : Subgroup 𝒪[L]ˣ) [V.FiniteIndex] [MulDistribMulAction (L ≃ₐ[K] L) V]
    (hV : ∀ (g : L ≃ₐ[K] L) (v : V), ((g • v : V) : 𝒪[L]ˣ) = g • (v : 𝒪[L]ˣ))
    [Subsingleton (TateZero (L ≃ₐ[K] L) V)] [Subsingleton (TateNegOne (L ≃ₐ[K] L) V)] :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  have : V.subtype.range.FiniteIndex := by rw [Subgroup.range_subtype]; infer_instance
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_injective V.subtype V.subtype_injective hV σ
  obtain ⟨h3, h4⟩ := cycHerbrand_eq_one_of_subsingleton (G := L ≃ₐ[K] L) (M := V) hσ
  exact ⟨h1.mp h3, h2.symm.trans h4⟩

end Sec_HerbrandLocalBase


/-! ### HerbrandLocal -/
section Sec_HerbrandLocal

open ValuativeRel RHDirect.Stage13CFT_IdeleNormResidue

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] in

theorem finiteIndex_of_isOpen_integerUnits {V : Subgroup 𝒪[L]ˣ} (h : IsOpen (V : Set 𝒪[L]ˣ)) :
    V.FiniteIndex := by
  have : Finite (𝒪[L]ˣ ⧸ V) := Subgroup.quotient_finite_of_isOpen V h
  exact Subgroup.finiteIndex_of_finite_quotient

variable [IsGalois K L] {σ : L ≃ₐ[K] L}

theorem cycHerbrand_integerUnits_eq_one (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) 𝒪[L]ˣ) σ = 1 := by
  obtain ⟨-, -, -, -, -, -, -, V, hV, -, hopen, hT⟩ :=
    exists_openSubgroup_units_tateTrivial (K := K) (L := L)
  let := stableUnitsAction V hV
  have := finiteIndex_of_isOpen_integerUnits hopen
  have := hT.1
  have := hT.2
  exact cycHerbrand_integerUnits_eq_one_of_subgroup hσ V
    fun g v => Units.ext (Subtype.ext (unitVal_smul V hV g v))

theorem cycHerbrand_units_eq_finrank (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) σ =
        Module.finrank K L := by
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hσ
  obtain ⟨hB, h2⟩ := cycHerbrand_units_eq_mul hσ hA
  refine ⟨hB, ?_⟩
  rw [h2, h1, one_mul, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

variable [IsCyclic (L ≃ₐ[K] L)]

theorem natCard_tateZero_integerUnits_eq :
    Finite (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) ∧ Finite (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) ∧
      Nat.card (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) = Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  obtain ⟨hA, h1⟩ := cycHerbrand_integerUnits_eq_one hτ
  obtain ⟨f0, f1⟩ := (hasHerbrandQuotient_iff hτ).mp hA
  refine ⟨f0, f1, ?_⟩
  rw [cycHerbrand_ofMulDistribMulAction hτ] at h1
  have h0 : (Nat.card (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  exact_mod_cast (div_eq_one_iff_eq h0).mp h1

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L] in

theorem natCard_tateNegOne_units : Nat.card (TateNegOne (L ≃ₐ[K] L) Lˣ) = 1 := by
  have := subsingleton_tateNegOne_units (K := K) (L := L)
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem natCard_tateZero_units :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Module.finrank K L := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have h := (cycHerbrand_units_eq_finrank hτ).2
  rw [cycHerbrand_ofMulDistribMulAction hτ, natCard_tateNegOne_units, Nat.cast_one, div_one] at h
  exact_mod_cast h

theorem natCard_units_quotient_range_normUnits :
    Nat.card (Kˣ ⧸ (normUnits K L).range) = Module.finrank K L := by
  rw [← natCard_tateZero_units_eq]
  exact natCard_tateZero_units

end Sec_HerbrandLocal


end RHDirect.CFT.LocalField
