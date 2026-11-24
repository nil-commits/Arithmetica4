import RHDirect.Stage5AdelicTate
import RHDirect.Stage11DefiniteUnitaryChain
import RHDirect.Stage12GaloisShaLen
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# RHDirect.Stage14M1_CMFieldAdeles

Field-2 Package M1 (Wave 1, Module 1 of 6): **CM Host Fields, Restricted Product Rings,
CM Finite Adeles, Adelic Haar/Tamagawa Measures, and the Unconditional Unit Product Formula**
in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`, zero `opaque`.

## Contents

1. **`CMHostField` (Totally Real / Totally Complex Quadratic CM Extensions `E / F`)**:
   - Concrete `CMHostField` packaging `[NumberField F] [IsTotallyReal F]`,
     `[NumberField E] [IsTotallyComplex E]`, `[Algebra F E]`, and `Module.finrank F E = 2`.
   - Canonical CM involution `C.conj : C.E ≃ₐ[C.F] C.E`, involutivity, non-triviality,
     norm/trace identities (`x * C.conj x = N_{E/F}(x)`, `x + C.conj x = Tr_{E/F}(x)`),
     and proof of complex-conjugation compatibility `σ (C.conj x) = star (σ x)` for every
     complex embedding `σ : C.E →+* ℂ` and `w (C.conj x) = w x` at every infinite place.
   - Restriction `C.conjRingOfIntegers : 𝓞 C.E ≃+* 𝓞 C.E`, induced action on height-one primes
     `C.conjHeightOne : HeightOneSpectrum (𝓞 C.E) ≃ HeightOneSpectrum (𝓞 C.E)`, place splitting
     classification (`IsSplitPlace`, `IsInertOrRamifiedPlace`, quadratic character `chiEF`),
     and concrete witness `gaussianCMHostField : CMHostField` (`ℚ(ζ_4)/ℚ`).

2. **`RestrictedProdRing` (General Restricted Products of Commutative Topological Rings)**:
   - Concrete `RestrictedProdRing ι R O := Πʳ i, [R i, (O i : Set (R i))]` with `CommRing`,
     `TopologicalSpace`, `IsTopologicalRing`, integral subring `integralSubring`, unit
     characterization, functorial `map` and `congr`, and `finAdeleEquiv`.

3. **`FiniteAdelesCM`, Adelic Hermitian Forms, & `AdelicPair`**:
   - Concrete `FiniteAdelesCM C` bundling `FiniteAdeleRing (𝓞 C.F) C.F`,
     `FiniteAdeleRing (𝓞 C.E) C.E`, Alpöge's base-change tensor ring `RA C.F C.E`,
     full adele rings `Adele F`, `Adele E`, integral finite adeles, CM involution on adeles,
     Hermitian forms (`IsHermForm`, `IsHermHyperbolic`), and `AdelicPair`.

4. **`AdelicMeasureData` & `tamagawaFactor_pos`**:
   - Concrete local/global Haar & Tamagawa measure normalizations for `F` and `E`,
     exact normalized lattice covolume `additiveTamagawaVolF_eq_one` /
     `additiveTamagawaVolE_eq_one` via `NumberField.mixedEmbedding.covolume_integerLattice`,
     local unitary Euler factors, and unconditional positivity `tamagawaFactor_pos`.

5. **`adelic_product_formula_unit` (Product Formula `∏_v |x|_v = 1` for Units & Places)**:
   - Grounded on `Stage5AdelicTate.artin_whaples_product_formula` and `ideleNorm_principal`:
     full product formula for `x : C.Eˣ` and `x : C.Fˣ`, unit finite-place triviality
     (`finiteAbsVal v u = 1`), archimedean unit product `∏_{w∣∞} |u|_w = 1`, CM involution
     invariance, norm-1 unitary elements, and relative norm compatibility.
-/

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Matrix
open scoped BigOperators NumberField Topology Real RestrictedProduct TensorProduct

namespace RHDirect.Stage14M1_CMFieldAdeles

/-! ## Section 1: Concrete CM Host Fields (`CMHostField`) -/

section CMHostFieldSection

/-- A concrete CM host-field extension `E / F`: `F` is a totally real number field, `E` is a
totally complex number field, and `[E : F] = 2`. -/
structure CMHostField : Type 1 where
  F : Type
  E : Type
  [fieldF : Field F]
  [nfF : NumberField F]
  [totallyRealF : IsTotallyReal F]
  [fieldE : Field E]
  [nfE : NumberField E]
  [totallyComplexE : IsTotallyComplex E]
  [algFE : Algebra F E]
  finrank_eq_two : Module.finrank F E = 2

attribute [instance] CMHostField.fieldF CMHostField.nfF CMHostField.totallyRealF
  CMHostField.fieldE CMHostField.nfE CMHostField.totallyComplexE CMHostField.algFE

namespace CMHostField

section QuadraticHelpers

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Candidate linear involution `x ↦ algebraMap F E (Tr_{E/F}(x)) - x`. -/
def conjLinear (F E : Type*) [Field F] [CommRing E] [Algebra F E] : E →ₗ[F] E :=
  (Algebra.linearMap F E).comp (Algebra.trace F E) - LinearMap.id

theorem conjLinear_apply (x : E) :
    conjLinear F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

lemma trace_algebraMap_two (h2 : Module.finrank F E = 2) (c : F) :
    Algebra.trace F E (algebraMap F E c) = 2 * c := by
  rw [Algebra.trace_algebraMap, h2, nsmul_eq_mul]
  norm_num

lemma conjLinear_algebraMap (h2 : Module.finrank F E = 2) (c : F) :
    conjLinear F E (algebraMap F E c) = algebraMap F E c := by
  rw [conjLinear_apply, trace_algebraMap_two h2, map_mul, map_ofNat]
  ring

lemma conjLinear_one (h2 : Module.finrank F E = 2) :
    conjLinear F E 1 = 1 := by
  simpa using conjLinear_algebraMap (F := F) (E := E) h2 1

lemma linearIndependent_one_of_not_mem {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : LinearIndependent F ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact one_ne_zero ((smul_eq_zero.mp hst).resolve_left hs)
  · exfalso
    apply hx
    refine ⟨-(s / t), ?_⟩
    have h1 : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.algebraMap_eq_smul_one]
    have h2 : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

def basisOneOf (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : Module.Basis (Fin 2) F E :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_not_mem hx)
    (by rw [h2, Fintype.card_fin])

lemma basisOneOf_zero (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf h2 hx 0 = 1 := by
  simp [basisOneOf]

lemma basisOneOf_one (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf h2 hx 1 = x := by
  simp [basisOneOf]

lemma sq_eq_of_not_mem (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) :
    x * x = algebraMap F E ((basisOneOf h2 hx).repr (x * x) 0) +
      algebraMap F E ((basisOneOf h2 hx).repr (x * x) 1) * x := by
  conv_lhs => rw [← (basisOneOf h2 hx).sum_repr (x * x)]
  rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
    mul_one]

lemma repr_self_zero (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : (basisOneOf h2 hx).repr x 0 = 0 := by
  have h := (basisOneOf h2 hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

lemma repr_self_one (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : (basisOneOf h2 hx).repr x 1 = 1 := by
  have h := (basisOneOf h2 hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

lemma trace_eq_of_not_mem (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.trace F E x = (basisOneOf h2 hx).repr (x * x) 1 := by
  rw [Algebra.trace_eq_matrix_trace (basisOneOf h2 hx), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, zero_add]

lemma norm_eq_of_not_mem (h2 : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf h2 hx).repr (x * x) 0 := by
  rw [Algebra.norm_eq_matrix_det (basisOneOf h2 hx), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, repr_self_one]
  ring

lemma conjLinear_mul_self (h2 : Module.finrank F E = 2) (x : E) :
    conjLinear F E (x * x) = conjLinear F E x * conjLinear F E x := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [← map_mul, conjLinear_algebraMap h2, conjLinear_algebraMap h2, map_mul]
  · have hsq := sq_eq_of_not_mem h2 hx
    have htr : Algebra.trace F E x = (basisOneOf h2 hx).repr (x * x) 1 :=
      trace_eq_of_not_mem h2 hx
    have htr2 : Algebra.trace F E (x * x) = 2 * (basisOneOf h2 hx).repr (x * x) 0 +
        (basisOneOf h2 hx).repr (x * x) 1 * (basisOneOf h2 hx).repr (x * x) 1 := by
      conv_lhs => rw [hsq]
      rw [map_add, trace_algebraMap_two h2, ← Algebra.smul_def, map_smul, htr, smul_eq_mul]
    rw [conjLinear_apply, conjLinear_apply, htr2, htr]
    simp only [map_add, map_mul, map_ofNat]
    linear_combination (-2 : E) * hsq

lemma conjLinear_mul (h2 : Module.finrank F E = 2) (x y : E) :
    conjLinear F E (x * y) = conjLinear F E x * conjLinear F E y := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conjLinear_algebraMap h2, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  · have key : (conjLinear F E).comp (LinearMap.mulLeft F x) =
        (LinearMap.mulLeft F (conjLinear F E x)).comp (conjLinear F E) := by
      refine (basisOneOf h2 hx).ext fun i => ?_
      fin_cases i
      · simp [basisOneOf_zero, conjLinear_one h2]
      · simp only [Fin.mk_one, basisOneOf_one, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply]
        exact conjLinear_mul_self h2 x
    exact LinearMap.congr_fun key y

lemma conjLinear_conjLinear (h2 : Module.finrank F E = 2) (x : E) :
    conjLinear F E (conjLinear F E x) = x := by
  rw [conjLinear_apply, conjLinear_apply x, map_sub, trace_algebraMap_two h2, map_sub,
    map_mul, map_ofNat]
  ring

end QuadraticHelpers

variable (C : CMHostField)

/-- The canonical CM complex conjugation `C.conj : C.E ≃ₐ[C.F] C.E`. -/
def conj : C.E ≃ₐ[C.F] C.E :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (conjLinear C.F C.E) (conjLinear_conjLinear C.finrank_eq_two))
    (conjLinear_one C.finrank_eq_two)
    (conjLinear_mul C.finrank_eq_two)

theorem conj_apply (x : C.E) :
    C.conj x = algebraMap C.F C.E (Algebra.trace C.F C.E x) - x := rfl

@[simp]
theorem conj_conj (x : C.E) : C.conj (C.conj x) = x :=
  conjLinear_conjLinear C.finrank_eq_two x

theorem conj_algebraMap (a : C.F) :
    C.conj (algebraMap C.F C.E a) = algebraMap C.F C.E a :=
  C.conj.commutes a

/-- Relative CM trace `Tr_{E/F} : E →ₗ[F] F`. -/
def cmTrace : C.E →ₗ[C.F] C.F := Algebra.trace C.F C.E

/-- Relative CM norm `N_{E/F} : E →* F`. -/
def cmNorm : C.E →* C.F := Algebra.norm C.F

theorem cmTrace_eq_add_conj (x : C.E) :
    algebraMap C.F C.E (C.cmTrace x) = x + C.conj x := by
  change algebraMap C.F C.E (Algebra.trace C.F C.E x) =
    x + (algebraMap C.F C.E (Algebra.trace C.F C.E x) - x)
  ring

theorem cmNorm_eq_mul_conj (x : C.E) :
    algebraMap C.F C.E (C.cmNorm x) = x * C.conj x := by
  by_cases hx : x ∈ Set.range (algebraMap C.F C.E)
  · obtain ⟨c, rfl⟩ := hx
    rw [cmNorm, Algebra.norm_algebraMap, C.finrank_eq_two, C.conj_algebraMap, map_pow, sq]
  · have hsq := sq_eq_of_not_mem C.finrank_eq_two hx
    have htr := trace_eq_of_not_mem C.finrank_eq_two hx
    have hnm := norm_eq_of_not_mem C.finrank_eq_two hx
    change algebraMap C.F C.E (Algebra.norm C.F x) =
      x * (algebraMap C.F C.E (Algebra.trace C.F C.E x) - x)
    rw [hnm, htr, map_neg]
    linear_combination hsq

theorem trace_conj (x : C.E) : C.cmTrace (C.conj x) = C.cmTrace x := by
  apply FaithfulSMul.algebraMap_injective C.F C.E
  rw [C.cmTrace_eq_add_conj, C.cmTrace_eq_add_conj, C.conj_conj, add_comm]

theorem norm_conj (x : C.E) : C.cmNorm (C.conj x) = C.cmNorm x := by
  apply FaithfulSMul.algebraMap_injective C.F C.E
  rw [C.cmNorm_eq_mul_conj, C.cmNorm_eq_mul_conj, C.conj_conj, mul_comm]

theorem exists_not_mem_range : ∃ x : C.E, x ∉ Set.range (algebraMap C.F C.E) := by
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective (Algebra.linearMap C.F C.E) := hall
  have h1 := LinearMap.finrank_range_le (Algebra.linearMap C.F C.E)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, C.finrank_eq_two] at h1
  omega

theorem mem_range_of_conj_eq {x : C.E} (hx : C.conj x = x) :
    x ∈ Set.range (algebraMap C.F C.E) := by
  refine ⟨C.cmTrace x / 2, ?_⟩
  have h2 := C.cmTrace_eq_add_conj x
  rw [hx] at h2
  rw [map_div₀, h2, map_ofNat]
  field_simp
  ring

theorem conj_ne_id : C.conj ≠ AlgEquiv.refl := by
  intro h
  obtain ⟨x, hx⟩ := C.exists_not_mem_range
  exact hx (C.mem_range_of_conj_eq (by rw [h]; rfl))

theorem finrank_Q_E : Module.finrank ℚ C.E = 2 * Module.finrank ℚ C.F := by
  have hmul := Module.finrank_mul_finrank ℚ C.F C.E
  rw [C.finrank_eq_two, mul_comm] at hmul
  exact hmul.symm

theorem infinitePlace_F_isReal (u : InfinitePlace C.F) : u.IsReal :=
  IsTotallyReal.isReal u

theorem infinitePlace_E_isComplex (w : InfinitePlace C.E) : w.IsComplex :=
  IsTotallyComplex.isComplex w

theorem nrComplexPlaces_F : InfinitePlace.nrComplexPlaces C.F = 0 :=
  IsTotallyReal.nrComplexPlaces_eq_zero C.F

theorem nrRealPlaces_E : InfinitePlace.nrRealPlaces C.E = 0 :=
  IsTotallyComplex.nrRealPlaces_eq_zero C.E

theorem nrRealPlaces_F_eq_finrank :
    InfinitePlace.nrRealPlaces C.F = Module.finrank ℚ C.F := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank C.F
  rw [C.nrComplexPlaces_F, mul_zero, add_zero] at h
  exact h

theorem nrComplexPlaces_E_eq_finrank :
    InfinitePlace.nrComplexPlaces C.E = Module.finrank ℚ C.F := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank C.E
  rw [C.nrRealPlaces_E, zero_add, C.finrank_Q_E] at h
  omega

theorem card_infinitePlace_F :
    Fintype.card (InfinitePlace C.F) = Module.finrank ℚ C.F := by
  have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces C.F
  rw [h, C.nrComplexPlaces_F, add_zero, C.nrRealPlaces_F_eq_finrank]

theorem card_infinitePlace_E :
    Fintype.card (InfinitePlace C.E) = Module.finrank ℚ C.F := by
  have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces C.E
  rw [h, C.nrRealPlaces_E, zero_add, C.nrComplexPlaces_E_eq_finrank]

theorem card_infinitePlace_eq :
    Fintype.card (InfinitePlace C.E) = Fintype.card (InfinitePlace C.F) := by
  rw [C.card_infinitePlace_E, C.card_infinitePlace_F]

/-- **Complex-conjugation compatibility**: every complex embedding `σ : E →+* ℂ` intertwines
`C.conj` with `starRingEnd ℂ`! -/
theorem embedding_conj (σ : C.E →+* ℂ) (x : C.E) :
    σ (C.conj x) = star (σ x) := by
  have hF_real : ∀ a : C.F, star (σ (algebraMap C.F C.E a)) = σ (algebraMap C.F C.E a) := by
    intro a
    have hisreal : ComplexEmbedding.IsReal (σ.comp (algebraMap C.F C.E)) := by
      rw [← InfinitePlace.isReal_mk_iff]
      exact C.infinitePlace_F_isReal _
    rw [ComplexEmbedding.isReal_iff] at hisreal
    exact congrArg (fun f : C.F →+* ℂ => f a) hisreal
  have hE_cplx : ¬ ComplexEmbedding.IsReal σ := by
    rw [← InfinitePlace.isReal_mk_iff]
    exact (InfinitePlace.not_isReal_iff_isComplex).mpr (C.infinitePlace_E_isComplex _)
  have hne : ComplexEmbedding.conjugate σ ≠ σ := by
    rwa [ComplexEmbedding.isReal_iff] at hE_cplx
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : C.E, star (σ x₀) ≠ σ x₀ := by
    by_contra h
    push Not at h
    apply hne
    ext y
    exact h y
  have hx₀_not : x₀ ∉ Set.range (algebraMap C.F C.E) := by
    rintro ⟨a, rfl⟩
    exact hx₀ (hF_real a)
  have hquad : (star (σ x₀) - σ x₀) * (star (σ x₀) - σ (C.conj x₀)) = 0 := by
    have hmul : σ (x₀ * C.conj x₀) = σ (algebraMap C.F C.E (C.cmNorm x₀)) := by
      rw [C.cmNorm_eq_mul_conj]
    have hadd : σ (x₀ + C.conj x₀) = σ (algebraMap C.F C.E (C.cmTrace x₀)) := by
      rw [C.cmTrace_eq_add_conj]
    have hstar_mul : star (σ x₀) * star (σ x₀) -
        star (σ (algebraMap C.F C.E (C.cmTrace x₀))) * star (σ x₀) +
        star (σ (algebraMap C.F C.E (C.cmNorm x₀))) = 0 := by
      have h0 : σ x₀ * σ x₀ - σ (algebraMap C.F C.E (C.cmTrace x₀)) * σ x₀ +
          σ (algebraMap C.F C.E (C.cmNorm x₀)) = 0 := by
        rw [← hadd, ← hmul]
        simp only [map_add, map_mul]
        ring
      have hs := congrArg (starRingEnd ℂ) h0
      simpa only [map_add, map_sub, map_mul, map_zero, starRingEnd_apply] using hs
    rw [hF_real, hF_real] at hstar_mul
    have hsum_eq : σ (algebraMap C.F C.E (C.cmTrace x₀)) = σ x₀ + σ (C.conj x₀) := by
      rw [← hadd, map_add]
    have hprod_eq : σ (algebraMap C.F C.E (C.cmNorm x₀)) = σ x₀ * σ (C.conj x₀) := by
      rw [← hmul, map_mul]
    rw [hsum_eq, hprod_eq] at hstar_mul
    linear_combination hstar_mul
  have hx₀_conj : star (σ x₀) = σ (C.conj x₀) := by
    rcases mul_eq_zero.mp hquad with h | h
    · exact absurd (sub_eq_zero.mp h) hx₀
    · exact sub_eq_zero.mp h
  let b := basisOneOf C.finrank_eq_two hx₀_not
  have hrepr : x = algebraMap C.F C.E (b.repr x 0) + algebraMap C.F C.E (b.repr x 1) * x₀ := by
    conv_lhs => rw [← b.sum_repr x]
    rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
      mul_one]
  conv_lhs => rw [hrepr]
  conv_rhs => rw [hrepr]
  simp only [map_add, map_mul, C.conj_algebraMap, star_add, star_mul', hF_real, hx₀_conj]

theorem infinitePlace_conj (w : InfinitePlace C.E) (x : C.E) :
    w (C.conj x) = w x := by
  have h1 : w (C.conj x) = ‖w.embedding (C.conj x)‖ :=
    (InfinitePlace.norm_embedding_eq w (C.conj x)).symm
  have h2 : w x = ‖w.embedding x‖ := (InfinitePlace.norm_embedding_eq w x).symm
  rw [h1, h2, C.embedding_conj, norm_star]

/-- Restriction of `C.conj` to the ring of integers `𝓞 C.E`. -/
def conjRingOfIntegers : 𝓞 C.E ≃+* 𝓞 C.E :=
  RingOfIntegers.mapRingEquiv C.conj.toRingEquiv

@[simp]
theorem conjRingOfIntegers_coe (x : 𝓞 C.E) :
    ((C.conjRingOfIntegers x : 𝓞 C.E) : C.E) = C.conj (x : C.E) := rfl

theorem conjRingOfIntegers_invol (x : 𝓞 C.E) :
    C.conjRingOfIntegers (C.conjRingOfIntegers x) = x := by
  ext
  simp

/-- Induced involution on global units `C.Eˣ`. -/
def conjUnits : C.Eˣ ≃* C.Eˣ := Units.mapEquiv C.conj.toMulEquiv

/-- Induced involution on integral units `(𝓞 C.E)ˣ`. -/
def conjIntUnits : (𝓞 C.E)ˣ ≃* (𝓞 C.E)ˣ := Units.mapEquiv C.conjRingOfIntegers.toMulEquiv

/-- For any ring isomorphism `e : R ≃+* S`, `I.map e.toRingHom = I.comap e.symm.toRingHom`. -/
lemma ideal_map_ringEquiv_eq_comap {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    I.map e.toRingHom = I.comap e.symm.toRingHom := by
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    change e.symm (e x) ∈ I
    simpa using hx
  · intro x hx
    change e.symm x ∈ I at hx
    rw [← e.apply_symm_apply x]
    exact Ideal.mem_map_of_mem e.toRingHom hx

/-- Action of `C.conj` on height-one prime ideals `HeightOneSpectrum (𝓞 C.E)`. -/
def conjHeightOne : HeightOneSpectrum (𝓞 C.E) ≃ HeightOneSpectrum (𝓞 C.E) where
  toFun v :=
    { asIdeal := v.asIdeal.map C.conjRingOfIntegers.toRingHom
      isPrime := by
        rw [ideal_map_ringEquiv_eq_comap]
        exact Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        apply v.ne_bot
        have h0 : (v.asIdeal.map C.conjRingOfIntegers.toRingHom).map
            C.conjRingOfIntegers.symm.toRingHom = v.asIdeal := by
          rw [Ideal.map_map]
          have hc : C.conjRingOfIntegers.symm.toRingHom.comp C.conjRingOfIntegers.toRingHom =
              RingHom.id _ := by ext x; simp
          rw [hc, Ideal.map_id]
        rw [hbot, Ideal.map_bot] at h0
        exact h0.symm }
  invFun v :=
    { asIdeal := v.asIdeal.map C.conjRingOfIntegers.symm.toRingHom
      isPrime := by
        rw [ideal_map_ringEquiv_eq_comap]
        exact Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        apply v.ne_bot
        have h0 : (v.asIdeal.map C.conjRingOfIntegers.symm.toRingHom).map
            C.conjRingOfIntegers.toRingHom = v.asIdeal := by
          rw [Ideal.map_map]
          have hc : C.conjRingOfIntegers.toRingHom.comp C.conjRingOfIntegers.symm.toRingHom =
              RingHom.id _ := by ext x; simp
          rw [hc, Ideal.map_id]
        rw [hbot, Ideal.map_bot] at h0
        exact h0.symm }
  left_inv v := by
    ext x
    change x ∈ (v.asIdeal.map C.conjRingOfIntegers.toRingHom).map
        C.conjRingOfIntegers.symm.toRingHom ↔ x ∈ v.asIdeal
    rw [Ideal.map_map]
    have hc : C.conjRingOfIntegers.symm.toRingHom.comp C.conjRingOfIntegers.toRingHom =
        RingHom.id _ := by ext y; simp
    rw [hc, Ideal.map_id]
  right_inv v := by
    ext x
    change x ∈ (v.asIdeal.map C.conjRingOfIntegers.symm.toRingHom).map
        C.conjRingOfIntegers.toRingHom ↔ x ∈ v.asIdeal
    rw [Ideal.map_map]
    have hc : C.conjRingOfIntegers.toRingHom.comp C.conjRingOfIntegers.symm.toRingHom =
        RingHom.id _ := by ext y; simp
    rw [hc, Ideal.map_id]

theorem mem_conjHeightOne_iff (v : HeightOneSpectrum (𝓞 C.E)) (x : 𝓞 C.E) :
    x ∈ (C.conjHeightOne v).asIdeal ↔ C.conjRingOfIntegers x ∈ v.asIdeal := by
  change x ∈ v.asIdeal.map C.conjRingOfIntegers.toRingHom ↔ _
  rw [ideal_map_ringEquiv_eq_comap]
  change C.conjRingOfIntegers.symm x ∈ v.asIdeal ↔ C.conjRingOfIntegers x ∈ v.asIdeal
  have hsymm : C.conjRingOfIntegers.symm x = C.conjRingOfIntegers x := by
    apply C.conjRingOfIntegers.injective
    rw [C.conjRingOfIntegers.apply_symm_apply, C.conjRingOfIntegers_invol]
  rw [hsymm]

theorem conjHeightOne_invol (v : HeightOneSpectrum (𝓞 C.E)) :
    C.conjHeightOne (C.conjHeightOne v) = v := by
  ext x
  rw [C.mem_conjHeightOne_iff, C.mem_conjHeightOne_iff, C.conjRingOfIntegers_invol]

theorem residueCard_conjHeightOne (v : HeightOneSpectrum (𝓞 C.E)) :
    Stage5AdelicTate.residueCard (C.conjHeightOne v) = Stage5AdelicTate.residueCard v := by
  unfold Stage5AdelicTate.residueCard
  let toF : 𝓞 C.E ⧸ (C.conjHeightOne v).asIdeal →+* 𝓞 C.E ⧸ v.asIdeal :=
    Ideal.Quotient.lift (C.conjHeightOne v).asIdeal
      ((Ideal.Quotient.mk v.asIdeal).comp C.conjRingOfIntegers.toRingHom) fun a ha => by
        change Ideal.Quotient.mk v.asIdeal (C.conjRingOfIntegers a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← C.mem_conjHeightOne_iff]
        exact ha
  let invF : 𝓞 C.E ⧸ v.asIdeal →+* 𝓞 C.E ⧸ (C.conjHeightOne v).asIdeal :=
    Ideal.Quotient.lift v.asIdeal
      ((Ideal.Quotient.mk (C.conjHeightOne v).asIdeal).comp C.conjRingOfIntegers.toRingHom)
      fun a ha => by
        change Ideal.Quotient.mk (C.conjHeightOne v).asIdeal (C.conjRingOfIntegers a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, C.mem_conjHeightOne_iff, C.conjRingOfIntegers_invol]
        exact ha
  exact Nat.card_congr
    { toFun := toF
      invFun := invF
      left_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ x =>
          change Ideal.Quotient.mk (C.conjHeightOne v).asIdeal
            (C.conjRingOfIntegers (C.conjRingOfIntegers x)) = Ideal.Quotient.mk _ x
          rw [C.conjRingOfIntegers_invol]
      right_inv := fun q => by
        induction q using Quotient.inductionOn with
        | _ x =>
          change Ideal.Quotient.mk v.asIdeal
            (C.conjRingOfIntegers (C.conjRingOfIntegers x)) = Ideal.Quotient.mk _ x
          rw [C.conjRingOfIntegers_invol] }

/-- Place `w` of `E` lies over place `v` of `F`. -/
def PlaceAbove (v : HeightOneSpectrum (𝓞 C.F)) (w : HeightOneSpectrum (𝓞 C.E)) : Prop :=
  w.asIdeal.comap (algebraMap (𝓞 C.F) (𝓞 C.E)) = v.asIdeal

/-- The unique finite place of `F` below a given finite place `w` of `E`. -/
def placeUnder (w : HeightOneSpectrum (𝓞 C.E)) : HeightOneSpectrum (𝓞 C.F) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 C.F) (𝓞 C.E))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hbot
    obtain ⟨x, hx_mem, hx_ne⟩ : ∃ x ∈ w.asIdeal, x ≠ 0 := by
      by_contra h
      push Not at h
      apply w.ne_bot
      rw [eq_bot_iff]
      exact fun y hy => h y hy
    have hnorm_int : IsIntegral ℤ (C.cmNorm (x : C.E)) := by
      rw [← isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective C.F C.E),
        C.cmNorm_eq_mul_conj]
      have hx1 : IsIntegral ℤ (x : C.E) := x.2
      have hx2 : IsIntegral ℤ (C.conj (x : C.E)) := (C.conjRingOfIntegers x).2
      exact hx1.mul hx2
    let nm : 𝓞 C.F := ⟨C.cmNorm (x : C.E), hnorm_int⟩
    have hnm_ne : nm ≠ 0 := by
      intro h0
      have h0' : C.cmNorm (x : C.E) = 0 := congrArg Subtype.val h0
      have hmul : (x : C.E) * C.conj (x : C.E) = 0 := by
        rw [← C.cmNorm_eq_mul_conj, h0', map_zero]
      rcases mul_eq_zero.mp hmul with hx0 | hcx0
      · exact hx_ne (ZeroMemClass.coe_eq_zero.mp hx0)
      · have hcx : (x : C.E) = 0 := by
          have := congrArg C.conj hcx0
          simpa [C.conj_conj] using this
        exact hx_ne (ZeroMemClass.coe_eq_zero.mp hcx)
    have halg : algebraMap (𝓞 C.F) (𝓞 C.E) nm = x * C.conjRingOfIntegers x := by
      apply Subtype.ext
      change algebraMap C.F C.E (C.cmNorm (x : C.E)) = (x : C.E) * C.conj (x : C.E)
      exact C.cmNorm_eq_mul_conj (x : C.E)
    have hmem_comap : nm ∈ w.asIdeal.comap (algebraMap (𝓞 C.F) (𝓞 C.E)) := by
      rw [Ideal.mem_comap, halg]
      exact w.asIdeal.mul_mem_right _ hx_mem
    rw [hbot, Ideal.mem_bot] at hmem_comap
    exact hnm_ne hmem_comap

theorem placeAbove_placeUnder (w : HeightOneSpectrum (𝓞 C.E)) :
    C.PlaceAbove (C.placeUnder w) w := rfl

theorem placeUnder_conjHeightOne (w : HeightOneSpectrum (𝓞 C.E)) :
    C.placeUnder (C.conjHeightOne w) = C.placeUnder w := by
  ext a
  change a ∈ (C.conjHeightOne w).asIdeal.comap (algebraMap (𝓞 C.F) (𝓞 C.E)) ↔
    a ∈ w.asIdeal.comap (algebraMap (𝓞 C.F) (𝓞 C.E))
  rw [Ideal.mem_comap, Ideal.mem_comap, C.mem_conjHeightOne_iff]
  have hfix : C.conjRingOfIntegers (algebraMap (𝓞 C.F) (𝓞 C.E) a) =
      algebraMap (𝓞 C.F) (𝓞 C.E) a := by
    apply Subtype.ext
    change C.conj (algebraMap C.F C.E (a : C.F)) = algebraMap C.F C.E (a : C.F)
    exact C.conj_algebraMap (a : C.F)
  rw [hfix]

/-- A finite place `v` of `F` is split in `E` if some prime `w ∣ v` satisfies `conj w ≠ w`. -/
def IsSplitPlace (v : HeightOneSpectrum (𝓞 C.F)) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 C.E), C.PlaceAbove v w ∧ C.conjHeightOne w ≠ w

/-- A finite place `v` of `F` is inert or ramified if `conj w = w` for every `w ∣ v`. -/
def IsInertOrRamifiedPlace (v : HeightOneSpectrum (𝓞 C.F)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 C.E), C.PlaceAbove v w → C.conjHeightOne w = w

open Classical in
/-- The quadratic CM character `χ_{E/F}(v) ∈ {1, -1, 0}` at finite places of `F`:
`+1` if split, `0` if ramified, `-1` if inert. -/
def chiEF (v : HeightOneSpectrum (𝓞 C.F)) : ℝ :=
  if C.IsSplitPlace v then 1
  else if ∃ w : HeightOneSpectrum (𝓞 C.E),
      C.PlaceAbove v w ∧ Stage5AdelicTate.residueCard w = Stage5AdelicTate.residueCard v then 0
  else -1

theorem abs_chiEF_le_one (v : HeightOneSpectrum (𝓞 C.F)) : |C.chiEF v| ≤ 1 := by
  unfold chiEF
  split_ifs <;> norm_num

end CMHostField

/-- Concrete unconditional inhabitant: the Gaussian CM extension `ℚ(ζ_4) / ℚ`. -/
def gaussianCMHostField : CMHostField where
  F := ℚ
  E := CyclotomicField 4 ℚ
  totallyRealF := by
    refine ⟨fun φ => ?_⟩
    rw [← InfinitePlace.mk_embedding φ, InfinitePlace.isReal_mk_iff,
      NumberField.ComplexEmbedding.isReal_iff]
    have hφ : φ.embedding = algebraMap ℚ ℂ := Subsingleton.elim _ _
    rw [hφ]
    ext x
    simp
  totallyComplexE := by
    let _ : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
      CyclotomicField.isCyclotomicExtension 4 ℚ
    let ζ : CyclotomicField 4 ℚ := IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ)
    have hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ)
    refine ⟨fun φ => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, ← InfinitePlace.mk_embedding φ,
      InfinitePlace.isReal_mk_iff, NumberField.ComplexEmbedding.isReal_iff]
    intro heq
    have h4 : (φ.embedding ζ) ^ 4 = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    have h2 : (φ.embedding ζ) ^ 2 = -1 := by
      have hne : (φ.embedding ζ) ^ 2 ≠ 1 := by
        intro h1
        have h1' : ζ ^ 2 = 1 :=
          φ.embedding.injective (by simpa [map_pow, map_one] using h1)
        exact absurd (hζ.dvd_of_pow_eq_one 2 h1') (by decide)
      have hfac : ((φ.embedding ζ) ^ 2 - 1) * ((φ.embedding ζ) ^ 2 + 1) = 0 := by
        linear_combination h4
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · exact absurd (sub_eq_zero.mp hsub) hne
      · exact eq_neg_of_add_eq_zero_left hadd
    have him : (φ.embedding ζ).im = 0 := by
      have hconj := congrArg (fun f : CyclotomicField 4 ℚ →+* ℂ => f ζ) heq
      have him2 : -(φ.embedding ζ).im = (φ.embedding ζ).im := by
        simpa [Complex.ext_iff] using congrArg Complex.im hconj
      linarith
    have hre : ((φ.embedding ζ).re : ℂ) = φ.embedding ζ := Complex.ext rfl him.symm
    have hsq_real : ((φ.embedding ζ).re) ^ 2 = -1 := by
      have := congrArg Complex.re h2
      rw [← hre, ← Complex.ofReal_pow, Complex.ofReal_re] at this
      exact this
    nlinarith [sq_nonneg (φ.embedding ζ).re]
  finrank_eq_two := by
    let _ : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
      CyclotomicField.isCyclotomicExtension 4 ℚ
    have hirr : Irreducible (Polynomial.cyclotomic 4 ℚ) :=
      Polynomial.cyclotomic.irreducible_rat (by decide : 0 < 4)
    rw [IsCyclotomicExtension.finrank (CyclotomicField 4 ℚ) hirr]
    decide

theorem cmHostField_nonempty : Nonempty CMHostField := ⟨gaussianCMHostField⟩

end CMHostFieldSection

/-! ## Section 2: `RestrictedProdRing` (General Restricted Products of Rings) -/

section RestrictedProdRingSection

/-- Concrete restricted product `∏'_i (R_i, O_i)` of commutative rings with respect to subrings
`O_i ≤ R_i` along `Filter.cofinite`. -/
abbrev RestrictedProdRing (ι : Type*) (R : ι → Type*) [∀ i, CommRing (R i)]
    (O : ∀ i, Subring (R i)) : Type _ :=
  Πʳ i, [R i, (O i : Set (R i))]

namespace RestrictedProdRing

section Algebraic

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] {O : ∀ i, Subring (R i)}

/-- Component evaluation ring homomorphism `Π'_i R_i →+* R i`. -/
def evalAt (i : ι) : RestrictedProdRing ι R O →+* R i where
  toFun x := x i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ext {x y : RestrictedProdRing ι R O} (h : ∀ i, x i = y i) : x = y :=
  DFunLike.ext x y h

/-- The integral subring `{x | ∀ i, x i ∈ O i}` of `RestrictedProdRing ι R O`. -/
def integralSubring : Subring (RestrictedProdRing ι R O) where
  carrier := {x | ∀ i, x i ∈ O i}
  one_mem' i := (O i).one_mem
  mul_mem' {_ _} hx hy i := (O i).mul_mem (hx i) (hy i)
  zero_mem' i := (O i).zero_mem
  add_mem' {_ _} hx hy i := (O i).add_mem (hx i) (hy i)
  neg_mem' {_} hx i := (O i).neg_mem (hx i)

theorem mem_integralSubring_iff (x : RestrictedProdRing ι R O) :
    x ∈ integralSubring (ι := ι) (R := R) (O := O) ↔ ∀ i, x i ∈ O i :=
  Iff.rfl

/-- Characterization of units in `RestrictedProdRing ι R O`: every component is a unit and
all but finitely many components are units in `O i`. -/
theorem isUnit_iff (x : RestrictedProdRing ι R O) :
    IsUnit x ↔ (∀ i, IsUnit (x i)) ∧
      (∀ᶠ i in Filter.cofinite, ∃ h1 : x i ∈ O i, IsUnit (⟨x i, h1⟩ : O i)) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i => ⟨⟨u.val i, u.inv i,
      by change (u.val * u.inv) i = 1; rw [u.val_inv]; rfl,
      by change (u.inv * u.val) i = 1; rw [u.inv_val]; rfl⟩, rfl⟩, ?_⟩
    filter_upwards [u.val.2, u.inv.2] with i hi1 hi2
    refine ⟨hi1, ⟨⟨⟨u.val i, hi1⟩, ⟨u.inv i, hi2⟩,
      Subtype.ext (by change (u.val * u.inv) i = 1; rw [u.val_inv]; rfl),
      Subtype.ext (by change (u.inv * u.val) i = 1; rw [u.inv_val]; rfl)⟩, rfl⟩⟩
  · rintro ⟨hunit, hfin⟩
    have hinv_mem : ∀ᶠ i in Filter.cofinite, ((hunit i).unit⁻¹ : (R i)ˣ).val ∈ O i := by
      filter_upwards [hfin] with i ⟨hi1, ⟨ui, hui⟩⟩
      have heq : ((hunit i).unit⁻¹ : (R i)ˣ).val = (ui⁻¹ : (O i)ˣ).val.val := by
        have h1 : (hunit i).unit.val = (ui : O i).val := by
          rw [(hunit i).unit_spec, hui]
        have h2 : (ui : O i).val * (ui⁻¹ : (O i)ˣ).val.val = 1 :=
          congrArg Subtype.val ui.val_inv
        rw [← h1] at h2
        have h3 : ((hunit i).unit⁻¹ : (R i)ˣ).val * (hunit i).unit.val = 1 :=
          (hunit i).unit.inv_val
        calc ((hunit i).unit⁻¹ : (R i)ˣ).val
            = ((hunit i).unit⁻¹ : (R i)ˣ).val *
                ((hunit i).unit.val * (ui⁻¹ : (O i)ˣ).val.val) := by rw [h2, mul_one]
          _ = (((hunit i).unit⁻¹ : (R i)ˣ).val * (hunit i).unit.val) *
                (ui⁻¹ : (O i)ˣ).val.val := by ring
          _ = (ui⁻¹ : (O i)ˣ).val.val := by rw [h3, one_mul]
      rw [heq]
      exact (ui⁻¹ : (O i)ˣ).val.2
    refine ⟨⟨x, RestrictedProduct.mk (fun i => ((hunit i).unit⁻¹ : (R i)ˣ).val) hinv_mem, ?_, ?_⟩, rfl⟩
    · apply ext
      intro i
      change x i * ((hunit i).unit⁻¹ : (R i)ˣ).val = 1
      exact (congrArg (· * ((hunit i).unit⁻¹ : (R i)ˣ).val) (hunit i).unit_spec.symm).trans
        (hunit i).unit.val_inv
    · apply ext
      intro i
      change ((hunit i).unit⁻¹ : (R i)ˣ).val * x i = 1
      exact (congrArg (((hunit i).unit⁻¹ : (R i)ˣ).val * ·) (hunit i).unit_spec.symm).trans
        (hunit i).unit.inv_val

/-- Integral unit subgroup `{u : (RestrictedProdRing ι R O)ˣ | ∀ i, u.val i ∈ O i ∧ u.inv i ∈ O i}`. -/
def integralUnitsSubgroup : Subgroup (RestrictedProdRing ι R O)ˣ where
  carrier := {u | ∀ i, u.val i ∈ O i ∧ u.inv i ∈ O i}
  one_mem' i := ⟨(O i).one_mem, (O i).one_mem⟩
  mul_mem' {_ _} hu hv i :=
    ⟨(O i).mul_mem (hu i).1 (hv i).1, (O i).mul_mem (hv i).2 (hu i).2⟩
  inv_mem' {_} hu i := ⟨(hu i).2, (hu i).1⟩

/-- Canonical isomorphism `integralUnitsSubgroup ≃* Π i, (O i)ˣ`. -/
def integralUnitsEquiv :
    integralUnitsSubgroup (ι := ι) (R := R) (O := O) ≃* ((i : ι) → (O i)ˣ) where
  toFun u i :=
    { val := ⟨u.1.val i, (u.2 i).1⟩
      inv := ⟨u.1.inv i, (u.2 i).2⟩
      val_inv := Subtype.ext (by change (u.1.val * u.1.inv) i = 1; rw [u.1.val_inv]; rfl)
      inv_val := Subtype.ext (by change (u.1.inv * u.1.val) i = 1; rw [u.1.inv_val]; rfl) }
  invFun f :=
    ⟨{ val := RestrictedProduct.mk (fun i => (f i).val.1)
          (Filter.Eventually.of_forall fun i => (f i).val.2)
       inv := RestrictedProduct.mk (fun i => (f i).inv.1)
          (Filter.Eventually.of_forall fun i => (f i).inv.2)
       val_inv := ext fun i => congrArg Subtype.val (f i).val_inv
       inv_val := ext fun i => congrArg Subtype.val (f i).inv_val },
      fun i => ⟨(f i).val.2, (f i).inv.2⟩⟩
  left_inv u := by apply Subtype.ext; apply Units.ext; exact ext fun _ => rfl
  right_inv f := by funext i; apply Units.ext; exact Subtype.ext rfl
  map_mul' _ _ := by funext i; apply Units.ext; exact Subtype.ext rfl

private lemma congr_left_aux {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {R₂ : ι₂ → Type*}
    [∀ i, CommRing (R₁ i)] [∀ j, CommRing (R₂ j)]
    (e : ι₁ ≃ ι₂) (φ : ∀ i, R₁ i ≃+* R₂ (e i)) (x : ∀ i, R₁ i) (i : ι₁) :
    (φ i).symm (cast (congrArg R₂ (e.apply_symm_apply (e i)))
      (φ (e.symm (e i)) (x (e.symm (e i))))) = x i := by
  have h1 : ∀ {i' : ι₁} (h : i' = i) (he : e i' = e i),
      (φ i).symm (cast (congrArg R₂ he) (φ i' (x i'))) = x i := by
    intro i' h he
    subst h
    simp
  exact h1 (e.symm_apply_apply i) (e.apply_symm_apply (e i))

private lemma congr_right_aux {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {R₂ : ι₂ → Type*}
    [∀ i, CommRing (R₁ i)] [∀ j, CommRing (R₂ j)]
    (e : ι₁ ≃ ι₂) (φ : ∀ i, R₁ i ≃+* R₂ (e i)) (y : ∀ j, R₂ j) (j : ι₂) :
    cast (congrArg R₂ (e.apply_symm_apply j))
      (φ (e.symm j) ((φ (e.symm j)).symm (y (e (e.symm j))))) = y j := by
  rw [RingEquiv.apply_symm_apply]
  have h1 : ∀ {j' : ι₂} (h : j' = j), cast (congrArg R₂ h) (y j') = y j := by
    intro j' h
    subst h
    rfl
  exact h1 (e.apply_symm_apply j)

private lemma cast_mem_subring {α : Type*} {S : α → Type*} [∀ a, CommRing (S a)]
    {O : ∀ a, Subring (S a)} {a b : α} (h : a = b) (x : S a) :
    cast (congrArg S h) x ∈ O b ↔ x ∈ O a := by
  subst h
  rfl

private lemma cast_mul {α : Type*} {S : α → Type*} [∀ a, CommRing (S a)]
    {a b : α} (h : a = b) (x y : S a) :
    cast (congrArg S h) (x * y) = cast (congrArg S h) x * cast (congrArg S h) y := by
  subst h
  rfl

private lemma cast_add {α : Type*} {S : α → Type*} [∀ a, CommRing (S a)]
    {a b : α} (h : a = b) (x y : S a) :
    cast (congrArg S h) (x + y) = cast (congrArg S h) x + cast (congrArg S h) y := by
  subst h
  rfl

/-- Functorial ring equivalence between restricted products along an index equivalence `e`
and component ring equivalences preserving the integral subrings. -/
def congr {ι₁ ι₂ : Type*} {R₁ : ι₁ → Type*} {R₂ : ι₂ → Type*}
    [∀ i, CommRing (R₁ i)] [∀ j, CommRing (R₂ j)]
    {O₁ : ∀ i, Subring (R₁ i)} {O₂ : ∀ j, Subring (R₂ j)}
    (e : ι₁ ≃ ι₂) (φ : ∀ i, R₁ i ≃+* R₂ (e i))
    (hO : ∀ i (x : R₁ i), x ∈ O₁ i ↔ φ i x ∈ O₂ (e i)) :
    RestrictedProdRing ι₁ R₁ O₁ ≃+* RestrictedProdRing ι₂ R₂ O₂ where
  toFun x := RestrictedProduct.mk
    (fun j => cast (congrArg R₂ (e.apply_symm_apply j)) (φ (e.symm j) (x (e.symm j)))) (by
      have h1 := x.2
      rw [Filter.eventually_cofinite] at h1 ⊢
      have hsub : {j : ι₂ | cast (congrArg R₂ (e.apply_symm_apply j))
          (φ (e.symm j) (x (e.symm j))) ∉ O₂ j} ⊆
          e '' {i : ι₁ | x i ∉ O₁ i} := by
        intro j hj
        refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
        intro hmem
        apply hj
        rw [cast_mem_subring (e.apply_symm_apply j), ← hO (e.symm j)]
        exact hmem
      exact (h1.image e).subset hsub)
  invFun y := RestrictedProduct.mk (fun i => (φ i).symm (y (e i))) (by
    have h1 := y.2
    rw [Filter.eventually_cofinite] at h1 ⊢
    have hsub : {i : ι₁ | (φ i).symm (y (e i)) ∉ O₁ i} ⊆
        e.symm '' {j : ι₂ | y j ∉ O₂ j} := by
      intro i hi
      refine ⟨e i, ?_, e.symm_apply_apply i⟩
      intro hmem
      apply hi
      rw [hO i, RingEquiv.apply_symm_apply]
      exact hmem
    exact (h1.image e.symm).subset hsub)
  left_inv x := by
    apply ext
    intro i
    exact congr_left_aux e φ x i
  right_inv y := by
    apply ext
    intro j
    exact congr_right_aux e φ y j
  map_mul' x y := by
    apply ext
    intro j
    change cast (congrArg R₂ (e.apply_symm_apply j)) (φ (e.symm j) (x (e.symm j) * y (e.symm j))) = _
    rw [map_mul, cast_mul (e.apply_symm_apply j)]
    rfl
  map_add' x y := by
    apply ext
    intro j
    change cast (congrArg R₂ (e.apply_symm_apply j)) (φ (e.symm j) (x (e.symm j) + y (e.symm j))) = _
    rw [map_add, cast_add (e.apply_symm_apply j)]
    rfl

end Algebraic

section Topological

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)]
  {O : ∀ i, Subring (R i)}

theorem isOpen_integralSubring (hopen : ∀ i, IsOpen (O i : Set (R i))) :
    IsOpen (integralSubring (ι := ι) (R := R) (O := O) : Set (RestrictedProdRing ι R O)) :=
  RestrictedProduct.isOpen_forall_mem hopen

theorem isCompact_integralSubring (hcomp : ∀ i, IsCompact (O i : Set (R i))) :
    IsCompact (integralSubring (ι := ι) (R := R) (O := O) : Set (RestrictedProdRing ι R O)) := by
  have : ∀ i, CompactSpace (O i : Set (R i)) := fun i => isCompact_iff_compactSpace.mp (hcomp i)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := R) (A := fun i => (O i : Set (R i))) (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end Topological

/-- Identification of Mathlib's `FiniteAdeleRing (𝓞 K) K` as an explicit `RestrictedProdRing`. -/
def finAdeleEquiv (K : Type*) [Field K] [NumberField K] :
    FiniteAdeleRing (𝓞 K) K ≃+*
      RestrictedProdRing (HeightOneSpectrum (𝓞 K))
        (fun v => v.adicCompletion K)
        (fun v => (v.adicCompletionIntegers K).toSubring) :=
  RingEquiv.refl _

end RestrictedProdRing

end RestrictedProdRingSection

/-! ## Section 3: `FiniteAdelesCM`, Adelic Hermitian Forms, & `AdelicPair` -/

section FiniteAdelesCMSection

/-- Adelic Hermitian form compatibility (`IsHermForm`), matching Alpöge's
`Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm`. -/
def IsHermForm {F E : Type*} [Field F] [Field E] [Algebra F E] (c : E ≃ₐ[F] E)
    {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ x, c (c x) = x) ∧ c ≠ AlgEquiv.refl ∧ (∀ a b, c (G a b) = G b a) ∧ G.det ≠ 0

/-- Hyperbolic Hermitian form predicate (`IsHermHyperbolic`), matching Alpöge's
`Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic`. -/
structure IsHermHyperbolic {R : Type*} [CommRing R] {n : ℕ}
    (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) : Prop where
  invol : ∀ a, σ (σ a) = a
  ne_id : ∃ a, σ a ≠ a
  herm : ∀ a b, σ (G a b) = G b a
  det_ne : IsUnit G.det

/-- Hyperbolic 2×2 Hermitian form `!![0, 1; 1, 0]` over any `CMHostField`. -/
theorem isHermHyperbolic_two (C : CMHostField) :
    IsHermHyperbolic (C.conj : C.E →+* C.E) !![(0 : C.E), 1; 1, 0] ∧
      ∃ z : Fin 2 → C.E, z ≠ 0 ∧
        (∑ a : Fin 2, ∑ b : Fin 2, z a * !![(0 : C.E), 1; 1, 0] a b * C.conj (z b)) = 0 := by
  refine ⟨⟨C.conj_conj, ?_, ?_, ?_⟩, ![1, 0], ?_, ?_⟩
  · obtain ⟨a, ha⟩ := C.exists_not_mem_range
    refine ⟨a, ?_⟩
    intro heq
    exact ha (C.mem_range_of_conj_eq heq)
  · intro a b
    fin_cases a <;> fin_cases b
    · exact map_zero _
    · exact map_one _
    · exact map_one _
    · exact map_zero _
  · have hd : (!![(0 : C.E), 1; 1, 0]).det = -1 := by
      rw [Matrix.det_fin_two]
      change (0 : C.E) * 0 - 1 * 1 = -1
      ring
    rw [hd]
    exact isUnit_one.neg
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Alpöge's `AdelicPair` property (`int_of_mem` + rational congruence approximation). -/
structure AdelicPair (R : Type*) [CommRing R] [Algebra ℚ R] (R₀ : Subring R) : Prop where
  int_of_mem : ∀ q : ℚ, algebraMap ℚ R q ∈ R₀ → ∃ z : ℤ, q = z
  approx : ∀ M : ℕ, 0 < M → ∀ r : R, ∃ q : ℚ, ∃ a ∈ R₀, r = algebraMap ℚ R q + (M : R) * a

/-- CM Finite Adeles bundle `FiniteAdelesCM C` for a CM host field `C : CMHostField`.
Provides the finite adeles of `F` and `E`, Alpöge's base-change tensor ring `RA C.F C.E`,
full adeles `Adele F` / `Adele E`, and CM conjugation involutions. -/
structure FiniteAdelesCM (C : CMHostField) where
  finAdeleF : Type := FiniteAdeleRing (𝓞 C.F) C.F
  finAdeleE : Type := FiniteAdeleRing (𝓞 C.E) C.E
  tensorFinAdele : Type := FiniteAdeleRing (𝓞 C.F) C.F ⊗[C.F] C.E
  adeleF : Type := NumberField.AdeleRing (𝓞 C.F) C.F
  adeleE : Type := NumberField.AdeleRing (𝓞 C.E) C.E

namespace FiniteAdelesCM

/-- Canonical instantiation of `FiniteAdelesCM C`. -/
def canonical (C : CMHostField) : FiniteAdelesCM C := {}

section InvolutionAndBaseChange

variable (C : CMHostField)

/-- The base-change tensor ring `RA(F, E) = 𝔸_{F,f} ⊗_F E`. -/
abbrev RA : Type _ := FiniteAdeleRing (𝓞 C.F) C.F ⊗[C.F] C.E

/-- CM conjugation on `RA(F, E) = 𝔸_{F,f} ⊗_F E` fixing `𝔸_{F,f}` (`1 ⊗ conj`). -/
def conjRA : RA C ≃ₐ[FiniteAdeleRing (𝓞 C.F) C.F] RA C :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) C.conj

@[simp]
theorem conjRA_tmul (a : FiniteAdeleRing (𝓞 C.F) C.F) (x : C.E) :
    conjRA C (a ⊗ₜ[C.F] x) = a ⊗ₜ[C.F] C.conj x := rfl

theorem conjRA_invol (z : RA C) : conjRA C (conjRA C z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [C.conj_conj]
  | add x y hx hy => simp [hx, hy]

/-- Hermitian pairing on `Fin n → RA C` with respect to `G : Matrix (Fin n) (Fin n) C.E`. -/
def hermRA {n : ℕ} (G : Matrix (Fin n) (Fin n) C.E) (x y : Fin n → RA C) : RA C :=
  ∑ a : Fin n, ∑ b : Fin n,
    x a * ((1 : FiniteAdeleRing (𝓞 C.F) C.F) ⊗ₜ[C.F] G a b) * conjRA C (y b)

/-- Ideal power preservation under `C.conjRingOfIntegers`:
`r ∈ (conj w)^k ↔ conj r ∈ w^k`. -/
theorem mem_conjHeightOne_pow_iff (w : HeightOneSpectrum (𝓞 C.E)) (k : ℕ) (r : 𝓞 C.E) :
    r ∈ (C.conjHeightOne w).asIdeal ^ k ↔ C.conjRingOfIntegers r ∈ w.asIdeal ^ k := by
  have hid : (C.conjHeightOne w).asIdeal ^ k =
      (w.asIdeal ^ k).map C.conjRingOfIntegers.toRingHom := by
    induction k with
    | zero => simp [Ideal.map_top]
    | succ k ih =>
      rw [pow_succ, pow_succ, ih, Ideal.map_mul]
      rfl
  rw [hid, CMHostField.ideal_map_ringEquiv_eq_comap]
  change C.conjRingOfIntegers.symm r ∈ w.asIdeal ^ k ↔ C.conjRingOfIntegers r ∈ w.asIdeal ^ k
  have hsymm : C.conjRingOfIntegers.symm r = C.conjRingOfIntegers r := by
    apply C.conjRingOfIntegers.injective
    rw [C.conjRingOfIntegers.apply_symm_apply, C.conjRingOfIntegers_invol]
  rw [hsymm]

/-- Local valuation invariance of `C.conj` on `𝓞 C.E` at height-one primes. -/
theorem intValuation_conj (w : HeightOneSpectrum (𝓞 C.E)) (r : 𝓞 C.E) :
    (C.conjHeightOne w).intValuation r = w.intValuation (C.conjRingOfIntegers r) := by
  classical
  by_cases hr : r = 0
  · subst hr; simp
  · have hcr : C.conjRingOfIntegers r ≠ 0 := by
      intro h0
      exact hr (C.conjRingOfIntegers.injective (by simpa using h0))
    rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hr,
      HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hcr]
    congr 1
    have hpow : ∀ k : ℕ, (C.conjHeightOne w).asIdeal ^ k ∣ Ideal.span {r} ↔
        w.asIdeal ^ k ∣ Ideal.span {C.conjRingOfIntegers r} := by
      intro k
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
        Ideal.span_singleton_le_iff_mem]
      exact mem_conjHeightOne_pow_iff C w k r
    have hfin1 : FiniteMultiplicity (C.conjHeightOne w).asIdeal (Ideal.span {r}) :=
      FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime (C.conjHeightOne w).ne_bot (C.conjHeightOne w).isPrime)
        (mt Ideal.span_singleton_eq_bot.mp hr)
    have hfin2 : FiniteMultiplicity w.asIdeal (Ideal.span {C.conjRingOfIntegers r}) :=
      FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime w.ne_bot w.isPrime)
        (mt Ideal.span_singleton_eq_bot.mp hcr)
    apply congrArg (fun m : ℕ => -(m : ℤ))
    apply le_antisymm
    · rw [← hfin2.pow_dvd_iff_le_multiplicity, ← hpow]
      exact hfin1.pow_dvd_iff_le_multiplicity.mpr le_rfl
    · rw [← hfin1.pow_dvd_iff_le_multiplicity, hpow]
      exact hfin2.pow_dvd_iff_le_multiplicity.mpr le_rfl

/-- Valuation invariance of `C.conj` on `C.E` at height-one primes. -/
theorem valuation_conj (w : HeightOneSpectrum (𝓞 C.E)) (x : C.E) :
    (C.conjHeightOne w).valuation C.E x = w.valuation C.E (C.conj x) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 C.E) x
  have hconj_div : C.conj (algebraMap (𝓞 C.E) C.E r / algebraMap (𝓞 C.E) C.E s) =
      algebraMap (𝓞 C.E) C.E (C.conjRingOfIntegers r) /
        algebraMap (𝓞 C.E) C.E (C.conjRingOfIntegers s) := by
    rw [map_div₀]
    rfl
  rw [hconj_div, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_conj, intValuation_conj]

private lemma continuous_conj_withVal (w w' : HeightOneSpectrum (𝓞 C.E))
    (hval : ∀ x : C.E, w'.valuation C.E (C.conj x) = w.valuation C.E x) :
    Continuous ((WithVal.equiv (w'.valuation C.E)).symm.toRingHom.comp
      (C.conj.toRingHom.comp (WithVal.equiv (w.valuation C.E)).toRingHom)) := by
  let f : WithVal (w.valuation C.E) →+* WithVal (w'.valuation C.E) :=
    (WithVal.equiv (w'.valuation C.E)).symm.toRingHom.comp
      (C.conj.toRingHom.comp (WithVal.equiv (w.valuation C.E)).toRingHom)
  have hf_val : ∀ a : WithVal (w.valuation C.E), Valued.v (f a) = Valued.v a :=
    fun a => hval ((WithVal.equiv (w.valuation C.E)) a)
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ', hγ'⟩ := Valued.mem_nhds_zero.1 hs
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ'.1
  have hc0 : c ≠ 0 := by simp [c]
  obtain ⟨ϖ, hϖ⟩ := w.valuation_exists_uniformizer C.E
  let k : ℤ := -WithZero.log c
  let u₀ : WithVal (w.valuation C.E) := (WithVal.equiv (w.valuation C.E)).symm (ϖ ^ k)
  have hu₀ : Valued.v u₀ = c := by
    change w.valuation C.E (ϖ ^ k) = c
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
    simp [k, WithZero.exp_log hc0]
  have hu₀_ne : (Valued.v : Valuation (WithVal (w.valuation C.E)) (WithZero (Multiplicative ℤ))).restrict u₀ ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h0
    rw [h0, map_zero] at hu₀
    exact hc0 hu₀.symm
  let γ₁ : (MonoidWithZeroHom.ValueGroup₀
      (.ofClass (Valued.v : Valuation (WithVal (w.valuation C.E)) (WithZero (Multiplicative ℤ)))))ˣ :=
    Units.mk0 _ hu₀_ne
  refine Valued.mem_nhds_zero.2 ⟨γ₁, fun x hx => Set.mem_preimage.2 (hγ' ?_)⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  change (Valued.v : Valuation (WithVal (w.valuation C.E)) (WithZero (Multiplicative ℤ))).restrict x <
    (Valued.v : Valuation (WithVal (w.valuation C.E)) (WithZero (Multiplicative ℤ))).restrict u₀ at hx
  rw [Valuation.restrict_lt_iff] at hx
  rw [Valuation.restrict_lt_iff_lt_embedding]
  change Valued.v (f x) < c
  rw [hf_val, ← hu₀]
  exact hx

private def conjCompletionHom (w w' : HeightOneSpectrum (𝓞 C.E))
    (hval : ∀ x : C.E, w'.valuation C.E (C.conj x) = w.valuation C.E x) :
    w.adicCompletion C.E →+* w'.adicCompletion C.E :=
  (HeightOneSpectrum.adicCompletion.equiv C.E w').symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        ((WithVal.equiv (w'.valuation C.E)).symm.toRingHom.comp
          (C.conj.toRingHom.comp (WithVal.equiv (w.valuation C.E)).toRingHom))
        (continuous_conj_withVal C w w' hval)).comp
      (HeightOneSpectrum.adicCompletion.equiv C.E w).toRingHom)

private theorem continuous_conjCompletionHom (w w' : HeightOneSpectrum (𝓞 C.E))
    (hval : ∀ x : C.E, w'.valuation C.E (C.conj x) = w.valuation C.E x) :
    Continuous (conjCompletionHom C w w' hval) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion C.E w').comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion C.E w)

private theorem conjCompletionHom_algebraMap (w w' : HeightOneSpectrum (𝓞 C.E))
    (hval : ∀ x : C.E, w'.valuation C.E (C.conj x) = w.valuation C.E x) (x : C.E) :
    conjCompletionHom C w w' hval (algebraMap C.E (w.adicCompletion C.E) x) =
      algebraMap C.E (w'.adicCompletion C.E) (C.conj x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  simp only [conjCompletionHom, RingHom.coe_comp, Function.comp_apply]
  change (HeightOneSpectrum.adicCompletion.equiv C.E w')
    ((HeightOneSpectrum.adicCompletion.equiv C.E w').symm
      (UniformSpace.Completion.mapRingHom _ (continuous_conj_withVal C w w' hval)
        ((algebraMap C.E (WithVal (w.valuation C.E)) x : WithVal (w.valuation C.E)) :
          UniformSpace.Completion (WithVal (w.valuation C.E))))) = _
  rw [RingEquiv.apply_symm_apply, UniformSpace.Completion.mapRingHom_coe]
  rfl

/-- Local completion ring isomorphism `w.adicCompletion C.E ≃+* (C.conjHeightOne w).adicCompletion C.E`
induced by `C.conj`. -/
def conjCompletionEquiv (w : HeightOneSpectrum (𝓞 C.E)) :
    w.adicCompletion C.E ≃+* (C.conjHeightOne w).adicCompletion C.E :=
  have h1 : ∀ x : C.E, (C.conjHeightOne w).valuation C.E (C.conj x) = w.valuation C.E x :=
    fun x => by rw [valuation_conj, C.conj_conj]
  have h2 : ∀ x : C.E, w.valuation C.E (C.conj x) = (C.conjHeightOne w).valuation C.E x :=
    fun x => (valuation_conj C w x).symm
  RingEquiv.ofRingHom
    (conjCompletionHom C w (C.conjHeightOne w) h1)
    (conjCompletionHom C (C.conjHeightOne w) w h2)
    (RingHom.ext (congrFun ((HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 C.E) (K := C.E)
      (C.conjHeightOne w)).equalizer
      ((continuous_conjCompletionHom C w (C.conjHeightOne w) h1).comp
        (continuous_conjCompletionHom C (C.conjHeightOne w) w h2))
      continuous_id (funext fun x => by
        simp only [Function.comp_apply, RingHom.coe_comp, RingHom.id_apply,
          conjCompletionHom_algebraMap, C.conj_conj]))))
    (RingHom.ext (congrFun ((HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 C.E) (K := C.E)
      w).equalizer
      ((continuous_conjCompletionHom C (C.conjHeightOne w) w h2).comp
        (continuous_conjCompletionHom C w (C.conjHeightOne w) h1))
      continuous_id (funext fun x => by
        simp only [Function.comp_apply, RingHom.coe_comp, RingHom.id_apply,
          conjCompletionHom_algebraMap, C.conj_conj]))))

theorem valued_conjCompletionEquiv (w : HeightOneSpectrum (𝓞 C.E)) (y : w.adicCompletion C.E) :
    Valued.v (conjCompletionEquiv C w y) = Valued.v y := by
  have h1 : ∀ x : C.E, (C.conjHeightOne w).valuation C.E (C.conj x) = w.valuation C.E x :=
    fun x => by rw [valuation_conj, C.conj_conj]
  change Valued.v (conjCompletionHom C w (C.conjHeightOne w) h1 y) = Valued.v y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hz : Valued.v (conjCompletionHom C w (C.conjHeightOne w) h1 y) ≠ 0 := by
    intro h0
    have hy0 : conjCompletionEquiv C w y = 0 := (Valuation.zero_iff _).mp h0
    exact hy ((conjCompletionEquiv C w).injective (by simpa using hy0))
  have hm1 := Valued.locally_const hy'
  have hm2 := (continuous_conjCompletionHom C w (C.conjHeightOne w) h1).continuousAt.preimage_mem_nhds
    (Valued.locally_const hz)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 C.E) (K := C.E)
    w).mem_nhds (Filter.inter_mem hm1 hm2)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk1 hk2
  rw [← hk1, ← hk2, conjCompletionHom_algebraMap]
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (C.conjHeightOne w),
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w]
  exact h1 k

theorem mem_conjCompletionEquiv_integers (w : HeightOneSpectrum (𝓞 C.E))
    (x : w.adicCompletion C.E) :
    x ∈ (w.adicCompletionIntegers C.E).toSubring ↔
      conjCompletionEquiv C w x ∈ ((C.conjHeightOne w).adicCompletionIntegers C.E).toSubring := by
  rw [ValuationSubring.mem_toSubring, ValuationSubring.mem_toSubring,
    HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    valued_conjCompletionEquiv]

/-- Global finite-adele CM conjugation equivalence `FiniteAdeleRing (𝓞 C.E) C.E ≃+* FiniteAdeleRing (𝓞 C.E) C.E`. -/
def conjFinAdele : FiniteAdeleRing (𝓞 C.E) C.E ≃+* FiniteAdeleRing (𝓞 C.E) C.E :=
  RestrictedProdRing.congr C.conjHeightOne (conjCompletionEquiv C)
    (mem_conjCompletionEquiv_integers C)

/-- Integral finite-adele subring `∏_v 𝒪_v ≤ FiniteAdeleRing (𝓞 K) K`. -/
def integralFiniteAdeles (K : Type*) [Field K] [NumberField K] :
    Subring (FiniteAdeleRing (𝓞 K) K) :=
  (RestrictedProdRing.integralSubring
    (ι := HeightOneSpectrum (𝓞 K))
    (R := fun v => v.adicCompletion K)
    (O := fun v => (v.adicCompletionIntegers K).toSubring)).comap
      (RestrictedProdRing.finAdeleEquiv K).toRingHom

theorem mem_integralFiniteAdeles_iff (K : Type*) [Field K] [NumberField K]
    (a : FiniteAdeleRing (𝓞 K) K) :
    a ∈ integralFiniteAdeles K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem isOpen_integralFiniteAdeles (K : Type*) [Field K] [NumberField K] :
    IsOpen (integralFiniteAdeles K : Set (FiniteAdeleRing (𝓞 K) K)) :=
  RestrictedProdRing.isOpen_integralSubring (fun _ => Valued.isOpen_valuationSubring _)

theorem conjFinAdele_preserves_integral (x : FiniteAdeleRing (𝓞 C.E) C.E) :
    x ∈ integralFiniteAdeles C.E ↔ conjFinAdele C x ∈ integralFiniteAdeles C.E := by
  rw [mem_integralFiniteAdeles_iff, mem_integralFiniteAdeles_iff]
  constructor
  · intro hx w
    change cast (congrArg (fun v : HeightOneSpectrum (𝓞 C.E) => v.adicCompletion C.E)
        (C.conjHeightOne.apply_symm_apply w))
        (conjCompletionEquiv C (C.conjHeightOne.symm w) (x (C.conjHeightOne.symm w))) ∈
      w.adicCompletionIntegers C.E
    have htr : ∀ {a b : HeightOneSpectrum (𝓞 C.E)} (h : a = b) (z : a.adicCompletion C.E),
        z ∈ a.adicCompletionIntegers C.E →
        cast (congrArg (fun v : HeightOneSpectrum (𝓞 C.E) => v.adicCompletion C.E) h) z ∈
          b.adicCompletionIntegers C.E := by
      intro a b h z hz
      subst h
      exact hz
    apply htr (C.conjHeightOne.apply_symm_apply w)
    rw [← ValuationSubring.mem_toSubring, ← mem_conjCompletionEquiv_integers]
    exact hx (C.conjHeightOne.symm w)
  · intro hx w
    have hw := hx (C.conjHeightOne w)
    change cast (congrArg (fun v : HeightOneSpectrum (𝓞 C.E) => v.adicCompletion C.E)
        (C.conjHeightOne.apply_symm_apply (C.conjHeightOne w)))
        (conjCompletionEquiv C (C.conjHeightOne.symm (C.conjHeightOne w))
          (x (C.conjHeightOne.symm (C.conjHeightOne w)))) ∈
      (C.conjHeightOne w).adicCompletionIntegers C.E at hw
    have htr : ∀ {a b : HeightOneSpectrum (𝓞 C.E)} (h : a = b) (z : a.adicCompletion C.E),
        cast (congrArg (fun v : HeightOneSpectrum (𝓞 C.E) => v.adicCompletion C.E) h) z ∈
          b.adicCompletionIntegers C.E → z ∈ a.adicCompletionIntegers C.E := by
      intro a b h z hz
      subst h
      exact hz
    have hw' := htr (C.conjHeightOne.apply_symm_apply (C.conjHeightOne w)) _ hw
    have hsym : C.conjHeightOne.symm (C.conjHeightOne w) = w := C.conjHeightOne.symm_apply_apply w
    have hmem : ∀ {w' : HeightOneSpectrum (𝓞 C.E)} (h : w' = w),
        conjCompletionEquiv C w' (x w') ∈ (C.conjHeightOne w').adicCompletionIntegers C.E →
        conjCompletionEquiv C w (x w) ∈ (C.conjHeightOne w).adicCompletionIntegers C.E := by
      intro w' h hz
      subst h
      exact hz
    have hw'' := hmem hsym hw'
    rwa [← ValuationSubring.mem_toSubring, ← mem_conjCompletionEquiv_integers] at hw''

end InvolutionAndBaseChange

end FiniteAdelesCM

end FiniteAdelesCMSection

/-! ## Section 4: `AdelicMeasureData` & `tamagawaFactor_pos` -/

section AdelicMeasureSection

open scoped Classical

/-- Concrete adelic Haar & Tamagawa measure data for a CM host field `C : CMHostField`. -/
structure AdelicMeasureData (C : CMHostField) where
  archScaleF : InfinitePlace C.F → ℝ
  archScaleF_pos : ∀ u, 0 < archScaleF u
  archScaleE : InfinitePlace C.E → ℝ
  archScaleE_pos : ∀ w, 0 < archScaleE w
  finVolF : HeightOneSpectrum (𝓞 C.F) → ℝ
  finVolF_pos : ∀ v, 0 < finVolF v
  finVolE : HeightOneSpectrum (𝓞 C.E) → ℝ
  finVolE_pos : ∀ w, 0 < finVolE w
  discNormF : ℝ
  discNormF_pos : 0 < discNormF
  discNormE : ℝ
  discNormE_pos : 0 < discNormE
  covolF : ℝ
  covolF_pos : 0 < covolF
  covolE : ℝ
  covolE_pos : 0 < covolE

namespace AdelicMeasureData

variable (C : CMHostField)

/-- Canonical Tate–Weil normalized adelic measure data on `C`:
- real places: `dx` (scale `1`),
- complex places: `|dz ∧ d\bar{z}| = 2 dx dy` (scale `2`),
- finite places: `vol(𝒪_v) = 1`,
- global discriminant normalization: `|discr K|^{-1/2}`. -/
def canonical : AdelicMeasureData C where
  archScaleF := fun _ => 1
  archScaleF_pos := fun _ => zero_lt_one
  archScaleE := fun _ => 2
  archScaleE_pos := fun _ => zero_lt_two
  finVolF := fun _ => 1
  finVolF_pos := fun _ => zero_lt_one
  finVolE := fun _ => 1
  finVolE_pos := fun _ => zero_lt_one
  discNormF := |(NumberField.discr C.F : ℝ)| ^ (-(1 / 2 : ℝ))
  discNormF_pos := Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero C.F))) _
  discNormE := |(NumberField.discr C.E : ℝ)| ^ (-(1 / 2 : ℝ))
  discNormE_pos := Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero C.E))) _
  covolF := ZLattice.covolume (NumberField.mixedEmbedding.integerLattice C.F) MeasureTheory.volume
  covolF_pos := by
    rw [NumberField.mixedEmbedding.covolume_integerLattice C.F]
    exact mul_pos (pow_pos (by norm_num) _)
      (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero C.F))))
  covolE := ZLattice.covolume (NumberField.mixedEmbedding.integerLattice C.E) MeasureTheory.volume
  covolE_pos := by
    rw [NumberField.mixedEmbedding.covolume_integerLattice C.E]
    exact mul_pos (pow_pos (by norm_num) _)
      (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero C.E))))

/-- Additive Tamagawa volume `vol(𝔸_F / F)` encoded by `M : AdelicMeasureData C`. -/
def additiveTamagawaVolF {C : CMHostField} (M : AdelicMeasureData C) : ℝ :=
  (∏ u : InfinitePlace C.F, M.archScaleF u) * M.discNormF * M.covolF

/-- Additive Tamagawa volume `vol(𝔸_E / E)` encoded by `M : AdelicMeasureData C`. -/
def additiveTamagawaVolE {C : CMHostField} (M : AdelicMeasureData C) : ℝ :=
  (∏ w : InfinitePlace C.E, M.archScaleE w) * M.discNormE * M.covolE

theorem additiveTamagawaVolF_pos {C : CMHostField} (M : AdelicMeasureData C) :
    0 < M.additiveTamagawaVolF :=
  mul_pos (mul_pos (Finset.prod_pos fun u _ => M.archScaleF_pos u) M.discNormF_pos) M.covolF_pos

theorem additiveTamagawaVolE_pos {C : CMHostField} (M : AdelicMeasureData C) :
    0 < M.additiveTamagawaVolE :=
  mul_pos (mul_pos (Finset.prod_pos fun w _ => M.archScaleE_pos w) M.discNormE_pos) M.covolE_pos

/-- **Exact Tate–Weil Normalization (`vol(𝔸_F / F) = 1`)**:
for any totally real field `C.F`, the canonical Tamagawa volume of `𝔸_F / F` equals `1`. -/
theorem canonical_additiveTamagawaVolF_eq_one :
    (canonical C).additiveTamagawaVolF = 1 := by
  unfold additiveTamagawaVolF canonical
  simp only [Finset.prod_const_one, one_mul]
  rw [NumberField.mixedEmbedding.covolume_integerLattice C.F, C.nrComplexPlaces_F, pow_zero, one_mul,
    Real.sqrt_eq_rpow, ← Real.rpow_add (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero C.F)))]
  norm_num

/-- **Exact Tate–Weil Normalization (`vol(𝔸_E / E) = 1`)**:
for any totally complex CM field `C.E`, the canonical Tamagawa volume `2^{r₂} |Δ_E|^{-1/2} covol(𝓞_E)` equals `1`. -/
theorem canonical_additiveTamagawaVolE_eq_one :
    (canonical C).additiveTamagawaVolE = 1 := by
  unfold additiveTamagawaVolE canonical
  simp only [Finset.prod_const, Finset.card_univ]
  rw [NumberField.mixedEmbedding.covolume_integerLattice C.E, C.card_infinitePlace_E,
    C.nrComplexPlaces_E_eq_finrank]
  have h2 : (2 : ℝ) ^ Module.finrank ℚ C.F * (2⁻¹ : ℝ) ^ Module.finrank ℚ C.F = 1 := by
    rw [← mul_pow]
    norm_num
  have hd : |(NumberField.discr C.E : ℝ)| ^ (-(1 / 2 : ℝ)) *
      Real.sqrt |(NumberField.discr C.E : ℝ)| = 1 := by
    rw [Real.sqrt_eq_rpow,
      ← Real.rpow_add (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero C.E)))]
    norm_num
  calc (2 : ℝ) ^ Module.finrank ℚ C.F * |(NumberField.discr C.E : ℝ)| ^ (-(1 / 2 : ℝ)) *
        ((2⁻¹ : ℝ) ^ Module.finrank ℚ C.F * Real.sqrt |(NumberField.discr C.E : ℝ)|)
      = ((2 : ℝ) ^ Module.finrank ℚ C.F * (2⁻¹ : ℝ) ^ Module.finrank ℚ C.F) *
          (|(NumberField.discr C.E : ℝ)| ^ (-(1 / 2 : ℝ)) *
            Real.sqrt |(NumberField.discr C.E : ℝ)|) := by ring
    _ = 1 * 1 := by rw [h2, hd]
    _ = 1 := one_mul 1

end AdelicMeasureData

/-- Local unitary `j`-th Euler factor `1 - χ_{E/F}(v)^j * q_v^{-j}` at a finite place `v` of `F`. -/
def localUnitaryEulerFactor (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F)) (j : ℕ) : ℝ :=
  1 - (C.chiEF v) ^ j * (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ))

/-- Local unitary Tamagawa factor `∏_{j=1}^n (1 - χ_{E/F}(v)^j q_v^{-j})⁻¹` at a finite place `v`. -/
def localTamagawaFactor (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 n, (localUnitaryEulerFactor C v j)⁻¹

/-- Global truncated Tamagawa factor of `U(n)` over `S ⊂ HeightOneSpectrum (𝓞 C.F)` with
archimedean / discriminant normalization from `M : AdelicMeasureData C`. -/
def tamagawaFactor (C : CMHostField) (M : AdelicMeasureData C) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 C.F))) : ℝ :=
  M.additiveTamagawaVolE * ∏ v ∈ S, localTamagawaFactor C v n

theorem localUnitaryEulerFactor_pos (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F))
    {j : ℕ} (hj : 1 ≤ j) : 0 < localUnitaryEulerFactor C v j := by
  unfold localUnitaryEulerFactor
  have hq1 : (1 : ℝ) < (Stage5AdelicTate.residueCard v : ℝ) := by
    exact_mod_cast Stage5AdelicTate.one_lt_residueCard v
  have hqpow : (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq1 (by exact_mod_cast (by omega : -(j : ℤ) < 0))
  have hqpos : 0 < (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hq1) _
  have hchi : |(C.chiEF v) ^ j| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (C.abs_chiEF_le_one v)
  have hterm : (C.chiEF v) ^ j * (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ)) < 1 := by
    calc (C.chiEF v) ^ j * (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ))
        ≤ |(C.chiEF v) ^ j * (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ))| := le_abs_self _
      _ = |(C.chiEF v) ^ j| * (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ)) := by
          rw [abs_mul, abs_of_pos hqpos]
      _ ≤ 1 * (Stage5AdelicTate.residueCard v : ℝ) ^ (-(j : ℝ)) :=
          mul_le_mul_of_nonneg_right hchi hqpos.le
      _ < 1 := by linarith
  linarith

theorem localTamagawaFactor_pos (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) :
    0 < localTamagawaFactor C v n := by
  unfold localTamagawaFactor
  refine Finset.prod_pos fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  exact inv_pos.mpr (localUnitaryEulerFactor_pos C v hj.1)

/-- **Strict Positivity of the CM Unitary Tamagawa Factor (`tamagawaFactor_pos`)**:
for every `CMHostField C`, `AdelicMeasureData C`, rank `n : ℕ`, and finite set of places `S`,
`0 < tamagawaFactor C M n S`. -/
theorem tamagawaFactor_pos (C : CMHostField) (M : AdelicMeasureData C) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 C.F))) :
    0 < tamagawaFactor C M n S :=
  mul_pos M.additiveTamagawaVolE_pos (Finset.prod_pos fun v _ => localTamagawaFactor_pos C v n)

end AdelicMeasureSection

/-! ## Section 5: `adelic_product_formula_unit` (Product Formula for CM Fields & Units) -/

section ProductFormulaSection

open Stage5AdelicTate

variable (C : CMHostField)

/-- At every finite place `v`, any global ring-of-integers unit `u : (𝓞 K)ˣ` has `v`-adic
valuation `Valued.v u = 1` and normalized absolute value `finiteAbsVal v u = 1`. -/
theorem finiteAbsVal_unit_eq_one {K : Type*} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteAbsVal v (((u : 𝓞 K) : K) : v.adicCompletion K) = 1 := by
  rw [finiteAbsVal_eq_one_iff_valued_eq_one]
  have hval : ∀ z : 𝓞 K,
      Valued.v (((z : 𝓞 K) : K) : v.adicCompletion K) = v.intValuation z := fun z => by
    rw [show (((z : 𝓞 K) : K) : v.adicCompletion K) =
        HeightOneSpectrum.adicCompletion.ofCompletion
          ((WithVal.equiv (v.valuation K)).symm (z : K)) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : Valued.v (((u : 𝓞 K) : K) : v.adicCompletion K) ≤ 1 := by
    rw [hval]
    exact v.intValuation_le_one _
  have hle2 : Valued.v ((((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) : v.adicCompletion K) ≤ 1 := by
    rw [hval]
    exact v.intValuation_le_one _
  have hmul : Valued.v (((u : 𝓞 K) : K) : v.adicCompletion K) *
      Valued.v ((((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) : v.adicCompletion K) = 1 := by
    rw [hval, hval, ← map_mul]
    have h1 : (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := u.mul_inv
    rw [h1, map_one]
  apply le_antisymm hle1
  have hbound : (1 : WithZero (Multiplicative ℤ)) ≤
      Valued.v (((u : 𝓞 K) : K) : v.adicCompletion K) * 1 := by
    calc (1 : WithZero (Multiplicative ℤ))
        = Valued.v (((u : 𝓞 K) : K) : v.adicCompletion K) *
            Valued.v ((((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) : v.adicCompletion K) := hmul.symm
      _ ≤ Valued.v (((u : 𝓞 K) : K) : v.adicCompletion K) * 1 :=
          mul_le_mul_of_nonneg_left hle2 zero_le
  simpa using hbound

/-- **Full Adelic Product Formula for `x : C.Eˣ`**:
`∏_{w∣∞} |x|_w * ∏'_v |x|_v = 1`. -/
theorem adelic_product_formula_E (x : C.Eˣ) :
    (∏ w : InfinitePlace C.E, infAbsVal w ((x : C.E) : w.Completion)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.E), finiteAbsVal v ((x : C.E) : v.adicCompletion C.E)) = 1 := by
  have h := artin_whaples_product_formula x
  have hinf :
      (∏ w : InfinitePlace C.E, infAbsVal w ((x : C.E) : w.Completion)) =
        ∏ w : InfinitePlace C.E, (w (x : C.E)) ^ w.mult := by
    refine Finset.prod_congr rfl fun w _ => infAbsVal_coe_eq w (x : C.E)
  have hfin :
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.E), finiteAbsVal v ((x : C.E) : v.adicCompletion C.E)) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 C.E),
          (Nat.card (𝓞 C.E ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v ((x : C.E) : v.adicCompletion C.E)) := by
    refine finprod_congr fun v => ?_
    have hxne : ((x : C.E) : v.adicCompletion C.E) ≠ 0 :=
      (map_ne_zero_iff (algebraMap C.E (v.adicCompletion C.E))
        (algebraMap C.E (v.adicCompletion C.E)).injective).mpr x.ne_zero
    exact finiteAbsVal_eq_residueCard_zpow v hxne
  rw [hinf, hfin]
  exact h

/-- **Full Adelic Product Formula for `x : C.Fˣ`**:
`∏_{u∣∞} |x|_u * ∏'_v |x|_v = 1`. -/
theorem adelic_product_formula_F (x : C.Fˣ) :
    (∏ u : InfinitePlace C.F, infAbsVal u ((x : C.F) : u.Completion)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.F), finiteAbsVal v ((x : C.F) : v.adicCompletion C.F)) = 1 := by
  have h := artin_whaples_product_formula x
  have hinf :
      (∏ u : InfinitePlace C.F, infAbsVal u ((x : C.F) : u.Completion)) =
        ∏ u : InfinitePlace C.F, (u (x : C.F)) ^ u.mult := by
    refine Finset.prod_congr rfl fun u _ => infAbsVal_coe_eq u (x : C.F)
  have hfin :
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.F), finiteAbsVal v ((x : C.F) : v.adicCompletion C.F)) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 C.F),
          (Nat.card (𝓞 C.F ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v ((x : C.F) : v.adicCompletion C.F)) := by
    refine finprod_congr fun v => ?_
    have hxne : ((x : C.F) : v.adicCompletion C.F) ≠ 0 :=
      (map_ne_zero_iff (algebraMap C.F (v.adicCompletion C.F))
        (algebraMap C.F (v.adicCompletion C.F)).injective).mpr x.ne_zero
    exact finiteAbsVal_eq_residueCard_zpow v hxne
  rw [hinf, hfin]
  exact h

/-- **UNCONDITIONAL UNIT PRODUCT FORMULA (`adelic_product_formula_unit`)**:
for any CM extension `C : CMHostField` and any global unit `u : (𝓞 C.E)ˣ`:
1. at every finite place `v`, `|u|_v = 1`,
2. at the archimedean places (all complex with multiplicity `2`), `∏_{w∣∞} (w u)^2 = 1`, and
3. the full adelic product satisfies `(∏_{w∣∞} |u|_w) * (∏'_v |u|_v) = 1`. -/
theorem adelic_product_formula_unit (u : (𝓞 C.E)ˣ) :
    (∀ v : HeightOneSpectrum (𝓞 C.E),
      finiteAbsVal v (((u : 𝓞 C.E) : C.E) : v.adicCompletion C.E) = 1) ∧
    (∏ w : InfinitePlace C.E, (w ((u : 𝓞 C.E) : C.E)) ^ 2 = 1) ∧
    ((∏ w : InfinitePlace C.E, infAbsVal w (((u : 𝓞 C.E) : C.E) : w.Completion)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.E),
        finiteAbsVal v (((u : 𝓞 C.E) : C.E) : v.adicCompletion C.E)) = 1) := by
  let uE : C.Eˣ := Units.map (algebraMap (𝓞 C.E) C.E).toMonoidHom u
  have hfull :
      (∏ w : InfinitePlace C.E, infAbsVal w (((u : 𝓞 C.E) : C.E) : w.Completion)) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 C.E),
          finiteAbsVal v (((u : 𝓞 C.E) : C.E) : v.adicCompletion C.E)) = 1 :=
    adelic_product_formula_E C uE
  have hfin_each : ∀ v : HeightOneSpectrum (𝓞 C.E),
      finiteAbsVal v (((u : 𝓞 C.E) : C.E) : v.adicCompletion C.E) = 1 :=
    finiteAbsVal_unit_eq_one u
  have hfin_prod :
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.E),
        finiteAbsVal v (((u : 𝓞 C.E) : C.E) : v.adicCompletion C.E)) = 1 :=
    finprod_eq_one_of_forall_eq_one hfin_each
  have harch :
      ∏ w : InfinitePlace C.E, (w ((u : 𝓞 C.E) : C.E)) ^ 2 = 1 := by
    have hinf_eq :
        (∏ w : InfinitePlace C.E, infAbsVal w (((u : 𝓞 C.E) : C.E) : w.Completion)) =
          ∏ w : InfinitePlace C.E, (w ((u : 𝓞 C.E) : C.E)) ^ 2 := by
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [infAbsVal_coe_eq, (C.infinitePlace_E_isComplex w).mult_eq_two]
    rw [hinf_eq, hfin_prod, mul_one] at hfull
    exact hfull
  exact ⟨hfin_each, harch, hfull⟩

/-- Unit product formula on the totally real base field `C.F`:
for `u : (𝓞 C.F)ˣ`, every finite place has `|u|_v = 1` and `∏_{w∣∞} w(u) = 1`. -/
theorem adelic_product_formula_unit_F (u : (𝓞 C.F)ˣ) :
    (∀ v : HeightOneSpectrum (𝓞 C.F),
      finiteAbsVal v (((u : 𝓞 C.F) : C.F) : v.adicCompletion C.F) = 1) ∧
    (∏ w : InfinitePlace C.F, w ((u : 𝓞 C.F) : C.F) = 1) := by
  let uF : C.Fˣ := Units.map (algebraMap (𝓞 C.F) C.F).toMonoidHom u
  have hfull :
      (∏ w : InfinitePlace C.F, infAbsVal w (((u : 𝓞 C.F) : C.F) : w.Completion)) *
        (∏ᶠ v : HeightOneSpectrum (𝓞 C.F),
          finiteAbsVal v (((u : 𝓞 C.F) : C.F) : v.adicCompletion C.F)) = 1 :=
    adelic_product_formula_F C uF
  have hfin_each := finiteAbsVal_unit_eq_one u
  have hfin_prod :
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.F),
        finiteAbsVal v (((u : 𝓞 C.F) : C.F) : v.adicCompletion C.F)) = 1 :=
    finprod_eq_one_of_forall_eq_one hfin_each
  have harch : ∏ w : InfinitePlace C.F, w ((u : 𝓞 C.F) : C.F) = 1 := by
    have hinf_eq :
        (∏ w : InfinitePlace C.F, infAbsVal w (((u : 𝓞 C.F) : C.F) : w.Completion)) =
          ∏ w : InfinitePlace C.F, w ((u : 𝓞 C.F) : C.F) := by
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [infAbsVal_coe_eq, (C.infinitePlace_F_isReal w).mult_eq_one, pow_one]
    rw [hinf_eq, hfin_prod, mul_one] at hfull
    exact hfull
  exact ⟨hfin_each, harch⟩

/-- Invariance of infinite-place absolute values under CM conjugation `C.conj`. -/
theorem infAbsVal_conj (w : InfinitePlace C.E) (x : C.E) :
    infAbsVal w ((C.conj x : C.E) : w.Completion) = infAbsVal w (x : w.Completion) := by
  rw [infAbsVal_coe_eq, infAbsVal_coe_eq, C.infinitePlace_conj]

/-- Invariance of finite-place absolute values under CM conjugation `C.conj`. -/
theorem finiteAbsVal_conj (w : HeightOneSpectrum (𝓞 C.E)) (y : w.adicCompletion C.E) :
    finiteAbsVal (C.conjHeightOne w) (FiniteAdelesCM.conjCompletionEquiv C w y) =
      finiteAbsVal w y := by
  by_cases hy : y = 0
  · subst hy
    simp [finiteAbsVal]
  · have hy' : FiniteAdelesCM.conjCompletionEquiv C w y ≠ 0 := by
      intro h0
      exact hy ((FiniteAdelesCM.conjCompletionEquiv C w).injective (by simpa using h0))
    rw [finiteAbsVal_eq_residueCard_zpow (C.conjHeightOne w) hy',
      finiteAbsVal_eq_residueCard_zpow w hy]
    have hcard : Nat.card (𝓞 C.E ⧸ (C.conjHeightOne w).asIdeal) =
        Nat.card (𝓞 C.E ⧸ w.asIdeal) := C.residueCard_conjHeightOne w
    have hord : finiteOrd (C.conjHeightOne w) (FiniteAdelesCM.conjCompletionEquiv C w y) =
        finiteOrd w y := by
      unfold finiteOrd
      rw [FiniteAdelesCM.valued_conjCompletionEquiv]
    rw [hcard, hord]

/-- Relative norm product formula: for any `x : C.Eˣ`, both `principalIdele C.E x` and
`principalIdele C.F (Units.map C.cmNorm x)` lie in the norm-1 ideles (`ideleNorm = 1`). -/
theorem adelic_product_formula_relative_norm (x : C.Eˣ) :
    ideleNorm (principalIdele C.E x) = 1 ∧
      ideleNorm (principalIdele C.F (Units.map C.cmNorm x)) = 1 :=
  ⟨ideleNorm_principal x, ideleNorm_principal (Units.map C.cmNorm x)⟩

/-- Product formula for norm-1 unitary elements `x : C.Eˣ` satisfying `C.conj x = x⁻¹`:
`N_{E/F}(x) = 1`, `principalIdele C.E x ∈ NormOneIdeles C.E`, and `∏_v |x|_v = 1`. -/
theorem adelic_product_formula_norm1_unit (x : C.Eˣ)
    (hx : C.conj (x : C.E) = ((x⁻¹ : C.Eˣ) : C.E)) :
    C.cmNorm (x : C.E) = 1 ∧
    principalIdele C.E x ∈ NormOneIdeles C.E ∧
    ((∏ w : InfinitePlace C.E, infAbsVal w ((x : C.E) : w.Completion)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.E), finiteAbsVal v ((x : C.E) : v.adicCompletion C.E)) = 1) := by
  have hnorm : C.cmNorm (x : C.E) = 1 := by
    apply FaithfulSMul.algebraMap_injective C.F C.E
    rw [C.cmNorm_eq_mul_conj, hx, map_one]
    exact x.mul_inv
  exact ⟨hnorm, ideleNorm_principal x, adelic_product_formula_E C x⟩

end ProductFormulaSection

end RHDirect.Stage14M1_CMFieldAdeles

end
