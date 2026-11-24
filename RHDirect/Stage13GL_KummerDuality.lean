import RHDirect.Stage12GaloisShaLen
import RHDirect.Stage13GL_LocalDvrNakayama
import RHDirect.Stage13GL_GaloisCohomLength
import RHDirect.Stage13GL_SelmerTransport
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# RHDirect.Stage13GL_KummerDuality

**GaloisLibrary Wave 2 (3 of 3 — Crown Kummer Duality):** Complete, compressed, zero-wrapper
formalization of the 64-file `GaloisLibrary/KummerTheory` library directly onto concrete Mathlib
types, `RHDirect.Stage12GaloisShaLen`, `RHDirect.Stage13GL_LocalDvrNakayama`,
`RHDirect.Stage13GL_GaloisCohomLength`, and `RHDirect.Stage13GL_SelmerTransport`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.overlappingInstances false

open NumberField IsDedekindDomain IntermediateField Module Representation
open scoped nonZeroDivisors Pointwise
open RHDirect.Stage12GaloisShaLen RHDirect.Stage13GL_LocalDvrNakayama
  RHDirect.Stage13GL_GaloisCohomLength RHDirect.Stage13GL_SelmerTransport

namespace RHDirect.Stage13GL_KummerDuality

/-! ## Section 1: Inlined External Helpers (`PartsSign`, `ExistsCen`, `HilbertNinety`, `CobOfGen`, `PrincTop`/`Generate`, `SUnits`/`PowerIndex`) -/

section ExternalHelpers

section PartsSignHelpers

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]

/-- Complex conjugation on `Ω`: there exists a complex embedding `j : Ω →+* ℂ` intertwining `σ` with `starRingEnd ℂ`. -/
def IsConjOm (σ : Ω ≃+* Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (σ x) = starRingEnd ℂ (j x)

include E in
theorem IsConjOm.cyc {σ : Ω ≃+* Ω} (h : IsConjOm σ) : cyclotomicCharacter Ω l σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ ζ hζ.pow_eq_one
  have h1 : σ ζ * ζ = 1 := by
    apply j.injective
    have : ‖j ζ‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hN0
    rw [map_mul, hj, map_one, Complex.conj_mul', this]
    simp
  rw [hspec, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff, Nat.cast_add,
    ZMod.natCast_zmod_val, Nat.cast_one] at h1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  exact eq_neg_of_add_eq_zero_left h1

variable [IsCMField E]

theorem IsConjOm.isLift {σ : Ω ≃+* Ω} (h : IsConjOm σ) : IsLift (cE E) σ := by
  obtain ⟨j, hj⟩ := h
  intro x
  apply j.injective
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E Ω)) x).symm

omit [IsCMField E] in
include E in
theorem exists_isConjOm : ∃ σ : Ω ≃+* Ω, IsConjOm σ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  let c : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  exact ⟨(c.restrictNormal Ω).toRingEquiv, j.toRingHom, fun x => c.restrictNormal_commutes Ω x⟩

omit [IsCMField E] in
include E in
theorem twScal_conj {σ : Ω ≃+* Ω} (h : IsConjOm σ) (e : ℕ) : twScal l σ (e : ℤ) = (-1) ^ e := by
  rw [twScal, h.cyc (E := E), zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
  simp

private theorem mem_eig_cAct (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ)
    (z : Z1 (qzTw D (e : ℤ))) (s : ℤ_[l]) :
    (Submodule.Quotient.mk z : H1 (qzTw D (e : ℤ))) ∈ (cAct D e).eigenspace ((-1) ^ e * s) ↔
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) - s • z.1 g = qzTw D e g m - m := by
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h.isLift z
  have hs : (-1 : ℤ_[l]) ^ e * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Module.End.mem_eigenspace_iff, cAct, galois_action_cohomology_eq_conj D e h.isLift, e₁,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype,
    mem_B1]
  have key : ∀ g, (z₁ - ((-1 : ℤ_[l]) ^ e * s) • z).1 g =
      (-1 : ℤ_[l]) ^ e • (z.1 (conjGS D h.isLift g) - s • z.1 g) := fun g => by
    show z₁.1 g - (((-1 : ℤ_[l]) ^ e * s) • z).1 g = _
    rw [f₁, twScal_conj (E := E) h, smul_sub, smul_smul]; rfl
  simp only [key]
  refine ⟨fun ⟨m, hm⟩ => ⟨(-1 : ℤ_[l]) ^ e • m, fun g => ?_⟩,
    fun ⟨m, hm⟩ => ⟨(-1 : ℤ_[l]) ^ e • m, fun g => ?_⟩⟩
  · rw [map_smul, ← smul_sub, ← hm, smul_smul, hs, one_smul]
  · rw [map_smul, ← smul_sub, ← hm]

theorem mk_mem_ShaPlus_iff (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ)
    (z : Z1 (qzTw D (e : ℤ))) :
    Submodule.Quotient.mk z ∈ ShaPlus D e ↔ Submodule.Quotient.mk z ∈ Sha D e ∧
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) - z.1 g = qzTw D e g m - m := by
  have := mem_eig_cAct D e h z 1
  simp only [mul_one, one_smul] at this
  exact and_congr_right fun _ => this

theorem mk_mem_ShaMinus_iff (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ)
    (z : Z1 (qzTw D (e : ℤ))) :
    Submodule.Quotient.mk z ∈ ShaMinus D e ↔ Submodule.Quotient.mk z ∈ Sha D e ∧
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) + z.1 g = qzTw D e g m - m := by
  have := mem_eig_cAct D e h z (-1)
  rw [show (-1 : ℤ_[l]) ^ e * (-1) = (-1) ^ (e + 1) by rw [pow_succ]] at this
  simp only [neg_smul, one_smul, sub_neg_eq_add] at this
  exact and_congr_right fun _ => this

end PartsSignHelpers

section ExistsCenHelpers

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem cen_int_mem (A : ValuationSubring Ω) (b : 𝓞 Ω) : (b : Ω) ∈ A := by
  have h : IsIntegral A (b : Ω) := b.isIntegral_coe.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

theorem cen_int_le (A : ValuationSubring Ω) (b : 𝓞 Ω) : A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (cen_int_mem A b)

def cen (A : ValuationSubring Ω) : Ideal (𝓞 Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show A.valuation ((a : Ω) + b) < 1
    exact A.valuation.map_add_lt ha hb
  smul_mem' := fun c b hb => by
    show A.valuation ((c : Ω) * b) < 1
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (cen_int_le A c) zero_le hb

theorem mem_cen {A : ValuationSubring Ω} {b : 𝓞 Ω} : b ∈ cen A ↔ A.valuation (b : Ω) < 1 := Iff.rfl

instance cen_prime (A : ValuationSubring Ω) : (cen A).IsPrime where
  ne_top' := fun h => by
    have : (1 : 𝓞 Ω) ∈ cen A := h ▸ Submodule.mem_top
    simp [mem_cen] at this
  mem_or_mem' := fun {a b} h => by
    by_contra hn
    rw [not_or, mem_cen, mem_cen, not_lt, not_lt] at hn
    rw [mem_cen, show ((a * b : 𝓞 Ω) : Ω) = (a : Ω) * b from rfl, map_mul,
      le_antisymm (cen_int_le A a) hn.1, le_antisymm (cen_int_le A b) hn.2, one_mul] at h
    exact lt_irrefl _ h

theorem cen_val_eq_one {A : ValuationSubring Ω} {s : 𝓞 Ω} (h : s ∉ cen A) :
    A.valuation (s : Ω) = 1 :=
  le_antisymm (cen_int_le A s) (not_lt.1 h)

variable (E) in
theorem cen_frac [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) {x : Ω} (hx : x ∈ A) :
    ∃ b s : 𝓞 Ω, s ∉ cen A ∧ x * s = b := by
  obtain ⟨F, hF, y, rfl⟩ :
      ∃ F : IntermediateField E Ω, FiniteDimensional E F ∧ ∃ y : F, algebraMap F Ω y = x :=
    ⟨E⟮x⟯, adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _),
      ⟨x, mem_adjoin_simple_self E x⟩, rfl⟩
  have : NumberField F := NumberField.of_module_finite E _
  let i : 𝓞 F →+* 𝓞 Ω := algebraMap _ _
  have hi : ∀ n : 𝓞 F, ((i n : 𝓞 Ω) : Ω) = algebraMap F Ω (algebraMap (𝓞 F) F n) := fun _ => rfl
  by_cases hP : (cen A).comap i = ⊥
  · obtain ⟨n, d, hd, e⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
    have hd0 := nonZeroDivisors.ne_zero hd
    refine ⟨i n, i d, fun h => hd0 ((Submodule.mem_bot _).1 (hP ▸ (Ideal.mem_comap.2 h))), ?_⟩
    have hd' : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd0
    rw [hi, hi, ← map_mul, ← e, div_mul_cancel₀ _ hd']
  · let v : HeightOneSpectrum (𝓞 F) := ⟨(cen A).comap i, inferInstance, hP⟩
    obtain ⟨n, d, h | h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := F) y
    · refine ⟨i n, i d, d.2, ?_⟩
      rw [hi, hi, ← map_mul, h]
    · have e : algebraMap F Ω y * (i n : 𝓞 Ω) = (i d : 𝓞 Ω) := by
        rw [hi, hi, ← map_mul, h]
      refine ⟨i d, i n, fun hn => ?_, e⟩
      have h1 : A.valuation ((i d : 𝓞 Ω) : Ω) = 1 := cen_val_eq_one d.2
      rw [← e, map_mul] at h1
      exact absurd h1
        (mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 hx) zero_le hn).ne

theorem cen_coe_smul (g : Ω ≃ₐ[E] Ω) (b : 𝓞 Ω) : ((g • b : 𝓞 Ω) : Ω) = g b := rfl

theorem cen_map_mem [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω)
    (hg : ∀ b : 𝓞 Ω, g • b ∈ cen A → b ∈ cen A) {x : Ω} (hx : x ∈ A) : g x ∈ A := by
  obtain ⟨b, s, hs, e⟩ := cen_frac E A hx
  have h1 := cen_val_eq_one fun h => hs (hg s h)
  have h2 := cen_int_le A (g • b)
  rw [cen_coe_smul, ← e, map_mul, map_mul, ← cen_coe_smul g s, h1, mul_one] at h2
  exact (A.valuation_le_one_iff _).1 h2

theorem cen_of_cong [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) {q : ℕ}
    (hq : q ≠ 0) (hg : ∀ b : 𝓞 Ω, g • b - b ^ q ∈ cen A) :
    g ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, g x - x ^ q ∈ A.nonunits := by
  have hiff : ∀ b : 𝓞 Ω, g • b ∈ cen A ↔ b ∈ cen A := fun b => by
    rw [← (cen_prime A).pow_mem_iff_mem (r := b) q (Nat.pos_of_ne_zero hq)]
    exact ⟨fun h => by simpa using (cen A).sub_mem h (hg b),
      fun h => by simpa using (cen A).add_mem (hg b) h⟩
  refine ⟨?_, fun x hx => ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    refine ⟨fun h => ?_, fun h => cen_map_mem A g⁻¹ (fun b hb => ?_) h⟩
    · simpa using cen_map_mem A g (fun b => (hiff b).1) h
    · simpa using (hiff (g⁻¹ • b)).2 (by simpa using hb)
  · obtain ⟨b, s, hs, e⟩ := cen_frac E A hx
    have h1 : A.valuation (g s) = 1 := cen_val_eq_one fun h => hs ((hiff s).1 h)
    have h2 : A.valuation (s : Ω) = 1 := cen_val_eq_one hs
    have h3 : (g x - x ^ q) * (g s * (s : Ω) ^ q) =
        ((g • b - b ^ q : 𝓞 Ω) : Ω) * (s : Ω) ^ q -
          ((g • s - s ^ q : 𝓞 Ω) : Ω) * (b : Ω) ^ q := by
      have e1 : g x * g s = ((g • b : 𝓞 Ω) : Ω) := by rw [← map_mul, e]; rfl
      have e2 : x ^ q * (s : Ω) ^ q = (b : Ω) ^ q := by rw [← mul_pow, e]
      have hb' : ((g • b - b ^ q : 𝓞 Ω) : Ω) = ((g • b : 𝓞 Ω) : Ω) - (b : Ω) ^ q := by
        change algebraMap (𝓞 Ω) Ω (g • b - b ^ q) = _
        rw [map_sub, map_pow]
      have hs' : ((g • s - s ^ q : 𝓞 Ω) : Ω) = g s - (s : Ω) ^ q := by
        change algebraMap (𝓞 Ω) Ω (g • s - s ^ q) = _
        rw [map_sub, map_pow]; rfl
      rw [hb', hs']
      linear_combination (s : Ω) ^ q * e1 - g s * e2
    have hlt : A.valuation ((g x - x ^ q) * (g s * (s : Ω) ^ q)) < 1 := by
      rw [h3]
      refine A.valuation.map_sub_lt ?_ ?_
      · rw [map_mul, map_pow, h2, one_pow, mul_one]
        exact hg b
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hg s)
          (by rw [map_pow]; exact pow_le_one₀ zero_le (cen_int_le A b))
    rw [map_mul, map_mul, h1, map_pow, h2, one_pow, mul_one, mul_one] at hlt
    exact (A.mem_nonunits_iff).2 hlt

theorem exists_cen (P : Ideal (𝓞 Ω)) [hP : P.IsPrime] : ∃ A : ValuationSubring Ω, cen A = P := by
  let f : Localization.AtPrime P →+* Ω :=
    IsLocalization.lift (M := P.primeCompl) (g := algebraMap (𝓞 Ω) Ω) fun y =>
      isUnit_iff_ne_zero.2 fun h0 => y.2 ((Subtype.ext h0 : (y : 𝓞 Ω) = 0) ▸ P.zero_mem)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    have hs0 : ((s : 𝓞 Ω) : Ω) ≠ 0 := fun hs =>
      s.2 ((Subtype.ext hs : (s : 𝓞 Ω) = 0) ▸ P.zero_mem)
    have h1 : f (IsLocalization.mk' (Localization.AtPrime P) a s) = (a : Ω) / ((s : 𝓞 Ω) : Ω) := by
      rw [IsLocalization.lift_mk'_spec]
      change (a : Ω) = ((s : 𝓞 Ω) : Ω) * ((a : Ω) / ((s : 𝓞 Ω) : Ω))
      rw [mul_div_cancel₀ _ hs0]
    rw [h1, div_eq_zero_iff] at hz
    have ha : (a : Ω) = 0 := hz.resolve_right hs0
    rw [show a = 0 from Subtype.ext ha, IsLocalization.mk'_zero]
  let e : Localization.AtPrime P ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' e.toRingHom e.surjective
  obtain ⟨A, hsub, hloc⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.mk f.range)
  refine ⟨A, Ideal.ext fun b => ?_⟩
  have hfb : f (algebraMap (𝓞 Ω) (Localization.AtPrime P) b) = (b : Ω) := by
    simp [f]
  have hmemA : (b : Ω) ∈ A := hsub ⟨algebraMap (𝓞 Ω) _ b, hfb⟩
  rw [mem_cen, show A.valuation (b : Ω) < 1 ↔
    (⟨(b : Ω), hmemA⟩ : A) ∈ IsLocalRing.maximalIdeal A from
      (A.valuation_lt_one_iff ⟨(b : Ω), hmemA⟩).symm]
  have h1 : (⟨(b : Ω), hmemA⟩ : A) ∈ IsLocalRing.maximalIdeal A ↔
      (⟨(b : Ω), ⟨algebraMap (𝓞 Ω) _ b, hfb⟩⟩ : f.range) ∈ IsLocalRing.maximalIdeal f.range := by
    have := hloc.map_nonunit (⟨(b : Ω), ⟨algebraMap (𝓞 Ω) _ b, hfb⟩⟩ : f.range)
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using
      ⟨fun h hu => h (hu.map (Subring.inclusion hsub)), fun h hu => h (this hu)⟩
  rw [h1]
  have heq : e (algebraMap (𝓞 Ω) (Localization.AtPrime P) b) =
      ⟨(b : Ω), ⟨algebraMap (𝓞 Ω) _ b, hfb⟩⟩ := Subtype.ext hfb
  have h2 : (⟨(b : Ω), ⟨algebraMap (𝓞 Ω) _ b, hfb⟩⟩ : f.range) ∈ IsLocalRing.maximalIdeal f.range ↔
      algebraMap (𝓞 Ω) (Localization.AtPrime P) b ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    rw [← heq, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    exact not_congr ⟨fun hu => by simpa [e.symm_apply_apply] using hu.map e.symm.toRingHom,
      fun hu => hu.map e.toRingHom⟩
  rw [h2, ← Ideal.mem_comap]
  exact SetLike.ext_iff.1 (Localization.AtPrime.under_maximalIdeal (I := P)) b

theorem cen_lift [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L]
    [NumberField L] (Q : Ideal (𝓞 Ω)) [Q.IsMaximal] (τ : L ≃ₐ[E] L)
    (θ : 𝓞 Ω ⧸ Q →+* 𝓞 Ω ⧸ Q)
    (hτ : ∀ x : 𝓞 L, θ (Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) x)) =
      Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) (τ • x))) :
    ∃ φ : Ω ≃ₐ[E] Ω, AlgEquiv.restrictNormalHom L φ = τ ∧
      ∀ b : 𝓞 Ω, Ideal.Quotient.mk Q (φ • b) = θ (Ideal.Quotient.mk Q b) := by
  let G := L.fixingSubgroup
  let _ : TopologicalSpace (𝓞 Ω) := ⊥
  have : DiscreteTopology (𝓞 Ω) := ⟨rfl⟩
  have : CompactSpace G :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  have hfix : ∀ (g : G) (a : 𝓞 L), g • algebraMap (𝓞 L) (𝓞 Ω) a = algebraMap (𝓞 L) (𝓞 Ω) a :=
    fun g a => RingOfIntegers.ext ((mem_fixingSubgroup_iff _ _).1 g.2 _ (a : L).2)
  have : SMulCommClass G (𝓞 L) (𝓞 Ω) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have hopen : ∀ b : 𝓞 Ω, IsOpen (MulAction.stabilizer (Ω ≃ₐ[E] Ω) b : Set (Ω ≃ₐ[E] Ω)) :=
    fun b => by
      have : FiniteDimensional E E⟮(b : Ω)⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
      exact Subgroup.isOpen_mono (H₁ := (E⟮(b : Ω)⟯).fixingSubgroup) (fun σ hσ => RingOfIntegers.ext
        ((mem_fixingSubgroup_iff _ _).1 hσ _ (mem_adjoin_simple_self E _)))
        (E⟮(b : Ω)⟯).fixingSubgroup_isOpen
  have : ContinuousSMul G (𝓞 Ω) := continuousSMul_iff_stabilizer_isOpen.2 fun b =>
    (hopen b).preimage continuous_subtype_val
  have : Algebra.IsInvariant (𝓞 L) (𝓞 Ω) G := ⟨fun b hb => by
    have hmem : (b : Ω) ∈ fixedField L.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro f hf
      exact congrArg (fun c : 𝓞 Ω => (c : Ω)) (hb ⟨f, hf⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hint : IsIntegral ℤ (⟨b, hmem⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Ω) (algebraMap L Ω).injective).1 b.isIntegral_coe
    exact ⟨⟨⟨b, hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩⟩
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) τ
  have hgL : ∀ x : 𝓞 L, g • algebraMap (𝓞 L) (𝓞 Ω) x = algebraMap (𝓞 L) (𝓞 Ω) (τ • x) :=
    fun x => RingOfIntegers.ext (by
      rw [← hg]
      exact (AlgEquiv.restrictNormal_commutes g L x).symm)
  let _ : Field (𝓞 Ω ⧸ Q) := Ideal.Quotient.field Q
  have hunder : Q.under (𝓞 L) = (g⁻¹ • Q).under (𝓞 L) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff, hgL,
      ← Ideal.Quotient.eq_zero_iff_mem (I := Q), ← Ideal.Quotient.eq_zero_iff_mem (I := Q),
      ← hτ, map_eq_zero θ]
  obtain ⟨h, hh⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 L) (G := G) Q (g⁻¹ • Q) hunder
  set g' : Ω ≃ₐ[E] Ω := g * h with hg'
  have hst : g' • Q = Q := by
    rw [hg', mul_smul]
    exact (congrArg (g • ·) (show (h : Ω ≃ₐ[E] Ω) • Q = g⁻¹ • Q from hh.symm)).trans
      (smul_inv_smul g Q)
  have hmem : ∀ b : 𝓞 Ω, g'⁻¹ • b ∈ Q ↔ b ∈ Q := fun b => by
    rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hst]
  let u : 𝓞 Ω ⧸ Q →+* 𝓞 Ω ⧸ Q :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ _ g'⁻¹) fun b hb => (hmem b).2 hb
  have hu : ∀ b : 𝓞 Ω, u (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g'⁻¹ • b) := fun _ => rfl
  have hg'L : ∀ x : 𝓞 L, g'⁻¹ • algebraMap (𝓞 L) (𝓞 Ω) (τ • x) = algebraMap (𝓞 L) (𝓞 Ω) x :=
    fun x => by
      rw [inv_smul_eq_iff, hg', mul_smul, ← hgL]
      exact congrArg (g • ·) (hfix h x).symm
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  let ψ : (𝓞 Ω ⧸ Q) →ₐ[𝓞 L ⧸ Q.under (𝓞 L)] (𝓞 Ω ⧸ Q) :=
    { θ.comp u with
      commutes' := fun c => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ : ∃ y, τ • y = x := ⟨τ⁻¹ • x, smul_inv_smul τ x⟩
        show θ (u (Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) (τ • y)))) =
          Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) (τ • y))
        rw [hu, hg'L, hτ] }
  have hmax : (Q.under (𝓞 L)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  let _ : Field (𝓞 L ⧸ Q.under (𝓞 L)) := Ideal.Quotient.field _
  have hbij : Function.Bijective ψ := Algebra.IsAlgebraic.algHom_bijective ψ
  obtain ⟨k, hk⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (Q.under (𝓞 L)) Q
    (AlgEquiv.ofBijective ψ hbij)
  refine ⟨((k : G) : Ω ≃ₐ[E] Ω) * g', ?_, fun b => ?_⟩
  · have hker : ∀ s : G, AlgEquiv.restrictNormalHom L (s : Ω ≃ₐ[E] Ω) = 1 := fun s => by
      rw [← MonoidHom.mem_ker, restrictNormalHom_ker]
      exact s.2
    rw [hg', map_mul, map_mul, hker, hker, hg, one_mul, mul_one]
  · have e := DFunLike.congr_fun hk (Ideal.Quotient.mk Q (g' • b))
    rw [mul_smul]
    refine (show _ = ψ (Ideal.Quotient.mk Q (g' • b)) from e).trans ?_
    show θ (u _) = _
    rw [hu, inv_smul_smul]

end ExistsCenHelpers

section Hilbert90AndCobOfGen

/-- Continuous Hilbert's Theorem 90 for locally constant 1-cocycles `G K Ω → Ωˣ`. -/
theorem h90 (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (f : G K Ω → Ω) (hlc : IsLocallyConstant f) (h0 : ∀ g, f g ≠ 0)
    (hc : ∀ g h, f (g * h) = f g * g (f h)) :
    ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β := by
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : G K Ω) := (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : G K Ω), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set (G K Ω)) := L.fixingSubgroup_isOpen
  haveI : Finite (G K Ω ⧸ L.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (G K Ω ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (G K Ω ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : G K Ω) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : G K Ω) (x : Ω) := fun _ _ => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : G K Ω, f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g
    rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : G K Ω) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm

/-- A continuous 1-cocycle vanishing on `ker χ` is a coboundary once `ρ γ - 1` is surjective
for a topological generator `γ` of `im χ ≤ ℤ_[l]ˣ`. -/
theorem cobOfGen (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (γ : Γ) (hχ : Continuous χ) (hρ : ContAction ρ)
    (hker : ∀ g, χ g = 1 → ∀ m, ρ g m = m)
    (hgen : ∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure)
    (hsurj : Function.Surjective fun m => ρ γ m - m)
    {z : Γ → M} (hz : z ∈ Z1 ρ) (hz0 : ∀ g, χ g = 1 → z g = 0) : z ∈ B1 ρ := by
  obtain ⟨hzc, hzm⟩ := hz
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  obtain ⟨m, hm⟩ := hsurj (z γ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by simp [hone]
      mul_mem' := fun {a b} ha hb => by
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha, hb, map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := fun {a} ha => by
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha, map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    hρ.comp (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      (Subgroup.zpowers_le.2 ⟨γ, hm.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  exact ⟨m, funext fun g => (hall g).symm⟩

end Hilbert90AndCobOfGen

section PadicPrincHelpers

variable {l : ℕ} [Fact l.Prime]

theorem princ_anti {a b : ℕ} (h : a ≤ b) : princ l b ≤ princ l a := fun u hu => by
  rw [mem_princ] at hu ⊢
  exact (pow_dvd_pow (l : ℤ_[l]) h).trans hu

theorem princ_one_eq_ker : princ l 1 = (red l).ker := by
  ext u
  rw [mem_princ, pow_one, MonoidHom.mem_ker, red, Units.ext_iff, Units.coe_map, Units.val_one]
  change (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 ↔ PadicInt.toZMod (u : ℤ_[l]) = 1
  rw [← sub_eq_zero, ← map_one PadicInt.toZMod, ← map_sub, ← RingHom.mem_ker,
    PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

theorem mem_of_isClosed_princ {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {x : ℤ_[l]ˣ}
    (h : ∀ b, ∃ u ∈ U, redPow l b u = redPow l b x) : x ∈ U := by
  rw [← SetLike.mem_coe, ← hU.closure_eq, mem_closure_iff_nhds]
  intro t ht
  have ht' : (fun y => x * y) ⁻¹' t ∈ nhds (1 : ℤ_[l]ˣ) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using ht
  obtain ⟨b, hb⟩ : ∃ b, (princ l b : Set ℤ_[l]ˣ) ⊆ (fun y => x * y) ⁻¹' t := by
    rw [(Units.isOpenEmbedding_val (R := ℤ_[l])).isEmbedding.isInducing.nhds_eq_comap,
      Filter.mem_comap] at ht'
    obtain ⟨s, hs, hst⟩ := ht'
    rw [Units.val_one, Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hball⟩ := hs
    obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l))
    refine ⟨b, fun u hu => hst (hball ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hu' : u ∈ princ l b := hu
    rw [mem_princ] at hu'
    obtain ⟨c, hc⟩ := hu'
    have hnorm : ‖(u : ℤ_[l]) - 1‖ ≤ ((l : ℝ)⁻¹) ^ b := by
      rw [hc, norm_mul, PadicInt.norm_p_pow, zpow_neg, zpow_natCast, inv_pow]
      exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c)
    exact hnorm.trans_lt hb
  obtain ⟨u, hu, hux⟩ := h b
  have hmem : x⁻¹ * u ∈ princ l b := by
    show x⁻¹ * u ∈ (redPow l b).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
  exact ⟨u, by simpa using hb hmem, hu⟩

private theorem gen_exists_nat {t : ℤ_[l]} (ht : IsUnit t) (d : ℤ_[l]) :
    ∃ j : ℕ, (l : ℤ_[l]) ∣ d + t * j := by
  have htz : PadicInt.toZMod t ≠ 0 := (ht.map PadicInt.toZMod).ne_zero
  refine ⟨(-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val, ?_⟩
  have hm : d + t * ((-(PadicInt.toZMod d) * (PadicInt.toZMod t)⁻¹ : ZMod l).val : ℤ_[l]) ∈
      RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [RingHom.mem_ker, map_add, map_mul, map_natCast, ZMod.natCast_zmod_val]
    field_simp
    ring
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact hm

private theorem gen_emult {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]}
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ l ^ n - 1) = ((a + n : ℕ) : ℕ∞) := by
  have hlp : Prime l := Nat.prime_iff.mp Fact.out
  have h1 : (l : ℤ_[l]) ∣ u - 1 := by
    have := pow_dvd_of_le_emultiplicity (k := 1) (a := (l : ℤ_[l])) (b := u - 1)
      (by rw [hu]; exact_mod_cast ha)
    simpa using this
  by_cases hl : l = 2
  · have h2 : (l : ℤ_[l]) ^ 2 ∣ u - 1 :=
      pow_dvd_of_le_emultiplicity (by rw [hu]; exact_mod_cast ha2 hl)
    rw [emultiplicity_pow_sub_one_sq h2, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast; rfl
  · rw [emultiplicity_pow_sub_one_odd hl h1, hu, emultiplicity_pow_self_of_prime hlp]
    push_cast; rfl

private theorem isUnit_padicInt_of_not_dvd {t : ℤ_[l]} (h : ¬ (l : ℤ_[l]) ∣ t) : IsUnit t := by
  by_contra hne
  have hm : t ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  exact h hm

private theorem exists_pow_eq_one_add_mul_sub_add_sq (v : ℤ_[l]) (j : ℕ) :
    ∃ c : ℤ_[l], v ^ j = 1 + (j : ℤ_[l]) * (v - 1) + (v - 1) ^ 2 * c := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨j + v * c, ?_⟩
    push_cast; rw [pow_succ, hc]; ring

private theorem gen_dvd {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]} (hunit : IsUnit u)
    (hu : emultiplicity (l : ℤ_[l]) (u - 1) = a) {x : ℤ_[l]} (hx : (l : ℤ_[l]) ^ a ∣ x - 1)
    (n : ℕ) : ∃ k : ℕ, (l : ℤ_[l]) ^ (a + n) ∣ u ^ k - x := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [pow_zero, add_zero, show (1 : ℤ_[l]) - x = -(x - 1) by ring]
    exact dvd_neg.mpr hx
  | succ n ih =>
    obtain ⟨k, d, hd⟩ := ih
    set v := u ^ l ^ n with hvdef
    have hv := gen_emult ha ha2 hu n
    obtain ⟨t, ht⟩ := pow_dvd_of_le_emultiplicity (le_of_eq hv.symm)
    have htu : IsUnit t := by
      apply isUnit_padicInt_of_not_dvd
      rintro ⟨s, hs⟩
      have hdv : (l : ℤ_[l]) ^ (a' + 1 + n + 1) ∣ v - 1 := ⟨s, by rw [ht, hs]; ring⟩
      have := le_emultiplicity_of_pow_dvd hdv
      rw [hv] at this
      norm_cast at this; omega
    obtain ⟨j, e, he⟩ := gen_exists_nat ((hunit.pow k).mul htu) d
    obtain ⟨c, hc⟩ := exists_pow_eq_one_add_mul_sub_add_sq v j
    refine ⟨k + l ^ n * j, e + (l : ℤ_[l]) ^ (a' + n) * u ^ k * t ^ 2 * c, ?_⟩
    rw [pow_add, pow_mul, ← hvdef]
    linear_combination u ^ k * hc + hd + ((u ^ k) * j + u ^ k * c *
      (v - 1 + (l : ℤ_[l]) ^ (a' + 1 + n) * t)) * ht + (l : ℤ_[l]) ^ (a' + 1 + n) * he

theorem exists_pow_redPow_eq {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {u : ℤ_[l]ˣ}
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) {x : ℤ_[l]ˣ} (hx : x ∈ princ l a)
    (b : ℕ) : ∃ k : ℕ, redPow l b (u ^ k) = redPow l b x := by
  rw [mem_princ] at hx
  obtain ⟨k, hk⟩ := gen_dvd ha ha2 u.isUnit hu hx b
  refine ⟨k, Units.ext ?_⟩
  have hkb : (l : ℤ_[l]) ^ b ∣ (u : ℤ_[l]) ^ k - x :=
    (pow_dvd_pow _ (Nat.le_add_left b a)).trans hk
  have hm : (u : ℤ_[l]) ^ k - x ∈ RingHom.ker (PadicInt.toZModPow b : ℤ_[l] →+* ZMod (l ^ b)) := by
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
    exact hkb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  simpa [redPow] using hm

theorem princ_le_of_isClosed {a : ℕ} (ha : 1 ≤ a) (ha2 : l = 2 → 2 ≤ a) {U : Subgroup ℤ_[l]ˣ}
    (hU : IsClosed (U : Set ℤ_[l]ˣ)) {u : ℤ_[l]ˣ} (huU : u ∈ U)
    (hu : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a) : princ l a ≤ U := by
  intro x hx
  refine mem_of_isClosed_princ hU fun b => ?_
  obtain ⟨k, hk⟩ := exists_pow_redPow_eq ha ha2 hu hx b
  exact ⟨u ^ k, U.pow_mem huU k, hk⟩

theorem mem_galImage_iff_of_equiv {E E' : Type*} [Field E] [CharZero E] [Field E'] (f : E ≃+* E')
    (Ω : Type*) [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω] (u : ℤ_[l]ˣ) :
    u ∈ galImage l E ↔ ∃ g : Ω ≃ₐ[E'] Ω, cyclotomicCharacter Ω l g.toRingEquiv = u := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E'
  haveI : CharZero E' := charZero_of_injective_ringHom (f := f.toRingHom) f.injective
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E' Ω).injective
  let ε := IsAlgClosure.equivOfEquiv (AlgebraicClosure E) Ω f
  have hε : ∀ s : E, ε (algebraMap E (AlgebraicClosure E) s) = algebraMap E' Ω (f s) :=
    IsAlgClosure.equivOfEquiv_algebraMap _ _ f
  have hε' : ∀ r : E',
      ε.symm (algebraMap E' Ω r) = algebraMap E (AlgebraicClosure E) (f.symm r) :=
    IsAlgClosure.equivOfEquiv_symm_algebraMap _ _ f
  simp only [galImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩
    let gr : Ω ≃+* Ω := ε.symm.trans (σ.toRingEquiv.trans ε)
    refine ⟨AlgEquiv.ofRingEquiv (f := gr) fun r => ?_, ?_⟩
    · simp only [gr, RingEquiv.trans_apply, hε', AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, hε,
        RingEquiv.apply_symm_apply]
    · simp only [eps, MonoidHom.comp_apply]
      exact cyclotomicCharacter_conj l ε _ _ fun x => by
        simp [gr, MulSemiringAction.toRingAut_apply]
  · rintro ⟨g, rfl⟩
    let sr := ε.trans (g.toRingEquiv.trans ε.symm)
    refine ⟨AlgEquiv.ofRingEquiv (f := sr) fun s => ?_, ?_⟩
    · simp [sr, hε, hε']
    · simp only [eps, MonoidHom.comp_apply]
      symm
      exact cyclotomicCharacter_conj l ε _ _ fun x => by
        simp [sr, MulSemiringAction.toRingAut_apply]

theorem isOpen_galImage_of_nf (E : Type) [Field E] [NumberField E] :
    IsOpen (galImage l E : Set ℤ_[l]ˣ) := by
  let Ω := AlgebraicClosure E
  have hpos : ∃ v : HeightOneSpectrum (𝓞 E), v ∈ Above E l := by
    have hlt : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ ⊤ := by
      intro h
      have hu : IsUnit ((l : ℕ) : 𝓞 E) := Ideal.span_singleton_eq_top.1 h
      have h1 : IsUnit (Algebra.norm ℤ ((l : ℕ) : 𝓞 E)) := hu.map (Algebra.norm ℤ)
      rw [show ((l : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l : ℤ) by simp, Algebra.norm_algebraMap,
        Int.isUnit_iff_natAbs_eq] at h1
      have h2 : l ^ Module.finrank ℤ (𝓞 E) = 1 := by
        simpa [Int.natAbs_pow] using h1
      have hfr : 0 < Module.finrank ℤ (𝓞 E) := by
        rw [NumberField.RingOfIntegers.rank]
        exact Module.finrank_pos
      have : l = 1 := (Nat.pow_eq_one.1 h2).resolve_right hfr.ne'
      exact (Fact.out : l.Prime).ne_one this
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hlt
    have hbot : P ≠ ⊥ := by
      intro hb
      rw [hb] at hle
      have h0 : ((l : ℕ) : 𝓞 E) = 0 := Ideal.mem_bot.1 (hle (Ideal.subset_span rfl))
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h0)
    exact ⟨⟨P, hP.isPrime, hbot⟩, hle (Ideal.subset_span rfl)⟩
  obtain ⟨v, hv⟩ := hpos
  have hopen := (ineOpen E Ω l v (placeOf Ω v) hv (isPlaceOver_placeOf Ω v)).1
  refine Subgroup.isOpen_mono (H₁ := ineImage E l (placeOf Ω v)) ?_ hopen
  rintro u ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

theorem exists_cyc_pow_ne_one (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ) (hn : n ≠ 0) :
    ∃ g : G E Ω, cycZ E Ω l g ^ n ≠ 1 := by
  have hopen := isOpen_galImage_of_nf (l := l) E
  rw [isOpen_iff_princ_le] at hopen
  obtain ⟨a, ha⟩ := hopen
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[l]ˣ, u ∈ princ l a ∧ u ^ n ≠ 1 := by
    have hl : l.Prime := Fact.out
    set m := max a 2
    let x : ℤ_[l] := 1 + (l : ℤ_[l]) ^ m
    have hux : IsUnit x := by
      apply isUnit_padicInt_of_not_dvd
      intro hd
      have h1 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ m := dvd_pow_self _ (by omega)
      have h2 : (l : ℤ_[l]) ∣ (1 : ℤ_[l]) := by simpa [x] using dvd_sub hd h1
      have h3 : ‖(l : ℤ_[l])‖ = 1 := PadicInt.isUnit_iff.1 (isUnit_of_dvd_one h2)
      rw [PadicInt.norm_p] at h3
      exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt : (1 : ℝ) < l)).ne h3
    refine ⟨hux.unit, princ_anti (le_max_left a 2) (by rw [mem_princ]; exact ⟨1, by simp [x, m]⟩), ?_⟩
    intro hpow
    have h1 : x ^ n = 1 := by
      have := congrArg (fun z : ℤ_[l]ˣ => (z : ℤ_[l])) hpow
      simpa using this
    have hlp : Prime (l : ℤ_[l]) := PadicInt.prime_p
    have hfin : emultiplicity (l : ℤ_[l]) (x - 1) = m := by
      have : x - 1 = (l : ℤ_[l]) ^ m := by simp [x]
      rw [this, emultiplicity_pow_self_of_prime hlp]
    have hd2 : (l : ℤ_[l]) ^ 2 ∣ x - 1 := by
      rw [show x - 1 = (l : ℤ_[l]) ^ m by simp [x]]
      exact pow_dvd_pow _ (le_max_right a 2)
    have hdiv : emultiplicity (l : ℤ_[l]) (x ^ n - 1) =
        emultiplicity (l : ℤ_[l]) (x - 1) + emultiplicity l n := by
      by_cases hl2 : l = 2
      · exact emultiplicity_pow_sub_one_sq hd2 n
      · have hd1 : (l : ℤ_[l]) ∣ x - 1 :=
          (show (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ 2 from dvd_pow_self _ (by norm_num)).trans hd2
        exact emultiplicity_pow_sub_one_odd hl2 hd1 n
    rw [h1, sub_self, emultiplicity_zero, hfin] at hdiv
    have hne : emultiplicity l n ≠ ⊤ := by
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity
        (Nat.finiteMultiplicity_iff.2 ⟨hl.ne_one, Nat.pos_of_ne_zero hn⟩)]
      exact WithTop.coe_ne_top
    exact hne (by simpa [WithTop.add_eq_top] using hdiv.symm)
  have huG : u ∈ galImage l E := ha hu.1
  obtain ⟨g, hg⟩ := (mem_galImage_iff_of_equiv (RingEquiv.refl E) Ω u).1 huG
  exact ⟨g, by simpa [cycZ, hg] using hu.2⟩

end PadicPrincHelpers

section SUnitPowerIndex

variable {K : Type*} [Field K] [NumberField K]

private theorem forall_valuation_eq_one_iff_sunit (x : Kˣ) :
    (∀ v : HeightOneSpectrum (𝓞 K), v.valuation K (x : K) = 1) ↔
      x ∈ (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K)).range := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K (x : K) fun v => (h v).le
    obtain ⟨b, hb⟩ :=
      HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((x⁻¹ : Kˣ) : K) fun v => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one]
    have hab : a * b = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, ha, hb, map_one, Units.mul_inv]
    refine ⟨⟨a, b, hab, mul_comm a b ▸ hab⟩, Units.ext (by simpa using ha)⟩
  · rintro ⟨u, rfl⟩ v
    rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq,
      WithZero.coe_one]

theorem valuation_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x)
    (v : HeightOneSpectrum (𝓞 K)) : v.valuation K (x : K) = 1 := by
  have h := v.valuationOfNeZero.isOfFinOrder hx
  rw [isOfFinOrder_iff_eq_one] at h
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, h, WithZero.coe_one]

private def sUnitOfUnits (S : Set (HeightOneSpectrum (𝓞 K))) : (𝓞 K)ˣ →* S.unit K where
  toFun u := ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, fun v _ =>
    (forall_valuation_eq_one_iff_sunit _).mpr ⟨u, rfl⟩ v⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

private theorem sUnitOfUnits_injective (S : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (sUnitOfUnits S (K := K)) := by
  intro u u' h
  have : ((sUnitOfUnits S u : Kˣ) : K) = ((sUnitOfUnits S u' : Kˣ) : K) := by rw [h]
  exact Units.ext (IsFractionRing.injective (𝓞 K) K this)

private def valuationVector (S : Set (HeightOneSpectrum (𝓞 K))) :
    Additive (S.unit K) →ₗ[ℤ] (S → ℤ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x v => Multiplicative.toAdd (v.1.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ))
      map_zero' := by funext v; simp
      map_add' := fun x y => by funext v; simp }

private def unitsEquivKer (S : Set (HeightOneSpectrum (𝓞 K))) :
    Additive (𝓞 K)ˣ ≃ₗ[ℤ] LinearMap.ker (valuationVector S) :=
  (LinearEquiv.ofInjective (sUnitOfUnits S).toAdditive.toIntLinearMap
    (sUnitOfUnits_injective S)).trans (LinearEquiv.ofEq _ _ <| by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · rintro ⟨u, hu⟩
        have hx : sUnitOfUnits S u.toMul = x.toMul := congrArg Additive.toMul hu
        funext v
        have h1 : valuationVector S x v =
            Multiplicative.toAdd (v.1.valuationOfNeZero ((sUnitOfUnits S u.toMul : S.unit K) : Kˣ)) := by
          change Multiplicative.toAdd (v.1.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ)) = _
          rw [hx]
        rw [h1, Pi.zero_apply, toAdd_eq_zero, ← WithZero.coe_inj,
          HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one]
        exact (forall_valuation_eq_one_iff_sunit _).mpr ⟨u.toMul, rfl⟩ v.1
      · intro h
        have hall : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x.toMul : Kˣ) : K) = 1 := by
          intro v
          by_cases hv : v ∈ S
          · have h1 : Multiplicative.toAdd (v.valuationOfNeZero ((x.toMul : S.unit K) : Kˣ)) = 0 :=
              congrFun h ⟨v, hv⟩
            rw [toAdd_eq_zero] at h1
            rw [← HeightOneSpectrum.valuationOfNeZero_eq, h1, WithZero.coe_one]
          · exact x.toMul.2 v hv
        obtain ⟨u, hu⟩ := (forall_valuation_eq_one_iff_sunit _).mp hall
        exact ⟨Additive.ofMul u, congrArg Additive.ofMul (Subtype.ext hu)⟩)

private theorem exists_pow_classNumber_eq_span (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ v.asIdeal ^ classNumber K = Ideal.span {a} := by
  let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : ClassGroup.mk0 (I ^ classNumber K) = 1 := by
    rw [map_pow, classNumber, Fintype.card_eq_nat_card]
    exact pow_card_eq_one'
  obtain ⟨a, ha⟩ := ((ClassGroup.mk0_eq_one_iff (I ^ classNumber K).2).mp h1).principal
  have ha' : v.asIdeal ^ classNumber K = Ideal.span {a} := by
    rw [SubmonoidClass.coe_pow] at ha; exact ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'
  exact pow_ne_zero _ v.ne_bot ha'

private def placeUnit (v : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (exists_pow_classNumber_eq_span v).choose) <| by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact (exists_pow_classNumber_eq_span v).choose_spec.1

open scoped Classical in
private theorem valuationOfNeZero_placeUnit (v w : HeightOneSpectrum (𝓞 K)) :
    w.valuationOfNeZero (placeUnit v) =
      if w = v then Multiplicative.ofAdd (-(classNumber K : ℤ)) else 1 := by
  have ha := (exists_pow_classNumber_eq_span v).choose_spec.1
  have hsp := (exists_pow_classNumber_eq_span v).choose_spec.2
  rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq, placeUnit, Units.val_mk0,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity w ha, ← hsp]
  split_ifs with hw
  · subst hw; rw [multiplicity_pow_self_of_prime w.prime]; rfl
  · have h0 : multiplicity w.asIdeal (v.asIdeal ^ classNumber K) = 0 := by
      rw [multiplicity_eq_zero]
      intro hdvd
      apply hw
      exact HeightOneSpectrum.ext
        (v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.le_of_dvd (w.prime.dvd_of_dvd_pow hdvd))).symm
    rw [h0]; simp

private theorem placeUnit_mem (S : Set (HeightOneSpectrum (𝓞 K))) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ S) : placeUnit v ∈ S.unit K := fun w hw => by
  have hwv : w ≠ v := fun h => hw (h ▸ hv)
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, valuationOfNeZero_placeUnit, if_neg hwv,
    WithZero.coe_one]

private def sUnitTorsionEquiv (S : Set (HeightOneSpectrum (𝓞 K))) :
    Units.torsion K ≃* CommGroup.torsion (S.unit K) :=
  MulEquiv.ofBijective
    ({ toFun := fun ζ => ⟨sUnitOfUnits S ζ, (sUnitOfUnits S).isOfFinOrder ζ.2⟩
       map_one' := Subtype.ext (map_one (sUnitOfUnits S))
       map_mul' := fun a b => Subtype.ext (map_mul (sUnitOfUnits S) (a : (𝓞 K)ˣ) b) } :
        Units.torsion K →* CommGroup.torsion (S.unit K)) <| by
    constructor
    · intro a b h; exact Subtype.ext (sUnitOfUnits_injective S (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      have hx' : IsOfFinOrder (x : Kˣ) := (S.unit K).subtype.isOfFinOrder hx
      obtain ⟨u, hu⟩ :=
        (forall_valuation_eq_one_iff_sunit (x : Kˣ)).mp (valuation_eq_one_of_isOfFinOrder hx')
      have hux : sUnitOfUnits S u = x := Subtype.ext hu
      refine ⟨⟨u, ?_⟩, Subtype.ext hux⟩
      change u ∈ CommGroup.torsion _
      rw [CommGroup.mem_torsion, ← orderOf_pos_iff,
        ← orderOf_injective (sUnitOfUnits S) (sUnitOfUnits_injective S), hux, orderOf_pos_iff]
      exact hx

theorem sUnit_finite_torsion (S : Set (HeightOneSpectrum (𝓞 K))) :
    Finite (CommGroup.torsion (S.unit K)) :=
  Finite.of_equiv _ (sUnitTorsionEquiv S).toEquiv

theorem sUnit_fg (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] : Group.FG (S.unit K) := by
  haveI : Module.Finite ℤ (Additive (S.unit K)) := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (valuationVector S)
      (IsNoetherian.noetherian _) ?_
    rw [inf_of_le_right le_top, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv (unitsEquivKer S)
  rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg,
    ← Module.Finite.iff_addGroup_fg]
  infer_instance

theorem sUnit_finrank_quotient_torsion (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    finrank ℤ (Additive (S.unit K ⧸ CommGroup.torsion (S.unit K))) =
      Units.rank K + Nat.card S := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Module.Finite ℤ (Additive (S.unit K)) := by
    rw [Module.finite_def]
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (valuationVector S)
      (IsNoetherian.noetherian _) ?_
    rw [inf_of_le_right le_top, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv (unitsEquivKer S)
  have hrange : finrank ℤ (LinearMap.range (valuationVector S)) = Nat.card S := by
    apply le_antisymm
    · calc finrank ℤ (LinearMap.range (valuationVector S)) ≤ finrank ℤ (S → ℤ) :=
            Submodule.finrank_le _
        _ = Nat.card S := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
    · let pm : (S → ℤ) →ₗ[ℤ] Additive (S.unit K) :=
        (Pi.basisFun ℤ S).constr ℤ fun v => Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩
      have hcomp : valuationVector S ∘ₗ pm = (-(classNumber K : ℤ)) • LinearMap.id := by
        refine (Pi.basisFun ℤ S).ext fun v => ?_
        funext w
        have hpm : pm (Pi.basisFun ℤ S v) = Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩ :=
          (Pi.basisFun ℤ S).constr_basis ℤ _ v
        rw [LinearMap.comp_apply, hpm, LinearMap.smul_apply, LinearMap.id_apply, Pi.basisFun_apply,
          Pi.smul_apply, smul_eq_mul]
        change Multiplicative.toAdd (w.1.valuationOfNeZero (placeUnit v.1)) = _
        rw [valuationOfNeZero_placeUnit]
        by_cases h : w = v
        · subst h; simp
        · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
          simp [h, h']
      have hinj : Function.Injective (valuationVector S ∘ₗ pm) := by
        rw [hcomp]
        intro a b hab
        have hne : (-(classNumber K : ℤ)) ≠ 0 := by simpa using classNumber_ne_zero K
        exact smul_right_injective (S → ℤ) hne hab
      calc Nat.card S = finrank ℤ (S → ℤ) := by
            rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
        _ = finrank ℤ (LinearMap.range (valuationVector S ∘ₗ pm)) :=
            (LinearMap.finrank_range_of_inj hinj).symm
        _ ≤ finrank ℤ (LinearMap.range (valuationVector S)) :=
            Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hfr : finrank ℤ (Additive (S.unit K)) = Units.rank K + Nat.card S := by
    rw [← Submodule.finrank_quotient_add_finrank (LinearMap.ker (valuationVector S)),
      LinearEquiv.finrank_eq (valuationVector S).quotKerEquivRange, hrange,
      ← LinearEquiv.finrank_eq (unitsEquivKer S), Units.finrank_eq, add_comm]
  rw [← hfr]
  exact finrank_quotient_torsion_eq (M := Additive (S.unit K))

private theorem index_range_nsmul_free_int {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.IsTorsionFree ℤ M] (n : ℕ) :
    (nsmulAddMonoidHom n : M →+ M).range.index = n ^ finrank ℤ M := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  let ι := Module.Free.ChooseBasisIndex ℤ M
  have hcard : Fintype.card ι = finrank ℤ M := (Module.finrank_eq_card_chooseBasisIndex ℤ M).symm
  let e : M ≃+ (ι → ℤ) := b.equivFun.toAddEquiv
  have hmap : ((nsmulAddMonoidHom n : M →+ M).range).map e.toAddMonoidHom =
      (nsmulAddMonoidHom n : (ι → ℤ) →+ (ι → ℤ)).range := by
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨e x, by rw [AddEquiv.coe_toAddMonoidHom, map_nsmul]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨n • e.symm x, ⟨e.symm x, rfl⟩, by
        rw [AddEquiv.coe_toAddMonoidHom, map_nsmul, e.apply_symm_apply]⟩
  have hidx1 : (nsmulAddMonoidHom n : M →+ M).range.index =
      (nsmulAddMonoidHom n : (ι → ℤ) →+ (ι → ℤ)).range.index := by
    rw [← hmap]
    exact (AddSubgroup.index_map_equiv (nsmulAddMonoidHom n : M →+ M).range e).symm
  rw [hidx1, ← hcard]
  let f : (ι → ℤ) →+ (ι → ZMod n) :=
    { toFun := fun v i => (v i : ZMod n)
      map_zero' := by funext i; simp
      map_add' := fun u v => by funext i; simp }
  have hf_surj : Function.Surjective f := fun w =>
    ⟨fun i => (ZMod.intCast_surjective (w i)).choose, funext fun i =>
      (ZMod.intCast_surjective (w i)).choose_spec⟩
  have hf_ker : f.ker = (nsmulAddMonoidHom n : (ι → ℤ) →+ (ι → ℤ)).range := by
    ext v
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
      funext_iff, Pi.zero_apply]
    constructor
    · intro hv
      have hd : ∀ i, (n : ℤ) ∣ v i := fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd (v i) n).1 (hv i)
      exact ⟨fun i => (hd i).choose, fun i => by
        show n • (hd i).choose = v i
        rw [nsmul_eq_mul]; exact (hd i).choose_spec.symm⟩
    · rintro ⟨u, hu⟩ i
      show (v i : ZMod n) = 0
      rw [← hu i]
      show ((n • u i : ℤ) : ZMod n) = 0
      rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  rw [← hf_ker, AddSubgroup.index_eq_card]
  have eQ := QuotientAddGroup.quotientKerEquivOfSurjective f hf_surj
  rw [Nat.card_congr eQ.toEquiv, Nat.card_pi]
  simp [Nat.card_zmod]

theorem index_range_powMonoidHom_eq_pow_mul {G : Type*} [CommGroup G] [Group.FG G] {n : ℕ}
    (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ finrank ℤ (Additive (G ⧸ CommGroup.torsion G)) *
        (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range.index := by
  haveI : Module.Finite ℤ (Additive (G ⧸ CommGroup.torsion G)) := by
    rw [Module.Finite.iff_addGroup_fg, AddGroup.fg_iff_addMonoid_fg, ← Monoid.fg_iff_add_fg,
      ← Group.fg_iff_monoid_fg]
    infer_instance
  haveI : Module.IsTorsionFree ℤ (Additive (G ⧸ CommGroup.torsion G)) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c x hcx
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion G) x.toMul
      have h1 : (QuotientGroup.mk' (CommGroup.torsion G) g) ^ c = 1 := by
        have := congrArg Additive.toMul hcx
        simpa [hg] using this
      rw [← map_zpow] at h1
      have h1' : g ^ c ∈ CommGroup.torsion G := (QuotientGroup.eq_one_iff (g ^ c)).1 h1
      have hnat : g ^ c.natAbs ∈ CommGroup.torsion G := by
        rcases Int.natAbs_eq c with h | h
        · rw [h, zpow_natCast] at h1'; exact h1'
        · rw [h, zpow_neg, zpow_natCast] at h1'; exact (inv_mem_iff).1 h1'
      have hgT : g ∈ CommGroup.torsion G :=
        (isOfFinOrder_pow.1 hnat).resolve_right (Int.natAbs_ne_zero.2 hc)
      have hx1 : x.toMul = 1 := by rw [← hg]; exact (QuotientGroup.eq_one_iff g).2 hgT
      exact Additive.toMul.injective hx1
  set T := CommGroup.torsion G
  set N := (powMonoidHom n : G →* G).range
  have hQ : (powMonoidHom n : G ⧸ T →* G ⧸ T).range.index = n ^ finrank ℤ (Additive (G ⧸ T)) := by
    have h := index_range_nsmul_free_int (M := Additive (G ⧸ T)) n
    rw [Subgroup.index_eq_card, ← h, AddSubgroup.index_eq_card]
    let Qm := (G ⧸ T) ⧸ (powMonoidHom n : G ⧸ T →* G ⧸ T).range
    let Qa := Additive (G ⧸ T) ⧸ (nsmulAddMonoidHom n : Additive (G ⧸ T) →+ Additive (G ⧸ T)).range
    have hrel : ∀ a b : G ⧸ T,
        (QuotientGroup.mk a : Qm) = QuotientGroup.mk b ↔
        (QuotientAddGroup.mk (Additive.ofMul a) : Qa) = QuotientAddGroup.mk (Additive.ofMul b) := by
      intro a b
      rw [QuotientGroup.eq, QuotientAddGroup.eq]
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨Additive.ofMul c, congrArg Additive.ofMul hc⟩
      · rintro ⟨c, hc⟩
        exact ⟨Additive.toMul c, congrArg Additive.toMul hc⟩
    let toF : Qm → Qa := Quotient.lift (fun a : G ⧸ T => (QuotientAddGroup.mk (Additive.ofMul a) : Qa))
      fun a b hab => (hrel a b).1 (Quotient.sound hab)
    let invF : Qa → Qm := Quotient.lift (fun a : Additive (G ⧸ T) => (QuotientGroup.mk a.toMul : Qm))
      fun a b hab => (hrel a.toMul b.toMul).2 (Quotient.sound hab)
    refine Nat.card_congr
      { toFun := toF
        invFun := invF
        left_inv := fun q => Quotient.inductionOn q fun _ => rfl
        right_inv := fun q => Quotient.inductionOn q fun _ => rfl }
  have hsupEq : N ⊔ T =
      (powMonoidHom n : G ⧸ T →* G ⧸ T).range.comap (QuotientGroup.mk' T) := by
    ext x
    simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hx
      obtain ⟨_, ⟨b, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.1 hx
      refine ⟨QuotientGroup.mk' T b, ?_⟩
      have ht1 : QuotientGroup.mk' T t = 1 := (QuotientGroup.eq_one_iff t).2 ht
      rw [map_mul, ht1, mul_one, powMonoidHom_apply, map_pow]
    · rintro ⟨q, hq⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective T q
      have ht : (b ^ n)⁻¹ * x ∈ T := by
        rw [← QuotientGroup.eq]
        change QuotientGroup.mk' T (b ^ n) = QuotientGroup.mk' T x
        rw [map_pow]; exact hq
      have h := Subgroup.mul_mem_sup (S := N) (T := T) ⟨b, rfl⟩ ht
      rwa [powMonoidHom_apply, mul_inv_cancel_left] at h
  have hsup : (N ⊔ T).index = n ^ finrank ℤ (Additive (G ⧸ T)) := by
    rw [hsupEq, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective T), hQ]
  have hsubEq : N.subgroupOf T = (powMonoidHom n : T →* T).range := by
    ext ⟨t, ht⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      rw [powMonoidHom_apply] at hx
      have hxT : x ∈ T := (isOfFinOrder_pow.1 (hx ▸ ht)).resolve_right hn
      exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  have hrel : N.relIndex T = (powMonoidHom n : T →* T).range.index := by
    rw [Subgroup.relIndex, hsubEq]
  rw [← Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T), Subgroup.relIndex_sup_left, hrel,
    hsup, mul_comm]

end SUnitPowerIndex

end ExternalHelpers

/-! ## Section 2: Core Kummer & Class-Group Definitions + Basic Algebra (`Mk0IdMapCongr`, `ClMapBasic`, `ClSubUniv`, `ClProd`, `LenDirected`, `LenOfCard`, `QzBasic`, `ZmodToQZ`, `CardHomQZ`, `FunRepMem`, `RestrMem`, `PlaceDict`, `ToGalDict`, `XdualBase`, `CardSUnit`) -/

section CoreDefs

section Cl

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

def primeCl (v : HeightOneSpectrum (𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

def clSub (S : Set (HeightOneSpectrum (𝓞 K))) : Subgroup (ClassGroup (𝓞 K)) :=
  Subgroup.closure (primeCl '' S)

abbrev ClS (S : Set (HeightOneSpectrum (𝓞 K))) : Type := ClassGroup (𝓞 K) ⧸ clSub S

def idMap (τ : K ≃+* K') : (Ideal (𝓞 K))⁰ →* (Ideal (𝓞 K'))⁰ where
  toFun I := ⟨I.1.map (RingOfIntegers.mapRingEquiv τ), mem_nonZeroDivisors_of_ne_zero fun h =>
    nonZeroDivisors.ne_zero I.2
      ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv τ).injective).1 h)⟩
  map_one' := Subtype.ext (by simp [Ideal.map_top])
  map_mul' I J := Subtype.ext (Ideal.map_mul _ _ _)

theorem mk0_idMap_congr (τ : K ≃+* K') {I J : (Ideal (𝓞 K))⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (idMap τ I) = ClassGroup.mk0 (idMap τ J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, h⟩ := h
  refine ⟨RingOfIntegers.mapRingEquiv τ x, RingOfIntegers.mapRingEquiv τ y,
    by simpa using hx, by simpa using hy, ?_⟩
  have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv τ)) h
  rw [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton] at this
  exact this

private def clFun (τ : K ≃+* K') (c : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K') :=
  ClassGroup.mk0 (idMap τ (ClassGroup.mk0_surjective c).choose)

private theorem class_fun_mk0 (τ : K ≃+* K') (I : (Ideal (𝓞 K))⁰) :
    clFun τ (ClassGroup.mk0 I) = ClassGroup.mk0 (idMap τ I) :=
  mk0_idMap_congr τ (ClassGroup.mk0_surjective _).choose_spec

def clMap (τ : K ≃+* K') : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K') :=
  MonoidHom.mk' (clFun τ) fun a b => by
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective a
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective b
    rw [← map_mul, class_fun_mk0, class_fun_mk0, class_fun_mk0, map_mul, map_mul]

theorem class_map_mk0 (τ : K ≃+* K') (I : (Ideal (𝓞 K))⁰) :
    clMap τ (ClassGroup.mk0 I) = ClassGroup.mk0 (idMap τ I) :=
  class_fun_mk0 τ I

variable (K) in
def ClDual (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    Submodule R (ClassGroup (𝓞 K) → M) where
  carrier := {θ | (∀ a b, θ (a * b) = θ a + θ b) ∧ ∀ v ∈ Above K N, θ (primeCl v) = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨fun x y => by simp only [Pi.add_apply, ha.1, hb.1]; abel,
    fun v hv => by simp [ha.2 v hv, hb.2 v hv]⟩
  smul_mem' c a ha := ⟨fun x y => by simp [ha.1], fun v hv => by simp [ha.2 v hv]⟩

def ordv (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero a)

theorem ordv_mul (v : HeightOneSpectrum (𝓞 K)) (a b : Kˣ) :
    ordv v (a * b) = ordv v a + ordv v b := by
  simp [ordv, add_comm]

theorem ordv_one (v : HeightOneSpectrum (𝓞 K)) : ordv v (1 : Kˣ) = 0 := by simp [ordv]

theorem ordv_inv (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : ordv v a⁻¹ = -ordv v a := by simp [ordv]

def SelK (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) : Subgroup Kˣ where
  carrier := {a | ∀ v ∉ S, (n : ℤ) ∣ ordv v a}
  one_mem' v _ := by rw [ordv_one]; exact dvd_zero _
  mul_mem' {a b} ha hb v hv := by rw [ordv_mul]; exact dvd_add (ha v hv) (hb v hv)
  inv_mem' {a} ha v hv := by rw [ordv_inv]; exact (ha v hv).neg_right

variable (K) in
def powK (n : ℕ) : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range

def radCl (n : ℕ) (a : Kˣ) : ClassGroup (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ (ordv v a / n)

end Cl

section X

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def XDual (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type) [CommRing R] [AddCommGroup M]
    [Module R M] : Submodule R (U → M) where
  carrier := {φ | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
    (∀ (A : ValuationSubring Ω) (u : U), u.1 ∈ Ine (F := F) A → φ u = 0) ∧
    ∀ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 → ∀ u : U, u.1 ∈ Dec (F := F) A → φ u = 0}
  zero_mem' := ⟨IsLocallyConstant.const _, by simp, by simp, by simp⟩
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1,
    fun x y => by simp only [Pi.add_apply, ha.2.1, hb.2.1]; abel,
    fun A u h => by simp [ha.2.2.1 A u h, hb.2.2.1 A u h],
    fun A hA u h => by simp [ha.2.2.2 A hA u h, hb.2.2.2 A hA u h]⟩
  smul_mem' c a ha := ⟨ha.1.comp (c • ·), fun x y => by simp [ha.2.1],
    fun A u h => by simp [ha.2.2.1 A u h], fun A hA u h => by simp [ha.2.2.2 A hA u h]⟩

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def conjCond (U : Subgroup (G F Ω)) (σ : Ω ≃+* Ω) (T : M →ₗ[R] M) : Submodule R (U → M) where
  carrier := {φ | ∀ u u' : U, (∀ x, u'.1 (σ x) = σ (u.1 x)) → φ u' = T (φ u)}
  zero_mem' := by intro u u' _; simp
  add_mem' {a b} ha hb u u' h := by simp [ha u u' h, hb u u' h]
  smul_mem' c a ha u u' h := by simp [ha u u' h]

def EqHom (N : ℕ) (U : Subgroup (G F Ω)) (ρ : Representation R (G F Ω) M) :
    Submodule R (U → M) :=
  XDual N U R M ⊓ ⨅ g : G F Ω, conjCond U g.toRingEquiv (ρ g)

def EqEig (N : ℕ) (U : Subgroup (G F Ω)) (ρ : Representation R (G F Ω) M) (σ : Ω ≃+* Ω) (s : R) :
    Submodule R (U → M) :=
  EqHom N U ρ ⊓ conjCond U σ (s • LinearMap.id)

variable (R M) in
def restr {U V : Subgroup (G F Ω)} (h : U ≤ V) : (V → M) →ₗ[R] (U → M) :=
  LinearMap.funLeft R M (Subgroup.inclusion h)

variable (R M) in
def funRep (U : Subgroup (G F Ω)) [U.Normal] : Representation R (G F Ω) (U → M) where
  toFun g := LinearMap.funLeft R M (conjHom U g)
  map_one' := LinearMap.ext fun φ => funext fun u => congrArg φ (Subtype.ext (by simp [conjHom]))
  map_mul' g h := LinearMap.ext fun φ => funext fun u =>
    congrArg φ (Subtype.ext (by simp [conjHom, mul_assoc]))

def toGal (K : Type) [Field K] [Algebra K Ω] {U : Subgroup (G F Ω)} (hU : U ≤ galOf F K Ω) :
    U →* G K Ω where
  toFun u := AlgEquiv.ofRingEquiv (f := u.1.toRingEquiv) (hU u.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def clCond (K : Type) [Field K] [NumberField K] [Algebra K Ω] (σ : Ω ≃+* Ω) (T : M →ₗ[R] M) :
    Submodule R (ClassGroup (𝓞 K) → M) where
  carrier := {θ | ∀ τ : K ≃+* K, IsLift τ σ → ∀ c, θ (clMap τ c) = T (θ c)}
  zero_mem' := by intro τ _ c; simp
  add_mem' {a b} ha hb τ h c := by simp [ha τ h c, hb τ h c]
  smul_mem' r a ha τ h c := by simp [ha τ h c]

def ClEq (K : Type) [Field K] [NumberField K] [Algebra K Ω] (N : ℕ)
    (ρ : Representation R (G F Ω) M) : Submodule R (ClassGroup (𝓞 K) → M) :=
  ClDual K N R M ⊓ ⨅ g : G F Ω, clCond K g.toRingEquiv (ρ g)

def ClEig (K : Type) [Field K] [NumberField K] [Algebra K Ω] (N : ℕ)
    (ρ : Representation R (G F Ω) M) (σ : Ω ≃+* Ω) (s : R) :
    Submodule R (ClassGroup (𝓞 K) → M) :=
  ClEq K N ρ ⊓ clCond K σ (s • LinearMap.id)

def ClTw (K : Type) [Field K] [NumberField K] [Algebra K Ω] (n : ℕ)
    (η : G F Ω →* (ZMod n)ˣ) : Subgroup (ClassGroup (𝓞 K)) where
  carrier := {c | c ^ n = 1 ∧
    ∀ (g : G F Ω) (τ : K ≃+* K), IsLift τ g.toRingEquiv → clMap τ c = c ^ (η g : ZMod n).val}
  one_mem' := ⟨one_pow _, fun g τ _ => by simp⟩
  mul_mem' {a b} ha hb := ⟨by rw [mul_pow, ha.1, hb.1, one_mul], fun g τ h => by
    rw [map_mul, ha.2 g τ h, hb.2 g τ h, mul_pow]⟩
  inv_mem' {a} ha := ⟨by rw [inv_pow, ha.1, inv_one], fun g τ h => by
    rw [map_inv, ha.2 g τ h, inv_pow]⟩

def ClMinus {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) : Subgroup (ClassGroup (𝓞 K)) :=
  (clMap τ * MonoidHom.id _).ker

def IsRad {n : ℕ} (ζ : Ω) (U : Subgroup (G F Ω)) (φ : U → ZMod n) (β : Ω) : Prop :=
  β ≠ 0 ∧ ∀ u : U, u.1 β = ζ ^ (φ u).val * β

variable [IsAlgClosure F Ω]

instance isAlgClosure_sub (K : IntermediateField F Ω) : IsAlgClosure K Ω :=
  ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) K⟩

end X

section Tower

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]

abbrev Uinf : Subgroup (G F Ω) := cycU l ⊤

def Fn (n : ℕ) : IntermediateField F Ω :=
  IntermediateField.adjoin F ((Polynomial.X ^ l ^ n - 1 : Polynomial F).rootSet Ω)

instance isSplittingField_Fn (n : ℕ) :
    Polynomial.IsSplittingField F (Fn F Ω l n) (Polynomial.X ^ l ^ n - 1) :=
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance (n : ℕ) : FiniteDimensional F (Fn F Ω l n) :=
  Polynomial.IsSplittingField.finiteDimensional _ (Polynomial.X ^ l ^ n - 1)

instance (n : ℕ) : Normal F (Fn F Ω l n) := Normal.of_isSplittingField (Polynomial.X ^ l ^ n - 1)

instance (n : ℕ) : NumberField (Fn F Ω l n) := NumberField.of_module_finite F _

abbrev Un (n : ℕ) : Subgroup (G F Ω) := levU l ⊤ n

def cycR (r : ℕ) : G F Ω →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp (cycZ F Ω l)

def Procyc : Prop := l ≠ 2 ∨ ∀ g, cycR F Ω l 2 g = 1

variable {F Ω}

abbrev Dinf (N : ℕ) (U : Subgroup (G F Ω)) : Submodule ℤ_[l] (cycU l U → QZ l) :=
  XDual N (cycU l U) ℤ_[l] (QZ l)

abbrev Xinf (N : ℕ) (U : Subgroup (G F Ω)) : Type := Dinf l N U →ₗ[ℤ_[l]] QZ l

end Tower

def errTwo (l : ℕ) : ℕ∞ := if l = 2 then 1 else 0

section Res

instance instTopologicalSpaceZMod (n : ℕ) : TopologicalSpace (ZMod n) := ⊥

instance instDiscreteTopologyZMod (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

instance instIsTopologicalAddGroupZMod (n : ℕ) : IsTopologicalAddGroup (ZMod n) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def resTriv {R Γ M U : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R Γ M) (φ : U → Γ) (h : ∀ u m, ρ (φ u) m = m) :
    H1 ρ →ₗ[R] (U → M) :=
  Submodule.liftQ _ ((LinearMap.funLeft R M φ).comp (Z1 ρ).subtype) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_B1 ρ _).1 hz
    exact funext fun u => (hm (φ u)).trans (by rw [h, sub_self]; rfl)

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime]

def resInf (D : LData F Ω l) (e : ℤ) : H1 (qzTw D e) →ₗ[ℤ_[l]] (Uinf F Ω l → QZ l) :=
  resTriv (qzTw D e) (fun u => toGS Ω _ u.1) fun u m => by
    have h : D.chi (toGS Ω _ u.1) = 1 := (DFunLike.congr_fun D.hchi u.1).trans u.2.2
    rw [qzTw_apply, h, one_zpow, Units.val_one, one_smul]

theorem resInf_mk (D : LData F Ω l) (e : ℤ) (z : Z1 (qzTw D e)) (u : Uinf F Ω l) :
    resInf D e (Submodule.Quotient.mk z) u = z.1 (toGS Ω _ u.1) := rfl

def zmTw (D : LData F Ω l) (r : ℕ) (e : ℤ) :
    Representation (ZMod (l ^ r)) (GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (ZMod (l ^ r)) :=
  scalRep (ZMod (l ^ r))
    (((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp D.chi) ^ (-e))

def ShaZm (D : LData F Ω l) (r : ℕ) (e : ℤ) : Submodule (ZMod (l ^ r)) (H1 (zmTw D r e)) :=
  Sha1 (zmTw D r e) (locFam D.S D.A) (continuous_locFam D.S D.A)

def resZm (D : LData F Ω l) (r : ℕ) : H1 (zmTw D r 0) →ₗ[ZMod (l ^ r)] (G F Ω → ZMod (l ^ r)) :=
  resTriv (zmTw D r 0) (toGS Ω _) fun _ _ => by simp [zmTw]

end Res

end CoreDefs

section BasicAlgebra

private theorem clMapBasic_mem {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    (τ : K ≃+* K') (I : Ideal (𝓞 K)) (y : 𝓞 K') :
    y ∈ I.map (RingOfIntegers.mapRingEquiv τ) ↔ ∃ x ∈ I, RingOfIntegers.mapRingEquiv τ x = y :=
  Ideal.mem_map_iff_of_surjective _ (RingOfIntegers.mapRingEquiv τ).surjective

private theorem clMap_trans_apply {K K' K'' : Type} [Field K] [NumberField K] [Field K']
    [NumberField K'] [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K'')
    (c : ClassGroup (𝓞 K)) : clMap (τ.trans τ') c = clMap τ' (clMap τ c) := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0, class_map_mk0, class_map_mk0]
  congr 1; apply Subtype.ext
  show Ideal.map _ _ = Ideal.map _ (Ideal.map _ _)
  ext y; rw [clMapBasic_mem, clMapBasic_mem]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv τ x, (clMapBasic_mem τ _ _).2 ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (clMapBasic_mem τ _ _).1 hz
    exact ⟨x, hx, rfl⟩

private theorem clMap_refl_apply {K : Type} [Field K] [NumberField K] (c : ClassGroup (𝓞 K)) :
    clMap (RingEquiv.refl K) c = c := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [class_map_mk0]; congr 1; apply Subtype.ext
  show Ideal.map _ _ = _
  ext y; rw [clMapBasic_mem]
  exact ⟨fun ⟨x, hx, h⟩ => h ▸ hx, fun hy => ⟨y, hy, rfl⟩⟩

theorem clMapBasic (K K' K'' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field K''] [NumberField K''] (τ : K ≃+* K') (τ' : K' ≃+* K'') :
    (∀ c, clMap (RingEquiv.refl K) c = c) ∧ (∀ c, clMap (τ.trans τ') c = clMap τ' (clMap τ c)) ∧
    Function.Bijective (clMap τ) ∧
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K')),
      (∀ x, x ∈ v.asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ w.asIdeal) →
      clMap τ (primeCl v) = primeCl w := by
  refine ⟨clMap_refl_apply, clMap_trans_apply τ τ', ?_, ?_⟩
  · have hl : Function.LeftInverse (clMap τ.symm) (clMap τ) := fun c => by
      rw [← clMap_trans_apply, RingEquiv.self_trans_symm, clMap_refl_apply]
    have hr : Function.RightInverse (clMap τ.symm) (clMap τ) := fun c => by
      rw [← clMap_trans_apply, RingEquiv.symm_trans_self, clMap_refl_apply]
    exact ⟨hl.injective, hr.surjective⟩
  · intro v w hvw
    unfold primeCl; rw [class_map_mk0]; congr 1; apply Subtype.ext
    show Ideal.map _ _ = _
    ext y; rw [clMapBasic_mem]
    refine ⟨fun ⟨x, hx, h⟩ => h ▸ (hvw x).1 hx, fun hy => ⟨(RingOfIntegers.mapRingEquiv τ).symm y,
      (hvw _).2 (by simpa using hy), RingEquiv.apply_symm_apply _ y⟩⟩

theorem clSubUniv (K : Type) [Field K] [NumberField K] :
    clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) = ⊤ := by
  classical
  have key : ∀ I : Ideal (𝓞 K), ∀ hI : I ∈ nonZeroDivisors (Ideal (𝓞 K)),
      ClassGroup.mk0 ⟨I, hI⟩ ∈ clSub (Set.univ : Set (HeightOneSpectrum (𝓞 K))) := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro hI; exact absurd hI zero_notMem_nonZeroDivisors
    | h₂ u hu =>
      intro hI
      have hu' : u = ⊤ := Ideal.isUnit_iff.mp hu
      subst hu'
      rw [show (⟨⊤, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = 1 from Subtype.ext Ideal.one_eq_top.symm,
        map_one]
      exact Subgroup.one_mem _
    | h₃ a p ha hp ih =>
      intro hI
      have ha' : a ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero ha
      have hp' : p ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
      have hsplit : (⟨p * a, hI⟩ : nonZeroDivisors (Ideal (𝓞 K))) = ⟨p, hp'⟩ * ⟨a, ha'⟩ := rfl
      rw [hsplit, map_mul]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩,
        Set.mem_univ _, rfl⟩) (ih ha')
  rw [eq_top_iff]
  intro c _
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
  exact key I hI

private theorem mk_eq_finprod (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1 := by
  let P : HeightOneSpectrum (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun v =>
    FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have hfin : (Function.mulSupport fun v => P v ^ FractionalIdeal.count K v I.1).Finite :=
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I.1)).subset
      fun v hv h => hv (by simp only [h, zpow_zero])
  have hI : ∏ᶠ v, P v ^ FractionalIdeal.count K v I.1 = I := by
    apply Units.ext
    rw [← Units.coeHom_apply, map_finprod _ hfin]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
    exact finprod_congr fun v => by simp [Units.val_zpow_eq_zpow_val, P]
  conv_lhs => rw [← hI]
  rw [map_finprod _ hfin]
  exact finprod_congr fun v => by rw [map_zpow, ClassGroup.mk_mk0]; rfl

private theorem count_eq_ordv (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) =
      ordv v a := by
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
        (algebraMap (𝓞 K) K (IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).2)⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).1} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsLocalization.sec_spec' (nonZeroDivisors (𝓞 K)) (a : K), inv_mul_cancel_left₀]
    simp [nonZeroDivisors.coe_ne_zero]
  rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero) hI]
  change _ = -Multiplicative.toAdd (v.valuationOfNeZeroToFun a)
  simp only [HeightOneSpectrum.valuationOfNeZeroToFun, toAdd_ofAdd]
  ring

theorem clProd (K : Type) [Field K] [NumberField K] :
    (∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ,
      ClassGroup.mk K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ FractionalIdeal.count K v I.1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ),
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) =
        ordv v a) ∧
    (∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ordv v a ≠ 0}.Finite) ∧
    ∀ a : Kˣ, radCl 1 a = 1 := by
  refine ⟨mk_eq_finprod K, count_eq_ordv K, fun a => ?_, fun a => ?_⟩
  · simp only [← count_eq_ordv]
    exact Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  · have h := mk_eq_finprod K (toPrincipalIdeal (𝓞 K) K a)
    rw [coe_toPrincipalIdeal] at h
    simp only [count_eq_ordv] at h
    simp only [radCl, Nat.cast_one, Int.ediv_one]
    rw [← h, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal]
    exact (FractionalIdeal.isPrincipal_iff _).2 ⟨_, rfl⟩

theorem lenDirected (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (W : Submodule R X)
    (P : ℕ → Submodule R X) (Bd : ℕ∞) (hP : Monotone P) (hW : W ≤ ⨆ n, P n)
    (hBd : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) : Module.length R W ≤ Bd := by
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim, iSup_le_iff]
  intro p
  have hstep : ∀ i : Fin p.length, ∃ x : W, x ∈ p i.succ ∧ x ∉ p i.castSucc := fun i =>
    SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hstep
  have hmem : ∀ i : Fin p.length, ∃ n, (x i : X) ∈ P n := fun i =>
    (Submodule.mem_iSup_of_directed P hP.directed_le).mp (hW (x i).2)
  choose m hm using hmem
  obtain ⟨n, hn, hlen⟩ := hBd (Finset.univ.sup m)
  have hxn : ∀ i : Fin p.length, (x i : X) ∈ P n := fun i =>
    hP ((Finset.le_sup (Finset.mem_univ i)).trans hn) (hm i)
  let f : Submodule R W → Submodule R (P n) := fun S => (S.map W.subtype).comap (P n).subtype
  let q : LTSeries (Submodule R (P n)) :=
    { length := p.length
      toFun := fun i => f (p i)
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (Submodule.map_mono (p.step i).le)) fun heq => ?_
        have h1 : (⟨(x i : X), hxn i⟩ : P n) ∈ f (p i.succ) := ⟨x i, hx1 i, rfl⟩
        change (⟨(x i : X), hxn i⟩ : P n) ∈
          Submodule.comap (P n).subtype (Submodule.map W.subtype (p i.succ)) at h1
        rw [← heq] at h1
        obtain ⟨y, hy, hyx⟩ := h1
        exact hx2 i ((Subtype.ext hyx : y = x i) ▸ hy) }
  have hq := Order.LTSeries.length_le_krullDim q
  rw [← Module.coe_length] at hq
  exact hq.trans (WithBot.coe_le_coe.mpr hlen)

private theorem card_simple_padicInt (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M]
    [Module ℤ_[l] M] [h : IsSimpleModule ℤ_[l] M] : Nat.card M = l := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  have hIm : I = IsLocalRing.maximalIdeal ℤ_[l] := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  rw [Nat.card_congr e.toEquiv]
  have f := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := l)))
  have g := Ideal.quotEquivOfEq (PadicInt.ker_toZMod (p := l))
  rw [← Nat.card_congr g.toEquiv, Nat.card_congr f.toEquiv, Nat.card_zmod]

private theorem lenOfCard_aux (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | of_subsingleton =>
    exact ⟨0, by rw [Module.length_eq_zero]; rfl, by rw [Nat.card_of_subsingleton (0 : _)]; simp⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
        (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      have h1 : Nat.card (M ⧸ N.toAddSubgroup) = l := card_simple_padicInt l (M ⧸ N)
      have h2 : Nat.card N.toAddSubgroup = l ^ k := hc
      rw [h1, h2, pow_succ, mul_comm]

theorem lenOfCard (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k :=
  lenOfCard_aux l M (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩)

theorem qzBasic (l : ℕ) [Fact l.Prime] :
    (∀ u : ℤ_[l], u ≠ 0 → Function.Surjective fun x : QZ l => u • x) ∧
    (∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0) ∧ (l ≠ 2 → ∀ x : QZ l, 2 • x = 0 → x = 0) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ : ∃ q, QZ.mk l q = x := Submodule.Quotient.mk_surjective (ZlSub l) x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hl1
    refine ⟨k, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    refine (Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨⟨_, ?_⟩, rfl⟩
    have hpos : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (by linarith) k
    change ‖((l ^ k : ℕ) : ℚ_[l]) * q‖ ≤ 1
    push_cast
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le
  refine ⟨?_, tors, ?_⟩
  · intro u hu a
    obtain ⟨q, rfl⟩ : ∃ q, QZ.mk l q = a := Submodule.Quotient.mk_surjective (ZlSub l) a
    have hu' : (u : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 hu
    refine ⟨QZ.mk l (q / u), ?_⟩
    show QZ.mk l ((u : ℚ_[l]) * (q / u)) = QZ.mk l q
    rw [mul_div_cancel₀ q hu']
  · intro h2 x hx
    obtain ⟨k, hk⟩ := tors x
    have hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))
    obtain ⟨a, b, hab⟩ := hc
    calc x = (1 : ℤ) • x := (one_smul ℤ x).symm
      _ = (a * 2 + b * ((l ^ k : ℕ) : ℤ)) • x := by rw [hab]
      _ = a • ((2 : ℕ) • x) + b • ((l ^ k) • x) := by
        rw [add_smul, mul_smul, mul_smul]; norm_cast
      _ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]

theorem zmodToQZ (l : ℕ) [Fact l.Prime] (r : ℕ) :
    ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧
      (∀ x, x ∈ Set.range ι ↔ (l : ℤ_[l]) ^ r • x = 0) ∧
      ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
  have hl : l.Prime := Fact.out
  have hlr0 : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  have zsm : ∀ (k : ℤ) (q : ℚ_[l]), k • QZ.mk l q = QZ.mk l ((k : ℚ_[l]) * q) := by
    intro k q
    rw [← Int.cast_smul_eq_zsmul ℤ_[l]]
    show QZ.mk l (((k : ℤ_[l]) : ℚ_[l]) * q) = _
    rw [PadicInt.coe_intCast]
  have hker : ((l ^ r : ℕ) : ℤ) • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 := by
    rw [zsm]
    refine (Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨1, ?_⟩
    push_cast; exact (mul_inv_cancel₀ hlr0).symm
  let ι : ZMod (l ^ r) →+ QZ l :=
    ZMod.lift (l ^ r) ⟨zmultiplesHom (QZ l) (QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹)), by
      rw [zmultiplesHom_apply]; exact hker⟩
  have hι : ∀ k : ℤ, ι (k : ZMod (l ^ r)) = QZ.mk l ((k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹) :=
    fun k => by simp only [ι, ZMod.lift_coe, zmultiplesHom_apply]; exact zsm k _
  have hkill : ∀ a : ZMod (l ^ r), (l ^ r : ℕ) • ι a = 0 := fun a => by
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  have h3 : ∀ (z : ℤ_[l]) (a : ZMod (l ^ r)), ι (PadicInt.toZModPow r z * a) = z • ι a := by
    intro z a
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec r z)
    have hz : PadicInt.toZModPow r z = ((z.appr r : ℕ) : ZMod (l ^ r)) := rfl
    rw [hz, ← nsmul_eq_mul, map_nsmul]
    have hzw : z = ((z.appr r : ℕ) : ℤ_[l]) + w * ((l ^ r : ℕ) : ℤ_[l]) := by
      push_cast; rw [hw]; ring
    conv_rhs => rw [hzw]
    rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul, hkill, smul_zero,
      add_zero]
  refine ⟨ι, ?_, ?_, h3⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [hι] at ha
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 ha
    have hy' : (y : ℚ_[l]) = (k : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹ := hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hky : (k : ℤ_[l]) = y * (l : ℤ_[l]) ^ r := by
      apply PadicInt.ext; push_cast; rw [hy', mul_assoc, inv_mul_cancel₀ hlr0, mul_one]
    have hn : ‖(k : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
      rw [hky, norm_mul, PadicInt.norm_p_pow]
      exact mul_le_of_le_one_left (by positivity) (PadicInt.norm_le_one y)
    exact_mod_cast PadicInt.norm_int_le_pow_iff_dvd.1 hn
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      have h := h3 ((l : ℤ_[l]) ^ r) a
      rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul, map_zero] at h
      exact h.symm
    · intro hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) x
      have hx' : QZ.mk l ((((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q) = 0 := hx
      obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 hx'
      have hz' : (z : ℚ_[l]) = (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * q := hz
      push_cast at hz'
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      rw [← mul_one (PadicInt.toZModPow r z), h3,
        show (1 : ZMod (l ^ r)) = ((1 : ℤ) : ZMod (l ^ r)) by simp, hι]
      show QZ.mk l ((z : ℚ_[l]) * (((1 : ℤ) : ℚ_[l]) * ((l : ℚ_[l]) ^ r)⁻¹)) =
        Submodule.Quotient.mk q
      congr 1; rw [hz']; push_cast; field_simp

private theorem cardTors_QZ (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : n ≠ 0) :
    Nat.card {x : QZ l // (n : ℤ) • x = 0} = l ^ n.factorization l := by
  have hl : l.Prime := Fact.out
  obtain ⟨ι, hι, hr, -⟩ := zmodToQZ l (n.factorization l)
  have hcop : ¬ l ∣ n / l ^ n.factorization l := Nat.not_dvd_ordCompl hl hn
  have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hcop
  have key : ∀ x : QZ l, (n : ℤ) • x = 0 ↔ x ∈ Set.range ι := fun x => by
    rw [hr, natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℤ_[l]]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l, mul_comm, Nat.cast_mul, mul_smul]
    rw [hu.smul_eq_zero, Nat.cast_pow]
  rw [Nat.card_congr (Equiv.subtypeEquivRight key)]
  exact (Nat.card_range_of_injective hι).trans (Nat.card_zmod _)

private theorem cardZmod_QZ (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : n ≠ 0) :
    Nat.card (ZMod n →+ QZ l) = l ^ n.factorization l := by
  rw [← cardTors_QZ l n hn, ← Nat.card_congr (ZMod.lift n)]
  exact (Nat.card_congr ((zmultiplesHom (QZ l)).subtypeEquiv fun _ => by simp)).symm

theorem cardHomQZ (l : ℕ) [Fact l.Prime] (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ QZ l) = l ^ (Nat.card A).factorization l := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
  have hn0 : ∀ i, n i ≠ 0 := fun i => by have := hn i; omega
  have h1 : Nat.card A = ∏ i, n i := by
    rw [Nat.card_congr (e.toEquiv.trans DFinsupp.equivFunOnFintype), Nat.card_pi]; simp
  have e2 : (A →+ QZ l) ≃ (∀ i, ZMod (n i) →+ QZ l) :=
    (AddEquiv.addMonoidHomCongrLeftEquiv e).trans (DFinsupp.liftAddHom).toEquiv.symm
  rw [Nat.card_congr e2, Nat.card_pi, h1, Nat.factorization_prod fun i _ => hn0 i,
    Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => cardZmod_QZ l _ (hn0 i)

theorem funRepMem (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal] (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] :
    (∀ g, ∀ φ ∈ XDual N U R M, funRep R M U g φ ∈ XDual N U R M) ∧
    (∀ g ∈ U, ∀ φ ∈ XDual N U R M, funRep R M U g φ = φ) ∧
    ∀ (ρ : Representation R (G F Ω) M) (φ : U → M),
      φ ∈ EqHom N U ρ ↔ φ ∈ XDual N U R M ∧ ∀ g u, ρ g (funRep R M U g φ u) = φ u := by
  have hf : ∀ (g : G F Ω) (φ : U → M) (u : U), funRep R M U g φ u = φ (conjHom U g u) :=
    fun _ _ _ => rfl
  have hc : ∀ (g : G F Ω) (u : U), (conjHom U g u).1 = g⁻¹ * u.1 * g := fun _ _ => rfl
  refine ⟨fun g φ hφ => ?_, fun g hg φ hφ => ?_, fun ρ φ => ?_⟩
  · have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
    have e1 : ∀ x : G F Ω, conjGal h x = g⁻¹ * x * g := fun _ => rfl
    have hA : ∀ (A : ValuationSubring Ω) x, g.toRingEquiv x ∈ A ↔
        x ∈ A.comap g.toRingEquiv.toRingHom := fun _ _ => Iff.rfl
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (continuous_conjHom U g), fun a b => ?_, fun A u hu => ?_,
      fun A hN u hu => ?_⟩
    · rw [hf, hf, hf, map_mul, h2]
    · rw [hf]
      refine h3 (A.comap g.toRingEquiv.toRingHom) _ ?_
      rw [hc, ← e1]; exact conjGal_mem_Ine h (hA A) hu
    · rw [hf]
      refine h4 (A.comap g.toRingEquiv.toRingHom) ?_ _ ?_
      · rw [comap_valuation_lt_one_iff_self A g.toRingEquiv, map_natCast]
        exact hN
      · rw [hc, ← e1]; exact conjGal_mem_Dec h (hA A) hu
  · funext u
    have e : (⟨g, hg⟩ : U) * conjHom U g u = u * ⟨g, hg⟩ := Subtype.ext (by simp [hc, mul_assoc])
    have e2 := congrArg φ e
    rw [hφ.2.1, hφ.2.1, add_comm] at e2
    rw [hf]; exact add_right_cancel e2
  · unfold EqHom
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    refine and_congr_right fun _ => forall_congr' fun g => ⟨fun h u => ?_, fun h u u' hu => ?_⟩
    · rw [hf]
      refine (h _ u fun x => ?_).symm
      show u.1 (g x) = g (g.symm (u.1 (g x)))
      rw [g.apply_symm_apply]
    · have e : conjHom U g u' = u := Subtype.ext (AlgEquiv.ext fun x => by
        show g.symm (u'.1 (g x)) = u.1 x
        exact g.symm_apply_eq.2 (hu x))
      rw [← h u', hf, e]
where
  comap_valuation_lt_one_iff_self (A : ValuationSubring Ω) (σ : Ω ≃+* Ω) (x : Ω) :
      (A.comap σ.toRingHom).valuation x < 1 ↔ A.valuation (σ x) < 1 := by
    rw [valuation_lt_one_iff', valuation_lt_one_iff']
    simp [ValuationSubring.mem_comap, map_inv₀]

theorem restrMem (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (N : ℕ) (U V : Subgroup (G F Ω)) (h : U ≤ V) (R M : Type) [CommRing R] [AddCommGroup M]
    [Module R M] (ρ : Representation R (G F Ω) M) :
    (XDual N V R M).map (restr R M h) ≤ XDual N U R M ∧
    (EqHom N V ρ).map (restr R M h) ≤ EqHom N U ρ ∧
    ∀ (σ : Ω ≃+* Ω) (s : R), (EqEig N V ρ σ s).map (restr R M h) ≤ EqEig N U ρ σ s := by
  have hX : ∀ φ ∈ XDual N V R M, restr R M h φ ∈ XDual N U R M := fun φ ⟨h1, h2, h3, h4⟩ =>
    ⟨h1.comp_continuous (continuous_inclusion h), fun a b => h2 (Subgroup.inclusion h a) (Subgroup.inclusion h b),
      fun A u hu => h3 A (Subgroup.inclusion h u) hu,
      fun A hA u hu => h4 A hA (Subgroup.inclusion h u) hu⟩
  have hC : ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), ∀ φ ∈ conjCond V σ T,
      restr R M h φ ∈ conjCond U σ T := fun _ _ _ hφ u u' hu => hφ _ _ hu
  have hE : ∀ φ ∈ EqHom N V ρ, restr R M h φ ∈ EqHom N U ρ := fun φ hφ => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    exact Submodule.mem_inf.2 ⟨hX φ h1, (Submodule.mem_iInf _).2 fun g =>
      hC _ _ φ ((Submodule.mem_iInf _).1 h2 g)⟩
  refine ⟨?_, ?_, fun σ s => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩; exact hX φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩; exact hE φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    exact Submodule.mem_inf.2 ⟨hE φ h1, hC _ _ φ h2⟩

private theorem val_top_eq_zero {Ω : Type} [Field Ω] {x : Ω}
    (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
  by_contra hx
  have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
  have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
  rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
  exact lt_irrefl _ h2

private theorem int_le_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω}
    (hb : IsIntegral ℤ b) : A.valuation b ≤ 1 := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place_of_ne_top (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (A : ValuationSubring Ω) (hA : A ≠ ⊤) :
    ∃ v : HeightOneSpectrum (𝓞 K),
      ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
  have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
    (A.valuation_le_one_iff _).1 (int_le_val A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
  rw [eq_top_iff]
  intro x _
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have h1 : Algebra.IsAlgebraic ℤ K :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
  have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
  obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
  have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
    rw [hP, h0, Ideal.mem_bot]; exact Int.cast_ne_zero.2 hn
  have h4 : A.valuation (n : Ω) = 1 :=
    le_antisymm (int_le_val A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
  have h5 := int_le_val A hi
  rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
  exact (A.valuation_le_one_iff x).1 h5

theorem placeDict (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] :
    Ine (F := K) (⊤ : ValuationSubring Ω) = ⊥ ∧
    (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v) ∧
    (∀ (A : ValuationSubring Ω) (N : ℕ), N ≠ 0 → A.valuation (N : Ω) < 1 → A ≠ ⊤) ∧
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (N : ℕ),
      IsPlaceOver A v → (A.valuation (N : Ω) < 1 ↔ v ∈ Above K N) := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  refine ⟨?_, fun A hA => exists_place_of_ne_top K Ω A hA, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    exact sub_eq_zero.1 (val_top_eq_zero (hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2
      (ValuationSubring.mem_top _))))
  · rintro A N hN h rfl
    exact hN (Nat.cast_eq_zero.1 (val_top_eq_zero h))
  · intro A v N hv
    have h := hv (N : 𝓞 K)
    have e : algebraMap K Ω ((N : 𝓞 K) : K) = (N : Ω) := by simp
    rw [← e]; exact h

theorem toGalDict (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω) :
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A) ∧
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Ine (F := K) A ↔ u.1 ∈ Ine (F := F) A) ∧
    Continuous (toGal K hU) ∧
    (galOf F K Ω ≤ U → IsHomeomorph (toGal K hU) ∧ IsOpen (U : Set (G F Ω))) := by
  obtain ⟨hE, hO, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (u : U),
      toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A := fun A u => by
    rw [mem_Dec, mem_Dec]
    have e : toGal K hU u • A = u.1 • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    rw [e]
  have hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val := funext fun _ => AlgEquiv.ext fun _ => rfl
  have hc : Continuous (toGal K hU) := by
    rw [hE.isInducing.continuous_iff, hcomp]
    exact continuous_subtype_val
  refine ⟨hD, fun A u => ⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩, hc,
    fun h => ⟨?_, le_antisymm hU h ▸ hO⟩⟩
  rw [isHomeomorph_iff_exists_inverse]
  exact ⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩,
    fun _ => Subtype.ext (AlgEquiv.ext fun _ => rfl),
    fun _ => AlgEquiv.ext fun _ => rfl, hE.continuous.subtype_mk _⟩

theorem xdualBase (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (E : Type) [Field E] [NumberField E] [Algebra F E] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type)
    [CommRing R] [AddCommGroup M] [Module R M] (hU : U ≤ galOf F E Ω) :
    (∃ ε : (U → M) ≃ₗ[R] (U.comap (galEmb F E Ω) → M),
      (∀ φ u, ε φ u = φ ⟨galEmb F E Ω u.1, u.2⟩) ∧
      (XDual N U R M).map ε.toLinearMap = XDual N (U.comap (galEmb F E Ω)) R M ∧
      ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M),
        (conjCond U σ T).map ε.toLinearMap = conjCond (U.comap (galEmb F E Ω)) σ T) ∧
    ∀ (l : ℕ) [Fact l.Prime],
      (cycU l (galOf F E Ω)).comap (galEmb F E Ω) = Uinf E Ω l ∧
      ∀ n, (levU l (galOf F E Ω) n).comap (galEmb F E Ω) = Un E Ω l n := by
  obtain ⟨hD, hI, hc, -⟩ := toGalDict F Ω E U hU
  obtain ⟨hE, -, -⟩ := galEmbTop F E Ω
  let e : U.comap (galEmb F E Ω) ≃ U :=
    { toFun := fun u => ⟨galEmb F E Ω u.1, u.2⟩
      invFun := fun u => ⟨toGal E hU u, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hec : Continuous e := (hE.continuous.comp continuous_subtype_val).subtype_mk _
  have hes : Continuous e.symm := hc.subtype_mk _
  refine ⟨⟨LinearEquiv.funCongrLeft R M e, fun _ _ => rfl, ?_, fun σ T => ?_⟩, fun l _ => ?_⟩
  · ext ψ
    constructor
    · rintro ⟨φ, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨h1.comp_continuous hec, fun a b => h2 (e a) (e b),
        fun A u hu => h3 A (e u) ((hI A (e u)).1 hu),
        fun A hA u hu => h4 A hA (e u) ((hD A (e u)).1 hu)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨ψ ∘ e.symm, ⟨h1.comp_continuous hes, fun a b => h2 (e.symm a) (e.symm b),
        fun A u hu => h3 A (e.symm u) ((hI A u).2 hu),
        fun A hA u hu => h4 A hA (e.symm u) ((hD A u).2 hu)⟩, rfl⟩
  · ext ψ
    exact ⟨fun ⟨φ, h, hp⟩ => hp ▸ fun u u' huu => h (e u) (e u') huu,
      fun h => ⟨ψ ∘ e.symm, fun u u' huu => h (e.symm u) (e.symm u') huu, rfl⟩⟩
  · have hz : ∀ g, cycZ F Ω l (galEmb F E Ω g) = cycZ E Ω l g := fun _ => rfl
    refine ⟨?_, fun n => ?_⟩
    · ext g
      exact ⟨fun h => ⟨trivial, (hz g).symm.trans h.2⟩,
        fun h => ⟨galEmb_mem F E Ω g, (hz g).trans h.2⟩⟩
    · ext g
      exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨galEmb_mem F E Ω g, h.2⟩⟩

private theorem index_range_eq_card_ker {T : Type*} [CommGroup T] [Finite T] (f : T →* T) :
    f.range.index = Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.range
  have h2 := Subgroup.card_mul_index f.ker
  have hk : f.ker.index = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hk] at h2
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (by rw [h1, ← h2, mul_comm])

private theorem powK_subgroupOf_sUnit {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) {p : ℕ} (hp : p ≠ 0) :
    (powK K p).subgroupOf (S.unit K) = (powMonoidHom p : S.unit K →* S.unit K).range := by
  ext x
  rw [Subgroup.mem_subgroupOf, powK, MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    rw [powMonoidHom_apply] at hb
    have hbS : b ∈ S.unit K := fun v hv => by
      have h := (hb ▸ x.2) v hv
      rw [Units.val_pow_eq_pow_val, map_pow] at h
      simpa [hp] using h
    exact ⟨⟨b, hbS⟩, Subtype.ext (by simpa using hb)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.1, by rw [← hc]; simp⟩

theorem cardSUnit (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) [NeZero n] (hS : S.Finite) :
    Nat.card (S.unit K ⧸ (powK K n).subgroupOf (S.unit K)) =
      n ^ (InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K - 1 + Nat.card S) *
        Nat.card (rootsOfUnity n K) := by
  haveI : Finite S := hS
  haveI : Group.FG (S.unit K) := sUnit_fg S
  haveI : Finite (CommGroup.torsion (S.unit K)) := sUnit_finite_torsion S
  have hker : Nat.card (powMonoidHom n : CommGroup.torsion (S.unit K) →*
      CommGroup.torsion (S.unit K)).ker = Nat.card (rootsOfUnity n K) := by
    have hfin : ∀ ζ : rootsOfUnity n K, IsOfFinOrder (ζ : Kˣ) := fun ζ =>
      isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, (mem_rootsOfUnity _ _).mp ζ.2⟩
    have hSu : ∀ ζ : rootsOfUnity n K, (ζ : Kˣ) ∈ S.unit K := fun ζ v _ =>
      valuation_eq_one_of_isOfFinOrder (hfin ζ) v
    refine Nat.card_congr
      { toFun := fun t => ⟨t.1.1.1, (mem_rootsOfUnity _ _).mpr (by
          have h := congrArg (fun y : CommGroup.torsion (S.unit K) => ((y : S.unit K) : Kˣ))
            (MonoidHom.mem_ker.mp t.2)
          simpa using h)⟩
        invFun := fun ζ => ⟨⟨⟨ζ.1, hSu ζ⟩, (CommGroup.mem_torsion _).mpr
            (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, NeZero.pos n, Subtype.ext (by
              simpa using (mem_rootsOfUnity _ _).mp ζ.2)⟩)⟩,
          MonoidHom.mem_ker.mpr (Subtype.ext (Subtype.ext (by
              simpa using (mem_rootsOfUnity _ _).mp ζ.2)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← Subgroup.index_eq_card, powK_subgroupOf_sUnit S (NeZero.ne n),
    index_range_powMonoidHom_eq_pow_mul (NeZero.ne n), sUnit_finrank_quotient_torsion,
    index_range_eq_card_ker, hker, Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

end BasicAlgebra

/-! ## Section 3: Radical Maps, Selmer Cardinality, `FinChar`, and Kummer Reflection (`RadCl*`, `CardSel`, `RadExists`, `DvdOfIne`, `FinChar`, `RadConj`, `RadXDual`, `Refl*`, `UnitMinus`, `Reflect`) -/

section RadicalAndReflection

private theorem intValuation_mapRingEquiv {K K' : Type} [Field K] [NumberField K] [Field K']
    [NumberField K'] (τ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v).intValuation
      (RingOfIntegers.mapRingEquiv τ x) = v.intValuation x := by
  set ρ := RingOfIntegers.mapRingEquiv τ
  have hw : (HeightOneSpectrum.equivOfRingEquiv ρ v).asIdeal = Ideal.map ρ v.asIdeal := by
    ext y
    rw [Ideal.mem_map_of_equiv]
    show ρ.symm y ∈ v.asIdeal ↔ _
    exact ⟨fun h => ⟨_, h, ρ.apply_symm_apply y⟩, fun ⟨z, hz, hzy⟩ => by rwa [← hzy, ρ.symm_apply_apply]⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hx' : ρ x ≠ 0 := (map_ne_zero_iff ρ ρ.injective).mpr hx
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx']
  have hm : multiplicity (HeightOneSpectrum.equivOfRingEquiv ρ v).asIdeal (Ideal.span {ρ x}) =
      multiplicity v.asIdeal (Ideal.span {x}) := by
    apply multiplicity_eq_of_emultiplicity_eq
    rw [emultiplicity_eq_emultiplicity_iff]
    intro k
    have hs : Ideal.span {ρ x} = Ideal.map ρ (Ideal.span {x}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, hw, hs, ← Ideal.map_pow]
    refine ⟨fun h => ?_, Ideal.map_mono⟩
    have h2 := Ideal.comap_mono (f := ρ) h
    rwa [Ideal.comap_map_of_bijective _ ρ.bijective, Ideal.comap_map_of_bijective _ ρ.bijective] at h2
  rw [hm]

private theorem ordv_units_map_ringEquiv {K K' : Type} [Field K] [NumberField K] [Field K']
    [NumberField K'] (τ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ordv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v)
      (Units.map τ.toMonoidHom a) = ordv v a := by
  have hτ : ∀ z : 𝓞 K, τ (algebraMap (𝓞 K) K z) =
      algebraMap (𝓞 K') K' (RingOfIntegers.mapRingEquiv τ z) := fun z =>
    (RingOfIntegers.mapRingEquiv_apply τ z).symm
  have hval : (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v).valuationOfNeZero
      (Units.map τ.toMonoidHom a) = v.valuationOfNeZero a := by
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
      HeightOneSpectrum.valuationOfNeZero_eq]
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (𝓞 K) (a : K)
    show HeightOneSpectrum.valuation K' _ (τ (a : K)) = HeightOneSpectrum.valuation K v (a : K)
    rw [← hxy, map_div₀, map_div₀, map_div₀, hτ, hτ, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, intValuation_mapRingEquiv, intValuation_mapRingEquiv]
  unfold ordv; rw [hval]

theorem radClMap (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    (τ : K ≃+* K') (n : ℕ) (a : Kˣ) :
    clMap τ (radCl n a) = radCl n (Units.map τ.toMonoidHom a) := by
  have hinj : Function.Injective (clMap τ) := (clMapBasic K K' K' τ (RingEquiv.refl K')).2.2.1.1
  unfold radCl
  rw [MonoidHom.map_finprod_of_injective _ hinj,
    ← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ))]
  refine finprod_congr fun v => ?_
  rw [map_zpow, ordv_units_map_ringEquiv]
  congr 1
  exact (clMapBasic K K' K' τ (RingEquiv.refl K')).2.2.2 v _ fun x => by
    change x ∈ v.asIdeal ↔ (RingOfIntegers.mapRingEquiv τ).symm (RingOfIntegers.mapRingEquiv τ x) ∈ v.asIdeal
    rw [RingEquiv.symm_apply_apply]

private theorem finSupp_ordv {K : Type} [Field K] [NumberField K] {G : Type} [CommGroup G]
    (g : HeightOneSpectrum (𝓞 K) → G) (n : ℤ) (a : Kˣ) :
    Function.HasFiniteMulSupport fun v => g v ^ (ordv v a / n) :=
  ((clProd K).2.2.1 a).subset fun _ hv h => hv (by simp [h])

private theorem mk_radCl {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (a : Kˣ) :
    (QuotientGroup.mk (radCl n a) : ClS S) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / n) := by
  simpa [radCl] using (QuotientGroup.mk' (clSub S)).map_finprod (finSupp_ordv primeCl (n : ℤ) a)

private theorem mk_primeCl_of_mem {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)

private theorem ordv_pow_nat {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (b : Kˣ) (n : ℕ) : ordv v (b ^ n) = n * ordv v b := by
  simp [ordv]

theorem radClMul (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) :
    (∀ a ∈ SelK S n, ∀ b ∈ SelK S n,
      (QuotientGroup.mk (radCl n (a * b)) : ClS S) =
        QuotientGroup.mk (radCl n a) * QuotientGroup.mk (radCl n b)) ∧
    (∀ a ∈ SelK S n, (QuotientGroup.mk (radCl n a) : ClS S) ^ n = 1) ∧
    ∀ a b : Kˣ, radCl n (a * b ^ n) = radCl n a := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have h1 : ∀ x : Kˣ, radCl 1 x = 1 := (clProd K).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [mk_radCl S n, mk_radCl S n, mk_radCl S n,
      ← finprod_mul_distrib (finSupp_ordv (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a)
        (finSupp_ordv (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) b)]
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ S
    · simp [mk_primeCl_of_mem hv]
    · rw [ordv_mul, Int.add_ediv_of_dvd_right (hb v hv), zpow_add]
  · intro a ha
    have e := mk_radCl S 1 a
    rw [h1 a] at e
    simp only [Nat.cast_one, Int.ediv_one, QuotientGroup.mk_one] at e
    rw [mk_radCl S n,
      finprod_pow (finSupp_ordv (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a)]
    refine (finprod_congr fun v => ?_).trans e.symm
    by_cases hv : v ∈ S
    · simp [mk_primeCl_of_mem hv]
    · rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (ha v hv)]
  · intro a b
    have e := h1 b
    simp only [radCl, Nat.cast_one, Int.ediv_one] at e
    have hb1 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) => primeCl v ^ ordv v b := by
      simpa only [Int.ediv_one] using finSupp_ordv (primeCl (K := K)) 1 b
    simp only [radCl]
    rw [finprod_congr (fun v => show primeCl v ^ (ordv v (a * b ^ n) / (n : ℤ)) =
        primeCl v ^ (ordv v a / (n : ℤ)) * primeCl v ^ ordv v b by
          rw [ordv_mul, ordv_pow_nat, Int.add_mul_ediv_left _ _ hn', zpow_add]),
      finprod_mul_distrib (finSupp_ordv primeCl (n : ℤ) a) hb1, e, mul_one]

private theorem exists_frac_of_mem_clSub {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (c : ClassGroup (𝓞 K)) (hc : c ∈ clSub S) :
    ∃ J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K J = c ∧
      ∀ v ∉ S, FractionalIdeal.count K v J.1 = 0 := by
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨FractionalIdeal.mk0 K ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩,
      ClassGroup.mk_mk0 _ _, fun v hv => ?_⟩
    rw [FractionalIdeal.coe_mk0]
    exact FractionalIdeal.count_maximal_coprime K v (fun h : w = v => hv (h ▸ hw))
  | one => exact ⟨1, map_one _, fun v _ => FractionalIdeal.count_one K v⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, rfl, hI⟩ := hx
    obtain ⟨J, rfl, hJ⟩ := hy
    refine ⟨I * J, map_mul _ _ _, fun v hv => ?_⟩
    rw [Units.val_mul, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  | inv x _ hx =>
    obtain ⟨I, rfl, hI⟩ := hx
    refine ⟨I⁻¹, map_inv _ _, fun v hv => ?_⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]

private theorem mk_finprod_congr_clS {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (f g : HeightOneSpectrum (𝓞 K) → ℤ)
    (hf : {v | f v ≠ 0}.Finite) (hg : {v | g v ≠ 0}.Finite) (h : ∀ v ∉ S, f v = g v) :
    (QuotientGroup.mk (∏ᶠ v, primeCl v ^ f v) : ClS S) =
      QuotientGroup.mk (∏ᶠ v, primeCl v ^ g v) := by
  have hfm : ∀ f : HeightOneSpectrum (𝓞 K) → ℤ, {v | f v ≠ 0}.Finite →
      Function.HasFiniteMulSupport (fun v => primeCl v ^ f v) := fun f hf =>
    hf.subset fun _ hv h0 => hv (by simp [h0])
  have e1 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm f hf)
  have e2 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm g hg)
  simp only [QuotientGroup.mk'_apply] at e1 e2
  rw [e1, e2]
  refine finprod_congr fun v => ?_
  by_cases hv : v ∈ S
  · simp [QuotientGroup.mk_zpow, mk_primeCl_of_mem hv]
  · rw [h v hv]

theorem radClSurj (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) (c : ClS S) (hc : c ^ n = 1) :
    ∃ a ∈ SelK S n, QuotientGroup.mk (radCl n a) = c := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨I, rfl⟩ : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = x :=
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hc
  obtain ⟨J, hJ, hJS⟩ := exists_frac_of_mem_clSub S _ hc
  have hP : ClassGroup.mk K (I ^ n * J⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, hJ, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at hP
  obtain ⟨y, hy⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hP
  have hx' : ((I ^ n * J⁻¹ : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = FractionalIdeal.spanSingleton _ y :=
    FractionalIdeal.coeToSubmodule_injective (hy.trans (FractionalIdeal.coe_spanSingleton _ y).symm)
  have hy0 : y ≠ 0 := fun h0 => Units.ne_zero (I ^ n * J⁻¹) (by
    rw [hx', h0, FractionalIdeal.spanSingleton_zero])
  let a : Kˣ := Units.mk0 y hy0
  have hcount : ∀ v ∉ S, ordv v a = n * FractionalIdeal.count K v (I : FractionalIdeal _ K) := by
    intro v hv
    rw [← (clProd K).2.1 v a]
    show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) = _
    rw [← hx', Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_inv, hJS v hv, neg_zero, add_zero]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine ⟨a, fun v hv => ⟨FractionalIdeal.count K v (I : FractionalIdeal _ K), hcount v hv⟩, ?_⟩
  rw [(clProd K).1 I]
  unfold radCl
  refine mk_finprod_congr_clS S _ _
    (((clProd K).2.2.1 a).subset fun _ hv h0 => hv (by simp [h0]))
    (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _))
    fun v hv => by rw [hcount v hv, Int.mul_ediv_cancel_left _ hn']

private theorem prod_add_primeCl {K : Type} [Field K] [NumberField K]
    (f g : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite) (hg : {v | g v ≠ 0}.Finite) :
    ∏ᶠ v, primeCl v ^ (f v + g v) = (∏ᶠ v, primeCl v ^ f v) * ∏ᶠ v, primeCl v ^ g v := by
  rw [← finprod_mul_distrib (hf.subset fun _ hv h => hv (by simp [h]))
    (hg.subset fun _ hv h => hv (by simp [h]))]
  exact finprod_congr fun v => zpow_add _ _ _

private theorem fin_add_supp {α : Type} {f g : α → ℤ} (hf : {v | f v ≠ 0}.Finite)
    (hg : {v | g v ≠ 0}.Finite) : {v | f v + g v ≠ 0}.Finite :=
  (hf.union hg).subset fun _ hv => by
    by_contra h; simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hv (by rw [h.1, h.2, add_zero])

private theorem mem_clSub_finprod {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {c : ClassGroup (𝓞 K)} (hc : c ∈ clSub S) :
    ∃ g : HeightOneSpectrum (𝓞 K) → ℤ, {v | g v ≠ 0}.Finite ∧ (∀ v ∉ S, g v = 0) ∧
      c = ∏ᶠ v, primeCl v ^ g v := by
  classical
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨fun v => if v = w then 1 else 0,
      (Set.finite_singleton w).subset fun _ hv => by by_contra h; exact hv (if_neg h),
      fun v hv => if_neg fun (h : v = w) => hv (h ▸ hw), ?_⟩
    rw [finprod_eq_single _ w fun _ hv => by simp [hv]]; simp
  | one => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf, hf', rfl⟩ := hx; obtain ⟨g, hg, hg', rfl⟩ := hy
    exact ⟨fun v => f v + g v, fin_add_supp hf hg, fun v hv => by simp [hf' v hv, hg' v hv],
      (prod_add_primeCl f g hf hg).symm⟩
  | inv x _ hx =>
    obtain ⟨f, hf, hf', rfl⟩ := hx
    refine ⟨fun v => -f v, by simpa using hf, fun v hv => by simp [hf' v hv], ?_⟩
    rw [← finprod_inv_distrib]; exact finprod_congr fun _ => (zpow_neg _ _).symm

private theorem exists_ordv_of_finprod_one {K : Type} [Field K] [NumberField K]
    (f : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite)
    (h : ∏ᶠ v, primeCl v ^ f v = 1) : ∃ b : Kˣ, ∀ v, ordv v b = f v := by
  obtain ⟨h1, h2, -, -⟩ := clProd K
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ f v
  have hI0 : I ≠ 0 := finprod_induction (fun J => J ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero)
    fun v => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hc : ∀ v, FractionalIdeal.count K v I = f v := fun v =>
    FractionalIdeal.count_finprod K v f (by simpa [Filter.eventually_cofinite] using hf)
  have h3 : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
    rw [h1, ← h]; exact finprod_congr fun v => by rw [Units.val_mk0, hc]
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h3)
  rw [Units.val_mk0] at hb
  have hb0 : b ≠ 0 := fun h0 => hI0 (by rw [hb, h0, FractionalIdeal.spanSingleton_zero])
  exact ⟨Units.mk0 b hb0, fun v => by rw [← h2, Units.val_mk0, ← hb, hc]⟩

private theorem mem_sUnit_iff_ordv_zero {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {u : Kˣ} :
    u ∈ S.unit K ↔ ∀ v ∉ S, ordv v u = 0 := by
  change (∀ v ∉ S, v.valuation K (u : K) = 1) ↔ _
  refine forall₂_congr fun v _ => ?_
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj, ordv,
    neg_eq_zero, toAdd_eq_zero]

theorem radClKer (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) (a : Kˣ) (ha : a ∈ SelK S n) :
    radCl n a ∈ clSub S ↔ a ∈ S.unit K ⊔ powK K n := by
  constructor
  · intro h
    obtain ⟨g, hg, hg', hc⟩ := mem_clSub_finprod (inv_mem h)
    have hf : {v | ordv v a / n ≠ 0}.Finite :=
      ((clProd K).2.2.1 a).subset fun _ hv h0 => hv (by simp [h0])
    obtain ⟨b, hb⟩ := exists_ordv_of_finprod_one (fun v => ordv v a / n + g v) (fin_add_supp hf hg)
      (by rw [prod_add_primeCl _ _ hf hg, ← hc]; exact mul_inv_cancel _)
    refine Subgroup.mem_sup.2 ⟨a * (b ^ n)⁻¹, mem_sUnit_iff_ordv_zero.2 fun v hv => ?_,
      b ^ n, ⟨b, rfl⟩, by simp⟩
    rw [ordv_mul, ordv_inv, ordv_pow_nat, hb, hg' v hv, add_zero, Int.mul_ediv_cancel' (ha v hv),
      add_neg_cancel]
  · intro h
    obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h
    rw [powMonoidHom_apply, (radClMul K S n hn).2.2]
    refine finprod_induction (fun c => c ∈ clSub S) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
    by_cases hv : v ∈ S
    · have h0 : primeCl v ∈ clSub S := Subgroup.subset_closure ⟨v, hv, rfl⟩
      exact zpow_mem h0 _
    · rw [mem_sUnit_iff_ordv_zero.1 hu v hv]; simp

theorem cardSel (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (SelK S n ⧸ (powK K n).subgroupOf (SelK S n)) =
      Nat.card (S.unit K ⧸ (powK K n).subgroupOf (S.unit K)) *
        Nat.card {c : ClS S // c ^ n = 1} := by
  obtain ⟨hmul, hpow, -⟩ := radClMul K S n hn
  let f : SelK S n →* ClS S :=
    MonoidHom.mk' (fun a => (QuotientGroup.mk (radCl n a.1) : ClS S)) fun a b => hmul a.1 a.2 b.1 b.2
  have hU : S.unit K ≤ SelK S n := fun a ha v hv => by
    rw [mem_sUnit_iff_ordv_zero.1 ha v hv]; exact dvd_zero _
  have hP : powK K n ≤ SelK S n := by rintro _ ⟨b, rfl⟩ v _; simp [ordv]
  have hf : f.ker = (S.unit K ⊔ powK K n).subgroupOf (SelK S n) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← radClKer K S n hn a.1 a.2]
    exact QuotientGroup.eq_one_iff _
  have hQ : S.unit K ⊔ powK K n ≤ SelK S n := sup_le hU hP
  have hPQ : (powK K n).subgroupOf (SelK S n) ≤ (S.unit K ⊔ powK K n).subgroupOf (SelK S n) :=
    fun _ hx => (le_sup_right : powK K n ≤ S.unit K ⊔ powK K n) hx
  have hcard : Nat.card (SelK S n ⧸ (powK K n).subgroupOf (SelK S n)) =
      Nat.card (S.unit K ⧸ (powK K n).subgroupOf (S.unit K)) * Nat.card f.range := by
    change ((powK K n).subgroupOf (SelK S n)).index = ((powK K n).subgroupOf (S.unit K)).index * _
    rw [← Subgroup.relIndex_mul_index hPQ, Subgroup.relIndex_subgroupOf hQ,
      Subgroup.relIndex_sup_right, ← hf]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hcard]; congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ⟨?_, fun hc => ?_⟩)
  · rintro ⟨a, rfl⟩; exact hpow a.1 a.2
  · obtain ⟨a, ha, h⟩ := radClSurj K S n hn c hc
    show c ∈ f.range
    exact ⟨⟨a, ha⟩, h⟩

theorem radExists (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (n : ℕ) [NeZero n] (ζ : Ω) (η z : G K Ω → ZMod n)
    (hζ : IsPrimitiveRoot ζ n) (hη : ∀ g : G K Ω, g ζ = ζ ^ (η g).val)
    (hz : IsLocallyConstant z) (hc : ∀ g h, z (g * h) = z g + η g * z h) :
    ∃ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζ ^ (z g).val * β := by
  have hmod : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => (pow_eq_pow_mod m hζ.pow_eq_one).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  obtain ⟨β, hβ0, hβ⟩ := h90 K Ω (fun g => ζ ^ (z g).val)
    (hz.comp fun x : ZMod n => ζ ^ x.val) (fun g => pow_ne_zero _ hζ0) (fun g h => by
      show ζ ^ (z (g * h)).val = ζ ^ (z g).val * g (ζ ^ (z h).val)
      rw [hc, ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod, map_pow, hη, ← pow_mul])
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g (β ^ n) = β ^ n := fun g => by
    rw [map_pow, hβ g, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ n)).2 hfix
  have ha0 : a ≠ 0 := fun h0 => pow_ne_zero n hβ0 (ha.symm.trans (by rw [h0, map_zero]))
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩

private theorem ram_one_fixedField {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois K E] (v : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 E)) [P.IsPrime]
    [P.LiesOver v.asIdeal] (L : IntermediateField K E) (h : P.inertia (E ≃ₐ[K] E) ≤ L.fixingSubgroup) :
    (P.under (𝓞 L)).ramificationIdx (𝓞 K) = 1 := by
  have hb := v.ne_bot
  have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
  have hqb : P.under (𝓞 L) ≠ ⊥ := Ideal.under_ne_bot _ hPb
  haveI : IsGaloisGroup L.fixingSubgroup L E :=
    .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv L) fun _ _ => rfl
  haveI : IsGaloisGroup L.fixingSubgroup (𝓞 L) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing _ _ _ L E
  haveI := v.isMaximal
  haveI : (P.under (𝓞 L)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
  haveI : Finite (𝓞 L ⧸ P.under (𝓞 L)) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
  haveI : (P.under (𝓞 L)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[K] E) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L.fixingSubgroup) (P.under (𝓞 L)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (E ≃ₐ[K] E)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P L.fixingSubgroup] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) (P.under (𝓞 L)) P
  have h4 : Nat.card (P.inertia L.fixingSubgroup) =
      Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := by
    rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
  rw [← h1, ← h2, h4] at h3
  have hpos : 0 < Nat.card ↥(P.inertia (E ≃ₐ[K] E) ⊓ L.fixingSubgroup) := Nat.card_pos
  rw [inf_eq_left.mpr h] at h3 hpos
  exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)

private theorem valuation_liesOver_of_ram_one {K M : Type} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
    (hram : w.asIdeal.ramificationIdx (𝓞 K) = 1) (x : K) :
    w.valuation M (algebraMap K M x) = v.valuation K x := by
  let f : 𝓞 K →+* 𝓞 M := algebraMap (𝓞 K) (𝓞 M)
  have hf_inj : Function.Injective f := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 M)
  have hmap_ne : ∀ {I : Ideal (𝓞 K)}, I ≠ ⊥ → Ideal.map f I ≠ ⊥ := fun {I} hI hbot => by
    obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hmem : f r ∈ Ideal.map f I := Ideal.mem_map_of_mem f hrI
    rw [hbot, Ideal.mem_bot] at hmem
    exact hr0 (hf_inj (hmem.trans (map_zero f).symm))
  have hw_prime : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hmult_v : emultiplicity w.asIdeal (Ideal.map f v.asIdeal) = 1 := by
    have hne : Ideal.map f v.asIdeal ≠ ⊥ := hmap_ne v.ne_bot
    have hfin : FiniteMultiplicity w.asIdeal (Ideal.map f v.asIdeal) :=
      FiniteMultiplicity.of_prime_left hw_prime hne
    rw [hfin.emultiplicity_eq_multiplicity,
      ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal w.asIdeal hne, hram]
    rfl
  have hmult_ne : ∀ {p : Ideal (𝓞 K)}, Prime p → p ≠ v.asIdeal →
      emultiplicity w.asIdeal (Ideal.map f p) = 0 := fun {p} hp hne => by
    refine emultiplicity_eq_zero.mpr fun hdvd => hne ?_
    have hle : p ≤ w.asIdeal.comap f := Ideal.map_le_iff_le_comap.mp (Ideal.le_of_dvd hdvd)
    rw [show w.asIdeal.comap f = v.asIdeal from
      (Ideal.LiesOver.over (p := v.asIdeal) (P := w.asIdeal)).symm] at hle
    exact ((Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le v.isPrime.ne_top hle
  have hmult_eq : ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      emultiplicity w.asIdeal (Ideal.map f I) = emultiplicity v.asIdeal I := fun I hI => by
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact absurd rfl hI
    | h₂ u hu =>
      rw [Ideal.isUnit_iff.mp hu, Ideal.map_top,
        emultiplicity_eq_zero.mpr (fun hd => w.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ (Ideal.le_of_dvd hd (by simp)) isUnit_one)),
        emultiplicity_eq_zero.mpr (fun hd => v.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ (Ideal.le_of_dvd hd (by simp)) isUnit_one))]
    | h₃ a p ha hp ih =>
      rw [Ideal.map_mul, emultiplicity_mul hw_prime, emultiplicity_mul hv_prime, ih ha]
      by_cases hpv : p = v.asIdeal
      · subst hpv
        have hself : emultiplicity v.asIdeal v.asIdeal = 1 :=
          emultiplicity_eq_coe.mpr ⟨by simp, fun hd =>
            hv_prime.not_isUnit (isUnit_iff_dvd_one.mpr ((mul_dvd_mul_iff_left v.ne_bot).mp (by simpa [sq] using hd)))⟩
        rw [hmult_v, hself]
      · have hzero : emultiplicity v.asIdeal p = 0 :=
          emultiplicity_eq_zero.mpr fun hd =>
            hpv (((Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le v.isPrime.ne_top
              (Ideal.le_of_dvd hd))
        rw [hmult_ne hp hpv, hzero]
  have hint_eq : ∀ r : 𝓞 K, w.intValuation (f r) = v.intValuation r := fun r => by
    by_cases hr : r = 0
    · subst hr; simp
    · have hfr : f r ≠ 0 := fun h => hr (hf_inj (h.trans (map_zero f).symm))
      have ha0 : w.intValuation (f r) ≠ 0 := HeightOneSpectrum.intValuation_ne_zero w (f r) hfr
      have hb0 : v.intValuation r ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v r hr
      have ha1 : w.intValuation (f r) ≤ 1 := HeightOneSpectrum.intValuation_le_one w (f r)
      have hb1 : v.intValuation r ≤ 1 := HeightOneSpectrum.intValuation_le_one v r
      have hcut : ∀ m : ℕ, w.intValuation (f r) ≤ WithZero.exp (-(m : ℤ)) ↔
          v.intValuation r ≤ WithZero.exp (-(m : ℤ)) := fun m => by
        rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          show Ideal.span {f r} = Ideal.map f (Ideal.span {r}) by rw [Ideal.map_span, Set.image_singleton],
          pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity,
          hmult_eq _ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hr)]
      have hkey : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
          (∀ m : ℕ, a ≤ WithZero.exp (-(m : ℤ)) → b ≤ WithZero.exp (-(m : ℤ))) → b ≤ a := by
        intro a b h0 h1 hc
        have hlog : WithZero.log a ≤ 0 := by
          rw [← WithZero.exp_le_exp, WithZero.exp_log h0, WithZero.exp_zero]; exact h1
        have hm : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
        have h2 := hc (-WithZero.log a).toNat (by rw [hm, neg_neg, WithZero.exp_log h0])
        rwa [hm, neg_neg, WithZero.exp_log h0] at h2
      exact le_antisymm (hkey hb0 hb1 fun m => (hcut m).2) (hkey ha0 ha1 fun m => (hcut m).1)
  obtain ⟨r, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : algebraMap K M (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) =
      algebraMap (𝓞 M) M (f r) / algebraMap (𝓞 M) M (f s) := by
    rw [map_div₀]; rfl
  rw [h1, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, hint_eq, hint_eq]

private theorem dvd_of_ram {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] (h : Q.ramificationIdx (𝓞 K) = 1) (n : ℕ) (b : L) (a : Kˣ)
    (hb : b ^ n = algebraMap K L a) : (n : ℤ) ∣ ordv v a := by
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have h1 : w.valuation L (algebraMap K L (a : K)) = v.valuation K (a : K) :=
    valuation_liesOver_of_ram_one v w h (a : K)
  rw [← hb, map_pow, ← HeightOneSpectrum.valuationOfNeZero_eq] at h1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at h1
    simp [ordv, h1]
  · have h0 : w.valuation L b ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at h1; exact WithZero.coe_ne_zero h1.symm
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at h1
    rw [ordv, ← h1, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

theorem dvdOfIne (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω)
    (a : Kˣ) (hA : IsPlaceOver A v) (hβ : β ^ n = algebraMap K Ω a)
    (hI : ∀ g ∈ Ine (F := K) A, g β = β) : (n : ℤ) ∣ ordv v a := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω :=
    (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  haveI : NumberField L := NumberField.of_module_finite K _
  have hv : (cen A).under (𝓞 K) = v.asIdeal := Ideal.ext fun x => hA x
  haveI : Algebra.IsIntegral (𝓞 K) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  haveI : (cen A).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) _ (by
      have := v.isMaximal; rwa [← hv] at this)
  let P : Ideal (𝓞 L) := (cen A).under (𝓞 L)
  haveI : P.LiesOver v.asIdeal := ⟨by rw [← hv]; exact (Ideal.under_under _).symm⟩
  let L0 : IntermediateField K L := IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L))
  have hle : P.inertia (L ≃ₐ[K] L) ≤ L0.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hbL0 : (⟨β, hβL⟩ : L) ∈ L0 := (IntermediateField.mem_fixedField_iff _ _).2 fun τ hτ => by
    obtain ⟨φ, h1, h2⟩ := cen_lift L (cen A) τ (RingHom.id _) fun x => by
      rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub]
      have hsub : x - τ • x ∈ P := by simpa [neg_sub] using P.neg_mem (hτ x)
      exact hsub
    obtain ⟨h3, h4⟩ := cen_of_cong A φ one_ne_zero fun b => by
      rw [pow_one]; exact Ideal.Quotient.eq.1 (h2 b)
    have h5 : φ ∈ Ine (F := K) A := ⟨h3, fun x hx => by
      simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩
    rw [← h1]
    exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ h5))
  haveI : (P.under (𝓞 L0)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  exact dvd_of_ram v (P.under (𝓞 L0)) (ram_one_fixedField v P L0 hle) n ⟨⟨β, hβL⟩, hbL0⟩ a
    (Subtype.ext (Subtype.ext hβ))

private theorem finite_above_of_ne_zero (K : Type) [Field K] [NumberField K] (N : ℕ) (hN : N ≠ 0) :
    (Above K N).Finite := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  exact (Ideal.finite_factors h0).subset fun _ hv => Ideal.dvd_span_singleton.2 hv

theorem finChar (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (n N : ℕ) (ζ : K) (hn : n ≠ 0) (hN : N ≠ 0) (hζ : IsPrimitiveRoot ζ n) :
    {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}.Finite := by
  haveI : NeZero n := ⟨hn⟩
  let ζΩ := algebraMap K Ω ζ
  have hζΩ : IsPrimitiveRoot ζΩ n := hζ.map_of_injective (algebraMap K Ω).injective
  have hfix : ∀ (g : G K Ω) (x : K), g (algebraMap K Ω x) = algebraMap K Ω x :=
    fun g x => AlgEquiv.commutes g x
  have hη : ∀ g : G K Ω, g ζΩ = ζΩ ^ ((fun _ => (1 : ZMod n)) g).val := fun g => by
    rw [hfix g ζ]
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, pow_one]
    · have hn1 : n = 1 := by omega
      subst hn1; simp [ζΩ, IsPrimitiveRoot.one_right_iff.1 hζ]
  have key : ∀ φ ∈ {φ : G K Ω → ZMod n | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0},
      ∃ β : Ω, ∃ a : Kˣ, a ∈ SelK (Above K N) n ∧ β ^ n = algebraMap K Ω a ∧
        ∀ g : G K Ω, g β = ζΩ ^ (φ g).val * β := by
    rintro φ ⟨hlc, hadd, hine⟩
    obtain ⟨β, a, hβ, hg⟩ := radExists K Ω n ζΩ (fun _ => 1) φ hζΩ hη hlc
      (fun g h => by rw [hadd, one_mul])
    refine ⟨β, a, fun v hv => ?_, hβ, hg⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    have hnot : ¬ A.valuation (N : Ω) < 1 := fun h => hv (((placeDict K Ω).2.2.2 A v N hA).1 h)
    exact dvdOfIne K Ω n A v β a hA hβ
      (fun g hg' => by rw [hg, hine A hnot g hg', ZMod.val_zero, pow_zero, one_mul])
  choose! β a ha hβ hg using key
  haveI hQ : Finite (↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n)) := by
    apply Nat.finite_of_card_ne_zero
    rw [cardSel K _ n hn, cardSUnit K _ n (finite_above_of_ne_zero K N hN)]
    have h1 : Nat.card ↥(rootsOfUnity n K) ≠ 0 := Nat.card_pos.ne'
    have h2 : Nat.card {c : ClS (Above K N) // c ^ n = 1} ≠ 0 := by
      haveI : Nonempty {c : ClS (Above K N) // c ^ n = 1} := ⟨⟨1, one_pow _⟩⟩
      exact Nat.card_pos.ne'
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn) h1) h2
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (β := ↥(SelK (Above K N) n) ⧸ (powK K n).subgroupOf (SelK (Above K N) n))
    (fun φ => QuotientGroup.mk ⟨a φ.1, ha φ.1 φ.2⟩) ?_
  rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h
  simp only at h
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hc
  have hcu : a φ * c ^ n = a ψ := by rw [hc, mul_inv_cancel_left]
  have hne : ∀ θ ∈ _, β θ ≠ 0 := fun θ hθ h0 => by
    have := hβ θ hθ; rw [h0, zero_pow hn] at this
    exact (Units.ne_zero (a θ)) ((algebraMap K Ω).injective (this.symm.trans (map_zero _).symm))
  refine Subtype.ext (funext fun g => ?_)
  have hφ0 := hne φ hφ
  have hcΩ : algebraMap K Ω (c : K) ≠ 0 := by rw [Ne, map_eq_zero]; exact c.ne_zero
  set ω := β ψ / (β φ * algebraMap K Ω (c : K)) with hωdef
  have hωn : ω ^ n = 1 := by
    rw [hωdef, div_pow, mul_pow, hβ ψ hψ, hβ φ hφ, ← map_pow, ← map_mul, ← hcu]
    push_cast; exact div_self (by simp)
  obtain ⟨i, -, hi⟩ := hζΩ.eq_pow_of_pow_eq_one hωn
  have hψeq : β ψ = ω * (β φ * algebraMap K Ω (c : K)) := by
    rw [hωdef, div_mul_cancel₀ _ (mul_ne_zero hφ0 hcΩ)]
  have hgω : g ω = ω := by rw [← hi, map_pow]; exact congrArg (· ^ i) (hfix g ζ)
  have hω0 : ω ≠ 0 := by rw [← hi]; exact pow_ne_zero _ (hζΩ.ne_zero hn)
  have e1 := hg ψ hψ g
  rw [hψeq, map_mul, map_mul, hgω, hg φ hφ g, hfix] at e1
  have e2 : ζΩ ^ (φ g).val = ζΩ ^ (ψ g).val := by
    apply mul_right_cancel₀ (mul_ne_zero hω0 (mul_ne_zero hφ0 hcΩ))
    linear_combination e1
  exact ZMod.val_injective _ (hζΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e2)

theorem radConj (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (ζ β : Ω) (σ : Ω ≃+* Ω) (k : ZMod n)
    (φ φ' : U → ZMod n) (hζ : ζ ^ n = 1) (hσ : σ ζ = ζ ^ k.val) (hβ : IsRad ζ U φ β)
    (h : ∀ u' : U, ∃ u : U, (∀ x, u'.1 (σ x) = σ (u.1 x)) ∧ φ' u' = k * φ u) :
    IsRad ζ U φ' (σ β) := by
  refine ⟨fun h0 => hβ.1 (σ.injective (by rw [h0, map_zero])), fun u' => ?_⟩
  obtain ⟨u, hu, hφ⟩ := h u'
  rw [hu β, hβ.2 u, map_mul, map_pow, hσ, hφ, ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hζ]

theorem radXDual (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K)
    (hU : U = galOf F K Ω) (hζ : IsPrimitiveRoot ζ n) :
    (∀ φ ∈ XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧
        a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) ∧
    ∀ (φ : U → ZMod n) (β β' : Ω), IsRad (algebraMap K Ω ζ) U φ β →
      IsRad (algebraMap K Ω ζ) U φ β' → ∃ c : Kˣ, β' = algebraMap K Ω c * β := by
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  obtain ⟨-, hI, -, hH⟩ := toGalDict F Ω K (galOf F K Ω) le_rfl
  obtain ⟨hH, -⟩ := hH le_rfl
  let s : G K Ω → galOf F K Ω := fun σ => ⟨galEmb F K Ω σ, galEmb_mem F K Ω σ⟩
  have hs : ∀ σ, toGal K le_rfl (s σ) = σ := fun _ => AlgEquiv.ext fun _ => rfl
  have hs' : ∀ u, s (toGal K le_rfl u) = u := fun _ => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have hsm : ∀ σ τ, s (σ * τ) = s σ * s τ := fun σ τ => Subtype.ext (map_mul (galEmb F K Ω) σ τ)
  have hsc : Continuous s := by
    have e : s = hH.homeomorph.symm := funext fun σ => by
      rw [eq_comm, Homeomorph.symm_apply_eq]; exact (hs σ).symm
    rw [e]; exact hH.homeomorph.symm.continuous
  refine ⟨fun φ hφ => ?_, fun φ β β' hβ hβ' => ?_⟩
  · obtain ⟨hlc, hadd, hine, -⟩ := hφ
    obtain ⟨β, a, hβa, hβ⟩ := radExists K Ω n (algebraMap K Ω ζ) (fun _ => 1) (fun σ => φ (s σ)) hζ'
      (fun g => by rw [g.commutes, ZMod.val_one_eq_one_mod, hζ'.eq_orderOf, pow_mod_orderOf, pow_one])
      (hlc.comp_continuous hsc) (fun g h => by rw [hsm, hadd, one_mul])
    refine ⟨β, a, ⟨fun h0 => a.ne_zero ((map_eq_zero _).1 (by
      rw [← hβa, h0, zero_pow (NeZero.ne n)])), fun u => by
        have hu := hβ (toGal K le_rfl u)
        rw [hs'] at hu
        exact hu⟩,
      hβa, fun v _ => ?_⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne K Ω n A v β a hA hβa fun g hg => ?_
    have h0 : φ (s g) = 0 := hine A (s g) ((hI A (s g)).1 (by rw [hs]; exact hg))
    rw [hβ g, h0, ZMod.val_zero, pow_zero, one_mul]
  · have hz : algebraMap K Ω ζ ≠ 0 := hζ'.ne_zero (NeZero.ne n)
    haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
    have hfix : ∀ g : G K Ω, g (β' / β) = β' / β := fun g => by
      have e1 : g β = _ := hβ.2 (s g)
      have e2 : g β' = _ := hβ'.2 (s g)
      rw [map_div₀, e1, e2, mul_div_mul_left _ _ (pow_ne_zero _ hz)]
    obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β' / β)).2 hfix
    have hc0 : c ≠ 0 := fun h0 => div_ne_zero hβ'.1 hβ.1 (hc.symm.trans (by rw [h0, map_zero]))
    exact ⟨Units.mk0 c hc0, by rw [Units.val_mk0, hc, div_mul_cancel₀ _ hβ.1]⟩

private theorem card_dvd_of_quot_inj {A B : Type} [Group A] [CommGroup B] (E P : Subgroup B)
    (j : A →* B ⧸ P) (hj : Function.Injective j) (hE : ∀ x, ∃ b ∈ E ⊔ P, j x = QuotientGroup.mk b) :
    Nat.card A ∣ Nat.card (E ⧸ P.subgroupOf E) := by
  let f : E →* B ⧸ P := (QuotientGroup.mk' P).comp E.subtype
  have hk : f.ker = P.subgroupOf E := by ext x; simp [f, Subgroup.mem_subgroupOf]
  have h1 : Nat.card (E ⧸ P.subgroupOf E) = Nat.card f.range := by
    rw [← hk]; exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hm : ∀ x, j x ∈ f.range := fun x => by
    obtain ⟨b, hb, h⟩ := hE x
    obtain ⟨e, he, p, hp, rfl⟩ := Subgroup.mem_sup.1 hb
    exact ⟨⟨e, he⟩, by rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p).2 hp, mul_one]; rfl⟩
  rw [h1]
  exact Subgroup.card_dvd_of_injective (j.codRestrict f.range hm)
    fun _ _ h => hj (congrArg Subtype.val h)

private theorem pow_val_add {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] {ζ : Ω} (hζ : ζ ^ n = 1)
    (x y : ZMod n) : ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + y.val) n, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem reflMap (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K)
    (hU : U = galOf F K Ω) (hζ : IsPrimitiveRoot ζ n) :
    ∃ κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K)),
      (∀ (φ : XDual N U (ZMod n) (ZMod n)) (β : Ω) (a : Kˣ),
        IsRad (algebraMap K Ω ζ) U φ.1 β → β ^ n = algebraMap K Ω a →
        κ φ = Additive.ofMul (radCl n a)) ∧
      Nat.card κ.ker ∣ Nat.card ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K ⧸
        (powK K n).subgroupOf ((∅ : Set (HeightOneSpectrum (𝓞 K))).unit K)) := by
  obtain ⟨hex, huniq⟩ := radXDual F Ω K U n N ζ hU hζ
  have hn : n ≠ 0 := NeZero.ne n
  obtain ⟨hmul, -, hpow⟩ := radClMul K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn
  have hker := radClKer K (∅ : Set (HeightOneSpectrum (𝓞 K))) n hn
  have hbot : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥ := by simp [clSub]
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hex' : ∀ φ : XDual N U (ZMod n) (ZMod n), ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) U φ.1 β ∧ β ^ n = algebraMap K Ω a ∧
        a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n := fun φ => hex φ.1 φ.2
  choose β a hrad hβ hsel using hex'
  have hwd : ∀ (φ : XDual N U (ZMod n) (ZMod n)) (β' : Ω) (a' : Kˣ),
      IsRad (algebraMap K Ω ζ) U φ.1 β' → β' ^ n = algebraMap K Ω a' → ∃ c : Kˣ, a' = a φ * c ^ n := by
    intro φ β' a' h1 h2
    obtain ⟨c, hc⟩ := huniq φ.1 (β φ) β' (hrad φ) h1
    refine ⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩
    rw [← h2, hc, mul_pow, hβ]; simp [mul_comm]
  have hadd : ∀ φ ψ : XDual N U (ZMod n) (ZMod n), ∃ c : Kˣ, a φ * a ψ = a (φ + ψ) * c ^ n := by
    intro φ ψ
    refine hwd (φ + ψ) (β φ * β ψ) _ ⟨mul_ne_zero (hrad φ).1 (hrad ψ).1, fun u => ?_⟩
      (by rw [mul_pow, hβ, hβ]; simp)
    rw [map_mul, (hrad φ).2 u, (hrad ψ).2 u]
    change _ = algebraMap K Ω ζ ^ (φ.1 u + ψ.1 u).val * _
    rw [pow_val_add hζ'.pow_eq_one]; ring
  have hmul' : ∀ φ ψ : XDual N U (ZMod n) (ZMod n),
      radCl n (a (φ + ψ)) = radCl n (a φ) * radCl n (a ψ) := fun φ ψ => by
    obtain ⟨c, hc⟩ := hadd φ ψ
    have h := hmul _ (hsel φ) _ (hsel ψ)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hbot, Subgroup.mem_bot, inv_mul_eq_one, hc, hpow] at h
    exact h
  let κ : XDual N U (ZMod n) (ZMod n) →+ Additive (ClassGroup (𝓞 K)) :=
    AddMonoidHom.mk' (fun φ => Additive.ofMul (radCl n (a φ))) fun φ ψ => by rw [hmul']; rfl
  have hκ : ∀ φ, κ φ = Additive.ofMul (radCl n (a φ)) := fun _ => rfl
  refine ⟨κ, fun φ β' a' h1 h2 => ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := hwd φ β' a' h1 h2
    rw [hκ, hpow]
  · let j : Multiplicative κ.ker →* Kˣ ⧸ powK K n :=
      MonoidHom.mk' (fun x => QuotientGroup.mk (a (Multiplicative.toAdd x).1)) fun x y => by
        obtain ⟨c, hc⟩ := hadd (Multiplicative.toAdd x).1 (Multiplicative.toAdd y).1
        have hc1 : (QuotientGroup.mk (c ^ n) : Kˣ ⧸ powK K n) = 1 :=
          (QuotientGroup.eq_one_iff _).2 ⟨c, rfl⟩
        rw [← QuotientGroup.mk_mul, hc, QuotientGroup.mk_mul, hc1, mul_one]; rfl
    refine card_dvd_of_quot_inj (A := Multiplicative κ.ker) _ _ j ?_ fun x => ?_
    · rw [injective_iff_map_eq_one]
      intro x hx
      change (QuotientGroup.mk (a (Multiplicative.toAdd x).1) : Kˣ ⧸ powK K n) = 1 at hx
      rw [QuotientGroup.eq_one_iff] at hx
      obtain ⟨c, hc⟩ := hx
      set φ := (Multiplicative.toAdd x).1
      have hc' : c ^ n = a φ := hc
      have hc0 : algebraMap K Ω c ≠ 0 := by simp
      have h1 : (β φ / algebraMap K Ω c) ^ n = 1 := by
        rw [div_pow, hβ, ← hc', Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hc0)]
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
      have h2 : β φ = algebraMap K Ω (ζ ^ i * c) := by rw [map_mul, map_pow, hi, div_mul_cancel₀ _ hc0]
      have h0 : φ = 0 := Subtype.ext (funext fun u => by
        have hu : u.1 ∈ galOf F K Ω := hU ▸ u.2
        have h3 : u.1 (β φ) = β φ := by rw [h2]; exact hu _
        rw [(hrad φ).2 u, mul_eq_right₀ (hrad φ).1] at h3
        exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt (hζ'.dvd_of_pow_eq_one _ h3) (ZMod.val_lt _)))
      exact Multiplicative.toAdd.injective (Subtype.ext h0)
    · have hx0 : radCl n (a (Multiplicative.toAdd x).1) = 1 :=
        Additive.ofMul.injective (Multiplicative.toAdd x).2
      refine ⟨a (Multiplicative.toAdd x).1,
        (hker _ (hsel (Multiplicative.toAdd x).1)).1 (by rw [hx0]; exact one_mem _), rfl⟩

private theorem exp_tors_nf (K : Type) [Field K] [NumberField K] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ a : K, IsOfFinOrder a → a ^ m = 1 := by
  refine ⟨Units.torsionOrder K, Units.torsionOrder_ne_zero K, fun a ha => ?_⟩
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  let x : 𝓞 K := ⟨a, IsIntegral.of_pow hk (by rw [hak]; exact isIntegral_one)⟩
  have hx : x ^ k = 1 := RingOfIntegers.coe_injective (by rw [map_pow, map_one]; exact hak)
  let y : (𝓞 K)ˣ := Units.ofPowEqOne x k hx hk.ne'
  have hy : y ∈ Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext (by simp [y])⟩)
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hy
  have h2 := congrArg (fun z : (𝓞 K)ˣ => algebraMap (𝓞 K) K z) hy
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h2
  exact h2

private theorem conj_root_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (g u : Ω ≃ₐ[F] Ω)
    (β : Ω) (hβ : IsOfFinOrder β) : g (u (g.symm β)) = u β := by
  have hp := IsPrimitiveRoot.orderOf β
  haveI : NeZero (orderOf β) := ⟨hβ.orderOf_pos.ne'⟩
  have key : ∀ s : Ω ≃ₐ[F] Ω, ∃ i : ℕ, β ^ i = s β := fun s => by
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one (ξ := s β)
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := key g.symm
  obtain ⟨j, hj⟩ := key u
  rw [← hi, map_pow, ← hj, ← pow_mul, mul_comm, pow_mul, hi, map_pow, g.apply_symm_apply]

theorem reflRoot (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K]
    (ψ : G F Ω →* (ZMod n)ˣ) (hU : U = galOf F K Ω) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧
      ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧
        IsOfFinOrder β} ≤ Nat.card (scalRep (ZMod n) ψ).invariants ∧
    Finite {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧
      ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧
        IsOfFinOrder β} := by
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hinj : ∀ x y : ZMod n, algebraMap K Ω ζ ^ x.val = algebraMap K Ω ζ ^ y.val → x = y :=
    fun x y h => ZMod.val_injective n (hζ'.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)
  obtain ⟨ξ, b, hb, hξ⟩ : ∃ (ξ : Ωˣ) (b : K), (ξ : Ω) ^ n = algebraMap K Ω b ∧
      ∀ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a → IsOfFinOrder β → ∃ j : ℤ, (ξ : Ω) ^ j = β := by
    obtain ⟨m, hm, hK⟩ := exp_tors_nf K
    haveI : NeZero (n * m) := ⟨mul_ne_zero (NeZero.ne n) hm⟩
    let T : Subgroup Ωˣ := rootsOfUnity (n * m) Ω ⊓
      ((Units.map (algebraMap K Ω).toMonoidHom).range).comap (powMonoidHom n)
    haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : T ≤ _))
    obtain ⟨⟨ξ, hξ⟩, hg⟩ := (isCyclic_subgroup_units T).exists_generator
    obtain ⟨b, hb⟩ := hξ.2
    refine ⟨ξ, b, by simpa using (congrArg Units.val hb).symm, fun β a h hβ => ?_⟩
    have h0 : β ≠ 0 := fun h0 => a.ne_zero ((map_eq_zero _).1 (by rw [← h, h0, zero_pow (NeZero.ne n)]))
    have ha : IsOfFinOrder (a : K) := by
      obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 (h ▸ hβ.pow (n := n))
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, (algebraMap K Ω).injective (by rw [map_pow, hak, map_one])⟩
    have hT : Units.mk0 β h0 ∈ T :=
      ⟨(mem_rootsOfUnity _ _).2 (Units.ext (by
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        rw [pow_mul, h, ← map_pow, hK a ha, map_one])), a, Units.ext (by simpa using h.symm)⟩
    obtain ⟨j, hj⟩ := hg ⟨_, hT⟩
    exact ⟨j, by simpa using congrArg (fun z : T => ((z : Ωˣ) : Ω)) hj⟩
  obtain ⟨u0, hu0⟩ : ∃ u0 : galOf F K Ω, ∀ u : galOf F K Ω,
      ∃ k : ℤ, u.1 ξ / ξ = (u0.1 ξ / ξ) ^ k := by
    have h1 : ∀ u : galOf F K Ω, (u.1 ξ / ξ) ^ n = 1 := fun u => by
      rw [div_pow, ← map_pow, hb, u.2 b, ← hb, div_self (pow_ne_zero _ ξ.ne_zero)]
    have h2 : ∀ u v : galOf F K Ω, u.1 (v.1 ξ / ξ) = v.1 ξ / ξ := fun u v => by
      obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one (h1 v)
      rw [← hi, map_pow, u.2 ζ]
    have h3 : ∀ u : galOf F K Ω, u.1 ξ ≠ 0 := fun u => (map_ne_zero _).2 ξ.ne_zero
    let f : galOf F K Ω →* Ωˣ :=
      MonoidHom.mk' (fun u => Units.mk0 (u.1 ξ / ξ) (div_ne_zero (h3 u) ξ.ne_zero)) fun u v => by
        apply Units.ext
        have := h2 u v
        rw [map_div₀, div_eq_iff (h3 u)] at this
        simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, this]; ring
    have hle : f.range ≤ rootsOfUnity n Ω := by
      rintro _ ⟨u, rfl⟩; exact (mem_rootsOfUnity _ _).2 (Units.ext (by simpa [f] using h1 u))
    haveI : Finite f.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
    obtain ⟨⟨_, u0, rfl⟩, hg⟩ := (isCyclic_subgroup_units f.range).exists_generator
    refine ⟨u0, fun u => ?_⟩
    obtain ⟨k, hk⟩ := hg ⟨f u, u, rfl⟩
    exact ⟨k, by simpa [f] using (congrArg (fun z : f.range => ((z : Ωˣ) : Ω)) hk).symm⟩
  have hval : ∀ (φ : galOf F K Ω → ZMod n) (j : ℤ),
      IsRad (algebraMap K Ω ζ) _ φ ((ξ : Ω) ^ j) →
      ∀ u, algebraMap K Ω ζ ^ (φ u).val = (u.1 ξ / ξ) ^ j := fun φ j hr u => by
    rw [div_zpow, ← map_zpow₀, hr.2, mul_div_cancel_right₀ _ hr.1]
  let e : {φ : galOf F K Ω → ZMod n // φ ∈ EqHom N _ (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) _ φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} →
      (scalRep (ZMod n) ψ).invariants := fun φ => ⟨φ.1 u0, fun g => by
    obtain ⟨hφ, β, -, hr, -, hβ⟩ := φ.2
    let u' : galOf F K Ω := ⟨g * u0.1 * g⁻¹, (galOf_normal F K Ω).conj_mem _ u0.2 g⟩
    have h1 : φ.1 u' = scalRep (ZMod n) ψ g (φ.1 u0) :=
      (Submodule.mem_iInf _).1 hφ.2 g u0 u' fun x => by
        show g (u0.1 (g.symm (g x))) = g (u0.1 x); rw [g.symm_apply_apply]
    rw [← h1]; apply hinj
    have h2 : u'.1 β = u0.1 β := conj_root_eq g u0.1 β hβ
    rw [hr.2, hr.2] at h2; exact mul_right_cancel₀ hr.1 h2⟩
  have he : Function.Injective e := by
    rintro ⟨φ, hφ, β, a, hr, ha, hβ⟩ ⟨φ', hφ', β', a', hr', ha', hβ'⟩ h
    have h0 : φ u0 = φ' u0 := congrArg Subtype.val h
    obtain ⟨j, rfl⟩ := hξ β a ha hβ
    obtain ⟨j', rfl⟩ := hξ β' a' ha' hβ'
    refine Subtype.ext (funext fun u => hinj _ _ ?_)
    obtain ⟨k, hk⟩ := hu0 u
    show algebraMap K Ω ζ ^ (φ u).val = algebraMap K Ω ζ ^ (φ' u).val
    rw [hval φ j hr, hval φ' j' hr', hk, ← zpow_mul, ← zpow_mul, mul_comm k, mul_comm k,
      zpow_mul, zpow_mul, ← hval φ j hr, ← hval φ' j' hr', h0]
  exact ⟨Nat.card_le_card_of_injective e he, Finite.of_injective e he⟩

private theorem reflTw_empty {K : Type} [Field K] [NumberField K] {c d : ClassGroup (𝓞 K)}
    (h : (QuotientGroup.mk c : ClS (∅ : Set (HeightOneSpectrum (𝓞 K)))) = QuotientGroup.mk d) :
    c = d := by
  rw [QuotientGroup.eq] at h
  have e : clSub (∅ : Set (HeightOneSpectrum (𝓞 K))) = ⊥ := by simp [clSub]
  rw [e, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.1 h

private theorem reflTw_pow {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) {a : Kˣ}
    (ha : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n) (m : ℕ) :
    radCl n (a ^ m) = radCl n a ^ m := by
  induction m with
  | zero => simp [radCl, ordv_one]
  | succ m ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact reflTw_empty ((radClMul K ∅ n hn).1 _ (pow_mem ha m) _ ha)

private theorem reflTw_key {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {K : Type} [Field K] [NumberField K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {φ : galOf F K Ω → ZMod n} {β : Ω} {a : Kˣ}
    (hβ : IsRad (algebraMap K Ω ζ) (galOf F K Ω) φ β) (ha : β ^ n = algebraMap K Ω a)
    {τ : K ≃+* K} {σ : Ω ≃+* Ω} (hl : IsLift τ σ) (k s : ZMod n)
    (hk : σ (algebraMap K Ω ζ) = algebraMap K Ω ζ ^ k.val)
    (hs : ∀ u u' : galOf F K Ω, (∀ x, u'.1 (σ x) = σ (u.1 x)) → φ u = s * φ u') :
    ∃ c : Kˣ, Units.map τ.toMonoidHom a = a ^ (k * s).val * c ^ n := by
  have hz : algebraMap K Ω ζ ^ n = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h1 : IsRad (algebraMap K Ω ζ) (galOf F K Ω) (fun u => k * s * φ u) (σ β) := by
    refine radConj F Ω _ n _ β σ k φ _ hz hk hβ fun u' => ?_
    have hK : ∀ x : K, ((σ.trans u'.1.toRingEquiv).trans σ.symm) (algebraMap K Ω x) =
        algebraMap K Ω x := fun x => by
      show σ.symm (u'.1 (σ (algebraMap K Ω x))) = _
      rw [hl x, u'.2, ← hl x, σ.symm_apply_apply]
    let u : galOf F K Ω := ⟨AlgEquiv.ofRingEquiv (f := (σ.trans u'.1.toRingEquiv).trans σ.symm)
      fun x => by rw [IsScalarTower.algebraMap_apply F K Ω, hK], hK⟩
    have hu : ∀ x, u'.1 (σ x) = σ (u.1 x) := fun x => (σ.apply_symm_apply _).symm
    exact ⟨u, hu, by rw [hs u u' hu, mul_assoc]⟩
  have h2 : IsRad (algebraMap K Ω ζ) (galOf F K Ω) (fun u => k * s * φ u) (β ^ (k * s).val) :=
    ⟨pow_ne_zero _ hβ.1, fun u => by
      change u.1 (β ^ (k * s).val) = algebraMap K Ω ζ ^ ((k * s) * φ u).val * β ^ (k * s).val
      rw [map_pow, hβ.2 u, mul_pow, ← pow_mul, ZMod.val_mul (k * s) (φ u),
        ← pow_eq_pow_mod _ hz, mul_comm (k * s).val]⟩
  obtain ⟨c, hc⟩ := (radXDual F Ω K _ n 1 ζ rfl hζ).2 _ _ _ h2 h1
  refine ⟨c, Units.ext ((algebraMap K Ω).injective ?_)⟩
  show algebraMap K Ω (τ a) = _
  rw [← hl, ← ha, map_pow, hc, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_mul, map_pow, map_pow, ← ha]; ring

theorem reflTw (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K]
    (χ ψ : G F Ω →* (ZMod n)ˣ) (φ : U → ZMod n) (β : Ω) (a : Kˣ) (hU : U = galOf F K Ω)
    (hζ : IsPrimitiveRoot ζ n)
    (hχ : ∀ g : G F Ω, g (algebraMap K Ω ζ) = (algebraMap K Ω ζ) ^ (χ g : ZMod n).val)
    (hφ : φ ∈ EqHom N U (scalRep (ZMod n) ψ)) (hβ : IsRad (algebraMap K Ω ζ) U φ β)
    (ha : β ^ n = algebraMap K Ω a) :
    radCl n a ∈ ClTw K n (χ * ψ⁻¹) ∧
    ∀ (τ : K ≃+* K) (σ : Ω ≃+* Ω), IsLift τ σ → τ ζ = ζ⁻¹ →
      φ ∈ conjCond U σ ((1 : ZMod n) • (LinearMap.id : ZMod n →ₗ[ZMod n] ZMod n)) →
      a * Units.map τ.toMonoidHom a ∈ powK K n ∧ radCl n a ∈ ClMinus τ := by
  subst hU
  have hn : n ≠ 0 := NeZero.ne n
  have hS : a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n := by
    obtain ⟨β₀, a₀, h₀, ha₀, hS₀⟩ := (radXDual F Ω K _ n N ζ rfl hζ).1 φ hφ.1
    obtain ⟨c, hc⟩ := (radXDual F Ω K _ n N ζ rfl hζ).2 _ _ _ h₀ hβ
    have e : a = a₀ * c ^ n := Units.ext ((algebraMap K Ω).injective (by
      rw [← ha, hc, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, ← ha₀]; ring))
    rw [e]; exact mul_mem hS₀ fun v _ => ⟨ordv v c, by simp [ordv]⟩
  have h1 : radCl n a ^ n = 1 := reflTw_empty (by
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_one]; exact (radClMul K ∅ n hn).2.1 _ hS)
  have hmap : ∀ (τ : K ≃+* K) (m : ℕ) (c : Kˣ), Units.map τ.toMonoidHom a = a ^ m * c ^ n →
      clMap τ (radCl n a) = radCl n a ^ m := fun τ m c h => by
    rw [radClMap, h, (radClMul K ∅ n hn).2.2, reflTw_pow hn hS]
  refine ⟨⟨h1, fun g τ hl => ?_⟩, fun τ σ hl hτ hc => ?_⟩
  · have hg : φ ∈ conjCond (galOf F K Ω) g.toRingEquiv (scalRep (ZMod n) ψ g) :=
      (Submodule.mem_iInf _).1 hφ.2 g
    obtain ⟨c, hc⟩ := reflTw_key hζ hβ ha hl (χ g) ((ψ g)⁻¹ : (ZMod n)ˣ) (hχ g) fun u u' h => by
      rw [hg u u' h, scalRep_apply]; simp
    exact hmap τ _ c (by simpa using hc)
  · obtain ⟨j, hj⟩ : n ∣ (-1 : ZMod n).val + 1 := by rw [← ZMod.natCast_eq_zero_iff]; simp
    have hk : σ (algebraMap K Ω ζ) = algebraMap K Ω ζ ^ (-1 : ZMod n).val := by
      rw [hl, hτ, ← map_pow]; congr 1
      exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ, hj, pow_mul, hζ.pow_eq_one, one_pow])
    obtain ⟨c, hc⟩ := reflTw_key hζ hβ ha hl (-1) 1 hk fun u u' h => by rw [hc u u' h]; simp
    rw [mul_one] at hc
    refine ⟨⟨a ^ j * c, ?_⟩, ?_⟩
    · rw [hc, ← mul_assoc, ← pow_succ', hj, powMonoidHom_apply, mul_pow, ← pow_mul, mul_comm j]
    · show clMap τ (radCl n a) * radCl n a = 1
      rw [hmap τ _ c hc, ← pow_succ, hj, pow_mul, h1, one_pow]

theorem unitMinus (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (a : Kˣ)
    (ha : a ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K)
    (hc : a * Units.map (cE K).toMonoidHom a ∈ powK K n) :
    a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK K n ∧ (Odd n → a ∈ CommGroup.torsion Kˣ ⊔ powK K n) := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (a : K)
    (fun v => (ha v (Set.notMem_empty v)).le)
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((a⁻¹ : Kˣ) : K)
    (fun v => ((Subgroup.inv_mem _ ha) v (Set.notMem_empty v)).le)
  have hxy : x * y = 1 := IsFractionRing.injective (𝓞 K) K (by rw [map_mul, hx, hy, map_one, Units.mul_inv])
  let u : (𝓞 K)ˣ := Units.mkOfMulEqOne x y hxy
  let f : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hu : f u = a := Units.ext hx
  have hcu : f (IsCMField.unitsComplexConj K u) = Units.map (cE K).toMonoidHom a := by
    rw [← hu]; exact Units.ext rfl
  have htor : a * (Units.map (cE K).toMonoidHom a)⁻¹ ∈ CommGroup.torsion Kˣ := by
    have hfin : IsOfFinOrder (u * (IsCMField.unitsComplexConj K u)⁻¹) :=
      (IsCMField.unitsMulComplexConjInv K u).2
    have := f.isOfFinOrder hfin
    rw [map_mul, map_inv, hu, hcu] at this; exact this
  have h2 : a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK K n := by
    have e : a ^ 2 = (a * (Units.map (cE K).toMonoidHom a)⁻¹) * (a * Units.map (cE K).toMonoidHom a) := by
      rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]
    rw [e]; exact Subgroup.mul_mem_sup htor hc
  refine ⟨h2, fun ⟨k, hk⟩ => ?_⟩
  subst hk
  have hn : a ^ (2 * k + 1) ∈ CommGroup.torsion Kˣ ⊔ powK K (2 * k + 1) :=
    Subgroup.mem_sup_right ⟨a, rfl⟩
  rw [pow_succ, pow_mul] at hn
  exact (Subgroup.mul_mem_cancel_left _ (Subgroup.pow_mem _ h2 k)).1 hn

/-- **Kummer Reflection Theorem (`reflect`)**: bounds the cardinality of the `+1`-eigenspace
`EqEig N U (scalRep (ZMod n) ψ) σ 1` by the product of `H⁰(ψ)` and the reflected `-1`-eigenspace
of the `n`-torsion of `Cl(K)` twisted by `χ * ψ⁻¹`. -/
theorem reflect (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K]
    [IsCMField K] (χ ψ : G F Ω →* (ZMod n)ˣ) (σ : Ω ≃+* Ω) (hU : U = galOf F K Ω) (hn : Odd n)
    (hζ : IsPrimitiveRoot ζ n)
    (hχ : ∀ g : G F Ω, g (algebraMap K Ω ζ) = (algebraMap K Ω ζ) ^ (χ g : ZMod n).val)
    (hσ : IsConjOm σ) :
    Nat.card (EqEig N U (scalRep (ZMod n) ψ) σ 1) ≤
      Nat.card (scalRep (ZMod n) ψ).invariants *
        Nat.card (ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K))) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  obtain ⟨κ, hκ, -⟩ := reflMap F Ω K U n N ζ hU hζ
  obtain ⟨hR, hfin⟩ := reflRoot F Ω K U n N ζ ψ hU hζ
  have hX := (radXDual F Ω K U n N ζ hU hζ).1
  have hle : EqEig N U (scalRep (ZMod n) ψ) σ 1 ≤ XDual N U (ZMod n) (ZMod n) := fun _ h => h.1.1
  let f : EqEig N U (scalRep (ZMod n) ψ) σ 1 →+ Additive (ClassGroup (𝓞 K)) :=
    κ.comp (Submodule.inclusion hle).toAddMonoidHom
  have hconj : cE K ζ = ζ⁻¹ := by
    obtain ⟨j⟩ : Nonempty (K →+* ℂ) := inferInstance
    apply j.injective
    have h1 : ‖j ζ‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hn0
    have h2 : j (cE K ζ) = starRingEnd ℂ (j ζ) := IsCMField.complexEmbedding_complexConj K j ζ
    rw [h2, map_inv₀]
    exact eq_inv_of_mul_eq_one_left (by rw [Complex.conj_mul', h1]; simp)
  have key : ∀ φ : EqEig N U (scalRep (ZMod n) ψ) σ 1, ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) U φ.1 β ∧ β ^ n = algebraMap K Ω a ∧
      a ∈ SelK (∅ : Set (HeightOneSpectrum (𝓞 K))) n ∧ f φ = Additive.ofMul (radCl n a) ∧
      a * Units.map (cE K).toMonoidHom a ∈ powK K n ∧
      radCl n a ∈ ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) := fun φ => by
    obtain ⟨β, a, h1, h2, h3⟩ := hX φ.1 (hle φ.2)
    obtain ⟨h4, h5⟩ := reflTw F Ω K U n N ζ χ ψ φ.1 β a hU hζ hχ φ.2.1 h1 h2
    obtain ⟨h6, h7⟩ := h5 (cE K) σ hσ.isLift hconj φ.2.2
    exact ⟨β, a, h1, h2, h3, hκ ⟨φ.1, hle φ.2⟩ β a h1 h2, h6, h4, h7⟩
  have hker : ∀ φ : f.ker, ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ.1.1 β ∧
      β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β := fun φ => by
    obtain ⟨β, a, h1, h2, h3, h4, h5, -⟩ := key φ.1
    have h0 : radCl n a = 1 := Additive.ofMul.injective (h4.symm.trans φ.2)
    have h2' := (radClKer K ∅ n hn0 a h3).1 (h0 ▸ one_mem _)
    obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 h2'
    have hb : powMonoidHom n b * Units.map (cE K).toMonoidHom (powMonoidHom n b) ∈ powK K n :=
      ⟨b * Units.map (cE K).toMonoidHom b, by simp only [powMonoidHom_apply, mul_pow, map_pow]⟩
    have hu' : u * Units.map (cE K).toMonoidHom u ∈ powK K n := by
      rw [map_mul, mul_mul_mul_comm] at h5
      exact (Subgroup.mul_mem_cancel_right _ hb).1 h5
    obtain ⟨t, ht, _, ⟨d, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 ((unitMinus K n u hu hu').2 hn)
    have hdb : algebraMap K Ω (d * b : Kˣ) ≠ 0 := (map_ne_zero _).2 (d * b).ne_zero
    have hp : (β / algebraMap K Ω (d * b : Kˣ)) ^ n = algebraMap K Ω t := by
      rw [div_pow, h2]
      have haeq : (t * powMonoidHom n d * powMonoidHom n b : Kˣ) = t * (d * b) ^ n := by
        simp [mul_pow, mul_assoc]
      rw [haeq, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
        mul_div_cancel_right₀ _ (pow_ne_zero _ hdb)]
    refine ⟨β / algebraMap K Ω (d * b : Kˣ), t, ⟨div_ne_zero h1.1 hdb, fun u => ?_⟩, hp, ?_⟩
    · have hu : u.1 ∈ galOf F K Ω := hU ▸ u.2
      rw [map_div₀, h1.2 u, hu ((d * b : Kˣ) : K), mul_div_assoc]
    · exact IsOfFinOrder.of_pow
        (hp ▸ ((algebraMap K Ω).toMonoidHom.comp (Units.coeHom K)).isOfFinOrder ht) hn0
  have hran : ∀ c : f.range, Additive.toMul c.1 ∈ ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) := by
    rintro ⟨c, φ, rfl⟩
    obtain ⟨β, a, -, -, -, h4, -, h6⟩ := key φ
    show Additive.toMul (f φ) ∈ _; rw [h4]; exact h6
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  refine (Nat.mul_le_mul
    (Nat.card_le_card_of_injective
      (fun φ : f.ker => (⟨φ.1.1, φ.1.2.1, hker φ⟩ :
        {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ),
          IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β}))
      (fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))))
    (Nat.card_le_card_of_injective
      (fun c : f.range => (⟨Additive.toMul c.1, hran c⟩ :
        (ClTw K n (χ * ψ⁻¹) ⊓ ClMinus (cE K) : Subgroup (ClassGroup (𝓞 K)))))
      (fun _ _ h => Subtype.ext (Additive.toMul.injective (Subtype.mk.inj h))))).trans
    (Nat.mul_le_mul_right _ hR)

end RadicalAndReflection

/-! ## Section 4: Decomposition Groups, Cyclotomic Towers & Equivariant Extension (`DecGen`, `DecCompact`, `LevCompact`, `HomExt`, `XdualExt`, `CycZConjGal`, `DinfNil`, `FnCycMap`, `GalOfCyc`, `IsCMOfConj`) -/

section DecAndTower

private theorem frob_pow_fin (k L : Type) [Field k] [Finite k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] (τ : L →ₐ[k] L) (S : Finset L) :
    ∃ i : ℕ, ∀ x ∈ S, τ x = x ^ Nat.card k ^ i := by
  classical
  haveI := Fintype.ofFinite k
  let E := IntermediateField.adjoin k (S : Set L)
  haveI : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI : Finite E := Module.finite_of_finite k
  haveI : Normal k E := inferInstance
  let τE : E →ₐ[k] E := τ.restrictNormal E
  let e : E ≃ₐ[k] E := AlgEquiv.ofBijective τE (Finite.injective_iff_bijective.1 τE.toRingHom.injective)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).2 e
  refine ⟨n, fun x hx => ?_⟩
  have hxE : x ∈ E := IntermediateField.subset_adjoin k _ hx
  have h1 := τ.restrictNormal_commutes E ⟨x, hxE⟩
  have h3 : e ⟨x, hxE⟩ = ⟨x, hxE⟩ ^ Fintype.card k ^ (n : ℕ) := by
    rw [← hn, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [Nat.card_eq_fintype_card]
  calc τ x = algebraMap E L (τE ⟨x, hxE⟩) := h1.symm
    _ = x ^ Fintype.card k ^ (n : ℕ) := by change algebraMap E L (e ⟨x, hxE⟩) = _; rw [h3, map_pow]; rfl

private theorem alg_residue {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) (k : Type)
    [Field k] [Algebra k (IsLocalRing.ResidueField A)] (x : A) (hx : IsAlgebraic ℤ (x : Ω)) :
    IsAlgebraic k (IsLocalRing.residue A x) := by
  obtain ⟨p, hp0, hpx⟩ := hx
  have hq : p.primPart.IsPrimitive := p.isPrimitive_primPart
  have hqx : Polynomial.aeval x p.primPart = 0 := by
    have h1 : Polynomial.aeval (x : Ω) p = (p.content : Ω) * Polynomial.aeval (x : Ω) p.primPart := by
      conv_lhs => rw [p.eq_C_content_mul_primPart]; simp
    have hc : (p.content : Ω) ≠ 0 := by exact_mod_cast (Polynomial.content_eq_zero_iff.not.2 hp0)
    rw [hpx] at h1
    have h2 : Polynomial.aeval (x : Ω) p.primPart = 0 := (mul_eq_zero.1 h1.symm).resolve_left hc
    apply Subtype.ext
    change algebraMap A Ω (Polynomial.aeval x p.primPart) = 0
    rw [← Polynomial.aeval_algebraMap_apply Ω x p.primPart]
    exact h2
  refine ⟨p.primPart.map (algebraMap ℤ k), fun h => ?_, ?_⟩
  · rcases CharP.char_is_prime_or_zero k (ringChar k) with hr | hr
    · have hdvd : Polynomial.C ((ringChar k : ℕ) : ℤ) ∣ p.primPart := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have := congrArg (fun P => Polynomial.coeff P i) h
        simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
        exact (CharP.intCast_eq_zero_iff k (ringChar k) _).1 this
      have hu := hq _ hdvd
      rw [Int.isUnit_iff] at hu; have := hr.two_le; omega
    · haveI : CharZero k := (CharP.ringChar_zero_iff_CharZero k).1 hr
      exact hq.ne_zero (Polynomial.map_injective (algebraMap ℤ k) (RingHom.injective_int _)
        (by rw [h, Polynomial.map_zero]))
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap k (IsLocalRing.ResidueField A)).comp (algebraMap ℤ k) =
        algebraMap ℤ (IsLocalRing.ResidueField A) from RingHom.ext_int _ _, ← Polynomial.aeval_def]
    have := Polynomial.aeval_algebraMap_apply (IsLocalRing.ResidueField A) x p.primPart
    rw [IsLocalRing.ResidueField.algebraMap_eq] at this
    rw [this, hqx, map_zero]

private theorem frob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : G F Ω} (hφ : IsFrob A q φ) (n : ℕ) :
    IsFrob A (q ^ n) (φ ^ n) := by
  have hD : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨pow_mem hD (n + 1), fun x hx => ?_⟩
    have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
    have hyA : (φ ^ n) x ∈ A := (apply_mem_iff_of_mem_Dec (pow_mem hD n) x).2 hxA
    have e1 : A.valuation (φ ((φ ^ n) x) - ((φ ^ n) x) ^ q) < 1 :=
      hφ.2 _ ((A.valuation_le_one_iff _).2 hyA)
    have e2 : A.valuation ((φ ^ n) x - x ^ q ^ n) < 1 := ih.2 x hx
    have e3 : A.valuation (((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q) < 1 := by
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (⟨(φ ^ n) x, hyA⟩ : A) ⟨x ^ q ^ n, pow_mem hxA _⟩ q
      have h4 : ((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q = ((φ ^ n) x - x ^ q ^ n) * c := by
        have := congrArg (fun z : A => (z : Ω)) hc; push_cast at this; exact this
      rw [h4, map_mul]
      calc _ ≤ A.valuation ((φ ^ n) x - x ^ q ^ n) * 1 := by gcongr; exact A.valuation_le_one c
        _ < 1 := by rw [mul_one]; exact e2
    have h5 : (φ ^ (n + 1)) x - x ^ q ^ (n + 1) =
        (φ ((φ ^ n) x) - ((φ ^ n) x) ^ q) + (((φ ^ n) x) ^ q - (x ^ q ^ n) ^ q) := by
      rw [pow_succ' φ n, AlgEquiv.mul_apply, pow_succ q n, pow_mul]; ring
    rw [h5]
    exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt e1 e3)

private theorem dec_pow_fin {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    (hA : IsPlaceOver A v) {g : G K Ω} (hg : g ∈ Dec (F := K) A) (S : Finset A) :
    ∃ i : ℕ, ∀ x ∈ S, A.valuation (g x - (x : Ω) ^ normV v ^ i) < 1 := by
  classical
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hint : ∀ a : 𝓞 K, ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)) a ∈ A := fun a =>
    mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω))
  let f0 : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let f1 : 𝓞 K →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp f0
  have hker : ∀ a ∈ v.asIdeal, f1 a = 0 := fun a ha => by
    show IsLocalRing.residue A (f0 a) = 0
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (hA a).2 ha
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) :=
    (Ideal.Quotient.lift v.asIdeal f1 hker).toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  haveI : Algebra.IsAlgebraic (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact alg_residue A _ x ((IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic (x : Ω)))⟩
  let gD : ValuationSubring.decompositionSubgroup K A := ⟨g, hg⟩
  have hfix : ∀ a : 𝓞 K, gD • f0 a = f0 a := fun a => Subtype.ext (g.commutes _)
  let τ : IsLocalRing.ResidueField A →ₐ[𝓞 K ⧸ v.asIdeal] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) gD with
      commutes' := fun c => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        show gD • (Ideal.Quotient.lift v.asIdeal f1 hker (Ideal.Quotient.mk _ a)) = _
        rw [Ideal.Quotient.lift_mk]
        show gD • IsLocalRing.residue A (f0 a) = IsLocalRing.residue A (f0 a)
        rw [← IsLocalRing.ResidueField.residue_smul (ValuationSubring.decompositionSubgroup K A) gD (f0 a), hfix] }
  obtain ⟨i, hi⟩ := frob_pow_fin (𝓞 K ⧸ v.asIdeal) (IsLocalRing.ResidueField A) τ
    (S.image (IsLocalRing.residue A))
  refine ⟨i, fun x hx => ?_⟩
  have h1 : gD • IsLocalRing.residue A x = IsLocalRing.residue A x ^ normV v ^ i :=
    hi _ (Finset.mem_image_of_mem _ hx)
  have h2 : IsLocalRing.residue A (gD • x - x ^ normV v ^ i) = 0 := by
    rw [map_sub, IsLocalRing.ResidueField.residue_smul, map_pow, h1, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
  exact h2

theorem decGen (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω) (H : Subgroup (G K Ω))
    (hA : IsPlaceOver A v) (hσ : IsFrob (F := K) A (normV v) σ) (hHo : IsOpen (H : Set (G K Ω)))
    (hI : Ine (F := K) A ≤ H) (hσH : σ ∈ H) : Dec (F := K) A ≤ H := by
  classical
  intro g hg
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hHc : IsClosed (H : Set (G K Ω)) := Subgroup.isClosed_of_isOpen H hHo
  let Cl : Set (G K Ω) := closure (Set.range fun i : ℕ => σ ^ i)
  have hClH : Cl ⊆ H := closure_minimal (by rintro _ ⟨i, rfl⟩; exact H.pow_mem hσH i) hHc
  have hClD : Cl ⊆ Dec (F := K) A :=
    closure_minimal (by rintro _ ⟨i, rfl⟩; exact (Dec (F := K) A).pow_mem hσ.1 i) (isClosed_Dec A)
  let C : Finset A → Set (G K Ω) := fun S => Cl ∩ {τ | ∀ x ∈ S, A.valuation (g x - τ x) < 1}
  have hCcl : ∀ S, IsClosed (C S) := fun S => by
    refine isClosed_closure.inter ?_
    rw [show {τ : G K Ω | ∀ x ∈ S, A.valuation (g x - τ x) < 1} =
        ⋂ x ∈ S, {τ : G K Ω | A.valuation (g x - τ x) < 1} by ext; simp]
    exact isClosed_biInter fun x _ => isClosed_setOf_apply (F := K) (x : Ω) (fun y => A.valuation (g x - y) < 1)
  have hCne : ∀ S, (C S).Nonempty := fun S => by
    obtain ⟨i, hi⟩ := dec_pow_fin hA hg S
    refine ⟨σ ^ i, subset_closure ⟨i, rfl⟩, fun x hx => ?_⟩
    have h1 := hi x hx
    have h2 := (frob_pow hσ i).2 x (A.valuation_le_one x)
    rw [show g x - (σ ^ i) x = (g x - (x : Ω) ^ normV v ^ i) - ((σ ^ i) x - (x : Ω) ^ normV v ^ i) by ring]
    exact lt_of_le_of_lt (A.valuation.map_sub _ _) (max_lt h1 h2)
  have hdir : Directed (fun s t => s ⊇ t) C := fun S T =>
    ⟨S ∪ T, fun _ ⟨h1, h2⟩ => ⟨h1, fun x hx => h2 x (Finset.mem_union_left _ hx)⟩,
      fun _ ⟨h1, h2⟩ => ⟨h1, fun x hx => h2 x (Finset.mem_union_right _ hx)⟩⟩
  obtain ⟨τ, hτ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCne
    (fun S => (hCcl S).isCompact) hCcl
  rw [Set.mem_iInter] at hτ
  have hτCl : τ ∈ Cl := (hτ ∅).1
  have hτD := hClD hτCl
  have hτx : ∀ x : A, A.valuation (g x - τ x) < 1 := fun x => (hτ {x}).2 x (Finset.mem_singleton_self x)
  have hι : τ⁻¹ * g ∈ Ine (F := K) A := by
    refine ⟨(Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hτD) hg, fun x hx => ?_⟩
    have e : (τ⁻¹ * g) x - x = τ⁻¹ (g x - τ x) := by
      rw [AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    rw [e, valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hτD)]
    exact hτx ⟨x, (A.valuation_le_one_iff x).1 hx⟩
  rw [show g = τ * (τ⁻¹ * g) by group]
  exact H.mul_mem (hClH hτCl) (hI hι)

private theorem compact_union_places (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) (hN : N ≠ 0) (H : ValuationSubring Ω → Set (G F Ω))
    (hcl : ∀ A, IsClosed (H A))
    (hconj : ∀ (A : ValuationSubring Ω) (g σ : G F Ω), σ ∈ H (g • A) → g⁻¹ * σ * g ∈ H A) :
    IsCompact {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ H A} := by
  obtain ⟨-, h2, h3, h4⟩ := placeDict F Ω
  have hfin : (Above F N).Finite := finite_above_of_ne_zero F N hN
  let T : ValuationSubring Ω → Set (G F Ω) := fun A =>
    (fun p : G F Ω × G F Ω => p.1 * p.2 * p.1⁻¹) '' (Set.univ ×ˢ H A)
  have hT : ∀ A, IsCompact (T A) := fun A =>
    (isCompact_univ.prod (hcl A).isCompact).image (by fun_prop)
  classical
  let P : HeightOneSpectrum (𝓞 F) → Set (G F Ω) := fun v =>
    if h : ∃ A : ValuationSubring Ω, IsPlaceOver A v then T h.choose else ∅
  have hP : ∀ v, IsCompact (P v) := fun v => by simp only [P]; split_ifs; exacts [hT _, isCompact_empty]
  have e : {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ H A} =
      ⋃ v ∈ Above F N, P v := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨A, hA, hσ⟩
      obtain ⟨v, hv⟩ := h2 A (h3 A N hN hA)
      refine ⟨v, (h4 A v N hv).1 hA, ?_⟩
      have h : ∃ A : ValuationSubring Ω, IsPlaceOver A v := ⟨A, hv⟩
      simp only [P, dif_pos h]
      obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) h.choose_spec hv
      exact ⟨(g, g⁻¹ * σ * g), ⟨trivial, hconj _ g σ (hg ▸ hσ)⟩, by simp [mul_assoc]⟩
    · rintro ⟨v, hv, hσ⟩
      simp only [P] at hσ
      split_ifs at hσ with h
      · obtain ⟨⟨g, τ⟩, ⟨-, hτ⟩, rfl⟩ := hσ
        refine ⟨g • h.choose, ?_, ?_⟩
        · rw [smul_valuation_lt_one_iff, map_natCast]
          exact (h4 _ v N h.choose_spec).2 hv
        · have := hconj (g • h.choose) g⁻¹ τ (by rw [inv_smul_smul]; exact hτ)
          rwa [inv_inv] at this
      · exact hσ.elim
  rw [e]
  exact hfin.isCompact_biUnion fun v _ => hP v

theorem decCompact (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) (hN : N ≠ 0) :
    IsCompact {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Dec (F := F) A} ∧
    IsCompact {g : G F Ω | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Ine (F := F) A} :=
  ⟨compact_union_places F Ω N hN (fun A => (Dec (F := F) A : Set (G F Ω))) (fun A => isClosed_Dec A)
      fun _ _ _ h => conj_mem_Dec h,
    compact_union_places F Ω N hN (fun A => (Ine (F := F) A : Set (G F Ω))) (fun A => isClosed_Ine A)
      fun _ _ _ h => conj_mem_Ine' h⟩

private theorem princ_isClosed_val (l : ℕ) [Fact l.Prime] (a : ℕ) :
    IsClosed ((princ l a : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_princ a)

private theorem eq_one_of_mem_all_princ (l : ℕ) [Fact l.Prime] (x : ℤ_[l]ˣ)
    (hx : ∀ a, x ∈ princ l a) : x = 1 := by
  ext
  refine PadicInt.ext_of_toZModPow.mp fun a => ?_
  have h := hx a
  simp only [princ, redPow, MonoidHom.mem_ker, Units.ext_iff] at h
  simpa using h

private theorem closed_levU {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] {U : Subgroup (G F Ω)}
    (hU : IsClosed (U : Set (G F Ω))) (m : ℕ) : IsClosed (levU l U m : Set (G F Ω)) :=
  hU.inter ((princ_isClosed_val l m).preimage (continuous_cycZ F Ω l))

theorem levCompact (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (n : ℕ) (T : Type)
    [TopologicalSpace T] [CompactSpace T] (M : Type) [Zero M] (ψ : T × levU l U n → M)
    (hU : IsClosed (U : Set (G F Ω))) (hψ : IsLocallyConstant ψ)
    (h0 : ∀ t (u : levU l U n), u.1 ∈ cycU l U → ψ (t, u) = 0) :
    ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), u.1 ∈ levU l U m → ψ (t, u) = 0 := by
  haveI : CompactSpace (levU l U n) := isCompact_iff_compactSpace.mp (closed_levU l hU n).isCompact
  let K : Set (T × levU l U n) := {p | ψ p ≠ 0}
  have hKc : IsClosed K := (hψ.isOpen_fiber 0).isClosed_compl
  let t : ℕ → Set (T × levU l U n) := fun m => {p | (p.2 : G F Ω) ∈ levU l U m}
  have htc : ∀ m, IsClosed (t m) := fun m =>
    (closed_levU l hU m).preimage (continuous_subtype_val.comp continuous_snd)
  have hst : K ∩ ⋂ m, t m = ∅ := by
    ext ⟨s, u⟩
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp hall
    exact hp (h0 s u ⟨u.2.1, eq_one_of_mem_all_princ l _ fun a => (hall a).2⟩)
  obtain ⟨v, hv⟩ := hKc.isCompact.elim_finite_subfamily_closed t htc hst
  refine ⟨max n (v.sup id), le_max_left _ _, fun s u hu => ?_⟩
  by_contra hne
  have hmem : (s, u) ∈ K ∩ ⋂ i ∈ v, t i := ⟨hne, Set.mem_iInter₂.2 fun i hi =>
    ⟨hu.1, princ_anti ((Finset.le_sup (f := id) hi).trans (le_max_right _ _)) hu.2⟩⟩
  rw [hv] at hmem; exact hmem

theorem homExt (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (M : Type) [AddCommGroup M] (φ : cycU l U → M)
    (hU : IsClosed (U : Set (G F Ω))) (hφ : IsLocallyConstant φ)
    (hmul : ∀ a b, φ (a * b) = φ a + φ b) :
    ∃ (n : ℕ) (ψ : levU l U n → M), IsLocallyConstant ψ ∧ (∀ a b, ψ (a * b) = ψ a + ψ b) ∧
      ∀ u : cycU l U, ψ ⟨u.1, cycU_le_levU l U n u.2⟩ = φ u := by
  classical
  have hφ1 : φ 1 = 0 := by simpa using hmul 1 1
  have hlev_anti : ∀ n m : ℕ, n ≤ m → (levU l U m : Set (G F Ω)) ⊆ levU l U n := fun _ _ hnm _ hx =>
    ⟨hx.1, princ_anti hnm hx.2⟩
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber (φ 1))
  have h1O : (1 : G F Ω) ∈ O := by
    have h : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; rfl
    exact h
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω O).mp (hOo.mem_nhds h1O)
  haveI := hEfin; haveI := hEnorm
  have hNnorm : (E.fixingSubgroup : Subgroup (G F Ω)).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]; exact MonoidHom.normal_ker _
  have hNopen : IsOpen ((E.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := E.fixingSubgroup_isOpen
  have hNker : ∀ c : cycU l U, (c : G F Ω) ∈ E.fixingSubgroup → φ c = 0 := fun c hc => by
    have h : c ∈ Subtype.val ⁻¹' O := hEsub hc
    rw [hOeq] at h; rw [← hφ1]; exact h
  have hwd : ∀ (c c' : cycU l U) (w w' : G F Ω), w ∈ E.fixingSubgroup → w' ∈ E.fixingSubgroup →
      (c : G F Ω) * w = c' * w' → φ c = φ c' := fun c c' w w' hw hw' h => by
    have hmem : ((c'⁻¹ * c : cycU l U) : G F Ω) ∈ E.fixingSubgroup := by
      rw [show ((c'⁻¹ * c : cycU l U) : G F Ω) = w' * w⁻¹ by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]]
      exact Subgroup.mul_mem _ hw' (Subgroup.inv_mem _ hw)
    have h0 := hNker _ hmem
    have hinv : φ c'⁻¹ = -φ c' := eq_neg_of_add_eq_zero_left (by rw [← hmul, inv_mul_cancel, hφ1])
    rw [hmul, hinv] at h0
    exact (neg_add_eq_zero.mp h0).symm
  have hinter : ∀ x ∈ ⋂ n, (levU l U n : Set (G F Ω)), x ∈ cycU l U := fun x hx => by
    rw [Set.mem_iInter] at hx
    exact ⟨(hx 0).1, eq_one_of_mem_all_princ l _ fun n => (hx n).2⟩
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_compactSpace (X := G F Ω) (ι := ℕ)
    (V := fun n => (levU l U n : Set (G F Ω)))
    (fun i j => ⟨max i j, hlev_anti _ _ (le_max_left _ _), hlev_anti _ _ (le_max_right _ _)⟩)
    (fun m => closed_levU l hU m)
    (U := {a | ∃ c ∈ cycU l U, ∃ w ∈ E.fixingSubgroup, a = c * w})
    (fun x hx => Filter.mem_of_superset
      (IsOpen.mem_nhds (hNopen.preimage (continuous_const_mul x⁻¹)) (by simp))
      fun a ha => ⟨x, hinter x hx, x⁻¹ * a, ha, by group⟩)
  have hex : ∀ y : levU l U n, ∃ c : cycU l U, ∃ w ∈ E.fixingSubgroup, (y : G F Ω) = c * w :=
    fun y => let ⟨c, hc, w, hw, e⟩ := hn y.2; ⟨⟨c, hc⟩, w, hw, e⟩
  choose cf wf hwf hcw using hex
  refine ⟨n, fun y => φ (cf y), ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    refine ⟨{z : levU l U n | (y : G F Ω)⁻¹ * z ∈ E.fixingSubgroup},
      hNopen.preimage (continuous_const.mul continuous_subtype_val), by simp,
      fun z hz => hwd (cf z) (cf y) (wf z) (wf y * ((y : G F Ω)⁻¹ * z)) (hwf z)
        (Subgroup.mul_mem _ (hwf y) hz) (by rw [← hcw z, ← mul_assoc, ← hcw y]; group)⟩
  · intro a b
    rw [← hmul]
    have hv : ((cf b : G F Ω)⁻¹ * wf a * cf b) * wf b ∈ E.fixingSubgroup :=
      Subgroup.mul_mem _ (by simpa using hNnorm.conj_mem _ (hwf a) ((cf b : G F Ω)⁻¹)) (hwf b)
    exact hwd (cf (a * b)) (cf a * cf b) (wf (a * b)) _ (hwf _) hv
      (by rw [← hcw (a * b), Subgroup.coe_mul, hcw a, hcw b, Subgroup.coe_mul]; group)
  · intro u
    exact hwd _ u (wf _) 1 (hwf _) (Subgroup.one_mem _) (by rw [← hcw, mul_one])

theorem xdualExt (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] (hN : N ≠ 0) (hU : IsClosed (U : Set (G F Ω)))
    (φ : cycU l U → M) (hφ : φ ∈ XDual N (cycU l U) R M) :
    ∃ n, ∃ ψ ∈ XDual N (levU l U n) R M, restr R M (cycU_le_levU l U n) ψ = φ := by
  obtain ⟨hφc, hφa, hφI, hφD⟩ := hφ
  obtain ⟨n, ψ, hψc, hψa, hψφ⟩ := homExt F Ω l U M φ hU hφc hφa
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hext : ∀ (g : G F Ω) (hg : g ∈ cycU l U) (hg' : g ∈ levU l U n), ψ ⟨g, hg'⟩ = φ ⟨g, hg⟩ :=
    fun g hg _ => hψφ ⟨g, hg⟩
  have hC : IsCompact ({g | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Dec (F := F) A} ∪
      {g | ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := F) A}) :=
    (decCompact F Ω N hN).1.union (decCompact F Ω l hl0).2
  have hB : IsClosed (Subtype.val '' ({u : levU l U n | ψ u = 0}ᶜ) : Set (G F Ω)) :=
    (closed_levU l hU n).isClosedMap_subtype_val _ (hψc.isOpen_fiber 0).isClosed_compl
  have hanti : ∀ {a b : ℕ}, a ≤ b → levU l U b ≤ levU l U a := fun h =>
    inf_le_inf_left _ (Subgroup.comap_mono (princ_anti h))
  obtain ⟨i, hi⟩ := (hC.inter_right hB).elim_directed_family_closed
    (fun m => (levU l U (n + m) : Set (G F Ω))) (fun m => closed_levU l hU (n + m))
    (by
      ext g
      constructor
      · rintro ⟨⟨hgC, u, hu, rfl⟩, hall⟩
        rw [Set.mem_iInter] at hall
        exfalso; apply hu
        have hucyc : (u : G F Ω) ∈ cycU l U :=
          ⟨u.2.1, eq_one_of_mem_all_princ l _ fun m => (hanti (Nat.le_add_left m n) (hall m)).2⟩
        show ψ u = 0
        rw [show u = ⟨u.1, u.2⟩ from rfl, hext u.1 hucyc u.2]
        rcases hgC with ⟨A, hA, hD⟩ | ⟨A, hA, hI⟩
        · exact hφD A hA _ hD
        · exact hφI A _ hI
      · intro hg; exact hg.elim)
    (fun a b => ⟨max a b, hanti (Nat.add_le_add_left (le_max_left a b) n),
      hanti (Nat.add_le_add_left (le_max_right a b) n)⟩)
  have hm : ∀ u : levU l U n, u.1 ∈ ({g | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Dec (F := F) A} ∪
      {g | ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := F) A}) →
      u.1 ∈ levU l U (n + i) → ψ u = 0 := fun u huC hum => by
    by_contra hne
    have hmem : u.1 ∈ ({g | ∃ A : ValuationSubring Ω, A.valuation (N : Ω) < 1 ∧ g ∈ Dec (F := F) A} ∪
        {g | ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ g ∈ Ine (F := F) A}) ∩
        (Subtype.val '' ({u : levU l U n | ψ u = 0}ᶜ)) ∩ (levU l U (n + i) : Set (G F Ω)) :=
      ⟨⟨huC, u, hne, rfl⟩, hum⟩
    rw [hi] at hmem; exact hmem
  refine ⟨n + i, restr R M (hanti (Nat.le_add_right n i)) ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hψc.comp_continuous (continuous_subtype_val.subtype_mk _)
  · intro a b; simp only [restr, LinearMap.funLeft_apply, map_mul]; exact hψa _ _
  · intro A u hu
    simp only [restr, LinearMap.funLeft_apply]
    by_cases hA : A.valuation (l : Ω) < 1
    · exact hm _ (Or.inr ⟨A, hA, hu⟩) u.2
    · have hker := (places F Ω l A).2.2.2 hA hu
      have hcu : (u : G F Ω) ∈ cycU l U := ⟨u.2.1, hker⟩
      rw [show Subgroup.inclusion (hanti (Nat.le_add_right n i)) u = ⟨u.1, (hanti (Nat.le_add_right n i)) u.2⟩ from rfl,
        hext _ hcu]
      exact hφI A _ hu
  · intro A hA u hu
    simp only [restr, LinearMap.funLeft_apply]
    exact hm _ (Or.inl ⟨A, hA, hu⟩) u.2
  · funext u; exact hψφ u

private theorem cycZ_eq_of_intertwined {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (l : ℕ)
    [Fact l.Prime] (σ : Ω ≃+* Ω) (u v : G F Ω) (h : ∀ x, v (σ x) = σ (u x)) :
    cycZ F Ω l v = cycZ F Ω l u := by
  have key : MulSemiringAction.toRingAut (G F Ω) Ω v * σ =
      σ * MulSemiringAction.toRingAut (G F Ω) Ω u := RingEquiv.ext h
  have e := congrArg (cyclotomicCharacter Ω l) key
  rw [map_mul, map_mul, mul_comm (cyclotomicCharacter Ω l σ)] at e
  exact mul_right_cancel e

private theorem spread_eq_on_levU (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (hU : IsClosed (U : Set (G F Ω)))
    (n : ℕ) (T : Type) [TopologicalSpace T] [CompactSpace T] (M : Type) [AddCommGroup M]
    (ψ₀ : levU l U n → M) (hψ₀ : IsLocallyConstant ψ₀) (c : T → G F Ω → G F Ω)
    (hc : Continuous fun p : T × G F Ω => c p.1 p.2) (hcU : ∀ t u, u ∈ levU l U n → c t u ∈ levU l U n)
    (A : T → M → M) (hA : ∀ x, IsLocallyConstant fun t => A t x)
    (h0 : ∀ t (u : levU l U n), (u : G F Ω) ∈ cycU l U → ψ₀ ⟨c t u, hcU t u u.2⟩ = A t (ψ₀ u)) :
    ∃ m, n ≤ m ∧ ∀ t (u : levU l U n), (u : G F Ω) ∈ levU l U m →
      ψ₀ ⟨c t u, hcU t u u.2⟩ = A t (ψ₀ u) := by
  have h1 : IsLocallyConstant fun p : T × levU l U n => ψ₀ ⟨c p.1 p.2, hcU p.1 p.2 p.2.2⟩ :=
    hψ₀.comp_continuous (Continuous.subtype_mk
      (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _)
  have h2 : IsLocallyConstant fun p : T × levU l U n => ψ₀ p.2 := hψ₀.comp_continuous continuous_snd
  have hloc : IsLocallyConstant fun p : T × levU l U n =>
      ψ₀ ⟨c p.1 p.2, hcU p.1 p.2 p.2.2⟩ - A p.1 (ψ₀ p.2) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t₀, u₀⟩
    have h3 : IsLocallyConstant fun p : T × levU l U n => A p.1 (ψ₀ u₀) :=
      (hA (ψ₀ u₀)).comp_continuous continuous_fst
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp h1 (t₀, u₀),
      (IsLocallyConstant.iff_eventually_eq _).mp h2 (t₀, u₀),
      (IsLocallyConstant.iff_eventually_eq _).mp h3 (t₀, u₀)] with p e1 e2 e3
    rw [e1, e2, e3]
  obtain ⟨m, hnm, hm⟩ := levCompact F Ω l U n T M _ hU hloc
    (fun t u hu => sub_eq_zero.mpr (h0 t u hu))
  exact ⟨m, hnm, fun t u hu => sub_eq_zero.mp (hm t u hu)⟩

theorem eqExt (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [hUn : U.Normal] (R M : Type)
    [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M) (hN : N ≠ 0)
    (hU : IsClosed (U : Set (G F Ω))) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m) :
    (∀ φ ∈ EqHom N (cycU l U) ρ, ∃ n, ∃ ψ ∈ EqHom N (levU l U n) ρ,
      restr R M (cycU_le_levU l U n) ψ = φ) ∧
    ∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω) (h : IsLift τ σ) (s : R), (∀ u ∈ U, conjGal h.symm u ∈ U) →
      ∀ φ ∈ EqEig N (cycU l U) ρ σ s, ∃ n, ∃ ψ ∈ EqEig N (levU l U n) ρ σ s,
        restr R M (cycU_le_levU l U n) ψ = φ := by
  have hanti : ∀ {a b : ℕ}, a ≤ b → levU l U b ≤ levU l U a := fun h =>
    inf_le_inf_left _ (Subgroup.comap_mono (princ_anti h))
  have step1 : ∀ φ ∈ EqHom N (cycU l U) ρ, ∃ n, ∃ ψ ∈ EqHom N (levU l U n) ρ,
      restr R M (cycU_le_levU l U n) ψ = φ := by
    intro φ hφ
    obtain ⟨hφX, hφC⟩ := Submodule.mem_inf.mp hφ
    obtain ⟨n, ψ₀, hψ₀X, hres⟩ := xdualExt F Ω l N U R M hN hU φ hφX
    have hcU : ∀ g u, u ∈ levU l U n → g * u * g⁻¹ ∈ levU l U n := fun g u hu =>
      ⟨hUn.conj_mem u hu.1 g, by
        show cycZ F Ω l (g * u * g⁻¹) ∈ princ l n
        rw [cycZ_eq_of_intertwined l g.toRingEquiv u _ (fun x => by simp [AlgEquiv.mul_apply])]
        exact hu.2⟩
    have h0 : ∀ g (u : levU l U n), (u : G F Ω) ∈ cycU l U →
        ψ₀ ⟨g * u * g⁻¹, hcU g u u.2⟩ = ρ g (ψ₀ u) := fun g u hu => by
      have hw' : g * (u : G F Ω) * g⁻¹ ∈ cycU l U :=
        ⟨hUn.conj_mem u u.2.1 g, by
          show cycZ F Ω l (g * u * g⁻¹) = 1
          rw [cycZ_eq_of_intertwined l g.toRingEquiv u _ (fun x => by simp [AlgEquiv.mul_apply])]
          exact hu.2⟩
      have e1 : ψ₀ ⟨g * u * g⁻¹, hcU g u u.2⟩ = φ ⟨g * u * g⁻¹, hw'⟩ := by rw [← hres]; rfl
      have e2 : ψ₀ u = φ ⟨u, hu⟩ := by rw [← hres]; rfl
      rw [e1, e2]
      exact (Submodule.mem_iInf _).mp hφC g ⟨u, hu⟩ ⟨g * u * g⁻¹, hw'⟩ (fun x => by simp [AlgEquiv.mul_apply])
    obtain ⟨m, hnm, hm⟩ := spread_eq_on_levU F Ω l U hU n (G F Ω) M ψ₀ hψ₀X.1 (fun g u => g * u * g⁻¹)
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv) hcU (fun g x => ρ g x) hρ h0
    refine ⟨m, restr R M (hanti hnm) ψ₀, Submodule.mem_inf.mpr ⟨
      (restrMem F Ω N _ _ (hanti hnm) R M ρ).1 (Submodule.mem_map_of_mem hψ₀X),
      (Submodule.mem_iInf _).mpr fun g u u' hrel => ?_⟩, by funext x; exact congrFun hres x⟩
    have hu' : (u' : G F Ω) = g * u * g⁻¹ := AlgEquiv.ext fun x => by
      have e := hrel (g⁻¹ x); simp only [AlgEquiv.coe_ringEquiv] at e
      simp only [AlgEquiv.mul_apply, ← e]; simp
    have e := hm g (Subgroup.inclusion (hanti hnm) u) u.2
    show ψ₀ (Subgroup.inclusion _ u') = ρ g (ψ₀ (Subgroup.inclusion _ u))
    rw [← e]; congr 1; exact Subtype.ext hu'
  refine ⟨step1, fun τ σ h s hUσ φ hφ => ?_⟩
  obtain ⟨hφH, hφS⟩ := Submodule.mem_inf.mp hφ
  obtain ⟨n, ψ, hψ, hres⟩ := step1 φ hφH
  have hrelc : ∀ (u : G F Ω) x, conjGal h.symm u (σ x) = σ (u x) := fun u x => by simp [conjGal_apply]
  have hcU : ∀ (_ : Unit) u, u ∈ levU l U n → conjGal h.symm u ∈ levU l U n := fun _ u hu =>
    ⟨hUσ u hu.1, by
      show cycZ F Ω l (conjGal h.symm u) ∈ princ l n
      rw [cycZ_eq_of_intertwined l σ u _ (hrelc u)]; exact hu.2⟩
  have h0 : ∀ (_ : Unit) (u : levU l U n), (u : G F Ω) ∈ cycU l U →
      ψ ⟨conjGal h.symm u, hcU () u u.2⟩ = s • ψ u := fun _ u hu => by
    have hw' : conjGal h.symm (u : G F Ω) ∈ cycU l U :=
      ⟨hUσ u u.2.1, by
        show cycZ F Ω l (conjGal h.symm u) = 1
        rw [cycZ_eq_of_intertwined l σ u _ (hrelc u)]; exact hu.2⟩
    have e1 : ψ ⟨conjGal h.symm u, hcU () u u.2⟩ = φ ⟨conjGal h.symm u, hw'⟩ := by rw [← hres]; rfl
    have e2 : ψ u = φ ⟨u, hu⟩ := by rw [← hres]; rfl
    rw [e1, e2]; exact hφS ⟨u, hu⟩ ⟨conjGal h.symm u, hw'⟩ (hrelc u)
  obtain ⟨m, hnm, hm⟩ := spread_eq_on_levU F Ω l U hU n Unit M ψ (Submodule.mem_inf.mp hψ).1.1
    (fun _ u => conjGal h.symm u) ((continuous_conjGal h.symm).comp continuous_snd) hcU
    (fun _ x => s • x) (fun _ => IsLocallyConstant.const _) h0
  refine ⟨m, restr R M (hanti hnm) ψ, Submodule.mem_inf.mpr ⟨
    (restrMem F Ω N _ _ (hanti hnm) R M ρ).2.1 (Submodule.mem_map_of_mem hψ), fun u u' hrel => ?_⟩,
    by funext x; exact congrFun hres x⟩
  have hu' : (u' : G F Ω) = conjGal h.symm u := AlgEquiv.ext fun x => by
    have e := hrel (σ.symm x); simp only [RingEquiv.apply_symm_apply] at e
    rw [e]; simp [conjGal_apply]
  have e := hm () (Subgroup.inclusion (hanti hnm) u) u.2
  show ψ (Subgroup.inclusion _ u') = s • ψ (Subgroup.inclusion _ u)
  rw [← e]; congr 1; exact Subtype.ext hu'

private theorem pow_succ_dvd_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (j : ℕ) (v : ℤ_[l])
    (h : (l : ℤ_[l]) ^ (j + 1) ∣ v - 1) : (l : ℤ_[l]) ^ (j + 2) ∣ v ^ l - 1 := by
  obtain ⟨c, hc⟩ := h
  have hg : v ^ l - 1 = (v - 1) * ∑ i ∈ Finset.range l, v ^ i := by rw [mul_comm, geom_sum_mul]
  have hs : v - 1 ∣ (∑ i ∈ Finset.range l, v ^ i) - l := by
    rw [show (∑ i ∈ Finset.range l, v ^ i) - l = ∑ i ∈ Finset.range l, (v ^ i - 1) by
      rw [Finset.sum_sub_distrib]; simp]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow v 1 i
  obtain ⟨d, hd⟩ := hs
  refine ⟨c + (l : ℤ_[l]) ^ j * c ^ 2 * d, ?_⟩
  have hsum : ∑ i ∈ Finset.range l, v ^ i = l + (v - 1) * d := by linear_combination hd
  rw [hg, hsum, hc]; ring

theorem dinfNil (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal]
    (hU : IsClosed (U : Set (G F Ω))) (φ : cycU l U → QZ l) (hφ : φ ∈ Dinf l N U) :
    (∃ n, ∀ g ∈ levU l U n, funRep ℤ_[l] (QZ l) (cycU l U) g φ = φ) ∧
    ∀ γ ∈ levU l U 1, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 ∧
      ((funRep ℤ_[l] (QZ l) (cycU l U) γ - 1) ^ k) φ = 0 := by
  classical
  have hlc : IsLocallyConstant φ := hφ.1
  have hadd : ∀ a b, φ (a * b) = φ a + φ b := hφ.2.1
  have h1 : φ 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ a, φ a⁻¹ = -φ a := fun a => by
    have h2 := hadd a⁻¹ a; rw [inv_mul_cancel, h1] at h2; exact eq_neg_of_add_eq_zero_left h2.symm
  have hCc : IsClosed (cycU l U : Set (G F Ω)) :=
    hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hCc.isCompact
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (hlc.isOpen_fiber 0)
  have h1O : (1 : G F Ω) ∈ O := by
    have h2 : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; exact h1
    exact h2
  obtain ⟨E, hEfin, hEnorm, hW⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω O).mp (hO.mem_nhds h1O)
  haveI := hEfin; haveI := hEnorm
  let W : Subgroup (G F Ω) := E.fixingSubgroup
  have hWopen : IsOpen (W : Set (G F Ω)) := E.fixingSubgroup_isOpen
  have hWnorm : W.Normal := by
    dsimp only [W]; rw [← IntermediateField.restrictNormalHom_ker]; exact MonoidHom.normal_ker _
  have hWker : ∀ (d : G F Ω) (hd : d ∈ cycU l U), d ∈ W → φ ⟨d, hd⟩ = 0 := fun d hd hdW => by
    have h2 : (⟨d, hd⟩ : cycU l U) ∈ Subtype.val ⁻¹' O := hW hdW
    rw [hOeq] at h2; exact h2
  have conj_val : ∀ (γ : G F Ω) (x : cycU l U), ((conjHom (cycU l U) γ x : cycU l U) : G F Ω) =
      γ⁻¹ * x * γ := fun _ _ => rfl
  have stabC : ∀ γ ∈ cycU l U, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := fun γ hγ x => by
    have e : conjHom (cycU l U) γ x = (⟨γ, hγ⟩ : cycU l U)⁻¹ * x * ⟨γ, hγ⟩ := Subtype.ext (by simp [conj_val])
    rw [e, hadd, hadd, hinv]; abel
  have stabW : ∀ γ ∈ W, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := fun γ hγ x => by
    have hdC : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ cycU l U :=
      mul_mem (conjHom (cycU l U) γ x).2 (inv_mem x.2)
    have hdW : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ W := by
      simpa [mul_assoc] using mul_mem (inv_mem hγ) (hWnorm.conj_mem γ hγ x)
    have e : conjHom (cycU l U) γ x = ⟨_, hdC⟩ * x := Subtype.ext (by simp only [conj_val, Subgroup.coe_mul]; group)
    rw [e, hadd, hWker _ hdC hdW, zero_add]
  have stabMul : ∀ a b : G F Ω, (∀ x, φ (conjHom (cycU l U) a x) = φ x) →
      (∀ x, φ (conjHom (cycU l U) b x) = φ x) → ∀ x, φ (conjHom (cycU l U) (a * b) x) = φ x :=
    fun a b ha hb x => by
      rw [show conjHom (cycU l U) (a * b) x = conjHom (cycU l U) b (conjHom (cycU l U) a x) from
        Subtype.ext (by simp only [conj_val]; group), hb, ha]
  let S : Set (G F Ω) := ⋃ c : cycU l U, (fun γ => γ * (c : G F Ω)⁻¹) ⁻¹' (W : Set (G F Ω))
  have hSo : IsOpen S := isOpen_iUnion fun _ => hWopen.preimage (continuous_id.mul continuous_const)
  have hSstab : ∀ γ ∈ S, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := fun γ hγ => by
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hγ
    rw [show γ = (γ * (c : G F Ω)⁻¹) * c by group]
    exact stabMul _ _ (stabW _ hc) (stabC _ c.2)
  let T : Set (G F Ω) := (U : Set (G F Ω)) ∩ Sᶜ
  have hχT : IsClosed (cycZ F Ω l '' T) := ((hU.inter hSo.isClosed_compl).isCompact.image (continuous_cycZ F Ω l)).isClosed
  have h1T : (1 : ℤ_[l]ˣ) ∉ cycZ F Ω l '' T := by
    rintro ⟨t, ⟨htU, htS⟩, ht1⟩
    exact htS (Set.mem_iUnion.mpr ⟨⟨t, ⟨htU, ht1⟩⟩, by show t * t⁻¹ ∈ W; rw [mul_inv_cancel]; exact one_mem _⟩)
  obtain ⟨n, hn⟩ : ∃ n, ∀ u ∈ princ l n, u ∈ (cycZ F Ω l '' T)ᶜ := by
    have hV := hχT.isOpen_compl.mem_nhds h1T
    rw [(Units.isOpenEmbedding_val (R := ℤ_[l])).isEmbedding.isInducing.nhds_eq_comap, Filter.mem_comap] at hV
    obtain ⟨s, hs, hsV⟩ := hV
    rw [Units.val_one, Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hball⟩ := hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l))
    refine ⟨n, fun u hu => hsV (hball ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]
    obtain ⟨c, hc⟩ := (mem_princ (l := l)).1 hu
    rw [hc, norm_mul, PadicInt.norm_p_pow, zpow_neg, zpow_natCast, ← inv_pow]
    exact (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one c)).trans_lt hn
  have hstab : ∀ g ∈ levU l U n, ∀ x, φ (conjHom (cycU l U) g x) = φ x := fun g hg => by
    apply hSstab; by_contra hgS; exact hn _ hg.2 ⟨g, ⟨hg.1, hgS⟩, rfl⟩
  refine ⟨⟨n, fun g hg => funext (hstab g hg)⟩, fun γ hγ => ?_⟩
  have hfin := hlc.range_finite
  choose mf hmf using fun v : QZ l => (qzBasic l).2.1 v
  let k0 := hfin.toFinset.sup mf
  have hk0 : (l : ℤ_[l]) ^ k0 • φ = 0 := by
    funext x
    have hle : mf (φ x) ≤ k0 := Finset.le_sup (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.sub_add_cancel hle, pow_add, mul_smul,
      ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hmf, smul_zero]
  set q := l ^ n with hqdef
  have hqpos : 0 < q := pow_pos (Fact.out : l.Prime).pos n
  have hγq : γ ^ q ∈ levU l U n := by
    refine ⟨pow_mem hγ.1 q, ?_⟩
    change cycZ F Ω l (γ ^ q) ∈ princ l n
    rw [mem_princ, map_pow]
    have key : ∀ j : ℕ, (l : ℤ_[l]) ^ (j + 1) ∣ ((cycZ F Ω l γ ^ (l ^ j) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      intro j; induction j with
      | zero => simpa [mem_princ] using hγ.2
      | succ j ih =>
        rw [show l ^ (j + 1) = l ^ j * l from pow_succ l j, pow_mul, Units.val_pow_eq_pow_val]
        exact pow_succ_dvd_pow_prime_sub_one l j _ ih
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (key n)
  let ρ := funRep ℤ_[l] (QZ l) (cycU l U)
  let Tm : Module.End ℤ_[l] (cycU l U → QZ l) := ρ γ - 1
  let J : Ideal (Polynomial ℤ) :=
    { carrier := {p | Polynomial.aeval Tm p φ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, LinearMap.add_apply] at *; rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c p hp => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, Module.End.mul_apply] at *; rw [hp, map_zero] }
  have hB : (Polynomial.X + 1) ^ q - 1 ∈ J := by
    show (Polynomial.aeval Tm ((Polynomial.X + 1) ^ q - 1)) φ = 0
    simp only [map_sub, map_pow, map_add, Polynomial.aeval_X, map_one]
    rw [show Tm + 1 = ρ γ from sub_add_cancel _ _, ← map_pow, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    exact funext (hstab _ hγq)
  have hL : Polynomial.C ((l : ℤ) ^ k0) ∈ J := by
    show (Polynomial.aeval Tm (Polynomial.C ((l : ℤ) ^ k0))) φ = 0
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast; exact hk0
  have hP : Polynomial.C (l : ℤ) ∣ (Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X,
        Polynomial.map_one]
      rw [hqdef, add_pow_char_pow, one_pow]; ring
    have h2 := congrArg (fun P => Polynomial.coeff P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  obtain ⟨Qp, hQp⟩ := hP
  have hXq : (Polynomial.X : Polynomial ℤ) ^ q = ((Polynomial.X + 1) ^ q - 1) - Polynomial.C (l : ℤ) * Qp := by
    linear_combination (-1 : Polynomial ℤ) * hQp
  have hmem : (Polynomial.X : Polynomial ℤ) ^ (q * k0) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, pow_mul, map_pow, hXq, map_sub,
      Ideal.Quotient.eq_zero_iff_mem.mpr hB, zero_sub, map_mul]
    calc (-(Ideal.Quotient.mk J (Polynomial.C (l : ℤ)) * Ideal.Quotient.mk J Qp)) ^ k0
        = (-(Ideal.Quotient.mk J Qp)) ^ k0 * Ideal.Quotient.mk J (Polynomial.C ((l : ℤ) ^ k0)) := by
          rw [Polynomial.C_pow, map_pow]; ring
      _ = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hL, mul_zero]
  refine ⟨q * k0, ?_, ?_⟩
  · rw [show q * k0 = (q * k0 - k0) + k0 from (Nat.sub_add_cancel (Nat.le_mul_of_pos_left k0 hqpos)).symm,
      pow_add, mul_smul, hk0, smul_zero]
  · change (Polynomial.aeval Tm (Polynomial.X ^ (q * k0))) φ = 0 at hmem
    rwa [map_pow, Polynomial.aeval_X] at hmem

private theorem apply_mem_fn_of_isLift (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (l n : ℕ)
    (τ : F ≃+* F) (σ : Ω ≃+* Ω) (h : IsLift τ σ) (x : Ω) (hx : x ∈ Fn F Ω l n) :
    σ x ∈ Fn F Ω l n := by
  let T : IntermediateField F Ω :=
    { (Fn F Ω l n).toSubfield.comap (σ : Ω →+* Ω) with
      algebraMap_mem' := fun c => by
        show σ (algebraMap F Ω c) ∈ Fn F Ω l n
        rw [h c]; exact (Fn F Ω l n).algebraMap_mem _ }
  exact (IntermediateField.adjoin_le_iff (T := T)).mpr (fun y hy => by
    show σ y ∈ Fn F Ω l n
    refine IntermediateField.subset_adjoin F _ ?_
    rw [Polynomial.mem_rootSet] at hy ⊢
    refine ⟨hy.1, ?_⟩
    have h2 := hy.2
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one] at h2 ⊢
    rw [← map_pow, ← map_one σ, ← map_sub, h2, map_zero]) hx

theorem fnCyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) :
    IsCyclotomicExtension {l ^ n} F (Fn F Ω l n) ∧
    (∀ (τ : F ≃+* F) (σ : Ω ≃+* Ω), IsLift τ σ → ∃ τ' : Fn F Ω l n ≃+* Fn F Ω l n, IsLift τ' σ) ∧
    (2 ≤ n → IsTotallyComplex (Fn F Ω l n)) := by
  have hl : l.Prime := Fact.out
  have hk : l ^ n ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ n) := ⟨hk⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hFn : Fn F Ω l n = IntermediateField.adjoin F {b : Ω | ∃ m ∈ ({l ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
    show IntermediateField.adjoin F _ = _
    congr 1; ext b
    have hp : (Polynomial.X ^ l ^ n - 1 : Polynomial F) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) (1 : F)
    rw [Polynomial.mem_rootSet_of_ne hp]
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, exists_eq_left]
    exact ⟨fun h => ⟨hk, h⟩, fun h => h.2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hFn]
    refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot (S := {l ^ n}) (K := F) (L := Ω) ?_
    intro m hm _; rw [Set.mem_singleton_iff] at hm; subst hm
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  · intro τ σ h
    refine ⟨{ toFun := fun x => ⟨σ x, apply_mem_fn_of_isLift F Ω l n τ σ h x.1 x.2⟩
              invFun := fun x => ⟨σ.symm x, apply_mem_fn_of_isLift F Ω l n τ.symm σ.symm h.symm x.1 x.2⟩
              left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
              right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1)
              map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
              map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) }, fun _ => rfl⟩
  · intro hn2
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    have hzmem : z ∈ Fn F Ω l n := by
      rw [hFn]; exact IntermediateField.subset_adjoin _ _ ⟨l ^ n, rfl, hk, hz.pow_eq_one⟩
    have hζ : IsPrimitiveRoot (⟨z, hzmem⟩ : Fn F Ω l n) (l ^ n) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Fn F Ω l n).val) hz Subtype.val_injective
    have hcyc := IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) hζ
    have h2 : 2 < l ^ n :=
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ l ^ 2 := Nat.pow_le_pow_left hl.two_le 2
        _ ≤ l ^ n := Nat.pow_le_pow_right hl.pos hn2
    have htc := @IsCyclotomicExtension.Rat.isTotallyComplex (l ^ n) _
      (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) _ _ hcyc h2
    exact isTotallyComplex_of_algebra (IntermediateField.adjoin ℚ {(⟨z, hzmem⟩ : Fn F Ω l n)}) (Fn F Ω l n)

theorem galOfCyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (E K : Type) [Field E] [Field K] [Algebra E K] [Algebra E Ω]
    [Algebra K Ω] [IsScalarTower E K Ω] [IsCyclotomicExtension {l ^ n} E K] :
    galOf F K Ω = levU l (galOf F E Ω) n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun _ => inferInstance
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  ext σ
  have key : ∀ t : Ω, t ^ (l ^ n) = 1 →
      σ t = t ^ ((cycZ F Ω l σ).val.toZModPow n).val := fun t ht =>
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω σ) t ht
  show σ ∈ galOf F K Ω ↔ σ ∈ galOf F E Ω ⊓ Subgroup.comap (cycZ F Ω l) (princ l n)
  rw [Subgroup.mem_inf, Subgroup.mem_comap, princ, MonoidHom.mem_ker, redPow]
  constructor
  · intro h
    refine ⟨fun x => by have hx := h (algebraMap E K x); rwa [← IsScalarTower.algebraMap_apply] at hx, ?_⟩
    have hζ : IsPrimitiveRoot (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) (l ^ n) :=
      (IsCyclotomicExtension.zeta_spec (l ^ n) E K).map_of_injective (algebraMap K Ω).injective
    have h1 := key _ hζ.pow_eq_one
    rw [h (IsCyclotomicExtension.zeta (l ^ n) E K)] at h1
    have hfin : IsOfFinOrder (algebraMap K Ω (IsCyclotomicExtension.zeta (l ^ n) E K)) :=
      orderOf_pos_iff.mp (by rw [← hζ.eq_orderOf]; exact Nat.pos_of_neZero _)
    have h3 : ((cycZ F Ω l σ).val.toZModPow n).val ≡ 1 [MOD l ^ n] := by
      have h5 := (hfin.pow_eq_pow_iff_modEq (n := ((cycZ F Ω l σ).val.toZModPow n).val) (m := 1)).mp
        (by rw [pow_one]; exact h1.symm)
      rwa [← hζ.eq_orderOf] at h5
    ext
    have h4 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    rw [ZMod.natCast_zmod_val, Nat.cast_one] at h4
    simpa using h4
  · rintro ⟨hE, hc⟩ x
    have hc' : (cycZ F Ω l σ).val.toZModPow n = 1 := by simpa using congrArg Units.val hc
    let f1 : K →ₐ[E] Ω := IsScalarTower.toAlgHom E K Ω
    let f2 : K →ₐ[E] Ω :=
      { toRingHom := (σ : Ω →+* Ω).comp (algebraMap K Ω)
        commutes' := fun r => by
          show σ (algebraMap K Ω (algebraMap E K r)) = algebraMap E Ω r
          rw [← IsScalarTower.algebraMap_apply]; exact hE r }
    have hmem : x ∈ AlgHom.equalizer f1 f2 :=
      Algebra.adjoin_le (fun b hb => by
        obtain ⟨m, hm, -, hbm⟩ := hb
        rw [Set.mem_singleton_iff] at hm; subst hm
        have ht : (algebraMap K Ω b) ^ (l ^ n) = 1 := by rw [← map_pow, hbm, map_one]
        show algebraMap K Ω b = σ (algebraMap K Ω b)
        rw [key _ ht, hc', ZMod.val_one_eq_one_mod]
        conv_lhs => rw [← pow_one (algebraMap K Ω b), ← Nat.mod_add_div 1 (l ^ n), pow_add, pow_mul, ht, one_pow, mul_one])
        (IsCyclotomicExtension.adjoin_roots (S := {l ^ n}) (A := E) (B := K) x)
    exact ((AlgHom.mem_equalizer f1 f2 x).mp hmem).symm

theorem fnCM (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) : IsCMField (Fn F Ω l n) := by
  classical
  haveI : IsTotallyComplex (Fn F Ω l n) := isTotallyComplex_of_algebra F (Fn F Ω l n)
  have hconj : ∀ x : Fn F Ω l n, ∃ y : Fn F Ω l n, ∀ φ : Fn F Ω l n →+* ℂ, φ y = starRingEnd ℂ (φ x) := by
    rintro ⟨x, hx⟩
    have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      have hx1 : x ^ l ^ n = 1 := by simpa [sub_eq_zero] using Polynomial.aeval_eq_zero_of_mem_rootSet hx
      let z : Fn F Ω l n := ⟨x, IntermediateField.subset_adjoin F _ hx⟩
      refine ⟨z⁻¹, fun φ => ?_⟩
      have : ‖φ z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
        (by rw [← map_pow, show z ^ l ^ n = 1 from Subtype.ext hx1, map_one]) hN0
      rw [map_inv₀, Complex.inv_eq_conj this]
    | algebraMap a =>
      exact ⟨algebraMap F _ (IsCMField.complexConj F a), fun φ =>
        IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F (Fn F Ω l n))) a⟩
    | add _ _ _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx; obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, fun φ => by rw [map_add, ha, hb, ← map_add, ← map_add]; rfl⟩
    | inv _ _ ihx =>
      obtain ⟨a, ha⟩ := ihx
      exact ⟨a⁻¹, fun φ => by rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]; rfl⟩
    | mul _ _ _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx; obtain ⟨b, hb⟩ := ihy
      exact ⟨a * b, fun φ => by rw [map_mul, ha, hb, ← map_mul, ← map_mul]; rfl⟩
  choose c hc using hconj
  let φ : Fn F Ω l n →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hcc : ∀ x, c (c x) = x := fun x => φ.injective (by rw [hc, hc, Complex.conj_conj])
  let τ : Fn F Ω l n ≃+* Fn F Ω l n :=
    { toFun := c, invFun := c, left_inv := hcc, right_inv := hcc,
      map_mul' := fun x y => φ.injective (by simp only [hc, map_mul]),
      map_add' := fun x y => φ.injective (by simp only [hc, map_add]) }
  let σ : Fn F Ω l n ≃ₐ[ℚ] Fn F Ω l n := AlgEquiv.ofRingEquiv (f := τ) (fun q => by simp)
  have hσ : ∀ ψ : Fn F Ω l n →+* ℂ, ComplexEmbedding.IsConj ψ σ := fun ψ => by
    ext x; exact (hc x ψ).symm
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, ComplexEmbedding.orderOf_isConj_two_of_ne_one (hσ φ)]
    exact (ComplexEmbedding.isConj_ne_one_iff (hσ φ)).mpr <|
      IsTotallyComplex.complexEmbedding_not_isReal φ
  let L := (FixedPoints.intermediateField (Subgroup.zpowers σ) : IntermediateField ℚ (Fn F Ω l n))
  haveI : IsTotallyReal L := ⟨fun w => by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := Fn F Ω l n)
    dsimp only
    rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
      ComplexEmbedding.isReal_iff]
    ext x
    have hx : c x.1 = x.1 := x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    have := hc x.1 W.embedding
    rw [hx] at this; exact this.symm⟩
  haveI : Algebra.IsQuadraticExtension L (Fn F Ω l n) := ⟨by
    haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    rw [← hσ', Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) (Fn F Ω l n)⟩
  exact IsCMField.ofCMExtension L (Fn F Ω l n)

end DecAndTower

/-! ## Section 5: Cyclotomic Cocycle Vanishing, Extension & `resInf` Exact Sequence (`ExistsGen`, `VanishCyc`, `ExtCocycle`, `ResInf*`) -/

section ResInfSection

private theorem eg_pow_mem {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 1 ≤ a) {u : ℤ_[l]ˣ}
    (hu : u ∈ princ l a) : u ^ l ∈ princ l (a + 1) := by
  rw [mem_princ] at hu ⊢
  obtain ⟨c, hc⟩ := hu
  obtain ⟨f, hf⟩ := sq_dvd_add_pow_sub_sub ((l : ℤ_[l]) ^ a * c) 1 l
  have hw : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ a * c := by rw [← hc]; ring
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  refine ⟨c + (l : ℤ_[l]) ^ m * c ^ 2 * f, ?_⟩
  rw [Units.val_pow_eq_pow_val, hw]
  simp only [one_pow, one_mul] at hf
  linear_combination hf

theorem existsGen (l : ℕ) [Fact l.Prime] (V : Subgroup ℤ_[l]ˣ) (_ : IsClosed (V : Set ℤ_[l]ˣ))
    (hl : l ≠ 2 ∨ V ≤ princ l 2) :
    ∃ γ ∈ V, V ≤ (Subgroup.zpowers γ).topologicalClosure := by
  classical
  have hp : l.Prime := Fact.out
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := V.map (red l))
  have key : ∀ γ ∈ V, red l γ = red l g → V ⊓ princ l 1 ≤ (Subgroup.zpowers γ).topologicalClosure →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := fun γ hγ e h v hv => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    have hk' : red l g ^ k = red l v := congrArg Subtype.val hk
    have h1 : v * (γ ^ k)⁻¹ ∈ V ⊓ princ l 1 :=
      ⟨V.mul_mem hv (V.inv_mem (V.zpow_mem hγ k)), by
        show v * (γ ^ k)⁻¹ ∈ princ l 1
        rw [princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, e, hk', mul_inv_cancel]⟩
    simpa using Subgroup.mul_mem _ (h h1)
      (Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k))
  by_cases hW : V ⊓ princ l 1 = ⊥
  · exact ⟨g, hg, key g hg rfl (by rw [hW]; exact bot_le)⟩
  have hex : ∃ b, ¬ V ⊓ princ l 1 ≤ princ l b := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW
    have hne1 : w ≠ 1 := fun h => hw1 (Subtype.ext h)
    have hex' : ∃ b, w ∉ princ l b := by
      by_contra hall; push Not at hall
      exact hne1 (eq_one_of_mem_all_princ l w hall)
    obtain ⟨b, hb⟩ := hex'
    exact ⟨b, fun h => hb (h hw)⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → V ⊓ princ l 1 ≤ princ l m :=
    fun m hm => not_not.1 (Nat.find_min hex hm)
  have h1 : 1 < Nat.find hex := by
    by_contra h; exact hspec (inf_le_right.trans (princ_anti (by omega)))
  have h2 : l = 2 → 2 < Nat.find hex := fun h2 => by
    by_contra h
    exact hspec (inf_le_left.trans ((hl.resolve_left (not_not.2 h2)).trans (princ_anti (by omega))))
  obtain ⟨a, ha⟩ : ∃ a, Nat.find hex = a + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ha] at hspec hmin h1 h2
  have hle := hmin a (Nat.lt_succ_self a)
  obtain ⟨u, hu, hua⟩ := SetLike.not_le_iff_exists.1 hspec
  have fin : ∀ γ ∈ V, red l γ = red l g → γ ^ (l - 1) ∉ princ l (a + 1) →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := fun γ hγ e h => by
    refine key γ hγ e (hle.trans ?_)
    have hm : γ ^ (l - 1) ∈ princ l a := hle ⟨V.pow_mem hγ _, by
      show γ ^ (l - 1) ∈ princ l 1
      rw [princ_one_eq_ker, MonoidHom.mem_ker, map_pow, ZMod.units_pow_card_sub_one_eq_one]⟩
    refine princ_le_of_isClosed (u := γ ^ (l - 1)) (by omega) (fun h2' => by have := h2 h2'; omega)
      (Subgroup.isClosed_topologicalClosure _)
      (Subgroup.le_topologicalClosure _ (Subgroup.npow_mem_zpowers γ _)) ?_
    exact emultiplicity_eq_coe.2 ⟨mem_princ.1 hm, fun h' => h (mem_princ.2 h')⟩
  by_cases hga : g ^ (l - 1) ∈ princ l (a + 1)
  · refine ⟨g * u, V.mul_mem hg hu.1, fin _ (V.mul_mem hg hu.1) ?_ ?_⟩
    · have : u ∈ (red l).ker := by rw [← princ_one_eq_ker]; exact hu.2
      rw [map_mul, MonoidHom.mem_ker.1 this, mul_one]
    · intro h
      rw [mul_pow] at h
      have h3 := (mul_mem_cancel_left hga).1 h
      have h4 := eg_pow_mem (by omega) (hle hu)
      rw [show u ^ l = u ^ (l - 1) * u by rw [← pow_succ, Nat.sub_add_cancel hp.one_le]] at h4
      exact hua ((mul_mem_cancel_left h3).1 h4)
  · exact ⟨g, hg, fin g hg rfl hga⟩

private theorem exists_level_pow_dvd_of_not_finOrder (l : ℕ) [hl : Fact l.Prime] (u : ℤ_[l]ˣ)
    (hu : ¬ IsOfFinOrder u) (a : ℕ) :
    ∃ j : ℕ, ∀ m : ℤ, PadicInt.toZModPow j ((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 → (l : ℤ) ^ (a + 1) ∣ m := by
  by_contra h
  push Not at h
  apply hu
  have hK : 0 < l ^ a * (l - 1) :=
    Nat.mul_pos (pow_pos hl.out.pos a) (Nat.sub_pos_of_lt hl.out.one_lt)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ a * (l - 1), hK, Units.ext (PadicInt.ext_of_toZModPow.mp fun j => ?_)⟩
  obtain ⟨m, hm, hnd⟩ := h j
  let w : (ZMod (l ^ j))ˣ := Units.map (PadicInt.toZModPow j).toMonoidHom u
  have hw : ∀ n : ℤ, ((w ^ n : (ZMod (l ^ j))ˣ) : ZMod (l ^ j)) =
      PadicInt.toZModPow j ((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) := fun n => by rw [← map_zpow]; rfl
  have hwm : w ^ m = 1 := Units.ext (by rw [hw, hm, Units.val_one])
  have hom : (orderOf w : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hwm
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hcard : orderOf w ∣ (l ^ j).totient := by rw [← ZMod.card_units_eq_totient]; exact orderOf_dvd_card
  have hdiv : orderOf w ∣ l ^ a * (l - 1) := by
    rcases j with _ | i
    · simp only [pow_zero, Nat.totient_one, Nat.dvd_one] at hcard; rw [hcard]; exact one_dvd _
    · rw [Nat.totient_prime_pow_succ hl.out, ← Nat.dvd_gcd_mul_iff_dvd_mul] at hcard
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hl.out).mp (Nat.gcd_dvd_right (orderOf w) (l ^ i))
      have hba : b ≤ a := by
        by_contra hba; push Not at hba
        exact hnd ((pow_dvd_pow _ hba).trans
          ((by exact_mod_cast (hb ▸ Nat.gcd_dvd_left _ _ : l ^ b ∣ orderOf w) : (l : ℤ) ^ b ∣ orderOf w).trans hom))
      rw [hb] at hcard
      exact hcard.trans (Nat.mul_dvd_mul_right (pow_dvd_pow l hba) _)
  have hwK : w ^ (l ^ a * (l - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have := hw ((l ^ a * (l - 1) : ℕ) : ℤ)
  rw [zpow_natCast, zpow_natCast, hwK, Units.val_one] at this
  rw [← this, Units.val_one, map_one]

theorem vanishCyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (M : Type) [AddCommGroup M] (φ : Uinf F Ω l → M) (γ : G F Ω)
    (hφ : IsLocallyConstant φ) (hmul : ∀ a b, φ (a * b) = φ a + φ b)
    (htor : ∀ m : M, ∃ k : ℕ, l ^ k • m = 0) (hγ : ¬ IsOfFinOrder (cycZ F Ω l γ))
    (x : Uinf F Ω l) (hx : x.1 ∈ (Subgroup.zpowers γ).topologicalClosure) : φ x = 0 := by
  have h1 : φ 1 = 0 := by simpa using hmul 1 1
  have hpow : ∀ (y : Uinf F Ω l) (n : ℕ), φ (y ^ n) = n • φ y := fun y n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, succ_nsmul]
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber 0)
  have hW1 : (1 : G F Ω) ∈ W := by
    have : (1 : Uinf F Ω l) ∈ Subtype.val ⁻¹' W := by rw [hWeq]; exact h1
    exact this
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff F Ω W).mp (hWo.mem_nhds hW1)
  haveI := hE
  have hN : IsOpen (E.fixingSubgroup : Set (G F Ω)) := IntermediateField.fixingSubgroup_isOpen E
  have hNφ : ∀ y : Uinf F Ω l, y.1 ∈ E.fixingSubgroup → φ y = 0 := fun y hy => by
    have : y ∈ Subtype.val ⁻¹' W := hEW hy; rw [hWeq] at this; exact this
  haveI : Finite (G F Ω ⧸ E.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hN
  obtain ⟨d, hd0, -, hdN⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) γ
  obtain ⟨a, d', hd'l, hdd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' l hl.out.ne_one
  obtain ⟨j, hj⟩ := exists_level_pow_dvd_of_not_finOrder l (cycZ F Ω l γ) hγ a
  let H : Subgroup (G F Ω) := (princ l j).comap (cycZ F Ω l)
  have hHo : IsOpen (H : Set (G F Ω)) := (isOpen_princ j).preimage (continuous_cycZ F Ω l)
  have ho : IsOpen ((fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω)))) :=
    (hN.inter hHo).preimage (continuous_const.mul continuous_id)
  have hxo : x.1 ∈ (fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω))) := by
    simp only [Set.mem_preimage, inv_mul_cancel, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨one_mem _, one_mem _⟩
  have hx' : x.1 ∈ closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) := by
    rw [← Subgroup.topologicalClosure_coe]; exact hx
  obtain ⟨g, ⟨hνN, hνH⟩, hgz⟩ := mem_closure_iff.mp hx' _ ho hxo
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgz
  have hcx : cycZ F Ω l x.1 = 1 := x.2.2
  have hcyc : PadicInt.toZModPow j ((cycZ F Ω l γ ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have hmem : redPow l j (cycZ F Ω l γ ^ m) = 1 := by
      have h1 : cycZ F Ω l (x.1⁻¹ * γ ^ m) ∈ princ l j := hνH
      rw [map_mul, map_inv, hcx, inv_one, one_mul, map_zpow] at h1
      exact MonoidHom.mem_ker.1 h1
    exact congrArg Units.val hmem
  have hma : (l : ℤ) ^ a ∣ m := (pow_dvd_pow _ (Nat.le_succ a)).trans (hj m hcyc)
  have hcl : closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) ⊆ {y | y * γ = γ * y} :=
    closure_minimal (fun y hy => let ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy; hi ▸ (Commute.self_zpow γ i).symm.eq)
      (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id))
  have hxν : Commute x.1 (x.1⁻¹ * γ ^ m) := (Commute.refl x.1).inv_right.mul_right (Commute.zpow_right (hcl hx') m)
  have hexp : (γ ^ m) ^ d' = x.1 ^ d' * (x.1⁻¹ * γ ^ m) ^ d' := by rw [← hxν.mul_pow, mul_inv_cancel_left]
  have hγN : (γ ^ m) ^ d' ∈ E.fixingSubgroup := by
    obtain ⟨t, ht⟩ := hma
    rw [show (γ ^ m) ^ d' = (γ ^ d) ^ t by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ht, hdd]; congr 1; push_cast; ring]
    exact zpow_mem hdN t
  have hxN : (x ^ d').1 ∈ E.fixingSubgroup := by
    rw [show (x ^ d').1 = (γ ^ m) ^ d' * ((x.1⁻¹ * γ ^ m) ^ d')⁻¹ by rw [hexp, mul_inv_cancel_right]; rfl]
    exact mul_mem hγN (inv_mem (pow_mem hνN d'))
  have h0 : d' • φ x = 0 := by rw [← hpow]; exact hNφ _ hxN
  obtain ⟨k, hk⟩ := htor (φ x)
  have hcop : Nat.Coprime d' (l ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr hd'l))
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one
    (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h0) (addOrderOf_dvd_of_nsmul_eq_zero hk)))

private theorem ext_of_prod {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (ρ : Representation R Γ M) (C U : Subgroup Γ) [hN : U.Normal]
    (hC : IsClosed (C : Set Γ)) (hU : IsClosed (U : Set Γ))
    (hCU : ∀ g : Γ, ∃ p : C × U, p.1.1 * p.2.1 = g) (φ : U → M) (hρ : ContAction ρ)
    (htr : ∀ u ∈ U, ∀ m, ρ u m = m) (hφ : Continuous φ) (hadd : ∀ a b, φ (a * b) = φ a + φ b)
    (heq : ∀ (g : Γ) (u u' : U), u'.1 * g = g * u.1 → φ u' = ρ g (φ u))
    (hv : ∀ x : U, x.1 ∈ C → φ x = 0) : ∃ z ∈ Z1 ρ, ∀ u : U, z u.1 = φ u := by
  classical
  let f : C × U → Γ := fun p => p.1.1 * p.2.1
  have hwd : ∀ p q : C × U, f p = f q → ρ p.1.1 (φ p.2) = ρ q.1.1 (φ q.2) := by
    rintro ⟨⟨c, hc⟩, ⟨u, hu⟩⟩ ⟨⟨c', hc'⟩, ⟨u', hu'⟩⟩ h
    change c * u = c' * u' at h
    have hw1 : c'⁻¹ * c = u' * u⁻¹ := by rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have hwU : c'⁻¹ * c ∈ U := hw1 ▸ U.mul_mem hu' (U.inv_mem hu)
    have hu'eq : (⟨u', hu'⟩ : U) = ⟨_, hwU⟩ * ⟨u, hu⟩ := Subtype.ext (by simp [hw1])
    have h2 : φ ⟨u', hu'⟩ = φ ⟨u, hu⟩ := by rw [hu'eq, hadd, hv _ (C.mul_mem (C.inv_mem hc') hc), zero_add]
    change ρ c (φ ⟨u, hu⟩) = ρ c' (φ ⟨u', hu'⟩)
    rw [h2, show ρ c = ρ c' * ρ (c'⁻¹ * c) by rw [← map_mul, mul_inv_cancel_left],
      Module.End.mul_apply, htr _ hwU]
  choose s hs using hCU
  let z : Γ → M := fun g => ρ (s g).1.1 (φ (s g).2)
  have hzf : ∀ p : C × U, z (f p) = ρ p.1.1 (φ p.2) := fun p => hwd _ _ (hs (f p))
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU.isCompact
  have hfc : Continuous f := (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hfs : Function.Surjective f := fun g => ⟨s g, hs g⟩
  have hzc : Continuous z := (hfc.isClosedMap.isQuotientMap hfc hfs).continuous_iff.2 <| by
    have : z ∘ f = fun p : C × U => ρ p.1.1 (φ p.2) := funext hzf
    rw [this]; exact hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  have hcoc : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := fun g h => by
    obtain ⟨⟨⟨c, hc⟩, ⟨u, hu⟩⟩, rfl⟩ := hfs g
    obtain ⟨⟨⟨d, hd⟩, ⟨v, hv'⟩⟩, rfl⟩ := hfs h
    have hu0 : d⁻¹ * u * d ∈ U := by simpa using hN.conj_mem u hu d⁻¹
    have hprod : f (⟨c, hc⟩, ⟨u, hu⟩) * f (⟨d, hd⟩, ⟨v, hv'⟩) =
        f (⟨c * d, C.mul_mem hc hd⟩, ⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩) := by
      simp only [f, Subgroup.coe_mul]; group
    rw [hprod, hzf, hzf, hzf]
    change ρ (c * d) (φ (⟨d⁻¹ * u * d, hu0⟩ * ⟨v, hv'⟩)) = ρ c (φ ⟨u, hu⟩) + ρ (c * u) (ρ d (φ ⟨v, hv'⟩))
    have hconj : φ ⟨u, hu⟩ = ρ d (φ ⟨d⁻¹ * u * d, hu0⟩) :=
      heq d ⟨d⁻¹ * u * d, hu0⟩ ⟨u, hu⟩ (by show u * d = d * (d⁻¹ * u * d); group)
    rw [hadd, map_add, hconj]; simp only [map_mul, Module.End.mul_apply]; rw [htr u hu]
  exact ⟨z, ⟨hzc, hcoc⟩, fun u => by simpa [f] using hzf (⟨1, C.one_mem⟩, u)⟩

theorem extCocycle (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (φ : Uinf F Ω l → M)
    (hP : Procyc F Ω l) (hρ : ContAction ρ) (htr : ∀ u ∈ Uinf F Ω l, ∀ m, ρ u m = m)
    (htors : ∀ m : M, ∃ k : ℕ, l ^ k • m = 0) (hloc : IsLocallyConstant φ)
    (hadd : ∀ a b, φ (a * b) = φ a + φ b)
    (hconj : ∀ g : G F Ω, φ ∈ conjCond (Uinf F Ω l) g.toRingEquiv (ρ g)) :
    ∃ z ∈ Z1 ρ, ∀ u : Uinf F Ω l, z u.1 = φ u := by
  classical
  have hVc : IsClosed ((cycZ F Ω l).range : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]; exact (isCompact_range (continuous_cycZ F Ω l)).isClosed
  have hcond : l ≠ 2 ∨ (cycZ F Ω l).range ≤ princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right; rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_ker.mpr (h g)
  obtain ⟨_, ⟨γ, rfl⟩, hgen⟩ := existsGen l _ hVc hcond
  have hnf : ¬ IsOfFinOrder (cycZ F Ω l γ) := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    obtain ⟨g, hg⟩ := exists_cyc_pow_ne_one l F Ω n hn.ne'
    have hsub : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ⊆
        {x | x ^ n = 1} :=
      closure_minimal (fun x hx => let ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
        hk ▸ by show ((cycZ F Ω l γ) ^ k) ^ n = 1; rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow])
        (isClosed_eq (continuous_pow n) continuous_const)
    have h1 := hgen (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
    exact hg (hsub h1)
  haveI : (Uinf F Ω l).Normal := show (⊤ ⊓ (cycZ F Ω l).ker).Normal by infer_instance
  have hUc : IsClosed ((Uinf F Ω l : Subgroup (G F Ω)) : Set (G F Ω)) := by
    show IsClosed ((⊤ ⊓ (cycZ F Ω l).ker : Subgroup (G F Ω)) : Set (G F Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_top, Set.univ_inter, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycZ F Ω l)
  have hCc := Subgroup.isClosed_topologicalClosure (Subgroup.zpowers γ)
  have hCU : ∀ g : G F Ω, ∃ p : (Subgroup.zpowers γ).topologicalClosure × Uinf F Ω l, p.1.1 * p.2.1 = g := by
    intro g
    have himg : closure ((Subgroup.zpowers (cycZ F Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ⊆
        (cycZ F Ω l) '' ((Subgroup.zpowers γ).topologicalClosure : Set (G F Ω)) :=
      closure_minimal (fun x hx => let ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
        ⟨γ ^ k, Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k), hk ▸ map_zpow _ _ _⟩)
        (hCc.isCompact.image (continuous_cycZ F Ω l)).isClosed
    have hg := hgen (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hg
    obtain ⟨c, hc, hcg⟩ := himg hg
    exact ⟨(⟨c, hc⟩, ⟨c⁻¹ * g, ⟨trivial, by show cycZ F Ω l (c⁻¹ * g) = 1; rw [map_mul, map_inv, hcg, inv_mul_cancel]⟩⟩),
      mul_inv_cancel_left c g⟩
  exact ext_of_prod ρ (Subgroup.zpowers γ).topologicalClosure (Uinf F Ω l) hCc hUc hCU φ hρ htr
    hloc.continuous hadd (fun g u u' h => hconj g u u' fun x => congrArg (fun e : G F Ω => e x) h)
    (fun x hx => vanishCyc F Ω l M φ γ hloc hadd htors hnf x hx)

private theorem coc_conj_triv {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (f : Γ → M) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (g h k : Γ)
    (e : k * g = g * h) (hk : ∀ m, ρ k m = m) : f k = ρ g (f h) := by
  have h1 := hf k g
  rw [e, hf, hk, add_comm] at h1
  exact (add_right_cancel h1).symm

theorem resInfMem (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resInf D e) ≤ EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  have hchi : ∀ g : G F Ω, D.chi (toGS Ω _ g) = cycZ F Ω l g := fun g => DFunLike.congr_fun D.hchi g
  have htriv : ∀ g : G F Ω, cycZ F Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
    rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
  have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
  have hconj : ∀ g h k : G F Ω, k * g = g * h → cycZ F Ω l k = 1 →
      z.1 (toGS Ω _ k) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ h)) := fun g h k e1 hk =>
    coc_conj_triv _ _ hz _ _ _ (by rw [← map_mul, ← map_mul, e1]) (htriv k hk)
  have h1 : z.1 1 = 0 := by have := hz 1 1; rw [one_mul, map_one] at this; exact left_eq_add.1 this
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : Uinf F Ω l,
      u.1 ∈ Dec (F := F) A → z.1 (toGS Ω _ u.1) = 0 := fun A hA u hu => by
    obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
    have hvS : v ∈ D.S := by have := (p4 A v l hv).1 hA; rwa [← D.hS] at this
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
    have hx' : resH1 (qzTw D e) (locFam D.S D.A ⟨v, hvS⟩) (continuous_locFam D.S D.A ⟨v, hvS⟩)
        (Submodule.Quotient.mk z) = 0 := (Submodule.mem_iInf _).1 hx ⟨v, hvS⟩
    obtain ⟨m, hm⟩ := (mem_B1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx')
    have hc : g⁻¹ * u.1 * g ∈ Dec (F := F) (D.A ⟨v, hvS⟩) := conj_mem_Dec hu
    have hu1 : cycZ F Ω l u.1 = 1 := u.2.2
    have h2 : z.1 (toGS Ω _ (g⁻¹ * u.1 * g)) = 0 := by
      have hloc : z.1 (toGS Ω _ (g⁻¹ * u.1 * g)) = qzTw D e (toGS Ω _ (g⁻¹ * u.1 * g)) m - m := hm ⟨_, hc⟩
      rw [htriv _ (by simp [hu1]), sub_self] at hloc
      exact hloc
    rw [hconj g (g⁻¹ * u.1 * g) u.1 (by group) hu1, h2, map_zero]
  refine ⟨⟨(IsLocallyConstant.iff_continuous _).2
      (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val)),
    fun a b => by rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2],
    fun A u hu => ?_, hdec⟩, (Submodule.mem_iInf _).2 fun g u u' h => ?_⟩
  · rw [resInf_mk]
    by_cases hA : A = ⊤
    · subst hA; rw [p1, Subgroup.mem_bot] at hu; rw [hu, map_one, h1]
    obtain ⟨v, hv⟩ := p2 A hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact hdec A hl u (Ine_le_Dec A hu)
    have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [D.hS]; exact fun h => hl ((p4 A v l hv).2 h)
    have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
      Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
        (Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨hvS, Set.mem_iUnion.2 ⟨A, Set.mem_iUnion.2 ⟨hv, hu⟩⟩⟩⟩))
    have hq1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
    rw [hq1, h1]
  · rw [resInf_mk, resInf_mk, hconj g u.1 u'.1 (AlgEquiv.ext h) u'.2.2, qzTw_apply, hchi]; rfl

theorem resInfInj (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (he : e ≠ 0) (hP : Procyc F Ω l) :
    Function.Injective (resInf D e) := by
  have hcomp : ∀ h : G F Ω, D.chi (QuotientGroup.mk h) = cycZ F Ω l h := fun h => by
    rw [← D.hchi]; rfl
  have hchi : Continuous D.chi := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <| by
    convert continuous_cycZ F Ω l using 1; funext h; exact hcomp h
  have hINF : ∃ g : G F Ω, cycZ F Ω l g ^ e ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_cyc_pow_ne_one l F Ω e.natAbs (Int.natAbs_ne_zero.2 he)
    refine ⟨g, fun h0 => hg ?_⟩
    rcases Int.natAbs_eq e with h' | h'
    · rw [h', zpow_natCast] at h0; exact h0
    · rw [h', zpow_neg, inv_eq_one, zpow_natCast] at h0; exact h0
  rw [← LinearMap.ker_eq_bot]
  unfold resInf resTriv
  refine Submodule.ker_liftQ_eq_bot _ _ _ fun z hz => ?_
  rw [LinearMap.mem_ker] at hz
  have hclosed : IsClosed ((D.chi.range : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]; exact (isCompact_range hchi).isClosed
  have hcond : l ≠ 2 ∨ D.chi.range ≤ princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right; rintro _ ⟨g, rfl⟩; obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [princ, MonoidHom.mem_ker, hcomp]; exact h g'
  obtain ⟨_, ⟨γ, rfl⟩, hu⟩ := existsGen l D.chi.range hclosed hcond
  have hcont : ContAction (qzTw D e) := (contTw F Ω l D e).1
  have hne : (((D.chi γ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 := fun h0 => by
    have h2 : D.chi γ ^ e = 1 := by
      have h1 : D.chi γ ^ (-e) = 1 := Units.ext (sub_eq_zero.mp h0)
      rwa [zpow_neg, inv_eq_one] at h1
    obtain ⟨g, hg⟩ := hINF
    apply hg; rw [← hcomp]
    have hmem : D.chi (QuotientGroup.mk g) ∈ (Subgroup.zpowers (D.chi γ)).topologicalClosure := hu ⟨_, rfl⟩
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hmem
    exact closure_minimal (by
      rintro _ ⟨k, rfl⟩; show ((D.chi γ) ^ k) ^ e = 1
      rw [← zpow_mul, mul_comm, zpow_mul, h2, one_zpow])
      (isClosed_eq (continuous_zpow e) continuous_const) hmem
  exact cobOfGen l _ D.chi ℤ_[l] (QZ l) (qzTw D e) γ hchi hcont
    (fun g hg m => by simp [qzTw, scalRep, hg]) (fun g => hu ⟨g, rfl⟩)
    (fun m => let ⟨m', hm'⟩ := (qzBasic l).1 _ hne m; ⟨m', by
      simp only [qzTw, scalRep] at hm' ⊢; rw [← hm', sub_smul, one_smul]; rfl⟩)
    z.2 (fun g hg => by
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
      exact congrFun hz ⟨h, ⟨trivial, by show cycZ F Ω l h = 1; rw [← hcomp]; exact hg⟩⟩)

private theorem qz_total (l : ℕ) [Fact l.Prime] (a b : QZ l) : ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
  obtain ⟨x, rfl⟩ : ∃ x, QZ.mk l x = a := Submodule.Quotient.mk_surjective (ZlSub l) a
  obtain ⟨y, rfl⟩ : ∃ y, QZ.mk l y = b := Submodule.Quotient.mk_surjective (ZlSub l) b
  have key : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := fun x y h => by
    by_cases hy : y = 0
    · subst hy; exact ⟨0, by simpa using h⟩
    · refine ⟨⟨x / y, by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩, ?_⟩
      show x = x / y * y; field_simp
  rcases le_total ‖x‖ ‖y‖ with h | h
  · obtain ⟨c, hc⟩ := key x y h; exact ⟨c, Or.inl (congrArg (QZ.mk l) hc)⟩
  · obtain ⟨c, hc⟩ := key y x h; exact ⟨c, Or.inr (congrArg (QZ.mk l) hc)⟩

private theorem len_le_one_of_simple_or_zero (l : ℕ) [Fact l.Prime] (K : Type) [AddCommGroup K]
    [Module ℤ_[l] K] (h1 : ∀ x : K, (l : ℤ_[l]) • x = 0)
    (h2 : ∀ a b : K, ∃ c : ℤ_[l], a = c • b ∨ b = c • a) : Module.length ℤ_[l] K ≤ 1 := by
  rcases subsingleton_or_nontrivial K with h | h
  · simp
  haveI : IsSimpleModule ℤ_[l] K := by
    rw [isSimpleModule_iff]
    refine ⟨fun N => or_iff_not_imp_left.2 fun hN => eq_top_iff.2 fun y _ => ?_⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    obtain ⟨c, hc | hc⟩ := h2 x y
    · by_cases hu : IsUnit c
      · obtain ⟨u, rfl⟩ := hu
        rw [show y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x by rw [hc, smul_smul, Units.inv_mul, one_smul]]
        exact N.smul_mem _ hx
      · have hm : c ∈ IsLocalRing.maximalIdeal ℤ_[l] := hu
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
        obtain ⟨d, rfl⟩ := hm
        rw [mul_smul, h1, smul_zero] at hc; exact absurd hc hx0
    · rw [hc]; exact N.smul_mem _ hx
  exact (Module.length_eq_one ℤ_[l] K).le

theorem resInfKer (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (he : e ≠ 0) :
    Module.length ℤ_[l] (LinearMap.ker (resInf D e)) ≤ errTwo l := by
  by_cases hP : Procyc F Ω l
  · rw [LinearMap.ker_eq_bot.2 (resInfInj F Ω l D e he hP)]; simp
  · rw [Procyc, not_or, not_not, not_forall] at hP
    obtain ⟨rfl, g, hg⟩ := hP
    have mul_mem_princ2 : ∀ u v : ℤ_[2]ˣ, u ∉ princ 2 2 → v ∉ princ 2 2 → u * v ∈ princ 2 2 := by
      have key : ∀ a b : (ZMod 4)ˣ, a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
      intro u v hu hv
      rw [princ, MonoidHom.mem_ker] at *
      rw [map_mul]; exact key _ _ hu hv
    have hg₀ : toGS Ω _ g ∉ (princ 2 2).comap D.chi := fun h =>
      hg (by rw [cycR, MonoidHom.comp_apply, ← DFunLike.congr_fun D.hchi g]; exact MonoidHom.mem_ker.1 h)
    have hH : ∀ a b, a ∉ (princ 2 2).comap D.chi → b ∉ (princ 2 2).comap D.chi →
        a * b ∈ (princ 2 2).comap D.chi := fun a b ha hb => by
      rw [Subgroup.mem_comap, map_mul]; exact mul_mem_princ2 _ _ ha hb
    have exists_vanish : ∀ (x : H1 (qzTw D e)), resInf D e x = 0 →
        ∃ z : Z1 (qzTw D e), x = Submodule.Quotient.mk z ∧
          ∀ h ∈ (princ 2 2).comap D.chi, z.1 h = 0 := by
      intro x hx
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      let H : Subgroup (G F Ω) := (princ 2 2).comap (cycZ F Ω 2)
      have hcl : IsClosed (H : Set (G F Ω)) := (princ_isClosed_val 2 2).preimage (continuous_cycZ F Ω 2)
      haveI : CompactSpace H := isCompact_iff_compactSpace.1 hcl.isCompact
      let χ : H →* ℤ_[2]ˣ := (cycZ F Ω 2).comp H.subtype
      have hχ : Continuous χ := (continuous_cycZ F Ω 2).comp continuous_subtype_val
      obtain ⟨_, ⟨γ, rfl⟩, hγ⟩ := existsGen 2 χ.range (isCompact_range hχ).isClosed
        (Or.inr (by rintro _ ⟨a, rfl⟩; exact a.2))
      have hne : χ γ ^ (-e) ≠ 1 := fun h => by
        obtain ⟨a, ha⟩ := exists_cyc_pow_ne_one 2 F Ω (2 * e.natAbs) (by omega)
        have ha2 : a * a ∈ H := by
          by_cases haH : a ∈ H
          · exact H.mul_mem haH haH
          · show cycZ F Ω 2 (a * a) ∈ princ 2 2; rw [map_mul]; exact mul_mem_princ2 _ _ haH haH
        have hc : IsClosed (((zpowGroupHom (-e) : ℤ_[2]ˣ →* ℤ_[2]ˣ).ker : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
          isClosed_singleton.preimage (continuous_zpow (-e))
        have h4 : (cycZ F Ω 2 (a * a)) ^ (-e) = 1 :=
          Subgroup.topologicalClosure_minimal _
            ((Subgroup.zpowers_le (H := (zpowGroupHom (-e) : ℤ_[2]ˣ →* ℤ_[2]ˣ).ker)).2 h) hc
            (hγ ⟨⟨_, ha2⟩, rfl⟩)
        apply ha; show cycZ F Ω 2 a ^ (2 * e.natAbs) = 1
        rw [pow_mul, sq, ← map_mul, pow_natAbs_eq_one, ← inv_eq_one, ← zpow_neg]; exact h4
      let φ : H →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := (toGS Ω _).comp H.subtype
      have hφ : Continuous φ := (continuous_toGS Ω _).comp continuous_subtype_val
      have hchi : ∀ a : H, D.chi (φ a) = χ a := fun a => DFunLike.congr_fun D.hchi a.1
      have hB := cobOfGen 2 H χ ℤ_[2] (QZ 2) ((qzTw D e).comp φ) γ hχ
        ((contTw F Ω 2 D e).1.comp (hφ.prodMap continuous_id))
        (fun a ha m => by show qzTw D e (φ a) m = m; rw [qzTw_apply, hchi, ha, one_zpow, Units.val_one, one_smul])
        (fun a => hγ ⟨a, rfl⟩)
        (fun m => by
          obtain ⟨a, ha⟩ := (qzBasic 2).1 (((χ γ ^ (-e) : ℤ_[2]ˣ) : ℤ_[2]) - 1)
            (fun h => hne (Units.ext (sub_eq_zero.1 h))) m
          exact ⟨a, by show qzTw D e (φ γ) a - a = m; rw [qzTw_apply, hchi, ← ha]; beta_reduce; rw [sub_smul, one_smul]⟩)
        ⟨z.2.1.comp hφ, fun a b => by show z.1 (φ (a * b)) = z.1 (φ a) + qzTw D e (φ a) (z.1 (φ b)); rw [map_mul, z.2.2]⟩
        (fun a ha => congrFun hx ⟨a.1, trivial, ha⟩)
      obtain ⟨m, hm⟩ := (mem_B1 _ _).1 hB
      have hb : d0 (qzTw D e) m ∈ B1 (qzTw D e) := ⟨m, rfl⟩
      have hbz : d0 (qzTw D e) m ∈ Z1 (qzTw D e) :=
        ⟨((contTw F Ω 2 D e).1.comp (continuous_id.prodMk continuous_const)).sub continuous_const,
         fun a b => by simp only [d0_apply, map_mul, Module.End.mul_apply, map_sub]; abel⟩
      refine ⟨z - ⟨d0 (qzTw D e) m, hbz⟩,
        (Submodule.Quotient.eq _).2 (by rw [sub_sub_cancel]; exact hb), fun a ha => ?_⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
      have ha' : a ∈ H := by show cycZ F Ω 2 a ∈ princ 2 2; rw [← DFunLike.congr_fun D.hchi a]; exact ha
      exact sub_eq_zero.2 (hm ⟨a, ha'⟩)
    have val_eq : ∀ (z : Z1 (qzTw D e)), (∀ a ∈ (princ 2 2).comap D.chi, z.1 a = 0) →
        ∀ {a b}, a ∉ (princ 2 2).comap D.chi → b ∉ (princ 2 2).comap D.chi → z.1 b = z.1 a := by
      intro z hz a b ha hb
      have h := z.2.2 a (a⁻¹ * b)
      rw [hz _ (hH _ _ (fun h' => ha ((inv_mem_iff).1 h')) hb), map_zero, add_zero, mul_inv_cancel_left] at h
      exact h
    rw [errTwo, if_pos rfl]
    refine len_le_one_of_simple_or_zero 2 _ (fun x => Subtype.ext ?_) fun a b => ?_
    · obtain ⟨z, hz, h0⟩ := exists_vanish x.1 x.2
      show ((2 : ℕ) : ℤ_[2]) • x.1 = 0
      rw [hz, Nat.cast_ofNat, ← Submodule.Quotient.mk_smul]
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨-z.1 (toGS Ω _ g), fun a => ?_⟩)
      show (2 : ℤ_[2]) • z.1 a = _
      by_cases ha : a ∈ (princ 2 2).comap D.chi
      · have h := z.2.2 a (toGS Ω _ g)
        rw [val_eq z h0 hg₀ (fun h' => hg₀ ((mul_mem_cancel_left ha).1 h')), h0 a ha, zero_add] at h
        rw [h0 a ha, map_neg, ← h, sub_self, smul_zero]
      · have h := z.2.2 a (toGS Ω _ g)
        rw [h0 _ (hH _ _ ha hg₀), val_eq z h0 hg₀ ha] at h
        rw [val_eq z h0 hg₀ ha, map_neg, two_smul, ← eq_neg_of_add_eq_zero_left h.symm, sub_neg_eq_add]
    · obtain ⟨z, hz, h0⟩ := exists_vanish a.1 a.2
      obtain ⟨z', hz', h0'⟩ := exists_vanish b.1 b.2
      have eq_smul : ∀ (z₁ z₂ : Z1 (qzTw D e)), (∀ h ∈ (princ 2 2).comap D.chi, z₁.1 h = 0) →
          (∀ h ∈ (princ 2 2).comap D.chi, z₂.1 h = 0) → ∀ c : ℤ_[2],
          z₁.1 (toGS Ω _ g) = c • z₂.1 (toGS Ω _ g) → z₁ = c • z₂ := fun z₁ z₂ h₁ h₂ c hc =>
        Subtype.ext (funext fun h => by
          show z₁.1 h = c • z₂.1 h
          by_cases hh : h ∈ (princ 2 2).comap D.chi
          · rw [h₁ h hh, h₂ h hh, smul_zero]
          · rw [val_eq z₁ h₁ hg₀ hh, val_eq z₂ h₂ hg₀ hh, hc])
      obtain ⟨c, hc | hc⟩ := qz_total 2 (z.1 (toGS Ω _ g)) (z'.1 (toGS Ω _ g))
      · exact ⟨c, Or.inl (Subtype.ext (by show a.1 = c • b.1; rw [hz, hz', eq_smul z z' h0 h0' c hc, Submodule.Quotient.mk_smul]))⟩
      · exact ⟨c, Or.inr (Subtype.ext (by show b.1 = c • a.1; rw [hz, hz', eq_smul z' z h0' h0 c hc, Submodule.Quotient.mk_smul]))⟩

theorem resInfConj (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) (σ : Ω ≃+* Ω) (h : IsLift τ σ)
    (x : H1 (qzTw D e)) (u u' : Uinf F Ω l) (hu : ∀ y, u'.1 (σ y) = σ (u.1 y)) :
    resInf D e (galoisActionOnCohomology D e τ x) u' = twScal l σ e • resInf D e x u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  have hc : conjGal h u'.1 = u.1 := AlgEquiv.ext fun y => by rw [conjGal_apply, hu, RingEquiv.symm_apply_apply]
  rw [galois_action_cohomology_eq_conj D e h, e₁, resInf_mk, resInf_mk, f₁, conjGS_toGS, hc]

private theorem resInfSign_eigen (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℕ)
    (σ : Ω ≃+* Ω) (h : IsConjOm σ) (s : ℤ_[l]) (hss : s * s = 1) (x : H1 (qzTw D (e : ℤ)))
    (hx : x ∈ Sha D (e : ℤ)) (hx' : x ∈ (cAct D e).eigenspace ((-1) ^ e * s)) :
    resInf D e x ∈ EqEig l (Uinf F Ω l) (qzG F Ω l e) σ s := by
  refine ⟨resInfMem F Ω l D e ⟨x, hx, rfl⟩, fun u u' huu => ?_⟩
  have h1 := resInfConj F Ω l D e (cE F) σ h.isLift x u u' huu
  rw [Module.End.mem_eigenspace_iff, cAct] at hx'
  rw [hx', twScal_conj (E := F) h, map_smul, Pi.smul_apply] at h1
  have hs : (-1 : ℤ_[l]) ^ e * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  have h2 := congrArg (fun m => (s * (-1 : ℤ_[l]) ^ e) • m) h1
  have k1 : s * (-1 : ℤ_[l]) ^ e * ((-1) ^ e * s) = 1 := by
    rw [mul_assoc, ← mul_assoc ((-1 : ℤ_[l]) ^ e), hs, one_mul, hss]
  have k2 : s * (-1 : ℤ_[l]) ^ e * (-1) ^ e = s := by rw [mul_assoc, hs, mul_one]
  simp only [smul_smul, k1, k2, one_smul] at h2
  exact h2

theorem resInfSign (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℕ) (σ : Ω ≃+* Ω)
    (h : IsConjOm σ) :
    (ShaPlus D e).map (resInf D e) ≤ EqEig l (Uinf F Ω l) (qzG F Ω l e) σ 1 ∧
    (ShaMinus D e).map (resInf D e) ≤ EqEig l (Uinf F Ω l) (qzG F Ω l e) σ (-1) :=
  ⟨fun _ ⟨x, hx, hEq⟩ => hEq ▸ resInfSign_eigen F Ω l D e σ h 1 (mul_one _) x hx.1 (by rw [mul_one]; exact hx.2),
   fun _ ⟨x, hx, hEq⟩ => hEq ▸ resInfSign_eigen F Ω l D e σ h (-1) (by simp) x hx.1 (by rw [← pow_succ]; exact hx.2)⟩

private theorem decCob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {e : ℤ} (he : e ≠ 0) (hP : Procyc F Ω l)
    {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} (hv : v ∈ Above F l)
    (hA : IsPlaceOver A v) {z : G F Ω → QZ l} (hz : z ∈ Z1 (qzG F Ω l e))
    (h0 : ∀ g ∈ Dec (F := F) A, cycZ F Ω l g = 1 → z g = 0) :
    ∃ m, ∀ g ∈ Dec (F := F) A, z g = qzG F Ω l e g m - m := by
  haveI : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.mp (isClosed_Dec A).isCompact
  let χ : Dec (F := F) A →* ℤ_[l]ˣ := (cycZ F Ω l).comp (Dec (F := F) A).subtype
  let ρ : Representation ℤ_[l] (Dec (F := F) A) (QZ l) := (qzG F Ω l e).comp (Dec (F := F) A).subtype
  have hV : IsClosed (decImage F l A : Set ℤ_[l]ˣ) := Subgroup.isClosed_of_isOpen _ (isOpen_decImage hv hA)
  have hVp : l ≠ 2 ∨ decImage F l A ≤ princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right; rintro _ ⟨g, -, rfl⟩
      have h1 := h g
      simp only [cycR, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map, Units.val_one] at h1
      rw [mem_princ]
      have h2 : PadicInt.toZModPow 2 ((cycZ F Ω l g : ℤ_[l]) - 1) = 0 := by
        rw [map_sub, map_one]; simpa using sub_eq_zero.mpr h1
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
      exact_mod_cast h2
  obtain ⟨γ', hγ'V, hgen'⟩ := existsGen l (decImage F l A) hV hVp
  obtain ⟨γ, hγ, hγχ⟩ := Subgroup.mem_map.mp hγ'V
  have hq : Continuous fun p : G F Ω × QZ l => qzG F Ω l e p.1 p.2 := contAction_qzG F Ω l e
  have hpm : Continuous fun p : Dec (F := F) A × QZ l => ((p.1 : G F Ω), p.2) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hρc : ContAction ρ := (hq.comp hpm).congr fun p => by
    simp only [ρ, Function.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have hχc : Continuous χ := ((continuous_cycZ F Ω l).comp continuous_subtype_val).congr fun g => by
    simp only [χ, Function.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
  have hne : (cycZ F Ω l γ) ^ (-e) ≠ 1 := fun h1 => by
    obtain ⟨g, hg, hg1⟩ := exists_mem_Dec_cycZ_zpow_ne_one F Ω l v A hv hA (-e) (neg_ne_zero.mpr he)
    let K : Subgroup ℤ_[l]ˣ := (zpowGroupHom (-e) : ℤ_[l]ˣ →* ℤ_[l]ˣ).ker
    have hK : IsClosed (K : Set ℤ_[l]ˣ) := by
      rw [show (K : Set ℤ_[l]ˣ) = {x : ℤ_[l]ˣ | x ^ (-e) = 1} by ext; simp [K]]
      exact isClosed_eq (continuous_zpow (-e)) continuous_const
    have hzK : Subgroup.zpowers γ' ≤ K := by
      rw [Subgroup.zpowers_le, MonoidHom.mem_ker, zpowGroupHom_apply, ← hγχ]; exact h1
    exact hg1 (Subgroup.topologicalClosure_minimal _ hzK hK (hgen' (Subgroup.mem_map_of_mem _ hg)))
  have htriv_dec : ∀ g : Dec (F := F) A, χ g = 1 → ∀ m : QZ l, ρ g m = m := fun g hg m => by
    simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype] at hg
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, qzG_apply, hg, one_zpow, Units.val_one, one_smul]
  have hgen_dec : ∀ g : Dec (F := F) A, χ g ∈ (Subgroup.zpowers (χ ⟨γ, hγ⟩)).topologicalClosure := fun g => by
    have h1 : χ ⟨γ, hγ⟩ = γ' := hγχ
    rw [h1]
    exact hgen' (Subgroup.mem_map_of_mem _ g.2)
  have hsurj_dec : Function.Surjective (fun x : QZ l => ρ ⟨γ, hγ⟩ x - x) := fun y => by
    obtain ⟨x, hx⟩ := (qzBasic l).1 (((cycZ F Ω l γ ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1)
      (fun h0' => hne (Units.val_eq_one.mp (sub_eq_zero.mp h0'))) y
    exact ⟨x, by simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, qzG_apply]; rw [← hx]; beta_reduce; rw [sub_smul, one_smul]⟩
  have hz_dec : (fun g : Dec (F := F) A => z g.1) ∈ Z1 ρ :=
    ⟨hz.1.comp continuous_subtype_val, fun a b => by
      have := hz.2 a.1 b.1
      simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul]
      exact this⟩
  have hB := cobOfGen l (Dec (F := F) A) χ ℤ_[l] (QZ l) ρ ⟨γ, hγ⟩ hχc hρc
    htriv_dec hgen_dec hsurj_dec hz_dec (fun g hg => h0 g.1 g.2 (by simpa [χ] using hg))
  obtain ⟨m, hm⟩ := (mem_B1 ρ _).mp hB
  exact ⟨m, fun g hg => by have := hm ⟨g, hg⟩; simpa [ρ] using this⟩

theorem resInfOnto (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ) (he : e ≠ 0) (hP : Procyc F Ω l) :
    (Sha D e).map (resInf D e) = EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  apply le_antisymm (resInfMem F Ω l D e)
  intro φ hφ
  have hX := (Submodule.mem_inf.mp hφ).1
  have hC := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hφ).2
  have hmemU : ∀ g : G F Ω, cycZ F Ω l g = 1 → g ∈ Uinf F Ω l := fun g hg => ⟨trivial, hg⟩
  have htriv : ∀ u ∈ Uinf F Ω l, ∀ m, qzG F Ω l e u m = m := fun u hu m => by
    rw [qzG_apply, hu.2, one_zpow, Units.val_one, one_smul]
  obtain ⟨z, hz, hzφ⟩ := extCocycle F Ω l ℤ_[l] (QZ l) (qzG F Ω l e) φ hP (contAction_qzG F Ω l e) htriv
    (qzBasic l).2.1 hX.1 hX.2.1 hC
  have hρ' : (qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) = qzG F Ω l e :=
    qzTw_comp_toGS F Ω l D e
  have hz' : z ∈ Z1 ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))) := hρ' ▸ hz
  have hsha := shaInfl F Ω D.S D.A D.hA ℤ_[l] (QZ l) (qzTw D e)
  have hmk : (Submodule.Quotient.mk ⟨z, hz'⟩ : H1 ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))))) ∈
      ShaAbs ((qzTw D e).comp (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))))
        (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
    rw [mk_mem_ShaAbs]
    refine ⟨fun v hv A hA => ?_, fun v hv A hA => ⟨0, fun g hg => ?_⟩⟩
    · rw [D.hS] at hv
      have hAl : A.valuation (l : Ω) < 1 := ((placeDict F Ω).2.2.2 A v l hA).mpr hv
      obtain ⟨m, hm⟩ := decCob he hP hv hA hz (fun g hg hg1 => by
        rw [show z g = φ ⟨g, hmemU g hg1⟩ from hzφ ⟨g, hmemU g hg1⟩]
        exact hX.2.2.2 A hAl ⟨g, hmemU g hg1⟩ hg)
      exact ⟨m, fun g hg => by
        change z g = ((qzTw D e).comp (toGS Ω _)) g m - m
        rw [hρ']; exact hm g hg⟩
    · have hgN : g ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
        Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
          (Set.mem_biUnion (x := v) hv (Set.mem_biUnion (x := A) hA hg)))
      have hg1 : cycZ F Ω l g = 1 := by
        have hq1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := (QuotientGroup.eq_one_iff g).mpr hgN
        rw [← DFunLike.congr_fun D.hchi g, MonoidHom.comp_apply, hq1, map_one]
      simp only [map_zero, sub_zero]
      rw [show z g = φ ⟨g, hmemU g hg1⟩ from hzφ ⟨g, hmemU g hg1⟩]
      exact hX.2.2.1 A ⟨g, hmemU g hg1⟩ hg
  rw [← hsha] at hmk
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp hmk
  refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (restrictCocycles1 (qzTw D e) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) _ w) =
    Submodule.Quotient.mk ⟨z, hz'⟩ at hyz
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_B1] at hyz
  obtain ⟨m, hm⟩ := hyz
  funext u
  have h1 : w.1 (toGS Ω _ u.1) - z u.1 = ((qzTw D e).comp (toGS Ω _)) u.1 m - m := hm u.1
  rw [hρ', htriv u u.2, sub_self, sub_eq_zero] at h1
  rw [resInf_mk, ← hzφ u]
  exact h1

end ResInfSection

/-! ## Section 6: Unconditional `EqHom`/`EqEig` Length Bounds, Local Place-Lift Helpers, Hilbert Class Field Artin Pullback (`Art*`, `Pull*`, `ShaFrom`, `MinusLenLeOfCl`), and `realGaloisSelmerSystem` Bridges -/

section ArtinPullbackAndLimits

section UnconditionalLimits

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

omit [IsAlgClosure F Ω] in
theorem levU_anti (U : Subgroup (G F Ω)) {m n : ℕ} (h : m ≤ n) : levU l U n ≤ levU l U m :=
  inf_le_inf_left _ (Subgroup.comap_mono (princ_anti h))

omit [IsAlgClosure F Ω] in
theorem len_le_of_layers (U : Subgroup (G F Ω)) (W : Submodule R (cycU l U → M))
    (P : ∀ n, Submodule R (levU l U n → M))
    (hP : ∀ m n (h : m ≤ n), (P m).map (restr R M (levU_anti U h)) ≤ P n)
    (hW : ∀ φ ∈ W, ∃ n, ∃ ψ ∈ P n, restr R M (cycU_le_levU l U n) ψ = φ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (P n) ≤ Bd) : Module.length R W ≤ Bd := by
  refine lenDirected R _ W (fun n => (P n).map (restr R M (cycU_le_levU l U n))) Bd ?_ ?_ ?_
  · rintro m n h _ ⟨ψ, hψ, rfl⟩; exact ⟨_, hP m n h ⟨ψ, hψ, rfl⟩, rfl⟩
  · intro φ hφ; obtain ⟨n, ψ, hψ, rfl⟩ := hW φ hφ; exact Submodule.mem_iSup_of_mem n ⟨ψ, hψ, rfl⟩
  · intro n₀; obtain ⟨n, h, hn⟩ := hB n₀
    exact ⟨n, h, (Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)).trans hn⟩

theorem galOf_Fn (n : ℕ) : galOf F (Fn F Ω l n) Ω = Un F Ω l n := by
  haveI := (fnCyc F Ω l n).1
  rw [galOfCyc F Ω l n F (Fn F Ω l n), galOf_self]

omit [NumberField F] in
theorem length_map_le {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (N : Submodule R X) : Module.length R (N.map f) ≤ Module.length R N :=
  Module.length_le_of_surjective _ (LinearMap.submoduleMap_surjective f N)

theorem length_le_map_add {X Y : Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (N : Submodule R X) :
    Module.length R N ≤ Module.length R (N.map f) + Module.length R (LinearMap.ker f) := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker (f.submoduleMap N)).subtype (f.submoduleMap N)
    (Submodule.subtype_injective _) (LinearMap.submoduleMap_surjective f N)
    (LinearMap.exact_subtype_ker_map _), add_comm]
  exact add_le_add le_rfl (Module.length_le_of_injective
    (LinearMap.codRestrict _ (N.subtype.comp (LinearMap.ker (f.submoduleMap N)).subtype)
      fun x => congrArg Subtype.val x.2)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : LinearMap.ker f => (z : X)) h)))

private theorem princ_smul_eq_self_of_pow_smul_eq_zero {k : ℕ} {x : QZ l} (hx : l ^ k • x = 0)
    {w : ℤ_[l]ˣ} (hw : w ∈ princ l k) : (w : ℤ_[l]) • x = x := by
  obtain ⟨c, hc⟩ := (mem_princ (l := l)).1 hw
  have h1 : ((w : ℤ_[l]) - 1) • x = 0 := by
    rw [hc, mul_comm ((l : ℤ_[l]) ^ k) c, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hx, smul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem locConst_qzG (e : ℤ) (m : QZ l) : IsLocallyConstant fun g => qzG F Ω l e g m := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  obtain ⟨k, hk⟩ := (qzBasic l).2.1 m
  have hc : Continuous fun g => cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ :=
    (continuous_cycZ F Ω l).mul continuous_const
  have hmem : ∀ᶠ g in nhds g0, cycZ F Ω l g * (cycZ F Ω l g0)⁻¹ ∈ princ l k :=
    hc.continuousAt.preimage_mem_nhds
      ((isOpen_princ k).mem_nhds (by simp only [mul_inv_cancel]; exact (princ l k).one_mem))
  filter_upwards [hmem] with g hg
  show ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m = ((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m
  have hw : (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) ∈ princ l k := zpow_mem hg _
  have hx : l ^ k • (((cycZ F Ω l g0 ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m) = 0 := by
    rw [smul_comm, hk, smul_zero]
  have key : cycZ F Ω l g ^ (-e) = (cycZ F Ω l g * (cycZ F Ω l g0)⁻¹) ^ (-e) * cycZ F Ω l g0 ^ (-e) := by
    rw [← mul_zpow, inv_mul_cancel_right]
  rw [key, Units.val_mul, mul_smul, princ_smul_eq_self_of_pow_smul_eq_zero hx hw]

theorem len_le_of_resInf (D : LData F Ω l) {e : ℤ} (he : e ≠ 0)
    (N : Submodule ℤ_[l] (H1 (qzTw D e))) (W : Submodule ℤ_[l] (Uinf F Ω l → QZ l))
    (h : N.map (resInf D e) ≤ W) :
    Module.length ℤ_[l] N ≤ Module.length ℤ_[l] W + errTwo l :=
  (length_le_map_add (resInf D e) N).trans
    (add_le_add (Module.length_le_of_injective _ (Submodule.inclusion_injective h))
      (resInfKer F Ω l D e he))

theorem shaLen_le_eqHom (D : LData F Ω l) {e : ℤ} (he : e ≠ 0) :
    shaLen D e ≤ Module.length ℤ_[l] (EqHom l (Uinf F Ω l) (qzG F Ω l e)) + errTwo l :=
  len_le_of_resInf D he _ _ (resInfMem F Ω l D e)

theorem galoisShaLen_le_eqHom (F : Type) [Field F] [NumberField F] (p : Nat.Primes) {e : ℤ}
    (he : e ≠ 0) :
    galoisShaLen F p e ≤
      Module.length ℤ_[p.1] (EqHom p.1 (Uinf F (AlgebraicClosure F) p.1) (qzG F (AlgebraicClosure F) p.1 e)) +
        errTwo p.1 := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  rw [← shaInv_eq_galoisShaLen F p e,
    ← shaLen_eq_shaInv (F := F) (Ω := AlgebraicClosure F) (l := p.1) (D := canonicalLData F p) e]
  exact shaLen_le_eqHom _ he

theorem realGaloisSelmerSystem_shaLen_le_eqHom (F : Type) [Field F] [NumberField F] (p : Nat.Primes)
    {e : ℕ} (he : e ≠ 0) :
    realGaloisSelmerSystem.shaLen F p e ≤
      Module.length ℤ_[p.1] (EqHom p.1 (Uinf F (AlgebraicClosure F) p.1) (qzG F (AlgebraicClosure F) p.1 e)) +
        errTwo p.1 :=
  galoisShaLen_le_eqHom F p (by exact_mod_cast he)

variable [IsCMField F]

theorem plusLen_le_eqEig (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) :
    plusLen D e ≤ Module.length ℤ_[l] (EqEig l (Uinf F Ω l) (qzG F Ω l e) σ 1) + errTwo l :=
  len_le_of_resInf D (by exact_mod_cast he) _ _ (resInfSign F Ω l D e σ hσ).1

theorem minusLen_le_eqEig (D : LData F Ω l) {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) :
    minusLen D e ≤ Module.length ℤ_[l] (EqEig l (Uinf F Ω l) (qzG F Ω l e) σ (-1)) + errTwo l :=
  len_le_of_resInf D (by exact_mod_cast he) _ _ (resInfSign F Ω l D e σ hσ).2

theorem galoisPlusLen_le_eqEig (F : Type) [Field F] [NumberField F] [IsCMField F] (p : Nat.Primes)
    {e : ℕ} (he : e ≠ 0) {σ : AlgebraicClosure F ≃+* AlgebraicClosure F} (hσ : IsConjOm σ) :
    galoisPlusLen F p e ≤
      Module.length ℤ_[p.1] (EqEig p.1 (Uinf F (AlgebraicClosure F) p.1) (qzG F (AlgebraicClosure F) p.1 e) σ 1) +
        errTwo p.1 := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  exact plusLen_le_eqEig _ he hσ

theorem galoisMinusLen_le_eqEig (F : Type) [Field F] [NumberField F] [IsCMField F] (p : Nat.Primes)
    {e : ℕ} (he : e ≠ 0) {σ : AlgebraicClosure F ≃+* AlgebraicClosure F} (hσ : IsConjOm σ) :
    galoisMinusLen F p e ≤
      Module.length ℤ_[p.1] (EqEig p.1 (Uinf F (AlgebraicClosure F) p.1) (qzG F (AlgebraicClosure F) p.1 e) σ (-1)) +
        errTwo p.1 := by
  haveI : Fact p.1.Prime := ⟨p.2⟩
  exact minusLen_le_eqEig _ he hσ

end UnconditionalLimits

section LocalArtinHelpers

/-- Unconditional place-between lemma (`ArtFrob` helper): any valuation ring `A` of `Ω` lying over
`v` on `K` induces a height-one prime `w` on any intermediate number field `L` lying over `v`. -/
theorem place_between {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  classical
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x =>
    mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap
  let f : 𝓞 L →+* A :=
    { toFun := fun x => ⟨algebraMap L Ω (x : L), hint x⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  have hmem : ∀ x : 𝓞 L, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔
      A.valuation (algebraMap L Ω (x : L)) < 1 := fun x => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]; rfl
  have hv : ∀ y : 𝓞 K, algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) y : 𝓞 L) : L) =
      algebraMap K Ω (y : K) := fun y => by rw [IsScalarTower.algebraMap_apply K L Ω]; congr 1
  obtain ⟨y, hyv, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hyP : algebraMap (𝓞 K) (𝓞 L) y ∈ (IsLocalRing.maximalIdeal A).comap f := by
    rw [hmem, hv]; exact (hA y).mpr hyv
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, Ideal.comap_isPrime f _, fun h => hy0 ?_⟩,
    fun x => (hmem x).symm, ⟨Ideal.ext fun z => by
      change z ∈ v.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) z ∈ (IsLocalRing.maximalIdeal A).comap f
      rw [hmem, hv]; exact (hA z).symm⟩⟩
  rw [h, Ideal.mem_bot] at hyP
  have h1 : algebraMap K Ω (y : K) = 0 := by rw [← hv, hyP]; simp
  exact_mod_cast (map_eq_zero_iff _ (algebraMap K Ω).injective).mp h1

/-- Unconditional Frobenius restriction (`ArtFrob` helper). -/
theorem res_frob {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsGalois K L]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal] {σ : G K Ω}
    (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  have hq : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) = normV v := by rw [← h.over]; rfl
  intro x
  rw [hq]
  refine (hw _).mp ?_
  have hcoe : algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) =
      σ (algebraMap L Ω (x : L)) := AlgEquiv.restrictNormal_commutes σ L (x : L)
  simp only [MulSemiringAction.toAlgHom_apply, map_sub, map_pow, hcoe]
  exact hσ.2 _ ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap))

/-- Unconditional inertia lift (`ArtKer` helper): every element of finite-level inertia lifts to
absolute inertia `Ine (F := E) A` for a valuation subring `A` over `w`. -/
theorem lift_ine_over {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (τ : L ≃ₐ[E] L) (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[E] L)) :
    ∃ (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω),
      AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := E) A := by
  haveI : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hw⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 Ω) w.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 Ω))]
    exact bot_le)
  obtain ⟨A, rfl⟩ := exists_cen Q
  obtain ⟨φ, h1, h2⟩ := cen_lift L (cen A) τ (RingHom.id _) fun x => by
    rw [RingHom.id_apply, Ideal.Quotient.eq, ← map_sub]
    exact (Ideal.mem_comap (f := algebraMap (𝓞 L) (𝓞 Ω))).1
      (hw.ge (by simpa [neg_sub] using w.asIdeal.neg_mem (hτ x)))
  obtain ⟨h3, h4⟩ := cen_of_cong A φ one_ne_zero fun b => by
    rw [pow_one]; exact Ideal.Quotient.eq.1 (h2 b)
  exact ⟨A, φ, h1, h3, fun x hx => by
    simpa using (A.mem_nonunits_iff).1 (h4 x ((A.valuation_le_one_iff _).1 hx))⟩

/-- Unconditional complex-conjugation lift (`ArtKer` helper). -/
theorem exists_conj_lift {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (L : IntermediateField E Ω) (j₀ : L →+* ℂ)
    (hE : ComplexEmbedding.IsReal (j₀.comp (algebraMap E L))) :
    ∃ c : Ω ≃ₐ[E] Ω, IsConjOm c.toRingEquiv ∧ ∀ x : L, c x = x → starRingEnd ℂ (j₀ x) = j₀ x := by
  letI : Algebra L ℂ := j₀.toAlgebra
  letI : Algebra E ℂ := (j₀.comp (algebraMap E L)).toAlgebra
  haveI : IsScalarTower E L ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := E) L
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  let j : Ω →ₐ[L] ℂ := IsAlgClosed.lift
  let j₁ : Ω →ₐ[E] ℂ := j.restrictScalars E
  let j₂ : Ω →ₐ[E] ℂ :=
    { (starRingEnd ℂ).comp j₁.toRingHom with
      commutes' := fun y => by
        show starRingEnd ℂ (j₁ (algebraMap E Ω y)) = _
        rw [j₁.commutes]
        exact DFunLike.congr_fun (ComplexEmbedding.isReal_iff.1 hE) y }
  letI : Algebra Ω ℂ := j₁.toRingHom.toAlgebra
  haveI : IsScalarTower E Ω ℂ := IsScalarTower.of_algebraMap_eq fun y => (j₁.commutes y).symm
  have hc : ∀ x, j₁ (j₂.restrictNormal' Ω x) = starRingEnd ℂ (j₁ x) := fun x =>
    j₂.restrictNormal_commutes Ω x
  refine ⟨j₂.restrictNormal' Ω, ⟨j₁.toRingHom, hc⟩, fun x hx => ?_⟩
  have := hc x
  rw [hx] at this
  have e : j₁ x = j₀ x := j.commutes x
  rw [← e]
  exact this.symm

end LocalArtinHelpers

section HilbertArtinReciprocityPullback

/-- **Exact Hilbert Class Field Artin Reciprocity Specification (`HilbertArtinData K Ω`)**:
the 4 concrete properties (`artSurj`, `artIne`, `artFrob`, `artKer`) of the Hilbert Class Field
Artin reciprocity homomorphism `artCl : G K Ω →* ClassGroup (𝓞 K)` from global idelic Class Field
Theory (`GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField`, ~60k lines not yet in
Mathlib `v4.33.1`). Every Artin pullback theorem (`artConj`, `artDec`, `pullMem`, `pullOnto`,
`pullCond`, `pullEq`, `shaZm`, `eqHom_le_of_cl`, `eqEig_le_of_cl`, `shaLen_le_of_cl`,
`plusLen_le_of_cl`, `minusLen_le_of_cl`) is proved unconditionally from this exact interface. -/
structure HilbertArtinData (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] where
  artCl : G K Ω →* ClassGroup (𝓞 K)
  surj : Function.Surjective artCl
  locConst : IsLocallyConstant artCl
  ine_eq_one : ∀ (A : ValuationSubring Ω) (g : G K Ω), g ∈ Ine (F := K) A → artCl g = 1
  conj_eq_one : ∀ c : G K Ω, IsConjOm c.toRingEquiv → artCl c = 1
  frob : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω),
    IsPlaceOver A v → IsFrob (F := K) A (normV v) σ → artCl σ = primeCl v
  ker_le : ∀ (C : Type) [CommGroup C] (χ : G K Ω →* C),
    IsOpen (χ.ker : Set (G K Ω)) →
    (∀ A : ValuationSubring Ω, Ine (F := K) A ≤ χ.ker) →
    (∀ c : G K Ω, IsConjOm c.toRingEquiv → χ c = 1) →
    artCl.ker ≤ χ.ker

section PullbackDefs

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
  (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] {U : Subgroup (G F Ω)}

def artU (hArt : HilbertArtinData K Ω) (hU : U ≤ galOf F K Ω) : U →* ClassGroup (𝓞 K) :=
  hArt.artCl.comp (toGal K hU)

def clPull (hArt : HilbertArtinData K Ω) (hU : U ≤ galOf F K Ω) (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] : (ClassGroup (𝓞 K) → M) →ₗ[R] (U → M) :=
  LinearMap.funLeft R M (artU K hArt hU)

theorem clPull_apply (hArt : HilbertArtinData K Ω) (hU : U ≤ galOf F K Ω) (R M : Type)
    [CommRing R] [AddCommGroup M] [Module R M] (θ : ClassGroup (𝓞 K) → M) (u : U) :
    clPull K hArt hU R M θ u = θ (hArt.artCl (toGal K hU u)) := rfl

end PullbackDefs

private theorem comap_val_lt_one_iff {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (σ : Ω ≃+* Ω)
    (x : Ω) : (A.comap (σ : Ω →+* Ω)).valuation x < 1 ↔ A.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff']
  simp [ValuationSubring.mem_comap, map_inv₀]

private theorem isFrob_comap_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {τ : K ≃+* K} {σ : Ω ≃+* Ω} (h : IsLift τ σ) (A : ValuationSubring Ω) (q : ℕ) (g : G K Ω)
    (hg : IsFrob A q g) : IsFrob (A.comap (σ : Ω →+* Ω)) q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h (fun _ => Iff.rfl) hg.1, fun x hx => ?_⟩
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap] at hx
  rw [comap_val_lt_one_iff, map_sub, map_pow, conjGal_apply, RingEquiv.apply_symm_apply]
  exact hg.2 (σ x) ((A.valuation_le_one_iff _).2 hx)

theorem artConj (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (hArt : HilbertArtinData K Ω) (τ : K ≃+* K) (σ : Ω ≃+* Ω) (h : IsLift τ σ) (g : G K Ω) :
    hArt.artCl g = clMap τ (hArt.artCl (conjGal h g)) := by
  set ψ : G K Ω →* ClassGroup (𝓞 K) := (clMap τ).comp (hArt.artCl.comp (conjGal h))
  have hker : hArt.artCl.ker ≤ ψ.ker := by
    refine hArt.ker_le _ ψ ?_ ?_ ?_
    · rw [MonoidHom.coe_ker]
      exact ((hArt.locConst.comp_continuous (continuous_conjGal h)).comp (clMap τ)).isOpen_fiber 1
    · intro A x hx
      rw [MonoidHom.mem_ker]
      show clMap τ (hArt.artCl (conjGal h x)) = 1
      rw [hArt.ine_eq_one (A.comap (σ : Ω →+* Ω)) _ (conjGal_mem_Ine h (fun _ => Iff.rfl) hx), map_one]
    · intro c ⟨j, hj⟩
      show clMap τ (hArt.artCl (conjGal h c)) = 1
      have hc' : IsConjOm (conjGal h c).toRingEquiv := ⟨j.comp (σ : Ω →+* Ω), fun x => by
        simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
          conjGal_apply, RingEquiv.apply_symm_apply]
        exact hj (σ x)⟩
      rw [hArt.conj_eq_one _ hc', map_one]
  have hsame : ∀ g₁ g₂, hArt.artCl g₁ = hArt.artCl g₂ → ψ g₁ = ψ g₂ := fun g₁ g₂ he => by
    have hm' : g₁ * g₂⁻¹ ∈ ψ.ker := hker (show hArt.artCl (g₁ * g₂⁻¹) = 1 by
      rw [map_mul, map_inv, he, mul_inv_cancel])
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hm'
    exact hm'
  have hall : ∀ c : ClassGroup (𝓞 K), ∃ x, hArt.artCl x = c ∧ ψ x = c := fun c => by
    have hc : c ∈ Subgroup.closure (primeCl '' (Set.univ : Set (HeightOneSpectrum (𝓞 K)))) := by
      have hu := clSubUniv K; rw [clSub] at hu; rw [hu]; exact Subgroup.mem_top c
    refine Subgroup.closure_induction (p := fun c _ => ∃ x, hArt.artCl x = c ∧ ψ x = c)
      ?_ ⟨1, map_one _, map_one _⟩
      (fun _ _ _ _ ⟨ga, ha1, ha2⟩ ⟨gb, hb1, hb2⟩ => ⟨ga * gb, by rw [map_mul, ha1, hb1], by rw [map_mul, ha2, hb2]⟩)
      (fun _ _ ⟨ga, h1, h2⟩ => ⟨ga⁻¹, by rw [map_inv, h1], by rw [map_inv, h2]⟩) hc
    rintro _ ⟨v, -, rfl⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨f, hf⟩ := exists_isFrob hA
    refine ⟨f, hArt.frob A v f hA hf, ?_⟩
    let τO := RingOfIntegers.mapRingEquiv τ
    let v' : HeightOneSpectrum (𝓞 K) := v.comap (τO : 𝓞 K →+* 𝓞 K) τO.surjective
    have hA' : IsPlaceOver (A.comap (σ : Ω →+* Ω)) v' := fun x => by
      rw [comap_val_lt_one_iff, h]; exact hA (τO x)
    have hn : normV v' = normV v :=
      Nat.card_congr (Ideal.quotientEquiv v'.asIdeal v.asIdeal τO
        (Ideal.map_comap_of_surjective _ τO.surjective _).symm).toEquiv
    have hF' : IsFrob (A.comap (σ : Ω →+* Ω)) (normV v') (conjGal h f) :=
      hn ▸ isFrob_comap_conjGal h A _ f hf
    show clMap τ (hArt.artCl (conjGal h f)) = primeCl v
    rw [hArt.frob _ v' _ hA' hF', primeCl, primeCl, class_map_mk0]
    congr 1; exact Subtype.ext (Ideal.map_comap_of_surjective _ τO.surjective _)
  obtain ⟨g₀, h1, h2⟩ := hall (hArt.artCl g)
  show hArt.artCl g = ψ g
  rw [hsame g g₀ h1.symm, h2]

theorem artDec (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (hArt : HilbertArtinData K Ω) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (hA : IsPlaceOver A v) : (Dec (F := K) A).map hArt.artCl = Subgroup.zpowers (primeCl v) := by
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  have hσv : hArt.artCl σ = primeCl v := hArt.frob A v σ hA hσ
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine decGen K Ω A v σ _ hA hσ
      (hArt.locConst (Subgroup.zpowers (primeCl v) : Set (ClassGroup (𝓞 K))))
      (fun g hg => by rw [Subgroup.mem_comap, hArt.ine_eq_one A g hg]; exact one_mem _)
      (by rw [Subgroup.mem_comap, hσv]; exact Subgroup.mem_zpowers _)
  · rw [Subgroup.zpowers_le]; exact ⟨σ, hσ.1, hσv⟩

theorem pullMem (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (hArt : HilbertArtinData K Ω) (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω)
    (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (hN : N ≠ 0) :
    (ClDual K N R M).map (clPull K hArt hU R M) ≤ XDual N U R M ∧
    (galOf F K Ω ≤ U → Function.Injective (clPull K hArt hU R M)) := by
  obtain ⟨hD, hI, hc, hH⟩ := toGalDict F Ω K U hU
  obtain ⟨-, hP, hT, hA⟩ := placeDict K Ω
  refine ⟨?_, fun h => LinearMap.funLeft_injective_of_surjective R M _ (hArt.surj.comp (hH h).1.surjective)⟩
  rintro _ ⟨θ, ⟨hm, hv⟩, rfl⟩
  let θ' : ClassGroup (𝓞 K) →* Multiplicative M :=
    MonoidHom.mk' (fun c => Multiplicative.ofAdd (θ c)) fun a b => by rw [hm, ofAdd_add]
  have h1 : θ 1 = 0 := congrArg Multiplicative.toAdd θ'.map_one
  refine ⟨(hArt.locConst.comp_continuous hc).comp θ,
    fun a b => by rw [clPull_apply, clPull_apply, clPull_apply, map_mul, map_mul, hm],
    fun A u hu => by rw [clPull_apply, hArt.ine_eq_one A _ ((hI A u).2 hu), h1],
    fun A hAN u hu => ?_⟩
  obtain ⟨v, hAv⟩ := hP A (hT A N hN hAN)
  have hmem : hArt.artCl (toGal K hU u) ∈ Subgroup.zpowers (primeCl v) := by
    rw [← artDec K Ω hArt A v hAv]; exact Subgroup.mem_map_of_mem _ ((hD A u).2 hu)
  have hle : Subgroup.zpowers (primeCl v) ≤ θ'.ker := by
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    exact congrArg Multiplicative.ofAdd (hv v ((hA A v N hAv).1 hAN))
  exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 (hle hmem))

theorem pullOnto (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (hArt : HilbertArtinData K Ω) (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω)
    (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (hN : N ≠ 0)
    (hU' : galOf F K Ω ≤ U) (hK : IsTotallyComplex K ∨ ∀ m : M, 2 • m = 0 → m = 0) :
    (ClDual K N R M).map (clPull K hArt hU R M) = XDual N U R M := by
  refine le_antisymm (pullMem F Ω K hArt U hU N R M hN).1 fun φ ⟨hlc, hadd, hI, hD⟩ => ?_
  obtain ⟨hDec, hIne, -, -⟩ := toGalDict F Ω K U hU
  obtain ⟨hE, -, -⟩ := galEmbTop F K Ω
  let ι : G K Ω →* U := (galEmb F K Ω).codRestrict U fun σ => hU' (galEmb_mem F K Ω σ)
  have hι : Continuous ι := hE.continuous.subtype_mk _
  have h1 : ∀ σ, toGal K hU (ι σ) = σ := fun _ => AlgEquiv.ext fun _ => rfl
  have h2 : ∀ u, ι (toGal K hU u) = u := fun _ => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  let φ' : U →* Multiplicative M :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (φ u)) fun a b => by rw [hadd, ofAdd_add]
  let χ : G K Ω →* Multiplicative M := φ'.comp ι
  have hχ : ∀ σ, χ σ = 1 ↔ φ (ι σ) = 0 := fun _ => Iff.rfl
  have hker : hArt.artCl.ker ≤ χ.ker := by
    refine hArt.ker_le (Multiplicative M) χ ((hlc.comp_continuous hι).isOpen_fiber 0)
      (fun A σ hσ => (hχ σ).2 (hI A _ ((hIne A _).1 ((h1 σ).symm ▸ hσ)))) fun c ⟨j, hj⟩ => ?_
    rcases hK with hK | hK
    · refine absurd ?_ (InfinitePlace.not_isReal_iff_isComplex.2
        (hK.isComplex (InfinitePlace.mk (j.comp (algebraMap K Ω)))))
      rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
      ext x
      have := hj (algebraMap K Ω x)
      rw [show c.toRingEquiv (algebraMap K Ω x) = algebraMap K Ω x from c.commutes x] at this
      exact this.symm
    · have hcc : c * c = 1 := AlgEquiv.ext fun x => j.injective
        ((hj (c x)).trans ((congrArg _ (hj x)).trans (Complex.conj_conj _)))
      have e : χ c * χ c = 1 := by rw [← map_mul, hcc, map_one]
      exact (hχ c).2 (hK _ (by rw [two_nsmul]; exact e))
  let θ := MonoidHom.liftOfSurjective hArt.artCl hArt.surj ⟨χ, hker⟩
  have hθ : ∀ σ, θ (hArt.artCl σ) = χ σ := fun σ =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨χ, hker⟩ σ
  refine ⟨fun c => Multiplicative.toAdd (θ c),
    ⟨fun a b => congrArg Multiplicative.toAdd (θ.map_mul a b), fun v hv => ?_⟩,
    funext fun u => by rw [clPull_apply, hθ]; exact congrArg φ (h2 u)⟩
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨σ, hσ⟩ := exists_isFrob hA
  show Multiplicative.toAdd (θ (primeCl v)) = 0
  rw [← hArt.frob A v σ hA hσ, hθ]
  exact hD A (((placeDict K Ω).2.2.2 A v N hA).2 hv) _ ((hDec A _).1 ((h1 σ).symm ▸ hσ.1))

theorem pullCond (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] (hArt : HilbertArtinData K Ω) (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω)
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (τ : K ≃+* K) (σ : Ω ≃+* Ω)
    (T : M →ₗ[R] M) (θ : ClassGroup (𝓞 K) → M) (hU' : galOf F K Ω ≤ U) (h : IsLift τ σ) :
    θ ∈ clCond K σ T ↔ clPull K hArt hU R M θ ∈ conjCond U σ T := by
  constructor
  · intro hθ u u' huu
    have e : conjGal h (toGal K hU u') = toGal K hU u :=
      AlgEquiv.ext fun x => σ.injective ((apply_conjGal h _ x).trans (huu x))
    rw [clPull_apply, clPull_apply, artConj K Ω hArt τ σ h (toGal K hU u'), e]
    exact hθ τ h _
  · intro hφ τ' h' c
    obtain ⟨g, rfl⟩ := hArt.surj c
    have e : conjGal h' (conjGal h'.symm g) = g := AlgEquiv.ext fun x => by
      show σ.symm (σ (g (σ.symm (σ x)))) = g x; rw [σ.symm_apply_apply, σ.symm_apply_apply]
    have k := hφ ⟨galEmb F K Ω g, hU' (galEmb_mem F K Ω g)⟩
      ⟨galEmb F K Ω (conjGal h'.symm g), hU' (galEmb_mem F K Ω _)⟩ fun x => by
        show σ (g (σ.symm (σ x))) = σ (g x); rw [σ.symm_apply_apply]
    have k' : θ (hArt.artCl (conjGal h'.symm g)) = T (θ (hArt.artCl g)) := k
    rw [artConj K Ω hArt τ' σ h' (conjGal h'.symm g), e] at k'
    exact k'

theorem pullEq (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure K Ω] [Normal F K] (hArt : HilbertArtinData K Ω) (U : Subgroup (G F Ω))
    (hU : U ≤ galOf F K Ω) (N : ℕ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (ρ : Representation R (G F Ω) M) (hN : N ≠ 0) (hU' : galOf F K Ω ≤ U)
    (hM : IsTotallyComplex K ∨ ∀ m : M, 2 • m = 0 → m = 0) :
    (ClEq K N ρ).map (clPull K hArt hU R M) = EqHom N U ρ ∧
    ∀ (τ : K ≃+* K) (σ : Ω ≃+* Ω) (s : R), IsLift τ σ →
      (ClEig K N ρ σ s).map (clPull K hArt hU R M) = EqEig N U ρ σ s := by
  have hO := pullOnto F Ω K hArt U hU N R M hN hU' hM
  have hL : ∀ g : G F Ω, IsLift (AlgEquiv.restrictNormal g K).toRingEquiv g.toRingEquiv := fun g x =>
    (AlgEquiv.restrictNormal_commutes g K x).symm
  have hC : ∀ (g : G F Ω) (θ : ClassGroup (𝓞 K) → M),
      θ ∈ clCond K g.toRingEquiv (ρ g) ↔ clPull K hArt hU R M θ ∈ conjCond U g.toRingEquiv (ρ g) :=
    fun g θ => pullCond F Ω K hArt U hU R M _ _ (ρ g) θ hU' (hL g)
  have h1 : (ClEq K N ρ).map (clPull K hArt hU R M) = EqHom N U ρ := by
    apply le_antisymm
    · rintro _ ⟨θ, ⟨hθ, hθ'⟩, rfl⟩
      exact ⟨hO ▸ Submodule.mem_map_of_mem hθ,
        (Submodule.mem_iInf _).2 fun g => (hC g θ).1 ((Submodule.mem_iInf _).1 hθ' g)⟩
    · rintro φ ⟨hφ, hφ'⟩
      obtain ⟨θ, hθ, rfl⟩ : φ ∈ (ClDual K N R M).map (clPull K hArt hU R M) := hO.symm ▸ hφ
      exact ⟨θ, ⟨hθ, (Submodule.mem_iInf _).2 fun g => (hC g θ).2 ((Submodule.mem_iInf _).1 hφ' g)⟩, rfl⟩
  refine ⟨h1, fun τ σ s h => le_antisymm ?_ ?_⟩
  · rintro _ ⟨θ, ⟨hθ, hθ'⟩, rfl⟩
    exact ⟨h1 ▸ Submodule.mem_map_of_mem hθ, (pullCond F Ω K hArt U hU R M τ σ _ θ hU' h).1 hθ'⟩
  · rintro φ ⟨hφ, hφ'⟩
    obtain ⟨θ, hθ, rfl⟩ : φ ∈ (ClEq K N ρ).map (clPull K hArt hU R M) := h1.symm ▸ hφ
    exact ⟨θ, ⟨hθ, (pullCond F Ω K hArt U hU R M τ σ _ θ hU' h).2 hφ'⟩, rfl⟩

theorem shaZm (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (hArt : HilbertArtinData F Ω) (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (r : ℕ)
    (hP : PTCase F l) :
    Function.Injective (resZm D r) ∧
    (ShaZm D r 0).map (resZm D r) =
      (ClDual F l (ZMod (l ^ r)) (ZMod (l ^ r))).map
        (LinearMap.funLeft (ZMod (l ^ r)) (ZMod (l ^ r)) hArt.artCl) := by
  have two_inj : l ≠ 2 → ∀ m : ZMod (l ^ r), 2 • m = 0 → m = 0 := fun hl m h => by
    have hc : Nat.Coprime 2 (l ^ r) :=
      Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two Fact.out).2 hl.symm)
    rw [nsmul_eq_mul] at h
    exact ((ZMod.isUnit_iff_coprime 2 _).2 hc).mul_right_eq_zero.1 h
  have zm_triv : ∀ g (m : ZMod (l ^ r)), zmTw D r 0 g m = m := fun _ _ => by simp [zmTw]
  have mem_iff : ∀ z : Z1 (zmTw D r 0), (Submodule.Quotient.mk z : H1 (zmTw D r 0)) ∈ ShaZm D r 0 ↔
      ∀ v : D.S, ∀ g ∈ Dec (F := F) (D.A v), z.1 (toGS Ω _ g) = 0 := fun z =>
    (Submodule.mem_iInf _).trans (forall_congr' fun v =>
      ((Submodule.Quotient.mk_eq_zero _).trans (mem_B1 _ _)).trans
        ⟨fun ⟨m, hm⟩ g hg => (hm ⟨g, hg⟩).trans (sub_eq_zero.2 (zm_triv _ m)),
         fun h => ⟨0, fun g => (h g.1 g.2).trans (sub_eq_zero.2 (zm_triv _ 0)).symm⟩⟩)
  have hU : (⊤ : Subgroup (G F Ω)) ≤ galOf F F Ω := (galOf_self F Ω).ge
  have key := pullOnto F Ω F hArt ⊤ hU l (ZMod (l ^ r)) (ZMod (l ^ r)) (Fact.out : l.Prime).ne_zero
    le_top (hP.elim (fun h => Or.inr (two_inj h)) fun h => Or.inl (nrRealPlaces_eq_zero_iff.1 h))
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  refine ⟨fun x y hxy => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    congr 1; exact Subtype.ext (funext fun g => by
      obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
      exact congrFun hxy σ)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hz : ∀ a b, z.1 (a * b) = z.1 a + z.1 b := fun a b => by rw [z.2.2, zm_triv]
    have h1 : z.1 1 = 0 := by have h := hz 1 1; rw [one_mul] at h; exact left_eq_add.1 h
    have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
        ∀ u : (⊤ : Subgroup (G F Ω)), u.1 ∈ Dec (F := F) A → z.1 (toGS Ω _ u.1) = 0 := fun A hA u hu => by
      obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
      have hvS : v ∈ D.S := by have := (p4 A v l hv).1 hA; rwa [← D.hS] at this
      obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
      have h2 := (mem_iff z).1 hx ⟨v, hvS⟩ _ (conj_mem_Dec hu)
      have hconj := hz (toGS Ω _ g * toGS Ω _ (g⁻¹ * u.1 * g) * (toGS Ω _ g)⁻¹) (toGS Ω _ g)
      rw [inv_mul_cancel_right, hz, add_comm] at hconj
      have h3 : z.1 (toGS Ω _ g * toGS Ω _ (g⁻¹ * u.1 * g) * (toGS Ω _ g)⁻¹) = z.1 (toGS Ω _ (g⁻¹ * u.1 * g)) :=
        (add_right_cancel hconj).symm
      rw [h2, ← map_inv, ← map_mul, ← map_mul] at h3
      rw [show g * (g⁻¹ * u.1 * g) * g⁻¹ = u.1 by group] at h3
      exact h3
    have hsha_to : (fun u : (⊤ : Subgroup (G F Ω)) => z.1 (toGS Ω _ u.1)) ∈
        XDual l ⊤ (ZMod (l ^ r)) (ZMod (l ^ r)) :=
      ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val)),
       fun a b => by show z.1 (toGS Ω _ (a.1 * b.1)) = _; rw [map_mul, hz],
       fun A u hu => by
         show z.1 (toGS Ω _ u.1) = 0
         by_cases hA : A = ⊤
         · subst hA; rw [p1, Subgroup.mem_bot] at hu; rw [hu, map_one, h1]
         obtain ⟨v, hv⟩ := p2 A hA
         by_cases hl : A.valuation (l : Ω) < 1
         · exact hdec A hl u (Ine_le_Dec A hu)
         have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
           rw [D.hS]; exact fun h => hl ((p4 A v l hv).2 h)
         have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
           Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
             (Set.mem_iUnion.2 ⟨v, Set.mem_iUnion.2 ⟨hvS, Set.mem_iUnion.2 ⟨A, Set.mem_iUnion.2 ⟨hv, hu⟩⟩⟩⟩))
         have hq1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
         rw [hq1, h1], hdec⟩
    rw [← key] at hsha_to
    obtain ⟨θ, hθ, e⟩ := hsha_to
    exact ⟨θ, hθ, funext fun g => congrFun e ⟨g, trivial⟩⟩
  · rintro _ ⟨θ, hθ, rfl⟩
    have hf : (fun u : (⊤ : Subgroup (G F Ω)) => θ (hArt.artCl u.1)) ∈
        XDual l ⊤ (ZMod (l ^ r)) (ZMod (l ^ r)) := key ▸ ⟨θ, hθ, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := hf
    set f : G F Ω → ZMod (l ^ r) := fun g => θ (hArt.artCl g)
    have hc : Continuous f :=
      h1.continuous.comp (continuous_id.subtype_mk fun g : G F Ω => Subgroup.mem_top g)
    have hm : ∀ a b, f (a * b) = f a + f b := fun a b => h2 ⟨a, trivial⟩ ⟨b, trivial⟩
    have hf1 : f 1 = 0 := by have h := hm 1 1; rw [one_mul] at h; exact left_eq_add.1 h
    let N : Subgroup (G F Ω) :=
      { carrier := {n | f n = 0}
        one_mem' := hf1
        mul_mem' := fun {a b} ha hb => by show f (a * b) = 0; rw [hm, ha, hb, add_zero]
        inv_mem' := fun {a} ha => by have := hm a⁻¹ a; rw [inv_mul_cancel, hf1, ha, add_zero] at this; exact this.symm }
    haveI : N.Normal := ⟨fun a ha g => by
      have h := hm (g * a * g⁻¹) g
      rw [inv_mul_cancel_right, hm, add_comm] at h
      exact (add_right_cancel h).symm.trans ha⟩
    have hNS : NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) ≤ N :=
      Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal (N := N) fun τ hτ => by
        simp only [Set.mem_iUnion] at hτ; obtain ⟨_, -, A', -, hτ⟩ := hτ; exact h3 A' ⟨τ, trivial⟩ hτ)
        (isClosed_singleton.preimage hc)
    have hv : ∀ n ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))), f n = 0 := fun n hn => hNS hn
    let f' : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → ZMod (l ^ r) :=
      Quotient.lift f fun a b hab => by
        have e1 := hv _ (QuotientGroup.leftRel_apply.1 hab)
        have e2 := hm a (a⁻¹ * b); rw [mul_inv_cancel_left, e1, add_zero] at e2; exact e2.symm
    refine ⟨Submodule.Quotient.mk ⟨f', hc.quotient_lift _, fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [zm_triv]; exact hm a b⟩, (mem_iff _).2 fun v g hg => ?_, rfl⟩
    exact h4 (D.A v) ((p4 _ v.1 l (D.hA v)).2 (D.hS ▸ v.2)) ⟨g, trivial⟩ hg

section ClassGroupLimits

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem eqHom_le_of_cl (hArt : ∀ n, HilbertArtinData (Fn F Ω l n) Ω) (N : ℕ) (hN : N ≠ 0)
    (ρ : Representation R (G F Ω) M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (ClEq (Fn F Ω l n) N ρ) ≤ Bd) :
    Module.length R (EqHom N (Uinf F Ω l) ρ) ≤ Bd := by
  refine len_le_of_layers ⊤ _ (fun n => EqHom N (levU l ⊤ n) ρ)
    (fun m n h => (restrMem F Ω N _ _ _ R M ρ).2.1)
    (eqExt F Ω l N ⊤ R M ρ hN (by simp) hρ).1 Bd fun n₀ => ?_
  obtain ⟨n, h, hn⟩ := hB (max n₀ 2)
  refine ⟨n, (le_max_left _ _).trans h, ?_⟩
  rw [← (pullEq F Ω (Fn F Ω l n) (hArt n) _ (galOf_Fn n).ge N R M ρ hN (galOf_Fn n).le
    (Or.inl ((fnCyc F Ω l n).2.2 ((le_max_right _ _).trans h)))).1]
  exact (length_map_le _ _).trans hn

theorem eqEig_le_of_cl (hArt : ∀ n, HilbertArtinData (Fn F Ω l n) Ω) (N : ℕ) (hN : N ≠ 0)
    (ρ : Representation R (G F Ω) M) (hρ : ∀ m, IsLocallyConstant fun g => ρ g m)
    {τ : F ≃+* F} {σ : Ω ≃+* Ω} (hσ : IsLift τ σ) (s : R) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length R (ClEig (Fn F Ω l n) N ρ σ s) ≤ Bd) :
    Module.length R (EqEig N (Uinf F Ω l) ρ σ s) ≤ Bd := by
  refine len_le_of_layers ⊤ _ (fun n => EqEig N (levU l ⊤ n) ρ σ s)
    (fun m n h => (restrMem F Ω N _ _ _ R M ρ).2.2 σ s)
    ((eqExt F Ω l N ⊤ R M ρ hN (by simp) hρ).2 τ σ hσ s fun _ _ => trivial) Bd fun n₀ => ?_
  obtain ⟨n, h, hn⟩ := hB (max n₀ 2)
  refine ⟨n, (le_max_left _ _).trans h, ?_⟩
  obtain ⟨τ', h'⟩ := (fnCyc F Ω l n).2.1 τ σ hσ
  rw [← (pullEq F Ω (Fn F Ω l n) (hArt n) _ (galOf_Fn n).ge N R M ρ hN (galOf_Fn n).le
    (Or.inl ((fnCyc F Ω l n).2.2 ((le_max_right _ _).trans h)))).2 τ' σ s h']
  exact (length_map_le _ _).trans hn

theorem shaLen_le_of_cl (hArt : ∀ n, HilbertArtinData (Fn F Ω l n) Ω) (D : LData F Ω l)
    {e : ℤ} (he : e ≠ 0) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEq (Fn F Ω l n) l (qzG F Ω l e)) ≤ Bd) :
    shaLen D e ≤ Bd + errTwo l :=
  (shaLen_le_eqHom D he).trans
    (add_le_add (eqHom_le_of_cl hArt l (Fact.out : l.Prime).ne_zero _ (locConst_qzG e) Bd hB) le_rfl)

variable [IsCMField F]

theorem plusLen_le_of_cl (hArt : ∀ n, HilbertArtinData (Fn F Ω l n) Ω) (D : LData F Ω l)
    {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEig (Fn F Ω l n) l (qzG F Ω l e) σ 1) ≤ Bd) :
    plusLen D e ≤ Bd + errTwo l :=
  (plusLen_le_eqEig D he hσ).trans
    (add_le_add (eqEig_le_of_cl hArt l (Fact.out : l.Prime).ne_zero _ (locConst_qzG _) hσ.isLift 1 Bd hB) le_rfl)

theorem minusLen_le_of_cl (hArt : ∀ n, HilbertArtinData (Fn F Ω l n) Ω) (D : LData F Ω l)
    {e : ℕ} (he : e ≠ 0) {σ : Ω ≃+* Ω} (hσ : IsConjOm σ) (Bd : ℕ∞)
    (hB : ∀ n₀, ∃ n, n₀ ≤ n ∧ Module.length ℤ_[l] (ClEig (Fn F Ω l n) l (qzG F Ω l e) σ (-1)) ≤ Bd) :
    minusLen D e ≤ Bd + errTwo l :=
  (minusLen_le_eqEig D he hσ).trans
    (add_le_add (eqEig_le_of_cl hArt l (Fact.out : l.Prime).ne_zero _ (locConst_qzG _) hσ.isLift (-1) Bd hB) le_rfl)

end ClassGroupLimits

end HilbertArtinReciprocityPullback

end ArtinPullbackAndLimits

end RHDirect.Stage13GL_KummerDuality

end
