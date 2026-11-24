import RHDirect.Stage10ArtinLFunctions
import RHDirect.Stage7DedekindZeta
import RHDirect.CFT_GlobalCompletion

/-!
# RHDirect.ArtinDedekindGenuine

Genuine native-Mathlib Galois Artin `L`-functions (`arithFrobAt`), unconditional Dedekind–Artin
factorization into `Stage7DedekindZeta.dedekindZeta`, and concrete `S₃` verification for
`K = ℚ(∛2)` and its Galois closure `L = ℚ(∛2, ω)` with zero hand-coded `frob` proxies.
-/

noncomputable section

open Complex Finset LinearMap Module Representation Subgroup
open NumberField IsDedekindDomain
open RHDirect.Stage13CFT_IdeleNormResidue.SemiLocal
open scoped BigOperators NumberField Pointwise

namespace RHDirect.ArtinDedekind

/-! ## Section 1: Genuine Unramified Galois Frobenius & Genuine Artin `L`-Function -/

section GenuineFrobenius

/-- Canonical height-one prime ideal `v_p` of `𝓞 ℚ` corresponding to a rational prime `p`. -/
def placeOfPrime (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp⟩

@[simp]
lemma primesEquiv_placeOfPrime (p : ℕ) (hp : p.Prime) :
    (Rat.HeightOneSpectrum.primesEquiv (placeOfPrime p hp)).1 = p :=
  congrArg Subtype.val (Equiv.apply_symm_apply Rat.HeightOneSpectrum.primesEquiv ⟨p, hp⟩)

theorem placeOfPrime_asIdeal (p : ℕ) (hp : p.Prime) :
    (placeOfPrime p hp).asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  let e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have hnat : Rat.HeightOneSpectrum.natGenerator (placeOfPrime p hp) = p :=
    primesEquiv_placeOfPrime p hp
  have hspan : Ideal.span {(p : ℤ)} = Ideal.map (e : 𝓞 ℚ →+* ℤ) (placeOfPrime p hp).asIdeal := by
    have h0 := Rat.HeightOneSpectrum.span_natGenerator (placeOfPrime p hp)
    rw [hnat] at h0
    exact h0
  have hback := congrArg (Ideal.map (e.symm : ℤ →+* 𝓞 ℚ)) hspan
  have hcomp : (e.symm : ℤ →+* 𝓞 ℚ).comp (e : 𝓞 ℚ →+* ℤ) = RingHom.id (𝓞 ℚ) := by
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply x
  rw [Ideal.map_map, hcomp, Ideal.map_id, Ideal.map_span] at hback
  rw [← hback]
  congr 1
  ext y
  simp

theorem liesOver_placeOfPrime_iff_liesOver_span {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) :
    w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal ↔
      w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have heq : (placeOfPrime p hp).asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [placeOfPrime_asIdeal p hp, Ideal.under]
    ext z
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    have hmap : algebraMap ℤ (𝓞 ℚ) z = (z : 𝓞 ℚ) := rfl
    rw [hmap]
    constructor
    · rintro ⟨c, hc⟩
      have hc' := congrArg (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) hc
      simp only [map_intCast, map_mul, map_natCast] at hc'
      exact ⟨Rat.ringOfIntegersEquiv c, hc'⟩
    · rintro ⟨c, hc⟩
      refine ⟨(c : 𝓞 ℚ), ?_⟩
      exact_mod_cast hc
  constructor
  · intro _
    have : (placeOfPrime p hp).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨heq.symm⟩
    exact Ideal.LiesOver.trans w.asIdeal (placeOfPrime p hp).asIdeal (Ideal.span {(p : ℤ)})
  · intro h
    refine ⟨?_⟩
    ext x
    have hx : ∃ z : ℤ, (z : 𝓞 ℚ) = x := by
      refine ⟨Rat.ringOfIntegersEquiv x, ?_⟩
      have h1 : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) = x :=
        Rat.ringOfIntegersEquiv.symm_apply_apply x
      simpa using h1
    obtain ⟨z, rfl⟩ := hx
    have h1 : (z : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ z ∈ w.asIdeal.under ℤ := by
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap]
      have hmap : (algebraMap (𝓞 ℚ) (𝓞 F)) (z : 𝓞 ℚ) = algebraMap ℤ (𝓞 F) z := by
        rw [show (z : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) z from rfl,
          ← IsScalarTower.algebraMap_apply ℤ (𝓞 ℚ) (𝓞 F)]
      rw [hmap]
    change (z : 𝓞 ℚ) ∈ (placeOfPrime p hp).asIdeal ↔ (z : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ)
    rw [h1, ← h.over, ← heq, Ideal.under, Ideal.mem_comap]
    rfl

theorem liesOver_placeOfPrime_iff_dvd_absNorm {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) :
    w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal ↔ p ∣ Ideal.absNorm w.asIdeal := by
  rw [liesOver_placeOfPrime_iff_liesOver_span w hp,
    Stage7DedekindZeta.dvd_absNorm_iff_liesOver w hp]

lemma placeOfPrime_ramificationIdx_inertiaDeg {p : ℕ} (hp : p.Prime) :
    (placeOfPrime p hp).asIdeal.ramificationIdx ℤ = 1 ∧
      (placeOfPrime p hp).asIdeal.inertiaDeg ℤ = 1 := by
  have : Finite (Stage7DedekindZeta.PrimesAbove ℚ p) :=
    Stage7DedekindZeta.finite_primesAbove ℚ hp
  classical
  let : Fintype (Stage7DedekindZeta.PrimesAbove ℚ p) := Fintype.ofFinite _
  have hsum := Stage7DedekindZeta.sum_ramification_inertia_primesAbove ℚ hp
  rw [Module.finrank_self] at hsum
  have hlo : (placeOfPrime p hp).asIdeal.LiesOver (placeOfPrime p hp).asIdeal := ⟨rfl⟩
  have hdvd : p ∣ Ideal.absNorm (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm (placeOfPrime p hp) hp).mp hlo
  let v₀ : Stage7DedekindZeta.PrimesAbove ℚ p := ⟨placeOfPrime p hp, hdvd⟩
  have hle : v₀.1.asIdeal.ramificationIdx ℤ * v₀.1.asIdeal.inertiaDeg ℤ ≤
      ∑ v : Stage7DedekindZeta.PrimesAbove ℚ p,
        v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ :=
    Finset.single_le_sum
      (f := fun v : Stage7DedekindZeta.PrimesAbove ℚ p =>
        v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v₀)
  rw [hsum] at hle
  have : v₀.1.asIdeal.IsPrime := v₀.1.isPrime
  have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos v₀.1.asIdeal ℤ)
    (Ideal.inertiaDeg_pos v₀.1.asIdeal ℤ)
  have heq1 : v₀.1.asIdeal.ramificationIdx ℤ * v₀.1.asIdeal.inertiaDeg ℤ = 1 :=
    le_antisymm hle hpos
  exact mul_eq_one.mp heq1

lemma placeOfPrime_liesOver_span {p : ℕ} (hp : p.Prime) :
    (placeOfPrime p hp).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hlo : (placeOfPrime p hp).asIdeal.LiesOver (placeOfPrime p hp).asIdeal := ⟨rfl⟩
  exact (liesOver_placeOfPrime_iff_liesOver_span (placeOfPrime p hp) hp).mp hlo

theorem ramificationIdx_rat_eq_int {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 ℚ) = w.asIdeal.ramificationIdx ℤ := by
  have : (placeOfPrime p hp).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    placeOfPrime_liesOver_span hp
  have htow := Ideal.ramificationIdx_tower (R := ℤ) (placeOfPrime p hp).asIdeal w.asIdeal
  rw [(placeOfPrime_ramificationIdx_inertiaDeg hp).1, one_mul] at htow
  exact htow.symm

theorem inertiaDeg_rat_eq_int {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    w.asIdeal.inertiaDeg (𝓞 ℚ) = w.asIdeal.inertiaDeg ℤ := by
  have : (placeOfPrime p hp).asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    placeOfPrime_liesOver_span hp
  have htow := Ideal.inertiaDeg_tower (R := ℤ) (placeOfPrime p hp).asIdeal w.asIdeal
  rw [(placeOfPrime_ramificationIdx_inertiaDeg hp).2, one_mul] at htow
  exact htow.symm

/-- Set of rational primes ramified in a number field `F`. -/
def ramifiedPrimesSet (F : Type*) [Field F] [NumberField F] : Set ℕ :=
  {p : ℕ | p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)})}

/-- Only finitely many rational primes ramify in any number field `F`. -/
theorem finite_ramifiedPrimesSet (F : Type*) [Field F] [NumberField F] :
    (ramifiedPrimesSet F).Finite := by
  have hev := RHDirect.CFT.Global.IdeleNorm.eventually_forall_placesOver ℚ
    (RHDirect.CFT.Global.IdeleNorm.eventually_ramificationIdx_eq_one ℚ F)
  have hfin_v : {v : HeightOneSpectrum (𝓞 ℚ) |
      ¬ ∀ w : PlacesOver F v, w.1.asIdeal.ramificationIdx (𝓞 ℚ) = 1}.Finite :=
    Filter.eventually_cofinite.mp hev
  let f : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v => (Rat.HeightOneSpectrum.primesEquiv v).1
  refine (hfin_v.image f).subset ?_
  intro p hp
  rcases hp with ⟨hp_prime, hram⟩
  refine ⟨placeOfPrime p hp_prime, ?_, primesEquiv_placeOfPrime p hp_prime⟩
  intro hall
  apply hram
  intro P hP hP_lo
  have hne : P ≠ ⊥ := by
    have hsp_ne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Int.natCast_ne_zero.mpr hp_prime.ne_zero
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hsp_ne P
  let w : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hne⟩
  have hw_lo : w.asIdeal.LiesOver (placeOfPrime p hp_prime).asIdeal :=
    (liesOver_placeOfPrime_iff_liesOver_span w hp_prime).mpr hP_lo
  have he1 : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := hall ⟨w, hw_lo⟩
  rw [ramificationIdx_rat_eq_int w hp_prime] at he1
  exact Ideal.ramificationIdx_eq_one_iff.mp he1

/-- Finite `Finset` of rational primes ramified in `F`. -/
def ramifiedPrimes (F : Type*) [Field F] [NumberField F] : Finset ℕ :=
  (finite_ramifiedPrimesSet F).toFinset

theorem mem_ramifiedPrimes_iff {F : Type*} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes F ↔ ¬ Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}) := by
  simp [ramifiedPrimes, ramifiedPrimesSet, hp]

theorem ramificationIdx_eq_one_of_notMem_ramifiedPrimes {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes F)
    (w : Stage7DedekindZeta.PrimesAbove F p) :
    w.1.asIdeal.ramificationIdx ℤ = 1 := by
  have hU : Algebra.IsUnramifiedIn (𝓞 F) (Ideal.span {(p : ℤ)}) := by
    by_contra h
    exact hunr ((mem_ramifiedPrimes_iff hp).mpr h)
  have : w.1.asIdeal.IsPrime := w.1.isPrime
  have : w.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Stage7DedekindZeta.dvd_absNorm_iff_liesOver w.1 hp).mp w.2
  exact Ideal.ramificationIdx_eq_one_iff.mpr (hU w.1.asIdeal w.1.isPrime this)

theorem ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes {F : Type*} [Field F] [NumberField F]
    {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes F)
    (w : HeightOneSpectrum (𝓞 F)) [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 := by
  rw [ramificationIdx_rat_eq_int w hp]
  have hdvd : p ∣ Ideal.absNorm w.asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm w hp).mp inferInstance
  exact ramificationIdx_eq_one_of_notMem_ramifiedPrimes hp hunr ⟨w, hdvd⟩

section GaloisFrobenius

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

/-- **Conjugation of Genuine Arithmetic Frobenius**: if `w` lies over `v_p` and `p` is unramified
in `L`, then `arithFrobAt (𝓞 ℚ) Gal(L/ℚ) (σ • w).asIdeal = σ * arithFrobAt (𝓞 ℚ) Gal(L/ℚ) w.asIdeal * σ⁻¹`. -/
theorem arithFrobAt_smul {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal]
    (σ : L ≃ₐ[ℚ] L) :
    arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) (σ • w).asIdeal =
      σ * arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w.asIdeal * σ⁻¹ := by
  let f₁ := arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w.asIdeal
  let f₂ := arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) (σ • w).asIdeal
  have : (σ • w).asIdeal.LiesOver (placeOfPrime p hp).asIdeal := by
    change (σ • w.asIdeal).LiesOver (placeOfPrime p hp).asIdeal
    infer_instance
  have hf₁ : IsArithFrobAt (𝓞 ℚ) f₁ w.asIdeal :=
    IsArithFrobAt.arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w.asIdeal
  have hf₂ : IsArithFrobAt (𝓞 ℚ) f₂ (σ • w).asIdeal :=
    IsArithFrobAt.arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) (σ • w).asIdeal
  have hunder : (σ • w).asIdeal.under (𝓞 ℚ) = w.asIdeal.under (𝓞 ℚ) := by
    rw [← Ideal.over_def (σ • w).asIdeal (placeOfPrime p hp).asIdeal,
      ← Ideal.over_def w.asIdeal (placeOfPrime p hp).asIdeal]
  have hf_conj : IsArithFrobAt (𝓞 ℚ) (σ * f₁ * σ⁻¹) (σ • w).asIdeal := by
    intro r
    rw [hunder]
    set q := Nat.card (𝓞 ℚ ⧸ w.asIdeal.under (𝓞 ℚ))
    have h1 : f₁ • (σ⁻¹ • r) - (σ⁻¹ • r) ^ q ∈ w.asIdeal := hf₁ (σ⁻¹ • r)
    have h2 : σ • (f₁ • (σ⁻¹ • r) - (σ⁻¹ • r) ^ q) ∈ (σ • w).asIdeal := by
      rw [smul_asIdeal, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul]
      exact h1
    have hpow : σ • (σ⁻¹ • r) ^ q = r ^ q := by
      rw [smul_pow', smul_inv_smul]
    have hact : σ • (f₁ • (σ⁻¹ • r) - (σ⁻¹ • r) ^ q) = (σ * f₁ * σ⁻¹) • r - r ^ q := by
      rw [smul_sub, hpow, ← mul_smul, ← mul_smul, mul_assoc]
    rwa [hact] at h2
  have hmem := hf_conj.mul_inv_mem_inertia hf₂
  have he : (σ • w).asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes hp hunr (σ • w)
  have hbot : (σ • w).asIdeal.inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [RHDirect.CFT.Global.natCard_inertia (placeOfPrime p hp) (σ • w), he]
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  exact hmem.symm

/-- **Conjugacy Well-Definedness of Unramified `arithFrobAt`**: any two primes `w₁, w₂` of `𝓞 L`
lying over the same unramified rational prime `p` have conjugate arithmetic Frobenius elements
in `Gal(L / ℚ)`. -/
theorem arithFrobAt_conj_of_liesOver {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (w₁ w₂ : HeightOneSpectrum (𝓞 L))
    [w₁.asIdeal.LiesOver (placeOfPrime p hp).asIdeal]
    [w₂.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    ∃ σ : L ≃ₐ[ℚ] L,
      arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w₂.asIdeal =
        σ * arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w₁.asIdeal * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (placeOfPrime p hp).asIdeal w₁.asIdeal w₂.asIdeal (L ≃ₐ[ℚ] L)
  have hw₂ : σ • w₁ = w₂ := HeightOneSpectrum.ext (by
    rw [smul_asIdeal]
    exact hσ)
  refine ⟨σ, ?_⟩
  rw [← hw₂]
  exact arithFrobAt_smul hp hunr w₁ σ

/-- **Canonical Independence of Choice of Prime `w | p`**: for ANY complex representation `ρ` of
`Gal(L / ℚ)` and any unramified rational prime `p`, `artinLocalFactor ρ (arithFrobAt ... w.asIdeal) T`
and `artinLocalPoly ρ (arithFrobAt ... w.asIdeal) T` are independent of `w | p`. -/
theorem artinLocalPoly_arithFrobAt_indep {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[ℚ] L) V) {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (w₁ w₂ : HeightOneSpectrum (𝓞 L))
    [w₁.asIdeal.LiesOver (placeOfPrime p hp).asIdeal]
    [w₂.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] (T : ℂ) :
    Stage10ArtinLFunctions.artinLocalPoly ρ (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w₁.asIdeal) T =
      Stage10ArtinLFunctions.artinLocalPoly ρ (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w₂.asIdeal) T := by
  obtain ⟨σ, hσ⟩ := arithFrobAt_conj_of_liesOver hp hunr w₁ w₂
  rw [hσ, Stage10ArtinLFunctions.artinLocalPoly_conj]

theorem artinLocalFactor_arithFrobAt_indep {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[ℚ] L) V) {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (w₁ w₂ : HeightOneSpectrum (𝓞 L))
    [w₁.asIdeal.LiesOver (placeOfPrime p hp).asIdeal]
    [w₂.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] (T : ℂ) :
    Stage10ArtinLFunctions.artinLocalFactor ρ (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w₁.asIdeal) T =
      Stage10ArtinLFunctions.artinLocalFactor ρ (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w₂.asIdeal) T := by
  simp [Stage10ArtinLFunctions.artinLocalFactor,
    artinLocalPoly_arithFrobAt_indep ρ hp hunr w₁ w₂ T]

/-- **Exact Order of Genuine Unramified Frobenius = Inertia Degree**:
`orderOf (arithFrobAt (𝓞 ℚ) Gal(L/ℚ) w.asIdeal) = w.asIdeal.inertiaDeg (𝓞 ℚ) = w.asIdeal.inertiaDeg ℤ`. -/
theorem orderOf_arithFrobAt_eq_inertiaDeg {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    orderOf (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w.asIdeal) = w.asIdeal.inertiaDeg (𝓞 ℚ) := by
  have he : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes hp hunr w
  have hstab := RHDirect.CFT.Global.stabilizer_eq_zpowers_arithFrobAt (placeOfPrime p hp) w he
  have hcard := RHDirect.CFT.Global.card_decompositionGroup (placeOfPrime p hp) w
  rw [hstab, Nat.card_zpowers, he, one_mul] at hcard
  exact hcard

theorem orderOf_arithFrobAt_eq_inertiaDeg_int {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    orderOf (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) w.asIdeal) = w.asIdeal.inertiaDeg ℤ := by
  rw [orderOf_arithFrobAt_eq_inertiaDeg hp hunr w, inertiaDeg_rat_eq_int w hp]

end GaloisFrobenius

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

/-- Pick a prime `w : PrimesAbove L p` lying over `p` (all choices yield conjugate `arithFrobAt`). -/
def chosenPlaceAbove (p : ℕ) (hp : p.Prime) : Stage7DedekindZeta.PrimesAbove L p :=
  let w := (RHDirect.CFT.Global.nonempty_placesOver L (placeOfPrime p hp)).some
  ⟨w.1, (liesOver_placeOfPrime_iff_dvd_absNorm w.1 hp).mp w.2⟩

/-- Genuine Galois arithmetic Frobenius element `Frob_p ∈ Gal(L / ℚ)` attached to a rational prime `p`. -/
def genuineFrobAt (p : ℕ) (hp : p.Prime) : L ≃ₐ[ℚ] L :=
  arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) (chosenPlaceAbove L p hp).1.asIdeal

/-- **Genuine Unramified Artin `L`-Function** attached to a finite Galois extension `L / ℚ` and
a complex representation `ρ` of `Gal(L / ℚ)`, defined directly via `arithFrobAt` (with ZERO
user-supplied `frob` proxy). -/
def genuineArtinL {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[ℚ] L) V) (s : ℂ) : ℂ :=
  Stage10ArtinLFunctions.artinL (ramifiedPrimes L)
    (fun p => genuineFrobAt L p.1 p.2.1) ρ s

/-- `genuineArtinL` equals the Euler product over ANY choice of primes `w(p) | p` above unramified `p`. -/
theorem genuineArtinL_eq_tprod_of_choice {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[ℚ] L) V)
    (w : (p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L}) → Stage7DedekindZeta.PrimesAbove L p.1)
    (s : ℂ) :
    genuineArtinL L ρ s =
      ∏' p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
        Stage10ArtinLFunctions.artinLocalFactor ρ
          (arithFrobAt (𝓞 ℚ) (L ≃ₐ[ℚ] L) (w p).1.asIdeal) ((p.1 : ℂ) ^ (-s)) := by
  unfold genuineArtinL Stage10ArtinLFunctions.artinL genuineFrobAt
  congr 1
  ext p
  have : (chosenPlaceAbove L p.1 p.2.1).1.asIdeal.LiesOver (placeOfPrime p.1 p.2.1).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm (chosenPlaceAbove L p.1 p.2.1).1 p.2.1).mpr
      (chosenPlaceAbove L p.1 p.2.1).2
  have : (w p).1.asIdeal.LiesOver (placeOfPrime p.1 p.2.1).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm (w p).1 p.2.1).mpr (w p).2
  exact artinLocalFactor_arithFrobAt_indep ρ p.2.1 p.2.2
    (chosenPlaceAbove L p.1 p.2.1).1 (w p).1 ((p.1 : ℂ) ^ (-s))

theorem genuineArtinL_multipliable {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (L ≃ₐ[ℚ] L) V) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L} =>
      Stage10ArtinLFunctions.artinLocalFactor ρ (genuineFrobAt L p.1 p.2.1) ((p.1 : ℂ) ^ (-s))) :=
  Stage10ArtinLFunctions.artinL_multipliable (ramifiedPrimes L)
    (fun p => genuineFrobAt L p.1 p.2.1) ρ hs

theorem genuineArtinL_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (L ≃ₐ[ℚ] L) V) {s : ℂ} (hs : 1 < s.re) :
    genuineArtinL L ρ s ≠ 0 :=
  Stage10ArtinLFunctions.artinL_ne_zero (ramifiedPrimes L)
    (fun p => genuineFrobAt L p.1 p.2.1) ρ hs

theorem genuineArtinL_prod {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (ρ₁ : Representation ℂ (L ≃ₐ[ℚ] L) V₁) (ρ₂ : Representation ℂ (L ≃ₐ[ℚ] L) V₂)
    {s : ℂ} (hs : 1 < s.re) :
    genuineArtinL L (Representation.prod ρ₁ ρ₂) s =
      genuineArtinL L ρ₁ s * genuineArtinL L ρ₂ s :=
  Stage10ArtinLFunctions.artinL_prod (ramifiedPrimes L)
    (fun p => genuineFrobAt L p.1 p.2.1) ρ₁ ρ₂ hs

theorem genuineArtinL_trivial {s : ℂ} (hs : 1 < s.re) :
    genuineArtinL L (Representation.trivial ℂ (L ≃ₐ[ℚ] L) ℂ) s =
      (∏ p ∈ (ramifiedPrimes L).filter Nat.Prime, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
  Stage10ArtinLFunctions.artinL_trivial (ramifiedPrimes L)
    (fun p => genuineFrobAt L p.1 p.2.1) hs

end GenuineFrobenius

/-! ## Section 2: Genuine Dedekind–Artin Factorization into `Stage7DedekindZeta.dedekindZeta` -/

section DedekindArtinFactorization

/-- Unramified Euler product of `Stage7DedekindZeta.dedekindZeta F s` outside a finite prime set `S`. -/
def dedekindZetaUnramified (F : Type*) [Field F] [NumberField F] (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 F) // (Ideal.absNorm v.asIdeal).minFac ∉ S},
    (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹

/-- Ramified Euler product of `Stage7DedekindZeta.dedekindZeta F s` over primes in `S`. -/
def dedekindZetaRamified (F : Type*) [Field F] [NumberField F] (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 F) // (Ideal.absNorm v.asIdeal).minFac ∈ S},
    (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹

/-- Exact splitting of `Stage7DedekindZeta.dedekindZeta F s` into ramified and unramified factors on
`1 < s.re`. -/
theorem dedekindZeta_eq_ramified_mul_unramified (F : Type*) [Field F] [NumberField F]
    (S : Finset ℕ) {s : ℂ} (hs : 1 < s.re) :
    Stage7DedekindZeta.dedekindZeta F s =
      dedekindZetaRamified F S s * dedekindZetaUnramified F S s := by
  classical
  rw [Stage7DedekindZeta.dedekindZeta_eq_exp_tsum_neg_log F hs]
  unfold dedekindZetaRamified dedekindZetaUnramified
  have hram_exp := (Stage7DedekindZeta.hasProd_eulerProduct_subtype_exp_neg_log F
    (fun v => (Ideal.absNorm v.asIdeal).minFac ∈ S) hs).tprod_eq
  have hunram_exp := (Stage7DedekindZeta.hasProd_eulerProduct_subtype_exp_neg_log F
    (fun v => (Ideal.absNorm v.asIdeal).minFac ∉ S) hs).tprod_eq
  rw [hram_exp, hunram_exp, ← Complex.exp_add]
  congr 1
  let g : HeightOneSpectrum (𝓞 F) → ℂ := fun v => -Complex.log (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
  have hg_sum : Summable g :=
    ((Stage7DedekindZeta.summable_heightOne_absNorm_cpow F hs).clog_one_sub).neg
  let T : Set (HeightOneSpectrum (𝓞 F)) := {v | (Ideal.absNorm v.asIdeal).minFac ∈ S}
  have hsplit := hg_sum.tsum_subtype_add_tsum_subtype_compl T
  exact hsplit.symm

section LocalAndGlobalIntermediate

section IntermediateHelpers

private lemma smul_fixingSubgroupEquiv_ideal {L : Type*} [Field L] [Algebra ℚ L]
    (K : IntermediateField ℚ L) (h : K.fixingSubgroup) (P : Ideal (𝓞 L)) :
    (IntermediateField.fixingSubgroupEquiv K h • P) = (h : L ≃ₐ[ℚ] L) • P := by
  ext a
  simp only [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private lemma smul_fixingSubgroup_under {L : Type*} [Field L] [Algebra ℚ L]
    (K : IntermediateField ℚ L) (h : K.fixingSubgroup) (P : Ideal (𝓞 L)) :
    ((h : L ≃ₐ[ℚ] L) • P).under (𝓞 K) = P.under (𝓞 K) := by
  ext a
  simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hfix : ((h : L ≃ₐ[ℚ] L)⁻¹ • algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
    apply Subtype.ext
    change ((h : L ≃ₐ[ℚ] L)⁻¹ (algebraMap K L (a : K))) = algebraMap K L (a : K)
    exact (IntermediateField.mem_fixingSubgroup_iff K (h : L ≃ₐ[ℚ] L)⁻¹).mp
      (K.fixingSubgroup.inv_mem h.2) ((a : K) : L) (a : K).2
  rw [hfix]

private lemma under_liesOver_placeOfPrime {L : Type*} [Field L] [NumberField L]
    (K : IntermediateField ℚ L) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal] :
    letI : NumberField K := NumberField.of_module_finite ℚ K
    (w.asIdeal.under (𝓞 K)).LiesOver (placeOfPrime p hp).asIdeal := by
  have : NumberField K := NumberField.of_module_finite ℚ K
  refine ⟨?_⟩
  have h1 := Ideal.LiesOver.over (P := w.asIdeal) (p := (placeOfPrime p hp).asIdeal)
  rw [h1]
  ext a
  simp only [Ideal.under, Ideal.mem_comap]
  rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 K) (𝓞 L)]

private noncomputable def orbitToPrimeAbove (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (K : IntermediateField ℚ L) {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L) :
    have : NumberField K := NumberField.of_module_finite ℚ K
    Stage10ArtinLFunctions.CycleOrbits (genuineFrobAt L p hp)
      ((L ≃ₐ[ℚ] L) ⧸ K.fixingSubgroup) ≃
      Stage7DedekindZeta.PrimesAbove K p := by
  classical
  have : NumberField K := NumberField.of_module_finite ℚ K
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  let G := L ≃ₐ[ℚ] L
  let H : Subgroup G := K.fixingSubgroup
  let frob : G := genuineFrobAt L p hp
  let w₀ : Stage7DedekindZeta.PrimesAbove L p := chosenPlaceAbove L p hp
  have hw₀_lo : w₀.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm w₀.1 hp).mpr w₀.2
  have he_w₀ : w₀.1.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes hp hunr w₀.1
  have hstab_w₀ : MulAction.stabilizer G w₀.1.asIdeal = Subgroup.zpowers frob :=
    RHDirect.CFT.Global.stabilizer_eq_zpowers_arithFrobAt (placeOfPrime p hp) w₀.1 he_w₀
  let specOfRep : G → Stage7DedekindZeta.PrimesAbove K p := fun x =>
    have hxw_lo : (x⁻¹ • w₀.1).asIdeal.LiesOver (placeOfPrime p hp).asIdeal := by
      rw [smul_asIdeal]; infer_instance
    have hu_lo : ((x⁻¹ • w₀.1).asIdeal.under (𝓞 K)).LiesOver (placeOfPrime p hp).asIdeal :=
      under_liesOver_placeOfPrime K hp (x⁻¹ • w₀.1)
    have hne : (x⁻¹ • w₀.1).asIdeal.under (𝓞 K) ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot (placeOfPrime p hp).ne_bot _
    let u : HeightOneSpectrum (𝓞 K) :=
      ⟨(x⁻¹ • w₀.1).asIdeal.under (𝓞 K), Ideal.comap_isPrime _ _, hne⟩
    ⟨u, (liesOver_placeOfPrime_iff_dvd_absNorm u hp).mp hu_lo⟩
  let specOfCoset : (G ⧸ H) → Stage7DedekindZeta.PrimesAbove K p :=
    Quotient.lift specOfRep fun x₁ x₂ hrel => by
      have hmem : x₁⁻¹ * x₂ ∈ H := QuotientGroup.leftRel_apply.mp hrel
      let h : H := ⟨x₁⁻¹ * x₂, hmem⟩
      have hx₂ : x₂ = x₁ * (h : G) := by simp [h]
      apply Subtype.ext; apply HeightOneSpectrum.ext
      change (x₁⁻¹ • w₀.1).asIdeal.under (𝓞 K) = (x₂⁻¹ • w₀.1).asIdeal.under (𝓞 K)
      rw [hx₂, mul_inv_rev, smul_asIdeal, smul_asIdeal, mul_smul]
      exact (smul_fixingSubgroup_under K h⁻¹ (x₁⁻¹ • w₀.1.asIdeal)).symm
  refine Equiv.ofBijective (Quotient.lift specOfCoset fun q₁ q₂ ⟨⟨d, hd⟩, hdq⟩ => by
    subst hdq
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q₂
    change specOfRep (d * x) = specOfRep x
    apply Subtype.ext; apply HeightOneSpectrum.ext
    change ((d * x)⁻¹ • w₀.1).asIdeal.under (𝓞 K) = (x⁻¹ • w₀.1).asIdeal.under (𝓞 K)
    have hdw : d⁻¹ • w₀.1.asIdeal = w₀.1.asIdeal := by
      rw [← hstab_w₀] at hd
      exact (MulAction.stabilizer G w₀.1.asIdeal).inv_mem hd
    rw [smul_asIdeal, smul_asIdeal, mul_inv_rev, mul_smul, hdw]) ⟨?_, ?_⟩
  · intro O₁ O₂ heq
    obtain ⟨q₁, rfl⟩ := Quotient.exists_rep O₁
    obtain ⟨q₂, rfl⟩ := Quotient.exists_rep O₂
    obtain ⟨x₁, rfl⟩ := Quotient.exists_rep q₁
    obtain ⟨x₂, rfl⟩ := Quotient.exists_rep q₂
    have hu : (x₁⁻¹ • w₀.1).asIdeal.under (𝓞 K) = (x₂⁻¹ • w₀.1).asIdeal.under (𝓞 K) :=
      congrArg (fun u : Stage7DedekindZeta.PrimesAbove K p => u.1.asIdeal) heq
    let u : Ideal (𝓞 K) := (x₁⁻¹ • w₀.1).asIdeal.under (𝓞 K)
    have : (x₁⁻¹ • w₀.1).asIdeal.LiesOver u := ⟨rfl⟩
    have : (x₂⁻¹ • w₀.1).asIdeal.LiesOver u := ⟨hu⟩
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      u (x₁⁻¹ • w₀.1).asIdeal (x₂⁻¹ • w₀.1).asIdeal (L ≃ₐ[K] L)
    let h : H := (IntermediateField.fixingSubgroupEquiv K).symm τ
    have hh_smul : (h : G) • (x₁⁻¹ • w₀.1.asIdeal) = x₂⁻¹ • w₀.1.asIdeal := by
      have hτ_eq := (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply τ
      rw [← hτ_eq] at hτ
      exact (smul_fixingSubgroupEquiv_ideal K h (x₁⁻¹ • w₀.1.asIdeal)).symm.trans hτ
    have hstab : x₁ * (h : G)⁻¹ * x₂⁻¹ ∈ Subgroup.zpowers frob := by
      rw [← hstab_w₀]
      change (x₁ * (h : G)⁻¹ * x₂⁻¹) • w₀.1.asIdeal = w₀.1.asIdeal
      rw [mul_smul, mul_smul]
      have hinv : (h : G)⁻¹ • (x₂⁻¹ • w₀.1.asIdeal) = x₁⁻¹ • w₀.1.asIdeal := by
        rw [← hh_smul, inv_smul_smul]
      rw [hinv, smul_inv_smul]
    apply Quotient.sound
    refine ⟨⟨x₁ * (h : G)⁻¹ * x₂⁻¹, hstab⟩, ?_⟩
    change QuotientGroup.mk ((x₁ * (h : G)⁻¹ * x₂⁻¹) * x₂) = QuotientGroup.mk x₁
    have hmul : x₁ * (h : G)⁻¹ * x₂⁻¹ * x₂ = x₁ * (h : G)⁻¹ := by
      rw [mul_assoc (x₁ * (h : G)⁻¹), inv_mul_cancel, mul_one]
    rw [hmul]
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
      have heq_h : (x₁ * (h : G)⁻¹)⁻¹ * x₁ = (h : G) := by
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      rw [heq_h]
      exact h.2))
  · intro u
    have : u.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
      (liesOver_placeOfPrime_iff_dvd_absNorm u.1 hp).mpr u.2
    obtain ⟨w⟩ := RHDirect.CFT.Global.nonempty_placesOver L u.1
    have : w.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
      Ideal.LiesOver.trans w.1.asIdeal u.1.asIdeal (placeOfPrime p hp).asIdeal
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
      (placeOfPrime p hp).asIdeal w₀.1.asIdeal w.1.asIdeal G
    refine ⟨Quotient.mk _ ((g⁻¹ : G) : G ⧸ H), ?_⟩
    apply Subtype.ext; apply HeightOneSpectrum.ext
    change ((g⁻¹)⁻¹ • w₀.1).asIdeal.under (𝓞 K) = u.1.asIdeal
    rw [inv_inv, smul_asIdeal, hg, ← Ideal.over_def w.1.asIdeal u.1.asIdeal]

private lemma orbitSize_orbitToPrimeAbove (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (K : IntermediateField ℚ L) {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    (O : Stage10ArtinLFunctions.CycleOrbits (genuineFrobAt L p hp)
      ((L ≃ₐ[ℚ] L) ⧸ K.fixingSubgroup)) :
    have : NumberField K := NumberField.of_module_finite ℚ K
    Stage10ArtinLFunctions.orbitSize (genuineFrobAt L p hp) O =
      (orbitToPrimeAbove L K hp hunr O).1.asIdeal.inertiaDeg ℤ := by
  classical
  have : NumberField K := NumberField.of_module_finite ℚ K
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  let G := L ≃ₐ[ℚ] L
  let H : Subgroup G := K.fixingSubgroup
  let frob : G := genuineFrobAt L p hp
  let w₀ : Stage7DedekindZeta.PrimesAbove L p := chosenPlaceAbove L p hp
  have hw₀_lo : w₀.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm w₀.1 hp).mpr w₀.2
  have he_w₀ : w₀.1.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes hp hunr w₀.1
  have hstab_w₀ : MulAction.stabilizer G w₀.1.asIdeal = Subgroup.zpowers frob :=
    RHDirect.CFT.Global.stabilizer_eq_zpowers_arithFrobAt (placeOfPrime p hp) w₀.1 he_w₀
  obtain ⟨q, rfl⟩ := Quotient.exists_rep O
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  let w : HeightOneSpectrum (𝓞 L) := x⁻¹ • w₀.1
  have hw_lo : w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal := by
    dsimp [w]; rw [smul_asIdeal]; infer_instance
  let u : HeightOneSpectrum (𝓞 K) := (orbitToPrimeAbove L K hp hunr (Quotient.mk _ (x : G ⧸ H))).1
  have hu_eq : u.asIdeal = w.asIdeal.under (𝓞 K) := rfl
  have hu_lo : u.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm u hp).mpr (orbitToPrimeAbove L K hp hunr _).2
  have hwu_lo : w.asIdeal.LiesOver u.asIdeal := ⟨hu_eq⟩
  have he_w_Q : w.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes hp hunr w
  have hram_tow := Ideal.ramificationIdx_tower (R := 𝓞 ℚ) u.asIdeal w.asIdeal
  rw [he_w_Q] at hram_tow
  have he_w_K : w.asIdeal.ramificationIdx (𝓞 K) = 1 := (mul_eq_one.mp hram_tow.symm).2
  have hcard_L_K := RHDirect.CFT.Global.card_decompositionGroup u w
  rw [he_w_K, one_mul] at hcard_L_K
  let D := Subgroup.zpowers frob
  let stabD := MulAction.stabilizer D (x : G ⧸ H)
  let stabHK := MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal
  let φ_fwd : stabD → stabHK := fun d =>
    ⟨IntermediateField.fixingSubgroupEquiv K ⟨x⁻¹ * (d.1 : G) * x,
      QuotientGroup.leftRel_apply.mp (Quotient.exact (d.2 : (d.1 : G) • (x : G ⧸ H) = (x : G ⧸ H)).symm)⟩, by
      change _ • w.asIdeal = w.asIdeal
      dsimp [w]
      rw [smul_asIdeal, smul_fixingSubgroupEquiv_ideal]
      have hd_smul : (d.1 : G) • w₀.1.asIdeal = w₀.1.asIdeal := by
        have hd_mem : (d.1 : G) ∈ MulAction.stabilizer G w₀.1.asIdeal := by
          rw [hstab_w₀]; exact d.1.2
        exact hd_mem
      rw [mul_smul, mul_smul, smul_inv_smul, hd_smul]⟩
  have hstab_bij : Nat.card stabD = Nat.card stabHK := by
    refine Nat.card_congr (Equiv.ofBijective φ_fwd ⟨?_, ?_⟩)
    · intro d₁ d₂ hd
      have h1 := congrArg (fun y : stabHK => ((IntermediateField.fixingSubgroupEquiv K).symm y.1 : G)) hd
      simp only [φ_fwd, MulEquiv.symm_apply_apply] at h1
      have h2 : (d₁.1 : G) = (d₂.1 : G) := by
        calc (d₁.1 : G) = x * (x⁻¹ * (d₁.1 : G) * x) * x⁻¹ := by
              rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]
          _ = x * (x⁻¹ * (d₂.1 : G) * x) * x⁻¹ := by rw [h1]
          _ = (d₂.1 : G) := by
              rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul]
      exact Subtype.ext (Subtype.ext h2)
    · rintro ⟨τ, hτ⟩
      let h : H := (IntermediateField.fixingSubgroupEquiv K).symm τ
      have hτ_eq := (IntermediateField.fixingSubgroupEquiv K).apply_symm_apply τ
      have hh : (h : G) • w.asIdeal = w.asIdeal := by
        rw [← hτ_eq] at hτ
        exact (smul_fixingSubgroupEquiv_ideal K h w.asIdeal).symm.trans hτ
      have hd_D : x * (h : G) * x⁻¹ ∈ D := by
        dsimp [D]; rw [← hstab_w₀]
        change (x * (h : G) * x⁻¹) • w₀.1.asIdeal = w₀.1.asIdeal
        have hw_def : w.asIdeal = x⁻¹ • w₀.1.asIdeal := smul_asIdeal x⁻¹ w₀.1
        rw [mul_smul, mul_smul, ← hw_def, hh, hw_def, smul_inv_smul]
      have hd_mem : (⟨x * (h : G) * x⁻¹, hd_D⟩ : D) ∈ stabD := by
        change QuotientGroup.mk ((x * (h : G) * x⁻¹) * x) = QuotientGroup.mk x
        have hmul : x * (h : G) * x⁻¹ * x = x * (h : G) := by
          rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
        rw [hmul]
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
          have heq_h : (x * (h : G))⁻¹ * x = (h : G)⁻¹ := by
            rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
          rw [heq_h]
          exact H.inv_mem h.2))
      refine ⟨⟨⟨x * (h : G) * x⁻¹, hd_D⟩, hd_mem⟩, ?_⟩
      apply Subtype.ext
      apply (IntermediateField.fixingSubgroupEquiv K).symm.injective
      apply Subtype.ext
      change x⁻¹ * (x * (h : G) * x⁻¹ * x) = (h : G)
      rw [mul_assoc (x * (h : G)), inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel, one_mul]
  have horb_eq : Stage10ArtinLFunctions.orbitSize frob (Quotient.mk _ (x : G ⧸ H)) =
      Nat.card (MulAction.orbit D (x : G ⧸ H)) := by
    unfold Stage10ArtinLFunctions.orbitSize
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1, (MulAction.orbitRel_apply (G := D) (a := y.1) (b := (x : G ⧸ H))).mp
          (Quotient.exact y.2)⟩
        invFun := fun y => ⟨y.1, Quotient.sound ((MulAction.orbitRel_apply (G := D) (a := y.1) (b := (x : G ⧸ H))).mpr y.2)⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  have hcard_os : Stage10ArtinLFunctions.orbitSize frob (Quotient.mk _ (x : G ⧸ H)) *
      Nat.card stabD = Nat.card D := by
    rw [horb_eq, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D (x : G ⧸ H))]
    exact Subgroup.index_mul_card (MulAction.stabilizer D (x : G ⧸ H))
  have hcard_D : Nat.card D = w.asIdeal.inertiaDeg (𝓞 ℚ) := by
    have hnorm_eq : Ideal.absNorm w.asIdeal = Ideal.absNorm w₀.1.asIdeal := by
      dsimp [w]; rw [absNorm_smul]
    have : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
      (liesOver_placeOfPrime_iff_liesOver_span w hp).mp hw_lo
    have : w₀.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
      (liesOver_placeOfPrime_iff_liesOver_span w₀.1 hp).mp hw₀_lo
    have : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    have hf_eq : w.asIdeal.inertiaDeg ℤ = w₀.1.asIdeal.inertiaDeg ℤ := by
      have hp1 : Ideal.absNorm w.asIdeal = p ^ w.asIdeal.inertiaDeg ℤ := by
        rw [Ideal.absNorm_eq_pow_inertiaDeg' w.asIdeal hp,
          Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) w.asIdeal]
      have hp0 : Ideal.absNorm w₀.1.asIdeal = p ^ w₀.1.asIdeal.inertiaDeg ℤ := by
        rw [Ideal.absNorm_eq_pow_inertiaDeg' w₀.1.asIdeal hp,
          Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) w₀.1.asIdeal]
      rw [hp1, hp0] at hnorm_eq
      exact Nat.pow_right_injective hp.two_le hnorm_eq
    change Nat.card (Subgroup.zpowers frob) = w.asIdeal.inertiaDeg (𝓞 ℚ)
    dsimp [frob, genuineFrobAt]
    rw [Nat.card_zpowers, orderOf_arithFrobAt_eq_inertiaDeg_int hp hunr w₀.1, ← hf_eq,
      ← inertiaDeg_rat_eq_int w hp]
  have hinert_tow := Ideal.inertiaDeg_tower (R := 𝓞 ℚ) u.asIdeal w.asIdeal
  rw [hstab_bij, hcard_L_K, hcard_D, hinert_tow] at hcard_os
  have hpos : 0 < w.asIdeal.inertiaDeg (𝓞 K) := by
    have : w.asIdeal.IsPrime := w.isPrime
    exact Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)
  exact (Nat.eq_of_mul_eq_mul_right hpos hcard_os).trans (inertiaDeg_rat_eq_int u hp)

end IntermediateHelpers

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

/-- **Genuine Local Intermediate-Field Euler Factor = Induced Trivial Representation**:
For ANY finite Galois extension `L / ℚ`, ANY intermediate field `K : IntermediateField ℚ L`
with subgroup `H = K.fixingSubgroup ≤ Gal(L / ℚ)`, and ANY prime `p ∉ ramifiedPrimes L`,
the actual local Dedekind Euler factor of `K` at `p` equals
`artinLocalFactor (Ind_H^G 1_H) (genuineFrobAt L p hp) (p^{-s})`. -/
theorem intermediateField_local_dedekind_eulerFactor_eq_ind
    (K : IntermediateField ℚ L) {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    [Fintype (Stage7DedekindZeta.PrimesAbove K p)] (s : ℂ) :
    ∏ u : Stage7DedekindZeta.PrimesAbove K p, (1 - (Ideal.absNorm u.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      Stage10ArtinLFunctions.artinLocalFactor
        (Representation.ind K.fixingSubgroup.subtype
          (Representation.trivial ℂ K.fixingSubgroup ℂ))
        (genuineFrobAt L p hp) ((p : ℂ) ^ (-s)) := by
  classical
  have : NumberField K := NumberField.of_module_finite ℚ K
  let orbEquiv := orbitToPrimeAbove L K hp hunr
  rw [Stage10ArtinLFunctions.artinLocalFactor_iso
      (Stage10ArtinLFunctions.indTrivialEquivOfMulAction K.fixingSubgroup)
      (genuineFrobAt L p hp) ((p : ℂ) ^ (-s)),
    Stage10ArtinLFunctions.artinLocalFactor_perm_eq_prod_cycles
      K.fixingSubgroup (genuineFrobAt L p hp) ((p : ℂ) ^ (-s)),
    ← Equiv.prod_comp orbEquiv]
  refine Finset.prod_congr rfl fun O _ => ?_
  have hlo_u : (orbEquiv O).1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm (orbEquiv O).1 hp).mpr (orbEquiv O).2
  have : (orbEquiv O).1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (liesOver_placeOfPrime_iff_liesOver_span (orbEquiv O).1 hp).mp hlo_u
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have habs_u : Ideal.absNorm (orbEquiv O).1.asIdeal = p ^ (orbEquiv O).1.asIdeal.inertiaDeg ℤ := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' (orbEquiv O).1.asIdeal hp,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) (orbEquiv O).1.asIdeal]
  rw [orbitSize_orbitToPrimeAbove L K hp hunr O, habs_u, Nat.cast_pow,
    ← Complex.ofReal_natCast, Stage7DedekindZeta.ofReal_pow_cpow (Nat.cast_nonneg p)]

/-- **Genuine Local Regular-Representation Euler Factor for Galois `L / ℚ`**:
At every unramified prime `p ∉ ramifiedPrimes L`, the actual local Euler factor of
`Stage7DedekindZeta.dedekindZeta L s` equals
`artinLocalFactor (leftRegular ℂ (L ≃ₐ[ℚ] L)) (genuineFrobAt L p hp) (p^{-s})`. -/
theorem galois_local_dedekind_eulerFactor_eq_leftRegular
    {p : ℕ} (hp : p.Prime) (hunr : p ∉ ramifiedPrimes L)
    [Fintype (Stage7DedekindZeta.PrimesAbove L p)] (s : ℂ) :
    ∏ w : Stage7DedekindZeta.PrimesAbove L p, (1 - (Ideal.absNorm w.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      Stage10ArtinLFunctions.artinLocalFactor (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L))
        (genuineFrobAt L p hp) ((p : ℂ) ^ (-s)) := by
  classical
  let G := L ≃ₐ[ℚ] L
  let frob : G := genuineFrobAt L p hp
  let w₀ : Stage7DedekindZeta.PrimesAbove L p := chosenPlaceAbove L p hp
  have hw₀_lo : w₀.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm w₀.1 hp).mpr w₀.2
  have he_w₀ : w₀.1.asIdeal.ramificationIdx (𝓞 ℚ) = 1 :=
    ramificationIdx_rat_eq_one_of_notMem_ramifiedPrimes hp hunr w₀.1
  have hstab_w₀ : MulAction.stabilizer G w₀.1.asIdeal = Subgroup.zpowers frob :=
    RHDirect.CFT.Global.stabilizer_eq_zpowers_arithFrobAt (placeOfPrime p hp) w₀.1 he_w₀
  let specOfG : G → Stage7DedekindZeta.PrimesAbove L p := fun x =>
    have hx_lo : (x⁻¹ • w₀.1).asIdeal.LiesOver (placeOfPrime p hp).asIdeal := by
      rw [smul_asIdeal]; infer_instance
    ⟨x⁻¹ • w₀.1, (liesOver_placeOfPrime_iff_dvd_absNorm (x⁻¹ • w₀.1) hp).mp hx_lo⟩
  let orbEquiv : Stage10ArtinLFunctions.CycleOrbits frob G ≃ Stage7DedekindZeta.PrimesAbove L p := by
    refine Equiv.ofBijective (Quotient.lift specOfG fun x₁ x₂ ⟨⟨d, hd⟩, hdx⟩ => by
      have hdw : d⁻¹ • w₀.1.asIdeal = w₀.1.asIdeal := by
        rw [← hstab_w₀] at hd
        exact (MulAction.stabilizer G w₀.1.asIdeal).inv_mem hd
      have hx1 : x₁ = d * x₂ := hdx.symm
      apply Subtype.ext; apply HeightOneSpectrum.ext
      change (x₁⁻¹ • w₀.1).asIdeal = (x₂⁻¹ • w₀.1).asIdeal
      rw [hx1, mul_inv_rev, smul_asIdeal, smul_asIdeal, mul_smul, hdw]) ⟨?_, ?_⟩
    · intro O₁ O₂ heq
      obtain ⟨x₁, rfl⟩ := Quotient.exists_rep O₁
      obtain ⟨x₂, rfl⟩ := Quotient.exists_rep O₂
      have hw_eq : x₁⁻¹ • w₀.1.asIdeal = x₂⁻¹ • w₀.1.asIdeal := by
        have h_eq := congrArg (fun w : Stage7DedekindZeta.PrimesAbove L p => w.1.asIdeal) heq
        change (x₁⁻¹ • w₀.1).asIdeal = (x₂⁻¹ • w₀.1).asIdeal at h_eq
        rw [smul_asIdeal, smul_asIdeal] at h_eq
        exact h_eq
      have hstab : x₁ * x₂⁻¹ ∈ Subgroup.zpowers frob := by
        rw [← hstab_w₀]
        change (x₁ * x₂⁻¹) • w₀.1.asIdeal = w₀.1.asIdeal
        rw [mul_smul, ← hw_eq, smul_inv_smul]
      exact Quotient.sound ⟨⟨x₁ * x₂⁻¹, hstab⟩, by
        change (x₁ * x₂⁻¹) * x₂ = x₁
        rw [mul_assoc, inv_mul_cancel, mul_one]⟩
    · intro w
      have : w.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
        (liesOver_placeOfPrime_iff_dvd_absNorm w.1 hp).mpr w.2
      obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
        (placeOfPrime p hp).asIdeal w₀.1.asIdeal w.1.asIdeal G
      refine ⟨Quotient.mk _ g⁻¹, ?_⟩
      apply Subtype.ext; apply HeightOneSpectrum.ext
      change (g⁻¹⁻¹ • w₀.1).asIdeal = w.1.asIdeal
      rw [inv_inv, smul_asIdeal, hg]
  have horb_size : ∀ O : Stage10ArtinLFunctions.CycleOrbits frob G,
      Stage10ArtinLFunctions.orbitSize frob O = (orbEquiv O).1.asIdeal.inertiaDeg ℤ := by
    intro O
    obtain ⟨x, rfl⟩ := Quotient.exists_rep O
    let D := Subgroup.zpowers frob
    have hstab_bot : MulAction.stabilizer D x = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨d, hd⟩ hdx
      have : d * x = x := hdx
      exact Subgroup.mem_bot.mpr (Subtype.ext (mul_right_cancel (b := x) (by simpa using this)))
    have horb_eq : Stage10ArtinLFunctions.orbitSize frob (Quotient.mk _ x) =
        Nat.card (MulAction.orbit D x) := by
      unfold Stage10ArtinLFunctions.orbitSize
      refine Nat.card_congr
        { toFun := fun y => ⟨y.1, (MulAction.orbitRel_apply (G := D) (a := y.1) (b := x)).mp (Quotient.exact y.2)⟩
          invFun := fun y => ⟨y.1, Quotient.sound ((MulAction.orbitRel_apply (G := D) (a := y.1) (b := x)).mpr y.2)⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
    have hcard_os : Stage10ArtinLFunctions.orbitSize frob (Quotient.mk _ x) *
        Nat.card (MulAction.stabilizer D x) = Nat.card D := by
      rw [horb_eq, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer D x)]
      exact Subgroup.index_mul_card (MulAction.stabilizer D x)
    rw [hstab_bot, Nat.card_unique, mul_one, Nat.card_zpowers] at hcard_os
    dsimp [frob, genuineFrobAt] at hcard_os
    rw [orderOf_arithFrobAt_eq_inertiaDeg_int hp hunr w₀.1] at hcard_os
    have hnorm_eq : Ideal.absNorm (orbEquiv (Quotient.mk _ x)).1.asIdeal =
        Ideal.absNorm w₀.1.asIdeal := by
      change Ideal.absNorm (x⁻¹ • w₀.1).asIdeal = Ideal.absNorm w₀.1.asIdeal
      exact absNorm_smul x⁻¹ w₀.1
    have hw_lo : (orbEquiv (Quotient.mk _ x)).1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
      (Stage7DedekindZeta.dvd_absNorm_iff_liesOver _ hp).mp (orbEquiv _).2
    have hw0_lo : w₀.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
      (Stage7DedekindZeta.dvd_absNorm_iff_liesOver _ hp).mp w₀.2
    have : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp, Ideal.absNorm_eq_pow_inertiaDeg' _ hp,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) _,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) _] at hnorm_eq
    exact hcard_os.trans (Nat.pow_right_injective hp.two_le hnorm_eq).symm
  rw [Stage10ArtinLFunctions.artinLocalFactor_leftRegular_eq_prod_cycles frob ((p : ℂ) ^ (-s)),
    ← Equiv.prod_comp orbEquiv]
  refine Finset.prod_congr rfl fun O _ => ?_
  have hw_lo : (orbEquiv O).1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (Stage7DedekindZeta.dvd_absNorm_iff_liesOver _ hp).mp (orbEquiv O).2
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have habs : Ideal.absNorm (orbEquiv O).1.asIdeal = p ^ (orbEquiv O).1.asIdeal.inertiaDeg ℤ := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg' (orbEquiv O).1.asIdeal hp,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) (orbEquiv O).1.asIdeal]
  rw [horb_size O, habs, Nat.cast_pow, ← Complex.ofReal_natCast,
    Stage7DedekindZeta.ofReal_pow_cpow (Nat.cast_nonneg p)]

/-- Helper: general unramified Euler product equality for ANY number field `F` and finite prime
set `S` whose local product at `p ∉ S` equals `f p`. -/
theorem dedekindZetaUnramified_eq_tprod_of_local
    (F : Type*) [Field F] [NumberField F] (S : Finset ℕ) (s : ℂ)
    (f : {p : ℕ // p.Prime ∧ p ∉ S} → ℂ)
    (hloc : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
      ∀ [Fintype (Stage7DedekindZeta.PrimesAbove F p.1)],
      ∏ v : Stage7DedekindZeta.PrimesAbove F p.1, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        f p)
    (hmult_f : Multipliable f) (hs : 1 < s.re) :
    dedekindZetaUnramified F S s = ∏' p : {p : ℕ // p.Prime ∧ p ∉ S}, f p := by
  classical
  unfold dedekindZetaUnramified
  let eUnram : {v : HeightOneSpectrum (𝓞 F) // (Ideal.absNorm v.asIdeal).minFac ∉ S} ≃
      Σ p : {p : ℕ // p.Prime ∧ p ∉ S}, Stage7DedekindZeta.PrimesAbove F p.1 :=
    { toFun := fun v =>
        ⟨⟨(Ideal.absNorm v.1.asIdeal).minFac,
          Stage7DedekindZeta.minFac_absNorm_prime v.1, v.2⟩,
          ⟨v.1, Nat.minFac_dvd (Ideal.absNorm v.1.asIdeal)⟩⟩
      invFun := fun x =>
        ⟨x.2.1, by
          have hpeq := Stage7DedekindZeta.eq_minFac_of_prime_dvd_absNorm x.2.1 x.1.2.1 x.2.2
          rw [← hpeq]
          exact x.1.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun x => by
        obtain ⟨⟨p, hp, hnd⟩, ⟨v, hv⟩⟩ := x
        dsimp only
        have hpeq : (Ideal.absNorm v.asIdeal).minFac = p :=
          (Stage7DedekindZeta.eq_minFac_of_prime_dvd_absNorm v hp hv).symm
        have hmk : ∀ (a b : ℕ) (ha : a.Prime ∧ a ∉ S) (hb : b.Prime ∧ b ∉ S)
            (hv1 : a ∣ Ideal.absNorm v.asIdeal) (hv2 : b ∣ Ideal.absNorm v.asIdeal),
            a = b →
              (⟨⟨a, ha⟩, ⟨v, hv1⟩⟩ :
                Σ q : {q : ℕ // q.Prime ∧ q ∉ S}, Stage7DedekindZeta.PrimesAbove F q.1) =
              ⟨⟨b, hb⟩, ⟨v, hv2⟩⟩ := by
          rintro _ _ _ _ _ _ rfl; rfl
        exact hmk _ _ _ _ _ _ hpeq }
  have hmult_v :
      Multipliable
        (fun v : {v : HeightOneSpectrum (𝓞 F) // (Ideal.absNorm v.asIdeal).minFac ∉ S} =>
          (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (Stage7DedekindZeta.hasProd_eulerProduct_subtype_exp_neg_log F
      (fun v => (Ideal.absNorm v.asIdeal).minFac ∉ S) hs).multipliable
  have hmult_sig :
      Multipliable
        (fun x : Σ p : {p : ℕ // p.Prime ∧ p ∉ S}, Stage7DedekindZeta.PrimesAbove F p.1 =>
          (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (Equiv.multipliable_iff eUnram).mp hmult_v
  have hfib : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
      HasProd (fun v : Stage7DedekindZeta.PrimesAbove F p.1 =>
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (f p) := by
    intro p
    have : Finite (Stage7DedekindZeta.PrimesAbove F p.1) :=
      Stage7DedekindZeta.finite_primesAbove F p.2.1
    let : Fintype (Stage7DedekindZeta.PrimesAbove F p.1) := Fintype.ofFinite _
    rw [← hloc p]
    exact hasProd_fintype _
  have hsig_prod :
      HasProd
        (fun x : Σ p : {p : ℕ // p.Prime ∧ p ∉ S}, Stage7DedekindZeta.PrimesAbove F p.1 =>
          (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹)
        (∏' p : {p : ℕ // p.Prime ∧ p ∉ S}, f p) :=
    HasProd.sigma_of_hasProd hmult_f.hasProd hfib hmult_sig
  exact ((Equiv.hasProd_iff eUnram).mpr hsig_prod).tprod_eq

/-- **UNCONDITIONAL GENUINE ARTIN INDUCTION EQUALITY FOR INTERMEDIATE FIELDS**:
For ANY finite Galois extension `L / ℚ`, ANY intermediate field `K : IntermediateField ℚ L`
with `H = K.fixingSubgroup`, and ANY `s : ℂ` with `1 < s.re`, the unramified Euler product of
`Stage7DedekindZeta.dedekindZeta K s` equals `genuineArtinL L (Ind_H^G 1_H) s`! -/
theorem dedekindZetaUnramified_intermediateField_eq_genuineArtinL_ind
    (K : IntermediateField ℚ L) {s : ℂ} (hs : 1 < s.re) :
    have : NumberField K := NumberField.of_module_finite ℚ K
    dedekindZetaUnramified K (ramifiedPrimes L) s =
      genuineArtinL L
        (Representation.ind K.fixingSubgroup.subtype
          (Representation.trivial ℂ K.fixingSubgroup ℂ)) s := by
  have : NumberField K := NumberField.of_module_finite ℚ K
  unfold genuineArtinL Stage10ArtinLFunctions.artinL
  refine dedekindZetaUnramified_eq_tprod_of_local K (ramifiedPrimes L) s _
    (fun p _ => intermediateField_local_dedekind_eulerFactor_eq_ind L K p.2.1 p.2.2 s) ?_ hs
  exact genuineArtinL_multipliable L _ hs

/-- **UNCONDITIONAL GENUINE REGULAR-REPRESENTATION IDENTITY**:
For ANY finite Galois extension `L / ℚ` and `1 < s.re`, the unramified Euler product of
`Stage7DedekindZeta.dedekindZeta L s` equals `genuineArtinL L (leftRegular ℂ (L ≃ₐ[ℚ] L)) s`! -/
theorem dedekindZetaUnramified_galois_eq_leftRegular {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaUnramified L (ramifiedPrimes L) s =
      genuineArtinL L (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L)) s := by
  unfold genuineArtinL Stage10ArtinLFunctions.artinL
  refine dedekindZetaUnramified_eq_tprod_of_local L (ramifiedPrimes L) s _
    (fun p _ => galois_local_dedekind_eulerFactor_eq_leftRegular L p.2.1 p.2.2 s) ?_ hs
  exact genuineArtinL_multipliable L _ hs

/-- **UNCONDITIONAL GENUINE DEDEKIND–ARTIN FACTORIZATION THEOREM**:
For ANY finite Galois extension `L / ℚ`, there exists a finite family `(W_i)_{i : ι}` of pairwise
non-isomorphic irreducible subrepresentations of `ℂ[Gal(L / ℚ)]` such that:
1. `∑ i, (dim W_i)² = [L : ℚ]`,
2. For EVERY `s : ℂ` with `1 < s.re`, the unramified Euler product of `Stage7DedekindZeta.dedekindZeta L s`
   equals `∏ i, (genuineArtinL L (W_i) s) ^ (dim W_i)`,
3. And `Stage7DedekindZeta.dedekindZeta L s = dedekindZetaRamified L (ramifiedPrimes L) s * ∏ i, (genuineArtinL L (W_i) s) ^ (dim W_i)`! -/
theorem dedekind_artin_factorization_galois :
    ∃ (ι : Type) (_ : Fintype ι)
      (W : ι → Subrepresentation (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L))),
      (∀ i, Representation.IsIrreducible (W i).toRepresentation) ∧
      (∀ i j, Nonempty (Representation.Equiv (W i).toRepresentation (W j).toRepresentation) → i = j) ∧
      (∑ i : ι, (Module.finrank ℂ (W i).toSubmodule) ^ 2 = Module.finrank ℚ L) ∧
      (∀ s : ℂ, 1 < s.re →
        dedekindZetaUnramified L (ramifiedPrimes L) s =
          ∏ i : ι, (genuineArtinL L (W i).toRepresentation s) ^
            Module.finrank ℂ (W i).toSubmodule) ∧
      (∀ s : ℂ, 1 < s.re →
        Stage7DedekindZeta.dedekindZeta L s =
          dedekindZetaRamified L (ramifiedPrimes L) s *
            ∏ i : ι, (genuineArtinL L (W i).toRepresentation s) ^
              Module.finrank ℂ (W i).toSubmodule) := by
  let frob : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L} → (L ≃ₐ[ℚ] L) :=
    fun p => genuineFrobAt L p.1 p.2.1
  obtain ⟨ι, hfin, W, hW_irr, hW_pair, _, hdim_sq, _, hglob⟩ :=
    Stage10ArtinLFunctions.dedekind_eq_prod_irrep_artinL (ramifiedPrimes L) frob
  refine ⟨ι, hfin, W, hW_irr, hW_pair, ?_, ?_, ?_⟩
  · rw [hdim_sq, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  · intro s hs
    rw [dedekindZetaUnramified_galois_eq_leftRegular L hs]
    have hloc : ∀ p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
        Stage10ArtinLFunctions.artinLocalFactor
          (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L)) (genuineFrobAt L p.1 p.2.1) ((p.1 : ℂ) ^ (-s)) =
          ∏ O : Stage10ArtinLFunctions.CycleOrbits (frob p) (L ≃ₐ[ℚ] L),
            (1 - ((p.1 : ℂ) ^ (-s)) ^ Stage10ArtinLFunctions.orbitSize (frob p) O)⁻¹ :=
      fun p => Stage10ArtinLFunctions.artinLocalFactor_leftRegular_eq_prod_cycles
        (frob p) ((p.1 : ℂ) ^ (-s))
    unfold genuineArtinL Stage10ArtinLFunctions.artinL
    have hprod_eq :
        (∏' p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
          Stage10ArtinLFunctions.artinLocalFactor
            (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L)) (genuineFrobAt L p.1 p.2.1) ((p.1 : ℂ) ^ (-s))) =
        ∏' p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
          ∏ O : Stage10ArtinLFunctions.CycleOrbits (frob p) (L ≃ₐ[ℚ] L),
            (1 - ((p.1 : ℂ) ^ (-s)) ^ Stage10ArtinLFunctions.orbitSize (frob p) O)⁻¹ :=
      tprod_congr hloc
    exact hprod_eq.trans (hglob s hs)
  · intro s hs
    rw [dedekindZeta_eq_ramified_mul_unramified L (ramifiedPrimes L) hs]
    congr 1
    rw [dedekindZetaUnramified_galois_eq_leftRegular L hs]
    have hloc : ∀ p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
        Stage10ArtinLFunctions.artinLocalFactor
          (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L)) (genuineFrobAt L p.1 p.2.1) ((p.1 : ℂ) ^ (-s)) =
          ∏ O : Stage10ArtinLFunctions.CycleOrbits (frob p) (L ≃ₐ[ℚ] L),
            (1 - ((p.1 : ℂ) ^ (-s)) ^ Stage10ArtinLFunctions.orbitSize (frob p) O)⁻¹ :=
      fun p => Stage10ArtinLFunctions.artinLocalFactor_leftRegular_eq_prod_cycles
        (frob p) ((p.1 : ℂ) ^ (-s))
    unfold genuineArtinL Stage10ArtinLFunctions.artinL
    have hprod_eq :
        (∏' p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
          Stage10ArtinLFunctions.artinLocalFactor
            (Representation.leftRegular ℂ (L ≃ₐ[ℚ] L)) (genuineFrobAt L p.1 p.2.1) ((p.1 : ℂ) ^ (-s))) =
        ∏' p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L},
          ∏ O : Stage10ArtinLFunctions.CycleOrbits (frob p) (L ≃ₐ[ℚ] L),
            (1 - ((p.1 : ℂ) ^ (-s)) ^ Stage10ArtinLFunctions.orbitSize (frob p) O)⁻¹ :=
      tprod_congr hloc
    exact hprod_eq.trans (hglob s hs)

end LocalAndGlobalIntermediate

end DedekindArtinFactorization

/-! ## Section 3: Concrete `S₃` Verification for `K = ℚ(∛2)` and `L = ℚ(∛2, ω)` -/

section ConcreteCbrt2S3

/-- The defining cubic polynomial `X³ - 2 ∈ ℤ[X]`. -/
def cbrt2PolyZ : Polynomial ℤ := Polynomial.X ^ 3 - Polynomial.C 2

/-- The defining cubic polynomial `X³ - 2 ∈ ℚ[X]`. -/
def cbrt2Poly : Polynomial ℚ := Polynomial.X ^ 3 - Polynomial.C 2

lemma cbrt2Poly_eq_map : cbrt2Poly = cbrt2PolyZ.map (Int.castRingHom ℚ) := by
  unfold cbrt2Poly cbrt2PolyZ
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    eq_intCast, Int.cast_ofNat]

lemma cbrt2PolyZ_monic : cbrt2PolyZ.Monic := by
  unfold cbrt2PolyZ
  exact Polynomial.monic_X_pow_sub_C 2 (by norm_num)

lemma cbrt2Poly_monic : cbrt2Poly.Monic := by
  unfold cbrt2Poly
  exact Polynomial.monic_X_pow_sub_C 2 (by norm_num)

@[simp]
lemma cbrt2PolyZ_natDegree : cbrt2PolyZ.natDegree = 3 := by
  unfold cbrt2PolyZ
  exact Polynomial.natDegree_X_pow_sub_C

@[simp]
lemma cbrt2Poly_natDegree : cbrt2Poly.natDegree = 3 := by
  unfold cbrt2Poly
  exact Polynomial.natDegree_X_pow_sub_C

theorem irreducible_cbrt2PolyZ : Irreducible cbrt2PolyZ := by
  let P : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hP_prime : P.IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr Int.prime_two
  have hdeg : cbrt2PolyZ.degree = 3 := by
    rw [Polynomial.degree_eq_natDegree cbrt2PolyZ_monic.ne_zero, cbrt2PolyZ_natDegree]
    rfl
  refine Polynomial.irreducible_of_eisenstein_criterion hP_prime ?_ ?_ ?_ ?_ cbrt2PolyZ_monic.isPrimitive
  · rw [cbrt2PolyZ_monic.leadingCoeff]
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    omega
  · intro n hn
    rw [hdeg] at hn
    have hn_lt : n < 3 := WithBot.coe_lt_coe.mp hn
    interval_cases n
    · simp [cbrt2PolyZ, P]
    · simp [cbrt2PolyZ, P]
    · simp [cbrt2PolyZ, P]
  · rw [hdeg]; decide
  · have hc0 : cbrt2PolyZ.coeff 0 = -2 := by
      unfold cbrt2PolyZ
      simp
    rw [hc0]
    have hP2 : P ^ 2 = Ideal.span {(4 : ℤ)} := by
      simp only [P, Ideal.span_singleton_pow]
      norm_num
    rw [hP2, Ideal.mem_span_singleton]
    omega

theorem irreducible_cbrt2Poly : Irreducible cbrt2Poly := by
  rw [cbrt2Poly_eq_map]
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    cbrt2PolyZ_monic.isPrimitive).mp irreducible_cbrt2PolyZ

theorem separable_cbrt2Poly : cbrt2Poly.Separable :=
  irreducible_cbrt2Poly.separable

/-- The genuine Galois closure `L = ℚ(∛2, ω)` = splitting field of `X³ - 2` over `ℚ`. -/
abbrev L_cbrt2 : Type := cbrt2Poly.SplittingField

instance : Polynomial.IsSplittingField ℚ L_cbrt2 cbrt2Poly :=
  ⟨Polynomial.SplittingField.splits cbrt2Poly, Polynomial.SplittingField.adjoin_rootSet cbrt2Poly⟩

instance : NumberField L_cbrt2 := NumberField.of_module_finite ℚ L_cbrt2

instance : IsGalois ℚ L_cbrt2 :=
  IsGalois.of_separable_splitting_field separable_cbrt2Poly

lemma card_rootSet_cbrt2Poly : Fintype.card (cbrt2Poly.rootSet L_cbrt2) = 3 := by
  have h := Polynomial.card_rootSet_eq_natDegree (K := L_cbrt2) separable_cbrt2Poly
    (Polynomial.SplittingField.splits cbrt2Poly)
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h ⊢
  exact h.trans cbrt2Poly_natDegree

/-- Indexing the 3 distinct roots of `X³ - 2` in `L_cbrt2` by `Fin 3`. -/
def rootEquivFin3 : Fin 3 ≃ cbrt2Poly.rootSet L_cbrt2 :=
  (Fintype.equivFinOfCardEq card_rootSet_cbrt2Poly).symm

/-- Chosen genuine cube root `α₀ = ∛2 ∈ L_cbrt2`. -/
def alpha0 : L_cbrt2 := (rootEquivFin3 0).1

/-- Second distinct root `α₁ ∈ L_cbrt2`. -/
def alpha1 : L_cbrt2 := (rootEquivFin3 1).1

/-- Primitive cube root of unity `ω = α₁ / α₀ ∈ L_cbrt2`. -/
def omegaCbrt2 : L_cbrt2 := alpha1 * alpha0⁻¹

lemma rootSet_pow_three {r : L_cbrt2} (hr : r ∈ cbrt2Poly.rootSet L_cbrt2) :
    r ^ 3 = 2 := by
  rw [Polynomial.mem_rootSet_of_ne irreducible_cbrt2Poly.ne_zero] at hr
  simp only [cbrt2Poly, map_sub, map_pow, Polynomial.aeval_X, map_ofNat] at hr
  exact sub_eq_zero.mp hr

lemma alpha0_pow_three : alpha0 ^ 3 = 2 :=
  rootSet_pow_three (rootEquivFin3 0).2

lemma alpha1_pow_three : alpha1 ^ 3 = 2 :=
  rootSet_pow_three (rootEquivFin3 1).2

lemma alpha0_ne_zero : alpha0 ≠ 0 := by
  intro h
  have h2 := alpha0_pow_three
  rw [h, zero_pow (by norm_num)] at h2
  norm_num at h2

lemma alpha1_ne_alpha0 : alpha1 ≠ alpha0 := by
  intro h
  have h01 : rootEquivFin3 1 = rootEquivFin3 0 := Subtype.ext h
  exact absurd (rootEquivFin3.injective h01) (by decide)

lemma omegaCbrt2_pow_three : omegaCbrt2 ^ 3 = 1 := by
  unfold omegaCbrt2
  rw [mul_pow, inv_pow, alpha1_pow_three, alpha0_pow_three]
  norm_num

lemma omegaCbrt2_ne_one : omegaCbrt2 ≠ 1 := by
  intro h
  apply alpha1_ne_alpha0
  unfold omegaCbrt2 at h
  calc alpha1 = (alpha1 * alpha0⁻¹) * alpha0 := by
        rw [mul_assoc, inv_mul_cancel₀ alpha0_ne_zero, mul_one]
    _ = 1 * alpha0 := by rw [h]
    _ = alpha0 := one_mul _

lemma omegaCbrt2_sq_add_add_one : omegaCbrt2 ^ 2 + omegaCbrt2 + 1 = 0 := by
  have hfac : (omegaCbrt2 - 1) * (omegaCbrt2 ^ 2 + omegaCbrt2 + 1) = 0 := by
    calc (omegaCbrt2 - 1) * (omegaCbrt2 ^ 2 + omegaCbrt2 + 1)
        = omegaCbrt2 ^ 3 - 1 := by ring
      _ = 0 := by rw [omegaCbrt2_pow_three, sub_self]
  exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr omegaCbrt2_ne_one)

/-- The genuine non-Galois cubic subfield `K = ℚ(∛2) ≤ L_cbrt2`. -/
def K_cbrt2 : IntermediateField ℚ L_cbrt2 :=
  IntermediateField.adjoin ℚ {alpha0}

instance : NumberField K_cbrt2 := NumberField.of_module_finite ℚ K_cbrt2

lemma minpoly_alpha0 : minpoly ℚ alpha0 = cbrt2Poly := by
  have haeval : Polynomial.aeval alpha0 cbrt2Poly = 0 := by
    change Polynomial.aeval alpha0 (Polynomial.X ^ 3 - Polynomial.C 2) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      map_ofNat (algebraMap ℚ L_cbrt2), alpha0_pow_three, sub_self]
  exact (minpoly.eq_of_irreducible_of_monic irreducible_cbrt2Poly haeval cbrt2Poly_monic).symm

theorem finrank_K_cbrt2 : Module.finrank ℚ K_cbrt2 = 3 := by
  have hint : IsIntegral ℚ alpha0 := Algebra.IsIntegral.isIntegral alpha0
  rw [show K_cbrt2 = IntermediateField.adjoin ℚ {alpha0} from rfl,
    IntermediateField.adjoin.finrank hint, minpoly_alpha0, cbrt2Poly_natDegree]

/-- Equivalence `K_cbrt2 ≃ₐ[ℚ] AdjoinRoot cbrt2Poly`, showing `K_cbrt2` is canonically `ℚ[X]/(X³ - 2)`. -/
def K_cbrt2EquivAdjoinRoot : K_cbrt2 ≃ₐ[ℚ] AdjoinRoot cbrt2Poly := by
  have : Fact (Irreducible cbrt2Poly) := ⟨irreducible_cbrt2Poly⟩
  let αK : K_cbrt2 := ⟨alpha0, IntermediateField.mem_adjoin_simple_self ℚ alpha0⟩
  have hαK : Polynomial.aeval αK cbrt2Poly = 0 := by
    change Polynomial.aeval αK (Polynomial.X ^ 3 - Polynomial.C 2) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      map_ofNat (algebraMap ℚ K_cbrt2)]
    apply Subtype.ext
    change alpha0 ^ 3 - (2 : L_cbrt2) = 0
    rw [alpha0_pow_three, sub_self]
  let f : AdjoinRoot cbrt2Poly →ₐ[ℚ] K_cbrt2 :=
    AdjoinRoot.liftAlgHom cbrt2Poly (Algebra.ofId ℚ K_cbrt2) αK hαK
  have hf_inj : Function.Injective f := f.toRingHom.injective
  have hfin_adjoin : Module.finrank ℚ (AdjoinRoot cbrt2Poly) = 3 := by
    rw [(AdjoinRoot.powerBasis irreducible_cbrt2Poly.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, cbrt2Poly_natDegree]
  have hf_surj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) (hfin_adjoin.trans finrank_K_cbrt2.symm)).mp hf_inj
  exact (AlgEquiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

/-- Any `ℚ`-algebra isomorphism of number fields preserves `Stage7DedekindZeta.dedekindZeta`. -/
theorem dedekindZeta_eq_of_algEquiv {F₁ F₂ : Type*} [Field F₁] [NumberField F₁]
    [Field F₂] [NumberField F₂] (e : F₁ ≃ₐ[ℚ] F₂) (s : ℂ) :
    Stage7DedekindZeta.dedekindZeta F₁ s = Stage7DedekindZeta.dedekindZeta F₂ s := by
  let eZ : F₁ →ₐ[ℤ] F₂ := e.toAlgHom.restrictScalars ℤ
  let eZinv : F₂ →ₐ[ℤ] F₁ := e.symm.toAlgHom.restrictScalars ℤ
  let eO : 𝓞 F₁ ≃+* 𝓞 F₂ :=
    { toFun := fun x => ⟨e x.1, IsIntegral.map eZ x.2⟩
      invFun := fun y => ⟨e.symm y.1, IsIntegral.map eZinv y.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1) }
  have hnorm_map : ∀ I : Ideal (𝓞 F₁),
      Ideal.absNorm (Ideal.map eO.toRingHom I) = Ideal.absNorm I := by
    intro I
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv I (Ideal.map eO.toRingHom I) eO rfl).symm.toEquiv
  have hlr : ∀ I : Ideal (𝓞 F₁), Ideal.map eO.symm.toRingHom (Ideal.map eO.toRingHom I) = I := by
    intro I
    rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]
  have hrl : ∀ J : Ideal (𝓞 F₂), Ideal.map eO.toRingHom (Ideal.map eO.symm.toRingHom J) = J := by
    intro J
    rw [Ideal.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Ideal.map_id]
  let eqIdeal : {I : Ideal (𝓞 F₁) // I ≠ ⊥} ≃ {J : Ideal (𝓞 F₂) // J ≠ ⊥} :=
    { toFun := fun I => ⟨Ideal.map eO.toRingHom I.1, fun hbot => by
        apply I.2
        have h1 := congrArg (Ideal.map eO.symm.toRingHom) hbot
        rw [hlr, Ideal.map_bot] at h1
        exact h1⟩
      invFun := fun J => ⟨Ideal.map eO.symm.toRingHom J.1, fun hbot => by
        apply J.2
        have h1 := congrArg (Ideal.map eO.toRingHom) hbot
        rw [hrl, Ideal.map_bot] at h1
        exact h1⟩
      left_inv := fun I => Subtype.ext (hlr I.1)
      right_inv := fun J => Subtype.ext (hrl J.1) }
  unfold Stage7DedekindZeta.dedekindZeta
  rw [← Equiv.tsum_eq eqIdeal]
  refine tsum_congr fun I => ?_
  exact congrArg (fun n : ℕ => (n : ℂ) ^ (-s)) (hnorm_map I.1).symm

/-- Exact equality `dedekindZeta K_cbrt2 s = dedekindZeta (AdjoinRoot (X³ - 2)) s`. -/
theorem dedekindZeta_K_cbrt2_eq_adjoinRoot (s : ℂ) :
    have : Fact (Irreducible cbrt2Poly) := ⟨irreducible_cbrt2Poly⟩
    have : NumberField (AdjoinRoot cbrt2Poly) :=
      NumberField.of_module_finite ℚ (AdjoinRoot cbrt2Poly)
    Stage7DedekindZeta.dedekindZeta K_cbrt2 s =
      Stage7DedekindZeta.dedekindZeta (AdjoinRoot cbrt2Poly) s := by
  have : Fact (Irreducible cbrt2Poly) := ⟨irreducible_cbrt2Poly⟩
  have : NumberField (AdjoinRoot cbrt2Poly) :=
    NumberField.of_module_finite ℚ (AdjoinRoot cbrt2Poly)
  exact dedekindZeta_eq_of_algEquiv K_cbrt2EquivAdjoinRoot s

lemma minpoly_omegaCbrt2 : minpoly ℚ omegaCbrt2 = Polynomial.cyclotomic 3 ℚ := by
  have hirr : Irreducible (Polynomial.cyclotomic 3 ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (by norm_num)
  have hmon : (Polynomial.cyclotomic 3 ℚ).Monic := Polynomial.cyclotomic.monic 3 ℚ
  have haeval : Polynomial.aeval omegaCbrt2 (Polynomial.cyclotomic 3 ℚ) = 0 := by
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    rw [Polynomial.cyclotomic_prime ℚ 3]
    change Polynomial.aeval omegaCbrt2 (∑ i ∈ Finset.range 3, Polynomial.X ^ i) = 0
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pow_zero,
      pow_one, Polynomial.aeval_add, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_one]
    linear_combination omegaCbrt2_sq_add_add_one
  exact (minpoly.eq_of_irreducible_of_monic hirr haeval hmon).symm

private def galCbrt2ToS3 : (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) →* Equiv.Perm (Fin 3) where
  toFun σ :=
    let p : Equiv.Perm (cbrt2Poly.rootSet L_cbrt2) :=
      { toFun := fun r => ⟨σ r.1, by
          have hr := r.2
          rw [Polynomial.mem_rootSet_of_ne irreducible_cbrt2Poly.ne_zero] at hr ⊢
          rw [Polynomial.aeval_algHom_apply, hr, map_zero]⟩
        invFun := fun r => ⟨σ⁻¹ r.1, by
          have hr := r.2
          rw [Polynomial.mem_rootSet_of_ne irreducible_cbrt2Poly.ne_zero] at hr ⊢
          rw [Polynomial.aeval_algHom_apply, hr, map_zero]⟩
        left_inv := fun r => Subtype.ext (σ.symm_apply_apply r.1)
        right_inv := fun r => Subtype.ext (σ.apply_symm_apply r.1) }
    (Equiv.permCongr rootEquivFin3.symm) p
  map_one' := by
    refine Equiv.Perm.ext fun i => ?_
    apply rootEquivFin3.injective
    apply Subtype.ext
    simp [Equiv.permCongr_apply]
  map_mul' σ τ := by
    refine Equiv.Perm.ext fun i => ?_
    apply rootEquivFin3.injective
    apply Subtype.ext
    simp [Equiv.permCongr_apply, AlgEquiv.mul_apply]

private lemma galCbrt2ToS3_injective : Function.Injective galCbrt2ToS3 := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hfix_root : ∀ r : cbrt2Poly.rootSet L_cbrt2, σ r.1 = r.1 := by
    intro r
    obtain ⟨i, rfl⟩ := rootEquivFin3.surjective r
    have hi : galCbrt2ToS3 σ i = i := by rw [hσ]; rfl
    have h1 := congrArg (fun j : Fin 3 => (rootEquivFin3 j).1) hi
    simpa [galCbrt2ToS3, Equiv.permCongr_apply] using h1
  have hadj : Algebra.adjoin ℚ (cbrt2Poly.rootSet L_cbrt2) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet cbrt2Poly
  have hle : Algebra.adjoin ℚ (cbrt2Poly.rootSet L_cbrt2) ≤
      AlgHom.equalizer σ.toAlgHom (AlgHom.id ℚ L_cbrt2) := by
    rw [Algebra.adjoin_le_iff]
    intro r hr
    exact hfix_root ⟨r, hr⟩
  rw [hadj, top_le_iff] at hle
  ext x
  have hx : x ∈ AlgHom.equalizer σ.toAlgHom (AlgHom.id ℚ L_cbrt2) := by
    rw [hle]; trivial
  exact hx

lemma finrank_L_cbrt2_dvd_and_eq :
    Module.finrank ℚ L_cbrt2 = 6 := by
  let F_omega := IntermediateField.adjoin ℚ {omegaCbrt2}
  have hfin_omega : Module.finrank ℚ F_omega = 2 := by
    have hint : IsIntegral ℚ omegaCbrt2 := Algebra.IsIntegral.isIntegral omegaCbrt2
    rw [show F_omega = IntermediateField.adjoin ℚ {omegaCbrt2} from rfl,
      IntermediateField.adjoin.finrank hint, minpoly_omegaCbrt2, Polynomial.natDegree_cyclotomic]
    decide
  have h2_dvd : 2 ∣ Module.finrank ℚ L_cbrt2 := by
    rw [← hfin_omega, ← Module.finrank_mul_finrank ℚ F_omega L_cbrt2]
    exact dvd_mul_right _ _
  have h3_dvd : 3 ∣ Module.finrank ℚ L_cbrt2 := by
    rw [← finrank_K_cbrt2, ← Module.finrank_mul_finrank ℚ K_cbrt2 L_cbrt2]
    exact dvd_mul_right _ _
  have h6_dvd : 6 ∣ Module.finrank ℚ L_cbrt2 := by omega
  have hpos : 0 < Module.finrank ℚ L_cbrt2 := Module.finrank_pos
  have hle6 : Module.finrank ℚ L_cbrt2 ≤ 6 := by
    rw [← IsGalois.card_aut_eq_finrank ℚ L_cbrt2, Nat.card_eq_fintype_card]
    calc Fintype.card (L_cbrt2 ≃ₐ[ℚ] L_cbrt2)
        ≤ Fintype.card (Equiv.Perm (Fin 3)) :=
          Fintype.card_le_of_injective galCbrt2ToS3 galCbrt2ToS3_injective
      _ = 6 := by decide
  have h6le : 6 ≤ Module.finrank ℚ L_cbrt2 := Nat.le_of_dvd hpos h6_dvd
  exact le_antisymm hle6 h6le

/-- **Genuine Galois Group Isomorphism `Gal(ℚ(∛2, ω) / ℚ) ≃* S₃`**. -/
def galCbrt2EquivS3 : (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ≃* Equiv.Perm (Fin 3) := by
  have hcard : Fintype.card (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) = Fintype.card (Equiv.Perm (Fin 3)) := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ L_cbrt2,
      finrank_L_cbrt2_dvd_and_eq]
    decide
  exact MulEquiv.ofBijective galCbrt2ToS3
    ((Fintype.bijective_iff_injective_and_card galCbrt2ToS3).mpr ⟨galCbrt2ToS3_injective, hcard⟩)

@[simp]
lemma galCbrt2EquivS3_apply_zero (σ : L_cbrt2 ≃ₐ[ℚ] L_cbrt2) :
    (rootEquivFin3 (galCbrt2EquivS3 σ 0)).1 = σ alpha0 := by
  simp [galCbrt2EquivS3, galCbrt2ToS3, alpha0, Equiv.permCongr_apply]

/-- Under `Gal(L_cbrt2 / ℚ) ≃* S₃`, the fixing subgroup of `K_cbrt2 = ℚ(∛2)` corresponds
EXACTLY to `Stage10ArtinLFunctions.s3C2 = Stab_{S₃}(0)`. -/
theorem fixingSubgroup_K_cbrt2_eq_comap_s3C2 :
    K_cbrt2.fixingSubgroup =
      Subgroup.comap galCbrt2EquivS3.toMonoidHom Stage10ArtinLFunctions.s3C2 := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_comap]
  constructor
  · intro hfix
    change galCbrt2EquivS3 σ • (0 : Fin 3) = 0
    apply rootEquivFin3.injective
    apply Subtype.ext
    change (rootEquivFin3 (galCbrt2EquivS3 σ 0)).1 = alpha0
    rw [galCbrt2EquivS3_apply_zero]
    exact hfix alpha0 (IntermediateField.mem_adjoin_simple_self ℚ alpha0)
  · intro hstab x hx
    have h0 : σ alpha0 = alpha0 := by
      rw [← galCbrt2EquivS3_apply_zero σ]
      have h0' : galCbrt2EquivS3 σ 0 = 0 := hstab
      rw [h0']
      rfl
    have hle : K_cbrt2 ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [K_cbrt2, IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      rw [Subgroup.mem_zpowers_iff] at hτ
      obtain ⟨k, rfl⟩ := hτ
      have hpow : ∀ n : ℕ, (σ ^ n) alpha0 = alpha0 := by
        intro n; induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ', AlgEquiv.mul_apply, ih, h0]
      have hzpow : (σ ^ k) alpha0 = alpha0 := by
        cases k with
        | ofNat n => simpa using hpow n
        | negSucc n =>
          have h1 : (σ ^ (n + 1)) ((σ ^ (-(n + 1 : ℤ))) alpha0) = alpha0 := by
            have hsum0 : ((n + 1 : ℕ) : ℤ) + -(n + 1 : ℤ) = 0 := by omega
            rw [← AlgEquiv.mul_apply, ← zpow_natCast, ← zpow_add, hsum0, zpow_zero,
              AlgEquiv.one_apply]
          have h2 : (σ ^ (n + 1)) alpha0 = alpha0 := hpow (n + 1)
          exact (σ ^ (n + 1)).injective (h1.trans h2.symm)
      exact hzpow
    have hx' := hle hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.mem_zpowers σ)

/-- The genuine 2-dimensional irreducible `S₃` Galois representation of `Gal(ℚ(∛2, ω) / ℚ)`. -/
def rho2Cbrt2 : Representation ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) (Fin 2 → ℂ) :=
  Stage10ArtinLFunctions.s3Rho2.comp galCbrt2EquivS3.toMonoidHom

theorem rho2Cbrt2_isIrreducible : Representation.IsIrreducible rho2Cbrt2 := by
  have hirr := Stage10ArtinLFunctions.s3Rho2_isIrreducible
  let eSub : Subrepresentation Stage10ArtinLFunctions.s3Rho2 ≃o Subrepresentation rho2Cbrt2 :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := fun g v hv => S.apply_mem_toSubmodule (galCbrt2EquivS3 g) hv }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := fun g v hv => by
            have h1 := S.apply_mem_toSubmodule (galCbrt2EquivS3.symm g) hv
            change rho2Cbrt2 (galCbrt2EquivS3.symm g) v ∈ S.toSubmodule at h1
            simpa [rho2Cbrt2] using h1 }
      left_inv := fun _ => Subrepresentation.ext rfl
      right_inv := fun _ => Subrepresentation.ext rfl
      map_rel_iff' := Iff.rfl }
  exact eSub.isSimpleOrder_iff.mp hirr

/-- **Unramifiedness of `ℚ(∛2, ω)` away from `{2, 3}`**:
every rational prime `p ≠ 2, 3` is unramified in `L_cbrt2` (`p ∉ ramifiedPrimes L_cbrt2`). -/
theorem isUnramifiedIn_L_cbrt2_of_ne_two_three {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Algebra.IsUnramifiedIn (𝓞 L_cbrt2) (Ideal.span {(p : ℤ)}) := by
  intro Q hQ hQ_lo
  have hbot : Q.inertia (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    have hα_int : IsIntegral ℤ alpha0 := by
      refine ⟨cbrt2PolyZ, cbrt2PolyZ_monic, ?_⟩
      simp [cbrt2PolyZ, alpha0_pow_three]
    let α₀ : 𝓞 L_cbrt2 := ⟨alpha0, hα_int⟩
    have hω_int : IsIntegral ℤ omegaCbrt2 := by
      refine ⟨Polynomial.X ^ 3 - 1, Polynomial.monic_X_pow_sub_C 1 (by norm_num), ?_⟩
      simp [omegaCbrt2_pow_three]
    let ω₀ : 𝓞 L_cbrt2 := ⟨omegaCbrt2, hω_int⟩
    have hσ_α : σ alpha0 = alpha0 := by
      by_contra hne
      let u : L_cbrt2 := σ alpha0 * alpha0⁻¹
      have hσα_pow : (σ alpha0) ^ 3 = 2 := by
        rw [← map_pow, alpha0_pow_three, map_ofNat]
      have hu3 : u ^ 3 = 1 := by
        dsimp [u]
        rw [mul_pow, inv_pow, hσα_pow, alpha0_pow_three]
        norm_num
      have hu_ne1 : u ≠ 1 := by
        intro hu1
        apply hne
        calc σ alpha0 = u * alpha0 := by
              dsimp [u]; rw [mul_assoc, inv_mul_cancel₀ alpha0_ne_zero, mul_one]
          _ = 1 * alpha0 := by rw [hu1]
          _ = alpha0 := one_mul _
      have hu2 : u ^ 2 + u + 1 = 0 := by
        have hfac : (u - 1) * (u ^ 2 + u + 1) = 0 := by
          calc (u - 1) * (u ^ 2 + u + 1) = u ^ 3 - 1 := by ring
            _ = 0 := by rw [hu3, sub_self]
        exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hu_ne1)
      have hu_int : IsIntegral ℤ u := by
        refine ⟨Polynomial.X ^ 3 - 1, Polynomial.monic_X_pow_sub_C 1 (by norm_num), ?_⟩
        simp [hu3]
      let u₀ : 𝓞 L_cbrt2 := ⟨u, hu_int⟩
      have hmemQ : σ • α₀ - α₀ ∈ Q := AddSubgroup.mem_inertia.mp hσ α₀
      have h6_eq : (σ • α₀ - α₀) * ((u₀ ^ 2 - 1) * α₀ ^ 2) = (6 : 𝓞 L_cbrt2) := by
        apply Subtype.ext
        change (σ alpha0 - alpha0) * ((u ^ 2 - 1) * alpha0 ^ 2) = (6 : L_cbrt2)
        have h1 : σ alpha0 = u * alpha0 := by
          dsimp [u]
          rw [mul_assoc, inv_mul_cancel₀ alpha0_ne_zero, mul_one]
        rw [h1]
        calc (u * alpha0 - alpha0) * ((u ^ 2 - 1) * alpha0 ^ 2)
            = (u - 1) * (u ^ 2 - 1) * alpha0 ^ 3 := by ring
          _ = (u ^ 3 - u ^ 2 - u + 1) * 2 := by rw [alpha0_pow_three]; ring
          _ = (1 - (u ^ 2 + u) + 1) * 2 := by rw [hu3]; ring
          _ = (1 - (-1) + 1) * 2 := by rw [show u ^ 2 + u = -1 by linear_combination hu2]
          _ = 6 := by norm_num
      have h6Q : (6 : 𝓞 L_cbrt2) ∈ Q := h6_eq ▸ Ideal.mul_mem_right _ Q hmemQ
      have h6Z : (6 : ℤ) ∈ Q.under ℤ := by
        rw [Ideal.under, Ideal.mem_comap]
        simpa using h6Q
      rw [← hQ_lo.over, Ideal.mem_span_singleton] at h6Z
      have hdvd : p ∣ 6 := Int.natCast_dvd_natCast.mp h6Z
      have hcases : p = 2 ∨ p = 3 := by
        have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases p <;> simp_all (config := { decide := true })
      rcases hcases with rfl | rfl
      · exact hp2 rfl
      · exact hp3 rfl
    have hσ_ω : σ omegaCbrt2 = omegaCbrt2 := by
      by_contra hne
      have hσω3 : (σ omegaCbrt2) ^ 3 = 1 := by
        rw [← map_pow, omegaCbrt2_pow_three, map_one]
      have hσω2 : (σ omegaCbrt2) ^ 2 + σ omegaCbrt2 + 1 = 0 := by
        have h1 := congrArg σ omegaCbrt2_sq_add_add_one
        simpa using h1
      have hsum : σ omegaCbrt2 + omegaCbrt2 = -1 := by
        have hdiff : (σ omegaCbrt2 - omegaCbrt2) * (σ omegaCbrt2 + omegaCbrt2 + 1) = 0 := by
          calc (σ omegaCbrt2 - omegaCbrt2) * (σ omegaCbrt2 + omegaCbrt2 + 1)
              = ((σ omegaCbrt2) ^ 2 + σ omegaCbrt2 + 1) - (omegaCbrt2 ^ 2 + omegaCbrt2 + 1) := by ring
            _ = 0 - 0 := by rw [hσω2, omegaCbrt2_sq_add_add_one]
            _ = 0 := sub_zero 0
        have hzero := (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne)
        linear_combination hzero
      have hprod : σ omegaCbrt2 * omegaCbrt2 = 1 := by
        have h1 : σ omegaCbrt2 = -1 - omegaCbrt2 := by linear_combination hsum
        rw [h1]
        linear_combination -omegaCbrt2_sq_add_add_one
      have hmemQ : σ • ω₀ - ω₀ ∈ Q := AddSubgroup.mem_inertia.mp hσ ω₀
      have h3_eq : (σ • ω₀ - ω₀) ^ 2 = (-3 : 𝓞 L_cbrt2) := by
        apply Subtype.ext
        change (σ omegaCbrt2 - omegaCbrt2) ^ 2 = (-3 : L_cbrt2)
        calc (σ omegaCbrt2 - omegaCbrt2) ^ 2
            = (σ omegaCbrt2 + omegaCbrt2) ^ 2 - 4 * (σ omegaCbrt2 * omegaCbrt2) := by ring
          _ = (-1) ^ 2 - 4 * 1 := by rw [hsum, hprod]
          _ = -3 := by norm_num
      have h3Q : (-3 : 𝓞 L_cbrt2) ∈ Q := h3_eq ▸ Ideal.pow_mem_of_mem Q hmemQ 2 (by norm_num)
      have h3Z : (-3 : ℤ) ∈ Q.under ℤ := by
        rw [Ideal.under, Ideal.mem_comap]
        simpa using h3Q
      rw [← hQ_lo.over, Ideal.mem_span_singleton] at h3Z
      have hdvd : p ∣ 3 := by
        have : (p : ℤ) ∣ 3 := dvd_neg.mp h3Z
        exact Int.natCast_dvd_natCast.mp this
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with h1 | h3
      · exact absurd h1 hp.ne_one
      · exact hp3 h3
    have hfix_root : ∀ r : cbrt2Poly.rootSet L_cbrt2, σ r.1 = r.1 := by
      intro r
      have hr3 : r.1 ^ 3 = 2 := rootSet_pow_three r.2
      let q : L_cbrt2 := r.1 * alpha0⁻¹
      have hq3 : q ^ 3 = 1 := by
        dsimp [q]; rw [mul_pow, inv_pow, hr3, alpha0_pow_three]; norm_num
      have hfac : (q - 1) * (q - omegaCbrt2) * (q - omegaCbrt2 ^ 2) = 0 := by
        calc (q - 1) * (q - omegaCbrt2) * (q - omegaCbrt2 ^ 2)
            = q ^ 3 - (1 + omegaCbrt2 + omegaCbrt2 ^ 2) * q ^ 2 +
                (omegaCbrt2 + omegaCbrt2 ^ 2 + omegaCbrt2 ^ 3) * q - omegaCbrt2 ^ 3 := by ring
          _ = q ^ 3 - 0 * q ^ 2 + (omegaCbrt2 + omegaCbrt2 ^ 2 + 1) * q - 1 := by
                rw [omegaCbrt2_pow_three]
                linear_combination -q ^ 2 * omegaCbrt2_sq_add_add_one
          _ = q ^ 3 - 1 := by linear_combination q * omegaCbrt2_sq_add_add_one
          _ = 0 := by rw [hq3, sub_self]
      have hr_eq : r.1 = q * alpha0 := by
        dsimp [q]; rw [mul_assoc, inv_mul_cancel₀ alpha0_ne_zero, mul_one]
      rcases mul_eq_zero.mp hfac with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · have : q = 1 := sub_eq_zero.mp h1
          rw [hr_eq, this, one_mul, hσ_α]
        · have : q = omegaCbrt2 := sub_eq_zero.mp h2
          rw [hr_eq, this, map_mul, hσ_ω, hσ_α]
      · have : q = omegaCbrt2 ^ 2 := sub_eq_zero.mp h3
        rw [hr_eq, this, map_mul, map_pow, hσ_ω, hσ_α]
    have hadj : Algebra.adjoin ℚ (cbrt2Poly.rootSet L_cbrt2) = ⊤ :=
      Polynomial.SplittingField.adjoin_rootSet cbrt2Poly
    have hle : Algebra.adjoin ℚ (cbrt2Poly.rootSet L_cbrt2) ≤
        AlgHom.equalizer σ.toAlgHom (AlgHom.id ℚ L_cbrt2) := by
      rw [Algebra.adjoin_le_iff]
      intro r hr
      exact hfix_root ⟨r, hr⟩
    rw [hadj, top_le_iff] at hle
    ext x
    have hx : x ∈ AlgHom.equalizer σ.toAlgHom (AlgHom.id ℚ L_cbrt2) := by
      rw [hle]; trivial
    exact hx
  have he1 : Q.ramificationIdx ℤ = 1 := by
    have hne : Q ≠ ⊥ := by
      have hsp : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.mpr hp.ne_zero
      exact Ideal.ne_bot_of_liesOver_of_ne_bot hsp Q
    let w : HeightOneSpectrum (𝓞 L_cbrt2) := ⟨Q, hQ, hne⟩
    have hw_lo : w.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
      (liesOver_placeOfPrime_iff_liesOver_span w hp).mpr hQ_lo
    rw [← ramificationIdx_rat_eq_int w hp, ← RHDirect.CFT.Global.natCard_inertia (placeOfPrime p hp) w,
      hbot]
    exact Nat.card_unique
  exact Ideal.ramificationIdx_eq_one_iff.mp he1

theorem notMem_ramifiedPrimes_L_cbrt2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    p ∉ ramifiedPrimes L_cbrt2 := by
  rw [mem_ramifiedPrimes_iff hp]
  push Not
  exact isUnramifiedIn_L_cbrt2_of_ne_two_three hp hp2 hp3

/-- Local Euler factor of `Ind_{Gal(L/K)}^{Gal(L/ℚ)} 1` equals `(1 - T)⁻¹ · det(1 - T ρ₂(g))⁻¹`
for EVERY `g ∈ Gal(L_cbrt2 / ℚ)`. -/
theorem artinLocalFactor_ind_K_cbrt2 (g : L_cbrt2 ≃ₐ[ℚ] L_cbrt2) (T : ℂ) :
    Stage10ArtinLFunctions.artinLocalFactor
        (Representation.ind K_cbrt2.fixingSubgroup.subtype
          (Representation.trivial ℂ K_cbrt2.fixingSubgroup ℂ)) g T =
      (1 - T)⁻¹ * Stage10ArtinLFunctions.artinLocalFactor rho2Cbrt2 g T := by
  let qEquiv : ((L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ⧸ K_cbrt2.fixingSubgroup) ≃
      (Equiv.Perm (Fin 3) ⧸ Stage10ArtinLFunctions.s3C2) :=
    { toFun := Quotient.lift (fun x => QuotientGroup.mk (galCbrt2EquivS3 x)) fun x₁ x₂ hrel => by
        apply Quotient.sound
        have hmem : x₁⁻¹ * x₂ ∈ K_cbrt2.fixingSubgroup := QuotientGroup.leftRel_apply.mp hrel
        rw [fixingSubgroup_K_cbrt2_eq_comap_s3C2, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          map_mul, map_inv] at hmem
        exact QuotientGroup.leftRel_apply.mpr hmem
      invFun := Quotient.lift (fun y => QuotientGroup.mk (galCbrt2EquivS3.symm y)) fun y₁ y₂ hrel => by
        apply Quotient.sound
        have hmem : y₁⁻¹ * y₂ ∈ Stage10ArtinLFunctions.s3C2 := QuotientGroup.leftRel_apply.mp hrel
        have hmem' : (galCbrt2EquivS3.symm y₁)⁻¹ * galCbrt2EquivS3.symm y₂ ∈ K_cbrt2.fixingSubgroup := by
          rw [fixingSubgroup_K_cbrt2_eq_comap_s3C2, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
            map_mul, map_inv, galCbrt2EquivS3.apply_symm_apply, galCbrt2EquivS3.apply_symm_apply]
          exact hmem
        exact QuotientGroup.leftRel_apply.mpr hmem'
      left_inv := fun q => by
        obtain ⟨x, rfl⟩ := Quotient.exists_rep q
        change QuotientGroup.mk (galCbrt2EquivS3.symm (galCbrt2EquivS3 x)) = QuotientGroup.mk x
        rw [galCbrt2EquivS3.symm_apply_apply]
      right_inv := fun q => by
        obtain ⟨y, rfl⟩ := Quotient.exists_rep q
        change QuotientGroup.mk (galCbrt2EquivS3 (galCbrt2EquivS3.symm y)) = QuotientGroup.mk y
        rw [galCbrt2EquivS3.apply_symm_apply] }
  have hq_smul : ∀ (a : L_cbrt2 ≃ₐ[ℚ] L_cbrt2)
      (q : (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ⧸ K_cbrt2.fixingSubgroup),
      qEquiv (a • q) = galCbrt2EquivS3 a • qEquiv q := by
    intro a q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change QuotientGroup.mk (galCbrt2EquivS3 (a * x)) =
      QuotientGroup.mk (galCbrt2EquivS3 a * galCbrt2EquivS3 x)
    rw [map_mul]
  let eRep : Representation.Equiv
      (Representation.ofMulAction ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2)
        ((L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ⧸ K_cbrt2.fixingSubgroup))
      ((Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ Stage10ArtinLFunctions.s3C2)).comp galCbrt2EquivS3.toMonoidHom) := by
    refine Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ qEquiv) fun a => ?_
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ qEquiv
        ((Representation.ofMulAction ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2)
          ((L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ⧸ K_cbrt2.fixingSubgroup)) a
          (MonoidAlgebra.single q (1 : ℂ))) =
      (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ Stage10ArtinLFunctions.s3C2)) (galCbrt2EquivS3 a)
        (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ qEquiv (MonoidAlgebra.single q (1 : ℂ)))
    rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearEquiv_single,
      MonoidAlgebra.mapDomainLinearEquiv_single, Representation.ofMulAction_single, hq_smul]
  rw [Stage10ArtinLFunctions.artinLocalFactor_iso
      (Stage10ArtinLFunctions.indTrivialEquivOfMulAction K_cbrt2.fixingSubgroup) g T,
    Stage10ArtinLFunctions.artinLocalFactor_iso eRep g T]
  change Stage10ArtinLFunctions.artinLocalFactor
      (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ Stage10ArtinLFunctions.s3C2)) (galCbrt2EquivS3 g) T = _
  rw [Stage10ArtinLFunctions.artinLocalFactor_s3_cosetC2 (galCbrt2EquivS3 g) T]
  have htriv : Stage10ArtinLFunctions.artinLocalFactor Stage10ArtinLFunctions.s3Triv
      (galCbrt2EquivS3 g) T = (1 - T)⁻¹ :=
    Stage10ArtinLFunctions.artinLocalFactor_trivial (galCbrt2EquivS3 g) T
  rw [htriv]
  rfl

/-- **CONCRETE GENUINE `S₃` LOCAL DEDEKIND–ARTIN FACTORIZATION FOR `ℚ(∛2)` (ZERO PROXIES!)**:
For EVERY rational prime `p ≠ 2, 3`, EVERY prime `w` of `𝓞 L_cbrt2` lying over `p`, and EVERY `s : ℂ`,
the actual local Dedekind zeta Euler factor of `K = ℚ(∛2)` at `p` equals:
`(1 - p^{-s})⁻¹ · det(1 - p^{-s} ρ₂(arithFrobAt (𝓞 ℚ) Gal(L/ℚ) w.asIdeal))⁻¹`. -/
theorem cbrt2_local_dedekindZeta_eq_genuine_S3 {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (w : Stage7DedekindZeta.PrimesAbove L_cbrt2 p)
    [Fintype (Stage7DedekindZeta.PrimesAbove K_cbrt2 p)] (s : ℂ) :
    ∏ u : Stage7DedekindZeta.PrimesAbove K_cbrt2 p, (1 - (Ideal.absNorm u.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      (1 - (p : ℂ) ^ (-s))⁻¹ *
        Stage10ArtinLFunctions.artinLocalFactor rho2Cbrt2
          (arithFrobAt (𝓞 ℚ) (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) w.1.asIdeal) ((p : ℂ) ^ (-s)) := by
  have hunr : p ∉ ramifiedPrimes L_cbrt2 := notMem_ramifiedPrimes_L_cbrt2 hp hp2 hp3
  rw [intermediateField_local_dedekind_eulerFactor_eq_ind L_cbrt2 K_cbrt2 hp hunr s,
    artinLocalFactor_ind_K_cbrt2]
  congr 1
  have : (chosenPlaceAbove L_cbrt2 p hp).1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm _ hp).mpr (chosenPlaceAbove L_cbrt2 p hp).2
  have : w.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm _ hp).mpr w.2
  exact artinLocalFactor_arithFrobAt_indep rho2Cbrt2 hp hunr
    (chosenPlaceAbove L_cbrt2 p hp).1 w.1 ((p : ℂ) ^ (-s))

/-- **CONCRETE GENUINE `S₃` GLOBAL DEDEKIND–ARTIN FACTORIZATION FOR `ℚ(∛2)`**:
On `1 < s.re`:
`dedekindZetaUnramified K_cbrt2 (ramifiedPrimes L_cbrt2) s = genuineArtinL L_cbrt2 1 s * genuineArtinL L_cbrt2 rho2Cbrt2 s`,
and away from `{2, 3}`, `dedekindZetaUnramified K_cbrt2 {2, 3} s` factors cleanly into the unramified
Riemann zeta times the genuine `S₃` Artin `L`-function `L(rho2Cbrt2, s)`! -/
theorem cbrt2_global_dedekindZetaUnramified_eq_genuine_S3 {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaUnramified K_cbrt2 (ramifiedPrimes L_cbrt2) s =
      genuineArtinL L_cbrt2 (Representation.trivial ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ℂ) s *
        genuineArtinL L_cbrt2 rho2Cbrt2 s := by
  rw [dedekindZetaUnramified_intermediateField_eq_genuineArtinL_ind L_cbrt2 K_cbrt2 hs]
  unfold genuineArtinL Stage10ArtinLFunctions.artinL
  have hloc : ∀ p : {p : ℕ // p.Prime ∧ p ∉ ramifiedPrimes L_cbrt2},
      Stage10ArtinLFunctions.artinLocalFactor
          (Representation.ind K_cbrt2.fixingSubgroup.subtype
            (Representation.trivial ℂ K_cbrt2.fixingSubgroup ℂ))
          (genuineFrobAt L_cbrt2 p.1 p.2.1) ((p.1 : ℂ) ^ (-s)) =
        Stage10ArtinLFunctions.artinLocalFactor
            (Representation.trivial ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ℂ)
            (genuineFrobAt L_cbrt2 p.1 p.2.1) ((p.1 : ℂ) ^ (-s)) *
          Stage10ArtinLFunctions.artinLocalFactor rho2Cbrt2
            (genuineFrobAt L_cbrt2 p.1 p.2.1) ((p.1 : ℂ) ^ (-s)) := by
    intro p
    rw [artinLocalFactor_ind_K_cbrt2,
      Stage10ArtinLFunctions.artinLocalFactor_trivial (genuineFrobAt L_cbrt2 p.1 p.2.1) ((p.1 : ℂ) ^ (-s))]
  rw [tprod_congr hloc]
  exact (genuineArtinL_multipliable L_cbrt2 _ hs).tprod_mul
    (genuineArtinL_multipliable L_cbrt2 rho2Cbrt2 hs)

theorem cbrt2_global_dedekindZetaUnramified_two_three {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaUnramified K_cbrt2 ({2, 3} : Finset ℕ) s =
      Stage10ArtinLFunctions.artinL ({2, 3} : Finset ℕ)
        (fun p => genuineFrobAt L_cbrt2 p.1 p.2.1)
        (Representation.trivial ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ℂ) s *
      Stage10ArtinLFunctions.artinL ({2, 3} : Finset ℕ)
        (fun p => genuineFrobAt L_cbrt2 p.1 p.2.1) rho2Cbrt2 s := by
  let frob : {p : ℕ // p.Prime ∧ p ∉ ({2, 3} : Finset ℕ)} → (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) :=
    fun p => genuineFrobAt L_cbrt2 p.1 p.2.1
  have hloc : ∀ p : {p : ℕ // p.Prime ∧ p ∉ ({2, 3} : Finset ℕ)},
      ∀ [Fintype (Stage7DedekindZeta.PrimesAbove K_cbrt2 p.1)],
      ∏ u : Stage7DedekindZeta.PrimesAbove K_cbrt2 p.1,
          (1 - (Ideal.absNorm u.1.asIdeal : ℂ) ^ (-s))⁻¹ =
        Stage10ArtinLFunctions.artinLocalFactor
          (Representation.prod (Representation.trivial ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ℂ) rho2Cbrt2)
          (frob p) ((p.1 : ℂ) ^ (-s)) := by
    intro p _
    have hp2 : p.1 ≠ 2 := fun h => p.2.2 (by simp [h])
    have hp3 : p.1 ≠ 3 := fun h => p.2.2 (by simp [h])
    rw [Stage10ArtinLFunctions.artinLocalFactor_prod,
      Stage10ArtinLFunctions.artinLocalFactor_trivial (frob p) ((p.1 : ℂ) ^ (-s))]
    exact cbrt2_local_dedekindZeta_eq_genuine_S3 p.2.1 hp2 hp3 (chosenPlaceAbove L_cbrt2 p.1 p.2.1) s
  have hmult := Stage10ArtinLFunctions.artinL_multipliable ({2, 3} : Finset ℕ) frob
    (Representation.prod (Representation.trivial ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ℂ) rho2Cbrt2) hs
  rw [dedekindZetaUnramified_eq_tprod_of_local K_cbrt2 ({2, 3} : Finset ℕ) s _ hloc hmult hs]
  exact Stage10ArtinLFunctions.artinL_prod ({2, 3} : Finset ℕ) frob
    (Representation.trivial ℂ (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) ℂ) rho2Cbrt2 hs

/-- For every prime `p ≠ 2, 3` and every `w | p` in `𝓞 L_cbrt2`, the inertia degree `f_w` of `w`
over `p` equals the order of `arithFrobAt w`, belongs to `{1, 2, 3}`, and completely determines the
local Euler factor of `Stage7DedekindZeta.dedekindZeta K_cbrt2` at `p` via `rho2Cbrt2`. -/
theorem cbrt2_local_eulerFactor_cases_by_inertiaDeg {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (w : Stage7DedekindZeta.PrimesAbove L_cbrt2 p)
    [Fintype (Stage7DedekindZeta.PrimesAbove K_cbrt2 p)] (s : ℂ) :
    let f_w := w.1.asIdeal.inertiaDeg (𝓞 ℚ)
    (f_w = 1 ∨ f_w = 2 ∨ f_w = 3) ∧
      (f_w = 1 →
        ∏ u : Stage7DedekindZeta.PrimesAbove K_cbrt2 p, (1 - (Ideal.absNorm u.1.asIdeal : ℂ) ^ (-s))⁻¹ =
          (1 - (p : ℂ) ^ (-s))⁻¹ ^ 3) ∧
      (f_w = 2 →
        ∏ u : Stage7DedekindZeta.PrimesAbove K_cbrt2 p, (1 - (Ideal.absNorm u.1.asIdeal : ℂ) ^ (-s))⁻¹ =
          (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - (p : ℂ) ^ (-2 * s))⁻¹) ∧
      (f_w = 3 →
        ∏ u : Stage7DedekindZeta.PrimesAbove K_cbrt2 p, (1 - (Ideal.absNorm u.1.asIdeal : ℂ) ^ (-s))⁻¹ =
          (1 - (p : ℂ) ^ (-s))⁻¹ * (1 + (p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s))⁻¹) := by
  intro f_w
  have hunr : p ∉ ramifiedPrimes L_cbrt2 := notMem_ramifiedPrimes_L_cbrt2 hp hp2 hp3
  have : w.1.asIdeal.LiesOver (placeOfPrime p hp).asIdeal :=
    (liesOver_placeOfPrime_iff_dvd_absNorm w.1 hp).mpr w.2
  have hord : orderOf (arithFrobAt (𝓞 ℚ) (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) w.1.asIdeal) = f_w :=
    orderOf_arithFrobAt_eq_inertiaDeg hp hunr w.1
  let σ : Equiv.Perm (Fin 3) :=
    galCbrt2EquivS3 (arithFrobAt (𝓞 ℚ) (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) w.1.asIdeal)
  have hordσ : orderOf σ = f_w := by
    rw [show σ = galCbrt2EquivS3 (arithFrobAt (𝓞 ℚ) (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) w.1.asIdeal) from rfl,
      MulEquiv.orderOf_eq, hord]
  have hcases : f_w = 1 ∨ f_w = 2 ∨ f_w = 3 := by
    rcases Stage10ArtinLFunctions.s3_order_cases σ with h1 | h3 | h2
    · exact Or.inl (by rw [← hordσ, h1, orderOf_one])
    · exact Or.inr (Or.inr (hordσ.symm.trans h3))
    · exact Or.inr (Or.inl (hordσ.symm.trans h2))
  have hpow2 : ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (-2 * s) := by
    rw [← Complex.cpow_nat_mul]
    congr 1; push_cast; ring
  have hloc := cbrt2_local_dedekindZeta_eq_genuine_S3 hp hp2 hp3 w s
  have hrho : Stage10ArtinLFunctions.artinLocalFactor rho2Cbrt2
      (arithFrobAt (𝓞 ℚ) (L_cbrt2 ≃ₐ[ℚ] L_cbrt2) w.1.asIdeal) ((p : ℂ) ^ (-s)) =
      Stage10ArtinLFunctions.artinLocalFactor Stage10ArtinLFunctions.s3Rho2 σ ((p : ℂ) ^ (-s)) := rfl
  rw [hrho] at hloc
  refine ⟨hcases, fun hf1 => ?_, fun hf2 => ?_, fun hf3 => ?_⟩
  · have hσ1 : σ = 1 := orderOf_eq_one_iff.mp (hordσ.trans hf1)
    rw [hloc, hσ1, Stage10ArtinLFunctions.artinLocalFactor_s3Rho2_one ((p : ℂ) ^ (-s))]; ring
  · rw [hloc, Stage10ArtinLFunctions.artinLocalFactor_s3Rho2_transposition (hordσ.trans hf2), hpow2]
  · rw [hloc, Stage10ArtinLFunctions.artinLocalFactor_s3Rho2_threeCycle (hordσ.trans hf3), hpow2]

end ConcreteCbrt2S3

end RHDirect.ArtinDedekind

#print axioms RHDirect.ArtinDedekind.arithFrobAt_conj_of_liesOver
#print axioms RHDirect.ArtinDedekind.artinLocalFactor_arithFrobAt_indep
#print axioms RHDirect.ArtinDedekind.orderOf_arithFrobAt_eq_inertiaDeg
#print axioms RHDirect.ArtinDedekind.genuineArtinL_eq_tprod_of_choice
#print axioms RHDirect.ArtinDedekind.intermediateField_local_dedekind_eulerFactor_eq_ind
#print axioms RHDirect.ArtinDedekind.galois_local_dedekind_eulerFactor_eq_leftRegular
#print axioms RHDirect.ArtinDedekind.dedekindZetaUnramified_intermediateField_eq_genuineArtinL_ind
#print axioms RHDirect.ArtinDedekind.dedekindZetaUnramified_galois_eq_leftRegular
#print axioms RHDirect.ArtinDedekind.dedekind_artin_factorization_galois
#print axioms RHDirect.ArtinDedekind.dedekindZeta_K_cbrt2_eq_adjoinRoot
#print axioms RHDirect.ArtinDedekind.galCbrt2EquivS3
#print axioms RHDirect.ArtinDedekind.fixingSubgroup_K_cbrt2_eq_comap_s3C2
#print axioms RHDirect.ArtinDedekind.rho2Cbrt2_isIrreducible
#print axioms RHDirect.ArtinDedekind.isUnramifiedIn_L_cbrt2_of_ne_two_three
#print axioms RHDirect.ArtinDedekind.cbrt2_local_dedekindZeta_eq_genuine_S3
#print axioms RHDirect.ArtinDedekind.cbrt2_global_dedekindZetaUnramified_eq_genuine_S3
#print axioms RHDirect.ArtinDedekind.cbrt2_global_dedekindZetaUnramified_two_three
#print axioms RHDirect.ArtinDedekind.cbrt2_local_eulerFactor_cases_by_inertiaDeg
