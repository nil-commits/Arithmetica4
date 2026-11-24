import RHDirect.Stage4ClassFieldTheory
import RHDirect.Stage5AdelicTate
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# RHDirect.Stage7DedekindZeta

Concrete, self-contained, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of:
1. **Concrete Dedekind Zeta Function `ζ_K(s)` & Ideal-Norm Counting Bounds** on Mathlib's actual
   `NumberField`, `NumberField.RingOfIntegers`, `Ideal.absNorm`, and `HeightOneSpectrum`:
   - `idealCount K n := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}` and
     `dedekindZeta K s := ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℂ) ^ (-s)`.
   - Exact prime-ideal splitting identity `∑_{v ∣ p} e_v f_v = [K : ℚ]` and multiplicity bound
     `#{v ∣ p} ≤ [K : ℚ]`, yielding `idealCount K (p^k) ≤ (k + 1)^[K : ℚ]` and coprime
     multiplicativity `idealCount K (m * n) = idealCount K m * idealCount K n`.
   - Unconditional absolute convergence and domination
     `∑'_{I ≠ ⊥} (Ideal.absNorm I)^{-σ} ≤ ((riemannZeta σ).re)^[K : ℚ]` for every `σ > 1`.
   - Unconditional exact Euler product
     `dedekindZeta K s = ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ)^(-s))⁻¹`
     for every `s : ℂ` with `1 < s.re`, identification with Mathlib's `NumberField.dedekindZeta`,
     nonvanishing `dedekindZeta K s ≠ 0` on `1 < s.re`, and `dedekindZeta ℚ s = riemannZeta s`.
2. **Exact Cyclotomic Dedekind Zeta Factorization (`ζ_{ℚ(ζ_m)}(s) = ∏_{χ mod m} L(s, χ)` away from
   `p ∣ m`)**:
   - At every unramified prime `p ∤ m`, proves `e_v = 1`, `f_v = resDeg m p hp`, `g = numPrimesAbove m p hp`,
     and `∏_{v ∣ p} (1 - N(v)^{-s})⁻¹ = dedekindCycEulerFactor m p hp s = ∏_χ (1 - χ(p) p^{-s})⁻¹`.
   - Deduces the exact global unramified product equality
     `∏' v : {v // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)}, (1 - N(v)^{-s})⁻¹ = ∏ χ, L(s, χ)`
     and full Dedekind zeta factorization on `1 < s.re`.
3. **Minkowski's Discriminant Lower Bound, Minkowski's Theorem & Exponential Discriminant Growth**:
   - Sharp Minkowski bound `((π / 4)^r₂ * (d^d / d!))^2 ≤ |NumberField.discr K|`.
   - Minkowski's Theorem (`1 < [K : ℚ] → 1 < |NumberField.discr K|`, in fact `2 < |discr K|`,
     and existence of a ramified rational prime `p`).
   - Exponential lower bound `4 / 9 * (3 π / 4)^d ≤ |discr K|` and super-linear growth
     `|discr K| / d → ∞` (hence `|discr K| → ∞`) as `d = [K : ℚ] → ∞`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex NumberField IsDedekindDomain Finset
open scoped BigOperators NumberField Real Topology

namespace RHDirect.Stage7DedekindZeta

/-! ## Section 1: Concrete Ideal-Norm Counting, Prime-Ideal Splitting & Multiplicativity -/

section IdealCounting

variable (K : Type*) [Field K] [NumberField K]

/-- Number of integral ideals of `𝓞 K` of absolute norm `n`. -/
def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- Concrete Dedekind zeta function `ζ_K(s) = ∑'_{I ≠ ⊥} N(I)^{-s}` over all nonzero ideals
of the ring of integers `𝓞 K`. -/
def dedekindZeta (s : ℂ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℂ) ^ (-s)

/-- Nonzero ideals of `𝓞 K` have strictly positive absolute norm. -/
theorem absNorm_pos_of_ne_bot {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 0 < Ideal.absNorm I :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hI)

/-- `idealCount K 0 = 1` (only the zero ideal `⊥` has absolute norm `0`). -/
theorem idealCount_zero : idealCount K 0 = 1 := by
  unfold idealCount
  let : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} :=
    { default := ⟨⊥, Ideal.absNorm_bot⟩
      uniq := fun ⟨I, hI⟩ => Subtype.ext (Ideal.absNorm_eq_zero_iff.mp hI) }
  exact Nat.card_unique

/-- `idealCount K 1 = 1` (only the unit ideal `⊤` has absolute norm `1`). -/
theorem idealCount_one : idealCount K 1 = 1 := by
  unfold idealCount
  let : Unique {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} :=
    { default := ⟨⊤, Ideal.absNorm_top⟩
      uniq := fun ⟨I, hI⟩ => Subtype.ext (Ideal.absNorm_eq_one_iff.mp hI) }
  exact Nat.card_unique

/-- For `n ≠ 0`, `idealCount K n` counts nonzero ideals of absolute norm `n`. -/
theorem idealCount_eq_card_nonzero {n : ℕ} (hn : n ≠ 0) :
    idealCount K n = Nat.card {I : {I : Ideal (𝓞 K) // I ≠ ⊥} // Ideal.absNorm I.1 = n} := by
  unfold idealCount
  refine Nat.card_congr ?_
  exact
    { toFun := fun ⟨I, hI⟩ => ⟨⟨I, mt Ideal.absNorm_eq_zero_iff.mpr (hI.symm ▸ hn)⟩, hI⟩
      invFun := fun ⟨⟨I, _⟩, hI⟩ => ⟨I, hI⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }

/-- Every height-one prime ideal `v` of `𝓞 K` is maximal. -/
theorem heightOne_isMaximal {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : v.asIdeal.IsMaximal :=
  v.isPrime.isMaximal v.ne_bot

/-- Every height-one prime ideal `v` of `𝓞 K` has `absNorm v.asIdeal = p ^ f` for a prime `p`
and `f > 0`, with `(p : 𝓞 K) ∈ v.asIdeal`. -/
theorem exists_prime_pow_absNorm_heightOne {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p f : ℕ, 0 < f ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ p.Prime ∧ Ideal.absNorm v.asIdeal = p ^ f := by
  have : v.asIdeal.IsMaximal := heightOne_isMaximal v
  exact Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal

/-- The least prime factor `(Ideal.absNorm v.asIdeal).minFac` of `N(v)` is prime. -/
theorem minFac_absNorm_prime {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : (Ideal.absNorm v.asIdeal).minFac.Prime :=
  Nat.minFac_prime (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm v))

/-- The least prime factor of `N(v)` is the unique rational prime dividing `N(v)`. -/
theorem eq_minFac_of_prime_dvd_absNorm {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) (hdvd : p ∣ Ideal.absNorm v.asIdeal) :
    p = (Ideal.absNorm v.asIdeal).minFac := by
  obtain ⟨q, f, _, _, hq, hnorm⟩ := exists_prime_pow_absNorm_heightOne v
  have hpq : p = q := by
    have h1 : p ∣ q := hp.dvd_of_dvd_pow (hnorm ▸ hdvd)
    exact ((hq.dvd_iff_eq hp.ne_one).mp h1).symm
  have hmf : (Ideal.absNorm v.asIdeal).minFac = q := by
    have hmf_p : (Ideal.absNorm v.asIdeal).minFac.Prime := minFac_absNorm_prime v
    have hmf_dvd : (Ideal.absNorm v.asIdeal).minFac ∣ q ^ f :=
      hnorm ▸ Nat.minFac_dvd (Ideal.absNorm v.asIdeal)
    have h1 : (Ideal.absNorm v.asIdeal).minFac ∣ q := hmf_p.dvd_of_dvd_pow hmf_dvd
    exact ((hq.dvd_iff_eq hmf_p.ne_one).mp h1).symm
  exact hpq.trans hmf.symm

/-- For a rational prime `p` and height-one prime `v : HeightOneSpectrum (𝓞 K)`,
`p ∣ Ideal.absNorm v.asIdeal` iff `v.asIdeal` lies over `(p) ⊂ ℤ`. -/
theorem dvd_absNorm_iff_liesOver {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) :
    p ∣ Ideal.absNorm v.asIdeal ↔ v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  · intro hdvd
    obtain ⟨q, f, _, hqmem, hq, hnorm⟩ := exists_prime_pow_absNorm_heightOne v
    have hpq : p = q := ((hq.dvd_iff_eq hp.ne_one).mp (hp.dvd_of_dvd_pow (hnorm ▸ hdvd))).symm
    subst hpq
    have hle : Ideal.span {(p : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      simpa using hqmem
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    have hcomap_ne : Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal ≠ ⊤ :=
      Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)
    have heq : Ideal.span {(p : ℤ)} = Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal :=
      hmax.eq_of_le hcomap_ne hle
    exact ⟨heq⟩
  · intro hlo
    have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := hlo
    have : v.asIdeal.IsPrime := v.isPrime
    have hnorm : Ideal.absNorm v.asIdeal = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal :=
      Ideal.absNorm_eq_pow_inertiaDeg' v.asIdeal hp
    have hfpos : 0 < (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal :=
      Ideal.inertiaDeg'_pos' (Ideal.span {(p : ℤ)}) v.asIdeal
    rw [hnorm]
    exact dvd_pow_self p hfpos.ne'

/-- Height-one prime ideals of `𝓞 K` lying above a rational prime `p`:
`{v : HeightOneSpectrum (𝓞 K) // p ∣ Ideal.absNorm v.asIdeal}`. -/
abbrev PrimesAbove (p : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // p ∣ Ideal.absNorm v.asIdeal}

/-- Canonical bijection between `PrimesAbove K p` and Mathlib's `(Ideal.span {(p : ℤ)}).primesOver (𝓞 K)`. -/
def primesAboveEquivPrimesOver {p : ℕ} (hp : p.Prime) :
    PrimesAbove K p ≃ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) where
  toFun v :=
    ⟨v.1.asIdeal, v.1.isPrime, (dvd_absNorm_iff_liesOver v.1 hp).mp v.2⟩
  invFun P :=
    have hne : P.1 ≠ ⊥ := by
      intro hbot
      have hlo : P.1.LiesOver (Ideal.span {(p : ℤ)}) := P.2.2
      have hp0 : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) P.1 := by
        change (p : ℤ) ∈ P.1.under ℤ
        rw [← hlo.over]
        exact Ideal.subset_span rfl
      rw [hbot, Ideal.mem_comap, Ideal.mem_bot,
        map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))] at hp0
      exact hp.ne_zero (Int.natCast_eq_zero.mp hp0)
    let v : HeightOneSpectrum (𝓞 K) := ⟨P.1, P.2.1, hne⟩
    ⟨v, (dvd_absNorm_iff_liesOver v hp).mpr P.2.2⟩
  left_inv v := by
    ext
    rfl
  right_inv P := by
    ext
    rfl

/-- There are finitely many prime ideals of `𝓞 K` above any rational prime `p`. -/
theorem finite_primesAbove {p : ℕ} (hp : p.Prime) : Finite (PrimesAbove K p) := by
  have : Fact p.Prime := ⟨hp⟩
  exact Finite.of_equiv _ (primesAboveEquivPrimesOver K hp).symm

/-- **Exact Prime-Ideal Splitting Identity (`∑_{v ∣ p} e_v f_v = [K : ℚ]`)** for every
number field `K` and every rational prime `p`. -/
theorem sum_ramification_inertia_primesAbove {p : ℕ} (hp : p.Prime)
    [Fintype (PrimesAbove K p)] :
    ∑ v : PrimesAbove K p, v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ =
      Module.finrank ℚ K := by
  have : Fact p.Prime := ⟨hp⟩
  have : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)
  classical
  let : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank K] at hsum
  rw [← hsum]
  exact Fintype.sum_equiv (primesAboveEquivPrimesOver K hp) _ _ fun _ => rfl

/-- **Exact Prime-Ideal Splitting Multiplicity Bound**: above every rational prime `p`,
there are at most `finrank ℚ K` prime ideals `v : HeightOneSpectrum (𝓞 K)` with
`p ∣ Ideal.absNorm v.asIdeal`. -/
theorem card_primesAbove_le_finrank {p : ℕ} (hp : p.Prime) :
    Nat.card (PrimesAbove K p) ≤ Module.finrank ℚ K := by
  have : Finite (PrimesAbove K p) := finite_primesAbove K hp
  classical
  let : Fintype (PrimesAbove K p) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← sum_ramification_inertia_primesAbove K hp]
  calc Fintype.card (PrimesAbove K p)
      = ∑ _v : PrimesAbove K p, 1 := by simp
    _ ≤ ∑ v : PrimesAbove K p, v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ := by
        refine Finset.sum_le_sum fun v _ => ?_
        have : v.1.asIdeal.IsPrime := v.1.isPrime
        exact Nat.mul_pos (Ideal.ramificationIdx_pos v.1.asIdeal ℤ)
          (Ideal.inertiaDeg_pos v.1.asIdeal ℤ)

/-- Helper: every normalized factor of an ideal `I` of `𝓞 K` is a nonzero prime ideal. -/
lemma mem_normalizedFactors_heightOne {K : Type*} [Field K] [NumberField K]
    {I P : Ideal (𝓞 K)} (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ := by
  have hirr : Irreducible P := UniqueFactorizationMonoid.irreducible_of_normalized_factor P hP
  have hpr : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  exact ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero⟩

/-- Helper: in `Ideal (𝓞 K)`, `normalizedFactors (I * J) = normalizedFactors I + normalizedFactors J`
for nonzero ideals `I, J`. -/
lemma normalizedFactors_mul_ideal {K : Type*} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    UniqueFactorizationMonoid.normalizedFactors (I * J) =
      UniqueFactorizationMonoid.normalizedFactors I +
        UniqueFactorizationMonoid.normalizedFactors J :=
  UniqueFactorizationMonoid.normalizedFactors_mul hI hJ

/-- Helper: for any nonzero ideal `I`, `Ideal.absNorm I` equals the product of `Ideal.absNorm P`
over `P ∈ normalizedFactors I`. -/
lemma absNorm_eq_prod_normalizedFactors {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Ideal.absNorm I = ((UniqueFactorizationMonoid.normalizedFactors I).map Ideal.absNorm).prod := by
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  exact map_multiset_prod Ideal.absNorm (UniqueFactorizationMonoid.normalizedFactors I)

/-- **Exact Prime-Power Ideal-Counting Bound**: for every number field `K`, every rational prime
`p`, and every `k : ℕ`, `idealCount K (p ^ k) ≤ (k + 1) ^ (Module.finrank ℚ K)`. -/
theorem idealCount_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    idealCount K (p ^ k) ≤ (k + 1) ^ (Module.finrank ℚ K) := by
  have : Finite (PrimesAbove K p) := finite_primesAbove K hp
  classical
  let : Fintype (PrimesAbove K p) := Fintype.ofFinite _
  let φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} → (PrimesAbove K p → Fin (k + 1)) :=
    fun I v =>
      let c := Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors I.1)
      have hc : c ≤ k := by
        have hI0 : I.1 ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (I.2.symm ▸ pow_ne_zero k hp.ne_zero)
        have hdvd_ideal : v.1.asIdeal ^ c ∣ I.1 := by
          have hsub : Multiset.replicate c v.1.asIdeal ≤ UniqueFactorizationMonoid.normalizedFactors I.1 :=
            Multiset.le_count_iff_replicate_le.mp le_rfl
          have hprod := Multiset.prod_dvd_prod_of_le hsub
          rwa [Multiset.prod_replicate, Ideal.prod_normalizedFactors_eq_self hI0] at hprod
        have hdvd_norm : (Ideal.absNorm v.1.asIdeal) ^ c ∣ p ^ k := by
          rw [← I.2, ← map_pow]
          exact map_dvd Ideal.absNorm hdvd_ideal
        have hp_dvd : p ^ c ∣ p ^ k := dvd_trans (pow_dvd_pow_of_dvd v.2 c) hdvd_norm
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hp_dvd
      ⟨c, Nat.lt_succ_of_le hc⟩
  have hφ_inj : Function.Injective φ := by
    intro I J hIJ
    have hI0 : I.1 ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (I.2.symm ▸ pow_ne_zero k hp.ne_zero)
    have hJ0 : J.1 ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (J.2.symm ▸ pow_ne_zero k hp.ne_zero)
    apply Subtype.ext
    rw [← Ideal.prod_normalizedFactors_eq_self hI0, ← Ideal.prod_normalizedFactors_eq_self hJ0]
    congr 1
    ext P
    by_cases hmem : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1 ∨
        P ∈ UniqueFactorizationMonoid.normalizedFactors J.1
    · have hP : P.IsPrime ∧ P ≠ ⊥ := by
        rcases hmem with h | h
        · exact mem_normalizedFactors_heightOne h
        · exact mem_normalizedFactors_heightOne h
      let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP.1, hP.2⟩
      have hv_dvd : p ∣ Ideal.absNorm v.asIdeal := by
        have hnorm_dvd : Ideal.absNorm P ∣ p ^ k := by
          rcases hmem with h | h
          · rw [← I.2]
            exact map_dvd Ideal.absNorm
              (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h)
          · rw [← J.2]
            exact map_dvd Ideal.absNorm
              (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h)
        have hmf_p : (Ideal.absNorm v.asIdeal).minFac.Prime := minFac_absNorm_prime v
        have hmf_dvd : (Ideal.absNorm v.asIdeal).minFac ∣ p :=
          hmf_p.dvd_of_dvd_pow (dvd_trans (Nat.minFac_dvd _) hnorm_dvd)
        have heq : (Ideal.absNorm v.asIdeal).minFac = p :=
          ((hp.dvd_iff_eq hmf_p.ne_one).mp hmf_dvd).symm
        rw [← heq]
        exact Nat.minFac_dvd _
      have hval := congrArg Fin.val (congrFun hIJ ⟨v, hv_dvd⟩)
      exact hval
    · push Not at hmem
      rw [Multiset.count_eq_zero.mpr hmem.1, Multiset.count_eq_zero.mpr hmem.2]
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (p ^ k)).to_subtype
  calc idealCount K (p ^ k)
      ≤ Nat.card (PrimesAbove K p → Fin (k + 1)) := Nat.card_le_card_of_injective φ hφ_inj
    _ = (k + 1) ^ Nat.card (PrimesAbove K p) := by
        rw [Nat.card_fun, Nat.card_fin]
    _ ≤ (k + 1) ^ Module.finrank ℚ K :=
        Nat.pow_le_pow_right (Nat.succ_pos k) (card_primesAbove_le_finrank K hp)

/-- **Exact Coprime Ideal-Factorization Equivalence**: for coprime positive integers `m, n`,
ideal multiplication `(I, J) ↦ I * J` is a bijection between pairs of ideals of norms `m, n`
and ideals of norm `m * n`. -/
def idealMulEquivOfCoprime {m n : ℕ} (hcop : m.Coprime n) (hm : m ≠ 0) (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} ≃
      {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n} where
  toFun p := ⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩
  invFun L :=
    have hL0 : L.1 ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (L.2.symm ▸ mul_ne_zero hm hn)
    let F := UniqueFactorizationMonoid.normalizedFactors L.1
    let F₁ := F.filter (fun P => Ideal.absNorm P ∣ m)
    let F₂ := F.filter (fun P => ¬ (Ideal.absNorm P ∣ m))
    have hF_split : F₁ + F₂ = F := Multiset.filter_add_not _ F
    have hprod_mul : F₁.prod * F₂.prod = L.1 := by
      rw [← Multiset.prod_add, hF_split, Ideal.prod_normalizedFactors_eq_self hL0]
    have hnorm_mul : Ideal.absNorm F₁.prod * Ideal.absNorm F₂.prod = m * n := by
      rw [← map_mul, hprod_mul, L.2]
    have hcop1 : (Ideal.absNorm F₁.prod).Coprime n := by
      rw [map_multiset_prod]
      refine Multiset.prod_induction (p := fun x : ℕ => x.Coprime n) _
        (fun a b ha hb => ha.mul_left hb) (Nat.coprime_one_left n) fun x hx => ?_
      rw [Multiset.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      exact Nat.Coprime.coprime_dvd_left (Multiset.mem_filter.mp hP).2 hcop
    have hcop2 : (Ideal.absNorm F₂.prod).Coprime m := by
      rw [map_multiset_prod]
      refine Multiset.prod_induction (p := fun x : ℕ => x.Coprime m) _
        (fun a b ha hb => ha.mul_left hb) (Nat.coprime_one_left m) fun x hx => ?_
      rw [Multiset.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      have ⟨hPF, hnotdvd⟩ := Multiset.mem_filter.mp hP
      have hP_ht := mem_normalizedFactors_heightOne hPF
      let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP_ht.1, hP_ht.2⟩
      obtain ⟨p, f, _, _, hp, hPnorm⟩ := exists_prime_pow_absNorm_heightOne v
      have hP_dvd_L : Ideal.absNorm P ∣ m * n := by
        rw [← L.2]
        exact map_dvd Ideal.absNorm (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hPF)
      have hp_not_dvd_m : ¬ p ∣ m := by
        intro hpm
        have hpn : ¬ p ∣ n := fun hpn => hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn)
        have hpcop_n : (p ^ f).Coprime n := (hp.coprime_iff_not_dvd.mpr hpn).pow_left f
        have hpf_dvd_m : p ^ f ∣ m := hpcop_n.dvd_of_dvd_mul_right (hPnorm ▸ hP_dvd_L)
        exact hnotdvd (hPnorm ▸ hpf_dvd_m)
      rw [show Ideal.absNorm P = p ^ f from hPnorm]
      exact (hp.coprime_iff_not_dvd.mpr hp_not_dvd_m).pow_left f
    have hnorm1 : Ideal.absNorm F₁.prod = m := by
      apply Nat.dvd_antisymm
      · exact hcop1.dvd_of_dvd_mul_right (hnorm_mul ▸ dvd_mul_right _ _)
      · exact hcop2.symm.dvd_of_dvd_mul_right (hnorm_mul.symm ▸ dvd_mul_right _ _)
    have hnorm2 : Ideal.absNorm F₂.prod = n := by
      rw [hnorm1] at hnorm_mul
      exact mul_left_cancel₀ hm hnorm_mul
    (⟨F₁.prod, hnorm1⟩, ⟨F₂.prod, hnorm2⟩)
  left_inv p := by
    obtain ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ := p
    have hI0 : I ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (hI.symm ▸ hm)
    have hJ0 : J ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (hJ.symm ▸ hn)
    have hFI_all : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, Ideal.absNorm P ∣ m := by
      intro P hP
      rw [← hI]
      exact map_dvd Ideal.absNorm (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
    have hFJ_none : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors J, ¬ (Ideal.absNorm P ∣ m) := by
      intro P hP hdvd_m
      have hP_ht := mem_normalizedFactors_heightOne hP
      let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP_ht.1, hP_ht.2⟩
      have hgt : 1 < Ideal.absNorm P := NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hdvd_n : Ideal.absNorm P ∣ n := by
        rw [← hJ]
        exact map_dvd Ideal.absNorm (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
      have hdvd_one : Ideal.absNorm P ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd hdvd_m hdvd_n
      exact hgt.ne' (Nat.dvd_one.mp hdvd_one)
    apply Prod.ext <;> apply Subtype.ext <;> dsimp only
    · rw [normalizedFactors_mul_ideal hI0 hJ0, Multiset.filter_add,
        Multiset.filter_eq_self.mpr hFI_all,
        Multiset.filter_eq_nil.mpr hFJ_none, add_zero,
        Ideal.prod_normalizedFactors_eq_self hI0]
    · rw [normalizedFactors_mul_ideal hI0 hJ0, Multiset.filter_add,
        Multiset.filter_eq_nil.mpr (fun P hP => not_not.mpr (hFI_all P hP)),
        Multiset.filter_eq_self.mpr hFJ_none, zero_add,
        Ideal.prod_normalizedFactors_eq_self hJ0]
  right_inv L := by
    have hL0 : L.1 ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (L.2.symm ▸ mul_ne_zero hm hn)
    apply Subtype.ext
    dsimp only
    rw [← Multiset.prod_add, Multiset.filter_add_not, Ideal.prod_normalizedFactors_eq_self hL0]

/-- **Exact Multiplicativity of `idealCount K`**: for every pair of coprime naturals `m, n`,
`idealCount K (m * n) = idealCount K m * idealCount K n`. -/
theorem idealCount_mul_of_coprime {m n : ℕ} (hcop : m.Coprime n) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by
  by_cases hm : m = 0
  · subst hm
    have hn : n = 1 := (Nat.coprime_zero_left n).mp hcop
    subst hn
    simp [idealCount_zero, idealCount_one]
  · by_cases hn : n = 0
    · subst hn
      have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hcop
      subst hm1
      simp [idealCount_zero, idealCount_one]
    · unfold idealCount
      rw [← Nat.card_prod]
      exact Nat.card_congr (idealMulEquivOfCoprime K hcop hm hn).symm

end IdealCounting

/-! ## Section 2: Unconditional Absolute Convergence, `(ζ(σ))^d` Bound, Exact Euler Product & Nonvanishing -/

section EulerProductAndConvergence

variable (K : Type*) [Field K] [NumberField K]

/-- Ideals of `𝓞 K` whose absolute norm is a power of `p`. -/
abbrev PrimePowIdeals (p : ℕ) : Type _ :=
  {I : Ideal (𝓞 K) // ∃ k : ℕ, Ideal.absNorm I = p ^ k}

/-- Helper: `normalizedFactors (v.asIdeal ^ e) = Multiset.replicate e v.asIdeal`. -/
lemma normalizedFactors_heightOne_pow {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    UniqueFactorizationMonoid.normalizedFactors (v.asIdeal ^ e) =
      Multiset.replicate e v.asIdeal := by
  induction e with
  | zero =>
    rw [pow_zero, UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  | succ e ih =>
    rw [pow_succ', normalizedFactors_mul_ideal v.ne_bot (pow_ne_zero e v.ne_bot), ih]
    have hirr : Irreducible v.asIdeal :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mpr (Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    have hnorm : UniqueFactorizationMonoid.normalizedFactors v.asIdeal = {v.asIdeal} := by
      have h1 := UniqueFactorizationMonoid.normalizedFactors_irreducible hirr
      simpa [normalize_eq] using h1
    rw [hnorm, Multiset.replicate_succ, Multiset.singleton_add]

/-- Helper: `normalizedFactors (∏ i ∈ s, (v i).asIdeal ^ a i) = ∑ i ∈ s, Multiset.replicate (a i) (v i).asIdeal`. -/
lemma normalizedFactors_finset_prod_heightOne_pow {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → HeightOneSpectrum (𝓞 K)) (a : ι → ℕ) :
    UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ s, (v i).asIdeal ^ a i) =
      ∑ i ∈ s, Multiset.replicate (a i) (v i).asIdeal := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, UniqueFactorizationMonoid.normalizedFactors_one]
  | insert x s hx ih =>
    have hprod_ne : (∏ i ∈ s, (v i).asIdeal ^ a i) ≠ ⊥ := by
      intro hbot
      have h0 : Ideal.absNorm (∏ i ∈ s, (v i).asIdeal ^ a i) = 0 := by
        rw [hbot, Ideal.absNorm_bot]
      rw [map_prod] at h0
      have hne : (∏ i ∈ s, Ideal.absNorm ((v i).asIdeal ^ a i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by
          rw [map_pow]
          exact pow_ne_zero _ (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm (v i))).ne'
      exact hne h0
    rw [Finset.prod_insert hx, Finset.sum_insert hx,
      normalizedFactors_mul_ideal (pow_ne_zero _ (v x).ne_bot) hprod_ne,
      normalizedFactors_heightOne_pow, ih]

/-- **Local Prime-Power Ideal Bijection**: for a rational prime `p`, every ideal `I` of `𝓞 K`
whose absolute norm is a power of `p` factors uniquely as `∏_{v ∣ p} v^{a(v)}` for a tuple
`a : PrimesAbove K p → ℕ`. -/
def primePowIdealsEquivFun {p : ℕ} (hp : p.Prime) [Fintype (PrimesAbove K p)] :
    (PrimesAbove K p → ℕ) ≃ PrimePowIdeals K p where
  toFun a :=
    ⟨∏ v : PrimesAbove K p, v.1.asIdeal ^ a v, by
      classical
      have hnorm : Ideal.absNorm (∏ v : PrimesAbove K p, v.1.asIdeal ^ a v) =
          ∏ v : PrimesAbove K p, (Ideal.absNorm v.1.asIdeal) ^ a v := by
        rw [map_prod]
        refine Finset.prod_congr rfl fun v _ => map_pow Ideal.absNorm _ _
      rw [hnorm]
      have hpow : ∀ v : PrimesAbove K p,
          ∃ f : ℕ, Ideal.absNorm v.1.asIdeal = p ^ f := by
        intro v
        have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
          (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
        exact ⟨(Ideal.span {(p : ℤ)}).inertiaDeg' v.1.asIdeal,
          Ideal.absNorm_eq_pow_inertiaDeg' v.1.asIdeal hp⟩
      choose f hf using hpow
      refine ⟨∑ v : PrimesAbove K p, f v * a v, ?_⟩
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hf v, ← pow_mul]⟩
  invFun I v := Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors I.1)
  left_inv a := by
    classical
    funext v
    dsimp only
    rw [normalizedFactors_finset_prod_heightOne_pow Finset.univ (fun w : PrimesAbove K p => w.1) a]
    rw [Multiset.count_sum']
    rw [Finset.sum_eq_single v]
    · simp
    · intro w _ hwv
      have hne : w.1.asIdeal ≠ v.1.asIdeal := fun h => hwv (Subtype.ext (HeightOneSpectrum.ext h))
      exact Multiset.count_eq_zero.mpr fun hmem => hne (Multiset.eq_of_mem_replicate hmem).symm
    · intro h
      exact absurd (Finset.mem_univ v) h
  right_inv I := by
    classical
    obtain ⟨k, hk⟩ := I.2
    have hI0 : I.1 ≠ ⊥ := mt Ideal.absNorm_eq_zero_iff.mpr (hk.symm ▸ pow_ne_zero k hp.ne_zero)
    apply Subtype.ext
    dsimp only
    have hsupp : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I.1,
        ∃ v : PrimesAbove K p, v.1.asIdeal = P := by
      intro P hP
      have hP_ht := mem_normalizedFactors_heightOne hP
      let v : HeightOneSpectrum (𝓞 K) := ⟨P, hP_ht.1, hP_ht.2⟩
      have hnorm_dvd : Ideal.absNorm P ∣ p ^ k := by
        rw [← hk]
        exact map_dvd Ideal.absNorm (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
      have hmf_p : (Ideal.absNorm v.asIdeal).minFac.Prime := minFac_absNorm_prime v
      have hmf_dvd : (Ideal.absNorm v.asIdeal).minFac ∣ p :=
        hmf_p.dvd_of_dvd_pow (dvd_trans (Nat.minFac_dvd _) hnorm_dvd)
      have heq : (Ideal.absNorm v.asIdeal).minFac = p :=
        ((hp.dvd_iff_eq hmf_p.ne_one).mp hmf_dvd).symm
      exact ⟨⟨v, heq ▸ Nat.minFac_dvd _⟩, rfl⟩
    have hms : (UniqueFactorizationMonoid.normalizedFactors I.1) =
        ∑ v : PrimesAbove K p,
          Multiset.replicate
            (Multiset.count v.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors I.1))
            v.1.asIdeal := by
      ext P
      rw [Multiset.count_sum']
      by_cases hmem : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1
      · obtain ⟨v, hv⟩ := hsupp P hmem
        rw [Finset.sum_eq_single v]
        · rw [hv, Multiset.count_replicate_self]
        · intro w _ hwv
          have hne : w.1.asIdeal ≠ P := fun h =>
            hwv (Subtype.ext (HeightOneSpectrum.ext (h.trans hv.symm)))
          exact Multiset.count_eq_zero.mpr fun hm => hne (Multiset.eq_of_mem_replicate hm).symm
        · intro h
          exact absurd (Finset.mem_univ v) h
      · rw [Multiset.count_eq_zero.mpr hmem]
        symm
        refine Finset.sum_eq_zero fun w _ => ?_
        by_cases hweq : w.1.asIdeal = P
        · rw [hweq, Multiset.count_eq_zero.mpr hmem, Multiset.replicate_zero, Multiset.count_zero]
        · exact Multiset.count_eq_zero.mpr fun hm => hweq (Multiset.eq_of_mem_replicate hm).symm
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0, hms]
    rw [Multiset.prod_sum]
    refine Finset.prod_congr rfl fun v _ => (Multiset.prod_replicate _ _).symm

/-- Helper: `(∏ i ∈ s, (f i : ℂ)) ^ z = ∏ i ∈ s, (f i : ℂ) ^ z` for nonnegative reals `f i`. -/
lemma finset_prod_ofReal_cpow {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (z : ℂ) :
    (∏ i ∈ s, (f i : ℂ)) ^ z = ∏ i ∈ s, (f i : ℂ) ^ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hxt ih =>
    have hx : 0 ≤ f x := hf x (Finset.mem_insert_self x t)
    have ht : ∀ i ∈ t, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ht_prod : 0 ≤ ∏ i ∈ t, f i := Finset.prod_nonneg ht
    rw [Finset.prod_insert hxt, Finset.prod_insert hxt, ← ih ht, ← Complex.ofReal_prod]
    exact Complex.mul_cpow_ofReal_nonneg hx ht_prod z

/-- General finite-product geometric series identity over a complete normed field `𝕜`:
if `∀ i : ι, ‖f i‖ < 1` for a finite type `ι`, then `∏ i, (f i) ^ (a i)` is absolutely summable
over `a : ι → ℕ` with exact sum `∏ i, (1 - f i)⁻¹`. -/
lemma summable_norm_and_hasSum_finset_geom {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → 𝕜} (hf : ∀ i ∈ s, ‖f i‖ < 1) :
    (Summable fun a : {a : ι → ℕ // ∀ i ∉ s, a i = 0} => ‖∏ i ∈ s, f i ^ a.1 i‖) ∧
      HasSum (fun a : {a : ι → ℕ // ∀ i ∉ s, a i = 0} => ∏ i ∈ s, f i ^ a.1 i)
        (∏ i ∈ s, (1 - f i)⁻¹) := by
  induction s using Finset.induction_on with
  | empty =>
    let : Unique {a : ι → ℕ // ∀ i ∉ (∅ : Finset ι), a i = 0} :=
      { default := ⟨fun _ => 0, fun _ _ => rfl⟩
        uniq := fun ⟨a, ha⟩ => Subtype.ext (funext fun i => ha i (Finset.notMem_empty i)) }
    refine ⟨Summable.of_finite, ?_⟩
    have h1 := hasSum_fintype (fun _ : {a : ι → ℕ // ∀ i ∉ (∅ : Finset ι), a i = 0} => (1 : 𝕜))
    simp only [Finset.prod_empty, Finset.sum_const, Finset.card_univ, Fintype.card_unique,
      one_smul] at h1 ⊢
    exact h1
  | insert x s hx ih =>
    have hfx : ‖f x‖ < 1 := hf x (Finset.mem_insert_self x s)
    have hfs : ∀ i ∈ s, ‖f i‖ < 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    obtain ⟨hs_norm, hs_sum⟩ := ih hfs
    let e : {a : ι → ℕ // ∀ i ∉ insert x s, a i = 0} ≃
        ℕ × {b : ι → ℕ // ∀ i ∉ s, b i = 0} :=
      { toFun := fun a =>
          (a.1 x, ⟨Function.update a.1 x 0, fun i hi => by
            by_cases hix : i = x
            · simp [hix]
            · simp [Function.update_of_ne hix, a.2 i (by simp [hix, hi])]⟩)
        invFun := fun p =>
          ⟨Function.update p.2.1 x p.1, fun i hi => by
            have hix : i ≠ x := fun h => hi (h ▸ Finset.mem_insert_self x s)
            have his : i ∉ s := fun h => hi (Finset.mem_insert_of_mem h)
            simp [Function.update_of_ne hix, p.2.2 i his]⟩
        left_inv := fun a => by
          apply Subtype.ext
          funext i
          by_cases hix : i = x
          · simp [hix]
          · simp [Function.update_of_ne hix]
        right_inv := fun p => by
          apply Prod.ext
          · simp
          · apply Subtype.ext
            funext i
            by_cases hix : i = x
            · simp [hix, p.2.2 x hx]
            · simp [Function.update_of_ne hix] }
    have hprod_eq : ∀ a : {a : ι → ℕ // ∀ i ∉ insert x s, a i = 0},
        ∏ i ∈ insert x s, f i ^ a.1 i =
          f x ^ (e a).1 * ∏ i ∈ s, f i ^ (e a).2.1 i := by
      intro a
      rw [Finset.prod_insert hx]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hix : i ≠ x := fun h => hx (h ▸ hi)
      simp [e, Function.update_of_ne hix]
    have hx_norm : Summable (fun n : ℕ => ‖f x ^ n‖) := by
      simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hfx
    have hx_sum : HasSum (fun n : ℕ => f x ^ n) (1 - f x)⁻¹ :=
      hasSum_geometric_of_norm_lt_one hfx
    have hprod_norm : Summable (fun p : ℕ × {b : ι → ℕ // ∀ i ∉ s, b i = 0} =>
        ‖f x ^ p.1‖ * ‖∏ i ∈ s, f i ^ p.2.1 i‖) :=
      hx_norm.mul_of_nonneg hs_norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    have hprod_summable : Summable (fun p : ℕ × {b : ι → ℕ // ∀ i ∉ s, b i = 0} =>
        f x ^ p.1 * ∏ i ∈ s, f i ^ p.2.1 i) :=
      (hprod_norm.congr fun p => (norm_mul _ _).symm).of_norm
    have hprod_sum : HasSum (fun p : ℕ × {b : ι → ℕ // ∀ i ∉ s, b i = 0} =>
        f x ^ p.1 * ∏ i ∈ s, f i ^ p.2.1 i)
        ((1 - f x)⁻¹ * ∏ i ∈ s, (1 - f i)⁻¹) :=
      hx_sum.mul hs_sum hprod_summable
    constructor
    · have hnorm_eq : (fun a : {a : ι → ℕ // ∀ i ∉ insert x s, a i = 0} =>
          ‖∏ i ∈ insert x s, f i ^ a.1 i‖) =
          (fun p : ℕ × {b : ι → ℕ // ∀ i ∉ s, b i = 0} =>
            ‖f x ^ p.1‖ * ‖∏ i ∈ s, f i ^ p.2.1 i‖) ∘ e := by
        funext a
        rw [Function.comp_apply, hprod_eq a, norm_mul]
      rw [hnorm_eq]
      exact hprod_norm.comp_injective e.injective
    · rw [Finset.prod_insert hx]
      have hfun_eq : (fun a : {a : ι → ℕ // ∀ i ∉ insert x s, a i = 0} =>
          ∏ i ∈ insert x s, f i ^ a.1 i) =
          (fun p : ℕ × {b : ι → ℕ // ∀ i ∉ s, b i = 0} =>
            f x ^ p.1 * ∏ i ∈ s, f i ^ p.2.1 i) ∘ e := by
        funext a
        exact hprod_eq a
      rw [hfun_eq]
      exact (e.hasSum_iff).mpr hprod_sum

lemma ofReal_pow_cpow {r : ℝ} (hr : 0 ≤ r) (n : ℕ) (z : ℂ) :
    ((r : ℂ) ^ n) ^ z = ((r : ℂ) ^ z) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← Complex.ofReal_pow,
      Complex.mul_cpow_ofReal_nonneg (pow_nonneg hr k) hr, Complex.ofReal_pow, ih]

lemma summable_norm_and_hasSum_fintype_geom {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    {ι : Type*} [Fintype ι] {f : ι → 𝕜} (hf : ∀ i : ι, ‖f i‖ < 1) :
    (Summable fun a : ι → ℕ => ‖∏ i : ι, f i ^ a i‖) ∧
      HasSum (fun a : ι → ℕ => ∏ i : ι, f i ^ a i) (∏ i : ι, (1 - f i)⁻¹) := by
  classical
  obtain ⟨hnorm, hsum⟩ := summable_norm_and_hasSum_finset_geom Finset.univ (fun i _ => hf i)
  let e : (ι → ℕ) ≃ {a : ι → ℕ // ∀ i ∉ (Finset.univ : Finset ι), a i = 0} :=
    { toFun := fun a => ⟨a, fun i hi => absurd (Finset.mem_univ i) hi⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : Summable ((fun a : {a : ι → ℕ // ∀ i ∉ (Finset.univ : Finset ι), a i = 0} =>
      ‖∏ i ∈ Finset.univ, f i ^ a.1 i‖) ∘ e) := hnorm.comp_injective e.injective
  have h2 : HasSum ((fun a : {a : ι → ℕ // ∀ i ∉ (Finset.univ : Finset ι), a i = 0} =>
      ∏ i ∈ Finset.univ, f i ^ a.1 i) ∘ e) (∏ i ∈ Finset.univ, (1 - f i)⁻¹) :=
    (e.hasSum_iff).mpr hsum
  exact ⟨h1, h2⟩

/-- Local prime-power Euler factor identity (complex version, `0 < s.re`):
`∑'_{k : ℕ} idealCount K (p ^ k) * (p ^ k)^(-s) = ∏_{v ∣ p} (1 - N(v)^(-s))⁻¹`. -/
theorem hasSum_idealCount_prime_pow_cpow {p : ℕ} (hp : p.Prime)
    [Fintype (PrimesAbove K p)] {s : ℂ} (hs : 0 < s.re) :
    HasSum (fun k : ℕ => (idealCount K (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-s))
      (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) := by
  classical
  have hlt : ∀ v : PrimesAbove K p, ‖(Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    intro v
    have hgt : 1 < Ideal.absNorm v.1.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_one.trans hgt), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hgt) (neg_lt_zero.mpr hs)
  obtain ⟨_, hgeom⟩ := summable_norm_and_hasSum_fintype_geom hlt
  have hpow_eq : ∀ a : PrimesAbove K p → ℕ,
      (Ideal.absNorm ((primePowIdealsEquivFun K hp a).1) : ℂ) ^ (-s) =
        ∏ v : PrimesAbove K p, ((Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) ^ a v := by
    intro a
    change (Ideal.absNorm (∏ v : PrimesAbove K p, v.1.asIdeal ^ a v) : ℂ) ^ (-s) = _
    rw [map_prod, Nat.cast_prod]
    have hcpow_prod :
        (∏ v : PrimesAbove K p, (Ideal.absNorm (v.1.asIdeal ^ a v) : ℂ)) ^ (-s) =
          ∏ v : PrimesAbove K p, (Ideal.absNorm (v.1.asIdeal ^ a v) : ℂ) ^ (-s) := by
      simpa only [Complex.ofReal_natCast] using
        finset_prod_ofReal_cpow (Finset.univ : Finset (PrimesAbove K p))
          (f := fun v => (Ideal.absNorm (v.1.asIdeal ^ a v) : ℝ))
          (fun v _ => Nat.cast_nonneg _) (-s)
    rw [hcpow_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, Nat.cast_pow, ← Complex.ofReal_natCast]
    exact ofReal_pow_cpow (Nat.cast_nonneg _) (a v) (-s)
  have hI_sum : HasSum (fun I : PrimePowIdeals K p => (Ideal.absNorm I.1 : ℂ) ^ (-s))
      (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) := by
    have hcomp : HasSum (fun a : PrimesAbove K p → ℕ =>
        (Ideal.absNorm ((primePowIdealsEquivFun K hp a).1) : ℂ) ^ (-s))
        (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) := by
      simpa only [hpow_eq] using hgeom
    exact (Equiv.hasSum_iff (primePowIdealsEquivFun K hp)).mp hcomp
  let eSig : (Σ k : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}) ≃ PrimePowIdeals K p :=
    { toFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
      invFun := fun I => ⟨I.2.choose, ⟨I.1, I.2.choose_spec⟩⟩
      left_inv := fun ⟨k, ⟨I, hI⟩⟩ => by
        dsimp only
        have hk : (⟨k, hI⟩ : ∃ m, Ideal.absNorm I = p ^ m).choose = k :=
          Nat.pow_right_injective hp.two_le
            ((⟨k, hI⟩ : ∃ m, Ideal.absNorm I = p ^ m).choose_spec.symm.trans hI)
        have hmk : ∀ (k₁ k₂ : ℕ) (h1 : Ideal.absNorm I = p ^ k₁) (h2 : Ideal.absNorm I = p ^ k₂),
            k₁ = k₂ → (⟨k₁, ⟨I, h1⟩⟩ : Σ m : ℕ, {J : Ideal (𝓞 K) // Ideal.absNorm J = p ^ m}) =
              ⟨k₂, ⟨I, h2⟩⟩ := by
          rintro _ _ _ _ rfl; rfl
        exact hmk _ _ _ _ hk
      right_inv := fun ⟨_, _⟩ => rfl }
  have hsig_sum : HasSum (fun x : Σ k : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} =>
      (Ideal.absNorm x.2.1 : ℂ) ^ (-s))
      (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (eSig.hasSum_iff).mpr hI_sum
  refine hsig_sum.sigma fun k => ?_
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} :=
    (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) (p ^ k)).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := Fintype.ofFinite _
  have hfin : ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}, (Ideal.absNorm I.1 : ℂ) ^ (-s) =
      (idealCount K (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-s) := by
    calc ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}, (Ideal.absNorm I.1 : ℂ) ^ (-s)
        = ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}, ((p ^ k : ℕ) : ℂ) ^ (-s) :=
            Finset.sum_congr rfl fun I _ => by rw [I.2]
      _ = (Fintype.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} : ℂ) *
            ((p ^ k : ℕ) : ℂ) ^ (-s) := by simp
      _ = (idealCount K (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-s) := by
            rw [idealCount, Nat.card_eq_fintype_card]
  rw [← hfin]
  exact hasSum_fintype _

/-- Local prime-power Euler factor identity (real version, `0 < σ`):
`∑'_{k : ℕ} idealCount K (p ^ k) * (p ^ k)^(-σ) = ∏_{v ∣ p} (1 - N(v)^(-σ))⁻¹`. -/
theorem hasSum_idealCount_prime_pow_rpow {p : ℕ} (hp : p.Prime)
    [Fintype (PrimesAbove K p)] {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun k : ℕ => (idealCount K (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-σ))
      (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹) := by
  have hc := hasSum_idealCount_prime_pow_cpow K hp (s := (σ : ℂ)) (by simpa using hσ)
  have hre := Complex.reCLM.hasSum hc
  have hterm : ∀ k : ℕ,
      Complex.reCLM ((idealCount K (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-(σ : ℂ))) =
        (idealCount K (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-σ) := by
    intro k
    change ((idealCount K (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-(σ : ℂ))).re = _
    have h2 : (idealCount K (p ^ k) : ℂ) * ((p ^ k : ℕ) : ℂ) ^ (-(σ : ℂ)) =
        (((idealCount K (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, Complex.ofReal_natCast,
        Complex.ofReal_cpow (Nat.cast_nonneg (p ^ k)) (-σ),
        Complex.ofReal_natCast, Complex.ofReal_neg]
    rw [h2, Complex.ofReal_re]
  have hprod :
      Complex.reCLM (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(σ : ℂ)))⁻¹) =
        ∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹ := by
    have heq :
        (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(σ : ℂ)))⁻¹) =
          (((∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹) : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_cpow (Nat.cast_nonneg (Ideal.absNorm v.1.asIdeal)) (-σ),
        Complex.ofReal_natCast, Complex.ofReal_neg]
    change (∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(σ : ℂ)))⁻¹).re = _
    rw [heq, Complex.ofReal_re]
  simpa only [Function.comp_def, hterm, hprod] using hre

/-- Local real Euler-factor domination at a prime `p`:
`∏_{v ∣ p} (1 - N(v)^(-σ))⁻¹ ≤ ((1 - p^(-σ))⁻¹)^[K : ℚ]` for every `σ > 0`. -/
theorem prod_local_eulerFactor_real_le {p : ℕ} (hp : p.Prime)
    [Fintype (PrimesAbove K p)] {σ : ℝ} (hσ : 0 < σ) :
    ∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹ ≤
      ((1 - (p : ℝ) ^ (-σ))⁻¹) ^ Module.finrank ℚ K := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hp_rpow_lt : (p : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr hσ)
  have h1p_pos : 0 < 1 - (p : ℝ) ^ (-σ) := sub_pos.mpr hp_rpow_lt
  have hfac_ge_one : 1 ≤ (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    rw [one_le_inv₀ h1p_pos]
    linarith [Real.rpow_pos_of_pos (zero_lt_one.trans hp1) (-σ)]
  have hterm : ∀ v : PrimesAbove K p,
      (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹ ≤ (1 - (p : ℝ) ^ (-σ))⁻¹ := by
    intro v
    have hle : (p : ℝ) ≤ (Ideal.absNorm v.1.asIdeal : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v.1)) v.2
    have hrpow_le : (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hp1) hle (neg_nonpos.mpr hσ.le)
    exact inv_anti₀ h1p_pos (sub_le_sub_left hrpow_le 1)
  have hterm_nn : ∀ v : PrimesAbove K p,
      0 ≤ (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹ := by
    intro v
    have hgt : (1 : ℝ) < (Ideal.absNorm v.1.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    exact inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_lt_one_of_one_lt_of_neg hgt (neg_lt_zero.mpr hσ)).le)
  calc ∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹
      ≤ ∏ _v : PrimesAbove K p, (1 - (p : ℝ) ^ (-σ))⁻¹ :=
        Finset.prod_le_prod (fun v _ => hterm_nn v) (fun v _ => hterm v)
    _ = ((1 - (p : ℝ) ^ (-σ))⁻¹) ^ Fintype.card (PrimesAbove K p) := by simp
    _ ≤ ((1 - (p : ℝ) ^ (-σ))⁻¹) ^ Module.finrank ℚ K := by
        refine pow_le_pow_right₀ hfac_ge_one ?_
        rw [← Nat.card_eq_fintype_card]
        exact card_primesAbove_le_finrank K hp

/-- Real Dirichlet-series coefficient function `n ↦ idealCount K n * n^(-σ)` (with `0 ↦ 0`). -/
def realDirichletTerm (σ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (idealCount K n : ℝ) * (n : ℝ) ^ (-σ)

lemma realDirichletTerm_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ realDirichletTerm K σ n := by
  unfold realDirichletTerm
  split_ifs
  · exact le_rfl
  · positivity

lemma realDirichletTerm_zero (σ : ℝ) : realDirichletTerm K σ 0 = 0 := by
  simp [realDirichletTerm]

lemma realDirichletTerm_one (σ : ℝ) : realDirichletTerm K σ 1 = 1 := by
  simp [realDirichletTerm, idealCount_one]

lemma realDirichletTerm_mul_of_coprime (σ : ℝ) {m n : ℕ} (hcop : m.Coprime n) :
    realDirichletTerm K σ (m * n) = realDirichletTerm K σ m * realDirichletTerm K σ n := by
  by_cases hm : m = 0
  · simp [hm, realDirichletTerm_zero]
  · by_cases hn : n = 0
    · simp [hn, realDirichletTerm_zero]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      simp only [realDirichletTerm, if_neg hm, if_neg hn, if_neg hmn,
        idealCount_mul_of_coprime K hcop, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
      ring

/-- Real Riemann zeta series value equals `(riemannZeta (σ : ℂ)).re` for `1 < σ`. -/
theorem tsum_nat_rpow_eq_riemannZeta_re {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) = (riemannZeta (σ : ℂ)).re := by
  have hcs : 1 < (σ : ℂ).re := by simpa using hσ
  rw [zeta_eq_tsum_one_div_nat_cpow hcs]
  have hterm : ∀ n : ℕ, (1 : ℂ) / (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      have hσ0 : σ ≠ 0 := by linarith
      have hσC : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ0
      rw [Nat.cast_zero, Nat.cast_zero, Complex.zero_cpow hσC, div_zero,
        Real.zero_rpow (neg_ne_zero.mpr hσ0), Complex.ofReal_zero]
    · rw [one_div, ← Complex.cpow_neg, Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ),
        Complex.ofReal_natCast, Complex.ofReal_neg]
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]

/-- **Unconditional Absolute Convergence & `(riemannZeta σ)^d` Bound (Dirichlet-Series Form)**
for every number field `K` and every `σ > 1`. -/
theorem summable_and_tsum_realDirichletTerm_le {σ : ℝ} (hσ : 1 < σ) :
    Summable (realDirichletTerm K σ) ∧
      (∑' n : ℕ, realDirichletTerm K σ n) ≤ ((riemannZeta (σ : ℂ)).re) ^ Module.finrank ℚ K := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hprime_sum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖realDirichletTerm K σ (p ^ k)‖) := by
    intro p hp
    have : Finite (PrimesAbove K p) := finite_primesAbove K hp
    classical
    let : Fintype (PrimesAbove K p) := Fintype.ofFinite _
    have hsum := (hasSum_idealCount_prime_pow_rpow K hp hσ0).summable
    refine hsum.congr fun k => ?_
    rw [Real.norm_of_nonneg (realDirichletTerm_nonneg K σ (p ^ k))]
    simp [realDirichletTerm, hp.ne_zero]
  have hzeta_summable : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    refine (Real.summable_nat_rpow_inv.mpr hσ).congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  let fR : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ) ^ (-σ)
      map_one' := by simp
      map_mul' := fun m n => by
        rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hfR_sum : Summable fR := hzeta_summable
  have hsmooth_le : ∀ N : ℕ,
      (∑' m : N.smoothNumbers, realDirichletTerm K σ m.1) ≤
        ((riemannZeta (σ : ℂ)).re) ^ Module.finrank ℚ K := by
    intro N
    have hN := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (realDirichletTerm_one K σ) (fun hcop => realDirichletTerm_mul_of_coprime K σ hcop)
      (fun hp => hprime_sum hp) N
    rw [hN.2.tsum_eq]
    have hprod_le :
        (∏ p ∈ N.primesBelow, ∑' k : ℕ, realDirichletTerm K σ (p ^ k)) ≤
          ∏ p ∈ N.primesBelow, ((1 - (p : ℝ) ^ (-σ))⁻¹) ^ Module.finrank ℚ K := by
      refine Finset.prod_le_prod (fun p _ => tsum_nonneg fun k => realDirichletTerm_nonneg K σ (p ^ k)) ?_
      intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primesBelow hp_mem
      have : Finite (PrimesAbove K p) := finite_primesAbove K hp
      classical
      let : Fintype (PrimesAbove K p) := Fintype.ofFinite _
      have htsum_eq : (∑' k : ℕ, realDirichletTerm K σ (p ^ k)) =
          ∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ))⁻¹ := by
        have hhs := hasSum_idealCount_prime_pow_rpow K hp hσ0
        rw [← hhs.tsum_eq]
        refine tsum_congr fun k => ?_
        simp [realDirichletTerm, hp.ne_zero]
      rw [htsum_eq]
      exact prod_local_eulerFactor_real_le K hp hσ0
    have hzeta_smooth_eq :
        ∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹ =
          ∑' m : N.smoothNumbers, (m.1 : ℝ) ^ (-σ) :=
      EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hfR_sum N
    have hzeta_smooth_le :
        (∑' m : N.smoothNumbers, (m.1 : ℝ) ^ (-σ)) ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := by
      rw [tsum_subtype N.smoothNumbers (fun n : ℕ => (n : ℝ) ^ (-σ))]
      refine Summable.tsum_le_tsum (fun n => ?_)
        (hzeta_summable.indicator N.smoothNumbers) hzeta_summable
      by_cases hn : n ∈ N.smoothNumbers
      · simp [Set.indicator, hn]
      · simp [Set.indicator, hn, Real.rpow_nonneg (Nat.cast_nonneg n)]
    have hzeta_smooth_nn : 0 ≤ ∑' m : N.smoothNumbers, (m.1 : ℝ) ^ (-σ) :=
      tsum_nonneg fun m => Real.rpow_nonneg (Nat.cast_nonneg m.1) _
    calc ∏ p ∈ N.primesBelow, ∑' k : ℕ, realDirichletTerm K σ (p ^ k)
        ≤ ∏ p ∈ N.primesBelow, ((1 - (p : ℝ) ^ (-σ))⁻¹) ^ Module.finrank ℚ K := hprod_le
      _ = (∏ p ∈ N.primesBelow, (1 - (p : ℝ) ^ (-σ))⁻¹) ^ Module.finrank ℚ K :=
          Finset.prod_pow _ _ _
      _ = (∑' m : N.smoothNumbers, (m.1 : ℝ) ^ (-σ)) ^ Module.finrank ℚ K := by
          rw [hzeta_smooth_eq]
      _ ≤ (∑' n : ℕ, (n : ℝ) ^ (-σ)) ^ Module.finrank ℚ K :=
          pow_le_pow_left₀ hzeta_smooth_nn hzeta_smooth_le _
      _ = ((riemannZeta (σ : ℂ)).re) ^ Module.finrank ℚ K := by
          rw [tsum_nat_rpow_eq_riemannZeta_re hσ]
  have hfin_le : ∀ s : Finset ℕ,
      (∑ n ∈ s, realDirichletTerm K σ n) ≤ ((riemannZeta (σ : ℂ)).re) ^ Module.finrank ℚ K := by
    intro s
    let N := s.sup id + 1
    let sPos := s.filter (fun n => n ≠ 0)
    have hsub : ∀ n ∈ sPos, n ∈ N.smoothNumbers := by
      intro n hn
      have ⟨hns, hn0⟩ := Finset.mem_filter.mp hn
      rw [Nat.mem_smoothNumbers]
      refine ⟨hn0, fun q hq => ?_⟩
      have hq_le : q ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactorsList hq)
      have hn_le : n ≤ s.sup id := Finset.le_sup (f := id) hns
      exact Nat.lt_succ_of_le (hq_le.trans hn_le)
    have hN_sum : Summable (fun m : N.smoothNumbers => realDirichletTerm K σ m.1) := by
      have hN := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
        (realDirichletTerm_one K σ) (fun hcop => realDirichletTerm_mul_of_coprime K σ hcop)
        (fun hp => hprime_sum hp) N
      exact hN.2.summable
    let emb : {n // n ∈ sPos} ↪ N.smoothNumbers :=
      ⟨fun x => ⟨x.1, hsub x.1 x.2⟩,
        fun x y h => Subtype.ext (congrArg (Subtype.val : N.smoothNumbers → ℕ) h)⟩
    have hsum_eq : ∑ n ∈ s, realDirichletTerm K σ n =
        ∑ m ∈ sPos.attach.map emb, realDirichletTerm K σ m.1 := by
      rw [Finset.sum_map]
      have h1 : ∑ x ∈ sPos.attach, realDirichletTerm K σ (emb x).1 =
          ∑ n ∈ sPos, realDirichletTerm K σ n := Finset.sum_attach sPos (realDirichletTerm K σ)
      rw [h1]
      symm
      refine Finset.sum_subset (Finset.filter_subset _ s) fun n hns hnot => ?_
      have hn0 : n = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hns, hne⟩)
      rw [hn0, realDirichletTerm_zero]
    rw [hsum_eq]
    exact (hN_sum.sum_le_tsum _ (fun m _ => realDirichletTerm_nonneg K σ m.1)).trans (hsmooth_le N)
  have hsummable : Summable (realDirichletTerm K σ) :=
    summable_of_sum_le (realDirichletTerm_nonneg K σ) hfin_le
  exact ⟨hsummable, hsummable.tsum_le_of_sum_le hfin_le⟩

/-- **Unconditional Absolute Convergence & `(riemannZeta σ)^d` Bound (Ideal-Sum Form)**:
for every number field `K` and every `σ > 1`,
`∑'_{I ≠ ⊥} (Ideal.absNorm I)^(-σ) ≤ ((riemannZeta σ).re)^[K : ℚ]`. -/
theorem summable_and_tsum_absNorm_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-σ)) ∧
      (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-σ)) ≤
        ((riemannZeta (σ : ℂ)).re) ^ Module.finrank ℚ K := by
  obtain ⟨hsum_dir, hle_dir⟩ := summable_and_tsum_realDirichletTerm_le K hσ
  let posSet : Set ℕ := {n : ℕ | n ≠ 0}
  let e : {I : Ideal (𝓞 K) // I ≠ ⊥} ≃
      Σ n : posSet, {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} :=
    { toFun := fun I => ⟨⟨Ideal.absNorm I.1, (absNorm_pos_of_ne_bot I.2).ne'⟩, ⟨I.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, mt Ideal.absNorm_eq_zero_iff.mpr (x.2.2.symm ▸ x.1.2)⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := by
        rintro ⟨⟨n, hn⟩, ⟨I, hI⟩⟩
        dsimp only at hI ⊢
        subst hI
        rfl }
  have hfib : ∀ n : posSet,
      HasSum (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} => (Ideal.absNorm I.1 : ℝ) ^ (-σ))
        (realDirichletTerm K σ n.1) := by
    intro n
    have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n.1).to_subtype
    classical
    let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} := Fintype.ofFinite _
    have hfin : ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1}, (Ideal.absNorm I.1 : ℝ) ^ (-σ) =
        realDirichletTerm K σ n.1 := by
      calc ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1}, (Ideal.absNorm I.1 : ℝ) ^ (-σ)
          = ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1}, (n.1 : ℝ) ^ (-σ) :=
              Finset.sum_congr rfl fun I _ => by rw [I.2]
        _ = (idealCount K n.1 : ℝ) * (n.1 : ℝ) ^ (-σ) := by
              simp [idealCount, Nat.card_eq_fintype_card]
        _ = realDirichletTerm K σ n.1 := by
              simp [realDirichletTerm, show n.1 ≠ 0 from n.2]
    rw [← hfin]
    exact hasSum_fintype _
  have hsum_pos : Summable (fun n : posSet => realDirichletTerm K σ n.1) :=
    hsum_dir.subtype _
  have htsum_pos_eq :
      (∑' n : posSet, realDirichletTerm K σ n.1) = ∑' n : ℕ, realDirichletTerm K σ n := by
    rw [tsum_subtype_eq_of_support_subset]
    intro n hn
    change n ≠ 0
    intro h0
    rw [Function.mem_support, h0, realDirichletTerm_zero] at hn
    exact hn rfl
  have hsig_summable : Summable (fun x : Σ n : posSet,
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} => (Ideal.absNorm x.2.1 : ℝ) ^ (-σ)) := by
    rw [summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    refine ⟨fun n => (hfib n).summable, ?_⟩
    simpa only [fun n => (hfib n).tsum_eq] using hsum_pos
  have hsig_eq :
      (∑' x : Σ n : posSet, {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1},
        (Ideal.absNorm x.2.1 : ℝ) ^ (-σ)) = ∑' n : ℕ, realDirichletTerm K σ n := by
    rw [hsig_summable.tsum_sigma]
    simp_rw [fun n => (hfib n).tsum_eq]
    exact htsum_pos_eq
  have hI_summable : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
      (Ideal.absNorm I.1 : ℝ) ^ (-σ)) := by
    have hcomp : (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-σ)) =
        (fun x : Σ n : posSet, {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} =>
          (Ideal.absNorm x.2.1 : ℝ) ^ (-σ)) ∘ e := rfl
    rw [hcomp]
    exact hsig_summable.comp_injective e.injective
  have hI_eq :
      (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-σ)) =
        ∑' n : ℕ, realDirichletTerm K σ n := by
    rw [← hsig_eq]
    exact e.tsum_eq (fun x => (Ideal.absNorm x.2.1 : ℝ) ^ (-σ))
  exact ⟨hI_summable, hI_eq.symm ▸ hle_dir⟩

/-- Complex Dirichlet-series term `n ↦ idealCount K n * n^(-s)` (with `0 ↦ 0`). -/
def complexDirichletTerm (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (idealCount K n : ℂ) * (n : ℂ) ^ (-s)

lemma complexDirichletTerm_zero (s : ℂ) : complexDirichletTerm K s 0 = 0 := by
  simp [complexDirichletTerm]

lemma complexDirichletTerm_one (s : ℂ) : complexDirichletTerm K s 1 = 1 := by
  simp [complexDirichletTerm, idealCount_one]

lemma complexDirichletTerm_mul_of_coprime (s : ℂ) {m n : ℕ} (hcop : m.Coprime n) :
    complexDirichletTerm K s (m * n) =
      complexDirichletTerm K s m * complexDirichletTerm K s n := by
  by_cases hm : m = 0
  · simp [hm, complexDirichletTerm_zero]
  · by_cases hn : n = 0
    · simp [hn, complexDirichletTerm_zero]
    · have hmn : m * n ≠ 0 := mul_ne_zero hm hn
      have hcpow : ((m : ℂ) * (n : ℂ)) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
      simp only [complexDirichletTerm, if_neg hm, if_neg hn, if_neg hmn,
        idealCount_mul_of_coprime K hcop, Nat.cast_mul, hcpow]
      ring

lemma norm_complexDirichletTerm (s : ℂ) (n : ℕ) :
    ‖complexDirichletTerm K s n‖ = realDirichletTerm K s.re n := by
  unfold complexDirichletTerm realDirichletTerm
  split_ifs with hn
  · simp
  · rw [norm_mul, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.neg_re]

/-- Unconditional absolute convergence of `dedekindZeta K s` on `1 < s.re`. -/
theorem summable_norm_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖) := by
  have hR := (summable_and_tsum_absNorm_rpow_le K hs).1
  refine hR.congr fun I => ?_
  rw [Complex.norm_natCast_cpow_of_pos (absNorm_pos_of_ne_bot I.2), Complex.neg_re]

theorem summable_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℂ) ^ (-s)) :=
  (summable_norm_absNorm_cpow K hs).of_norm

/-- Norm bound `‖dedekindZeta K s‖ ≤ ((riemannZeta s.re).re)^[K : ℚ]` on `1 < s.re`. -/
theorem norm_dedekindZeta_le_riemannZeta_pow {s : ℂ} (hs : 1 < s.re) :
    ‖dedekindZeta K s‖ ≤ ((riemannZeta (s.re : ℂ)).re) ^ Module.finrank ℚ K := by
  unfold dedekindZeta
  have hnorm_le := norm_tsum_le_tsum_norm (summable_norm_absNorm_cpow K hs)
  have hR_eq : (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖) =
      ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-s.re) := by
    refine tsum_congr fun I => ?_
    rw [Complex.norm_natCast_cpow_of_pos (absNorm_pos_of_ne_bot I.2), Complex.neg_re]
  exact hnorm_le.trans (hR_eq ▸ (summable_and_tsum_absNorm_rpow_le K hs).2)

/-- Identification of the ideal-sum `dedekindZeta K s` with the Dirichlet series
`∑' n, idealCount K n * n^(-s)` on `1 < s.re`. -/
theorem dedekindZeta_eq_tsum_complexDirichletTerm {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' n : ℕ, complexDirichletTerm K s n := by
  unfold dedekindZeta
  let posSet : Set ℕ := {n : ℕ | n ≠ 0}
  let e : {I : Ideal (𝓞 K) // I ≠ ⊥} ≃
      Σ n : posSet, {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} :=
    { toFun := fun I => ⟨⟨Ideal.absNorm I.1, (absNorm_pos_of_ne_bot I.2).ne'⟩, ⟨I.1, rfl⟩⟩
      invFun := fun x => ⟨x.2.1, mt Ideal.absNorm_eq_zero_iff.mpr (x.2.2.symm ▸ x.1.2)⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := by
        rintro ⟨⟨n, hn⟩, ⟨I, hI⟩⟩
        dsimp only at hI ⊢
        subst hI
        rfl }
  have hsig_summable : Summable (fun x : Σ n : posSet,
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} => (Ideal.absNorm x.2.1 : ℂ) ^ (-s)) :=
    (e.summable_iff).mp (summable_absNorm_cpow K hs)
  have hfib : ∀ n : posSet,
      HasSum (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} => (Ideal.absNorm I.1 : ℂ) ^ (-s))
        (complexDirichletTerm K s n.1) := by
    intro n
    have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n.1).to_subtype
    classical
    let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1} := Fintype.ofFinite _
    have hfin : ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1}, (Ideal.absNorm I.1 : ℂ) ^ (-s) =
        complexDirichletTerm K s n.1 := by
      calc ∑ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1}, (Ideal.absNorm I.1 : ℂ) ^ (-s)
          = ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1}, (n.1 : ℂ) ^ (-s) :=
              Finset.sum_congr rfl fun I _ => by rw [I.2]
        _ = (idealCount K n.1 : ℂ) * (n.1 : ℂ) ^ (-s) := by
              simp [idealCount, Nat.card_eq_fintype_card]
        _ = complexDirichletTerm K s n.1 := by
              simp [complexDirichletTerm, show n.1 ≠ 0 from n.2]
    rw [← hfin]
    exact hasSum_fintype _
  have he_tsum : (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℂ) ^ (-s)) =
      ∑' x : Σ n : posSet, {I : Ideal (𝓞 K) // Ideal.absNorm I = n.1},
        (Ideal.absNorm x.2.1 : ℂ) ^ (-s) :=
    e.tsum_eq (fun x => (Ideal.absNorm x.2.1 : ℂ) ^ (-s))
  rw [he_tsum, hsig_summable.tsum_sigma]
  simp_rw [fun n => (hfib n).tsum_eq]
  rw [tsum_subtype_eq_of_support_subset]
  intro n hn
  change n ≠ 0
  intro h0
  rw [Function.mem_support, h0, complexDirichletTerm_zero] at hn
  exact hn rfl

/-- Exact equality between our concrete ideal-sum `dedekindZeta K s` and Mathlib's
`NumberField.dedekindZeta K s` on `1 < s.re`. -/
theorem dedekindZeta_eq_mathlib {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = NumberField.dedekindZeta K s := by
  rw [dedekindZeta_eq_tsum_complexDirichletTerm K hs, NumberField.dedekindZeta, LSeries]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    simp [complexDirichletTerm, LSeries.term]
  · simp only [complexDirichletTerm, LSeries.term, if_neg hn, idealCount,
      div_eq_mul_inv, Complex.cpow_neg]

/-- Summability of `N(v)^(-s)` over all height-one prime ideals `v : HeightOneSpectrum (𝓞 K)`
for `1 < s.re`. -/
theorem summable_heightOne_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  let ι : HeightOneSpectrum (𝓞 K) → {I : Ideal (𝓞 K) // I ≠ ⊥} := fun v => ⟨v.asIdeal, v.ne_bot⟩
  have hι : Function.Injective ι := fun v w h => HeightOneSpectrum.ext (congrArg Subtype.val h)
  have h : Summable ((fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℂ) ^ (-s)) ∘ ι) :=
    (summable_absNorm_cpow K hs).comp_injective hι
  exact h

/-- General subtype exponential-logarithm `HasProd` for the Dedekind Euler product on ANY
predicate `P : HeightOneSpectrum (𝓞 K) → Prop` on `1 < s.re`. -/
theorem hasProd_eulerProduct_subtype_exp_neg_log (P : HeightOneSpectrum (𝓞 K) → Prop)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // P v} =>
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
      (Complex.exp (∑' v : {v : HeightOneSpectrum (𝓞 K) // P v},
        -Complex.log (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hsum : Summable (fun v : {v : HeightOneSpectrum (𝓞 K) // P v} =>
      (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) :=
    (summable_heightOne_absNorm_cpow K hs).comp_injective Subtype.val_injective
  have hlog : Summable (fun v : {v : HeightOneSpectrum (𝓞 K) // P v} =>
      -Complex.log (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))) :=
    hsum.clog_one_sub.neg
  have hexp := hlog.hasSum.cexp
  refine hexp.congr_fun fun v => ?_
  rw [Function.comp_apply, Complex.exp_neg]
  have hnorm_lt : ‖(Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    have hgt : 1 < Ideal.absNorm v.1.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_one.trans hgt), Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hgt) (neg_lt_zero.mpr hs0)
  have hne : 1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s) ≠ 0 := by
    intro h0
    have heq : (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
    rw [heq, norm_one] at hnorm_lt
    exact lt_irrefl 1 hnorm_lt
  rw [Complex.exp_log hne]

/-- Multipliability and exponential-logarithm representation of the Dedekind Euler product over
all height-one prime ideals `v : HeightOneSpectrum (𝓞 K)` on `1 < s.re`. -/
theorem hasProd_eulerProduct_exp_neg_log {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (Complex.exp (∑' v : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))) := by
  let e : HeightOneSpectrum (𝓞 K) ≃ {v : HeightOneSpectrum (𝓞 K) // True} :=
    { toFun := fun v => ⟨v, trivial⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := hasProd_eulerProduct_subtype_exp_neg_log K (fun _ => True) hs
  rw [← e.tsum_eq (fun v : {v : HeightOneSpectrum (𝓞 K) // True} =>
    -Complex.log (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)))] at h
  exact (Equiv.hasProd_iff e).mpr h

/-- Canonical fiber decomposition of all height-one prime ideals of `𝓞 K` by the unique rational
prime `p` below them: `HeightOneSpectrum (𝓞 K) ≃ Σ p : Nat.Primes, PrimesAbove K p`. -/
def heightOneEquivSigmaPrimesAbove :
    HeightOneSpectrum (𝓞 K) ≃ Σ p : Nat.Primes, PrimesAbove K p where
  toFun v := ⟨⟨(Ideal.absNorm v.asIdeal).minFac, minFac_absNorm_prime v⟩,
    ⟨v, Nat.minFac_dvd (Ideal.absNorm v.asIdeal)⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨⟨p, hp⟩, ⟨v, hv⟩⟩ := x
    have hpeq : (Ideal.absNorm v.asIdeal).minFac = p :=
      (eq_minFac_of_prime_dvd_absNorm v hp hv).symm
    have hprime_eq : (⟨(Ideal.absNorm v.asIdeal).minFac, minFac_absNorm_prime v⟩ : Nat.Primes) =
        ⟨p, hp⟩ := Subtype.ext hpeq
    refine Sigma.ext hprime_eq ?_
    cases hprime_eq
    rfl

/-- **UNCONDITIONAL EXACT EULER PRODUCT OF THE DEDEKIND ZETA FUNCTION (`HasProd` form)**:
for every number field `K` and every `s : ℂ` with `1 < s.re`,
`HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - N(v)^(-s))⁻¹) (dedekindZeta K s)`. -/
theorem dedekindZeta_hasProd_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (dedekindZeta K s) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hnorm_sum : Summable (fun n : ℕ => ‖complexDirichletTerm K s n‖) := by
    simpa only [norm_complexDirichletTerm] using (summable_and_tsum_realDirichletTerm_le K hs).1
  have hep := EulerProduct.eulerProduct_hasProd
    (complexDirichletTerm_one K s) (fun hcop => complexDirichletTerm_mul_of_coprime K s hcop)
    hnorm_sum (complexDirichletTerm_zero K s)
  rw [← dedekindZeta_eq_tsum_complexDirichletTerm K hs] at hep
  have hmult_v : Multipliable (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (hasProd_eulerProduct_exp_neg_log K hs).multipliable
  have hmult_sig : Multipliable (fun x : Σ p : Nat.Primes, PrimesAbove K p =>
      (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (Equiv.multipliable_iff (heightOneEquivSigmaPrimesAbove K)).mp hmult_v
  have hfib_prod : ∀ p : Nat.Primes,
      HasProd (fun v : PrimesAbove K p => (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
        (∑' k : ℕ, complexDirichletTerm K s ((p : ℕ) ^ k)) := by
    intro p
    have : Finite (PrimesAbove K p) := finite_primesAbove K p.2
    classical
    let : Fintype (PrimesAbove K p) := Fintype.ofFinite _
    have hlocal := hasSum_idealCount_prime_pow_cpow K p.2 hs0
    have htsum_eq : (∑' k : ℕ, complexDirichletTerm K s ((p : ℕ) ^ k)) =
        ∏ v : PrimesAbove K p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ := by
      rw [← hlocal.tsum_eq]
      refine tsum_congr fun k => ?_
      simp [complexDirichletTerm, p.2.ne_zero]
    rw [htsum_eq]
    exact hasProd_fintype _
  have hsig_prod : HasProd (fun x : Σ p : Nat.Primes, PrimesAbove K p =>
      (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) :=
    HasProd.sigma_of_hasProd hep hfib_prod hmult_sig
  exact (Equiv.hasProd_iff (heightOneEquivSigmaPrimesAbove K)).mpr hsig_prod

/-- **UNCONDITIONAL EXACT EULER PRODUCT OF THE DEDEKIND ZETA FUNCTION (`tprod` form)**:
for every number field `K` and every `s : ℂ` with `1 < s.re`,
`dedekindZeta K s = ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ)^(-s))⁻¹`. -/
theorem dedekindZeta_eq_tprod_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ :=
  (dedekindZeta_hasProd_eulerProduct K hs).tprod_eq.symm

/-- Exact exponential-logarithm formula for `dedekindZeta K s` on `1 < s.re`. -/
theorem dedekindZeta_eq_exp_tsum_neg_log {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      Complex.exp (∑' v : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) :=
  (dedekindZeta_hasProd_eulerProduct K hs).unique (hasProd_eulerProduct_exp_neg_log K hs)

/-- **Exact Bridge to `Stage5AdelicTate`**: for every number field `K` and every `s : ℂ` with
`1 < s.re`, the concrete Dedekind zeta function equals the global Euler product of
`Stage5AdelicTate.localTateZetaFin v 1 s` over all finite places `v : HeightOneSpectrum (𝓞 K)`. -/
theorem dedekindZeta_eq_tprod_localTateZetaFin {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      ∏' v : HeightOneSpectrum (𝓞 K), RHDirect.Stage5AdelicTate.localTateZetaFin v 1 s := by
  rw [dedekindZeta_eq_tprod_eulerProduct K hs]
  refine tprod_congr fun v => ?_
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  rw [RHDirect.Stage5AdelicTate.localTateZetaFin_eq_eulerFactor v (by simp) hs0,
    one_mul, RHDirect.Stage5AdelicTate.residueCard_eq_absNorm]

/-- **Unconditional Nonvanishing of `dedekindZeta K s` on `1 < s.re`**. -/
theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  rw [dedekindZeta_eq_exp_tsum_neg_log K hs]
  exact Complex.exp_ne_zero _

/-- For `K = ℚ`, every natural number `n` is the absolute norm of a unique ideal of `𝓞 ℚ`. -/
theorem idealCount_rat (n : ℕ) : idealCount ℚ n = 1 := by
  unfold idealCount
  have heq : Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} =
      Nat.card {J : Ideal ℤ // Ideal.absNorm J = n} := by
    let eR : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
    have hnorm_map : ∀ I : Ideal (𝓞 ℚ), Ideal.absNorm (Ideal.map eR.toRingHom I) = Ideal.absNorm I := by
      intro I
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
      exact Nat.card_congr (Ideal.quotientEquiv I (Ideal.map eR.toRingHom I) eR rfl).symm.toEquiv
    have hlr : ∀ I : Ideal (𝓞 ℚ), Ideal.map eR.symm.toRingHom (Ideal.map eR.toRingHom I) = I := by
      intro I
      rw [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id]
    have hrl : ∀ J : Ideal ℤ, Ideal.map eR.toRingHom (Ideal.map eR.symm.toRingHom J) = J := by
      intro J
      rw [Ideal.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Ideal.map_id]
    refine Nat.card_congr
      { toFun := fun I => ⟨Ideal.map eR.toRingHom I.1, (hnorm_map I.1).trans I.2⟩
        invFun := fun J => ⟨Ideal.map eR.symm.toRingHom J.1, by
          have h1 := hnorm_map (Ideal.map eR.symm.toRingHom J.1)
          rw [hrl] at h1
          exact h1.symm.trans J.2⟩
        left_inv := fun I => Subtype.ext (hlr I.1)
        right_inv := fun J => Subtype.ext (hrl J.1) }
  rw [heq]
  let : Unique {J : Ideal ℤ // Ideal.absNorm J = n} :=
    { default := ⟨Ideal.span {(n : ℤ)}, by
        rw [Ideal.absNorm_span_singleton]
        simp [Algebra.norm_self]⟩
      uniq := fun ⟨J, hJ⟩ => by
        apply Subtype.ext
        dsimp only
        rw [← Int.ideal_span_absNorm_eq_self J, hJ] }
  exact Nat.card_unique

/-- **Exact Rational Base Case**: `dedekindZeta ℚ s = riemannZeta s` on `1 < s.re`. -/
theorem dedekindZeta_rat_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s := by
  rw [dedekindZeta_eq_tsum_complexDirichletTerm ℚ hs, zeta_eq_tsum_one_div_nat_cpow hs]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst hn
    have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
    simp [complexDirichletTerm_zero, Complex.zero_cpow hs0]
  · simp [complexDirichletTerm, hn, idealCount_rat n, one_div, Complex.cpow_neg]

end EulerProductAndConvergence

/-! ## Section 3: Exact Cyclotomic Dedekind Zeta Factorization (`ζ_{ℚ(ζ_m)}(s) = ∏_{χ mod m} L(s, χ)`) -/

section CyclotomicFactorization

open RHDirect.Stage4ClassFieldTheory

/-- At every unramified prime `p ∤ m`, the inertia degree of every prime ideal `v` of
`𝓞 (CycField m)` above `p` equals `Stage4ClassFieldTheory.resDeg m p hp_cop`. -/
theorem cyc_inertiaDeg_eq_resDeg {m p : ℕ} [NeZero m] (hp : p.Prime) (hndvd : ¬ p ∣ m)
    (v : PrimesAbove (CycField m) p) :
    v.1.asIdeal.inertiaDeg ℤ = resDeg m p (hp.coprime_iff_not_dvd.mpr hndvd) := by
  have : Fact p.Prime := ⟨hp⟩
  have : v.1.asIdeal.IsPrime := v.1.isPrime
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := m) p (CycField m) v.1.asIdeal hndvd]
  unfold resDeg
  have hcoe : ((ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hndvd) : (ZMod m)ˣ) : ZMod m) =
      (p : ZMod m) := ZMod.coe_unitOfCoprime p _
  rw [← hcoe, orderOf_units]

/-- At every unramified prime `p ∤ m`, the ramification index of every prime ideal `v` of
`𝓞 (CycField m)` above `p` equals `1`. -/
theorem cyc_ramificationIdx_eq_one {m p : ℕ} [NeZero m] (hp : p.Prime) (hndvd : ¬ p ∣ m)
    (v : PrimesAbove (CycField m) p) :
    v.1.asIdeal.ramificationIdx ℤ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : v.1.asIdeal.IsPrime := v.1.isPrime
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (m := m) p (CycField m)
    v.1.asIdeal hndvd

/-- At every unramified prime `p ∤ m`, every prime ideal `v` of `𝓞 (CycField m)` above `p`
has exact absolute norm `Ideal.absNorm v.1.asIdeal = p ^ (resDeg m p hp_cop)`. -/
theorem cyc_absNorm_eq_pow_resDeg {m p : ℕ} [NeZero m] (hp : p.Prime) (hndvd : ¬ p ∣ m)
    (v : PrimesAbove (CycField m) p) :
    Ideal.absNorm v.1.asIdeal = p ^ resDeg m p (hp.coprime_iff_not_dvd.mpr hndvd) := by
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    (dvd_absNorm_iff_liesOver v.1 hp).mp v.2
  have : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have : v.1.asIdeal.IsMaximal := heightOne_isMaximal v.1
  rw [Ideal.absNorm_eq_pow_inertiaDeg' v.1.asIdeal hp,
    Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) v.1.asIdeal,
    cyc_inertiaDeg_eq_resDeg hp hndvd v]

/-- At every unramified prime `p ∤ m`, the number of prime ideals of `𝓞 (CycField m)` above `p`
equals `Stage4ClassFieldTheory.numPrimesAbove m p hp_cop = φ(m) / f`. -/
theorem cyc_card_primesAbove_eq_numPrimesAbove {m p : ℕ} [NeZero m] (hp : p.Prime) (hndvd : ¬ p ∣ m)
    [Fintype (PrimesAbove (CycField m) p)] :
    Fintype.card (PrimesAbove (CycField m) p) =
      numPrimesAbove m p (hp.coprime_iff_not_dvd.mpr hndvd) := by
  set hp_cop := hp.coprime_iff_not_dvd.mpr hndvd
  have hsum := sum_ramification_inertia_primesAbove (CycField m) hp
  rw [cyc_finrank m] at hsum
  have hlhs :
      ∑ v : PrimesAbove (CycField m) p, v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ =
        Fintype.card (PrimesAbove (CycField m) p) * resDeg m p hp_cop := by
    calc ∑ v : PrimesAbove (CycField m) p, v.1.asIdeal.ramificationIdx ℤ * v.1.asIdeal.inertiaDeg ℤ
        = ∑ _v : PrimesAbove (CycField m) p, 1 * resDeg m p hp_cop :=
            Finset.sum_congr rfl fun v _ => by
              rw [cyc_ramificationIdx_eq_one hp hndvd v, cyc_inertiaDeg_eq_resDeg hp hndvd v]
      _ = Fintype.card (PrimesAbove (CycField m) p) * resDeg m p hp_cop := by simp
  rw [hlhs] at hsum
  have hf_pos : 0 < resDeg m p hp_cop := resDeg_pos hp_cop
  unfold numPrimesAbove
  rw [← hsum, Nat.mul_div_cancel _ hf_pos]

/-- **Exact Local Cyclotomic Dedekind Euler Factor = `dedekindCycEulerFactor` = `∏_χ L_p(s, χ)`**:
at every unramified prime `p ∤ m` and every `s : ℂ`, the product of the actual Dedekind zeta
local Euler factors of `CyclotomicField m ℚ` over primes `v ∣ p` equals both
`Stage4ClassFieldTheory.dedekindCycEulerFactor m p hp_cop s` and
`∏ χ : DirichletCharacter ℂ m, (1 - χ p * p^(-s))⁻¹`. -/
theorem cyc_local_dedekind_eulerFactor_eq_dedekindCycEulerFactor {m p : ℕ} [NeZero m]
    (hp : p.Prime) (hndvd : ¬ p ∣ m) [Fintype (PrimesAbove (CycField m) p)] (s : ℂ) :
    ∏ v : PrimesAbove (CycField m) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      dedekindCycEulerFactor m p (hp.coprime_iff_not_dvd.mpr hndvd) s := by
  set hp_cop := hp.coprime_iff_not_dvd.mpr hndvd
  rw [dedekindCycEulerFactor_eq_norm_pow hp.pos hp_cop s]
  calc ∏ v : PrimesAbove (CycField m) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹
      = ∏ _v : PrimesAbove (CycField m) p, (1 - ((p ^ resDeg m p hp_cop : ℕ) : ℂ) ^ (-s))⁻¹ :=
          Finset.prod_congr rfl fun v _ => by rw [cyc_absNorm_eq_pow_resDeg hp hndvd v]
    _ = ((1 - ((p ^ resDeg m p hp_cop : ℕ) : ℂ) ^ (-s))⁻¹) ^
          Fintype.card (PrimesAbove (CycField m) p) := by simp
    _ = ((1 - ((p ^ resDeg m p hp_cop : ℕ) : ℂ) ^ (-s))⁻¹) ^ numPrimesAbove m p hp_cop := by
          rw [cyc_card_primesAbove_eq_numPrimesAbove hp hndvd]

theorem cyc_local_dedekind_eulerFactor_eq_prod_dirichlet {m p : ℕ} [NeZero m]
    (hp : p.Prime) (hndvd : ¬ p ∣ m) [Fintype (PrimesAbove (CycField m) p)] (s : ℂ) :
    ∏ v : PrimesAbove (CycField m) p, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ =
      ∏ χ : DirichletCharacter ℂ m, dirichletEulerFactor χ p s := by
  rw [cyc_local_dedekind_eulerFactor_eq_dedekindCycEulerFactor hp hndvd s,
    prod_dirichletEulerFactor_eq_dedekindCycEulerFactor (hp.coprime_iff_not_dvd.mpr hndvd) s]

/-- Helper: finite product of `HasProd` families in a topological commutative monoid. -/
lemma hasProd_finset_prod {ι α β : Type*} [CommMonoid β] [TopologicalSpace β] [ContinuousMul β]
    (S : Finset ι) {f : ι → α → β} {a : ι → β} (hf : ∀ i ∈ S, HasProd (f i) (a i)) :
    HasProd (fun x : α => ∏ i ∈ S, f i x) (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty] using hasProd_one
  | insert x s hx ih =>
    have h1 := hf x (Finset.mem_insert_self x s)
    have h2 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.prod_insert hx] using h1.mul h2

/-- For every Dirichlet character `χ : DirichletCharacter ℂ m`, its Euler product restricted to
unramified primes `p ∤ m` equals `DirichletCharacter.LFunction χ s` on `1 < s.re` (because
every ramified prime `p ∣ m` has `χ(p) = 0`, hence local Euler factor `1`). -/
theorem dirichletLFunction_hasProd_unramified {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : {p : Nat.Primes // ¬ ((p : ℕ) ∣ m)} => dirichletEulerFactor χ p.1 s)
      (DirichletCharacter.LFunction χ s) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hall := DirichletCharacter.LSeries_eulerProduct_hasProd χ hs
  let U : Set Nat.Primes := {p : Nat.Primes | ¬ ((p : ℕ) ∣ m)}
  have hsupp : Function.mulSupport (fun p : Nat.Primes => dirichletEulerFactor χ p s) ⊆ U := by
    intro p hp_supp
    change ¬ ((p : ℕ) ∣ m)
    intro hdvd
    apply hp_supp
    change dirichletEulerFactor χ p s = 1
    unfold dirichletEulerFactor
    have hnot_unit : ¬ IsUnit ((p : ℕ) : ZMod m) := by
      rw [ZMod.isUnit_iff_coprime]
      intro hcop
      exact p.2.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd)
    rw [MulChar.map_nonunit χ hnot_unit, zero_mul, sub_zero, inv_one]
  exact (hasProd_subtype_iff_of_mulSupport_subset hsupp).mpr hall

/-- **EXACT UNRAMIFIED GLOBAL CYCLOTOMIC DEDEKIND PRODUCT = `∏_{χ mod m} L(s, χ)` (`HasProd` form)**:
for every `m ≥ 1` and every `s : ℂ` with `1 < s.re`,
`HasProd (fun v : {v // ¬ (N(v).minFac ∣ m)} => (1 - N(v)^(-s))⁻¹) (∏ χ, L(s, χ))`. -/
theorem cyc_unramified_hasProd_eq_prod_dirichletLFunction (m : ℕ) [NeZero m]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun v : {v : HeightOneSpectrum (𝓞 (CycField m)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)} =>
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
      (∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s) := by
  have hprod_primes :
      HasProd
        (fun p : {p : Nat.Primes // ¬ ((p : ℕ) ∣ m)} =>
          ∏ χ : DirichletCharacter ℂ m, dirichletEulerFactor χ p.1 s)
        (∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s) :=
    hasProd_finset_prod Finset.univ fun χ _ => dirichletLFunction_hasProd_unramified χ hs
  let eUnram :
      {v : HeightOneSpectrum (𝓞 (CycField m)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)} ≃
        Σ p : {p : Nat.Primes // ¬ ((p : ℕ) ∣ m)}, PrimesAbove (CycField m) p.1 :=
    { toFun := fun v =>
        ⟨⟨⟨(Ideal.absNorm v.1.asIdeal).minFac, minFac_absNorm_prime v.1⟩, v.2⟩,
          ⟨v.1, Nat.minFac_dvd (Ideal.absNorm v.1.asIdeal)⟩⟩
      invFun := fun x =>
        ⟨x.2.1, by
          have hpeq := eq_minFac_of_prime_dvd_absNorm x.2.1 x.1.1.2 x.2.2
          rw [← hpeq]
          exact x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun x => by
        obtain ⟨⟨⟨p, hp⟩, hndvd⟩, ⟨v, hv⟩⟩ := x
        dsimp only
        have hpeq : (⟨(Ideal.absNorm v.asIdeal).minFac, minFac_absNorm_prime v⟩ : Nat.Primes) =
            ⟨p, hp⟩ := Subtype.ext (eq_minFac_of_prime_dvd_absNorm v hp hv).symm
        have hmk : ∀ (a b : Nat.Primes) (ha : ¬ ((a : ℕ) ∣ m)) (hb : ¬ ((b : ℕ) ∣ m))
            (hv1 : (a : ℕ) ∣ Ideal.absNorm v.asIdeal) (hv2 : (b : ℕ) ∣ Ideal.absNorm v.asIdeal),
            a = b →
              (⟨⟨a, ha⟩, ⟨v, hv1⟩⟩ :
                Σ q : {q : Nat.Primes // ¬ ((q : ℕ) ∣ m)}, PrimesAbove (CycField m) q.1) =
              ⟨⟨b, hb⟩, ⟨v, hv2⟩⟩ := by
          rintro _ _ _ _ _ _ rfl; rfl
        exact hmk _ _ _ _ _ _ hpeq }
  have hmult_v :
      Multipliable
        (fun v : {v : HeightOneSpectrum (𝓞 (CycField m)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)} =>
          (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (hasProd_eulerProduct_subtype_exp_neg_log (CycField m)
      (fun v => ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)) hs).multipliable
  have hmult_sig :
      Multipliable
        (fun x : Σ p : {p : Nat.Primes // ¬ ((p : ℕ) ∣ m)}, PrimesAbove (CycField m) p.1 =>
          (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (Equiv.multipliable_iff eUnram).mp hmult_v
  have hfib : ∀ p : {p : Nat.Primes // ¬ ((p : ℕ) ∣ m)},
      HasProd (fun v : PrimesAbove (CycField m) p.1 =>
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹)
        (∏ χ : DirichletCharacter ℂ m, dirichletEulerFactor χ p.1 s) := by
    intro p
    have : Finite (PrimesAbove (CycField m) p.1) := finite_primesAbove (CycField m) p.1.2
    classical
    let : Fintype (PrimesAbove (CycField m) p.1) := Fintype.ofFinite _
    rw [← cyc_local_dedekind_eulerFactor_eq_prod_dirichlet p.1.2 p.2 s]
    exact hasProd_fintype _
  have hsig_prod :
      HasProd
        (fun x : Σ p : {p : Nat.Primes // ¬ ((p : ℕ) ∣ m)}, PrimesAbove (CycField m) p.1 =>
          (1 - (Ideal.absNorm x.2.1.asIdeal : ℂ) ^ (-s))⁻¹)
        (∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s) :=
    HasProd.sigma_of_hasProd hprod_primes hfib hmult_sig
  exact (Equiv.hasProd_iff eUnram).mpr hsig_prod

/-- **EXACT UNRAMIFIED GLOBAL CYCLOTOMIC PRODUCT EQUALITY (`tprod` form)**:
for every `m ≥ 1` and every `s : ℂ` with `1 < s.re`:
`∏' v : {v : HeightOneSpectrum (𝓞 (CycField m)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)}, (1 - N(v)^(-s))⁻¹ = ∏ χ : DirichletCharacter ℂ m, L(s, χ)`. -/
theorem cyc_unramified_tprod_eq_prod_dirichletLFunction (m : ℕ) [NeZero m]
    {s : ℂ} (hs : 1 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 (CycField m)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)},
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) =
      ∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s :=
  (cyc_unramified_hasProd_eq_prod_dirichletLFunction m hs).tprod_eq

/-- **Exact Full Cyclotomic Dedekind Zeta Factorization on `1 < s.re`**:
`ζ_{ℚ(ζ_m)}(s)` equals the product of the ramified Euler factors at primes `v ∣ m` times
`∏_{χ : DirichletCharacter ℂ m} L(s, χ)`. -/
theorem cyc_dedekindZeta_eq_ramified_mul_prod_dirichletLFunction (m : ℕ) [NeZero m]
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (CycField m) s =
      (∏' v : {v : HeightOneSpectrum (𝓞 (CycField m)) // (Ideal.absNorm v.asIdeal).minFac ∣ m},
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) *
      (∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s) := by
  classical
  rw [dedekindZeta_eq_tprod_eulerProduct (CycField m) hs,
    ← cyc_unramified_tprod_eq_prod_dirichletLFunction m hs]
  let S : Set (HeightOneSpectrum (𝓞 (CycField m))) :=
    {v | (Ideal.absNorm v.asIdeal).minFac ∣ m}
  have hmult_ram : Multipliable (fun v : S => (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (hasProd_eulerProduct_subtype_exp_neg_log (CycField m)
      (fun v => (Ideal.absNorm v.asIdeal).minFac ∣ m) hs).multipliable
  have hmult_unram : Multipliable (fun v : (Sᶜ : Set _) =>
      (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) :=
    (hasProd_eulerProduct_subtype_exp_neg_log (CycField m)
      (fun v => ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)) hs).multipliable
  have h1 : (∏' v : {v : HeightOneSpectrum (𝓞 (CycField m)) // (Ideal.absNorm v.asIdeal).minFac ∣ m},
      (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) =
      ∏' v : S, (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ := rfl
  have h2 : (∏' v : {v : HeightOneSpectrum (𝓞 (CycField m)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)},
      (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) =
      ∏' v : (Sᶜ : Set _), (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ := rfl
  rw [h1, h2,
    tprod_subtype S (fun v => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹),
    tprod_subtype (Sᶜ : Set _) (fun v => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹),
    ← Multipliable.tprod_mul
      (multipliable_subtype_iff_mulIndicator.mp hmult_ram)
      (multipliable_subtype_iff_mulIndicator.mp hmult_unram)]
  refine tprod_congr fun v => ?_
  by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]

end CyclotomicFactorization

/-! ## Section 4: Minkowski's Discriminant Lower Bound, Minkowski's Theorem & Exponential Growth -/

section MinkowskiDiscriminant

open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

/-- Exact covolume of the canonical lattice `𝓞 K ↪ ℝ^{r₁} × ℂ^{r₂}` in terms of `|NumberField.discr K|`. -/
theorem integerLattice_covolume_eq :
    ZLattice.covolume (NumberField.mixedEmbedding.integerLattice K) MeasureTheory.volume =
      2⁻¹ ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)| :=
  NumberField.mixedEmbedding.covolume_integerLattice K

/-- Strict positivity of the discriminant `|NumberField.discr K| > 0` for every number field `K`. -/
theorem abs_discr_pos : 0 < |(NumberField.discr K : ℝ)| := by
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  exact abs_pos.mpr (Int.cast_ne_zero.mpr hne)

/-- Strict positivity of the canonical lattice covolume of `𝓞 K`. -/
theorem integerLattice_covolume_pos :
    0 < ZLattice.covolume (NumberField.mixedEmbedding.integerLattice K) MeasureTheory.volume := by
  rw [integerLattice_covolume_eq K]
  exact mul_pos (pow_pos (by norm_num) _) (Real.sqrt_pos.mpr (abs_discr_pos K))

/-- **SHARP MINKOWSKI DISCRIMINANT LOWER BOUND**:
for EVERY number field `K` of degree `d = finrank ℚ K` and `r₂ = nrComplexPlaces K`:
`((π / 4)^r₂ * (d^d / d!))^2 ≤ |NumberField.discr K|`. -/
theorem minkowski_discr_lower_bound :
    ((Real.pi / 4) ^ InfinitePlace.nrComplexPlaces K *
        ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K /
          ((Module.finrank ℚ K).factorial : ℝ))) ^ 2 ≤
      |(NumberField.discr K : ℝ)| := by
  have hbase := NumberField.abs_discr_ge' K
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hfac : ((Module.finrank ℚ K).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hlhs :
      ((Real.pi / 4) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K /
            ((Module.finrank ℚ K).factorial : ℝ))) ^ 2 =
        (Module.finrank ℚ K : ℝ) ^ (2 * Module.finrank ℚ K) /
          ((4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces K) *
            ((Module.finrank ℚ K).factorial : ℝ) ^ 2) := by
    rw [mul_pow, ← pow_mul (Real.pi / 4),
      div_pow ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K),
      ← pow_mul (Module.finrank ℚ K : ℝ),
      mul_comm (InfinitePlace.nrComplexPlaces K) 2, mul_comm (Module.finrank ℚ K) 2]
    have hinv : (Real.pi / 4) ^ (2 * InfinitePlace.nrComplexPlaces K) =
        ((4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces K))⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [hinv]
    field_simp
  rw [hlhs]
  simpa only [Int.cast_abs] using hbase

/-- Expanded form of the sharp Minkowski discriminant lower bound:
`(π / 4)^(2 r₂) * (d^d / d!)^2 ≤ |NumberField.discr K|`. -/
theorem minkowski_discr_lower_bound_expanded :
    (Real.pi / 4) ^ (2 * InfinitePlace.nrComplexPlaces K) *
        ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K /
          ((Module.finrank ℚ K).factorial : ℝ)) ^ 2 ≤
      |(NumberField.discr K : ℝ)| := by
  have h := minkowski_discr_lower_bound K
  rw [mul_pow, ← pow_mul, mul_comm (InfinitePlace.nrComplexPlaces K) 2] at h
  exact h

/-- **Minkowski's Theorem (Strong Form)**: every nontrivial number field `K ≠ ℚ` has
`|NumberField.discr K| > 2`. -/
theorem minkowski_abs_discr_gt_two (hK : 1 < Module.finrank ℚ K) :
    2 < |NumberField.discr K| :=
  NumberField.abs_discr_gt_two hK

/-- **Minkowski's Theorem (`|disc(K)| > 1` for `K ≠ ℚ`)**: every nontrivial number field
has discriminant strictly greater than `1` in absolute value. -/
theorem minkowski_abs_discr_gt_one (hK : 1 < Module.finrank ℚ K) :
    1 < |NumberField.discr K| :=
  lt_trans (by norm_num : (1 : ℤ) < 2) (minkowski_abs_discr_gt_two K hK)

/-- **Minkowski's Ramification Theorem**: every nontrivial number field (`1 < finrank ℚ K`)
is ramified at some rational prime `p`. -/
theorem minkowski_exists_ramified_prime (hK : 1 < Module.finrank ℚ K) :
    ∃ p : ℕ, p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) :=
  NumberField.exists_not_isUnramifiedIn (ne_of_gt hK)

/-- **Minkowski's Exponential Discriminant Lower Bound**:
for every number field `K` with `1 < finrank ℚ K`:
`4 / 9 * (3 * π / 4)^[K : ℚ] ≤ |NumberField.discr K|`. -/
theorem minkowski_discr_exponential_lower_bound (hK : 1 < Module.finrank ℚ K) :
    4 / 9 * (3 * Real.pi / 4) ^ Module.finrank ℚ K ≤ |(NumberField.discr K : ℝ)| := by
  simpa only [Int.cast_abs] using NumberField.abs_discr_ge (K := K) hK

/-- Helper: `2 ≤ 3 * π / 4` (since `π > 3`). -/
lemma two_le_three_pi_div_four : (2 : ℝ) ≤ 3 * Real.pi / 4 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith

/-- Helper: `2 ^ n ≥ n ^ 2 / 4`? Even simpler: for all `n : ℕ`, `n ^ 2 ≤ 2 ^ n` for `n ≥ 4`,
and `2 ^ n` grows super-linearly (`n * (n - 1) / 2 ≤ 2 ^ n`). We prove directly by induction
that `n ^ 2 ≤ 2 ^ n` for all `n ≥ 4`. -/
lemma sq_le_two_pow {n : ℕ} (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 3
    · subst hk; norm_num
    · have hk4 : 4 ≤ k := by omega
      have h1 := ih hk4
      have h2 : 2 * k + 1 ≤ k ^ 2 := by nlinarith
      calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
        _ ≤ k ^ 2 + k ^ 2 := by omega
        _ = 2 * k ^ 2 := by ring
        _ ≤ 2 * 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by ring

/-- **Super-Linear Growth of Number Field Discriminants**:
for every constant `C : ℝ`, there exists `D : ℕ` such that EVERY number field `K` with
`D ≤ finrank ℚ K` satisfies `C * finrank ℚ K ≤ |NumberField.discr K|`. -/
theorem minkowski_discr_superlinear_growth (C : ℝ) :
    ∃ D : ℕ, ∀ (K : Type) [Field K] [NumberField K],
      D ≤ Module.finrank ℚ K → C * (Module.finrank ℚ K : ℝ) ≤ |(NumberField.discr K : ℝ)| := by
  refine ⟨max 4 (Nat.ceil (9 / 4 * max C 0)), fun K _ _ hd => ?_⟩
  have hd4 : 4 ≤ Module.finrank ℚ K := le_trans (le_max_left _ _) hd
  have hd1 : 1 < Module.finrank ℚ K := by omega
  have hdC : 9 / 4 * max C 0 ≤ (Module.finrank ℚ K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hd)
  have hsq : ((Module.finrank ℚ K : ℝ) ^ 2) ≤ (2 : ℝ) ^ Module.finrank ℚ K := by
    exact_mod_cast sq_le_two_pow hd4
  have hpow : (2 : ℝ) ^ Module.finrank ℚ K ≤ (3 * Real.pi / 4) ^ Module.finrank ℚ K :=
    pow_le_pow_left₀ (by norm_num) two_le_three_pi_div_four _
  have hd_nn : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  calc C * (Module.finrank ℚ K : ℝ)
      ≤ max C 0 * (Module.finrank ℚ K : ℝ) := mul_le_mul_of_nonneg_right (le_max_left C 0) hd_nn
    _ = 4 / 9 * ((9 / 4 * max C 0) * (Module.finrank ℚ K : ℝ)) := by ring
    _ ≤ 4 / 9 * ((Module.finrank ℚ K : ℝ) * (Module.finrank ℚ K : ℝ)) := by
        gcongr
    _ = 4 / 9 * (Module.finrank ℚ K : ℝ) ^ 2 := by ring
    _ ≤ 4 / 9 * (2 : ℝ) ^ Module.finrank ℚ K := by gcongr
    _ ≤ 4 / 9 * (3 * Real.pi / 4) ^ Module.finrank ℚ K := by gcongr
    _ ≤ |(NumberField.discr K : ℝ)| := minkowski_discr_exponential_lower_bound K hd1

/-- **Discriminant Divergence `|disc(K)| → ∞` as `[K : ℚ] → ∞`**:
for every bound `M : ℝ`, there exists `D : ℕ` such that every number field `K` of degree
`finrank ℚ K ≥ D` has `M ≤ |NumberField.discr K|`. -/
theorem minkowski_discr_tendsto_infinity (M : ℝ) :
    ∃ D : ℕ, ∀ (K : Type) [Field K] [NumberField K],
      D ≤ Module.finrank ℚ K → M ≤ |(NumberField.discr K : ℝ)| := by
  obtain ⟨D, hD⟩ := minkowski_discr_superlinear_growth (max M 0)
  refine ⟨max D 1, fun K _ _ hd => ?_⟩
  have hdD : D ≤ Module.finrank ℚ K := le_trans (le_max_left _ _) hd
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast le_trans (le_max_right _ _) hd
  calc M ≤ max M 0 := le_max_left M 0
    _ = max M 0 * 1 := (mul_one _).symm
    _ ≤ max M 0 * (Module.finrank ℚ K : ℝ) :=
        mul_le_mul_of_nonneg_left hd1 (le_max_right M 0)
    _ ≤ |(NumberField.discr K : ℝ)| := hD K hdD

/-- **Minkowski Lattice First-Minimum Bridge**: every number field `K` contains a nonzero
algebraic integer `a ∈ 𝓞 K` whose rational norm is bounded by the Minkowski constant times
the canonical lattice covolume `2^{r₂} · covol(𝓞 K) = √|disc(K)|`. -/
theorem minkowski_nonzero_int_norm_bound_covolume :
    ∃ a : 𝓞 K, a ≠ 0 ∧
      |(Algebra.norm ℚ (a : K) : ℝ)| ≤
        (8 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K).factorial : ℝ) /
          (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
          ZLattice.covolume (NumberField.mixedEmbedding.integerLattice K) MeasureTheory.volume := by
  obtain ⟨a, ha0, hnorm⟩ :=
    NumberField.exists_ne_zero_mem_ringOfIntegers_of_norm_le_mul_sqrt_discr K
  refine ⟨a, ha0, ?_⟩
  rw [integerLattice_covolume_eq K]
  have hrhs :
      (8 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K).factorial : ℝ) /
          (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
          (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|) =
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K).factorial : ℝ) /
          (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
          Real.sqrt |(NumberField.discr K : ℝ)| := by
    have hpow : (8 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K =
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K := by
      rw [← mul_pow]
      congr 1
      ring
    calc (8 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
            ((Module.finrank ℚ K).factorial : ℝ) /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
            (2⁻¹ ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)|)
        = ((8 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
            (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K) *
            ((Module.finrank ℚ K).factorial : ℝ) /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
            Real.sqrt |(NumberField.discr K : ℝ)| := by ring
      _ = (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
            ((Module.finrank ℚ K).factorial : ℝ) /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
            Real.sqrt |(NumberField.discr K : ℝ)| := by rw [hpow]
  rw [hrhs]
  simpa only [Rat.cast_abs] using hnorm

/-- **Hermite's Finiteness Theorem** (direct consequence of Minkowski's discriminant bound):
inside any characteristic-zero ambient field `A`, there are only finitely many number fields
of bounded absolute discriminant `|disc(K)| ≤ N`. -/
theorem hermite_finite_numberFields_of_discr_bdd (A : Type*) [Field A] [CharZero A] (N : ℕ) :
    {K : {F : IntermediateField ℚ A // NumberField F} |
      have := K.2; |NumberField.discr K.1| ≤ N}.Finite := by
  have h := NumberField.finite_of_discr_bdd A N
  let f : {F : IntermediateField ℚ A // NumberField F} →
      {F : IntermediateField ℚ A // FiniteDimensional ℚ F} :=
    fun K => ⟨K.1, K.2.to_finiteDimensional⟩
  have hpre : {K : {F : IntermediateField ℚ A // NumberField F} |
      have := K.2; |NumberField.discr K.1| ≤ N} =
      f ⁻¹' {K : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} |
        have := K.2; have : NumberField K.1 := ⟨⟩; |NumberField.discr K.1| ≤ N} := by
    ext K
    rfl
  rw [hpre]
  exact h.preimage fun x _ y _ hxy =>
    Subtype.ext (congrArg (Subtype.val : {F : IntermediateField ℚ A // FiniteDimensional ℚ F} → _) hxy)

end MinkowskiDiscriminant

/-! ## Section 5: Unified Unconditional Stage 7 Dedekind Zeta & Minkowski Summary -/

/-- **Unified Unconditional Stage 7 Master Theorem (`0` Assumptions)**:
packages:
1. Exact prime-ideal splitting multiplicity bound `Nat.card (PrimesAbove K p) ≤ finrank ℚ K`,
   prime-power ideal counting bound `idealCount K (p^k) ≤ (k + 1)^(finrank ℚ K)`,
   and `(riemannZeta σ)^d` domination of `∑'_{I ≠ ⊥} (Ideal.absNorm I)^(-σ)` for `σ > 1`;
2. Exact unconditional Dedekind zeta Euler product
   `dedekindZeta K s = ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ)^(-s))⁻¹`,
   nonvanishing `dedekindZeta K s ≠ 0` on `1 < s.re`, and `dedekindZeta ℚ s = riemannZeta s`;
3. Exact global unramified cyclotomic factorization
   `∏' v : {v // ¬ (N(v).minFac ∣ m)}, (1 - N(v)^(-s))⁻¹ = ∏ χ : DirichletCharacter ℂ m, L(s, χ)`;
4. Sharp Minkowski discriminant lower bound `((π / 4)^r₂ * (d^d / d!))^2 ≤ |discr K|`,
   Minkowski's Theorem (`1 < finrank ℚ K → 1 < |discr K|`), existence of a ramified prime,
   and super-linear discriminant growth `|discr K| / d → ∞`. -/
theorem stage7_dedekindZeta_unconditional :
    (∀ (K : Type) [Field K] [NumberField K] (p : ℕ), p.Prime →
      Nat.card (PrimesAbove K p) ≤ Module.finrank ℚ K ∧
      (∀ k : ℕ, idealCount K (p ^ k) ≤ (k + 1) ^ Module.finrank ℚ K)) ∧
    (∀ (K : Type) [Field K] [NumberField K] (σ : ℝ), 1 < σ →
      Summable (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥} => (Ideal.absNorm I.1 : ℝ) ^ (-σ)) ∧
      (∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, (Ideal.absNorm I.1 : ℝ) ^ (-σ)) ≤
        ((riemannZeta (σ : ℂ)).re) ^ Module.finrank ℚ K) ∧
    (∀ (K : Type) [Field K] [NumberField K] (s : ℂ), 1 < s.re →
      dedekindZeta K s =
        ∏' v : HeightOneSpectrum (𝓞 K), (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ ∧
      dedekindZeta K s ≠ 0) ∧
    (∀ (s : ℂ), 1 < s.re → dedekindZeta ℚ s = riemannZeta s) ∧
    (∀ (m : ℕ) [NeZero m] (s : ℂ), 1 < s.re →
      (∏' v : {v : HeightOneSpectrum (𝓞 (Stage4ClassFieldTheory.CycField m)) //
          ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ m)},
          (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) =
        ∏ χ : DirichletCharacter ℂ m, DirichletCharacter.LFunction χ s) ∧
    (∀ (K : Type) [Field K] [NumberField K],
      ((Real.pi / 4) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K /
            ((Module.finrank ℚ K).factorial : ℝ))) ^ 2 ≤
        |(NumberField.discr K : ℝ)| ∧
      (1 < Module.finrank ℚ K →
        1 < |NumberField.discr K| ∧
        ∃ p : ℕ, p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}))) ∧
    (∀ C : ℝ, ∃ D : ℕ, ∀ (K : Type) [Field K] [NumberField K],
      D ≤ Module.finrank ℚ K → C * (Module.finrank ℚ K : ℝ) ≤ |(NumberField.discr K : ℝ)|) :=
  ⟨fun K _ _ _ hp => ⟨card_primesAbove_le_finrank K hp, fun k => idealCount_prime_pow_le K hp k⟩,
   fun K _ _ _ hσ => summable_and_tsum_absNorm_rpow_le K hσ,
   fun K _ _ _ hs => ⟨dedekindZeta_eq_tprod_eulerProduct K hs, dedekindZeta_ne_zero K hs⟩,
   fun _ hs => dedekindZeta_rat_eq_riemannZeta hs,
   fun m _ _ hs => cyc_unramified_tprod_eq_prod_dirichletLFunction m hs,
   fun K _ _ =>
     ⟨minkowski_discr_lower_bound K,
      fun hK => ⟨minkowski_abs_discr_gt_one K hK, minkowski_exists_ramified_prime K hK⟩⟩,
   fun C => minkowski_discr_superlinear_growth C⟩

end RHDirect.Stage7DedekindZeta

end
