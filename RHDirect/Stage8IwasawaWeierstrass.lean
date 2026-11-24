import RHDirect.Stage7PadicLFunction
import RHDirect.Stage2IwasawaTwoTower
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# RHDirect.Stage8IwasawaWeierstrass

Unconditional Lean 4 formalization (zero `sorry`, zero custom `axiom`s) of:

1. **Concrete Weierstrass Division & Preparation Theorem in `ℤ_[p][[T]]` (`PowerSeries ℤ_[p]`)**:
   - Distinguished polynomials `IsDistinguishedPoly`, `p`-adic content `iwasawaMu`, primitive part
     `primitivePart`, and Weierstrass degree `iwasawaLambda`.
   - Additivity `iwasawaMu_mul` and `iwasawaLambda_mul`.
   - **Unconditional Weierstrass Division Theorem (`weierstrass_division_Zp`)**: unique `q ∈ ℤ_[p][[T]]`
     and `r ∈ ℤ_[p][T]` (`r = 0 ∨ r.natDegree < iwasawaLambda g`) with `f = g * q + r.toPowerSeries`
     for every `g ≠ 0` with `iwasawaMu g = 0`.
   - **Unconditional Weierstrass Preparation Theorem (`weierstrass_preparation_Zp`)**: every nonzero
     `f ∈ ℤ_[p][[T]]` factors uniquely as `f = p^μ * P.toPowerSeries * u` with `μ = iwasawaMu f`,
     `P` distinguished of degree `λ = iwasawaLambda f`, and `u` a unit in `ℤ_[p][[T]]`.
   - Structure of `ℤ_[p][[T]]`: local ring (`isLocalRing_iwasawaAlg`), principal ideal canonical
     generators, Noetherianity (`isNoetherianRing_iwasawaAlg`), unique factorization domain
     (`uniqueFactorizationMonoid_iwasawaAlg`), and **Strassmann's Theorem (`iwasawa_eval_zeros_finite`)**:
     every nonzero `f ∈ ℤ_[p][[T]]` has at most `iwasawaLambda f` zeros in `{y : ℤ_[p] | ‖y‖ < 1}`.

2. **Concrete Kummer Regularity / Irregular-Prime Criterion on `kubotaLeopoldtSeries`**:
   - For odd prime `p`, even `2 ≤ i ≤ p - 3`, and `c` with `¬ p ∣ c` and `(c : ZMod p) ^ i ≠ 1`:
     `kubotaLeopoldtSeries p hp2 c hc (i - 1)` is a unit in `ℤ_[p][[T]]` (equivalently `μ = 0 ∧ λ = 0`)
     IFF `¬ (p : ℤ_[p]) ∣ (B_i / i)` IFF `¬ (p : ℤ) ∣ (bernoulli i).num`
     (`kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli`).
   - Full regularity equivalence `regular_prime_iff_all_branches_unit`.
   - Exact computation of even Bernoulli numbers `B_2, B_4, ..., B_32`, proving explicitly that
     `p = 3, 5, 7, 11, 13` are regular primes (`regular_prime_3`, `regular_prime_5`,
     `regular_prime_7`, `regular_prime_11`, `regular_prime_13`) with unit Kubota–Leopoldt series
     (`μ = 0, λ = 0`), and exhibiting the exact `p = 37` irregular-prime witness
     `37 ∣ num(B_32)` (`irregular_prime_37_bernoulli32`, giving `iwasawaMu ≥ 1 ∨ iwasawaLambda ≥ 1`
     on the `i = 32` branch of `kubotaLeopoldtSeries 37`).
-/

noncomputable section

open scoped BigOperators Topology
open Finset Filter Topology RHDirect.Stage2IwasawaTwoTower RHDirect.Stage7PadicLFunction

namespace RHDirect.Stage8IwasawaWeierstrass

/-! ## Section 1: Distinguished Polynomials, `iwasawaMu`, `iwasawaLambda`, & Additivity -/

section IwasawaInvariants

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

lemma padicInt_p_ne_zero : (p : ℤ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

lemma padicInt_p_dvd_iff_toZMod_eq_zero (x : ℤ_[p]) :
    (p : ℤ_[p]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← Ideal.mem_span_singleton, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker]

lemma padicInt_isUnit_iff_not_p_dvd (x : ℤ_[p]) :
    IsUnit x ↔ ¬ (p : ℤ_[p]) ∣ x := by
  rw [← IsLocalRing.notMem_maximalIdeal, padicInt_maximalIdeal_eq_span_p, Ideal.mem_span_singleton]

lemma padicInt_p_not_isUnit : ¬ IsUnit (p : ℤ_[p]) := by
  rw [padicInt_isUnit_iff_not_p_dvd]
  exact not_not.mpr dvd_rfl

lemma padicInt_not_p_pow_succ_valuation_dvd {x : ℤ_[p]} (hx : x ≠ 0) :
    ¬ (p : ℤ_[p]) ^ (x.valuation + 1) ∣ x := by
  rintro ⟨c, hc⟩
  have hspec : x = (PadicInt.unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation :=
    PadicInt.unitCoeff_spec hx
  have hpv : (p : ℤ_[p]) ^ x.valuation ≠ 0 := pow_ne_zero _ padicInt_p_ne_zero
  have heq : (p : ℤ_[p]) ^ x.valuation * (PadicInt.unitCoeff hx : ℤ_[p]) =
      (p : ℤ_[p]) ^ x.valuation * ((p : ℤ_[p]) * c) := by
    calc (p : ℤ_[p]) ^ x.valuation * (PadicInt.unitCoeff hx : ℤ_[p])
        = x := by rw [mul_comm, ← hspec]
      _ = (p : ℤ_[p]) ^ (x.valuation + 1) * c := hc
      _ = (p : ℤ_[p]) ^ x.valuation * ((p : ℤ_[p]) * c) := by rw [pow_succ, mul_assoc]
  have hu : (PadicInt.unitCoeff hx : ℤ_[p]) = (p : ℤ_[p]) * c := mul_left_cancel₀ hpv heq
  exact (padicInt_isUnit_iff_not_p_dvd _).mp (PadicInt.unitCoeff hx).isUnit ⟨c, hu⟩

lemma padicInt_p_pow_dvd_iff_norm_le (x : ℤ_[p]) (m : ℕ) :
    (p : ℤ_[p]) ^ m ∣ x ↔ ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]

lemma padicInt_norm_lt_one_iff_p_dvd (x : ℤ_[p]) :
    ‖x‖ < 1 ↔ (p : ℤ_[p]) ∣ x := by
  rw [padicInt_p_dvd_iff_toZMod_eq_zero]
  constructor
  · intro hlt
    by_contra hne
    have hu : IsUnit x := padicInt_isUnit_of_toZMod_ne_zero hne
    have h1 : ‖x‖ = 1 := PadicInt.isUnit_iff.mp hu
    linarith
  · intro h0
    have hdvd : (p : ℤ_[p]) ^ 1 ∣ x := by
      rw [pow_one, padicInt_p_dvd_iff_toZMod_eq_zero]; exact h0
    have hle : ‖x‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := (padicInt_p_pow_dvd_iff_norm_le x 1).mp hdvd
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hinv : (p : ℝ) ^ (-(1 : ℤ)) < 1 := by
      rw [zpow_neg_one]; exact inv_lt_one_of_one_lt₀ hp1
    exact hle.trans_lt hinv

lemma padicInt_norm_eq_one_iff_not_p_dvd (x : ℤ_[p]) :
    ‖x‖ = 1 ↔ ¬ (p : ℤ_[p]) ∣ x := by
  rw [← PadicInt.isUnit_iff, padicInt_isUnit_iff_not_p_dvd]

lemma padicInt_p_pow_dvd_of_le {x : ℤ_[p]} {m n : ℕ} (h : m ≤ n)
    (hdvd : (p : ℤ_[p]) ^ n ∣ x) : (p : ℤ_[p]) ^ m ∣ x :=
  (pow_dvd_pow (p : ℤ_[p]) h).trans hdvd

lemma padicInt_p_pow_dvd_iff_p_dvd_quot {x y : ℤ_[p]} {m : ℕ}
    (hxy : x = (p : ℤ_[p]) ^ m * y) :
    (p : ℤ_[p]) ^ (m + 1) ∣ x ↔ (p : ℤ_[p]) ∣ y := by
  rw [hxy, pow_succ]
  have hpv : (p : ℤ_[p]) ^ m ≠ 0 := pow_ne_zero _ padicInt_p_ne_zero
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, mul_left_cancel₀ hpv ?_⟩
    calc (p : ℤ_[p]) ^ m * y = (p : ℤ_[p]) ^ m * (p : ℤ_[p]) * c := hc
      _ = (p : ℤ_[p]) ^ m * ((p : ℤ_[p]) * c) := by ring
  · rintro ⟨c, rfl⟩
    exact ⟨c, by ring⟩

/-! ### Polynomial-to-PowerSeries Helpers -/

lemma toPowerSeries_coeff (P : Polynomial ℤ_[p]) (k : ℕ) :
    PowerSeries.coeff k P.toPowerSeries = P.coeff k :=
  Polynomial.coeff_coe P k

lemma toPowerSeries_zero : (0 : Polynomial ℤ_[p]).toPowerSeries = 0 :=
  Polynomial.coe_zero

lemma toPowerSeries_one : (1 : Polynomial ℤ_[p]).toPowerSeries = 1 :=
  Polynomial.coe_one

lemma toPowerSeries_C (a : ℤ_[p]) : (Polynomial.C a).toPowerSeries = PowerSeries.C a :=
  Polynomial.coe_C a

lemma toPowerSeries_X : (Polynomial.X : Polynomial ℤ_[p]).toPowerSeries = PowerSeries.X :=
  Polynomial.coe_X

lemma toPowerSeries_X_pow (n : ℕ) :
    ((Polynomial.X : Polynomial ℤ_[p]) ^ n).toPowerSeries = PowerSeries.X ^ n := by
  rw [Polynomial.coe_pow, Polynomial.coe_X]

lemma toPowerSeries_add (P Q : Polynomial ℤ_[p]) :
    (P + Q).toPowerSeries = P.toPowerSeries + Q.toPowerSeries :=
  Polynomial.coe_add P Q

lemma toPowerSeries_sub (P Q : Polynomial ℤ_[p]) :
    (P - Q).toPowerSeries = P.toPowerSeries - Q.toPowerSeries :=
  Polynomial.coe_sub P Q

lemma toPowerSeries_mul (P Q : Polynomial ℤ_[p]) :
    (P * Q).toPowerSeries = P.toPowerSeries * Q.toPowerSeries :=
  Polynomial.coe_mul P Q

lemma toPowerSeries_injective : Function.Injective (Polynomial.toPowerSeries (R := ℤ_[p])) := by
  intro P Q h
  ext k
  have hk := congrArg (PowerSeries.coeff k) h
  simpa [toPowerSeries_coeff] using hk

lemma poly_deg_lt_iff_coeff_eq_zero (r : Polynomial ℤ_[p]) (d : ℕ) :
    (r = 0 ∨ r.natDegree < d) ↔ ∀ k : ℕ, d ≤ k → r.coeff k = 0 := by
  constructor
  · rintro (rfl | hlt) k hk
    · simp
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hlt hk)
  · intro h
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      by_contra hge
      push Not at hge
      have hlc : r.coeff r.natDegree = 0 := h r.natDegree hge
      exact Polynomial.leadingCoeff_ne_zero.mpr hr hlc

/-! ### Distinguished Polynomials -/

/-- A polynomial `P ∈ ℤ_[p][T]` is **distinguished** (Weierstrass polynomial) if it is monic and
every lower coefficient (`k < P.natDegree`) is divisible by `p`. -/
def IsDistinguishedPoly (P : Polynomial ℤ_[p]) : Prop :=
  P.Monic ∧ ∀ k < P.natDegree, (p : ℤ_[p]) ∣ P.coeff k

lemma IsDistinguishedPoly.ne_zero {P : Polynomial ℤ_[p]} (hP : IsDistinguishedPoly P) :
    P ≠ 0 := hP.1.ne_zero

lemma IsDistinguishedPoly.one : IsDistinguishedPoly (p := p) (1 : Polynomial ℤ_[p]) := by
  refine ⟨Polynomial.monic_one, fun k hk => ?_⟩
  simp at hk

lemma IsDistinguishedPoly.X : IsDistinguishedPoly (p := p) (Polynomial.X : Polynomial ℤ_[p]) := by
  refine ⟨Polynomial.monic_X, fun k hk => ?_⟩
  rw [Polynomial.natDegree_X] at hk
  obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
  simp

lemma IsDistinguishedPoly.mul {P Q : Polynomial ℤ_[p]}
    (hP : IsDistinguishedPoly P) (hQ : IsDistinguishedPoly Q) :
    IsDistinguishedPoly (P * Q) := by
  refine ⟨hP.1.mul hQ.1, fun k hk => ?_⟩
  rw [hP.1.natDegree_mul hQ.1] at hk
  rw [Polynomial.coeff_mul]
  refine Finset.dvd_sum fun ab hab => ?_
  have hab_eq : ab.1 + ab.2 = k := Finset.mem_antidiagonal.mp hab
  by_cases ha : ab.1 < P.natDegree
  · exact dvd_mul_of_dvd_left (hP.2 ab.1 ha) _
  · have hb : ab.2 < Q.natDegree := by omega
    exact dvd_mul_of_dvd_right (hQ.2 ab.2 hb) _

/-! ### `p`-adic Content `iwasawaMu` & Primitive Part `primitivePart` -/

lemma natCast_p_pow_powerSeries (m : ℕ) :
    ((p : PowerSeries ℤ_[p]) ^ m) = PowerSeries.C ((p : ℤ_[p]) ^ m) := by
  rw [← map_natCast (PowerSeries.C (R := ℤ_[p])), ← map_pow]

lemma coeff_p_pow_mul (m : ℕ) (f : PowerSeries ℤ_[p]) (k : ℕ) :
    PowerSeries.coeff k ((p : PowerSeries ℤ_[p]) ^ m * f) =
      (p : ℤ_[p]) ^ m * PowerSeries.coeff k f := by
  rw [natCast_p_pow_powerSeries, PowerSeries.coeff_C_mul]

lemma p_pow_mul_right_cancel {m : ℕ} {f g : PowerSeries ℤ_[p]}
    (h : (p : PowerSeries ℤ_[p]) ^ m * f = (p : PowerSeries ℤ_[p]) ^ m * g) : f = g := by
  ext k
  have hk := congrArg (PowerSeries.coeff k) h
  rw [coeff_p_pow_mul, coeff_p_pow_mul] at hk
  exact mul_left_cancel₀ (pow_ne_zero m padicInt_p_ne_zero) hk

private lemma exists_not_p_pow_succ_dvd_coeff {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ m : ℕ, ∃ k : ℕ, ¬ (p : ℤ_[p]) ^ (m + 1) ∣ PowerSeries.coeff k f := by
  have hk : ∃ k : ℕ, PowerSeries.coeff k f ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext k
    simpa using h k
  obtain ⟨k, hkf⟩ := hk
  exact ⟨(PowerSeries.coeff k f).valuation, k, padicInt_not_p_pow_succ_valuation_dvd hkf⟩

/-- The Iwasawa `μ`-invariant (`p`-adic content) of `f ∈ ℤ_[p][[T]]`: for `f ≠ 0`, the largest
`μ : ℕ` such that `p^μ ∣ f.coeff k` for all `k` (and `0` for `f = 0`). -/
def iwasawaMu (f : PowerSeries ℤ_[p]) : ℕ :=
  if hf : f ≠ 0 then Nat.find (exists_not_p_pow_succ_dvd_coeff hf) else 0

lemma iwasawaMu_zero : iwasawaMu (0 : PowerSeries ℤ_[p]) = 0 := by
  simp [iwasawaMu]

theorem p_pow_iwasawaMu_dvd_coeff (f : PowerSeries ℤ_[p]) (k : ℕ) :
    (p : ℤ_[p]) ^ iwasawaMu f ∣ PowerSeries.coeff k f := by
  by_cases hf : f ≠ 0
  · unfold iwasawaMu
    rw [dif_pos hf]
    generalize_proofs hne
    cases hμ : Nat.find hne with
    | zero =>
      rw [pow_zero]
      exact one_dvd _
    | succ m =>
      have hlt : m < Nat.find hne := by omega
      have hnot := Nat.find_min hne hlt
      push Not at hnot
      exact hnot k
  · push Not at hf
    rw [hf, iwasawaMu_zero, pow_zero, map_zero]
    exact dvd_zero _

theorem exists_not_p_pow_succ_iwasawaMu_dvd_coeff {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ k : ℕ, ¬ (p : ℤ_[p]) ^ (iwasawaMu f + 1) ∣ PowerSeries.coeff k f := by
  unfold iwasawaMu
  rw [dif_pos hf]
  exact Nat.find_spec (exists_not_p_pow_succ_dvd_coeff hf)

theorem forall_p_pow_dvd_coeff_iff_le_iwasawaMu {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) (m : ℕ) :
    (∀ k : ℕ, (p : ℤ_[p]) ^ m ∣ PowerSeries.coeff k f) ↔ m ≤ iwasawaMu f := by
  constructor
  · intro hall
    by_contra hgt
    push Not at hgt
    obtain ⟨k, hk⟩ := exists_not_p_pow_succ_iwasawaMu_dvd_coeff hf
    exact hk (padicInt_p_pow_dvd_of_le (Nat.succ_le_of_lt hgt) (hall k))
  · intro hle k
    exact padicInt_p_pow_dvd_of_le hle (p_pow_iwasawaMu_dvd_coeff f k)

theorem iwasawaMu_eq_zero_iff {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    iwasawaMu f = 0 ↔ ∃ k : ℕ, ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff k f := by
  constructor
  · intro h0
    obtain ⟨k, hk⟩ := exists_not_p_pow_succ_iwasawaMu_dvd_coeff hf
    rw [h0, zero_add, pow_one] at hk
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    by_contra hne
    have hge : 1 ≤ iwasawaMu f := Nat.one_le_iff_ne_zero.mpr hne
    have hdvd := padicInt_p_pow_dvd_of_le hge (p_pow_iwasawaMu_dvd_coeff f k)
    rw [pow_one] at hdvd
    exact hk hdvd

/-- Reduction homomorphism `ℤ_[p][[T]] →+* (ZMod p)[[T]]`. -/
def reduceModP : PowerSeries ℤ_[p] →+* PowerSeries (ZMod p) :=
  PowerSeries.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p)

lemma coeff_reduceModP (f : PowerSeries ℤ_[p]) (k : ℕ) :
    PowerSeries.coeff k (reduceModP f) = PadicInt.toZMod (PowerSeries.coeff k f) :=
  PowerSeries.coeff_map _ k f

lemma reduceModP_eq_zero_iff (f : PowerSeries ℤ_[p]) :
    reduceModP f = 0 ↔ ∀ k : ℕ, (p : ℤ_[p]) ∣ PowerSeries.coeff k f := by
  constructor
  · intro h0 k
    rw [padicInt_p_dvd_iff_toZMod_eq_zero, ← coeff_reduceModP, h0, map_zero]
  · intro hall
    ext k
    rw [coeff_reduceModP, map_zero, ← padicInt_p_dvd_iff_toZMod_eq_zero]
    exact hall k

lemma reduceModP_ne_zero_iff (f : PowerSeries ℤ_[p]) :
    reduceModP f ≠ 0 ↔ ∃ k : ℕ, ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff k f := by
  rw [ne_eq, reduceModP_eq_zero_iff]
  push Not
  rfl

theorem iwasawaMu_eq_zero_iff_reduceModP_ne_zero {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    iwasawaMu f = 0 ↔ reduceModP f ≠ 0 := by
  rw [iwasawaMu_eq_zero_iff hf, reduceModP_ne_zero_iff]

/-- The primitive part `f / p^(iwasawaMu f) ∈ ℤ_[p][[T]]`. -/
def primitivePart (f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] :=
  PowerSeries.mk fun k => (p_pow_iwasawaMu_dvd_coeff f k).choose

theorem p_pow_iwasawaMu_mul_primitivePart (f : PowerSeries ℤ_[p]) :
    (p : PowerSeries ℤ_[p]) ^ iwasawaMu f * primitivePart f = f := by
  ext k
  rw [coeff_p_pow_mul, primitivePart, PowerSeries.coeff_mk]
  exact (p_pow_iwasawaMu_dvd_coeff f k).choose_spec.symm

lemma primitivePart_eq_self_of_iwasawaMu_zero {f : PowerSeries ℤ_[p]} (hμ : iwasawaMu f = 0) :
    primitivePart f = f := by
  have h := p_pow_iwasawaMu_mul_primitivePart f
  rwa [hμ, pow_zero, one_mul] at h

lemma primitivePart_ne_zero {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    primitivePart f ≠ 0 := by
  intro h0
  apply hf
  rw [← p_pow_iwasawaMu_mul_primitivePart f, h0, mul_zero]

lemma exists_not_p_dvd_coeff_primitivePart {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ k : ℕ, ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff k (primitivePart f) := by
  obtain ⟨k, hk⟩ := exists_not_p_pow_succ_iwasawaMu_dvd_coeff hf
  refine ⟨k, fun hdvd => hk ?_⟩
  have heq : PowerSeries.coeff k f =
      (p : ℤ_[p]) ^ iwasawaMu f * PowerSeries.coeff k (primitivePart f) := by
    conv_lhs => rw [← p_pow_iwasawaMu_mul_primitivePart f]
    rw [coeff_p_pow_mul]
  exact (padicInt_p_pow_dvd_iff_p_dvd_quot heq).mpr hdvd

lemma iwasawaMu_primitivePart (f : PowerSeries ℤ_[p]) :
    iwasawaMu (primitivePart f) = 0 := by
  by_cases hf : f ≠ 0
  · exact (iwasawaMu_eq_zero_iff (primitivePart_ne_zero hf)).mpr
      (exists_not_p_dvd_coeff_primitivePart hf)
  · push Not at hf
    have h0 : primitivePart (0 : PowerSeries ℤ_[p]) = 0 :=
      primitivePart_eq_self_of_iwasawaMu_zero iwasawaMu_zero
    rw [hf, h0, iwasawaMu_zero]

lemma reduceModP_primitivePart_ne_zero {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    reduceModP (primitivePart f) ≠ 0 :=
  (reduceModP_ne_zero_iff _).mpr (exists_not_p_dvd_coeff_primitivePart hf)

theorem iwasawaMu_p_pow_mul {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) (m : ℕ) :
    iwasawaMu ((p : PowerSeries ℤ_[p]) ^ m * f) = m + iwasawaMu f := by
  have hne : (p : PowerSeries ℤ_[p]) ^ m * f ≠ 0 := by
    intro h0
    apply hf
    exact p_pow_mul_right_cancel (m := m) (h0.trans (mul_zero _).symm)
  apply le_antisymm
  · by_contra hgt
    push Not at hgt
    obtain ⟨k, hk⟩ := exists_not_p_pow_succ_iwasawaMu_dvd_coeff hf
    have hdvd := padicInt_p_pow_dvd_of_le (Nat.succ_le_of_lt hgt)
      (p_pow_iwasawaMu_dvd_coeff ((p : PowerSeries ℤ_[p]) ^ m * f) k)
    rw [coeff_p_pow_mul] at hdvd
    have hpow : (p : ℤ_[p]) ^ (m + iwasawaMu f + 1) = (p : ℤ_[p]) ^ m * (p : ℤ_[p]) ^ (iwasawaMu f + 1) := by
      rw [add_assoc, pow_add]
    rw [hpow] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    apply hk
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero m padicInt_p_ne_zero) ?_⟩
    calc (p : ℤ_[p]) ^ m * PowerSeries.coeff k f
        = (p : ℤ_[p]) ^ m * (p : ℤ_[p]) ^ (iwasawaMu f + 1) * c := hc
      _ = (p : ℤ_[p]) ^ m * ((p : ℤ_[p]) ^ (iwasawaMu f + 1) * c) := by ring
  · rw [← forall_p_pow_dvd_coeff_iff_le_iwasawaMu hne]
    intro k
    rw [coeff_p_pow_mul, pow_add]
    exact mul_dvd_mul_left _ (p_pow_iwasawaMu_dvd_coeff f k)

/-! ### Weierstrass Degree `iwasawaLambda` -/

/-- The Iwasawa `λ`-invariant (Weierstrass degree) of `f ∈ ℤ_[p][[T]]`: for `f ≠ 0`, the smallest
`λ : ℕ` such that `¬ (p : ℤ_[p]) ∣ (primitivePart f).coeff λ` (and `0` for `f = 0`). -/
def iwasawaLambda (f : PowerSeries ℤ_[p]) : ℕ :=
  if hf : f ≠ 0 then Nat.find (exists_not_p_dvd_coeff_primitivePart hf) else 0

lemma iwasawaLambda_zero : iwasawaLambda (0 : PowerSeries ℤ_[p]) = 0 := by
  simp [iwasawaLambda]

theorem p_dvd_coeff_primitivePart_of_lt_iwasawaLambda {f : PowerSeries ℤ_[p]} (hf : f ≠ 0)
    {k : ℕ} (hk : k < iwasawaLambda f) :
    (p : ℤ_[p]) ∣ PowerSeries.coeff k (primitivePart f) := by
  unfold iwasawaLambda at hk
  rw [dif_pos hf] at hk
  have hnot := Nat.find_min (exists_not_p_dvd_coeff_primitivePart hf) hk
  exact not_not.mp hnot

theorem not_p_dvd_coeff_primitivePart_iwasawaLambda {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff (iwasawaLambda f) (primitivePart f) := by
  unfold iwasawaLambda
  rw [dif_pos hf]
  exact Nat.find_spec (exists_not_p_dvd_coeff_primitivePart hf)

theorem isUnit_coeff_primitivePart_iwasawaLambda {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    IsUnit (PowerSeries.coeff (iwasawaLambda f) (primitivePart f)) :=
  (padicInt_isUnit_iff_not_p_dvd _).mpr (not_p_dvd_coeff_primitivePart_iwasawaLambda hf)

theorem p_dvd_coeff_of_lt_iwasawaLambda {f : PowerSeries ℤ_[p]} (hf : f ≠ 0)
    (hμ : iwasawaMu f = 0) {k : ℕ} (hk : k < iwasawaLambda f) :
    (p : ℤ_[p]) ∣ PowerSeries.coeff k f := by
  have h := p_dvd_coeff_primitivePart_of_lt_iwasawaLambda hf hk
  rwa [primitivePart_eq_self_of_iwasawaMu_zero hμ] at h

theorem not_p_dvd_coeff_iwasawaLambda {f : PowerSeries ℤ_[p]} (hf : f ≠ 0)
    (hμ : iwasawaMu f = 0) :
    ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff (iwasawaLambda f) f := by
  have h := not_p_dvd_coeff_primitivePart_iwasawaLambda hf
  rwa [primitivePart_eq_self_of_iwasawaMu_zero hμ] at h

theorem iwasawaLambda_eq_of_primitive {f : PowerSeries ℤ_[p]} (hf : f ≠ 0)
    (hμ : iwasawaMu f = 0) {d : ℕ}
    (hlt : ∀ k < d, (p : ℤ_[p]) ∣ PowerSeries.coeff k f)
    (hd : ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff d f) :
    iwasawaLambda f = d := by
  apply le_antisymm
  · unfold iwasawaLambda
    rw [dif_pos hf]
    refine Nat.find_le ?_
    rwa [primitivePart_eq_self_of_iwasawaMu_zero hμ]
  · by_contra hlt'
    push Not at hlt'
    exact not_p_dvd_coeff_iwasawaLambda hf hμ (hlt _ hlt')

theorem iwasawaLambda_primitivePart (f : PowerSeries ℤ_[p]) :
    iwasawaLambda (primitivePart f) = iwasawaLambda f := by
  by_cases hf : f ≠ 0
  · refine iwasawaLambda_eq_of_primitive (primitivePart_ne_zero hf) (iwasawaMu_primitivePart f)
      (fun k hk => p_dvd_coeff_primitivePart_of_lt_iwasawaLambda hf hk)
      (not_p_dvd_coeff_primitivePart_iwasawaLambda hf)
  · push Not at hf
    have h0 : primitivePart (0 : PowerSeries ℤ_[p]) = 0 :=
      primitivePart_eq_self_of_iwasawaMu_zero iwasawaMu_zero
    rw [hf, h0]

theorem iwasawaMu_distinguished {P : Polynomial ℤ_[p]} (hP : IsDistinguishedPoly P) :
    iwasawaMu P.toPowerSeries = 0 := by
  have hne : P.toPowerSeries ≠ 0 := fun h0 =>
    hP.ne_zero (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
  rw [iwasawaMu_eq_zero_iff hne]
  refine ⟨P.natDegree, ?_⟩
  rw [toPowerSeries_coeff, ← Polynomial.leadingCoeff, hP.1.leadingCoeff, ← padicInt_isUnit_iff_not_p_dvd]
  exact isUnit_one

theorem iwasawaLambda_distinguished {P : Polynomial ℤ_[p]} (hP : IsDistinguishedPoly P) :
    iwasawaLambda P.toPowerSeries = P.natDegree := by
  have hne : P.toPowerSeries ≠ 0 := fun h0 =>
    hP.ne_zero (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
  refine iwasawaLambda_eq_of_primitive hne (iwasawaMu_distinguished hP) ?_ ?_
  · intro k hk
    rw [toPowerSeries_coeff]
    exact hP.2 k hk
  · rw [toPowerSeries_coeff, ← Polynomial.leadingCoeff, hP.1.leadingCoeff, ← padicInt_isUnit_iff_not_p_dvd]
    exact isUnit_one

theorem isUnit_iwasawaAlg_iff (f : PowerSeries ℤ_[p]) :
    IsUnit f ↔ ¬ (p : ℤ_[p]) ∣ PowerSeries.constantCoeff f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, padicInt_isUnit_iff_not_p_dvd]

theorem isUnit_iff_iwasawaMu_zero_and_iwasawaLambda_zero {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    IsUnit f ↔ iwasawaMu f = 0 ∧ iwasawaLambda f = 0 := by
  rw [isUnit_iwasawaAlg_iff]
  constructor
  · intro hndvd
    have hμ : iwasawaMu f = 0 := (iwasawaMu_eq_zero_iff hf).mpr ⟨0, by simpa using hndvd⟩
    have hlam : iwasawaLambda f = 0 :=
      iwasawaLambda_eq_of_primitive hf hμ (fun k hk => absurd hk (Nat.not_lt_zero k))
        (by simpa using hndvd)
    exact ⟨hμ, hlam⟩
  · rintro ⟨hμ, hlam⟩
    have h := not_p_dvd_coeff_iwasawaLambda hf hμ
    rw [hlam] at h
    simpa using h

theorem isUnit_iff_ne_zero_and_mu_lambda_zero (f : PowerSeries ℤ_[p]) :
    IsUnit f ↔ f ≠ 0 ∧ iwasawaMu f = 0 ∧ iwasawaLambda f = 0 := by
  constructor
  · intro hu
    have hf : f ≠ 0 := hu.ne_zero
    exact ⟨hf, (isUnit_iff_iwasawaMu_zero_and_iwasawaLambda_zero hf).mp hu⟩
  · rintro ⟨hf, hμ, hlam⟩
    exact (isUnit_iff_iwasawaMu_zero_and_iwasawaLambda_zero hf).mpr ⟨hμ, hlam⟩

theorem iwasawaMu_of_isUnit {u : PowerSeries ℤ_[p]} (hu : IsUnit u) : iwasawaMu u = 0 :=
  ((isUnit_iff_ne_zero_and_mu_lambda_zero u).mp hu).2.1

theorem iwasawaLambda_of_isUnit {u : PowerSeries ℤ_[p]} (hu : IsUnit u) : iwasawaLambda u = 0 :=
  ((isUnit_iff_ne_zero_and_mu_lambda_zero u).mp hu).2.2

theorem iwasawaMu_p_pow (m : ℕ) : iwasawaMu ((p : PowerSeries ℤ_[p]) ^ m) = m := by
  have h := iwasawaMu_p_pow_mul (p := p) (f := (1 : PowerSeries ℤ_[p])) one_ne_zero m
  rw [mul_one, iwasawaMu_of_isUnit isUnit_one, add_zero] at h
  exact h

theorem iwasawaLambda_p_pow (m : ℕ) : iwasawaLambda ((p : PowerSeries ℤ_[p]) ^ m) = 0 := by
  have hprim : primitivePart ((p : PowerSeries ℤ_[p]) ^ m) = 1 := by
    apply p_pow_mul_right_cancel (m := m)
    rw [mul_one]
    have h := p_pow_iwasawaMu_mul_primitivePart ((p : PowerSeries ℤ_[p]) ^ m)
    rwa [iwasawaMu_p_pow] at h
  rw [← iwasawaLambda_primitivePart, hprim]
  exact iwasawaLambda_of_isUnit isUnit_one

/-! ### Additivity of `iwasawaMu` and `iwasawaLambda` -/

theorem iwasawaMu_mul {f g : PowerSeries ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    iwasawaMu (f * g) = iwasawaMu f + iwasawaMu g := by
  have hrf : reduceModP (primitivePart f) ≠ 0 := reduceModP_primitivePart_ne_zero hf
  have hrg : reduceModP (primitivePart g) ≠ 0 := reduceModP_primitivePart_ne_zero hg
  have hrfg : reduceModP (primitivePart f * primitivePart g) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hrf hrg
  have hfg0_ne : primitivePart f * primitivePart g ≠ 0 := by
    intro h0; apply hrfg; rw [h0, map_zero]
  have hμ0 : iwasawaMu (primitivePart f * primitivePart g) = 0 :=
    (iwasawaMu_eq_zero_iff_reduceModP_ne_zero hfg0_ne).mpr hrfg
  have hprod : f * g = (p : PowerSeries ℤ_[p]) ^ (iwasawaMu f + iwasawaMu g) *
      (primitivePart f * primitivePart g) := by
    conv_lhs => rw [← p_pow_iwasawaMu_mul_primitivePart f, ← p_pow_iwasawaMu_mul_primitivePart g]
    rw [pow_add]
    ring
  rw [hprod, iwasawaMu_p_pow_mul hfg0_ne, hμ0, add_zero]

theorem primitivePart_mul {f g : PowerSeries ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    primitivePart (f * g) = primitivePart f * primitivePart g := by
  apply p_pow_mul_right_cancel (m := iwasawaMu f + iwasawaMu g)
  rw [← iwasawaMu_mul hf hg, p_pow_iwasawaMu_mul_primitivePart]
  conv_lhs => rw [← p_pow_iwasawaMu_mul_primitivePart f, ← p_pow_iwasawaMu_mul_primitivePart g]
  rw [iwasawaMu_mul hf hg, pow_add]
  ring

theorem iwasawaLambda_mul {f g : PowerSeries ℤ_[p]} (hf : f ≠ 0) (hg : g ≠ 0) :
    iwasawaLambda (f * g) = iwasawaLambda f + iwasawaLambda g := by
  rw [← iwasawaLambda_primitivePart (f * g), primitivePart_mul hf hg]
  set f₀ := primitivePart f
  set g₀ := primitivePart g
  have hf₀ : f₀ ≠ 0 := primitivePart_ne_zero hf
  have hg₀ : g₀ ≠ 0 := primitivePart_ne_zero hg
  have hfg₀ : f₀ * g₀ ≠ 0 := mul_ne_zero hf₀ hg₀
  have hμ_fg : iwasawaMu (f₀ * g₀) = 0 := by
    rw [iwasawaMu_mul hf₀ hg₀, iwasawaMu_primitivePart, iwasawaMu_primitivePart]
  refine iwasawaLambda_eq_of_primitive hfg₀ hμ_fg ?_ ?_
  · intro k hk
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun ab hab => ?_
    have hab_eq : ab.1 + ab.2 = k := Finset.mem_antidiagonal.mp hab
    by_cases ha : ab.1 < iwasawaLambda f
    · exact dvd_mul_of_dvd_left (p_dvd_coeff_primitivePart_of_lt_iwasawaLambda hf ha) _
    · have hb : ab.2 < iwasawaLambda g := by omega
      exact dvd_mul_of_dvd_right (p_dvd_coeff_primitivePart_of_lt_iwasawaLambda hg hb) _
  · rw [padicInt_p_dvd_iff_toZMod_eq_zero, ← coeff_reduceModP, map_mul, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (iwasawaLambda f, iwasawaLambda g)]
    · rw [coeff_reduceModP, coeff_reduceModP]
      have h1 : PadicInt.toZMod (PowerSeries.coeff (iwasawaLambda f) f₀) ≠ 0 := by
        rw [ne_eq, ← padicInt_p_dvd_iff_toZMod_eq_zero]
        exact not_p_dvd_coeff_primitivePart_iwasawaLambda hf
      have h2 : PadicInt.toZMod (PowerSeries.coeff (iwasawaLambda g) g₀) ≠ 0 := by
        rw [ne_eq, ← padicInt_p_dvd_iff_toZMod_eq_zero]
        exact not_p_dvd_coeff_primitivePart_iwasawaLambda hg
      exact mul_ne_zero h1 h2
    · intro ab hab hne
      have hab_eq : ab.1 + ab.2 = iwasawaLambda f + iwasawaLambda g := Finset.mem_antidiagonal.mp hab
      by_cases ha : ab.1 < iwasawaLambda f
      · rw [coeff_reduceModP, (padicInt_p_dvd_iff_toZMod_eq_zero _).mp
          (p_dvd_coeff_primitivePart_of_lt_iwasawaLambda hf ha), zero_mul]
      · have hb : ab.2 < iwasawaLambda g := by
          by_contra hge
          push Not at hge ha
          apply hne
          ext <;> omega
        rw [coeff_reduceModP (f := g₀), (padicInt_p_dvd_iff_toZMod_eq_zero _).mp
          (p_dvd_coeff_primitivePart_of_lt_iwasawaLambda hg hb), mul_zero]
    · intro hnot
      exact absurd (Finset.mem_antidiagonal.mpr
        (rfl : iwasawaLambda f + iwasawaLambda g = iwasawaLambda f + iwasawaLambda g)) hnot

end IwasawaInvariants

/-! ## Section 2: Unconditional Weierstrass Division & Preparation Theorem in `ℤ_[p][[T]]` -/

section WeierstrassDivisionAndPreparation

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Auxiliary decomposition of any primitive `g ∈ ℤ_[p][[T]]` (`iwasawaMu g = 0`, `d = iwasawaLambda g`):
there exist `h ∈ ℤ_[p][[T]]` and a unit `u ∈ (ℤ_[p][[T]])ˣ` such that
`g * (u⁻¹ : PowerSeries ℤ_[p]) = X ^ d + C p * h`. -/
lemma exists_unit_mul_eq_X_pow_add_p_mul {g : PowerSeries ℤ_[p]}
    (hg : g ≠ 0) (hμ : iwasawaMu g = 0) :
    ∃ (u : (PowerSeries ℤ_[p])ˣ) (h : PowerSeries ℤ_[p]),
      g * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) =
        PowerSeries.X ^ iwasawaLambda g + PowerSeries.C (p : ℤ_[p]) * h := by
  set d := iwasawaLambda g
  have hshift_unit : IsUnit (psShift d g) := by
    rw [isUnit_iwasawaAlg_iff]
    have hc : PowerSeries.constantCoeff (psShift d g) = PowerSeries.coeff d g := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff]
      simp [psShift]
    rw [hc]
    exact not_p_dvd_coeff_iwasawaLambda hg hμ
  set u : (PowerSeries ℤ_[p])ˣ := hshift_unit.unit
  have htrunc_dvd : ∀ k : ℕ, (p : ℤ_[p]) ∣ PowerSeries.coeff k (psTrunc d g) := by
    intro k
    unfold psTrunc
    rw [map_sum]
    refine Finset.dvd_sum fun i hi => ?_
    rw [PowerSeries.coeff_C_mul_X_pow]
    split_ifs with hik
    · exact p_dvd_coeff_of_lt_iwasawaLambda hg hμ (Finset.mem_range.mp hi)
    · exact dvd_zero _
  let h₀ : PowerSeries ℤ_[p] := PowerSeries.mk fun k => (htrunc_dvd k).choose
  have hh₀ : psTrunc d g = PowerSeries.C (p : ℤ_[p]) * h₀ := by
    ext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact (htrunc_dvd k).choose_spec
  refine ⟨u, h₀ * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]), ?_⟩
  have hsplit : g = PowerSeries.C (p : ℤ_[p]) * h₀ + PowerSeries.X ^ d * (u : PowerSeries ℤ_[p]) := by
    conv_lhs => rw [ps_eq_trunc_add_X_pow_mul_shift d g, hh₀]
    rfl
  calc g * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])
      = (PowerSeries.C (p : ℤ_[p]) * h₀ + PowerSeries.X ^ d * (u : PowerSeries ℤ_[p])) *
          ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) := by rw [hsplit]
    _ = PowerSeries.X ^ d * ((u : PowerSeries ℤ_[p]) * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) +
          PowerSeries.C (p : ℤ_[p]) * (h₀ * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) := by ring
    _ = PowerSeries.X ^ d + PowerSeries.C (p : ℤ_[p]) * (h₀ * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) := by
          rw [Units.mul_inv, mul_one]

/-- Existence of Weierstrass division by `g' = X^d + C p * h'`. -/
private lemma weierstrass_division_special (d : ℕ) (f g' h' : PowerSeries ℤ_[p])
    (hg' : g' = PowerSeries.X ^ d + PowerSeries.C (p : ℤ_[p]) * h') :
    ∃ (q : PowerSeries ℤ_[p]) (r : Polynomial ℤ_[p]),
      (r = 0 ∨ r.natDegree < d) ∧ f = g' * q + r.toPowerSeries := by
  let step : ℕ → PowerSeries ℤ_[p] := Nat.rec f (fun _ G => -(h' * psShift d G))
  have hstep_succ : ∀ m, step (m + 1) = -(h' * psShift d (step m)) := fun _ => rfl
  have hstep_zero : step 0 = f := rfl
  have hp_lt1 : ‖(p : ℤ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hsum_coeff : ∀ (seq : ℕ → ℤ_[p]), Summable (fun m : ℕ => (p : ℤ_[p]) ^ m * seq m) := by
    intro seq
    have hnorm : Summable (fun m : ℕ => ‖(p : ℤ_[p]) ^ m * seq m‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
        (summable_geometric_of_lt_one (norm_nonneg _) hp_lt1)
      rw [norm_mul, norm_pow]
      calc ‖(p : ℤ_[p])‖ ^ m * ‖seq m‖ ≤ ‖(p : ℤ_[p])‖ ^ m * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) m)
        _ = ‖(p : ℤ_[p])‖ ^ m := mul_one _
    exact hnorm.of_norm
  let rCoeff : ℕ → ℤ_[p] := fun k => ∑' m : ℕ, (p : ℤ_[p]) ^ m * PowerSeries.coeff k (step m)
  let r : Polynomial ℤ_[p] := ∑ k ∈ Finset.range d, Polynomial.C (rCoeff k) * Polynomial.X ^ k
  let q : PowerSeries ℤ_[p] := PowerSeries.mk fun k =>
    ∑' m : ℕ, (p : ℤ_[p]) ^ m * PowerSeries.coeff k (psShift d (step m))
  have hr_coeff : ∀ k : ℕ, r.coeff k = if k < d then rCoeff k else 0 := by
    intro k
    dsimp only [r]
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    by_cases hk : k < d
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro i _ hi; simp [hi.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hne : i ≠ k := ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) (not_lt.mp hk))
      simp [hne.symm]
  have hr_deg : r = 0 ∨ r.natDegree < d := by
    rw [poly_deg_lt_iff_coeff_eq_zero]
    intro k hk
    rw [hr_coeff k, if_neg (not_lt.mpr hk)]
  refine ⟨q, r, hr_deg, ?_⟩
  have hpart : ∀ M : ℕ,
      f = (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) +
          g' * (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) +
          PowerSeries.C ((p : ℤ_[p]) ^ M) * step M := by
    intro M
    induction M with
    | zero => simp [hstep_zero]
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      have hsplitM : step M = psTrunc d (step M) + g' * psShift d (step M) +
          PowerSeries.C (p : ℤ_[p]) * step (M + 1) := by
        rw [hstep_succ, hg']
        conv_lhs => rw [ps_eq_trunc_add_X_pow_mul_shift d (step M)]
        ring
      conv_lhs => rw [ih, hsplitM]
      rw [pow_succ, map_mul]
      ring
  ext k
  refine padicInt_eq_of_forall_norm_le_pow fun M => ?_
  have hM := congrArg (PowerSeries.coeff k) (hpart M)
  rw [hM]
  have htail_bd : ∀ (seq : ℕ → ℤ_[p]),
      ‖(∑' m : ℕ, (p : ℤ_[p]) ^ m * seq m) - ∑ m ∈ Finset.range M, (p : ℤ_[p]) ^ m * seq m‖ ≤
        (p : ℝ) ^ (-(M : ℤ)) := by
    intro seq
    have hs := hsum_coeff seq
    have hsp : (∑' m : ℕ, (p : ℤ_[p]) ^ m * seq m) - ∑ m ∈ Finset.range M, (p : ℤ_[p]) ^ m * seq m =
        ∑' m : ℕ, (p : ℤ_[p]) ^ (m + M) * seq (m + M) := by
      rw [← hs.sum_add_tsum_nat_add M]; ring
    rw [hsp]
    have hs' := (summable_nat_add_iff M).mpr hs
    have hlim : Tendsto (fun N => ‖∑ m ∈ Finset.range N, (p : ℤ_[p]) ^ (m + M) * seq (m + M)‖)
        atTop (nhds ‖∑' m : ℕ, (p : ℤ_[p]) ^ (m + M) * seq (m + M)‖) :=
      hs'.hasSum.tendsto_sum_nat.norm
    refine le_of_tendsto' hlim fun N => ?_
    refine padicInt_norm_sum_le _ _ (by positivity) fun m _ => ?_
    rw [pow_add, mul_assoc, norm_mul, norm_pow]
    have hnp : ‖(p : ℤ_[p])‖ ^ M = (p : ℝ) ^ (-(M : ℤ)) := by
      change ‖(p : ℚ_[p])‖ ^ M = _
      rw [Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
    rw [norm_mul, norm_pow, hnp]
    calc ‖(p : ℤ_[p])‖ ^ m * ((p : ℝ) ^ (-(M : ℤ)) * ‖seq (m + M)‖)
        ≤ 1 * ((p : ℝ) ^ (-(M : ℤ)) * 1) :=
          mul_le_mul (pow_le_one₀ (norm_nonneg _) hp_lt1.le)
            (mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity))
            (by positivity) zero_le_one
      _ = (p : ℝ) ^ (-(M : ℤ)) := by ring
  have hR_part : PowerSeries.coeff k
      (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) =
      if k < d then ∑ m ∈ Finset.range M, (p : ℤ_[p]) ^ m * PowerSeries.coeff k (step m) else 0 := by
    rw [map_sum]
    by_cases hk : k < d
    · rw [if_pos hk]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [PowerSeries.coeff_C_mul]
      congr 1
      unfold psTrunc
      rw [map_sum]
      simp_rw [PowerSeries.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hi; simp [hi.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [PowerSeries.coeff_C_mul]
      have hz : PowerSeries.coeff k (psTrunc d (step m)) = 0 := by
        unfold psTrunc
        rw [map_sum]
        simp_rw [PowerSeries.coeff_C_mul_X_pow]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hne : i ≠ k := ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) (not_lt.mp hk))
        simp [hne.symm]
      rw [hz, mul_zero]
  have hQ_coeff : ∀ j : ℕ,
      ‖PowerSeries.coeff j (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
        PowerSeries.coeff j q‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    intro j
    rw [map_sum]
    simp_rw [PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_mk, ← norm_neg, neg_sub]
    exact htail_bd (fun m => PowerSeries.coeff j (psShift d (step m)))
  simp only [map_add]
  have hdiff_split :
      (PowerSeries.coeff k (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) +
        PowerSeries.coeff k (g' * ∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) +
        PowerSeries.coeff k (PowerSeries.C ((p : ℤ_[p]) ^ M) * step M)) -
      (PowerSeries.coeff k (g' * q) + PowerSeries.coeff k r.toPowerSeries) =
      (PowerSeries.coeff k (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) -
        PowerSeries.coeff k r.toPowerSeries) +
      (PowerSeries.coeff k (g' * ∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
        PowerSeries.coeff k (g' * q)) +
      PowerSeries.coeff k (PowerSeries.C ((p : ℤ_[p]) ^ M) * step M) := by ring
  rw [hdiff_split]
  have hbd1 : ‖PowerSeries.coeff k (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) -
      PowerSeries.coeff k r.toPowerSeries‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    rw [hR_part, toPowerSeries_coeff, hr_coeff]
    by_cases hk : k < d
    · rw [if_pos hk, if_pos hk, ← norm_neg, neg_sub]
      exact htail_bd (fun m => PowerSeries.coeff k (step m))
    · rw [if_neg hk, if_neg hk, sub_self, norm_zero]
      positivity
  have hbd2 : ‖PowerSeries.coeff k (g' * ∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
      PowerSeries.coeff k (g' * q)‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    rw [← map_sub, ← mul_sub, PowerSeries.coeff_mul]
    refine padicInt_norm_sum_le _ _ (by positivity) fun ab _ => ?_
    rw [norm_mul, map_sub]
    calc ‖PowerSeries.coeff ab.1 g'‖ *
          ‖PowerSeries.coeff ab.2 (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
            PowerSeries.coeff ab.2 q‖
        ≤ 1 * (p : ℝ) ^ (-(M : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one _) (hQ_coeff ab.2) (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-(M : ℤ)) := one_mul _
  have hbd3 : ‖PowerSeries.coeff k (PowerSeries.C ((p : ℤ_[p]) ^ M) * step M)‖ ≤
      (p : ℝ) ^ (-(M : ℤ)) := by
    rw [PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    have hnp : ‖(p : ℤ_[p])‖ ^ M = (p : ℝ) ^ (-(M : ℤ)) := by
      change ‖(p : ℚ_[p])‖ ^ M = _
      rw [Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
    rw [hnp]
    calc (p : ℝ) ^ (-(M : ℤ)) * ‖PowerSeries.coeff k (step M)‖
        ≤ (p : ℝ) ^ (-(M : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
      _ = (p : ℝ) ^ (-(M : ℤ)) := mul_one _
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hbd3)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbd1 hbd2)

/-- Uniqueness core for Weierstrass division: if `g * q = r.toPowerSeries` with `iwasawaMu g = 0`
and `r = 0 ∨ r.natDegree < iwasawaLambda g`, then `q = 0` and `r = 0`. -/
lemma weierstrass_division_eq_zero {g q : PowerSeries ℤ_[p]} {r : Polynomial ℤ_[p]}
    (hg : g ≠ 0)
    (hr : r = 0 ∨ r.natDegree < iwasawaLambda g)
    (heq : g * q = r.toPowerSeries) : q = 0 ∧ r = 0 := by
  have hq0 : q = 0 := by
    by_contra hq
    have hcoeff_r : ∀ k, iwasawaLambda g ≤ k → r.coeff k = 0 :=
      (poly_deg_lt_iff_coeff_eq_zero r (iwasawaLambda g)).mp hr
    have hprod_ne : g * q ≠ 0 := mul_ne_zero hg hq
    have hlam_prod : iwasawaLambda (g * q) = iwasawaLambda g + iwasawaLambda q :=
      iwasawaLambda_mul hg hq
    set k := iwasawaLambda (g * q)
    have hk_ge : iwasawaLambda g ≤ k := by rw [hlam_prod]; exact Nat.le_add_right _ _
    have hrk : PowerSeries.coeff k (g * q) = 0 := by
      rw [heq, toPowerSeries_coeff, hcoeff_r k hk_ge]
    have hnot : ¬ (p : ℤ_[p]) ∣ PowerSeries.coeff k (primitivePart (g * q)) :=
      not_p_dvd_coeff_primitivePart_iwasawaLambda hprod_ne
    have hmul0 : (p : ℤ_[p]) ^ iwasawaMu (g * q) * PowerSeries.coeff k (primitivePart (g * q)) = 0 := by
      rw [← coeff_p_pow_mul, p_pow_iwasawaMu_mul_primitivePart, hrk]
    have hprim0 : PowerSeries.coeff k (primitivePart (g * q)) = 0 :=
      (mul_eq_zero.mp hmul0).resolve_left (pow_ne_zero _ padicInt_p_ne_zero)
    exact hnot (hprim0 ▸ dvd_zero _)
  refine ⟨hq0, ?_⟩
  rw [hq0, mul_zero] at heq
  exact toPowerSeries_injective (heq.symm.trans toPowerSeries_zero.symm)

/-- **UNCONDITIONAL WEIERSTRASS DIVISION THEOREM IN `ℤ_[p][[T]]` (0 ASSUMPTIONS!)**:
for every `f, g ∈ ℤ_[p][[T]]` with `g ≠ 0` and `iwasawaMu g = 0`, there exist unique
`q ∈ ℤ_[p][[T]]` and `r ∈ ℤ_[p][T]` with `r = 0 ∨ r.natDegree < iwasawaLambda g` such that
`f = g * q + r.toPowerSeries`. -/
theorem weierstrass_division_Zp {f g : PowerSeries ℤ_[p]}
    (hg : g ≠ 0) (hμ : iwasawaMu g = 0) :
    ∃! qr : PowerSeries ℤ_[p] × Polynomial ℤ_[p],
      (qr.2 = 0 ∨ qr.2.natDegree < iwasawaLambda g) ∧
      f = g * qr.1 + qr.2.toPowerSeries := by
  obtain ⟨u, h', hg'⟩ := exists_unit_mul_eq_X_pow_add_p_mul hg hμ
  obtain ⟨q', r, hr_deg, hdiv⟩ :=
    weierstrass_division_special (iwasawaLambda g) f
      (g * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) h' hg'
  refine ⟨(((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) * q', r), ⟨hr_deg, ?_⟩, ?_⟩
  · calc f = g * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) * q' + r.toPowerSeries := hdiv
      _ = g * (((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) * q') + r.toPowerSeries := by ring
  · rintro ⟨q₂, r₂⟩ ⟨hr₂_deg, hdiv₂⟩
    have hsub : g * (q₂ - ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) * q') =
        (r - r₂).toPowerSeries := by
      rw [toPowerSeries_sub, mul_sub]
      have h1 : g * (((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) * q') + r.toPowerSeries = f := by
        rw [← mul_assoc, ← hdiv]
      have h2 : g * q₂ + r₂.toPowerSeries = f := hdiv₂.symm
      linear_combination h2 - h1
    have hdeg_sub : r - r₂ = 0 ∨ (r - r₂).natDegree < iwasawaLambda g := by
      rw [poly_deg_lt_iff_coeff_eq_zero]
      intro k hk
      rw [Polynomial.coeff_sub,
        (poly_deg_lt_iff_coeff_eq_zero r _).mp hr_deg k hk,
        (poly_deg_lt_iff_coeff_eq_zero r₂ _).mp hr₂_deg k hk, sub_zero]
    obtain ⟨hq_eq, hr_eq⟩ := weierstrass_division_eq_zero hg hdeg_sub hsub
    exact Prod.ext (sub_eq_zero.mp hq_eq) (sub_eq_zero.mp hr_eq).symm

/-- **UNCONDITIONAL WEIERSTRASS PREPARATION THEOREM IN `ℤ_[p][[T]]` (0 ASSUMPTIONS!)**:
every nonzero `f ∈ ℤ_[p][[T]]` factors uniquely as
`f = p^(iwasawaMu f) * P.toPowerSeries * u`
where `P ∈ ℤ_[p][T]` is distinguished of degree `iwasawaLambda f` and `u ∈ (ℤ_[p][[T]])ˣ` is a unit. -/
theorem weierstrass_preparation_Zp {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃! data : Polynomial ℤ_[p] × (PowerSeries ℤ_[p])ˣ,
      IsDistinguishedPoly data.1 ∧
      data.1.natDegree = iwasawaLambda f ∧
      f = (p : PowerSeries ℤ_[p]) ^ iwasawaMu f * data.1.toPowerSeries * (data.2 : PowerSeries ℤ_[p]) := by
  set μ := iwasawaMu f
  set f₀ := primitivePart f
  set d := iwasawaLambda f
  have hf₀ : f₀ ≠ 0 := primitivePart_ne_zero hf
  have hμ₀ : iwasawaMu f₀ = 0 := iwasawaMu_primitivePart f
  have hlam₀ : iwasawaLambda f₀ = d := iwasawaLambda_primitivePart f
  obtain ⟨⟨q, r⟩, ⟨hr_deg, hdiv⟩, _⟩ :=
    weierstrass_division_Zp (f := PowerSeries.X ^ d) (g := f₀) hf₀ hμ₀
  rw [hlam₀] at hr_deg
  have hr_coeff : ∀ k, d ≤ k → r.coeff k = 0 := (poly_deg_lt_iff_coeff_eq_zero r d).mp hr_deg
  let P : Polynomial ℤ_[p] := Polynomial.X ^ d - r
  have hP_ps : P.toPowerSeries = f₀ * q := by
    dsimp only [P]
    rw [toPowerSeries_sub, toPowerSeries_X_pow, hdiv]
    ring
  have hP_coeff_d : P.coeff d = 1 := by
    dsimp only [P]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, hr_coeff d le_rfl, sub_zero]
  have hP_coeff_gt : ∀ k, d < k → P.coeff k = 0 := by
    intro k hk
    dsimp only [P]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (ne_of_gt hk),
      hr_coeff k hk.le, sub_zero]
  have hP_deg : P.natDegree = d := by
    apply le_antisymm
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      exact hP_coeff_gt
    · exact Polynomial.le_natDegree_of_ne_zero (by rw [hP_coeff_d]; exact one_ne_zero)
  have hP_monic : P.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hP_deg, hP_coeff_d]
  have hq_ne : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hP_ps
    exact hP_monic.ne_zero (toPowerSeries_injective (hP_ps.trans toPowerSeries_zero.symm))
  have hP_ne : P.toPowerSeries ≠ 0 := fun h0 =>
    hP_monic.ne_zero (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
  have hμ_P : iwasawaMu P.toPowerSeries = 0 := by
    rw [iwasawaMu_eq_zero_iff hP_ne]
    refine ⟨d, ?_⟩
    rw [toPowerSeries_coeff, hP_coeff_d, ← padicInt_isUnit_iff_not_p_dvd]
    exact isUnit_one
  have hμ_q : iwasawaMu q = 0 := by
    have h := iwasawaMu_mul hf₀ hq_ne
    rw [← hP_ps, hμ_P, hμ₀, zero_add] at h
    exact h.symm
  have hlam_P_le : iwasawaLambda P.toPowerSeries ≤ d := by
    unfold iwasawaLambda
    rw [dif_pos hP_ne]
    refine Nat.find_le ?_
    rw [primitivePart_eq_self_of_iwasawaMu_zero hμ_P, toPowerSeries_coeff, hP_coeff_d,
      ← padicInt_isUnit_iff_not_p_dvd]
    exact isUnit_one
  have hlam_sum : iwasawaLambda P.toPowerSeries = d + iwasawaLambda q := by
    rw [hP_ps, iwasawaLambda_mul hf₀ hq_ne, hlam₀]
  have hlam_q : iwasawaLambda q = 0 := by omega
  have hlam_P : iwasawaLambda P.toPowerSeries = d := by omega
  have hP_dist : IsDistinguishedPoly P := by
    refine ⟨hP_monic, fun k hk => ?_⟩
    rw [hP_deg] at hk
    rw [← toPowerSeries_coeff]
    exact p_dvd_coeff_of_lt_iwasawaLambda hP_ne hμ_P (by rwa [hlam_P])
  have hq_unit : IsUnit q :=
    (isUnit_iff_iwasawaMu_zero_and_iwasawaLambda_zero hq_ne).mpr ⟨hμ_q, hlam_q⟩
  set u : (PowerSeries ℤ_[p])ˣ := (hq_unit.unit)⁻¹
  have hfac : f = (p : PowerSeries ℤ_[p]) ^ μ * P.toPowerSeries * (u : PowerSeries ℤ_[p]) := by
    have hPu : P.toPowerSeries * (u : PowerSeries ℤ_[p]) = f₀ := by
      rw [hP_ps, mul_assoc]
      have hqu : q * (u : PowerSeries ℤ_[p]) = 1 := Units.mul_inv hq_unit.unit
      rw [hqu, mul_one]
    rw [mul_assoc, hPu]
    exact (p_pow_iwasawaMu_mul_primitivePart f).symm
  refine ⟨(P, u), ⟨hP_dist, hP_deg, hfac⟩, ?_⟩
  rintro ⟨P₂, u₂⟩ ⟨hP₂_dist, hP₂_deg, hfac₂⟩
  dsimp only at hP₂_dist hP₂_deg hfac₂
  have hP₂u₂ : P₂.toPowerSeries * (u₂ : PowerSeries ℤ_[p]) = f₀ := by
    apply p_pow_mul_right_cancel (m := μ)
    rw [p_pow_iwasawaMu_mul_primitivePart, ← mul_assoc]
    exact hfac₂.symm
  have hdiv₂ : PowerSeries.X ^ d =
      f₀ * ((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) + (Polynomial.X ^ d - P₂).toPowerSeries := by
    have hP₂_eq : P₂.toPowerSeries = f₀ * ((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) := by
      calc P₂.toPowerSeries
          = P₂.toPowerSeries * ((u₂ : PowerSeries ℤ_[p]) * ((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) := by
              rw [Units.mul_inv, mul_one]
        _ = (P₂.toPowerSeries * (u₂ : PowerSeries ℤ_[p])) * ((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) := by ring
        _ = f₀ * ((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) := by rw [hP₂u₂]
    rw [toPowerSeries_sub, toPowerSeries_X_pow, hP₂_eq]
    ring
  have hr₂_deg : Polynomial.X ^ d - P₂ = 0 ∨ (Polynomial.X ^ d - P₂).natDegree < iwasawaLambda f₀ := by
    rw [hlam₀, poly_deg_lt_iff_coeff_eq_zero]
    intro k hk
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases eq_or_lt_of_le hk with rfl | hlt
    · rw [if_pos rfl, ← hP₂_deg, ← Polynomial.leadingCoeff, hP₂_dist.1.leadingCoeff, sub_self]
    · rw [if_neg (ne_of_gt hlt),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P₂.natDegree < k), sub_zero]
  have hr₁_deg : Polynomial.X ^ d - P = 0 ∨ (Polynomial.X ^ d - P).natDegree < iwasawaLambda f₀ := by
    have : Polynomial.X ^ d - P = r := by dsimp only [P]; abel
    rw [this, hlam₀]
    exact hr_deg
  have hdiv₁ : PowerSeries.X ^ d = f₀ * q + (Polynomial.X ^ d - P).toPowerSeries := by
    have : Polynomial.X ^ d - P = r := by dsimp only [P]; abel
    rw [this]; exact hdiv
  have huniq := (weierstrass_division_Zp (f := PowerSeries.X ^ d) (g := f₀) hf₀ hμ₀).unique
    (y₁ := (((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]), Polynomial.X ^ d - P₂))
    (y₂ := (q, Polynomial.X ^ d - P)) ⟨hr₂_deg, hdiv₂⟩ ⟨hr₁_deg, hdiv₁⟩
  have hu_inv_eq : u₂⁻¹ = u⁻¹ := by
    have h1 : ((u₂⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) = q := congrArg Prod.fst huniq
    apply Units.ext
    simpa [u] using h1
  have hu_eq : u₂ = u := inv_injective hu_inv_eq
  have hP_eq : P₂ = P := by
    have h2 : Polynomial.X ^ d - P₂ = Polynomial.X ^ d - P := congrArg Prod.snd huniq
    exact sub_right_inj.mp h2
  exact Prod.ext hP_eq hu_eq

/-- Full triple uniqueness version of Weierstrass Preparation: `(μ, P, u)` is uniquely determined
with `μ = iwasawaMu f` and `P.natDegree = iwasawaLambda f`. -/
theorem weierstrass_preparation_Zp_unique_triple {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃! data : ℕ × Polynomial ℤ_[p] × (PowerSeries ℤ_[p])ˣ,
      IsDistinguishedPoly data.2.1 ∧
      f = (p : PowerSeries ℤ_[p]) ^ data.1 * data.2.1.toPowerSeries * (data.2.2 : PowerSeries ℤ_[p]) := by
  obtain ⟨⟨P, u⟩, ⟨hP_dist, hP_deg, hfac⟩, huniq⟩ := weierstrass_preparation_Zp hf
  refine ⟨(iwasawaMu f, P, u), ⟨hP_dist, hfac⟩, ?_⟩
  rintro ⟨μ₂, P₂, u₂⟩ ⟨hP₂_dist, hfac₂⟩
  have hP₂_ne : P₂.toPowerSeries ≠ 0 := fun h0 =>
    hP₂_dist.ne_zero (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
  have hp_ne : (p : PowerSeries ℤ_[p]) ^ μ₂ ≠ 0 := by
    intro h0
    have := congrArg (PowerSeries.coeff 0) h0
    rw [natCast_p_pow_powerSeries, PowerSeries.coeff_zero_C, map_zero] at this
    exact pow_ne_zero μ₂ padicInt_p_ne_zero this
  have hμ_eq : μ₂ = iwasawaMu f := by
    have h := congrArg iwasawaMu hfac₂
    rw [iwasawaMu_mul (mul_ne_zero hp_ne hP₂_ne) u₂.ne_zero,
      iwasawaMu_mul hp_ne hP₂_ne, iwasawaMu_p_pow, iwasawaMu_distinguished hP₂_dist,
      iwasawaMu_of_isUnit u₂.isUnit, add_zero, add_zero] at h
    exact h.symm
  have hlam_eq : P₂.natDegree = iwasawaLambda f := by
    have h := congrArg iwasawaLambda hfac₂
    rw [iwasawaLambda_mul (mul_ne_zero hp_ne hP₂_ne) u₂.ne_zero,
      iwasawaLambda_mul hp_ne hP₂_ne, iwasawaLambda_p_pow, iwasawaLambda_distinguished hP₂_dist,
      iwasawaLambda_of_isUnit u₂.isUnit, zero_add, add_zero] at h
    exact h.symm
  subst hμ_eq
  have hpair := huniq (P₂, u₂) ⟨hP₂_dist, hlam_eq, hfac₂⟩
  exact Prod.ext rfl hpair

end WeierstrassDivisionAndPreparation

/-! ## Section 3: Ring Structure (`LocalRing`, `Noetherian`, `UFD`) & Strassmann's Theorem -/

section RingStructureAndStrassmann

open scoped Classical

variable {p : ℕ} [Fact p.Prime]

/-- Every nonzero principal ideal `(f)` in `ℤ_[p][[T]]` equals `(p^μ * P)` for a unique
distinguished polynomial `P` of degree `λ`. -/
theorem span_eq_span_p_pow_mul_distinguished {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ P : Polynomial ℤ_[p], IsDistinguishedPoly P ∧ P.natDegree = iwasawaLambda f ∧
      Ideal.span ({f} : Set (PowerSeries ℤ_[p])) =
        Ideal.span ({(p : PowerSeries ℤ_[p]) ^ iwasawaMu f * P.toPowerSeries} : Set (PowerSeries ℤ_[p])) := by
  obtain ⟨⟨P, u⟩, ⟨hP_dist, hP_deg, hfac⟩, _⟩ := weierstrass_preparation_Zp hf
  dsimp only at hP_dist hP_deg hfac
  refine ⟨P, hP_dist, hP_deg, ?_⟩
  conv_lhs => rw [hfac]
  exact Ideal.span_singleton_mul_right_unit u.isUnit _

/-- `ℤ_[p][[T]]` is a local ring (`IsLocalRing (PowerSeries ℤ_[p])`). -/
instance isLocalRing_iwasawaAlg : IsLocalRing (PowerSeries ℤ_[p]) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  rw [isUnit_iwasawaAlg_iff, isUnit_iwasawaAlg_iff]
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (PowerSeries.constantCoeff f)
  rcases h with h1 | h2
  · exact Or.inl ((padicInt_isUnit_iff_not_p_dvd _).mp h1)
  · right
    rw [map_sub, map_one]
    exact (padicInt_isUnit_iff_not_p_dvd _).mp h2

/-- The maximal ideal of `ℤ_[p][[T]]` is `(p, T)`. -/
theorem maximalIdeal_iwasawaAlg_eq_span_p_X :
    IsLocalRing.maximalIdeal (PowerSeries ℤ_[p]) =
      Ideal.span ({(p : PowerSeries ℤ_[p]), PowerSeries.X} : Set (PowerSeries ℤ_[p])) := by
  ext f
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iwasawaAlg_iff, not_not]
  constructor
  · rintro ⟨c, hc⟩
    have hsplit : f = (p : PowerSeries ℤ_[p]) * PowerSeries.C c + PowerSeries.X * psShift 1 f := by
      have h := ps_eq_trunc_add_X_pow_mul_shift 1 f
      have ht : psTrunc 1 f = PowerSeries.C (PowerSeries.constantCoeff f) := by
        unfold psTrunc
        simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
          PowerSeries.coeff_zero_eq_constantCoeff]
      conv_lhs => rw [h, ht, pow_one, hc, map_mul, map_natCast]
    rw [hsplit]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · intro hf
    have hle : Ideal.span ({(p : PowerSeries ℤ_[p]), PowerSeries.X} : Set (PowerSeries ℤ_[p])) ≤
        IsLocalRing.maximalIdeal (PowerSeries ℤ_[p]) := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iwasawaAlg_iff, not_not]
        simp
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iwasawaAlg_iff, not_not]
        simp
    have hmem := hle hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iwasawaAlg_iff, not_not] at hmem
    exact hmem

/-- `ℤ_[p]` is a principal ideal ring (every nonzero ideal is `(p^v)`). -/
instance isPrincipalIdealRing_padicInt : IsPrincipalIdealRing ℤ_[p] := by
  refine ⟨fun I => ?_⟩
  by_cases hbot : I = ⊥
  · refine ⟨0, ?_⟩
    rw [hbot, Submodule.span_zero_singleton]
  · have hne : ∃ v : ℕ, ∃ x ∈ I, x ≠ 0 ∧ x.valuation = v := by
      have hne' : ∃ x ∈ I, x ≠ 0 := by
        by_contra h
        push Not at h
        apply hbot
        ext x
        simp only [Submodule.mem_bot]
        exact ⟨h x, fun hx0 => hx0 ▸ I.zero_mem⟩
      obtain ⟨x, hxI, hx0⟩ := hne'
      exact ⟨x.valuation, x, hxI, hx0, rfl⟩
    let v := Nat.find hne
    obtain ⟨x₀, hx₀I, hx₀0, hx₀v⟩ := Nat.find_spec hne
    refine ⟨(p : ℤ_[p]) ^ v, ?_⟩
    ext y
    rw [Submodule.mem_span_singleton]
    constructor
    · intro hyI
      by_cases hy0 : y = 0
      · exact ⟨0, by simp [hy0]⟩
      · have hle : v ≤ y.valuation := Nat.find_min' hne ⟨y, hyI, hy0, rfl⟩
        have hspec := PadicInt.unitCoeff_spec hy0
        refine ⟨(PadicInt.unitCoeff hy0 : ℤ_[p]) * (p : ℤ_[p]) ^ (y.valuation - v), ?_⟩
        rw [smul_eq_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
        exact hspec.symm
    · rintro ⟨c, rfl⟩
      rw [smul_eq_mul]
      let u₀ : ℤ_[p]ˣ := PadicInt.unitCoeff hx₀0
      have hspec : x₀ = (u₀ : ℤ_[p]) * (p : ℤ_[p]) ^ v := by
        simpa [u₀, hx₀v] using PadicInt.unitCoeff_spec hx₀0
      have hpv_mem : (p : ℤ_[p]) ^ v ∈ I := by
        have h1 : (p : ℤ_[p]) ^ v = (u₀⁻¹ : ℤ_[p]ˣ) * x₀ := by
          calc (p : ℤ_[p]) ^ v = ((u₀⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((u₀ : ℤ_[p]) * (p : ℤ_[p]) ^ v) := by
                rw [← mul_assoc, Units.inv_mul, one_mul]
            _ = (u₀⁻¹ : ℤ_[p]ˣ) * x₀ := by rw [← hspec]
        rw [h1]
        exact I.mul_mem_left _ hx₀I
      exact I.mul_mem_left c hpv_mem

/-- Every ideal of `ℤ_[p][[T]]` containing an element of `iwasawaMu ≤ m` is finitely generated. -/
private lemma ideal_fg_of_exists_iwasawaMu_le :
    ∀ (m : ℕ) (I : Ideal (PowerSeries ℤ_[p])),
      (∃ g ∈ I, g ≠ 0 ∧ iwasawaMu g ≤ m) → I.FG
  | 0, I, ⟨g, hgI, hg0, hμg⟩ => by
      have hμ0 : iwasawaMu g = 0 := Nat.le_zero.mp hμg
      set d := iwasawaLambda g
      let proj : PowerSeries ℤ_[p] →ₗ[ℤ_[p]] (Fin d → ℤ_[p]) :=
        { toFun := fun f j => PowerSeries.coeff (j : ℕ) f
          map_add' := fun _ _ => by ext j; simp
          map_smul' := fun c f => by
            ext j
            simp }
      let N : Submodule ℤ_[p] (Fin d → ℤ_[p]) :=
        Submodule.map proj
          ({ carrier := {f : PowerSeries ℤ_[p] | f ∈ I ∧ ∀ k, d ≤ k → PowerSeries.coeff k f = 0}
             add_mem' := fun {a b} ha hb => ⟨I.add_mem ha.1 hb.1, fun k hk => by rw [map_add, ha.2 k hk, hb.2 k hk, add_zero]⟩
             zero_mem' := ⟨I.zero_mem, fun _ _ => by simp⟩
             smul_mem' := fun c {a} ha => by
               refine ⟨?_, fun k hk => ?_⟩
               · rw [Algebra.smul_def]
                 exact I.mul_mem_left _ ha.1
               · simp [ha.2 k hk] } : Submodule ℤ_[p] (PowerSeries ℤ_[p]))
      have hN_fg : N.FG := IsNoetherian.noetherian N
      obtain ⟨S, hS⟩ := hN_fg
      let lift : (Fin d → ℤ_[p]) → PowerSeries ℤ_[p] :=
        fun v => ∑ j : Fin d, PowerSeries.C (v j) * PowerSeries.X ^ (j : ℕ)
      have hlift_mem : ∀ v ∈ S, lift v ∈ I := by
        intro v hv
        have hvN : v ∈ N := by rw [← hS]; exact Submodule.subset_span hv
        obtain ⟨f, ⟨hfI, hf_zero⟩, hfv⟩ := hvN
        have hfeq : lift v = f := by
          ext k
          dsimp only [lift]
          rw [map_sum]
          simp_rw [PowerSeries.coeff_C_mul_X_pow]
          by_cases hk : k < d
          · rw [Finset.sum_eq_single ⟨k, hk⟩]
            · simp only [↓reduceIte]
              exact (congrFun hfv ⟨k, hk⟩).symm
            · intro j _ hj
              have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
              simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [hf_zero k (not_lt.mp hk)]
            refine Finset.sum_eq_zero fun j _ => ?_
            have hne : (j : ℕ) ≠ k := ne_of_lt (lt_of_lt_of_le j.2 (not_lt.mp hk))
            simp [hne.symm]
        rwa [hfeq]
      refine ⟨insert g (S.image lift), le_antisymm ?_ ?_⟩
      · rw [Ideal.span_le]
        intro x hx
        rw [Finset.coe_insert, Set.mem_insert_iff] at hx
        rcases hx with rfl | hxS
        · exact hgI
        · rw [Finset.coe_image, Set.mem_image] at hxS
          obtain ⟨v, hvS, rfl⟩ := hxS
          exact hlift_mem v hvS
      · intro f hfI
        obtain ⟨⟨q, r⟩, ⟨hr_deg, hdiv⟩, _⟩ := weierstrass_division_Zp (f := f) (g := g) hg0 hμ0
        have hrI : r.toPowerSeries ∈ I := by
          have : r.toPowerSeries = f - g * q := by rw [hdiv]; ring
          rw [this]
          exact I.sub_mem hfI (I.mul_mem_right q hgI)
        have hr_zero : ∀ k, d ≤ k → PowerSeries.coeff k r.toPowerSeries = 0 := by
          intro k hk
          rw [toPowerSeries_coeff]
          exact (poly_deg_lt_iff_coeff_eq_zero r d).mp hr_deg k hk
        have hproj_mem : proj r.toPowerSeries ∈ Submodule.span ℤ_[p] (S : Set (Fin d → ℤ_[p])) := by
          rw [hS]
          exact ⟨r.toPowerSeries, ⟨hrI, hr_zero⟩, rfl⟩
        have hlift_span : ∀ v ∈ Submodule.span ℤ_[p] (S : Set (Fin d → ℤ_[p])),
            lift v ∈ Ideal.span (↑(insert g (S.image lift)) : Set (PowerSeries ℤ_[p])) := by
          intro v hv
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
          · intro w hw
            refine Ideal.subset_span ?_
            rw [Finset.coe_insert]
            exact Set.mem_insert_of_mem g (Finset.mem_coe.mpr (Finset.mem_image_of_mem lift hw))
          · have h0 : lift 0 = 0 := by ext k; simp [lift]
            rw [h0]; exact Ideal.zero_mem _
          · intro x y _ _ hx hy
            have hadd : lift (x + y) = lift x + lift y := by
              ext k
              dsimp only [lift]
              simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
            rw [hadd]; exact Ideal.add_mem _ hx hy
          · intro c x _ hx
            have hsmul : lift (c • x) = PowerSeries.C c * lift x := by
              dsimp only [lift]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
            rw [hsmul]; exact Ideal.mul_mem_left _ _ hx
        have hr_eq_lift : r.toPowerSeries = lift (proj r.toPowerSeries) := by
          ext k
          dsimp only [lift, proj]
          rw [map_sum]
          simp_rw [PowerSeries.coeff_C_mul_X_pow]
          by_cases hk : k < d
          · rw [Finset.sum_eq_single ⟨k, hk⟩]
            · simp
            · intro j _ hj
              have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
              simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
          · rw [hr_zero k (not_lt.mp hk)]
            symm
            refine Finset.sum_eq_zero fun j _ => ?_
            have hne : (j : ℕ) ≠ k := ne_of_lt (lt_of_lt_of_le j.2 (not_lt.mp hk))
            simp [hne.symm]
        rw [hdiv]
        refine Ideal.add_mem _ ?_ ?_
        · refine Ideal.mul_mem_right q _ (Ideal.subset_span ?_)
          rw [Finset.coe_insert]
          exact Set.mem_insert g _
        · rw [hr_eq_lift]
          exact hlift_span _ hproj_mem
  | m + 1, I, ⟨g, hgI, hg0, hμg⟩ => by
      by_cases h0 : ∃ g' ∈ I, g' ≠ 0 ∧ iwasawaMu g' = 0
      · obtain ⟨g', hg'I, hg'0, hμ0⟩ := h0
        exact ideal_fg_of_exists_iwasawaMu_le 0 I ⟨g', hg'I, hg'0, hμ0.le⟩
      · push Not at h0
        let I' : Ideal (PowerSeries ℤ_[p]) :=
          { carrier := {h : PowerSeries ℤ_[p] | (p : PowerSeries ℤ_[p]) * h ∈ I}
            add_mem' := fun {a b} ha hb => by
              show (p : PowerSeries ℤ_[p]) * (a + b) ∈ I
              rw [mul_add]; exact I.add_mem ha hb
            zero_mem' := by show (p : PowerSeries ℤ_[p]) * 0 ∈ I; simp [I.zero_mem]
            smul_mem' := fun c {a} ha => by
              show (p : PowerSeries ℤ_[p]) * (c * a) ∈ I
              rw [mul_left_comm]
              exact I.mul_mem_left c ha }
        have hp_dvd_all : ∀ f ∈ I, ∃ h ∈ I', f = (p : PowerSeries ℤ_[p]) * h := by
          intro f hfI
          by_cases hf0 : f = 0
          · exact ⟨0, I'.zero_mem, by simp [hf0]⟩
          · have hμ_pos : 1 ≤ iwasawaMu f := Nat.one_le_iff_ne_zero.mpr (h0 f hfI hf0)
            let h := (p : PowerSeries ℤ_[p]) ^ (iwasawaMu f - 1) * primitivePart f
            have hfeq : f = (p : PowerSeries ℤ_[p]) * h := by
              dsimp only [h]
              rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hμ_pos,
                p_pow_iwasawaMu_mul_primitivePart]
            exact ⟨h, by show (p : PowerSeries ℤ_[p]) * h ∈ I; rwa [← hfeq], hfeq⟩
        obtain ⟨g₁, hg₁I', hgeq⟩ := hp_dvd_all g hgI
        have hg₁0 : g₁ ≠ 0 := by intro h; apply hg0; rw [hgeq, h, mul_zero]
        have hμg₁ : iwasawaMu g₁ ≤ m := by
          have h := iwasawaMu_p_pow_mul hg₁0 1
          rw [pow_one, ← hgeq] at h
          omega
        obtain ⟨S, hS⟩ := ideal_fg_of_exists_iwasawaMu_le m I' ⟨g₁, hg₁I', hg₁0, hμg₁⟩
        refine ⟨S.image (fun h => (p : PowerSeries ℤ_[p]) * h), le_antisymm ?_ ?_⟩
        · rw [Ideal.span_le]
          intro x hx
          rw [Finset.coe_image, Set.mem_image] at hx
          obtain ⟨h, hhS, rfl⟩ := hx
          have hhI' : h ∈ I' := by rw [← hS]; exact Ideal.subset_span hhS
          exact hhI'
        · intro f hfI
          obtain ⟨h, hhI', rfl⟩ := hp_dvd_all f hfI
          rw [← hS] at hhI'
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hhI'
          · intro w hw
            exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
          · rw [mul_zero]; exact Ideal.zero_mem _
          · intro x y _ _ hx hy
            rw [mul_add]; exact Ideal.add_mem _ hx hy
          · intro c x _ hx
            change (p : PowerSeries ℤ_[p]) * (c * x) ∈ _
            rw [mul_left_comm]
            exact Ideal.mul_mem_left _ c hx

/-- **`ℤ_[p][[T]]` is a Noetherian Ring** (unconditional proof via Weierstrass Division!). -/
instance isNoetherianRing_iwasawaAlg : IsNoetherianRing (PowerSeries ℤ_[p]) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases hbot : I = ⊥
  · rw [hbot]; exact Submodule.fg_bot
  · have hne : ∃ g ∈ I, g ≠ 0 := by
      by_contra h
      push Not at h
      apply hbot
      ext x
      simp only [Submodule.mem_bot]
      exact ⟨h x, fun hx0 => hx0 ▸ I.zero_mem⟩
    obtain ⟨g, hgI, hg0⟩ := hne
    exact ideal_fg_of_exists_iwasawaMu_le (iwasawaMu g) I ⟨g, hgI, hg0, le_rfl⟩

/-- `p` is a prime element in `ℤ_[p][[T]]`. -/
theorem prime_p_iwasawaAlg : Prime (p : PowerSeries ℤ_[p]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have := congrArg (PowerSeries.coeff 0) h0
    rw [show (p : PowerSeries ℤ_[p]) = PowerSeries.C (p : ℤ_[p]) from (map_natCast PowerSeries.C p).symm,
      PowerSeries.coeff_zero_C, map_zero] at this
    exact padicInt_p_ne_zero this
  · intro hu
    have h := iwasawaMu_of_isUnit hu
    have h1 := iwasawaMu_p_pow (p := p) 1
    rw [pow_one] at h1
    omega
  · intro a b hab
    by_cases ha : a = 0
    · exact Or.inl (ha ▸ dvd_zero _)
    by_cases hb : b = 0
    · exact Or.inr (hb ▸ dvd_zero _)
    obtain ⟨c, hc⟩ := hab
    have hc0 : c ≠ 0 := by intro h; rw [h, mul_zero] at hc; exact mul_ne_zero ha hb hc
    have hμ : iwasawaMu a + iwasawaMu b = 1 + iwasawaMu c := by
      rw [← iwasawaMu_mul ha hb, hc]
      simpa [pow_one] using iwasawaMu_p_pow_mul hc0 1
    have hor : 1 ≤ iwasawaMu a ∨ 1 ≤ iwasawaMu b := by omega
    rcases hor with ha1 | hb1
    · left
      refine ⟨(p : PowerSeries ℤ_[p]) ^ (iwasawaMu a - 1) * primitivePart a, ?_⟩
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel ha1, p_pow_iwasawaMu_mul_primitivePart]
    · right
      refine ⟨(p : PowerSeries ℤ_[p]) ^ (iwasawaMu b - 1) * primitivePart b, ?_⟩
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hb1, p_pow_iwasawaMu_mul_primitivePart]

/-- A distinguished polynomial `P` divides `Q` in `ℤ_[p][[T]]` iff `P ∣ Q` in `ℤ_[p][T]`. -/
lemma distinguished_dvd_toPowerSeries_iff {P Q : Polynomial ℤ_[p]} (hP : IsDistinguishedPoly P) :
    P.toPowerSeries ∣ Q.toPowerSeries ↔ P ∣ Q := by
  constructor
  · rintro ⟨F, hF⟩
    have hdiv : Q %ₘ P + P * (Q /ₘ P) = Q := Polynomial.modByMonic_add_div Q P
    set r := Q %ₘ P
    set q := Q /ₘ P
    have hr_deg : r = 0 ∨ r.natDegree < iwasawaLambda P.toPowerSeries := by
      rw [iwasawaLambda_distinguished hP]
      by_cases hr0 : r = 0
      · exact Or.inl hr0
      · right
        have hlt : r.degree < P.degree := Polynomial.degree_modByMonic_lt Q hP.1
        rw [Polynomial.degree_eq_natDegree hr0, Polynomial.degree_eq_natDegree hP.ne_zero] at hlt
        exact_mod_cast hlt
    have hP_ne : P.toPowerSeries ≠ 0 := fun h0 =>
      hP.ne_zero (toPowerSeries_injective (h0.trans toPowerSeries_zero.symm))
    have heq1 : Q.toPowerSeries = P.toPowerSeries * q.toPowerSeries + r.toPowerSeries := by
      conv_lhs => rw [← hdiv]
      rw [toPowerSeries_add, toPowerSeries_mul, add_comm]
    have heq2 : Q.toPowerSeries = P.toPowerSeries * F + (0 : Polynomial ℤ_[p]).toPowerSeries := by
      rw [toPowerSeries_zero, add_zero, hF]
    have huniq := (weierstrass_division_Zp (f := Q.toPowerSeries) (g := P.toPowerSeries)
      hP_ne (iwasawaMu_distinguished hP)).unique
      (y₁ := (q.toPowerSeries, r)) (y₂ := (F, 0))
      ⟨hr_deg, heq1⟩ ⟨Or.inl rfl, heq2⟩
    have hr0 : r = 0 := congrArg Prod.snd huniq
    refine ⟨q, ?_⟩
    rw [← hdiv, hr0, zero_add]
  · rintro ⟨R, rfl⟩
    exact ⟨R.toPowerSeries, toPowerSeries_mul P R⟩

/-- If `P` is distinguished and `P.toPowerSeries` is irreducible in `ℤ_[p][[T]]`, then `P` is
irreducible in `ℤ_[p][T]`. -/
lemma irreducible_poly_of_distinguished_irreducible_ps {P : Polynomial ℤ_[p]}
    (hP : IsDistinguishedPoly P) (hirr : Irreducible P.toPowerSeries) :
    Irreducible P := by
  refine ⟨?_, fun A B hAB => ?_⟩
  · intro hu
    exact hirr.not_isUnit (by
      obtain ⟨Q, hQ⟩ := hu.exists_right_inv
      exact isUnit_iff_exists_inv.mpr ⟨Q.toPowerSeries, by rw [← toPowerSeries_mul, hQ, toPowerSeries_one]⟩)
  · have hps : P.toPowerSeries = A.toPowerSeries * B.toPowerSeries := by
      rw [hAB, toPowerSeries_mul]
    have hAB_unit : IsUnit A.toPowerSeries ∨ IsUnit B.toPowerSeries := hirr.isUnit_or_isUnit hps
    have hlead : A.leadingCoeff * B.leadingCoeff = 1 := by
      have h := congrArg Polynomial.leadingCoeff hAB
      rw [hP.1.leadingCoeff, Polynomial.leadingCoeff_mul] at h
      exact h.symm
    have hA_lc_unit : IsUnit A.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨B.leadingCoeff, hlead⟩
    have hB_lc_unit : IsUnit B.leadingCoeff := isUnit_iff_exists_inv.mpr ⟨A.leadingCoeff, by rwa [mul_comm]⟩
    have helper : ∀ (X Y : Polynomial ℤ_[p]), P = X * Y → IsUnit X.leadingCoeff →
        IsUnit X.toPowerSeries → IsUnit X := by
      intro X Y hXY hXlc hXps
      have hP_mod : Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) P = Polynomial.X ^ P.natDegree := by
        ext k
        rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
        rcases lt_trichotomy k P.natDegree with hlt | rfl | hgt
        · rw [if_neg (ne_of_lt hlt), ← padicInt_p_dvd_iff_toZMod_eq_zero]
          exact hP.2 k hlt
        · rw [if_pos rfl, ← Polynomial.leadingCoeff, hP.1.leadingCoeff, map_one]
        · rw [if_neg (ne_of_gt hgt), Polynomial.coeff_eq_zero_of_natDegree_lt hgt, map_zero]
      have hX_const_ne : (Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X).coeff 0 ≠ 0 := by
        rw [Polynomial.coeff_map, ne_eq, ← padicInt_p_dvd_iff_toZMod_eq_zero]
        have := (isUnit_iwasawaAlg_iff X.toPowerSeries).mp hXps
        simpa [toPowerSeries_coeff] using this
      have hX_dvd : Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X ∣ Polynomial.X ^ P.natDegree :=
        ⟨Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) Y, by rw [← Polynomial.map_mul, ← hXY, hP_mod]⟩
      have hX_not_dvd_X : ¬ (Polynomial.X : Polynomial (ZMod p)) ∣
          Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X := by
        rintro ⟨R, hR⟩
        have h0 := congrArg (fun f : Polynomial (ZMod p) => f.coeff 0) hR
        simp at h0
        exact hX_const_ne (by rwa [Polynomial.coeff_map])
      have hX_unit_mod : IsUnit (Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X) := by
        have hcop : IsCoprime (Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X)
            (Polynomial.X : Polynomial (ZMod p)) := by
          have hprimeX : Prime (Polynomial.X : Polynomial (ZMod p)) := Polynomial.prime_X
          exact (hprimeX.coprime_iff_not_dvd.mpr hX_not_dvd_X).symm
        exact isUnit_of_dvd_one (hcop.pow_right.dvd_of_dvd_mul_right
          (by simpa [mul_one] using hX_dvd))
      have hX_deg_mod : (Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hX_unit_mod
      have hX_lc_ne : PadicInt.toZMod X.leadingCoeff ≠ 0 := by
        rw [ne_eq, ← padicInt_p_dvd_iff_toZMod_eq_zero, ← padicInt_isUnit_iff_not_p_dvd]
        exact hXlc
      have hX_deg : X.natDegree = 0 := by
        by_contra hne0
        have hcoeff_ne : (Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X).coeff X.natDegree ≠ 0 := by
          rw [Polynomial.coeff_map]
          exact hX_lc_ne
        have hle : X.natDegree ≤ (Polynomial.map (PadicInt.toZMod : ℤ_[p] →+* ZMod p) X).natDegree :=
          Polynomial.le_natDegree_of_ne_zero hcoeff_ne
        omega
      rw [Polynomial.eq_C_of_natDegree_eq_zero hX_deg]
      have h0u : IsUnit (X.coeff 0) := by
        have := (isUnit_iwasawaAlg_iff X.toPowerSeries).mp hXps
        rw [padicInt_isUnit_iff_not_p_dvd]
        simpa [toPowerSeries_coeff] using this
      exact h0u.map Polynomial.C
    rcases hAB_unit with hAu | hBu
    · exact Or.inl (helper A B hAB hA_lc_unit hAu)
    · exact Or.inr (helper B A (by rw [hAB, mul_comm]) hB_lc_unit hBu)

/-- `ℤ_[p][[T]]` satisfies ascending chain condition on principal ideals (`WfDvdMonoid`),
via the strictly decreasing `ℕ∞`-measure `f ↦ iwasawaMu f + iwasawaLambda f` (`0 ↦ ⊤`). -/
instance wfDvdMonoid_iwasawaAlg : WfDvdMonoid (PowerSeries ℤ_[p]) := by
  let meas : PowerSeries ℤ_[p] → ℕ∞ :=
    fun f => if f = 0 then ⊤ else ((iwasawaMu f + iwasawaLambda f : ℕ) : ℕ∞)
  refine ⟨Subrelation.wf ?_ (InvImage.wf meas wellFounded_lt)⟩
  intro a b hab
  obtain ⟨ha0, c, hc_nu, rfl⟩ := hab
  change meas a < meas (a * c)
  dsimp only [meas]
  rw [if_neg ha0]
  by_cases hc0 : c = 0
  · rw [hc0, mul_zero, if_pos rfl]
    exact WithTop.coe_lt_top _
  · rw [if_neg (mul_ne_zero ha0 hc0)]
    rw [iwasawaMu_mul ha0 hc0, iwasawaLambda_mul ha0 hc0]
    have hpos : 0 < iwasawaMu c + iwasawaLambda c := by
      by_contra h0
      have hμ0 : iwasawaMu c = 0 := by omega
      have hlam0 : iwasawaLambda c = 0 := by omega
      exact hc_nu ((isUnit_iff_iwasawaMu_zero_and_iwasawaLambda_zero hc0).mpr ⟨hμ0, hlam0⟩)
    exact_mod_cast (show iwasawaMu a + iwasawaLambda a <
      iwasawaMu a + iwasawaMu c + (iwasawaLambda a + iwasawaLambda c) by omega)

/-- **`ℤ_[p][[T]]` is a Unique Factorization Domain (`UniqueFactorizationMonoid (PowerSeries ℤ_[p])`)**:
unconditional proof from Weierstrass Preparation + Division + `ℤ_[p][T]` UFD! -/
instance uniqueFactorizationMonoid_iwasawaAlg : UniqueFactorizationMonoid (PowerSeries ℤ_[p]) where
  irreducible_iff_prime := fun {f} => ⟨fun hirr => by
    have hf0 : f ≠ 0 := hirr.ne_zero
    obtain ⟨⟨P, u⟩, ⟨hP_dist, _, hfac⟩, _⟩ := weierstrass_preparation_Zp hf0
    dsimp only at hP_dist hfac
    by_cases hμ : iwasawaMu f = 0
    · rw [hμ, pow_zero, one_mul] at hfac
      have hP_irr_ps : Irreducible P.toPowerSeries := by
        have hassoc : Associated P.toPowerSeries f := ⟨u, hfac.symm⟩
        exact hassoc.irreducible_iff.mpr hirr
      have hP_irr_poly : Irreducible P :=
        irreducible_poly_of_distinguished_irreducible_ps hP_dist hP_irr_ps
      have hP_prime_poly : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.mp hP_irr_poly
      have hP_prime_ps : Prime P.toPowerSeries := by
        refine ⟨hP_irr_ps.ne_zero, hP_irr_ps.not_isUnit, fun g h hgh => ?_⟩
        by_cases hg0 : g = 0
        · exact Or.inl (hg0 ▸ dvd_zero _)
        by_cases hh0 : h = 0
        · exact Or.inr (hh0 ▸ dvd_zero _)
        obtain ⟨⟨G, ug⟩, ⟨_, _, hfacG⟩, _⟩ := weierstrass_preparation_Zp hg0
        obtain ⟨⟨H, uh⟩, ⟨_, _, hfacH⟩, _⟩ := weierstrass_preparation_Zp hh0
        dsimp only at hfacG hfacH
        set μg := iwasawaMu g
        set μh := iwasawaMu h
        have hP_dvd_prod : P.toPowerSeries ∣ (p : PowerSeries ℤ_[p]) ^ (μg + μh) *
            (G * H).toPowerSeries := by
          obtain ⟨Q, hQ⟩ := hgh
          refine ⟨Q * (((ug * uh)⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]), ?_⟩
          calc (p : PowerSeries ℤ_[p]) ^ (μg + μh) * (G * H).toPowerSeries
              = g * h * (((ug * uh)⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) := by
                  rw [hfacG, hfacH, pow_add, toPowerSeries_mul]
                  have hinv : (ug : PowerSeries ℤ_[p]) * (uh : PowerSeries ℤ_[p]) *
                      (((ug * uh)⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p]) = 1 := by
                    simpa [Units.val_mul] using Units.mul_inv (ug * uh)
                  linear_combination ((p : PowerSeries ℤ_[p]) ^ μg *
                    (p : PowerSeries ℤ_[p]) ^ μh * G.toPowerSeries * H.toPowerSeries) * hinv.symm
            _ = P.toPowerSeries * (Q * (((ug * uh)⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) := by
                  rw [hQ]; ring
        have hP_not_p : ¬ (p : PowerSeries ℤ_[p]) ∣ P.toPowerSeries := by
          rintro ⟨R, hR⟩
          by_cases hR0 : R = 0
          · rw [hR0, mul_zero] at hR; exact hP_irr_ps.ne_zero hR
          · have h := congrArg iwasawaMu hR
            rw [iwasawaMu_distinguished hP_dist] at h
            have h1 := iwasawaMu_p_pow_mul hR0 1
            rw [pow_one] at h1
            omega
        have hP_dvd_GH_ps : P.toPowerSeries ∣ (G * H).toPowerSeries := by
          have hcancel : ∀ n : ℕ, P.toPowerSeries ∣ (p : PowerSeries ℤ_[p]) ^ n * (G * H).toPowerSeries →
              P.toPowerSeries ∣ (G * H).toPowerSeries := by
            intro n
            induction n with
            | zero => simp
            | succ n ih =>
              intro hd
              obtain ⟨Q, hQ⟩ := hd
              have hp_dvd : (p : PowerSeries ℤ_[p]) ∣ P.toPowerSeries * Q := by
                rw [← hQ, pow_succ', mul_assoc]
                exact dvd_mul_right _ _
              have hp_dvd_Q : (p : PowerSeries ℤ_[p]) ∣ Q :=
                (prime_p_iwasawaAlg.dvd_or_dvd hp_dvd).resolve_left hP_not_p
              obtain ⟨Q', rfl⟩ := hp_dvd_Q
              refine ih ⟨Q', ?_⟩
              apply p_pow_mul_right_cancel (m := 1)
              rw [pow_one]
              calc (p : PowerSeries ℤ_[p]) * ((p : PowerSeries ℤ_[p]) ^ n * (G * H).toPowerSeries)
                  = (p : PowerSeries ℤ_[p]) ^ (n + 1) * (G * H).toPowerSeries := by rw [pow_succ', mul_assoc]
                _ = P.toPowerSeries * ((p : PowerSeries ℤ_[p]) * Q') := hQ
                _ = (p : PowerSeries ℤ_[p]) * (P.toPowerSeries * Q') := by ring
          exact hcancel _ hP_dvd_prod
        have hP_dvd_GH : P ∣ G * H := (distinguished_dvd_toPowerSeries_iff hP_dist).mp hP_dvd_GH_ps
        rcases hP_prime_poly.dvd_or_dvd hP_dvd_GH with hPG | hPH
        · left
          have h1 : P.toPowerSeries ∣ G.toPowerSeries :=
            (distinguished_dvd_toPowerSeries_iff hP_dist).mpr hPG
          exact h1.trans ⟨(p : PowerSeries ℤ_[p]) ^ μg * (ug : PowerSeries ℤ_[p]), by
            rw [hfacG]; ring⟩
        · right
          have h1 : P.toPowerSeries ∣ H.toPowerSeries :=
            (distinguished_dvd_toPowerSeries_iff hP_dist).mpr hPH
          exact h1.trans ⟨(p : PowerSeries ℤ_[p]) ^ μh * (uh : PowerSeries ℤ_[p]), by
            rw [hfacH]; ring⟩
      exact (Associated.prime_iff (⟨u, hfac.symm⟩ : Associated P.toPowerSeries f)).mp hP_prime_ps
    · have hμ1 : 1 ≤ iwasawaMu f := Nat.one_le_iff_ne_zero.mpr hμ
      let rest := (p : PowerSeries ℤ_[p]) ^ (iwasawaMu f - 1) * P.toPowerSeries * (u : PowerSeries ℤ_[p])
      have hf_eq : f = (p : PowerSeries ℤ_[p]) * rest := by
        dsimp only [rest]
        rw [← mul_assoc, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hμ1]
        exact hfac
      have hrest_unit : IsUnit rest :=
        (hirr.isUnit_or_isUnit hf_eq).resolve_left prime_p_iwasawaAlg.not_isUnit
      exact (Associated.prime_iff (⟨hrest_unit.unit, hf_eq.symm⟩ : Associated (p : PowerSeries ℤ_[p]) f)).mp
        prime_p_iwasawaAlg,
    Prime.irreducible⟩

/-! ### Analytic Evaluation Ring Homomorphism & Strassmann's Theorem -/

lemma evalIwasawa_zero {y : ℤ_[p]} : evalIwasawa (0 : PowerSeries ℤ_[p]) y = 0 := by
  simp [evalIwasawa]

lemma evalIwasawa_C (c : ℤ_[p]) (y : ℤ_[p]) : evalIwasawa (PowerSeries.C c) y = c := by
  unfold evalIwasawa
  rw [tsum_eq_single 0]
  · simp
  · intro k hk; simp [PowerSeries.coeff_C, hk]

lemma evalIwasawa_one (y : ℤ_[p]) : evalIwasawa (1 : PowerSeries ℤ_[p]) y = 1 := by
  simpa using evalIwasawa_C (p := p) 1 y

lemma evalIwasawa_add (f g : PowerSeries ℤ_[p]) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    evalIwasawa (f + g) y = evalIwasawa f y + evalIwasawa g y := by
  unfold evalIwasawa
  simp_rw [map_add, add_mul]
  exact (summable_evalIwasawa_term f hy).tsum_add (summable_evalIwasawa_term g hy)

lemma norm_evalIwasawa_sub_trunc_le (f : PowerSeries ℤ_[p]) {y : ℤ_[p]} (hy : ‖y‖ < 1) (N : ℕ) :
    ‖evalIwasawa f y - ∑ k ∈ Finset.range N, PowerSeries.coeff k f * y ^ k‖ ≤ ‖y‖ ^ N := by
  have hs := summable_evalIwasawa_term f hy
  have hsp : evalIwasawa f y - ∑ k ∈ Finset.range N, PowerSeries.coeff k f * y ^ k =
      ∑' k : ℕ, PowerSeries.coeff (k + N) f * y ^ (k + N) := by
    unfold evalIwasawa
    rw [← hs.sum_add_tsum_nat_add N]
    ring
  rw [hsp]
  have hs' := (summable_nat_add_iff N).mpr hs
  have hlim : Tendsto (fun M => ‖∑ k ∈ Finset.range M, PowerSeries.coeff (k + N) f * y ^ (k + N)‖)
      atTop (nhds ‖∑' k : ℕ, PowerSeries.coeff (k + N) f * y ^ (k + N)‖) :=
    hs'.hasSum.tendsto_sum_nat.norm
  refine le_of_tendsto' hlim fun M => ?_
  refine padicInt_norm_sum_le _ _ (pow_nonneg (norm_nonneg _) N) fun k _ => ?_
  rw [norm_mul, norm_pow, pow_add]
  calc ‖PowerSeries.coeff (k + N) f‖ * (‖y‖ ^ k * ‖y‖ ^ N)
      ≤ 1 * (1 * ‖y‖ ^ N) :=
        mul_le_mul (PadicInt.norm_le_one _)
          (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hy.le)
            (pow_nonneg (norm_nonneg _) N))
          (by positivity) zero_le_one
    _ = ‖y‖ ^ N := by ring

lemma norm_le_p_inv_of_lt_one {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    ‖y‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
  have hdvd : (p : ℤ_[p]) ^ 1 ∣ y := by
    rw [pow_one]
    exact (padicInt_norm_lt_one_iff_p_dvd y).mp hy
  exact (padicInt_p_pow_dvd_iff_norm_le y 1).mp hdvd

/-- Crucial mod-`p` congruence for analytic evaluation on the open unit disk:
for any `f ∈ ℤ_[p][[T]]` and `y ∈ p ℤ_[p]` (`‖y‖ < 1`),
`evalIwasawa f y ≡ f(0) [mod p]`! -/
theorem toZMod_evalIwasawa (f : PowerSeries ℤ_[p]) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    PadicInt.toZMod (evalIwasawa f y) = PadicInt.toZMod (PowerSeries.constantCoeff f) := by
  have hbd := norm_evalIwasawa_sub_trunc_le f hy 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, pow_one,
    PowerSeries.coeff_zero_eq_constantCoeff] at hbd
  have hlt : ‖evalIwasawa f y - PowerSeries.constantCoeff f‖ < 1 := hbd.trans_lt hy
  have hdvd : (p : ℤ_[p]) ∣ evalIwasawa f y - PowerSeries.constantCoeff f :=
    (padicInt_norm_lt_one_iff_p_dvd _).mp hlt
  rw [padicInt_p_dvd_iff_toZMod_eq_zero, map_sub, sub_eq_zero] at hdvd
  exact hdvd

theorem evalIwasawa_mul (f g : PowerSeries ℤ_[p]) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    evalIwasawa (f * g) y = evalIwasawa f y * evalIwasawa g y := by
  refine padicInt_eq_of_forall_norm_le_pow fun M => ?_
  have hy_le : ‖y‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := norm_le_p_inv_of_lt_one hy
  have hyM : ‖y‖ ^ M ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    calc ‖y‖ ^ M ≤ ((p : ℝ) ^ (-(1 : ℤ))) ^ M := pow_le_pow_left₀ (norm_nonneg _) hy_le M
      _ = (p : ℝ) ^ (-(M : ℤ)) := by rw [← zpow_natCast, ← zpow_mul]; congr 1; ring
  let Sf := ∑ k ∈ Finset.range M, PowerSeries.coeff k f * y ^ k
  let Sg := ∑ k ∈ Finset.range M, PowerSeries.coeff k g * y ^ k
  let Sfg := ∑ k ∈ Finset.range M, PowerSeries.coeff k (f * g) * y ^ k
  have h1 : ‖evalIwasawa (f * g) y - Sfg‖ ≤ (p : ℝ) ^ (-(M : ℤ)) :=
    (norm_evalIwasawa_sub_trunc_le (f * g) hy M).trans hyM
  have h2 : ‖evalIwasawa f y - Sf‖ ≤ (p : ℝ) ^ (-(M : ℤ)) :=
    (norm_evalIwasawa_sub_trunc_le f hy M).trans hyM
  have h3 : ‖evalIwasawa g y - Sg‖ ≤ (p : ℝ) ^ (-(M : ℤ)) :=
    (norm_evalIwasawa_sub_trunc_le g hy M).trans hyM
  have hprod_diff : ‖Sf * Sg - Sfg‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    have hSfSg : Sf * Sg = ∑ ab ∈ Finset.range M ×ˢ Finset.range M,
        (PowerSeries.coeff ab.1 f * PowerSeries.coeff ab.2 g) * y ^ (ab.1 + ab.2) := by
      dsimp only [Sf, Sg]
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun ab _ => by rw [pow_add]; ring
    have hSfg_eq : Sfg = ∑ ab ∈ (Finset.range M ×ˢ Finset.range M).filter (fun ab : ℕ × ℕ => ab.1 + ab.2 < M),
        (PowerSeries.coeff ab.1 f * PowerSeries.coeff ab.2 g) * y ^ (ab.1 + ab.2) := by
      dsimp only [Sfg]
      simp_rw [PowerSeries.coeff_mul, Finset.sum_mul]
      rw [Finset.sum_sigma']
      symm
      refine Finset.sum_bij (fun ab _ => ⟨ab.1 + ab.2, ab⟩) ?_ ?_ ?_ ?_
      · intro ab hab
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
        exact ⟨hab.2, trivial⟩
      · intro ab₁ _ ab₂ _ heq
        have h := congrArg Sigma.snd heq
        simpa using h
      · intro s hs
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hs
        refine ⟨s.2, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, by omega⟩
        · cases s with | mk k ab =>
          simp only [hs.2]
      · intro ab _; rfl
    rw [hSfSg, hSfg_eq]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M ×ˢ Finset.range M)
      (fun ab : ℕ × ℕ => ab.1 + ab.2 < M), add_sub_cancel_left]
    refine padicInt_norm_sum_le _ _ (by positivity) fun ab hab => ?_
    simp only [Finset.mem_filter, not_lt] at hab
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff ab.1 f * PowerSeries.coeff ab.2 g‖ * ‖y‖ ^ (ab.1 + ab.2)
        ≤ 1 * ‖y‖ ^ M :=
          mul_le_mul (PadicInt.norm_le_one _)
            (pow_le_pow_of_le_one (norm_nonneg _) hy.le hab.2)
            (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖y‖ ^ M := one_mul _
      _ ≤ (p : ℝ) ^ (-(M : ℤ)) := hyM
  have hdecomp : evalIwasawa (f * g) y - evalIwasawa f y * evalIwasawa g y =
      (evalIwasawa (f * g) y - Sfg) - (Sf * Sg - Sfg) -
      ((evalIwasawa f y - Sf) * evalIwasawa g y + Sf * (evalIwasawa g y - Sg)) := by ring
  rw [hdecomp]
  have h4 : ‖(evalIwasawa f y - Sf) * evalIwasawa g y + Sf * (evalIwasawa g y - Sg)‖ ≤
      (p : ℝ) ^ (-(M : ℤ)) := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖evalIwasawa f y - Sf‖ * ‖evalIwasawa g y‖
          ≤ (p : ℝ) ^ (-(M : ℤ)) * 1 :=
            mul_le_mul h2 (PadicInt.norm_le_one _) (norm_nonneg _) (by positivity)
        _ = (p : ℝ) ^ (-(M : ℤ)) := mul_one _
    · rw [norm_mul]
      calc ‖Sf‖ * ‖evalIwasawa g y - Sg‖
          ≤ 1 * (p : ℝ) ^ (-(M : ℤ)) :=
            mul_le_mul (PadicInt.norm_le_one _) h3 (norm_nonneg _) zero_le_one
        _ = (p : ℝ) ^ (-(M : ℤ)) := one_mul _
  refine (padicInt_norm_sub_le_max _ _).trans (max_le ?_ h4)
  exact (padicInt_norm_sub_le_max _ _).trans (max_le h1 hprod_diff)

theorem evalIwasawa_pow (f : PowerSeries ℤ_[p]) (n : ℕ) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    evalIwasawa (f ^ n) y = (evalIwasawa f y) ^ n := by
  induction n with
  | zero => simp [evalIwasawa_one]
  | succ n ih => rw [pow_succ, pow_succ, evalIwasawa_mul _ _ hy, ih]

theorem evalIwasawa_toPowerSeries (P : Polynomial ℤ_[p]) (y : ℤ_[p]) :
    evalIwasawa P.toPowerSeries y = P.eval y := by
  unfold evalIwasawa
  rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1))]
  · rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [toPowerSeries_coeff]
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [toPowerSeries_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem evalIwasawa_unit_ne_zero (u : (PowerSeries ℤ_[p])ˣ) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    evalIwasawa (u : PowerSeries ℤ_[p]) y ≠ 0 := by
  intro h0
  have h1 : evalIwasawa ((u : PowerSeries ℤ_[p]) * ((u⁻¹ : (PowerSeries ℤ_[p])ˣ) : PowerSeries ℤ_[p])) y = 1 := by
    rw [Units.mul_inv, evalIwasawa_one]
  rw [evalIwasawa_mul _ _ hy, h0, zero_mul] at h1
  exact zero_ne_one h1

/-- **STRASSMANN'S THEOREM (`iwasawa_eval_zeros_finite`)**:
every nonzero Iwasawa power series `f ∈ ℤ_[p][[T]]` has finitely many zeros in the open unit disk
`{y : ℤ_[p] | ‖y‖ < 1}`, and in fact **at most `iwasawaLambda f` zeros**! -/
theorem iwasawa_eval_zeros_finite {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ({y : ℤ_[p] | ‖y‖ < 1 ∧ evalIwasawa f y = 0}).Finite ∧
    ({y : ℤ_[p] | ‖y‖ < 1 ∧ evalIwasawa f y = 0}).ncard ≤ iwasawaLambda f := by
  obtain ⟨⟨P, u⟩, ⟨hP_dist, hP_deg, hfac⟩, _⟩ := weierstrass_preparation_Zp hf
  have hsub : {y : ℤ_[p] | ‖y‖ < 1 ∧ evalIwasawa f y = 0} ⊆ (P.roots.toFinset : Set ℤ_[p]) := by
    intro y ⟨hy, hfy⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP_dist.ne_zero, Polynomial.IsRoot]
    rw [hfac, evalIwasawa_mul _ _ hy, evalIwasawa_mul _ _ hy, evalIwasawa_pow _ _ hy,
      show (p : PowerSeries ℤ_[p]) = PowerSeries.C (p : ℤ_[p]) from (map_natCast PowerSeries.C p).symm,
      evalIwasawa_C, evalIwasawa_toPowerSeries] at hfy
    have h1 : (p : ℤ_[p]) ^ iwasawaMu f * P.eval y = 0 :=
      (mul_eq_zero.mp hfy).resolve_right (evalIwasawa_unit_ne_zero u hy)
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ padicInt_p_ne_zero)
  refine ⟨(P.roots.toFinset).finite_toSet.subset hsub, ?_⟩
  calc ({y : ℤ_[p] | ‖y‖ < 1 ∧ evalIwasawa f y = 0}).ncard
      ≤ (P.roots.toFinset : Set ℤ_[p]).ncard :=
        Set.ncard_le_ncard hsub (P.roots.toFinset).finite_toSet
    _ = P.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = iwasawaLambda f := hP_deg

/-- Finset version of Strassmann's Theorem: any finite set of zeros of nonzero `f ∈ ℤ_[p][[T]]`
in `{y : ℤ_[p] | ‖y‖ < 1}` has cardinality `≤ iwasawaLambda f`. -/
theorem iwasawa_eval_zeros_finset_card_le {f : PowerSeries ℤ_[p]} (hf : f ≠ 0)
    (s : Finset ℤ_[p]) (hs : ∀ y ∈ s, ‖y‖ < 1 ∧ evalIwasawa f y = 0) :
    s.card ≤ iwasawaLambda f := by
  obtain ⟨hfin, hcard⟩ := iwasawa_eval_zeros_finite hf
  have hsub : (s : Set ℤ_[p]) ⊆ {y : ℤ_[p] | ‖y‖ < 1 ∧ evalIwasawa f y = 0} := hs
  calc s.card = (s : Set ℤ_[p]).ncard := (Set.ncard_coe_finset s).symm
    _ ≤ ({y : ℤ_[p] | ‖y‖ < 1 ∧ evalIwasawa f y = 0}).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ iwasawaLambda f := hcard

end RingStructureAndStrassmann

/-! ## Section 4: Concrete Kummer Regularity / Irregular-Prime Criterion on `kubotaLeopoldtSeries` -/

section KummerRegularityCriterion

/-- A prime `p` is **regular** (Kummer) if `p` is an odd prime and `p` does not divide the
numerator of any even Bernoulli number `B_i` with `2 ≤ i ≤ p - 3`. -/
def IsRegularPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli i).num

lemma not_dvd_of_ge_two_le_sub_three {p i : ℕ} (hi2 : 2 ≤ i) (hip : i ≤ p - 3) :
    ¬ (p - 1) ∣ i :=
  Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

/-- The `p`-adic integer `B_i / i ∈ ℤ_[p]` for an odd prime `p` and `i ≥ 2` with `(p - 1) ∤ i`. -/
def bernoulliDivPadicInt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {i : ℕ}
    (hi2 : 2 ≤ i) (hndvd : ¬ (p - 1) ∣ i) : ℤ_[p] :=
  ⟨((bernoulli i / (i : ℚ) : ℚ) : ℚ_[p]), by
    have h := (bernoulli_div_norm_le_one p hp2 (k := i - 1) (by omega)
      (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)])).2
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h⟩

lemma padic_norm_intCast_lt_one_iff_dvd (p : ℕ) [Fact p.Prime] (z : ℤ) :
    ‖(z : ℚ_[p])‖ < 1 ↔ (p : ℤ) ∣ z := by
  have h1 : ‖(z : ℚ_[p])‖ = ‖(z : ℤ_[p])‖ := rfl
  rw [h1, padicInt_norm_lt_one_iff_p_dvd, padicInt_p_dvd_iff_toZMod_eq_zero,
    map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma padic_norm_intCast_eq_one_iff_not_dvd (p : ℕ) [Fact p.Prime] (z : ℤ) :
    ‖(z : ℚ_[p])‖ = 1 ↔ ¬ (p : ℤ) ∣ z := by
  have hle : ‖(z : ℚ_[p])‖ ≤ 1 := Padic.norm_int_le_one z
  rw [← padic_norm_intCast_lt_one_iff_dvd p z]
  constructor
  · intro h; linarith
  · intro h; exact le_antisymm hle (not_lt.mp h)

/-- Exact equivalence for odd prime `p` and `2 ≤ i ≤ p - 3`:
`(p : ℤ_[p]) ∣ (B_i / i)` iff `(p : ℤ) ∣ (bernoulli i).num`. -/
theorem p_dvd_bernoulliDivPadicInt_iff_dvd_num (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {i : ℕ} (hi2 : 2 ≤ i) (hip : i ≤ p - 3) :
    (p : ℤ_[p]) ∣ bernoulliDivPadicInt p hp2 hi2 (not_dvd_of_ge_two_le_sub_three hi2 hip) ↔
      (p : ℤ) ∣ (bernoulli i).num := by
  have hp : p.Prime := Fact.out
  have hndvd_i : ¬ p ∣ i := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hi_norm : ‖(i : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr hndvd_i)
  have hdiv_norm : ‖((bernoulli i / (i : ℚ) : ℚ) : ℚ_[p])‖ = ‖(bernoulli i : ℚ_[p])‖ := by
    rw [Rat.cast_div, Rat.cast_natCast, norm_div, hi_norm, div_one]
  have hB_le : ‖(bernoulli i : ℚ_[p])‖ ≤ 1 := by
    rw [← hdiv_norm]
    exact PadicInt.norm_le_one (bernoulliDivPadicInt p hp2 hi2 (not_dvd_of_ge_two_le_sub_three hi2 hip))
  have hden_ndvd : ¬ p ∣ (bernoulli i).den := by
    intro hden_dvd
    have hcop : Nat.Coprime (bernoulli i).num.natAbs (bernoulli i).den := (bernoulli i).reduced
    have hnum_ndvd_nat : ¬ p ∣ (bernoulli i).num.natAbs := fun hnum_dvd =>
      hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hnum_dvd hden_dvd)
    have hnum_ndvd : ¬ (p : ℤ) ∣ (bernoulli i).num := by
      intro hd
      exact hnum_ndvd_nat (Int.natCast_dvd.mp hd)
    have hnum_norm : ‖((bernoulli i).num : ℚ_[p])‖ = 1 :=
      (padic_norm_intCast_eq_one_iff_not_dvd p _).mpr hnum_ndvd
    have hden_lt : ‖((bernoulli i).den : ℚ_[p])‖ < 1 := by
      have := (padic_norm_intCast_lt_one_iff_dvd p ((bernoulli i).den : ℤ)).mpr
        (Int.natCast_dvd_natCast.mpr hden_dvd)
      simpa using this
    have hden_pos : 0 < ‖((bernoulli i).den : ℚ_[p])‖ :=
      norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (bernoulli i).den_nz)
    have hq : (bernoulli i : ℚ_[p]) = ((bernoulli i).num : ℚ_[p]) / ((bernoulli i).den : ℚ_[p]) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    have hgt1 : 1 < ‖(bernoulli i : ℚ_[p])‖ := by
      rw [hq, norm_div, hnum_norm, one_div]
      exact one_lt_inv_iff₀.mpr ⟨hden_pos, hden_lt⟩
    linarith
  have hden_norm : ‖((bernoulli i).den : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr (hp.coprime_iff_not_dvd.mpr hden_ndvd)
  have hB_eq_num : ‖(bernoulli i : ℚ_[p])‖ = ‖((bernoulli i).num : ℚ_[p])‖ := by
    have hq : (bernoulli i : ℚ_[p]) = ((bernoulli i).num : ℚ_[p]) / ((bernoulli i).den : ℚ_[p]) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    rw [hq, norm_div, hden_norm, div_one]
  rw [← padicInt_norm_lt_one_iff_p_dvd]
  change ‖((bernoulli i / (i : ℚ) : ℚ) : ℚ_[p])‖ < 1 ↔ _
  rw [hdiv_norm, hB_eq_num, padic_norm_intCast_lt_one_iff_dvd]

/-- **KUMMER UNIT CRITERION ON `kubotaLeopoldtSeries` (`kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli`)**:
for an odd prime `p`, regularizing parameter `c` (`¬ p ∣ c`), branch `2 ≤ i ≤ p - 3` with
`(c : ZMod p) ^ i ≠ 1` (automatic for every primitive root `c` mod `p`):
`kubotaLeopoldtSeries p hp2 c hc (i - 1)` is a unit in `ℤ_[p][[T]]` (i.e. `μ = 0 ∧ λ = 0`)
IFF `¬ (p : ℤ_[p]) ∣ (B_i / i)`! -/
theorem kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (c : ℕ) (hc : ¬ p ∣ c) {i : ℕ} (hi2 : 2 ≤ i) (hip : i ≤ p - 3)
    (hci : (c : ZMod p) ^ i ≠ 1) :
    IsUnit (kubotaLeopoldtSeries p hp2 c hc (i - 1)) ↔
      ¬ (p : ℤ_[p]) ∣ bernoulliDivPadicInt p hp2 hi2 (not_dvd_of_ge_two_le_sub_three hi2 hip) := by
  let F := kubotaLeopoldtSeries p hp2 c hc (i - 1)
  let y : ℤ_[p] := padicPowOneAdd (p : ℤ_[p]) ((i - 1 : ℕ) : ℤ_[p]) - 1
  have hy : ‖y‖ < 1 := norm_padicPowOneAdd_prime_sub_one_lt_one _
  have heval := evalIwasawa_kubotaLeopoldtSeries_nat p hp2 c hc (i - 1) (i - 1) Nat.ModEq.rfl
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i)] at heval
  have hres : PadicInt.toZMod (evalIwasawa F y) = PadicInt.toZMod (PowerSeries.constantCoeff F) :=
    toZMod_evalIwasawa F hy
  have h1p_norm : ‖(((1 - (p : ℚ) ^ (i - 1)) : ℚ) : ℚ_[p])‖ = 1 := by
    have hres1 : PadicInt.toZMod (1 - (p : ℤ_[p]) ^ (i - 1)) ≠ 0 := by
      rw [map_sub, map_one, map_pow, map_natCast, ZMod.natCast_self, zero_pow (by omega), sub_zero]
      exact one_ne_zero
    have hu := PadicInt.isUnit_iff.mp (padicInt_isUnit_of_toZMod_ne_zero hres1)
    have hcoe : ((1 - (p : ℤ_[p]) ^ (i - 1) : ℤ_[p]) : ℚ_[p]) = (((1 - (p : ℚ) ^ (i - 1)) : ℚ) : ℚ_[p]) := by
      push_cast; rfl
    rwa [← hcoe]
  have h1c_norm : ‖(((1 - (c : ℚ) ^ i) : ℚ) : ℚ_[p])‖ = 1 := by
    have hres1 : PadicInt.toZMod (1 - (c : ℤ_[p]) ^ i) ≠ 0 := by
      rw [map_sub, map_one, map_pow, map_natCast, sub_ne_zero]
      exact hci.symm
    have hu := PadicInt.isUnit_iff.mp (padicInt_isUnit_of_toZMod_ne_zero hres1)
    have hcoe : ((1 - (c : ℤ_[p]) ^ i : ℤ_[p]) : ℚ_[p]) = (((1 - (c : ℚ) ^ i) : ℚ) : ℚ_[p]) := by
      push_cast; rfl
    rwa [← hcoe]
  have hnorm_eq : ‖evalIwasawa F y‖ =
      ‖bernoulliDivPadicInt p hp2 hi2 (not_dvd_of_ge_two_le_sub_three hi2 hip)‖ := by
    change ‖((evalIwasawa F y : ℤ_[p]) : ℚ_[p])‖ = ‖((bernoulli i / (i : ℚ) : ℚ) : ℚ_[p])‖
    rw [heval, Rat.cast_mul, Rat.cast_mul, norm_mul, norm_mul, h1p_norm, h1c_norm, one_mul, one_mul]
  rw [isUnit_iwasawaAlg_iff, padicInt_p_dvd_iff_toZMod_eq_zero, ← hres,
    ← padicInt_p_dvd_iff_toZMod_eq_zero, ← padicInt_norm_eq_one_iff_not_p_dvd, hnorm_eq,
    padicInt_norm_eq_one_iff_not_p_dvd]

/-- Equivalent form in terms of the Bernoulli numerator `(bernoulli i).num`. -/
theorem kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli_num (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (c : ℕ) (hc : ¬ p ∣ c) {i : ℕ} (hi2 : 2 ≤ i) (hip : i ≤ p - 3)
    (hci : (c : ZMod p) ^ i ≠ 1) :
    IsUnit (kubotaLeopoldtSeries p hp2 c hc (i - 1)) ↔ ¬ (p : ℤ) ∣ (bernoulli i).num := by
  rw [kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli p hp2 c hc hi2 hip hci,
    p_dvd_bernoulliDivPadicInt_iff_dvd_num p hp2 hi2 hip]

/-- **KUMMER REGULARITY CHARACTERIZATION (`regular_prime_iff_all_branches_unit`)**:
for any odd prime `p` and any primitive root `c` mod `p`, `p` is regular IFF every non-trivial
even branch `i ∈ {2, 4, ..., p - 3}` of `kubotaLeopoldtSeries` is a unit in `ℤ_[p][[T]]`
(with `iwasawaMu = 0` and `iwasawaLambda = 0`). -/
theorem regular_prime_iff_all_branches_unit (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (c : ℕ) (hc : ¬ p ∣ c) (hprim : ∀ r : ℕ, ¬ (p - 1) ∣ r → (c : ZMod p) ^ r ≠ 1) :
    IsRegularPrime p ↔
      ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
        IsUnit (kubotaLeopoldtSeries p hp2 c hc (i - 1)) ∧
        iwasawaMu (kubotaLeopoldtSeries p hp2 c hc (i - 1)) = 0 ∧
        iwasawaLambda (kubotaLeopoldtSeries p hp2 c hc (i - 1)) = 0 := by
  have hp : p.Prime := Fact.out
  unfold IsRegularPrime
  constructor
  · rintro ⟨_, _, hreg⟩ i heven hi2 hip
    have hci : (c : ZMod p) ^ i ≠ 1 := hprim i (not_dvd_of_ge_two_le_sub_three hi2 hip)
    have hu : IsUnit (kubotaLeopoldtSeries p hp2 c hc (i - 1)) :=
      (kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli_num p hp2 c hc hi2 hip hci).mpr
        (hreg i heven hi2 hip)
    exact ⟨hu, iwasawaMu_of_isUnit hu, iwasawaLambda_of_isUnit hu⟩
  · intro hall
    refine ⟨hp, hp2, fun i heven hi2 hip => ?_⟩
    have hci : (c : ZMod p) ^ i ≠ 1 := hprim i (not_dvd_of_ge_two_le_sub_three hi2 hip)
    exact (kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli_num p hp2 c hc hi2 hip hci).mp
      (hall i heven hi2 hip).1

end KummerRegularityCriterion

/-! ## Section 5: Concrete Bernoulli Computations (`B_2`..`B_32`), Regular Primes `3, 5, 7, 11, 13`, & Irregular `p = 37` -/

section ConcreteComputations

private lemma sum_range_odd_zero (f : ℕ → ℚ) (hf : ∀ j : ℕ, f (2 * j + 3) = 0) :
    ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.range (2 * m - 1), f (k + 2) = ∑ j ∈ Finset.range m, f (2 * j + 2)
  | 0, hm => absurd hm (by omega)
  | 1, _ => by simp
  | m + 2, _ => by
      have ih := sum_range_odd_zero f hf (m + 1) (by omega)
      have h1 : 2 * (m + 2) - 1 = (2 * (m + 1) - 1) + 1 + 1 := by omega
      rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hodd : 2 * (m + 1) - 1 + 2 = 2 * m + 3 := by omega
      have heven : 2 * (m + 1) - 1 + 1 + 2 = 2 * (m + 1) + 2 := by omega
      rw [hodd, hf m, add_zero, heven, ← Finset.sum_range_succ]

/-- Even-only Bernoulli recurrence:
`1 - (2m + 1)/2 + ∑_{j < m} C(2m + 1, 2j + 2) * B_{2j + 2} = 0` for all `m ≥ 1`. -/
private lemma sum_bernoulli_even (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℚ) - ((2 * m + 1 : ℕ) : ℚ) / 2 +
      ∑ j ∈ Finset.range m,
        (((2 * m + 1).choose (2 * j + 2) : ℕ) : ℚ) * bernoulli (2 * j + 2) = 0 := by
  have hsum := sum_bernoulli (2 * m + 1)
  rw [if_neg (by omega)] at hsum
  have h2 : 2 * m + 1 = (2 * m - 1) + 1 + 1 := by omega
  have hsplit : ∑ k ∈ Finset.range (2 * m + 1), (((2 * m + 1).choose k : ℕ) : ℚ) * bernoulli k =
      (1 : ℚ) - ((2 * m + 1 : ℕ) : ℚ) / 2 +
      ∑ k ∈ Finset.range (2 * m - 1),
        (((2 * m + 1).choose (k + 2) : ℕ) : ℚ) * bernoulli (k + 2) := by
    conv_lhs => rw [h2, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, bernoulli_zero, mul_one,
      Nat.choose_one_right, bernoulli_one]
    have hcast : (((2 * m - 1 + 1 + 1 : ℕ) : ℚ)) = ((2 * m + 1 : ℕ) : ℚ) := by congr 1; omega
    have hcongr : ∑ x ∈ Finset.range (2 * m - 1),
        (((2 * m - 1 + 1 + 1).choose (x + 1 + 1) : ℕ) : ℚ) * bernoulli (x + 1 + 1) =
        ∑ k ∈ Finset.range (2 * m - 1),
          (((2 * m + 1).choose (k + 2) : ℕ) : ℚ) * bernoulli (k + 2) := by
      refine Finset.sum_congr rfl fun k _ => by rw [← h2]
    rw [hcast, hcongr]
    ring
  rw [hsplit] at hsum
  have heven := sum_range_odd_zero
    (fun r => (((2 * m + 1).choose r : ℕ) : ℚ) * bernoulli r)
    (fun j => by rw [bernoulli_eq_zero_of_odd ⟨j + 1, by omega⟩ (by omega), mul_zero])
    m hm
  rwa [heven] at hsum

private lemma sum_bernoulli_even_fact (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℚ) - ((2 * m + 1 : ℕ) : ℚ) / 2 +
      ∑ j ∈ Finset.range m,
        ((((2 * m + 1).factorial /
          ((2 * j + 2).factorial * (2 * m + 1 - (2 * j + 2)).factorial) : ℕ)) : ℚ) *
          bernoulli (2 * j + 2) = 0 := by
  have h := sum_bernoulli_even m hm
  refine (Eq.trans ?_ h)
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < m := Finset.mem_range.mp hj
  rw [Nat.choose_eq_factorial_div_factorial (by omega)]

lemma bernoulli_2 : bernoulli 2 = 1 / 6 := by
  rw [bernoulli_two, one_div]

lemma bernoulli_4 : bernoulli 4 = -1 / 30 := by
  have h := sum_bernoulli_even_fact 2 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linarith

lemma bernoulli_6 : bernoulli 6 = 1 / 42 := by
  have h := sum_bernoulli_even_fact 3 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4] at h
  linarith

lemma bernoulli_8 : bernoulli 8 = -1 / 30 := by
  have h := sum_bernoulli_even_fact 4 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6] at h
  linarith

lemma bernoulli_10 : bernoulli 10 = 5 / 66 := by
  have h := sum_bernoulli_even_fact 5 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8] at h
  linarith

lemma bernoulli_12 : bernoulli 12 = -691 / 2730 := by
  have h := sum_bernoulli_even_fact 6 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10] at h
  linarith

lemma bernoulli_14 : bernoulli 14 = 7 / 6 := by
  have h := sum_bernoulli_even_fact 7 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12] at h
  linarith

lemma bernoulli_16 : bernoulli 16 = -3617 / 510 := by
  have h := sum_bernoulli_even_fact 8 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14] at h
  linarith

lemma bernoulli_18 : bernoulli 18 = 43867 / 798 := by
  have h := sum_bernoulli_even_fact 9 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16] at h
  linarith

lemma bernoulli_20 : bernoulli 20 = -174611 / 330 := by
  have h := sum_bernoulli_even_fact 10 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18] at h
  linarith

lemma bernoulli_22 : bernoulli 22 = 854513 / 138 := by
  have h := sum_bernoulli_even_fact 11 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18, bernoulli_20] at h
  linarith

lemma bernoulli_24 : bernoulli 24 = -236364091 / 2730 := by
  have h := sum_bernoulli_even_fact 12 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18, bernoulli_20, bernoulli_22] at h
  linarith

lemma bernoulli_26 : bernoulli 26 = 8553103 / 6 := by
  have h := sum_bernoulli_even_fact 13 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18, bernoulli_20, bernoulli_22, bernoulli_24] at h
  linarith

lemma bernoulli_28 : bernoulli 28 = -23749461029 / 870 := by
  have h := sum_bernoulli_even_fact 14 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18, bernoulli_20, bernoulli_22, bernoulli_24, bernoulli_26] at h
  linarith

lemma bernoulli_30 : bernoulli 30 = 8615841276005 / 14322 := by
  have h := sum_bernoulli_even_fact 15 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18, bernoulli_20, bernoulli_22, bernoulli_24, bernoulli_26,
    bernoulli_28] at h
  linarith

lemma bernoulli_32 : bernoulli 32 = -7709321041217 / 510 := by
  have h := sum_bernoulli_even_fact 16 (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [bernoulli_4, bernoulli_6, bernoulli_8, bernoulli_10, bernoulli_12, bernoulli_14,
    bernoulli_16, bernoulli_18, bernoulli_20, bernoulli_22, bernoulli_24, bernoulli_26,
    bernoulli_28, bernoulli_30] at h
  linarith

/-- Clean numerator extraction for reduced fractions `a / b : ℚ`. -/
private lemma rat_num_of_div {a : ℤ} {b : ℕ} (hb : 0 < b) (hcop : Nat.Coprime a.natAbs b) :
    ((a : ℚ) / (b : ℚ)).num = a := by
  have hmk : ((a : ℚ) / (b : ℚ)) = Rat.mk' a b hb.ne' hcop := by
    have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    apply (div_eq_iff hbQ).mpr
    have hnum := Rat.num_div_den (Rat.mk' a b hb.ne' hcop)
    have h1 : (Rat.mk' a b hb.ne' hcop).num = a := rfl
    have h2 : (Rat.mk' a b hb.ne' hcop).den = b := rfl
    rw [h1, h2] at hnum
    exact (div_eq_iff hbQ).mp hnum
  rw [hmk]

lemma bernoulli_2_num : (bernoulli 2).num = 1 := by
  rw [bernoulli_2]
  exact rat_num_of_div (a := 1) (b := 6) (by decide) (by decide)

lemma bernoulli_4_num : (bernoulli 4).num = -1 := by
  rw [bernoulli_4]
  exact rat_num_of_div (a := -1) (b := 30) (by decide) (by decide)

lemma bernoulli_6_num : (bernoulli 6).num = 1 := by
  rw [bernoulli_6]
  exact rat_num_of_div (a := 1) (b := 42) (by decide) (by decide)

lemma bernoulli_8_num : (bernoulli 8).num = -1 := by
  rw [bernoulli_8]
  exact rat_num_of_div (a := -1) (b := 30) (by decide) (by decide)

lemma bernoulli_10_num : (bernoulli 10).num = 5 := by
  rw [bernoulli_10]
  exact rat_num_of_div (a := 5) (b := 66) (by decide) (by decide)

lemma bernoulli_32_num : (bernoulli 32).num = -7709321041217 := by
  rw [bernoulli_32]
  exact rat_num_of_div (a := -7709321041217) (b := 510) (by decide) (by decide)

/-- Helper to check primitive-root non-vanishing on `r` with `(p - 1) ∤ r` via finite `decide`. -/
private lemma prim_of_fin_check (p c : ℕ) [Fact p.Prime] (hc : ¬ p ∣ c)
    (hfin : ∀ a : Fin (p - 1), a.val ≠ 0 → (c : ZMod p) ^ a.val ≠ 1) :
    ∀ r : ℕ, ¬ (p - 1) ∣ r → (c : ZMod p) ^ r ≠ 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hc0 : (c : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hc
  have hfermat : (c : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hc0
  intro r hr
  have hmod_ne : r % (p - 1) ≠ 0 := fun h0 => hr (Nat.dvd_of_mod_eq_zero h0)
  have hdiv : r = (p - 1) * (r / (p - 1)) + r % (p - 1) := (Nat.div_add_mod r (p - 1)).symm
  rw [hdiv, pow_add, pow_mul, hfermat, one_pow, one_mul]
  exact hfin ⟨r % (p - 1), Nat.mod_lt r hp1⟩ hmod_ne

private lemma prim_fin_3 : ∀ a : Fin (3 - 1), a.val ≠ 0 → (2 : ZMod 3) ^ a.val ≠ 1 := by decide
private lemma prim_fin_5 : ∀ a : Fin (5 - 1), a.val ≠ 0 → (2 : ZMod 5) ^ a.val ≠ 1 := by decide
private lemma prim_fin_7 : ∀ a : Fin (7 - 1), a.val ≠ 0 → (3 : ZMod 7) ^ a.val ≠ 1 := by decide
private lemma prim_fin_11 : ∀ a : Fin (11 - 1), a.val ≠ 0 → (2 : ZMod 11) ^ a.val ≠ 1 := by decide
private lemma prim_fin_13 : ∀ a : Fin (13 - 1), a.val ≠ 0 → (2 : ZMod 13) ^ a.val ≠ 1 := by decide
private lemma pow_two_32_ne_one_mod_37 : ((2 : ZMod 37) ^ 32) ≠ 1 := by decide

/-- `p = 3` is a regular prime, and all non-trivial even branches of `kubotaLeopoldtSeries 3`
are units (`μ = 0, λ = 0`). -/
theorem regular_prime_3 :
    IsRegularPrime 3 ∧
      ∀ [Fact (Nat.Prime 3)] (i : ℕ), Even i → 2 ≤ i → i ≤ 3 - 3 →
        IsUnit (kubotaLeopoldtSeries 3 (by decide) 2 (by decide) (i - 1)) ∧
        iwasawaMu (kubotaLeopoldtSeries 3 (by decide) 2 (by decide) (i - 1)) = 0 ∧
        iwasawaLambda (kubotaLeopoldtSeries 3 (by decide) 2 (by decide) (i - 1)) = 0 := by
  have hreg : IsRegularPrime 3 := ⟨by decide, by decide, fun i _ hi2 hip => by omega⟩
  refine ⟨hreg, fun i => ?_⟩
  exact (regular_prime_iff_all_branches_unit 3 (by decide) 2 (by decide)
    (prim_of_fin_check 3 2 (by decide) prim_fin_3)).mp hreg i

/-- `p = 5` is a regular prime, and all non-trivial even branches (`i = 2`) of
`kubotaLeopoldtSeries 5` (with primitive root `c = 2`) are units (`μ = 0, λ = 0`). -/
theorem regular_prime_5 :
    IsRegularPrime 5 ∧
      ∀ [Fact (Nat.Prime 5)] (i : ℕ), Even i → 2 ≤ i → i ≤ 5 - 3 →
        IsUnit (kubotaLeopoldtSeries 5 (by decide) 2 (by decide) (i - 1)) ∧
        iwasawaMu (kubotaLeopoldtSeries 5 (by decide) 2 (by decide) (i - 1)) = 0 ∧
        iwasawaLambda (kubotaLeopoldtSeries 5 (by decide) 2 (by decide) (i - 1)) = 0 := by
  have hreg : IsRegularPrime 5 := by
    refine ⟨by decide, by decide, fun i _ hi2 hip => ?_⟩
    obtain rfl : i = 2 := by omega
    rw [bernoulli_2_num]
    decide
  refine ⟨hreg, fun i => ?_⟩
  exact (regular_prime_iff_all_branches_unit 5 (by decide) 2 (by decide)
    (prim_of_fin_check 5 2 (by decide) prim_fin_5)).mp hreg i

/-- `p = 7` is a regular prime, and all non-trivial even branches (`i = 2, 4`) of
`kubotaLeopoldtSeries 7` (with primitive root `c = 3`) are units (`μ = 0, λ = 0`). -/
theorem regular_prime_7 :
    IsRegularPrime 7 ∧
      ∀ [Fact (Nat.Prime 7)] (i : ℕ), Even i → 2 ≤ i → i ≤ 7 - 3 →
        IsUnit (kubotaLeopoldtSeries 7 (by decide) 3 (by decide) (i - 1)) ∧
        iwasawaMu (kubotaLeopoldtSeries 7 (by decide) 3 (by decide) (i - 1)) = 0 ∧
        iwasawaLambda (kubotaLeopoldtSeries 7 (by decide) 3 (by decide) (i - 1)) = 0 := by
  have hreg : IsRegularPrime 7 := by
    refine ⟨by decide, by decide, fun i heven hi2 hip => ?_⟩
    obtain ⟨m, rfl⟩ := heven
    have hm : m = 1 ∨ m = 2 := by omega
    rcases hm with rfl | rfl
    · rw [show 1 + 1 = 2 from rfl, bernoulli_2_num]; decide
    · rw [show 2 + 2 = 4 from rfl, bernoulli_4_num]; decide
  refine ⟨hreg, fun i => ?_⟩
  exact (regular_prime_iff_all_branches_unit 7 (by decide) 3 (by decide)
    (prim_of_fin_check 7 3 (by decide) prim_fin_7)).mp hreg i

/-- `p = 11` is a regular prime, and all non-trivial even branches (`i = 2, 4, 6, 8`) of
`kubotaLeopoldtSeries 11` (with primitive root `c = 2`) are units (`μ = 0, λ = 0`). -/
theorem regular_prime_11 :
    IsRegularPrime 11 ∧
      ∀ [Fact (Nat.Prime 11)] (i : ℕ), Even i → 2 ≤ i → i ≤ 11 - 3 →
        IsUnit (kubotaLeopoldtSeries 11 (by decide) 2 (by decide) (i - 1)) ∧
        iwasawaMu (kubotaLeopoldtSeries 11 (by decide) 2 (by decide) (i - 1)) = 0 ∧
        iwasawaLambda (kubotaLeopoldtSeries 11 (by decide) 2 (by decide) (i - 1)) = 0 := by
  have hreg : IsRegularPrime 11 := by
    refine ⟨by decide, by decide, fun i heven hi2 hip => ?_⟩
    obtain ⟨m, rfl⟩ := heven
    have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases hm with rfl | rfl | rfl | rfl
    · rw [show 1 + 1 = 2 from rfl, bernoulli_2_num]; decide
    · rw [show 2 + 2 = 4 from rfl, bernoulli_4_num]; decide
    · rw [show 3 + 3 = 6 from rfl, bernoulli_6_num]; decide
    · rw [show 4 + 4 = 8 from rfl, bernoulli_8_num]; decide
  refine ⟨hreg, fun i => ?_⟩
  exact (regular_prime_iff_all_branches_unit 11 (by decide) 2 (by decide)
    (prim_of_fin_check 11 2 (by decide) prim_fin_11)).mp hreg i

/-- `p = 13` is a regular prime, and all non-trivial even branches (`i = 2, 4, 6, 8, 10`) of
`kubotaLeopoldtSeries 13` (with primitive root `c = 2`) are units (`μ = 0, λ = 0`). -/
theorem regular_prime_13 :
    IsRegularPrime 13 ∧
      ∀ [Fact (Nat.Prime 13)] (i : ℕ), Even i → 2 ≤ i → i ≤ 13 - 3 →
        IsUnit (kubotaLeopoldtSeries 13 (by decide) 2 (by decide) (i - 1)) ∧
        iwasawaMu (kubotaLeopoldtSeries 13 (by decide) 2 (by decide) (i - 1)) = 0 ∧
        iwasawaLambda (kubotaLeopoldtSeries 13 (by decide) 2 (by decide) (i - 1)) = 0 := by
  have hreg : IsRegularPrime 13 := by
    refine ⟨by decide, by decide, fun i heven hi2 hip => ?_⟩
    obtain ⟨m, rfl⟩ := heven
    have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · rw [show 1 + 1 = 2 from rfl, bernoulli_2_num]; decide
    · rw [show 2 + 2 = 4 from rfl, bernoulli_4_num]; decide
    · rw [show 3 + 3 = 6 from rfl, bernoulli_6_num]; decide
    · rw [show 4 + 4 = 8 from rfl, bernoulli_8_num]; decide
    · rw [show 5 + 5 = 10 from rfl, bernoulli_10_num]; decide
  refine ⟨hreg, fun i => ?_⟩
  exact (regular_prime_iff_all_branches_unit 13 (by decide) 2 (by decide)
    (prim_of_fin_check 13 2 (by decide) prim_fin_13)).mp hreg i

/-- **EXACT `p = 37` IRREGULAR-PRIME BERNOULLI WITNESS (`irregular_prime_37_bernoulli32`)**:
1. `37 ∣ (bernoulli 32).num` (since `B_32 = -7709321041217 / 510` and `7709321041217 = 37 * 208360028141`),
2. `¬ IsRegularPrime 37`,
3. On the `i = 32` branch (`kubotaLeopoldtSeries 37 _ 2 _ 31`), the Kubota–Leopoldt Iwasawa power
   series is **nonzero**, **not a unit**, and satisfies **`1 ≤ iwasawaMu ∨ 1 ≤ iwasawaLambda`**! -/
theorem irregular_prime_37_bernoulli32 :
    (37 : ℤ) ∣ (bernoulli 32).num ∧
    ¬ IsRegularPrime 37 ∧
    ∀ [Fact (Nat.Prime 37)],
      let F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
      F ≠ 0 ∧ ¬ IsUnit F ∧ (1 ≤ iwasawaMu F ∨ 1 ≤ iwasawaLambda F) := by
  have h37_dvd : (37 : ℤ) ∣ (bernoulli 32).num := by
    rw [bernoulli_32_num]
    decide
  have hnot_reg : ¬ IsRegularPrime 37 := by
    rintro ⟨_, _, hreg⟩
    exact hreg 32 ⟨16, rfl⟩ (by decide) (by decide) h37_dvd
  refine ⟨h37_dvd, hnot_reg, ?_⟩
  intro _
  set F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
  have hF_ne : F ≠ 0 := by
    intro hF0
    have hev := evalIwasawa_kubotaLeopoldtSeries_nat 37 (by decide) 2 (by decide) 31 31 Nat.ModEq.rfl
    change ((evalIwasawa F (padicPowOneAdd (37 : ℤ_[37]) (31 : ℤ_[37]) - 1) : ℤ_[37]) : ℚ_[37]) = _ at hev
    rw [hF0, evalIwasawa_zero, PadicInt.coe_zero] at hev
    have hrhs_ne : (((1 - (37 : ℚ) ^ 31) * (1 - (2 : ℚ) ^ 32) *
        (bernoulli 32 / ((32 : ℕ) : ℚ)) : ℚ) : ℚ_[37]) ≠ 0 := by
      have hq_ne : ((1 - (37 : ℚ) ^ 31) * (1 - (2 : ℚ) ^ 32) *
          (bernoulli 32 / ((32 : ℕ) : ℚ)) : ℚ) ≠ 0 := by
        rw [bernoulli_32]
        norm_num
      exact Rat.cast_ne_zero.mpr hq_ne
    exact hrhs_ne hev.symm
  have hF_not_unit : ¬ IsUnit F := by
    rw [kubotaLeopoldtSeries_isUnit_iff_not_dvd_bernoulli_num 37 (by decide) 2 (by decide)
      (i := 32) (by decide) (by decide) pow_two_32_ne_one_mod_37]
    exact not_not.mpr h37_dvd
  have hinv_pos : 1 ≤ iwasawaMu F ∨ 1 ≤ iwasawaLambda F := by
    by_contra h
    push Not at h
    have hμ0 : iwasawaMu F = 0 := Nat.lt_one_iff.mp h.1
    have hlam0 : iwasawaLambda F = 0 := Nat.lt_one_iff.mp h.2
    exact hF_not_unit ((isUnit_iff_iwasawaMu_zero_and_iwasawaLambda_zero hF_ne).mpr ⟨hμ0, hlam0⟩)
  exact ⟨hF_ne, hF_not_unit, hinv_pos⟩

end ConcreteComputations

end RHDirect.Stage8IwasawaWeierstrass
