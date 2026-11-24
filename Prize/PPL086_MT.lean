import RHDirect.MaynardTaoUnconditional
import RHDirect.Stage11LinnikUnconditional
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# PPL 086 (Erdős Problem #470): Maynard–Tao, Linnik, Exact Barriers, & Generalized Primitive Weird Families

This self-contained module (zero edits to any sibling file; native Mathlib `Nat.divisors`,
`Nat.properDivisors`, `Nat.Prime` + precompiled `Arithmetica4` crown theorems) establishes:

## Part I: Exact Unconditional Barriers Explaining the Erdős #470 Part A Obstruction
1. `isPseudoperfect_two_pow_pq_of_le_sub_two`:
   For every `k ≥ 1` and primes `2^(k+1) < p < q ≤ 2^(k+2) - 2`, `2^k * p * q` is **ALWAYS pseudoperfect**.
2. `isDeficient_two_pow_pq_of_ge_sub_one`:
   For every `k ≥ 1` and primes `2^(k+2) - 1 ≤ p < q`, `2^k * p * q` is **ALWAYS deficient**.
3. `straddling_of_isWeird_two_pow_pq` (**Exact Straddling Theorem for `2^k * p * q`**):
   Every weird number `2^k * p * q` (`k ≥ 1`, `p < q` primes) MUST straddle `2^(k+2) - 1`:
   `2^(k+1) < p ∧ p < 2^(k+2) - 1 ∧ 2^(k+2) - 1 ≤ q`.
   Thus arbitrary Maynard–Tao bounded-gap prime pairs cannot produce weird `2^k * p * q` unless
   they straddle `2^(k+2) - 1`.
4. `gap0_interval_sqrt_barrier` (**Universal `√X` Prime-Gap Barrier for ALL Deficient `D`**):
   For ANY deficient integer `D ≥ 1` (`e = 2D - σ(D) ≥ 1`) and ANY prime `p` with `D * p` deficient
   (`e' = e * p - σ(D) ≥ 1`), the Gap-0 interval for `q` (`0 < δ(D * p * q) < p`) has length `L = p / e'`
   and scale `X = σ(D) * (p + 1) / e'` satisfying `(L - 1/e)^2 < X / (e * e')` and `L < 1 + √X`.
5. `mod_r_obstruction_abundance_barrier` (**Congruence-Obstruction Barrier**):
   For ANY deficient `D`, prime `r`, and `m`-element Finset `P` of primes `> r`, the anti-wraparound
   condition `2^m * σ(D) < r` forces `D * r * ∏ p ∈ P, p` to be **strictly deficient**.

## Part II: Brand-New Generalized Primitive Weird Constructions & Weakened Conditional Infinitude
6. `isPrimitiveWeird_two_pow_pq_of_mod_p_ge` (**Unbalanced Mod-`p` Primitive Weird Criterion**):
   If `2^(k+1) < p < q`, `0 < δ < q`, and `2^(k+1) ≤ δ % p`, then `2^k * p * q` is primitive weird.
7. `isPrimitiveWeird_exact_ap_family` (**Exact Arithmetic-Progression Primitive Weird Family**):
   For `k ≥ 2`, `1 ≤ j < k`, `R = 2^(k+1)`, `d = 2^j`, if `p = R + d - 1` is prime and
   `q = (R / d) * (R + d - 2) - 1 - t * p` is prime with `t * d * p + R < q`, then `2^k * p * q`
   is primitive weird with exact abundance `δ = t * d * p + R`.
8. `isPrimitiveWeird_multi_prime_gap0` (**Amato–Hasler–Melfi–Parton Multi-Prime Gap-0 Theorem**):
   Generalizes Kravitz to arbitrarily many odd prime factors `2^k * (∏ p ∈ P, p) * q`.
9. Seven kernel-verified primitive weird numbers (ZERO `native_decide`):
   - `isPrimitiveWeird_70` (`2^1 * 5 * 7`)
   - `isPrimitiveWeird_4030` (`2^1 * 5 * 13 * 31`, smallest 4-prime PWN)
   - `isPrimitiveWeird_9272` (`2^3 * 19 * 61`, non-Kravitz unbalanced mod-`p`, `δ = 56`)
   - `isPrimitiveWeird_45356` (`2^2 * 17 * 23 * 29`, 4-prime PWN)
   - `isPrimitiveWeird_73616` (`2^4 * 43 * 107`, non-Kravitz unbalanced mod-`p`, `δ = 80`)
   - `isPrimitiveWeird_15126992` (`2^4 * 67 * 103 * 137`, 4-prime PWN)
   - `isPrimitiveWeird_993360512` (`2^7 * 257 * 30197`, 9-digit Exact AP PWN with `t = 10`, `δ = 5396`)
10. `infinite_primitiveWeird_of_exact_ap_infinitely_often`:
    Infinitely-often conditional infinitude for the Exact AP Family.

## Part III: Unconditional Maynard–Tao (`H = 600` & Arbitrary `m`-Tuples) & Linnik Theorems for Weird Numbers
11. `weird_bounded_gaps_600_unconditional` (**Maynard–Tao Bounded-Gap Weird Numbers, `gap ≤ 42000`**):
    Powered by `RHDirect.MaynardTao.maynard_tao_bounded_gaps_unconditional` (`q - p ≤ 600`).
12. `weird_m_tuples_bounded_diameter_unconditional` (**Maynard–Tao Arbitrary `m`-Tuples of Weird Numbers**):
    Powered by `RHDirect.MaynardTao.maynard_tao_m_tuples_unconditional`.
13. `weird_in_every_coprime_ap_linnik_unconditional` (**Linnik-Bounded Weird Numbers in Coprime APs**):
    Powered by `RHDirect.Stage11LinnikUnconditional.linnikAPDyadic_unconditional`.

Zero `sorry`, zero custom axioms, zero `native_decide`.
-/

namespace PPL086_MT

open Finset

/-! ## Section 0: Self-Contained Core Definitions & Elementary Identities -/

/-- Sum of all positive divisors `σ(n) = ∑ d ∈ n.divisors, d`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Sum of proper divisors `s(n) = ∑ d ∈ n.properDivisors, d`. -/
def aliquotSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- A positive integer `n` is abundant if `σ(n) ≥ 2n`. -/
def IsAbundant (n : ℕ) : Prop :=
  0 < n ∧ 2 * n ≤ sigma n

/-- A positive integer `n` is deficient if `σ(n) < 2n`. -/
def IsDeficient (n : ℕ) : Prop :=
  0 < n ∧ sigma n < 2 * n

/-- A positive integer `n` is pseudoperfect if some subset of its proper divisors sums to `n`. -/
def IsPseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ ∑ d ∈ S, d = n

/-- A positive integer `n` is weird if it is abundant and not pseudoperfect. -/
def IsWeird (n : ℕ) : Prop :=
  IsAbundant n ∧ ¬ IsPseudoperfect n

/-- A positive integer `n` is primitive weird if it is weird and no proper divisor is weird. -/
def IsPrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d ∈ n.properDivisors, ¬ IsWeird d

lemma sigma_eq_aliquotSum_add {n : ℕ} (hn : 0 < n) :
    sigma n = aliquotSum n + n := by
  unfold sigma aliquotSum
  rw [← Nat.insert_self_properDivisors hn.ne',
      Finset.sum_insert Nat.self_notMem_properDivisors, add_comm]

lemma sigma_eq_arith_sigma (n : ℕ) : sigma n = ArithmeticFunction.sigma 1 n := by
  unfold sigma
  rw [ArithmeticFunction.sigma_apply]
  simp

lemma sigma_mul_of_coprime {a b : ℕ} (hcop : Nat.Coprime a b) :
    sigma (a * b) = sigma a * sigma b := by
  simp only [sigma_eq_arith_sigma]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop

lemma sigma_prime {p : ℕ} (hp : p.Prime) : sigma p = p + 1 := by
  unfold sigma
  rw [hp.divisors, Finset.sum_pair hp.ne_one.symm, add_comm]

lemma sigma_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  unfold sigma
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigma_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega

lemma sigma_pos {n : ℕ} (hn : 0 < n) : 0 < sigma n := by
  unfold sigma
  exact Finset.sum_pos (fun _ hd => Nat.pos_of_mem_divisors hd)
    ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩

lemma le_sigma {n : ℕ} (hn : 0 < n) : n ≤ sigma n := by
  unfold sigma
  exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn.ne')

lemma sigma_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    sigma (∏ p ∈ P, p) = ∏ p ∈ P, (p + 1) := by
  classical
  induction P using Finset.induction_on with
  | empty => unfold sigma; simp
  | insert a s ha ih =>
    have ha_prime : a.Prime := hP a (Finset.mem_insert_self a s)
    have hs_primes : ∀ p ∈ s, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_prime (hs_primes p hp)).mpr (fun heq => ha (heq ▸ hp))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, sigma_mul_of_coprime hcop,
        sigma_prime ha_prime, ih hs_primes]

lemma coprime_two_pow_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Coprime (2 ^ k) p :=
  (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow_left k

lemma sigma_two_pow_mul_prime_mul_prime {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) :
    sigma (2 ^ k * p * q) = (2 ^ (k + 1) - 1) * (p + 1) * (q + 1) := by
  have hcop_2p : Nat.Coprime (2 ^ k) p := coprime_two_pow_prime hp hp2
  have hcop_2q : Nat.Coprime (2 ^ k) q := coprime_two_pow_prime hq hq2
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcop_2p_q : Nat.Coprime (2 ^ k * p) q := hcop_2q.mul_left hcop_pq
  rw [sigma_mul_of_coprime hcop_2p_q, sigma_mul_of_coprime hcop_2p,
      sigma_two_pow, sigma_prime hp, sigma_prime hq]

lemma sigma_div_mono {d n : ℕ} (_hd : 0 < d) (hdn : d ∣ n) (hn : 0 < n) :
    sigma d * n ≤ sigma n * d := by
  obtain ⟨k, rfl⟩ := hdn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  have hinj : Set.InjOn (fun x => k * x) (d.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hk h
  have hsub : d.divisors.image (fun x => k * x) ⊆ (d * k).divisors := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [Nat.mem_divisors] at hx ⊢
    exact ⟨by rw [mul_comm d k]; exact mul_dvd_mul_left k hx.1, hn.ne'⟩
  have hsum : k * sigma d ≤ sigma (d * k) := by
    unfold sigma
    rw [Finset.mul_sum]
    calc ∑ i ∈ d.divisors, k * i
        = ∑ y ∈ d.divisors.image (fun x => k * x), y := (Finset.sum_image (f := id) hinj).symm
      _ ≤ ∑ y ∈ (d * k).divisors, y := Finset.sum_le_sum_of_subset hsub
  calc sigma d * (d * k) = (k * sigma d) * d := by ring
    _ ≤ sigma (d * k) * d := Nat.mul_le_mul_right d hsum

lemma isDeficient_of_dvd_deficient {d n : ℕ} (hd : 0 < d) (hdn : d ∣ n) (hn : IsDeficient n) :
    IsDeficient d := by
  refine ⟨hd, ?_⟩
  have h1 := sigma_div_mono hd hdn hn.1
  have h2 := hn.2
  nlinarith

lemma isPseudoperfect_iff_abundance_subset_sum {n : ℕ} (hab : IsAbundant n) :
    IsPseudoperfect n ↔
      ∃ T : Finset ℕ, T ⊆ n.properDivisors ∧ ∑ d ∈ T, d = sigma n - 2 * n := by
  have hsig := sigma_eq_aliquotSum_add hab.1
  have hab2 : 2 * n ≤ sigma n := hab.2
  constructor
  · rintro ⟨_, S, hS, hsum⟩
    refine ⟨n.properDivisors \ S, Finset.sdiff_subset, ?_⟩
    have hsplit : ∑ d ∈ n.properDivisors \ S, d + ∑ d ∈ S, d = aliquotSum n := by
      unfold aliquotSum
      exact Finset.sum_sdiff hS
    omega
  · rintro ⟨T, hT, hsum⟩
    refine ⟨hab.1, n.properDivisors \ T, Finset.sdiff_subset, ?_⟩
    have hsplit : ∑ d ∈ n.properDivisors \ T, d + ∑ d ∈ T, d = aliquotSum n := by
      unfold aliquotSum
      exact Finset.sum_sdiff hT
    omega

lemma isPseudoperfect_mul_of_isPseudoperfect {d k : ℕ} (hd : IsPseudoperfect d) (hk : 0 < k) :
    IsPseudoperfect (d * k) := by
  rcases hd with ⟨hd0, S, hS, hsum⟩
  refine ⟨Nat.mul_pos hd0 hk, S.image (fun x => x * k), ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    have hx' := Nat.mem_properDivisors.mp (hS hx)
    exact Nat.mem_properDivisors.mpr ⟨mul_dvd_mul_right hx'.1 k, Nat.mul_lt_mul_of_pos_right hx'.2 hk⟩
  · rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_right hk h),
        ← Finset.sum_mul, hsum]

lemma not_isPseudoperfect_of_dvd {d n : ℕ} (hdn : d ∣ n) (hn0 : 0 < n) (hnp : ¬ IsPseudoperfect n) :
    ¬ IsPseudoperfect d := by
  intro hdp
  obtain ⟨k, rfl⟩ := hdn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn0
  exact hnp (isPseudoperfect_mul_of_isPseudoperfect hdp hk)

lemma isPrimitiveWeird_iff_properDivisors_deficient {n : ℕ} :
    IsPrimitiveWeird n ↔ IsWeird n ∧ ∀ d ∈ n.properDivisors, IsDeficient d := by
  constructor
  · rintro ⟨hw, hprim⟩
    refine ⟨hw, fun d hd => ?_⟩
    have hd_mem := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd_mem.1 hw.1.1
    refine ⟨hd0, ?_⟩
    by_contra hge
    push Not at hge
    exact hprim d hd ⟨⟨hd0, hge⟩, not_isPseudoperfect_of_dvd hd_mem.1 hw.1.1 hw.2⟩
  · rintro ⟨hw, hdef⟩
    refine ⟨hw, fun d hd hdw => ?_⟩
    have h1 := (hdef d hd).2
    have h2 := hdw.1.2
    omega

lemma exists_subset_sum_two_pow (k : ℕ) :
    ∀ x : ℕ, x < 2 ^ (k + 1) →
      ∃ S : Finset ℕ, S ⊆ (2 ^ k).divisors ∧ ∑ d ∈ S, d = x := by
  induction k with
  | zero =>
    intro x hx
    have hx' : x = 0 ∨ x = 1 := by omega
    rcases hx' with rfl | rfl
    · exact ⟨∅, Finset.empty_subset _, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ k ih =>
    intro x hx
    have hsub : (2 ^ k).divisors ⊆ (2 ^ (k + 1)).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨dvd_trans hd.1 (pow_dvd_pow 2 (Nat.le_succ k)), by positivity⟩
    by_cases hlt : x < 2 ^ (k + 1)
    · obtain ⟨S, hS, hsum⟩ := ih x hlt
      exact ⟨S, Finset.Subset.trans hS hsub, hsum⟩
    · have hx' : x - 2 ^ (k + 1) < 2 ^ (k + 1) := by
        have : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
        omega
      obtain ⟨S, hS, hsum⟩ := ih (x - 2 ^ (k + 1)) hx'
      have hnot : 2 ^ (k + 1) ∉ S := by
        intro hmem
        have hle := Nat.le_of_dvd (by positivity) (Nat.dvd_of_mem_divisors (hS hmem))
        have hgt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
        omega
      refine ⟨insert (2 ^ (k + 1)) S, ?_, ?_⟩
      · exact Finset.insert_subset (Nat.mem_divisors_self _ (by positivity))
          (Finset.Subset.trans hS hsub)
      · rw [Finset.sum_insert hnot, hsum]
        omega

lemma isPseudoperfect_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : p < 2 ^ (k + 1)) : IsPseudoperfect (2 ^ k * p) := by
  have hcop : Nat.Coprime (2 ^ k) p := coprime_two_pow_prime hp hp2
  have hsig : sigma (2 ^ k * p) = (2 ^ (k + 1) - 1) * (p + 1) := by
    rw [sigma_mul_of_coprime hcop, sigma_two_pow, sigma_prime hp]
  have hpos : 0 < 2 ^ k * p := Nat.mul_pos (by positivity) hp.pos
  have hab : IsAbundant (2 ^ k * p) := by
    refine ⟨hpos, ?_⟩
    rw [hsig]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    zify [hge1]
    nlinarith
  rw [isPseudoperfect_iff_abundance_subset_sum hab]
  set δ := sigma (2 ^ k * p) - 2 * (2 ^ k * p) with hδ_def
  have hδ_lt : δ < 2 ^ (k + 1) := by
    rw [hδ_def, hsig]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hsub : (2 ^ (k + 1) - 1) * (p + 1) = 2 * (2 ^ k * p) + (2 ^ (k + 1) - 1 - p) := by
      have hp_le : p ≤ 2 ^ (k + 1) - 1 := by omega
      zify [hge1, hp_le]; nlinarith
    omega
  obtain ⟨S, hS, hsum⟩ := exists_subset_sum_two_pow k δ hδ_lt
  refine ⟨S, ?_, hsum⟩
  intro d hd
  have hd_mem := Nat.mem_divisors.mp (hS hd)
  refine Nat.mem_properDivisors.mpr ⟨dvd_mul_of_dvd_left hd_mem.1 p, ?_⟩
  have hd_le : d ≤ 2 ^ k := Nat.le_of_dvd (by positivity) hd_mem.1
  have hp_gt1 : 1 < p := hp.one_lt
  nlinarith

lemma isDeficient_properDivisor_two_pow_pq {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_gt : 2 ^ (k + 1) < p) (hpq : p < q) :
    ∀ d ∈ (2 ^ k * p * q).properDivisors, IsDeficient d := by
  have hR_ge4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos
  have hn_pos : 0 < 2 ^ k * p * q := Nat.mul_pos (Nat.mul_pos (by positivity) hp_pos) hq_pos
  have hdef_p : IsDeficient (2 ^ k * p) := by
    refine ⟨Nat.mul_pos (by positivity) hp_pos, ?_⟩
    rw [sigma_mul_of_coprime (coprime_two_pow_prime hp hp2), sigma_two_pow, sigma_prime hp]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    zify [hge1]; nlinarith
  have hdef_q : IsDeficient (2 ^ k * q) := by
    refine ⟨Nat.mul_pos (by positivity) hq_pos, ?_⟩
    rw [sigma_mul_of_coprime (coprime_two_pow_prime hq hq2), sigma_two_pow, sigma_prime hq]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    zify [hge1]; nlinarith
  have hdef_2 : IsDeficient (2 ^ (k - 1) * p * q) := by
    refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hp_pos) hq_pos, ?_⟩
    rw [sigma_two_pow_mul_prime_mul_prime hp hq hp2 hq2 hpq_ne]
    have hpow1 : 2 ^ (k - 1 + 1) = 2 ^ k := by congr 1; omega
    have h2k_eq : 2 * 2 ^ (k - 1) = 2 ^ k := by
      have : 2 ^ (k - 1) * 2 = 2 ^ (k - 1 + 1) := (pow_succ 2 (k - 1)).symm
      rw [mul_comm, this, hpow1]
    have hpow2 : 2 * (2 ^ (k - 1) * p * q) = 2 ^ k * p * q := by
      calc 2 * (2 ^ (k - 1) * p * q) = (2 * 2 ^ (k - 1)) * p * q := by ring
        _ = 2 ^ k * p * q := by rw [h2k_eq]
    rw [hpow1, hpow2]
    have hge1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hp_2k : 2 * 2 ^ k < p := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hq_2k : 2 * 2 ^ k < q := by omega
    zify [hge1]; nlinarith
  intro d hd
  have hd_mem := Nat.mem_properDivisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd_mem.1 hn_pos
  obtain ⟨m, hm⟩ := hd_mem.1
  have hm1 : 1 < m := by nlinarith [hd_mem.2]
  obtain ⟨r, hr_prime, hr_dvd_m⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hr_dvd_n : r ∣ 2 ^ k * p * q := hm ▸ dvd_mul_of_dvd_right hr_dvd_m d
  have hr_cases : r = 2 ∨ r = p ∨ r = q := by
    rcases hr_prime.dvd_mul.mp hr_dvd_n with h2p | hq_dvd
    · rcases hr_prime.dvd_mul.mp h2p with h2_dvd | hp_dvd
      · left; exact (Nat.prime_dvd_prime_iff_eq hr_prime Nat.prime_two).mp (hr_prime.dvd_of_dvd_pow h2_dvd)
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hr_prime hp).mp hp_dvd
    · right; right; exact (Nat.prime_dvd_prime_iff_eq hr_prime hq).mp hq_dvd
  obtain ⟨m', rfl⟩ := hr_dvd_m
  rcases hr_cases with hr2 | hrp | hrq
  · rw [hr2] at hm
    have hdvd : d ∣ 2 ^ (k - 1) * p * q := by
      refine ⟨m', ?_⟩
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
        have h1 : 2 ^ (k - 1) * 2 = 2 ^ (k - 1 + 1) := (pow_succ 2 (k - 1)).symm
        have h2 : k - 1 + 1 = k := by omega
        rw [h2] at h1; linarith
      have hmul : 2 * (2 ^ (k - 1) * p * q) = 2 * (d * m') := by
        calc 2 * (2 ^ (k - 1) * p * q) = (2 * 2 ^ (k - 1)) * p * q := by ring
          _ = 2 ^ k * p * q := by rw [← h2k]
          _ = d * (2 * m') := hm
          _ = 2 * (d * m') := by ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
    exact isDeficient_of_dvd_deficient hd0 hdvd hdef_2
  · rw [hrp] at hm
    have hdvd : d ∣ 2 ^ k * q := by
      refine ⟨m', ?_⟩
      have hmul : p * (2 ^ k * q) = p * (d * m') := by
        calc p * (2 ^ k * q) = 2 ^ k * p * q := by ring
          _ = d * (p * m') := hm
          _ = p * (d * m') := by ring
      exact Nat.eq_of_mul_eq_mul_left hp_pos hmul
    exact isDeficient_of_dvd_deficient hd0 hdvd hdef_q
  · rw [hrq] at hm
    have hdvd : d ∣ 2 ^ k * p := by
      refine ⟨m', ?_⟩
      have hmul : q * (2 ^ k * p) = q * (d * m') := by
        calc q * (2 ^ k * p) = 2 ^ k * p * q := by ring
          _ = d * (q * m') := hm
          _ = q * (d * m') := by ring
      exact Nat.eq_of_mul_eq_mul_left hq_pos hmul
    exact isDeficient_of_dvd_deficient hd0 hdvd hdef_p

/-! ## Part I: Exact Unconditional Barrier Theorems -/

/-- **Exact Straddling Barrier (Half 1 — Constructive Pseudoperfectness below `2^(k+2) - 1`):**
For EVERY `k ≥ 1` and primes `2^(k+1) < p < q` with `q ≤ 2^(k+2) - 2`,
`2^k * p * q` is **ALWAYS pseudoperfect** (NEVER weird)! -/
theorem isPseudoperfect_two_pow_pq_of_le_sub_two {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_gt : 2 ^ (k + 1) < p) (hpq : p < q)
    (hq_le : q ≤ 2 ^ (k + 2) - 2) :
    IsPseudoperfect (2 ^ k * p * q) := by
  set R := 2 ^ (k + 1) with hR_def
  have h2R : 2 ^ (k + 2) = 2 * R := by rw [hR_def, pow_succ]; ring
  have hR_ge4 : 4 ≤ R := by
    rw [hR_def]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos
  -- `p, q` are odd primes, so `q - p = 2 * t` for some `t ≥ 1` with `2 * t < R`
  have hp_odd : p % 2 = 1 := by obtain ⟨u, hu⟩ := hp.odd_of_ne_two hp2; omega
  have hq_odd : q % 2 = 1 := by obtain ⟨u, hu⟩ := hq.odd_of_ne_two hq2; omega
  set t := (q - p) / 2 with ht_def
  have hq_eq : q = p + 2 * t := by omega
  have ht_pos : 1 ≤ t := by omega
  have h2t_lt_R : 2 * t < R := by omega
  set a := 2 * R - p with ha_def
  have hp_eq : p = 2 * R - a := by omega
  have ha_ge : 2 * t + 2 ≤ a := by omega
  have ha_lt_R : a < R := by omega
  set s := a - t - 2 with hs_def
  have hs_ge_t : t ≤ s := by omega
  have hs_lt_R : s < R := by omega
  set M := R + t * a - 2 * t - 1 with hM_def
  -- Key bounds on `M`: `R - 1 ≤ M ≤ 2 * t * s + R - 1`
  have hta_ge : 2 * t + 2 ≤ t * a := by nlinarith
  have hM_ge : R - 1 ≤ M := by omega
  have hM_le : M ≤ 2 * t * s + (R - 1) := by
    have hkey : 2 * t * t + 2 * t ≤ t * a := by nlinarith
    have hsat : s + t + 2 = a := by omega
    have h2ts : 2 * t * s + 2 * t * t + 4 * t = 2 * t * a := by nlinarith
    have hM_add : M + (2 * t + 1) = R + t * a := by omega
    have hR_add : (R - 1) + 1 = R := by omega
    linarith
  -- Compute exact abundance `δ = s * p + M`
  set δ := s * p + M with hδ_def
  have hsig := sigma_two_pow_mul_prime_mul_prime (k := k) hp hq hp2 hq2 hpq_ne
  have h2n : 2 * (2 ^ k * p * q) = R * p * q := by rw [hR_def, pow_succ]; ring
  have hsig_eq : sigma (2 ^ k * p * q) = R * p * q + δ := by
    rw [hsig, ← hR_def, hδ_def]
    have hR1 : 1 ≤ R := by omega
    zify [hR1]
    have hp_z : (p : ℤ) = 2 * (R : ℤ) - (a : ℤ) := by omega
    have hq_z : (q : ℤ) = (p : ℤ) + 2 * (t : ℤ) := by omega
    have hs_z : (s : ℤ) = (a : ℤ) - (t : ℤ) - 2 := by omega
    have hM_z : (M : ℤ) = (R : ℤ) + (t : ℤ) * (a : ℤ) - 2 * (t : ℤ) - 1 := by omega
    rw [hM_z, hs_z, hq_z, hp_z]
    ring
  have hab : IsAbundant (2 ^ k * p * q) :=
    ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hp_pos) hq_pos, by rw [hsig_eq, h2n]; omega⟩
  rw [isPseudoperfect_iff_abundance_subset_sum hab]
  have hδ_eq : sigma (2 ^ k * p * q) - 2 * (2 ^ k * p * q) = δ := by rw [hsig_eq, h2n]; omega
  rw [hδ_eq]
  -- Construct `c₂ := min s (M / (2 * t))`, `c₀ := M - c₂ * (2 * t)`, `c₁ := s - c₂`
  set c₂ := min s (M / (2 * t)) with hc₂_def
  have hc₂_le_s : c₂ ≤ s := min_le_left _ _
  have hc₂_mul_le : c₂ * (2 * t) ≤ M := by
    have hle : c₂ ≤ M / (2 * t) := min_le_right _ _
    calc c₂ * (2 * t) ≤ (M / (2 * t)) * (2 * t) := Nat.mul_le_mul_right _ hle
      _ ≤ M := Nat.div_mul_le_self M (2 * t)
  set c₀ := M - c₂ * (2 * t) with hc₀_def
  set c₁ := s - c₂ with hc₁_def
  have hc₀_lt_R : c₀ < R := by
    by_cases hcase : M / (2 * t) ≤ s
    · have hc₂_eq : c₂ = M / (2 * t) := min_eq_right hcase
      have hrem : c₀ = M % (2 * t) := by
        have hdm : M / (2 * t) * (2 * t) + M % (2 * t) = M := by
          rw [mul_comm]; exact Nat.div_add_mod M (2 * t)
        rw [hc₀_def, hc₂_eq]
        omega
      have hlt : M % (2 * t) < 2 * t := Nat.mod_lt M (by omega)
      omega
    · have hc₂_eq : c₂ = s := min_eq_left (by omega)
      rw [hc₀_def, hc₂_eq]
      have : s * (2 * t) = 2 * t * s := by ring
      omega
  have hc₁_lt_R : c₁ < R := lt_of_le_of_lt (Nat.sub_le s c₂) hs_lt_R
  have hc₂_lt_R : c₂ < R := lt_of_le_of_lt hc₂_le_s hs_lt_R
  have hdecomp : c₀ + c₁ * p + c₂ * q = δ := by
    rw [hδ_def, hq_eq]
    have h1 : c₀ + c₂ * (2 * t) = M := Nat.sub_add_cancel hc₂_mul_le
    have h2 : c₁ + c₂ = s := Nat.sub_add_cancel hc₂_le_s
    calc c₀ + c₁ * p + c₂ * (p + 2 * t)
        = (c₁ + c₂) * p + (c₀ + c₂ * (2 * t)) := by ring
      _ = s * p + M := by rw [h1, h2]
  -- Realize `c₀, c₁, c₂` as binary subset sums of `(2^k).divisors`
  obtain ⟨S₀, hS₀, hsum₀⟩ := exists_subset_sum_two_pow k c₀ hc₀_lt_R
  obtain ⟨S₁, hS₁, hsum₁⟩ := exists_subset_sum_two_pow k c₁ hc₁_lt_R
  obtain ⟨S₂, hS₂, hsum₂⟩ := exists_subset_sum_two_pow k c₂ hc₂_lt_R
  set A₁ := S₁.image (fun d => d * p)
  set A₂ := S₂.image (fun d => d * q)
  have hsumA1 : ∑ d ∈ A₁, d = c₁ * p := by
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_right hp_pos h), ← Finset.sum_mul, hsum₁]
  have hsumA2 : ∑ d ∈ A₂, d = c₂ * q := by
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_right hq_pos h), ← Finset.sum_mul, hsum₂]
  have hcop_2p : Nat.Coprime (2 ^ k) p := coprime_two_pow_prime hp hp2
  have hcop_2q : Nat.Coprime (2 ^ k) q := coprime_two_pow_prime hq hq2
  have hnot_p_of_div2 : ∀ d ∈ (2 ^ k).divisors, ¬ (p ∣ d) := by
    intro d hd hpd
    have h1 : p ∣ 2 ^ k := dvd_trans hpd (Nat.dvd_of_mem_divisors hd)
    have h2 : p ∣ Nat.gcd (2 ^ k) p := Nat.dvd_gcd h1 dvd_rfl
    rw [hcop_2p.gcd_eq_one] at h2
    exact hp.not_dvd_one h2
  have hnot_q_of_div2 : ∀ d ∈ (2 ^ k).divisors, ¬ (q ∣ d) := by
    intro d hd hqd
    have h1 : q ∣ 2 ^ k := dvd_trans hqd (Nat.dvd_of_mem_divisors hd)
    have h2 : q ∣ Nat.gcd (2 ^ k) q := Nat.dvd_gcd h1 dvd_rfl
    rw [hcop_2q.gcd_eq_one] at h2
    exact hq.not_dvd_one h2
  have hdisj01 : Disjoint S₀ A₁ := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    rcases Finset.mem_image.mp hx1 with ⟨y, _, rfl⟩
    exact hnot_p_of_div2 _ (hS₀ hx0) (dvd_mul_left p y)
  have hdisj02 : Disjoint S₀ A₂ := by
    rw [Finset.disjoint_left]
    intro x hx0 hx2
    rcases Finset.mem_image.mp hx2 with ⟨y, _, rfl⟩
    exact hnot_q_of_div2 _ (hS₀ hx0) (dvd_mul_left q y)
  have hdisj12 : Disjoint A₁ A₂ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨y₁, hy₁, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨y₂, _, hyeq⟩
    have hq_dvd : q ∣ y₁ * p := ⟨y₂, by linarith⟩
    rcases hq.dvd_mul.mp hq_dvd with hqy1 | hqp
    · exact hnot_q_of_div2 y₁ (hS₁ hy₁) hqy1
    · exact hpq_ne ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp).symm
  refine ⟨S₀ ∪ (A₁ ∪ A₂), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx0 | hx12
    · have hxd := Nat.dvd_of_mem_divisors (hS₀ hx0)
      have hxle : x ≤ 2 ^ k := Nat.le_of_dvd (by positivity) hxd
      refine Nat.mem_properDivisors.mpr ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hxd p) q, ?_⟩
      have h1 : 1 < p * q := by nlinarith [hp.one_lt, hq.one_lt]
      calc x ≤ 2 ^ k := hxle
        _ < 2 ^ k * (p * q) := lt_mul_of_one_lt_right (by positivity) h1
        _ = 2 ^ k * p * q := by ring
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · rcases Finset.mem_image.mp hx1 with ⟨y, hy, rfl⟩
        have hyd := Nat.dvd_of_mem_divisors (hS₁ hy)
        have hyle : y ≤ 2 ^ k := Nat.le_of_dvd (by positivity) hyd
        refine Nat.mem_properDivisors.mpr ⟨dvd_mul_of_dvd_left (mul_dvd_mul_right hyd p) q, ?_⟩
        calc y * p ≤ 2 ^ k * p := Nat.mul_le_mul_right p hyle
          _ < 2 ^ k * p * q := lt_mul_of_one_lt_right (Nat.mul_pos (by positivity) hp_pos) hq.one_lt
      · rcases Finset.mem_image.mp hx2 with ⟨y, hy, rfl⟩
        have hyd := Nat.dvd_of_mem_divisors (hS₂ hy)
        have hyle : y ≤ 2 ^ k := Nat.le_of_dvd (by positivity) hyd
        refine Nat.mem_properDivisors.mpr ⟨?_, ?_⟩
        · have : y * q ∣ (2 ^ k * q) * p := dvd_mul_of_dvd_left (mul_dvd_mul_right hyd q) p
          simpa [mul_assoc, mul_comm, mul_left_comm] using this
        · calc y * q ≤ 2 ^ k * q := Nat.mul_le_mul_right q hyle
            _ < 2 ^ k * q * p := lt_mul_of_one_lt_right (Nat.mul_pos (by positivity) hq_pos) hp.one_lt
            _ = 2 ^ k * p * q := by ring
  · rw [Finset.sum_union (Finset.disjoint_union_right.mpr ⟨hdisj01, hdisj02⟩),
        Finset.sum_union hdisj12, hsum₀, hsumA1, hsumA2]
    omega

/-- **Exact Straddling Barrier (Half 2 — Strict Deficiency at or above `2^(k+2) - 1`):**
For EVERY `k ≥ 1` and primes `2^(k+2) - 1 ≤ p < q`, `2^k * p * q` is **ALWAYS deficient**. -/
theorem isDeficient_two_pow_pq_of_ge_sub_one {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_ge : 2 ^ (k + 2) - 1 ≤ p) (hpq : p < q) :
    IsDeficient (2 ^ k * p * q) := by
  set R := 2 ^ (k + 1) with hR_def
  have h2R : 2 ^ (k + 2) = 2 * R := by rw [hR_def, pow_succ]; ring
  have hR_ge4 : 4 ≤ R := by
    rw [hR_def]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hp.pos) hq.pos, ?_⟩
  rw [sigma_two_pow_mul_prime_mul_prime hp hq hp2 hq2 (ne_of_lt hpq), ← hR_def]
  have h2n : 2 * (2 ^ k * p * q) = R * p * q := by rw [hR_def, pow_succ]; ring
  rw [h2n]
  have hR1 : 1 ≤ R := by omega
  zify [hR1]
  have hp_z : 2 * (R : ℤ) - 1 ≤ (p : ℤ) := by omega
  have hq_z : 2 * (R : ℤ) ≤ (q : ℤ) := by omega
  nlinarith

/-- **EXACT STRADDLING THEOREM FOR `2^k * p * q` (100% UNCONDITIONAL):**
Every weird number of the form `2^k * p * q` (`k ≥ 1`, primes `p < q`) MUST satisfy
`2^(k+1) < p < 2^(k+2) - 1 ≤ q` (i.e., `[p, q]` strictly straddles `2^(k+2) - 1`). -/
theorem straddling_of_isWeird_two_pow_pq {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hw : IsWeird (2 ^ k * p * q)) :
    2 ^ (k + 1) < p ∧ p < 2 ^ (k + 2) - 1 ∧ 2 ^ (k + 2) - 1 ≤ q := by
  have hR_ge4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by
    intro h2
    subst h2
    have hq2 : q ≠ 2 := by omega
    have hrew : 2 ^ k * 2 * q = 2 ^ (k + 1) * q := by rw [pow_succ]
    rw [hrew] at hw
    by_cases hq_lt : q < 2 ^ (k + 2)
    · exact hw.2 (isPseudoperfect_two_pow_mul_prime hq hq2 hq_lt)
    · have hdef : sigma (2 ^ (k + 1) * q) < 2 * (2 ^ (k + 1) * q) := by
        rw [sigma_mul_of_coprime (coprime_two_pow_prime hq hq2), sigma_two_pow, sigma_prime hq]
        have hpow : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by rw [mul_comm, ← pow_succ]
        have hge1 : 1 ≤ 2 ^ (k + 2) := Nat.one_le_pow _ _ (by norm_num)
        have hne : q ≠ 2 ^ (k + 2) := by
          intro heq
          have h2q : 2 ∣ q := by rw [heq]; exact dvd_pow_self 2 (by omega)
          exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2q).symm
        zify [hge1]; nlinarith
      have := hw.1.2
      omega
  have hp_gt : 2 ^ (k + 1) < p := by
    by_contra hle
    have hlt : p < 2 ^ (k + 1) := by
      have hne : p ≠ 2 ^ (k + 1) := by
        intro heq
        have h2p : 2 ∣ p := by rw [heq]; exact dvd_pow_self 2 (by omega)
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
      omega
    have hpp := isPseudoperfect_two_pow_mul_prime hp hp2 hlt
    exact not_isPseudoperfect_of_dvd (dvd_mul_right (2 ^ k * p) q) hw.1.1 hw.2 hpp
  have hp_lt : p < 2 ^ (k + 2) - 1 := by
    by_contra hge
    have hdef := isDeficient_two_pow_pq_of_ge_sub_one hk hp hq (by omega) hpq
    have := hw.1.2
    have := hdef.2
    omega
  have hq_ge : 2 ^ (k + 2) - 1 ≤ q := by
    by_contra hlt
    have hpp := isPseudoperfect_two_pow_pq_of_le_sub_two hk hp hq hp_gt hpq (by omega)
    exact hw.2 hpp
  exact ⟨hp_gt, hp_lt, hq_ge⟩

/-- **CHEN SEMIPRIME BARRIER FOR `2^k * m` (100% UNCONDITIONAL):**
Replacing a prime `q` of size `< 2^(2*k + 2)` in `2^k * p * q` by a Chen semiprime `q = r₁ * r₂`
(with odd primes `r₁, r₂`) ALWAYS yields a **pseudoperfect** (hence NEVER weird) number, because
`min r₁ r₂ < 2^(k + 1)` forces `2^k * min r₁ r₂` to be pseudoperfect! -/
theorem isPseudoperfect_two_pow_mul_semiprime_of_lt_sq {k m r₁ r₂ : ℕ}
    (hm : 0 < m) (hr₁ : r₁.Prime) (hr₂ : r₂.Prime) (hr₁2 : r₁ ≠ 2) (hr₂2 : r₂ ≠ 2)
    (hlt : r₁ * r₂ < 2 ^ (2 * k + 2)) :
    IsPseudoperfect (2 ^ k * m * (r₁ * r₂)) := by
  have hsq : 2 ^ (2 * k + 2) = 2 ^ (k + 1) * 2 ^ (k + 1) := by
    rw [← pow_add]; congr 1; omega
  have hor : r₁ < 2 ^ (k + 1) ∨ r₂ < 2 ^ (k + 1) := by
    by_contra h
    push Not at h
    have hmul : 2 ^ (k + 1) * 2 ^ (k + 1) ≤ r₁ * r₂ := Nat.mul_le_mul h.1 h.2
    omega
  rcases hor with h1 | h2
  · have hpp := isPseudoperfect_two_pow_mul_prime hr₁ hr₁2 h1
    have hrew : 2 ^ k * m * (r₁ * r₂) = (2 ^ k * r₁) * (m * r₂) := by ring
    rw [hrew]
    exact isPseudoperfect_mul_of_isPseudoperfect hpp (Nat.mul_pos hm hr₂.pos)
  · have hpp := isPseudoperfect_two_pow_mul_prime hr₂ hr₂2 h2
    have hrew : 2 ^ k * m * (r₁ * r₂) = (2 ^ k * r₂) * (m * r₁) := by ring
    rw [hrew]
    exact isPseudoperfect_mul_of_isPseudoperfect hpp (Nat.mul_pos hm hr₁.pos)

/-- **UNIVERSAL `√X` PRIME-GAP BARRIER FOR ALL DEFICIENT MULTIPLIERS `D` (100% UNCONDITIONAL):**
For ANY deficient integer `D ≥ 1` (`S = σ(D)`, `e = 2*D - S ≥ 1`) and ANY `p ≥ 1` with `D * p`
deficient (`e' = e * p - S ≥ 1`), the Gap-0 interval `((S*(p+1) - p)/e', S*(p+1)/e')` for `q`
has length `L = p / e'` and location `X = S * (p + 1) / e'` satisfying
`(L - 1 / e)^2 < X / (e * e')` and in particular `L < 1 + √X`. -/
theorem gap0_interval_sqrt_barrier {D p : ℕ} (hD : IsDeficient D)
    (hp_def : sigma D < (2 * D - sigma D) * p) :
    let S : ℝ := (sigma D : ℝ)
    let e : ℝ := ((2 * D - sigma D : ℕ) : ℝ)
    let e' : ℝ := (((2 * D - sigma D) * p - sigma D : ℕ) : ℝ)
    let L : ℝ := (p : ℝ) / e'
    let X : ℝ := S * ((p : ℝ) + 1) / e'
    (L - 1 / e) ^ 2 < X / (e * e') ∧ L < 1 + Real.sqrt X := by
  intro S e e' L X
  have hS_pos : 0 < S := by dsimp only [S]; exact_mod_cast sigma_pos hD.1
  have he_nat : 1 ≤ 2 * D - sigma D := by have := hD.2; omega
  have he'_nat : 1 ≤ (2 * D - sigma D) * p - sigma D := by omega
  have he_pos : 0 < e := by dsimp only [e]; exact_mod_cast (by omega : 0 < 2 * D - sigma D)
  have he_ge1 : 1 ≤ e := by dsimp only [e]; exact_mod_cast he_nat
  have he'_pos : 0 < e' := by dsimp only [e']; exact_mod_cast (by omega : 0 < (2 * D - sigma D) * p - sigma D)
  have he'_ge1 : 1 ≤ e' := by dsimp only [e']; exact_mod_cast he'_nat
  have hp_eq : e * (p : ℝ) = S + e' := by
    have hnat : (2 * D - sigma D) * p = sigma D + ((2 * D - sigma D) * p - sigma D) := by omega
    have hcast : (((2 * D - sigma D) * p : ℕ) : ℝ) =
        ((sigma D + ((2 * D - sigma D) * p - sigma D) : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [S, e, e', Nat.cast_mul, Nat.cast_add] using hcast
  have hL_sub : L - 1 / e = S / (e * e') := by
    dsimp only [L]
    field_simp [he_pos.ne', he'_pos.ne']
    linarith
  have hX_pos : 0 < X := by
    dsimp only [X]
    have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    positivity
  have hsq : (L - 1 / e) ^ 2 < X / (e * e') := by
    rw [hL_sub]
    dsimp only [X]
    have hSp : S < e * ((p : ℝ) + 1) := by linarith
    have h1 : S ^ 2 / (e * e') ^ 2 = S * S / (e * e' * (e * e')) := by ring
    have h2 : S * ((p : ℝ) + 1) / e' / (e * e') = S * (e * ((p : ℝ) + 1)) / (e * e' * (e * e')) := by
      field_simp [he_pos.ne', he'_pos.ne']
    rw [div_pow, h1, h2]
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hSp hS_pos) (by positivity)
  refine ⟨hsq, ?_⟩
  have hX_div_le : X / (e * e') ≤ X := by
    rw [div_le_iff₀ (mul_pos he_pos he'_pos)]
    have hee : 1 ≤ e * e' := by nlinarith
    nlinarith
  have hlt_X : (L - 1 / e) ^ 2 < X := lt_of_lt_of_le hsq hX_div_le
  have hL_sub_lt : L - 1 / e < Real.sqrt X := by
    have h1 : Real.sqrt ((L - 1 / e) ^ 2) < Real.sqrt X :=
      Real.sqrt_lt_sqrt (sq_nonneg _) hlt_X
    have h2 : 0 ≤ L - 1 / e := by rw [hL_sub]; positivity
    rwa [Real.sqrt_sq h2] at h1
  have h1e_le : 1 / e ≤ 1 := by
    rw [div_le_one he_pos]; exact he_ge1
  linarith

/-- Helper: telescoping bound for a sorted list of `m` distinct integers `≥ r + 1`. -/
private lemma prod_one_add_inv_le_of_sorted (r : ℕ) (hr : 0 < r) (L : List ℕ)
    (hsorted : L.Pairwise (· < ·)) (hge : ∀ p ∈ L, r + 1 ≤ p) :
    (L.map (fun (p : ℕ) => ((p : ℚ) + 1) / (p : ℚ))).prod ≤
      ((r + 1 + L.length : ℕ) : ℚ) / ((r + 1 : ℕ) : ℚ) := by
  induction L generalizing r with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil, add_zero]
    rw [div_self (by positivity)]
  | cons a tl ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have ha_ge : r + 1 ≤ a := hge a (by simp)
    have htl_sorted : tl.Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
    have htl_gt_a : ∀ p ∈ tl, a < p := (List.pairwise_cons.mp hsorted).1
    have htl_ge : ∀ p ∈ tl, (r + 1) + 1 ≤ p := fun p hp => by
      have := htl_gt_a p hp; omega
    have hih := ih (r + 1) (by omega) htl_sorted htl_ge
    have ha_rat : ((a : ℚ) + 1) / (a : ℚ) ≤ ((r + 2 : ℕ) : ℚ) / ((r + 1 : ℕ) : ℚ) := by
      have ha_pos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (by omega : 0 < a)
      have hr1_pos : (0 : ℚ) < ((r + 1 : ℕ) : ℚ) := by positivity
      rw [div_le_div_iff₀ ha_pos hr1_pos]
      have har : ((r + 1 : ℕ) : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha_ge
      push_cast at har ⊢
      nlinarith
    have hprod_nn : (0 : ℚ) ≤ (tl.map (fun (p : ℕ) => ((p : ℚ) + 1) / (p : ℚ))).prod := by
      refine List.prod_nonneg fun x hx => ?_
      rcases List.mem_map.mp hx with ⟨p, _, rfl⟩
      positivity
    calc ((a : ℚ) + 1) / (a : ℚ) * (tl.map (fun (p : ℕ) => ((p : ℚ) + 1) / (p : ℚ))).prod
        ≤ (((r + 2 : ℕ) : ℚ) / ((r + 1 : ℕ) : ℚ)) *
            (((r + 1 + 1 + tl.length : ℕ) : ℚ) / ((r + 1 + 1 : ℕ) : ℚ)) :=
          mul_le_mul ha_rat hih hprod_nn (by positivity)
      _ = ((r + 1 + (tl.length + 1) : ℕ) : ℚ) / ((r + 1 : ℕ) : ℚ) := by
          have hr2 : ((r + 2 : ℕ) : ℚ) ≠ 0 := by positivity
          have hrew1 : r + 1 + 1 = r + 2 := by omega
          have hrew2 : r + 1 + 1 + tl.length = r + 1 + (tl.length + 1) := by omega
          rw [hrew1, hrew2]
          field_simp [hr2]

/-- **CONGRUENCE-OBSTRUCTION ABUNDANCE BARRIER (100% UNCONDITIONAL):**
If `D` is deficient, `r` is prime with `Nat.Coprime D r`, `P` is a Finset of `m` primes strictly
greater than `r` (and coprime to `D`), and `2^m * σ(D) < r` (the condition preventing mod-`r`
subset-sum wraparound when `p ≡ 1 [MOD r]`), then `D * r * ∏ p ∈ P, p` is **ALWAYS strictly deficient**. -/
theorem mod_r_obstruction_abundance_barrier {D r : ℕ} {P : Finset ℕ}
    (hD : IsDeficient D) (hr : r.Prime) (hDr : Nat.Coprime D r)
    (hP : ∀ p ∈ P, p.Prime ∧ r < p ∧ Nat.Coprime D p)
    (hnowrap : 2 ^ P.card * sigma D < r) :
    IsDeficient (D * r * ∏ p ∈ P, p) := by
  have hprod_pos : 0 < ∏ p ∈ P, p := Finset.prod_pos fun p hp => (hP p hp).1.pos
  have hn_pos : 0 < D * r * ∏ p ∈ P, p := Nat.mul_pos (Nat.mul_pos hD.1 hr.pos) hprod_pos
  refine ⟨hn_pos, ?_⟩
  have hcop_DP : Nat.Coprime D (∏ p ∈ P, p) := Nat.Coprime.prod_right fun p hp => (hP p hp).2.2
  have hcop_rP : Nat.Coprime r (∏ p ∈ P, p) :=
    Nat.Coprime.prod_right fun p hp => (Nat.coprime_primes hr (hP p hp).1).mpr (ne_of_lt (hP p hp).2.1)
  have hsig_prod : sigma (∏ p ∈ P, p) = ∏ p ∈ P, (p + 1) :=
    sigma_prod_primes P fun p hp => (hP p hp).1
  have hsig_n : sigma (D * r * ∏ p ∈ P, p) = sigma D * (r + 1) * ∏ p ∈ P, (p + 1) := by
    rw [sigma_mul_of_coprime (hcop_DP.mul_left hcop_rP), sigma_mul_of_coprime hDr,
        sigma_prime hr, hsig_prod]
  rw [hsig_n]
  set L := P.sort (· ≤ ·) with hL_def
  have hL_len : L.length = P.card := Finset.length_sort (· ≤ ·)
  have hL_nodup : L.Nodup := Finset.sort_nodup P (· ≤ ·)
  have hL_sorted_le : L.Pairwise (· ≤ ·) := Finset.pairwise_sort P (· ≤ ·)
  have hL_sorted : L.Pairwise (· < ·) := by
    rw [List.pairwise_iff_get] at hL_sorted_le ⊢
    intro i j hij
    have hle := hL_sorted_le i j hij
    have hne : L.get i ≠ L.get j := fun heq => (ne_of_lt hij) (hL_nodup.get_inj_iff.mp heq)
    omega
  have hL_ge : ∀ p ∈ L, r + 1 ≤ p := fun p hp => by
    have hpm : p ∈ P := (Finset.mem_sort (· ≤ ·)).mp hp
    have := (hP p hpm).2.1
    omega
  have htel := prod_one_add_inv_le_of_sorted r hr.pos L hL_sorted hL_ge
  rw [hL_len] at htel
  have hprod_eq : (∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ))) =
      (L.map (fun (p : ℕ) => ((p : ℚ) + 1) / (p : ℚ))).prod := by
    have hmult : (L : Multiset ℕ) = P.val := Finset.sort_eq P (· ≤ ·)
    rw [← Multiset.prod_coe, ← Multiset.map_coe, hmult]
    rfl
  have hprod_le : (∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ))) ≤
      ((r + 1 + P.card : ℕ) : ℚ) / ((r + 1 : ℕ) : ℚ) := hprod_eq ▸ htel
  have hr_pos_q : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr.pos
  have hr1_pos_q : (0 : ℚ) < ((r + 1 : ℕ) : ℚ) := by positivity
  have hprod_P_pos_q : (0 : ℚ) < (∏ p ∈ P, (p : ℚ)) :=
    Finset.prod_pos fun p hp => by exact_mod_cast (hP p hp).1.pos
  have hstep1 : (((r + 1 : ℕ) : ℚ) / (r : ℚ)) * (∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ))) ≤
      ((r + 1 + P.card : ℕ) : ℚ) / (r : ℚ) := by
    calc (((r + 1 : ℕ) : ℚ) / (r : ℚ)) * (∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ)))
        ≤ (((r + 1 : ℕ) : ℚ) / (r : ℚ)) * (((r + 1 + P.card : ℕ) : ℚ) / ((r + 1 : ℕ) : ℚ)) :=
          mul_le_mul_of_nonneg_left hprod_le (by positivity)
      _ = ((r + 1 + P.card : ℕ) : ℚ) / (r : ℚ) := by field_simp [hr_pos_q.ne', hr1_pos_q.ne']
  have hcard_le_pow : P.card + 1 ≤ 2 ^ P.card := by
    induction P.card with
    | zero => norm_num
    | succ n ih =>
      have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      omega
  have hlt_q : ((sigma D : ℚ) * ((r + 1 : ℕ) : ℚ) * ∏ p ∈ P, ((p + 1 : ℕ) : ℚ)) <
      (2 : ℚ) * (D : ℚ) * (r : ℚ) * ∏ p ∈ P, (p : ℚ) := by
    have hdiv_prod : (∏ p ∈ P, (((p : ℚ) + 1) / (p : ℚ))) =
        (∏ p ∈ P, ((p + 1 : ℕ) : ℚ)) / (∏ p ∈ P, (p : ℚ)) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p _ => by push_cast; rfl
    rw [hdiv_prod] at hstep1
    have hmul1 : ((r + 1 : ℕ) : ℚ) * (∏ p ∈ P, ((p + 1 : ℕ) : ℚ)) ≤
        ((r + 1 + P.card : ℕ) : ℚ) * (∏ p ∈ P, (p : ℚ)) := by
      have h1 : (((r + 1 : ℕ) : ℚ) * ∏ p ∈ P, ((p + 1 : ℕ) : ℚ)) / ((r : ℚ) * ∏ p ∈ P, (p : ℚ)) ≤
          ((r + 1 + P.card : ℕ) : ℚ) / (r : ℚ) := by
        simpa [div_mul_div_comm] using hstep1
      rw [div_le_div_iff₀ (mul_pos hr_pos_q hprod_P_pos_q) hr_pos_q] at h1
      have h2 : (((r + 1 : ℕ) : ℚ) * ∏ p ∈ P, ((p + 1 : ℕ) : ℚ)) * (r : ℚ) ≤
          (((r + 1 + P.card : ℕ) : ℚ) * ∏ p ∈ P, (p : ℚ)) * (r : ℚ) := by linarith
      exact le_of_mul_le_mul_right h2 hr_pos_q
    have hnat_lt : sigma D * (r + 1 + P.card) < 2 * D * r := by
      have h1 : (P.card + 1) * sigma D ≤ 2 ^ P.card * sigma D := Nat.mul_le_mul_right _ hcard_le_pow
      have h2 : sigma D + 1 ≤ 2 * D := by have := hD.2; omega
      nlinarith
    have hq_lt : (sigma D : ℚ) * ((r + 1 + P.card : ℕ) : ℚ) < (2 : ℚ) * (D : ℚ) * (r : ℚ) := by
      exact_mod_cast hnat_lt
    calc (sigma D : ℚ) * ((r + 1 : ℕ) : ℚ) * ∏ p ∈ P, ((p + 1 : ℕ) : ℚ)
        = (sigma D : ℚ) * (((r + 1 : ℕ) : ℚ) * ∏ p ∈ P, ((p + 1 : ℕ) : ℚ)) := by ring
      _ ≤ (sigma D : ℚ) * (((r + 1 + P.card : ℕ) : ℚ) * ∏ p ∈ P, (p : ℚ)) :=
          mul_le_mul_of_nonneg_left hmul1 (by positivity)
      _ = ((sigma D : ℚ) * ((r + 1 + P.card : ℕ) : ℚ)) * ∏ p ∈ P, (p : ℚ) := by ring
      _ < ((2 : ℚ) * (D : ℚ) * (r : ℚ)) * ∏ p ∈ P, (p : ℚ) :=
          mul_lt_mul_of_pos_right hq_lt hprod_P_pos_q
      _ = (2 : ℚ) * (D : ℚ) * (r : ℚ) * ∏ p ∈ P, (p : ℚ) := by ring
  have hcast_lt : ((sigma D * (r + 1) * ∏ p ∈ P, (p + 1) : ℕ) : ℚ) <
      ((2 * (D * r * ∏ p ∈ P, p) : ℕ) : ℚ) := by
    push_cast at hlt_q ⊢
    linarith
  exact_mod_cast hcast_lt

/-! ## Part II: Brand-New Generalized Primitive Weird Constructions -/

/-- **UNBALANCED MOD-`p` PRIMITIVE WEIRD CRITERION:**
If `k ≥ 1`, `2^(k+1) < p < q` are primes, and the abundance `δ = (2^(k+1) - 1)*(p + q + 1) - p * q`
satisfies `0 < δ < q` and `2^(k+1) ≤ δ % p`, then `2^k * p * q` is **primitive weird**! -/
theorem isPrimitiveWeird_two_pow_pq_of_mod_p_ge {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_gt : 2 ^ (k + 1) < p) (hpq : p < q)
    (hlo : p * q < (2 ^ (k + 1) - 1) * (p + q + 1))
    (hhi : (2 ^ (k + 1) - 1) * (p + q + 1) < p * q + q)
    (hmod : 2 ^ (k + 1) ≤ ((2 ^ (k + 1) - 1) * (p + q + 1) - p * q) % p) :
    IsPrimitiveWeird (2 ^ k * p * q) := by
  have hR_ge4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hn_pos : 0 < 2 ^ k * p * q := Nat.mul_pos (Nat.mul_pos (by positivity) hp.pos) hq.pos
  have hsig := sigma_two_pow_mul_prime_mul_prime (k := k) hp hq hp2 hq2 hpq_ne
  have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by rw [pow_succ]; ring
  set δ := (2 ^ (k + 1) - 1) * (p + q + 1) - p * q with hδ_def
  have hsig_eq : sigma (2 ^ k * p * q) = 2 ^ (k + 1) * p * q + δ := by
    rw [hsig, hδ_def]
    have hge1 : 1 ≤ 2 ^ (k + 1) := by omega
    zify [hge1, le_of_lt hlo]
    ring
  have hab : IsAbundant (2 ^ k * p * q) := ⟨hn_pos, by rw [hsig_eq, h2n]; omega⟩
  rw [isPrimitiveWeird_iff_properDivisors_deficient]
  refine ⟨⟨hab, ?_⟩, isDeficient_properDivisor_two_pow_pq hk hp hq hp_gt hpq⟩
  rw [isPseudoperfect_iff_abundance_subset_sum hab]
  rintro ⟨T, hT, hsum⟩
  have hδ_eq : sigma (2 ^ k * p * q) - 2 * (2 ^ k * p * q) = δ := by rw [hsig_eq, h2n]; omega
  rw [hδ_eq] at hsum
  have hδ_lt_q : δ < q := by omega
  have hno_q : ∀ d ∈ T, ¬ (q ∣ d) := by
    intro d hd hqd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp (hT hd)).1 hn_pos
    have hq_le : q ≤ d := Nat.le_of_dvd hd_pos hqd
    have hd_le : d ≤ ∑ x ∈ T, x := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
    omega
  set T₀ := T.filter (fun d => ¬ p ∣ d)
  set T₁ := T.filter (fun d => p ∣ d)
  have hsplit : ∑ d ∈ T₀, d + ∑ d ∈ T₁, d = δ := by
    rw [add_comm, Finset.sum_filter_add_sum_filter_not, hsum]
  have hT0_sub : T₀ ⊆ (2 ^ k).divisors := by
    intro d hd
    have ⟨hdT, hnp⟩ := Finset.mem_filter.mp hd
    have hnq : ¬ (q ∣ d) := hno_q d hdT
    have hd_dvd : d ∣ 2 ^ k * p * q := (Nat.mem_properDivisors.mp (hT hdT)).1
    have hd_2p : d ∣ 2 ^ k * p :=
      Nat.Coprime.dvd_of_dvd_mul_right ((hq.coprime_iff_not_dvd.mpr hnq).symm) hd_dvd
    have hd_2 : d ∣ 2 ^ k :=
      Nat.Coprime.dvd_of_dvd_mul_right ((hp.coprime_iff_not_dvd.mpr hnp).symm) hd_2p
    exact Nat.mem_divisors.mpr ⟨hd_2, by positivity⟩
  have hc0_le : ∑ d ∈ T₀, d ≤ 2 ^ (k + 1) - 1 := by
    calc ∑ d ∈ T₀, d ≤ ∑ d ∈ (2 ^ k).divisors, d := Finset.sum_le_sum_of_subset hT0_sub
      _ = sigma (2 ^ k) := rfl
      _ = 2 ^ (k + 1) - 1 := sigma_two_pow k
  have hp_dvd_T1 : p ∣ ∑ d ∈ T₁, d :=
    Finset.dvd_sum fun d hd => (Finset.mem_filter.mp hd).2
  obtain ⟨c₁, hc₁⟩ := hp_dvd_T1
  have hδ_mod : δ % p = ∑ d ∈ T₀, d := by
    rw [← hsplit, hc₁, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **EXACT ARITHMETIC-PROGRESSION PRIMITIVE WEIRD FAMILY:**
For `k ≥ 2`, `1 ≤ j < k`, let `R = 2^(k+1)`, `d = 2^j`, `p = R + d - 1`, and
`Q₀ = (R / d) * (R + d - 2) - 1`. If `p` is prime and `q = Q₀ - t * p` is prime with
`t * d * p + R < q`, then `2^k * p * q` is **primitive weird** with exact abundance
`δ = t * d * p + R`. -/
theorem isPrimitiveWeird_exact_ap_family {k j t : ℕ} (hk : 2 ≤ k) (hj1 : 1 ≤ j) (hjk : j < k)
    (hp : (2 ^ (k + 1) + 2 ^ j - 1).Prime)
    (hq : ((2 ^ (k + 1) / 2 ^ j) * (2 ^ (k + 1) + 2 ^ j - 2) - 1 - t * (2 ^ (k + 1) + 2 ^ j - 1)).Prime)
    (hdelta_lt : t * 2 ^ j * (2 ^ (k + 1) + 2 ^ j - 1) + 2 ^ (k + 1) <
      (2 ^ (k + 1) / 2 ^ j) * (2 ^ (k + 1) + 2 ^ j - 2) - 1 - t * (2 ^ (k + 1) + 2 ^ j - 1)) :
    IsPrimitiveWeird (2 ^ k * (2 ^ (k + 1) + 2 ^ j - 1) *
      ((2 ^ (k + 1) / 2 ^ j) * (2 ^ (k + 1) + 2 ^ j - 2) - 1 - t * (2 ^ (k + 1) + 2 ^ j - 1))) := by
  set R := 2 ^ (k + 1) with hR_def
  set d := 2 ^ j with hd_def
  set p := R + d - 1 with hp_def
  set Q₀ := (R / d) * (R + d - 2) - 1 with hQ0_def
  set q := Q₀ - t * p with hq_def
  have hd_ge2 : 2 ≤ d := by
    rw [hd_def]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
  have hR_ge8 : 8 ≤ R := by
    rw [hR_def]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd_dvd_R : d ∣ R := pow_dvd_pow 2 (by omega)
  have hd_mul_div : (R / d) * d = R := Nat.div_mul_cancel hd_dvd_R
  have hR_div_d_ge4 : 4 ≤ R / d := by
    have hpow : 2 ^ (k + 1 - j) = R / d := by
      have h1 : 2 ^ j * 2 ^ (k + 1 - j) = 2 ^ (k + 1) := by rw [← pow_add]; congr 1; omega
      have h2 : d * 2 ^ (k + 1 - j) = d * (R / d) := by
        calc d * 2 ^ (k + 1 - j) = 2 ^ j * 2 ^ (k + 1 - j) := by rw [hd_def]
          _ = 2 ^ (k + 1) := h1
          _ = R := hR_def.symm
          _ = (R / d) * d := hd_mul_div.symm
          _ = d * (R / d) := mul_comm _ _
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) h2
    rw [← hpow]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1 - j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hRd2_ge : 8 ≤ R + d - 2 := by omega
  have hQ0_ge1 : 1 ≤ (R / d) * (R + d - 2) := Nat.mul_pos (by omega) (by omega)
  have htp_lt_Q0 : t * p < Q₀ := by omega
  have hp_gt_R : R < p := by omega
  have hpq : p < q := by
    by_cases ht0 : t = 0
    · subst ht0
      have hq_eq : q = Q₀ := by simp [hq_def]
      have h1 : 4 * (R + d - 2) ≤ (R / d) * (R + d - 2) := Nat.mul_le_mul_right _ hR_div_d_ge4
      rw [hq_eq, hQ0_def]
      omega
    · have ht1 : 1 ≤ t := by omega
      have htd : 2 ≤ t * d := by nlinarith
      have h2p : 2 * p ≤ t * d * p := Nat.mul_le_mul_right p htd
      omega
  have hdelta_id : (R - 1) * (p + q + 1) = p * q + (t * d * p + R) := by
    have hR1 : 1 ≤ R := by omega
    have hQ0_z : (d : ℤ) * (Q₀ : ℤ) = (R : ℤ) * ((R : ℤ) + (d : ℤ) - 2) - (d : ℤ) := by
      have hd_z : ((R / d : ℕ) : ℤ) * (d : ℤ) = (R : ℤ) := by exact_mod_cast hd_mul_div
      have hQ : (Q₀ : ℤ) = ((R / d : ℕ) : ℤ) * ((R : ℤ) + (d : ℤ) - 2) - 1 := by
        rw [hQ0_def]
        zify [hQ0_ge1, show 2 ≤ R + d by omega]
      nlinarith [hQ, hd_z]
    have hq_z : (q : ℤ) = (Q₀ : ℤ) - (t : ℤ) * (p : ℤ) := by rw [hq_def]; zify [le_of_lt htp_lt_Q0]
    have hp_z : (p : ℤ) = (R : ℤ) + (d : ℤ) - 1 := by rw [hp_def]; zify [show 1 ≤ R + d by omega]
    zify [hR1]
    have hd_q : (d : ℤ) * (q : ℤ) = (R : ℤ) * ((R : ℤ) + (d : ℤ) - 2) - (d : ℤ) - (t : ℤ) * (d : ℤ) * (p : ℤ) := by
      nlinarith [hQ0_z, hq_z]
    nlinarith [hp_z, hd_q]
  refine isPrimitiveWeird_two_pow_pq_of_mod_p_ge (by omega) hp hq hp_gt_R hpq ?_ ?_ ?_
  · rw [← hR_def, hdelta_id]; omega
  · rw [← hR_def, hdelta_id]; omega
  · rw [← hR_def, hdelta_id, Nat.add_sub_cancel_left]
    have hrew : t * d * p + R = R + (t * d) * p := by ring
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp_gt_R]

/-- **AMATO–HASLER–MELFI–PARTON MULTI-PRIME GAP-0 THEOREM:**
Let `k ≥ 1`, `P` be a nonempty Finset of primes all `> 2^(k+1)`, and let `D' = 2^k * ∏ p ∈ P, p`.
If `D'` is deficient (`e' = 2 * D' - σ(D') > 0`) and `q` is a prime strictly greater than every
`p ∈ P` such that `2^(k+1) ≤ σ(D') - e' * q < P.min' hP_ne`, then `D' * q` is **primitive weird**! -/
theorem isPrimitiveWeird_multi_prime_gap0 {k q : ℕ} {P : Finset ℕ} (hk : 1 ≤ k)
    (hP_ne : P.Nonempty) (hP : ∀ p ∈ P, p.Prime ∧ 2 ^ (k + 1) < p)
    (hq : q.Prime) (hq_gt : ∀ p ∈ P, p < q)
    (hD_def : IsDeficient (2 ^ k * ∏ p ∈ P, p))
    (hlo : 2 ^ (k + 1) ≤ sigma (2 ^ k * ∏ p ∈ P, p) - (2 * (2 ^ k * ∏ p ∈ P, p) - sigma (2 ^ k * ∏ p ∈ P, p)) * q)
    (hhi : sigma (2 ^ k * ∏ p ∈ P, p) - (2 * (2 ^ k * ∏ p ∈ P, p) - sigma (2 ^ k * ∏ p ∈ P, p)) * q < P.min' hP_ne) :
    IsPrimitiveWeird ((2 ^ k * ∏ p ∈ P, p) * q) := by
  set M := ∏ p ∈ P, p with hM_def
  set D' := 2 ^ k * M with hD'_def
  set e' := 2 * D' - sigma D' with he'_def
  have hR_ge4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hP p hp).1.pos
  have hD'_pos : 0 < D' := Nat.mul_pos (by positivity) hM_pos
  have hn_pos : 0 < D' * q := Nat.mul_pos hD'_pos hq.pos
  have hq_gt_R : 2 ^ (k + 1) < q := by
    obtain ⟨p₀, hp₀⟩ := hP_ne
    exact lt_trans (hP p₀ hp₀).2 (hq_gt p₀ hp₀)
  have hq2 : q ≠ 2 := by omega
  have hcop_2q : Nat.Coprime (2 ^ k) q := coprime_two_pow_prime hq hq2
  have hcop_Mq : Nat.Coprime M q :=
    Nat.Coprime.prod_left fun p hp => (Nat.coprime_primes (hP p hp).1 hq).mpr (ne_of_lt (hq_gt p hp))
  have hcop_D'q : Nat.Coprime D' q := hcop_2q.mul_left hcop_Mq
  have hcop_2M : Nat.Coprime (2 ^ k) M :=
    Nat.Coprime.prod_right fun p hp => coprime_two_pow_prime (hP p hp).1 (by have := (hP p hp).2; omega)
  have he'_pos : 0 < e' := by have := hD_def.2; omega
  have hle_sig : e' * q ≤ sigma D' := by omega
  set δ := sigma D' - e' * q with hδ_def
  have hsig_n : sigma (D' * q) = 2 * (D' * q) + δ := by
    rw [sigma_mul_of_coprime hcop_D'q, sigma_prime hq, hδ_def]
    have h1 : sigma D' + e' = 2 * D' := by have := hD_def.2; omega
    zify [hle_sig]
    have h1z : (sigma D' : ℤ) + (e' : ℤ) = 2 * (D' : ℤ) := by exact_mod_cast h1
    nlinarith
  have hab : IsAbundant (D' * q) := ⟨hn_pos, by rw [hsig_n]; omega⟩
  rw [isPrimitiveWeird_iff_properDivisors_deficient]
  refine ⟨⟨hab, ?_⟩, ?_⟩
  · rw [isPseudoperfect_iff_abundance_subset_sum hab]
    rintro ⟨T, hT, hsum⟩
    have hδ_eq : sigma (D' * q) - 2 * (D' * q) = δ := by rw [hsig_n]; omega
    rw [hδ_eq] at hsum
    have hT_sub : T ⊆ (2 ^ k).divisors := by
      intro d hd
      have hd_prop := Nat.mem_properDivisors.mp (hT hd)
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_prop.1 hn_pos
      have hd_le_δ : d ≤ δ := hsum ▸ Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
      have hcop_d_q : Nat.Coprime d q := by
        rw [Nat.coprime_comm]
        refine hq.coprime_iff_not_dvd.mpr fun hqd => ?_
        have hq_le_d : q ≤ d := Nat.le_of_dvd hd_pos hqd
        have hmin_lt_q : P.min' hP_ne < q := hq_gt _ (Finset.min'_mem P hP_ne)
        omega
      have hcop_d_M : Nat.Coprime d M := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        rw [Nat.coprime_comm]
        refine (hP p hp).1.coprime_iff_not_dvd.mpr fun hpd => ?_
        have hp_le_d : p ≤ d := Nat.le_of_dvd hd_pos hpd
        have hmin_le_p : P.min' hP_ne ≤ p := Finset.min'_le P p hp
        omega
      have hd_D' : d ∣ D' := Nat.Coprime.dvd_of_dvd_mul_right hcop_d_q hd_prop.1
      have hd_2k : d ∣ 2 ^ k := Nat.Coprime.dvd_of_dvd_mul_right hcop_d_M hd_D'
      exact Nat.mem_divisors.mpr ⟨hd_2k, by positivity⟩
    have hle_R : δ ≤ 2 ^ (k + 1) - 1 := by
      calc δ = ∑ d ∈ T, d := hsum.symm
        _ ≤ ∑ d ∈ (2 ^ k).divisors, d := Finset.sum_le_sum_of_subset hT_sub
        _ = sigma (2 ^ k) := rfl
        _ = 2 ^ (k + 1) - 1 := sigma_two_pow k
    omega
  · have hdef_half : IsDeficient (2 ^ (k - 1) * M * q) := by
      refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hM_pos) hq.pos, ?_⟩
      have hcop_2km1_M : Nat.Coprime (2 ^ (k - 1)) M :=
        Nat.Coprime.prod_right fun p hp => coprime_two_pow_prime (hP p hp).1 (by have := (hP p hp).2; omega)
      have hcop_2km1_q : Nat.Coprime (2 ^ (k - 1)) q := coprime_two_pow_prime hq hq2
      have hsig_half : sigma (2 ^ (k - 1) * M * q) = (2 ^ k - 1) * sigma M * (q + 1) := by
        rw [sigma_mul_of_coprime (hcop_2km1_q.mul_left hcop_Mq),
            sigma_mul_of_coprime hcop_2km1_M, sigma_two_pow, sigma_prime hq]
        have hsub : k - 1 + 1 = k := by omega
        rw [hsub]
      have hsig_full : (2 ^ (k + 1) - 1) * sigma M * (q + 1) = 2 * (D' * q) + δ := by
        have h1 : sigma (D' * q) = (2 ^ (k + 1) - 1) * sigma M * (q + 1) := by
          rw [sigma_mul_of_coprime hcop_D'q, hD'_def, sigma_mul_of_coprime hcop_2M,
              sigma_two_pow, sigma_prime hq]
        linarith [hsig_n]
      have h2k_eq : 2 * 2 ^ (k - 1) = 2 ^ k := by
        have h1 : 2 ^ (k - 1) * 2 = 2 ^ (k - 1 + 1) := (pow_succ 2 (k - 1)).symm
        have h2 : k - 1 + 1 = k := by omega
        rw [h2] at h1; linarith
      have hmin_le_M : P.min' hP_ne ≤ M :=
        Nat.le_of_dvd hM_pos (Finset.dvd_prod_of_mem _ (Finset.min'_mem P hP_ne))
      have hδ_lt_M : δ < M := lt_of_lt_of_le hhi hmin_le_M
      have hmul_lt : (2 ^ (k + 1) - 1) * sigma (2 ^ (k - 1) * M * q) <
          (2 ^ (k + 1) - 1) * (2 * (2 ^ (k - 1) * M * q)) := by
        rw [hsig_half]
        have hlhs : (2 ^ (k + 1) - 1) * ((2 ^ k - 1) * sigma M * (q + 1)) =
            (2 ^ k - 1) * (2 * (D' * q) + δ) := by
          calc (2 ^ (k + 1) - 1) * ((2 ^ k - 1) * sigma M * (q + 1))
              = (2 ^ k - 1) * ((2 ^ (k + 1) - 1) * sigma M * (q + 1)) := by ring
            _ = (2 ^ k - 1) * (2 * (D' * q) + δ) := by rw [hsig_full]
        have hrhs : (2 ^ (k + 1) - 1) * (2 * (2 ^ (k - 1) * M * q)) =
            (2 ^ (k + 1) - 1) * (D' * q) := by
          calc (2 ^ (k + 1) - 1) * (2 * (2 ^ (k - 1) * M * q))
              = (2 ^ (k + 1) - 1) * ((2 * 2 ^ (k - 1)) * M * q) := by ring
            _ = (2 ^ (k + 1) - 1) * (2 ^ k * M * q) := by rw [h2k_eq]
            _ = (2 ^ (k + 1) - 1) * (D' * q) := by rw [← hD'_def]
        rw [hlhs, hrhs]
        have h2k_ge2 : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        have h2kp1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        have h1 : 1 ≤ 2 ^ k := by omega
        have h2 : 1 ≤ 2 ^ (k + 1) := by omega
        zify [h1, h2]
        have hD'q_z : (D' : ℤ) * (q : ℤ) = (2 ^ k : ℤ) * (M : ℤ) * (q : ℤ) := by
          rw [hD'_def]; push_cast; ring
        have hδ_z : (δ : ℤ) < (M : ℤ) := by exact_mod_cast hδ_lt_M
        have hq_z : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq.one_le
        nlinarith [h2kp1, hD'q_z]
      exact Nat.lt_of_mul_lt_mul_left hmul_lt
    intro d hd
    have hd_prop := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd_prop.1 hn_pos
    obtain ⟨m, hm⟩ := hd_prop.1
    have hm1 : 1 < m := by nlinarith [hd_prop.2]
    obtain ⟨r, hr_prime, hr_dvd_m⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hr_dvd_n : r ∣ D' * q := hm ▸ dvd_mul_of_dvd_right hr_dvd_m d
    obtain ⟨m', rfl⟩ := hr_dvd_m
    rcases hr_prime.dvd_mul.mp hr_dvd_n with hr_D' | hr_q
    · rcases hr_prime.dvd_mul.mp hr_D' with hr_2k | hr_M
      · have hr2 : r = 2 :=
          (Nat.prime_dvd_prime_iff_eq hr_prime Nat.prime_two).mp (hr_prime.dvd_of_dvd_pow hr_2k)
        rw [hr2] at hm
        have hdvd : d ∣ 2 ^ (k - 1) * M * q := by
          refine ⟨m', ?_⟩
          have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
            have h1 : 2 ^ (k - 1) * 2 = 2 ^ (k - 1 + 1) := (pow_succ 2 (k - 1)).symm
            have h2 : k - 1 + 1 = k := by omega
            rw [h2] at h1; linarith
          have hmul : 2 * (2 ^ (k - 1) * M * q) = 2 * (d * m') := by
            calc 2 * (2 ^ (k - 1) * M * q) = (2 * 2 ^ (k - 1)) * M * q := by ring
              _ = D' * q := by rw [← h2k, hD'_def]
              _ = d * (2 * m') := hm
              _ = 2 * (d * m') := by ring
          exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
        exact isDeficient_of_dvd_deficient hd0 hdvd hdef_half
      · have hr_mem : r ∈ P := by
          obtain ⟨p, hpP, hrp⟩ := (hr_prime.prime.dvd_finsetProd_iff id).mp hr_M
          have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr_prime (hP p hpP).1).mp hrp
          exact heq ▸ hpP
        set M' := ∏ x ∈ P.erase r, x
        have hM_eq : M = r * M' := (Finset.mul_prod_erase P id hr_mem).symm
        have hcop_rM' : Nat.Coprime r M' :=
          Nat.Coprime.prod_right fun x hx =>
            (Nat.coprime_primes hr_prime (hP x (Finset.mem_of_mem_erase hx)).1).mpr
              (Ne.symm (Finset.ne_of_mem_erase hx))
        have hcop_2r : Nat.Coprime (2 ^ k) r :=
          coprime_two_pow_prime hr_prime (by have := (hP r hr_mem).2; omega)
        have hcop_M'q : Nat.Coprime M' q :=
          Nat.Coprime.prod_left fun x hx =>
            (Nat.coprime_primes (hP x (Finset.mem_of_mem_erase hx)).1 hq).mpr
              (ne_of_lt (hq_gt x (Finset.mem_of_mem_erase hx)))
        have hdef_r : IsDeficient (2 ^ k * M' * q) := by
          have hM'_pos : 0 < M' :=
            Finset.prod_pos fun x hx => (hP x (Finset.mem_of_mem_erase hx)).1.pos
          refine ⟨Nat.mul_pos (Nat.mul_pos (by positivity) hM'_pos) hq.pos, ?_⟩
          have hsig_D' : sigma D' = sigma (2 ^ k * M') * (r + 1) := by
            rw [hD'_def, hM_eq, show 2 ^ k * (r * M') = (2 ^ k * M') * r by ring,
                sigma_mul_of_coprime (hcop_2r.mul_left hcop_rM'.symm), sigma_prime hr_prime]
          have hsig_sub : sigma (2 ^ k * M' * q) = sigma (2 ^ k * M') * (q + 1) := by
            rw [sigma_mul_of_coprime (hcop_2q.mul_left hcop_M'q), sigma_prime hq]
          rw [hsig_sub]
          have hrq : r < q := hq_gt r hr_mem
          have h1 : sigma (2 ^ k * M') * (r + 1) < 2 * (2 ^ k * M') * r := by
            have := hD_def.2
            rw [hsig_D', hD'_def, hM_eq] at this
            nlinarith
          have h2 : (q + 1) * r < (r + 1) * q := by nlinarith
          have h3 : sigma (2 ^ k * M') * (q + 1) * r < 2 * (2 ^ k * M' * q) * r := by
            calc sigma (2 ^ k * M') * (q + 1) * r
                = sigma (2 ^ k * M') * ((q + 1) * r) := by ring
              _ < sigma (2 ^ k * M') * ((r + 1) * q) :=
                  Nat.mul_lt_mul_of_pos_left h2 (sigma_pos (Nat.mul_pos (by positivity) hM'_pos))
              _ = (sigma (2 ^ k * M') * (r + 1)) * q := by ring
              _ < (2 * (2 ^ k * M') * r) * q := Nat.mul_lt_mul_of_pos_right h1 hq.pos
              _ = 2 * (2 ^ k * M' * q) * r := by ring
          exact Nat.lt_of_mul_lt_mul_right h3
        have hdvd : d ∣ 2 ^ k * M' * q := by
          refine ⟨m', ?_⟩
          have hmul : r * (2 ^ k * M' * q) = r * (d * m') := by
            calc r * (2 ^ k * M' * q) = 2 ^ k * (r * M') * q := by ring
              _ = D' * q := by rw [← hM_eq, hD'_def]
              _ = d * (r * m') := hm
              _ = r * (d * m') := by ring
          exact Nat.eq_of_mul_eq_mul_left hr_prime.pos hmul
        exact isDeficient_of_dvd_deficient hd0 hdvd hdef_r
    · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr_prime hq).mp hr_q
      rw [hrq] at hm
      have hdvd : d ∣ D' := by
        refine ⟨m', ?_⟩
        have hmul : q * D' = q * (d * m') := by
          calc q * D' = D' * q := by ring
            _ = d * (q * m') := hm
            _ = q * (d * m') := by ring
        exact Nat.eq_of_mul_eq_mul_left hq.pos hmul
      exact isDeficient_of_dvd_deficient hd0 hdvd hD_def

/-! ## Concrete Certified Primitive Weird Numbers (ZERO `native_decide`!) -/

/-- `70 = 2^1 * 5 * 7` (smallest weird number). -/
theorem isPrimitiveWeird_70 : IsPrimitiveWeird 70 := by
  have h := isPrimitiveWeird_two_pow_pq_of_mod_p_ge (k := 1) (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- `9272 = 2^3 * 19 * 61` (unbalanced non-Kravitz primitive weird number, `δ = 56`, `56 % 19 = 18 ≥ 16`). -/
theorem isPrimitiveWeird_9272 : IsPrimitiveWeird 9272 := by
  have h := isPrimitiveWeird_two_pow_pq_of_mod_p_ge (k := 3) (p := 19) (q := 61)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- `73616 = 2^4 * 43 * 107` (unbalanced non-Kravitz primitive weird number, `δ = 80`, `80 % 43 = 37 ≥ 32`). -/
theorem isPrimitiveWeird_73616 : IsPrimitiveWeird 73616 := by
  have h := isPrimitiveWeird_two_pow_pq_of_mod_p_ge (k := 4) (p := 43) (q := 107)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- `993360512 = 2^7 * 257 * 30197` (9-digit Exact AP family primitive weird number, `t = 10`, `δ = 5396`). -/
theorem isPrimitiveWeird_993360512 : IsPrimitiveWeird 993360512 := by
  have hp : (2 ^ (7 + 1) + 2 ^ 1 - 1).Prime := by norm_num
  have hq : ((2 ^ (7 + 1) / 2 ^ 1) * (2 ^ (7 + 1) + 2 ^ 1 - 2) - 1 -
      10 * (2 ^ (7 + 1) + 2 ^ 1 - 1)).Prime := by norm_num
  have h := isPrimitiveWeird_exact_ap_family (k := 7) (j := 1) (t := 10)
    (by norm_num) (by norm_num) (by norm_num) hp hq (by norm_num)
  simpa using h

/-- Helper for 4-prime concrete `sigma (2^k * p1 * p2)`. -/
private lemma sigma_two_pow_p1_p2 {k p1 p2 : ℕ} (hp1 : p1.Prime) (hp2 : p2.Prime)
    (h12 : p1 ≠ 2) (h22 : p2 ≠ 2) (hne : p1 ≠ p2) :
    sigma (2 ^ k * (∏ p ∈ ({p1, p2} : Finset ℕ), p)) = (2 ^ (k + 1) - 1) * (p1 + 1) * (p2 + 1) := by
  rw [Finset.prod_pair hne, ← mul_assoc]
  exact sigma_two_pow_mul_prime_mul_prime hp1 hp2 h12 h22 hne

/-- `4030 = 2^1 * 5 * 13 * 31` (smallest 4-prime primitive weird number!). -/
theorem isPrimitiveWeird_4030 : IsPrimitiveWeird 4030 := by
  have hsig : sigma (2 ^ 1 * ∏ p ∈ ({5, 13} : Finset ℕ), p) = 252 := by
    rw [sigma_two_pow_p1_p2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hprod : (2 ^ 1 * ∏ p ∈ ({5, 13} : Finset ℕ), p) = 130 := by
    rw [Finset.prod_pair (by norm_num)]; norm_num
  have hmin : ({5, 13} : Finset ℕ).min' (by simp) = 5 := by decide
  have h := isPrimitiveWeird_multi_prime_gap0 (k := 1) (q := 31) (P := {5, 13})
    (by norm_num) (by simp)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    (by norm_num)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    ⟨by rw [hprod]; norm_num, by rw [hsig, hprod]; norm_num⟩
    (by rw [hsig, hprod]; norm_num)
    (by rw [hsig, hprod, hmin]; norm_num)
  rw [hprod] at h
  simpa using h

/-- `45356 = 2^2 * 17 * 23 * 29` (4-prime primitive weird number). -/
theorem isPrimitiveWeird_45356 : IsPrimitiveWeird 45356 := by
  have hsig : sigma (2 ^ 2 * ∏ p ∈ ({17, 23} : Finset ℕ), p) = 3024 := by
    rw [sigma_two_pow_p1_p2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hprod : (2 ^ 2 * ∏ p ∈ ({17, 23} : Finset ℕ), p) = 1564 := by
    rw [Finset.prod_pair (by norm_num)]; norm_num
  have hmin : ({17, 23} : Finset ℕ).min' (by simp) = 17 := by decide
  have h := isPrimitiveWeird_multi_prime_gap0 (k := 2) (q := 29) (P := {17, 23})
    (by norm_num) (by simp)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    (by norm_num)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    ⟨by rw [hprod]; norm_num, by rw [hsig, hprod]; norm_num⟩
    (by rw [hsig, hprod]; norm_num)
    (by rw [hsig, hprod, hmin]; norm_num)
  rw [hprod] at h
  simpa using h

/-- `15126992 = 2^4 * 67 * 103 * 137` (4-prime primitive weird number, `δ = 32`). -/
theorem isPrimitiveWeird_15126992 : IsPrimitiveWeird 15126992 := by
  have hsig : sigma (2 ^ 4 * ∏ p ∈ ({67, 103} : Finset ℕ), p) = 219232 := by
    rw [sigma_two_pow_p1_p2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  have hprod : (2 ^ 4 * ∏ p ∈ ({67, 103} : Finset ℕ), p) = 110416 := by
    rw [Finset.prod_pair (by norm_num)]; norm_num
  have hmin : ({67, 103} : Finset ℕ).min' (by simp) = 67 := by decide
  have h := isPrimitiveWeird_multi_prime_gap0 (k := 4) (q := 137) (P := {67, 103})
    (by norm_num) (by simp)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    (by norm_num)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> norm_num)
    ⟨by rw [hprod]; norm_num, by rw [hsig, hprod]; norm_num⟩
    (by rw [hsig, hprod]; norm_num)
    (by rw [hsig, hprod, hmin]; norm_num)
  rw [hprod] at h
  simpa using h

/-! ### Weakened Conditional Infinitude: Infinitely-Often Exact AP Family -/

/-- **Infinitely-Often Exact AP Conditional Infinitude:**
If there exist arbitrarily large `(k, j, t)` satisfying the Exact AP Family conditions,
then `{n : ℕ | IsPrimitiveWeird n}.Infinite`. -/
theorem infinite_primitiveWeird_of_exact_ap_infinitely_often
    (h : ∀ N : ℕ, ∃ k j t : ℕ, N ≤ k ∧ 2 ≤ k ∧ 1 ≤ j ∧ j < k ∧
      (2 ^ (k + 1) + 2 ^ j - 1).Prime ∧
      ((2 ^ (k + 1) / 2 ^ j) * (2 ^ (k + 1) + 2 ^ j - 2) - 1 - t * (2 ^ (k + 1) + 2 ^ j - 1)).Prime ∧
      t * 2 ^ j * (2 ^ (k + 1) + 2 ^ j - 1) + 2 ^ (k + 1) <
        (2 ^ (k + 1) / 2 ^ j) * (2 ^ (k + 1) + 2 ^ j - 2) - 1 - t * (2 ^ (k + 1) + 2 ^ j - 1)) :
    {n : ℕ | IsPrimitiveWeird n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨k, j, t, hNk, hk2, hj1, hjk, hp, hq, hlt⟩ := h N
  refine ⟨_, isPrimitiveWeird_exact_ap_family hk2 hj1 hjk hp hq hlt, ?_⟩
  have hk_lt_pow : k < 2 ^ k := Nat.lt_two_pow_self
  have h1 : 2 ^ k ≤ 2 ^ k * (2 ^ (k + 1) + 2 ^ j - 1) :=
    Nat.le_mul_of_pos_right _ hp.pos
  have h2 : 2 ^ k * (2 ^ (k + 1) + 2 ^ j - 1) ≤
      2 ^ k * (2 ^ (k + 1) + 2 ^ j - 1) *
        ((2 ^ (k + 1) / 2 ^ j) * (2 ^ (k + 1) + 2 ^ j - 2) - 1 - t * (2 ^ (k + 1) + 2 ^ j - 1)) :=
    Nat.le_mul_of_pos_right _ hq.pos
  omega

/-! ## Part III: Unconditional Maynard–Tao (`H = 600` & Arbitrary `m`-Tuples) & Linnik Theorems for Weird Numbers -/

/-- Helper: if `w` is weird and `p > σ(w)` is prime, then `w * p` is weird. -/
theorem isWeird_mul_prime_of_gt_sigma {w p : ℕ} (hw : IsWeird w) (hp : p.Prime)
    (hgt : sigma w < p) : IsWeird (w * p) := by
  have hw0 : 0 < w := hw.1.1
  have hw_lt_p : w < p := lt_of_le_of_lt (le_sigma hw0) hgt
  have hcop : Nat.Coprime w p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hw0 hw_lt_p)).symm
  have hsig_wp : sigma (w * p) = sigma w * (p + 1) := by
    rw [sigma_mul_of_coprime hcop, sigma_prime hp]
  have hab : IsAbundant (w * p) := by
    refine ⟨Nat.mul_pos hw0 hp.pos, ?_⟩
    rw [hsig_wp]
    have := hw.1.2
    nlinarith
  refine ⟨hab, ?_⟩
  rintro ⟨_, S, hS, hsum⟩
  set S₁ := S.filter (fun d => p ∣ d)
  set S₂ := S.filter (fun d => ¬ p ∣ d)
  have hsplit : ∑ d ∈ S₁, d + ∑ d ∈ S₂, d = w * p := by
    rw [Finset.sum_filter_add_sum_filter_not, hsum]
  set T := S₁.image (fun d => d / p)
  have hS1_eq : ∑ d ∈ S₁, d = (∑ e ∈ T, e) * p := by
    rw [Finset.sum_mul, Finset.sum_image]
    · refine Finset.sum_congr rfl fun d hd => (Nat.div_mul_cancel (Finset.mem_filter.mp hd).2).symm
    · intro x hx y hy hxy
      dsimp only at hxy
      rw [← Nat.div_mul_cancel (Finset.mem_filter.mp hx).2,
          ← Nat.div_mul_cancel (Finset.mem_filter.mp hy).2, hxy]
  have hT_sub : T ⊆ w.properDivisors := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨d, hd1, rfl⟩
    have ⟨hdS, hpd⟩ := Finset.mem_filter.mp hd1
    have hd_prop := Nat.mem_properDivisors.mp (hS hdS)
    obtain ⟨e', he'⟩ := hpd
    rw [he', Nat.mul_div_cancel_left _ hp.pos]
    refine Nat.mem_properDivisors.mpr ⟨?_, ?_⟩
    · have hdvd : p * e' ∣ p * w := by rw [← he', mul_comm p w]; exact hd_prop.1
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp hdvd
    · have hlt : p * e' < p * w := by rw [← he', mul_comm p w]; exact hd_prop.2
      exact Nat.lt_of_mul_lt_mul_left hlt
  have hT_ne : ∑ e ∈ T, e ≠ w := fun heq => hw.2 ⟨hw0, T, hT_sub, heq⟩
  have hT_le : ∑ e ∈ T, e ≤ w := Nat.le_of_mul_le_mul_right (by omega) hp.pos
  have hS2_ge : p ≤ ∑ d ∈ S₂, d := by
    have hT_lt : ∑ e ∈ T, e + 1 ≤ w := by omega
    nlinarith
  have hS2_sub : S₂ ⊆ w.divisors := by
    intro d hd2
    have ⟨hdS, hnpd⟩ := Finset.mem_filter.mp hd2
    have hd_dvd := (Nat.mem_properDivisors.mp (hS hdS)).1
    exact Nat.mem_divisors.mpr ⟨Nat.Coprime.dvd_of_dvd_mul_right
      ((hp.coprime_iff_not_dvd.mpr hnpd).symm) hd_dvd, hw0.ne'⟩
  have hS2_le : ∑ d ∈ S₂, d ≤ sigma w := Finset.sum_le_sum_of_subset hS2_sub
  omega

lemma sigma_70 : sigma 70 = 144 := by
  have h := sigma_two_pow_mul_prime_mul_prime (k := 1) (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- **UNCONDITIONAL MAYNARD–TAO BOUNDED-GAP WEIRD NUMBERS (`w₂ - w₁ ≤ 42000`, 0 ASSUMPTIONS!):**
Powered by `RHDirect.MaynardTao.maynard_tao_bounded_gaps_unconditional`: for every `N : ℕ`, there
exist weird numbers `N ≤ w₁ < w₂` with `w₂ - w₁ ≤ 42000` (and `w₁ = 70 * p`, `w₂ = 70 * q` for
primes `p < q` with `q - p ≤ 600`). -/
theorem weird_bounded_gaps_600_unconditional :
    ∀ N : ℕ, ∃ w₁ w₂ : ℕ, N ≤ w₁ ∧ w₁ < w₂ ∧ IsWeird w₁ ∧ IsWeird w₂ ∧ w₂ - w₁ ≤ 42000 := by
  intro N
  obtain ⟨p, q, hp_ge, hp, hq, hpq, hgap⟩ :=
    RHDirect.MaynardTao.maynard_tao_bounded_gaps_unconditional (max N 145)
  have hp_gt144 : sigma 70 < p := by
    rw [sigma_70]
    have : 145 ≤ p := le_trans (le_max_right N 145) hp_ge
    omega
  have hq_gt144 : sigma 70 < q := lt_trans hp_gt144 hpq
  have hp_geN : N ≤ p := le_trans (le_max_left N 145) hp_ge
  refine ⟨70 * p, 70 * q, by omega, by omega,
    isWeird_mul_prime_of_gt_sigma isPrimitiveWeird_70.1 hp hp_gt144,
    isWeird_mul_prime_of_gt_sigma isPrimitiveWeird_70.1 hq hq_gt144,
    by omega⟩

/-- **UNCONDITIONAL MAYNARD–TAO ARBITRARY `m`-TUPLES OF WEIRD NUMBERS IN BOUNDED DIAMETER:**
Powered by `RHDirect.MaynardTao.maynard_tao_m_tuples_unconditional`: for EVERY `m ≥ 1` and ANY
base weird number `w`, there exists `H : ℕ` such that for every `N : ℕ`, there exists a Finset `W`
of `m` weird numbers all `≥ N`, all multiples of `w` with distinct prime cofactors, and all lying
in a bounded interval of diameter `≤ H` (`∀ a ∈ W, ∀ b ∈ W, a ≤ b + H`). -/
theorem weird_m_tuples_bounded_diameter_unconditional {w : ℕ} (hw : IsWeird w)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ H : ℕ, ∀ N : ℕ, ∃ W : Finset ℕ, W.card = m ∧
      (∀ a ∈ W, N ≤ a ∧ IsWeird a ∧ w ∣ a ∧ (a / w).Prime) ∧
      ∀ a ∈ W, ∀ b ∈ W, a ≤ b + H := by
  obtain ⟨H₀, hMT⟩ := RHDirect.MaynardTao.maynard_tao_m_tuples_unconditional m hm
  refine ⟨w * H₀, fun N => ?_⟩
  obtain ⟨S, hScard, hSprimes, hSdiam⟩ := hMT (max N (sigma w + 1))
  have hw0 : 0 < w := hw.1.1
  set W := S.image (fun p => w * p)
  have hinj : Set.InjOn (fun p => w * p) (S : Set ℕ) :=
    fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hw0 h
  refine ⟨W, by rw [Finset.card_image_of_injOn hinj, hScard], ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨p, hpS, rfl⟩
    obtain ⟨hp_ge, hp_prime⟩ := hSprimes p hpS
    have hp_gt : sigma w < p := lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (le_max_right _ _) hp_ge)
    have hp_geN : N ≤ p := le_trans (le_max_left _ _) hp_ge
    refine ⟨?_, isWeird_mul_prime_of_gt_sigma hw hp_prime hp_gt, dvd_mul_right w p, ?_⟩
    · nlinarith
    · rwa [Nat.mul_div_cancel_left _ hw0]
  · intro a ha b hb
    rcases Finset.mem_image.mp ha with ⟨p, hpS, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨q, hqS, rfl⟩
    have hle := hSdiam p hpS q hqS
    calc w * p ≤ w * (q + H₀) := Nat.mul_le_mul_left w hle
      _ = w * q + w * H₀ := mul_add w q H₀

/-- **UNCONDITIONAL LINNIK-BOUNDED WEIRD NUMBERS IN EVERY COPRIME ARITHMETIC PROGRESSION:**
Powered by `RHDirect.Stage11LinnikUnconditional.linnikAPDyadic_unconditional`:
there exists an absolute constant `L ≥ 1` such that for ANY weird number `w`, ANY modulus `m ≥ 2`
coprime to `w`, and ANY residue class `b` coprime to `m`, there exists a weird number `n ≡ b [MOD m]`
with `(n : ℝ) ≤ (2 * w * (σ(w) + 1)) * m^L`! -/
theorem weird_in_every_coprime_ap_linnik_unconditional :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (w : ℕ), IsWeird w →
        ∀ (m b : ℕ), 2 ≤ m → Nat.Coprime w m → Nat.Coprime b m →
          ∃ n : ℕ, IsWeird n ∧ n ≡ b [MOD m] ∧
            (n : ℝ) ≤ (2 * (w : ℝ) * ((sigma w : ℝ) + 1)) * (m : ℝ) ^ L := by
  obtain ⟨L, hL1, hLinnik⟩ := RHDirect.Stage11LinnikUnconditional.linnikAPDyadic_unconditional
  refine ⟨L, hL1, fun w hw m b hm hwm hbm => ?_⟩
  have : NeZero m := ⟨by omega⟩
  let uZ : (ZMod m)ˣ := ZMod.unitOfCoprime w hwm
  set u : ℕ := (uZ⁻¹ : ZMod m).val
  have hwu : w * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    have h1 : (u : ZMod m) = ((uZ⁻¹ : (ZMod m)ˣ) : ZMod m) := ZMod.natCast_zmod_val _
    have h2 : (w : ZMod m) = (uZ : ZMod m) := rfl
    rw [h1, h2]
    exact_mod_cast Units.mul_inv uZ
  have hu_cop : Nat.Coprime u m := by
    have h1 : Nat.Coprime (w * u) m := by
      rw [Nat.Coprime]
      have hgcd : Nat.gcd (w * u) m = Nat.gcd 1 m := Nat.ModEq.gcd_eq hwu
      simpa using hgcd
    exact h1.coprime_mul_left
  set a := u * b
  have ha_cop : Nat.Coprime a m := hu_cop.mul_left hbm
  set X : ℝ := max ((m : ℝ) ^ L) ((sigma w : ℝ) + 1)
  have hX_ge : (m : ℝ) ^ L ≤ X := le_max_left _ _
  obtain ⟨p, hp, hmod_p, hp_gt_X, hp_le_2X⟩ := hLinnik m a hm ha_cop X hX_ge
  have hp_gt_sig : sigma w < p := by
    have h1 : (sigma w : ℝ) + 1 ≤ X := le_max_right _ _
    have h2 : (sigma w : ℝ) < (p : ℝ) := by linarith
    exact_mod_cast h2
  refine ⟨w * p, isWeird_mul_prime_of_gt_sigma hw hp hp_gt_sig, ?_, ?_⟩
  · have h1 : w * p ≡ w * (u * b) [MOD m] := Nat.ModEq.mul_left w hmod_p
    have h2 : (w * u) * b ≡ 1 * b [MOD m] := Nat.ModEq.mul_right b hwu
    calc w * p ≡ w * (u * b) [MOD m] := h1
      _ = (w * u) * b := by ring
      _ ≡ 1 * b [MOD m] := h2
      _ = b := one_mul b
  · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hmL_ge1 : (1 : ℝ) ≤ (m : ℝ) ^ L := Real.one_le_rpow (by linarith) (by linarith)
    have hsig_ge1 : (1 : ℝ) ≤ (sigma w : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (sigma w)]
    have hX_le : X ≤ ((sigma w : ℝ) + 1) * (m : ℝ) ^ L := by
      dsimp only [X]
      exact max_le (by nlinarith) (by nlinarith)
    have hw_nn : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
    push_cast
    nlinarith

/-- Concrete corollary for `w = 70`: Linnik-bounded weird numbers in EVERY arithmetic progression
`b [MOD m]` with `m ≥ 2`, `Nat.Coprime 70 m`, and `Nat.Coprime b m`. -/
theorem weird_in_every_ap_coprime_70_linnik :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ (m b : ℕ), 2 ≤ m → Nat.Coprime 70 m → Nat.Coprime b m →
        ∃ n : ℕ, IsWeird n ∧ n ≡ b [MOD m] ∧ (n : ℝ) ≤ 20300 * (m : ℝ) ^ L := by
  obtain ⟨L, hL1, h⟩ := weird_in_every_coprime_ap_linnik_unconditional
  refine ⟨L, hL1, fun m b hm h70 hbm => ?_⟩
  obtain ⟨n, hwn, hmod, hbd⟩ := h 70 isPrimitiveWeird_70.1 m b hm h70 hbm
  rw [sigma_70] at hbd
  refine ⟨n, hwn, hmod, ?_⟩
  norm_num at hbd ⊢
  exact hbd

/-! ## Axiom Audit for All Headline Theorems -/

#print axioms isPseudoperfect_two_pow_pq_of_le_sub_two
#print axioms isDeficient_two_pow_pq_of_ge_sub_one
#print axioms straddling_of_isWeird_two_pow_pq
#print axioms isPseudoperfect_two_pow_mul_semiprime_of_lt_sq
#print axioms gap0_interval_sqrt_barrier
#print axioms mod_r_obstruction_abundance_barrier
#print axioms isPrimitiveWeird_two_pow_pq_of_mod_p_ge
#print axioms isPrimitiveWeird_exact_ap_family
#print axioms isPrimitiveWeird_multi_prime_gap0
#print axioms isPrimitiveWeird_70
#print axioms isPrimitiveWeird_9272
#print axioms isPrimitiveWeird_73616
#print axioms isPrimitiveWeird_993360512
#print axioms isPrimitiveWeird_4030
#print axioms isPrimitiveWeird_45356
#print axioms isPrimitiveWeird_15126992
#print axioms infinite_primitiveWeird_of_exact_ap_infinitely_often
#print axioms weird_bounded_gaps_600_unconditional
#print axioms weird_m_tuples_bounded_diameter_unconditional
#print axioms weird_in_every_coprime_ap_linnik_unconditional
#print axioms weird_in_every_ap_coprime_70_linnik

end PPL086_MT
