import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# PPL 086 (Erdős Problem #470): Weird and Primitive Weird Numbers — Definitions & Structure

This module defines abundant, deficient, pseudoperfect (semiperfect), weird, and
primitive weird numbers, and proves the foundational unconditional structural theorems
for both even and odd weird numbers:

1. `isPseudoperfect_iff_abundance_subset_sum`: complement characterization via abundance `σ(n) - 2n`.
2. `isPseudoperfect_mul_of_isPseudoperfect`: every positive multiple of a pseudoperfect number is pseudoperfect.
3. `isPrimitiveWeird_iff_properDivisors_deficient`: a weird number is primitive weird iff every proper divisor is deficient.
4. `exists_primitiveWeird_dvd_of_isWeird`: every weird number has a primitive weird divisor.
5. `infinite_primitiveWeird_of_unbounded_min_odd_prime`: reduction of Erdős #470 Part A to finding weird numbers with arbitrarily large smallest odd prime factor.
6. `odd_prime_gt_two_pow_of_even_weird`: for any even weird `n = 2^k * m` (`m` odd), every odd prime `p ∣ m` satisfies `2^(k+1) < p`.
7. `not_dvd_three_of_even_weird`: no even weird number is divisible by `3`.
8. `three_le_card_primeFactors_of_isWeird`: EVERY weird number (even OR odd!) has at least `3` distinct prime factors.
9. `seven_le_card_primeFactors_of_odd_abundant_not_dvd_three`: every odd abundant (hence odd weird) number not divisible by `3` has at least `7` distinct prime factors.
10. `not_dvd_945_of_isWeird`: no weird number is divisible by `945` (the smallest odd abundant number).
-/

namespace PPL086

open Finset

/-- Sum of all positive divisors `σ(n) = ∑ d ∈ n.divisors, d`. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- Sum of proper divisors `s(n) = ∑ d ∈ n.properDivisors, d`. -/
def aliquotSum (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- A positive integer `n` is abundant if `σ(n) ≥ 2n`. -/
def IsAbundant (n : ℕ) : Prop :=
  0 < n ∧ 2 * n ≤ sigma n

/-- A positive integer `n` is strictly abundant if `σ(n) > 2n`. -/
def IsStrictlyAbundant (n : ℕ) : Prop :=
  0 < n ∧ 2 * n < sigma n

/-- A positive integer `n` is deficient if `σ(n) < 2n`. -/
def IsDeficient (n : ℕ) : Prop :=
  0 < n ∧ sigma n < 2 * n

/-- A positive integer `n` is pseudoperfect (semiperfect) if some subset of its proper divisors sums to `n`. -/
def IsPseudoperfect (n : ℕ) : Prop :=
  0 < n ∧ ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ ∑ d ∈ S, d = n

/-- A positive integer `n` is weird if it is abundant and not pseudoperfect. -/
def IsWeird (n : ℕ) : Prop :=
  IsAbundant n ∧ ¬ IsPseudoperfect n

/-- A positive integer `n` is primitive weird if it is weird and no proper divisor of `n` is weird. -/
def IsPrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d ∈ n.properDivisors, ¬ IsWeird d

/-! ## Section 1: Basic `sigma` and `aliquotSum` Identities -/

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

lemma sigma_prime_pow_mul_sub {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma (p ^ k) * (p - 1) = p ^ (k + 1) - 1 := by
  rw [sigma_prime_pow hp]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    have hp1 : 1 ≤ p := hp.one_le
    have hpow : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ hp.pos
    have hpow2 : 1 ≤ p ^ (k + 1 + 1) := Nat.one_le_pow _ _ hp.pos
    zify [hp1, hpow, hpow2]
    ring

lemma sigma_two_pow (k : ℕ) : sigma (2 ^ k) = 2 ^ (k + 1) - 1 := by
  have h := sigma_prime_pow_mul_sub Nat.prime_two k
  simpa using h

lemma sigma_prime_pow_lt {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma (p ^ k) * (p - 1) < p ^ (k + 1) := by
  rw [sigma_prime_pow_mul_sub hp]
  exact Nat.sub_lt (pow_pos hp.pos _) Nat.one_pos

lemma sigma_pos {n : ℕ} (hn : 0 < n) : 0 < sigma n := by
  unfold sigma
  exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd)
    ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩

lemma le_sigma {n : ℕ} (hn : 0 < n) : n ≤ sigma n := by
  unfold sigma
  exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self n hn.ne')

lemma sigma_one : sigma 1 = 1 := by
  unfold sigma; simp

lemma sigma_div_mono {d n : ℕ} (_hd : 0 < d) (hdn : d ∣ n) (hn : 0 < n) :
    sigma d * n ≤ sigma n * d := by
  obtain ⟨k, rfl⟩ := hdn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  -- Every divisor `x ∣ d` yields a distinct divisor `k * x ∣ d * k`
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

lemma sigma_div_strictMono {d n : ℕ} (hd : 0 < d) (hdn : d ∣ n) (hlt : d < n) :
    sigma d * n < sigma n * d := by
  have hn : 0 < n := lt_trans hd hlt
  obtain ⟨k, rfl⟩ := hdn
  have hk : 1 < k := by nlinarith
  have hk0 : 0 < k := by omega
  have hinj : Set.InjOn (fun x => k * x) (d.divisors : Set ℕ) :=
    fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hk0 h
  have hsub : d.divisors.image (fun x => k * x) ⊆ (d * k).divisors := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [Nat.mem_divisors] at hx ⊢
    exact ⟨by rw [mul_comm d k]; exact mul_dvd_mul_left k hx.1, hn.ne'⟩
  have h1_not : 1 ∉ d.divisors.image (fun x => k * x) := by
    intro h1
    rcases Finset.mem_image.mp h1 with ⟨x, hx, hkx⟩
    have hx1 : 1 ≤ x := Nat.pos_of_mem_divisors hx
    nlinarith
  have h1_mem : 1 ∈ (d * k).divisors := Nat.one_mem_divisors.mpr hn.ne'
  have hsum : k * sigma d + 1 ≤ sigma (d * k) := by
    unfold sigma
    rw [Finset.mul_sum]
    have himg : ∑ i ∈ d.divisors, k * i = ∑ y ∈ d.divisors.image (fun x => k * x), y :=
      (Finset.sum_image (f := id) hinj).symm
    have hins : insert 1 (d.divisors.image (fun x => k * x)) ⊆ (d * k).divisors :=
      Finset.insert_subset h1_mem hsub
    have hle : ∑ y ∈ insert 1 (d.divisors.image (fun x => k * x)), y ≤
        ∑ y ∈ (d * k).divisors, y := Finset.sum_le_sum_of_subset hins
    rw [Finset.sum_insert h1_not] at hle
    omega
  calc sigma d * (d * k) = (k * sigma d) * d := by ring
    _ < (k * sigma d + 1) * d := by nlinarith
    _ ≤ sigma (d * k) * d := Nat.mul_le_mul_right d hsum

lemma isDeficient_of_dvd_deficient {d n : ℕ} (hd : 0 < d) (hdn : d ∣ n) (hn : IsDeficient n) :
    IsDeficient d := by
  refine ⟨hd, ?_⟩
  have h1 := sigma_div_mono hd hdn hn.1
  have h2 := hn.2
  nlinarith

/-! ## Section 2: Complement Trick, Pseudoperfect Multiples, and Primitive Weird Characterization -/

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

lemma isPseudoperfect_of_perfect {n : ℕ} (hn : 0 < n) (hperf : sigma n = 2 * n) :
    IsPseudoperfect n := by
  refine ⟨hn, n.properDivisors, Finset.Subset.refl _, ?_⟩
  have hsig := sigma_eq_aliquotSum_add hn
  unfold aliquotSum at hsig
  omega

lemma isWeird_implies_strictlyAbundant {n : ℕ} (hw : IsWeird n) :
    IsStrictlyAbundant n := by
  refine ⟨hw.1.1, ?_⟩
  have hle := hw.1.2
  by_contra h
  have heq : sigma n = 2 * n := by omega
  exact hw.2 (isPseudoperfect_of_perfect hw.1.1 heq)

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

/-- A weird number `n` is primitive weird iff every proper divisor of `n` is deficient. -/
theorem isPrimitiveWeird_iff_properDivisors_deficient {n : ℕ} :
    IsPrimitiveWeird n ↔ IsWeird n ∧ ∀ d ∈ n.properDivisors, IsDeficient d := by
  constructor
  · rintro ⟨hw, hprim⟩
    refine ⟨hw, fun d hd => ?_⟩
    have hd_mem := Nat.mem_properDivisors.mp hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd_mem.1 hw.1.1
    refine ⟨hd0, ?_⟩
    by_contra hge
    push Not at hge
    have hd_ab : IsAbundant d := ⟨hd0, hge⟩
    have hd_np : ¬ IsPseudoperfect d := not_isPseudoperfect_of_dvd hd_mem.1 hw.1.1 hw.2
    exact hprim d hd ⟨hd_ab, hd_np⟩
  · rintro ⟨hw, hdef⟩
    refine ⟨hw, fun d hd hdw => ?_⟩
    have h1 := (hdef d hd).2
    have h2 := hdw.1.2
    omega

/-- Every weird number is divisible by a primitive weird number. -/
theorem exists_primitiveWeird_dvd_of_isWeird {n : ℕ} (hw : IsWeird n) :
    ∃ d : ℕ, d ∣ n ∧ IsPrimitiveWeird d := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hprim : ∀ d ∈ n.properDivisors, ¬ IsWeird d
    · exact ⟨n, dvd_rfl, hw, hprim⟩
    · push Not at hprim
      obtain ⟨d, hd_mem, hdw⟩ := hprim
      have hd_prop := Nat.mem_properDivisors.mp hd_mem
      obtain ⟨e, hed, hep⟩ := ih d hd_prop.2 hdw
      exact ⟨e, dvd_trans hed hd_prop.1, hep⟩

/-- Prime powers are always deficient, hence never weird. -/
lemma isDeficient_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : IsDeficient (p ^ k) := by
  refine ⟨pow_pos hp.pos k, ?_⟩
  have h1 := sigma_prime_pow_lt hp k
  have hp2 : 2 ≤ p := hp.two_le
  have hmul : sigma (p ^ k) * (p - 1) < (2 * p ^ k) * (p - 1) := by
    have h2 : p ^ (k + 1) = p ^ k * p := pow_succ p k
    have h3 : p ≤ 2 * (p - 1) := by omega
    calc sigma (p ^ k) * (p - 1) < p ^ (k + 1) := h1
      _ = p ^ k * p := h2
      _ ≤ p ^ k * (2 * (p - 1)) := Nat.mul_le_mul_left _ h3
      _ = (2 * p ^ k) * (p - 1) := by ring
  exact Nat.lt_of_mul_lt_mul_right hmul

lemma not_isWeird_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : ¬ IsWeird (p ^ k) := by
  intro hw
  have h1 := (isDeficient_prime_pow hp k).2
  have h2 := hw.1.2
  omega

lemma not_isWeird_one : ¬ IsWeird 1 := by
  have h := not_isWeird_prime_pow Nat.prime_two 0
  simpa using h

/-- **Reduction Theorem for Erdős Problem #470 Part A:**
If for every `B : ℕ`, there exists a weird number `n` whose every odd prime factor exceeds `B`,
then there are infinitely many primitive weird numbers. -/
theorem infinite_primitiveWeird_of_unbounded_min_odd_prime
    (h : ∀ B : ℕ, ∃ n : ℕ, IsWeird n ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ n → B < p) :
    {n : ℕ | IsPrimitiveWeird n}.Infinite := by
  rw [Set.infinite_iff_exists_gt]
  intro B
  obtain ⟨n, hwn, hodd⟩ := h B
  obtain ⟨d, hdn, hpd⟩ := exists_primitiveWeird_dvd_of_isWeird hwn
  have hd0 : 0 < d := hpd.1.1.1
  -- `d` cannot be a power of `2` (since powers of `2` are deficient)
  have hex_odd : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ d := by
    by_contra hall
    push Not at hall
    have hpow : d = 2 ^ (d.factorization 2) := by
      have hfac := Nat.prod_factorization_pow_eq_self hd0.ne'
      rw [Finsupp.prod] at hfac
      have hsupp : d.factorization.support ⊆ {2} := by
        intro p hp
        rw [Finset.mem_singleton]
        by_contra hp2
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
        exact hall p hprime hp2 hdvd
      by_cases h2 : 2 ∈ d.factorization.support
      · have heq : d.factorization.support = {2} :=
          Finset.Subset.antisymm hsupp (Finset.singleton_subset_iff.mpr h2)
        rw [heq, Finset.prod_singleton] at hfac
        exact hfac.symm
      · have heq : d.factorization.support = ∅ := by
          ext p
          simp only [Finset.notMem_empty, iff_false]
          intro hp
          have hp2 := Finset.mem_singleton.mp (hsupp hp)
          subst hp2
          exact h2 hp
        rw [heq, Finset.prod_empty] at hfac
        have hz : d.factorization 2 = 0 := Finsupp.notMem_support_iff.mp h2
        rw [hz, pow_zero, ← hfac]
    rw [hpow] at hpd
    exact not_isWeird_prime_pow Nat.prime_two _ hpd.1
  obtain ⟨p, hp, hp2, hpdvd⟩ := hex_odd
  have hBp : B < p := hodd p hp hp2 (dvd_trans hpdvd hdn)
  have hpd_le : p ≤ d := Nat.le_of_dvd hd0 hpdvd
  exact ⟨d, hpd, lt_of_lt_of_le hBp hpd_le⟩

/-! ## Section 3: Binary Subset-Sum Lemma & Even Weird Number Structure -/

/-- Every natural number `x < 2 ^ (k + 1)` is a subset sum of `{2^j | j ≤ k}`. -/
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

/-- If `p` is an odd prime with `p < 2^(k+1)`, then `2^k * p` is pseudoperfect! -/
lemma isPseudoperfect_two_pow_mul_prime {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : p < 2 ^ (k + 1)) : IsPseudoperfect (2 ^ k * p) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow_left k
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

/-- **Fundamental Structure Theorem for Even Weird Numbers:**
If `n = 2^k * m` (`k ≥ 1`, `m` odd) is weird, then every odd prime `p ∣ m` satisfies `2^(k+1) < p`. -/
theorem odd_prime_gt_two_pow_of_even_weird {n k m p : ℕ} (hw : IsWeird n)
    (hn : n = 2 ^ k * m) (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m) :
    2 ^ (k + 1) < p := by
  by_contra hle
  push Not at hle
  have hlt : p < 2 ^ (k + 1) := by
    have hne : p ≠ 2 ^ (k + 1) := by
      intro heq
      have h2p : 2 ∣ p := by rw [heq]; exact dvd_pow_self 2 (Nat.succ_ne_zero k)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p).symm
    omega
  have hpp : IsPseudoperfect (2 ^ k * p) := isPseudoperfect_two_pow_mul_prime hp hp2 hlt
  have hdvd : 2 ^ k * p ∣ n := by rw [hn]; exact mul_dvd_mul_left _ hpm
  exact not_isPseudoperfect_of_dvd hdvd hw.1.1 hw.2 hpp

/-- **No even weird number is divisible by `3`.** -/
theorem not_dvd_three_of_even_weird {n : ℕ} (hw : IsWeird n) (heven : 2 ∣ n) : ¬ (3 ∣ n) := by
  intro h3
  have h6 : 6 ∣ n := (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) heven h3)
  have hpp6 : IsPseudoperfect 6 := isPseudoperfect_of_perfect (by norm_num) (by
    unfold sigma; decide)
  exact not_isPseudoperfect_of_dvd h6 hw.1.1 hw.2 hpp6

/-- **Every even weird number has at least `3` distinct prime factors.** -/
theorem three_le_card_primeFactors_of_even_weird {n : ℕ} (hw : IsWeird n) (heven : 2 ∣ n) :
    3 ≤ n.primeFactors.card := by
  have hn0 : 0 < n := hw.1.1
  set k := n.factorization 2 with hk_def
  have hk_pos : 1 ≤ k := by
    have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, heven, hn0.ne'⟩
    have : 0 < n.factorization 2 := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp h2mem)
    omega
  have h2pow_dvd : 2 ^ k ∣ n := Nat.ordProj_dvd n 2
  obtain ⟨m, hm⟩ := h2pow_dvd
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left (hm ▸ hn0)
  have hm_odd : ¬ (2 ∣ m) := by
    intro h2m
    have hpow : 2 ^ (k + 1) ∣ n := by
      rw [hm, pow_succ]
      exact mul_dvd_mul_left _ h2m
    have hle : k + 1 ≤ n.factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0.ne').mp hpow
    omega
  have hcop : Nat.Coprime (2 ^ k) m :=
    (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (Nat.mod_two_ne_zero.mp (fun h => hm_odd (Nat.dvd_of_mod_eq_zero h))))).pow_left k
  have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, heven, hn0.ne'⟩
  -- `n.primeFactors = insert 2 m.primeFactors` and `2 ∉ m.primeFactors`
  have h2notm : 2 ∉ m.primeFactors := fun h => hm_odd (Nat.dvd_of_mem_primeFactors h)
  have hcard_eq : n.primeFactors.card = m.primeFactors.card + 1 := by
    rw [hm, Nat.primeFactors_mul (by positivity) hm0.ne',
        Nat.primeFactors_pow 2 (by omega), Nat.Prime.primeFactors Nat.prime_two,
        Finset.singleton_union, Finset.card_insert_of_notMem h2notm]
  -- So it suffices to show `2 ≤ m.primeFactors.card`
  suffices h2m : 2 ≤ m.primeFactors.card by omega
  by_contra hlt
  have hle1 : m.primeFactors.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
  · -- `m = 1`, so `n = 2^k`
    have hm1 : m = 1 := by
      have := Nat.prod_factorization_pow_eq_self hm0.ne'
      rw [Finsupp.prod] at this
      have hemp : m.factorization.support = ∅ := Finset.card_eq_zero.mp h0
      rw [hemp, Finset.prod_empty] at this
      exact this.symm
    rw [hm, hm1, mul_one] at hw
    exact not_isWeird_prime_pow Nat.prime_two k hw
  · -- `m = p^a` for a single odd prime `p`
    obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
    have hp_mem : p ∈ m.primeFactors := by rw [hp_eq]; simp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp_mem
    have hp2 : p ≠ 2 := fun heq => h2notm (heq ▸ hp_mem)
    have hpgt : 2 ^ (k + 1) < p := odd_prime_gt_two_pow_of_even_weird hw hm hp hp2 hpm
    have hm_pow : m = p ^ (m.factorization p) := by
      have hfac := Nat.prod_factorization_pow_eq_self hm0.ne'
      rw [Finsupp.prod] at hfac
      change (∏ x ∈ m.primeFactors, x ^ m.factorization x) = m at hfac
      rw [hp_eq, Finset.prod_singleton] at hfac
      exact hfac.symm
    -- Now `σ(n) = (2^(k+1) - 1) * σ(p^a) < 2^(k+1) * p^a = 2 * n`, contradicting abundance!
    set a := m.factorization p
    have hsig_n : sigma n = (2 ^ (k + 1) - 1) * sigma (p ^ a) := by
      rw [hm, sigma_mul_of_coprime hcop, sigma_two_pow, hm_pow]
    have hpa_lt := sigma_prime_pow_lt hp a
    have hab := hw.1.2
    rw [hsig_n, hm, hm_pow] at hab
    -- `(2^(k+1) - 1) * σ(p^a) * (p - 1) < (2^(k+1) - 1) * p^(a+1)`
    -- while `2 * (2^k * p^a) * (p - 1) = 2^(k+1) * p^a * (p - 1)`
    -- And `(2^(k+1) - 1) * p < 2^(k+1) * (p - 1)` iff `2^(k+1) < p`!
    have hp1 : 1 ≤ p := hp.one_le
    have h2ge1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hstep1 : (2 ^ (k + 1) - 1) * sigma (p ^ a) * (p - 1) < (2 ^ (k + 1) - 1) * p ^ (a + 1) := by
      rw [mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left hpa_lt (by
        have : 2 ≤ 2 ^ (k + 1) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
    have hstep2 : (2 ^ (k + 1) - 1) * p ^ (a + 1) < 2 ^ (k + 1) * p ^ a * (p - 1) := by
      have hkey : (2 ^ (k + 1) - 1) * p < 2 ^ (k + 1) * (p - 1) := by
        zify [h2ge1, hp1]; nlinarith
      calc (2 ^ (k + 1) - 1) * p ^ (a + 1)
          = ((2 ^ (k + 1) - 1) * p) * p ^ a := by rw [pow_succ]; ring
        _ < (2 ^ (k + 1) * (p - 1)) * p ^ a := Nat.mul_lt_mul_of_pos_right hkey (pow_pos hp.pos a)
        _ = 2 ^ (k + 1) * p ^ a * (p - 1) := by ring
    have hstep3 : 2 * (2 ^ k * p ^ a) * (p - 1) = 2 ^ (k + 1) * p ^ a * (p - 1) := by
      rw [pow_succ]; ring
    have hhab : 2 * (2 ^ k * p ^ a) * (p - 1) ≤ (2 ^ (k + 1) - 1) * sigma (p ^ a) * (p - 1) :=
      Nat.mul_le_mul_right (p - 1) hab
    omega

/-! ## Section 4: Odd Abundant & Odd Weird Number Structural Lower Bounds (Erdős #470 Part B) -/

/-- Rational upper bound on `σ(n) / n`:
`σ(n) * ∏_{p ∈ n.primeFactors} (p - 1) ≤ n * ∏_{p ∈ n.primeFactors} p`, with strict inequality for `n > 1`. -/
lemma sigma_mul_prod_pred_le (n : ℕ) (hn : 0 < n) :
    sigma n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  -- Induction on `n.primeFactors.card`
  induction hcard : n.primeFactors.card generalizing n with
  | zero =>
    have hn1 : n = 1 := by
      have hfac := Nat.prod_factorization_pow_eq_self hn.ne'
      rw [Finsupp.prod] at hfac
      have hemp : n.factorization.support = ∅ := Finset.card_eq_zero.mp hcard
      rw [hemp, Finset.prod_empty] at hfac
      exact hfac.symm
    subst hn1
    simp [sigma_one]
  | succ k ih =>
    have hne : n.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p, hp_mem⟩ := hne
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    set a := n.factorization p
    have ha_pos : 1 ≤ a := by
      have : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
      omega
    have hpow_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
    obtain ⟨m, hm⟩ := hpow_dvd
    have hm0 : 0 < m := Nat.pos_of_mul_pos_left (hm ▸ hn)
    have hp_not_m : ¬ (p ∣ m) := by
      intro hpm
      have hpow : p ^ (a + 1) ∣ n := by rw [hm, pow_succ]; exact mul_dvd_mul_left _ hpm
      have hle : a + 1 ≤ n.factorization p :=
        (Nat.Prime.pow_dvd_iff_le_factorization hp hn.ne').mp hpow
      omega
    have hcop : Nat.Coprime (p ^ a) m := (hp.coprime_iff_not_dvd.mpr hp_not_m).pow_left a
    have hp_not_pf : p ∉ m.primeFactors := fun h => hp_not_m (Nat.dvd_of_mem_primeFactors h)
    have hpf_eq : n.primeFactors = insert p m.primeFactors := by
      rw [hm, Nat.primeFactors_mul (pow_pos hp.pos a).ne' hm0.ne',
          Nat.primeFactors_pow p (by omega), hp.primeFactors, Finset.singleton_union]
    have hm_card : m.primeFactors.card = k := by
      rw [hpf_eq, Finset.card_insert_of_notMem hp_not_pf] at hcard
      omega
    have ihm := ih m hm0 hm_card
    have hsig_eq : sigma n = sigma (p ^ a) * sigma m := by
      rw [hm, sigma_mul_of_coprime hcop]
    have hpa_le : sigma (p ^ a) * (p - 1) ≤ p ^ a * p := by
      have hlt := sigma_prime_pow_lt hp a
      rw [pow_succ] at hlt
      omega
    rw [hsig_eq, hpf_eq, Finset.prod_insert hp_not_pf, Finset.prod_insert hp_not_pf]
    calc sigma (p ^ a) * sigma m * ((p - 1) * ∏ x ∈ m.primeFactors, (x - 1))
        = (sigma (p ^ a) * (p - 1)) * (sigma m * ∏ x ∈ m.primeFactors, (x - 1)) := by ring
      _ ≤ (p ^ a * p) * (m * ∏ x ∈ m.primeFactors, x) := Nat.mul_le_mul hpa_le ihm
      _ = (p ^ a * m) * (p * ∏ x ∈ m.primeFactors, x) := by ring
      _ = n * (p * ∏ x ∈ m.primeFactors, x) := by rw [← hm]

/-- Strict version of `sigma_mul_prod_pred_le` when `n > 1` (i.e. `n.primeFactors.Nonempty`). -/
lemma sigma_mul_prod_pred_lt {n : ℕ} (hn : 1 < n) :
    sigma n * ∏ p ∈ n.primeFactors, (p - 1) < n * ∏ p ∈ n.primeFactors, p := by
  have hn0 : 0 < n := by omega
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  obtain ⟨p, hp_mem⟩ := hne
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  set a := n.factorization p
  have ha_pos : 1 ≤ a := by
    have : 0 < n.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_mem)
    omega
  obtain ⟨m, hm⟩ := Nat.ordProj_dvd n p
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left (hm ▸ hn0)
  have hp_not_m : ¬ (p ∣ m) := by
    intro hpm
    have hpow : p ^ (a + 1) ∣ n := by rw [hm, pow_succ]; exact mul_dvd_mul_left _ hpm
    have hle : a + 1 ≤ n.factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hn0.ne').mp hpow
    omega
  have hcop : Nat.Coprime (p ^ a) m := (hp.coprime_iff_not_dvd.mpr hp_not_m).pow_left a
  have hp_not_pf : p ∉ m.primeFactors := fun h => hp_not_m (Nat.dvd_of_mem_primeFactors h)
  have hpf_eq : n.primeFactors = insert p m.primeFactors := by
    rw [hm, Nat.primeFactors_mul (pow_pos hp.pos a).ne' hm0.ne',
        Nat.primeFactors_pow p (by omega), hp.primeFactors, Finset.singleton_union]
  have ihm := sigma_mul_prod_pred_le m hm0
  have hsig_eq : sigma n = sigma (p ^ a) * sigma m := by
    rw [hm, sigma_mul_of_coprime hcop]
  have hpa_lt : sigma (p ^ a) * (p - 1) < p ^ a * p := by
    simpa [pow_succ] using sigma_prime_pow_lt hp a
  have hpos_m : 0 < m * ∏ x ∈ m.primeFactors, x := by
    refine Nat.mul_pos hm0 (Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors hx).pos)
  have hpos_sm : 0 < sigma m * ∏ x ∈ m.primeFactors, (x - 1) := by
    refine Nat.mul_pos (sigma_pos hm0) (Finset.prod_pos fun x hx => ?_)
    have hx2 := (Nat.prime_of_mem_primeFactors hx).two_le; omega
  rw [hsig_eq, hpf_eq, Finset.prod_insert hp_not_pf, Finset.prod_insert hp_not_pf]
  calc sigma (p ^ a) * sigma m * ((p - 1) * ∏ x ∈ m.primeFactors, (x - 1))
      = (sigma (p ^ a) * (p - 1)) * (sigma m * ∏ x ∈ m.primeFactors, (x - 1)) := by ring
    _ < (p ^ a * p) * (sigma m * ∏ x ∈ m.primeFactors, (x - 1)) :=
        Nat.mul_lt_mul_of_pos_right hpa_lt hpos_sm
    _ ≤ (p ^ a * p) * (m * ∏ x ∈ m.primeFactors, x) :=
        Nat.mul_le_mul_left _ ihm
    _ = (p ^ a * m) * (p * ∏ x ∈ m.primeFactors, x) := by ring
    _ = n * (p * ∏ x ∈ m.primeFactors, x) := by rw [← hm]

/-- Monotonicity of `p / (p - 1)` in `ℚ`: if `2 ≤ a ≤ b`, then `(b : ℚ) / (b - 1) ≤ a / (a - 1)`. -/
lemma rat_div_pred_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b : ℚ) / ((b - 1 : ℕ) : ℚ) ≤ (a : ℚ) / ((a - 1 : ℕ) : ℚ) := by
  have ha1 : (0 : ℚ) < ((a - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < a - 1)
  have hb1 : (0 : ℚ) < ((b - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < b - 1)
  rw [div_le_div_iff₀ hb1 ha1]
  have hcast_a : ((a - 1 : ℕ) : ℚ) = (a : ℚ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ a)
  have hcast_b : ((b - 1 : ℕ) : ℚ) = (b : ℚ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ b)
  rw [hcast_a, hcast_b]
  have habq : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  nlinarith

/-- For any abundant number `n`, `2 < ∏_{p ∈ n.primeFactors} (p / (p - 1))` in `ℚ`. -/
lemma two_lt_prod_prime_div_pred_of_isAbundant {n : ℕ} (hab : IsAbundant n) :
    (2 : ℚ) < ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) := by
  have hn1 : 1 < n := by
    by_contra hle
    have hn1' : n = 1 := by have := hab.1; omega
    subst hn1'
    have := hab.2
    rw [sigma_one] at this; omega
  have hlt := sigma_mul_prod_pred_lt hn1
  have h2n : 2 * n * ∏ p ∈ n.primeFactors, (p - 1) < n * ∏ p ∈ n.primeFactors, p := by
    calc 2 * n * ∏ p ∈ n.primeFactors, (p - 1)
        ≤ sigma n * ∏ p ∈ n.primeFactors, (p - 1) := Nat.mul_le_mul_right _ hab.2
      _ < n * ∏ p ∈ n.primeFactors, p := hlt
  have h2prod : 2 * ∏ p ∈ n.primeFactors, (p - 1) < ∏ p ∈ n.primeFactors, p :=
    Nat.lt_of_mul_lt_mul_left (by simpa [mul_assoc, mul_left_comm] using h2n)
  have hprod_pos : (0 : ℚ) < ∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℚ) := by
    refine Finset.prod_pos fun p hp => ?_
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    exact_mod_cast (by omega : 0 < p - 1)
  rw [Finset.prod_div_distrib, lt_div_iff₀ hprod_pos]
  have hcast : ((2 * ∏ p ∈ n.primeFactors, (p - 1) : ℕ) : ℚ) <
      ((∏ p ∈ n.primeFactors, p : ℕ) : ℚ) := by exact_mod_cast h2prod
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_prod] using hcast

/-- **Every odd abundant (hence every odd weird) number has at least `3` distinct prime factors.** -/
theorem three_le_card_primeFactors_of_odd_abundant {n : ℕ} (hab : IsAbundant n) (hodd : ¬ (2 ∣ n)) :
    3 ≤ n.primeFactors.card := by
  by_contra hlt
  have hle2 : n.primeFactors.card ≤ 2 := by omega
  have hprod_gt := two_lt_prod_prime_div_pred_of_isAbundant hab
  -- Every prime in `n.primeFactors` is `≥ 3`, and at most `2` distinct primes, so product `≤ (3/2) * (5/4)`?
  -- Even simpler: every prime is `≥ 3`, so each factor is `≤ 3/2`, except wait: `(3/2)^2 = 9/4 > 2`!
  -- So use distinctness: if `card = 2`, the two primes are `p < q` with `3 ≤ p` and `5 ≤ q`!
  have hbound : ∏ p ∈ n.primeFactors, ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) ≤ 2 := by
    rcases Nat.le_iff_lt_or_eq.mp hle2 with hlt2 | heq2
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : n.primeFactors.card ≤ 1) with h0 | h1
      · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]; norm_num
      · obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp h1
        have hp_mem : p ∈ n.primeFactors := by rw [hp_eq]; simp
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
        have hp2 : p ≠ 2 := fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hp_mem)
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        rw [hp_eq, Finset.prod_singleton]
        exact (rat_div_pred_anti (by norm_num) hp3).trans (by norm_num)
    · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp heq2
      have hpm : p ∈ n.primeFactors := by rw [hset]; simp
      have hqm : q ∈ n.primeFactors := by rw [hset]; simp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hqm
      have hp2 : p ≠ 2 := fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hpm)
      have hq2 : q ≠ 2 := fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hqm)
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hq3 : 3 ≤ q := by have := hq.two_le; omega
      rw [hset, Finset.prod_pair hpq]
      -- One of `p, q` is `≥ 5` since `p ≠ q` are odd primes `≥ 3` (cannot be 4)
      have hor : (3 ≤ p ∧ 5 ≤ q) ∨ (5 ≤ p ∧ 3 ≤ q) := by
        rcases lt_or_gt_of_ne hpq with hlt_pq | hlt_qp
        · left
          refine ⟨hp3, ?_⟩
          have hq4 : q ≠ 4 := fun h => by subst h; norm_num at hq
          omega
        · right
          refine ⟨?_, hq3⟩
          have hp4 : p ≠ 4 := fun h => by subst h; norm_num at hp
          omega
      rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a1 := rat_div_pred_anti (by norm_num) h1
        have a2 := rat_div_pred_anti (by norm_num) h2
        have hpos1 : (0 : ℚ) ≤ (p : ℚ) / ((p - 1 : ℕ) : ℚ) := by positivity
        have hpos2 : (0 : ℚ) ≤ (3 : ℚ) / ((3 - 1 : ℕ) : ℚ) := by positivity
        calc ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) * ((q : ℚ) / ((q - 1 : ℕ) : ℚ))
            ≤ ((3 : ℚ) / ((3 - 1 : ℕ) : ℚ)) * ((5 : ℚ) / ((5 - 1 : ℕ) : ℚ)) :=
              mul_le_mul a1 a2 (by positivity) (by positivity)
          _ ≤ 2 := by norm_num
      · have a1 := rat_div_pred_anti (by norm_num) h1
        have a2 := rat_div_pred_anti (by norm_num) h2
        calc ((p : ℚ) / ((p - 1 : ℕ) : ℚ)) * ((q : ℚ) / ((q - 1 : ℕ) : ℚ))
            ≤ ((5 : ℚ) / ((5 - 1 : ℕ) : ℚ)) * ((3 : ℚ) / ((3 - 1 : ℕ) : ℚ)) :=
              mul_le_mul a1 a2 (by positivity) (by positivity)
          _ ≤ 2 := by norm_num
  linarith

/-- **Universal Lower Bound for ALL Weird Numbers (Even OR Odd):**
Every weird number has at least `3` distinct prime factors. -/
theorem three_le_card_primeFactors_of_isWeird {n : ℕ} (hw : IsWeird n) :
    3 ≤ n.primeFactors.card := by
  by_cases heven : 2 ∣ n
  · exact three_le_card_primeFactors_of_even_weird hw heven
  · exact three_le_card_primeFactors_of_odd_abundant hw.1 heven

/-- Helper: sorted list of `k ≤ 6` distinct odd primes `≥ 5` satisfies `∏ p/(p-1) ≤ (5/4)(7/6)(11/10)(13/12)(17/16)(19/18) < 2`. -/
private lemma odd_primes_ge5_lower (L : List ℕ) (hsorted : L.Pairwise (· < ·))
    (hprimes : ∀ p ∈ L, p.Prime ∧ 5 ≤ p) :
    ∀ i (hi : i < L.length) (hi6 : i < 6),
      ([5, 7, 11, 13, 17, 19][i]'(by simp; omega)) ≤ L[i]'hi := by
  intro i
  induction i with
  | zero =>
    intro hi _
    exact (hprimes L[0] (List.getElem_mem hi)).2
  | succ i ih =>
    intro hi hi6
    have hi_prev : i < L.length := by omega
    have hprev := ih hi_prev (by omega)
    have hlt : L[i]'hi_prev < L[i + 1]'hi :=
      List.pairwise_iff_getElem.mp hsorted i (i + 1) hi_prev hi (by omega)
    have hp_cur : (L[i + 1]'hi).Prime := (hprimes _ (List.getElem_mem hi)).1
    rcases i with _ | _ | _ | _ | _ | i
    · simp only [Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ] at hprev hlt hp_cur ⊢
      by_contra h
      have h6 : L[1]'hi = 6 := by omega
      rw [h6] at hp_cur; norm_num at hp_cur
    · simp only [Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ] at hprev hlt hp_cur ⊢
      by_contra h
      have hor : L[2]'hi = 8 ∨ L[2]'hi = 9 ∨ L[2]'hi = 10 := by omega
      rcases hor with heq | heq | heq <;> (rw [heq] at hp_cur; norm_num at hp_cur)
    · simp only [Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ] at hprev hlt hp_cur ⊢
      by_contra h
      have h12 : L[3]'hi = 12 := by omega
      rw [h12] at hp_cur; norm_num at hp_cur
    · simp only [Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ] at hprev hlt hp_cur ⊢
      by_contra h
      have hor : L[4]'hi = 14 ∨ L[4]'hi = 15 ∨ L[4]'hi = 16 := by omega
      rcases hor with heq | heq | heq <;> (rw [heq] at hp_cur; norm_num at hp_cur)
    · simp only [Nat.reduceAdd, List.getElem_cons_zero, List.getElem_cons_succ] at hprev hlt hp_cur ⊢
      by_contra h
      have h18 : L[5]'hi = 18 := by omega
      rw [h18] at hp_cur; norm_num at hp_cur
    · omega

/-- **Erdős #470 Part B Structural Bound:**
Every odd abundant (hence every odd weird) number NOT divisible by `3` has at least `7` distinct prime factors! -/
theorem seven_le_card_primeFactors_of_odd_abundant_not_dvd_three {n : ℕ}
    (hab : IsAbundant n) (hodd : ¬ (2 ∣ n)) (h3 : ¬ (3 ∣ n)) :
    7 ≤ n.primeFactors.card := by
  by_contra hlt
  have hle6 : n.primeFactors.card ≤ 6 := by omega
  have hprod_gt := two_lt_prod_prime_div_pred_of_isAbundant hab
  set L := n.primeFactors.sort (· ≤ ·) with hL_def
  have hL_len : L.length = n.primeFactors.card := Finset.length_sort (· ≤ ·)
  have hL_nodup : L.Nodup := Finset.sort_nodup n.primeFactors (· ≤ ·)
  have hL_sorted_le : L.Pairwise (· ≤ ·) := Finset.pairwise_sort n.primeFactors (· ≤ ·)
  have hL_sorted : L.Pairwise (· < ·) := by
    rw [List.pairwise_iff_get] at hL_sorted_le ⊢
    intro i j hij
    have hle := hL_sorted_le i j hij
    have hne : L.get i ≠ L.get j := fun heq => (ne_of_lt hij) (hL_nodup.get_inj_iff.mp heq)
    omega
  have hL_primes : ∀ p ∈ L, p.Prime ∧ 5 ≤ p := by
    intro p hp
    have hpm : p ∈ n.primeFactors := (Finset.mem_sort (· ≤ ·)).mp hp
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hpm
    have hp2 : p ≠ 2 := fun h => hodd (h ▸ Nat.dvd_of_mem_primeFactors hpm)
    have hp3 : p ≠ 3 := fun h => h3 (h ▸ Nat.dvd_of_mem_primeFactors hpm)
    have hp4 : p ≠ 4 := fun h => by subst h; norm_num at hpr
    exact ⟨hpr, by have := hpr.two_le; omega⟩
  have hlow := odd_primes_ge5_lower L hL_sorted hL_primes
  set f : ℕ → ℚ := fun p => (p : ℚ) / ((p - 1 : ℕ) : ℚ)
  -- Rewrite the `Finset.prod` as a `List.prod` over `L`
  have hprod_eq : ∏ p ∈ n.primeFactors, f p = (L.map f).prod := by
    have hcoe : (L : Multiset ℕ) = n.primeFactors.val := Finset.sort_eq n.primeFactors (· ≤ ·)
    change (n.primeFactors.val.map f).prod = (L.map f).prod
    rw [← hcoe, Multiset.map_coe, Multiset.prod_coe]
  -- Bound `(L.map f).prod` by `∏_{i < L.length} f(target[i]) ≤ ∏_{i < 6} f(target[i]) < 2`
  set targets : List ℕ := [5, 7, 11, 13, 17, 19]
  have hlist_prod_le : (L.map f).prod ≤ ((targets.take L.length).map f).prod := by
    have hlen_eq : (L.map f).length = ((targets.take L.length).map f).length := by
      simp [targets]; omega
    have hfin : ∀ (A B : List ℚ), A.length = B.length →
        (∀ i (hiA : i < A.length) (hiB : i < B.length), 0 ≤ A[i]'hiA ∧ A[i]'hiA ≤ B[i]'hiB) →
        A.prod ≤ B.prod := by
      intro A
      induction A with
      | nil =>
        intro B hlen _
        cases B with
        | nil => simp
        | cons _ _ => simp at hlen
      | cons a as iha =>
        intro B hlen hle
        cases B with
        | nil => simp at hlen
        | cons b bs =>
          simp only [List.prod_cons]
          have h0 := hle 0 (by simp) (by simp)
          simp only [List.getElem_cons_zero] at h0
          have htail : as.prod ≤ bs.prod := iha bs (by simpa using hlen) (fun i hiA hiB =>
            hle (i + 1) (by simpa using hiA) (by simpa using hiB))
          have has_nonneg : 0 ≤ as.prod := List.prod_nonneg (fun x hx => by
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
            exact (hle (i + 1) (by simpa using hi) (by simpa [← hlen] using hi)).1)
          exact mul_le_mul h0.2 htail has_nonneg (le_trans h0.1 h0.2)
    refine hfin _ _ hlen_eq (fun i hiA hiB => ?_)
    have hiL : i < L.length := by simpa using hiA
    have hi6 : i < 6 := by omega
    simp only [List.getElem_map, List.getElem_take]
    refine ⟨by dsimp only [f]; positivity, ?_⟩
    have hti_ge2 : 2 ≤ targets[i]'(by simp [targets]; omega) := by
      have hi6' : i < 6 := hi6
      interval_cases i <;> norm_num [targets]
    have hle_i : targets[i]'(by simp [targets]; omega) ≤ L[i]'hiL := hlow i hiL hi6
    exact rat_div_pred_anti hti_ge2 hle_i
  -- And `((targets.take k).map f).prod < 2` for every `k ≤ 6`!
  have htake_lt_all : ∀ k ≤ 6, ((targets.take k).map f).prod < 2 := by
    intro k hk
    interval_cases k <;> norm_num [targets, f]
  have htake_lt : ((targets.take L.length).map f).prod < 2 := htake_lt_all L.length (by omega)
  have hprod_gt' : (2 : ℚ) < (L.map f).prod := hprod_eq ▸ hprod_gt
  linarith

/-- `945 = 3^3 * 5 * 7` (the smallest odd abundant number) is pseudoperfect,
so NO weird number is divisible by `945`. -/
theorem isPseudoperfect_945 : IsPseudoperfect 945 := by
  refine ⟨by norm_num, {1, 9, 21, 27, 35, 45, 63, 105, 135, 189, 315}, ?_, by norm_num⟩
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Nat.mem_properDivisors.mpr ⟨by norm_num, by norm_num⟩

theorem not_dvd_945_of_isWeird {n : ℕ} (hw : IsWeird n) : ¬ (945 ∣ n) :=
  fun h => not_isPseudoperfect_of_dvd h hw.1.1 hw.2 isPseudoperfect_945

end PPL086
