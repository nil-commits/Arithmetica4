import Prize.PPL086_Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# PPL 086 (Erdős Problem #470): Kravitz (1976), Sharp Melfi (2015), & Conditional Infinitude

This module proves:
1. `isDeficient_properDivisor_two_pow_pq`: for `k ≥ 1` and primes `2^(k+1) < p < q`, every proper divisor of `2^k * p * q` is deficient.
2. `subset_sum_two_pow_pq_decomp`: any subset sum `< p * q` of proper divisors of `2^k * p * q` has the form `c₀ + c₁ * p + c₂ * q` with `c₀, c₁, c₂ ≤ 2^(k+1) - 1`.
3. `isPrimitiveWeird_two_pow_pq_of_delta_lt_p`: Gap-0 primitive weirdness criterion.
4. `isPrimitiveWeird_kravitz`: **Kravitz's Theorem (1976)**.
5. `isPrimitiveWeird_mersenne_partner`: Mersenne-partner primitive weird family `2^k * (2^(k+2) - a) * (2^(k+2) - 1)`.
6. `isPrimitiveWeird_melfi_sharp`: **Sharp Melfi Theorem (2015)** with exact quadratic bound `a^2 + a * b < 2^(k+2) + 2 * b + 2`.
7. `infinite_primitiveWeird_of_sqrt_prime_gap`: **Conditional Infinitude of Primitive Weird Numbers** under `SqrtPrimeGap c` for ANY `0 < c` with `6 * c^2 < 1` (e.g. `c = 2/5 = 0.4`, sharpening Melfi's `c = 1/10` by `4×`).
8. Concrete certified primitive weird numbers (ZERO `native_decide`): `70`, `836`, `7192`, `4128448`.
-/

namespace PPL086

open Finset

/-! ## Section 1: Divisor & Subset-Sum Engine for `2^k * p * q` -/

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

/-- For `k ≥ 1` and primes `2^(k+1) < p < q`, every proper divisor of `2^k * p * q` is deficient. -/
theorem isDeficient_properDivisor_two_pow_pq {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_gt : 2 ^ (k + 1) < p) (hpq : p < q) :
    ∀ d ∈ (2 ^ k * p * q).properDivisors, IsDeficient d := by
  have h2ge4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos
  have hn_pos : 0 < 2 ^ k * p * q := by positivity
  -- First prove the 3 maximal proper divisors are deficient:
  have hdef_p : IsDeficient (2 ^ k * p) := by
    refine ⟨by positivity, ?_⟩
    rw [sigma_mul_of_coprime (coprime_two_pow_prime hp hp2), sigma_two_pow, sigma_prime hp]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge1 : 1 ≤ 2 ^ (k + 1) := by omega
    zify [hge1]; nlinarith
  have hdef_q : IsDeficient (2 ^ k * q) := by
    refine ⟨by positivity, ?_⟩
    rw [sigma_mul_of_coprime (coprime_two_pow_prime hq hq2), sigma_two_pow, sigma_prime hq]
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge1 : 1 ≤ 2 ^ (k + 1) := by omega
    zify [hge1]; nlinarith
  have hdef_2 : IsDeficient (2 ^ (k - 1) * p * q) := by
    refine ⟨by positivity, ?_⟩
    rw [sigma_two_pow_mul_prime_mul_prime hp hq hp2 hq2 hpq_ne]
    have hpow1 : 2 ^ (k - 1 + 1) = 2 ^ k := by congr 1; omega
    have hpow2_aux : 2 * 2 ^ (k - 1) = 2 ^ k := by
      rw [mul_comm, ← pow_succ, hpow1]
    have hpow2 : 2 * (2 ^ (k - 1) * p * q) = 2 ^ k * p * q := by
      calc 2 * (2 ^ (k - 1) * p * q) = (2 * 2 ^ (k - 1)) * p * q := by ring
        _ = 2 ^ k * p * q := by rw [hpow2_aux]
    rw [hpow1, hpow2]
    have hge1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
    have hp_2k : 2 * 2 ^ k < p := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hq_2k : 2 * 2 ^ k < q := by omega
    zify [hge1]
    nlinarith
  -- Now any proper divisor `d` divides one of these three maximal proper divisors
  intro d hd
  have hd_mem := Nat.mem_properDivisors.mp hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd_mem.1 hn_pos
  obtain ⟨m, hm⟩ := hd_mem.1
  have hm1 : 1 < m := by nlinarith [hd_mem.2]
  obtain ⟨r, hr_prime, hr_dvd_m⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hr_dvd_n : r ∣ 2 ^ k * p * q := dvd_trans hr_dvd_m ⟨d, hm.trans (mul_comm d m)⟩
  -- `r` must be `2`, `p`, or `q`
  have hr_cases : r = 2 ∨ r = p ∨ r = q := by
    rcases hr_prime.dvd_mul.mp hr_dvd_n with h2p | hq_dvd
    · rcases hr_prime.dvd_mul.mp h2p with h2_dvd | hp_dvd
      · left; exact (Nat.prime_dvd_prime_iff_eq hr_prime Nat.prime_two).mp (hr_prime.dvd_of_dvd_pow h2_dvd)
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hr_prime hp).mp hp_dvd
    · right; right; exact (Nat.prime_dvd_prime_iff_eq hr_prime hq).mp hq_dvd
  obtain ⟨m', hm'⟩ := hr_dvd_m
  rcases hr_cases with rfl | rfl | rfl
  · have hdvd : d ∣ 2 ^ (k - 1) * p * q := by
      refine ⟨m', ?_⟩
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [mul_comm, ← pow_succ]; congr 1; omega
      have hmul : 2 * (2 ^ (k - 1) * p * q) = 2 * (d * m') := by
        calc 2 * (2 ^ (k - 1) * p * q) = (2 * 2 ^ (k - 1)) * p * q := by ring
          _ = 2 ^ k * p * q := by rw [← h2k]
          _ = d * (2 * m') := by rw [← hm']; exact hm
          _ = 2 * (d * m') := by ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
    exact isDeficient_of_dvd_deficient hd0 hdvd hdef_2
  · have hdvd : d ∣ 2 ^ k * q := by
      refine ⟨m', ?_⟩
      have hmul : r * (2 ^ k * q) = r * (d * m') := by
        calc r * (2 ^ k * q) = 2 ^ k * r * q := by ring
          _ = d * (r * m') := by rw [← hm']; exact hm
          _ = r * (d * m') := by ring
      exact Nat.eq_of_mul_eq_mul_left hr_prime.pos hmul
    exact isDeficient_of_dvd_deficient hd0 hdvd hdef_q
  · have hdvd : d ∣ 2 ^ k * p := by
      refine ⟨m', ?_⟩
      have hmul : r * (2 ^ k * p) = r * (d * m') := by
        calc r * (2 ^ k * p) = 2 ^ k * p * r := by ring
          _ = d * (r * m') := by rw [← hm']; exact hm
          _ = r * (d * m') := by ring
      exact Nat.eq_of_mul_eq_mul_left hr_prime.pos hmul
    exact isDeficient_of_dvd_deficient hd0 hdvd hdef_p

/-- Any subset sum `< p * q` of divisors of `2^k * p * q` decomposes as `c₀ + c₁ * p + c₂ * q`
with `c₀, c₁, c₂ ≤ 2^(k+1) - 1`. -/
theorem subset_sum_two_pow_pq_decomp {k p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    {T : Finset ℕ} (hT : T ⊆ (2 ^ k * p * q).properDivisors) (hlt : ∑ d ∈ T, d < p * q) :
    ∃ c₀ c₁ c₂ : ℕ,
      c₀ ≤ 2 ^ (k + 1) - 1 ∧ c₁ ≤ 2 ^ (k + 1) - 1 ∧ c₂ ≤ 2 ^ (k + 1) - 1 ∧
      ∑ d ∈ T, d = c₀ + c₁ * p + c₂ * q := by
  have hcop_2p : Nat.Coprime (2 ^ k) p := coprime_two_pow_prime hp hp2
  have hcop_2q : Nat.Coprime (2 ^ k) q := coprime_two_pow_prime hq hq2
  have hcop_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  -- No element of `T` is divisible by both `p` and `q` (else its value ≥ p * q, contradicting `hlt`)
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos
  have hno_pq : ∀ d ∈ T, ¬ (p ∣ d ∧ q ∣ d) := by
    intro d hd ⟨hpd, hqd⟩
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp (hT hd)).1 (by positivity)
    have hpq_dvd : p * q ∣ d := hcop_pq.mul_dvd_of_dvd_of_dvd hpd hqd
    have hpq_le_d : p * q ≤ d := Nat.le_of_dvd hd_pos hpq_dvd
    have hd_le_sum : d ≤ ∑ x ∈ T, x := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hd
    omega
  -- Partition `T` into `T₀` (neither `p` nor `q` divides `d`), `T₁` (`p ∣ d`), `T₂` (`q ∣ d`)
  set T₀ := T.filter (fun d => ¬ p ∣ d ∧ ¬ q ∣ d)
  set T₁ := T.filter (fun d => p ∣ d)
  set T₂ := T.filter (fun d => q ∣ d)
  have hsum_split : ∑ d ∈ T, d = (∑ d ∈ T₀, d) + (∑ d ∈ T₁, d) + (∑ d ∈ T₂, d) := by
    have hdisj12 : Disjoint T₁ T₂ := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      exact hno_pq d (Finset.mem_filter.mp hd1).1 ⟨(Finset.mem_filter.mp hd1).2, (Finset.mem_filter.mp hd2).2⟩
    have hdisj012 : Disjoint T₀ (T₁ ∪ T₂) := by
      rw [Finset.disjoint_left]
      intro d hd0 hd12
      have h0 := (Finset.mem_filter.mp hd0).2
      rcases Finset.mem_union.mp hd12 with hd1 | hd2
      · exact h0.1 (Finset.mem_filter.mp hd1).2
      · exact h0.2 (Finset.mem_filter.mp hd2).2
    have hunion : T = T₀ ∪ (T₁ ∪ T₂) := by
      ext d
      simp only [T₀, T₁, T₂, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hd
        by_cases hpd : p ∣ d
        · right; left; exact ⟨hd, hpd⟩
        · by_cases hqd : q ∣ d
          · right; right; exact ⟨hd, hqd⟩
          · left; exact ⟨hd, hpd, hqd⟩
      · rintro (⟨hd, _⟩ | ⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
    conv_lhs => rw [hunion]
    rw [Finset.sum_union hdisj012, Finset.sum_union hdisj12, add_assoc]
  -- Bound `∑ d ∈ T₀, d ≤ 2^(k+1) - 1`
  have hT0_sub : T₀ ⊆ (2 ^ k).divisors := by
    intro d hd
    have ⟨hdT, hnp, hnq⟩ := Finset.mem_filter.mp hd
    have hd_dvd : d ∣ 2 ^ k * p * q := (Nat.mem_properDivisors.mp (hT hdT)).1
    have hd_2p : d ∣ 2 ^ k * p :=
      (Nat.Coprime.dvd_of_dvd_mul_right ((hq.coprime_iff_not_dvd.mpr hnq).symm) hd_dvd)
    have hd_2 : d ∣ 2 ^ k :=
      (Nat.Coprime.dvd_of_dvd_mul_right ((hp.coprime_iff_not_dvd.mpr hnp).symm) hd_2p)
    exact Nat.mem_divisors.mpr ⟨hd_2, by positivity⟩
  have hc0_le : ∑ d ∈ T₀, d ≤ 2 ^ (k + 1) - 1 := by
    calc ∑ d ∈ T₀, d ≤ ∑ d ∈ (2 ^ k).divisors, d := Finset.sum_le_sum_of_subset hT0_sub
      _ = sigma (2 ^ k) := rfl
      _ = 2 ^ (k + 1) - 1 := sigma_two_pow k
  -- Express `∑ d ∈ T₁, d = (∑ e ∈ T₁.image (· / p), e) * p` with sum ≤ `2^(k+1) - 1`
  set E₁ := T₁.image (fun d => d / p)
  have hT1_sum : ∑ d ∈ T₁, d = (∑ e ∈ E₁, e) * p := by
    rw [Finset.sum_mul, Finset.sum_image]
    · refine Finset.sum_congr rfl fun d hd => ?_
      exact (Nat.div_mul_cancel (Finset.mem_filter.mp hd).2).symm
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp only at hxy
      rw [← Nat.div_mul_cancel hx', ← Nat.div_mul_cancel hy', hxy]
  have hE1_sub : E₁ ⊆ (2 ^ k).divisors := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨d, hd1, rfl⟩
    have ⟨hdT, hpd⟩ := Finset.mem_filter.mp hd1
    have hnq : ¬ (q ∣ d) := fun hqd => hno_pq d hdT ⟨hpd, hqd⟩
    have hd_dvd : d ∣ 2 ^ k * p * q := (Nat.mem_properDivisors.mp (hT hdT)).1
    have hd_2p : d ∣ 2 ^ k * p :=
      (Nat.Coprime.dvd_of_dvd_mul_right ((hq.coprime_iff_not_dvd.mpr hnq).symm) hd_dvd)
    obtain ⟨e', he'⟩ := hpd
    have he_eq : d / p = e' := by rw [he', Nat.mul_div_cancel_left _ hp.pos]
    rw [he_eq]
    have he'_dvd : e' ∣ 2 ^ k := by
      rw [he', mul_comm (2 ^ k) p] at hd_2p
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp hd_2p
    exact Nat.mem_divisors.mpr ⟨he'_dvd, by positivity⟩
  have hc1_le : ∑ e ∈ E₁, e ≤ 2 ^ (k + 1) - 1 := by
    calc ∑ e ∈ E₁, e ≤ ∑ e ∈ (2 ^ k).divisors, e := Finset.sum_le_sum_of_subset hE1_sub
      _ = sigma (2 ^ k) := rfl
      _ = 2 ^ (k + 1) - 1 := sigma_two_pow k
  -- Express `∑ d ∈ T₂, d = (∑ e ∈ T₂.image (· / q), e) * q` with sum ≤ `2^(k+1) - 1`
  set E₂ := T₂.image (fun d => d / q)
  have hT2_sum : ∑ d ∈ T₂, d = (∑ e ∈ E₂, e) * q := by
    rw [Finset.sum_mul, Finset.sum_image]
    · refine Finset.sum_congr rfl fun d hd => ?_
      exact (Nat.div_mul_cancel (Finset.mem_filter.mp hd).2).symm
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      dsimp only at hxy
      rw [← Nat.div_mul_cancel hx', ← Nat.div_mul_cancel hy', hxy]
  have hE2_sub : E₂ ⊆ (2 ^ k).divisors := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨d, hd2, rfl⟩
    have ⟨hdT, hqd⟩ := Finset.mem_filter.mp hd2
    have hnp : ¬ (p ∣ d) := fun hpd => hno_pq d hdT ⟨hpd, hqd⟩
    have hd_dvd : d ∣ 2 ^ k * p * q := (Nat.mem_properDivisors.mp (hT hdT)).1
    have hd_2q : d ∣ 2 ^ k * q := by
      have hd_dvd' : d ∣ (2 ^ k * q) * p := by simpa [mul_assoc, mul_comm, mul_left_comm] using hd_dvd
      exact Nat.Coprime.dvd_of_dvd_mul_right ((hp.coprime_iff_not_dvd.mpr hnp).symm) hd_dvd'
    obtain ⟨e', he'⟩ := hqd
    have he_eq : d / q = e' := by rw [he', Nat.mul_div_cancel_left _ hq.pos]
    rw [he_eq]
    have he'_dvd : e' ∣ 2 ^ k := by
      rw [he', mul_comm (2 ^ k) q] at hd_2q
      exact (mul_dvd_mul_iff_left hq.ne_zero).mp hd_2q
    exact Nat.mem_divisors.mpr ⟨he'_dvd, by positivity⟩
  have hc2_le : ∑ e ∈ E₂, e ≤ 2 ^ (k + 1) - 1 := by
    calc ∑ e ∈ E₂, e ≤ ∑ e ∈ (2 ^ k).divisors, e := Finset.sum_le_sum_of_subset hE2_sub
      _ = sigma (2 ^ k) := rfl
      _ = 2 ^ (k + 1) - 1 := sigma_two_pow k
  exact ⟨∑ d ∈ T₀, d, ∑ e ∈ E₁, e, ∑ e ∈ E₂, e, hc0_le, hc1_le, hc2_le, by
    rw [hsum_split, hT1_sum, hT2_sum]⟩

/-! ## Section 2: Gap-0 Criterion, Kravitz's Theorem (1976), & Concrete Primitive Weird Numbers -/

/-- **Gap-0 Primitive Weirdness Criterion:**
If `k ≥ 1`, `p < q` are primes `> 2^(k+1)`, and the abundance `δ = (2^(k+1) - 1)(p + q + 1) - p q`
satisfies `2^(k+1) ≤ δ < p`, then `2^k * p * q` is **primitive weird**. -/
theorem isPrimitiveWeird_two_pow_pq_of_delta_lt_p {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_gt : 2 ^ (k + 1) < p) (hpq : p < q)
    (hlo : p * q + 2 ^ (k + 1) ≤ (2 ^ (k + 1) - 1) * (p + q + 1))
    (hhi : (2 ^ (k + 1) - 1) * (p + q + 1) < p * q + p) :
    IsPrimitiveWeird (2 ^ k * p * q) := by
  have h2ge4 : 4 ≤ 2 ^ (k + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos
  have hsig := sigma_two_pow_mul_prime_mul_prime (k := k) hp hq hp2 hq2 hpq_ne
  have h2n : 2 * (2 ^ k * p * q) = 2 ^ (k + 1) * p * q := by rw [pow_succ]; ring
  have hsig_expand : sigma (2 ^ k * p * q) = 2 ^ (k + 1) * p * q + ((2 ^ (k + 1) - 1) * (p + q + 1) - p * q) := by
    rw [hsig]
    have hge1 : 1 ≤ 2 ^ (k + 1) := by omega
    have hle_pq : p * q ≤ (2 ^ (k + 1) - 1) * (p + q + 1) := by omega
    zify [hge1, hle_pq]
    ring
  have hab : IsAbundant (2 ^ k * p * q) := by
    refine ⟨by positivity, ?_⟩
    rw [hsig_expand, h2n]
    omega
  rw [isPrimitiveWeird_iff_properDivisors_deficient]
  refine ⟨⟨hab, ?_⟩, isDeficient_properDivisor_two_pow_pq hk hp hq hp_gt hpq⟩
  rw [isPseudoperfect_iff_abundance_subset_sum hab]
  rintro ⟨T, hT, hsum⟩
  have hδ_eq : sigma (2 ^ k * p * q) - 2 * (2 ^ k * p * q) =
      (2 ^ (k + 1) - 1) * (p + q + 1) - p * q := by
    rw [hsig_expand, h2n]; omega
  rw [hδ_eq] at hsum
  have hsum_lt_p : ∑ d ∈ T, d < p := by omega
  have hsum_lt_pq : ∑ d ∈ T, d < p * q := by
    have : p ≤ p * q := Nat.le_mul_of_pos_right p hq_pos
    omega
  obtain ⟨c₀, c₁, c₂, hc0, _, _, hdecomp⟩ :=
    subset_sum_two_pow_pq_decomp hp hq hp2 hq2 hpq_ne hT hsum_lt_pq
  have hc1_zero : c₁ = 0 := by
    by_contra h
    have : p ≤ c₁ * p := Nat.le_mul_of_pos_left p (Nat.pos_of_ne_zero h)
    omega
  have hc2_zero : c₂ = 0 := by
    by_contra h
    have : q ≤ c₂ * q := Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero h)
    omega
  rw [hc1_zero, hc2_zero] at hdecomp
  simp only [zero_mul, add_zero] at hdecomp
  omega

/-- **Kravitz's Theorem (1976):**
For `k ≥ 1` and distinct primes `p, q > 2^(k+1)` satisfying
`q * (p - (2^(k+1) - 1)) = (2^(k+1) - 1) * p - 1` (equivalently `(2^(k+1) - 1)*(p + q + 1) = p*q + 2^(k+1)`),
`2^k * p * q` is **primitive weird**. -/
theorem isPrimitiveWeird_kravitz {k p q : ℕ} (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hp_gt : 2 ^ (k + 1) < p) (hq_gt : 2 ^ (k + 1) < q)
    (hpq_ne : p ≠ q)
    (hkrav : (2 ^ (k + 1) - 1) * (p + q + 1) = p * q + 2 ^ (k + 1)) :
    IsPrimitiveWeird (2 ^ k * p * q) := by
  rcases lt_or_gt_of_ne hpq_ne with hpq | hqp
  · exact isPrimitiveWeird_two_pow_pq_of_delta_lt_p hk hp hq hp_gt hpq (by omega) (by omega)
  · have hcomm : 2 ^ k * p * q = 2 ^ k * q * p := by ring
    rw [hcomm]
    exact isPrimitiveWeird_two_pow_pq_of_delta_lt_p hk hq hp hq_gt hqp
      (by linarith [hkrav]) (by linarith [hkrav, hq_gt])

/-- Concrete Certified Primitive Weird Number #1: `70 = 2^1 * 5 * 7` (the smallest weird number!). -/
theorem isPrimitiveWeird_70 : IsPrimitiveWeird 70 := by
  have h := isPrimitiveWeird_kravitz (k := 1) (p := 5) (q := 7)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Concrete Certified Primitive Weird Number #2: `836 = 2^2 * 11 * 19`. -/
theorem isPrimitiveWeird_836 : IsPrimitiveWeird 836 := by
  have h := isPrimitiveWeird_kravitz (k := 2) (p := 11) (q := 19)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Concrete Certified Primitive Weird Number #3: `7192 = 2^3 * 29 * 31`. -/
theorem isPrimitiveWeird_7192 : IsPrimitiveWeird 7192 := by
  have h := isPrimitiveWeird_kravitz (k := 3) (p := 29) (q := 31)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-! ## Section 3: Mersenne-Partner Family & Sharp Melfi Theorem (2015) -/

/-- **Mersenne-Partner Primitive Weird Family:**
If `k ≥ 2`, `q = 2^(k+2) - 1` is a Mersenne prime, and `p = 2^(k+2) - a` is prime with `3 ≤ a` odd
and `a * (a + 1) < 2^(k+2)`, then `2^k * p * q` is **primitive weird**. -/
theorem isPrimitiveWeird_mersenne_partner {k a : ℕ} (hk : 2 ≤ k)
    (ha3 : 3 ≤ a) (ha_quad : a * (a + 1) < 2 ^ (k + 2))
    (hp : (2 ^ (k + 2) - a).Prime) (hq : (2 ^ (k + 2) - 1).Prime) :
    IsPrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) - 1)) := by
  set R := 2 ^ (k + 1) with hR_def
  have h2R : 2 ^ (k + 2) = 2 * R := by rw [hR_def, pow_succ]; ring
  have hR_ge8 : 8 ≤ R := by
    rw [hR_def]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha_lt_R : a < R := by nlinarith
  set p := 2 * R - a with hp_def
  set q := 2 * R - 1 with hq_def
  have hp' : p.Prime := by simpa [hp_def, h2R] using hp
  have hq' : q.Prime := by simpa [hq_def, h2R] using hq
  have hp_gt_R : R < p := by omega
  have hpq : p < q := by omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  -- `p` is odd, `2 * R` is even, so `a` is odd
  have hp_odd : Odd p := hp'.odd_of_ne_two hp2
  have ha_odd : a % 2 = 1 := by
    obtain ⟨t, ht⟩ := hp_odd
    omega
  set s := (a - 3) / 2 with hs_def
  have h2s : 2 * s = a - 3 := by omega
  -- Compute `σ(2^k * p * q)` and `δ = 2 * R * s + R`
  have hsig := sigma_two_pow_mul_prime_mul_prime (k := k) hp' hq' hp2 hq2 hpq_ne
  have h2n : 2 * (2 ^ k * p * q) = R * p * q := by rw [hR_def, pow_succ]; ring
  have hsig_eq : sigma (2 ^ k * p * q) = R * p * q + (2 * R * s + R) := by
    rw [hsig, ← hR_def]
    have hge1 : 1 ≤ R := by omega
    have h2R_a : a ≤ 2 * R := by omega
    zify [hge1, h2R_a]
    have h2s_z : (2 : ℤ) * (s : ℤ) = (a : ℤ) - 3 := by omega
    have hp_z : (p : ℤ) = 2 * (R : ℤ) - (a : ℤ) := by rw [hp_def]; omega
    have hq_z : (q : ℤ) = 2 * (R : ℤ) - 1 := by rw [hq_def]; omega
    rw [hp_z, hq_z]
    linear_combination -(R : ℤ) * h2s_z
  have hab : IsAbundant (2 ^ k * p * q) := by
    have hp_pos : 0 < p := hp'.pos
    have hq_pos : 0 < q := hq'.pos
    refine ⟨by positivity, ?_⟩
    rw [hsig_eq, h2n]; omega
  rw [h2R, ← hp_def, ← hq_def, isPrimitiveWeird_iff_properDivisors_deficient]
  refine ⟨⟨hab, ?_⟩, isDeficient_properDivisor_two_pow_pq (by omega) hp' hq' hp_gt_R hpq⟩
  rw [isPseudoperfect_iff_abundance_subset_sum hab]
  rintro ⟨T, hT, hsum⟩
  have hδ : sigma (2 ^ k * p * q) - 2 * (2 ^ k * p * q) = 2 * R * s + R := by
    rw [hsig_eq, h2n]; omega
  rw [hδ] at hsum
  have hδ_lt_pq : 2 * R * s + R < p * q := by
    have h1 : 2 * s + 1 < R := by omega
    have h2 : R * R ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (2 * s + 1) * R < R * R := Nat.mul_lt_mul_of_pos_right h1 (by omega)
    have h4 : 2 * R * s + R = (2 * s + 1) * R := by ring
    omega
  obtain ⟨c₀, c₁, c₂, hc0, _, _, hdecomp⟩ :=
    subset_sum_two_pow_pq_decomp hp' hq' hp2 hq2 hpq_ne hT (hsum ▸ hδ_lt_pq)
  rw [hsum] at hdecomp
  set m := c₁ + c₂
  by_cases hm : m ≤ s
  · -- Case 1: `m ≤ s` ⇒ `c₀ + c₁ p + c₂ q ≤ (R - 1) + m * (2R) ≤ 2Rs + R - 1 < 2Rs + R`
    have hle1 : c₁ * p ≤ c₁ * (2 * R) := Nat.mul_le_mul_left c₁ (by omega)
    have hle2 : c₂ * q ≤ c₂ * (2 * R) := Nat.mul_le_mul_left c₂ (by omega)
    have hle3 : m * (2 * R) ≤ s * (2 * R) := Nat.mul_le_mul_right (2 * R) hm
    have hsum_le : c₁ * p + c₂ * q ≤ m * (2 * R) := by
      have : c₁ * (2 * R) + c₂ * (2 * R) = m * (2 * R) := by dsimp only [m]; ring
      omega
    have hs_eq : s * (2 * R) = 2 * R * s := by ring
    omega
  · -- Case 2: `s + 1 ≤ m` ⇒ `c₀ + c₁ p + c₂ q ≥ m * p ≥ (s + 1) * (2R - a) > 2Rs + R`
    have hm1 : s + 1 ≤ m := by omega
    have hge1 : m * p ≤ c₁ * p + c₂ * q := by
      have : c₂ * p ≤ c₂ * q := Nat.mul_le_mul_left c₂ (le_of_lt hpq)
      have : m * p = c₁ * p + c₂ * p := by dsimp only [m]; ring
      omega
    have hge2 : (s + 1) * p ≤ m * p := Nat.mul_le_mul_right p hm1
    have hkey : 2 * R * s + R < (s + 1) * p := by
      have h2sa : 2 * ((s + 1) * a) < 2 * R := by
        have h2s1 : 2 * (s + 1) = a - 1 := by omega
        have hlt1 : (a - 1) * a < a * (a + 1) := by
          have : a - 1 < a + 1 := by omega
          calc (a - 1) * a = a * (a - 1) := mul_comm _ _
            _ < a * (a + 1) := Nat.mul_lt_mul_of_pos_left this (by omega)
        calc 2 * ((s + 1) * a) = (2 * (s + 1)) * a := by ring
          _ = (a - 1) * a := by rw [h2s1]
          _ < a * (a + 1) := hlt1
          _ < 2 * R := by omega
      have hsa_lt_R : (s + 1) * a < R := by omega
      have hp_eq : (s + 1) * p + (s + 1) * a = (s + 1) * (2 * R) := by
        rw [← mul_add, hp_def, Nat.sub_add_cancel (by omega)]
      have h2Rs : (s + 1) * (2 * R) = 2 * R * s + 2 * R := by ring
      omega
    omega

/-- **Sharp Melfi Theorem (2015, sharpened quadratic bound):**
For `k ≥ 2`, let `R = 2^(k+1)` (so `2^(k+2) = 2*R`). If `p = 2^(k+2) - a` and `q = 2^(k+2) + b`
are primes with `0 < b`, `b + 3 < a`, `a < 2^(k+1)`, and
`a^2 + a * b < 2^(k+2) + 2 * b + 2`,
then `2^k * p * q` is **primitive weird**! -/
theorem isPrimitiveWeird_melfi_sharp {k a b : ℕ} (hk : 2 ≤ k)
    (hb : 0 < b) (hab_gap : b + 3 < a) (ha_lt : a < 2 ^ (k + 1))
    (hquad : a ^ 2 + a * b < 2 ^ (k + 2) + 2 * b + 2)
    (hp : (2 ^ (k + 2) - a).Prime) (hq : (2 ^ (k + 2) + b).Prime) :
    IsPrimitiveWeird (2 ^ k * (2 ^ (k + 2) - a) * (2 ^ (k + 2) + b)) := by
  set R := 2 ^ (k + 1) with hR_def
  have h2R : 2 ^ (k + 2) = 2 * R := by rw [hR_def, pow_succ]; ring
  have hR_ge8 : 8 ≤ R := by
    rw [hR_def]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set p := 2 * R - a with hp_def
  set q := 2 * R + b with hq_def
  have hp' : p.Prime := by simpa [hp_def, h2R] using hp
  have hq' : q.Prime := by simpa [hq_def, h2R] using hq
  have hp_gt_R : R < p := by omega
  have hpq : p < q := by omega
  have hp2 : p ≠ 2 := by omega
  have hq2 : q ≠ 2 := by omega
  have hpq_ne : p ≠ q := ne_of_lt hpq
  -- `p` and `q` are odd, `2 * R` is even ⇒ `a` and `b` are odd ⇒ `a - b - 4` is even!
  have ha_odd : a % 2 = 1 := by
    obtain ⟨t, ht⟩ := hp'.odd_of_ne_two hp2; omega
  have hb_odd : b % 2 = 1 := by
    obtain ⟨t, ht⟩ := hq'.odd_of_ne_two hq2; omega
  set s := (a - b - 4) / 2 with hs_def
  have h2s : 2 * s = a - b - 4 := by omega
  -- Exact abundance identity: `σ(2^k p q) = R p q + (2 R s + R + 2 s + 3 + a b)`
  have hsig := sigma_two_pow_mul_prime_mul_prime (k := k) hp' hq' hp2 hq2 hpq_ne
  have h2n : 2 * (2 ^ k * p * q) = R * p * q := by rw [hR_def, pow_succ]; ring
  set δ := 2 * R * s + R + 2 * s + 3 + a * b with hδ_def
  have hsig_eq : sigma (2 ^ k * p * q) = R * p * q + δ := by
    rw [hsig, ← hR_def, hδ_def]
    have hge1 : 1 ≤ R := by omega
    have h2R_a : a ≤ 2 * R := by omega
    zify [hge1, h2R_a]
    have h2s_z : (2 : ℤ) * (s : ℤ) = (a : ℤ) - (b : ℤ) - 4 := by omega
    have hp_z : (p : ℤ) = 2 * (R : ℤ) - (a : ℤ) := by rw [hp_def]; omega
    have hq_z : (q : ℤ) = 2 * (R : ℤ) + (b : ℤ) := by rw [hq_def]; omega
    rw [hp_z, hq_z]
    linear_combination -((R : ℤ) + 1) * h2s_z
  have hab_n : IsAbundant (2 ^ k * p * q) := by
    have hp_pos : 0 < p := hp'.pos
    have hq_pos : 0 < q := hq'.pos
    refine ⟨by positivity, ?_⟩
    rw [hsig_eq, h2n]; omega
  rw [h2R, ← hp_def, ← hq_def, isPrimitiveWeird_iff_properDivisors_deficient]
  refine ⟨⟨hab_n, ?_⟩, isDeficient_properDivisor_two_pow_pq (by omega) hp' hq' hp_gt_R hpq⟩
  rw [isPseudoperfect_iff_abundance_subset_sum hab_n]
  rintro ⟨T, hT, hsum⟩
  have hδ_eq : sigma (2 ^ k * p * q) - 2 * (2 ^ k * p * q) = δ := by
    rw [hsig_eq, h2n]; omega
  rw [hδ_eq] at hsum
  -- Key quadratic inequality: `(s + 1) * a + 2 * s + 3 + a * b < R`
  have hkey_quad : (s + 1) * a + 2 * s + 3 + a * b < R := by
    have h2mul : 2 * ((s + 1) * a + 2 * s + 3 + a * b) + 2 * b + 2 = a ^ 2 + a * b := by
      have h2s_eq : 2 * s + b + 4 = a := by omega
      have h2s1_eq : 2 * (s + 1) + b + 2 = a := by omega
      calc 2 * ((s + 1) * a + 2 * s + 3 + a * b) + 2 * b + 2
          = (2 * (s + 1)) * a + 2 * (2 * s + b + 4) + 2 * a * b := by ring
        _ = (2 * (s + 1)) * a + 2 * a + 2 * a * b := by rw [h2s_eq]
        _ = (2 * (s + 1) + b + 2) * a + a * b := by ring
        _ = a * a + a * b := by rw [h2s1_eq]
        _ = a ^ 2 + a * b := by rw [sq]
    omega
  -- Check `δ < p * q`
  have hδ_lt_pq : δ < p * q := by
    have h1 : R * (2 * R) ≤ p * q := Nat.mul_le_mul (by omega) (by omega)
    have h2 : 2 * s + 3 + a * b < R := by omega
    have h4 : δ < 2 * R * (s + 1) := by
      have : 2 * R * (s + 1) = 2 * R * s + 2 * R := by ring
      omega
    have hs1_lt_R : s + 1 < R := by omega
    have h5 : 2 * R * (s + 1) < R * (2 * R) := by
      calc 2 * R * (s + 1) < 2 * R * R := Nat.mul_lt_mul_of_pos_left hs1_lt_R (by omega)
        _ = R * (2 * R) := by ring
    omega
  obtain ⟨c₀, c₁, c₂, hc0, _, _, hdecomp⟩ :=
    subset_sum_two_pow_pq_decomp hp' hq' hp2 hq2 hpq_ne hT (hsum ▸ hδ_lt_pq)
  rw [hsum] at hdecomp
  set m := c₁ + c₂
  by_cases hm : m ≤ s
  · -- Case 1: `m ≤ s` ⇒ `c₀ + c₁ p + c₂ q ≤ (R - 1) + 2Rm + m b ≤ (R - 1) + 2Rs + s b < δ`!
    have hs_lt_a : s < a := by omega
    have hsb_lt_ab : s * b < a * b := Nat.mul_lt_mul_of_pos_right hs_lt_a hb
    have hup : c₀ + c₁ * p + c₂ * q ≤ (R - 1) + 2 * R * m + m * b := by
      have h1 : c₁ * p ≤ c₁ * (2 * R) := Nat.mul_le_mul_left c₁ (by omega)
      have h2 : c₂ * q = c₂ * (2 * R) + c₂ * b := by rw [hq_def]; ring
      have h3 : c₂ * b ≤ m * b := Nat.mul_le_mul_right b (by omega)
      have h4 : c₁ * (2 * R) + c₂ * (2 * R) = 2 * R * m := by dsimp only [m]; ring
      omega
    have hup2 : (R - 1) + 2 * R * m + m * b ≤ (R - 1) + 2 * R * s + s * b := by
      have h1 : 2 * R * m ≤ 2 * R * s := Nat.mul_le_mul_left (2 * R) hm
      have h2 : m * b ≤ s * b := Nat.mul_le_mul_right b hm
      omega
    omega
  · -- Case 2: `s + 1 ≤ m` ⇒ `c₀ + c₁ p + c₂ q ≥ m * p ≥ (s + 1) * (2R - a) > δ`!
    have hm1 : s + 1 ≤ m := by omega
    have hge1 : m * p ≤ c₁ * p + c₂ * q := by
      have : c₂ * p ≤ c₂ * q := Nat.mul_le_mul_left c₂ (le_of_lt hpq)
      have : m * p = c₁ * p + c₂ * p := by dsimp only [m]; ring
      omega
    have hge2 : (s + 1) * p ≤ m * p := Nat.mul_le_mul_right p hm1
    have hgt : δ < (s + 1) * p := by
      have hp_eq : (s + 1) * p + (s + 1) * a = (s + 1) * (2 * R) := by
        rw [← mul_add, hp_def, Nat.sub_add_cancel (by omega)]
      have h2Rs : (s + 1) * (2 * R) = 2 * R * s + 2 * R := by ring
      omega
    omega

/-- Concrete Certified Primitive Weird Number #4 (Melfi family): `4128448 = 2^6 * 251 * 257`. -/
theorem isPrimitiveWeird_4128448 : IsPrimitiveWeird 4128448 := by
  have h := isPrimitiveWeird_melfi_sharp (k := 6) (a := 5) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

/-! ## Section 4: Conditional Infinitude of Primitive Weird Numbers under Sharp Prime Gaps -/

/-- Short-interval square-root prime gap hypothesis with constant `c > 0`:
for all sufficiently large `x`, there is a prime in `(x, x + c * √x)`. -/
def SqrtPrimeGap (c : ℝ) : Prop :=
  ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < x + c * Real.sqrt x

/-- **Conditional Infinitude of Primitive Weird Numbers (Sharpened Melfi 2015):**
For ANY `0 < c` with `6 * c^2 < 1` (for example `c = 2/5 = 0.4`, sharpening Melfi's `c = 1/10` by `4×`!),
the prime-gap hypothesis `SqrtPrimeGap c` implies `{n : ℕ | IsPrimitiveWeird n}.Infinite`. -/
theorem infinite_primitiveWeird_of_sqrt_prime_gap {c : ℝ} (hc : 0 < c) (hc6 : 6 * c ^ 2 < 1)
    (hgap : SqrtPrimeGap c) :
    {n : ℕ | IsPrimitiveWeird n}.Infinite := by
  obtain ⟨X₀, hX₀⟩ := hgap
  rw [Set.infinite_iff_exists_gt]
  intro N
  -- Choose `ε = 1 - 6 * c^2 > 0`, pick `k` sufficiently large so all asymptotic inequalities hold
  set ε : ℝ := 1 - 6 * c ^ 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  -- Choose `k : ℕ` large enough that `2^(k+2)` dominates `2 * max X₀ 100`, `N`, and `((20*c + 20) / ε)^2`
  set B0 : ℝ := ((20 * c + 20) / ε) ^ 2
  set T0 : ℝ := max (max (max (2 * max X₀ 100) (N : ℝ)) B0) 400
  set S : ℝ := T0 + 100
  obtain ⟨k, hk_gt⟩ : ∃ k : ℕ, S < (2 ^ (k + 2) : ℝ) := by
    have hpow : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    rw [Filter.tendsto_atTop_atTop] at hpow
    obtain ⟨k0, hk0⟩ := hpow (S + 1)
    refine ⟨k0, ?_⟩
    have hle : (2 : ℝ) ^ k0 ≤ (2 : ℝ) ^ (k0 + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1 := hk0 k0 le_rfl
    linarith
  have h400_le_T0 : (400 : ℝ) ≤ T0 := le_max_right _ _
  have hB0_le_T0 : B0 ≤ T0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN_le_T0 : (N : ℝ) ≤ T0 :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have h2X0_le_T0 : 2 * max X₀ 100 ≤ T0 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have hk1 : k ≤ 1 := by omega
    have hpow_le : (2 ^ (k + 2) : ℝ) ≤ 8 := by
      have : 2 ^ (k + 2) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact_mod_cast this
    linarith
  set M : ℕ := 2 ^ (k + 2) with hM_def
  have hM_real : (M : ℝ) = (2 ^ (k + 2) : ℝ) := by exact_mod_cast rfl
  have hM_gt_S : S < (M : ℝ) := by rwa [hM_real]
  have hM_ge_2X0 : 2 * max X₀ 100 ≤ (M : ℝ) := by linarith
  have hM_ge_X0 : X₀ ≤ (M : ℝ) := by
    have : X₀ ≤ max X₀ 100 := le_max_left _ _
    have : (100 : ℝ) ≤ max X₀ 100 := le_max_right _ _
    linarith
  have hM_ge_400 : (400 : ℝ) ≤ (M : ℝ) := by linarith
  have hM_gt_N : (N : ℝ) < (M : ℝ) := by linarith
  have hsqrtM_pos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsqrtM_sq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt (by linarith)
  have hsqrtM_ge20 : (20 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 20)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsqrtM_ge : (20 * c + 20) / ε ≤ Real.sqrt (M : ℝ) := by
    have h1 : ((20 * c + 20) / ε) ^ 2 ≤ (M : ℝ) := by linarith [hB0_le_T0]
    have hnonneg : 0 ≤ (20 * c + 20) / ε := by positivity
    rw [← Real.sqrt_sq hnonneg]
    exact Real.sqrt_le_sqrt h1
  have hc_lt_half : c < 1 / 2 := by
    by_contra hge
    push Not at hge
    have : (1 / 2 : ℝ) ^ 2 ≤ c ^ 2 := by
      rw [sq, sq]; exact mul_le_mul hge hge (by norm_num) (by linarith)
    linarith
  have h20sqrt_le_M : 20 * Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    calc 20 * Real.sqrt (M : ℝ) ≤ Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) :=
          mul_le_mul_of_nonneg_right hsqrtM_ge20 hsqrtM_pos.le
      _ = (M : ℝ) := hsqrtM_sq
  have hc_sqrt_lt : c * Real.sqrt (M : ℝ) < (1 / 2) * Real.sqrt (M : ℝ) :=
    mul_lt_mul_of_pos_right hc_lt_half hsqrtM_pos
  -- Step 1: find prime `q = M + b` in `(M, M + c * √M)`
  obtain ⟨q, hq_prime, hM_lt_q, hq_lt⟩ := hX₀ (M : ℝ) hM_ge_X0
  have hM_lt_q_nat : M < q := by exact_mod_cast hM_lt_q
  set b : ℕ := q - M with hb_def
  have hb_pos : 0 < b := by omega
  have hq_eq : q = M + b := by omega
  have hb_lt : (b : ℝ) < c * Real.sqrt (M : ℝ) := by
    have hcast : (q : ℝ) = (M : ℝ) + (b : ℝ) := by exact_mod_cast hq_eq
    linarith
  -- Step 2: find prime `p = M - a` in `(x₁, M - b - 3)` where `x₁ = M - b - 3 - c * √M`
  set x₁ : ℝ := (M : ℝ) - (b : ℝ) - 3 - c * Real.sqrt (M : ℝ) with hx₁_def
  have hx₁_gt_half : (M : ℝ) / 2 < x₁ := by
    linarith [h20sqrt_le_M, hsqrtM_ge20, hb_lt, hc_sqrt_lt]
  have hx₁_ge_X0 : X₀ ≤ x₁ := by
    have : X₀ ≤ max X₀ 100 := le_max_left _ _
    linarith
  have hx₁_lt_M : x₁ < (M : ℝ) := by
    have hb_pos_r : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have hcs_pos : 0 < c * Real.sqrt (M : ℝ) := mul_pos hc hsqrtM_pos
    linarith
  obtain ⟨p, hp_prime, hx₁_lt_p, hp_lt⟩ := hX₀ x₁ hx₁_ge_X0
  have hsqrt_x1_le : Real.sqrt x₁ ≤ Real.sqrt (M : ℝ) := Real.sqrt_le_sqrt (le_of_lt hx₁_lt_M)
  have hp_lt_Mb3 : (p : ℝ) < (M : ℝ) - (b : ℝ) - 3 := by
    have : c * Real.sqrt x₁ ≤ c * Real.sqrt (M : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt_x1_le hc.le
    linarith
  have hp_lt_M_nat : p + b + 3 < M := by
    have : ((p + b + 3 : ℕ) : ℝ) < (M : ℝ) := by push_cast; linarith
    exact_mod_cast this
  set a : ℕ := M - p with ha_def
  have hab_gap : b + 3 < a := by omega
  have hp_eq : p = M - a := by omega
  have ha_lt_real : (a : ℝ) < 2 * c * Real.sqrt (M : ℝ) + 3 := by
    have hcast : (p : ℝ) + (a : ℝ) = (M : ℝ) := by exact_mod_cast (show p + a = M by omega)
    linarith
  -- Step 3: verify `a < 2^(k+1)` (i.e., `2 * a < M`)
  have ha_lt_R : a < 2 ^ (k + 1) := by
    have h2a_lt_M : (2 : ℝ) * (a : ℝ) < (M : ℝ) := by
      linarith [h20sqrt_le_M, hsqrtM_ge20, ha_lt_real, hc_sqrt_lt]
    have h2a_nat : 2 * a < M := by exact_mod_cast (show ((2 * a : ℕ) : ℝ) < (M : ℝ) by push_cast; linarith)
    have hM2 : M = 2 * 2 ^ (k + 1) := by rw [hM_def, pow_succ]; ring
    omega
  -- Step 4: verify the sharp quadratic bound `a^2 + a * b < M + 2 * b + 2`
  have hquad : a ^ 2 + a * b < M + 2 * b + 2 := by
    have hquad_r : (a : ℝ) ^ 2 + (a : ℝ) * (b : ℝ) < (M : ℝ) := by
      have ha_nonneg : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
      have hb_nonneg : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      have hcs_pos : 0 < c * Real.sqrt (M : ℝ) := mul_pos hc hsqrtM_pos
      have h1 : (a : ℝ) ^ 2 < (2 * c * Real.sqrt (M : ℝ) + 3) ^ 2 := by
        rw [sq, sq]
        exact mul_lt_mul'' ha_lt_real ha_lt_real ha_nonneg ha_nonneg
      have h2 : (a : ℝ) * (b : ℝ) < (2 * c * Real.sqrt (M : ℝ) + 3) * (c * Real.sqrt (M : ℝ)) :=
        mul_lt_mul'' ha_lt_real hb_lt ha_nonneg hb_nonneg
      have hexp : (2 * c * Real.sqrt (M : ℝ) + 3) ^ 2 +
          (2 * c * Real.sqrt (M : ℝ) + 3) * (c * Real.sqrt (M : ℝ)) =
          6 * c ^ 2 * (M : ℝ) + 15 * c * Real.sqrt (M : ℝ) + 9 := by
        linear_combination (6 * c ^ 2) * hsqrtM_sq
      have hε_mul : 20 * c + 20 ≤ ε * Real.sqrt (M : ℝ) := by
        have := (div_le_iff₀ hε_pos).mp hsqrtM_ge
        linarith
      have hε_M : (15 * c + 20) * Real.sqrt (M : ℝ) ≤ ε * (M : ℝ) := by
        calc (15 * c + 20) * Real.sqrt (M : ℝ)
            ≤ (20 * c + 20) * Real.sqrt (M : ℝ) :=
              mul_le_mul_of_nonneg_right (by linarith) hsqrtM_pos.le
          _ ≤ (ε * Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ) :=
              mul_le_mul_of_nonneg_right hε_mul hsqrtM_pos.le
          _ = ε * (M : ℝ) := by rw [mul_assoc, hsqrtM_sq]
      have hεM_eq : 6 * c ^ 2 * (M : ℝ) + ε * (M : ℝ) = (M : ℝ) := by
        rw [hε_def]; ring
      have h15_expand : (15 * c + 20) * Real.sqrt (M : ℝ) =
          15 * c * Real.sqrt (M : ℝ) + 20 * Real.sqrt (M : ℝ) := by ring
      linarith [hsqrtM_ge20]
    have hquad_nat : a ^ 2 + a * b < M := by
      exact_mod_cast (show ((a ^ 2 + a * b : ℕ) : ℝ) < (M : ℝ) by push_cast; linarith)
    omega
  -- Step 5: apply `isPrimitiveWeird_melfi_sharp`!
  have hpw : IsPrimitiveWeird (2 ^ k * (M - a) * (M + b)) :=
    isPrimitiveWeird_melfi_sharp hk_ge2 hb_pos hab_gap ha_lt_R hquad
      (by rwa [← hp_eq]) (by rwa [← hq_eq])
  refine ⟨2 ^ k * (M - a) * (M + b), hpw, ?_⟩
  have hN_lt_M : N < M := by exact_mod_cast hM_gt_N
  have hp_pos : 1 ≤ M - a := hp_eq ▸ hp_prime.one_le
  have h2k_pos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h1 : 1 * (M + b) ≤ (2 ^ k * (M - a)) * (M + b) :=
    Nat.mul_le_mul_right (M + b) (Nat.mul_pos h2k_pos hp_pos)
  omega

/-- Concrete Melfi-type corollary for `c = 2/5 = 0.4` (sharpening Melfi's `1/10` by `4×`). -/
theorem infinite_primitiveWeird_of_two_fifths_sqrt_prime_gap
    (hgap : SqrtPrimeGap (2 / 5)) :
    {n : ℕ | IsPrimitiveWeird n}.Infinite :=
  infinite_primitiveWeird_of_sqrt_prime_gap (by norm_num) (by norm_num) hgap

end PPL086
