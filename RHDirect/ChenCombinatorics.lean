import RHDirect.ChenDefs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# RHDirect.ChenCombinatorics

The exact combinatorial heart of **Chen's Theorem (1973)** at `z = N^{1/8}`, `y = N^{1/3}`:
1. Every `a ∈ chenGoldbachSet N` with `1 < a`, surviving `P(N^{1/8})`, and not divisible by `q²`
   for any prime `q ≥ N^{1/8}` satisfies:
   `1_{IsP2 a} ≥ 1 - (1/2) * #{q ∈ chenMidPrimes N : q ∣ a} - (1/2) * 1_{a ∈ chenMProd N}`.
2. The non-squarefree exception count (`∃ q ≥ N^{1/8}, q.Prime ∧ q² ∣ a`) is bounded by
   `2 * N^{7/8}` for `N ≥ 256`.
3. **Chen's Switching Inequality**:
   `#{a ∈ chenGoldbachSet N : a ∈ chenMProd N} ≤ siftedCard (chenSwitchedSet N) (N^{1/4}) + N^{1/4} + 1`.
4. **Master Weighted Sieve Inequality (`chen_weighted_sieve_inequality`)** + direct extraction of
   `∃ p q, Nat.Prime p ∧ IsP2 q ∧ p + q = N` from `0 < chenP2Count N`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open Finset Classical

namespace RHDirect.Chen

/-- The switched sequence `B_sw(N) = {N - m : m ∈ chenMProd N}` sifted for primes `p = N - q₁q₂q₃`. -/
def chenSwitchedSet (N : ℕ) : Finset ℕ :=
  (chenMProd N).image (fun m => N - m)

/-- The primes in `[N^{1/8}, N^{1/3})` not dividing `N`. -/
def chenMidPrimes (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun q : ℕ =>
    q.Prime ∧ ¬ q ∣ N ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ (q : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 3))

/-- The shifted-prime subsequence `A_q(N) = {a ∈ chenGoldbachSet N : q ∣ a}`. -/
def chenGoldbachSetDiv (N q : ℕ) : Finset ℕ :=
  (chenGoldbachSet N).filter (fun a => q ∣ a)

/-- Elements of `chenGoldbachSet N` that are `P₂`-numbers. -/
def chenP2Count (N : ℕ) : ℕ :=
  ((chenGoldbachSet N).filter IsP2).card

/-- Auxiliary: if `m > 0` has no prime factor `< y` and `(m : ℝ) < y^3`, then `m = 1 ∨ IsP2 m`. -/
private lemma isP2_or_one_of_lt_cube {m : ℕ} {y : ℝ} (hm0 : 0 < m) (hy : 0 ≤ y)
    (hmin : ∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬ p ∣ m)
    (hlt : (m : ℝ) < y ^ 3) : m = 1 ∨ IsP2 m := by
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  · right
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨k, rfl⟩ := hpm
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hm0
      · exact hk
    by_cases hk1 : k = 1
    · subst hk1; left; simpa using hp
    · obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
      obtain ⟨r, rfl⟩ := hqk
      have hr0 : 0 < r := by
        rcases Nat.eq_zero_or_pos r with rfl | hr
        · simp at hk0
        · exact hr
      by_cases hr1 : r = 1
      · subst hr1; right; exact ⟨p, q, hp, hq, by ring⟩
      · obtain ⟨t, ht, htr⟩ := Nat.exists_prime_and_dvd hr1
        have hp_ge : y ≤ (p : ℝ) := by
          by_contra hltp; push Not at hltp
          exact hmin p hp hltp (dvd_mul_right p _)
        have hq_ge : y ≤ (q : ℝ) := by
          by_contra hltq; push Not at hltq
          exact hmin q hq hltq ⟨p * r, by ring⟩
        have ht_ge : y ≤ (t : ℝ) := by
          by_contra hltt; push Not at hltt
          obtain ⟨u, rfl⟩ := htr
          exact hmin t ht hltt ⟨p * q * u, by ring⟩
        have hle_nat : p * q * t ≤ p * (q * r) := by
          have ht_le_r : t ≤ r := Nat.le_of_dvd hr0 htr
          calc p * q * t ≤ p * q * r := Nat.mul_le_mul_left (p * q) ht_le_r
            _ = p * (q * r) := by ring
        have hle_real : (p : ℝ) * (q : ℝ) * (t : ℝ) ≤ ((p * (q * r) : ℕ) : ℝ) := by
          exact_mod_cast hle_nat
        have hcube : y ^ 3 ≤ (p : ℝ) * (q : ℝ) * (t : ℝ) := by
          have h1 : y * y ≤ (p : ℝ) * (q : ℝ) := mul_le_mul hp_ge hq_ge hy (le_trans hy hp_ge)
          have h2 : y * y * y ≤ (p : ℝ) * (q : ℝ) * (t : ℝ) :=
            mul_le_mul h1 ht_ge hy (mul_nonneg (le_trans hy hp_ge) (le_trans hy hq_ge))
          simpa [pow_three, mul_assoc] using h2
        linarith

/-- If `a ∈ chenGoldbachSet N`, then `0 < a`, `a < N`, no prime dividing `a` divides `N`,
and `N - a` is prime. -/
lemma mem_chenGoldbachSet_props {N a : ℕ} (ha : a ∈ chenGoldbachSet N) :
    0 < a ∧ a < N ∧ (∀ p : ℕ, p.Prime → p ∣ a → ¬ p ∣ N) ∧ Nat.Prime (N - a) := by
  unfold chenGoldbachSet at ha
  rcases Finset.mem_image.mp ha with ⟨p, hp_mem, rfl⟩
  rcases Finset.mem_filter.mp hp_mem with ⟨hp_lt, hp_prime, hp2, hp_ndvd⟩
  have hlt : p < N := Finset.mem_range.mp hp_lt
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro q hq hqa hqN
    have hqp : q ∣ p := by
      have hsum : (N - p) + p = N := Nat.sub_add_cancel hlt.le
      exact (Nat.dvd_add_right hqa).mp (hsum.symm ▸ hqN)
    have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp_prime).mp hqp
    exact hp_ndvd (hqeq ▸ hqN)
  · rw [Nat.sub_sub_self hlt.le]
    exact hp_prime

/-- **Core Pointwise Chen Weight Inequality**:
For any `N ≥ 2` and any `a ∈ chenGoldbachSet N` with `1 < a`, no prime divisor `< N^{1/8}`,
and no squared prime divisor `q² ∣ a` with `q ≥ N^{1/8}`,
`(if IsP2 a then 1 else 0) ≥ 1 - (1/2) * #{q ∈ chenMidPrimes N : q ∣ a} - (1/2) * 1_{a ∈ chenMProd N}`. -/
lemma chen_pointwise_weight {N a : ℕ} (hN : 2 ≤ N) (ha : a ∈ chenGoldbachSet N) (ha1 : 1 < a)
    (hsift : ∀ p : ℕ, p.Prime → (p : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 8) → ¬ p ∣ a)
    (hsqf : ∀ q : ℕ, q.Prime → (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) → ¬ q ^ 2 ∣ a) :
    (1 : ℝ) - (1 / 2 : ℝ) * (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ)
      - (1 / 2 : ℝ) * (if a ∈ chenMProd N then (1 : ℝ) else 0) ≤
      if IsP2 a then (1 : ℝ) else 0 := by
  obtain ⟨ha0, haN, ha_cop, _⟩ := mem_chenGoldbachSet_props ha
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hz_def
  set y : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3) with hy_def
  have hy_pos : 0 < y := Real.rpow_pos_of_pos hNpos _
  have hy_cube : y ^ 3 = (N : ℝ) := by
    rw [hy_def, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  set S_mid := (chenMidPrimes N).filter (fun q => q ∣ a) with hSmid_def
  by_cases hP2 : IsP2 a
  · rw [if_pos hP2]
    have h1 : 0 ≤ (1 / 2 : ℝ) * (S_mid.card : ℝ) := by positivity
    have h2 : 0 ≤ (1 / 2 : ℝ) * (if a ∈ chenMProd N then (1 : ℝ) else 0) := by
      split_ifs <;> positivity
    linarith
  · rw [if_neg hP2]
    by_cases hcard2 : 2 ≤ S_mid.card
    · have hc : (2 : ℝ) ≤ (S_mid.card : ℝ) := by exact_mod_cast hcard2
      have h2 : 0 ≤ (1 / 2 : ℝ) * (if a ∈ chenMProd N then (1 : ℝ) else 0) := by
        split_ifs <;> positivity
      linarith
    · -- So `S_mid.card = 0` or `S_mid.card = 1`
      have hcard_le1 : S_mid.card ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos S_mid.card with hcard0 | hcard_pos
      · -- Case `S_mid.card = 0`: every prime factor of `a` is `≥ y`, contradicting `¬ IsP2 a`
        exfalso
        have hmin_y : ∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬ p ∣ a := by
          intro p hp hpy hpa
          have hp_ge_z : z ≤ (p : ℝ) := by
            by_contra hltz; push Not at hltz
            exact hsift p hp hltz hpa
          have hp_lt_N : p < N := lt_of_le_of_lt (Nat.le_of_dvd ha0 hpa) haN
          have hmem : p ∈ S_mid := by
            rw [hSmid_def, Finset.mem_filter]
            refine ⟨?_, hpa⟩
            unfold chenMidPrimes
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr hp_lt_N, hp, ha_cop p hp hpa, hp_ge_z, hpy⟩
          have : 0 < S_mid.card := Finset.card_pos.mpr ⟨p, hmem⟩
          omega
        have ha_lt_cube : (a : ℝ) < y ^ 3 := by rw [hy_cube]; exact_mod_cast haN
        rcases isP2_or_one_of_lt_cube ha0 hy_pos.le hmin_y ha_lt_cube with haeq1 | hP2'
        · omega
        · exact hP2 hP2'
      · -- Case `S_mid.card = 1`: extract the unique prime `q₁ ∈ S_mid`
        have hcard1 : S_mid.card = 1 := by omega
        obtain ⟨q₁, hSmid_eq⟩ := Finset.card_eq_one.mp hcard1
        have hq₁_mem : q₁ ∈ S_mid := by rw [hSmid_eq]; exact Finset.mem_singleton_self q₁
        rw [hSmid_def, Finset.mem_filter] at hq₁_mem
        rcases hq₁_mem with ⟨hq₁_mid, hq₁_dvd⟩
        unfold chenMidPrimes at hq₁_mid
        rw [Finset.mem_filter] at hq₁_mid
        rcases hq₁_mid with ⟨hq₁_ltN, hq₁_prime, hq₁_ndvdN, hq₁_ge_z, hq₁_lt_y⟩
        obtain ⟨m, hm_eq⟩ := hq₁_dvd
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at hm_eq; omega
          · exact hm
        have hq₁_ndvd_m : ¬ q₁ ∣ m := by
          intro hqm
          obtain ⟨t, rfl⟩ := hqm
          exact hsqf q₁ hq₁_prime hq₁_ge_z ⟨t, by rw [hm_eq]; ring⟩
        -- Every prime divisor of `m` is `≥ y`
        have hm_min_y : ∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬ p ∣ m := by
          intro p hp hpy hpm
          have hpa : p ∣ a := by rw [hm_eq]; exact dvd_mul_of_dvd_right hpm q₁
          have hp_ge_z : z ≤ (p : ℝ) := by
            by_contra hltz; push Not at hltz
            exact hsift p hp hltz hpa
          have hp_lt_N : p < N := lt_of_le_of_lt (Nat.le_of_dvd ha0 hpa) haN
          have hp_mem : p ∈ S_mid := by
            rw [hSmid_def, Finset.mem_filter]
            refine ⟨?_, hpa⟩
            unfold chenMidPrimes
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_range.mpr hp_lt_N, hp, ha_cop p hp hpa, hp_ge_z, hpy⟩
          rw [hSmid_eq, Finset.mem_singleton] at hp_mem
          subst hp_mem
          exact hq₁_ndvd_m hpm
        have hm_lt_N : m < N := by
          have hm_le_a : m ≤ a := by rw [hm_eq]; exact Nat.le_mul_of_pos_left m hq₁_prime.pos
          exact lt_of_le_of_lt hm_le_a haN
        have hm_lt_cube : (m : ℝ) < y ^ 3 := by rw [hy_cube]; exact_mod_cast hm_lt_N
        rcases isP2_or_one_of_lt_cube hm0 hy_pos.le hm_min_y hm_lt_cube with hm1 | hmP2
        · -- `m = 1` implies `a = q₁` is prime, contradicting `¬ IsP2 a`
          exfalso; subst hm1; rw [mul_one] at hm_eq; exact hP2 (Or.inl (hm_eq ▸ hq₁_prime))
        · rcases hmP2 with hm_prime | ⟨r, s, hr_prime, hs_prime, hm_rs⟩
          · -- `m` prime implies `a = q₁ * m` is `P₂`, contradicting `¬ IsP2 a`
            exfalso; exact hP2 (Or.inr ⟨q₁, m, hq₁_prime, hm_prime, hm_eq⟩)
          · -- `m = r * s`: sort `(r, s)` into `q₂ ≤ q₃` to prove `a ∈ chenMProd N`!
            have ha_in_MProd : a ∈ chenMProd N := by
              let q₂ := min r s
              let q₃ := max r s
              have hq₂_prime : q₂.Prime := by
                dsimp only [q₂]; by_cases h : r ≤ s
                · rw [min_eq_left h]; exact hr_prime
                · rw [min_eq_right (le_of_not_ge h)]; exact hs_prime
              have hq₃_prime : q₃.Prime := by
                dsimp only [q₃]; by_cases h : r ≤ s
                · rw [max_eq_right h]; exact hs_prime
                · rw [max_eq_left (le_of_not_ge h)]; exact hr_prime
              have hq₂_le_q₃ : q₂ ≤ q₃ := min_le_max
              have hq₂q₃_eq : q₂ * q₃ = m := by
                rw [hm_rs]; dsimp only [q₂, q₃]
                by_cases h : r ≤ s
                · rw [min_eq_left h, max_eq_right h]
                · rw [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), mul_comm]
              have ha_prod : q₁ * q₂ * q₃ = a := by rw [hm_eq, ← hq₂q₃_eq, mul_assoc]
              have hq₂_dvd_m : q₂ ∣ m := ⟨q₃, hq₂q₃_eq.symm⟩
              have hq₃_dvd_m : q₃ ∣ m := ⟨q₂, by rw [mul_comm]; exact hq₂q₃_eq.symm⟩
              have hq₂_dvd_a : q₂ ∣ a := by rw [hm_eq]; exact dvd_mul_of_dvd_right hq₂_dvd_m q₁
              have hq₃_dvd_a : q₃ ∣ a := by rw [hm_eq]; exact dvd_mul_of_dvd_right hq₃_dvd_m q₁
              have hq₂_ge_y : y ≤ (q₂ : ℝ) := by
                by_contra hlt; push Not at hlt
                exact hm_min_y q₂ hq₂_prime hlt hq₂_dvd_m
              have hq₁_range : q₁ ∈ Finset.range N := hq₁_ltN
              have hq₂_range : q₂ ∈ Finset.range N :=
                Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_dvd ha0 hq₂_dvd_a) haN)
              have hq₃_range : q₃ ∈ Finset.range N :=
                Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_dvd ha0 hq₃_dvd_a) haN)
              unfold chenMProd
              refine Finset.mem_image.mpr ⟨(q₁, q₂, q₃), ?_, ha_prod⟩
              unfold chenM
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_product.mpr ⟨hq₁_range, Finset.mem_product.mpr ⟨hq₂_range, hq₃_range⟩⟩, ?_⟩
              exact ⟨hq₁_prime, hq₂_prime, hq₃_prime,
                hq₁_ndvdN, ha_cop q₂ hq₂_prime hq₂_dvd_a, ha_cop q₃ hq₃_prime hq₃_dvd_a,
                hq₁_ge_z, hq₁_lt_y, hq₂_ge_y, hq₂_le_q₃, ha_prod.symm ▸ haN⟩
            rw [if_pos ha_in_MProd, hcard1]
            norm_num

/-- Telescoping bound: for `2 ≤ m ≤ M + 1`, `∑ q ∈ Icc m M, (1 : ℝ) / q^2 ≤ 1 / (m - 1)`. -/
private lemma sum_inv_sq_Icc_le (m M : ℕ) (hm : 2 ≤ m) :
    ∑ q ∈ Finset.Icc m M, (1 : ℝ) / ((q : ℝ) ^ 2) ≤ 1 / ((m : ℝ) - 1) := by
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  by_cases hlt : M < m
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hle : m ≤ M := by omega
    have hstep : ∀ q ∈ Finset.Icc m M,
        (1 : ℝ) / ((q : ℝ) ^ 2) ≤ 1 / ((q : ℝ) - 1) - 1 / (q : ℝ) := by
      intro q hq
      have hqm : m ≤ q := (Finset.mem_Icc.mp hq).1
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_trans hm hqm)
      have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
      have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      rw [div_sub_div _ _ hq1_pos.ne' hq_pos.ne']
      have hnum : (1 : ℝ) * (q : ℝ) - ((q : ℝ) - 1) * 1 = 1 := by ring
      rw [hnum]
      refine div_le_div_of_nonneg_left zero_le_one (mul_pos hq1_pos hq_pos) ?_
      nlinarith
    have hsum_le : ∑ q ∈ Finset.Icc m M, (1 : ℝ) / ((q : ℝ) ^ 2) ≤
        ∑ q ∈ Finset.Icc m M, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) :=
      Finset.sum_le_sum hstep
    -- Telescope by induction on `M` starting at `m`
    have htel : ∀ k : ℕ, m ≤ k →
        ∑ q ∈ Finset.Icc m k, (1 / ((q : ℝ) - 1) - 1 / (q : ℝ)) =
          1 / ((m : ℝ) - 1) - 1 / (k : ℝ) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [show Finset.Icc m (k + 1) = insert (k + 1) (Finset.Icc m k) by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
        rw [Finset.sum_insert (by simp), ih]
        push_cast
        ring
    rw [htel M hle] at hsum_le
    have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    have : 0 ≤ 1 / (M : ℝ) := by positivity
    linarith

/-- Non-squarefree exception set in `chenGoldbachSet N`: elements divisible by `q²` for some
prime `q ≥ N^{1/8}`. -/
def chenSqExceptions (N : ℕ) : Finset ℕ :=
  (chenGoldbachSet N).filter (fun a => ∃ q : ℕ, q.Prime ∧ (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (q : ℝ) ∧ q ^ 2 ∣ a)

/-- Elementary `O(N^{7/8})` upper bound on `chenSqExceptions N` for all `N ≥ 256`. -/
lemma chenSqExceptions_card_le {N : ℕ} (hN : 256 ≤ N) :
    ((chenSqExceptions N).card : ℝ) ≤ 2 * (N : ℝ) ^ ((7 : ℝ) / 8) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set z : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8) with hz_def
  have hz_ge2 : (2 : ℝ) ≤ z := by
    have h256 : (256 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2eq : (2 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h2eq, hz_def]
    exact Real.rpow_le_rpow (by norm_num) h256 (by norm_num)
  set m : ℕ := ⌈z⌉₊ with hm_def
  have hm_ge2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ (m : ℝ) := hz_ge2.trans (Nat.le_ceil z)
    exact_mod_cast this
  have hsub : chenSqExceptions N ⊆
      (Finset.Icc m (N.sqrt + 1)).biUnion (fun q => (Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a)) := by
    intro a ha
    rw [chenSqExceptions, Finset.mem_filter] at ha
    rcases ha with ⟨haG, q, hq_prime, hq_ge_z, hq2_dvd⟩
    obtain ⟨ha0, haN, _, _⟩ := mem_chenGoldbachSet_props haG
    refine Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩
    · refine Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hq_ge_z, ?_⟩
      have hq2_le : q ^ 2 ≤ a := Nat.le_of_dvd ha0 hq2_dvd
      have hq_le_sqrt : q ≤ N.sqrt := Nat.le_sqrt.mpr (by nlinarith)
      omega
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ha0, haN⟩, hq2_dvd⟩
  have hcard_le : ((chenSqExceptions N).card : ℝ) ≤
      ∑ q ∈ Finset.Icc m (N.sqrt + 1), (((Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a)).card : ℝ) := by
    have h1 : (chenSqExceptions N).card ≤
        ((Finset.Icc m (N.sqrt + 1)).biUnion (fun q => (Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a))).card :=
      Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := Finset.Icc m (N.sqrt + 1))
      (t := fun q => (Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a))
    exact_mod_cast h1.trans h2
  have hmult_le : ∀ q ∈ Finset.Icc m (N.sqrt + 1),
      (((Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a)).card : ℝ) ≤ (N : ℝ) / ((q : ℝ) ^ 2) := by
    intro q hq
    have hq_ge2 : 2 ≤ q := le_trans hm_ge2 (Finset.mem_Icc.mp hq).1
    have hq2_pos : 0 < q ^ 2 := by positivity
    -- Map `a ↦ a / q²` injects into `Finset.Icc 1 (N / q²)`
    have hinj : ((Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a)).card ≤ (Finset.Icc 1 (N / q ^ 2)).card := by
      refine Finset.card_le_card_of_injOn (fun a => a / q ^ 2) ?_ ?_
      · intro a ha
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha
        rcases ha with ⟨⟨ha1, haN⟩, ⟨k, rfl⟩⟩
        rw [Finset.mem_coe]
        dsimp only
        rw [Nat.mul_div_cancel_left k hq2_pos]
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · rcases Nat.eq_zero_or_pos k with rfl | hk
          · simp at ha1
          · exact hk
        · exact (Nat.le_div_iff_mul_le hq2_pos).mpr (by rw [mul_comm]; exact haN.le)
      · intro a₁ ha₁ a₂ ha₂ heq
        rw [Finset.mem_coe] at ha₁ ha₂
        dsimp only at heq
        rcases (Finset.mem_filter.mp ha₁).2 with ⟨k₁, rfl⟩
        rcases (Finset.mem_filter.mp ha₂).2 with ⟨k₂, rfl⟩
        rw [Nat.mul_div_cancel_left k₁ hq2_pos, Nat.mul_div_cancel_left k₂ hq2_pos] at heq
        rw [heq]
    have hnat : ((Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a)).card ≤ N / q ^ 2 := by
      simpa [Nat.card_Icc] using hinj
    have hcast : (((Finset.Ico 1 N).filter (fun a => q ^ 2 ∣ a)).card : ℝ) ≤ ((N / q ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hdiv : ((N / q ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) ^ 2) := by
      have hq2r_pos : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      rw [le_div_iff₀ hq2r_pos]
      exact_mod_cast Nat.div_mul_le_self N (q ^ 2)
    exact hcast.trans hdiv
  have hsum_bd : ((chenSqExceptions N).card : ℝ) ≤ (N : ℝ) * (1 / ((m : ℝ) - 1)) := by
    calc ((chenSqExceptions N).card : ℝ)
        ≤ ∑ q ∈ Finset.Icc m (N.sqrt + 1), (N : ℝ) / ((q : ℝ) ^ 2) :=
          hcard_le.trans (Finset.sum_le_sum hmult_le)
      _ = (N : ℝ) * ∑ q ∈ Finset.Icc m (N.sqrt + 1), (1 : ℝ) / ((q : ℝ) ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by ring
      _ ≤ (N : ℝ) * (1 / ((m : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le m (N.sqrt + 1) hm_ge2) hNpos.le
  -- Since `z ≤ m` and `2 ≤ z`, we have `z / 2 ≤ m - 1`, so `N / (m - 1) ≤ 2 * N / z = 2 * N^{7/8}`!
  have hz_le_m : z ≤ (m : ℝ) := Nat.le_ceil z
  have hm1_ge : z / 2 ≤ (m : ℝ) - 1 := by linarith
  have hz_pos : 0 < z := by linarith
  have hm1_pos : 0 < (m : ℝ) - 1 := by linarith
  have hinv_le : 1 / ((m : ℝ) - 1) ≤ 2 / z := by
    rw [div_le_div_iff₀ hm1_pos hz_pos]
    linarith
  have hpow : (N : ℝ) * (2 / z) = 2 * (N : ℝ) ^ ((7 : ℝ) / 8) := by
    rw [hz_def, mul_div_assoc', mul_comm (N : ℝ) 2, mul_div_assoc]
    congr 1
    rw [div_eq_iff (Real.rpow_pos_of_pos hNpos _).ne', ← Real.rpow_add hNpos]
    norm_num
  calc ((chenSqExceptions N).card : ℝ)
      ≤ (N : ℝ) * (1 / ((m : ℝ) - 1)) := hsum_bd
    _ ≤ (N : ℝ) * (2 / z) := mul_le_mul_of_nonneg_left hinv_le hNpos.le
    _ = 2 * (N : ℝ) ^ ((7 : ℝ) / 8) := hpow

/-- **Chen's Switching Upper Bound**:
Every `a ∈ chenGoldbachSet N ∩ chenMProd N` maps injectively via `a ↦ N - a` to a prime
`p ∈ chenSwitchedSet N`. Either `p < N^{1/4}` (at most `⌊N^{1/4}⌋₊ + 1` primes), or
`p ≥ N^{1/4}` and thus `p` survives `siftedCard (chenSwitchedSet N) (N^{1/4})`! -/
lemma chen_B_card_le_switched (N : ℕ) :
    (((chenGoldbachSet N).filter (fun a => a ∈ chenMProd N)).card : ℝ) ≤
      (siftedCard (chenSwitchedSet N) ((N : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) +
        (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
  set z4 : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with hz4_def
  set B_hit := (chenGoldbachSet N).filter (fun a => a ∈ chenMProd N)
  set S_sw := (chenSwitchedSet N).filter (fun p => ∀ r : ℕ, r.Prime → (r : ℝ) < z4 → ¬ r ∣ p)
  set S_small := Finset.range (⌊z4⌋₊ + 1)
  have hcard : B_hit.card ≤ (S_sw ∪ S_small).card := by
    refine Finset.card_le_card_of_injOn (fun a => N - a) ?_ ?_
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      obtain ⟨_, haN, _, hp_prime⟩ := mem_chenGoldbachSet_props ha.1
      rw [Finset.mem_coe]
      dsimp only
      have hsw_mem : N - a ∈ chenSwitchedSet N :=
        Finset.mem_image.mpr ⟨a, ha.2, rfl⟩
      by_cases hlt : ((N - a : ℕ) : ℝ) < z4
      · refine Finset.mem_union_right _ (Finset.mem_range.mpr ?_)
        have : N - a ≤ ⌊z4⌋₊ := Nat.le_floor hlt.le
        omega
      · push Not at hlt
        refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hsw_mem, ?_⟩)
        intro r hr hrz hrdvd
        have hreq : r = N - a := (Nat.prime_dvd_prime_iff_eq hr hp_prime).mp hrdvd
        subst hreq
        linarith
    · intro a₁ ha₁ a₂ ha₂ heq
      rw [Finset.mem_coe] at ha₁ ha₂
      dsimp only at heq
      have h1 : a₁ < N := (mem_chenGoldbachSet_props (Finset.mem_filter.mp ha₁).1).2.1
      have h2 : a₂ < N := (mem_chenGoldbachSet_props (Finset.mem_filter.mp ha₂).1).2.1
      omega
  have hunion : (S_sw ∪ S_small).card ≤ S_sw.card + S_small.card := Finset.card_union_le _ _
  have hsmall_cast : (S_small.card : ℝ) ≤ z4 + 1 := by
    rw [Finset.card_range, Nat.cast_add, Nat.cast_one]
    have hz4_nn : 0 ≤ z4 := by positivity
    linarith [Nat.floor_le hz4_nn]
  have hle_real : (B_hit.card : ℝ) ≤ (S_sw.card : ℝ) + (S_small.card : ℝ) := by
    exact_mod_cast hcard.trans hunion
  change (B_hit.card : ℝ) ≤ (S_sw.card : ℝ) + z4 + 1
  linarith

/-- **Master Combinatorial Weighted-Sieve Inequality for Chen's Theorem (`N ≥ 256`)**:
`chenP2Count N ≥ S(A, P(N^{1/8})) - (1/2) ∑_{q ∈ chenMidPrimes N} S(A_q, P(N^{1/8}))
   - (1/2) S(B_sw, P(N^{1/4})) - 2 N^{7/8} - (1/2) N^{1/4} - 2`. -/
theorem chen_weighted_sieve_inequality {N : ℕ} (hN : 256 ≤ N) :
    (siftedCard (chenGoldbachSet N) ((N : ℝ) ^ ((1 : ℝ) / 8)) : ℝ)
      - (1 / 2 : ℝ) * ∑ q ∈ chenMidPrimes N,
          (siftedCard (chenGoldbachSetDiv N q) ((N : ℝ) ^ ((1 : ℝ) / 8)) : ℝ)
      - (1 / 2 : ℝ) * (siftedCard (chenSwitchedSet N) ((N : ℝ) ^ ((1 : ℝ) / 4)) : ℝ)
      - 2 * (N : ℝ) ^ ((7 : ℝ) / 8) - (1 / 2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 4) - 2 ≤
    (chenP2Count N : ℝ) := by
  set z8 : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)
  set A_sift := (chenGoldbachSet N).filter (fun a => ∀ p : ℕ, p.Prime → (p : ℝ) < z8 → ¬ p ∣ a)
  set A_good := A_sift.filter (fun a => 1 < a ∧ a ∉ chenSqExceptions N)
  -- 1. Compare `A_sift.card` and `A_good.card`: at most `1` (`a = 1`) + `chenSqExceptions.card` removed
  have hgood_diff : (A_sift.card : ℝ) ≤ (A_good.card : ℝ) + ((chenSqExceptions N).card : ℝ) + 1 := by
    have hsub : A_sift ⊆ A_good ∪ chenSqExceptions N ∪ {1} := by
      intro a ha
      by_cases ha1 : a = 1
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr ha1)
      · by_cases hsq : a ∈ chenSqExceptions N
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hsq)
        · have ha0 : 0 < a := (mem_chenGoldbachSet_props (Finset.mem_filter.mp ha).1).1
          exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨ha, by omega, hsq⟩))
    have h1 : A_sift.card ≤ (A_good ∪ chenSqExceptions N ∪ {1}).card := Finset.card_le_card hsub
    have h2 : (A_good ∪ chenSqExceptions N ∪ {1}).card ≤ A_good.card + (chenSqExceptions N).card + 1 := by
      calc (A_good ∪ chenSqExceptions N ∪ {1}).card
          ≤ (A_good ∪ chenSqExceptions N).card + ({1} : Finset ℕ).card := Finset.card_union_le _ _
        _ ≤ A_good.card + (chenSqExceptions N).card + 1 := by
            simp only [Finset.card_singleton]
            linarith [Finset.card_union_le A_good (chenSqExceptions N)]
    exact_mod_cast h1.trans h2
  -- 2. Sum the pointwise Chen weight inequality over `a ∈ A_good`
  have hsum_pt :
      ∑ a ∈ A_good, ((1 : ℝ) - (1 / 2 : ℝ) * (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ)
          - (1 / 2 : ℝ) * (if a ∈ chenMProd N then (1 : ℝ) else 0)) ≤
        ∑ a ∈ A_good, (if IsP2 a then (1 : ℝ) else 0) := by
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.mem_filter] at ha
    rcases ha with ⟨ha_sift, ha1, ha_nsq⟩
    rw [Finset.mem_filter] at ha_sift
    have hsqf : ∀ q : ℕ, q.Prime → z8 ≤ (q : ℝ) → ¬ q ^ 2 ∣ a := by
      intro q hq hqz hq2
      exact ha_nsq (Finset.mem_filter.mpr ⟨ha_sift.1, q, hq, hqz, hq2⟩)
    exact chen_pointwise_weight (by omega) ha_sift.1 ha1 ha_sift.2 hsqf
  -- 3. RHS is `≤ chenP2Count N`
  have hRHS_le : ∑ a ∈ A_good, (if IsP2 a then (1 : ℝ) else 0) ≤ (chenP2Count N : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_card (fun a ha => by
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha.1).1).1, ha.2⟩)
  -- 4. Expand LHS sum over `A_good`
  have hLHS_eq :
      ∑ a ∈ A_good, ((1 : ℝ) - (1 / 2 : ℝ) * (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ)
          - (1 / 2 : ℝ) * (if a ∈ chenMProd N then (1 : ℝ) else 0)) =
        (A_good.card : ℝ)
          - (1 / 2 : ℝ) * (∑ a ∈ A_good, (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ))
          - (1 / 2 : ℝ) * (∑ a ∈ A_good, (if a ∈ chenMProd N then (1 : ℝ) else 0)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
  -- 5. Upper-bound the `chenMidPrimes` double sum by `∑ q ∈ chenMidPrimes N, siftedCard (A_q) z8`
  have hmid_le :
      ∑ a ∈ A_good, (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ) ≤
        ∑ q ∈ chenMidPrimes N, (siftedCard (chenGoldbachSetDiv N q) z8 : ℝ) := by
    have hswap :
        ∑ a ∈ A_good, (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ) =
          ∑ q ∈ chenMidPrimes N, ((A_good.filter (fun a => q ∣ a)).card : ℝ) := by
      have h1 : ∀ a ∈ A_good, (((chenMidPrimes N).filter (fun q => q ∣ a)).card : ℝ) =
          ∑ q ∈ chenMidPrimes N, (if q ∣ a then (1 : ℝ) else 0) := by
        intro a _; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hswap]
    refine Finset.sum_le_sum fun q _ => ?_
    exact_mod_cast Finset.card_le_card (fun a ha => by
      rw [Finset.mem_filter] at ha
      have ha_sift := (Finset.mem_filter.mp ha.1).1
      rw [Finset.mem_filter] at ha_sift
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨ha_sift.1, ha.2⟩, ha_sift.2⟩)
  -- 6. Upper-bound the `chenMProd` hit sum by `chen_B_card_le_switched`
  have hB_le :
      ∑ a ∈ A_good, (if a ∈ chenMProd N then (1 : ℝ) else 0) ≤
        (siftedCard (chenSwitchedSet N) ((N : ℝ) ^ ((1 : ℝ) / 4)) : ℝ) +
          (N : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub_B : ((A_good.filter (fun a => a ∈ chenMProd N)).card : ℝ) ≤
        (((chenGoldbachSet N).filter (fun a => a ∈ chenMProd N)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (fun a ha => by
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha.1).1).1, ha.2⟩)
    exact hsub_B.trans (chen_B_card_le_switched N)
  have hsq_bd := chenSqExceptions_card_le hN
  change (A_sift.card : ℝ)
    - (1 / 2 : ℝ) * ∑ q ∈ chenMidPrimes N, (siftedCard (chenGoldbachSetDiv N q) z8 : ℝ)
    - (1 / 2 : ℝ) * (siftedCard (chenSwitchedSet N) ((N : ℝ) ^ ((1 : ℝ) / 4)) : ℝ)
    - 2 * (N : ℝ) ^ ((7 : ℝ) / 8) - (1 / 2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 4) - 2 ≤
    (chenP2Count N : ℝ)
  linarith

/-- Direct witness extraction: if `0 < (chenP2Count N : ℝ)`, then `N = p + q` with `p` prime
and `q` a `P₂`-number (`Nat.Prime q ∨ ∃ r s, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s`). -/
theorem exists_prime_add_isP2_of_pos {N : ℕ} (hpos : (0 : ℝ) < (chenP2Count N : ℝ)) :
    ∃ p q : ℕ, Nat.Prime p ∧ IsP2 q ∧ p + q = N := by
  have hcard : 0 < ((chenGoldbachSet N).filter IsP2).card := by
    exact_mod_cast hpos
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter] at hq
  obtain ⟨_, hqN, _, hp_prime⟩ := mem_chenGoldbachSet_props hq.1
  exact ⟨N - q, q, hp_prime, hq.2, Nat.sub_add_cancel hqN.le⟩

end RHDirect.Chen
