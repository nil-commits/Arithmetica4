import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# PPL 119 (Althöfer Optimal-Play 2-Player `3n ± 1` Game): Partial Structural Milestone

**Scope Notice (Partial Milestone — NOT a full resolution of the €500 open problem):**
PPL 119 (whether every odd positive integer terminates at `1` under optimal play in Althöfer's
2-player `3n ± 1` game, i.e., zero finite or unbounded draw-traps exist) remains **OPEN**.
This file formalizes the unconditionally proved structural, cycle-obstruction, rotation-wave, and
percolation-threshold theorems documented in `scripts/ppl119_findings.md`, strictly using pure
Mathlib types (`0` custom or `private` definitions in any public theorem signature):

1. **Transition Mechanics & Predecessor Structure (Section 1):**
   - `ppl119_step_parity_dichotomy`: Exact `mod 4` parity split between the upward move
     `U(n) = (3n ± 1)/2` (`padicValNat 2 = 1`) and downward move `D(n) = (3n ∓ 1)/2^v`
     (`2 ≤ padicValNat 2`), together with uniqueness of the `2`-adic exponent `k`.
   - `ppl119_mult_three_no_predecessor`: Odd multiples of `3` have in-degree `0` in the `3n ± 1` graph.
   - `ppl119_exact_parent_fiber`: Every odd `m ≥ 1` with `¬ (3 ∣ m)` has a unique `(n, s)` parent at
     every exponent `k ≥ 1`.
   - `ppl119_smallest_losing_and_win_families`: Exact winning witnesses for `3, 5, 11` and the two
     infinite `1`-ply families `(4^k - 1)/3` (`k ≥ 2`) and `(2^(2k+1) + 1)/3` (`k ≥ 1`), plus
     verification that `n = 7` is a losing (`L`) position (both moves land in `{5, 11}`).
2. **Trap Cycle Existence & Eliahou Cycle-Length Obstruction (Section 2):**
   - `ppl119_trap_contains_cycle`: Every nonempty finite trap `D` of odd integers `≥ 3` closed
     under outgoing `3n ± 1` moves contains a directed cycle.
   - `ppl119_cycle_exact_product_equation`: Exact product equation
     `2^A = 3^L * ∏_j (1 + ε_j / (3 n_j))` and strict step excess `L < A`.
   - `ppl119_cycle_eliahou_log_bound`: Unconditional Eliahou-type logarithmic lower bound
     `|A ln 2 - L ln 3| < L / (3 n_min - 1)` and `n_min < 1/3 + L / (3 |A ln 2 - L ln 3|)`.
   - `ppl119_eliahou_farey_bracket`: General Farey-convergent cycle bound for any bracket
     `(p₁/q₁, p₂/q₂)` around `log₂ 3` with `p₂ q₁ - p₁ q₂ = 1`.
   - `ppl119_short_cycle_min_bounds`: Certified exclusions proving `n_min ≤ 295` for `L ≤ 26`,
     `n_min ≤ 112269` for `L ≤ 664`, and `n_min ≤ 5077796` for `L ≤ 970`.
3. **Irrational `log₂ 3` Rotation, `O(1/n)` 6-Wave Shift & `12`-Step Drift (Section 3):**
   - `ppl119_log2_step_shift_and_irrationality`: `Irrational (Real.log 3 / Real.log 2)`, uniform
     `|log₂ m + k - (log₂ n + log₂ 3)| < 1 / ((3n - 1) ln 2)` for both `U(n)` and `D(n)`, and
     the exact `12`-step phase drift `0 < 12 log₂ 3 - 19 < 1 / 50`.
4. **Branching Random Walk Percolation Transform & Critical Density (Section 4):**
   - `ppl119_branching_generating_function_identity`: Exact infinite-series identity for the `v₂ ≥ 2`
     downward Biggins transform for all `γ > -1`.
   - `ppl119_critical_percolation_subcritical_bound`: Explicit proof at `γ = 1/2` that
     `Φ(1/2) < 1.895`, rigorously establishing subcriticality (`p * Φ(1/2) < 1`) for all win
     densities `p ≤ 0.527` (above the empirical `0.513–0.517` 6-wave band).
-/

namespace PPL119

section TransitionStructure

private lemma odd_three_mul_add_one_even {n : ℕ} (hn : Odd n) : Even (3 * n + 1) := by
  rcases hn with ⟨k, rfl⟩
  exact ⟨3 * k + 2, by ring⟩

private lemma odd_three_mul_sub_one_even {n : ℕ} (hn : Odd n) (hn1 : 1 ≤ n) :
    Even (3 * n - 1) := by
  rcases hn with ⟨k, rfl⟩
  refine ⟨3 * k + 1, ?_⟩
  omega

private lemma padicValNat_two_eq_one_of_mod_four_eq_two {x : ℕ} (hx : x % 4 = 2) :
    padicValNat 2 x = 1 := by
  have hne0 : x ≠ 0 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ x := by omega
  have h4ndvd : ¬ 4 ∣ x := by omega
  have hle : 1 ≤ padicValNat 2 x := one_le_padicValNat_of_dvd hne0 h2dvd
  have hlt : padicValNat 2 x < 2 := by
    by_contra hge
    push Not at hge
    have hd4 : 2 ^ 2 ∣ x := (padicValNat_dvd_iff_le hne0).mpr hge
    exact h4ndvd (by simpa using hd4)
  omega

private lemma padicValNat_two_ge_two_of_dvd_four {x : ℕ} (hx0 : x ≠ 0) (hx4 : 4 ∣ x) :
    2 ≤ padicValNat 2 x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (padicValNat_dvd_iff_le hx0).mp (by simpa using hx4)

private lemma padicValNat_two_unique {m k x : ℕ} (hm : Odd m) (_hx : x ≠ 0) (heq : m * 2 ^ k = x) :
    k = padicValNat 2 x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by rcases hm with ⟨r, rfl⟩; omega
  have hm_cop : ¬ 2 ∣ m := by rcases hm with ⟨r, rfl⟩; omega
  have hv_m : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd hm_cop
  have hv_pow : padicValNat 2 (2 ^ k) = k := padicValNat.prime_pow k
  rw [← heq, padicValNat.mul hm0 (pow_ne_zero k (by norm_num)), hv_m, hv_pow, zero_add]

/-- Theorem 1a (`3n ± 1` Parity Dichotomy & `2`-Adic Valuation Uniqueness):
For any odd `n ≥ 1`, both `3 * n + 1` and `3 * n - 1` are positive and even; one has
`padicValNat 2 = 1` (producing the upward step `U(n) = (3n ± 1)/2 ≥ n`, strictly `> n` for `n ≥ 3`)
while the other has `2 ≤ padicValNat 2` (producing the downward step `D(n) ≤ (3n ∓ 1)/4`, strictly
`< n` for `n ≥ 3`). Furthermore, any factorization `(m : ℤ) * 2 ^ k = 3 * (n : ℤ) + s` (`Odd m`,
`s ∈ {1, -1}`) uniquely forces `k = padicValNat 2 (3 * n + s).natAbs`. -/
theorem ppl119_step_parity_dichotomy {n : ℕ} (hn : Odd n) (hn1 : 1 ≤ n) :
    (0 < 3 * n + 1 ∧ 0 < 3 * n - 1) ∧
    (1 ≤ padicValNat 2 (3 * n + 1) ∧ 1 ≤ padicValNat 2 (3 * n - 1)) ∧
    ((n % 4 = 1 →
        padicValNat 2 (3 * n - 1) = 1 ∧ 2 ≤ padicValNat 2 (3 * n + 1) ∧
        (3 ≤ n → n < (3 * n - 1) / 2 ∧
          (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1) < n)) ∧
     (n % 4 = 3 →
        padicValNat 2 (3 * n + 1) = 1 ∧ 2 ≤ padicValNat 2 (3 * n - 1) ∧
        (3 ≤ n → n < (3 * n + 1) / 2 ∧
          (3 * n - 1) / 2 ^ padicValNat 2 (3 * n - 1) < n))) ∧
    (∀ m k : ℕ, Odd m → ∀ s : ℤ, (s = 1 ∨ s = -1) →
      (m : ℤ) * 2 ^ k = 3 * (n : ℤ) + s →
      k = padicValNat 2 (3 * n + s).natAbs ∧ 1 ≤ k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : 0 < 3 * n + 1 := by omega
  have hm1 : 0 < 3 * n - 1 := by omega
  have hev1 : 2 ∣ 3 * n + 1 := Even.two_dvd (odd_three_mul_add_one_even hn)
  have hev2 : 2 ∣ 3 * n - 1 := Even.two_dvd (odd_three_mul_sub_one_even hn hn1)
  have hv1_pos : 1 ≤ padicValNat 2 (3 * n + 1) := one_le_padicValNat_of_dvd hp1.ne' hev1
  have hv2_pos : 1 ≤ padicValNat 2 (3 * n - 1) := one_le_padicValNat_of_dvd hm1.ne' hev2
  refine ⟨⟨hp1, hm1⟩, ⟨hv1_pos, hv2_pos⟩, ⟨?_, ?_⟩, ?_⟩
  · intro hmod
    have hval1 : padicValNat 2 (3 * n - 1) = 1 :=
      padicValNat_two_eq_one_of_mod_four_eq_two (by omega)
    have hval2 : 2 ≤ padicValNat 2 (3 * n + 1) :=
      padicValNat_two_ge_two_of_dvd_four hp1.ne' (by omega)
    refine ⟨hval1, hval2, fun hn3 => ⟨by omega, ?_⟩⟩
    have hpow : 4 ≤ 2 ^ padicValNat 2 (3 * n + 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ padicValNat 2 (3 * n + 1) := Nat.pow_le_pow_right (by norm_num) hval2
    have hq_le : (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1) ≤ (3 * n + 1) / 4 :=
      Nat.div_le_div_left hpow (by norm_num)
    omega
  · intro hmod
    have hval1 : padicValNat 2 (3 * n + 1) = 1 :=
      padicValNat_two_eq_one_of_mod_four_eq_two (by omega)
    have hval2 : 2 ≤ padicValNat 2 (3 * n - 1) :=
      padicValNat_two_ge_two_of_dvd_four hm1.ne' (by omega)
    refine ⟨hval1, hval2, fun hn3 => ⟨by omega, ?_⟩⟩
    have hpow : 4 ≤ 2 ^ padicValNat 2 (3 * n - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ padicValNat 2 (3 * n - 1) := Nat.pow_le_pow_right (by norm_num) hval2
    have hq_le : (3 * n - 1) / 2 ^ padicValNat 2 (3 * n - 1) ≤ (3 * n - 1) / 4 :=
      Nat.div_le_div_left hpow (by norm_num)
    omega
  · intro m k hm s hs heq
    have hx_nat : m * 2 ^ k = (3 * (n : ℤ) + s).natAbs := by
      have hnn : 0 ≤ 3 * (n : ℤ) + s := by rcases hs with rfl | rfl <;> omega
      zify
      rw [abs_of_nonneg hnn]
      exact heq
    have hx0 : (3 * (n : ℤ) + s).natAbs ≠ 0 := by rcases hs with rfl | rfl <;> omega
    have hk_eq := padicValNat_two_unique hm hx0 hx_nat
    refine ⟨hk_eq, ?_⟩
    rcases hs with rfl | rfl
    · have : (3 * (n : ℤ) + 1).natAbs = 3 * n + 1 := by omega
      rw [hk_eq, this]; exact hv1_pos
    · have : (3 * (n : ℤ) + -1).natAbs = 3 * n - 1 := by omega
      rw [hk_eq, this]; exact hv2_pos

/-- Theorem 1b (Multiples of `3` Have Zero In-Degree):
If `3 ∣ m`, then `m` has no predecessors in the `3n ± 1` transition graph. -/
theorem ppl119_mult_three_no_predecessor {m : ℕ} (hm3 : 3 ∣ m) :
    ¬ ∃ n k : ℕ, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (m : ℤ) * 2 ^ k = 3 * (n : ℤ) + s := by
  rintro ⟨n, k, s, hs, heq⟩
  rcases hm3 with ⟨t, rfl⟩
  have h3dvd : (3 : ℤ) ∣ 3 * ((t : ℤ) * 2 ^ k - n) := dvd_mul_right 3 _
  have hs_eq : s = 3 * ((t : ℤ) * 2 ^ k - n) := by
    calc s = 3 * (n : ℤ) + s - 3 * (n : ℤ) := by ring
      _ = ((3 * t : ℕ) : ℤ) * 2 ^ k - 3 * (n : ℤ) := by rw [← heq]
      _ = 3 * ((t : ℤ) * 2 ^ k - n) := by push_cast; ring
  rw [← hs_eq] at h3dvd
  rcases hs with rfl | rfl <;> omega

/-- Theorem 1c (Exact Parent Fiber):
For every odd `m ≥ 1` not divisible by `3` and every exponent `k ≥ 1`, there exists a unique
odd `n ≥ 1` and sign `s ∈ {1, -1}` satisfying `(m : ℤ) * 2 ^ k = 3 * (n : ℤ) + s`. -/
theorem ppl119_exact_parent_fiber {m : ℕ} (hm_odd : Odd m) (hm1 : 1 ≤ m) (hm3 : ¬ 3 ∣ m)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃! p : ℕ × ℤ, 1 ≤ p.1 ∧ Odd p.1 ∧ (p.2 = 1 ∨ p.2 = -1) ∧
      (m : ℤ) * 2 ^ k = 3 * (p.1 : ℤ) + p.2 := by
  have _ := hm_odd
  have h2k_ndvd3 : ¬ 3 ∣ 2 ^ k := by
    intro h
    have h2dvd : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hm2k_ndvd3 : ¬ 3 ∣ m * 2 ^ k := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h2
    · exact hm3 h1
    · exact h2k_ndvd3 h2
  have h2k_even : 2 ∣ m * 2 ^ k := dvd_mul_of_dvd_right (dvd_pow_self 2 (by omega)) m
  have h2k_mod2 : (m * 2 ^ k) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2k_even
  have h2k_ge2 : 2 ≤ m * 2 ^ k := by
    have : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
    nlinarith
  have hmod3 : (m * 2 ^ k) % 3 = 1 ∨ (m * 2 ^ k) % 3 = 2 := by omega
  rcases hmod3 with h1 | h2
  · set q := (m * 2 ^ k - 1) / 3
    have hsub_mod : (m * 2 ^ k - 1) % 3 = 0 := by omega
    have hdiv3 : 3 ∣ m * 2 ^ k - 1 := Nat.dvd_of_mod_eq_zero hsub_mod
    have hmul : 3 * q = m * 2 ^ k - 1 := Nat.mul_div_cancel' hdiv3
    have hmulZ : (m : ℤ) * 2 ^ k = 3 * (q : ℤ) + 1 := by
      have hmul' : ((3 * q : ℕ) : ℤ) = ((m * 2 ^ k - 1 : ℕ) : ℤ) := by exact_mod_cast hmul
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_pow] at hmul'
      push_cast at hmul' ⊢
      linarith
    refine ⟨(q, 1), ?_, ?_⟩
    · have hn_pos : 1 ≤ q := by omega
      have hn_odd : Odd q := by rw [Nat.odd_iff]; omega
      exact ⟨hn_pos, hn_odd, Or.inl rfl, hmulZ⟩
    · rintro ⟨n, s⟩ ⟨_, _, hs, heq⟩
      have hs1 : s = 1 := by
        rcases hs with rfl | rfl
        · rfl
        · exfalso; omega
      subst hs1
      have hn_eqZ : (n : ℤ) = (q : ℤ) := by linarith
      exact Prod.ext (by exact_mod_cast hn_eqZ) rfl
  · set q := (m * 2 ^ k + 1) / 3
    have hadd_mod : (m * 2 ^ k + 1) % 3 = 0 := by omega
    have hdiv3 : 3 ∣ m * 2 ^ k + 1 := Nat.dvd_of_mod_eq_zero hadd_mod
    have hmul : 3 * q = m * 2 ^ k + 1 := Nat.mul_div_cancel' hdiv3
    have hmulZ : (m : ℤ) * 2 ^ k = 3 * (q : ℤ) + -1 := by
      have hmul' : ((3 * q : ℕ) : ℤ) = ((m * 2 ^ k + 1 : ℕ) : ℤ) := by exact_mod_cast hmul
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hmul'
      push_cast at hmul' ⊢
      linarith
    refine ⟨(q, -1), ?_, ?_⟩
    · have hn_pos : 1 ≤ q := by omega
      have hn_odd : Odd q := by rw [Nat.odd_iff]; omega
      exact ⟨hn_pos, hn_odd, Or.inr rfl, hmulZ⟩
    · rintro ⟨n, s⟩ ⟨_, _, hs, heq⟩
      have hsm1 : s = -1 := by
        rcases hs with rfl | rfl
        · exfalso; omega
        · rfl
      subst hsm1
      have hn_eqZ : (n : ℤ) = (q : ℤ) := by linarith
      exact Prod.ext (by exact_mod_cast hn_eqZ) rfl

/-- Theorem 1d (Base Game Resolutions — `n = 7` Smallest `L` & Infinite `1`-Ply `W` Families):
1. `n = 3, 5, 11` and every member of BOTH infinite families `n = (4 ^ k - 1) / 3` (`k ≥ 2`) and
   `n = (2 ^ (2 * k + 1) + 1) / 3` (`k ≥ 1`) are `1`-ply `W`-positions reaching `1` directly.
2. At `n = 7`, every valid `3 * 7 ± 1` move (`m` odd, `(m : ℤ) * 2^j = 3 * 7 + s`) equals `5` or
   `11`, each of which reaches `1` in `1` ply — certifying `7` as a `2`-ply `L`-position. -/
theorem ppl119_smallest_losing_and_win_families :
    (∀ n ∈ ({3, 5, 11} : Finset ℕ),
      ∃ j : ℕ, 1 ≤ j ∧ ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (1 : ℤ) * 2 ^ j = 3 * (n : ℤ) + s) ∧
    (∀ k : ℕ, 2 ≤ k →
      let n : ℕ := (4 ^ k - 1) / 3
      3 ≤ n ∧ Odd n ∧ ∃ j : ℕ, 1 ≤ j ∧ (1 : ℤ) * 2 ^ j = 3 * (n : ℤ) + 1) ∧
    (∀ k : ℕ, 1 ≤ k →
      let n : ℕ := (2 ^ (2 * k + 1) + 1) / 3
      3 ≤ n ∧ Odd n ∧ ∃ j : ℕ, 1 ≤ j ∧ (1 : ℤ) * 2 ^ j = 3 * (n : ℤ) - 1) ∧
    (∀ m j : ℕ, Odd m → 1 ≤ j → ∀ s : ℤ, (s = 1 ∨ s = -1) →
      (m : ℤ) * 2 ^ j = 3 * (7 : ℤ) + s →
      (m = 5 ∨ m = 11) ∧
        ∃ j' : ℕ, 1 ≤ j' ∧ ∃ s' : ℤ, (s' = 1 ∨ s' = -1) ∧ (1 : ℤ) * 2 ^ j' = 3 * (m : ℤ) + s') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨3, by norm_num, -1, Or.inr rfl, by norm_num⟩
    · exact ⟨4, by norm_num, 1, Or.inl rfl, by norm_num⟩
    · exact ⟨5, by norm_num, -1, Or.inr rfl, by norm_num⟩
  · intro k hk
    have h4mod_all : ∀ r : ℕ, 4 ^ r % 3 = 1 := fun r => by
      induction r with
      | zero => norm_num
      | succ r ih => rw [pow_succ, Nat.mul_mod, ih]
    have hmod : 4 ^ k % 3 = 1 := h4mod_all k
    have h4ge : 16 ≤ 4 ^ k := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    set n : ℕ := (4 ^ k - 1) / 3
    have hsub_mod : (4 ^ k - 1) % 3 = 0 := by omega
    have hdvd3 : 3 ∣ 4 ^ k - 1 := Nat.dvd_of_mod_eq_zero hsub_mod
    have hmul : 3 * n = 4 ^ k - 1 := Nat.mul_div_cancel' hdvd3
    have h4mod2 : (4 ^ k) % 2 = 0 := by
      have : 4 ^ k = 2 ^ (2 * k) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      rw [this]
      exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
    have hodd : Odd n := by rw [Nat.odd_iff]; omega
    refine ⟨by omega, hodd, 2 * k, by omega, ?_⟩
    have hpow : (2 : ℤ) ^ (2 * k) = (4 : ℤ) ^ k := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [one_mul, hpow]
    have hmulZ : (3 : ℤ) * n = (4 : ℤ) ^ k - 1 := by
      have hmul' : (3 : ℤ) * n = ((4 ^ k - 1 : ℕ) : ℤ) := by exact_mod_cast hmul
      rw [hmul', Nat.cast_sub (by omega), Nat.cast_pow]
      norm_num
    linarith
  · intro k hk
    have h4mod_fn : ∀ r : ℕ, 1 ≤ r → 4 ^ r % 3 = 1 := by
      intro r hr
      induction r with
      | zero => omega
      | succ r ih =>
        by_cases hr0 : r = 0
        · subst hr0; norm_num
        · rw [pow_succ, Nat.mul_mod, ih (by omega)]
    have hpow_even : 2 ^ (2 * k) % 3 = 1 := by
      rw [← h4mod_fn k hk, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    have hmod : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, Nat.mul_mod, hpow_even]
    have hge8 : 8 ≤ 2 ^ (2 * k + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    set n : ℕ := (2 ^ (2 * k + 1) + 1) / 3
    have hadd_mod : (2 ^ (2 * k + 1) + 1) % 3 = 0 := by omega
    have hdvd3 : 3 ∣ 2 ^ (2 * k + 1) + 1 := Nat.dvd_of_mod_eq_zero hadd_mod
    have hmul : 3 * n = 2 ^ (2 * k + 1) + 1 := Nat.mul_div_cancel' hdvd3
    have h2mod2 : (2 ^ (2 * k + 1)) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
    have hodd : Odd n := by rw [Nat.odd_iff]; omega
    refine ⟨by omega, hodd, 2 * k + 1, by omega, ?_⟩
    rw [one_mul]
    have hmulZ : (3 : ℤ) * n = (2 : ℤ) ^ (2 * k + 1) + 1 := by exact_mod_cast hmul
    linarith
  · intro m j hm hj s hs heq
    have hm_eq : m = 5 ∨ m = 11 := by
      rcases hs with rfl | rfl
      · have heq22Z : (m : ℤ) * 2 ^ j = 22 := by linarith
        have heq22 : m * 2 ^ j = 22 := by exact_mod_cast heq22Z
        have hj_eq : j = 1 := by
          have : 2 ^ j ≤ 22 := by
            have hm1 : 1 ≤ m := by rcases hm with ⟨r, rfl⟩; omega
            nlinarith
          have hj_lt : j < 5 := by
            by_contra hge; push Not at hge
            have : 32 ≤ 2 ^ j := le_trans (by norm_num : 32 ≤ 2 ^ 5)
              (Nat.pow_le_pow_right (by norm_num) hge)
            omega
          interval_cases j <;> rcases hm with ⟨r, rfl⟩ <;> omega
        subst hj_eq; right; omega
      · have heq20Z : (m : ℤ) * 2 ^ j = 20 := by linarith
        have heq20 : m * 2 ^ j = 20 := by exact_mod_cast heq20Z
        have hj_eq : j = 2 := by
          have : 2 ^ j ≤ 20 := by
            have hm1 : 1 ≤ m := by rcases hm with ⟨r, rfl⟩; omega
            nlinarith
          have hj_lt : j < 5 := by
            by_contra hge; push Not at hge
            have : 32 ≤ 2 ^ j := le_trans (by norm_num : 32 ≤ 2 ^ 5)
              (Nat.pow_le_pow_right (by norm_num) hge)
            omega
          interval_cases j <;> rcases hm with ⟨r, rfl⟩ <;> omega
        subst hj_eq; left; omega
    refine ⟨hm_eq, ?_⟩
    rcases hm_eq with rfl | rfl
    · exact ⟨4, by norm_num, 1, Or.inl rfl, by norm_num⟩
    · exact ⟨5, by norm_num, -1, Or.inr rfl, by norm_num⟩

end TransitionStructure

section EliahouCycleObstruction

/-- Theorem 2a (Every Finite Draw-Trap Contains a Directed `3n ± 1` Cycle):
If `D : Finset ℕ` is nonempty, consists of odd integers `≥ 3`, and every `x ∈ D` has at least one
`3n ± 1` successor in `D`, then there exists a directed `3n ± 1` cycle `n : Fin L → ℕ` (`1 ≤ L`)
inside `D`. -/
theorem ppl119_trap_contains_cycle {D : Finset ℕ} (hD_ne : D.Nonempty)
    (hD_odd : ∀ x ∈ D, 3 ≤ x ∧ Odd x)
    (hD_step : ∀ x ∈ D, ∃ y ∈ D, ∃ k : ℕ, 1 ≤ k ∧ ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (y : ℤ) * 2 ^ k = 3 * (x : ℤ) + s) :
    ∃ (L : ℕ) (_ : 1 ≤ L) (n : Fin L → ℕ) (k : Fin L → ℕ) (ε : Fin L → ℤ),
      (∀ j : Fin L, n j ∈ D ∧ 3 ≤ n j ∧ Odd (n j) ∧ 1 ≤ k j ∧ (ε j = 1 ∨ ε j = -1)) ∧
      (∀ j : Fin L,
        (n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℤ) * 2 ^ (k j) = 3 * (n j : ℤ) + ε j) := by
  classical
  let succ : ℕ → ℕ := fun x =>
    if hx : x ∈ D then Classical.choose (hD_step x hx) else x
  have hsucc_mem : ∀ x ∈ D, succ x ∈ D := fun x hx => by
    dsimp [succ]; rw [dif_pos hx]; exact (Classical.choose_spec (hD_step x hx)).1
  have hsucc_eq : ∀ x ∈ D, ∃ k : ℕ, 1 ≤ k ∧ ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      (succ x : ℤ) * 2 ^ k = 3 * (x : ℤ) + s := fun x hx => by
    dsimp [succ]; rw [dif_pos hx]; exact (Classical.choose_spec (hD_step x hx)).2
  let seq : ℕ → ℕ := fun t => Nat.iterate succ t hD_ne.choose
  have hseq_mem : ∀ t : ℕ, seq t ∈ D := fun t => by
    induction t with
    | zero => exact hD_ne.choose_spec
    | succ t ih => simpa [seq, Function.iterate_succ_apply'] using hsucc_mem _ ih
  have hnot_inj : ¬ Function.Injective (fun i : Fin (D.card + 1) => seq i.1) := by
    intro hinj
    have hcard := Finset.card_le_card (Finset.image_subset_iff.mpr (fun i _ => hseq_mem i.1) :
      Finset.univ.image (fun i : Fin (D.card + 1) => seq i.1) ⊆ D)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  rw [Function.Injective] at hnot_inj
  push Not at hnot_inj
  obtain ⟨i₁, i₂, heq, hne⟩ := hnot_inj
  wlog hlt : i₁.1 < i₂.1 generalizing i₁ i₂
  · exact this i₂ i₁ heq.symm hne.symm (lt_of_le_of_ne (not_lt.mp hlt) (fun h => hne (Fin.ext h.symm)))
  let L := i₂.1 - i₁.1
  have hL : 1 ≤ L := by omega
  have hperiod : ∀ r : ℕ, seq (i₁.1 + r) = seq (i₂.1 + r) := fun r => by
    induction r with
    | zero => exact heq
    | succ r ih =>
      dsimp [seq]
      rw [show i₁.1 + (r + 1) = (i₁.1 + r) + 1 by omega,
        show i₂.1 + (r + 1) = (i₂.1 + r) + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg succ ih
  have hperiod_L : ∀ r : ℕ, seq (i₁.1 + (r + L)) = seq (i₁.1 + r) := fun r => by
    have : i₁.1 + (r + L) = i₂.1 + r := by dsimp [L]; omega
    rw [this, ← hperiod r]
  have hperiod_mod : ∀ t : ℕ, seq (i₁.1 + t % L) = seq (i₁.1 + t) := fun t => by
    have hdiv : t = t % L + L * (t / L) := (Nat.mod_add_div t L).symm
    conv_rhs => rw [hdiv]
    induction (t / L) with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ]
      calc seq (i₁.1 + t % L)
          = seq (i₁.1 + (t % L + L * m)) := ih
        _ = seq (i₁.1 + (t % L + L * m + L)) := (hperiod_L (t % L + L * m)).symm
        _ = seq (i₁.1 + (t % L + (L * m + L))) := by rw [add_assoc (t % L)]
  let n : Fin L → ℕ := fun j => seq (i₁.1 + j.1)
  let k : Fin L → ℕ := fun j => Classical.choose (hsucc_eq (n j) (hseq_mem (i₁.1 + j.1)))
  let ε : Fin L → ℤ := fun j =>
    Classical.choose (Classical.choose_spec (hsucc_eq (n j) (hseq_mem (i₁.1 + j.1)))).2
  refine ⟨L, hL, n, k, ε, fun j => ?_, fun j => ?_⟩
  · have hm := hseq_mem (i₁.1 + j.1)
    have hspec1 := Classical.choose_spec (hsucc_eq (n j) hm)
    have hspec2 := Classical.choose_spec hspec1.2
    exact ⟨hm, (hD_odd _ hm).1, (hD_odd _ hm).2, hspec1.1, hspec2.1⟩
  · have hm := hseq_mem (i₁.1 + j.1)
    have hspec1 := Classical.choose_spec (hsucc_eq (n j) hm)
    have hspec2 := Classical.choose_spec hspec1.2
    have hnext : n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ = succ (n j) := by
      dsimp [n]
      rw [hperiod_mod (j.1 + 1)]
      dsimp [seq]
      rw [show i₁.1 + (j.1 + 1) = (i₁.1 + j.1) + 1 by omega, Function.iterate_succ_apply']
    rw [hnext]
    exact hspec2.2

/-- Theorem 2b (Exact Cycle Product Equation & Step Excess `L < A`):
For any directed `3n ± 1` cycle `n : Fin L → ℕ` (`1 ≤ L`, `∀ j, 3 ≤ n j`, `ε j ∈ {1, -1}`) with
`(n (j + 1) : ℤ) * 2^(k j) = 3 * (n j : ℤ) + ε j` and `A = ∑ j : Fin L, k j`:
1. `(2 : ℝ) ^ A = (3 : ℝ) ^ L * ∏ j : Fin L, (1 + (ε j : ℝ) / (3 * (n j : ℝ)))`, and
2. `L < A` strictly. -/
theorem ppl119_cycle_exact_product_equation {L : ℕ} (hL : 1 ≤ L)
    (n : Fin L → ℕ) (k : Fin L → ℕ) (ε : Fin L → ℤ)
    (hn3 : ∀ j : Fin L, 3 ≤ n j)
    (hε : ∀ j : Fin L, ε j = 1 ∨ ε j = -1)
    (hstep : ∀ j : Fin L,
      (n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℤ) * 2 ^ (k j) = 3 * (n j : ℤ) + ε j) :
    L < ∑ j : Fin L, k j ∧
    (2 : ℝ) ^ (∑ j : Fin L, k j) =
      (3 : ℝ) ^ L * ∏ j : Fin L, (1 + (ε j : ℝ) / (3 * (n j : ℝ))) := by
  have hn_pos : ∀ j : Fin L, (0 : ℝ) < (n j : ℝ) := fun j => by
    have := hn3 j
    exact_mod_cast (by omega : 0 < n j)
  have hstepR : ∀ j : Fin L,
      ((n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℝ) / (n j : ℝ)) * (2 : ℝ) ^ (k j) =
      3 * (1 + (ε j : ℝ) / (3 * (n j : ℝ))) := fun j => by
    have hnj0 : (n j : ℝ) ≠ 0 := (hn_pos j).ne'
    have hZ : (n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℝ) * (2 : ℝ) ^ (k j) =
        3 * (n j : ℝ) + (ε j : ℝ) := by
      exact_mod_cast hstep j
    field_simp
    linarith
  have hprod_eq : (∏ j : Fin L, ((n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℝ) / (n j : ℝ)) *
        (2 : ℝ) ^ (k j)) =
      ∏ j : Fin L, (3 * (1 + (ε j : ℝ) / (3 * (n j : ℝ)))) :=
    Finset.prod_congr rfl fun j _ => hstepR j
  have htele : (∏ j : Fin L, ((n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℝ) / (n j : ℝ))) = 1 := by
    rw [Finset.prod_div_distrib]
    let e : Fin L ≃ Fin L :=
      { toFun := fun j => ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩
        invFun := fun j => ⟨(j.1 + (L - 1)) % L, Nat.mod_lt _ (by omega)⟩
        left_inv := fun j => Fin.ext (by
          dsimp
          have hj := j.2
          rw [Nat.mod_add_mod, show j.1 + 1 + (L - 1) = j.1 + L by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hj])
        right_inv := fun j => Fin.ext (by
          dsimp
          have hj := j.2
          rw [Nat.mod_add_mod, show j.1 + (L - 1) + 1 = j.1 + L by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hj]) }
    have hnum : (∏ j : Fin L, (n (e j) : ℝ)) = ∏ j : Fin L, (n j : ℝ) :=
      Fintype.prod_equiv e _ _ fun _ => rfl
    have hden0 : (∏ j : Fin L, (n j : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => (hn_pos j).ne'
    dsimp [e] at hnum
    rw [hnum, div_self hden0]
  rw [Finset.prod_mul_distrib, htele, one_mul, Finset.prod_pow_eq_pow_sum,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod_eq
  refine ⟨?_, hprod_eq⟩
  have hterm : ∀ j : Fin L, (8 / 9 : ℝ) ≤ 1 + (ε j : ℝ) / (3 * (n j : ℝ)) := by
    intro j
    have hnR : (3 : ℝ) ≤ n j := by exact_mod_cast hn3 j
    rcases hε j with h | h <;> rw [h]
    · have : 0 < 1 / (3 * (n j : ℝ)) := by positivity
      push_cast; linarith
    · have : 1 / (3 * (n j : ℝ)) ≤ 1 / 9 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      push_cast; rw [neg_div]; linarith
  have hprod_ge : (8 / 9 : ℝ) ^ L ≤ ∏ j : Fin L, (1 + (ε j : ℝ) / (3 * (n j : ℝ))) := by
    calc (8 / 9 : ℝ) ^ L = ∏ _j : Fin L, (8 / 9 : ℝ) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j : Fin L, (1 + (ε j : ℝ) / (3 * (n j : ℝ))) :=
          Finset.prod_le_prod (fun _ _ => by norm_num) (fun j _ => hterm j)
  have h2L_lt : (2 : ℝ) ^ L < (3 : ℝ) ^ L * (8 / 9 : ℝ) ^ L := by
    rw [← mul_pow, show (3 : ℝ) * (8 / 9) = 8 / 3 by norm_num]
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have h2_lt : (2 : ℝ) ^ L < (2 : ℝ) ^ (∑ j : Fin L, k j) := by
    calc (2 : ℝ) ^ L < (3 : ℝ) ^ L * (8 / 9 : ℝ) ^ L := h2L_lt
      _ ≤ (3 : ℝ) ^ L * ∏ j : Fin L, (1 + (ε j : ℝ) / (3 * (n j : ℝ))) :=
          mul_le_mul_of_nonneg_left hprod_ge (by positivity)
      _ = (2 : ℝ) ^ (∑ j : Fin L, k j) := hprod_eq.symm
  have h2_nat : (2 : ℕ) ^ L < 2 ^ (∑ j : Fin L, k j) := by exact_mod_cast h2_lt
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2_nat

private lemma log_one_add_sub_abs_lt {n s : ℝ} (hn : 3 ≤ n) (hs : s = 1 ∨ s = -1) :
    |Real.log (1 + s / (3 * n))| < 1 / (3 * n - 1) := by
  have h3n_gt1 : 1 < 3 * n := by linarith
  have h3n_pos : 0 < 3 * n := by linarith
  rcases hs with rfl | rfl
  · have hge1 : 1 ≤ 1 + 1 / (3 * n) := by linarith [div_pos one_pos h3n_pos]
    have hgt1 : 1 < 1 + 1 / (3 * n) := by linarith [div_pos one_pos h3n_pos]
    have hpos : 0 < 1 + 1 / (3 * n) := by linarith
    rw [abs_of_nonneg (Real.log_nonneg hge1)]
    have hlt := Real.log_lt_sub_one_of_pos hpos hgt1.ne'
    have hlt2 : 1 / (3 * n) < 1 / (3 * n - 1) :=
      div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
    linarith
  · have hpos : 0 < 1 + (-1) / (3 * n) := by
      have : 1 / (3 * n) ≤ 1 / 9 := div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
      rw [neg_div]; linarith
    have hlt1 : 1 + (-1) / (3 * n) < 1 := by
      have : 0 < 1 / (3 * n) := div_pos one_pos h3n_pos
      rw [neg_div]; linarith
    rw [abs_of_nonpos (Real.log_nonpos hpos.le hlt1.le), ← Real.log_inv]
    have hinv_gt1 : 1 < (1 + (-1) / (3 * n))⁻¹ := one_lt_inv₀ hpos |>.mpr hlt1
    have hlt := Real.log_lt_sub_one_of_pos (inv_pos.mpr hpos) hinv_gt1.ne'
    have hne_sub : 3 * n - 1 ≠ 0 := by linarith
    have h3n0 : 3 * n ≠ 0 := by linarith
    have h1m : 1 + (-1) / (3 * n) = (3 * n - 1) / (3 * n) := by field_simp; ring
    have hid : (1 + (-1) / (3 * n))⁻¹ - 1 = 1 / (3 * n - 1) := by
      rw [h1m, inv_div]; field_simp; ring
    linarith

private lemma abs_sum_log_eq_ne_zero {A L : ℕ} (hA : 1 ≤ A) (_hL : 1 ≤ L) :
    |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| ≠ 0 := by
  intro h0
  rw [abs_eq_zero, sub_eq_zero] at h0
  have hexp : Real.exp ((A : ℝ) * Real.log 2) = Real.exp ((L : ℝ) * Real.log 3) :=
    congrArg Real.exp h0
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num), Real.exp_log (by norm_num)] at hexp
  have hnat : 2 ^ A = 3 ^ L := by exact_mod_cast hexp
  have hev : Even (2 ^ A) := Even.pow_of_ne_zero even_two (by omega)
  have hodd : Odd (3 ^ L) := Odd.pow (by decide : Odd 3)
  rw [hnat] at hev
  exact (Nat.not_odd_iff_even.mpr hev) hodd

/-- Theorem 2c (Unconditional Eliahou-Type Cycle-Length Bound):
For any directed `3n ± 1` cycle `n : Fin L → ℕ` (`1 ≤ L`, `ε j ∈ {1, -1}`) with lower bound
`3 ≤ n_min ≤ n j` (`∀ j`) and `A = ∑ j, k j`:
1. `|A * ln 2 - L * ln 3| < L / (3 * n_min - 1)`,
2. `|A * ln 2 - L * ln 3| ≠ 0`, and
3. `(n_min : ℝ) < 1 / 3 + (L : ℝ) / (3 * |A * ln 2 - L * ln 3|)`. -/
theorem ppl119_cycle_eliahou_log_bound {L : ℕ} (hL : 1 ≤ L)
    (n : Fin L → ℕ) (k : Fin L → ℕ) (ε : Fin L → ℤ)
    (n_min : ℕ) (hn_min3 : 3 ≤ n_min) (hn_ge : ∀ j : Fin L, n_min ≤ n j)
    (hε : ∀ j : Fin L, ε j = 1 ∨ ε j = -1)
    (hstep : ∀ j : Fin L,
      (n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℤ) * 2 ^ (k j) = 3 * (n j : ℤ) + ε j) :
    let A := ∑ j : Fin L, k j
    |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| < (L : ℝ) / (3 * (n_min : ℝ) - 1) ∧
    |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| ≠ 0 ∧
    (n_min : ℝ) < 1 / 3 + (L : ℝ) / (3 * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) := by
  intro A
  have hn3 : ∀ j : Fin L, 3 ≤ n j := fun j => le_trans hn_min3 (hn_ge j)
  obtain ⟨hL_lt_A, hprod⟩ := ppl119_cycle_exact_product_equation hL n k ε hn3 hε hstep
  have hfactor_pos : ∀ j : Fin L, 0 < 1 + (ε j : ℝ) / (3 * (n j : ℝ)) := fun j => by
    have : (3 : ℝ) ≤ n j := by exact_mod_cast hn3 j
    rcases hε j with h | h <;> rw [h]
    · positivity
    · have : 1 / (3 * (n j : ℝ)) ≤ 1 / 9 :=
        div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
      push_cast; rw [neg_div]; linarith
  have hlog_eq := congrArg Real.log hprod
  rw [Real.log_pow, Real.log_mul (by positivity) (Finset.prod_ne_zero_iff.mpr fun j _ => (hfactor_pos j).ne'),
    Real.log_pow, Real.log_prod (fun j _ => (hfactor_pos j).ne')] at hlog_eq
  have hdiff : (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 =
      ∑ j : Fin L, Real.log (1 + (ε j : ℝ) / (3 * (n j : ℝ))) := by
    linarith
  have habs_lt : |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| < (L : ℝ) / (3 * (n_min : ℝ) - 1) := by
    rw [hdiff]
    have htri : |∑ j : Fin L, Real.log (1 + (ε j : ℝ) / (3 * (n j : ℝ)))| ≤
        ∑ j : Fin L, |Real.log (1 + (ε j : ℝ) / (3 * (n j : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
    have hlt_sum : ∑ j : Fin L, |Real.log (1 + (ε j : ℝ) / (3 * (n j : ℝ)))| <
        ∑ _j : Fin L, (1 / (3 * (n_min : ℝ) - 1)) := by
      refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => ?_
      have hnj_ge : (3 : ℝ) ≤ n j := by exact_mod_cast hn3 j
      have hnminR : (3 : ℝ) ≤ n_min := by exact_mod_cast hn_min3
      have hεR : (ε j : ℝ) = 1 ∨ (ε j : ℝ) = -1 := by
        rcases hε j with h | h <;> simp [h]
      have h1 := log_one_add_sub_abs_lt hnj_ge hεR
      have h2 : 1 / (3 * (n j : ℝ) - 1) ≤ 1 / (3 * (n_min : ℝ) - 1) := by
        have hnm : (n_min : ℝ) ≤ n j := by exact_mod_cast hn_ge j
        exact div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith)
      linarith
    have hsum_const : ∑ _j : Fin L, (1 / (3 * (n_min : ℝ) - 1)) = (L : ℝ) / (3 * (n_min : ℝ) - 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
    linarith
  have hne0 : |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| ≠ 0 :=
    abs_sum_log_eq_ne_zero (by omega) hL
  have hpos_err : 0 < |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| :=
    lt_of_le_of_ne (abs_nonneg _) hne0.symm
  refine ⟨habs_lt, hne0, ?_⟩
  have hnmin_pos : 0 < 3 * (n_min : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n_min := by exact_mod_cast hn_min3
    linarith
  have hmul : (3 * (n_min : ℝ) - 1) * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| < L := by
    rwa [lt_div_iff₀ hnmin_pos, mul_comm] at habs_lt
  have h3n_lt : 3 * (n_min : ℝ) - 1 < (L : ℝ) / |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| :=
    (lt_div_iff₀ hpos_err).mpr hmul
  rw [show (L : ℝ) / (3 * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) =
      ((L : ℝ) / |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) / 3 by ring]
  linarith

private lemma two_mul_le_log_one_add_div_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ Real.log ((1 + t) / (1 - t)) := by
  have hlog_div : Real.log ((1 + t) / (1 - t)) = Real.log (1 + t) - Real.log (1 - t) :=
    Real.log_div (by linarith) (by linarith)
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · simp
  · let g : ℝ → ℝ := fun x => Real.log (1 + x) - Real.log (1 - x) - 2 * x
    let g' : ℝ → ℝ := fun x => (1 + x)⁻¹ * 1 - (1 - x)⁻¹ * (-1) - 2
    have hcont : ContinuousOn g (Set.Icc 0 t) := by
      refine (((continuousOn_const.add continuousOn_id).log ?_).sub
        ((continuousOn_const.sub continuousOn_id).log ?_)).sub
        (continuousOn_const.mul continuousOn_id)
      · intro x hx; dsimp; simp only [Set.mem_Icc] at hx; linarith
      · intro x hx; dsimp; simp only [Set.mem_Icc] at hx; linarith
    have hderiv : ∀ x ∈ Set.Ioo 0 t, HasDerivAt g (g' x) x := by
      intro x hx
      simp only [Set.mem_Ioo] at hx
      have d1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) ((1 + x)⁻¹ * 1) x :=
        (Real.hasDerivAt_log (by linarith)).comp x ((hasDerivAt_id x).const_add 1)
      have d2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((1 - x)⁻¹ * (-1)) x :=
        (Real.hasDerivAt_log (by linarith)).comp x
          (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).congr_deriv (by ring))
      have d3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul 2
      exact (d1.sub d2).sub d3
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' ht_pos hcont hderiv
    simp only [Set.mem_Ioo] at hc
    have hgp_nn : 0 ≤ g' c := by
      dsimp [g']
      have h1c : 1 + c ≠ 0 := by linarith
      have h1mc : 1 - c ≠ 0 := by linarith
      have h1mc2 : 1 - c ^ 2 ≠ 0 := by nlinarith
      rw [show (1 + c)⁻¹ * 1 - (1 - c)⁻¹ * (-1) - 2 = 2 * c ^ 2 / ((1 + c) * (1 - c)) by
        field_simp; ring]
      have hden : 0 < (1 + c) * (1 - c) := mul_pos (by linarith) (by linarith)
      positivity
    have hg0 : g 0 = 0 := by simp [g]
    have hdiv_nn : 0 ≤ (g t - g 0) / (t - 0) := hslope ▸ hgp_nn
    have hgt_nn : 0 ≤ g t := by
      rw [hg0, sub_zero, sub_zero] at hdiv_nn
      exact (div_nonneg_iff.mp hdiv_nn).elim (fun h => h.1) (fun h => by linarith)
    dsimp [g] at hgt_nn
    linarith

private lemma log_ratio_ge_of_pow_lt {p q : ℕ} (hpq : 2 ^ p < 3 ^ q) :
    2 * ((3 : ℝ) ^ q - (2 : ℝ) ^ p) / ((3 : ℝ) ^ q + (2 : ℝ) ^ p) ≤
      (q : ℝ) * Real.log 3 - (p : ℝ) * Real.log 2 := by
  have hpqR : (2 : ℝ) ^ p < (3 : ℝ) ^ q := by exact_mod_cast hpq
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  let t : ℝ := ((3 : ℝ) ^ q - (2 : ℝ) ^ p) / ((3 : ℝ) ^ q + (2 : ℝ) ^ p)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]; rw [div_lt_one (by positivity)]; linarith
  have hid : (1 + t) / (1 - t) = (3 : ℝ) ^ q / (2 : ℝ) ^ p := by
    dsimp [t]; field_simp; ring
  have hle := two_mul_le_log_one_add_div_one_sub ht0 ht1
  rw [hid, Real.log_div h3pos.ne' h2pos.ne', Real.log_pow, Real.log_pow] at hle
  simpa [t, mul_div_assoc'] using hle

private lemma log_ratio_ge_of_pow_gt {p q : ℕ} (hpq : 3 ^ q < 2 ^ p) :
    2 * ((2 : ℝ) ^ p - (3 : ℝ) ^ q) / ((2 : ℝ) ^ p + (3 : ℝ) ^ q) ≤
      (p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3 := by
  have hpqR : (3 : ℝ) ^ q < (2 : ℝ) ^ p := by exact_mod_cast hpq
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  let t : ℝ := ((2 : ℝ) ^ p - (3 : ℝ) ^ q) / ((2 : ℝ) ^ p + (3 : ℝ) ^ q)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]; rw [div_lt_one (by positivity)]; linarith
  have hid : (1 + t) / (1 - t) = (2 : ℝ) ^ p / (3 : ℝ) ^ q := by
    dsimp [t]; field_simp; ring
  have hle := two_mul_le_log_one_add_div_one_sub ht0 ht1
  rw [hid, Real.log_div h2pos.ne' h3pos.ne', Real.log_pow, Real.log_pow] at hle
  simpa [t, mul_div_assoc'] using hle

/-- Theorem 2d (General Farey-Bracket Cycle Exclusion Bound):
For ANY convergent bracket `(p₁, q₁), (p₂, q₂)` with `2 ^ p₁ < 3 ^ q₁`, `3 ^ q₂ < 2 ^ p₂`, and
`p₂ * q₁ - p₁ * q₂ = 1`, every `3n ± 1` cycle of length `1 ≤ L < q₁ + q₂` with `3 ≤ n_min ≤ n j`
satisfies
`n_min < 1 / 3 + max (q₁ * (3^q₁ + 2^p₁) / (6 * (3^q₁ - 2^p₁))) (q₂ * (2^p₂ + 3^q₂) / (6 * (2^p₂ - 3^q₂)))`. -/
theorem ppl119_eliahou_farey_bracket {p₁ q₁ p₂ q₂ L : ℕ}
    (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂) (hL : 1 ≤ L) (hL_lt : L < q₁ + q₂)
    (hlow : 2 ^ p₁ < 3 ^ q₁) (hhigh : 3 ^ q₂ < 2 ^ p₂)
    (hdet : (p₂ : ℤ) * q₁ - (p₁ : ℤ) * q₂ = 1)
    (n : Fin L → ℕ) (k : Fin L → ℕ) (ε : Fin L → ℤ)
    (n_min : ℕ) (hn_min3 : 3 ≤ n_min) (hn_ge : ∀ j : Fin L, n_min ≤ n j)
    (hε : ∀ j : Fin L, ε j = 1 ∨ ε j = -1)
    (hstep : ∀ j : Fin L,
      (n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℤ) * 2 ^ (k j) = 3 * (n j : ℤ) + ε j) :
    (n_min : ℝ) < 1 / 3 + max
      ((q₁ : ℝ) * ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁) / (6 * ((3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁)))
      ((q₂ : ℝ) * ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂) / (6 * ((2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂))) := by
  set A := ∑ j : Fin L, k j
  obtain ⟨_, hne0, hn_bd⟩ := ppl119_cycle_eliahou_log_bound hL n k ε n_min hn_min3 hn_ge hε hstep
  have hcase : (A : ℤ) * q₁ ≤ (p₁ : ℤ) * L ∨ (p₂ : ℤ) * L ≤ (A : ℤ) * q₂ := by
    by_contra hboth
    push Not at hboth
    have ha : 1 ≤ (A : ℤ) * q₁ - (p₁ : ℤ) * L := by omega
    have hb : 1 ≤ (p₂ : ℤ) * L - (A : ℤ) * q₂ := by omega
    have hq₁p : (0 : ℤ) < q₁ := by omega
    have hq₂p : (0 : ℤ) < q₂ := by omega
    have hcomb : (q₂ : ℤ) * ((A : ℤ) * q₁ - (p₁ : ℤ) * L) +
        (q₁ : ℤ) * ((p₂ : ℤ) * L - (A : ℤ) * q₂) = L := by
      calc (q₂ : ℤ) * ((A : ℤ) * q₁ - (p₁ : ℤ) * L) +
            (q₁ : ℤ) * ((p₂ : ℤ) * L - (A : ℤ) * q₂)
          = (L : ℤ) * ((p₂ : ℤ) * q₁ - (p₁ : ℤ) * q₂) := by ring
        _ = L := by rw [hdet, mul_one]
    nlinarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq₁R : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq₂R : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rcases hcase with hle | hge
  · have h_err_ge : ((L : ℝ) / q₁) * ((q₁ : ℝ) * Real.log 3 - (p₁ : ℝ) * Real.log 2) ≤
        |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| := by
      have hdiff_nn : 0 ≤ ((p₁ : ℝ) * L - (A : ℝ) * q₁) := by
        have : (A : ℝ) * q₁ ≤ (p₁ : ℝ) * L := by exact_mod_cast hle
        linarith
      have hraw : ((L : ℝ) / q₁) * ((q₁ : ℝ) * Real.log 3 - (p₁ : ℝ) * Real.log 2) ≤
          (L : ℝ) * Real.log 3 - (A : ℝ) * Real.log 2 := by
        have hid : (L : ℝ) * Real.log 3 - (A : ℝ) * Real.log 2 =
            ((L : ℝ) / q₁) * ((q₁ : ℝ) * Real.log 3 - (p₁ : ℝ) * Real.log 2) +
            (((p₁ : ℝ) * L - (A : ℝ) * q₁) / q₁) * Real.log 2 := by
          field_simp; ring
        rw [hid]
        have : 0 ≤ (((p₁ : ℝ) * L - (A : ℝ) * q₁) / q₁) * Real.log 2 := by positivity
        linarith
      have hneg : (L : ℝ) * Real.log 3 - (A : ℝ) * Real.log 2 =
          -((A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3) := by ring
      rw [hneg] at hraw
      exact le_trans hraw (neg_le_abs _)
    have hgap := log_ratio_ge_of_pow_lt hlow
    have hnum_pos : 0 < (3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁ := by
      have : (2 : ℝ) ^ p₁ < (3 : ℝ) ^ q₁ := by exact_mod_cast hlow
      linarith
    have h_low_pos : 0 < 2 * ((3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁) / ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁) := by
      positivity
    have h_comb : ((L : ℝ) / q₁) *
        (2 * ((3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁) / ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁)) ≤
        |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| :=
      le_trans (mul_le_mul_of_nonneg_left hgap (by positivity)) h_err_ge
    have hdiv_le : (L : ℝ) / (3 * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) ≤
        (q₁ : ℝ) * ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁) / (6 * ((3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁)) := by
      have habs_pos : 0 < |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| :=
        lt_of_le_of_ne (abs_nonneg _) hne0.symm
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc (L : ℝ) * (6 * ((3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁))
          = (3 * q₁) * (((L : ℝ) / q₁) *
              (2 * ((3 : ℝ) ^ q₁ - (2 : ℝ) ^ p₁) / ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁))) *
              ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁) := by field_simp; ring
        _ ≤ (3 * q₁) * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| *
              ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁) := by
            have h1 := mul_le_mul_of_nonneg_left h_comb (by positivity : 0 ≤ 3 * (q₁ : ℝ))
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (q₁ : ℝ) * ((3 : ℝ) ^ q₁ + (2 : ℝ) ^ p₁) *
              (3 * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) := by ring
    exact lt_of_lt_of_le hn_bd (add_le_add_right (le_trans hdiv_le (le_max_left _ _)) _)
  · have h_err_ge : ((L : ℝ) / q₂) * ((p₂ : ℝ) * Real.log 2 - (q₂ : ℝ) * Real.log 3) ≤
        |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| := by
      have hdiff_nn : 0 ≤ ((A : ℝ) * q₂ - (p₂ : ℝ) * L) := by
        have : (p₂ : ℝ) * L ≤ (A : ℝ) * q₂ := by exact_mod_cast hge
        linarith
      have hraw : ((L : ℝ) / q₂) * ((p₂ : ℝ) * Real.log 2 - (q₂ : ℝ) * Real.log 3) ≤
          (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 := by
        have hid : (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 =
            ((L : ℝ) / q₂) * ((p₂ : ℝ) * Real.log 2 - (q₂ : ℝ) * Real.log 3) +
            (((A : ℝ) * q₂ - (p₂ : ℝ) * L) / q₂) * Real.log 2 := by
          field_simp; ring
        rw [hid]
        have : 0 ≤ (((A : ℝ) * q₂ - (p₂ : ℝ) * L) / q₂) * Real.log 2 := by positivity
        linarith
      exact le_trans hraw (le_abs_self _)
    have hgap := log_ratio_ge_of_pow_gt hhigh
    have hnum_pos : 0 < (2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂ := by
      have : (3 : ℝ) ^ q₂ < (2 : ℝ) ^ p₂ := by exact_mod_cast hhigh
      linarith
    have h_low_pos : 0 < 2 * ((2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂) / ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂) := by
      positivity
    have h_comb : ((L : ℝ) / q₂) *
        (2 * ((2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂) / ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂)) ≤
        |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| :=
      le_trans (mul_le_mul_of_nonneg_left hgap (by positivity)) h_err_ge
    have hdiv_le : (L : ℝ) / (3 * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) ≤
        (q₂ : ℝ) * ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂) / (6 * ((2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂)) := by
      have habs_pos : 0 < |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| :=
        lt_of_le_of_ne (abs_nonneg _) hne0.symm
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc (L : ℝ) * (6 * ((2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂))
          = (3 * q₂) * (((L : ℝ) / q₂) *
              (2 * ((2 : ℝ) ^ p₂ - (3 : ℝ) ^ q₂) / ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂))) *
              ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂) := by field_simp; ring
        _ ≤ (3 * q₂) * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3| *
              ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂) := by
            have h1 := mul_le_mul_of_nonneg_left h_comb (by positivity : 0 ≤ 3 * (q₂ : ℝ))
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (q₂ : ℝ) * ((2 : ℝ) ^ p₂ + (3 : ℝ) ^ q₂) *
              (3 * |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|) := by ring
    exact lt_of_lt_of_le hn_bd (add_le_add_right (le_trans hdiv_le (le_max_right _ _)) _)

/-- Theorem 2e (Explicit Short-Cycle Exclusions for `L ≤ 26`, `L ≤ 664`, `L ≤ 970`):
Every directed `3n ± 1` cycle `n : Fin L → ℕ` (`1 ≤ L`, `3 ≤ n j`, `ε j ∈ {1, -1}`) satisfies:
1. If `L ≤ 26`, then `∃ j : Fin L, n j ≤ 295` (no cycle of length `≤ 26` exists above `295`);
2. If `L ≤ 664`, then `∃ j : Fin L, n j ≤ 112269`;
3. If `L ≤ 970`, then `∃ j : Fin L, n j ≤ 5077796`. -/
theorem ppl119_short_cycle_min_bounds {L : ℕ} (hL : 1 ≤ L)
    (n : Fin L → ℕ) (k : Fin L → ℕ) (ε : Fin L → ℤ)
    (hn3 : ∀ j : Fin L, 3 ≤ n j)
    (hε : ∀ j : Fin L, ε j = 1 ∨ ε j = -1)
    (hstep : ∀ j : Fin L,
      (n ⟨(j.1 + 1) % L, Nat.mod_lt _ (by omega)⟩ : ℤ) * 2 ^ (k j) = 3 * (n j : ℤ) + ε j) :
    (L ≤ 26 → ∃ j : Fin L, n j ≤ 295) ∧
    (L ≤ 664 → ∃ j : Fin L, n j ≤ 112269) ∧
    (L ≤ 970 → ∃ j : Fin L, n j ≤ 5077796) := by
  let S := Finset.univ.image n
  have hSne : S.Nonempty := ⟨n ⟨0, hL⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  set n_min := S.min' hSne
  have hn_min_mem : n_min ∈ S := Finset.min'_mem S hSne
  obtain ⟨j₀, _, hj₀⟩ := Finset.mem_image.mp hn_min_mem
  have hn_ge : ∀ j : Fin L, n_min ≤ n j := fun j =>
    Finset.min'_le S (n j) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hn_min3 : 3 ≤ n_min := by rw [← hj₀]; exact hn3 j₀
  refine ⟨?_, ?_, ?_⟩
  · intro hL26
    have hbd := ppl119_eliahou_farey_bracket (p₁ := 19) (q₁ := 12) (p₂ := 27) (q₂ := 17)
      (by norm_num) (by norm_num) hL (by omega) (by norm_num) (by norm_num) (by norm_num)
      n k ε n_min hn_min3 hn_ge hε hstep
    have hmax : (1 / 3 : ℝ) + max
        ((12 : ℝ) * ((3 : ℝ) ^ 12 + (2 : ℝ) ^ 19) / (6 * ((3 : ℝ) ^ 12 - (2 : ℝ) ^ 19)))
        ((17 : ℝ) * ((2 : ℝ) ^ 27 + (3 : ℝ) ^ 17) / (6 * ((2 : ℝ) ^ 27 - (3 : ℝ) ^ 17))) ≤
        296 := by norm_num
    have hn_lt : (n_min : ℝ) < 296 := lt_of_lt_of_le hbd hmax
    have hn_nat : n_min < 296 := by exact_mod_cast hn_lt
    exact ⟨j₀, by omega⟩
  · intro hL664
    have hlowN : 2 ^ 569 < 3 ^ 359 := by
      rw [show (569 : ℕ) = 9 + 140 * 4 by norm_num, pow_add, pow_mul,
        show (359 : ℕ) = 5 + 177 * 2 by norm_num, pow_add, pow_mul]
      norm_num
    have hhighN : 3 ^ 306 < 2 ^ 485 := by
      rw [show (306 : ℕ) = 153 * 2 by norm_num, pow_mul,
        show (485 : ℕ) = 5 + 160 * 3 by norm_num, pow_add, pow_mul]
      norm_num
    have hbd := ppl119_eliahou_farey_bracket (p₁ := 569) (q₁ := 359) (p₂ := 485) (q₂ := 306)
      (by norm_num) (by norm_num) hL (by omega) hlowN hhighN (by norm_num)
      n k ε n_min hn_min3 hn_ge hε hstep
    have hmax : (1 / 3 : ℝ) + max
        ((359 : ℝ) * ((3 : ℝ) ^ 359 + (2 : ℝ) ^ 569) / (6 * ((3 : ℝ) ^ 359 - (2 : ℝ) ^ 569)))
        ((306 : ℝ) * ((2 : ℝ) ^ 485 + (3 : ℝ) ^ 306) / (6 * ((2 : ℝ) ^ 485 - (3 : ℝ) ^ 306))) ≤
        112270 := by
      rw [show (359 : ℕ) = 5 + 177 * 2 by norm_num, pow_add, pow_mul,
        show (569 : ℕ) = 9 + 140 * 4 by norm_num, pow_add, pow_mul,
        show (306 : ℕ) = 153 * 2 by norm_num, pow_mul,
        show (485 : ℕ) = 5 + 160 * 3 by norm_num, pow_add, pow_mul]
      norm_num
    have hn_lt : (n_min : ℝ) < 112270 := lt_of_lt_of_le hbd hmax
    have hn_nat : n_min < 112270 := by exact_mod_cast hn_lt
    exact ⟨j₀, by omega⟩
  · intro hL970
    have hlowN : 2 ^ 1054 < 3 ^ 665 := by
      rw [show (1054 : ℕ) = 4 + 210 * 5 by norm_num, pow_add, pow_mul,
        show (665 : ℕ) = 5 + 165 * 4 by norm_num, pow_add, pow_mul]
      norm_num
    have hhighN : 3 ^ 306 < 2 ^ 485 := by
      rw [show (306 : ℕ) = 153 * 2 by norm_num, pow_mul,
        show (485 : ℕ) = 5 + 160 * 3 by norm_num, pow_add, pow_mul]
      norm_num
    have hbd := ppl119_eliahou_farey_bracket (p₁ := 1054) (q₁ := 665) (p₂ := 485) (q₂ := 306)
      (by norm_num) (by norm_num) hL (by omega) hlowN hhighN (by norm_num)
      n k ε n_min hn_min3 hn_ge hε hstep
    have hmax : (1 / 3 : ℝ) + max
        ((665 : ℝ) * ((3 : ℝ) ^ 665 + (2 : ℝ) ^ 1054) / (6 * ((3 : ℝ) ^ 665 - (2 : ℝ) ^ 1054)))
        ((306 : ℝ) * ((2 : ℝ) ^ 485 + (3 : ℝ) ^ 306) / (6 * ((2 : ℝ) ^ 485 - (3 : ℝ) ^ 306))) ≤
        5077797 := by
      rw [show (665 : ℕ) = 5 + 165 * 4 by norm_num, pow_add, pow_mul,
        show (1054 : ℕ) = 4 + 210 * 5 by norm_num, pow_add, pow_mul,
        show (306 : ℕ) = 153 * 2 by norm_num, pow_mul,
        show (485 : ℕ) = 5 + 160 * 3 by norm_num, pow_add, pow_mul]
      norm_num
    have hn_lt : (n_min : ℝ) < 5077797 := lt_of_lt_of_le hbd hmax
    have hn_nat : n_min < 5077797 := by exact_mod_cast hn_lt
    exact ⟨j₀, by omega⟩

end EliahouCycleObstruction

section WaveRotation

/-- Theorem 3 (Irrational `log₂ 3` Rotation, Uniform `O(1/n)` Step Shift, & `12`-Step Drift):
1. `Real.log 3 / Real.log 2` (`= Real.logb 2 3`) is irrational.
2. For every `n ≥ 3`, `k ≥ 1`, `s ∈ {1, -1}`, and `(m : ℤ) * 2 ^ k = 3 * (n : ℤ) + s`, both
   `U(n)` (`k = 1`) and `D(n)` (`k ≥ 2`) shift `log₂` by `log₂ 3` up to error
   `< 1 / ((3n - 1) * ln 2)`.
3. Over `12` steps, `0 < 12 * Real.logb 2 3 - 19 < 1 / 50` (the `+0.01955` rotation driving the
   6-wave bands). -/
theorem ppl119_log2_step_shift_and_irrationality :
    Irrational (Real.log 3 / Real.log 2) ∧
    (∀ n m k : ℕ, 3 ≤ n → 1 ≤ m → ∀ s : ℤ, (s = 1 ∨ s = -1) →
      (m : ℤ) * 2 ^ k = 3 * (n : ℤ) + s →
      |Real.logb 2 m + k - (Real.logb 2 n + Real.logb 2 3)| <
        1 / ((3 * (n : ℝ) - 1) * Real.log 2)) ∧
    (0 < 12 * Real.logb 2 3 - 19 ∧ 12 * Real.logb 2 3 - 19 < 1 / 50) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [irrational_iff_ne_rational]
    intro a b hb hrat
    have hpos : 0 < Real.log 3 / Real.log 2 := div_pos (Real.log_pos (by norm_num)) hlog2_pos
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have ha_ne0 : a ≠ 0 := by
      intro ha0; subst ha0; rw [Int.cast_zero, zero_div] at hrat; linarith
    have hab_eq : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 3 := by
      have h1 : Real.log 3 / Real.log 2 = (a : ℝ) / b := hrat
      rw [div_eq_div_iff hlog2_pos.ne' hb0] at h1
      linarith
    have hnat_eq : (a.natAbs : ℝ) * Real.log 2 = (b.natAbs : ℝ) * Real.log 3 := by
      have hab_abs := congrArg abs hab_eq
      have hca : |(a : ℝ)| = (a.natAbs : ℝ) := by
        rcases Int.natAbs_eq a with ha | ha
        · conv_lhs => rw [ha]
          simp [abs_of_nonneg]
        · conv_lhs => rw [ha]
          simp [abs_of_nonneg]
      have hcb : |(b : ℝ)| = (b.natAbs : ℝ) := by
        rcases Int.natAbs_eq b with hb' | hb'
        · conv_lhs => rw [hb']
          simp [abs_of_nonneg]
        · conv_lhs => rw [hb']
          simp [abs_of_nonneg]
      rw [abs_mul, abs_mul, abs_of_pos hlog2_pos, abs_of_pos (Real.log_pos (by norm_num)),
        hca, hcb] at hab_abs
      exact hab_abs
    have hzero : |(a.natAbs : ℝ) * Real.log 2 - (b.natAbs : ℝ) * Real.log 3| = 0 := by
      rw [hnat_eq, sub_self, abs_zero]
    exact abs_sum_log_eq_ne_zero (Int.natAbs_pos.mpr ha_ne0) (Int.natAbs_pos.mpr hb) hzero
  · intro n m k hn3 hm1 s hs heq
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hfactor_pos : 0 < 1 + (s : ℝ) / (3 * (n : ℝ)) := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      rcases hs with rfl | rfl
      · positivity
      · have : 1 / (3 * (n : ℝ)) ≤ 1 / 9 :=
          div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
        push_cast; rw [neg_div]; linarith
    have heqR : (m : ℝ) * (2 : ℝ) ^ k = (3 * (n : ℝ)) * (1 + (s : ℝ) / (3 * (n : ℝ))) := by
      have hZ : (m : ℝ) * (2 : ℝ) ^ k = 3 * (n : ℝ) + (s : ℝ) := by exact_mod_cast heq
      field_simp
      linarith
    have hlog := congrArg Real.log heqR
    rw [Real.log_mul hm_pos.ne' (by positivity), Real.log_pow,
      Real.log_mul (by positivity) hfactor_pos.ne', Real.log_mul (by norm_num) hn_pos.ne'] at hlog
    have hid : Real.logb 2 m + k - (Real.logb 2 n + Real.logb 2 3) =
        Real.log (1 + (s : ℝ) / (3 * (n : ℝ))) / Real.log 2 := by
      simp only [Real.logb]
      rw [show Real.log m / Real.log 2 + k - (Real.log n / Real.log 2 + Real.log 3 / Real.log 2) =
          (Real.log m + k * Real.log 2 - (Real.log 3 + Real.log n)) / Real.log 2 by
        field_simp; ring, hlog]
      ring
    rw [hid, abs_div, abs_of_pos hlog2_pos]
    have hsR : (s : ℝ) = 1 ∨ (s : ℝ) = -1 := by
      rcases hs with rfl | rfl
      · exact Or.inl (by norm_num)
      · exact Or.inr (by norm_num)
    have h_abs := log_one_add_sub_abs_lt (by exact_mod_cast hn3 : (3 : ℝ) ≤ (n : ℝ)) hsR
    have h3n1 : 3 * (n : ℝ) - 1 ≠ 0 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      linarith
    calc |Real.log (1 + (s : ℝ) / (3 * (n : ℝ)))| / Real.log 2
        < (1 / (3 * (n : ℝ) - 1)) / Real.log 2 := div_lt_div_of_pos_right h_abs hlog2_pos
      _ = 1 / ((3 * (n : ℝ) - 1) * Real.log 2) := by field_simp
  · have h_num_pos : 0 < 12 * Real.log 3 - 19 * Real.log 2 := by
      have hpow : (2 : ℕ) ^ 19 < 3 ^ 12 := by norm_num
      have hgap := log_ratio_ge_of_pow_lt hpow
      have hnum_gt : (0 : ℝ) < 2 * ((3 : ℝ) ^ 12 - (2 : ℝ) ^ 19) / ((3 : ℝ) ^ 12 + (2 : ℝ) ^ 19) := by
        norm_num
      linarith
    have h_num_le : 12 * Real.log 3 - 19 * Real.log 2 ≤ 7153 / 524288 := by
      have hid : 12 * Real.log 3 - 19 * Real.log 2 = Real.log ((531441 : ℝ) / 524288) := by
        rw [Real.log_div (by norm_num) (by norm_num),
          show (531441 : ℝ) = 3 ^ (12 : ℕ) by norm_num,
          show (524288 : ℝ) = 2 ^ (19 : ℕ) by norm_num,
          Real.log_pow, Real.log_pow]
        norm_num
      rw [hid]
      have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 531441 / 524288)
      linarith
    have hlog2_lb : (24 / 35 : ℝ) ≤ Real.log 2 := by
      have h1 := two_mul_le_log_one_add_div_one_sub (t := 1 / 7) (by norm_num) (by norm_num)
      have h2 := two_mul_le_log_one_add_div_one_sub (t := 1 / 5) (by norm_num) (by norm_num)
      have hr1 : (1 + (1 / 7 : ℝ)) / (1 - 1 / 7) = 4 / 3 := by norm_num
      have hr2 : (1 + (1 / 5 : ℝ)) / (1 - 1 / 5) = 3 / 2 := by norm_num
      rw [hr1] at h1
      rw [hr2] at h2
      have hprod2 : Real.log 2 = Real.log (4 / 3) + Real.log (3 / 2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hid12 : 12 * Real.logb 2 3 - 19 = (12 * Real.log 3 - 19 * Real.log 2) / Real.log 2 := by
      simp only [Real.logb]
      field_simp
    rw [hid12]
    refine ⟨div_pos h_num_pos hlog2_pos, ?_⟩
    calc (12 * Real.log 3 - 19 * Real.log 2) / Real.log 2
        ≤ (7153 / 524288) / (24 / 35) :=
          div_le_div₀ (by norm_num) h_num_le (by norm_num) hlog2_lb
      _ < 1 / 50 := by norm_num

end WaveRotation

section CriticalPercolation

/-- Theorem 4a (Exact Downward Branching Generating Function Identity):
For every Chernoff tilt parameter `γ > -1`, the downward `v₂ ≥ 2` transition weights
`2^{-(k-1)} (3 / 2^k)^γ` sum exactly to `(1/2 * (3/4)^γ) / (1 - 2^{-(1 + γ)})`. -/
theorem ppl119_branching_generating_function_identity {γ : ℝ} (hγ : -1 < γ) :
    HasSum (fun t : ℕ => (2 : ℝ)⁻¹ ^ (t + 1) * (3 / (2 : ℝ) ^ (t + 2)) ^ γ)
      ((1 / 2 * (3 / 4 : ℝ) ^ γ) / (1 - (2 : ℝ) ^ (-(1 + γ)))) := by
  let r : ℝ := (2 : ℝ) ^ (-(1 + γ))
  have hr_nn : 0 ≤ r := by dsimp [r]; positivity
  have hr_lt1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : HasSum (fun t : ℕ => r ^ t) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr_nn hr_lt1
  have hscaled := hgeom.mul_left (1 / 2 * (3 / 4 : ℝ) ^ γ)
  have hterm : ∀ t : ℕ,
      (1 / 2 * (3 / 4 : ℝ) ^ γ) * r ^ t =
        (2 : ℝ)⁻¹ ^ (t + 1) * (3 / (2 : ℝ) ^ (t + 2)) ^ γ := by
    intro t
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have h3pos : (0 : ℝ) < 3 := by norm_num
    have hpow_div : (3 / (2 : ℝ) ^ (t + 2)) ^ γ =
        (3 / 4 : ℝ) ^ γ * ((2 : ℝ) ^ (-γ)) ^ t := by
      rw [show (3 / (2 : ℝ) ^ (t + 2) : ℝ) = (3 / 4) * (2⁻¹ : ℝ) ^ t by
        rw [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, inv_pow]; ring]
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      congr 1
      rw [inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_natCast (2 : ℝ) t,
        ← Real.rpow_mul h2pos.le, ← Real.rpow_neg h2pos.le]
      symm
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-γ)) t, ← Real.rpow_mul (by positivity)]
      congr 1; ring
    have hpow_r : r ^ t = (2 : ℝ)⁻¹ ^ t * ((2 : ℝ) ^ (-γ)) ^ t := by
      dsimp [r]
      rw [← mul_pow]
      congr 1
      rw [← Real.rpow_neg_one, ← Real.rpow_add h2pos]
      ring_nf
    rw [hpow_div, hpow_r, pow_succ']
    ring
  simp_rw [hterm] at hscaled
  simpa [r, div_eq_mul_inv] using hscaled

/-- Theorem 4b (Subcriticality Bound Below `p_{W,crit}` at `γ = 1/2`):
At `γ = 1/2`, the exact Biggins Laplace transform
`Φ(1/2) = (3/2)^(1/2) + (1/2 * (3/4)^(1/2)) / (1 - 2^{-(1 + 1/2)})`
satisfies `Φ(1/2) < 1895 / 1000`, rigorously proving `p * Φ(1/2) < 1` (subcriticality) for
every survival/win density `0 ≤ p ≤ 527 / 1000` (above the empirical `0.513–0.517` 6-wave band). -/
theorem ppl119_critical_percolation_subcritical_bound :
    let Φ_half : ℝ := (3 / 2 : ℝ) ^ (1 / 2 : ℝ) +
      (1 / 2 * (3 / 4 : ℝ) ^ (1 / 2 : ℝ)) / (1 - (2 : ℝ) ^ (-(1 + (1 / 2 : ℝ))))
    Φ_half < 1895 / 1000 ∧ ∀ p : ℝ, 0 ≤ p → p ≤ 527 / 1000 → p * Φ_half < 1 := by
  intro Φ_half
  have hr32 : (3 / 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 6 / 2 := by
    rw [← Real.sqrt_eq_rpow]
    have : Real.sqrt (3 / 2 : ℝ) = Real.sqrt (6 / 4) := by norm_num
    rw [this, Real.sqrt_div (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hr34 : (3 / 4 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 3 / 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have hr2m : (2 : ℝ) ^ (-(1 + (1 / 2 : ℝ))) = 1 / (2 * Real.sqrt 2) := by
    rw [show -(1 + (1 / 2 : ℝ)) = -1 + -(1 / 2 : ℝ) by ring, Real.rpow_add (by norm_num),
      Real.rpow_neg_one, Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    ring
  have hsqrt6 : Real.sqrt 6 < 24495 / 10000 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
    have hn : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
    nlinarith
  have hsqrt3 : Real.sqrt 3 < 17321 / 10000 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith
  have hsqrt2 : 1414 / 1000 < Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    nlinarith
  have hden_lb : (1 - 1 / (2 * (1414 / 1000 : ℝ))) ≤ 1 - 1 / (2 * Real.sqrt 2) := by
    have : 1 / (2 * Real.sqrt 2) ≤ 1 / (2 * (1414 / 1000 : ℝ)) :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith)
    linarith
  have hterm1 : (3 / 2 : ℝ) ^ (1 / 2 : ℝ) < (24495 / 10000) / 2 := by rw [hr32]; linarith
  have hterm2_num : 1 / 2 * (3 / 4 : ℝ) ^ (1 / 2 : ℝ) < 1 / 2 * ((17321 / 10000) / 2) := by
    rw [hr34]; linarith
  have hterm2_num_nn : 0 ≤ 1 / 2 * (3 / 4 : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have hterm2 : (1 / 2 * (3 / 4 : ℝ) ^ (1 / 2 : ℝ)) / (1 - (2 : ℝ) ^ (-(1 + (1 / 2 : ℝ)))) <
      (1 / 2 * ((17321 / 10000) / 2)) / (1 - 1 / (2 * (1414 / 1000 : ℝ))) := by
    rw [hr2m]
    calc (1 / 2 * (3 / 4 : ℝ) ^ (1 / 2 : ℝ)) / (1 - 1 / (2 * Real.sqrt 2))
        ≤ (1 / 2 * (3 / 4 : ℝ) ^ (1 / 2 : ℝ)) / (1 - 1 / (2 * (1414 / 1000 : ℝ))) :=
          div_le_div_of_nonneg_left hterm2_num_nn (by norm_num) hden_lb
      _ < (1 / 2 * ((17321 / 10000) / 2)) / (1 - 1 / (2 * (1414 / 1000 : ℝ))) :=
          div_lt_div_of_pos_right hterm2_num (by norm_num)
  have hphi_lt : Φ_half < 1895 / 1000 := by
    dsimp [Φ_half]
    linarith
  refine ⟨hphi_lt, fun p hp0 hp => ?_⟩
  have hphi_pos : 0 < Φ_half := by
    dsimp [Φ_half]
    have hden_pos : 0 < 1 - (2 : ℝ) ^ (-(1 + (1 / 2 : ℝ))) := by
      rw [hr2m]; linarith [hden_lb]
    positivity
  calc p * Φ_half ≤ (527 / 1000) * Φ_half := mul_le_mul_of_nonneg_right hp hphi_pos.le
    _ < (527 / 1000) * (1895 / 1000) := mul_lt_mul_of_pos_left hphi_lt (by norm_num)
    _ < 1 := by norm_num

end CriticalPercolation

end PPL119
