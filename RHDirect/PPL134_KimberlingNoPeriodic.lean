import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# PPL 134 — Kimberling's Expulsion Sequence (`A007063`): No Eventually Periodic Sign Itinerary

**Status (Honest Labeling):**
This file formalizes a **verified original partial / structural theorem** discovered during the
PPL 134 (Kimberling #2, OEIS `A007063`) campaign. It does **NOT** resolve full surjectivity of
Kimberling's expulsion sequence `A007063` (which remains open, behind a non-periodic
Collatz/Mahler-class dynamical barrier).

## Mathematical Summary

In Kimberling's expulsion array (`A035486`), an integer `m ≥ 1` starts at stage `t = 1` in column
`p = m`. At stage `t ≥ 1`, the diagonal entry at column `p = t` is expelled (`A007063(t)`).
Otherwise its column updates to:
- `2 * (t - p)` if `1 ≤ p < t`,
- `2 * (p - t) - 1` if `t < p < 2 * t`,
- `p - 1` if `p ≥ 2 * t`.

Every `m ≥ 2` deterministically drifts into the forward-invariant **active zone** `1 ≤ p ≤ 2t - 1`
at stage `t₀ = ⌊(m + 1) / 3⌋ + 1` with `p₀ = m - (t₀ - 1)`.

For any never-expelled active-zone orbit `(t₀ + n, p_n)` (`1 ≤ p₀ ≤ 2t₀ - 1`, `∀ n, p_n ≠ t₀ + n`),
let `s_n ∈ {-1, +1}` be the step sign (`-1` if `p_n < t₀ + n`, `+1` if `p_n > t₀ + n`),
`σ_{n+1} = ∏_{j=0}^n s_j ∈ {-1, +1}` be the cumulative sign product, and
`b'_n = (1 + σ_{n+1}) / 2 ∈ {0, 1}` be the cumulative sign bit.

We prove unconditionally (zero `sorry`, zero extra axioms):
1. **Exact Binary Series Identity (`kimberling_never_expelled_series_eq`):**
   ```
   2 * p₀ + 5 = (4 * t₀ + 3) * ∑' n, b'_n / 2^(n+1) + 4 * ∑' n, (n + 1) * b'_n / 2^(n+1).
   ```
2. **Main Structural Theorem (`kimberling_no_eventually_periodic_itinerary`):**
   No never-expelled active-zone orbit in Kimberling's expulsion map can have an eventually
   periodic sign itinerary (`p_n > t₀ + n`). The proof reduces an eventually periodic itinerary
   of minimal period `P ≥ 1` to a periodic tent-map orbit `x_k = a_k / q ∈ (0, 2) \ {1}` with
   odd denominator `q ≥ 3`, even numerators `a_k` coprime to `q`, giving both `P ≤ φ(q) < q`
   and `q ∣ P`, a contradiction.
3. **Full-Orbit Corollary (`kimberlingFullOrbit_no_eventually_periodic_itinerary`):**
   The same impossibility holds for the full OEIS `A007063` forward orbit of every `m ≥ 1`
   starting at `(t = 1, p = m)`.
-/

namespace PPL134_KimberlingNoPeriodic

open scoped BigOperators
open Finset Filter Topology

/-! ## Section 1: Kimberling Expulsion Dynamics & OEIS `A007063` Verification -/

section Dynamics

/-- Active-zone forward map of Kimberling's expulsion array at stage `t` and column `p`:
- if `p < t`, moves to `2 * (t - p)`;
- if `p > t` (with `p ≤ 2t - 1`), moves to `2 * (p - t) - 1`. -/
def kimberlingActiveStep (t p : ℕ) : ℕ :=
  if p < t then 2 * (t - p) else 2 * (p - t) - 1

/-- Active-zone column orbit `p_n` at stage `t₀ + n`, starting from `(t₀, p₀)`. -/
def kimberlingOrbit (t₀ p₀ : ℕ) : ℕ → ℕ
  | 0 => p₀
  | n + 1 => kimberlingActiveStep (t₀ + n) (kimberlingOrbit t₀ p₀ n)

/-- Full forward map of Kimberling's expulsion array (`A035486` / `A007063`) at stage `t ≥ 1`. -/
def kimberlingFullStep (t p : ℕ) : ℕ :=
  if p < t then 2 * (t - p)
  else if p < 2 * t then 2 * (p - t) - 1
  else p - 1

/-- Full column orbit of integer `m` in Kimberling's expulsion array:
at index `n`, the stage is `t = n + 1` (with `kimberlingFullOrbit m 0 = m` at stage `t = 1`).
Expulsion occurs at stage `t = n + 1` when `kimberlingFullOrbit m n = n + 1`. -/
def kimberlingFullOrbit (m : ℕ) : ℕ → ℕ
  | 0 => m
  | n + 1 => kimberlingFullStep (n + 1) (kimberlingFullOrbit m n)

/-! ### Exact OEIS `A007063` sanity checks (`1, 3, 5, 4, ...` and `m = 2` at `t = 25`) -/

lemma a007063_m1_expelled_at_1 : kimberlingFullOrbit 1 0 = 1 := by decide
lemma a007063_m3_expelled_at_2 :
    kimberlingFullOrbit 3 0 ≠ 1 ∧ kimberlingFullOrbit 3 1 = 2 := by decide
lemma a007063_m5_expelled_at_3 :
    kimberlingFullOrbit 5 0 ≠ 1 ∧ kimberlingFullOrbit 5 1 ≠ 2 ∧
    kimberlingFullOrbit 5 2 = 3 := by decide
lemma a007063_m4_expelled_at_4 :
    kimberlingFullOrbit 4 0 ≠ 1 ∧ kimberlingFullOrbit 4 1 ≠ 2 ∧
    kimberlingFullOrbit 4 2 ≠ 3 ∧ kimberlingFullOrbit 4 3 = 4 := by decide
lemma a007063_m2_expelled_at_25 :
    (∀ k < 24, kimberlingFullOrbit 2 k ≠ k + 1) ∧ kimberlingFullOrbit 2 24 = 25 := by decide

lemma kimberlingActiveStep_bounds {t p : ℕ} (hlo : 1 ≤ p) (hhi : p ≤ 2 * t - 1) (hne : p ≠ t) :
    1 ≤ kimberlingActiveStep t p ∧ kimberlingActiveStep t p ≤ 2 * (t + 1) - 1 := by
  unfold kimberlingActiveStep
  split_ifs with hlt <;> omega

lemma kimberlingOrbit_bounds {t₀ p₀ : ℕ} (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    ∀ n, 1 ≤ kimberlingOrbit t₀ p₀ n ∧ kimberlingOrbit t₀ p₀ n ≤ 2 * (t₀ + n) - 1 := by
  intro n
  induction n with
  | zero => exact ⟨hlo, by simpa [kimberlingOrbit] using hhi⟩
  | succ k ih =>
    have hstep := kimberlingActiveStep_bounds ih.1 ih.2 (hne k)
    simpa [kimberlingOrbit, Nat.add_assoc] using hstep

lemma kimberlingOrbit_add (t₀ p₀ k n : ℕ) :
    kimberlingOrbit (t₀ + k) (kimberlingOrbit t₀ p₀ k) n = kimberlingOrbit t₀ p₀ (k + n) := by
  induction n with
  | zero => simp [kimberlingOrbit]
  | succ m ih =>
    simp [kimberlingOrbit, ih, Nat.add_assoc]

lemma kimberlingFullStep_eq_activeStep {t p : ℕ} (ht : 1 ≤ t) (hhi : p ≤ 2 * t - 1) :
    kimberlingFullStep t p = kimberlingActiveStep t p := by
  unfold kimberlingFullStep kimberlingActiveStep
  by_cases h1 : p < t
  · simp [h1]
  · have h2 : p < 2 * t := by omega
    simp [h1, h2]

lemma kimberlingFullOrbit_drift {m : ℕ} (hm : 2 ≤ m) :
    ∀ k ≤ (m + 1) / 3, kimberlingFullOrbit m k = m - k := by
  intro k hk
  induction k with
  | zero => simp [kimberlingFullOrbit]
  | succ j ih =>
    have hj : j ≤ (m + 1) / 3 := by omega
    have hprev := ih hj
    have hge : 2 * (j + 1) ≤ m - j := by omega
    have hnlt1 : ¬ (m - j < j + 1) := by omega
    have hnlt2 : ¬ (m - j < 2 * (j + 1)) := by omega
    simp only [kimberlingFullOrbit, hprev, kimberlingFullStep, hnlt1, hnlt2, ↓reduceIte]
    omega

lemma kimberlingFullOrbit_enters_active {m : ℕ} (hm : 2 ≤ m)
    (hne : ∀ n, kimberlingFullOrbit m n ≠ n + 1) :
    let k₀ := (m + 1) / 3
    let t₀ := k₀ + 1
    let p₀ := m - k₀
    1 ≤ p₀ ∧ p₀ ≤ 2 * t₀ - 1 ∧
      ∀ n, kimberlingFullOrbit m (k₀ + n) = kimberlingOrbit t₀ p₀ n := by
  intro k₀ t₀ p₀
  have hlo : 1 ≤ p₀ := by omega
  have hhi : p₀ ≤ 2 * t₀ - 1 := by omega
  have hmain : ∀ n,
      kimberlingFullOrbit m (k₀ + n) = kimberlingOrbit t₀ p₀ n ∧
      1 ≤ kimberlingOrbit t₀ p₀ n ∧
      kimberlingOrbit t₀ p₀ n ≤ 2 * (t₀ + n) - 1 := by
    intro n
    induction n with
    | zero =>
      exact ⟨by simpa [kimberlingOrbit, p₀] using kimberlingFullOrbit_drift hm k₀ (le_refl k₀),
             hlo, by simpa [kimberlingOrbit] using hhi⟩
    | succ j ih =>
      rcases ih with ⟨heq_j, hlo_j, hhi_j⟩
      have hne_j : kimberlingOrbit t₀ p₀ j ≠ t₀ + j := by
        rw [← heq_j]
        have hstage : t₀ + j = (k₀ + j) + 1 := by omega
        rw [hstage]
        exact hne (k₀ + j)
      have hstep_eq : kimberlingFullOrbit m (k₀ + (j + 1)) = kimberlingOrbit t₀ p₀ (j + 1) := by
        have h1 : k₀ + (j + 1) = (k₀ + j) + 1 := by omega
        rw [h1, kimberlingFullOrbit, heq_j]
        have hstage : (k₀ + j) + 1 = t₀ + j := by omega
        rw [hstage, kimberlingFullStep_eq_activeStep (by omega) hhi_j]
        rfl
      have hbounds_next := kimberlingActiveStep_bounds hlo_j hhi_j hne_j
      exact ⟨hstep_eq, hbounds_next.1, by simpa [kimberlingOrbit, Nat.add_assoc] using hbounds_next.2⟩
  exact ⟨hlo, hhi, fun n => (hmain n).1⟩

end Dynamics

/-! ## Section 2: Elementary Dyadic Series Convergence Lemmas -/

section DyadicSeries

lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    calc k + 1 ≤ 2 ^ k + 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

lemma nat_sq_le_two_pow_succ (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    by_cases hk : k ≤ 2
    · rcases k with _ | _ | _ | k
      · norm_num
      · norm_num
      · norm_num
      · omega
    · have h2 : 2 * k + 1 ≤ k ^ 2 := by nlinarith
      calc (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
        _ ≤ k ^ 2 + k ^ 2 := by omega
        _ ≤ 2 ^ (k + 1) + 2 ^ (k + 1) := by omega
        _ = 2 ^ (k + 2) := by ring

lemma tendsto_const_add_nat_div_two_pow (c : ℝ) :
    Tendsto (fun N : ℕ => (c + (N : ℝ)) / (2 : ℝ) ^ N) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt ((|c| + 2) / ε)
  refine ⟨max M 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right M 1) hN
  have hNM : M ≤ N := le_trans (le_max_left M 1) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h1 : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast nat_le_two_pow N
  have h2 : (N : ℝ) ^ 2 ≤ 2 * (2 : ℝ) ^ N := by
    have := nat_sq_le_two_pow_succ N
    have hcast : ((N ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (N + 1) : ℕ) : ℝ) := by exact_mod_cast this
    simpa [pow_succ, mul_comm] using hcast
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpow_pos]
  have hnum : |c + (N : ℝ)| ≤ |c| + (N : ℝ) := by
    calc |c + (N : ℝ)| ≤ |c| + |(N : ℝ)| := abs_add_le c (N : ℝ)
      _ = |c| + (N : ℝ) := by rw [Nat.abs_cast]
  have hdiv1 : |c| / (2 : ℝ) ^ N ≤ |c| / (N : ℝ) :=
    div_le_div_of_nonneg_left (abs_nonneg c) hNpos h1
  have hdiv2 : (N : ℝ) / (2 : ℝ) ^ N ≤ 2 / (N : ℝ) := by
    rw [div_le_div_iff₀ hpow_pos hNpos]
    linarith [h2]
  have hbound : (|c| + (N : ℝ)) / (2 : ℝ) ^ N ≤ (|c| + 2) / (N : ℝ) := by
    rw [add_div, add_div]
    linarith
  have hlt : (|c| + 2) / (N : ℝ) < ε := by
    have hMle : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNM
    have hlt' : (|c| + 2) / ε < (N : ℝ) := lt_of_lt_of_le hM hMle
    exact (div_lt_iff₀ hNpos).mpr (by rwa [div_lt_iff₀ hε, mul_comm] at hlt')
  exact lt_of_le_of_lt (le_trans (div_le_div_of_nonneg_right hnum (le_of_lt hpow_pos)) hbound) hlt

lemma sum_inv_two_pow_succ (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 : ℝ) / (2 : ℝ) ^ (n + 1) = 1 - 1 / (2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

lemma hasSum_inv_two_pow_succ :
    HasSum (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ (n + 1)) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  simp_rw [sum_inv_two_pow_succ]
  have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) := by
    have hlin := tendsto_const_add_nat_div_two_pow 1
    have hle : ∀ N : ℕ, 0 ≤ (1 : ℝ) / (2 : ℝ) ^ N := fun N => by positivity
    have hge : ∀ N : ℕ, (1 : ℝ) / (2 : ℝ) ^ N ≤ (1 + (N : ℝ)) / (2 : ℝ) ^ N := fun N => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith [Nat.cast_nonneg (α := ℝ) N]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlin hle hge
  simpa using tendsto_const_nhds.sub h0

lemma summable_inv_two_pow_succ :
    Summable (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ (n + 1)) :=
  hasSum_inv_two_pow_succ.summable

lemma sum_succ_div_two_pow_succ (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1) =
      2 - ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma hasSum_succ_div_two_pow_succ :
    HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) 2 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  simp_rw [sum_succ_div_two_pow_succ]
  have h0 : Tendsto (fun N : ℕ => ((N : ℝ) + 2) / (2 : ℝ) ^ N) atTop (nhds 0) := by
    simpa [add_comm] using tendsto_const_add_nat_div_two_pow 2
  simpa using tendsto_const_nhds.sub h0

lemma summable_succ_div_two_pow_succ :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) :=
  hasSum_succ_div_two_pow_succ.summable

lemma summable_of_abs_le_const_div_two_pow {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n, |f n| ≤ C * ((1 : ℝ) / (2 : ℝ) ^ (n + 1))) : Summable f :=
  Summable.of_norm_bounded (summable_inv_two_pow_succ.mul_left C) (fun n => by simpa [Real.norm_eq_abs] using hf n)

lemma summable_of_abs_le_linear_div_two_pow {f : ℕ → ℝ} {A B : ℝ}
    (hf : ∀ n, |f n| ≤ A * ((1 : ℝ) / (2 : ℝ) ^ (n + 1)) +
        B * (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))) : Summable f :=
  Summable.of_norm_bounded
    ((summable_inv_two_pow_succ.mul_left A).add (summable_succ_div_two_pow_succ.mul_left B))
    (fun n => by simpa [Real.norm_eq_abs] using hf n)

end DyadicSeries

/-! ## Section 3: Exact Binary Series Identity -/

section SeriesIdentity

/-- Step sign `s_n ∈ {-1, +1}`: `-1` if `p_n < t₀ + n`, `+1` if `p_n ≥ t₀ + n`
(for never-expelled orbits, `+1` iff `p_n > t₀ + n`). -/
def stepSign (t₀ p₀ n : ℕ) : ℤ :=
  if kimberlingOrbit t₀ p₀ n < t₀ + n then -1 else 1

/-- Cumulative sign product `σ_n = ∏_{j=0}^{n-1} s_j ∈ {-1, +1}`, with `σ_0 = 1`. -/
def cumSign (t₀ p₀ : ℕ) : ℕ → ℤ
  | 0 => 1
  | n + 1 => cumSign t₀ p₀ n * stepSign t₀ p₀ n

/-- Cumulative sign bit `b'_n = (1 + σ_{n+1}) / 2 ∈ {0, 1}` matching `verify_identity.py`. -/
def cumBit (t₀ p₀ n : ℕ) : ℕ :=
  if cumSign t₀ p₀ (n + 1) = 1 then 1 else 0

lemma stepSign_eq_neg_one_or_one (t₀ p₀ n : ℕ) :
    stepSign t₀ p₀ n = -1 ∨ stepSign t₀ p₀ n = 1 := by
  unfold stepSign; split_ifs <;> simp

lemma stepSign_sq (t₀ p₀ n : ℕ) : stepSign t₀ p₀ n * stepSign t₀ p₀ n = 1 := by
  rcases stepSign_eq_neg_one_or_one t₀ p₀ n with h | h <;> simp [h]

lemma stepSign_abs_real (t₀ p₀ n : ℕ) : |(stepSign t₀ p₀ n : ℝ)| = 1 := by
  rcases stepSign_eq_neg_one_or_one t₀ p₀ n with h | h <;> simp [h]

lemma cumSign_eq_neg_one_or_one (t₀ p₀ n : ℕ) :
    cumSign t₀ p₀ n = -1 ∨ cumSign t₀ p₀ n = 1 := by
  induction n with
  | zero => right; rfl
  | succ k ih =>
    simp only [cumSign]
    rcases ih with h1 | h1 <;> rcases stepSign_eq_neg_one_or_one t₀ p₀ k with h2 | h2 <;>
      simp [h1, h2]

lemma cumSign_abs_real (t₀ p₀ n : ℕ) : |(cumSign t₀ p₀ n : ℝ)| = 1 := by
  rcases cumSign_eq_neg_one_or_one t₀ p₀ n with h | h <;> simp [h]

lemma cumBit_eq_zero_or_one (t₀ p₀ n : ℕ) :
    cumBit t₀ p₀ n = 0 ∨ cumBit t₀ p₀ n = 1 := by
  unfold cumBit; split_ifs <;> simp

lemma cumBit_cast_real (t₀ p₀ n : ℕ) :
    (cumBit t₀ p₀ n : ℝ) = (1 + (cumSign t₀ p₀ (n + 1) : ℝ)) / 2 := by
  unfold cumBit
  rcases cumSign_eq_neg_one_or_one t₀ p₀ (n + 1) with h | h <;> norm_num [h]

lemma cumSign_cast_from_bit (t₀ p₀ n : ℕ) :
    (cumSign t₀ p₀ (n + 1) : ℝ) = 2 * (cumBit t₀ p₀ n : ℝ) - 1 := by
  linarith [cumBit_cast_real t₀ p₀ n]

lemma stepSign_shift (t₀ p₀ k n : ℕ) :
    stepSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) n = stepSign t₀ p₀ (k + n) := by
  simp [stepSign, kimberlingOrbit_add, Nat.add_assoc]

lemma cumSign_shift_succ (t₀ p₀ k n : ℕ) :
    cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) (n + 1) =
      stepSign t₀ p₀ k * cumSign (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) n := by
  induction n with
  | zero =>
    simp [cumSign, stepSign_shift]
  | succ m ih =>
    rw [cumSign, ih, cumSign, stepSign_shift, stepSign_shift]
    have h1 : k + (m + 1) = k + 1 + m := by omega
    rw [h1]
    ring

/-- Single-step algebraic identity in `ℝ`:
`p_n - (t₀ + n) - 1/4 = s_n * (p_{n+1} / 2 + 1/4)`. -/
lemma kimberling_step_real_eq {t₀ p₀ : ℕ} (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) (n : ℕ) :
    (kimberlingOrbit t₀ p₀ n : ℝ) - ((t₀ + n : ℕ) : ℝ) - 1 / 4 =
      (stepSign t₀ p₀ n : ℝ) * ((kimberlingOrbit t₀ p₀ (n + 1) : ℝ) / 2 + 1 / 4) := by
  have hnext : kimberlingOrbit t₀ p₀ (n + 1) = kimberlingActiveStep (t₀ + n) (kimberlingOrbit t₀ p₀ n) := rfl
  rw [hnext]
  unfold kimberlingActiveStep stepSign
  set p := kimberlingOrbit t₀ p₀ n
  set t := t₀ + n
  have hne_n : p ≠ t := hne n
  by_cases hlt : p < t
  · simp only [hlt, ↓reduceIte, Int.cast_neg, Int.cast_one]
    have hle : p ≤ t := le_of_lt hlt
    have hcast : ((2 * (t - p) : ℕ) : ℝ) = 2 * ((t : ℝ) - (p : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_sub hle]; norm_num
    rw [hcast]
    ring
  · have hgt : t < p := by omega
    simp only [hlt, ↓reduceIte, Int.cast_one]
    have h1 : 1 ≤ 2 * (p - t) := by omega
    have hcast : ((2 * (p - t) - 1 : ℕ) : ℝ) = 2 * ((p : ℝ) - (t : ℝ)) - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_mul, Nat.cast_sub (le_of_lt hgt)]; norm_num
    rw [hcast]
    ring

/-- Exact telescoping remainder identity for every `N : ℕ`:
`p₀ - (t₀ + 1/4) - ∑_{n<N} σ_{n+1} (t₀ + (n+1) + 3/4) / 2^(n+1) = σ_N (p_N - (t₀ + N) - 1/4) / 2^N`. -/
lemma kimberling_partial_sum_remainder {t₀ p₀ : ℕ}
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) (N : ℕ) :
    (p₀ : ℝ) - ((t₀ : ℝ) + 1 / 4) -
      ∑ n ∈ Finset.range N,
        (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1) =
      (cumSign t₀ p₀ N : ℝ) *
        ((kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4) / (2 : ℝ) ^ N := by
  induction N with
  | zero =>
    simp [kimberlingOrbit, cumSign]
    ring
  | succ k ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    have hstep := kimberling_step_real_eq hne k
    have hcum : (cumSign t₀ p₀ (k + 1) : ℝ) = (cumSign t₀ p₀ k : ℝ) * (stepSign t₀ p₀ k : ℝ) := by
      simp [cumSign]
    rw [hstep, ← mul_assoc, ← hcum]
    rw [pow_succ]
    push_cast
    ring

lemma kimberling_signed_term_summable (t₀ p₀ : ℕ) :
    Summable (fun n : ℕ =>
      (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) := by
  apply summable_of_abs_le_linear_div_two_pow (A := (t₀ : ℝ) + 3 / 4) (B := 1)
  intro n
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hnonneg : (0 : ℝ) ≤ (t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4 := by positivity
  rw [abs_div, abs_mul, cumSign_abs_real, one_mul, abs_of_nonneg hnonneg, abs_of_pos hpos]
  ring_nf
  rfl

lemma kimberling_bit_summable (t₀ p₀ : ℕ) :
    Summable (fun n : ℕ => (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  apply summable_of_abs_le_const_div_two_pow (C := 1)
  intro n
  have hb : (cumBit t₀ p₀ n : ℝ) ≤ 1 := by
    rcases cumBit_eq_zero_or_one t₀ p₀ n with h | h <;> norm_num [h]
  rw [abs_of_nonneg (by positivity)]
  rw [one_mul]
  exact div_le_div_of_nonneg_right hb (by positivity)

lemma kimberling_weighted_bit_summable (t₀ p₀ : ℕ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  apply summable_of_abs_le_linear_div_two_pow (A := 0) (B := 1)
  intro n
  have hb : (cumBit t₀ p₀ n : ℝ) ≤ 1 := by
    rcases cumBit_eq_zero_or_one t₀ p₀ n with h | h <;> norm_num [h]
  rw [abs_of_nonneg (by positivity), zero_mul, zero_add, one_mul]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) (n + 1)]

lemma kimberling_never_expelled_signed_hasSum {t₀ p₀ : ℕ}
    (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    HasSum (fun n : ℕ =>
      (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1))
      ((p₀ : ℝ) - ((t₀ : ℝ) + 1 / 4)) := by
  have hsum := kimberling_signed_term_summable t₀ p₀
  have hrem_zero : Tendsto (fun N : ℕ =>
      (cumSign t₀ p₀ N : ℝ) *
        ((kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4) / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
    have hbounds := kimberlingOrbit_bounds hlo hhi hne
    have hdom := tendsto_const_add_nat_div_two_pow ((t₀ : ℝ) + 1)
    have hneg : Tendsto (fun N : ℕ => -(((t₀ : ℝ) + 1 + (N : ℝ)) / (2 : ℝ) ^ N))
        atTop (nhds 0) := by simpa using hdom.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hneg hdom ?_ ?_ <;> intro N
    · have hb := hbounds N
      have hp_lo : (1 : ℝ) ≤ (kimberlingOrbit t₀ p₀ N : ℝ) := by exact_mod_cast hb.1
      have hp_hi : (kimberlingOrbit t₀ p₀ N : ℝ) ≤ 2 * ((t₀ + N : ℕ) : ℝ) - 1 := by
        have ht1 : 1 ≤ 2 * (t₀ + N) := by omega
        have hcast : ((2 * (t₀ + N) - 1 : ℕ) : ℝ) = 2 * ((t₀ + N : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub ht1]; push_cast; ring
        have := (Nat.cast_le (α := ℝ)).mpr hb.2
        linarith
      have habs : |(kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4| ≤
          (t₀ : ℝ) + 1 + (N : ℝ) := by
        rw [abs_le]; push_cast at hp_hi ⊢; constructor <;> linarith
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
      have hterm : |(cumSign t₀ p₀ N : ℝ) *
          ((kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4) / (2 : ℝ) ^ N| ≤
          ((t₀ : ℝ) + 1 + (N : ℝ)) / (2 : ℝ) ^ N := by
        rw [abs_div, abs_mul, cumSign_abs_real, one_mul, abs_of_pos hpow_pos]
        exact div_le_div_of_nonneg_right habs (le_of_lt hpow_pos)
      exact (abs_le.mp hterm).1
    · have hb := hbounds N
      have hp_lo : (1 : ℝ) ≤ (kimberlingOrbit t₀ p₀ N : ℝ) := by exact_mod_cast hb.1
      have hp_hi : (kimberlingOrbit t₀ p₀ N : ℝ) ≤ 2 * ((t₀ + N : ℕ) : ℝ) - 1 := by
        have ht1 : 1 ≤ 2 * (t₀ + N) := by omega
        have hcast : ((2 * (t₀ + N) - 1 : ℕ) : ℝ) = 2 * ((t₀ + N : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub ht1]; push_cast; ring
        have := (Nat.cast_le (α := ℝ)).mpr hb.2
        linarith
      have habs : |(kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4| ≤
          (t₀ : ℝ) + 1 + (N : ℝ) := by
        rw [abs_le]; push_cast at hp_hi ⊢; constructor <;> linarith
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
      have hterm : |(cumSign t₀ p₀ N : ℝ) *
          ((kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4) / (2 : ℝ) ^ N| ≤
          ((t₀ : ℝ) + 1 + (N : ℝ)) / (2 : ℝ) ^ N := by
        rw [abs_div, abs_mul, cumSign_abs_real, one_mul, abs_of_pos hpow_pos]
        exact div_le_div_of_nonneg_right habs (le_of_lt hpow_pos)
      exact (abs_le.mp hterm).2
  have heq : (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) =
      fun N : ℕ => ((p₀ : ℝ) - ((t₀ : ℝ) + 1 / 4)) -
        (cumSign t₀ p₀ N : ℝ) *
          ((kimberlingOrbit t₀ p₀ N : ℝ) - ((t₀ + N : ℕ) : ℝ) - 1 / 4) / (2 : ℝ) ^ N := by
    funext N
    linarith [kimberling_partial_sum_remainder hne N]
  have htend : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1))
      atTop (nhds ((p₀ : ℝ) - ((t₀ : ℝ) + 1 / 4))) := by
    rw [heq]
    simpa using tendsto_const_nhds.sub hrem_zero
  have htsum : (∑' n : ℕ,
      (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) =
      (p₀ : ℝ) - ((t₀ : ℝ) + 1 / 4) :=
    tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat htend
  rw [← htsum]
  exact hsum.hasSum

/-- Exact signed binary series identity for every never-expelled active-zone orbit. -/
theorem kimberling_never_expelled_signed_series {t₀ p₀ : ℕ}
    (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    (p₀ : ℝ) = (t₀ : ℝ) + 1 / 4 +
      ∑' n : ℕ,
        (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1) := by
  have hs := (kimberling_never_expelled_signed_hasSum hlo hhi hne).tsum_eq
  linarith

/-- **Part 1 — Exact Binary Series Identity (`kimberling_never_expelled_series_eq`):**
For every never-expelled active-zone orbit `(t₀ + n, p_n)` (`1 ≤ p₀ ≤ 2t₀ - 1`),
letting `b'_n = cumBit t₀ p₀ n = (1 + σ_{n+1}) / 2 ∈ {0, 1}`,
```
2 * p₀ + 5 = (4 * t₀ + 3) * ∑' n, b'_n / 2^(n+1) + 4 * ∑' n, (n + 1) * b'_n / 2^(n+1).
``` -/
theorem kimberling_never_expelled_series_eq {t₀ p₀ : ℕ}
    (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    2 * (p₀ : ℝ) + 5 =
      (4 * (t₀ : ℝ) + 3) * (∑' n : ℕ, (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) +
      4 * (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  have hs_signed := kimberling_never_expelled_signed_series hlo hhi hne
  have hs1 := hasSum_inv_two_pow_succ.tsum_eq
  have hs2 := hasSum_succ_div_two_pow_succ.tsum_eq
  have hsum_b := kimberling_bit_summable t₀ p₀
  have hsum_nb := kimberling_weighted_bit_summable t₀ p₀
  have hterm :
      (fun n : ℕ =>
        (cumSign t₀ p₀ (n + 1) : ℝ) * ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) =
      fun n : ℕ =>
        (2 * ((t₀ : ℝ) + 3 / 4) * ((cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) +
         2 * (((n + 1 : ℕ) : ℝ) * (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1))) -
        (((t₀ : ℝ) + 3 / 4) * ((1 : ℝ) / (2 : ℝ) ^ (n + 1)) +
         ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
    funext n
    rw [cumSign_cast_from_bit]
    ring
  rw [hterm] at hs_signed
  have hA : Summable (fun n : ℕ =>
      2 * ((t₀ : ℝ) + 3 / 4) * ((cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) +
      2 * (((n + 1 : ℕ) : ℝ) * (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1))) :=
    (hsum_b.mul_left _).add (hsum_nb.mul_left _)
  have hB : Summable (fun n : ℕ =>
      ((t₀ : ℝ) + 3 / 4) * ((1 : ℝ) / (2 : ℝ) ^ (n + 1)) +
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) :=
    (summable_inv_two_pow_succ.mul_left _).add summable_succ_div_two_pow_succ
  rw [hA.tsum_sub hB,
      (hsum_b.mul_left _).tsum_add (hsum_nb.mul_left _),
      (summable_inv_two_pow_succ.mul_left _).tsum_add summable_succ_div_two_pow_succ,
      tsum_mul_left, tsum_mul_left, tsum_mul_left, hs1, hs2] at hs_signed
  linarith

end SeriesIdentity

/-! ## Section 4: Dyadic Coordinate, Tent Map, and No Eventually Periodic Itinerary -/

section NoPeriodic

/-- Normalized dyadic coordinate `x(t₀, p₀) = 1 + ∑' n, σ_{n+1} / 2^(n+1) ∈ [0, 2]`. -/
noncomputable def dyadicCoord (t₀ p₀ : ℕ) : ℝ :=
  1 + ∑' n : ℕ, (cumSign t₀ p₀ (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

lemma cumSign_div_two_pow_summable (t₀ p₀ : ℕ) :
    Summable (fun n : ℕ => (cumSign t₀ p₀ (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
  apply summable_of_abs_le_const_div_two_pow (C := 1)
  intro n
  rw [abs_div, cumSign_abs_real, abs_of_pos (by positivity), one_mul]

lemma dyadicCoord_eq_two_mul_bit_tsum (t₀ p₀ : ℕ) :
    dyadicCoord t₀ p₀ = 2 * ∑' n : ℕ, (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) := by
  unfold dyadicCoord
  have hterm :
      (fun n : ℕ => (cumSign t₀ p₀ (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)) =
      fun n : ℕ => 2 * ((cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1)) - (1 : ℝ) / (2 : ℝ) ^ (n + 1) := by
    funext n
    rw [cumSign_cast_from_bit]
    ring
  rw [hterm, ((kimberling_bit_summable t₀ p₀).mul_left 2).tsum_sub summable_inv_two_pow_succ,
      tsum_mul_left, hasSum_inv_two_pow_succ.tsum_eq]
  ring

lemma two_sub_dyadicCoord_eq (t₀ p₀ : ℕ) :
    2 - dyadicCoord t₀ p₀ = 2 * ∑' n : ℕ, (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1) := by
  rw [dyadicCoord_eq_two_mul_bit_tsum]
  have hterm :
      (fun n : ℕ => (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1)) =
      fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ (n + 1) - (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) := by
    funext n; ring
  rw [hterm, summable_inv_two_pow_succ.tsum_sub (kimberling_bit_summable t₀ p₀),
      hasSum_inv_two_pow_succ.tsum_eq]
  ring

lemma dyadicCoord_pos {t₀ p₀ : ℕ} (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    0 < dyadicCoord t₀ p₀ := by
  have hnonneg : 0 ≤ ∑' n : ℕ, (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) :=
    tsum_nonneg (fun n => by positivity)
  rw [dyadicCoord_eq_two_mul_bit_tsum]
  by_contra hle
  push Not at hle
  have hzero : ∑' n : ℕ, (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) = 0 := by linarith
  have hall : ∀ n, cumBit t₀ p₀ n = 0 := by
    intro n
    have hle_n : (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) ≤
        ∑' m : ℕ, (cumBit t₀ p₀ m : ℝ) / (2 : ℝ) ^ (m + 1) :=
      (kimberling_bit_summable t₀ p₀).le_tsum n (fun m _ => by positivity)
    have hge_n : (0 : ℝ) ≤ (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) := by positivity
    have hdiv0 : (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) = 0 := by linarith
    have hcast0 : (cumBit t₀ p₀ n : ℝ) = 0 := by
      have hpos : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
      exact (div_eq_zero_iff.mp hdiv0).resolve_right hpos
    exact_mod_cast hcast0
  have hser := kimberling_never_expelled_series_eq hlo hhi hne
  simp [hall] at hser
  have hp0 : (0 : ℝ) ≤ (p₀ : ℝ) := Nat.cast_nonneg p₀
  linarith

lemma dyadicCoord_lt_two {t₀ p₀ : ℕ} (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    dyadicCoord t₀ p₀ < 2 := by
  have hsub_summable : Summable (fun n : ℕ => (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1)) := by
    have heq : (fun n : ℕ => (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1)) =
        fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ (n + 1) - (cumBit t₀ p₀ n : ℝ) / (2 : ℝ) ^ (n + 1) := by
      funext n; ring
    rw [heq]
    exact summable_inv_two_pow_succ.sub (kimberling_bit_summable t₀ p₀)
  have hterm_nonneg : ∀ n, 0 ≤ (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1) := by
    intro n
    apply div_nonneg _ (by positivity)
    rcases cumBit_eq_zero_or_one t₀ p₀ n with h | h <;> norm_num [h]
  have hnonneg : 0 ≤ 2 - dyadicCoord t₀ p₀ := by
    rw [two_sub_dyadicCoord_eq]
    exact mul_nonneg (by norm_num) (tsum_nonneg hterm_nonneg)
  by_contra hge
  push Not at hge
  have hzero : ∑' n : ℕ, (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1) = 0 := by
    linarith [two_sub_dyadicCoord_eq t₀ p₀]
  have hall : ∀ n, cumBit t₀ p₀ n = 1 := by
    intro n
    have hle_n : (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1) ≤
        ∑' m : ℕ, (1 - (cumBit t₀ p₀ m : ℝ)) / (2 : ℝ) ^ (m + 1) :=
      hsub_summable.le_tsum n (fun m _ => hterm_nonneg m)
    have hdiv0 : (1 - (cumBit t₀ p₀ n : ℝ)) / (2 : ℝ) ^ (n + 1) = 0 := by
      linarith [hterm_nonneg n]
    have hcast1 : (cumBit t₀ p₀ n : ℝ) = 1 := by
      have hpos : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
      linarith [(div_eq_zero_iff.mp hdiv0).resolve_right hpos]
    exact_mod_cast hcast1
  have hser := kimberling_never_expelled_series_eq hlo hhi hne
  simp only [hall, Nat.cast_one, mul_one, hasSum_inv_two_pow_succ.tsum_eq,
             hasSum_succ_div_two_pow_succ.tsum_eq] at hser
  have hhi_real : (p₀ : ℝ) ≤ 2 * (t₀ : ℝ) - 1 := by
    have ht1 : 1 ≤ 2 * t₀ := by omega
    have hcast : ((2 * t₀ - 1 : ℕ) : ℝ) = 2 * (t₀ : ℝ) - 1 := by
      rw [Nat.cast_sub ht1]; push_cast; ring
    have := (Nat.cast_le (α := ℝ)).mpr hhi
    linarith
  linarith

/-- Exact step equation for `dyadicCoord`:
`x_k = 1 + (s_k / 2) * x_{k+1}`. -/
lemma dyadicCoord_step (t₀ p₀ k : ℕ) :
    dyadicCoord (t₀ + k) (kimberlingOrbit t₀ p₀ k) =
      1 + (stepSign t₀ p₀ k : ℝ) / 2 *
        dyadicCoord (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) := by
  unfold dyadicCoord
  have hsum := cumSign_div_two_pow_summable (t₀ + k) (kimberlingOrbit t₀ p₀ k)
  rw [hsum.tsum_eq_zero_add]
  have h0 : (cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) 1 : ℝ) / (2 : ℝ) ^ 1 =
      (stepSign t₀ p₀ k : ℝ) / 2 := by
    simp [cumSign, stepSign_shift]
  rw [h0]
  have htail :
      (fun n : ℕ =>
        (cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) (n + 1 + 1) : ℝ) / (2 : ℝ) ^ (n + 1 + 1)) =
      fun n : ℕ =>
        ((stepSign t₀ p₀ k : ℝ) / 2) *
          ((cumSign (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) (n + 1) : ℝ) /
            (2 : ℝ) ^ (n + 1)) := by
    funext n
    rw [cumSign_shift_succ t₀ p₀ k (n + 1)]
    push_cast
    rw [pow_succ]
    ring
  rw [htail, tsum_mul_left]
  ring

/-- Equivalent tent-map form: `x_{k+1} = 2 * s_k * (x_k - 1)`. -/
lemma dyadicCoord_succ_eq (t₀ p₀ k : ℕ) :
    dyadicCoord (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) =
      2 * (stepSign t₀ p₀ k : ℝ) * (dyadicCoord (t₀ + k) (kimberlingOrbit t₀ p₀ k) - 1) := by
  have h := dyadicCoord_step t₀ p₀ k
  have hsq : (stepSign t₀ p₀ k : ℝ) * (stepSign t₀ p₀ k : ℝ) = 1 := by
    exact_mod_cast stepSign_sq t₀ p₀ k
  calc dyadicCoord (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1))
      = (stepSign t₀ p₀ k : ℝ) * (stepSign t₀ p₀ k : ℝ) *
          dyadicCoord (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) := by rw [hsq, one_mul]
    _ = 2 * (stepSign t₀ p₀ k : ℝ) * (dyadicCoord (t₀ + k) (kimberlingOrbit t₀ p₀ k) - 1) := by
        rw [h]; ring

/-- On any never-expelled active-zone orbit, `s_k` is uniquely determined by `x_k`
(`s_k = 1 ↔ 1 < x_k`, and `x_k ≠ 1`). -/
lemma stepSign_eq_one_iff_one_lt_dyadicCoord {t₀ p₀ : ℕ}
    (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) (k : ℕ) :
    stepSign t₀ p₀ k = 1 ↔ 1 < dyadicCoord (t₀ + k) (kimberlingOrbit t₀ p₀ k) := by
  have hb := kimberlingOrbit_bounds hlo hhi hne (k + 1)
  have hne' : ∀ n, kimberlingOrbit (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) n ≠
      (t₀ + (k + 1)) + n := by
    intro n
    rw [kimberlingOrbit_add]
    have h1 : t₀ + (k + 1) + n = t₀ + (k + 1 + n) := by omega
    rw [h1]
    exact hne (k + 1 + n)
  have hx_next_pos : 0 < dyadicCoord (t₀ + (k + 1)) (kimberlingOrbit t₀ p₀ (k + 1)) :=
    dyadicCoord_pos hb.1 hb.2 hne'
  have hstep := dyadicCoord_step t₀ p₀ k
  rcases stepSign_eq_neg_one_or_one t₀ p₀ k with hs | hs
  · rw [hs] at hstep ⊢
    norm_num at hstep ⊢
    linarith
  · rw [hs] at hstep ⊢
    norm_num at hstep ⊢
    linarith

/-- Iterated expansion of `x_k` for `m` steps:
`x_k = ∑_{j < m} σ^{(k)}_j / 2^j + σ^{(k)}_m / 2^m * x_{k+m}`. -/
lemma dyadicCoord_iter (t₀ p₀ k m : ℕ) :
    dyadicCoord (t₀ + k) (kimberlingOrbit t₀ p₀ k) =
      (∑ j ∈ Finset.range m,
        (cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) j : ℝ) / (2 : ℝ) ^ j) +
      (cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) m : ℝ) / (2 : ℝ) ^ m *
        dyadicCoord (t₀ + (k + m)) (kimberlingOrbit t₀ p₀ (k + m)) := by
  induction m with
  | zero => simp [cumSign]
  | succ r ih =>
    rw [ih, Finset.sum_range_succ, dyadicCoord_step t₀ p₀ (k + r)]
    have hcum : (cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) (r + 1) : ℝ) =
        (cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) r : ℝ) * (stepSign t₀ p₀ (k + r) : ℝ) := by
      simp [cumSign, stepSign_shift]
    rw [hcum, pow_succ]
    have hadd : k + r + 1 = k + (r + 1) := by omega
    rw [hadd]
    ring

/-- If two shifts of a never-expelled orbit have equal `dyadicCoord`, then all subsequent
step signs agree. -/
lemma dyadicCoord_eq_imp_stepSign_eq {t₀ p₀ : ℕ}
    (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) {i j : ℕ}
    (heq : dyadicCoord (t₀ + i) (kimberlingOrbit t₀ p₀ i) =
           dyadicCoord (t₀ + j) (kimberlingOrbit t₀ p₀ j)) :
    ∀ n, dyadicCoord (t₀ + (i + n)) (kimberlingOrbit t₀ p₀ (i + n)) =
         dyadicCoord (t₀ + (j + n)) (kimberlingOrbit t₀ p₀ (j + n)) ∧
         stepSign t₀ p₀ (i + n) = stepSign t₀ p₀ (j + n) := by
  have hs_of_x : ∀ a b,
      dyadicCoord (t₀ + a) (kimberlingOrbit t₀ p₀ a) =
      dyadicCoord (t₀ + b) (kimberlingOrbit t₀ p₀ b) →
      stepSign t₀ p₀ a = stepSign t₀ p₀ b := by
    intro a b hab
    have ha := stepSign_eq_one_iff_one_lt_dyadicCoord hlo hhi hne a
    have hb := stepSign_eq_one_iff_one_lt_dyadicCoord hlo hhi hne b
    rw [hab] at ha
    rcases stepSign_eq_neg_one_or_one t₀ p₀ a with h1 | h1 <;>
    rcases stepSign_eq_neg_one_or_one t₀ p₀ b with h2 | h2
    · rw [h1, h2]
    · exfalso; have := ha.mpr (hb.mp h2); omega
    · exfalso; have := hb.mpr (ha.mp h1); omega
    · rw [h1, h2]
  intro n
  induction n with
  | zero =>
    simpa using And.intro heq (hs_of_x i j heq)
  | succ m ih =>
    have hx_next : dyadicCoord (t₀ + (i + (m + 1))) (kimberlingOrbit t₀ p₀ (i + (m + 1))) =
        dyadicCoord (t₀ + (j + (m + 1))) (kimberlingOrbit t₀ p₀ (j + (m + 1))) := by
      have hi_add : i + (m + 1) = (i + m) + 1 := by omega
      have hj_add : j + (m + 1) = (j + m) + 1 := by omega
      rw [hi_add, hj_add, dyadicCoord_succ_eq, dyadicCoord_succ_eq, ih.1, ih.2]
    exact ⟨hx_next, hs_of_x _ _ hx_next⟩

/-- Under a purely periodic step-sign sequence of period `P`, the cumulative signs repeat
after shift `P`. -/
lemma cumSign_periodic_shift {t₀ p₀ P : ℕ}
    (hper : ∀ n, stepSign t₀ p₀ (n + P) = stepSign t₀ p₀ n) (k n : ℕ) :
    cumSign (t₀ + (k + P)) (kimberlingOrbit t₀ p₀ (k + P)) n =
      cumSign (t₀ + k) (kimberlingOrbit t₀ p₀ k) n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [cumSign, ih, stepSign_shift]
    have h1 : k + P + m = (k + m) + P := by omega
    rw [h1, hper]

/-- Shift difference identity under period `P`: `(p_P : ℝ) - (p₀ : ℝ) = P * x₀`. -/
lemma orbit_period_diff_eq {t₀ p₀ P : ℕ}
    (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n)
    (hper : ∀ n, stepSign t₀ p₀ (n + P) = stepSign t₀ p₀ n) :
    (kimberlingOrbit t₀ p₀ P : ℝ) - (p₀ : ℝ) = (P : ℝ) * dyadicCoord t₀ p₀ := by
  have hbP := kimberlingOrbit_bounds hlo hhi hne P
  have hneP : ∀ n, kimberlingOrbit (t₀ + P) (kimberlingOrbit t₀ p₀ P) n ≠ (t₀ + P) + n := by
    intro n
    rw [kimberlingOrbit_add, Nat.add_assoc]
    exact hne (P + n)
  have hs0 := kimberling_never_expelled_signed_series hlo hhi hne
  have hsP := kimberling_never_expelled_signed_series hbP.1 hbP.2 hneP
  have hcumP : ∀ n, cumSign (t₀ + P) (kimberlingOrbit t₀ p₀ P) n = cumSign t₀ p₀ n := by
    intro n
    simpa [kimberlingOrbit] using cumSign_periodic_shift hper 0 n
  simp_rw [hcumP] at hsP
  have hsum0 := kimberling_signed_term_summable t₀ p₀
  have hsumP : Summable (fun n : ℕ =>
      (cumSign t₀ p₀ (n + 1) : ℝ) * (((t₀ + P : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) /
        (2 : ℝ) ^ (n + 1)) := by
    simpa [hcumP] using kimberling_signed_term_summable (t₀ + P) (kimberlingOrbit t₀ p₀ P)
  have hsub :
      (∑' n : ℕ, (cumSign t₀ p₀ (n + 1) : ℝ) *
          (((t₀ + P : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) -
      (∑' n : ℕ, (cumSign t₀ p₀ (n + 1) : ℝ) *
          ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) =
      (P : ℝ) * ∑' n : ℕ, (cumSign t₀ p₀ (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1) := by
    rw [← hsumP.tsum_sub hsum0]
    have hfun : (fun n : ℕ =>
        (cumSign t₀ p₀ (n + 1) : ℝ) *
            (((t₀ + P : ℕ) : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1) -
        (cumSign t₀ p₀ (n + 1) : ℝ) *
            ((t₀ : ℝ) + ((n + 1 : ℕ) : ℝ) + 3 / 4) / (2 : ℝ) ^ (n + 1)) =
        fun n : ℕ => (P : ℝ) * ((cumSign t₀ p₀ (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)) := by
      funext n
      push_cast
      ring
    rw [hfun, tsum_mul_left]
  unfold dyadicCoord
  have htp : ((t₀ + P : ℕ) : ℝ) = (t₀ : ℝ) + (P : ℝ) := Nat.cast_add t₀ P
  linarith [hs0, hsP, hsub, htp]

/-- Core impossibility for a purely periodic never-expelled active-zone orbit. -/
theorem kimberling_no_purely_periodic_itinerary
    {t₀ p₀ : ℕ} (hlo : 1 ≤ p₀) (hhi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n)
    (hper_ex : ∃ P : ℕ, 0 < P ∧ ∀ n, stepSign t₀ p₀ (n + P) = stepSign t₀ p₀ n) :
    False := by
  classical
  -- Choose minimal positive period P ≥ 1
  let P : ℕ := Nat.find hper_ex
  have hP_spec : 0 < P ∧ ∀ n, stepSign t₀ p₀ (n + P) = stepSign t₀ p₀ n := Nat.find_spec hper_ex
  have hP_pos : 0 < P := hP_spec.1
  have hP_per : ∀ n, stepSign t₀ p₀ (n + P) = stepSign t₀ p₀ n := hP_spec.2
  have hP_min : ∀ d, 0 < d → d < P → ¬ ∀ n, stepSign t₀ p₀ (n + d) = stepSign t₀ p₀ n :=
    fun d hd hlt => fun h => Nat.find_min hper_ex hlt ⟨hd, h⟩
  -- Helper: periodicity by multiples of P
  have hP_mul : ∀ m n, stepSign t₀ p₀ (n + m * P) = stepSign t₀ p₀ n := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ r ih =>
      intro n
      have h1 : n + (r + 1) * P = (n + r * P) + P := by ring
      rw [h1, hP_per, ih]
  -- Shorthand x k := dyadicCoord (t₀ + k) (p_k)
  let x : ℕ → ℝ := fun k => dyadicCoord (t₀ + k) (kimberlingOrbit t₀ p₀ k)
  have hx0_eq : x 0 = dyadicCoord t₀ p₀ := by simp [x, kimberlingOrbit]
  have hx_bounds : ∀ k, 0 < x k ∧ x k < 2 := by
    intro k
    have hb := kimberlingOrbit_bounds hlo hhi hne k
    have hne_k : ∀ n, kimberlingOrbit (t₀ + k) (kimberlingOrbit t₀ p₀ k) n ≠ (t₀ + k) + n := by
      intro n; rw [kimberlingOrbit_add, Nat.add_assoc]; exact hne (k + n)
    exact ⟨dyadicCoord_pos hb.1 hb.2 hne_k, dyadicCoord_lt_two hb.1 hb.2 hne_k⟩
  -- x is periodic of period P
  have hx_per : ∀ k, x (k + P) = x k := by
    intro k
    simp only [x, dyadicCoord, cumSign_periodic_shift hP_per]
  -- x 0, ..., x (P - 1) are pairwise distinct by minimality of P
  have hx_inj : ∀ i ∈ Finset.range P, ∀ j ∈ Finset.range P, x i = x j → i = j := by
    intro i hi j hj hij
    rw [Finset.mem_range] at hi hj
    by_contra hne_ij
    wlog hlt : i < j generalizing i j
    · exact this j hj i hi hij.symm (Ne.symm hne_ij) (by omega)
    set d := j - i
    have hd_pos : 0 < d := by omega
    have hd_lt : d < P := by omega
    have hagree := dyadicCoord_eq_imp_stepSign_eq hlo hhi hne hij
    have hper_d : ∀ n, stepSign t₀ p₀ (n + d) = stepSign t₀ p₀ n := by
      intro n
      have hge : i ≤ n + i * P := by
        have : i ≤ i * P := Nat.le_mul_of_pos_right i hP_pos
        omega
      set r := n + i * P - i
      have hr1 : i + r = n + i * P := by omega
      have hr2 : j + r = (n + d) + i * P := by omega
      have hsr := (hagree r).2
      rw [hr1, hr2, hP_mul, hP_mul] at hsr
      exact hsr.symm
    exact hP_min d hd_pos hd_lt hper_d
  -- Rational closed form for x 0: ((2^P : ℤ) - S) * x 0 = N₀ with N₀ even, D odd > 0
  let S : ℤ := cumSign t₀ p₀ P
  let D : ℤ := (2 : ℤ) ^ P - S
  let N₀ : ℤ := ∑ j ∈ Finset.range P, cumSign t₀ p₀ j * (2 : ℤ) ^ (P - j)
  have hS_pm : S = -1 ∨ S = 1 := cumSign_eq_neg_one_or_one t₀ p₀ P
  have hD_pos : 0 < D := by
    have h2P : (2 : ℤ) ≤ (2 : ℤ) ^ P := by
      have : 2 ^ 1 ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) hP_pos
      exact_mod_cast this
    rcases hS_pm with hS | hS <;> dsimp only [D] <;> omega
  have hD_odd : ¬ ((2 : ℤ) ∣ D) := by
    have h2dvd : (2 : ℤ) ∣ (2 : ℤ) ^ P := dvd_pow_self 2 (by omega)
    rcases hS_pm with hS | hS
    · dsimp only [D]; rw [hS]; intro hdvd
      have : (2 : ℤ) ∣ (2 : ℤ) ^ P - ((2 : ℤ) ^ P - -1) := dvd_sub h2dvd hdvd
      norm_num at this
    · dsimp only [D]; rw [hS]; intro hdvd
      have : (2 : ℤ) ∣ (2 : ℤ) ^ P - ((2 : ℤ) ^ P - 1) := dvd_sub h2dvd hdvd
      norm_num at this
  have hN₀_even : (2 : ℤ) ∣ N₀ := by
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hpos : P - j ≠ 0 := by omega
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 hpos) _
  have hDx0 : (D : ℝ) * x 0 = (N₀ : ℝ) := by
    have hiter := dyadicCoord_iter t₀ p₀ 0 P
    have hxP : dyadicCoord (t₀ + P) (kimberlingOrbit t₀ p₀ P) = dyadicCoord t₀ p₀ := by
      simpa [x, kimberlingOrbit] using hx_per 0
    have hiter' : x 0 =
        (∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j) +
        (S : ℝ) / (2 : ℝ) ^ P * x 0 := by
      simpa [x, kimberlingOrbit, S, hxP] using hiter
    have h2P_ne : (2 : ℝ) ^ P ≠ 0 := by positivity
    have hmul : (2 : ℝ) ^ P * x 0 - (S : ℝ) * x 0 =
        (2 : ℝ) ^ P * ∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j := by
      have h1 : (2 : ℝ) ^ P * x 0 =
          (2 : ℝ) ^ P * (∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j) +
          (S : ℝ) * x 0 := by
        calc (2 : ℝ) ^ P * x 0
            = (2 : ℝ) ^ P * ((∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j) +
                (S : ℝ) / (2 : ℝ) ^ P * x 0) := by rw [← hiter']
          _ = (2 : ℝ) ^ P * (∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j) +
                ((2 : ℝ) ^ P * ((S : ℝ) / (2 : ℝ) ^ P)) * x 0 := by ring
          _ = (2 : ℝ) ^ P * (∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j) +
                (S : ℝ) * x 0 := by field_simp
      linarith
    have hsum_eq : (2 : ℝ) ^ P * ∑ j ∈ Finset.range P, (cumSign t₀ p₀ j : ℝ) / (2 : ℝ) ^ j =
        (N₀ : ℝ) := by
      rw [Finset.mul_sum]
      simp only [N₀, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hpow : (2 : ℝ) ^ P = (2 : ℝ) ^ (P - j) * (2 : ℝ) ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj)]
      have h2j_ne : (2 : ℝ) ^ j ≠ 0 := by positivity
      rw [hpow]
      field_simp
    calc (D : ℝ) * x 0 = (2 : ℝ) ^ P * x 0 - (S : ℝ) * x 0 := by
          simp only [D, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]; ring
      _ = (N₀ : ℝ) := by rw [hmul, hsum_eq]
  -- Represent x 0 as reduced fraction r = a / q in ℚ
  let r : ℚ := (N₀ : ℚ) / (D : ℚ)
  let a : ℤ := r.num
  let q : ℕ := r.den
  have hq_pos : 0 < q := r.pos
  have hr_cop : Nat.Coprime a.natAbs q := r.reduced
  have hx0_rat : x 0 = (a : ℝ) / (q : ℝ) := by
    have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD_pos)
    have hr_real : (r : ℝ) = (N₀ : ℝ) / (D : ℝ) := by
      simp [r]
    have hr_num_den : (r : ℝ) = (a : ℝ) / (q : ℝ) := by
      dsimp only [a, q]
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    calc x 0 = (N₀ : ℝ) / (D : ℝ) := (eq_div_iff hD_ne).mpr (by linarith [hDx0])
      _ = (r : ℝ) := hr_real.symm
      _ = (a : ℝ) / (q : ℝ) := hr_num_den
  -- Cross-multiplication in ℤ: a * D = N₀ * q
  have hcross : a * D = N₀ * (q : ℤ) := by
    have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq_pos)
    have hreal : ((a * D : ℤ) : ℝ) = ((N₀ * (q : ℤ) : ℤ) : ℝ) := by
      push_cast
      have h1 : (a : ℝ) = x 0 * (q : ℝ) := by
        rw [hx0_rat]; field_simp
      calc (a : ℝ) * (D : ℝ) = (x 0 * (q : ℝ)) * (D : ℝ) := by rw [h1]
        _ = ((D : ℝ) * x 0) * (q : ℝ) := by ring
        _ = (N₀ : ℝ) * (q : ℝ) := by rw [hDx0]
    exact_mod_cast hreal
  -- q is odd (since q ∣ D and D is odd)
  have hq_dvd_D : (q : ℤ) ∣ D := by
    have hdvd_nat : q ∣ a.natAbs * D.natAbs := by
      refine ⟨N₀.natAbs, ?_⟩
      have hnat := congrArg Int.natAbs hcross
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnat
      linarith
    have hq_dvd_Dnat : q ∣ D.natAbs := hr_cop.symm.dvd_of_dvd_mul_left hdvd_nat
    exact Int.natCast_dvd.mpr hq_dvd_Dnat
  have hq_odd : ¬ (2 ∣ q) := by
    intro h2q
    have h2q_int : (2 : ℤ) ∣ (q : ℤ) := by exact_mod_cast h2q
    exact hD_odd (dvd_trans h2q_int hq_dvd_D)
  -- a is even (since 2 ∣ N₀ * q = a * D and D is odd)
  have ha_even : (2 : ℤ) ∣ a := by
    have h2_aD : (2 : ℤ) ∣ a * D := by
      rw [hcross]
      exact dvd_mul_of_dvd_left hN₀_even (q : ℤ)
    have hD_mod : D % 2 = 1 := by
      have : D % 2 ≠ 0 := fun h => hD_odd (Int.dvd_of_emod_eq_zero h)
      omega
    have haD_mod : (a * D) % 2 = 0 := Int.emod_eq_zero_of_dvd h2_aD
    rw [Int.mul_emod, hD_mod, mul_one, Int.emod_emod] at haD_mod
    exact Int.dvd_of_emod_eq_zero haD_mod
  -- From 0 < x 0 < 2 we get 0 < a < 2 * q, and since a is even and q is odd, q ≥ 3
  have ha_bounds : 0 < a ∧ a < 2 * (q : ℤ) := by
    have hx0_b := hx_bounds 0
    have hq_rpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
    rw [hx0_rat, div_pos_iff_of_pos_right hq_rpos, div_lt_iff₀ hq_rpos] at hx0_b
    constructor
    · exact_mod_cast hx0_b.1
    · exact_mod_cast hx0_b.2
  have hq_gt_one : 1 < q := by
    rcases ha_even with ⟨c, hc⟩
    omega
  -- Propagate numerators a_k along the tent-map orbit: x k = a_k / q
  let numSeq : ℕ → ℤ := fun k =>
    Nat.rec (motive := fun _ => ℤ) a (fun n prev => 2 * stepSign t₀ p₀ n * (prev - (q : ℤ))) k
  have hnum_spec : ∀ k,
      x k = (Int.cast (numSeq k) : ℝ) / (q : ℝ) ∧
      (2 : ℤ) ∣ numSeq k ∧
      0 < numSeq k ∧ numSeq k < 2 * (q : ℤ) ∧
      Nat.Coprime (numSeq k).natAbs q := by
    intro k
    induction k with
    | zero =>
      exact ⟨hx0_rat, ha_even, ha_bounds.1, ha_bounds.2, hr_cop⟩
    | succ m ih =>
      rcases ih with ⟨hx_m, heven_m, hpos_m, hlt_m, hcop_m⟩
      have hstep_m : numSeq (m + 1) = 2 * stepSign t₀ p₀ m * (numSeq m - (q : ℤ)) := rfl
      have hx_succ : x (m + 1) = (Int.cast (numSeq (m + 1)) : ℝ) / (q : ℝ) := by
        have hsucc := dyadicCoord_succ_eq t₀ p₀ m
        have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq_pos)
        change dyadicCoord (t₀ + (m + 1)) (kimberlingOrbit t₀ p₀ (m + 1)) = _
        rw [hsucc, hstep_m]
        change 2 * (stepSign t₀ p₀ m : ℝ) * (x m - 1) = _
        rw [hx_m]
        push_cast
        field_simp
      have heven_succ : (2 : ℤ) ∣ numSeq (m + 1) := by
        rw [hstep_m]
        exact ⟨stepSign t₀ p₀ m * (numSeq m - (q : ℤ)), by ring⟩
      have hbounds_succ : 0 < numSeq (m + 1) ∧ numSeq (m + 1) < 2 * (q : ℤ) := by
        have hxb := hx_bounds (m + 1)
        have hq_rpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
        rw [hx_succ, div_pos_iff_of_pos_right hq_rpos, div_lt_iff₀ hq_rpos] at hxb
        exact ⟨by exact_mod_cast hxb.1, by exact_mod_cast hxb.2⟩
      have hcop_succ : Nat.Coprime (numSeq (m + 1)).natAbs q := by
        have hs_abs : (stepSign t₀ p₀ m).natAbs = 1 := by
          rcases stepSign_eq_neg_one_or_one t₀ p₀ m with hs | hs <;> simp [hs]
        have hnat_abs : (numSeq (m + 1)).natAbs = 2 * (numSeq m - (q : ℤ)).natAbs := by
          rw [hstep_m, Int.natAbs_mul, Int.natAbs_mul, hs_abs]
          norm_num
        rw [hnat_abs]
        have hcop_2 : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr hq_odd
        have hcop_sub : Nat.Coprime (numSeq m - (q : ℤ)).natAbs q := by
          rw [Nat.coprime_iff_gcd_eq_one]
          set d := Nat.gcd (numSeq m - (q : ℤ)).natAbs q
          have hd1 : (d : ℤ) ∣ numSeq m - (q : ℤ) := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
          have hd2 : (d : ℤ) ∣ (q : ℤ) := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
          have hd_num : (d : ℤ) ∣ numSeq m := by
            have := dvd_add hd1 hd2
            simpa using this
          have hd_nat : d ∣ (numSeq m).natAbs := Int.natCast_dvd.mp hd_num
          have hd_q : d ∣ q := Nat.gcd_dvd_right _ _
          have hd_gcd : d ∣ Nat.gcd (numSeq m).natAbs q := Nat.dvd_gcd hd_nat hd_q
          rw [hcop_m.gcd_eq_one] at hd_gcd
          exact Nat.eq_one_of_dvd_one hd_gcd
        exact hcop_2.mul_left hcop_sub
      exact ⟨hx_succ, heven_succ, hbounds_succ.1, hbounds_succ.2, hcop_succ⟩
  -- Inject Finset.range P into (Finset.range q).filter q.Coprime via k ↦ (numSeq k / 2).toNat
  let halfSeq : ℕ → ℕ := fun k => (numSeq k / 2).toNat
  have hmaps : ∀ k ∈ Finset.range P, halfSeq k ∈ (Finset.range q).filter q.Coprime := by
    intro k _
    rcases hnum_spec k with ⟨_, ⟨c, hc⟩, hpos_k, hlt_k, hcop_k⟩
    have hhalf_eq : numSeq k / 2 = c := by rw [hc]; omega
    have hc_pos : 0 < c := by omega
    have hc_lt : c < (q : ℤ) := by omega
    have hhalf_nat : (halfSeq k : ℤ) = c := by
      dsimp only [halfSeq]
      rw [hhalf_eq]
      exact Int.toNat_of_nonneg (le_of_lt hc_pos)
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact_mod_cast (show (halfSeq k : ℤ) < (q : ℤ) by linarith)
    · have h2c : (numSeq k).natAbs = 2 * halfSeq k := by
        have h1 : ((numSeq k).natAbs : ℤ) = (2 * halfSeq k : ℕ) := by
          rw [Int.natAbs_of_nonneg (le_of_lt hpos_k), hc]
          push_cast; linarith [hhalf_nat]
        exact_mod_cast h1
      rw [h2c] at hcop_k
      exact (Nat.coprime_mul_iff_left.mp hcop_k).2.symm
  have hinj : Set.InjOn halfSeq (Finset.range P : Set ℕ) := by
    intro i hi j hj hij
    rcases hnum_spec i with ⟨hxi, ⟨ci, hci⟩, hposi, _, _⟩
    rcases hnum_spec j with ⟨hxj, ⟨cj, hcj⟩, hposj, _, _⟩
    have hci_eq : (halfSeq i : ℤ) = ci := by
      dsimp only [halfSeq]
      have : numSeq i / 2 = ci := by rw [hci]; omega
      rw [this]; exact Int.toNat_of_nonneg (by omega)
    have hcj_eq : (halfSeq j : ℤ) = cj := by
      dsimp only [halfSeq]
      have : numSeq j / 2 = cj := by rw [hcj]; omega
      rw [this]; exact Int.toNat_of_nonneg (by omega)
    have hnum_eq : numSeq i = numSeq j := by
      have : (halfSeq i : ℤ) = (halfSeq j : ℤ) := by exact_mod_cast hij
      omega
    have hx_eq : x i = x j := by rw [hxi, hxj, hnum_eq]
    exact hx_inj i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hx_eq
  -- Upper bound: P ≤ φ(q) < q
  have hP_le_totient : P ≤ q.totient := by
    rw [Nat.totient]
    calc P = (Finset.range P).card := (Finset.card_range P).symm
      _ ≤ ((Finset.range q).filter q.Coprime).card :=
        Finset.card_le_card_of_injOn halfSeq hmaps hinj
  have htot_lt : q.totient < q := by
    calc q.totient = ((Finset.range q).filter q.Coprime).card := rfl
      _ < (Finset.range q).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
        have h0 : 0 ∈ (Finset.range q).filter q.Coprime := by
          rw [heq, Finset.mem_range]; omega
        rw [Finset.mem_filter] at h0
        have hgcd : q.gcd 0 = 1 := h0.2
        simp at hgcd
        omega
      _ = q := Finset.card_range q
  have hP_lt_q : P < q := lt_of_le_of_lt hP_le_totient htot_lt
  -- Lower bound: q ∣ P, hence q ≤ P
  have hdiff := orbit_period_diff_eq hlo hhi hne hP_per
  have hdiff_int : ((kimberlingOrbit t₀ p₀ P : ℤ) - (p₀ : ℤ)) * (q : ℤ) = (P : ℤ) * a := by
    have hq_ne : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq_pos)
    have hreal : ((((kimberlingOrbit t₀ p₀ P : ℤ) - (p₀ : ℤ)) * (q : ℤ) : ℤ) : ℝ) =
        (((P : ℤ) * a : ℤ) : ℝ) := by
      push_cast
      rw [← hx0_eq, hx0_rat] at hdiff
      have hmul : ((kimberlingOrbit t₀ p₀ P : ℝ) - (p₀ : ℝ)) * (q : ℝ) =
          ((P : ℝ) * ((a : ℝ) / (q : ℝ))) * (q : ℝ) := congrArg (fun z : ℝ => z * (q : ℝ)) hdiff
      rw [mul_div_assoc', div_mul_cancel₀ _ hq_ne] at hmul
      linarith
    exact_mod_cast hreal
  have hq_dvd_P : q ∣ P := by
    have hdvd_nat : q ∣ P * a.natAbs := by
      refine ⟨((kimberlingOrbit t₀ p₀ P : ℤ) - (p₀ : ℤ)).natAbs, ?_⟩
      have hnat := congrArg Int.natAbs hdiff_int
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnat
      linarith
    exact hr_cop.symm.dvd_of_dvd_mul_right hdvd_nat
  have hq_le_P : q ≤ P := Nat.le_of_dvd hP_pos hq_dvd_P
  omega

/-- **Part 2 — Main Unconditional Structural Theorem (`kimberling_no_eventually_periodic_itinerary`):**
No never-expelled active-zone orbit `(t₀ + n, p_n)` (`1 ≤ p₀ ≤ 2t₀ - 1`) in Kimberling's
expulsion map can have an eventually periodic sign itinerary `(p_n > t₀ + n)`. -/
theorem kimberling_no_eventually_periodic_itinerary
    (t₀ p₀ : ℕ) (hp_lo : 1 ≤ p₀) (hp_hi : p₀ ≤ 2 * t₀ - 1)
    (hne : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n) :
    ¬ ∃ (N₀ P : ℕ), 0 < P ∧
      ∀ n ≥ N₀, (kimberlingOrbit t₀ p₀ (n + P) > t₀ + (n + P) ↔
                 kimberlingOrbit t₀ p₀ n > t₀ + n) := by
  rintro ⟨N₀, P, hP_pos, hper⟩
  have hb := kimberlingOrbit_bounds hp_lo hp_hi hne N₀
  have hne' : ∀ n, kimberlingOrbit (t₀ + N₀) (kimberlingOrbit t₀ p₀ N₀) n ≠ (t₀ + N₀) + n := by
    intro n
    rw [kimberlingOrbit_add, Nat.add_assoc]
    exact hne (N₀ + n)
  have hper' : ∀ n,
      stepSign (t₀ + N₀) (kimberlingOrbit t₀ p₀ N₀) (n + P) =
      stepSign (t₀ + N₀) (kimberlingOrbit t₀ p₀ N₀) n := by
    intro n
    rw [stepSign_shift, stepSign_shift]
    have hiff := hper (N₀ + n) (by omega)
    have hne1 := hne (N₀ + n)
    have hne2 := hne (N₀ + n + P)
    have hadd : N₀ + (n + P) = N₀ + n + P := by omega
    rw [hadd]
    unfold stepSign
    by_cases hlt1 : kimberlingOrbit t₀ p₀ (N₀ + n) < t₀ + (N₀ + n)
    · have hlt2 : kimberlingOrbit t₀ p₀ (N₀ + n + P) < t₀ + (N₀ + n + P) := by
        by_contra hge
        have hgt2 : kimberlingOrbit t₀ p₀ (N₀ + n + P) > t₀ + (N₀ + n + P) := by omega
        have hgt1 := hiff.mp hgt2
        omega
      simp [hlt1, hlt2]
    · have hgt1 : kimberlingOrbit t₀ p₀ (N₀ + n) > t₀ + (N₀ + n) := by omega
      have hgt2 := hiff.mpr hgt1
      have hnlt2 : ¬ (kimberlingOrbit t₀ p₀ (N₀ + n + P) < t₀ + (N₀ + n + P)) := by omega
      simp [hlt1, hnlt2]
  exact kimberling_no_purely_periodic_itinerary hb.1 hb.2 hne' ⟨P, hP_pos, hper'⟩

/-- **Full-Orbit Corollary for OEIS `A007063`:**
For every integer `m ≥ 1` whose full Kimberling expulsion orbit `(n + 1, kimberlingFullOrbit m n)`
is never expelled, its sign itinerary `(kimberlingFullOrbit m n > n + 1)` cannot be eventually
periodic. -/
theorem kimberlingFullOrbit_no_eventually_periodic_itinerary
    (m : ℕ) (hm : 1 ≤ m)
    (hne : ∀ n, kimberlingFullOrbit m n ≠ n + 1) :
    ¬ ∃ (N₀ P : ℕ), 0 < P ∧
      ∀ n ≥ N₀, (kimberlingFullOrbit m (n + P) > (n + P) + 1 ↔
                 kimberlingFullOrbit m n > n + 1) := by
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    subst hm1
    exact hne 0 a007063_m1_expelled_at_1
  -- Prove active-zone entry and orbit agreement together by induction
  set k₀ := (m + 1) / 3
  set t₀ := k₀ + 1
  set p₀ := m - k₀
  have hlo : 1 ≤ p₀ := by omega
  have hhi : p₀ ≤ 2 * t₀ - 1 := by omega
  have hfull_eq_and_bounds : ∀ n,
      kimberlingFullOrbit m (k₀ + n) = kimberlingOrbit t₀ p₀ n ∧
      1 ≤ kimberlingOrbit t₀ p₀ n ∧
      kimberlingOrbit t₀ p₀ n ≤ 2 * (t₀ + n) - 1 := by
    intro n
    induction n with
    | zero =>
      exact ⟨by simpa [kimberlingOrbit, p₀] using kimberlingFullOrbit_drift hm2 k₀ (le_refl k₀),
             hlo, by simpa [kimberlingOrbit] using hhi⟩
    | succ j ih =>
      rcases ih with ⟨heq_j, hlo_j, hhi_j⟩
      have hne_j : kimberlingOrbit t₀ p₀ j ≠ t₀ + j := by
        rw [← heq_j]
        have hstage : t₀ + j = (k₀ + j) + 1 := by omega
        rw [hstage]
        exact hne (k₀ + j)
      have hstep_eq : kimberlingFullOrbit m (k₀ + (j + 1)) = kimberlingOrbit t₀ p₀ (j + 1) := by
        have h1 : k₀ + (j + 1) = (k₀ + j) + 1 := by omega
        rw [h1, kimberlingFullOrbit, heq_j]
        have hstage : (k₀ + j) + 1 = t₀ + j := by omega
        rw [hstage, kimberlingFullStep_eq_activeStep (by omega) hhi_j]
        rfl
      have hbounds_next := kimberlingActiveStep_bounds hlo_j hhi_j hne_j
      exact ⟨hstep_eq, hbounds_next.1, by simpa [kimberlingOrbit, Nat.add_assoc] using hbounds_next.2⟩
  have hne_active : ∀ n, kimberlingOrbit t₀ p₀ n ≠ t₀ + n := by
    intro n
    rw [← (hfull_eq_and_bounds n).1]
    have hstage : t₀ + n = (k₀ + n) + 1 := by omega
    rw [hstage]
    exact hne (k₀ + n)
  rintro ⟨N₀, P, hP_pos, hper⟩
  apply kimberling_no_eventually_periodic_itinerary t₀ p₀ hlo hhi hne_active
  refine ⟨N₀, P, hP_pos, fun n hn => ?_⟩
  have hiff := hper (k₀ + n) (by omega)
  have h1 := (hfull_eq_and_bounds n).1
  have h2 := (hfull_eq_and_bounds (n + P)).1
  have hadd : k₀ + (n + P) = (k₀ + n) + P := by omega
  have hs1 : t₀ + n = (k₀ + n) + 1 := by omega
  have hs2 : t₀ + (n + P) = ((k₀ + n) + P) + 1 := by omega
  rw [← h1, ← h2, hadd, hs1, hs2]
  exact hiff

end NoPeriodic

end PPL134_KimberlingNoPeriodic
