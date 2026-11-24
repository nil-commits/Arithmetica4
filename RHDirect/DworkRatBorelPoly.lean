/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign: Borel's theorem (holomorphic case)

The foundation of Dwork's proof of Weil Conjecture I is Borel's observation that a power
series with integer coefficients cannot be simultaneously small at the archimedean and at
the p-adic place unless it is trivial. In the holomorphic case this says:

  if `f = ∑ a_n T^n ∈ ℤ[[T]]` has archimedean radius of convergence `R_∞` and p-adic radius
  `R_p` with `R_∞ · R_p > 1`, then `f` is a polynomial.

We state it in coefficient form: archimedean growth `|a_n| ≤ C·ρ^n` together with p-adic
divisibility `p^{c·n} ∣ a_n` and `ρ < p^c` (i.e. `R_∞ = ρ^{-1}`, `R_p = p^c`, product `> 1`)
force `a_n = 0` for all large `n`. The proof is the Borel uncertainty principle
(`eq_zero_of_dvd_and_natAbs_lt`) plus exponential growth separation.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RHDirect.DworkRatBorelDwork
import RHDirect.DworkRatCriterion

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

noncomputable section

namespace RHDirect.DworkRat

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Exponential growth separation -/

/-- If `ρ < σ`, then `C·ρ^n < σ^n` for all sufficiently large `n`. -/
lemma exists_mul_pow_lt_pow {C ρ σ : ℕ} (h : ρ < σ) :
    ∃ N, ∀ n ≥ N, C * ρ ^ n < σ ^ n := by
  by_cases hρ0 : ρ = 0
  · use 1
    intro n hn
    have h0 : ρ ^ n = 0 := by rw [hρ0]; exact Nat.zero_pow (by omega)
    rw [h0, mul_zero]
    exact pow_pos (by omega) n
  · have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ0
    have hr : 1 < (σ : ℝ) / ρ := by
      rw [one_lt_div (by positivity)]
      exact_mod_cast h
    have ht := tendsto_pow_atTop_atTop_of_one_lt hr
    have hev := ht.eventually_gt_atTop (C : ℝ)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    use N
    intro n hn
    have hreal : (C : ℝ) < ((σ : ℝ) / ρ) ^ n := hN n hn
    have hdiv : ((σ : ℝ) / ρ) ^ n = (σ : ℝ) ^ n / (ρ : ℝ) ^ n := by rw [div_pow]
    rw [hdiv] at hreal
    have hρn : 0 < (ρ : ℝ) ^ n := by positivity
    have hlt : (C : ℝ) * (ρ : ℝ) ^ n < (σ : ℝ) ^ n := by
      have := mul_lt_mul_of_pos_right hreal hρn
      have hsimp : ((σ : ℝ) ^ n / (ρ : ℝ) ^ n) * (ρ : ℝ) ^ n = (σ : ℝ) ^ n := by
        field_simp
      rw [hsimp] at this
      exact this
    exact_mod_cast hlt

/-! ### Borel's theorem (holomorphic case) -/

omit hp in
/-- **Borel's theorem, coefficient form.** Integer coefficients with archimedean growth
`|a_n| ≤ C·ρ^n` and p-adic divisibility `p^{c·n} ∣ a_n`, where `ρ < p^c`, vanish eventually. -/
theorem borel_holomorphic_eventually_zero {a : ℕ → ℤ} {C ρ c : ℕ}
    (h_arch : ∀ n, (a n).natAbs ≤ C * ρ ^ n)
    (h_padic : ∀ n, (p ^ (c * n) : ℤ) ∣ a n)
    (hρ : ρ < p ^ c) :
    ∃ N, ∀ n ≥ N, a n = 0 := by
  obtain ⟨N, hN⟩ := exists_mul_pow_lt_pow hρ
  use N
  intro n hn
  have hsep : C * ρ ^ n < p ^ (c * n) := by
    rw [pow_mul]
    exact hN n hn
  have hlt : (a n).natAbs < p ^ (c * n) := lt_of_le_of_lt (h_arch n) hsep
  exact eq_zero_of_dvd_and_natAbs_lt (h_padic n) hlt

omit hp in
/-- **Borel's theorem (holomorphic case), power-series form.** Under the same hypotheses,
the power series `∑ a_n T^n` over `ℚ` is a polynomial. -/
theorem borel_holomorphic_isPolynomial {a : ℕ → ℤ} {C ρ c : ℕ}
    (h_arch : ∀ n, (a n).natAbs ≤ C * ρ ^ n)
    (h_padic : ∀ n, (p ^ (c * n) : ℤ) ∣ a n)
    (hρ : ρ < p ^ c) :
    ∃ P : Polynomial ℚ, (P : PowerSeries ℚ) = PowerSeries.mk (fun n => (a n : ℚ)) := by
  obtain ⟨N, hN⟩ := borel_holomorphic_eventually_zero h_arch h_padic hρ
  have hcoeff : ∀ n ≥ N, PowerSeries.coeff n (PowerSeries.mk (fun n => (a n : ℚ))) = 0 := by
    intro n hn
    rw [PowerSeries.coeff_mk]
    exact_mod_cast hN n hn
  exact isPolynomial_of_coeff_eq_zero hcoeff

end RHDirect.DworkRat