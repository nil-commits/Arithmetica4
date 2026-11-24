/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign, Wave 2: the Borel–Dwork integrality core

The analytic engine of Dwork's proof of Weil Conjecture I is the Borel–Dwork rationality
criterion: a power series with integer coefficients, positive archimedean radius of
convergence, and p-adic meromorphic continuation is rational. Its heart is an integrality
argument: a nonzero integer divisible by `p^k` has archimedean absolute value `≥ p^k`, so an
integer that is both p-adically very small and archimedean-bounded must be zero.

This file builds that integrality core and the p-adic norm facts on Mathlib's native
`Padic` / `PadicInt` / `padicValInt`.
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

noncomputable section

namespace RHDirect.DworkRat

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The Borel integrality lemma -/

omit hp in
/-- A nonzero integer divisible by `p^k` has archimedean absolute value at least `p^k`. -/
theorem int_natAbs_ge_pow_of_dvd {k : ℕ} {z : ℤ} (hz : z ≠ 0)
    (hdvd : (p ^ k : ℤ) ∣ z) : p ^ k ≤ z.natAbs := by
  obtain ⟨m, hm⟩ := hdvd
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact hz hm
  have h1 : 1 ≤ m.natAbs := Int.natAbs_pos.mpr hm0
  have hz' : z.natAbs = p ^ k * m.natAbs := by
    rw [hm, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  rw [hz']
  calc p ^ k ≤ p ^ k * 1 := by simp
    _ ≤ p ^ k * m.natAbs := Nat.mul_le_mul_left _ h1

omit hp in
/-- **Borel integrality.** An integer divisible by `p^k` whose archimedean absolute value is
strictly less than `p^k` must be zero. -/
theorem eq_zero_of_dvd_and_natAbs_lt {k : ℕ} {z : ℤ}
    (hdvd : (p ^ k : ℤ) ∣ z) (hlt : z.natAbs < p ^ k) : z = 0 := by
  by_contra hz
  have := int_natAbs_ge_pow_of_dvd hz hdvd
  omega

/-! ### p-adic norm of integers -/

/-- The p-adic norm of an integer is at most 1. -/
theorem padic_norm_intCast_le_one (z : ℤ) : ‖(z : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_int_le_one z

/-- **p-adic smallness ↔ divisibility.** An integer has p-adic norm `≤ p^{-k}` iff it is
divisible by `p^k`. This is the bridge between the p-adic and archimedean worlds in the
Borel–Dwork argument. -/
theorem padic_norm_le_pow_iff_dvd (z : ℤ) (k : ℕ) :
    ‖(z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) ↔ (p ^ k : ℤ) ∣ z :=
  Padic.norm_int_le_pow_iff_dvd z k

/-- **Borel integrality, p-adic form.** An integer whose p-adic norm is `≤ p^{-k}` and whose
archimedean absolute value is `< p^k` must be zero. -/
theorem eq_zero_of_padic_norm_le_and_natAbs_lt {z : ℤ} {k : ℕ}
    (hpad : ‖(z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ))) (harch : z.natAbs < p ^ k) : z = 0 :=
  eq_zero_of_dvd_and_natAbs_lt ((padic_norm_le_pow_iff_dvd z k).mp hpad) harch

end RHDirect.DworkRat
