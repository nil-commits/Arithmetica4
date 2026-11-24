import RHDirect.VinogradovRepresentation

/-!
# Vinogradov — Wave 4: assembly (prime extraction + circle-method reduction)

Two unconditional, kernel-checked pieces of the final assembly:

1. **Prime extraction.** A positive log-weighted representation count `R_N(n) > 0`
   forces an actual triple of primes summing to `n` (every summand is nonnegative,
   so a positive sum has a positive summand, whose indicator must be `1`).
2. **Circle-method reduction.** If the real part of the circle integral
   `∫₀¹ S_N(α)³ e(-nα)` equals `main + error` with `main > 0` and `|error| < main`,
   then `n` is a sum of three primes. This packages the major-arc main term
   (`𝔖(n)·n²/2`) against the minor-arc + major-arc error.

Native Mathlib objects; no `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- Prime extraction: a positive weighted count yields a genuine prime triple. -/
theorem R_pos_implies_three_primes {N n : ℕ} (hR : 0 < R N n) :
    ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n := by
  by_contra hno
  push Not at hno
  have hsum0 : R N n = 0 := by
    simp only [R]
    apply Finset.sum_eq_zero; intro p₁ hp₁
    apply Finset.sum_eq_zero; intro p₂ hp₂
    apply Finset.sum_eq_zero; intro p₃ hp₃
    have hprime1 : p₁.Prime := (Finset.mem_filter.mp hp₁).2
    have hprime2 : p₂.Prime := (Finset.mem_filter.mp hp₂).2
    have hprime3 : p₃.Prime := (Finset.mem_filter.mp hp₃).2
    have hne : p₁ + p₂ + p₃ ≠ n := hno p₁ p₂ p₃ hprime1 hprime2 hprime3
    simp only [hne, ite_false]
  linarith

/-- Bridge: positive real part of the circle integral ⇒ three primes (via `R_eq_integral`). -/
theorem three_primes_of_integral_re_pos {N n : ℕ}
    (h : 0 < (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α)).re) :
    ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n := by
  have hre : (R N n : ℝ) = (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α)).re := by
    have := congrArg Complex.re (R_eq_integral N n)
    simpa using this
  have hR : 0 < R N n := by rw [hre]; exact h
  exact R_pos_implies_three_primes hR

/-- Circle-method assembly reduction: a dominant positive main term in the circle
integral forces a prime triple. The major arc supplies `main = 𝔖(n)·n²/2`; the
minor-arc and major-arc errors are bounded by `error`. -/
theorem vinogradov_assembly {N n : ℕ} (main error : ℝ)
    (_hmain : 0 < main) (herr : |error| < main)
    (hintegral :
      (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α)).re = main + error) :
    ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n := by
  have hpos : 0 < (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α)).re := by
    rw [hintegral]
    linarith [abs_lt.mp herr, _hmain]
  exact three_primes_of_integral_re_pos hpos

end

#print axioms RHDirect.Vinogradov.R_pos_implies_three_primes
#print axioms RHDirect.Vinogradov.vinogradov_assembly

end RHDirect.Vinogradov
