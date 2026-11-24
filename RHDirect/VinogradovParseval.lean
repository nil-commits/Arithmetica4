import RHDirect.VinogradovRepresentation

/-!
# Vinogradov — Wave 1c: Parseval / the L² identity for the prime exponential sum

`∫₀¹ S_N(α) · conj(S_N(α)) dα = ∑_{p≤N prime} (log p)²`.

This is the Parseval identity for `S_N`, the `L²` input used in the minor-arc
estimate `∫_𝔪 |S|³ ≤ sup_𝔪|S| · ∫₀¹|S|²`. Proof: conjugate the sum, expand the
product into a double prime sum, exchange sum ↔ integral, apply orthogonality at
frequency `p − q`, and collapse to the diagonal. Native Mathlib; no `sorry`.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- Conjugation flips the sign of the circle character. -/
theorem e_star (x : ℝ) : star (e x) = e (-x) := by
  simp only [e]
  have hse : star (Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I)) =
      Complex.exp (star ((↑(2 * Real.pi * x) : ℂ) * Complex.I)) := by
    simp only [Complex.star_def, ← Complex.exp_conj]
  rw [hse]
  congr 1
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The conjugate of the prime exponential sum. -/
theorem S_star (N : ℕ) (α : ℝ) :
    star (S N α) = ∑ q ∈ primesUpTo N, (Real.log (q : ℝ) : ℂ) * e (-(q : ℝ) * α) := by
  simp only [S_eq, star_sum]
  apply Finset.sum_congr rfl; intro q _
  rw [star_mul, e_star]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [show (-((q : ℝ) * α)) = (-(q : ℝ)) * α by ring]
  ring

/-- Exchange the integral with a double finite sum. -/
theorem integral_double_sum (N : ℕ) (F : ℕ → ℕ → ℝ → ℂ)
    (hF : ∀ p q, IntervalIntegrable (F p q) volume (0 : ℝ) 1) :
    (∫ α in (0 : ℝ)..1, ∑ p ∈ primesUpTo N, ∑ q ∈ primesUpTo N, F p q α) =
      ∑ p ∈ primesUpTo N, ∑ q ∈ primesUpTo N, ∫ α in (0 : ℝ)..1, F p q α := by
  have h1 (p : ℕ) :
      IntervalIntegrable (fun α => ∑ q ∈ primesUpTo N, F p q α) volume (0 : ℝ) 1 :=
    intervalIntegrable_sum_fun (primesUpTo N) (F p) (fun q _ => hF p q)
  rw [intervalIntegral.integral_finsetSum (fun p _ => h1 p)]
  apply Finset.sum_congr rfl; intro p _
  rw [intervalIntegral.integral_finsetSum (fun q _ => hF p q)]

/-- Orthogonality at a difference frequency: `∫₀¹ e((p−q)α) = ite(p=q)`. -/
theorem integral_e_sub (p q : ℕ) :
    (∫ α in (0 : ℝ)..1, e (((p : ℝ) - (q : ℝ)) * α)) = if p = q then 1 else 0 := by
  set k : ℤ := (p : ℤ) - q with hk
  have hf : (fun α => e (((p : ℝ) - (q : ℝ)) * α)) = (fun α => e ((k : ℝ) * α)) := by
    funext α
    congr 1
    simp only [hk]
    push_cast
    ring
  rw [hf, integral_e_mul_intCast]
  have hiff : (k = 0) ↔ p = q := by
    simp only [hk]
    constructor <;> intro h <;> omega
  simp only [hiff]

/-- Parseval: `∫₀¹ S_N(α) conj(S_N(α)) = ∑_{p≤N} (log p)²`. -/
theorem parseval_S (N : ℕ) :
    ∫ α in (0 : ℝ)..1, S N α * star (S N α) =
      ∑ p ∈ primesUpTo N, (Real.log (p : ℝ) : ℂ) ^ 2 := by
  have hinteg :
      (∫ α in (0 : ℝ)..1, S N α * star (S N α)) =
        ∑ p ∈ primesUpTo N, ∑ q ∈ primesUpTo N,
          (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) * (if p = q then 1 else 0) := by
    calc (∫ α in (0 : ℝ)..1, S N α * star (S N α))
        = ∫ α in (0 : ℝ)..1,
            ∑ p ∈ primesUpTo N, ∑ q ∈ primesUpTo N,
              (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) * e (((p : ℝ) - (q : ℝ)) * α) := by
          refine intervalIntegral.integral_congr (fun α _ => ?_)
          rw [S_star, S_eq, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          calc ((Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * α)) *
                ((Real.log (q : ℝ) : ℂ) * e (-(q : ℝ) * α))
              = (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) *
                  (e ((p : ℝ) * α) * e (-(q : ℝ) * α)) := by ring
            _ = (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) *
                  e (((p : ℝ) - (q : ℝ)) * α) := by
                rw [← e_add]
                congr 1
                congr 1
                ring
      _ = ∑ p ∈ primesUpTo N, ∑ q ∈ primesUpTo N,
            ∫ α in (0 : ℝ)..1,
              (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) * e (((p : ℝ) - (q : ℝ)) * α) := by
          apply integral_double_sum
          intro p q
          apply Continuous.intervalIntegrable
          fun_prop
      _ = ∑ p ∈ primesUpTo N, ∑ q ∈ primesUpTo N,
            (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) * (if p = q then 1 else 0) := by
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          rw [intervalIntegral.integral_const_mul, integral_e_sub]
  rw [hinteg]
  apply Finset.sum_congr rfl; intro p hp
  calc ∑ q ∈ primesUpTo N,
        (Real.log (p : ℝ) : ℂ) * (Real.log (q : ℝ) : ℂ) * (if p = q then 1 else 0)
      = ∑ q ∈ primesUpTo N,
          (Real.log (p : ℝ) : ℂ) * ((Real.log (q : ℝ) : ℂ) * (if p = q then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro q _; ring
    _ = (Real.log (p : ℝ) : ℂ) *
        ∑ q ∈ primesUpTo N, (Real.log (q : ℝ) : ℂ) * (if p = q then 1 else 0) := by
        rw [← Finset.mul_sum]
    _ = (Real.log (p : ℝ) : ℂ) * (Real.log (p : ℝ) : ℂ) := by
        congr 1
        have hsum : (∑ q ∈ primesUpTo N, (Real.log (q : ℝ) : ℂ) * (if p = q then 1 else 0)) =
            ∑ q ∈ primesUpTo N, ite (p = q) (Real.log (q : ℝ) : ℂ) 0 := by
          apply Finset.sum_congr rfl; intro q _
          split_ifs <;> ring
        rw [hsum, Finset.sum_ite_eq]
        simp only [hp, ite_true]
    _ = (Real.log (p : ℝ) : ℂ) ^ 2 := by ring

end

#print axioms RHDirect.Vinogradov.parseval_S

end RHDirect.Vinogradov
