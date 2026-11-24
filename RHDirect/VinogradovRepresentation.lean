import RHDirect.VinogradovExpSum

/-!
# Vinogradov — Wave 1b: the circle-method representation identity

The log-weighted three-prime representation count
`R_N(n) = ∑_{p₁+p₂+p₃=n, pᵢ≤N prime} log p₁ log p₂ log p₃`
equals the circle integral `∫₀¹ S_N(α)³ e(-nα) dα`.

Proof: expand the cube into a triple prime sum, combine exponentials, exchange
the finite sum with the integral, and apply integer-frequency orthogonality.
Native Mathlib objects throughout; no `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- Primes `≤ N` as a finset. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

theorem S_eq (N : ℕ) (α : ℝ) :
    S N α = ∑ p ∈ primesUpTo N, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * α) := rfl

/-- Log-weighted representation count of `n` as a sum of three primes `≤ N`. -/
def R (N n : ℕ) : ℝ :=
  ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
    if p₁ + p₂ + p₃ = n then
      Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) else 0

/-- General cube of a finite sum as a triple sum. -/
theorem sum_cube_general {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ s, f i) ^ 3 = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c := by
  have h2 : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ a ∈ s, ∑ b ∈ s, f a * f b := by
    rw [Finset.sum_mul_sum]
  calc (∑ i ∈ s, f i) ^ 3
      = ((∑ i ∈ s, f i) * (∑ i ∈ s, f i)) * (∑ i ∈ s, f i) := by ring
    _ = (∑ a ∈ s, ∑ b ∈ s, f a * f b) * (∑ c ∈ s, f c) := by rw [h2]
    _ = ∑ a ∈ s, ∑ c ∈ s, (∑ b ∈ s, f a * f b) * f c := by rw [Finset.sum_mul_sum]
    _ = ∑ a ∈ s, ∑ c ∈ s, ∑ b ∈ s, (f a * f b) * f c := by simp only [Finset.sum_mul]
    _ = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c := by
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_comm]

/-- Expand the cube of the prime exponential sum into a triple sum. -/
theorem S_cube (N : ℕ) (α : ℝ) :
    (S N α) ^ 3 =
      ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
        (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
          e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) := by
  simp only [S_eq]
  rw [sum_cube_general]
  apply Finset.sum_congr rfl; intro p₁ _
  apply Finset.sum_congr rfl; intro p₂ _
  apply Finset.sum_congr rfl; intro p₃ _
  have he : e ((p₁ : ℝ) * α) * e ((p₂ : ℝ) * α) * e ((p₃ : ℝ) * α) =
      e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) := by
    rw [← e_add, ← e_add]
    congr 1
    push_cast
    ring
  calc ((Real.log (p₁ : ℝ) : ℂ) * e ((p₁ : ℝ) * α)) *
        ((Real.log (p₂ : ℝ) : ℂ) * e ((p₂ : ℝ) * α)) *
        ((Real.log (p₃ : ℝ) : ℂ) * e ((p₃ : ℝ) * α))
      = ((Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ)) *
          (e ((p₁ : ℝ) * α) * e ((p₂ : ℝ) * α) * e ((p₃ : ℝ) * α)) := by ring
    _ = (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
          e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) := by rw [he]

/-- Integer subtraction vanishes iff the naturals agree. -/
theorem sum_eq_iff (p₁ p₂ p₃ n : ℕ) :
    ((p₁ + p₂ + p₃ : ℤ) - n = 0) ↔ p₁ + p₂ + p₃ = n := by
  constructor <;> intro h <;> omega

/-- Integral of a single triple-sum term, via orthogonality. -/
theorem integral_term (p₁ p₂ p₃ n : ℕ) :
    (∫ α in (0 : ℝ)..1,
        (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
          e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) * e (-(n : ℝ) * α)) =
      (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) *
        (if p₁ + p₂ + p₃ = n then 1 else 0) := by
  set k : ℤ := (p₁ + p₂ + p₃ : ℤ) - n with hk
  have hcong :
      (∫ α in (0 : ℝ)..1,
          (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
            e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) * e (-(n : ℝ) * α)) =
        (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) *
          ∫ α in (0 : ℝ)..1, e ((k : ℝ) * α) := by
    calc (∫ α in (0 : ℝ)..1,
            (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
              e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) * e (-(n : ℝ) * α))
        = ∫ α in (0 : ℝ)..1,
            (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) *
              (e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) * e (-(n : ℝ) * α)) := by
          refine intervalIntegral.integral_congr (fun α _ => ?_)
          push_cast
          ring
      _ = ∫ α in (0 : ℝ)..1,
            (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) * e ((k : ℝ) * α) := by
          refine intervalIntegral.integral_congr (fun α _ => ?_)
          rw [← e_add]
          congr 1
          congr 1
          simp only [hk]
          push_cast
          ring
      _ = (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) *
            ∫ α in (0 : ℝ)..1, e ((k : ℝ) * α) := by
          rw [intervalIntegral.integral_const_mul]
  rw [hcong, integral_e_mul_intCast]
  simp only [hk, sum_eq_iff]

/-- Integrability of a pointwise finite sum, in `fun x => ∑ i, f i x` form. -/
lemma intervalIntegrable_sum_fun {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume (0 : ℝ) 1) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume (0 : ℝ) 1 := by
  have heq : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp only [Finset.sum_apply]
  rw [heq]
  exact IntervalIntegrable.sum s h

/-- Exchange the integral with the triple finite sum. -/
theorem integral_triple_sum (N : ℕ) (F : ℕ → ℕ → ℕ → ℝ → ℂ)
    (hF : ∀ p₁ p₂ p₃, IntervalIntegrable (F p₁ p₂ p₃) volume (0 : ℝ) 1) :
    (∫ α in (0 : ℝ)..1,
        ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N, F p₁ p₂ p₃ α) =
      ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
        ∫ α in (0 : ℝ)..1, F p₁ p₂ p₃ α := by
  have h2 (p₁ : ℕ) :
      IntervalIntegrable (fun α => ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N, F p₁ p₂ p₃ α)
        volume (0 : ℝ) 1 :=
    intervalIntegrable_sum_fun (primesUpTo N) (fun p₂ α => ∑ p₃ ∈ primesUpTo N, F p₁ p₂ p₃ α)
      (fun p₂ _ => intervalIntegrable_sum_fun (primesUpTo N) (F p₁ p₂) (fun p₃ _ => hF p₁ p₂ p₃))
  rw [intervalIntegral.integral_finsetSum (fun p₁ _ => h2 p₁)]
  apply Finset.sum_congr rfl; intro p₁ _
  rw [intervalIntegral.integral_finsetSum (fun p₂ _ =>
    intervalIntegrable_sum_fun (primesUpTo N) (F p₁ p₂) (fun p₃ _ => hF p₁ p₂ p₃))]
  apply Finset.sum_congr rfl; intro p₂ _
  rw [intervalIntegral.integral_finsetSum (fun p₃ _ => hF p₁ p₂ p₃)]

/-- The representation identity: `R_N(n) = ∫₀¹ S_N(α)³ e(-nα) dα`. -/
theorem R_eq_integral (N n : ℕ) :
    (R N n : ℂ) = ∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α) := by
  have hswap :
      (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α)) =
        ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
          (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) *
            (if p₁ + p₂ + p₃ = n then 1 else 0) := by
    calc (∫ α in (0 : ℝ)..1, (S N α) ^ 3 * e (-(n : ℝ) * α))
        = ∫ α in (0 : ℝ)..1,
            ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
              (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
                e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) * e (-(n : ℝ) * α) := by
          simp only [S_cube, Finset.sum_mul]
      _ = ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
            ∫ α in (0 : ℝ)..1,
              (Real.log (p₁ : ℝ) : ℂ) * (Real.log (p₂ : ℝ) : ℂ) * (Real.log (p₃ : ℝ) : ℂ) *
                e (((p₁ + p₂ + p₃ : ℕ) : ℝ) * α) * e (-(n : ℝ) * α) := by
          apply integral_triple_sum
          intro p₁ p₂ p₃
          apply Continuous.intervalIntegrable
          fun_prop
      _ = ∑ p₁ ∈ primesUpTo N, ∑ p₂ ∈ primesUpTo N, ∑ p₃ ∈ primesUpTo N,
            (Real.log (p₁ : ℝ) * Real.log (p₂ : ℝ) * Real.log (p₃ : ℝ) : ℂ) *
              (if p₁ + p₂ + p₃ = n then 1 else 0) := by
          apply Finset.sum_congr rfl; intro p₁ _
          apply Finset.sum_congr rfl; intro p₂ _
          apply Finset.sum_congr rfl; intro p₃ _
          exact integral_term p₁ p₂ p₃ n
  rw [hswap]
  simp only [R]
  push_cast
  apply Finset.sum_congr rfl; intro p₁ _
  apply Finset.sum_congr rfl; intro p₂ _
  apply Finset.sum_congr rfl; intro p₃ _
  split_ifs with h
  · push_cast; ring
  · push_cast; ring

end

#print axioms RHDirect.Vinogradov.R_eq_integral

end RHDirect.Vinogradov
