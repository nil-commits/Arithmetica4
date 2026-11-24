import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Vinogradov's three-primes theorem — Wave 1 foundations: the prime exponential sum

`S_N(α) = ∑_{p ≤ N, p prime} (log p) · e(p α)` with `e(x) = exp(2π i x)`.
Elementary algebraic / norm properties, the trivial `L^∞` bound, and the
orthogonality integral `∫₀¹ e(k α) dα = ite(k = 0)` for integer `k`.

All on native Mathlib objects (`Nat.Prime`, `Real.log`, `Complex.exp`,
`intervalIntegral`). No `sorry`, no custom axioms.
-/

open Real Complex Finset MeasureTheory intervalIntegral

namespace RHDirect.Vinogradov

noncomputable section

/-- The circle-method character `e(x) = exp(2π i x)`. -/
def e (x : ℝ) : ℂ := Complex.exp ((↑(2 * Real.pi * x) : ℂ) * Complex.I)

@[simp] theorem e_zero : e 0 = 1 := by
  simp [e]

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, ← Complex.exp_add]
  push_cast
  ring

theorem e_neg (x : ℝ) : e (-x) = (e x)⁻¹ := by
  simp only [e, ← Complex.exp_neg]
  push_cast
  ring

theorem e_sub (x y : ℝ) : e (x - y) = e x / e y := by
  rw [sub_eq_add_neg, e_add, e_neg, div_eq_mul_inv]

@[simp] theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp only [e]
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_ne_zero (x : ℝ) : e x ≠ 0 := by
  have h := norm_e x
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

/-- `e` is 1 on integers (periodicity). -/
@[simp] theorem e_intCast (k : ℤ) : e (k : ℝ) = 1 := by
  simp only [e]
  rw [Complex.exp_eq_one_iff]
  use k
  push_cast
  ring

/-- `e` is continuous (registered for `fun_prop`). -/
@[fun_prop] theorem continuous_e : Continuous e := by
  have he : e = fun x : ℝ => Complex.exp ((↑(2 * Real.pi) : ℂ) * (x : ℂ) * Complex.I) := by
    funext x
    simp only [e]
    push_cast
    ring
  rw [he]
  fun_prop

/-- The prime exponential sum `S_N(α) = ∑_{p ≤ N, prime} (log p) e(p α)`. -/
def S (N : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * e ((p : ℝ) * α)

@[simp] theorem S_zero (α : ℝ) : S 0 α = 0 := by
  simp only [S]
  have h : (Finset.range 1).filter Nat.Prime = ∅ := by decide
  rw [h]
  simp

/-- Trivial `L^∞` bound: `|S_N(α)| ≤ ∑_{p ≤ N} log p`. -/
theorem norm_S_le (N : ℕ) (α : ℝ) :
    ‖S N α‖ ≤ ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log (p : ℝ) := by
  simp only [S]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  have hp' : p.Prime := (Finset.mem_filter.mp hp).2
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
  simp only [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg hlog]
  exact le_rfl

/-- Orthogonality: `∫₀¹ e(k α) dα = ite(k = 0)` for integer frequency `k`. -/
theorem integral_e_mul_intCast (k : ℤ) :
    ∫ α in (0 : ℝ)..1, e ((k : ℝ) * α) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp only [hk, Int.cast_zero, zero_mul, e_zero, ite_true]
    simp [intervalIntegral.integral_const]
  · simp only [hk, ite_false]
    set c := (2 * Real.pi * (k : ℂ)) * Complex.I with hc_def
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hc : c ≠ 0 := by
      simp only [hc_def]
      refine mul_ne_zero ?_ Complex.I_ne_zero
      refine mul_ne_zero ?_ hk'
      exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    have hcong : (∫ α in (0 : ℝ)..1, e ((k : ℝ) * α)) =
        ∫ α in (0 : ℝ)..1, Complex.exp (c * α) := by
      refine intervalIntegral.integral_congr (fun α _ => ?_)
      simp only [e, hc_def]
      push_cast
      ring
    rw [hcong, integral_exp_mul_complex hc]
    have h1 : Complex.exp c = 1 := by
      simp only [hc_def]
      rw [Complex.exp_eq_one_iff]
      use k
      ring
    simp [h1]

end

#print axioms RHDirect.Vinogradov.e_intCast
#print axioms RHDirect.Vinogradov.norm_S_le
#print axioms RHDirect.Vinogradov.integral_e_mul_intCast

end RHDirect.Vinogradov
