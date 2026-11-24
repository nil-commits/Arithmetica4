/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
-/
import RHDirect.DworkZetaCore

/-!
# `RHDirect.DworkZetaLog`

The exponential/logarithm calculus needed to evaluate the Hasse–Weil zeta function.

Main results (all unconditional):
* `geom_mul_one_add_X` : `(∑ (-1)^n T^n) * (1 + T) = 1`.
* `deriv_logOf`       : `(log f)' = f⁻¹ * f'` for `f` with constant term `1`.
* `expSeries_logOf`   : `exp (log f) = f`.
* `expSeries_sum`     : `exp (∑ f i) = ∏ exp (f i)`.
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-- The geometric series `∑ (-1)^n T^n`, i.e. `(1 + T)⁻¹`. -/
def geom : PowerSeries ℚ := PowerSeries.mk fun n => (-1 : ℚ) ^ n

lemma coeff_geom (n : ℕ) : (coeff n) geom = (-1 : ℚ) ^ n := PowerSeries.coeff_mk n _

lemma sum_ite_single {c : ℚ} {N K : ℕ} (h : N < K) :
    ∑ k ∈ Finset.range K, (if k = N then c else 0) = c := by
  rw [Finset.sum_eq_single N]
  · simp
  · intro b _ hb; simp [hb]
  · intro hmem; exact absurd (Finset.mem_range.mpr h) hmem

/-- `(∑ (-1)^n T^n) * (1 + T) = 1`. -/
theorem geom_mul_one_add_X : geom * (1 + PowerSeries.X) = 1 := by
  ext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (coeff i) geom * (coeff j) (1 + PowerSeries.X : PowerSeries ℚ)) n]
  rcases n with _ | m
  · simp [coeff_geom]
  · have hstep : ∀ k ∈ Finset.range (m + 1 + 1),
        (coeff k) geom * (coeff (m + 1 - k)) (1 + PowerSeries.X : PowerSeries ℚ)
          = (if k = m + 1 then (-1 : ℚ) ^ (m + 1) else 0)
            + (if k = m then (-1 : ℚ) ^ m else 0) := by
      intro k hk
      have hk' : k ≤ m + 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hXc : (coeff (m + 1 - k)) (PowerSeries.X : PowerSeries ℚ)
          = if m + 1 - k = 1 then 1 else 0 := by
        rw [show (PowerSeries.X : PowerSeries ℚ) = PowerSeries.X ^ 1 by ring]
        rw [PowerSeries.coeff_X_pow]
      rw [coeff_geom, map_add, PowerSeries.coeff_one, hXc]
      by_cases h1 : k = m + 1
      · subst h1; simp
      · by_cases h2 : k = m
        · subst h2; simp
        · have h3 : m + 1 - k ≠ 0 := by omega
          have h4 : m + 1 - k ≠ 1 := by omega
          simp [h1, h2, h3, h4]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    rw [sum_ite_single (N := m + 1) (K := m + 1 + 1) (by omega),
      sum_ite_single (N := m) (K := m + 1 + 1) (by omega)]
    rw [PowerSeries.coeff_one, if_neg (by omega)]
    rw [pow_succ]
    ring

lemma one_add_X_mul_geom : (1 + PowerSeries.X : PowerSeries ℚ) * geom = 1 := by
  rw [mul_comm, geom_mul_one_add_X]

/-- The derivative of `log f` is `f⁻¹ * f'`, for `f` with constant term `1`. -/
theorem deriv_logOf {f : PowerSeries ℚ} (h1 : constantCoeff f = 1) :
    (d⁄dX ℚ) (PowerSeries.logOf f) = f⁻¹ * (d⁄dX ℚ) f := by
  have hf : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_sub, h1, map_one, sub_self])
  have hkey : f * PowerSeries.subst (f - 1) geom = 1 := by
    have hone : PowerSeries.subst (f - 1) (1 : PowerSeries ℚ) = 1 := by
      rw [show (1 : PowerSeries ℚ) = PowerSeries.C 1 by simp, PowerSeries.subst_C]
      simp
    have hX : PowerSeries.subst (f - 1) (PowerSeries.X : PowerSeries ℚ) = f - 1 :=
      PowerSeries.subst_X hf
    have h := congrArg (PowerSeries.subst (f - 1)) (one_add_X_mul_geom)
    rw [PowerSeries.subst_mul hf, PowerSeries.subst_add hf, hone, hX] at h
    simpa using h
  have hsub : PowerSeries.subst (f - 1) geom = f⁻¹ := by
    have hinv : f * f⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ (by rw [h1]; exact one_ne_zero)
    have hne : f ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hkey
      exact zero_ne_one hkey
    exact mul_left_cancel₀ hne (hkey.trans hinv.symm)
  rw [PowerSeries.logOf_eq, PowerSeries.derivative_subst hf, PowerSeries.deriv_log]
  change PowerSeries.subst (f - 1) geom * (d⁄dX ℚ) (f - 1) = f⁻¹ * (d⁄dX ℚ) f
  rw [hsub, map_sub, PowerSeries.derivative_one, sub_zero]

/-- **`exp (log f) = f`** for `f` with constant term `1`. -/
theorem expSeries_logOf {f : PowerSeries ℚ} (h1 : constantCoeff f = 1) :
    expSeries (PowerSeries.logOf f) = f := by
  have h0 : constantCoeff (PowerSeries.logOf f) = 0 := PowerSeries.constantCoeff_logOf h1
  refine eq_of_derivative_eq_mul (g := f⁻¹ * (d⁄dX ℚ) f) ?_ ?_ ?_
  · rw [derivative_expSeries h0, deriv_logOf h1]
  · symm
    rw [← mul_assoc, PowerSeries.mul_inv_cancel f (by rw [h1]; exact one_ne_zero), one_mul]
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    rw [constantCoeff_expSeries h0, h1]

lemma constantCoeff_finset_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ)
    (hF : ∀ i ∈ s, constantCoeff (F i) = 0) :
    constantCoeff (∑ i ∈ s, F i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, map_add, hF a (Finset.mem_insert_self a s),
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)), zero_add]

/-- **`exp` is multiplicative over finite sums.** -/
theorem expSeries_sum {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ)
    (hF : ∀ i ∈ s, constantCoeff (F i) = 0) :
    expSeries (∑ i ∈ s, F i) = ∏ i ∈ s, expSeries (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      expSeries_add (hF a (Finset.mem_insert_self a s))
        (constantCoeff_finset_sum s F (fun i hi => hF i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

end

end HasseWeil
end RHDirect
