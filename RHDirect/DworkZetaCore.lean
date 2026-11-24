/-
Copyright: reference implementation for the ORACLE P3 (Dwork / Hasse–Weil) campaign.
No `sorry`, no custom axioms, no `native_decide`.
-/
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Tactic

/-!
# `RHDirect.DworkZetaCore`

The dimension-`0` stratum of Dwork's rationality theorem (Weil I).

For a finite type `V` with a permutation `σ` (the Frobenius), the Hasse–Weil zeta function is
`Z(V, T) = exp (∑_{m ≥ 1} N_m T^m / m)` where `N_m = #Fix(σ^m)`.  The theorem is that `Z` is
rational, with the explicit denominator `∏_c (1 - T^{|c|})` ranging over the cycles `c` of `σ`.

Nothing here is conditional: every statement is proved from Mathlib.  This file supplies

* `expSeries`, `expSeries_add`, `expSeries_logOf` — the missing functional equations for
  `PowerSeries.exp` regarded as `exp` of a series with zero constant term, proved by the
  uniqueness of solutions of the linear ODE `y' = y * g`, `y(0) = 1`;
* `fixedCount`, `zetaLog`, `zetaFinite`, `cycleProduct`;
* `zetaFinite_cyclic`, `zetaFinite_prod`, and the headline `zetaFinite_mul_cycleProduct`.
-/

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-! ## 0.  Exponential and logarithm of a power series -/

/-- `expSeries A = ∑_{n ≥ 0} A^n / n!`, i.e. `PowerSeries.exp` substituted at `A`.
For `A` with zero constant term this is the usual exponential of a formal power series. -/
def expSeries (A : PowerSeries ℚ) : PowerSeries ℚ := PowerSeries.subst A (PowerSeries.exp ℚ)

@[simp] lemma expSeries_zero : expSeries 0 = 1 := by
  unfold expSeries
  rw [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp]
  simp

lemma hasSubst_of_constantCoeff_zero {A : PowerSeries ℚ} (h : constantCoeff A = 0) :
    HasSubst A := HasSubst.of_constantCoeff_zero' h

lemma constantCoeff_add_zero {A B : PowerSeries ℚ} (hA : constantCoeff A = 0)
    (hB : constantCoeff B = 0) : constantCoeff (A + B) = 0 := by
  rw [map_add, hA, hB, add_zero]

@[simp] lemma constantCoeff_expSeries {A : PowerSeries ℚ} (hA : constantCoeff A = 0) :
    constantCoeff (expSeries A) = 1 := by
  have hA' : MvPowerSeries.constantCoeff A = 0 := by
    rwa [← PowerSeries.constantCoeff_eq]
  unfold expSeries
  rw [PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_subst (hasSubst_of_constantCoeff_zero hA)]
  rw [finsum_eq_single (fun d => (coeff d) (PowerSeries.exp ℚ) •
    MvPowerSeries.constantCoeff (A ^ d)) 0]
  · simp
  · intro d hd
    rw [map_pow, hA', zero_pow hd, smul_zero]

/-- The derivative of `expSeries A`. -/
lemma derivative_expSeries {A : PowerSeries ℚ} (hA : constantCoeff A = 0) :
    (d⁄dX ℚ) (expSeries A) = expSeries A * (d⁄dX ℚ) A := by
  unfold expSeries
  rw [PowerSeries.derivative_subst (hasSubst_of_constantCoeff_zero hA),
    PowerSeries.derivative_exp]

/-- **Uniqueness for the linear ODE `y' = y * g`.**  Two power series over `ℚ` with the same
derivative relation and the same constant term coincide. -/
theorem eq_of_derivative_eq_mul {f h g : PowerSeries ℚ}
    (hf : (d⁄dX ℚ) f = f * g) (hh : (d⁄dX ℚ) h = h * g)
    (h0 : (coeff 0) f = (coeff 0) h) : f = h := by
  set w : PowerSeries ℚ := f - h with hw
  have hw' : (d⁄dX ℚ) w = w * g := by
    rw [hw, map_sub, hf, hh, sub_mul]
  have hw0 : (coeff 0) w = 0 := by
    rw [hw, map_sub, h0, sub_self]
  have key : ∀ n, (coeff n) w = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | m
      · simpa using hw0
      · have hderiv : (coeff m) ((d⁄dX ℚ) w) = (coeff (m + 1)) w * ((m : ℚ) + 1) :=
          PowerSeries.coeff_derivative w m
        rw [hw'] at hderiv
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun i j => (coeff i) w * (coeff j) g) m] at hderiv
        have hsum : ∑ k ∈ Finset.range (m + 1), (coeff k) w * (coeff (m - k)) g = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          rw [ih k (Nat.lt_succ_of_le hk'), zero_mul]
        rw [hsum] at hderiv
        have hpos : ((m : ℚ) + 1) ≠ 0 := by positivity
        exact (mul_eq_zero.mp hderiv.symm).resolve_right hpos
  have : w = 0 := by
    ext n
    simpa using key n
  exact sub_eq_zero.mp this

/-- **`exp` is additive** (for arguments with zero constant term). -/
theorem expSeries_add {A B : PowerSeries ℚ} (hA : constantCoeff A = 0)
    (hB : constantCoeff B = 0) :
    expSeries (A + B) = expSeries A * expSeries B := by
  have hAB : constantCoeff (A + B) = 0 := constantCoeff_add_zero hA hB
  refine eq_of_derivative_eq_mul (g := (d⁄dX ℚ) A + (d⁄dX ℚ) B) ?_ ?_ ?_
  · rw [derivative_expSeries hAB, map_add]
  · rw [Derivation.leibniz, derivative_expSeries hA, derivative_expSeries hB]
    simp only [smul_eq_mul]
    ring
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    rw [constantCoeff_expSeries hAB, map_mul, constantCoeff_expSeries hA,
      constantCoeff_expSeries hB, one_mul]

@[simp] lemma expSeries_neg {A : PowerSeries ℚ} (hA : constantCoeff A = 0) :
    expSeries (-A) = (expSeries A)⁻¹ := by
  have hneg : constantCoeff (-A) = 0 := by rw [map_neg, hA, neg_zero]
  have hmul : expSeries A * expSeries (-A) = 1 := by
    rw [← expSeries_add hA hneg, add_neg_cancel, expSeries_zero]
  have hinv : expSeries A * (expSeries A)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_expSeries hA]; exact one_ne_zero)
  have hne : expSeries A ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmul
    exact zero_ne_one hmul
  exact mul_left_cancel₀ hne (hmul.trans hinv.symm)

/-! ## 1.  The zeta function of a finite `F_q`-scheme -/

/-- `N_m = #Fix(σ^m)`: the number of `F_{q^m}`-points of a finite `F_q`-scheme whose Frobenius
acts as `σ` on the underlying finite set. -/
def fixedCount {V : Type*} [Fintype V] (σ : Equiv.Perm V) (m : ℕ) : ℕ :=
  Nat.card {v : V // (σ ^ m) v = v}

/-- The logarithmic derivative data of the Hasse–Weil zeta function:
`∑_{m ≥ 1} N_m T^m / m`, as a formal power series over `ℚ`. -/
def zetaLog {V : Type*} [Fintype V] (σ : Equiv.Perm V) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (fixedCount σ n : ℚ) / n

/-- **The Hasse–Weil zeta function of a finite `F_q`-scheme**:
`Z(V, T) = exp (∑_{m ≥ 1} N_m T^m / m)`. -/
def zetaFinite {V : Type*} [Fintype V] (σ : Equiv.Perm V) : PowerSeries ℚ :=
  expSeries (zetaLog σ)

lemma constantCoeff_zetaLog {V : Type*} [Fintype V] (σ : Equiv.Perm V) :
    constantCoeff (zetaLog σ) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, zetaLog, PowerSeries.coeff_mk]
  simp

/-- The explicit denominator `∏_c (1 - T^{|c|})`, ranging over the cycles of `σ`. -/
def cycleProduct {V : Type*} [Fintype V] [DecidableEq V] (σ : Equiv.Perm V) : PowerSeries ℚ :=
  ∏ c ∈ σ.cycleFactorsFinset, (1 - PowerSeries.X ^ c.support.card)

end

end HasseWeil
end RHDirect
