/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign, Gap 3: the trace → Fredholm-determinant identity

The algebraic heart of Dwork's method: for a square matrix `A` over a char-0 field,
`exp(∑_{r≥1} Tr(A^r) T^r/r) · det(1 - T·A) = 1`.
Equivalently the trace generating series is `-log det(1 - T·A)`. This converts the point
counts produced by Dwork's trace formula (traces of the Dwork operator) into a Fredholm
determinant, so the zeta function becomes a ratio of (p-adic entire) determinants.

Proof: by `PowerSeries.derivative.ext`, it suffices to show the derivative of the product is
zero and its constant term is `1`. The derivative computation is Jacobi's formula
`d/dT det M = Tr(adjugate M · dM/dT)` applied to `M = 1 - T·A`, together with the geometric
series `(1 - T·A)⁻¹ = ∑ T^n A^n`.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import RHDirect.DworkRatZeta
import RHDirect.Stage3DworkFrobenius

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

noncomputable section

namespace RHDirect.DworkRat

open PowerSeries Finset BigOperators Matrix

variable {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]

/-- The trace generating series `∑_{r≥1} Tr(A^r) T^r/r`. -/
def traceLog {N : ℕ} (A : Matrix (Fin N) (Fin N) K) : PowerSeries K :=
  PowerSeries.mk fun r => if r = 0 then 0 else (A ^ r).trace / (r : K)

theorem constantCoeff_traceLog {N : ℕ} (A : Matrix (Fin N) (Fin N) K) :
    PowerSeries.constantCoeff (traceLog A) = 0 := by
  simp [traceLog]

theorem coeff_traceLog {N : ℕ} (A : Matrix (Fin N) (Fin N) K) (r : ℕ) :
    PowerSeries.coeff r (traceLog A) = if r = 0 then 0 else (A ^ r).trace / (r : K) := by
  simp [traceLog]

/-- The derivative of the trace generating series is `∑_{n≥0} Tr(A^{n+1}) T^n`. -/
theorem derivative_traceLog {N : ℕ} (A : Matrix (Fin N) (Fin N) K) :
    PowerSeries.derivative K (traceLog A) =
      PowerSeries.mk fun n => (A ^ (n + 1)).trace := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_traceLog, if_neg (Nat.succ_ne_zero n),
    PowerSeries.coeff_mk]
  have hne : ((n + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hne]
  push_cast
  ring

/-- The geometric-series matrix `∑_{n≥0} T^n A^n`, entrywise a power series. -/
def geomSeries {N : ℕ} (A : Matrix (Fin N) (Fin N) K) :
    Matrix (Fin N) (Fin N) (PowerSeries K) :=
  fun i j => PowerSeries.mk fun n => (A ^ n) i j

theorem coeff_geomSeries {N : ℕ} (A : Matrix (Fin N) (Fin N) K) (i j : Fin N) (n : ℕ) :
    PowerSeries.coeff n (geomSeries A i j) = (A ^ n) i j := by
  simp [geomSeries]

private theorem coeff_X_mul (n : ℕ) (f : PowerSeries K) :
    PowerSeries.coeff n (PowerSeries.X * f) =
      if n = 0 then 0 else PowerSeries.coeff (n - 1) f := by
  rcases n with _ | n
  · simp [PowerSeries.coeff_zero_X_mul]
  · simp [PowerSeries.coeff_succ_X_mul]

/-- Multiplying the constant-entry matrix `A.map C` by the geometric series shifts the
power: `(A.map C · S) i j = ∑ T^n (A^{n+1}) i j`. -/
theorem mapC_mul_geomSeries {N : ℕ} (A : Matrix (Fin N) (Fin N) K) :
    A.map (fun x : K => PowerSeries.C x) * geomSeries A =
      fun i j => PowerSeries.mk fun n => (A ^ (n + 1)) i j := by
  ext i j n
  simp only [Matrix.mul_apply, Matrix.map_apply, PowerSeries.coeff_mk, coeff_geomSeries,
    PowerSeries.coeff_C_mul, map_sum]
  rw [pow_succ', Matrix.mul_apply]

/-- **Geometric-series inverse**: `(1 - T·A) · (∑ T^n A^n) = 1`. -/
theorem one_sub_X_smul_mul_geomSeries {N : ℕ} (A : Matrix (Fin N) (Fin N) K) :
    ((1 : Matrix (Fin N) (Fin N) (PowerSeries K)) -
        (PowerSeries.X : PowerSeries K) •
          (A.map (fun x : K => PowerSeries.C x))) * geomSeries A =
      (1 : Matrix (Fin N) (Fin N) (PowerSeries K)) := by
  ext i j n
  simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.map_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  have h1 : ∑ k : Fin N, (if i = k then (1 : PowerSeries K) else 0) * geomSeries A k j =
      geomSeries A i j := by
    have : ∑ k : Fin N, (if i = k then (1 : PowerSeries K) else 0) * geomSeries A k j =
        ∑ k : Fin N, if k = i then geomSeries A k j else 0 := by
      apply Finset.sum_congr rfl; intro k _
      by_cases h : k = i
      · simp [h]
      · simp [h, Ne.symm h]
    rw [this, Finset.sum_ite_eq']; simp
  have h2 : ∑ k : Fin N, (PowerSeries.X * PowerSeries.C (A i k)) * geomSeries A k j =
      PowerSeries.X * ∑ k : Fin N, PowerSeries.C (A i k) * geomSeries A k j := by
    simp [Finset.mul_sum, mul_assoc]
  rw [h1, h2]
  simp only [geomSeries, PowerSeries.coeff_mk, map_sub, coeff_X_mul, map_sum,
    PowerSeries.coeff_C_mul]
  rcases n with _ | n
  · simp [pow_zero, Matrix.one_apply]
  · simp only [Nat.add_sub_cancel]
    simp
    have hsum : ∑ x : Fin N, A i x * (A ^ n) x j = (A ^ (n + 1)) i j := by
      rw [← Matrix.mul_apply, ← pow_succ']
    rw [hsum, sub_self]
    split_ifs <;> simp [PowerSeries.coeff_one]

end RHDirect.DworkRat
