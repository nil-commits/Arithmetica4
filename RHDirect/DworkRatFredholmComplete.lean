/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign, Gap 3 (complete): Finite-Matrix Jacobi / Fredholm Identity

Unconditional proof over any characteristic-0 field `K` (`[Field K] [CharZero K] [Algebra ℚ K]`)
of the finite-matrix Jacobi / Fredholm determinant identity:

`expSeries (∑_{m≥1} Tr(A^m) T^m / m) * det(1 - T · A) = 1`

via Jacobi's derivative formula `d/dT det(M) = Tr(adjugate M · dM/dT)` applied to
`M = 1 - T · A` together with the geometric-series inverse `(1 - T · A) · (∑ T^n A^n) = 1`
from `RHDirect.DworkRatFredholm`.

Also proves:
  * `detOneSubPoly` as a polynomial in `K[X]` whose coercion to `K[[T]]` is `detOneSubMul`,
  * `expSeries_trace_eq_inv` (`expSeries (traceLog A) = (detOneSubMul A)⁻¹`),
  * rationality of `zetaOfCounts N` over `K` for any integer linear combination of matrix
    power traces `N_m = ∑_i c_i Tr(A_i^m)`,
  * rationality descent from any field extension `L / ℚ` down to `ℚ` (`isRationalPS_descent`),
    giving `ℚ`-rationality whenever `N_m ∈ ℚ`.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import RHDirect.DworkRatZeta
import RHDirect.DworkRatFredholm
import RHDirect.DworkRatCriterion

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

noncomputable section

namespace RHDirect.DworkRat

open PowerSeries Finset BigOperators Matrix

section FredholmJacobi

variable {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]

/-- The Fredholm determinant `det(1 - T · A)` in `K[[T]]` for a finite square matrix `A`. -/
def detOneSubMul {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : PowerSeries K :=
  Matrix.det ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
    (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x))

/-- The polynomial `det(1 - X · A)` in `K[X]`. -/
def detOneSubPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : Polynomial K :=
  Matrix.det ((1 : Matrix (Fin n) (Fin n) (Polynomial K)) -
    (Polynomial.X : Polynomial K) • A.map Polynomial.C)

theorem coe_detOneSubPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (detOneSubPoly A : PowerSeries K) = detOneSubMul A := by
  unfold detOneSubPoly detOneSubMul
  change Polynomial.coeToPowerSeries.ringHom
      (Matrix.det ((1 : Matrix (Fin n) (Fin n) (Polynomial K)) -
        (Polynomial.X : Polynomial K) • A.map Polynomial.C)) =
    Matrix.det ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
      (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x))
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, Polynomial.coeToPowerSeries.ringHom_apply]
  split_ifs <;> simp

theorem constantCoeff_detOneSubMul {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    PowerSeries.constantCoeff (detOneSubMul A) = 1 := by
  unfold detOneSubMul
  have hmap := (PowerSeries.constantCoeff : PowerSeries K →+* K).map_det
    ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
      (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x))
  rw [hmap]
  change (((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
      (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x)).map
        PowerSeries.constantCoeff).det = 1
  have hM : ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
      (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x)).map
        PowerSeries.constantCoeff = (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C,
      zero_mul, sub_zero]
    split_ifs <;> simp
  rw [hM, Matrix.det_one]

theorem detOneSubPoly_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    detOneSubPoly A ≠ 0 := by
  intro h
  have hcc := constantCoeff_detOneSubMul A
  rw [← coe_detOneSubPoly, h] at hcc
  simp at hcc

/-- Product rule for `PowerSeries.derivative K` over a finite product. -/
private theorem derivative_prod_ps {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → PowerSeries K) :
    PowerSeries.derivative K (∏ i ∈ s, f i) =
      ∑ j ∈ s, (∏ i ∈ s.erase j, f i) * PowerSeries.derivative K (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, ih]
    simp only [smul_eq_mul]
    rw [Finset.erase_insert ha, Finset.mul_sum]
    have hstep : ∀ j ∈ s, (∏ i ∈ (insert a s).erase j, f i) * PowerSeries.derivative K (f j) =
        f a * ((∏ i ∈ s.erase j, f i) * PowerSeries.derivative K (f j)) := by
      intro j hj
      have hne : a ≠ j := by rintro rfl; exact ha hj
      have hmem : a ∉ s.erase j := fun h => ha (Finset.mem_of_mem_erase h)
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (a := a) (s := s.erase j) hmem]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    ring

/-- Entry `(j, k)` of `M.adjugate` expressed via the Leibniz sum restricted to `k = σ j`. -/
private theorem adjugate_apply_eq_perm_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (j k : Fin n) :
    M.adjugate j k = ∑ σ : Equiv.Perm (Fin n),
      if k = σ j then (Equiv.Perm.sign σ : ℤˣ) • ∏ i ∈ univ.erase j, M (σ i) i else 0 := by
  rw [Matrix.adjugate_apply, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hσ : k = σ j
  · rw [if_pos hσ]
    congr 1
    rw [← Finset.mul_prod_erase univ (fun i => (M.updateRow k (Pi.single j 1)) (σ i) i)
      (Finset.mem_univ j)]
    have hj_factor : (M.updateRow k (Pi.single j 1)) (σ j) j = 1 := by
      rw [← hσ, Matrix.updateRow_self, Pi.single_eq_same]
    rw [hj_factor, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hσne : σ i ≠ k := fun h => hij (σ.injective (h.trans hσ))
    rw [Matrix.updateRow_ne hσne]
  · rw [if_neg hσ]
    have hzero : ∏ i : Fin n, (M.updateRow k (Pi.single j 1)) (σ i) i = 0 := by
      let i0 : Fin n := σ.symm k
      have hi0j : i0 ≠ j := fun h => hσ (by rw [← h]; simp [i0])
      refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
      have hσi0 : σ i0 = k := σ.apply_symm_apply k
      rw [hσi0, Matrix.updateRow_self, Pi.single_eq_of_ne hi0j]
    rw [hzero, smul_zero]

/-- **Jacobi's derivative formula** for a matrix of formal power series:
`d/dT det(M) = Tr(adjugate M · dM/dT)`. -/
theorem derivative_det {n : ℕ} (M : Matrix (Fin n) (Fin n) (PowerSeries K)) :
    PowerSeries.derivative K M.det =
      Matrix.trace (M.adjugate * M.map (PowerSeries.derivative K)) := by
  rw [Matrix.det_apply, map_sum]
  have hLHS : (∑ σ : Equiv.Perm (Fin n),
      PowerSeries.derivative K ((Equiv.Perm.sign σ : ℤˣ) • ∏ i : Fin n, M (σ i) i)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n,
        ((Equiv.Perm.sign σ : ℤˣ) • ∏ i ∈ univ.erase j, M (σ i) i) *
          PowerSeries.derivative K (M (σ j) j) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Units.smul_def, map_zsmul]
    rw [derivative_prod_ps, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc]
  rw [hLHS, Finset.sum_comm]
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply]
  have hRHS : (∑ k : Fin n, M.adjugate j k * PowerSeries.derivative K (M k j)) =
      ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if k = σ j then
          ((Equiv.Perm.sign σ : ℤˣ) • ∏ i ∈ univ.erase j, M (σ i) i) *
            PowerSeries.derivative K (M k j)
        else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [adjugate_apply_eq_perm_sum M j k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    split_ifs <;> simp
  rw [hRHS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_ite_eq']
  simp

/-- Right-multiplying `geomSeries A` by `A.map C` shifts the matrix power by `1`. -/
theorem geomSeries_mul_mapC {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    geomSeries A * A.map (fun x : K => PowerSeries.C x) =
      fun i j => PowerSeries.mk fun m => (A ^ (m + 1)) i j := by
  ext i j m
  simp only [Matrix.mul_apply, Matrix.map_apply, PowerSeries.coeff_mk, coeff_geomSeries,
    PowerSeries.coeff_mul_C, map_sum]
  rw [pow_succ, Matrix.mul_apply]

/-- Derivative of `1 - X • A.map C` is `-A.map C`. -/
private theorem map_derivative_one_sub_X_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    ((1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
      (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x)).map
        (PowerSeries.derivative K) =
      -(A.map (fun x : K => PowerSeries.C x)) := by
  funext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.neg_apply, smul_eq_mul, map_sub]
  have hd1 : PowerSeries.derivative K (if i = j then (1 : PowerSeries K) else 0) = 0 := by
    split_ifs <;> simp
  have hd2 : PowerSeries.derivative K ((PowerSeries.X : PowerSeries K) * PowerSeries.C (A i j)) =
      PowerSeries.C (A i j) := by
    rw [Derivation.leibniz, PowerSeries.derivative_X, PowerSeries.derivative_C]
    simp
  rw [hd1, hd2, zero_sub]

/-- **Differential equation for `detOneSubMul`**:
`d/dT det(1 - T·A) = - det(1 - T·A) * (d/dT traceLog A)`. -/
theorem derivative_detOneSubMul {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    PowerSeries.derivative K (detOneSubMul A) =
      -(detOneSubMul A * PowerSeries.derivative K (traceLog A)) := by
  let M : Matrix (Fin n) (Fin n) (PowerSeries K) :=
    (1 : Matrix (Fin n) (Fin n) (PowerSeries K)) -
      (PowerSeries.X : PowerSeries K) • A.map (fun x : K => PowerSeries.C x)
  have hM_geom : M * geomSeries A = 1 := one_sub_X_smul_mul_geomSeries A
  have hadj_geom : M.adjugate = M.det • geomSeries A := by
    have h1 : M.adjugate * (M * geomSeries A) = M.adjugate * 1 := congrArg (M.adjugate * ·) hM_geom
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul] at h1
    exact h1.symm
  have hderiv : PowerSeries.derivative K M.det =
      Matrix.trace (M.adjugate * M.map (PowerSeries.derivative K)) := derivative_det M
  rw [hadj_geom, map_derivative_one_sub_X_smul, Matrix.mul_neg, Matrix.smul_mul,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, geomSeries_mul_mapC] at hderiv
  have htr : Matrix.trace (fun i j => PowerSeries.mk fun m => (A ^ (m + 1)) i j) =
      PowerSeries.derivative K (traceLog A) := by
    rw [derivative_traceLog A]
    ext m
    simp [Matrix.trace, Matrix.diag]
  change PowerSeries.derivative K M.det = -(M.det * PowerSeries.derivative K (traceLog A))
  rw [hderiv, htr]

/-- **Finite-Matrix Jacobi / Fredholm Determinant Identity** in `traceLog` form. -/
theorem expSeries_traceLog_mul_detOneSubMul {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    expSeries (traceLog A) * detOneSubMul A = 1 := by
  apply PowerSeries.derivative.ext
  · rw [PowerSeries.derivative_one, Derivation.leibniz,
      derivative_expSeries (constantCoeff_traceLog A), derivative_detOneSubMul A]
    simp only [smul_eq_mul]
    ring
  · rw [map_mul, map_one, constantCoeff_expSeries (constantCoeff_traceLog A),
      constantCoeff_detOneSubMul A, mul_one]

/-- **Finite-Matrix Jacobi / Fredholm Determinant Identity** over any char-0 field `K`:
`exp(∑_{m≥1} Tr(A^m) T^m / m) * det(1 - T · A) = 1`. -/
theorem expSeries_trace_mul_charpoly_rev_eq_one {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    expSeries (PowerSeries.mk fun m => if m = 0 then 0 else (Matrix.trace (A ^ m)) / (m : K)) *
      detOneSubMul A = 1 :=
  expSeries_traceLog_mul_detOneSubMul A

/-- Companion inverse form: `exp(∑_{m≥1} Tr(A^m) T^m / m) = (det(1 - T · A))⁻¹`. -/
theorem expSeries_trace_eq_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    expSeries (traceLog A) = (detOneSubMul A)⁻¹ := by
  have hmul : expSeries (traceLog A) * detOneSubMul A = 1 :=
    expSeries_traceLog_mul_detOneSubMul A
  have hinv : detOneSubMul A * (detOneSubMul A)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_detOneSubMul]; exact one_ne_zero)
  calc expSeries (traceLog A)
      = expSeries (traceLog A) * 1 := (mul_one _).symm
    _ = expSeries (traceLog A) * (detOneSubMul A * (detOneSubMul A)⁻¹) := by rw [hinv]
    _ = (expSeries (traceLog A) * detOneSubMul A) * (detOneSubMul A)⁻¹ := by ring
    _ = 1 * (detOneSubMul A)⁻¹ := by rw [hmul]
    _ = (detOneSubMul A)⁻¹ := one_mul _

/-- `zetaOfCounts` of matrix power traces `m ↦ Tr(A^m)` satisfies `Z · det(1 - T·A) = 1`. -/
theorem zetaOfCounts_trace_mul_detOneSubMul {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    zetaOfCounts (fun m => (A ^ m).trace) * detOneSubMul A = 1 := by
  change expSeries (traceLog A) * detOneSubMul A = 1
  exact expSeries_traceLog_mul_detOneSubMul A

/-- `zetaOfCounts` of `m ↦ (c : ℤ) * Tr(A^m)` is rational over `K`. -/
private theorem zetaOfCounts_int_mul_trace {n : ℕ} (c : ℤ) (A : Matrix (Fin n) (Fin n) K) :
    ((if 0 ≤ c then (detOneSubPoly A) ^ c.natAbs else 1 : Polynomial K) : PowerSeries K) *
      zetaOfCounts (fun m => (c : K) * (A ^ m).trace) =
    ((if c < 0 then (detOneSubPoly A) ^ c.natAbs else 1 : Polynomial K) : PowerSeries K) := by
  have hz : zetaOfCounts (fun m => (c : K) * (A ^ m).trace) =
      if 0 ≤ c then (expSeries (traceLog A)) ^ c.natAbs
      else (detOneSubMul A) ^ c.natAbs := by
    have hlog : zetaLog (fun m => (c : K) * (A ^ m).trace) = (c : K) • traceLog A := by
      ext m
      simp only [zetaLog, traceLog, PowerSeries.coeff_mk, smul_eq_mul, PowerSeries.coeff_smul]
      split_ifs with hm
      · simp
      · ring
    rw [zetaOfCounts_eq_expSeries_zetaLog, hlog]
    by_cases hc : 0 ≤ c
    · rw [if_pos hc]
      have hcnat : (c : K) = (c.natAbs : K) := by
        have hc_eq : c = (c.natAbs : ℤ) := (Int.natAbs_of_nonneg hc).symm
        conv_lhs => rw [hc_eq]
        rw [Int.cast_natCast]
      rw [hcnat]
      clear hcnat hc hlog
      induction c.natAbs with
      | zero => simp [expSeries_zero]
      | succ k ih =>
        have hsucc : ((k + 1 : ℕ) : K) • traceLog A = (k : K) • traceLog A + traceLog A := by
          ext m
          simp only [PowerSeries.coeff_smul, smul_eq_mul, map_add]
          push_cast; ring
        have hk0 : PowerSeries.constantCoeff ((k : K) • traceLog A) = 0 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_smul,
            PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_traceLog, smul_zero]
        rw [hsucc, expSeries_add hk0 (constantCoeff_traceLog A), ih, pow_succ]
    · rw [if_neg hc]
      have hlt : c < 0 := Int.lt_of_not_ge hc
      have hcnat : (c : K) = -((c.natAbs : ℕ) : K) := by
        have hc_eq : c = -(c.natAbs : ℤ) := by omega
        conv_lhs => rw [hc_eq]
        rw [Int.cast_neg, Int.cast_natCast]
      rw [hcnat, neg_smul]
      clear hcnat hlt hc hlog
      have hdet_eq : expSeries (-traceLog A) = detOneSubMul A := by
        calc expSeries (-traceLog A)
            = expSeries (-traceLog A) * 1 := (mul_one _).symm
          _ = expSeries (-traceLog A) * (expSeries (traceLog A) * detOneSubMul A) := by
              rw [expSeries_traceLog_mul_detOneSubMul]
          _ = (expSeries (traceLog A) * expSeries (-traceLog A)) * detOneSubMul A := by ring
          _ = 1 * detOneSubMul A := by
              rw [expSeries_mul_expSeries_neg (constantCoeff_traceLog A)]
          _ = detOneSubMul A := one_mul _
      induction c.natAbs with
      | zero => simp [expSeries_zero]
      | succ k ih =>
        have hsucc : -(((k + 1 : ℕ) : K) • traceLog A) =
            -((k : K) • traceLog A) + (-traceLog A) := by
          ext m
          simp only [map_neg, map_add, PowerSeries.coeff_smul, smul_eq_mul]
          push_cast; ring
        have hk0 : PowerSeries.constantCoeff (-((k : K) • traceLog A)) = 0 := by
          rw [map_neg, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_smul,
            PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_traceLog, smul_zero, neg_zero]
        have ht0 : PowerSeries.constantCoeff (-traceLog A) = 0 := by
          rw [map_neg, constantCoeff_traceLog, neg_zero]
        rw [hsucc, expSeries_add hk0 ht0, ih, hdet_eq, pow_succ]
  rw [hz]
  by_cases hc : 0 ≤ c
  · have hlt : ¬(c < 0) := Int.not_lt.mpr hc
    simp only [if_pos hc, if_neg hlt, Polynomial.coe_pow, coe_detOneSubPoly, Polynomial.coe_one]
    rw [← mul_pow, mul_comm, expSeries_traceLog_mul_detOneSubMul, one_pow]
  · have hlt : c < 0 := Int.lt_of_not_ge hc
    simp only [if_neg hc, if_pos hlt, Polynomial.coe_pow, coe_detOneSubPoly, Polynomial.coe_one,
      one_mul]

/-- **DworkRat Rationality Corollary (over `K`)**:
Any sequence `N_m = ∑_{i ∈ s} c_i Tr(A_i^m)` with integer coefficients `c_i : ℤ` and
matrices `A_i` over `K` has a rational zeta function `IsRationalPS (zetaOfCounts N)` over `K`. -/
theorem isRationalPS_zetaOfCounts_trace_sum {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (d : ι → ℕ) (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) K) :
    IsRationalPS (zetaOfCounts (fun m => ∑ i ∈ s, (c i : K) * ((A i) ^ m).trace)) := by
  classical
  let Q : Polynomial K :=
    ∏ i ∈ s, if 0 ≤ c i then (detOneSubPoly (A i)) ^ (c i).natAbs else 1
  let P : Polynomial K :=
    ∏ i ∈ s, if c i < 0 then (detOneSubPoly (A i)) ^ (c i).natAbs else 1
  refine ⟨P, Q, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split_ifs
    · exact pow_ne_zero _ (detOneSubPoly_ne_zero (A i))
    · exact one_ne_zero
  · induction s using Finset.induction_on with
    | empty =>
      simp only [P, Q, Finset.prod_empty, Finset.sum_empty, Polynomial.coe_one, one_mul]
      exact zetaOfCounts_zero
    | insert a s ha ih =>
      have hsplit : (fun m => ∑ i ∈ insert a s, (c i : K) * ((A i) ^ m).trace) =
          (fun m => (c a : K) * ((A a) ^ m).trace +
            ∑ i ∈ s, (c i : K) * ((A i) ^ m).trace) := by
        funext m
        exact Finset.sum_insert ha
      rw [hsplit, zetaOfCounts_add]
      have hQins : (∏ i ∈ insert a s, if 0 ≤ c i then (detOneSubPoly (A i)) ^ (c i).natAbs else 1) =
          (if 0 ≤ c a then (detOneSubPoly (A a)) ^ (c a).natAbs else 1) *
            ∏ i ∈ s, if 0 ≤ c i then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :=
        Finset.prod_insert ha
      have hPins : (∏ i ∈ insert a s, if c i < 0 then (detOneSubPoly (A i)) ^ (c i).natAbs else 1) =
          (if c a < 0 then (detOneSubPoly (A a)) ^ (c a).natAbs else 1) *
            ∏ i ∈ s, if c i < 0 then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :=
        Finset.prod_insert ha
      change ((∏ i ∈ insert a s, if 0 ≤ c i then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :
          Polynomial K) : PowerSeries K) * _ =
        ((∏ i ∈ insert a s, if c i < 0 then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :
          Polynomial K) : PowerSeries K)
      rw [hQins, hPins, Polynomial.coe_mul, Polynomial.coe_mul]
      calc (((if 0 ≤ c a then (detOneSubPoly (A a)) ^ (c a).natAbs else 1 : Polynomial K) :
              PowerSeries K) *
            ((∏ i ∈ s, if 0 ≤ c i then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :
              Polynomial K) : PowerSeries K)) *
          (zetaOfCounts (fun m => (c a : K) * ((A a) ^ m).trace) *
            zetaOfCounts (fun m => ∑ i ∈ s, (c i : K) * ((A i) ^ m).trace))
          = (((if 0 ≤ c a then (detOneSubPoly (A a)) ^ (c a).natAbs else 1 : Polynomial K) :
              PowerSeries K) *
              zetaOfCounts (fun m => (c a : K) * ((A a) ^ m).trace)) *
            (((∏ i ∈ s, if 0 ≤ c i then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :
              Polynomial K) : PowerSeries K) *
              zetaOfCounts (fun m => ∑ i ∈ s, (c i : K) * ((A i) ^ m).trace)) := by ring
        _ = ((if c a < 0 then (detOneSubPoly (A a)) ^ (c a).natAbs else 1 : Polynomial K) :
              PowerSeries K) *
            ((∏ i ∈ s, if c i < 0 then (detOneSubPoly (A i)) ^ (c i).natAbs else 1 :
              Polynomial K) : PowerSeries K) := by
            rw [zetaOfCounts_int_mul_trace (c a) (A a), ih]

end FredholmJacobi

section RationalityDescent

/-- **Field-extension descent for `IsRationalPS`**:
If `f : PowerSeries ℚ` becomes rational after mapping into any field extension `L`
(`[Field L] [Algebra ℚ L]`), then `f` is already rational over `ℚ`. -/
theorem isRationalPS_descent {L : Type*} [Field L] [Algebra ℚ L]
    (f : PowerSeries ℚ) (hf : IsRationalPS (f.map (algebraMap ℚ L))) :
    IsRationalPS f := by
  obtain ⟨d, q, N, hdN, ⟨i₀, hi₀d, hi₀ne⟩, _, hrec⟩ := recurrence_of_rational hf
  let a : ℕ → ℚ := fun m => PowerSeries.coeff m f
  have hrec' : ∀ m : ℕ, ∑ i : Fin (d + 1), q i.val * algebraMap ℚ L (a (m + N - i.val)) = 0 := by
    intro m
    have hm : m + N ≥ N := by omega
    have hr := hrec (m + N) hm
    rw [← Finset.sum_range (fun i => q i * algebraMap ℚ L (a (m + N - i)))]
    refine Eq.trans ?_ hr
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [a, PowerSeries.coeff_map]
  let row : ℕ → (Fin (d + 1) → ℚ) →ₗ[ℚ] ℚ := fun m =>
    { toFun := fun v => ∑ i : Fin (d + 1), a (m + N - i.val) * v i
      map_add' := fun u v => by
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  let Ksub : ℕ → Submodule ℚ (Fin (d + 1) → ℚ) := fun M =>
    ⨅ m ∈ Finset.range M, LinearMap.ker (row m)
  by_cases hex : ∃ v : Fin (d + 1) → ℚ, v ≠ 0 ∧ ∀ m : ℕ, row m v = 0
  · obtain ⟨v, hvne, hv0⟩ := hex
    have hvne' : ∃ i ≤ d, (if h : i ≤ d then v ⟨i, Nat.lt_succ_of_le h⟩ else 0) ≠ 0 := by
      have hne : ∃ j : Fin (d + 1), v j ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hvne (funext hall)
      obtain ⟨j, hj⟩ := hne
      refine ⟨j.val, Nat.le_of_lt_succ j.isLt, ?_⟩
      simp [Nat.le_of_lt_succ j.isLt, hj]
    refine rational_of_recurrence ⟨d, (fun i => if h : i ≤ d then v ⟨i, Nat.lt_succ_of_le h⟩ else 0),
      N, hdN, ?_, ?_, ?_⟩
    · obtain ⟨i, hid, hi⟩ := hvne'
      exact ⟨i, hid, hi⟩
    · intro i hi
      simp [show ¬(i ≤ d) by omega]
    · intro n hn
      have hr := hv0 (n - N)
      dsimp only
      rw [Finset.sum_range (fun i => (if h : i ≤ d then v ⟨i, Nat.lt_succ_of_le h⟩ else 0) *
        PowerSeries.coeff (n - i) f)]
      simp only [row, LinearMap.coe_mk, AddHom.coe_mk] at hr
      have hsub : n - N + N = n := Nat.sub_add_cancel hn
      rw [hsub] at hr
      convert hr using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Nat.le_of_lt_succ i.isLt, a, mul_comm]
  · exfalso
    push Not at hex
    let S : Set ℕ := Set.range (fun M => Module.finrank ℚ (Ksub M))
    have hSne : S.Nonempty := ⟨Module.finrank ℚ (Ksub 0), 0, rfl⟩
    obtain ⟨M₀, hM₀min⟩ := Nat.sInf_mem hSne
    dsimp only at hM₀min
    have hK0 : Ksub M₀ = ⊥ := by
      by_contra hbot
      have hne : ∃ v ∈ Ksub M₀, v ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hbot
        rw [Submodule.eq_bot_iff]
        exact hall
      obtain ⟨v, hvK, hvne⟩ := hne
      obtain ⟨m₁, hm₁⟩ := hex v hvne
      let M₁ := max M₀ (m₁ + 1)
      have hle : Ksub M₁ ≤ Ksub M₀ := by
        refine le_iInf₂ fun m hm => ?_
        exact iInf₂_le m (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hm)
          (le_max_left M₀ (m₁ + 1))))
      have hlt : Ksub M₁ < Ksub M₀ := by
        refine lt_of_le_of_ne hle fun heq => ?_
        have hvm₁ : v ∈ Ksub M₁ := heq ▸ hvK
        have hker : v ∈ LinearMap.ker (row m₁) := by
          have hm₁_mem : m₁ ∈ Finset.range M₁ :=
            Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self m₁) (le_max_right M₀ (m₁ + 1)))
          exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hvm₁ m₁) hm₁_mem
        exact hm₁ (LinearMap.mem_ker.mp hker)
      have hfrlt : Module.finrank ℚ (Ksub M₁) < Module.finrank ℚ (Ksub M₀) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      have hmin : Module.finrank ℚ (Ksub M₀) ≤ Module.finrank ℚ (Ksub M₁) := by
        rw [hM₀min]
        exact Nat.sInf_le ⟨M₁, rfl⟩
      omega
    let Lmap : (Fin (d + 1) → ℚ) →ₗ[ℚ] (Fin M₀ → ℚ) :=
      { toFun := fun v m => row m.val v
        map_add' := fun u v => by ext m; simp
        map_smul' := fun r v => by ext m; simp }
    have hLker : LinearMap.ker Lmap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : v ∈ Ksub M₀ := by
        rw [Submodule.mem_iInf]
        intro m
        rw [Submodule.mem_iInf]
        intro hm
        rw [LinearMap.mem_ker]
        exact congrFun (LinearMap.mem_ker.mp hv) ⟨m, Finset.mem_range.mp hm⟩
      rw [hK0] at hv'
      exact hv'
    obtain ⟨Rmap, hRL⟩ := LinearMap.exists_leftInverse_of_injective Lmap hLker
    let A_mat : Matrix (Fin M₀) (Fin (d + 1)) ℚ := LinearMap.toMatrix' Lmap
    let B_mat : Matrix (Fin (d + 1)) (Fin M₀) ℚ := LinearMap.toMatrix' Rmap
    have hBA : B_mat * A_mat = 1 := by
      rw [← LinearMap.toMatrix'_comp, hRL, LinearMap.toMatrix'_id]
    have hBA_L : B_mat.map (algebraMap ℚ L) * A_mat.map (algebraMap ℚ L) = 1 := by
      ext i j
      have h := congrArg (algebraMap ℚ L) (congrArg (fun M => M i j) hBA)
      simpa [Matrix.mul_apply, Matrix.one_apply, map_sum, map_mul] using h
    let qv : Fin (d + 1) → L := fun i => q i.val
    have hAqv : (A_mat.map (algebraMap ℚ L)).mulVec qv = 0 := by
      ext m
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
      have hrow_eq : ∀ i : Fin (d + 1), A_mat m i = a (m.val + N - i.val) := by
        intro i
        simp [A_mat, LinearMap.toMatrix'_apply, Lmap, row, Pi.single_apply]
      simp_rw [hrow_eq]
      have hm := hrec' m.val
      convert hm using 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [qv, mul_comm]
    have hqv0 : qv = 0 := by
      calc qv = (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) L).mulVec qv := (Matrix.one_mulVec qv).symm
        _ = (B_mat.map (algebraMap ℚ L) * A_mat.map (algebraMap ℚ L)).mulVec qv := by rw [hBA_L]
        _ = (B_mat.map (algebraMap ℚ L)).mulVec ((A_mat.map (algebraMap ℚ L)).mulVec qv) := by
            rw [Matrix.mulVec_mulVec]
        _ = (B_mat.map (algebraMap ℚ L)).mulVec 0 := by rw [hAqv]
        _ = 0 := Matrix.mulVec_zero _
    have hi0_fin : qv ⟨i₀, by omega⟩ = 0 := congrFun hqv0 ⟨i₀, by omega⟩
    exact hi₀ne hi0_fin

/-- Mapping `PowerSeries ℚ` into `PowerSeries L` commutes with `expSeries`. -/
theorem map_expSeries {L : Type*} [Field L] [Algebra ℚ L] [CharZero L]
    (f : PowerSeries ℚ) (hf : PowerSeries.constantCoeff f = 0) :
    (expSeries f).map (algebraMap ℚ L) = expSeries (f.map (algebraMap ℚ L)) := by
  let φ : ℚ →+* L := algebraMap ℚ L
  have hderiv_map : ∀ g : PowerSeries ℚ,
      PowerSeries.derivative L (g.map φ) = (PowerSeries.derivative ℚ g).map φ := by
    intro g
    ext n
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul]
    congr 1
    simp [φ]
  have hfL : PowerSeries.constantCoeff (f.map φ) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hf, map_zero]
  have hnegL : PowerSeries.constantCoeff (-(f.map φ)) = 0 := by rw [map_neg, hfL, neg_zero]
  have hprod : (expSeries f).map φ * expSeries (-(f.map φ)) = 1 := by
    apply PowerSeries.derivative.ext
    · rw [PowerSeries.derivative_one, Derivation.leibniz]
      simp only [smul_eq_mul]
      rw [hderiv_map, derivative_expSeries hf, map_mul, derivative_expSeries hnegL, map_neg,
        hderiv_map]
      ring
    · rw [map_mul, map_one, ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_expSeries hf, map_one, one_mul,
        PowerSeries.coeff_zero_eq_constantCoeff]
      exact constantCoeff_expSeries hnegL
  calc (expSeries f).map φ
      = (expSeries f).map φ * 1 := (mul_one _).symm
    _ = (expSeries f).map φ * (expSeries (-(f.map φ)) * expSeries (f.map φ)) := by
        rw [mul_comm (expSeries (-(f.map φ))), expSeries_mul_expSeries_neg hfL]
    _ = ((expSeries f).map φ * expSeries (-(f.map φ))) * expSeries (f.map φ) := by ring
    _ = 1 * expSeries (f.map φ) := by rw [hprod]
    _ = expSeries (f.map φ) := one_mul _

/-- Mapping `PowerSeries ℚ` into `PowerSeries L` commutes with `zetaOfCounts`. -/
theorem map_zetaOfCounts {L : Type*} [Field L] [Algebra ℚ L] [CharZero L] (N : ℕ → ℚ) :
    (zetaOfCounts N).map (algebraMap ℚ L) = zetaOfCounts (fun m => algebraMap ℚ L (N m)) := by
  rw [zetaOfCounts_eq_expSeries_zetaLog, map_expSeries _ (constantCoeff_zetaLog N),
    zetaOfCounts_eq_expSeries_zetaLog]
  congr 1
  ext m
  simp only [zetaLog, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

/-- **DworkRat Rationality Corollary (over `ℚ` when `N_m ∈ ℚ`)**:
If a rational sequence `N_Q : ℕ → ℚ` equals an integer linear combination of matrix
power traces `∑_{i ∈ s} c_i Tr(A_i^m)` over some char-0 field `K`, then `zetaOfCounts N_Q`
is already rational over `ℚ`! -/
theorem isRationalPS_zetaOfCounts_rat_of_trace_sum
    {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    {ι : Type*} (s : Finset ι) (c : ι → ℤ) (d : ι → ℕ)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) K)
    (N_Q : ℕ → ℚ)
    (hN : ∀ m, (N_Q m : K) = ∑ i ∈ s, (c i : K) * ((A i) ^ m).trace) :
    IsRationalPS (zetaOfCounts N_Q) := by
  apply isRationalPS_descent (L := K)
  rw [map_zetaOfCounts]
  have hfun : (fun m => algebraMap ℚ K (N_Q m)) =
      fun m => ∑ i ∈ s, (c i : K) * ((A i) ^ m).trace := by
    funext m
    exact (map_ratCast (algebraMap ℚ K) (N_Q m)).trans (hN m)
  rw [hfun]
  exact isRationalPS_zetaOfCounts_trace_sum s c d A

end RationalityDescent

end RHDirect.DworkRat
