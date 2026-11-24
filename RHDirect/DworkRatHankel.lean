/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign: Hankel determinants and the archimedean bound

The Borel–Dwork rationality criterion is proved through Hankel determinants
`N_{s,m} = det (a_{s+i+j})_{0 ≤ i,j ≤ m}` (Kronecker's criterion). This file defines them
and proves the archimedean upper bound: if the coefficients grow at most exponentially,
`|a_n| ≤ C·ρ^n`, then `|N_{s,m}| ≤ (m+1)!·(C·ρ^{s+2m})^{m+1}`.

Together with a p-adic decay bound (next file) and the integrality lemma
(`DworkRatBorelDwork`), this forces `N_{s,m} = 0` for large `s`, hence rationality.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RHDirect.DworkRatBorelDwork

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open Matrix Finset BigOperators

namespace RHDirect.DworkRat

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Hankel matrices and determinants -/

/-- The `(m+1)×(m+1)` Hankel matrix of the sequence `a`, starting at index `s`. -/
def hankelMat (a : ℕ → ℤ) (s m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℤ :=
  fun i j => a (s + i.val + j.val)

/-- The Hankel determinant `N_{s,m} = det (a_{s+i+j})`. -/
def hankelDet (a : ℕ → ℤ) (s m : ℕ) : ℤ := (hankelMat a s m).det

@[simp] theorem hankelMat_apply (a : ℕ → ℤ) (s m : ℕ) (i j : Fin (m + 1)) :
    hankelMat a s m i j = a (s + i.val + j.val) := rfl

/-! ### Product-form integrality (the Borel uncertainty principle) -/

/-- A nonzero integer has `|z|_∞ · |z|_p ≥ 1` (the product formula over `ℚ`, restricted to
the two places `∞` and `p`, using `|z|_ℓ ≤ 1` at all other finite places). -/
theorem one_le_natAbs_mul_padicNorm (z : ℤ) (hz : z ≠ 0) :
    1 ≤ (z.natAbs : ℝ) * ‖(z : ℚ_[p])‖ := by
  set v := padicValInt p z
  have hnorm : ‖(z : ℚ_[p])‖ = (p : ℝ) ^ (-(v : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hz), Padic.valuation_intCast]
  have hdvd : (p ^ v : ℤ) ∣ z := by
    rw [← Padic.norm_int_le_pow_iff_dvd]
    exact hnorm.le
  have hge : (p ^ v : ℝ) ≤ z.natAbs := by
    exact_mod_cast int_natAbs_ge_pow_of_dvd hz hdvd
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  have hprod : (p ^ v : ℝ) * (p : ℝ) ^ (-(v : ℤ)) = 1 := by
    have : (p ^ v : ℝ) = (p : ℝ) ^ (v : ℤ) := by rw [zpow_natCast]
    rw [this, ← zpow_add₀ (ne_of_gt hpos)]
    simp
  have hnonneg : 0 ≤ (p : ℝ) ^ (-(v : ℤ)) := zpow_nonneg (le_of_lt hpos) _
  calc (1 : ℝ) = (p ^ v : ℝ) * (p : ℝ) ^ (-(v : ℤ)) := hprod.symm
    _ ≤ (z.natAbs : ℝ) * (p : ℝ) ^ (-(v : ℤ)) := mul_le_mul_of_nonneg_right hge hnonneg
    _ = (z.natAbs : ℝ) * ‖(z : ℚ_[p])‖ := by rw [hnorm]

/-- **Borel uncertainty principle.** An integer whose archimedean size times its p-adic norm
is `< 1` must be zero. -/
theorem eq_zero_of_natAbs_mul_padicNorm_lt_one {z : ℤ}
    (h : (z.natAbs : ℝ) * ‖(z : ℚ_[p])‖ < 1) : z = 0 := by
  by_contra hz
  have := one_le_natAbs_mul_padicNorm (p := p) z hz
  linarith

/-! ### The archimedean Hankel bound -/

/-- The natAbs of a unit-scalar multiple is unchanged. -/
private theorem natAbs_units_smul (u : ℤˣ) (z : ℤ) : (u • z).natAbs = z.natAbs := by
  have hu : u.val.natAbs = 1 := by
    have h1 : u.val.natAbs * u.inv.natAbs = 1 := by
      have h := congrArg Int.natAbs u.val_inv
      have h2 : (u.val * u.inv).natAbs = u.val.natAbs * u.inv.natAbs := Int.natAbs_mul _ _
      have h3 : (1 : ℤ).natAbs = 1 := rfl
      rw [h2, h3] at h
      exact h
    exact Nat.eq_one_of_mul_eq_one_right h1
  have hsmul : u • z = (u : ℤ) * z := by rw [Units.smul_def]; rfl
  rw [hsmul, Int.natAbs_mul, hu, one_mul]

/-- natAbs commutes with a finite product. -/
private theorem natAbs_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∏ i ∈ s, f i).natAbs = ∏ i ∈ s, (f i).natAbs := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    simp only [Finset.prod_insert ha, Int.natAbs_mul, ih]

/-- **Archimedean Hankel bound.** If `|a_n| ≤ C·ρ^n` with `ρ ≥ 1`, then
`|N_{s,m}| ≤ (m+1)!·(C·ρ^{s+2m})^{m+1}`. -/
theorem hankelDet_natAbs_le {a : ℕ → ℤ} {C ρ : ℕ} (hρ : 1 ≤ ρ)
    (h : ∀ n, (a n).natAbs ≤ C * ρ ^ n) (s m : ℕ) :
    (hankelDet a s m).natAbs ≤ Nat.factorial (m + 1) * (C * ρ ^ (s + 2 * m)) ^ (m + 1) := by
  classical
  simp only [hankelDet, Matrix.det_apply, hankelMat_apply]
  have hentry : ∀ (σ : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1)),
      (a (s + (σ i).val + i.val)).natAbs ≤ C * ρ ^ (s + 2 * m) := by
    intro σ i
    have hi : i.val ≤ m := Nat.le_of_lt_succ i.isLt
    have hσ : (σ i).val ≤ m := Nat.le_of_lt_succ (σ i).isLt
    have hidx : s + (σ i).val + i.val ≤ s + 2 * m := by omega
    calc (a (s + (σ i).val + i.val)).natAbs
        ≤ C * ρ ^ (s + (σ i).val + i.val) := h _
      _ ≤ C * ρ ^ (s + 2 * m) :=
          Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) hidx)
  calc (∑ σ : Equiv.Perm (Fin (m + 1)), Equiv.Perm.sign σ • ∏ i, a (s + (σ i).val + i.val)).natAbs
      ≤ ∑ σ : Equiv.Perm (Fin (m + 1)), (Equiv.Perm.sign σ • ∏ i, a (s + (σ i).val + i.val)).natAbs :=
        Int.natAbs_sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin (m + 1)), (∏ i, a (s + (σ i).val + i.val)).natAbs := by
        apply Finset.sum_congr rfl; intro σ _; exact natAbs_units_smul _ _
    _ = ∑ σ : Equiv.Perm (Fin (m + 1)), ∏ i, (a (s + (σ i).val + i.val)).natAbs := by
        apply Finset.sum_congr rfl; intro σ _
        exact natAbs_prod Finset.univ _
    _ ≤ ∑ σ : Equiv.Perm (Fin (m + 1)), (C * ρ ^ (s + 2 * m)) ^ (m + 1) := by
        apply Finset.sum_le_sum; intro σ _
        calc ∏ i : Fin (m + 1), (a (s + (σ i).val + i.val)).natAbs
            ≤ ∏ i : Fin (m + 1), (C * ρ ^ (s + 2 * m)) :=
              Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hentry σ i)
          _ = (C * ρ ^ (s + 2 * m)) ^ (m + 1) := by
              rw [Finset.prod_const]; simp [Fintype.card_fin]
    _ = Nat.factorial (m + 1) * (C * ρ ^ (s + 2 * m)) ^ (m + 1) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

end RHDirect.DworkRat