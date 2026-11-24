/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polymorphic Elliptic & Genus-g Hasse–Weil Zeta Rationality over `ℚ[[T]]`

Upgrades `zeta_elliptic_den` from `RHDirect.DworkZetaW3j` (which required `α, β : ℚ`) to
**arbitrary algebraic / complex Frobenius eigenvalues** `α, β : ℂ` with `α + β = a` (`a : ℤ`)
and `α * β = q` (`q : ℕ`). Using Newton's power-sum recurrence `newtonPowSum a q m`, the
point counts `N_m = q^m + 1 - (α^m + β^m)` are automatically rational, and the classical
rationality identity

`Z(E, T) · (1 - T)(1 - qT) = 1 - aT + qT²`

is proved unconditionally in `PowerSeries ℚ` by descending from `PowerSeries ℂ` along the
injective embedding `algebraMap ℚ ℂ`.

Also proves the general **genus-`g` curve / abelian-variety Hasse–Weil rationality** over
`ℚ[[T]]` for `N_m = q^m + 1 - Tr(F^m)` with any `F : Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ`
using `RHDirect.DworkRat.expSeries_trace_mul_charpoly_rev_eq_one`.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import RHDirect.DworkRatZeta
import RHDirect.DworkRatFredholmComplete
import RHDirect.DworkZetaVerify

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.unusedSectionVars false

namespace RHDirect
namespace HasseWeil

open PowerSeries

noncomputable section

/-! ## 1. Bridge between `HasseWeil.zetaSeq` and `DworkRat.zetaOfCounts` -/

theorem zetaSeq_eq_zetaOfCounts (N : ℕ → ℚ) :
    zetaSeq N = RHDirect.DworkRat.zetaOfCounts (K := ℚ) N := by
  unfold zetaSeq RHDirect.DworkRat.zetaOfCounts
  change PowerSeries.subst (PowerSeries.mk fun n => N n / (n : ℚ)) (PowerSeries.exp ℚ) =
    PowerSeries.subst (PowerSeries.mk fun r => if r = 0 then 0 else N r / (r : ℚ))
      (PowerSeries.exp ℚ)
  congr 1
  ext r
  simp only [PowerSeries.coeff_mk]
  by_cases hr : r = 0
  · subst hr; simp
  · simp [hr]

/-! ## 2. Newton power sums and complex Frobenius eigenvalues for elliptic curves -/

/-- Integer Newton power sum `p_m = α^m + β^m` for roots of `X^2 - a X + q`. -/
def newtonPowSumInt (a : ℤ) (q : ℕ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | m + 2 => a * newtonPowSumInt a q (m + 1) - (q : ℤ) * newtonPowSumInt a q m

/-- Rational Newton power sum `α^m + β^m` for roots of `X^2 - a X + q`. -/
def newtonPowSum (a : ℤ) (q : ℕ) (m : ℕ) : ℚ :=
  (newtonPowSumInt a q m : ℚ)

/-- Newton's identity: for any `α, β : ℂ` with `α + β = a` and `α * β = q`,
`(newtonPowSum a q m : ℂ) = α^m + β^m` for all `m`. -/
theorem newtonPowSum_eq_pow_add {a : ℤ} {q : ℕ} (α β : ℂ)
    (ha : α + β = (a : ℂ)) (hq : α * β = (q : ℂ)) (m : ℕ) :
    (newtonPowSum a q m : ℂ) = α ^ m + β ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | k
    · simp [newtonPowSum, newtonPowSumInt]
      norm_num
    · simp [newtonPowSum, newtonPowSumInt, ha]
    · have ih1 := ih (k + 1) (by omega)
      have ih0 := ih k (by omega)
      have hrec : newtonPowSumInt a q (k + 2) =
          a * newtonPowSumInt a q (k + 1) - (q : ℤ) * newtonPowSumInt a q k := rfl
      have hcast : (newtonPowSum a q (k + 2) : ℂ) =
          (a : ℂ) * (newtonPowSum a q (k + 1) : ℂ) -
            (q : ℂ) * (newtonPowSum a q k : ℂ) := by
        unfold newtonPowSum
        rw [hrec]
        push_cast
        rfl
      rw [hcast, ih1, ih0, ← ha, ← hq]
      ring

/-- Existence of complex Frobenius eigenvalues `α, β : ℂ` with `α + β = a` and `α * β = q`. -/
theorem exists_complex_roots_quadratic (a : ℤ) (q : ℕ) :
    ∃ α β : ℂ, α + β = (a : ℂ) ∧ α * β = (q : ℂ) := by
  let P : Polynomial ℂ :=
    Polynomial.X ^ 2 - Polynomial.C (a : ℂ) * Polynomial.X + Polynomial.C (q : ℂ)
  have hdeg : P.degree ≠ 0 := by
    intro h
    have hP := Polynomial.eq_C_of_degree_eq_zero h
    have hc := congrArg (fun f : Polynomial ℂ => f.coeff 2) hP
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at hc
    norm_num at hc
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root P hdeg
  refine ⟨α, (a : ℂ) - α, by ring, ?_⟩
  have hev : α ^ 2 - (a : ℂ) * α + (q : ℂ) = 0 := by
    simpa [P, Polynomial.IsRoot] using hα
  linear_combination -hev

/-- **Complex-eigenvalue elliptic curve zeta rationality (descended to `PowerSeries ℚ`)**:
For arbitrary algebraic / complex `α, β : ℂ` with `α + β = a` (`a : ℤ`) and `α * β = q` (`q : ℕ`),
if `N : ℕ → ℚ` satisfies `(N m : ℂ) = q^m + 1 - (α^m + β^m)`, then in `PowerSeries ℚ`:
`Z(N, T) · (1 - T)(1 - qT) = 1 - aT + qT²`. -/
theorem zeta_elliptic_complex {a : ℤ} {q : ℕ} (α β : ℂ)
    (ha : α + β = (a : ℂ)) (hq : α * β = (q : ℂ))
    (N : ℕ → ℚ) (hN : ∀ m, (N m : ℂ) = (q : ℂ) ^ m + 1 - (α ^ m + β ^ m)) :
    zetaSeq N * ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℚ) * PowerSeries.X)) =
      1 - (a : PowerSeries ℚ) * PowerSeries.X + (q : PowerSeries ℚ) * PowerSeries.X ^ 2 := by
  let φ : ℚ →+* ℂ := algebraMap ℚ ℂ
  have hmap_eq : (zetaSeq N * ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℚ) * PowerSeries.X))).map φ =
      (1 - (a : PowerSeries ℚ) * PowerSeries.X + (q : PowerSeries ℚ) * PowerSeries.X ^ 2).map φ := by
    rw [map_mul, zetaSeq_eq_zetaOfCounts, RHDirect.DworkRat.map_zetaOfCounts (L := ℂ) N]
    have hN_fun : (fun m => φ (N m)) =
        fun m => (q : ℂ) ^ m + 1 - ∑ i ∈ ({0, 1} : Finset (Fin 2)), (![α, β] i) ^ m := by
      funext m
      have hφ : φ (N m) = (N m : ℂ) := map_ratCast φ (N m)
      rw [hφ, hN m]
      simp [Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide)]
    rw [hN_fun]
    have hmul_map : ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℚ) * PowerSeries.X)).map φ =
        (1 - PowerSeries.X) * (1 - PowerSeries.C (q : ℂ) * PowerSeries.X) := by
      simp [φ, map_sub, map_mul, map_one, map_natCast, PowerSeries.map_X]
    rw [hmul_map, ← mul_assoc]
    rw [RHDirect.DworkRat.zeta_rationality_general ({0, 1} : Finset (Fin 2)) (q : ℂ) ![α, β]]
    have hprod : ((∏ i ∈ ({0, 1} : Finset (Fin 2)),
          (1 - Polynomial.C (![α, β] i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
        1 - PowerSeries.C (a : ℂ) * PowerSeries.X + PowerSeries.C (q : ℂ) * PowerSeries.X ^ 2 := by
      rw [Finset.prod_pair (show (0 : Fin 2) ≠ 1 by decide)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_C,
        Polynomial.coe_X]
      calc (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X)
          = 1 - (PowerSeries.C α + PowerSeries.C β) * PowerSeries.X +
              (PowerSeries.C α * PowerSeries.C β) * PowerSeries.X ^ 2 := by ring
        _ = 1 - PowerSeries.C (α + β) * PowerSeries.X +
              PowerSeries.C (α * β) * PowerSeries.X ^ 2 := by
            rw [← map_add, ← map_mul]
        _ = 1 - PowerSeries.C (a : ℂ) * PowerSeries.X +
              PowerSeries.C (q : ℂ) * PowerSeries.X ^ 2 := by
            rw [ha, hq]
    rw [hprod]
    simp [φ, map_add, map_sub, map_mul, map_pow, map_one, map_intCast, map_natCast,
      PowerSeries.map_X]
  ext n
  apply φ.injective
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map, hmap_eq]

/-- **Unconditional Elliptic Curve Zeta Rationality in `PowerSeries ℚ`**
(via Newton power sums `newtonPowSum a q m` and descent from `ℂ`). -/
theorem zeta_elliptic_den_poly (a : ℤ) (q : ℕ) :
    zetaSeq (fun m => (q : ℚ) ^ m + 1 - newtonPowSum a q m) *
      ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℚ) * PowerSeries.X)) =
      1 - (a : PowerSeries ℚ) * PowerSeries.X + (q : PowerSeries ℚ) * PowerSeries.X ^ 2 := by
  obtain ⟨α, β, ha, hq⟩ := exists_complex_roots_quadratic a q
  refine zeta_elliptic_complex α β ha hq _ ?_
  intro m
  push_cast
  rw [newtonPowSum_eq_pow_add α β ha hq m]

/-! ## 3. Genus-`g` curve and abelian-variety Hasse–Weil rationality over `ℚ[[T]]` -/

/-- **General matrix-Frobenius Hasse–Weil rationality over `ℚ[[T]]`**:
For any `n : ℕ`, `q : ℚ`, and `F : Matrix (Fin n) (Fin n) ℚ`, if `N_m = q^m + 1 - Tr(F^m)`,
then `Z(N, T) · (1 - T)(1 - qT) = det(1 - T · F)`. -/
theorem zeta_matrix_frob_den {n : ℕ} (q : ℚ) (F : Matrix (Fin n) (Fin n) ℚ) :
    zetaSeq (fun m => q ^ m + 1 - (F ^ m).trace) *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) =
      RHDirect.DworkRat.detOneSubMul F := by
  rw [zetaSeq_eq_zetaOfCounts]
  have hsplit : (fun m => q ^ m + 1 - (F ^ m).trace) =
      fun m => (q ^ m + 1) + (-(F ^ m).trace) := by
    funext m; ring
  rw [hsplit, RHDirect.DworkRat.zetaOfCounts_add]
  have h1 : RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => q ^ m + 1) *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) = 1 := by
    rw [← zetaSeq_eq_zetaOfCounts]
    have hmul : ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) =
        ((1 - PowerSeries.C q * PowerSeries.X) * (1 - PowerSeries.X)) := mul_comm _ _
    rw [hmul]
    exact zeta_projective_line_den q
  have hF : RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace) =
      RHDirect.DworkRat.detOneSubMul F := by
    have hneg := RHDirect.DworkRat.zetaOfCounts_neg_mul (K := ℚ) (fun m => (F ^ m).trace)
    have hdet := RHDirect.DworkRat.zetaOfCounts_trace_mul_detOneSubMul F
    calc RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace)
        = RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace) * 1 := (mul_one _).symm
      _ = RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace) *
            (RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => (F ^ m).trace) *
              RHDirect.DworkRat.detOneSubMul F) := by rw [hdet]
      _ = (RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace) *
            RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => (F ^ m).trace)) *
            RHDirect.DworkRat.detOneSubMul F := by ring
      _ = 1 * RHDirect.DworkRat.detOneSubMul F := by rw [hneg]
      _ = RHDirect.DworkRat.detOneSubMul F := one_mul _
  calc (RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => q ^ m + 1) *
          RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace)) *
        ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))
      = (RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => q ^ m + 1) *
          ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X))) *
          RHDirect.DworkRat.zetaOfCounts (K := ℚ) (fun m => -(F ^ m).trace) := by ring
    _ = 1 * RHDirect.DworkRat.detOneSubMul F := by rw [h1, hF]
    _ = RHDirect.DworkRat.detOneSubMul F := one_mul _

/-- **Genus-`g` curve Hasse–Weil zeta identity over `ℚ[[T]]`**:
For any `g : ℕ`, `q : ℚ`, and Frobenius matrix `F : Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ`
acting on `H¹`, if `N_m = q^m + 1 - Tr(F^m)`, then
`Z(C, T) · (1 - T)(1 - qT) = det(1 - T · F) ∈ ℚ[T]`. -/
theorem zeta_genus_g_den (g : ℕ) (q : ℚ) (F : Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ) :
    zetaSeq (fun m => q ^ m + 1 - (F ^ m).trace) *
      ((1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X)) =
      (RHDirect.DworkRat.detOneSubPoly F : PowerSeries ℚ) := by
  rw [RHDirect.DworkRat.coe_detOneSubPoly]
  exact zeta_matrix_frob_den q F

/-- **`IsRationalPS` for genus-`g` curves over `ℚ[[T]]`**. -/
theorem isRationalPS_zeta_genus_g (g : ℕ) (q : ℚ) (F : Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ) :
    RHDirect.DworkRat.IsRationalPS (zetaSeq (fun m => q ^ m + 1 - (F ^ m).trace)) := by
  let Q : Polynomial ℚ := (1 - Polynomial.X) * (1 - Polynomial.C q * Polynomial.X)
  have hQ0 : Polynomial.eval 0 Q = 1 := by simp [Q]
  have hQne : Q ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hQ0
    exact zero_ne_one hQ0
  refine ⟨RHDirect.DworkRat.detOneSubPoly F, Q, hQne, ?_⟩
  have hQcoe : (Q : PowerSeries ℚ) =
      (1 - PowerSeries.X) * (1 - PowerSeries.C q * PowerSeries.X) := by
    simp [Q]
  rw [hQcoe, mul_comm]
  exact zeta_genus_g_den g q F

/-- **General genus-`g` / abelian-variety rationality over `ℚ[[T]]` via `ℂ`-matrix descent**:
Even when the Frobenius matrix `F` on `H¹` has entries in `ℂ` (or any char-0 field `K`),
if the point counts `N_m : ℚ` satisfy `(N_m : K) = q^m + 1 - Tr(F^m)`, then
`Z(N, T)` is rational over `ℚ` (`IsRationalPS (zetaSeq N)`). -/
theorem isRationalPS_zeta_genus_g_descent
    {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    (g : ℕ) (q : ℚ) (F : Matrix (Fin (2 * g)) (Fin (2 * g)) K)
    (N : ℕ → ℚ) (hN : ∀ m, (N m : K) = (q : K) ^ m + 1 - (F ^ m).trace) :
    RHDirect.DworkRat.IsRationalPS (zetaSeq N) := by
  rw [zetaSeq_eq_zetaOfCounts]
  let d : Fin 3 → ℕ := ![1, 1, 2 * g]
  let c : Fin 3 → ℤ := ![1, 1, -1]
  let A : ∀ i : Fin 3, Matrix (Fin (d i)) (Fin (d i)) K
    | ⟨0, _⟩ => (q : K) • (1 : Matrix (Fin 1) (Fin 1) K)
    | ⟨1, _⟩ => (1 : Matrix (Fin 1) (Fin 1) K)
    | ⟨2, _⟩ => F
  refine RHDirect.DworkRat.isRationalPS_zetaOfCounts_rat_of_trace_sum
    Finset.univ c d A N ?_
  intro m
  rw [hN m, Fin.sum_univ_three]
  have hA0 : ((A 0) ^ m).trace = (q : K) ^ m := by
    change (((q : K) • (1 : Matrix (Fin 1) (Fin 1) K)) ^ m).trace = (q : K) ^ m
    rw [smul_pow, one_pow, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    simp
  have hA1 : ((A 1) ^ m).trace = 1 := by
    change ((1 : Matrix (Fin 1) (Fin 1) K) ^ m).trace = 1
    rw [one_pow, Matrix.trace_one, Fintype.card_fin]
    simp
  have hA2 : ((A 2) ^ m).trace = (F ^ m).trace := rfl
  have hc0 : (c 0 : K) = 1 := by simp [c]
  have hc1 : (c 1 : K) = 1 := by simp [c]
  have hc2 : (c 2 : K) = -1 := by simp [c]
  rw [hc0, hc1, hc2, hA0, hA1, hA2]
  ring

end

end HasseWeil
end RHDirect
