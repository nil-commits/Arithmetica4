/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign: p-adic Hankel decay bound (second half of Gap 1)

For `f = ∑ a_n T^n ∈ ℤ[[T]]` with `f·h = g` where `g, h` are p-adic entire (`‖g_n‖, ‖h_n‖ ≤ C·r^{-n}`)
and `h₀ = 1`, the Hankel determinants satisfy the ultrametric decay bound
`‖N_{0,m}‖_K ≤ (C·r^{-⌊m/2⌋})^{m+1-⌊m/2⌋}`. Combined with the archimedean bound and the
Borel uncertainty principle this forces `N_{0,m} = 0` for large `m`, hence rationality by
Kronecker (`DworkRatKronecker`). No Weierstrass preparation / rank theory is used.
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RHDirect.DworkRatHankel
import RHDirect.DworkRatKronecker

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open Matrix Finset BigOperators PowerSeries

namespace RHDirect.DworkRat

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Monotonicity of integer powers for base ≥ 1. -/
lemma zpow_le_zpow_of_le' {r : ℝ} (hr : 1 ≤ r) {a b : ℤ} (hab : a ≤ b) : r ^ a ≤ r ^ b := by
  have ha : r ^ a = r ^ (a : ℝ) := by rw [Real.rpow_intCast]
  have hb : r ^ b = r ^ (b : ℝ) := by rw [Real.rpow_intCast]
  rw [ha, hb]
  exact Real.rpow_le_rpow_of_exponent_le hr (by exact_mod_cast hab)

/-! ### Ultrametric Leibniz determinant bound -/

omit [IsUltrametricDist K] in
/-- The norm of a unit-scalar multiple is unchanged. -/
private theorem norm_units_smul (u : ℤˣ) (x : K) : ‖u • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- **Ultrametric Leibniz bound.** If column `j` has entries bounded by `b j ≤ 1`, then
`‖det M‖ ≤ ∏ j, b j`. -/
theorem norm_det_le_prod_col_bounds {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (b : Fin n → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ i j, ‖M i j‖ ≤ b j) : ‖M.det‖ ≤ ∏ j, b j := by
  classical
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
  · exact Finset.prod_nonneg (fun j _ => hb j)
  · intro σ _
    rw [norm_units_smul]
    rw [norm_prod]
    apply Finset.prod_le_prod
    · intro i _; exact norm_nonneg _
    · intro i _; exact h (σ i) i

/-! ### The p-adic Hankel decay bound -/

omit [IsUltrametricDist K] in
/-- The Hankel determinant over `K` is the cast of the integer Hankel determinant. -/
lemma hankel0_cast_det (a : ℕ → ℤ) (m : ℕ) :
    (hankel0 (fun n => (a n : K)) m).det = (hankelDet a 0 m : K) := by
  have hmap : hankel0 (fun n => (a n : K)) m = (hankelMat a 0 m).map (Int.castRingHom K) := by
    ext i j
    simp [hankel0, hankelMat]
  rw [hmap]
  simp only [hankelDet, Matrix.det_apply, Matrix.map_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

omit [IsUltrametricDist K] in
/-- Convert an antidiagonal coefficient sum to a range sum. -/
private lemma coeff_mul_range (f h : PowerSeries K) (n : ℕ) :
    coeff n (f * h) = ∑ t ∈ range (n + 1), coeff t h * coeff (n - t) f := by
  rw [PowerSeries.coeff_mul]
  -- antidiagonal sum: ∑ p, coeff p.1 f * coeff p.2 h
  have : ∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff p.2 h =
      ∑ t ∈ range (n + 1), coeff t h * coeff (n - t) f := by
    apply Eq.symm
    apply Finset.sum_bij (fun (t : ℕ) _ => (n - t, t))
    · intro t ht
      rw [Finset.mem_antidiagonal]
      simp only [mem_range] at ht
      omega
    · intro t₁ _ t₂ _ h
      simpa using congrArg Prod.snd h
    · intro p hp
      rw [Finset.mem_antidiagonal] at hp
      refine ⟨p.2, ?_, ?_⟩
      · simp only [mem_range]; omega
      · ext <;> (simp; try omega)
    · intro t ht
      simp only [mem_range] at ht
      rw [mul_comm]
  exact this

/-- **p-adic Hankel decay bound.** If `f·h = g` with `g,h` entire (`‖·‖ ≤ C·r^{-n}`) and `h₀ = 1`,
then `‖N_{0,m}‖_K ≤ (C·r^{-⌊m/2⌋})^{m+1-⌊m/2⌋}`. -/
theorem padic_hankel_decay (a : ℕ → ℤ) (g h : PowerSeries K)
    (hgh : (mk (fun n => (a n : K))) * h = g)
    (hh0 : coeff 0 h = 1)
    {C r : ℝ} (hr : 1 < r) (hC : 1 ≤ C)
    (hg : ∀ n, ‖coeff n g‖ ≤ C * r ^ (-(n : ℤ)))
    (hh : ∀ n, ‖coeff n h‖ ≤ C * r ^ (-(n : ℤ)))
    (m : ℕ) :
    let d := m / 2
    ‖(hankelDet a 0 m : K)‖ ≤ (C * r ^ (-(d : ℤ))) ^ (m + 1 - d) := by
  intro d
  let U : Matrix (Fin (m + 1)) (Fin (m + 1)) K := fun k j =>
    if j.val < d then (if k = j then 1 else 0)
    else if j.val - d ≤ k.val ∧ k.val ≤ j.val then coeff (j.val - k.val) h else 0
  have hU_upper : U.IsUpperTriangular := by
    intro i j hij
    simp only [U]
    split_ifs <;> (simp_all; try omega)
  have hU_diag : ∀ j, U j j = 1 := by
    intro j
    by_cases hj : j.val < d
    · show (if j.val < d then (if j = j then (1 : K) else 0) else
        (if j.val - d ≤ j.val ∧ j.val ≤ j.val then coeff (j.val - j.val) h else 0)) = 1
      rw [if_pos hj]
      exact if_pos (by rfl : j = j)
    · show (if j.val < d then (if j = j then (1 : K) else 0) else
        (if j.val - d ≤ j.val ∧ j.val ≤ j.val then coeff (j.val - j.val) h else 0)) = 1
      rw [if_neg hj]
      have hcond : j.val - d ≤ j.val ∧ j.val ≤ j.val := by omega
      rw [if_pos hcond]
      have hjm : j.val - j.val = 0 := by omega
      rw [hjm, hh0]
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_upper]
    simp_rw [hU_diag]
    simp
  let M := hankel0 (fun n => (a n : K)) m * U
  have hdetM : M.det = (hankelDet a 0 m : K) := by
    simp only [M, Matrix.det_mul, hdetU, mul_one]
    exact hankel0_cast_det a m
  -- entry bounds: column j < d bounded by 1, column j ≥ d bounded by C·r^{-d}
  have hentry : ∀ i j, ‖M i j‖ ≤ if j.val < d then 1 else C * r ^ (-(d : ℤ)) := by
    intro i j
    simp only [M, Matrix.mul_apply]
    simp_rw [hankel0_apply, U]
    split_ifs with hj
    · rw [Finset.sum_eq_single j]
      · simp
        exact IsUltrametricDist.norm_intCast_le_one K (a (i.val + j.val))
      · intro k _ hk
        simp [hk]
      · intro hcon
        exact absurd (Finset.mem_univ j) hcon
    · have hjd : d ≤ j.val := by omega
      -- reindex the sum to t = j - k ∈ range (d+1)
      have hM : (∑ k : Fin (m + 1), (a (i.val + k.val) : K) *
          if j.val - d ≤ k.val ∧ k.val ≤ j.val then coeff (j.val - k.val) h else 0) =
          ∑ t ∈ range (d + 1), coeff t h * (a (i.val + j.val - t) : K) := by
        have hf : ∑ k : Fin (m + 1), (a (i.val + k.val) : K) *
            (if j.val - d ≤ k.val ∧ k.val ≤ j.val then coeff (j.val - k.val) h else 0) =
            ∑ k ∈ (univ : Finset (Fin (m + 1))).filter
              (fun k => j.val - d ≤ k.val ∧ k.val ≤ j.val),
              (a (i.val + k.val) : K) * coeff (j.val - k.val) h := by
          simp_rw [mul_ite, mul_zero]
          rw [← Finset.sum_filter]
        rw [hf]
        apply Finset.sum_bij (fun (k : Fin (m + 1)) _ => j.val - k.val)
        · intro k hk
          simp only [mem_filter, mem_univ, true_and] at hk
          simp only [mem_range]
          omega
        · intro k₁ _ k₂ _ h
          apply Fin.ext
          simp only [mem_filter, mem_univ, true_and] at *
          omega
        · intro t ht
          simp only [mem_range] at ht
          refine ⟨⟨j.val - t, by omega⟩, ?_, ?_⟩
          · simp only [mem_filter, mem_univ, true_and]
            omega
          · simp; omega
        · intro k hk
          simp only [mem_filter, mem_univ, true_and] at hk
          have : i.val + j.val - (j.val - k.val) = i.val + k.val := by omega
          rw [this]
          ring
      rw [hM]
      -- split off the g coefficient using f·h = g
      have hcoeff : coeff (i.val + j.val) g =
          ∑ t ∈ range (i.val + j.val + 1), coeff t h * (a (i.val + j.val - t) : K) := by
        have := congrArg (coeff (i.val + j.val)) hgh
        simp only [coeff_mul_range, coeff_mk] at this
        exact this.symm
      have hsplit : ∑ t ∈ range (d + 1), coeff t h * (a (i.val + j.val - t) : K) =
          coeff (i.val + j.val) g -
          ∑ t ∈ (range (i.val + j.val + 1)).filter (fun t => d + 1 ≤ t),
            coeff t h * (a (i.val + j.val - t) : K) := by
        have hsub : range (d + 1) ⊆ range (i.val + j.val + 1) := by
          intro x hx
          simp only [mem_range] at hx ⊢
          omega
        have hfilter : (range (i.val + j.val + 1)).filter (fun t => d + 1 ≤ t) =
            range (i.val + j.val + 1) \ range (d + 1) := by
          ext t
          simp only [mem_filter, mem_range, mem_sdiff]
          omega
        have hsum := Finset.sum_sdiff hsub (f := fun t => coeff t h * (a (i.val + j.val - t) : K))
        rw [hcoeff, hfilter, eq_sub_iff_add_eq]
        rw [add_comm]
        exact hsum
      rw [hsplit]
      have hnormg : ‖coeff (i.val + j.val) g‖ ≤ C * r ^ (-(d : ℤ)) := by
        calc ‖coeff (i.val + j.val) g‖
            ≤ C * r ^ (-(i.val + j.val : ℤ)) := hg _
          _ ≤ C * r ^ (-(d : ℤ)) := by
            apply mul_le_mul_of_nonneg_left
            · apply zpow_le_zpow_of_le' (by linarith)
              omega
            · linarith
      have hnormtail : ‖∑ t ∈ (range (i.val + j.val + 1)).filter (fun t => d + 1 ≤ t),
          coeff t h * (a (i.val + j.val - t) : K)‖ ≤ C * r ^ (-(d : ℤ)) := by
        apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        · positivity
        · intro t ht
          simp only [mem_filter, mem_range] at ht
          have ht' : d + 1 ≤ t := ht.2
          calc ‖coeff t h * (a (i.val + j.val - t) : K)‖
              = ‖coeff t h‖ * ‖(a (i.val + j.val - t) : K)‖ := by rw [norm_mul]
            _ ≤ ‖coeff t h‖ * 1 := by
              gcongr
              exact IsUltrametricDist.norm_intCast_le_one K _
            _ = ‖coeff t h‖ := by ring
            _ ≤ C * r ^ (-(t : ℤ)) := hh t
            _ ≤ C * r ^ (-(d : ℤ)) := by
              apply mul_le_mul_of_nonneg_left
              · apply zpow_le_zpow_of_le' (by linarith)
                omega
              · linarith
      have hsub : ‖coeff (i.val + j.val) g -
          ∑ t ∈ (range (i.val + j.val + 1)).filter (fun t => d + 1 ≤ t),
            coeff t h * (a (i.val + j.val - t) : K)‖ ≤
          max ‖coeff (i.val + j.val) g‖
            ‖∑ t ∈ (range (i.val + j.val + 1)).filter (fun t => d + 1 ≤ t),
              coeff t h * (a (i.val + j.val - t) : K)‖ := by
        have := IsUltrametricDist.norm_add_le_max (coeff (i.val + j.val) g)
          (-∑ t ∈ (range (i.val + j.val + 1)).filter (fun t => d + 1 ≤ t),
            coeff t h * (a (i.val + j.val - t) : K))
        simpa [sub_eq_add_neg] using this
      exact le_trans hsub (max_le hnormg hnormtail)
  -- apply the ultrametric Leibniz bound with per-column bounds
  have hprod : ‖M.det‖ ≤ ∏ j : Fin (m + 1), (if j.val < d then 1 else C * r ^ (-(d : ℤ))) := by
    apply norm_det_le_prod_col_bounds M (fun j => if j.val < d then 1 else C * r ^ (-(d : ℤ)))
    · intro j
      split_ifs
      · norm_num
      · positivity
    · exact hentry
  rw [hdetM] at hprod
  have hprodval : ∏ j : Fin (m + 1), (if j.val < d then 1 else C * r ^ (-(d : ℤ))) =
      (C * r ^ (-(d : ℤ))) ^ (m + 1 - d) := by
    -- d columns contribute 1, (m+1-d) columns contribute C·r^{-d}
    have hite : ∀ j : Fin (m + 1), (if j.val < d then 1 else C * r ^ (-(d : ℤ))) =
        (if d ≤ j.val then C * r ^ (-(d : ℤ)) else 1) := by
      intro j
      by_cases hj : j.val < d <;> simp [hj]
    simp_rw [hite]
    rw [← Finset.prod_filter]
    rw [Finset.prod_const]
    have hcard : ((univ : Finset (Fin (m + 1))).filter (fun j => d ≤ j.val)).card = m + 1 - d := by
      have : ((univ : Finset (Fin (m + 1))).filter (fun j => d ≤ j.val)).card =
          (range (m + 1 - d)).card := by
        apply Finset.card_bij (fun (j : Fin (m + 1)) _ => j.val - d)
        · intro j hj
          simp only [mem_filter, mem_univ, true_and] at hj
          simp only [mem_range]
          omega
        · intro j₁ _ j₂ _ h
          apply Fin.ext
          simp only [mem_filter, mem_univ, true_and] at *
          omega
        · intro t ht
          simp only [mem_range] at ht
          refine ⟨⟨d + t, by omega⟩, ?_, ?_⟩
          · simp only [mem_filter, mem_univ, true_and]
            try omega
          · simp; try omega
      rw [this, Finset.card_range]
    rw [hcard]
  rw [← hprodval]
  exact hprod

end RHDirect.DworkRat