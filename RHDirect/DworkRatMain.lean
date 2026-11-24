/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dwork Rationality campaign: the Borel–Dwork rationality criterion (Gap 1 assembly)

A power series `f = ∑ a_n T^n ∈ ℤ[[T]]` with
  * archimedean exponential growth `|a_n| ≤ C₀·A^n`, and
  * p-adic meromorphic continuation (`f·h = g` with `g,h` p-adic entire, `h₀ = 1`)
is a rational function. This is the analytic heart of Dwork's proof of Weil Conjecture I.

Proof: the archimedean Hankel bound (`DworkRatHankel`) and the p-adic Hankel decay bound
(`DworkRatPadicBound`) together force `|N_{0,m}|_∞ · ‖N_{0,m}‖_p < 1` for large `m`; the Borel
uncertainty principle then gives `N_{0,m} = 0`, and Kronecker's criterion (`DworkRatKronecker`)
yields a linear recurrence, hence rationality (`DworkRatCriterion`).
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RHDirect.DworkRatCriterion
import RHDirect.DworkRatBorelDwork
import RHDirect.DworkRatHankel
import RHDirect.DworkRatKronecker
import RHDirect.DworkRatPadicBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open PowerSeries Finset BigOperators

namespace RHDirect.DworkRat

/-! ### The exponential-decay limit helper -/

/-- For `0 ≤ q < 1` and `D ≥ 0`, `D^m · q^{m²} < ε` for all large `m`. -/
lemma exists_pow_mul_pow_sq_lt {q D : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hD : 0 ≤ D)
    {ε : ℝ} (hε : 0 < ε) : ∃ M, ∀ m ≥ M, D ^ m * q ^ (m * m) < ε := by
  have hrew : ∀ m : ℕ, D ^ m * q ^ (m * m) = (D * q ^ m) ^ m := by
    intro m
    rw [mul_pow, pow_mul]
  have hq : Filter.Tendsto (fun m : ℕ => q ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hDq : Filter.Tendsto (fun m : ℕ => D * q ^ m) Filter.atTop (nhds 0) := by
    simpa using hq.const_mul D
  have hhalf : ∀ᶠ m in Filter.atTop, D * q ^ m < 1 / 2 := by
    have := Filter.Tendsto.eventually_lt hDq tendsto_const_nhds (by norm_num : (0 : ℝ) < 1 / 2)
    simpa using this
  have hhalf' : ∃ M₁, ∀ m ≥ M₁, D * q ^ m < 1 / 2 := by
    rw [Filter.eventually_atTop] at hhalf
    exact hhalf
  obtain ⟨M₁, hM₁⟩ := hhalf'
  have hdecay : Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hε : ∀ᶠ m in Filter.atTop, (1 / 2 : ℝ) ^ m < ε := by
    have := Filter.Tendsto.eventually_lt hdecay tendsto_const_nhds hε
    simpa using this
  rw [Filter.eventually_atTop] at hε
  obtain ⟨M₂, hM₂⟩ := hε
  use max M₁ M₂
  intro m hm
  have hm1 : M₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm2 : M₂ ≤ m := le_trans (le_max_right _ _) hm
  have hDqm : D * q ^ m < 1 / 2 := hM₁ m hm1
  have hDqm0 : 0 ≤ D * q ^ m := mul_nonneg hD (pow_nonneg hq0 _)
  calc D ^ m * q ^ (m * m) = (D * q ^ m) ^ m := hrew m
    _ ≤ (1 / 2 : ℝ) ^ m := by
      gcongr
    _ < ε := hM₂ m hm2

/-! ### The Borel–Dwork rationality criterion -/

/-- **Borel–Dwork rationality criterion (Dwork's proof of Weil Conjecture I, analytic core).**
An integer-coefficient power series with archimedean exponential growth and p-adic meromorphic
continuation (a quotient of p-adic entire series) is rational. -/
theorem borel_dwork_rationality {p : ℕ} [Fact p.Prime] (a : ℕ → ℤ)
    (h_arch : ∃ C₀ A : ℕ, ∀ n, (a n).natAbs ≤ C₀ * A ^ n)
    (h_mero : ∃ (g h : PowerSeries ℚ_[p]),
      (mk (fun n => (a n : ℚ_[p]))) * h = g ∧ coeff 0 h = 1 ∧
      (∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n,
        ‖coeff n g‖ ≤ C * r ^ (-(n : ℤ)) ∧ ‖coeff n h‖ ≤ C * r ^ (-(n : ℤ)))) :
    IsRationalPS (mk (fun n => (a n : ℚ))) := by
  obtain ⟨C₀, A, hA⟩ := h_arch
  obtain ⟨g, h, hgh, hh0, h_entire⟩ := h_mero
  -- choose r large enough that q = 2(max A 1)²/r^{1/4} < 1
  let r : ℝ := 16 * (max A 1 : ℝ) ^ 8 + 1
  have hr1 : 1 < r := by
    dsimp [r]
    have hmax : 1 ≤ (max A 1 : ℝ) := by exact_mod_cast le_max_right A 1
    have hp : 0 < (max A 1 : ℝ) ^ 8 := pow_pos (by linarith) 8
    linarith [mul_pos (by norm_num : (0 : ℝ) < 16) hp]
  have hr0 : 0 ≤ r := by linarith
  have hrpos' : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith : 0 < r) _
  have hrA : (2 * (max A 1 : ℝ) ^ 2) ^ 4 < r := by
    dsimp [r]
    have : (2 * (max A 1 : ℝ) ^ 2) ^ 4 = 16 * (max A 1 : ℝ) ^ 8 := by ring
    linarith
  obtain ⟨C, hC⟩ := h_entire r (by linarith)
  let C' : ℝ := max C 1
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'0 : 0 ≤ C' := by linarith
  have hg : ∀ n, ‖coeff n g‖ ≤ C' * r ^ (-(n : ℤ)) := by
    intro n
    calc ‖coeff n g‖ ≤ C * r ^ (-(n : ℤ)) := (hC n).1
      _ ≤ C' * r ^ (-(n : ℤ)) := by
        gcongr
        exact le_max_left _ _
  have hh : ∀ n, ‖coeff n h‖ ≤ C' * r ^ (-(n : ℤ)) := by
    intro n
    calc ‖coeff n h‖ ≤ C * r ^ (-(n : ℤ)) := (hC n).2
      _ ≤ C' * r ^ (-(n : ℤ)) := by
        gcongr
        exact le_max_left _ _
  -- p-adic Hankel decay bound (K = ℚ_[p])
  have hpadic : ∀ m, ‖(hankelDet a 0 m : ℚ_[p])‖ ≤
      (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) := by
    intro m
    exact padic_hankel_decay a g h hgh hh0 hr1 hC'1 hg hh m
  -- archimedean Hankel bound
  have harch : ∀ m, (hankelDet a 0 m).natAbs ≤
      Nat.factorial (m + 1) * (C₀ * (max A 1) ^ (2 * m)) ^ (m + 1) := by
    intro m
    have hbound : ∀ n, (a n).natAbs ≤ C₀ * (max A 1) ^ n := by
      intro n
      calc (a n).natAbs ≤ C₀ * A ^ n := hA n
        _ ≤ C₀ * (max A 1) ^ n := by
          gcongr
          exact le_max_left _ _
    have := hankelDet_natAbs_le (show 1 ≤ max A 1 by omega) hbound 0 m
    simpa using this
  -- q = 2(max A 1)²/r^{1/4} < 1 and D = 2(max A 1)²C₀C'
  set q : ℝ := 2 * (max A 1 : ℝ) ^ 2 / r ^ (1 / 4 : ℝ) with hq_def
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg _)) (le_of_lt hrpos')
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hrpos']
    by_contra hge
    push Not at hge
    have hpow : (r ^ (1 / 4 : ℝ)) ^ 4 ≤ (2 * (max A 1 : ℝ) ^ 2) ^ 4 := by
      gcongr
    have hy : (r ^ (1 / 4 : ℝ)) ^ 4 = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ r)]
      rw [show (1 / 4 : ℝ) * ↑(4 : ℕ) = 1 by norm_num, Real.rpow_one]
    rw [hy] at hpow
    linarith [hrA]
  set D : ℝ := 2 * (max A 1 : ℝ) ^ 2 * (C₀ : ℝ) * C' with hD_def
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg _))
      (Nat.cast_nonneg _)) hC'0
  -- product bound: |N|_∞ · ‖N‖_p ≤ (C₀C'+1)·r^{1/4} · D^m · q^{m²}
  have hprod : ∀ m, ((hankelDet a 0 m).natAbs : ℝ) * ‖(hankelDet a 0 m : ℚ_[p])‖ ≤
      ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) := by
    intro m
    have hp := hpadic m
    have ha := harch m
    have h1 : ((hankelDet a 0 m).natAbs : ℝ) ≤
        (Nat.factorial (m + 1) : ℝ) * ((C₀ : ℝ) * (max A 1 : ℝ) ^ (2 * m)) ^ (m + 1) := by
      exact_mod_cast ha
    calc ((hankelDet a 0 m).natAbs : ℝ) * ‖(hankelDet a 0 m : ℚ_[p])‖
        ≤ ((Nat.factorial (m + 1) : ℝ) * ((C₀ : ℝ) * (max A 1 : ℝ) ^ (2 * m)) ^ (m + 1)) *
            (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) := by
          gcongr
      _ ≤ ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) := by
          -- factorial bound: (m+1)! ≤ 2^{m(m+1)}
          have hfact : (Nat.factorial (m + 1) : ℝ) ≤ (2 : ℝ) ^ (m * (m + 1)) := by
            have hf : (Nat.factorial (m + 1) : ℝ) ≤ ((m + 1) : ℝ) ^ (m + 1) := by
              exact_mod_cast Nat.factorial_le_pow (m + 1)
            have h2 : ((m + 1) : ℝ) ≤ (2 : ℝ) ^ m := by
              have : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
                intro n
                induction n with
                | zero => norm_num
                | succ n ih =>
                  calc n + 1 + 1 ≤ 2 ^ n + 1 := by omega
                    _ ≤ 2 ^ n + 2 ^ n := by
                      have : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
                      omega
                    _ = 2 ^ (n + 1) := by ring
              exact_mod_cast this m
            calc (Nat.factorial (m + 1) : ℝ) ≤ ((m + 1) : ℝ) ^ (m + 1) := hf
              _ ≤ ((2 : ℝ) ^ m) ^ (m + 1) := by
                gcongr
              _ = (2 : ℝ) ^ (m * (m + 1)) := by
                rw [← pow_mul]
          -- d(m+1-d) ≥ (m²-1)/4 (as reals), d = m/2 (floor)
          have hd : ((m / 2 : ℕ) : ℝ) * ((m : ℝ) + 1 - ((m / 2 : ℕ) : ℝ)) ≥
              ((m : ℝ) * (m : ℝ) - 1) / 4 := by
            have h4 : (m : ℝ) * (m : ℝ) - 1 ≤
                4 * (((m / 2 : ℕ) : ℝ) * ((m : ℝ) + 1 - ((m / 2 : ℕ) : ℝ))) := by
              have hpar : m % 2 = 0 ∨ m % 2 = 1 := by omega
              rcases hpar with hpar | hpar
              · have hm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
                  have := congrArg (fun k : ℕ => (k : ℝ)) (show m = 2 * (m / 2) by omega)
                  push_cast at this
                  linarith
                rw [hm]
                ring_nf
                linarith [show 0 ≤ ((m / 2 : ℕ) : ℝ) from Nat.cast_nonneg _]
              · have hm : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) + 1 := by
                  have := congrArg (fun k : ℕ => (k : ℝ)) (show m = 2 * (m / 2) + 1 by omega)
                  push_cast at this
                  linarith
                rw [hm]
                ring_nf
                linarith [show 0 ≤ ((m / 2 : ℕ) : ℝ) from Nat.cast_nonneg _]
            linarith
          -- C' ≥ 1, so C'^{m+1-d} ≤ C'^{m+1}
          have hC'pow : C' ^ (m + 1 - m / 2) ≤ C' ^ (m + 1) := by
            gcongr
            omega
          -- r^{-d(m+1-d)} ≤ (r^{1/4})^{-m²} · r^{1/4}
          have hrpow : r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) ≤
              (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ) := by
            have hL : r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) =
                r ^ (-(((m / 2 : ℕ) * (m + 1 - m / 2) : ℕ) : ℝ)) := by
              have heq : (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) =
                  (-(((m / 2 : ℕ) * (m + 1 - m / 2) : ℕ) : ℤ)) := by
                rw [neg_mul, ← Nat.cast_mul]
              rw [heq, ← Real.rpow_intCast]
              simp only [Int.cast_neg, Int.cast_natCast]
            have hR : (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ) =
                r ^ (-(((m : ℝ) * (m : ℝ) - 1) / 4)) := by
              rw [← Real.rpow_mul (by linarith : 0 ≤ r),
                ← Real.rpow_add (by linarith : 0 < r)]
              ring_nf
            rw [hL, hR]
            apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ r)
            have hcast : (((m / 2 : ℕ) * (m + 1 - m / 2) : ℕ) : ℝ) =
                ((m / 2 : ℕ) : ℝ) * ((m : ℝ) + 1 - ((m / 2 : ℕ) : ℝ)) := by
              have hsub : m / 2 ≤ m + 1 := by omega
              rw [Nat.cast_mul, Nat.cast_sub hsub]
              push_cast
              ring
            linarith [hd]
          set B : ℝ := (max A 1 : ℝ) with hB_def
          -- expansion of the archimedean × p-adic product
          have e1 : ((C₀ : ℝ) * B ^ (2 * m)) ^ (m + 1) =
              (C₀ : ℝ) ^ (m + 1) * (B ^ 2) ^ (m * (m + 1)) := by
            have hBpow : (B ^ (2 * m)) ^ (m + 1) = (B ^ 2) ^ (m * (m + 1)) := by
              rw [← pow_mul, show (2 * m * (m + 1) : ℕ) = 2 * (m * (m + 1)) by ring, pow_mul]
            rw [mul_pow, hBpow]
          have e2 : (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) =
              C' ^ (m + 1 - m / 2) * r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by
            have hz : (r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) =
                r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by
              rw [← zpow_natCast, ← zpow_mul]
            rw [mul_pow, hz]
          calc (Nat.factorial (m + 1) : ℝ) * ((C₀ : ℝ) * (max A 1 : ℝ) ^ (2 * m)) ^ (m + 1) *
                (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2)
              ≤ (2 : ℝ) ^ (m * (m + 1)) * ((C₀ : ℝ) * B ^ (2 * m)) ^ (m + 1) *
                  (C' * r ^ (-((m / 2 : ℕ) : ℤ))) ^ (m + 1 - m / 2) := by
                gcongr
            _ = (2 * B ^ 2) ^ (m * (m + 1)) *
                  ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1 - m / 2)) *
                  r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by
                rw [e1, e2]
                have hcomb : (2 : ℝ) ^ (m * (m + 1)) * (B ^ 2) ^ (m * (m + 1)) =
                    (2 * B ^ 2) ^ (m * (m + 1)) := by rw [← mul_pow]
                calc (2 : ℝ) ^ (m * (m + 1)) *
                      ((C₀ : ℝ) ^ (m + 1) * (B ^ 2) ^ (m * (m + 1))) *
                      (C' ^ (m + 1 - m / 2) * r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)))
                    = ((2 : ℝ) ^ (m * (m + 1)) * (B ^ 2) ^ (m * (m + 1))) *
                      ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1 - m / 2)) *
                      r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by ring
                  _ = (2 * B ^ 2) ^ (m * (m + 1)) *
                      ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1 - m / 2)) *
                      r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by rw [hcomb]
            _ ≤ (2 * B ^ 2) ^ (m * (m + 1)) *
                  ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1)) *
                  r ^ (-((m / 2 : ℕ) : ℤ) * ((m + 1 - m / 2 : ℕ) : ℤ)) := by
                have hmid : (2 * B ^ 2) ^ (m * (m + 1)) *
                    ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1 - m / 2)) ≤
                    (2 * B ^ 2) ^ (m * (m + 1)) * ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hC'pow (pow_nonneg (Nat.cast_nonneg _) _))
                    (pow_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg _)) _)
                exact mul_le_mul_of_nonneg_right hmid (zpow_nonneg hr0 _)
            _ ≤ (2 * B ^ 2) ^ (m * (m + 1)) *
                  ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1)) *
                  ((r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ)) := by
                exact mul_le_mul_of_nonneg_left hrpow
                  (mul_nonneg
                    (pow_nonneg (mul_nonneg (by norm_num) (pow_two_nonneg _)) _)
                    (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg hC'0 _)))
            _ = ((C₀ : ℝ) * C') * r ^ (1 / 4 : ℝ) *
                  ((2 * B ^ 2) ^ m * (C₀ : ℝ) ^ m * C' ^ m) *
                  (2 * B ^ 2 / r ^ (1 / 4 : ℝ)) ^ (m * m) := by
                have hpow : (2 * B ^ 2) ^ (m * (m + 1)) =
                    (2 * B ^ 2) ^ (m * m) * (2 * B ^ 2) ^ m := by
                  rw [show (m * (m + 1) : ℕ) = m * m + m by ring, pow_add]
                have hCC : (C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1) =
                    ((C₀ : ℝ) * C') * ((C₀ : ℝ) ^ m * C' ^ m) := by
                  rw [pow_succ, pow_succ]
                  ring
                have hq' : (2 * B ^ 2 / r ^ (1 / 4 : ℝ)) ^ (m * m) =
                    (2 * B ^ 2) ^ (m * m) * (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) := by
                  rw [div_pow, Real.rpow_neg (le_of_lt hrpos')]
                  rw [show (↑m * ↑m : ℝ) = ↑(m * m) by rw [← Nat.cast_mul]]
                  rw [Real.rpow_natCast, div_eq_mul_inv]
                calc (2 * B ^ 2) ^ (m * (m + 1)) *
                      ((C₀ : ℝ) ^ (m + 1) * C' ^ (m + 1)) *
                      ((r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ))
                    = ((2 * B ^ 2) ^ (m * m) * (2 * B ^ 2) ^ m) *
                      (((C₀ : ℝ) * C') * ((C₀ : ℝ) ^ m * C' ^ m)) *
                      ((r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ)) * r ^ (1 / 4 : ℝ)) := by
                      rw [hpow, hCC]
                  _ = ((C₀ : ℝ) * C') * r ^ (1 / 4 : ℝ) *
                      ((2 * B ^ 2) ^ m * (C₀ : ℝ) ^ m * C' ^ m) *
                      ((2 * B ^ 2) ^ (m * m) * (r ^ (1 / 4 : ℝ)) ^ (-(m * m : ℝ))) := by ring
                  _ = ((C₀ : ℝ) * C') * r ^ (1 / 4 : ℝ) *
                      ((2 * B ^ 2) ^ m * (C₀ : ℝ) ^ m * C' ^ m) *
                      (2 * B ^ 2 / r ^ (1 / 4 : ℝ)) ^ (m * m) := by rw [← hq']
            _ ≤ ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) := by
                have hDpow : (2 * B ^ 2) ^ m * (C₀ : ℝ) ^ m * C' ^ m = D ^ m := by
                  dsimp [D, B]
                  rw [← mul_pow, ← mul_pow]
                have hqeq : 2 * B ^ 2 / r ^ (1 / 4 : ℝ) = q := by dsimp [q, B]
                rw [hDpow, hqeq]
                apply mul_le_mul_of_nonneg_right
                · apply mul_le_mul_of_nonneg_right
                  · apply mul_le_mul_of_nonneg_right
                    · linarith
                    · exact le_of_lt hrpos'
                  · exact pow_nonneg hD0 _
                · exact pow_nonneg hq0 _
  -- for large m the product is < 1, so N_{0,m} = 0
  have hN0 : ∃ M, ∀ m ≥ M, hankelDet a 0 m = 0 := by
    have hKpos : 0 < ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) :=
      mul_pos (by linarith [mul_nonneg (Nat.cast_nonneg C₀) hC'0]) hrpos'
    have hε : 0 < (1 : ℝ) / (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ)) :=
      div_pos zero_lt_one hKpos
    obtain ⟨M, hM⟩ := exists_pow_mul_pow_sq_lt hq0 hq1 hD0 hε
    use M
    intro m hm
    have hprod' := hprod m
    have hlt : ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m) < 1 := by
      have := hM m hm
      calc ((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ) * D ^ m * q ^ (m * m)
          = (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ)) * (D ^ m * q ^ (m * m)) := by ring
        _ < (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ)) *
            (1 / (((C₀ : ℝ) * C' + 1) * r ^ (1 / 4 : ℝ))) := by
          gcongr
        _ = 1 := by field_simp
    have hfinal : ((hankelDet a 0 m).natAbs : ℝ) * ‖(hankelDet a 0 m : ℚ_[p])‖ < 1 :=
      lt_of_le_of_lt hprod' hlt
    exact eq_zero_of_natAbs_mul_padicNorm_lt_one hfinal
  -- Kronecker: N_{0,m} = 0 for large m ⇒ linear recurrence over ℚ
  obtain ⟨M, hM⟩ := hN0
  have hkronecker : ∃ (d : ℕ) (c : ℕ → ℚ), c d = 1 ∧ (∀ j > d, c j = 0) ∧
      ∀ n, ∑ j ∈ range (d + 1), c j * (a (n + j) : ℚ) = 0 := by
    apply kronecker_recurrence (fun n => (a n : ℚ))
    use M
    intro m hm
    have := hankel0_cast_det (K := ℚ) a m
    rw [this]
    exact_mod_cast hM m hm
  obtain ⟨d, c, hc1, hc0, hrec⟩ := hkronecker
  -- convert the forward recurrence to HasRecurrencePS (backward form)
  let qcoef : ℕ → ℚ := fun i => if i ≤ d then c (d - i) else 0
  have hrecPS : HasRecurrencePS (mk (fun n => (a n : ℚ))) := by
    refine ⟨d, qcoef, d, le_rfl, ?_, ?_, ?_⟩
    · refine ⟨0, by omega, ?_⟩
      simp [qcoef, hc1]
    · intro i hi
      simp [qcoef, show ¬(i ≤ d) by omega]
    · intro n hn
      simp only [coeff_mk]
      -- ∑ i ≤ d, qcoef i * a (n - i) = ∑ j ≤ d, c j * a (n - d + j) = 0 (forward rec at n - d)
      have hsum : ∑ i ∈ range (d + 1), qcoef i * (a (n - i) : ℚ) =
          ∑ j ∈ range (d + 1), c j * (a (n - d + j) : ℚ) := by
        apply Finset.sum_bij (fun (i : ℕ) _ => d - i)
        · intro i hi
          simp only [mem_range] at hi ⊢
          omega
        · intro i₁ hi₁ i₂ hi₂ h
          simp only [mem_range] at hi₁ hi₂
          omega
        · intro j hj
          refine ⟨d - j, ?_, ?_⟩
          · simp only [mem_range] at hj ⊢
            omega
          · simp only [mem_range] at hj
            omega
        · intro i hi
          simp only [mem_range] at hi
          simp only [qcoef, if_pos (show i ≤ d by omega)]
          rw [show n - i = n - d + (d - i) by omega]
      rw [hsum]
      exact hrec (n - d)
  exact rational_of_recurrence hrecPS

end RHDirect.DworkRat
