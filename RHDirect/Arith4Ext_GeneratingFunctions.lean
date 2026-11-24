/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# `Arith4Ext.GeneratingFunctions`: Reusable Tier A Generating Functions, Partitions & Explicit Asymptotics Engine

Pure-Mathlib, zero-sorry, zero-custom-axiom library extending `Arithmetica4` with:
1. **Formal Power Series & Combinatorial Generating Functions (`PowerSeries`):**
   - Formal derivative `psDeriv` with Leibniz rule and uniqueness up to constants.
   - Catalan numbers `catalanSeq` & generating function `X * C^2 - C + 1 = 0`, central-binomial GF
     `(1 - 4 X) * B^2 = 1`, and closed form `(n + 1) * catalanSeq n = C(2n, n)`.
   - Fibonacci GF `(1 - X - X^2) * F = X`, general 2-term linear constant-coefficient recurrence
     generating functions, Binet's formula for distinct characteristic roots, and explicit coefficient
     growth bounds for linear recurrences and rational generating functions.
2. **Partition Function `p(n)` Identities & Erdős (1942) Elementary Upper Bound:**
   - Explicit `IntPartition n` (`Fintype`), `partitionCount n`, `distinctPartitionCount n`,
     `oddPartitionCount n`.
   - Euler's distinct-equals-odd partition theorem (`p_distinct(n) = p_odd(n)`) via Glaisher's
     binary-decomposition bijection.
   - Euler's Pentagonal Number Theorem (`∏_{k=1}^N (1 - X^k)` via Franklin's involution),
     `partitionGF * pentagonalPS = 1`, and Euler's Pentagonal Recurrence.
   - Divisor-sum identity `n * p(n) = ∑_{t=1}^n ∑_{m=1}^{⌊n/t⌋} m * p(n - m t)` and Erdős's
     elementary upper bound `p(n) ≤ exp(π √(2 n / 3))` (`∀ n : ℕ`).
3. **Explicit Non-Asymptotic Stirling / Robbins & Central-Binomial Sharp Bounds:**
   - Robbins's non-asymptotic two-sided Stirling bounds
     `√(2πn) (n/e)^n exp(1/(12n + 1)) ≤ n! ≤ √(2πn) (n/e)^n exp(1/(12n))`.
   - Sharp two-sided central-binomial bounds `4^n / √(π (n + 1/2)) ≤ C(2n, n) ≤ 4^n / √(π n)`.
   - Binary-entropy upper bounds `C(n, k) ≤ 2^{n H(k/n)}` and tail sum bound for `k ≤ n / 2`.
4. **`q`-Binomial / Gaussian Polynomial Identities:**
   - Both `q`-Pascal recurrences, symmetry `[n choose k]_q = [n choose n - k]_q`, `q = 1`
     specialization, `q`-factorial product identity, `q`-Chu–Vandermonde identity, and the
     `q`-Binomial Theorem `∏_{j=0}^{n-1} (1 + q^j x) = ∑_{k=0}^n q^{k(k-1)/2} [n choose k]_q x^k`.
-/

namespace Arith4Ext.GeneratingFunctions

open scoped BigOperators

/-!
## 1. Formal Power Series & Combinatorial Generating Functions (`PowerSeries`)
-/

section PowerSeriesComb

/-- Shifting a formal power series by `X`: coefficient `n` of `X * F`. -/
theorem coeff_X_mul {R : Type*} [Semiring R] (n : ℕ) (F : PowerSeries R) :
    PowerSeries.coeff n (PowerSeries.X * F) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) F else 0 := by
  rw [PowerSeries.coeff_mul]
  cases n with
  | zero =>
    simp [PowerSeries.coeff_X]
  | succ n =>
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
    have hterm : ∀ p ∈ Finset.antidiagonal (n + 1),
        PowerSeries.coeff p.1 (PowerSeries.X : PowerSeries R) * PowerSeries.coeff p.2 F =
          if p = (1, n) then PowerSeries.coeff n F else 0 := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [PowerSeries.coeff_X]
      by_cases h1 : p.1 = 1
      · have hp_eq : p = (1, n) := Prod.ext h1 (by omega)
        subst hp_eq
        simp
      · have hp_ne : p ≠ (1, n) := fun h => h1 (congrArg Prod.fst h)
        simp [h1, hp_ne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    have hmem : (1, n) ∈ Finset.antidiagonal (n + 1) := by
      rw [Finset.mem_antidiagonal]; omega
    rw [if_pos hmem]

/-- Shifting a formal power series by `X^k`: coefficient `n` of `X^k * F`. -/
theorem coeff_X_pow_mul {R : Type*} [Semiring R] (k n : ℕ) (F : PowerSeries R) :
    PowerSeries.coeff n (PowerSeries.X ^ k * F) =
      if k ≤ n then PowerSeries.coeff (n - k) F else 0 := by
  rw [PowerSeries.coeff_mul]
  by_cases hkn : k ≤ n
  · rw [if_pos hkn]
    have hterm : ∀ p ∈ Finset.antidiagonal n,
        PowerSeries.coeff p.1 ((PowerSeries.X : PowerSeries R) ^ k) * PowerSeries.coeff p.2 F =
          if p = (k, n - k) then PowerSeries.coeff (n - k) F else 0 := by
      intro p hp
      rw [Finset.mem_antidiagonal] at hp
      rw [PowerSeries.coeff_X_pow]
      by_cases h1 : p.1 = k
      · have hp_eq : p = (k, n - k) := Prod.ext h1 (by omega)
        subst hp_eq
        simp
      · have hp_ne : p ≠ (k, n - k) := fun h => h1 (congrArg Prod.fst h)
        simp [h1, hp_ne]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    have hmem : (k, n - k) ∈ Finset.antidiagonal n := by
      rw [Finset.mem_antidiagonal]; omega
    rw [if_pos hmem]
  · rw [if_neg hkn]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

/-- Formal power series derivative `D(∑ a_n X^n) = ∑ (n + 1) a_{n+1} X^n`. -/
noncomputable def psDeriv {R : Type*} [CommRing R] (F : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : R) * PowerSeries.coeff (n + 1) F

@[simp]
theorem coeff_psDeriv {R : Type*} [CommRing R] (F : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (psDeriv F) = ((n + 1 : ℕ) : R) * PowerSeries.coeff (n + 1) F :=
  PowerSeries.coeff_mk n _

theorem psDeriv_C {R : Type*} [CommRing R] (c : R) :
    psDeriv (PowerSeries.C c) = 0 := by
  ext n
  simp

theorem psDeriv_X {R : Type*} [CommRing R] :
    psDeriv (PowerSeries.X : PowerSeries R) = 1 := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_X]
  | succ n => simp [PowerSeries.coeff_X, PowerSeries.coeff_one]

theorem psDeriv_add {R : Type*} [CommRing R] (F G : PowerSeries R) :
    psDeriv (F + G) = psDeriv F + psDeriv G := by
  ext n
  simp only [coeff_psDeriv, map_add]
  ring

theorem psDeriv_neg {R : Type*} [CommRing R] (F : PowerSeries R) :
    psDeriv (-F) = -psDeriv F := by
  ext n
  simp only [coeff_psDeriv, map_neg]
  ring

theorem psDeriv_sub {R : Type*} [CommRing R] (F G : PowerSeries R) :
    psDeriv (F - G) = psDeriv F - psDeriv G := by
  rw [sub_eq_add_neg, psDeriv_add, psDeriv_neg, ← sub_eq_add_neg]

theorem psDeriv_smul {R : Type*} [CommRing R] (c : R) (F : PowerSeries R) :
    psDeriv (c • F) = c • psDeriv F := by
  ext n
  simp only [coeff_psDeriv, PowerSeries.coeff_smul, smul_eq_mul]
  ring

/-- Exact Leibniz product rule for the formal power series derivative `psDeriv`. -/
theorem psDeriv_mul {R : Type*} [CommRing R] (F G : PowerSeries R) :
    psDeriv (F * G) = psDeriv F * G + F * psDeriv G := by
  ext n
  simp only [coeff_psDeriv, map_add, PowerSeries.coeff_mul]
  have hlhs : ((n + 1 : ℕ) : R) *
      ∑ p ∈ Finset.antidiagonal (n + 1), PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G =
      ∑ p ∈ Finset.antidiagonal (n + 1),
        (((p.1 : R) * PowerSeries.coeff p.1 F) * PowerSeries.coeff p.2 G +
          PowerSeries.coeff p.1 F * ((p.2 : R) * PowerSeries.coeff p.2 G)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    have hnat : ((n + 1 : ℕ) : R) = (p.1 : R) + (p.2 : R) := by
      rw [← hp]; push_cast; rfl
    rw [hnat]
    ring
  rw [hlhs, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ Finset.antidiagonal (n + 1),
        ((p.1 : R) * PowerSeries.coeff p.1 F) * PowerSeries.coeff p.2 G =
      ∑ p ∈ Finset.antidiagonal n,
        (((p.1 + 1 : ℕ) : R) * PowerSeries.coeff (p.1 + 1) F) * PowerSeries.coeff p.2 G := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ']
    simp
  have h2 : ∑ p ∈ Finset.antidiagonal (n + 1),
        PowerSeries.coeff p.1 F * ((p.2 : R) * PowerSeries.coeff p.2 G) =
      ∑ p ∈ Finset.antidiagonal n,
        PowerSeries.coeff p.1 F * (((p.2 + 1 : ℕ) : R) * PowerSeries.coeff (p.2 + 1) G) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    have hx1 : n + 1 - x = n - x + 1 := by omega
    rw [hx1]
  rw [h1, h2]

/-- Over a characteristic-zero integral domain, a formal power series with zero derivative is
constant. -/
theorem powerSeries_eq_C_of_psDeriv_eq_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {F : PowerSeries R} (hD : psDeriv F = 0) :
    F = PowerSeries.C (PowerSeries.coeff 0 F) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    have h := congrArg (PowerSeries.coeff n) hD
    simp only [coeff_psDeriv, map_zero] at h
    have hne : ((n + 1 : ℕ) : R) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have h0 : PowerSeries.coeff (n + 1) F = 0 := (mul_eq_zero.mp h).resolve_left hne
    rw [h0, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]

/-- Catalan sequence defined by Segner's convolution recurrence. -/
def catalanSeq : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), catalanSeq i * catalanSeq (n - i)

@[simp]
theorem catalanSeq_zero : catalanSeq 0 = 1 := by unfold catalanSeq; rfl

theorem catalanSeq_succ (n : ℕ) :
    catalanSeq (n + 1) = ∑ i ∈ Finset.range (n + 1), catalanSeq i * catalanSeq (n - i) := by
  conv_lhs => unfold catalanSeq
  simpa using Fin.sum_univ_eq_sum_range (fun i => catalanSeq i * catalanSeq (n - i)) (n + 1)

/-- Catalan generating function `C(X) = ∑_{n≥0} C_n X^n`. -/
noncomputable def catalanGF (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => (catalanSeq n : R)

/-- Catalan generating function satisfies the exact quadratic equation `X * C^2 - C + 1 = 0`. -/
theorem catalanGF_eq (R : Type*) [CommRing R] :
    PowerSeries.X * (catalanGF R) ^ 2 - catalanGF R + 1 = 0 := by
  ext n
  simp only [map_add, map_sub, map_zero, coeff_X_mul, PowerSeries.coeff_one]
  cases n with
  | zero =>
    simp [catalanGF]
  | succ n =>
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
    rw [sq, PowerSeries.coeff_mul]
    simp only [catalanGF, PowerSeries.coeff_mk]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hc : ∑ x ∈ Finset.range (n + 1), (catalanSeq x : R) * (catalanSeq (n - x) : R) =
        (catalanSeq (n + 1) : R) := by
      rw [catalanSeq_succ]
      push_cast
      rfl
    rw [hc]
    simp

/-- Uniqueness of solutions to `X * F^2 - F + 1 = 0` in `PowerSeries R`. -/
theorem eq_catalanGF_of_quad_eq {R : Type*} [CommRing R] {F : PowerSeries R}
    (hF : PowerSeries.X * F ^ 2 - F + 1 = 0) :
    F = catalanGF R := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) hF
    simp only [map_add, map_sub, map_zero, coeff_X_mul, PowerSeries.coeff_one] at hn
    cases n with
    | zero =>
      simp only [catalanGF, PowerSeries.coeff_mk, catalanSeq_zero, Nat.cast_one]
      have h0 : ¬ (1 : ℕ) ≤ 0 := by omega
      rw [if_neg h0, if_pos rfl] at hn
      linear_combination -hn
    | succ n =>
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel] at hn
      rw [if_neg (Nat.succ_ne_zero n), add_zero] at hn
      have hsub : PowerSeries.coeff (n + 1) F = PowerSeries.coeff n (F ^ 2) := by
        linear_combination -hn
      rw [hsub, sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [catalanGF, PowerSeries.coeff_mk, catalanSeq_succ]
      push_cast
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ih i (by omega), ih (n - i) (by omega)]
      simp [catalanGF]

private lemma choose_two_mul_succ_mul (n : ℕ) :
    (n + 1) * Nat.choose (2 * n + 2) (n + 1) = (4 * n + 2) * Nat.choose (2 * n) n := by
  have hL := Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * n + 2 by omega)
  have hR := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have hs1 : 2 * n + 2 - (n + 1) = n + 1 := by omega
  have hs2 : 2 * n - n = n := by omega
  rw [hs1] at hL
  rw [hs2] at hR
  have hf1 : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
  have hf2 : (2 * n + 2).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    ring
  have hmul : ((n + 1) * Nat.choose (2 * n + 2) (n + 1)) * ((n + 1) * n.factorial * n.factorial) =
      ((4 * n + 2) * Nat.choose (2 * n) n) * ((n + 1) * n.factorial * n.factorial) := by
    calc
      ((n + 1) * Nat.choose (2 * n + 2) (n + 1)) * ((n + 1) * n.factorial * n.factorial)
        = (Nat.choose (2 * n + 2) (n + 1) * (n + 1).factorial * (n + 1).factorial) := by
            rw [hf1]; ring
      _ = (2 * n + 2).factorial := hL
      _ = (2 * n + 2) * (2 * n + 1) * (Nat.choose (2 * n) n * n.factorial * n.factorial) := by
            rw [hf2, hR]
      _ = ((4 * n + 2) * Nat.choose (2 * n) n) * ((n + 1) * n.factorial * n.factorial) := by
            ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

private lemma smul_eq_C_mul {R : Type*} [CommRing R] (c : R) (G : PowerSeries R) :
    c • G = PowerSeries.C c * G := by
  ext k
  simp [PowerSeries.coeff_C_mul]

/-- Central binomial generating function `B(X) = ∑_{n≥0} C(2n, n) X^n`. -/
noncomputable def centralBinomGF (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => (Nat.choose (2 * n) n : R)

/-- Exact identity `(1 - 4 X) * B(X)^2 = 1`, equivalently
`∑_{i=0}^n C(2i, i) C(2(n-i), n-i) = 4^n`. -/
theorem centralBinomGF_sq_eq :
    (1 - (4 : ℚ) • (PowerSeries.X : PowerSeries ℚ)) * (centralBinomGF ℚ) ^ 2 = 1 := by
  set B : PowerSeries ℚ := centralBinomGF ℚ
  set Q : PowerSeries ℚ := 1 - (4 : ℚ) • (PowerSeries.X : PowerSeries ℚ)
  have hB_ode : Q * psDeriv B = (2 : ℚ) • B := by
    ext n
    have hsmulX : (4 : ℚ) • (PowerSeries.X : PowerSeries ℚ) * psDeriv B =
        (4 : ℚ) • (PowerSeries.X * psDeriv B) := Algebra.smul_mul_assoc _ _ _
    rw [show Q * psDeriv B = psDeriv B - (4 : ℚ) • (PowerSeries.X * psDeriv B) by
      dsimp only [Q]; rw [sub_mul, one_mul, hsmulX]]
    rw [map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
      coeff_X_mul, coeff_psDeriv, coeff_psDeriv]
    simp only [B, centralBinomGF, PowerSeries.coeff_mk]
    cases n with
    | zero =>
      norm_num
    | succ n =>
      rw [if_pos (by omega)]
      have hsub : n + 1 - 1 = n := by omega
      rw [hsub]
      have hrel : ((n + 2 : ℕ) : ℚ) * (Nat.choose (2 * n + 4) (n + 2) : ℚ) =
          ((4 * n + 6 : ℕ) : ℚ) * (Nat.choose (2 * n + 2) (n + 1) : ℚ) := by
        have hnat := choose_two_mul_succ_mul (n + 1)
        have ha : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
        have hb : 2 * (n + 1) = 2 * n + 2 := by omega
        have hc : 4 * (n + 1) + 2 = 4 * n + 6 := by omega
        rw [ha, hb, hc] at hnat
        exact_mod_cast hnat
      have hsucc : n + 1 + 1 = n + 2 := by omega
      have hmul2 : 2 * (n + 1 + 1) = 2 * n + 4 := by omega
      have hmul1 : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hsucc, hmul2, hmul1]
      push_cast at hrel ⊢
      linarith
  have hQ_deriv : psDeriv Q = -PowerSeries.C (4 : ℚ) := by
    dsimp only [Q]
    have h1 : (1 : PowerSeries ℚ) = PowerSeries.C 1 := (map_one PowerSeries.C).symm
    rw [psDeriv_sub, h1, psDeriv_C, psDeriv_smul, psDeriv_X, zero_sub,
      smul_eq_C_mul, mul_one]
  have hP_deriv : psDeriv (Q * B ^ 2) = 0 := by
    rw [psDeriv_mul, sq, psDeriv_mul, hQ_deriv]
    calc
      -PowerSeries.C (4 : ℚ) * (B * B) + Q * (psDeriv B * B + B * psDeriv B)
        = (-(4 : ℚ) • B + (2 : ℚ) • (Q * psDeriv B)) * B := by
          simp only [smul_eq_C_mul, map_ofNat, map_neg]
          ring
      _ = (-(4 : ℚ) • B + (2 : ℚ) • ((2 : ℚ) • B)) * B := by rw [hB_ode]
      _ = 0 := by
          have h0 : -(4 : ℚ) • B + (2 : ℚ) • ((2 : ℚ) • B) = 0 := by
            simp only [smul_eq_C_mul, map_ofNat, map_neg]; ring
          rw [h0, zero_mul]
  have hP_const := powerSeries_eq_C_of_psDeriv_eq_zero hP_deriv
  have h0 : PowerSeries.coeff 0 (Q * B ^ 2) = 1 := by
    have hQ0 : PowerSeries.coeff 0 Q = 1 := by
      dsimp only [Q]
      rw [map_sub, PowerSeries.coeff_one, if_pos rfl, PowerSeries.coeff_smul, smul_eq_mul,
        PowerSeries.coeff_zero_X, mul_zero, sub_zero]
    have hB0 : PowerSeries.coeff 0 B = 1 := by
      simp [B, centralBinomGF]
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.sum_range_one, Nat.sub_zero, hQ0, sq, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hB0, mul_one]
  change Q * B ^ 2 = 1
  rw [hP_const, h0, map_one]

/-- Self-contained convolution identity `∑_{i=0}^n C(2i, i) C(2(n-i), n-i) = 4^n`. -/
theorem sum_centralBinom_mul_centralBinom (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.choose (2 * i) i * Nat.choose (2 * (n - i)) (n - i) =
      4 ^ n := by
  have hrec : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1),
      (Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * (k - i)) (k - i) : ℚ)) = (4 : ℚ) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hcoeff := congrArg (PowerSeries.coeff (k + 1)) centralBinomGF_sq_eq
      have hsmul : (4 : ℚ) • (PowerSeries.X : PowerSeries ℚ) * (centralBinomGF ℚ) ^ 2 =
          (4 : ℚ) • (PowerSeries.X * (centralBinomGF ℚ) ^ 2) := Algebra.smul_mul_assoc _ _ _
      rw [sub_mul, one_mul, hsmul, map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_X_mul,
        if_pos (by omega), PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k)] at hcoeff
      have hk1 : k + 1 - 1 = k := by omega
      rw [hk1] at hcoeff
      have hB2_succ : PowerSeries.coeff (k + 1) ((centralBinomGF ℚ) ^ 2) =
          4 * PowerSeries.coeff k ((centralBinomGF ℚ) ^ 2) := by
        linear_combination hcoeff
      have hsum_fn : ∀ m : ℕ, PowerSeries.coeff m ((centralBinomGF ℚ) ^ 2) =
          ∑ i ∈ Finset.range (m + 1),
            (Nat.choose (2 * i) i : ℚ) * (Nat.choose (2 * (m - i)) (m - i) : ℚ) := by
        intro m
        rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp [centralBinomGF]
      rw [← hsum_fn (k + 1), hB2_succ, hsum_fn k, ih]
      ring
  exact_mod_cast hrec n

/-- Closed-form Catalan formula `(n + 1) * catalanSeq n = Nat.choose (2 * n) n`. -/
theorem catalanSeq_closed_form (n : ℕ) :
    (n + 1) * catalanSeq n = Nat.choose (2 * n) n := by
  let A : PowerSeries ℚ := PowerSeries.mk fun k => (Nat.choose (2 * k) k : ℚ) / (k + 1 : ℚ)
  let B := centralBinomGF ℚ
  let Q : PowerSeries ℚ := 1 - (4 : ℚ) • PowerSeries.X
  have hBA : B * Q = 1 - (2 : ℚ) • (PowerSeries.X * A) := by
    ext k
    have hX : B * ((4 : ℚ) • PowerSeries.X) = (4 : ℚ) • (PowerSeries.X * B) := by
      rw [Algebra.mul_smul_comm, mul_comm B PowerSeries.X]
    dsimp only [Q]
    rw [mul_sub, mul_one, hX, map_sub, map_sub, PowerSeries.coeff_smul, PowerSeries.coeff_smul,
      smul_eq_mul, smul_eq_mul, PowerSeries.coeff_one, coeff_X_mul, coeff_X_mul]
    cases k with
    | zero =>
      simp [B, centralBinomGF]
    | succ k =>
      have hk0 : ¬ k + 1 = 0 := Nat.succ_ne_zero k
      have hk1 : (1 : ℕ) ≤ k + 1 := by omega
      have hsub : k + 1 - 1 = k := by omega
      rw [if_neg hk0, if_pos hk1, hsub]
      simp only [B, centralBinomGF, A, PowerSeries.coeff_mk]
      have hrel : ((k + 1 : ℕ) : ℚ) * (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) =
          ((4 * k + 2 : ℕ) : ℚ) * (Nat.choose (2 * k) k : ℚ) := by
        exact_mod_cast choose_two_mul_succ_mul k
      have hk1_ne : (k : ℚ) + 1 ≠ 0 := by positivity
      calc
        (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) - 4 * (Nat.choose (2 * k) k : ℚ)
          = ((4 * (k : ℚ) + 2) * (Nat.choose (2 * k) k : ℚ) / ((k : ℚ) + 1)) -
              4 * (Nat.choose (2 * k) k : ℚ) := by
                have hdiv : (Nat.choose (2 * (k + 1)) (k + 1) : ℚ) =
                    (4 * (k : ℚ) + 2) * (Nat.choose (2 * k) k : ℚ) / ((k : ℚ) + 1) := by
                  push_cast at hrel
                  field_simp [hk1_ne]
                  linarith
                rw [hdiv]
        _ = 0 - 2 * ((Nat.choose (2 * k) k : ℚ) / ((k : ℚ) + 1)) := by
            field_simp [hk1_ne]; ring
  have hAsq : (1 - (2 : ℚ) • (PowerSeries.X * A)) ^ 2 = Q := by
    rw [← hBA]
    calc
      (B * Q) ^ 2 = Q * (Q * B ^ 2) := by ring
      _ = Q * 1 := by rw [centralBinomGF_sq_eq]
      _ = Q := mul_one Q
  have hXquad : (4 : ℚ) • (PowerSeries.X * (PowerSeries.X * A ^ 2 - A + 1)) = 0 := by
    have hexp : (1 - (2 : ℚ) • (PowerSeries.X * A)) ^ 2 - Q =
        (4 : ℚ) • (PowerSeries.X * (PowerSeries.X * A ^ 2 - A + 1)) := by
      dsimp only [Q]
      simp only [smul_eq_C_mul, map_ofNat]
      ring
    rw [hAsq, sub_self] at hexp
    exact hexp.symm
  have hquad : PowerSeries.X * A ^ 2 - A + 1 = 0 := by
    ext k
    have hc := congrArg (PowerSeries.coeff (k + 1)) hXquad
    rw [PowerSeries.coeff_smul, smul_eq_mul, coeff_X_mul, if_pos (by omega),
      show k + 1 - 1 = k by omega, map_zero] at hc
    exact (mul_eq_zero.mp hc).resolve_left (by norm_num)
  have hA_eq : A = catalanGF ℚ := eq_catalanGF_of_quad_eq hquad
  have hc := congrArg (PowerSeries.coeff n) hA_eq
  simp only [A, catalanGF, PowerSeries.coeff_mk] at hc
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hq : ((n + 1 : ℕ) : ℚ) * (catalanSeq n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    rw [← hc]
    push_cast
    field_simp [hn1]
  exact_mod_cast hq

theorem catalanSeq_eq_div (n : ℕ) :
    (catalanSeq n : ℚ) = (Nat.choose (2 * n) n : ℚ) / (n + 1 : ℚ) := by
  have h := catalanSeq_closed_form n
  have hq : ((n + 1 : ℕ) : ℚ) * (catalanSeq n : ℚ) = (Nat.choose (2 * n) n : ℚ) := by
    exact_mod_cast h
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hn1]
  push_cast at hq
  linarith

/-- Fibonacci sequence `F_0 = 0, F_1 = 1, F_{n+2} = F_{n+1} + F_n`. -/
def fibSeq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibSeq (n + 1) + fibSeq n

@[simp] theorem fibSeq_zero : fibSeq 0 = 0 := rfl
@[simp] theorem fibSeq_one : fibSeq 1 = 1 := rfl
@[simp] theorem fibSeq_add_two (n : ℕ) : fibSeq (n + 2) = fibSeq (n + 1) + fibSeq n := rfl

/-- General 2-term linear constant-coefficient recurrence GF identity:
if `a (n + 2) = c₁ * a (n + 1) + c₂ * a n`, then
`(1 - c₁ • X - c₂ • X^2) * ∑ a_n X^n = C (a 0) + C (a 1 - c₁ * a 0) * X`. -/
theorem linearRecurrence2GF_eq {R : Type*} [CommRing R] (a : ℕ → R) (c₁ c₂ : R)
    (hrec : ∀ n : ℕ, a (n + 2) = c₁ * a (n + 1) + c₂ * a n) :
    (1 - c₁ • PowerSeries.X - c₂ • (PowerSeries.X : PowerSeries R) ^ 2) * PowerSeries.mk a =
      PowerSeries.C (a 0) + PowerSeries.C (a 1 - c₁ * a 0) * PowerSeries.X := by
  ext n
  have hsmulX : (c₁ • (PowerSeries.X : PowerSeries R)) * PowerSeries.mk a =
      c₁ • (PowerSeries.X * PowerSeries.mk a) := Algebra.smul_mul_assoc _ _ _
  have hsmulX2 : (c₂ • (PowerSeries.X : PowerSeries R) ^ 2) * PowerSeries.mk a =
      c₂ • ((PowerSeries.X : PowerSeries R) ^ 2 * PowerSeries.mk a) := Algebra.smul_mul_assoc _ _ _
  rw [sub_mul, sub_mul, one_mul, hsmulX, hsmulX2, map_sub, map_sub,
    PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
    coeff_X_mul, coeff_X_pow_mul, map_add]
  simp only [PowerSeries.coeff_mk]
  rcases n with _ | _ | n
  · simp
  · simp [mul_comm]
  · have hc0 : PowerSeries.coeff (n + 2) (PowerSeries.C (a 0)) = 0 := by
      rw [PowerSeries.coeff_C, if_neg (by omega)]
    have hcx : PowerSeries.coeff (n + 2) (PowerSeries.C (a 1 - c₁ * a 0) * PowerSeries.X) = 0 := by
      rw [mul_comm, coeff_X_mul, if_pos (by omega), PowerSeries.coeff_C, if_neg (by omega)]
    rw [hc0, hcx, add_zero, if_pos (by omega), if_pos (by omega)]
    have hr := hrec n
    have h1 : n + 2 - 1 = n + 1 := by omega
    have h2 : n + 2 - 2 = n := by omega
    rw [h1, h2]
    linear_combination hr

/-- Fibonacci generating function `F(X) = ∑_{n≥0} F_n X^n`. -/
noncomputable def fibGF (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.mk fun n => (fibSeq n : R)

/-- Exact Fibonacci GF identity `(1 - X - X^2) * fibGF R = X`. -/
theorem fibGF_eq (R : Type*) [CommRing R] :
    (1 - PowerSeries.X - (PowerSeries.X : PowerSeries R) ^ 2) * fibGF R = PowerSeries.X := by
  have h := linearRecurrence2GF_eq (fun n => (fibSeq n : R)) 1 1 fun n => by
    simp [fibSeq_add_two]
  simpa [fibGF, one_smul] using h

/-- **Binet Formula for Distinct Characteristic Roots:** if `a (n + 2) = c₁ * a (n + 1) + c₂ * a n`
and `r₁ ≠ r₂` satisfy `r_i^2 = c₁ * r_i + c₂`, then `a n = α * r₁^n + β * r₂^n` explicitly. -/
theorem binet_distinct_roots {F : Type*} [Field F] (a : ℕ → F) (c₁ c₂ r₁ r₂ : F)
    (hrec : ∀ n : ℕ, a (n + 2) = c₁ * a (n + 1) + c₂ * a n)
    (hr₁ : r₁ ^ 2 = c₁ * r₁ + c₂) (hr₂ : r₂ ^ 2 = c₁ * r₂ + c₂) (hne : r₁ ≠ r₂) :
    let α := (a 1 - r₂ * a 0) / (r₁ - r₂)
    let β := (r₁ * a 0 - a 1) / (r₁ - r₂)
    ∀ n : ℕ, a n = α * r₁ ^ n + β * r₂ ^ n := by
  intro α β n
  have hdiff : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr hne
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · dsimp only [α, β]
      field_simp [hdiff]
      ring
    · dsimp only [α, β]
      field_simp [hdiff]
      ring
    · rw [hrec n, ih (n + 1) (by omega), ih n (by omega)]
      have hp1 : r₁ ^ (n + 2) = (c₁ * r₁ + c₂) * r₁ ^ n := by
        rw [← hr₁, pow_add]; ring
      have hp2 : r₂ ^ (n + 2) = (c₁ * r₂ + c₂) * r₂ ^ n := by
        rw [← hr₂, pow_add]; ring
      rw [hp1, hp2]
      ring

/-- Coefficient upper bound for 2-term linear recurrences with distinct real roots. -/
theorem binet_coeff_bound (a : ℕ → ℝ) (c₁ c₂ r₁ r₂ : ℝ)
    (hrec : ∀ n : ℕ, a (n + 2) = c₁ * a (n + 1) + c₂ * a n)
    (hr₁ : r₁ ^ 2 = c₁ * r₁ + c₂) (hr₂ : r₂ ^ 2 = c₁ * r₂ + c₂) (hne : r₁ ≠ r₂) :
    let α := (a 1 - r₂ * a 0) / (r₁ - r₂)
    let β := (r₁ * a 0 - a 1) / (r₁ - r₂)
    ∀ n : ℕ, |a n| ≤ (|α| + |β|) * (max |r₁| |r₂|) ^ n := by
  intro α β n
  rw [binet_distinct_roots a c₁ c₂ r₁ r₂ hrec hr₁ hr₂ hne n]
  calc
    |α * r₁ ^ n + β * r₂ ^ n| ≤ |α * r₁ ^ n| + |β * r₂ ^ n| := abs_add_le _ _
    _ = |α| * |r₁| ^ n + |β| * |r₂| ^ n := by simp [abs_mul, abs_pow]
    _ ≤ |α| * (max |r₁| |r₂|) ^ n + |β| * (max |r₁| |r₂|) ^ n := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) n) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) n) (abs_nonneg _)
    _ = (|α| + |β|) * (max |r₁| |r₂|) ^ n := by ring

/-- Exact **Binet Formula** for Fibonacci numbers: `F_n = (φ^n - ψ^n) / √5`. -/
theorem fibSeq_binet (n : ℕ) :
    (fibSeq n : ℝ) =
      (((1 + Real.sqrt 5) / 2) ^ n - ((1 - Real.sqrt 5) / 2) ^ n) / Real.sqrt 5 := by
  let φ : ℝ := (1 + Real.sqrt 5) / 2
  let ψ : ℝ := (1 - Real.sqrt 5) / 2
  have h5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hφ : φ ^ 2 = 1 * φ + 1 := by
    dsimp only [φ]
    nlinarith [h5_sq]
  have hψ : ψ ^ 2 = 1 * ψ + 1 := by
    dsimp only [ψ]
    nlinarith [h5_sq]
  have hne : φ ≠ ψ := by
    dsimp only [φ, ψ]
    intro h
    linarith
  have hbin := binet_distinct_roots (fun k => (fibSeq k : ℝ)) 1 1 φ ψ
    (fun k => by simp [fibSeq_add_two]) hφ hψ hne n
  rw [hbin]
  dsimp only [fibSeq_zero, fibSeq_one, Nat.cast_zero, Nat.cast_one]
  have hdiff : φ - ψ = Real.sqrt 5 := by dsimp only [φ, ψ]; ring
  rw [hdiff]
  ring

/-- Sharp exponential bound `F_n ≤ φ^n` (`∀ n : ℕ`). -/
theorem fibSeq_le_golden_pow (n : ℕ) :
    (fibSeq n : ℝ) ≤ ((1 + Real.sqrt 5) / 2) ^ n := by
  let φ : ℝ := (1 + Real.sqrt 5) / 2
  have hφ_ge : (1 : ℝ) ≤ φ := by
    dsimp only [φ]
    have h1 : (1 : ℝ) ≤ Real.sqrt 5 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · simp
    · simpa using hφ_ge
    · rw [fibSeq_add_two]
      push_cast
      have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have hφ2 : φ ^ 2 = φ + 1 := by dsimp only [φ]; nlinarith [h5]
      calc
        (fibSeq (n + 1) : ℝ) + (fibSeq n : ℝ)
          ≤ φ ^ (n + 1) + φ ^ n := add_le_add (ih (n + 1) (by omega)) (ih n (by omega))
        _ = (φ + 1) * φ ^ n := by ring
        _ = φ ^ 2 * φ ^ n := by rw [hφ2]
        _ = φ ^ (n + 2) := by rw [← pow_add]; ring

/-- Coefficient bound for any rational GF `(1 - r₁ X)(1 - r₂ X) F = c₀ + c₁ X` with `r₁ ≠ r₂`. -/
theorem rationalGF_two_root_coeff_bound (F : PowerSeries ℝ) (r₁ r₂ c₀ c₁ : ℝ) (hne : r₁ ≠ r₂)
    (hGF : (1 - r₁ • PowerSeries.X) * (1 - r₂ • PowerSeries.X) * F =
      PowerSeries.C c₀ + PowerSeries.C c₁ * PowerSeries.X) :
    let a₀ := PowerSeries.coeff 0 F
    let a₁ := PowerSeries.coeff 1 F
    let α := (a₁ - r₂ * a₀) / (r₁ - r₂)
    let β := (r₁ * a₀ - a₁) / (r₁ - r₂)
    ∀ n : ℕ, |PowerSeries.coeff n F| ≤ (|α| + |β|) * (max |r₁| |r₂|) ^ n := by
  have hpoly : (1 - r₁ • PowerSeries.X) * (1 - r₂ • PowerSeries.X) =
      1 - (r₁ + r₂) • PowerSeries.X - (-(r₁ * r₂)) • (PowerSeries.X : PowerSeries ℝ) ^ 2 := by
    simp only [smul_eq_C_mul, map_add, map_neg, map_mul]
    ring
  have hrec : ∀ n : ℕ, PowerSeries.coeff (n + 2) F =
      (r₁ + r₂) * PowerSeries.coeff (n + 1) F + (-(r₁ * r₂)) * PowerSeries.coeff n F := by
    intro n
    have hcoeff := congrArg (PowerSeries.coeff (n + 2)) hGF
    rw [hpoly] at hcoeff
    have hsmul1 : ((r₁ + r₂) • (PowerSeries.X : PowerSeries ℝ)) * F =
        (r₁ + r₂) • (PowerSeries.X * F) := Algebra.smul_mul_assoc _ _ _
    have hsmul2 : ((-(r₁ * r₂)) • (PowerSeries.X : PowerSeries ℝ) ^ 2) * F =
        (-(r₁ * r₂)) • ((PowerSeries.X : PowerSeries ℝ) ^ 2 * F) := Algebra.smul_mul_assoc _ _ _
    rw [sub_mul, sub_mul, one_mul, hsmul1, hsmul2, map_sub, map_sub,
      PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
      coeff_X_mul, coeff_X_pow_mul, map_add] at hcoeff
    have hc0 : PowerSeries.coeff (n + 2) (PowerSeries.C c₀) = 0 := by
      rw [PowerSeries.coeff_C, if_neg (by omega)]
    have hc1 : PowerSeries.coeff (n + 2) (PowerSeries.C c₁ * PowerSeries.X) = 0 := by
      rw [mul_comm, coeff_X_mul, if_pos (by omega), PowerSeries.coeff_C, if_neg (by omega)]
    rw [hc0, hc1, add_zero, if_pos (by omega), if_pos (by omega)] at hcoeff
    have hsub1 : n + 2 - 1 = n + 1 := by omega
    have hsub2 : n + 2 - 2 = n := by omega
    rw [hsub1, hsub2] at hcoeff
    linarith
  have hr₁ : r₁ ^ 2 = (r₁ + r₂) * r₁ + -(r₁ * r₂) := by ring
  have hr₂ : r₂ ^ 2 = (r₁ + r₂) * r₂ + -(r₁ * r₂) := by ring
  exact binet_coeff_bound (fun n => PowerSeries.coeff n F) (r₁ + r₂) (-(r₁ * r₂)) r₁ r₂
    hrec hr₁ hr₂ hne

end PowerSeriesComb

/-!
## 2. Partition Function `p(n)` Identities & Erdős (1942) Elementary Upper Bound
-/

section Partitions

/-- Integer partition of `n` represented by its part-multiplicity vector `mult : Fin (n + 1) → ℕ`. -/
@[ext]
structure IntPartition (n : ℕ) where
  mult : Fin (n + 1) → ℕ
  mult_zero : mult 0 = 0
  sum_eq : ∑ k : Fin (n + 1), k.val * mult k = n

namespace IntPartition

theorem mult_le {n : ℕ} (P : IntPartition n) (k : Fin (n + 1)) : P.mult k ≤ n := by
  by_cases hk : k.val = 0
  · have h0 : k = 0 := Fin.ext hk
    rw [h0, P.mult_zero]
    exact Nat.zero_le n
  · have hk1 : 1 ≤ k.val := Nat.one_le_iff_ne_zero.mpr hk
    calc
      P.mult k ≤ k.val * P.mult k := Nat.le_mul_of_pos_left _ hk1
      _ ≤ ∑ j : Fin (n + 1), j.val * P.mult j :=
        Finset.single_le_sum (f := fun j : Fin (n + 1) => j.val * P.mult j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ = n := P.sum_eq

noncomputable instance (n : ℕ) : Fintype (IntPartition n) :=
  Fintype.ofInjective
    (fun (P : IntPartition n) (k : Fin (n + 1)) =>
      (⟨P.mult k, Nat.lt_succ_of_le (P.mult_le k)⟩ : Fin (n + 1)))
    (fun P Q h => by
      ext k
      have hk := congrFun h k
      exact congrArg Fin.val hk)

end IntPartition

/-- Total number of integer partitions of `n`: `p(n)`. -/
noncomputable def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (IntPartition n)

/-- Number of partitions of `n` into distinct parts (`mult k ≤ 1` for all `k`). -/
noncomputable def distinctPartitionCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun P : IntPartition n => ∀ k : Fin (n + 1), P.mult k ≤ 1).card

/-- Number of partitions of `n` into odd parts (`mult k ≠ 0 → Odd k`). -/
noncomputable def oddPartitionCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun P : IntPartition n => ∀ k : Fin (n + 1), P.mult k ≠ 0 → Odd k.val).card

private def splitTwoPow : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | m + 1 =>
    if (m + 1) % 2 = 0 then
      let p := splitTwoPow ((m + 1) / 2)
      (p.1, p.2 + 1)
    else
      (m + 1, 0)
termination_by m => m
decreasing_by exact Nat.div_lt_self (Nat.succ_pos m) (by norm_num)

private lemma splitTwoPow_spec (m : ℕ) (hm : 1 ≤ m) :
    Odd (splitTwoPow m).1 ∧ (splitTwoPow m).1 * 2 ^ (splitTwoPow m).2 = m ∧
      (splitTwoPow m).1 ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | m
    · omega
    · unfold splitTwoPow
      by_cases h2 : (m + 1) % 2 = 0
      · rw [if_pos h2]
        have hhalf_lt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by norm_num)
        have hhalf_ge : 1 ≤ (m + 1) / 2 := by omega
        obtain ⟨hodd, hmul, hle⟩ := ih ((m + 1) / 2) hhalf_lt hhalf_ge
        refine ⟨hodd, ?_, ?_⟩
        · dsimp only
          rw [pow_succ, ← mul_assoc, hmul]
          omega
        · dsimp only
          omega
      · rw [if_neg h2]
        refine ⟨?_, by simp, le_rfl⟩
        rw [Nat.odd_iff]
        omega

private lemma splitTwoPow_mul_two_pow {k : ℕ} (hk : Odd k) (j : ℕ) :
    splitTwoPow (k * 2 ^ j) = (k, j) := by
  induction j with
  | zero =>
    have hk_ne : k ≠ 0 := by rintro rfl; simp at hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne
    rw [pow_zero, mul_one]
    unfold splitTwoPow
    rw [if_neg (by rw [Nat.odd_iff] at hk; omega)]
  | succ j ih =>
    have hmul_ne : k * 2 ^ (j + 1) ≠ 0 := by
      have hk0 : k ≠ 0 := by rintro rfl; simp at hk
      positivity
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hmul_ne
    have h2 : (k * 2 ^ (j + 1)) % 2 = 0 := by
      rw [pow_succ, ← mul_assoc]
      omega
    have hdiv : (k * 2 ^ (j + 1)) / 2 = k * 2 ^ j := by
      rw [pow_succ, ← mul_assoc]
      omega
    have h2m : (m + 1) % 2 = 0 := by omega
    have hdivm : (m + 1) / 2 = k * 2 ^ j := by omega
    conv_lhs => rw [hm]; unfold splitTwoPow
    rw [if_pos h2m, hdivm, ih]

private lemma binary_bit_sum_eq (b m : ℕ) (hm : m < 2 ^ b) :
    ∑ j ∈ Finset.range b, (if m.testBit j then 1 else 0) * 2 ^ j = m := by
  induction b generalizing m with
  | zero =>
    simp at hm
    simp [hm]
  | succ b ih =>
    rw [Finset.sum_range_succ']
    have hdiv_lt : m / 2 < 2 ^ b := by
      rw [pow_succ] at hm
      omega
    have hbit0 : (if m.testBit 0 then 1 else 0) = m % 2 := by
      rw [Nat.testBit_zero]
      by_cases hmod : m % 2 = 1
      · simp [hmod]
      · have h0 : m % 2 = 0 := by omega
        simp [h0]
    have hshift : ∀ j : ℕ, m.testBit (j + 1) = (m / 2).testBit j := by
      intro j
      rw [Nat.testBit_succ]
    simp only [hshift, pow_zero, mul_one, hbit0]
    have hmul : ∑ x ∈ Finset.range b, (if (m / 2).testBit x then 1 else 0) * 2 ^ (x + 1) =
        2 * ∑ x ∈ Finset.range b, (if (m / 2).testBit x then 1 else 0) * 2 ^ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pow_succ]
      ring
    rw [hmul, ih (m / 2) hdiv_lt]
    omega

private lemma testBit_binary_sum (b : ℕ) (f : ℕ → ℕ) (hf : ∀ j, f j ≤ 1) (i : ℕ) :
    (∑ j ∈ Finset.range b, f j * 2 ^ j).testBit i =
      if i < b then decide (f i = 1) else false := by
  induction b generalizing f i with
  | zero =>
    simp
  | succ b ih =>
    rw [Finset.sum_range_succ']
    have hmul : ∑ x ∈ Finset.range b, f (x + 1) * 2 ^ (x + 1) =
        2 * ∑ x ∈ Finset.range b, f (x + 1) * 2 ^ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pow_succ]
      ring
    rw [pow_zero, mul_one, hmul]
    set S := ∑ x ∈ Finset.range b, f (x + 1) * 2 ^ x
    have hf0 : f 0 = 0 ∨ f 0 = 1 := by have := hf 0; omega
    cases i with
    | zero =>
      rw [Nat.testBit_zero, if_pos (Nat.succ_pos b)]
      rcases hf0 with h0 | h1
      · simp [h0]
      · simp [h1]
    | succ i =>
      rw [Nat.testBit_succ]
      have hdiv : (2 * S + f 0) / 2 = S := by
        rcases hf0 with h0 | h1 <;> omega
      rw [hdiv, ih (fun j => f (j + 1)) (fun j => hf (j + 1)) i]
      by_cases hi : i < b <;> simp [hi]

private lemma partition_mul_mult_le {n : ℕ} (P : IntPartition n) (k : Fin (n + 1)) :
    k.val * P.mult k ≤ n := by
  have hle : k.val * P.mult k ≤ ∑ i : Fin (n + 1), i.val * P.mult i :=
    Finset.single_le_sum (f := fun i : Fin (n + 1) => i.val * P.mult i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  simpa [P.sum_eq] using hle

private lemma testBit_eq_true_le {b m j : ℕ} (hm : m < 2 ^ b) (hj : j < b)
    (hbit : Nat.testBit m j = true) : 2 ^ j ≤ m := by
  have hsum := binary_bit_sum_eq b m hm
  have hle : (if Nat.testBit m j then 1 else 0) * 2 ^ j ≤
      ∑ i ∈ Finset.range b, (if Nat.testBit m i then 1 else 0) * 2 ^ i :=
    Finset.single_le_sum (f := fun i => (if Nat.testBit m i then 1 else 0) * 2 ^ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  rw [hbit, if_pos rfl, one_mul, hsum] at hle
  exact hle

private lemma oddPartition_toDist_sum {n : ℕ} (P : IntPartition n)
    (hPodd : ∀ k : Fin (n + 1), P.mult k ≠ 0 → Odd k.val) :
    ∑ d : Fin (n + 1), d.val *
      (if hd : 1 ≤ d.val then
        have hp_le : (splitTwoPow d.val).1 < n + 1 := by
          have := (splitTwoPow_spec d.val hd).2.2
          have _hd_lt : d.val < n + 1 := d.isLt
          omega
        if Nat.testBit (P.mult ⟨(splitTwoPow d.val).1, hp_le⟩) (splitTwoPow d.val).2 then 1 else 0
      else 0) = n := by
  have hlt2n : ∀ m : ℕ, m ≤ n → m < 2 ^ (n + 1) := fun m hm => by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
    omega
  let f : Fin (n + 1) → ℕ := fun d =>
    if hd : 1 ≤ d.val then
      have hp_le : (splitTwoPow d.val).1 < n + 1 := by
        have := (splitTwoPow_spec d.val hd).2.2
        have _hd_lt : d.val < n + 1 := d.isLt
        omega
      if Nat.testBit (P.mult ⟨(splitTwoPow d.val).1, hp_le⟩) (splitTwoPow d.val).2 then 1 else 0
    else 0
  change ∑ d : Fin (n + 1), d.val * f d = n
  have hLHS1 : ∑ d : Fin (n + 1), d.val * f d =
      ∑ d ∈ Finset.Icc 1 n,
        (if hd : 1 ≤ d then
          if hd_lt : d < n + 1 then
            have hp_le : (splitTwoPow d).1 < n + 1 := by
              have := (splitTwoPow_spec d hd).2.2
              omega
            if Nat.testBit (P.mult ⟨(splitTwoPow d).1, hp_le⟩) (splitTwoPow d).2 then d else 0
          else 0
        else 0) := by
    have hrange : ∑ d : Fin (n + 1), d.val * f d =
        ∑ d ∈ Finset.range (n + 1), if h : d < n + 1 then d * f ⟨d, h⟩ else 0 := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => if h : d < n + 1 then d * f ⟨d, h⟩ else 0) (n + 1)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [dif_pos d.isLt]
    rw [hrange, Finset.sum_range_succ']
    simp only [dif_pos (Nat.succ_pos n), zero_mul, add_zero]
    have hIcc : Finset.Icc 1 n = (Finset.range n).image Nat.succ := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        omega
    rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha1 : 1 ≤ a + 1 := by omega
    have ha_lt : a + 1 < n + 1 := by
      rw [Finset.mem_range] at ha
      omega
    change (if h : a + 1 < n + 1 then (a + 1) * f ⟨a + 1, h⟩ else 0) = _
    rw [dif_pos ha_lt]
    simp only [f, dif_pos ha1, dif_pos ha_lt]
    split_ifs <;> simp
  let S_d := (Finset.Icc 1 n).filter fun d =>
    ∃ (hd : 1 ≤ d) (hp_le : (splitTwoPow d).1 < n + 1),
      Nat.testBit (P.mult ⟨(splitTwoPow d).1, hp_le⟩) (splitTwoPow d).2 = true
  have hLHS2 : ∑ d ∈ Finset.Icc 1 n,
        (if hd : 1 ≤ d then
          if hd_lt : d < n + 1 then
            have hp_le : (splitTwoPow d).1 < n + 1 := by
              have := (splitTwoPow_spec d hd).2.2
              omega
            if Nat.testBit (P.mult ⟨(splitTwoPow d).1, hp_le⟩) (splitTwoPow d).2 then d else 0
          else 0
        else 0) = ∑ d ∈ S_d, d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hd_lt : d < n + 1 := by
      have := (Finset.mem_Icc.mp hd).2
      omega
    have hp_le : (splitTwoPow d).1 < n + 1 := by
      have := (splitTwoPow_spec d hd1).2.2
      omega
    simp only [dif_pos hd1, dif_pos hd_lt]
    by_cases hbit : Nat.testBit (P.mult ⟨(splitTwoPow d).1, hp_le⟩) (splitTwoPow d).2 = true
    · have hex : ∃ (hd' : 1 ≤ d) (hp' : (splitTwoPow d).1 < n + 1),
          Nat.testBit (P.mult ⟨(splitTwoPow d).1, hp'⟩) (splitTwoPow d).2 = true :=
        ⟨hd1, hp_le, hbit⟩
      rw [if_pos hbit, if_pos hex]
    · have hnex : ¬ ∃ (hd' : 1 ≤ d) (hp' : (splitTwoPow d).1 < n + 1),
          Nat.testBit (P.mult ⟨(splitTwoPow d).1, hp'⟩) (splitTwoPow d).2 = true := by
        rintro ⟨_, _, h⟩
        exact hbit h
      rw [if_neg hbit, if_neg hnex]
  let S_kj := ((Finset.univ : Finset (Fin (n + 1))) ×ˢ Finset.range (n + 1)).filter
    fun kj => Nat.testBit (P.mult kj.1) kj.2 = true
  have hRHS : n = ∑ kj ∈ S_kj, kj.1.val * 2 ^ kj.2 := by
    have hn : n = ∑ k : Fin (n + 1), k.val * P.mult k := P.sum_eq.symm
    have hbit_expand : ∑ k : Fin (n + 1), k.val * P.mult k =
        ∑ k : Fin (n + 1), ∑ j ∈ Finset.range (n + 1),
          (k.val * 2 ^ j) * (if Nat.testBit (P.mult k) j then 1 else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hm := hlt2n (P.mult k) (P.mult_le k)
      conv_lhs => rw [← binary_bit_sum_eq (n + 1) (P.mult k) hm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    conv_lhs => rw [hn]
    rw [hbit_expand, ← Finset.sum_product', Finset.sum_filter]
    refine Finset.sum_congr rfl fun kj _ => ?_
    by_cases hbit : Nat.testBit (P.mult kj.1) kj.2 = true
    · simp [hbit]
    · simp [hbit]
  rw [hLHS1, hLHS2, hRHS]
  refine Finset.sum_bij (fun d hd =>
      (⟨(splitTwoPow d).1, by
        have hd_icc : d ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hd).1
        have h1 : 1 ≤ d := (Finset.mem_Icc.mp hd_icc).1
        have h2 : d ≤ n := (Finset.mem_Icc.mp hd_icc).2
        have := (splitTwoPow_spec d h1).2.2
        omega⟩, (splitTwoPow d).2)) ?_ ?_ ?_ ?_
  · intro d hd_mem
    rcases Finset.mem_filter.mp hd_mem with ⟨hd_icc, hd1, hp_le, hbit⟩
    have hspec := splitTwoPow_spec d hd1
    have hd_le_n : d ≤ n := (Finset.mem_Icc.mp hd_icc).2
    have hpow_le : 2 ^ (splitTwoPow d).2 ≤ d := by
      calc 2 ^ (splitTwoPow d).2 = 1 * 2 ^ (splitTwoPow d).2 := (one_mul _).symm
        _ ≤ (splitTwoPow d).1 * 2 ^ (splitTwoPow d).2 :=
            Nat.mul_le_mul_right _ hspec.1.pos
        _ = d := hspec.2.1
    have hj_lt : (splitTwoPow d).2 < n + 1 := by
      have hpow_lt : 2 ^ (splitTwoPow d).2 < 2 ^ (n + 1) := by
        have := hlt2n d hd_le_n
        omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
    simp only [S_kj, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
      true_and]
    exact ⟨hj_lt, hbit⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    have h1 := (splitTwoPow_spec d₁ (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1).1).2.1
    have h2 := (splitTwoPow_spec d₂ (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₂).1).1).2.1
    have hf : (splitTwoPow d₁).1 = (splitTwoPow d₂).1 := congrArg (fun x => x.1.val) heq
    have hs : (splitTwoPow d₁).2 = (splitTwoPow d₂).2 :=
      congrArg (fun x : Fin (n + 1) × ℕ => x.2) heq
    rw [← h1, ← h2, hf, hs]
  · intro kj hkj_mem
    rcases Finset.mem_filter.mp hkj_mem with ⟨hkj_prod, hbit⟩
    rcases Finset.mem_product.mp hkj_prod with ⟨_, hj_range⟩
    have hj_lt : kj.2 < n + 1 := Finset.mem_range.mp hj_range
    have hmult_ne : P.mult kj.1 ≠ 0 := by
      intro h0
      rw [h0, Nat.zero_testBit] at hbit
      exact Bool.false_ne_true hbit
    have hk_odd : Odd kj.1.val := hPodd kj.1 hmult_ne
    have h2j_le : 2 ^ kj.2 ≤ P.mult kj.1 :=
      testBit_eq_true_le (hlt2n (P.mult kj.1) (P.mult_le kj.1)) hj_lt hbit
    have hd_ge1 : 1 ≤ kj.1.val * 2 ^ kj.2 :=
      Nat.mul_pos hk_odd.pos (Nat.pow_pos (by norm_num))
    have hd_len : kj.1.val * 2 ^ kj.2 ≤ n := by
      calc kj.1.val * 2 ^ kj.2 ≤ kj.1.val * P.mult kj.1 := Nat.mul_le_mul_left _ h2j_le
        _ ≤ n := partition_mul_mult_le P kj.1
    refine ⟨kj.1.val * 2 ^ kj.2, ?_, ?_⟩
    · have hsp := splitTwoPow_mul_two_pow hk_odd kj.2
      simp only [S_d, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hd_ge1, hd_len⟩, hd_ge1, by rw [hsp]; exact kj.1.isLt, ?_⟩
      have hfin : (⟨(splitTwoPow (kj.1.val * 2 ^ kj.2)).1, by rw [hsp]; exact kj.1.isLt⟩ :
          Fin (n + 1)) = kj.1 := Fin.ext (by simp [hsp])
      rw [hfin, hsp]
      exact hbit
    · have hsp := splitTwoPow_mul_two_pow hk_odd kj.2
      ext
      · simp [hsp]
      · simp [hsp]
  · intro d hd_mem
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd_mem).1).1
    exact (splitTwoPow_spec d hd1).2.1.symm

private lemma oddPartition_fromDist_sum {n : ℕ} (Q : IntPartition n)
    (hQdist : ∀ d : Fin (n + 1), Q.mult d ≤ 1) :
    ∑ k : Fin (n + 1), k.val *
      (if Odd k.val then
        ∑ j ∈ Finset.range (n + 1),
          2 ^ j * (if h : k.val * 2 ^ j < n + 1 then Q.mult ⟨k.val * 2 ^ j, h⟩ else 0)
      else 0) = n := by
  have hlt2n : ∀ m : ℕ, m ≤ n → m < 2 ^ (n + 1) := fun m hm => by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
    omega
  let S_kj := ((Finset.univ : Finset (Fin (n + 1))) ×ˢ Finset.range (n + 1)).filter
    fun kj => Odd kj.1.val ∧ ∃ (h : kj.1.val * 2 ^ kj.2 < n + 1), Q.mult ⟨kj.1.val * 2 ^ kj.2, h⟩ = 1
  have hLHS : ∑ k : Fin (n + 1), k.val *
      (if Odd k.val then
        ∑ j ∈ Finset.range (n + 1),
          2 ^ j * (if h : k.val * 2 ^ j < n + 1 then Q.mult ⟨k.val * 2 ^ j, h⟩ else 0)
      else 0) = ∑ kj ∈ S_kj, kj.1.val * 2 ^ kj.2 := by
    have h1 : ∑ k : Fin (n + 1), k.val *
        (if Odd k.val then
          ∑ j ∈ Finset.range (n + 1),
            2 ^ j * (if h : k.val * 2 ^ j < n + 1 then Q.mult ⟨k.val * 2 ^ j, h⟩ else 0)
        else 0) =
        ∑ k : Fin (n + 1), ∑ j ∈ Finset.range (n + 1),
          if Odd k.val then
            (k.val * 2 ^ j) *
              (if h : k.val * 2 ^ j < n + 1 then Q.mult ⟨k.val * 2 ^ j, h⟩ else 0)
          else 0 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : Odd k.val
      · simp only [hk, ite_true, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      · simp [hk]
    rw [h1, ← Finset.sum_product', Finset.sum_filter]
    refine Finset.sum_congr rfl fun kj _ => ?_
    by_cases hodd : Odd kj.1.val
    · by_cases hlt : kj.1.val * 2 ^ kj.2 < n + 1
      · have hle1 := hQdist ⟨kj.1.val * 2 ^ kj.2, hlt⟩
        have hcases : Q.mult ⟨kj.1.val * 2 ^ kj.2, hlt⟩ = 0 ∨
            Q.mult ⟨kj.1.val * 2 ^ kj.2, hlt⟩ = 1 := by omega
        rcases hcases with h0 | h1v
        · have hnex : ¬ (Odd kj.1.val ∧
              ∃ (h : kj.1.val * 2 ^ kj.2 < n + 1), Q.mult ⟨kj.1.val * 2 ^ kj.2, h⟩ = 1) := by
            rintro ⟨_, _, hq⟩
            omega
          rw [if_pos hodd, dif_pos hlt, h0, mul_zero, if_neg hnex]
        · have hex : Odd kj.1.val ∧
              ∃ (h : kj.1.val * 2 ^ kj.2 < n + 1), Q.mult ⟨kj.1.val * 2 ^ kj.2, h⟩ = 1 :=
            ⟨hodd, hlt, h1v⟩
          rw [if_pos hodd, dif_pos hlt, h1v, mul_one, if_pos hex]
      · have hnex : ¬ (Odd kj.1.val ∧
            ∃ (h : kj.1.val * 2 ^ kj.2 < n + 1), Q.mult ⟨kj.1.val * 2 ^ kj.2, h⟩ = 1) := by
          rintro ⟨_, h, _⟩
          exact hlt h
        rw [if_pos hodd, dif_neg hlt, mul_zero, if_neg hnex]
    · have hnex : ¬ (Odd kj.1.val ∧
          ∃ (h : kj.1.val * 2 ^ kj.2 < n + 1), Q.mult ⟨kj.1.val * 2 ^ kj.2, h⟩ = 1) := by
        rintro ⟨ho, _⟩
        exact hodd ho
      rw [if_neg hodd, if_neg hnex]
  let S_d := (Finset.Icc 1 n).filter fun d => ∃ (hd : d < n + 1), Q.mult ⟨d, hd⟩ = 1
  have hRHS : n = ∑ d ∈ S_d, d := by
    have hn : n = ∑ d : Fin (n + 1), d.val * Q.mult d := Q.sum_eq.symm
    have hrange : ∑ d : Fin (n + 1), d.val * Q.mult d =
        ∑ d ∈ Finset.range (n + 1), if hd : d < n + 1 then d * Q.mult ⟨d, hd⟩ else 0 := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => if hd : d < n + 1 then d * Q.mult ⟨d, hd⟩ else 0) (n + 1)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [dif_pos d.isLt]
    have hIcc : Finset.Icc 1 n = (Finset.range n).image Nat.succ := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨x - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        omega
    conv_lhs => rw [hn, hrange, Finset.sum_range_succ']
    simp only [dif_pos (Nat.succ_pos n), zero_mul, add_zero]
    conv_rhs => rw [Finset.sum_filter, hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha_lt : a + 1 < n + 1 := by
      rw [Finset.mem_range] at ha
      omega
    have hle1 := hQdist ⟨a + 1, ha_lt⟩
    have hcases : Q.mult ⟨a + 1, ha_lt⟩ = 0 ∨ Q.mult ⟨a + 1, ha_lt⟩ = 1 := by omega
    rcases hcases with h0 | h1v
    · have hnex : ¬ ∃ (hd : a + 1 < n + 1), Q.mult ⟨a + 1, hd⟩ = 1 := by
        rintro ⟨_, hq⟩
        omega
      change (if hd : a + 1 < n + 1 then (a + 1) * Q.mult ⟨a + 1, hd⟩ else 0) = _
      rw [dif_pos ha_lt, h0, mul_zero, if_neg hnex]
    · have hex : ∃ (hd : a + 1 < n + 1), Q.mult ⟨a + 1, hd⟩ = 1 := ⟨ha_lt, h1v⟩
      change (if hd : a + 1 < n + 1 then (a + 1) * Q.mult ⟨a + 1, hd⟩ else 0) = _
      rw [dif_pos ha_lt, h1v, mul_one, if_pos hex]
  rw [hLHS]
  conv_rhs => rw [hRHS]
  refine Finset.sum_bij (fun kj _ => kj.1.val * 2 ^ kj.2) ?_ ?_ ?_ ?_
  · intro kj hkj_mem
    rcases Finset.mem_filter.mp hkj_mem with ⟨_, hodd, hlt, hq⟩
    have hge1 : 1 ≤ kj.1.val * 2 ^ kj.2 :=
      Nat.mul_pos hodd.pos (Nat.pow_pos (by norm_num))
    simp only [S_d, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hge1, by omega⟩, hlt, hq⟩
  · intro kj₁ hkj₁ kj₂ hkj₂ heq
    have hodd₁ : Odd kj₁.1.val := (Finset.mem_filter.mp hkj₁).2.1
    have hodd₂ : Odd kj₂.1.val := (Finset.mem_filter.mp hkj₂).2.1
    have hsp := congrArg splitTwoPow heq
    rw [splitTwoPow_mul_two_pow hodd₁ kj₁.2, splitTwoPow_mul_two_pow hodd₂ kj₂.2] at hsp
    ext
    · exact (congrArg (Prod.fst : ℕ × ℕ → ℕ) hsp)
    · exact (congrArg (Prod.snd : ℕ × ℕ → ℕ) hsp)
  · intro d hd_mem
    rcases Finset.mem_filter.mp hd_mem with ⟨hd_icc, hlt_d, hq⟩
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd_icc).1
    have hd_len : d ≤ n := (Finset.mem_Icc.mp hd_icc).2
    have hspec := splitTwoPow_spec d hd1
    have hp1_lt : (splitTwoPow d).1 < n + 1 := by have := hspec.2.2; omega
    have hpow_le : 2 ^ (splitTwoPow d).2 ≤ d := by
      calc 2 ^ (splitTwoPow d).2 = 1 * 2 ^ (splitTwoPow d).2 := (one_mul _).symm
        _ ≤ (splitTwoPow d).1 * 2 ^ (splitTwoPow d).2 := Nat.mul_le_mul_right _ hspec.1.pos
        _ = d := hspec.2.1
    have hp2_lt : (splitTwoPow d).2 < n + 1 := by
      have hpow_lt : 2 ^ (splitTwoPow d).2 < 2 ^ (n + 1) := by
        have := hlt2n d hd_len
        omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
    refine ⟨(⟨(splitTwoPow d).1, hp1_lt⟩, (splitTwoPow d).2), ?_, hspec.2.1⟩
    simp only [S_kj, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, Finset.mem_range,
      true_and]
    refine ⟨hp2_lt, hspec.1, ⟨by rw [hspec.2.1]; exact hlt_d, ?_⟩⟩
    have hfin : (⟨(splitTwoPow d).1 * 2 ^ (splitTwoPow d).2, by rw [hspec.2.1]; exact hlt_d⟩ :
        Fin (n + 1)) = ⟨d, hlt_d⟩ := Fin.ext hspec.2.1
    rw [hfin]
    exact hq
  · intro _ _
    rfl

/-- **Euler's Distinct = Odd Partition Theorem** (Glaisher's binary bijection):
For every `n : ℕ`, the number of partitions of `n` into distinct parts equals the
number of partitions of `n` into odd parts. -/
theorem euler_distinct_eq_odd_partitions (n : ℕ) :
    distinctPartitionCount n = oddPartitionCount n := by
  unfold distinctPartitionCount oddPartitionCount
  let distS := Finset.univ.filter fun P : IntPartition n => ∀ k : Fin (n + 1), P.mult k ≤ 1
  let oddS := Finset.univ.filter fun P : IntPartition n =>
    ∀ k : Fin (n + 1), P.mult k ≠ 0 → Odd k.val
  change distS.card = oddS.card
  symm
  have hlt2n : ∀ m : ℕ, m ≤ n → m < 2 ^ (n + 1) := fun m hm => by
    have h1 : n < 2 ^ n := Nat.lt_two_pow_self
    have h2 : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
    omega
  let toDist : ∀ P ∈ oddS, IntPartition n := fun P hP =>
    { mult := fun d =>
        if hd : 1 ≤ d.val then
          have hp_le : (splitTwoPow d.val).1 < n + 1 := by
            have := (splitTwoPow_spec d.val hd).2.2
            have hd_lt : d.val < n + 1 := d.isLt
            omega
          if Nat.testBit (P.mult ⟨(splitTwoPow d.val).1, hp_le⟩) (splitTwoPow d.val).2 then 1 else 0
        else 0
      mult_zero := by simp
      sum_eq := oddPartition_toDist_sum P (Finset.mem_filter.mp hP).2 }
  let toOdd : ∀ Q ∈ distS, IntPartition n := fun Q hQ =>
    { mult := fun k =>
        if Odd k.val then
          ∑ j ∈ Finset.range (n + 1),
            2 ^ j * (if h : k.val * 2 ^ j < n + 1 then Q.mult ⟨k.val * 2 ^ j, h⟩ else 0)
        else 0
      mult_zero := by simp [Nat.not_odd_zero]
      sum_eq := oddPartition_fromDist_sum Q (Finset.mem_filter.mp hQ).2 }
  refine Finset.card_bij toDist ?_ ?_ ?_
  · intro P hP
    simp only [distS, Finset.mem_filter, Finset.mem_univ, true_and]
    intro d
    dsimp only [toDist]
    split_ifs <;> decide
  · intro P₁ hP₁ P₂ hP₂ heq
    have hP₁odd := (Finset.mem_filter.mp hP₁).2
    have hP₂odd := (Finset.mem_filter.mp hP₂).2
    ext k
    by_cases hk_odd : Odd k.val
    · have hk1 : 1 ≤ k.val := hk_odd.pos
      have hm₁ := hlt2n (P₁.mult k) (P₁.mult_le k)
      have hm₂ := hlt2n (P₂.mult k) (P₂.mult_le k)
      rw [← binary_bit_sum_eq (n + 1) (P₁.mult k) hm₁,
          ← binary_bit_sum_eq (n + 1) (P₂.mult k) hm₂]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_lt : j < n + 1 := Finset.mem_range.mp hj
      have hbit_eq : Nat.testBit (P₁.mult k) j = Nat.testBit (P₂.mult k) j := by
        by_cases h1 : Nat.testBit (P₁.mult k) j = true
        · have h2j : 2 ^ j ≤ P₁.mult k := testBit_eq_true_le hm₁ hj_lt h1
          have hd_le : k.val * 2 ^ j ≤ n := by
            calc k.val * 2 ^ j ≤ k.val * P₁.mult k := Nat.mul_le_mul_left _ h2j
              _ ≤ n := partition_mul_mult_le P₁ k
          let d : Fin (n + 1) := ⟨k.val * 2 ^ j, by omega⟩
          have hd1 : 1 ≤ d.val := Nat.mul_pos hk1 (Nat.pow_pos (by norm_num))
          have hd_eq := congrArg (fun R : IntPartition n => R.mult d) heq
          dsimp only [toDist] at hd_eq
          have hsp := splitTwoPow_mul_two_pow hk_odd j
          have hfin : ∀ hp_le, (⟨(splitTwoPow d.val).1, hp_le⟩ : Fin (n + 1)) = k := fun hp_le =>
            Fin.ext (by change (splitTwoPow (k.val * 2 ^ j)).1 = k.val; rw [hsp])
          simp only [dif_pos hd1] at hd_eq
          rw [hfin] at hd_eq
          have hsnd : (splitTwoPow d.val).2 = j := by
            change (splitTwoPow (k.val * 2 ^ j)).2 = j; rw [hsp]
          rw [hsnd, h1, if_pos rfl] at hd_eq
          by_cases h2 : Nat.testBit (P₂.mult k) j = true
          · rw [h1, h2]
          · rw [if_neg h2] at hd_eq
            omega
        · by_cases h2 : Nat.testBit (P₂.mult k) j = true
          · have h2j : 2 ^ j ≤ P₂.mult k := testBit_eq_true_le hm₂ hj_lt h2
            have hd_le : k.val * 2 ^ j ≤ n := by
              calc k.val * 2 ^ j ≤ k.val * P₂.mult k := Nat.mul_le_mul_left _ h2j
                _ ≤ n := partition_mul_mult_le P₂ k
            let d : Fin (n + 1) := ⟨k.val * 2 ^ j, by omega⟩
            have hd1 : 1 ≤ d.val := Nat.mul_pos hk1 (Nat.pow_pos (by norm_num))
            have hd_eq := congrArg (fun R : IntPartition n => R.mult d) heq
            dsimp only [toDist] at hd_eq
            have hsp := splitTwoPow_mul_two_pow hk_odd j
            have hfin : ∀ hp_le, (⟨(splitTwoPow d.val).1, hp_le⟩ : Fin (n + 1)) = k := fun hp_le =>
              Fin.ext (by change (splitTwoPow (k.val * 2 ^ j)).1 = k.val; rw [hsp])
            simp only [dif_pos hd1] at hd_eq
            rw [hfin] at hd_eq
            have hsnd : (splitTwoPow d.val).2 = j := by
              change (splitTwoPow (k.val * 2 ^ j)).2 = j; rw [hsp]
            rw [hsnd, if_neg h1, if_pos h2] at hd_eq
            omega
          · cases hb1 : Nat.testBit (P₁.mult k) j <;> cases hb2 : Nat.testBit (P₂.mult k) j <;>
              simp_all
      rw [hbit_eq]
    · have hp1 : P₁.mult k = 0 := by by_contra hne; exact hk_odd (hP₁odd k hne)
      have hp2 : P₂.mult k = 0 := by by_contra hne; exact hk_odd (hP₂odd k hne)
      rw [hp1, hp2]
  · intro Q hQ
    have hQdist := (Finset.mem_filter.mp hQ).2
    refine ⟨toOdd Q hQ, ?_, ?_⟩
    · simp only [oddS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k hk
      dsimp only [toOdd] at hk
      by_contra hnot
      simp [hnot] at hk
    · ext d
      dsimp only [toDist, toOdd]
      by_cases hd0 : d.val = 0
      · have hd_fin : d = 0 := Fin.ext hd0
        rw [hd_fin, Q.mult_zero]
        simp
      · have hd1 : 1 ≤ d.val := Nat.pos_of_ne_zero hd0
        have hspec := splitTwoPow_spec d.val hd1
        have hp2_lt : (splitTwoPow d.val).2 < n + 1 := by
          have hpow_le : 2 ^ (splitTwoPow d.val).2 ≤ d.val := by
            calc 2 ^ (splitTwoPow d.val).2 = 1 * 2 ^ (splitTwoPow d.val).2 := (one_mul _).symm
              _ ≤ (splitTwoPow d.val).1 * 2 ^ (splitTwoPow d.val).2 :=
                  Nat.mul_le_mul_right _ hspec.1.pos
              _ = d.val := hspec.2.1
          have hpow_lt : 2 ^ (splitTwoPow d.val).2 < 2 ^ (n + 1) := by
            have := hlt2n d.val (by omega)
            omega
          exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hpow_lt
        simp only [dif_pos hd1, hspec.1, ite_true]
        have hf_le : ∀ j,
            (if h : (splitTwoPow d.val).1 * 2 ^ j < n + 1 then
              Q.mult ⟨(splitTwoPow d.val).1 * 2 ^ j, h⟩ else 0) ≤ 1 := fun j => by
          split_ifs with h
          · exact hQdist _
          · exact Nat.zero_le 1
        have hcomm :
            ∑ j ∈ Finset.range (n + 1),
              2 ^ j * (if h : (splitTwoPow d.val).1 * 2 ^ j < n + 1 then
                Q.mult ⟨(splitTwoPow d.val).1 * 2 ^ j, h⟩ else 0) =
            ∑ j ∈ Finset.range (n + 1),
              (if h : (splitTwoPow d.val).1 * 2 ^ j < n + 1 then
                Q.mult ⟨(splitTwoPow d.val).1 * 2 ^ j, h⟩ else 0) * 2 ^ j :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [hcomm, testBit_binary_sum (n + 1) _ hf_le (splitTwoPow d.val).2, if_pos hp2_lt]
        have hd_lt : (splitTwoPow d.val).1 * 2 ^ (splitTwoPow d.val).2 < n + 1 := by
          rw [hspec.2.1]; exact d.isLt
        rw [dif_pos hd_lt]
        have hfin : (⟨(splitTwoPow d.val).1 * 2 ^ (splitTwoPow d.val).2, hd_lt⟩ : Fin (n + 1)) = d :=
          Fin.ext hspec.2.1
        rw [hfin]
        have hq1 := hQdist d
        rcases (by omega : Q.mult d = 0 ∨ Q.mult d = 1) with h0 | h1
        · simp [h0]
        · simp [h1]

/-! ### Part 2B: Euler's Pentagonal Number Theorem & Partition Recurrence -/

/-- First generalized pentagonal number: `k * (3 * k - 1) / 2` (index `+k`). -/
def pentagonalNum1 (k : ℕ) : ℕ :=
  k * (3 * k - 1) / 2

/-- Second generalized pentagonal number: `k * (3 * k + 1) / 2` (index `-k`). -/
def pentagonalNum2 (k : ℕ) : ℕ :=
  k * (3 * k + 1) / 2

lemma two_mul_pentagonalNum1 (k : ℕ) : 2 * pentagonalNum1 k = k * (3 * k - 1) := by
  unfold pentagonalNum1
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have : 2 ∣ (m + m) * (3 * (m + m) - 1) := ⟨m * (3 * (m + m) - 1), by ring⟩
    omega
  · have h3 : 2 ∣ 3 * (2 * m + 1) - 1 := by
      have : 3 * (2 * m + 1) - 1 = 2 * (3 * m + 1) := by omega
      exact ⟨3 * m + 1, this⟩
    have : 2 ∣ (2 * m + 1) * (3 * (2 * m + 1) - 1) := dvd_mul_of_dvd_right h3 _
    omega

lemma two_mul_pentagonalNum2 (k : ℕ) : 2 * pentagonalNum2 k = k * (3 * k + 1) := by
  unfold pentagonalNum2
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have : 2 ∣ (m + m) * (3 * (m + m) + 1) := ⟨m * (3 * (m + m) + 1), by ring⟩
    omega
  · have : 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) := by omega
    have h3 : 2 ∣ 3 * (2 * m + 1) + 1 := ⟨3 * m + 2, this⟩
    have : 2 ∣ (2 * m + 1) * (3 * (2 * m + 1) + 1) := dvd_mul_of_dvd_right h3 _
    omega

lemma pentagonalNum1_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ pentagonalNum1 k := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := two_mul_pentagonalNum1 (k' + 1)
  have hsub : 3 * (k' + 1) - 1 = 3 * k' + 2 := by omega
  nlinarith

lemma pentagonalNum_strict {k : ℕ} (hk : 1 ≤ k) :
    pentagonalNum1 k < pentagonalNum2 k ∧ pentagonalNum2 k < pentagonalNum1 (k + 1) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h1 := two_mul_pentagonalNum1 (k' + 1)
  have h2 := two_mul_pentagonalNum2 (k' + 1)
  have h3 := two_mul_pentagonalNum1 (k' + 1 + 1)
  have hs1 : 3 * (k' + 1) - 1 = 3 * k' + 2 := by omega
  have hs3 : 3 * (k' + 1 + 1) - 1 = 3 * k' + 5 := by omega
  constructor <;> nlinarith

lemma pentagonalNum1_le_of_le {k : ℕ} (hk : 1 ≤ k) : k ≤ pentagonalNum1 k := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := two_mul_pentagonalNum1 (k' + 1)
  have hs : 3 * (k' + 1) - 1 = 3 * k' + 2 := by omega
  rw [hs] at h
  nlinarith

lemma pentagonalNum2_le_of_le {k : ℕ} (hk : 1 ≤ k) : k ≤ pentagonalNum2 k := by
  have h := two_mul_pentagonalNum2 k
  nlinarith

lemma pentagonalNum1_injOn : Set.InjOn pentagonalNum1 {k : ℕ | 1 ≤ k} := by
  intro a ha b hb hab
  have ha0 : a ≠ 0 := Nat.ne_of_gt (show 1 ≤ a from ha)
  have hb0 : b ≠ 0 := Nat.ne_of_gt (show 1 ≤ b from hb)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha0
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
  have ha1 := two_mul_pentagonalNum1 (a' + 1)
  have hb1 := two_mul_pentagonalNum1 (b' + 1)
  have hsa : 3 * (a' + 1) - 1 = 3 * a' + 2 := by omega
  have hsb : 3 * (b' + 1) - 1 = 3 * b' + 2 := by omega
  rw [hsa] at ha1
  rw [hsb] at hb1
  rcases lt_trichotomy a' b' with hlt | rfl | hgt
  · exfalso; nlinarith
  · rfl
  · exfalso; nlinarith

lemma pentagonalNum2_injOn : Set.InjOn pentagonalNum2 {k : ℕ | 1 ≤ k} := by
  intro a ha b hb hab
  have ha2 := two_mul_pentagonalNum2 a
  have hb2 := two_mul_pentagonalNum2 b
  have heq : a * (3 * a + 1) = b * (3 * b + 1) := by omega
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · have : a * (3 * a + 1) < b * (3 * b + 1) := by
      have ha' : 1 ≤ a := ha
      nlinarith
    omega
  · rfl
  · have : b * (3 * b + 1) < a * (3 * a + 1) := by
      have hb' : 1 ≤ b := hb
      nlinarith
    omega

lemma pentagonalNum1_ne_pentagonalNum2 {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    pentagonalNum1 a ≠ pentagonalNum2 b := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have ha1 := two_mul_pentagonalNum1 (a' + 1)
  have hb2 := two_mul_pentagonalNum2 (b' + 1)
  have hsa : 3 * (a' + 1) - 1 = 3 * a' + 2 := by omega
  intro heq
  by_cases hab : a' ≤ b'
  · nlinarith
  · have hba : b' + 1 ≤ a' := by omega
    nlinarith

/-- Coefficient `[X^n] ∏_{k ≥ 1} (1 - X^k)` from Euler's Pentagonal Number Theorem:
`1` at `n = 0`, `(-1)^k` at `n = k(3k-1)/2` or `k(3k+1)/2` (`k ≥ 1`), and `0` otherwise. -/
def pentagonalCoeff (n : ℕ) : ℤ :=
  if n = 0 then 1
  else
    (∑ k ∈ Finset.Icc 1 n, if pentagonalNum1 k = n then (-1 : ℤ) ^ k else 0) +
    (∑ k ∈ Finset.Icc 1 n, if pentagonalNum2 k = n then (-1 : ℤ) ^ k else 0)

@[simp]
lemma pentagonalCoeff_zero : pentagonalCoeff 0 = 1 := by
  simp [pentagonalCoeff]

lemma pentagonalCoeff_num1 {k : ℕ} (hk : 1 ≤ k) :
    pentagonalCoeff (pentagonalNum1 k) = (-1 : ℤ) ^ k := by
  have hpos : 1 ≤ pentagonalNum1 k := pentagonalNum1_pos hk
  have hne0 : pentagonalNum1 k ≠ 0 := by omega
  have hkle : k ≤ pentagonalNum1 k := pentagonalNum1_le_of_le hk
  unfold pentagonalCoeff
  rw [if_neg hne0]
  have hs1 : ∑ j ∈ Finset.Icc 1 (pentagonalNum1 k),
      (if pentagonalNum1 j = pentagonalNum1 k then (-1 : ℤ) ^ j else 0) = (-1 : ℤ) ^ k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [if_neg (fun heq => hjk (pentagonalNum1_injOn hj1 hk heq))]
    · intro hk_nmem
      exfalso
      exact hk_nmem (Finset.mem_Icc.mpr ⟨hk, hkle⟩)
  have hs2 : ∑ j ∈ Finset.Icc 1 (pentagonalNum1 k),
      (if pentagonalNum2 j = pentagonalNum1 k then (-1 : ℤ) ^ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [if_neg (fun heq => pentagonalNum1_ne_pentagonalNum2 hk hj1 heq.symm)]
  rw [hs1, hs2, add_zero]

lemma pentagonalCoeff_num2 {k : ℕ} (hk : 1 ≤ k) :
    pentagonalCoeff (pentagonalNum2 k) = (-1 : ℤ) ^ k := by
  have hpos : 1 ≤ pentagonalNum2 k := le_trans hk (pentagonalNum2_le_of_le hk)
  have hne0 : pentagonalNum2 k ≠ 0 := by omega
  have hkle : k ≤ pentagonalNum2 k := pentagonalNum2_le_of_le hk
  unfold pentagonalCoeff
  rw [if_neg hne0]
  have hs1 : ∑ j ∈ Finset.Icc 1 (pentagonalNum2 k),
      (if pentagonalNum1 j = pentagonalNum2 k then (-1 : ℤ) ^ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [if_neg (fun heq => pentagonalNum1_ne_pentagonalNum2 hj1 hk heq)]
  have hs2 : ∑ j ∈ Finset.Icc 1 (pentagonalNum2 k),
      (if pentagonalNum2 j = pentagonalNum2 k then (-1 : ℤ) ^ j else 0) = (-1 : ℤ) ^ k := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [if_neg (fun heq => hjk (pentagonalNum2_injOn hj1 hk heq))]
    · intro hk_nmem
      exfalso
      exact hk_nmem (Finset.mem_Icc.mpr ⟨hk, hkle⟩)
  rw [hs1, hs2, zero_add]

lemma pentagonalCoeff_eq_zero {n : ℕ} (hn0 : n ≠ 0)
    (h1 : ∀ k, 1 ≤ k → pentagonalNum1 k ≠ n)
    (h2 : ∀ k, 1 ≤ k → pentagonalNum2 k ≠ n) :
    pentagonalCoeff n = 0 := by
  unfold pentagonalCoeff
  rw [if_neg hn0]
  have hs1 : ∑ k ∈ Finset.Icc 1 n, (if pentagonalNum1 k = n then (-1 : ℤ) ^ k else 0) = 0 :=
    Finset.sum_eq_zero fun k hk => if_neg (h1 k (Finset.mem_Icc.mp hk).1)
  have hs2 : ∑ k ∈ Finset.Icc 1 n, (if pentagonalNum2 k = n then (-1 : ℤ) ^ k else 0) = 0 :=
    Finset.sum_eq_zero fun k hk => if_neg (h2 k (Finset.mem_Icc.mp hk).1)
  rw [hs1, hs2, add_zero]

/-- Euler pentagonal formal power series `∏_{k ≥ 1} (1 - X^k)` over `ℤ`. -/
noncomputable def pentagonalPS : PowerSeries ℤ :=
  PowerSeries.mk pentagonalCoeff

/-- Partition generating function `∑_{n ≥ 0} p(n) X^n` over `ℤ`. -/
noncomputable def partitionGF : PowerSeries ℤ :=
  PowerSeries.mk fun n => (partitionCount n : ℤ)

private def runDown (S : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | a + 1 => if a + 1 ∈ S then runDown S a + 1 else 0

private lemma runDown_le (S : Finset ℕ) (a : ℕ) : runDown S a ≤ a := by
  induction a with
  | zero => simp [runDown]
  | succ a ih =>
    unfold runDown
    split_ifs <;> omega

private lemma runDown_mem {S : Finset ℕ} {a j : ℕ} (hj : j < runDown S a) : a - j ∈ S := by
  induction a generalizing j with
  | zero => simp [runDown] at hj
  | succ a ih =>
    unfold runDown at hj
    split_ifs at hj with ha
    · cases j with
      | zero => simpa using ha
      | succ j =>
        have hj' : j < runDown S a := by omega
        have hmem := ih hj'
        have : a + 1 - (j + 1) = a - j := by omega
        rwa [this]
    · omega

private lemma runDown_not_mem {S : Finset ℕ} (h0 : 0 ∉ S) (a : ℕ) : a - runDown S a ∉ S := by
  induction a with
  | zero => simpa [runDown] using h0
  | succ a ih =>
    unfold runDown
    split_ifs with ha
    · have : a + 1 - (runDown S a + 1) = a - runDown S a := by omega
      rw [this]
      exact ih
    · simpa using ha

private lemma runDown_ge_of_forall {S : Finset ℕ} {a k : ℕ} (hk : k ≤ a)
    (hmem : ∀ j < k, a - j ∈ S) : k ≤ runDown S a := by
  induction a generalizing k with
  | zero => omega
  | succ a ih =>
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      have ha1 : a + 1 ∈ S := by simpa using hmem 0 (Nat.succ_pos k)
      unfold runDown
      rw [if_pos ha1]
      have hsub : k ≤ runDown S a := ih (by omega) fun j hj => by
        have := hmem (j + 1) (by omega)
        have heq : a + 1 - (j + 1) = a - j := by omega
        rwa [← heq]
      omega

private lemma runDown_le_of_not_mem {S : Finset ℕ} {a k : ℕ} (hnot : a - k ∉ S) :
    runDown S a ≤ k := by
  by_contra hgt
  have hlt : k < runDown S a := by omega
  exact hnot (runDown_mem hlt)

private lemma sum_Icc_eq_pentagonalNum1 (k : ℕ) (hk : 1 ≤ k) :
    (Finset.Icc k (2 * k - 1)).sum id = pentagonalNum1 k := by
  have h2 := two_mul_pentagonalNum1 k
  have hsum : 2 * (Finset.Icc k (2 * k - 1)).sum id = k * (3 * k - 1) := by
    have hrev : (Finset.Icc k (2 * k - 1)).sum (fun x => k + (2 * k - 1) - x) =
        (Finset.Icc k (2 * k - 1)).sum id := by
      refine Finset.sum_bij (fun x _ => k + (2 * k - 1) - x) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        rcases Finset.mem_Icc.mp hx₁ with ⟨_, hhi₁⟩
        rcases Finset.mem_Icc.mp hx₂ with ⟨_, hhi₂⟩
        omega
      · intro y hy
        rcases Finset.mem_Icc.mp hy with ⟨hlo, hhi⟩
        exact ⟨k + (2 * k - 1) - y, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro _ _; rfl
    have hadd : (Finset.Icc k (2 * k - 1)).sum id +
        (Finset.Icc k (2 * k - 1)).sum (fun x => k + (2 * k - 1) - x) =
        ∑ _x ∈ Finset.Icc k (2 * k - 1), (3 * k - 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
      simp only [id_eq]
      omega
    rw [hrev] at hadd
    simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at hadd
    have hlen : 2 * k - 1 + 1 - k = k := by omega
    rw [hlen] at hadd
    omega
  omega

private lemma sum_Icc_eq_pentagonalNum2 (k : ℕ) (hk : 1 ≤ k) :
    (Finset.Icc (k + 1) (2 * k)).sum id = pentagonalNum2 k := by
  have h2 := two_mul_pentagonalNum2 k
  have hsum : 2 * (Finset.Icc (k + 1) (2 * k)).sum id = k * (3 * k + 1) := by
    have hrev : (Finset.Icc (k + 1) (2 * k)).sum (fun x => (k + 1) + 2 * k - x) =
        (Finset.Icc (k + 1) (2 * k)).sum id := by
      refine Finset.sum_bij (fun x _ => (k + 1) + 2 * k - x) ?_ ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro x₁ hx₁ x₂ hx₂ heq
        rcases Finset.mem_Icc.mp hx₁ with ⟨_, hhi₁⟩
        rcases Finset.mem_Icc.mp hx₂ with ⟨_, hhi₂⟩
        omega
      · intro y hy
        rcases Finset.mem_Icc.mp hy with ⟨hlo, hhi⟩
        exact ⟨(k + 1) + 2 * k - y, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro _ _; rfl
    have hadd : (Finset.Icc (k + 1) (2 * k)).sum id +
        (Finset.Icc (k + 1) (2 * k)).sum (fun x => (k + 1) + 2 * k - x) =
        ∑ _x ∈ Finset.Icc (k + 1) (2 * k), (3 * k + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
      simp only [id_eq]
      omega
    rw [hrev] at hadd
    simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at hadd
    have hlen : 2 * k + 1 - (k + 1) = k := by omega
    rw [hlen] at hadd
    omega
  omega

private lemma prod_X_pow_sum {R : Type*} [CommRing R] (S : Finset ℕ) (x : R) :
    ∏ k ∈ S, x ^ k = x ^ (S.sum id) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, id_eq, pow_add]

private lemma prod_one_sub_X_pow_coeff (N n : ℕ) :
    PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) =
      ∑ S ∈ (Finset.Icc 1 N).powerset.filter (fun S => S.sum id = n), (-1 : ℤ) ^ S.card := by
  have hprod : (∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) =
      ∑ S ∈ (Finset.Icc 1 N).powerset,
        (-1 : PowerSeries ℤ) ^ S.card * (PowerSeries.X : PowerSeries ℤ) ^ (S.sum id) := by
    have heq : (∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) =
        ∏ k ∈ Finset.Icc 1 N, (1 + (-((PowerSeries.X : PowerSeries ℤ) ^ k))) := by
      refine Finset.prod_congr rfl fun k _ => by ring
    rw [heq, Finset.prod_one_add]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hneg : ∀ k : ℕ, -((PowerSeries.X : PowerSeries ℤ) ^ k) =
        (-1 : PowerSeries ℤ) * (PowerSeries.X : PowerSeries ℤ) ^ k := fun k => by ring
    simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, prod_X_pow_sum]
  rw [hprod, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hneg1 : (-1 : PowerSeries ℤ) ^ S.card = PowerSeries.C ((-1 : ℤ) ^ S.card) := by simp
  rw [hneg1, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  by_cases hsum : S.sum id = n
  · have hsum' : n = S.sum id := hsum.symm
    rw [if_pos hsum', if_pos hsum]
    simp
  · have hsum' : n ≠ S.sum id := fun h => hsum h.symm
    rw [if_neg hsum', if_neg hsum]
    simp

private lemma runDown_pos_of_mem {S : Finset ℕ} {M : ℕ} (hM1 : 1 ≤ M) (hM : M ∈ S) :
    1 ≤ runDown S M := by
  cases M with
  | zero => omega
  | succ M' =>
    unfold runDown
    rw [if_pos hM]
    omega

private lemma franklin_fixed_iff {N n : ℕ} {S : Finset ℕ}
    (hS_sub : S ⊆ Finset.Icc 1 N) (_hS_sum : S.sum id = n) (hSne : S.Nonempty) :
    let m := S.min' hSne
    let M := S.max' hSne
    let s := runDown S M
    (¬ (m ≤ s ∧ 2 * m ≤ M) ∧ ¬ (s < m ∧ 2 * s < M)) ↔
      ((m = s ∧ M = 2 * s - 1 ∧ S = Finset.Icc s (2 * s - 1)) ∨
       (m = s + 1 ∧ M = 2 * s ∧ S = Finset.Icc (s + 1) (2 * s))) := by
  intro m M s
  have hm_mem : m ∈ S := Finset.min'_mem S hSne
  have hM_mem : M ∈ S := Finset.max'_mem S hSne
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hS_sub hm_mem)).1
  have hM1 : 1 ≤ M := (Finset.mem_Icc.mp (hS_sub hM_mem)).1
  have h0nmem : 0 ∉ S := fun h0 => by linarith [(Finset.mem_Icc.mp (hS_sub h0)).1]
  have hs_pos : 1 ≤ s := runDown_pos_of_mem hM1 hM_mem
  have hs_le_M : s ≤ M := runDown_le S M
  have hbot_mem : M - (s - 1) ∈ S := runDown_mem (by omega : s - 1 < s)
  have hm_le_bot : m ≤ M - (s - 1) := Finset.min'_le S _ hbot_mem
  have hms : m + s ≤ M + 1 := by omega
  constructor
  · intro ⟨hA, hB⟩
    by_cases hle : m ≤ s
    · have hM_lt : M < 2 * m := by omega
      have hmeq : m = s := by omega
      have hMeq : M = 2 * s - 1 := by omega
      refine Or.inl ⟨hmeq, hMeq, ?_⟩
      ext x
      constructor
      · intro hx
        have hlo : s ≤ x := hmeq ▸ Finset.min'_le S x hx
        have hhi : x ≤ 2 * s - 1 := hMeq ▸ Finset.le_max' S x hx
        exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      · intro hx
        rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
        have hj : M - x < s := by omega
        have hxmem := runDown_mem hj
        have heq : M - (M - x) = x := by omega
        rwa [heq] at hxmem
    · have hlt : s < m := by omega
      have hM_le : M ≤ 2 * s := by omega
      have hmeq : m = s + 1 := by omega
      have hMeq : M = 2 * s := by omega
      refine Or.inr ⟨hmeq, hMeq, ?_⟩
      ext x
      constructor
      · intro hx
        have hlo : s + 1 ≤ x := hmeq ▸ Finset.min'_le S x hx
        have hhi : x ≤ 2 * s := hMeq ▸ Finset.le_max' S x hx
        exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
      · intro hx
        rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
        have hj : M - x < s := by omega
        have hxmem := runDown_mem hj
        have heq : M - (M - x) = x := by omega
        rwa [heq] at hxmem
  · rintro (⟨hmeq, hMeq, _⟩ | ⟨hmeq, hMeq, _⟩) <;> constructor <;> omega

/-- **Euler's Pentagonal Number Theorem** (explicit finite-product truncation):
For all `n ≤ N`, `[X^n] ∏_{k=1}^N (1 - X^k) = pentagonalCoeff n`. -/
theorem euler_pentagonal_prod_coeff (n N : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n (∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) =
      pentagonalCoeff n := by
  rw [prod_one_sub_X_pow_coeff]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [pentagonalCoeff_zero]
    have hflt : (Finset.Icc 1 N).powerset.filter (fun S => S.sum id = 0) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hsub, hsum⟩
        by_contra hne
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hx1 : 1 ≤ x := (Finset.mem_Icc.mp (hsub hx)).1
        have hle : x ≤ S.sum id := Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hx
        omega
      · rintro rfl
        exact ⟨Finset.empty_subset _, by simp⟩
    rw [hflt]
    simp
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  let A := (Finset.Icc 1 N).powerset.filter (fun S => S.sum id = n)
  let isFixed : Finset ℕ → Prop := fun S =>
    ∃ h : S.Nonempty,
      let m := S.min' h
      let M := S.max' h
      let s := runDown S M
      ¬ (m ≤ s ∧ 2 * m ≤ M) ∧ ¬ (s < m ∧ 2 * s < M)
  classical
  let A_fixed := A.filter isFixed
  let A_moved := A.filter (fun S => ¬ isFixed S)
  have hsplit : ∑ S ∈ A, (-1 : ℤ) ^ S.card =
      (∑ S ∈ A_fixed, (-1 : ℤ) ^ S.card) + (∑ S ∈ A_moved, (-1 : ℤ) ^ S.card) := by
    rw [← Finset.sum_filter_add_sum_filter_not A isFixed]
  change ∑ S ∈ A, (-1 : ℤ) ^ S.card = pentagonalCoeff n
  rw [hsplit]
  have hmoved_zero : ∑ S ∈ A_moved, (-1 : ℤ) ^ S.card = 0 := by
    let franklin : ∀ S ∈ A_moved, Finset ℕ := fun S hS =>
      have hSne : S.Nonempty := by
        by_contra hne
        have hsemp : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hsum : S.sum id = n := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
        simp [hsemp] at hsum
        omega
      let m := S.min' hSne
      let M := S.max' hSne
      let s := runDown S M
      if hA : m ≤ s ∧ 2 * m ≤ M then
        insert (M + 1) ((S.erase m).erase (M - m + 1))
      else
        insert s (insert (M - s) (S.erase M))
    have hfr_irrel : ∀ {T₁ T₂} (ht₁ : T₁ ∈ A_moved) (ht₂ : T₂ ∈ A_moved),
        T₁ = T₂ → franklin T₁ ht₁ = franklin T₂ ht₂ := by
      rintro T _ ht₁ ht₂ rfl; rfl
    have hprop : ∀ S (hS : S ∈ A_moved),
        let S' := franklin S hS
        S' ∈ A_moved ∧
          ((-1 : ℤ) ^ S.card + (-1 : ℤ) ^ S'.card = 0) ∧
          (∃ hS' : S' ∈ A_moved, franklin S' hS' = S) := by
      intro S hS
      have hSA : S ∈ A := (Finset.mem_filter.mp hS).1
      have hS_not_fix : ¬ isFixed S := (Finset.mem_filter.mp hS).2
      have hS_sub : S ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
      have hS_sum : S.sum id = n := (Finset.mem_filter.mp hSA).2
      have hsum_raw : ∑ x ∈ S, x = n := hS_sum
      have hSne : S.Nonempty := by
        by_contra hne
        have hsemp : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hsemp] at hS_sum
        omega
      let m := S.min' hSne
      let M := S.max' hSne
      let s := runDown S M
      have hm_mem : m ∈ S := Finset.min'_mem S hSne
      have hM_mem : M ∈ S := Finset.max'_mem S hSne
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (hS_sub hm_mem)).1
      have hM_le_N : M ≤ N := (Finset.mem_Icc.mp (hS_sub hM_mem)).2
      have h0nmem : 0 ∉ S := fun h0 => by linarith [(Finset.mem_Icc.mp (hS_sub h0)).1]
      have hs_pos : 1 ≤ s :=
        runDown_pos_of_mem (Finset.mem_Icc.mp (hS_sub hM_mem)).1 hM_mem
      have hs_le_M : s ≤ M := runDown_le S M
      have hbot_mem : M - (s - 1) ∈ S := runDown_mem (by omega : s - 1 < s)
      have hm_le_bot : m ≤ M - (s - 1) := Finset.min'_le S _ hbot_mem
      by_cases hA : m ≤ s ∧ 2 * m ≤ M
      · have hM_lt_n : M + 1 ≤ n := by
          have hm_ne_M : m ≠ M := by omega
          have hpair : {m, M} ⊆ S := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption
          have hsum_le : ({m, M} : Finset ℕ).sum id ≤ S.sum id :=
            Finset.sum_le_sum_of_subset_of_nonneg hpair (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hm_ne_M] at hsum_le
          simp only [id_eq] at hsum_le
          rw [hsum_raw] at hsum_le
          omega
        let S' := insert (M + 1) ((S.erase m).erase (M - m + 1))
        have hS'_def : franklin S hS = S' := by
          dsimp only [franklin]
          rw [dif_pos hA]
        have hmid_mem : M - m + 1 ∈ S := by
          have hj : m - 1 < s := by omega
          have hmem := runDown_mem hj
          have heq : M - (m - 1) = M - m + 1 := by omega
          rwa [heq] at hmem
        have hm_ne_mid : m ≠ M - m + 1 := by omega
        have hMp1_nmem : M + 1 ∉ (S.erase m).erase (M - m + 1) := by
          intro hmem
          have hmemS : M + 1 ∈ S := Finset.erase_subset _ _ (Finset.erase_subset _ _ hmem)
          have := Finset.le_max' S (M + 1) hmemS
          omega
        have hmid_mem_er : M - m + 1 ∈ S.erase m :=
          Finset.mem_erase.mpr ⟨hm_ne_mid.symm, hmid_mem⟩
        have hS'_card : S'.card = S.card - 1 := by
          have hc1 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hm_mem
          have hc2 : ((S.erase m).erase (M - m + 1)).card = (S.erase m).card - 1 :=
            Finset.card_erase_of_mem hmid_mem_er
          have hS2 : 2 ≤ S.card := by
            have : ({m, M - m + 1} : Finset ℕ) ⊆ S := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            calc 2 = ({m, M - m + 1} : Finset ℕ).card := (Finset.card_pair hm_ne_mid).symm
              _ ≤ S.card := Finset.card_le_card this
          rw [Finset.card_insert_of_notMem hMp1_nmem, hc2, hc1]
          omega
        have hS'_pos : 1 ≤ S.card := Finset.card_pos.mpr hSne
        have hparity : (-1 : ℤ) ^ S.card + (-1 : ℤ) ^ S'.card = 0 := by
          rw [hS'_card]
          obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S.card ≠ 0)
          rw [hc]
          simp [pow_succ]
        have hS'_sub : S' ⊆ Finset.Icc 1 N := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx_er
          · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          · exact hS_sub (Finset.erase_subset _ _ (Finset.erase_subset _ _ hx_er))
        have hS'_sum : S'.sum id = n := by
          have hs1 := Finset.sum_insert hMp1_nmem (f := id)
          have hs2 := Finset.add_sum_erase (S.erase m) id hmid_mem_er
          have hs3 := Finset.add_sum_erase S id hm_mem
          change S'.sum id = _ at hs1
          simp only [id_eq] at hs1 hs2 hs3
          have h1 : S'.sum id = (M + 1) + ∑ x ∈ (S.erase m).erase (M - m + 1), x := hs1
          have h2 : (M - m + 1) + ∑ x ∈ (S.erase m).erase (M - m + 1), x = ∑ x ∈ S.erase m, x := hs2
          have h3 : m + ∑ x ∈ S.erase m, x = ∑ x ∈ S, x := hs3
          omega
        have hS'_ne : S'.Nonempty := ⟨M + 1, Finset.mem_insert_self _ _⟩
        have hM' : S'.max' hS'_ne = M + 1 := by
          apply le_antisymm
          · refine Finset.max'_le S' _ _ fun x hx => ?_
            rcases Finset.mem_insert.mp hx with rfl | hx_er
            · exact le_rfl
            · have := Finset.le_max' S x (Finset.erase_subset _ _ (Finset.erase_subset _ _ hx_er))
              omega
          · exact Finset.le_max' S' _ (Finset.mem_insert_self _ _)
        have hm'_gt : m < S'.min' hS'_ne := by
          by_contra hle
          have hmem := Finset.min'_mem S' hS'_ne
          rcases Finset.mem_insert.mp hmem with hbad | hx_er
          · omega
          · have hx_er1 := Finset.mem_of_mem_erase hx_er
            have hx_ne : S'.min' hS'_ne ≠ m := (Finset.mem_erase.mp hx_er1).1
            have hxS : S'.min' hS'_ne ∈ S := Finset.mem_of_mem_erase hx_er1
            have hminS := Finset.min'_le S _ hxS
            omega
        have hs' : runDown S' (S'.max' hS'_ne) = m := by
          rw [hM']
          apply le_antisymm
          · refine runDown_le_of_not_mem ?_
            have heq : M + 1 - m = M - m + 1 := by omega
            rw [heq]
            intro hmem
            rcases Finset.mem_insert.mp hmem with hbad | hbad
            · omega
            · exact (Finset.mem_erase.mp hbad).1 rfl
          · refine runDown_ge_of_forall (by omega) fun j hj => ?_
            cases j with
            | zero =>
              rw [Nat.sub_zero]
              exact Finset.mem_insert_self (M + 1) _
            | succ j =>
              have hval : M + 1 - (j + 1) = M - j := by omega
              rw [hval]
              apply Finset.mem_insert_of_mem
              refine Finset.mem_erase.mpr ⟨by omega, Finset.mem_erase.mpr ⟨by omega, ?_⟩⟩
              exact runDown_mem (by omega : j < s)
        have hB' : runDown S' (S'.max' hS'_ne) < S'.min' hS'_ne ∧
            2 * runDown S' (S'.max' hS'_ne) < S'.max' hS'_ne := by
          rw [hs', hM']
          exact ⟨hm'_gt, by omega⟩
        have hS'_moved : S' ∈ A_moved := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS'_sub, hS'_sum⟩, ?_⟩
          intro ⟨hne'', hbad⟩
          have h1 : S'.max' hne'' = S'.max' hS'_ne := rfl
          have h2 : S'.min' hne'' = S'.min' hS'_ne := rfl
          rw [h1, h2] at hbad
          exact hbad.2 hB'
        have hS_fr_moved : franklin S hS ∈ A_moved := by rwa [hS'_def]
        refine ⟨hS_fr_moved, by rw [hS'_def]; exact hparity, hS_fr_moved, ?_⟩
        rw [hfr_irrel hS_fr_moved hS'_moved hS'_def]
        dsimp only [franklin]
        have hnotA' : ¬ (S'.min' hS'_ne ≤ runDown S' (S'.max' hS'_ne) ∧
            2 * S'.min' hS'_ne ≤ S'.max' hS'_ne) := by
          have hs'_lt := hB'.1
          omega
        split_ifs with hbad
        · exfalso
          exact hnotA' hbad
        · rw [hs', hM']
          ext x
          dsimp only [S']
          simp only [Finset.mem_insert, Finset.mem_erase]
          have hsub' : M + 1 - m = M - m + 1 := by omega
          rw [hsub']
          constructor
          · rintro (rfl | rfl | ⟨hx1, hx2⟩)
            · exact hm_mem
            · exact hmid_mem
            · rcases hx2 with rfl | ⟨_, _, hxS⟩
              · contradiction
              · exact hxS
          · intro hxS
            by_cases hxm : x = m
            · exact Or.inl hxm
            · by_cases hxmid : x = M - m + 1
              · exact Or.inr (Or.inl hxmid)
              · have hx_ne_M1 : x ≠ M + 1 := by
                  have := Finset.le_max' S x hxS
                  omega
                exact Or.inr (Or.inr ⟨hx_ne_M1, Or.inr ⟨hxmid, hxm, hxS⟩⟩)
      · have hB : s < m ∧ 2 * s < M := by
          by_contra hnotB
          exact hS_not_fix ⟨hSne, hA, hnotB⟩
        let S' := insert s (insert (M - s) (S.erase M))
        have hS'_def : franklin S hS = S' := by
          dsimp only [franklin]
          rw [dif_neg hA]
        have hs_nmem : s ∉ S := fun hs_mem => by
          have := Finset.min'_le S s hs_mem
          omega
        have hMs_nmem : M - s ∉ S := runDown_not_mem h0nmem M
        have hs_ne_Ms : s ≠ M - s := by omega
        have hMs_ne_M : M - s ≠ M := by omega
        have hs_ne_M : s ≠ M := by omega
        have hS'_card : S'.card = S.card + 1 := by
          have h1 : M - s ∉ S.erase M := fun h => hMs_nmem (Finset.mem_of_mem_erase h)
          have h2 : s ∉ insert (M - s) (S.erase M) := by
            intro h
            rcases Finset.mem_insert.mp h with hbad | hbad
            · exact hs_ne_Ms hbad
            · exact hs_nmem (Finset.mem_of_mem_erase hbad)
          rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1,
              Finset.card_erase_of_mem hM_mem]
          have : 1 ≤ S.card := Finset.card_pos.mpr hSne
          omega
        have hparity : (-1 : ℤ) ^ S.card + (-1 : ℤ) ^ S'.card = 0 := by
          rw [hS'_card, pow_succ]
          ring
        have hS'_sub : S' ⊆ Finset.Icc 1 N := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx1
          · exact Finset.mem_Icc.mpr ⟨hs_pos, by omega⟩
          · rcases Finset.mem_insert.mp hx1 with rfl | hx2
            · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            · exact hS_sub (Finset.mem_of_mem_erase hx2)
        have hS'_sum : S'.sum id = n := by
          have h1 : M - s ∉ S.erase M := fun h => hMs_nmem (Finset.mem_of_mem_erase h)
          have h2 : s ∉ insert (M - s) (S.erase M) := by
            intro h
            rcases Finset.mem_insert.mp h with hbad | hbad
            · exact hs_ne_Ms hbad
            · exact hs_nmem (Finset.mem_of_mem_erase hbad)
          have hs1 := Finset.sum_insert h2 (f := id)
          have hs2 := Finset.sum_insert h1 (f := id)
          have hs3 := Finset.add_sum_erase S id hM_mem
          change S'.sum id = _ at hs1
          have h1' : S'.sum id = s + ∑ x ∈ insert (M - s) (S.erase M), x := hs1
          have h2' : ∑ x ∈ insert (M - s) (S.erase M), x = (M - s) + ∑ x ∈ S.erase M, x := hs2
          have h3' : M + ∑ x ∈ S.erase M, x = ∑ x ∈ S, x := hs3
          omega
        have hS'_ne : S'.Nonempty := ⟨s, Finset.mem_insert_self _ _⟩
        have hm' : S'.min' hS'_ne = s := by
          apply le_antisymm
          · exact Finset.min'_le S' s (Finset.mem_insert_self _ _)
          · refine Finset.le_min' S' hS'_ne s fun x hx => ?_
            rcases Finset.mem_insert.mp hx with rfl | hx1
            · exact le_rfl
            · rcases Finset.mem_insert.mp hx1 with rfl | hx2
              · omega
              · have := Finset.min'_le S x (Finset.mem_of_mem_erase hx2)
                omega
        have hMm1_mem : M - 1 ∈ S' := by
          by_cases hs1 : s = 1
          · rw [← hs1]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · have hmem : M - 1 ∈ S := runDown_mem (by omega : 1 < s)
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨by omega, hmem⟩))
        have hM' : S'.max' hS'_ne = M - 1 := by
          apply le_antisymm
          · refine Finset.max'_le S' _ _ fun x hx => ?_
            rcases Finset.mem_insert.mp hx with rfl | hx1
            · omega
            · rcases Finset.mem_insert.mp hx1 with rfl | hx2
              · omega
              · rcases Finset.mem_erase.mp hx2 with ⟨hx_ne, hxS⟩
                have := Finset.le_max' S x hxS
                omega
          · exact Finset.le_max' S' _ hMm1_mem
        have hs'_ge : s ≤ runDown S' (S'.max' hS'_ne) := by
          rw [hM']
          refine runDown_ge_of_forall (by omega) fun j hj => ?_
          by_cases hlast : j = s - 1
          · have heq : M - 1 - j = M - s := by omega
            rw [heq]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          · have hj1 : j + 1 < s := by omega
            have hmem : M - (j + 1) ∈ S := runDown_mem hj1
            have heq : M - 1 - j = M - (j + 1) := by omega
            rw [heq]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.mpr ⟨by omega, hmem⟩))
        have hA' : S'.min' hS'_ne ≤ runDown S' (S'.max' hS'_ne) ∧
            2 * S'.min' hS'_ne ≤ S'.max' hS'_ne := by
          rw [hm']
          have hs'_ge2 : s ≤ runDown S' (M - 1) := by rwa [hM'] at hs'_ge
          rw [hM']
          exact ⟨hs'_ge2, by omega⟩
        have hS'_moved : S' ∈ A_moved := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS'_sub, hS'_sum⟩, ?_⟩
          intro ⟨hne'', hbad⟩
          have h1 : S'.max' hne'' = S'.max' hS'_ne := rfl
          have h2 : S'.min' hne'' = S'.min' hS'_ne := rfl
          rw [h1, h2] at hbad
          exact hbad.1 hA'
        have hS_fr_moved : franklin S hS ∈ A_moved := by rwa [hS'_def]
        refine ⟨hS_fr_moved, by rw [hS'_def]; exact hparity, hS_fr_moved, ?_⟩
        rw [hfr_irrel hS_fr_moved hS'_moved hS'_def]
        dsimp only [franklin]
        rw [dif_pos hA', hm', hM']
        have hadd1 : M - 1 + 1 = M := by omega
        have hsub1 : M - 1 - s + 1 = M - s := by omega
        rw [hadd1, hsub1]
        ext x
        dsimp only [S']
        simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨hx1, hx2, hx3⟩)
          · exact hM_mem
          · rcases hx3 with rfl | rfl | ⟨_, hxS⟩
            · contradiction
            · contradiction
            · exact hxS
        · intro hxS
          by_cases hxM : x = M
          · exact Or.inl hxM
          · have hxs : x ≠ s := fun h => by subst h; exact hs_nmem hxS
            have hxMs : x ≠ M - s := fun h => by subst h; exact hMs_nmem hxS
            exact Or.inr ⟨hxMs, hxs, Or.inr (Or.inr ⟨hxM, hxS⟩)⟩
    refine Finset.sum_involution franklin ?_ ?_ ?_ ?_
    · intro S hS
      linarith [(hprop S hS).2.1]
    · intro S hS _ heq
      have h0 := (hprop S hS).2.1
      rw [heq] at h0
      have hne0 : (-1 : ℤ) ^ (franklin S hS).card ≠ 0 := by simp
      omega
    · intro S hS
      exact (hprop S hS).1
    · intro S hS
      obtain ⟨hS', hinv⟩ := (hprop S hS).2.2
      exact hinv
  rw [hmoved_zero, add_zero]
  by_cases hp1 : ∃ k, 1 ≤ k ∧ pentagonalNum1 k = n
  · obtain ⟨k, hk1, hpk⟩ := hp1
    have hcoeff : pentagonalCoeff n = (-1 : ℤ) ^ k := by rw [← hpk]; exact pentagonalCoeff_num1 hk1
    let S₀ := Finset.Icc k (2 * k - 1)
    have hS₀_mem : S₀ ∈ A_fixed := by
      have hsub : S₀ ⊆ Finset.Icc 1 N := fun x hx => by
        rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
        have hle_n : 2 * k - 1 ≤ n := by
          rw [← hpk]
          by_cases hk2 : k = 1
          · subst hk2; simp [pentagonalNum1]
          · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
            have h := two_mul_pentagonalNum1 (k' + 2)
            have hs : 3 * (k' + 2) - 1 = 3 * k' + 5 := by omega
            have hs2 : 2 * (k' + 2) - 1 = 2 * k' + 3 := by omega
            rw [hs] at h
            rw [hs2]
            nlinarith
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hsum : S₀.sum id = n := by rw [← hpk]; exact sum_Icc_eq_pentagonalNum1 k hk1
      have hne : S₀.Nonempty := ⟨k, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
      have hmin : S₀.min' hne = k := by
        apply le_antisymm
        · exact Finset.min'_le S₀ k (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
        · exact Finset.le_min' S₀ hne k fun x hx => (Finset.mem_Icc.mp hx).1
      have hmax : S₀.max' hne = 2 * k - 1 := by
        apply le_antisymm
        · exact Finset.max'_le S₀ _ _ fun x hx => (Finset.mem_Icc.mp hx).2
        · exact Finset.le_max' S₀ (2 * k - 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
      have hrun : runDown S₀ (S₀.max' hne) = k := by
        rw [hmax]
        apply le_antisymm
        · refine runDown_le_of_not_mem ?_
          have heq : 2 * k - 1 - k = k - 1 := by omega
          rw [heq, Finset.mem_Icc]
          omega
        · refine runDown_ge_of_forall (by omega) fun j hj => by
            rw [Finset.mem_Icc]
            omega
      have hfix : isFixed S₀ := by
        refine ⟨hne, ?_⟩
        dsimp only
        rw [hmin, hrun, hmax]
        constructor <;> omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsum⟩, hfix⟩
    have huniq : A_fixed = {S₀} := by
      ext S
      simp only [Finset.mem_singleton]
      constructor
      · intro hS
        have hSA := (Finset.mem_filter.mp hS).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
        have hsum := (Finset.mem_filter.mp hSA).2
        obtain ⟨hne, hfix⟩ := (Finset.mem_filter.mp hS).2
        have hiff := (franklin_fixed_iff hsub hsum hne).mp hfix
        rcases hiff with ⟨hmeq, hMeq, hSeq⟩ | ⟨hmeq, hMeq, hSeq⟩
        · have hs1 : 1 ≤ runDown S (S.max' hne) := by
            have hm1 := (Finset.mem_Icc.mp (hsub (Finset.min'_mem S hne))).1
            omega
          have hpk' : pentagonalNum1 (runDown S (S.max' hne)) = n := by
            have hsum' : S.sum id = n := hsum
            rw [← hsum']
            conv_rhs => rw [hSeq]
            exact (sum_Icc_eq_pentagonalNum1 _ hs1).symm
          have hkeq := pentagonalNum1_injOn hs1 hk1 (hpk'.trans hpk.symm)
          rw [hSeq, hkeq]
        · have hs1 : 1 ≤ runDown S (S.max' hne) :=
            runDown_pos_of_mem (Finset.mem_Icc.mp (hsub (Finset.max'_mem S hne))).1
              (Finset.max'_mem S hne)
          have hpk' : pentagonalNum2 (runDown S (S.max' hne)) = n := by
            have hsum' : S.sum id = n := hsum
            rw [← hsum']
            conv_rhs => rw [hSeq]
            exact (sum_Icc_eq_pentagonalNum2 _ hs1).symm
          exfalso
          exact pentagonalNum1_ne_pentagonalNum2 hk1 hs1 (hpk.trans hpk'.symm)
      · rintro rfl
        exact hS₀_mem
    rw [huniq, Finset.sum_singleton, hcoeff]
    have hcard : S₀.card = k := by
      simp only [S₀, Nat.card_Icc]
      omega
    rw [hcard]
  · by_cases hp2 : ∃ k, 1 ≤ k ∧ pentagonalNum2 k = n
    · obtain ⟨k, hk1, hpk⟩ := hp2
      have hcoeff : pentagonalCoeff n = (-1 : ℤ) ^ k := by rw [← hpk]; exact pentagonalCoeff_num2 hk1
      let S₀ := Finset.Icc (k + 1) (2 * k)
      have hS₀_mem : S₀ ∈ A_fixed := by
        have hsub : S₀ ⊆ Finset.Icc 1 N := fun x hx => by
          rcases Finset.mem_Icc.mp hx with ⟨hlo, hhi⟩
          have hle_n : 2 * k ≤ n := by
            have := two_mul_pentagonalNum2 k
            rw [← hpk]
            nlinarith
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hsum : S₀.sum id = n := by rw [← hpk]; exact sum_Icc_eq_pentagonalNum2 k hk1
        have hne : S₀.Nonempty := ⟨k + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
        have hmin : S₀.min' hne = k + 1 := by
          apply le_antisymm
          · exact Finset.min'_le S₀ (k + 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
          · exact Finset.le_min' S₀ hne (k + 1) fun x hx => (Finset.mem_Icc.mp hx).1
        have hmax : S₀.max' hne = 2 * k := by
          apply le_antisymm
          · exact Finset.max'_le S₀ _ _ fun x hx => (Finset.mem_Icc.mp hx).2
          · exact Finset.le_max' S₀ (2 * k) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
        have hrun : runDown S₀ (S₀.max' hne) = k := by
          rw [hmax]
          apply le_antisymm
          · refine runDown_le_of_not_mem ?_
            have heq : 2 * k - k = k := by omega
            rw [heq, Finset.mem_Icc]
            omega
          · refine runDown_ge_of_forall (by omega) fun j hj => by
              rw [Finset.mem_Icc]
              omega
        have hfix : isFixed S₀ := by
          refine ⟨hne, ?_⟩
          dsimp only
          rw [hmin, hrun, hmax]
          constructor <;> omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsum⟩, hfix⟩
      have huniq : A_fixed = {S₀} := by
        ext S
        simp only [Finset.mem_singleton]
        constructor
        · intro hS
          have hSA := (Finset.mem_filter.mp hS).1
          have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
          have hsum := (Finset.mem_filter.mp hSA).2
          obtain ⟨hne, hfix⟩ := (Finset.mem_filter.mp hS).2
          have hiff := (franklin_fixed_iff hsub hsum hne).mp hfix
          rcases hiff with ⟨hmeq, hMeq, hSeq⟩ | ⟨hmeq, hMeq, hSeq⟩
          · have hs1 : 1 ≤ runDown S (S.max' hne) := by
              have hm1 := (Finset.mem_Icc.mp (hsub (Finset.min'_mem S hne))).1
              omega
            have hpk' : pentagonalNum1 (runDown S (S.max' hne)) = n := by
              have hsum' : S.sum id = n := hsum
              rw [← hsum']
              conv_rhs => rw [hSeq]
              exact (sum_Icc_eq_pentagonalNum1 _ hs1).symm
            exfalso
            exact hp1 ⟨_, hs1, hpk'⟩
          · have hs1 : 1 ≤ runDown S (S.max' hne) :=
              runDown_pos_of_mem (Finset.mem_Icc.mp (hsub (Finset.max'_mem S hne))).1
                (Finset.max'_mem S hne)
            have hpk' : pentagonalNum2 (runDown S (S.max' hne)) = n := by
              have hsum' : S.sum id = n := hsum
              rw [← hsum']
              conv_rhs => rw [hSeq]
              exact (sum_Icc_eq_pentagonalNum2 _ hs1).symm
            have hkeq := pentagonalNum2_injOn hs1 hk1 (hpk'.trans hpk.symm)
            rw [hSeq, hkeq]
        · rintro rfl
          exact hS₀_mem
      rw [huniq, Finset.sum_singleton, hcoeff]
      have hcard : S₀.card = k := by
        simp only [S₀, Nat.card_Icc]
        omega
      rw [hcard]
    · have hcoeff : pentagonalCoeff n = 0 :=
        pentagonalCoeff_eq_zero hn0 (fun k hk hpk => hp1 ⟨k, hk, hpk⟩)
          (fun k hk hpk => hp2 ⟨k, hk, hpk⟩)
      have hemp : A_fixed = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro S hS
        have hSA := (Finset.mem_filter.mp hS).1
        have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hSA).1
        have hsum := (Finset.mem_filter.mp hSA).2
        obtain ⟨hne, hfix⟩ := (Finset.mem_filter.mp hS).2
        have hiff := (franklin_fixed_iff hsub hsum hne).mp hfix
        rcases hiff with ⟨hmeq, hMeq, hSeq⟩ | ⟨hmeq, hMeq, hSeq⟩
        · have hs1 : 1 ≤ runDown S (S.max' hne) := by
            have hm1 := (Finset.mem_Icc.mp (hsub (Finset.min'_mem S hne))).1
            omega
          exact hp1 ⟨_, hs1, by
            have hsum' : S.sum id = n := hsum
            rw [← hsum']
            conv_rhs => rw [hSeq]
            exact (sum_Icc_eq_pentagonalNum1 _ hs1).symm⟩
        · have hs1 : 1 ≤ runDown S (S.max' hne) :=
            runDown_pos_of_mem (Finset.mem_Icc.mp (hsub (Finset.max'_mem S hne))).1
              (Finset.max'_mem S hne)
          exact hp2 ⟨_, hs1, by
            have hsum' : S.sum id = n := hsum
            rw [← hsum']
            conv_rhs => rw [hSeq]
            exact (sum_Icc_eq_pentagonalNum2 _ hs1).symm⟩
      rw [hemp, Finset.sum_empty, hcoeff]

private lemma prod_pow_sum {R : Type*} [CommRing R] (S : Finset ℕ) (f : ℕ → ℕ) (x : R) :
    ∏ k ∈ S, x ^ (f k) = x ^ (∑ k ∈ S, f k) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_add]

private lemma coeff_prod_one_sub_mul_geom (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n
      ((∏ k ∈ Finset.Icc 1 N, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)) *
        (∏ k ∈ Finset.Icc 1 N,
          ∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * j))) =
      PowerSeries.coeff n (1 : PowerSeries ℤ) := by
  have hfactor : ∀ k : ℕ,
      (1 - (PowerSeries.X : PowerSeries ℤ) ^ k) *
        (∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * j)) =
      1 - (PowerSeries.X : PowerSeries ℤ) ^ (k * (N + 1)) := by
    intro k
    rw [sub_mul, one_mul, Finset.mul_sum]
    have hshift : ∑ j ∈ Finset.range (N + 1),
        (PowerSeries.X : PowerSeries ℤ) ^ k * (PowerSeries.X : PowerSeries ℤ) ^ (k * j) =
        ∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * (j + 1)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_add, show k + k * j = k * (j + 1) by ring]
    rw [hshift]
    have htele := Finset.sum_range_sub' (fun j => (PowerSeries.X : PowerSeries ℤ) ^ (k * j)) (N + 1)
    simp only [mul_zero, pow_zero] at htele
    rw [← Finset.sum_sub_distrib, htele]
  rw [← Finset.prod_mul_distrib]
  have hprod_eq :
      (∏ k ∈ Finset.Icc 1 N,
        (1 - (PowerSeries.X : PowerSeries ℤ) ^ k) *
          ∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * j)) =
      ∏ k ∈ Finset.Icc 1 N, (1 + (-(PowerSeries.X : PowerSeries ℤ) ^ (k * (N + 1)))) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hfactor k]
    ring
  rw [hprod_eq, Finset.prod_one_add, map_sum]
  have h0mem : ∅ ∈ (Finset.Icc 1 N).powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
  rw [← Finset.add_sum_erase _ _ h0mem, Finset.prod_empty]
  have hrest : ∑ S ∈ (Finset.Icc 1 N).powerset.erase ∅,
      PowerSeries.coeff n (∏ k ∈ S, -(PowerSeries.X : PowerSeries ℤ) ^ (k * (N + 1))) = 0 := by
    refine Finset.sum_eq_zero fun S hS => ?_
    have hS_ne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    have hS_sub : S ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp (Finset.mem_erase.mp hS).2
    obtain ⟨k₀, hk₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS_ne
    have hk₀_ge : 1 ≤ k₀ := (Finset.mem_Icc.mp (hS_sub hk₀)).1
    have hdeg_ge : N + 1 ≤ ∑ k ∈ S, k * (N + 1) := by
      calc N + 1 = 1 * (N + 1) := (one_mul _).symm
        _ ≤ k₀ * (N + 1) := Nat.mul_le_mul_right _ hk₀_ge
        _ ≤ ∑ k ∈ S, k * (N + 1) :=
          Finset.single_le_sum (f := fun k => k * (N + 1)) (fun _ _ => Nat.zero_le _) hk₀
    have hprod_S : (∏ k ∈ S, -(PowerSeries.X : PowerSeries ℤ) ^ (k * (N + 1))) =
        PowerSeries.C ((-1 : ℤ) ^ S.card) *
          (PowerSeries.X : PowerSeries ℤ) ^ (∑ k ∈ S, k * (N + 1)) := by
      have hneg : ∀ k : ℕ, -(PowerSeries.X : PowerSeries ℤ) ^ (k * (N + 1)) =
          (-1 : PowerSeries ℤ) * (PowerSeries.X : PowerSeries ℤ) ^ (k * (N + 1)) :=
        fun k => by ring
      simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, prod_pow_sum]
      simp
    rw [hprod_S, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    rw [if_neg (by omega : n ≠ ∑ k ∈ S, k * (N + 1)), mul_zero]
  rw [hrest, add_zero]

private lemma prod_geom_eq_sum_fun (M N : ℕ) :
    (∏ k ∈ Finset.Icc 1 M,
        ∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * j)) =
      ∑ f : (Fin M → Fin (N + 1)),
        (PowerSeries.X : PowerSeries ℤ) ^ (∑ k : Fin M, (k.val + 1) * (f k).val) := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : M + 1 ∉ Finset.Icc 1 M := by simp
    rw [hIcc, Finset.prod_insert hnot, ih]
    have hrange : (∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ ((M + 1) * j)) =
        ∑ j : Fin (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ ((M + 1) * j.val) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => (PowerSeries.X : PowerSeries ℤ) ^ ((M + 1) * j)) (N + 1)]
    rw [hrange, Finset.sum_mul_sum]
    have hprod_equiv :
        ∑ p : Fin (N + 1) × (Fin M → Fin (N + 1)),
          (PowerSeries.X : PowerSeries ℤ) ^ ((M + 1) * p.1.val) *
            (PowerSeries.X : PowerSeries ℤ) ^ (∑ k : Fin M, (k.val + 1) * (p.2 k).val) =
        ∑ f : (Fin (M + 1) → Fin (N + 1)),
          (PowerSeries.X : PowerSeries ℤ) ^ (∑ k : Fin (M + 1), (k.val + 1) * (f k).val) := by
      refine Finset.sum_bij (fun p _ => Fin.snoc p.2 p.1) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro p₁ _ p₂ _ heq
        have hf : p₁.2 = p₂.2 := by
          funext k
          have hk := congrFun heq (Fin.castSucc k)
          simpa using hk
        have hj : p₁.1 = p₂.1 := by
          have hl := congrFun heq (Fin.last M)
          simpa using hl
        exact Prod.ext hj hf
      · intro f _
        refine ⟨(f (Fin.last M), fun k => f (Fin.castSucc k)), Finset.mem_univ _, ?_⟩
        funext k
        by_cases hk : k.val = M
        · have hlast : k = Fin.last M := Fin.ext hk
          subst hlast
          simp
        · have hk_lt : k.val < M := by have := k.isLt; omega
          have hcast : k = Fin.castSucc ⟨k.val, hk_lt⟩ := Fin.ext rfl
          rw [hcast, Fin.snoc_castSucc]
      · intro p _
        rw [← pow_add, Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        ring_nf
    rw [← hprod_equiv]
    exact (Fintype.sum_prod_type (fun p : Fin (N + 1) × (Fin M → Fin (N + 1)) =>
      (PowerSeries.X : PowerSeries ℤ) ^ ((M + 1) * p.1.val) *
        (PowerSeries.X : PowerSeries ℤ) ^ (∑ k : Fin M, (k.val + 1) * (p.2 k).val))).symm

private lemma coeff_prod_geom_eq_partitionCount (N n : ℕ) (hn : n ≤ N) :
    PowerSeries.coeff n
      (∏ k ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.range (N + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * j)) =
      (partitionCount n : ℤ) := by
  rw [prod_geom_eq_sum_fun, map_sum]
  simp_rw [PowerSeries.coeff_X_pow]
  have hsum_nat : (∑ f : Fin N → Fin (N + 1),
      (if n = ∑ k : Fin N, (k.val + 1) * (f k).val then (1 : ℤ) else 0)) =
      ((Finset.univ.filter fun f : Fin N → Fin (N + 1) =>
        ∑ k : Fin N, (k.val + 1) * (f k).val = n).card : ℤ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases heq : ∑ k : Fin N, (k.val + 1) * (f k).val = n
    · rw [if_pos heq.symm, if_pos heq]; simp
    · rw [if_neg (fun h => heq h.symm), if_neg heq]; simp
  rw [hsum_nat]
  congr 1
  unfold partitionCount
  rw [← Finset.card_univ (α := IntPartition n)]
  symm
  refine Finset.card_bij
    (fun (P : IntPartition n) (_ : P ∈ Finset.univ) (k : Fin N) =>
      if hk : k.val < n then
        (⟨P.mult ⟨k.val + 1, by omega⟩, Nat.lt_succ_of_le (le_trans (P.mult_le _) hn)⟩ :
          Fin (N + 1))
      else 0)
    ?_ ?_ ?_
  · intro P _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    let pM : ℕ → ℕ := fun k => if hk : k < n + 1 then P.mult ⟨k, hk⟩ else 0
    have hPsum := P.sum_eq
    have hrange : ∑ k : Fin (n + 1), k.val * P.mult k =
        ∑ k ∈ Finset.range n, (k + 1) * pM (k + 1) := by
      have h1 : ∑ k : Fin (n + 1), k.val * P.mult k =
          ∑ k ∈ Finset.range (n + 1), k * pM k := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => k * pM k) (n + 1)]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [pM, dif_pos k.isLt]
      rw [h1, Finset.sum_range_succ']
      simp only [zero_mul, add_zero]
    have hsplit : ∑ k : Fin N, (k.val + 1) *
        (if hk : k.val < n then
          (⟨P.mult ⟨k.val + 1, by omega⟩, Nat.lt_succ_of_le (le_trans (P.mult_le _) hn)⟩ :
            Fin (N + 1))
        else 0).val =
        ∑ k ∈ Finset.range N, (k + 1) *
          (if k < n then pM (k + 1) else 0) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (k + 1) * (if k < n then pM (k + 1) else 0)) N]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k.val < n
      · simp only [dif_pos hk, if_pos hk, pM, dif_pos (Nat.succ_lt_succ hk)]
      · simp [hk]
    rw [hsplit]
    have hsum_cut : ∑ k ∈ Finset.range N, (k + 1) *
        (if k < n then pM (k + 1) else 0) =
        ∑ k ∈ Finset.range n, (k + 1) * pM (k + 1) := by
      have hite : ∀ k ∈ Finset.range N,
          (k + 1) * (if k < n then pM (k + 1) else 0) =
          if k ∈ Finset.range n then (k + 1) * pM (k + 1) else 0 := by
        intro k _
        by_cases hkn : k < n
        · simp [hkn]
        · simp [hkn]
      rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
      have hflt : (Finset.range N).filter (fun k => k ∈ Finset.range n) = Finset.range n := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hflt]
    rw [hsum_cut, ← hrange, hPsum]
  · intro P₁ _ P₂ _ heq
    ext j
    by_cases hj0 : j.val = 0
    · have hjfin : j = (0 : Fin (n + 1)) := Fin.ext hj0
      rw [hjfin, P₁.mult_zero, P₂.mult_zero]
    · have hj_ge : 1 ≤ j.val := Nat.pos_of_ne_zero hj0
      have hk_lt_n : j.val - 1 < n := by have := j.isLt; omega
      have hk_lt_N : j.val - 1 < N := lt_of_lt_of_le hk_lt_n hn
      let k : Fin N := ⟨j.val - 1, hk_lt_N⟩
      have hk_eq := congrArg Fin.val (congrFun heq k)
      dsimp only [k] at hk_eq
      rw [dif_pos hk_lt_n, dif_pos hk_lt_n] at hk_eq
      dsimp only at hk_eq
      have hj_eq : ∀ p : j.val - 1 + 1 < n + 1, (⟨j.val - 1 + 1, p⟩ : Fin (n + 1)) = j :=
        fun _ => Fin.ext (Nat.sub_add_cancel hj_ge)
      simpa only [hj_eq] using hk_eq
  · intro f hf
    have hfs := (Finset.mem_filter.mp hf).2
    have hf_zero : ∀ k : Fin N, n ≤ k.val → (f k).val = 0 := by
      intro k hk
      have hle : (k.val + 1) * (f k).val ≤ ∑ i : Fin N, (i.val + 1) * (f i).val :=
        Finset.single_le_sum (f := fun i : Fin N => (i.val + 1) * (f i).val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      rw [hfs] at hle
      by_contra hne0
      have hpos : 1 ≤ (f k).val := Nat.pos_of_ne_zero hne0
      have hgt : n + 1 ≤ (k.val + 1) * (f k).val := by
        calc n + 1 ≤ k.val + 1 := by omega
          _ = (k.val + 1) * 1 := (mul_one _).symm
          _ ≤ (k.val + 1) * (f k).val := Nat.mul_le_mul_left _ hpos
      omega
    let P : IntPartition n :=
      { mult := fun j =>
          if hj : 1 ≤ j.val ∧ j.val - 1 < N then (f ⟨j.val - 1, hj.2⟩).val else 0
        mult_zero := by simp
        sum_eq := by
          let fVal : ℕ → ℕ := fun x =>
            if hx : x < N then (f ⟨x, hx⟩).val else 0
          have h1 : ∑ j : Fin (n + 1), j.val *
              (if hj : 1 ≤ j.val ∧ j.val - 1 < N then (f ⟨j.val - 1, hj.2⟩).val else 0) =
              ∑ j ∈ Finset.range (n + 1),
                j * (if hj : 1 ≤ j ∧ j - 1 < N then fVal (j - 1) else 0) := by
            rw [← Fin.sum_univ_eq_sum_range (fun j =>
              j * (if hj : 1 ≤ j ∧ j - 1 < N then fVal (j - 1) else 0)) (n + 1)]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : 1 ≤ j.val ∧ j.val - 1 < N
            · rw [dif_pos hj, dif_pos hj]
              simp only [fVal, dif_pos hj.2]
            · rw [dif_neg hj, dif_neg hj]
          rw [h1, Finset.sum_range_succ']
          simp only [zero_mul, add_zero]
          have h2 : ∑ x ∈ Finset.range n,
              (x + 1) * (if hx : 1 ≤ x + 1 ∧ x + 1 - 1 < N then fVal (x + 1 - 1) else 0) =
              ∑ x ∈ Finset.range N, (x + 1) * fVal x := by
            have hcut : ∀ x ∈ Finset.range N,
                (x + 1) * fVal x =
                if x ∈ Finset.range n then (x + 1) * fVal x else 0 := by
              intro x hx
              have hxN := Finset.mem_range.mp hx
              by_cases hxn : x < n
              · simp [hxn]
              · have hz := hf_zero ⟨x, hxN⟩ (Nat.not_lt.mp hxn)
                rw [if_neg (fun hm => hxn (Finset.mem_range.mp hm))]
                simp only [fVal, dif_pos hxN, hz, mul_zero]
            rw [Finset.sum_congr rfl hcut, ← Finset.sum_filter]
            have hflt : (Finset.range N).filter (fun x => x ∈ Finset.range n) = Finset.range n := by
              ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
            rw [hflt]
            refine Finset.sum_congr rfl fun x hx => ?_
            have hxn : x < n := Finset.mem_range.mp hx
            have hxN : x < N := lt_of_lt_of_le hxn hn
            have hxcond : 1 ≤ x + 1 ∧ x + 1 - 1 < N := ⟨Nat.succ_pos x, by rw [Nat.add_sub_cancel]; exact hxN⟩
            rw [dif_pos hxcond, Nat.add_sub_cancel]
          rw [h2, ← Fin.sum_univ_eq_sum_range (fun x => (x + 1) * fVal x) N]
          have hfin : ∑ x : Fin N, (x.val + 1) * fVal x.val =
              ∑ x : Fin N, (x.val + 1) * (f x).val := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [fVal, dif_pos x.isLt]
          rw [hfin, hfs] }
    refine ⟨P, Finset.mem_univ P, ?_⟩
    funext k
    apply Fin.ext
    by_cases hk : k.val < n
    · have hkN : k.val + 1 - 1 < N := by rw [Nat.add_sub_cancel]; exact k.isLt
      have hk_cond : 1 ≤ k.val + 1 ∧ k.val + 1 - 1 < N := ⟨Nat.succ_pos k.val, hkN⟩
      rw [dif_pos hk]
      dsimp only [P]
      rw [dif_pos hk_cond]
      exact congrArg Fin.val (congrArg f (Fin.ext (Nat.add_sub_cancel k.val 1)))
    · rw [dif_neg hk]
      exact (hf_zero k (Nat.not_lt.mp hk)).symm

/-- **Euler's Partition Generating Function Identity:**
`partitionGF * pentagonalPS = 1` in `PowerSeries ℤ`. -/
theorem partitionGF_mul_pentagonalPS : partitionGF * pentagonalPS = 1 := by
  ext n
  let Q_n := ∏ k ∈ Finset.Icc 1 n, (1 - (PowerSeries.X : PowerSeries ℤ) ^ k)
  let P_n := ∏ k ∈ Finset.Icc 1 n,
    ∑ j ∈ Finset.range (n + 1), (PowerSeries.X : PowerSeries ℤ) ^ (k * j)
  have hcoeff_prod : PowerSeries.coeff n (partitionGF * pentagonalPS) =
      PowerSeries.coeff n (Q_n * P_n) := by
    rw [mul_comm partitionGF pentagonalPS, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p.1 ≤ n := (Finset.mem_antidiagonal.mp hp) ▸ Nat.le_add_right p.1 p.2
    have hp2 : p.2 ≤ n := (Finset.mem_antidiagonal.mp hp) ▸ Nat.le_add_left p.2 p.1
    have hQ : PowerSeries.coeff p.1 pentagonalPS = PowerSeries.coeff p.1 Q_n := by
      unfold pentagonalPS
      rw [PowerSeries.coeff_mk]
      exact (euler_pentagonal_prod_coeff p.1 n hp1).symm
    have hP : PowerSeries.coeff p.2 partitionGF = PowerSeries.coeff p.2 P_n := by
      unfold partitionGF
      rw [PowerSeries.coeff_mk]
      exact (coeff_prod_geom_eq_partitionCount n p.2 hp2).symm
    rw [hQ, hP]
  rw [hcoeff_prod]
  exact coeff_prod_one_sub_mul_geom n n le_rfl

/-- **Euler's Pentagonal Recurrence for `p(n)`:**
For all `n ≥ 1`,
`p(n) = ∑_{k=1}^n (-1)^{k+1} (p(n - k(3k-1)/2) + p(n - k(3k+1)/2))`
where terms with `k(3k ± 1)/2 > n` vanish. -/
theorem partitionCount_pentagonal_recurrence (n : ℕ) (hn : 1 ≤ n) :
    (partitionCount n : ℤ) =
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (k + 1) *
        ((if pentagonalNum1 k ≤ n then (partitionCount (n - pentagonalNum1 k) : ℤ) else 0) +
         (if pentagonalNum2 k ≤ n then (partitionCount (n - pentagonalNum2 k) : ℤ) else 0)) := by
  have hmul : PowerSeries.coeff n (pentagonalPS * partitionGF) = 0 := by
    rw [mul_comm, partitionGF_mul_pentagonalPS, PowerSeries.coeff_one]
    rw [if_neg (by omega)]
  rw [PowerSeries.coeff_mul] at hmul
  have hsplit : ∑ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff p.1 pentagonalPS * PowerSeries.coeff p.2 partitionGF =
      ∑ m ∈ Finset.range (n + 1), pentagonalCoeff m * (partitionCount (n - m) : ℤ) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun x y => PowerSeries.coeff x pentagonalPS * PowerSeries.coeff y partitionGF) n]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [pentagonalPS, partitionGF]
  rw [hsplit, Finset.sum_range_succ'] at hmul
  simp only [pentagonalCoeff_zero, Nat.sub_zero, one_mul] at hmul
  have hp_eq : (partitionCount n : ℤ) =
      - ∑ m ∈ Finset.range n, pentagonalCoeff (m + 1) * (partitionCount (n - (m + 1)) : ℤ) := by
    linarith
  have hIcc : Finset.Icc 1 n = (Finset.range n).image Nat.succ := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  have hsum_Icc :
      - ∑ m ∈ Finset.range n, pentagonalCoeff (m + 1) * (partitionCount (n - (m + 1)) : ℤ) =
      ∑ m ∈ Finset.Icc 1 n, (-pentagonalCoeff m) * (partitionCount (n - m) : ℤ) := by
    rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => by simp [neg_mul]
  rw [hp_eq, hsum_Icc]
  have hexpand : ∀ m ∈ Finset.Icc 1 n,
      (-pentagonalCoeff m) * (partitionCount (n - m) : ℤ) =
      ∑ k ∈ Finset.Icc 1 n, (-1 : ℤ) ^ (k + 1) *
        ((if pentagonalNum1 k = m then (partitionCount (n - pentagonalNum1 k) : ℤ) else 0) +
         (if pentagonalNum2 k = m then (partitionCount (n - pentagonalNum2 k) : ℤ) else 0)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmn : m ≤ n := (Finset.mem_Icc.mp hm).2
    have hpc : -pentagonalCoeff m =
        ∑ k ∈ Finset.Icc 1 n,
          ((if pentagonalNum1 k = m then (-1 : ℤ) ^ (k + 1) else 0) +
           (if pentagonalNum2 k = m then (-1 : ℤ) ^ (k + 1) else 0)) := by
      unfold pentagonalCoeff
      rw [if_neg (by omega : m ≠ 0)]
      have hneg : ∀ (s1 s2 : ℤ), -(s1 + s2) = (-s1) + (-s2) := fun _ _ => by ring
      rw [hneg, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
      have hcut1 : ∑ k ∈ Finset.Icc 1 m, -(if pentagonalNum1 k = m then (-1 : ℤ) ^ k else 0) =
          ∑ k ∈ Finset.Icc 1 n, if pentagonalNum1 k = m then (-1 : ℤ) ^ (k + 1) else 0 := by
        have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 n := fun k hk => by
          rcases Finset.mem_Icc.mp hk with ⟨h1, h2⟩; exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
        rw [← Finset.sum_subset hsub (fun k hk hnot => ?_)]
        · refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs with heq
          · rw [pow_succ]; ring
          · simp
        · rcases Finset.mem_Icc.mp hk with ⟨hk1, hkn⟩
          have hkm : m < k := by
            by_contra hle
            exact hnot (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
          have hgt : m < pentagonalNum1 k := lt_of_lt_of_le hkm (pentagonalNum1_le_of_le hk1)
          have hne : pentagonalNum1 k ≠ m := by omega
          simp [hne]
      have hcut2 : ∑ k ∈ Finset.Icc 1 m, -(if pentagonalNum2 k = m then (-1 : ℤ) ^ k else 0) =
          ∑ k ∈ Finset.Icc 1 n, if pentagonalNum2 k = m then (-1 : ℤ) ^ (k + 1) else 0 := by
        have hsub : Finset.Icc 1 m ⊆ Finset.Icc 1 n := fun k hk => by
          rcases Finset.mem_Icc.mp hk with ⟨h1, h2⟩; exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
        rw [← Finset.sum_subset hsub (fun k hk hnot => ?_)]
        · refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs with heq
          · rw [pow_succ]; ring
          · simp
        · rcases Finset.mem_Icc.mp hk with ⟨hk1, hkn⟩
          have hkm : m < k := by
            by_contra hle
            exact hnot (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
          have hgt : m < pentagonalNum2 k := lt_of_lt_of_le hkm (pentagonalNum2_le_of_le hk1)
          have hne : pentagonalNum2 k ≠ m := by omega
          simp [hne]
      rw [hcut1, hcut2, ← Finset.sum_add_distrib]
    rw [hpc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    by_cases h1 : pentagonalNum1 k = m
    · have h2 : pentagonalNum2 k ≠ m := fun h =>
        pentagonalNum1_ne_pentagonalNum2 hk1 hk1 (h1.trans h.symm)
      simp [h1, h2]
    · by_cases h2 : pentagonalNum2 k = m
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib]
  have hs1 : ∑ m ∈ Finset.Icc 1 n,
      (if pentagonalNum1 k = m then (partitionCount (n - pentagonalNum1 k) : ℤ) else 0) =
      if pentagonalNum1 k ≤ n then (partitionCount (n - pentagonalNum1 k) : ℤ) else 0 := by
    have hpos : 1 ≤ pentagonalNum1 k := pentagonalNum1_pos hk1
    by_cases hle : pentagonalNum1 k ≤ n
    · rw [if_pos hle, Finset.sum_eq_single (pentagonalNum1 k)]
      · simp
      · intro m _ hm; rw [if_neg hm.symm]
      · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hpos, hle⟩)
    · rw [if_neg hle]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hmn := (Finset.mem_Icc.mp hm).2
      rw [if_neg (by omega)]
  have hs2 : ∑ m ∈ Finset.Icc 1 n,
      (if pentagonalNum2 k = m then (partitionCount (n - pentagonalNum2 k) : ℤ) else 0) =
      if pentagonalNum2 k ≤ n then (partitionCount (n - pentagonalNum2 k) : ℤ) else 0 := by
    have hpos : 1 ≤ pentagonalNum2 k := le_trans hk1 (pentagonalNum2_le_of_le hk1)
    by_cases hle : pentagonalNum2 k ≤ n
    · rw [if_pos hle, Finset.sum_eq_single (pentagonalNum2 k)]
      · simp
      · intro m _ hm; rw [if_neg hm.symm]
      · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hpos, hle⟩)
    · rw [if_neg hle]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hmn := (Finset.mem_Icc.mp hm).2
      rw [if_neg (by omega)]
  rw [hs1, hs2]

/-! ### Part 2C: Erdős (1942) Elementary Partition Upper Bound -/

private lemma intPartition_sum_Icc {n : ℕ} (P : IntPartition n) :
    ∑ k ∈ Finset.Icc 1 n, k * (if hk : k < n + 1 then P.mult ⟨k, hk⟩ else 0) = n := by
  have hP := P.sum_eq
  have h1 : ∑ k : Fin (n + 1), k.val * P.mult k =
      ∑ k ∈ Finset.range (n + 1),
        k * (if hk : k < n + 1 then P.mult ⟨k, hk⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k => k * (if hk : k < n + 1 then P.mult ⟨k, hk⟩ else 0)) (n + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dif_pos k.isLt]
  rw [h1, Finset.sum_range_succ'] at hP
  simp only [zero_mul, add_zero] at hP
  have hIcc : Finset.Icc 1 n = (Finset.range n).image Nat.succ := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega
  rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
  exact hP

private lemma card_intPartition_ge_eq {n m t : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (_ht1 : 1 ≤ t) (hmt : m * t ≤ n) :
    (Finset.univ.filter fun P : IntPartition n => t ≤ P.mult ⟨m, by omega⟩).card =
      partitionCount (n - m * t) := by
  unfold partitionCount
  let pM : IntPartition n → ℕ → ℕ := fun P k =>
    if hk : k < n + 1 then P.mult ⟨k, hk⟩ else 0
  have hpM_eq : ∀ (P : IntPartition n) (k : ℕ) (hk : k < n + 1), pM P k = P.mult ⟨k, hk⟩ :=
    fun P k hk => dif_pos hk
  rw [← Finset.card_univ (α := IntPartition (n - m * t))]
  refine Finset.card_bij
    (fun (P : IntPartition n) (hP : P ∈ _) =>
      { mult := fun k =>
          if k.val = m then P.mult ⟨m, by omega⟩ - t
          else P.mult ⟨k.val, by omega⟩
        mult_zero := by simp [show (0 : ℕ) ≠ m by omega, P.mult_zero]
        sum_eq := by
          have hP'' : ∑ k ∈ Finset.Icc 1 n, k * pM P k = n := intPartition_sum_Icc P
          have ht_mem : t ≤ pM P m := by
            rw [hpM_eq P m (by omega)]
            exact (Finset.mem_filter.mp hP).2
          have hhi_zero : ∀ k ∈ Finset.Icc 1 n, n - m * t < k → k ≠ m →
              pM P k = 0 := by
            intro k hk hgt hne
            by_contra hne0
            have h1 : 1 ≤ pM P k := Nat.pos_of_ne_zero hne0
            have hpair : ({k, m} : Finset ℕ) ⊆ Finset.Icc 1 n := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl
              · exact hk
              · exact Finset.mem_Icc.mpr ⟨hm1, hmn⟩
            have hsum_le : ∑ x ∈ ({k, m} : Finset ℕ), x * pM P x ≤
                ∑ x ∈ Finset.Icc 1 n, x * pM P x :=
              Finset.sum_le_sum_of_subset_of_nonneg hpair (fun _ _ _ => Nat.zero_le _)
            rw [Finset.sum_pair hne, hP''] at hsum_le
            have hm_le : m * t ≤ m * pM P m := Nat.mul_le_mul_left _ ht_mem
            have hk_le : k ≤ k * pM P k := Nat.le_mul_of_pos_right _ h1
            omega
          have hmeq_t : m > n - m * t → pM P m = t := by
            intro hmgt
            by_contra hne_t
            have hge : t + 1 ≤ pM P m := by omega
            have hle : m * (t + 1) ≤ m * pM P m := Nat.mul_le_mul_left _ hge
            have hsing : m * pM P m ≤ ∑ k ∈ Finset.Icc 1 n, k * pM P k :=
              Finset.single_le_sum (f := fun k => k * pM P k)
                (fun _ _ => Nat.zero_le _) (Finset.mem_Icc.mpr ⟨hm1, hmn⟩)
            rw [hP''] at hsing
            have : m * (t + 1) = m * t + m := by ring
            omega
          have hsub_sum :
              ∑ k ∈ Finset.Icc 1 (n - m * t),
                (if k = m then m * (pM P m - t) else k * pM P k) =
              ∑ k ∈ Finset.Icc 1 n,
                (if k = m then m * (pM P m - t) else k * pM P k) := by
            have hsub : Finset.Icc 1 (n - m * t) ⊆ Finset.Icc 1 n := fun k hk => by
              rcases Finset.mem_Icc.mp hk with ⟨h1, h2⟩; exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
            rw [Finset.sum_subset hsub]
            intro k hk hnot
            rcases Finset.mem_Icc.mp hk with ⟨hk1, hkn⟩
            have hkgt : n - m * t < k := by
              by_contra hle
              exact hnot (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
            by_cases hkm : k = m
            · subst hkm; simp [hmeq_t hkgt]
            · simp [hkm, hhi_zero k hk hkgt hkm]
          have hdirect :
              ∑ k : Fin (n - m * t + 1),
                k.val * (if k.val = m then P.mult ⟨m, by omega⟩ - t else P.mult ⟨k.val, by omega⟩) =
              ∑ k ∈ Finset.Icc 1 (n - m * t),
                (if k = m then m * (pM P m - t) else k * pM P k) := by
            have h1 :
                ∑ k : Fin (n - m * t + 1),
                  k.val * (if k.val = m then P.mult ⟨m, by omega⟩ - t else P.mult ⟨k.val, by omega⟩) =
                ∑ k ∈ Finset.range (n - m * t + 1),
                  (if k = m then m * (pM P m - t) else k * pM P k) := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun k => if k = m then m * (pM P m - t) else k * pM P k)
                (n - m * t + 1)]
              refine Finset.sum_congr rfl fun k _ => ?_
              by_cases hkm : k.val = m
              · rw [if_pos hkm, if_pos hkm, hpM_eq P m (by omega), hkm]
              · rw [if_neg hkm, if_neg hkm, hpM_eq P k.val (by omega)]
            rw [h1, Finset.sum_range_succ']
            simp only [zero_mul]
            have hzero0 : (if (0 : ℕ) = m then m * (pM P m - t) else 0) = 0 := by
              rw [if_neg (by omega)]
            rw [hzero0, add_zero]
            have hIcc : Finset.Icc 1 (n - m * t) = (Finset.range (n - m * t)).image (fun a => a + 1) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
              · rintro ⟨a, ha, rfl⟩; omega
            rw [hIcc, Finset.sum_image (by intro a _ b _ hab; dsimp only at hab; omega)]
          rw [hdirect, hsub_sum]
          have hm_mem : m ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hm1, hmn⟩
          rw [← Finset.add_sum_erase (Finset.Icc 1 n) _ hm_mem, if_pos rfl]
          have hP_split := Finset.add_sum_erase (Finset.Icc 1 n)
            (fun k => k * pM P k) hm_mem
          rw [hP''] at hP_split
          have her : ∑ x ∈ (Finset.Icc 1 n).erase m,
              (if x = m then m * (pM P m - t) else x * pM P x) =
              ∑ x ∈ (Finset.Icc 1 n).erase m, x * pM P x := by
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [if_neg (Finset.mem_erase.mp hx).1]
          rw [her]
          have hm_eq : m * (pM P m - t) + m * t = m * pM P m := by
            rw [← Nat.mul_add, Nat.sub_add_cancel ht_mem]
          omega })
    ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro P₁ hP₁ P₂ hP₂ heq
    have ht₁ := (Finset.mem_filter.mp hP₁).2
    have ht₂ := (Finset.mem_filter.mp hP₂).2
    have hhi : ∀ (P : IntPartition n), t ≤ P.mult ⟨m, by omega⟩ →
        ∀ k : Fin (n + 1), n - m * t < k.val → k.val ≠ m → P.mult k = 0 := by
      intro P hPt k hkgt hkne
      by_contra hne0
      have h1 : 1 ≤ P.mult k := Nat.pos_of_ne_zero hne0
      have hne_fin : k ≠ ⟨m, by omega⟩ := fun h => hkne (congrArg Fin.val h)
      have hsum_le : k.val * P.mult k + m * P.mult ⟨m, by omega⟩ ≤
          ∑ i : Fin (n + 1), i.val * P.mult i := by
        have hp : ({k, ⟨m, by omega⟩} : Finset (Fin (n + 1))) ⊆ Finset.univ := Finset.subset_univ _
        have hs := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun i : Fin (n + 1) => i.val * P.mult i) hp (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hne_fin] at hs
      rw [P.sum_eq] at hsum_le
      have hk_le : k.val ≤ k.val * P.mult k := Nat.le_mul_of_pos_right _ h1
      have hm_le : m * t ≤ m * P.mult ⟨m, by omega⟩ := Nat.mul_le_mul_left _ hPt
      omega
    have hm_hi : ∀ (P : IntPartition n), t ≤ P.mult ⟨m, by omega⟩ →
        n - m * t < m → P.mult ⟨m, by omega⟩ = t := by
      intro P hPt hmgt
      by_contra hne_t
      have hge : t + 1 ≤ P.mult ⟨m, by omega⟩ := by omega
      have hle : m * (t + 1) ≤ m * P.mult ⟨m, by omega⟩ := Nat.mul_le_mul_left _ hge
      have hs : m * P.mult ⟨m, by omega⟩ ≤ ∑ i : Fin (n + 1), i.val * P.mult i :=
        Finset.single_le_sum (f := fun i : Fin (n + 1) => i.val * P.mult i)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨m, by omega⟩)
      rw [P.sum_eq] at hs
      have : m * (t + 1) = m * t + m := by ring
      omega
    ext k
    by_cases hkm : k.val = m
    · have hkfin : k = ⟨m, by omega⟩ := Fin.ext hkm
      rw [hkfin]
      by_cases hle : m ≤ n - m * t
      · have hq := congrArg (fun R : IntPartition (n - m * t) => R.mult ⟨m, by omega⟩) heq
        dsimp only at hq
        rw [if_pos rfl, if_pos rfl] at hq
        omega
      · rw [hm_hi P₁ ht₁ (by omega), hm_hi P₂ ht₂ (by omega)]
    · by_cases hle : k.val ≤ n - m * t
      · have hq := congrArg (fun R : IntPartition (n - m * t) => R.mult ⟨k.val, by omega⟩) heq
        dsimp only at hq
        rw [if_neg hkm, if_neg hkm] at hq
        have hkfin : (⟨k.val, by omega⟩ : Fin (n + 1)) = k := Fin.ext rfl
        rwa [hkfin] at hq
      · rw [hhi P₁ ht₁ k (by omega) hkm, hhi P₂ ht₂ k (by omega) hkm]
  · intro Q _
    let P : IntPartition n :=
      { mult := fun k =>
          if k.val = m then
            (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
          else
            if h : k.val < n - m * t + 1 then Q.mult ⟨k.val, h⟩ else 0
        mult_zero := by simp [show (0 : ℕ) ≠ m by omega, Q.mult_zero]
        sum_eq := by
          have hQ := Q.sum_eq
          have hrange : ∀ (N : ℕ) (g : Fin (N + 1) → ℕ),
              ∑ k : Fin (N + 1), k.val * g k =
                ∑ k ∈ Finset.Icc 1 N, if hk : k < N + 1 then k * g ⟨k, hk⟩ else 0 := by
            intro N g
            have h1 : ∑ k : Fin (N + 1), k.val * g k =
                ∑ k ∈ Finset.range (N + 1), if hk : k < N + 1 then k * g ⟨k, hk⟩ else 0 := by
              rw [← Fin.sum_univ_eq_sum_range
                (fun k => if hk : k < N + 1 then k * g ⟨k, hk⟩ else 0) (N + 1)]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [dif_pos k.isLt]
            rw [h1, Finset.sum_range_succ']
            simp only [dif_pos (Nat.succ_pos N), zero_mul, add_zero]
            have hIcc : Finset.Icc 1 N = (Finset.range N).image (fun a => a + 1) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
              · rintro ⟨a, ha, rfl⟩; omega
            rw [hIcc, Finset.sum_image (by intro a _ b _ hab; dsimp only at hab; omega)]
          have hQ' : ∑ k ∈ Finset.Icc 1 (n - m * t), k *
              (if hk : k < n - m * t + 1 then Q.mult ⟨k, hk⟩ else 0) = n - m * t := by
            have h1 := intPartition_sum_Icc Q
            exact h1
          have hdirect :
              ∑ k : Fin (n + 1),
                k.val * (if k.val = m then
                  (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                else if h : k.val < n - m * t + 1 then Q.mult ⟨k.val, h⟩ else 0) =
              ∑ k ∈ Finset.Icc 1 n,
                (if hk : k < n + 1 then
                  k * (if k = m then
                    (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                  else if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0)
                else 0) := by
            have h1 :
                ∑ k : Fin (n + 1),
                  k.val * (if k.val = m then
                    (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                  else if h : k.val < n - m * t + 1 then Q.mult ⟨k.val, h⟩ else 0) =
                ∑ k ∈ Finset.range (n + 1),
                  if hk : k < n + 1 then
                    k * (if k = m then
                      (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                    else if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0)
                  else 0 := by
              rw [← Fin.sum_univ_eq_sum_range (fun k =>
                if hk : k < n + 1 then
                  k * (if k = m then
                    (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                  else if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0)
                else 0) (n + 1)]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [dif_pos k.isLt]
            rw [h1, Finset.sum_range_succ']
            simp only [dif_pos (Nat.succ_pos n), zero_mul, add_zero]
            have hIcc : Finset.Icc 1 n = (Finset.range n).image (fun a => a + 1) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
              constructor
              · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
              · rintro ⟨a, ha, rfl⟩; omega
            rw [hIcc, Finset.sum_image (by intro a _ b _ hab; dsimp only at hab; omega)]
          rw [hdirect]
          have hIcc_split :
              ∑ k ∈ Finset.Icc 1 n,
                (if hk : k < n + 1 then
                  k * (if k = m then
                        (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                      else if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0)
                else 0) =
              m * t + ∑ k ∈ Finset.Icc 1 (n - m * t), k *
                (if hk : k < n - m * t + 1 then Q.mult ⟨k, hk⟩ else 0) := by
            have h1 : ∑ k ∈ Finset.Icc 1 n,
                (if hk : k < n + 1 then
                  k * (if k = m then
                        (if h : m < n - m * t + 1 then Q.mult ⟨m, h⟩ else 0) + t
                      else if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0)
                else 0) =
                (∑ k ∈ Finset.Icc 1 n,
                  k * (if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0)) +
                (∑ k ∈ Finset.Icc 1 n, if k = m then m * t else 0) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun k hk => ?_
              have hk_lt : k < n + 1 := by have := (Finset.mem_Icc.mp hk).2; omega
              rw [dif_pos hk_lt]
              by_cases hkm : k = m
              · subst hkm
                rw [if_pos rfl, if_pos rfl]
                ring
              · rw [if_neg hkm, if_neg hkm, add_zero]
            rw [h1]
            have hm_sum : ∑ k ∈ Finset.Icc 1 n, (if k = m then m * t else 0) = m * t := by
              rw [Finset.sum_eq_single m]
              · simp
              · intro k _ hk; rw [if_neg hk]
              · intro hnot; exfalso; exact hnot (Finset.mem_Icc.mpr ⟨hm1, hmn⟩)
            have hcut : ∑ k ∈ Finset.Icc 1 n,
                k * (if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0) =
                ∑ k ∈ Finset.Icc 1 (n - m * t),
                  k * (if h : k < n - m * t + 1 then Q.mult ⟨k, h⟩ else 0) := by
              have hsub : Finset.Icc 1 (n - m * t) ⊆ Finset.Icc 1 n := fun k hk => by
                rcases Finset.mem_Icc.mp hk with ⟨h1, h2⟩; exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
              rw [← Finset.sum_subset hsub]
              intro k hk hnot
              rcases Finset.mem_Icc.mp hk with ⟨hk1, _⟩
              have hkgt : ¬ k < n - m * t + 1 := by
                intro hlt
                exact hnot (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
              simp [hkgt]
            rw [hm_sum, hcut, add_comm]
          rw [hIcc_split, hQ']
          omega }
    refine ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ P, ?_⟩, ?_⟩
    · dsimp only [P]; rw [if_pos rfl]; omega
    · ext k
      dsimp only [P]
      by_cases hkm : k.val = m
      · rw [if_pos rfl, if_pos hkm, dif_pos (by omega)]
        have hq_eq : Q.mult ⟨m, by omega⟩ = Q.mult k := congrArg Q.mult (Fin.ext hkm.symm)
        rw [hq_eq]
        omega
      · rw [if_neg hkm, if_neg hkm, dif_pos k.isLt]

/-- **Divisor-Weighted Partition Recurrence:**
`n * p(n) = ∑_{t=1}^n ∑_{m=1}^{⌊n/t⌋} m * p(n - m * t)`. -/
theorem partitionCount_mul_eq_divisor_sum (n : ℕ) :
    n * partitionCount n =
      ∑ t ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 (n / t), m * partitionCount (n - m * t) := by
  let pM : IntPartition n → ℕ → ℕ := fun P m =>
    if hm : m < n + 1 then P.mult ⟨m, hm⟩ else 0
  have h1 : n * partitionCount n =
      ∑ m ∈ Finset.Icc 1 n, m * ∑ P : IntPartition n, pM P m := by
    have hsumP : ∑ _P : IntPartition n, n = n * partitionCount n := by
      simp [Finset.sum_const, partitionCount, mul_comm]
    rw [← hsumP]
    have hP_expand : ∀ P : IntPartition n,
        ∑ m ∈ Finset.Icc 1 n, m * pM P m = n :=
      fun P => intPartition_sum_Icc P
    calc ∑ _P : IntPartition n, n
        = ∑ P : IntPartition n, ∑ m ∈ Finset.Icc 1 n, m * pM P m := by
          refine Finset.sum_congr rfl fun P _ => (hP_expand P).symm
      _ = ∑ m ∈ Finset.Icc 1 n, ∑ P : IntPartition n, m * pM P m :=
          Finset.sum_comm
      _ = ∑ m ∈ Finset.Icc 1 n, m * ∑ P : IntPartition n, pM P m := by
          refine Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
  have h2 : ∀ m ∈ Finset.Icc 1 n,
      ∑ P : IntPartition n, pM P m =
        ∑ t ∈ Finset.Icc 1 (n / m), partitionCount (n - m * t) := by
    intro m hm
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmn⟩
    have hm_lt : m < n + 1 := by omega
    have hpM_m : ∀ P : IntPartition n, pM P m = P.mult ⟨m, hm_lt⟩ := fun P => dif_pos hm_lt
    have hP_le : ∀ P : IntPartition n, pM P m ≤ n / m := by
      intro P
      rw [hpM_m P]
      have hle : m * P.mult ⟨m, hm_lt⟩ ≤ ∑ j : Fin (n + 1), j.val * P.mult j :=
        Finset.single_le_sum (f := fun j : Fin (n + 1) => j.val * P.mult j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨m, hm_lt⟩)
      rw [P.sum_eq] at hle
      exact (Nat.le_div_iff_mul_le hm1).mpr (by rw [mul_comm]; exact hle)
    have hsplit : ∀ P : IntPartition n,
        pM P m = ∑ t ∈ Finset.Icc 1 (n / m), if t ≤ pM P m then 1 else 0 := by
      intro P
      have hle := hP_le P
      have hflt : (Finset.Icc 1 (n / m)).filter (fun t => t ≤ pM P m) =
          Finset.Icc 1 (pM P m) := by
        ext t; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [← Finset.sum_filter, hflt, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
      omega
    calc ∑ P : IntPartition n, pM P m
        = ∑ P : IntPartition n, ∑ t ∈ Finset.Icc 1 (n / m),
            if t ≤ pM P m then 1 else 0 := by
          refine Finset.sum_congr rfl fun P _ => hsplit P
      _ = ∑ t ∈ Finset.Icc 1 (n / m), ∑ P : IntPartition n,
            if t ≤ pM P m then 1 else 0 := Finset.sum_comm
      _ = ∑ t ∈ Finset.Icc 1 (n / m),
            (Finset.univ.filter fun P : IntPartition n => t ≤ pM P m).card := by
          refine Finset.sum_congr rfl fun t _ => by rw [Finset.card_filter]
      _ = ∑ t ∈ Finset.Icc 1 (n / m), partitionCount (n - m * t) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          rcases Finset.mem_Icc.mp ht with ⟨ht1, htn⟩
          have hmt : m * t ≤ n := by
            rw [mul_comm]
            exact (Nat.le_div_iff_mul_le hm1).mp htn
          have hflt_eq :
              (Finset.univ.filter fun P : IntPartition n => t ≤ pM P m) =
              (Finset.univ.filter fun P : IntPartition n => t ≤ P.mult ⟨m, hm_lt⟩) := by
            ext P
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpM_m P]
          rw [hflt_eq]
          exact card_intPartition_ge_eq hm1 hmn ht1 hmt
  rw [h1]
  have hswap1 :
      ∑ m ∈ Finset.Icc 1 n, m * ∑ P : IntPartition n, pM P m =
      ∑ m ∈ Finset.Icc 1 n, ∑ t ∈ Finset.Icc 1 (n / m), m * partitionCount (n - m * t) := by
    refine Finset.sum_congr rfl fun m hm => by rw [h2 m hm, Finset.mul_sum]
  rw [hswap1]
  let S := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun mt => mt.1 * mt.2 ≤ n)
  have hS1 : ∑ m ∈ Finset.Icc 1 n, ∑ t ∈ Finset.Icc 1 (n / m), m * partitionCount (n - m * t) =
      ∑ mt ∈ S, mt.1 * partitionCount (n - mt.1 * mt.2) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hsub : Finset.Icc 1 (n / m) ⊆ Finset.Icc 1 n := fun t ht => by
      rcases Finset.mem_Icc.mp ht with ⟨ht1, htm⟩
      exact Finset.mem_Icc.mpr ⟨ht1, le_trans htm (Nat.div_le_self n m)⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun t ht => ?_
      have hmt : m * t ≤ n := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hm1).mp (Finset.mem_Icc.mp ht).2
      rw [if_pos hmt]
    · intro t ht hnot
      rcases Finset.mem_Icc.mp ht with ⟨ht1, _⟩
      have hgt : ¬ m * t ≤ n := by
        intro hmt
        exact hnot (Finset.mem_Icc.mpr ⟨ht1, (Nat.le_div_iff_mul_le hm1).mpr (by rw [mul_comm]; exact hmt)⟩)
      rw [if_neg hgt]
  have hS2 : ∑ t ∈ Finset.Icc 1 n, ∑ m ∈ Finset.Icc 1 (n / t), m * partitionCount (n - m * t) =
      ∑ mt ∈ S, mt.1 * partitionCount (n - mt.1 * mt.2) := by
    rw [Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht1 := (Finset.mem_Icc.mp ht).1
    have hsub : Finset.Icc 1 (n / t) ⊆ Finset.Icc 1 n := fun m hm => by
      rcases Finset.mem_Icc.mp hm with ⟨hm1, hmt⟩
      exact Finset.mem_Icc.mpr ⟨hm1, le_trans hmt (Nat.div_le_self n t)⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hmt : m * t ≤ n := (Nat.le_div_iff_mul_le ht1).mp (Finset.mem_Icc.mp hm).2
      rw [if_pos hmt]
    · intro m hm hnot
      rcases Finset.mem_Icc.mp hm with ⟨hm1, _⟩
      have hgt : ¬ m * t ≤ n := by
        intro hmt
        exact hnot (Finset.mem_Icc.mpr ⟨hm1, (Nat.le_div_iff_mul_le ht1).mpr hmt⟩)
      rw [if_neg hgt]
  rw [hS1, hS2]

private lemma exp_add_exp_neg_sub_two_ge_sq {a : ℝ} (ha : 0 ≤ a) :
    a ^ 2 ≤ Real.exp a + Real.exp (-a) - 2 := by
  let f1 : ℝ → ℝ := fun x => Real.exp x - Real.exp (-x) - 2 * x
  have hf1_deriv : ∀ x : ℝ, HasDerivAt f1 (Real.exp x + Real.exp (-x) - 2) x := by
    intro x
    have h1 := Real.hasDerivAt_exp x
    have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have h3 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have hd := (h1.fun_sub h2).fun_sub h3
    change HasDerivAt (fun t : ℝ => Real.exp t - Real.exp (-t) - 2 * t)
      (Real.exp x + Real.exp (-x) - 2) x
    rwa [show Real.exp x - Real.exp (-x) * -1 - 2 = Real.exp x + Real.exp (-x) - 2 by ring] at hd
  have hf1_nonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ f1 x := by
    intro x hx
    have hmono : Monotone f1 := monotone_of_deriv_nonneg
      (fun y => (hf1_deriv y).differentiableAt)
      (fun y => by
        rw [(hf1_deriv y).deriv]
        have hsq : Real.exp y + Real.exp (-y) - 2 =
            (Real.exp (y / 2) - Real.exp (-(y / 2))) ^ 2 := by
          have hexp1 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
            rw [← Real.exp_add]; ring_nf
          have hexp2 : Real.exp (-y) = Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
            rw [← Real.exp_add]; ring_nf
          have hexp0 : Real.exp (y / 2) * Real.exp (-(y / 2)) = 1 := by
            rw [← Real.exp_add]; simp
          linarith [sq_sub_sq (Real.exp (y / 2)) (Real.exp (-(y / 2)))]
        rw [hsq]
        exact sq_nonneg _)
    have h0 : f1 0 = 0 := by simp [f1]
    rw [← h0]
    exact hmono hx
  let f2 : ℝ → ℝ := fun x => Real.exp x + Real.exp (-x) - 2 - x ^ 2
  have hf2_deriv : ∀ x : ℝ, HasDerivAt f2 (f1 x) x := by
    intro x
    have h1 := Real.hasDerivAt_exp x
    have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have h3 : HasDerivAt (fun _t : ℝ => (2 : ℝ)) 0 x := hasDerivAt_const x 2
    have h4 := hasDerivAt_pow 2 x
    have hd := ((h1.fun_add h2).fun_sub h3).fun_sub h4
    change HasDerivAt (fun t : ℝ => Real.exp t + Real.exp (-t) - 2 - t ^ 2) (f1 x) x
    rw [show Real.exp x + Real.exp (-x) * -1 - 0 - ((2 : ℕ) : ℝ) * x ^ (2 - 1) = f1 x by
      simp only [f1, Nat.reduceSub, Nat.cast_ofNat]
      ring] at hd
    exact hd
  have hmono2 : MonotoneOn f2 (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hf2_deriv x).differentiableAt.continuousAt.continuousWithinAt)
      (fun x _ => (hf2_deriv x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hf2_deriv x).deriv]
        exact hf1_nonneg x (le_of_lt (by simpa [interior_Ici] using hx)))
  have h0 : f2 0 = 0 := by simp [f2]; norm_num
  have hle := hmono2 (Set.mem_Ici.mpr (le_refl (0 : ℝ))) ha ha
  rw [h0] at hle
  dsimp only [f2] at hle
  linarith [hle]

private lemma sum_nat_mul_exp_neg_le {α : ℝ} (hα : 0 < α) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * Real.exp (-α * m) ≤ 1 / α ^ 2 := by
  let x : ℝ := Real.exp (-α)
  have hx_pos : 0 < x := Real.exp_pos (-α)
  have hx_lt1 : x < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1x_pos : 0 < 1 - x := by linarith
  have hsum_geom : ∑ m ∈ Finset.Icc 1 M, x ^ m ≤ x / (1 - x) := by
    have hmul : (1 - x) * ∑ m ∈ Finset.Icc 1 M, x ^ m = x - x ^ (M + 1) := by
      rw [Finset.mul_sum]
      have hIcc : Finset.Icc 1 M = (Finset.range M).image Nat.succ := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
      have htele := Finset.sum_range_sub' (fun k => x ^ (k + 1)) M
      have hcong : ∑ i ∈ Finset.range M, (1 - x) * x ^ (i + 1) =
          ∑ i ∈ Finset.range M, (x ^ (i + 1) - x ^ (i + 1 + 1)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_succ]; ring
      rw [hcong, htele]
      ring
    have hxpow_nonneg : 0 ≤ x ^ (M + 1) := pow_nonneg hx_pos.le _
    rw [le_div_iff₀ h1x_pos]
    linarith
  have hsum_arith : (1 - x) * ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * x ^ m ≤ ∑ m ∈ Finset.Icc 1 M, x ^ m := by
    rw [Finset.mul_sum]
    have hrewrite : ∑ m ∈ Finset.Icc 1 M, (1 - x) * ((m : ℝ) * x ^ m) =
        ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * x ^ m - ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * x ^ (m + 1) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [pow_succ]; ring
    rw [hrewrite]
    cases M with
    | zero => simp
    | succ M' =>
      have hIcc : Finset.Icc 1 (M' + 1) = (Finset.range (M' + 1)).image Nat.succ := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨a, ha, rfl⟩; omega
      have hs1 : ∑ m ∈ Finset.Icc 1 (M' + 1), (m : ℝ) * x ^ m =
          ∑ m ∈ Finset.range (M' + 1), ((m : ℝ) + 1) * x ^ (m + 1) := by
        rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
        refine Finset.sum_congr rfl fun m _ => by simp
      have hshift_eq : ∀ N : ℕ,
          ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * x ^ (m + 2) =
            ∑ m ∈ Finset.range (N + 1), (m : ℝ) * x ^ (m + 1) + (N + 1 : ℝ) * x ^ (N + 2) := by
        intro N
        induction N with
        | zero => simp
        | succ N' ihN =>
          rw [Finset.sum_range_succ (fun m => ((m : ℝ) + 1) * x ^ (m + 2)) (N' + 1), ihN]
          conv_rhs => rw [Finset.sum_range_succ (fun m => (m : ℝ) * x ^ (m + 1)) (N' + 1)]
          push_cast
          ring
      have hs2 : ∑ m ∈ Finset.Icc 1 (M' + 1), (m : ℝ) * x ^ (m + 1) =
          ∑ m ∈ Finset.range (M' + 1), (m : ℝ) * x ^ (m + 1) + (M' + 1 : ℝ) * x ^ (M' + 2) := by
        rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
        simpa [Nat.cast_add, Nat.cast_one] using hshift_eq M'
      have hs3 : ∑ m ∈ Finset.Icc 1 (M' + 1), x ^ m =
          ∑ m ∈ Finset.range (M' + 1), x ^ (m + 1) := by
        rw [hIcc, Finset.sum_image (by intro a _ b _ hab; omega)]
      have hdiff :
          ∑ m ∈ Finset.range (M' + 1), ((m : ℝ) + 1) * x ^ (m + 1) -
            ∑ m ∈ Finset.range (M' + 1), (m : ℝ) * x ^ (m + 1) =
          ∑ m ∈ Finset.range (M' + 1), x ^ (m + 1) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ => by ring
      have hlast_nonneg : 0 ≤ (M' + 1 : ℝ) * x ^ (M' + 2) := by positivity
      linarith [hs1, hs2, hs3, hdiff, hlast_nonneg]
  have hmain : ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * Real.exp (-α * m) ≤ x / (1 - x) ^ 2 := by
    have hpow_eq : ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * Real.exp (-α * m) =
        ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * x ^ m := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show x ^ m = Real.exp (-α * m) by simp [x, ← Real.exp_nat_mul]; ring_nf]
    rw [hpow_eq, le_div_iff₀ (sq_pos_of_pos h1x_pos)]
    calc (∑ m ∈ Finset.Icc 1 M, (m : ℝ) * x ^ m) * (1 - x) ^ 2
        = ((1 - x) * ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * x ^ m) * (1 - x) := by ring
      _ ≤ (∑ m ∈ Finset.Icc 1 M, x ^ m) * (1 - x) :=
          mul_le_mul_of_nonneg_right hsum_arith h1x_pos.le
      _ ≤ (x / (1 - x)) * (1 - x) :=
          mul_le_mul_of_nonneg_right hsum_geom h1x_pos.le
      _ = x := div_mul_cancel₀ x h1x_pos.ne'
  have hden : x * α ^ 2 ≤ (1 - x) ^ 2 := by
    have hexp_inv : x⁻¹ = Real.exp α := by simp [x, Real.exp_neg]
    have hge := exp_add_exp_neg_sub_two_ge_sq hα.le
    have hmul : α ^ 2 ≤ Real.exp α + Real.exp (-α) - 2 := hge
    have heq : (Real.exp α + Real.exp (-α) - 2) * x = (1 - x) ^ 2 := by
      rw [← hexp_inv]
      have hxx : x⁻¹ * x = 1 := inv_mul_cancel₀ hx_pos.ne'
      nlinarith [mul_comm x⁻¹ x]
    calc x * α ^ 2 = α ^ 2 * x := by ring
      _ ≤ (Real.exp α + Real.exp (-α) - 2) * x :=
          mul_le_mul_of_nonneg_right hmul hx_pos.le
      _ = (1 - x) ^ 2 := heq
  calc ∑ m ∈ Finset.Icc 1 M, (m : ℝ) * Real.exp (-α * m)
      ≤ x / (1 - x) ^ 2 := hmain
    _ ≤ 1 / α ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos h1x_pos) (sq_pos_of_pos hα), one_mul]
      exact hden

/-- **Erdős (1942) Elementary Partition Upper Bound:**
For every `n : ℕ`, `p(n) ≤ exp(π * √(2 * n / 3))`. -/
theorem erdos_partition_upper_bound (n : ℕ) :
    (partitionCount n : ℝ) ≤ Real.exp (Real.pi * Real.sqrt (2 * (n : ℝ) / 3)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have h0 : partitionCount 0 = 1 := by
        unfold partitionCount
        rw [Fintype.card_eq_one_iff]
        refine ⟨⟨fun _ => 0, rfl, by simp⟩, fun P => ?_⟩
        ext k
        have hk : k = 0 := Fin.ext (by omega)
        rw [hk, P.mult_zero]
      simp [h0]
    | succ n' =>
      set N := n' + 1
      have hN_pos : (0 : ℝ) < N := by positivity
      let c : ℝ := Real.pi * Real.sqrt (2 / 3)
      have hc_pos : 0 < c := by positivity
      have hc_sq : c ^ 2 = 2 * Real.pi ^ 2 / 3 := by
        dsimp only [c]
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        ring
      have harg : Real.pi * Real.sqrt (2 * (N : ℝ) / 3) = c * Real.sqrt (N : ℝ) := by
        dsimp only [c]
        rw [mul_assoc, ← Real.sqrt_mul (by norm_num)]
        ring_nf
      rw [harg]
      have hrec : ((N : ℝ) * (partitionCount N : ℝ)) =
          ∑ t ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / t),
            (m : ℝ) * (partitionCount (N - m * t) : ℝ) := by
        have hnat := partitionCount_mul_eq_divisor_sum N
        have hcast := congrArg (Nat.cast (R := ℝ)) hnat
        push_cast at hcast
        exact hcast
      have hsqrt_conc : ∀ a : ℝ, 0 ≤ a → a ≤ N →
          Real.sqrt ((N : ℝ) - a) ≤ Real.sqrt N - a / (2 * Real.sqrt N) := by
        intro a _ haN
        have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN_pos
        have hrhs_nonneg : 0 ≤ Real.sqrt N - a / (2 * Real.sqrt N) := by
          rw [sub_nonneg, div_le_iff₀ (by positivity)]
          calc a ≤ N := haN
            _ = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN_pos.le).symm
            _ ≤ 2 * (Real.sqrt N * Real.sqrt N) := by linarith [mul_nonneg hsqrtN.le hsqrtN.le]
            _ = Real.sqrt N * (2 * Real.sqrt N) := by ring
        rw [← Real.sqrt_sq hrhs_nonneg]
        apply Real.sqrt_le_sqrt
        have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN_pos.le
        have hsq_pos : 0 ≤ (a / (2 * Real.sqrt N)) ^ 2 := sq_nonneg _
        have hcross : 2 * Real.sqrt N * (a / (2 * Real.sqrt N)) = a := by
          field_simp [hsqrtN.ne']
        nlinarith [sq_nonneg (Real.sqrt N - a / (2 * Real.sqrt N)), hsqN, hsq_pos, hcross]
      have hterm_le : ∀ t ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Icc 1 (N / t), (m : ℝ) * (partitionCount (N - m * t) : ℝ) ≤
            Real.exp (c * Real.sqrt N) * (4 * (N : ℝ) / (c ^ 2 * (t : ℝ) ^ 2)) := by
        intro t ht
        rcases Finset.mem_Icc.mp ht with ⟨ht1, htN⟩
        have ht_pos : (0 : ℝ) < t := by positivity
        let α : ℝ := c * t / (2 * Real.sqrt N)
        have hα_pos : 0 < α := by
          have := Real.sqrt_pos.mpr hN_pos
          positivity
        have hbound_m : ∀ m ∈ Finset.Icc 1 (N / t),
            (m : ℝ) * (partitionCount (N - m * t) : ℝ) ≤
              Real.exp (c * Real.sqrt N) * ((m : ℝ) * Real.exp (-α * m)) := by
          intro m hm
          rcases Finset.mem_Icc.mp hm with ⟨hm1, hmt⟩
          have hmt_le : m * t ≤ N := (Nat.le_div_iff_mul_le ht1).mp hmt
          have hmt_pos : 1 ≤ m * t := Nat.mul_pos hm1 ht1
          have hltN : N - m * t < N := by omega
          have hIH := ih (N - m * t) hltN
          have harg_mt : Real.pi * Real.sqrt (2 * ((N - m * t : ℕ) : ℝ) / 3) =
              c * Real.sqrt ((N : ℝ) - (m : ℝ) * t) := by
            dsimp only [c]
            rw [mul_assoc, ← Real.sqrt_mul (by norm_num), Nat.cast_sub hmt_le, Nat.cast_mul]
            ring_nf
          rw [harg_mt] at hIH
          have hsq := hsqrt_conc ((m : ℝ) * t) (by positivity) (by exact_mod_cast hmt_le)
          have hexp_le : Real.exp (c * Real.sqrt ((N : ℝ) - (m : ℝ) * t)) ≤
              Real.exp (c * Real.sqrt N) * Real.exp (-α * m) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hlin : c * (Real.sqrt N - (m : ℝ) * t / (2 * Real.sqrt N)) =
                c * Real.sqrt N + (-α * m) := by
              dsimp only [α]
              ring
            calc c * Real.sqrt ((N : ℝ) - (m : ℝ) * t)
                ≤ c * (Real.sqrt N - (m : ℝ) * t / (2 * Real.sqrt N)) :=
                  mul_le_mul_of_nonneg_left hsq hc_pos.le
              _ = c * Real.sqrt N + (-α * m) := hlin
          have hcomb := le_trans hIH hexp_le
          calc (m : ℝ) * (partitionCount (N - m * t) : ℝ)
              ≤ (m : ℝ) * (Real.exp (c * Real.sqrt N) * Real.exp (-α * m)) :=
                mul_le_mul_of_nonneg_left hcomb (by positivity)
            _ = Real.exp (c * Real.sqrt N) * ((m : ℝ) * Real.exp (-α * m)) := by ring
        calc ∑ m ∈ Finset.Icc 1 (N / t), (m : ℝ) * (partitionCount (N - m * t) : ℝ)
            ≤ ∑ m ∈ Finset.Icc 1 (N / t),
                Real.exp (c * Real.sqrt N) * ((m : ℝ) * Real.exp (-α * m)) :=
              Finset.sum_le_sum hbound_m
          _ = Real.exp (c * Real.sqrt N) *
                ∑ m ∈ Finset.Icc 1 (N / t), (m : ℝ) * Real.exp (-α * m) := by
              rw [← Finset.mul_sum]
          _ ≤ Real.exp (c * Real.sqrt N) * (1 / α ^ 2) :=
              mul_le_mul_of_nonneg_left (sum_nat_mul_exp_neg_le hα_pos (N / t))
                (Real.exp_pos _).le
          _ = Real.exp (c * Real.sqrt N) * (4 * (N : ℝ) / (c ^ 2 * (t : ℝ) ^ 2)) := by
              congr 1
              dsimp only [α]
              rw [div_pow, one_div, inv_div, mul_pow, mul_pow, Real.sq_sqrt hN_pos.le]
              ring
      have hzeta : ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (t : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
        calc ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (t : ℝ) ^ 2
            ≤ ∑' t : ℕ, (1 : ℝ) / (t : ℝ) ^ 2 :=
              Summable.sum_le_tsum (Finset.Icc 1 N) (fun _ _ => by positivity)
                hasSum_zeta_two.summable
          _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
      have hN_mul : (N : ℝ) * (partitionCount N : ℝ) ≤ (N : ℝ) * Real.exp (c * Real.sqrt N) := by
        calc (N : ℝ) * (partitionCount N : ℝ)
            ≤ ∑ t ∈ Finset.Icc 1 N,
                Real.exp (c * Real.sqrt N) * (4 * (N : ℝ) / (c ^ 2 * (t : ℝ) ^ 2)) := by
              rw [hrec]
              exact Finset.sum_le_sum hterm_le
          _ = Real.exp (c * Real.sqrt N) * (4 * (N : ℝ) / c ^ 2) *
                ∑ t ∈ Finset.Icc 1 N, (1 : ℝ) / (t : ℝ) ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun t _ => by ring
          _ ≤ Real.exp (c * Real.sqrt N) * (4 * (N : ℝ) / c ^ 2) * (Real.pi ^ 2 / 6) := by
              apply mul_le_mul_of_nonneg_left hzeta
              positivity
          _ = (N : ℝ) * Real.exp (c * Real.sqrt N) := by
              rw [hc_sq]
              field_simp
              ring
      exact le_of_mul_le_mul_left hN_mul hN_pos

end Partitions

/-!
## Section 3: Explicit Non-Asymptotic Stirling / Robbins & Central-Binomial Sharp Bounds
-/

section StirlingBounds

private lemma log_one_add_div_one_sub_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t + (2 / 3) * t ^ 3 ≤ Real.log ((1 + t) / (1 - t)) ∧
      Real.log ((1 + t) / (1 - t)) ≤ 2 * t + 2 * t ^ 3 / (3 * (1 - t ^ 2)) := by
  have hdiff_log : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt (fun u => Real.log ((1 + u) / (1 - u))) (2 / (1 - x ^ 2)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x < 1 := hx.2
    have h1p : 1 + x ≠ 0 := by linarith
    have h1m : 1 - x ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun u : ℝ => 1 + u) 1 x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_add (hasDerivAt_id x)
    have hd2 : HasDerivAt (fun u : ℝ => 1 - u) (-1) x := by
      simpa using (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
    have hquot : HasDerivAt (fun u => (1 + u) / (1 - u))
        ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x :=
      hd1.fun_div hd2 h1m
    have hpos : (1 + x) / (1 - x) ≠ 0 := div_ne_zero h1p h1m
    have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx0, hx1]
    have hlog := hquot.log hpos
    convert hlog using 1
    field_simp [h1p, h1m, h1x2]
    ring
  constructor
  · let gL : ℝ → ℝ := fun u => Real.log ((1 + u) / (1 - u)) - (2 * u + (2 / 3) * u ^ 3)
    have hgL_deriv : ∀ x ∈ Set.Ico (0 : ℝ) 1,
        HasDerivAt gL (2 * x ^ 4 / (1 - x ^ 2)) x := by
      intro x hx
      have hdlog := hdiff_log x hx
      have hdpoly : HasDerivAt (fun u : ℝ => 2 * u + (2 / 3) * u ^ 3) (2 + 2 * x ^ 2) x := by
        have h1 : HasDerivAt (fun u : ℝ => 2 * u) 2 x := by
          simpa using (hasDerivAt_id x).const_mul 2
        have h2 : HasDerivAt (fun u : ℝ => (2 / 3 : ℝ) * u ^ 3) (2 * x ^ 2) x := by
          have h2' := (hasDerivAt_pow 3 x).const_mul (2 / 3 : ℝ)
          rwa [show (2 / 3 : ℝ) * (((3 : ℕ) : ℝ) * x ^ (3 - 1)) = 2 * x ^ 2 by
            simp only [Nat.reduceSub, Nat.cast_ofNat]
            ring] at h2'
        exact h1.fun_add h2
      have hsub := hdlog.fun_sub hdpoly
      have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
      have hderiv_eq : 2 / (1 - x ^ 2) - (2 + 2 * x ^ 2) = 2 * x ^ 4 / (1 - x ^ 2) := by
        field_simp [h1x2]
        ring
      change HasDerivAt (fun u => Real.log ((1 + u) / (1 - u)) - (2 * u + (2 / 3) * u ^ 3))
        (2 * x ^ 4 / (1 - x ^ 2)) x
      rwa [hderiv_eq] at hsub
    have hcont : ContinuousOn gL (Set.Icc 0 t) := by
      intro x hx
      have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 ht1⟩
      exact (hgL_deriv x hx').continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ gL (interior (Set.Icc 0 t)) := by
      intro x hx
      have hxI : x ∈ Set.Icc 0 t := interior_subset hx
      have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_lt hxI.2 ht1⟩
      exact (hgL_deriv x hx').differentiableAt.differentiableWithinAt
    have hmono : MonotoneOn gL (Set.Icc 0 t) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont hdiff fun x hx => by
        have hxI : x ∈ Set.Icc 0 t := interior_subset hx
        have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_lt hxI.2 ht1⟩
        rw [(hgL_deriv x hx').deriv]
        have h1x2 : 0 < 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
        positivity
    have hg0 : gL 0 = 0 := by simp [gL]
    have hle := hmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
    rw [hg0] at hle
    dsimp only [gL] at hle
    linarith [hle]
  · let gU : ℝ → ℝ := fun u => (2 * u + 2 * u ^ 3 / (3 * (1 - u ^ 2))) - Real.log ((1 + u) / (1 - u))
    have hgU_deriv : ∀ x ∈ Set.Ico (0 : ℝ) 1,
        HasDerivAt gU ((4 / 3) * x ^ 4 / (1 - x ^ 2) ^ 2) x := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x < 1 := hx.2
      have h1x2 : 1 - x ^ 2 ≠ 0 := by nlinarith
      have hden : 3 * (1 - x ^ 2) ≠ 0 := mul_ne_zero (by norm_num) h1x2
      have hd1 : HasDerivAt (fun u : ℝ => 2 * u) 2 x := by
        simpa using (hasDerivAt_id x).const_mul 2
      have hd_num : HasDerivAt (fun u : ℝ => 2 * u ^ 3) (6 * x ^ 2) x := by
        have h' := (hasDerivAt_pow 3 x).const_mul (2 : ℝ)
        rwa [show (2 : ℝ) * (((3 : ℕ) : ℝ) * x ^ (3 - 1)) = 6 * x ^ 2 by
          simp only [Nat.reduceSub, Nat.cast_ofNat]
          ring] at h'
      have hd_den : HasDerivAt (fun u : ℝ => 3 * (1 - u ^ 2)) (-6 * x) x := by
        have hsq' := (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_pow 2 x)
        have hsq : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (-2 * x) x := by
          rwa [show (0 : ℝ) - ((2 : ℕ) : ℝ) * x ^ (2 - 1) = -2 * x by
            simp only [Nat.reduceSub, Nat.cast_ofNat]
            ring] at hsq'
        have hd3 := hsq.const_mul (3 : ℝ)
        rwa [show (3 : ℝ) * (-2 * x) = -6 * x by ring] at hd3
      have hd_quot := hd_num.fun_div hd_den hden
      have hd_poly := hd1.fun_add hd_quot
      have hd_log := hdiff_log x hx
      have hsub := hd_poly.fun_sub hd_log
      have hderiv_eq :
          (2 + (6 * x ^ 2 * (3 * (1 - x ^ 2)) - 2 * x ^ 3 * (-6 * x)) / (3 * (1 - x ^ 2)) ^ 2) -
            2 / (1 - x ^ 2) =
          (4 / 3) * x ^ 4 / (1 - x ^ 2) ^ 2 := by
        field_simp [h1x2, hden]
        ring
      change HasDerivAt
        (fun u => (2 * u + 2 * u ^ 3 / (3 * (1 - u ^ 2))) - Real.log ((1 + u) / (1 - u)))
        ((4 / 3) * x ^ 4 / (1 - x ^ 2) ^ 2) x
      rwa [hderiv_eq] at hsub
    have hcont : ContinuousOn gU (Set.Icc 0 t) := by
      intro x hx
      have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 ht1⟩
      exact (hgU_deriv x hx').continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ gU (interior (Set.Icc 0 t)) := by
      intro x hx
      have hxI : x ∈ Set.Icc 0 t := interior_subset hx
      have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_lt hxI.2 ht1⟩
      exact (hgU_deriv x hx').differentiableAt.differentiableWithinAt
    have hmono : MonotoneOn gU (Set.Icc 0 t) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hcont hdiff fun x hx => by
        have hxI : x ∈ Set.Icc 0 t := interior_subset hx
        have hx' : x ∈ Set.Ico (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_lt hxI.2 ht1⟩
        rw [(hgU_deriv x hx').deriv]
        positivity
    have hg0 : gU 0 = 0 := by simp [gU]
    have hle := hmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
    rw [hg0] at hle
    dsimp only [gU] at hle
    linarith [hle]

/-- **Robbins Ratio Step Bounds:** For all `n ≥ 1`,
`1 / (12 * n + 1) - 1 / (12 * (n + 1) + 1) ≤ (n + 1/2) * log((n+1)/n) - 1 ≤ 1 / (12 * n) - 1 / (12 * (n + 1))`. -/
theorem robbins_ratio_bounds (n : ℕ) (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ) + 1) - 1 / (12 * ((n : ℝ) + 1) + 1) ≤
        ((n : ℝ) + 1 / 2) * Real.log (((n : ℝ) + 1) / (n : ℝ)) - 1 ∧
      ((n : ℝ) + 1 / 2) * Real.log (((n : ℝ) + 1) / (n : ℝ)) - 1 ≤
        1 / (12 * (n : ℝ)) - 1 / (12 * ((n : ℝ) + 1)) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  let t : ℝ := 1 / (2 * (n : ℝ) + 1)
  have ht_pos : 0 < t := by positivity
  have ht_le : t ≤ 1 / 3 := by
    dsimp only [t]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have ht1 : t < 1 := lt_of_le_of_lt ht_le (by norm_num)
  have hfrac : ((n : ℝ) + 1) / (n : ℝ) = (1 + t) / (1 - t) := by
    dsimp only [t]
    field_simp [hn_pos.ne']
    ring
  have hhalf : (n : ℝ) + 1 / 2 = 1 / (2 * t) := by
    dsimp only [t]
    field_simp
  obtain ⟨hL, hU⟩ := log_one_add_div_one_sub_bounds ht_pos.le ht1
  rw [hfrac, hhalf]
  constructor
  · have hlower_t : t ^ 2 / 3 ≤ 1 / (2 * t) * Real.log ((1 + t) / (1 - t)) - 1 := by
      have hmul : 2 * t * (t ^ 2 / 3 + 1) ≤ Real.log ((1 + t) / (1 - t)) := by
        linarith [hL]
      rw [le_sub_iff_add_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
      linarith [hmul]
    have hcmp : 1 / (12 * (n : ℝ) + 1) - 1 / (12 * ((n : ℝ) + 1) + 1) ≤ t ^ 2 / 3 := by
      dsimp only [t]
      have h12_1 : (0 : ℝ) < 12 * (n : ℝ) + 1 := by positivity
      have h12_2 : (0 : ℝ) < 12 * ((n : ℝ) + 1) + 1 := by positivity
      have h2n1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have heq1 : 1 / (12 * (n : ℝ) + 1) - 1 / (12 * ((n : ℝ) + 1) + 1) =
          12 / ((12 * (n : ℝ) + 1) * (12 * ((n : ℝ) + 1) + 1)) := by
        field_simp [h12_1.ne', h12_2.ne']
        ring
      have heq2 : (1 / (2 * (n : ℝ) + 1)) ^ 2 / 3 = 1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
        field_simp [h2n1.ne']
      rw [heq1, heq2, div_le_div_iff₀ (by positivity) (by positivity)]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    exact le_trans hcmp hlower_t
  · have hupper_t : 1 / (2 * t) * Real.log ((1 + t) / (1 - t)) - 1 ≤ t ^ 2 / (3 * (1 - t ^ 2)) := by
      rw [sub_le_iff_le_add, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      calc Real.log ((1 + t) / (1 - t))
          ≤ 2 * t + 2 * t ^ 3 / (3 * (1 - t ^ 2)) := hU
        _ = (t ^ 2 / (3 * (1 - t ^ 2)) + 1) * (2 * t) := by ring
    have heq_t : t ^ 2 / (3 * (1 - t ^ 2)) =
        1 / (12 * (n : ℝ)) - 1 / (12 * ((n : ℝ) + 1)) := by
      dsimp only [t]
      have h2n1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      have h1m_eq : 1 - (1 / (2 * (n : ℝ) + 1)) ^ 2 =
          4 * (n : ℝ) * ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) ^ 2 := by
        field_simp [h2n1]
        ring
      rw [h1m_eq]
      field_simp [hn_pos.ne', h2n1]
      ring
    linarith [hupper_t, heq_t]

private lemma stirlingSeq_pos {n : ℕ} (hn : 1 ≤ n) : 0 < Stirling.stirlingSeq n := by
  unfold Stirling.stirlingSeq
  have hn_pos : (0 : ℝ) < n := by positivity
  positivity

private lemma stirlingSeq_div_succ {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n / Stirling.stirlingSeq (n + 1)) =
      ((n : ℝ) + 1 / 2) * Real.log (((n : ℝ) + 1) / (n : ℝ)) - 1 := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hratio : Stirling.stirlingSeq n / Stirling.stirlingSeq (n + 1) =
      (((n : ℝ) + 1) / (n : ℝ)) ^ ((n : ℝ) + 1 / 2) / Real.exp 1 := by
    unfold Stirling.stirlingSeq
    rw [Nat.cast_add, Nat.cast_one, hfac]
    have hsqrt_n : 0 < Real.sqrt (2 * (n : ℝ)) := by positivity
    have hsqrt_n1 : 0 < Real.sqrt (2 * ((n : ℝ) + 1)) := by positivity
    have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    have hrpow : (((n : ℝ) + 1) / (n : ℝ)) ^ ((n : ℝ) + 1 / 2) =
        (((n : ℝ) + 1) / (n : ℝ)) ^ (n : ℕ) * Real.sqrt (((n : ℝ) + 1) / (n : ℝ)) := by
      rw [Real.rpow_add (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    have hsqrt_div : Real.sqrt (2 * ((n : ℝ) + 1)) / Real.sqrt (2 * (n : ℝ)) =
        Real.sqrt (((n : ℝ) + 1) / (n : ℝ)) := by
      rw [← Real.sqrt_div (by positivity)]
      congr 1
      field_simp
    rw [hrpow, ← hsqrt_div]
    have hpow_n : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
    have hpow_n1 : (((n : ℝ) + 1) / Real.exp 1) ^ (n + 1) ≠ 0 := by positivity
    rw [div_div_div_eq]
    have hsimp : (n.factorial : ℝ) * (Real.sqrt (2 * ((n : ℝ) + 1)) * (((n : ℝ) + 1) / Real.exp 1) ^ (n + 1)) /
        (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n * (((n : ℝ) + 1) * (n.factorial : ℝ))) =
        (((n : ℝ) + 1) / (n : ℝ)) ^ n * (Real.sqrt (2 * ((n : ℝ) + 1)) / Real.sqrt (2 * (n : ℝ))) / Real.exp 1 := by
      rw [pow_succ, div_pow, div_pow, div_pow]
      field_simp [hfac_pos.ne', hsqrt_n.ne', hsqrt_n1.ne', hn_pos.ne', hn1_pos.ne', hexp_ne]
    exact hsimp
  rw [hratio, Real.log_div (by positivity) (Real.exp_pos 1).ne', Real.log_exp,
      Real.log_rpow (by positivity)]

/-- **Robbins Non-Asymptotic Two-Sided Stirling Sequence Bounds:**
For all `n ≥ 1`,
`√π * exp(1/(12n + 1)) ≤ Stirling.stirlingSeq n ≤ √π * exp(1/(12n))`. -/
theorem stirling_robbins_two_sided (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ) + 1)) ≤ Stirling.stirlingSeq n ∧
      Stirling.stirlingSeq n ≤ Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ))) := by
  let b : ℕ → ℝ := fun k => Stirling.stirlingSeq k * Real.exp (-1 / (12 * (k : ℝ)))
  let c : ℕ → ℝ := fun k => Stirling.stirlingSeq k * Real.exp (-1 / (12 * (k : ℝ) + 1))
  have hb_mono : ∀ k, 1 ≤ k → b k ≤ b (k + 1) := by
    intro k hk
    have hlog_le : Real.log (Stirling.stirlingSeq k / Stirling.stirlingSeq (k + 1)) ≤
        1 / (12 * (k : ℝ)) - 1 / (12 * ((k : ℝ) + 1)) := by
      rw [stirlingSeq_div_succ hk]
      exact (robbins_ratio_bounds k hk).2
    have hdiv_le : Stirling.stirlingSeq k / Stirling.stirlingSeq (k + 1) ≤
        Real.exp (1 / (12 * (k : ℝ)) - 1 / (12 * ((k : ℝ) + 1))) := by
      rw [← Real.exp_log (div_pos (stirlingSeq_pos hk) (stirlingSeq_pos (by omega)))]
      exact Real.exp_le_exp.mpr hlog_le
    have hk_pos : (0 : ℝ) < Stirling.stirlingSeq (k + 1) := stirlingSeq_pos (by omega)
    have hmul := (div_le_iff₀ hk_pos).mp hdiv_le
    dsimp only [b]
    rw [Nat.cast_add, Nat.cast_one]
    have hprod : Real.exp (1 / (12 * (k : ℝ)) - 1 / (12 * ((k : ℝ) + 1))) *
        Real.exp (-1 / (12 * (k : ℝ))) = Real.exp (-1 / (12 * ((k : ℝ) + 1))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Stirling.stirlingSeq k * Real.exp (-1 / (12 * (k : ℝ)))
        ≤ (Real.exp (1 / (12 * (k : ℝ)) - 1 / (12 * ((k : ℝ) + 1))) * Stirling.stirlingSeq (k + 1)) *
            Real.exp (-1 / (12 * (k : ℝ))) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
      _ = Stirling.stirlingSeq (k + 1) * Real.exp (-1 / (12 * ((k : ℝ) + 1))) := by
          rw [mul_right_comm, hprod, mul_comm]
  have hc_anti : ∀ k, 1 ≤ k → c (k + 1) ≤ c k := by
    intro k hk
    have hlog_ge : 1 / (12 * (k : ℝ) + 1) - 1 / (12 * ((k : ℝ) + 1) + 1) ≤
        Real.log (Stirling.stirlingSeq k / Stirling.stirlingSeq (k + 1)) := by
      rw [stirlingSeq_div_succ hk]
      exact (robbins_ratio_bounds k hk).1
    have hdiv_ge : Real.exp (1 / (12 * (k : ℝ) + 1) - 1 / (12 * ((k : ℝ) + 1) + 1)) ≤
        Stirling.stirlingSeq k / Stirling.stirlingSeq (k + 1) := by
      rw [← Real.exp_log (div_pos (stirlingSeq_pos hk) (stirlingSeq_pos (by omega)))]
      exact Real.exp_le_exp.mpr hlog_ge
    have hk_pos : (0 : ℝ) < Stirling.stirlingSeq (k + 1) := stirlingSeq_pos (by omega)
    have hmul := (le_div_iff₀ hk_pos).mp hdiv_ge
    dsimp only [c]
    rw [Nat.cast_add, Nat.cast_one]
    have hprod : Real.exp (-1 / (12 * ((k : ℝ) + 1) + 1)) =
        Real.exp (1 / (12 * (k : ℝ) + 1) - 1 / (12 * ((k : ℝ) + 1) + 1)) *
          Real.exp (-1 / (12 * (k : ℝ) + 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Stirling.stirlingSeq (k + 1) * Real.exp (-1 / (12 * ((k : ℝ) + 1) + 1))
        = Stirling.stirlingSeq (k + 1) *
            (Real.exp (1 / (12 * (k : ℝ) + 1) - 1 / (12 * ((k : ℝ) + 1) + 1)) *
              Real.exp (-1 / (12 * (k : ℝ) + 1))) := by rw [← hprod]
      _ = (Real.exp (1 / (12 * (k : ℝ) + 1) - 1 / (12 * ((k : ℝ) + 1) + 1)) *
            Stirling.stirlingSeq (k + 1)) * Real.exp (-1 / (12 * (k : ℝ) + 1)) := by ring
      _ ≤ Stirling.stirlingSeq k * Real.exp (-1 / (12 * (k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
  have hb_step : ∀ m : ℕ, b n ≤ b (n + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => exact le_trans ih (hb_mono (n + m) (by omega))
  have hc_step : ∀ m : ℕ, c (n + m) ≤ c n := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => exact le_trans (hc_anti (n + m) (by omega)) ih
  have htend_b : Filter.Tendsto b Filter.atTop (nhds (Real.sqrt Real.pi)) := by
    have hzero : Filter.Tendsto (fun k : ℕ => -1 / (12 * (k : ℝ))) Filter.atTop (nhds 0) := by
      have ht : Filter.Tendsto (fun k : ℕ => (12 : ℝ) * (k : ℝ)) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      simpa using tendsto_const_nhds.div_atTop ht
    have hexp : Filter.Tendsto (fun k : ℕ => Real.exp (-1 / (12 * (k : ℝ)))) Filter.atTop (nhds 1) := by
      have hc := (Real.continuous_exp.tendsto 0).comp hzero
      rw [Real.exp_zero] at hc
      exact hc
    have hb' := Stirling.tendsto_stirlingSeq_sqrt_pi.mul hexp
    rw [mul_one] at hb'
    exact hb'
  have htend_c : Filter.Tendsto c Filter.atTop (nhds (Real.sqrt Real.pi)) := by
    have hzero : Filter.Tendsto (fun k : ℕ => -1 / (12 * (k : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have ht : Filter.Tendsto (fun k : ℕ => (12 : ℝ) * (k : ℝ) + 1) Filter.atTop Filter.atTop :=
        (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop).atTop_add
          tendsto_const_nhds
      simpa using tendsto_const_nhds.div_atTop ht
    have hexp : Filter.Tendsto (fun k : ℕ => Real.exp (-1 / (12 * (k : ℝ) + 1))) Filter.atTop (nhds 1) := by
      have hc := (Real.continuous_exp.tendsto 0).comp hzero
      rw [Real.exp_zero] at hc
      exact hc
    have hc' := Stirling.tendsto_stirlingSeq_sqrt_pi.mul hexp
    rw [mul_one] at hc'
    exact hc'
  have hbn_le : b n ≤ Real.sqrt Real.pi := by
    refine ge_of_tendsto htend_b ?_
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hb_step m
  have hcn_ge : Real.sqrt Real.pi ≤ c n := by
    refine le_of_tendsto htend_c ?_
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hc_step m
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hcn_ge (Real.exp_pos (1 / (12 * (n : ℝ) + 1))).le
    dsimp only [c] at hmul
    rw [mul_assoc, ← Real.exp_add] at hmul
    have h0 : -1 / (12 * (n : ℝ) + 1) + 1 / (12 * (n : ℝ) + 1) = 0 := by ring
    rwa [h0, Real.exp_zero, mul_one] at hmul
  · have hmul := mul_le_mul_of_nonneg_right hbn_le (Real.exp_pos (1 / (12 * (n : ℝ)))).le
    dsimp only [b] at hmul
    rw [mul_assoc, ← Real.exp_add] at hmul
    have h0 : -1 / (12 * (n : ℝ)) + 1 / (12 * (n : ℝ)) = 0 := by ring
    rwa [h0, Real.exp_zero, mul_one] at hmul

/-- **Robbins Non-Asymptotic Factorial Bounds:** For all `n ≥ 1`,
`√(2 * π * n) * (n / e)^n * exp(1 / (12n + 1)) ≤ n! ≤ √(2 * π * n) * (n / e)^n * exp(1 / (12n))`. -/
theorem stirling_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
        Real.exp (1 / (12 * (n : ℝ) + 1)) ≤ (n.factorial : ℝ) ∧
      (n.factorial : ℝ) ≤
        Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ))) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hden_pos : 0 < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by positivity
  have hfac_eq : (n.factorial : ℝ) =
      Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
    unfold Stirling.stirlingSeq
    exact (div_mul_cancel₀ _ hden_pos.ne').symm
  have hsqrt_mul : Real.sqrt (2 * Real.pi * (n : ℝ)) =
      Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ)) := by
    rw [show 2 * Real.pi * (n : ℝ) = Real.pi * (2 * (n : ℝ)) by ring, Real.sqrt_mul Real.pi_pos.le]
  obtain ⟨hL, hU⟩ := stirling_robbins_two_sided n hn
  rw [hfac_eq, hsqrt_mul]
  constructor
  · calc Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ) + 1))
        = (Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ) + 1))) *
            (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by ring
      _ ≤ Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) :=
          mul_le_mul_of_nonneg_right hL hden_pos.le
  · calc Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n)
        ≤ (Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ)))) *
            (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) :=
          mul_le_mul_of_nonneg_right hU hden_pos.le
      _ = Real.sqrt Real.pi * Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
            Real.exp (1 / (12 * (n : ℝ))) := by ring

/-- **Sharp Two-Sided Central Binomial Bounds:** For all `n ≥ 1`,
`4^n / √(π * (n + 1/2)) ≤ C(2n, n) ≤ 4^n / √(π * n)`. -/
theorem centralBinom_sharp_bounds (n : ℕ) (hn : 1 ≤ n) :
    (4 : ℝ) ^ n / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2)) ≤ (Nat.choose (2 * n) n : ℝ) ∧
      (Nat.choose (2 * n) n : ℝ) ≤ (4 : ℝ) ^ n / Real.sqrt (Real.pi * (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have hcb_eq : (Nat.choose (2 * n) n : ℝ) =
      (4 : ℝ) ^ n * (Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ))) := by
    have hch := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)
    rw [show 2 * n - n = n by omega] at hch
    have hchR : (Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ) ^ 2 = ((2 * n).factorial : ℝ) := by
      have hc := congrArg (Nat.cast (R := ℝ)) hch
      push_cast at hc
      linarith [hc]
    have h1 : (n.factorial : ℝ) =
        Stirling.stirlingSeq n * (Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n) := by
      unfold Stirling.stirlingSeq
      exact (div_mul_cancel₀ _ (by positivity)).symm
    have h2 : ((2 * n).factorial : ℝ) =
        Stirling.stirlingSeq (2 * n) *
          (Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) * (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n)) := by
      unfold Stirling.stirlingSeq
      exact (div_mul_cancel₀ _ (by positivity)).symm
    have hfac_ne : (n.factorial : ℝ) ≠ 0 := by positivity
    have hch_div : (Nat.choose (2 * n) n : ℝ) = ((2 * n).factorial : ℝ) / (n.factorial : ℝ) ^ 2 :=
      (eq_div_iff (pow_ne_zero 2 hfac_ne)).mpr hchR
    rw [hch_div, h1, h2]
    have hsqrt4 : Real.sqrt (2 * ((2 * n : ℕ) : ℝ)) = 2 * Real.sqrt (n : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, show 2 * (2 * (n : ℝ)) = 2 ^ 2 * (n : ℝ) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hpow2n : (((2 * n : ℕ) : ℝ) / Real.exp 1) ^ (2 * n) =
        (4 : ℝ) ^ n * (((n : ℝ) / Real.exp 1) ^ n) ^ 2 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, show 2 * (n : ℝ) / Real.exp 1 = 2 * ((n : ℝ) / Real.exp 1) by ring,
          mul_pow, pow_mul, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
      ring
    have hsqrt_sq : (Real.sqrt (2 * (n : ℝ))) ^ 2 = 2 * (n : ℝ) := Real.sq_sqrt (by positivity)
    have hsqrt_n_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn_pos.le
    have hsn_ne : Stirling.stirlingSeq n ≠ 0 := (stirlingSeq_pos hn).ne'
    have hsqrt_n_ne : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn_pos).ne'
    have hpow_ne : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := by positivity
    rw [hsqrt4, hpow2n]
    rw [mul_pow, mul_pow, hsqrt_sq]
    field_simp [hfac_ne, hsn_ne, hsqrt_n_ne, hpow_ne]
    rw [hsqrt_n_sq]
  obtain ⟨hLn, hUn⟩ := stirling_robbins_two_sided n hn
  obtain ⟨hL2n, hU2n⟩ := stirling_robbins_two_sided (2 * n) (by omega)
  have hpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsn_pos : 0 < Stirling.stirlingSeq n := stirlingSeq_pos hn
  rw [hcb_eq]
  constructor
  · have hlower_stirl :
        1 / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2)) ≤
          Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ)) := by
      have hratio_ge : Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) / Real.sqrt Real.pi ≤
          Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 := by
        have hnum : Real.sqrt Real.pi * Real.exp (1 / (24 * (n : ℝ) + 1)) ≤
            Stirling.stirlingSeq (2 * n) := by
          have h2n_eq : (1 : ℝ) / (24 * (n : ℝ) + 1) =
              1 / (12 * ((2 * n : ℕ) : ℝ) + 1) := by
            push_cast
            ring
          rw [h2n_eq]
          exact hL2n
        have hden : Stirling.stirlingSeq n ^ 2 ≤ Real.pi * Real.exp (1 / (6 * (n : ℝ))) := by
          calc Stirling.stirlingSeq n ^ 2
              ≤ (Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ)))) ^ 2 :=
                pow_le_pow_left₀ hsn_pos.le hUn 2
            _ = Real.pi * Real.exp (1 / (6 * (n : ℝ))) := by
                rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Real.exp_nat_mul]
                congr 1
                ring
        have hpi_mul : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
          Real.mul_self_sqrt Real.pi_pos.le
        have hexp_eq : Real.exp (1 / (24 * (n : ℝ) + 1)) / (Real.pi * Real.exp (1 / (6 * (n : ℝ)))) =
            Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) / Real.pi := by
          rw [Real.exp_sub]
          ring
        calc Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) / Real.sqrt Real.pi
            = (Real.sqrt Real.pi * Real.exp (1 / (24 * (n : ℝ) + 1))) /
                (Real.pi * Real.exp (1 / (6 * (n : ℝ)))) := by
              rw [mul_div_assoc, hexp_eq, ← mul_div_assoc, div_eq_div_iff hpi_pos.ne' Real.pi_pos.ne']
              calc Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) * Real.pi
                  = Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) *
                      (Real.sqrt Real.pi * Real.sqrt Real.pi) := by rw [hpi_mul]
                _ = Real.sqrt Real.pi * Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) *
                      Real.sqrt Real.pi := by ring
          _ ≤ Stirling.stirlingSeq (2 * n) / (Real.pi * Real.exp (1 / (6 * (n : ℝ)))) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ ≤ Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 :=
              div_le_div_of_nonneg_left (stirlingSeq_pos (by omega)).le (pow_pos hsn_pos 2) hden
      have hlog_bound : 1 / (6 * (n : ℝ)) - 1 / (24 * (n : ℝ) + 1) ≤
          (1 / 2) * Real.log (((n : ℝ) + 1 / 2) / (n : ℝ)) := by
        let u : ℝ := 1 / (4 * (n : ℝ) + 1)
        have hu_pos : 0 < u := by positivity
        have hu_lt1 : u < 1 := by
          dsimp only [u]
          rw [div_lt_one (by positivity)]
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have hfrac_u : ((n : ℝ) + 1 / 2) / (n : ℝ) = (1 + u) / (1 - u) := by
          dsimp only [u]
          field_simp [hn_pos.ne']
          ring
        have hlog_u := (log_one_add_div_one_sub_bounds hu_pos.le hu_lt1).1
        have hhalf_log : u ≤ (1 / 2) * Real.log (((n : ℝ) + 1 / 2) / (n : ℝ)) := by
          rw [hfrac_u]
          have h3 : 0 ≤ (2 / 3 : ℝ) * u ^ 3 := by positivity
          linarith [hlog_u]
        have hcmp_u : 1 / (6 * (n : ℝ)) - 1 / (24 * (n : ℝ) + 1) ≤ u := by
          dsimp only [u]
          have h1 : (0 : ℝ) < 6 * (n : ℝ) := by positivity
          have h2 : (0 : ℝ) < 24 * (n : ℝ) + 1 := by positivity
          have h3 : (0 : ℝ) < 4 * (n : ℝ) + 1 := by positivity
          rw [show 1 / (6 * (n : ℝ)) - 1 / (24 * (n : ℝ) + 1) =
              (18 * (n : ℝ) + 1) / (6 * (n : ℝ) * (24 * (n : ℝ) + 1)) by
            field_simp [h1.ne', h2.ne']; ring]
          rw [div_le_div_iff₀ (by positivity) h3]
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        exact le_trans hcmp_u hhalf_log
      have hexp_sqrt : Real.sqrt ((n : ℝ) / ((n : ℝ) + 1 / 2)) ≤
          Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) := by
        have h1 : Real.sqrt ((n : ℝ) / ((n : ℝ) + 1 / 2)) =
            Real.exp (-(1 / 2 * Real.log (((n : ℝ) + 1 / 2) / (n : ℝ)))) := by
          rw [Real.exp_neg, ← Real.log_rpow (by positivity), Real.exp_log (by positivity),
              ← Real.sqrt_eq_rpow, Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
              inv_div]
        rw [h1]
        apply Real.exp_le_exp.mpr
        linarith
      calc 1 / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2))
          = Real.sqrt ((n : ℝ) / ((n : ℝ) + 1 / 2)) / (Real.sqrt Real.pi * Real.sqrt (n : ℝ)) := by
            rw [Real.sqrt_mul Real.pi_pos.le, Real.sqrt_div hn_pos.le]
            field_simp [hpi_pos.ne', (Real.sqrt_pos.mpr hn_pos).ne',
              (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1 / 2)).ne']
        _ ≤ (Real.exp (1 / (24 * (n : ℝ) + 1) - 1 / (6 * (n : ℝ))) / Real.sqrt Real.pi) /
              Real.sqrt (n : ℝ) := by
            rw [div_div]
            exact div_le_div_of_nonneg_right hexp_sqrt (by positivity)
        _ ≤ (Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2) / Real.sqrt (n : ℝ) :=
            div_le_div_of_nonneg_right hratio_ge (by positivity)
        _ = Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ)) := by
            rw [div_div]
    calc (4 : ℝ) ^ n / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2))
        = (4 : ℝ) ^ n * (1 / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2))) := by ring
      _ ≤ (4 : ℝ) ^ n *
            (Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hlower_stirl (by positivity)
  · have hupper_stirl :
        Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ)) ≤
          1 / Real.sqrt (Real.pi * (n : ℝ)) := by
      have hnum : Stirling.stirlingSeq (2 * n) ≤ Real.sqrt Real.pi * Real.exp (1 / (24 * (n : ℝ))) := by
        have h2n_eq : (1 : ℝ) / (24 * (n : ℝ)) = 1 / (12 * ((2 * n : ℕ) : ℝ)) := by
          push_cast
          ring
        rw [h2n_eq]
        exact hU2n
      have hden : Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1)) ≤ Stirling.stirlingSeq n ^ 2 := by
        calc Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1))
            = (Real.sqrt Real.pi * Real.exp (1 / (12 * (n : ℝ) + 1))) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Real.exp_nat_mul]
              congr 1
              ring
          _ ≤ Stirling.stirlingSeq n ^ 2 := pow_le_pow_left₀ (by positivity) hLn 2
      have hexp_cmp : Real.exp (1 / (24 * (n : ℝ))) ≤ Real.exp (2 / (12 * (n : ℝ) + 1)) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      have hratio_le : Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2 ≤
          1 / Real.sqrt Real.pi := by
        have hpi_mul : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
          Real.mul_self_sqrt Real.pi_pos.le
        calc Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2
            ≤ (Real.sqrt Real.pi * Real.exp (1 / (24 * (n : ℝ)))) /
                (Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1))) :=
              div_le_div₀ (by positivity) hnum (by positivity) hden
          _ ≤ (Real.sqrt Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1))) /
                (Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1))) := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left hexp_cmp hpi_pos.le
              · positivity
          _ = 1 / Real.sqrt Real.pi := by
              rw [div_eq_div_iff (by positivity) hpi_pos.ne']
              calc Real.sqrt Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1)) * Real.sqrt Real.pi
                  = (Real.sqrt Real.pi * Real.sqrt Real.pi) *
                      Real.exp (2 / (12 * (n : ℝ) + 1)) := by ring
                _ = 1 * (Real.pi * Real.exp (2 / (12 * (n : ℝ) + 1))) := by
                    rw [hpi_mul]; ring
      calc Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ))
          = (Stirling.stirlingSeq (2 * n) / Stirling.stirlingSeq n ^ 2) / Real.sqrt (n : ℝ) := by
            rw [div_div]
        _ ≤ (1 / Real.sqrt Real.pi) / Real.sqrt (n : ℝ) :=
            div_le_div_of_nonneg_right hratio_le (by positivity)
        _ = 1 / Real.sqrt (Real.pi * (n : ℝ)) := by
            rw [Real.sqrt_mul Real.pi_pos.le, div_div]
    calc (4 : ℝ) ^ n *
          (Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n ^ 2 * Real.sqrt (n : ℝ)))
        ≤ (4 : ℝ) ^ n * (1 / Real.sqrt (Real.pi * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hupper_stirl (by positivity)
      _ = (4 : ℝ) ^ n / Real.sqrt (Real.pi * (n : ℝ)) := by ring

/-- **All-`n` Central Binomial Lower Bound:**
`4^n / √(π * (n + 1/2)) ≤ C(2n, n)` holds for every `n : ℕ` (including `n = 0`). -/
theorem centralBinom_lower_all (n : ℕ) :
    (4 : ℝ) ^ n / Real.sqrt (Real.pi * ((n : ℝ) + 1 / 2)) ≤ (Nat.choose (2 * n) n : ℝ) := by
  cases n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_add, mul_zero, Nat.choose_self, Nat.cast_one]
    have hsqrt_gt : 1 < Real.sqrt (Real.pi * (1 / 2)) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_lt_sqrt (by norm_num)
      linarith [Real.pi_gt_three]
    exact (div_le_one (lt_trans (by norm_num) hsqrt_gt)).mpr hsqrt_gt.le
  | succ n' =>
    exact (centralBinom_sharp_bounds (n' + 1) (Nat.succ_pos n')).1

/-- Binary Shannon entropy in bits: `H₂(p) = -p log₂ p - (1 - p) log₂ (1 - p)`. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  (-p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2

/-- **Binary-Entropy Binomial Bound:** For all `k ≤ n`,
`C(n, k) ≤ 2 ^ (n * H₂(k / n))`. -/
theorem choose_le_two_pow_binaryEntropy (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [binaryEntropy]
  by_cases hkn : k = n
  · subst hkn
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
    simp [binaryEntropy, hk_ne]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hnk_pos : (0 : ℝ) < (n - k : ℕ) := by
    have : 1 ≤ n - k := by omega
    positivity
  let p : ℝ := (k : ℝ) / (n : ℝ)
  have hp_pos : 0 < p := by positivity
  have h1p_pos : 0 < 1 - p := by
    dsimp only [p]
    rw [sub_pos, div_lt_one hn_pos]
    exact_mod_cast lt_of_le_of_ne hk hkn
  have h1p_eq : 1 - p = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
    dsimp only [p]
    rw [Nat.cast_sub hk]
    field_simp [hn_pos.ne']
  have hbinom_term :
      (Nat.choose n k : ℝ) * (p ^ k * (1 - p) ^ (n - k)) ≤ 1 := by
    have hadd : (p + (1 - p)) ^ n =
        ∑ j ∈ Finset.range (n + 1), p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ) :=
      add_pow p (1 - p) n
    have h1 : (p + (1 - p)) ^ n = 1 := by simp
    rw [h1] at hadd
    have hle := Finset.single_le_sum
      (f := fun j => p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ))
      (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    linarith [hle, hadd]
  have hpow_eq : p ^ k * (1 - p) ^ (n - k) =
      (2 : ℝ) ^ (-((n : ℝ) * binaryEntropy p)) := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexp_lhs : p ^ k * (1 - p) ^ (n - k) =
        Real.exp ((k : ℝ) * Real.log p + ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
      rw [← Real.exp_log (mul_pos (pow_pos hp_pos k) (pow_pos h1p_pos (n - k))),
          Real.log_mul (pow_pos hp_pos k).ne' (pow_pos h1p_pos (n - k)).ne',
          Real.log_pow, Real.log_pow]
    rw [hexp_lhs]
    congr 1
    dsimp only [binaryEntropy]
    have hnkR : ((n - k : ℕ) : ℝ) = (n : ℝ) * (1 - p) := by
      rw [h1p_eq]
      field_simp [hn_pos.ne']
    have hkR : (k : ℝ) = (n : ℝ) * p := by
      dsimp only [p]
      field_simp [hn_pos.ne']
    rw [hkR, hnkR]
    field_simp [hlog2_pos.ne']
    ring
  rw [hpow_eq, Real.rpow_neg (by norm_num)] at hbinom_term
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc (Nat.choose n k : ℝ)
      = ((Nat.choose n k : ℝ) * ((2 : ℝ) ^ ((n : ℝ) * binaryEntropy p))⁻¹) *
          (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) := by
        rw [mul_assoc, inv_mul_cancel₀ h2pow_pos.ne', mul_one]
    _ ≤ 1 * (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) :=
        mul_le_mul_of_nonneg_right hbinom_term h2pow_pos.le
    _ = (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) := one_mul _

/-- **Binary-Entropy Binomial Tail Bound:** For all `2 * k ≤ n`,
`∑_{j ≤ k} C(n, j) ≤ 2 ^ (n * H₂(k / n))`. -/
theorem sum_choose_le_two_pow_binaryEntropy (n k : ℕ) (hk : 2 * k ≤ n) :
    ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ) ≤
      (2 : ℝ) ^ ((n : ℝ) * binaryEntropy ((k : ℝ) / n)) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [binaryEntropy]
  have hkn : k < n := by omega
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  let p : ℝ := (k : ℝ) / (n : ℝ)
  have hp_pos : 0 < p := by positivity
  have h1p_pos : 0 < 1 - p := by
    dsimp only [p]
    rw [sub_pos, div_lt_one hn_pos]
    exact_mod_cast hkn
  have hp_le_1p : p ≤ 1 - p := by
    dsimp only [p]
    rw [le_sub_iff_add_le, ← two_mul, mul_div_assoc', div_le_one hn_pos]
    exact_mod_cast hk
  have hterm_le : ∀ j ∈ Finset.range (k + 1),
      (Nat.choose n j : ℝ) * (p ^ k * (1 - p) ^ (n - k)) ≤
        p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ) := by
    intro j hj
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpj : p ^ k * (1 - p) ^ (n - k) ≤ p ^ j * (1 - p) ^ (n - j) := by
      have hk_split : p ^ k = p ^ j * p ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hj_le]
      have hnk_split : (1 - p) ^ (n - j) = (1 - p) ^ (n - k) * (1 - p) ^ (k - j) := by
        rw [← pow_add, show n - k + (k - j) = n - j by omega]
      rw [hk_split, hnk_split]
      have hpow_cmp : p ^ (k - j) ≤ (1 - p) ^ (k - j) :=
        pow_le_pow_left₀ hp_pos.le hp_le_1p (k - j)
      calc (p ^ j * p ^ (k - j)) * (1 - p) ^ (n - k)
          = (p ^ j * (1 - p) ^ (n - k)) * p ^ (k - j) := by ring
        _ ≤ (p ^ j * (1 - p) ^ (n - k)) * (1 - p) ^ (k - j) :=
            mul_le_mul_of_nonneg_left hpow_cmp (by positivity)
        _ = p ^ j * ((1 - p) ^ (n - k) * (1 - p) ^ (k - j)) := by ring
    calc (Nat.choose n j : ℝ) * (p ^ k * (1 - p) ^ (n - k))
        ≤ (Nat.choose n j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) :=
          mul_le_mul_of_nonneg_left hpj (by positivity)
      _ = p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ) := by ring
  have hsum_le : (∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)) * (p ^ k * (1 - p) ^ (n - k)) ≤ 1 := by
    rw [Finset.sum_mul]
    calc ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ) * (p ^ k * (1 - p) ^ (n - k))
        ≤ ∑ j ∈ Finset.range (k + 1), p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ) :=
          Finset.sum_le_sum hterm_le
      _ ≤ ∑ j ∈ Finset.range (n + 1), p ^ j * (1 - p) ^ (n - j) * (Nat.choose n j : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          exact Finset.range_subset.mpr fun _ hx =>
            Finset.mem_range.mpr (lt_of_lt_of_le hx (Nat.succ_le_succ hkn.le))
      _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
      _ = 1 := by simp
  have hpow_eq : p ^ k * (1 - p) ^ (n - k) =
      (2 : ℝ) ^ (-((n : ℝ) * binaryEntropy p)) := by
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hexp_lhs : p ^ k * (1 - p) ^ (n - k) =
        Real.exp ((k : ℝ) * Real.log p + ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
      rw [← Real.exp_log (mul_pos (pow_pos hp_pos k) (pow_pos h1p_pos (n - k))),
          Real.log_mul (pow_pos hp_pos k).ne' (pow_pos h1p_pos (n - k)).ne',
          Real.log_pow, Real.log_pow]
    rw [hexp_lhs]
    congr 1
    dsimp only [binaryEntropy]
    have h1p_eq : 1 - p = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
      dsimp only [p]
      rw [Nat.cast_sub hkn.le]
      field_simp [hn_pos.ne']
    have hnkR : ((n - k : ℕ) : ℝ) = (n : ℝ) * (1 - p) := by
      rw [h1p_eq]
      field_simp [hn_pos.ne']
    have hkR : (k : ℝ) = (n : ℝ) * p := by
      dsimp only [p]
      field_simp [hn_pos.ne']
    rw [hkR, hnkR]
    field_simp [hlog2_pos.ne']
    ring
  rw [hpow_eq, Real.rpow_neg (by norm_num)] at hsum_le
  have h2pow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) :=
    Real.rpow_pos_of_pos (by norm_num) _
  calc ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)
      = ((∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)) *
          ((2 : ℝ) ^ ((n : ℝ) * binaryEntropy p))⁻¹) * (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) := by
        rw [mul_assoc, inv_mul_cancel₀ h2pow_pos.ne', mul_one]
    _ ≤ 1 * (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) :=
        mul_le_mul_of_nonneg_right hsum_le h2pow_pos.le
    _ = (2 : ℝ) ^ ((n : ℝ) * binaryEntropy p) := one_mul _

end StirlingBounds

/-!
## Section 4: `q`-Binomial / Gaussian Polynomial Identities & `q`-Binomial Theorem
-/

section QBinomial

/-- Gaussian `q`-binomial polynomial `[n choose k]_q ∈ R[q]`, defined by the first
`q`-Pascal recurrence `[n+1 choose k+1]_q = q^{k+1} [n choose k+1]_q + [n choose k]_q`. -/
noncomputable def qBinomPoly (R : Type*) [CommRing R] : ℕ → ℕ → Polynomial R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => Polynomial.X ^ (k + 1) * qBinomPoly R n (k + 1) + qBinomPoly R n k

/-- Evaluated Gaussian `q`-binomial coefficient `[n choose k]_q ∈ R`. -/
noncomputable def qBinom {R : Type*} [CommRing R] (q : R) (n k : ℕ) : R :=
  (qBinomPoly R n k).eval q

/-- `q`-integer bracket `[k]_q = ∑_{i < k} q^i ∈ R[q]`. -/
noncomputable def qBracketPoly (R : Type*) [CommRing R] (k : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range k, Polynomial.X ^ i

/-- `q`-factorial polynomial `[n]_q! = ∏_{j=1}^n [j]_q ∈ R[q]`. -/
noncomputable def qFactorialPoly (R : Type*) [CommRing R] (n : ℕ) : Polynomial R :=
  ∏ j ∈ Finset.range n, qBracketPoly R (j + 1)

@[simp]
theorem qBinomPoly_zero {R : Type*} [CommRing R] (n : ℕ) : qBinomPoly R n 0 = 1 := by
  cases n <;> simp [qBinomPoly]

theorem qBinomPoly_of_lt {R : Type*} [CommRing R] {n k : ℕ} (h : n < k) :
    qBinomPoly R n k = 0 := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ k' => simp [qBinomPoly]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k' =>
      unfold qBinomPoly
      rw [ih (by omega), ih (by omega)]
      simp

@[simp]
theorem qBinomPoly_self {R : Type*} [CommRing R] (n : ℕ) : qBinomPoly R n n = 1 := by
  induction n with
  | zero => simp [qBinomPoly]
  | succ n ih =>
    unfold qBinomPoly
    rw [qBinomPoly_of_lt (Nat.lt_succ_self n), ih]
    simp

/-- **First `q`-Pascal Recurrence:**
`[n + 1 choose k + 1]_q = q^{k + 1} [n choose k + 1]_q + [n choose k]_q`. -/
theorem qBinomPoly_pascal_left {R : Type*} [CommRing R] (n k : ℕ) :
    qBinomPoly R (n + 1) (k + 1) =
      Polynomial.X ^ (k + 1) * qBinomPoly R n (k + 1) + qBinomPoly R n k := rfl

private lemma poly_coeff_X_pow_mul {R : Type*} [CommRing R] (d i : ℕ) (P : Polynomial R) :
    (Polynomial.X ^ d * P).coeff (i + d) = P.coeff i := by
  induction d generalizing i with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', mul_assoc, mul_comm Polynomial.X (Polynomial.X ^ d * P),
        show i + (d + 1) = (i + d) + 1 by omega, Polynomial.coeff_mul_X, ih]

private lemma poly_finset_sum_coeff {A : Type*} [Semiring A] {ι : Type*}
    (s : Finset ι) (f : ι → Polynomial A) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [ha, ih]

private lemma poly_X_pow_mul_cancel {R : Type*} [CommRing R] (d : ℕ) {P Q : Polynomial R}
    (h : Polynomial.X ^ d * P = Polynomial.X ^ d * Q) : P = Q := by
  ext i
  have hi := congrArg (fun f : Polynomial R => f.coeff (i + d)) h
  simpa [poly_coeff_X_pow_mul] using hi

private lemma poly_eval₂_finset_sum {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : B) {ι : Type*} (s : Finset ι) (g : ι → Polynomial A) :
    Polynomial.eval₂ f x (∑ i ∈ s, g i) = ∑ i ∈ s, Polynomial.eval₂ f x (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.eval₂_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Polynomial.eval₂_add, ih, Finset.sum_insert ha]

private lemma poly_eval₂_finset_prod {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (x : B) {ι : Type*} (s : Finset ι) (g : ι → Polynomial A) :
    Polynomial.eval₂ f x (∏ i ∈ s, g i) = ∏ i ∈ s, Polynomial.eval₂ f x (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.eval₂_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Polynomial.eval₂_mul, ih, Finset.prod_insert ha]

private lemma tri_succ (k : ℕ) : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  cases k with
  | zero => simp
  | succ k' =>
    have hd : (k' + 2) * (k' + 1) = 2 * (k' + 1) + (k' + 1) * k' := by ring
    rw [hd, Nat.mul_add_div (by norm_num : 0 < 2), show k' + 1 - 1 = k' by omega, add_comm]

/-- **The `q`-Binomial Theorem (Polynomial Identity in `(R[q])[Y]`):**
`∏_{j=0}^{n-1} (1 + q^j Y) = ∑_{k=0}^n q^{k(k-1)/2} [n choose k]_q Y^k`. -/
theorem qBinom_theorem (R : Type*) [CommRing R] (n : ℕ) :
    (∏ j ∈ Finset.range n,
      (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ j) * Polynomial.X)) =
      ∑ k ∈ Finset.range (n + 1),
        Polynomial.C ((Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2) * qBinomPoly R n k) *
          Polynomial.X ^ k := by
  induction n with
  | zero =>
    simp [qBinomPoly]
  | succ n ih =>
    rw [Finset.prod_range_succ']
    have hzero : 1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ 0) * Polynomial.X =
        1 + Polynomial.X := by simp
    rw [hzero]
    let qY : Polynomial (Polynomial R) :=
      Polynomial.C (Polynomial.X : Polynomial R) * Polynomial.X
    have hshift :
        (∏ j ∈ Finset.range n,
          (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ (j + 1)) * Polynomial.X)) =
        Polynomial.eval₂ Polynomial.C qY
          (∏ j ∈ Finset.range n,
            (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ j) * Polynomial.X)) := by
      rw [poly_eval₂_finset_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
      have hpow : Polynomial.C ((Polynomial.X : Polynomial R) ^ (j + 1)) * Polynomial.X =
          Polynomial.C ((Polynomial.X : Polynomial R) ^ j) * qY := by
        dsimp only [qY]
        rw [pow_succ, map_mul, mul_assoc]
      rw [hpow]
    rw [hshift, ih, poly_eval₂_finset_sum]
    have heval_sum :
        (∑ k ∈ Finset.range (n + 1),
          Polynomial.eval₂ Polynomial.C qY
            (Polynomial.C ((Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2) * qBinomPoly R n k) *
              Polynomial.X ^ k)) =
        ∑ k ∈ Finset.range (n + 1),
          Polynomial.C ((Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2 + k) * qBinomPoly R n k) *
            Polynomial.X ^ k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      dsimp only [qY]
      rw [mul_pow, ← Polynomial.C_pow, ← mul_assoc (Polynomial.C _), ← map_mul]
      congr 1
      rw [pow_add]
      ring
    rw [heval_sum, Finset.sum_mul]
    apply Polynomial.ext
    intro k
    simp only [poly_finset_sum_coeff]
    have hmul_split :
        (∑ x ∈ Finset.range (n + 1),
          Polynomial.coeff
            (Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x) *
              Polynomial.X ^ x * (1 + Polynomial.X)) k) =
        (∑ x ∈ Finset.range (n + 1),
          Polynomial.coeff
            (Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x) *
              Polynomial.X ^ x) k) +
        (∑ x ∈ Finset.range (n + 1),
          Polynomial.coeff
            (Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x) *
              Polynomial.X ^ (x + 1)) k) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_add, mul_one, Polynomial.coeff_add, mul_assoc _ (Polynomial.X ^ x) Polynomial.X,
          ← pow_succ]
    rw [hmul_split]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    cases k with
    | zero =>
      have h1 : (∑ x ∈ Finset.range (n + 1),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x *
            (if 0 = x then (1 : Polynomial R) else 0)) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro x _ hx; rw [if_neg hx.symm, mul_zero]
        · intro h0; exfalso; exact h0 (Finset.mem_range.mpr (Nat.succ_pos n))
      have h2 : (∑ x ∈ Finset.range (n + 1),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x *
            (if 0 = x + 1 then (1 : Polynomial R) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun x _ => by rw [if_neg (by omega), mul_zero]
      have h3 : (∑ x ∈ Finset.range (n + 2),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R (n + 1) x *
            (if 0 = x then (1 : Polynomial R) else 0)) = 1 := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro x _ hx; rw [if_neg hx.symm, mul_zero]
        · intro h0; exfalso; exact h0 (Finset.mem_range.mpr (Nat.succ_pos _))
      rw [h1, h2, h3, add_zero]
    | succ m =>
      have hs1 : (∑ x ∈ Finset.range (n + 1),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x *
            (if m + 1 = x then (1 : Polynomial R) else 0)) =
          if m + 1 < n + 1 then
            (Polynomial.X : Polynomial R) ^ ((m + 1) * m / 2 + (m + 1)) * qBinomPoly R n (m + 1)
          else 0 := by
        by_cases hm : m + 1 < n + 1
        · rw [if_pos hm, Finset.sum_eq_single (m + 1)]
          · simp
          · intro x _ hx; rw [if_neg hx.symm, mul_zero]
          · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr hm)
        · rw [if_neg hm]
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx_lt := Finset.mem_range.mp hx
          rw [if_neg (by omega), mul_zero]
      have hs2 : (∑ x ∈ Finset.range (n + 1),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + x) * qBinomPoly R n x *
            (if m + 1 = x + 1 then (1 : Polynomial R) else 0)) =
          if m < n + 1 then
            (Polynomial.X : Polynomial R) ^ (m * (m - 1) / 2 + m) * qBinomPoly R n m
          else 0 := by
        by_cases hm : m < n + 1
        · rw [if_pos hm, Finset.sum_eq_single m]
          · simp
          · intro x _ hx; rw [if_neg (by omega), mul_zero]
          · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr hm)
        · rw [if_neg hm]
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx_lt := Finset.mem_range.mp hx
          rw [if_neg (by omega), mul_zero]
      have hs3 : (∑ x ∈ Finset.range (n + 2),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R (n + 1) x *
            (if m + 1 = x then (1 : Polynomial R) else 0)) =
          if m + 1 < n + 2 then
            (Polynomial.X : Polynomial R) ^ ((m + 1) * m / 2) * qBinomPoly R (n + 1) (m + 1)
          else 0 := by
        by_cases hm : m + 1 < n + 2
        · rw [if_pos hm, Finset.sum_eq_single (m + 1)]
          · simp
          · intro x _ hx; rw [if_neg hx.symm, mul_zero]
          · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr hm)
        · rw [if_neg hm]
          refine Finset.sum_eq_zero fun x hx => ?_
          have hx_lt := Finset.mem_range.mp hx
          rw [if_neg (by omega), mul_zero]
      rw [hs1, hs2, hs3]
      by_cases hm1 : m + 1 < n + 1
      · have hm0 : m < n + 1 := by omega
        have hm2 : m + 1 < n + 2 := by omega
        rw [if_pos hm1, if_pos hm0, if_pos hm2, qBinomPoly_pascal_left, tri_succ m, pow_add]
        ring
      · by_cases hm0 : m < n + 1
        · have hm_eq : m = n := by omega
          subst hm_eq
          have hm2 : m + 1 < m + 2 := by omega
          rw [if_neg hm1, if_pos hm0, if_pos hm2, qBinomPoly_pascal_left,
              qBinomPoly_of_lt (Nat.lt_succ_self m), mul_zero, zero_add, zero_add, tri_succ m]
        · have hm2 : ¬ m + 1 < n + 2 := by omega
          rw [if_neg hm1, if_neg hm0, if_neg hm2, add_zero]

/-- **Second `q`-Pascal Recurrence:**
For all `k ≤ n`, `[n + 1 choose k + 1]_q = [n choose k + 1]_q + q^{n - k} [n choose k]_q`. -/
theorem qBinomPoly_pascal_right {R : Type*} [CommRing R] {n k : ℕ} (hk : k ≤ n) :
    qBinomPoly R (n + 1) (k + 1) =
      qBinomPoly R n (k + 1) + Polynomial.X ^ (n - k) * qBinomPoly R n k := by
  have h1 := qBinom_theorem R (n + 1)
  have h0 := qBinom_theorem R n
  have hprod :
      (∏ j ∈ Finset.range (n + 1),
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ j) * Polynomial.X)) =
      (∏ j ∈ Finset.range n,
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ j) * Polynomial.X)) *
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ n) * Polynomial.X) :=
    Finset.prod_range_succ _ n
  rw [hprod, h0] at h1
  have hcoeff := congrArg (fun F : Polynomial (Polynomial R) => F.coeff (k + 1)) h1
  have hLHS :
      (∑ x ∈ Finset.range (n + 2),
        Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R (n + 1) x) *
          Polynomial.X ^ x).coeff (k + 1) =
      (Polynomial.X : Polynomial R) ^ ((k + 1) * k / 2) * qBinomPoly R (n + 1) (k + 1) := by
    rw [poly_finset_sum_coeff]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single (k + 1)]
    · simp
    · intro x _ hx; rw [if_neg hx.symm, mul_zero]
    · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
  have hRHS :
      ((∑ x ∈ Finset.range (n + 1),
        Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
          Polynomial.X ^ x) *
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ n) * Polynomial.X)).coeff (k + 1) =
      (Polynomial.X : Polynomial R) ^ ((k + 1) * k / 2) * qBinomPoly R n (k + 1) +
        (Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2 + n) * qBinomPoly R n k := by
    rw [Finset.sum_mul, poly_finset_sum_coeff]
    have hterm :
        ∑ x ∈ Finset.range (n + 1),
          (Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
            Polynomial.X ^ x * (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ n) * Polynomial.X)).coeff
            (k + 1) =
        (∑ x ∈ Finset.range (n + 1),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x *
            (if k + 1 = x then 1 else 0)) +
        ∑ x ∈ Finset.range (n + 1),
          (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + n) * qBinomPoly R n x *
            (if k + 1 = x + 1 then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have heq :
          Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
            Polynomial.X ^ x * (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ n) * Polynomial.X) =
          Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
            Polynomial.X ^ x +
          Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + n) * qBinomPoly R n x) *
            Polynomial.X ^ (x + 1) := by
        rw [mul_add, mul_one]
        congr 1
        have hC : Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
            Polynomial.C ((Polynomial.X : Polynomial R) ^ n) =
            Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + n) * qBinomPoly R n x) := by
          rw [← map_mul]
          congr 1
          rw [pow_add]
          ring
        calc Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
              Polynomial.X ^ x * (Polynomial.C ((Polynomial.X : Polynomial R) ^ n) * Polynomial.X)
            = (Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x) *
                Polynomial.C ((Polynomial.X : Polynomial R) ^ n)) * (Polynomial.X ^ x * Polynomial.X) := by
              ring
          _ = Polynomial.C ((Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + n) * qBinomPoly R n x) *
                Polynomial.X ^ (x + 1) := by
              rw [hC, pow_succ]
      rw [heq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, Polynomial.coeff_X_pow]
    rw [hterm]
    have hs1 : ∑ x ∈ Finset.range (n + 1),
        (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2) * qBinomPoly R n x *
          (if k + 1 = x then 1 else 0) =
        (Polynomial.X : Polynomial R) ^ ((k + 1) * k / 2) * qBinomPoly R n (k + 1) := by
      by_cases hkn : k + 1 < n + 1
      · rw [Finset.sum_eq_single (k + 1)]
        · simp
        · intro x _ hx; rw [if_neg hx.symm, mul_zero]
        · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr hkn)
      · have hkeq : k = n := by omega
        subst hkeq
        rw [qBinomPoly_of_lt (Nat.lt_succ_self k), mul_zero]
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx_lt := Finset.mem_range.mp hx
        rw [if_neg (by omega), mul_zero]
    have hs2 : ∑ x ∈ Finset.range (n + 1),
        (Polynomial.X : Polynomial R) ^ (x * (x - 1) / 2 + n) * qBinomPoly R n x *
          (if k + 1 = x + 1 then 1 else 0) =
        (Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2 + n) * qBinomPoly R n k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro x _ hx; rw [if_neg (by omega), mul_zero]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
    rw [hs1, hs2]
  rw [hLHS, hRHS] at hcoeff
  have hexp : k * (k - 1) / 2 + n = (k + 1) * k / 2 + (n - k) := by
    rw [tri_succ k]
    omega
  rw [hexp, pow_add, mul_assoc ((Polynomial.X : Polynomial R) ^ ((k + 1) * k / 2)), ← mul_add] at hcoeff
  exact poly_X_pow_mul_cancel ((k + 1) * k / 2) hcoeff.symm

/-- **Symmetry of `q`-Binomial Coefficients:**
For all `k ≤ n`, `[n choose n - k]_q = [n choose k]_q`. -/
theorem qBinomPoly_symm {R : Type*} [CommRing R] {n k : ℕ} (hk : k ≤ n) :
    qBinomPoly R n (n - k) = qBinomPoly R n k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ j =>
      by_cases hjn : j = n
      · subst hjn; simp
      · have hj_lt : j < n := by omega
        have hsub : n + 1 - (j + 1) = (n - (j + 1)) + 1 := by omega
        rw [hsub, qBinomPoly_pascal_right (by omega : n - (j + 1) ≤ n)]
        have hsub2 : n - (n - (j + 1)) = j + 1 := by omega
        rw [hsub2, show n - (j + 1) + 1 = n - j by omega, ih (by omega : j ≤ n),
            ih (by omega : j + 1 ≤ n), qBinomPoly_pascal_left, add_comm]

/-- **`q = 1` Specialization:** Evaluating `[n choose k]_q` at `q = 1` recovers `C(n, k)`. -/
theorem qBinomPoly_eval_one (R : Type*) [CommRing R] (n k : ℕ) :
    qBinom (1 : R) n k = (Nat.choose n k : R) := by
  unfold qBinom
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k' => simp [qBinomPoly]
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k' =>
      rw [qBinomPoly_pascal_left, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, one_pow, one_mul, ih (k' + 1), ih k', Nat.choose_succ_succ,
          Nat.cast_add, add_comm]

/-- **Evaluated `q`-Binomial Theorem:** For any `q x : R` in a commutative ring `R`,
`∏_{j=0}^{n-1} (1 + q^j x) = ∑_{k=0}^n q^{k(k-1)/2} [n choose k]_q x^k`. -/
theorem qBinom_eval_theorem {R : Type*} [CommRing R] (n : ℕ) (q x : R) :
    (∏ j ∈ Finset.range n, (1 + q ^ j * x)) =
      ∑ k ∈ Finset.range (n + 1), q ^ (k * (k - 1) / 2) * qBinom q n k * x ^ k := by
  have h := qBinom_theorem R n
  let ev : Polynomial (Polynomial R) → R :=
    Polynomial.eval₂ (Polynomial.evalRingHom q) x
  have hev_prod := congrArg ev h
  have hLHS : ev (∏ j ∈ Finset.range n,
      (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ j) * Polynomial.X)) =
      ∏ j ∈ Finset.range n, (1 + q ^ j * x) := by
    dsimp only [ev]
    rw [poly_eval₂_finset_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X]
    simp [Polynomial.evalRingHom]
  have hRHS : ev (∑ k ∈ Finset.range (n + 1),
      Polynomial.C ((Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2) * qBinomPoly R n k) *
        Polynomial.X ^ k) =
      ∑ k ∈ Finset.range (n + 1), q ^ (k * (k - 1) / 2) * qBinom q n k * x ^ k := by
    dsimp only [ev]
    rw [poly_eval₂_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    simp [Polynomial.evalRingHom, qBinom]
  rw [← hLHS, ← hRHS]
  exact hev_prod

private lemma tri_split {k j : ℕ} (hj : j ≤ k) :
    k * (k - 1) / 2 = j * (j - 1) / 2 + (k - j) * (k - j - 1) / 2 + j * (k - j) := by
  have heven : ∀ a : ℕ, 2 ∣ a * (a - 1) := fun a => by
    rcases Nat.even_or_odd a with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (m + m - 1), by ring⟩
    · have : 2 * m + 1 - 1 = 2 * m := by omega
      rw [this]
      exact ⟨(2 * m + 1) * m, by ring⟩
  have h1 := Nat.mul_div_cancel' (heven k)
  have h2 := Nat.mul_div_cancel' (heven j)
  have h3 := Nat.mul_div_cancel' (heven (k - j))
  have hmul : k * (k - 1) = j * (j - 1) + (k - j) * (k - j - 1) + 2 * (j * (k - j)) := by
    rcases k with _ | k'
    · have : j = 0 := by omega
      subst this; simp
    · rcases j with _ | j'
      · simp
      · have hkj : j' ≤ k' := by omega
        rcases Nat.eq_or_lt_of_le hkj with rfl | hkj_lt
        · simp
        · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k' - j' ≠ 0)
          have hk_eq : k' = j' + (d + 1) := by omega
          have hsub1 : k' + 1 - 1 = k' := by omega
          have hsub2 : j' + 1 - 1 = j' := by omega
          have hsub3 : k' + 1 - (j' + 1) = d + 1 := by omega
          have hsub4 : d + 1 - 1 = d := by omega
          rw [hsub1, hsub2, hsub3, hsub4, hk_eq]
          ring
  omega

/-- **`q`-Chu–Vandermonde Identity (Polynomial Version):**
For all `m n k : ℕ`,
`[m + n choose k]_q = ∑_{j=0}^k [j ≤ m ? q^{(m-j)(k-j)} [m choose j]_q [n choose k - j]_q : 0]`. -/
theorem qBinom_chu_vandermonde (R : Type*) [CommRing R] (m n k : ℕ) :
    qBinomPoly R (m + n) k =
      ∑ j ∈ Finset.range (k + 1),
        if j ≤ m then
          (Polynomial.X : Polynomial R) ^ ((m - j) * (k - j)) *
            qBinomPoly R m j * qBinomPoly R n (k - j)
        else 0 := by
  have hprod :
      (∏ r ∈ Finset.range (m + n),
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ r) * Polynomial.X)) =
      (∏ r ∈ Finset.range m,
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ r) * Polynomial.X)) *
      (∏ s ∈ Finset.range n,
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ (m + s)) * Polynomial.X)) :=
    Finset.prod_range_add _ m n
  let qmY : Polynomial (Polynomial R) :=
    Polynomial.C ((Polynomial.X : Polynomial R) ^ m) * Polynomial.X
  have hshift :
      (∏ s ∈ Finset.range n,
        (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ (m + s)) * Polynomial.X)) =
      Polynomial.eval₂ Polynomial.C qmY
        (∏ s ∈ Finset.range n,
          (1 + Polynomial.C ((Polynomial.X : Polynomial R) ^ s) * Polynomial.X)) := by
    rw [poly_eval₂_finset_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X]
    dsimp only [qmY]
    rw [pow_add, map_mul, mul_assoc]
    ring
  rw [hshift, qBinom_theorem R (m + n), qBinom_theorem R m, qBinom_theorem R n,
      poly_eval₂_finset_sum] at hprod
  have heval_n :
      (∑ s ∈ Finset.range (n + 1),
        Polynomial.eval₂ Polynomial.C qmY
          (Polynomial.C ((Polynomial.X : Polynomial R) ^ (s * (s - 1) / 2) * qBinomPoly R n s) *
            Polynomial.X ^ s)) =
      ∑ s ∈ Finset.range (n + 1),
        Polynomial.C ((Polynomial.X : Polynomial R) ^ (s * (s - 1) / 2 + m * s) * qBinomPoly R n s) *
          Polynomial.X ^ s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X]
    dsimp only [qmY]
    rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, ← mul_assoc (Polynomial.C _), ← map_mul]
    congr 1
    rw [pow_add]
    ring
  rw [heval_n] at hprod
  have hcoeff := congrArg (fun F : Polynomial (Polynomial R) => F.coeff k) hprod
  have hLHS :
      (∑ r ∈ Finset.range (m + n + 1),
        Polynomial.C ((Polynomial.X : Polynomial R) ^ (r * (r - 1) / 2) * qBinomPoly R (m + n) r) *
          Polynomial.X ^ r).coeff k =
      (Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2) * qBinomPoly R (m + n) k := by
    rw [poly_finset_sum_coeff]
    simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hk : k < m + n + 1
    · rw [Finset.sum_eq_single k]
      · simp
      · intro r _ hr; simp [hr.symm]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr hk)
    · rw [qBinomPoly_of_lt (by omega), mul_zero]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr_lt := Finset.mem_range.mp hr
      simp [show k ≠ r by omega]
  have hRHS :
      ((∑ r ∈ Finset.range (m + 1),
          Polynomial.C ((Polynomial.X : Polynomial R) ^ (r * (r - 1) / 2) * qBinomPoly R m r) *
            Polynomial.X ^ r) *
        (∑ s ∈ Finset.range (n + 1),
          Polynomial.C ((Polynomial.X : Polynomial R) ^ (s * (s - 1) / 2 + m * s) * qBinomPoly R n s) *
            Polynomial.X ^ s)).coeff k =
      (Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2) *
        ∑ j ∈ Finset.range (k + 1),
          if j ≤ m then
            (Polynomial.X : Polynomial R) ^ ((m - j) * (k - j)) *
              qBinomPoly R m j * qBinomPoly R n (k - j)
          else 0 := by
    let PA : Polynomial (Polynomial R) := ∑ r ∈ Finset.range (m + 1),
      Polynomial.C ((Polynomial.X : Polynomial R) ^ (r * (r - 1) / 2) * qBinomPoly R m r) *
        Polynomial.X ^ r
    let PB : Polynomial (Polynomial R) := ∑ s ∈ Finset.range (n + 1),
      Polynomial.C ((Polynomial.X : Polynomial R) ^ (s * (s - 1) / 2 + m * s) * qBinomPoly R n s) *
        Polynomial.X ^ s
    change (PA * PB).coeff k = _
    rw [Polynomial.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PA.coeff i * PB.coeff j) k,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hcoeffA :
        PA.coeff j =
        (Polynomial.X : Polynomial R) ^ (j * (j - 1) / 2) * qBinomPoly R m j := by
      dsimp only [PA]
      rw [poly_finset_sum_coeff]
      simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hjm : j ≤ m
      · rw [Finset.sum_eq_single j]
        · simp
        · intro r _ hr; simp [hr.symm]
        · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
      · rw [qBinomPoly_of_lt (by omega), mul_zero]
        refine Finset.sum_eq_zero fun r hr => ?_
        have hr_lt := Finset.mem_range.mp hr
        simp [show j ≠ r by omega]
    have hcoeffB :
        PB.coeff (k - j) =
        (Polynomial.X : Polynomial R) ^ ((k - j) * (k - j - 1) / 2 + m * (k - j)) *
          qBinomPoly R n (k - j) := by
      dsimp only [PB]
      rw [poly_finset_sum_coeff]
      simp_rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hkjn : k - j ≤ n
      · rw [Finset.sum_eq_single (k - j)]
        · simp
        · intro s _ hs; simp [hs.symm]
        · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
      · rw [qBinomPoly_of_lt (by omega), mul_zero]
        refine Finset.sum_eq_zero fun s hs => ?_
        have hs_lt := Finset.mem_range.mp hs
        simp [show k - j ≠ s by omega]
    rw [hcoeffA, hcoeffB]
    by_cases hjm : j ≤ m
    · rw [if_pos hjm]
      have hexp : j * (j - 1) / 2 + ((k - j) * (k - j - 1) / 2 + m * (k - j)) =
          k * (k - 1) / 2 + (m - j) * (k - j) := by
        rw [tri_split hj_le]
        have hmul_sub : m * (k - j) = j * (k - j) + (m - j) * (k - j) := by
          rw [← add_mul, Nat.add_sub_cancel' hjm]
        omega
      calc ((Polynomial.X : Polynomial R) ^ (j * (j - 1) / 2) * qBinomPoly R m j) *
            ((Polynomial.X : Polynomial R) ^ ((k - j) * (k - j - 1) / 2 + m * (k - j)) *
              qBinomPoly R n (k - j))
          = (Polynomial.X : Polynomial R) ^ (j * (j - 1) / 2 +
              ((k - j) * (k - j - 1) / 2 + m * (k - j))) *
              qBinomPoly R m j * qBinomPoly R n (k - j) := by rw [pow_add]; ring
        _ = (Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2 + (m - j) * (k - j)) *
              qBinomPoly R m j * qBinomPoly R n (k - j) := by rw [hexp]
        _ = (Polynomial.X : Polynomial R) ^ (k * (k - 1) / 2) *
              ((Polynomial.X : Polynomial R) ^ ((m - j) * (k - j)) *
                qBinomPoly R m j * qBinomPoly R n (k - j)) := by rw [pow_add]; ring
    · rw [if_neg hjm, qBinomPoly_of_lt (by omega), mul_zero, zero_mul, mul_zero]
  rw [hLHS, hRHS] at hcoeff
  exact poly_X_pow_mul_cancel (k * (k - 1) / 2) hcoeff

/-- **Evaluated `q`-Chu–Vandermonde Identity:** For any `q : R` and `m n k : ℕ`,
`[m + n choose k]_q = ∑_{j=0}^k [j ≤ m ? q^{(m-j)(k-j)} [m choose j]_q [n choose k - j]_q : 0]`. -/
theorem qBinom_eval_chu_vandermonde {R : Type*} [CommRing R] (q : R) (m n k : ℕ) :
    qBinom q (m + n) k =
      ∑ j ∈ Finset.range (k + 1),
        if j ≤ m then
          q ^ ((m - j) * (k - j)) * qBinom q m j * qBinom q n (k - j)
        else 0 := by
  have h := congrArg (Polynomial.eval q) (qBinom_chu_vandermonde R m n k)
  change qBinom q (m + n) k = _ at h
  rw [h, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp [qBinom]
  · simp

private lemma qBracketPoly_split {R : Type*} [CommRing R] {n k : ℕ} (hk : k ≤ n + 1) :
    qBracketPoly R (n + 1) =
      Polynomial.X ^ k * qBracketPoly R (n + 1 - k) + qBracketPoly R k := by
  unfold qBracketPoly
  conv_lhs => rw [show n + 1 = k + (n + 1 - k) by omega, Finset.sum_range_add]
  rw [Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by rw [pow_add]

private lemma qFactorialPoly_succ {R : Type*} [CommRing R] (n : ℕ) :
    qFactorialPoly R (n + 1) = qBracketPoly R (n + 1) * qFactorialPoly R n := by
  unfold qFactorialPoly
  rw [Finset.prod_range_succ, mul_comm]

/-- **`q`-Factorial Product Identity:** For all `k ≤ n`,
`[n choose k]_q * [k]_q! * [n - k]_q! = [n]_q!` in `R[q]`. -/
theorem qBinomPoly_mul_qFactorial (R : Type*) [CommRing R] {n k : ℕ} (hk : k ≤ n) :
    qBinomPoly R n k * qFactorialPoly R k * qFactorialPoly R (n - k) = qFactorialPoly R n := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp [qFactorialPoly]
  | succ n ih =>
    cases k with
    | zero =>
      simp [qFactorialPoly]
    | succ k' =>
      by_cases hkn : k' = n
      · subst hkn
        simp [qFactorialPoly]
      · have hk'_lt : k' < n := by omega
        have hsub : n + 1 - (k' + 1) = n - k' := by omega
        rw [hsub, qBinomPoly_pascal_left, add_mul, add_mul]
        have hterm1 :
            Polynomial.X ^ (k' + 1) * qBinomPoly R n (k' + 1) * qFactorialPoly R (k' + 1) *
              qFactorialPoly R (n - k') =
            Polynomial.X ^ (k' + 1) * qBracketPoly R (n - k') * qFactorialPoly R n := by
          have hfac_n : qFactorialPoly R (n - k') =
              qBracketPoly R (n - k') * qFactorialPoly R (n - (k' + 1)) := by
            have heq : n - k' = (n - (k' + 1)) + 1 := by omega
            rw [heq, qFactorialPoly_succ, show n - (k' + 1) + 1 = n - k' by omega]
          have hIH1 := ih (by omega : k' + 1 ≤ n)
          calc Polynomial.X ^ (k' + 1) * qBinomPoly R n (k' + 1) * qFactorialPoly R (k' + 1) *
                qFactorialPoly R (n - k')
              = Polynomial.X ^ (k' + 1) * qBracketPoly R (n - k') *
                  (qBinomPoly R n (k' + 1) * qFactorialPoly R (k' + 1) *
                    qFactorialPoly R (n - (k' + 1))) := by
                rw [hfac_n]; ring
            _ = Polynomial.X ^ (k' + 1) * qBracketPoly R (n - k') * qFactorialPoly R n := by
                rw [hIH1]
        have hterm2 :
            qBinomPoly R n k' * qFactorialPoly R (k' + 1) * qFactorialPoly R (n - k') =
              qBracketPoly R (k' + 1) * qFactorialPoly R n := by
          have hfac_k : qFactorialPoly R (k' + 1) =
              qBracketPoly R (k' + 1) * qFactorialPoly R k' := qFactorialPoly_succ k'
          have hIH2 := ih hk'_lt.le
          calc qBinomPoly R n k' * qFactorialPoly R (k' + 1) * qFactorialPoly R (n - k')
              = qBracketPoly R (k' + 1) *
                  (qBinomPoly R n k' * qFactorialPoly R k' * qFactorialPoly R (n - k')) := by
                rw [hfac_k]; ring
            _ = qBracketPoly R (k' + 1) * qFactorialPoly R n := by rw [hIH2]
        rw [hterm1, hterm2, ← add_mul]
        have hbr := qBracketPoly_split (R := R) (n := n) (k := k' + 1) (by omega)
        rw [show n + 1 - (k' + 1) = n - k' by omega] at hbr
        rw [← hbr, qFactorialPoly_succ]

end QBinomial

end Arith4Ext.GeneratingFunctions
