/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# `Arith4Ext.PolyInterpolation`: Reusable Tier A Polynomial Approximation & Interpolation Engine

Pure-Mathlib, zero-sorry, zero-custom-axiom library extending `Arithmetica4` with:
1. **Lagrange Interpolation & Vandermonde Uniqueness / Reproduction** over arbitrary fields `K`
   and injective node arrays `Fin n → K`.
2. **Chebyshev Polynomials `T_n` Exact Identities & Minimax Extremality** (`T_n(cos θ) = cos(nθ)`,
   `|T_n(x)| ≤ 1` on `[-1, 1]`, exact `n` roots `cos((2k+1)π/(2n))`, equioscillation points,
   and Chebyshev Minimax Theorem for monic polynomials of degree `n ≥ 1`).
3. **Bernstein Polynomials & Quantitative Popoviciu–Weierstrass Approximation** (exact moments
   `B_n(1) = 1`, `B_n(x) = x`, `B_n(x^2) = x^2 + x(1-x)/n`, exact variance identity, quantitative
   modulus-of-continuity bound, `O(n^{-1/2})` Lipschitz rate, and uniform Weierstrass convergence
   on `[0, 1]`).
4. **Lebesgue Constant Quasi-Optimality** (`‖L^n f - f‖_∞ ≤ (1 + Λ_n) E_{n-1}(f)`).
-/

namespace Arith4Ext.PolyInterpolation

noncomputable section

open scoped BigOperators

/-!
## 1. Lagrange Interpolation & Vandermonde Uniqueness / Reproduction
-/

section LagrangeVandermonde

variable {K : Type*} [Field K]

/-- The `i`-th Lagrange basis polynomial for nodes `x : Fin n → K`. -/
def lagrangeBasis {n : ℕ} (x : Fin n → K) (i : Fin n) : Polynomial K :=
  ∏ j ∈ Finset.univ.filter (· ≠ i),
    Polynomial.C ((x i - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))

/-- The Lagrange interpolating polynomial for nodes `x : Fin n → K` and values `y : Fin n → K`. -/
def lagrangeInterp {n : ℕ} (x : Fin n → K) (y : Fin n → K) : Polynomial K :=
  ∑ i : Fin n, Polynomial.C (y i) * lagrangeBasis x i

theorem lagrangeBasis_eval_self {n : ℕ} {x : Fin n → K} (hx : Function.Injective x) (i : Fin n) :
    (lagrangeBasis x i).eval (x i) = 1 := by
  dsimp only [lagrangeBasis]
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_one fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_filter.mp hj).2
  have hne : x i - x j ≠ 0 := sub_ne_zero.mpr fun h => hji (hx h).symm
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  exact inv_mul_cancel₀ hne

theorem lagrangeBasis_eval_ne {n : ℕ} (x : Fin n → K) {i j : Fin n} (hij : j ≠ i) :
    (lagrangeBasis x i).eval (x j) = 0 := by
  dsimp only [lagrangeBasis]
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩) ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    sub_self, mul_zero]

theorem lagrangeBasis_eval {n : ℕ} {x : Fin n → K} (hx : Function.Injective x) (i j : Fin n) :
    (lagrangeBasis x i).eval (x j) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h]; exact lagrangeBasis_eval_self hx i
  · exact lagrangeBasis_eval_ne x h

theorem lagrangeBasis_degree_lt {n : ℕ} (x : Fin n → K) (i : Fin n) :
    (lagrangeBasis x i).degree < (n : ℕ) := by
  dsimp only [lagrangeBasis]
  have hdeg_le : ∀ S : Finset (Fin n),
      (∏ j ∈ S, Polynomial.C ((x i - x j)⁻¹) * (Polynomial.X - Polynomial.C (x j))).degree ≤
        ((S.card : ℕ) : WithBot ℕ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      refine (Polynomial.degree_mul_le _ _).trans ?_
      have ha1 : (Polynomial.C ((x i - x a)⁻¹) * (Polynomial.X - Polynomial.C (x a))).degree ≤
          (1 : WithBot ℕ) := by
        refine (Polynomial.degree_mul_le _ _).trans ?_
        have hC : (Polynomial.C ((x i - x a)⁻¹)).degree ≤ 0 := Polynomial.degree_C_le
        have hX : (Polynomial.X - Polynomial.C (x a)).degree ≤ 1 := by
          refine (Polynomial.degree_sub_le _ _).trans ?_
          simp only [Polynomial.degree_X]
          exact max_le le_rfl (Polynomial.degree_C_le.trans (by decide))
        exact (add_le_add hC hX).trans (by simp)
      exact (add_le_add ha1 ih).trans_eq (add_comm _ _)
  have hcard : (Finset.univ.filter (· ≠ i)).card < n := by
    have hi : i ∉ Finset.univ.filter (· ≠ i) := by simp
    have hss : Finset.univ.filter (· ≠ i) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨i, Finset.mem_univ i, hi⟩
    simpa only [Finset.card_fin] using Finset.card_lt_card hss
  exact (hdeg_le _).trans_lt (WithBot.coe_lt_coe.mpr hcard)

theorem lagrangeBasis_natDegree_le {n : ℕ} (x : Fin n → K) (i : Fin n) :
    (lagrangeBasis x i).natDegree ≤ n - 1 := by
  by_cases h0 : lagrangeBasis x i = 0
  · simp [h0]
  · have hlt := lagrangeBasis_degree_lt x i
    have hnat : (lagrangeBasis x i).natDegree < n :=
      Nat.lt_of_not_ge fun hle => not_le_of_gt hlt
        (by rw [Polynomial.degree_eq_natDegree h0]; exact_mod_cast hle)
    omega

theorem lagrangeInterp_eval {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    (y : Fin n → K) (j : Fin n) :
    (lagrangeInterp x y).eval (x j) = y j := by
  dsimp only [lagrangeInterp]
  rw [Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_mul, Polynomial.eval_C, lagrangeBasis_eval hx]
  simp

theorem lagrangeInterp_degree_lt {n : ℕ} (x y : Fin n → K) :
    (lagrangeInterp x y).degree < (n : ℕ) := by
  dsimp only [lagrangeInterp]
  have hsum : ∀ S : Finset (Fin n),
      (∑ i ∈ S, Polynomial.C (y i) * lagrangeBasis x i).degree < (n : ℕ) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe n
    | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ih)
      refine (Polynomial.degree_mul_le _ _).trans_lt ?_
      have hC : (Polynomial.C (y a)).degree ≤ 0 := Polynomial.degree_C_le
      have h0 : (Polynomial.C (y a)).degree + (lagrangeBasis x a).degree ≤
          0 + (lagrangeBasis x a).degree := add_le_add hC le_rfl
      rw [zero_add] at h0
      exact h0.trans_lt (lagrangeBasis_degree_lt x a)
  exact hsum Finset.univ

theorem lagrangeInterp_natDegree_le {n : ℕ} (x y : Fin n → K) :
    (lagrangeInterp x y).natDegree ≤ n - 1 := by
  by_cases h0 : lagrangeInterp x y = 0
  · simp [h0]
  · have hlt := lagrangeInterp_degree_lt x y
    have hnat : (lagrangeInterp x y).natDegree < n :=
      Nat.lt_of_not_ge fun hle => not_le_of_gt hlt
        (by rw [Polynomial.degree_eq_natDegree h0]; exact_mod_cast hle)
    omega

/-- **Vandermonde / Polynomial Root-Counting Uniqueness:** any polynomial of degree `< n`
vanishing at `n` distinct nodes `x : Fin n → K` is identically zero. -/
theorem poly_eq_zero_of_eval_eq_zero {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    {P : Polynomial K} (hdeg : P.degree < (n : ℕ)) (heval : ∀ i : Fin n, P.eval (x i) = 0) :
    P = 0 := by
  classical
  by_contra hP
  have hsub : (Finset.univ.image x) ⊆ P.roots.toFinset := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr (heval i))
  have hcard1 : n ≤ (Finset.univ.image x).card := by
    rw [Finset.card_image_of_injective _ hx, Finset.card_fin]
  have hcard2 : (Finset.univ.image x).card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
  have hcard3 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
  have hcard4 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
  have hnat : P.natDegree < n :=
    Nat.lt_of_not_ge fun hle => not_le_of_gt hdeg
      (by rw [Polynomial.degree_eq_natDegree hP]; exact_mod_cast hle)
  omega

theorem poly_eq_of_eval_eq {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    {P Q : Polynomial K} (hP : P.degree < (n : ℕ)) (hQ : Q.degree < (n : ℕ))
    (heval : ∀ i : Fin n, P.eval (x i) = Q.eval (x i)) :
    P = Q := by
  have hsub : P - Q = 0 := by
    refine poly_eq_zero_of_eval_eq_zero hx ?_ ?_
    · refine (Polynomial.degree_sub_le P Q).trans_lt (max_lt hP hQ)
    · intro i; simp [heval i]
  exact sub_eq_zero.mp hsub

/-- Uniqueness of the degree `< n` Lagrange interpolant. -/
theorem lagrangeInterp_unique {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    (y : Fin n → K) {P : Polynomial K} (hP : P.degree < (n : ℕ))
    (heval : ∀ i : Fin n, P.eval (x i) = y i) :
    P = lagrangeInterp x y :=
  poly_eq_of_eval_eq hx hP (lagrangeInterp_degree_lt x y) fun i => by
    rw [heval i, lagrangeInterp_eval hx]

/-- Existence and uniqueness of the degree `< n` Lagrange interpolating polynomial. -/
theorem lagrangeInterp_exists_unique {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    (y : Fin n → K) :
    ∃! P : Polynomial K, P.degree < (n : ℕ) ∧ ∀ i : Fin n, P.eval (x i) = y i :=
  ⟨lagrangeInterp x y, ⟨lagrangeInterp_degree_lt x y, lagrangeInterp_eval hx y⟩,
    fun _ ⟨hdeg, heval⟩ => lagrangeInterp_unique hx y hdeg heval⟩

/-- **Lagrange Reproduction Identity:** Lagrange interpolation reproduces every polynomial of
degree `< n`. -/
theorem lagrangeInterp_reproduce {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    {P : Polynomial K} (hP : P.degree < (n : ℕ)) :
    lagrangeInterp x (fun i => P.eval (x i)) = P :=
  (lagrangeInterp_unique hx (fun i => P.eval (x i)) hP (fun _ => rfl)).symm

/-- **Lagrange Partition of Unity:** `∑ i, lagrangeBasis x i = 1` whenever `1 ≤ n`. -/
theorem sum_lagrangeBasis_eq_one {n : ℕ} (hn : 1 ≤ n) {x : Fin n → K}
    (hx : Function.Injective x) :
    ∑ i : Fin n, lagrangeBasis x i = 1 := by
  have h1 : (1 : Polynomial K).degree < (n : ℕ) := by
    rw [Polynomial.degree_one]
    exact WithBot.coe_lt_coe.mpr hn
  have hrep := lagrangeInterp_reproduce hx h1
  simpa only [lagrangeInterp, Polynomial.eval_one, Polynomial.C_1, one_mul] using hrep

/-- **Lagrange Monomial Moment Identity:** `∑ i, (x i)^m * l_i(X) = X^m` for all `m < n`. -/
theorem sum_pow_mul_lagrangeBasis_eq {n m : ℕ} (hm : m < n) {x : Fin n → K}
    (hx : Function.Injective x) :
    ∑ i : Fin n, Polynomial.C ((x i) ^ m) * lagrangeBasis x i = Polynomial.X ^ m := by
  have hX : (Polynomial.X ^ m : Polynomial K).degree < (n : ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact WithBot.coe_lt_coe.mpr hm
  have hrep := lagrangeInterp_reproduce hx hX
  simpa only [lagrangeInterp, Polynomial.eval_pow, Polynomial.eval_X] using hrep

/-- **Vandermonde Column Linear Independence:** for any injective nodes `x : Fin n → K`, the
Vandermonde columns `(x i ^ k)_{k < n}` are linearly independent over `K`. -/
theorem vandermonde_linear_indep {n : ℕ} {x : Fin n → K} (hx : Function.Injective x)
    (c : Fin n → K) (hc : ∀ k : Fin n, ∑ i : Fin n, c i * (x i) ^ (k : ℕ) = 0) :
    ∀ i : Fin n, c i = 0 := by
  intro i₀
  have hdeg : (lagrangeBasis x i₀).degree < (n : ℕ) := lagrangeBasis_degree_lt x i₀
  have heval_sum : ∀ y : K,
      (lagrangeBasis x i₀).eval y = ∑ k : Fin n, (lagrangeBasis x i₀).coeff k * y ^ (k : ℕ) := by
    intro y
    rw [Polynomial.eval_eq_sum_range]
    have hsplit : ∑ k ∈ Finset.range ((lagrangeBasis x i₀).natDegree + 1),
          (lagrangeBasis x i₀).coeff k * y ^ k =
        ∑ k ∈ Finset.range n, (lagrangeBasis x i₀).coeff k * y ^ k := by
      by_cases h0 : lagrangeBasis x i₀ = 0
      · simp [h0]
      · have hnat : (lagrangeBasis x i₀).natDegree < n :=
          Nat.lt_of_not_ge fun hle => not_le_of_gt hdeg
            (by rw [Polynomial.degree_eq_natDegree h0]; exact_mod_cast hle)
        refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
        intro k hk hkn
        rw [Finset.mem_range] at hk hkn
        have hlt : (lagrangeBasis x i₀).natDegree < k := by omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    rw [hsplit, ← Fin.sum_univ_eq_sum_range]
  calc
    c i₀ = ∑ i : Fin n, c i * (lagrangeBasis x i₀).eval (x i) := by
        simp [lagrangeBasis_eval hx]
    _ = ∑ i : Fin n, c i * ∑ k : Fin n, (lagrangeBasis x i₀).coeff k * (x i) ^ (k : ℕ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [heval_sum (x i)]
    _ = ∑ k : Fin n, (lagrangeBasis x i₀).coeff k * ∑ i : Fin n, c i * (x i) ^ (k : ℕ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hc k, mul_zero]

/-- Linearity of Lagrange interpolation in the target vector `y`. -/
theorem lagrangeInterp_add {n : ℕ} (x y z : Fin n → K) :
    lagrangeInterp x (y + z) = lagrangeInterp x y + lagrangeInterp x z := by
  dsimp only [lagrangeInterp]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Polynomial.C_add, add_mul]

theorem lagrangeInterp_smul {n : ℕ} (x : Fin n → K) (c : K) (y : Fin n → K) :
    lagrangeInterp x (fun i => c * y i) = Polynomial.C c * lagrangeInterp x y := by
  dsimp only [lagrangeInterp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.C_mul, mul_assoc]

end LagrangeVandermonde

/-!
## 2. Chebyshev Polynomials `T_n` Exact Identities & Minimax Extremality
-/

section Chebyshev

/-- Chebyshev polynomial of the first kind `T_n ∈ ℝ[X]`, defined by the standard
three-term recurrence `T_0 = 1`, `T_1 = X`, `T_{n+2} = 2 X T_{n+1} - T_n`. -/
def chebyshevT : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => 2 * Polynomial.X * chebyshevT (n + 1) - chebyshevT n

@[simp]
theorem chebyshevT_zero : chebyshevT 0 = 1 := rfl

@[simp]
theorem chebyshevT_one : chebyshevT 1 = Polynomial.X := rfl

theorem chebyshevT_succ_succ (n : ℕ) :
    chebyshevT (n + 2) = 2 * Polynomial.X * chebyshevT (n + 1) - chebyshevT n := rfl

/-- **Fundamental Trigonometric Identity:** `T_n(cos θ) = cos(n θ)` for all `n : ℕ` and `θ : ℝ`. -/
theorem chebyshevT_eval_cos (n : ℕ) (θ : ℝ) :
    (chebyshevT n).eval (Real.cos θ) = Real.cos ((n : ℝ) * θ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    rw [chebyshevT_succ_succ, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_X, ih1, ih0]
    have hadd := Real.cos_add (((n + 1 : ℕ) : ℝ) * θ) θ
    have hsub := Real.cos_sub (((n + 1 : ℕ) : ℝ) * θ) θ
    have h1 : (((n + 1 : ℕ) : ℝ) * θ) + θ = (((n + 2 : ℕ) : ℝ) * θ) := by push_cast; ring
    have h2 : (((n + 1 : ℕ) : ℝ) * θ) - θ = ((n : ℝ) * θ) := by push_cast; ring
    rw [h1] at hadd
    rw [h2] at hsub
    linarith

/-- `|T_n(x)| ≤ 1` for every `n : ℕ` and every `x ∈ [-1, 1]`. -/
theorem chebyshevT_abs_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(chebyshevT n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, chebyshevT_eval_cos]
  exact Real.abs_cos_le_one _

/-- Exact `natDegree` and `leadingCoeff` of `chebyshevT n`. -/
theorem chebyshevT_natDegree_and_leadingCoeff (n : ℕ) :
    (chebyshevT n).natDegree = n ∧
      (chebyshevT n).leadingCoeff = if n = 0 then 1 else (2 : ℝ) ^ (n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
    have hc_nz : chebyshevT (n + 1) ≠ 0 := by
      intro h0
      have hlc := ih1.2
      rw [h0, Polynomial.leadingCoeff_zero] at hlc
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel] at hlc
      exact absurd hlc.symm (pow_ne_zero n (by norm_num))
    have h2X_eq : (2 : Polynomial ℝ) * Polynomial.X = Polynomial.C 2 * Polynomial.X := by
      simp [Polynomial.C_ofNat]
    have h2X_nz : (2 : Polynomial ℝ) * Polynomial.X ≠ 0 := by
      rw [h2X_eq]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) Polynomial.X_ne_zero
    have h2X_deg : ((2 : Polynomial ℝ) * Polynomial.X).natDegree = 1 := by
      rw [h2X_eq, Polynomial.natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0), Polynomial.natDegree_X]
    have h2X_lc : ((2 : Polynomial ℝ) * Polynomial.X).leadingCoeff = 2 := by
      rw [h2X_eq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
        Polynomial.leadingCoeff_X, mul_one]
    have hmul_deg : ((2 : Polynomial ℝ) * Polynomial.X * chebyshevT (n + 1)).natDegree = n + 2 := by
      rw [Polynomial.natDegree_mul h2X_nz hc_nz, h2X_deg, ih1.1]
      ring
    have hmul_lc : ((2 : Polynomial ℝ) * Polynomial.X * chebyshevT (n + 1)).leadingCoeff =
        (2 : ℝ) ^ (n + 1) := by
      rw [Polynomial.leadingCoeff_mul, h2X_lc, ih1.2]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      ring
    have hlt : (chebyshevT n).natDegree <
        ((2 : Polynomial ℝ) * Polynomial.X * chebyshevT (n + 1)).natDegree := by
      rw [ih0.1, hmul_deg]; omega
    rw [chebyshevT_succ_succ]
    have hdeg_sub :
        (2 * Polynomial.X * chebyshevT (n + 1) - chebyshevT n).natDegree = n + 2 := by
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hmul_deg]
    refine ⟨hdeg_sub, ?_⟩
    have hzero : (chebyshevT n).coeff (n + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ih0.1]; omega)
    rw [Polynomial.leadingCoeff, hdeg_sub, Polynomial.coeff_sub, hzero, sub_zero]
    have hlc_eq : (2 * Polynomial.X * chebyshevT (n + 1)).coeff (n + 2) =
        (2 * Polynomial.X * chebyshevT (n + 1)).leadingCoeff := by
      rw [← hmul_deg]; rfl
    rw [hlc_eq, hmul_lc]
    simp

theorem chebyshevT_natDegree (n : ℕ) : (chebyshevT n).natDegree = n :=
  (chebyshevT_natDegree_and_leadingCoeff n).1

theorem chebyshevT_leadingCoeff {n : ℕ} (hn : 1 ≤ n) :
    (chebyshevT n).leadingCoeff = (2 : ℝ) ^ (n - 1) := by
  have h := (chebyshevT_natDegree_and_leadingCoeff n).2
  simpa [Nat.ne_of_gt hn] using h

/-- Monic Chebyshev polynomial `T̃_n = 2^{-(n-1)} T_n` for `n ≥ 1` (`T̃_0 = 1`). -/
def monicChebyshevT (n : ℕ) : Polynomial ℝ :=
  if n = 0 then 1 else Polynomial.C (((2 : ℝ) ^ (n - 1))⁻¹) * chebyshevT n

theorem monicChebyshevT_monic (n : ℕ) : (monicChebyshevT n).Monic := by
  dsimp only [monicChebyshevT]
  split_ifs with h0
  · exact Polynomial.monic_one
  · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      chebyshevT_leadingCoeff (Nat.pos_of_ne_zero h0)]
    exact inv_mul_cancel₀ (pow_ne_zero _ (by norm_num))

theorem monicChebyshevT_natDegree (n : ℕ) : (monicChebyshevT n).natDegree = n := by
  dsimp only [monicChebyshevT]
  split_ifs with h0
  · subst h0; simp
  · rw [Polynomial.natDegree_C_mul (inv_ne_zero (pow_ne_zero _ (by norm_num))),
      chebyshevT_natDegree]

theorem monicChebyshevT_abs_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(monicChebyshevT n).eval x| ≤ (2 : ℝ) ^ (1 - (n : ℤ)) := by
  dsimp only [monicChebyshevT]
  rw [if_neg (Nat.ne_of_gt hn), Polynomial.eval_mul, Polynomial.eval_C, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))]
  have hz : (2 : ℝ) ^ (1 - (n : ℤ)) = ((2 : ℝ) ^ (n - 1))⁻¹ := by
    rw [show (1 - (n : ℤ)) = -((n - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  rw [hz]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (chebyshevT_abs_le_one n hx)
    (inv_nonneg.mpr (pow_nonneg (by norm_num) _))

/-- The `k`-th Chebyshev root (`k = 0, ..., n - 1`): `cos((2k + 1)π / (2n))`. -/
def chebyshevNode (n k : ℕ) : ℝ :=
  Real.cos (((2 * k + 1 : ℕ) : ℝ) * Real.pi / (2 * n : ℝ))

theorem chebyshevNode_mem_Icc {n k : ℕ} :
    chebyshevNode n k ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem chebyshevNode_eval {n k : ℕ} (hn : 1 ≤ n) :
    (chebyshevT n).eval (chebyshevNode n k) = 0 := by
  dsimp only [chebyshevNode]
  rw [chebyshevT_eval_cos]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have harg : (n : ℝ) * (((2 * k + 1 : ℕ) : ℝ) * Real.pi / (2 * n : ℝ)) =
      Real.pi / 2 + (k : ℝ) * Real.pi := by
    push_cast
    field_simp [hn_ne]
    ring
  rw [harg, Real.cos_add, Real.cos_pi_div_two, zero_mul, Real.sin_pi_div_two, one_mul,
    Real.sin_nat_mul_pi, sub_zero]

theorem chebyshevNode_strictAnti {n : ℕ} (hn : 1 ≤ n) {j k : ℕ} (hjk : j < k) (hk : k < n) :
    chebyshevNode n k < chebyshevNode n j := by
  dsimp only [chebyshevNode]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hj_mem : ((2 * j + 1 : ℕ) : ℝ) * Real.pi / (2 * n : ℝ) ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      have : ((2 * j + 1 : ℕ) : ℝ) ≤ (2 * n : ℝ) := by exact_mod_cast (by omega : 2 * j + 1 ≤ 2 * n)
      nlinarith [Real.pi_pos]
  have hk_mem : ((2 * k + 1 : ℕ) : ℝ) * Real.pi / (2 * n : ℝ) ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      have : ((2 * k + 1 : ℕ) : ℝ) ≤ (2 * n : ℝ) := by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * n)
      nlinarith [Real.pi_pos]
  have hlt : ((2 * j + 1 : ℕ) : ℝ) * Real.pi / (2 * n : ℝ) <
      ((2 * k + 1 : ℕ) : ℝ) * Real.pi / (2 * n : ℝ) := by
    refine div_lt_div_of_pos_right ?_ (by positivity)
    have hnum : ((2 * j + 1 : ℕ) : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * j + 1 < 2 * k + 1)
    exact mul_lt_mul_of_pos_right hnum Real.pi_pos
  exact Real.strictAntiOn_cos hj_mem hk_mem hlt

theorem chebyshevNode_injective {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective (fun k : Fin n => chebyshevNode n k) := by
  intro j k hEq
  rcases lt_trichotomy (j : ℕ) (k : ℕ) with hlt | heq | hgt
  · exact False.elim ((chebyshevNode_strictAnti hn hlt k.isLt).ne hEq.symm)
  · exact Fin.ext heq
  · exact False.elim ((chebyshevNode_strictAnti hn hgt j.isLt).ne hEq)

/-- Exact `n` distinct roots of `chebyshevT n` on `[-1, 1]` via `Fin n → chebyshevNode n`. -/
theorem chebyshevT_roots_card {n : ℕ} (hn : 1 ≤ n) :
    (Finset.univ.image (fun k : Fin n => chebyshevNode n k)).card = n ∧
      ∀ k : Fin n, chebyshevNode n k ∈ Set.Icc (-1 : ℝ) 1 ∧
        (chebyshevT n).eval (chebyshevNode n k) = 0 := by
  refine ⟨?_, fun k => ⟨chebyshevNode_mem_Icc, chebyshevNode_eval hn⟩⟩
  rw [Finset.card_image_of_injective _ (chebyshevNode_injective hn), Finset.card_fin]

/-- The `k`-th Chebyshev equioscillation point (`k = 0, ..., n`): `cos(k π / n)`. -/
def chebyshevExtremum (n k : ℕ) : ℝ :=
  Real.cos ((k : ℝ) * Real.pi / (n : ℝ))

theorem chebyshevExtremum_mem_Icc {n k : ℕ} :
    chebyshevExtremum n k ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem chebyshevExtremum_eval {n k : ℕ} (hn : 1 ≤ n) :
    (chebyshevT n).eval (chebyshevExtremum n k) = (-1 : ℝ) ^ k := by
  dsimp only [chebyshevExtremum]
  rw [chebyshevT_eval_cos]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [show (n : ℝ) * ((k : ℝ) * Real.pi / (n : ℝ)) = (k : ℝ) * Real.pi by field_simp [hn_ne]]
  exact Real.cos_nat_mul_pi k

theorem chebyshevExtremum_strictAnti {n : ℕ} (hn : 1 ≤ n) {j k : ℕ} (hjk : j < k) (hk : k ≤ n) :
    chebyshevExtremum n k < chebyshevExtremum n j := by
  dsimp only [chebyshevExtremum]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hj_mem : (j : ℝ) * Real.pi / (n : ℝ) ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · rw [div_le_iff₀ hn_pos]
      have : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : j ≤ n)
      nlinarith [Real.pi_pos]
  have hk_mem : (k : ℝ) * Real.pi / (n : ℝ) ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · rw [div_le_iff₀ hn_pos]
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      nlinarith [Real.pi_pos]
  have hlt : (j : ℝ) * Real.pi / (n : ℝ) < (k : ℝ) * Real.pi / (n : ℝ) := by
    refine div_lt_div_of_pos_right ?_ hn_pos
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hjk) Real.pi_pos
  exact Real.strictAntiOn_cos hj_mem hk_mem hlt

/-- **Chebyshev Minimax Theorem:** Every monic polynomial `P ∈ ℝ[X]` of degree `n ≥ 1`
satisfies `sup_{x ∈ [-1, 1]} |P(x)| ≥ 2^{1 - n}`. -/
theorem chebyshev_minimax_monic {n : ℕ} (hn : 1 ≤ n) {P : Polynomial ℝ}
    (hP_monic : P.Monic) (hP_deg : P.natDegree = n) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, (2 : ℝ) ^ (1 - (n : ℤ)) ≤ |P.eval x| := by
  by_contra hlt
  push Not at hlt
  set M : ℝ := (2 : ℝ) ^ (1 - (n : ℤ))
  have hM_pos : 0 < M := by positivity
  set Q : Polynomial ℝ := monicChebyshevT n - P
  have hQ_coeff_ge : ∀ m : ℕ, n ≤ m → Q.coeff m = 0 := by
    intro m hm
    dsimp only [Q]
    rw [Polynomial.coeff_sub]
    rcases eq_or_lt_of_le hm with hmn | hgt
    · rw [← hmn]
      have hc1 : (monicChebyshevT n).coeff n = 1 := by
        nth_rw 2 [← monicChebyshevT_natDegree n]
        exact (monicChebyshevT_monic n).leadingCoeff
      have hc2 : P.coeff n = 1 := by
        rw [← hP_deg]
        exact hP_monic.leadingCoeff
      linarith
    · have hc1 : (monicChebyshevT n).coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt ((monicChebyshevT_natDegree n).symm ▸ hgt)
      have hc2 : P.coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (hP_deg.symm ▸ hgt)
      linarith
  have hT_eval : ∀ k : ℕ, (monicChebyshevT n).eval (chebyshevExtremum n k) = M * (-1 : ℝ) ^ k := by
    intro k
    dsimp only [monicChebyshevT]
    rw [if_neg (Nat.ne_of_gt hn), Polynomial.eval_mul, Polynomial.eval_C,
      chebyshevExtremum_eval hn]
    have hM_eq : M = ((2 : ℝ) ^ (n - 1))⁻¹ := by
      dsimp only [M]
      rw [show (1 - (n : ℤ)) = -((n - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    rw [hM_eq]
  have hQ_sign : ∀ k : ℕ, k ≤ n →
      (Even k → 0 < Q.eval (chebyshevExtremum n k)) ∧
      (Odd k → Q.eval (chebyshevExtremum n k) < 0) := by
    intro k _
    have hP_lt := hlt (chebyshevExtremum n k) chebyshevExtremum_mem_Icc
    have hP_abs := abs_lt.mp hP_lt
    have hQ_eq : Q.eval (chebyshevExtremum n k) =
        M * (-1 : ℝ) ^ k - P.eval (chebyshevExtremum n k) := by
      dsimp only [Q]; rw [Polynomial.eval_sub, hT_eval k]
    constructor
    · intro hev
      rw [hQ_eq, Even.neg_one_pow hev, mul_one]
      linarith
    · intro hodd
      rw [hQ_eq, Odd.neg_one_pow hodd, mul_neg, mul_one]
      linarith
  have hQ_ne : Q ≠ 0 := by
    intro h0
    have hpos := (hQ_sign 0 (Nat.zero_le n)).1 (by exact ⟨0, rfl⟩)
    rw [h0, Polynomial.eval_zero] at hpos
    exact lt_irrefl 0 hpos
  have hQ_deg : Q.natDegree < n := by
    by_contra hge
    push Not at hge
    have hlc := hQ_coeff_ge Q.natDegree hge
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ_ne hlc
  have hroots_ex : ∀ k : Fin n,
      ∃ r ∈ Set.Ioo (chebyshevExtremum n (k + 1)) (chebyshevExtremum n k), Q.eval r = 0 := by
    intro k
    have hk_lt : (k : ℕ) < n := k.isLt
    have hord : chebyshevExtremum n (k + 1) ≤ chebyshevExtremum n k :=
      (chebyshevExtremum_strictAnti hn (Nat.lt_succ_self k) (by omega)).le
    have hcont : ContinuousOn (fun x => Q.eval x)
        (Set.Icc (chebyshevExtremum n (k + 1)) (chebyshevExtremum n k)) :=
      Q.continuous.continuousOn
    rcases Nat.even_or_odd (k : ℕ) with hev | hodd
    · have h0 : 0 < Q.eval (chebyshevExtremum n k) := (hQ_sign k hk_lt.le).1 hev
      have h1 : Q.eval (chebyshevExtremum n (k + 1)) < 0 :=
        (hQ_sign (k + 1) (by omega)).2 (by simpa using hev.add_one)
      exact intermediate_value_Ioo hord hcont ⟨h1, h0⟩
    · have h0 : Q.eval (chebyshevExtremum n k) < 0 := (hQ_sign k hk_lt.le).2 hodd
      have h1 : 0 < Q.eval (chebyshevExtremum n (k + 1)) :=
        (hQ_sign (k + 1) (by omega)).1 (by simpa using hodd.add_one)
      exact intermediate_value_Ioo' hord hcont ⟨h0, h1⟩
  choose r hr_mem hr_zero using hroots_ex
  have hr_inj : Function.Injective r := by
    intro j k hEq
    rcases lt_trichotomy (j : ℕ) (k : ℕ) with hlt | heq | hgt
    · have hj_lt := (hr_mem j).1
      have hk_lt := (hr_mem k).2
      have hmid : chebyshevExtremum n k ≤ chebyshevExtremum n (j + 1) := by
        rcases eq_or_lt_of_le (by omega : (j : ℕ) + 1 ≤ k) with h1 | h1
        · rw [h1]
        · exact (chebyshevExtremum_strictAnti hn h1 k.isLt.le).le
      have hstrict : r k < r j := (hk_lt.trans_le hmid).trans hj_lt
      exact False.elim (hstrict.ne hEq.symm)
    · exact Fin.ext heq
    · have hk_lt := (hr_mem k).1
      have hj_lt := (hr_mem j).2
      have hmid : chebyshevExtremum n j ≤ chebyshevExtremum n (k + 1) := by
        rcases eq_or_lt_of_le (by omega : (k : ℕ) + 1 ≤ j) with h1 | h1
        · rw [h1]
        · exact (chebyshevExtremum_strictAnti hn h1 j.isLt.le).le
      have hstrict : r j < r k := (hj_lt.trans_le hmid).trans hk_lt
      exact False.elim (hstrict.ne hEq)
  have hsub : (Finset.univ.image r) ⊆ Q.roots.toFinset := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ_ne).mpr (hr_zero k))
  have hcard1 : n = (Finset.univ.image r).card := by
    rw [Finset.card_image_of_injective _ hr_inj, Finset.card_fin]
  have hcard2 : (Finset.univ.image r).card ≤ Q.roots.toFinset.card := Finset.card_le_card hsub
  have hcard3 : Q.roots.toFinset.card ≤ Q.roots.card := Multiset.toFinset_card_le _
  have hcard4 : Q.roots.card ≤ Q.natDegree := Polynomial.card_roots' Q
  omega

/-- Scaled **Chebyshev Minimax Theorem** for any degree `n ≥ 1` polynomial `P ∈ ℝ[X]`
(not necessarily monic). -/
theorem chebyshev_minimax_general {n : ℕ} (hn : 1 ≤ n) {P : Polynomial ℝ}
    (hP_deg : P.natDegree = n) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, |P.leadingCoeff| * (2 : ℝ) ^ (1 - (n : ℤ)) ≤ |P.eval x| := by
  have hP_ne : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hP_deg
    omega
  have hlc_ne : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
  set P₀ : Polynomial ℝ := Polynomial.C (P.leadingCoeff⁻¹) * P
  have hP0_monic : P₀.Monic := by
    dsimp only [P₀]
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact inv_mul_cancel₀ hlc_ne
  have hP0_deg : P₀.natDegree = n := by
    dsimp only [P₀]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc_ne), hP_deg]
  rcases chebyshev_minimax_monic hn hP0_monic hP0_deg with ⟨x, hx, hbx⟩
  refine ⟨x, hx, ?_⟩
  dsimp only [P₀] at hbx
  rw [Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_inv] at hbx
  have habs_pos : 0 < |P.leadingCoeff| := abs_pos.mpr hlc_ne
  calc
    |P.leadingCoeff| * (2 : ℝ) ^ (1 - (n : ℤ))
      ≤ |P.leadingCoeff| * (|P.leadingCoeff|⁻¹ * |P.eval x|) :=
        mul_le_mul_of_nonneg_left hbx habs_pos.le
    _ = |P.eval x| := by
        rw [← mul_assoc, mul_inv_cancel₀ habs_pos.ne', one_mul]

end Chebyshev

/-!
## 3. Bernstein Polynomials & Quantitative Popoviciu–Weierstrass Approximation
-/

section Bernstein

/-- The `n`-th Bernstein operator `B_n(f)(x)` on `[0, 1]`. -/
def bernsteinPoly (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f ((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)

/-- As an explicit element of `ℝ[X]` of degree `≤ n`. -/
def bernsteinPolynomial (n : ℕ) (f : ℝ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (f ((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ)) *
      Polynomial.X ^ k * (1 - Polynomial.X) ^ (n - k)

theorem bernsteinPolynomial_eval (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (bernsteinPolynomial n f).eval x = bernsteinPoly n f x := by
  dsimp only [bernsteinPolynomial, bernsteinPoly]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]

theorem bernsteinPolynomial_natDegree_le (n : ℕ) (f : ℝ → ℝ) :
    (bernsteinPolynomial n f).natDegree ≤ n := by
  dsimp only [bernsteinPolynomial]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine Polynomial.natDegree_mul_le.trans ?_
  have h1 : (Polynomial.C (f ((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ)) *
      Polynomial.X ^ k).natDegree ≤ k := by
    refine Polynomial.natDegree_mul_le.trans ?_
    have hC : (Polynomial.C (f ((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ))).natDegree = 0 :=
      Polynomial.natDegree_C _
    have hX : (Polynomial.X ^ k : Polynomial ℝ).natDegree = k := Polynomial.natDegree_X_pow k
    rw [hC, hX, zero_add]
  have h2 : ((1 - Polynomial.X : Polynomial ℝ) ^ (n - k)).natDegree ≤ n - k := by
    refine Polynomial.natDegree_pow_le.trans ?_
    have h1X : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp
    exact (Nat.mul_le_mul_left (n - k) h1X).trans_eq (mul_one _)
  exact (add_le_add h1 h2).trans (by omega)

private lemma mul_choose_eq_choose_pred {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * Nat.choose n k = n * Nat.choose (n - 1) (k - 1) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hkn
  have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : k - 1 ≤ n - 1)
  have hsub : n - 1 - (k - 1) = n - k := by omega
  rw [hsub] at h2
  have hpos : 0 < Nat.factorial (k - 1) * Nat.factorial (n - k) :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.mul_right_cancel hpos
  calc
    k * Nat.choose n k * (Nat.factorial (k - 1) * Nat.factorial (n - k))
      = Nat.choose n k * (k * Nat.factorial (k - 1)) * Nat.factorial (n - k) := by ring
    _ = Nat.choose n k * Nat.factorial k * Nat.factorial (n - k) := by
        rw [Nat.mul_factorial_pred (by omega : k ≠ 0)]
    _ = Nat.factorial n := h1
    _ = n * Nat.factorial (n - 1) := by
        rw [← Nat.mul_factorial_pred (by omega : n ≠ 0)]
    _ = n * (Nat.choose (n - 1) (k - 1) * Nat.factorial (k - 1) * Nat.factorial (n - k)) := by
        rw [h2]
    _ = n * Nat.choose (n - 1) (k - 1) * (Nat.factorial (k - 1) * Nat.factorial (n - k)) := by ring

theorem bernsteinPoly_const (n : ℕ) (c x : ℝ) :
    bernsteinPoly n (fun _ => c) x = c := by
  dsimp only [bernsteinPoly]
  calc
    ∑ k ∈ Finset.range (n + 1), c * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)
      = c * ∑ k ∈ Finset.range (n + 1), x ^ k * (1 - x) ^ (n - k) * (Nat.choose n k : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ = c * (x + (1 - x)) ^ n := by rw [← add_pow x (1 - x) n]
    _ = c := by simp

theorem bernsteinPoly_one (n : ℕ) (x : ℝ) :
    bernsteinPoly n (fun _ => 1) x = 1 :=
  bernsteinPoly_const n 1 x

theorem bernsteinPoly_id {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    bernsteinPoly n (fun t => t) x = x := by
  dsimp only [bernsteinPoly]
  have hIcc : Finset.range (n + 1) = insert 0 ((Finset.Icc 1 n)) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hnot0 : 0 ∉ Finset.Icc 1 n := by simp
  rw [hIcc, Finset.sum_insert hnot0]
  simp only [Nat.cast_zero, zero_div, zero_mul, zero_add]
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      (k : ℝ) / (n : ℝ) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
        x * ((Nat.choose (n - 1) (k - 1) : ℝ) * x ^ (k - 1) * (1 - x) ^ ((n - 1) - (k - 1))) := by
    intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkn⟩
    have hid : (k : ℝ) * (Nat.choose n k : ℝ) = (n : ℝ) * (Nat.choose (n - 1) (k - 1) : ℝ) := by
      exact_mod_cast mul_choose_eq_choose_pred hn hk1 hkn
    have hxk : x ^ k = x * x ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    have hnk : n - k = (n - 1) - (k - 1) := by omega
    rw [hxk, hnk]
    calc
      (k : ℝ) / (n : ℝ) * (Nat.choose n k : ℝ) * (x * x ^ (k - 1)) * (1 - x) ^ (n - 1 - (k - 1))
        = ((k : ℝ) * (Nat.choose n k : ℝ)) / (n : ℝ) * x * x ^ (k - 1) *
            (1 - x) ^ (n - 1 - (k - 1)) := by ring
      _ = ((n : ℝ) * (Nat.choose (n - 1) (k - 1) : ℝ)) / (n : ℝ) * x * x ^ (k - 1) *
            (1 - x) ^ (n - 1 - (k - 1)) := by rw [hid]
      _ = x * ((Nat.choose (n - 1) (k - 1) : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - 1 - (k - 1))) := by
            field_simp [hn_ne]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hreindex :
      ∑ k ∈ Finset.Icc 1 n,
          (Nat.choose (n - 1) (k - 1) : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - 1 - (k - 1)) =
        ∑ m ∈ Finset.range ((n - 1) + 1),
          (Nat.choose (n - 1) m : ℝ) * x ^ m * (1 - x) ^ (n - 1 - m) := by
    refine Finset.sum_bij' (fun k _ => k - 1) (fun m _ => m + 1)
      (fun k hk => ?_) (fun m hm => ?_) (fun k hk => ?_) (fun m hm => ?_) (fun _ _ => rfl)
    · simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
    · simp only [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
    · simp only [Finset.mem_Icc] at hk; omega
    · simp only [Finset.mem_range] at hm; omega
  rw [hreindex]
  have h1 := bernsteinPoly_one (n - 1) x
  dsimp only [bernsteinPoly] at h1
  simp only [one_mul] at h1
  rw [h1, mul_one]

theorem bernsteinPoly_sq {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    bernsteinPoly n (fun t => t ^ 2) x = x ^ 2 + x * (1 - x) / (n : ℝ) := by
  by_cases hn1 : n = 1
  · subst hn1
    dsimp only [bernsteinPoly]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp
    ring
  have hn2 : 2 ≤ n := by omega
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  dsimp only [bernsteinPoly]
  have hIcc : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have hnot0 : 0 ∉ Finset.Icc 1 n := by simp
  rw [hIcc, Finset.sum_insert hnot0]
  simp only [Nat.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_mul, zero_add]
  have hIcc1 : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hnot1 : 1 ∉ Finset.Icc 2 n := by simp
  have hsplit : ∑ k ∈ Finset.Icc 1 n,
        ((k : ℝ) / (n : ℝ)) ^ 2 * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
      (∑ k ∈ Finset.Icc 2 n,
        ((k : ℝ) * ((k : ℝ) - 1) / (n : ℝ) ^ 2) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)) +
      (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n,
        ((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) := by
    have hsplit1 : ∑ k ∈ Finset.Icc 1 n,
          ((k : ℝ) / (n : ℝ)) ^ 2 * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
        ∑ k ∈ Finset.Icc 1 n,
          (((k : ℝ) * ((k : ℝ) - 1) / (n : ℝ) ^ 2) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) +
           (1 / (n : ℝ)) * (((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k))) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp [hn_ne]
      ring
    rw [hsplit1, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [hIcc1, Finset.sum_insert hnot1]
    simp
  rw [hsplit]
  have hlin_sum : ∑ k ∈ Finset.Icc 1 n,
        ((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) = x := by
    have hid := bernsteinPoly_id hn x
    dsimp only [bernsteinPoly] at hid
    have hIcc0 : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hIcc0, Finset.sum_insert hnot0] at hid
    simpa using hid
  have hquad_sum : ∑ k ∈ Finset.Icc 2 n,
        ((k : ℝ) * ((k : ℝ) - 1) / (n : ℝ) ^ 2) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
      ((n - 1 : ℝ) / (n : ℝ)) * x ^ 2 := by
    have hterm2 : ∀ k ∈ Finset.Icc 2 n,
        ((k : ℝ) * ((k : ℝ) - 1) / (n : ℝ) ^ 2) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
          (((n - 1 : ℝ) / (n : ℝ)) * x ^ 2) *
            ((Nat.choose (n - 2) (k - 2) : ℝ) * x ^ (k - 2) * (1 - x) ^ ((n - 2) - (k - 2))) := by
      intro k hk
      rcases Finset.mem_Icc.mp hk with ⟨hk2, hkn⟩
      have hid1 := mul_choose_eq_choose_pred hn (by omega : 1 ≤ k) hkn
      have hid2 := mul_choose_eq_choose_pred (by omega : 1 ≤ n - 1) (by omega : 1 ≤ k - 1)
        (by omega : k - 1 ≤ n - 1)
      have hmul_nat : k * (k - 1) * Nat.choose n k =
          n * (n - 1) * Nat.choose (n - 2) (k - 2) := by
        calc
          k * (k - 1) * Nat.choose n k = (k - 1) * (k * Nat.choose n k) := by ring
          _ = (k - 1) * (n * Nat.choose (n - 1) (k - 1)) := by rw [hid1]
          _ = n * ((k - 1) * Nat.choose (n - 1) (k - 1)) := by ring
          _ = n * ((n - 1) * Nat.choose (n - 1 - 1) (k - 1 - 1)) := by rw [hid2]
          _ = n * (n - 1) * Nat.choose (n - 2) (k - 2) := by
              rw [show n - 1 - 1 = n - 2 by omega, show k - 1 - 1 = k - 2 by omega]; ring
      have hmul_r : (k : ℝ) * ((k : ℝ) - 1) * (Nat.choose n k : ℝ) =
          (n : ℝ) * ((n : ℝ) - 1) * (Nat.choose (n - 2) (k - 2) : ℝ) := by
        have hm := congrArg (Nat.cast (R := ℝ)) hmul_nat
        push_cast [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub hn] at hm
        exact hm
      have hxk : x ^ k = x ^ 2 * x ^ (k - 2) := by
        conv_lhs => rw [show k = 2 + (k - 2) by omega, pow_add]
      have hnk : n - k = (n - 2) - (k - 2) := by omega
      rw [hxk, hnk]
      calc
        ((k : ℝ) * ((k : ℝ) - 1) / (n : ℝ) ^ 2) * (Nat.choose n k : ℝ) * (x ^ 2 * x ^ (k - 2)) *
            (1 - x) ^ (n - 2 - (k - 2))
          = ((k : ℝ) * ((k : ℝ) - 1) * (Nat.choose n k : ℝ)) / (n : ℝ) ^ 2 * x ^ 2 *
              x ^ (k - 2) * (1 - x) ^ (n - 2 - (k - 2)) := by ring
        _ = ((n : ℝ) * ((n : ℝ) - 1) * (Nat.choose (n - 2) (k - 2) : ℝ)) / (n : ℝ) ^ 2 * x ^ 2 *
              x ^ (k - 2) * (1 - x) ^ (n - 2 - (k - 2)) := by rw [hmul_r]
        _ = (((n - 1 : ℝ) / (n : ℝ)) * x ^ 2) *
              ((Nat.choose (n - 2) (k - 2) : ℝ) * x ^ (k - 2) * (1 - x) ^ (n - 2 - (k - 2))) := by
              field_simp [hn_ne]
    rw [Finset.sum_congr rfl hterm2, ← Finset.mul_sum]
    have hreindex :
        ∑ k ∈ Finset.Icc 2 n,
            (Nat.choose (n - 2) (k - 2) : ℝ) * x ^ (k - 2) * (1 - x) ^ (n - 2 - (k - 2)) =
          ∑ m ∈ Finset.range ((n - 2) + 1),
            (Nat.choose (n - 2) m : ℝ) * x ^ m * (1 - x) ^ (n - 2 - m) := by
      refine Finset.sum_bij' (fun k _ => k - 2) (fun m _ => m + 2)
        (fun k hk => ?_) (fun m hm => ?_) (fun k hk => ?_) (fun m hm => ?_) (fun _ _ => rfl)
      · simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
      · simp only [Finset.mem_range] at hm; simp only [Finset.mem_Icc]; omega
      · simp only [Finset.mem_Icc] at hk; omega
      · simp only [Finset.mem_range] at hm; omega
    rw [hreindex]
    have h1 := bernsteinPoly_one (n - 2) x
    dsimp only [bernsteinPoly] at h1
    simp only [one_mul] at h1
    rw [h1, mul_one]
  rw [hquad_sum, hlin_sum]
  field_simp [hn_ne]
  ring

/-- **Exact Bernstein Variance Identity:** for all `n ≥ 1` and `x : ℝ`,
`∑_{k=0}^n (k/n - x)^2 C(n,k) x^k (1 - x)^{n-k} = x(1 - x) / n`. -/
theorem bernsteinPoly_variance {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        ((k : ℝ) / (n : ℝ) - x) ^ 2 * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
      x * (1 - x) / (n : ℝ) := by
  have hexp : ∀ k : ℕ,
      ((k : ℝ) / (n : ℝ) - x) ^ 2 * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) =
        ((k : ℝ) / (n : ℝ)) ^ 2 * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k) -
          2 * x * (((k : ℝ) / (n : ℝ)) * (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)) +
          x ^ 2 * ((Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)) := by
    intro k; ring
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 := bernsteinPoly_sq hn x
  have h1 := bernsteinPoly_id hn x
  have h0 := bernsteinPoly_one n x
  dsimp only [bernsteinPoly] at h2 h1 h0
  simp only [one_mul] at h0
  rw [h2, h1, h0]
  ring

/-- **Quantitative Popoviciu–Weierstrass Bound:** if `f` has local oscillation `≤ ε` at scale `δ > 0`
on `[0, 1]` and `|f| ≤ M` on `[0, 1]`, then for all `n ≥ 1` and `x ∈ [0, 1]`:
`|B_n(f, x) - f x| ≤ ε + 2 M · x(1 - x)/(n δ^2) ≤ ε + M / (2 n δ^2)`. -/
theorem bernsteinPoly_abs_sub_le_popoviciu {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ)
    {δ ε M : ℝ} (hδ : 0 < δ) (hM_nn : 0 ≤ M)
    (hosc : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |y - z| ≤ δ → |f y - f z| ≤ ε)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernsteinPoly n f x - f x| ≤ ε + 2 * M * (x * (1 - x) / ((n : ℝ) * δ ^ 2)) ∧
      |bernsteinPoly n f x - f x| ≤ ε + M / (2 * (n : ℝ) * δ ^ 2) := by
  have hε_nn : 0 ≤ ε := by
    have := hosc x hx x hx (by simp; exact hδ.le)
    simpa using this
  let w : ℕ → ℝ := fun k => (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)
  have hw_nn : ∀ k : ℕ, 0 ≤ w k := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
      (pow_nonneg (sub_nonneg.mpr hx.2) _)
  have hw_sum : ∑ k ∈ Finset.range (n + 1), w k = 1 := by
    have h := bernsteinPoly_one n x
    dsimp only [bernsteinPoly] at h
    simpa only [one_mul] using h
  have hdiff_eq : bernsteinPoly n f x - f x =
      ∑ k ∈ Finset.range (n + 1), (f ((k : ℝ) / (n : ℝ)) - f x) * w k := by
    have hfx : f x = ∑ k ∈ Finset.range (n + 1), f x * w k := by
      rw [← Finset.mul_sum, hw_sum, mul_one]
    dsimp only [bernsteinPoly]
    conv_lhs => rhs; rw [hfx]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by dsimp only [w]; ring
  have hpt : ∀ k ∈ Finset.range (n + 1),
      |(f ((k : ℝ) / (n : ℝ)) - f x) * w k| ≤
        (ε + 2 * M / δ ^ 2 * ((k : ℝ) / (n : ℝ) - x) ^ 2) * w k := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkn_mem : (k : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      refine ⟨div_nonneg (Nat.cast_nonneg k) hn_pos.le, ?_⟩
      rw [div_le_one hn_pos]
      exact_mod_cast hkn
    rw [abs_mul, abs_of_nonneg (hw_nn k)]
    refine mul_le_mul_of_nonneg_right ?_ (hw_nn k)
    by_cases hnear : |(k : ℝ) / (n : ℝ) - x| ≤ δ
    · have h1 := hosc _ hkn_mem x hx hnear
      have h2 : 0 ≤ 2 * M / δ ^ 2 * ((k : ℝ) / (n : ℝ) - x) ^ 2 := by positivity
      linarith
    · push Not at hnear
      have hsq : 1 ≤ ((k : ℝ) / (n : ℝ) - x) ^ 2 / δ ^ 2 := by
        rw [one_le_div (pow_pos hδ 2), ← sq_abs ((k : ℝ) / (n : ℝ) - x)]
        exact sq_le_sq' (by linarith) hnear.le
      have h2M : |f ((k : ℝ) / (n : ℝ)) - f x| ≤ 2 * M := by
        calc
          |f ((k : ℝ) / (n : ℝ)) - f x|
            ≤ |f ((k : ℝ) / (n : ℝ))| + |f x| := by
                rw [sub_eq_add_neg]
                exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
          _ ≤ M + M := add_le_add (hbound _ hkn_mem) (hbound x hx)
          _ = 2 * M := by ring
      calc
        |f ((k : ℝ) / (n : ℝ)) - f x|
          ≤ 2 * M := h2M
        _ = (2 * M) * 1 := by ring
        _ ≤ (2 * M) * (((k : ℝ) / (n : ℝ) - x) ^ 2 / δ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 2 * M / δ ^ 2 * ((k : ℝ) / (n : ℝ) - x) ^ 2 := by ring
        _ ≤ ε + 2 * M / δ ^ 2 * ((k : ℝ) / (n : ℝ) - x) ^ 2 := le_add_of_nonneg_left hε_nn
  have h1 : |bernsteinPoly n f x - f x| ≤ ε + 2 * M * (x * (1 - x) / ((n : ℝ) * δ ^ 2)) := by
    rw [hdiff_eq]
    calc
      |∑ k ∈ Finset.range (n + 1), (f ((k : ℝ) / (n : ℝ)) - f x) * w k|
        ≤ ∑ k ∈ Finset.range (n + 1), |(f ((k : ℝ) / (n : ℝ)) - f x) * w k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1),
            (ε + 2 * M / δ ^ 2 * ((k : ℝ) / (n : ℝ) - x) ^ 2) * w k :=
          Finset.sum_le_sum hpt
      _ = ε * (∑ k ∈ Finset.range (n + 1), w k) +
            (2 * M / δ ^ 2) * ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / (n : ℝ) - x) ^ 2 * w k := by
          have heq : ∀ k : ℕ, (ε + 2 * M / δ ^ 2 * ((k : ℝ) / (n : ℝ) - x) ^ 2) * w k =
              ε * w k + (2 * M / δ ^ 2) * (((k : ℝ) / (n : ℝ) - x) ^ 2 * w k) := fun k => by ring
          simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = ε * 1 + (2 * M / δ ^ 2) * (x * (1 - x) / (n : ℝ)) := by
          rw [hw_sum]
          congr 2
          simpa only [w, mul_assoc] using bernsteinPoly_variance hn x
      _ = ε + 2 * M * (x * (1 - x) / ((n : ℝ) * δ ^ 2)) := by ring
  refine ⟨h1, h1.trans ?_⟩
  have hquarter : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2 : 2 * M * (x * (1 - x) / ((n : ℝ) * δ ^ 2)) ≤ M / (2 * (n : ℝ) * δ ^ 2) := by
    calc
      2 * M * (x * (1 - x) / ((n : ℝ) * δ ^ 2))
        ≤ 2 * M * ((1 / 4) / ((n : ℝ) * δ ^ 2)) := by gcongr
      _ = M / (2 * (n : ℝ) * δ ^ 2) := by ring
  linarith

/-- **Quantitative Lipschitz Rate for Bernstein Approximation:** if `f` is `L`-Lipschitz on
`[0, 1]`, then for all `n ≥ 1` and `x ∈ [0, 1]`:
`|B_n(f, x) - f x| ≤ L / (2 * Real.sqrt n)`. -/
theorem bernsteinPoly_lipschitz_rate {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |f y - f z| ≤ L * |y - z|)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernsteinPoly n f x - f x| ≤ L / (2 * Real.sqrt (n : ℝ)) := by
  let w : ℕ → ℝ := fun k => (Nat.choose n k : ℝ) * x ^ k * (1 - x) ^ (n - k)
  have hw_nn : ∀ k : ℕ, 0 ≤ w k := fun k =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
      (pow_nonneg (sub_nonneg.mpr hx.2) _)
  have hw_sum : ∑ k ∈ Finset.range (n + 1), w k = 1 := by
    have h := bernsteinPoly_one n x
    dsimp only [bernsteinPoly] at h
    simpa only [one_mul] using h
  have hdiff_eq : bernsteinPoly n f x - f x =
      ∑ k ∈ Finset.range (n + 1), (f ((k : ℝ) / (n : ℝ)) - f x) * w k := by
    have hfx : f x = ∑ k ∈ Finset.range (n + 1), f x * w k := by
      rw [← Finset.mul_sum, hw_sum, mul_one]
    dsimp only [bernsteinPoly]
    conv_lhs => rhs; rw [hfx]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by dsimp only [w]; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun k => Real.sqrt (w k)) (fun k => Real.sqrt (w k) * |(k : ℝ) / (n : ℝ) - x|)
  have hlhs_eq : ∑ k ∈ Finset.range (n + 1),
        Real.sqrt (w k) * (Real.sqrt (w k) * |(k : ℝ) / (n : ℝ) - x|) =
      ∑ k ∈ Finset.range (n + 1), w k * |(k : ℝ) / (n : ℝ) - x| := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (hw_nn k)]
  have hrhs1 : ∑ k ∈ Finset.range (n + 1), (Real.sqrt (w k)) ^ 2 = 1 := by
    calc
      ∑ k ∈ Finset.range (n + 1), (Real.sqrt (w k)) ^ 2
        = ∑ k ∈ Finset.range (n + 1), w k :=
          Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hw_nn k)
      _ = 1 := hw_sum
  have hrhs2 : ∑ k ∈ Finset.range (n + 1), (Real.sqrt (w k) * |(k : ℝ) / (n : ℝ) - x|) ^ 2 =
      x * (1 - x) / (n : ℝ) := by
    calc
      ∑ k ∈ Finset.range (n + 1), (Real.sqrt (w k) * |(k : ℝ) / (n : ℝ) - x|) ^ 2
        = ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / (n : ℝ) - x) ^ 2 * w k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, Real.sq_sqrt (hw_nn k), sq_abs]; ring
      _ = x * (1 - x) / (n : ℝ) := by
          simpa only [w, mul_assoc] using bernsteinPoly_variance hn x
  rw [hlhs_eq, hrhs1, hrhs2, one_mul] at hcs
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hquarter : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hsq_le : (∑ k ∈ Finset.range (n + 1), w k * |(k : ℝ) / (n : ℝ) - x|) ^ 2 ≤
      (1 / (2 * Real.sqrt (n : ℝ))) ^ 2 := by
    calc
      (∑ k ∈ Finset.range (n + 1), w k * |(k : ℝ) / (n : ℝ) - x|) ^ 2
        ≤ x * (1 - x) / (n : ℝ) := hcs
      _ ≤ (1 / 4) / (n : ℝ) := div_le_div_of_nonneg_right hquarter hn_pos.le
      _ = (1 / (2 * Real.sqrt (n : ℝ))) ^ 2 := by
          rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hn_pos.le]; ring
  have hsum_abs_le : ∑ k ∈ Finset.range (n + 1), w k * |(k : ℝ) / (n : ℝ) - x| ≤
      1 / (2 * Real.sqrt (n : ℝ)) := by
    exact le_of_sq_le_sq hsq_le (by positivity)
  calc
    |bernsteinPoly n f x - f x|
      ≤ ∑ k ∈ Finset.range (n + 1), |(f ((k : ℝ) / (n : ℝ)) - f x) * w k| := by
        rw [hdiff_eq]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), L * (w k * |(k : ℝ) / (n : ℝ) - x|) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hkn_mem : (k : ℝ) / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
          refine ⟨div_nonneg (Nat.cast_nonneg k) hn_pos.le, ?_⟩
          rw [div_le_one hn_pos]; exact_mod_cast hkn
        rw [abs_mul, abs_of_nonneg (hw_nn k)]
        calc
          |f ((k : ℝ) / (n : ℝ)) - f x| * w k
            ≤ (L * |(k : ℝ) / (n : ℝ) - x|) * w k :=
              mul_le_mul_of_nonneg_right (hlip _ hkn_mem x hx) (hw_nn k)
          _ = L * (w k * |(k : ℝ) / (n : ℝ) - x|) := by ring
    _ = L * ∑ k ∈ Finset.range (n + 1), w k * |(k : ℝ) / (n : ℝ) - x| :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ L * (1 / (2 * Real.sqrt (n : ℝ))) := mul_le_mul_of_nonneg_left hsum_abs_le hL
    _ = L / (2 * Real.sqrt (n : ℝ)) := by ring

/-- **Weierstrass Uniform Convergence of Bernstein Polynomials on `[0, 1]`:**
for every `f` continuous on `[0, 1]` and every `ε > 0`, `‖B_n(f) - f‖_{[0,1]} < ε` for all
sufficiently large `n`. -/
theorem bernsteinPoly_tendsto_uniformlyOn {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernsteinPoly n f x - f x| < ε := by
  have hcomp : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have huc := hcomp.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  rcases huc (ε / 2) (by linarith) with ⟨δ, hδ_pos, hδ⟩
  have hbdd : BddAbove ((fun t => |f t|) '' Set.Icc (0 : ℝ) 1) :=
    hcomp.bddAbove_image hf.abs
  rcases hbdd with ⟨M₀, hM₀⟩
  set M : ℝ := max M₀ 1
  have hM_pos : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right M₀ 1)
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |f t| ≤ M := fun t ht =>
    (hM₀ ⟨t, ht, rfl⟩).trans (le_max_left M₀ 1)
  set δ' : ℝ := δ / 2
  have hδ'_pos : 0 < δ' := half_pos hδ_pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * M / (ε * δ' ^ 2))
  refine ⟨max N₀ 1, fun n hn x hx => ?_⟩
  have hn1 : 1 ≤ n := (le_max_right N₀ 1).trans hn
  have hn0 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_left N₀ 1).trans hn
  have hn_gt : 2 * M / (ε * δ' ^ 2) < (n : ℝ) := lt_of_lt_of_le hN₀ hn0
  have hosc : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |y - z| ≤ δ' → |f y - f z| ≤ ε / 2 := by
    intro y hy z hz hyz
    have hdist : dist y z < δ := by
      rw [Real.dist_eq]
      dsimp only [δ'] at hyz
      linarith
    have := hδ y hy z hz hdist
    rw [Real.dist_eq] at this
    exact this.le
  have hpop := (bernsteinPoly_abs_sub_le_popoviciu hn1 f hδ'_pos hM_pos.le hosc hbound hx).2
  have htail : M / (2 * (n : ℝ) * δ' ^ 2) < ε / 2 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn_gt
    nlinarith
  linarith

end Bernstein

/-!
## 4. Lebesgue Constant Quasi-Optimality (`‖L^n f - f‖_∞ ≤ (1 + Λ_n) E_{n-1}(f)`)
-/

section LebesgueQuasiOptimality

/-- The Lebesgue function `λ_n(x; t) = ∑_{i=0}^{n-1} |l_i(t)|`. -/
def lebesgueFunction {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ i : Fin n, |(lagrangeBasis x i).eval t|

/-- Uniform (`L^∞`) distance between two functions on a set `S : Set ℝ`. -/
def uniformDist (S : Set ℝ) (g h : ℝ → ℝ) : ℝ :=
  sSup ((fun t => |g t - h t|) '' S)

/-- The Lebesgue constant `Λ_n(S; x) = sup_{t ∈ S} ∑_i |l_i(t)|`. -/
def lebesgueConstant {n : ℕ} (S : Set ℝ) (x : Fin n → ℝ) : ℝ :=
  sSup (lebesgueFunction x '' S)

/-- Best uniform polynomial approximation error `E_{n-1}(f; S)` by polynomials of degree `< n`. -/
def bestPolyApproxErr (S : Set ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  sInf { E : ℝ | 0 ≤ E ∧ ∃ P : Polynomial ℝ, P.degree < (n : ℕ) ∧ ∀ t ∈ S, |f t - P.eval t| ≤ E }

theorem lebesgueFunction_nonneg {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    0 ≤ lebesgueFunction x t :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem lebesgueFunction_ge_one {n : ℕ} (hn : 1 ≤ n) {x : Fin n → ℝ}
    (hx : Function.Injective x) (t : ℝ) :
    1 ≤ lebesgueFunction x t := by
  have hsum1 : ∑ i : Fin n, (lagrangeBasis x i).eval t = 1 := by
    have h := congrArg (Polynomial.eval t) (sum_lagrangeBasis_eq_one hn hx)
    rwa [Polynomial.eval_finsetSum, Polynomial.eval_one] at h
  calc
    (1 : ℝ) = |∑ i : Fin n, (lagrangeBasis x i).eval t| := by rw [hsum1, abs_one]
    _ ≤ lebesgueFunction x t := Finset.abs_sum_le_sum_abs _ _

theorem lebesgueFunction_at_node {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x) (j : Fin n) :
    lebesgueFunction x (x j) = 1 := by
  dsimp only [lebesgueFunction]
  simp only [lagrangeBasis_eval hx, apply_ite abs, abs_one, abs_zero]
  exact Finset.sum_ite_eq Finset.univ j (fun _ => (1 : ℝ)) |>.trans (if_pos (Finset.mem_univ j))

/-- **Pointwise Lebesgue Lemma:** for any injective nodes `x : Fin n → ℝ`, any `f : ℝ → ℝ`,
and any polynomial `P` of degree `< n`,
`|(L_x f)(t) - f(t)| ≤ |f(t) - P(t)| + λ_n(x; t) · max_i |f(x_i) - P(x_i)|`. -/
theorem lebesgue_pointwise_bound {n : ℕ} {x : Fin n → ℝ} (hx : Function.Injective x)
    (f : ℝ → ℝ) {P : Polynomial ℝ} (hP : P.degree < (n : ℕ)) {E_nodes : ℝ}
    (hnodes : ∀ i : Fin n, |f (x i) - P.eval (x i)| ≤ E_nodes) (t : ℝ) :
    |(lagrangeInterp x (fun i => f (x i))).eval t - f t| ≤
      |f t - P.eval t| + lebesgueFunction x t * E_nodes := by
  have hrep : P = lagrangeInterp x (fun i => P.eval (x i)) :=
    (lagrangeInterp_reproduce hx hP).symm
  have hdiff : (lagrangeInterp x (fun i => f (x i))).eval t - P.eval t =
      ∑ i : Fin n, (f (x i) - P.eval (x i)) * (lagrangeBasis x i).eval t := by
    conv_lhs => rw [hrep]
    dsimp only [lagrangeInterp]
    rw [Polynomial.eval_finsetSum, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    ring
  have hinterp_err : |(lagrangeInterp x (fun i => f (x i))).eval t - P.eval t| ≤
      lebesgueFunction x t * E_nodes := by
    rw [hdiff]
    calc
      |∑ i : Fin n, (f (x i) - P.eval (x i)) * (lagrangeBasis x i).eval t|
        ≤ ∑ i : Fin n, |(f (x i) - P.eval (x i)) * (lagrangeBasis x i).eval t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |f (x i) - P.eval (x i)| * |(lagrangeBasis x i).eval t| := by
          refine Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i : Fin n, E_nodes * |(lagrangeBasis x i).eval t| :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hnodes i) (abs_nonneg _)
      _ = lebesgueFunction x t * E_nodes := by
          rw [← Finset.mul_sum]; dsimp only [lebesgueFunction]; ring
  calc
    |(lagrangeInterp x (fun i => f (x i))).eval t - f t|
      = |((lagrangeInterp x (fun i => f (x i))).eval t - P.eval t) + (P.eval t - f t)| := by
        ring_nf
    _ ≤ |(lagrangeInterp x (fun i => f (x i))).eval t - P.eval t| + |P.eval t - f t| :=
        abs_add_le _ _
    _ = |f t - P.eval t| + |(lagrangeInterp x (fun i => f (x i))).eval t - P.eval t| := by
        rw [abs_sub_comm (P.eval t) (f t), add_comm]
    _ ≤ |f t - P.eval t| + lebesgueFunction x t * E_nodes :=
        add_le_add le_rfl hinterp_err

/-- **Explicit Uniform-Bound Lebesgue Quasi-Optimality** on any set `S : Set ℝ` containing
all interpolation nodes `x i`. -/
theorem lebesgue_quasi_optimal_of_bound {n : ℕ} {S : Set ℝ} {x : Fin n → ℝ}
    (hx : Function.Injective x) (hxS : ∀ i : Fin n, x i ∈ S)
    (f : ℝ → ℝ) {P : Polynomial ℝ} (hP : P.degree < (n : ℕ)) {Λ E : ℝ}
    (hΛ : ∀ t ∈ S, lebesgueFunction x t ≤ Λ) (hE : ∀ t ∈ S, |f t - P.eval t| ≤ E) :
    ∀ t ∈ S, |(lagrangeInterp x (fun i => f (x i))).eval t - f t| ≤ (1 + Λ) * E := by
  intro t ht
  have hE_nn : 0 ≤ E := (abs_nonneg _).trans (hE t ht)
  have hpt := lebesgue_pointwise_bound hx f hP (fun i => hE (x i) (hxS i)) t
  have h1 : lebesgueFunction x t * E ≤ Λ * E :=
    mul_le_mul_of_nonneg_right (hΛ t ht) hE_nn
  linarith [hE t ht]

theorem lebesgueConstant_ge_one {n : ℕ} (hn : 1 ≤ n) {S : Set ℝ} (hS : S.Nonempty)
    {x : Fin n → ℝ} (hx : Function.Injective x) (hΛ : BddAbove (lebesgueFunction x '' S)) :
    1 ≤ lebesgueConstant S x := by
  rcases hS with ⟨t₀, ht₀⟩
  exact (lebesgueFunction_ge_one hn hx t₀).trans (le_csSup hΛ ⟨t₀, ht₀, rfl⟩)

theorem bestPolyApproxErr_nonneg (S : Set ℝ) (n : ℕ) (f : ℝ → ℝ) :
    0 ≤ bestPolyApproxErr S n f := by
  dsimp only [bestPolyApproxErr]
  by_cases hne :
      ({ E : ℝ | 0 ≤ E ∧ ∃ P : Polynomial ℝ, P.degree < (n : ℕ) ∧ ∀ t ∈ S, |f t - P.eval t| ≤ E }).Nonempty
  · exact le_csInf hne fun _ hE => hE.1
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sInf_empty]

/-- **Lebesgue Constant Quasi-Optimality Theorem (Best-Approximation `sInf` Form):**
if `S` is nonempty, `x i ∈ S` for all `i`, `Λ_n(S; x) < ∞`, and `f` is bounded on `S`, then
`‖L_x f - f‖_S ≤ (1 + Λ_n(S; x)) · E_{n-1}(f; S)`. -/
theorem lebesgue_quasi_optimal_uniform {n : ℕ} {S : Set ℝ} (hS : S.Nonempty)
    {x : Fin n → ℝ} (hx : Function.Injective x) (hxS : ∀ i : Fin n, x i ∈ S)
    (hΛ_bdd : BddAbove (lebesgueFunction x '' S))
    (f : ℝ → ℝ) (hf_bdd : BddAbove ((fun t => |f t|) '' S)) :
    (∀ t ∈ S, |(lagrangeInterp x (fun i => f (x i))).eval t - f t| ≤
      (1 + lebesgueConstant S x) * bestPolyApproxErr S n f) ∧
    uniformDist S (fun t => (lagrangeInterp x (fun i => f (x i))).eval t) f ≤
      (1 + lebesgueConstant S x) * bestPolyApproxErr S n f := by
  let A : Set ℝ :=
    { E : ℝ | 0 ≤ E ∧ ∃ P : Polynomial ℝ, P.degree < (n : ℕ) ∧ ∀ t ∈ S, |f t - P.eval t| ≤ E }
  have hA_ne : A.Nonempty := by
    rcases hf_bdd with ⟨M, hM⟩
    rcases hS with ⟨t₀, ht₀⟩
    have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hM ⟨t₀, ht₀, rfl⟩)
    refine ⟨M, hM_nn, 0, ?_, ?_⟩
    · simp only [Polynomial.degree_zero]; exact WithBot.bot_lt_coe n
    · intro t ht; simpa only [Polynomial.eval_zero, sub_zero] using hM ⟨t, ht, rfl⟩
  have hΛ_nonneg : 0 ≤ lebesgueConstant S x := by
    rcases hS with ⟨t₀, ht₀⟩
    exact (lebesgueFunction_nonneg x t₀).trans (le_csSup hΛ_bdd ⟨t₀, ht₀, rfl⟩)
  have h1Λ_pos : 0 < 1 + lebesgueConstant S x := by linarith
  have hpt : ∀ t ∈ S, |(lagrangeInterp x (fun i => f (x i))).eval t - f t| ≤
      (1 + lebesgueConstant S x) * bestPolyApproxErr S n f := by
    intro t ht
    have hdiv_le : |(lagrangeInterp x (fun i => f (x i))).eval t - f t| /
        (1 + lebesgueConstant S x) ≤ bestPolyApproxErr S n f := by
      refine le_csInf hA_ne ?_
      rintro E ⟨_, P, hP_deg, hP_err⟩
      rw [div_le_iff₀ h1Λ_pos]
      have hΛ_le : ∀ s ∈ S, lebesgueFunction x s ≤ lebesgueConstant S x := fun s hs =>
        le_csSup hΛ_bdd ⟨s, hs, rfl⟩
      have hres := lebesgue_quasi_optimal_of_bound hx hxS f hP_deg hΛ_le hP_err t ht
      linarith
    exact ((div_le_iff₀ h1Λ_pos).mp hdiv_le).trans_eq (mul_comm _ _)
  refine ⟨hpt, ?_⟩
  dsimp only [uniformDist]
  refine csSup_le (hS.image _) ?_
  rintro y ⟨t, ht, rfl⟩
  exact hpt t ht

/-- **Compact-Interval Lebesgue Quasi-Optimality** on `[a, b]` (`a ≤ b`) for continuous `f`,
discharging all boundedness side conditions automatically. -/
theorem lebesgue_quasi_optimal_Icc {n : ℕ} {a b : ℝ} (hab : a ≤ b)
    {x : Fin n → ℝ} (hx : Function.Injective x) (hxS : ∀ i : Fin n, x i ∈ Set.Icc a b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    uniformDist (Set.Icc a b) (fun t => (lagrangeInterp x (fun i => f (x i))).eval t) f ≤
      (1 + lebesgueConstant (Set.Icc a b) x) * bestPolyApproxErr (Set.Icc a b) n f := by
  have hcomp : IsCompact (Set.Icc a b) := isCompact_Icc
  have hS : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  have hcont_lebesgue : Continuous (lebesgueFunction x) := by
    change Continuous fun t => ∑ i : Fin n, |(lagrangeBasis x i).eval t|
    refine continuous_finsetSum _ fun i _ => ?_
    exact (lagrangeBasis x i).continuous.abs
  have hΛ_bdd : BddAbove (lebesgueFunction x '' Set.Icc a b) :=
    hcomp.bddAbove_image hcont_lebesgue.continuousOn
  have hf_bdd : BddAbove ((fun t => |f t|) '' Set.Icc a b) :=
    hcomp.bddAbove_image hf.abs
  exact (lebesgue_quasi_optimal_uniform hS hx hxS hΛ_bdd f hf_bdd).2

end LebesgueQuasiOptimality

end

end Arith4Ext.PolyInterpolation
