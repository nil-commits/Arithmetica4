/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 128 (Erdős Problem #671 — Lagrange Interpolation Lebesgue Function Divergence vs. Convergence, $250)

**Honest Scope Notice:**
Erdős Problem #671 (`erdosproblems.com/671`, PPL 128, $250 prize) remains **OPEN** as of 2026.
Given a triangular array of distinct interpolation nodes `a_i^n ∈ [-1, 1]` (`1 ≤ i ≤ n`),
fundamental Lagrange polynomials `p_i^n(x) = ∏_{j ≠ i} (x - a_j^n) / (a_i^n - a_j^n)`,
Lagrange interpolants `L^n f(x) = ∑_i f(a_i^n) p_i^n(x)`, and Lebesgue functions
`Λ_n(x) = ∑_i |p_i^n(x)|`, the two open questions ask:
- **Part 1 (OPEN):** Does there exist a node array `(a_i^n)` such that for every continuous
  `f : [-1, 1] → ℝ`, there exists `x ∈ [-1, 1]` (depending on `f`) with
  `limsup_n Λ_n(x) = ∞` and `L^n f(x) → f(x)`?
- **Part 2 (OPEN, stronger than Part 1):** Does there exist a node array `(a_i^n)` such that
  `limsup_n Λ_n(x) = ∞` for every `x ∈ [-1, 1]`, yet for every continuous `f : [-1, 1] → ℝ`,
  there exists `x ∈ [-1, 1]` with `L^n f(x) → f(x)`?

This file provides a self-contained, 100%-pure-Mathlib Lean 4 formalization (zero custom or
private definitions in any public theorem signature, zero `sorry`/`admit`/`axiom`/`native_decide`)
of the core functional-analytic, extremal, and Chebyshev theory surrounding PPL 128:
1. **Exact Lagrange Basis Identities, Polynomial Reproduction, & Lebesgue's Lemma.**
2. **Exact Pointwise & Global Operator Norm Characterizations** on `C([-1, 1], ℝ)` via disjoint
   tent functions: `‖Φ_{n,x}‖ = Λ_n(x)` and `‖L^n‖ = sup_{x ∈ [-1, 1]} Λ_n(x)`.
3. **Exact Fixed-`x` Pointwise Convergence Equivalence (`∀ f, L^n f(x) → f(x) ↔ BddAbove Λ_·(x)`)**
   via Weierstrass approximation + Baire Category, completely refuting the reversed-quantifier
   fixed-`x` variant (`∃ x ∀ f`).
4. **Countable-Set Baire Category Obstruction:** Simultaneous divergence at every point of any
   countable subset of the Lebesgue divergence locus, proving that any witness to Erdős #671 Part 1
   must have an **uncountable** Lebesgue divergence set, plus the formal implication Part 2 → Part 1.
5. **Faber (1914) / Berman–Marcinkiewicz Universal Logarithmic Lower Bound**
   (`Λ_n ≥ (1 / (4 * (1 + π))) * log n > (1 / 17) * log n` for every node set of size `n ≥ 1`,
   via purely discrete cosine orthogonality + Abel summation) and **Faber's Uniform Divergence Theorem**.
6. **Chebyshev Nodes Optimal `O(log n)` Upper Bound (`≤ (2/π) log n + 4`), Exact Endpoint Formula &
   Matching Lower Bound (`≥ (2/π) log n - 2/π`), and Everywhere-Unbounded Lebesgue Function**
   (`∀ x ∈ [-1, 1], limsup_n Λ_n^Cheb(x) = ∞`, explicitly witnessing the first half of Part 2).
-/

namespace PPL128

open scoped BigOperators
open Filter Topology

/-! ## Section 1: Internal Helpers, Lagrange Basis Exactness & Lebesgue's Lemma -/

section LagrangeCore

private noncomputable def lagBasisVal {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)

private noncomputable def lagInterpVal {n : ℕ} (a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (a i) * lagBasisVal a i x

private noncomputable def lebesgueFn {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |lagBasisVal a i x|

private lemma lagBasis_eval_eq {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    (Lagrange.basis Finset.univ a i).eval x = lagBasisVal a i x := by
  unfold lagBasisVal Lagrange.basis Lagrange.basisDivisor
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv,
    mul_comm]

private lemma lagInterp_eval_eq {n : ℕ} (a : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (Lagrange.interpolate Finset.univ a (fun i => f (a i))).eval x = lagInterpVal a f x := by
  unfold lagInterpVal
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, lagBasis_eval_eq]

private lemma lagBasisVal_self {n : ℕ} {a : Fin n → ℝ} (ha : Function.Injective a) (i : Fin n) :
    lagBasisVal a i (a i) = 1 := by
  unfold lagBasisVal
  refine Finset.prod_eq_one fun j hj => ?_
  have hne : a i - a j ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.ne_of_mem_erase hj).symm (ha h))
  exact div_self hne

private lemma lagBasisVal_ne {n : ℕ} (a : Fin n → ℝ) {i j : Fin n} (hij : j ≠ i) :
    lagBasisVal a i (a j) = 0 := by
  unfold lagBasisVal
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (by simp)

private lemma lagInterp_reproduces_poly {n : ℕ} (_hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (P : Polynomial ℝ) (hdeg : P.natDegree < n) (x : ℝ) :
    lagInterpVal a (fun t => P.eval t) x = P.eval x := by
  rw [← lagInterp_eval_eq]
  have hdeg' : P.degree < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    by_cases hP : P = 0
    · subst hP; simp
    · rw [Polynomial.degree_eq_natDegree hP]
      exact WithBot.coe_lt_coe.mpr hdeg
  have hinj : Set.InjOn a (Finset.univ : Finset (Fin n)) := fun _ _ _ _ h => ha h
  have hEq : Lagrange.interpolate Finset.univ a (fun i => P.eval (a i)) = P :=
    (Lagrange.eq_interpolate hinj hdeg').symm
  rw [hEq]

private lemma lagBasisVal_sum_eq_one {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (x : ℝ) :
    ∑ i : Fin n, lagBasisVal a i x = 1 := by
  have h := lagInterp_reproduces_poly hn ha (1 : Polynomial ℝ) (by simp; omega) x
  simpa [lagInterpVal] using h

private lemma one_le_lebesgueFn {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (x : ℝ) :
    1 ≤ lebesgueFn a x := by
  calc
    (1 : ℝ) = |∑ i : Fin n, lagBasisVal a i x| := by
      rw [lagBasisVal_sum_eq_one hn ha x, abs_one]
    _ ≤ ∑ i : Fin n, |lagBasisVal a i x| := Finset.abs_sum_le_sum_abs _ _

private lemma lagBasisVal_continuous {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    Continuous (fun x : ℝ => lagBasisVal a i x) := by
  rw [show (fun x => lagBasisVal a i x) = fun x => (Lagrange.basis Finset.univ a i).eval x by
    ext x; exact (lagBasis_eval_eq a i x).symm]
  exact (Lagrange.basis Finset.univ a i).continuous

private lemma lebesgueFn_continuous {n : ℕ} (a : Fin n → ℝ) :
    Continuous (fun x : ℝ => lebesgueFn a x) := by
  unfold lebesgueFn
  exact continuous_finsetSum _ fun i _ => (lagBasisVal_continuous a i).abs

/-- **Exact Lagrange Basis Characterization & Polynomial Reproduction (Pure Mathlib):**
For any `n ≥ 1` and injective nodes `a : Fin n → ℝ`, the explicit product
`∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)` equals `(Lagrange.basis Finset.univ a i).eval x`,
satisfies Kronecker delta at the nodes, sums to `1`, and reproduces every polynomial of degree `< n`. -/
theorem ppl128_lagrange_basis_and_reproduction {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) :
    (∀ i x, (Lagrange.basis Finset.univ a i).eval x =
        ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)) ∧
    (∀ i, ∏ j ∈ Finset.univ.erase i, (a i - a j) / (a i - a j) = 1) ∧
    (∀ i j, j ≠ i → ∏ k ∈ Finset.univ.erase i, (a j - a k) / (a i - a k) = 0) ∧
    (∀ x, ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j) = 1) ∧
    (∀ (P : Polynomial ℝ), P.natDegree < n → ∀ x : ℝ,
      ∑ i : Fin n, P.eval (a i) * ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j) =
        P.eval x) :=
  ⟨lagBasis_eval_eq a, lagBasisVal_self ha, fun _ _ h => lagBasisVal_ne a h,
   lagBasisVal_sum_eq_one hn ha, lagInterp_reproduces_poly hn ha⟩

/-- **Lebesgue's Lemma (Pointwise Quasi-Optimality of Lagrange Interpolation):**
For any `n ≥ 1`, injective nodes `a : Fin n → ℝ` in `[-1, 1]`, any function `f : ℝ → ℝ`,
any polynomial `P` of degree `< n`, and any uniform approximation error bound `M` with
`|f t - P.eval t| ≤ M` on `[-1, 1]`, the pointwise interpolation error at every `x ∈ [-1, 1]`
satisfies `|L^n f(x) - f(x)| ≤ (1 + Λ_n(x)) * M`. -/
theorem ppl128_lebesgue_lemma_pointwise {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (ha_mem : ∀ i, a i ∈ Set.Icc (-1 : ℝ) 1)
    (f : ℝ → ℝ) (P : Polynomial ℝ) (hdeg : P.natDegree < n)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - P.eval t| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(∑ i : Fin n, f (a i) * ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)) - f x| ≤
      (1 + ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)|) * M := by
  have hrep := lagInterp_reproduces_poly hn ha P hdeg x
  have hdiff :
      lagInterpVal a f x - f x =
        (∑ i : Fin n, (f (a i) - P.eval (a i)) * lagBasisVal a i x) + (P.eval x - f x) := by
    have hsum : lagInterpVal a f x - lagInterpVal a (fun t => P.eval t) x =
        ∑ i : Fin n, (f (a i) - P.eval (a i)) * lagBasisVal a i x := by
      unfold lagInterpVal
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  change |lagInterpVal a f x - f x| ≤ (1 + lebesgueFn a x) * M
  rw [hdiff]
  have h1 : |∑ i : Fin n, (f (a i) - P.eval (a i)) * lagBasisVal a i x| ≤ lebesgueFn a x * M := by
    calc
      |∑ i : Fin n, (f (a i) - P.eval (a i)) * lagBasisVal a i x|
          ≤ ∑ i : Fin n, |(f (a i) - P.eval (a i)) * lagBasisVal a i x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |f (a i) - P.eval (a i)| * |lagBasisVal a i x| := by
            refine Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i : Fin n, M * |lagBasisVal a i x| :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hM (a i) (ha_mem i)) (abs_nonneg _)
      _ = lebesgueFn a x * M := by
            unfold lebesgueFn; rw [← Finset.mul_sum, mul_comm]
  have h2 : |P.eval x - f x| ≤ M := by
    rw [abs_sub_comm]
    exact hM x hx
  calc
    |(∑ i : Fin n, (f (a i) - P.eval (a i)) * lagBasisVal a i x) + (P.eval x - f x)|
        ≤ |∑ i : Fin n, (f (a i) - P.eval (a i)) * lagBasisVal a i x| + |P.eval x - f x| :=
          abs_add_le _ _
    _ ≤ lebesgueFn a x * M + M := add_le_add h1 h2
    _ = (1 + lebesgueFn a x) * M := by ring

end LagrangeCore

/-! ## Section 2: Disjoint Tent Functions & Exact Operator Norms on `C([-1, 1], ℝ)` -/

section OperatorNorms

private lemma exists_continuous_unit_matching {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (s : Fin n → ℝ) (hs : ∀ i, |s i| ≤ 1) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ t : ℝ, |g t| ≤ 1) ∧ (∀ i : Fin n, g (a i) = s i) := by
  by_cases h1 : n = 1
  · refine ⟨fun _ => s ⟨0, by omega⟩, continuous_const, fun _ => hs ⟨0, by omega⟩, fun i => ?_⟩
    have hi : i = ⟨0, by omega⟩ := by ext; omega
    rw [hi]
  · have h2 : 2 ≤ n := by omega
    let S : Finset (Fin n × Fin n) :=
      (Finset.univ ×ˢ Finset.univ).filter fun p => p.1 ≠ p.2
    have hS : S.Nonempty := by
      refine ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
      simp [S, Fin.ext_iff]
    let d : ℝ := S.inf' hS fun p => |a p.1 - a p.2|
    have hd_pos : 0 < d := by
      rw [Finset.lt_inf'_iff]
      intro p hp
      have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hpne (ha h)))
    have hd_le : ∀ i j : Fin n, i ≠ j → d ≤ |a i - a j| := by
      intro i j hij
      exact Finset.inf'_le (f := fun p : Fin n × Fin n => |a p.1 - a p.2|) (b := (i, j))
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩, hij⟩)
    let δ : ℝ := d / 2
    have hδ_pos : 0 < δ := half_pos hd_pos
    let tent : Fin n → ℝ → ℝ := fun i t => max 0 (1 - |t - a i| / δ)
    let g : ℝ → ℝ := fun t => ∑ i : Fin n, s i * tent i t
    have htent_cont : ∀ i, Continuous (tent i) := fun i => by
      have hsub : Continuous (fun t : ℝ => t - a i) := continuous_id.sub continuous_const
      exact continuous_const.max (continuous_const.sub (hsub.abs.div_const δ))
    have htent_zero : ∀ i t, δ ≤ |t - a i| → tent i t = 0 := by
      intro i t ht
      have hge : 1 ≤ |t - a i| / δ := (one_le_div hδ_pos).mpr ht
      exact max_eq_left (by linarith)
    have htent_le_one : ∀ i t, 0 ≤ tent i t ∧ tent i t ≤ 1 := by
      intro i t
      refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
      have hnn : 0 ≤ |t - a i| / δ := div_nonneg (abs_nonneg _) hδ_pos.le
      linarith
    refine ⟨g, continuous_finsetSum _ fun i _ => continuous_const.mul (htent_cont i), ?_, ?_⟩
    · intro t
      by_cases hex : ∃ i₀ : Fin n, |t - a i₀| < δ
      · rcases hex with ⟨i₀, hi₀⟩
        have hsingle : g t = s i₀ * tent i₀ t := by
          unfold g
          refine Finset.sum_eq_single i₀ ?_ (fun h => absurd (Finset.mem_univ _) h)
          intro j _ hj
          have hsep : d ≤ |a i₀ - a j| := hd_le i₀ j hj.symm
          have htri : |a i₀ - a j| ≤ |t - a i₀| + |t - a j| := by
            have : a i₀ - a j = (t - a j) - (t - a i₀) := by ring
            rw [this]
            calc
              |(t - a j) - (t - a i₀)| ≤ |t - a j| + |t - a i₀| := abs_sub _ _
              _ = |t - a i₀| + |t - a j| := add_comm _ _
          have hjδ : δ ≤ |t - a j| := by dsimp [δ] at *; linarith
          rw [htent_zero j t hjδ, mul_zero]
        rw [hsingle, abs_mul, abs_of_nonneg (htent_le_one i₀ t).1]
        calc
          |s i₀| * tent i₀ t ≤ 1 * 1 :=
            mul_le_mul (hs i₀) (htent_le_one i₀ t).2 (htent_le_one i₀ t).1 zero_le_one
          _ = 1 := one_mul 1
      · push Not at hex
        have hzero : g t = 0 := by
          unfold g
          exact Finset.sum_eq_zero fun i _ => by rw [htent_zero i t (hex i), mul_zero]
        rw [hzero, abs_zero]
        exact zero_le_one
    · intro i
      unfold g
      rw [Finset.sum_eq_single i]
      · simp [tent]
      · intro j _ hji
        have hsep : d ≤ |a i - a j| := hd_le i j hji.symm
        have hjδ : δ ≤ |a i - a j| := by dsimp [δ]; linarith
        rw [htent_zero j (a i) hjδ, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h

private lemma exists_unit_attaining_lebesgue {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (x : ℝ) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ t : ℝ, |g t| ≤ 1) ∧
      lagInterpVal a g x = lebesgueFn a x := by
  let s : Fin n → ℝ := fun i => if 0 ≤ lagBasisVal a i x then 1 else -1
  have hs : ∀ i, |s i| ≤ 1 := fun i => by dsimp [s]; split_ifs <;> norm_num
  rcases exists_continuous_unit_matching hn ha s hs with ⟨g, hg_cont, hg_bdd, hg_val⟩
  refine ⟨g, hg_cont, hg_bdd, ?_⟩
  unfold lagInterpVal lebesgueFn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hg_val i]
  dsimp [s]
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · push Not at h
    rw [neg_one_mul, abs_of_neg h]

private def clampIcc (t : ℝ) : Set.Icc (-1 : ℝ) 1 :=
  ⟨max (-1) (min 1 t), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private lemma continuous_clampIcc : Continuous clampIcc := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.max (continuous_const.min continuous_id)

private lemma clampIcc_of_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    clampIcc t = ⟨t, ht⟩ := by
  ext
  simp [clampIcc, min_eq_right ht.2, max_eq_right ht.1]

private noncomputable def restrictIcc (g : ℝ → ℝ) (hg : Continuous g) :
    C(Set.Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun t => g t.1, hg.comp continuous_subtype_val⟩

private lemma norm_restrictIcc_le {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |g t| ≤ B) :
    ‖restrictIcc g hg‖ ≤ B := by
  rw [ContinuousMap.norm_le _ hB]
  intro t
  simpa [restrictIcc, Real.norm_eq_abs] using h t.1 t.2

/-- **Exact Pointwise Lagrange Functional Norm (`‖Φ_{n, x}‖ = Λ_n(x)`):**
For any `n ≥ 1`, injective nodes `a : Fin n → ℝ` in `[-1, 1]`, and `x : ℝ`,
the continuous linear functional `f ↦ L^n f(x)` on `C([-1, 1], ℝ)` has operator norm
**exactly equal** to the Lebesgue function `Λ_n(x) = ∑_i |p_i(x)|`. -/
theorem ppl128_pointwise_operator_norm_eq {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (ha_mem : ∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) (x : ℝ) :
    ∃ Φ : C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] ℝ,
      (∀ f, Φ f = ∑ i : Fin n, f ⟨a i, ha_mem i⟩ *
        ∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)) ∧
      ‖Φ‖ = ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)| := by
  let Llin : C(Set.Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑ i : Fin n, f ⟨a i, ha_mem i⟩ * lagBasisVal a i x
      map_add' := fun f g => by
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        simp [mul_assoc, Finset.mul_sum] }
  have hle_op : ∀ f : C(Set.Icc (-1 : ℝ) 1, ℝ), ‖Llin f‖ ≤ lebesgueFn a x * ‖f‖ := by
    intro f
    rw [Real.norm_eq_abs]
    calc
      |∑ i : Fin n, f ⟨a i, ha_mem i⟩ * lagBasisVal a i x|
          ≤ ∑ i : Fin n, |f ⟨a i, ha_mem i⟩ * lagBasisVal a i x| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |f ⟨a i, ha_mem i⟩| * |lagBasisVal a i x| :=
            Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i : Fin n, ‖f‖ * |lagBasisVal a i x| :=
            Finset.sum_le_sum fun i _ => by
              have hfi : |f ⟨a i, ha_mem i⟩| ≤ ‖f‖ := by
                simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f ⟨a i, ha_mem i⟩
              exact mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
      _ = lebesgueFn a x * ‖f‖ := by
            unfold lebesgueFn; rw [← Finset.mul_sum, mul_comm]
  let Φ : C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] ℝ := Llin.mkContinuous (lebesgueFn a x) hle_op
  refine ⟨Φ, fun f => rfl, ?_⟩
  have hΛ_nn : 0 ≤ lebesgueFn a x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hupper : ‖Φ‖ ≤ lebesgueFn a x := Llin.mkContinuous_norm_le hΛ_nn hle_op
  have hlower : lebesgueFn a x ≤ ‖Φ‖ := by
    rcases exists_unit_attaining_lebesgue hn ha x with ⟨g, hg_cont, hg_bdd, hg_eq⟩
    let gC : C(Set.Icc (-1 : ℝ) 1, ℝ) := restrictIcc g hg_cont
    have hg_norm : ‖gC‖ ≤ 1 := norm_restrictIcc_le hg_cont zero_le_one fun t _ => hg_bdd t
    have hval : Φ gC = lebesgueFn a x := by
      simpa [Φ, Llin, gC, restrictIcc, lagInterpVal] using hg_eq
    calc
      lebesgueFn a x = |Φ gC| := by rw [hval, abs_of_nonneg hΛ_nn]
      _ = ‖Φ gC‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Φ‖ * ‖gC‖ := Φ.le_opNorm gC
      _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left hg_norm (norm_nonneg _)
      _ = ‖Φ‖ := mul_one _
  exact le_antisymm hupper hlower

/-- **Exact Global Lagrange Operator Norm (`‖L^n‖ = sup_{x ∈ [-1, 1]} Λ_n(x)`):**
For any `n ≥ 1` and injective nodes `a : Fin n → ℝ` in `[-1, 1]`, the Lagrange interpolation
operator `L^n : C([-1, 1], ℝ) →L[ℝ] C([-1, 1], ℝ)` has operator norm **exactly equal** to
the Lebesgue constant `Λ_n = sSup (Λ_n '' [-1, 1])`. -/
theorem ppl128_global_operator_norm_eq {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (ha_mem : ∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ L : C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ),
      (∀ f x, L f x = ∑ i : Fin n, f ⟨a i, ha_mem i⟩ *
        ∏ j ∈ Finset.univ.erase i, ((x : ℝ) - a j) / (a i - a j)) ∧
      ‖L‖ = sSup ((fun x : ℝ =>
        ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)|) ''
          Set.Icc (-1 : ℝ) 1) := by
  have hcomp : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := ⟨0, by norm_num, by norm_num⟩
  have hbdd : BddAbove ((fun x : ℝ => lebesgueFn a x) '' Set.Icc (-1 : ℝ) 1) :=
    (hcomp.image (lebesgueFn_continuous a)).bddAbove
  let Λ : ℝ := sSup ((fun x : ℝ => lebesgueFn a x) '' Set.Icc (-1 : ℝ) 1)
  have hΛ_ge : ∀ x ∈ Set.Icc (-1 : ℝ) 1, lebesgueFn a x ≤ Λ := fun x hx =>
    le_csSup hbdd ⟨x, hx, rfl⟩
  have hΛ_nn : 0 ≤ Λ :=
    (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hΛ_ge 0 ⟨by norm_num, by norm_num⟩)
  let Llin : C(Set.Icc (-1 : ℝ) 1, ℝ) →ₗ[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ) :=
    { toFun := fun f =>
        ⟨fun x => ∑ i : Fin n, f ⟨a i, ha_mem i⟩ * lagBasisVal a i x.1,
         continuous_finsetSum _ fun i _ =>
           continuous_const.mul ((lagBasisVal_continuous a i).comp continuous_subtype_val)⟩
      map_add' := fun f g => by
        ext x; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        ext x; simp [mul_assoc, Finset.mul_sum] }
  have hle_op : ∀ f : C(Set.Icc (-1 : ℝ) 1, ℝ), ‖Llin f‖ ≤ Λ * ‖f‖ := by
    intro f
    rw [ContinuousMap.norm_le _ (mul_nonneg hΛ_nn (norm_nonneg _))]
    intro x
    rw [Real.norm_eq_abs]
    calc
      |∑ i : Fin n, f ⟨a i, ha_mem i⟩ * lagBasisVal a i x.1|
          ≤ ∑ i : Fin n, |f ⟨a i, ha_mem i⟩ * lagBasisVal a i x.1| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |f ⟨a i, ha_mem i⟩| * |lagBasisVal a i x.1| :=
            Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i : Fin n, ‖f‖ * |lagBasisVal a i x.1| :=
            Finset.sum_le_sum fun i _ => by
              have hfi : |f ⟨a i, ha_mem i⟩| ≤ ‖f‖ := by
                simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f ⟨a i, ha_mem i⟩
              exact mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
      _ = lebesgueFn a x.1 * ‖f‖ := by
            unfold lebesgueFn; rw [← Finset.mul_sum, mul_comm]
      _ ≤ Λ * ‖f‖ := mul_le_mul_of_nonneg_right (hΛ_ge x.1 x.2) (norm_nonneg _)
  let L : C(Set.Icc (-1 : ℝ) 1, ℝ) →L[ℝ] C(Set.Icc (-1 : ℝ) 1, ℝ) :=
    Llin.mkContinuous Λ hle_op
  refine ⟨L, fun f x => rfl, ?_⟩
  have hupper : ‖L‖ ≤ Λ := Llin.mkContinuous_norm_le hΛ_nn hle_op
  have hlower : Λ ≤ ‖L‖ := by
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases exists_unit_attaining_lebesgue hn ha x with ⟨g, hg_cont, hg_bdd, hg_eq⟩
    let gC : C(Set.Icc (-1 : ℝ) 1, ℝ) := restrictIcc g hg_cont
    have hg_norm : ‖gC‖ ≤ 1 := norm_restrictIcc_le hg_cont zero_le_one fun t _ => hg_bdd t
    have hval : L gC ⟨x, hx⟩ = lebesgueFn a x := by
      simpa [L, Llin, gC, restrictIcc, lagInterpVal] using hg_eq
    have hnn : 0 ≤ lebesgueFn a x := Finset.sum_nonneg fun _ _ => abs_nonneg _
    calc
      lebesgueFn a x = |L gC ⟨x, hx⟩| := by rw [hval, abs_of_nonneg hnn]
      _ ≤ ‖L gC‖ := by
        simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (L gC) ⟨x, hx⟩
      _ ≤ ‖L‖ * ‖gC‖ := L.le_opNorm gC
      _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left hg_norm (norm_nonneg _)
      _ = ‖L‖ := mul_one _
  exact le_antisymm hupper hlower

end OperatorNorms

/-! ## Section 3: Baire Category Obstructions & Exact Fixed-`x` Equivalence -/

section BaireAndFixedPoint

private lemma continuous_eval_Icc (p : Set.Icc (-1 : ℝ) 1) :
    Continuous (fun f : C(Set.Icc (-1 : ℝ) 1, ℝ) => f p) := by
  rw [Metric.continuous_iff]
  intro f ε hε
  exact ⟨ε, hε, fun g hfg => (ContinuousMap.dist_apply_le_dist p).trans_lt hfg⟩

private lemma baire_countable_unbounded_lagrange
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (ha : ∀ n, Function.Injective (a n))
    (ha_mem : ∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1)
    {S : Set ℝ} (hS_count : S.Countable)
    (hS_unbdd : ∀ x ∈ S, ∀ M : ℝ, ∃ n : ℕ, M < lebesgueFn (a n) x) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ x ∈ S, ∀ B : ℝ, ∃ n : ℕ, B < |lagInterpVal (a n) f x| := by
  let U : ℝ → ℕ → Set C(Set.Icc (-1 : ℝ) 1, ℝ) := fun x k =>
    {f | ∃ n : ℕ, (k : ℝ) < |∑ i : Fin (n + 1), f ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x|}
  have hU_open : ∀ x k, IsOpen (U x k) := by
    intro x k
    have hEq : U x k = ⋃ n : ℕ,
        (fun f : C(Set.Icc (-1 : ℝ) 1, ℝ) =>
          |∑ i : Fin (n + 1), f ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x|) ⁻¹' Set.Ioi (k : ℝ) := by
      ext f; simp [U]
    rw [hEq]
    refine isOpen_iUnion fun n => isOpen_Ioi.preimage ?_
    refine Continuous.abs ?_
    exact continuous_finsetSum _ fun i _ =>
      (continuous_eval_Icc ⟨a n i, ha_mem n i⟩).mul continuous_const
  have hU_dense : ∀ x ∈ S, ∀ k : ℕ, Dense (U x k) := by
    intro x hx k
    rw [Metric.dense_iff]
    intro f₀ ε hε
    by_cases hf₀ : f₀ ∈ U x k
    · exact ⟨f₀, Metric.mem_ball_self hε, hf₀⟩
    · simp only [U, Set.mem_ofPred_eq, not_exists, not_lt] at hf₀
      let r : ℝ := ε / 2
      have hr : 0 < r := half_pos hε
      rcases hS_unbdd x hx ((2 * (k : ℝ) + 2) / r) with ⟨n, hn_big⟩
      rcases exists_unit_attaining_lebesgue (Nat.succ_pos n) (ha n) x with
        ⟨g, hg_cont, hg_bdd, hg_eq⟩
      let gC : C(Set.Icc (-1 : ℝ) 1, ℝ) := restrictIcc g hg_cont
      have hg_norm : ‖gC‖ ≤ 1 := norm_restrictIcc_le hg_cont zero_le_one fun t _ => hg_bdd t
      let f : C(Set.Icc (-1 : ℝ) 1, ℝ) := f₀ + r • gC
      refine ⟨f, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        have hsub : f - f₀ = r • gC := by simp [f]
        rw [hsub, norm_smul, Real.norm_of_nonneg hr.le]
        calc
          r * ‖gC‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hg_norm hr.le
          _ = ε / 2 := by rw [mul_one]
          _ < ε := half_lt_self hε
      · refine ⟨n, ?_⟩
        have hsum_eq :
            ∑ i : Fin (n + 1), f ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x =
              (∑ i : Fin (n + 1), f₀ ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x) +
                r * lebesgueFn (a n) x := by
          have hg_sum : ∑ i : Fin (n + 1), gC ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x =
              lebesgueFn (a n) x := by
            simpa [gC, restrictIcc, lagInterpVal] using hg_eq
          calc
            ∑ i : Fin (n + 1), f ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x
                = ∑ i : Fin (n + 1),
                    (f₀ ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x +
                      r * (gC ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x)) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  simp [f]; ring
            _ = (∑ i : Fin (n + 1), f₀ ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x) +
                  r * (∑ i : Fin (n + 1), gC ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ = _ := by rw [hg_sum]
        rw [hsum_eq]
        have h1 : 2 * (k : ℝ) + 2 < r * lebesgueFn (a n) x := by
          have := (div_lt_iff₀ hr).mp hn_big
          linarith
        have h0 : |∑ i : Fin (n + 1), f₀ ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x| ≤ k :=
          hf₀ n
        have htri := abs_sub_abs_le_abs_add
          (r * lebesgueFn (a n) x)
          (∑ i : Fin (n + 1), f₀ ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x)
        have hpos : 0 ≤ r * lebesgueFn (a n) x :=
          mul_nonneg hr.le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        rw [abs_of_nonneg hpos] at htri
        rw [add_comm]
        linarith
  have : Countable S := hS_count.to_subtype
  have hdense : Dense (⋂ p : S × ℕ, U p.1.1 p.2) :=
    dense_iInter_of_isOpen (fun p => hU_open p.1.1 p.2) (fun p => hU_dense p.1.1 p.1.2 p.2)
  rcases hdense.nonempty with ⟨fC, hfC⟩
  refine ⟨fun t => fC (clampIcc t), fC.continuous.comp continuous_clampIcc, ?_⟩
  intro x hx B
  rcases exists_nat_gt B with ⟨k, hk⟩
  have hmem : fC ∈ U x k := by
    have := Set.mem_iInter.mp hfC (⟨x, hx⟩, k)
    exact this
  rcases hmem with ⟨n, hn⟩
  refine ⟨n, lt_trans hk ?_⟩
  have hEq : lagInterpVal (a n) (fun t => fC (clampIcc t)) x =
      ∑ i : Fin (n + 1), fC ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x := by
    unfold lagInterpVal
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [clampIcc_of_mem (ha_mem n i)]
  rwa [hEq]

/-- **Countable-Set Baire Category Obstruction (Pure Mathlib):**
For any triangular array of distinct nodes in `[-1, 1]` and any countable set `S ⊆ [-1, 1]`
on which the Lebesgue function `Λ_n(x)` is unbounded at every `x ∈ S`, there exists a single
continuous function `f : ℝ → ℝ` whose Lagrange interpolants `L^n f(x)` are unbounded at
**every** `x ∈ S` simultaneously (hence diverge at every `x ∈ S`). -/
theorem ppl128_countable_divergence_obstruction
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (ha : ∀ n, Function.Injective (a n))
    (ha_mem : ∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1)
    {S : Set ℝ} (hS_count : S.Countable)
    (hS_unbdd : ∀ x ∈ S, ∀ M : ℝ, ∃ n : ℕ,
      M < ∑ i : Fin (n + 1), |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)|) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ x ∈ S, ∀ B : ℝ, ∃ n : ℕ,
        B < |∑ i : Fin (n + 1), f (a n i) *
          ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)| :=
  baire_countable_unbounded_lagrange a ha ha_mem hS_count hS_unbdd

/-- **Necessary Uncountability of the Lebesgue Divergence Set for Erdős #671 Part 1:**
If a triangular array of distinct nodes in `[-1, 1]` satisfies Erdős #671 Part 1
(`∀ continuous f, ∃ x ∈ [-1, 1], Λ_n(x) unbounded ∧ L^n f(x) → f(x)`),
then the Lebesgue divergence set `{x ∈ [-1, 1] | ∀ M, ∃ n, M < Λ_n(x)}` MUST be **uncountable**. -/
theorem ppl128_part1_requires_uncountable_divergence_set
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (ha : ∀ n, Function.Injective (a n))
    (ha_mem : ∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1)
    (hPart1 : ∀ f : ℝ → ℝ, Continuous f →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        (∀ M : ℝ, ∃ n : ℕ, M < ∑ i : Fin (n + 1),
            |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)|) ∧
        Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), f (a n i) *
            ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j))
          atTop (nhds (f x))) :
    ¬ ({x ∈ Set.Icc (-1 : ℝ) 1 | ∀ M : ℝ, ∃ n : ℕ,
        M < ∑ i : Fin (n + 1),
          |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)|}).Countable := by
  intro hcount
  let D : Set ℝ := {x ∈ Set.Icc (-1 : ℝ) 1 | ∀ M : ℝ, ∃ n : ℕ, M < lebesgueFn (a n) x}
  rcases baire_countable_unbounded_lagrange a ha ha_mem hcount (fun x hx => hx.2) with
    ⟨f, hf_cont, hf_unbdd⟩
  rcases hPart1 f hf_cont with ⟨x, hx_mem, hx_unbdd, hx_conv⟩
  have hbdd := Metric.isBounded_range_of_tendsto _ hx_conv
  rw [Metric.isBounded_iff_subset_closedBall 0] at hbdd
  rcases hbdd with ⟨R, hR⟩
  rcases hf_unbdd x ⟨hx_mem, hx_unbdd⟩ R with ⟨n, hn⟩
  have hle : |lagInterpVal (a n) f x| ≤ R := by
    have hmem := hR (Set.mem_range_self n)
    unfold lagInterpVal lagBasisVal
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hmem
  exact not_lt_of_ge hle hn

/-- **Exact Fixed-`x` Pointwise Convergence Equivalence (Weierstrass + Baire Category):**
For any triangular array of distinct nodes in `[-1, 1]` and any fixed `x ∈ [-1, 1]`,
`L^n f(x) → f(x)` holds for every continuous `f : ℝ → ℝ` **if and only if** the Lebesgue
function sequence `n ↦ Λ_{n+1}(x)` is bounded above.
In particular, this completely refutes the reversed-quantifier fixed-`x` variant (`∃ x ∀ f`). -/
theorem ppl128_fixed_point_convergence_iff_bdd
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (ha : ∀ n, Function.Injective (a n))
    (ha_mem : ∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (∀ f : ℝ → ℝ, Continuous f →
      Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), f (a n i) *
          ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j))
        atTop (nhds (f x))) ↔
    (∃ M : ℝ, ∀ n : ℕ,
      ∑ i : Fin (n + 1), |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)| ≤ M) := by
  constructor
  · intro hconv
    by_contra hnot
    push Not at hnot
    rcases baire_countable_unbounded_lagrange a ha ha_mem (Set.countable_singleton x)
        (fun y hy => by rwa [Set.mem_singleton_iff.mp hy]) with ⟨f, hf_cont, hf_unbdd⟩
    have htend := hconv f hf_cont
    have hbdd := Metric.isBounded_range_of_tendsto _ htend
    rw [Metric.isBounded_iff_subset_closedBall 0] at hbdd
    rcases hbdd with ⟨R, hR⟩
    rcases hf_unbdd x (Set.mem_singleton x) R with ⟨n, hn⟩
    have hle : |lagInterpVal (a n) f x| ≤ R := by
      have hmem := hR (Set.mem_range_self n)
      unfold lagInterpVal lagBasisVal
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hmem
    exact not_lt_of_ge hle hn
  · rintro ⟨M, hM⟩ f hf_cont
    have hM_nn : 0 ≤ M :=
      (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hM 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    let fC : C(Set.Icc (-1 : ℝ) 1, ℝ) := restrictIcc f hf_cont
    have hcl : fC ∈ (polynomialFunctions (Set.Icc (-1 : ℝ) 1)).topologicalClosure := by
      rw [polynomialFunctions_closure_eq_top (-1) 1]
      trivial
    have hδ : 0 < ε / (1 + M) := div_pos hε (by linarith)
    change fC ∈ closure (polynomialFunctions (Set.Icc (-1 : ℝ) 1) : Set _) at hcl
    rw [Metric.mem_closure_iff] at hcl
    rcases hcl (ε / (1 + M)) hδ with ⟨pC, hpC_mem, hpC_dist⟩
    rcases hpC_mem with ⟨P, _, rfl⟩
    refine ⟨P.natDegree, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hlt_approx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - P.eval t| ≤
        dist fC (Polynomial.toContinuousMapOn P (Set.Icc (-1 : ℝ) 1)) := by
      intro t ht
      have h1 := ContinuousMap.dist_apply_le_dist (f := fC)
        (g := Polynomial.toContinuousMapOn P (Set.Icc (-1 : ℝ) 1)) ⟨t, ht⟩
      simpa [fC, restrictIcc, Real.dist_eq, Polynomial.toContinuousMapOn_apply] using h1
    have hleb2 := ppl128_lebesgue_lemma_pointwise (Nat.succ_pos n) (ha n) (ha_mem n)
      f P (by omega) hlt_approx hx
    have h1M : 0 < 1 + M := by linarith
    have hMn : lebesgueFn (a n) x ≤ M := hM n
    change |lagInterpVal (a n) f x - f x| < ε
    calc
      |lagInterpVal (a n) f x - f x|
          ≤ (1 + lebesgueFn (a n) x) *
              dist fC (Polynomial.toContinuousMapOn P (Set.Icc (-1 : ℝ) 1)) := hleb2
      _ ≤ (1 + M) * dist fC (Polynomial.toContinuousMapOn P (Set.Icc (-1 : ℝ) 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < (1 + M) * (ε / (1 + M)) := mul_lt_mul_of_pos_left hpC_dist h1M
      _ = ε := mul_div_cancel₀ ε h1M.ne'

/-- **Refutation of the Reversed-Quantifier Fixed-`x` Variant of Erdős #671:**
There does NOT exist a node array and a fixed point `x ∈ [-1, 1]` where `Λ_n(x)` is unbounded
and yet `L^n f(x) → f(x)` for every continuous `f : ℝ → ℝ`. -/
theorem ppl128_refute_fixed_point_variant
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (ha : ∀ n, Function.Injective (a n))
    (ha_mem : ∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hunbdd : ∀ M : ℝ, ∃ n : ℕ, M < ∑ i : Fin (n + 1),
      |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)|) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ¬ Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), f (a n i) *
          ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j))
        atTop (nhds (f x)) := by
  by_contra hall
  push Not at hall
  rcases (ppl128_fixed_point_convergence_iff_bdd a ha ha_mem hx).mp hall with ⟨M, hM⟩
  rcases hunbdd M with ⟨n, hn⟩
  exact not_lt_of_ge (hM n) hn

/-- **Logical Hierarchy of Erdős Problem #671 (Part 2 implies Part 1):**
Any triangular node array whose Lebesgue function is unbounded at every `x ∈ [-1, 1]` and
which converges at some `x(f) ∈ [-1, 1]` for every continuous `f` (Part 2) automatically
satisfies Part 1. -/
theorem ppl128_part2_implies_part1
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (hAllUnbdd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ M : ℝ, ∃ n : ℕ,
      M < ∑ i : Fin (n + 1),
        |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)|)
    (hAllConv : ∀ f : ℝ → ℝ, Continuous f →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), f (a n i) *
            ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j))
          atTop (nhds (f x))) :
    ∀ f : ℝ → ℝ, Continuous f →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        (∀ M : ℝ, ∃ n : ℕ, M < ∑ i : Fin (n + 1),
            |∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)|) ∧
        Tendsto (fun n : ℕ => ∑ i : Fin (n + 1), f (a n i) *
            ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j))
          atTop (nhds (f x)) := by
  intro f hf
  rcases hAllConv f hf with ⟨x, hx, hconv⟩
  exact ⟨x, hx, hAllUnbdd x hx, hconv⟩

end BaireAndFixedPoint

/-! ## Section 4: Faber (1914) / Berman–Marcinkiewicz Universal Lower Bound & Divergence Theorem -/

section FaberLowerBound

private noncomputable def chebT : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 => Polynomial.C 2 * Polynomial.X * chebT (n + 1) - chebT n

private lemma chebT_eval_cos (n : ℕ) (θ : ℝ) :
    (chebT n).eval (Real.cos θ) = Real.cos ((n : ℝ) * θ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [chebT]
    | 1 => simp [chebT]
    | k + 2 =>
      simp only [chebT, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      have h1 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      have h2 : ((k : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      rw [h1, h2, Real.cos_add, Real.cos_sub]
      ring

private lemma chebT_natDegree_and_coeff (n : ℕ) :
    (chebT n).natDegree = n ∧ 0 < (chebT n).coeff n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [chebT]
    | 1 => simp [chebT]
    | k + 2 =>
      have ih1 := ih (k + 1) (by omega)
      have ih0 := ih k (by omega)
      have hcoeff_high : ∀ j, k + 2 < j → (chebT (k + 2)).coeff j = 0 := by
        intro j hj
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        simp only [chebT, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_mul]
        have h1 : (chebT (k + 1)).coeff j' = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ih1.1]; omega)
        have h0 : (chebT k).coeff (j' + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ih0.1]; omega)
        rw [h1, h0]; ring
      have hcoeff_top : (chebT (k + 2)).coeff (k + 2) = 2 * (chebT (k + 1)).coeff (k + 1) := by
        simp only [chebT, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_mul]
        have h0 : (chebT k).coeff (k + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [ih0.1]; omega)
        rw [h0, sub_zero]
      have hpos : 0 < (chebT (k + 2)).coeff (k + 2) := by
        rw [hcoeff_top]; linarith [ih1.2]
      have hle : (chebT (k + 2)).natDegree ≤ k + 2 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hcoeff_high
      exact ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle hpos.ne', hpos⟩

private lemma poly_eq_sum_chebT (m : ℕ) :
    ∀ q : Polynomial ℝ, q.natDegree ≤ m →
      ∃ c : Fin (m + 1) → ℝ, q = ∑ r : Fin (m + 1), Polynomial.C (c r) * chebT r.1 := by
  induction m with
  | zero =>
    intro q hq
    refine ⟨fun _ => q.coeff 0, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [chebT, mul_one]
    exact Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hq)
  | succ m ih =>
    intro q hq
    have hT := chebT_natDegree_and_coeff (m + 1)
    let a : ℝ := q.coeff (m + 1) / (chebT (m + 1)).coeff (m + 1)
    let q' : Polynomial ℝ := q - Polynomial.C a * chebT (m + 1)
    have hq'_le : q'.natDegree ≤ m := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro j hj
      simp only [q', Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      by_cases hjeq : j = m + 1
      · subst hjeq
        dsimp [a]
        rw [div_mul_cancel₀ _ hT.2.ne', sub_self]
      · have hjgt : m + 1 < j := by omega
        have h1 : q.coeff j = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hjgt)
        have h2 : (chebT (m + 1)).coeff j = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hT.1]; exact hjgt)
        rw [h1, h2]; ring
    rcases ih q' hq'_le with ⟨c', hc'⟩
    let c : Fin (m + 2) → ℝ := fun r =>
      if hr : r.1 < m + 1 then c' ⟨r.1, hr⟩ else a
    refine ⟨c, ?_⟩
    rw [Fin.sum_univ_castSucc]
    have hinit : ∑ i : Fin (m + 1), Polynomial.C (c i.castSucc) * chebT (i.castSucc : ℕ) = q' := by
      rw [hc']
      refine Finset.sum_congr rfl fun i _ => ?_
      have hci : c i.castSucc = c' i := dif_pos i.isLt
      rw [hci]
      rfl
    have hlast : Polynomial.C (c (Fin.last (m + 1))) * chebT (Fin.last (m + 1) : ℕ) =
        Polynomial.C a * chebT (m + 1) := by
      simp [c]
    rw [hinit, hlast]
    dsimp [q']
    abel

private lemma sum_cos_equispaced_eq_zero {M d : ℕ} (hd_pos : 1 ≤ d) (hd_lt : d < M) :
    ∑ s ∈ Finset.range M, Real.cos (2 * Real.pi * (d : ℝ) * (s : ℝ) / (M : ℝ)) = 0 := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  let α : ℝ := Real.pi * (d : ℝ) / (M : ℝ)
  have hα_pos : 0 < α := div_pos (mul_pos Real.pi_pos (by exact_mod_cast hd_pos)) hM_pos
  have hα_lt : α < Real.pi := by
    dsimp [α]
    rw [div_lt_iff₀ hM_pos]
    have hdm : (d : ℝ) < (M : ℝ) := by exact_mod_cast hd_lt
    nlinarith [Real.pi_pos]
  have hsin_ne : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hα_pos hα_lt).ne'
  have hterm : ∀ s : ℕ,
      2 * Real.sin α * Real.cos (2 * Real.pi * (d : ℝ) * (s : ℝ) / (M : ℝ)) =
        Real.sin ((2 * ((s + 1 : ℕ) : ℝ) - 1) * α) - Real.sin ((2 * (s : ℝ) - 1) * α) := by
    intro s
    have h1 : (2 * ((s + 1 : ℕ) : ℝ) - 1) * α = 2 * (s : ℝ) * α + α := by push_cast; ring
    have h2 : (2 * (s : ℝ) - 1) * α = 2 * (s : ℝ) * α - α := by ring
    have h3 : 2 * Real.pi * (d : ℝ) * (s : ℝ) / (M : ℝ) = 2 * (s : ℝ) * α := by
      dsimp [α]; ring
    rw [h1, h2, h3, Real.sin_add, Real.sin_sub]
    ring
  have hmul : 2 * Real.sin α *
      ∑ s ∈ Finset.range M, Real.cos (2 * Real.pi * (d : ℝ) * (s : ℝ) / (M : ℝ)) = 0 := by
    rw [Finset.mul_sum]
    have hcongr : ∑ s ∈ Finset.range M,
        2 * Real.sin α * Real.cos (2 * Real.pi * (d : ℝ) * (s : ℝ) / (M : ℝ)) =
        ∑ s ∈ Finset.range M,
          (Real.sin ((2 * ((s + 1 : ℕ) : ℝ) - 1) * α) - Real.sin ((2 * (s : ℝ) - 1) * α)) :=
      Finset.sum_congr rfl fun s _ => hterm s
    rw [hcongr, Finset.sum_range_sub (fun s => Real.sin ((2 * (s : ℝ) - 1) * α)) M]
    have htop : (2 * (M : ℝ) - 1) * α = (-α) + (d : ℤ) * (2 * Real.pi) := by
      dsimp [α]
      field_simp [hM_pos.ne']
      push_cast; ring
    have hbot : (2 * ((0 : ℕ) : ℝ) - 1) * α = -α := by simp
    rw [htop, hbot, Real.sin_add_int_mul_two_pi, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero two_ne_zero hsin_ne)

private lemma sum_cos_mul_cos_equispaced {M k r : ℕ} (hk_pos : 1 ≤ k) (hkr : k + r < M) :
    ∑ s ∈ Finset.range M,
      Real.cos (2 * Real.pi * (k : ℝ) * (s : ℝ) / (M : ℝ)) *
        Real.cos (2 * Real.pi * (r : ℝ) * (s : ℝ) / (M : ℝ)) =
      if k = r then (M : ℝ) / 2 else 0 := by
  have hsplit : ∀ s : ℕ,
      Real.cos (2 * Real.pi * (k : ℝ) * (s : ℝ) / (M : ℝ)) *
        Real.cos (2 * Real.pi * (r : ℝ) * (s : ℝ) / (M : ℝ)) =
      (Real.cos (2 * Real.pi * ((k + r : ℕ) : ℝ) * (s : ℝ) / (M : ℝ)) +
        Real.cos (2 * Real.pi * ((k : ℝ) - (r : ℝ)) * (s : ℝ) / (M : ℝ))) / 2 := by
    intro s
    have h1 : 2 * Real.pi * ((k + r : ℕ) : ℝ) * (s : ℝ) / (M : ℝ) =
        2 * Real.pi * (k : ℝ) * (s : ℝ) / (M : ℝ) +
          2 * Real.pi * (r : ℝ) * (s : ℝ) / (M : ℝ) := by push_cast; ring
    have h2 : 2 * Real.pi * ((k : ℝ) - (r : ℝ)) * (s : ℝ) / (M : ℝ) =
        2 * Real.pi * (k : ℝ) * (s : ℝ) / (M : ℝ) -
          2 * Real.pi * (r : ℝ) * (s : ℝ) / (M : ℝ) := by ring
    rw [h1, h2, Real.cos_add, Real.cos_sub]
    ring
  rw [Finset.sum_congr rfl fun s _ => hsplit s, ← Finset.sum_div, Finset.sum_add_distrib]
  have hsum_add : ∑ s ∈ Finset.range M,
      Real.cos (2 * Real.pi * ((k + r : ℕ) : ℝ) * (s : ℝ) / (M : ℝ)) = 0 :=
    sum_cos_equispaced_eq_zero (by omega) hkr
  rw [hsum_add, zero_add]
  split_ifs with hEq
  · subst hEq
    simp
  · have hsum_diff : ∑ s ∈ Finset.range M,
        Real.cos (2 * Real.pi * ((k : ℝ) - (r : ℝ)) * (s : ℝ) / (M : ℝ)) = 0 := by
      rcases lt_or_gt_of_ne hEq with hlt | hgt
      · have hcast : ∀ s : ℕ,
            Real.cos (2 * Real.pi * ((k : ℝ) - (r : ℝ)) * (s : ℝ) / (M : ℝ)) =
              Real.cos (2 * Real.pi * ((r - k : ℕ) : ℝ) * (s : ℝ) / (M : ℝ)) := by
          intro s
          rw [← Real.cos_neg]
          congr 1
          rw [Nat.cast_sub hlt.le]
          ring
        rw [Finset.sum_congr rfl fun s _ => hcast s]
        exact sum_cos_equispaced_eq_zero (by omega) (by omega)
      · have hcast : ∀ s : ℕ,
            Real.cos (2 * Real.pi * ((k : ℝ) - (r : ℝ)) * (s : ℝ) / (M : ℝ)) =
              Real.cos (2 * Real.pi * ((k - r : ℕ) : ℝ) * (s : ℝ) / (M : ℝ)) := by
          intro s
          congr 1
          rw [Nat.cast_sub hgt.le]
        rw [Finset.sum_congr rfl fun s _ => hcast s]
        exact sum_cos_equispaced_eq_zero (by omega) (by omega)
    rw [hsum_diff, zero_div]

private lemma sin_sum_Icc_bound {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi) (a b : ℕ) :
    |∑ j ∈ Finset.Icc (a + 1) b, Real.sin ((j : ℝ) * θ)| ≤ Real.pi / θ := by
  have hhalf_pos : 0 < θ / 2 := half_pos hθ0
  have hhalf_le : θ / 2 ≤ Real.pi / 2 := by linarith
  have hsin_lb : θ / Real.pi ≤ Real.sin (θ / 2) := by
    have h := Real.mul_le_sin hhalf_pos.le hhalf_le
    have hEq : θ / Real.pi = 2 / Real.pi * (θ / 2) := by ring
    linarith
  have hsin_pos : 0 < Real.sin (θ / 2) := lt_of_lt_of_le (div_pos hθ0 Real.pi_pos) hsin_lb
  by_cases hab : b < a + 1
  · have hempty : Finset.Icc (a + 1) b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty, Finset.sum_empty, abs_zero]
    exact (div_pos Real.pi_pos hθ0).le
  · push Not at hab
    have htele :
        2 * Real.sin (θ / 2) * ∑ j ∈ Finset.Icc (a + 1) b, Real.sin ((j : ℝ) * θ) =
          Real.cos (((a : ℝ) + 1 / 2) * θ) - Real.cos (((b : ℝ) + 1 / 2) * θ) := by
      rw [Finset.mul_sum]
      have hterm : ∀ j : ℕ,
          2 * Real.sin (θ / 2) * Real.sin ((j : ℝ) * θ) =
            Real.cos (((j : ℝ) - 1 / 2) * θ) - Real.cos (((j : ℝ) + 1 / 2) * θ) := by
        intro j
        have h1 : ((j : ℝ) - 1 / 2) * θ = (j : ℝ) * θ - θ / 2 := by ring
        have h2 : ((j : ℝ) + 1 / 2) * θ = (j : ℝ) * θ + θ / 2 := by ring
        rw [h1, h2, Real.cos_sub, Real.cos_add]
        ring
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      have hIco : Finset.Icc (a + 1) b = Finset.Ico (a + 1) (b + 1) := rfl
      rw [hIco]
      have hshift :
          ∑ j ∈ Finset.Ico (a + 1) (b + 1),
              (Real.cos (((j : ℝ) - 1 / 2) * θ) - Real.cos (((j : ℝ) + 1 / 2) * θ)) =
            ∑ k ∈ Finset.range (b - a),
              (Real.cos ((((a + k : ℕ) : ℝ) + 1 / 2) * θ) -
                Real.cos ((((a + (k + 1) : ℕ) : ℝ) + 1 / 2) * θ)) := by
        rw [Finset.sum_Ico_eq_sum_range]
        have hlen : b + 1 - (a + 1) = b - a := by omega
        rw [hlen]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hL : (((a + 1 + k : ℕ) : ℝ) - 1 / 2) = ((a + k : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
        have hR : (((a + 1 + k : ℕ) : ℝ) + 1 / 2) = ((a + (k + 1) : ℕ) : ℝ) + 1 / 2 := by
          push_cast; ring
        rw [hL, hR]
      rw [hshift]
      have hsub := Finset.sum_range_sub' (fun k => Real.cos ((((a + k : ℕ) : ℝ) + 1 / 2) * θ))
        (b - a)
      have hba : a + (b - a) = b := by omega
      simpa [hba] using hsub
    have habs_mul : |2 * Real.sin (θ / 2) *
        ∑ j ∈ Finset.Icc (a + 1) b, Real.sin ((j : ℝ) * θ)| ≤ 2 := by
      rw [htele]
      calc
        |Real.cos (((a : ℝ) + 1 / 2) * θ) - Real.cos (((b : ℝ) + 1 / 2) * θ)|
            ≤ |Real.cos (((a : ℝ) + 1 / 2) * θ)| + |Real.cos (((b : ℝ) + 1 / 2) * θ)| :=
              abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
        _ = 2 := by norm_num
    rw [abs_mul, abs_of_pos (mul_pos two_pos hsin_pos)] at habs_mul
    have hdiv : |∑ j ∈ Finset.Icc (a + 1) b, Real.sin ((j : ℝ) * θ)| ≤ 1 / Real.sin (θ / 2) := by
      rw [le_div_iff₀ hsin_pos]
      linarith
    have hinv : 1 / Real.sin (θ / 2) ≤ Real.pi / θ := by
      rw [div_le_div_iff₀ hsin_pos hθ0]
      have := (div_le_iff₀ Real.pi_pos).mp hsin_lb
      linarith
    exact hdiv.trans hinv

private lemma abel_sum_Icc (N m : ℕ) (hNm : N + 1 ≤ m) (f : ℕ → ℝ) :
    let T : ℕ → ℝ := fun r => ∑ j ∈ Finset.Icc (N + 1) r, f j
    ∑ j ∈ Finset.Icc (N + 1) m, f j / (j : ℝ) =
      T m / (m : ℝ) +
        ∑ j ∈ Finset.Icc (N + 1) (m - 1), T j * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) := by
  intro T
  induction m, hNm using Nat.le_induction with
  | base =>
    simp [T]
  | succ k hk ih =>
    have hIcc1 : Finset.Icc (N + 1) (k + 1) = insert (k + 1) (Finset.Icc (N + 1) k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem1 : k + 1 ∉ Finset.Icc (N + 1) k := by simp
    have hIcc2 : Finset.Icc (N + 1) k = insert k (Finset.Icc (N + 1) (k - 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem2 : k ∉ Finset.Icc (N + 1) (k - 1) := by
      simp only [Finset.mem_Icc, not_and, not_le]; intro _; omega
    have hTsucc : T (k + 1) = T k + f (k + 1) := by
      dsimp [T]
      rw [hIcc1, Finset.sum_insert hnotmem1, add_comm]
    rw [hIcc1, Finset.sum_insert hnotmem1, ih]
    have hsub1 : k + 1 - 1 = k := by omega
    rw [hsub1, hIcc2, Finset.sum_insert hnotmem2, hTsucc]
    ring

private lemma fejer_dirichlet_sin_sum_bound_Ioo (m : ℕ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi) :
    |∑ j ∈ Finset.Icc 1 m, Real.sin ((j : ℝ) * θ) / (j : ℝ)| ≤ 1 + Real.pi := by
  let N : ℕ := min m ⌊1 / θ⌋₊
  have hN_le_m : N ≤ m := min_le_left _ _
  have hN_le_fl : N ≤ ⌊1 / θ⌋₊ := min_le_right _ _
  have hsplit : Finset.Icc 1 m = Finset.Icc 1 N ∪ Finset.Icc (N + 1) m := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) m) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_Icc] at hj1 hj2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hpart1 : |∑ j ∈ Finset.Icc 1 N, Real.sin ((j : ℝ) * θ) / (j : ℝ)| ≤ 1 := by
    calc
      |∑ j ∈ Finset.Icc 1 N, Real.sin ((j : ℝ) * θ) / (j : ℝ)|
          ≤ ∑ j ∈ Finset.Icc 1 N, |Real.sin ((j : ℝ) * θ) / (j : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.Icc 1 N, θ := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj_pos : (0 : ℝ) < (j : ℝ) := by
              have := (Finset.mem_Icc.mp hj).1; exact_mod_cast this
            rw [abs_div, abs_of_pos hj_pos, div_le_iff₀ hj_pos]
            have hsin : |Real.sin ((j : ℝ) * θ)| ≤ |(j : ℝ) * θ| := Real.abs_sin_le_abs
            rw [abs_of_pos (mul_pos hj_pos hθ0)] at hsin
            linarith
      _ = (N : ℝ) * θ := by simp
      _ ≤ (⌊1 / θ⌋₊ : ℝ) * θ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hN_le_fl) hθ0.le
      _ ≤ (1 / θ) * θ :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (div_nonneg zero_le_one hθ0.le)) hθ0.le
      _ = 1 := one_div_mul_cancel hθ0.ne'
  have hpart2 : |∑ j ∈ Finset.Icc (N + 1) m, Real.sin ((j : ℝ) * θ) / (j : ℝ)| ≤ Real.pi := by
    by_cases hNm : m < N + 1
    · have hempty : Finset.Icc (N + 1) m = ∅ := Finset.Icc_eq_empty (by omega)
      rw [hempty, Finset.sum_empty, abs_zero]
      exact Real.pi_pos.le
    · push Not at hNm
      have hN_eq : N = ⌊1 / θ⌋₊ := by
        dsimp [N]
        exact min_eq_right (by omega)
      have hN_gt : 1 / θ < ((N + 1 : ℕ) : ℝ) := by
        rw [hN_eq]; push_cast; exact Nat.lt_floor_add_one (1 / θ)
      have hAbel := abel_sum_Icc N m hNm (fun j => Real.sin ((j : ℝ) * θ))
      dsimp only at hAbel
      rw [hAbel]
      let T : ℕ → ℝ := fun r => ∑ j ∈ Finset.Icc (N + 1) r, Real.sin ((j : ℝ) * θ)
      have hT_bdd : ∀ r, |T r| ≤ Real.pi / θ := fun r => sin_sum_Icc_bound hθ0 hθ1 N r
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
      have htele_inv :
          (1 : ℝ) / (m : ℝ) +
            ∑ j ∈ Finset.Icc (N + 1) (m - 1), (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) =
            1 / ((N + 1 : ℕ) : ℝ) := by
        clear hAbel hN_eq hN_gt hpart1 hsplit hdisj hN_le_m hN_le_fl
        induction m, hNm using Nat.le_induction with
        | base =>
          simp
        | succ k hk ihk =>
          have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
          have hsub1 : k + 1 - 1 = k := by omega
          have hIcc : Finset.Icc (N + 1) k = insert k (Finset.Icc (N + 1) (k - 1)) := by
            ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hnm : k ∉ Finset.Icc (N + 1) (k - 1) := by
            simp only [Finset.mem_Icc, not_and, not_le]; intro _; omega
          rw [hsub1, hIcc, Finset.sum_insert hnm]
          linarith [ihk hk_pos]
      have h1 : |T m / (m : ℝ)| ≤ (Real.pi / θ) * (1 / (m : ℝ)) := by
        rw [abs_div, abs_of_pos hm_pos, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right (hT_bdd m) (by positivity)
      have h2 : |∑ j ∈ Finset.Icc (N + 1) (m - 1),
            T j * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))| ≤
          (Real.pi / θ) *
            ∑ j ∈ Finset.Icc (N + 1) (m - 1), (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) := by
        calc
          |∑ j ∈ Finset.Icc (N + 1) (m - 1), T j * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))|
              ≤ ∑ j ∈ Finset.Icc (N + 1) (m - 1),
                  |T j * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.Icc (N + 1) (m - 1),
                (Real.pi / θ) * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj_pos : (0 : ℝ) < (j : ℝ) := by
                have := (Finset.mem_Icc.mp hj).1; exact_mod_cast (show 0 < j by omega)
              have hdiff_nn : 0 ≤ 1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) := by
                rw [sub_nonneg]
                exact one_div_le_one_div_of_le hj_pos (by push_cast; linarith)
              rw [abs_mul, abs_of_nonneg hdiff_nn]
              exact mul_le_mul_of_nonneg_right (hT_bdd j) hdiff_nn
          _ = _ := by rw [← Finset.mul_sum]
      calc
        |T m / (m : ℝ) + ∑ j ∈ Finset.Icc (N + 1) (m - 1),
            T j * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))|
            ≤ |T m / (m : ℝ)| + |∑ j ∈ Finset.Icc (N + 1) (m - 1),
                T j * (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))| := abs_add_le _ _
        _ ≤ (Real.pi / θ) * (1 / (m : ℝ)) +
            (Real.pi / θ) * ∑ j ∈ Finset.Icc (N + 1) (m - 1),
              (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) := add_le_add h1 h2
        _ = (Real.pi / θ) * ((1 : ℝ) / (m : ℝ) +
            ∑ j ∈ Finset.Icc (N + 1) (m - 1), (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))) := by ring
        _ = (Real.pi / θ) * (1 / ((N + 1 : ℕ) : ℝ)) := by rw [htele_inv]
        _ ≤ (Real.pi / θ) * θ := by
            refine mul_le_mul_of_nonneg_left ?_ (div_nonneg Real.pi_pos.le hθ0.le)
            have hN1_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
            rw [div_le_iff₀ hN1_pos]
            have := (div_lt_iff₀ hθ0).mp hN_gt
            linarith
        _ = Real.pi := div_mul_cancel₀ Real.pi hθ0.ne'
  exact (abs_add_le _ _).trans (add_le_add hpart1 hpart2)

private lemma fejer_dirichlet_sin_sum_bound (m : ℕ) (θ : ℝ) :
    |∑ j ∈ Finset.Icc 1 m, Real.sin ((j : ℝ) * θ) / (j : ℝ)| ≤ 1 + Real.pi := by
  have h2pi_pos : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  let k : ℤ := ⌊θ / (2 * Real.pi)⌋
  let θ₁ : ℝ := θ - (k : ℝ) * (2 * Real.pi)
  have hθ₁_ge : 0 ≤ θ₁ := by
    dsimp [θ₁, k]
    have := Int.floor_le (θ / (2 * Real.pi))
    have := (le_div_iff₀ h2pi_pos).mp this
    linarith
  have hθ₁_lt : θ₁ < 2 * Real.pi := by
    dsimp [θ₁, k]
    have := Int.lt_floor_add_one (θ / (2 * Real.pi))
    have := (div_lt_iff₀ h2pi_pos).mp this
    linarith
  have hshift : ∀ j : ℕ, Real.sin ((j : ℝ) * θ) = Real.sin ((j : ℝ) * θ₁) := by
    intro j
    have harg : (j : ℝ) * θ = (j : ℝ) * θ₁ + ((j : ℤ) * k : ℤ) * (2 * Real.pi) := by
      dsimp [θ₁]; push_cast; ring
    rw [harg, Real.sin_add_int_mul_two_pi]
  rw [Finset.sum_congr rfl fun j _ => by rw [hshift j]]
  by_cases h0 : θ₁ = 0
  · rw [h0]; simp; linarith [Real.pi_pos]
  · by_cases hpi : θ₁ = Real.pi
    · rw [hpi]
      have hzero : ∀ j : ℕ, Real.sin ((j : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi
      simp [hzero]; linarith [Real.pi_pos]
    · rcases lt_or_gt_of_ne hpi with hlt | hgt
      · exact fejer_dirichlet_sin_sum_bound_Ioo m (lt_of_le_of_ne hθ₁_ge (Ne.symm h0)) hlt
      · let θ₂ : ℝ := 2 * Real.pi - θ₁
        have hθ₂_0 : 0 < θ₂ := by dsimp [θ₂]; linarith
        have hθ₂_1 : θ₂ < Real.pi := by dsimp [θ₂]; linarith
        have hrefl : ∀ j : ℕ, Real.sin ((j : ℝ) * θ₁) = -Real.sin ((j : ℝ) * θ₂) := by
          intro j
          have harg : (j : ℝ) * θ₁ = -((j : ℝ) * θ₂) + (j : ℤ) * (2 * Real.pi) := by
            dsimp [θ₂]; push_cast; ring
          rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_neg]
        have hsum_neg :
            ∑ j ∈ Finset.Icc 1 m, Real.sin ((j : ℝ) * θ₁) / (j : ℝ) =
              -(∑ j ∈ Finset.Icc 1 m, Real.sin ((j : ℝ) * θ₂) / (j : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hrefl j, neg_div]
        rw [hsum_neg, abs_neg]
        exact fejer_dirichlet_sin_sum_bound_Ioo m hθ₂_0 hθ₂_1

private lemma log_le_harmonic (m : ℕ) :
    Real.log ((m : ℝ) + 1) ≤ ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : k + 1 ∉ Finset.Icc 1 k := by simp
    rw [hIcc, Finset.sum_insert hnm]
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    have hstep : Real.log (((k + 1 : ℕ) : ℝ) + 1) - Real.log ((k : ℝ) + 1) ≤
        1 / ((k + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div hk2_pos.ne' hk1_pos.ne']
      have hratio : (((k + 1 : ℕ) : ℝ) + 1) / ((k : ℝ) + 1) = 1 + 1 / ((k + 1 : ℕ) : ℝ) := by
        push_cast; field_simp
      rw [hratio]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / ((k + 1 : ℕ) : ℝ) by positivity)
      linarith
    linarith

/-- **Faber (1914) / Berman–Marcinkiewicz Universal Lebesgue Function Lower Bound:**
For EVERY `n ≥ 1` and EVERY injective node array `a : Fin n → ℝ` in `[-1, 1]`, there exists
`x ∈ [-1, 1]` where the Lebesgue function satisfies
`Λ_n(x) ≥ (1 / (4 * (1 + π))) * log n`.
Proved from scratch via purely discrete cosine orthogonality, Chebyshev polynomials, and
Fejér–Dirichlet Abel summation (zero measure theory). -/
theorem ppl128_faber_lebesgue_lower_bound {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (ha_mem : ∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      (1 / (4 * (1 + Real.pi))) * Real.log (n : ℝ) ≤
        ∑ i : Fin n, |∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)| := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp only [Nat.cast_one, Real.log_one, mul_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · let m : ℕ := n - 1
    have hm_pos : 1 ≤ m := by omega
    have hmn : m + 1 = n := by omega
    let M : ℕ := 4 * m + 4
    have hM_pos : 0 < M := by omega
    let Fm : ℝ → ℝ := fun θ =>
      (∑ j ∈ Finset.Icc 1 m, Real.sin ((j : ℝ) * θ) / (j : ℝ)) *
        Real.sin (((m + 1 : ℕ) : ℝ) * θ)
    have hFm_bdd : ∀ θ : ℝ, |Fm θ| ≤ 1 + Real.pi := by
      intro θ
      dsimp [Fm]
      rw [abs_mul]
      calc
        |∑ j ∈ Finset.Icc 1 m, Real.sin ((j : ℝ) * θ) / (j : ℝ)| *
            |Real.sin (((m + 1 : ℕ) : ℝ) * θ)|
            ≤ (1 + Real.pi) * 1 :=
              mul_le_mul (fejer_dirichlet_sin_sum_bound m θ) (Real.abs_sin_le_one _)
                (abs_nonneg _) (by linarith [Real.pi_pos])
        _ = 1 + Real.pi := mul_one _
    have hFm_cos : ∀ θ : ℝ, Fm θ =
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 1 m,
          (Real.cos (((m + 1 - j : ℕ) : ℝ) * θ) - Real.cos (((m + 1 + j : ℕ) : ℝ) * θ)) /
            (j : ℝ) := by
      intro θ
      dsimp [Fm]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ m := (Finset.mem_Icc.mp hj).2
      have h1 : ((m + 1 - j : ℕ) : ℝ) * θ = ((m + 1 : ℕ) : ℝ) * θ - (j : ℝ) * θ := by
        rw [Nat.cast_sub (by omega)]; ring
      have h2 : ((m + 1 + j : ℕ) : ℝ) * θ = ((m + 1 : ℕ) : ℝ) * θ + (j : ℝ) * θ := by
        push_cast; ring
      rw [h1, h2, Real.cos_sub, Real.cos_add]
      ring
    let gt : ℝ → ℝ → ℝ := fun t x =>
      (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 1 m,
        (Real.cos (((m + 1 - j : ℕ) : ℝ) * t) * (chebT (m + 1 - j)).eval x -
          Real.cos (((m + 1 + j : ℕ) : ℝ) * t) * (chebT (m + 1 + j)).eval x) / (j : ℝ)
    have hgt_bdd : ∀ t : ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |gt t x| ≤ 1 + Real.pi := by
      intro t x hx
      let u : ℝ := Real.arccos x
      have hxu : x = Real.cos u := (Real.cos_arccos hx.1 hx.2).symm
      have hgt_eq : gt t x = (1 / 2 : ℝ) * (Fm (u + t) + Fm (u - t)) := by
        rw [hFm_cos (u + t), hFm_cos (u - t), hxu]
        dsimp [gt]
        rw [← mul_add, ← Finset.sum_add_distrib]
        rw [Finset.mul_sum (a := (1 / 2 : ℝ)), Finset.mul_sum (a := (1 / 2 : ℝ)),
          Finset.mul_sum (a := (1 / 2 : ℝ))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [chebT_eval_cos, chebT_eval_cos]
        have hcos1 : Real.cos (((m + 1 - j : ℕ) : ℝ) * (u + t)) +
            Real.cos (((m + 1 - j : ℕ) : ℝ) * (u - t)) =
            2 * Real.cos (((m + 1 - j : ℕ) : ℝ) * t) *
              Real.cos (((m + 1 - j : ℕ) : ℝ) * u) := by
          have ha1 : ((m + 1 - j : ℕ) : ℝ) * (u + t) =
              ((m + 1 - j : ℕ) : ℝ) * u + ((m + 1 - j : ℕ) : ℝ) * t := by ring
          have hb1 : ((m + 1 - j : ℕ) : ℝ) * (u - t) =
              ((m + 1 - j : ℕ) : ℝ) * u - ((m + 1 - j : ℕ) : ℝ) * t := by ring
          rw [ha1, hb1, Real.cos_add, Real.cos_sub]; ring
        have hcos2 : Real.cos (((m + 1 + j : ℕ) : ℝ) * (u + t)) +
            Real.cos (((m + 1 + j : ℕ) : ℝ) * (u - t)) =
            2 * Real.cos (((m + 1 + j : ℕ) : ℝ) * t) *
              Real.cos (((m + 1 + j : ℕ) : ℝ) * u) := by
          have ha2 : ((m + 1 + j : ℕ) : ℝ) * (u + t) =
              ((m + 1 + j : ℕ) : ℝ) * u + ((m + 1 + j : ℕ) : ℝ) * t := by ring
          have hb2 : ((m + 1 + j : ℕ) : ℝ) * (u - t) =
              ((m + 1 + j : ℕ) : ℝ) * u - ((m + 1 + j : ℕ) : ℝ) * t := by ring
          rw [ha2, hb2, Real.cos_add, Real.cos_sub]; ring
        have hcomb :
            (Real.cos (((m + 1 - j : ℕ) : ℝ) * (u + t)) -
              Real.cos (((m + 1 + j : ℕ) : ℝ) * (u + t))) +
            (Real.cos (((m + 1 - j : ℕ) : ℝ) * (u - t)) -
              Real.cos (((m + 1 + j : ℕ) : ℝ) * (u - t))) =
            2 * (Real.cos (((m + 1 - j : ℕ) : ℝ) * t) *
                  Real.cos (((m + 1 - j : ℕ) : ℝ) * u) -
                Real.cos (((m + 1 + j : ℕ) : ℝ) * t) *
                  Real.cos (((m + 1 + j : ℕ) : ℝ) * u)) := by
          linarith
        calc
          1 / 2 * ((Real.cos (((m + 1 - j : ℕ) : ℝ) * t) *
                Real.cos (((m + 1 - j : ℕ) : ℝ) * u) -
              Real.cos (((m + 1 + j : ℕ) : ℝ) * t) *
                Real.cos (((m + 1 + j : ℕ) : ℝ) * u)) / (j : ℝ))
              = 1 / 2 * ((1 / 2) * (2 * (Real.cos (((m + 1 - j : ℕ) : ℝ) * t) *
                  Real.cos (((m + 1 - j : ℕ) : ℝ) * u) -
                Real.cos (((m + 1 + j : ℕ) : ℝ) * t) *
                  Real.cos (((m + 1 + j : ℕ) : ℝ) * u))) / (j : ℝ)) := by ring
          _ = 1 / 2 * ((1 / 2) * ((Real.cos (((m + 1 - j : ℕ) : ℝ) * (u + t)) -
                Real.cos (((m + 1 + j : ℕ) : ℝ) * (u + t))) +
              (Real.cos (((m + 1 - j : ℕ) : ℝ) * (u - t)) -
                Real.cos (((m + 1 + j : ℕ) : ℝ) * (u - t)))) / (j : ℝ)) := by rw [hcomb]
          _ = _ := by ring
      rw [hgt_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc
        (1 / 2 : ℝ) * |Fm (u + t) + Fm (u - t)|
            ≤ (1 / 2 : ℝ) * (|Fm (u + t)| + |Fm (u - t)|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
        _ ≤ (1 / 2 : ℝ) * ((1 + Real.pi) + (1 + Real.pi)) :=
              mul_le_mul_of_nonneg_left (add_le_add (hFm_bdd _) (hFm_bdd _)) (by norm_num)
        _ = 1 + Real.pi := by ring
    let ts : ℕ → ℝ := fun s => 2 * Real.pi * (s : ℝ) / (M : ℝ)
    -- Linearity of lagInterpVal on gt t
    have hL_gt : ∀ t x : ℝ,
        lagInterpVal a (gt t) x =
          (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 1 m,
            (Real.cos (((m + 1 - j : ℕ) : ℝ) * t) *
                lagInterpVal a (fun y => (chebT (m + 1 - j)).eval y) x -
              Real.cos (((m + 1 + j : ℕ) : ℝ) * t) *
                lagInterpVal a (fun y => (chebT (m + 1 + j)).eval y) x) / (j : ℝ) := by
      intro t x
      unfold lagInterpVal
      dsimp [gt]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      congr 1
      simp_rw [Finset.sum_mul, Finset.sum_comm (s := Finset.univ) (t := Finset.Icc 1 m)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      congr 1
      simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    -- Orthogonality for high frequencies k > m
    have hhigh_zero : ∀ k : ℕ, m + 1 < k → k ≤ 2 * m + 1 →
        ∑ s ∈ Finset.range M,
          Real.cos ((k : ℝ) * ts s) *
            lagInterpVal a (fun y => (chebT k).eval y) (Real.cos (ts s)) = 0 := by
      intro k hk_gt hk_le
      let q : Polynomial ℝ := Lagrange.interpolate Finset.univ a (fun i => (chebT k).eval (a i))
      have hq_deg : q.natDegree ≤ m := by
        have hlt : q.degree < (Finset.univ : Finset (Fin n)).card :=
          Lagrange.degree_interpolate_lt _ fun _ _ _ _ h => ha h
        rw [Finset.card_univ, Fintype.card_fin] at hlt
        by_cases hq0 : q = 0
        · rw [hq0]; simp
        · rw [Polynomial.degree_eq_natDegree hq0] at hlt
          have hlt' : q.natDegree < n := by exact_mod_cast hlt
          omega
      rcases poly_eq_sum_chebT m q hq_deg with ⟨c, hc⟩
      have hq_eval : ∀ s : ℕ,
          lagInterpVal a (fun y => (chebT k).eval y) (Real.cos (ts s)) =
            ∑ r : Fin (m + 1), c r * Real.cos ((r.1 : ℝ) * ts s) := by
        intro s
        rw [← lagInterp_eval_eq]
        change q.eval (Real.cos (ts s)) = _
        rw [hc, Polynomial.eval_finsetSum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_C, chebT_eval_cos]
      simp_rw [hq_eval, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun r _ => ?_
      have hpull :
          ∑ s ∈ Finset.range M,
              Real.cos ((k : ℝ) * ts s) * (c r * Real.cos ((r.1 : ℝ) * ts s)) =
            c r * ∑ s ∈ Finset.range M,
              Real.cos (2 * Real.pi * (k : ℝ) * (s : ℝ) / (M : ℝ)) *
                Real.cos (2 * Real.pi * (r.1 : ℝ) * (s : ℝ) / (M : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        have h1 : (k : ℝ) * ts s = 2 * Real.pi * (k : ℝ) * (s : ℝ) / (M : ℝ) := by
          dsimp [ts]; ring
        have h2 : (r.1 : ℝ) * ts s = 2 * Real.pi * (r.1 : ℝ) * (s : ℝ) / (M : ℝ) := by
          dsimp [ts]; ring
        rw [h1, h2]; ring
      rw [hpull, sum_cos_mul_cos_equispaced (by omega) (by have := r.isLt; omega)]
      have hne : k ≠ r.1 := by have := r.isLt; omega
      simp [hne]
    -- Exact evaluation of discrete average
    have havg :
        ∑ s ∈ Finset.range M, lagInterpVal a (gt (ts s)) (Real.cos (ts s)) =
          ((M : ℝ) / 4) * ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ) := by
      simp_rw [hL_gt]
      rw [← Finset.mul_sum, Finset.sum_comm]
      have hterm_j : ∀ j ∈ Finset.Icc 1 m,
          ∑ s ∈ Finset.range M,
            (Real.cos (((m + 1 - j : ℕ) : ℝ) * ts s) *
                lagInterpVal a (fun y => (chebT (m + 1 - j)).eval y) (Real.cos (ts s)) -
              Real.cos (((m + 1 + j : ℕ) : ℝ) * ts s) *
                lagInterpVal a (fun y => (chebT (m + 1 + j)).eval y) (Real.cos (ts s))) /
              (j : ℝ) = ((M : ℝ) / 2) * (1 / (j : ℝ)) := by
        intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hjm : j ≤ m := (Finset.mem_Icc.mp hj).2
        rw [← Finset.sum_div, Finset.sum_sub_distrib]
        have hhi := hhigh_zero (m + 1 + j) (by omega) (by omega)
        rw [hhi, sub_zero]
        have hlo_deg : (chebT (m + 1 - j)).natDegree < n := by
          rw [(chebT_natDegree_and_coeff _).1]; omega
        have hlo_eval : ∀ s : ℕ,
            lagInterpVal a (fun y => (chebT (m + 1 - j)).eval y) (Real.cos (ts s)) =
              Real.cos (((m + 1 - j : ℕ) : ℝ) * ts s) := by
          intro s
          rw [lagInterp_reproduces_poly hn ha _ hlo_deg, chebT_eval_cos]
        simp_rw [hlo_eval]
        have harg : ∀ s : ℕ,
            Real.cos (((m + 1 - j : ℕ) : ℝ) * ts s) *
              Real.cos (((m + 1 - j : ℕ) : ℝ) * ts s) =
            Real.cos (2 * Real.pi * ((m + 1 - j : ℕ) : ℝ) * (s : ℝ) / (M : ℝ)) *
              Real.cos (2 * Real.pi * ((m + 1 - j : ℕ) : ℝ) * (s : ℝ) / (M : ℝ)) := by
          intro s
          have : ((m + 1 - j : ℕ) : ℝ) * ts s =
              2 * Real.pi * ((m + 1 - j : ℕ) : ℝ) * (s : ℝ) / (M : ℝ) := by dsimp [ts]; ring
          rw [this]
        rw [Finset.sum_congr rfl fun s _ => harg s,
          sum_cos_mul_cos_equispaced (by omega) (by omega)]
        simp only [↓reduceIte]
        ring
      rw [Finset.sum_congr rfl hterm_j, ← Finset.mul_sum]
      ring
    -- Lower bound the discrete average by (M / 4) * log n
    have havg_lb : ((M : ℝ) / 4) * Real.log (n : ℝ) ≤
        ∑ s ∈ Finset.range M, lagInterpVal a (gt (ts s)) (Real.cos (ts s)) := by
      rw [havg]
      have hlog : Real.log (n : ℝ) ≤ ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ) := by
        have hcast : (n : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hmn.symm
        rw [hcast]
        exact log_le_harmonic m
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    -- Pigeonhole over s ∈ range M
    have hex_s : ∃ s ∈ Finset.range M,
        (1 / 4 : ℝ) * Real.log (n : ℝ) ≤ lagInterpVal a (gt (ts s)) (Real.cos (ts s)) := by
      by_contra hall
      push Not at hall
      have hsum_lt :
          ∑ s ∈ Finset.range M, lagInterpVal a (gt (ts s)) (Real.cos (ts s)) <
            ∑ _s ∈ Finset.range M, (1 / 4 : ℝ) * Real.log (n : ℝ) :=
        Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hM_pos.ne') hall
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_lt
      linarith
    rcases hex_s with ⟨s, _, hs⟩
    let x : ℝ := Real.cos (ts s)
    have hx : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have hupper_x : lagInterpVal a (gt (ts s)) x ≤ (1 + Real.pi) * lebesgueFn a x := by
      calc
        lagInterpVal a (gt (ts s)) x ≤ |lagInterpVal a (gt (ts s)) x| := le_abs_self _
        _ ≤ ∑ i : Fin n, |gt (ts s) (a i) * lagBasisVal a i x| :=
              Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin n, |gt (ts s) (a i)| * |lagBasisVal a i x| :=
              Finset.sum_congr rfl fun i _ => abs_mul _ _
        _ ≤ ∑ i : Fin n, (1 + Real.pi) * |lagBasisVal a i x| :=
              Finset.sum_le_sum fun i _ =>
                mul_le_mul_of_nonneg_right (hgt_bdd (ts s) (a i) (ha_mem i)) (abs_nonneg _)
        _ = (1 + Real.pi) * lebesgueFn a x := by unfold lebesgueFn; rw [← Finset.mul_sum]
    refine ⟨x, hx, ?_⟩
    have h1pi : 0 < 1 + Real.pi := by linarith [Real.pi_pos]
    have h4pi : 0 < 4 * (1 + Real.pi) := by linarith
    change (1 / (4 * (1 + Real.pi))) * Real.log (n : ℝ) ≤ lebesgueFn a x
    have hcomb : (1 / 4 : ℝ) * Real.log (n : ℝ) ≤ (1 + Real.pi) * lebesgueFn a x :=
      hs.trans hupper_x
    rw [one_div_mul_eq_div, div_le_iff₀ h4pi]
    linarith

/-- **Faber (1914) Universal Lebesgue Constant Lower Bound (`sSup` & Explicit `1/17` Constant):**
For every `n ≥ 1` and every injective node vector `a : Fin n → ℝ` in `[-1, 1]`, the Lebesgue
constant `Λ_n = sup_{x ∈ [-1, 1]} Λ_n(x)` satisfies both
`Λ_n ≥ (1 / (4 * (1 + π))) * log n` and `Λ_n ≥ (1 / 17) * log n`. -/
theorem ppl128_faber_lebesgue_sup_lower_bound {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℝ}
    (ha : Function.Injective a) (ha_mem : ∀ i, a i ∈ Set.Icc (-1 : ℝ) 1) :
    (1 / (4 * (1 + Real.pi))) * Real.log (n : ℝ) ≤
      sSup ((fun x : ℝ => ∑ i : Fin n,
          |∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)|) '' Set.Icc (-1 : ℝ) 1) ∧
    (1 / 17 : ℝ) * Real.log (n : ℝ) ≤
      sSup ((fun x : ℝ => ∑ i : Fin n,
          |∏ j ∈ Finset.univ.erase i, (x - a j) / (a i - a j)|) '' Set.Icc (-1 : ℝ) 1) := by
  have hbdd : BddAbove ((fun x : ℝ => lebesgueFn a x) '' Set.Icc (-1 : ℝ) 1) :=
    (isCompact_Icc.image (lebesgueFn_continuous a)).bddAbove
  rcases ppl128_faber_lebesgue_lower_bound hn ha ha_mem with ⟨x, hx, hx_lb⟩
  have hsup : (1 / (4 * (1 + Real.pi))) * Real.log (n : ℝ) ≤
      sSup ((fun x : ℝ => lebesgueFn a x) '' Set.Icc (-1 : ℝ) 1) :=
    hx_lb.trans (le_csSup hbdd ⟨x, hx, rfl⟩)
  refine ⟨hsup, ?_⟩
  have hlog_nn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hconst : (1 / 17 : ℝ) ≤ 1 / (4 * (1 + Real.pi)) := by
    rw [one_div_le_one_div (by norm_num) (by linarith [Real.pi_pos])]
    linarith
  exact (mul_le_mul_of_nonneg_right hconst hlog_nn).trans hsup

/-- **Faber's Divergence Theorem (1914) — Failure of Uniform Convergence for Every Node Array:**
For EVERY triangular array of distinct nodes `a : ∀ n, Fin (n + 1) → ℝ` in `[-1, 1]`, there exists
a continuous function `f : ℝ → ℝ` whose Lagrange interpolants are uniformly unbounded on `[-1, 1]`
(`∀ B, ∃ n, ∃ x ∈ [-1, 1], B < |L^{n+1} f(x)|`), and hence do NOT converge uniformly to `f`. -/
theorem ppl128_faber_uniform_divergence_theorem
    (a : ∀ n : ℕ, Fin (n + 1) → ℝ)
    (ha : ∀ n, Function.Injective (a n))
    (ha_mem : ∀ n i, a n i ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ B : ℝ, ∃ n : ℕ, ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        B < |∑ i : Fin (n + 1), f (a n i) *
          ∏ j ∈ Finset.univ.erase i, (x - a n j) / (a n i - a n j)| := by
  let V : ℕ → Set C(Set.Icc (-1 : ℝ) 1, ℝ) := fun k =>
    {f | ∃ n : ℕ, ∃ x ∈ Set.Icc (-1 : ℝ) 1,
      (k : ℝ) < |∑ i : Fin (n + 1), f ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x|}
  have hV_open : ∀ k : ℕ, IsOpen (V k) := by
    intro k
    have hEq : V k = ⋃ (n : ℕ) (x : Set.Icc (-1 : ℝ) 1),
        (fun f : C(Set.Icc (-1 : ℝ) 1, ℝ) =>
          |∑ i : Fin (n + 1), f ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x.1|) ⁻¹'
            Set.Ioi (k : ℝ) := by
      ext f
      simp only [V, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_Ioi,
        Subtype.exists]
      constructor
      · rintro ⟨n, x, hx, hlt⟩; exact ⟨n, x, hx, hlt⟩
      · rintro ⟨n, x, hx, hlt⟩; exact ⟨n, x, hx, hlt⟩
    rw [hEq]
    refine isOpen_iUnion fun n => isOpen_iUnion fun x => isOpen_Ioi.preimage ?_
    refine Continuous.abs ?_
    exact continuous_finsetSum _ fun i _ =>
      (continuous_eval_Icc ⟨a n i, ha_mem n i⟩).mul continuous_const
  have hV_dense : ∀ k : ℕ, Dense (V k) := by
    intro k
    rw [Metric.dense_iff]
    intro f₀ ε hε
    by_cases hf₀ : f₀ ∈ V k
    · exact ⟨f₀, Metric.mem_ball_self hε, hf₀⟩
    · simp only [V, Set.mem_ofPred_eq, not_exists] at hf₀
      let r : ℝ := ε / 2
      have hr : 0 < r := half_pos hε
      let B : ℝ := (2 * (k : ℝ) + 2) / r
      let N : ℕ := ⌈Real.exp (17 * max B 0 + 1)⌉₊
      have hN_gt : Real.exp (17 * max B 0 + 1) < ((N + 1 : ℕ) : ℝ) := by
        have hle := Nat.le_ceil (Real.exp (17 * max B 0 + 1))
        push_cast; linarith
      have hlog_gt : 17 * max B 0 + 1 < Real.log ((N + 1 : ℕ) : ℝ) := by
        rw [← Real.log_exp (17 * max B 0 + 1)]
        exact Real.log_lt_log (Real.exp_pos _) hN_gt
      rcases ppl128_faber_lebesgue_lower_bound (Nat.succ_pos N) (ha N) (ha_mem N) with
        ⟨x, hx, hx_lb⟩
      have hpi : Real.pi < 3.15 := Real.pi_lt_d2
      have hconst : (1 / 17 : ℝ) ≤ 1 / (4 * (1 + Real.pi)) := by
        rw [one_div_le_one_div (by norm_num) (by linarith [Real.pi_pos])]
        linarith
      have hlog_nn : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.succ_pos N)
      have hbig : B < lebesgueFn (a N) x := by
        have h1 : (1 / 17 : ℝ) * Real.log ((N + 1 : ℕ) : ℝ) ≤ lebesgueFn (a N) x :=
          (mul_le_mul_of_nonneg_right hconst hlog_nn).trans hx_lb
        have h2 : max B 0 < (1 / 17 : ℝ) * Real.log ((N + 1 : ℕ) : ℝ) := by linarith
        exact (le_max_left B 0).trans_lt (h2.trans_le h1)
      rcases exists_unit_attaining_lebesgue (Nat.succ_pos N) (ha N) x with
        ⟨g, hg_cont, hg_bdd, hg_eq⟩
      let gC : C(Set.Icc (-1 : ℝ) 1, ℝ) := restrictIcc g hg_cont
      have hg_norm : ‖gC‖ ≤ 1 := norm_restrictIcc_le hg_cont zero_le_one fun t _ => hg_bdd t
      let f : C(Set.Icc (-1 : ℝ) 1, ℝ) := f₀ + r • gC
      refine ⟨f, ?_, N, x, hx, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        have hsub : f - f₀ = r • gC := by simp [f]
        rw [hsub, norm_smul, Real.norm_of_nonneg hr.le]
        calc
          r * ‖gC‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hg_norm hr.le
          _ = ε / 2 := by rw [mul_one]
          _ < ε := half_lt_self hε
      · have hsum_eq :
            ∑ i : Fin (N + 1), f ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x =
              (∑ i : Fin (N + 1), f₀ ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x) +
                r * lebesgueFn (a N) x := by
          have hg_sum : ∑ i : Fin (N + 1), gC ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x =
              lebesgueFn (a N) x := by
            simpa [gC, restrictIcc, lagInterpVal] using hg_eq
          calc
            ∑ i : Fin (N + 1), f ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x
                = ∑ i : Fin (N + 1),
                    (f₀ ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x +
                      r * (gC ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x)) :=
                  Finset.sum_congr rfl fun i _ => by simp [f]; ring
            _ = (∑ i : Fin (N + 1), f₀ ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x) +
                  r * (∑ i : Fin (N + 1), gC ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            _ = _ := by rw [hg_sum]
        rw [hsum_eq]
        have h1 : 2 * (k : ℝ) + 2 < r * lebesgueFn (a N) x := by
          have := (div_lt_iff₀ hr).mp hbig
          linarith
        have h0 : |∑ i : Fin (N + 1), f₀ ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x| ≤ k :=
          not_lt.mp fun hlt => hf₀ N x ⟨hx, hlt⟩
        have htri := abs_sub_abs_le_abs_add
          (r * lebesgueFn (a N) x)
          (∑ i : Fin (N + 1), f₀ ⟨a N i, ha_mem N i⟩ * lagBasisVal (a N) i x)
        have hpos : 0 ≤ r * lebesgueFn (a N) x :=
          mul_nonneg hr.le (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        rw [abs_of_nonneg hpos] at htri
        rw [add_comm]
        linarith
  have hdense : Dense (⋂ k : ℕ, V k) := dense_iInter_of_isOpen hV_open hV_dense
  rcases hdense.nonempty with ⟨fC, hfC⟩
  refine ⟨fun t => fC (clampIcc t), fC.continuous.comp continuous_clampIcc, ?_⟩
  intro B
  rcases exists_nat_gt B with ⟨k, hk⟩
  rcases Set.mem_iInter.mp hfC k with ⟨n, x, hx, hlt⟩
  refine ⟨n, x, hx, lt_trans hk ?_⟩
  have hEq :
      (∑ i : Fin (n + 1), fC (clampIcc (a n i)) * lagBasisVal (a n) i x) =
        ∑ i : Fin (n + 1), fC ⟨a n i, ha_mem n i⟩ * lagBasisVal (a n) i x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [clampIcc_of_mem (ha_mem n i)]
  change (k : ℝ) < |∑ i : Fin (n + 1), fC (clampIcc (a n i)) * lagBasisVal (a n) i x|
  rwa [hEq]

end FaberLowerBound

/-! ## Section 5: Chebyshev Nodes — Sharp `(2/π) log n` Upper/Lower Bounds & Everywhere Divergence -/

section ChebyshevNodes

private noncomputable def chebTheta (n : ℕ) (k : Fin n) : ℝ :=
  (2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ))

private noncomputable def chebNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos (chebTheta n k)

private lemma chebTheta_mem_Ioo {n : ℕ} (k : Fin n) :
    chebTheta n k ∈ Set.Ioo 0 Real.pi := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by have := k.isLt; omega))
  have hk_lt : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast k.isLt
  constructor
  · unfold chebTheta; positivity
  · unfold chebTheta
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    nlinarith [Real.pi_pos]

private lemma chebNode_mem_Icc {n : ℕ} (k : Fin n) :
    chebNode n k ∈ Set.Icc (-1 : ℝ) 1 :=
  ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

private lemma chebTheta_strictMono (n : ℕ) : StrictMono (chebTheta n) := by
  intro j k hjk
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by have := k.isLt; omega))
  unfold chebTheta
  apply div_lt_div_of_pos_right _ (by positivity)
  have hjk' : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
  nlinarith [Real.pi_pos]

private lemma chebNode_injective (n : ℕ) : Function.Injective (chebNode n) := by
  intro j k hjk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := chebTheta_mem_Ioo j
    have h2 := chebTheta_mem_Ioo k
    have hlt_th := chebTheta_strictMono n hlt
    have hanti := Real.strictAntiOn_cos ⟨h1.1.le, h1.2.le⟩ ⟨h2.1.le, h2.2.le⟩ hlt_th
    exact hanti.ne hjk.symm
  · have h1 := chebTheta_mem_Ioo k
    have h2 := chebTheta_mem_Ioo j
    have hlt_th := chebTheta_strictMono n hgt
    have hanti := Real.strictAntiOn_cos ⟨h1.1.le, h1.2.le⟩ ⟨h2.1.le, h2.2.le⟩ hlt_th
    exact hanti.ne hjk

private lemma chebTheta_rev {n : ℕ} (k : Fin n) :
    chebTheta n k.rev = Real.pi - chebTheta n k := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by have := k.isLt; omega))
  unfold chebTheta
  have hrev : ((k.rev : ℕ) : ℝ) = (n : ℝ) - 1 - (k : ℝ) := by
    have hnat : (k.rev : ℕ) + 1 + (k : ℕ) = n := by simp [Fin.val_rev]; omega
    have hcast : ((k.rev : ℕ) : ℝ) + 1 + (k : ℝ) = (n : ℝ) := by exact_mod_cast hnat
    linarith
  rw [hrev]
  field_simp [hn_pos.ne']
  ring

private lemma chebNode_rev {n : ℕ} (k : Fin n) :
    chebNode n k.rev = -chebNode n k := by
  unfold chebNode
  rw [chebTheta_rev, Real.cos_pi_sub]

private lemma lebesgueFn_chebNode_neg {n : ℕ} (x : ℝ) :
    lebesgueFn (chebNode n) (-x) = lebesgueFn (chebNode n) x := by
  unfold lebesgueFn
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  unfold lagBasisVal
  refine Finset.prod_bij (fun j _ => j.rev) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨fun h => hj.1 (by simpa using congrArg Fin.rev h), Finset.mem_univ _⟩
  · intro j₁ _ j₂ _ h
    simpa using congrArg Fin.rev h
  · intro j hj
    refine ⟨j.rev, ?_, Fin.rev_rev j⟩
    rw [Finset.mem_erase] at hj ⊢
    exact ⟨fun h => hj.1 (by simpa using congrArg Fin.rev h), Finset.mem_univ _⟩
  · intro j _
    change (-x - chebNode n j) / (chebNode n k.rev - chebNode n j) =
      (x - chebNode n j.rev) / (chebNode n k - chebNode n j.rev)
    rw [chebNode_rev k, chebNode_rev j]
    have hnum : -x - chebNode n j = -(x - -chebNode n j) := by ring
    have hden : -chebNode n k - chebNode n j = -(chebNode n k - -chebNode n j) := by ring
    rw [hnum, hden, neg_div_neg_eq]

private noncomputable def dirichletK (n : ℕ) (α : ℝ) : ℝ :=
  1 + 2 * ∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * α)

private lemma dirichletK_zero {n : ℕ} (hn : 1 ≤ n) :
    dirichletK n 0 = 2 * (n : ℝ) - 1 := by
  unfold dirichletK
  simp only [mul_zero, Real.cos_zero, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  have hcast : ((n - 1 + 1 - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : n - 1 + 1 - 1 = n - 1 := by omega
    rw [this, Nat.cast_sub hn, Nat.cast_one]
  rw [hcast]
  ring

private lemma dirichletK_abs_le {n : ℕ} (hn : 1 ≤ n) (α : ℝ) :
    |dirichletK n α| ≤ 2 * (n : ℝ) := by
  unfold dirichletK
  have hsum : |∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * α)| ≤ (n : ℝ) - 1 := by
    calc
      |∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * α)|
          ≤ ∑ r ∈ Finset.Icc 1 (n - 1), |Real.cos ((r : ℝ) * α)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.Icc 1 (n - 1), (1 : ℝ) :=
            Finset.sum_le_sum fun r _ => Real.abs_cos_le_one _
      _ = (n : ℝ) - 1 := by
            simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
            have : n - 1 + 1 - 1 = n - 1 := by omega
            rw [this, Nat.cast_sub hn, Nat.cast_one]
  calc
    |1 + 2 * ∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * α)|
        ≤ |1| + |2 * ∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * α)| := abs_add_le _ _
    _ = 1 + 2 * |∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * α)| := by
          rw [abs_one, abs_mul, abs_of_pos two_pos]
    _ ≤ 1 + 2 * ((n : ℝ) - 1) := by linarith
    _ ≤ 2 * (n : ℝ) := by linarith

private lemma dirichletK_closed_form {n : ℕ} (hn : 1 ≤ n) (α : ℝ) (hsin : Real.sin (α / 2) ≠ 0) :
    dirichletK n α =
      Real.sin ((n : ℝ) * α) * (Real.cos (α / 2) / Real.sin (α / 2)) - Real.cos ((n : ℝ) * α) := by
  have hmul : Real.sin (α / 2) * dirichletK n α = Real.sin (((n : ℝ) - 1 / 2) * α) := by
    unfold dirichletK
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (Real.sin (α / 2)) 2, mul_assoc, Finset.mul_sum]
    have hterm : ∀ r : ℕ,
        2 * Real.sin (α / 2) * Real.cos ((r : ℝ) * α) =
          Real.sin (((r : ℝ) + 1 / 2) * α) - Real.sin (((r : ℝ) - 1 / 2) * α) := by
      intro r
      have h1 : ((r : ℝ) + 1 / 2) * α = (r : ℝ) * α + α / 2 := by ring
      have h2 : ((r : ℝ) - 1 / 2) * α = (r : ℝ) * α - α / 2 := by ring
      rw [h1, h2, Real.sin_add, Real.sin_sub]
      ring
    have hcongr :
        2 * ∑ r ∈ Finset.Icc 1 (n - 1), Real.sin (α / 2) * Real.cos ((r : ℝ) * α) =
          ∑ r ∈ Finset.Icc 1 (n - 1),
            (Real.sin (((r : ℝ) + 1 / 2) * α) - Real.sin (((r : ℝ) - 1 / 2) * α)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by rw [← mul_assoc, hterm r]
    rw [hcongr]
    have htele :
        ∑ r ∈ Finset.Icc 1 (n - 1),
            (Real.sin (((r : ℝ) + 1 / 2) * α) - Real.sin (((r : ℝ) - 1 / 2) * α)) =
          Real.sin (((n : ℝ) - 1 / 2) * α) - Real.sin (α / 2) := by
      have hIco : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
        ext r; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIco, Finset.sum_Ico_eq_sum_range]
      have hshift :
          ∑ k ∈ Finset.range (n - 1),
              (Real.sin ((((1 + k : ℕ) : ℝ) + 1 / 2) * α) -
                Real.sin ((((1 + k : ℕ) : ℝ) - 1 / 2) * α)) =
            ∑ k ∈ Finset.range (n - 1),
              (Real.sin ((((k + 1 : ℕ) : ℝ) + 1 / 2) * α) -
                Real.sin (((k : ℝ) + 1 / 2) * α)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have h1 : (((1 + k : ℕ) : ℝ) + 1 / 2) = ((k + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
        have h2 : (((1 + k : ℕ) : ℝ) - 1 / 2) = (k : ℝ) + 1 / 2 := by push_cast; ring
        rw [h1, h2]
      rw [hshift, Finset.sum_range_sub (fun k => Real.sin (((k : ℝ) + 1 / 2) * α)) (n - 1)]
      have htop : (((n - 1 : ℕ) : ℝ) + 1 / 2) * α = ((n : ℝ) - 1 / 2) * α := by
        rw [Nat.cast_sub hn, Nat.cast_one]; ring
      have hbot : (((0 : ℕ) : ℝ) + 1 / 2) * α = α / 2 := by simp; ring
      rw [htop, hbot]
    rw [htele]
    ring
  have hexpand : Real.sin (((n : ℝ) - 1 / 2) * α) =
      Real.sin ((n : ℝ) * α) * Real.cos (α / 2) - Real.cos ((n : ℝ) * α) * Real.sin (α / 2) := by
    have harg : ((n : ℝ) - 1 / 2) * α = (n : ℝ) * α - α / 2 := by ring
    rw [harg, Real.sin_sub]
  rw [hexpand] at hmul
  have hdiv : dirichletK n α =
      (Real.sin ((n : ℝ) * α) * Real.cos (α / 2) - Real.cos ((n : ℝ) * α) * Real.sin (α / 2)) /
        Real.sin (α / 2) := by
    rw [eq_div_iff hsin, mul_comm]; exact hmul
  rw [hdiv]
  field_simp [hsin]

private lemma cheb_lagBasis_eq_dirichlet {n : ℕ} (hn : 1 ≤ n) (k : Fin n) (θ : ℝ) :
    lagBasisVal (chebNode n) k (Real.cos θ) =
      (dirichletK n (θ - chebTheta n k) + dirichletK n (θ + chebTheta n k)) / (2 * (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let P : Polynomial ℝ :=
    Polynomial.C (1 / (n : ℝ)) *
      (1 + Polynomial.C 2 *
        ∑ r ∈ Finset.Icc 1 (n - 1),
          Polynomial.C (Real.cos ((r : ℝ) * chebTheta n k)) * chebT r)
  have hP_eval : ∀ φ : ℝ, P.eval (Real.cos φ) =
      (dirichletK n (φ - chebTheta n k) + dirichletK n (φ + chebTheta n k)) / (2 * (n : ℝ)) := by
    intro φ
    simp only [P, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_C,
      Polynomial.eval_finsetSum, chebT_eval_cos]
    unfold dirichletK
    have hsum :
        2 * ∑ r ∈ Finset.Icc 1 (n - 1),
              Real.cos ((r : ℝ) * chebTheta n k) * Real.cos ((r : ℝ) * φ) =
          (∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ - chebTheta n k))) +
            (∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ + chebTheta n k))) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      have h1 : (r : ℝ) * (φ - chebTheta n k) = (r : ℝ) * φ - (r : ℝ) * chebTheta n k := by ring
      have h2 : (r : ℝ) * (φ + chebTheta n k) = (r : ℝ) * φ + (r : ℝ) * chebTheta n k := by ring
      rw [h1, h2, Real.cos_sub, Real.cos_add]
      ring
    calc
      1 / (n : ℝ) * (1 + 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
          Real.cos ((r : ℝ) * chebTheta n k) * Real.cos ((r : ℝ) * φ))
          = 1 / (n : ℝ) * (1 + ((∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ - chebTheta n k))) +
              (∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ + chebTheta n k))))) := by
            rw [hsum]
      _ = ((1 + 2 * ∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ - chebTheta n k))) +
           (1 + 2 * ∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ + chebTheta n k)))) /
            (2 * (n : ℝ)) := by
            generalize (∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ - chebTheta n k))) = S1
            generalize (∑ r ∈ Finset.Icc 1 (n - 1), Real.cos ((r : ℝ) * (φ + chebTheta n k))) = S2
            field_simp [hn_pos.ne']
            ring
  have hP_deg : P.natDegree < n := by
    have hsum_le :
        (∑ r ∈ Finset.Icc 1 (n - 1),
          Polynomial.C (Real.cos ((r : ℝ) * chebTheta n k)) * chebT r).natDegree ≤ n - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
      calc
        (Polynomial.C (Real.cos ((r : ℝ) * chebTheta n k)) * chebT r).natDegree
            ≤ (chebT r).natDegree := Polynomial.natDegree_C_mul_le _ _
        _ = r := (chebT_natDegree_and_coeff r).1
        _ ≤ n - 1 := (Finset.mem_Icc.mp hr).2
    have hinner :
        (1 + Polynomial.C 2 * ∑ r ∈ Finset.Icc 1 (n - 1),
          Polynomial.C (Real.cos ((r : ℝ) * chebTheta n k)) * chebT r).natDegree ≤ n - 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans hsum_le
    have hP_le : P.natDegree ≤ n - 1 := (Polynomial.natDegree_C_mul_le _ _).trans hinner
    omega
  -- Evaluate P at all Chebyshev nodes chebNode n j
  have hP_at_node : ∀ j : Fin n, P.eval (chebNode n j) = if j = k then 1 else 0 := by
    intro j
    unfold chebNode
    rw [hP_eval]
    have hsum_pos : 0 < (chebTheta n j + chebTheta n k) / 2 := by
      have := (chebTheta_mem_Ioo j).1; have := (chebTheta_mem_Ioo k).1; linarith
    have hsum_lt : (chebTheta n j + chebTheta n k) / 2 < Real.pi := by
      have := (chebTheta_mem_Ioo j).2; have := (chebTheta_mem_Ioo k).2; linarith
    have hsin_add : Real.sin ((chebTheta n j + chebTheta n k) / 2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hsum_pos hsum_lt).ne'
    have hn_add : (n : ℝ) * (chebTheta n j + chebTheta n k) =
        (((j.1 + k.1 + 1 : ℕ) : ℝ)) * Real.pi := by
      unfold chebTheta; field_simp [hn_pos.ne']; push_cast; ring
    have hD_add : dirichletK n (chebTheta n j + chebTheta n k) = (-1 : ℝ) ^ (j.1 + k.1) := by
      rw [dirichletK_closed_form hn _ hsin_add, hn_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
      simp [pow_succ]
    by_cases hjk : j = k
    · subst hjk
      simp only [↓reduceIte, sub_self, dirichletK_zero hn, hD_add]
      have heven : (-1 : ℝ) ^ (j.1 + j.1) = 1 := by
        rw [show j.1 + j.1 = 2 * j.1 by omega, pow_mul]
        norm_num
      rw [heven]
      field_simp [hn_pos.ne']
      ring
    · simp only [hjk, ↓reduceIte]
      have hdiff_ne : (chebTheta n j - chebTheta n k) / 2 ≠ 0 := by
        intro h0
        have hEq : chebTheta n j = chebTheta n k := by linarith
        exact hjk ((chebTheta_strictMono n).injective hEq)
      have hdiff_abs_lt : |(chebTheta n j - chebTheta n k) / 2| < Real.pi := by
        have h1 := chebTheta_mem_Ioo j
        have h2 := chebTheta_mem_Ioo k
        rw [abs_lt]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have hsin_sub : Real.sin ((chebTheta n j - chebTheta n k) / 2) ≠ 0 := by
        rcases lt_or_gt_of_ne hdiff_ne with hneg | hpos
        · have hpos' : 0 < -((chebTheta n j - chebTheta n k) / 2) := by linarith
          have hlt' : -((chebTheta n j - chebTheta n k) / 2) < Real.pi := by
            rw [abs_lt] at hdiff_abs_lt; linarith
          have := (Real.sin_pos_of_pos_of_lt_pi hpos' hlt').ne'
          rw [Real.sin_neg] at this
          exact neg_ne_zero.mp this
        · have hlt' : (chebTheta n j - chebTheta n k) / 2 < Real.pi := by
            rw [abs_lt] at hdiff_abs_lt; linarith
          exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt').ne'
      have hn_sub : (n : ℝ) * (chebTheta n j - chebTheta n k) =
          (((j.1 : ℤ) - (k.1 : ℤ) : ℤ) : ℝ) * Real.pi := by
        unfold chebTheta; field_simp [hn_pos.ne']; push_cast; ring
      have hD_sub : dirichletK n (chebTheta n j - chebTheta n k) = -((-1 : ℝ) ^ (j.1 + k.1)) := by
        rw [dirichletK_closed_form hn _ hsin_sub, hn_sub, Real.sin_int_mul_pi, Real.cos_int_mul_pi]
        simp only [zero_mul, zero_sub]
        congr 1
        have hz : (-1 : ℝ) ^ ((j.1 : ℤ) - (k.1 : ℤ)) = (-1 : ℝ) ^ (j.1 + k.1) := by
          have h1 : (-1 : ℝ) ^ ((j.1 : ℤ) - (k.1 : ℤ)) * (-1 : ℝ) ^ (2 * (k.1 : ℤ)) =
              (-1 : ℝ) ^ ((j.1 : ℤ) + (k.1 : ℤ)) := by
            rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
            congr 1; ring
          have h2 : (-1 : ℝ) ^ (2 * (k.1 : ℤ)) = 1 := by
            rw [zpow_mul]; norm_num
          rw [h2, mul_one] at h1
          rw [h1]
          exact_mod_cast (zpow_natCast (-1 : ℝ) (j.1 + k.1))
        exact hz
      rw [hD_sub, hD_add, neg_add_cancel, zero_div]
  have hrep := lagInterp_reproduces_poly hn (chebNode_injective n) P hP_deg (Real.cos θ)
  rw [← hP_eval θ, ← hrep]
  unfold lagInterpVal
  rw [Finset.sum_eq_single k]
  · simp [hP_at_node k]
  · intro j _ hjk
    simp [hP_at_node j, hjk]
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma cheb_lagBasis_cot_formula {n : ℕ} (hn : 1 ≤ n) (k : Fin n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) (hne : θ ≠ chebTheta n k) :
    lagBasisVal (chebNode n) k (Real.cos θ) =
      ((-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ)) / (2 * (n : ℝ)) *
        (Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
          Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk_mem := chebTheta_mem_Ioo k
  have hsin_add : Real.sin ((θ + chebTheta n k) / 2) ≠ 0 := by
    have h0 : 0 < (θ + chebTheta n k) / 2 := by linarith [hθ.1, hk_mem.1]
    have h1 : (θ + chebTheta n k) / 2 < Real.pi := by linarith [hθ.2, hk_mem.2]
    exact (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
  have hsin_sub : Real.sin ((θ - chebTheta n k) / 2) ≠ 0 := by
    have habs : |(θ - chebTheta n k) / 2| < Real.pi := by
      rw [abs_lt]; constructor <;> linarith [hθ.1, hθ.2, hk_mem.1, hk_mem.2]
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hneg | hpos
    · have h0 : 0 < -((θ - chebTheta n k) / 2) := by linarith
      have h1 : -((θ - chebTheta n k) / 2) < Real.pi := by rw [abs_lt] at habs; linarith
      have := (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
      rw [Real.sin_neg] at this
      exact neg_ne_zero.mp this
    · have h0 : 0 < (θ - chebTheta n k) / 2 := by linarith
      have h1 : (θ - chebTheta n k) / 2 < Real.pi := by rw [abs_lt] at habs; linarith
      exact (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
  rw [cheb_lagBasis_eq_dirichlet hn k θ,
    dirichletK_closed_form hn _ hsin_sub, dirichletK_closed_form hn _ hsin_add]
  have hn_thk : (n : ℝ) * chebTheta n k = (k : ℝ) * Real.pi + Real.pi / 2 := by
    unfold chebTheta; field_simp [hn_pos.ne']
  have hsin_n_add : Real.sin ((n : ℝ) * (θ + chebTheta n k)) =
      (-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ) := by
    have harg : (n : ℝ) * (θ + chebTheta n k) = ((n : ℝ) * θ + (k : ℝ) * Real.pi) + Real.pi / 2 := by
      linarith [hn_thk]
    rw [harg, Real.sin_add_pi_div_two, Real.cos_add_nat_mul_pi]
  have hcos_n_add : Real.cos ((n : ℝ) * (θ + chebTheta n k)) =
      -((-1 : ℝ) ^ (k : ℕ) * Real.sin ((n : ℝ) * θ)) := by
    have harg : (n : ℝ) * (θ + chebTheta n k) = ((n : ℝ) * θ + (k : ℝ) * Real.pi) + Real.pi / 2 := by
      linarith [hn_thk]
    rw [harg, Real.cos_add_pi_div_two, Real.sin_add_nat_mul_pi]
  have hsin_n_sub : Real.sin ((n : ℝ) * (θ - chebTheta n k)) =
      -((-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ)) := by
    have harg : (n : ℝ) * (θ - chebTheta n k) = ((n : ℝ) * θ - (k : ℝ) * Real.pi) - Real.pi / 2 := by
      linarith [hn_thk]
    rw [harg, Real.sin_sub_pi_div_two, Real.cos_sub_nat_mul_pi]
  have hcos_n_sub : Real.cos ((n : ℝ) * (θ - chebTheta n k)) =
      (-1 : ℝ) ^ (k : ℕ) * Real.sin ((n : ℝ) * θ) := by
    have harg : (n : ℝ) * (θ - chebTheta n k) = ((n : ℝ) * θ - (k : ℝ) * Real.pi) - Real.pi / 2 := by
      linarith [hn_thk]
    rw [harg, Real.cos_sub_pi_div_two, Real.sin_sub_nat_mul_pi]
  rw [hsin_n_add, hcos_n_add, hsin_n_sub, hcos_n_sub]
  ring

private lemma cheb_lagBasis_sin_cos_formula {n : ℕ} (hn : 1 ≤ n) (k : Fin n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 Real.pi) (hne : θ ≠ chebTheta n k) :
    lagBasisVal (chebNode n) k (Real.cos θ) =
      ((-1 : ℝ) ^ (k : ℕ) * Real.sin (chebTheta n k) * Real.cos ((n : ℝ) * θ)) /
        ((n : ℝ) * (Real.cos θ - Real.cos (chebTheta n k))) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk_mem := chebTheta_mem_Ioo k
  have hsin_add : Real.sin ((θ + chebTheta n k) / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, hk_mem.1])
      (by linarith [hθ.2, hk_mem.2])).ne'
  have hsin_sub : Real.sin ((θ - chebTheta n k) / 2) ≠ 0 := by
    have habs : |(θ - chebTheta n k) / 2| < Real.pi := by
      rw [abs_lt]; constructor <;> linarith [hθ.1, hθ.2, hk_mem.1, hk_mem.2]
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hneg | hpos
    · have h0 : 0 < -((θ - chebTheta n k) / 2) := by linarith
      have h1 : -((θ - chebTheta n k) / 2) < Real.pi := by rw [abs_lt] at habs; linarith
      have := (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
      rw [Real.sin_neg] at this; exact neg_ne_zero.mp this
    · have h0 : 0 < (θ - chebTheta n k) / 2 := by linarith
      have h1 : (θ - chebTheta n k) / 2 < Real.pi := by rw [abs_lt] at habs; linarith
      exact (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'
  have hcos_ne : Real.cos θ - Real.cos (chebTheta n k) ≠ 0 := by
    intro h0
    have hEq : Real.cos θ = Real.cos (chebTheta n k) := sub_eq_zero.mp h0
    exact hne (Real.injOn_cos hθ ⟨hk_mem.1.le, hk_mem.2.le⟩ hEq)
  rw [cheb_lagBasis_cot_formula hn k hθ hne]
  have hcot_diff :
      Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
        Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2) =
      2 * Real.sin (chebTheta n k) / (Real.cos θ - Real.cos (chebTheta n k)) := by
    have hnum :
        Real.cos ((θ + chebTheta n k) / 2) * Real.sin ((θ - chebTheta n k) / 2) -
          Real.cos ((θ - chebTheta n k) / 2) * Real.sin ((θ + chebTheta n k) / 2) =
        -Real.sin (chebTheta n k) := by
      have harg : (θ - chebTheta n k) / 2 - (θ + chebTheta n k) / 2 = -chebTheta n k := by ring
      have hsub := Real.sin_sub ((θ - chebTheta n k) / 2) ((θ + chebTheta n k) / 2)
      rw [harg, Real.sin_neg] at hsub
      linarith
    have hden :
        2 * Real.sin ((θ + chebTheta n k) / 2) * Real.sin ((θ - chebTheta n k) / 2) =
          -(Real.cos θ - Real.cos (chebTheta n k)) := by
      have h1 : (θ + chebTheta n k) / 2 - (θ - chebTheta n k) / 2 = chebTheta n k := by ring
      have h2 : (θ + chebTheta n k) / 2 + (θ - chebTheta n k) / 2 = θ := by ring
      have hc1 := Real.cos_sub ((θ + chebTheta n k) / 2) ((θ - chebTheta n k) / 2)
      have hc2 := Real.cos_add ((θ + chebTheta n k) / 2) ((θ - chebTheta n k) / 2)
      rw [h1] at hc1; rw [h2] at hc2
      linarith
    field_simp [hsin_add, hsin_sub, hcos_ne]
    have hprod :
        (Real.cos ((θ + chebTheta n k) / 2) * Real.sin ((θ - chebTheta n k) / 2) -
          Real.cos ((θ - chebTheta n k) / 2) * Real.sin ((θ + chebTheta n k) / 2)) *
        (Real.cos θ - Real.cos (chebTheta n k)) =
        (-Real.sin (chebTheta n k)) *
          (-(2 * Real.sin ((θ + chebTheta n k) / 2) * Real.sin ((θ - chebTheta n k) / 2))) := by
      rw [hnum, hden]; ring
    linarith [hprod]
  rw [hcot_diff]
  field_simp [hn_pos.ne', hcos_ne]

private lemma mul_cos_le_sin {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ Real.pi / 2) :
    u * Real.cos u ≤ Real.sin u := by
  let f : ℝ → ℝ := fun t => Real.sin t - t * Real.cos t
  have hderiv : ∀ t ∈ Set.Icc 0 (Real.pi / 2), HasDerivAt f (t * Real.sin t) t := by
    intro t _
    have h1 := Real.hasDerivAt_sin t
    have h2 := (hasDerivAt_id t).mul (Real.hasDerivAt_cos t)
    have hsub := h1.sub h2
    have hval : Real.cos t - (1 * Real.cos t + t * -Real.sin t) = t * Real.sin t := by ring
    have hfn : (Real.sin - id * Real.cos) = f := rfl
    rw [hfn, id_eq, hval] at hsub
    exact hsub
  have hmono : MonotoneOn f (Set.Icc 0 (Real.pi / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (Real.pi / 2)) ?_ ?_ ?_
    · exact (Real.continuous_sin.sub (continuous_id.mul Real.continuous_cos)).continuousOn
    · intro t ht
      exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_mem : t ∈ Set.Icc 0 (Real.pi / 2) := interior_subset ht
      rw [(hderiv t ht_mem).deriv]
      exact mul_nonneg ht_mem.1 (Real.sin_nonneg_of_nonneg_of_le_pi ht_mem.1 (by linarith [ht_mem.2]))
  have h0 : f 0 ≤ f u := hmono ⟨le_rfl, by positivity⟩ ⟨hu0, hu1⟩ hu0
  dsimp [f] at h0
  simp only [Real.sin_zero, zero_mul, sub_self] at h0
  linarith

private lemma cos_div_sin_le_inv {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ Real.pi / 2) :
    Real.cos u / Real.sin u ≤ 1 / u := by
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  rw [div_le_div_iff₀ hsin_pos hu0, one_mul, mul_comm]
  exact mul_cos_le_sin hu0.le hu1

private lemma abs_cos_div_sin_le {u : ℝ} (hu0 : 0 < u) (hu1 : u < Real.pi) :
    |Real.cos u / Real.sin u| ≤ 1 / u + 1 / (Real.pi - u) := by
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hu1
  by_cases hle : u ≤ Real.pi / 2
  · have hcos_nn : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hle⟩
    rw [abs_of_nonneg (div_nonneg hcos_nn hsin_pos.le)]
    have h1 := cos_div_sin_le_inv hu0 hle
    have h2 : 0 ≤ 1 / (Real.pi - u) := div_nonneg zero_le_one (by linarith)
    linarith
  · push Not at hle
    let v : ℝ := Real.pi - u
    have hv0 : 0 < v := by dsimp [v]; linarith
    have hv1 : v ≤ Real.pi / 2 := by dsimp [v]; linarith
    have hEq : |Real.cos u / Real.sin u| = Real.cos v / Real.sin v := by
      have hu_eq : u = Real.pi - v := by dsimp [v]; ring
      rw [hu_eq, Real.cos_pi_sub, Real.sin_pi_sub, neg_div, abs_neg]
      exact abs_of_nonneg (div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hv1⟩)
        (Real.sin_pos_of_pos_of_lt_pi hv0 (by linarith [Real.pi_pos])).le)
    rw [hEq]
    have h1 := cos_div_sin_le_inv hv0 hv1
    have h2 : 0 ≤ 1 / u := div_nonneg zero_le_one hu0.le
    dsimp [v] at h1
    linarith

private lemma inv_sub_two_div_pi_le_cos_div_sin {u : ℝ} (hu0 : 0 < u) (hu1 : u < Real.pi / 2) :
    1 / u - 2 / Real.pi ≤ Real.cos u / Real.sin u := by
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
  have hsin_le : Real.sin u ≤ u := Real.sin_le hu0.le
  have hcos_ge : 1 - 2 / Real.pi * u ≤ Real.cos u := by
    have h := Real.mul_le_sin (show 0 ≤ Real.pi / 2 - u by linarith) (by linarith)
    rw [Real.sin_pi_div_two_sub] at h
    have hEq : 2 / Real.pi * (Real.pi / 2 - u) = 1 - 2 / Real.pi * u := by
      field_simp [Real.pi_pos.ne']
    linarith
  have hcos_nn : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hu1.le⟩
  calc
    1 / u - 2 / Real.pi = (1 - 2 / Real.pi * u) / u := by field_simp [hu0.ne']
    _ ≤ Real.cos u / u := div_le_div_of_nonneg_right hcos_ge hu0.le
    _ ≤ Real.cos u / Real.sin u := div_le_div_of_nonneg_left hcos_nn hsin_pos hsin_le

private lemma two_div_odd_le_log_ratio {m : ℕ} (hm : 1 ≤ m) :
    2 / (2 * (m : ℝ) + 1) ≤ Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - Real.log (1 - t) - 2 * t
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
      HasDerivAt f (1 / (1 + t) + 1 / (1 - t) - 2) t := by
    intro t ht
    have h1p : (1 + t) ≠ 0 := by linarith [ht.1]
    have h1m : (1 - t) ≠ 0 := by linarith [ht.2]
    have d1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + t)) t := by
      have := ((hasDerivAt_id t).const_add 1).log h1p
      simpa [one_div] using this
    have d2 : HasDerivAt (fun x => Real.log (1 - x)) (-(1 / (1 - t))) t := by
      have h := ((hasDerivAt_id t).const_sub 1).log h1m
      have hfn : (fun y : ℝ => Real.log (1 - id y)) = (fun x : ℝ => Real.log (1 - x)) := rfl
      rw [hfn, id_eq, neg_div] at h
      exact h
    have d3 : HasDerivAt (fun x => 2 * x) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hcomb := (d1.sub d2).sub d3
    have hval : 1 / (1 + t) - -(1 / (1 - t)) - 2 = 1 / (1 + t) + 1 / (1 - t) - 2 := by ring
    rwa [hval] at hcomb
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
    · refine ((ContinuousOn.log (continuousOn_const.add continuousOn_id)
          (fun t ht => by simp only [Pi.add_apply, id_eq]; linarith [ht.1])).sub
        (ContinuousOn.log (continuousOn_const.sub continuousOn_id)
          (fun t ht => by simp only [Pi.sub_apply, id_eq]; linarith [ht.2]))).sub
        (continuousOn_const.mul continuousOn_id)
    · intro t ht
      exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht_mem := interior_subset ht
      rw [(hderiv t ht_mem).deriv]
      have h1p : 0 < 1 + t := by linarith [ht_mem.1]
      have h1m : 0 < 1 - t := by linarith [ht_mem.2]
      have hEq : 1 / (1 + t) + 1 / (1 - t) - 2 = 2 * t ^ 2 / ((1 + t) * (1 - t)) := by
        field_simp [h1p.ne', h1m.ne']; ring
      rw [hEq]
      positivity
  let u : ℝ := 1 / (2 * (m : ℝ) + 1)
  have hm_r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hu_mem : u ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    dsimp [u]
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have h0 : f 0 ≤ f u := hmono ⟨le_rfl, by norm_num⟩ hu_mem hu_mem.1
  dsimp [f] at h0
  simp only [add_zero, sub_zero, Real.log_one, mul_zero, sub_self] at h0
  have hratio : (1 + u) / (1 - u) = ((m : ℝ) + 1) / (m : ℝ) := by
    dsimp [u]; field_simp [show (2 * (m : ℝ) + 1) ≠ 0 by linarith, show (m : ℝ) ≠ 0 by linarith]; ring
  have h1p : 0 < 1 + u := by linarith [hu_mem.1]
  have h1m : 0 < 1 - u := by linarith [hu_mem.2]
  rw [← hratio, Real.log_div h1p.ne' h1m.ne']
  have h2u : 2 / (2 * (m : ℝ) + 1) = 2 * u := by dsimp [u]; ring
  linarith

private lemma sum_odd_inv_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ m ∈ Finset.range M, (1 : ℝ) / (2 * (m : ℝ) + 1) ≤ 1 + (1 / 2 : ℝ) * Real.log (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_range_succ]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hstep := two_div_odd_le_log_ratio hk
    have hlog : Real.log (((k : ℝ) + 1) / (k : ℝ)) =
        Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      push_cast; exact Real.log_div (by positivity) hk_pos.ne'
    rw [hlog] at hstep
    have hhalf : 1 / (2 * (k : ℝ) + 1) ≤
        (1 / 2 : ℝ) * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
      have h2 : 2 / (2 * (k : ℝ) + 1) = 2 * (1 / (2 * (k : ℝ) + 1)) := by ring
      linarith
    linarith

private lemma sum_le_sum_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (g : α → β) (f : β → ℝ)
    (hmaps : ∀ a ∈ s, g a ∈ t)
    (hinj : Set.InjOn g s)
    (hf : ∀ b ∈ t, 0 ≤ f b) :
    ∑ a ∈ s, f (g a) ≤ ∑ b ∈ t, f b := by
  rw [← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.image_subset_iff.mpr hmaps) (fun b hb _ => hf b hb)

private lemma cheb_odd_sum_pair_bound {n : ℕ} (k0 : Fin n) (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m) :
    ∑ k ∈ Finset.univ.erase k0,
        ((if k.1 < k0.1 then f (k0.1 - k.1 - 1) else f (k.1 - k0.1 - 1)) +
          f (k.1 + k0.1) + f ((n - 1 - k.1) + (n - 1 - k0.1))) ≤
      2 * ∑ m ∈ Finset.range (2 * n), f m := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsplit_if :
      ∑ k ∈ Finset.univ.erase k0,
          (if k.1 < k0.1 then f (k0.1 - k.1 - 1) else f (k.1 - k0.1 - 1)) =
        (∑ k ∈ (Finset.univ.erase k0).filter (fun k : Fin n => k.1 < k0.1),
          f (k0.1 - k.1 - 1)) +
        (∑ k ∈ (Finset.univ.erase k0).filter (fun k : Fin n => ¬ k.1 < k0.1),
          f (k.1 - k0.1 - 1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase k0) (fun k : Fin n => k.1 < k0.1)]
    congr 1
    · exact Finset.sum_congr rfl fun k hk => if_pos (Finset.mem_filter.mp hk).2
    · exact Finset.sum_congr rfl fun k hk => if_neg (Finset.mem_filter.mp hk).2
  have hpair1 :
      (∑ k ∈ (Finset.univ.erase k0).filter (fun k : Fin n => k.1 < k0.1),
          f (k0.1 - k.1 - 1)) +
        (∑ k ∈ Finset.univ.erase k0, f (k.1 + k0.1)) ≤
      ∑ m ∈ Finset.range (2 * n), f m := by
    have hA : ∑ k ∈ (Finset.univ.erase k0).filter (fun k : Fin n => k.1 < k0.1),
          f (k0.1 - k.1 - 1) ≤ ∑ m ∈ Finset.range k0.1, f m := by
      refine sum_le_sum_of_injOn (fun k : Fin n => k0.1 - k.1 - 1) f ?_ ?_ (fun m _ => hf m)
      · intro k hk
        have hlt := (Finset.mem_filter.mp hk).2
        simp only [Finset.mem_range]; omega
      · intro k₁ hk₁ k₂ hk₂ hEq
        dsimp only at hEq
        have h1 := (Finset.mem_filter.mp hk₁).2
        have h2 := (Finset.mem_filter.mp hk₂).2
        ext; omega
    have hB : ∑ k ∈ Finset.univ.erase k0, f (k.1 + k0.1) ≤
        ∑ m ∈ Finset.Ico k0.1 (2 * n), f m := by
      refine sum_le_sum_of_injOn (fun k : Fin n => k.1 + k0.1) f ?_ ?_ (fun m _ => hf m)
      · intro k _
        simp only [Finset.mem_Ico]
        have := k.isLt; have := k0.isLt; omega
      · intro k₁ _ k₂ _ hEq
        dsimp only at hEq
        ext; omega
    have hdisj : ∑ m ∈ Finset.range k0.1, f m +
        ∑ m ∈ Finset.Ico k0.1 (2 * n), f m = ∑ m ∈ Finset.range (2 * n), f m := by
      rw [show Finset.range k0.1 = Finset.Ico 0 k0.1 by ext; simp,
        show Finset.range (2 * n) = Finset.Ico 0 (2 * n) by ext; simp,
        Finset.sum_Ico_consecutive f (Nat.zero_le _) (by have := k0.isLt; omega)]
    linarith
  have hpair2 :
      (∑ k ∈ (Finset.univ.erase k0).filter (fun k : Fin n => ¬ k.1 < k0.1),
          f (k.1 - k0.1 - 1)) +
        (∑ k ∈ Finset.univ.erase k0, f ((n - 1 - k.1) + (n - 1 - k0.1))) ≤
      ∑ m ∈ Finset.range (2 * n), f m := by
    have hA : ∑ k ∈ (Finset.univ.erase k0).filter (fun k : Fin n => ¬ k.1 < k0.1),
          f (k.1 - k0.1 - 1) ≤ ∑ m ∈ Finset.range (n - 1 - k0.1), f m := by
      refine sum_le_sum_of_injOn (fun k : Fin n => k.1 - k0.1 - 1) f ?_ ?_ (fun m _ => hf m)
      · intro k hk
        have hne : k ≠ k0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hk).1).1
        have hge : ¬ k.1 < k0.1 := (Finset.mem_filter.mp hk).2
        have hgt : k0.1 < k.1 := by have : k.1 ≠ k0.1 := fun h => hne (Fin.ext h); omega
        simp only [Finset.mem_range]
        have := k.isLt; omega
      · intro k₁ hk₁ k₂ hk₂ hEq
        dsimp only at hEq
        have hne1 : k₁ ≠ k0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hk₁).1).1
        have hge1 : ¬ k₁.1 < k0.1 := (Finset.mem_filter.mp hk₁).2
        have hne2 : k₂ ≠ k0 := (Finset.mem_erase.mp (Finset.mem_filter.mp hk₂).1).1
        have hge2 : ¬ k₂.1 < k0.1 := (Finset.mem_filter.mp hk₂).2
        have h1 : k0.1 < k₁.1 := by have : k₁.1 ≠ k0.1 := fun h => hne1 (Fin.ext h); omega
        have h2 : k0.1 < k₂.1 := by have : k₂.1 ≠ k0.1 := fun h => hne2 (Fin.ext h); omega
        ext; omega
    have hB : ∑ k ∈ Finset.univ.erase k0, f ((n - 1 - k.1) + (n - 1 - k0.1)) ≤
        ∑ m ∈ Finset.Ico (n - 1 - k0.1) (2 * n), f m := by
      refine sum_le_sum_of_injOn (fun k : Fin n => (n - 1 - k.1) + (n - 1 - k0.1)) f ?_ ?_
        (fun m _ => hf m)
      · intro k _
        simp only [Finset.mem_Ico]
        have := k.isLt; have := k0.isLt; omega
      · intro k₁ _ k₂ _ hEq
        dsimp only at hEq
        have := k₁.isLt; have := k₂.isLt; ext; omega
    have hdisj : ∑ m ∈ Finset.range (n - 1 - k0.1), f m +
        ∑ m ∈ Finset.Ico (n - 1 - k0.1) (2 * n), f m =
        ∑ m ∈ Finset.range (2 * n), f m := by
      rw [show Finset.range (n - 1 - k0.1) = Finset.Ico 0 (n - 1 - k0.1) by ext; simp,
        show Finset.range (2 * n) = Finset.Ico 0 (2 * n) by ext; simp,
        Finset.sum_Ico_consecutive f (Nat.zero_le _) (by omega)]
    linarith
  linarith

/-- **Chebyshev Nodes Sharp Uniform Lebesgue Upper Bound (`≤ (2/π) log n + 4`):**
For every `n ≥ 1` and every `x ∈ [-1, 1]`, the Lebesgue function of the first-kind Chebyshev
nodes `c_k = cos((2k + 1)π / (2n))` satisfies the asymptotically optimal bound
`Λ_n^Cheb(x) ≤ (2 / π) * log n + 4`. -/
theorem ppl128_chebyshev_lebesgue_upper_bound {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ k : Fin n, |∏ j ∈ Finset.univ.erase k,
      (x - Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) /
      (Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) -
        Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ))))| ≤
      (2 / Real.pi) * Real.log (n : ℝ) + 4 := by
  change lebesgueFn (chebNode n) x ≤ (2 / Real.pi) * Real.log (n : ℝ) + 4
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  let θ : ℝ := Real.arccos x
  have hθ_mem : θ ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
  have hx_eq : x = Real.cos θ := (Real.cos_arccos hx.1 hx.2).symm
  rw [hx_eq]
  let k0Nat : ℕ := min (n - 1) ⌊(n : ℝ) * θ / Real.pi⌋₊
  have hk0_lt : k0Nat < n := by dsimp [k0Nat]; omega
  let k0 : Fin n := ⟨k0Nat, hk0_lt⟩
  -- Key bin containment: k0 * π / n ≤ θ ≤ (k0 + 1) * π / n
  have hbin_lo : (k0.1 : ℝ) * Real.pi / (n : ℝ) ≤ θ := by
    have hle_fl : (k0.1 : ℝ) ≤ (⌊(n : ℝ) * θ / Real.pi⌋₊ : ℝ) := by
      exact_mod_cast (min_le_right (n - 1) ⌊(n : ℝ) * θ / Real.pi⌋₊)
    have hfl := Nat.floor_le (div_nonneg (mul_nonneg hn_pos.le hθ_mem.1) Real.pi_pos.le)
    have hcomb : (k0.1 : ℝ) ≤ (n : ℝ) * θ / Real.pi := hle_fl.trans hfl
    rw [div_le_iff₀ hn_pos]
    have := (le_div_iff₀ Real.pi_pos).mp hcomb
    linarith
  have hbin_hi : θ ≤ ((k0.1 : ℝ) + 1) * Real.pi / (n : ℝ) := by
    by_cases hcap : n - 1 ≤ ⌊(n : ℝ) * θ / Real.pi⌋₊
    · have hk0_eq : k0.1 = n - 1 := min_eq_left hcap
      rw [hk0_eq, Nat.cast_sub hn, Nat.cast_one]
      have hEq : ((n : ℝ) - 1 + 1) * Real.pi / (n : ℝ) = Real.pi := by
        field_simp [hn_pos.ne']; ring
      rw [hEq]; exact hθ_mem.2
    · push Not at hcap
      have hk0_eq : k0.1 = ⌊(n : ℝ) * θ / Real.pi⌋₊ := min_eq_right hcap.le
      rw [hk0_eq]
      have hgt := Nat.lt_floor_add_one ((n : ℝ) * θ / Real.pi)
      rw [le_div_iff₀ hn_pos]
      have := (div_lt_iff₀ Real.pi_pos).mp hgt
      linarith
  -- Split the sum into k = k0 and k ≠ k0
  unfold lebesgueFn
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k0)]
  have hk0_bound : |lagBasisVal (chebNode n) k0 (Real.cos θ)| ≤ 2 := by
    rw [cheb_lagBasis_eq_dirichlet hn k0 θ, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
    rw [div_le_iff₀ (by positivity)]
    calc
      |dirichletK n (θ - chebTheta n k0) + dirichletK n (θ + chebTheta n k0)|
          ≤ |dirichletK n (θ - chebTheta n k0)| + |dirichletK n (θ + chebTheta n k0)| :=
            abs_add_le _ _
      _ ≤ 2 * (n : ℝ) + 2 * (n : ℝ) :=
            add_le_add (dirichletK_abs_le hn _) (dirichletK_abs_le hn _)
      _ = 2 * (2 * (n : ℝ)) := by ring
  -- Bound each term k ≠ k0 via cotangent inequality
  have hterm_ne : ∀ k ∈ Finset.univ.erase k0,
      |lagBasisVal (chebNode n) k (Real.cos θ)| ≤
        (2 / Real.pi) *
          ((if k.1 < k0.1 then 1 / (2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1)
            else 1 / (2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1)) +
           1 / (2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1) +
           1 / (2 * (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) + 1)) := by
    intro k hk
    have hkne : k ≠ k0 := (Finset.mem_erase.mp hk).1
    have hkne_val : k.1 ≠ k0.1 := fun h => hkne (Fin.ext h)
    have hsep : (if k.1 < k0.1 then
          ((2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) ≤ θ - chebTheta n k
        else
          ((2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) ≤ chebTheta n k - θ) := by
      split_ifs with hlt
      · have hcast : 2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1 = 2 * (k0.1 : ℝ) - 2 * (k.1 : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]; ring
        rw [hcast]
        unfold chebTheta
        have hEq : (2 * (k0.1 : ℝ) - 2 * (k.1 : ℝ) - 1) * Real.pi / (2 * (n : ℝ)) =
            (k0.1 : ℝ) * Real.pi / (n : ℝ) - (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
          field_simp [hn_pos.ne']; ring
        linarith
      · have hgt : k0.1 < k.1 := by omega
        have hcast : 2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1 = 2 * (k.1 : ℝ) - 2 * (k0.1 : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]; ring
        rw [hcast]
        unfold chebTheta
        have hEq : (2 * (k.1 : ℝ) - 2 * (k0.1 : ℝ) - 1) * Real.pi / (2 * (n : ℝ)) =
            (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) - ((k0.1 : ℝ) + 1) * Real.pi / (n : ℝ) := by
          field_simp [hn_pos.ne']; ring
        linarith
    have hθ_ne : θ ≠ chebTheta n k := by
      intro hEq
      split_ifs at hsep with hlt
      · rw [hEq, sub_self] at hsep
        have hpos : 0 < (2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
          positivity
        linarith
      · rw [hEq, sub_self] at hsep
        have hpos : 0 < (2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
          positivity
        linarith
    rw [cheb_lagBasis_cot_formula hn k hθ_mem hθ_ne, abs_mul]
    have hpref : |((-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ)) / (2 * (n : ℝ))| ≤
        1 / (2 * (n : ℝ)) := by
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by positivity)
    have hcot_tri :
        |Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
          Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)| ≤
        |Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)| +
          |Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2)| := by
      rw [sub_eq_add_neg, add_comm]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    have hk_mem := chebTheta_mem_Ioo k
    have hsub_cot :
        |Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)| ≤
          2 / |θ - chebTheta n k| := by
      have habs_pos : 0 < |θ - chebTheta n k| / 2 := half_pos (abs_pos.mpr (sub_ne_zero.mpr hθ_ne))
      have habs_le : |θ - chebTheta n k| / 2 ≤ Real.pi / 2 := by
        have : |θ - chebTheta n k| ≤ Real.pi := by
          rw [abs_le]; constructor <;> linarith [hθ_mem.1, hθ_mem.2, hk_mem.1, hk_mem.2]
        linarith
      have hEq_abs : |Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)| =
          Real.cos (|θ - chebTheta n k| / 2) / Real.sin (|θ - chebTheta n k| / 2) := by
        rcases le_or_gt 0 (θ - chebTheta n k) with hnn | hneg
        · rw [abs_of_nonneg hnn]
          exact abs_of_nonneg (div_nonneg
            (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by rw [abs_of_nonneg hnn] at habs_le; exact habs_le⟩)
            (Real.sin_pos_of_pos_of_lt_pi (by rw [abs_of_nonneg hnn] at habs_pos; exact habs_pos)
              (by rw [abs_of_nonneg hnn] at habs_le; linarith [Real.pi_pos])).le)
        · rw [abs_of_neg hneg]
          have harg : (θ - chebTheta n k) / 2 = -(-(θ - chebTheta n k) / 2) := by ring
          rw [harg, Real.cos_neg, Real.sin_neg, div_neg, abs_neg]
          exact abs_of_nonneg (div_nonneg
            (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by rw [abs_of_neg hneg] at habs_le; exact habs_le⟩)
            (Real.sin_pos_of_pos_of_lt_pi (by rw [abs_of_neg hneg] at habs_pos; exact habs_pos)
              (by rw [abs_of_neg hneg] at habs_le; linarith [Real.pi_pos])).le)
      rw [hEq_abs]
      calc
        Real.cos (|θ - chebTheta n k| / 2) / Real.sin (|θ - chebTheta n k| / 2)
            ≤ 1 / (|θ - chebTheta n k| / 2) := cos_div_sin_le_inv habs_pos habs_le
        _ = 2 / |θ - chebTheta n k| := by
              have hne' : |θ - chebTheta n k| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hθ_ne)
              field_simp [hne']
    have hterm1 : (1 / (2 * (n : ℝ))) * (2 / |θ - chebTheta n k|) ≤
        (2 / Real.pi) *
          (if k.1 < k0.1 then 1 / (2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1)
           else 1 / (2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1)) := by
      have habs_ge :
          (if k.1 < k0.1 then (2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1)
           else (2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1)) * Real.pi / (2 * (n : ℝ)) ≤
            |θ - chebTheta n k| := by
        split_ifs at hsep ⊢ with hlt
        · exact hsep.trans (le_abs_self _)
        · rw [abs_sub_comm]; exact hsep.trans (le_abs_self _)
      split_ifs at habs_ge ⊢ with hlt
      · have hden_pos : 0 < (2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
          positivity
        have h1 : 1 / |θ - chebTheta n k| ≤
            1 / ((2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) :=
          one_div_le_one_div_of_le hden_pos habs_ge
        have hEqL : (1 / (2 * (n : ℝ))) * (2 / |θ - chebTheta n k|) =
            (1 / (n : ℝ)) * (1 / |θ - chebTheta n k|) := by ring
        have hEqR : (1 / (n : ℝ)) * (1 / ((2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) =
            (2 / Real.pi) * (1 / (2 * ((k0.1 - k.1 - 1 : ℕ) : ℝ) + 1)) := by
          field_simp [hn_pos.ne', Real.pi_pos.ne']
        rw [hEqL, ← hEqR]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      · have hden_pos : 0 < (2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
          positivity
        have h1 : 1 / |θ - chebTheta n k| ≤
            1 / ((2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) :=
          one_div_le_one_div_of_le hden_pos habs_ge
        have hEqL : (1 / (2 * (n : ℝ))) * (2 / |θ - chebTheta n k|) =
            (1 / (n : ℝ)) * (1 / |θ - chebTheta n k|) := by ring
        have hEqR : (1 / (n : ℝ)) * (1 / ((2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) =
            (2 / Real.pi) * (1 / (2 * ((k.1 - k0.1 - 1 : ℕ) : ℝ) + 1)) := by
          field_simp [hn_pos.ne', Real.pi_pos.ne']
        rw [hEqL, ← hEqR]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hadd_cot :
        |Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2)| ≤
          2 / (θ + chebTheta n k) + 2 / (2 * Real.pi - (θ + chebTheta n k)) := by
      have h0 : 0 < (θ + chebTheta n k) / 2 := by linarith [hθ_mem.1, hk_mem.1]
      have h1 : (θ + chebTheta n k) / 2 < Real.pi := by linarith [hθ_mem.2, hk_mem.2]
      have h := abs_cos_div_sin_le h0 h1
      have hR1 : 1 / ((θ + chebTheta n k) / 2) = 2 / (θ + chebTheta n k) := by
        field_simp [show θ + chebTheta n k ≠ 0 by linarith]
      have hR2 : 1 / (Real.pi - (θ + chebTheta n k) / 2) = 2 / (2 * Real.pi - (θ + chebTheta n k)) := by
        have hden : Real.pi - (θ + chebTheta n k) / 2 = (2 * Real.pi - (θ + chebTheta n k)) / 2 := by
          ring
        rw [hden]
        field_simp [show 2 * Real.pi - (θ + chebTheta n k) ≠ 0 by linarith]
      linarith
    have hterm2a : (1 / (2 * (n : ℝ))) * (2 / (θ + chebTheta n k)) ≤
        (2 / Real.pi) * (1 / (2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1)) := by
      have hlo : (2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) ≤ θ + chebTheta n k := by
        unfold chebTheta
        have hEq : (2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) =
            (k0.1 : ℝ) * Real.pi / (n : ℝ) + (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
          push_cast; field_simp [hn_pos.ne']; ring
        linarith
      have hden_pos : 0 < (2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by positivity
      have h1 := one_div_le_one_div_of_le hden_pos hlo
      have hEqL : (1 / (2 * (n : ℝ))) * (2 / (θ + chebTheta n k)) =
          (1 / (n : ℝ)) * (1 / (θ + chebTheta n k)) := by ring
      have hEqR : (1 / (n : ℝ)) * (1 / ((2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) =
          (2 / Real.pi) * (1 / (2 * ((k.1 + k0.1 : ℕ) : ℝ) + 1)) := by
        field_simp [hn_pos.ne', Real.pi_pos.ne']
      rw [hEqL, ← hEqR]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hterm2b : (1 / (2 * (n : ℝ))) * (2 / (2 * Real.pi - (θ + chebTheta n k))) ≤
        (2 / Real.pi) * (1 / (2 * (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) + 1)) := by
      have hlo : (2 * (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) ≤
          2 * Real.pi - (θ + chebTheta n k) := by
        unfold chebTheta
        have hcast : (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) =
            2 * (n : ℝ) - 2 - (k.1 : ℝ) - (k0.1 : ℝ) := by
          have hk_le : k.1 ≤ n - 1 := by have := k.isLt; omega
          have hk0_le : k0.1 ≤ n - 1 := by have := k0.isLt; omega
          push_cast
          rw [Nat.cast_sub hk_le, Nat.cast_sub hk0_le, Nat.cast_sub hn, Nat.cast_one]
          ring
        rw [hcast]
        have hEq : (2 * (2 * (n : ℝ) - 2 - (k.1 : ℝ) - (k0.1 : ℝ)) + 1) * Real.pi / (2 * (n : ℝ)) =
            2 * Real.pi - (((k0.1 : ℝ) + 1) * Real.pi / (n : ℝ) +
              (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) := by
          field_simp [hn_pos.ne']; ring
        linarith
      have hden_pos :
          0 < (2 * (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
        positivity
      have h1 := one_div_le_one_div_of_le hden_pos hlo
      have hEqL : (1 / (2 * (n : ℝ))) * (2 / (2 * Real.pi - (θ + chebTheta n k))) =
          (1 / (n : ℝ)) * (1 / (2 * Real.pi - (θ + chebTheta n k))) := by ring
      have hEqR : (1 / (n : ℝ)) *
          (1 / ((2 * (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) =
          (2 / Real.pi) * (1 / (2 * (((n - 1 - k.1) + (n - 1 - k0.1) : ℕ) : ℝ) + 1)) := by
        field_simp [hn_pos.ne', Real.pi_pos.ne']
      rw [hEqL, ← hEqR]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    calc
      |((-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ)) / (2 * (n : ℝ))| *
          |Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
            Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)|
          ≤ (1 / (2 * (n : ℝ))) *
              (2 / |θ - chebTheta n k| +
                (2 / (θ + chebTheta n k) + 2 / (2 * Real.pi - (θ + chebTheta n k)))) := by
            refine mul_le_mul hpref (hcot_tri.trans (add_le_add hsub_cot hadd_cot)) (abs_nonneg _)
              (by positivity)
      _ = (1 / (2 * (n : ℝ))) * (2 / |θ - chebTheta n k|) +
            (1 / (2 * (n : ℝ))) * (2 / (θ + chebTheta n k)) +
            (1 / (2 * (n : ℝ))) * (2 / (2 * Real.pi - (θ + chebTheta n k))) := by ring
      _ ≤ _ := by linarith
  -- Sum the odd-harmonic terms using cheb_odd_sum_pair_bound
  let fOdd : ℕ → ℝ := fun m => (1 : ℝ) / (2 * (m : ℝ) + 1)
  have hsum_erased :
      ∑ k ∈ Finset.univ.erase k0, |lagBasisVal (chebNode n) k (Real.cos θ)| ≤
        (2 / Real.pi) * (2 * ∑ m ∈ Finset.range (2 * n), fOdd m) := by
    calc
      ∑ k ∈ Finset.univ.erase k0, |lagBasisVal (chebNode n) k (Real.cos θ)|
          ≤ ∑ k ∈ Finset.univ.erase k0,
              (2 / Real.pi) *
                ((if k.1 < k0.1 then fOdd (k0.1 - k.1 - 1) else fOdd (k.1 - k0.1 - 1)) +
                 fOdd (k.1 + k0.1) + fOdd ((n - 1 - k.1) + (n - 1 - k0.1))) :=
            Finset.sum_le_sum hterm_ne
      _ = (2 / Real.pi) * ∑ k ∈ Finset.univ.erase k0,
            ((if k.1 < k0.1 then fOdd (k0.1 - k.1 - 1) else fOdd (k.1 - k0.1 - 1)) +
              fOdd (k.1 + k0.1) + fOdd ((n - 1 - k.1) + (n - 1 - k0.1))) := by
            rw [← Finset.mul_sum]
      _ ≤ (2 / Real.pi) * (2 * ∑ m ∈ Finset.range (2 * n), fOdd m) :=
            mul_le_mul_of_nonneg_left
              (cheb_odd_sum_pair_bound k0 fOdd (fun m => by dsimp [fOdd]; positivity))
              (by positivity)
  -- Finish numeric constant: 2 + (4 / π) * (1 + (1/2) * log (2n)) ≤ (2/π) * log n + 4
  have hodd_bound := sum_odd_inv_le (show 1 ≤ 2 * n by omega)
  have hlog2n : Real.log ((2 * n : ℕ) : ℝ) = Real.log 2 + Real.log (n : ℝ) := by
    push_cast; exact Real.log_mul two_ne_zero hn_pos.ne'
  rw [hlog2n] at hodd_bound
  have hlog2_le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2); linarith
  have hpi_gt : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hconst : (4 / Real.pi) * (1 + (1 / 2 : ℝ) * Real.log 2) ≤ 2 := by
    have h1 : 1 + (1 / 2 : ℝ) * Real.log 2 ≤ 1.5 := by linarith
    have h2 : (4 / Real.pi) * (1 + (1 / 2 : ℝ) * Real.log 2) < (4 / 3.14) * 1.5 := by
      have hdiv : 4 / Real.pi < 4 / 3.14 :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi_gt
      calc
        (4 / Real.pi) * (1 + (1 / 2 : ℝ) * Real.log 2)
            ≤ (4 / Real.pi) * 1.5 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ < (4 / 3.14) * 1.5 := mul_lt_mul_of_pos_right hdiv (by norm_num)
    linarith
  have hstep : (2 / Real.pi) * (2 * ∑ m ∈ Finset.range (2 * n), fOdd m) ≤
      (2 / Real.pi) * Real.log (n : ℝ) + 2 := by
    have hmul : (2 / Real.pi) * (2 * ∑ m ∈ Finset.range (2 * n), fOdd m) ≤
        (2 / Real.pi) * (2 * (1 + (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hodd_bound two_pos.le) (by positivity)
    have hEq : (2 / Real.pi) * (2 * (1 + (1 / 2 : ℝ) * (Real.log 2 + Real.log (n : ℝ)))) =
        (2 / Real.pi) * Real.log (n : ℝ) + (4 / Real.pi) * (1 + (1 / 2 : ℝ) * Real.log 2) := by
      ring
    linarith
  linarith

/-- **Exact Chebyshev Endpoint Lebesgue Formula & Optimal `(2/π) log n` Lower Bound:**
At `x = 1`, the Lebesgue function of the first-kind Chebyshev nodes equals the exact cotangent
sum `(1 / n) * ∑_{k=0}^{n-1} cot((2k + 1)π / (4n))`, which satisfies the matching sharp lower
bound `Λ_n^Cheb(1) ≥ (2 / π) * log n - 2 / π`. -/
theorem ppl128_chebyshev_endpoint_exact_and_lower_bound {n : ℕ} (hn : 1 ≤ n) :
    (∑ k : Fin n, |∏ j ∈ Finset.univ.erase k,
      ((1 : ℝ) - Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) /
      (Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) -
        Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ))))| =
      (1 / (n : ℝ)) * ∑ k : Fin n,
        Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (4 * (n : ℝ))) /
        Real.sin ((2 * (k : ℝ) + 1) * Real.pi / (4 * (n : ℝ)))) ∧
    ((2 / Real.pi) * Real.log (n : ℝ) - 2 / Real.pi ≤
      ∑ k : Fin n, |∏ j ∈ Finset.univ.erase k,
        ((1 : ℝ) - Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ)))) /
        (Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) -
          Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * (n : ℝ))))|) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hexact : lebesgueFn (chebNode n) 1 =
      (1 / (n : ℝ)) * ∑ k : Fin n,
        Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2) := by
    rw [← Real.cos_zero]
    unfold lebesgueFn
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk_mem := chebTheta_mem_Ioo k
    rw [cheb_lagBasis_cot_formula hn k ⟨le_rfl, Real.pi_pos.le⟩ hk_mem.1.ne]
    simp only [mul_zero, Real.cos_zero, mul_one, zero_add, zero_sub, neg_div,
      Real.cos_neg, Real.sin_neg, div_neg, sub_neg_eq_add]
    have hu0 : 0 < chebTheta n k / 2 := half_pos hk_mem.1
    have hu1 : chebTheta n k / 2 < Real.pi / 2 := by linarith [hk_mem.2]
    have hcot_nn : 0 ≤ Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2) :=
      div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, hu1.le⟩)
        (Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])).le
    have hEq : (-1 : ℝ) ^ (k : ℕ) / (2 * (n : ℝ)) *
        (Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2) +
          Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2)) =
        (-1 : ℝ) ^ (k : ℕ) * ((1 / (n : ℝ)) *
          (Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2))) := by
      ring
    rw [hEq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (mul_nonneg (by positivity) hcot_nn)]
  have harg : ∀ k : Fin n, chebTheta n k / 2 = (2 * (k : ℝ) + 1) * Real.pi / (4 * (n : ℝ)) := by
    intro k; unfold chebTheta; ring
  have hexact' : lebesgueFn (chebNode n) 1 =
      (1 / (n : ℝ)) * ∑ k : Fin n,
        Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (4 * (n : ℝ))) /
        Real.sin ((2 * (k : ℝ) + 1) * Real.pi / (4 * (n : ℝ))) := by
    rw [hexact]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by rw [harg k]
  refine ⟨hexact', ?_⟩
  change (2 / Real.pi) * Real.log (n : ℝ) - 2 / Real.pi ≤ lebesgueFn (chebNode n) 1
  rw [hexact]
  have hcot_lb : ∀ k : Fin n,
      (4 * (n : ℝ)) / ((2 * (k : ℝ) + 1) * Real.pi) - 2 / Real.pi ≤
        Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2) := by
    intro k
    have hk_mem := chebTheta_mem_Ioo k
    have h := inv_sub_two_div_pi_le_cos_div_sin (half_pos hk_mem.1) (by linarith [hk_mem.2])
    have h1 : 1 / (chebTheta n k / 2) = (4 * (n : ℝ)) / ((2 * (k : ℝ) + 1) * Real.pi) := by
      rw [harg k]; field_simp [hn_pos.ne', Real.pi_pos.ne']
    linarith
  have hsum_lb :
      (1 / (n : ℝ)) * ∑ k : Fin n,
          ((4 * (n : ℝ)) / ((2 * (k : ℝ) + 1) * Real.pi) - 2 / Real.pi) ≤
        (1 / (n : ℝ)) * ∑ k : Fin n,
          Real.cos (chebTheta n k / 2) / Real.sin (chebTheta n k / 2) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hcot_lb k) (by positivity)
  have hsimp :
      (1 / (n : ℝ)) * ∑ k : Fin n,
          ((4 * (n : ℝ)) / ((2 * (k : ℝ) + 1) * Real.pi) - 2 / Real.pi) =
        (4 / Real.pi) * (∑ k : Fin n, (1 : ℝ) / (2 * (k : ℝ) + 1)) - 2 / Real.pi := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_sub, Finset.mul_sum, Finset.mul_sum]
    have h1 : (1 / (n : ℝ)) * ((n : ℝ) * (2 / Real.pi)) = 2 / Real.pi := by
      field_simp [hn_pos.ne']
    rw [h1]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp [hn_pos.ne', Real.pi_pos.ne']
  have hharm : (1 / 2 : ℝ) * Real.log (n : ℝ) ≤ ∑ k : Fin n, (1 : ℝ) / (2 * (k : ℝ) + 1) := by
    have h1 : ∑ k : Fin n, (1 : ℝ) / (2 * ((k : ℝ) + 1)) ≤
        ∑ k : Fin n, (1 : ℝ) / (2 * (k : ℝ) + 1) :=
      Finset.sum_le_sum fun k _ => one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : ∑ k : Fin n, (1 : ℝ) / (2 * ((k : ℝ) + 1)) =
        (1 / 2 : ℝ) * ∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / (j : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun k _ => k.1 + 1) ?_ ?_ ?_ ?_
      · intro k _; simp only [Finset.mem_Icc]; have := k.isLt; omega
      · intro k₁ _ k₂ _ h; ext; omega
      · intro j hj
        simp only [Finset.mem_Icc] at hj
        exact ⟨⟨j - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
      · intro k _
        push_cast
        have hpos : (k : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hpos]
    have h3 : Real.log (n : ℝ) ≤ ∑ j ∈ Finset.Icc 1 n, (1 : ℝ) / (j : ℝ) :=
      (Real.log_le_log hn_pos (by linarith)).trans (log_le_harmonic n)
    linarith
  have hfinal : (2 / Real.pi) * Real.log (n : ℝ) - 2 / Real.pi ≤
      (4 / Real.pi) * (∑ k : Fin n, (1 : ℝ) / (2 * (k : ℝ) + 1)) - 2 / Real.pi := by
    have h1 := mul_le_mul_of_nonneg_left hharm (show 0 ≤ 4 / Real.pi by positivity)
    have h2 : 4 / Real.pi * (1 / 2 * Real.log (n : ℝ)) = (2 / Real.pi) * Real.log (n : ℝ) := by
      ring
    linarith
  linarith

private lemma abs_cos_sub_cos_le (a b : ℝ) :
    |Real.cos a - Real.cos b| ≤ |a - b| := by
  have htrig : Real.cos a - Real.cos b = -2 * Real.sin ((a + b) / 2) * Real.sin ((a - b) / 2) := by
    have h1 : a = (a + b) / 2 + (a - b) / 2 := by ring
    have h2 : b = (a + b) / 2 - (a - b) / 2 := by ring
    conv_lhs => rw [h1, h2]
    rw [Real.cos_add, Real.cos_sub]
    ring
  rw [htrig, abs_mul, abs_mul, abs_neg, abs_of_pos two_pos]
  calc
    2 * |Real.sin ((a + b) / 2)| * |Real.sin ((a - b) / 2)|
        ≤ 2 * 1 * |(a - b) / 2| :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) two_pos.le)
            Real.abs_sin_le_abs (abs_nonneg _) (by norm_num)
    _ = |a - b| := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring

private lemma cheb_lebesgue_pointwise_lower_of_large_cos {n : ℕ} (hn : 8 ≤ n)
    {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (hcos : 1 / 2 ≤ |Real.cos ((n : ℝ) * θ)|) :
    (1 / (4 * Real.pi)) * (Real.log ((n / 4 : ℕ) : ℝ) - 1) ≤
      lebesgueFn (chebNode n) (Real.cos θ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hθ_Icc : θ ∈ Set.Icc 0 Real.pi := ⟨hθ.1, hθ.2.trans (by linarith [Real.pi_pos])⟩
  -- For every k : Fin n, θ ≠ chebTheta n k because cos(n * chebTheta n k) = 0 ≠ cos(n * θ)
  have hθ_ne : ∀ k : Fin n, θ ≠ chebTheta n k := by
    intro k hEq
    have h0 : Real.cos ((n : ℝ) * chebTheta n k) = 0 := by
      unfold chebTheta
      have harg : (n : ℝ) * ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ))) =
          (k : ℝ) * Real.pi + Real.pi / 2 := by field_simp [hn_pos.ne']
      rw [harg, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]
    rw [hEq, h0, abs_zero] at hcos
    linarith
  let k0 : ℕ := ⌊(n : ℝ) * θ / Real.pi⌋₊
  have hk0_le_th : (k0 : ℝ) * Real.pi / (n : ℝ) ≤ θ := by
    have hfl := Nat.floor_le (div_nonneg (mul_nonneg hn_pos.le hθ.1) Real.pi_pos.le)
    rw [div_le_iff₀ hn_pos]
    have := (le_div_iff₀ Real.pi_pos).mp hfl
    linarith
  have hth_lt_k0 : θ < ((k0 : ℝ) + 1) * Real.pi / (n : ℝ) := by
    have hfl := Nat.lt_floor_add_one ((n : ℝ) * θ / Real.pi)
    rw [lt_div_iff₀ hn_pos]
    have := (div_lt_iff₀ Real.pi_pos).mp hfl
    linarith
  have hdist_ub : ∀ k : Fin n, k0 + 1 ≤ k.1 →
      0 < chebTheta n k - θ ∧ chebTheta n k - θ ≤ ((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
    intro k hk
    unfold chebTheta
    constructor
    · have h1 : ((k0 : ℝ) + 1) * Real.pi / (n : ℝ) < (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) := by
        have hlt : (k0 : ℝ) + 1 ≤ (k.1 : ℝ) := by exact_mod_cast hk
        rw [div_lt_div_iff₀ hn_pos (by positivity)]
        have hpi_n : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hn_pos
        nlinarith
      linarith
    · have hcast : ((k.1 - k0 + 1 : ℕ) : ℝ) = (k.1 : ℝ) - (k0 : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcast]
      have h2 : (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) - (k0 : ℝ) * Real.pi / (n : ℝ) ≤
          ((k.1 : ℝ) - (k0 : ℝ) + 1) * Real.pi / (n : ℝ) := by
        have hEq : (2 * (k.1 : ℝ) + 1) * Real.pi / (2 * (n : ℝ)) - (k0 : ℝ) * Real.pi / (n : ℝ) =
            ((k.1 : ℝ) - (k0 : ℝ) + 1 / 2) * Real.pi / (n : ℝ) := by
          field_simp [hn_pos.ne']; ring
        rw [hEq]
        exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hn_pos.le
      linarith
  -- Harmonic tail helper: ∑_{j=2}^{m} 1/j ≥ log m - 1 for m ≥ 2
  have hharm_tail : ∀ m : ℕ, 2 ≤ m →
      Real.log (m : ℝ) - 1 ≤ ∑ j ∈ Finset.Icc 2 m, (1 : ℝ) / (j : ℝ) := by
    intro m hm
    have hsplit : Finset.Icc 1 m = insert 1 (Finset.Icc 2 m) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnm : 1 ∉ Finset.Icc 2 m := by simp
    have hfull : Real.log (m : ℝ) ≤ ∑ j ∈ Finset.Icc 1 m, (1 : ℝ) / (j : ℝ) :=
      (Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) (by linarith)).trans
        (log_le_harmonic m)
    rw [hsplit, Finset.sum_insert hnm] at hfull
    have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) = 1 := by norm_num
    rw [h1] at hfull
    linarith
  by_cases hquarter : θ ≤ Real.pi / 4
  · -- Case 1: θ ∈ [0, π/4], sum over k ∈ [k0 + 1, n / 2)
    have hk0_le_q : k0 ≤ n / 4 := by
      have hle : (n : ℝ) * θ / Real.pi ≤ (n : ℝ) / 4 := by
        rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
        nlinarith [Real.pi_pos]
      have hfl : k0 ≤ ⌊(n : ℝ) / 4⌋₊ := Nat.floor_mono hle
      have hnat : ⌊(n : ℝ) / 4⌋₊ = n / 4 := by
        rw [Nat.floor_eq_iff (by positivity)]
        constructor
        · have : ((n / 4 : ℕ) : ℝ) * 4 ≤ (n : ℝ) := by exact_mod_cast Nat.div_mul_le_self n 4
          linarith
        · have : (n : ℝ) < (((n / 4 : ℕ) + 1 : ℕ) : ℝ) * 4 := by
            have := Nat.lt_div_mul_add (a := n) (b := 4) (by norm_num)
            exact_mod_cast (show n < (n / 4 + 1) * 4 by omega)
          push_cast at this; linarith
      omega
    let S : Finset (Fin n) := Finset.univ.filter fun k : Fin n => k0 + 1 ≤ k.1 ∧ k.1 < n / 2
    have hS_term : ∀ k ∈ S,
        1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ)) ≤
          |lagBasisVal (chebNode n) k (Real.cos θ)| := by
      intro k hk
      rcases (Finset.mem_filter.mp hk).2 with ⟨hk_lo, hk_hi⟩
      have hd := hdist_ub k hk_lo
      have hthk_lt : chebTheta n k < Real.pi / 2 := by
        unfold chebTheta
        rw [div_lt_div_iff₀ (by positivity) two_pos]
        have h2k : 2 * (k.1 : ℝ) + 1 < (n : ℝ) := by
          have : 2 * k.1 + 1 < n := by omega
          exact_mod_cast this
        nlinarith [Real.pi_pos]
      rw [cheb_lagBasis_cot_formula (by omega : 1 ≤ n) k hθ_Icc (hθ_ne k), abs_mul]
      have hpref : 1 / (4 * (n : ℝ)) ≤
          |((-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ)) / (2 * (n : ℝ))| := by
        rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hn_pos, hcos]
      have hcot_add_pos : 0 ≤ Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) := by
        have h0 : 0 < (θ + chebTheta n k) / 2 := by linarith [hθ.1, (chebTheta_mem_Ioo k).1]
        have h1 : (θ + chebTheta n k) / 2 < Real.pi / 2 := by linarith [hquarter, hthk_lt]
        exact div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, h1.le⟩)
          (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).le
      have hcot_sub_eq :
          -(Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)) =
            Real.cos ((chebTheta n k - θ) / 2) / Real.sin ((chebTheta n k - θ) / 2) := by
        have harg : (θ - chebTheta n k) / 2 = -((chebTheta n k - θ) / 2) := by ring
        rw [harg, Real.cos_neg, Real.sin_neg, div_neg, neg_neg]
      have hcot_sub_lb : 1 / (chebTheta n k - θ) ≤
          Real.cos ((chebTheta n k - θ) / 2) / Real.sin ((chebTheta n k - θ) / 2) := by
        let u : ℝ := (chebTheta n k - θ) / 2
        have hu0 : 0 < u := half_pos hd.1
        have hu_le : u ≤ Real.pi / 3 := by dsimp [u]; linarith [hθ.1, hthk_lt]
        have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [Real.pi_pos])
        have hsin_le : Real.sin u ≤ u := Real.sin_le hu0.le
        have hcos_ge : 1 / 2 ≤ Real.cos u := by
          rw [← Real.cos_pi_div_three]
          exact Real.antitoneOn_cos ⟨hu0.le, by linarith [Real.pi_pos]⟩
            ⟨by positivity, by linarith [Real.pi_pos]⟩ hu_le
        calc
          1 / (chebTheta n k - θ) = (1 / 2) / u := by dsimp [u]; field_simp [hd.1.ne']
          _ ≤ Real.cos u / u := div_le_div_of_nonneg_right hcos_ge hu0.le
          _ ≤ Real.cos u / Real.sin u :=
                div_le_div_of_nonneg_left (by linarith) hsin_pos hsin_le
      have hcot_abs : 1 / (chebTheta n k - θ) ≤
          |Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
            Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)| := by
        have hdiff_eq :
            Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
              Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2) =
            Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) +
              Real.cos ((chebTheta n k - θ) / 2) / Real.sin ((chebTheta n k - θ) / 2) := by
          linarith [hcot_sub_eq]
        rw [hdiff_eq]
        exact (by linarith : 1 / (chebTheta n k - θ) ≤
          Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) +
            Real.cos ((chebTheta n k - θ) / 2) / Real.sin ((chebTheta n k - θ) / 2)).trans
          (le_abs_self _)
      have hdist_inv : (n : ℝ) / (((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi) ≤ 1 / (chebTheta n k - θ) := by
        have h1 := one_div_le_one_div_of_le hd.1 hd.2
        have hEq : 1 / (((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ)) =
            (n : ℝ) / (((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi) := by field_simp [hn_pos.ne']
        linarith
      calc
        1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ))
            = (1 / (4 * (n : ℝ))) * ((n : ℝ) / (((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi)) := by
              field_simp [hn_pos.ne', Real.pi_pos.ne']
        _ ≤ |((-1 : ℝ) ^ (k : ℕ) * Real.cos ((n : ℝ) * θ)) / (2 * (n : ℝ))| *
              |Real.cos ((θ + chebTheta n k) / 2) / Real.sin ((θ + chebTheta n k) / 2) -
                Real.cos ((θ - chebTheta n k) / 2) / Real.sin ((θ - chebTheta n k) / 2)| :=
              mul_le_mul hpref (hdist_inv.trans hcot_abs) (by positivity) (abs_nonneg _)
    -- Sum over S ≥ (1 / (4π)) * ∑_{j=2}^{n/4} 1/j
    have hS_sum :
        (1 / (4 * Real.pi)) * ∑ j ∈ Finset.Icc 2 (n / 4), (1 : ℝ) / (j : ℝ) ≤
          ∑ k ∈ S, |lagBasisVal (chebNode n) k (Real.cos θ)| := by
      let gMap : ℕ → Fin n := fun j =>
        if hj : j + k0 - 1 < n then ⟨j + k0 - 1, hj⟩ else ⟨0, by omega⟩
      have hreidx :
          (1 / (4 * Real.pi)) * ∑ j ∈ Finset.Icc 2 (n / 4), (1 : ℝ) / (j : ℝ) =
            ∑ j ∈ Finset.Icc 2 (n / 4), 1 / (4 * Real.pi * (((gMap j).1 - k0 + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_Icc] at hj
        have hlt : j + k0 - 1 < n := by omega
        have hval : (gMap j).1 = j + k0 - 1 := by simp [gMap, dif_pos hlt]
        rw [hval, show j + k0 - 1 - k0 + 1 = j by omega]
        ring
      calc
        (1 / (4 * Real.pi)) * ∑ j ∈ Finset.Icc 2 (n / 4), (1 : ℝ) / (j : ℝ)
            = ∑ j ∈ Finset.Icc 2 (n / 4), 1 / (4 * Real.pi * (((gMap j).1 - k0 + 1 : ℕ) : ℝ)) :=
              hreidx
        _ ≤ ∑ k ∈ S, 1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ)) := by
              refine sum_le_sum_of_injOn gMap
                (fun k : Fin n => 1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ))) ?_ ?_
                (fun _ _ => by positivity)
              · intro j hj
                simp only [Finset.mem_Icc] at hj
                have hlt : j + k0 - 1 < n := by omega
                simp only [gMap, dif_pos hlt, S, Finset.mem_filter, Finset.mem_univ, true_and]
                omega
              · intro j₁ hj₁ j₂ hj₂ hEq
                simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
                have h1 : j₁ + k0 - 1 < n := by omega
                have h2 : j₂ + k0 - 1 < n := by omega
                simp only [gMap, dif_pos h1, dif_pos h2, Fin.mk.injEq] at hEq
                omega
        _ ≤ ∑ k ∈ S, |lagBasisVal (chebNode n) k (Real.cos θ)| := Finset.sum_le_sum hS_term
    have hle_all : ∑ k ∈ S, |lagBasisVal (chebNode n) k (Real.cos θ)| ≤
        lebesgueFn (chebNode n) (Real.cos θ) := by
      unfold lebesgueFn
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _
    have htail := hharm_tail (n / 4) (by omega)
    exact (mul_le_mul_of_nonneg_left htail (by positivity)).trans (hS_sum.trans hle_all)
  · -- Case 2: θ ∈ (π/4, π/2], sum over k ∈ [k0 + 1, 3 * n / 4)
    push Not at hquarter
    have hk0_le_half : k0 ≤ n / 2 := by
      have hle : (n : ℝ) * θ / Real.pi ≤ (n : ℝ) / 2 := by
        rw [div_le_div_iff₀ Real.pi_pos two_pos]
        nlinarith [Real.pi_pos, hθ.2]
      have hfl : k0 ≤ ⌊(n : ℝ) / 2⌋₊ := Nat.floor_mono hle
      have hnat : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
        rw [Nat.floor_eq_iff (by positivity)]
        constructor
        · have : ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast Nat.div_mul_le_self n 2
          linarith
        · have : (n : ℝ) < (((n / 2 : ℕ) + 1 : ℕ) : ℝ) * 2 := by
            exact_mod_cast (show n < (n / 2 + 1) * 2 by omega)
          push_cast at this; linarith
      omega
    let S : Finset (Fin n) := Finset.univ.filter fun k : Fin n => k0 + 1 ≤ k.1 ∧ k.1 < 3 * n / 4
    have hS_term : ∀ k ∈ S,
        1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ)) ≤
          |lagBasisVal (chebNode n) k (Real.cos θ)| := by
      intro k hk
      rcases (Finset.mem_filter.mp hk).2 with ⟨hk_lo, hk_hi⟩
      have hd := hdist_ub k hk_lo
      have hthk_lo : Real.pi / 4 < chebTheta n k := lt_trans hquarter (by linarith [hd.1])
      have hthk_hi : chebTheta n k ≤ 5 * Real.pi / 6 := by
        unfold chebTheta
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have h2k : 2 * (k.1 : ℝ) + 1 ≤ 3 * (n : ℝ) / 2 := by
          have : 2 * k.1 + 1 ≤ 3 * n / 2 := by omega
          have h1 : ((2 * k.1 + 1 : ℕ) : ℝ) ≤ ((3 * n / 2 : ℕ) : ℝ) := by exact_mod_cast this
          have h2 : ((3 * n / 2 : ℕ) : ℝ) * 2 ≤ (3 * n : ℝ) := by
            exact_mod_cast Nat.div_mul_le_self (3 * n) 2
          push_cast at h1 h2; linarith
        nlinarith [Real.pi_pos]
      have hsin_ge : 1 / 2 ≤ Real.sin (chebTheta n k) := by
        by_cases hmid : chebTheta n k ≤ Real.pi / 2
        · rw [← Real.sin_pi_div_six]
          exact Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], hmid⟩ (by linarith [Real.pi_pos])
        · push Not at hmid
          have hEq : Real.sin (chebTheta n k) = Real.sin (Real.pi - chebTheta n k) :=
            (Real.sin_pi_sub _).symm
          rw [hEq, ← Real.sin_pi_div_six]
          exact Real.monotoneOn_sin ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
            ⟨by linarith [Real.pi_pos], by linarith⟩ (by linarith [Real.pi_pos])
      rw [cheb_lagBasis_sin_cos_formula (by omega : 1 ≤ n) k hθ_Icc (hθ_ne k), abs_div, abs_mul, abs_mul,
        abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (by linarith : 0 < Real.sin (chebTheta n k)),
        abs_mul, abs_of_pos hn_pos]
      have hcos_pos : 0 < |Real.cos θ - Real.cos (chebTheta n k)| :=
        abs_pos.mpr (sub_ne_zero.mpr fun h =>
          hθ_ne k (Real.injOn_cos hθ_Icc ⟨(chebTheta_mem_Ioo k).1.le, (chebTheta_mem_Ioo k).2.le⟩ h))
      have hcos_le : |Real.cos θ - Real.cos (chebTheta n k)| ≤
          ((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := by
        calc
          |Real.cos θ - Real.cos (chebTheta n k)| ≤ |θ - chebTheta n k| := abs_cos_sub_cos_le _ _
          _ = chebTheta n k - θ := by rw [abs_sub_comm, abs_of_pos hd.1]
          _ ≤ ((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi / (n : ℝ) := hd.2
      have hnum_ge : 1 / 4 ≤ Real.sin (chebTheta n k) * |Real.cos ((n : ℝ) * θ)| := by
        nlinarith [hsin_ge, hcos]
      have hden_le : (n : ℝ) * |Real.cos θ - Real.cos (chebTheta n k)| ≤
          ((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi := by
        have := mul_le_mul_of_nonneg_left hcos_le hn_pos.le
        rwa [mul_div_cancel₀ _ hn_pos.ne'] at this
      calc
        1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ))
            = (1 / 4) / (((k.1 - k0 + 1 : ℕ) : ℝ) * Real.pi) := by ring
        _ ≤ (Real.sin (chebTheta n k) * |Real.cos ((n : ℝ) * θ)|) /
              ((n : ℝ) * |Real.cos θ - Real.cos (chebTheta n k)|) :=
              div_le_div₀ (by linarith) hnum_ge (mul_pos hn_pos hcos_pos) hden_le
    -- Sum over S ≥ (1 / (4π)) * ∑_{j=2}^{n/4} 1/j
    have hS_sum :
        (1 / (4 * Real.pi)) * ∑ j ∈ Finset.Icc 2 (n / 4), (1 : ℝ) / (j : ℝ) ≤
          ∑ k ∈ S, |lagBasisVal (chebNode n) k (Real.cos θ)| := by
      let gMap : ℕ → Fin n := fun j =>
        if hj : j + k0 - 1 < n then ⟨j + k0 - 1, hj⟩ else ⟨0, by omega⟩
      have hreidx :
          (1 / (4 * Real.pi)) * ∑ j ∈ Finset.Icc 2 (n / 4), (1 : ℝ) / (j : ℝ) =
            ∑ j ∈ Finset.Icc 2 (n / 4), 1 / (4 * Real.pi * (((gMap j).1 - k0 + 1 : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [Finset.mem_Icc] at hj
        have hlt : j + k0 - 1 < n := by omega
        have hval : (gMap j).1 = j + k0 - 1 := by simp [gMap, dif_pos hlt]
        rw [hval, show j + k0 - 1 - k0 + 1 = j by omega]
        ring
      calc
        (1 / (4 * Real.pi)) * ∑ j ∈ Finset.Icc 2 (n / 4), (1 : ℝ) / (j : ℝ)
            = ∑ j ∈ Finset.Icc 2 (n / 4), 1 / (4 * Real.pi * (((gMap j).1 - k0 + 1 : ℕ) : ℝ)) :=
              hreidx
        _ ≤ ∑ k ∈ S, 1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ)) := by
              refine sum_le_sum_of_injOn gMap
                (fun k : Fin n => 1 / (4 * Real.pi * ((k.1 - k0 + 1 : ℕ) : ℝ))) ?_ ?_
                (fun _ _ => by positivity)
              · intro j hj
                simp only [Finset.mem_Icc] at hj
                have hlt : j + k0 - 1 < n := by omega
                simp only [gMap, dif_pos hlt, S, Finset.mem_filter, Finset.mem_univ, true_and]
                omega
              · intro j₁ hj₁ j₂ hj₂ hEq
                simp only [Finset.mem_coe, Finset.mem_Icc] at hj₁ hj₂
                have h1 : j₁ + k0 - 1 < n := by omega
                have h2 : j₂ + k0 - 1 < n := by omega
                simp only [gMap, dif_pos h1, dif_pos h2, Fin.mk.injEq] at hEq
                omega
        _ ≤ ∑ k ∈ S, |lagBasisVal (chebNode n) k (Real.cos θ)| := Finset.sum_le_sum hS_term
    have hle_all : ∑ k ∈ S, |lagBasisVal (chebNode n) k (Real.cos θ)| ≤
        lebesgueFn (chebNode n) (Real.cos θ) := by
      unfold lebesgueFn
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => abs_nonneg _
    have htail := hharm_tail (n / 4) (by omega)
    exact (mul_le_mul_of_nonneg_left htail (by positivity)).trans (hS_sum.trans hle_all)

/-- **Everywhere-Unbounded Lebesgue Function for Chebyshev Nodes (First Half of Erdős #671 Part 2):**
For EVERY `x ∈ [-1, 1]` and EVERY `M : ℝ`, there exists `n : ℕ` (`n + 1` nodes) such that the
Chebyshev Lebesgue function satisfies `M < Λ_{n+1}^Cheb(x)`.
Thus the first-kind Chebyshev node array explicitly witnesses the everywhere-divergence hypothesis
of Erdős #671 Part 2 while simultaneously achieving the asymptotically optimal `O(log n)` global
Lebesgue constant. -/
theorem ppl128_chebyshev_lebesgue_unbounded_everywhere
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (M : ℝ) :
    ∃ n : ℕ, M <
      ∑ k : Fin (n + 1), |∏ j ∈ Finset.univ.erase k,
        (x - Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * ((n + 1 : ℕ) : ℝ)))) /
        (Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * ((n + 1 : ℕ) : ℝ))) -
          Real.cos ((2 * (j : ℝ) + 1) * Real.pi / (2 * ((n + 1 : ℕ) : ℝ))))| := by
  -- Reduce to x ≥ 0 by symmetry Λ_m(-x) = Λ_m(x)
  suffices hnonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∃ m : ℕ, 1 ≤ m ∧ M < lebesgueFn (chebNode m) y by
    by_cases hx0 : 0 ≤ x
    · rcases hnonneg x ⟨hx0, hx.2⟩ with ⟨m, hm, hlt⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      exact ⟨n, hlt⟩
    · push Not at hx0
      rcases hnonneg (-x) ⟨by linarith, by linarith [hx.1]⟩ with ⟨m, hm, hlt⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [lebesgueFn_chebNode_neg] at hlt
      exact ⟨n, hlt⟩
  intro y hy
  let θ : ℝ := Real.arccos y
  have hθ : θ ∈ Set.Icc 0 (Real.pi / 2) :=
    ⟨Real.arccos_nonneg y, Real.arccos_le_pi_div_two.mpr hy.1⟩
  have hy_eq : y = Real.cos θ := (Real.cos_arccos (by linarith [hy.1]) hy.2).symm
  let N : ℕ := max 8 (4 * (⌈Real.exp (4 * Real.pi * (max M 0 + 1) + 2)⌉₊ + 1))
  have hN_ge8 : 8 ≤ N := le_max_left _ _
  -- Double-angle dichotomy: max(|cos(Nθ)|, |cos(2Nθ)|) ≥ 1/2
  have hdich : ∃ m : ℕ, N ≤ m ∧ 1 / 2 ≤ |Real.cos ((m : ℝ) * θ)| := by
    by_cases h1 : 1 / 2 ≤ |Real.cos ((N : ℝ) * θ)|
    · exact ⟨N, le_rfl, h1⟩
    · push Not at h1
      refine ⟨2 * N, by omega, ?_⟩
      have hdouble : Real.cos (((2 * N : ℕ) : ℝ) * θ) =
          2 * (Real.cos ((N : ℝ) * θ)) ^ 2 - 1 := by
        have harg : ((2 * N : ℕ) : ℝ) * θ = 2 * ((N : ℝ) * θ) := by push_cast; ring
        rw [harg, Real.cos_two_mul]
      have hsq : (Real.cos ((N : ℝ) * θ)) ^ 2 < 1 / 4 := by
        have : |Real.cos ((N : ℝ) * θ)| ^ 2 < (1 / 2 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
        rw [sq_abs] at this; linarith
      have hneg : Real.cos (((2 * N : ℕ) : ℝ) * θ) < -(1 / 2 : ℝ) := by linarith
      rw [abs_of_neg (by linarith)]
      linarith
  rcases hdich with ⟨m, hm_ge, hm_cos⟩
  refine ⟨m, by omega, ?_⟩
  rw [hy_eq]
  have hlb := cheb_lebesgue_pointwise_lower_of_large_cos (by omega) hθ hm_cos
  have hm4_gt : Real.exp (4 * Real.pi * (max M 0 + 1) + 2) < ((m / 4 : ℕ) : ℝ) := by
    have h1 : ⌈Real.exp (4 * Real.pi * (max M 0 + 1) + 2)⌉₊ + 1 ≤ m / 4 := by
      have : 4 * (⌈Real.exp (4 * Real.pi * (max M 0 + 1) + 2)⌉₊ + 1) ≤ m :=
        (le_max_right _ _).trans hm_ge
      omega
    have h2 : (⌈Real.exp (4 * Real.pi * (max M 0 + 1) + 2)⌉₊ : ℝ) + 1 ≤ ((m / 4 : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 := Nat.le_ceil (Real.exp (4 * Real.pi * (max M 0 + 1) + 2))
    linarith
  have hlog_gt : 4 * Real.pi * (max M 0 + 1) + 2 < Real.log ((m / 4 : ℕ) : ℝ) := by
    rw [← Real.log_exp (4 * Real.pi * (max M 0 + 1) + 2)]
    exact Real.log_lt_log (Real.exp_pos _) hm4_gt
  have hM_lt : M < (1 / (4 * Real.pi)) * (Real.log ((m / 4 : ℕ) : ℝ) - 1) := by
    have h1 : max M 0 + 1 < (1 / (4 * Real.pi)) * (Real.log ((m / 4 : ℕ) : ℝ) - 1) := by
      rw [one_div_mul_eq_div, lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)]
      linarith
    exact (le_max_left M 0).trans_lt (by linarith)
  exact hM_lt.trans_le hlb

end ChebyshevNodes

end PPL128
