/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# Arithmetica4 Extension: Polynomial Method & Combinatorial Nullstellensatz Engine (`Arith4Ext.AlgebraicMethod`)

Clean, general, non-vacuous Tier A reusable library built 100% from scratch on targeted
Mathlib imports (`0` monolithic `import Mathlib`, `0` Tier C imports, `0` custom axioms).

## Exported API Summary (`namespace Arith4Ext.AlgebraicMethod`)
1. **Alon's Combinatorial Nullstellensatz (`MvPolynomial`):**
   - `combinatorial_nullstellensatz_fin`: for `f : MvPolynomial (Fin n) R` over an integral domain `R`,
     if `f.totalDegree ≤ ∑ i, t i`, `f.coeff (∑ i, t i • Finsupp.single i 1) ≠ 0`, and `∀ i, t i < (S i).card`,
     then `∃ x, (∀ i, x i ∈ S i) ∧ MvPolynomial.eval x f ≠ 0`.
   - `combinatorial_nullstellensatz`: general finite-index `[Fintype ι] [DecidableEq ι]` version.
2. **Cauchy–Davenport & Erdős–Heilbronn (`ZMod p`):**
   - `cauchy_davenport`: `min p (A.card + B.card - 1) ≤ ((A ×ˢ B).image (fun x => x.1 + x.2)).card`
   - `erdos_heilbronn`: `min p (2 * A.card - 3) ≤ (((A ×ˢ A).filter (fun x => x.1 ≠ x.2)).image (fun x => x.1 + x.2)).card`
3. **Schwartz–Zippel Lemma (`MvPolynomial`):**
   - `schwartz_zippel`: for nonzero `f : MvPolynomial (Fin n) R` over an integral domain `R` and nonempty
     `S : Finset R`, `|{(x : Fin n → S) : eval x f = 0}| ≤ f.totalDegree * S.card ^ (n - 1)`.
4. **Chevalley–Warning Theorem (`ZMod p`):**
   - `chevalley_warning`: if `(fs.map totalDegree).sum < n`, then `p ∣ |{x : Fin n → ZMod p | ∀ f ∈ fs, eval x f = 0}|`.
   - `chevalley_warning_nonzero_root`: nonzero common root existence when `0` is a common root.
5. **Babai–Frankl Triangular Rank Criterion & Oddtown (`m ≤ d`):**
   - `babai_frankl_triangular`: if `v, w : Fin m → Fin d → K` satisfy `dot (v i) (w i) ≠ 0` and
     `dot (v i) (w j) = 0` for `i < j`, then `m ≤ d`.
   - `oddtown_bound`: `m` pairwise even-intersection odd-size subsets of `Fin d` satisfy `m ≤ d`.
-/

namespace Arith4Ext.AlgebraicMethod

open scoped BigOperators

/-! ## Section 1: Alon's Combinatorial Nullstellensatz -/

section Nullstellensatz

private lemma totalDegree_sum_le {σ R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) (g : α → MvPolynomial σ R) (B : ℕ)
    (hg : ∀ a ∈ s, (g a).totalDegree ≤ B) :
    (∑ a ∈ s, g a).totalDegree ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (hg a (Finset.mem_insert_self a s))
        (ih (fun b hb => hg b (Finset.mem_insert_of_mem hb))))

private lemma totalDegree_sub_le {σ R : Type*} [CommRing R] (p q : MvPolynomial σ R) :
    (p - q).totalDegree ≤ max p.totalDegree q.totalDegree := by
  rw [sub_eq_add_neg]
  exact le_trans (MvPolynomial.totalDegree_add _ _) (by simp)

private lemma coeff_eq_zero_of_totalDegree_lt {σ R : Type*} [CommRing R]
    (p : MvPolynomial σ R) (μ : σ →₀ ℕ) (h : p.totalDegree < μ.sum (fun _ e => e)) :
    p.coeff μ = 0 := by
  by_contra hne
  have hmem : μ ∈ p.support := MvPolynomial.mem_support_iff.mpr hne
  have hle : μ.sum (fun _ e => e) ≤ p.totalDegree := MvPolynomial.le_totalDegree hmem
  omega

private lemma fin_succ_finsupp_split {n : ℕ} (d : Fin (n + 1) →₀ ℕ) :
    d = d 0 • Finsupp.single 0 1 + ∑ i : Fin n, d i.succ • Finsupp.single i.succ 1 := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp [Finsupp.coe_finsetSum, Finset.sum_apply]
  · intro i
    simp [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Fin.succ_inj]

private lemma fin_succ_sum_deg {n : ℕ} (d : Fin (n + 1) →₀ ℕ) :
    d.sum (fun _ e => e) = d 0 + ∑ i : Fin n, d i.succ := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]

private lemma finSuccEquiv_C_eq {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simpa [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply] using
    (MvPolynomial.finSuccEquiv R n).commutes a

private lemma finSuccEquiv_monomial {R : Type*} [CommRing R] (n : ℕ)
    (d : Fin (n + 1) →₀ ℕ) (c : R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.monomial d c) =
      Polynomial.monomial (d 0)
        (MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) c) := by
  have hd := fin_succ_finsupp_split d
  have hprod_succ : ∀ (s : Finset (Fin n)),
      MvPolynomial.monomial (∑ i ∈ s, d i.succ • Finsupp.single i.succ 1) (1 : R) =
        ∏ i ∈ s, MvPolynomial.X i.succ ^ d i.succ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, MvPolynomial.X_pow_eq_monomial, ← ih]
      calc MvPolynomial.monomial (d a.succ • Finsupp.single a.succ 1 +
              ∑ i ∈ s, d i.succ • Finsupp.single i.succ 1) (1 : R)
          = MvPolynomial.monomial (d a.succ • Finsupp.single a.succ 1) 1 *
              MvPolynomial.monomial (∑ i ∈ s, d i.succ • Finsupp.single i.succ 1) 1 := by
            rw [MvPolynomial.monomial_mul, mul_one]
        _ = MvPolynomial.monomial (Finsupp.single a.succ (d a.succ)) 1 *
              MvPolynomial.monomial (∑ i ∈ s, d i.succ • Finsupp.single i.succ 1) 1 := by
            simp [Finsupp.smul_single]
  have hprod_n : ∀ (s : Finset (Fin n)),
      MvPolynomial.monomial (∑ i ∈ s, d i.succ • Finsupp.single i 1) (1 : R) =
        ∏ i ∈ s, MvPolynomial.X i ^ d i.succ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, MvPolynomial.X_pow_eq_monomial, ← ih]
      calc MvPolynomial.monomial (d a.succ • Finsupp.single a 1 +
              ∑ i ∈ s, d i.succ • Finsupp.single i 1) (1 : R)
          = MvPolynomial.monomial (d a.succ • Finsupp.single a 1) 1 *
              MvPolynomial.monomial (∑ i ∈ s, d i.succ • Finsupp.single i 1) 1 := by
            rw [MvPolynomial.monomial_mul, mul_one]
        _ = MvPolynomial.monomial (Finsupp.single a (d a.succ)) 1 *
              MvPolynomial.monomial (∑ i ∈ s, d i.succ • Finsupp.single i 1) 1 := by
            simp [Finsupp.smul_single]
  have hmon : MvPolynomial.monomial d c =
      MvPolynomial.C c *
        (MvPolynomial.X 0 ^ d 0 * ∏ i : Fin n, MvPolynomial.X i.succ ^ d i.succ) := by
    calc MvPolynomial.monomial d c
        = MvPolynomial.monomial (d 0 • Finsupp.single 0 1 +
            ∑ i : Fin n, d i.succ • Finsupp.single i.succ 1) (c * 1) := by rw [← hd, mul_one]
      _ = MvPolynomial.monomial (d 0 • Finsupp.single 0 1) c *
            MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i.succ 1) 1 := by
          rw [MvPolynomial.monomial_mul]
      _ = MvPolynomial.C c *
            (MvPolynomial.monomial (d 0 • Finsupp.single (0 : Fin (n + 1)) 1) 1 *
              MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i.succ 1) 1) := by
          have hc_mul : MvPolynomial.monomial (d 0 • Finsupp.single (0 : Fin (n + 1)) 1) c =
              MvPolynomial.C c * MvPolynomial.monomial (d 0 • Finsupp.single (0 : Fin (n + 1)) 1) 1 := by
            rw [MvPolynomial.C_mul_monomial, mul_one]
          change MvPolynomial.monomial (d 0 • Finsupp.single (0 : Fin (n + 1)) 1) c * _ = _
          rw [hc_mul, mul_assoc]
      _ = MvPolynomial.C c *
            (MvPolynomial.X 0 ^ d 0 * ∏ i : Fin n, MvPolynomial.X i.succ ^ d i.succ) := by
          rw [hprod_succ Finset.univ, MvPolynomial.X_pow_eq_monomial]
          simp [Finsupp.smul_single]
  have hmon_rhs : MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) c =
      MvPolynomial.C c * ∏ i : Fin n, MvPolynomial.X i ^ d i.succ := by
    calc MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) c
        = MvPolynomial.C c *
            MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) 1 := by
          rw [MvPolynomial.C_mul_monomial, mul_one]
      _ = MvPolynomial.C c * ∏ i : Fin n, MvPolynomial.X i ^ d i.succ := by
          rw [hprod_n Finset.univ]
  have hprod_map :
      (∏ i : Fin n, MvPolynomial.finSuccEquiv R n (MvPolynomial.X i.succ ^ d i.succ)) =
        Polynomial.C (∏ i : Fin n, MvPolynomial.X i ^ d i.succ) := by
    simp only [map_pow, MvPolynomial.finSuccEquiv_X_succ]
    simp only [← map_pow, ← map_prod]
  rw [hmon, map_mul, map_mul, map_pow, map_prod, finSuccEquiv_C_eq, MvPolynomial.finSuccEquiv_X_zero,
      hprod_map, ← Polynomial.C_mul_X_pow_eq_monomial, hmon_rhs, map_mul, ← mul_assoc]
  ring

private lemma finSuccEquiv_eval_eq {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (x : Fin (n + 1) → R) :
    MvPolynomial.eval x f =
      Polynomial.eval (x 0) ((MvPolynomial.finSuccEquiv R n f).map
        (MvPolynomial.eval (fun i : Fin n => x i.succ))) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_C_eq]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.map_mul, Polynomial.eval_mul, hp]
    refine Fin.cases ?_ ?_ i
    · simp [MvPolynomial.finSuccEquiv_X_zero]
    · intro j
      simp [MvPolynomial.finSuccEquiv_X_succ]

private lemma finSuccEquiv_coeff_eq {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (k : ℕ) (μ : Fin n →₀ ℕ) :
    ((MvPolynomial.finSuccEquiv R n f).coeff k).coeff μ =
      f.coeff (k • Finsupp.single 0 1 + ∑ i : Fin n, μ i • Finsupp.single i.succ 1) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, MvPolynomial.coeff_sum]
  conv_rhs => rw [f.as_sum]
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [finSuccEquiv_monomial, Polynomial.coeff_monomial]
  split_ifs with h0
  · rw [MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    have hiff : (∑ i : Fin n, d i.succ • Finsupp.single i 1) = μ ↔
        d = k • Finsupp.single 0 1 + ∑ i : Fin n, μ i • Finsupp.single i.succ 1 := by
      constructor
      · intro heq
        ext j
        refine Fin.cases ?_ ?_ j
        · simp [Finsupp.coe_finsetSum, Finset.sum_apply, h0]
        · intro i
          have hi := congrFun (congrArg DFunLike.coe heq) i
          simpa [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Fin.succ_inj] using hi
      · intro heq
        ext i
        have hi := congrFun (congrArg DFunLike.coe heq) i.succ
        simpa [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Fin.succ_inj] using hi
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · rfl
  · rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_monomial]
    symm
    split_ifs with hEq
    · have h0' := congrFun (congrArg DFunLike.coe hEq) 0
      simp [Finsupp.coe_finsetSum, Finset.sum_apply] at h0'
      exact absurd h0' h0
    · rfl

private lemma finSuccEquiv_coeff_totalDegree_le {R : Type*} [CommRing R] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) R) (k : ℕ)
    (hk : (MvPolynomial.finSuccEquiv R n f).coeff k ≠ 0) :
    ((MvPolynomial.finSuccEquiv R n f).coeff k).totalDegree + k ≤ f.totalDegree := by
  have heq : (MvPolynomial.finSuccEquiv R n f).coeff k =
      ∑ d ∈ f.support.filter (fun d => d 0 = k),
        MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) (f.coeff d) := by
    conv_lhs => rw [f.as_sum, map_sum, Polynomial.finsetSum_coeff]
    simp only [finSuccEquiv_monomial, Polynomial.coeff_monomial]
    rw [Finset.sum_filter]
  have hne_set : (f.support.filter (fun d => d 0 = k)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at heq
    exact hk heq
  have hdeg_le : ∀ d ∈ f.support.filter (fun d => d 0 = k),
      (MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) (f.coeff d)).totalDegree + k ≤
        f.totalDegree := by
    intro d hd
    rw [Finset.mem_filter] at hd
    have hmon_le : (MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1)
        (f.coeff d)).totalDegree ≤ ∑ i : Fin n, d i.succ := by
      refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    have hd_tot := MvPolynomial.le_totalDegree hd.1
    rw [fin_succ_sum_deg, hd.2] at hd_tot
    omega
  rw [heq]
  have hsum_le : (∑ d ∈ f.support.filter (fun d => d 0 = k),
      MvPolynomial.monomial (∑ i : Fin n, d i.succ • Finsupp.single i 1) (f.coeff d)).totalDegree ≤
      f.totalDegree - k := by
    refine totalDegree_sum_le _ _ _ fun d hd => ?_
    have := hdeg_le d hd
    omega
  rcases hne_set with ⟨d₀, hd₀⟩
  have hk_le : k ≤ f.totalDegree := by
    have := hdeg_le d₀ hd₀
    omega
  omega

private lemma nullstellensatz_q_bound {R : Type*} [CommRing R] {n : ℕ}
    (P G q r : Polynomial (MvPolynomial (Fin n) R)) (t0 D' : ℕ)
    (hdiv : r + G * q = P) (hr_deg : r.natDegree ≤ t0)
    (hG_deg : G.natDegree = t0 + 1) (hG_lead : G.coeff (t0 + 1) = 1)
    (hG_coeff_deg : ∀ a : ℕ, (G.coeff a).totalDegree = 0)
    (hP_bound : ∀ k : ℕ, P.coeff k ≠ 0 → (P.coeff k).totalDegree + k ≤ t0 + D') :
    ∀ (m j : ℕ), q.natDegree + 1 ≤ j + m → q.coeff j ≠ 0 →
      (q.coeff j).totalDegree + j + (t0 + 1) ≤ t0 + D' := by
  intro m
  induction m with
  | zero =>
    intro j hjm hqj
    exact absurd (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < j)) hqj
  | succ m ih =>
    intro j hjm hqj
    by_cases hj_gt : q.natDegree < j
    · exact absurd (Polynomial.coeff_eq_zero_of_natDegree_lt hj_gt) hqj
    have hP_at : P.coeff (j + (t0 + 1)) = (G * q).coeff (j + (t0 + 1)) := by
      rw [← hdiv, Polynomial.coeff_add]
      have hr0 : r.coeff (j + (t0 + 1)) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hr0, zero_add]
    have hGq_expand : (G * q).coeff (j + (t0 + 1)) =
        q.coeff j + ∑ ab ∈ (Finset.antidiagonal (j + (t0 + 1))).erase (t0 + 1, j),
          G.coeff ab.1 * q.coeff ab.2 := by
      have hmem_anti : (t0 + 1, j) ∈ Finset.antidiagonal (j + (t0 + 1)) :=
        Finset.mem_antidiagonal.mpr (by ring)
      rw [Polynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmem_anti, hG_lead, one_mul]
    have hq_j_eq : q.coeff j = P.coeff (j + (t0 + 1)) -
        ∑ ab ∈ (Finset.antidiagonal (j + (t0 + 1))).erase (t0 + 1, j),
          G.coeff ab.1 * q.coeff ab.2 := by
      rw [hP_at, hGq_expand]; ring
    have hzero_erase : ∀ ab ∈ (Finset.antidiagonal (j + (t0 + 1))).erase (t0 + 1, j),
        G.coeff ab.1 * q.coeff ab.2 = 0 ∨
          (ab.1 ≤ t0 + 1 ∧ j < ab.2 ∧
            (G.coeff ab.1 * q.coeff ab.2).totalDegree + ab.2 + (t0 + 1) ≤ t0 + D') := by
      intro ab hab
      have hmem := Finset.mem_of_mem_erase hab
      have hne : ab ≠ (t0 + 1, j) := Finset.ne_of_mem_erase hab
      have hsum_ab : ab.1 + ab.2 = j + (t0 + 1) := Finset.mem_antidiagonal.mp hmem
      by_cases ha_gt : t0 + 1 < ab.1
      · left
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
      · have ha_le : ab.1 ≤ t0 + 1 := by omega
        have ha_lt : ab.1 < t0 + 1 := by
          by_contra ha_eq
          have : ab.1 = t0 + 1 := by omega
          exact hne (Prod.ext this (by omega))
        have hb_gt : j < ab.2 := by omega
        by_cases hqb : q.coeff ab.2 = 0
        · left; rw [hqb, mul_zero]
        · right
          have hq_ih := ih ab.2 (by omega) hqb
          have hmul_deg : (G.coeff ab.1 * q.coeff ab.2).totalDegree ≤ (q.coeff ab.2).totalDegree := by
            refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
            rw [hG_coeff_deg, zero_add]
          exact ⟨ha_le, hb_gt, by omega⟩
    by_cases hj_big : t0 + D' < j + (t0 + 1)
    · have hP0 : P.coeff (j + (t0 + 1)) = 0 := by
        by_contra hPne
        have := hP_bound (j + (t0 + 1)) hPne
        omega
      have hsum0 : ∑ ab ∈ (Finset.antidiagonal (j + (t0 + 1))).erase (t0 + 1, j),
          G.coeff ab.1 * q.coeff ab.2 = 0 := by
        refine Finset.sum_eq_zero fun ab hab => ?_
        rcases hzero_erase ab hab with h0 | ⟨_, hb_gt, hdeg_b⟩
        · exact h0
        · omega
      rw [hP0, hsum0, sub_zero] at hq_j_eq
      exact absurd hq_j_eq hqj
    · have hP_deg_j : (P.coeff (j + (t0 + 1))).totalDegree + j + (t0 + 1) ≤ t0 + D' := by
        by_cases hP0 : P.coeff (j + (t0 + 1)) = 0
        · simp [hP0]; omega
        · have := hP_bound (j + (t0 + 1)) hP0
          omega
      have hsum_deg : (∑ ab ∈ (Finset.antidiagonal (j + (t0 + 1))).erase (t0 + 1, j),
          G.coeff ab.1 * q.coeff ab.2).totalDegree ≤ t0 + D' - (j + (t0 + 1)) := by
        refine totalDegree_sum_le _ _ _ fun ab hab => ?_
        rcases hzero_erase ab hab with h0 | ⟨_, hb_gt, hdeg_b⟩
        · simp [h0]
        · omega
      rw [hq_j_eq]
      have hsub := totalDegree_sub_le (P.coeff (j + (t0 + 1)))
        (∑ ab ∈ (Finset.antidiagonal (j + (t0 + 1))).erase (t0 + 1, j),
          G.coeff ab.1 * q.coeff ab.2)
      omega

/-- **Alon's Combinatorial Nullstellensatz (`Fin n`):**
Over any integral domain `R`, if `f : MvPolynomial (Fin n) R` satisfies `f.totalDegree ≤ ∑ i, t i`,
`f.coeff (∑ i, t i • Finsupp.single i 1) ≠ 0`, and `∀ i, t i < (S i).card`, then there exists
`x : Fin n → R` with `∀ i, x i ∈ S i` and `MvPolynomial.eval x f ≠ 0`. -/
theorem combinatorial_nullstellensatz_fin {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) R) (t : Fin n → ℕ) (S : Fin n → Finset R),
      f.totalDegree ≤ ∑ i : Fin n, t i →
      f.coeff (∑ i : Fin n, t i • Finsupp.single i 1) ≠ 0 →
      (∀ i : Fin n, t i < (S i).card) →
      ∃ x : Fin n → R, (∀ i : Fin n, x i ∈ S i) ∧ MvPolynomial.eval x f ≠ 0
  | 0, f, t, S, _, hcoeff, _ => by
    have hf : f = MvPolynomial.C (f.coeff 0) := by
      ext d
      have hd : d = 0 := Subsingleton.elim d 0
      subst hd
      simp
    have hsum0 : (∑ i : Fin 0, t i • Finsupp.single i 1) = 0 := by simp
    rw [hsum0] at hcoeff
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    rw [hf, MvPolynomial.eval_C]
    exact hcoeff
  | n + 1, f, t, S, hdeg, hcoeff, hcard => by
    let e := MvPolynomial.finSuccEquiv R n
    let P := e f
    let t0 := t 0
    let t' : Fin n → ℕ := fun i => t i.succ
    let S' : Fin n → Finset R := fun i => S i.succ
    let D' := ∑ i : Fin n, t' i
    have hdeg_split : f.totalDegree ≤ t0 + D' := by
      simpa [t0, D', t', Fin.sum_univ_succ] using hdeg
    obtain ⟨S0', hS0'_sub, hS0'_card⟩ :=
      Finset.exists_subset_card_eq (Nat.succ_le_of_lt (hcard 0))
    let G0 : Polynomial R := ∏ s ∈ S0', (Polynomial.X - Polynomial.C s)
    have hG0_monic : G0.Monic := Polynomial.monic_prod_of_monic _ _
      (fun s _ => Polynomial.monic_X_sub_C s)
    have hG0_deg : G0.natDegree = t0 + 1 := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_sub_C s)]
      simp [hS0'_card, t0]
    let G : Polynomial (MvPolynomial (Fin n) R) := G0.map MvPolynomial.C
    have hG_monic : G.Monic := hG0_monic.map MvPolynomial.C
    have hG_deg : G.natDegree = t0 + 1 := by
      rw [hG0_monic.natDegree_map MvPolynomial.C, hG0_deg]
    let q := P /ₘ G
    let r := P %ₘ G
    have hdiv : r + G * q = P := Polynomial.modByMonic_add_div P G
    have hr_deg : r.natDegree ≤ t0 := by
      have hG_ne1 : G ≠ 1 := by
        intro h1
        rw [h1, Polynomial.natDegree_one] at hG_deg
        omega
      have hlt : (P %ₘ G).natDegree < G.natDegree :=
        Polynomial.natDegree_modByMonic_lt P hG_monic hG_ne1
      change (P %ₘ G).natDegree ≤ t0
      omega
    have hG_coeff_deg : ∀ a : ℕ, (G.coeff a).totalDegree = 0 := by
      intro a
      simp [G, Polynomial.coeff_map]
    have hG_lead : G.coeff (t0 + 1) = 1 := by
      rw [← hG_deg]; exact hG_monic.leadingCoeff
    have hP_bound : ∀ k : ℕ, P.coeff k ≠ 0 → (P.coeff k).totalDegree + k ≤ t0 + D' := by
      intro k hk
      exact le_trans (finSuccEquiv_coeff_totalDegree_le n f k hk) hdeg_split
    have hq_bound := nullstellensatz_q_bound P G q r t0 D' hdiv hr_deg hG_deg hG_lead
      hG_coeff_deg hP_bound
    -- Step B: Bound `(G * q).coeff t0` totalDegree strictly `< D'`.
    have hGq_deg : ((G * q).coeff t0).totalDegree < D' ∨ (G * q).coeff t0 = 0 := by
      by_cases h0 : (G * q).coeff t0 = 0
      · right; exact h0
      · left
        rw [Polynomial.coeff_mul]
        have hpos_D' : 0 < D' := by
          by_contra hD0
          have hD0' : D' = 0 := by omega
          have h_all0 : ∀ ab ∈ Finset.antidiagonal t0, G.coeff ab.1 * q.coeff ab.2 = 0 := by
            intro ab hab
            by_cases hqb : q.coeff ab.2 = 0
            · rw [hqb, mul_zero]
            · have hq_b := hq_bound (q.natDegree + 1) ab.2 (by omega) hqb
              omega
          exact h0 (by rw [Polynomial.coeff_mul]; exact Finset.sum_eq_zero h_all0)
        refine lt_of_le_of_lt (totalDegree_sum_le _ _ (D' - 1) fun ab hab => ?_) (by omega)
        by_cases hqb : q.coeff ab.2 = 0
        · simp [hqb]
        · have hq_b := hq_bound (q.natDegree + 1) ab.2 (by omega) hqb
          refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          rw [hG_coeff_deg, zero_add]
          omega
    -- Step C: Show `r.coeff t0` satisfies the IH hypotheses for `t'`, `S'`.
    let g := r.coeff t0
    have hg_deg : g.totalDegree ≤ D' := by
      have hr_eq : g = P.coeff t0 - (G * q).coeff t0 := by
        dsimp [g]
        rw [← hdiv, Polynomial.coeff_add]
        ring
      rw [hr_eq]
      have hP_t0 : (P.coeff t0).totalDegree ≤ D' := by
        by_cases hP0 : P.coeff t0 = 0
        · simp [hP0]
        · have := finSuccEquiv_coeff_totalDegree_le n f t0 hP0
          dsimp only [P, e, D', t0] at *
          omega
      refine le_trans (totalDegree_sub_le _ _) (max_le hP_t0 ?_)
      rcases hGq_deg with hlt | h0
      · omega
      · simp [h0]
    let μ' : Fin n →₀ ℕ := ∑ i : Fin n, t' i • Finsupp.single i 1
    have hμ'_deg : μ'.sum (fun _ e => e) = D' := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp [μ', D', Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    have hGq_coeff : ((G * q).coeff t0).coeff μ' = 0 := by
      rcases hGq_deg with hlt | h0
      · exact coeff_eq_zero_of_totalDegree_lt _ μ' (by omega)
      · simp [h0]
    have hg_coeff : g.coeff μ' ≠ 0 := by
      have hr_eq : g = P.coeff t0 - (G * q).coeff t0 := by
        dsimp [g]; rw [← hdiv, Polynomial.coeff_add]; ring
      rw [hr_eq, MvPolynomial.coeff_sub, hGq_coeff, sub_zero]
      dsimp only [P, e]
      rw [finSuccEquiv_coeff_eq]
      have hsum_eq : t0 • Finsupp.single (0 : Fin (n + 1)) 1 +
            ∑ i : Fin n, μ' i • Finsupp.single i.succ 1 =
          ∑ i : Fin (n + 1), t i • Finsupp.single i 1 := by
        rw [Fin.sum_univ_succ]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        have hμi : μ' i = t' i := by
          dsimp only [μ']
          rw [Finsupp.coe_finsetSum, Finset.sum_apply]
          simp [Finsupp.single_apply]
        rw [hμi]
      rw [hsum_eq]
      exact hcoeff
    -- Step D: Apply IH to `g` and find root-nonvanishing `s0 ∈ S0'`.
    obtain ⟨x', hx'_mem, hx'_ne⟩ :=
      combinatorial_nullstellensatz_fin n g t' S' hg_deg hg_coeff (fun i => hcard i.succ)
    let rUni : Polynomial R := r.map (MvPolynomial.eval x')
    have hrUni_coeff : rUni.coeff t0 = MvPolynomial.eval x' g := by
      simp [rUni, Polynomial.coeff_map, g]
    have hrUni_ne : rUni ≠ 0 := by
      intro hr0
      rw [hr0, Polynomial.coeff_zero] at hrUni_coeff
      exact hx'_ne hrUni_coeff.symm
    have hrUni_deg : rUni.natDegree ≤ t0 :=
      le_trans (Polynomial.natDegree_map_le) hr_deg
    have hnot_all_roots : ∃ s0 ∈ S0', rUni.eval s0 ≠ 0 := by
      by_contra h_all
      push Not at h_all
      have hsub_roots : S0' ⊆ rUni.roots.toFinset := by
        intro s hs
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hrUni_ne]
        exact h_all s hs
      have hcard_le : S0'.card ≤ rUni.roots.toFinset.card := Finset.card_le_card hsub_roots
      have hroots_le : rUni.roots.toFinset.card ≤ rUni.natDegree :=
        le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' rUni)
      omega
    rcases hnot_all_roots with ⟨s0, hs0_mem, hs0_ne⟩
    let x : Fin (n + 1) → R := Fin.cons s0 x'
    refine ⟨x, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact hS0'_sub hs0_mem
      · intro j; exact hx'_mem j
    · rw [finSuccEquiv_eval_eq]
      change Polynomial.eval (x 0) (P.map (MvPolynomial.eval (fun i : Fin n => x i.succ))) ≠ 0
      have hx_tail : (fun i : Fin n => x i.succ) = x' := by
        ext i; simp [x]
      have hx_zero : x 0 = s0 := rfl
      rw [hx_tail, hx_zero, ← hdiv, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.eval_add, Polynomial.eval_mul]
      have hG_eval : (G.map (MvPolynomial.eval x')).eval s0 = 0 := by
        have hG_eq : G.map (MvPolynomial.eval x') = G0 := by
          ext k
          simp [G, Polynomial.coeff_map]
        rw [hG_eq, Polynomial.eval_prod]
        exact Finset.prod_eq_zero hs0_mem (by simp)
      rw [hG_eval, zero_mul, add_zero]
      exact hs0_ne

/-- **Alon's Combinatorial Nullstellensatz (general `[Fintype ι] [DecidableEq ι]`):** -/
theorem combinatorial_nullstellensatz {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [IsDomain R] [DecidableEq R]
    (f : MvPolynomial ι R) (t : ι → ℕ) (S : ι → Finset R)
    (hdeg : f.totalDegree ≤ ∑ i : ι, t i)
    (hcoeff : f.coeff (∑ i : ι, t i • Finsupp.single i 1) ≠ 0)
    (hcard : ∀ i : ι, t i < (S i).card) :
    ∃ x : ι → R, (∀ i : ι, x i ∈ S i) ∧ MvPolynomial.eval x f ≠ 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let f' : MvPolynomial (Fin (Fintype.card ι)) R := MvPolynomial.rename e f
  let t' : Fin (Fintype.card ι) → ℕ := t ∘ e.symm
  let S' : Fin (Fintype.card ι) → Finset R := S ∘ e.symm
  have hdeg' : f'.totalDegree ≤ ∑ j : Fin (Fintype.card ι), t' j := by
    refine le_trans (MvPolynomial.totalDegree_rename_le e f) ?_
    calc f.totalDegree ≤ ∑ i : ι, t i := hdeg
      _ = ∑ j : Fin (Fintype.card ι), t' j := (Equiv.sum_comp e.symm t).symm
  have hmon_map : Finsupp.mapDomain e (∑ i : ι, t i • Finsupp.single i 1) =
      ∑ j : Fin (Fintype.card ι), t' j • Finsupp.single j 1 := by
    ext j
    have hLval : (Finsupp.mapDomain e (∑ i : ι, t i • Finsupp.single i 1)) j = t (e.symm j) := by
      conv_lhs => rw [← e.apply_symm_apply j, Finsupp.mapDomain_apply e.injective]
      simp [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    have hRval : (∑ k : Fin (Fintype.card ι), t' k • Finsupp.single k 1) j = t (e.symm j) := by
      simp [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, t']
    exact hLval.trans hRval.symm
  have hcoeff' : f'.coeff (∑ j : Fin (Fintype.card ι), t' j • Finsupp.single j 1) ≠ 0 := by
    rw [← hmon_map]
    dsimp only [f']
    have hL : (MvPolynomial.rename e f).coeff
        (Finsupp.mapDomain e (∑ i : ι, t i • Finsupp.single i 1)) =
        ∑ d ∈ f.support, (MvPolynomial.rename e (MvPolynomial.monomial d (f.coeff d))).coeff
          (Finsupp.mapDomain e (∑ i : ι, t i • Finsupp.single i 1)) := by
      conv_lhs => rw [f.as_sum, map_sum, MvPolynomial.coeff_sum]
    have hR : f.coeff (∑ i : ι, t i • Finsupp.single i 1) =
        ∑ d ∈ f.support, (MvPolynomial.monomial d (f.coeff d)).coeff
          (∑ i : ι, t i • Finsupp.single i 1) := by
      conv_lhs => rw [f.as_sum, MvPolynomial.coeff_sum]
    rw [hL]
    have hsame : ∀ d ∈ f.support,
        (MvPolynomial.rename e (MvPolynomial.monomial d (f.coeff d))).coeff
          (Finsupp.mapDomain e (∑ i : ι, t i • Finsupp.single i 1)) =
          (MvPolynomial.monomial d (f.coeff d)).coeff (∑ i : ι, t i • Finsupp.single i 1) := by
      intro d _
      rw [MvPolynomial.rename_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd ((Finsupp.mapDomain_injective e.injective) h1) h2
      · exact absurd (congrArg (Finsupp.mapDomain e) h2) h1
      · rfl
    rw [Finset.sum_congr rfl hsame, ← hR]
    exact hcoeff
  obtain ⟨x', hx'_mem, hx'_ne⟩ :=
    combinatorial_nullstellensatz_fin (Fintype.card ι) f' t' S' hdeg' hcoeff' (fun j => hcard (e.symm j))
  refine ⟨x' ∘ e, fun i => ?_, ?_⟩
  · simpa [S'] using hx'_mem (e i)
  · simpa [f', MvPolynomial.eval_rename] using hx'_ne

end Nullstellensatz

/-! ## Section 2: Cauchy–Davenport & Erdős–Heilbronn via Nullstellensatz -/

section SumsetsZMod

private lemma prime_dvd_factorial_le {p : ℕ} (hp : p.Prime) :
    ∀ n : ℕ, p ∣ n.factorial → p ≤ n
  | 0, h => absurd h hp.not_dvd_one
  | n + 1, h => by
    rw [Nat.factorial_succ, hp.dvd_mul] at h
    rcases h with h1 | h2
    · exact Nat.le_of_dvd (Nat.succ_pos n) h1
    · exact le_trans (prime_dvd_factorial_le hp n h2) (Nat.le_succ n)

private lemma zmod_choose_ne_zero {p : ℕ} [Fact p.Prime] {a b : ℕ} (hab : a + b < p) :
    (((a + b).choose a : ℕ) : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have hmul : (a + b).choose a * (a.factorial * b.factorial) = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rw [Nat.add_sub_cancel_left, mul_assoc] at h
    exact h
  have hdvd : p ∣ (a + b).factorial := dvd_trans h0 ⟨a.factorial * b.factorial, hmul.symm⟩
  have hle : p ≤ a + b := prime_dvd_factorial_le Fact.out (a + b) hdvd
  omega

private lemma erdos_heilbronn_catalan_ne_zero {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 2 * k < p) (hk1 : 1 ≤ k) :
    ((((2 * k).choose k : ℕ) : ZMod p) - (((2 * k).choose (k - 1) : ℕ) : ZMod p)) ≠ 0 := by
  rcases k with _ | k
  · omega
  · have hpos : 0 < (k + 1).factorial * (k + 2).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    have hmul_eq : (k + 2) * (2 * (k + 1)).choose k = (k + 1) * (2 * (k + 1)).choose (k + 1) := by
      apply Nat.mul_right_cancel hpos
      have h1 : (2 * (k + 1)).choose k * (k.factorial * (k + 2).factorial) = (2 * (k + 1)).factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * (k + 1) by omega)
        rw [show 2 * (k + 1) - k = k + 2 by omega, mul_assoc] at h
        exact h
      have h2 : (2 * (k + 1)).choose (k + 1) * ((k + 1).factorial * (k + 1).factorial) =
          (2 * (k + 1)).factorial := by
        have h := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ 2 * (k + 1) by omega)
        rw [show 2 * (k + 1) - (k + 1) = k + 1 by omega, mul_assoc] at h
        exact h
      calc (k + 2) * (2 * (k + 1)).choose k * ((k + 1).factorial * (k + 2).factorial)
          = (k + 2) * (k + 1) * ((2 * (k + 1)).choose k * (k.factorial * (k + 2).factorial)) := by
            rw [Nat.factorial_succ k]; ring
        _ = (k + 2) * (k + 1) * (2 * (k + 1)).factorial := by rw [h1]
        _ = (k + 2) * (k + 1) * ((2 * (k + 1)).choose (k + 1) *
              ((k + 1).factorial * (k + 1).factorial)) := by rw [h2]
        _ = (k + 1) * (2 * (k + 1)).choose (k + 1) * ((k + 1).factorial * (k + 2).factorial) := by
            rw [Nat.factorial_succ (k + 1)]; ring
    have hle_ch : (2 * (k + 1)).choose k ≤ (2 * (k + 1)).choose (k + 1) := by nlinarith
    have hcat : (k + 2) * ((2 * (k + 1)).choose (k + 1) - (2 * (k + 1)).choose k) =
        (2 * (k + 1)).choose (k + 1) := by
      zify [hle_ch]; linarith
    intro h0
    have h0' : ((((2 * (k + 1)).choose (k + 1) - (2 * (k + 1)).choose k : ℕ) : ZMod p)) = 0 := by
      rw [Nat.cast_sub hle_ch]
      exact h0
    have hcat_z : ((k + 2 : ℕ) : ZMod p) *
        ((((2 * (k + 1)).choose (k + 1) - (2 * (k + 1)).choose k : ℕ) : ZMod p)) =
        (((2 * (k + 1)).choose (k + 1) : ℕ) : ZMod p) := by
      simpa [Nat.cast_mul] using congrArg (Nat.cast : ℕ → ZMod p) hcat
    rw [h0', mul_zero] at hcat_z
    have hnz := zmod_choose_ne_zero (p := p) (a := k + 1) (b := k + 1) (by omega)
    rw [show k + 1 + (k + 1) = 2 * (k + 1) by omega] at hnz
    exact hnz hcat_z.symm

private lemma prod_lin_sub_top_deg {σ R : Type*} [CommRing R] {α : Type*}
    (s : Finset α) (g : α → R) (p : MvPolynomial σ R) (hp : p.totalDegree ≤ 1) :
    (∏ a ∈ s, (p - MvPolynomial.C (g a)) - p ^ s.card).totalDegree < s.card ∨ s = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => right; rfl
  | @insert a s ha ih =>
    left
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
    rcases ih with hlt | rfl
    · have hdecomp :
          (p - MvPolynomial.C (g a)) * ∏ b ∈ s, (p - MvPolynomial.C (g b)) - p ^ s.card * p =
            p * (∏ b ∈ s, (p - MvPolynomial.C (g b)) - p ^ s.card) -
              MvPolynomial.C (g a) * ∏ b ∈ s, (p - MvPolynomial.C (g b)) := by ring
      rw [hdecomp]
      have h1 : (p * (∏ b ∈ s, (p - MvPolynomial.C (g b)) - p ^ s.card)).totalDegree ≤ s.card := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        omega
      have hprod_deg : (∏ b ∈ s, (p - MvPolynomial.C (g b))).totalDegree ≤ s.card := by
        refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
        have hsum_le : (∑ b ∈ s, (p - MvPolynomial.C (g b)).totalDegree) ≤ ∑ _b ∈ s, 1 := by
          refine Finset.sum_le_sum fun b _ => ?_
          exact le_trans (totalDegree_sub_le p (MvPolynomial.C (g b))) (by simp [hp])
        simpa using hsum_le
      have h2 : (MvPolynomial.C (g a) * ∏ b ∈ s, (p - MvPolynomial.C (g b))).totalDegree ≤ s.card := by
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        simpa using hprod_deg
      refine lt_of_le_of_lt (totalDegree_sub_le _ _) (max_lt (by omega) (by omega))
    · simp

private lemma coeff_X0_add_X1_pow {R : Type*} [CommRing R] (a b : ℕ) :
    ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ^ (a + b)).coeff
      (a • Finsupp.single 0 1 + b • Finsupp.single 1 1) = ((a + b).choose a : R) := by
  rw [add_pow, MvPolynomial.coeff_sum]
  have hsingle : ∀ k ∈ Finset.range (a + b + 1),
      (MvPolynomial.X (0 : Fin 2) ^ k * MvPolynomial.X 1 ^ (a + b - k) *
        (((a + b).choose k : ℕ) : MvPolynomial (Fin 2) R)).coeff
          (a • Finsupp.single 0 1 + b • Finsupp.single 1 1) =
        if k = a then ((a + b).choose a : R) else 0 := by
    intro k hk
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
        MvPolynomial.monomial_mul, one_mul, ← map_natCast MvPolynomial.C ((a + b).choose k),
        mul_comm _ (MvPolynomial.C _), MvPolynomial.C_mul_monomial, mul_one,
        MvPolynomial.coeff_monomial]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hiff : Finsupp.single (0 : Fin 2) k + Finsupp.single 1 (a + b - k) =
        Finsupp.single 0 a + Finsupp.single 1 b ↔ k = a := by
      constructor
      · intro h
        have h0 := congrFun (congrArg DFunLike.coe h) 0
        simpa [Finsupp.single_apply] using h0
      · intro h; subst h; simp
    split_ifs with h1 h2 h2
    · subst h2; rfl
    · exact absurd (hiff.mp h1) h2
    · exact absurd (hiff.mpr h2) h1
    · rfl
  rw [Finset.sum_congr rfl hsingle]
  simp [Nat.lt_succ_of_le (Nat.le_add_right a b)]

/-- **Cauchy–Davenport Theorem (`ZMod p`):**
For prime `p` and nonempty `A, B : Finset (ZMod p)`,
`min p (A.card + B.card - 1) ≤ ((A ×ˢ B).image (fun x => x.1 + x.2)).card`. -/
theorem cauchy_davenport {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ ((A ×ˢ B).image (fun x => x.1 + x.2)).card := by
  let C := (A ×ˢ B).image (fun x => x.1 + x.2)
  by_cases hbig : p ≤ A.card + B.card - 1
  · suffices hC : C = Finset.univ by
      change min p (A.card + B.card - 1) ≤ C.card
      rw [hC, Finset.card_univ, ZMod.card]
      exact min_le_left _ _
    rw [Finset.eq_univ_iff_forall]
    intro c
    let B' := B.image (fun b => c - b)
    have hB'_card : B'.card = B.card :=
      Finset.card_image_of_injective B (fun x y h => by linear_combination -h)
    have hinter : (A ∩ B').Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hdisj : Disjoint A B' := Finset.disjoint_iff_inter_eq_empty.mpr hemp
      have hle := Finset.card_le_univ (A ∪ B')
      rw [Finset.card_union_of_disjoint hdisj, hB'_card, ZMod.card] at hle
      have := hA.card_pos
      have := hB.card_pos
      omega
    rcases hinter with ⟨a, ha⟩
    rw [Finset.mem_inter, Finset.mem_image] at ha
    rcases ha with ⟨haA, b, hbB, hba⟩
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨haA, hbB⟩, by linear_combination -hba⟩
  · have hlt : A.card + B.card - 1 < p := by omega
    by_contra hC_lt
    have hC_le : C.card ≤ A.card + B.card - 2 := by
      have hmin : min p (A.card + B.card - 1) = A.card + B.card - 1 := min_eq_right (by omega)
      change ¬ min p (A.card + B.card - 1) ≤ C.card at hC_lt
      rw [hmin] at hC_lt
      omega
    have hA_pos : 1 ≤ A.card := hA.card_pos
    have hB_pos : 1 ≤ B.card := hB.card_pos
    let t0 := A.card - 1
    let t1 := B.card - 1
    let r := t0 + t1 - C.card
    let f : MvPolynomial (Fin 2) (ZMod p) :=
      (MvPolynomial.X 0 + MvPolynomial.X 1) ^ r *
        ∏ c ∈ C, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c)
    let t : Fin 2 → ℕ := ![t0, t1]
    let S : Fin 2 → Finset (ZMod p) := ![A, B]
    have hsum_t : (∑ i : Fin 2, t i) = t0 + t1 := by simp [t]
    have hdeg_lin : (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 :=
      le_trans (MvPolynomial.totalDegree_add _ _) (by simp)
    have hdeg_f : f.totalDegree ≤ ∑ i : Fin 2, t i := by
      rw [hsum_t]
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r).totalDegree ≤ r := by
        refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
        nlinarith [hdeg_lin]
      have hsum_le : (∑ c ∈ C, (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 - MvPolynomial.C c).totalDegree) ≤
          ∑ _c ∈ C, 1 :=
        Finset.sum_le_sum fun c _ => le_trans (totalDegree_sub_le _ _) (by simp [hdeg_lin])
      have h2 : (∏ c ∈ C, (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 - MvPolynomial.C c)).totalDegree ≤ C.card := by
        refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
        simpa using hsum_le
      omega
    let μ := ∑ i : Fin 2, t i • Finsupp.single i 1
    have hμ_eq : μ = t0 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1 := by
      simp [μ, t, Fin.sum_univ_two]
    have hμ_deg : μ.sum (fun _ e => e) = t0 + t1 := by
      rw [hμ_eq, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp [Finsupp.single_apply, Fin.sum_univ_two]
    have hdiff_deg : (f - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (t0 + t1)).totalDegree < t0 + t1 ∨
        f = (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (t0 + t1) := by
      rcases prod_lin_sub_top_deg C id (MvPolynomial.X 0 + MvPolynomial.X 1) hdeg_lin with hlt_C | hC_emp
      · left
        have hdecomp : f - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (t0 + t1) =
            (MvPolynomial.X 0 + MvPolynomial.X 1) ^ r *
              (∏ c ∈ C, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) -
                (MvPolynomial.X 0 + MvPolynomial.X 1) ^ C.card) := by
          dsimp [f]
          rw [mul_sub, ← pow_add, show r + C.card = t0 + t1 by dsimp only [r, t0, t1]; omega]
        rw [hdecomp]
        refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
        have h1 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r).totalDegree ≤ r := by
          refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
          nlinarith [hdeg_lin]
        have hrC : r + C.card = t0 + t1 := by dsimp only [r, t0, t1]; omega
        calc ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r).totalDegree +
              (∏ c ∈ C, (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 - MvPolynomial.C c) -
                (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1) ^ C.card).totalDegree
            < r + C.card := Nat.add_lt_add_of_le_of_lt h1 hlt_C
          _ = t0 + t1 := hrC
      · right
        dsimp [f, r]
        rw [hC_emp]
        simp
    have hcoeff_eq : f.coeff μ = ((t0 + t1).choose t0 : ZMod p) := by
      have hpow : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^
          (t0 + t1)).coeff μ = ((t0 + t1).choose t0 : ZMod p) := by
        rw [hμ_eq]
        exact coeff_X0_add_X1_pow t0 t1
      rcases hdiff_deg with hlt_d | heq_d
      · have hc0 := coeff_eq_zero_of_totalDegree_lt
          (f - (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (t0 + t1)) μ (by omega)
        rw [MvPolynomial.coeff_sub, sub_eq_zero] at hc0
        rw [hc0, hpow]
      · rw [heq_d, hpow]
    have hcoeff_ne : f.coeff μ ≠ 0 := by
      rw [hcoeff_eq]
      exact zmod_choose_ne_zero (by dsimp only [t0, t1]; omega)
    obtain ⟨x, hx_mem, hx_ne⟩ :=
      combinatorial_nullstellensatz_fin 2 f t S hdeg_f hcoeff_ne (fun i => by
        fin_cases i
        · dsimp only [S, t, t0]; simp; omega
        · dsimp only [S, t, t1]; simp; omega)
    have hx0 : x 0 ∈ A := by simpa [S] using hx_mem 0
    have hx1 : x 1 ∈ B := by simpa [S] using hx_mem 1
    have hmem_C : x 0 + x 1 ∈ C := Finset.mem_image.mpr ⟨(x 0, x 1), Finset.mem_product.mpr ⟨hx0, hx1⟩, rfl⟩
    have heval0 : MvPolynomial.eval x f = 0 := by
      dsimp [f]
      rw [map_mul, map_prod]
      have hprod0 : (∏ c ∈ C, MvPolynomial.eval x (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c)) = 0 :=
        Finset.prod_eq_zero hmem_C (by simp)
      rw [hprod0, mul_zero]
    exact hx_ne heval0

/-- **Erdős–Heilbronn Restricted Sumset Bound (`ZMod p`):**
For prime `p` and `A : Finset (ZMod p)`,
`min p (2 * A.card - 3) ≤ (((A ×ˢ A).filter (fun x => x.1 ≠ x.2)).image (fun x => x.1 + x.2)).card`. -/
theorem erdos_heilbronn {p : ℕ} [Fact p.Prime] (A : Finset (ZMod p)) :
    min p (2 * A.card - 3) ≤
      (((A ×ˢ A).filter (fun x => x.1 ≠ x.2)).image (fun x => x.1 + x.2)).card := by
  let S_sum := ((A ×ˢ A).filter (fun x => x.1 ≠ x.2)).image (fun x => x.1 + x.2)
  by_cases hsmall : A.card ≤ 2
  · by_cases h1 : A.card ≤ 1
    · have : 2 * A.card - 3 = 0 := by omega
      rw [this, min_zero]
      exact Nat.zero_le _
    · have hA2 : A.card = 2 := by omega
      rcases Finset.card_eq_two.mp hA2 with ⟨a, b, hab, rfl⟩
      have hmem : a + b ∈ S_sum := Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by simp, by simp⟩, hab⟩, rfl⟩
      have hpos : 1 ≤ S_sum.card := Finset.card_pos.mpr ⟨a + b, hmem⟩
      have hmin : min p (2 * ({a, b} : Finset (ZMod p)).card - 3) ≤ 1 := by
        rw [hA2]
        exact min_le_right _ _
      exact le_trans hmin hpos
  · have hA3 : 3 ≤ A.card := by omega
    by_cases hbig : p ≤ 2 * A.card - 3
    · have hp3 : 3 ≤ p := by
        have hAp : A.card ≤ p := by simpa [ZMod.card] using Finset.card_le_univ A
        omega
      suffices hU : S_sum = Finset.univ by
        change min p (2 * A.card - 3) ≤ S_sum.card
        rw [hU, Finset.card_univ, ZMod.card]
        exact min_le_left _ _
      rw [Finset.eq_univ_iff_forall]
      intro c
      let B' := A.image (fun b => c - b)
      have hB'_card : B'.card = A.card :=
        Finset.card_image_of_injective A (fun x y h => by linear_combination -h)
      have hinter_card : 3 ≤ (A ∩ B').card := by
        have hunion := Finset.card_union_add_card_inter A B'
        have hle := Finset.card_le_univ (A ∪ B')
        rw [ZMod.card] at hle
        omega
      let bad : Finset (ZMod p) := (A ∩ B').filter (fun a => a = c - a)
      have hbad_le : bad.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        have h2 : (2 : ZMod p) ≠ 0 := by
          intro h20
          rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from rfl, ZMod.natCast_eq_zero_iff] at h20
          have := Nat.le_of_dvd (by omega) h20
          omega
        apply mul_left_cancel₀ h2
        linear_combination ha.2 - hb.2
      have hgood : ((A ∩ B') \ bad).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.card_sdiff_add_card_inter (A ∩ B') bad
        have hsub : bad ⊆ A ∩ B' := Finset.filter_subset _ _
        rw [Finset.inter_eq_right.mpr hsub] at this
        omega
      rcases hgood with ⟨a, ha⟩
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      rcases ha with ⟨ha_inter, hnot_bad⟩
      have haA : a ∈ A := (Finset.mem_inter.mp ha_inter).1
      have haB' : a ∈ B' := (Finset.mem_inter.mp ha_inter).2
      have hne : a ≠ c - a := fun heq => hnot_bad ⟨ha_inter, heq⟩
      rw [Finset.mem_image] at haB'
      rcases haB' with ⟨b, hbA, hba⟩
      have hne_ab : a ≠ b := by
        intro heq
        apply hne
        rw [← heq] at hba
        exact hba.symm
      exact Finset.mem_image.mpr ⟨(a, b),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haA, hbA⟩, hne_ab⟩,
        by linear_combination -hba⟩
    · have hlt : 2 * A.card - 3 < p := by omega
      by_contra hS_lt
      have hS_le : S_sum.card ≤ 2 * A.card - 4 := by
        have hmin : min p (2 * A.card - 3) = 2 * A.card - 3 := min_eq_right (by omega)
        change ¬ min p (2 * A.card - 3) ≤ S_sum.card at hS_lt
        rw [hmin] at hS_lt
        omega
      let t0 := A.card - 1
      let t1 := A.card - 2
      let r := (2 * A.card - 4) - S_sum.card
      let f : MvPolynomial (Fin 2) (ZMod p) :=
        (MvPolynomial.X 0 - MvPolynomial.X 1) *
          ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ r *
            ∏ c ∈ S_sum, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c))
      let t : Fin 2 → ℕ := ![t0, t1]
      let S : Fin 2 → Finset (ZMod p) := ![A, A]
      have hsum_t : (∑ i : Fin 2, t i) = t0 + t1 := by simp [t]
      have hdeg_lin : (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 :=
        le_trans (MvPolynomial.totalDegree_add _ _) (by simp)
      have hdeg_sub : (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X 1 :
          MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 :=
        le_trans (totalDegree_sub_le _ _) (by simp)
      have hdeg_f : f.totalDegree ≤ ∑ i : Fin 2, t i := by
        rw [hsum_t]
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        have hrest : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1) ^ r *
            ∏ c ∈ S_sum, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c)).totalDegree ≤
            r + S_sum.card := by
          refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
          have h1 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r).totalDegree ≤ r := by
            refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
            nlinarith [hdeg_lin]
          have hsum_le : (∑ c ∈ S_sum, (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 - MvPolynomial.C c).totalDegree) ≤
              ∑ _c ∈ S_sum, 1 :=
            Finset.sum_le_sum fun c _ => le_trans (totalDegree_sub_le _ _) (by simp [hdeg_lin])
          have h2 : (∏ c ∈ S_sum, (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 - MvPolynomial.C c)).totalDegree ≤
              S_sum.card := by
            refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
            simpa using hsum_le
          dsimp only [r, t0, t1] at *
          omega
        dsimp only [r, t0, t1] at *
        omega
      let μ := ∑ i : Fin 2, t i • Finsupp.single i 1
      have hμ_eq : μ = t0 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1 := by
        simp [μ, t, Fin.sum_univ_two]
      have hμ_deg : μ.sum (fun _ e => e) = t0 + t1 := by
        rw [hμ_eq, Finsupp.sum_fintype _ _ (fun _ => rfl)]
        simp [Fin.sum_univ_two]
      let topPoly : MvPolynomial (Fin 2) (ZMod p) :=
        (MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ (2 * t1)
      have hrS : r + S_sum.card = 2 * t1 := by
        dsimp only [r, t1]
        omega
      have hdiff_deg : (f - topPoly).totalDegree < t0 + t1 ∨ f = topPoly := by
        rcases prod_lin_sub_top_deg S_sum id (MvPolynomial.X 0 + MvPolynomial.X 1) hdeg_lin with hlt_S | hS_emp
        · left
          have hdecomp : f - topPoly = (MvPolynomial.X 0 - MvPolynomial.X 1) *
              ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ r *
                (∏ c ∈ S_sum, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) -
                  (MvPolynomial.X 0 + MvPolynomial.X 1) ^ S_sum.card)) := by
            dsimp [f, topPoly]
            rw [mul_sub, ← pow_add, hrS]
            ring
          rw [hdecomp]
          have h1 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r).totalDegree ≤ r := by
            refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
            nlinarith [hdeg_lin]
          refine lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) ?_
          have h2 := MvPolynomial.totalDegree_mul
            ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r)
            (∏ c ∈ S_sum, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) -
              (MvPolynomial.X 0 + MvPolynomial.X 1) ^ S_sum.card)
          have h3 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ r *
              (∏ c ∈ S_sum, (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c) -
                (MvPolynomial.X 0 + MvPolynomial.X 1) ^ S_sum.card)).totalDegree < 2 * t1 := by
            refine lt_of_le_of_lt h2 ?_
            calc _ < r + S_sum.card := Nat.add_lt_add_of_le_of_lt h1 hlt_S
              _ = 2 * t1 := hrS
          have hsum_t01 : 1 + (2 * t1) = t0 + t1 := by dsimp only [t0, t1]; omega
          omega
        · right
          dsimp [f, topPoly, r]
          rw [hS_emp]
          simp [show 2 * A.card - 4 = 2 * t1 by dsimp only [t1]; omega]
      have htop_coeff : topPoly.coeff μ =
          (((2 * t1).choose t1 : ℕ) : ZMod p) - (((2 * t1).choose (t1 - 1) : ℕ) : ZMod p) := by
        have ht0_succ : t0 = t1 + 1 := by dsimp only [t0, t1]; omega
        have hmul0 : ∀ (g : MvPolynomial (Fin 2) (ZMod p)),
            (MvPolynomial.X 0 * g).coeff (t0 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1) =
              g.coeff (t1 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1) := by
          intro g
          conv_lhs => rw [g.as_sum, Finset.mul_sum, MvPolynomial.coeff_sum]
          conv_rhs => rw [g.as_sum, MvPolynomial.coeff_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
              MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
          have hiff : Finsupp.single (0 : Fin 2) 1 + d = t0 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1 ↔
              d = t1 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1 := by
            constructor
            · intro h; ext i; have hi := congrFun (congrArg DFunLike.coe h) i
              fin_cases i <;> simp [ht0_succ] at hi ⊢ <;> omega
            · intro h; rw [h]; ext i
              fin_cases i
              · simp [ht0_succ]; omega
              · simp [ht0_succ]
          split_ifs with h1 h2 h2 <;> simp_all
        have hmul1 : ∀ (g : MvPolynomial (Fin 2) (ZMod p)),
            (MvPolynomial.X 1 * g).coeff (t0 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1) =
              if t1 = 0 then 0 else g.coeff (t0 • Finsupp.single 0 1 + (t1 - 1) • Finsupp.single 1 1) := by
          intro g
          by_cases ht1z : t1 = 0
          · simp only [ht1z, ↓reduceIte, zero_smul, add_zero]
            conv_lhs => rw [g.as_sum, Finset.mul_sum, MvPolynomial.coeff_sum]
            refine Finset.sum_eq_zero fun d _ => ?_
            rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, MvPolynomial.coeff_monomial]
            split_ifs with heq
            · have h1 := congrFun (congrArg DFunLike.coe heq) 1
              simp at h1
            · rfl
          · simp only [ht1z, ↓reduceIte]
            conv_lhs => rw [g.as_sum, Finset.mul_sum, MvPolynomial.coeff_sum]
            conv_rhs => rw [g.as_sum, MvPolynomial.coeff_sum]
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
                MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
            have hiff : Finsupp.single (1 : Fin 2) 1 + d = t0 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1 ↔
                d = t0 • Finsupp.single 0 1 + (t1 - 1) • Finsupp.single 1 1 := by
              constructor
              · intro h; ext i; have hi := congrFun (congrArg DFunLike.coe h) i
                fin_cases i <;> simp at hi ⊢ <;> omega
              · intro h; rw [h]; ext i
                fin_cases i
                · simp
                · simp; omega
            split_ifs with h1 h2 h2 <;> simp_all
        dsimp [topPoly]
        rw [sub_mul, MvPolynomial.coeff_sub, hμ_eq, hmul0, hmul1]
        have hc0 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ (2 * t1)).coeff
            (t1 • Finsupp.single 0 1 + t1 • Finsupp.single 1 1) = (((2 * t1).choose t1 : ℕ) : ZMod p) := by
          rw [show 2 * t1 = t1 + t1 by ring]
          exact coeff_X0_add_X1_pow t1 t1
        rw [hc0]
        have ht1_pos : t1 ≠ 0 := by dsimp only [t1]; omega
        simp only [ht1_pos, ↓reduceIte]
        have h2t1 : 2 * t1 = t0 + (t1 - 1) := by dsimp only [t0, t1]; omega
        have hc1 : ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod p)) ^ (2 * t1)).coeff
            (t0 • Finsupp.single 0 1 + (t1 - 1) • Finsupp.single 1 1) =
            (((2 * t1).choose (t1 - 1) : ℕ) : ZMod p) := by
          rw [h2t1, coeff_X0_add_X1_pow t0 (t1 - 1)]
          have hsymm : (t0 + (t1 - 1)).choose t0 = (t0 + (t1 - 1)).choose (t1 - 1) := by
            have ht0_le : t0 ≤ t0 + (t1 - 1) := Nat.le_add_right _ _
            have hsym := Nat.choose_symm ht0_le
            rw [Nat.add_sub_cancel_left] at hsym
            exact hsym.symm
          rw [hsymm]
        rw [hc1]
      have hcoeff_eq : f.coeff μ = topPoly.coeff μ := by
        rcases hdiff_deg with hlt_d | heq_d
        · have hc0 := coeff_eq_zero_of_totalDegree_lt (f - topPoly) μ (by omega)
          rw [MvPolynomial.coeff_sub, sub_eq_zero] at hc0
          exact hc0
        · rw [heq_d]
      have hcoeff_ne : f.coeff μ ≠ 0 := by
        rw [hcoeff_eq, htop_coeff]
        exact erdos_heilbronn_catalan_ne_zero (by dsimp only [t1]; omega) (by dsimp only [t1]; omega)
      obtain ⟨x, hx_mem, hx_ne⟩ :=
        combinatorial_nullstellensatz_fin 2 f t S hdeg_f hcoeff_ne (fun i => by
          fin_cases i
          · change t0 < A.card; dsimp only [t0]; omega
          · change t1 < A.card; dsimp only [t1]; omega)
      have hx0 : x 0 ∈ A := by simpa [S] using hx_mem 0
      have hx1 : x 1 ∈ A := by simpa [S] using hx_mem 1
      have hne_01 : x 0 ≠ x 1 := by
        intro heq
        apply hx_ne
        simp [f, heq]
      have hmem_S : x 0 + x 1 ∈ S_sum := Finset.mem_image.mpr ⟨(x 0, x 1),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx0, hx1⟩, hne_01⟩, rfl⟩
      apply hx_ne
      dsimp [f]
      rw [map_mul, map_mul, map_prod]
      have hprod0 : (∏ c ∈ S_sum, MvPolynomial.eval x (MvPolynomial.X 0 + MvPolynomial.X 1 - MvPolynomial.C c)) = 0 :=
        Finset.prod_eq_zero hmem_S (by simp)
      rw [hprod0, mul_zero, mul_zero]

end SumsetsZMod

/-! ## Section 3: Schwartz–Zippel Lemma -/

section SchwartzZippel

/-- **Schwartz–Zippel Lemma (`MvPolynomial (Fin n) R`):**
For any nonzero polynomial `f : MvPolynomial (Fin n) R` over an integral domain `R` and any
nonempty finite set `S : Finset R`, the number of roots in `S ^ n` is at most
`f.totalDegree * S.card ^ (n - 1)`. -/
theorem schwartz_zippel {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] :
    ∀ {n : ℕ} (f : MvPolynomial (Fin n) R), f ≠ 0 →
      ∀ (S : Finset R), S.Nonempty →
        (Finset.univ.filter (fun x : Fin n → S => MvPolynomial.eval (fun i => (x i).1) f = 0)).card ≤
          f.totalDegree * S.card ^ (n - 1)
  | 0, f, hf, S, _ => by
    have hf_eq : f = MvPolynomial.C (f.coeff 0) := by
      ext d
      have hd : d = 0 := Subsingleton.elim d 0
      subst hd
      simp
    have hc0 : f.coeff 0 ≠ 0 := by
      intro hc
      apply hf
      rw [hf_eq, hc, map_zero]
    have hemp : Finset.univ.filter (fun x : Fin 0 → S =>
        MvPolynomial.eval (fun i => (x i).1) f = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x _
      rw [hf_eq, MvPolynomial.eval_C]
      exact hc0
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _
  | n + 1, f, hf, S, hS => by
    let e := MvPolynomial.finSuccEquiv R n
    let P := e f
    have hP_ne : P ≠ 0 := fun h0 => hf (e.injective (by simpa [P] using h0))
    let d := P.natDegree
    let g := P.leadingCoeff
    have hg_ne : g ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP_ne
    have hdeg_le : g.totalDegree + d ≤ f.totalDegree := by
      change (P.coeff d).totalDegree + d ≤ f.totalDegree
      exact finSuccEquiv_coeff_totalDegree_le n f d hg_ne
    let Z := Finset.univ.filter (fun x : Fin (n + 1) → S =>
      MvPolynomial.eval (fun i => (x i).1) f = 0)
    let splitEquiv : (Fin (n + 1) → S) ≃ S × (Fin n → S) :=
      { toFun := fun x => (x 0, fun i => x i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun x => by ext i; refine Fin.cases rfl (fun _ => rfl) i
        right_inv := fun p => by ext <;> rfl }
    let Z' := (S.attach ×ˢ Finset.univ).filter (fun p : S × (Fin n → S) =>
      MvPolynomial.eval (fun i => (splitEquiv.symm p i).1) f = 0)
    have hZ_card : Z.card = Z'.card := by
      refine Finset.card_bij (fun x _ => splitEquiv x) ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, ?_⟩
        have hcons : (fun i : Fin (n + 1) => (splitEquiv.symm (splitEquiv x) i).1) =
            fun i : Fin (n + 1) => (x i).1 := by
          ext i
          dsimp only [splitEquiv]
          refine Fin.cases rfl (fun _ => rfl) i
        rw [hcons]
        exact hx.2
      · intro x₁ _ x₂ _ heq
        exact splitEquiv.injective heq
      · intro p hp
        rw [Finset.mem_filter] at hp
        refine ⟨splitEquiv.symm p, ?_, splitEquiv.apply_symm_apply p⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hp.2⟩
    let Z_bad := Z'.filter (fun p => MvPolynomial.eval (fun i => (p.2 i).1) g = 0)
    let Z_good := Z'.filter (fun p => MvPolynomial.eval (fun i => (p.2 i).1) g ≠ 0)
    have hZ_split : Z'.card = Z_bad.card + Z_good.card := by
      rw [← Finset.card_filter_add_card_filter_not (s := Z')
        (p := fun p => MvPolynomial.eval (fun i => (p.2 i).1) g = 0)]
    let tailRoots := Finset.univ.filter (fun x' : Fin n → S =>
      MvPolynomial.eval (fun i => (x' i).1) g = 0)
    have hbad_sub : Z_bad ⊆ S.attach ×ˢ tailRoots := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩⟩
    have hbad_card : Z_bad.card ≤ g.totalDegree * S.card ^ n := by
      have h1 : Z_bad.card ≤ (S.attach ×ˢ tailRoots).card := Finset.card_le_card hbad_sub
      rw [Finset.card_product, Finset.card_attach] at h1
      have hIH := schwartz_zippel g hg_ne S hS
      rcases n with _ | n'
      · have hg_deg0 : g.totalDegree = 0 := by
          have hg_c : g = MvPolynomial.C (g.coeff 0) := by
            ext d'; rw [Subsingleton.elim d' 0]; simp
          rw [hg_c, MvPolynomial.totalDegree_C]
        rw [hg_deg0, zero_mul] at hIH
        have h0 : tailRoots.card = 0 := by
          change tailRoots.card ≤ 0 at hIH
          omega
        rw [h0, mul_zero] at h1
        exact le_trans h1 (Nat.zero_le _)
      · have h2 := Nat.mul_le_mul_left S.card hIH
        have hpow : S.card * (g.totalDegree * S.card ^ n') = g.totalDegree * S.card ^ (n' + 1) := by
          rw [pow_succ]; ring
        exact le_trans h1 (by simpa [Nat.succ_sub_one, hpow] using h2)
    let tailGood := Finset.univ.filter (fun x' : Fin n → S =>
      MvPolynomial.eval (fun i => (x' i).1) g ≠ 0)
    have hgood_bound : Z_good.card ≤ d * S.card ^ n := by
      have hZ_good_eq : Z_good.card =
          ∑ x' ∈ tailGood, (S.filter (fun s0 : R =>
            Polynomial.eval s0 (P.map (MvPolynomial.eval (fun i => (x' i).1))) = 0)).card := by
        have hsub_fib : ∀ x' ∈ tailGood,
            (Z_good.filter (fun p => p.2 = x')).card =
              (S.filter (fun s0 : R =>
                Polynomial.eval s0 (P.map (MvPolynomial.eval (fun i => (x' i).1))) = 0)).card := by
          intro x' hx'
          refine Finset.card_bij (fun p _ => p.1.1) ?_ ?_ ?_
          · intro p hp
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at hp
            refine Finset.mem_filter.mpr ⟨p.1.2, ?_⟩
            have heval := finSuccEquiv_eval_eq n f (fun i => (splitEquiv.symm p i).1)
            have htail : (fun i : Fin n => (splitEquiv.symm p i.succ).1) = fun i => (x' i).1 := by
              ext i; simp [splitEquiv, hp.2]
            rw [hp.1.1.2] at heval
            rw [← hp.2]
            symm
            simpa [P, e, splitEquiv, htail] using heval
          · intro p₁ hp₁ p₂ hp₂ heq
            rw [Finset.mem_filter] at hp₁ hp₂
            ext
            · exact heq
            · rw [hp₁.2, hp₂.2]
          · intro s0 hs0
            rw [Finset.mem_filter] at hs0
            rw [Finset.mem_filter] at hx'
            refine ⟨(⟨s0, hs0.1⟩, x'), ?_, rfl⟩
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
            refine ⟨⟨⟨Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_univ _⟩, ?_⟩, hx'.2⟩, rfl⟩
            rw [finSuccEquiv_eval_eq]
            exact hs0.2
        have hpart := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := Z_good) (t := tailGood)
          (fun p hp => by
            rw [Finset.mem_coe, Finset.mem_filter] at hp
            rw [Finset.mem_coe, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hp.2⟩)
        rw [hpart]
        exact Finset.sum_congr rfl hsub_fib
      rw [hZ_good_eq]
      have hterm : ∀ x' ∈ tailGood,
          (S.filter (fun s0 : R =>
            Polynomial.eval s0 (P.map (MvPolynomial.eval (fun i => (x' i).1))) = 0)).card ≤ d := by
        intro x' hx'
        rw [Finset.mem_filter] at hx'
        let Px' := P.map (MvPolynomial.eval (fun i => (x' i).1))
        have hPx'_ne : Px' ≠ 0 := by
          intro h0
          have hc := congrArg (fun p : Polynomial R => p.coeff d) h0
          simp only [Px', Polynomial.coeff_map, Polynomial.coeff_zero] at hc
          exact hx'.2 hc
        have hPx'_deg : Px'.natDegree ≤ d := Polynomial.natDegree_map_le
        have hsub : (S.filter (fun s0 : R => Px'.eval s0 = 0)) ⊆ Px'.roots.toFinset := by
          intro s0 hs0
          rw [Finset.mem_filter] at hs0
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hPx'_ne]
          exact hs0.2
        exact le_trans (Finset.card_le_card hsub)
          (le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' Px') hPx'_deg))
      calc ∑ x' ∈ tailGood, (S.filter _).card
          ≤ ∑ _x' ∈ tailGood, d := Finset.sum_le_sum hterm
        _ = tailGood.card * d := by simp
        _ ≤ Fintype.card (Fin n → S) * d :=
            Nat.mul_le_mul_right d (Finset.card_le_univ tailGood)
        _ = d * S.card ^ n := by
            simp [Fintype.card_coe, mul_comm]
    rw [hZ_card, hZ_split]
    calc Z_bad.card + Z_good.card
        ≤ g.totalDegree * S.card ^ n + d * S.card ^ n := Nat.add_le_add hbad_card hgood_bound
      _ = (g.totalDegree + d) * S.card ^ n := by ring
      _ ≤ f.totalDegree * S.card ^ n := Nat.mul_le_mul_right _ hdeg_le
      _ = f.totalDegree * S.card ^ (n + 1 - 1) := by simp

end SchwartzZippel

/-! ## Section 4: Chevalley–Warning Theorem -/

section ChevalleyWarning

private lemma zmod_sum_pow_eq_zero {p : ℕ} [Fact p.Prime] {e : ℕ} (he : e < p - 1) :
    (∑ a : ZMod p, a ^ e) = 0 := by
  rcases eq_or_ne e 0 with rfl | he_pos
  · simp
  · have hex : ∃ c : (ZMod p)ˣ, c.1 ^ e ≠ 1 := by
      by_contra hall
      push Not at hall
      let P : Polynomial (ZMod p) := Polynomial.X ^ e - 1
      have hP_ne : P ≠ 0 := by
        intro h0
        have hc := congrArg (fun q : Polynomial (ZMod p) => q.coeff e) h0
        simp [P, Polynomial.coeff_one, he_pos] at hc
      have hP_deg : P.natDegree ≤ e := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        simp
      have hroots : Finset.univ.map ⟨Units.val, Units.val_injective⟩ ⊆ P.roots.toFinset := by
        intro u hu
        rw [Finset.mem_map] at hu
        rcases hu with ⟨c, _, rfl⟩
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne]
        simp [P, hall c]
      have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
      have hle := Finset.card_le_card hroots
      rw [Finset.card_map, Finset.card_univ, hcard_u] at hle
      have hle2 := le_trans hle (le_trans (Multiset.toFinset_card_le _)
        (le_trans (Polynomial.card_roots' P) hP_deg))
      omega
    rcases hex with ⟨c, hc_ne⟩
    let S : ZMod p := ∑ a : ZMod p, a ^ e
    have hmul_S : c.1 ^ e * S = S := by
      dsimp [S]
      rw [Finset.mul_sum]
      calc ∑ a : ZMod p, c.1 ^ e * a ^ e
          = ∑ a : ZMod p, (c.1 * a) ^ e := Finset.sum_congr rfl fun a _ => by ring
        _ = ∑ a : ZMod p, a ^ e :=
            Equiv.sum_comp (Equiv.mulLeft₀ c.1 (Units.ne_zero c)) (fun a => a ^ e)
    have hdiff : (c.1 ^ e - 1) * S = 0 := by linear_combination hmul_S
    rcases mul_eq_zero.mp hdiff with h1 | h2
    · exact absurd (sub_eq_zero.mp h1) hc_ne
    · exact h2

private lemma zmod_sum_monomial_eq_zero {p : ℕ} [Fact p.Prime] {n : ℕ}
    (d : Fin n →₀ ℕ) (c : ZMod p) (hd : d.sum (fun _ e => e) < (p - 1) * n) :
    (∑ x : Fin n → ZMod p, MvPolynomial.eval x (MvPolynomial.monomial d c)) = 0 := by
  have hex_lt : ∃ i₀ : Fin n, d i₀ < p - 1 := by
    by_contra hall
    push Not at hall
    have hsum : (p - 1) * n ≤ d.sum (fun _ e => e) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      calc (p - 1) * n = ∑ _i : Fin n, (p - 1) := by simp [mul_comm]
        _ ≤ ∑ i : Fin n, d i := Finset.sum_le_sum fun i _ => hall i
    omega
  rcases hex_lt with ⟨i₀, hi₀⟩
  have hfact : ∀ x : Fin n → ZMod p,
      MvPolynomial.eval x (MvPolynomial.monomial d c) = c * ∏ i : Fin n, (x i) ^ (d i) := by
    intro x
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp_rw [hfact, ← Finset.mul_sum]
  have hprod_sum : (∑ x : Fin n → ZMod p, ∏ i : Fin n, (x i) ^ (d i)) =
      ∏ i : Fin n, ∑ a : ZMod p, a ^ (d i) := by
    symm
    exact Fintype.prod_sum (fun i a => a ^ (d i))
  rw [hprod_sum, Finset.prod_eq_zero (Finset.mem_univ i₀) (zmod_sum_pow_eq_zero hi₀), mul_zero]

/-- **Chevalley–Warning Theorem (`ZMod p`):**
For prime `p` and polynomials `fs : List (MvPolynomial (Fin n) (ZMod p))` with
`(fs.map MvPolynomial.totalDegree).sum < n`, `p` divides the number of common zeros in `(ZMod p)^n`. -/
theorem chevalley_warning {p : ℕ} [Fact p.Prime] {n : ℕ}
    (fs : List (MvPolynomial (Fin n) (ZMod p)))
    (hdeg : (fs.map MvPolynomial.totalDegree).sum < n) :
    p ∣ (Finset.univ.filter (fun x : Fin n → ZMod p => ∀ f ∈ fs, MvPolynomial.eval x f = 0)).card := by
  rw [← ZMod.natCast_eq_zero_iff]
  let F : MvPolynomial (Fin n) (ZMod p) := (fs.map (fun f => 1 - f ^ (p - 1))).prod
  have hp_pos : 1 ≤ p := Nat.Prime.one_lt Fact.out |>.le
  have hF_eval : ∀ x : Fin n → ZMod p,
      MvPolynomial.eval x F =
        if (∀ f ∈ fs, MvPolynomial.eval x f = 0) then (1 : ZMod p) else 0 := by
    intro x
    dsimp [F]
    rw [map_list_prod]
    simp only [List.map_map, Function.comp_def, map_sub, map_one, map_pow]
    split_ifs with hall
    · refine List.prod_eq_one fun y hy => ?_
      rw [List.mem_map] at hy
      rcases hy with ⟨f, hf, rfl⟩
      rw [hall f hf, zero_pow (by have := Nat.Prime.two_le (Fact.out : p.Prime); omega), sub_zero]
    · push Not at hall
      rcases hall with ⟨f, hf, hne⟩
      refine List.prod_eq_zero (List.mem_map.mpr ⟨f, hf, ?_⟩)
      have hpow1 : (MvPolynomial.eval x f) ^ (p - 1) = 1 :=
        @ZMod.pow_card_sub_one_eq_one p _ (MvPolynomial.eval x f) hne
      rw [hpow1, sub_self]
  have hsum_card :
      ((Finset.univ.filter (fun x : Fin n → ZMod p => ∀ f ∈ fs, MvPolynomial.eval x f = 0)).card : ZMod p) =
        ∑ x : Fin n → ZMod p, MvPolynomial.eval x F := by
    simp_rw [hF_eval, Finset.sum_boole]
  have hF_deg : F.totalDegree < (p - 1) * n := by
    have h1 : F.totalDegree ≤ (fs.map (fun f => (1 - f ^ (p - 1)).totalDegree)).sum := by
      dsimp [F]
      clear hsum_card hF_eval hdeg
      induction fs with
      | nil => simp
      | cons f fs ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        exact Nat.add_le_add_left ih _
    have h2 : (fs.map (fun f => (1 - f ^ (p - 1)).totalDegree)).sum ≤
        (p - 1) * (fs.map MvPolynomial.totalDegree).sum := by
      clear h1 hsum_card hF_eval hdeg
      induction fs with
      | nil => simp
      | cons f fs ih =>
        simp only [List.map_cons, List.sum_cons]
        have hf1 : (1 - f ^ (p - 1)).totalDegree ≤ (p - 1) * f.totalDegree := by
          refine le_trans (totalDegree_sub_le 1 (f ^ (p - 1))) ?_
          simp only [MvPolynomial.totalDegree_one, zero_le, max_eq_right]
          exact MvPolynomial.totalDegree_pow f (p - 1)
        calc (1 - f ^ (p - 1)).totalDegree + (fs.map (fun f => (1 - f ^ (p - 1)).totalDegree)).sum
            ≤ (p - 1) * f.totalDegree + (p - 1) * (fs.map MvPolynomial.totalDegree).sum :=
              Nat.add_le_add hf1 ih
          _ = (p - 1) * (f.totalDegree + (fs.map MvPolynomial.totalDegree).sum) := by ring
    have hp2 : 0 < p - 1 := by have := Nat.Prime.two_le (Fact.out : p.Prime); omega
    exact lt_of_le_of_lt (le_trans h1 h2) (Nat.mul_lt_mul_of_pos_left hdeg hp2)
  rw [hsum_card]
  conv_lhs =>
    arg 2; ext x
    rw [F.as_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hd_lt : d.sum (fun _ e => e) < (p - 1) * n :=
    lt_of_le_of_lt (MvPolynomial.le_totalDegree hd) hF_deg
  exact zmod_sum_monomial_eq_zero d (F.coeff d) hd_lt

/-- **Chevalley–Warning Nonzero Common Root:**
If `0` is a common zero of `fs` and `(fs.map totalDegree).sum < n`, then there exists
a nonzero common zero `x ≠ 0`. -/
theorem chevalley_warning_nonzero_root {p : ℕ} [Fact p.Prime] {n : ℕ}
    (fs : List (MvPolynomial (Fin n) (ZMod p)))
    (hdeg : (fs.map MvPolynomial.totalDegree).sum < n)
    (hzero : ∀ f ∈ fs, MvPolynomial.eval 0 f = 0) :
    ∃ x : Fin n → ZMod p, x ≠ 0 ∧ ∀ f ∈ fs, MvPolynomial.eval x f = 0 := by
  let V := Finset.univ.filter (fun x : Fin n → ZMod p => ∀ f ∈ fs, MvPolynomial.eval x f = 0)
  have h0_mem : (0 : Fin n → ZMod p) ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
  have hV_pos : 0 < V.card := Finset.card_pos.mpr ⟨0, h0_mem⟩
  have hdvd : p ∣ V.card := chevalley_warning fs hdeg
  have hp_le : p ≤ V.card := Nat.le_of_dvd hV_pos hdvd
  have h2_le : 2 ≤ V.card := le_trans (Nat.Prime.two_le Fact.out) hp_le
  have hex : (V.erase 0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem h0_mem]
    omega
  rcases hex with ⟨x, hx⟩
  rw [Finset.mem_erase, Finset.mem_filter] at hx
  exact ⟨x, hx.1, hx.2.2⟩

end ChevalleyWarning

/-! ## Section 5: Babai–Frankl Triangular Rank Criterion & Oddtown -/

section LinearAlgebraRank

/-- **Babai–Frankl Triangular Rank Criterion:**
If vectors `v, w : Fin m → Fin d → K` over a field `K` satisfy `dot (v i) (w i) ≠ 0` and
`dot (v i) (w j) = 0` for all `i < j`, then `m ≤ d`. -/
theorem babai_frankl_triangular {K : Type*} [Field K] {m d : ℕ}
    (v w : Fin m → Fin d → K)
    (hdiag : ∀ i : Fin m, (∑ k : Fin d, v i k * w i k) ≠ 0)
    (htri : ∀ i j : Fin m, i < j → (∑ k : Fin d, v i k * w j k) = 0) :
    m ≤ d := by
  classical
  have hlin : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    by_contra hci
    let S := Finset.univ.filter (fun j : Fin m => c j ≠ 0)
    have hS_ne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩⟩
    let j := S.max' hS_ne
    have hj_mem : j ∈ S := Finset.max'_mem S hS_ne
    have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj_mem).2
    have hdot_zero : ∑ l : Fin m, c l * (∑ k : Fin d, v l k * w j k) = 0 := by
      have h1 : ∑ k : Fin d, (∑ l : Fin m, c l • v l) k * w j k = 0 := by
        rw [hc]
        simp
      calc ∑ l : Fin m, c l * (∑ k : Fin d, v l k * w j k)
          = ∑ l : Fin m, ∑ k : Fin d, c l * v l k * w j k := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => by ring
        _ = ∑ k : Fin d, ∑ l : Fin m, (c l * v l k) * w j k := Finset.sum_comm
        _ = ∑ k : Fin d, (∑ l : Fin m, c l • v l) k * w j k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [Finset.sum_apply, Finset.sum_mul, smul_eq_mul]
        _ = 0 := h1
    have honly_j : ∑ l : Fin m, c l * (∑ k : Fin d, v l k * w j k) =
        c j * (∑ k : Fin d, v j k * w j k) := by
      refine Finset.sum_eq_single j (fun l _ hlj => ?_) (fun h => absurd (Finset.mem_univ j) h)
      rcases lt_or_gt_of_ne hlj with hlt | hgt
      · rw [htri l j hlt, mul_zero]
      · have hcl : c l = 0 := by
          by_contra hc_ne
          have hl_mem : l ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_ne⟩
          have hle : l ≤ j := Finset.le_max' S l hl_mem
          exact absurd hgt (not_lt_of_ge hle)
        rw [hcl, zero_mul]
    rw [honly_j] at hdot_zero
    rcases mul_eq_zero.mp hdot_zero with h1 | h2
    · exact hcj h1
    · exact hdiag j h2
  have hcard := hlin.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using hcard

/-- **Oddtown Theorem (`m ≤ d`):**
If `A : Fin m → Finset (Fin d)` satisfy `Odd (A i).card` for all `i` and
`Even (A i ∩ A j).card` for all `i ≠ j`, then `m ≤ d`. -/
theorem oddtown_bound {m d : ℕ} (A : Fin m → Finset (Fin d))
    (hodd : ∀ i : Fin m, Odd (A i).card)
    (heven : ∀ i j : Fin m, i ≠ j → Even (A i ∩ A j).card) :
    m ≤ d := by
  let v : Fin m → Fin d → ZMod 2 := fun i k => if k ∈ A i then 1 else 0
  have hdot : ∀ i j : Fin m, (∑ k : Fin d, v i k * v j k) = (((A i ∩ A j).card : ℕ) : ZMod 2) := by
    intro i j
    have h1 : ∀ k : Fin d, v i k * v j k = if k ∈ A i ∩ A j then (1 : ZMod 2) else 0 := by
      intro k
      by_cases hi : k ∈ A i <;> by_cases hj : k ∈ A j <;> simp [v, hi, hj]
    simp_rw [h1, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine babai_frankl_triangular v v (fun i => ?_) (fun i j hij => ?_)
  · rw [hdot i i, Finset.inter_self]
    rcases hodd i with ⟨k, hk⟩
    rw [hk, Nat.cast_add, Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    simp
  · rw [hdot i j]
    rcases heven i j hij.ne with ⟨k, hk⟩
    rw [hk, ← two_mul, Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]

end LinearAlgebraRank

end Arith4Ext.AlgebraicMethod
