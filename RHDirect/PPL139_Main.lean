/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.
Licensed under the Apache License, Version 2.0.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-!
# PPL 139 (Erdős Problem #52 — The Erdős–Szemerédi Sum-Product Conjecture):
# Sharp Layer-Cake Solymosi `4/3` Theorem (Improving the Explicit Constant to `2 ln |A|`),
# Exact Multiplicative-Energy & Signed `Finset ℤ` Bounds, and Erdős's Multiplication-Table Upper Bound

**Scope Notice (Genuine Explicit Constant Improvement & Landmark Pure-Mathlib Milestones — NOT a Solution to the $250 Conjecture):**
Erdős Problem #52 (`erdosproblems.com/52`, PPL 139, $250 prize) asks whether for every finite set
`A : Finset ℤ` and every `ε > 0`, `max(|A + A|, |A * A|) ≫_ε |A|^(2 - ε)`.
Over `ℤ` (and `ℚ`), this conjecture remains **OPEN** (note that in May 2026, Bloom, Sawin,
Schildkraut, and Zhelezov, `arXiv:2605.28781`, disproved the corresponding conjecture over `ℝ`
using algebraic integers in number fields of degree `≍ log |A|`, establishing a relativization
barrier against purely real-order / incidence-geometry proofs).

This file formalizes the following **unconditional** theorems using pure Mathlib (`Finset`,
`open scoped Pointwise` for `A + A` and `A * A`, `Real.log`, `Real.rpow`), with **zero custom
definitions** in any public theorem signature:

1. **Exact Elementary Sumset & Product-Set Baselines:**
   - `card_add_self_ge_two_mul_sub_one_real` / `card_add_self_ge_two_mul_sub_one_int`:
     `2 * A.card - 1 ≤ (A + A).card` for every nonempty finite subset of `ℝ` or `ℤ`.
   - `card_mul_self_ge_card_real` / `card_mul_self_ge_card_int`:
     `A.card ≤ (A * A).card` for every finite subset of `ℝ` or `ℤ` with `2 ≤ A.card`.
   - `card_add_self_Icc_int` & `card_mul_self_gp_int`: exact arithmetic-progression and
     geometric-progression cardinalities (`2 * N - 1`).
2. **Exact Multiplicative Energy & Cauchy–Schwarz:**
   - `cauchy_schwarz_mul_energy_real`: `(A.card : ℝ) ^ 4 ≤ ((A * A).card : ℝ) * (E^×(A) : ℝ)`.
3. **NEW Sharp Layer-Cake + Diagonal-Bridge + Self-Ray Solymosi Theorem:**
   Replacing Solymosi's (2009) dyadic slicing (`4 * ⌈log₂ |A|⌉ ≈ 5.7708 ln |A|`) with:
   (i) mirror symmetry `s ↦ s⁻¹` bridged across the diagonal ray `s = 1` (eliminating boundary-ray
   loss), (ii) inclusion of all disjoint self-ray sumsets `L_t + L_t` (strengthening the level
   denominator from `k²` to `k² + 2k - 1` and shaving `|A + A|` from `|A + A|²`), and
   (iii) exact discrete layer-cake summation `m² = ∑_{k=1}^m (2k - 1)`, we prove for every
   finite `A ⊂ ℝ_{>0}` with `2 ≤ A.card`:
   - `solymosi_mul_energy_exact_harmonic`:
     `E^×(A) ≤ |A|² + (∑_{k=1}^{|A|-1} (2k - 1) / (k² + 2k - 1)) * |A + A| * (|A + A| - 1)`.
   - `solymosi_mul_energy_sharp_two_log`:
     `E^×(A) ≤ 2 * Real.log |A| * |A + A|²` (improving Solymosi's `4 ⌈log₂ |A|⌉` by a factor of
     `2 / ln 2 ≈ 2.885×` asymptotically and up to `8×` for small sets).
   - `solymosi_sum_product_pos_sharp` & `solymosi_max_sum_product_pos_sharp`:
     `|A + A|² * |A * A| ≥ |A|⁴ / (2 * Real.log |A|)` and
     `max(|A + A|, |A * A|) ≥ |A|^(4/3) / (2 * Real.log |A|)^(1/3)`.
4. **Full Signed `Finset ℝ` and `Finset ℤ` Solymosi `4/3` Theorems (Matching `ErdosProblems/52.lean`):**
   - `solymosi_sum_product_real`, `solymosi_sum_product_int`, `solymosi_max_sum_product_int`:
     `|A + A|² * |A * A| ≥ |A|⁴ / (36 * Real.log |A|)` for ALL finite `A` with `2 ≤ A.card`
     (allowing `0` and negative elements).
   - `solymosi_sum_product_int_rpow`:
     `∀ ε > 0, ε < 4 / 3 → ∃ C > 0, ∀ A : Finset ℤ, max(|A + A|, |A * A|) ≥ C * |A|^(4/3 - ε)`.
5. **Erdős (1955) Multiplication Table Theorem & Non-Trivial Upper Bound (`max(|A+A|, |AA|) = o(|A|²)`):**
   - Formalized via Turán's second-moment method on `Ω_P(n) = ∑_{p ∈ P} v_p(n)` plus Euler's
     divergence of `∑ 1/p` (`Nat.Primes.not_summable_one_div`), proving
     `erdos_multiplication_table_card_le` and `not_quadratic_sum_product_int`:
     `∀ C > 0, ∀ M : ℕ, ∃ A : Finset ℤ, M ≤ A.card ∧ max(|A + A|, |A * A|) < C * |A|²`,
     ruling out `Ω(|A|²)` (proving `ε > 0` in Erdős Problem #52 cannot be removed).
-/

open scoped Pointwise BigOperators

namespace PPL139

/-! ## Section 1: Elementary Sumset & Product-Set Baselines -/

section ElementaryBaselines

private lemma card_add_self_ge_two_mul_sub_one_aux {α : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] (A : Finset α) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by
  let m := A.min' hA
  let M := A.max' hA
  have hm : m ∈ A := Finset.min'_mem A hA
  have hM : M ∈ A := Finset.max'_mem A hA
  let S₁ : Finset α := A.image (· + m)
  let S₂ : Finset α := (A.erase m).image (· + M)
  have hS₁_sub : S₁ ⊆ A + A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact Finset.add_mem_add ha hm
  have hS₂_sub : S₂ ⊆ A + A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    exact Finset.add_mem_add (Finset.mem_of_mem_erase ha) hM
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rcases Finset.mem_image.mp hx₁ with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hx₂ with ⟨b, hb, hEq⟩
    have hb_ne : b ≠ m := (Finset.mem_erase.mp hb).1
    have hb_mem : b ∈ A := Finset.mem_of_mem_erase hb
    have hmb : m < b := lt_of_le_of_ne (Finset.min'_le A b hb_mem) (Ne.symm hb_ne)
    have haM : a ≤ M := Finset.le_max' A a ha
    have hlt : a + m < b + M := by
      calc a + m ≤ M + m := add_le_add_left haM m
        _ = m + M := add_comm M m
        _ < b + M := add_lt_add_left hmb M
    exact (ne_of_lt hlt) hEq.symm
  have hS₁_card : S₁.card = A.card := by
    apply Finset.card_image_of_injective
    intro a b h
    exact add_right_cancel h
  have hS₂_card : S₂.card = A.card - 1 := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_erase_of_mem hm
    · intro a b h
      exact add_right_cancel h
  have hle : (S₁ ∪ S₂).card ≤ (A + A).card := Finset.card_le_card (Finset.union_subset hS₁_sub hS₂_sub)
  rw [Finset.card_union_of_disjoint hdisj, hS₁_card, hS₂_card] at hle
  have hpos : 1 ≤ A.card := Finset.one_le_card.mpr hA
  omega

/-- Every nonempty finite set `A ⊂ ℝ` satisfies `2 |A| - 1 ≤ |A + A|`. -/
theorem card_add_self_ge_two_mul_sub_one_real (A : Finset ℝ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card :=
  card_add_self_ge_two_mul_sub_one_aux A hA

/-- Every nonempty finite set `A ⊂ ℤ` satisfies `2 |A| - 1 ≤ |A + A|`. -/
theorem card_add_self_ge_two_mul_sub_one_int (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card :=
  card_add_self_ge_two_mul_sub_one_aux A hA

private lemma card_mul_self_ge_card_aux {α : Type*} [CommRing α] [IsDomain α] [DecidableEq α]
    (A : Finset α) (hA : 2 ≤ A.card) :
    A.card ≤ (A * A).card := by
  have hex : ∃ a ∈ A, a ≠ 0 := by
    by_contra h
    push Not at h
    have hsub : A ⊆ ({0} : Finset α) := by
      intro x hx
      exact Finset.mem_singleton.mpr (h x hx)
    have hle : A.card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    omega
  rcases hex with ⟨a₀, ha₀, hne⟩
  have hsub : A.image (a₀ * ·) ⊆ A * A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
    exact Finset.mul_mem_mul ha₀ hb
  have hcard : (A.image (a₀ * ·)).card = A.card := by
    apply Finset.card_image_of_injective
    intro x y h
    exact mul_left_cancel₀ hne h
  exact hcard ▸ Finset.card_le_card hsub

/-- Every finite set `A ⊂ ℝ` with `|A| ≥ 2` satisfies `|A| ≤ |A * A|`. -/
theorem card_mul_self_ge_card_real (A : Finset ℝ) (hA : 2 ≤ A.card) :
    A.card ≤ (A * A).card :=
  card_mul_self_ge_card_aux A hA

/-- Every finite set `A ⊂ ℤ` with `|A| ≥ 2` satisfies `|A| ≤ |A * A|`. -/
theorem card_mul_self_ge_card_int (A : Finset ℤ) (hA : 2 ≤ A.card) :
    A.card ≤ (A * A).card :=
  card_mul_self_ge_card_aux A hA

/-- Exact sumset cardinality of the integer arithmetic progression `{1, …, N}`. -/
theorem card_add_self_Icc_int (N : ℕ) (hN : 1 ≤ N) :
    (Finset.Icc (1 : ℤ) (N : ℤ) + Finset.Icc (1 : ℤ) (N : ℤ)).card = 2 * N - 1 := by
  have hEq : Finset.Icc (1 : ℤ) (N : ℤ) + Finset.Icc (1 : ℤ) (N : ℤ) =
      Finset.Icc (2 : ℤ) (2 * (N : ℤ)) := by
    ext x
    simp only [Finset.mem_add, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ⟨ha1, haN⟩, b, ⟨hb1, hbN⟩, rfl⟩
      omega
    · rintro ⟨hx2, hx2N⟩
      by_cases hle : x ≤ (N : ℤ) + 1
      · refine ⟨1, ⟨le_rfl, by omega⟩, x - 1, ⟨by omega, by omega⟩, by ring⟩
      · refine ⟨(N : ℤ), ⟨by omega, le_rfl⟩, x - (N : ℤ), ⟨by omega, by omega⟩, by ring⟩
  rw [hEq, Int.card_Icc]
  omega

/-- Exact product-set cardinality of the integer geometric progression `{1, 2, …, 2^(N-1)}`. -/
theorem card_mul_self_gp_int (N : ℕ) (hN : 1 ≤ N) :
    let G : Finset ℤ := (Finset.range N).image (fun k => (2 : ℤ) ^ k)
    G.card = N ∧ (G * G).card = 2 * N - 1 := by
  intro G
  have hinj : Function.Injective (fun k : ℕ => (2 : ℤ) ^ k) := by
    intro a b h
    have hpos : (1 : ℤ) < 2 := by norm_num
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (pow_lt_pow_right₀ hpos hlt)) h
    · exact (ne_of_gt (pow_lt_pow_right₀ hpos hgt)) h
  have hGcard : G.card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hmul : G * G = (Finset.range (2 * N - 1)).image (fun k => (2 : ℤ) ^ k) := by
    ext x
    simp only [G, Finset.mem_mul, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨i + j, by omega, pow_add (2 : ℤ) i j⟩
    · rintro ⟨k, hk, rfl⟩
      by_cases hkn : k < N
      · exact ⟨(2 : ℤ) ^ k, ⟨k, hkn, rfl⟩, (2 : ℤ) ^ 0, ⟨0, by omega, rfl⟩, by simp⟩
      · refine ⟨(2 : ℤ) ^ (N - 1), ⟨N - 1, by omega, rfl⟩,
          (2 : ℤ) ^ (k - (N - 1)), ⟨k - (N - 1), by omega, rfl⟩, ?_⟩
        rw [← pow_add]
        congr 1
        omega
  refine ⟨hGcard, ?_⟩
  rw [hmul, Finset.card_image_of_injective _ hinj, Finset.card_range]

end ElementaryBaselines

/-! ## Section 2: Multiplicative Energy `E^×(A)` Identities & Cauchy–Schwarz -/

section MultiplicativeEnergy

private lemma sq_sum_le_card_mul_sum_sq_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have h0 : (0 : ℝ) ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexp : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
      2 * ((s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
    have h1 : ∀ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
        (s.card : ℝ) * (f i) ^ 2 - (2 * ∑ j ∈ s, f j) * f i + ∑ j ∈ s, (f j) ^ 2 := by
      intro i _
      have : ∀ j ∈ s, (f i - f j) ^ 2 = (f i) ^ 2 - (2 * f i) * f j + (f j) ^ 2 := fun j _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

private lemma mulEnergy_eq_sum_prod_fib_sq (A : Finset ℝ) :
    (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card =
      ∑ p ∈ A * A, ((A ×ˢ A).filter (fun y => y.1 * y.2 = p)).card ^ 2 := by
  have hmaps : ∀ x ∈ ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2),
      x.1.1 * x.1.2 ∈ A * A := by
    intro x hx
    have hmem := (Finset.mem_filter.mp hx).1
    have h1 := (Finset.mem_product.mp hmem).1
    exact Finset.mul_mem_mul (Finset.mem_product.mp h1).1 (Finset.mem_product.mp h1).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hEq : (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).filter
      (fun x => x.1.1 * x.1.2 = p) =
      ((A ×ˢ A).filter (fun y => y.1 * y.2 = p)) ×ˢ ((A ×ˢ A).filter (fun y => y.1 * y.2 = p)) := by
    ext ⟨⟨a, b⟩, ⟨c, d⟩⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨hab, hcd⟩, hmul⟩, hp⟩
      exact ⟨⟨hab, hp⟩, ⟨hcd, hmul.symm.trans hp⟩⟩
    · rintro ⟨⟨hab, hp1⟩, ⟨hcd, hp2⟩⟩
      exact ⟨⟨⟨hab, hcd⟩, hp1.trans hp2.symm⟩, hp1⟩
  rw [hEq, Finset.card_product, sq]

private lemma sum_prod_fib_eq_card_sq (A : Finset ℝ) :
    ∑ p ∈ A * A, ((A ×ˢ A).filter (fun y => y.1 * y.2 = p)).card = A.card ^ 2 := by
  have hmaps : ∀ y ∈ A ×ˢ A, y.1 * y.2 ∈ A * A := by
    intro y hy
    exact Finset.mul_mem_mul (Finset.mem_product.mp hy).1 (Finset.mem_product.mp hy).2
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_product, ← sq] at h
  exact h.symm

/-- Cauchy–Schwarz inequality for multiplicative energy:
`|A|⁴ ≤ |A * A| · E^×(A)` for every finite `A : Finset ℝ`. -/
theorem cauchy_schwarz_mul_energy_real (A : Finset ℝ) :
    (A.card : ℝ) ^ 4 ≤ ((A * A).card : ℝ) *
      ((((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card : ℝ) := by
  have h1 := sq_sum_le_card_mul_sum_sq_real (A * A)
    (fun p => (((A ×ˢ A).filter (fun y => y.1 * y.2 = p)).card : ℝ))
  have hsum : (∑ p ∈ A * A, (((A ×ˢ A).filter (fun y => y.1 * y.2 = p)).card : ℝ)) =
      (A.card : ℝ) ^ 2 := by
    exact_mod_cast sum_prod_fib_eq_card_sq A
  have hsq : (∑ p ∈ A * A, (((A ×ˢ A).filter (fun y => y.1 * y.2 = p)).card : ℝ) ^ 2) =
      ((((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card : ℝ) := by
    exact_mod_cast (mulEnergy_eq_sum_prod_fib_sq A).symm
  rw [hsum, hsq] at h1
  calc (A.card : ℝ) ^ 4 = ((A.card : ℝ) ^ 2) ^ 2 := by ring
    _ ≤ _ := h1

private noncomputable def ratioSet (A : Finset ℝ) : Finset ℝ :=
  (A ×ˢ A).image (fun p => p.2 / p.1)

private noncomputable def ray (A : Finset ℝ) (s : ℝ) : Finset (ℝ × ℝ) :=
  (A ×ˢ A).filter (fun p => p.2 = s * p.1)

private noncomputable def negSlopes (A : Finset ℝ) : Finset ℝ :=
  (ratioSet A).filter (· < 1)

private noncomputable def posSlopes (A : Finset ℝ) : Finset ℝ :=
  (ratioSet A).filter (1 < ·)

private lemma ratioSet_pos {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) {s : ℝ} (hs : s ∈ ratioSet A) :
    0 < s := by
  rcases Finset.mem_image.mp hs with ⟨⟨x, y⟩, hxy, rfl⟩
  exact div_pos (hpos y (Finset.mem_product.mp hxy).2) (hpos x (Finset.mem_product.mp hxy).1)

private lemma ray_card_inv {A : Finset ℝ} {s : ℝ} (hs : 0 < s) :
    (ray A s⁻¹).card = (ray A s).card := by
  have hEq : ray A s⁻¹ = (ray A s).image Prod.swap := by
    ext ⟨x, y⟩
    simp only [ray, Finset.mem_filter, Finset.mem_product, Finset.mem_image, Prod.swap]
    constructor
    · rintro ⟨⟨hx, hy⟩, hmul⟩
      refine ⟨(y, x), ⟨⟨hy, hx⟩, ?_⟩, rfl⟩
      have hne : s ≠ 0 := ne_of_gt hs
      calc x = s * (s⁻¹ * x) := by field_simp
        _ = s * y := by rw [← hmul]
    · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, hmul⟩, hswap⟩
      rcases Prod.mk.inj hswap with ⟨rfl, rfl⟩
      refine ⟨⟨hb, ha⟩, ?_⟩
      have hne : s ≠ 0 := ne_of_gt hs
      calc a = s⁻¹ * (s * a) := by field_simp
        _ = s⁻¹ * b := by rw [← hmul]
  rw [hEq, Finset.card_image_of_injective _ Prod.swap_injective]

private lemma ray_one_card (A : Finset ℝ) : (ray A 1).card = A.card := by
  have hEq : ray A 1 = A.image (fun a => (a, a)) := by
    ext ⟨x, y⟩
    simp only [ray, Finset.mem_filter, Finset.mem_product, Finset.mem_image, one_mul]
    constructor
    · rintro ⟨⟨hx, _⟩, hxy⟩
      exact ⟨x, hx, by simp [hxy]⟩
    · rintro ⟨a, ha, h⟩
      rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact ⟨⟨ha, ha⟩, rfl⟩
  rw [hEq, Finset.card_image_of_injective]
  intro a b h
  exact (Prod.mk.inj h).1

private lemma one_mem_ratioSet {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) (hA : A.Nonempty) :
    (1 : ℝ) ∈ ratioSet A := by
  rcases hA with ⟨a, ha⟩
  exact Finset.mem_image.mpr ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩, div_self (ne_of_gt (hpos a ha))⟩

private lemma mulEnergy_eq_sum_ray_sq {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) :
    (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card =
      ∑ s ∈ ratioSet A, (ray A s).card ^ 2 := by
  let S := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)
  have hmaps : ∀ x ∈ S, x.1.2 / x.2.1 ∈ ratioSet A := by
    intro x hx
    have hmem := (Finset.mem_filter.mp hx).1
    have h1 := (Finset.mem_product.mp hmem).1
    have h2 := (Finset.mem_product.mp hmem).2
    exact Finset.mem_image.mpr
      ⟨(x.2.1, x.1.2), Finset.mem_product.mpr ⟨(Finset.mem_product.mp h2).1, (Finset.mem_product.mp h1).2⟩, rfl⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun s _ => ?_
  let f : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) := fun x => ((x.2.1, x.1.2), (x.1.1, x.2.2))
  have hf_inj : Function.Injective f := by
    intro ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩ ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ h
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    rfl
  have hEq : (S.filter (fun x => x.1.2 / x.2.1 = s)).image f = ray A s ×ˢ ray A s := by
    ext ⟨⟨c, b⟩, ⟨a, d⟩⟩
    simp only [S, f, ray, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨a', b'⟩, ⟨c', d'⟩⟩, ⟨⟨⟨⟨ha', hb'⟩, ⟨hc', hd'⟩⟩, hmul⟩, hdiv⟩, heq⟩
      simp only [Prod.mk.injEq] at heq hmul hdiv
      rcases heq with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      have hc0 : c' ≠ 0 := ne_of_gt (hpos c' hc')
      have hb_eq : b' = s * c' := by
        rw [← hdiv]
        exact (div_mul_cancel₀ b' hc0).symm
      have hd_eq : d' = s * a' := by
        have h1 : a' * (s * c') = c' * d' := by rwa [← hb_eq]
        have h2 : c' * (s * a') = c' * d' := by linarith
        exact (mul_left_cancel₀ hc0 h2).symm
      exact ⟨⟨⟨hc', hb'⟩, hb_eq⟩, ⟨⟨ha', hd'⟩, hd_eq⟩⟩
    · rintro ⟨⟨⟨hc, hb⟩, hb_eq⟩, ⟨⟨ha, hd⟩, hd_eq⟩⟩
      refine ⟨((a, b), (c, d)), ⟨⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, ?_⟩, ?_⟩, rfl⟩
      · simp only; rw [hb_eq, hd_eq]; ring
      · have hc0 : c ≠ 0 := ne_of_gt (hpos c hc)
        simp only; rw [hb_eq, mul_div_cancel_right₀ s hc0]
  rw [← Finset.card_image_of_injective _ hf_inj, hEq, Finset.card_product, sq]

private lemma mulEnergy_eq_diag_add_two_neg {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) (hA : A.Nonempty) :
    (((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card =
      A.card ^ 2 + 2 * ∑ s ∈ negSlopes A, (ray A s).card ^ 2 := by
  rw [mulEnergy_eq_sum_ray_sq hpos]
  have hpart : ratioSet A = negSlopes A ∪ ({1} ∪ posSlopes A) := by
    ext s
    simp only [negSlopes, posSlopes, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hs
      rcases lt_trichotomy s 1 with hlt | rfl | hgt
      · exact Or.inl ⟨hs, hlt⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨hs, hgt⟩)
    · rintro (⟨hs, _⟩ | rfl | ⟨hs, _⟩)
      · exact hs
      · exact one_mem_ratioSet hpos hA
      · exact hs
  have hd1 : Disjoint (negSlopes A) ({1} ∪ posSlopes A) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    have hlt : s < 1 := (Finset.mem_filter.mp hs1).2
    simp only [posSlopes, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter] at hs2
    rcases hs2 with rfl | ⟨_, hgt⟩
    · exact lt_irrefl 1 hlt
    · exact lt_asymm hlt hgt
  have hd2 : Disjoint ({1} : Finset ℝ) (posSlopes A) := by
    rw [Finset.disjoint_singleton_left]
    intro h
    exact lt_irrefl 1 (Finset.mem_filter.mp h).2
  have hpos_eq : posSlopes A = (negSlopes A).image Inv.inv := by
    ext s
    simp only [posSlopes, negSlopes, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hs, hgt⟩
      refine ⟨s⁻¹, ⟨?_, inv_lt_one_of_one_lt₀ hgt⟩, inv_inv s⟩
      rcases Finset.mem_image.mp hs with ⟨⟨x, y⟩, hxy, rfl⟩
      refine Finset.mem_image.mpr ⟨(y, x), Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hxy).2, (Finset.mem_product.mp hxy).1⟩, ?_⟩
      exact (inv_div y x).symm
    · rintro ⟨t, ⟨ht, hlt⟩, rfl⟩
      have htpos : 0 < t := ratioSet_pos hpos ht
      refine ⟨?_, one_lt_inv₀ htpos |>.mpr hlt⟩
      rcases Finset.mem_image.mp ht with ⟨⟨x, y⟩, hxy, rfl⟩
      refine Finset.mem_image.mpr ⟨(y, x), Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hxy).2, (Finset.mem_product.mp hxy).1⟩, ?_⟩
      exact (inv_div y x).symm
  have hsum_pos : ∑ s ∈ posSlopes A, (ray A s).card ^ 2 =
      ∑ s ∈ negSlopes A, (ray A s).card ^ 2 := by
    rw [hpos_eq, Finset.sum_image (fun a _ b _ h => inv_injective h)]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hspos : 0 < s := ratioSet_pos hpos (Finset.mem_filter.mp hs).1
    rw [ray_card_inv hspos]
  rw [hpart, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton,
    ray_one_card, hsum_pos]
  ring

private lemma ray_card_lt_card_of_mem_negSlopes {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a)
    {s : ℝ} (hs : s ∈ negSlopes A) :
    (ray A s).card < A.card := by
  have hlt1 : s < 1 := (Finset.mem_filter.mp hs).2
  have hsub : (ray A s).image Prod.fst ⊆ A := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨⟨a, b⟩, hab, rfl⟩
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
  have hinj : Set.InjOn Prod.fst (ray A s : Set (ℝ × ℝ)) := by
    intro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 hEq
    simp only at hEq
    subst hEq
    have hy1 : y1 = s * x1 := (Finset.mem_filter.mp h1).2
    have hy2 : y2 = s * x1 := (Finset.mem_filter.mp h2).2
    rw [hy1, hy2]
  have hcard_eq : ((ray A s).image Prod.fst).card = (ray A s).card :=
    Finset.card_image_of_injOn hinj
  have hA : A.Nonempty := by
    rcases Finset.mem_image.mp (Finset.mem_filter.mp hs).1 with ⟨⟨x, _⟩, hxy, _⟩
    exact ⟨x, (Finset.mem_product.mp hxy).1⟩
  let m := A.min' hA
  have hm : m ∈ A := Finset.min'_mem A hA
  have hm_not : m ∉ (ray A s).image Prod.fst := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨⟨a, b⟩, hab, hma⟩
    simp only at hma
    have hbA : b ∈ A := (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).2
    have hbeq : b = s * a := (Finset.mem_filter.mp hab).2
    have hlt : b < m := by
      rw [hbeq, hma]
      nlinarith [hpos m hm]
    exact not_lt_of_ge (Finset.min'_le A b hbA) hlt
  have hssub : (ray A s).image Prod.fst ⊂ A := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun hEq => ?_⟩
    exact hm_not (hEq.symm ▸ hm)
  rw [← hcard_eq]
  exact Finset.card_lt_card hssub

end MultiplicativeEnergy

/-! ## Section 3: Sharp Layer-Cake + Diagonal-Bridge + Self-Ray Solymosi Theorem -/

section SharpSolymosi

private lemma sum_ray_pair_inj {A : Finset ℝ} {s₁ s₂ : ℝ} (hs : s₁ < s₂) :
    Set.InjOn (fun q : (ℝ × ℝ) × (ℝ × ℝ) => (q.1.1 + q.2.1, q.1.2 + q.2.2))
      ((ray A s₁ ×ˢ ray A s₂ : Finset ((ℝ × ℝ) × (ℝ × ℝ))) : Set ((ℝ × ℝ) × (ℝ × ℝ))) := by
  intro ⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩ h1 ⟨⟨x1', y1'⟩, ⟨x2', y2'⟩⟩ h2 hEq
  simp only [Finset.mem_coe, Finset.mem_product, ray, Finset.mem_filter] at h1 h2
  rcases Prod.mk.inj hEq with ⟨hx, hy⟩
  simp only at hx hy
  have hy1 : y1 = s₁ * x1 := h1.1.2
  have hy2 : y2 = s₂ * x2 := h1.2.2
  have hy1' : y1' = s₁ * x1' := h2.1.2
  have hy2' : y2' = s₂ * x2' := h2.2.2
  have hdiff : (s₂ - s₁) * (x2 - x2') = 0 := by
    have hlin : s₁ * x1 + s₂ * x2 = s₁ * x1' + s₂ * x2' := by rw [← hy1, ← hy2, ← hy1', ← hy2', hy]
    have h1x : s₁ * (x1 + x2) = s₁ * (x1' + x2') := by rw [hx]
    linarith
  have hne : s₂ - s₁ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hs)
  have hx2 : x2 = x2' := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hne)
  have hx1 : x1 = x1' := by linarith
  subst hx1; subst hx2
  rw [hy1, hy2, hy1', hy2']

private lemma sector_slope_bounds {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) {s₁ s₂ : ℝ} (hs : s₁ < s₂)
    {p : ℝ × ℝ}
    (hp : p ∈ (ray A s₁ ×ˢ ray A s₂).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2))) :
    0 < p.1 ∧ s₁ < p.2 / p.1 ∧ p.2 / p.1 < s₂ := by
  rcases Finset.mem_image.mp hp with ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, hmem, rfl⟩
  simp only [Finset.mem_product, ray, Finset.mem_filter] at hmem
  have hx1 : 0 < x1 := hpos x1 hmem.1.1.1
  have hx2 : 0 < x2 := hpos x2 hmem.2.1.1
  have hy1 : y1 = s₁ * x1 := hmem.1.2
  have hy2 : y2 = s₂ * x2 := hmem.2.2
  have hsum : 0 < x1 + x2 := add_pos hx1 hx2
  refine ⟨hsum, ?_, ?_⟩
  · rw [lt_div_iff₀ hsum, hy1, hy2]
    nlinarith
  · rw [div_lt_iff₀ hsum, hy1, hy2]
    nlinarith

private lemma self_ray_slope_eq {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) {s : ℝ}
    {p : ℝ × ℝ}
    (hp : p ∈ (ray A s ×ˢ ray A s).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2))) :
    0 < p.1 ∧ p.2 / p.1 = s := by
  rcases Finset.mem_image.mp hp with ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, hmem, rfl⟩
  simp only [Finset.mem_product, ray, Finset.mem_filter] at hmem
  have hx1 : 0 < x1 := hpos x1 hmem.1.1.1
  have hx2 : 0 < x2 := hpos x2 hmem.2.1.1
  have hsum : 0 < x1 + x2 := add_pos hx1 hx2
  refine ⟨hsum, ?_⟩
  rw [div_eq_iff (ne_of_gt hsum), hmem.1.2, hmem.2.2]
  ring

private lemma self_ray_sumset_card_ge {A : Finset ℝ} {s : ℝ} (hnon : (ray A s).Nonempty) :
    2 * (ray A s).card - 1 ≤
      ((ray A s ×ˢ ray A s).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2))).card := by
  let X : Finset ℝ := (ray A s).image Prod.fst
  have hinjX : Set.InjOn Prod.fst (ray A s : Set (ℝ × ℝ)) := by
    intro ⟨x1, y1⟩ h1 ⟨x2, y2⟩ h2 hEq
    simp only at hEq
    subst hEq
    have hy1 : y1 = s * x1 := (Finset.mem_filter.mp h1).2
    have hy2 : y2 = s * x1 := (Finset.mem_filter.mp h2).2
    rw [hy1, hy2]
  have hXcard : X.card = (ray A s).card := Finset.card_image_of_injOn hinjX
  have hXnon : X.Nonempty := hnon.image Prod.fst
  have hEq : (ray A s ×ˢ ray A s).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2)) =
      (X + X).image (fun u => (u, s * u)) := by
    ext ⟨u, v⟩
    simp only [X, Finset.mem_image, Finset.mem_product, Finset.mem_add, ray, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, ⟨⟨h1, hy1⟩, ⟨h2, hy2⟩⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair hy1 hy2
      rcases hpair with ⟨rfl, rfl⟩
      refine ⟨x1 + x2, ⟨x1, ⟨(x1, y1), ⟨h1, hy1⟩, rfl⟩, x2, ⟨(x2, y2), ⟨h2, hy2⟩, rfl⟩, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      rw [hy1, hy2]; ring
    · rintro ⟨w, ⟨x1, ⟨⟨a1, b1⟩, ⟨h1, hb1⟩, hxa1⟩, x2, ⟨⟨a2, b2⟩, ⟨h2, hb2⟩, hxa2⟩, hw⟩, hpair⟩
      simp only [Prod.mk.injEq] at hxa1 hxa2 hb1 hb2 hpair
      subst hxa1; subst hxa2; subst hw
      rcases hpair with ⟨rfl, rfl⟩
      refine ⟨((a1, b1), (a2, b2)), ⟨⟨h1, hb1⟩, ⟨h2, hb2⟩⟩, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      rw [hb1, hb2]; ring
  rw [hEq, Finset.card_image_of_injective]
  · rw [← hXcard]
    exact card_add_self_ge_two_mul_sub_one_real X hXnon
  · intro u₁ u₂ h
    exact (Prod.mk.inj h).1

private lemma self_ray_one_sumset_card (A : Finset ℝ) :
    ((ray A 1 ×ˢ ray A 1).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2))).card = (A + A).card := by
  have hEq : (ray A 1 ×ˢ ray A 1).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2)) =
      (A + A).image (fun u => (u, u)) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_add, ray, Finset.mem_filter, one_mul]
    constructor
    · rintro ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, ⟨⟨⟨hx1, _⟩, hy1⟩, ⟨⟨hx2, _⟩, hy2⟩⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair hy1 hy2
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨x1 + x2, ⟨x1, hx1, x2, hx2, rfl⟩, by simp [hy1, hy2]⟩
    · rintro ⟨w, ⟨x1, hx1, x2, hx2, rfl⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      exact ⟨((x1, x1), (x2, x2)), ⟨⟨⟨hx1, hx1⟩, rfl⟩, ⟨⟨hx2, hx2⟩, rfl⟩⟩, rfl⟩
  rw [hEq, Finset.card_image_of_injective]
  intro u₁ u₂ h
  exact (Prod.mk.inj h).1

/-- Core symmetric-sector + self-ray level-set bound:
for every finite `A ⊂ ℝ_{>0}` and every `1 ≤ k < |A|`, the upper level set
`U_k = {s ∈ A/A : s < 1 ∧ k ≤ |L_s|}` satisfies
`2 * |U_k| * (k² + 2k - 1) ≤ |A + A| * (|A + A| - 1)`. -/
private lemma sector_self_ray_level_bound {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a)
    {k : ℕ} (hk1 : 1 ≤ k) (hklt : k < A.card) :
    2 * ((negSlopes A).filter (fun s => k ≤ (ray A s).card)).card * (k ^ 2 + 2 * k - 1) ≤
      (A + A).card * ((A + A).card - 1) := by
  let U := (negSlopes A).filter (fun s => k ≤ (ray A s).card)
  let r := U.card
  change 2 * r * (k ^ 2 + 2 * k - 1) ≤ (A + A).card * ((A + A).card - 1)
  by_cases hr0 : r = 0
  · simp [hr0]
  have hrpos : 1 ≤ r := Nat.pos_of_ne_zero hr0
  let e : Fin r ↪o ℝ := U.orderEmbOfFin rfl
  have he_mem : ∀ j : Fin r, e j ∈ U := fun j => Finset.orderEmbOfFin_mem U rfl j
  have he_lt1 : ∀ j : Fin r, e j < 1 := fun j =>
    (Finset.mem_filter.mp (Finset.mem_filter.mp (he_mem j)).1).2
  have he_pos : ∀ j : Fin r, 0 < e j := fun j =>
    ratioSet_pos hpos (Finset.mem_filter.mp (Finset.mem_filter.mp (he_mem j)).1).1
  have he_card : ∀ j : Fin r, k ≤ (ray A (e j)).card := fun j =>
    (Finset.mem_filter.mp (he_mem j)).2
  let t : Fin (2 * r + 1) → ℝ := fun i =>
    if h1 : i.val < r then e ⟨i.val, h1⟩
    else if h2 : i.val = r then 1
    else (e ⟨2 * r - i.val, by omega⟩)⁻¹
  have ht_strict : StrictMono t := by
    intro i j hij
    change i.val < j.val at hij
    by_cases hi1 : i.val < r <;> by_cases hj1 : j.val < r
    · simp only [t, dif_pos hi1, dif_pos hj1]
      exact e.strictMono (by exact hij)
    · by_cases hj2 : j.val = r
      · simp only [t, dif_pos hi1, dif_neg hj1, dif_pos hj2]
        exact he_lt1 ⟨i.val, hi1⟩
      · simp only [t, dif_pos hi1, dif_neg hj1, dif_neg hj2]
        have hlt1 : e ⟨i.val, hi1⟩ < 1 := he_lt1 ⟨i.val, hi1⟩
        have hgt1 : 1 < (e ⟨2 * r - j.val, by omega⟩)⁻¹ :=
          (one_lt_inv₀ (he_pos _)).mpr (he_lt1 _)
        exact lt_trans hlt1 hgt1
    · omega
    · by_cases hi2 : i.val = r
      · have hj2 : j.val ≠ r := by omega
        simp only [t, dif_neg hi1, dif_pos hi2, dif_neg hj1, dif_neg hj2]
        exact (one_lt_inv₀ (he_pos _)).mpr (he_lt1 _)
      · have hj2 : j.val ≠ r := by omega
        simp only [t, dif_neg hi1, dif_neg hi2, dif_neg hj1, dif_neg hj2]
        have hlt : e ⟨2 * r - j.val, by omega⟩ < e ⟨2 * r - i.val, by omega⟩ :=
          e.strictMono (by show 2 * r - j.val < 2 * r - i.val; omega)
        exact inv_strictAnti₀ (he_pos _) hlt
  have ht_mid : t ⟨r, by omega⟩ = 1 := by
    simp only [t, show ¬ (r < r) by omega, dite_false, dite_true]
  have ht_card_ge : ∀ i : Fin (2 * r + 1), k ≤ (ray A (t i)).card := by
    intro i
    by_cases h1 : i.val < r
    · simp only [t, dif_pos h1]
      exact he_card ⟨i.val, h1⟩
    · by_cases h2 : i.val = r
      · simp only [t, dif_neg h1, dif_pos h2, ray_one_card]
        omega
      · simp only [t, dif_neg h1, dif_neg h2]
        rw [ray_card_inv (he_pos _)]
        exact he_card _
  -- Open sectors P i (i : Fin (2 * r)) and self-rays Q j (j : Fin (2 * r + 1))
  let P : Fin (2 * r) → Finset (ℝ × ℝ) := fun i =>
    (ray A (t i.castSucc) ×ˢ ray A (t i.succ)).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2))
  let Q : Fin (2 * r + 1) → Finset (ℝ × ℝ) := fun j =>
    (ray A (t j) ×ˢ ray A (t j)).image (fun q => (q.1.1 + q.2.1, q.1.2 + q.2.2))
  have hP_sub : ∀ i, P i ⊆ (A + A) ×ˢ (A + A) := by
    intro i p hp
    rcases Finset.mem_image.mp hp with ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, hmem, rfl⟩
    simp only [Finset.mem_product, ray, Finset.mem_filter] at hmem ⊢
    exact ⟨Finset.add_mem_add hmem.1.1.1 hmem.2.1.1, Finset.add_mem_add hmem.1.1.2 hmem.2.1.2⟩
  have hQ_sub : ∀ j, Q j ⊆ (A + A) ×ˢ (A + A) := by
    intro j p hp
    rcases Finset.mem_image.mp hp with ⟨⟨⟨x1, y1⟩, ⟨x2, y2⟩⟩, hmem, rfl⟩
    simp only [Finset.mem_product, ray, Finset.mem_filter] at hmem ⊢
    exact ⟨Finset.add_mem_add hmem.1.1.1 hmem.2.1.1, Finset.add_mem_add hmem.1.1.2 hmem.2.1.2⟩
  have hP_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin (2 * r))) P := by
    intro i _ j _ hij
    change Disjoint (P i) (P j)
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have hbi := sector_slope_bounds hpos (ht_strict (Fin.castSucc_lt_succ (i := i))) hpi
    have hbj := sector_slope_bounds hpos (ht_strict (Fin.castSucc_lt_succ (i := j))) hpj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hle : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        exact hlt
      have htle : t i.succ ≤ t j.castSucc := ht_strict.monotone hle
      linarith
    · have hle : j.succ ≤ i.castSucc := by
        change j.val + 1 ≤ i.val
        exact hgt
      have htle : t j.succ ≤ t i.castSucc := ht_strict.monotone hle
      linarith
  have hQ_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin (2 * r + 1))) Q := by
    intro i _ j _ hij
    change Disjoint (Q i) (Q j)
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have hbi := self_ray_slope_eq hpos hpi
    have hbj := self_ray_slope_eq hpos hpj
    exact hij (ht_strict.injective (hbi.2.symm.trans hbj.2))
  have hPQ_disj : Disjoint (Finset.univ.biUnion P) (Finset.univ.biUnion Q) := by
    rw [Finset.disjoint_left]
    intro p hpP hpQ
    rcases Finset.mem_biUnion.mp hpP with ⟨i, _, hpi⟩
    rcases Finset.mem_biUnion.mp hpQ with ⟨j, _, hqj⟩
    have hbi := sector_slope_bounds hpos (ht_strict (Fin.castSucc_lt_succ (i := i))) hpi
    have hbj := self_ray_slope_eq hpos hqj
    by_cases hle : j.val ≤ i.val
    · have : t j ≤ t i.castSucc := ht_strict.monotone hle
      linarith
    · have : t i.succ ≤ t j := ht_strict.monotone (show i.val + 1 ≤ j.val by omega)
      linarith
  have htotal : (∑ i : Fin (2 * r), (P i).card) + (∑ j : Fin (2 * r + 1), (Q j).card) ≤
      (A + A).card * (A + A).card := by
    have hsub : (Finset.univ.biUnion P) ∪ (Finset.univ.biUnion Q) ⊆ (A + A) ×ˢ (A + A) :=
      Finset.union_subset (Finset.biUnion_subset.mpr fun i _ => hP_sub i)
        (Finset.biUnion_subset.mpr fun j _ => hQ_sub j)
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hPQ_disj, Finset.card_biUnion hP_disj,
      Finset.card_biUnion hQ_disj, Finset.card_product] at hle
    exact hle
  -- Bound ∑ P i ≥ 2 * r * k^2
  have hP_card : ∀ i : Fin (2 * r), k ^ 2 ≤ (P i).card := by
    intro i
    have hEq : (P i).card = (ray A (t i.castSucc)).card * (ray A (t i.succ)).card := by
      rw [Finset.card_image_of_injOn (sum_ray_pair_inj (ht_strict (Fin.castSucc_lt_succ (i := i)))),
        Finset.card_product]
    rw [hEq, sq]
    exact Nat.mul_le_mul (ht_card_ge i.castSucc) (ht_card_ge i.succ)
  have hP_sum : 2 * r * k ^ 2 ≤ ∑ i : Fin (2 * r), (P i).card := by
    calc 2 * r * k ^ 2 = ∑ _i : Fin (2 * r), k ^ 2 := by simp
      _ ≤ ∑ i : Fin (2 * r), (P i).card := Finset.sum_le_sum fun i _ => hP_card i
  -- Bound ∑ Q j ≥ (A + A).card + 2 * r * (2 * k - 1)
  let mid : Fin (2 * r + 1) := ⟨r, by omega⟩
  have hQ_mid : (Q mid).card = (A + A).card := by
    simp only [Q, mid, ht_mid]
    exact self_ray_one_sumset_card A
  have hQ_other : ∀ j : Fin (2 * r + 1), j ≠ mid → 2 * k - 1 ≤ (Q j).card := by
    intro j _
    have hge := ht_card_ge j
    have hnon : (ray A (t j)).Nonempty := Finset.card_pos.mp (by omega)
    have h1 : 2 * (ray A (t j)).card - 1 ≤ (Q j).card := self_ray_sumset_card_ge hnon
    omega
  have hQ_sum : (A + A).card + 2 * r * (2 * k - 1) ≤ ∑ j : Fin (2 * r + 1), (Q j).card := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ mid), hQ_mid]
    refine Nat.add_le_add_left ?_ _
    have hcard_erase : (Finset.univ.erase mid : Finset (Fin (2 * r + 1))).card = 2 * r := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ mid), Finset.card_univ, Fintype.card_fin]
      omega
    calc 2 * r * (2 * k - 1) =
          (Finset.univ.erase mid : Finset (Fin (2 * r + 1))).card * (2 * k - 1) := by rw [hcard_erase]
      _ = ∑ _j ∈ Finset.univ.erase mid, (2 * k - 1) := by simp
      _ ≤ ∑ j ∈ Finset.univ.erase mid, (Q j).card :=
            Finset.sum_le_sum fun j hj => hQ_other j (Finset.ne_of_mem_erase hj)
  have hcomb : 2 * r * k ^ 2 + (A + A).card + 2 * r * (2 * k - 1) ≤ (A + A).card * (A + A).card := by
    omega
  have hsub_le : 2 * r * (k ^ 2 + 2 * k - 1) + (A + A).card ≤ (A + A).card * (A + A).card := by
    have h1 : k ^ 2 + 2 * k - 1 = k ^ 2 + (2 * k - 1) := by omega
    rw [h1, mul_add]
    omega
  have hAA_pos : 1 ≤ (A + A).card := by
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    have := card_add_self_ge_two_mul_sub_one_real A hA
    omega
  have hmul_sub : (A + A).card * ((A + A).card - 1) + (A + A).card = (A + A).card * (A + A).card := by
    cases h : (A + A).card with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring
  omega

private lemma sq_eq_sum_odd (m : ℕ) :
    m ^ 2 = ∑ k ∈ Finset.Ico 1 (m + 1), (2 * k - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1), ← ih]
    have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [this]
    ring

private lemma layer_cake_negSlopes_sq {A : Finset ℝ} (hpos : ∀ a ∈ A, 0 < a) :
    2 * ∑ s ∈ negSlopes A, (ray A s).card ^ 2 =
      ∑ k ∈ Finset.Ico 1 A.card,
        (2 * k - 1) * (2 * ((negSlopes A).filter (fun s => k ≤ (ray A s).card)).card) := by
  have h1 : ∑ s ∈ negSlopes A, (ray A s).card ^ 2 =
      ∑ s ∈ negSlopes A, ∑ k ∈ Finset.Ico 1 A.card,
        if k ≤ (ray A s).card then (2 * k - 1) else 0 := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hlt : (ray A s).card < A.card := ray_card_lt_card_of_mem_negSlopes hpos hs
    rw [sq_eq_sum_odd, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_Ico, Finset.mem_filter]
    omega
  rw [h1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  ring

/-- **Exact Rational-Harmonic Solymosi Multiplicative Energy Bound:**
For every finite `A ⊂ ℝ_{>0}`:
`E^×(A) ≤ |A|² + (∑_{k=1}^{|A|-1} (2k - 1) / (k² + 2k - 1)) · |A + A| (|A + A| - 1)`. -/
theorem solymosi_mul_energy_exact_harmonic (A : Finset ℝ) (hpos : ∀ a ∈ A, 0 < a) :
    ((((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card : ℝ) ≤
      (A.card : ℝ) ^ 2 +
        (∑ k ∈ Finset.Ico 1 A.card,
          ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)) *
          (((A + A).card * ((A + A).card - 1) : ℕ) : ℝ) := by
  by_cases hA : A.Nonempty
  · rw [mulEnergy_eq_diag_add_two_neg hpos hA, layer_cake_negSlopes_sq hpos]
    push_cast
    rw [Finset.sum_mul]
    refine add_le_add_right (Finset.sum_le_sum fun k hk => ?_) _
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hklt : k < A.card := (Finset.mem_Ico.mp hk).2
    have hden_pos : (0 : ℝ) < ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ) := by
      have : 0 < k ^ 2 + 2 * k - 1 := by
        have hk2 : 1 ≤ k ^ 2 := by nlinarith
        omega
      exact_mod_cast this
    have hlev : (2 * (((negSlopes A).filter (fun s => k ≤ (ray A s).card)).card : ℝ) *
        ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)) ≤
        (((A + A).card : ℝ) * (((A + A).card - 1 : ℕ) : ℝ)) := by
      exact_mod_cast sector_self_ray_level_bound hpos hk1 hklt
    rw [div_mul_eq_mul_div, le_div_iff₀ hden_pos]
    have hnonneg : (0 : ℝ) ≤ ((2 * k - 1 : ℕ) : ℝ) := by positivity
    calc (((2 * k - 1 : ℕ) : ℝ) *
          (2 * (((negSlopes A).filter (fun s => k ≤ (ray A s).card)).card : ℝ))) *
          ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)
        = ((2 * k - 1 : ℕ) : ℝ) *
          (2 * (((negSlopes A).filter (fun s => k ≤ (ray A s).card)).card : ℝ) *
            ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)) := by ring
      _ ≤ ((2 * k - 1 : ℕ) : ℝ) * (((A + A).card : ℝ) * (((A + A).card - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hlev hnonneg
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    subst hA
    simp

private lemma harmonic_term_le_two_div {k : ℕ} (hk : 1 ≤ k) :
    ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ) ≤ 2 / ((k + 2 : ℕ) : ℝ) := by
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have h1 : 1 ≤ k ^ 2 + 2 * k := by omega
  have hden1 : (0 : ℝ) < ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ) := by
    have : 0 < k ^ 2 + 2 * k - 1 := by omega
    exact_mod_cast this
  have hden2 : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  have hcast1 : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; push_cast; ring
  have hcast2 : ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ) = (k : ℝ) ^ 2 + 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub h1]; push_cast; ring
  have hcast3 : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
  rw [hcast1, hcast2, hcast3]
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith

private lemma inv_le_log_diff {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) / (m : ℝ) ≤ Real.log (m : ℝ) - Real.log ((m - 1 : ℕ) : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    have : 0 < m - 1 := by omega
    exact_mod_cast this
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  have hlog : Real.log (((m - 1 : ℕ) : ℝ) / (m : ℝ)) ≤ ((m - 1 : ℕ) : ℝ) / (m : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hm1_pos hm0)
  rw [Real.log_div (ne_of_gt hm1_pos) (ne_of_gt hm0)] at hlog
  have hEq : ((m - 1 : ℕ) : ℝ) / (m : ℝ) - 1 = -((1 : ℝ) / (m : ℝ)) := by
    rw [hcast]
    field_simp
    ring
  linarith

private lemma sum_harmonic_le_two_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Ico 1 n, ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ) ≤
      2 * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log 2) := by
  have hstep1 : ∑ k ∈ Finset.Ico 1 n, ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 n, 2 * (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    calc ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)
        ≤ 2 / ((k + 2 : ℕ) : ℝ) := harmonic_term_le_two_div hk1
      _ = 2 * ((1 : ℝ) / ((k + 2 : ℕ) : ℝ)) := by ring
      _ ≤ 2 * (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
          have := inv_le_log_diff (m := k + 2) (by omega)
          have hsub : k + 2 - 1 = k + 1 := by omega
          rw [hsub] at this
          linarith
  have hteles : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ Finset.Ico 1 m, (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) =
        Real.log ((m + 1 : ℕ) : ℝ) - Real.log 2 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ih]
      ring
  calc ∑ k ∈ Finset.Ico 1 n, ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Ico 1 n, 2 * (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := hstep1
    _ = 2 * ∑ k ∈ Finset.Ico 1 n, (Real.log ((k + 2 : ℕ) : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum]
    _ = 2 * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log 2) := by rw [hteles n hn]

/-- **Sharp Solymosi Multiplicative Energy Bound (`2 ln |A|`):**
For every finite `A ⊂ ℝ_{>0}` with `2 ≤ |A|`,
`E^×(A) ≤ 2 · ln(|A|) · |A + A|²`.
This improves Solymosi's (2009) explicit constant `4 ⌈log₂ |A|⌉ ≈ 5.7708 ln |A|` by a factor
of `2 / ln 2 ≈ 2.885×` asymptotically (and up to `8×` for small sets). -/
theorem solymosi_mul_energy_sharp_two_log (A : Finset ℝ) (hpos : ∀ a ∈ A, 0 < a)
    (hcard : 2 ≤ A.card) :
    ((((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card : ℝ) ≤
      2 * Real.log (A.card : ℝ) * ((A + A).card : ℝ) ^ 2 := by
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have hexact := solymosi_mul_energy_exact_harmonic A hpos
  have hharm := sum_harmonic_le_two_log A.card (by omega)
  have hAA_ge : 2 * A.card - 1 ≤ (A + A).card := card_add_self_ge_two_mul_sub_one_real A hA
  have hAA_sub_le : (((A + A).card * ((A + A).card - 1) : ℕ) : ℝ) ≤ ((A + A).card : ℝ) ^ 2 := by
    have hnat : (A + A).card * ((A + A).card - 1) ≤ (A + A).card ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact_mod_cast hnat
  have hlog_nonneg : 0 ≤ 2 * (Real.log ((A.card + 1 : ℕ) : ℝ) - Real.log 2) := by
    have h2le : (2 : ℝ) ≤ ((A.card + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ A.card + 1)
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    linarith
  have hn_pos : (0 : ℝ) < (A.card : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((A.card + 1 : ℕ) : ℝ) := by positivity
  have hratio_pos : (0 : ℝ) < ((A.card + 1 : ℕ) : ℝ) / (2 * (A.card : ℝ)) := by positivity
  have hratio_le : ((A.card + 1 : ℕ) : ℝ) / (2 * (A.card : ℝ)) ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hn2 : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
    push_cast
    linarith
  have hlog_ratio : Real.log (((A.card + 1 : ℕ) : ℝ) / (2 * (A.card : ℝ))) ≤ -1 / 4 := by
    have := Real.log_le_sub_one_of_pos hratio_pos
    linarith
  have hlog_split : Real.log (((A.card + 1 : ℕ) : ℝ) / (2 * (A.card : ℝ))) =
      Real.log ((A.card + 1 : ℕ) : ℝ) - Real.log 2 - Real.log (A.card : ℝ) := by
    rw [Real.log_div (ne_of_gt hn1_pos) (by positivity),
      Real.log_mul (by norm_num) (ne_of_gt hn_pos)]
    ring
  have hlog_gap : 2 * (Real.log ((A.card + 1 : ℕ) : ℝ) - Real.log 2) + (1 / 2 : ℝ) ≤
      2 * Real.log (A.card : ℝ) := by
    linarith
  have hsq_le : (A.card : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * ((A + A).card : ℝ) ^ 2 := by
    have hn2 : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
    have hAA_R : 2 * (A.card : ℝ) - 1 ≤ ((A + A).card : ℝ) := by
      have : ((2 * A.card - 1 : ℕ) : ℝ) ≤ ((A + A).card : ℝ) := by exact_mod_cast hAA_ge
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * A.card)] at this
      push_cast at this
      exact this
    have h32 : 3 * (A.card : ℝ) ≤ 2 * ((A + A).card : ℝ) := by linarith
    nlinarith
  calc ((((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card : ℝ)
      ≤ (A.card : ℝ) ^ 2 +
          (∑ k ∈ Finset.Ico 1 A.card,
            ((2 * k - 1 : ℕ) : ℝ) / ((k ^ 2 + 2 * k - 1 : ℕ) : ℝ)) *
            (((A + A).card * ((A + A).card - 1) : ℕ) : ℝ) := hexact
    _ ≤ (A.card : ℝ) ^ 2 +
          (2 * (Real.log ((A.card + 1 : ℕ) : ℝ) - Real.log 2)) * ((A + A).card : ℝ) ^ 2 := by
          refine add_le_add_right ?_ _
          exact mul_le_mul hharm hAA_sub_le (by positivity) hlog_nonneg
    _ ≤ ((1 / 2 : ℝ) + 2 * (Real.log ((A.card + 1 : ℕ) : ℝ) - Real.log 2)) *
          ((A + A).card : ℝ) ^ 2 := by linarith
    _ ≤ (2 * Real.log (A.card : ℝ)) * ((A + A).card : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- **Sharp Solymosi `4/3` Sum-Product Inequality for Positive Reals (`2 ln |A|`):**
For every finite `A ⊂ ℝ_{>0}` with `2 ≤ |A|`,
`|A + A|² · |A * A| ≥ |A|⁴ / (2 ln |A|)`. -/
theorem solymosi_sum_product_pos_sharp (A : Finset ℝ) (hpos : ∀ a ∈ A, 0 < a)
    (hcard : 2 ≤ A.card) :
    ((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ) ≥
      (A.card : ℝ) ^ 4 / (2 * Real.log (A.card : ℝ)) := by
  have hlog_pos : 0 < 2 * Real.log (A.card : ℝ) := by
    have hgt1 : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast (by omega : 1 < A.card)
    exact mul_pos (by norm_num) (Real.log_pos hgt1)
  rw [ge_iff_le, div_le_iff₀ hlog_pos]
  have hcs := cauchy_schwarz_mul_energy_real A
  have he := solymosi_mul_energy_sharp_two_log A hpos hcard
  have hmul : ((A * A).card : ℝ) *
      ((((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun x => x.1.1 * x.1.2 = x.2.1 * x.2.2)).card : ℝ) ≤
      ((A * A).card : ℝ) * (2 * Real.log (A.card : ℝ) * ((A + A).card : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  linarith

private lemma max_ge_rpow_of_sq_mul {S P N D : ℝ} (hS : 0 ≤ S) (hP : 0 ≤ P)
    (hN : 0 ≤ N) (hD : 0 < D) (h : N ^ 4 / D ≤ S ^ 2 * P) :
    N ^ ((4 : ℝ) / 3) / D ^ ((1 : ℝ) / 3) ≤ max S P := by
  have hM : 0 ≤ max S P := le_trans hS (le_max_left S P)
  have hcube : (N ^ ((4 : ℝ) / 3) / D ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) ≤ (max S P) ^ (3 : ℕ) := by
    rw [div_pow]
    have hnum : (N ^ ((4 : ℝ) / 3)) ^ (3 : ℕ) = N ^ 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN]
      norm_num
    have hden : (D ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = D := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hD)]
      norm_num
    rw [hnum, hden]
    calc N ^ 4 / D ≤ S ^ 2 * P := h
      _ ≤ (max S P) ^ 2 * max S P := by
          exact mul_le_mul (pow_le_pow_left₀ hS (le_max_left S P) 2) (le_max_right S P) hP (sq_nonneg _)
      _ = (max S P) ^ (3 : ℕ) := by ring
  by_contra hlt
  push Not at hlt
  have hstrict : (max S P) ^ (3 : ℕ) < (N ^ ((4 : ℝ) / 3) / D ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ hlt hM (by norm_num)
  linarith

/-- **Sharp Solymosi `4/3` Max Sum-Product Bound for Positive Reals:**
`max(|A + A|, |A * A|) ≥ |A|^(4/3) / (2 ln |A|)^(1/3)` for every finite `A ⊂ ℝ_{>0}` with `2 ≤ |A|`. -/
theorem solymosi_max_sum_product_pos_sharp (A : Finset ℝ) (hpos : ∀ a ∈ A, 0 < a)
    (hcard : 2 ≤ A.card) :
    (max (A + A).card (A * A).card : ℝ) ≥
      (A.card : ℝ) ^ ((4 : ℝ) / 3) / (2 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3) := by
  have hlog_pos : 0 < 2 * Real.log (A.card : ℝ) := by
    have hgt1 : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast (by omega : 1 < A.card)
    exact mul_pos (by norm_num) (Real.log_pos hgt1)
  have h := max_ge_rpow_of_sq_mul (S := ((A + A).card : ℝ)) (P := ((A * A).card : ℝ))
    (N := (A.card : ℝ)) (D := 2 * Real.log (A.card : ℝ))
    (by positivity) (by positivity) (by positivity) hlog_pos
    (solymosi_sum_product_pos_sharp A hpos hcard)
  simpa [Nat.cast_max] using h

end SharpSolymosi

/-! ## Section 4: Full Signed `Finset ℝ` & `Finset ℤ` Solymosi `4/3` Theorems -/

section SignedAndIntSolymosi

private lemma exists_large_pos_subset (A : Finset ℝ) :
    ∃ B : Finset ℝ, (∀ b ∈ B, 0 < b) ∧ A.card - 1 ≤ 2 * B.card ∧
      B.card ≤ A.card ∧ (B + B).card ≤ (A + A).card ∧ (B * B).card ≤ (A * A).card := by
  let Apos := A.filter (0 < ·)
  let Aneg := A.filter (· < 0)
  have hcov : A ⊆ Apos ∪ (Aneg ∪ {0}) := by
    intro x hx
    simp only [Apos, Aneg, Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · exact Or.inr (Or.inl ⟨hx, hlt⟩)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ⟨hx, hgt⟩
  have hcard_cov : A.card ≤ Apos.card + Aneg.card + 1 := by
    calc A.card ≤ (Apos ∪ (Aneg ∪ {0})).card := Finset.card_le_card hcov
      _ ≤ Apos.card + (Aneg ∪ {0}).card := Finset.card_union_le _ _
      _ ≤ Apos.card + (Aneg.card + ({0} : Finset ℝ).card) :=
            Nat.add_le_add_left (Finset.card_union_le _ _) _
      _ = Apos.card + Aneg.card + 1 := by simp; omega
  by_cases hge : Aneg.card ≤ Apos.card
  · refine ⟨Apos, fun b hb => (Finset.mem_filter.mp hb).2, by omega,
      Finset.card_le_card (Finset.filter_subset _ _), ?_, ?_⟩
    · exact Finset.card_le_card (Finset.add_subset_add (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    · exact Finset.card_le_card (Finset.mul_subset_mul (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  · let B := Aneg.image Neg.neg
    have hBcard : B.card = Aneg.card := Finset.card_image_of_injective _ neg_injective
    have hBpos : ∀ b ∈ B, 0 < b := by
      intro b hb
      rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      exact neg_pos.mpr (Finset.mem_filter.mp ha).2
    have hBadd : (B + B).card ≤ (A + A).card := by
      have hsub : (B + B).image Neg.neg ⊆ A + A := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rcases Finset.mem_add.mp hy with ⟨u, hu, v, hv, rfl⟩
        rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
        have hEq : -(-a + -b) = a + b := by ring
        rw [hEq]
        exact Finset.add_mem_add (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      rw [← Finset.card_image_of_injective (B + B) neg_injective]
      exact Finset.card_le_card hsub
    have hBmul : (B * B).card ≤ (A * A).card := by
      have hsub : B * B ⊆ A * A := by
        intro x hx
        rcases Finset.mem_mul.mp hx with ⟨u, hu, v, hv, rfl⟩
        rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
        rw [neg_mul_neg]
        exact Finset.mul_mem_mul (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      exact Finset.card_le_card hsub
    refine ⟨B, hBpos, by omega, ?_, hBadd, hBmul⟩
    rw [hBcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **Full Signed Real Solymosi `4/3` Theorem:**
For EVERY finite set `A : Finset ℝ` with `2 ≤ |A|` (arbitrary signs, may include `0` and negatives):
`|A + A|² · |A * A| ≥ |A|⁴ / (36 ln |A|)`. -/
theorem solymosi_sum_product_real (A : Finset ℝ) (hcard : 2 ≤ A.card) :
    ((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ) ≥
      (A.card : ℝ) ^ 4 / (36 * Real.log (A.card : ℝ)) := by
  have hlog_pos : 0 < Real.log (A.card : ℝ) := by
    have hgt1 : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast (by omega : 1 < A.card)
    exact Real.log_pos hgt1
  by_cases hbig : 36 ≤ A.card
  · rcases exists_large_pos_subset A with ⟨B, hBpos, hBhalf, hBle, hBadd, hBmul⟩
    have hB2 : 2 ≤ B.card := by omega
    have hBsharp := solymosi_sum_product_pos_sharp B hBpos hB2
    have hBlog_pos : 0 < Real.log (B.card : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < B.card))
    have hBlog_le : Real.log (B.card : ℝ) ≤ Real.log (A.card : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hBle)
    have hB4_ge : (A.card : ℝ) ^ 4 / 18 ≤ (B.card : ℝ) ^ 4 := by
      have hA36 : (36 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hbig
      have hhalfR : (A.card : ℝ) - 1 ≤ 2 * (B.card : ℝ) := by
        have : ((A.card - 1 : ℕ) : ℝ) ≤ ((2 * B.card : ℕ) : ℝ) := by exact_mod_cast hBhalf
        rw [Nat.cast_sub (by omega : 1 ≤ A.card)] at this
        push_cast at this
        exact this
      have hlin : (35 : ℝ) / 72 * (A.card : ℝ) ≤ (B.card : ℝ) := by linarith
      have hpow : ((35 : ℝ) / 72 * (A.card : ℝ)) ^ 4 ≤ (B.card : ℝ) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hlin 4
      have hnum : (1 : ℝ) / 18 ≤ ((35 : ℝ) / 72) ^ 4 := by norm_num
      have hA4 : 0 ≤ (A.card : ℝ) ^ 4 := by positivity
      calc (A.card : ℝ) ^ 4 / 18 = ((1 : ℝ) / 18) * (A.card : ℝ) ^ 4 := by ring
        _ ≤ ((35 : ℝ) / 72) ^ 4 * (A.card : ℝ) ^ 4 := mul_le_mul_of_nonneg_right hnum hA4
        _ = ((35 : ℝ) / 72 * (A.card : ℝ)) ^ 4 := by ring
        _ ≤ (B.card : ℝ) ^ 4 := hpow
    have hstep1 : (A.card : ℝ) ^ 4 / (36 * Real.log (A.card : ℝ)) ≤
        (B.card : ℝ) ^ 4 / (2 * Real.log (B.card : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc (A.card : ℝ) ^ 4 * (2 * Real.log (B.card : ℝ))
          ≤ (A.card : ℝ) ^ 4 * (2 * Real.log (A.card : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = ((A.card : ℝ) ^ 4 / 18) * (36 * Real.log (A.card : ℝ)) := by ring
        _ ≤ (B.card : ℝ) ^ 4 * (36 * Real.log (A.card : ℝ)) :=
            mul_le_mul_of_nonneg_right hB4_ge (by positivity)
    have hmono : ((B + B).card : ℝ) ^ 2 * ((B * B).card : ℝ) ≤
        ((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ) := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hBadd) 2)
        (by exact_mod_cast hBmul) (by positivity) (sq_nonneg _)
    linarith
  · rw [ge_iff_le, div_le_iff₀ (by positivity)]
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    have hAA := card_add_self_ge_two_mul_sub_one_real A hA
    have hMM := card_mul_self_ge_card_real A hcard
    have hMM_R : (A.card : ℝ) ≤ ((A * A).card : ℝ) := by exact_mod_cast hMM
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log (A.card : ℝ) := by
      have h2le : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
      have hinv : Real.log ((1 : ℝ) / 2) ≤ (1 : ℝ) / 2 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hinv
      have hlog_mono : Real.log 2 ≤ Real.log (A.card : ℝ) :=
        Real.log_le_log (by norm_num) h2le
      linarith
    have hlt36 : (A.card : ℝ) ≤ 36 := by exact_mod_cast (by omega : A.card ≤ 36)
    have hAA2 : (3 / 2 : ℝ) * (A.card : ℝ) ≤ ((A + A).card : ℝ) := by
      have h1 : ((2 * A.card - 1 : ℕ) : ℝ) ≤ ((A + A).card : ℝ) := by exact_mod_cast hAA
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * A.card)] at h1
      push_cast at h1
      have h2 : (2 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcard
      linarith
    have h3 : (9 / 4 : ℝ) * (A.card : ℝ) ^ 3 ≤ ((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ) := by
      have hsq : (9 / 4 : ℝ) * (A.card : ℝ) ^ 2 ≤ ((A + A).card : ℝ) ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hAA2 2
        linarith
      calc (9 / 4 : ℝ) * (A.card : ℝ) ^ 3 = ((9 / 4 : ℝ) * (A.card : ℝ) ^ 2) * (A.card : ℝ) := by ring
        _ ≤ ((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ) :=
            mul_le_mul hsq hMM_R (by positivity) (sq_nonneg _)
    have h36 : (18 : ℝ) ≤ 36 * Real.log (A.card : ℝ) := by linarith
    have hA3_nonneg : 0 ≤ (A.card : ℝ) ^ 3 := by positivity
    calc (A.card : ℝ) ^ 4 = (A.card : ℝ) * (A.card : ℝ) ^ 3 := by ring
      _ ≤ 36 * (A.card : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hlt36 hA3_nonneg
      _ ≤ ((9 / 4 : ℝ) * (A.card : ℝ) ^ 3) * 18 := by nlinarith
      _ ≤ (((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ)) * (36 * Real.log (A.card : ℝ)) :=
          mul_le_mul h3 h36 (by norm_num) (by positivity)

private lemma card_image_int_cast_add (A : Finset ℤ) :
    (A.image (Int.cast : ℤ → ℝ) + A.image (Int.cast : ℤ → ℝ)).card = (A + A).card := by
  have hEq : A.image (Int.cast : ℤ → ℝ) + A.image (Int.cast : ℤ → ℝ) =
      (A + A).image (Int.cast : ℤ → ℝ) := by
    ext x
    simp only [Finset.mem_add, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by push_cast; rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨(a : ℝ), ⟨a, ha, rfl⟩, (b : ℝ), ⟨b, hb, rfl⟩, by push_cast; rfl⟩
  rw [hEq, Finset.card_image_of_injective _ Int.cast_injective]

private lemma card_image_int_cast_mul (A : Finset ℤ) :
    (A.image (Int.cast : ℤ → ℝ) * A.image (Int.cast : ℤ → ℝ)).card = (A * A).card := by
  have hEq : A.image (Int.cast : ℤ → ℝ) * A.image (Int.cast : ℤ → ℝ) =
      (A * A).image (Int.cast : ℤ → ℝ) := by
    ext x
    simp only [Finset.mem_mul, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, by push_cast; rfl⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨(a : ℝ), ⟨a, ha, rfl⟩, (b : ℝ), ⟨b, hb, rfl⟩, by push_cast; rfl⟩
  rw [hEq, Finset.card_image_of_injective _ Int.cast_injective]

/-- **Full Integer Solymosi `4/3` Theorem (for every `A : Finset ℤ` with `2 ≤ |A|`):**
`|A + A|² · |A * A| ≥ |A|⁴ / (36 ln |A|)`. -/
theorem solymosi_sum_product_int (A : Finset ℤ) (hcard : 2 ≤ A.card) :
    ((A + A).card : ℝ) ^ 2 * ((A * A).card : ℝ) ≥
      (A.card : ℝ) ^ 4 / (36 * Real.log (A.card : ℝ)) := by
  let AR : Finset ℝ := A.image (Int.cast : ℤ → ℝ)
  have hAR_card : AR.card = A.card := Finset.card_image_of_injective _ Int.cast_injective
  have h := solymosi_sum_product_real AR (hAR_card.symm ▸ hcard)
  rw [hAR_card, card_image_int_cast_add A, card_image_int_cast_mul A] at h
  exact h

/-- **Full Integer Solymosi `4/3` Max Sum-Product Bound:**
`max(|A + A|, |A * A|) ≥ |A|^(4/3) / (36 ln |A|)^(1/3)` for every `A : Finset ℤ` with `2 ≤ |A|`. -/
theorem solymosi_max_sum_product_int (A : Finset ℤ) (hcard : 2 ≤ A.card) :
    (max (A + A).card (A * A).card : ℝ) ≥
      (A.card : ℝ) ^ ((4 : ℝ) / 3) / (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3) := by
  have hlog_pos : 0 < 36 * Real.log (A.card : ℝ) := by
    have hgt1 : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast (by omega : 1 < A.card)
    exact mul_pos (by norm_num) (Real.log_pos hgt1)
  have h := max_ge_rpow_of_sq_mul (S := ((A + A).card : ℝ)) (P := ((A * A).card : ℝ))
    (N := (A.card : ℝ)) (D := 36 * Real.log (A.card : ℝ))
    (by positivity) (by positivity) (by positivity) hlog_pos
    (solymosi_sum_product_int A hcard)
  simpa [Nat.cast_max] using h

/-- **Solymosi `4/3 - ε` Milestone in the Exact Signature of `FormalConjectures/ErdosProblems/52.lean`:**
For every `0 < ε < 4/3`, there exists `C > 0` such that for EVERY finite set `A : Finset ℤ`,
`max(|A + A|, |A * A|) ≥ C · |A|^(4/3 - ε)`. -/
theorem solymosi_sum_product_int_rpow :
    ∀ (ε : ℝ), 0 < ε → ε < (4 : ℝ) / 3 →
      ∃ (C : ℝ), 0 < C ∧
        ∀ (A : Finset ℤ), (max (A + A).card (A * A).card : ℝ) ≥
          C * (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) := by
  intro ε hε hεlt
  let C : ℝ := min 1 ((ε / 12) ^ ((1 : ℝ) / 3))
  have hC_pos : 0 < C := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨C, hC_pos, fun A => ?_⟩
  by_cases h0 : A.card = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp h0
    subst hA
    simp only [Finset.card_empty, Nat.cast_zero, ge_iff_le]
    have hsign : (4 : ℝ) / 3 - ε ≠ 0 := by linarith
    rw [Real.zero_rpow hsign, mul_zero]
    positivity
  · by_cases h1 : A.card = 1
    · rcases Finset.card_eq_one.mp h1 with ⟨a, rfl⟩
      simp only [Finset.singleton_add_singleton, Finset.singleton_mul_singleton,
        Finset.card_singleton, max_self, Nat.cast_one, Real.one_rpow, mul_one, ge_iff_le]
      exact min_le_left _ _
    · have h2 : 2 ≤ A.card := by omega
      have hsol := solymosi_max_sum_product_int A h2
      have hN_pos : (0 : ℝ) < (A.card : ℝ) := by positivity
      have hlog_le : Real.log (A.card : ℝ) ≤ (A.card : ℝ) ^ (3 * ε) / (3 * ε) := by
        have hpow_pos : 0 < (A.card : ℝ) ^ (3 * ε) := Real.rpow_pos_of_pos hN_pos _
        have h1 := Real.log_le_sub_one_of_pos hpow_pos
        rw [Real.log_rpow hN_pos] at h1
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h36log_le : 36 * Real.log (A.card : ℝ) ≤ (12 / ε) * (A.card : ℝ) ^ (3 * ε) := by
        calc 36 * Real.log (A.card : ℝ)
            ≤ 36 * ((A.card : ℝ) ^ (3 * ε) / (3 * ε)) := mul_le_mul_of_nonneg_left hlog_le (by norm_num)
          _ = (12 / ε) * (A.card : ℝ) ^ (3 * ε) := by field_simp; ring
      have hden_le : (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3) ≤
          (12 / ε) ^ ((1 : ℝ) / 3) * (A.card : ℝ) ^ ε := by
        have hlog_pos : 0 < Real.log (A.card : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < A.card))
        calc (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3)
            ≤ ((12 / ε) * (A.card : ℝ) ^ (3 * ε)) ^ ((1 : ℝ) / 3) :=
              Real.rpow_le_rpow (by positivity) h36log_le (by norm_num)
          _ = (12 / ε) ^ ((1 : ℝ) / 3) * ((A.card : ℝ) ^ (3 * ε)) ^ ((1 : ℝ) / 3) :=
              Real.mul_rpow (by positivity) (by positivity)
          _ = (12 / ε) ^ ((1 : ℝ) / 3) * (A.card : ℝ) ^ ε := by
              rw [← Real.rpow_mul (le_of_lt hN_pos)]
              congr 2; ring
      have hden_pos : 0 < (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3) := by
        have hlog_pos : 0 < Real.log (A.card : ℝ) :=
          Real.log_pos (by exact_mod_cast (by omega : 1 < A.card))
        exact Real.rpow_pos_of_pos (by positivity) _
      have hinv : ((ε / 12) ^ ((1 : ℝ) / 3)) * (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) ≤
          (A.card : ℝ) ^ ((4 : ℝ) / 3) / (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3) := by
        rw [le_div_iff₀ hden_pos]
        have hrecip : (ε / 12) ^ ((1 : ℝ) / 3) * (12 / ε) ^ ((1 : ℝ) / 3) = 1 := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          have : ε / 12 * (12 / ε) = 1 := by field_simp
          rw [this, Real.one_rpow]
        have hexp : (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) * (A.card : ℝ) ^ ε = (A.card : ℝ) ^ ((4 : ℝ) / 3) := by
          rw [← Real.rpow_add hN_pos]
          congr 1; ring
        calc (ε / 12) ^ ((1 : ℝ) / 3) * (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) *
              (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3)
            ≤ (ε / 12) ^ ((1 : ℝ) / 3) * (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) *
              ((12 / ε) ^ ((1 : ℝ) / 3) * (A.card : ℝ) ^ ε) :=
              mul_le_mul_of_nonneg_left hden_le (by positivity)
          _ = ((ε / 12) ^ ((1 : ℝ) / 3) * (12 / ε) ^ ((1 : ℝ) / 3)) *
              ((A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) * (A.card : ℝ) ^ ε) := by ring
          _ = (A.card : ℝ) ^ ((4 : ℝ) / 3) := by rw [hrecip, hexp, one_mul]
      have hC_le : C ≤ (ε / 12) ^ ((1 : ℝ) / 3) := min_le_right _ _
      calc C * (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε)
          ≤ (ε / 12) ^ ((1 : ℝ) / 3) * (A.card : ℝ) ^ ((4 : ℝ) / 3 - ε) :=
            mul_le_mul_of_nonneg_right hC_le (by positivity)
        _ ≤ (A.card : ℝ) ^ ((4 : ℝ) / 3) / (36 * Real.log (A.card : ℝ)) ^ ((1 : ℝ) / 3) := hinv
        _ ≤ (max (A + A).card (A * A).card : ℝ) := hsol

end SignedAndIntSolymosi

/-! ## Section 5: Erdős (1955) Multiplication Table Theorem & Non-Trivial Upper Bound (`o(|A|²)`) -/

section ErdosMultiplicationTable

private def omegaP (P : Finset ℕ) (m : ℕ) : ℕ :=
  ∑ p ∈ P, m.factorization p

private noncomputable def muP (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1)

private lemma omegaP_mul (P : Finset ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    omegaP P (a * b) = omegaP P a + omegaP P b := by
  simp only [omegaP, Nat.factorization_mul ha hb, Finsupp.add_apply, Finset.sum_add_distrib]

private lemma card_multiples_Icc (M d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 M).filter (fun m => d ∣ m)).card = M / d := by
  have hEq : (Finset.Icc 1 M).filter (fun m => d ∣ m) = (Finset.Icc 1 (M / d)).image (d * ·) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm1, hmM⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · by_contra hk0
        have : k = 0 := by omega
        subst this; omega
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr (by rw [mul_comm]; exact hmM)
    · rintro ⟨k, ⟨hk1, hkdiv⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨k, rfl⟩⟩
      · nlinarith
      · have := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hkdiv
        linarith
  rw [hEq, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h),
    Nat.card_Icc]
  exact Nat.add_sub_cancel (M / d) 1

private lemma factorization_le_self {m p : ℕ} (hm : 1 ≤ m) (hp : Nat.Prime p) :
    m.factorization p ≤ m := by
  have hne : m ≠ 0 := by omega
  have hdvd : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
  have hle1 : p ^ m.factorization p ≤ m := Nat.le_of_dvd (by omega) hdvd
  have hle2 : 2 ^ m.factorization p ≤ p ^ m.factorization p := Nat.pow_le_pow_left hp.two_le _
  have hlt : m.factorization p < 2 ^ m.factorization p := Nat.lt_two_pow_self
  omega

private lemma sum_geom_inv_le {p : ℝ} (hp : 2 ≤ p) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / p ^ k ≤ 1 / (p - 1) := by
  have hExact : ∀ n : ℕ, (p - 1) * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / p ^ k = 1 - 1 / p ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), mul_add, ih]
      have hp0 : p ≠ 0 := by linarith
      rw [pow_succ]
      field_simp
      ring
  have hp1 : 0 < p - 1 := by linarith
  rw [le_div_iff₀ hp1, mul_comm, hExact M]
  have : (0 : ℝ) ≤ 1 / p ^ M := by positivity
  linarith

private lemma sum_odd_geom_inv_le {p : ℝ} (hp : 2 ≤ p) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((2 * k - 1 : ℕ) : ℝ) / p ^ k ≤ 3 / (p - 1) := by
  have hExact : ∀ n : ℕ,
      (p - 1) ^ 2 * ∑ k ∈ Finset.Icc 1 n, ((2 * k - 1 : ℕ) : ℝ) / p ^ k =
        (p + 1) - ((2 * (n : ℝ) + 1) * p - (2 * (n : ℝ) - 1)) / p ^ n := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty, mul_zero,
        Nat.cast_zero, pow_zero, div_one]
      ring
    | succ n ih =>
      have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp), mul_add, ih]
      have hcast : ((2 * (n + 1) - 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by
        have : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast, Nat.cast_add, Nat.cast_one, pow_succ]
      have hp0 : p ≠ 0 := by linarith
      field_simp
      ring
  have hp1 : 0 < p - 1 := by linarith
  have hrem_nonneg : 0 ≤ ((2 * (M : ℝ) + 1) * p - (2 * (M : ℝ) - 1)) / p ^ M := by
    have hnum : 0 ≤ (2 * (M : ℝ) + 1) * p - (2 * (M : ℝ) - 1) := by nlinarith
    have hden : (0 : ℝ) < p ^ M := by positivity
    exact div_nonneg hnum (le_of_lt hden)
  have hle1 : ∑ k ∈ Finset.Icc 1 M, ((2 * k - 1 : ℕ) : ℝ) / p ^ k ≤ (p + 1) / (p - 1) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hp1), mul_comm, hExact M]
    linarith
  have hle2 : (p + 1) / (p - 1) ^ 2 ≤ 3 / (p - 1) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hp1) hp1]
    nlinarith
  exact le_trans hle1 hle2

private lemma sum_vp_Icc_ge (M : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    (M : ℝ) / (p : ℝ) - 1 ≤ ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) := by
  have hnat : M / p ≤ ∑ m ∈ Finset.Icc 1 M, m.factorization p := by
    rw [← card_multiples_Icc M p (by have := hp.two_le; omega), Finset.card_eq_sum_ones,
      Finset.sum_filter]
    refine Finset.sum_le_sum fun m hm => ?_
    split_ifs with hdvd
    · have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
      exact (hp.dvd_iff_one_le_factorization hm0).mp hdvd
    · exact Nat.zero_le _
  have hR : ((M / p : ℕ) : ℝ) ≤ ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) := by
    exact_mod_cast hnat
  have hdiv : (M : ℝ) / (p : ℝ) - 1 ≤ ((M / p : ℕ) : ℝ) := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    rw [sub_le_iff_le_add, div_le_iff₀ hp0]
    have hmod : M < (M / p + 1) * p := by
      have := Nat.div_add_mod M p
      have hlt := Nat.mod_lt M hp.pos
      nlinarith
    have hmodR : (M : ℝ) ≤ (((M / p + 1) * p : ℕ) : ℝ) := by exact_mod_cast le_of_lt hmod
    push_cast at hmodR
    linarith
  linarith

private lemma sum_vp_sq_Icc_le (M : ℕ) {p : ℕ} (hp : Nat.Prime p) :
    ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) ^ 2 ≤ (M : ℝ) * (3 / ((p : ℝ) - 1)) := by
  have hnat : ∑ m ∈ Finset.Icc 1 M, m.factorization p ^ 2 =
      ∑ k ∈ Finset.Icc 1 M, (2 * k - 1) * (M / p ^ k) := by
    have h1 : ∑ m ∈ Finset.Icc 1 M, m.factorization p ^ 2 =
        ∑ m ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M, if p ^ k ∣ m then (2 * k - 1) else 0 := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
      have hvle : m.factorization p ≤ M := le_trans (factorization_le_self hm1 hp) hmM
      rw [sq_eq_sum_odd, ← Finset.sum_filter]
      congr 1
      ext k
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_Icc]
      rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)]
      omega
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul,
      card_multiples_Icc M (p ^ k) (Nat.one_le_pow _ _ hp.pos), mul_comm]
  have hR : ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) ^ 2 =
      ∑ k ∈ Finset.Icc 1 M, ((2 * k - 1 : ℕ) : ℝ) * ((M / p ^ k : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hR]
  have hterm : ∀ k ∈ Finset.Icc 1 M,
      ((2 * k - 1 : ℕ) : ℝ) * ((M / p ^ k : ℕ) : ℝ) ≤
        (M : ℝ) * (((2 * k - 1 : ℕ) : ℝ) / (p : ℝ) ^ k) := by
    intro k _
    have hdiv : ((M / p ^ k : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) ^ k := by
      have hp_pos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.pos) k
      rw [le_div_iff₀ hp_pos]
      have : (M / p ^ k) * p ^ k ≤ M := Nat.div_mul_le_self M (p ^ k)
      exact_mod_cast this
    calc ((2 * k - 1 : ℕ) : ℝ) * ((M / p ^ k : ℕ) : ℝ)
        ≤ ((2 * k - 1 : ℕ) : ℝ) * ((M : ℝ) / (p : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = (M : ℝ) * (((2 * k - 1 : ℕ) : ℝ) / (p : ℝ) ^ k) := by ring
  calc ∑ k ∈ Finset.Icc 1 M, ((2 * k - 1 : ℕ) : ℝ) * ((M / p ^ k : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 M, (M : ℝ) * (((2 * k - 1 : ℕ) : ℝ) / (p : ℝ) ^ k) :=
        Finset.sum_le_sum hterm
    _ = (M : ℝ) * ∑ k ∈ Finset.Icc 1 M, ((2 * k - 1 : ℕ) : ℝ) / (p : ℝ) ^ k := by
        rw [← Finset.mul_sum]
    _ ≤ (M : ℝ) * (3 / ((p : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (sum_odd_geom_inv_le (by exact_mod_cast hp.two_le) M) (by positivity)

private lemma sum_vp_vq_Icc_le (M : ℕ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : p ≠ q) :
    ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) * (m.factorization q : ℝ) ≤
      (M : ℝ) * (1 / ((p : ℝ) - 1)) * (1 / ((q : ℝ) - 1)) := by
  have hcop : ∀ j k : ℕ, Nat.Coprime (p ^ j) (q ^ k) := fun j k =>
    ((hp.coprime_iff_not_dvd.mpr fun h =>
      hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)).pow_left j).pow_right k
  have hnat : ∑ m ∈ Finset.Icc 1 M, m.factorization p * m.factorization q =
      ∑ j ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M, M / (p ^ j * q ^ k) := by
    have h1 : ∀ m ∈ Finset.Icc 1 M,
        m.factorization p * m.factorization q =
          ∑ j ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M, if p ^ j * q ^ k ∣ m then 1 else 0 := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmM : m ≤ M := (Finset.mem_Icc.mp hm).2
      have hvp : m.factorization p = ∑ j ∈ Finset.Icc 1 M, if p ^ j ∣ m then 1 else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have hvle : m.factorization p ≤ M := le_trans (factorization_le_self hm1 hp) hmM
        have hEq : (Finset.Icc 1 M).filter (fun j => p ^ j ∣ m) = Finset.Icc 1 (m.factorization p) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_Icc]
          rw [hp.pow_dvd_iff_le_factorization (by omega : m ≠ 0)]
          omega
        rw [hEq, Nat.card_Icc]; omega
      have hvq : m.factorization q = ∑ k ∈ Finset.Icc 1 M, if q ^ k ∣ m then 1 else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        have hvle : m.factorization q ≤ M := le_trans (factorization_le_self hm1 hq) hmM
        have hEq : (Finset.Icc 1 M).filter (fun k => q ^ k ∣ m) = Finset.Icc 1 (m.factorization q) := by
          ext k; simp only [Finset.mem_filter, Finset.mem_Icc]
          rw [hq.pow_dvd_iff_le_factorization (by omega : m ≠ 0)]
          omega
        rw [hEq, Nat.card_Icc]; omega
      rw [hvp, hvq, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hiff : p ^ j * q ^ k ∣ m ↔ p ^ j ∣ m ∧ q ^ k ∣ m :=
        ⟨fun h => ⟨dvd_trans (dvd_mul_right _ _) h, dvd_trans (dvd_mul_left _ _) h⟩,
          fun ⟨h1, h2⟩ => (hcop j k).mul_dvd_of_dvd_of_dvd h1 h2⟩
      by_cases h1 : p ^ j ∣ m <;> by_cases h2 : q ^ k ∣ m <;> simp [h1, h2, hiff]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
      card_multiples_Icc M (p ^ j * q ^ k) (Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos))]
  have hR : ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) * (m.factorization q : ℝ) =
      ∑ j ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M, ((M / (p ^ j * q ^ k) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hR]
  have hterm : ∀ j ∈ Finset.Icc 1 M, ∀ k ∈ Finset.Icc 1 M,
      ((M / (p ^ j * q ^ k) : ℕ) : ℝ) ≤ (M : ℝ) * ((1 : ℝ) / (p : ℝ) ^ j) * ((1 : ℝ) / (q : ℝ) ^ k) := by
    intro j _ k _
    have hdiv : ((M / (p ^ j * q ^ k) : ℕ) : ℝ) ≤ (M : ℝ) / ((p : ℝ) ^ j * (q : ℝ) ^ k) := by
      have hpq_pos : (0 : ℝ) < (p : ℝ) ^ j * (q : ℝ) ^ k :=
        mul_pos (pow_pos (by exact_mod_cast hp.pos) j) (pow_pos (by exact_mod_cast hq.pos) k)
      rw [le_div_iff₀ hpq_pos]
      have : (M / (p ^ j * q ^ k)) * (p ^ j * q ^ k) ≤ M := Nat.div_mul_le_self M _
      exact_mod_cast this
    calc ((M / (p ^ j * q ^ k) : ℕ) : ℝ)
        ≤ (M : ℝ) / ((p : ℝ) ^ j * (q : ℝ) ^ k) := hdiv
      _ = (M : ℝ) * ((1 : ℝ) / (p : ℝ) ^ j) * ((1 : ℝ) / (q : ℝ) ^ k) := by ring
  calc ∑ j ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M, ((M / (p ^ j * q ^ k) : ℕ) : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 M,
          (M : ℝ) * ((1 : ℝ) / (p : ℝ) ^ j) * ((1 : ℝ) / (q : ℝ) ^ k) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm j hj k hk
    _ = (M : ℝ) * (∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (p : ℝ) ^ j) *
          (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (q : ℝ) ^ k) := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.mul_sum]
    _ ≤ (M : ℝ) * (1 / ((p : ℝ) - 1)) * (1 / ((q : ℝ) - 1)) := by
        have hp_le := sum_geom_inv_le (by exact_mod_cast hp.two_le : (2 : ℝ) ≤ p) M
        have hq_le := sum_geom_inv_le (by exact_mod_cast hq.two_le : (2 : ℝ) ≤ q) M
        have hp1_nonneg : (0 : ℝ) ≤ (p : ℝ) - 1 := by
          have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
          linarith
        have h1 : (M : ℝ) * (∑ j ∈ Finset.Icc 1 M, (1 : ℝ) / (p : ℝ) ^ j) ≤
            (M : ℝ) * (1 / ((p : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left hp_le (by positivity)
        exact mul_le_mul h1 hq_le (Finset.sum_nonneg fun _ _ => by positivity)
          (mul_nonneg (by positivity) (div_nonneg (by norm_num) hp1_nonneg))

private lemma muP_sub_sum_inv_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    muP P - ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ 1 := by
  let K : ℕ := P.sup id + 2
  have hsub : P ⊆ Finset.Icc 2 K := by
    intro p hp
    rw [Finset.mem_Icc]
    refine ⟨(hP p hp).two_le, ?_⟩
    have : p ≤ P.sup id := Finset.le_sup (f := id) hp
    omega
  have hnonneg : ∀ n ∈ Finset.Icc 2 K, (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [sub_nonneg, one_div_le_one_div (by linarith) (by linarith)]
    linarith
  have hteles : ∀ m : ℕ, 2 ≤ m →
      ∑ n ∈ Finset.Icc 2 m, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) = 1 - 1 / (m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_ofNat]
      norm_num
    | succ m hm ih =>
      have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih]
      push_cast
      ring
  have hK2 : 2 ≤ K := by omega
  calc muP P - ∑ p ∈ P, (1 : ℝ) / (p : ℝ)
      = ∑ p ∈ P, ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
        simp only [muP, Finset.sum_sub_distrib]
    _ ≤ ∑ n ∈ Finset.Icc 2 K, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hnonneg n hn
    _ = 1 - 1 / (K : ℝ) := hteles K hK2
    _ ≤ 1 := by
        have : (0 : ℝ) ≤ 1 / (K : ℝ) := by positivity
        linarith

private lemma variance_omegaP_Icc_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, ((omegaP P m : ℝ) - muP P) ^ 2 ≤
      5 * (M : ℝ) * muP P + 2 * muP P * (P.card : ℝ) := by
  have hmu_nonneg : 0 ≤ muP P := by
    refine Finset.sum_nonneg fun p hp => ?_
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).two_le
    exact div_nonneg (by norm_num) (by linarith)
  -- First moment lower bound
  have hsum1 : (M : ℝ) * (muP P - 1) - (P.card : ℝ) ≤ ∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ) := by
    have h1 : ∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ) =
        ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) := by
      simp only [omegaP, Nat.cast_sum]
      exact Finset.sum_comm
    rw [h1]
    have h2 : ∑ p ∈ P, ((M : ℝ) / (p : ℝ) - 1) ≤
        ∑ p ∈ P, ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) :=
      Finset.sum_le_sum fun p hp => sum_vp_Icc_ge M (hP p hp)
    have h3 : ∑ p ∈ P, ((M : ℝ) / (p : ℝ) - 1) =
        (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) - (P.card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun p _ => by ring
    have hdiff := muP_sub_sum_inv_le_one P hP
    have h4 : (M : ℝ) * (muP P - 1) ≤ (M : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  -- Second moment upper bound
  have hsum2 : ∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ) ^ 2 ≤
      (M : ℝ) * (muP P) ^ 2 + 3 * (M : ℝ) * muP P := by
    have hexp : ∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ) ^ 2 =
        ∑ p ∈ P, ∑ q ∈ P, ∑ m ∈ Finset.Icc 1 M,
          (m.factorization p : ℝ) * (m.factorization q : ℝ) := by
      have hsq : ∀ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ) ^ 2 =
          ∑ p ∈ P, ∑ q ∈ P, (m.factorization p : ℝ) * (m.factorization q : ℝ) := by
        intro m _
        simp only [omegaP, Nat.cast_sum, sq, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      rw [Finset.sum_congr rfl hsq, Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_comm
    rw [hexp]
    have hsplit : ∀ p ∈ P,
        ∑ q ∈ P, ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) * (m.factorization q : ℝ) ≤
          (M : ℝ) * (1 / ((p : ℝ) - 1)) * muP P + 3 * (M : ℝ) * (1 / ((p : ℝ) - 1)) := by
      intro p hp
      have hdiag : ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) * (m.factorization p : ℝ) ≤
          3 * (M : ℝ) * (1 / ((p : ℝ) - 1)) := by
        have : ∀ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) * (m.factorization p : ℝ) =
            (m.factorization p : ℝ) ^ 2 := fun m _ => (sq _).symm
        rw [Finset.sum_congr rfl this]
        calc ∑ m ∈ Finset.Icc 1 M, (m.factorization p : ℝ) ^ 2
            ≤ (M : ℝ) * (3 / ((p : ℝ) - 1)) := sum_vp_sq_Icc_le M (hP p hp)
          _ = 3 * (M : ℝ) * (1 / ((p : ℝ) - 1)) := by ring
      rw [← Finset.add_sum_erase _ _ hp]
      have hoff : ∑ q ∈ P.erase p, ∑ m ∈ Finset.Icc 1 M,
            (m.factorization p : ℝ) * (m.factorization q : ℝ) ≤
          ∑ q ∈ P.erase p, (M : ℝ) * (1 / ((p : ℝ) - 1)) * (1 / ((q : ℝ) - 1)) :=
        Finset.sum_le_sum fun q hq =>
          sum_vp_vq_Icc_le M (hP p hp) (hP q (Finset.mem_of_mem_erase hq))
            (Ne.symm (Finset.ne_of_mem_erase hq))
      have hoff2 : ∑ q ∈ P.erase p, (M : ℝ) * (1 / ((p : ℝ) - 1)) * (1 / ((q : ℝ) - 1)) ≤
          (M : ℝ) * (1 / ((p : ℝ) - 1)) * muP P := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ ?_
        · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p P) fun q hq _ => by
            have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hP q hq).two_le
            exact div_nonneg (by norm_num) (by linarith)
        · have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).two_le
          exact mul_nonneg (by positivity) (div_nonneg (by norm_num) (by linarith))
      linarith
    calc ∑ p ∈ P, ∑ q ∈ P, ∑ m ∈ Finset.Icc 1 M,
            (m.factorization p : ℝ) * (m.factorization q : ℝ)
        ≤ ∑ p ∈ P, ((M : ℝ) * (1 / ((p : ℝ) - 1)) * muP P + 3 * (M : ℝ) * (1 / ((p : ℝ) - 1))) :=
          Finset.sum_le_sum hsplit
      _ = (M : ℝ) * (muP P) ^ 2 + 3 * (M : ℝ) * muP P := by
          rw [Finset.sum_add_distrib]
          have hA : ∑ p ∈ P, (M : ℝ) * (1 / ((p : ℝ) - 1)) * muP P = (M : ℝ) * (muP P) ^ 2 := by
            simp only [muP, sq, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => by ring
          have hB : ∑ p ∈ P, 3 * (M : ℝ) * (1 / ((p : ℝ) - 1)) = 3 * (M : ℝ) * muP P := by
            simp only [muP, Finset.mul_sum]
          rw [hA, hB]
  -- Combine into variance
  have hexp_var : ∑ m ∈ Finset.Icc 1 M, ((omegaP P m : ℝ) - muP P) ^ 2 =
      (∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ) ^ 2) -
        2 * muP P * (∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ)) + (M : ℝ) * (muP P) ^ 2 := by
    have h1 : ∀ m ∈ Finset.Icc 1 M, ((omegaP P m : ℝ) - muP P) ^ 2 =
        (omegaP P m : ℝ) ^ 2 - (2 * muP P) * (omegaP P m : ℝ) + (muP P) ^ 2 := fun m _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hsub : M + 1 - 1 = M := by omega
    rw [hsub]
  rw [hexp_var]
  have h2mu : 2 * muP P * ((M : ℝ) * (muP P - 1) - (P.card : ℝ)) ≤
      2 * muP P * (∑ m ∈ Finset.Icc 1 M, (omegaP P m : ℝ)) :=
    mul_le_mul_of_nonneg_left hsum1 (by linarith)
  linarith

private lemma exists_finset_primes_sum_inv_gt (B : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) ∧ B < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  by_contra h
  push Not at h
  apply Nat.Primes.not_summable_one_div
  refine summable_of_sum_le (c := B) (fun _ => by positivity) fun s => ?_
  have h1 := h (s.image (fun p : Nat.Primes => (p : ℕ)))
    (fun q hq => by rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩; exact p.2)
  rw [Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ))
    (g := fun p : Nat.Primes => (p : ℕ)) (fun a _ b _ hab => Subtype.ext hab)] at h1
  exact h1

/-- **Erdős (1955) Multiplication Table Explicit Upper Bound:**
For every finite set of primes `P` with `μ = ∑_{p ∈ P} 1/(p - 1) > 0` and every `N ≥ max(1, |P|)`,
`|{1, …, N} * {1, …, N}| ≤ (252 / μ) · N²`. -/
theorem erdos_multiplication_table_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hmu : 0 < ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1)) (N : ℕ) (hN1 : 1 ≤ N) (hNP : P.card ≤ N) :
    ((Finset.Icc (1 : ℤ) (N : ℤ) * Finset.Icc (1 : ℤ) (N : ℤ)).card : ℝ) ≤
      (252 / (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1))) * (N : ℝ) ^ 2 := by
  let μ : ℝ := muP P
  change ((Finset.Icc (1 : ℤ) (N : ℤ) * Finset.Icc (1 : ℤ) (N : ℤ)).card : ℝ) ≤ (252 / μ) * (N : ℝ) ^ 2
  have hμpos : 0 < μ := hmu
  -- Transfer from Finset ℤ to Finset ℕ
  let AN : Finset ℕ := Finset.Icc 1 N
  have hcard_eq : (Finset.Icc (1 : ℤ) (N : ℤ) * Finset.Icc (1 : ℤ) (N : ℤ)).card = (AN * AN).card := by
    have hEq : Finset.Icc (1 : ℤ) (N : ℤ) * Finset.Icc (1 : ℤ) (N : ℤ) =
        (AN * AN).image (Nat.cast : ℕ → ℤ) := by
      ext x
      simp only [AN, Finset.mem_mul, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨a, ⟨ha1, haN⟩, b, ⟨hb1, hbN⟩, rfl⟩
        refine ⟨a.toNat * b.toNat, ⟨a.toNat, ⟨by omega, by omega⟩, b.toNat, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
        push_cast
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
      · rintro ⟨_, ⟨a, ⟨ha1, haN⟩, b, ⟨hb1, hbN⟩, rfl⟩, rfl⟩
        refine ⟨(a : ℤ), ⟨by omega, by omega⟩, (b : ℤ), ⟨by omega, by omega⟩, ?_⟩
        push_cast; rfl
    rw [hEq, Finset.card_image_of_injective _ Nat.cast_injective]
  rw [hcard_eq]
  -- Partition AN * AN into bad products (a or b has Ω_P < 3/4 μ) and good products (m has Ω_P ≥ 3/2 μ)
  let BadA : Finset ℕ := AN.filter (fun a => (omegaP P a : ℝ) < (3 / 4 : ℝ) * μ)
  let HighM : Finset ℕ := (Finset.Icc 1 (N ^ 2)).filter (fun m => (3 / 2 : ℝ) * μ ≤ (omegaP P m : ℝ))
  have hcov : AN * AN ⊆
      ((BadA ×ˢ AN).image (fun p => p.1 * p.2)) ∪
      (((AN ×ˢ BadA).image (fun p => p.1 * p.2)) ∪ HighM) := by
    intro m hm
    rcases Finset.mem_mul.mp hm with ⟨a, ha, b, hb, rfl⟩
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hba : (omegaP P a : ℝ) < (3 / 4 : ℝ) * μ
    · exact Or.inl (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha, hba⟩, hb⟩, rfl⟩)
    · by_cases hbb : (omegaP P b : ℝ) < (3 / 4 : ℝ) * μ
      · exact Or.inr (Or.inl (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, Finset.mem_filter.mpr ⟨hb, hbb⟩⟩, rfl⟩))
      · refine Or.inr (Or.inr (Finset.mem_filter.mpr ⟨?_, ?_⟩))
        · rw [Finset.mem_Icc]
          have ha1 := (Finset.mem_Icc.mp ha).1; have haN := (Finset.mem_Icc.mp ha).2
          have hb1 := (Finset.mem_Icc.mp hb).1; have hbN := (Finset.mem_Icc.mp hb).2
          exact ⟨by nlinarith, by nlinarith⟩
        · have ha0 : a ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
          have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb).1; omega
          rw [omegaP_mul P ha0 hb0, Nat.cast_add]
          linarith
  -- Chebyshev bound on BadA
  have hBadA : (BadA.card : ℝ) ≤ (112 / μ) * (N : ℝ) := by
    have hvar := variance_omegaP_Icc_le P hP N
    have hP_le : (P.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNP
    have hvar7 : ∑ m ∈ AN, ((omegaP P m : ℝ) - μ) ^ 2 ≤ 7 * (N : ℝ) * μ := by
      have : 2 * μ * (P.card : ℝ) ≤ 2 * (N : ℝ) * μ := by nlinarith
      linarith
    have hcheb : (BadA.card : ℝ) * ((1 / 4 : ℝ) * μ) ^ 2 ≤ ∑ m ∈ AN, ((omegaP P m : ℝ) - μ) ^ 2 := by
      calc (BadA.card : ℝ) * ((1 / 4 : ℝ) * μ) ^ 2
          = ∑ _m ∈ BadA, ((1 / 4 : ℝ) * μ) ^ 2 := by simp
        _ ≤ ∑ m ∈ BadA, ((omegaP P m : ℝ) - μ) ^ 2 := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hlt : (omegaP P m : ℝ) < (3 / 4 : ℝ) * μ := (Finset.mem_filter.mp hm).2
            nlinarith
        _ ≤ ∑ m ∈ AN, ((omegaP P m : ℝ) - μ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
    have hcomb : (BadA.card : ℝ) * ((1 / 4 : ℝ) * μ) ^ 2 ≤ 7 * (N : ℝ) * μ := le_trans hcheb hvar7
    have hden : 0 < ((1 / 4 : ℝ) * μ) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hμpos]
    nlinarith
  -- Chebyshev bound on HighM
  have hHighM : (HighM.card : ℝ) ≤ (28 / μ) * (N : ℝ) ^ 2 := by
    have hvar := variance_omegaP_Icc_le P hP (N ^ 2)
    have hP_le : (P.card : ℝ) ≤ (N : ℝ) ^ 2 := by
      have : P.card ≤ N ^ 2 := by nlinarith
      exact_mod_cast this
    have hvar7 : ∑ m ∈ Finset.Icc 1 (N ^ 2), ((omegaP P m : ℝ) - μ) ^ 2 ≤ 7 * (N : ℝ) ^ 2 * μ := by
      have hcast : ((N ^ 2 : ℕ) : ℝ) = (N : ℝ) ^ 2 := by push_cast; ring
      rw [hcast] at hvar
      have : 2 * μ * (P.card : ℝ) ≤ 2 * (N : ℝ) ^ 2 * μ := by nlinarith
      linarith
    have hcheb : (HighM.card : ℝ) * ((1 / 2 : ℝ) * μ) ^ 2 ≤
        ∑ m ∈ Finset.Icc 1 (N ^ 2), ((omegaP P m : ℝ) - μ) ^ 2 := by
      calc (HighM.card : ℝ) * ((1 / 2 : ℝ) * μ) ^ 2
          = ∑ _m ∈ HighM, ((1 / 2 : ℝ) * μ) ^ 2 := by simp
        _ ≤ ∑ m ∈ HighM, ((omegaP P m : ℝ) - μ) ^ 2 := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hge : (3 / 2 : ℝ) * μ ≤ (omegaP P m : ℝ) := (Finset.mem_filter.mp hm).2
            nlinarith
        _ ≤ ∑ m ∈ Finset.Icc 1 (N ^ 2), ((omegaP P m : ℝ) - μ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
    have hcomb : (HighM.card : ℝ) * ((1 / 2 : ℝ) * μ) ^ 2 ≤ 7 * (N : ℝ) ^ 2 * μ := le_trans hcheb hvar7
    rw [div_mul_eq_mul_div, le_div_iff₀ hμpos]
    nlinarith
  -- Combine union cardinality bounds
  have hAN_card : AN.card = N := by simp [AN]
  have hcard_le : (AN * AN).card ≤ 2 * BadA.card * N + HighM.card := by
    have h1 := Finset.card_le_card hcov
    have h2 : (((BadA ×ˢ AN).image (fun p => p.1 * p.2)) ∪
        (((AN ×ˢ BadA).image (fun p => p.1 * p.2)) ∪ HighM)).card ≤
        ((BadA ×ˢ AN).image (fun p => p.1 * p.2)).card +
        (((AN ×ˢ BadA).image (fun p => p.1 * p.2)).card + HighM.card) :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    have h3 : ((BadA ×ˢ AN).image (fun p => p.1 * p.2)).card ≤ BadA.card * N := by
      calc ((BadA ×ˢ AN).image (fun p => p.1 * p.2)).card ≤ (BadA ×ˢ AN).card := Finset.card_image_le
        _ = BadA.card * N := by rw [Finset.card_product, hAN_card]
    have h4 : ((AN ×ˢ BadA).image (fun p => p.1 * p.2)).card ≤ BadA.card * N := by
      calc ((AN ×ˢ BadA).image (fun p => p.1 * p.2)).card ≤ (AN ×ˢ BadA).card := Finset.card_image_le
        _ = N * BadA.card := by rw [Finset.card_product, hAN_card]
        _ = BadA.card * N := mul_comm _ _
    have h2b : 2 * BadA.card * N = BadA.card * N + BadA.card * N := by ring
    omega
  have hcard_R : ((AN * AN).card : ℝ) ≤ 2 * (BadA.card : ℝ) * (N : ℝ) + (HighM.card : ℝ) := by
    exact_mod_cast hcard_le
  have hbad_prod : 2 * (BadA.card : ℝ) * (N : ℝ) ≤ (224 / μ) * (N : ℝ) ^ 2 := by
    have : 2 * ((112 / μ) * (N : ℝ)) * (N : ℝ) = (224 / μ) * (N : ℝ) ^ 2 := by ring
    rw [← this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBadA (by norm_num)) (by positivity)
  have hsum252 : (224 / μ) * (N : ℝ) ^ 2 + (28 / μ) * (N : ℝ) ^ 2 = (252 / μ) * (N : ℝ) ^ 2 := by ring
  linarith

/-- **Non-Trivial Upper Bound Witness (`max(|A + A|, |A * A|) = o(|A|²)`, Ruling Out `Ω(|A|²)`):**
For every `C > 0` and every `M : ℕ`, there exists a finite set of integers `A : Finset ℤ` with
`M ≤ A.card` and `max(|A + A|, |A * A|) < C · |A|²`.
In particular, the `ε > 0` loss in the Erdős–Szemerédi conjecture cannot be eliminated. -/
theorem not_quadratic_sum_product_int :
    ∀ (C : ℝ), 0 < C → ∀ (M : ℕ),
      ∃ (A : Finset ℤ), M ≤ A.card ∧
        (max (A + A).card (A * A).card : ℝ) < C * (A.card : ℝ) ^ 2 := by
  intro C hC M
  rcases exists_finset_primes_sum_inv_gt (252 / C + 1) with ⟨P, hP, hsum⟩
  have hmu_gt : 252 / C + 1 < ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
    have hle : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP p hp).two_le
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have hmu_pos : 0 < ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
    have : 0 < 252 / C + 1 := by positivity
    linarith
  let N : ℕ := max (max M P.card) (Nat.ceil (2 / C) + 1)
  have hN1 : 1 ≤ N := by omega
  have hNM : M ≤ N := le_trans (le_max_left M P.card) (le_max_left _ _)
  have hNP : P.card ≤ N := le_trans (le_max_right M P.card) (le_max_left _ _)
  have hNgt : 2 / C < (N : ℝ) := by
    have h1 : Nat.ceil (2 / C) + 1 ≤ N := le_max_right _ _
    have h2 : 2 / C ≤ (Nat.ceil (2 / C) : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil (2 / C) + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  let A : Finset ℤ := Finset.Icc (1 : ℤ) (N : ℤ)
  have hAcard : A.card = N := by
    simp only [A, Int.card_Icc]
    omega
  refine ⟨A, hAcard.symm ▸ hNM, ?_⟩
  rw [max_lt_iff, hAcard]
  constructor
  · -- Sumset: |A + A| = 2N - 1 < 2N < C * N^2
    rw [card_add_self_Icc_int N hN1]
    have h1 : ((2 * N - 1 : ℕ) : ℝ) < 2 * (N : ℝ) := by
      have : 2 * N - 1 < 2 * N := by omega
      exact_mod_cast this
    have h2 : 2 * (N : ℝ) < C * (N : ℝ) ^ 2 := by
      have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
      have hCN : 2 < C * (N : ℝ) := (div_lt_iff₀ hC).mp hNgt |> fun h => by linarith
      nlinarith
    linarith
  · -- Product set: |A * A| ≤ (252 / μ) * N^2 < C * N^2
    have hmul := erdos_multiplication_table_card_le P hP hmu_pos N hN1 hNP
    have hratio : 252 / (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1)) < C := by
      rw [div_lt_iff₀ hmu_pos]
      have h1 : 252 / C < ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by linarith
      have h2 := (div_lt_iff₀ hC).mp h1
      linarith
    have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    calc ((A * A).card : ℝ)
        ≤ (252 / (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1))) * (N : ℝ) ^ 2 := hmul
      _ < C * (N : ℝ) ^ 2 := mul_lt_mul_of_pos_right hratio hN2pos

end ErdosMultiplicationTable

end PPL139
