/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# PPL 097 & PPL 162 (Ethereum Foundation Proximity Prize): Reed–Solomon List Decoding & Mutual Correlated Agreement

## Honest Scope Statement
The two $1,000,000 Ethereum Foundation Proximity Prize grand challenges (Arnon–Boneh–Fenzi [ABF26],
ePrint 2026/680; `proximityprize.org`; `prizeproblems.org/problems/097` and `/162`) ask for the
exact largest normalized distance `δ*_C` meeting a `2^-128` security threshold for constant-rate
(`ρ ∈ {1/2, 1/4, 1/8, 1/16}`) Reed–Solomon codes over smooth domains:
- **PPL 097 (Grand List-Decoding Challenge):** `|Λ(C^(≡ m), δ*_C)| ≤ ε* · |F|`.
- **PPL 162 (Grand MCA Challenge):** `ε_mca(C, δ*_C) ≤ ε*`.

Both grand challenges **remain OPEN** as of November 2026 (see `scripts/ppl097_findings.md` for the
full live 2026 literature map, including the late-2025/2026 refutations of up-to-capacity conjectures
and binary-field beyond-Johnson gaps alongside the Sept–Nov 2026 large-characteristic hidden-derivative
breakthroughs). This file is a **verified partial structural & certified-counterexample milestone**
and does **NOT** claim to solve the open $1,000,000 concrete-threshold grand challenges.

## Main Verified Theorems (0 `sorry`, 0 custom definitions in public theorem signatures)

### Part I: Positive Bounds (Unique Decoding, Johnson List Decoding, Sharp One-Third MCA)
1. `ppl097_rs_unique_decoding_uniqueness`:
   Unique decoding uniqueness whenever `2 * e + k ≤ L.card`.
2. `ppl097_johnson_list_size_bound` (PPL 097 Positive Frontier):
   Exact sharp Johnson list-decoding upper bound over arbitrary fields and evaluation domains:
   if `L.card * (k - 1) < t * t`, then `Λ.card * (t * t - L.card * (k - 1)) ≤ L.card * (t - (k - 1))`.
3. `ppl097_mca_one_third_sharp` (PPL 162 Sharp Unique-Decoding MCA):
   Whenever `3 * e + k ≤ L.card` and strictly more than `e + 1` affine-line challenges `z ∈ Z`
   make `u₀ + z • u₁` agree with `RS_<k(L)` on `≥ L.card - e` points, there exist `P₀, P₁` of
   `natDegree < k` with mutual correlated agreement on `≥ L.card - e` points (zero proximity loss,
   exact exception count `e + 1`, strictly sharper than BCIKS20's `n` by a factor of `≥ 3`).

### Part II: Exact Unique-Decoding Tightness & Phase Transition
4. `ppl097_mca_one_third_tight_witness`:
   For every `2 * e + k + 1 ≤ L.card`, explicit `(u₀, u₁)` achieving `Z.card = e + 1` bad
   challenges with no mutual correlated agreement on `≥ L.card - e` points.
5. `ppl097_mca_unique_decoding_top_lower_bound`:
   At the exact top of unique decoding (`2 * e + k = L.card`, `k ≥ 2`, `e ≥ 1`), the `e + 1` bound
   breaks down: explicit `(u₀, u₁)` achieving `Z.card = L.card - k + 2 = 2 * e + 2` bad challenges
   with no mutual correlated agreement (hitting `Z.card = L.card` at `k = 2`, proving BCIKS20's
   `≤ n` bound is exact down to the last integer).

### Part III: Unified `d`-to-1 Folding Beyond-Johnson Obstruction (KKH26 & Binary Subspace Core)
6. `ppl097_folding_list_decoding_lower_bound`:
   For any monic `φ : Polynomial F` of degree `d ≥ 1` whose fibers in `L` over `Y` have size `≥ d`,
   and `k = d * k'`, the word `w(x) = φ(x)^(k'+1)` admits a list `Λ` of distinct degree-`< k`
   polynomials agreeing on `≥ k + d` points with `Λ.card = |{T ∈ P_(k'+1)(Y) : ∑ T = 0}|`.
7. `ppl097_folding_mca_counterexample`:
   Under the same hypotheses, the affine line `(φ^(k'+1), φ^k')` has common agreement `≤ k < k + d`
   with `RS_<k(L)`, yet every `z ∈ -Σ_(k'+1)(Y)` makes `u₀ + z • u₁` agree with `RS_<k(L)` on
   `≥ k + d` points.

### Part IV: Concrete Kernel-Certified Beyond-Johnson Counterexamples over Prime-Field Subgroups
8. `ppl097_prime_field_f37_beyond_johnson`:
   In `ZMod 37` on `H₁₂` (`n = 12, k = 4, t = 5`, strictly beyond Johnson `25 < 36`):
   list size `≥ 24` for `x^5`, and **37 / 37 (100%)** of `z : ZMod 37` fail MCA for `(x^5, x^4)`.
9. `ppl097_prime_field_f97_rate_quarter_beyond_johnson`:
   In `ZMod 97` on smooth `H₁₆` (`n = 16, k = 4`, exact prize rate `ρ = 1/4`, `t = 5`, strictly
   beyond Johnson `25 < 48`): list size `≥ 16` for `x^5`, and **97 / 97 (100%)** of `z : ZMod 97`
   fail MCA for `(x^5, x^4)`.
10. `ppl097_prime_field_f97_folding_rate_eighth_beyond_johnson`:
    In `ZMod 97` on smooth `H₃₂` (`n = 32, k = 4`, exact prize rate `ρ = 1/8`, 4-to-1 folding
    `φ(X) = X^4`, `t = 8`, strictly beyond Johnson `64 < 96`): common agreement `≤ 4 < 8`, yet
    list size `≥ 4` for `x^8` and `≥ 25` distinct bad `z : ZMod 97` for `(x^8, x^4)`.
-/

open Polynomial Finset BigOperators

namespace PPL097

section Helpers

private lemma card_filter_eval_eq_zero_le_natDegree
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) {P : Polynomial F} (hP : P ≠ 0) :
    (L.filter (fun x => P.eval x = 0)).card ≤ P.natDegree := by
  have hsub : (L.filter (fun x => P.eval x = 0)).val ⊆ P.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_filter] at hx
    exact (Polynomial.mem_roots hP).2 hx.2
  have hle : (L.filter (fun x => P.eval x = 0)).val ≤ P.roots :=
    (Multiset.le_iff_subset (L.filter (fun x => P.eval x = 0)).nodup).2 hsub
  exact le_trans (Multiset.card_le_card hle) (Polynomial.card_roots' P)

private lemma eq_zero_of_natDegree_lt_of_card_roots
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) {P : Polynomial F} {k : ℕ}
    (hdeg : P.natDegree < k) (hcard : k ≤ (L.filter (fun x => P.eval x = 0)).card) :
    P = 0 := by
  by_contra hP
  have hle := card_filter_eval_eq_zero_le_natDegree L hP
  omega

private lemma natDegree_sub_lt_of_lt {F : Type*} [Field F] {P Q : Polynomial F} {k : ℕ}
    (hP : P.natDegree < k) (hQ : Q.natDegree < k) : (P - Q).natDegree < k :=
  lt_of_le_of_lt (Polynomial.natDegree_sub_le P Q) (max_lt hP hQ)

private lemma natDegree_add_lt_of_lt {F : Type*} [Field F] {P Q : Polynomial F} {k : ℕ}
    (hP : P.natDegree < k) (hQ : Q.natDegree < k) : (P + Q).natDegree < k :=
  lt_of_le_of_lt (Polynomial.natDegree_add_le P Q) (max_lt hP hQ)

private lemma natDegree_C_mul_lt_of_lt {F : Type*} [Field F] (c : F) {P : Polynomial F} {k : ℕ}
    (hP : P.natDegree < k) : (C c * P).natDegree < k :=
  lt_of_le_of_lt (Polynomial.natDegree_C_mul_le c P) hP

private lemma card_agree_pair_le
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) {P Q : Polynomial F} {k : ℕ}
    (hk : 1 ≤ k) (hP : P.natDegree < k) (hQ : Q.natDegree < k) (hne : P ≠ Q) :
    (L.filter (fun x => P.eval x = Q.eval x)).card ≤ k - 1 := by
  have hsub : P - Q ≠ 0 := sub_ne_zero.2 hne
  have hdeg : (P - Q).natDegree < k := natDegree_sub_lt_of_lt hP hQ
  have hfilt : L.filter (fun x => P.eval x = Q.eval x) =
      L.filter (fun x => (P - Q).eval x = 0) := by
    ext x
    simp [sub_eq_zero]
  rw [hfilt]
  have hle := card_filter_eval_eq_zero_le_natDegree L hsub
  omega

private lemma card_inter_ge_of_subset
    {α : Type*} [DecidableEq α] {L A B : Finset α} (hA : A ⊆ L) (hB : B ⊆ L) :
    A.card + B.card ≤ L.card + (A ∩ B).card := by
  have hU : (A ∪ B).card ≤ L.card := Finset.card_le_card (Finset.union_subset hA hB)
  have hUI := Finset.card_union_add_card_inter A B
  omega

/-- Cauchy–Schwarz inequality for non-negative integer weights on a `Finset`, proved directly
without extra analysis imports. -/
private lemma sq_sum_le_card_mul_sum_sq_nat {α : Type*} (L : Finset α) (f : α → ℕ) :
    (∑ x ∈ L, f x) * (∑ x ∈ L, f x) ≤ L.card * ∑ x ∈ L, f x * f x := by
  zify
  have hnonneg : (0 : ℤ) ≤ ∑ x ∈ L, ∑ y ∈ L, ((f x : ℤ) - (f y : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hexpand :
      (∑ x ∈ L, ∑ y ∈ L, ((f x : ℤ) - (f y : ℤ)) ^ 2) =
        2 * (L.card : ℤ) * (∑ x ∈ L, (f x : ℤ) * (f x : ℤ)) -
          2 * (∑ x ∈ L, (f x : ℤ)) * (∑ x ∈ L, (f x : ℤ)) := by
    have h1 : ∀ x : α,
        (∑ y ∈ L, ((f x : ℤ) - (f y : ℤ)) ^ 2) =
          (L.card : ℤ) * ((f x : ℤ) * (f x : ℤ)) - 2 * ((f x : ℤ) * (∑ y ∈ L, (f y : ℤ))) +
            (∑ y ∈ L, (f y : ℤ) * (f y : ℤ)) := by
      intro x
      have hrw : ∀ y : α, ((f x : ℤ) - (f y : ℤ)) ^ 2 =
          (f x : ℤ) * (f x : ℤ) - (2 * (f x : ℤ)) * (f y : ℤ) + (f y : ℤ) * (f y : ℤ) := by
        intro y; ring
      simp_rw [hrw, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
      ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  linarith

private lemma monic_prod_X_sub_C {F : Type*} [Field F] [DecidableEq F] (T : Finset F) :
    (∏ y ∈ T, (X - C y)).Monic ∧ (∏ y ∈ T, (X - C y)).natDegree = T.card := by
  induction T using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hlin : (X - C a : Polynomial F).Monic := Polynomial.monic_X_sub_C a
    have hdeg : (X - C a : Polynomial F).natDegree = 1 := Polynomial.natDegree_X_sub_C a
    refine ⟨hlin.mul ih.1, ?_⟩
    rw [hlin.natDegree_mul ih.1, hdeg, ih.2]
    omega

private lemma coeff_pred_prod_X_sub_C {F : Type*} [Field F] [DecidableEq F] (T : Finset F)
    (hT : 1 ≤ T.card) :
    (∏ y ∈ T, (X - C y)).coeff (T.card - 1) = -(∑ y ∈ T, y) := by
  induction T using Finset.induction_on with
  | empty =>
    simp at hT
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    simp only [Nat.add_sub_cancel]
    have hmul : ((X - C a) * ∏ y ∈ s, (X - C y)).coeff s.card =
        (X * ∏ y ∈ s, (X - C y)).coeff s.card - (C a * ∏ y ∈ s, (X - C y)).coeff s.card := by
      rw [sub_mul, Polynomial.coeff_sub]
    rw [hmul, Polynomial.coeff_C_mul]
    have ⟨hmon, hdeg⟩ := monic_prod_X_sub_C s
    have hlead : (∏ y ∈ s, (X - C y)).coeff s.card = 1 := by
      rw [← hdeg]
      exact hmon.leadingCoeff
    rw [hlead, mul_one]
    by_cases hs : s.card = 0
    · have hempty : s = ∅ := Finset.card_eq_zero.1 hs
      subst hempty
      simp
    · have hs1 : 1 ≤ s.card := Nat.pos_of_ne_zero hs
      have hX : (X * ∏ y ∈ s, (X - C y)).coeff s.card =
          (∏ y ∈ s, (X - C y)).coeff (s.card - 1) := by
        cases hsc : s.card with
        | zero => omega
        | succ m =>
          simp [Polynomial.coeff_X_mul]
      rw [hX, ih hs1]
      ring

private lemma natDegree_residual_poly_lt {F : Type*} [Field F] [DecidableEq F]
    (T : Finset F) {m : ℕ} (hm : 1 ≤ m) (hcard : T.card = m + 1) :
    (X ^ (m + 1) - C (∑ y ∈ T, y) * X ^ m - ∏ y ∈ T, (X - C y)).natDegree < m := by
  set H : Polynomial F := X ^ (m + 1) - C (∑ y ∈ T, y) * X ^ m - ∏ y ∈ T, (X - C y)
  have ⟨hmon, hdegP⟩ := monic_prod_X_sub_C T
  rw [hcard] at hdegP
  have hcoeff_zero : ∀ j : ℕ, m ≤ j → H.coeff j = 0 := by
    intro j hj
    dsimp only [H]
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    by_cases hj1 : j = m + 1
    · subst hj1
      have hlead : (∏ y ∈ T, (X - C y)).coeff (m + 1) = 1 := by
        rw [← hdegP]; exact hmon.leadingCoeff
      simp [hlead]
    · by_cases hj0 : j = m
      · subst hj0
        have hpred := coeff_pred_prod_X_sub_C T (by omega)
        rw [hcard] at hpred
        simp only [Nat.add_sub_cancel] at hpred
        rw [hpred]
        simp
      · have hgt : m + 1 < j := by omega
        have hP0 : (∏ y ∈ T, (X - C y)).coeff j = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simp [Nat.ne_of_gt hgt, Nat.ne_of_gt (by omega : m < j), hP0]
  by_cases hH : H = 0
  · rw [hH, Polynomial.natDegree_zero]; exact hm
  · by_contra hge
    push Not at hge
    have hlc : H.coeff H.natDegree = 0 := hcoeff_zero H.natDegree hge
    exact (Polynomial.leadingCoeff_ne_zero.2 hH) hlc

end Helpers

/-! ## Part I: Positive Bounds (Unique Decoding, Johnson List Decoding, Sharp One-Third MCA) -/

/-- **Unique Decoding Uniqueness for Reed–Solomon Codes**:
Over any field `F`, evaluation domain `L : Finset F`, and parameters `1 ≤ k`, `2 * e + k ≤ L.card`,
any received word `u : F → F` has at most one degree-`< k` polynomial agreeing with `u` on at least
`L.card - e` points of `L`. -/
theorem ppl097_rs_unique_decoding_uniqueness
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (u : F → F) {k e : ℕ}
    (hbound : 2 * e + k ≤ L.card)
    {P₁ P₂ : Polynomial F} (hP₁ : P₁.natDegree < k) (hP₂ : P₂.natDegree < k)
    (hA₁ : L.card - e ≤ (L.filter (fun x => P₁.eval x = u x)).card)
    (hA₂ : L.card - e ≤ (L.filter (fun x => P₂.eval x = u x)).card) :
    P₁ = P₂ := by
  let A₁ := L.filter (fun x => P₁.eval x = u x)
  let A₂ := L.filter (fun x => P₂.eval x = u x)
  have hinter : A₁ ∩ A₂ ⊆ L.filter (fun x => (P₁ - P₂).eval x = 0) := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    exact ⟨hx.1.1, by simp [hx.1.2, hx.2.2]⟩
  have hcard_inter : k ≤ (A₁ ∩ A₂).card := by
    have hci := card_inter_ge_of_subset
      (Finset.filter_subset (fun x => P₁.eval x = u x) L)
      (Finset.filter_subset (fun x => P₂.eval x = u x) L)
    change A₁.card + A₂.card ≤ L.card + (A₁ ∩ A₂).card at hci
    change L.card - e ≤ A₁.card at hA₁
    change L.card - e ≤ A₂.card at hA₂
    omega
  have hzero : P₁ - P₂ = 0 :=
    eq_zero_of_natDegree_lt_of_card_roots L (natDegree_sub_lt_of_lt hP₁ hP₂)
      (le_trans hcard_inter (Finset.card_le_card hinter))
  exact sub_eq_zero.1 hzero

/-- **PPL 097 Positive Frontier — Exact Sharp Johnson List-Decoding Bound**:
Over any field `F` and arbitrary evaluation domain `L : Finset F`, let `Λ : Finset (Polynomial F)`
be any set of polynomials of `natDegree < k` (`1 ≤ k`), each agreeing with `u : F → F` on at least
`t` points of `L`. Strictly inside the Johnson radius (`L.card * (k - 1) < t * t`), the list size
satisfies the exact sharp Johnson bound:
`Λ.card * (t * t - L.card * (k - 1)) ≤ L.card * (t - (k - 1))`. -/
theorem ppl097_johnson_list_size_bound
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (u : F → F)
    {k t : ℕ} (hk : 1 ≤ k) (ht : L.card * (k - 1) < t * t)
    (Λ : Finset (Polynomial F))
    (hdeg : ∀ P ∈ Λ, P.natDegree < k)
    (hagr : ∀ P ∈ Λ, t ≤ (L.filter (fun x => P.eval x = u x)).card) :
    Λ.card * (t * t - L.card * (k - 1)) ≤ L.card * (t - (k - 1)) := by
  by_cases hΛ : Λ.card = 0
  · simp [hΛ]
  have hm1 : 1 ≤ Λ.card := Nat.pos_of_ne_zero hΛ
  obtain ⟨P₀, hP₀⟩ := Finset.card_pos.1 hm1
  have ht_le_n : t ≤ L.card :=
    le_trans (hagr P₀ hP₀) (Finset.card_le_card (Finset.filter_subset _ L))
  have hk_lt_t : k - 1 < t := by
    by_contra hge
    push Not at hge
    have hmul : t * t ≤ L.card * (k - 1) := Nat.mul_le_mul ht_le_n hge
    omega
  -- Case 1: Λ.card * t ≤ L.card (small list; direct arithmetic).
  by_cases hsmall : Λ.card * t ≤ L.card
  · zify [le_of_lt ht, le_of_lt hk_lt_t]
    have h1 : (Λ.card : ℤ) * ((t : ℤ) * (t : ℤ)) ≤ (L.card : ℤ) * (t : ℤ) := by
      have : (Λ.card : ℤ) * (t : ℤ) ≤ (L.card : ℤ) := by exact_mod_cast hsmall
      nlinarith
    have h2 : (L.card : ℤ) * ((k - 1 : ℕ) : ℤ) ≤
        (Λ.card : ℤ) * ((L.card : ℤ) * ((k - 1 : ℕ) : ℤ)) := by
      have hΛ1 : (1 : ℤ) ≤ (Λ.card : ℤ) := by exact_mod_cast hm1
      have hnn : (0 : ℤ) ≤ (L.card : ℤ) * ((k - 1 : ℕ) : ℤ) := by positivity
      nlinarith
    linarith
  -- Case 2: L.card < Λ.card * t (main Cauchy–Schwarz double-counting argument).
  push Not at hsmall
  let c : F → ℕ := fun x => (Λ.filter (fun P => P.eval x = u x)).card
  let S : ℕ := ∑ x ∈ L, c x
  have hS_eq : S = ∑ P ∈ Λ, (L.filter (fun x => P.eval x = u x)).card := by
    dsimp only [S, c]
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hS_ge : Λ.card * t ≤ S := by
    rw [hS_eq]
    calc Λ.card * t = ∑ _P ∈ Λ, t := by simp
      _ ≤ ∑ P ∈ Λ, (L.filter (fun x => P.eval x = u x)).card :=
          Finset.sum_le_sum fun P hP => hagr P hP
  have hpair_eq :
      (∑ x ∈ L, c x * (c x - 1)) =
        ∑ P ∈ Λ, ∑ Q ∈ Λ.erase P, (L.filter (fun x => P.eval x = u x ∧ Q.eval x = u x)).card := by
    have hinner : ∀ x ∈ L, c x * (c x - 1) =
        ∑ P ∈ Λ, ∑ Q ∈ Λ.erase P, (if P.eval x = u x ∧ Q.eval x = u x then 1 else 0) := by
      intro x _
      let B := Λ.filter (fun P => P.eval x = u x)
      have hBcard : c x = B.card := rfl
      have hsumB : ∑ P ∈ B, (B.erase P).card = B.card * (B.card - 1) := by
        have hconst : ∀ P ∈ B, (B.erase P).card = B.card - 1 := fun P hP =>
          Finset.card_erase_of_mem hP
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
      rw [hBcard, ← hsumB]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun P hP => ?_
      by_cases hPx : P.eval x = u x
      · simp only [hPx, ↓reduceIte, true_and]
        have herase : B.erase P = (Λ.erase P).filter (fun Q => Q.eval x = u x) := by
          ext Q
          simp [B, and_assoc]
        rw [herase, Finset.card_filter]
      · simp [hPx]
    rw [Finset.sum_congr rfl hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q _ => ?_
    rw [Finset.card_filter]
  have hpair_le : ∑ x ∈ L, c x * (c x - 1) ≤ Λ.card * (Λ.card - 1) * (k - 1) := by
    rw [hpair_eq]
    calc ∑ P ∈ Λ, ∑ Q ∈ Λ.erase P,
          (L.filter (fun x => P.eval x = u x ∧ Q.eval x = u x)).card
        ≤ ∑ P ∈ Λ, ∑ Q ∈ Λ.erase P, (k - 1) := by
          refine Finset.sum_le_sum fun P hP => Finset.sum_le_sum fun Q hQ => ?_
          have hne : P ≠ Q := (Finset.ne_of_mem_erase hQ).symm
          have hQmem : Q ∈ Λ := Finset.mem_of_mem_erase hQ
          have hsub : L.filter (fun x => P.eval x = u x ∧ Q.eval x = u x) ⊆
              L.filter (fun x => P.eval x = Q.eval x) := by
            intro x hx
            rw [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, hx.2.1.trans hx.2.2.symm⟩
          exact le_trans (Finset.card_le_card hsub)
            (card_agree_pair_le L hk (hdeg P hP) (hdeg Q hQmem) hne)
      _ = ∑ P ∈ Λ, (Λ.erase P).card * (k - 1) := by
          refine Finset.sum_congr rfl fun P _ => by simp
      _ = ∑ P ∈ Λ, (Λ.card - 1) * (k - 1) := by
          refine Finset.sum_congr rfl fun P hP => by rw [Finset.card_erase_of_mem hP]
      _ = Λ.card * (Λ.card - 1) * (k - 1) := by
          simp [mul_assoc]
  have hcs := sq_sum_le_card_mul_sum_sq_nat L c
  have hsq_split : (∑ x ∈ L, c x * c x) = (∑ x ∈ L, c x * (c x - 1)) + S := by
    dsimp only [S]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases hcx : c x with
    | zero => simp
    | succ r =>
      simp only [Nat.add_sub_cancel]
      ring
  have hS_ineq : S * S ≤ L.card * (Λ.card * (Λ.card - 1) * (k - 1)) + L.card * S := by
    calc S * S ≤ L.card * (∑ x ∈ L, c x * c x) := hcs
      _ = L.card * ((∑ x ∈ L, c x * (c x - 1)) + S) := by rw [hsq_split]
      _ = L.card * (∑ x ∈ L, c x * (c x - 1)) + L.card * S := Nat.mul_add _ _ _
      _ ≤ L.card * (Λ.card * (Λ.card - 1) * (k - 1)) + L.card * S :=
          Nat.add_le_add_right (Nat.mul_le_mul_left L.card hpair_le) _
  zify [le_of_lt ht, le_of_lt hk_lt_t, hm1] at hS_ineq hS_ge hsmall ⊢
  have hmonotone : ((Λ.card : ℤ) * (t : ℤ)) * ((Λ.card : ℤ) * (t : ℤ) - (L.card : ℤ)) ≤
      (S : ℤ) * ((S : ℤ) - (L.card : ℤ)) := by
    nlinarith
  have hstep : ((Λ.card : ℤ) * (t : ℤ)) * ((Λ.card : ℤ) * (t : ℤ) - (L.card : ℤ)) ≤
      (L.card : ℤ) * ((Λ.card : ℤ) * ((Λ.card : ℤ) - 1) * ((k - 1 : ℕ) : ℤ)) := by
    linarith
  have hm_pos : (0 : ℤ) < (Λ.card : ℤ) := by exact_mod_cast hm1
  have hfactor : (Λ.card : ℤ) * ((Λ.card : ℤ) * ((t : ℤ) * (t : ℤ) - (L.card : ℤ) * ((k - 1 : ℕ) : ℤ)) -
      (L.card : ℤ) * ((t : ℤ) - ((k - 1 : ℕ) : ℤ))) ≤ 0 := by
    nlinarith
  nlinarith

/-- **PPL 162 Positive Frontier — Exact Sharp Mutual Correlated Agreement (`3e + k ≤ n`)**:
Over any field `F`, evaluation domain `L : Finset F`, and parameters `1 ≤ k`, `3 * e + k ≤ L.card`:
if strictly more than `e + 1` affine-line challenges `z ∈ Z` satisfy that `u₀ + z • u₁` agrees with
some polynomial of `natDegree < k` on `≥ L.card - e` points of `L`, then `u₀` and `u₁` admit
**mutual correlated agreement** (with zero proximity loss) on `≥ L.card - e` points of `L`.
The exception threshold `e + 1` is exact (see `ppl097_mca_one_third_tight_witness`). -/
theorem ppl097_mca_one_third_sharp
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) (u₀ u₁ : F → F)
    {k e : ℕ} (hbound : 3 * e + k ≤ L.card)
    (Z : Finset F)
    (hZ : ∀ z ∈ Z, ∃ P : Polynomial F, P.natDegree < k ∧
      L.card - e ≤ (L.filter (fun x => u₀ x + z * u₁ x = P.eval x)).card)
    (hcard : e + 1 < Z.card) :
    ∃ P₀ P₁ : Polynomial F, P₀.natDegree < k ∧ P₁.natDegree < k ∧
      L.card - e ≤ (L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)).card := by
  by_contra hno
  push Not at hno
  have hZ2 : 1 < Z.card := by omega
  obtain ⟨z₁, hz₁, z₂, hz₂, hne12⟩ := Finset.one_lt_card.1 hZ2
  obtain ⟨c₁, hc₁deg, hc₁agr⟩ := hZ z₁ hz₁
  obtain ⟨c₂, hc₂deg, hc₂agr⟩ := hZ z₂ hz₂
  let inv : F := (z₁ - z₂)⁻¹
  have hdz : z₁ - z₂ ≠ 0 := sub_ne_zero.2 hne12
  let P₁ : Polynomial F := C inv * (c₁ - c₂)
  let P₀ : Polynomial F := c₁ - C z₁ * P₁
  have hP₁deg : P₁.natDegree < k := natDegree_C_mul_lt_of_lt inv (natDegree_sub_lt_of_lt hc₁deg hc₂deg)
  have hP₀deg : P₀.natDegree < k :=
    natDegree_sub_lt_of_lt hc₁deg (natDegree_C_mul_lt_of_lt z₁ hP₁deg)
  let A₁ := L.filter (fun x => u₀ x + z₁ * u₁ x = c₁.eval x)
  let A₂ := L.filter (fun x => u₀ x + z₂ * u₁ x = c₂.eval x)
  let D := A₁ ∩ A₂
  have hD_sub_agree : D ⊆ L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x) := by
    intro x hx
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    refine ⟨hx.1.1, ?_, ?_⟩
    · have h1 : u₀ x + z₁ * u₁ x = c₁.eval x := hx.1.2
      have h2 : u₀ x + z₂ * u₁ x = c₂.eval x := hx.2.2
      have hu1 : u₁ x = inv * (c₁.eval x - c₂.eval x) := by
        have hdiff : (z₁ - z₂) * u₁ x = c₁.eval x - c₂.eval x := by linear_combination h1 - h2
        calc u₁ x = inv * ((z₁ - z₂) * u₁ x) := by simp [inv, inv_mul_cancel_left₀ hdz]
          _ = inv * (c₁.eval x - c₂.eval x) := by rw [hdiff]
      simp only [P₀, P₁, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      linear_combination h1 - z₁ * hu1
    · have h1 : u₀ x + z₁ * u₁ x = c₁.eval x := hx.1.2
      have h2 : u₀ x + z₂ * u₁ x = c₂.eval x := hx.2.2
      have hdiff : (z₁ - z₂) * u₁ x = c₁.eval x - c₂.eval x := by linear_combination h1 - h2
      simp only [P₁, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
      calc u₁ x = inv * ((z₁ - z₂) * u₁ x) := by simp [inv, inv_mul_cancel_left₀ hdz]
        _ = inv * (c₁.eval x - c₂.eval x) := by rw [hdiff]
  let v₀ : F → F := fun x => u₀ x - P₀.eval x
  let v₁ : F → F := fun x => u₁ x - P₁.eval x
  let G := L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)
  let S := L.filter (fun x => ¬(u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x))
  have hGS_card : G.card + S.card = L.card :=
    Finset.card_filter_add_card_filter_not (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)
  have hG_lt : G.card < L.card - e := hno P₀ P₁ hP₀deg hP₁deg
  have hS_ge : e + 1 ≤ S.card := by omega
  have hD_card : L.card - 2 * e ≤ D.card := by
    have hci := card_inter_ge_of_subset
      (Finset.filter_subset (fun x => u₀ x + z₁ * u₁ x = c₁.eval x) L)
      (Finset.filter_subset (fun x => u₀ x + z₂ * u₁ x = c₂.eval x) L)
    change A₁.card + A₂.card ≤ L.card + D.card at hci
    change L.card - e ≤ A₁.card at hc₁agr
    change L.card - e ≤ A₂.card at hc₂agr
    omega
  have hD_le_G : D.card ≤ G.card := Finset.card_le_card hD_sub_agree
  have hS_le : S.card ≤ 2 * e := by omega
  -- Every z ∈ Z has residual polynomial q_z = 0, so v₀(x) + z * v₁(x) = 0 on ≥ S.card - e points of S.
  have hrow : ∀ z ∈ Z, S.card - e ≤ (S.filter (fun x => v₀ x + z * v₁ x = 0)).card := by
    intro z hz
    obtain ⟨cz, hczdeg, hczagr⟩ := hZ z hz
    let Az := L.filter (fun x => u₀ x + z * u₁ x = cz.eval x)
    let qz : Polynomial F := cz - (P₀ + C z * P₁)
    have hqzdeg : qz.natDegree < k :=
      natDegree_sub_lt_of_lt hczdeg (natDegree_add_lt_of_lt hP₀deg (natDegree_C_mul_lt_of_lt z hP₁deg))
    have hAzG_sub : Az ∩ G ⊆ L.filter (fun x => qz.eval x = 0) := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      refine ⟨hx.1.1, ?_⟩
      simp only [qz, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      rw [← hx.1.2, hx.2.2.1, hx.2.2.2]
      ring
    have hAzG_card : k ≤ (Az ∩ G).card := by
      have hci := card_inter_ge_of_subset
        (Finset.filter_subset (fun x => u₀ x + z * u₁ x = cz.eval x) L)
        (Finset.filter_subset (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x) L)
      change Az.card + G.card ≤ L.card + (Az ∩ G).card at hci
      change L.card - e ≤ Az.card at hczagr
      omega
    have hqz_zero : qz = 0 :=
      eq_zero_of_natDegree_lt_of_card_roots L hqzdeg
        (le_trans hAzG_card (Finset.card_le_card hAzG_sub))
    have hcz_eq : cz = P₀ + C z * P₁ := sub_eq_zero.1 hqz_zero
    have hAzS_sub : Az ∩ S ⊆ S.filter (fun x => v₀ x + z * v₁ x = 0) := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      refine ⟨hx.2, ?_⟩
      have hev : u₀ x + z * u₁ x = (P₀ + C z * P₁).eval x := by rw [← hcz_eq]; exact hx.1.2
      simp only [v₀, v₁]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hev
      linear_combination hev
    have hAzS_card : S.card - e ≤ (Az ∩ S).card := by
      have hci := card_inter_ge_of_subset
        (Finset.filter_subset (fun x => u₀ x + z * u₁ x = cz.eval x) L)
        (Finset.filter_subset (fun x => ¬(u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)) L)
      change Az.card + S.card ≤ L.card + (Az ∩ S).card at hci
      change L.card - e ≤ Az.card at hczagr
      omega
    exact le_trans hAzS_card (Finset.card_le_card hAzS_sub)
  have hcol : ∀ x ∈ S, (Z.filter (fun z => v₀ x + z * v₁ x = 0)).card ≤ 1 := by
    intro x hx
    rw [Finset.mem_filter] at hx
    refine Finset.card_le_one.2 fun z₁ hz₁ z₂ hz₂ => ?_
    rw [Finset.mem_filter] at hz₁ hz₂
    by_cases hv1 : v₁ x = 0
    · have hv0 : v₀ x = 0 := by simpa [hv1] using hz₁.2
      exfalso
      exact hx.2 ⟨sub_eq_zero.1 hv0, sub_eq_zero.1 hv1⟩
    · have hdiff : (z₁ - z₂) * v₁ x = 0 := by linear_combination hz₁.2 - hz₂.2
      exact sub_eq_zero.1 ((mul_eq_zero.1 hdiff).resolve_right hv1)
  have hdc :
      (∑ z ∈ Z, (S.filter (fun x => v₀ x + z * v₁ x = 0)).card) =
        ∑ x ∈ S, (Z.filter (fun z => v₀ x + z * v₁ x = 0)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have hlo : Z.card * (S.card - e) ≤ ∑ z ∈ Z, (S.filter (fun x => v₀ x + z * v₁ x = 0)).card := by
    calc Z.card * (S.card - e) = ∑ _z ∈ Z, (S.card - e) := by simp
      _ ≤ ∑ z ∈ Z, (S.filter (fun x => v₀ x + z * v₁ x = 0)).card := Finset.sum_le_sum hrow
  have hhi : (∑ x ∈ S, (Z.filter (fun z => v₀ x + z * v₁ x = 0)).card) ≤ S.card := by
    calc (∑ x ∈ S, (Z.filter (fun z => v₀ x + z * v₁ x = 0)).card)
        ≤ ∑ _x ∈ S, 1 := Finset.sum_le_sum hcol
      _ = S.card := by simp
  have hineq : Z.card * (S.card - e) ≤ S.card := le_trans hlo (hdc.le.trans hhi)
  have ht1 : 1 ≤ S.card - e := by omega
  have hstep : (e + 2) * (S.card - e) ≤ S.card :=
    le_trans (Nat.mul_le_mul_right (S.card - e) hcard) hineq
  have hS_eq : S.card = e + (S.card - e) := by omega
  nlinarith

/-! ## Part II: Exact Unique-Decoding Tightness & Phase Transition -/

/-- **Tightness of the `e + 1` Exception Bound**:
Whenever `1 ≤ k` and `2 * e + k + 1 ≤ L.card`, there exist words `u₀, u₁ : F → F` and a set
`Z : Finset F` of size `e + 1` such that every `z ∈ Z` makes `u₀ + z • u₁` agree with `0` on
`≥ L.card - e` points of `L`, yet NO pair `(P₀, P₁)` of degree `< k` has mutual correlated
agreement on `≥ L.card - e` points of `L`. -/
theorem ppl097_mca_one_third_tight_witness
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) {k e : ℕ}
    (hk : 1 ≤ k) (hbound : 2 * e + k + 1 ≤ L.card) :
    ∃ (u₀ u₁ : F → F) (Z : Finset F),
      Z.card = e + 1 ∧
      (∀ z ∈ Z, ∃ P : Polynomial F, P.natDegree < k ∧
        L.card - e ≤ (L.filter (fun x => u₀ x + z * u₁ x = P.eval x)).card) ∧
      (∀ P₀ P₁ : Polynomial F, P₀.natDegree < k → P₁.natDegree < k →
        (L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)).card < L.card - e) := by
  obtain ⟨S, hSL, hScard⟩ := Finset.exists_subset_card_eq (by omega : e + 1 ≤ L.card)
  let u₀ : F → F := fun x => if x ∈ S then x else 0
  let u₁ : F → F := fun x => if x ∈ S then 1 else 0
  let Z : Finset F := S.image (fun s => -s)
  refine ⟨u₀, u₁, Z, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective S neg_injective, hScard]
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨s, hsS, rfl⟩ := hz
    refine ⟨0, by simp; omega, ?_⟩
    have hsub : insert s (L \ S) ⊆ L.filter (fun x => u₀ x + (-s) * u₁ x = (0 : Polynomial F).eval x) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_sdiff] at hx
      rw [Finset.mem_filter]
      rcases hx with rfl | ⟨hxL, hxS⟩
      · exact ⟨hSL hsS, by simp [u₀, u₁, hsS]⟩
      · exact ⟨hxL, by simp [u₀, u₁, hxS]⟩
    have hs_not : s ∉ L \ S := by simp [hsS]
    have hcard_ins : (insert s (L \ S)).card = L.card - e := by
      rw [Finset.card_insert_of_notMem hs_not, Finset.card_sdiff_of_subset hSL, hScard]
      omega
    rw [← hcard_ins]
    exact Finset.card_le_card hsub
  · intro P₀ P₁ _ hP₁
    by_contra hge
    push Not at hge
    let A := L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)
    change L.card - e ≤ A.card at hge
    have hsub_zero : A ∩ (L \ S) ⊆ L.filter (fun x => P₁.eval x = 0) := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff] at hx
      rw [Finset.mem_filter]
      refine ⟨hx.1.1, ?_⟩
      have h1 : u₁ x = P₁.eval x := hx.1.2.2
      simp [u₁, hx.2.2] at h1
      exact h1.symm
    have hcard_inter : k ≤ (A ∩ (L \ S)).card := by
      have hci := card_inter_ge_of_subset
        (Finset.filter_subset (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x) L)
        (Finset.sdiff_subset : L \ S ⊆ L)
      have hLS : (L \ S).card = L.card - (e + 1) := by rw [Finset.card_sdiff_of_subset hSL, hScard]
      change A.card + (L \ S).card ≤ L.card + (A ∩ (L \ S)).card at hci
      omega
    have hP₁zero : P₁ = 0 :=
      eq_zero_of_natDegree_lt_of_card_roots L hP₁
        (le_trans hcard_inter (Finset.card_le_card hsub_zero))
    have hA_sub : A ⊆ L \ S := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, fun hxS => ?_⟩
      have h1 := hx.2.2
      simp [u₁, hxS, hP₁zero] at h1
    have hA_le : A.card ≤ L.card - (e + 1) := by
      calc A.card ≤ (L \ S).card := Finset.card_le_card hA_sub
        _ = L.card - (e + 1) := by rw [Finset.card_sdiff_of_subset hSL, hScard]
    omega

/-- **Exact Phase Transition at the Top of Unique Decoding (`2e + k = n`, `k ≥ 2`, `e ≥ 1`)**:
At the exact top of unique decoding `2 * e + k = L.card`, the `e + 1` exception bound breaks down:
there exist words `u₀, u₁ : F → F` and a set `Z : Finset F` of size **`L.card - k + 2`** (which
equals `L.card` when `k = 2`, proving BCIKS20 Theorem 4.1's `≤ n` bound is exact down to the last
integer) such that every `z ∈ Z` makes `u₀ + z • u₁` agree with `RS_<k(L)` on `≥ L.card - e`
points, yet NO pair `(P₀, P₁)` of degree `< k` has mutual correlated agreement on `≥ L.card - e`
points. -/
theorem ppl097_mca_unique_decoding_top_lower_bound
    {F : Type*} [Field F] [DecidableEq F] (L : Finset F) {k e : ℕ}
    (hk : 2 ≤ k) (he : 1 ≤ e) (htop : 2 * e + k = L.card) :
    ∃ (u₀ u₁ : F → F) (Z : Finset F),
      Z.card = L.card - k + 2 ∧
      (∀ z ∈ Z, ∃ P : Polynomial F, P.natDegree < k ∧
        L.card - e ≤ (L.filter (fun x => u₀ x + z * u₁ x = P.eval x)).card) ∧
      (∀ P₀ P₁ : Polynomial F, P₀.natDegree < k → P₁.natDegree < k →
        (L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)).card < L.card - e) := by
  obtain ⟨S, hSL, hScard⟩ := Finset.exists_subset_card_eq (by omega : e + 1 ≤ L.card)
  have hLS_card : (L \ S).card = k + e - 1 := by rw [Finset.card_sdiff_of_subset hSL, hScard]; omega
  obtain ⟨R, hRLS, hRcard⟩ := Finset.exists_subset_card_eq (by omega : k - 2 ≤ (L \ S).card)
  let Q : Polynomial F := ∏ r ∈ R, (X - C r)
  have ⟨hQmon, hQdeg⟩ := monic_prod_X_sub_C R
  rw [hRcard] at hQdeg
  have hQne_on : ∀ x : F, x ∉ R → Q.eval x ≠ 0 := by
    intro x hxR
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [Finset.prod_ne_zero_iff]
    intro r hr
    exact sub_ne_zero.2 fun h => hxR (h ▸ hr)
  have hQzero_on : ∀ r ∈ R, Q.eval r = 0 := by
    intro r hr
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero hr (sub_self r)
  let D' : Finset F := (L \ S) \ R
  have hD'_card : D'.card = e + 1 := by
    rw [Finset.card_sdiff_of_subset hRLS, hLS_card, hRcard]; omega
  have hdisj_SD' : Disjoint S D' := by
    rw [Finset.disjoint_left]
    intro x hxS hxD'
    exact (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hxD').1).2 hxS
  have hdisj_SR : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro x hxS hxR
    exact (Finset.mem_sdiff.1 (hRLS hxR)).2 hxS
  let u₀ : F → F := fun x => if x ∈ S then x * Q.eval x else 0
  let u₁ : F → F := fun x => if x ∈ S then Q.eval x else 0
  let Z : Finset F := (S ∪ D').image (fun x => -x)
  refine ⟨u₀, u₁, Z, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ neg_injective, Finset.card_union_of_disjoint hdisj_SD',
      hScard, hD'_card]
    omega
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Finset.mem_union] at hw
    rcases hw with hwS | hwD'
    · refine ⟨0, by simp; omega, ?_⟩
      have hsub : insert w (L \ S) ⊆
          L.filter (fun x => u₀ x + (-w) * u₁ x = (0 : Polynomial F).eval x) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_sdiff] at hx
        rw [Finset.mem_filter]
        rcases hx with rfl | ⟨hxL, hxS⟩
        · exact ⟨hSL hwS, by simp [u₀, u₁, hwS]⟩
        · exact ⟨hxL, by simp [u₀, u₁, hxS]⟩
      have hw_not : w ∉ L \ S := by simp [hwS]
      have hcard_ins : (insert w (L \ S)).card = L.card - e := by
        rw [Finset.card_insert_of_notMem hw_not, Finset.card_sdiff_of_subset hSL, hScard]; omega
      rw [← hcard_ins]
      exact Finset.card_le_card hsub
    · let P : Polynomial F := (X - C w) * Q
      have hPdeg : P.natDegree < k := by
        have hlin : (X - C w : Polynomial F).Monic := Polynomial.monic_X_sub_C w
        rw [hlin.natDegree_mul hQmon, Polynomial.natDegree_X_sub_C, hQdeg]
        omega
      refine ⟨P, hPdeg, ?_⟩
      have hwL : w ∈ L := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hwD').1).1
      have hwS : w ∉ S := (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hwD').1).2
      have hwR : w ∉ R := (Finset.mem_sdiff.1 hwD').2
      have hsub : insert w (S ∪ R) ⊆
          L.filter (fun x => u₀ x + (-w) * u₁ x = P.eval x) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_union] at hx
        rw [Finset.mem_filter]
        rcases hx with rfl | hxS | hxR
        · exact ⟨hwL, by simp [u₀, u₁, hwS, P]⟩
        · exact ⟨hSL hxS, by simp [u₀, u₁, hxS, P]; ring⟩
        · have hxLS := hRLS hxR
          have hxL : x ∈ L := (Finset.mem_sdiff.1 hxLS).1
          have hxnotS : x ∉ S := (Finset.mem_sdiff.1 hxLS).2
          exact ⟨hxL, by simp [u₀, u₁, hxnotS, P, hQzero_on x hxR]⟩
      have hw_not_SR : w ∉ S ∪ R := by simp [hwS, hwR]
      have hcard_ins : (insert w (S ∪ R)).card = L.card - e := by
        rw [Finset.card_insert_of_notMem hw_not_SR, Finset.card_union_of_disjoint hdisj_SR,
          hScard, hRcard]
        omega
      rw [← hcard_ins]
      exact Finset.card_le_card hsub
  · intro P₀ P₁ hP₀ hP₁
    by_contra hge
    push Not at hge
    let A := L.filter (fun x => u₀ x = P₀.eval x ∧ u₁ x = P₁.eval x)
    change L.card - e ≤ A.card at hge
    by_cases hP₁z : P₁ = 0
    · have hA_sub : A ⊆ L \ S := by
        intro x hx
        rw [Finset.mem_filter] at hx
        rw [Finset.mem_sdiff]
        refine ⟨hx.1, fun hxS => ?_⟩
        have h1 := hx.2.2
        simp only [u₁, hxS, ↓reduceIte, hP₁z, Polynomial.eval_zero] at h1
        have hxnotR : x ∉ R := Finset.disjoint_left.1 hdisj_SR hxS
        exact hQne_on x hxnotR h1
      have hA_le : A.card ≤ L.card - (e + 1) := by
        calc A.card ≤ (L \ S).card := Finset.card_le_card hA_sub
          _ = L.card - (e + 1) := by rw [Finset.card_sdiff_of_subset hSL, hScard]
      omega
    · let D := A ∩ (L \ S)
      have hD_roots₁ : ∀ d ∈ D, P₁.eval d = 0 := by
        intro d hd
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff] at hd
        have h1 := hd.1.2.2
        simp [u₁, hd.2.2] at h1
        exact h1.symm
      have hD_roots₀ : ∀ d ∈ D, P₀.eval d = 0 := by
        intro d hd
        rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff] at hd
        have h0 := hd.1.2.1
        simp [u₀, hd.2.2] at h0
        exact h0.symm
      have hD_le : D.card ≤ k - 1 := by
        have hsub : D ⊆ L.filter (fun x => P₁.eval x = 0) := by
          intro d hd
          rw [Finset.mem_filter]
          exact ⟨(Finset.mem_sdiff.1 (Finset.mem_inter.1 hd).2).1, hD_roots₁ d hd⟩
        have hle := card_filter_eval_eq_zero_le_natDegree L hP₁z
        have := Finset.card_le_card hsub
        omega
      have hA_split : A.card = (A ∩ S).card + D.card := by
        have hU : A = (A ∩ S) ∪ D := by
          ext x
          simp only [D, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          constructor
          · intro hx
            by_cases hxS : x ∈ S
            · exact Or.inl ⟨hx, hxS⟩
            · exact Or.inr ⟨hx, (Finset.mem_filter.1 hx).1, hxS⟩
          · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
        have hdj : Disjoint (A ∩ S) D := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hx2).2).2 (Finset.mem_inter.1 hx1).2
        conv_lhs => rw [hU]
        exact Finset.card_union_of_disjoint hdj
      have hAS_le : (A ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
      have hD_eq : D.card = k - 1 := by omega
      have hAS_eq : (A ∩ S).card = S.card := by omega
      have hS_sub_A : S ⊆ A := by
        have hEq : A ∩ S = S := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        intro x hx
        rw [← hEq] at hx
        exact (Finset.mem_inter.1 hx).1
      let G : Polynomial F := ∏ d ∈ D, (X - C d)
      have ⟨hGmon, hGdeg⟩ := monic_prod_X_sub_C D
      rw [hD_eq] at hGdeg
      have hdvd : ∀ P : Polynomial F, (∀ d ∈ D, P.eval d = 0) → G ∣ P := by
        intro P hPr
        have hpair : ∀ d ∈ D, (X - C d) ∣ P := fun d hd =>
          Polynomial.dvd_iff_isRoot.2 (hPr d hd)
        have hcop : Set.Pairwise (D : Set F) (fun a b => IsCoprime (X - C a) (X - C b)) := by
          intro a _ b _ hab
          exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.2 (sub_ne_zero.2 hab))
        exact Finset.prod_dvd_of_coprime hcop hpair
      obtain ⟨q₁, hq₁⟩ := hdvd P₁ hD_roots₁
      obtain ⟨q₀, hq₀⟩ := hdvd P₀ hD_roots₀
      have hq₁ne : q₁ ≠ 0 := by
        intro h0; simp [h0] at hq₁; exact hP₁z hq₁
      have hq₁deg : q₁.natDegree = 0 := by
        have h := congr_arg Polynomial.natDegree hq₁
        rw [hGmon.natDegree_mul' hq₁ne, hGdeg] at h
        omega
      have hq₀deg : q₀.natDegree = 0 := by
        by_cases hq₀z : q₀ = 0
        · simp [hq₀z]
        · have h := congr_arg Polynomial.natDegree hq₀
          rw [hGmon.natDegree_mul' hq₀z, hGdeg] at h
          omega
      obtain ⟨c₁, rfl⟩ := Polynomial.natDegree_eq_zero.1 hq₁deg
      obtain ⟨c₀, rfl⟩ := Polynomial.natDegree_eq_zero.1 hq₀deg
      have hc₁ne : c₁ ≠ 0 := by intro h; simp [h] at hq₁ne
      have hS2 : 1 < S.card := by omega
      obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.1 hS2
      have hGneS : ∀ s ∈ S, G.eval s ≠ 0 := by
        intro s hs
        simp only [G, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [Finset.prod_ne_zero_iff]
        intro d hd
        exact sub_ne_zero.2 fun h => (Finset.mem_sdiff.1 (Finset.mem_inter.1 hd).2).2 (h ▸ hs)
      have hsc : ∀ s ∈ S, c₀ = s * c₁ := by
        intro s hs
        have hsA := Finset.mem_filter.1 (hS_sub_A hs)
        have h0 : s * Q.eval s = G.eval s * c₀ := by
          have := hsA.2.1
          simp only [u₀, hs, ↓reduceIte, hq₀, Polynomial.eval_mul, Polynomial.eval_C] at this
          exact this
        have h1 : Q.eval s = G.eval s * c₁ := by
          have := hsA.2.2
          simp only [u₁, hs, ↓reduceIte, hq₁, Polynomial.eval_mul, Polynomial.eval_C] at this
          exact this
        have hmul : G.eval s * c₀ = G.eval s * (s * c₁) := by
          calc G.eval s * c₀ = s * Q.eval s := h0.symm
            _ = s * (G.eval s * c₁) := by rw [h1]
            _ = G.eval s * (s * c₁) := by ring
        exact mul_left_cancel₀ (hGneS s hs) hmul
      have heq : s₁ * c₁ = s₂ * c₁ := (hsc s₁ hs₁).symm.trans (hsc s₂ hs₂)
      exact hne (mul_right_cancel₀ hc₁ne heq)

/-! ## Part III: Unified `d`-to-1 Folding Beyond-Johnson Obstruction (PPL 097 & PPL 162) -/

/-- **PPL 097 Unified `d`-to-1 Folding List-Decoding Lower Bound**:
For any field `F`, evaluation domain `L : Finset F`, quotient image `Y : Finset F`, monic folding
polynomial `φ : Polynomial F` of `natDegree = d ≥ 1` whose fibers in `L` over every `y ∈ Y` have
size `≥ d`, and `k' ≥ 1` (`k = d * k'`), the single received word `w(x) = (φ.eval x) ^ (k' + 1)`
admits a list `Λ : Finset (Polynomial F)` of distinct polynomials of `natDegree < d * k'`, each
agreeing with `w` on at least `d * k' + d` points of `L`, whose size equals the number of zero-sum
`(k' + 1)`-subsets of `Y`.

Specializing to `φ(X) = X^d` on multiplicative subgroups `H_(dm) → H_m` yields the algebraic core
of Krachun–Kazanin–Haböck (ePrint 2026/782); specializing to linearized subspace polynomials
yields binary-field additive-folding list-decoding obstructions. -/
theorem ppl097_folding_list_decoding_lower_bound
    {F : Type*} [Field F] [DecidableEq F] (L Y : Finset F)
    (φ : Polynomial F) {d k' : ℕ}
    (hd : 1 ≤ d) (hk' : 1 ≤ k') (hφdeg : φ.natDegree = d)
    (hfib : ∀ y ∈ Y, d ≤ (L.filter (fun x => φ.eval x = y)).card) :
    ∃ Λ : Finset (Polynomial F),
      Λ.card = ((Y.powersetCard (k' + 1)).filter (fun T => ∑ y ∈ T, y = 0)).card ∧
      (∀ Q ∈ Λ, Q.natDegree < d * k') ∧
      (∀ Q ∈ Λ, d * k' + d ≤
        (L.filter (fun x => Q.eval x = (φ.eval x) ^ (k' + 1))).card) := by
  let Z0 : Finset (Finset F) := (Y.powersetCard (k' + 1)).filter (fun T => ∑ y ∈ T, y = 0)
  let mkQ : Finset F → Polynomial F := fun T =>
    (X ^ (k' + 1) - C (∑ y ∈ T, y) * X ^ k' - ∏ y ∈ T, (X - C y)).comp φ
  have hmkQ_eval : ∀ T ∈ Z0, ∀ x : F,
      (mkQ T).eval x = (φ.eval x) ^ (k' + 1) - ∏ y ∈ T, (φ.eval x - y) := by
    intro T hT x
    have hsum : ∑ y ∈ T, y = 0 := (Finset.mem_filter.1 hT).2
    simp only [mkQ, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      hsum, zero_mul, sub_zero]
  have hmkQ_deg : ∀ T ∈ Z0, (mkQ T).natDegree < d * k' := by
    intro T hT
    have hcard : T.card = k' + 1 := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hT).1).2
    set H := X ^ (k' + 1) - C (∑ y ∈ T, y) * X ^ k' - ∏ y ∈ T, (X - C y)
    have hHdeg : H.natDegree < k' := natDegree_residual_poly_lt T hk' hcard
    have hcomp : (H.comp φ).natDegree ≤ H.natDegree * φ.natDegree :=
      Polynomial.natDegree_comp_le
    rw [hφdeg] at hcomp
    calc (mkQ T).natDegree ≤ H.natDegree * d := hcomp
      _ < k' * d := Nat.mul_lt_mul_of_pos_right hHdeg (by omega)
      _ = d * k' := mul_comm k' d
  have hmkQ_agr : ∀ T ∈ Z0,
      d * k' + d ≤ (L.filter (fun x => (mkQ T).eval x = (φ.eval x) ^ (k' + 1))).card := by
    intro T hT
    have hTY : T ⊆ Y := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hT).1).1
    have hcard : T.card = k' + 1 := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hT).1).2
    let U := T.biUnion (fun y => L.filter (fun x => φ.eval x = y))
    have hUsub : U ⊆ L.filter (fun x => (mkQ T).eval x = (φ.eval x) ^ (k' + 1)) := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨y, hyT, hxf⟩ := hx
      rw [Finset.mem_filter] at hxf ⊢
      refine ⟨hxf.1, ?_⟩
      rw [hmkQ_eval T hT x, hxf.2]
      have hprod : ∏ y' ∈ T, (y - y') = 0 := Finset.prod_eq_zero hyT (sub_self y)
      rw [hprod, sub_zero]
    have hdisj : Set.PairwiseDisjoint (T : Set F) (fun y => L.filter (fun x => φ.eval x = y)) := by
      intro y₁ _ y₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
    have hUcard : d * k' + d ≤ U.card := by
      rw [Finset.card_biUnion hdisj]
      calc d * k' + d = (k' + 1) * d := by ring
        _ = T.card * d := by rw [hcard]
        _ = ∑ _y ∈ T, d := by simp
        _ ≤ ∑ y ∈ T, (L.filter (fun x => φ.eval x = y)).card :=
            Finset.sum_le_sum fun y hyT => hfib y (hTY hyT)
    exact le_trans hUcard (Finset.card_le_card hUsub)
  have hmkQ_inj : Set.InjOn mkQ (Z0 : Set (Finset F)) := by
    intro T₁ hT₁ T₂ hT₂ hEq
    have hT₁Y : T₁ ⊆ Y := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hT₁).1).1
    have hT₂Y : T₂ ⊆ Y := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hT₂).1).1
    ext y
    constructor
    · intro hy1
      have hfib_pos : 0 < (L.filter (fun x => φ.eval x = y)).card :=
        lt_of_lt_of_le (by omega) (hfib y (hT₁Y hy1))
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hfib_pos
      have hφx : φ.eval x = y := (Finset.mem_filter.1 hx).2
      have hev := congr_arg (fun P => P.eval x) hEq
      rw [hmkQ_eval T₁ hT₁ x, hmkQ_eval T₂ hT₂ x, hφx] at hev
      have hprod1 : ∏ y' ∈ T₁, (y - y') = 0 := Finset.prod_eq_zero hy1 (sub_self y)
      rw [hprod1, sub_zero] at hev
      have hprod2 : ∏ y' ∈ T₂, (y - y') = 0 := by linear_combination hev
      obtain ⟨y', hy'2, hsub0⟩ := Finset.prod_eq_zero_iff.1 hprod2
      exact (sub_eq_zero.1 hsub0) ▸ hy'2
    · intro hy2
      have hfib_pos : 0 < (L.filter (fun x => φ.eval x = y)).card :=
        lt_of_lt_of_le (by omega) (hfib y (hT₂Y hy2))
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hfib_pos
      have hφx : φ.eval x = y := (Finset.mem_filter.1 hx).2
      have hev := congr_arg (fun P => P.eval x) hEq
      rw [hmkQ_eval T₁ hT₁ x, hmkQ_eval T₂ hT₂ x, hφx] at hev
      have hprod2 : ∏ y' ∈ T₂, (y - y') = 0 := Finset.prod_eq_zero hy2 (sub_self y)
      rw [hprod2, sub_zero] at hev
      have hprod1 : ∏ y' ∈ T₁, (y - y') = 0 := by linear_combination -hev
      obtain ⟨y', hy'1, hsub0⟩ := Finset.prod_eq_zero_iff.1 hprod1
      exact (sub_eq_zero.1 hsub0) ▸ hy'1
  refine ⟨Z0.image mkQ, Finset.card_image_of_injOn hmkQ_inj, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hQ
    exact hmkQ_deg T hT
  · intro Q hQ
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hQ
    exact hmkQ_agr T hT

/-- **PPL 162 Unified `d`-to-1 Folding MCA Counterexample**:
Under the same hypotheses as `ppl097_folding_list_decoding_lower_bound`, consider the affine line
`u₀(x) = (φ.eval x) ^ (k' + 1)`, `u₁(x) = (φ.eval x) ^ k'`:
1. Every pair `(P₀, P₁)` of degree `< d * k'` has common agreement **at most `d * k'`** (strictly
   below `d * k' + d`) with `(u₀, u₁)` on `L`.
2. Yet **every** `z` in the negated restricted `(k' + 1)`-fold sumset
   `-(Σ_(k'+1)(Y)) = (Y.powersetCard (k' + 1)).image (fun T => -(∑ y ∈ T, y))`
   admits a polynomial `Q` of `natDegree < d * k'` agreeing with `u₀ + z • u₁` on at least
   `d * k' + d` points of `L`. -/
theorem ppl097_folding_mca_counterexample
    {F : Type*} [Field F] [DecidableEq F] (L Y : Finset F)
    (φ : Polynomial F) {d k' : ℕ}
    (hd : 1 ≤ d) (hk' : 1 ≤ k') (hφmon : φ.Monic) (hφdeg : φ.natDegree = d)
    (hfib : ∀ y ∈ Y, d ≤ (L.filter (fun x => φ.eval x = y)).card) :
    (∀ P₀ P₁ : Polynomial F, P₀.natDegree < d * k' → P₁.natDegree < d * k' →
      (L.filter (fun x => (φ.eval x) ^ (k' + 1) = P₀.eval x ∧
        (φ.eval x) ^ k' = P₁.eval x)).card ≤ d * k') ∧
    (∀ z ∈ (Y.powersetCard (k' + 1)).image (fun T => -(∑ y ∈ T, y)),
      ∃ Q : Polynomial F, Q.natDegree < d * k' ∧
        d * k' + d ≤ (L.filter (fun x =>
          (φ.eval x) ^ (k' + 1) + z * (φ.eval x) ^ k' = Q.eval x)).card) := by
  constructor
  · intro P₀ P₁ _ hP₁
    have hpow_deg : (φ ^ k').natDegree = d * k' := by
      rw [hφmon.natDegree_pow, hφdeg, mul_comm]
    have hdiff_ne : φ ^ k' - P₁ ≠ 0 := by
      intro h0
      have hEq : φ ^ k' = P₁ := sub_eq_zero.1 h0
      rw [← hEq, hpow_deg] at hP₁
      exact lt_irrefl _ hP₁
    have hdiff_deg : (φ ^ k' - P₁).natDegree ≤ d * k' :=
      le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_of_eq hpow_deg) (le_of_lt hP₁))
    have hsub : L.filter (fun x => (φ.eval x) ^ (k' + 1) = P₀.eval x ∧
        (φ.eval x) ^ k' = P₁.eval x) ⊆ L.filter (fun x => (φ ^ k' - P₁).eval x = 0) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by simp [hx.2.2]⟩
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (card_filter_eval_eq_zero_le_natDegree L hdiff_ne) hdiff_deg)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨T, hT, rfl⟩ := hz
    obtain ⟨hTY, hTcard⟩ := Finset.mem_powersetCard.1 hT
    set H : Polynomial F := X ^ (k' + 1) - C (∑ y ∈ T, y) * X ^ k' - ∏ y ∈ T, (X - C y)
    let Q : Polynomial F := H.comp φ
    have hHdeg : H.natDegree < k' := natDegree_residual_poly_lt T hk' hTcard
    have hQdeg : Q.natDegree < d * k' := by
      have hcomp : (H.comp φ).natDegree ≤ H.natDegree * φ.natDegree :=
        Polynomial.natDegree_comp_le
      rw [hφdeg] at hcomp
      calc Q.natDegree ≤ H.natDegree * d := hcomp
        _ < k' * d := Nat.mul_lt_mul_of_pos_right hHdeg (by omega)
        _ = d * k' := mul_comm k' d
    refine ⟨Q, hQdeg, ?_⟩
    let U := T.biUnion (fun y => L.filter (fun x => φ.eval x = y))
    have hUsub : U ⊆ L.filter (fun x =>
        (φ.eval x) ^ (k' + 1) + -(∑ y ∈ T, y) * (φ.eval x) ^ k' = Q.eval x) := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨y, hyT, hxf⟩ := hx
      rw [Finset.mem_filter] at hxf ⊢
      refine ⟨hxf.1, ?_⟩
      have hprod : ∏ y' ∈ T, (φ.eval x - y') = 0 := by
        rw [hxf.2]
        exact Finset.prod_eq_zero hyT (sub_self y)
      simp only [Q, H, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        hprod, sub_zero]
      ring
    have hdisj : Set.PairwiseDisjoint (T : Set F) (fun y => L.filter (fun x => φ.eval x = y)) := by
      intro y₁ _ y₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_filter] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
    have hUcard : d * k' + d ≤ U.card := by
      rw [Finset.card_biUnion hdisj]
      calc d * k' + d = (k' + 1) * d := by ring
        _ = T.card * d := by rw [hTcard]
        _ = ∑ _y ∈ T, d := by simp
        _ ≤ ∑ y ∈ T, (L.filter (fun x => φ.eval x = y)).card :=
            Finset.sum_le_sum fun y hyT => hfib y (hTY hyT)
    exact le_trans hUcard (Finset.card_le_card hUsub)

/-! ## Part IV: Certified Prime-Field Beyond-Johnson Counterexamples (`ZMod 37` and `ZMod 97`) -/

section ConcreteWitnesses

private def H12_37 : Finset (ZMod 37) := {1, 6, 8, 10, 11, 14, 23, 26, 27, 29, 31, 36}

private def wit37 (z : ZMod 37) : Finset (ZMod 37) :=
  match z.val / 10 with
  | 0 =>
    match z.val % 10 with
    | 0 => {1, 6, 8, 23, 36}
    | 1 => {1, 6, 8, 10, 11}
    | 2 => {1, 6, 8, 26, 31}
    | 3 => {1, 6, 8, 27, 29}
    | 4 => {1, 6, 8, 26, 29}
    | 5 => {1, 6, 8, 23, 31}
    | 6 => {1, 6, 8, 26, 27}
    | 7 => {1, 6, 8, 23, 29}
    | 8 => {1, 6, 10, 23, 26}
    | 9 => {1, 6, 8, 14, 36}
    | _ => ∅
  | 1 =>
    match z.val % 10 with
    | 0 => {1, 6, 8, 23, 26}
    | 1 => {1, 6, 11, 14, 31}
    | 2 => {1, 6, 8, 11, 36}
    | 3 => {1, 6, 8, 10, 36}
    | 4 => {1, 6, 8, 14, 31}
    | 5 => {1, 6, 10, 11, 31}
    | 6 => {1, 6, 8, 14, 29}
    | 7 => {1, 6, 8, 11, 31}
    | 8 => {1, 6, 8, 10, 31}
    | 9 => {1, 6, 8, 11, 29}
    | _ => ∅
  | 2 =>
    match z.val % 10 with
    | 0 => {1, 6, 8, 10, 29}
    | 1 => {1, 6, 8, 11, 27}
    | 2 => {1, 6, 8, 10, 27}
    | 3 => {1, 6, 8, 10, 26}
    | 4 => {1, 6, 23, 26, 31}
    | 5 => {1, 6, 8, 11, 23}
    | 6 => {1, 6, 8, 10, 23}
    | 7 => {1, 6, 10, 31, 36}
    | 8 => {1, 6, 11, 29, 36}
    | 9 => {1, 6, 8, 31, 36}
    | _ => ∅
  | 3 =>
    match z.val % 10 with
    | 0 => {1, 6, 11, 27, 36}
    | 1 => {1, 6, 8, 29, 36}
    | 2 => {1, 6, 10, 11, 14}
    | 3 => {1, 6, 8, 27, 36}
    | 4 => {1, 6, 8, 11, 14}
    | 5 => {1, 6, 8, 10, 14}
    | 6 => {1, 6, 8, 29, 31}
    | _ => ∅
  | _ => ∅

private def zero37 (i : Fin 24) : Finset (ZMod 37) :=
  match i.val / 10 with
  | 0 =>
    match i.val % 10 with
    | 0 => {1, 6, 8, 23, 36}
    | 1 => {1, 6, 10, 26, 31}
    | 2 => {1, 6, 11, 27, 29}
    | 3 => {1, 6, 14, 26, 27}
    | 4 => {1, 8, 10, 26, 29}
    | 5 => {1, 8, 11, 23, 31}
    | 6 => {1, 10, 11, 23, 29}
    | 7 => {1, 10, 14, 23, 26}
    | 8 => {1, 14, 29, 31, 36}
    | 9 => {1, 23, 27, 29, 31}
    | _ => ∅
  | 1 =>
    match i.val % 10 with
    | 0 => {6, 8, 10, 14, 36}
    | 1 => {6, 8, 10, 23, 27}
    | 2 => {6, 8, 11, 23, 26}
    | 3 => {6, 11, 27, 31, 36}
    | 4 => {6, 14, 26, 29, 36}
    | 5 => {6, 23, 26, 27, 29}
    | 6 => {8, 10, 11, 14, 31}
    | 7 => {8, 10, 26, 31, 36}
    | 8 => {8, 11, 27, 29, 36}
    | 9 => {8, 14, 26, 27, 36}
    | _ => ∅
  | 2 =>
    match i.val % 10 with
    | 0 => {10, 11, 23, 31, 36}
    | 1 => {10, 14, 27, 29, 31}
    | 2 => {11, 14, 23, 27, 36}
    | 3 => {11, 14, 26, 29, 31}
    | _ => ∅
  | _ => ∅

private lemma H12_37_eq :
    Finset.univ.filter (fun x : ZMod 37 => x ≠ 0 ∧ x ^ 12 = 1) = H12_37 := by
  decide

private lemma wit37_spec :
    ∀ z : ZMod 37, wit37 z ⊆ H12_37 ∧ (wit37 z).card = 5 ∧ -(∑ y ∈ wit37 z, y) = z := by
  decide

private lemma zero37_spec :
    (∀ i j : Fin 24, zero37 i = zero37 j → i = j) ∧
    (∀ i : Fin 24, zero37 i ⊆ H12_37 ∧ (zero37 i).card = 5 ∧ ∑ y ∈ zero37 i, y = 0) := by
  decide

private def H16_97 : Finset (ZMod 97) := {1, 8, 12, 18, 22, 27, 33, 47, 50, 64, 70, 75, 79, 85, 89, 96}

private def wit97_16 (z : ZMod 97) : Finset (ZMod 97) :=
  match z.val / 10 with
  | 0 =>
    match z.val % 10 with
    | 0 => {1, 12, 22, 70, 89}
    | 1 => {1, 8, 18, 22, 47}
    | 2 => {1, 8, 12, 27, 47}
    | 3 => {1, 8, 18, 75, 89}
    | 4 => {1, 8, 12, 22, 50}
    | 5 => {1, 8, 12, 79, 89}
    | 6 => {1, 8, 22, 27, 33}
    | 7 => {1, 8, 12, 22, 47}
    | 8 => {1, 8, 12, 18, 50}
    | 9 => {1, 8, 12, 75, 89}
    | _ => ∅
  | 1 =>
    match z.val % 10 with
    | 0 => {1, 8, 18, 27, 33}
    | 1 => {1, 8, 12, 18, 47}
    | 2 => {1, 8, 18, 70, 85}
    | 3 => {1, 8, 12, 64, 96}
    | 4 => {1, 8, 12, 70, 89}
    | 5 => {1, 8, 18, 22, 33}
    | 6 => {1, 8, 12, 27, 33}
    | 7 => {1, 8, 22, 50, 96}
    | 8 => {1, 8, 12, 70, 85}
    | 9 => {1, 8, 12, 75, 79}
    | _ => ∅
  | 2 =>
    match z.val % 10 with
    | 0 => {1, 8, 12, 64, 89}
    | 1 => {1, 8, 12, 22, 33}
    | 2 => {1, 8, 18, 70, 75}
    | 3 => {1, 8, 27, 50, 85}
    | 4 => {1, 8, 12, 64, 85}
    | 5 => {1, 8, 12, 18, 33}
    | 6 => {1, 8, 27, 47, 85}
    | 7 => {1, 8, 12, 22, 27}
    | 8 => {1, 8, 12, 70, 75}
    | 9 => {1, 8, 22, 64, 70}
    | _ => ∅
  | 3 =>
    match z.val % 10 with
    | 0 => {1, 8, 12, 47, 96}
    | 1 => {1, 8, 12, 18, 27}
    | 2 => {1, 8, 18, 50, 85}
    | 3 => {1, 8, 18, 64, 70}
    | 4 => {1, 8, 12, 50, 89}
    | 5 => {1, 8, 18, 47, 85}
    | 6 => {1, 8, 12, 18, 22}
    | 7 => {1, 8, 12, 47, 89}
    | 8 => {1, 8, 12, 50, 85}
    | 9 => {1, 8, 12, 64, 70}
    | _ => ∅
  | 4 =>
    match z.val % 10 with
    | 0 => {1, 8, 22, 27, 96}
    | 1 => {1, 8, 12, 47, 85}
    | 2 => {1, 8, 18, 50, 75}
    | 3 => {1, 8, 22, 50, 70}
    | 4 => {1, 8, 12, 33, 96}
    | 5 => {1, 8, 18, 33, 89}
    | 6 => {1, 8, 22, 47, 70}
    | 7 => {1, 8, 12, 47, 79}
    | 8 => {1, 8, 12, 50, 75}
    | 9 => {1, 8, 18, 22, 96}
    | _ => ∅
  | 5 =>
    match z.val % 10 with
    | 0 => {1, 8, 12, 27, 96}
    | 1 => {1, 8, 12, 33, 89}
    | 2 => {1, 8, 22, 47, 64}
    | 3 => {1, 8, 12, 50, 70}
    | 4 => {1, 8, 47, 85, 96}
    | 5 => {1, 8, 12, 22, 96}
    | 6 => {1, 8, 12, 47, 70}
    | 7 => {1, 8, 12, 27, 89}
    | 8 => {1, 8, 50, 85, 89}
    | 9 => {1, 8, 12, 18, 96}
    | _ => ∅
  | 6 =>
    match z.val % 10 with
    | 0 => {1, 8, 18, 22, 85}
    | 1 => {1, 8, 12, 27, 85}
    | 2 => {1, 8, 12, 22, 89}
    | 3 => {1, 8, 64, 70, 85}
    | 4 => {1, 8, 18, 33, 70}
    | 5 => {1, 8, 12, 33, 75}
    | 6 => {1, 8, 12, 18, 89}
    | 7 => {1, 8, 12, 27, 79}
    | 8 => {1, 8, 33, 85, 96}
    | 9 => {1, 8, 47, 70, 96}
    | _ => ∅
  | 7 =>
    match z.val % 10 with
    | 0 => {1, 8, 12, 18, 85}
    | 1 => {1, 8, 12, 27, 75}
    | 2 => {1, 8, 12, 22, 79}
    | 3 => {1, 8, 50, 70, 89}
    | 4 => {1, 8, 27, 85, 96}
    | 5 => {1, 8, 18, 22, 70}
    | 6 => {1, 8, 12, 18, 79}
    | 7 => {1, 8, 50, 70, 85}
    | 8 => {1, 8, 27, 33, 47}
    | 9 => {1, 8, 18, 89, 96}
    | _ => ∅
  | 8 =>
    match z.val % 10 with
    | 0 => {1, 8, 12, 18, 75}
    | 1 => {1, 8, 12, 22, 70}
    | 2 => {1, 8, 12, 27, 64}
    | 3 => {1, 8, 18, 85, 96}
    | 4 => {1, 8, 18, 33, 50}
    | 5 => {1, 8, 12, 18, 70}
    | 6 => {1, 8, 22, 27, 50}
    | 7 => {1, 8, 12, 22, 64}
    | 8 => {1, 12, 22, 79, 89}
    | 9 => {1, 8, 12, 85, 96}
    | _ => ∅
  | 9 =>
    match z.val % 10 with
    | 0 => {1, 8, 12, 33, 50}
    | 1 => {1, 8, 12, 18, 64}
    | 2 => {1, 8, 22, 79, 89}
    | 3 => {1, 8, 12, 33, 47}
    | 4 => {1, 8, 22, 70, 96}
    | 5 => {1, 8, 12, 79, 96}
    | 6 => {1, 8, 12, 27, 50}
    | _ => ∅
  | _ => ∅

private def zero97_16 (i : Fin 16) : Finset (ZMod 97) :=
  match i.val with
  | 0 => {1, 12, 22, 70, 89}
  | 1 => {1, 12, 27, 75, 79}
  | 2 => {1, 12, 47, 64, 70}
  | 3 => {1, 18, 22, 64, 89}
  | 4 => {1, 47, 75, 79, 89}
  | 5 => {8, 18, 22, 50, 96}
  | 6 => {8, 18, 33, 50, 85}
  | 7 => {8, 27, 33, 47, 79}
  | 8 => {8, 27, 75, 85, 96}
  | 9 => {8, 33, 75, 79, 96}
  | 10 => {12, 27, 33, 47, 75}
  | 11 => {12, 47, 64, 79, 89}
  | 12 => {18, 22, 70, 85, 96}
  | 13 => {18, 50, 64, 70, 89}
  | 14 => {22, 50, 64, 70, 85}
  | 15 => {27, 33, 50, 85, 96}
  | _ => ∅

private lemma H16_97_eq :
    Finset.univ.filter (fun x : ZMod 97 => x ≠ 0 ∧ x ^ 16 = 1) = H16_97 := by
  decide

private lemma wit97_16_spec :
    ∀ z : ZMod 97, wit97_16 z ⊆ H16_97 ∧ (wit97_16 z).card = 5 ∧ -(∑ y ∈ wit97_16 z, y) = z := by
  decide

private lemma zero97_16_spec :
    (∀ i j : Fin 16, zero97_16 i = zero97_16 j → i = j) ∧
    (∀ i : Fin 16, zero97_16 i ⊆ H16_97 ∧ (zero97_16 i).card = 5 ∧ ∑ y ∈ zero97_16 i, y = 0) := by
  decide

private def H32_97 : Finset (ZMod 97) := {1, 8, 12, 18, 19, 20, 22, 27, 28, 30, 33, 34, 42, 45, 46, 47, 50, 51, 52, 55, 63, 64, 67, 69, 70, 75, 77, 78, 79, 85, 89, 96}

private def H8_97 : Finset (ZMod 97) := {1, 22, 33, 47, 50, 64, 75, 96}

private def wit97_8 (i : Fin 25) : Finset (ZMod 97) :=
  match i.val / 10 with
  | 0 =>
    match i.val % 10 with
    | 0 => {1, 96}
    | 1 => {22, 64}
    | 2 => {33, 50}
    | 3 => {33, 47}
    | 4 => {1, 75}
    | 5 => {75, 96}
    | 6 => {22, 50}
    | 7 => {22, 47}
    | 8 => {1, 64}
    | 9 => {64, 96}
    | _ => ∅
  | 1 =>
    match i.val % 10 with
    | 0 => {22, 33}
    | 1 => {1, 50}
    | 2 => {50, 96}
    | 3 => {1, 47}
    | 4 => {47, 96}
    | 5 => {64, 75}
    | 6 => {1, 33}
    | 7 => {33, 96}
    | 8 => {50, 75}
    | 9 => {47, 75}
    | _ => ∅
  | 2 =>
    match i.val % 10 with
    | 0 => {1, 22}
    | 1 => {22, 96}
    | 2 => {50, 64}
    | 3 => {47, 64}
    | 4 => {33, 75}
    | _ => ∅
  | _ => ∅

private def zero97_8 (i : Fin 4) : Finset (ZMod 97) :=
  match i.val with
  | 0 => {1, 96}
  | 1 => {22, 75}
  | 2 => {33, 64}
  | 3 => {47, 50}
  | _ => ∅

private lemma H32_97_eq :
    Finset.univ.filter (fun x : ZMod 97 => x ≠ 0 ∧ x ^ 32 = 1) = H32_97 := by
  decide

private lemma H8_97_eq :
    Finset.univ.filter (fun x : ZMod 97 => x ≠ 0 ∧ x ^ 8 = 1) = H8_97 := by
  decide

private lemma H32_97_fibers :
    ∀ y ∈ H8_97, 4 ≤ (H32_97.filter (fun x : ZMod 97 => x ^ 4 = y)).card := by
  decide

private lemma wit97_8_spec :
    (∀ i j : Fin 25, -(∑ y ∈ wit97_8 i, y) = -(∑ y ∈ wit97_8 j, y) → i = j) ∧
    (∀ i : Fin 25, wit97_8 i ⊆ H8_97 ∧ (wit97_8 i).card = 2) := by
  decide

private lemma zero97_8_spec :
    (∀ i j : Fin 4, zero97_8 i = zero97_8 j → i = j) ∧
    (∀ i : Fin 4, zero97_8 i ⊆ H8_97 ∧ (zero97_8 i).card = 2 ∧ ∑ y ∈ zero97_8 i, y = 0) := by
  decide

end ConcreteWitnesses

/-- **Certified Prime-Field Beyond-Johnson Counterexample (`ZMod 37`, `H₁₂`, `n = 12, k = 4, t = 5`)**:
On the multiplicative subgroup `L = {x ∈ ZMod 37 | x ≠ 0 ∧ x ^ 12 = 1}` of order `12`, at
agreement threshold `t = 5` — **strictly beyond the Johnson bound** (`5 * 5 < 12 * (4 - 1)`):
1. **(PPL 097)** `w(x) = x ^ 5` admits at least **24 distinct** polynomials of `natDegree < 4`
   agreeing with `w` on `≥ 5` points of `L`.
2. **(PPL 162)** The affine line `(x ^ 5, x ^ 4)` has common agreement **at most `4`** with
   `RS_<4(L)`, yet **every single `z : ZMod 37` (37 / 37 = 100% of the field)** makes
   `x ^ 5 + z * x ^ 4` agree with a degree-`< 4` polynomial on `≥ 5` points of `L`. -/
theorem ppl097_prime_field_f37_beyond_johnson :
    let L : Finset (ZMod 37) := Finset.univ.filter (fun x => x ≠ 0 ∧ x ^ 12 = 1)
    L.card = 12 ∧ 5 * 5 < L.card * (4 - 1) ∧
    (∃ Λ : Finset (Polynomial (ZMod 37)),
      24 ≤ Λ.card ∧
      (∀ Q ∈ Λ, Q.natDegree < 4) ∧
      (∀ Q ∈ Λ, 5 ≤ (L.filter (fun x => Q.eval x = x ^ 5)).card)) ∧
    (∀ P₀ P₁ : Polynomial (ZMod 37), P₀.natDegree < 4 → P₁.natDegree < 4 →
      (L.filter (fun x => x ^ 5 = P₀.eval x ∧ x ^ 4 = P₁.eval x)).card ≤ 4) ∧
    (∀ z : ZMod 37, ∃ Q : Polynomial (ZMod 37), Q.natDegree < 4 ∧
      5 ≤ (L.filter (fun x => x ^ 5 + z * x ^ 4 = Q.eval x)).card) := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  dsimp only
  rw [H12_37_eq]
  have hcard : H12_37.card = 12 := by decide
  have hfib : ∀ y ∈ H12_37, 1 ≤ (H12_37.filter (fun x => (X : Polynomial (ZMod 37)).eval x = y)).card := by
    intro y hy
    have hy' : y ∈ H12_37.filter (fun x => (X : Polynomial (ZMod 37)).eval x = y) := by
      simp [hy]
    exact Finset.card_pos.2 ⟨y, hy'⟩
  have hLD := ppl097_folding_list_decoding_lower_bound H12_37 H12_37 (X : Polynomial (ZMod 37))
    (d := 1) (k' := 4) (by norm_num) (by norm_num) Polynomial.natDegree_X hfib
  have hMCA := ppl097_folding_mca_counterexample H12_37 H12_37 (X : Polynomial (ZMod 37))
    (d := 1) (k' := 4) (by norm_num) (by norm_num) Polynomial.monic_X Polynomial.natDegree_X hfib
  refine ⟨hcard, by omega, ?_, ?_, ?_⟩
  · obtain ⟨Λ, hΛcard, hΛdeg, hΛagr⟩ := hLD
    have h24 : 24 ≤ ((H12_37.powersetCard 5).filter (fun T => ∑ y ∈ T, y = 0)).card := by
      have hinj : Function.Injective zero37 := fun i j h => zero37_spec.1 i j h
      have hsub : Finset.univ.image zero37 ⊆
          (H12_37.powersetCard 5).filter (fun T => ∑ y ∈ T, y = 0) := by
        intro T hT
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hT
        have hs := zero37_spec.2 i
        exact Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨hs.1, hs.2.1⟩, hs.2.2⟩
      calc 24 = (Finset.univ : Finset (Fin 24)).card := by simp
        _ = (Finset.univ.image zero37).card := (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ((H12_37.powersetCard 5).filter (fun T => ∑ y ∈ T, y = 0)).card :=
            Finset.card_le_card hsub
    refine ⟨Λ, ?_, ?_, ?_⟩
    · rw [hΛcard]; exact h24
    · intro Q hQ; simpa using hΛdeg Q hQ
    · intro Q hQ; simpa using hΛagr Q hQ
  · intro P₀ P₁ hP₀ hP₁
    simpa using hMCA.1 P₀ P₁ (by simpa using hP₀) (by simpa using hP₁)
  · intro z
    have hz : z ∈ (H12_37.powersetCard 5).image (fun T => -(∑ y ∈ T, y)) := by
      rw [Finset.mem_image]
      have hw := wit37_spec z
      exact ⟨wit37 z, Finset.mem_powersetCard.2 ⟨hw.1, hw.2.1⟩, hw.2.2⟩
    simpa using hMCA.2 z hz

/-- **Certified Prime-Field Rate-`1/4` Beyond-Johnson Counterexample (`ZMod 97`, `H₁₆`, `n = 16, k = 4, t = 5`)**:
On the smooth multiplicative subgroup `L = {x ∈ ZMod 97 | x ≠ 0 ∧ x ^ 16 = 1}` of order `16 = 2^4`
at exact Proximity Prize rate `ρ = 4/16 = 1/4` and agreement `t = 5` — **strictly beyond the
Johnson bound** (`5 * 5 < 16 * (4 - 1)`):
1. **(PPL 097)** `w(x) = x ^ 5` admits at least **16 distinct** polynomials of `natDegree < 4`
   agreeing with `w` on `≥ 5` points of `L`.
2. **(PPL 162)** The affine line `(x ^ 5, x ^ 4)` has common agreement **at most `4`** with
   `RS_<4(L)`, yet **every single `z : ZMod 97` (97 / 97 = 100% of the field)** makes
   `x ^ 5 + z * x ^ 4` agree with a degree-`< 4` polynomial on `≥ 5` points of `L`. -/
theorem ppl097_prime_field_f97_rate_quarter_beyond_johnson :
    let L : Finset (ZMod 97) := Finset.univ.filter (fun x => x ≠ 0 ∧ x ^ 16 = 1)
    L.card = 16 ∧ 5 * 5 < L.card * (4 - 1) ∧
    (∃ Λ : Finset (Polynomial (ZMod 97)),
      16 ≤ Λ.card ∧
      (∀ Q ∈ Λ, Q.natDegree < 4) ∧
      (∀ Q ∈ Λ, 5 ≤ (L.filter (fun x => Q.eval x = x ^ 5)).card)) ∧
    (∀ P₀ P₁ : Polynomial (ZMod 97), P₀.natDegree < 4 → P₁.natDegree < 4 →
      (L.filter (fun x => x ^ 5 = P₀.eval x ∧ x ^ 4 = P₁.eval x)).card ≤ 4) ∧
    (∀ z : ZMod 97, ∃ Q : Polynomial (ZMod 97), Q.natDegree < 4 ∧
      5 ≤ (L.filter (fun x => x ^ 5 + z * x ^ 4 = Q.eval x)).card) := by
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  dsimp only
  rw [H16_97_eq]
  have hcard : H16_97.card = 16 := by decide
  have hfib : ∀ y ∈ H16_97, 1 ≤ (H16_97.filter (fun x => (X : Polynomial (ZMod 97)).eval x = y)).card := by
    intro y hy
    have hy' : y ∈ H16_97.filter (fun x => (X : Polynomial (ZMod 97)).eval x = y) := by
      simp [hy]
    exact Finset.card_pos.2 ⟨y, hy'⟩
  have hLD := ppl097_folding_list_decoding_lower_bound H16_97 H16_97 (X : Polynomial (ZMod 97))
    (d := 1) (k' := 4) (by norm_num) (by norm_num) Polynomial.natDegree_X hfib
  have hMCA := ppl097_folding_mca_counterexample H16_97 H16_97 (X : Polynomial (ZMod 97))
    (d := 1) (k' := 4) (by norm_num) (by norm_num) Polynomial.monic_X Polynomial.natDegree_X hfib
  refine ⟨hcard, by omega, ?_, ?_, ?_⟩
  · obtain ⟨Λ, hΛcard, hΛdeg, hΛagr⟩ := hLD
    have h16 : 16 ≤ ((H16_97.powersetCard 5).filter (fun T => ∑ y ∈ T, y = 0)).card := by
      have hinj : Function.Injective zero97_16 := fun i j h => zero97_16_spec.1 i j h
      have hsub : Finset.univ.image zero97_16 ⊆
          (H16_97.powersetCard 5).filter (fun T => ∑ y ∈ T, y = 0) := by
        intro T hT
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hT
        have hs := zero97_16_spec.2 i
        exact Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨hs.1, hs.2.1⟩, hs.2.2⟩
      calc 16 = (Finset.univ : Finset (Fin 16)).card := by simp
        _ = (Finset.univ.image zero97_16).card := (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ((H16_97.powersetCard 5).filter (fun T => ∑ y ∈ T, y = 0)).card :=
            Finset.card_le_card hsub
    refine ⟨Λ, ?_, ?_, ?_⟩
    · rw [hΛcard]; exact h16
    · intro Q hQ; simpa using hΛdeg Q hQ
    · intro Q hQ; simpa using hΛagr Q hQ
  · intro P₀ P₁ hP₀ hP₁
    simpa using hMCA.1 P₀ P₁ (by simpa using hP₀) (by simpa using hP₁)
  · intro z
    have hz : z ∈ (H16_97.powersetCard 5).image (fun T => -(∑ y ∈ T, y)) := by
      rw [Finset.mem_image]
      have hw := wit97_16_spec z
      exact ⟨wit97_16 z, Finset.mem_powersetCard.2 ⟨hw.1, hw.2.1⟩, hw.2.2⟩
    simpa using hMCA.2 z hz

/-- **Certified Smooth 4-to-1 Folding Rate-`1/8` Beyond-Johnson Counterexample (`ZMod 97`, `H₃₂`, `n = 32, k = 4, t = 8`)**:
On the smooth multiplicative subgroup `L = {x ∈ ZMod 97 | x ≠ 0 ∧ x ^ 32 = 1}` of order `32 = 2^5`
at exact Proximity Prize rate `ρ = 4/32 = 1/8` and agreement `t = 8` (relative agreement `1/4`,
**strictly beyond the Johnson bound** `8 * 8 < 32 * (4 - 1)`), using the 4-to-1 folding map `X ^ 4`:
1. **(PPL 097)** `w(x) = x ^ 8` admits at least **4 distinct** polynomials of `natDegree < 4`
   agreeing with `w` on `≥ 8` points of `L`.
2. **(PPL 162)** The affine line `(x ^ 8, x ^ 4)` has common agreement **at most `4`** with
   `RS_<4(L)`, yet at least **25 distinct** challenges `z ∈ ZMod 97` make `x ^ 8 + z * x ^ 4`
   agree with a degree-`< 4` polynomial on `≥ 8` points of `L`. -/
theorem ppl097_prime_field_f97_folding_rate_eighth_beyond_johnson :
    let L : Finset (ZMod 97) := Finset.univ.filter (fun x => x ≠ 0 ∧ x ^ 32 = 1)
    L.card = 32 ∧ 8 * 8 < L.card * (4 - 1) ∧
    (∃ Λ : Finset (Polynomial (ZMod 97)),
      4 ≤ Λ.card ∧
      (∀ Q ∈ Λ, Q.natDegree < 4) ∧
      (∀ Q ∈ Λ, 8 ≤ (L.filter (fun x => Q.eval x = x ^ 8)).card)) ∧
    (∀ P₀ P₁ : Polynomial (ZMod 97), P₀.natDegree < 4 → P₁.natDegree < 4 →
      (L.filter (fun x => x ^ 8 = P₀.eval x ∧ x ^ 4 = P₁.eval x)).card ≤ 4) ∧
    (∃ Z : Finset (ZMod 97), 25 ≤ Z.card ∧
      ∀ z ∈ Z, ∃ Q : Polynomial (ZMod 97), Q.natDegree < 4 ∧
        8 ≤ (L.filter (fun x => x ^ 8 + z * x ^ 4 = Q.eval x)).card) := by
  have : Fact (Nat.Prime 97) := ⟨by norm_num⟩
  dsimp only
  rw [H32_97_eq]
  have hcard : H32_97.card = 32 := by decide
  have hφmon : (X ^ 4 : Polynomial (ZMod 97)).Monic := Polynomial.monic_X_pow 4
  have hφdeg : (X ^ 4 : Polynomial (ZMod 97)).natDegree = 4 := Polynomial.natDegree_X_pow 4
  have hfib : ∀ y ∈ H8_97,
      4 ≤ (H32_97.filter (fun x => (X ^ 4 : Polynomial (ZMod 97)).eval x = y)).card := by
    intro y hy
    simpa using H32_97_fibers y hy
  have hLD := ppl097_folding_list_decoding_lower_bound H32_97 H8_97 (X ^ 4 : Polynomial (ZMod 97))
    (d := 4) (k' := 1) (by norm_num) (by norm_num) hφdeg hfib
  have hMCA := ppl097_folding_mca_counterexample H32_97 H8_97 (X ^ 4 : Polynomial (ZMod 97))
    (d := 4) (k' := 1) (by norm_num) (by norm_num) hφmon hφdeg hfib
  have hpow8 : ∀ x : ZMod 97, (x ^ 4) ^ 2 = x ^ 8 := fun x => by ring
  refine ⟨hcard, by omega, ?_, ?_, ?_⟩
  · obtain ⟨Λ, hΛcard, hΛdeg, hΛagr⟩ := hLD
    have h4 : 4 ≤ ((H8_97.powersetCard 2).filter (fun T => ∑ y ∈ T, y = 0)).card := by
      have hinj : Function.Injective zero97_8 := fun i j h => zero97_8_spec.1 i j h
      have hsub : Finset.univ.image zero97_8 ⊆
          (H8_97.powersetCard 2).filter (fun T => ∑ y ∈ T, y = 0) := by
        intro T hT
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hT
        have hs := zero97_8_spec.2 i
        exact Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨hs.1, hs.2.1⟩, hs.2.2⟩
      calc 4 = (Finset.univ : Finset (Fin 4)).card := by simp
        _ = (Finset.univ.image zero97_8).card := (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ((H8_97.powersetCard 2).filter (fun T => ∑ y ∈ T, y = 0)).card :=
            Finset.card_le_card hsub
    refine ⟨Λ, ?_, ?_, ?_⟩
    · rw [hΛcard]; exact h4
    · intro Q hQ; simpa using hΛdeg Q hQ
    · intro Q hQ
      have h := hΛagr Q hQ
      simp only [Polynomial.eval_pow, Polynomial.eval_X, hpow8] at h
      exact h
  · intro P₀ P₁ hP₀ hP₁
    have h := hMCA.1 P₀ P₁ (by simpa using hP₀) (by simpa using hP₁)
    simp only [Polynomial.eval_pow, Polynomial.eval_X, hpow8, pow_one, mul_one] at h
    exact h
  · let Z : Finset (ZMod 97) := Finset.univ.image (fun i : Fin 25 => -(∑ y ∈ wit97_8 i, y))
    have hZcard : Z.card = 25 := by
      have hinj : Function.Injective (fun i : Fin 25 => -(∑ y ∈ wit97_8 i, y)) :=
        fun i j h => wit97_8_spec.1 i j h
      rw [Finset.card_image_of_injective _ hinj]
      simp
    refine ⟨Z, by omega, ?_⟩
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hz
    have hmem : -(∑ y ∈ wit97_8 i, y) ∈ (H8_97.powersetCard 2).image (fun T => -(∑ y ∈ T, y)) := by
      rw [Finset.mem_image]
      have hw := wit97_8_spec.2 i
      exact ⟨wit97_8 i, Finset.mem_powersetCard.2 ⟨hw.1, hw.2⟩, rfl⟩
    have h := hMCA.2 _ hmem
    simp only [Polynomial.eval_pow, Polynomial.eval_X, hpow8, pow_one, mul_one] at h
    exact h

end PPL097
