/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-!
# PPL 050 (Erdős Problem #28 — Erdős–Turán Additive Basis Conjecture)

## Scope & Honest Labeling
This file formalizes a comprehensive pure-Mathlib milestone (`0` `sorry`, `0` custom or `private`
definitions in any public theorem signature) for **Erdős Problem #28** (`$500`, VERIFIED OPEN as of
2026):

> If `A ⊆ ℕ` is such that `A + A` contains all but finitely many natural numbers, then
> `limsup_{n → ∞} (1_A * 1_A)(n) = ∞`.

- **Honest Scope:** The full Erdős–Turán Conjecture (`limsup_{n → ∞} r_A(n) = ∞`) remains **OPEN**.
  No finite lower bound solves `limsup = ∞`, and this file makes **no claim** to solve the full
  conjecture.
- **Verified Pure-Mathlib Theorems in this File:**
  1. `ppl050_oscillation_bound`: **General Quantitative Representation Oscillation Theorem** —
     for every `A : Set ℕ` and integers `1 ≤ a ≤ b`, if `2 * a - 1 ≤ r_A(n) ≤ 2 * b + 1` for all
     sufficiently large `n`, then `(b - a)^2 ≥ a + b` (proved completely elementarily via discrete
     Parseval on `M`-th roots of unity, avoiding Lebesgue integration and measure theory).
  2. `ppl050_limsup_ge_six` & `ppl050_limsup_ge_six_enat`: **Grekos–Haddad–Helou–Pihko (2003)** —
     for every asymptotic additive basis `A ⊆ ℕ` of order 2 (`(A + A)ᶜ.Finite`),
     `∀ N, ∃ n ≥ N, 6 ≤ r_A(n)` and `6 ≤ Filter.limsup (fun n => (r_A(n) : ℕ∞)) Filter.atTop`.
  3. `ppl050_limsup_ge_ten_of_ge_three` & `ppl050_limsup_ge_twelve_of_ge_five`: Higher-multiplicity
     asymptotic basis lower bounds (`r_A ≥ 3` eventually `⇒ limsup ≥ 10`; `r_A ≥ 5` eventually
     `⇒ limsup ≥ 12`).
  4. `ppl050_dirac_not_eventually_const`: **Dirac's Theorem (1951)** — for every infinite
     `A ⊆ ℕ`, the ordered representation function `r_A(n)` is never eventually constant.
  5. `ppl050_finite_abelian_ruzsa_ge_six`: **Universal Finite Abelian Group Ruzsa Lower Bound** —
     for every finite abelian group `G` of order `|G| ≥ 46` and every additive basis `A ⊆ G`
     (`A + A = G`), `max_{g ∈ G} r_A(g) ≥ 6` (generalizing Sándor–Yang's `R_m ≥ 6` via pure
     additive energy `E(A) = ∑ r_A(g)^2 = ∑ d_A(k)^2` and integer convexity).
  6. `ppl050_int_sidon_basis_barrier`: **Exact `ℤ` vs. `ℕ` Counterexample Barrier (Nathanson)** —
     there exists `A ⊆ ℤ` with `A + A = ℤ` such that every `z ∈ ℤ` has a **unique unordered
     representation** (hence `1 ≤ r_A(z) ≤ 2` for every `z ∈ ℤ`), proving rigorously that
     Erdős–Turán fails over `ℤ` and requires one-sidedness `A ⊆ ℕ`.
  7. `ppl050_cantor_binary_basis`: **Explicit Thin Order-2 Basis (`|A ∩ [0, 4^k)| < 2 · 2^k`)**
     with `A + A = ℕ` and `r_A((4^m - 1)/3) ≥ 2^m` (hence `limsup r_A(n) = ∞`).
  8. `ppl050_asymptotic_iff_exact_basis`: Exact equivalence between the asymptotic-basis and
     exact-basis formulations of Erdős Problem #28.
-/

open scoped Pointwise
open Classical

namespace PPL050

/-! ### Section 1: Ordered Representation Function & Parity Lemma -/

private noncomputable def rep (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card

private noncomputable def truncRep (A : Set ℕ) (N n : ℕ) : ℕ :=
  ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card

private lemma truncRep_eq_rep_of_le (A : Set ℕ) {N n : ℕ} (hn : n ≤ N) :
    truncRep A N n = rep A n := by
  unfold truncRep rep
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, _⟩, ha, hb, hab⟩
    exact ⟨⟨by omega, by omega⟩, ha, hb, hab⟩
  · rintro ⟨⟨_, _⟩, ha, hb, hab⟩
    exact ⟨⟨by omega, by omega⟩, ha, hb, hab⟩

private lemma truncRep_le_rep (A : Set ℕ) (N n : ℕ) :
    truncRep A N n ≤ rep A n := by
  unfold truncRep rep
  apply Finset.card_le_card
  intro ⟨a, b⟩ hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  exact ⟨⟨by omega, by omega⟩, hp.2⟩

private lemma rep_le_succ (A : Set ℕ) (n : ℕ) : rep A n ≤ n + 1 := by
  unfold rep
  have hsub :
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n) ⊆
      (Finset.range (n + 1)).image (fun a => (a, n - a)) := by
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image] at hp ⊢
    exact ⟨a, hp.1.1, Prod.ext rfl (by omega)⟩
  calc
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card
        ≤ ((Finset.range (n + 1)).image (fun a => (a, n - a))).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (n + 1)).card := Finset.card_image_le
    _ = n + 1 := Finset.card_range (n + 1)

private lemma rep_pos_of_mem_add {A : Set ℕ} {n : ℕ} (h : n ∈ A + A) : 1 ≤ rep A n := by
  rcases Set.mem_add.mp h with ⟨a, ha, b, hb, hab⟩
  unfold rep
  rw [Finset.one_le_card]
  refine ⟨(a, b), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  exact ⟨⟨by omega, by omega⟩, ha, hb, hab⟩

private lemma rep_odd_imp_half_mem {A : Set ℕ} {n : ℕ} (hodd : rep A n % 2 = 1) :
    ∃ m ∈ A, n = 2 * m := by
  let S := (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)
  let Slt := S.filter (fun p => p.1 < p.2)
  let Sgt := S.filter (fun p => p.2 < p.1)
  let Seq := S.filter (fun p => p.1 = p.2)
  have hlt_gt : Slt.card = Sgt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro ⟨a, b⟩ hp
      simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.2.1, hp.1.2.1, by omega⟩, hp.2⟩
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro ⟨a, b⟩ hp
      refine ⟨(b, a), ?_, rfl⟩
      simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, hp.1.2.2.1, hp.1.2.1, by omega⟩, hp.2⟩
  have hpart : S = (Slt ∪ Sgt) ∪ Seq := by
    ext ⟨a, b⟩
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases lt_trichotomy a b with h1 | h2 | h3
      · exact Or.inl (Or.inl ⟨h, h1⟩)
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (Or.inr ⟨h, h3⟩)
    · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hdisj1 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2; omega
  have hdisj2 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter] at hp1 hp2
    rcases hp1 with ⟨_, hlt⟩ | ⟨_, hgt⟩ <;> omega
  have hcard : S.card = 2 * Slt.card + Seq.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
      hlt_gt, two_mul]
  have hS : S.card = rep A n := rfl
  have hSeq_pos : 0 < Seq.card := by omega
  rcases Finset.card_pos.mp hSeq_pos with ⟨⟨a, b⟩, hab⟩
  simp only [Seq, S, Finset.mem_filter] at hab
  exact ⟨a, hab.1.2.1, by omega⟩

/-! ### Section 2: Elementary Discrete Parseval & Harmonic Pole Bound -/

/-- `M`-th root of unity raised to integer power `k`: `exp(2πi k / M)`. -/
private noncomputable def rootPow (M : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * (k : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I)

private lemma rootPow_zero (M : ℕ) : rootPow M 0 = 1 := by
  simp [rootPow]

private lemma rootPow_add (M : ℕ) (k₁ k₂ : ℤ) :
    rootPow M (k₁ + k₂) = rootPow M k₁ * rootPow M k₂ := by
  unfold rootPow
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma rootPow_mul_nat (M : ℕ) (k : ℤ) (n : ℕ) :
    rootPow M (k * n) = (rootPow M k) ^ n := by
  unfold rootPow
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma star_rootPow (M : ℕ) (k : ℤ) :
    star (rootPow M k) = rootPow M (-k) := by
  unfold rootPow
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma norm_rootPow (M : ℕ) (k : ℤ) : ‖rootPow M k‖ = 1 := by
  unfold rootPow
  exact Complex.norm_exp_ofReal_mul_I _

private lemma rootPow_pow_M {M : ℕ} (hM : 0 < M) (k : ℤ) :
    (rootPow M k) ^ M = 1 := by
  rw [← rootPow_mul_nat]
  unfold rootPow
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have harg : (2 * Real.pi * ((k * (M : ℤ) : ℤ) : ℝ) / (M : ℝ)) = (k : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp [hM']
  rw [harg]
  have : (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

private lemma rootPow_ne_one {M : ℕ} (hM : 0 < M) {k : ℤ}
    (hk0 : k ≠ 0) (hk_lt : k < M) (hk_gt : -(M : ℤ) < k) :
    rootPow M k ≠ 1 := by
  intro heq
  unfold rootPow at heq
  rw [Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨n, hn⟩
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hrew :
      (((2 * Real.pi * (k : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I) =
      (((k : ℝ) / (M : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [hrew] at hn
  have hdiv : (((k : ℝ) / (M : ℝ) : ℝ) : ℂ) = (n : ℂ) := mul_right_cancel₀ h2piI hn
  have hdivR : (k : ℝ) / (M : ℝ) = (n : ℝ) := by exact_mod_cast hdiv
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hkR : (k : ℝ) = (n : ℝ) * (M : ℝ) := (div_eq_iff hM').mp hdivR
  have hkZ : k = n * (M : ℤ) := by exact_mod_cast hkR
  rcases lt_trichotomy n 0 with hn_neg | rfl | hn_pos
  · have : n ≤ -1 := by omega
    have : k ≤ -(M : ℤ) := by nlinarith
    omega
  · simp at hkZ; exact hk0 hkZ
  · have : 1 ≤ n := by omega
    have : (M : ℤ) ≤ k := by nlinarith
    omega

private lemma sum_rootPow_ortho {M : ℕ} (hM : 0 < M) {a b : ℕ} (ha : a < M) (hb : b < M) :
    (∑ j : Fin M, rootPow M ((a : ℤ) * (j : ℕ)) * star (rootPow M ((b : ℤ) * (j : ℕ)))) =
      if a = b then (M : ℂ) else 0 := by
  have hterm : ∀ j : Fin M,
      rootPow M ((a : ℤ) * (j : ℕ)) * star (rootPow M ((b : ℤ) * (j : ℕ))) =
        (rootPow M ((a : ℤ) - (b : ℤ))) ^ (j : ℕ) := by
    intro j
    rw [star_rootPow, ← rootPow_add, ← rootPow_mul_nat]
    congr 1; ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j => (rootPow M ((a : ℤ) - (b : ℤ))) ^ j) M]
  by_cases hab : a = b
  · subst hab
    simp [rootPow_zero]
  · rw [if_neg hab]
    have hne : rootPow M ((a : ℤ) - (b : ℤ)) ≠ 1 :=
      rootPow_ne_one hM (by omega) (by omega) (by omega)
    rw [geom_sum_eq hne, rootPow_pow_M hM, sub_self, zero_div]

/-- Exact discrete Parseval identity for finite real-coefficient trigonometric polynomials on
`Fin M`. -/
private lemma discrete_parseval {M L : ℕ} (hM : 0 < M) (hLM : L ≤ M) (c : ℕ → ℝ) :
    (∑ j : Fin M, ‖∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))‖ ^ 2) =
      (M : ℝ) * ∑ n ∈ Finset.range L, (c n) ^ 2 := by
  have hC :
      (∑ j : Fin M,
        (‖∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))‖ ^ 2 : ℂ)) =
      ((M : ℂ) * ∑ n ∈ Finset.range L, ((c n) ^ 2 : ℂ)) := by
    have hnorm : ∀ j : Fin M,
        (‖∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))‖ ^ 2 : ℂ) =
        (∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))) *
          star (∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))) := by
      intro j
      rw [Complex.star_def, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    simp_rw [hnorm]
    have hexp : ∀ j : Fin M,
        (∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))) *
          star (∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))) =
        ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
          ((c a : ℂ) * (c b : ℂ)) *
            (rootPow M ((a : ℤ) * (j : ℕ)) * star (rootPow M ((b : ℤ) * (j : ℕ)))) := by
      intro j
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    trans ∑ a ∈ Finset.range L, ∑ b ∈ Finset.range L,
        ((c a : ℂ) * (c b : ℂ)) *
          ∑ j : Fin M, rootPow M ((a : ℤ) * (j : ℕ)) * star (rootPow M ((b : ℤ) * (j : ℕ)))
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.mul_sum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have haM : a < M := lt_of_lt_of_le (Finset.mem_range.mp ha) hLM
      have hinner :
          ∑ b ∈ Finset.range L, ((c a : ℂ) * (c b : ℂ)) *
            (∑ j : Fin M, rootPow M ((a : ℤ) * (j : ℕ)) * star (rootPow M ((b : ℤ) * (j : ℕ)))) =
          ∑ b ∈ Finset.range L, if a = b then ((c a : ℂ) * (c b : ℂ)) * (M : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun b hb => ?_
        have hbM : b < M := lt_of_lt_of_le (Finset.mem_range.mp hb) hLM
        rw [sum_rootPow_ortho hM haM hbM]
        split_ifs <;> ring
      rw [hinner]
      simp [ha, sq]
      ring
  have hC' :
      ((∑ j : Fin M, ‖∑ n ∈ Finset.range L, (c n : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))‖ ^ 2 : ℝ) : ℂ) =
      (((M : ℝ) * ∑ n ∈ Finset.range L, (c n) ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact hC
  exact Complex.ofReal_injective hC'

/-- Elementary Cauchy–Schwarz inequality for finite real sums. -/
private lemma sq_sum_le_card_mul_sum_sq_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
  have h0 : (0 : ℝ) ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp :
      ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
        2 * (s.card : ℝ) * (∑ x ∈ s, (f x) ^ 2) - 2 * (∑ x ∈ s, f x) ^ 2 := by
    have h1 : ∀ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
        (s.card : ℝ) * (f x) ^ 2 - 2 * f x * (∑ y ∈ s, f y) + ∑ y ∈ s, (f y) ^ 2 := by
      intro x _
      have hsub : ∀ y ∈ s, (f x - f y) ^ 2 = (f x) ^ 2 - 2 * f x * f y + (f y) ^ 2 := by
        intro y _; ring
      rw [Finset.sum_congr rfl hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ s, 2 * f x = 2 * ∑ x ∈ s, f x := by rw [← Finset.mul_sum]
    rw [h2]; ring
  linarith

/-- Lower bound `‖1 - r * exp(θ * I)‖ ≥ 2 * sqrt r * |sin(θ / 2)|`. -/
private lemma norm_one_sub_r_exp_ge_sin {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    2 * Real.sqrt r * |Real.sin (θ / 2)| ≤
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have hsq :
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 =
        (1 - r) ^ 2 + 4 * r * (Real.sin (θ / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero, add_zero, zero_sub]
    have hcos : Real.cos θ = 1 - 2 * (Real.sin (θ / 2)) ^ 2 := by
      have h := Real.cos_two_mul (θ / 2)
      have hsc := Real.sin_sq_add_cos_sq (θ / 2)
      have h2 : 2 * (θ / 2) = θ := by ring
      rw [h2] at h
      linarith
    have hsc2 : (Real.sin θ) ^ 2 + (Real.cos θ) ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    nlinarith
  have hge : (2 * Real.sqrt r * |Real.sin (θ / 2)|) ^ 2 ≤
      ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ^ 2 := by
    rw [hsq]
    have hsr : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hr
    have habs : |Real.sin (θ / 2)| ^ 2 = (Real.sin (θ / 2)) ^ 2 := sq_abs _
    have h1 : (2 * Real.sqrt r * |Real.sin (θ / 2)|) ^ 2 = 4 * r * (Real.sin (θ / 2)) ^ 2 := by
      calc (2 * Real.sqrt r * |Real.sin (θ / 2)|) ^ 2
          = 4 * (Real.sqrt r) ^ 2 * |Real.sin (θ / 2)| ^ 2 := by ring
        _ = 4 * r * (Real.sin (θ / 2)) ^ 2 := by rw [hsr, habs]
    linarith [sq_nonneg (1 - r)]
  have hL : 0 ≤ 2 * Real.sqrt r * |Real.sin (θ / 2)| := by positivity
  have hR : 0 ≤ ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith

/-- Elementary dyadic harmonic sum bound: `∑_{j=1}^{2^m} 1/j ≤ m + 1`. -/
private lemma harmonic_pow_two_le (m : ℕ) :
    (∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ m), (1 : ℝ) / (j : ℝ)) ≤ (m : ℝ) + 1 := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hsplit : Finset.Icc (1 : ℕ) (2 ^ (m + 1)) =
        Finset.Icc (1 : ℕ) (2 ^ m) ∪ Finset.Icc (2 ^ m + 1) (2 ^ (m + 1)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union]
      have hpow : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
      omega
    have hdisj : Disjoint (Finset.Icc (1 : ℕ) (2 ^ m)) (Finset.Icc (2 ^ m + 1) (2 ^ (m + 1))) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hblock :
        (∑ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / (j : ℝ)) ≤ 1 := by
      have hterm : ∀ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)),
          (1 : ℝ) / (j : ℝ) ≤ (1 : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
        intro j hj
        simp only [Finset.mem_Icc] at hj
        have hpos : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by positivity
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast (by omega : 2 ^ m ≤ j))
      calc
        (∑ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / (j : ℝ))
            ≤ ∑ _j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1)), (1 : ℝ) / ((2 ^ m : ℕ) : ℝ) :=
              Finset.sum_le_sum hterm
        _ = ((Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1))).card : ℝ) * ((1 : ℝ) / ((2 ^ m : ℕ) : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = 1 := by
              rw [Nat.card_Icc]
              have hc : 2 ^ (m + 1) + 1 - (2 ^ m + 1) = 2 ^ m := by
                rw [pow_succ]; omega
              rw [hc]
              have hne : ((2 ^ m : ℕ) : ℝ) ≠ 0 := by positivity
              field_simp [hne]
    push_cast
    linarith

/-- Pole-sum bound on `Fin (2 * 2^m + 1)` for `r ∈ [1/4, 1)`:
`((1 : ℝ) / M) * ∑_{j < M} ‖∑_{n < M} (r * ω^j)^n‖ ≤ 2 / (M * (1 - r)) + 2 * (m + 1)`. -/
private lemma pole_sum_bound (m : ℕ) {r : ℝ} (hr1 : (1 : ℝ) / 4 ≤ r) (hr2 : r < 1) :
    let N : ℕ := 2 ^ m
    let M : ℕ := 2 * N + 1
    ((1 : ℝ) / (M : ℝ)) *
        (∑ j : Fin M, ‖∑ n ∈ Finset.range M, ((r : ℂ) * rootPow M (j : ℤ)) ^ n‖) ≤
      2 / ((M : ℝ) * (1 - r)) + 2 * ((m : ℝ) + 1) := by
  intro N M
  have hMpos : 0 < M := Nat.succ_pos _
  have hMrpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hr0 : 0 ≤ r := by linarith
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt r := by
    have : ((1 : ℝ) / 2) ^ 2 ≤ r := by linarith
    calc (1 : ℝ) / 2 = Real.sqrt (((1 : ℝ) / 2) ^ 2) := by
            rw [Real.sqrt_sq (by norm_num)]
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt this
  -- Pointwise bound on the geometric sum at z = r * ω^j
  have hgeom_le : ∀ j : Fin M,
      ‖∑ n ∈ Finset.range M, ((r : ℂ) * rootPow M (j : ℤ)) ^ n‖ ≤
        2 / ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ := by
    intro j
    set z : ℂ := (r : ℂ) * rootPow M (j : ℤ)
    have hnz : ‖z‖ = r := by
      simp [z, norm_rootPow, abs_of_nonneg hr0]
    have hz_ne : z ≠ 1 := by
      intro h
      have := congrArg norm h
      rw [hnz, norm_one] at this
      linarith
    rw [geom_sum_eq hz_ne, norm_div]
    have hnum : ‖z ^ M - 1‖ ≤ 2 := by
      calc ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = r ^ M + 1 := by rw [norm_pow, hnz, norm_one]
        _ ≤ 1 + 1 := by
              have : r ^ M ≤ 1 := pow_le_one₀ hr0 hr2.le
              linarith
        _ = 2 := by norm_num
    have hden : ‖z - 1‖ = ‖(1 : ℂ) - z‖ := norm_sub_rev z 1
    rw [hden]
    exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
  -- Lower bound on ‖1 - r * ω^j‖ for j = 0, 1 ≤ j ≤ N, and N < j < M
  have h0 : ‖(1 : ℂ) - (r : ℂ) * rootPow M (0 : ℤ)‖ = 1 - r := by
    rw [rootPow_zero, mul_one]
    have : (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hsin_bound : ∀ j : ℕ, 1 ≤ j → j ≤ N →
      2 * (j : ℝ) / (M : ℝ) ≤ ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ := by
    intro j hj1 hjN
    have hstep := norm_one_sub_r_exp_ge_sin hr0 (2 * Real.pi * (j : ℝ) / (M : ℝ))
    have htheta_half : (2 * Real.pi * (j : ℝ) / (M : ℝ)) / 2 = Real.pi * (j : ℝ) / (M : ℝ) := by
      ring
    have hx0 : 0 ≤ Real.pi * (j : ℝ) / (M : ℝ) := by positivity
    have hx_le : Real.pi * (j : ℝ) / (M : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hMrpos (by norm_num : (0 : ℝ) < 2)]
      have h2j : 2 * (j : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show 2 * j ≤ 2 * N + 1 by omega)
      nlinarith [Real.pi_pos]
    have hmul := Real.mul_le_sin hx0 hx_le
    have hsin_ge : 2 * (j : ℝ) / (M : ℝ) ≤ Real.sin (Real.pi * (j : ℝ) / (M : ℝ)) := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have heq : 2 / Real.pi * (Real.pi * (j : ℝ) / (M : ℝ)) = 2 * (j : ℝ) / (M : ℝ) := by
        field_simp [hpi]
      linarith
    have hsin_nn : 0 ≤ Real.sin (Real.pi * (j : ℝ) / (M : ℝ)) := by
      linarith [show (0 : ℝ) ≤ 2 * (j : ℝ) / (M : ℝ) by positivity]
    have h2sr : 1 ≤ 2 * Real.sqrt r := by linarith
    have hEq :
        ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ =
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((2 * Real.pi * (j : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I)‖ := by
      unfold rootPow; congr 3
    rw [hEq]
    rw [htheta_half, abs_of_nonneg hsin_nn] at hstep
    nlinarith
  have hsym : ∀ j : ℕ, N + 1 ≤ j → j < M →
      2 * ((M - j : ℕ) : ℝ) / (M : ℝ) ≤ ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ := by
    intro j hj1 hjM
    have hstep := norm_one_sub_r_exp_ge_sin hr0 (2 * Real.pi * (j : ℝ) / (M : ℝ))
    have htheta_half : (2 * Real.pi * (j : ℝ) / (M : ℝ)) / 2 = Real.pi * (j : ℝ) / (M : ℝ) := by
      ring
    set j' : ℕ := M - j
    have hj'1 : 1 ≤ j' := by omega
    have hj'N : j' ≤ N := by omega
    have hsin_eq : Real.sin (Real.pi * (j : ℝ) / (M : ℝ)) =
        Real.sin (Real.pi * (j' : ℝ) / (M : ℝ)) := by
      have hsum : Real.pi * (j : ℝ) / (M : ℝ) = Real.pi - Real.pi * (j' : ℝ) / (M : ℝ) := by
        have hMne : (M : ℝ) ≠ 0 := hMrpos.ne'
        have hadd : (j : ℝ) + (j' : ℝ) = (M : ℝ) := by exact_mod_cast (show j + (M - j) = M by omega)
        field_simp [hMne]
        linarith
      rw [hsum, Real.sin_pi_sub]
    have hx0 : 0 ≤ Real.pi * (j' : ℝ) / (M : ℝ) := by positivity
    have hx_le : Real.pi * (j' : ℝ) / (M : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hMrpos (by norm_num : (0 : ℝ) < 2)]
      have h2j' : 2 * (j' : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast (show 2 * j' ≤ 2 * N + 1 by omega)
      nlinarith [Real.pi_pos]
    have hmul := Real.mul_le_sin hx0 hx_le
    have hsin_ge : 2 * (j' : ℝ) / (M : ℝ) ≤ Real.sin (Real.pi * (j' : ℝ) / (M : ℝ)) := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have heq : 2 / Real.pi * (Real.pi * (j' : ℝ) / (M : ℝ)) = 2 * (j' : ℝ) / (M : ℝ) := by
        field_simp [hpi]
      linarith
    have hsin_nn : 0 ≤ Real.sin (Real.pi * (j' : ℝ) / (M : ℝ)) := by
      linarith [show (0 : ℝ) ≤ 2 * (j' : ℝ) / (M : ℝ) by positivity]
    have h2sr : 1 ≤ 2 * Real.sqrt r := by linarith
    have hEq :
        ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ =
          ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((2 * Real.pi * (j : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I)‖ := by
      unfold rootPow; congr 3
    rw [hEq]
    rw [htheta_half, hsin_eq, abs_of_nonneg hsin_nn] at hstep
    nlinarith
  -- Sum over Fin M = {0} ∪ Icc 1 N ∪ Icc (N+1) (2N)
  let term : ℕ → ℝ := fun j => ‖∑ n ∈ Finset.range M, ((r : ℂ) * rootPow M (j : ℤ)) ^ n‖
  have hsum_eq_term :
      (∑ j : Fin M, ‖∑ n ∈ Finset.range M, ((r : ℂ) * rootPow M (j : ℤ)) ^ n‖) =
        ∑ j ∈ Finset.range M, term j :=
    Fin.sum_univ_eq_sum_range term M
  rw [hsum_eq_term]
  have hrange_split :
      Finset.range M = ({0} ∪ Finset.Icc 1 N) ∪ Finset.Icc (N + 1) (2 * N) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hd1 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 N) := by
    simp [Finset.disjoint_singleton_left]
  have hd2 : Disjoint ({0} ∪ Finset.Icc 1 N) (Finset.Icc (N + 1) (2 * N)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at h1 h2
    omega
  rw [hrange_split, Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_singleton]
  have hterm0 : term 0 ≤ 2 / (1 - r) := by
    have := hgeom_le ⟨0, hMpos⟩
    simpa [term, h0] using this
  have hsum1 :
      (∑ j ∈ Finset.Icc 1 N, term j) ≤
        (M : ℝ) * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    have hgj := hgeom_le ⟨j, by omega⟩
    have hlb := hsin_bound j hj.1 hj.2
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    have hlbpos : (0 : ℝ) < 2 * (j : ℝ) / (M : ℝ) := by positivity
    calc
      term j
          ≤ 2 / ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ := hgj
      _ ≤ 2 / (2 * (j : ℝ) / (M : ℝ)) := div_le_div_of_nonneg_left (by norm_num) hlbpos hlb
      _ = (M : ℝ) * ((1 : ℝ) / (j : ℝ)) := by field_simp [hMrpos.ne', hjpos.ne']
  have hsum2 :
      (∑ j ∈ Finset.Icc (N + 1) (2 * N), term j) ≤
        (M : ℝ) * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) := by
    have hreidx :
        (∑ j ∈ Finset.Icc (N + 1) (2 * N), (M : ℝ) * ((1 : ℝ) / ((M - j : ℕ) : ℝ))) =
          (M : ℝ) * ∑ j' ∈ Finset.Icc 1 N, (1 : ℝ) / (j' : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun j _ => M - j) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
      · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Icc] at hj₁ hj₂; omega
      · intro j' hj'; refine ⟨M - j', ?_, ?_⟩
        · simp only [Finset.mem_Icc] at hj' ⊢; omega
        · simp only [Finset.mem_Icc] at hj'; omega
      · intro j _; rfl
    rw [← hreidx]
    refine Finset.sum_le_sum fun j hj => ?_
    simp only [Finset.mem_Icc] at hj
    have hgj := hgeom_le ⟨j, by omega⟩
    have hlb := hsym j hj.1 (by omega)
    have hj'pos : (0 : ℝ) < ((M - j : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < M - j by omega)
    have hlbpos : (0 : ℝ) < 2 * ((M - j : ℕ) : ℝ) / (M : ℝ) := by positivity
    calc
      term j
          ≤ 2 / ‖(1 : ℂ) - (r : ℂ) * rootPow M (j : ℤ)‖ := hgj
      _ ≤ 2 / (2 * ((M - j : ℕ) : ℝ) / (M : ℝ)) :=
            div_le_div_of_nonneg_left (by norm_num) hlbpos hlb
      _ = (M : ℝ) * ((1 : ℝ) / ((M - j : ℕ) : ℝ)) := by field_simp [hMrpos.ne', hj'pos.ne']
  have hharm := harmonic_pow_two_le m
  have htot :
      term 0 + (∑ j ∈ Finset.Icc 1 N, term j) + (∑ j ∈ Finset.Icc (N + 1) (2 * N), term j) ≤
      2 / (1 - r) + 2 * (M : ℝ) * ((m : ℝ) + 1) := by
    nlinarith
  calc
    ((1 : ℝ) / (M : ℝ)) *
        (term 0 + (∑ j ∈ Finset.Icc 1 N, term j) + (∑ j ∈ Finset.Icc (N + 1) (2 * N), term j))
        ≤ ((1 : ℝ) / (M : ℝ)) * (2 / (1 - r) + 2 * (M : ℝ) * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 2 / ((M : ℝ) * (1 - r)) + 2 * ((m : ℝ) + 1) := by
          field_simp [hMrpos.ne']

/-! ### Section 3: Truncated Generating Function Identities & Oscillation Theorem -/

/-- Convolution identity for the truncated polynomial `f_N(z) = ∑_{a ∈ A ∩ [0, N]} z^a`:
`f_N(z)^2 = ∑_{n < 2*N+1} truncRep A N n * z^n`. -/
private lemma trunc_poly_sq (A : Set ℕ) (N : ℕ) (z : ℂ) :
    (∑ a ∈ Finset.range (N + 1), (if a ∈ A then (1 : ℂ) else 0) * z ^ a) ^ 2 =
      ∑ n ∈ Finset.range (2 * N + 1), (truncRep A N n : ℂ) * z ^ n := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  have hpart :
      ∑ p ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        ((if p.1 ∈ A then (1 : ℂ) else 0) * z ^ p.1) *
          ((if p.2 ∈ A then (1 : ℂ) else 0) * z ^ p.2) =
      ∑ n ∈ Finset.range (2 * N + 1),
        ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 = n),
          ((if p.1 ∈ A then (1 : ℂ) else 0) * z ^ p.1) *
            ((if p.2 ∈ A then (1 : ℂ) else 0) * z ^ p.2) := by
    symm
    refine Finset.sum_fiberwise_of_maps_to ?_ _
    intro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  rw [hpart]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hinner :
      ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 = n),
        ((if p.1 ∈ A then (1 : ℂ) else 0) * z ^ p.1) *
          ((if p.2 ∈ A then (1 : ℂ) else 0) * z ^ p.2) =
      ∑ p ∈ (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n), z ^ n := by
    have hfeq :
        ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => p.1 + p.2 = n)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A) =
        (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n) := by
      ext p; simp only [Finset.mem_filter]; tauto
    symm
    rw [← hfeq, Finset.sum_filter]
    symm
    refine Finset.sum_congr rfl fun p hp => ?_
    have hsum : p.1 + p.2 = n := (Finset.mem_filter.mp hp).2
    by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;> simp [h1, h2, ← pow_add, hsum]
  rw [hinner, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- Real version: `(∑_{a ∈ A ∩ [0, N]} r^{2a})^2 = ∑_{n < 2*N+1} truncRep A N n * r^{2n}`. -/
private lemma trunc_poly_sq_real (A : Set ℕ) (N : ℕ) (r : ℝ) :
    (∑ a ∈ Finset.range (N + 1), (if a ∈ A then (1 : ℝ) else 0) * r ^ (2 * a)) ^ 2 =
      ∑ n ∈ Finset.range (2 * N + 1), (truncRep A N n : ℝ) * r ^ (2 * n) := by
  have hC := trunc_poly_sq A N ((r ^ 2 : ℝ) : ℂ)
  have hL :
      (∑ a ∈ Finset.range (N + 1), (if a ∈ A then (1 : ℂ) else 0) * ((r ^ 2 : ℝ) : ℂ) ^ a) =
      ((∑ a ∈ Finset.range (N + 1), (if a ∈ A then (1 : ℝ) else 0) * r ^ (2 * a) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ A <;> simp [ha, pow_mul]
  have hR :
      (∑ n ∈ Finset.range (2 * N + 1), (truncRep A N n : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ n) =
      ((∑ n ∈ Finset.range (2 * N + 1), (truncRep A N n : ℝ) * r ^ (2 * n) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pow_mul]
  rw [hL, hR] at hC
  exact_mod_cast hC

/-- Core discrete-Parseval inequality: for every `m : ℕ`, `N = 2^m`, `M = 2*N + 1`, `r ∈ [1/4, 1)`,
and real constant `c ≥ 0`:
`S_R - S_D ≤ E_P^2 + 2 * E_P * sqrt(S_D)`. -/
private lemma discrete_parseval_master (A : Set ℕ) (m : ℕ) {r c : ℝ}
    (hr1 : (1 : ℝ) / 4 ≤ r) (hr2 : r < 1) (hc : 0 ≤ c) :
    let N := 2 ^ m
    let M := 2 * N + 1
    let S_R := ∑ n ∈ Finset.range M, (truncRep A N n : ℝ) * r ^ (2 * n)
    let S_D := ∑ n ∈ Finset.range M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)
    let E_P := c * (2 / ((M : ℝ) * (1 - r)) + 2 * ((m : ℝ) + 1))
    S_R - S_D ≤ E_P ^ 2 + 2 * E_P * Real.sqrt S_D := by
  intro N M S_R S_D E_P
  have hMpos : 0 < M := Nat.succ_pos _
  have hMrpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hr0 : 0 ≤ r := by linarith
  -- Define f_N(r * ω^j), P_N(r * ω^j), D_N(r * ω^j)
  let fval : Fin M → ℂ := fun j =>
    ∑ a ∈ Finset.range (N + 1),
      (((if a ∈ A then (1 : ℝ) else 0) * r ^ a : ℝ) : ℂ) * rootPow M ((a : ℤ) * (j : ℕ))
  let Pval : Fin M → ℂ := fun j =>
    (c : ℂ) * ∑ n ∈ Finset.range M, ((r : ℂ) * rootPow M (j : ℤ)) ^ n
  let Dval : Fin M → ℂ := fun j =>
    ∑ n ∈ Finset.range M,
      ((((truncRep A N n : ℝ) - c) * r ^ n : ℝ) : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))
  -- Exact identity fval(j)^2 = Pval(j) + Dval(j)
  have hdecomp : ∀ j : Fin M, (fval j) ^ 2 = Pval j + Dval j := by
    intro j
    have hf : fval j =
        ∑ a ∈ Finset.range (N + 1),
          (if a ∈ A then (1 : ℂ) else 0) * ((r : ℂ) * rootPow M (j : ℤ)) ^ a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_pow, ← rootPow_mul_nat]
      have hcomm : (j : ℤ) * (a : ℕ) = (a : ℤ) * (j : ℕ) := by ring
      rw [hcomm]
      by_cases ha : a ∈ A <;> simp [ha]
    rw [hf, trunc_poly_sq]
    dsimp only [Pval, Dval]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, ← rootPow_mul_nat]
    have hcomm : (j : ℤ) * (n : ℕ) = (n : ℤ) * (j : ℕ) := by ring
    rw [hcomm]
    push_cast
    ring
  -- Discrete Parseval for fval: (1/M) * ∑ ‖fval j‖^2 = f_N(r^2)
  let F2 : ℝ := ∑ a ∈ Finset.range (N + 1), (if a ∈ A then (1 : ℝ) else 0) * r ^ (2 * a)
  have hF2_nn : 0 ≤ F2 := Finset.sum_nonneg fun a _ => by
    by_cases ha : a ∈ A
    · simp only [if_pos ha, one_mul]; exact pow_nonneg hr0 _
    · simp [ha]
  have hF2_sq : F2 ^ 2 = S_R := trunc_poly_sq_real A N r
  have hPars_f : (∑ j : Fin M, ‖fval j‖ ^ 2) = (M : ℝ) * F2 := by
    have hNle : N + 1 ≤ M := by omega
    have hp := discrete_parseval hMpos hNle (fun a => (if a ∈ A then (1 : ℝ) else 0) * r ^ a)
    change (∑ j : Fin M, ‖∑ a ∈ Finset.range (N + 1),
      (((if a ∈ A then (1 : ℝ) else 0) * r ^ a : ℝ) : ℂ) * rootPow M ((a : ℤ) * (j : ℕ))‖ ^ 2) =
      (M : ℝ) * F2
    rw [hp]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ A
    · simp [ha, ← pow_mul, mul_comm 2 a]
    · simp [ha]
  -- Discrete Parseval for Dval: (1/M) * ∑ ‖Dval j‖^2 = S_D
  have hPars_D : (∑ j : Fin M, ‖Dval j‖ ^ 2) = (M : ℝ) * S_D := by
    have hp := discrete_parseval hMpos le_rfl (fun n => ((truncRep A N n : ℝ) - c) * r ^ n)
    change (∑ j : Fin M, ‖∑ n ∈ Finset.range M,
      ((((truncRep A N n : ℝ) - c) * r ^ n : ℝ) : ℂ) * rootPow M ((n : ℤ) * (j : ℕ))‖ ^ 2) =
      (M : ℝ) * S_D
    rw [hp]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow, ← pow_mul, mul_comm 2 n]
  -- Triangle inequality: ‖fval j‖^2 = ‖fval(j)^2‖ ≤ ‖Pval j‖ + ‖Dval j‖
  have htri : ∀ j : Fin M, ‖fval j‖ ^ 2 ≤ ‖Pval j‖ + ‖Dval j‖ := by
    intro j
    rw [← norm_pow, hdecomp j]
    exact norm_add_le _ _
  have hsum_le : (M : ℝ) * F2 ≤ (∑ j : Fin M, ‖Pval j‖) + (∑ j : Fin M, ‖Dval j‖) := by
    rw [← hPars_f, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => htri j
  -- Pole bound: (1/M) * ∑ ‖Pval j‖ ≤ E_P
  have hP_le : ((1 : ℝ) / (M : ℝ)) * (∑ j : Fin M, ‖Pval j‖) ≤ E_P := by
    have hPb := pole_sum_bound m hr1 hr2
    have hPnorm : ∑ j : Fin M, ‖Pval j‖ =
        c * ∑ j : Fin M, ‖∑ n ∈ Finset.range M, ((r : ℂ) * rootPow M (j : ℤ)) ^ n‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [Pval]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    rw [hPnorm]
    calc
      ((1 : ℝ) / (M : ℝ)) * (c * _)
          = c * (((1 : ℝ) / (M : ℝ)) * _) := by ring
      _ ≤ E_P := mul_le_mul_of_nonneg_left hPb hc
  -- Cauchy–Schwarz on Dval: (1/M) * ∑ ‖Dval j‖ ≤ sqrt S_D
  have hSD_nn : 0 ≤ S_D := Finset.sum_nonneg fun n _ => by positivity
  have hD_le : ((1 : ℝ) / (M : ℝ)) * (∑ j : Fin M, ‖Dval j‖) ≤ Real.sqrt S_D := by
    have hcs := sq_sum_le_card_mul_sum_sq_real (Finset.univ : Finset (Fin M)) (fun j => ‖Dval j‖)
    rw [Finset.card_univ, Fintype.card_fin, hPars_D] at hcs
    have hsq : (((1 : ℝ) / (M : ℝ)) * ∑ j : Fin M, ‖Dval j‖) ^ 2 ≤ S_D := by
      rw [mul_pow, one_div, inv_pow]
      have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      rw [← div_eq_inv_mul, div_le_iff₀ hMsq]
      nlinarith
    have hnn : 0 ≤ ((1 : ℝ) / (M : ℝ)) * ∑ j : Fin M, ‖Dval j‖ :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => norm_nonneg _)
    calc
      ((1 : ℝ) / (M : ℝ)) * ∑ j : Fin M, ‖Dval j‖
          = Real.sqrt ((((1 : ℝ) / (M : ℝ)) * ∑ j : Fin M, ‖Dval j‖) ^ 2) :=
            (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt S_D := Real.sqrt_le_sqrt hsq
  -- Combine: F2 ≤ E_P + sqrt S_D ⇒ S_R = F2^2 ≤ (E_P + sqrt S_D)^2 = E_P^2 + 2 E_P sqrt S_D + S_D
  have hF2_le : F2 ≤ E_P + Real.sqrt S_D := by
    have hdiv : F2 ≤ ((1 : ℝ) / (M : ℝ)) * (∑ j : Fin M, ‖Pval j‖) +
        ((1 : ℝ) / (M : ℝ)) * (∑ j : Fin M, ‖Dval j‖) := by
      have : ((1 : ℝ) / (M : ℝ)) * ((M : ℝ) * F2) ≤
          ((1 : ℝ) / (M : ℝ)) * ((∑ j : Fin M, ‖Pval j‖) + (∑ j : Fin M, ‖Dval j‖)) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
      have hleft : ((1 : ℝ) / (M : ℝ)) * ((M : ℝ) * F2) = F2 := by field_simp [hMrpos.ne']
      linarith [mul_add ((1 : ℝ) / (M : ℝ)) (∑ j : Fin M, ‖Pval j‖) (∑ j : Fin M, ‖Dval j‖)]
    linarith
  have hEP_nn : 0 ≤ E_P := by
    have : 0 ≤ 1 - r := by linarith
    positivity
  have hsq_le : F2 ^ 2 ≤ (E_P + Real.sqrt S_D) ^ 2 := by nlinarith [Real.sqrt_nonneg S_D]
  rw [hF2_sq] at hsq_le
  have hrt : (Real.sqrt S_D) ^ 2 = S_D := Real.sq_sqrt hSD_nn
  nlinarith

/-- Elementary Bernoulli decay: `(1 - 1/K)^K ≤ 1/2` for `K ≥ 2`. -/
private lemma one_sub_inv_pow_le_half {K : ℕ} (hK : 2 ≤ K) :
    ((1 : ℝ) - 1 / (K : ℝ)) ^ K ≤ (1 : ℝ) / 2 := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have hKm1 : (0 : ℝ) < (K : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have h1 : (1 : ℝ) - 1 / (K : ℝ) = ((K : ℝ) - 1) / (K : ℝ) := by field_simp [hKpos.ne']
  have hinv : (K : ℝ) / ((K : ℝ) - 1) = 1 + 1 / ((K : ℝ) - 1) := by field_simp [hKm1.ne']; ring
  have hbern : 1 + (K : ℝ) * (1 / ((K : ℝ) - 1)) ≤ (1 + 1 / ((K : ℝ) - 1)) ^ K :=
    one_add_mul_le_pow (by linarith [show (0 : ℝ) < 1 / ((K : ℝ) - 1) by positivity]) K
  have hge2 : (2 : ℝ) ≤ (1 + 1 / ((K : ℝ) - 1)) ^ K := by
    have hfrac : (1 : ℝ) ≤ (K : ℝ) / ((K : ℝ) - 1) := by
      rw [one_le_div hKm1]; linarith
    have : (K : ℝ) * (1 / ((K : ℝ) - 1)) = (K : ℝ) / ((K : ℝ) - 1) := by ring
    linarith
  rw [h1, div_pow]
  have hpow_pos : (0 : ℝ) < ((K : ℝ) - 1) ^ K := by positivity
  have hKpow_pos : (0 : ℝ) < (K : ℝ) ^ K := by positivity
  rw [div_le_div_iff₀ hKpow_pos (by norm_num : (0 : ℝ) < 2)]
  have h2' : (2 : ℝ) * ((K : ℝ) - 1) ^ K ≤ (K : ℝ) ^ K := by
    rw [← hinv, div_pow, le_div_iff₀ hpow_pos] at hge2
    linarith
  linarith

/-- Elementary growth domination: `2^B ≥ B + 1` for all `B : ℕ`. -/
private lemma add_one_le_two_pow (B : ℕ) : B + 1 ≤ 2 ^ B := by
  induction B with
  | zero => norm_num
  | succ B ih => rw [pow_succ]; omega

/-- Elementary scale selection: for any nonnegative constants `A0 A1 A2 A3 : ℝ` and `N₀ : ℕ`,
there exists `B ≥ 2` with `4 * N₀ + 4 ≤ 2^(4B)` and
`A0 + A1 * 2^(2B) + (A2 * B)^2 + A3 * B * 2^(2B) < (3/32) * 2^(4B)`. -/
private lemma exists_scale_B (N₀ : ℕ) {A0 A1 A2 A3 : ℝ}
    (h0 : 0 ≤ A0) (h1 : 0 ≤ A1) (_h2 : 0 ≤ A2) (h3 : 0 ≤ A3) :
    ∃ B : ℕ, 2 ≤ B ∧ 4 * N₀ + 4 ≤ 2 ^ (4 * B) ∧
      A0 + A1 * (2 ^ (2 * B) : ℝ) + (A2 * (B : ℝ)) ^ 2 +
          A3 * (B : ℝ) * (2 ^ (2 * B) : ℝ) <
        (3 : ℝ) / 32 * (2 ^ (4 * B) : ℝ) := by
  let P : ℝ := A0 + A1 + A2 ^ 2 + A3
  have hP : 0 ≤ P := by positivity
  obtain ⟨B0, hB0⟩ := exists_nat_gt (32 * (P + 1))
  let B := max (max 2 (N₀ + 1)) B0
  refine ⟨B, le_trans (le_max_left _ _) (le_max_left _ _), ?_, ?_⟩
  · have hB_ge : N₀ + 1 ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
    have h4 : 4 * N₀ + 4 ≤ 4 * B := by omega
    have hpow := add_one_le_two_pow (4 * B)
    omega
  · have hB2 : 2 ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
    have hB_gt : 32 * (P + 1) < (B : ℝ) :=
      lt_of_lt_of_le hB0 (by exact_mod_cast le_max_right _ _)
    have hB_le_2B : (B : ℝ) ≤ (2 ^ B : ℝ) := by
      have := add_one_le_two_pow B
      exact_mod_cast (show B ≤ 2 ^ B by omega)
    have h1_le_2B : (1 : ℝ) ≤ (2 ^ B : ℝ) := by
      exact_mod_cast Nat.one_le_pow B 2 (by norm_num)
    have hpow2 : (2 ^ (2 * B) : ℝ) = (2 ^ B : ℝ) * (2 ^ B : ℝ) := by
      rw [← pow_add]; congr 1; omega
    have hpow3 : (2 ^ (3 * B) : ℝ) = (2 ^ B : ℝ) * (2 ^ (2 * B) : ℝ) := by
      rw [← pow_add]; congr 1; omega
    have hpow4 : (2 ^ (4 * B) : ℝ) = (2 ^ B : ℝ) * (2 ^ (3 * B) : ℝ) := by
      rw [← pow_add]; congr 1; omega
    have h2B_ge1 : (1 : ℝ) ≤ (2 ^ (2 * B) : ℝ) := by rw [hpow2]; nlinarith
    have h3B_ge1 : (1 : ℝ) ≤ (2 ^ (3 * B) : ℝ) := by rw [hpow3]; nlinarith
    have h2B_le_3B : (2 ^ (2 * B) : ℝ) ≤ (2 ^ (3 * B) : ℝ) := by rw [hpow3]; nlinarith
    have hB_nn : (0 : ℝ) ≤ (B : ℝ) := by positivity
    have hB2_le_3B : (B : ℝ) ^ 2 ≤ (2 ^ (3 * B) : ℝ) := by
      have h1' : (B : ℝ) ^ 2 ≤ (2 ^ B : ℝ) ^ 2 := pow_le_pow_left₀ hB_nn hB_le_2B 2
      have h2' : (2 ^ B : ℝ) ^ 2 = (2 ^ (2 * B) : ℝ) := by rw [sq, hpow2]
      linarith
    have hB2B_le_3B : (B : ℝ) * (2 ^ (2 * B) : ℝ) ≤ (2 ^ (3 * B) : ℝ) := by
      rw [hpow3]
      exact mul_le_mul_of_nonneg_right hB_le_2B (by positivity)
    have ht0 : A0 ≤ A0 * (2 ^ (3 * B) : ℝ) := le_mul_of_one_le_right h0 h3B_ge1
    have ht1 : A1 * (2 ^ (2 * B) : ℝ) ≤ A1 * (2 ^ (3 * B) : ℝ) :=
      mul_le_mul_of_nonneg_left h2B_le_3B h1
    have ht2 : (A2 * (B : ℝ)) ^ 2 ≤ A2 ^ 2 * (2 ^ (3 * B) : ℝ) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hB2_le_3B (sq_nonneg A2)
    have ht3 : A3 * (B : ℝ) * (2 ^ (2 * B) : ℝ) ≤ A3 * (2 ^ (3 * B) : ℝ) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hB2B_le_3B h3
    have hsum_le :
        A0 + A1 * (2 ^ (2 * B) : ℝ) + (A2 * (B : ℝ)) ^ 2 +
            A3 * (B : ℝ) * (2 ^ (2 * B) : ℝ) ≤
          P * (2 ^ (3 * B) : ℝ) := by
      dsimp only [P]; linarith
    have h32 : P * (2 ^ (3 * B) : ℝ) < (3 : ℝ) / 32 * (2 ^ (4 * B) : ℝ) := by
      rw [hpow4]
      have hgt : P < (3 : ℝ) / 32 * (2 ^ B : ℝ) := by linarith
      have hpos3B : (0 : ℝ) < (2 ^ (3 * B) : ℝ) := by positivity
      calc P * (2 ^ (3 * B) : ℝ)
          < ((3 : ℝ) / 32 * (2 ^ B : ℝ)) * (2 ^ (3 * B) : ℝ) :=
            mul_lt_mul_of_pos_right hgt hpos3B
        _ = (3 : ℝ) / 32 * ((2 ^ B : ℝ) * (2 ^ (3 * B) : ℝ)) := by ring
    linarith

/-- Opaque-parameter analytic step for `ppl050_oscillation_bound`: keeping `K, N, M, r, c, C0, C1`
as lemma parameters prevents `whnf` from ever unfolding `2^(8*B)` during arithmetic tactics. -/
private lemma osc_bounds_contradiction (A : Set ℕ) (a b N₀ B K N M : ℕ) (r c C0 C1 E_P : ℝ)
    (hlo : ∀ n ≥ N₀, 2 * a - 1 ≤ rep A n)
    (hhi : ∀ n ≥ N₀, rep A n ≤ 2 * b + 1)
    (hc_pos : 0 ≤ c)
    (hC0_def : C0 = ((N₀ : ℝ) + 1 + c) ^ 2)
    (hC1_def : C1 = (2 * (b : ℝ) + 1 + c) ^ 2 + 1)
    (heven_gap : ∀ k : ℕ, k % 2 = 0 → 2 * a - 1 ≤ k → k ≤ 2 * b + 1 →
      (3 : ℝ) / 4 ≤ (k : ℝ) - ((k : ℝ) - c) ^ 2)
    (hK4 : 4 ≤ K)
    (hKsq : (K : ℝ) = (2 ^ (2 * B) : ℝ) ^ 2)
    (hK4B : (K : ℝ) = (2 ^ (4 * B) : ℝ))
    (hN0_le_N : N₀ ≤ N)
    (hM_eq : M = 2 * N + 1)
    (hr0 : 0 ≤ r) (hr2 : r < 1)
    (h1mr2_pos : 0 < 1 - r ^ 2)
    (hK_inv_le : 1 / (1 - r ^ 2) ≤ (K : ℝ))
    (hK_half_le : (K : ℝ) / 2 ≤ 1 / (1 - r ^ 2))
    (hr2N_le : r ^ (2 * N) ≤ 1 / ((K : ℝ) * (K : ℝ)))
    (hr2N_le_quarter : r ^ (2 * N) ≤ (1 : ℝ) / 4)
    (hr2N0_ge : (1 : ℝ) / 2 ≤ r ^ (2 * N₀))
    (hEP_nn : 0 ≤ E_P)
    (hEP_le : E_P ≤ c * (2 + 16 * (B : ℝ) + 2))
    (hmaster :
      (∑ n ∈ Finset.range M, (truncRep A N n : ℝ) * r ^ (2 * n)) -
        (∑ n ∈ Finset.range M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)) ≤
      E_P ^ 2 + 2 * E_P * Real.sqrt
        (∑ n ∈ Finset.range M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)))
    (hB_main :
      (N₀ : ℝ) * C0 + C1 +
        (C1 + 1) * (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ) +
        (c * (2 + 16 * (B : ℝ) + 2)) ^ 2 +
        2 * (c * (2 + 16 * (B : ℝ) + 2)) *
          ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) <
      (3 : ℝ) / 32 * (2 ^ (4 * B) : ℝ)) : False := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hKge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
  have hC0_nn : 0 ≤ C0 := by rw [hC0_def]; exact sq_nonneg _
  have hC1_pos : 0 < C1 := by rw [hC1_def]; positivity
  have hN0_le_M : N₀ ≤ M := by omega
  set S_R : ℝ := ∑ n ∈ Finset.range M, (truncRep A N n : ℝ) * r ^ (2 * n)
  set S_D : ℝ := ∑ n ∈ Finset.range M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)
  have hsub_sq_le : ∀ {x U : ℝ}, 0 ≤ x → x ≤ U → (x - c) ^ 2 ≤ (U + c) ^ 2 := by
    intro x U hx hxU
    have hUC : 0 ≤ U + c := by linarith
    rw [sq_le_sq, abs_of_nonneg hUC, abs_le]
    constructor <;> linarith
  -- Geometric sum bound
  have hgeom_all : ∀ L : ℕ, (∑ n ∈ Finset.range L, r ^ (2 * n)) ≤ 1 / (1 - r ^ 2) := by
    intro L
    have hrew : ∑ n ∈ Finset.range L, r ^ (2 * n) = ∑ n ∈ Finset.range L, (r ^ 2) ^ n := by
      refine Finset.sum_congr rfl fun n _ => ?_; rw [pow_mul]
    rw [hrew, geom_sum_eq (by linarith [h1mr2_pos] : r ^ 2 ≠ 1)]
    have hneg : ((r ^ 2) ^ L - 1) / (r ^ 2 - 1) = (1 - (r ^ 2) ^ L) / (1 - r ^ 2) := by
      field_simp [show r ^ 2 - 1 ≠ 0 by linarith, h1mr2_pos.ne']; ring
    rw [hneg]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (sq_nonneg r) L]) h1mr2_pos.le
  -- Upper bound on S_R and sqrt S_R
  have hSR_le : S_R ≤ (((N₀ : ℝ) + 1) * (N₀ : ℝ) + (2 * (b : ℝ) + 1)) * (K : ℝ) := by
    have hsplit : S_R = (∑ n ∈ Finset.range N₀, (truncRep A N n : ℝ) * r ^ (2 * n)) +
        (∑ n ∈ Finset.Ico N₀ M, (truncRep A N n : ℝ) * r ^ (2 * n)) := by
      dsimp only [S_R]
      rw [← Finset.sum_union]
      · congr 1; ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      · rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit]
    have hpart1 : (∑ n ∈ Finset.range N₀, (truncRep A N n : ℝ) * r ^ (2 * n)) ≤
        ((N₀ : ℝ) + 1) * (N₀ : ℝ) := by
      calc (∑ n ∈ Finset.range N₀, (truncRep A N n : ℝ) * r ^ (2 * n))
          ≤ ∑ _n ∈ Finset.range N₀, ((N₀ : ℝ) + 1) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' : n < N₀ := Finset.mem_range.mp hn
            have htr : (truncRep A N n : ℝ) ≤ (N₀ : ℝ) + 1 := by
              have h1 := truncRep_le_rep A N n
              have h2 := rep_le_succ A n
              exact_mod_cast (show truncRep A N n ≤ N₀ + 1 by omega)
            have hrp : r ^ (2 * n) ≤ 1 := pow_le_one₀ hr0 hr2.le
            exact le_trans (mul_le_mul_of_nonneg_right htr (pow_nonneg hr0 _))
              (mul_le_of_le_one_right (by positivity) hrp)
        _ = (N₀ : ℝ) * ((N₀ : ℝ) + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ((N₀ : ℝ) + 1) * (N₀ : ℝ) := by ring
    have hpart2 : (∑ n ∈ Finset.Ico N₀ M, (truncRep A N n : ℝ) * r ^ (2 * n)) ≤
        (2 * (b : ℝ) + 1) * (K : ℝ) := by
      calc (∑ n ∈ Finset.Ico N₀ M, (truncRep A N n : ℝ) * r ^ (2 * n))
          ≤ ∑ n ∈ Finset.Ico N₀ M, (2 * (b : ℝ) + 1) * r ^ (2 * n) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' : N₀ ≤ n := (Finset.mem_Ico.mp hn).1
            have htr : (truncRep A N n : ℝ) ≤ 2 * (b : ℝ) + 1 := by
              have h1 := truncRep_le_rep A N n
              have h2 : rep A n ≤ 2 * b + 1 := hhi n hn'
              exact_mod_cast (le_trans h1 h2)
            exact mul_le_mul_of_nonneg_right htr (pow_nonneg hr0 _)
        _ = (2 * (b : ℝ) + 1) * ∑ n ∈ Finset.Ico N₀ M, r ^ (2 * n) := by rw [← Finset.mul_sum]
        _ ≤ (2 * (b : ℝ) + 1) * ∑ n ∈ Finset.range M, r ^ (2 * n) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => pow_nonneg hr0 _)
            intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; exact hn.2
        _ ≤ (2 * (b : ℝ) + 1) * (K : ℝ) :=
            mul_le_mul_of_nonneg_left (le_trans (hgeom_all M) hK_inv_le) (by positivity)
    have hmulK : ((N₀ : ℝ) + 1) * (N₀ : ℝ) ≤ ((N₀ : ℝ) + 1) * (N₀ : ℝ) * (K : ℝ) :=
      le_mul_of_one_le_right (by positivity) hKge1
    linarith
  have hsqrtSR_le :
      Real.sqrt S_R ≤ (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ) := by
    have hcoef_ge1 : (1 : ℝ) ≤ ((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1) := by
      have h1 : (0 : ℝ) ≤ ((N₀ : ℝ) + 1) * (N₀ : ℝ) := by positivity
      have h2 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      linarith
    have hsq : S_R ≤ ((((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ)) ^ 2 := by
      have h1 : ((N₀ : ℝ) + 1) * (N₀ : ℝ) + (2 * (b : ℝ) + 1) ≤
          (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) ^ 2 := by
        have hle1 : ((N₀ : ℝ) + 1) * (N₀ : ℝ) + (2 * (b : ℝ) + 1) ≤
            ((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1) := by
          linarith [show (0 : ℝ) ≤ 2 * (b : ℝ) + 1 by positivity]
        exact le_trans hle1 (le_self_pow₀ hcoef_ge1 (by norm_num))
      calc S_R ≤ (((N₀ : ℝ) + 1) * (N₀ : ℝ) + (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ) ^ 2 := by
              rw [← hKsq]; exact hSR_le
        _ ≤ (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) ^ 2 * (2 ^ (2 * B) : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = _ := by ring
    calc Real.sqrt S_R
        ≤ Real.sqrt (((((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_sq (by positivity)
  -- Upper bound on S_D and sqrt S_D
  have hSD_le : S_D ≤ ((N₀ : ℝ) * C0 + 2 * C1) * (K : ℝ) := by
    have hsplit : S_D = (∑ n ∈ Finset.range N₀, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)) +
        (∑ n ∈ Finset.Ico N₀ M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)) := by
      dsimp only [S_D]
      rw [← Finset.sum_union]
      · congr 1; ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
      · rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit]
    have hpart1 : (∑ n ∈ Finset.range N₀, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)) ≤
        (N₀ : ℝ) * C0 := by
      calc (∑ n ∈ Finset.range N₀, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n))
          ≤ ∑ _n ∈ Finset.range N₀, C0 := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' : n < N₀ := Finset.mem_range.mp hn
            have htr : (truncRep A N n : ℝ) ≤ (N₀ : ℝ) + 1 := by
              have h1 := truncRep_le_rep A N n
              have h2 := rep_le_succ A n
              exact_mod_cast (show truncRep A N n ≤ N₀ + 1 by omega)
            have hsqC : ((truncRep A N n : ℝ) - c) ^ 2 ≤ C0 := by
              rw [hC0_def]; exact hsub_sq_le (by positivity) htr
            have hrp : r ^ (2 * n) ≤ 1 := pow_le_one₀ hr0 hr2.le
            exact le_trans (mul_le_mul_of_nonneg_right hsqC (pow_nonneg hr0 _))
              (mul_le_of_le_one_right hC0_nn hrp)
        _ = (N₀ : ℝ) * C0 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hpart2 : (∑ n ∈ Finset.Ico N₀ M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n)) ≤
        C1 * (K : ℝ) := by
      calc (∑ n ∈ Finset.Ico N₀ M, ((truncRep A N n : ℝ) - c) ^ 2 * r ^ (2 * n))
          ≤ ∑ n ∈ Finset.Ico N₀ M, C1 * r ^ (2 * n) := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hn' : N₀ ≤ n := (Finset.mem_Ico.mp hn).1
            have htr : (truncRep A N n : ℝ) ≤ 2 * (b : ℝ) + 1 := by
              have h1 := truncRep_le_rep A N n
              have h2 : rep A n ≤ 2 * b + 1 := hhi n hn'
              exact_mod_cast (le_trans h1 h2)
            have hsqC : ((truncRep A N n : ℝ) - c) ^ 2 ≤ C1 := by
              have h := hsub_sq_le (by positivity) htr
              rw [hC1_def]; linarith
            exact mul_le_mul_of_nonneg_right hsqC (pow_nonneg hr0 _)
        _ = C1 * ∑ n ∈ Finset.Ico N₀ M, r ^ (2 * n) := by rw [← Finset.mul_sum]
        _ ≤ C1 * ∑ n ∈ Finset.range M, r ^ (2 * n) := by
            apply mul_le_mul_of_nonneg_left _ hC1_pos.le
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => pow_nonneg hr0 _)
            intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; exact hn.2
        _ ≤ C1 * (K : ℝ) :=
            mul_le_mul_of_nonneg_left (le_trans (hgeom_all M) hK_inv_le) hC1_pos.le
    have hmulK : (N₀ : ℝ) * C0 ≤ (N₀ : ℝ) * C0 * (K : ℝ) :=
      le_mul_of_one_le_right (by positivity) hKge1
    have hC1K : 0 ≤ C1 * (K : ℝ) := by positivity
    linarith
  have hsqrtSD_le : Real.sqrt S_D ≤ (((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ) := by
    have hcoef_ge1 : (1 : ℝ) ≤ ((N₀ : ℝ) * C0 + 2 * C1) + 1 := by
      have : (0 : ℝ) ≤ (N₀ : ℝ) * C0 + 2 * C1 := by positivity
      linarith
    have hsq : S_D ≤ ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) ^ 2 := by
      have h1 : (N₀ : ℝ) * C0 + 2 * C1 ≤ (((N₀ : ℝ) * C0 + 2 * C1) + 1) ^ 2 :=
        le_trans (by linarith) (le_self_pow₀ hcoef_ge1 (by norm_num))
      calc S_D ≤ ((N₀ : ℝ) * C0 + 2 * C1) * (2 ^ (2 * B) : ℝ) ^ 2 := by
              rw [← hKsq]; exact hSD_le
        _ ≤ (((N₀ : ℝ) * C0 + 2 * C1) + 1) ^ 2 * (2 ^ (2 * B) : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = _ := by ring
    calc Real.sqrt S_D
        ≤ Real.sqrt (((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_sq (by positivity)
  -- Lower bound on S_R - S_D by splitting [0, M) into [0, N₀), [N₀, N], (N, M)
  have hSR_sub_SD :
      S_R - S_D = ∑ n ∈ Finset.range M,
        ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) := by
    dsimp only [S_R, S_D]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => by ring
  have hsplit3 :
      Finset.range M = (Finset.range N₀ ∪ Finset.Icc N₀ N) ∪ Finset.Ico (N + 1) M := by
    ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico]; omega
  have hdisjA : Disjoint (Finset.range N₀) (Finset.Icc N₀ N) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_range, Finset.mem_Icc] at h1 h2; omega
  have hdisjB : Disjoint (Finset.range N₀ ∪ Finset.Icc N₀ N) (Finset.Ico (N + 1) M) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Icc, Finset.mem_Ico] at h1 h2; omega
  rw [hsplit3, Finset.sum_union hdisjB, Finset.sum_union hdisjA] at hSR_sub_SD
  -- Piece 1: [0, N₀) ≥ - N₀ * C0
  have hpiece1 :
      -((N₀ : ℝ) * C0) ≤
        ∑ n ∈ Finset.range N₀,
          ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) := by
    have : -((N₀ : ℝ) * C0) = ∑ _n ∈ Finset.range N₀, (-C0) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [this]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn' : n < N₀ := Finset.mem_range.mp hn
    have htr : (truncRep A N n : ℝ) ≤ (N₀ : ℝ) + 1 := by
      have h1 := truncRep_le_rep A N n
      have h2 := rep_le_succ A n
      exact_mod_cast (show truncRep A N n ≤ N₀ + 1 by omega)
    have hsqC : ((truncRep A N n : ℝ) - c) ^ 2 ≤ C0 := by
      rw [hC0_def]; exact hsub_sq_le (by positivity) htr
    have hrp : r ^ (2 * n) ≤ 1 := pow_le_one₀ hr0 hr2.le
    have htr0 : (0 : ℝ) ≤ (truncRep A N n : ℝ) := by positivity
    have h1 : (-C0) * r ^ (2 * n) ≤
        ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 _)
    have h2 : -C0 ≤ (-C0) * r ^ (2 * n) := by
      have := mul_le_of_le_one_right hC0_nn hrp
      linarith
    exact le_trans h2 h1
  -- Piece 3: (N, M) ≥ - C1
  have hpiece3 :
      -C1 ≤
        ∑ n ∈ Finset.Ico (N + 1) M,
          ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) := by
    have htail_geom : (∑ n ∈ Finset.Ico (N + 1) M, r ^ (2 * n)) ≤ 1 := by
      have hshift :
          (∑ n ∈ Finset.Ico (N + 1) M, r ^ (2 * n)) =
            r ^ (2 * N) * ∑ j ∈ Finset.range N, r ^ (2 * (j + 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun n _ => n - (N + 1)) ?_ ?_ ?_ ?_
        · intro n hn; simp only [Finset.mem_Ico, Finset.mem_range] at hn ⊢; omega
        · intro n₁ hn₁ n₂ hn₂ h; simp only [Finset.mem_Ico] at hn₁ hn₂; omega
        · intro j hj; refine ⟨j + N + 1, ?_, by omega⟩
          simp only [Finset.mem_range, Finset.mem_Ico] at hj ⊢; omega
        · intro n hn
          simp only [Finset.mem_Ico] at hn
          rw [← pow_add]; congr 1; omega
      rw [hshift]
      have hle : (∑ j ∈ Finset.range N, r ^ (2 * (j + 1))) ≤ ∑ j ∈ Finset.range N, r ^ (2 * j) := by
        refine Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one hr0 hr2.le (by omega)
      have hsum_leK : (∑ j ∈ Finset.range N, r ^ (2 * j)) ≤ (K : ℝ) :=
        le_trans (hgeom_all N) hK_inv_le
      calc r ^ (2 * N) * ∑ j ∈ Finset.range N, r ^ (2 * (j + 1))
          ≤ r ^ (2 * N) * (K : ℝ) :=
            mul_le_mul_of_nonneg_left (le_trans hle hsum_leK) (pow_nonneg hr0 _)
        _ ≤ (1 / ((K : ℝ) * (K : ℝ))) * (K : ℝ) :=
            mul_le_mul_of_nonneg_right hr2N_le hKpos.le
        _ = 1 / (K : ℝ) := by field_simp [hKpos.ne']
        _ ≤ 1 := by rw [div_le_one hKpos]; exact hKge1
    calc -C1 = (-C1) * 1 := by ring
      _ ≤ (-C1) * (∑ n ∈ Finset.Ico (N + 1) M, r ^ (2 * n)) :=
          mul_le_mul_of_nonpos_left htail_geom (by linarith)
      _ = ∑ n ∈ Finset.Ico (N + 1) M, (-C1) * r ^ (2 * n) := by rw [Finset.mul_sum]
      _ ≤ ∑ n ∈ Finset.Ico (N + 1) M,
            ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' : N₀ ≤ n := by simp only [Finset.mem_Ico] at hn; omega
          have htr : (truncRep A N n : ℝ) ≤ 2 * (b : ℝ) + 1 := by
            have h1 := truncRep_le_rep A N n
            have h2 : rep A n ≤ 2 * b + 1 := hhi n hn'
            exact_mod_cast (le_trans h1 h2)
          have hsqC : ((truncRep A N n : ℝ) - c) ^ 2 ≤ C1 := by
            have h := hsub_sq_le (by positivity) htr
            rw [hC1_def]; linarith
          have htr0 : (0 : ℝ) ≤ (truncRep A N n : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 _)
  -- Piece 2: [N₀, N] ≥ (3/4) * ∑_{n ∈ [N₀, N]} r^(2n) - (C1 + 1) * sqrt(S_R)
  have hpiece2 :
      (3 : ℝ) / 4 * (∑ n ∈ Finset.Icc N₀ N, r ^ (2 * n)) - (C1 + 1) * Real.sqrt S_R ≤
        ∑ n ∈ Finset.Icc N₀ N,
          ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) := by
    have hterm_ge : ∀ n ∈ Finset.Icc N₀ N,
        (3 : ℝ) / 4 * r ^ (2 * n) -
          (if rep A n % 2 = 1 then (C1 + 1) * r ^ (2 * n) else 0) ≤
        ((truncRep A N n : ℝ) - ((truncRep A N n : ℝ) - c) ^ 2) * r ^ (2 * n) := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      rw [truncRep_eq_rep_of_le A hn.2]
      by_cases hodd : rep A n % 2 = 1
      · rw [if_pos hodd]
        have htr : (rep A n : ℝ) ≤ 2 * (b : ℝ) + 1 := by exact_mod_cast hhi n hn.1
        have hsqC : ((rep A n : ℝ) - c) ^ 2 ≤ C1 := by
          have h := hsub_sq_le (by positivity) htr
          rw [hC1_def]; linarith
        have htr0 : (0 : ℝ) ≤ (rep A n : ℝ) := by positivity
        have hcoeff : (3 : ℝ) / 4 - (C1 + 1) ≤ (rep A n : ℝ) - ((rep A n : ℝ) - c) ^ 2 := by
          linarith
        have := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr0 (2 * n))
        linarith
      · rw [if_neg hodd, sub_zero]
        have heven : rep A n % 2 = 0 := by omega
        have hgap := heven_gap (rep A n) heven (hlo n hn.1) (hhi n hn.1)
        exact mul_le_mul_of_nonneg_right hgap (pow_nonneg hr0 _)
    have hodd_bound :
        (∑ n ∈ Finset.Icc N₀ N, if rep A n % 2 = 1 then r ^ (2 * n) else 0) ≤ Real.sqrt S_R := by
      rw [← Finset.sum_filter]
      have hsub :
          ((Finset.Icc N₀ N).filter (fun n => rep A n % 2 = 1)) ⊆
            ((Finset.range (N + 1)).filter (fun m => m ∈ A)).image (fun m => 2 * m) := by
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hn ⊢
        rcases rep_odd_imp_half_mem hn.2 with ⟨x, hxA, hnx⟩
        exact ⟨x, ⟨by omega, hxA⟩, hnx.symm⟩
      have h1 :
          (∑ n ∈ (Finset.Icc N₀ N).filter (fun n => rep A n % 2 = 1), r ^ (2 * n)) ≤
            ∑ n ∈ ((Finset.range (N + 1)).filter (fun x => x ∈ A)).image (fun x => 2 * x),
              r ^ (2 * n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hr0 _)
      have h2 :
          (∑ n ∈ ((Finset.range (N + 1)).filter (fun x => x ∈ A)).image (fun x => 2 * x),
              r ^ (2 * n)) =
            ∑ x ∈ (Finset.range (N + 1)).filter (fun x => x ∈ A), r ^ (2 * (2 * x)) := by
        rw [Finset.sum_image]
        intro x₁ _ x₂ _ h
        dsimp only at h
        omega
      have h3 :
          (∑ x ∈ (Finset.range (N + 1)).filter (fun x => x ∈ A), r ^ (2 * (2 * x))) ≤
            ∑ x ∈ Finset.range (N + 1), (if x ∈ A then (1 : ℝ) else 0) * r ^ (2 * x) := by
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hx : x ∈ A
        · simp only [if_pos hx, one_mul]
          exact pow_le_pow_of_le_one hr0 hr2.le (by omega)
        · simp [hx]
      have hF2_eq :
          (∑ x ∈ Finset.range (N + 1), (if x ∈ A then (1 : ℝ) else 0) * r ^ (2 * x)) =
            Real.sqrt S_R := by
        have hnn : 0 ≤ ∑ x ∈ Finset.range (N + 1), (if x ∈ A then (1 : ℝ) else 0) * r ^ (2 * x) :=
          Finset.sum_nonneg fun x _ => by
            by_cases hx : x ∈ A
            · simp only [if_pos hx, one_mul]; exact pow_nonneg hr0 _
            · simp [hx]
        rw [← Real.sqrt_sq hnn, trunc_poly_sq_real A N r]
        dsimp only [S_R]; rw [hM_eq]
      linarith
    have hsum_step := Finset.sum_le_sum hterm_ge
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum_step
    have hpull :
        (∑ n ∈ Finset.Icc N₀ N, if rep A n % 2 = 1 then (C1 + 1) * r ^ (2 * n) else 0) =
          (C1 + 1) * ∑ n ∈ Finset.Icc N₀ N, if rep A n % 2 = 1 then r ^ (2 * n) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> ring
    rw [hpull] at hsum_step
    have hmul_odd :
        (C1 + 1) * (∑ n ∈ Finset.Icc N₀ N, if rep A n % 2 = 1 then r ^ (2 * n) else 0) ≤
          (C1 + 1) * Real.sqrt S_R :=
      mul_le_mul_of_nonneg_left hodd_bound (by linarith)
    linarith
  -- Lower bound on ∑_{n ∈ [N₀, N]} r^(2n) ≥ K / 8
  have hmain_geom : (K : ℝ) / 8 ≤ ∑ n ∈ Finset.Icc N₀ N, r ^ (2 * n) := by
    have hsum_eq :
        (∑ n ∈ Finset.Icc N₀ N, r ^ (2 * n)) =
          (r ^ (2 * N₀) - r ^ (2 * (N + 1))) / (1 - r ^ 2) := by
      have hdiff :
          (∑ n ∈ Finset.Icc N₀ N, r ^ (2 * n)) + (∑ n ∈ Finset.range N₀, r ^ (2 * n)) =
            ∑ n ∈ Finset.range (N + 1), r ^ (2 * n) := by
        rw [← Finset.sum_union]
        · congr 1; ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_range]; omega
        · rw [Finset.disjoint_left]; intro n h1 h2
          simp only [Finset.mem_Icc, Finset.mem_range] at h1 h2; omega
      have hgf : ∀ L : ℕ, (∑ n ∈ Finset.range L, r ^ (2 * n)) = (1 - r ^ (2 * L)) / (1 - r ^ 2) := by
        intro L
        have hrew : ∑ n ∈ Finset.range L, r ^ (2 * n) = ∑ n ∈ Finset.range L, (r ^ 2) ^ n := by
          refine Finset.sum_congr rfl fun n _ => ?_; rw [pow_mul]
        rw [hrew, geom_sum_eq (by linarith [h1mr2_pos] : r ^ 2 ≠ 1), ← pow_mul]
        field_simp [show r ^ 2 - 1 ≠ 0 by linarith, h1mr2_pos.ne']; ring
      have h1 := hgf (N + 1)
      have h2 := hgf N₀
      have : (1 - r ^ (2 * (N + 1))) / (1 - r ^ 2) - (1 - r ^ (2 * N₀)) / (1 - r ^ 2) =
          (r ^ (2 * N₀) - r ^ (2 * (N + 1))) / (1 - r ^ 2) := by ring
      linarith
    rw [hsum_eq]
    have hr2N1 : r ^ (2 * (N + 1)) ≤ r ^ (2 * N) := pow_le_pow_of_le_one hr0 hr2.le (by omega)
    have hnum : (1 : ℝ) / 4 ≤ r ^ (2 * N₀) - r ^ (2 * (N + 1)) := by linarith
    calc (K : ℝ) / 8 = ((1 : ℝ) / 4) * ((K : ℝ) / 2) := by ring
      _ ≤ ((1 : ℝ) / 4) * (1 / (1 - r ^ 2)) := mul_le_mul_of_nonneg_left hK_half_le (by norm_num)
      _ = ((1 : ℝ) / 4) / (1 - r ^ 2) := by ring
      _ ≤ (r ^ (2 * N₀) - r ^ (2 * (N + 1))) / (1 - r ^ 2) :=
          div_le_div_of_nonneg_right hnum h1mr2_pos.le
  -- Combine lower and upper bounds on S_R - S_D to contradict hB_main!
  have hRHS_bound :
      E_P ^ 2 + 2 * E_P * Real.sqrt S_D ≤
        (c * (2 + 16 * (B : ℝ) + 2)) ^ 2 +
          2 * (c * (2 + 16 * (B : ℝ) + 2)) *
            ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) := by
    have h1 : E_P ^ 2 ≤ (c * (2 + 16 * (B : ℝ) + 2)) ^ 2 :=
      pow_le_pow_left₀ hEP_nn hEP_le 2
    have h2 : 2 * E_P * Real.sqrt S_D ≤
        2 * (c * (2 + 16 * (B : ℝ) + 2)) *
          ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) :=
      mul_le_mul (by linarith) hsqrtSD_le (Real.sqrt_nonneg _) (by positivity)
    linarith
  have hLB_total :
      (3 : ℝ) / 32 * (2 ^ (4 * B) : ℝ) -
        ((N₀ : ℝ) * C0 + C1 +
          (C1 + 1) * (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ)) ≤
      S_R - S_D := by
    rw [hSR_sub_SD]
    have h34 : (3 : ℝ) / 32 * (2 ^ (4 * B) : ℝ) ≤ (3 : ℝ) / 4 * (∑ n ∈ Finset.Icc N₀ N, r ^ (2 * n)) := by
      rw [← hK4B]; linarith
    have hsr_mul :
        (C1 + 1) * Real.sqrt S_R ≤
          (C1 + 1) * ((((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrtSR_le (by linarith)
    linarith
  linarith

/-- **Theorem 1 (General Quantitative Representation Oscillation Theorem):**
For any subset `A ⊆ ℕ` and any integers `1 ≤ a ≤ b`, if the ordered representation function
`r_A(n) = |{(x, y) ∈ [0, n]² : x ∈ A ∧ y ∈ A ∧ x + y = n}|` satisfies
`2 * a - 1 ≤ r_A(n) ≤ 2 * b + 1` for all sufficiently large `n`, then
`(b - a) ^ 2 ≥ a + b`. -/
theorem ppl050_oscillation_bound (A : Set ℕ) (a b N₀ : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hlo : ∀ n ≥ N₀, 2 * a - 1 ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card)
    (hhi : ∀ n ≥ N₀,
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ 2 * b + 1) :
    a + b ≤ (b - a) ^ 2 := by
  by_contra hlt
  push Not at hlt
  let c : ℝ := (a : ℝ) + (b : ℝ) - 1 / 2
  have hc_pos : (0 : ℝ) ≤ c := by
    dsimp only [c]
    have : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  have heven_gap : ∀ k : ℕ, k % 2 = 0 → 2 * a - 1 ≤ k → k ≤ 2 * b + 1 →
      (3 : ℝ) / 4 ≤ (k : ℝ) - ((k : ℝ) - c) ^ 2 := by
    intro k hk_even hk_lo hk_hi
    have hk_lo' : (2 * a : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 * a ≤ k by omega)
    have hk_hi' : (k : ℝ) ≤ (2 * b : ℝ) := by exact_mod_cast (show k ≤ 2 * b by omega)
    have hgapN : (b - a) ^ 2 + 1 ≤ a + b := by omega
    have hgapR : ((b - a : ℕ) : ℝ) ^ 2 + 1 ≤ (a : ℝ) + (b : ℝ) := by exact_mod_cast hgapN
    have hba : ((b - a : ℕ) : ℝ) = (b : ℝ) - (a : ℝ) := Nat.cast_sub hab
    rw [hba] at hgapR
    have hprod : 0 ≤ ((k : ℝ) - 2 * (a : ℝ)) * (2 * (b : ℝ) - (k : ℝ)) := by nlinarith
    have hid : (k : ℝ) - ((k : ℝ) - c) ^ 2 =
        ((k : ℝ) - 2 * (a : ℝ)) * (2 * (b : ℝ) - (k : ℝ)) +
          ((a : ℝ) + (b : ℝ) - ((b : ℝ) - (a : ℝ)) ^ 2) - 1 / 4 := by
      dsimp only [c]; ring
    linarith
  let C0 : ℝ := ((N₀ : ℝ) + 1 + c) ^ 2
  let C1 : ℝ := (2 * (b : ℝ) + 1 + c) ^ 2 + 1
  obtain ⟨B, hB1, hB_N0, hB_scale⟩ := exists_scale_B N₀
    (A0 := (N₀ : ℝ) * C0 + C1)
    (A1 := (C1 + 1) * (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)))
    (A2 := 20 * c)
    (A3 := 40 * c * (((N₀ : ℝ) * C0 + 2 * C1) + 1))
    (by positivity) (by positivity) (by positivity) (by positivity)
  have hB_main :
      (N₀ : ℝ) * C0 + C1 +
        (C1 + 1) * (((N₀ : ℝ) + 1) * (N₀ : ℝ) + 2 * (2 * (b : ℝ) + 1)) * (2 ^ (2 * B) : ℝ) +
        (c * (2 + 16 * (B : ℝ) + 2)) ^ 2 +
        2 * (c * (2 + 16 * (B : ℝ) + 2)) *
          ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) <
      (3 : ℝ) / 32 * (2 ^ (4 * B) : ℝ) := by
    have hBge1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show 1 ≤ B by omega)
    have h16 : c * (2 + 16 * (B : ℝ) + 2) ≤ 20 * c * (B : ℝ) := by nlinarith
    have h16_nn : 0 ≤ c * (2 + 16 * (B : ℝ) + 2) := by positivity
    have hsq : (c * (2 + 16 * (B : ℝ) + 2)) ^ 2 ≤ (20 * c * (B : ℝ)) ^ 2 :=
      pow_le_pow_left₀ h16_nn h16 2
    have hlin :
        2 * (c * (2 + 16 * (B : ℝ) + 2)) *
          ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) ≤
        40 * c * (((N₀ : ℝ) * C0 + 2 * C1) + 1) * (B : ℝ) * (2 ^ (2 * B) : ℝ) := by
      have hfac : 0 ≤ 2 * ((((N₀ : ℝ) * C0 + 2 * C1) + 1) * (2 ^ (2 * B) : ℝ)) := by positivity
      have hmul := mul_le_mul_of_nonneg_right h16 hfac
      linarith
    linarith
  let K : ℕ := 2 ^ (4 * B)
  let m : ℕ := 8 * B
  let N : ℕ := 2 ^ m
  let M : ℕ := 2 * N + 1
  let r : ℝ := 1 - 1 / (K : ℝ)
  have hK4 : 4 ≤ K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hN_eq : N = K ^ 2 := by
    dsimp only [N, m, K]; rw [← pow_mul]; congr 1; omega
  have hKsq : (K : ℝ) = (2 ^ (2 * B) : ℝ) ^ 2 := by
    dsimp only [K]; push_cast; rw [← pow_mul]; congr 1; omega
  have hK4B : (K : ℝ) = (2 ^ (4 * B) : ℝ) := by dsimp only [K]; push_cast; rfl
  have hN0_le_N : N₀ ≤ N := by
    have : K ≤ K ^ 2 := Nat.le_self_pow (by norm_num) K
    omega
  have hr1 : (1 : ℝ) / 4 ≤ r := by
    dsimp only [r]
    have : (1 : ℝ) / (K : ℝ) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hK4)
    linarith
  have hr2 : r < 1 := by
    dsimp only [r]
    have : (0 : ℝ) < 1 / (K : ℝ) := by positivity
    linarith
  have hr0 : 0 ≤ r := by linarith
  have h1mr : 1 - r = 1 / (K : ℝ) := by dsimp only [r]; ring
  have h1mr2_lo : 1 / (K : ℝ) ≤ 1 - r ^ 2 := by
    have : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [this, h1mr]
    exact le_mul_of_one_le_right (by positivity) (by linarith)
  have h1mr2_hi : 1 - r ^ 2 ≤ 2 / (K : ℝ) := by
    have hfac : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    rw [hfac, h1mr]
    have hmul : (1 / (K : ℝ)) * (1 + r) ≤ (1 / (K : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [show (1 / (K : ℝ)) * 2 = 2 / (K : ℝ) by ring]
  have h1mr2_pos : 0 < 1 - r ^ 2 := by linarith [show (0 : ℝ) < 1 / (K : ℝ) by positivity]
  have hK_inv_le : 1 / (1 - r ^ 2) ≤ (K : ℝ) := by
    rw [div_le_iff₀ h1mr2_pos]
    have : 1 = (1 / (K : ℝ)) * (K : ℝ) := by field_simp [hKpos.ne']
    have hmul := mul_le_mul_of_nonneg_right h1mr2_lo hKpos.le
    linarith
  have hK_half_le : (K : ℝ) / 2 ≤ 1 / (1 - r ^ 2) := by
    rw [le_div_iff₀ h1mr2_pos]
    have : (K : ℝ) / 2 * (2 / (K : ℝ)) = 1 := by field_simp [hKpos.ne']
    have hmul := mul_le_mul_of_nonneg_left h1mr2_hi (by positivity : (0 : ℝ) ≤ (K : ℝ) / 2)
    linarith
  have hr2N_le : r ^ (2 * N) ≤ 1 / ((K : ℝ) * (K : ℝ)) := by
    have hhalf := one_sub_inv_pow_le_half (show 2 ≤ K by omega)
    have hrpow : r ^ (2 * N) = (r ^ K) ^ (2 * K) := by
      rw [← pow_mul, hN_eq]; congr 1; ring
    rw [hrpow]
    have hstep1 : (r ^ K) ^ (2 * K) ≤ ((1 : ℝ) / 2) ^ (2 * K) :=
      pow_le_pow_left₀ (pow_nonneg hr0 K) hhalf (2 * K)
    have hstep2 : ((1 : ℝ) / 2) ^ (2 * K) ≤ 1 / ((K : ℝ) * (K : ℝ)) := by
      have hK_le_2K : (K : ℝ) ≤ (2 ^ K : ℝ) := by
        have := add_one_le_two_pow K
        exact_mod_cast (show K ≤ 2 ^ K by omega)
      have hsq : (K : ℝ) * (K : ℝ) ≤ (2 : ℝ) ^ (2 * K) := by
        calc (K : ℝ) * (K : ℝ)
            ≤ (2 ^ K : ℝ) * (2 ^ K : ℝ) := mul_le_mul hK_le_2K hK_le_2K hKpos.le (by positivity)
          _ = (2 : ℝ) ^ (2 * K) := by rw [← pow_add]; congr 1; omega
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) hsq
    exact le_trans hstep1 hstep2
  have hr2N_le_quarter : r ^ (2 * N) ≤ (1 : ℝ) / 4 := by
    have hKsq4 : (4 : ℝ) ≤ (K : ℝ) * (K : ℝ) := by
      have : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK4
      nlinarith
    exact le_trans hr2N_le (one_div_le_one_div_of_le (by norm_num) hKsq4)
  have hr2N0_ge : (1 : ℝ) / 2 ≤ r ^ (2 * N₀) := by
    have hbern : 1 + (2 * N₀ : ℕ) * (- (1 / (K : ℝ))) ≤ (1 + (- (1 / (K : ℝ)))) ^ (2 * N₀) :=
      one_add_mul_le_pow (by linarith [hr1]) (2 * N₀)
    have hsub : (1 : ℝ) + -(1 / (K : ℝ)) = r := by dsimp only [r]; ring
    rw [hsub] at hbern
    have h2N0_le : ((2 * N₀ : ℕ) : ℝ) / (K : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 2), one_mul]
      exact_mod_cast (show 2 * N₀ * 2 ≤ K by omega)
    have : ((2 * N₀ : ℕ) : ℝ) * -(1 / (K : ℝ)) = -(((2 * N₀ : ℕ) : ℝ) / (K : ℝ)) := by ring
    linarith
  let E_P : ℝ := c * (2 / ((M : ℝ) * (1 - r)) + 2 * ((m : ℝ) + 1))
  have hEP_nn : 0 ≤ E_P := by
    dsimp only [E_P]
    rw [h1mr]
    positivity
  have hEP_le : E_P ≤ c * (2 + 16 * (B : ℝ) + 2) := by
    dsimp only [E_P]
    apply mul_le_mul_of_nonneg_left _ hc_pos
    have hM1mr : 1 ≤ (M : ℝ) * (1 - r) := by
      rw [h1mr]
      have : (K : ℝ) ≤ (M : ℝ) := by
        have : K ≤ K ^ 2 := Nat.le_self_pow (by norm_num) K
        exact_mod_cast (show K ≤ 2 * N + 1 by omega)
      rw [mul_one_div, one_le_div hKpos]
      exact this
    have hdiv2 : 2 / ((M : ℝ) * (1 - r)) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hm_eq : (m : ℝ) = 8 * (B : ℝ) := by dsimp only [m]; push_cast; ring
    linarith
  have hmaster := discrete_parseval_master A m hr1 hr2 hc_pos
  dsimp only at hmaster
  exact osc_bounds_contradiction A a b N₀ B K N M r c C0 C1 E_P
    hlo hhi hc_pos rfl rfl heven_gap hK4 hKsq hK4B hN0_le_N rfl
    hr0 hr2 h1mr2_pos hK_inv_le hK_half_le hr2N_le hr2N_le_quarter hr2N0_ge
    hEP_nn hEP_le hmaster hB_main

/-! ### Section 4: Grekos–Haddad–Helou–Pihko (`limsup ≥ 6`), Higher-Multiplicity & Dirac (1951) -/

/-- **Theorem 2a (Grekos–Haddad–Helou–Pihko, 2003):**
For every asymptotic additive basis `A ⊆ ℕ` of order 2 (`(A + A)ᶜ.Finite`), the ordered
representation function `r_A(n)` is at least `6` for infinitely many `n`. -/
theorem ppl050_limsup_ge_six (A : Set ℕ) (h : (A + A)ᶜ.Finite) :
    ∀ N : ℕ, ∃ n ≥ N, 6 ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card := by
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨N₁, hlt6⟩
  -- Since (A + A)ᶜ is finite, it has an upper bound M₀
  have hbdd : ∃ M₀ : ℕ, ∀ n ≥ M₀, n ∈ A + A := by
    rcases h.bddAbove with ⟨M, hM⟩
    refine ⟨M + 1, fun n hn => ?_⟩
    by_contra hnotmem
    have : n ≤ M := hM hnotmem
    omega
  rcases hbdd with ⟨M₀, hcov⟩
  let N₀ := max N₁ M₀
  have hosc := ppl050_oscillation_bound A 1 2 N₀ (by norm_num) (by norm_num)
    (fun n hn => by
      have h1 : 1 ≤ rep A n := rep_pos_of_mem_add (hcov n (le_trans (le_max_right _ _) hn))
      simpa [rep] using h1)
    (fun n hn => by
      have hlt := hlt6 n (le_trans (le_max_left _ _) hn)
      omega)
  norm_num at hosc

/-- **Theorem 2b (Grekos–Haddad–Helou–Pihko, 2003 — `ℕ∞` `Filter.limsup` form matching
`FormalConjectures/ErdosProblems/28.lean`):**
For every `A : Set ℕ` with `(A + A)ᶜ.Finite`,
`6 ≤ Filter.limsup (fun n => (r_A(n) : ℕ∞)) Filter.atTop`. -/
theorem ppl050_limsup_ge_six_enat (A : Set ℕ) (h : (A + A)ᶜ.Finite) :
    (6 : ℕ∞) ≤ Filter.limsup (fun n : ℕ =>
      (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞)) Filter.atTop := by
  refine Filter.le_limsup_of_frequently_le ?_
  rw [Filter.frequently_atTop]
  intro N
  rcases ppl050_limsup_ge_six A h N with ⟨n, hn, h6⟩
  exact ⟨n, hn, by exact_mod_cast h6⟩

/-- **Theorem 2c (Higher-Multiplicity Corollary: `liminf ≥ 3 ⇒ limsup ≥ 10`):** -/
theorem ppl050_limsup_ge_ten_of_ge_three (A : Set ℕ) (N₀ : ℕ)
    (hlo : ∀ n ≥ N₀, 3 ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card) :
    ∀ N : ℕ, ∃ n ≥ N, 10 ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card := by
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨N₁, hlt⟩
  have hosc := ppl050_oscillation_bound A 2 4 (max N₀ N₁) (by norm_num) (by norm_num)
    (fun n hn => hlo n (le_trans (le_max_left _ _) hn))
    (fun n hn => by have := hlt n (le_trans (le_max_right _ _) hn); omega)
  norm_num at hosc

/-- **Theorem 2d (Higher-Multiplicity Corollary: `liminf ≥ 5 ⇒ limsup ≥ 12`):** -/
theorem ppl050_limsup_ge_twelve_of_ge_five (A : Set ℕ) (N₀ : ℕ)
    (hlo : ∀ n ≥ N₀, 5 ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card) :
    ∀ N : ℕ, ∃ n ≥ N, 12 ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card := by
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨N₁, hlt⟩
  have hosc := ppl050_oscillation_bound A 3 5 (max N₀ N₁) (by norm_num) (by norm_num)
    (fun n hn => hlo n (le_trans (le_max_left _ _) hn))
    (fun n hn => by have := hlt n (le_trans (le_max_right _ _) hn); omega)
  norm_num at hosc

/-- **Theorem 3 (Dirac, 1951):**
For every infinite subset `A ⊆ ℕ`, the ordered representation function `r_A(n)` is never eventually
constant. -/
theorem ppl050_dirac_not_eventually_const (A : Set ℕ) (hinf : A.Infinite) :
    ¬ ∃ c N₀ : ℕ, ∀ n ≥ N₀,
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card = c := by
  rintro ⟨c, N₀, hconst⟩
  by_cases hc0 : c = 0
  · subst hc0
    -- Pick a ∈ A with a ≥ N₀; then 2*a ≥ N₀ has r_A(2*a) ≥ 1, contradiction.
    obtain ⟨a, haA, ha_ge⟩ : ∃ a ∈ A, N₀ ≤ a := by
      by_contra hnone
      push Not at hnone
      have hsub : A ⊆ Set.Iio N₀ := fun x hx => hnone x hx
      exact hinf ((Set.finite_Iio N₀).subset hsub)
    have hpos : 1 ≤ rep A (2 * a) := rep_pos_of_mem_add ⟨a, haA, a, haA, by ring⟩
    have hzero : rep A (2 * a) = 0 := hconst (2 * a) (by omega)
    omega
  · by_cases hodd : c % 2 = 1
    · -- For odd n = 2*N₀ + 1 ≥ N₀, rep A n cannot be odd!
      have hval : rep A (2 * N₀ + 1) = c := hconst (2 * N₀ + 1) (by omega)
      have hodd_n : rep A (2 * N₀ + 1) % 2 = 1 := by omega
      rcases rep_odd_imp_half_mem hodd_n with ⟨m, _, hm⟩
      omega
    · -- c is even and c ≥ 2: write c = 2 * a with a ≥ 1 and apply ppl050_oscillation_bound
      let a := c / 2
      have ha1 : 1 ≤ a := by omega
      have h2a : 2 * a = c := by omega
      have hosc := ppl050_oscillation_bound A a a N₀ ha1 le_rfl
        (fun n hn => by have := hconst n hn; omega)
        (fun n hn => by have := hconst n hn; omega)
      simp at hosc
      omega

/-! ### Section 5: Universal Finite Abelian Group Ruzsa Lower Bound (`|G| ≥ 46 ⇒ R(G) ≥ 6`) -/

/-- **Theorem 4 (Universal Finite Abelian Group Ruzsa Lower Bound):**
For every finite abelian group `G` of order `|G| ≥ 46` and every additive basis `A ⊆ G`
(`A + A = G`), there exists `g ∈ G` with at least `6` ordered representations `a + b = g`
(`a, b ∈ A`). This generalizes Sándor–Yang's cyclic Ruzsa bound `R_m ≥ 6` to all finite abelian
groups via pure additive energy `E(A) = ∑ r_A(g)^2 = ∑ d_A(k)^2` and integer convexity. -/
theorem ppl050_finite_abelian_ruzsa_ge_six {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (hcard : 46 ≤ Fintype.card G) (A : Finset G)
    (hbasis : ∀ g : G, ∃ a ∈ A, ∃ b ∈ A, a + b = g) :
    ∃ g : G, 6 ≤ ((A ×ˢ A).filter (fun p => p.1 + p.2 = g)).card := by
  by_contra hlt6
  push Not at hlt6
  let m : ℕ := Fintype.card G
  let s : ℕ := A.card
  let r : G → ℕ := fun g => ((A ×ˢ A).filter (fun p => p.1 + p.2 = g)).card
  let d : G → ℕ := fun k => ((A ×ˢ A).filter (fun p => p.1 - p.2 = k)).card
  -- Basic sum identities: ∑ r g = s^2, ∑ d k = s^2, d 0 = s
  have hsum_r : ∑ g : G, r g = s ^ 2 := by
    have hpart : ∑ g : G, r g = (A ×ˢ A).card := by
      simp only [r, Finset.card_eq_sum_ones]
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : G × G => p.1 + p.2)
        (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)]
    rw [hpart, Finset.card_product, sq]
  have hsum_d : ∑ k : G, d k = s ^ 2 := by
    have hpart : ∑ k : G, d k = (A ×ˢ A).card := by
      simp only [d, Finset.card_eq_sum_ones]
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : G × G => p.1 - p.2)
        (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)]
    rw [hpart, Finset.card_product, sq]
  have hd0 : d 0 = s := by
    dsimp only [d, s]
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      exact hp.1.1
    · intro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ h
      simp only [Finset.mem_filter, Finset.mem_product, sub_eq_zero] at hp₁ hp₂
      dsimp at h
      exact Prod.ext h (by rw [← hp₁.2, ← hp₂.2, h])
    · intro a ha
      exact ⟨(a, a), by simp [ha], rfl⟩
  -- Additive energy identity: ∑ (r g)^2 = ∑ (d k)^2
  have henergy : ∑ g : G, (r g) ^ 2 = ∑ k : G, (d k) ^ 2 := by
    let Q := ((A ×ˢ A) ×ˢ (A ×ˢ A)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)
    have hQ_r : Q.card = ∑ g : G, (r g) ^ 2 := by
      have h1 : Q.card = ∑ g : G, (Q.filter (fun q => q.1.1 + q.1.2 = g)).card := by
        simp only [Finset.card_eq_sum_ones]
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun q : (G × G) × (G × G) => q.1.1 + q.1.2)
          (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)]
      rw [h1]
      refine Finset.sum_congr rfl fun g _ => ?_
      have heq : Q.filter (fun q => q.1.1 + q.1.2 = g) =
          ((A ×ˢ A).filter (fun p => p.1 + p.2 = g)) ×ˢ
            ((A ×ˢ A).filter (fun p => p.1 + p.2 = g)) := by
        ext ⟨p₁, p₂⟩
        simp only [Q, Finset.mem_filter, Finset.mem_product]
        constructor
        · rintro ⟨⟨⟨h1, h2⟩, heq12⟩, h1g⟩
          exact ⟨⟨h1, h1g⟩, ⟨h2, by rw [← heq12, h1g]⟩⟩
        · rintro ⟨⟨h1, h1g⟩, ⟨h2, h2g⟩⟩
          exact ⟨⟨⟨h1, h2⟩, by rw [h1g, h2g]⟩, h1g⟩
      rw [heq, Finset.card_product, sq]
    have hQ_d : Q.card = ∑ k : G, (d k) ^ 2 := by
      have h1 : Q.card = ∑ k : G, (Q.filter (fun q => q.1.1 - q.2.1 = k)).card := by
        simp only [Finset.card_eq_sum_ones]
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun q : (G × G) × (G × G) => q.1.1 - q.2.1)
          (t := (Finset.univ : Finset G)) (fun _ _ => Finset.mem_univ _)]
      rw [h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hbij : (Q.filter (fun q => q.1.1 - q.2.1 = k)).card =
          (((A ×ˢ A).filter (fun p => p.1 - p.2 = k)) ×ˢ
            ((A ×ˢ A).filter (fun p => p.1 - p.2 = k))).card := by
        refine Finset.card_bij (fun q _ => ((q.1.1, q.2.1), (q.2.2, q.1.2))) ?_ ?_ ?_
        · intro ⟨⟨a, b⟩, ⟨c, e⟩⟩ hq
          simp only [Q, Finset.mem_filter, Finset.mem_product] at hq ⊢
          refine ⟨⟨⟨hq.1.1.1.1, hq.1.1.2.1⟩, hq.2⟩, ⟨⟨hq.1.1.2.2, hq.1.1.1.2⟩, ?_⟩⟩
          have hab : a + b = c + e := hq.1.2
          have hac : a - c = k := hq.2
          rw [← hac, sub_eq_sub_iff_add_eq_add]
          simpa [add_comm] using hab.symm
        · intro ⟨⟨a₁, b₁⟩, ⟨c₁, e₁⟩⟩ _ ⟨⟨a₂, b₂⟩, ⟨c₂, e₂⟩⟩ _ h
          simp only [Prod.mk.injEq] at h
          rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩; rfl
        · intro ⟨⟨a, c⟩, ⟨e, b⟩⟩ hq
          simp only [Finset.mem_product, Finset.mem_filter] at hq
          refine ⟨((a, b), (c, e)), ?_, rfl⟩
          simp only [Q, Finset.mem_filter, Finset.mem_product]
          refine ⟨⟨⟨⟨hq.1.1.1, hq.2.1.2⟩, ⟨hq.1.1.2, hq.2.1.1⟩⟩, ?_⟩, hq.1.2⟩
          have hsub : a - c = e - b := by rw [hq.1.2, hq.2.2]
          have := sub_eq_sub_iff_add_eq_add.mp hsub
          simpa [add_comm] using this
      rw [hbij, Finset.card_product, sq]
    rw [← hQ_r, hQ_d]
  -- Parity bound: at most s elements g ∈ G have odd r g
  let Godd := Finset.univ.filter (fun g : G => r g % 2 = 1)
  have hodd_card : Godd.card ≤ s := by
    have hsub : Godd ⊆ A.image (fun a => a + a) := by
      intro g hg
      simp only [Godd, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hg ⊢
      -- Involution Prod.swap on S = (A ×ˢ A).filter (p.1 + p.2 = g) pairs off p.1 ≠ p.2
      let S := (A ×ˢ A).filter (fun p => p.1 + p.2 = g)
      let Sdiag := S.filter (fun p => p.1 = p.2)
      let Soff := S.filter (fun p => p.1 ≠ p.2)
      have hSoff_even : Even Soff.card := by
        have hfix : ∀ p ∈ Soff, Prod.swap p ∈ Soff ∧ Prod.swap p ≠ p ∧ Prod.swap (Prod.swap p) = p := by
          intro ⟨a, b⟩ hp
          simp only [Soff, S, Finset.mem_filter, Finset.mem_product] at hp ⊢
          refine ⟨⟨⟨⟨hp.1.1.2, hp.1.1.1⟩, by rw [add_comm]; exact hp.1.2⟩, Ne.symm hp.2⟩, ?_, rfl⟩
          intro hsw; simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hsw; exact hp.2 hsw.2
        have hgen : ∀ (T : Finset (G × G)),
            (∀ p ∈ T, Prod.swap p ∈ T ∧ Prod.swap p ≠ p) → Even T.card := by
          intro T
          induction T using Finset.strongInduction with
          | H T ih =>
            intro hT
            by_cases hE : T = ∅
            · subst hE; exact ⟨0, rfl⟩
            · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hE
              have hsp : Prod.swap p ∈ T := (hT p hp).1
              have hne : Prod.swap p ≠ p := (hT p hp).2
              let T' := (T.erase p).erase (Prod.swap p)
              have hT'_ssub : T' ⊂ T := by
                refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
                · exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
                · intro heq
                  have : p ∈ T' := heq ▸ hp
                  exact (Finset.mem_erase.mp (Finset.erase_subset _ _ this)).1 rfl
              have hT'_inv : ∀ q ∈ T', Prod.swap q ∈ T' ∧ Prod.swap q ≠ q := by
                intro q hq
                have hq1 : q ≠ Prod.swap p := (Finset.mem_erase.mp hq).1
                have hq2 : q ≠ p := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
                have hqT : q ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
                refine ⟨?_, (hT q hqT).2⟩
                refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, (hT q hqT).1⟩⟩
                · intro h; exact hq2 (by simpa using congrArg Prod.swap h)
                · intro h; exact hq1 (by simpa using congrArg Prod.swap h)
              have hcardT : T.card = T'.card + 2 := by
                have hsp' : Prod.swap p ∈ T.erase p := Finset.mem_erase.mpr ⟨hne, hsp⟩
                have h1 := Finset.card_erase_add_one hsp'
                have h2 := Finset.card_erase_add_one hp
                dsimp only [T']
                omega
              rcases ih T' hT'_ssub hT'_inv with ⟨k, hk⟩
              exact ⟨k + 1, by omega⟩
        exact hgen Soff (fun p hp => ⟨(hfix p hp).1, (hfix p hp).2.1⟩)
      have hS_part : S.card = Sdiag.card + Soff.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext p; simp only [Sdiag, Soff, Finset.mem_union, Finset.mem_filter]; tauto
        · rw [Finset.disjoint_filter]; intro _ _ h1 h2; exact h2 h1
      have hSdiag_pos : 0 < Sdiag.card := by
        rcases hSoff_even with ⟨k, hk⟩
        have hS : S.card = r g := rfl
        omega
      rcases Finset.card_pos.mp hSdiag_pos with ⟨⟨a, b⟩, hab⟩
      simp only [Sdiag, S, Finset.mem_filter, Finset.mem_product] at hab
      exact ⟨a, hab.1.1.1, by rw [← hab.2] at hab; exact hab.1.2⟩
    calc Godd.card ≤ (A.image (fun a => a + a)).card := Finset.card_le_card hsub
      _ ≤ A.card := Finset.card_image_le
  -- Cast all inequalities to ℤ for clean arithmetic!
  have hr_bounds : ∀ g : G, 1 ≤ r g ∧ r g ≤ 5 := by
    intro g
    refine ⟨?_, by have := hlt6 g; dsimp only [r]; omega⟩
    rcases hbasis g with ⟨a, ha, b, hb, hab⟩
    dsimp only [r]
    rw [Finset.one_le_card]
    exact ⟨(a, b), by simp [ha, hb, hab]⟩
  -- 1. Size bounds on s^2: 2m - s ≤ s^2 ≤ 4m + s
  have hs2_lo : (2 : ℤ) * m - s ≤ (s : ℤ) ^ 2 := by
    have hpt : ∀ g : G, (2 : ℤ) - (if r g % 2 = 1 then 1 else 0) ≤ (r g : ℤ) := by
      intro g
      have ⟨h1, _⟩ := hr_bounds g
      split_ifs <;> omega
    have hsum := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hpt g
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    have hsrZ : ∑ g : G, (r g : ℤ) = (s : ℤ) ^ 2 := by exact_mod_cast hsum_r
    have hoddZ : (Godd.card : ℤ) ≤ (s : ℤ) := by exact_mod_cast hodd_card
    dsimp only [Godd, m] at hoddZ hsum ⊢
    linarith
  have hs2_hi : (s : ℤ) ^ 2 ≤ (4 : ℤ) * m + s := by
    have hpt : ∀ g : G, (r g : ℤ) ≤ (4 : ℤ) + (if r g % 2 = 1 then 1 else 0) := by
      intro g
      have ⟨_, h5⟩ := hr_bounds g
      split_ifs <;> omega
    have hsum := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hpt g
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
    have hsrZ : ∑ g : G, (r g : ℤ) = (s : ℤ) ^ 2 := by exact_mod_cast hsum_r
    have hoddZ : (Godd.card : ℤ) ≤ (s : ℤ) := by exact_mod_cast hodd_card
    dsimp only [Godd, m] at hoddZ hsum ⊢
    linarith
  -- 2. Upper bound on E(A) = ∑ (r g)^2 ≤ 6 s^2 - 8 m + 3 s
  have hE_ub : (∑ g : G, (r g : ℤ) ^ 2) ≤ 6 * (s : ℤ) ^ 2 - 8 * m + 3 * s := by
    have hpt : ∀ g : G,
        (r g : ℤ) ^ 2 ≤ 6 * (r g : ℤ) - 8 + (if r g % 2 = 1 then 3 else 0) := by
      intro g
      have ⟨h1, h5⟩ := hr_bounds g
      split_ifs with ho
      · have : r g = 1 ∨ r g = 3 ∨ r g = 5 := by omega
        rcases this with h | h | h <;> simp [h]
      · have : r g = 2 ∨ r g = 4 := by omega
        rcases this with h | h <;> simp [h]
    have hsum := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hpt g
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    have hsrZ : ∑ g : G, (r g : ℤ) = (s : ℤ) ^ 2 := by exact_mod_cast hsum_r
    have hoddZ : (Godd.card : ℤ) ≤ (s : ℤ) := by exact_mod_cast hodd_card
    dsimp only [Godd, m] at hoddZ hsum ⊢
    linarith
  -- 3. Lower bounds on E(A) = s^2 + ∑_{k ≠ 0} (d k)^2 via integer convexity (d - t)(d - t - 1) ≥ 0
  have hE_lb : ∀ t : ℤ,
      (s : ℤ) ^ 2 + (2 * t + 1) * ((s : ℤ) ^ 2 - s) - t * (t + 1) * (m - 1) ≤
        ∑ k : G, (d k : ℤ) ^ 2 := by
    intro t
    have hpt : ∀ k : G, (2 * t + 1) * (d k : ℤ) - t * (t + 1) ≤ (d k : ℤ) ^ 2 := by
      intro k
      have hsq : 0 ≤ ((d k : ℤ) - t) * ((d k : ℤ) - (t + 1)) := by
        rcases le_or_gt (d k : ℤ) t with hle | hgt
        · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
        · exact mul_nonneg (by omega) (by omega)
      linarith
    have hsplit : ∑ k : G, (d k : ℤ) ^ 2 = (d 0 : ℤ) ^ 2 + ∑ k ∈ Finset.univ.erase 0, (d k : ℤ) ^ 2 :=
      (Finset.add_sum_erase Finset.univ (fun k => (d k : ℤ) ^ 2) (Finset.mem_univ 0)).symm
    have hsum_d_nz : ∑ k ∈ Finset.univ.erase 0, (d k : ℤ) = (s : ℤ) ^ 2 - s := by
      have hsp := Finset.add_sum_erase Finset.univ (fun k => (d k : ℤ)) (Finset.mem_univ 0)
      have hsdZ : ∑ k : G, (d k : ℤ) = (s : ℤ) ^ 2 := by exact_mod_cast hsum_d
      have hd0Z : (d 0 : ℤ) = s := by exact_mod_cast hd0
      linarith
    have hcard_nz : ((Finset.univ.erase (0 : G)).card : ℤ) = (m : ℤ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ,
        Nat.cast_sub (show 1 ≤ Fintype.card G by omega)]
      simp [m]
    have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ.erase 0) => hpt k
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      hsum_d_nz, hcard_nz] at hsum
    have hd0Z : (d 0 : ℤ) = s := by exact_mod_cast hd0
    rw [hsplit, hd0Z]
    linarith
  -- Apply t = 2 and t = 3!
  have hEZ : ∑ g : G, (r g : ℤ) ^ 2 = ∑ k : G, (d k : ℤ) ^ 2 := by exact_mod_cast henergy
  have hlb2 := hE_lb 2
  have hlb3 := hE_lb 3
  -- From t = 2: 6 s^2 - 5 s - 6(m - 1) ≤ 6 s^2 - 8 m + 3 s  ⇒  2m + 6 ≤ 8s  ⇒  m + 3 ≤ 4s
  -- From t = 3: 8 s^2 - 7 s - 12(m - 1) ≤ 6 s^2 - 8 m + 3 s  ⇒  2 s^2 ≤ 4m + 10s - 12
  -- Combining m + 3 ≤ 4s with 2 s^2 ≤ 4m + 10s - 12 forces m ≤ 45!
  have hm46 : (46 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hcard
  have hs_nn : (0 : ℤ) ≤ (s : ℤ) := by positivity
  -- Check: 8*(2 s^2 - 10s + 12) = 16 s^2 - 80 s + 96 ≤ 32 m, while 4s ≥ m + 3
  -- implies (m + 3)^2 - 20(m + 3) + 96 ≤ 32 m, i.e. m^2 - 46m + 45 ≤ 0, i.e. (m - 1)(m - 45) ≤ 0!
  have h1 : (m : ℤ) + 3 ≤ 4 * (s : ℤ) := by linarith
  have h2 : 2 * (s : ℤ) ^ 2 ≤ 4 * (m : ℤ) + 10 * (s : ℤ) - 12 := by linarith
  have h3 : ((m : ℤ) - 1) * ((m : ℤ) - 45) ≤ 0 := by nlinarith
  nlinarith

/-! ### Section 6: Exact `ℤ` vs. `ℕ` Counterexample Barrier (Sidon Basis of `ℤ`) -/

/-- Explicit surjection `ℕ → ℤ`: `0, -1, 1, -2, 2, ...`. -/
private def enumZ (k : ℕ) : ℤ :=
  if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) else -((k / 2 + 1 : ℕ) : ℤ)

private lemma enumZ_surjective (z : ℤ) : ∃ k : ℕ, enumZ k = z := by
  by_cases hz : 0 ≤ z
  · refine ⟨2 * z.toNat, ?_⟩
    unfold enumZ
    have hmod : (2 * z.toNat) % 2 = 0 := by omega
    rw [if_pos hmod]
    have hdiv : 2 * z.toNat / 2 = z.toNat := by omega
    rw [hdiv]
    exact Int.toNat_of_nonneg hz
  · push Not at hz
    let m : ℕ := (-z).toNat - 1
    refine ⟨2 * m + 1, ?_⟩
    unfold enumZ
    have hmod : (2 * m + 1) % 2 ≠ 0 := by omega
    rw [if_neg hmod]
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hdiv]
    have hpos : 1 ≤ (-z).toNat := by omega
    have hm1 : m + 1 = (-z).toNat := by omega
    rw [hm1]
    have := Int.toNat_of_nonneg (show 0 ≤ -z by omega)
    linarith

private def maxAbs (S : Finset ℤ) : ℤ :=
  ((S.sup (fun a => a.natAbs) : ℕ) : ℤ)

private lemma abs_le_maxAbs {S : Finset ℤ} {a : ℤ} (ha : a ∈ S) : |a| ≤ maxAbs S := by
  have hle : a.natAbs ≤ S.sup (fun x => x.natAbs) := Finset.le_sup (f := fun x : ℤ => x.natAbs) ha
  have hleZ : (a.natAbs : ℤ) ≤ ((S.sup (fun x => x.natAbs) : ℕ) : ℤ) := Int.ofNat_le.mpr hle
  rw [Int.natCast_natAbs] at hleZ
  exact hleZ

private lemma maxAbs_nonneg (S : Finset ℤ) : 0 ≤ maxAbs S := by
  unfold maxAbs
  exact Int.natCast_nonneg _

/-- Greedy Sidon-basis step over `ℤ`. -/
private noncomputable def sidonStep : ℕ → Finset ℤ
  | 0 => ∅
  | k + 1 =>
    let A := sidonStep k
    let t := enumZ k
    if ∃ a ∈ A, ∃ b ∈ A, a + b = t then A
    else
      let x : ℤ := 5 * maxAbs A + 3 * |t| + 10
      let y : ℤ := t - x
      insert x (insert y A)

private lemma sidonStep_mono (k : ℕ) : sidonStep k ⊆ sidonStep (k + 1) := by
  dsimp only [sidonStep]
  split_ifs
  · exact Finset.Subset.refl _
  · exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

private lemma sidonStep_mono_le {j k : ℕ} (h : j ≤ k) : sidonStep j ⊆ sidonStep k := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (sidonStep_mono _)

private lemma sidonStep_covers (k : ℕ) :
    ∃ a ∈ sidonStep (k + 1), ∃ b ∈ sidonStep (k + 1), a + b = enumZ k := by
  dsimp only [sidonStep]
  split_ifs with hcov
  · exact hcov
  · set x : ℤ := 5 * maxAbs (sidonStep k) + 3 * |enumZ k| + 10
    set y : ℤ := enumZ k - x
    refine ⟨x, Finset.mem_insert_self _ _, y,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by ring⟩

private lemma sidonStep_isSidon (k : ℕ) :
    ∀ a ∈ sidonStep k, ∀ b ∈ sidonStep k, ∀ c ∈ sidonStep k, ∀ d ∈ sidonStep k,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  induction k with
  | zero =>
    intro a ha; simp [sidonStep] at ha
  | succ k ih =>
    dsimp only [sidonStep]
    split_ifs with hcov
    · exact ih
    · set A := sidonStep k
      set t := enumZ k
      set M := maxAbs A
      set T := |t|
      set x : ℤ := 5 * M + 3 * T + 10
      set y : ℤ := t - x
      have hM : 0 ≤ M := maxAbs_nonneg A
      have hT : 0 ≤ T := abs_nonneg t
      have ht_lo : -T ≤ t := neg_abs_le t
      have ht_hi : t ≤ T := le_abs_self t
      have hmem_bound : ∀ u ∈ A, -M ≤ u ∧ u ≤ M := fun u hu => abs_le.mp (abs_le_maxAbs hu)
      intro a ha b hb c hc d hd heq
      -- Case-split each of a, b, c, d ∈ {x} ∪ {y} ∪ A: the five sum intervals
      -- {2y} < y + A < (A + A) ∪ {t} < x + A < {2x} are strictly separated!
      simp only [Finset.mem_insert] at ha hb hc hd
      rcases ha with rfl | rfl | haA <;>
      rcases hb with rfl | rfl | hbA <;>
      rcases hc with rfl | rfl | hcA <;>
      rcases hd with rfl | rfl | hdA
      -- All 81 cases resolved by interval separation (`omega` + `hcov` + `ih`):
      all_goals
        try exact Or.inl ⟨rfl, rfl⟩
        try exact Or.inr ⟨rfl, rfl⟩
        try (exfalso; exact hcov ⟨_, hcA, _, hdA, by omega⟩)
        try (exfalso; exact hcov ⟨_, haA, _, hbA, by omega⟩)
        try (exact ih _ haA _ hbA _ hcA _ hdA heq)
        try (
          try have ⟨_, _⟩ := hmem_bound _ haA
          try have ⟨_, _⟩ := hmem_bound _ hbA
          try have ⟨_, _⟩ := hmem_bound _ hcA
          try have ⟨_, _⟩ := hmem_bound _ hdA
          omega)

/-- **Theorem 5 (Exact `ℤ` vs. `ℕ` Counterexample Barrier — Nathanson):**
There exists a subset `A ⊆ ℤ` such that:
1. Every integer `z : ℤ` is representable as `z = a + b` with `a, b ∈ A` (`A + A = ℤ`), AND
2. Every integer has a **unique unordered representation** (equivalently, `A` is a Sidon basis of
   `ℤ`, so `1 ≤ r_A(z) ≤ 2` for every `z : ℤ`).
Thus the Erdős–Turán Conjecture fails completely over `ℤ` and genuinely requires one-sidedness
`A ⊆ ℕ`. -/
theorem ppl050_int_sidon_basis_barrier :
    ∃ A : Set ℤ,
      (∀ z : ℤ, ∃ a ∈ A, ∃ b ∈ A, a + b = z) ∧
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
        a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) := by
  let A : Set ℤ := {z : ℤ | ∃ k : ℕ, z ∈ sidonStep k}
  refine ⟨A, ?_, ?_⟩
  · intro z
    rcases enumZ_surjective z with ⟨k, hk⟩
    rcases sidonStep_covers k with ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ⟨k + 1, ha⟩, b, ⟨k + 1, hb⟩, hab.trans hk⟩
  · rintro a ⟨k₁, ha⟩ b ⟨k₂, hb⟩ c ⟨k₃, hc⟩ d ⟨k₄, hd⟩ heq
    let K := max (max k₁ k₂) (max k₃ k₄)
    have haK : a ∈ sidonStep K :=
      sidonStep_mono_le (le_trans (le_max_left _ _) (le_max_left _ _)) ha
    have hbK : b ∈ sidonStep K :=
      sidonStep_mono_le (le_trans (le_max_right _ _) (le_max_left _ _)) hb
    have hcK : c ∈ sidonStep K :=
      sidonStep_mono_le (le_trans (le_max_left _ _) (le_max_right _ _)) hc
    have hdK : d ∈ sidonStep K :=
      sidonStep_mono_le (le_trans (le_max_right _ _) (le_max_right _ _)) hd
    exact sidonStep_isSidon K a haK b hbK c hcK d hdK heq

/-! ### Section 7: Explicit Thin Binary/Cantor-Digit Basis & Exact ↔ Asymptotic Equivalence -/

/-- Spread binary bits of `n` into even bit positions (base-4 digits in `{0, 1}`):
`evenBits n = (n % 2) + 4 * evenBits (n / 2)`. -/
private def evenBits : ℕ → ℕ
  | 0 => 0
  | n + 1 => ((n + 1) % 2) + 4 * evenBits ((n + 1) / 2)
termination_by n => n

private lemma evenBits_eq (n : ℕ) : evenBits n = n % 2 + 4 * evenBits (n / 2) := by
  cases n with
  | zero => simp [evenBits]
  | succ n => rw [evenBits]

private lemma evenBits_lt_pow_four (k : ℕ) : ∀ n < 2 ^ k, evenBits n < 4 ^ k := by
  induction k with
  | zero =>
    intro n hn
    have : n = 0 := by omega
    subst this; simp [evenBits]
  | succ k ih =>
    intro n hn
    rw [evenBits_eq, pow_succ]
    have hdiv : n / 2 < 2 ^ k := by rw [pow_succ] at hn; omega
    have hrec := ih (n / 2) hdiv
    omega

private lemma evenBits_pos : ∀ n, 1 ≤ n → 1 ≤ evenBits n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [evenBits_eq]
    by_cases h0 : n / 2 = 0
    · have : n = 1 := by omega
      subst this; simp [evenBits]
    · have hrec := ih (n / 2) (Nat.div_lt_self (by omega) (by norm_num)) (by omega)
      omega

private lemma evenBits_ge_pow_four (k : ℕ) : ∀ n, 2 ^ k ≤ n → 4 ^ k ≤ evenBits n := by
  induction k with
  | zero =>
    intro n hn
    simpa using evenBits_pos n hn
  | succ k ih =>
    intro n hn
    rw [evenBits_eq, pow_succ]
    have hdiv : 2 ^ k ≤ n / 2 := by rw [pow_succ] at hn; omega
    have hrec := ih (n / 2) hdiv
    omega

private lemma evenBits_injective : Function.Injective evenBits := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b hab
    rw [evenBits_eq a, evenBits_eq b] at hab
    have hmod : a % 2 = b % 2 := by omega
    have hdiv_eq : evenBits (a / 2) = evenBits (b / 2) := by omega
    by_cases ha0 : a = 0
    · subst ha0
      have hb_mod : b % 2 = 0 := by omega
      have hb_div : evenBits (b / 2) = 0 := by simpa [evenBits] using hdiv_eq.symm
      by_contra hb0
      have hge := evenBits_ge_pow_four 0 (b / 2) (by omega)
      omega
    · have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by norm_num)
      have hdiv := ih (a / 2) hlt hdiv_eq
      omega

private lemma exists_even_add_two_even (m : ℕ) :
    ∃ u v : ℕ, evenBits u + 2 * evenBits v = m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m = 0
    · subst hm; exact ⟨0, 0, by simp [evenBits]⟩
    · have hlt : m / 4 < m := Nat.div_lt_self (by omega) (by norm_num)
      rcases ih (m / 4) hlt with ⟨u', v', huv'⟩
      let u := m % 2 + 2 * u'
      let v := (m / 2) % 2 + 2 * v'
      refine ⟨u, v, ?_⟩
      rw [evenBits_eq u, evenBits_eq v]
      have hu1 : u % 2 = m % 2 := by dsimp only [u]; omega
      have hu2 : u / 2 = u' := by dsimp only [u]; omega
      have hv1 : v % 2 = (m / 2) % 2 := by dsimp only [v]; omega
      have hv2 : v / 2 = v' := by dsimp only [v]; omega
      rw [hu1, hu2, hv1, hv2]
      omega

private lemma evenBits_complement_sum (m : ℕ) :
    ∀ u < 2 ^ m, evenBits u + evenBits (2 ^ m - 1 - u) = evenBits (2 ^ m - 1) := by
  induction m with
  | zero =>
    intro u hu
    have : u = 0 := by omega
    subst this; simp [evenBits]
  | succ m ih =>
    intro u hu
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have h1m : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    rw [evenBits_eq u, evenBits_eq (2 ^ (m + 1) - 1 - u), evenBits_eq (2 ^ (m + 1) - 1)]
    have hmod_sum : u % 2 + (2 ^ (m + 1) - 1 - u) % 2 = 1 := by omega
    have hmod_top : (2 ^ (m + 1) - 1) % 2 = 1 := by omega
    have hdiv_top : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by omega
    have hdiv_comp : (2 ^ (m + 1) - 1 - u) / 2 = 2 ^ m - 1 - u / 2 := by omega
    have hrec := ih (u / 2) (by omega)
    rw [hdiv_top, hdiv_comp]
    omega

/-- **Theorem 6 (Explicit Thin Cantor/Binary Order-2 Basis with Unbounded Representations):**
There exists an explicit order-2 basis `A ⊆ ℕ` (`A + A = ℕ`) of optimal `O(√N)` density
(`|A ∩ [0, 4^k)| < 2 · 2^k` for every `k ≥ 1`) whose ordered representation function is unbounded
(`∀ M, ∃ n ≥ M, M ≤ r_A(n)`). -/
theorem ppl050_cantor_binary_basis :
    ∃ A : Set ℕ,
      (∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      (∀ k : ℕ, 1 ≤ k → ((Finset.range (4 ^ k)).filter (fun n => n ∈ A)).card < 2 * 2 ^ k) ∧
      (∀ M : ℕ, ∃ n ≥ M, M ≤
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card) := by
  let A : Set ℕ := Set.range evenBits ∪ Set.range (fun n => 2 * evenBits n)
  refine ⟨A, ?_, ?_, ?_⟩
  · -- Exact basis: A + A = ℕ
    intro n
    rcases exists_even_add_two_even n with ⟨u, v, huv⟩
    exact ⟨evenBits u, Or.inl ⟨u, rfl⟩, 2 * evenBits v, Or.inr ⟨v, rfl⟩, huv⟩
  · -- Thin density: |A ∩ [0, 4^k)| < 2 * 2^k for all k ≥ 1
    intro k hk
    let S0 := (Finset.range (2 ^ k)).image evenBits
    let S1 := (Finset.range (2 ^ k)).image (fun n => 2 * evenBits n)
    have hsub : (Finset.range (4 ^ k)).filter (fun n => n ∈ A) ⊆ S0 ∪ S1 := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, S0, S1,
        Finset.mem_image] at hx ⊢
      rcases hx.2 with ⟨u, rfl⟩ | ⟨v, rfl⟩
      · left
        refine ⟨u, ?_, rfl⟩
        by_contra hge; push Not at hge
        have := evenBits_ge_pow_four k u hge
        omega
      · right
        refine ⟨v, ?_, rfl⟩
        by_contra hge; push Not at hge
        have := evenBits_ge_pow_four k v hge
        dsimp only at hx
        omega
    have h0_inter : (0 : ℕ) ∈ S0 ∩ S1 := by
      have hpos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
      simp only [Finset.mem_inter, S0, S1, Finset.mem_image, Finset.mem_range]
      exact ⟨⟨0, hpos, by simp [evenBits]⟩, ⟨0, hpos, by simp [evenBits]⟩⟩
    have hinter_pos : 1 ≤ (S0 ∩ S1).card := Finset.one_le_card.mpr ⟨0, h0_inter⟩
    have hunion := Finset.card_union_add_card_inter S0 S1
    have hS0 : S0.card ≤ 2 ^ k := Finset.card_image_le.trans (by simp)
    have hS1 : S1.card ≤ 2 ^ k := Finset.card_image_le.trans (by simp)
    have hle := Finset.card_le_card hsub
    have hlt' : ((Finset.range (4 ^ k)).filter (fun n => n ∈ A)).card < 2 * 2 ^ k := by omega
    convert hlt' using 1
    congr 1
    exact Finset.filter_congr_decidable _ _ _
  · -- Unbounded representations: at n = evenBits (2^m - 1), r_A(n) ≥ 2^m
    intro M
    let m := M + 1
    let n := evenBits (2 ^ m - 1)
    have h2m_ge : M ≤ 2 ^ m := by
      have := add_one_le_two_pow m
      omega
    have hn_ge : M ≤ n := by
      have hge := evenBits_ge_pow_four M (2 ^ m - 1) (by
        have h1 : 1 ≤ 2 ^ M := Nat.one_le_pow M 2 (by norm_num)
        dsimp only [m]; rw [pow_succ]; omega)
      have h4 : M ≤ 4 ^ M := by
        have := add_one_le_two_pow M
        have h24 : 2 ^ M ≤ 4 ^ M := Nat.pow_le_pow_left (by norm_num) M
        omega
      omega
    refine ⟨n, hn_ge, ?_⟩
    -- Map u ∈ range (2^m) to (evenBits u, evenBits (2^m - 1 - u))
    let f : ℕ → ℕ × ℕ := fun u => (evenBits u, evenBits (2 ^ m - 1 - u))
    have himg : (Finset.range (2 ^ m)).image f ⊆
        (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨u, hu, rfl⟩
      have hu' : u < 2 ^ m := Finset.mem_range.mp hu
      have hsum : evenBits u + evenBits (2 ^ m - 1 - u) = n := evenBits_complement_sum m u hu'
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, f]
      exact ⟨⟨by omega, by omega⟩, Or.inl ⟨u, rfl⟩, Or.inl ⟨2 ^ m - 1 - u, rfl⟩, hsum⟩
    have hinj : Set.InjOn f (Finset.range (2 ^ m) : Set ℕ) := by
      intro u₁ _ u₂ _ h
      exact evenBits_injective (congrArg Prod.fst h)
    have hcard : ((Finset.range (2 ^ m)).image f).card = 2 ^ m := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hle := Finset.card_le_card himg
    have hMle : M ≤ ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card := by omega
    convert hMle using 1
    congr 1
    exact Finset.filter_congr_decidable _ _ _

/-- **Theorem 7 (Exact vs. Asymptotic Basis Equivalence for Erdős Problem #28):**
The Erdős–Turán Conjecture for all asymptotic order-2 bases (`(A + A)ᶜ.Finite`) is equivalent
to the Erdős–Turán Conjecture for all exact order-2 bases (`A + A = Set.univ`). -/
theorem ppl050_asymptotic_iff_exact_basis :
    (∀ A : Set ℕ, (A + A)ᶜ.Finite →
      ∀ M : ℕ, ∃ n ≥ M, M ≤
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card) ↔
    (∀ A : Set ℕ, A + A = Set.univ →
      ∀ M : ℕ, ∃ n ≥ M, M ≤
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card) := by
  constructor
  · intro h A hex
    exact h A (by simp [hex])
  · intro h A hfin M
    -- Enlarge A by F = {0} ∪ (A + A)ᶜ (a finite set); then A' = A ∪ F satisfies A' + A' = Set.univ,
    -- and for every n, r_{A'}(n) ≤ r_A(n) + 2 * |F|.
    let F : Finset ℕ := insert 0 hfin.toFinset
    let A' : Set ℕ := A ∪ (F : Set ℕ)
    have h0A' : (0 : ℕ) ∈ A' := Or.inr (by simp [F])
    have hex : A' + A' = Set.univ := by
      ext n
      simp only [Set.mem_univ, iff_true]
      by_cases hn : n ∈ A + A
      · rcases Set.mem_add.mp hn with ⟨a, ha, b, hb, hab⟩
        exact ⟨a, Or.inl ha, b, Or.inl hb, hab⟩
      · have hnF : n ∈ F := Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hn)
        exact ⟨0, h0A', n, Or.inr hnF, zero_add n⟩
    rcases h A' hex (M + 2 * F.card) with ⟨n, hn, hrep'⟩
    refine ⟨n, by omega, ?_⟩
    -- Every pair (a, b) ∈ A' × A' with a + b = n lies in (A × A) ∪ (F × {n - a}) ∪ ({n - b} × F)
    let S := (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)
    let S' := (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A' ∧ p.2 ∈ A' ∧ p.1 + p.2 = n)
    let L := F.image (fun a => (a, n - a))
    let R := F.image (fun b => (n - b, b))
    have hsub : S' ⊆ (S ∪ L) ∪ R := by
      intro ⟨a, b⟩ hp
      simp only [S', S, L, R, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_union, Finset.mem_image] at hp ⊢
      rcases hp.2.1 with haA | haF
      · rcases hp.2.2.1 with hbA | hbF
        · exact Or.inl (Or.inl ⟨hp.1, haA, hbA, hp.2.2.2⟩)
        · exact Or.inr ⟨b, hbF, Prod.ext (by omega) rfl⟩
      · exact Or.inl (Or.inr ⟨a, haF, Prod.ext rfl (by omega)⟩)
    have hcard : S'.card ≤ S.card + F.card + F.card := by
      calc S'.card ≤ ((S ∪ L) ∪ R).card := Finset.card_le_card hsub
        _ ≤ (S ∪ L).card + R.card := Finset.card_union_le _ _
        _ ≤ (S.card + L.card) + R.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ (S.card + F.card) + F.card :=
            Nat.add_le_add (Nat.add_le_add_left Finset.card_image_le _) Finset.card_image_le
    have hrep'_eq : M + 2 * F.card ≤ S'.card := by convert hrep'
    have hgoal : M ≤ S.card := by omega
    convert hgoal

end PPL050
