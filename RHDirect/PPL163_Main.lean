/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# PPL 163 (Erdős Problem #40 — Generalized Erdős–Turán Conjecture)

## Honest Scope Statement
**Erdős Problem #40** (`erdosproblems.com/40`, `prizeproblems.org`, `$500`, **LIVE-VERIFIED OPEN**
as of 2026) asks:

> For what functions `g(N) → ∞` is it true that
> `|A ∩ {1, ..., N}| ≫ N^{1/2} / g(N)` implies `limsup_{n → ∞} (1_A * 1_A)(n) = ∞`?

This module makes **no claim** to resolve the open sub-polynomial frontier (`g(N) = N^{o(1)}`,
such as `g(N) = (log N)^c`) or the Erdős–Turán Conjecture (Erdős Problem #28). Instead, it
provides a **100% unconditional, kernel-verified, pure-Mathlib-signature formalization** of the
complete surrounding phase diagram and exact reductions:

1. **Exact Representation & `limsup = ∞` Equivalences (`Section 1`):**
   - `ppl163_rep_eq_filter_card`: exact equality between the ordered-pair convolution
     `#{(a, b) ∈ A × A : a + b = n}` and `#{a ≤ n : a ∈ A ∧ n - a ∈ A}`.
   - `ppl163_limsup_top_iff_unbounded`: exact equivalence between
     `Filter.limsup (fun n => (r_A(n) : ℕ∞)) Filter.atTop = ⊤`,
     `∀ M, ∃ n ≥ M, M ≤ r_A(n)`, and `¬ ∃ M, ∀ n, r_A(n) ≤ M`.
2. **Quantitative `B_2[h]` and Sidon Upper Bounds + Super-`√N` Density Regime (`Section 2`):**
   - `ppl163_b2h_card_le_sqrt_two_mul`: for every `A ⊆ ℕ` with `∀ n, r_A(n) ≤ h`,
     `|A ∩ {1, ..., N}| ≤ √(2 h N)` (and exact integer form `|A ∩ {1, ..., N}|^2 ≤ (2 N - 1) h`).
   - `ppl163_b2h_card_le_sqrt_90_div_47`: unconditional improvement over `√(2 h N)` for ALL `h`
     and ALL `N`: `|A ∩ {1, ..., N}| ≤ √((90 / 47) h N)`, proved elementarily via discrete
     Parseval on `2N`-th roots of unity and the exact identity `2 sin(πx) + cos(2πx) ≥ 1`.
   - `ppl163_sidon_card_le_lindstrom`: sharp Erdős–Turán (1941) / Lindström (1969) Sidon upper
     bound `|A ∩ {1, ..., N}| ≤ √N + N^{1/4} + 1` for every Sidon set `A ⊆ ℕ` and `N ≥ 1`.
   - `ppl163_super_sqrt_implies_limsup_top`: unconditional resolution of the super-`√N` regime
     (`g(N) → 0`): if `|A ∩ {1, ..., N}| / N^{1/2} → ∞`, then `limsup r_A(n) = ⊤`.
3. **Exact `#40 ⇒ #28` Reduction (`Section 3`):**
   - `ppl163_basis_counting_lower_bound`: every asymptotic additive basis `A ⊆ ℕ` of order 2
     (`(A + A)ᶜ.Finite`) satisfies `|A ∩ {1, ..., N}| ≥ (1/2) N^{1/2}` for all large `N`.
   - `ppl163_erdos40_implies_erdos28`, `ppl163_erdos40_tendsto_implies_erdos28`, and
     `ppl163_erdos40_const_one_implies_erdos28`: if ANY `g : ℕ → ℝ` with eventually `g(N) ≥ 1`
     (in particular any `g(N) → ∞`, or even constant `g(N) = 1`) satisfies the Erdős #40
     implication, then the full Erdős–Turán Conjecture (PPL 050 / Erdős #28) follows.
4. **Erdős–Rényi (1960) / Cilleruelo–Pliego `N^{g/(2g+1)}` Construction & Polynomial Refutation (`Section 4`):**
   - `ppl163_erdos_renyi_b2g_existence`: for every integer `g ≥ 1`, there exists `A ⊆ ℕ` with
     `∀ n, r_A(n) ≤ 4 g` and `∀ N ≥ 8192, (1 / 2048) N^{g / (2g + 1)} ≤ |A ∩ {1, ..., N}|`,
     constructed via a completely finitary, zero-measure-theory block-by-block averaging and
     alteration argument on dyadic-16 blocks `[16^j, 2 · 16^j)`.
   - `ppl163_erdos_renyi_poly_refutation` & `ppl163_poly_g_fails_erdos40`: for every `ε > 0`,
     there exists `A ⊆ ℕ` with bounded `r_A(n)` and `|A ∩ {1, ..., N}| ≫ N^{1/2 - ε}`,
     unconditionally refuting EVERY polynomial `g(N) = N^ε` (`ε > 0`) in Erdős #40.
5. **Threshold Monotonicity & Sub-Polynomial Frontier Barriers (`Section 5`):**
   - `ppl163_threshold_monotonicity`: downward closure of valid `g` under asymptotic domination.
   - `ppl163_valid_g_liminf_poly_zero` & `ppl163_valid_g_log_ratio_not_pos`: any valid `g` for
     Erdős #40 must satisfy `∃ᶠ N in atTop, g N < C * N^ε` and
     `∃ᶠ N in atTop, log (g N) / log N < ε` for every `ε, C > 0`, confining the open frontier
     strictly inside `g(N) = N^{o(1)}`.
   - `ppl163_polylog_subpolynomial`: for every `c > 0` and `ε > 0`, `(log N)^c / N^ε → 0`,
     certifying why Erdős's test family `g(N) = (log N)^c` lies strictly inside the surviving
     open sub-polynomial frontier.

Every public theorem signature uses **zero custom or private definitions** (100% native Mathlib).
-/

open scoped Pointwise BigOperators
open Classical

namespace PPL163

noncomputable section

/-! ## Section 1: Exact Representation Function & `limsup = ∞` Equivalences -/

/-- Exact identity between the ordered-pair representation count
`#{(a, b) ∈ A × A : a + b = n}` and the single-variable convolution count
`#{a ≤ n : a ∈ A ∧ n - a ∈ A}`. -/
theorem ppl163_rep_eq_filter_card (A : Set ℕ) (n : ℕ) :
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card =
    ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card := by
  symm
  refine Finset.card_bij (fun a _ => (a, n - a)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at ha ⊢
    exact ⟨⟨ha.1, by omega⟩, ha.2.1, ha.2.2, by omega⟩
  · intro a₁ _ a₂ _ h
    exact congrArg Prod.fst h
  · intro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hab
    refine ⟨a, ?_, Prod.ext rfl (by omega)⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hab.1.1, hab.2.1, by simpa [show n - a = b by omega] using hab.2.2.1⟩

private lemma rep_card_le_succ (A : Set ℕ) (n : ℕ) :
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ n + 1 := by
  rw [ppl163_rep_eq_filter_card]
  calc
    ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card
        ≤ (Finset.range (n + 1)).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.card_range (n + 1)

/-- Exact three-way equivalence for `limsup_{n → ∞} (1_A * 1_A)(n) = ∞`:
because `r_A(n) ≤ n + 1`, `limsup = ⊤` in `ℕ∞` is equivalent both to
`∀ M, ∃ n ≥ M, M ≤ r_A(n)` and to global unboundedness `¬ ∃ M, ∀ n, r_A(n) ≤ M`. -/
theorem ppl163_limsup_top_iff_unbounded (A : Set ℕ) :
    (Filter.limsup
      (fun n : ℕ =>
        (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
      Filter.atTop = ⊤ ↔
      ∀ M : ℕ, ∃ n ≥ M, M ≤
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card)
    ∧
    ((∀ M : ℕ, ∃ n ≥ M, M ≤
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card) ↔
      ¬ ∃ M : ℕ, ∀ n : ℕ,
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ M) := by
  let r : ℕ → ℕ := fun n =>
    ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card
  have h23 : (∀ M : ℕ, ∃ n ≥ M, M ≤ r n) ↔ ¬ ∃ M : ℕ, ∀ n : ℕ, r n ≤ M := by
    constructor
    · rintro h ⟨M, hM⟩
      rcases h (M + 1) with ⟨n, _, hn⟩
      have := hM n
      omega
    · intro h M
      by_contra hno
      push Not at hno
      apply h
      refine ⟨M, fun n => ?_⟩
      by_cases hn : M ≤ n
      · exact Nat.le_of_lt (hno n hn)
      · have hle : r n ≤ n + 1 := rep_card_le_succ A n
        omega
  have h12 : (Filter.limsup (fun n : ℕ => (r n : ℕ∞)) Filter.atTop = ⊤) ↔
      (∀ M : ℕ, ∃ n ≥ M, M ≤ r n) := by
    constructor
    · intro htop M
      rw [Filter.limsup_eq_iInf_iSup_of_nat] at htop
      have hge : (M : ℕ∞) < ⨅ n : ℕ, ⨆ i : ℕ, ⨆ (_ : i ≥ n), (r i : ℕ∞) := by
        rw [htop]
        exact WithTop.coe_lt_top M
      have hsup : (M : ℕ∞) < ⨆ i : ℕ, ⨆ (_ : i ≥ M), (r i : ℕ∞) :=
        lt_of_lt_of_le hge (iInf_le _ M)
      rw [lt_iSup_iff] at hsup
      rcases hsup with ⟨n, hsup⟩
      rw [lt_iSup_iff] at hsup
      rcases hsup with ⟨hn, hlt⟩
      exact ⟨n, hn, Nat.le_of_lt (by exact_mod_cast hlt)⟩
    · intro hunb
      rw [eq_top_iff, Filter.limsup_eq_iInf_iSup_of_nat]
      refine le_iInf fun N => ?_
      rw [← eq_top_iff]
      by_contra hne
      rcases WithTop.ne_top_iff_exists.mp hne with ⟨K, hK⟩
      rcases hunb (max N (K + 1)) with ⟨n, hn, hrn⟩
      have hle : (r n : ℕ∞) ≤ ⨆ i : ℕ, ⨆ (_ : i ≥ N), (r i : ℕ∞) :=
        le_iSup_of_le n (le_iSup_of_le (le_trans (le_max_left _ _) hn) le_rfl)
      rw [← hK] at hle
      have hleNat : r n ≤ K := Nat.cast_le.mp hle
      have : K + 1 ≤ r n := le_trans (le_max_right _ _) hrn
      omega
  exact ⟨h12, h23⟩

/-! ## Section 2: Quantitative `B_2[h]` and Sidon Upper Bounds & Super-`√N` Regime -/

private lemma card_sq_eq_sum_trunc_rep (S : Finset ℕ) (N : ℕ) (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ N) :
    S.card ^ 2 =
      ∑ n ∈ Finset.Icc 2 (2 * N),
        ((S ×ˢ S).filter (fun p => p.1 + p.2 = n)).card := by
  have hmaps : ∀ p ∈ S ×ˢ S, p.1 + p.2 ∈ Finset.Icc 2 (2 * N) := by
    intro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    have ha := hS a hp.1
    have hb := hS b hp.2
    rw [Finset.mem_Icc]
    omega
  rw [sq, ← Finset.card_product]
  exact Finset.card_eq_sum_card_fiberwise hmaps

private lemma trunc_rep_le_full_rep (A : Set ℕ) (S : Finset ℕ)
    (hSA : ∀ a ∈ S, a ∈ A) (n : ℕ) :
    ((S ×ˢ S).filter (fun p => p.1 + p.2 = n)).card ≤
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card := by
  apply Finset.card_le_card
  intro ⟨a, b⟩ hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  exact ⟨⟨by omega, by omega⟩, hSA a hp.1.1, hSA b hp.1.2, hp.2⟩

/-- **Elementary `B_2[h]` Upper Bound (`√(2 h N)`):**
For any `A ⊆ ℕ` whose ordered representation function satisfies `r_A(n) ≤ h` for all `n`,
`|A ∩ {1, ..., N}|^2 ≤ (2 N - 1) * h` and `|A ∩ {1, ..., N}| ≤ √(2 h N)` for every `N : ℕ`. -/
theorem ppl163_b2h_card_le_sqrt_two_mul (A : Set ℕ) (h : ℕ)
    (hrep : ∀ n : ℕ,
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ h)
    (N : ℕ) :
    ((Finset.Icc 1 N).filter (· ∈ A)).card ^ 2 ≤ (2 * N - 1) * h ∧
    (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤ Real.sqrt (2 * (h : ℝ) * (N : ℝ)) := by
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hS_bounds : ∀ a ∈ S, 1 ≤ a ∧ a ≤ N := by
    intro a ha
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
  have hSA : ∀ a ∈ S, a ∈ A := fun a ha => (Finset.mem_filter.mp ha).2
  have hsq_nat : S.card ^ 2 ≤ (2 * N - 1) * h := by
    rw [card_sq_eq_sum_trunc_rep S N hS_bounds]
    calc
      ∑ n ∈ Finset.Icc 2 (2 * N), ((S ×ˢ S).filter (fun p => p.1 + p.2 = n)).card
          ≤ ∑ _n ∈ Finset.Icc 2 (2 * N), h :=
            Finset.sum_le_sum fun n _ => le_trans (trunc_rep_le_full_rep A S hSA n) (hrep n)
      _ = (Finset.Icc 2 (2 * N)).card * h := by rw [Finset.sum_const, smul_eq_mul]
      _ = (2 * N - 1) * h := by rw [Nat.card_Icc]; exact congrArg (· * h) (by omega)
  refine ⟨hsq_nat, ?_⟩
  have hsq_le : (S.card : ℝ) ^ 2 ≤ 2 * (h : ℝ) * (N : ℝ) := by
    have h1 : (S.card : ℝ) ^ 2 ≤ ((2 * N - 1 : ℕ) : ℝ) * (h : ℝ) := by exact_mod_cast hsq_nat
    have h2 : ((2 * N - 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have : 2 * N - 1 ≤ 2 * N := Nat.sub_le _ _
      exact_mod_cast this
    have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    nlinarith
  have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  rw [← Real.sqrt_sq hnonneg]
  exact Real.sqrt_le_sqrt hsq_le

/-! ### Discrete Parseval Engine on `M`-th Roots of Unity (for the `√((90/47) h N)` Bound) -/

private noncomputable def rootU (M : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (((2 * Real.pi * (k : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I)

private lemma rootU_zero (M : ℕ) : rootU M 0 = 1 := by
  simp [rootU]

private lemma rootU_add (M : ℕ) (k₁ k₂ : ℤ) :
    rootU M (k₁ + k₂) = rootU M k₁ * rootU M k₂ := by
  unfold rootU
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma rootU_mul_nat (M : ℕ) (k : ℤ) (n : ℕ) :
    rootU M (k * n) = (rootU M k) ^ n := by
  unfold rootU
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma star_rootU (M : ℕ) (k : ℤ) : star (rootU M k) = rootU M (-k) := by
  unfold rootU
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma norm_rootU (M : ℕ) (k : ℤ) : ‖rootU M k‖ = 1 := by
  unfold rootU
  exact Complex.norm_exp_ofReal_mul_I _

private lemma rootU_pow_M {M : ℕ} (hM : 0 < M) (k : ℤ) :
    (rootU M k) ^ M = 1 := by
  rw [← rootU_mul_nat]
  unfold rootU
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have harg : (2 * Real.pi * ((k * (M : ℤ) : ℤ) : ℝ) / (M : ℝ)) = (k : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp [hM']
  rw [harg]
  have hrew : (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
      (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [hrew, Complex.exp_int_mul_two_pi_mul_I]

private lemma rootU_ne_one {M : ℕ} (hM : 0 < M) {k : ℤ}
    (hk0 : k ≠ 0) (hk_lt : k < M) (hk_gt : -(M : ℤ) < k) :
    rootU M k ≠ 1 := by
  intro heq
  unfold rootU at heq
  rw [Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨n, hn⟩
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hrew : (((2 * Real.pi * (k : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I) =
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

private lemma sum_rootU_ortho {M : ℕ} (hM : 0 < M) {a b : ℕ} (ha : a < M) (hb : b < M) :
    (∑ j : Fin M, rootU M ((a : ℤ) * (j : ℕ)) * star (rootU M ((b : ℤ) * (j : ℕ)))) =
      if a = b then (M : ℂ) else 0 := by
  have hterm : ∀ j : Fin M,
      rootU M ((a : ℤ) * (j : ℕ)) * star (rootU M ((b : ℤ) * (j : ℕ))) =
        (rootU M ((a : ℤ) - (b : ℤ))) ^ (j : ℕ) := by
    intro j
    rw [star_rootU, ← rootU_add, ← rootU_mul_nat]
    congr 1; ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j => (rootU M ((a : ℤ) - (b : ℤ))) ^ j) M]
  by_cases hab : a = b
  · subst hab
    simp [rootU_zero]
  · rw [if_neg hab]
    have hne : rootU M ((a : ℤ) - (b : ℤ)) ≠ 1 :=
      rootU_ne_one hM (by omega) (by omega) (by omega)
    rw [geom_sum_eq hne, rootU_pow_M hM, sub_self, zero_div]

private lemma discrete_parseval_fin {M : ℕ} (hM : 0 < M) (c : ℕ → ℝ) :
    (∑ j : Fin M, ‖∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))‖ ^ 2) =
      (M : ℝ) * ∑ n ∈ Finset.range M, (c n) ^ 2 := by
  have hC :
      (∑ j : Fin M,
        (‖∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))‖ ^ 2 : ℂ)) =
      ((M : ℂ) * ∑ n ∈ Finset.range M, ((c n) ^ 2 : ℂ)) := by
    have hnorm : ∀ j : Fin M,
        (‖∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))‖ ^ 2 : ℂ) =
        (∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))) *
          star (∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))) := by
      intro j
      rw [Complex.star_def, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    simp_rw [hnorm]
    have hexp : ∀ j : Fin M,
        (∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))) *
          star (∑ n ∈ Finset.range M, (c n : ℂ) * rootU M ((n : ℤ) * (j : ℕ))) =
        ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
          ((c a : ℂ) * (c b : ℂ)) *
            (rootU M ((a : ℤ) * (j : ℕ)) * star (rootU M ((b : ℤ) * (j : ℕ)))) := by
      intro j
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    trans ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        ((c a : ℂ) * (c b : ℂ)) *
          ∑ j : Fin M, rootU M ((a : ℤ) * (j : ℕ)) * star (rootU M ((b : ℤ) * (j : ℕ)))
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.mul_sum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have haM : a < M := Finset.mem_range.mp ha
      rw [Finset.sum_eq_single a]
      · rw [sum_rootU_ortho hM haM haM, if_pos rfl]
        ring
      · intro b hb hba
        rw [sum_rootU_ortho hM haM (Finset.mem_range.mp hb), if_neg (Ne.symm hba), mul_zero]
      · intro ha'; exact absurd ha ha'
  exact_mod_cast hC

private lemma rootU_neg_freq {M : ℕ} (hM : 0 < M) (a : ℕ) {j : ℕ} (hj : j ≤ M) :
    rootU M ((a : ℤ) * ((M - j : ℕ) : ℤ)) = star (rootU M ((a : ℤ) * (j : ℤ))) := by
  rw [star_rootU]
  have hsub : ((M - j : ℕ) : ℤ) = (M : ℤ) - (j : ℤ) := by omega
  rw [hsub]
  have hexp : (a : ℤ) * ((M : ℤ) - (j : ℤ)) = (a : ℤ) * (M : ℤ) + -((a : ℤ) * (j : ℤ)) := by ring
  rw [hexp, rootU_add, rootU_mul_nat, rootU_pow_M hM, one_mul]

/-- **Sharper Universal `B_2[h]` Upper Bound (`√((90 / 47) h N) < √(2 h N)`):**
For every `A ⊆ ℕ`, every `h : ℕ` with `∀ n, r_A(n) ≤ h`, and every `N : ℕ`,
`|A ∩ {1, ..., N}| ≤ √((90 / 47) h N)`.
This unconditionally improves the trivial sumset constant `√2 ≈ 1.4142` to `√(90/47) ≈ 1.3838`
for every multiplicity `h ≥ 1`, using discrete Parseval on `2N`-th roots of unity and the
elementary trigonometric identity `2 sin(πx) + cos(2πx) = 1 + 2 sin(πx)(1 - sin(πx)) ≥ 1`. -/
theorem ppl163_b2h_card_le_sqrt_90_div_47 (A : Set ℕ) (h : ℕ)
    (hrep : ∀ n : ℕ,
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ h)
    (N : ℕ) :
    (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤
      Real.sqrt ((90 / 47 : ℝ) * (h : ℝ) * (N : ℝ)) := by
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hS_bounds : ∀ a ∈ S, 1 ≤ a ∧ a ≤ N := by
    intro a ha
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
  have hSA : ∀ a ∈ S, a ∈ A := fun a ha => (Finset.mem_filter.mp ha).2
  have hcard_sq : (S.card : ℝ) ^ 2 ≤ (90 / 47 : ℝ) * (h : ℝ) * (N : ℝ) := by
    by_cases hS0 : S.card = 0
    · simp only [hS0, Nat.cast_zero, sq, mul_zero]
      positivity
    by_cases hN3 : N < 3
    · -- Direct finite verification for N = 0, 1, 2
      have hS_le_N : S.card ≤ N := by
        calc S.card ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
          _ = N := by rw [Nat.card_Icc]; omega
      have hN_pos : 1 ≤ N := by omega
      have hS_pos : 0 < S.card := Nat.pos_of_ne_zero hS0
      rcases Finset.card_pos.mp hS_pos with ⟨a₀, ha₀⟩
      have hh1 : 1 ≤ h := by
        have hmem : (a₀, a₀) ∈ (Finset.range (2 * a₀ + 1) ×ˢ Finset.range (2 * a₀ + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = 2 * a₀) := by
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, hSA a₀ ha₀, hSA a₀ ha₀, by omega⟩
        have hpos : 1 ≤ ((Finset.range (2 * a₀ + 1) ×ˢ Finset.range (2 * a₀ + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = 2 * a₀)).card :=
          Finset.card_pos.mpr ⟨_, hmem⟩
        exact le_trans hpos (hrep (2 * a₀))
      interval_cases N
      · -- N = 1
        have hS1 : S.card = 1 := by omega
        have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
        simp only [hS1, Nat.cast_one, one_pow, mul_one]
        nlinarith
      · -- N = 2
        by_cases hS2 : S.card = 2
        · have hSsub : S ⊆ Finset.Icc 1 2 := fun a ha => Finset.mem_Icc.mpr (hS_bounds a ha)
          have hSeq : S = Finset.Icc 1 2 :=
            Finset.eq_of_subset_of_card_le hSsub (by rw [Nat.card_Icc]; omega)
          have h1A : 1 ∈ A := hSA 1 (by rw [hSeq]; decide)
          have h2A : 2 ∈ A := hSA 2 (by rw [hSeq]; decide)
          have hsub2 : ({(1, 2), (2, 1)} : Finset (ℕ × ℕ)) ⊆
              (Finset.range (3 + 1) ×ˢ Finset.range (3 + 1)).filter
                (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = 3) := by
            intro p hp
            simp only [Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl <;>
              simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range, h1A, h2A]
          have hh2 : 2 ≤ h := by
            have hle2 := Finset.card_le_card hsub2
            have hcard2 : ({(1, 2), (2, 1)} : Finset (ℕ × ℕ)).card = 2 := by decide
            have h3 := hrep 3
            omega
          have hh2R : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh2
          simp only [hS2, Nat.cast_ofNat]
          nlinarith
        · have hS1 : S.card = 1 := by omega
          have hh1R : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
          simp only [hS1, Nat.cast_one, Nat.cast_ofNat]
          nlinarith
    · -- Main case: N ≥ 3, M = 2 * N ≥ 6
      push Not at hN3
      let M : ℕ := 2 * N
      have hM : 0 < M := by omega
      let rS : ℕ → ℕ := fun n => ((S ×ˢ S).filter (fun p => p.1 + p.2 = n)).card
      let F : Fin M → ℂ := fun j => ∑ a ∈ S, rootU M ((a : ℤ) * (j : ℕ))
      -- Convolution identity: (F j)^2 = ∑_{n=2}^{2N} rS(n) * rootU M (n * j)
      have hconv : ∀ j : Fin M,
          (F j) ^ 2 = ∑ n ∈ Finset.Icc 2 M, (rS n : ℂ) * rootU M ((n : ℤ) * (j : ℕ)) := by
        intro j
        calc
          (F j) ^ 2 = (∑ a ∈ S, rootU M ((a : ℤ) * (j : ℕ))) *
              (∑ b ∈ S, rootU M ((b : ℤ) * (j : ℕ))) := sq _
          _ = ∑ p ∈ S ×ˢ S, rootU M (((p.1 + p.2 : ℕ) : ℤ) * (j : ℕ)) := by
                rw [Finset.sum_mul_sum, Finset.sum_product]
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
                rw [← rootU_add]
                congr 1; push_cast; ring
          _ = ∑ n ∈ Finset.Icc 2 M,
                ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = n),
                  rootU M (((p.1 + p.2 : ℕ) : ℤ) * (j : ℕ)) := by
                refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
                intro ⟨a, b⟩ hp
                rw [Finset.mem_product] at hp
                have ha := hS_bounds a hp.1
                have hb := hS_bounds b hp.2
                rw [Finset.mem_Icc]
                omega
          _ = ∑ n ∈ Finset.Icc 2 M, (rS n : ℂ) * rootU M ((n : ℤ) * (j : ℕ)) := by
                refine Finset.sum_congr rfl fun n _ => ?_
                have hcongr : ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = n),
                    rootU M (((p.1 + p.2 : ℕ) : ℤ) * (j : ℕ)) =
                  ∑ _p ∈ (S ×ˢ S).filter (fun p => p.1 + p.2 = n),
                    rootU M ((n : ℤ) * (j : ℕ)) :=
                  Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
                rw [hcongr, Finset.sum_const, nsmul_eq_mul]
      -- Shift by 2 so indices lie in Finset.range M
      let c : ℕ → ℝ := fun m => if m < M - 1 then (rS (m + 2) : ℝ) else 0
      have hnorm_shift : ∀ j : Fin M,
          ‖F j‖ ^ 4 = ‖∑ m ∈ Finset.range M, (c m : ℂ) * rootU M ((m : ℤ) * (j : ℕ))‖ ^ 2 := by
        intro j
        have hstep : ∑ m ∈ Finset.range M, (c m : ℂ) * rootU M ((m : ℤ) * (j : ℕ)) =
            rootU M (-2 * (j : ℕ)) * (F j) ^ 2 := by
          rw [hconv j, Finset.mul_sum]
          have hsplit : Finset.range M = insert (M - 1) (Finset.range (M - 1)) := by
            have : M = (M - 1) + 1 := by omega
            conv_lhs => rw [this, Finset.range_add_one]
          rw [hsplit, Finset.sum_insert (Finset.notMem_range_self)]
          have hlast : c (M - 1) = 0 := by simp [c]
          rw [hlast, Complex.ofReal_zero, zero_mul, zero_add]
          refine Finset.sum_bij (fun m _ => m + 2) ?_ ?_ ?_ ?_
          · intro m hm
            rw [Finset.mem_range] at hm
            rw [Finset.mem_Icc]; omega
          · intro m₁ _ m₂ _ hEq; omega
          · intro n hn
            rw [Finset.mem_Icc] at hn
            exact ⟨n - 2, Finset.mem_range.mpr (by omega), by omega⟩
          · intro m hm
            have hm' : m < M - 1 := Finset.mem_range.mp hm
            simp only [c, if_pos hm']
            rw [← mul_assoc, mul_comm (rootU M (-2 * (j : ℕ))) (rS (m + 2) : ℂ), mul_assoc,
              ← rootU_add]
            congr 2; push_cast; ring
        rw [hstep, norm_mul, norm_rootU, one_mul, norm_pow]
        ring
      -- Parseval identity: ∑_j ‖F j‖^4 = M * ∑_{n=2}^{2N} rS(n)^2 ≤ 2 N h |S|^2
      have hparseval : ∑ j : Fin M, ‖F j‖ ^ 4 ≤ 2 * (N : ℝ) * (h : ℝ) * (S.card : ℝ) ^ 2 := by
        simp_rw [hnorm_shift]
        rw [discrete_parseval_fin hM c]
        have hsum_c : ∑ m ∈ Finset.range M, (c m) ^ 2 =
            ∑ n ∈ Finset.Icc 2 M, (rS n : ℝ) ^ 2 := by
          have hsplit : Finset.range M = insert (M - 1) (Finset.range (M - 1)) := by
            have : M = (M - 1) + 1 := by omega
            conv_lhs => rw [this, Finset.range_add_one]
          rw [hsplit, Finset.sum_insert (Finset.notMem_range_self)]
          simp only [c, lt_self_iff_false, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
            zero_pow, zero_add]
          refine Finset.sum_bij (fun m _ => m + 2) ?_ ?_ ?_ ?_
          · intro m hm; rw [Finset.mem_range] at hm; rw [Finset.mem_Icc]; omega
          · intro m₁ _ m₂ _ hEq; omega
          · intro n hn; rw [Finset.mem_Icc] at hn
            exact ⟨n - 2, Finset.mem_range.mpr (by omega), by omega⟩
          · intro m hm; simp [Finset.mem_range.mp hm]
        rw [hsum_c]
        have hsum_sq_le : ∑ n ∈ Finset.Icc 2 M, (rS n : ℝ) ^ 2 ≤
            (h : ℝ) * ∑ n ∈ Finset.Icc 2 M, (rS n : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun n _ => ?_
          have hr_le : (rS n : ℝ) ≤ (h : ℝ) := by
            exact_mod_cast le_trans (trunc_rep_le_full_rep A S hSA n) (hrep n)
          have hr_nn : (0 : ℝ) ≤ (rS n : ℝ) := Nat.cast_nonneg _
          nlinarith
        have hsum_rS : ∑ n ∈ Finset.Icc 2 M, (rS n : ℝ) = (S.card : ℝ) ^ 2 := by
          exact_mod_cast (card_sq_eq_sum_trunc_rep S N hS_bounds).symm
        rw [hsum_rS] at hsum_sq_le
        have hM_eq : (M : ℝ) = 2 * (N : ℝ) := by simp [M]
        rw [hM_eq]
        have hN_nn : (0 : ℝ) ≤ 2 * (N : ℝ) := by positivity
        nlinarith
      -- Pick the 5 distinct frequencies 0, 1, 2, M - 2, M - 1 in Fin M
      let j0 : Fin M := ⟨0, by omega⟩
      let j1 : Fin M := ⟨1, by omega⟩
      let j2 : Fin M := ⟨2, by omega⟩
      let jm2 : Fin M := ⟨M - 2, by omega⟩
      let jm1 : Fin M := ⟨M - 1, by omega⟩
      let J5 : Finset (Fin M) := {j0, j1, j2, jm2, jm1}
      have hJ5_sum : ∑ j ∈ J5, ‖F j‖ ^ 4 =
          ‖F j0‖ ^ 4 + ‖F j1‖ ^ 4 + ‖F j2‖ ^ 4 + ‖F jm2‖ ^ 4 + ‖F jm1‖ ^ 4 := by
        have h01 : j0 ≠ j1 := by simp [j0, j1, Fin.ext_iff]
        have h02 : j0 ≠ j2 := by simp [j0, j2, Fin.ext_iff]
        have h0m2 : j0 ≠ jm2 := by simp [j0, jm2, Fin.ext_iff]; omega
        have h0m1 : j0 ≠ jm1 := by simp [j0, jm1, Fin.ext_iff]; omega
        have h12 : j1 ≠ j2 := by simp [j1, j2, Fin.ext_iff]
        have h1m2 : j1 ≠ jm2 := by simp [j1, jm2, Fin.ext_iff]; omega
        have h1m1 : j1 ≠ jm1 := by simp [j1, jm1, Fin.ext_iff]; omega
        have h2m2 : j2 ≠ jm2 := by simp [j2, jm2, Fin.ext_iff]; omega
        have h2m1 : j2 ≠ jm1 := by simp [j2, jm1, Fin.ext_iff]; omega
        have hm2m1 : jm2 ≠ jm1 := by simp [jm2, jm1, Fin.ext_iff]; omega
        simp only [J5, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
          Finset.sum_singleton, h01, h02, h0m2, h0m1, h12, h1m2, h1m1, h2m2, h2m1, hm2m1,
          or_self, not_false_eq_true]
        ring
      have h5_le_all : ∑ j ∈ J5, ‖F j‖ ^ 4 ≤ ∑ j : Fin M, ‖F j‖ ^ 4 :=
        Finset.sum_le_univ_sum_of_nonneg fun j => by positivity
      -- Symmetry: ‖F jm1‖ = ‖F j1‖, ‖F jm2‖ = ‖F j2‖, ‖F j0‖ = |S|
      have hF0 : ‖F j0‖ = (S.card : ℝ) := by
        have : F j0 = (S.card : ℂ) := by
          simp [F, j0, rootU_zero]
        rw [this, Complex.norm_natCast]
      have hFm1 : ‖F jm1‖ = ‖F j1‖ := by
        have : F jm1 = star (F j1) := by
          simp only [F, jm1, j1, star_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simpa using rootU_neg_freq hM a (j := 1) (by omega)
        rw [this, norm_star]
      have hFm2 : ‖F jm2‖ = ‖F j2‖ := by
        have : F jm2 = star (F j2) := by
          simp only [F, jm2, j2, star_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simpa using rootU_neg_freq hM a (j := 2) (by omega)
        rw [this, norm_star]
      -- Elementary trigonometric lower bound: |S| ≤ 2 ‖F j1‖ + ‖F j2‖
      have htrig_lb : (S.card : ℝ) ≤ 2 * ‖F j1‖ + ‖F j2‖ := by
        have hN_ne : (N : ℝ) ≠ 0 := by positivity
        have hM_eq : (M : ℝ) = 2 * (N : ℝ) := by simp [M]
        have him1 : (F j1).im = ∑ a ∈ S, Real.sin (Real.pi * (a : ℝ) / (N : ℝ)) := by
          simp only [F, j1, Complex.im_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          unfold rootU
          rw [Complex.exp_ofReal_mul_I_im]
          congr 1
          rw [hM_eq]
          push_cast
          field_simp [hN_ne]
        have hre2 : (F j2).re = ∑ a ∈ S, Real.cos (2 * Real.pi * (a : ℝ) / (N : ℝ)) := by
          simp only [F, j2, Complex.re_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          unfold rootU
          rw [Complex.exp_ofReal_mul_I_re]
          congr 1
          rw [hM_eq]
          push_cast
          field_simp [hN_ne]
        have hpt : ∀ a ∈ S, (1 : ℝ) ≤
            2 * Real.sin (Real.pi * (a : ℝ) / (N : ℝ)) +
              Real.cos (2 * Real.pi * (a : ℝ) / (N : ℝ)) := by
          intro a ha
          have haB := hS_bounds a ha
          set t := Real.pi * (a : ℝ) / (N : ℝ)
          have ht_nn : 0 ≤ t := by positivity
          have ht_le : t ≤ Real.pi := by
            have haN : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast haB.2
            have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
            rw [div_le_iff₀ hNpos]
            nlinarith [Real.pi_pos]
          have hsin_nn : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht_nn ht_le
          have hsin_le : Real.sin t ≤ 1 := Real.sin_le_one t
          have h2t : 2 * Real.pi * (a : ℝ) / (N : ℝ) = 2 * t := by ring
          rw [h2t, Real.cos_two_mul']
          nlinarith [Real.cos_sq_add_sin_sq t]
        have hsum_pt : (S.card : ℝ) ≤ 2 * (F j1).im + (F j2).re := by
          rw [him1, hre2, Finset.mul_sum, ← Finset.sum_add_distrib]
          calc
            (S.card : ℝ) = ∑ _a ∈ S, (1 : ℝ) := by simp
            _ ≤ ∑ a ∈ S, (2 * Real.sin (Real.pi * (a : ℝ) / (N : ℝ)) +
                  Real.cos (2 * Real.pi * (a : ℝ) / (N : ℝ))) := Finset.sum_le_sum hpt
        have h1 : (F j1).im ≤ ‖F j1‖ := (Complex.im_le_norm (F j1))
        have h2 : (F j2).re ≤ ‖F j2‖ := (Complex.re_le_norm (F j2))
        linarith
      -- Two exact squares: (2u + v)^4 ≤ 45 (u^4 + v^4)
      set u := ‖F j1‖
      set v := ‖F j2‖
      have hsq1 : (2 * u + v) ^ 2 ≤ 3 * (2 * u ^ 2 + v ^ 2) := by
        nlinarith [sq_nonneg (u - v)]
      have hsq2 : (2 * u ^ 2 + v ^ 2) ^ 2 ≤ 5 * (u ^ 4 + v ^ 4) := by
        nlinarith [sq_nonneg (u ^ 2 - 2 * v ^ 2)]
      have hpow4 : (S.card : ℝ) ^ 4 ≤ 45 * (u ^ 4 + v ^ 4) := by
        have hS_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
        have h2uv_nn : 0 ≤ 2 * u + v := by positivity
        have hle1 : (S.card : ℝ) ^ 2 ≤ (2 * u + v) ^ 2 := by nlinarith
        have hle2 : (S.card : ℝ) ^ 4 ≤ (2 * u + v) ^ 4 := by
          have : (S.card : ℝ) ^ 4 = ((S.card : ℝ) ^ 2) ^ 2 := by ring
          have : (2 * u + v) ^ 4 = ((2 * u + v) ^ 2) ^ 2 := by ring
          nlinarith
        have hle3 : (2 * u + v) ^ 4 ≤ 9 * (2 * u ^ 2 + v ^ 2) ^ 2 := by
          have : (2 * u + v) ^ 4 = ((2 * u + v) ^ 2) ^ 2 := by ring
          nlinarith [sq_nonneg (2 * u + v)]
        nlinarith
      -- Combine with Parseval
      have h47 : (47 / 45 : ℝ) * (S.card : ℝ) ^ 4 ≤
          2 * (N : ℝ) * (h : ℝ) * (S.card : ℝ) ^ 2 := by
        have hcomb : (S.card : ℝ) ^ 4 + 2 * u ^ 4 + 2 * v ^ 4 ≤
            2 * (N : ℝ) * (h : ℝ) * (S.card : ℝ) ^ 2 := by
          calc
            (S.card : ℝ) ^ 4 + 2 * u ^ 4 + 2 * v ^ 4
                = ‖F j0‖ ^ 4 + ‖F j1‖ ^ 4 + ‖F j2‖ ^ 4 + ‖F jm2‖ ^ 4 + ‖F jm1‖ ^ 4 := by
                  rw [hF0, hFm1, hFm2]; ring
            _ = ∑ j ∈ J5, ‖F j‖ ^ 4 := hJ5_sum.symm
            _ ≤ ∑ j : Fin M, ‖F j‖ ^ 4 := h5_le_all
            _ ≤ 2 * (N : ℝ) * (h : ℝ) * (S.card : ℝ) ^ 2 := hparseval
        nlinarith
      have hS2_pos : (0 : ℝ) < (S.card : ℝ) ^ 2 := by
        have : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS0)
        positivity
      nlinarith
  have hnn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt hcard_sq

private lemma two_mul_sum_Icc_sub (M : ℕ) :
    2 * ∑ d ∈ Finset.Icc 1 (M - 1), (M - d) = M * (M - 1) := by
  induction M with
  | zero => simp
  | succ m ih =>
      cases m with
      | zero => simp
      | succ k =>
          have hsub : ∑ d ∈ Finset.Icc 1 (k + 1), (k + 1 + 1 - d) =
              (∑ d ∈ Finset.Icc 1 k, (k + 1 - d)) + (k + 1) := by
            have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Icc])]
            have hshift : ∑ d ∈ Finset.Icc 1 k, (k + 1 + 1 - d) =
                ∑ d ∈ Finset.Icc 1 k, ((k + 1 - d) + 1) :=
              Finset.sum_congr rfl fun d hd => by rw [Finset.mem_Icc] at hd; omega
            rw [hshift, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
            omega
          simp only [Nat.add_sub_cancel] at ih ⊢
          rw [hsub]
          nlinarith

/-- **Erdős–Turán (1941) / Lindström (1969) Sharp Sidon Upper Bound:**
For every Sidon set `A ⊆ ℕ` (`∀ a b c d ∈ A, a + b = c + d → a = c ∨ a = d`) and every `N ≥ 1`,
`|A ∩ {1, ..., N}| ≤ √N + N^{1/4} + 1`. -/
theorem ppl163_sidon_card_le_lindstrom (A : Set ℕ)
    (hSidon : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → a = c ∨ a = d)
    (N : ℕ) (hN : 1 ≤ N) :
    (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) ≤
      Real.sqrt (N : ℝ) + (N : ℝ) ^ (1 / 4 : ℝ) + 1 := by
  let S := (Finset.Icc 1 N).filter (· ∈ A)
  have hS_bounds : ∀ a ∈ S, 1 ≤ a ∧ a ≤ N := fun a ha =>
    Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
  have hSA : ∀ a ∈ S, a ∈ A := fun a ha => (Finset.mem_filter.mp ha).2
  -- Sliding-window inequality for any M ≥ 1: M * |S|^2 ≤ (N + M - 1) * (M - 1 + |S|)
  have hwindow : ∀ M : ℕ, 1 ≤ M →
      M * S.card ^ 2 ≤ (N + M - 1) * (M - 1 + S.card) := by
    intro M hM
    -- Use shifted windows W t = S ∩ [t + 1 - M, t] for t ∈ Icc 1 (N + M - 1)
    let T := Finset.Icc 1 (N + M - 1)
    let c : ℕ → ℕ := fun t => (S.filter (fun a => a ≤ t ∧ t < a + M)).card
    -- 1. First moment: ∑_{t ∈ T} c t = M * |S|
    have hsum1 : ∑ t ∈ T, c t = M * S.card := by
      have hswap : ∑ t ∈ T, c t =
          ∑ a ∈ S, (T.filter (fun t => a ≤ t ∧ t < a + M)).card := by
        simp only [c, Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap]
      have hcard_each : ∀ a ∈ S, (T.filter (fun t => a ≤ t ∧ t < a + M)).card = M := by
        intro a ha
        have haB := hS_bounds a ha
        have heq : T.filter (fun t => a ≤ t ∧ t < a + M) = Finset.Ico a (a + M) := by
          ext t
          simp only [T, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [heq, Nat.card_Ico]
        omega
      rw [Finset.sum_congr rfl hcard_each, Finset.sum_const, smul_eq_mul, mul_comm]
    -- 2. Ordered off-diagonal pairs in windows: ∑_t c t * (c t - 1) ≤ M * (M - 1)
    have hsum_off : ∑ t ∈ T, c t * (c t - 1) ≤ M * (M - 1) := by
      let P := (S ×ˢ S).filter (fun p => p.1 < p.2 ∧ p.2 < p.1 + M)
      -- Each t contributes 2 * #{a < b in window t} to c t * (c t - 1)
      have hpt : ∀ t ∈ T, c t * (c t - 1) =
          2 * (P.filter (fun p => p.2 ≤ t ∧ t < p.1 + M)).card := by
        intro t _
        let Wt := S.filter (fun a => a ≤ t ∧ t < a + M)
        have hW_off : (Wt ×ˢ Wt).filter (fun p => p.1 ≠ p.2) =
            ((Wt ×ˢ Wt).filter (fun p => p.1 < p.2)) ∪
            ((Wt ×ˢ Wt).filter (fun p => p.2 < p.1)) := by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]
          constructor
          · rintro ⟨hmem, hne⟩
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact Or.inl ⟨hmem, hlt⟩
            · exact Or.inr ⟨hmem, hgt⟩
          · rintro (⟨hmem, hlt⟩ | ⟨hmem, hgt⟩)
            · exact ⟨hmem, hlt.ne⟩
            · exact ⟨hmem, hgt.ne'⟩
        have hdisj : Disjoint ((Wt ×ˢ Wt).filter (fun p => p.1 < p.2))
            ((Wt ×ˢ Wt).filter (fun p => p.2 < p.1)) := by
          rw [Finset.disjoint_left]
          intro ⟨a, b⟩ h1 h2
          simp only [Finset.mem_filter] at h1 h2
          omega
        have hsym : ((Wt ×ˢ Wt).filter (fun p => p.2 < p.1)).card =
            ((Wt ×ˢ Wt).filter (fun p => p.1 < p.2)).card := by
          refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
          · intro ⟨a, b⟩ hp
            simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
            exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
          · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ hEq
            simp only [Prod.mk.injEq] at hEq
            exact Prod.ext hEq.2 hEq.1
          · intro ⟨a, b⟩ hp
            simp only [Finset.mem_filter, Finset.mem_product] at hp
            exact ⟨(b, a), by simp [Finset.mem_filter, Finset.mem_product, hp.1.1, hp.1.2, hp.2],
              rfl⟩
        have hcard_off : ((Wt ×ˢ Wt).filter (fun p => p.1 ≠ p.2)).card =
            Wt.card * (Wt.card - 1) := by
          have heq_off : (Wt ×ˢ Wt).filter (fun p => p.1 ≠ p.2) = Wt.offDiag := by
            ext ⟨a, b⟩
            simp [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product, and_assoc]
          rw [heq_off, Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
        have hfilt_eq : (Wt ×ˢ Wt).filter (fun p => p.1 < p.2) =
            P.filter (fun p => p.2 ≤ t ∧ t < p.1 + M) := by
          ext ⟨a, b⟩
          simp only [Wt, P, Finset.mem_filter, Finset.mem_product]
          constructor
          · rintro ⟨⟨⟨haS, ha1, ha2⟩, ⟨hbS, hb1, hb2⟩⟩, hab⟩
            exact ⟨⟨⟨haS, hbS⟩, hab, by omega⟩, hb1, ha2⟩
          · rintro ⟨⟨⟨haS, hbS⟩, hab, hMab⟩, hbt, hta⟩
            exact ⟨⟨⟨haS, by omega, hta⟩, ⟨hbS, hbt, by omega⟩⟩, hab⟩
        have hc_eq : c t = Wt.card := rfl
        rw [hc_eq, ← hcard_off, hW_off, Finset.card_union_of_disjoint hdisj, hsym, hfilt_eq]
        omega
      rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
      have hswap2 : ∑ t ∈ T, (P.filter (fun p => p.2 ≤ t ∧ t < p.1 + M)).card =
          ∑ p ∈ P, (T.filter (fun t => p.2 ≤ t ∧ t < p.1 + M)).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap2]
      have hcard_p : ∀ p ∈ P,
          (T.filter (fun t => p.2 ≤ t ∧ t < p.1 + M)).card = M - (p.2 - p.1) := by
        intro ⟨a, b⟩ hp
        simp only [P, Finset.mem_filter, Finset.mem_product] at hp
        have haB := hS_bounds a hp.1.1
        have hbB := hS_bounds b hp.1.2
        have heq : T.filter (fun t => b ≤ t ∧ t < a + M) = Finset.Ico b (a + M) := by
          ext t
          simp only [T, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
          omega
        rw [heq, Nat.card_Ico]
        omega
      rw [Finset.sum_congr rfl hcard_p]
      -- Distinct differences in Sidon set: p ↦ p.2 - p.1 is injective on P into Icc 1 (M - 1)
      have hdiff_inj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (P : Set (ℕ × ℕ)) := by
        intro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2 hdiff
        dsimp only at hdiff
        simp only [P, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h1 h2
        have hsum : b₁ + a₂ = b₂ + a₁ := by omega
        rcases hSidon b₁ (hSA _ h1.1.2) a₂ (hSA _ h2.1.1) b₂ (hSA _ h2.1.2) a₁ (hSA _ h1.1.1) hsum
          with hbb | hba
        · exact Prod.ext (by omega) hbb
        · omega
      have hdiff_maps : (P.image (fun p => p.2 - p.1)) ⊆ Finset.Icc 1 (M - 1) := by
        intro d hd
        rcases Finset.mem_image.mp hd with ⟨⟨a, b⟩, hp, rfl⟩
        simp only [P, Finset.mem_filter, Finset.mem_product] at hp
        rw [Finset.mem_Icc]; omega
      have hsum_img : ∑ p ∈ P, (M - (p.2 - p.1)) =
          ∑ d ∈ P.image (fun p => p.2 - p.1), (M - d) := by
        rw [Finset.sum_image (fun p₁ h1 p₂ h2 => hdiff_inj h1 h2)]
      rw [hsum_img]
      have hsum_le : ∑ d ∈ P.image (fun p => p.2 - p.1), (M - d) ≤
          ∑ d ∈ Finset.Icc 1 (M - 1), (M - d) :=
        Finset.sum_le_sum_of_subset hdiff_maps
      have htri : 2 * ∑ d ∈ Finset.Icc 1 (M - 1), (M - d) = M * (M - 1) :=
        two_mul_sum_Icc_sub M
      omega
    -- 3. Cauchy–Schwarz on T (of cardinality N + M - 1)
    have hsum2 : ∑ t ∈ T, c t ^ 2 ≤ M * (M - 1 + S.card) := by
      have hdecomp : ∀ t ∈ T, c t ^ 2 = c t * (c t - 1) + c t := by
        intro t _
        cases hct : c t with
        | zero => simp
        | succ k => simp; ring
      rw [Finset.sum_congr rfl hdecomp, Finset.sum_add_distrib, hsum1]
      nlinarith
    have hCS : (∑ t ∈ T, c t) ^ 2 ≤ T.card * ∑ t ∈ T, c t ^ 2 := by
      have hR := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : ℝ)) (fun t => (c t : ℝ))
      simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hR
      exact_mod_cast hR
    have hTcard : T.card = N + M - 1 := by
      simp only [T, Nat.card_Icc]; omega
    rw [hsum1, hTcard] at hCS
    have hmul : M * (M * S.card ^ 2) ≤ M * ((N + M - 1) * (M - 1 + S.card)) := by
      calc
        M * (M * S.card ^ 2) = (M * S.card) ^ 2 := by ring
        _ ≤ (N + M - 1) * ∑ t ∈ T, c t ^ 2 := hCS
        _ ≤ (N + M - 1) * (M * (M - 1 + S.card)) := Nat.mul_le_mul_left _ hsum2
        _ = M * ((N + M - 1) * (M - 1 + S.card)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hM
  -- Choose M = ⌈N^{3/4}⌉
  let M : ℕ := Nat.ceil ((N : ℝ) ^ (3 / 4 : ℝ))
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN34_pos : (0 : ℝ) < (N : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hM_ge1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by
    intro h0
    have := Nat.le_ceil ((N : ℝ) ^ (3 / 4 : ℝ))
    simp only [M, h0, Nat.cast_zero] at this
    linarith)
  have hM_ge : (N : ℝ) ^ (3 / 4 : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  have hM_lt : ((M - 1 : ℕ) : ℝ) < (N : ℝ) ^ (3 / 4 : ℝ) := by
    have hlt := Nat.ceil_lt_add_one hN34_pos.le
    have hsub : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub hM_ge1, Nat.cast_one]
    linarith
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_ge1
  have hwinR : (M : ℝ) * (S.card : ℝ) ^ 2 ≤
      ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) * (((M - 1 : ℕ) : ℝ) + (S.card : ℝ)) := by
    have hnat := hwindow M hM_ge1
    have hR : (M : ℝ) * (S.card : ℝ) ^ 2 ≤
        ((N + M - 1 : ℕ) : ℝ) * ((M - 1 + S.card : ℕ) : ℝ) := by exact_mod_cast hnat
    have h1 : ((N + M - 1 : ℕ) : ℝ) = (N : ℝ) + ((M - 1 : ℕ) : ℝ) := by
      have : N + M - 1 = N + (M - 1) := by omega
      rw [this, Nat.cast_add]
    have h2 : ((M - 1 + S.card : ℕ) : ℝ) = ((M - 1 : ℕ) : ℝ) + (S.card : ℝ) := by
      rw [Nat.cast_add]
    rwa [h1, h2] at hR
  -- Powers of N^{1/4}
  set q := (N : ℝ) ^ (1 / 4 : ℝ)
  have hq_pos : 0 < q := Real.rpow_pos_of_pos hNpos _
  have hq2 : q ^ 2 = Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hq3 : q ^ 3 = (N : ℝ) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hq4 : q ^ 4 = (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hq_ge1 : 1 ≤ q := Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  -- Divide hwinR by M: x^2 ≤ N + q^3 + (q + 1) * x
  set x := (S.card : ℝ)
  have hx_nn : 0 ≤ x := Nat.cast_nonneg _
  have hM1_le_M : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.sub_le M 1
  have hN_div_M : (N : ℝ) / (M : ℝ) ≤ q := by
    rw [div_le_iff₀ hM_pos]
    calc (N : ℝ) = q ^ 4 := hq4.symm
      _ = q * q ^ 3 := by ring
      _ ≤ q * (M : ℝ) := by rw [hq3]; exact mul_le_mul_of_nonneg_left hM_ge hq_pos.le
  have hquad : x ^ 2 ≤ q ^ 4 + q ^ 3 + (q + 1) * x := by
    have hdiv : x ^ 2 ≤
        ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) * (((M - 1 : ℕ) : ℝ) + x) / (M : ℝ) := by
      rw [le_div_iff₀ hM_pos]
      linarith
    have hterm1 : (N : ℝ) * ((M - 1 : ℕ) : ℝ) / (M : ℝ) ≤ (N : ℝ) := by
      rw [div_le_iff₀ hM_pos]
      exact mul_le_mul_of_nonneg_left hM1_le_M hNpos.le
    have hterm2 : ((M - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) / (M : ℝ) ≤ q ^ 3 := by
      rw [div_le_iff₀ hM_pos, hq3]
      exact mul_le_mul hM_lt.le hM1_le_M (Nat.cast_nonneg _) hN34_pos.le
    have hterm3 : ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) * x / (M : ℝ) ≤ (q + 1) * x := by
      have : ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) / (M : ℝ) ≤ q + 1 := by
        rw [add_div]
        have : ((M - 1 : ℕ) : ℝ) / (M : ℝ) ≤ 1 := (div_le_one hM_pos).mpr hM1_le_M
        linarith
      have hrew : ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) * x / (M : ℝ) =
          (((N : ℝ) + ((M - 1 : ℕ) : ℝ)) / (M : ℝ)) * x := by ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_right this hx_nn
    have hexpand : ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) * (((M - 1 : ℕ) : ℝ) + x) / (M : ℝ) =
        (N : ℝ) * ((M - 1 : ℕ) : ℝ) / (M : ℝ) +
        ((M - 1 : ℕ) : ℝ) * ((M - 1 : ℕ) : ℝ) / (M : ℝ) +
        ((N : ℝ) + ((M - 1 : ℕ) : ℝ)) * x / (M : ℝ) := by ring
    rw [hexpand] at hdiv
    linarith [hq4]
  -- Complete the square: (x - (q + 1) / 2)^2 ≤ (q^2 + q / 2 + 1 / 2)^2
  have hcomp : (x - (q + 1) / 2) ^ 2 ≤ (q ^ 2 + q / 2 + 1 / 2) ^ 2 := by
    nlinarith [sq_nonneg q]
  have hrhs_nn : 0 ≤ q ^ 2 + q / 2 + 1 / 2 := by positivity
  have hle_abs : x - (q + 1) / 2 ≤ q ^ 2 + q / 2 + 1 / 2 :=
    le_of_sq_le_sq hcomp hrhs_nn
  rw [← hq2]
  linarith

/-- **Unconditional Super-`√N` Density Regime (`g(N) → 0`):**
If `|A ∩ {1, ..., N}| / N^{1/2} → ∞` as `N → ∞`, then `limsup_{n → ∞} (1_A * 1_A)(n) = ∞`. -/
theorem ppl163_super_sqrt_implies_limsup_top (A : Set ℕ)
    (hdense : Filter.Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ))
      Filter.atTop Filter.atTop) :
    Filter.limsup
      (fun n : ℕ =>
        (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
      Filter.atTop = ⊤ := by
  rw [(ppl163_limsup_top_iff_unbounded A).1, (ppl163_limsup_top_iff_unbounded A).2]
  rintro ⟨h, hh⟩
  have hev := (Filter.tendsto_atTop.mp hdense) (Real.sqrt (2 * (h : ℝ)) + 1)
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨N₀, hN₀⟩
  let N := max N₀ 1
  have hN1 : 1 ≤ N := le_max_right _ _
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlb := hN₀ N (le_max_left _ _)
  have hub := (ppl163_b2h_card_le_sqrt_two_mul A h hh N).2
  have hsqrt_pos : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hdiv_le : (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) / (N : ℝ) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (2 * (h : ℝ)) := by
    rw [div_le_iff₀ hsqrt_pos, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    exact hub
  linarith

/-! ## Section 3: Exact `#40 ⇒ #28` Reduction (Erdős #40 Implies Erdős–Turán Conjecture) -/

/-- Every asymptotic additive basis `A ⊆ ℕ` of order 2 (`(A + A)ᶜ.Finite`) satisfies
`|A ∩ {1, ..., N}| ≥ (1 / 2) N^{1/2}` for all sufficiently large `N`. -/
theorem ppl163_basis_counting_lower_bound (A : Set ℕ) (hbasis : (A + A)ᶜ.Finite) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) ≤
        (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) := by
  -- Find n₀ such that every n ≥ n₀ lies in A + A
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → n ∈ A + A := by
    by_cases hne : hbasis.toFinset.Nonempty
    · refine ⟨hbasis.toFinset.max' hne + 1, fun n hn => ?_⟩
      by_contra hnot
      have hmem : n ∈ hbasis.toFinset := hbasis.mem_toFinset.mpr hnot
      have hle := Finset.le_max' _ _ hmem
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨0, fun n _ => ?_⟩
      by_contra hnot
      have hmem : n ∈ hbasis.toFinset := hbasis.mem_toFinset.mpr hnot
      simp [hne] at hmem
  refine ⟨4 * n₀ + 16, fun N hN => ?_⟩
  let S0 := (Finset.range (N + 1)).filter (· ∈ A)
  let S1 := (Finset.Icc 1 N).filter (· ∈ A)
  have hS0_le : S0.card ≤ S1.card + 1 := by
    have hsub : S0 ⊆ insert 0 S1 := by
      intro a ha
      simp only [S0, S1, Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_Icc] at ha ⊢
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · exact Or.inr ⟨⟨by omega, by omega⟩, ha.2⟩
    exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le 0 S1)
  have hcover : Finset.Icc n₀ N ⊆ (S0 ×ˢ S0).image (fun p => p.1 + p.2) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rcases Set.mem_add.mp (hn₀ n hn.1) with ⟨a, ha, b, hb, hab⟩
    rw [Finset.mem_image]
    refine ⟨(a, b), ?_, hab⟩
    simp only [S0, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨by omega, ha⟩, ⟨by omega, hb⟩⟩
  have hcard_lb : N + 1 - n₀ ≤ S0.card ^ 2 := by
    calc
      N + 1 - n₀ = (Finset.Icc n₀ N).card := (Nat.card_Icc n₀ N).symm
      _ ≤ ((S0 ×ˢ S0).image (fun p => p.1 + p.2)).card := Finset.card_le_card hcover
      _ ≤ (S0 ×ˢ S0).card := Finset.card_image_le
      _ = S0.card ^ 2 := by rw [Finset.card_product, sq]
  have hcard_R : (3 / 4 : ℝ) * (N : ℝ) ≤ ((S1.card : ℝ) + 1) ^ 2 := by
    have h1 : ((N + 1 - n₀ : ℕ) : ℝ) ≤ (S0.card : ℝ) ^ 2 := by exact_mod_cast hcard_lb
    have h2 : (S0.card : ℝ) ≤ (S1.card : ℝ) + 1 := by exact_mod_cast hS0_le
    have h3 : (3 / 4 : ℝ) * (N : ℝ) ≤ ((N + 1 - n₀ : ℕ) : ℝ) := by
      have hsub : ((N + 1 - n₀ : ℕ) : ℝ) = (N : ℝ) + 1 - (n₀ : ℝ) := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
      have hn₀N : 4 * (n₀ : ℝ) + 16 ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hS0_nn : (0 : ℝ) ≤ (S0.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsqrt_eq : (N : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (N : ℝ) := (Real.sqrt_eq_rpow (N : ℝ)).symm
  rw [hsqrt_eq]
  have hsqrt_ge4 : 4 ≤ Real.sqrt (N : ℝ) := by
    have h16 : (16 : ℝ) ≤ (N : ℝ) := by
      have : 16 ≤ N := by omega
      exact_mod_cast this
    calc (4 : ℝ) = Real.sqrt 16 := by norm_num
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt h16
  have hsq_step : (3 / 4 : ℝ) * Real.sqrt (N : ℝ) ≤ (S1.card : ℝ) + 1 := by
    have h1 : ((3 / 4 : ℝ) * Real.sqrt (N : ℝ)) ^ 2 ≤ ((S1.card : ℝ) + 1) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hN_nn]
      nlinarith
    exact le_of_sq_le_sq h1 (by positivity)
  linarith

/-- **Exact `#40 ⇒ #28` Reduction (for any `g : ℕ → ℝ` with eventually `g(N) ≥ 1`):**
If ANY function `g : ℕ → ℝ` with eventually `1 ≤ g N` satisfies the Erdős Problem #40
implication, then the full Erdős–Turán Conjecture (PPL 050 / Erdős Problem #28) holds! -/
theorem ppl163_erdos40_implies_erdos28 (g : ℕ → ℝ)
    (hg_ge : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 1 ≤ g N)
    (h40 : ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * ((N : ℝ) ^ (1 / 2 : ℝ) / g N) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤) :
    ∀ A : Set ℕ, (A + A)ᶜ.Finite →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤ := by
  intro A hbasis
  rcases hg_ge with ⟨N₁, hN₁⟩
  rcases ppl163_basis_counting_lower_bound A hbasis with ⟨N₀, hN₀⟩
  apply h40 A
  refine ⟨1 / 2, by norm_num, max N₀ N₁, fun N hN => ?_⟩
  have hg1 : 1 ≤ g N := hN₁ N (le_trans (le_max_right _ _) hN)
  have hdiv_le : (N : ℝ) ^ (1 / 2 : ℝ) / g N ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    div_le_self (Real.rpow_nonneg (Nat.cast_nonneg N) _) hg1
  have hlb := hN₀ N (le_trans (le_max_left _ _) hN)
  linarith

/-- **Exact `#40 ⇒ #28` Reduction for any diverging `g(N) → ∞`:**
If ANY function `g : ℕ → ℝ` with `g(N) → ∞` satisfies the Erdős #40 implication, then the full
Erdős–Turán Conjecture (Erdős #28) holds. -/
theorem ppl163_erdos40_tendsto_implies_erdos28 (g : ℕ → ℝ)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (h40 : ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * ((N : ℝ) ^ (1 / 2 : ℝ) / g N) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤) :
    ∀ A : Set ℕ, (A + A)ᶜ.Finite →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤ := by
  have hg_ge : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 1 ≤ g N := by
    have hev := (Filter.tendsto_atTop.mp hg) 1
    rwa [Filter.eventually_atTop] at hev
  exact ppl163_erdos40_implies_erdos28 g hg_ge h40

/-- **Exact `#40 (g ≡ 1) ⇒ #28` Reduction:**
Even the constant threshold `g(N) = 1` (`|A ∩ {1, ..., N}| ≫ N^{1/2} ⇒ limsup r_A(n) = ∞`)
already implies the full Erdős–Turán Conjecture (Erdős #28). -/
theorem ppl163_erdos40_const_one_implies_erdos28
    (h1 : ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * (N : ℝ) ^ (1 / 2 : ℝ) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤) :
    ∀ A : Set ℕ, (A + A)ᶜ.Finite →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤ := by
  refine ppl163_erdos40_implies_erdos28 (fun _ => 1) ⟨0, fun _ _ => le_rfl⟩ ?_
  intro A hA
  apply h1 A
  simpa using hA

/-! ## Section 4: Finitary Block-by-Block Erdős–Rényi (1960) / Cilleruelo–Pliego `N^{g/(2g+1)}` Construction -/

/-- Reusable fiber-counting lemma on `Fin M → Fin L`: if every `f` satisfying `Φ` is uniquely
determined by its restriction outside a coordinate set `S : Finset (Fin M)`, then at most
`L ^ (M - S.card)` functions satisfy `Φ`. -/
private lemma card_filter_determined_coords {M L : ℕ}
    (S : Finset (Fin M)) (Φ : (Fin M → Fin L) → Prop) [DecidablePred Φ]
    (hdet : ∀ f₁ f₂ : Fin M → Fin L, Φ f₁ → Φ f₂ → (∀ i, i ∉ S → f₁ i = f₂ i) → f₁ = f₂) :
    (Finset.univ.filter Φ).card ≤ L ^ (M - S.card) := by
  let res : (Fin M → Fin L) → ({i : Fin M // i ∉ S} → Fin L) := fun f i => f i.1
  have hinj : Set.InjOn res ((Finset.univ.filter Φ : Finset (Fin M → Fin L)) : Set (Fin M → Fin L)) := by
    intro f₁ h1 f₂ h2 hEq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hdet f₁ f₂ h1 h2 (fun i hi => congrFun hEq ⟨i, hi⟩)
  have hcard_sub : Fintype.card {i : Fin M // i ∉ S} = M - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have : Fintype.card {i : Fin M // i ∈ S} = S.card := Fintype.card_coe S
    rw [this]
  calc
    (Finset.univ.filter Φ).card
        = ((Finset.univ.filter Φ).image res).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset ({i : Fin M // i ∉ S} → Fin L)).card := Finset.card_le_univ _
    _ = L ^ (M - S.card) := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcard_sub]

/-- Single-block alteration lemma: given `g ≥ 1`, `L ≥ 1`, `M`, and a previous set `P : Finset ℕ`
with `P.card ≤ M` and `(16 * M)^(2g + 1) ≤ L^g`, there exists `B ⊆ Ico L (2 * L)` such that:
1. `M - M / 2 ≤ B.card` and `B.card ≤ M`,
2. every `n` has at most `g` cross-sum pairs `(p, b) ∈ P × B` with `p + b = n`,
3. every `n` has at most `g` unordered self-sum pairs `(b₁, b₂) ∈ B × B` with `b₁ ≤ b₂` and
   `b₁ + b₂ = n`. -/
private lemma exists_good_block {g L M : ℕ} (hg : 1 ≤ g) (hL : 1 ≤ L)
    (P : Finset ℕ) (hP : P.card ≤ M)
    (hML : (16 * M) ^ (2 * g + 1) ≤ L ^ g) :
    ∃ B : Finset ℕ,
      (∀ b ∈ B, L ≤ b ∧ b < 2 * L) ∧
      M - M / 2 ≤ B.card ∧
      B.card ≤ M ∧
      (∀ n : ℕ, ((P ×ˢ B).filter (fun q => q.1 + q.2 = n)).card ≤ g) ∧
      (∀ n : ℕ, ((B ×ˢ B).filter (fun q => q.1 ≤ q.2 ∧ q.1 + q.2 = n)).card ≤ g) := by
  by_cases hM0 : M = 0
  · subst hM0
    exact ⟨∅, by simp, by simp, by simp, fun _ => by simp, fun _ => by simp⟩
  have hM_pos : 1 ≤ M := Nat.pos_of_ne_zero hM0
  -- Key arithmetic inequalities from (16 * M)^(2g + 1) ≤ L^g
  have h16M_le_L : 16 * M ≤ L := by
    have hLg_le : L ^ g ≤ L ^ (2 * g + 1) := Nat.pow_le_pow_right hL (by omega)
    have hpow : (16 * M) ^ (2 * g + 1) ≤ L ^ (2 * g + 1) := le_trans hML hLg_le
    by_contra hlt
    push Not at hlt
    have : L ^ (2 * g + 1) < (16 * M) ^ (2 * g + 1) := Nat.pow_lt_pow_left hlt (by omega)
    omega
  have h16M2g1_le_Lg : 16 * M ^ (2 * g + 1) ≤ L ^ g := by
    have h16 : 16 ≤ 16 ^ (2 * g + 1) := by
      calc 16 = 16 ^ 1 := (pow_one 16).symm
        _ ≤ 16 ^ (2 * g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 16 * M ^ (2 * g + 1)
        ≤ 16 ^ (2 * g + 1) * M ^ (2 * g + 1) := Nat.mul_le_mul_right _ h16
      _ = (16 * M) ^ (2 * g + 1) := (Nat.mul_pow 16 M (2 * g + 1)).symm
      _ ≤ L ^ g := hML
  -- Four bad-configuration Finsets for each tuple f : Fin M → Fin L
  let Bad1 (f : Fin M → Fin L) : Finset (Fin M × Fin M) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ f p.1 = f p.2)
  let Bad2 (f : Fin M → Fin L) : Finset ((Fin (g + 1) → Fin M) × (Fin (g + 1) → P)) :=
    Finset.univ.filter (fun q =>
      Function.Injective q.1 ∧
      ∀ r : Fin (g + 1), (q.2 r : ℕ) + (f (q.1 r)).val = (q.2 0 : ℕ) + (f (q.1 0)).val)
  let Bad3 (f : Fin M → Fin L) : Finset (Fin (2 * g + 2) → Fin M) :=
    Finset.univ.filter (fun w =>
      Function.Injective w ∧
      ∀ r : Fin (g + 1),
        (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
        (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val)
  let Bad4 (f : Fin M → Fin L) : Finset (Fin (2 * g + 1) → Fin M) :=
    Finset.univ.filter (fun w =>
      Function.Injective w ∧
      ∀ r : Fin g,
        (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
        2 * (f (w ⟨0, by omega⟩)).val)
  -- Sum bound 1: ∑_f (Bad1 f).card ≤ M^2 * L^(M - 1)
  have hsum1 : 16 * ∑ f : Fin M → Fin L, (Bad1 f).card ≤ M * L ^ M := by
    have hswap : ∑ f : Fin M → Fin L, (Bad1 f).card =
        ∑ p : Fin M × Fin M,
          (Finset.univ.filter (fun f : Fin M → Fin L => p.1 < p.2 ∧ f p.1 = f p.2)).card := by
      simp only [Bad1, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    have hpt : ∀ p : Fin M × Fin M,
        (Finset.univ.filter (fun f : Fin M → Fin L => p.1 < p.2 ∧ f p.1 = f p.2)).card ≤
          L ^ (M - 1) := by
      intro ⟨u, v⟩
      dsimp only
      by_cases huv : u < v
      · have hS : ({v} : Finset (Fin M)).card = 1 := Finset.card_singleton v
        calc
          (Finset.univ.filter (fun f : Fin M → Fin L => u < v ∧ f u = f v)).card
              ≤ L ^ (M - ({v} : Finset (Fin M)).card) := by
                apply card_filter_determined_coords {v}
                intro f₁ f₂ h1 h2 hag
                funext i
                by_cases hi : i = v
                · rw [hi]
                  have hu_not : u ∉ ({v} : Finset (Fin M)) := by
                    simp only [Finset.mem_singleton]; exact huv.ne
                  rw [← h1.2, ← h2.2, hag u hu_not]
                · exact hag i (by simp [hi])
          _ = L ^ (M - 1) := by rw [hS]
      · have hemp : Finset.univ.filter (fun f : Fin M → Fin L => u < v ∧ f u = f v) = ∅ := by
          ext f; simp [huv]
        rw [hemp, Finset.card_empty]
        exact Nat.zero_le _
    have hbound : ∑ p : Fin M × Fin M,
        (Finset.univ.filter (fun f : Fin M → Fin L => p.1 < p.2 ∧ f p.1 = f p.2)).card ≤
        M * M * L ^ (M - 1) := by
      calc _ ≤ ∑ _p : Fin M × Fin M, L ^ (M - 1) := Finset.sum_le_sum fun p _ => hpt p
        _ = (Finset.univ : Finset (Fin M × Fin M)).card * L ^ (M - 1) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ = M * M * L ^ (M - 1) := by simp [Fintype.card_prod, Fintype.card_fin]
    have hpow : L * L ^ (M - 1) = L ^ M := by
      conv_rhs => rw [show M = (M - 1) + 1 by omega, pow_succ, mul_comm]
    calc
      16 * ∑ p : Fin M × Fin M,
          (Finset.univ.filter (fun f : Fin M → Fin L => p.1 < p.2 ∧ f p.1 = f p.2)).card
          ≤ 16 * (M * M * L ^ (M - 1)) := Nat.mul_le_mul_left 16 hbound
      _ = M * ((16 * M) * L ^ (M - 1)) := by ring
      _ ≤ M * (L * L ^ (M - 1)) :=
            Nat.mul_le_mul_left M (Nat.mul_le_mul_right _ h16M_le_L)
      _ = M * L ^ M := by rw [hpow]
  -- Sum bound 2: ∑_f (Bad2 f).card
  have hsum2 : 16 * ∑ f : Fin M → Fin L, (Bad2 f).card ≤ M * L ^ M := by
    by_cases hMg : M < g + 1
    · have hzero : ∀ f : Fin M → Fin L, (Bad2 f).card = 0 := by
        intro f
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro q _ hq
        have hle := Fintype.card_le_of_injective q.1 hq.1
        simp only [Fintype.card_fin] at hle
        omega
      simp [hzero]
    · push Not at hMg
      have hswap : ∑ f : Fin M → Fin L, (Bad2 f).card =
          ∑ q : (Fin (g + 1) → Fin M) × (Fin (g + 1) → P),
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective q.1 ∧
              ∀ r : Fin (g + 1),
                (q.2 r : ℕ) + (f (q.1 r)).val = (q.2 0 : ℕ) + (f (q.1 0)).val)).card := by
        simp only [Bad2, Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap]
      have hpt : ∀ q : (Fin (g + 1) → Fin M) × (Fin (g + 1) → P),
          (Finset.univ.filter (fun f : Fin M → Fin L =>
            Function.Injective q.1 ∧
            ∀ r : Fin (g + 1),
              (q.2 r : ℕ) + (f (q.1 r)).val = (q.2 0 : ℕ) + (f (q.1 0)).val)).card ≤
            L ^ (M - g) := by
        intro ⟨u, p⟩
        dsimp only
        by_cases hu : Function.Injective u
        · let R : Finset (Fin (g + 1)) := Finset.univ.erase 0
          let S : Finset (Fin M) := R.image u
          have hScard : S.card = g := by
            rw [Finset.card_image_of_injective _ hu, Finset.card_erase_of_mem (Finset.mem_univ 0),
              Finset.card_univ, Fintype.card_fin]
            omega
          calc
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective u ∧
              ∀ r : Fin (g + 1),
                (p r : ℕ) + (f (u r)).val = (p 0 : ℕ) + (f (u 0)).val)).card
                ≤ L ^ (M - S.card) := by
                  apply card_filter_determined_coords S
                  intro f₁ f₂ h1 h2 hag
                  funext i
                  by_cases hi : i ∈ S
                  · rcases Finset.mem_image.mp hi with ⟨r, hr, rfl⟩
                    have hu0_not : u 0 ∉ S := by
                      intro hmem
                      rcases Finset.mem_image.mp hmem with ⟨r', hr', hEq⟩
                      have := hu hEq
                      rw [Finset.mem_erase] at hr'
                      exact hr'.1 this
                    have hf0 : f₁ (u 0) = f₂ (u 0) := hag (u 0) hu0_not
                    have h1r := h1.2 r
                    have h2r := h2.2 r
                    rw [hf0] at h1r
                    exact Fin.ext (by omega)
                  · exact hag i hi
            _ = L ^ (M - g) := by rw [hScard]
        · have hemp : Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective u ∧
              ∀ r : Fin (g + 1), (p r : ℕ) + (f (u r)).val = (p 0 : ℕ) + (f (u 0)).val) = ∅ := by
            ext f; simp [hu]
          rw [hemp, Finset.card_empty]
          exact Nat.zero_le _
      have hcard_dom :
          (Finset.univ : Finset ((Fin (g + 1) → Fin M) × (Fin (g + 1) → P))).card ≤
            M ^ (2 * g + 2) := by
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, Fintype.card_coe]
        calc M ^ (g + 1) * P.card ^ (g + 1)
            ≤ M ^ (g + 1) * M ^ (g + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP _)
          _ = M ^ (2 * g + 2) := by rw [← pow_add]; congr 1; omega
      have hbound : ∑ q : (Fin (g + 1) → Fin M) × (Fin (g + 1) → P),
          (Finset.univ.filter (fun f : Fin M → Fin L =>
            Function.Injective q.1 ∧
            ∀ r : Fin (g + 1),
              (q.2 r : ℕ) + (f (q.1 r)).val = (q.2 0 : ℕ) + (f (q.1 0)).val)).card ≤
          M ^ (2 * g + 2) * L ^ (M - g) := by
        calc _ ≤ ∑ _q : (Fin (g + 1) → Fin M) × (Fin (g + 1) → P), L ^ (M - g) :=
              Finset.sum_le_sum fun q _ => hpt q
          _ = (Finset.univ : Finset ((Fin (g + 1) → Fin M) × (Fin (g + 1) → P))).card *
                L ^ (M - g) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ M ^ (2 * g + 2) * L ^ (M - g) := Nat.mul_le_mul_right _ hcard_dom
      have hpow : L ^ g * L ^ (M - g) = L ^ M := by
        rw [← pow_add, show g + (M - g) = M by omega]
      calc
        16 * ∑ q : (Fin (g + 1) → Fin M) × (Fin (g + 1) → P),
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective q.1 ∧
              ∀ r : Fin (g + 1),
                (q.2 r : ℕ) + (f (q.1 r)).val = (q.2 0 : ℕ) + (f (q.1 0)).val)).card
            ≤ 16 * (M ^ (2 * g + 2) * L ^ (M - g)) := Nat.mul_le_mul_left 16 hbound
        _ = M * ((16 * M ^ (2 * g + 1)) * L ^ (M - g)) := by
              rw [show 2 * g + 2 = (2 * g + 1) + 1 by omega, pow_succ]; ring
        _ ≤ M * (L ^ g * L ^ (M - g)) :=
              Nat.mul_le_mul_left M (Nat.mul_le_mul_right _ h16M2g1_le_Lg)
        _ = M * L ^ M := by rw [hpow]
  -- Sum bound 3: ∑_f (Bad3 f).card
  have hsum3 : 16 * ∑ f : Fin M → Fin L, (Bad3 f).card ≤ M * L ^ M := by
    by_cases hMg : M < 2 * g + 2
    · have hzero : ∀ f : Fin M → Fin L, (Bad3 f).card = 0 := by
        intro f
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w _ hw
        have hle := Fintype.card_le_of_injective w hw.1
        simp only [Fintype.card_fin] at hle
        omega
      simp [hzero]
    · push Not at hMg
      have hswap : ∑ f : Fin M → Fin L, (Bad3 f).card =
          ∑ w : Fin (2 * g + 2) → Fin M,
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin (g + 1),
                (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
                (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val)).card := by
        simp only [Bad3, Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap]
      have hpt : ∀ w : Fin (2 * g + 2) → Fin M,
          (Finset.univ.filter (fun f : Fin M → Fin L =>
            Function.Injective w ∧
            ∀ r : Fin (g + 1),
              (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
              (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val)).card ≤
            L ^ (M - g) := by
        intro w
        by_cases hw : Function.Injective w
        · let emb : Fin g → Fin M := fun r => w ⟨2 * r.1 + 3, by omega⟩
          have hemb_inj : Function.Injective emb := by
            intro r₁ r₂ hEq
            have := congrArg Fin.val (hw hEq)
            exact Fin.ext (by dsimp at this; omega)
          let S : Finset (Fin M) := Finset.univ.image emb
          have hScard : S.card = g := by
            rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fin]
          calc
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin (g + 1),
                (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
                (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val)).card
                ≤ L ^ (M - S.card) := by
                  apply card_filter_determined_coords S
                  intro f₁ f₂ h1 h2 hag
                  funext i
                  by_cases hi : i ∈ S
                  · rcases Finset.mem_image.mp hi with ⟨r, _, rfl⟩
                    have hnot0 : w ⟨0, by omega⟩ ∉ S := by
                      intro hm; rcases Finset.mem_image.mp hm with ⟨k, _, hEq⟩
                      dsimp only [emb] at hEq
                      have hval := congrArg Fin.val (hw hEq)
                      dsimp only at hval; omega
                    have hnot1 : w ⟨1, by omega⟩ ∉ S := by
                      intro hm; rcases Finset.mem_image.mp hm with ⟨k, _, hEq⟩
                      dsimp only [emb] at hEq
                      have hval := congrArg Fin.val (hw hEq)
                      dsimp only at hval; omega
                    have hnotEven : w ⟨2 * (r.1 + 1), by omega⟩ ∉ S := by
                      intro hm; rcases Finset.mem_image.mp hm with ⟨k, _, hEq⟩
                      dsimp only [emb] at hEq
                      have hval := congrArg Fin.val (hw hEq)
                      dsimp only at hval; omega
                    have hf0 := hag _ hnot0
                    have hf1 := hag _ hnot1
                    have hfe := hag _ hnotEven
                    have h1r := h1.2 ⟨r.1 + 1, by omega⟩
                    have h2r := h2.2 ⟨r.1 + 1, by omega⟩
                    dsimp only at h1r h2r
                    have hidx : (⟨2 * (r.1 + 1) + 1, by omega⟩ : Fin (2 * g + 2)) =
                        ⟨2 * r.1 + 3, by omega⟩ := Fin.ext (by dsimp; omega)
                    rw [hidx] at h1r h2r
                    rw [hf0, hf1, hfe] at h1r
                    exact Fin.ext (by dsimp only [emb]; omega)
                  · exact hag i hi
            _ = L ^ (M - g) := by rw [hScard]
        · have hemp : Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin (g + 1),
                (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
                (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val) = ∅ := by
            ext f; simp [hw]
          rw [hemp, Finset.card_empty]
          exact Nat.zero_le _
      have hbound : ∑ w : Fin (2 * g + 2) → Fin M,
          (Finset.univ.filter (fun f : Fin M → Fin L =>
            Function.Injective w ∧
            ∀ r : Fin (g + 1),
              (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
              (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val)).card ≤
          M ^ (2 * g + 2) * L ^ (M - g) := by
        calc _ ≤ ∑ _w : Fin (2 * g + 2) → Fin M, L ^ (M - g) := Finset.sum_le_sum fun w _ => hpt w
          _ = M ^ (2 * g + 2) * L ^ (M - g) := by
                rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
                  Fintype.card_fin, Fintype.card_fin]
      have hpow : L ^ g * L ^ (M - g) = L ^ M := by
        rw [← pow_add, show g + (M - g) = M by omega]
      calc
        16 * ∑ w : Fin (2 * g + 2) → Fin M,
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin (g + 1),
                (f (w ⟨2 * r.1, by omega⟩)).val + (f (w ⟨2 * r.1 + 1, by omega⟩)).val =
                (f (w ⟨0, by omega⟩)).val + (f (w ⟨1, by omega⟩)).val)).card
            ≤ 16 * (M ^ (2 * g + 2) * L ^ (M - g)) := Nat.mul_le_mul_left 16 hbound
        _ = M * ((16 * M ^ (2 * g + 1)) * L ^ (M - g)) := by
              rw [show 2 * g + 2 = (2 * g + 1) + 1 by omega, pow_succ]; ring
        _ ≤ M * (L ^ g * L ^ (M - g)) :=
              Nat.mul_le_mul_left M (Nat.mul_le_mul_right _ h16M2g1_le_Lg)
        _ = M * L ^ M := by rw [hpow]
  -- Sum bound 4: ∑_f (Bad4 f).card
  have hsum4 : 16 * ∑ f : Fin M → Fin L, (Bad4 f).card ≤ M * L ^ M := by
    by_cases hMg : M < 2 * g + 1
    · have hzero : ∀ f : Fin M → Fin L, (Bad4 f).card = 0 := by
        intro f
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w _ hw
        have hle := Fintype.card_le_of_injective w hw.1
        simp only [Fintype.card_fin] at hle
        omega
      simp [hzero]
    · push Not at hMg
      have hswap : ∑ f : Fin M → Fin L, (Bad4 f).card =
          ∑ w : Fin (2 * g + 1) → Fin M,
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin g,
                (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
                2 * (f (w ⟨0, by omega⟩)).val)).card := by
        simp only [Bad4, Finset.card_filter]
        rw [Finset.sum_comm]
      rw [hswap]
      have hpt : ∀ w : Fin (2 * g + 1) → Fin M,
          (Finset.univ.filter (fun f : Fin M → Fin L =>
            Function.Injective w ∧
            ∀ r : Fin g,
              (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
              2 * (f (w ⟨0, by omega⟩)).val)).card ≤
            L ^ (M - g) := by
        intro w
        by_cases hw : Function.Injective w
        · let emb : Fin g → Fin M := fun r => w ⟨2 * r.1 + 2, by omega⟩
          have hemb_inj : Function.Injective emb := by
            intro r₁ r₂ hEq
            have := congrArg Fin.val (hw hEq)
            exact Fin.ext (by dsimp at this; omega)
          let S : Finset (Fin M) := Finset.univ.image emb
          have hScard : S.card = g := by
            rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fin]
          calc
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin g,
                (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
                2 * (f (w ⟨0, by omega⟩)).val)).card
                ≤ L ^ (M - S.card) := by
                  apply card_filter_determined_coords S
                  intro f₁ f₂ h1 h2 hag
                  funext i
                  by_cases hi : i ∈ S
                  · rcases Finset.mem_image.mp hi with ⟨r, _, rfl⟩
                    have hnot0 : w ⟨0, by omega⟩ ∉ S := by
                      intro hm; rcases Finset.mem_image.mp hm with ⟨k, _, hEq⟩
                      have := congrArg Fin.val (hw hEq); dsimp at this; omega
                    have hnotOdd : w ⟨2 * r.1 + 1, by omega⟩ ∉ S := by
                      intro hm; rcases Finset.mem_image.mp hm with ⟨k, _, hEq⟩
                      have := congrArg Fin.val (hw hEq); dsimp at this; omega
                    have hf0 := hag _ hnot0
                    have hfo := hag _ hnotOdd
                    have h1r := h1.2 r
                    have h2r := h2.2 r
                    rw [hf0, hfo] at h1r
                    exact Fin.ext (by dsimp [emb]; omega)
                  · exact hag i hi
            _ = L ^ (M - g) := by rw [hScard]
        · have hemp : Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin g,
                (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
                2 * (f (w ⟨0, by omega⟩)).val) = ∅ := by
            ext f; simp [hw]
          rw [hemp, Finset.card_empty]
          exact Nat.zero_le _
      have hbound : ∑ w : Fin (2 * g + 1) → Fin M,
          (Finset.univ.filter (fun f : Fin M → Fin L =>
            Function.Injective w ∧
            ∀ r : Fin g,
              (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
              2 * (f (w ⟨0, by omega⟩)).val)).card ≤
          M ^ (2 * g + 1) * L ^ (M - g) := by
        calc _ ≤ ∑ _w : Fin (2 * g + 1) → Fin M, L ^ (M - g) := Finset.sum_le_sum fun w _ => hpt w
          _ = M ^ (2 * g + 1) * L ^ (M - g) := by
                rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun,
                  Fintype.card_fin, Fintype.card_fin]
      have hpow : L ^ g * L ^ (M - g) = L ^ M := by
        rw [← pow_add, show g + (M - g) = M by omega]
      calc
        16 * ∑ w : Fin (2 * g + 1) → Fin M,
            (Finset.univ.filter (fun f : Fin M → Fin L =>
              Function.Injective w ∧
              ∀ r : Fin g,
                (f (w ⟨2 * r.1 + 1, by omega⟩)).val + (f (w ⟨2 * r.1 + 2, by omega⟩)).val =
                2 * (f (w ⟨0, by omega⟩)).val)).card
            ≤ 16 * (M ^ (2 * g + 1) * L ^ (M - g)) := Nat.mul_le_mul_left 16 hbound
        _ = (16 * M ^ (2 * g + 1)) * L ^ (M - g) := by ring
        _ ≤ L ^ g * L ^ (M - g) := Nat.mul_le_mul_right _ h16M2g1_le_Lg
        _ = L ^ M := hpow
        _ ≤ M * L ^ M := Nat.le_mul_of_pos_left _ hM_pos
  -- Averaging: there exists f : Fin M → Fin L with total bad count ≤ M / 2
  let totBad (f : Fin M → Fin L) : ℕ :=
    (Bad1 f).card + (Bad2 f).card + (Bad3 f).card + (Bad4 f).card
  have htot_sum : 2 * ∑ f : Fin M → Fin L, totBad f ≤ M * L ^ M := by
    have hsplit : ∑ f : Fin M → Fin L, totBad f =
        (∑ f, (Bad1 f).card) + (∑ f, (Bad2 f).card) +
        (∑ f, (Bad3 f).card) + (∑ f, (Bad4 f).card) := by
      simp only [totBad, Finset.sum_add_distrib]
    omega
  have hex_f : ∃ f : Fin M → Fin L, totBad f ≤ M / 2 := by
    by_contra hno
    push Not at hno
    have hlow : ∀ f : Fin M → Fin L, M / 2 + 1 ≤ totBad f := fun f => hno f
    have hsum_low : (Finset.univ : Finset (Fin M → Fin L)).card * (M / 2 + 1) ≤
        ∑ f : Fin M → Fin L, totBad f := by
      calc (Finset.univ : Finset (Fin M → Fin L)).card * (M / 2 + 1)
          = ∑ _f : Fin M → Fin L, (M / 2 + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ f : Fin M → Fin L, totBad f := Finset.sum_le_sum fun f _ => hlow f
    have hcard_fun : (Finset.univ : Finset (Fin M → Fin L)).card = L ^ M := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [hcard_fun] at hsum_low
    have hLM_pos : 0 < L ^ M := pow_pos hL M
    have h2 : M + 1 ≤ 2 * (M / 2 + 1) := by omega
    have : (M + 1) * L ^ M ≤ 2 * ∑ f : Fin M → Fin L, totBad f := by
      calc (M + 1) * L ^ M ≤ 2 * (M / 2 + 1) * L ^ M := Nat.mul_le_mul_right _ h2
        _ = 2 * (L ^ M * (M / 2 + 1)) := by ring
        _ ≤ 2 * ∑ f : Fin M → Fin L, totBad f := Nat.mul_le_mul_left 2 hsum_low
    nlinarith
  rcases hex_f with ⟨f, hf_bad⟩
  -- Alteration: delete one witness coordinate from every bad configuration
  let D : Finset (Fin M) :=
    ((Bad1 f).image Prod.snd) ∪
    ((Bad2 f).image (fun q => q.1 0)) ∪
    ((Bad3 f).image (fun w => w ⟨0, by omega⟩)) ∪
    ((Bad4 f).image (fun w => w ⟨0, by omega⟩))
  have hD_card : D.card ≤ M / 2 := by
    calc
      D.card ≤ ((Bad1 f).image Prod.snd).card + ((Bad2 f).image (fun q => q.1 0)).card +
          ((Bad3 f).image (fun w => w ⟨0, by omega⟩)).card +
          ((Bad4 f).image (fun w => w ⟨0, by omega⟩)).card := by
        dsimp only [D]
        have h1 := Finset.card_union_le
          (((Bad1 f).image Prod.snd) ∪ ((Bad2 f).image (fun q => q.1 0)) ∪
            ((Bad3 f).image (fun w => w ⟨0, by omega⟩)))
          ((Bad4 f).image (fun w => w ⟨0, by omega⟩))
        have h2 := Finset.card_union_le
          (((Bad1 f).image Prod.snd) ∪ ((Bad2 f).image (fun q => q.1 0)))
          ((Bad3 f).image (fun w => w ⟨0, by omega⟩))
        have h3 := Finset.card_union_le
          ((Bad1 f).image Prod.snd) ((Bad2 f).image (fun q => q.1 0))
        omega
      _ ≤ totBad f := by
        have c1 := Finset.card_image_le (s := Bad1 f) (f := Prod.snd)
        have c2 := Finset.card_image_le (s := Bad2 f) (f := fun q => q.1 0)
        have c3 := Finset.card_image_le (s := Bad3 f) (f := fun w => w ⟨0, by omega⟩)
        have c4 := Finset.card_image_le (s := Bad4 f) (f := fun w => w ⟨0, by omega⟩)
        dsimp only [totBad]; omega
      _ ≤ M / 2 := hf_bad
  let U : Finset (Fin M) := Finset.univ \ D
  have hU_card : M - M / 2 ≤ U.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  have hf_inj : Set.InjOn (fun i : Fin M => L + (f i).val) (U : Set (Fin M)) := by
    intro i hi j hj hEq
    dsimp only at hEq
    have hfeq : f i = f j := Fin.ext (by omega)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hbad : (i, j) ∈ Bad1 f := by simp [Bad1, hlt, hfeq]
      have hjD : j ∈ D := by
        simp only [D, Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inl ⟨(i, j), hbad, rfl⟩))
      exact (Finset.mem_sdiff.mp hj).2 hjD
    · have hbad : (j, i) ∈ Bad1 f := by simp [Bad1, hgt, hfeq.symm]
      have hiD : i ∈ D := by
        simp only [D, Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inl (Or.inl ⟨(j, i), hbad, rfl⟩))
      exact (Finset.mem_sdiff.mp hi).2 hiD
  let B : Finset ℕ := U.image (fun i => L + (f i).val)
  have hB_card : B.card = U.card := Finset.card_image_of_injOn hf_inj
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · -- Bounds L ≤ b < 2 * L
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
    exact ⟨Nat.le_add_right _ _, by have := (f i).isLt; omega⟩
  · -- Lower cardinality bound
    rw [hB_card]; exact hU_card
  · -- Upper cardinality bound
    rw [hB_card]
    calc U.card ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_le_univ _
      _ = M := by simp
  · -- Cross-sum bound ≤ g
    intro n
    by_contra hgt
    push Not at hgt
    let C := (P ×ˢ B).filter (fun q => q.1 + q.2 = n)
    have hC_ge : g + 1 ≤ C.card := hgt
    obtain ⟨e⟩ := Finset.exists_subset_card_eq hC_ge
    -- Actually take an injection Fin (g + 1) → C via C.equivFin
    let idx : Fin (g + 1) → {q // q ∈ C} :=
      fun r => (C.equivFin.symm ⟨r.1, lt_of_lt_of_le r.2 hC_ge⟩)
    have hidx_inj : Function.Injective idx := by
      intro r₁ r₂ hEq
      have := C.equivFin.symm.injective hEq
      exact Fin.ext (by simpa using congrArg Fin.val this)
    -- Lift each b_r ∈ B to u r ∈ U
    have hmemU : ∀ r : Fin (g + 1), ∃ i ∈ U, L + (f i).val = (idx r).1.2 := by
      intro r
      have hBmem : (idx r).1.2 ∈ B := (Finset.mem_product.mp (Finset.mem_filter.mp (idx r).2).1).2
      exact Finset.mem_image.mp hBmem
    let u : Fin (g + 1) → Fin M := fun r => Classical.choose (hmemU r)
    have huU : ∀ r, u r ∈ U := fun r => (Classical.choose_spec (hmemU r)).1
    have hfu : ∀ r, L + (f (u r)).val = (idx r).1.2 := fun r => (Classical.choose_spec (hmemU r)).2
    let p : Fin (g + 1) → P := fun r =>
      ⟨(idx r).1.1, (Finset.mem_product.mp (Finset.mem_filter.mp (idx r).2).1).1⟩
    have hu_inj : Function.Injective u := by
      intro r₁ r₂ hEq
      have hb_eq : (idx r₁).1.2 = (idx r₂).1.2 := by rw [← hfu r₁, ← hfu r₂, hEq]
      have hsum1 : (idx r₁).1.1 + (idx r₁).1.2 = n := (Finset.mem_filter.mp (idx r₁).2).2
      have hsum2 : (idx r₂).1.1 + (idx r₂).1.2 = n := (Finset.mem_filter.mp (idx r₂).2).2
      have hp_eq : (idx r₁).1.1 = (idx r₂).1.1 := by omega
      exact hidx_inj (Subtype.ext (Prod.ext hp_eq hb_eq))
    have hbad : (u, p) ∈ Bad2 f := by
      simp only [Bad2, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hu_inj, fun r => ?_⟩
      have hsr : (p r : ℕ) + (L + (f (u r)).val) = n := by
        rw [hfu r]; exact (Finset.mem_filter.mp (idx r).2).2
      have hs0 : (p 0 : ℕ) + (L + (f (u 0)).val) = n := by
        rw [hfu 0]; exact (Finset.mem_filter.mp (idx 0).2).2
      omega
    have hu0D : u 0 ∈ D := by
      simp only [D, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨(u, p), hbad, rfl⟩))
    exact (Finset.mem_sdiff.mp (huU 0)).2 hu0D
  · -- Unordered self-sum bound ≤ g
    intro n
    by_contra hgt
    push Not at hgt
    let C := (B ×ˢ B).filter (fun q => q.1 ≤ q.2 ∧ q.1 + q.2 = n)
    have hC_ge : g + 1 ≤ C.card := hgt
    let idx : Fin (g + 1) → {q // q ∈ C} :=
      fun r => C.equivFin.symm ⟨r.1, lt_of_lt_of_le r.2 hC_ge⟩
    have hidx_inj : Function.Injective idx := by
      intro r₁ r₂ hEq
      have := C.equivFin.symm.injective hEq
      exact Fin.ext (by simpa using congrArg Fin.val this)
    -- Every pair in C has elements lifting uniquely to U
    have hmem1 : ∀ r : Fin (g + 1), ∃ i ∈ U, L + (f i).val = (idx r).1.1 := fun r =>
      Finset.mem_image.mp (Finset.mem_product.mp (Finset.mem_filter.mp (idx r).2).1).1
    have hmem2 : ∀ r : Fin (g + 1), ∃ i ∈ U, L + (f i).val = (idx r).1.2 := fun r =>
      Finset.mem_image.mp (Finset.mem_product.mp (Finset.mem_filter.mp (idx r).2).1).2
    let u1 : Fin (g + 1) → Fin M := fun r => Classical.choose (hmem1 r)
    let u2 : Fin (g + 1) → Fin M := fun r => Classical.choose (hmem2 r)
    have hu1U : ∀ r, u1 r ∈ U := fun r => (Classical.choose_spec (hmem1 r)).1
    have hu2U : ∀ r, u2 r ∈ U := fun r => (Classical.choose_spec (hmem2 r)).1
    have hfu1 : ∀ r, L + (f (u1 r)).val = (idx r).1.1 := fun r => (Classical.choose_spec (hmem1 r)).2
    have hfu2 : ∀ r, L + (f (u2 r)).val = (idx r).1.2 := fun r => (Classical.choose_spec (hmem2 r)).2
    have hle_idx : ∀ r, (idx r).1.1 ≤ (idx r).1.2 := fun r => (Finset.mem_filter.mp (idx r).2).2.1
    have hsum_idx : ∀ r, (idx r).1.1 + (idx r).1.2 = n := fun r => (Finset.mem_filter.mp (idx r).2).2.2
    -- Disjointness across distinct indices r ≠ s
    have hdisj_11 : ∀ r s, u1 r = u1 s → r = s := by
      intro r s hEq
      have h1 : (idx r).1.1 = (idx s).1.1 := by rw [← hfu1 r, ← hfu1 s, hEq]
      have h2 : (idx r).1.2 = (idx s).1.2 := by have := hsum_idx r; have := hsum_idx s; omega
      exact hidx_inj (Subtype.ext (Prod.ext h1 h2))
    have hdisj_22 : ∀ r s, u2 r = u2 s → r = s := by
      intro r s hEq
      have h2 : (idx r).1.2 = (idx s).1.2 := by rw [← hfu2 r, ← hfu2 s, hEq]
      have h1 : (idx r).1.1 = (idx s).1.1 := by have := hsum_idx r; have := hsum_idx s; omega
      exact hidx_inj (Subtype.ext (Prod.ext h1 h2))
    have hdisj_12 : ∀ r s, u1 r = u2 s → r = s ∧ (idx r).1.1 = (idx r).1.2 := by
      intro r s hEq
      have h12 : (idx r).1.1 = (idx s).1.2 := by rw [← hfu1 r, ← hfu2 s, hEq]
      have hle_r := hle_idx r
      have hle_s := hle_idx s
      have hs_r := hsum_idx r
      have hs_s := hsum_idx s
      have h1 : (idx r).1.1 = (idx s).1.1 := by omega
      have h2 : (idx r).1.2 = (idx s).1.2 := by omega
      exact ⟨hidx_inj (Subtype.ext (Prod.ext h1 h2)), by omega⟩
    -- Split by whether any diagonal pair exists among idx r
    by_cases hdiag : ∃ r₀ : Fin (g + 1), (idx r₀).1.1 = (idx r₀).1.2
    · -- Case 4: exactly one diagonal pair r₀; permute r₀ to 0 and build w : Fin (2g + 1) → Fin M
      rcases hdiag with ⟨r₀, hr₀⟩
      let perm : Fin (g + 1) ≃ Fin (g + 1) := Equiv.swap 0 r₀
      have hperm0 : perm 0 = r₀ := Equiv.swap_apply_left 0 r₀
      have hnon_diag : ∀ k : Fin g, (idx (perm ⟨k.1 + 1, by omega⟩)).1.1 ≠
          (idx (perm ⟨k.1 + 1, by omega⟩)).1.2 := by
        intro k hEq
        have hne : perm ⟨k.1 + 1, by omega⟩ ≠ r₀ := by
          rw [← hperm0]
          intro h
          have := perm.injective h
          have := congrArg Fin.val this
          dsimp at this; omega
        have hs1 := hsum_idx (perm ⟨k.1 + 1, by omega⟩)
        have hs0 := hsum_idx r₀
        have h1 : (idx (perm ⟨k.1 + 1, by omega⟩)).1.1 = (idx r₀).1.1 := by omega
        have h2 : (idx (perm ⟨k.1 + 1, by omega⟩)).1.2 = (idx r₀).1.2 := by omega
        exact hne (hidx_inj (Subtype.ext (Prod.ext h1 h2)))
      let w : Fin (2 * g + 1) → Fin M := fun t =>
        if ht0 : t.1 = 0 then u1 r₀
        else if t.1 % 2 = 1 then u1 (perm ⟨(t.1 - 1) / 2 + 1, by omega⟩)
        else u2 (perm ⟨(t.1 - 2) / 2 + 1, by omega⟩)
      have hw_inj : Function.Injective w := by
        intro a b hEq
        dsimp only [w] at hEq
        split_ifs at hEq with ha0 hb0 ha1 hb1 hb1' ha1' hb1''
        · exact Fin.ext (by omega)
        · have := hdisj_11 _ _ hEq
          have hne : perm ⟨(b.1 - 1) / 2 + 1, by omega⟩ ≠ r₀ := by
            rw [← hperm0]; intro h; have := congrArg Fin.val (perm.injective h); dsimp at this; omega
          exact absurd this.symm hne
        · have := (hdisj_12 _ _ hEq).1
          have hne : perm ⟨(b.1 - 2) / 2 + 1, by omega⟩ ≠ r₀ := by
            rw [← hperm0]; intro h; have := congrArg Fin.val (perm.injective h); dsimp at this; omega
          exact absurd this.symm hne
        · have := hdisj_11 _ _ hEq
          have hne : perm ⟨(a.1 - 1) / 2 + 1, by omega⟩ ≠ r₀ := by
            rw [← hperm0]; intro h; have := congrArg Fin.val (perm.injective h); dsimp at this; omega
          exact absurd this hne
        · have := perm.injective (hdisj_11 _ _ hEq)
          have := congrArg Fin.val this; dsimp at this
          exact Fin.ext (by omega)
        · have h12 := hdisj_12 _ _ hEq
          exact absurd h12.2 (hnon_diag ⟨(a.1 - 1) / 2, by omega⟩)
        · have := (hdisj_12 _ _ hEq.symm).1
          have hne : perm ⟨(a.1 - 2) / 2 + 1, by omega⟩ ≠ r₀ := by
            rw [← hperm0]; intro h; have := congrArg Fin.val (perm.injective h); dsimp at this; omega
          exact absurd this.symm hne
        · have h12 := hdisj_12 _ _ hEq.symm
          exact absurd h12.2 (hnon_diag ⟨(b.1 - 1) / 2, by omega⟩)
        · have := perm.injective (hdisj_22 _ _ hEq)
          have := congrArg Fin.val this; dsimp at this
          exact Fin.ext (by omega)
      have hbad : w ∈ Bad4 f := by
        simp only [Bad4, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hw_inj, fun k => ?_⟩
        have hw0 : w ⟨0, by omega⟩ = u1 r₀ := by simp [w]
        have hw1 : w ⟨2 * k.1 + 1, by omega⟩ = u1 (perm ⟨k.1 + 1, by omega⟩) := by
          simp only [w]
          rw [dif_neg (by omega), if_pos (by omega)]
          congr 2; exact Fin.ext (by dsimp; omega)
        have hw2 : w ⟨2 * k.1 + 2, by omega⟩ = u2 (perm ⟨k.1 + 1, by omega⟩) := by
          simp only [w]
          rw [dif_neg (by omega), if_neg (by omega)]
          congr 2; exact Fin.ext (by dsimp; omega)
        rw [hw0, hw1, hw2]
        have h1 := hfu1 (perm ⟨k.1 + 1, by omega⟩)
        have h2 := hfu2 (perm ⟨k.1 + 1, by omega⟩)
        have hs := hsum_idx (perm ⟨k.1 + 1, by omega⟩)
        have h0 := hfu1 r₀
        have hs0 := hsum_idx r₀
        omega
      have hw0D : w ⟨0, by omega⟩ ∈ D := by
        simp only [D, Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨w, hbad, rfl⟩
      have hw0U : w ⟨0, by omega⟩ ∈ U := by
        have : w ⟨0, by omega⟩ = u1 r₀ := by simp [w]
        rw [this]; exact hu1U r₀
      exact (Finset.mem_sdiff.mp hw0U).2 hw0D
    · -- Case 3: no diagonal pair; all 2(g + 1) indices are pairwise distinct
      push Not at hdiag
      let w : Fin (2 * g + 2) → Fin M := fun t =>
        if t.1 % 2 = 0 then u1 ⟨t.1 / 2, by omega⟩ else u2 ⟨t.1 / 2, by omega⟩
      have hw_inj : Function.Injective w := by
        intro a b hEq
        dsimp only [w] at hEq
        split_ifs at hEq with ha hb hb'
        · have := congrArg Fin.val (hdisj_11 _ _ hEq); dsimp at this
          exact Fin.ext (by omega)
        · exact absurd (hdisj_12 _ _ hEq).2 (hdiag _)
        · exact absurd (hdisj_12 _ _ hEq.symm).2 (hdiag _)
        · have := congrArg Fin.val (hdisj_22 _ _ hEq); dsimp at this
          exact Fin.ext (by omega)
      have hbad : w ∈ Bad3 f := by
        simp only [Bad3, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hw_inj, fun r => ?_⟩
        have hw0 : w ⟨0, by omega⟩ = u1 0 := by simp [w]
        have hw1 : w ⟨1, by omega⟩ = u2 0 := by simp [w]
        have hwe : w ⟨2 * r.1, by omega⟩ = u1 r := by
          simp only [w, if_pos (show 2 * r.1 % 2 = 0 by omega)]
          congr 1; exact Fin.ext (by dsimp; omega)
        have hwo : w ⟨2 * r.1 + 1, by omega⟩ = u2 r := by
          simp only [w, if_neg (show ¬ (2 * r.1 + 1) % 2 = 0 by omega)]
          congr 1; exact Fin.ext (by dsimp; omega)
        rw [hw0, hw1, hwe, hwo]
        have h1 := hfu1 r; have h2 := hfu2 r; have hs := hsum_idx r
        have h01 := hfu1 0; have h02 := hfu2 0; have hs0 := hsum_idx 0
        omega
      have hw0D : w ⟨0, by omega⟩ ∈ D := by
        simp only [D, Finset.mem_union, Finset.mem_image]
        exact Or.inl (Or.inr ⟨w, hbad, rfl⟩)
      have hw0U : w ⟨0, by omega⟩ ∈ U := by
        have : w ⟨0, by omega⟩ = u1 0 := by simp [w]
        rw [this]; exact hu1U 0
      exact (Finset.mem_sdiff.mp hw0U).2 hw0D

/-- Target size `M_j` for block `j` (`[16^j, 2 * 16^j)`): the largest `m` with
`(16 * m)^(2g + 1) ≤ (16^j)^g`. -/
private lemma exists_blockSize_bound (g j : ℕ) :
    ∃ m : ℕ, (16 ^ j) ^ g < (16 * (m + 1)) ^ (2 * g + 1) := by
  refine ⟨(16 ^ j) ^ g, ?_⟩
  have h1 : (16 ^ j) ^ g < 16 * ((16 ^ j) ^ g + 1) := by omega
  calc (16 ^ j) ^ g < 16 * ((16 ^ j) ^ g + 1) := h1
    _ = (16 * ((16 ^ j) ^ g + 1)) ^ 1 := (pow_one _).symm
    _ ≤ (16 * ((16 ^ j) ^ g + 1)) ^ (2 * g + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)

private noncomputable def blockSize (g j : ℕ) : ℕ :=
  Nat.find (exists_blockSize_bound g j)

private lemma blockSize_lt (g j : ℕ) :
    (16 ^ j) ^ g < (16 * (blockSize g j + 1)) ^ (2 * g + 1) :=
  Nat.find_spec (exists_blockSize_bound g j)

private lemma blockSize_le (g j : ℕ) :
    (16 * blockSize g j) ^ (2 * g + 1) ≤ (16 ^ j) ^ g := by
  unfold blockSize
  cases hm : Nat.find (exists_blockSize_bound g j) with
  | zero => simp
  | succ k =>
      have hmin := Nat.find_min (exists_blockSize_bound g j) (show k < Nat.find _ by omega)
      push Not at hmin
      exact hmin

private lemma two_mul_blockSize_le_succ {g : ℕ} (hg : 1 ≤ g) (j : ℕ) :
    2 * blockSize g j ≤ blockSize g (j + 1) := by
  by_contra hlt
  push Not at hlt
  have h1 : blockSize g (j + 1) + 1 ≤ 2 * blockSize g j := by omega
  have h2pow : 2 ^ (2 * g + 1) ≤ 16 ^ g := by
    have : 2 ^ (2 * g + 1) = 2 * 4 ^ g := by
      rw [pow_succ, mul_comm, pow_mul]; norm_num
    have h4 : 16 ^ g = 4 ^ g * 4 ^ g := by
      rw [← mul_pow]; norm_num
    have h4g : 2 ≤ 4 ^ g := by
      calc 2 ≤ 4 ^ 1 := by norm_num
        _ ≤ 4 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    rw [this, h4]
    exact Nat.mul_le_mul_right _ h4g
  have hchain : (16 ^ (j + 1)) ^ g < (16 ^ (j + 1)) ^ g := by
    calc
      (16 ^ (j + 1)) ^ g
          < (16 * (blockSize g (j + 1) + 1)) ^ (2 * g + 1) := blockSize_lt g (j + 1)
      _ ≤ (16 * (2 * blockSize g j)) ^ (2 * g + 1) :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_left 16 h1) _
      _ = 2 ^ (2 * g + 1) * (16 * blockSize g j) ^ (2 * g + 1) := by
            rw [show 16 * (2 * blockSize g j) = 2 * (16 * blockSize g j) by ring, mul_pow]
      _ ≤ 16 ^ g * (16 ^ j) ^ g := Nat.mul_le_mul h2pow (blockSize_le g j)
      _ = (16 ^ (j + 1)) ^ g := by rw [← mul_pow, pow_succ, mul_comm]
  exact lt_irrefl _ hchain

private lemma blockSize_ge_one {g j : ℕ} (hg : 1 ≤ g) (hj : 3 ≤ j) :
    1 ≤ blockSize g j := by
  by_contra h0
  have hzero : blockSize g j = 0 := by omega
  have hlt := blockSize_lt g j
  rw [hzero] at hlt
  simp only [zero_add, mul_one] at hlt
  have hexp : 2 * g + 1 ≤ j * g := by nlinarith
  have hle : 16 ^ (2 * g + 1) ≤ (16 ^ j) ^ g := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hexp
  omega

/-- Inductive state bundling the cumulative prefix `P_j = ⋃_{i < j} A_i` and all block invariants. -/
private structure BlockChain (g : ℕ) (j : ℕ) where
  prefixSet : Finset ℕ
  blocks : Fin j → Finset ℕ
  prefix_card : prefixSet.card ≤ blockSize g j
  prefix_eq : ∀ x, x ∈ prefixSet ↔ ∃ i : Fin j, x ∈ blocks i
  block_bounds : ∀ i : Fin j, ∀ b ∈ blocks i, 16 ^ i.1 ≤ b ∧ b < 2 * 16 ^ i.1
  block_lb : ∀ i : Fin j, blockSize g i.1 - blockSize g i.1 / 2 ≤ (blocks i).card
  block_ub : ∀ i : Fin j, (blocks i).card ≤ blockSize g i.1
  cross_bound : ∀ i : Fin j, ∀ n : ℕ,
    (((Finset.univ.filter (fun k : Fin j => k.1 < i.1)).biUnion blocks ×ˢ blocks i).filter
      (fun q => q.1 + q.2 = n)).card ≤ g
  self_bound : ∀ i : Fin j, ∀ n : ℕ,
    ((blocks i ×ˢ blocks i).filter (fun q => q.1 ≤ q.2 ∧ q.1 + q.2 = n)).card ≤ g

private noncomputable def buildChain {g : ℕ} (hg : 1 ≤ g) : ∀ j : ℕ, BlockChain g j
  | 0 =>
    { prefixSet := ∅
      blocks := Fin.elim0
      prefix_card := by simp
      prefix_eq := by simp
      block_bounds := fun i => Fin.elim0 i
      block_lb := fun i => Fin.elim0 i
      block_ub := fun i => Fin.elim0 i
      cross_bound := fun i => Fin.elim0 i
      self_bound := fun i => Fin.elim0 i }
  | j + 1 =>
    let prev := buildChain hg j
    have hex := exists_good_block hg (Nat.one_le_pow j 16 (by norm_num))
      prev.prefixSet prev.prefix_card (blockSize_le g j)
    let B := Classical.choose hex
    have hB := Classical.choose_spec hex
    { prefixSet := prev.prefixSet ∪ B
      blocks := Fin.snoc prev.blocks B
      prefix_card := by
        calc (prev.prefixSet ∪ B).card
            ≤ prev.prefixSet.card + B.card := Finset.card_union_le _ _
          _ ≤ blockSize g j + blockSize g j := Nat.add_le_add prev.prefix_card hB.2.2.1
          _ = 2 * blockSize g j := by omega
          _ ≤ blockSize g (j + 1) := two_mul_blockSize_le_succ hg j
      prefix_eq := by
        intro x
        rw [Finset.mem_union, prev.prefix_eq]
        constructor
        · rintro (⟨i, hi⟩ | hxB)
          · exact ⟨i.castSucc, by simpa [Fin.snoc_castSucc] using hi⟩
          · exact ⟨Fin.last j, by simpa [Fin.snoc_last] using hxB⟩
        · rintro ⟨i, hi⟩
          refine Fin.lastCases ?_ ?_ i hi
          · intro h; exact Or.inr (by simpa [Fin.snoc_last] using h)
          · intro k h; exact Or.inl ⟨k, by simpa [Fin.snoc_castSucc] using h⟩
      block_bounds := fun i => by
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]; exact hB.1
        · intro k; rw [Fin.snoc_castSucc]; exact prev.block_bounds k
      block_lb := fun i => by
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]; exact hB.2.1
        · intro k; rw [Fin.snoc_castSucc]; exact prev.block_lb k
      block_ub := fun i => by
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]; exact hB.2.2.1
        · intro k; rw [Fin.snoc_castSucc]; exact prev.block_ub k
      cross_bound := fun i n => by
        refine Fin.lastCases ?_ ?_ i
        · -- i = Fin.last j: previous blocks biUnion equals prev.prefixSet
          have hbi : (Finset.univ.filter (fun k : Fin (j + 1) => k.1 < (Fin.last j).1)).biUnion
              (Fin.snoc prev.blocks B) = prev.prefixSet := by
            ext x
            rw [Finset.mem_biUnion, prev.prefix_eq]
            constructor
            · rintro ⟨k, hk, hxk⟩
              rw [Finset.mem_filter] at hk
              refine Fin.lastCases ?_ ?_ k hk.2 hxk
              · intro hlt _; simp at hlt
              · intro r _ hxr; exact ⟨r, by simpa [Fin.snoc_castSucc] using hxr⟩
            · rintro ⟨r, hxr⟩
              exact ⟨r.castSucc, by simp [Finset.mem_filter, r.isLt],
                by simpa [Fin.snoc_castSucc] using hxr⟩
          rw [hbi, Fin.snoc_last]
          exact hB.2.2.2.1 n
        · intro k
          have hbi : (Finset.univ.filter (fun m : Fin (j + 1) => m.1 < k.castSucc.1)).biUnion
              (Fin.snoc prev.blocks B) =
              (Finset.univ.filter (fun m : Fin j => m.1 < k.1)).biUnion prev.blocks := by
            ext x
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨m, hm, hxm⟩
              refine Fin.lastCases ?_ ?_ m hm hxm
              · intro hlt _; have := k.isLt; simp at hlt; omega
              · intro r hr hxr; exact ⟨r, hr, by simpa [Fin.snoc_castSucc] using hxr⟩
            · rintro ⟨r, hr, hxr⟩
              exact ⟨r.castSucc, hr, by simpa [Fin.snoc_castSucc] using hxr⟩
          rw [hbi, Fin.snoc_castSucc]
          exact prev.cross_bound k n
      self_bound := fun i n => by
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]; exact hB.2.2.2.2 n
        · intro k; rw [Fin.snoc_castSucc]; exact prev.self_bound k n }

private lemma buildChain_blocks_stable {g : ℕ} (hg : 1 ≤ g) :
    ∀ {j k : ℕ} (hk : k < j),
      (buildChain hg (j + 1)).blocks ⟨k, by omega⟩ = (buildChain hg j).blocks ⟨k, hk⟩ := by
  intro j k hk
  dsimp [buildChain]
  have hcast : (⟨k, by omega⟩ : Fin (j + 1)) = (⟨k, hk⟩ : Fin j).castSucc := rfl
  rw [hcast, Fin.snoc_castSucc]

private lemma buildChain_blocks_eq {g : ℕ} (hg : 1 ≤ g) {j₁ j₂ k : ℕ}
    (h1 : k < j₁) (h2 : k < j₂) :
    (buildChain hg j₁).blocks ⟨k, h1⟩ = (buildChain hg j₂).blocks ⟨k, h2⟩ := by
  have hle : ∀ (j : ℕ) (h : k < j),
      (buildChain hg j).blocks ⟨k, h⟩ = (buildChain hg (k + 1)).blocks ⟨k, Nat.lt_succ_self k⟩ := by
    intro j
    induction j with
    | zero => intro h; omega
    | succ m ih =>
        intro h
        by_cases hm : k < m
        · exact (buildChain_blocks_stable hg hm).trans (ih hm)
        · have hmk : m = k := by omega
          subst hmk
          rfl
  exact (hle j₁ h1).trans (hle j₂ h2).symm

/-- **Quantitative Erdős–Rényi (1960) / Cilleruelo–Pliego `N^{g/(2g+1)}` Existence Theorem:**
For every positive integer `g ≥ 1`, there exists an infinite subset `A ⊆ ℕ` whose ordered
representation function is globally bounded by `4 g` (`∀ n, r_A(n) ≤ 4 g`) and whose counting
function satisfies `|A ∩ {1, ..., N}| ≥ (1 / 2048) · N^{g / (2g + 1)}` for ALL `N ≥ 8192`. -/
theorem ppl163_erdos_renyi_b2g_existence (g : ℕ) (hg : 1 ≤ g) :
    ∃ A : Set ℕ,
      (∀ n : ℕ,
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ 4 * g) ∧
      (∀ N : ℕ, 8192 ≤ N →
        (1 / 2048 : ℝ) * (N : ℝ) ^ ((g : ℝ) / (2 * (g : ℝ) + 1)) ≤
          (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) := by
  let block : ℕ → Finset ℕ := fun j => (buildChain hg (j + 1)).blocks (Fin.last j)
  let A : Set ℕ := {x : ℕ | ∃ j : ℕ, x ∈ block j}
  have hblock_bounds : ∀ j : ℕ, ∀ b ∈ block j, 16 ^ j ≤ b ∧ b < 2 * 16 ^ j :=
    fun j b hb => (buildChain hg (j + 1)).block_bounds (Fin.last j) b hb
  have hblock_lb : ∀ j : ℕ, blockSize g j - blockSize g j / 2 ≤ (block j).card :=
    fun j => (buildChain hg (j + 1)).block_lb (Fin.last j)
  have hblock_self : ∀ j n : ℕ,
      ((block j ×ˢ block j).filter (fun q => q.1 ≤ q.2 ∧ q.1 + q.2 = n)).card ≤ g :=
    fun j n => (buildChain hg (j + 1)).self_bound (Fin.last j) n
  have hblock_cross : ∀ j n : ℕ,
      (((Finset.range j).biUnion block ×ˢ block j).filter (fun q => q.1 + q.2 = n)).card ≤ g := by
    intro j n
    have hbi : (Finset.range j).biUnion block =
        (Finset.univ.filter (fun k : Fin (j + 1) => k.1 < (Fin.last j).1)).biUnion
          (buildChain hg (j + 1)).blocks := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, hxi⟩
        refine ⟨⟨i, by omega⟩, hi, ?_⟩
        dsimp only [block] at hxi
        have heq := buildChain_blocks_eq hg (j₁ := i + 1) (j₂ := j + 1) (k := i) (by omega) (by omega)
        exact heq ▸ hxi
      · rintro ⟨k, hk, hxk⟩
        have hklt : k.1 < j := hk
        refine ⟨k.1, hklt, ?_⟩
        dsimp only [block]
        have heq := buildChain_blocks_eq hg (j₁ := k.1 + 1) (j₂ := j + 1) (k := k.1) (by omega) k.isLt
        exact heq.symm ▸ hxk
    rw [hbi]
    exact (buildChain hg (j + 1)).cross_bound (Fin.last j) n
  refine ⟨A, ?_, ?_⟩
  · -- Part 1: Global representation bound r_A(n) ≤ 4 * g
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      have hemp : (Finset.range 1 ×ˢ Finset.range 1).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = 0) = ∅ := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.notMem_empty, iff_false]
        rintro ⟨_, ⟨j, hj⟩, _, hab⟩
        have := (hblock_bounds j a hj).1
        have h16 : 1 ≤ 16 ^ j := Nat.one_le_pow j 16 (by norm_num)
        omega
      rw [hemp, Finset.card_empty]
      exact Nat.zero_le _
    · -- Find unique j with 16^j ≤ n < 16^(j + 1)
      have hex_j : ∃ j : ℕ, 16 ^ j ≤ n ∧ n < 16 ^ (j + 1) := by
        have hlt_pow : ∃ k : ℕ, n < 16 ^ k := ⟨n + 1, by
          calc n < n + 1 := Nat.lt_succ_self n
            _ ≤ 2 ^ (n + 1) := Nat.le_of_lt (Nat.lt_two_pow_self)
            _ ≤ 16 ^ (n + 1) := Nat.pow_le_pow_left (by norm_num) _⟩
        let k := Nat.find hlt_pow
        have hk_lt : n < 16 ^ k := Nat.find_spec hlt_pow
        have hk_pos : 1 ≤ k := by
          by_contra h0
          have hk0 : k = 0 := by omega
          rw [hk0] at hk_lt; omega
        refine ⟨k - 1, ?_, by rwa [show k - 1 + 1 = k by omega]⟩
        have hmin := Nat.find_min hlt_pow (show k - 1 < k by omega)
        omega
      rcases hex_j with ⟨j, hj_le, hj_lt⟩
      let Pj := (Finset.range j).biUnion block
      let Bj := block j
      let S1 := (Pj ×ˢ Bj).filter (fun q => q.1 + q.2 = n)
      let S2 := ((Pj ×ˢ Bj).filter (fun q => q.1 + q.2 = n)).image Prod.swap
      let S3 := (Bj ×ˢ Bj).filter (fun q => q.1 ≤ q.2 ∧ q.1 + q.2 = n)
      let S4 := ((Bj ×ˢ Bj).filter (fun q => q.1 ≤ q.2 ∧ q.1 + q.2 = n)).image Prod.swap
      have hsub : (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n) ⊆ S1 ∪ S2 ∪ S3 ∪ S4 := by
        intro ⟨a, b⟩ hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        rcases hp.2.1 with ⟨i, hi⟩
        rcases hp.2.2.1 with ⟨k, hk⟩
        have haB := hblock_bounds i a hi
        have hbB := hblock_bounds k b hk
        have hab := hp.2.2.2
        -- Prove max i k = j
        have hmax_eq : max i k = j := by
          have hlow : 16 ^ (max i k) ≤ n := by
            rcases max_choice i k with h | h <;> rw [h] <;> omega
          have hhigh : n < 16 ^ (max i k + 1) := by
            have h1 : 16 ^ i ≤ 16 ^ (max i k) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
            have h2 : 16 ^ k ≤ 16 ^ (max i k) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
            rw [pow_succ]; omega
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have : 16 ^ (max i k + 1) ≤ 16 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
          · have : 16 ^ (j + 1) ≤ 16 ^ (max i k) := Nat.pow_le_pow_right (by norm_num) (by omega)
            omega
        simp only [Finset.mem_union]
        by_cases hik : i < j
        · have hkj : k = j := by omega
          rw [hkj] at hk
          refine Or.inl (Or.inl (Or.inl ?_))
          simp only [S1, Pj, Bj, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
            Finset.mem_range]
          exact ⟨⟨⟨i, hik, hi⟩, hk⟩, hab⟩
        · have hij : i = j := by omega
          rw [hij] at hi
          by_cases hkj : k < j
          · refine Or.inl (Or.inl (Or.inr ?_))
            simp only [S2, Pj, Bj, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
              Finset.mem_biUnion, Finset.mem_range]
            exact ⟨(b, a), ⟨⟨⟨k, hkj, hk⟩, hi⟩, by omega⟩, rfl⟩
          · have hk_eq : k = j := by omega
            rw [hk_eq] at hk
            by_cases hle : a ≤ b
            · refine Or.inl (Or.inr ?_)
              simp only [S3, Bj, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨hi, hk⟩, hle, hab⟩
            · refine Or.inr ?_
              simp only [S4, Bj, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
              exact ⟨(b, a), ⟨⟨hk, hi⟩, by omega, by omega⟩, rfl⟩
      have c1 : S1.card ≤ g := hblock_cross j n
      have c2 : S2.card ≤ g := le_trans Finset.card_image_le (hblock_cross j n)
      have c3 : S3.card ≤ g := hblock_self j n
      have c4 : S4.card ≤ g := le_trans Finset.card_image_le (hblock_self j n)
      have hU := Finset.card_le_card hsub
      have u1 := Finset.card_union_le (S1 ∪ S2 ∪ S3) S4
      have u2 := Finset.card_union_le (S1 ∪ S2) S3
      have u3 := Finset.card_union_le S1 S2
      omega
  · -- Part 2: Lower bound |A ∩ {1, ..., N}| ≥ (1/2048) N^{g / (2g + 1)} for all N ≥ 8192
    intro N hN
    -- Choose largest j such that 2 * 16^j ≤ N
    have hex_j : ∃ j : ℕ, 3 ≤ j ∧ 2 * 16 ^ j ≤ N ∧ N < 2 * 16 ^ (j + 1) := by
      have hlt_pow : ∃ k : ℕ, N < 2 * 16 ^ k := ⟨N + 1, by
        have h1 : N < 2 ^ (N + 1) := lt_trans (Nat.lt_succ_self N) Nat.lt_two_pow_self
        have h2 : 2 ^ (N + 1) ≤ 16 ^ (N + 1) := Nat.pow_le_pow_left (by norm_num) _
        omega⟩
      let k := Nat.find hlt_pow
      have hk_lt : N < 2 * 16 ^ k := Nat.find_spec hlt_pow
      have hk_ge4 : 4 ≤ k := by
        by_contra hlt
        have hk_le3 : k ≤ 3 := by omega
        have : 2 * 16 ^ k ≤ 2 * 16 ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hk_le3)
        norm_num at this
        omega
      refine ⟨k - 1, by omega, ?_, by rwa [show k - 1 + 1 = k by omega]⟩
      have hmin := Nat.find_min hlt_pow (show k - 1 < k by omega)
      omega
    rcases hex_j with ⟨j, hj3, hj_le, hj_lt⟩
    -- block j ⊆ (Icc 1 N).filter (· ∈ A)
    have hsub : block j ⊆ (Finset.Icc 1 N).filter (· ∈ A) := by
      intro b hb
      have hbB := hblock_bounds j b hb
      have h16 : 1 ≤ 16 ^ j := Nat.one_le_pow j 16 (by norm_num)
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, ⟨j, hb⟩⟩
    have hcard_ge : blockSize g j - blockSize g j / 2 ≤ ((Finset.Icc 1 N).filter (· ∈ A)).card :=
      le_trans (hblock_lb j) (Finset.card_le_card hsub)
    have hM_ge1 : 1 ≤ blockSize g j := blockSize_ge_one hg hj3
    -- Real inequality: (M + 1) / 4 ≤ M - M / 2 ≤ card
    have hcard_R : ((blockSize g j : ℝ) + 1) / 4 ≤
        (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) := by
      have hnat : blockSize g j + 1 ≤ 4 * (blockSize g j - blockSize g j / 2) := by omega
      have hnat2 : blockSize g j + 1 ≤ 4 * ((Finset.Icc 1 N).filter (· ∈ A)).card :=
        le_trans hnat (Nat.mul_le_mul_left 4 hcard_ge)
      have hR : (blockSize g j : ℝ) + 1 ≤ 4 * (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) := by
        exact_mod_cast hnat2
      linarith
    -- From N < 32 * 16^j and (16^j)^g < (16 * (M + 1))^(2g + 1):
    -- (N / 32)^g < (16 * (M + 1))^(2g + 1)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
    have hpow_strict : ((N : ℝ) / 32) ^ g < (16 * ((blockSize g j : ℝ) + 1)) ^ (2 * g + 1) := by
      have h1 : (N : ℝ) / 32 < (16 ^ j : ℝ) := by
        have hltR : (N : ℝ) < 32 * (16 ^ j : ℝ) := by
          have : N < 32 * 16 ^ j := by rw [pow_succ] at hj_lt; omega
          exact_mod_cast this
        linarith
      have h2 : ((N : ℝ) / 32) ^ g < ((16 ^ j : ℝ)) ^ g :=
        pow_lt_pow_left₀ h1 (by positivity) (by omega)
      have h3 : ((16 ^ j : ℝ)) ^ g < (16 * ((blockSize g j : ℝ) + 1)) ^ (2 * g + 1) := by
        exact_mod_cast blockSize_lt g j
      exact lt_trans h2 h3
    -- Take (2g + 1)-th roots via Real.rpow
    set e : ℝ := (g : ℝ) / (2 * (g : ℝ) + 1)
    have h2g1_pos : (0 : ℝ) < 2 * (g : ℝ) + 1 := by positivity
    have he_pos : 0 < e := by positivity
    have he_le1 : e ≤ 1 := by
      rw [div_le_one h2g1_pos]
      have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
      linarith
    have hroot : ((N : ℝ) / 32) ^ e ≤ 16 * ((blockSize g j : ℝ) + 1) := by
      have hbase1 : 0 ≤ (N : ℝ) / 32 := by positivity
      have hbase2 : 0 ≤ 16 * ((blockSize g j : ℝ) + 1) := by positivity
      have hr := Real.rpow_le_rpow (pow_nonneg hbase1 g) hpow_strict.le
        (inv_nonneg.mpr h2g1_pos.le)
      have hlhs : (((N : ℝ) / 32) ^ g) ^ ((2 * (g : ℝ) + 1)⁻¹) = ((N : ℝ) / 32) ^ e := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase1]
        rfl
      have hrhs : ((16 * ((blockSize g j : ℝ) + 1)) ^ (2 * g + 1)) ^ ((2 * (g : ℝ) + 1)⁻¹) =
          16 * ((blockSize g j : ℝ) + 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase2]
        have hcast : ((2 * g + 1 : ℕ) : ℝ) = 2 * (g : ℝ) + 1 := by push_cast; ring
        rw [hcast, mul_inv_cancel₀ h2g1_pos.ne', Real.rpow_one]
      rwa [hlhs, hrhs] at hr
    have h32_le : (32 : ℝ) ^ e ≤ 32 := by
      calc (32 : ℝ) ^ e ≤ (32 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he_le1
        _ = 32 := Real.rpow_one 32
    have hdiv_rpow : (N : ℝ) ^ e / 32 ≤ ((N : ℝ) / 32) ^ e := by
      rw [Real.div_rpow hN_pos.le (by norm_num)]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hN_pos.le e)
        (Real.rpow_pos_of_pos (by norm_num) e) h32_le
    linarith

/-- **Erdős–Rényi (1960) Polynomial-Exponent Refutation for Erdős Problem #40:**
For EVERY `ε > 0`, there exists `A ⊆ ℕ` and `M : ℕ` such that:
1. `∀ n, r_A(n) ≤ M` (and hence `limsup_{n → ∞} r_A(n) ≠ ⊤`), AND
2. `∀ N ≥ 8192, (1 / 2048) · (N^{1/2} / N^ε) ≤ |A ∩ {1, ..., N}|`. -/
theorem ppl163_erdos_renyi_poly_refutation (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℕ, ∃ M : ℕ,
      (∀ n : ℕ,
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card ≤ M) ∧
      (∀ N : ℕ, 8192 ≤ N →
        (1 / 2048 : ℝ) * ((N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) ^ ε) ≤
          (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) := by
  -- Choose integer g ≥ 1 such that 1 / (4g + 2) ≤ ε, so 1/2 - ε ≤ g / (2g + 1)
  let g : ℕ := max 1 (Nat.ceil (1 / (4 * ε)))
  have hg1 : 1 ≤ g := le_max_left 1 _
  have hge_ceil : 1 / (4 * ε) ≤ (g : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 1 (Nat.ceil (1 / (4 * ε))))
  have hexp : 1 / 2 - ε ≤ (g : ℝ) / (2 * (g : ℝ) + 1) := by
    have h2g1 : (0 : ℝ) < 2 * (g : ℝ) + 1 := by positivity
    have h4g : 1 ≤ 4 * ε * (g : ℝ) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * ε)).mp hge_ceil
      linarith
    rw [le_div_iff₀ h2g1]
    nlinarith
  rcases ppl163_erdos_renyi_b2g_existence g hg1 with ⟨A, hrep, hcard⟩
  refine ⟨A, 4 * g, hrep, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hrpow_le : (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) ^ ε ≤
      (N : ℝ) ^ ((g : ℝ) / (2 * (g : ℝ) + 1)) := by
    rw [← Real.rpow_sub hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have hlb := hcard N hN
  linarith

/-- **Every Polynomial `g(N) = N^ε` (`ε > 0`) Fails Erdős Problem #40:**
Unconditional refutation of the Erdős #40 implication for every polynomial growth function
`g(N) = N^ε` (`ε > 0`). -/
theorem ppl163_poly_g_fails_erdos40 (ε : ℝ) (hε : 0 < ε) :
    ¬ (∀ A : Set ℕ,
        (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          c * ((N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) ^ ε) ≤
            (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
        Filter.limsup
          (fun n : ℕ =>
            (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
              (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
          Filter.atTop = ⊤) := by
  intro hall
  rcases ppl163_erdos_renyi_poly_refutation ε hε with ⟨A, M, hrep, hcard⟩
  have htop := hall A ⟨1 / 2048, by norm_num, 8192, hcard⟩
  rw [(ppl163_limsup_top_iff_unbounded A).1, (ppl163_limsup_top_iff_unbounded A).2] at htop
  exact htop ⟨M, hrep⟩

/-! ## Section 5: Threshold Monotonicity & Sub-Polynomial Frontier Barriers (`g(N) = N^{o(1)}`) -/

/-- **Threshold Monotonicity in `g`:**
If `g₁` and `g₂` satisfy eventually `0 < g₁ N` and `g₁ N ≤ C * g₂ N` (for some `C > 0`), and
`g₂` satisfies the Erdős #40 implication, then `g₁` also satisfies the Erdős #40 implication. -/
theorem ppl163_threshold_monotonicity (g₁ g₂ : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hdom : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 0 < g₁ N ∧ g₁ N ≤ C * g₂ N)
    (h40_g₂ : ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * ((N : ℝ) ^ (1 / 2 : ℝ) / g₂ N) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤) :
    ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * ((N : ℝ) ^ (1 / 2 : ℝ) / g₁ N) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤ := by
  intro A ⟨c, hc, N₀, hN₀⟩
  rcases hdom with ⟨N₁, hN₁⟩
  apply h40_g₂ A
  refine ⟨c / C, div_pos hc hC, max N₀ N₁, fun N hN => ?_⟩
  have h1 := hN₁ N (le_trans (le_max_right _ _) hN)
  have h0 := hN₀ N (le_trans (le_max_left _ _) hN)
  have hg₂_pos : 0 < g₂ N := by nlinarith
  have hstep : (c / C) * ((N : ℝ) ^ (1 / 2 : ℝ) / g₂ N) ≤
      c * ((N : ℝ) ^ (1 / 2 : ℝ) / g₁ N) := by
    have hnum_nn : 0 ≤ c * (N : ℝ) ^ (1 / 2 : ℝ) :=
      mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    have hrew1 : (c / C) * ((N : ℝ) ^ (1 / 2 : ℝ) / g₂ N) =
        (c * (N : ℝ) ^ (1 / 2 : ℝ)) / (C * g₂ N) := by ring
    have hrew2 : c * ((N : ℝ) ^ (1 / 2 : ℝ) / g₁ N) =
        (c * (N : ℝ) ^ (1 / 2 : ℝ)) / g₁ N := by ring
    rw [hrew1, hrew2]
    exact div_le_div_of_nonneg_left hnum_nn h1.1 h1.2
  linarith

/-- **Sub-Polynomial Barrier (`liminf g(N) / N^ε = 0` for every `ε > 0`):**
If `g : ℕ → ℝ` satisfies the Erdős #40 implication, then `g` CANNOT eventually dominate
`C * N^ε` for ANY `ε > 0` and ANY `C > 0`: equivalently, for every `ε > 0` and `C > 0`,
`∃ᶠ N in Filter.atTop, g N < C * N^ε`. -/
theorem ppl163_valid_g_liminf_poly_zero (g : ℕ → ℝ)
    (h40 : ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * ((N : ℝ) ^ (1 / 2 : ℝ) / g N) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤)
    (ε : ℝ) (hε : 0 < ε) (C : ℝ) (hC : 0 < C) :
    ∃ᶠ N : ℕ in Filter.atTop, g N < C * (N : ℝ) ^ ε := by
  rw [Filter.frequently_atTop]
  intro N₁
  by_contra hno
  push Not at hno
  have hpoly := ppl163_threshold_monotonicity (fun N => (N : ℝ) ^ ε) g (1 / C) (by positivity)
    ⟨max N₁ 1, fun N hN => by
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : 1 ≤ N := le_trans (le_max_right _ _) hN
        exact_mod_cast this
      have hge := hno N (le_trans (le_max_left _ _) hN)
      refine ⟨Real.rpow_pos_of_pos hNpos ε, ?_⟩
      rw [one_div_mul_eq_div, le_div_iff₀ hC]
      linarith⟩
    h40
  exact ppl163_poly_g_fails_erdos40 ε hε hpoly

/-- **Logarithmic Exponent Barrier (`∃ᶠ N, log(g N) / log N < ε` for every `ε > 0`):**
If `g : ℕ → ℝ` satisfies the Erdős #40 implication and eventually `1 ≤ g N`, then for every
`ε > 0`, `log (g N) / log N < ε` infinitely often — proving unconditionally that no positive
polynomial growth exponent can survive in Erdős #40. -/
theorem ppl163_valid_g_log_ratio_not_pos (g : ℕ → ℝ)
    (hg1 : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 1 ≤ g N)
    (h40 : ∀ A : Set ℕ,
      (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * ((N : ℝ) ^ (1 / 2 : ℝ) / g N) ≤ (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)) →
      Filter.limsup
        (fun n : ℕ =>
          (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
            (fun p => p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n)).card : ℕ∞))
        Filter.atTop = ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ in Filter.atTop, Real.log (g N) / Real.log (N : ℝ) < ε := by
  rcases hg1 with ⟨N₁, hN₁⟩
  have hfreq := ppl163_valid_g_liminf_poly_zero g h40 ε hε 1 one_pos
  rw [Filter.frequently_atTop] at hfreq ⊢
  intro M
  rcases hfreq (max M (max N₁ 2)) with ⟨N, hN, hlt⟩
  refine ⟨N, le_trans (le_max_left _ _) hN, ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right N₁ 2) (le_trans (le_max_right M _) hN)
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    have : 1 < N := by omega
    exact_mod_cast this
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hg_pos : 0 < g N := by
    have := hN₁ N (le_trans (le_max_left N₁ 2) (le_trans (le_max_right M _) hN))
    linarith
  rw [one_mul] at hlt
  have hlog_lt : Real.log (g N) < Real.log ((N : ℝ) ^ ε) := Real.log_lt_log hg_pos hlt
  rw [Real.log_rpow (by linarith)] at hlog_lt
  exact (div_lt_iff₀ hlog_pos).mpr (by linarith)

/-- **Polylogarithmic Functions Sit Strictly Inside the Open `N^{o(1)}` Frontier:**
For every `c > 0` and every `ε > 0`, `(Real.log N)^c / N^ε → 0` as `N → ∞`, certifying why
Erdős's primary open test family `g(N) = (log N)^c` is NOT ruled out by Erdős–Rényi (1960). -/
theorem ppl163_polylog_subpolynomial (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    Filter.Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ c / (N : ℝ) ^ ε)
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ (ε / c)) Filter.atTop (nhds 0) := by
    simpa using (isLittleO_log_rpow_atTop (div_pos hε hc)).tendsto_div_nhds_zero
  have h2 : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ) ^ (ε / c))
      Filter.atTop (nhds 0) :=
    h1.comp tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_atTop] at h2 ⊢
  intro δ hδ
  rcases h2 (δ ^ (1 / c)) (Real.rpow_pos_of_pos hδ _) with ⟨N₀, hN₀⟩
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : 1 ≤ N := by omega
    exact_mod_cast this
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hq_nn : 0 ≤ Real.log (N : ℝ) / (N : ℝ) ^ (ε / c) :=
    div_nonneg hlog_nn (Real.rpow_nonneg hNpos.le _)
  have hlt := hN₀ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hq_nn] at hlt
  have hpow_lt : (Real.log (N : ℝ) / (N : ℝ) ^ (ε / c)) ^ c < δ := by
    calc (Real.log (N : ℝ) / (N : ℝ) ^ (ε / c)) ^ c
        < (δ ^ (1 / c)) ^ c := Real.rpow_lt_rpow hq_nn hlt hc
      _ = δ := by
            rw [← Real.rpow_mul hδ.le, one_div_mul_cancel hc.ne', Real.rpow_one]
  have hrew : (Real.log (N : ℝ) / (N : ℝ) ^ (ε / c)) ^ c =
      (Real.log (N : ℝ)) ^ c / (N : ℝ) ^ ε := by
    rw [Real.div_rpow hlog_nn (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le,
      div_mul_cancel₀ ε hc.ne']
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  rwa [← hrew]

end

end PPL163
